if _G.PoolTrainingHelper then pcall(_G.PoolTrainingHelper.Stop) end
local RS=game:GetService("RunService")
local UIS=game:GetService("UserInputService")
local Players=game:GetService("Players")
local H={Enabled=true,Running=true,ShowCollisions=false,Version="robust-2",Stats={}}
_G.PoolTrainingHelper=H
local physics={deceleration=10,minSpeed=30,maxSpeed=138,curve=2,stopSpeed=0.5,
 railRestitution=0.72,railFriction=0.20,ballRestitution=0.94,breakMultiplier=2.5,
 spinDecay=1.2,spinTransfer=0.35,cushionSpin=22,slidingDeceleration=0}
local SIM_SLICE=0.006
local REMOVE_HOLD=0.6
local MIN_POWER=0.03
local BALL_RADIUS=1.125
local GHOST_HALF=1.15*BALL_RADIUS
local TABLE_Y=5000+BALL_RADIUS
local LABEL_MAX=260
local function finite(n) return type(n)=="number" and n==n and n>-1e7 and n<1e7 end
local function shotSpeed(power) return physics.minSpeed+(physics.maxSpeed-physics.minSpeed)*power^physics.curve end
local function V(x,y) return {x=x,y=y} end
local function add(a,b) return V(a.x+b.x,a.y+b.y) end
local function sub(a,b) return V(a.x-b.x,a.y-b.y) end
local function mul(a,s) return V(a.x*s,a.y*s) end
local function dot(a,b) return a.x*b.x+a.y*b.y end
local function length(a) return math.sqrt(dot(a,a)) end
local function unit(a) local m=length(a);return m>1e-8 and mul(a,1/m) or V(0,0) end
local rails,pockets,jaws={},{},{}
local function rail(a,b,n)
 local d=sub(b,a);local span=length(d)
 rails[#rails+1]={a=a,b=b,n=n,tx=d.x/span,ty=d.y/span,span=span}
end
local corner=4.5/math.sqrt(2)
rail(V(-44+corner,-22),V(-2.5,-22),V(0,1))
rail(V(2.5,-22),V(44-corner,-22),V(0,1))
rail(V(-44+corner,22),V(-2.5,22),V(0,-1))
rail(V(2.5,22),V(44-corner,22),V(0,-1))
rail(V(-44,-22+corner),V(-44,22-corner),V(1,0))
rail(V(44,-22+corner),V(44,22-corner),V(-1,0))
local function pocket(a,b,side)
 local centre=mul(add(a,b),0.5)
 local tangent=unit(sub(b,a))
 local n=V(tangent.y,-tangent.x)
 if dot(n,centre)<0 then n=mul(n,-1) end
 local mouth=length(sub(b,a))
 local flare=side and math.rad(-14) or 0
 local radius=mouth/2
 local bowl=add(centre,mul(n,mouth*(side and 0.8 or 1.4)))
 local function facing(start)
  local outward=unit(sub(start,centre))
  local direction=add(mul(n,math.cos(flare)),mul(outward,math.sin(flare)))
  local q=sub(bowl,start)
  local projected=dot(q,direction)
  local inside=radius*radius-(dot(q,q)-projected*projected)
  if inside>0 then projected=projected-math.sqrt(inside) end
  local finish=add(start,mul(direction,math.max(projected,2/math.cos(flare))))
  local tang=unit(sub(finish,start))
  local normal=V(-tang.y,tang.x)
  if dot(normal,sub(centre,start))<0 then normal=mul(normal,-1) end
  rail(start,finish,normal)
  jaws[#jaws+1]=start
 end
 facing(a);facing(b)
 pockets[#pockets+1]={c=centre,n=n,tx=-n.y,ty=n.x,mouth=mouth,half=mouth/2,
  depth=side and 0.3 or 2.6,bowl=bowl,id=#pockets+1}
end
pocket(V(-44+corner,-22),V(-44,-22+corner),false)
pocket(V(-44+corner,22),V(-44,22-corner),false)
pocket(V(44-corner,-22),V(44,-22+corner),false)
pocket(V(44-corner,22),V(44,22-corner),false)
pocket(V(-2.5,-22),V(2.5,-22),true)
pocket(V(-2.5,22),V(2.5,22),true)
local function timeCircle(dx,dy,vx,vy,radius,limit)
 local c=dx*dx+dy*dy-radius*radius
 local b=2*(dx*vx+dy*vy)
 if c<0 then return b<0 and 0 or nil end
 if b>=0 then return nil end
 local a=vx*vx+vy*vy
 if a<=1e-6 then return nil end
 local disc=b*b-4*a*c
 if disc<0 then return nil end
 local t=(-b-math.sqrt(disc))/(2*a)
 if t<0 or t>limit then return nil end
 return t
end
local function timeRail(p,v,r,rail,limit)
 local n=rail.n
 local approach=v.x*n.x+v.y*n.y
 if approach>=-1e-6 then return nil end
 local ax,ay=rail.a.x,rail.a.y
 local distance=(p.x-ax)*n.x+(p.y-ay)*n.y
 if distance< -r then return nil end
 local t=distance<r and 0 or (r-distance)/approach
 if t<0 or t>limit then return nil end
 local along=(p.x+v.x*t-ax)*rail.tx+(p.y+v.y*t-ay)*rail.ty
 return along>=0 and along<=rail.span and t or nil
end
local function timePocket(p,v,k,limit)
 local n=k.n
 local approach=v.x*n.x+v.y*n.y
 if approach<=1e-6 then return nil end
 local qx,qy=p.x-k.c.x,p.y-k.c.y
 local t=(k.depth-(qx*n.x+qy*n.y))/approach
 if t<0 or t>limit then return nil end
 if math.abs((qx+v.x*t)*k.tx+(qy+v.y*t)*k.ty)>k.half then return nil end
 return t
end
local function simulateAll(snapshot,power,doYield)
 local balls,byId={},{}
 for _,source in ipairs(snapshot.balls) do
  local b={id=source.id,p=V(source.p.x,source.p.y),v=V(0,0),spin=V(0,0),r=source.r,
   start=V(source.p.x,source.p.y),anchor=V(source.p.x,source.p.y),moved=false,pocketed=false,paths={}}
  balls[#balls+1]=b;byId[b.id]=b
 end
 local white=byId[0]
 if not white then return {balls=balls,byId=byId,settled=true,collisions=0} end
 white.v=mul(snapshot.direction,shotSpeed(power)*(snapshot.isBreak and physics.breakMultiplier or 1))
 white.spin=V(snapshot.spin and snapshot.spin.x or 0,snapshot.spin and snapshot.spin.y or 0)
 local result={balls=balls,byId=byId,settled=false,collisions=0,steps=0,contact=nil}
 local count=#balls
 local function flush(b)
  local p,anchor=b.p,b.anchor
  local dx,dy=p.x-anchor.x,p.y-anchor.y
  if dx*dx+dy*dy>0.0004 then
   local point=V(p.x,p.y)
   b.paths[#b.paths+1]={a=anchor,b=point,id=b.id,afterContact=result.firstContact~=nil}
   b.anchor=point
  end
 end
 local function transferSpin(ball,incoming)
  local incomingSpeed=length(incoming)
  if math.abs(ball.spin.y)>0.001 and incomingSpeed>1e-6 then
   local velocity=add(ball.v,mul(unit(incoming),ball.spin.y*physics.spinTransfer*incomingSpeed))
   if length(velocity)>incomingSpeed then velocity=mul(unit(velocity),incomingSpeed) end
   ball.v=velocity;ball.spin.y=ball.spin.y*0.35
  end
 end
 local function bounce(ball,n,useSideSpin)
  local normal=dot(ball.v,n)
  if normal<0 then
   local tangent=mul(sub(ball.v,mul(n,normal)),1-physics.railFriction)
   if useSideSpin and math.abs(ball.spin.x)>0.001 then
    tangent=add(tangent,mul(V(-n.y,n.x),ball.spin.x*physics.cushionSpin))
    ball.spin.x=ball.spin.x*0.4
   end
   ball.v=sub(tangent,mul(n,normal*physics.railRestitution))
  end
 end
 local function pocketBall(ball,k)
  flush(ball)
  ball.pocketed=true;ball.pocketId=k.id;ball.p=V(k.bowl.x,k.bowl.y)
  ball.v=V(0,0);ball.spin=V(0,0);ball.moved=true
 end
 local function capture(ball)
  if ball.pocketed then return end
  local p=ball.p
  for _,k in ipairs(pockets) do
   local qx,qy=p.x-k.c.x,p.y-k.c.y
   if qx*k.n.x+qy*k.n.y>=k.depth and math.abs(qx*k.tx+qy*k.ty)<=k.half then
    pocketBall(ball,k);return
   end
  end
 end
 for _,ball in ipairs(balls) do capture(ball) end
 local dt=1/120
 local spinFactor=math.exp(-physics.spinDecay*dt)
 local moving={}
 local sliceStart=tick()
 for step=1,3000 do
  result.steps=step
  local remaining=dt
  for substep=1,128 do
   if remaining<=1e-6 then break end
   local best=remaining
   local kind,a,b,geometry=nil,nil,nil,nil
   for i=1,count-1 do
    local one=balls[i]
    if not one.pocketed then
     local p1,v1,r1=one.p,one.v,one.r
     local active=v1.x*v1.x+v1.y*v1.y>1e-9
     for j=i+1,count do
      local two=balls[j]
      if not two.pocketed then
       local v2=two.v
       if active or v2.x*v2.x+v2.y*v2.y>1e-9 then
        local p2=two.p
        local t=timeCircle(p2.x-p1.x,p2.y-p1.y,v2.x-v1.x,v2.y-v1.y,r1+two.r,best)
        if t and t<best then best=t;kind="ball";a=one;b=two;geometry=nil end
       end
      end
     end
    end
   end
   local movingCount=0
   for _,ball in ipairs(balls) do
    local v=ball.v
    if not ball.pocketed and v.x*v.x+v.y*v.y>1e-9 then
     movingCount=movingCount+1;moving[movingCount]=ball
     local p,r=ball.p,ball.r
     for _,rl in ipairs(rails) do
      local t=timeRail(p,v,r,rl,best)
      if t and t<best then best=t;kind="rail";a=ball;b=nil;geometry=rl end
     end
     for _,jaw in ipairs(jaws) do
      local t=timeCircle(jaw.x-p.x,jaw.y-p.y,-v.x,-v.y,r,best)
      if t and t<best then best=t;kind="jaw";a=ball;b=nil;geometry=jaw end
     end
     for _,k in ipairs(pockets) do
      local t=timePocket(p,v,k,best)
      if t and t<best then best=t;kind="pocket";a=ball;b=nil;geometry=k end
     end
    end
   end
   for i=1,movingCount do
    local ball=moving[i]
    local p,v=ball.p,ball.v
    local dx,dy=v.x*best,v.y*best
    p.x=p.x+dx;p.y=p.y+dy
    if dx*dx+dy*dy>1e-12 then ball.moved=true end
   end
   remaining=remaining-best
   if kind=="ball" then
    flush(a);flush(b)
    local delta=sub(b.p,a.p)
    local separation=length(delta)
    local n=separation>1e-8 and mul(delta,1/separation) or V(1,0)
    local incomingA,incomingB=a.v,b.v
    local impulse=dot(sub(a.v,b.v),n)*(1+physics.ballRestitution)/2
    if impulse>0 then
     a.v=sub(a.v,mul(n,impulse));b.v=add(b.v,mul(n,impulse))
     transferSpin(a,incomingA);transferSpin(b,incomingB)
     a.moved=true;b.moved=true;result.collisions=result.collisions+1
     if not result.contact and (a.id==0 or b.id==0) then
      result.contact=V(white.p.x,white.p.y)
      result.firstContact=a.id==0 and b.id or a.id
     end
    end
   elseif kind=="rail" then
    if a.id==0 then result.cueRails=(result.cueRails or 0)+1 else result.objectRails=(result.objectRails or 0)+1 end
    flush(a);bounce(a,geometry.n,true)
    local distance=dot(sub(a.p,geometry.a),geometry.n)
    if distance<a.r then a.p=add(a.p,mul(geometry.n,math.min(a.r-distance+0.0001,a.r*2))) end
   elseif kind=="jaw" then
    if a.id==0 then result.cueRails=(result.cueRails or 0)+1 else result.objectRails=(result.objectRails or 0)+1 end
    flush(a)
    local n=unit(sub(a.p,geometry))
    bounce(a,n,false)
    a.p=add(geometry,mul(n,a.r+0.0001))
   elseif kind=="pocket" then
    pocketBall(a,geometry)
   end
   for i=1,movingCount do capture(moving[i]) end
   if best<1e-9 and not kind then break end
  end
  local any=false
  for _,ball in ipairs(balls) do
   if not ball.pocketed then
    local v,s=ball.v,ball.spin
    local speed=math.sqrt(v.x*v.x+v.y*v.y)
    local deceleration=physics.deceleration+(math.abs(s.y)>0.05 and physics.slidingDeceleration*0.35 or 0)
    local nextSpeed=speed-deceleration*dt
    s.x=s.x*spinFactor;s.y=s.y*spinFactor
    if nextSpeed<=physics.stopSpeed then
     v.x=0;v.y=0
    elseif speed>1e-9 then
     local f=nextSpeed/speed
     v.x=v.x*f;v.y=v.y*f;any=true
    end
   end
  end
  if not any then result.settled=true;break end
  if doYield and step%30==0 and tick()-sliceStart>SIM_SLICE then
   task.wait();sliceStart=tick()
   if not H.Running or (snapshot.epoch and (not H.CurrentInput or H.CurrentInput.base~=snapshot.base)) then return nil end
  end
 end
 result.settled=true
 for _,ball in ipairs(balls) do flush(ball) end
 return result
end



local function lowestBall(balls)
 local lowest=nil
 for _,b in ipairs(balls) do
  if not b.pocketed and b.id>=1 and b.id<=15 and (not lowest or b.id<lowest) then lowest=b.id end
 end
 return lowest
end
H.LowestBall=lowestBall
local function eightIsReady(balls,group)
 if group~="Solid" and group~="Stripe" then return false end
 for _,b in ipairs(balls) do
  if not b.pocketed and ((group=="Solid" and b.id>=1 and b.id<=7) or (group=="Stripe" and b.id>=9 and b.id<=15)) then return false end
 end
 return true
end
local function showBallPreview(ball,primary,extras,ready)
 return ball.moved and (ball.id==0 or ball.id==primary or extras or (ball.id==8 and ready==false))
end
H.EightIsReady=eightIsReady
H.ShowBallPreview=showBallPreview
local function ballSide(id,group,ready)
 if group=="NineBall" then return id and id>=1 and id<=15 and "Own" or nil end
 if group~="Solid" and group~="Stripe" then return nil end
 if id==8 then return ready and "Own" or nil end
 if id==0 or not id or id<1 or id>15 then return nil end
 local own=(group=="Solid" and id<=7) or (group=="Stripe" and id>=9)
 return own and "Own" or "Opponent"
end
local function safePocket(result,id,group,ready,lowest)
 local ball=result.byId[id]
 local white=result.byId[0]
 local eight=result.byId[8]
 if group=="NineBall" then
  return ball~=nil and ball.pocketed and result.settled and lowest~=nil and result.firstContact==lowest
   and not (white and white.pocketed)
 end
 return ball~=nil and ball.pocketed and result.settled and ballSide(id,group,ready)=="Own"
  and ballSide(result.firstContact,group,ready)=="Own"
  and not (white and white.pocketed) and not (eight and eight.pocketed and not ready)
end
H.BallSide=ballSide
H.SafePocket=safePocket

local yellow=Color3.fromRGB(255,220,30)
local cyan=Color3.fromRGB(90,220,255)
local whiteColor=Color3.fromRGB(245,245,245)
local red=Color3.fromRGB(255,70,70)
local green=Color3.fromRGB(90,245,130)
local pink=Color3.fromRGB(255,105,180)
local neutral=Color3.fromRGB(190,190,190)
local function pathColor(id,group,ready)
 if id==0 then return whiteColor end
 if group=="NineBall" then return id==9 and green or pink end
 if id==8 then return ready and green or red end
 if group~="Solid" and group~="Stripe" then return neutral end
 local own=(group=="Solid" and id>=1 and id<=7) or (group=="Stripe" and id>=9 and id<=15)
 return own and pink or cyan
end
H.PathColor=pathColor
local function markerColor(ball,primary,group,ready,extras)
 if ball.id==0 then return ball.pocketed and red or whiteColor end
 if ball.id==8 then return pathColor(8,group,ready) end
 local side=ballSide(ball.id,group,ready)
 if side=="Opponent" and ball.pocketed then return red end
 if ball.id==primary then return yellow end
 if extras and side=="Own" then return pink end
 if extras and side=="Opponent" then return cyan end
 if not side then return neutral end
 return ball.pocketed and green or cyan
end
H.MarkerColor=markerColor
local lines,extraLines,markers,connections={},{},{},{}
for i=1,64 do
 local l=Drawing.new("Line")
 l.Color=yellow;l.Thickness=2;l.Visible=false;l.ZIndex=90;lines[i]=l
end
for i=1,128 do
 local l=Drawing.new("Line")
 l.Color=cyan;l.Thickness=1.5;l.Visible=false;l.ZIndex=89;extraLines[i]=l
end
for id=0,15 do
 local c=Drawing.new("Circle")
 c.Color=id==0 and whiteColor or cyan;c.Thickness=2;c.NumSides=40
 c.Filled=id~=0;c.Transparency=id==0 and 0 or 0.35;c.Visible=false;c.ZIndex=91
 markers[id+1]=c
end
local ghost=Drawing.new("Circle")
ghost.Color=yellow;ghost.Thickness=2;ghost.NumSides=40;ghost.Filled=false;ghost.Visible=false;ghost.ZIndex=91
local label=Drawing.new("Text")
label.Color=yellow;label.Size=16;label.Outline=true;label.Font=1
label.Position=Vector2.new(20,100);label.Visible=true;label.ZIndex=92
label.Text="Loading pool preview... | X toggle | Hold O: remove"
local function newBadge(color)
 local ring=Drawing.new("Circle")
 ring.Color=color;ring.Thickness=2;ring.NumSides=40;ring.Filled=false;ring.Visible=false;ring.ZIndex=93
 local text=Drawing.new("Text")
 text.Color=color;text.Size=15;text.Font=1;text.Outline=true;text.Center=true;text.Visible=false;text.ZIndex=94
 return {ring=ring,text=text}
end
local warningDrawings={eight=newBadge(red),white=newBadge(red)}
local pocketDrawings={}
for id=1,15 do pocketDrawings[id]=newBadge(green) end
local ownGroup,ownSeat="Unknown",nil
local warningHud,warningContext=nil,nil
local warningGroupSignature=nil
local warningResolveNeeded=false
local groupMemory=nil
local currentBalls={}
local profileNames=_G.PoolHelperDisplayNames or {}
_G.PoolHelperDisplayNames=profileNames
local latest,preview,guideCache=nil,nil,nil
local cueShapeAddress,cueShapeMin,cueShapeMax,cueShapeAxis=nil,nil,nil,nil
local cueFallbackAddress,cueFallback=nil,nil
local previous={}
local quietAt=0
local epoch=0
local sourceKey=nil
local frame={mode="3D",vw=1920,vh=1080}
local shown,wasShown={},{}
local function show(d) d.Visible=true;shown[d]=true end
local function endFrame()
 for d in pairs(wasShown) do if not shown[d] then d.Visible=false end end
 wasShown=shown;shown={}
end
local function hide()
 for _,l in ipairs(lines) do pcall(function() l.Visible=false end) end
 for _,l in ipairs(extraLines) do pcall(function() l.Visible=false end) end
 for _,c in ipairs(markers) do pcall(function() c.Visible=false end) end
 pcall(function() ghost.Visible=false end)
 for _,w in pairs(warningDrawings) do pcall(function() w.ring.Visible=false;w.text.Visible=false end) end
 for _,w in pairs(pocketDrawings) do pcall(function() w.ring.Visible=false;w.text.Visible=false end) end
 shown={};wasShown={}
end
local function remove(d) pcall(function() d:Remove() end) end
function H.Stop()
 if not H.Running then return end
 H.Running=false
 for _,c in ipairs(connections) do pcall(function() c:Disconnect() end) end
 for _,l in ipairs(lines) do remove(l) end
 for _,l in ipairs(extraLines) do remove(l) end
 for _,c in ipairs(markers) do remove(c) end
 remove(ghost);remove(label)
 for _,w in pairs(warningDrawings) do remove(w.ring);remove(w.text) end
 for _,w in pairs(pocketDrawings) do remove(w.ring);remove(w.text) end
end
local function isPart(inst) local c=inst.ClassName;return c=="MeshPart" or c=="Part" end
local function firstPart(model)
 if not model then return nil end
 for _,child in ipairs(model:GetDescendants()) do if isPart(child) then return child end end
 return nil
end
local function findCue(stick,refresh)
 if not stick then return nil end
 local root=stick:FindFirstChild("Cue_0")
 if root and isPart(root) then return root end
 local address=stick.Address
 if refresh or address~=cueFallbackAddress then cueFallbackAddress=address;cueFallback=firstPart(stick) end
 return cueFallback
end
local function axisVector(cf,index)
 if index==2 then return cf.UpVector elseif index==3 then return cf.LookVector end
 return cf.RightVector
end
local function longAxis(part)
 local size=part.Size
 if not size or not finite(size.X) or not finite(size.Y) or not finite(size.Z) then return 1 end
 if size.Y>size.X and size.Y>=size.Z then return 2 end
 if size.Z>size.X and size.Z>size.Y then return 3 end
 return 1
end
local function cacheCueShape(stick,cue)
 local address=stick and stick.Address or nil
 if address==cueShapeAddress and cueShapeMin then return end
 cueShapeMin=nil;cueShapeMax=nil;cueShapeAxis=nil
 if not stick or not cue then cueShapeAddress=nil;return end
 cueShapeAddress=address
 local axisIndex=longAxis(cue)
 local centre=cue.Position
 local axis=axisVector(cue.CFrame,axisIndex)
 local low,high=math.huge,-math.huge
 for _,part in ipairs(stick:GetDescendants()) do
  if isPart(part) then
   local frameCF,position,size=part.CFrame,part.Position,part.Size
   local r,u,l=frameCF.RightVector,frameCF.UpVector,frameCF.LookVector
   local extent=(math.abs(axis.X*r.X+axis.Y*r.Y+axis.Z*r.Z)*size.X
    +math.abs(axis.X*u.X+axis.Y*u.Y+axis.Z*u.Z)*size.Y
    +math.abs(axis.X*l.X+axis.Y*l.Y+axis.Z*l.Z)*size.Z)/2
   local at=(position.X-centre.X)*axis.X+(position.Y-centre.Y)*axis.Y+(position.Z-centre.Z)*axis.Z
   if finite(extent) and finite(at) then low=math.min(low,at-extent);high=math.max(high,at+extent) end
  end
 end
 if low<high then cueShapeMin=low;cueShapeMax=high;cueShapeAxis=axisIndex end
end
local function powerFromCue(distance,low,high,radius,percent)
 if not low or not high or not finite(distance) then return nil end
 local gap=distance>0 and distance-high or -distance+low
 local raw=(gap-radius-1.6)/9
 if raw~=raw or raw< -0.01 or raw>1.01 then return nil end
 raw=math.clamp(raw,0,1)
 return math.abs(raw-percent/100)<0.012 and raw or nil
end
H.PowerFromCue=powerFromCue
local function normalizeSpin(x,y)
 local m=math.sqrt(x*x+y*y)
 return m>1 and V(x/m,y/m) or V(x,y)
end
local function guiSpin(widget)
 local spinDot=widget and widget:FindFirstChild("Dot")
 local spinIcon=widget and widget:FindFirstChild("Icon")
 if not spinDot or not spinIcon then return nil end
 local root,dotPosition,icon=widget.AbsolutePosition,spinDot.AbsolutePosition,spinIcon.AbsolutePosition
 if not root or not dotPosition or not icon then return nil end
 if not (finite(root.X) and finite(root.Y) and finite(dotPosition.X) and finite(dotPosition.Y) and finite(icon.X) and finite(icon.Y)) then return nil end
 local margin=((root.X-icon.X)+(root.Y-icon.Y))/2
 local width=margin/0.075
 if width<=1 then return nil end
 local spin=normalizeSpin((dotPosition.X-root.X-width*0.4)/(width*0.37),
  -(dotPosition.Y-root.Y-width*0.4)/(width*0.37))
 if not finite(spin.x) or not finite(spin.y) then return nil end
 return spin
end
local function selectedSpin(widget)
 local ok,visual=pcall(guiSpin,widget)
 if ok and visual then H.Stats.spinSource="spin control";H.Stats.spinError=nil;return visual end
 H.Stats.spinSource="unavailable";H.Stats.spinError="Spin unavailable: assuming centre";return V(0,0)
end
H.ReadSpin=selectedSpin
local function cleanName(value)
 local name=(value or ""):gsub("<[^>]*>","")
 name=name:match("^(.-)%s+·%s*") or name
 return name:gsub("^%s+",""):gsub("%s+$",""):lower()
end
local function resolveSide(userId,username,display,names,mode,seats)
 if mode=="Offline" or mode=="Tutorial" or mode=="Trickshot" then return nil,"No user seats in local practice" end
 if seats then
  local found=nil
  for i=1,2 do
   if seats[i] and seats[i].UserId==userId then
    if found then return nil,"Ambiguous user seats" end
    found=i
   end
  end
  return found,found and "Match UserId" or "User is not seated in this match"
 end
 local found=nil
 for i=1,2 do
  local n=cleanName(names[i])
  if n~="" and (n==cleanName(username) or (display and n==cleanName(display))) then
   if found then return nil,"Ambiguous player names" end
   found=i
  end
 end
 return found,found and "Unique player name" or "Waiting for user identity"
end
H.ResolveSide=resolveSide
local function chipGroup(panel)
 local chips=panel and panel:FindFirstChild("Chips")
 local solid,stripe,open=0,0,0
 if chips then
  for _,child in ipairs(chips:GetChildren()) do
   local id=tonumber(child.Name:match("^Chip(%d+)$"))
   if id and id>=1 and id<=7 then solid=solid+1 end
   if id and id>=9 and id<=15 then stripe=stripe+1 end
   if child.Name:match("^Placeholder%d+$") then open=open+1 end
  end
 end
 return solid>0 and stripe==0 and "Solid" or stripe>0 and solid==0 and "Stripe" or open>0 and "Open" or "Unknown",solid+stripe+open
end
local function nineBallActive(hud)
 local rack=hud:FindFirstChild("NineBallRack")
 local holder=rack and rack:FindFirstChild("Balls")
 if not holder or not holder:FindFirstChild("Slot9") then return false end
 for _,side in ipairs({"LeftPlayer","RightPlayer"}) do
  local _,chips=chipGroup(hud:FindFirstChild(side))
  if chips>0 then return false end
 end
 return true
end
local function refreshOwnGroup()
 ownGroup="Unknown";ownSeat=nil
 H.Stats.ownSeat=nil;H.Stats.ownGroup="Unknown";H.Stats.groupSource=nil
 if not warningHud then H.Stats.sideSource="Waiting for table";return end
 local lp=Players.LocalPlayer
 local parent=warningHud.Parent
 local mode=parent and parent:GetAttribute("MatchMode") or "Unknown"
 H.Stats.matchMode=mode
 local names={}
 for i,side in ipairs({"LeftPlayer","RightPlayer"}) do
  local panel=warningHud:FindFirstChild(side)
  local nameLabel=panel and panel:FindFirstChild("PlayerName")
  names[i]=nameLabel and nameLabel.Text or ""
  if type(names[i])~="string" then names[i]="" end
 end
 local signature=tostring(mode).."|"..names[1].."|"..names[2]
 if signature~=warningGroupSignature then
  warningGroupSignature=signature;warningResolveNeeded=true
  groupMemory=nil
 end
 local source=nil
 ownSeat,source=resolveSide(lp.UserId,lp.Name,profileNames[tostring(lp.UserId)],names,mode,nil)
 if nineBallActive(warningHud) then
  groupMemory=nil;ownGroup="NineBall";H.Stats.groupSource="nine-ball rack"
 elseif ownSeat then
  local group=chipGroup(warningHud:FindFirstChild(ownSeat==1 and "LeftPlayer" or "RightPlayer"))
  local memoryKey=tostring(warningContext).."|"..signature.."|"..ownSeat
  H.Stats.groupSource="chips"
  if group=="Solid" or group=="Stripe" then groupMemory={key=memoryKey,group=group}
  elseif group=="Open" then groupMemory=nil
  elseif groupMemory and groupMemory.key==memoryKey then group=groupMemory.group;H.Stats.groupSource="remembered" end
  ownGroup=group
 end
 H.Stats.sideSource=source;H.Stats.ownSeat=ownSeat;H.Stats.ownGroup=ownGroup
end
H.RefreshOwnGroup=refreshOwnGroup
local function resolveIdentity()
 local parent=warningHud and warningHud.Parent
 local mode=parent and parent:GetAttribute("MatchMode")
 if mode~="Online" and mode~="Bots" then return end
 local lp=Players.LocalPlayer
 local id=lp and tostring(lp.UserId)
 if id and not profileNames[id] then
  local fetched,profile=pcall(function()
   return game:GetService("HttpService"):JSONDecode(httpget("https://users.roblox.com/v1/users/"..id))
  end)
  if fetched and type(profile)=="table" and type(profile.displayName)=="string" then profileNames[id]=profile.displayName end
 end
end
task.spawn(function()
 while H.Running do
  if warningResolveNeeded and warningHud then
   warningResolveNeeded=false
   local ok,err=pcall(resolveIdentity)
   if not ok then H.Stats.identityError=tostring(err) end
  end
  task.wait(0.5)
 end
end)

local function bind()
 local lp=Players.LocalPlayer
 local pg=lp and lp:FindFirstChild("PlayerGui")
 local ui=pg and pg:FindFirstChild("PoolGameUI")
 local hud=ui and ui:FindFirstChild("Hud")
 warningHud=hud
 local context=tostring(hud and hud.Address)
 if context~=warningContext then
  warningContext=context;warningGroupSignature=nil;warningResolveNeeded=hud~=nil;ownGroup="Unknown";ownSeat=nil
 end
 refreshOwnGroup()
 local scene=workspace:FindFirstChild("PoolScene3D")
 local stick=scene and scene:FindFirstChild("CueStick")
 local cue=findCue(stick,true)
 cacheCueShape(stick,cue)
 H.Stats.sceneAddress=scene and scene.Address or nil
 H.Stats.cueShape=cueShapeMin and "ok" or "unavailable"
end
H.BindScene=bind
local function collect()
 local ok,err=pcall(bind)
 H.Stats.collectError=not ok and tostring(err) or nil
end
collect()
task.spawn(function() while H.Running do collect();task.wait(0.4) end end)

local DIAMOND_SPANS={{"Diamond1","Diamond11","X",66},{"Diamond2","Diamond12","X",66},{"Diamond14","Diamond13","X",95.5},
 {"Diamond1","Diamond2","Y",51.5},{"Diamond17","Diamond13","Y",22}}
local guiCache={}
local function buildGuiCache(root)
 local c={root=root,address=root.Address,diamonds={},refreshed=tick()}
 for _,span in ipairs(DIAMOND_SPANS) do
  for i=1,2 do
   if not c.diamonds[span[i]] then c.diamonds[span[i]]=root:FindFirstChild(span[i]) end
  end
 end
 c.cloth=root:FindFirstChild("Cloth")
 c.balls=root:FindFirstChild("Balls")
 local overlay=root:FindFirstChild("Overlay")
 local aim=overlay and overlay:FindFirstChild("AimOverlay")
 c.ghost=aim and aim:FindFirstChild("Ghost")
 return c
end
local function readGui(ui)
 local tableFrame=ui and ui:FindFirstChild("Table")
 local root=tableFrame and tableFrame:FindFirstChild("PoolTable")
 if not root then guiCache={};return nil end
 if guiCache.address~=root.Address then guiCache=buildGuiCache(root) end
 return guiCache
end
local cachedView=nil
local ballRadii={}
local function refreshSlowState()
 local lp=Players.LocalPlayer
 local pg=lp and lp:FindFirstChild("PlayerGui")
 local ui=pg and pg:FindFirstChild("PoolGameUI")
 cachedView=ui and ui:GetAttribute("ViewMode") or nil
 local tableFrame=ui and ui:FindFirstChild("Table")
 local root=tableFrame and tableFrame:FindFirstChild("PoolTable")
 if root and (guiCache.address~=root.Address or tick()-(guiCache.refreshed or 0)>2) then guiCache=buildGuiCache(root) end
 local scene=workspace:FindFirstChild("PoolScene3D")
 local holder=scene and scene:FindFirstChild("Balls")
 local radii={}
 if holder then
  for _,part in ipairs(holder:GetChildren()) do
   local size=part.Size
   if size and finite(size.X) and size.X>0.6 and size.X<8 then radii[part.Name]=size.X/2 end
  end
 end
 ballRadii=radii
end
task.spawn(function()
 while H.Running do
  local ok,err=pcall(refreshSlowState)
  H.Stats.slowStateError=not ok and tostring(err) or nil
  task.wait(0.4)
 end
end)
local function calibrate(gui)
 local root=gui.root
 local estimates={}
 local diamonds=gui.diamonds or {}
 for _,span in ipairs(DIAMOND_SPANS) do
  local a,b=diamonds[span[1]],diamonds[span[2]]
  local pa,pb=a and a.AbsolutePosition,b and b.AbsolutePosition
  if pa and pb then
   local k=((span[3]=="X") and (pb.X-pa.X) or (pb.Y-pa.Y))/span[4]
   if finite(k) and k>0.5 and k<500 then estimates[#estimates+1]=k end
  end
 end
 if #estimates==0 then return nil,"2D table scale unavailable" end
 table.sort(estimates)
 local k=estimates[math.floor((#estimates+1)/2)]
 local origin=root.AbsolutePosition
 if not origin or not finite(origin.X) or not finite(origin.Y) then return nil,"2D table position unavailable" end
 local cal={k=k,ax=origin.X+51.5*k,ay=origin.Y+29.5*k,spread=estimates[#estimates]/estimates[1]}
 local cloth=gui.cloth and gui.cloth.AbsolutePosition
 if cloth and finite(cloth.X) and finite(cloth.Y) then
  cal.clothError=math.abs(cloth.X-(cal.ax-44*k))+math.abs(cloth.Y-(cal.ay-22*k))
 end
 return cal
end
H.Calibrate=calibrate
local function insidePocket(p)
 for _,k in ipairs(pockets) do
  local qx,qy=p.x-k.c.x,p.y-k.c.y
  if qx*k.n.x+qy*k.n.y>=k.depth and math.abs(qx*k.tx+qy*k.ty)<=k.half then return true end
 end
 return false
end
local function onTable(p) return math.abs(p.x)<=46 and math.abs(p.y)<=24 and not insidePocket(p) end
local function readBalls3D(scene)
 local holder=scene:FindFirstChild("Balls")
 if not holder then return nil,"No 3D balls folder" end
 local raw={}
 for _,part in ipairs(holder:GetChildren()) do
  local id=tonumber(part.Name:match("^Ball(%d+)$"))
  if id and id<=15 then
   local p=part.Position
   if p and finite(p.X) and finite(p.Y) and finite(p.Z) then
    local r=ballRadii[part.Name] or BALL_RADIUS
    local t=part.Transparency
    if not (finite(t) and t>=0.99 and t<=1.0001) then
     raw[#raw+1]={id=id,p=V(p.X,-p.Z),y=p.Y,r=r}
    end
   end
  end
 end
 local planeY=TABLE_Y
 local count=0
 for _,b in ipairs(raw) do if math.abs(b.y-planeY)<0.6 then count=count+1 end end
 if count==0 and #raw>0 then
  local bestCount=0
  for _,a in ipairs(raw) do
   local n=0
   for _,b in ipairs(raw) do if math.abs(a.y-b.y)<0.6 then n=n+1 end end
   if n>bestCount or (n==bestCount and a.y>planeY) then bestCount=n;planeY=a.y end
  end
 end
 local balls={}
 for _,b in ipairs(raw) do
  if math.abs(b.y-planeY)<0.6 and onTable(b.p) then balls[#balls+1]={id=b.id,p=b.p,r=b.r} end
 end
 frame.tableY=planeY
 if #balls==0 then return nil,"No balls on the 3D table" end
 return balls
end
local function readBalls2D(holder,cal)
 local balls={}
 for _,f in ipairs(holder:GetChildren()) do
  local id=tonumber(f.Name:match("^Ball(%d+)$"))
  if id and id<=15 then
   local tl=f.AbsolutePosition
   if tl and finite(tl.X) and finite(tl.Y) then
    local half=BALL_RADIUS*cal.k
    local p=V((tl.X+half-cal.ax)/cal.k,(cal.ay-(tl.Y+half))/cal.k)
    if finite(p.x) and finite(p.y) and onTable(p) then balls[#balls+1]={id=id,p=p,r=BALL_RADIUS} end
   end
  end
 end
 if #balls==0 then return nil,"No balls on the 2D table" end
 return balls
end
local function firstHit(white,direction,balls)
 local p,d=white.p,direction
 local distance=200
 local target=nil
 for _,b in ipairs(balls) do
  if b.id~=0 then
   local t=timeCircle(b.p.x-p.x,b.p.y-p.y,-d.x,-d.y,white.r+b.r,distance)
   if t and t<distance then distance=t;target=b.id end
  end
 end
 for _,r in ipairs(rails) do
  local t=timeRail(p,d,white.r,r,distance)
  if t and t<distance then distance=t;target=nil end
 end
 for _,j in ipairs(jaws) do
  local t=timeCircle(j.x-p.x,j.y-p.y,-d.x,-d.y,white.r,distance)
  if t and t<distance then distance=t;target=nil end
 end
 for _,k in ipairs(pockets) do
  local t=timePocket(p,d,k,distance)
  if t and t<distance then distance=t;target=nil end
 end
 return distance,target
end
local function cueAim(cue,white)
 local cp,cf=cue.Position,cue.CFrame
 if not cp or not cf or not finite(cp.X) or not finite(cp.Z) then return nil end
 local toward=V(white.p.x-cp.X,white.p.y+cp.Z)
 local tl=length(toward)
 if tl<0.5 or tl>150 then return nil end
 local tu=mul(toward,1/tl)
 local axisIndex=cueShapeAxis or longAxis(cue)
 local axis=axisVector(cf,axisIndex)
 local result={toward=toward,towardUnit=tu}
 if axis and finite(axis.X) and finite(axis.Z) then
  local a=V(axis.X,-axis.Z)
  if length(a)>0.9 then
   a=unit(a);result.axis=a
   local d=dot(a,tu)
   if math.abs(d)>0.985 then result.direction=d<0 and mul(a,-1) or a end
  end
 end
 return result
end
local function ghostAim(gui,cal,white,balls)
 local tl=gui.ghost.AbsolutePosition
 if not tl or not finite(tl.X) or not finite(tl.Y) then return nil end
 local half=GHOST_HALF*cal.k
 local g=V((tl.X+half-cal.ax)/cal.k,(cal.ay-(tl.Y+half))/cal.k)
 local d=sub(g,white.p);local m=length(d)
 if m<0.2 or m>120 then return nil end
 local direction=mul(d,1/m)
 local distance=firstHit(white,direction,balls)
 if math.abs(distance-m)>0.75 then return nil end
 return direction
end
local function angleBetween(a,b) return math.deg(math.acos(math.clamp(dot(a,b),-1,1))) end
local function snapshot()
 local st=H.Stats
 latest=nil
 st.previewStatus="Waiting for pool table"
 if not H.Enabled then currentBalls={};return end
 local lp=Players.LocalPlayer
 local pg=lp and lp:FindFirstChild("PlayerGui")
 local ui=pg and pg:FindFirstChild("PoolGameUI")
 local hud=ui and ui:FindFirstChild("Hud")
 local view=H.ForceView or cachedView
 local scene=view~="2D" and workspace:FindFirstChild("PoolScene3D") or nil
 local cam=workspace.CurrentCamera
 local vp=cam and cam.ViewportSize
 frame.vw=vp and finite(vp.X) and vp.X>0 and vp.X or 1920
 frame.vh=vp and finite(vp.Y) and vp.Y>0 and vp.Y or 1080
 frame.mode=(view=="2D" or not scene) and "2D" or "3D"
 frame.tableY=TABLE_Y
 st.viewMode=frame.mode
 local gui=ui and readGui(ui)
 local cal,calError=nil,"2D table missing"
 if gui then
  local ok,c,e=pcall(calibrate,gui)
  if ok then cal,calError=c,e else calError=tostring(c) end
 end
 frame.cal=cal
 st.calibration=cal and string.format("k=%.2f spread=%.3f cloth=%.1f",cal.k,cal.spread,cal.clothError or -1) or calError
 local balls,ballError,ballSource=nil,nil,nil
 if scene then
  local ok,b,e=pcall(readBalls3D,scene)
  if ok then balls,ballError=b,e else ballError=tostring(b) end
  ballSource="3D parts"
 end
 if not balls and gui and gui.balls and cal then
  local ok,b,e=pcall(readBalls2D,gui.balls,cal)
  if ok then balls,ballError=b,e else ballError=tostring(b) end
  ballSource="2D table"
 end
 local key=scene and ("3D:"..tostring(scene.Address)) or (gui and ("2D:"..tostring(gui.root.Address))) or nil
 if key~=sourceKey then
  sourceKey=key;epoch=epoch+1;preview=nil;guideCache=nil;previous={};quietAt=tick()+0.18
  st.rebinds=(st.rebinds or 0)+1
 end
 if not balls then
  H.Waiting=true;currentBalls={};st.ballSource=nil
  st.previewStatus=ballError or "Waiting for pool table";return
 end
 H.Waiting=false;st.ballSource=ballSource;st.ballCount=#balls
 local white,moved=nil,false
 for _,b in ipairs(balls) do
  if b.id==0 then white=b end
  local last=previous[b.id]
  if last and length(sub(b.p,last))>0.015 then moved=true end
  previous[b.id]=b.p
 end
 table.sort(balls,function(a,b) return a.id<b.id end)
 currentBalls=balls
 if moved then quietAt=tick()+0.18 end
 if not white then st.previewStatus="Cue ball not on table";return end
 if tick()<quietAt then st.previewStatus="Balls moving";return end
 local stick=scene and scene:FindFirstChild("CueStick")
 local cue=stick and findCue(stick,false)
 local aim=nil
 if cue and frame.mode=="3D" then
  local ok,a=pcall(cueAim,cue,white)
  if ok then aim=a end
 end
 local ghostDirection=nil
 if gui and gui.ghost and cal then
  local ok,d=pcall(ghostAim,gui,cal,white,balls)
  if ok then ghostDirection=d end
 end
 local direction,aimSource=nil,nil
 if aim and aim.direction then direction,aimSource=aim.direction,"cue"
 elseif ghostDirection then direction,aimSource=ghostDirection,"game ghost"
 elseif aim and aim.towardUnit then direction,aimSource=aim.towardUnit,"cue position" end
 st.aimSource=aimSource
 st.aimCheck=(aim and aim.direction and ghostDirection) and string.format("cue/ghost %.2f deg",angleBetween(aim.direction,ghostDirection)) or nil
 if not direction then
  st.previewStatus=frame.mode=="2D" and "Aim unknown in 2D (turn on game predictions)" or "Aim direction unavailable";return
 end
 local percent=nil
 local powerLabel=hud and hud:FindFirstChild("PowerLabel")
 if powerLabel then
  local text=powerLabel.Text
  percent=type(text)=="string" and tonumber(text:match("([%d%.]+)")) or nil
  if percent and not finite(percent) then percent=nil end
  if percent then percent=math.clamp(percent,0,100) end
 end
 local widget=hud and hud:FindFirstChild("SpinWidget")
 local spin=selectedSpin(widget)
 st.spinX=spin.x;st.spinY=spin.y
 local isBreak=#balls==16
 for _,b in ipairs(balls) do if b.id~=0 and (b.p.x<20 or b.p.x>32 or math.abs(b.p.y)>7) then isBreak=false end end
 local rawPower=nil
 if percent and aim and aim.axis and cueShapeAxis then
  rawPower=powerFromCue(dot(aim.toward,aim.axis),cueShapeMin,cueShapeMax,white.r,percent)
 end
 local selectedPower
 if rawPower then selectedPower=rawPower;st.powerSource="cue pullback"
 elseif percent then selectedPower=percent/100;st.powerSource="power label"
 else selectedPower=1;st.powerSource="unknown (100%)" end
 selectedPower=math.clamp(selectedPower,MIN_POWER,1)
 st.precisePowerPercent=selectedPower*100
 local parts={tostring(sourceKey),string.format("%.6f,%.6f:%.4f,%.4f",direction.x,direction.y,spin.x,spin.y)}
 for _,b in ipairs(balls) do parts[#parts+1]=string.format("%d:%.4f,%.4f,%.4f",b.id,b.p.x,b.p.y,b.r) end
 local base=table.concat(parts,"|")
 latest={balls=balls,direction=direction,spin=spin,power=selectedPower,
  percent=percent or 100,isBreak=isBreak,base=base,key=base..":"..string.format("%.5f",selectedPower),epoch=epoch}
 st.powerPercent=percent;st.previewStatus="Computing preview"
end
H.Simulate=simulateAll
local lastDump=0
function H.Dump(reason)
 local rows={"8-Ball helper diagnostics","version="..tostring(H.Version),"reason="..tostring(reason or "manual"),string.format("clock=%.1f",tick())}
 local keys={}
 for k in pairs(H.Stats) do keys[#keys+1]=k end
 table.sort(keys)
 for _,k in ipairs(keys) do rows[#rows+1]=k.."="..tostring(H.Stats[k]) end
 local ok,err=pcall(writefile,"8ball_diag.txt",table.concat(rows,"\n"))
 H.Stats.lastDump=ok and "8ball_diag.txt" or ("dump failed: "..tostring(err))
 return ok
end
local function autoDump(reason)
 if tick()-lastDump<15 then return end
 lastDump=tick();H.Dump(reason)
end
task.spawn(function()
 while H.Running do
  local input=latest
  if H.Enabled and input and (not preview or preview.key~=input.key) then
   local start=tick()
   local ok,err=pcall(function()
    local guide=guideCache and guideCache.base==input.base and guideCache.result or simulateAll(input,1,true)
    if not guide then return end
    guideCache={base=input.base,result=guide}
    if latest and latest.base==input.base and latest.epoch==input.epoch then input=latest end
    local actual=input.power==1 and guide or simulateAll(input,input.power,true)
    if actual and H.Running and epoch==input.epoch and latest and latest.base==input.base then
     preview={key=input.key,base=input.base,guide=guide,actual=actual,spin=input.spin,power=input.power}
     H.Stats.collisions=actual.collisions;H.Stats.settled=actual.settled
     H.Stats.computeMs=math.floor((tick()-start)*1000)
     H.Stats.target=guide.firstContact
     H.Stats.linePowerPercent=100;H.Stats.extraLinePowerPercent=input.power*100;H.Stats.markerPowerPercent=input.power*100
    end
   end)
   H.Stats.simulationError=not ok and tostring(err) or nil
   if not ok then autoDump("simulation: "..tostring(err)) end
  end
  task.wait(0.015)
 end
end)
local function world(p) return Vector3.new(p.x,frame.tableY or TABLE_Y,-p.y) end
local function sanePoint(x,y)
 return finite(x) and finite(y) and x>-frame.vw and x<frame.vw*2 and y>-frame.vh and y<frame.vh*2
end
local function toScreen(p)
 if frame.mode=="3D" then
  local s,visible=WorldToScreen(world(p))
  if visible and s and sanePoint(s.X,s.Y) then return s.X,s.Y end
 end
 local c=frame.cal
 if c then
  local x,y=c.ax+c.k*p.x,c.ay-c.k*p.y
  if sanePoint(x,y) then return x,y end
 end
 return nil
end
H.ToScreen=toScreen
local function drawLine(line,segment,color)
 local ax,ay=toScreen(segment.a)
 if not ax then return false end
 local bx,by=toScreen(segment.b)
 if not bx then return false end
 line.Color=color;line.From=Vector2.new(ax,ay);line.To=Vector2.new(bx,by);show(line)
 return true
end
local function project(ball)
 local x,y=toScreen(ball.p)
 if not x then return nil end
 local qx,qy=toScreen(add(ball.p,V(ball.r,0)))
 if not qx then return nil end
 local radius=math.sqrt((qx-x)^2+(qy-y)^2)
 if not finite(radius) then return nil end
 return Vector2.new(x,y),math.clamp(radius,1,400)
end
local function drawCircle(circle,ball,color)
 local p,radius=project(ball)
 if not p then return false end
 circle.Position=p;circle.Radius=math.max(3,radius);circle.Color=color;show(circle)
 return true
end
local function drawBadge(drawing,ball,message,color)
 local p,radius=project(ball)
 if not p then return false end
 radius=math.max(5,radius+3)
 if color then drawing.ring.Color=color;drawing.text.Color=color end
 drawing.ring.Position=p;drawing.ring.Radius=radius;show(drawing.ring)
 drawing.text.Position=Vector2.new(p.X,p.Y-radius-20)
 drawing.text.Text=message;show(drawing.text)
 return true
end
local KEY_X,KEY_O,KEY_SPACE,KEY_F7=Enum.KeyCode.X.Value,Enum.KeyCode.O.Value,Enum.KeyCode.Space.Value,Enum.KeyCode.F7.Value
local held={}
local removeAt=nil
local function handleKey(key)
 if held[key] then return end
 held[key]=true
 if key==KEY_X then H.Enabled=not H.Enabled
 elseif key==KEY_SPACE then H.ShowCollisions=not H.ShowCollisions
 elseif key==KEY_F7 then H.Dump("F7")
 elseif key==KEY_O then removeAt=tick()+REMOVE_HOLD end
end
local function releaseKey(key)
 held[key]=nil
 if key==KEY_O then removeAt=nil end
end
H.HandleKey=handleKey
H.ReleaseKey=releaseKey
connections[#connections+1]=UIS.InputBegan:Connect(function(input) pcall(handleKey,input.KeyCode) end)
connections[#connections+1]=UIS.InputEnded:Connect(function(input) pcall(releaseKey,input.KeyCode) end)
local elapsed,lastLabel=0,nil
local function setLabel(text)
 if #text>LABEL_MAX then text=text:sub(1,LABEL_MAX-3).."..." end
 if text~=lastLabel then label.Text=text;lastLabel=text end
 H.Stats.labelText=text
end
H.ImmediateGuide=function(input)
 local white=nil
 for _,b in ipairs(input.balls) do if b.id==0 then white=b;break end end
 if not white then return nil end
 local distance,target=firstHit(white,input.direction,input.balls)
 return {a=white.p,b=add(white.p,mul(input.direction,distance))},target
end
local function render()
 snapshot()
 H.CurrentInput=latest
 local mainCount,extraCount,markerCount,blueCount=0,0,0,0
 H.Stats.projectedLines=0
 local ready=eightIsReady(currentBalls,ownGroup)
 local nine=ownGroup=="NineBall"
 local lowest=nine and lowestBall(currentBalls) or nil
 local eightRisk=not nine and not ready
 H.Stats.eightReady=ready;H.Stats.eightWarning=false;H.Stats.eightLineWarning=false;H.Stats.eightIndicator=false;H.Stats.scratchWarning=false;H.Stats.safeBadges=0;H.Stats.opponentBadges=0;H.Stats.predictedPots=0
 H.Stats.nineBall=nine;H.Stats.lowestBall=lowest;H.Stats.nineFoul=false
 if H.Enabled and latest and preview and preview.base==latest.base then
  H.Stats.previewStatus="Ready"
  local guide,actual=preview.guide,preview.actual
  local live={}
  for _,ball in ipairs(currentBalls) do live[ball.id]=ball end
  local primary=guide.firstContact
  local eightDanger=primary==8 and eightRisk
  local nineFoul=nine and primary~=nil and lowest~=nil and primary~=lowest
  H.Stats.nineFoul=nineFoul
  local mainColor=(eightDanger or nineFoul) and red or yellow
  local function mainLine(s)
   if mainCount<#lines then
    mainCount=mainCount+1
    if drawLine(lines[mainCount],s,mainColor) then
     H.Stats.projectedLines=H.Stats.projectedLines+1
     if eightDanger then H.Stats.eightLineWarning=true end
    end
   end
  end
  local cueGuide=guide.byId[0]
  if cueGuide then for _,s in ipairs(cueGuide.paths) do if not s.afterContact then mainLine(s) end end end
  local target=primary and guide.byId[primary]
  if target then for _,s in ipairs(target.paths) do mainLine(s) end end
  if guide.contact and not eightDanger and not nineFoul and cueGuide then drawCircle(ghost,{p=guide.contact,r=cueGuide.r},yellow) end
  local white=actual.byId[0]
  if white and white.pocketed and live[0] then
   H.Stats.scratchWarning=drawBadge(warningDrawings.white,live[0],"WARNING")
  end
  local eight=actual.byId[8]
  if eight and eight.pocketed and eightRisk and live[8] then
   H.Stats.eightWarning=drawBadge(warningDrawings.eight,live[8],"WARNING")
  end
  for _,ball in ipairs(currentBalls) do
   local predicted=actual.byId[ball.id]
   if ball.id~=0 and predicted and predicted.pocketed and pocketDrawings[ball.id] then
    H.Stats.predictedPots=H.Stats.predictedPots+1
    if safePocket(actual,ball.id,ownGroup,ready,lowest) then
     if drawBadge(pocketDrawings[ball.id],ball,"SAFE",green) then H.Stats.safeBadges=H.Stats.safeBadges+1 end
    elseif ballSide(ball.id,ownGroup,ready)=="Opponent" then
     if drawBadge(pocketDrawings[ball.id],ball,"!",cyan) then H.Stats.opponentBadges=H.Stats.opponentBadges+1 end
    end
   end
  end
  for _,ball in ipairs(actual.balls) do
   if markers[ball.id+1] and showBallPreview(ball,primary,H.ShowCollisions,not eightRisk) then
    local color=markerColor(ball,primary,ownGroup,ready,H.ShowCollisions)
    if drawCircle(markers[ball.id+1],ball,color) then
     markerCount=markerCount+1
     if ball.id==8 then H.Stats.eightIndicator=true end
     if H.ShowCollisions and ball.id~=primary and ballSide(ball.id,ownGroup,ready)=="Opponent" and not ball.pocketed then blueCount=blueCount+1 end
    end
   end
  end
  for _,ball in ipairs(actual.balls) do
   if ball.id~=0 and ball.moved and ball.id~=primary and (H.ShowCollisions or (ball.id==8 and eightRisk)) then
    local color=pathColor(ball.id,ownGroup,ready)
    for _,s in ipairs(ball.paths) do
     if extraCount>=#extraLines then break end
     extraCount=extraCount+1
     if drawLine(extraLines[extraCount],s,color) and ball.id==8 and eightRisk then H.Stats.eightLineWarning=true end
    end
   end
  end
 end
 if H.Enabled and latest and (not preview or preview.base~=latest.base) then
  local segment,target=H.ImmediateGuide(latest)
  if segment then
   local danger=(target==8 and eightRisk) or (nine and target and lowest and target~=lowest)
   if drawLine(lines[1],segment,danger and red or yellow) then
    mainCount=1;H.Stats.projectedLines=1
   end
   H.Stats.previewStatus="Aiming (first segment)"
  end
 end
 if H.Enabled and latest and H.Stats.previewStatus=="Ready" and mainCount>0 and H.Stats.projectedLines==0 then
  H.Stats.previewStatus="Lines off screen ("..frame.mode.." view)"
 end
 endFrame()
 local text=H.Waiting and "Waiting for pool table... | Hold O: remove" or not H.Enabled and "Preview paused | X resume | Hold O: remove"
  or ("Main 100% | Balls + extra lines: "..tostring(H.Stats.powerPercent or "?").."% | SPACE: extra lines "..(H.ShowCollisions and "ON" or "OFF").." | X toggle | Hold O: remove")
 if H.ShowCollisions and H.Enabled and not H.Waiting and (ownGroup=="Solid" or ownGroup=="Stripe") then
  text=text.." | Pink: yours / Blue: opponent"
 end
 if nine and H.Enabled and not H.Waiting then
  text=text.." | 9-Ball: hit "..(lowest and tostring(lowest) or "?").." first"
 end
 if ownSeat then text=text.." | Your side: "..(ownSeat==1 and "Left" or "Right")
 else text=text.." | "..(H.Stats.sideSource or "Waiting for user identity") end
 if H.Enabled and not H.Waiting then
  if frame.mode=="2D" then text=text.." | 2D view" end
  if H.Stats.aimSource and H.Stats.aimSource~="cue" then text=text.." | aim: "..H.Stats.aimSource end
 end
 if H.Stats.spinError then text=text.." | "..H.Stats.spinError end
 if H.Stats.simulationError then text=text.." | Simulation: "..H.Stats.simulationError
 elseif H.Stats.collectError then text=text.." | Table: "..H.Stats.collectError
 elseif H.Enabled and H.Stats.previewStatus~="Ready" then text=text.." | "..(H.Stats.previewStatus or "Loading") end
 setLabel(text)
 H.Stats.frames=(H.Stats.frames or 0)+1;H.Stats.visible=mainCount;H.Stats.extraPaths=extraCount;H.Stats.actualPaths=mainCount+extraCount;H.Stats.markers=markerCount;H.Stats.blueMarkers=blueCount
end
local renderErrors=0
connections[#connections+1]=RS.RenderStepped:Connect(function(dt)
 if not H.Running then return end
 if removeAt and tick()>=removeAt then
  removeAt=nil
  local ok,down=pcall(function() return UIS:IsKeyDown(KEY_O) end)
  if not ok or down then H.Stop();return end
 end
 elapsed=elapsed+(finite(dt) and dt or 0.016)
 if elapsed<0.03 then return end
 elapsed=0
 local started=tick()
 local ok,err=pcall(render)
 H.Stats.renderMs=math.floor((tick()-started)*10000)/10
 if not ok then
  renderErrors=renderErrors+1
  H.Stats.error=tostring(err);H.Stats.renderErrors=renderErrors
  hide()
  pcall(setLabel,"Pool helper error: "..tostring(err).." | F7: save diagnostics | Hold O: remove")
  autoDump("render: "..tostring(err))
 else H.Stats.error=nil end
end)
print("8-Ball Duels helper "..H.Version.." loaded. SPACE extra lines / X toggle / F7 diagnostics / hold O remove.")
