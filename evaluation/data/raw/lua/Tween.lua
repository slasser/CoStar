-- Tween.lua
-- Module adding the Tweener and Timer objects, and the easing equations.
--
-- Last modified for v1.2.0
-- Copyright © 2013 Florent POUJOL, published under the MIT licence.

function DaneelConfigModuleTween()
    Daneel.Tween = DaneelTween

    return {
        tween = {
            tweener = {
                isEnabled = true, -- a disabled tweener won't update but the function like Play(), Pause(), Complete(), Destroy() will have no effect
                isPaused = false,

                delay = 0.0, -- delay before the tweener starts (in the same time unit as the duration (durationType))
                duration = 0.0, -- time or frames the tween (or one loop) should take (in durationType unit)
                durationType = "time", -- the unit of time for delay, duration, elapsed and fullElapsed. Can be "time", "realTime" or "frame"

                startValue = nil, -- it will be the current value of the target's property
                endValue = 0.0,

                loops = 0, -- number of loops to perform (-1 = infinite)
                loopType = "simple", -- type of loop. Can be "simple" (X to Y, repeat), "yoyo" (X to Y, Y to X, repeat)
                
                easeType = "linear", -- type of easing, check the doc or the end of the "Daneel/Lib/Easing" script for all possible values
                
                isRelative = false, -- If false, tween the value TO endValue. If true, tween the value BY endValue.

                destroyOnComplete = true, -- tell wether to destroy the tweener (true) when it completes
                destroyOnSceneLoad = true, -- tell wether to destroy the tweener (true) or keep it 'alive' (false) when the scene is changing

                ------------
                -- "read-only" properties or properties the user has no interest to change the value of

                Id = -1, -- can be anything, not restricted to numbers
                hasStarted = false,
                isCompleted = false,
                elapsed = 0, -- elapsed time or frame (in durationType unit), delay excluded
                fullElapsed = 0, -- elapsed time, including loops, excluding delay
                completedLoops = 0,
                diffValue = 0.0, -- endValue - startValue
                value = 0.0, -- current value (between startValue and endValue)
            },
        },

        daneelObjects = {
            ["Daneel.Tween.Tweener"] = Daneel.Tween.Tweener,
        },
    }
end

function DaneelAwakeModuleTween()
    -- destroy and sanitize the tweeners when the scene loads
    Daneel.Event.Listen("OnSceneLoad", function()
        for id, tweener in pairs(Daneel.Tween.Tweener.tweeners) do
            if not (tweener.destroyOnSceneLoad == false) then -- wil destroy the tweener even when the property is nil
                tweener:Destroy()
            end
        end
    end)
end

----------------------------------------------------------------------------------
-- Tween

DaneelTween = {}

-- Allow to get the target's "property" even if it is virtual and normally handled via getter/setter.
local function GetTweenerProperty(tweener)
    Daneel.Debug.StackTrace.BeginFunction("GetTweenerProperty", tweener)
    local value = nil
    if tweener.target ~= nil then
        value = tweener.target[tweener.property]
        if value == nil then
            local functionName = "Get"..tweener.property:ucfirst()
            if tweener.target[functionName] ~= nil then
                value = tweener.target[functionName](tweener.target)
            end
        end
    end
    Daneel.Debug.StackTrace.EndFunction()
    return value
end

-- Allow to set the target's "property" even if it is virtual and normally handled via getter/setter.
local function SetTweenerProperty(tweener, value)
    Daneel.Debug.StackTrace.BeginFunction("SetTweenerProperty", tweener, value)
    if tweener.target ~= nil then
        if tweener.target[tweener.property] == nil then
            local functionName = "Set"..tweener.property:ucfirst()
            if tweener.target[functionName] ~= nil then
                tweener.target[functionName](tweener.target, tweener.property)
            end
        else
            tweener.target[tweener.property] = value
        end
    end
    Daneel.Debug.StackTrace.EndFunction()
end


function DaneelTween.Update()
    for id, tweener in pairs( Daneel.Tween.Tweener.tweeners ) do
        if tweener.isEnabled == true and tweener.isPaused == false and tweener.isCompleted == false and tweener.duration > 0 then

            local deltaDuration = Daneel.Time.deltaTime
            if tweener.durationType == "realTime" then
                deltaDuration = Daneel.Time.realDeltaTime
            elseif tweener.durationType == "frame" then
                deltaDuration = 1
            end

            if deltaDuration > 0 then
                if tweener.delay <= 0 then
                    -- no more delay before starting the tweener, update the tweener
                    if tweener.hasStarted == false then
                        -- firt loop for this tweener
                        tweener.hasStarted = true
                        
                        if tweener.startValue == nil then
                            if tweener.target ~= nil then
                                tweener.startValue = GetTweenerProperty( tweener )
                            else
                                error( "Daneel.Tween.Update() : startValue is nil but no target is set for tweener with Id '" .. tweener.Id .. "'" )
                            end
                        elseif tweener.target ~= nil then
                            -- when start value and a target are set move the target to startValue before updating the tweener
                            SetTweenerProperty( tweener, tweener.startValue )
                        end
                        tweener.value = tweener.startValue

                        if tweener.isRelative == true then
                            tweener.diffValue = tweener.endValue
                        else
                            tweener.diffValue = tweener.endValue - tweener.startValue
                        end

                        Daneel.Event.Fire( tweener, "OnStart", tweener )
                    end
                    
                    -- update the tweener
                    tweener:Update( deltaDuration )
                else
                    tweener.delay = tweener.delay - deltaDuration
                end -- end if tweener.delay <= 0


                if tweener.isCompleted == true then
                    tweener.completedLoops = tweener.completedLoops + 1
                    if tweener.loops == -1 or tweener.completedLoops < tweener.loops then
                        tweener.isCompleted = false
                        tweener.elapsed = 0

                        if tweener.loopType:lower() == "yoyo" then
                            local startValue = tweener.startValue
                            
                            if tweener.isRelative then
                                tweener.startValue = tweener.value
                                tweener.endValue = -tweener.endValue
                                tweener.diffValue = tweener.endValue
                            else
                                tweener.startValue = tweener.endValue
                                tweener.endValue = startValue
                                tweener.diffValue = -tweener.diffValue
                            end

                        elseif tweener.target ~= nil then
                            SetTweenerProperty( tweener, tweener.startValue )
                        end

                        tweener.value = tweener.startValue
                        Daneel.Event.Fire( tweener, "OnLoopComplete", tweener )

                    else
                        Daneel.Event.Fire( tweener, "OnComplete", tweener )
                        if tweener.destroyOnComplete and tweener.Destroy ~= nil then
                            -- tweener.Destroy may be nil if a new scene is loaded from the OnComplete callback
                            -- the tweener will have been destroyed already an its metatable stripped
                            tweener:Destroy()
                        end
                    end
                end
            end -- end if deltaDuration > 0
        end -- end if tweener.isEnabled == true
    end -- end for tweeners
end

DaneelUpdateModuleTween = DaneelTween.Update


----------------------------------------------------------------------------------
-- Tweener

DaneelTween.Tweener = { tweeners = {} }
DaneelTween.Tweener.__index = DaneelTween.Tweener
setmetatable(DaneelTween.Tweener, { __call = function(Object, ...) return Object.New(...) end })

function DaneelTween.Tweener.__tostring(tweener)
    return "Tweener: " .. tweener.Id
end

--- Creates a new tweener via one of the three allowed constructors : <br>
-- Tweener.New(target, property, endValue, duration[, params]) <br>
-- Tweener.New(startValue, endValue, duration[, params]) <br>
-- Tweener.New(params)
-- @param target (table) An object.
-- @param property (string) The name of the propertty to animate.
-- @param endValue (number) The value the property should have at the end of the duration.
-- @param duration (number) The time or frame it should take for the property to reach endValue.
-- @param params [optional] (table) A table of parameters.
-- @return (Tweener) The Tweener.
function DaneelTween.Tweener.New(target, property, endValue, duration, params)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.Tween.Tweener.New", target, property, endValue, duration, params)
    local errorHead = "Daneel.Tween.Tweener.New(target, property, endValue, duration[, params]) : "
    
    local tweener = table.copy(Daneel.Config.tween.tweener)
    setmetatable(tweener, Daneel.Tween.Tweener)
    tweener.Id = math.round( math.randomrange( 100000, 999999 ) )

    -- three constructors :
    -- target, property, endValue, duration[, params]
    -- startValue, endValue, duration[, params]
    -- params
    if type(target) == "number" then
        -- constructor n°2
        errorHead = "Daneel.Tween.Tweener.New(startValue, endValue, duration[, params]) : "
        Daneel.Debug.CheckArgType(endValue, "duration", "number", errorHead)
        Daneel.Debug.CheckOptionalArgType(duration, "params", "table", errorHead)

        tweener.startValue = target
        tweener.endValue = property
        tweener.duration = endValue
        if duration ~= nil then
            tweener:Set(duration)
        end
    elseif property == nil then
        -- constructor n°3
        Daneel.Debug.CheckArgType(target, "params", "table", errorHead)
        errorHead = "Daneel.Tween.Tweener.New(params) : "
        tweener:Set(target)
    else
        -- constructor n°1
        Daneel.Debug.CheckArgType(target, "target", "table", errorHead)
        Daneel.Debug.CheckArgType(property, "property", "string", errorHead)
        Daneel.Debug.CheckArgType(duration, "duration", "number", errorHead)
        Daneel.Debug.CheckOptionalArgType(params, "params", "table", errorHead)

        tweener.target = target
        tweener.property = property
        tweener.endValue = endValue
        tweener.duration = duration
        if params ~= nil then
            tweener:Set(params)
        end
    end
    
    Daneel.Tween.Tweener.tweeners[tweener.Id] = tweener
    Daneel.Debug.StackTrace.EndFunction()
    return tweener
end

-- Sets parameters in mass.
-- Should not be used after the tweener has been created.
-- That's why it is not in the function reference.
function DaneelTween.Tweener.Set(tweener, params)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.Tween.Tweener.Set", tweener, params)
    local errorHead = "Daneel.Tween.Tweener.Set(tweener, params) : "
    Daneel.Debug.CheckArgType(tweener, "tweener", "Daneel.Tween.Tweener", errorHead)

    for key, value in pairs(params) do
        tweener[key] = value
    end
    Daneel.Debug.StackTrace.EndFunction()
    return tweener
end

--- Unpause the tweener and fire the OnPlay event.
-- @param tweener (Daneel.Tween.Tweener) The tweener.
function DaneelTween.Tweener.Play(tweener)
    if tweener.isEnabled == false then return end
    Daneel.Debug.StackTrace.BeginFunction("Daneel.Tween.Tweener.Play", tweener)
    local errorHead = "Daneel.Tween.Tweener.Play(tweener) : "
    Daneel.Debug.CheckArgType(tweener, "tweener", "Daneel.Tween.Tweener", errorHead)

    tweener.isPaused = false
    Daneel.Event.Fire(tweener, "OnPlay", tweener)
    Daneel.Debug.StackTrace.EndFunction()
end

--- Pause the tweener and fire the OnPause event.
-- @param tweener (Daneel.Tween.Tweener) The tweener.
function DaneelTween.Tweener.Pause(tweener)
    if tweener.isEnabled == false then return end
    Daneel.Debug.StackTrace.BeginFunction("Daneel.Tween.Tweener.Pause", tweener)
    local errorHead = "Daneel.Tween.Tweener.Pause(tweener) : "
    Daneel.Debug.CheckArgType(tweener, "tweener", "Daneel.Tween.Tweener", errorHead)

    tweener.isPaused = true
    Daneel.Event.Fire(tweener, "OnPause", tweener)
    Daneel.Debug.StackTrace.EndFunction()
end

--- Completely restart the tweener.
-- @param tweener (Daneel.Tween.Tweener) The tweener.
function DaneelTween.Tweener.Restart(tweener)
    if tweener.isEnabled == false then return end
    Daneel.Debug.StackTrace.BeginFunction("Daneel.Tween.Tweener.Restart", tweener)
    local errorHead = "Daneel.Tween.Tweener.Restart(tweener) : "
    Daneel.Debug.CheckArgType(tweener, "tweener", "Daneel.Tween.Tweener", errorHead)

    tweener.elapsed = 0
    tweener.fullElapsed = 0
    tweener.completedLoops = 0
    tweener.isCompleted = false
    tweener.hasStarted = false
    local startValue = tweener.startValue
    if tweener.loopType == "yoyo" and tweener.completedLoops % 2 ~= 0 then -- the current loop is Y to X, so endValue and startValue are inversed
        startValue = tweener.endValue
    end
    if tweener.target ~= nil then
        SetTweenerProperty(tweener, startValue)
    end
    tweener.value = startValue
    Daneel.Debug.StackTrace.EndFunction()
end

--- Complete the tweener fire the OnComple event.
-- @param tweener (Daneel.Tween.Tweener) The tweener.
function DaneelTween.Tweener.Complete( tweener )
    if tweener.isEnabled == false or tweener.loops == -1 then return end
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.Tween.Tweener.Complete", tweener )
    local errorHead = "Daneel.Tween.Tweener.Complete( tweener ) : "
    Daneel.Debug.CheckArgType( tweener, "tweener", "Daneel.Tween.Tweener", errorHead )

    tweener.isCompleted = true
    local endValue = tweener.endValue
    if tweener.loopType == "yoyo" then
        if
            (tweener.loops % 2 == 0 and tweener.completedLoops % 2 == 0) or -- endValue must be original startValue (because of even number of loops) | current X to Y loop, 
            (tweener.loops % 2 ~= 0 and tweener.completedLoops % 2 ~= 0) -- endValue must be the original endValue but the current loop is Y to X, so endValue and startValue are inversed
        then
            endValue = tweener.startValue
        end
    end
    if tweener.target ~= nil then
        SetTweenerProperty( tweener, endValue )
    end
    tweener.value = endValue
    
    Daneel.Event.Fire( tweener, "OnComplete", tweener )
    if tweener.destroyOnComplete then
        tweener:Destroy()
    end

    Daneel.Debug.StackTrace.EndFunction()
end

--- Destroy the tweener.
-- @param tweener (Daneel.Tween.Tweener) The tweener.
function DaneelTween.Tweener.Destroy( tweener )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.Tween.Tweener.Destroy", tweener )
    local errorHead = "Daneel.Tween.Tweener.Destroy( tweener ) : "
    Daneel.Debug.CheckArgType( tweener, "tweener", "Daneel.Tween.Tweener", errorHead )

    tweener.isEnabled = false
    tweener.isPaused = true
    tweener.target = nil
    tweener.duration = 0

    table.removevalue( Daneel.Tween.Tweener.tweeners, tweener )
    Daneel.Tween.Tweener.tweeners[ tweener.Id ] = nil
    
    CraftStudio.Destroy( tweener )
    Daneel.Debug.StackTrace.EndFunction()
end

--- Update the tweener's value based on the tweener's elapsed property.
-- Fire the OnUpdate event.
-- This allows the tweener to fast-forward to a certain time.
-- @param tweener (Daneel.Tween.Tweener) The tweener.
-- @param deltaDuration [optional] (number) <strong>Only used internaly.</strong> If nil, the tweener's value will be updated based on the current value of tweener.elapsed.
function DaneelTween.Tweener.Update(tweener, deltaDuration) -- the deltaDuration argument is only used from the Tween.Update() function
    if tweener.isEnabled == false then return end
    Daneel.Debug.StackTrace.BeginFunction("Daneel.Tween.Tweener.Update", tweener, deltaDuration)
    local errorHead = "Daneel.Tween.Tweener.Update(tweener[, deltaDuration]) : "
    Daneel.Debug.CheckArgType(tweener, "tweener", "Daneel.Tween.Tweener", errorHead)
    Daneel.Debug.CheckArgType(deltaDuration, "deltaDuration", "number", errorHead)

    if Daneel.Tween.Ease[tweener.easeType] == nil then
        if DEBUG == true then
            print("Daneel.Tween.Tweener.Update() : Easing '"..tostring(tweener.easeType).."' for tweener ID '"..tween.id.."' does not exists. Setting it back for the default easing '"..Daneel.Config.tween.tweener.easeType.."'.")
        end
        tweener.easeType = Daneel.Config.tween.tweener.easeType
    end

    if deltaDuration ~= nil then
        tweener.elapsed = tweener.elapsed + deltaDuration
        tweener.fullElapsed = tweener.fullElapsed + deltaDuration
    end
    local value = nil

    if tweener.elapsed > tweener.duration then
        tweener.isCompleted = true
        tweener.elapsed = tweener.duration
        if tweener.isRelative == true then
            value = tweener.startValue + tweener.endValue
        else
            value = tweener.endValue
        end
    else
        value = Daneel.Tween.Ease[tweener.easeType](tweener.elapsed, tweener.startValue, tweener.diffValue, tweener.duration)
    end


    if tweener.target ~= nil then
        SetTweenerProperty(tweener, value)
    end
    tweener.value = value

    Daneel.Event.Fire(tweener, "OnUpdate", tweener)
    Daneel.Debug.StackTrace.EndFunction()
end


----------------------------------------------------------------------------------
-- Timer

DaneelTween.Timer = {}
DaneelTween.Timer.__index = DaneelTween.Tweener
setmetatable(DaneelTween.Timer, { __call = function(Object, ...) return Object.New(...) end })


--- Creates a new tweener via one of the two allowed constructors : <br>
-- Timer.New(duration, OnCompleteCallback[, params]) <br>
-- Timer.New(duration, OnLoopCompleteCallback, true[, params]) <br>
-- @param duration (number) The time or frame it should take for the timer or one loop to complete.
-- @param callback (function or userdata) The function that gets called when the OnComplete or OnLoopComplete event are fired.
-- @param isInfiniteLoop [optional default=false] (boolean) Tell wether the timer loops indefinitely.
-- @param params [optional] (table) A table of parameters.
-- @return (Tweener) The tweener.
function DaneelTween.Timer.New( duration, callback, isInfiniteLoop, params )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.Tween.Timer.New", duration, callback, isInfiniteLoop, params )
    local errorHead = "Daneel.Tween.Timer.New( duration, callback[, isInfiniteLoop, params] ) : "
    if type( isInfiniteLoop ) == "table" then
        params = isInfiniteLoop
        errorHead = "Daneel.Tween.Timer.New( duration, callback[, params] ) : "
    end
    Daneel.Debug.CheckArgType( duration, "duration", "number", errorHead )
    Daneel.Debug.CheckArgType( callback, "callback", {"function", "userdata"}, errorHead )
    Daneel.Debug.CheckOptionalArgType( params, "params", "table", errorHead )

    local tweener = table.copy( Daneel.Config.tween.tweener )
    setmetatable( tweener, Daneel.Tween.Tweener )
    tweener.Id = "Timer" .. math.round( math.randomrange( 100000, 999999 ) )
    tweener.startValue = duration
    tweener.endValue = 0
    tweener.duration = duration

    if isInfiniteLoop == true then
        tweener.loops = -1
        tweener.OnLoopComplete = callback
    else
        tweener.OnComplete = callback
    end
    if params ~= nil then
        tweener:Set( params )
    end

    Daneel.Tween.Tweener.tweeners[ tweener.Id ] = tweener
    Daneel.Debug.StackTrace.EndFunction()
    return tweener
end


----------------------------------------------------------------------------------
-- Easing equations
-- From Emmanuel Oga's easing equations : https://github.com/EmmanuelOga/easing

--
-- Adapted from
-- Tweener's easing functions (Penner's Easing Equations)
-- and http://code.google.com/p/tweener/ (jstweener javascript version)
--

--[[
Disclaimer for Robert Penner's Easing Equations license:

TERMS OF USE - EASING EQUATIONS

Open source under the BSD License.

Copyright © 2001 Robert Penner
All rights reserved.

Redistribution and use in source and binary forms, with or without modification, are permitted provided that the following conditions are met:

* Redistributions of source code must retain the above copyright notice, this list of conditions and the following disclaimer.
* Redistributions in binary form must reproduce the above copyright notice, this list of conditions and the following disclaimer in the documentation and/or other materials provided with the distribution.
* Neither the name of the author nor the names of contributors may be used to endorse or promote products derived from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
]]

-- For all easing functions:
-- t = elapsed time
-- b = begin
-- c = change == ending - beginning
-- d = duration (total time)

local pow = math.pow
local sin = math.sin
local cos = math.cos
local pi = math.pi
local sqrt = math.sqrt
local abs = math.abs
local asin = math.asin

local function linear(t, b, c, d)
  return c * t / d + b
end

local function inQuad(t, b, c, d)
  t = t / d
  return c * pow(t, 2) + b
end

local function outQuad(t, b, c, d)
  t = t / d
  return -c * t * (t - 2) + b
end

local function inOutQuad(t, b, c, d)
  t = t / d * 2
  if t < 1 then
    return c / 2 * pow(t, 2) + b
  else
    return -c / 2 * ((t - 1) * (t - 3) - 1) + b
  end
end

local function outInQuad(t, b, c, d)
  if t < d / 2 then
    return outQuad (t * 2, b, c / 2, d)
  else
    return inQuad((t * 2) - d, b + c / 2, c / 2, d)
  end
end

local function inCubic (t, b, c, d)
  t = t / d
  return c * pow(t, 3) + b
end

local function outCubic(t, b, c, d)
  t = t / d - 1
  return c * (pow(t, 3) + 1) + b
end

local function inOutCubic(t, b, c, d)
  t = t / d * 2
  if t < 1 then
    return c / 2 * t * t * t + b
  else
    t = t - 2
    return c / 2 * (t * t * t + 2) + b
  end
end

local function outInCubic(t, b, c, d)
  if t < d / 2 then
    return outCubic(t * 2, b, c / 2, d)
  else
    return inCubic((t * 2) - d, b + c / 2, c / 2, d)
  end
end

local function inQuart(t, b, c, d)
  t = t / d
  return c * pow(t, 4) + b
end

local function outQuart(t, b, c, d)
  t = t / d - 1
  return -c * (pow(t, 4) - 1) + b
end

local function inOutQuart(t, b, c, d)
  t = t / d * 2
  if t < 1 then
    return c / 2 * pow(t, 4) + b
  else
    t = t - 2
    return -c / 2 * (pow(t, 4) - 2) + b
  end
end

local function outInQuart(t, b, c, d)
  if t < d / 2 then
    return outQuart(t * 2, b, c / 2, d)
  else
    return inQuart((t * 2) - d, b + c / 2, c / 2, d)
  end
end

local function inQuint(t, b, c, d)
  t = t / d
  return c * pow(t, 5) + b
end

local function outQuint(t, b, c, d)
  t = t / d - 1
  return c * (pow(t, 5) + 1) + b
end

local function inOutQuint(t, b, c, d)
  t = t / d * 2
  if t < 1 then
    return c / 2 * pow(t, 5) + b
  else
    t = t - 2
    return c / 2 * (pow(t, 5) + 2) + b
  end
end

local function outInQuint(t, b, c, d)
  if t < d / 2 then
    return outQuint(t * 2, b, c / 2, d)
  else
    return inQuint((t * 2) - d, b + c / 2, c / 2, d)
  end
end

local function inSine(t, b, c, d)
  return -c * cos(t / d * (pi / 2)) + c + b
end

local function outSine(t, b, c, d)
  return c * sin(t / d * (pi / 2)) + b
end

local function inOutSine(t, b, c, d)
  return -c / 2 * (cos(pi * t / d) - 1) + b
end

local function outInSine(t, b, c, d)
  if t < d / 2 then
    return outSine(t * 2, b, c / 2, d)
  else
    return inSine((t * 2) -d, b + c / 2, c / 2, d)
  end
end

local function inExpo(t, b, c, d)
  if t == 0 then
    return b
  else
    return c * pow(2, 10 * (t / d - 1)) + b - c * 0.001
  end
end

local function outExpo(t, b, c, d)
  if t == d then
    return b + c
  else
    return c * 1.001 * (-pow(2, -10 * t / d) + 1) + b
  end
end

local function inOutExpo(t, b, c, d)
  if t == 0 then return b end
  if t == d then return b + c end
  t = t / d * 2
  if t < 1 then
    return c / 2 * pow(2, 10 * (t - 1)) + b - c * 0.0005
  else
    t = t - 1
    return c / 2 * 1.0005 * (-pow(2, -10 * t) + 2) + b
  end
end

local function outInExpo(t, b, c, d)
  if t < d / 2 then
    return outExpo(t * 2, b, c / 2, d)
  else
    return inExpo((t * 2) - d, b + c / 2, c / 2, d)
  end
end

local function inCirc(t, b, c, d)
  t = t / d
  return(-c * (sqrt(1 - pow(t, 2)) - 1) + b)
end

local function outCirc(t, b, c, d)
  t = t / d - 1
  return(c * sqrt(1 - pow(t, 2)) + b)
end

local function inOutCirc(t, b, c, d)
  t = t / d * 2
  if t < 1 then
    return -c / 2 * (sqrt(1 - t * t) - 1) + b
  else
    t = t - 2
    return c / 2 * (sqrt(1 - t * t) + 1) + b
  end
end

local function outInCirc(t, b, c, d)
  if t < d / 2 then
    return outCirc(t * 2, b, c / 2, d)
  else
    return inCirc((t * 2) - d, b + c / 2, c / 2, d)
  end
end

local function inElastic(t, b, c, d, a, p)
  if t == 0 then return b end

  t = t / d

  if t == 1 then return b + c end

  if not p then p = d * 0.3 end

  local s

  if not a or a < abs(c) then
    a = c
    s = p / 4
  else
    s = p / (2 * pi) * asin(c/a)
  end

  t = t - 1

  return -(a * pow(2, 10 * t) * sin((t * d - s) * (2 * pi) / p)) + b
end

-- a: amplitud
-- p: period
local function outElastic(t, b, c, d, a, p)
  if t == 0 then return b end

  t = t / d

  if t == 1 then return b + c end

  if not p then p = d * 0.3 end

  local s

  if not a or a < abs(c) then
    a = c
    s = p / 4
  else
    s = p / (2 * pi) * asin(c/a)
  end

  return a * pow(2, -10 * t) * sin((t * d - s) * (2 * pi) / p) + c + b
end

-- p = period
-- a = amplitud
local function inOutElastic(t, b, c, d, a, p)
  if t == 0 then return b end

  t = t / d * 2

  if t == 2 then return b + c end

  if not p then p = d * (0.3 * 1.5) end
  if not a then a = 0 end

  if not a or a < abs(c) then
    a = c
    s = p / 4
  else
    s = p / (2 * pi) * asin(c / a)
  end

  if t < 1 then
    t = t - 1
    return -0.5 * (a * pow(2, 10 * t) * sin((t * d - s) * (2 * pi) / p)) + b
  else
    t = t - 1
    return a * pow(2, -10 * t) * sin((t * d - s) * (2 * pi) / p ) * 0.5 + c + b
  end
end

-- a: amplitud
-- p: period
local function outInElastic(t, b, c, d, a, p)
  if t < d / 2 then
    return outElastic(t * 2, b, c / 2, d, a, p)
  else
    return inElastic((t * 2) - d, b + c / 2, c / 2, d, a, p)
  end
end

local function inBack(t, b, c, d, s)
  if not s then s = 1.70158 end
  t = t / d
  return c * t * t * ((s + 1) * t - s) + b
end

local function outBack(t, b, c, d, s)
  if not s then s = 1.70158 end
  t = t / d - 1
  return c * (t * t * ((s + 1) * t + s) + 1) + b
end

local function inOutBack(t, b, c, d, s)
  if not s then s = 1.70158 end
  s = s * 1.525
  t = t / d * 2
  if t < 1 then
    return c / 2 * (t * t * ((s + 1) * t - s)) + b
  else
    t = t - 2
    return c / 2 * (t * t * ((s + 1) * t + s) + 2) + b
  end
end

local function outInBack(t, b, c, d, s)
  if t < d / 2 then
    return outBack(t * 2, b, c / 2, d, s)
  else
    return inBack((t * 2) - d, b + c / 2, c / 2, d, s)
  end
end

local function outBounce(t, b, c, d)
  t = t / d
  if t < 1 / 2.75 then
    return c * (7.5625 * t * t) + b
  elseif t < 2 / 2.75 then
    t = t - (1.5 / 2.75)
    return c * (7.5625 * t * t + 0.75) + b
  elseif t < 2.5 / 2.75 then
    t = t - (2.25 / 2.75)
    return c * (7.5625 * t * t + 0.9375) + b
  else
    t = t - (2.625 / 2.75)
    return c * (7.5625 * t * t + 0.984375) + b
  end
end

local function inBounce(t, b, c, d)
  return c - outBounce(d - t, 0, c, d) + b
end

local function inOutBounce(t, b, c, d)
  if t < d / 2 then
    return inBounce(t * 2, 0, c, d) * 0.5 + b
  else
    return outBounce(t * 2 - d, 0, c, d) * 0.5 + c * .5 + b
  end
end

local function outInBounce(t, b, c, d)
  if t < d / 2 then
    return outBounce(t * 2, b, c / 2, d)
  else
    return inBounce((t * 2) - d, b + c / 2, c / 2, d)
  end
end

-- Modifications for Daneel : replaced 'return {' by 'DaneelTween.Ease = {'
DaneelTween.Ease = {
  linear = linear,
  inQuad = inQuad,
  outQuad = outQuad,
  inOutQuad = inOutQuad,
  outInQuad = outInQuad,
  inCubic = inCubic ,
  outCubic = outCubic,
  inOutCubic = inOutCubic,
  outInCubic = outInCubic,
  inQuart = inQuart,
  outQuart = outQuart,
  inOutQuart = inOutQuart,
  outInQuart = outInQuart,
  inQuint = inQuint,
  outQuint = outQuint,
  inOutQuint = inOutQuint,
  outInQuint = outInQuint,
  inSine = inSine,
  outSine = outSine,
  inOutSine = inOutSine,
  outInSine = outInSine,
  inExpo = inExpo,
  outExpo = outExpo,
  inOutExpo = inOutExpo,
  outInExpo = outInExpo,
  inCirc = inCirc,
  outCirc = outCirc,
  inOutCirc = inOutCirc,
  outInCirc = outInCirc,
  inElastic = inElastic,
  outElastic = outElastic,
  inOutElastic = inOutElastic,
  outInElastic = outInElastic,
  inBack = inBack,
  outBack = outBack,
  inOutBack = inOutBack,
  outInBack = outInBack,
  inBounce = inBounce,
  outBounce = outBounce,
  inOutBounce = inOutBounce,
  outInBounce = outInBounce,
}
