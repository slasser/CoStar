-- Util functions for development and debug use
--
-- @author Huang Wei <huangw@pe-po.com>
--

local util = {}

-- ## Usable Constants

util.SCR_W = display.contentWidth - display.screenOriginX * 2
util.SCR_H = display.contentHeight - display.screenOriginY * 2

-- http://developer.anscamobile.com/code/iosinfo-definitive-way-determine-type-ios-device-your-app-running
util.PHY_W  = math.floor((-display.screenOriginX * 1.975 + display.contentWidth) / display.contentScaleX )
util.PHY_H = math.floor((-display.screenOriginY * 2 + display.contentHeight) / display.contentScaleY )

util.isSmallScreen = display.contentScaleX < 1.5 -- TODO

-- device detection
util.model = system.getInfo("model")
util.isSimulator = system.getInfo( "environment" ) == "simulator"
util.isiOS = string.match( util.model, "iP" )
util.isiPad = string.match( util.model, "iPad" )
util.isNewiPad = string.match( util.model, "iPad3" )
-- isiPhone4 includes iphone 5 and ipod 4, 5
util.isiPhone4 = string.match( util.model, "iPhone4" ) or string.match( util.model, "iPhone5" ) or string.match( util.model, "iPod4" )
util.isiPhone = string.match( util.model, "iPhone" )
util.isKindle = string.match( util.model, "Kindle Fire" )

-- detect the physical screen size in inches
local devices =
{
--{{{
        -- Acer
        { model = "A100", inchesDiagonal = 7.0, comModel = "Iconia Tab A100" },
        { model = "Iconia Tab A100", inchesDiagonal = 7.0, },
        { model = "A101", inchesDiagonal = 7.0, comModel = "Iconia Tab A101" },
        { model = "A200", inchesDiagonal = 10.1, comModel = "Iconia Tab A200" },
        { model = "A500", inchesDiagonal = 10.1, comModel = "Iconia Tab A500" },
        { model = "A501", inchesDiagonal = 10.1, comModel = "Iconia Tab A501" },
        { model = "A700", inchesDiagonal = 10.1, comModel = "Iconia Tab A700" }, -- Unverified

        -- Amazon
        { model = "Kindle Fire", inchesDiagonal = 7.0, },

        -- Apple
        { model = "iPhone", inchesDiagonal = 3.5, },
        { model = "iPad", inchesDiagonal = 9.7, },
        { model = "iPod touch", inchesDiagonal = 3.5, },

        -- Asus
        { model = "Transformer TF101", inchesDiagonal = 10.1, },
        { model = "Epad", inchesDiagonal = 10.1, comModel = "Eee Pad Transformer" },
        { model = "Eee Pad Transformer TF101", inchesDiagonal = 10.1, },

        -- Barnes & Noble
        { model = "Nook Color", inchesDiagonal = 7.0, },

        -- Dell
        { model = "Dell Streak", inchesDiagonal = 5.0, },

        -- Google
        { model = "Nexus One", inchesDiagonal = 3.7, },
        { model = "Nexus S", inchesDiagonal = 4.0, },
        { model = "Galaxy Nexus", inchesDiagonal = 4.65, },

        -- HP
        { model = "Touchpad", inchesDiagonal = 9.7 },

        -- HTC
        { model = "HTC Desire", inchesDiagonal = 3.7 },
        { model = "HTC Desire S", inchesDiagonal = 3.7 },
        { model = "Desire HD", inchesDiagonal = 4.3 },
        { model = "Desire HD2", inchesDiagonal = 4.3 },
        { model = "PC36100", inchesDiagonal = 4.3, comModel = "EVO 4G" },
        { model = "Vision", inchesDiagonal = 3.7, comModel = "Desire Z/T-Mobile G2" },
        { model = "HTC Vision", inchesDiagonal = 3.7, comModel = "Desire Z/T-Mobile G2" }, -- Unverified
        { model = "Sensation", inchesDiagonal = 4.3 }, -- Unverified
        { model = "HTC Sensation", inchesDiagonal = 4.3 }, -- Unverified
        { model = "HTC Sensation Z710e", inchesDiagonal = 4.3 }, -- Unverified
        { model = "Flyer", inchesDiagonal = 7.0, },
        { model = "HTC Flyer", inchesDiagonal = 7.0, },
        { model = "HTC Flyer P510e", inchesDiagonal = 7.0, }, -- Unverified

        -- LG
        { model = "LG-P500", inchesDiagonal = 3.2, comModel = "Optimus One" },
        { model = "LG-P920", inchesDiagonal = 4.3, comModel = "Optimus 3D" }, -- Unverified
        { model = "LG-P970", inchesDiagonal = 4.0, comModel = "Optimus Black" },
        { model = "US855", inchesDiagonal = 4.0, comModel = "Optimus Black" },
        { model = "Optimus 2X", inchesDiagonal = 4.0, },
        { model = "LG-P990", inchesDiagonal = 4.0, comModel = "Optimus 2X" }, -- Unverified
        { model = "SU660", inchesDiagonal = 4.0, comModel = "Optimus 2X korean" }, -- Unverified
        { model = "VM670", inchesDiagonal = 3.2, comModel = "Optimus V/S/U" },
        { model = "LG-VM670", inchesDiagonal = 3.2, comModel = "Optimus V/S/U" },
        { model = "VS910", inchesDiagonal = 4.3, comModel = "Revolution" }, -- Unverified
        { model = "VS910 4G", inchesDiagonal = 4.3, comModel = "Revolution" }, -- Unverified
        { model = "LG-V900", inchesDiagonal = 8.9, comModel = "Optimus Pad" }, -- Unverified
        { model = "V900", inchesDiagonal = 8.9, comModel = "Optimus Pad" },
        { model = "L-06C", inchesDiagonal = 8.9, comModel = "Optimus Pad" },

        -- Motorola
        { model = "MB525", inchesDiagonal = 3.7, comModel = "Defy" },
        { model = "MB526", inchesDiagonal = 3.7, comModel = "Defy+" },
        { model = "MB860", inchesDiagonal = 4.0, comModel = "Atrix 4G" },
        { model = "Droid", inchesDiagonal = 3.7, },
        { model = "Milestone", inchesDiagonal = 3.7, },
        { model = "DROID 2", inchesDiagonal = 3.7 },
        { model = "A953", inchesDiagonal = 3.7, comModel = "Milestone 2" },
        { model = "ME722", inchesDiagonal = 3.7, comModel = "Milestone 2" },
        { model = "DROID 2 GLOBAL", inchesDiagonal = 3.7 },
        { model = "Droid X", inchesDiagonal = 4.3, },
        { model = "Xoom", inchesDiagonal = 10.1, },
        { model = "MZ601", inchesDiagonal = 10.1, comModel = "Xoom", },

        -- Samsung
        { model = "GT-I5500", inchesDiagonal = 2.8, comModel = "Galaxy 5" },
        { model = "GT-S5830", inchesDiagonal = 3.5, comModel = "Galaxy Ace" },
        { model = "Galaxy S", inchesDiagonal = 4.0, },
        { model = "SGH-T959P", inchesDiagonal = 4.0, comModel = "Galaxy S (Telus Fascinate)" },
        { model = "GT-I9000", inchesDiagonal = 4.0, comModel = "Galaxy S" },
        { model = "GT-I9001", inchesDiagonal = 4.0, comModel = "Galaxy S" },
        { model = "SHW M110S", inchesDiagonal = 4.0, comModel = "Galaxy S Korea" },
        { model = "SC-02B", inchesDiagonal = 4.0, comModel = "Galaxy S DoCoMo" },
        { model = "GT-I9100", inchesDiagonal = 4.3, comModel = "Galaxy S2" },
        { model = "SAMSUNG-SGH-I777", inchesDiagonal = 4.3, comModel = "Galaxy S2 AT&T" },
        { model = "SGH-T989", inchesDiagonal = 4.3, comModel = "Galaxy S2 T-Mobile" },
        { model = "GT-N7000", inchesDiagonal = 5.0, comModel = "Galaxy Note" },
        { model = "Galaxy Tab", inchesDiagonal = 7.0, },
        { model = "GT-P1000", inchesDiagonal = 7.0, comModel = "Galaxy Tab" },
        { model = "GT-P1010", inchesDiagonal = 7.0, comModel = "Galaxy Tab" },
        { model = "SGH-T849", inchesDiagonal = 7.0, comModel = "Galaxy Tab T-Mobile" },
        { model = "GT-P6200", inchesDiagonal = 7.0, comModel = "Galaxy Tab 7.0 Plus" },
        { model = "GT-P6210", inchesDiagonal = 7.0, comModel = "Galaxy Tab 7.0 Plus" },
        { model = "GT-P6800", inchesDiagonal = 7.7, comModel = "Galaxy Tab 7.7" },
        { model = "GT-P7100", inchesDiagonal = 10.1, comModel = "Galaxy Tab 10.1v" },
        { model = "GT-P7300", inchesDiagonal = 8.9, comModel = "Galaxy Tab 8.9" },
        { model = "GT-P7310", inchesDiagonal = 8.9, comModel = "Galaxy Tab 8.9" },
        { model = "Galaxy Tab X", inchesDiagonal = 10.1, comModel = "Galaxy Tab 10.1" },
        { model = "GT-P7500", inchesDiagonal = 10.1, comModel = "Galaxy Tab 10.1" },
        { model = "GT-P7510", inchesDiagonal = 10.1, comModel = "Galaxy Tab 10.1" },

        -- Sharp
        { model = "SH-12C", inchesDiagonal = 4.2, comModel = "Aquos SH-12C" },

        -- Sony-Ericsson
        { model = "shakira", inchesDiagonal = 3.0, comModel = "Xperia X8" }, -- Unverified
        { model = "X10", inchesDiagonal = 4.0, comModel = "Xperia X10" },
        { model = "E10a", inchesDiagonal = 2.55, comModel = "Xperia X10 mini" },
        { model = "LT15i", inchesDiagonal = 4.2, comModel = "Xperia Arc" },

        -- Toshiba
        { model = "Folio 100", inchesDiagonal = 10.1, },

        -- ZTE
        { model = "Blade", inchesDiagonal = 3.5 },

        -- Cheap chinese stuff
        { model = "uvt210", inchesDiagonal = 7.0, comName = "Herotab C8/Dropad A8/MID7009/Haipad M7" },
        { model = "p7901a", inchesDiagonal = 10.0, comName = "Epad P7901A" }, -- Unverified
--}}}
}
for i,m in ipairs(devices) do
    if string.match( util.model, m.model ) then
        util.SCR_INCHES = m.inchesDiagonal
    end
end
util.isTablet = util.SCR_INCHES >= 7

-- ## Debug Functions

-- ---
-- dump arbitrary variables include table
--
function util.print_r ( t )
--{{{
    local print_r_cache={}
        local function sub_print_r(t,indent)
            if (print_r_cache[tostring(t)]) then
                print(indent.."*"..tostring(t))
            else
                print_r_cache[tostring(t)]=true
            if (type(t)=="table") then
                for pos,val in pairs(t) do
                    if (type(val)=="table") then
                        print(indent.."["..pos.."] => "..tostring(t).." {")
                        sub_print_r(val,indent..string.rep(" ",string.len(pos)+8))
                        print(indent..string.rep(" ",string.len(pos)+6).."}")
                    elseif (type(val)=="string") then
                        print(indent.."["..pos..'] => "'..val..'"')
                    else
                        print(indent.."["..pos.."] => "..tostring(val))
                    end
                end
            else
                print(indent..tostring(t))
            end
        end
    end

    if (type(t)=="table") then
        print(tostring(t).." {")
        sub_print_r(t,"  ")
        print("}")
    else
        sub_print_r(t,"  ")
    end
    print()
--}}}
end

-- ---
-- split string to array
-- ---
function util.explode(div,str)
--{{{
  if (div=='') then return false end
  local pos,arr = 0,{}
  -- for each divider found
  for st,sp in function() return string.find(str,div,pos,true) end do
    table.insert(arr,string.sub(str,pos,st-1)) -- Attach chars left of current divider
    pos = sp + 1 -- Jump past current divider
  end
  table.insert(arr,string.sub(str,pos)) -- Attach chars right of last divider
  return arr
--}}}
end

-- ---
-- Show a fps widget on screen
--
-- parameters:
-- - opts.x, opts.y
-- - opts.warn_level, opts.alert_level: size of textual memory in MB
function util.show_fps(opts)
--{{{
	-- keep singleton: if any fps exist then return
	if util.fps then return true end
	local prvtime = 0
	local maxFps = 30

	local opts = opts or {}

    util.fps = display.newGroup()
	util.fps.alpha = opts.alpha or 0.7
    util.fps.warn_level = opts.warn_level or 8
    util.fps.alert_level = opts.alert_level or 24
	assert((util.fps.alert_level-util.fps.warn_level) > 0, "alert_level should above warn_level")
	util.fps.x = opts.x or display.contentWidth-120-display.screenOriginX
    util.fps.y = opts.y or display.contentHeight-45-display.screenOriginY
    --util.fps.y = opts.y or display.viewableContentHeight-45
	--
    -- initialize dashboard
	--
	function util.fps:layout()
		self.background = display.newRect(-50, 0, 175, 50)
	    self.memory = display.newText("0/10", 20, 0, Helvetica, 18)
	    self.framerate = display.newText("0", 30, self.memory.height, Helvetica, 18)
		self.memory:setTextColor(255,255,255)
		self.framerate:setTextColor(255,255,255)
		self.background:setFillColor(0,0,0)
		self:insert(self.background)
		self:insert(self.memory)
		self:insert(self.framerate)
	end

	--
    -- update textual memory and fps numbers
	--
    function util.fps:enterFrame (event)
		local lastFps = {}
		local lastFpsCounter = 1
		local crtime = system.getTimer()
		local dt = crtime - prvtime
		prvtime = crtime
		-- dynamic frame number per second
		local fps = math.floor(1000/dt)
		lastFps[lastFpsCounter] = fps
		lastFpsCounter = lastFpsCounter + 1
		if(lastFpsCounter > maxFps) then lastFpsCounter = 1 end
		-- pick lowest fps out every 30 frames
		local function minLastFps()
			for i = 1, #lastFps do
				if (lastFps[i] < 10000) then
					return lastFps[i]
				end
			end
		end
		local min=minLastFps() or 0
		-- update fps text and change text colors
		self:toFront()
		local memoryUsed = system.getInfo("textureMemoryUsed")/1000000
		self.framerate.text = "FPS: "..fps.."(min: "..min..")"
		self.memory.text = "Mem: "..(system.getInfo("textureMemoryUsed")/1000000).." mb"
		if (memoryUsed < self.warn_level) then
			self.memory:setTextColor(255,255,255)
		elseif (memoryUsed < self.alert_level) then
			self.memory:setTextColor(255,255,0)
		else
			self.memory:setTextColor(255,0,0)
		end
    end

	util.fps:layout()
    Runtime:addEventListener('enterFrame', util.fps)
--}}}
end

-- ---
-- Hide the fps widget
--
function util.hide_fps()
--{{{
	if not util.fps then return end
	Runtime:removeEventListener('enterFrame', util.fps)
    util.fps:removeSelf()
    util.fps = nil
--}}}
end

-- ---
-- Move a display object around and report the x, y position when released
-- NOTE:
--   - `touch` function of the display object will be overwritten
--   - LiveWidget with `canvas` property defined can be properly handled.
function util.xy(aDisplayObject)
--{{{
    if not util.isDisplayObject(aDisplayObject) then
        if aDisplayObject.canvas and util.isDisplayObject(aDisplayObject.canvas) then
            aDisplayObject = aDisplayObject.canvas
        end
    end

    assert(util.isDisplayObject(aDisplayObject), "only works for display object")

    -- define (overwritten) the `touch` function
    function aDisplayObject:touch(event)
        if event.phase == "began" then
            self._startX, self._startY = self.x - event.x, self.y - event.y
        elseif event.phase == "moved" then
            self.x, self.y = self._startX + event.x, self._startY + event.y
        elseif event.phase == "ended" or event.phase == "cancelled" then
           print(string.format("x: %s; y: %s", self.x, self.y))
        end
    end
    aDisplayObject:addEventListener('touch', aDisplayObject)
--}}}
end

-- ## Utilities for Display Objects

-- ---
-- Check whether a variable is a display object
--
function util.isDisplayObject(aDisplayObject)
    local coronaMetaTable = getmetatable(display.getCurrentStage())
    return (type(aDisplayObject) == "table" and getmetatable(aDisplayObject) == coronaMetaTable)
end

-- ---
-- Remove a object from memory safely
--
function util.rm(aDisplayObject)
--{{{
    if not util.isDisplayObject(aDisplayObject) then
        if aDisplayObject.canvas and util.isDisplayObject(aDisplayObject.canvas) then
            aDisplayObject = aDisplayObject.canvas
        end
    end

    -- assert(util.isDisplayObject(aDisplayObject), "only works for display object")
    if aDisplayObject.removeSelf and type(aDisplayObject.removeSelf) == 'function' then
        aDisplayObject:removeSelf()
    end
--}}}
end

-- ---
-- Locate a display object based on 9 reference point in the visiable screen,
-- from left top:
-- ```
-- 1, 2, 3
--
-- 4, 5, 6
--
-- 7, 8, 9
-- ```
-- for example, use util.locate(5, 0, 0) to locate a object to the center of the screen.
--
-- parameters:
-- - obj: a display object or a live widget with obj.canvas as a display object
-- - reference_point: one of the 9 point in the screen (in 1, ..., 9)
-- - transition_opt(optional): a table contains transition options
function util.locate(obj, reference_point, x, y, transition_opt)
--{{{
    -- obj can be a display object or a live widget with obj.canvas
    if not util.isDisplayObject(obj) then
        if obj.canvas and util.isDisplayObject(obj.canvas) then
            obj = obj.canvas
        end
    end
    assert(util.isDisplayObject(obj), "only works for display object")

    -- find obj.x, obj.y based on reference_point, x, y
    local locators={{1,2,3},{4,5,6},{7,8,9}}
    local reference_x = display.screenOriginX
    local reference_y = display.screenOriginY
    local located = false
    for v,h in pairs(locators) do
        if located == true then break end
        for i,n in pairs(h) do
            if reference_point == n then
                reference_x = reference_x + (display.viewableContentWidth/2)*(i-1)
                reference_y = reference_y + (display.viewableContentHeight/2)*(v-1)
                located = true
                break
            end
        end
    end

    -- if transition_opt set, use transition to move the object,
    if transition_opt then
        transition_opt.x, transition_opt.y = reference_x+x, reference_y+y
        transition.to(obj,transition_opt)
    -- otherwise just set x, y to the obj directly
    else
        obj.x = reference_x + x
        obj.y = reference_y + y
    end

--}}}
end

-- ---
-- Centerize a display object or a live widget to the screen center
--
-- parameters:
-- - obj: a display object or a live widget with obj.canvas as a display object
-- - transition_opt(optional): a table contains transition options
function util.center(obj, transition_opt)
--{{{
    -- obj can be a display object or a live widget with obj.canvas
    if not util.isDisplayObject(obj) then
        if obj.canvas and util.isDisplayObject(obj.canvas) then
            obj = obj.canvas
        end
    end
    assert(util.isDisplayObject(obj), "only works for display object")

    -- count target x, y using contentBounds property of the object(G)
    -- TODO: keep bounds dynamic
    local bounds = obj.contentBounds
    -- find bounds' center location(L)
    local center_x=bounds.xMax-bounds.xMin
    local center_y=bounds.yMax-bounds.yMin
    -- offset of real position(L)
    local delta_x = obj.x - (bounds.xMin + center_x*0.5)
    local delta_y = obj.y - (bounds.yMin + center_y*0.5)
    
    local location_x = display.contentCenterX + delta_x
    local location_y = display.contentCenterY + delta_y
    -- if transition_opt set, use transition to move the object
    if transition_opt then
    transition_opt.x, transition_opt.y = location_x, location_y
    transition.to(obj,transition_opt)
    -- otherwise just set x, y to the obj directly
    else
        obj.x = location_x
        obj.y = location_y
    end
--}}}
end

return util

