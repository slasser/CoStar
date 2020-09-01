-----------------------------------------------------------------------------------------
--
-- View_spec.lua
--
-----------------------------------------------------------------------------------------

local util = require 'util'
local ts = require 'spec_runner'
local View = require 'View'

local VCW = display.viewableContentWidth
local VCH = display.viewableContentHeight

ts.desc("#Instance constructor")
ts.regist(0, function()
    print("initialize")
    ts.blueColor = {90, 200, 255}
    local blue = ts.blueColor
    ts.window = View {
      name = "fullscreened",
      y = 20,
      width = VCW, height = VCH - 20,
      backgroundColor = blue,
      --cornerRadius = 10em,
      --backgroundFilter = "filter.blur",
    }
    local window = ts.window
    assert(window and window.name == "fullscreened", "incorrect name")
    assert(window.backgroundColor and window.backgroundColor == blue, "unmatched color")
    assert(window.frame and window.frame.width == VCW and window.frame.height == VCH-20, "incorrect dimension")
    assert(window.frame.y == 20)
    print(window.bounds.contentBounds.yMin)
    print(window.bounds.contentBounds.yMax)
end, "display a fullscreen view")

ts.desc("#Configuring a View's Visual Appearance")
ts.regist(2, function()
    local window = ts.window
    local white = {255, 255, 255, 255}
    window:setBackgroundColor(white)
    assert(window.backgroundColor == white, "incorrect color")
    util.print_r(window.backgroundColor)
end, "change background's color to white")

ts.desc("#Managing the View Hierarchy")
ts.regist(1, function()
    print("create a new view")
    ts.grayColor = {142, 142, 147, 255}
    ts.blueColor = {90, 200, 250, 255}
    local bar = View {
      name = "bar",
      yOffset = 22,
      width = VCW, height = 44,
      backgroundColor = ts.blueColor,
    }
    ts.window:addSubview(bar)
    assert(ts.window[bar.name] == bar)
    assert(ts.window.bar == bar)
    assert(bar.superview == ts.window)
end, "display a bar view at the top")

ts.regist(1, function()
    local bar = ts.window.bar
    local shade_1 = View {
      name = "shade",
      y = 20,
      height = 4,
      backgroundColor = {52, 170, 220}, -- blue shade
    }
    local shade_2 = View {
      name = "purple",
      height = 22,
      backgroundColor = {88, 86, 214},
    }
    bar:addSubview(shade_1)
    bar:addSubview(shade_2)
    print("only purple subview should be see")
end, "add shade subviews to bar view")

ts.regist(2, function()
    local bar = ts.window.bar
    print("background is always on bottom")
    bar.purple:moveToIndex(1)
end, "move subview back")

ts.regist(2, function()
    print("purple view come back to top")
    ts.window.bar.purple:moveToIndex(2)
end, "bring subview front")

ts.regist(1, function()
    local rect = View {
      name = "rect",
      width = 128, height = 128,
      --verticalAlign = View.Algin.ALIGN_CENTER
      backgroundColor = {76, 217, 100}
    }
    util.center(rect.frame)
    local window = ts.window
    window:addSubview(rect)
    print("check true")
    local inWindow = rect:isDescendantOfView(window)
    assert(rect:isDescendantOfView(window))
    print(inWindow)
    print("check false")
    local inBar = rect:isDescendantOfView(window.bar)
    assert(not inBar)
    print(inBar)
end, "check the view hierarchy")

ts.regist(2, function()
    local window = ts.window
    window.bar.purple:removeFromSuperview()
    assert(type(window.bar.purple) == "nil", "reference is not removed")
end, "remove subview from its superview")

ts.desc("#Animations")
ts.regist(2, function() end, "create/modify/commit animation")

return ts