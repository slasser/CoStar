-----------------------------------------------------------------------------------------
--
-- Window_spec.lua
--
-----------------------------------------------------------------------------------------

local util = require 'util'
local ts = require 'spec_runner'
local Window = require 'Window'
local View = require 'View'

local VCW = display.viewableContentWidth
local VCH = display.viewableContentHeight

ts.desc("#Instance constructor")
ts.regist(0, function()
  ts.window = Window {
    name = 'keyWindow'
  }
end, "Check window appearence")

return ts