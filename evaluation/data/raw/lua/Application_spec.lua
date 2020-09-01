-----------------------------------------------------------------------------------------
--
-- Application_spec.lua
--
-----------------------------------------------------------------------------------------

local util = require 'util'
local ts = require 'spec_runner'
local Application = require 'Application'

local VCW = display.viewableContentWidth
local VCH = display.viewableContentHeight

ts.desc("#Instance constructor")
ts.regist(0, function()
end)

return ts