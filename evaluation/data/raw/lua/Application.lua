-----------------------------------------------
-- @class: Application (singleton)
-- @file Application.lua - v0.0.1 (2013-09)
-----------------------------------------------
-- created at: 2013-09-25 10:30:13

-- ======
-- LIBRARIES
-- ======
local util = require 'util'
local class = require 'middleclass'
local Window = require 'Window'

-- ======
-- CLASS
-- ======
local Application = class 'Application'

-- ======
-- CONSTANTS
-- ======

local ACW = display.actualContentWidth
local ACH = display.actualContentHeight

-- ======
-- VARIABLES
-- ======

-- Internal identifier

-- ======
-- FUNCTIONS <TASKS>
-- ======

-- ------
-- @task Task description
-- ------

--- Instance constructor
-- @param opt Intent table for construct new instance.
function Application:initialize(opt)
  self.window = Window { name = "mainWindow" }
end

return Application