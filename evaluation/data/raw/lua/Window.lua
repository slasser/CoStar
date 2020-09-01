-----------------------------------------------
-- @class: View
-- @file View.lua - v0.0.1 (2013-09)
-----------------------------------------------
-- created at: 2013-09-25 10:30:13

-- ======
-- LIBRARIES
-- ======
local util = require 'util'
local class = require 'middleclass'
local View = require 'View'

-- ======
-- CLASS
-- ======
local Window = View:subclass('Window')

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
-- FUNCTIONS
-- ======

-- ------
-- Initializing a View Object
-- ------

--- Instance constructor
-- @param opt Intent table for construct new instance.
function Window:initialize(opt)
  -- define window properties
  opt = opt or {}
  opt.x, opt.y = 0, 0 -- top left
  opt.xOffset, opt.yOffset = 0, 0 -- bounds with none offset
  opt.width, opt.height = ACW, ACH -- clips to device screen
  opt.backgroundColor = {255, 255, 255, 0}
  
  View.initialize(self, opt)
  
  -- View Hierarchy
  --self.subviews = {}
  self.superview = nil -- root view
  self.window = self
end

-- ------
-- Managing the View Hierarchy
-- ------

--- Remove a subview (current view) from its parent
-- @param view Name of the parent view.
function Window:removeFromSuperview(view)
end

--- Move view to special index of its superview.
-- @param zIndex The target z-order to move the view to. This parameter is adopt from native group object.
function Window:moveToIndex(zIndex)
end

--- Check if the view is another view's descendant.
-- @param view The target view to check.
-- @return true if view is in parent chain, false if view is not found.
function Window:isDescendantOfView(view)
end

return Window