--
-- A simple interface for 
-- test LiveWidget powered Corona SDK applications
--
-- @author Huang Wei <huangw@pe-po.com>

-- ### USAGE
--
-- ```
-- local dr = require "debug_runner"
-- dr.desc("default runner")
-- dr.regist(10, function() print("do something") end, "so lets do it")
-- dr.run()
--```

local debug_runner = {}

-- Define a series of actions registed in `action` (a _upvalue_)
local actions = {}
local jobque = {}
local total_time = 0

-- ---
-- Create a description for the following test
--
function debug_runner.desc(msg)
    -- Description is just an echo action without delay
    debug_runner.regist(0, function() 
        print()
        print("[CONTEXT] " .. msg:gsub("^%l", string.upper)) 
        print("-------------------------------------")
    end)
end

function debug_runner.exp(expection)
    print("Should", expection:lower())
end

function debug_runner.rslt(result)
    print(">>", result)
    -- or print_table(rslt_tbl)
end

-- ---
-- Add some code to perform after n second
--
function debug_runner.regist(n, code, desc)    
    -- check parameter format
    assert(type(n) == 'number', "must specify a number as #1 argument for seconds")
    assert(type(code) == 'function', "#2 argument must be a function")

    action = {}
    action.time = n
    action.code = code
    -- `desc` is optional
    if desc then action.desc = desc end
    
    -- regist to time stacks
    if n > 0 then
        -- add a waiting report for next time
        local echo = {}
        echo.time = 0
        echo.code = function() print(); print(string.format("(wait for %s second ...)", n)); print(); end
        table.insert(jobque, echo)

        local que = {}
        que.time = total_time
        que.action = jobque
        table.insert(actions, que)
        total_time = total_time + n * 1000
        -- reset jobque
        jobque = {} 
    end
    table.insert(jobque, action)
end

-- ---
-- Run all actions
--
function debug_runner.run()
    -- add last jobque
    local que = {}
    que.time = total_time
    que.action = jobque
    table.insert(actions, que)

    -- clean up the screen by print a lot of new lines
    for i=1,12 do print() end

    print("-------------------------------------") 
    print("        START THE TEST RUNNER        ")
    print("-------------------------------------") 
    print()
    print()

    local lastvtime = 0
    for i,v in ipairs(actions) do
        local code = function() 
            for j,c in ipairs(v.action) do
                if c.desc then
                  print('* * *')
                  print(c.desc:upper())
                end
                local action_code = c.code
                action_code()
            end
        end
        if v.time > 0 then
            lastvtime = v.time
            timer.performWithDelay(v.time, code)
        else
            code()
        end
    end

    timer.performWithDelay(lastvtime + 1, function() 
        print()
        print()
        print("-------------------------------------") 
        print("        TEST RUNNER COMPLETED        ")
        print("=====================================") 
    end)
end

return debug_runner
