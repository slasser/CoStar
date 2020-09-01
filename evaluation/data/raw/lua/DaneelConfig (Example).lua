-- DaneelConfig (Example).lua
-- This file is an example of every configuration key/value pairs that you might be interested to tweak
-- As this file may be overwritten in future versions, do not modify it
-- Instead, copy it to another script and remove "_Example" from the function name
--
-- Last modified for v1.2.0
-- Copyright © 2013 Florent POUJOL, published under the MIT licence.

function DaneelConfig_Example()
    return {
        -- List of the Scripts paths as values and optionally the script alias as the keys.
        -- Ie :
        -- "fully-qualified Script path"
        -- or
        -- alias = "fully-qualified Script path"
        --
        -- Setting a script path here allow you to  :
        -- * Use the dynamic getters and setters
        -- * Use component:Set() (for scripted behaviors)
        -- * Use component:GetId() (for scripted behaviors)
        -- * If you defined aliases, dynamically access the scripted behavior on the game object via its alias
        scriptPaths = {},

 
        ----------------------------------------------------------------------------------

        input = {
            -- Button names as you defined them in the "Administration > Game Controls" tab of your project.
            -- Button whose name is defined here can be used as HotKeys.
            buttons = {
                -- Ie: "Fire",
            },

            doubleClickDelay = 20, -- Maximum number of frames between two clicks of the left mouse button to be considered as a double click
        },


        ----------------------------------------------------------------------------------

        language = {
            languageNames = {}, -- list of the languages supported by the game
            
            current = nil, -- Current language
            default = nil, -- Default language
            searchInDefault = true, -- Tell wether Daneel.Lang.Get() search a line key in the default language 
            -- when it is not found in the current language before returning the value of keyNotFound
            keyNotFound = "langkeynotfound", -- Value returned when a language key is not found
        },


        ----------------------------------------------------------------------------------

        gui = {
            cameraName = "HUDCamera", -- Name of the gameObject who has the orthographic camera used to render the HUD

            -- Default GUI components settings
            hud = {
                localPosition = Vector2.New(0, 0),
                layer = 1,
            },
            
            toggle = {
                isChecked = false, -- false = unchecked, true = checked
                text = "",
                group = nil,
                -- ':text' represents the toggle's text
                checkedMark = "√ :text",
                uncheckedMark = "X :text",
                checkedModel = nil,
                uncheckedModel = nil,
            },

            progressBar = {
                minValue = 0,
                maxValue = 100,
                minLength = 0,
                maxLength = 5, -- in units
                height = 1,
                progress = "100%",
            },

            slider = {
                minValue = 0,
                maxValue = 100,
                length = 5, -- 5 units
                axis = "x",
                value = "0%",
            },

            input = {
                isFocused = false,
                maxLength = 99999,
                characterRange = nil, -- a string containing all allowed characters (case sensitive)
            },

            textArea = {
                areaWidth = 0, -- max line length, in units or pixel as a string (0 = no max length)
                wordWrap = false, -- when a ligne is longer than the area width: cut the ligne when false, put the rest of the ligne in one or several lignes when true
                newLine = "\n", -- end of ligne delimiter
                lineHeight = 1, -- in units or pixels as a string
                verticalAlignment = "top",

                font = nil,
                text = "Text\nArea",
                alignment = nil,
                opacity = nil,
            },
        },


        ----------------------------------------------------------------------------------

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
            },
        },


        ----------------------------------------------------------------------------------

        debug = {
            enableDebug = true, -- Enable/disable Daneel's global debugging features (error reporting + stacktrace).
            enableStackTrace = true, -- Enable/disable the Stack Trace.
        },


        ----------------------------------------------------------------------------------

        -- Default CraftStudio's components settings (except Transform)
        -- See 'gui' section above for default GUI component settings
        components = {
            --[[ ie :
            textRenderer = {
                font = "MyFont",
                alignment = "right",
            },
            ]]
        },


        ----------------------------------------------------------------------------------
        
        -- Objects (keys = Type, value = Object)
        -- For use by Daneel.Debug.GetType() which will return the Type when the Object is the metatable of the provided object
        userObjects = {},
    }
end
