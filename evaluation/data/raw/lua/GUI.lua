-- GUI.lua
-- Module adding the GUI components and Vector2 object
--
-- Last modified for v1.2.0
-- Copyright © 2013 Florent POUJOL, published under the MIT licence.

function DaneelConfigModuleGUI()
    Daneel.GUI = DaneelGUI

    return {
        gui = {
            screenSize = CraftStudio.Screen.GetSize(),
            cameraName = "HUDCamera",  -- Name of the gameObject who has the orthographic camera used to render the HUD
            cameraGO = nil, -- the corresponding GameObject, set at runtime
            originGO = nil, -- "parent" gameObject for global hud positioning, created at runtime in DaneelModuleGUIAwake
            originPosition = Vector3:New(0),

            -- Default GUI components settings
            hud = {
                localPosition = Vector2.New(0, 0),
                layer = 1,
            },

            toggle = {
                isChecked = false, -- false = unchecked, true = checked
                text = "Toggle",
                -- ':text' represents the toggle's text
                checkedMark = ":text",
                uncheckedMark = ":text",
                checkedModel = nil,
                uncheckedModel = nil,
            },

            progressBar = {
                height = 1,
                minValue = 0,
                maxValue = 100,
                minLength = 0,
                maxLength = 5, -- in units
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
                characterRange = nil,
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

            behaviorPaths = {
                toggle = "Daneel/Behaviors/Toggle",
                --progressBar = "Daneel/Behaviors/ProgresBar",
                slider = "Daneel/Behaviors/Slider",
                --input = "Daneel/Behaviors/Input",
                --textArea = "Daneel/Behaviors/textArea",
            },
        },

        daneelComponentObjects = {
            Hud = Daneel.GUI.Hud,
            Toggle = Daneel.GUI.Toggle,
            ProgressBar = Daneel.GUI.ProgressBar,
            Slider = Daneel.GUI.Slider,
            Input = Daneel.GUI.Input,
            TextArea = Daneel.GUI.TextArea,
        },

        daneelObjects = {
            Vector2 = Vector2,
        },
    }
end

function DaneelAwakeModuleGUI()
    -- setting pixelToUnits  

    -- get the smaller side of the screen (usually screenSize.y, the height)
    local smallSideSize = Daneel.Config.gui.screenSize.y
    if Daneel.Config.gui.screenSize.x < Daneel.Config.gui.screenSize.y then
        smallSideSize = Daneel.Config.gui.screenSize.x
    end

    Daneel.Config.gui.cameraGO = GameObject.Get( Daneel.Config.gui.cameraName )

    if Daneel.Config.gui.cameraGO ~= nil then
        -- The orthographic scale value (in units) is equivalent to the smallest side size of the screen (in pixel)
        -- pixelsToUnits (in units/pixels) is the correspondance between screen pixels and scene units
        Daneel.GUI.pixelsToUnits = Daneel.Config.gui.cameraGO.camera:GetOrthographicScale() / smallSideSize
        --Daneel.GUI.pixelsToUnits = Daneel.Config.gui.cameraGO.camera.orthographicScale / smallSideSize

        Daneel.Config.gui.originGO = GameObject.New( "HUDOrigin", { parent = Daneel.Config.gui.cameraGO } )
        Daneel.Config.gui.originGO.transform:SetLocalPosition( Vector3:New(
            -Daneel.Config.gui.screenSize.x * Daneel.GUI.pixelsToUnits / 2, 
            Daneel.Config.gui.screenSize.y * Daneel.GUI.pixelsToUnits / 2,
            0
        ) )
        -- the HUDOrigin is now at the top-left corner of the screen
        Daneel.Config.gui.originPosition = Daneel.Config.gui.originGO.transform:GetPosition()
    end
end


----------------------------------------------------------------------------------
-- GUI

DaneelGUI = { pixelsToUnits = 0 }

-- convert a string value (maybe in pixels)
-- into a number of units
local function tounit(value)
    if type(value) == "string" then
        local length = #value
        if value:endswith("px") then
            value = tonumber(value:sub(0, length-2)) * Daneel.GUI.pixelsToUnits
        elseif value:endswith("u") then
            value = tonumber(value:sub(0, length-1))
        else
            value = tonumber(value)
        end
    end
    return value
end


----------------------------------------------------------------------------------
-- Hud

DaneelGUI.Hud = {}

--- Transform the 3D position into a Hud position and a layer.
-- @param position (Vector3) The 3D position.
-- @return (Vector2) The hud position.
-- @return (numbe) The layer.
function DaneelGUI.Hud.ToHudPosition(position)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Hud.ToHudPosition", position)
    local errorHead = "Daneel.GUI.Hud.ToHudPosition(hud, position) : "
    Daneel.Debug.CheckArgType(position, "position", "Vector3", errorHead)

    local layer = Daneel.Config.gui.originPosition.z - position.z
    position = position - Daneel.Config.gui.originPosition
    position = Vector2(
        position.x / Daneel.GUI.pixelsToUnits,
        -position.y / Daneel.GUI.pixelsToUnits
    )
    Daneel.Debug.StackTrace.EndFunction()
    return position, layer
end

-- Create a new Hud component instance.
-- @param gameObject (GameObject) The gameObject to add to the component to.
-- @return (Hud) The hud component.
function DaneelGUI.Hud.New(gameObject)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Hud.New", gameObject)
    Daneel.Debug.CheckArgType(gameObject, "gameObject", "GameObject", "Hud.New(gameObject) : ")
    if Daneel.Config.gui.cameraGO == nil then
        error("GUI was not set up or the HUD Camera gameObject with name '"..Daneel.Config.gui.cameraName.."' (value of Daneel.Config.gui.cameraName) was not found. Be sure that you call Daneel.Awake() early on from your scene and check your Daneel.Config.")
    end

    local hud = setmetatable({}, Daneel.GUI.Hud)
    hud.gameObject = gameObject
    hud.Id = math.round( math.randomrange( 100000, 999999 ) )
    hud.localPosition = Daneel.Config.gui.hud.localPosition
    hud.layer = Daneel.Config.gui.hud.layer
    gameObject.hud = hud
    Daneel.Debug.StackTrace.EndFunction()
    return hud
end

--- Sets the position of the gameObject on screen.
-- With the top-left corner of the screen as origin.
-- @param hud (Hud) The hud component.
-- @param position (Vector2) The position as a Vector2.
function DaneelGUI.Hud.SetPosition(hud, position)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Hud.SetPosition", hud, position)
    local errorHead = "Daneel.GUI.Hud.SetPosition(hud, position) : "
    Daneel.Debug.CheckArgType(hud, "hud", "Hud", errorHead)
    Daneel.Debug.CheckArgType(position, "position", "Vector2", errorHead)

    local newPosition = Daneel.Config.gui.originPosition + 
    Vector3:New(
        position.x * Daneel.GUI.pixelsToUnits,
        -position.y * Daneel.GUI.pixelsToUnits,
        0
    )
    newPosition.z = hud.gameObject.transform.position.z
    hud.gameObject.transform.position = newPosition
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the position of the provided hud on the screen.
-- @param hud (Hud) The hud component.
-- @return (Vector2) The position.
function DaneelGUI.Hud.GetPosition(hud)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Hud.GetPosition", hud)
    local errorHead = "Daneel.GUI.Hud.GetPosition(hud) : "
    Daneel.Debug.CheckArgType(hud, "hud", "Hud", errorHead)
    
    local position = hud.gameObject.transform.position - Daneel.Config.gui.originPosition
    position = position / Daneel.GUI.pixelsToUnits
    position = Vector2.New(math.round(position.x), math.round(-position.y))
    Daneel.Debug.StackTrace.EndFunction()
    return position
end

--- Sets the local position (relative to its parent) of the gameObject on screen .
-- @param hud (Hud) The hud component.
-- @param position (Vector2) The position as a Vector2.
function DaneelGUI.Hud.SetLocalPosition(hud, position)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Hud.SetLocalPosition", hud, position)
    local errorHead = "Daneel.GUI.Hud.SetLocalPosition(hud, position) : "
    Daneel.Debug.CheckArgType(hud, "hud", "Hud", errorHead)
    Daneel.Debug.CheckArgType(position, "position", "Vector2", errorHead)

    local parent = hud.gameObject.parent
    if parent == nil then parent = Daneel.Config.gui.originGO end
    local newPosition = parent.transform.position + 
    Vector3:New(
        position.x * Daneel.GUI.pixelsToUnits,
        -position.y * Daneel.GUI.pixelsToUnits,
        0
    )
    newPosition.z = hud.gameObject.transform.position.z
    hud.gameObject.transform.position = newPosition
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the local position (relative to its parent) of the gameObject on screen.
-- @param hud (Hud) The hud component.
-- @return (Vector2) The position.
function DaneelGUI.Hud.GetLocalPosition(hud)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Hud.GetLocalPosition", hud)
    local errorHead = "Daneel.GUI.Hud.GetLocalPosition(hud) : "
    Daneel.Debug.CheckArgType(hud, "hud", "Hud", errorHead)
    
    local parent = hud.gameObject.parent
    if parent == nil then parent = Daneel.Config.gui.originGO end
    local position = hud.gameObject.transform.position - parent.transform.position
    position = position / Daneel.GUI.pixelsToUnits
    position = Vector2.New(math.round(position.x), math.round(-position.y))
    Daneel.Debug.StackTrace.EndFunction()
    return position
end

--- Set the gameObject's layer.
-- @param hud (Hud) The hud component.
-- @param layer (number) The layer (a postive number).
function DaneelGUI.Hud.SetLayer(hud, layer)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Hud.SetLayer", hud)
    local errorHead = "Daneel.GUI.Hud.SetLayer(hud, layer) : "
    Daneel.Debug.CheckArgType(hud, "hud", "Hud", errorHead)
    Daneel.Debug.CheckArgType(layer, "layer", "number", errorHead)

    local originLayer = Daneel.Config.gui.originPosition.z
    local currentPosition = hud.gameObject.transform.position
    hud.gameObject.transform.position = Vector3:New(currentPosition.x, currentPosition.y, originLayer-layer)
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the gameObject's layer.
-- @param hud (Hud) The hud component.
-- @return (number) The layer.
function DaneelGUI.Hud.GetLayer(hud)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Hud.GetLayer", hud)
    local errorHead = "Daneel.GUI.Hud.GetLyer(hud) : "
    Daneel.Debug.CheckArgType(hud, "hud", "Hud", errorHead)

    local originLayer = Daneel.Config.gui.originPosition.z
    local layer = originLayer - hud.gameObject.transform.position.z 
    Daneel.Debug.StackTrace.EndFunction()
    return layer
end

--- Set the huds's local layer.
-- @param hud (Hud) The hud component.
-- @param layer (number) The layer (a postiv number).
function DaneelGUI.Hud.SetLocalLayer(hud, layer)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Hud.SetLayer", hud)
    local errorHead = "Daneel.GUI.Hud.SetLayer(hud, layer) : "
    Daneel.Debug.CheckArgType(hud, "hud", "Hud", errorHead)
    Daneel.Debug.CheckArgType(layer, "layer", "number", errorHead)

    local parent = hud.gameObject.parent
    if parent == nil then parent = Daneel.Config.gui.originGO end
    local originLayer = parent.transform.position.z
    local currentPosition = hud.gameObject.transform.position
    hud.gameObject.transform.position = Vector3:New(currentPosition.x, currentPosition.y, originLayer-layer)
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the gameObject's layer which is actually the inverse of its local position's z component.
-- @param hud (Hud) The hud component.
-- @return (number) The layer.
function DaneelGUI.Hud.GetLocalLayer(hud)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Hud.GetLayer", hud)
    local errorHead = "Daneel.GUI.Hud.GetLyer(hud) : "
    Daneel.Debug.CheckArgType(hud, "hud", "Hud", errorHead)

    local parent = hud.gameObject.parent
    if parent == nil then parent = Daneel.Config.gui.originGO end
    local originLayer = parent.transform.position.z
    local layer = originLayer - hud.gameObject.transform.position.z 
    Daneel.Debug.StackTrace.EndFunction()
    return layer
end


----------------------------------------------------------------------------------
-- Toggle

DaneelGUI.Toggle = {}

-- Create a new Toggle component.
-- @param gameObject (GameObject) The component gameObject.
-- @return (Toggle) The new component.
function DaneelGUI.Toggle.New( gameObject )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.Toggle.New", gameObject )
    local errorHead = "Daneel.GUI.Toggle.New(gameObject) : "
    Daneel.Debug.CheckArgType( gameObject, "gameObject", "GameObject", errorHead )
    
    local toggle = table.copy( Daneel.Config.gui.toggle )
    toggle.defaultText = toggle.text
    toggle.text = nil
    toggle.gameObject = gameObject
    toggle.Id = math.round( math.randomrange( 100000, 999999 ) )
    setmetatable( toggle, Daneel.GUI.Toggle )
    
    gameObject.toggle = toggle
    gameObject:AddTag( "guiComponent" )
    if gameObject:GetScriptedBehavior( Daneel.Config.gui.behaviorPaths.toggle ) == nil then
        gameObject:AddScriptedBehavior( Daneel.Config.gui.behaviorPaths.toggle )
    end

    if gameObject.textRenderer ~= nil and gameObject.textRenderer:GetText() ~= nil then
        toggle:SetText( gameObject.textRenderer:GetText() )
    end

    if gameObject.modelRenderer ~= nil then
        if toggle.isChecked and toggle.checkedModel ~= nil then
            toggle.gameObject.modelRenderer:SetModel( toggle.checkedModel )
        elseif not toggle.isChecked and toggle.uncheckedModel ~= nil then
            toggle.gameObject.modelRenderer:SetModel( toggle.uncheckedModel )
        end
    end

    toggle:Check( toggle.isChecked )

    Daneel.Debug.StackTrace.EndFunction()
    return toggle
end

--- Set the provided toggle's text.
-- Actually set the text of the TextRenderer component on the same gameObject,
-- but add the correct check mark in front of the provided text.
-- @param toggle (Toggle) The toggle component.
-- @param text (string) The text to display.
function DaneelGUI.Toggle.SetText( toggle, text )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.Toggle.SetText", toggle, text )
    local errorHead = "Daneel.GUI.Toggle.SetText( toggle, text ) : "
    Daneel.Debug.CheckArgType( toggle, "toggle", "Toggle", errorHead )
    Daneel.Debug.CheckArgType( text, "text", "string", errorHead )

    if toggle.gameObject.textRenderer ~= nil then
        if toggle.isChecked == true then
            text = Daneel.Utilities.ReplaceInString( toggle.checkedMark, { text = text } )
        else
            text = Daneel.Utilities.ReplaceInString( toggle.uncheckedMark, { text = text } )
        end
        toggle.gameObject.textRenderer.text = text

    else
        if DEBUG then
            print( "WARNING : "..errorHead.."Can't set the toggle's text because no TextRenderer component has been found on the gameObject '"..tostring( toggle.gameObject ).."'. Waiting for a TextRenderer to be added." )
        end
        toggle.defaultText = text
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the provided toggle's text.
-- Actually get the text of the TextRenderer component on the same gameObject but without the check mark.
-- @param toggle (Toggle) The toggle component.
-- @return (string) The text.
function DaneelGUI.Toggle.GetText(toggle)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Toggle.GetText", toggle)
    local errorHead = "Daneel.GUI.Toggle.GetText(toggle, text) : "
    Daneel.Debug.CheckArgType(toggle, "toggle", "Toggle", errorHead)

    local text = nil
    if toggle.gameObject.textRenderer ~= nil then
        local textMark = toggle.checkedMark
        if not toggle.isChecked then
            textMark = toggle.uncheckedMark
        end
        local start, _end = textMark:find(":text")
        local prefix = textMark:sub(1, start-1)
        local suffix = textMark:sub(_end+1)

        text = toggle.gameObject.textRenderer.text
        if text == nil then
            text = toggle.defaultText
        end
        text = text:gsub(prefix, ""):gsub(suffix, "")
    
    elseif DEBUG then
        print("WARNING : "..errorHead.."Can't get the toggle's text because no TextRenderer component has been found on the gameObject '"..tostring(toggle.gameObject).."'. Returning nil.")
    end
    Daneel.Debug.StackTrace.EndFunction()
    return text
end 

--- Check or uncheck the provided toggle and fire the OnUpdate event.
-- You can get the toggle's state via toggle.isChecked.
-- @param toggle (Toggle) The toggle component.
-- @param state [optional default=true] (boolean) The new state of the toggle.
-- @param forceUpdate [optional default=false] (boolean) Tell wether to force the updating of the state.
function DaneelGUI.Toggle.Check( toggle, state, forceUpdate )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.Toggle.Check", toggle, state, forceUpdate )
    local errorHead = "Daneel.GUI.Toggle.Check( toggle[, state, forceUpdate] ) : "
    Daneel.Debug.CheckArgType( toggle, "toggle", "Toggle", errorHead )
    state = Daneel.Debug.CheckOptionalArgType( state, "state", "boolean", errorHead, true )
    forceUpdate = Daneel.Debug.CheckOptionalArgType( forceUpdate, "forceUpdate", "boolean", errorHead, false ) 

    if forceUpdate or toggle.isChecked ~= state then
        local text = nil
        if toggle.gameObject.textRenderer ~= nil then
            text = toggle:GetText()
        end
        
        toggle.isChecked = state
        
        if toggle.gameObject.textRenderer ~= nil then
            toggle:SetText( text ) -- "reload" the check mark based on the new checked state

        elseif toggle.gameObject.modelRenderer ~= nil then
            if state == true and toggle.checkedModel ~= nil then
                toggle.gameObject.modelRenderer:SetModel( toggle.checkedModel )
            elseif state == false and toggle.uncheckedModel ~= nil then
                toggle.gameObject.modelRenderer:SetModel( toggle.uncheckedModel )
            end
        end

        Daneel.Event.Fire( toggle, "OnUpdate", toggle )

        if toggle._group ~= nil and state == true then
            local gameObjects = GameObject.Tags[ toggle._group ]
            for i, gameObject in ipairs( gameObjects ) do
                if gameObject ~= toggle.gameObject then
                    gameObject.toggle:Check( false )
                end
            end
        end
    end
    
    Daneel.Debug.StackTrace.EndFunction()
end

--- Set the toggle's group.
-- If the toggle was already in a group it will be removed from it.
-- @param toggle (Toggle) The toggle component.
-- @param group [optional] (string) The new group, or nil to remove from its group.
function DaneelGUI.Toggle.SetGroup(toggle, group)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Toggle.SetGroup", toggle, group)
    local errorHead = "Daneel.GUI.Toggle.SetGroup(toggle[, group]) : "
    Daneel.Debug.CheckArgType(toggle, "toggle", "Toggle", errorHead)
    Daneel.Debug.CheckOptionalArgType(group, "group", "string", errorHead)

    if group == nil and toggle._group ~= nil then
        toggle.gameObject:RemoveTag(toggle._group)
    else
        if toggle._group ~= nil then
            toggle.gameObject:RemoveTag(toggle._group)
        end
        toggle:Check(false)
        toggle._group = group
        toggle.gameObject:AddTag(toggle._group)
    end
    Daneel.Debug.StackTrace.EndFunction()
end

-- Get the toggle's group.
-- @param toggle (Toggle) The toggle component.
-- @return (string) The group, or nil.
function DaneelGUI.Toggle.GetGroup(toggle)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Toggle.GetGroup", toggle)
    local errorHead = "Daneel.GUI.Toggle.GetGroup(toggle) : "
    Daneel.Debug.CheckArgType(toggle, "toggle", "Toggle", errorHead)
    Daneel.Debug.StackTrace.EndFunction()
    return toggle._group
end


----------------------------------------------------------------------------------
-- ProgressBar

DaneelGUI.ProgressBar = {}

-- Create a new GUI.ProgressBar.
-- @param gameObject (GameObject) The component gameObject.
-- @return (ProgressBar) The new component.
function DaneelGUI.ProgressBar.New(gameObject)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.ProgressBar.New", gameObject)
    local errorHead = "Daneel.GUI.ProgressBar.New(gameObject) : "
    Daneel.Debug.CheckArgType(gameObject, "gameObject", "GameObject", errorHead)

    local progressBar = table.copy(Daneel.Config.gui.progressBar)
    progressBar.gameObject = gameObject
    progressBar.Id = math.round( math.randomrange( 100000, 999999 ) )
    progressBar.progress = nil -- remove the property to allow to use the dynamic getter/setter
    setmetatable(progressBar, Daneel.GUI.ProgressBar)
    progressBar.progress = Daneel.Config.gui.progressBar.progress
    
    gameObject.progressBar = progressBar

    Daneel.Debug.StackTrace.EndFunction()
    return progressBar
end

--- Set the progress of the progress bar, adjusting its length.
-- Fires the 'OnUpdate' event.
-- @param progressBar (ProgressBar) The progressBar.
-- @param progress (number or string) The progress as a number (between minVal and maxVal) or as a string and a percentage (between "0%" and "100%").
function DaneelGUI.ProgressBar.SetProgress(progressBar, progress)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.ProgressBar.SetProgress", progressBar, progress)
    local errorHead = "Daneel.GUI.ProgressBar.SetProgress(progressBar, progress) : "
    Daneel.Debug.CheckArgType(progressBar, "progressBar", "ProgressBar", errorHead)
    Daneel.Debug.CheckArgType(progress, "progress", {"string", "number"}, errorHead)

    local minVal = progressBar.minValue
    local maxVal = progressBar.maxValue
    local percentageOfProgress = nil

    if type(progress) == "string" then
        if progress:endswith("%") then
            percentageOfProgress = tonumber(progress:sub(1, #progress-1)) / 100

            local oldPercentage = percentageOfProgress
            percentageOfProgress = math.clamp(percentageOfProgress, 0.0, 1.0)
            if percentageOfProgress ~= oldPercentage and DEBUG == true then
                print(errorHead.."WARNING : progress in percentage with value '"..progress.."' is below 0% or above 100%.")
            end

            progress = (maxVal - minVal) * percentageOfProgress + minVal
        else
            progress = tonumber(progress)
        end
    end

    -- now progress is a number and should be a value between minVal and maxVal
    local oldProgress = progress
    progress = math.clamp(progress, minVal, maxVal)

    progressBar.minLength = tounit(progressBar.minLength)
    progressBar.maxLength = tounit(progressBar.maxLength)
    local currentProgress = progressBar.progress

    if progress ~= currentProgress then
        if progress ~= oldProgress and DEBUG == true then
            print(errorHead.." WARNING : progress with value '"..oldProgress.."' is out of its boundaries : min='"..minVal.."', max='"..maxVal.."'")
        end
        percentageOfProgress = (progress - minVal) / (maxVal - minVal)
        
        progressBar.height = tounit(progressBar.height)

        local newLength = (progressBar.maxLength - progressBar.minLength) * percentageOfProgress + progressBar.minLength 
        local currentScale = progressBar.gameObject.transform.localScale
        progressBar.gameObject.transform.localScale = Vector3:New(newLength, progressBar.height, currentScale.z)
        -- newLength = scale only because the base size of the model is of one unit at a scale of one

        Daneel.Event.Fire(progressBar, "OnUpdate", progressBar)
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Set the progress of the progress bar, adjusting its length.
-- Does the same things as SetProgress() by does it faster. 
-- Unlike SetProgress(), does not fire the 'OnUpdate' event by default.
-- Should be used when the progress is updated regularly (ie : from a Behavior:Update() function).
-- @param progressBar (ProgressBar) The progressBar.
-- @param progress (number or string) The progress as a number (between minVal and maxVal) or as a string and a percentage (between "0%" and "100%").
-- @param fireEvent [optional default=false] (boolean) Tell wether to fire the 'OnUpdate' event (true) or not (false).
function DaneelGUI.ProgressBar.UpdateProgress( progressBar, progress, fireEvent )
    if progress == progressBar._progress then return end
    progressBar._progress = progress

    local minVal = progressBar.minValue
    local maxVal = progressBar.maxValue
    local minLength = progressBar.minLength
    local percentageOfProgress = nil

    if type(progress) == "string" then
        local _progress = progress
        progress = tonumber(progress)
        if progress == nil then -- progress in percentage. ie "50%"
            percentageOfProgress = tonumber( _progress:sub( 1, #_progress-1 ) ) / 100
        end
    end

    if percentageOfProgress == nil then
        percentageOfProgress = (progress - minVal) / (maxVal - minVal)
    end
    percentageOfProgress = math.clamp( percentageOfProgress, 0.0, 1.0 )

    local newLength = (progressBar.maxLength - minLength) * percentageOfProgress + minLength 
    local currentScale = progressBar.gameObject.transform.localScale
    progressBar.gameObject.transform.localScale = Vector3:New( newLength, progressBar.height, currentScale.z )
    
    if fireEvent == true then
        Daneel.Event.Fire( progressBar, "OnUpdate", progressBar )
    end
end

--- Get the current progress of the progress bar.
-- @param progressBar (ProgressBar) The progressBar.
-- @param getAsPercentage [optional default=false] (boolean) Get the progress as a percentage (between 0 and 100) instead of an absolute value.
-- @return (number) The progress.
function DaneelGUI.ProgressBar.GetProgress(progressBar, getAsPercentage)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.ProgressBar.GetProgress", progressBar, getAsPercentage)
    local errorHead = "Daneel.GUI.ProgressBar.GetProgress(progressBar[, getAsPercentage]) : "
    Daneel.Debug.CheckArgType(progressBar, "progressBar", "ProgressBar", errorHead)
    Daneel.Debug.CheckOptionalArgType(getAsPercentage, "getAsPercentage", "boolean", errorHead)

    local scale = progressBar.gameObject.transform.localScale.x
    local progress = (scale - progressBar.minLength) / (progressBar.maxLength - progressBar.minLength)
    if getAsPercentage == true then
        progress = progress * 100
    else
        progress = (progressBar.maxValue - progressBar.minValue) * progress + progressBar.minValue
    end
    progress = math.round(progress)
    Daneel.Debug.StackTrace.EndFunction()
    return progress
end


----------------------------------------------------------------------------------
-- Slider

DaneelGUI.Slider = {}

-- Create a new GUI.Slider.
-- @param gameObject (GameObject) The component gameObject.
-- @return (Slider) The new component.
function DaneelGUI.Slider.New(gameObject)
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.Slider.New", gameObject )
    local errorHead = "Daneel.GUI.Slider.New( gameObject ) : "
    Daneel.Debug.CheckArgType( gameObject, "gameObject", "GameObject", errorHead )

    local slider = table.copy( Daneel.Config.gui.slider )
    slider.gameObject = gameObject
    slider.Id = math.round( math.randomrange( 100000, 999999 ) )
    slider.startPosition = gameObject.transform.position
    slider.value = nil
    setmetatable( slider, Daneel.GUI.Slider )
    slider.value = Daneel.Config.gui.slider.value
    
    gameObject.slider = slider
    gameObject:AddTag( "guiComponent" )
    if gameObject:GetScriptedBehavior( Daneel.Config.gui.behaviorPaths.slider ) == nil then
        gameObject:AddScriptedBehavior( Daneel.Config.gui.behaviorPaths.slider )
    end
    
    Daneel.Debug.StackTrace.EndFunction()
    return slider
end

--- Set the value of the slider, adjusting its position.
-- @param slider (Slider) The slider.
-- @param value (number or string) The value as a number (between minVal and maxVal) or as a string and a percentage (between "0%" and "100%").
function DaneelGUI.Slider.SetValue( slider, value )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.Slider.SetValue", slider, value )
    local errorHead = "Daneel.GUI.Slider.SetValue( slider, value ) : "
    Daneel.Debug.CheckArgType( slider, "slider", "Slider", errorHead )
    Daneel.Debug.CheckArgType( value, "value", {"string", "number"}, errorHead )

    local maxVal = slider.maxValue
    local minVal = slider.minValue
    local percentage = nil

    if type( value ) == "string" then
        if value:endswith( "%" ) then
            percentage = tonumber( value:sub( 1, #value-1 ) ) / 100
            value = (maxVal - minVal) * percentage + minVal
        else
            value = tonumber( value )
        end
    end

    -- now value is a number and should be a value between minVal and maxVal
    local oldValue = value
    value = math.clamp( value, minVal, maxVal )
    if value ~= oldValue and DEBUG == true then
        print( errorHead .. "WARNING : Argument 'value' with value '" .. oldValue .. "' is out of its boundaries : min='" .. minVal .. "', max='" .. maxVal .. "'" )
    end
    percentage = (value - minVal) / (maxVal - minVal)

    slider.length = tounit( slider.length )

    local direction = -Vector3:Left()
    if slider.axis == "y" then
        direction = Vector3:Up()
    end
    local orientation = Vector3.Transform( direction, slider.gameObject.transform.orientation )
    local newPosition = slider.startPosition + orientation * slider.length * percentage
    slider.gameObject.transform.position = newPosition

    Daneel.Event.Fire( slider, "OnUpdate", slider )
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the current slider's value.
-- @param slider (Slider) The slider.
-- @param getAsPercentage [optional default=false] (boolean) Get the value as a percentage (between 0 and 100) instead of an absolute value.
-- @return (number) The value.
function DaneelGUI.Slider.GetValue(slider, getAsPercentage)
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Slider.GetValue", slider, getAsPercentage)
    local errorHead = "Daneel.GUI.Slider.GetValue(slider, value) : "
    Daneel.Debug.CheckArgType(slider, "slider", "Slider", errorHead)
    Daneel.Debug.CheckOptionalArgType(getAsPercentage, "getAsPercentage", "boolean", errorHead)
   
    local percentage = Vector3.Distance(slider.startPosition, slider.gameObject.transform.position) / slider.length
    local value = percentage * 100
    if getAsPercentage ~= true then
        value = (slider.maxValue - slider.minValue) * percentage + slider.minValue
    end
    value = math.round(value) -- ??
    Daneel.Debug.StackTrace.EndFunction()
    return value
end


----------------------------------------------------------------------------------
-- Input

DaneelGUI.Input = {}

-- Create a new GUI.Input.
-- @param gameObject (GameObject) The component gameObject.
-- @return (Input) The new component.
function DaneelGUI.Input.New( gameObject )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.Input.New", gameObject )
    local errorHead = "Daneel.GUI.Input.New(gameObject) : "
    Daneel.Debug.CheckArgType( gameObject, "gameObject", "GameObject", errorHead )

    local input = table.copy( Daneel.Config.gui.input )
    input.gameObject = gameObject
    input.Id = math.round( math.randomrange( 100000, 999999 ) )
    -- adapted from Blast Turtles
    input.OnTextEntered = function( char )
        if not input.isFocused then return end
        local charNumber = string.byte( char )
        
        if charNumber == 8 then -- Backspace
            local text = gameObject.textRenderer.text
            input:Update( text:sub( 1, #text - 1 ), true )
        
        elseif charNumber == 13 then -- Enter
            Daneel.Event.Fire( input, "OnValidate", input )
        
        -- Any character between 32 and 127 is regular printable ASCII
        elseif charNumber >= 32 and charNumber <= 127 then
            if input.characterRange ~= nil and input.characterRange:find( char ) == nil then
                return
            end
            input:Update( char )
        end
    end
    setmetatable( input, Daneel.GUI.Input )

    gameObject.input = input
    gameObject:AddTag( "guiComponent" )
    
    Daneel.Event.Listen( "OnLeftMouseButtonJustPressed", 
        function()
            if gameObject.isMouseOver == nil then
                gameObject.isMouseOver = false
            end
            gameObject.input:Focus( gameObject.isMouseOver )
        end 
    )

    Daneel.Debug.StackTrace.EndFunction()
    return input
end

-- Set the focused state of the input.
-- @param input (Input) The input component.
-- @param state [optional default=true] (boolean) The new state.
function DaneelGUI.Input.Focus( input, state )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.Input.Focus", input, state )
    local errorHead = "Daneel.GUI.Input.Focus(input[, state]) : "
    Daneel.Debug.CheckArgType( input, "input", "Input", errorHead )
    state = Daneel.Debug.CheckOptionalArgType( state, "state", "boolean", errorHead, true )
    
    if input.isFocused ~= state then
        input.isFocused = state
        if state == true then
            CS.Input.OnTextEntered( input.OnTextEntered )
        else
            CS.Input.OnTextEntered( nil )
        end
        Daneel.Event.Fire( input, "OnFocus", input )
    end
    Daneel.Debug.StackTrace.EndFunction()
end

-- Set the focused state of the input.
-- @param input (Input) The input component.
-- @param text (string) The text to add to the current text.
-- @param replaceText [optional default=false] (boolean) Tell wether the provided text should be added (false) or replace (true) the current text.
function DaneelGUI.Input.Update( input, text, replaceText )
    Daneel.Debug.StackTrace.BeginFunction("Daneel.GUI.Input.Update", input, text)
    local errorHead = "Daneel.GUI.Input.Update(input, text) : "
    Daneel.Debug.CheckArgType(input, "input", "Input", errorHead)
    Daneel.Debug.CheckArgType(text, "text", "string", errorHead)
    replaceText = Daneel.Debug.CheckOptionalArgType(replaceText, "replaceText", "boolean", errorHead, false)

    if input.isFocused == false then 
        Daneel.Debug.StackTrace.EndFunction()
        return
    end
    
    local oldText = input.gameObject.textRenderer.text
    if replaceText == false then
        text = oldText .. text
    end
    if #text > input.maxLength then
        text = text:sub( 1, input.maxLength )
    end
    if oldText ~= text then
        input.gameObject.textRenderer.text = text
        Daneel.Event.Fire( input, "OnUpdate", input )
    end
    Daneel.Debug.StackTrace.EndFunction()
end


----------------------------------------------------------------------------------
-- TextArea

DaneelGUI.TextArea = {}

--- Creates a new TextArea component.
-- @param gameObject (GameObject) The game object.
-- @return (TextArea) The new component.
function DaneelGUI.TextArea.New( gameObject )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.TextArea.New", gameObject )
    local errorHead = "Daneel.GUI.TextArea.New( gameObject ) : "
    Daneel.Debug.CheckArgType( gameObject, "gameObject", "GameObject", errorHead )

    local textArea = {}
    textArea.gameObject = gameObject
    textArea.Id = math.round( math.randomrange( 100000, 999999 ) )
    textArea.lineRenderers = {}
    setmetatable( textArea, Daneel.GUI.TextArea )

    gameObject:AddComponent( "TextRenderer" ) -- used to store the TextRenderer properties and mesure the lines length in SetText()
    textArea:Set( Daneel.Config.gui.textArea )

    gameObject.textArea = textArea
    Daneel.Debug.StackTrace.EndFunction()
    return textArea
end

--- Set the component's text.
-- @param textArea (TextArea) The textArea component.
-- @param text (string) The text to display.
function DaneelGUI.TextArea.SetText( textArea, text )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.TextArea.SetText", textArea, text )
    local errorHead = "Daneel.GUI.TextArea.SetText( textArea, text ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    Daneel.Debug.CheckArgType( text, "text", "string", errorHead )

    textArea.Text = text

    local lines = { text }
    if textArea.newLine ~= "" then
        lines = text:split( textArea.NewLine )
    end

    -- areaWidth is the max length in units of each line
    local areaWidth = textArea.AreaWidth
    if areaWidth ~= nil and areaWidth > 0 then
        -- cut the lines based on their length
        local tempLines = table.copy( lines )
        lines = {}

        for i = 1, #tempLines do
            local line = tempLines[i]
            
            if textArea.gameObject.textRenderer:GetTextWidth( line ) > areaWidth then
                line = line:totable()
                local newLine = {}
                
                for j, char in ipairs( line ) do
                    table.insert( newLine, char )

                    if textArea.gameObject.textRenderer:GetTextWidth( table.concat( newLine ) ) > areaWidth then  
                        table.remove( newLine )
                        table.insert( lines, table.concat( newLine ) )
                        newLine = { char }
                                 
                        if not textArea.WordWrap then
                            newLine = nil
                            break
                        end
                    end
                end
                
                if newLine ~= nil then
                    table.insert( lines, table.concat( newLine ) )
                end
            else
                table.insert( lines, line )
            end
        end -- end loop on lines
    end
    
    local linesCount = #lines
    local lineRenderers = textArea.lineRenderers
    local lineRenderersCount = #lineRenderers
    local lineHeight = textArea.LineHeight
    local gameObject = textArea.gameObject
    local textRendererParams = {
        font = textArea.Font,
        alignment = textArea.Alignment,
        opacity = textArea.Opacity,
    }

    -- calculate position offset based on vertical alignment and number of lines
    local offset = -lineHeight / 2 -- verticalAlignment = "top"
    if textArea.VerticalAlignment == "middle" then
        offset = lineHeight * linesCount / 2 - lineHeight / 2
    elseif textArea.VerticalAlignment == "bottom" then
        offset = lineHeight * linesCount
    end

    for i, line in ipairs( lines ) do
        textRendererParams.text = line

        if lineRenderers[i] ~= nil then
            lineRenderers[i].gameObject.transform:SetLocalPosition( Vector3:New( 0, offset, 0 ) )
            lineRenderers[i]:SetText( line )
        else
            local newLineGO = GameObject.New( "TextAreaLine-" .. textArea.Id .. "-" .. i, {
                parent = gameObject,
                transform = {
                    localPosition = Vector3:New( 0, offset, 0 )
                },
                textRenderer = textRendererParams
            })

            table.insert( lineRenderers, newLineGO.textRenderer )
        end

        offset = offset - textArea.lineHeight
    end

    -- this new text as less lines than the previous one
    if lineRenderersCount > linesCount then
        for i = linesCount + 1, lineRenderersCount do
            lineRenderers[i]:SetText( "" )
        end
    end

    Daneel.Event.Fire( textArea, "OnUpdate", textArea)
    
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the component's text.
-- @param textArea (TextArea) The textArea component.
-- @return (string) The component's text.
function DaneelGUI.TextArea.GetText( textArea )
    local errorHead = "Daneel.GUI.TextArea.GetText( textArea ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    return textArea.Text
end

--- Set the component's area width (maximum line length).
-- Must be strictly positive to have an effect.
-- Set as a negative value, 0 or nil to remove the limitation.
-- @param textArea (TextArea) The textArea component.
-- @param areaWidth (number or string) The area width in scene units or in pixels as a string suffixed with "px".
function DaneelGUI.TextArea.SetAreaWidth( textArea, areaWidth )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.TextArea.SetAreaWidth", textArea, areaWidth )
    local errorHead = "Daneel.GUI.TextArea.SetAreaWidth( textArea, areaWidth ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    Daneel.Debug.CheckOptionalArgType( areaWidth, "areaWidth", {"string", "number"}, errorHead )

    if areaWidth ~= nil then
        areaWidth = math.clamp( tounit( areaWidth ), 0, 999999 )
    end

    if textArea.AreaWidth ~= areaWidth then
        textArea.AreaWidth = areaWidth
        if #textArea.lineRenderers > 0 then
            textArea:SetText( textArea.Text )
        end
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the component's area width.
-- @param textArea (TextArea) The textArea component.
-- @return (number) The area width in scene units.
function DaneelGUI.TextArea.GetAreaWidth( textArea )
    local errorHead = "Daneel.GUI.TextArea.GetAreaWidth( textArea ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    return textArea.AreaWidth
end

--- Set the component's wordWrap property.
-- Define what happens when the lines are longer then the area width.
-- @param textArea (TextArea) The textArea component.
-- @param wordWrap (boolean) Cut the line when false, or creates new additional lines with the remaining text when true.
function DaneelGUI.TextArea.SetWordWrap( textArea, wordWrap )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.TextArea.SetWordWrap", textArea, wordWrap )
    local errorHead = "Daneel.GUI.TextArea.SetWordWrap( textArea, wordWrap ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    Daneel.Debug.CheckArgType( wordWrap, "wordWrap", "boolean", errorHead )

    textArea.WordWrap = wordWrap
    if #textArea.lineRenderers > 0 then
        textArea:SetText( textArea.Text )
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the component's wordWrap property.
-- @param textArea (TextArea) The textArea component.
-- @return (boolean) True or false.
function DaneelGUI.TextArea.GetWordWrap( textArea )
    local errorHead = "Daneel.GUI.TextArea.GetWordWrap( textArea ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    return textArea.WordWrap
end

--- Set the component's newLine string used by SetText() to split the input text in several lines.
-- @param textArea (TextArea) The textArea component.
-- @param newLine (string) The newLine string (one or several character long). Set "\n" to split multiline strings.
function DaneelGUI.TextArea.SetNewLine( textArea, newLine )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.TextArea.SetNewLine", textArea, newLine )
    local errorHead = "Daneel.GUI.TextArea.SetNewLine( textArea, newLine ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    Daneel.Debug.CheckArgType( newLine, "newLine", "string", errorHead )

    textArea.NewLine = newLine
    if #textArea.lineRenderers > 0 then
        textArea:SetText( textArea.Text )
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the component's newLine string.
-- @param textArea (TextArea) The textArea component.
-- @return (string) The newLine string.
function DaneelGUI.TextArea.GetNewLine( textArea )
    local errorHead = "Daneel.GUI.TextArea.GetNewLine( textArea ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    return textArea.NewLine
end

--- Set the component's line height.
-- @param textArea (TextArea) The textArea component.
-- @param lineHeight (number or string) The line height in scene units or in pixels as a string suffixed with "px".
function DaneelGUI.TextArea.SetLineHeight( textArea, lineHeight )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.TextArea.SetLineHeight", textArea, lineHeight )
    local errorHead = "Daneel.GUI.TextArea.SetLineHeight( textArea, lineHeight ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    Daneel.Debug.CheckArgType( lineHeight, "lineHeight", {"string", "number"}, errorHead )

    textArea.LineHeight = tounit( lineHeight )
    if #textArea.lineRenderers > 0 then
        textArea:SetText( textArea.Text )
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the component's line height.
-- @param textArea (TextArea) The textArea component.
-- @return (number) The line height in scene units.
function DaneelGUI.TextArea.GetLineHeight( textArea )
    local errorHead = "Daneel.GUI.TextArea.GetLineHeight( textArea ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    return textArea.LineHeight
end

--- Set the component's vertical alignment.
-- @param textArea (TextArea) The textArea component.
-- @param verticalAlignment (string) "top", "middle" or "bottom". Case-insensitive.
function DaneelGUI.TextArea.SetVerticalAlignment( textArea, verticalAlignment )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.TextArea.SetVerticalAlignment", textArea, verticalAlignment )
    local errorHead = "Daneel.GUI.TextArea.SetVerticalAlignment( textArea, verticalAlignment ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    Daneel.Debug.CheckArgType( verticalAlignment, "verticalAlignment", "string", errorHead )
    verticalAlignment = Daneel.Debug.CheckArgValue( verticalAlignment, "verticalAlignment", {"top", "middle", "bottom"}, errorHead, "top" )

    textArea.VerticalAlignment = verticalAlignment:lower():trim()
    if #textArea.lineRenderers > 0 then
        textArea:SetText( textArea.Text )
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the component's vertical alignment property.
-- @param textArea (TextArea) The textArea component.
-- @return (string) The vertical alignment.
function DaneelGUI.TextArea.GetVerticalAlignment( textArea )
    local errorHead = "Daneel.GUI.TextArea.GetVerticalAlignment( textArea ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    return textArea.VerticalAlignment
end

--- Set the component's font used to renderer the text.
-- @param textArea (TextArea) The textArea component.
-- @param font (Font or string) The font asset or fully-qualified path.
function DaneelGUI.TextArea.SetFont( textArea, font )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.TextArea.SetFont", textArea, font )
    local errorHead = "Daneel.GUI.TextArea.SetFont( textArea, font ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    Daneel.Debug.CheckArgType( font, "font", {"string", "Font"}, errorHead )

    textArea.gameObject.textRenderer:SetFont( font )
    textArea.Font = textArea.gameObject.textRenderer:GetFont()

    if #textArea.lineRenderers > 0 then
        for i, textRenderer in ipairs( textArea.lineRenderers ) do
            textRenderer:SetFont( textArea.Font )
        end
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the component's font used to render the text.
-- @param textArea (TextArea) The textArea component.
-- @return (Font) The font.
function DaneelGUI.TextArea.GetFont( textArea )
    local errorHead = "Daneel.GUI.TextArea.GetFont( textArea ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    return textArea.Font
end

--- Set the component's alignment.
-- Works like a TextRenderer alignment.
-- @param textArea (TextArea) The textArea component.
-- @param alignment (TextRenderer.Alignment or string) One of the values in the 'TextRenderer.Alignment' enum (Left, Center or Right) or the same values as case-insensitive string ("left", "center" or "right").
function DaneelGUI.TextArea.SetAlignment( textArea, alignment )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.TextArea.SetAlignment", textArea, alignment )
    local errorHead = "Daneel.GUI.TextArea.SetAlignment( textArea, alignment ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    Daneel.Debug.CheckArgType( alignment, "alignment", {"string", "userdata"}, errorHead )

    textArea.gameObject.textRenderer:SetAlignment( alignment )
    textArea.Alignment = textArea.gameObject.textRenderer:GetAlignment()

    if #textArea.lineRenderers > 0 then
        for i, textRenderer in ipairs( textArea.lineRenderers ) do
            textRenderer:SetAlignment( textArea.Alignment )
        end
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the component's horizontal alignment.
-- @param textArea (TextArea) The textArea component.
-- @return (TextRenderer.Alignment) The alignment.
function DaneelGUI.TextArea.GetAlignment( textArea )
    local errorHead = "Daneel.GUI.TextArea.GetAlignment( textArea ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    return textArea.Alignment
end

--- Set the component's opacity.
-- @param textArea (TextArea) The textArea component.
-- @param opacity (number) The opacity between 0.0 and 1.0.
function DaneelGUI.TextArea.SetOpacity( textArea, opacity )
    Daneel.Debug.StackTrace.BeginFunction( "Daneel.GUI.TextArea.SetOpacity", textArea, opacity )
    local errorHead = "Daneel.GUI.TextArea.SetOpacity( textArea, opacity ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    Daneel.Debug.CheckArgType( opacity, "opacity", "number", errorHead )

    textArea.Opacity = opacity
    if #textArea.lineRenderers > 0 then
        for i, textRenderer in ipairs( textArea.lineRenderers ) do
            textRenderer:SetOpacity( opacity )
        end
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Get the component's opacity.
-- @param textArea (TextArea) The textArea component.
-- @return (number) The opacity between 0.0 and 1.0.
function DaneelGUI.TextArea.GetOpacity( textArea )
    local errorHead = "Daneel.GUI.TextArea.GetOpacity( textArea ) : "
    Daneel.Debug.CheckArgType( textArea, "textArea", "TextArea", errorHead )
    return textArea.Opacity
end


----------------------------------------------------------------------------------
-- Vector 2

Vector2 = {}
Vector2.__index = Vector2
setmetatable(Vector2, { __call = function(Object, ...) return Object.New(...) end })

function Vector2.__tostring(vector2)
    return "Vector2: { x="..vector2.x..", y="..vector2.y.." }"
end

--- Creates a new Vector2 intance.
-- @param x (number or string) The vector's x component.
-- @param y [optional] (number or string) The vector's y component. If nil, will be equal to x. 
-- @return (Vector2) The new instance.
function Vector2.New(x, y)
    Daneel.Debug.StackTrace.BeginFunction("Vector2.New", x, y)
    local errorHead = "Vector2.New(x, y) : "
    Daneel.Debug.CheckArgType(x, "x", {"string", "number"}, errorHead)
    Daneel.Debug.CheckOptionalArgType(y, "y", {"string", "number"}, errorHead)
    
    if y == nil then y = x end
    local vector = setmetatable({ x = x, y = y }, Vector2)
    Daneel.Debug.StackTrace.EndFunction()
    return vector
end

--- Allow to add two Vector2 by using the + operator.
-- Ie : vector1 + vector2
-- @param a (Vector2) The left member.
-- @param b (Vector2) The right member.
-- @return (Vector2) The new vector.
function Vector2.__add(a, b)
    Daneel.Debug.StackTrace.BeginFunction("Vector2.__add", a, b)
    local errorHead = "Vector2.__add(a, b) : "
    Daneel.Debug.CheckArgType(a, "a", "Vector2", errorHead)
    Daneel.Debug.CheckArgType(b, "b", "Vector2", errorHead)
    a = Vector2.New(a.x + b.x, a.y + b.y)
    Daneel.Debug.StackTrace.EndFunction()
    return a
end

--- Allow to substract two Vector2 by using the - operator.
-- Ie : vector1 - vector2
-- @param a (Vector2) The left member.
-- @param b (Vector2) The right member.
-- @return (Vector2) The new vector.
function Vector2.__sub(a, b)
    Daneel.Debug.StackTrace.BeginFunction("Vector2.__sub", a, b)
    local errorHead = "Vector2.__sub(a, b) : "
    Daneel.Debug.CheckArgType(a, "a", "Vector2", errorHead)
    Daneel.Debug.CheckArgType(b, "b", "Vector2", errorHead)
    a = Vector2.New(a.x - b.x, a.y - b.y)
    Daneel.Debug.StackTrace.EndFunction()
    return a
end

--- Allow to multiply two Vector2 or a Vector2 and a number by using the * operator.
-- @param a (Vector2 or number) The left member.
-- @param b (Vector2 or number) The right member.
-- @return (Vector2) The new vector.
function Vector2.__mul(a, b)
    Daneel.Debug.StackTrace.BeginFunction("Vector2.__mull", a, b)
    local errorHead = "Vector2.__mul(a, b) : "
    Daneel.Debug.CheckArgType(a, "a", {"Vector2", "number"}, errorHead)
    Daneel.Debug.CheckArgType(b, "b", {"Vector2", "number"}, errorHead)
    local newVector = 0
    if type(a) == "number" then
        newVector = Vector2.New(a * b.x, a * b.y)
    elseif type(b) == "number" then
        newVector = Vector2.New(a.x * b, a.y * b)
    else
        newVector = Vector2.New(a.x * b.x, a.y * b.y)
    end
    Daneel.Debug.StackTrace.EndFunction()
    return newVector
end

--- Allow to divide two Vector2 or a Vector2 and a number by using the / operator.
-- @param a (Vector2 or number) The numerator.
-- @param b (Vector2 or number) The denominator. Can't be equal to 0.
-- @return (Vector2) The new vector.
function Vector2.__div(a, b)
    Daneel.Debug.StackTrace.BeginFunction("Vector2.__div", a, b)
    local errorHead = "Vector2.__div(a, b) : "
    Daneel.Debug.CheckArgType(a, "a", {"Vector2", "number"}, errorHead)
    Daneel.Debug.CheckArgType(b, "b", {"Vector2", "number"}, errorHead)
    local newVector = 0
    if type(a) == "number" then
        if b.x == 0 or b.y == 0 then
            error(errorHead.."One of the components of the denominator is equal to 0. Can't divide by 0 ! b.x="..b.x.." b.y="..b.y)
        end
        newVector = Vector2.New(a / b.x, a / b.y)
    elseif type(b) == "number" then
        if b == 0 then
            error(errorHead.."The denominator is equal to 0 ! Can't divide by 0 !")
        end
        newVector = Vector2.New(a.x / b, a.y / b)
    else
        if b.x == 0 or b.y == 0 then
            error(errorHead.."One of the components of the denominator is equal to 0. Can't divide by 0 ! b.x="..b.x.." b.y="..b.y)
        end
        newVector = Vector2.New(a.x / b.x, a.y / b.y)
    end
    Daneel.Debug.StackTrace.EndFunction()
    return newVector
end

--- Allow to inverse a vector2 using the - operator.
-- @param vector (Vector2) The vector.
-- @return (Vector2) The new vector.
function Vector2.__unm(vector)
    Daneel.Debug.StackTrace.BeginFunction("Vector2.__unm", vector)
    local errorHead = "Vector2.__unm(vector) : "
    Daneel.Debug.CheckArgType(vector, "vector", "Vector2", errorHead)
    local vector = Vector2.New(-vector.x, -vector.y)
    Daneel.Debug.StackTrace.EndFunction()
    return vector
end

--- Allow to raise a Vector2 to a power using the ^ operator.
-- @param vector (Vector2) The vector.
-- @param exp (number) The power to raise the vector to.
-- @return (Vector2) The new vector.
function Vector2.__pow(vector, exp)
    Daneel.Debug.StackTrace.BeginFunction("Vector2.__pow", vector, exp)
    local errorHead = "Vector2.__pow(vector, exp) : "
    Daneel.Debug.CheckArgType(vector, "vector", "Vector2", errorHead)
    Daneel.Debug.CheckArgType(exp, "exp", "number", errorHead)
    vector = Vector2.New(vector.x ^ exp, vector.y ^ exp)
    Daneel.Debug.StackTrace.EndFunction()
    return vector
end

--- Allow to check for the equality between two Vector2 using the == comparison operator.
-- @param a (Vector2) The left member.
-- @param b (Vector2) The right member.
-- @return (boolean) True if the same components of the two vectors are equal (a.x=b.x and a.y=b.y)
function Vector2.__eq(a, b)
    Daneel.Debug.StackTrace.BeginFunction("Vector2.__eq", a, b)
    local errorHead = "Vector2.__eq(a, b) : "
    Daneel.Debug.CheckArgType(a, "a", "Vector2", errorHead)
    Daneel.Debug.CheckArgType(b, "b", "Vector2", errorHead)
    local eq = ((a.x == b.x) and (a.y == b.y))
    Daneel.Debug.StackTrace.EndFunction()
    return eq
end

--- Return the length of the vector.
-- @param vector (Vector2) The vector.
function Vector2.GetLength(vector)
    return math.sqrt(vector.x^2 + vector.y^2)
end
