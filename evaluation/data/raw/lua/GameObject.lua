-- GameObject.lua
-- Extends the GameObject object.
--
-- Last modified for v1.2.0
-- Copyright © 2013 Florent POUJOL, published under the MIT licence.

setmetatable(GameObject, { __call = function(Object, ...) return Object.New(...) end })

function GameObject.__tostring(gameObject)
    if gameObject.isDestroyed == true then
        return "Destroyed gameObject: " .. Daneel.Debug.ToRawString( gameObject )
        -- the important here was to prevent throwing an error
    end
    -- returns something like "GameObject: 123456789: 'MyName'"
    -- do not use gameObject:GetID() here, it throws a stack overflow when stacktrace is enabled (BeginFunction uses tostring() on the input argument)
    local id = gameObject.Id
    if id == nil then
        id = tostring( gameObject.inner ):sub( 5, 20 )
        gameObject.Id = id
    end
    return "GameObject: " .. id .. ": '" .. gameObject:GetName() .. "'"
end

-- Dynamic getters
function GameObject.__index( gameObject, key )
    if GameObject[ key ] ~= nil then
        return GameObject[ key ]
    end

    -- maybe the key is a script alias
    local path = Daneel.Config.scriptPaths[ key ]
    if path ~= nil then
        local behavior = gameObject:GetScriptedBehavior( path )
        if behavior ~= nil then
            rawset( gameObject, key, behavior )
            return behavior
        end
    end

    local ucKey = key:ucfirst()
    if key ~= ucKey then
        local funcName = "Get" .. ucKey
        if GameObject[ funcName ] ~= nil then
            return GameObject[ funcName ]( gameObject )
        end
    end

    return nil
end

-- Dynamic setters
function GameObject.__newindex( gameObject, key, value )
    local ucKey = key:ucfirst()
    if key ~= ucKey and key ~= "transform" then -- first letter lowercase
        -- check about Transform is needed because CraftStudio.CreateGameObject() set the transfom variable on new gameObjects
        local funcName = "Set" .. ucKey
        -- ie: variable "name" call "SetName"
        if GameObject[ funcName ] ~= nil then
            return GameObject[ funcName ]( gameObject, value )
        end
    end
    rawset( gameObject, key, value )
end


----------------------------------------------------------------------------------

--- Create a new gameObject and optionally initialize it.
-- @param name (string) The GameObject name.
-- @param params [optional] (table) A table with parameters to initialize the new gameObject with.
-- @return (GameObject) The new gameObject.
function GameObject.New(name, params)
    Daneel.Debug.StackTrace.BeginFunction("GameObject.New", name, params)
    local errorHead = "GameObject.New(name[, params]) : "
    Daneel.Debug.CheckArgType(name, "name", "string", errorHead)
    Daneel.Debug.CheckOptionalArgType(params, "params", "table", errorHead)
    local gameObject = CraftStudio.CreateGameObject(name)
    if params ~= nil then
        gameObject:Set(params)
    end
    Daneel.Debug.StackTrace.EndFunction()
    return gameObject
end

--- Create a new gameObject with the content of the provided scene and optionally initialize it.
-- @param gameObjectName (string) The gameObject name.
-- @param sceneNameOrAsset (string or Scene) The scene name or scene asset.
-- @param params [optional] (table) A table with parameters to initialize the new gameObject with.
-- @return (GameObject) The new gameObject.
function GameObject.Instantiate(gameObjectName, sceneNameOrAsset, params)
    Daneel.Debug.StackTrace.BeginFunction("GameObject.Instantiate", gameObjectName, sceneNameOrAsset, params)
    local errorHead = "GameObject.Instantiate(gameObjectName, sceneNameOrAsset[, params]) : "
    Daneel.Debug.CheckArgType(gameObjectName, "gameObjectName", "string", errorHead)
    Daneel.Debug.CheckArgType(sceneNameOrAsset, "sceneNameOrAsset", {"string", "Scene"}, errorHead)
    Daneel.Debug.CheckOptionalArgType(params, "params", "table", errorHead)

    local scene = Asset.Get(sceneNameOrAsset, "Scene", true)   
    local gameObject = CraftStudio.Instantiate(gameObjectName, scene)
    if params ~= nil then
        gameObject:Set(params)
    end
    Daneel.Debug.StackTrace.EndFunction("GameObject.Instantiate", gameObject)
    return gameObject
end

--- Returns the first gameObject that was in the provided scene.
-- @param sceneNameOrAsset (string or Scene) The scene name or scene asset.
-- @param params [optional] (table) A table with parameters to initialize the new gameObject with.
-- @return (GameObject) The gameObject that was in the scene.
function GameObject.NewFromScene(sceneNameOrAsset, params)
    Daneel.Debug.StackTrace.BeginFunction("GameObject.NewFromScene",  sceneNameOrAsset, params)
    local errorHead = "GameObject.NewFromScene(sceneNameOrAsset[, params]) : "
    Daneel.Debug.CheckArgType(sceneNameOrAsset, "sceneNameOrAsset", {"string", "Scene"}, errorHead)
    Daneel.Debug.CheckOptionalArgType(params, "params", "table", errorHead)
    
    local scene = Asset.Get(sceneNameOrAsset, "Scene", true)
    local gameObject = CraftStudio.AppendScene(scene)
    if params ~= nil then
        gameObject:Set(params)
    end
    Daneel.Debug.StackTrace.EndFunction()
    return gameObject
end

--- Apply the content of the params argument to the provided gameObject.
-- @param gameObject (GameObject) The game object.
-- @param params (table) A table of parameters to set the gameObject with.
function GameObject.Set( gameObject, params )
    Daneel.Debug.StackTrace.BeginFunction( "GameObject.Set", gameObject, params )
    local errorHead = "GameObject.Set( gameObject, params ) : "
    Daneel.Debug.CheckArgType( params, "params", "table", errorHead )
    local argType = nil
    
    if params.parent ~= nil then
        -- do that first so that setting a local position works
        gameObject:SetParent( params.parent )
        params.parent = nil
    end
    
    -- components
    local component = nil
    local componentTypes = table.copy( Daneel.Config.componentTypes )
    table.removevalue( componentTypes, "ScriptedBehavior" )
    for i, type in ipairs( componentTypes ) do
        componentTypes[i] = type:lcfirst()
    end

    for i, componentType in ipairs( componentTypes ) do
        if params[componentType] ~= nil then
            Daneel.Debug.CheckArgType( params[componentType], "params."..componentType, "table", errorHead )

            component = gameObject[ componentType ]
            if component == nil then
                component = gameObject:GetComponent( componentType )
            end

            if component == nil then
                component = gameObject:AddComponent( componentType, params[componentType] )
            else
                component:Set( params[componentType] )
            end
            params[componentType] = nil
        end
    end

    -- all other keys/values
    for key, value in pairs( params ) do

        -- if key is a script path in Daneel.Config.scriptPath or a script alias
        if Daneel.Config.scriptPaths[key] ~= nil or table.containsvalue( Daneel.Config.scriptPaths, key ) then
            local scriptPath = key
            if Daneel.Config.scriptPaths[key] ~= nil then
                scriptPath = Daneel.Config.scriptPaths[key]
            end
            local component = gameObject:GetScriptedBehavior( scriptPath )
            if component == nil then
                component = gameObject:AddScriptedBehavior( scriptPath, value )
            else
                component:Set(value)
            end

        elseif key == "tags"  then
            gameObject:RemoveTag()
            gameObject:AddTag( value )

        else
            -- check if the key is a script path
            local script = CS.FindAsset( key, "Script" )
            if script ~= nil then
                local behavior = gameObject:GetScriptedBehavior( script )
                if behavior ~= nil then
                    Component.Set( behavior, value )
                end
            else
                gameObject[key] = value
            end
        end
    end
    Daneel.Debug.StackTrace.EndFunction()
end


----------------------------------------------------------------------------------
-- Miscellaneous

--- Alias of CraftStudio.FindGameObject(name).
-- Get the first gameObject with the provided name.
-- @param name (string) The gameObject name.
-- @param errorIfGameObjectNotFound [optional default=false] (boolean) Throw an error if the gameObject was not found (instead of returning nil).
-- @return (GameObject) The gameObject or nil if none is found.
function GameObject.Get( name, errorIfGameObjectNotFound )
    Daneel.Debug.StackTrace.BeginFunction( "GameObject.Get", name, errorIfGameObjectNotFound )
    
    if getmetatable(name) == GameObject then
        Daneel.Debug.StackTrace.EndFunction()
        return name
    end

    local errorHead = "GameObject.Get( name[, errorIfGameObjectNotFound] ) : "
    Daneel.Debug.CheckArgType( name, "name", "string", errorHead )
    Daneel.Debug.CheckOptionalArgType( errorIfGameObjectNotFound, "errorIfGameObjectNotFound", "boolean", errorHead )
    
    -- can't use name:find(".") because for some reason it always returns 1, 1
    -- 31/07/2013 see in Core/Lua string.split() for reason
    local gameObject = nil
    local names = name:split( "." )
    
    gameObject = CraftStudio.FindGameObject( names[1] )
    if gameObject == nil and errorIfGameObjectNotFound == true then
        error( errorHead.."GameObject with name '" .. names[1] .. "' (from '" .. name .. "') was not found." )
    end

    if gameObject ~= nil then
        local originalName = name
        local fullName = table.remove( names, 1 )

        for i, name in ipairs( names ) do
            gameObject = gameObject:GetChild( name )
            fullName = fullName .. "." .. name

            if gameObject == nil then
                if errorIfGameObjectNotFound == true then
                    error( errorHead.."GameObject with name '" .. fullName .. "' (from '" .. originalName .. "') was not found." )
                end

                break
            end
        end
    end

    Daneel.Debug.StackTrace.EndFunction()
    return gameObject
end

--- Returns the game object's internal unique identifier.
-- @param gameObject (GameObject) The game object.
-- @return (number) The id (-1 if something goes wrong)
function GameObject.GetId( gameObject )
    Daneel.Debug.StackTrace.BeginFunction( "GameObject.GetId", gameObject )
    local errorHead = "GameObject.GetId( gameObject ) : "
    Daneel.Debug.CheckArgType( gameObject, "gameObject", "GameObject", errorHead )

    if gameObject.Id ~= nil then
        Daneel.Debug.StackTrace.EndFunction()
        return gameObject.Id
    end

    local id = -1
    if gameObject.inner ~= nil then
        id = tostring( gameObject.inner ):sub( 5, 20 )
        rawset( gameObject, "Id", id )
    end

    Daneel.Debug.StackTrace.EndFunction()
    return id
end

local OriginalSetParent = GameObject.SetParent

--- Set the gameObject's parent. 
-- Optionaly carry over the gameObject's local transform instead of the global one.
-- @param gameObject (GameObject) The game object.
-- @param parentNameOrInstance [optional] (string or GameObject) The parent name or gameObject (or nil to remove the parent).
-- @param keepLocalTransform [optional default=false] (boolean) Carry over the game object's local transform instead of the global one.
function GameObject.SetParent(gameObject, parentNameOrInstance, keepLocalTransform)
    Daneel.Debug.StackTrace.BeginFunction("GameObject.SetParent", gameObject, parentNameOrInstance, keepLocalTransform)
    local errorHead = "GameObject.SetParent(gameObject, [parentNameOrInstance, keepLocalTransform]) : "
    Daneel.Debug.CheckArgType(gameObject, "gameObject", "GameObject", errorHead)
    Daneel.Debug.CheckOptionalArgType(parentNameOrInstance, "parentNameOrInstance", {"string", "GameObject"}, errorHead)
    keepLocalTransform = Daneel.Debug.CheckOptionalArgType(keepLocalTransform, "keepLocalTransform", "boolean", errorHead, false)

    local parent = nil
    if parentNameOrInstance ~= nil then
        parent = GameObject.Get(parentNameOrInstance, true)
    end
    OriginalSetParent(gameObject, parent, keepLocalTransform)
    Daneel.Debug.StackTrace.EndFunction()
end

--- Alias of GameObject:FindChild().
-- Find the first gameObject's child with the provided name.
-- If the name is not provided, it returns the first child.
-- @param gameObject (GameObject) The game object.
-- @param name [optional] (string) The child name (may be hyerarchy of names separated by dots).
-- @param recursive [optional default=false] (boolean) Search for the child in all descendants instead of just the first generation.
-- @return (GameObject) The child or nil if none is found.
function GameObject.GetChild( gameObject, name, recursive )
    Daneel.Debug.StackTrace.BeginFunction( "GameObject.GetChild", gameObject, name, recursive )
    local errorHead = "GameObject.GetChild( gameObject, name[, recursive] ) : "
    Daneel.Debug.CheckArgType( gameObject, "gameObject", "GameObject", errorHead )
    Daneel.Debug.CheckOptionalArgType( name, "name", "string", errorHead )
    recursive = Daneel.Debug.CheckOptionalArgType( recursive, "recursive", "boolean", errorHead, false )
    
    local child = nil
    if name == nil then
        local children = gameObject:GetChildren()
        child = children[1]
    else
        -- can't use name:Find(".") because for some reason it always returns 1, 1
        local names = name:split( "." )
        for i, name in ipairs( names ) do
            gameObject = gameObject:FindChild( name, recursive )

            if gameObject == nil then
                break
            end
        end
        child = gameObject
    end
    Daneel.Debug.StackTrace.EndFunction()
    return child
end

local OriginalGetChildren = GameObject.GetChildren

--- Get all descendants of the gameObject.
-- @param gameObject (GameObject) The game object.
-- @param recursive [optional default=false] (boolean) Look for all descendants instead of just the first generation.
-- @param includeSelf [optional default=false] (boolean) Include the gameObject in the children.
-- @return (table) The children.
function GameObject.GetChildren(gameObject, recursive, includeSelf)
    Daneel.Debug.StackTrace.BeginFunction("GameObject.GetChildren", gameObject, recursive, includeSelf)
    local errorHead = "GameObject.GetChildrenRecursive(gameObject[, recursive, includeSelf]) : "
    Daneel.Debug.CheckArgType(gameObject, "gameObject", "GameObject", errorHead)
    Daneel.Debug.CheckOptionalArgType(recursive, "recursive", "boolean", errorHead)
    Daneel.Debug.CheckOptionalArgType(includeSelf, "includeSelf", "boolean", errorHead)
    
    local allChildren = {}
    if includeSelf == true then
        table.insert( allChildren, gameObject )
    end
    local selfChildren = OriginalGetChildren( gameObject )
    if recursive == true then
        -- get the rest of the children
        for i, child in ipairs( selfChildren ) do
            allChildren = table.merge( allChildren, child:GetChildren( true, true ) )
        end
    else
        allChildren = table.merge( allChildren, selfChildren )
    end
    Daneel.Debug.StackTrace.EndFunction()
    return allChildren
end

local OriginalSendMessage = GameObject.SendMessage

--- Tries to call a method with the provided name on all the scriptedBehaviors attached to the gameObject. 
-- The data argument can be nil or a table you want the method to receive as its first (and only) argument.
-- If none of the scripteBehaviors attached to the gameObject or its children have a method matching the provided name, nothing happens. 
-- @param gameObject (GameObject) The game object.
-- @param functionName (string) The method name.
-- @param data [optional] (table) The data to pass along the method call.
function GameObject.SendMessage(gameObject, functionName, data)
    Daneel.Debug.StackTrace.BeginFunction("GameObject.SendMessage", gameObject, functionName, data)
    local errorHead = "GameObject.SendMessage(gameObject, functionName[, data]) : "
    Daneel.Debug.CheckArgType(gameObject, "gameObject", "GameObject", errorHead)
    Daneel.Debug.CheckArgType(functionName, "functionName", "string", errorHead)
    Daneel.Debug.CheckOptionalArgType(data, "data", "table", errorHead)
    
    OriginalSendMessage(gameObject, functionName, data)
    Daneel.Debug.StackTrace.EndFunction("GameObject.SendMessage")
end

--- Tries to call a method with the provided name on all the scriptedBehaviors attached to the gameObject or any of its descendants. 
-- The data argument can be nil or a table you want the method to receive as its first (and only) argument.
-- If none of the scripteBehaviors attached to the gameObject or its children have a method matching the provided name, nothing happens. 
-- @param gameObject (GameObject) The game object.
-- @param functionName (string) The method name.
-- @param data [optional] (table) The data to pass along the method call.
function GameObject.BroadcastMessage(gameObject, functionName, data)
    Daneel.Debug.StackTrace.BeginFunction("GameObject.BroadcastMessage", gameObject, functionName, data)
    local errorHead = "GameObject.BroadcastMessage(gameObject, functionName[, data]) : "
    Daneel.Debug.CheckArgType(gameObject, "gameObject", "GameObject", errorHead)
    Daneel.Debug.CheckArgType(functionName, "functionName", "string", errorHead)
    Daneel.Debug.CheckOptionalArgType(data, "data", "table", errorHead)
    
    local allGos = gameObject:GetChildren(true, true) -- the gameObject + all of its children
    for i, go in ipairs(allGos) do
        go:SendMessage(functionName, data)
    end
    Daneel.Debug.StackTrace.EndFunction("GameObject.BroadcastMessage")
end


----------------------------------------------------------------------------------
-- Add components

--- Add a component to the gameObject and optionally initialize it.
-- @param gameObject (GameObject) The game object.
-- @param componentType (string) The component type (can't be Transform or ScriptedBehavior).
-- @param params [optional] (string, Script or table) A table of parameters to initialize the new component with or, if componentType is 'ScriptedBehavior', the mandatory script name or asset.
-- @return (One of the component types) The component.
function GameObject.AddComponent( gameObject, componentType, params )
    Daneel.Debug.StackTrace.BeginFunction( "GameObject.AddComponent", gameObject, componentType, params )
    local errorHead = "GameObject.AddComponent( gameObject, componentType[, params] ) : "
    Daneel.Debug.CheckArgType( gameObject, "gameObject", "GameObject", errorHead )
    Daneel.Debug.CheckArgType( componentType, "componentType", "string", errorHead ) 
    componentType = Daneel.Debug.CheckArgValue( componentType, "componentType", Daneel.Config.componentTypes, errorHead )
    Daneel.Debug.CheckOptionalArgType( params, "params", "table", errorHead )

    if componentType == "Transform" and DEBUG == true then
        print( errorHead.."Can't add a transform component because gameObjects may only have one transform." )
        Daneel.Debug.StackTrace.EndFunction()
        return
    end
    if componentType == "ScriptedBehavior" and DEBUG == true then
        print( errorHead.."Can't add a ScriptedBehavior via 'GameObject.AddComponent()'. Use 'GameObject.AddScriptedBehavior()' instead." )
        Daneel.Debug.StackTrace.EndFunction()
        return
    end

    local component = nil

    if table.containsvalue( Daneel.Config.daneelComponentTypes, componentType ) then
        component = Daneel.GUI[ componentType ].New( gameObject )
    else
        component = gameObject:CreateComponent( componentType )

        local defaultComponentParams = Daneel.Config.components[ componentType:lcfirst() ]
        if defaultComponentParams ~= nil then
            params = table.merge( defaultComponentParams, params )
        end
    end

    if params ~= nil then
        component:Set( params )
    end

    Daneel.Event.Fire( gameObject, "OnNewComponent", component )
    Daneel.Debug.StackTrace.EndFunction()
    return component
end

--- Add a ScriptedBehavior to the gameObject and optionally initialize it.
-- @param gameObject (GameObject) The game object.
-- @param scriptNameOrAsset (string or Script) The script name or asset.
-- @param params [optional] (table) A table of parameters to initialize the new component with.
-- @return (ScriptedBehavior) The component.
function GameObject.AddScriptedBehavior( gameObject, scriptNameOrAsset, params ) 
    Daneel.Debug.StackTrace.BeginFunction( "GameObject.AddScriptedBehavior", gameObject, scriptNameOrAsset, params )
    local errorHead = "GameObject.AddScriptedBehavior( gameObject, scriptNameOrAsset[, params] ) : "
    Daneel.Debug.CheckArgType( gameObject, "gameObject", "GameObject", errorHead )
    Daneel.Debug.CheckArgType( scriptNameOrAsset, "scriptNameOrAsset", {"string", "Script"}, errorHead )
    Daneel.Debug.CheckOptionalArgType( params, "params", "table", errorHead )

    local script = Asset.Get( scriptNameOrAsset, "Script", true )
    local component = gameObject:CreateScriptedBehavior( script )
    
    if params ~= nil then
        component:Set( params )
    end

    Daneel.Event.Fire( gameObject, "OnNewComponent", component )
    Daneel.Debug.StackTrace.EndFunction()
    return component
end


----------------------------------------------------------------------------------
-- Get components

local OriginalGetComponent = GameObject.GetComponent

--- Get the first component of the provided type attached to the gameObject.
-- @param gameObject (GameObject) The game object.
-- @param componentType (string) The component type.
-- @return (One of the component types) The component instance, or nil if none is found.
function GameObject.GetComponent( gameObject, componentType )
    Daneel.Debug.StackTrace.BeginFunction( "GameObject.GetComponent", gameObject, componentType )
    local errorHead = "GameObject.GetComponent( gameObject, componentType ) : "
    Daneel.Debug.CheckArgType( gameObject, "gameObject", "GameObject", errorHead )
    Daneel.Debug.CheckArgType( componentType, "componentType", "string", errorHead )
    componentType = Daneel.Debug.CheckArgValue( componentType, "componentType", Daneel.Config.componentTypes, errorHead )
    
    if componentType == "ScriptedBehavior" then
        print( errorHead.."Can't get a ScriptedBehavior via 'GameObject.GetComponent()'. Use 'GameObject.GetScriptedBehavior()' instead." )
        Daneel.Debug.StackTrace.EndFunction()
        return nil
    end

    local lcComponentType = componentType:lcfirst()
    local component = gameObject[ lcComponentType ]
    
    if component == nil and not table.containsvalue( Daneel.Config.daneelComponentTypes, componentType ) then
        component = OriginalGetComponent( gameObject, componentType )

        if component ~= nil then
            gameObject[ lcComponentType ] = component
        end
    end

    Daneel.Debug.StackTrace.EndFunction()
    return component
end

local OriginalGetScriptedBehavior = GameObject.GetScriptedBehavior

--- Get the provided scripted behavior instance attached to the gameObject.
-- @param gameObject (GameObject) The game object.
-- @param scriptNameOrAsset (string or Script) The script name or asset.
-- @return (ScriptedBehavior) The ScriptedBehavior instance.
function GameObject.GetScriptedBehavior( gameObject, scriptNameOrAsset )
    Daneel.Debug.StackTrace.BeginFunction( "GameObject.GetScriptedBehavior", gameObject, scriptNameOrAsset )
    local errorHead = "GameObject.GetScriptedBehavior( gameObject, scriptNameOrAsset ) : "
    Daneel.Debug.CheckArgType( gameObject, "gameObject", "GameObject", errorHead )
    Daneel.Debug.CheckArgType( scriptNameOrAsset, "scriptNameOrAsset", {"string", "Script"}, errorHead )

    local script = scriptNameOrAsset
    if type( scriptNameOrAsset ) == "string" then
        script = Asset.Get( scriptNameOrAsset, "Script", true )
    end
    local component = OriginalGetScriptedBehavior( gameObject, script )
    Daneel.Debug.StackTrace.EndFunction()
    return component
end


----------------------------------------------------------------------------------
-- Destroy gameObject

--- Destroy the gameObject at the end of this frame.
-- @param gameObject (GameObject) The game object.
function GameObject.Destroy(gameObject)
    Daneel.Debug.StackTrace.BeginFunction("GameObject.Destroy", gameObject)
    local errorHead = "GameObject.Destroy(gameObject) : "
    Daneel.Debug.CheckArgType(gameObject, "gameObject", "GameObject", errorHead)

    CraftStudio.Destroy(gameObject)
    Daneel.Debug.StackTrace.EndFunction()
end


----------------------------------------------------------------------------------
-- Tags

GameObject.Tags = {}

--- Returns the game object(s) that have all the provided tag(s).
-- @param tag (string or table) One or several tags.
-- @return (table) The game object(s) (empty if none is found)
function GameObject.GetWithTag( tag )
    Daneel.Debug.StackTrace.BeginFunction( "GameObject.GetWithTag", tag )
    local errorHead = "GameObject.GetWithTag( tag ) : "
    local argType = Daneel.Debug.CheckArgType( tag, "tag", {"string", "table"}, errorHead )

    local tags = tag
    if argType == "string" then
        tags = { tags }
    end

    local gameObjectsWithTag = {}

    for i, tag in ipairs( tags ) do
        local gameObjects = GameObject.Tags[ tag ]
        if gameObjects ~= nil then
            for i, gameObject in ipairs( gameObjects ) do
                if gameObject:HasTag( tags ) and not table.containsvalue( gameObjectsWithTag, gameObject ) then
                    table.insert( gameObjectsWithTag, gameObject )
                end
            end
        end
    end

    Daneel.Debug.StackTrace.EndFunction()
    return gameObjectsWithTag
end

--- Add the provided tag(s) to the provided gameObject.
-- @param gameObject (GameObject) The game object.
-- @param tag (string or table) One or several tag(s) (as a string or table of strings).
function GameObject.AddTag(gameObject, tag)
    Daneel.Debug.StackTrace.BeginFunction("GameObject.AddTag", gameObject, tag)
    local errorHead = "GameObject.AddTag(gameObject, tag) : "
    Daneel.Debug.CheckArgType(gameObject, "gameObject", "GameObject", errorHead)
    Daneel.Debug.CheckArgType(tag, "tag", {"string", "table"}, errorHead)
    
    local tags = tag
    if type(tags) == "string" then
        tags = { tags }
    end
    if gameObject.tags == nil then
        gameObject.tags = {}
    end
    for i, tag in ipairs(tags) do
        if not table.containsvalue(gameObject.tags, tag) then
            table.insert(gameObject.tags, tag)
        end
        if GameObject.Tags[tag] == nil then
            GameObject.Tags[tag] = { gameObject }
        else
            table.insert(GameObject.Tags[tag], gameObject)
        end
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Remove the provided tag(s) from the provided gameObject.
-- If the 'tag' argument is not provided, all tag of the gameObject will be removed.
-- @param gameObject (GameObject) The game object.
-- @param tag [optional] (string or table) One or several tag(s) (as a string or table of strings).
function GameObject.RemoveTag(gameObject, tag)
    if gameObject.tags == nil then return end
    
    Daneel.Debug.StackTrace.BeginFunction("GameObject.RemoveTag", gameObject, tag)
    local errorHead = "GameObject.RemoveTag(gameObject[, tag]) : "
    Daneel.Debug.CheckArgType(gameObject, "gameObject", "GameObject", errorHead)
    tag = Daneel.Debug.CheckOptionalArgType(tag, "tag", {"string", "table"}, errorHead, gameObject.tags)
    
    local tags = tag
    if type(tags) == "string" then
        tags = { tags }
    end
    for i, tag in ipairs(tags) do
        table.removevalue(gameObject.tags, tag)
        if GameObject.Tags[tag] ~= nil then
            table.removevalue(GameObject.Tags[tag], gameObject)
        end
    end
    Daneel.Debug.StackTrace.EndFunction()
end

--- Tell wether the provided gameObject has all (or at least one of) the provided tag.
-- @param gameObject (GameObject) The game object.
-- @param tag (string or table) One or several tag (as a string or table of strings).
-- @param atLeastOneTag [default=false] (boolean) If true, returns true if the gameObject has AT LEAST one of the tag (instead of ALL the tag).
-- @return (boolean) True
function GameObject.HasTag(gameObject, tag, atLeastOneTag)
    if gameObject.tags == nil then return false end
    
    Daneel.Debug.StackTrace.BeginFunction("GameObject.HasTag", gameObject, tag, atLeastOneTag)
    local errorHead = "GameObject.HasTag(gameObject, tag) : "
    Daneel.Debug.CheckArgType(gameObject, "gameObject", "GameObject", errorHead)
    Daneel.Debug.CheckArgType(tag, "tag", {"string", "table"}, errorHead, {})
    Daneel.Debug.CheckOptionalArgType(atLeastOneTag, "atLeastOneTag", "boolean", errorHead)

    local tags = tag
    if type(tags) == "string" then
        tags = { tags }
    end
    local hasTags = false
    if atLeastOneTag == true then
        for i, tag in ipairs(tags) do
            if table.containsvalue(gameObject.tags, tag) then
                hasTags = true
                break
            end
        end
    else
        hasTags = true
        for i, tag in ipairs(tags) do
            if not table.containsvalue(gameObject.tags, tag) then
                hasTags = false
                break
            end
        end
    end

    Daneel.Debug.StackTrace.EndFunction()
    return hasTags
end
