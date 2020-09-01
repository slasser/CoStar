-- Trigger.lua
-- Scripted behavior for triggers.
--
-- Last modified for v1.2.0
-- Copyright © 2013 Florent POUJOL, published under the MIT licence.

--[[PublicProperties
range number 0
tags string ""
checkInterval number 10
/PublicProperties]]

function Behavior:Awake()
    self.GameObjectsInRange = {} -- the gameObjects that touches this trigger

    if self.tags:trim() == "" then
        self.tags = {}
    else
        self.tags = self.tags:split( ",", true )
    end

    self.frameCount = 0
end


function Behavior:Update()
    self.frameCount = self.frameCount + 1

    if 
        self.range <= 0 or self.checkInterval < 1 or #self.tags == 0 or
        ( self.checkInterval > 1 and self.frameCount % self.checkInterval ~= 0 )
    then
        return
    end

    local triggerPosition = self.gameObject.transform:GetPosition()
    
    for i, layer in ipairs(self.tags) do
        local gameObjects = GameObject.Tags[layer]
        if gameObjects ~= nil then
            
            for i = #gameObjects, i, -1 do
                local gameObject = gameObjects[i]
                if gameObject ~= nil and gameObject.isDestroyed ~= true then

                    if 
                        gameObject ~= self.gameObject and 
                        Vector3.Distance( gameObject.transform:GetPosition(), triggerPosition ) < self.range 
                    then
                        if not table.containsvalue( self.GameObjectsInRange, gameObject ) then
                            -- just entered the trigger
                            table.insert( self.GameObjectsInRange, gameObject )
                            Daneel.Event.Fire( gameObject, "OnTriggerEnter", self.gameObject )
                            Daneel.Event.Fire( self.gameObject, "OnTriggerEnter", gameObject )
                        else
                            -- already in this trigger
                            Daneel.Event.Fire( gameObject, "OnTriggerStay", self.gameObject )
                            Daneel.Event.Fire( self.gameObject, "OnTriggerStay", gameObject )
                        end
                    else
                        -- was the gameObject still in this trigger the last frame ?
                        if table.containsvalue( self.GameObjectsInRange, gameObject ) then
                            table.removevalue( self.GameObjectsInRange, gameObject )
                            Daneel.Event.Fire( gameObject, "OnTriggerExit", self.gameObject )
                            Daneel.Event.Fire( self.gameObject, "OnTriggerExit", gameObject )
                        end
                    end

                else
                    table.remove( gameObjects )
                end
            end

        end
    end
end

--- Get the gameObjets that are closer than the trigger's range.
-- @param tags [optional] (string or table) The tags(s) the gameObjects must have. If nil, it uses the trigger's tags(s).
-- @param range [optional] (number) The range within which to pick the gameObjects. If nil, it uses the trigger's range.
-- @return (table) The list of the gameObjects in range (empty if none in range).
function Behavior:GetGameObjectsInRange( tags, range )
    if type( tags ) == "number" then
        range = tags
        tags = nil
    end

    local errorHead = "Trigger:GetGameObjectsInRange( [tags, range] ) : "
    Daneel.Debug.CheckOptionalArgType( tags, "tags", {"string", "table"}, errorHead )

    if tags == nil then
        tags = self.tags
    end
    if type( tags ) == "string" then
        tags = { tags }
    end

    range = Daneel.Debug.CheckOptionalArgType( range, "range", "number", errorHead, self.range )
    
    local gameObjectsInRange = {}
    local triggerPosition = self.gameObject.transform:GetPosition()
    
    for i, layer in ipairs( tags ) do
        local gameObjects = GameObject.Tags[ layer ]
        if gameObjects ~= nil then

            for i, gameObject in ipairs( gameObjects ) do
                if 
                    gameObject ~= nil and gameObject.isDestroyed ~= true and
                    gameObject ~= self.gameObject and 
                    Vector3.Distance( gameObject.transform:GetPosition(), triggerPosition ) <= self.range
                then
                    table.insert( gameObjectsInRange, gameObject )
                end
            end

        end
    end

    return gameObjectsInRange
end
