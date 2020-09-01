-- Hud.lua
-- Scripted behavior for Daneel.GUI.Hud component.
--
-- Last modified for v1.2.0
-- Copyright © 2013 Florent POUJOL, published under the MIT licence.

--[[PublicProperties
positionX string ""
positionY string ""
localPositionX string ""
localPositionY string ""
layer string ""
localLayer string ""
/PublicProperties]]

function Behavior:Awake()
    if self.gameObject.hud == nil then
        local params = {}
        if self.positionX ~= "" and self.positionY ~= "" then
            params.position = Vector2.New(tonumber(self.positionX), tonumber(self.positionY))
        end
        if self.localPositionX ~= "" and self.localPositionY ~= "" then
            params.localPosition = Vector2.New(tonumber(self.localPositionX), tonumber(self.localPositionY))
        end
        if self.layer ~= "" then
            params.layer = tonumber(self.layer)
        end
        if self.localLayer ~= "" then
            params.localLayer = tonumber(self.localLayer)
        end

        -- allow the gameObject to stay at the same position than defined in the scene
        local position, layer = Daneel.GUI.Hud.ToHudPosition(self.gameObject.transform.position)
        if params.position == nil and params.localPosition == nil then
            params.position = position
        end
        if params.layer == nil and params.localLayer == nil then
            params.layer = layer
        end

        self.gameObject:AddComponent("Hud", params)
    end
end
