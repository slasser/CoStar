-- Slider.lua
-- Scripted behavior for Daneel.GUI.Slider component.
--
-- Last modified for v1.2.0
-- Copyright © 2013 Florent POUJOL, published under the MIT licence.

--[[PublicProperties
minValue number 0
maxValue number 100
length string "5"
axis string "x"
value string "0%"
/PublicProperties]]

function Behavior:Awake()
    if self.gameObject.slider == nil then
        self.gameObject:AddComponent( "Slider", { 
            minValue = self.minValue,
            maxValue = self.maxValue,
            length = self.length,
            axis = self.axis,
            value = self.value,
        } )
    end
end

-- when the handle is dragged
function Behavior:OnDrag()
    local slider = self.gameObject.slider

    local mouseDelta = CraftStudio.Input.GetMouseDelta()
    local positionDelta = Vector3( mouseDelta.x, 0, 0 )
    if slider.axis == "y" then
        positionDelta = Vector3( 0, -mouseDelta.y, 0, 0 )
    end  
    
    self.gameObject.transform:Move( positionDelta * Daneel.GUI.pixelsToUnits )
    
    if 
        (slider.axis == "x" and self.gameObject.transform.position.x < slider.startPosition.x) or
        (slider.axis == "y" and self.gameObject.transform.position.y < slider.startPosition.y)
    then
        slider.value = slider.minValue
    elseif slider.value > slider.maxValue then
        slider.value = slider.maxValue
    else
        Daneel.Event.Fire( slider, "OnUpdate", slider )
    end
end
