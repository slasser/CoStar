-- TextArea.lua
-- Scripted behavior for Daneel.GUI.TextArea component.
--
-- Last modified for v1.2.0
-- Copyright © 2013 Florent POUJOL, published under the MIT licence.

--[[PublicProperties
areaWidth string ""
wordWrap boolean false
newLine string "\n"
lineHeight string "1"
verticalAlignment string "top"
font string ""
text string "Text\nArea"
alignment string ""
opacity number 1.0
/PublicProperties]]

-- creating a TextArea from Awake cause an exception (collecion being modified while looping on it)
function Behavior:Start()
    if self.gameObject.textArea == nil then
        local params = {
            wordWrap = self.wordWrap,
            opacity = self.opacity
        }
        local props = {"areaWidth", "newLine", "lineHeight", "verticalAlignment", "font", "text", "alignment"}
        for i, prop in ipairs( props ) do
            if self[ prop ]:trim() ~= "" then
                params[ prop ] = self[ prop ]
            end
        end

        self.gameObject:AddComponent( "TextArea", params )
    end
end
