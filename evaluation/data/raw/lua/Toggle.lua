-- Toggle.lua
-- Scripted behavior for Daneel.GUI.Toggle component.
--
-- Last modified for v1.2.0
-- Copyright © 2013 Florent POUJOL, published under the MIT licence.

--[[PublicProperties
isChecked boolean false
text string ""
group string ""
checkedMark string ""
uncheckedMark string ""
checkedModel string ""
uncheckedModel string ""
/PublicProperties]]

function Behavior:Awake()
    if self.gameObject.toggle == nil then
        local params = {
            isChecked = self.isChecked,
        }
        local props = {"text", "group", "checkedMark", "uncheckedMark", "checkedModel", "uncheckedModel"}
        for i, prop in ipairs( props ) do
            if self[ prop ]:trim() ~= "" then
                params[ prop ] = self[ prop ]
            end
        end
        
        self.gameObject:AddComponent( "Toggle", params )
    end
end

-- when the gameObject is clicked by the mouse
function Behavior:OnClick()
    local toggle = self.gameObject.toggle
    if not (toggle.group ~= nil and toggle.isChecked) then -- true when not in a group or when in group but not checked
        toggle:Check( not toggle.isChecked )
    end
end


-- "wait" for the TextRenderer or ModelRenderer to be added
function Behavior:OnNewComponent( data )
    local component = data[1]
    if component == nil then return end
    local mt = getmetatable(component)
    local toggle = self.gameObject.toggle

    if mt == TextRenderer then
        local text = component:GetText()
        if text == nil then
            text = toggle.defaultText
        end
        toggle:SetText( text )

    elseif mt == ModelRenderer and toggle.checkedModel ~= nil then
        if toggle.isChecked and toggle.checkedModel ~= nil then
            self.gameObject.modelRenderer:SetModel( toggle.checkedModel )
        elseif not toggle.isChecked and toggle.uncheckedModel ~= nil then
            self.gameObject.modelRenderer:SetModel( toggle.uncheckedModel )
        end
    end
end
