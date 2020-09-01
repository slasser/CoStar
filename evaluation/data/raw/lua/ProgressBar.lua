-- ProgressBar.lua
-- Scripted behavior for Daneel.GUI.PogressBar component.
--
-- Last modified for v1.2.0
-- Copyright © 2013 Florent POUJOL, published under the MIT licence.

--[[PublicProperties
minValue number 0
maxValue number 100
minLength string "0"
maxLength string "5"
height string "1"
progress string "100%"
/PublicProperties]]

function Behavior:Awake()
    if self.gameObject.progressBar == nil then
        self.gameObject:AddComponent("ProgressBar", { 
            minValue = self.minValue,
            maxValue = self.maxValue,
            minLength = self.minLength,
            maxLength = self.maxLength,
            height = self.height,
            progress = self.progress,
        })
    end
end