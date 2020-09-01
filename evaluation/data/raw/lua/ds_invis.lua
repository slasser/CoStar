function rdrInvis( ply, bool, visibility )
	if not ( ply and IsValid(ply) ) then return end -- This is called on a timer so we need to verify they're still connected

	if bool then
		visibility = visibility or 0
		ply:DrawShadow( false )
		ply:SetMaterial( "models/effects/vol_light001" )
		ply:SetRenderMode( RENDERMODE_TRANSALPHA )
		ply:Fire( "alpha", visibility, 0 )
		ply:GetTable().invis = { vis=visibility, wep=ply:GetActiveWeapon() }

		if ply:GetActiveWeapon():IsValid() then
			ply:GetActiveWeapon():SetRenderMode( RENDERMODE_TRANSALPHA )
			ply:GetActiveWeapon():Fire( "alpha", visibility, 0 )
			ply:GetActiveWeapon():SetMaterial( "models/effects/vol_light001" )
			if ply:GetActiveWeapon():GetClass() == "gmod_tool" then
				ply:DrawWorldModel( false ) -- tool gun has problems
			else
				ply:DrawWorldModel( true )
			end
		end

		hook.Add( "Think", "InvisThink", doInvis )
	else
		ply:DrawShadow( true )
		ply:SetMaterial( "" )
		ply:SetRenderMode( RENDERMODE_NORMAL )
		ply:Fire( "alpha", 255, 0 )
		
		if ply:GetActiveWeapon():IsValid() then
			ply:GetActiveWeapon():SetRenderMode( RENDERMODE_NORMAL )
			ply:GetActiveWeapon():Fire( "alpha", 255, 0 )
			ply:GetActiveWeapon():SetMaterial( "" )
			
			if ply:GetActiveWeapon():GetClass() == "gmod_tool" then
				ply:DrawWorldModel( true )
			end
		end
		
		ply:GetTable().invis = nil
	end
end