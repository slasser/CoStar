--[[
Copyright (C) <2012> <HeLLFox15>

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
]]

-- Made by HeLLFox15 @ http://steamcommunity.com/profiles/76561198000875949 --

-- Feel free to edit the code below as you like but make sure to give me credit for the original code. --
-- Special thanks to, the creator of the TTT player crush code, CapsAdmin for his super jump idea...  --
-- and Megiddo for making the ULX forums and helping me when I needed help. --

function notify( ply, msg, cvar )
    ply:SendLua("GAMEMODE:AddNotify(\"" .. msg .. "\", " .. tostring(cvar) .. ", 5)")
end

function actMoney(ply)
	local getMoney = 0
	getMoney = ply:GetPData( "money" ) or 1000
	ply:SetPData( "money", getMoney )
end

function initspawn( ply )
	actMoney(ply)
end
hook.Add( "PlayerInitialSpawn", "spawn", spawn )

function rCanAfford(ply, cost)
	if(ply and IsValid(ply)) then
		if( ( ply:GetPData( "money" ) - cost ) >= 1 ) then
			return true
		else
			return false
		end
	else
		return false
	end
end

function DScapeVars(ply)
	if( ply:IsPlayer() ) then
		return ply:GetPData( "money", 0 ) or 0
	else
		return 0
	end
end

--Restrict Some Stuff--

function NoWeapons(ply, class, model)
	if not ( ply:IsAdmin()) then
		notify( ply, "You May Not Spawn That!", "NOTIFY_ERROR" )
		return false
	end
end
hook.Add("PlayerSpawnSWEP", "NoWeaponsA", NoWeapons)
hook.Add("PlayerGiveSWEP", "NoWeaponsB", NoWeapons)
hook.Add("PlayerSpawnEffect", "NoWeaponsC", NoWeapons)
hook.Add("PlayerSpawnVehicle", "NoWeaponsD", NoWeapons)
hook.Add("PlayerSpawnNPC", "NoWeaponsE", NoWeapons)

--Okay lets continue...--

--Players get 35 SMG ammo every 120 seconds.--
timer.Create( "SmgAmmo", 120, 0, function()
    for _,v in pairs(player.GetAll()) do
        v:SetAmmo( 35, "smg1" )
    end
end)

--Pistol ammo is made infinate, and the camera is striped from the player.--
function infpistol()
    for _,v in pairs(player.GetAll()) do
        v:SetAmmo( 255, "Pistol" )
        if( SERVER ) then v:StripWeapon("gmod_camera") end
    end
end
hook.Add( "Think", "infpistol", infpistol )


-- Stuff for falls. (I have enabled fall damage, how ever I only made it do half damage.) --
-- Also last time I checked only players really take FallDamage so using IsPlayer should not break any thing. --
function nofall( target, dmginfo )
    if ( target:IsPlayer() and dmginfo:IsFallDamage() ) then
		if GetConVarNumber("mp_falldamage") == 1 then
			dmginfo:ScaleDamage( 0.5 )
		else
			dmginfo:ScaleDamage( 0 )
		end
	end
end
hook.Add( "EntityTakeDamage", "nofall", nofall )

-- Special thanks to http://steamcommunity.com/groups/metastruct for giving me the idea. :) --
function supajump(ply, key)
    if( IsValid(ply) and key == IN_JUMP and ply:GetEyeTrace().HitNormal[3] > 0 and ply:GetEyeTrace().Fraction < 0.002 ) then
       ply:SetJumpPower( 400 )
    else
       ply:SetJumpPower( 200 )
    end
end
hook.Add( "KeyPress", "supajump", supajump )

if( SERVER ) then
	-- function TempScoreDisplay()
		-- for _,v in pairs(player.GetAll()) do
			-- if( v and IsValid(v) ) then
				-- if( DScapeVars(v) and tonumber(DScapeVars(v)) > 0 ) then 
					-- if not ( DScapeVars(v) ) then return end
					-- v:SetFrags(tonumber(DScapeVars(v)))
				-- end
			-- end
		-- end
	-- end
	-- hook.Add("Think", "TempScoreDisplay", TempScoreDisplay )	
	
    -- What the hell is TTT doing here? (GoombaStomp) --
    function PlyHitGround(ply, in_water, on_floater, speed)
       if in_water or speed < 250 or not IsValid(ply) then return end

       -- if we fell on a dude, that hurts (him)
       local ground = ply:GetGroundEntity()
       if IsValid(ground) and ground:IsPlayer() then
         local dmg = DamageInfo()
         -- hijack physgun damage as a marker of this type of kill
         dmg:SetDamageType(DMG_PHYSGUN) -- I hope this will fix the glitches I have been having.
         dmg:SetAttacker(ply)
         dmg:SetInflictor(ply)
         dmg:SetDamageForce(Vector(0,0,-1))
         dmg:SetDamage(ground:Health())

         ground:TakeDamageInfo(dmg)
       end
    end
    hook.Add( "OnPlayerHitGround", "PlyHitGround", PlyHitGround)
	
	-- Have you ever wanted Garrysmod to have a good health restore system? Well now it does. --
	function hprestore()
		for _,v in pairs(player.GetAll()) do
			if(v:Health() < 100) then
				local ident = tostring(v:UserID())
				if( v and IsValid(v) and ident ) then
					if not ( timer.Exists(ident .. "_restorehp_init") ) then
						timer.Create(ident .. "_restorehp_init", 10, 1, function()
							if not ( timer.Exists(ident .. "_restorehp_run") ) then
								timer.Create(ident .. "_restorehp_run", 0.1, 0, function() 
									if( v and IsValid(v) and v:Alive() ) then
										if(v:Health() < 100) then
											v:SetHealth(v:Health() + 1)
										end
										if( (v:Health() >= 100) ) then
											if( ident ) then timer.Destroy(ident .. "_restorehp_run") end
										end
									else
										if( ident ) then timer.Destroy(ident .. "_restorehp_run") end
									end
								end)
							end
						end)
					end
				end
			end
		end
	end
	hook.Add( "Think", "hprestore", hprestore )
	
	-- This will stop you from getting a false and broken godmode. (From the HP regen above.) --
	function hprestorestop(ply, dmginfo)
		if(ply and IsValid(ply) and ply:IsPlayer()) then
			local dplyid = tostring(ply:UserID())
			if( dplyid and timer.Exists(dplyid .. "_restorehp_init") ) then
				timer.Destroy(dplyid .. "_restorehp_init")
			end
			if( dplyid and timer.Exists(dplyid .. "_restorehp_run") ) then
				timer.Destroy(dplyid .. "_restorehp_run")
			end
		end
	end
	hook.Add( "EntityTakeDamage", "hprestorestop", hprestorestop )
end

-- Now lets get the points working... --
function killpay( v, w, k )
	
	if not (DScapeVars(k) or DScapeVars(v)) then return end --If for some reason they dont exsist...
	
    local km = tonumber(DScapeVars(k))
    local vm = tonumber(DScapeVars(v))
    
	if not (km or vm) then return end --If some how they got removed...
	
    if(vm > km) then
        k:ChatPrint("You got " .. math.Round(10 + ((vm - km)/4)) .. " coin for a kill!")
        k:SetPData( "money", ( km + math.Round( 10 + ( (vm - km)/4 ) ) ) )
    else
        k:SetPData( "money", (km + (10)) )
        k:ChatPrint("You got 10 coin for a kill!")
    end
    
    if(rCanAfford(v, 10)) then
        if(vm >= 2000) then
            v:ChatPrint("You lost " .. (10 * math.Round(vm/1000)) .. " coin for dying.")
            v:SetPData( "money", (vm - (10 * math.Round(vm/1000))) )
        else
            v:SetPData( "money", (vm - (10)) )
            v:ChatPrint("You lost 10 coin for dying.")
        end
    else
        v:ChatPrint("You are dead not big surprise.")
    end
end
hook.Add( "PlayerDeath", "killpay", killpay )

-- This is for props.

function propPay( ply )
    local plym = tonumber(DScapeVars(ply))
    if(rCanAfford(ply, 10)) then
        ply:SetPData( "money", (plym - (10)) )
        notify( ply, "You have bought a prop for 10 coins.", "NOTIFY_GENERIC" )
    else
        notify( ply, "You can't afford that, go get some kills.", "NOTIFY_ERROR" )
        return false
    end
end
hook.Add( "PlayerSpawnProp", "propPay", propPay )

function explode( ent )
    local pos = ent:GetPos()
    ent:Remove()
    local effectdata = EffectData()
    effectdata:SetStart( pos ) -- Not sure if we need a start and origin (endpoint) for this effect, but whatever.
    effectdata:SetOrigin( pos )
    effectdata:SetScale( 2 )
    util.Effect( "Explosion", effectdata )
end


-- I have been playing around with the stuff below but have never been able to get every thing completly realistic, so if you figure it out please send me the code. :) --
CreateConVar( "_ent_health_offset", 0, FCVAR_SERVER_CAN_EXECUTE, "Set the entity HP offset." )

function SetPropHealthOffset( v, _, args )
	if( v and IsValid(v) and ( v:IsSuperAdmin() ) ) then
		RunConsoleCommand("_ent_health_offset", args[1])
	end
end
concommand.Add( "ent_health_offset", SetPropHealthOffset )

/* -- Needs Better Prop Breaking
function PropBreak( e, dmginfo )
    local dmg = dmginfo:GetDamage();
    if( IsValid(e) and not ( e:IsPlayer() or e:IsNPC() or e:IsWorld() ) ) then
		hpa = 10 + GetConVarNumber("_ent_health_offset")
        if( e:Health() == 0 or (not e:Health()) ) then
            if(e:GetPhysicsObject():GetMass() > 100) then
                if((50 + (e:GetPhysicsObject():GetMass()/10)) >= 2000) then
                    e:SetHealth((900 + hpa) + math.random( 666 ))
                else
                    e:SetHealth((hpa/2) + (e:GetPhysicsObject():GetMass()/10))
                end
            else
                e:SetHealth(hpa + (e:GetPhysicsObject():GetMass()))
            end
        end
        
        if( ( e:Health() - dmg ) > 0 ) then
            e:SetHealth(e:Health() - dmg)
        else
            explode(e)
        end
    end
end
hook.Add( "EntityTakeDamage", "PropBreak", PropBreak )
*/
