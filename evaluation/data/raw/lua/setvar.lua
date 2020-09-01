module(..., package.seeall)
local url = require("socket.url")

local variables = { }

function run(wsapi_env)
	local headers = {["Content-type"] = "text/plain", ["Access-Control-Allow-Origin"]="*"}
	local function setvar()
		print("page accessed")
		--Parse arguments
		local args = { }
		local requests = wsapi_env.PATH_INFO:sub(2)
		
		for param in requests:gmatch("([^%s/]+)") do
			table.insert(args, param)
		end
		
		local method = args[1]
		table.remove(args, 1)
		
		if method == "put" then
			if pcall(function() variables[args[1]] = args[2] end) then
				coroutine.yield("1")
			else
				coroutine.yield("0")
			end
		elseif method == "get" then
			coroutine.yield(url.unescape(variables[args[1]]))
		end
	end
	
	return 200, headers, coroutine.wrap(setvar)
end