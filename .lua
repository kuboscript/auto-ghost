do
	local StrToNumber = tonumber;
	local Byte = string.byte;
	local Char = string.char;
	local Sub = string.sub;
	local Subg = string.gsub;
	local Rep = string.rep;
	local Concat = table.concat;
	local Insert = table.insert;
	local LDExp = math.ldexp;
	local GetFEnv = getfenv or function()
		return _ENV;
	end;
	local Setmetatable = setmetatable;
	local PCall = pcall;
	local Select = select;
	local Unpack = unpack or table.unpack;
	local ToNumber = tonumber;
	local function VMCall(ByteString, vmenv, ...)
		local DIP = 1;
		local repeatNext;
		ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
			if (Byte(byte, 2) == 79) then
				repeatNext = StrToNumber(Sub(byte, 1, 1));
				return "";
			else
				local a = Char(StrToNumber(byte, 16));
				if repeatNext then
					local b = Rep(a, repeatNext);
					repeatNext = nil;
					return b;
				else
					return a;
				end
			end
		end);
		local function gBit(Bit, Start, End)
			if End then
				local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
				return Res - (Res % 1);
			else
				local Plc = 2 ^ (Start - 1);
				return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
			end
		end
		local function gBits8()
			local a = Byte(ByteString, DIP, DIP);
			DIP = DIP + 1;
			return a;
		end
		local function gBits16()
			local a, b = Byte(ByteString, DIP, DIP + 2);
			DIP = DIP + 2;
			return (b * 256) + a;
		end
		local function gBits32()
			local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
			DIP = DIP + 4;
			return (d * 16777216) + (c * 65536) + (b * 256) + a;
		end
		local function gFloat()
			local Left = gBits32();
			local Right = gBits32();
			local IsNormal = 1;
			local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
			local Exponent = gBit(Right, 21, 31);
			local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
			if (Exponent == 0) then
				if (Mantissa == 0) then
					return Sign * 0;
				else
					Exponent = 1;
					IsNormal = 0;
				end
			elseif (Exponent == 2047) then
				return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
			end
			return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
		end
		local function gString(Len)
			local Str;
			if not Len then
				Len = gBits32();
				if (Len == 0) then
					return "";
				end
			end
			Str = Sub(ByteString, DIP, (DIP + Len) - 1);
			DIP = DIP + Len;
			local FStr = {};
			for Idx = 1, #Str do
				FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
			end
			return Concat(FStr);
		end
		local gInt = gBits32;
		local function _R(...)
			return {...}, Select("#", ...);
		end
		local function Deserialize()
			local Instrs = {};
			local Functions = {};
			local Lines = {};
			local Chunk = {Instrs,Functions,nil,Lines};
			local ConstCount = gBits32();
			local Consts = {};
			for Idx = 1, ConstCount do
				local Type = gBits8();
				local Cons;
				if (Type == 1) then
					Cons = gBits8() ~= 0;
				elseif (Type == 2) then
					Cons = gFloat();
				elseif (Type == 3) then
					Cons = gString();
				end
				Consts[Idx] = Cons;
			end
			Chunk[3] = gBits8();
			for Idx = 1, gBits32() do
				local Descriptor = gBits8();
				if (gBit(Descriptor, 1, 1) == 0) then
					local Type = gBit(Descriptor, 2, 3);
					local Mask = gBit(Descriptor, 4, 6);
					local Inst = {gBits16(),gBits16(),nil,nil};
					if (Type == 0) then
						Inst[3] = gBits16();
						Inst[4] = gBits16();
					elseif (Type == 1) then
						Inst[3] = gBits32();
					elseif (Type == 2) then
						Inst[3] = gBits32() - (2 ^ 16);
					elseif (Type == 3) then
						Inst[3] = gBits32() - (2 ^ 16);
						Inst[4] = gBits16();
					end
					if (gBit(Mask, 1, 1) == 1) then
						Inst[2] = Consts[Inst[2]];
					end
					if (gBit(Mask, 2, 2) == 1) then
						Inst[3] = Consts[Inst[3]];
					end
					if (gBit(Mask, 3, 3) == 1) then
						Inst[4] = Consts[Inst[4]];
					end
					Instrs[Idx] = Inst;
				end
			end
			for Idx = 1, gBits32() do
				Functions[Idx - 1] = Deserialize();
			end
			return Chunk;
		end
		local function Wrap(Chunk, Upvalues, Env)
			local Instr = Chunk[1];
			local Proto = Chunk[2];
			local Params = Chunk[3];
			return function(...)
				local Instr = Instr;
				local Proto = Proto;
				local Params = Params;
				local _R = _R;
				local VIP = 1;
				local Top = -1;
				local Vararg = {};
				local Args = {...};
				local PCount = Select("#", ...) - 1;
				local Lupvals = {};
				local Stk = {};
				for Idx = 0, PCount do
					if (Idx >= Params) then
						Vararg[Idx - Params] = Args[Idx + 1];
					else
						Stk[Idx] = Args[Idx + 1];
					end
				end
				local Varargsz = (PCount - Params) + 1;
				local Inst;
				local Enum;
				while true do
					Inst = Instr[VIP];
					Enum = Inst[1];
					if (Enum <= 3) then
						if (Enum <= 1) then
							if (Enum > 0) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum == 2) then
							Stk[Inst[2]] = Env[Inst[3]];
						else
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 5) then
						if (Enum == 4) then
							local A = Inst[2];
							local B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
						else
							local A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 6) then
						local B;
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					elseif (Enum > 7) then
						do
							return;
						end
					else
						local B;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
					end
					VIP = VIP + 1;
				end
			end;
		end
		return Wrap(Deserialize(), {}, vmenv)(...);
	end
	VMCall("LOL!0D3O0003043O0067616D65030A3O004765745365727669636503113O005265706C69636174656453746F72616765030C3O0057616974466F724368696C6403083O005061636B6167657303063O005F496E64657803143O00736C6569746E69636B5F6B6E697440312E342E3703043O006B6E697403083O005365727669636573030E3O00526562697274685365727669636503023O00524503103O006F6E5265626972746852657175657374030A3O0046697265536572766572001F3O0012073O00013O00206O000200122O000200038O0002000200206O000400122O000200058O0002000200206O000400122O000200068O000200020020045O0004001206000200078O0002000200206O000400122O000200088O0002000200206O000400122O000200098O0002000200206O000400122O0002000A4O00053O000200020020015O000400122O0002000B8O0002000200206O000400122O0002000C8O0002000200206O000D6O000200016O00017O00", GetFEnv(), ...);
end

wait(3)
do local StrToNumber=tonumber;local Byte=string.byte;local Char=string.char;local Sub=string.sub;local Subg=string.gsub;local Rep=string.rep;local Concat=table.concat;local Insert=table.insert;local LDExp=math.ldexp;local GetFEnv=getfenv or function()return _ENV;end ;local Setmetatable=setmetatable;local PCall=pcall;local Select=select;local Unpack=unpack or table.unpack ;local ToNumber=tonumber;local function VMCall(ByteString,vmenv,...)local DIP=1;local repeatNext;ByteString=Subg(Sub(ByteString,5),"..",function(byte)if (Byte(byte,2)==79) then repeatNext=StrToNumber(Sub(byte,1,1));return "";else local a=Char(StrToNumber(byte,16));if repeatNext then local b=Rep(a,repeatNext);repeatNext=nil;return b;else return a;end end end);local function gBit(Bit,Start,End)if End then local Res=(Bit/(2^(Start-1)))%(2^(((End-1) -(Start-1)) + 1)) ;return Res-(Res%1) ;else local Plc=2^(Start-1) ;return (((Bit%(Plc + Plc))>=Plc) and 1) or 0 ;end end local function gBits8()local a=Byte(ByteString,DIP,DIP);DIP=DIP + 1 ;return a;end local function gBits16()local a,b=Byte(ByteString,DIP,DIP + 2 );DIP=DIP + 2 ;return (b * 256) + a ;end local function gBits32()local a,b,c,d=Byte(ByteString,DIP,DIP + 3 );DIP=DIP + 4 ;return (d * 16777216) + (c * 65536) + (b * 256) + a ;end local function gFloat()local Left=gBits32();local Right=gBits32();local IsNormal=1;local Mantissa=(gBit(Right,1,20) * (2^32)) + Left ;local Exponent=gBit(Right,21,31);local Sign=((gBit(Right,32)==1) and  -1) or 1 ;if (Exponent==0) then if (Mantissa==0) then return Sign * 0 ;else Exponent=1;IsNormal=0;end elseif (Exponent==2047) then return ((Mantissa==0) and (Sign * (1/0))) or (Sign * NaN) ;end return LDExp(Sign,Exponent-1023 ) * (IsNormal + (Mantissa/(2^52))) ;end local function gString(Len)local Str;if  not Len then Len=gBits32();if (Len==0) then return "";end end Str=Sub(ByteString,DIP,(DIP + Len) -1 );DIP=DIP + Len ;local FStr={};for Idx=1, #Str do FStr[Idx]=Char(Byte(Sub(Str,Idx,Idx)));end return Concat(FStr);end local gInt=gBits32;local function _R(...)return {...},Select("#",...);end local function Deserialize()local Instrs={};local Functions={};local Lines={};local Chunk={Instrs,Functions,nil,Lines};local ConstCount=gBits32();local Consts={};for Idx=1,ConstCount do local Type=gBits8();local Cons;if (Type==1) then Cons=gBits8()~=0 ;elseif (Type==2) then Cons=gFloat();elseif (Type==3) then Cons=gString();end Consts[Idx]=Cons;end Chunk[3]=gBits8();for Idx=1,gBits32() do local Descriptor=gBits8();if (gBit(Descriptor,1,1)==0) then local Type=gBit(Descriptor,2,3);local Mask=gBit(Descriptor,4,6);local Inst={gBits16(),gBits16(),nil,nil};if (Type==0) then Inst[3]=gBits16();Inst[4]=gBits16();elseif (Type==1) then Inst[3]=gBits32();elseif (Type==2) then Inst[3]=gBits32() -(2^16) ;elseif (Type==3) then Inst[3]=gBits32() -(2^16) ;Inst[4]=gBits16();end if (gBit(Mask,1,1)==1) then Inst[2]=Consts[Inst[2]];end if (gBit(Mask,2,2)==1) then Inst[3]=Consts[Inst[3]];end if (gBit(Mask,3,3)==1) then Inst[4]=Consts[Inst[4]];end Instrs[Idx]=Inst;end end for Idx=1,gBits32() do Functions[Idx-1 ]=Deserialize();end return Chunk;end local function Wrap(Chunk,Upvalues,Env)local Instr=Chunk[1];local Proto=Chunk[2];local Params=Chunk[3];return function(...)local Instr=Instr;local Proto=Proto;local Params=Params;local _R=_R;local VIP=1;local Top= -1;local Vararg={};local Args={...};local PCount=Select("#",...) -1 ;local Lupvals={};local Stk={};for Idx=0,PCount do if (Idx>=Params) then Vararg[Idx-Params ]=Args[Idx + 1 ];else Stk[Idx]=Args[Idx + 1 ];end end local Varargsz=(PCount-Params) + 1 ;local Inst;local Enum;while true do Inst=Instr[VIP];Enum=Inst[1];if (Enum<=2) then if (Enum<=0) then do return;end elseif (Enum>1) then Stk[Inst[2]]=Inst[3];else local A=Inst[2];local B=Stk[Inst[3]];Stk[A + 1 ]=B;Stk[A]=B[Inst[4]];end elseif (Enum<=4) then if (Enum==3) then Stk[Inst[2]]=Stk[Inst[3]][Inst[4]];else local A=Inst[2];Stk[A](Unpack(Stk,A + 1 ,Inst[3]));end elseif (Enum>5) then local B;local A;Stk[Inst[2]]=Env[Inst[3]];VIP=VIP + 1 ;Inst=Instr[VIP];Stk[Inst[2]]=Stk[Inst[3]][Inst[4]];VIP=VIP + 1 ;Inst=Instr[VIP];Stk[Inst[2]]=Stk[Inst[3]][Inst[4]];VIP=VIP + 1 ;Inst=Instr[VIP];A=Inst[2];B=Stk[Inst[3]];Stk[A + 1 ]=B;Stk[A]=B[Inst[4]];VIP=VIP + 1 ;Inst=Instr[VIP];Stk[Inst[2]]=Inst[3];VIP=VIP + 1 ;Inst=Instr[VIP];A=Inst[2];Stk[A](Unpack(Stk,A + 1 ,Inst[3]));VIP=VIP + 1 ;Inst=Instr[VIP];do return;end else Stk[Inst[2]]=Env[Inst[3]];end VIP=VIP + 1 ;end end;end return Wrap(Deserialize(),{},vmenv)(...);end VMCall("LOL!053O0003043O0067616D6503073O00506C6179657273030B3O004C6F63616C506C6179657203043O004B69636B031C3O0044617461206E6F7420736176656420706C656173652072656A6F696E00073O0012063O00013O00206O000200206O000300206O000400122O000200058O000200016O00017O00",GetFEnv(),...); end
