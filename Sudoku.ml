open Printf
open Pervasives
open Str
(* formatting the Sudoku grids*)

 type cellule = { i : int; j : int };;
 type atome = { cellule : cellule; d : int; signe : bool };;
 type clause = atome list;;
 type fnc = clause list;;

let grid = Array.make_matrix 9 9 0;;
(*let formula = [];;*)


let rec line2grid line countline countcolumn =
	match line with
			|"" -> grid
			|line -> begin
					grid.(countline).(countcolumn) <- Char.code (String.get line 0) - 48;

					match countcolumn with
						| 8 -> line2grid (String.sub line 1 ((String.length line)-1)) (countline+1) 0 
						| _ -> line2grid (String.sub line 1 ((String.length line)-1)) countline (countcolumn+1)
					
				  end

;;
	
let rec printgrid grid countline countcolumn =
        match countline with
	| 9 -> begin printf "---------------------\n"; () end
	| _ -> begin
		if (countline mod 3 == 0 && countcolumn == 0) then printf "---------------------\n";
		match countcolumn with
			| 0|3|6 -> begin printf "|%d " grid.(countline).(countcolumn); printgrid  grid countline (countcolumn+1) end
			| 8 -> begin printf "%d|\n" grid.(countline).(countcolumn); printgrid  grid (countline+1) 0 end
			| _ -> begin printf "%d " grid.(countline).(countcolumn); printgrid  grid countline (countcolumn+1) end
		end
;;


(*translating into CNF formulas*)


(*DEFINEDNESS CLAUSES*)

(*for one cell*)
  let rec define_cell (*mat*) line column compt dclause = match compt with
	| 10 -> dclause
	| _ -> define_cell (*mat*) line column (compt+1) ( {cellule = {i=line;j=column}; d = compt; signe = true}::dclause)
  ;;

(*for the whole grid*)
  let rec define_mat (*mat*) line column dfnc =  
		match line with
			|9 -> dfnc
			|_ ->  (*if mat.(line).(column) = 0 
				then*) let dclause = define_cell (*mat*) line column 1 []  in define_mat (*mat*) (line+((column+1)/9)) ((column+1) mod 9) (dclause ::dfnc)
				(*else define_mat mat (line+((column+1)/9)) ((column+1) mod 9) dfnc*)
	;;

(*UNIQUENESS CLAUSES*)

(*for one cell*)
  let rec unique_cell (*mat*) line column compt compt' dfnc = 
	match compt with
	| 9 -> dfnc
	| _ -> match compt' with
		| 9 -> unique_cell (*mat*) line column (compt+1) (compt+2) ([{cellule = {i=line; j=column}; d = compt; signe = false};{cellule = {i=line; j=column}; d= compt'; signe = false}]::dfnc)
		| _ -> unique_cell (*mat*) line column compt (compt'+1) ([{cellule = {i=line; j=column}; d = compt; signe = false};{cellule = {i=line; j=column}; d= compt'; signe = false}]::dfnc)
 ;;

(*for the whole grid*)

 let rec unique_mat (*mat*) line column dfnc =
	match line with
		| 9 -> dfnc
		| _ -> (*if mat.(line).(column) = 0
			then*) let cell_dfnc = unique_cell (*mat*) line column 1 2 [] in unique_mat (*mat*) (line+((column+1)/9)) ((column+1) mod 9) 
												(List.append cell_dfnc dfnc)
			(*else unique_mat mat (line+((column+1)/9)) ((column+1) mod 9) dfnc*)
 ;;
	

(*VALIDITY CLAUSES*)

(*array constructors; construct arrays of indices*)

let array_sgrid x y = Array.of_list [{i=x;j=y};{i=x;j=y+1};{i=x;j=y+2};{i=x+1;j=y};{i=x+1;j=y+1};{i=x+1;j=y+2};{i=x+2;j=y};{i=x+2;j=y+1};{i=x+2;j=y+2}];;
	
let array_line x = Array.of_list [{i=x;j=0};{i=x;j=1};{i=x;j=2};{i=x;j=3};{i=x;j=4};{i=x;j=5};{i=x;j=6};{i=x;j=7};{i=x;j=8}];;

let array_column y = Array.of_list [{i=0;j=y};{i=1;j=y};{i=2;j=y};{i=3;j=y};{i=4;j=y};{i=5;j=y};{i=6;j=y};{i=7;j=y};{i=8;j=y}];;

(*validity formulas*)

(*iarray is the array holding the indices of the cells being considered: array_sgrid for small grid, array_line for line and array_column for column*)

let rec valid iarray i' j' d' dfnc =
	 match i' with
	| 8 -> dfnc
	| _ -> match j' with 
		| 8 -> if d'=9 then valid iarray (i'+1) (i'+2) 1 ([{cellule = {i= iarray.(i').i; j=iarray.(i').j}; d=d'; signe = false};{cellule ={i=iarray.(j').i; j= iarray.(j').j}; d=d'; signe=false}] :: dfnc) else valid iarray i' j' (d'+1) ([{cellule = {i= iarray.(i').i; j=iarray.(i').j}; d=d'; signe = false};{cellule ={i=iarray.(j').i; j= iarray.(j').j}; d=d'; signe=false}] :: dfnc)
			
		| _ -> match d' with
			| 9 -> valid iarray i' (j'+1) 1 ([{cellule = {i= iarray.(i').i; j=iarray.(i').j}; d=d'; signe = false};{cellule ={i=iarray.(j').i; j= iarray.(j').j}; d=d'; signe=false}] :: dfnc) 
			| _ -> valid iarray i' j' (d'+1) ([{cellule = {i= iarray.(i').i; j=iarray.(i').j}; d=d'; signe = false};{cellule ={i=iarray.(j').i; j= iarray.(j').j}; d=d'; signe=false}] :: dfnc)
	;;			


			


(*SMALL GRID*)

let valid_small_grid i j = let iarray = array_sgrid i j in
			    valid iarray 0 1 1 [];;

let rec valid_all_small_grids i j dfnc=
	match i with
	| 9 -> dfnc
	| _ -> match j with
		| 6 -> valid_all_small_grids (i+3) 0 (List.append (valid_small_grid i j) dfnc)
		| _ -> valid_all_small_grids i (j+3) (List.append (valid_small_grid i j) dfnc)
	;;
				

(*LINE*)

let valid_line i = let iarray = array_line i in
		   valid iarray 0 1 1 [];;

let rec valid_all_lines i dfnc=
	match i with
	| 9 -> dfnc
	| _ -> valid_all_lines (i+1) (List.append (valid_line i) dfnc)
	;;

(*COLUMN*)

let valid_column j = let iarray = array_column j in
		     valid iarray 0 1 1 [];;

let rec valid_all_columns j dfnc=
	match j with
	| 9 -> dfnc
	| _ -> valid_all_columns (j+1) (List.append (valid_column j) dfnc)
	;;

(*formulas for filled in cases*)
let rec unique_mat (*mat*) line column dfnc =
	match line with
		| 9 -> dfnc
		| _ -> (*if mat.(line).(column) = 0
			then*) let cell_dfnc = unique_cell (*mat*) line column 1 2 [] in unique_mat (*mat*) (line+((column+1)/9)) ((column+1) mod 9) 
												(List.append cell_dfnc dfnc)
			(*else unique_mat mat (line+((column+1)/9)) ((column+1) mod 9) dfnc*)
 ;;

let rec fill_case  line column dfnc=
	match line with
		| 9 -> dfnc
		| _ -> if grid.(line).(column) <> 0 then fill_case  (line+(column+1)/9) ((column+1) mod 9) ([{cellule={i=line;j=column};d=grid.(line).(column);signe=true}]::dfnc) else fill_case  (line+(column+1)/9) ((column+1) mod 9) dfnc
	;;
		
(*TODO - GET RID OF UNNECESSARY CLAUSES*)

(*print clauses in file*)

let rec recup_clause s formula =
	match s with
	| [] -> formula
	| {cellule = {i= a; j=b}; d=d'; signe = c}:: rest -> recup_clause rest (String.concat "|" [formula; (String.concat " " [Pervasives.string_of_int a;Pervasives.string_of_int b;Pervasives.string_of_int d';Pervasives.string_of_bool c;])])
	;;

let printclause dfnc = 
	let out = open_out "dfnc.txt" in
	List.iter (fun s ->fprintf out "Clause: %s \n" (recup_clause s "")) dfnc;
	close_out out;;

(*convert to dimacs format*)

let rec dimacs_clause s formula =
	match s with
	|[] -> String.concat " " [formula;"0"]
	|{cellule={i=a;j=b};d=d';signe=c}::rest -> let sign = if c=false then "-" else "" in dimacs_clause rest (String.concat " " [formula; (String.concat "" [sign;Pervasives.string_of_int (81*a + 9*b + d')])])
 ;;

let printdimacs dfnc =
	let out=open_out "dimacs.txt" in
	List.iter (fun s -> fprintf out "%s\n" (dimacs_clause s "")) dfnc;
	close_out out;;

let formatting string_formula =
	let _ = line2grid string_formula 0 0 in
	let  formula =  fill_case 0 0 (unique_mat 0 0 (define_mat 0 0 (valid_all_columns 0 (valid_all_lines 0 (valid_all_small_grids 0 0 []))))) in
	printgrid grid 0 0;
	printdimacs formula;;



(*turn minisat solution into Sudoku grid*)

let filetolist f = try let ic = open_in f in
		  	let n = in_channel_length ic in
				let s = String.create n in
					let _ = really_input ic s 0 n in
				        let s_list = Str.split (Str.regexp " ") (Str.global_replace (Str.regexp "SAT\n") "" (s)) in
					(*begin printf "found and opened!\n";*)
					close_in ic;	
					(*List.iter (fun s -> printf " %s;" s) s_list;*)
					s_list (*end*)
		with Not_found -> printf "What!\n";[];;
		
	
let rec turn2grid solution matrix=
	match solution with
	|a1::a2::a3::a4::a5::a6::a7::a8::a9::rest -> let aux =[a1;a2;a3;a4;a5;a6;a7;a8;a9] 
									in let value= int_of_string (List.find (fun s -> (int_of_string s) > 0) aux)
									in let i = if (value mod 81 <> 0)then value/81 else (value/81 -1)in let j = if (value - 81*i) mod 9 <> 0 then (value-81*i)/ 9 else ((value-81*i)/9-1) in let d = (value - 81*i - 9*j) in (*List.iter (fun s -> printf "%s;" s) aux; printf "\n %d \n" value;*)matrix.(i).(j) <- d; turn2grid rest matrix
	|_ -> matrix;;


let run_minisat f = let code = Sys.command "minisat dimacs.txt solution.txt -no-luby -rinc=1.5 -phase-saving=0 -rnd-freq=0.02" in
		    if code = -1 
			then printf "Something went wrong using minisat\n"
			else 
				printf "Minisat solution output in file solution.txt\n";
				printgrid (turn2grid (filetolist "solution.txt") (Array.make_matrix 9 9 0)) 0 0;;

	

(*
(*solution for this particular grid, retrieved via minisat*)
let solution =[-1;-2;-3;-4;-5;-6;7;-8;-9;-10;-11;-12;-13;-14;-15;-16;-17;18;-19;-20;-21;-22;23;-24;-25;-26;-27;-28;-29;30;-31;-32;-33;-34;-35;-36;-37;38;-39;-40;-41;-42;-43;-44;-45;-46;-47;-48;49;-50;-51;-52;-53;-54;55;-56;-57;-58;-59;-60;-61;-62;-63;-64;-65;-66;-67;-68;69;-70;-71;-72;-73;-74;-75;-76;-77;-78;-79;80;-81;-82;-83;-84;-85;-86;-87;-88;89;-90;-91;92;-93;-94;-95;-96;-97;-98;-99;100;-101;-102;-103;-104;-105;-106;-107;-108;-109;-110;-111;-112;-113;-114;-115;-116;117;-118;-119;-120;-121;122;-123;-124;-125;-126;-127;-128;-129;-130;-131;132;-133;-134;-135;-136;-137;-138;-139;-140;-141;142;-143;-144;-145;-146;-147;148;-149;-150;-151;-152;-153;-154;-155;156;-157;-158;-159;-160;-161;-162;-163;-164;-165;-166;-167;168;-169;-170;-171;-172;-173;-174;175;-176;-177;-178;-179;-180;-181;-182;183;-184;-185;-186;-187;-188;-189;190;-191;-192;-193;-194;-195;-196;-197;-198;-199;-200;-201;-202;-203;-204;-205;206;-207;-208;-209;-210;-211;-212;-213;214;-215;-216;-217;218;-219;-220;-221;-222;-223;-224;-225;-226;-227;-228;-229;230;-231;-232;-233;-234;-235;-236;-237;-238;-239;-240;-241;-242;243;-244;-245;-246;-247;248;-249;-250;-251;-252;-253;-254;255;-256;-257;-258;-259;-260;-261;-262;-263;-264;-265;-266;-267;-268;269;-270;-271;272;-273;-274;-275;-276;-277;-278;-279;-280;-281;-282;-283;-284;285;-286;-287;-288;289;-290;-291;-292;-293;-294;-295;-296;-297;-298;-299;-300;301;-302;-303;-304;-305;-306;-307;-308;-309;-310;-311;-312;-313;-314;315;-316;-317;-318;-319;-320;-321;322;-323;-324;-325;-326;-327;-328;-329;-330;-331;-332;333;-334;-335;-336;-337;-338;339;-340;-341;-342;-343;-344;-345;346;-347;-348;-349;-350;-351;-352;-353;-354;-355;356;-357;-358;-359;-360;-361;-362;-363;-364;-365;-366;367;-368;-369;-370;-371;372;-373;-374;-375;-376;-377;-378;-379;-380;-381;-382;-383;-384;-385;386;-387;388;-389;-390;-391;-392;-393;-394;-395;-396;-397;398;-399;-400;-401;-402;-403;-404;-405;-406;407;-408;-409;-410;-411;-412;-413;-414;415;-416;-417;-418;-419;-420;-421;-422;-423;-424;-425;-426;-427;-428;-429;430;-431;-432;-433;-434;-435;436;-437;-438;-439;-440;-441;-442;-443;-444;-445;-446;-447;-448;-449;450;-451;-452;-453;-454;-455;-456;-457;458;-459;-460;-461;-462;-463;-464;465;-466;-467;-468;-469;-470;471;-472;-473;-474;-475;-476;-477;-478;-479;-480;-481;482;-483;-484;-485;-486;-487;-488;-489;490;-491;-492;-493;-494;-495;-496;-497;-498;-499;-500;-501;502;-503;-504;-505;-506;-507;-508;-509;-510;-511;-512;513;-514;-515;-516;-517;-518;-519;-520;521;-522;523;-524;-525;-526;-527;-528;-529;-530;-531;-532;-533;-534;-535;536;-537;-538;-539;-540;-541;-542;543;-544;-545;-546;-547;-548;-549;-550;551;-552;-553;-554;-555;-556;-557;-558;-559;-560;-561;-562;-563;564;-565;-566;-567;568;-569;-570;-571;-572;-573;-574;-575;-576;-577;-578;-579;-580;581;-582;-583;-584;-585;-586;-587;-588;-589;-590;591;-592;-593;-594;-595;-596;-597;-598;-599;-600;601;-602;-603;-604;-605;606;-607;-608;-609;-610;-611;-612;-613;614;-615;-616;-617;-618;-619;-620;-621;-622;-623;-624;-625;-626;-627;-628;-629;630;-631;-632;-633;-634;-635;-636;-637;638;-639;-640;-641;-642;643;-644;-645;-646;-647;-648;-649;-650;651;-652;-653;-654;-655;-656;-657;-658;-659;-660;-661;-662;-663;-664;665;-666;-667;668;-669;-670;-671;-672;-673;-674;-675;-676;-677;-678;-679;-680;681;-682;-683;-684;-685;-686;-687;688;-689;-690;-691;-692;-693;-694;-695;-696;-697;-698;-699;-700;-701;702;-703;-704;-705;-706;707;-708;-709;-710;-711;-712;-713;-714;-715;-716;-717;718;-719;-720;721;-722;-723;-724;-725;-726;-727;-728;-729]
in let matrix = Array.make_matrix 9 9 0 in
    let m = turn2grid solution matrix in printgrid m 0 0;;
	*)

(*printgrid line2grid "790304108000006000000080059030000497000000000217000030470010000000700000302609071" 0 0*)

(*let l1 = define_cell grid 0 0 1 [];;*)



