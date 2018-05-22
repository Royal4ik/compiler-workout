open GT       
open Language
       
(* The type for the stack machine instructions *)
@type insn =
(* binary operator                 *) | BINOP   of string
(* put a constant on the stack     *) | CONST   of int
(* put a string on the stack       *) | STRING  of string
(* create an S-expression          *) | SEXP    of string * int
(* load a variable to the stack    *) | LD      of string
(* store a variable from the stack *) | ST      of string
(* store in an array               *) | STA     of string * int
(* a label                         *) | LABEL   of string
(* unconditional jump              *) | JMP     of string
(* conditional jump                *) | CJMP    of string * string
(* begins procedure definition     *) | BEGIN   of string * string list * string list
(* end procedure definition        *) | END
(* calls a function/procedure      *) | CALL    of string * int * bool
(* returns from a function         *) | RET     of bool
(* drops the top element off       *) | DROP
(* duplicates the top element      *) | DUP
(* swaps two top elements          *) | SWAP
(* checks the tag of S-expression  *) | TAG     of string
(* enters a scope                  *) | ENTER   of string list
(* leaves a scope                  *) | LEAVE
with show
                                                   
(* The type for the stack machine program *)
type prg = insn list

let print_prg p = List.iter (fun i -> Printf.printf "%s\n" (show(insn) i)) p
                            
(* The type for the stack machine configuration: control stack, stack and configuration from statement
   interpreter
*)
type config = (prg * State.t) list * Value.t list * Expr.config

(* Stack machine interpreter

     val eval : env -> config -> prg -> config

   Takes an environment, a configuration and a program, and returns a configuration as a result. The
   environment is used to locate a label to jump to (via method env#labeled <label_name>)
*)                                                  
let split n l =
  let rec unzip (taken, rest) = function
  | 0 -> (List.rev taken, rest)
  | n -> let h::tl = rest in unzip (h::taken, tl) (n-1)
  in
  unzip ([], l) n
          
let rec eval env config prg = 
	match prg with 
	| [] -> config
	| insn::p ->
		match config, insn with
		| (cstack, y::x::stack, c), BINOP operation -> 
eval env (cstack, (Value.of_int (Expr.binop operation (Value.to_int x) (Value.to_int y)))::stack, c) p
	 	| (cstack, stack, (s, i, o)), LD x -> eval env (cstack, (State.eval s x)::stack, (s, i, o)) p
		| (cstack, stack, conf), CONST value -> eval env (cstack, (Value.of_int value) :: stack, conf) p
		| (cstack, z::stack, (s, i, o)), ST x -> eval env (cstack, stack, ((Language.State.update x z s), i, o)) p
		| (cstack, stack, c), STRING str ->
                  eval env (cstack, (Value.of_string str)::stack, c) p
		|(cstack, stack, (s, i, o)), STA (x, n) -> 
      let v::ind, stack' = split (n + 1) stack in 
      eval env (cstack, stack', (Language.Stmt.update s x v (List.rev ind), i, o)) p
		| (cstack, stack, (s, i, o)), CALL (func, n, fl) -> if env#is_label func then eval env ((p, s)::cstack, stack, (s, i, o)) (env#labeled func) else eval env (env#builtin config func n fl) p
		| config, LABEL _ -> eval env config p
		| config, JMP label -> eval env config (env#labeled label)
    		| (cstack, z::stack, c), CJMP (cond, label)  -> (
		let x = match cond with
		| "nz" ->  Value.to_int z <> 0
		| "z" ->  Value.to_int z = 0 
	      	in eval env (cstack, stack, c) (if (x) then (env#labeled label) else p)
		)
		| (cstack, stack, (s, i, o)), BEGIN (_, args, x) ->
      		  let rec getArgs s = function
       			| a::args, z::stack -> let s', stack' = getArgs s (args, stack)
        		in State.update a z s', stack'
        		| [], stack -> s, stack
      		  in let s', stack' = getArgs (State.enter s (args @ x)) (args, stack)
      		  in eval env (cstack, stack', (s', i, o)) p
   		| (cstack, stack, (s, i, o)), END | (cstack, stack, (s, i, o)), RET _ ->
		(
      		  match cstack with
      		  | (prg, s')::cstack' ->
       		    eval env (cstack', stack, (State.leave s s', i, o)) prg
      		  | [] -> config
                )
		| (cstack, z::stack, c), DROP -> eval env (cstack, stack, c) p
                | (cstack, z::stack, c), DUP -> eval env (cstack, z::z::stack, c) p
                | (cstack, x::y::stack, c), SWAP -> eval env (cstack, y::x::stack, c) p
                | (cstack, sexp::stack, c), TAG s -> 
                  let res = if s = Value.tag_of sexp then 1 else 0 in 
                  eval env (cstack, (Value.of_int res)::stack, c) p
                | (cstack, stack, (s, i, o)), ENTER xs -> 
                  let vals, stack' = split (List.length xs) stack in
                  let st = List.fold_left2 (fun st' e var -> State.bind var e st') State.undefined vals xs in 
                    eval env (cstack, stack', (State.push s st xs, i, o)) p
                | (cstack, stack, (s, i, o)), LEAVE -> eval env (cstack, stack, (State.drop s, i, o)) p

(* Top-level evaluation

     val run : prg -> int list -> int list

   Takes a program, an input stream, and returns an output stream this program calculates
*)
let run p i =
  (* print_prg p; *)
  let module M = Map.Make (String) in
  let rec make_map m = function
  | []              -> m
  | (LABEL l) :: tl -> make_map (M.add l tl m) tl
  | _ :: tl         -> make_map m tl
  in
  let m = make_map M.empty p in
  let (_, _, (_, _, o)) =
    eval
      (object
         method is_label l = M.mem l m
         method labeled l = M.find l m
         method builtin (cstack, stack, (st, i, o)) f n p =
           let f = match f.[0] with 'L' -> String.sub f 1 (String.length f - 1) | _ -> f in
           let args, stack' = split n stack in
           let (st, i, o, r) = Language.Builtin.eval (st, i, o, None) (List.rev args) f in
           let stack'' = if p then stack' else let Some r = r in r::stack' in
           Printf.printf "Builtin: %s\n";
           (cstack, stack'', (st, i, o))
       end
      )
      ([], [], (State.empty, i, []))
      p
  in
  o

(* Stack machine compiler

     val compile : Language.t -> prg

   Takes a program in the source language and returns an equivalent program for the
   stack machine
*)
let compile (defs, p) = 
  let label s = "L" ^ s in
  let rec call f args p =
    let args_code = List.concat @@ List.map expr args in
    args_code @ [CALL (f, List.length args, p)]
  and pattern p lfalse =
    (let rec comp patt = 
      (match patt with
        Stmt.Pattern.Wildcard -> [DROP]
      | Stmt.Pattern.Ident x -> [DROP]
      | Stmt.Pattern.Sexp (tag, ps) -> 
        let res, _ = (List.fold_left (fun (acc, pos) patt -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ (comp patt)), pos + 1) ([], 0) ps) in
        [DUP; TAG tag; CJMP ("z", lfalse)] @ res) in comp p)
  and bindings p =
      let rec bind cp = 
        (match cp with
          Stmt.Pattern.Wildcard -> [DROP]
        | Stmt.Pattern.Ident x -> [SWAP]
        | Stmt.Pattern.Sexp (_, xs) -> 
        let res, _ = List.fold_left (fun (acc, pos) curp -> (acc @ [DUP; CONST pos; CALL (".elem", 2, false)] @ bind curp, pos + 1)) ([], 0) xs in 
        res @ [DROP]) in bind p @ [ENTER (Stmt.Pattern.vars p)]
    and expr e = 
        match e with
        | Expr.Const c -> [CONST c]
	| Expr.Var x -> [LD x]
	| Expr.String s -> [STRING s]
	| Expr.Array elems -> List.flatten (List.map expr elems) @ [CALL (".array", List.length elems, false)]
	| Expr.Elem (elems, i) ->  expr elems @ expr i @ [CALL (".elem", 2, false)]
        | Expr.Length t -> expr t @ [CALL (".length", 1, false)];
	| Expr.Binop (op, first, second) -> expr first @ expr second @ [BINOP op]
	| Expr.Call (name, params) -> call (label name) params false
        | Expr.Sexp (tag, exprs) ->
        let args = List.fold_left (fun acc index -> acc @ (expr index)) [] exprs in args @ [SEXP (tag, List.length exprs)] in
  let rec compile_stmt l env stmt =  
        match stmt with
	| Stmt.Assign (x, [], e) -> env, false, expr e @ [ST x]
	| Stmt.Assign (x, ind, e) -> 
          let indexes = List.fold_left (fun acc index -> acc @ (expr index)) [] ind in 
          env, false, (List.rev indexes @ expr e @ [STA (x, List.length ind)])
	| Stmt.Seq (firstStmt, secondStmt) -> 
          let env, _, first = compile_stmt l env firstStmt in
          let env, _, second = compile_stmt l env secondStmt in
          env, false, first @ second
	| Stmt.Skip -> env, false, []
  	| Stmt.If (e, t, f) ->
    	  let else_label, env = env#get_label in
      	  let end_label, env = env#get_label in
      	  let env, _, current_case = compile_stmt l env t in
          let env, _, last_case = compile_stmt l env f in
          env, false, (expr e) @ [CJMP ("z", else_label)] @ current_case @ [JMP end_label] @ [LABEL else_label] @ last_case @ [LABEL end_label]
  	| Stmt.While (e, s) ->
   	  let label_check, env = env#get_label in
          let loop, env = env#get_label in
          let env, _, s' = compile_stmt l env s in
          env, false, [JMP label_check; LABEL loop] @ s' @ [LABEL label_check] @ expr e @ [CJMP ("nz", loop)]
  	| Stmt.Repeat (e, s) ->
    	  let loop, env = env#get_label in
          let env, _, s' = compile_stmt l env s in
          env, false, [LABEL loop] @ s' @ expr e @ [CJMP ("z", loop)]
	| Stmt.Call (name, p) ->  env, false, call (label name) p true   
	|Stmt.Return e -> (
      	    match e with
            | None -> env, false, [RET false]
            | Some e -> env, false, expr e @ [RET true]
        )
	| Stmt.Case (e, pats) ->
          let rec compile_pat ps env label isFirst lend = 
          (match ps with
            [] -> env, []
            | (p, act)::tl -> 
              let env, _, body = compile_stmt l env act in 
              let lfalse, env = env#get_label
              and start = if isFirst then [] else [LABEL label] in
              let env, code = compile_pat tl env lfalse false lend in
              env, start @ (pattern p lfalse) @ bindings p @ body @ [LEAVE; JMP lend] @ code) in
          let lend, env = env#get_label in
          let env, code = compile_pat pats env "" true lend in
          env, false, (expr e) @ code @ [LABEL lend]
    | Stmt.Leave -> env, false, [LEAVE] 
in
let compile_def env (name, (args, locals, stmt)) =
    let lend, env       = env#get_label in
    let env, flag, code = compile_stmt lend env stmt in
    env,
    [LABEL name; BEGIN (name, args, locals)] @
    code @
    (if flag then [LABEL lend] else []) @
    [END]
  in
  let env =
    object
      val ls = 0
      method get_label = (label @@ string_of_int ls), {< ls = ls + 1 >}
    end
  in
  let env, def_code =
    List.fold_left
      (fun (env, code) (name, others) -> let env, code' = compile_def env (label name, others) in env, code'::code)
      (env, [])
      defs
  in
  let lend, env = env#get_label in
  let _, flag, code = compile_stmt lend env p in
  (if flag then code @ [LABEL lend] else code) @ [END] @ (List.concat def_code)
