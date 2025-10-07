use "ast.sml";
use "exceptions.sml";
open HashTable;

datatype value = 
    INT_VAL of int
  | BOOL_VAL of bool
  | STR_VAL of string
  | NONE_VAL
  | CLOSURE_VAL of {id: unit ref, st: state, params: decl list, decls: decl list, body: statement list}
  withtype state = (string, value) hash_table list
;

exception DoesNotExistException;
exception InvalidReturnException of value;

val hash : string -> word = HashString.hashString;
val compare : string * string -> bool = (op =);
val stateSize : int = 101;

fun createValue(var: string, st : state): unit = 
    if isSome(find (hd st) var)
    then raise VariableRedeclarationException(var)
    else insert (hd st) (var, NONE_VAL)
;

fun declareFunction((name, {params, decls, body}): (string * function), st: state): unit =
    if isSome(find (hd st) name)
    then raise VariableRedeclarationException(name)
    else insert (hd st) (name, CLOSURE_VAL {id = ref (), st = st, params = params, decls = decls, body = body})
;

fun createValues([], _) = ()
  | createValues(x :: xs, st) =
      (createValue(x, st); createValues(xs, st))
;

fun declareFunctions([], _) = () 
  | declareFunctions((name, f) :: xs, st) =
      (declareFunction ((name, f), st); declareFunctions(xs, st))
;

fun findVal(st: state, var: string): value =
    case st of
        [] => raise UndeclaredVariableException(var)
        | x :: xs =>
            (case find x var of
                SOME v => v
                | NONE => findVal(xs, var)
            )
;

fun assignValue(id: string, value: value, st: state) =
    case st of
        [] => raise UndeclaredVariableException(id)
        | x :: xs =>
            if isSome(find x id)
            then insert x (id, value)
            else assignValue(id, value, xs)
;

fun getTypeAsString(var: value): string =
    case var of 
        INT_VAL x => "number"
        | BOOL_VAL x => "boolean"
        | STR_VAL x => "string"
        | NONE_VAL => "none"
        | CLOSURE_VAL _ => "closure"
;

fun eqValue (INT_VAL n1, INT_VAL n2) = n1 = n2
    | eqValue (BOOL_VAL b1, BOOL_VAL b2) = b1 = b2
    | eqValue (STR_VAL s1, STR_VAL s2) = s1 = s2
    | eqValue (NONE_VAL, NONE_VAL) = true
    | eqValue (CLOSURE_VAL {id = id1, ...}, CLOSURE_VAL {id = id2, ...}) = id1 = id2
    | eqValue _ = false
;

fun printValue v =
    case v of
        INT_VAL n => 
            let 
                val str = Int.toString n
            in
                if String.sub(str, 0) = #"~" 
                then print ("-" ^ String.extract(str, 1, NONE))
                else print str
            end
        | STR_VAL s => print s
        | BOOL_VAL b => print (Bool.toString b)
        | NONE_VAL => print "none"
        | CLOSURE_VAL _ => print "function"
;

fun evalExpression (exp: expression, st: state) : value =
    case exp of
        EXP_NUM n => INT_VAL n
        | EXP_STRING s => STR_VAL s
        | EXP_BOOL b => BOOL_VAL b
        | EXP_NONE => NONE_VAL
        | EXP_ID var => findVal(st, var)
        | EXP_ASSIGN {lhs, rhs} =>
            (case lhs of 
                EXP_ID var =>
                    let val v = evalExpression(rhs, st)
                    in assignValue (var, v, st); v
                    end
                | _ => raise AssignmentTargetException)
        | EXP_BINARY {opr, lft, rht} =>
            let
                val val1 = evalExpression(lft, st)
                val val2 = evalExpression(rht, st)
            in
                case opr of
                    BOP_PLUS =>
                        (case (val1, val2) of
                            (INT_VAL n1, INT_VAL n2) => INT_VAL (n1 + n2)
                            | (STR_VAL s1, STR_VAL s2) => STR_VAL (s1 ^ s2)
                            | _ => raise AddException (getTypeAsString(val1), getTypeAsString(val2)))
                    | BOP_MINUS =>
                        (case (val1, val2) of
                            (INT_VAL n1, INT_VAL n2) => INT_VAL (n1 - n2)
                            | _ => raise ArithmeticException (BOP_MINUS, getTypeAsString(val1), getTypeAsString(val2)))
                    | BOP_TIMES =>
                        (case (val1, val2) of
                            (INT_VAL n1, INT_VAL n2) => INT_VAL (n1 * n2)
                            | _ => raise ArithmeticException (BOP_TIMES, getTypeAsString(val1), getTypeAsString(val2)))
                    | BOP_DIVIDE =>
                        (case (val1, val2) of
                            (INT_VAL n1, INT_VAL 0) => raise ZeroDivideException
                            | (INT_VAL n1, INT_VAL n2) => INT_VAL (n1 div n2)
                            | _ => raise ArithmeticException (BOP_DIVIDE, getTypeAsString(val1), getTypeAsString(val2)))
                    | BOP_MOD =>
                        (case (val1, val2) of
                            (INT_VAL n1, INT_VAL n2) => INT_VAL (n1 mod n2)
                            | _ => raise ArithmeticException (BOP_MOD, getTypeAsString(val1), getTypeAsString(val2)))
                    | BOP_EQ => BOOL_VAL (eqValue(val1, val2))
                    | BOP_NE => BOOL_VAL (not(eqValue(val1, val2)))
                    | BOP_LT =>
                        (case (val1, val2) of
                            (INT_VAL n1, INT_VAL n2) => BOOL_VAL (n1 < n2)
                            | _ => raise RelationalException (BOP_LT, getTypeAsString(val1), getTypeAsString(val2)))
                    | BOP_GT =>
                        (case (val1, val2) of
                            (INT_VAL n1, INT_VAL n2) => BOOL_VAL (n1 > n2)
                            | _ => raise RelationalException (BOP_GT, getTypeAsString(val1), getTypeAsString(val2)))
                    | BOP_LE =>
                        (case (val1, val2) of
                            (INT_VAL n1, INT_VAL n2) => BOOL_VAL (n1 <= n2)
                            | _ => raise RelationalException (BOP_LE, getTypeAsString(val1), getTypeAsString(val2)))
                    | BOP_GE =>
                        (case (val1, val2) of
                            (INT_VAL n1, INT_VAL n2) => BOOL_VAL (n1 >= n2)
                            | _ => raise RelationalException (BOP_GE, getTypeAsString(val1), getTypeAsString(val2)))
                    | BOP_AND =>
                        (case (val1, val2) of
                            (BOOL_VAL b1, BOOL_VAL b2) => BOOL_VAL (b1 andalso b2)
                            | _ => raise BooleanFirstException (BOP_AND, "Expected Boolean"))
                    | BOP_OR =>
                        (case (val1, val2) of
                            (BOOL_VAL b1, BOOL_VAL b2) => BOOL_VAL (b1 orelse b2)
                            | _ => raise BooleanFirstException (BOP_OR, "Expected Boolean"))
            end
        | EXP_UNARY {opr, opnd} =>
            let val v = evalExpression(opnd, st)
            in
                case opr of
                    UOP_NOT =>
                        (case v of
                            BOOL_VAL b => BOOL_VAL (not b)
                            | _ => raise UnaryNotException "Expected Boolean")
                    | UOP_MINUS =>
                        (case v of
                            INT_VAL n => INT_VAL (~n)
                            | _ => raise UnaryMinusException "Expected Number")
            end
        | EXP_COND {guard, thenExp, elseExp} =>
            (case evalExpression(guard, st) of
                BOOL_VAL true => evalExpression(thenExp, st)
                | BOOL_VAL false => evalExpression(elseExp, st)
                | _ => raise ConditionalException "Expected Boolean Guard")

        | EXP_CALL {func, args} => 
            (let 
                val closure = evalExpression(func, st)
                val arg_values = List.map (fn arg => evalExpression(arg, st)) args
            in 
                case closure of 
                    CLOSURE_VAL {id, st = closure_st, params, decls, body} => 
                    (let
                        val _ = if length arg_values > length params
                                then raise CallTooManyArgumentsException
                                else if length arg_values < length params
                                then raise CallTooFewArgumentsException
                                else ()
                        val scope = mkTable (hash, compare) (stateSize, DoesNotExistException)
                        val _ = createValues(params, [scope])
                        val _ = List.app (fn (param, arg_val) => insert scope (param, arg_val)) (ListPair.zip (params, arg_values))
                        val _ = createValues(decls, [scope])
                    in 
                        (evaluateStatements(body, scope :: closure_st); NONE_VAL)
                        handle InvalidReturnException v => v
                    end)
                | _ => raise NonFunctionException(getTypeAsString closure)
            end)
    | EXP_ANON {params, decls, body} => 
        (CLOSURE_VAL {id = ref (), st = st, params = params, decls = decls, body = body})

and evaluateStatement (stmt: statement, st: state) : unit =
    case stmt of
        ST_EXP {exp} => 
            (ignore (evalExpression(exp, st)); ())
        | ST_PRINT {exp} => 
            (printValue (evalExpression(exp, st)); ())
        | ST_IF {guard, th, el} =>
            evaluateIfStatement (guard, th, el, st)
        | ST_WHILE {guard, body} =>
            let
                fun loop () =
                    case evalExpression(guard, st) of
                        BOOL_VAL true => (evaluateStatement(body, st); loop ())
                      | BOOL_VAL false => ()
                      | _ => raise WhileGuardException "Expected Boolean in while-loop guard"
            in
                loop ()
            end
        | ST_BLOCK {stmts} => 
            (List.app (fn stmt => evaluateStatement(stmt, st)) stmts; ())
        | ST_RETURN {exp = SOME exp} => 
            (let
                val v = evalExpression(exp, st)
            in
                raise InvalidReturnException v
            end
            )
        | ST_RETURN {exp = NONE} => raise InvalidReturnException(NONE_VAL)

and evaluateIfStatement (guard: expression, th: statement, el: statement option, st: state) : unit =
    (let 
        val v = evalExpression(guard, st)
    in 
        case v of 
            BOOL_VAL true => evaluateStatement(th, st)
            | BOOL_VAL false => (case el of
                                    SOME elseStmt => evaluateStatement(elseStmt, st)
                                    | _ => ())
            | _ => raise IfGuardException "Expected Boolean"
    end)

and evaluateStatements (stmts: statement list, st: state) : unit =
    case stmts of
        [] => ()
      | x :: xs => (evaluateStatement(x, st); evaluateStatements(xs, st))

and evaluate(PROGRAM {decls, func_decls, stmts}: program): unit =
    let 
        val s = mkTable (hash, compare) (stateSize, DoesNotExistException);
        val _ = createValues(decls, [s]);
        val _ = declareFunctions(func_decls, [s])

    in 
        (evaluateStatements(stmts, [s]); ())
        handle InvalidReturnException v => raise ReturnOutsideFunctionException
    end
;