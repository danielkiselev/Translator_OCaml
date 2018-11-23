let globalCounter = ref 0;;
let globalBool = ref 0;;
let local_count = ref 0;;
let label_count = ref 0;;
let globalData = Hashtbl.create 123456;;
let localData = Hashtbl.create 123456;;
let funcCode = ref [];;
let stringBuilder = ref "";;
let breakCounter = ref 0;;
let contCounter = ref 0;;






type token_type = Symbol | Reserved | Identifier | Meta | String | Number | End ;;
type token = { v : string ; t : token_type};;


type 'a btnode = 
  | Nil
  | Node of 'a btnode * 'a  * 'a btnode;;


let tokens = Queue.create () ;;
let addToken t = Queue.add t tokens;;


let peekToken txs =
    if Queue.is_empty txs 
        then {v=""; t=End} 
    else Queue.peek txs;;

let matchToken txs =
    if Queue.is_empty txs
        then {v=""; t=End}
            else Queue.pop txs;;
(*inserts right sibling into left sibling*)

let checkToken txs c = 
    if (peekToken txs).v = c then
    (
        let _ = matchToken txs in
        Node (Nil, c, Nil)
    )
    else Nil;;

let codeAdd s =
    funcCode := !funcCode @ [s] ;;



let rec print_list l =
match l with
| [] -> ()
| e::l -> (
    print_string e ; print_string "\n" ; print_list l
          );;



let addNextSibling leftSibling rightSibling =
    match leftSibling with
    | Nil -> Nil
    | Node(lmc, data, rs) -> Node(lmc, data, rightSibling);;


let addChild parent child =
    match parent with
    | Nil -> Nil
    | Node(lmc, data, rs) -> Node(child, data, rs);;

let childOf node =
    match node with
    | Nil -> Nil
    | Node (lmc, data, rs) -> lmc;;
    

let siblingOf node =
    match node with
    | Nil -> Nil
    | Node (lmc, data, rs) -> rs;;
    
let getData node =
    match node with
    | Nil -> ""
    | Node (lmc, data, rs) -> data;;

let codeCheck input =
    let len = String.length input - 1 in
    let p1 = String.get input len in
    let p2 = String.get input 0 in
    if p1 = '>' && p2 = '<' then begin
        false
    end
    else true;;

let replaceLabel node new_label =
    match node with
    | Nil -> Nil
    | Node(lmc, data, rs)-> Node(lmc, new_label, rs);;

(*
=================================================================================
======================= GRAMMAR BELOW THIS LINE =================================
=================================================================================
*)

let string txs = (* <string> -> any sequence of chars between " " *) 
    let production  = Node (Nil, "<string>", Nil) in
    if (peekToken txs).t = String
        then
        (
            let c1 = checkToken txs (peekToken txs).v in
            addChild production c1
        )
    else Nil;;

let typeName txs =
    let production  = Node (Nil, "<typeName>", Nil) in
    if (peekToken txs).v = "void" || (peekToken txs).v = "int"
        then begin
            let c1 = checkToken txs (peekToken txs).v in
            addChild production c1
        end
    else Nil;;


(*    <mulOp> -> * | /     *)
let mulOp txs =  
    let production  = Node (Nil, "<mulop>", Nil) in
    if (peekToken txs).v = "*" || (peekToken txs).v = "/"
        then begin
            let c1 = checkToken txs (peekToken txs).v  in
            addChild production c1
        end
    else Nil;;



(* <number> -> [0-9]*      *)
let number txs = 
    let production = Node(Nil, "<number>", Nil) in
    if (peekToken txs).t = Number
        then begin
            let c1 = checkToken txs (peekToken txs).v in
            addChild production c1
        end
    else Nil;;




(*<addOp> -> + | - *)
let addOp txs =
    let production  = Node (Nil, "<addOp>", Nil) in
    if (peekToken txs).v = "+" || (peekToken txs).v = "-"
        then (
            let c1 = checkToken txs (peekToken txs).v in
            addChild production c1
        )
    else Nil;;

(*  <identifier> -> [a-Z]+[0-9]*      -- this could change if we have to include arrays as part of INPUT grammar *)
let identifier txs = 
    let production  = Node (Nil, "<identifier>", Nil) in
    let c1 = checkToken txs (peekToken txs).v in
    addChild production c1;;


(*    <mulOp> -> * | /     *)
let mulOp txs =  
    let production = Node(Nil, "<mulOp>", Nil) in
    if (peekToken txs).v = "*" || (peekToken txs).v = "/"
        then (
            addChild production (checkToken txs (peekToken txs).v)
        )
    else Nil;;



let rec idList txs =  (* <idList> -> <identifier> <idListSuffix> *)
    let production = Node(Nil, "<idList>", Nil) in
    let c1 = identifier txs in
    let c2 = idListSuffix txs in
    addChild production (addNextSibling c1 c2)
(* <idListSuffix> -> , <idList> | epsilon *)
and idListSuffix txs =
    let production = Node(Nil, "<idListSuffix>", Nil) in
    if (peekToken txs).v = ","
        then(
            let c1 = checkToken txs "," in
            let c2 = idList txs in
            addChild production (addNextSibling c1 c2)
        )
else addChild production (Node(Nil, "<epsilon>", Nil));; (*epsilon*)


let rec dataDecls txs = (* <dataDecls> -> epsilon | <typeName> <idList> ; <dataDecls> *)
    let production = Node(Nil, "<dataDecls>", Nil) in
    let myToken = peekToken txs in
    if myToken.v = "int" || myToken.v = "void"
        then
            (
                let c1 = typeName txs in
                let c2 = idList txs in
                let c3 = checkToken txs ";" in 
                let c4 = dataDecls txs in
                addChild production (addNextSibling c1 (addNextSibling c2 (addNextSibling c3 c4)))
            )
else addChild production (Node(Nil, "<epsilon>", Nil));;



(*NOTE: FUNCTIONS BELOW CALL EACH OTHER SO THEY HAD TO BE DONE IN A SINGLE DECLARATION*)
(*<expression> -> <term> <addExp> *)
let rec expression txs = 
    let production = Node(Nil, "<expression>", Nil) in
    let term_node = term txs in
    let addExp_node = addExp txs in
    addChild production (addNextSibling term_node addExp_node)
and (*<addExp> -> <addOp> <expression> | epsilon *)
addExp txs = 
    let production = Node(Nil, "<addExp>", Nil) in
    if (peekToken txs).v = "+" || (peekToken txs).v = "-"
        then begin
            let addOp_node = addOp txs in
            let expression_node = expression txs in
            addChild production (addNextSibling addOp_node expression_node)
        end
    else addChild production (Node(Nil, "<epsilon>", Nil)) (*epsilon*)
and (*<term> -> <factor> <mulTerm> *)
term txs =
    let production = Node(Nil, "<term>", Nil) in
    let factor_node = factor txs in
    let mulTerm_node = mulTerm txs in
    if factor_node = Nil  || mulTerm_node = Nil then(
        Nil;
    )
    else(
        addChild production (addNextSibling factor_node mulTerm_node)
    )
    
and (*<mulTerm> -> <mulOp> <term> | epsilon*)
mulTerm txs =
    let production = Node(Nil, "<mulTerm>", Nil) in
    if (peekToken txs).v = "*" || (peekToken txs).v =  "/" then
    (
        let mulOp_node = mulOp txs in
        let term_node = term txs in
        addChild production (addNextSibling mulOp_node term_node)
    )else addChild production (Node(Nil, "<epsilon>", Nil))
and (*<factor> -> <identifier><factorSuffix> | <number> | -<number> | (<expression>) *)
factor txs =
    let production = Node(Nil, "<factor>", Nil) in
    if (peekToken txs).t = Identifier
        then (
            let ident_node = identifier txs in
            let factor_suffix_node = factorSuffix txs in
            addChild production (addNextSibling ident_node factor_suffix_node)
             )
    else if (peekToken txs).v = "-"
    then
        (
            let minus_char = checkToken txs "-" in
            let number_node = number txs in
            addChild production (addNextSibling minus_char number_node)
        )

    else if (peekToken txs).t = Number
        then addChild production (number txs) 
    else if (peekToken txs).v = "("
        then
            (
                let o_paren_node =  checkToken txs "(" in
                let exp_node = expression txs in 
                let c_paren_node = checkToken txs ")" in
                addChild production (addNextSibling o_paren_node (addNextSibling exp_node c_paren_node))
            )
    else Nil

(*
NOTE: do not actually implement the [<expression>] part since the input language does not include arrays
<factorSuffix> -> [<expression>] | (<exprList>) | epsilon *)
and 
factorSuffix txs = 
    let production = Node(Nil, "<factorSuffix>", Nil) in 
    let character = (peekToken txs).v in 
    if character = "("
        then 
            (
                let open_bracket_node = checkToken txs "(" in
                let expression_node = exprList txs in
                let close_bracket_node = checkToken txs ")" in
                addChild production (addNextSibling open_bracket_node (addNextSibling expression_node close_bracket_node))
            )
    else addChild production (Node(Nil, "<epsilon>", Nil)) (*epsilon*)
and
nonEmptyExprList txs =  (* <nonEmptyExprList> -> <expression> <commaExp> *)
    let production = Node(Nil, "<nonEmptyExprList>", Nil) in
    let expression_node = expression txs in
    let commaExp_node = commaExp txs in
    addChild production (addNextSibling expression_node commaExp_node)
and
commaExp txs=  (* <commaExp> -> , <nonEmptyExprList> | epsilon *)
    let production = Node(Nil, "<commaExp>", Nil) in
    if (peekToken txs).v = ","
        then
        (
            let comma_node = checkToken txs "," in
            let nonEmptyExprList_node = nonEmptyExprList txs in
            addChild production (addNextSibling comma_node nonEmptyExprList_node)
        )
    else addChild production (Node(Nil, "<epsilon>", Nil))
and 
exprList txs =  (* <exprList> -> <nonEmptyExprList> | epsilon *)
    let production = Node(Nil, "<exprList>", Nil) in
    
    let c1 = nonEmptyExprList txs in
        if c1 = Nil then(
            addChild production (Node(Nil, "<epsilon>", Nil))
        )
        else addChild production c1;;


(* <assignment> -> = <expression> ; *)

let assignment txs =
    let production = Node(Nil, "<assignment>", Nil) in
    let equals_node = checkToken txs "=" in
    let expression_node = expression txs in
    let semicolon_node = checkToken txs ";" in
    addChild production (addNextSibling equals_node (addNextSibling expression_node semicolon_node));;

let rec statements txs = (* <statements> -> epsilon | <statement> <statements> *)
    let production = Node(Nil, "<statements>", Nil) in
    let myToken = (peekToken txs) in
    if myToken.t = Identifier || myToken.v = "printf" || myToken.v = "scanf" || myToken.v = "if" || myToken.v = "while" || myToken.v = "return" || myToken.v = "break" || myToken.v = "continue"
        then 
        (
        let c1 = statement txs in
        let c2 = statements txs in
        addChild production (addNextSibling c1 c2)
        )
    else addChild production (Node(Nil, "<epsilon>", Nil))

and statement txs = (* <statement> -> <assignmentOrGeneralFuncCallPrefix> | <printFuncCall> | <scanfFuncCall> | <ifStatement> | <whileStatement> | <returnStatement> | <breakStatement> | <continueStatement> *)
    let production = Node(Nil, "<statement>", Nil) in

    let myToken = (peekToken txs) in
    if myToken.t = Identifier then addChild production (assignmentOrGeneralFuncCall txs)
    else if myToken.v = "printf" then addChild production (printFuncCall txs)
    else if myToken.v = "scanf" then addChild production (scanfFuncCall txs)
    else if myToken.v = "if" then addChild production (ifStatement txs)
    else if myToken.v = "while" then addChild production (whileStatement txs)
    else if myToken.v = "return" then addChild production (returnStatement txs)
    else if myToken.v = "break" then addChild production (breakStatement txs)
    else if myToken.v = "continue" then addChild production (continueStatement txs)
    else Nil

and assignmentOrGeneralFuncCall txs = (* <assignmentOrGeneralFuncCall> -> <identifier> <assignmentOrGeneralFuncCallSuffix> *)
    let production = Node(Nil, "<assignmentOrGeneralFuncCall>", Nil) in
    let c1 = identifier txs in
    let c2 = assignmentOrGeneralFuncCallSuffix txs in
    addChild production (addNextSibling c1 c2)



and generalFuncCall txs = (* <generalFuncCall> -> ( <exprList> ) ; *)
    let production = Node(Nil, "<generalFuncCall>", Nil) in
    let c1 = checkToken txs "(" in
    let c2 = exprList txs in
    let c3 = checkToken txs ")" in
    let c4 = checkToken txs ";" in
    addChild production (addNextSibling c1 (addNextSibling c2 (addNextSibling c3 c4)))

and assignmentOrGeneralFuncCallSuffix txs =  (* <assignmentOrGeneralFuncCallSuffix> -> [ <identifier> ] <assignment> | <assignment> | <generalFuncCall> *)
    let production = Node(Nil, "<assignmentOrGeneralFuncCallSuffix>", Nil) in
    let myToken = peekToken txs in
    if myToken.v = "="
        then (
            let c1 = assignment txs in 
            addChild production c1
        )
    else if myToken.v = "(" then (
        let c1 = generalFuncCall txs in 
        addChild production c1
    )
    else Nil

and printFuncCall txs =         (* <printfFuncCall> -> printf ( <string> <printFuncCallWithExpression> ) ; *)
    let production = Node(Nil, "<printFuncCall>", Nil) in
    if (peekToken txs).v = "printf"
        then
            (
                let c1 = checkToken txs "printf"  in                
                let c2 = checkToken txs "(" in
                let c3 = string txs in
                let c4 = printFuncCallWithExpression txs in
                let c5 = checkToken txs ")"  in
                let c6 = checkToken txs ";" in
                addChild production (addNextSibling c1 (addNextSibling c2 (addNextSibling c3 (addNextSibling c4 (addNextSibling c5 c6)))))
            )
        else Nil


and printFuncCallWithExpression txs = (* <printFuncCallWithExpression> -> epsilon | , <expression> *)
let production = Node(Nil, "<printFuncCallWithExpression>", Nil) in
if (peekToken txs).v = ","
        then
            (
                let c1 = checkToken txs "," in
                let c2 = expression txs in
                addChild production (addNextSibling c1 c2)
            )
        else addChild production (Node(Nil, "<epsilon>", Nil))


and scanfFuncCall txs =         (* <scanfFuncCall> -> scanf ( <string> , & <expression> ) ; *)
    let production = Node(Nil, "<scanf>", Nil) in
    if (peekToken txs).v = "scanf"
        then
            (
                let c1 = checkToken txs "scanf" in                
                let c2 = checkToken txs "(" in
                let c3 = string txs in
                let c4 = checkToken txs "," in
                let c5 = checkToken txs "&" in
                let c6 = expression txs in
                let c7 = checkToken txs ")" in
                let c8 = checkToken txs ";" in
                addChild production (addNextSibling c1 (addNextSibling c2 (addNextSibling c3 (addNextSibling c4 (addNextSibling c5 (addNextSibling c6 (addNextSibling c7 c8)))))))
            )
        else Nil

and ifStatement txs =           (* <ifStatement> -> if ( <conditionExpression> ) <blockStatements> <elseStatement> *)
    let production = Node(Nil, "<ifStatement>", Nil) in
            let c1 = checkToken txs "if" in                
            let c2 = checkToken txs "(" in
            let c3 = conditionExpression txs in
            let c4 = checkToken txs ")" in
            let c5 = blockStatements txs in
            let c6 = elseStatement txs in
            addChild production (addNextSibling c1 (addNextSibling c2 (addNextSibling c3 (addNextSibling c4 (addNextSibling c5 c6)))))

and elseStatement txs =   (* <elseStatement> -> epsilon |  else <blockStatements> *)
let production = Node(Nil, "<elseStatement>", Nil) in
if (peekToken txs).v = "else"
        then
            (
                let c1 = checkToken txs "else" in 
                let c2 = blockStatements txs in
                addChild production (addNextSibling c1 c2 )
            )
else addChild production (Node(Nil, "<epsilon>", Nil))

and whileStatement txs =        (* <whileStatement> -> while ( <conditionExpression> ) <blockStatements> *)
    let production = Node(Nil, "<whileStatement>", Nil) in
        let c1 = checkToken txs "while"  in                
        let c2 = checkToken txs "(" in
        let c3 = conditionExpression txs in
        let c4 = checkToken txs ")"  in
        let c5 = blockStatements txs in
        addChild production (addNextSibling c1 (addNextSibling c2 (addNextSibling c3 (addNextSibling c4 c5))))
        

and conditionExpression txs =     (* <conditionExpression> -> <condition> <conditionExpressionSuffix> *)
    let production = Node(Nil, "<conditionExpression>", Nil) in
    let c1 = condition txs in
    let c2 = conditionExpressionSuffix txs in
    addChild production (addNextSibling c1 c2)

and condition txs =      (* <condition> -> <expression> <comparisonOp> <expression> *)
    let production = Node(Nil, "<condition>", Nil) in
    let c1 = expression txs in
    let c2 = comparisonOp txs in
    let c3 = expression txs in
    addChild production (addNextSibling c1 (addNextSibling c2 c3))
        

and comparisonOp txs =  (* <comparisonOp> -> == | != | > | >= | < | <= *)
    let production = Node(Nil, "<comparisonOp>", Nil) in
    if (peekToken txs).v =  "==" ||(peekToken txs).v = "!=" || (peekToken txs).v = ">" || (peekToken txs).v = ">=" || (peekToken txs).v = "<" || (peekToken txs).v = "<=" then(
        let c1 = checkToken txs (peekToken txs).v in
        addChild production c1
    )
    else Nil


and conditionExpressionSuffix txs =  (* <conditionExpressionSuffix> -> <conditionOp> <condition> | epsilon *)
    let production = Node(Nil, "<conditionExpressionSuffix>", Nil) in
    if (peekToken txs).v = "&&" || (peekToken txs).v = "||" then
    (
    let c1 = conditionOp txs in
    let c2 = condition txs in
    addChild production (addNextSibling c1 c2)
    )
else addChild production (Node(Nil, "<epsilon>", Nil))


and conditionOp txs =  (* <conditionOp> -> && | || *)
    let production  = Node (Nil, "<conditionOp>", Nil) in
    if (peekToken txs).v = "&&" || (peekToken txs).v = "||"
        then(
            let c1 = checkToken txs (peekToken txs).v in
            addChild production c1
        )
    else Nil

and blockStatements txs = (* <blockStatements> -> { <statements> } *)
    let production = Node(Nil, "<blockStatements>", Nil) in
    let c1 = checkToken txs "{" in
    let c2 = statements txs in
    let c3 = checkToken txs "}" in
    addChild production (addNextSibling c1 (addNextSibling c2 c3))

and returnStatement txs =       (* <returnStatement> -> return  <returnStatementSuffix> ; *)
    let production = Node(Nil, "<returnStatement>", Nil) in
    let c1 = checkToken txs "return" in
    let c2 = returnStatementSuffix txs in
    let c3 = checkToken txs ";" in
    addChild production (addNextSibling c1 (addNextSibling c2 c3 ))
    

and returnStatementSuffix txs = (* <returnStatementSuffix> -> <expression> | epsilon *)
let production = Node(Nil, "<returnStatementSuffix>", Nil) in
    let c1 = expression txs in
        if c1 = Nil then(
            addChild production (Node(Nil, "<epsilon>", Nil))
        )
    else addChild production c1

and breakStatement txs =        (* <breakStatement> -> break; *)
    let production = Node(Nil, "<breakStatement>", Nil) in
    let c1 = checkToken txs "break" in
    let c2 = checkToken txs ";" in
    addChild production (addNextSibling c1 c2)
    

and continueStatement txs =  (* <continueStatement> -> continue; *)
    let production = Node(Nil, "<continueStatement>", Nil) in
    let c1 = checkToken txs "continue"  in
    let c2 = checkToken txs ";"  in
    addChild production (addNextSibling c1 c2);;



let funcSuffix txs =  (* <funcSuffix> -> ;  | { <dataDecls> <statements> } *)
    let production = Node(Nil, "<funcSuffix>", Nil) in
    if (peekToken txs).v = ";"
    then
        (
            addChild production (checkToken txs ";")
        )
    else if (peekToken txs).v = "{" then
        (
            let open_paren_node = checkToken txs "{" in
            let dataDecls_node = dataDecls txs in
            let statements_node = statements txs in
            let close_paren_node = checkToken txs "}" in
            addChild production (addNextSibling open_paren_node (addNextSibling dataDecls_node (addNextSibling statements_node close_paren_node)))
        )
    else Nil;;

let rec funcList txs = (* <funcList> -> epsilon | <func> <funcList> *)
    let production = Node(Nil, "<funcList>", Nil) in
    if (peekToken txs).v = "void" || (peekToken txs).v = "int"
    then 
        (
            let func_node = func txs in
            let funcList_node = funcList txs in
            addChild production (addNextSibling func_node funcList_node)
        )
    else addChild production (Node(Nil, "<epsilon>", Nil))
and func txs = (*<func> -> <funcDecl> <funcSuffix>*)
    let production = Node(Nil, "<func>", Nil) in
    let funcDecl_node = funcDecl txs in
    let funcSuffix_node = funcSuffix txs in
    addChild production (addNextSibling funcDecl_node funcSuffix_node)

and funcDecl txs = (*<funcDecl> -> <typeName> <identifier> ( <parameterList> )*)
    let production = Node(Nil, "<funcDecl>", Nil) in
    let typeName_node = typeName txs in
    let identifier_node = identifier txs in
    let open_paren_node = checkToken txs "(" in
    let parameterList_node = parameterList txs in
    let close_paren_node = checkToken txs ")" in
    addChild production (addNextSibling typeName_node (addNextSibling identifier_node (addNextSibling open_paren_node (addNextSibling parameterList_node close_paren_node))))


and parameterList txs = (*<parameterList> -> epsilon | void | <nonEmptyList>*)
    let production = Node(Nil, "<parameterList>", Nil) in
    if (peekToken txs).v = "void"
        then addChild production (checkToken txs "void")
    else if (peekToken txs).v = "int" 
        then addChild production (nonEmptyList txs)
    else addChild production (Node(Nil, "<epsilon>", Nil))
and nonEmptyList txs =  (*<nonEmptyList> -> int <identifier> <nonEmptyListSuffix>*)
    let production = Node(Nil, "<nonEmptyList>", Nil) in
    let int_node = checkToken txs "int" in
    let identifier_node = identifier txs in
    let nonEmptyListSuffix_node = nonEmptyListSuffix txs in
    addChild production (addNextSibling int_node (addNextSibling identifier_node nonEmptyListSuffix_node))
and nonEmptyListSuffix txs = (*<nonEmptyListSuffix> -> , <nonEmptyList> | epsilon*)
    let production = Node(Nil, "<nonEmptyListSuffix>", Nil) in
    if (peekToken txs).v = ","
        then (
            let comma_node = checkToken txs "," in
            let nonEmptyList_node = nonEmptyList txs in
            addChild production (addNextSibling comma_node nonEmptyList_node)
        )
    else addChild production (Node(Nil, "<epsilon>", Nil));;

(*<nonEmptyList> -> int <identifier> <nonEmptyListSuffix>
<nonEmptyListSuffix> -> , <nonEmptyList> | epsilon
*)
let programFuncList txs = (* <programFuncList> -> (<parameterList>) <programFuncListBody> <funcList> *)
    let production = Node(Nil, "<programFuncList>", Nil) in
    let open_paren_node = checkToken txs "(" in
    let parameterList_node = parameterList txs in
    let close_paren_node = checkToken txs ")" in
    let programFuncListBody_node = funcSuffix txs in
    let funcList_node = funcList txs in
    addChild production (addNextSibling open_paren_node (addNextSibling parameterList_node (addNextSibling close_paren_node (addNextSibling programFuncListBody_node funcList_node))))

let programDataDecls txs = (*<programDataDecls> -> ; | , <idList> ;*)
    let production = Node(Nil, "<programDataDecls>", Nil) in
    if (peekToken txs).v = ";" 
        then(
            addChild production (checkToken txs ";")
        )
    else if (peekToken txs).v = "," 
        then (
            let comma_node = checkToken txs "," in
            let idList_node = idList txs in
            let semicolon_node = checkToken txs ";" in
            addChild production (addNextSibling comma_node (addNextSibling idList_node semicolon_node))
        )
    else Nil;;

let programSuffix txs =  (* <programSuffix> -> <programDataDecls> | <programFuncList> *)
    let production = Node(Nil, "<programSuffix>", Nil) in
    if (peekToken txs).v = ";" || (peekToken txs).v = ","
        then (
            let c1 = programDataDecls txs in
            addChild production c1
        )
        
    else if (peekToken txs).v = "("
        then (            
            let c1 = programFuncList txs in
            addChild production c1
        )
    else Nil;;

let programPrefix txs = (* <programPrefix> -> <typeName> <identifier> <programSuffix> | epsilon *)
    let production = Node(Nil, "<programPrefix>", Nil) in
        if (peekToken txs).v = "void" || (peekToken txs).v = "int" then 
        (
            let typeName_node = typeName txs in
            let identifier_node = identifier txs in
            let programSuffix_node = programSuffix txs in
            addChild production (addNextSibling typeName_node (addNextSibling identifier_node programSuffix_node))
        )
    else addChild production (Node(Nil, "<epsilon>", Nil));;

let program txs = (*<program> -> <programPrefix> <programPrefix>*)
  let production = Node(Nil, "<program>", Nil) in
  let pp1 = programPrefix txs in
  let pp2 = programPrefix txs in
  addChild production (addNextSibling pp1 pp2);;


let ran production tokens =
    let result = production tokens in
    (result, peekToken tokens) ;;

let isParsingSuccessful f txs =
    let parse = f txs in
    let endToken = (peekToken txs).t = End in
    parse && endToken;;





(*
=================================================================================
======================= SCANNER BELOW THIS LINE =================================
=================================================================================
*)


let read_file file =
  let ic = open_in file in
  let buf = Buffer.create (in_channel_length ic) in
  try
    while true do
      let line = input_line ic in
      Buffer.add_string buf line;
      Buffer.add_char buf '\n';
    done; assert false
  with End_of_file ->
    Buffer.contents buf
;;

 (*let rec print_list lst= match lst with
   | [] -> ()
   | e::l -> Printf.printf "%s " e.t ; Printf.printf "%s\n" e.v ; print_list l ;;*)

 let is_alpha alpha = match alpha with 
  | 'a'|'b'|'c'|'d'|'e'|'f'|'g'|'h'|'i'|'j'|'k'|'l'|'m'|'n'|'o'|'p'|'q'|'r'|'s'|'t'|'u'|'v'|'w'|'x'|'y'|'z' -> true
  | 'A'|'B'|'C'|'D'|'E'|'F'|'G'|'H'|'I'|'J'|'K'|'L'|'M'|'N'|'O'|'P'|'Q'|'R'|'S'|'T'|'U'|'V'|'W'|'X'|'Y'|'Z' -> true    
  | _ -> false;;

let is_digit digit = match digit with
  |'0'|'1'|'2'|'3'|'4'|'5'|'6'|'7'|'8'|'9' -> true
  | _ -> false;; 
  
 let prefix_char s c = String.make 1 c ^ s


 let to_ch_list (s:string) : char list =
   let rec tol i l = 
     if i < 0 
       then l else tol (i-1) (s.[i] :: l) in
   tol (String.length s - 1) [];;


 let to_stri (l:char list) : string =
   let res = Bytes.create (List.length l) in
   let rec toc i l =
     match l with
     | [] -> Bytes.to_string res
     | c :: l -> Bytes.set res i c; toc (i - 1) l in
   toc ((List.length l)-1) l;;


 let analysis (mystr:string) : token list =

   let get_id str =
     let rec result tk chh =
         match chh with
         | c :: rmlist when ((is_alpha c) || (c = '_')|| (is_digit c))
             -> result (c :: tk) rmlist
         | _ -> (to_stri (tk), chh) in
     result [] str in

   let get_int str =
     let rec result tk chh =
         match chh with
         | c :: rmlist when (is_digit c)
             -> result (c :: tk) rmlist
         | _ -> (to_stri (tk), chh) in
     result [] str in

 let get_string str =
     let rec result tk chh =
         match chh with
         | c :: rmlist ->
           match c with
           | '"' -> (prefix_char (to_stri ('"'::tk)) '"', rmlist)
           | _ -> result (c::tk) rmlist in
     result [] str in

   let get_equal str =
     let rec result tk chh =
         match chh with
         | c :: rmlist when ((c = '='))
             -> result (c :: tk) rmlist
         | _ -> (to_stri (tk), chh) in
     result [] str in

   let get_condition str =
     let rec result tk chh =
         match chh with
         | c :: rmlist when ((c = '&') || (c = '|'))
             -> result (c :: tk) rmlist
         | _ -> (to_stri (tk), chh) in
     result [] str in

   let get_num str =
     let (tk, rmlist) = get_int str in
     match rmlist with
     | '.' :: c :: r when (is_digit c)
         -> let (tk2, rmlist2) = get_int (c :: r) in
            ((tk ^ "." ^ tk2), rmlist2)
     | _ -> (tk, rmlist) in

   let rec get_error tk str =
     match str with
     | [] -> (to_stri ( tk), str)
     | c :: rmlist ->
         match c with
         | '+' | '-' | '*' | '/' | '(' | ')' | '_'
         | '<' | '>' | '=' | 'a'..'z' | 'A'..'Z' | '0'..'9'
             -> (to_stri ( tk), str)
         | _ -> get_error (c :: tk) rmlist in

   let rec skip_space str =
     match str with
     | [] -> []
     | c :: rmlist -> if (c = ' ' || c = '\n' || c = '\t' || c = '\r')
                       then skip_space rmlist else str in

   let rec skip_comment str =
     match str with
     | [] -> []
     | c :: rmlist -> if (c != '\n')
                       then skip_comment rmlist else str in

   let rec skip_meta str =
     match str with
     | [] -> []
     | c :: rmlist -> if (c != '\n')
                       then skip_meta rmlist else str in

   let rec maketk tkk str =
     match str with
     | []                 -> (tkk, [])
     | '\n' :: rmlist
     | '\r' :: rmlist
     | '\t' :: rmlist
     | ' ' :: rmlist        -> maketk tkk (skip_space str)
     | '/' :: '/' :: rmlist    -> maketk tkk (skip_comment str)
     | '#' :: rmlist        -> maketk tkk (skip_meta str)

     | '<' :: '=' :: rmlist         -> maketk ("<=" :: tkk) rmlist
     | '<' :: rmlist        -> maketk ("<"  :: tkk) rmlist
     | '>' :: '=' :: rmlist         -> maketk (">=" :: tkk) rmlist
     | '>' :: rmlist        -> maketk (">"  :: tkk) rmlist
     | '!' :: '=' :: rmlist    -> maketk ("!=" :: tkk) rmlist

     | '-' :: rmlist        -> maketk ("-"  :: tkk) rmlist
     | '+' :: rmlist        -> maketk ("+"  :: tkk) rmlist
     | '/' :: rmlist        -> maketk ("/"  :: tkk) rmlist
     | '*' :: rmlist        -> maketk ("*"  :: tkk) rmlist
     | '(' :: rmlist        -> maketk ("("  :: tkk) rmlist
     | ')' :: rmlist        -> maketk (")"  :: tkk) rmlist
     | '{' :: rmlist        -> maketk ("{"  :: tkk) rmlist
     | '}' :: rmlist        -> maketk ("}"  :: tkk) rmlist
     | '[' :: rmlist        -> maketk ("["  :: tkk) rmlist
     | ']' :: rmlist        -> maketk ("]"  :: tkk) rmlist
     | ',' :: rmlist        -> maketk (","  :: tkk) rmlist
     | ';' :: rmlist        -> maketk (";"  :: tkk) rmlist


     | h :: t -> match h with
            | '0'..'9' -> let (t, rmlist) = get_num str in
                          maketk (t :: tkk) rmlist
            | 'a'..'z'
            | 'A'..'Z' 
            | '_'      -> let (t, rmlist) = get_id str in
                          maketk (t :: tkk) rmlist
            | '='      -> let (t, rmlist) = get_equal str in
                          maketk (t :: tkk) rmlist
            | '"'      -> let (t, rmlist) = get_string t in
                          maketk (t :: tkk) rmlist
            | '&'      -> let (t, rmlist) = get_condition str in
                          maketk (t :: tkk) rmlist
            | '|'      -> let (t, rmlist) = get_condition str in
                          maketk (t :: tkk) rmlist
            | c        -> let (t, rmlist) = get_error [c] t in
                          maketk (t :: tkk) rmlist in

   let (tkk, _) = (maketk [] (to_ch_list mystr)) in
   let categorize tk =
     match tk with
     | "+" 
     | "-"  
     | "*"  
     | "/"  
     | "("  
     | ")"  
     | "{" 
     | "}" 
     | "=" 
     | "<" 
     | "<=" 
     | ">"  
     | ">=" 
     | "==" 
     | "," 
     | ";" 
     | "!="
     | "["
     | "]"
     | "&"
     | "|"
     | "&&"
     | "||"
         -> {t = Symbol; v=tk}
     | "int" 
     | "void" 
     | "if"
     | "else"
     | "while" 
     | "return" 
     | "continue" 
     | "break" 
     | "scanf" 
     | "printf" 
        -> { t = Reserved; v=tk}
     | _ -> match tk.[0] with
            | '0'..'9' -> {t = Number; v=tk}
            | 'a'..'z'
            | 'A'..'Z' | '_' -> {t = Identifier; v=tk}
            | '"' -> {t = String; v=tk} in

   List.map categorize (tkk);;


 let file = Sys.argv.(1);;
 let str = read_file file;;
 let result = analysis str;;
 let result_reverse = List.rev result;;
 
 let suffix_char s c = s ^ String.make 1 c

 let meta (mystr: string) : string =
   let value = ref ""
   and index = ref 0 in
   while !index < (String.length mystr) do
     let ch = String.get mystr !index in
     if ch = '#' then (
      let chh = ref (String.get mystr !index) in
      value:= suffix_char !value '\n';
        try
        while ( !chh != '\n' ) do
            value:= suffix_char !value !chh;
            index:= !index+1;
            chh:=String.get mystr !index;
            if !index >= String.length mystr then raise Exit;
            chh:=String.get mystr !index;
        done;
        with Exit->();
     ) else (
       index := !index+1;
     )
   done;
   !value
;;

(*
=================================================================================
======================= Translator BELOW THIS LINE =================================
=================================================================================
*)



let rec treeToString root =
    match root with
    | Nil -> "Nil"
    | Node(lmc, data, rs) -> String.concat (String.concat data [(String.concat "" [(treeToString lmc); ","]); (String.concat "" [ "," ; (treeToString rs)])]) ["Node(" ; ")"];;

(*<term> -> <factor> <mulTerm> *)



(* <commaExp> -> , <nonEmptyExprList> | epsilon *)
(* <nonEmptyExprList> -> <expression> <commaExp> *)
 (* <exprList> -> <nonEmptyExprList> | epsilon *)
(*<addExp> -> <addOp> <expression> | epsilon *)

(*<expression> -> <term> <addExp> *)

(* <generalFuncCall> -> ( <exprList> ) ; *)
(* <assignmentOrGeneralFuncCallSuffix> -> [ <identifier> ] <assignment> | <assignment> | <generalFuncCall> *)


(*  = <expression> ; *) 



let rec getExpression t = 
    match t with 
        | Nil -> ""
        | Node (l, d, r) ->
            if d = "<term>" then(
                let c1 = String.concat ""["local[";(string_of_int !local_count); " ] "] in 
                local_count := !local_count +1;
                let c2 = getTerm l in
                let c3 = addExp (childOf r) c2 in
                if c3 = "" 
                    then 
                    (
                        c2 (*just return term local var*)
                    ) 
                else (*combine term and addExp into a single var then return new memory location*)
                (
                    c3
(*                     let c5 = String.concat ""[c2 ; c3] in
                    let c7 = String.concat ""[" = "; c5] in
                    let c8 = String.concat ""[c1 ; c7] in
                    let c9 = String.concat ""[c8 ; ";"]in 
                    codeAdd c9;
                    c1 *)
                )
            )
            else(
                ""
            )
        
and addExp t v =
    match t with 
        | Nil -> ""
        | Node (l, d, r) ->
            (* Printf.printf "addExp %s" d; *)
            if d = "<addOp>" then(
                
                let c1 = String.concat ""["local[";(string_of_int !local_count); " ] "] in 
                local_count := !local_count +1;
                let c2 =  getData l in
                let c3 = getTerm (childOf (childOf r)) in
                let c4 = String.concat ""[c1 ;" = ";v;" ";c2 ;" "; c3;";" ] in
                codeAdd c4;
                let c5 = addExp (childOf(siblingOf(childOf r))) c1 in
                c5
            )
            else(
                v
            )


 (*<term> -> <factor> <mulTerm> *)
and getTerm t =
    match t with 
        | Nil -> ""
        | Node (l, d, r) ->
            if d = "<factor>" then(
                let c1 = String.concat ""["local[";(string_of_int !local_count); " ] "] in 
                local_count := !local_count +1;
                let c2 = getFactor l in
                let c3 = getmulTerm (childOf r) in
                let c4 = String.concat ""[c2 ; c3] in
                let c5 = String.concat  ""[" = "; c4] in
                let c6 = String.concat ""[c1 ; c5] in
                let c7 = String.concat ""[c6; " ;"] in 
                codeAdd c7;
                c1
            )
            else(
                ""
            )
(*<mulTerm> -> <mulOp> <term> | epsilon*)
and getmulTerm t =
    match t with
        | Nil -> ""
        | Node (l, d, r) ->
            if d = "<mulOp>" then(
                let c1 = getData l in
                let c2 = getTerm (childOf r) in 
                String.concat ""[c1 ; c2]

            )
            else(
                ""
            )
(*<factor> -> <identifier><factorSuffix> | <number> | -<number> | (<expression>) *)
and getFactor t =
    match t with 
        | Nil -> ""
        | Node (l, d, r) ->
            if d = "<identifier>"then(
                if (Hashtbl.mem globalData (getData l)) then(
                    let c2 = Hashtbl.find globalData (getData l)in
                    let c3 = String.concat ""["global[" ; c2; " ]" ]in
                    let c4 = getFactorSuff (childOf r) in 
                    String.concat ""[c3; c4]
                )
                else if (Hashtbl.mem localData (getData l))then(
                    let c2 = Hashtbl.find localData (getData l) in 
                    let c3 = String.concat ""["local[" ; c2; " ]  " ]in
                    let c4 = getFactorSuff (childOf r) in 
                    String.concat ""[c3 ; c4]
                )
                else (
                    let c1 = (getData l) in
                    let c2 = getFactorSuff (childOf r) in 
                    String.concat ""[c1 ; c2]

                )
            )
            else if d = "<number>"then(
                let c1 = String.concat ""["local[";(string_of_int !local_count); " ] "] in 
                local_count := !local_count +1;
                let c2 = String.concat "" [ " = "; (getData l)] in
                let c3 = String.concat ""[c1;c2 ;"; "] in
                codeAdd c3;
                c1
            )
            else if d = "-"then(
                let c1 = String.concat ""["local[";(string_of_int !local_count); " ] "] in 
                local_count := !local_count +1;
                let c2 = String.concat ""[" = - " ;(getData (childOf r))] in
                let c3 = String.concat ""[c1;c2 ;"; "] in
                codeAdd c3;
                c1

            )
            else if d = "("then(
                let c2 = getExpression (childOf r) in
                let c4 = String.concat ""["("; c2 ; ")"] in 
                c4
            )
            else ""
        

(*<factorSuffix> -> [<expression>] | (<exprList>) | epsilon *)
and getFactorSuff t =
    match t with 
        | Nil -> ""
        | Node (l, d, r) ->
            if d = "("then(
                let c2 = getExprList (childOf r) in
                let c3 = String.concat ""["(";c2 ;")"] in
                c3
            )
            else ""
and getExprList t = (* <exprList> -> <nonEmptyExprList> | epsilon *)
    match t with 
            | Nil -> "" 
            | Node (l, d, r) ->
                if d = "<nonEmptyExprList>"then(
                    let c1 = getNonExprList l in    
                    let c2 = getComa (childOf (siblingOf l)) in
                    let c3 = String.concat ""[c1 ; c2]in
                    c3

                )
                else ( "")
and getNonExprList t = 
    match t with 
            | Nil -> ""
            | Node (l, d, r) ->
             if d = "<expression>"then(
                    let c1 = getExpression (l) in 
                    let c2 = getComa (childOf (siblingOf l)) in
                    let c3 = String.concat ""[c1 ; c2]in
                    c3
                )
            else""



(* nonEmptyExprList txs =  (* <nonEmptyExprList> -> <expression> <commaExp> *)
    let production = Node(Nil, "<nonEmptyExprList>", Nil) in
    let expression_node = expression txs in
    let commaExp_node = commaExp txs in
    addChild production (addNextSibling expression_node commaExp_node)
and
commaExp txs=  (* <commaExp> -> , <nonEmptyExprList> | epsilon *)
    let production = Node(Nil, "<commaExp>", Nil) in
    if (peekToken txs).v = ","
        then
        (
            let comma_node = checkToken txs "," in
            let nonEmptyExprList_node = nonEmptyExprList txs in
            addChild production (addNextSibling comma_node nonEmptyExprList_node)
        )
    else addChild production (Node(Nil, "<epsilon>", Nil))
and 
exprList txs =  (* <exprList> -> <nonEmptyExprList> | epsilon *) *)


and getComa t =  (*<nonEmptyListSuffix> -> , <nonEmptyList> | epsilon*)
    match t with 
            | Nil -> ""
            | Node (l, d, r) ->
                if d = ","then(
                    let c1 = "," in 
                    let c2 = getNonExprList(childOf r) in
                    let c3 = String.concat ""[c1 ; c2] in
                    c3


                )
                else ""

 and aOGenFCallSuff t =
        match t with 
        | Nil -> ""
        | Node (l, d, r) ->
            if d = "<assignment>" then(
                let c1 = getExpression (childOf (siblingOf l)) in
                let c2 = String.concat ""["=" ; c1 ; ";"] in
                c2
            )
            else if d = "<generalFuncCall>" then(
                let c1 = getExprList (siblingOf l) in
                let c2 = String.concat ""["(" ; c1 ; ") ;"] in
                c2
            )
            else ""
;;




let getGlobals o =
    let rec traverse t = 
        match t with 
            | Nil -> ()
            | Node (l, d, r) ->
                if d = "<funcSuffix>" || d = ";" then(
                    if !globalBool = 1 then(
                        Printf.printf "\n int global[%d]; \n" !globalCounter;
                        globalBool := 2;
                    )
                    else 
                    (
                        globalBool := 2;
                        globalCounter := 0;
                        Hashtbl.reset globalData;
                    )                 
                    
                )
                else(
                    if d = "<programDataDecls>" then(
                        globalBool := 1;
                    );
                    if d = "<identifier>" then(
                        let id = (getData l) in
                        Hashtbl.add globalData id (string_of_int !globalCounter);
                        globalCounter := !globalCounter+1;
                    )
                    else
                        if !globalBool != 2 then(
                            traverse l
                        );
                        if !globalBool != 2 then(
                            traverse r
                        )
                        
                )    
    in
    traverse o










let rec getStatements t = 
        match t with
            | Nil -> ()
            | Node (l, d, r) ->
                if d = "<statement>" then(
                    getStatements (l);
                    getStatements( childOf r);


                    (* <statements> -> epsilon | <statement> <statements> *)
                )
                else if d = "<epsilon>" then(
                    
                )
                (*<assignmentOrGeneralFuncCall> | <printFuncCall> | <scanfFuncCall> | <ifStatement> | <whileStatement> | <returnStatement> | <breakStatement> | <continueStatement> *)
                else if d =  "<assignmentOrGeneralFuncCall>"  then(
                    if (getData l) = "<identifier>" then(
                        if (getData (childOf l)) = "read" || (getData (childOf l)) = "write" then 
                        (
                            let c1 = (getData (childOf l)) in 
                            let c2 = (getFactor(childOf(childOf(childOf(childOf(childOf(siblingOf(childOf(childOf(siblingOf l)))))))))) in
                            (* let c3 = (getData (childOf(siblingOf(childOf(childOf(siblingOf l)))))) in *)
                            codeAdd (String.concat "" [c1; "(";c2; ");"])
                        )


                        else if (Hashtbl.mem globalData (getData (childOf l))) then(
                            let c2 = Hashtbl.find globalData (getData (childOf l))in
                            let c3 = String.concat ""["global[" ; c2; "]" ]in
                            let c4 = aOGenFCallSuff (childOf(siblingOf l)) in  
                            let c5 = String.concat ""[c3 ; c4] in 
                            codeAdd c5
                        )
                        else if (Hashtbl.mem localData (getData (childOf l)))then(
                            let c2 = Hashtbl.find localData (getData (childOf l)) in 
                            let c3 = String.concat ""["local[" ; c2; "]" ]in
                            let c4 = aOGenFCallSuff (childOf(siblingOf l)) in  
                            let c4 = String.concat ""[c3 ; c4] in
                            codeAdd c4
                        )
                        else (
                            let c2 = (getData (childOf l)) in 
                            let c3 = aOGenFCallSuff (childOf(siblingOf l)) in  
                            let c4 = String.concat ""[c2 ; c3] in
                            codeAdd c4
                         )
                    )
                    else (

                    )

                     (* -> <identifier> <assignmentOrGeneralFuncCallSuffix> *)
                    
                )
                else if d =  "<printFuncCall>"  then(
                    
                    let c2 = printfStatement l in
                    codeAdd c2 

                )
                else if d =  "<scanf>"  then(
                    codeAdd (scanfStatement l)
(* <scanfFuncCall> -> scanf ( <string> , & <expression> ) ; *)
                    
                )
                else if d =  "<ifStatement>" then(
                    codeAdd (ifStatement0 l)



                )
                else if d =  "<whileStatement>"  then(
                    codeAdd (whileStatement0 l)
                     (* <whileStatement> -> while ( <conditionExpression> ) <blockStatements> *)
                )
                else if d =  "<returnStatement>"  then(
                    codeAdd (returnStatement0 l)
                    
                )
                else if d =  "<breakStatement>"  then(
                    codeAdd (break0 l)

                )
                else if d =  "<continueStatement>" then (
                    codeAdd(continue0 l)

                )
                else(

                )
and printfStatement t =
        match t with 
            | Nil -> ""
            | Node (l, d, r) ->
                if (getData(siblingOf (siblingOf r)))  = "<printFuncCallWithExpression>" then(
                    let c1 = "printf (" in
                    let c2 = (getData (childOf (siblingOf r))) in
                    let c3 = printfExpr (childOf(siblingOf (siblingOf r))) in 
                    let c4 = " );"in
                    let c5 = String.concat ""[c1 ; c2; c3 ; c4] in
                    c5

                    )
                    
                    
                    (* <printfFuncCall> -> printf ( <string> <printFuncCallWithExpression> ) ; *)
                    (* <printFuncCallWithExpression> -> epsilon | , <expression> *)
                
                else(
                    ""

                )
(*
                    let localLabelRun =  String.concat ""["L_" ;(string_of_int !label_count)]in
                    contCounter := !label_count; 
                    label_count := !label_count +1;
                    let breakLabel = String.concat ""["L_" ;(string_of_int !label_count)]in 
*)
and break0  t = 
    match t with 
                | Nil -> ""
                | Node (l, d, r) ->
                 if d = "break" then(
                    let c1 = !breakCounter in
                    let c2 = String.concat ""["goto L_" ;(string_of_int c1); ";"]in
                    c2
                 )                
                else(
                    ""

                )
and continue0   t = 
    match t with 
                | Nil -> ""
                | Node (l, d, r) ->
                 if d = "continue" then(
                    let c1 = !contCounter in
                    let c2 = String.concat ""["goto L_" ;(string_of_int c1) ; ";"]in
                    c2



                 )                
                else(
                    ""

                )

(* <scanfFuncCall> -> scanf ( <string> , & <expression> ) ; *)
and scanfStatement t = 
        match t with 
            | Nil -> ""
            | Node (l, d, r) ->
               (*  Printf.printf("gucciGang"); *)
                if d = "scanf" then(
                    let c1 = "scanf(" in
                    let c2 = (getData (childOf (siblingOf r))) in
                    let c3 = ", &" in
                    let c4 = getExpression (childOf(siblingOf(siblingOf(siblingOf (siblingOf r))))) in 
                    let c5 = " );"in
                    let c6 = (String.concat ""[c1 ; c2; c3 ; c4 ; c5] )in
                    c6

                    )
                    
                    
                    (* <printfFuncCall> -> printf ( <string> <printFuncCallWithExpression> ) ; *)
                    (* <printFuncCallWithExpression> -> epsilon | , <expression> *)
                
                else(
                    ""

                )


 (* <returnStatement> -> return  <returnStatementSuffix> ; *)
    (* <returnStatementSuffix> -> <expression> | epsilon *)
and returnStatementSuffix0 t = 
        match t with 
            | Nil -> ""
            | Node (l, d, r) -> 
                if d = "<expression>" then(
                    let c1 = getExpression l in 
                    c1
                )
            else""


and returnStatement0 t = 
        match t with 
            | Nil -> ""
            | Node (l, d, r) -> 
                if d = "return" then(
                    let c1 = "return " in
                    let c2 = returnStatementSuffix0 (childOf r)in
                    let c3 = String.concat ""[c1 ; c2; ";"]in 
                    c3
                )
            else""


(* <elseStatement> -> epsilon |  else <blockStatements> *)
(* <comparisonOp> -> == | != | > | >= | < | <= *)
 (* <conditionOp> -> && | || *)

and whileStatement0 t = 
 (* <whileStatement> -> while ( <conditionExpression> ) <blockStatements> *)
    match t with 
            | Nil -> ""
            | Node (l, d, r) -> 
                if d = "while" then(
                    let localLabelCheck =  String.concat ""["L_" ;(string_of_int !label_count)]in
                    let prevCont = !contCounter in
                    contCounter := !label_count;
                    label_count := !label_count +1;
                    let localLabelRun =  String.concat ""["L_" ;(string_of_int !label_count)]in
                    label_count := !label_count +1;
                    let breakLabel = String.concat ""["L_" ;(string_of_int !label_count)]in 
                    let prevBreak = !breakCounter in
                    breakCounter := !label_count;
                    label_count := !label_count +1;
                    let goCheck = String.concat ""["goto ";localLabelCheck;";"]in
                    let defRun = String.concat ""["";localLabelRun;":;"]in
                    codeAdd goCheck;
                    codeAdd defRun;
                    let block = blockStatement0 (childOf (siblingOf(siblingOf(siblingOf r))))in
                    let defCheck = String.concat ""["";localLabelCheck;":;"]in
                    codeAdd defCheck;
                    let c1 = "if(" in
                    let c2 = condExpr (childOf (siblingOf r))in
                    let c3 = ")" in
                    let c4 = String.concat ""[c1; c2; c3;"goto ";localLabelRun;";"]in
                    let defBreak = String.concat ""["";breakLabel;":;"]in
                    contCounter := prevCont;
                    breakCounter := prevBreak;
                    codeAdd c4;
                    codeAdd defBreak;

                
                    ""
                )
            else""

and condExprSuff t = 
(* <conditionExpressionSuffix> -> <conditionOp> <condition> | epsilon *)
    match t with 
        | Nil -> ""
        | Node (l, d, r) -> 
            if d = "<conditionOp>" then(
                let c1 = (getData l) in 
                let c2 = (cond0 (childOf r)) in 
                String.concat ""[c1 ;c2 ]
            )
        else""

and cond0 t = 
(* <condition> -> <expression> <comparisonOp> <expression> *)
    match t with 
        | Nil -> ""
        | Node (l, d, r) -> 
            if d = "<expression>" then(
                let c1 = getExpression l in 
                let c2 = (getData (childOf r)) in 
                let c3 = getExpression (childOf (siblingOf r))in
                String.concat ""[c1 ;c2 ; c3]
            )
        else""

and condExpr t = 
(* <conditionExpression> -> <condition> <conditionExpressionSuffix> *)
    match t with 
                | Nil -> ""
                | Node (l, d, r) -> 
                    if d = "<condition>" then(
                        let c1 = cond0 l in 
                        let c2 = condExprSuff (childOf r) in 
                        String.concat ""[c1 ;c2]
                    )
                else""


and blockStatement0 t = 
(* <blockStatements> -> { <statements> } *)
        match t with 
            | Nil -> ""
            | Node (l, d, r) -> 
                if d = "{" then(
                    getStatements (childOf r); 
                    ""
                )
            else""


and  elseStatement0 t = 
        match t with 
            | Nil -> ""
            | Node (l, d, r) -> 
                if d = "else" then(
                    blockStatement0 (childOf r);
                    ""
                    
                )
            else""


and  ifStatement0 t = 
        match t with 
            | Nil -> ""
            | Node (l, d, r) -> 
                if d = "if" then(
                    let localLabelCheck =  String.concat ""["L_" ;(string_of_int !label_count)]in 
                    label_count := !label_count +1;
                    let localLabelRun =  String.concat ""["L_" ;(string_of_int !label_count)]in 
                    label_count := !label_count +1;
                    let c4 = "if( " in
                    let c5 = condExpr (childOf (siblingOf r)) in
                    let c6 = " )" in
                    let c0 = String.concat ""[c4; c5; c6;"goto ";localLabelRun;";"]in
                    let c1 = String.concat ""["goto ";localLabelCheck;";"]in
                    let c2 = String.concat ""["";localLabelRun;":;"]in
                    codeAdd c0;
                    codeAdd c1;
                    codeAdd c2;
                    let c3 = blockStatement0 (childOf (siblingOf(siblingOf(siblingOf r))))in
                    let c7 = String.concat ""["";localLabelCheck;":;"]in
                    let c8 = elseStatement0 (childOf (siblingOf(siblingOf(siblingOf(siblingOf r)))))in
                    codeAdd c3;
                    codeAdd c7;
                    codeAdd c8;
                    ""
                )
            else""
and printfExpr t = 
        match t with 
                | Nil -> ""
                | Node (l, d, r) ->
                    if d  = "," then(
                        let c1 = ", " in
                        let c2 = (getExpression (childOf r)) in
                        let c3 = String.concat ""[c1 ; c2] in
                        c3
                    )
                    else(
                        ""

                    )
;;


    


let locDataDec o = 
    let rec traverse t = 
        match t with 
            | Nil -> ()
            | Node (l, d, r) -> 
                if d = "<identifier>" then(
                    let id = (getData l) in
                    Hashtbl.add localData id  (string_of_int !local_count);
                    local_count := !local_count+1;



                );
                if d = "<epsilon>" then(

                )
                else(
                    traverse l;
                    traverse r
                )            
    in
    traverse o
(* <funcList> -> epsilon | <func> <funcList> *)
(*<func> -> <funcDecl> <funcSuffix>*)
(*<funcDecl> -> <typeName> <identifier> ( <parameterList> )*)
(* <funcSuffix> -> ;  | { <dataDecls> <statements> } *)
(* <dataDecls> -> epsilon | <typeName> <idList> ; <dataDecls> *)


let getFuncSuff o =
    let rec traverse t = 
        match t with 
            | Nil -> ()
            | Node (l, d, r) ->
                if d = "<dataDecls>" then(
                    locDataDec l;
                    getStatements (childOf r);
                    Printf.printf "\nint local[%d]; \n" !local_count;
                    print_list !funcCode;
                    funcCode := []  ;
                    Hashtbl.reset localData;
                    local_count := 0;
                    Printf.printf "} \n";
                )
                else(
                    traverse l;
                    traverse r
                )

    in
    traverse o



let getFuncList o =
    let rec traverse t = 
        match t with 
            | Nil -> ()
            | Node (l, d, r) ->
                if codeCheck d then(
                    Printf.printf "%s " d;
                );
                if d = "<funcSuffix>" then(
                    Printf.printf "%s \n" (getData l);
                    getFuncSuff l;
                    traverse (childOf r);
                    

                ) 
                else(
                    traverse l;
                    traverse r
                )

    in
    traverse o

let strr = meta str;;
Printf.printf "%s" strr;;
Printf.printf "%c" '\n';;
List.map addToken result_reverse;;

(* Printf.printf "Tokens before %d\n" (Queue.length tokens);; *)
let output = program tokens;;
(* Printf.printf "Program output: %b\n" (if output = Nil then false else true);; *)
(* Printf.printf "Tokens after %d\n" (Queue.length tokens);; *)
(*  Printf.printf "%s\n" (treeToString output);;  *)
(* print_string (treeToString output);; *)
(* print_to_standard_output output;;*)





getGlobals output;;


if (!globalCounter) > 0 then(
    getFuncList (siblingOf (childOf output));
)
else getFuncList output;
(* 
Hashtbl.iter (fun x y -> Printf.printf "%s -> %s\n" x y) globalData;;
Hashtbl.iter (fun x y -> Printf.printf "%s -> %s\n" x y) localData;;
 *)



 


