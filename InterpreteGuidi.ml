(*
*	Nome:Elena			*
*	Cognome:Guidi	 	*
*	Matricola:537336	*
*	Corso:A				*
*)

(*Tipi*)
type ide = string;;

type exp = 
	  Eint of int 							(* Interi *)
	| Ebool of bool 						(* Booleani *)
	| Den of ide 							(* Identificatori *)
	| Prod of exp * exp 					(* Prodotto di interi*)
	| Sum of exp * exp						(* Somma di interi*)
	| Diff of exp * exp 					(* Differenza di interi*)
	| Eq of exp * exp 						(* Booleano indentifica se due interi sono uguali*)
	| Minus of exp 							(* Opposto di un intero*)
	| IsZero of exp 						(* Booleano indentifica se un int è zero*)
	| Or of exp * exp						(* Or logico *)
	| And of exp * exp 						(* And logico *)
	| Not of exp 							(* Not logico *)
	| Ifthenelse of exp * exp * exp 		(* Condizione if *)
    | Fun of ide * exp                      (* Dichiarazione di funzione*)
	| Let of ide * exp * exp 				(* Dichiarazione di Identificatore : modifica ambiente *)
	
	(*estensione alberi binari di espressioni*)
	
	| ETree of tree                     	(* Gli alberi sono anche espressioni *)
	| Appl of exp * exp
	| ApplyOver of exp * exp            	(* Applicazione di funzione ai nodi *)
	(* Applicare la funzione denotata dal primo parametro al valore associato 
	a ogni nodo dell’albero denotato dal secondo parametro*)
	| Update of (ide list) * exp * exp	(* Aggiornamento di un nodo *)
	(* Aggiorna	solo il	valore del	nodo (o	dei	nodi) identificati dal cammino (1 parametro) nell’albero
	applicando la funzione (2 parametro),non esegue nulla se nessun	 nodo  corrisponde al cammino*)
	| Select of (ide list) * exp * exp	(* Selezione condizionale di un nodo *)
	(* Restituisce un sotto-albero dell'albero input (3 parametro) la cui radice è uno dei nodi dell'albero che	
	sono individuati dal cammino	(1 parametro) e il cui valoresoddisfa la proprietà definita	dalla funzione (2 parametro)*)
		
and tree = 									(* Albero*)
    | Empty                             	(* Albero vuoto *)
    | Node of ide * exp * tree * tree 		(* Albero binario *)
			
and evT =									(* Tipi di valori del risultato di un espressione *)
	  Int of int 							(* Interi *)
	| Bool of bool 							(* Booleani *)
	| Unbound 								(* Special value *)
	| VTree of vtree     					(* Albero valutato*)
	| VFun of ide * exp * evT env			(* Funzione valutata: una tripla Parametro Codice Ambiente *)
	| RecVFun of ide*ide*exp*evT env		(* Funzione Ricorsiva valutata *)
	
and vtree =									(* Albero valutato*)
    | VEmpty                                (* Albero vuoto *)
    | VNode of ide * evT * vtree * vtree	(* Albero binario *)	

(*Ambiente, scoping statico -> permetto determinare tutti gli ambienti a compile time*)
and 't env = (ide * 't) list ;;				(* Ambiente: Una collezione di coppie Identificatore-Valore(bind)*)

let emptyenv : (evT env) = [("",Unbound)] ;;(* Ambiente Vuoto *)

let rec applyenv (x: evT env) (y: ide) = 	(* Ricerca nell'ambiente*)
	match x with
		| (i,v)::o when y = i -> v
		| [("",Unbound)] -> Unbound
		| x::o -> applyenv o y
		| [] -> failwith "Errore applyenv: Ambiente errato";;
		
let bind (r: evT env) (l: ide) (v: evT) = (l,v)::r;;	(* Inserimento nell'ambiente *)

(*Type checking dinamico -> da il risultato solo a runtime*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("Not a valid type");;
	
(*Type checking "ricorsivo" per alberi*)
let rec isTree t = match t with
	  ETree(Empty) -> true (*L'albero vuoto è un albero*)
	| ETree(Node(_,_, firstChild, secondChild)) -> (isTree(ETree(firstChild)) && isTree(ETree(secondChild))) 
	(*Controllo che ogni nodo sia a sua volta un albero binario*)
	| _ -> false ;;

(*Operazioni*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u)
		| _ ->  failwith "Error prod")
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u)
		| _ ->  failwith "Error sum")
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u)
		| _ ->  failwith "Error diff")
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u)
		| _ ->  failwith "Error eq")
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n)
	   	| _ ->  failwith "Error minus")
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0)
		| _ ->  failwith "Error iszero")
	else failwith("Type error");;
	
(*operazione usata nel or*)
let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e))
		| _ ->  failwith "Error vel")
	else failwith("Type error");;

(*operazione usata nel and*)
let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e)
		| _ ->  failwith "Error et")
	else failwith("Type error");;

(*operazione usata nel not*)
let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) 
		| Bool(false) -> Bool(true)
		| _ ->  failwith "Error non")
	else failwith("Type error");;
	
	
(*Interprete*)
let rec eval (e : exp) (r : evT env) = match e with

	(*Casi base*)
	| Eint n -> Int n 
	| Ebool b -> Bool b 
	| Den i -> applyenv r i 
	| Eq(a, b) -> eq (eval a r) (eval b r)
	
	(*Op con interi*)
	| Prod(a, b) -> prod (eval a r) (eval b r) 
	| Sum(a, b) -> sum (eval a r) (eval b r)|Diff(a, b) -> diff (eval a r) (eval b r)
	| Minus a -> minus (eval a r)
	
	(*Op con booleani*)
	| And(a, b) -> et (eval a r) (eval b r) 
	| Or(a, b) -> vel (eval a r) (eval b r) 
	| Not a -> non (eval a r) 
	
	(*Condizioni e valutazioni*)
	| IsZero a -> iszero (eval a r) 
	| Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("non boolean guard")
				
	(*Funzioni*)
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) (*Dichiarazione di Espressione. Valuto e1, aggiungo nell'ambiente i = e1, valuto e2*)
	| Fun(i, a) -> VFun(i, a, r)
	
	
	| Appl(f, eArg) -> let fclosure = (eval f r) in
	(*Applica nell'ambiente la funzione passata come primo argomento con gli argomenti passati come secondo paramento*)
		(match fclosure with
			VFun(arg, fbody, fDecEnv) -> (eval fbody (bind fDecEnv arg (eval eArg r))) |
			RecVFun(f, arg, fbody, fDecEnv) -> 
				let aVal = (eval eArg r) in
					let rEnv = (bind fDecEnv f fclosure) in
						let aEnv = (bind rEnv arg aVal) in
							(eval fbody aEnv) |
			_ -> failwith("non functional value"))
	| Appl(_,_) -> failwith("no function in apply")

	| ETree(x) -> if isTree(ETree(x)) = true then 	
            match ETree(x) with
            | ETree(Empty) -> VTree(VEmpty)
            | ETree(Node(tag, value, lchild, rchild)) -> VTree(
                VNode(tag,(eval value r),
                    (match (eval (ETree(lchild)) r) with
                        | VTree(x) -> x
                        | _ -> failwith "Error in Tree: Non Tree Node"
                    ),
                    (match (eval (ETree(rchild)) r) with 
                        | VTree(x) -> x
                        | _ -> failwith "Error in Tree: Non Tree Node"
                    )))
            | _ -> failwith "Invalid ETree"
		else failwith "Invalid ETree"
	
	(*Funzioni sugli alberi*)
	| ApplyOver(funzione, albero) -> 
		(*Controllo che l'albero in input sia effettivamente un albero*)
		if (isTree(albero)) then 
			let f = ( eval funzione r ) in
			(*Valuto la funzione input e controllo che sia una funzione ternaria*)
			match f with 
				| VFun(a, b, c) ->  (match ( eval albero r ) with
                                    | VTree(xr) -> VTree(apply_over_tree f xr) 
									(*Chiamo la funzione ausiliaria e passo la funzione e il cammino*)
                                    | _ -> failwith "Error ApplyOver: Invalid Type")		
				| _ -> failwith "Error ApplyOver: No function in Apply"
		
		else failwith("Input not a tree")
	
	| Update(cammino, funzione, albero)->  
		(*Controllo che l'albero in input sia effettivamente un albero*)
		if (isTree(albero)) then 
			let f = ( eval funzione r ) in
			(*Valuto la funzione input e controllo che sia una funzione ternaria*)
			match f with 
				| VFun(a, b, c) -> (match ( eval albero r ) with 
                                    | VTree(xr) -> VTree(update_tree cammino f xr)
									(*Chiamo la funzione ausiliaria e passo la funzione e il cammino*)
                                    | _ -> failwith "Error update: Invalid Type")						
				| _ -> failwith "Error update: No function in Apply"
		else failwith ("Input not a tree")
			
	| Select(cammino, funzione, albero)-> 
		(*Controllo che l'albero in input sia effettivamente un albero*)
		if (isTree(albero)) then 
			let f = ( eval funzione r ) in
			(*Valuto la funzione input e controllo che sia una funzione ternaria*)
			match f with 
				| VFun(a, b, c) -> (match ( eval albero r ) with 
                                    | VTree(xr) -> VTree(select_in_tree cammino f xr)
									(*Chiamo la funzione ausiliaria e passo la funzione e il cammino*)
                                    | _ -> failwith "Error select: Invalid Type")						
				| _ -> failwith "Error select: No function in Apply"
		else failwith ("Input not a tree")
	| _ -> failwith "Error in eval: Not supported expression"		
		
	
	
(*Operazioni sugli alberi*)
and apply_over_tree (f: evT) (t: vtree) =
	match t with
	 VEmpty -> VEmpty (*Albero input vuoto*)
	| VNode(tag, value, lchild, rchild) -> (
			match f with (*Controllo che f sia ternaria e valutata*)
			 VFun(a, b, c) -> VNode(tag, ( eval b ( bind c a value )), (apply_over_tree f lchild), (apply_over_tree f rchild) )	
			(*Applica la funzione al nodo passato come "radice" dell'albero e 
			 scorro l'albero e i due figli (non ancora valutati) si passano come "radice" alla chiamata di funzione*)
			| _ -> failwith "Errore apply_over_tree: No function can be applied"
		)
	|_ -> failwith("Error apply_over_tree: Type error")
	
	
and update_tree (ca: ide list)  (f: evT) (t: vtree) =
	match (ca, t) with
	  (_, VEmpty) -> VEmpty (*Cammino e albero input vuoti*)
	| ([], v) -> v (*Cammino input vuoto*)
	| (el::leftList, VNode(tag, value, lchild, rchild)) -> 
		if ( el=tag ) then
			VNode(tag,   
				(match f with (*Controllo che f sia ternaria e valutata*)
					  VFun(a, b, c) -> ( eval b ( bind c a value )) (*Aggiorno il value del nodo*)
					| _ -> failwith "Errore in update_tree: Wrong Type"
                 ), 
				(*Controllo il sottoalbero sinistro*)
				(match lchild with
				  VNode(tgl,_,_,_) -> (match leftList with
					  x::_ -> if ( x=tgl ) then update_tree leftList f lchild else lchild
					| [] -> lchild
					)
				| VEmpty -> VEmpty
				),
				(*Controllo il sottoalbero destro*)
				(match rchild with
				  VNode(tgr,_,_,_) -> 
					(match leftList with
					  x::_ -> if ( x=tgr ) then update_tree leftList f rchild else rchild
					| [] -> rchild
					)
				| VEmpty -> VEmpty
				)
			)
		else t
	| (_,_) -> failwith("Error update_tree: Type error")
	
and select_in_tree (ca: ide list)  (f: evT) (t: vtree) =
	match (ca,t) with
	  (_, VEmpty) -> VEmpty (*Cammino e albero input vuoti*)
	| ([], _) -> VEmpty (*Cammino input vuoto*)
	| (el::leftList, VNode(tag, value, lchild, rchild)) -> (
		match f with  (*Controllo che f sia ternaria e valutata*)
			| VFun(a, b, c) -> ( 
				match ( eval b ( bind c a value )) with
				| Bool(x) ->
				if((el = tag) && ( not x)) then
					(match ((lchild, rchild), leftList) with
					| ((VNode(kl,_,_,_),VNode(kr,_,_,_)),j::k::remaininglist) -> (*figlio dx, sx e almeno un elemento da valutare*)
						if kl = j then 
							let node = (select_in_tree leftList f lchild) in (*Assegnamo alla var node il risultato del select in ogni iterazione*)
								match node with (*Controlliamo se il risultato di select e' nullo*)
									| VEmpty -> (*Caso vuoto: iniziamo la ricorsivita' sul ramo destro*)
										if kr = k then (select_in_tree (k::remaininglist) f rchild)
										else VEmpty 
									| _ -> node (*Caso non vuoto: continuiamo la ricorsivita' sul ramo sinistro*)
						else if kr = j then (select_in_tree leftList f rchild)        
                        else VEmpty	
					| ((VEmpty,VNode(kr,_,_,_)),j::_) -> (*figlio sx e almeno un elemento da valutare*)
							if kr = j then (select_in_tree leftList f rchild)
							else VEmpty
					| ((VNode(kl,_,_,_),VEmpty),j::_) ->  (*figlio dx e almeno un elemento da valutare*)
							if kl = j then (select_in_tree leftList f rchild)
							else VEmpty
					| ((_,_),_) -> VEmpty (*altri casi*)
				)	
				else if ((el = tag) && x) then t
				else VEmpty				
				| _ -> failwith "Error in select_in_tree: Wrong Function"
			)
			| _ -> failwith "Error in select_in_tree: Wrong Type"
		)
	| (_,_) -> failwith "Error select_in_tree: Type error";;
	
	
	
(***************************************   TESTS   ***************************************)
	
	
(*test valutazione albero*)
let fourNodesTree = eval (
	(	ETree(
			Node( "root", Eint(100),Empty,
				Node( "rchildRoot" , Eint(50),
					Node("lchild", Eint(25), Empty, Empty),
					Node("rchild",Eint(25),Empty,Empty)
				)
			)
		)
	)
) emptyenv;;

(*test valutazione albero vuoto*)
let emptyTree = eval (ETree(Empty)) emptyenv;;

(*test uso ApplyOver*)
let allNodesWithSixAsValue = eval (
    Let("function", (Fun("x", Prod(Eint(3), Eint(2))) ), (*dichiaro una funzione da poter passare a ApplyOver*)
			(	ApplyOver( (*Applico la funzione funciton (3x2) a tutti i nodi del cammino denotato dal secondo argomento*)
					(Den("function")), 
					(ETree(		Node( "root", Eint(0), Empty,
									Node("rchildRoot",Eint(10),
										Node("lchild", Eint(20),Empty, Empty),
										Node("rchild", Eint(30),Empty, Empty)
									)
								)
						  )
					)
				)
			)
    ) 
) emptyenv;;

(*test uso Update*)
let radiceRchildRootLchildWithSixAsValue = eval (
    Let("function", (Fun("x", Prod(Eint(3), Eint(2))) ), (*dichiaro una funzione da poter passare a Update*)
			(	Update( (*Applico la funzione funciton (3x2) a tutti i nodi del cammino denotato dal primo argomento*)
					([("root"); ("rchildRoot"); ("lchild")]), (*cammino: root -> rchildRoot -> lchild*)
					(Den("function")),  
					(ETree(		Node( "root", Eint(10), Empty,
									Node("rchildRoot",Eint(10),
										Node("lchild", Eint(10),Empty, Empty),
										Node("rchild", Eint(10),Empty, Empty)
									)
								)
						  )
					)
				)
			)
    ) 
) emptyenv;;

(*test Update senza effetto*)
let updateNullEffect = eval (
    Let("function", (Fun("x", Prod(Eint(3), Eint(2))) ), (*dichiaro una funzione da poter passare a Update*)
			(	Update( (*Applico la funzione funciton (3x2) a tutti i nodi del cammino denotato dal primo argomento*)
					([("rchildRoot"); ("lchild")]), (*cammino: [root] ->rchildRoot -> lchild*)
					(*NB update non dovrebbe cambiare nessun valore dato che il cammino non inizia per il nodo radice*)
					(Den("function")),  
					(ETree(		Node( "root", Eint(10), Empty,
									Node("rchildRoot",Eint(10),
										Node("lchild", Eint(10),Empty, Empty),
										Node("rchild", Eint(10),Empty, Empty)
									)
								)
						  )
					)
				)
			)
    ) 
) emptyenv;;

(*test Update solo radice*)
let updateOnlyRoot = eval (
    Let("function", (Fun("x", Prod(Eint(3), Eint(2))) ), (*dichiaro una funzione da poter passare a Update*)
			(	Update( (*Applico la funzione funciton (3x2) a tutti i nodi del cammino denotato dal primo argomento*)
					([("root"); ("lchild")]), (*cammino: root -> [rchildRoot] -> lchild*)
					(*NB update dovrebbe cambiare solo il nodo radice poiche' non c'è un cammino diretto che porti a lchild*)
					(Den("function")),  
					(ETree(		Node( "root", Eint(10), Empty,
									Node("rchildRoot",Eint(10),
										Node("lchild", Eint(10),Empty, Empty),
										Node("rchild", Eint(10),Empty, Empty)
									)
								)
						  )
					)
				)
			)
    ) 
) emptyenv;;


(*test uso Select*)
let subtreeRchild = eval (
    Let("function", (Fun("x", IsZero(Den("x"))) ), (*dichiaro una funzione da poter passare a Select NB deve restituire un booleano*)
			(	Select( 
					([("root"); ("rchildRoot"); ("lchild"); ("rchild")]),
					(Den("function")),  
					(ETree(		Node( "root", Eint(10), Empty,
									Node("rchildRoot",Eint(10),
										Node("lchild", Eint(10),Empty, Empty),
										Node("rchild", Eint(0),Empty, Empty)
									)
								)
						  )
					)
				)
			)
		)
) emptyenv;;

(*test Select di tutto l'albero*)
let allTree = eval (
    Let("function", (Fun("x", IsZero(Den("x"))) ), (*dichiaro una funzione da poter passare a Select NB deve restituire un booleano*)
			(	Select( 
					([("root"); ("rchildRoot")]),
					(Den("function")),  
					(ETree(		Node( "root", Eint(0), Empty,
					(*NB Ritorna il sottoalbero con radice il primo nodo che rispetta la funzione -> tutto l'albero*)
									Node("rchildRoot",Eint(0),
										Node("lchild", Eint(0),Empty, Empty),
										Node("rchild", Eint(0),Empty, Empty)
									)
								)
						  )
					)
				)
			)
		)
) emptyenv;;


(*test Select con cammino vuoto*)
let emptySubtree = eval (
   Let("function", (Fun("x", IsZero(Den("x"))) ), (*dichiaro una funzione da poter passare a Select NB deve restituire un booleano*)
			(	Select( 
					([]),
					(*se non c'e' nessu cammino -> nessun nodo nel cammino puo' soddisfare una condizione*)
					(Den("function")),  
					(ETree(		Node( "root", Eint(5), Empty,
									Node("rchildRoot",Eint(5),
										Node("lchild", Eint(5),Empty, Empty),
										Node("rchild", Eint(5),Empty, Empty)
									)
								)
						  )
					)
				)
			)
		)
) emptyenv;;

(*test Select nessun nodo ha valore zero*)
let emptySubtree = eval (
   Let("function", (Fun("x", IsZero(Den("x"))) ), (*dichiaro una funzione da poter passare a Select NB deve restituire un booleano*)
   (*Nessun nodo soddisfa isZero, il risultato sarà un albero vuoto*)
			(	Select( 
					([("root"); ("rchildRoot"); ("lchild"); ("rchild")]),
					(Den("function")),  
					(ETree(		Node( "root", Eint(5), Empty,
									Node("rchildRoot",Eint(5),
										Node("lchild", Eint(5),Empty, Empty),
										Node("rchild", Eint(5),Empty, Empty)
									)
								)
						  )
					)
				)
			)
		)
) emptyenv;;