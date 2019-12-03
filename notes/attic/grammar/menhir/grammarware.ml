module Source = struct let filename = "parser.cmly" end
module G = MenhirSdk.Cmly_read.Read(Source)

open MenhirSdk.Keyword

let print_keyword kw =
  (match kw with
  | Position _ (* (subject, where, flavor) *) ->
      print_endline "Position...";
      ()
  | SyntaxError -> print_endline "SyntaxError"
  )

let print_action action =
  print_endline "action:";
  List.iter print_keyword (G.Action.keywords action);
  ()

let print_lr1 _lr1 =
  print_endline "\n...lr1..."

let print_entrypoint (nt, prod, lr1) =
  print_endline "nonterminal:";
  print_endline (G.Nonterminal.name nt);
  print_endline "prod:";
  (match (G.Production.action prod) with
  | Some action -> print_action action
  | None -> print_endline "(no action)"
  );
  print_endline "nonterminal:";
  G.Print.nonterminal Format.std_formatter nt;
  Format.print_flush ();
  print_endline "\nproduction:";
  G.Print.production Format.std_formatter prod;
  Format.print_flush ();
  print_lr1 lr1;
  ()

let _ = print_endline "hello world"
let _ = print_endline (G.Grammar.basename)
let _ = print_endline "preludes:"
let _ = List.iter print_endline (G.Grammar.preludes)
let _ = print_endline "postludes:"
let _ = List.iter print_endline (G.Grammar.postludes)
let _ = print_endline "parameters:"
let _ = List.iter print_endline (G.Grammar.parameters)
let _ = List.iter print_entrypoint (G.Grammar.entry_points)
