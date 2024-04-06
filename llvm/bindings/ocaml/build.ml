module C = Configurator.V1

let find_llvm_config t version =
  let candidates = [
    Printf.sprintf "llvm-config-%s" version;
    Printf.sprintf "llvm-config-%s.0" version;
    Printf.sprintf "llvm-config%s0" version;
    Printf.sprintf "llvm-config-mp-%s" version;
    Printf.sprintf "llvm-config-mp-%s.0" version;
    Printf.sprintf "llvm%s-config" version;
    Printf.sprintf "llvm-config-%s-32" version;
    Printf.sprintf "llvm-config-%s-64" version;
    "llvm-config";
    "$brew_llvm_config";
  ]
  in
  let rec loop = function
    | [] -> None
    | candidate :: candidates ->
      match C.which t candidate with
      | Some s -> Some s
      | None -> loop candidates
  in
  loop candidates

let components = Queue.create ()

let main t =
  match find_llvm_config t "15" with
  | None -> ()
  | Some llvm_config ->
    prerr_endline llvm_config;
    ()

let add_component s =
  let split = String.split_on_char ';' s in
  List.iter (fun s -> Queue.add s components) split

let () =
  C.main
    ~args:[
      ("-components", Arg.String add_component, "The LLVM components")
    ]
    ~name:"build"
    main
