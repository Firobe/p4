type player = P1 | P2
type token =
  | Empty
  | Full of player

(* 7 columns, 6 rows *)
let row_nb = 6
let col_nb = 7
let towin = 4
let allocated_time = 15.
let allocated_height = 6

open Hashcons
type 'a cached =
  | Uncomputed
  | Uncomputable
  | Computed of 'a

type column = column_node hash_consed
and column_node = {
  data : token array;
  height : int;
  mutable p1 : column cached;
  mutable p2 : column cached;
}
module Column_node = struct
  type t = column_node
  let equal c1 c2 = c1.data = c2.data
  let hash c = Hashtbl.hash c.data
end
module HCT = Hashcons.Make(Column_node)
let hct = HCT.create 128
let mkcol data height : column =
  HCT.hashcons hct {data; height; p1 = Uncomputed; p2 = Uncomputed}

type state = {
  player : player;
  grid : column array;
}
type node = node_node hash_consed
and node_node = {
  state : state;
  mutable value : int cached;
  children : node cached array
}
module Node_node = struct
  type t = node_node
  let equal n1 n2 = n1.state = n2.state
  let hash n = Hashtbl.hash n.state
end
module HNT = Hashcons.Make(Node_node)
let hnt = HNT.create 1000000
let mknode state : node =
  HNT.hashcons hnt {state; value = Uncomputed;
                    children = Array.make col_nb Uncomputed}


module Basic =
struct
  let next_player = function
    | P1 -> P2
    | P2 -> P1

  let initial_state : state = 
    let emptycol = mkcol (Array.make row_nb Empty) 0 in
    { grid = Array.make col_nb emptycol; player = P1 }

  let is_move_legal state move =
    state.grid.(move).node.height < row_nb

  let play (state : state)  move : state =
    let retrieve_np = if state.player = P1 then
        fun col -> col.node.p1
      else fun col -> col.node.p2
    in
    let curcol = state.grid.(move) in
    let ncol = match retrieve_np curcol with
      | Uncomputable -> assert false
      | Computed col -> col
      | Uncomputed ->
        let ndata = Array.copy curcol.node.data in
        ndata.(curcol.node.height) <- Full state.player;
        let computed = mkcol ndata (curcol.node.height + 1) in
        if state.player = P1 then curcol.node.p1 <- Computed computed
        else curcol.node.p2 <- Computed computed;
        computed
    in
    let ngrid = Array.copy state.grid in
    ngrid.(move) <- ncol;
    {player = next_player state.player;
     grid = ngrid}

  let row_ok r = 0 <= r && r < row_nb
  let col_ok c = 0 <= c && c < col_nb
  let coord_ok c r = row_ok r && col_ok c

  let is_move_winning (state : state) move =
    let grid = state.grid in
    let row, col = grid.(move).node.height, move in
    let player = state.player in
    let find_step dir (f : int -> token option) =
      let rec aux cur = match f cur with
        | Some (Full p) when p = player -> 1 + aux (cur + dir)
        | _ -> 0
      in
      aux dir in
    let max_interv f = find_step 1 f + find_step (-1) f + 1 in
    let f_row i = if col_ok (col + i) then
        Some grid.(col + i).node.data.(row) else None in
    let f_col i = if row_ok (row + i) then
        Some grid.(col).node.data.(row + i) else None in
    let f_diag_ne i = if coord_ok (col + i) (row + i) then
        Some grid.(col + i).node.data.(row + i) else None in
    let f_diag_se i = if coord_ok (col - i) (row + i) then
        Some grid.(col - i).node.data.(row + i) else None in
    max_interv f_row >= towin ||
    max_interv f_col >= towin ||
    max_interv f_diag_se >= towin ||
    max_interv f_diag_ne >= towin

  let pp_player fmt = function
    | P1 -> Format.fprintf fmt "P1"
    | P2 -> Format.fprintf fmt "P2"

  let pp_state fmt (state : state) =
    Format.fprintf fmt "It's %a's turn.\n" pp_player state.player;
    for y = row_nb - 1 downto 0 do
      for x = 0 to col_nb - 1 do
        let c = match state.grid.(x).node.data.(y) with
          | Empty -> '.'
          | Full P1 -> 'O'
          | Full P2 -> 'X'
        in Format.fprintf fmt "%c " c
      done;
      Format.pp_print_newline fmt ()
    done
end

let rec foldi : ('a -> int -> 'a) -> int -> int -> 'a -> 'a =
  fun f from tov init ->
  if from = tov then init
  else f (foldi f (from + 1) tov init) from

module AI = struct
  let weights = [|
    [| 3; 4; 5; 5; 4; 3 |];
    [| 4; 6; 8; 8; 6; 4 |];
    [| 5; 8;11;11; 8; 5 |];
    [| 7;10;13;13;10; 7 |];
    [| 5; 8;11;11; 8; 5 |];
    [| 4; 6; 8; 8; 6; 4 |];
    [| 3; 4; 5; 5; 4; 3 |]
  |]
  let eval (state : state) =
    foldi (fun acc1 x ->
        let col = state.grid.(x) in
        (foldi (fun acc2 y -> match col.node.data.(y) with
            | Full P1 -> acc2 + weights.(x).(y)
            | Full P2 -> acc2 - weights.(x).(y)
            | Empty -> assert false
          ) 0 col.node.height 0
        ) + acc1
      ) 0 col_nb 0

  let rec eval_child node move f_next ss =
    let nn = node.node in
    let get_child_value child =
      let cnn = child.node in
      match cnn.value with
      | Uncomputable -> assert false
      | Computed v -> v
      | Uncomputed ->
        let computed =
        if ss cnn.state then eval cnn.state
        else
          if Basic.is_move_winning nn.state move then
            if nn.state.player = P1 then 1000
            else -1000
          else fst (f_next child ss)
        in
        cnn.value <- Computed computed;
        computed
    in
    match nn.children.(move) with
      | Uncomputable -> None
      | Computed child -> Some (get_child_value child)
      | Uncomputed ->
        if Basic.is_move_legal nn.state move then (
          let nstate = Basic.play nn.state move in
          let child = mknode nstate in
          let nval = get_child_value child in
          nn.children.(move) <- Computed child;
          Some nval
        )
        else (nn.children.(move) <- Uncomputable; None)
  and explore comp constant f_next node ss =
    let v, i = foldi (fun (mv, mi) move ->
        match eval_child node move f_next ss with
        | None -> (mv, mi)
        | Some nval ->
          if comp nval mv then (nval, move) else (mv, mi)
    ) 0 col_nb (constant, 42) in
    if v = constant then 0, 42 else v, i
  and max node = explore (>) (-0xDEADBEEF) min node
  and min node = explore (<) 0xDEADBEEF max node

  let pp_cached pp_elem fmt = function
    | Uncomputable -> Format.pp_print_string fmt "Uncomputable"
    | Uncomputed -> Format.pp_print_string fmt "Uncomputed"
    | Computed x -> Format.fprintf fmt "Computed (%a)" pp_elem x

  let rec pp_node fmt node =
    let nn = node.node in
    Format.fprintf fmt "Value: %a@," (pp_cached Format.pp_print_int) nn.value;
    Format.fprintf fmt "Children:@,";
    Array.iteri (fun i child ->
        Format.fprintf fmt "@[<v 2>%d ->@,%a@]@," i (pp_cached pp_node) child
      ) nn.children

  let next_move (state : state) =
    let root = mknode state in
    let timer = Unix.gettimeofday () in
    let count_token = Array.fold_left (fun acc col -> col.node.height + acc) 0 in
    let cur_height = count_token state.grid in
    let ss s =
      if count_token s.grid - cur_height > allocated_height then (
        true
      ) else if Unix.gettimeofday () > timer +. allocated_time then (
        Format.printf "Stopped by time\n"; true
      ) else false
    in
    let score, move = (if state.player = P1 then max else min) root ss in
(*     Format.printf "@[<v 2>Root after:@,%a@]" pp_node root; *)
    Format.printf "Expected AI score: %d\n" score;
    move
end

let gameloop =
  Printexc.record_backtrace true;
  let init = Basic.initial_state in
  Format.printf "Should P1 be human (true/false) ? %!";
  let is_p1_human = read_line () |> bool_of_string in
  Format.printf "Should P2 be human (true/false) ? %!";
  let is_p2_human = read_line () |> bool_of_string in
  let askwhere () = Format.printf "Where to play [0-6] ? %!"; read_int () in
  let rec loop state =
    if Array.for_all (fun col -> col.node.height = row_nb) state.grid then (
      Format.printf "DRAW\n"; state
    )
    else (
      Basic.pp_state Format.std_formatter state;
      let next_move =
        match state.player with
        | P1 when is_p1_human -> askwhere ()
        | P2 when is_p2_human -> askwhere ()
        | _ -> AI.next_move state
      in
      Format.printf "Will play in the %d-nth column\n" (next_move + 1);
      if 0 <= next_move && next_move < col_nb
         && Basic.is_move_legal state next_move then
        if Basic.is_move_winning state next_move then (
          Format.printf "%a WINS\n" Basic.pp_player state.player;
          Basic.play state next_move
        )
        else loop (Basic.play state next_move)
      else loop state
    )
  in loop init |> Basic.pp_state Format.std_formatter;
  let _, coln, _, _, _, _ = HCT.stats hct in
  let _, nodn, _, _, _, _ = HNT.stats hnt in
  Format.printf "Number of allocated columns: %d\nNumber of alloc nodes: %d\n"
    coln nodn
