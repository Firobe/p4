type player = P1 | P2
type token =
  | Empty
  | Full of player

(* 7 columns, 6 rows *)

type height = int
type grid = token array array
type state = player * grid * height array
type move = int

let row_nb = 6
let col_nb = 7

let next_player = function
  | P1 -> P2
  | P2 -> P1

module Basic =
struct
  let initial_state : state =
    P1, Array.make_matrix col_nb row_nb Empty, Array.make col_nb 0

  let is_move_legal grid move =
    grid.(move).(row_nb - 1) = Empty

  let play (player, grid, heights) move : state =
    let ngrid = Array.copy grid in
    let nheights = Array.copy heights in
    let row = heights.(move) in
    ngrid.(move).(row) <- Full player;
    nheights.(move) <- row + 1;
    (next_player player, ngrid, nheights)

  let row_ok r = 0 <= r && r < row_nb
  let col_ok c = 0 <= c && c < col_nb
  let coord_ok c r = row_ok r && col_ok c

  let is_move_winning (player, grid, heights) move =
    let row, col = heights.(move), move in
    let find_step dir (f : int -> token option) =
      let rec aux cur = match f cur with
        | Some (Full p) when p = player -> 1 + aux (cur + dir)
        | _ -> 0
      in
      aux dir in
    let max_interv f = find_step 1 f + find_step (-1) f + 1 in
    let f_row i = if col_ok (col + i) then
        Some grid.(col + i).(row) else None in
    let f_col i = if row_ok (row + i) then
        Some grid.(col).(row + i) else None in
    let f_diag_ne i = if coord_ok (col + i) (row + i) then
        Some grid.(col + i).(row + i) else None in
    let f_diag_se i = if coord_ok (col - i) (row + i) then
        Some grid.(col - i).(row + i) else None in
    max_interv f_row >= 4 ||
    max_interv f_col >= 4 ||
    max_interv f_diag_se >= 4 ||
    max_interv f_diag_ne >= 4

  let pp_player fmt = function
    | P1 -> Format.fprintf fmt "P1"
    | P2 -> Format.fprintf fmt "P2"

  let pp_state fmt (player, grid, _) =
    Format.fprintf fmt "It's %a's turn.\n" pp_player player;
    for y = row_nb - 1 downto 0 do
      for x = 0 to col_nb - 1 do
        let c = match grid.(x).(y) with
          | Empty -> '.'
          | Full P1 -> 'O'
          | Full P2 -> 'X'
        in Format.fprintf fmt "%c " c
      done;
      Format.pp_print_newline fmt ()
    done
end

module AI = struct
  let next_move (player, grid, _) =
    ignore player;
    let rec aux cur =
      if cur = col_nb then assert false
      else if Basic.is_move_legal grid cur then cur
      else aux (cur + 1)
    in aux 0
end

let () =
  let init = Basic.initial_state in
  Format.printf "Should P1 be human (true/false) ? %!";
  let is_p1_human = read_line () |> bool_of_string in
  Format.printf "Should P2 be human (true/false) ? %!";
  let is_p2_human = read_line () |> bool_of_string in
  let askwhere () = Format.printf "Where to play [1-7] ? %!"; read_int () in
  let rec loop ((player, grid, heights) as state) =
    if Array.for_all ((=) 6) heights then (
      Format.printf "DRAW\n"; state
    )
    else (
      Basic.pp_state Format.std_formatter state;
      let next_move =
        match player with
        | P1 when is_p1_human -> askwhere ()
        | P2 when is_p2_human -> askwhere ()
        | _ -> AI.next_move state
      in
      if Basic.is_move_legal grid next_move then
        if Basic.is_move_winning state next_move then (
          Format.printf "%a WINS\n" Basic.pp_player player;
          Basic.play state next_move
        )
        else loop (Basic.play state next_move)
      else loop state
    )
  in loop init |> Basic.pp_state Format.std_formatter
