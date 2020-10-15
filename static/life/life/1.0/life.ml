(* Copyright (C) 2004 Julien SIGNOLES *)

(* *************************************************************************
   compilation line :

   ocamlopt -o life -I +threads graphics.cmxa unix.cmxa threads.cmxa life.ml
   ************************************************************************* *)

type cell = Dead | Alive
type map = cell array array

module View : 
sig
  val size_x : int
  val size_y : int
  val draw : map -> unit
  val wait_action : key:(char -> unit) -> mouse:(int -> int -> unit) -> unit
  val close : unit -> unit
end = 
struct

  open Graphics

  let () =
    open_graph (Sys.getenv "DISPLAY" ^ " 512x512");
    display_mode false;
    set_window_title "Game of life"

  let size_x = size_x ()
  let size_y = size_y ()

  let draw w =
    let n = Array.length w in
    let m = Array.length w.(0) in
    let x = size_x / n in
    let y = size_y / m in
    for i = 0 to n - 1 do
      for j = 0 to m - 1 do
	set_color (match w.(i).(j) with Dead -> white | Alive -> blue);
	let a = i * x in
	let b = j * y in
	fill_rect a b x y;
	set_color black;
	draw_rect a b x y
      done
    done;
    synchronize ()

  let wait_action ~key ~mouse =
    let status = Graphics.wait_next_event [ Key_pressed; Button_down ] in
    if status.keypressed then 
      key status.key
    else
      mouse status.mouse_x status.mouse_y

  let close = close_graph

end

module Model : 
sig
  val next_state : unit -> unit
  val default_size : int
  val get_x : unit -> int
  val get_y : unit -> int
  val set_x : int -> unit
  val set_y : int -> unit
    (* Setters assume their arguments are stricly positive *)
  val clear : unit -> unit
  val rand : unit -> unit
  val swap_cell : int -> int -> unit
end = 
struct

  let default_size = 64
  let x = ref default_size
  let y = ref default_size

  let w = ref [||]
    (* Late initialization *)

  let get_x () = Array.length !w
  let get_y () = Array.length !w.(0)

  let set_x n = 
    assert (n > 0); 
    x := n

  let set_y n =
    assert (n > 0);
    y := n

  let rand =
    Random.self_init ();
    fun () -> 
      w := Array.init !x (fun _ -> Array.init !y 
			    (fun _ -> if Random.bool () then Dead else Alive));
      View.draw !w

  let () = rand ()
    (* Random initialization of [w] *)

  let neighbours w x y =
    (* The world is considered as a tore *)
    let h = Array.length w - 1 in
    let v = Array.length w.(0) - 1 in
    let wi = w.(x) in
    let wp = w.(if x = 0 then h else x - 1) in
    let wn = w.(if x = h then 0 else x + 1) in
    let yp = if y = 0 then v else y - 1 in
    let yn = if y = v then 0 else y + 1 in
    [ wp.(y); wp.(yp); wi.(yp); wn.(yp); wn.(y); wn.(yn); wi.(yn); wp.(yn) ]

  let next_one_state x y = 
    let n = 
      List.fold_left 
	(fun a -> function Alive -> a + 1 | Dead -> a) 0 (neighbours !w x y)
    in
    match !w.(x).(y) with
      | Dead  -> if n = 3 then Alive else Dead
      | Alive -> if n < 2 || n > 3 then Dead else Alive

  let next_state () =
    let x = get_x () in
    let y = get_y () in
    w := Array.init x (fun i -> Array.init y (next_one_state i));
    View.draw !w

  let clear () =
    w := Array.init !x (fun _ -> Array.init !y (fun _ -> Dead));
    View.draw !w

  let swap_cell x y =
    (!w.(x).(y) <- match !w.(x).(y) with Dead -> Alive | Alive -> Dead);
    View.draw !w

end

module AutoPlay : sig
  val run : unit -> unit
  val stop : unit -> unit
  val set_speed : int -> unit
end = 
struct

  let speed = ref 0
  let id = ref None

  let play () =
    try
      while true do 
	if !id = None then raise Exit;
	Model.next_state ();
	Thread.delay (float_of_int !speed /. 10.)
      done
    with Exit -> ()

  let run () =
    match !id with
      | None -> id := Some (Thread.create play ())
      | Some _ -> ()

  let stop () = 
    match !id with
      | None -> ()
      | Some x ->
	  id := None;
	  Thread.join x

  let set_speed n = speed := n

end

module Controller :
sig
  val key : char -> unit
  val mouse : int -> int -> unit
end = 
struct

  let help () =
    Format.printf "
h \t\t\thelp
q \t\t\tquit
n \t\t\tnext state
x \t\t\tenter a new abscisse
y \t\t\tenter a new ordinate
b \t\t\tnew blank world
r \t\t\tnew random world
0..9\t\t\tspeed of the timer (in second)
t \t\t\tauto play with a timer
k \t\t\tstop auto play@."

  let read () = 
    try 
      let x = read_int () in
      if x > 0 then x else Model.default_size
    with Failure _ -> 
      Model.default_size

  let key = function
    | 'h' -> help ()
    | 'q' -> raise Exit
    | 'n' -> 
	AutoPlay.stop ();
	Model.next_state ()
    | 'x' -> 
	Format.printf "new abscisse: @?"; 
	Model.set_x (read ())
    | 'y' -> 
	Format.printf "new ordinate: @?"; 
	Model.set_x (read ())
    | 'b' -> 
	AutoPlay.stop ();
	Model.clear ();
    | 'r' -> 
	AutoPlay.stop ();
	Model.rand ()
    | '0' .. '9' as s -> 
	AutoPlay.set_speed (int_of_char s - 48);
	AutoPlay.run ()
    | 't' -> AutoPlay.run ()
    | 'k' -> AutoPlay.stop ()
    | _ -> ()

  let mouse x y =
    AutoPlay.stop ();
    Model.swap_cell 
      (x * Model.get_x () / View.size_x) 
      (y * Model.get_y () / View.size_y)

end

let () = 
  try
    while true do View.wait_action Controller.key Controller.mouse done
  with Exit ->
    View.close ()
