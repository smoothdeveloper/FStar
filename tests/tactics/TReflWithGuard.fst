module TReflWithGuard

open FStar.Tactics

assume val f : int -> string

let test (x:int) (_ : squash (x == 25)) =
  assert (f x == f 25) by begin
    (* dump "1"; *)
    trefl_with_guard ();
    (* dump "2"; *)
    ()
  end
