(* the test type for Crowbar is just a lazy call to Crowbar.add_test *)
(* same with Base_quickcheck, but with Test.run  *)
type qtest = QCheck.Test.t
type ctest = unit -> unit
type btest = unit -> unit

(* rename of the Core module type *)
type 'a basegen = (module Base_quickcheck.Test.S with type t = 'a)

(* Generalizing pre and post conditions *)
type test = Pre of bool * test | Post of bool

let ( =>> ) pre post = Pre (pre, post)
let ( ->> ) pre post = Pre (pre, Post post)

(* Generalizing parameterization of tests *)

type 'a property = {
  name : string;
  q : 'a QCheck.arbitrary -> string -> qtest;
  c : 'a Crowbar.gen -> string -> ctest;
  b : 'a basegen -> string -> btest;
}

(* Functions for realizing preconditions *)
let rec qmake (t : test) : bool =
  match t with
  | Pre (pre, post) ->
      QCheck.assume pre;
      qmake post
  | Post post -> post

let rec cmake (t : test) : unit =
  match t with
  | Pre (pre, post) ->
      Crowbar.guard pre;
      cmake post
  | Post post -> Crowbar.check post

let rec bmake (t : test) : unit Base.Or_error.t =
  match t with
  | Pre (true, post) -> bmake post
  | Pre (false, _) ->
      (* false precondition, we can skip test *)
      Ok ()
  | Post true -> Ok ()
  | Post false -> Error (Base.Error.of_string "fail")

(* Helpers to build `'a property` types. Note that `'b` is the input to the property, INCLUDING the other parameters. *)
let qbuild (g : 'b QCheck.arbitrary) (f : 'b -> bool) : string -> qtest =
 fun name -> QCheck.Test.make ~name ~count:500000000 g f

(* crowbar's type signature means 'c is essentially 'b -> unit *)
let cbuild (g : ('c, unit) Crowbar.gens) (f : 'c) : string -> ctest =
 fun name () -> Crowbar.add_test ~name g f

let _verbose res =
  if Core.is_ok res then print_endline "tests passed?"
  else print_endline "bug found!"

let bbuild (g : 'b basegen) (f : 'b -> unit Base.Or_error.t) : string -> btest =
 fun _ () ->
  Base_quickcheck.Test.run ~f g
    ~config:
      {
        seed = Base_quickcheck.Test.Config.Seed.Nondeterministic;
        test_count = Core.Int.max_value;
        shrink_count = 0;
        (* todo: we might need to alter the size ranges here *)
        sizes = Base_quickcheck.Test.default_config.sizes;
      }
  |> _verbose
