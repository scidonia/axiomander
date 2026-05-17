Require Import ZArith String List.
Require Import Imp.
Import ListNotations.

(** * Pydantic Model Encoding

    Maps Pydantic model classes to Coq records.
    Each model becomes a [Record] with typed fields.
    For IMP verification, records are flattened into per-field
    state variables (e.g. [p.x] → state key ["p.x"]).

    ## Mapping

    Python                          Coq
    ──────                          ───
    class Point(BaseModel):         Record Point : Type :=
        x: int                          { point_x : Z
        y: int = 0                      ; point_y : Z }.
    p = Point(x=3, y=4)
    p.x                            point_x p
    Optional[int]                  option Z
    List[int]                      list Z
*)

(** ** Field Schema *)

Record field : Type := {
  field_name    : string;
  field_type    : string;
  field_default : option Z;
}.

Definition model_schema := list field.

(** ** Example: Point model (hand-written) *)

Record Point : Type := {
  point_x : Z;
  point_y : Z;
}.

Definition mk_point (x y : Z) : Point :=
  {| point_x := x; point_y := y |}.

(** Field access as Coq proposition for use in contracts. *)
Definition point_valid (p : Point) : Prop :=
  p.(point_x) >= 0 /\ p.(point_y) >= 0.

(** ** Flattening: Model ↔ IMP State

    A model instance with prefix [pfx] stores each field
    [f] at state key [pfx ++ "." ++ f].
*)

Definition flat_key (pfx f : string) : string :=
  pfx ++ "."%string ++ f.

Definition store_field (pfx f : string) (v : value) (s : state) : state :=
  upd s (flat_key pfx f) v.

Definition load_field (pfx f : string) (s : state) : Z :=
  asZ (s (flat_key pfx f)).

Definition store_point (p : Point) (pfx : string) (s : state) : state :=
  let s1 := store_field pfx "y"%string (VZ (p.(point_y))) s in
  store_field pfx "x"%string (VZ (p.(point_x))) s1.

Definition load_point (pfx : string) (s : state) : Point :=
  mk_point (load_field pfx "x"%string s) (load_field pfx "y"%string s).

(** Convenience: initialise a state with a Point's fields. *)
Definition init_point_state (px py : Z) : state :=
  let s := store_field "p"%string "y"%string (VZ py) empty_state in
  store_field "p"%string "x"%string (VZ px) s.

(** ** Validation in WP contracts

    @requires(lambda p: p.x >= 0 and p.y >= 0)
    becomes:
    wp ... (fun s => load_field "p" "x" s >= 0 /\ load_field "p" "y" s >= 0)
*)

Definition point_pre (s : state) : Prop :=
  load_field "p"%string "x"%string s >= 0 /\
  load_field "p"%string "y"%string s >= 0.

(** ** Encoding Optional types

    An Optional[int] is stored as:
      state[f".tag"] = 0 (Some) or 1 (None)
      state[f".val"] = value if Some else 0
*)

Definition optional_tag (pfx f : string) (s : state) : Z :=
  asZ (s (flat_key pfx (f ++ ".tag"%string))).

Definition optional_val (pfx f : string) (s : state) : Z :=
  asZ (s (flat_key pfx (f ++ ".val"%string))).

Definition load_optional (pfx f : string) (s : state) : option Z :=
  if Z.eqb (optional_tag pfx f s) 0
  then Some (optional_val pfx f s)
  else None.

(** ** Encoding List types

    For now, lists are not encoded in IMP state.
    The WP handles them through pre/post condition predicates
    that refer to the abstract model. Full state encoding
    can be added when needed for imperative list manipulation.
*)
