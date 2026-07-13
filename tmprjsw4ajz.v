From Stdlib Require Import ZArith String List.
Import ListNotations.
Require Import SCoqShared.Supercompiler SCoqShared.LambdaA.
Open Scope Z_scope. Open Scope string_scope.

Definition F : fn_table := 
  [("is_sorted", (["xs"],
     PIf (PListIsNil (PVar "xs"))
       (PVal (PLitBool true))
       (PIf (PListIsNil (PListTail (PVar "xs")))
          (PVal (PLitBool true))
          (PBinOp PAndOp
            (PBinOp PLeOp (PListHead (PVar "xs")) (PListHead (PListTail (PVar "xs"))))
            (PCall "is_sorted" [PListTail (PVar "xs")])))))
  ].

Compute (supercompile F 100 nil (PCall "is_sorted" [PVar "xs"])).
