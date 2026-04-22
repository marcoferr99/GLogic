Require Export base.
From Stdlib Require Import Lia.


Ltac2 s_simpl (c : Std.clause) : unit := Std.simpl {
    Std.rStrength := Std.Norm;
    Std.rBeta := true;
    Std.rMatch := true;
    Std.rFix := true;
    Std.rCofix := true;
    Std.rZeta := true;
    Std.rDelta := true;
    Std.rConst := []
  }
  None
  c.

Ltac2 all_hyps (t : ident -> unit) : unit :=
  List.iter (fun (x, _, _) => t x) (Control.hyps ()).

Ltac2 first_hyp (t : ident -> unit) : unit :=
  match! goal with | [h : _ |- _] => t h end.

Ltac2 autorewrite (dt : ident) (c : Std.clause) : unit :=
  let f x := ltac1:(dt x |- autorewrite with dt in x)
    (Ltac1.of_ident dt) (Ltac1.of_ident x) in
  match c.(Std.on_hyps) with
  | None => all_hyps f
  | Some l => List.iter (fun (x, _, _) => f x) l
  end;
  match c.(Std.on_concl) with
  | Std.AllOccurrences => ltac1:(dt |- autorewrite with dt) (Ltac1.of_ident dt)
  | _ => ()
  end.

Ltac2 Notation "easy" := ltac1:(easy).
Ltac2 Notation easy := easy.
Ltac2 Notation "lia" := ltac1:(lia).
Ltac2 Notation lia := lia.
Ltac2 Notation "intuition" := ltac1:(intuition).

Ltac2 goal : Std.clause := {
    Std.on_hyps := Some [];
    Std.on_concl := Std.AllOccurrences
  }.
Ltac2 one_hyp (h : ident) : Std.clause := {
    Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
    Std.on_concl := Std.NoOccurrences
  }.
Ltac2 all : Std.clause := {
    Std.on_hyps := None;
    Std.on_concl := Std.AllOccurrences
  }.


(*
Ltac2 choices (l : (unit -> unit) list) :=
  List.fold_right (fun t1 t2 => Control.plus t1 (fun _ => t2)) l (fun () => fail).
  *)

Ltac2 rec and_unfold (c : constr) : constr list :=
  lazy_match! Constr.type c with
  | _ /\ _ => List.append (and_unfold '(proj1 $c)) (and_unfold '(proj2 $c))
  | _ => [c]
  end.

Ltac2 rec c_first (f : 'b -> 'a) (l : 'b list) : 'a :=
  match l with
  | [] => Control.zero No_value
  | h :: t => Control.plus (fun () => f h) (fun _ => c_first f t)
  end.

Ltac2 rec c_injection (l : (unit -> constr) list) (e : constr) : unit :=
  let a := c_first (fun f => let fc := f () in '($fc $e)) l in
  List.iter (fun x =>
    Control.plus (fun () => c_injection l x) (fun _ => try (rewrite $x in *))
  ) (and_unfold a).

(*
Ltac2 rec c_iter (f : 'a -> 'a list) (c : 'a list) : 'a list :=
  match c with
  | [] => []
  | h :: t => Control.plus
    (fun () => c_iter f (List.append (f h) t)) (fun _ => h :: c_iter f t)
  end.
*)

Ltac2 rec i_iter (f : 'a -> 'a list) (l : 'a list) : unit :=
  match l with
  | [] => ()
  | h :: t => Control.plus
      (fun () => i_iter f (List.append (f h) t)) (fun _ => i_iter f t)
  end.

(* TODO: rew should be a Strategy.t *)
Ltac2 c_discriminate f (rew : ident -> unit) h :=
  let c := Control.hyp h in
  lazy_match! (Constr.type c) with
    ?a = _ => let g := f a in
      apply (f_equal $g) in $h; rew h; exfalso; rewrite <- $c; apply I
  end.

Ltac2 c_discriminate_all f rew := first_hyp (c_discriminate f rew).
