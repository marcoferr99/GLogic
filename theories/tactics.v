From Stdlib Require Import Lia.
Require Export base.


Ltac2 rec c_injection l h :=
  let h1 := Fresh.in_goal @IA in let h2 := Fresh.in_goal @IB in
  apply $l in $h as [$h1 $h2];
  let f x := Control.plus (fun () => c_injection l x) (
    fun _ => let c := Control.hyp x in try (rewrite $c in *); clear $x
  ) in
  f h1; f h2.
(*
  let c1 := Control.hyp h1 in let c2 := Control.hyp h2 in
  try (rewrite $c1 in * ); try (rewrite $c2 in * ).
  *)


Ltac2 s_simpl c := Std.simpl {
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
  c
  .

Ltac2 all_hyps t :=
  List.iter (
    fun (x, _, _) => t x
  ) (Control.hyps ()).

Ltac2 autorewrite (dt : ident) (c : Std.clause) :=
  match c.(Std.on_hyps) with
  | None => all_hyps (fun x => ltac1:(dt x |- autorewrite with dt in x) (Ltac1.of_ident dt) (Ltac1.of_ident x))
  | Some l => List.iter (fun (x, _, _) => ltac1:(dt x |- autorewrite with dt in x) (Ltac1.of_ident dt) (Ltac1.of_ident x)) l
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

Ltac2 goal := {
    Std.on_hyps := Some [];
    Std.on_concl := Std.AllOccurrences
  }.
Ltac2 one_hyp h := {
    Std.on_hyps := Some [(h, Std.AllOccurrences, Std.InHyp)];
    Std.on_concl := Std.NoOccurrences
  }.
Ltac2 all := {
    Std.on_hyps := None;
    Std.on_concl := Std.AllOccurrences
  }.


Ltac2 Type view_parameters := {
  to_tp : constr;
  to_view : constr;
  to_tp_to_view : constr;
  tp_simpl : Std.clause -> unit;
  discriminate_other : constr -> unit
}.

Ltac2 to_tp p h :=
  let to_tp := p.(to_tp) in let to_tp_to_view := p.(to_tp_to_view) in
  apply (f_equal $to_tp) in $h; repeat (rewrite $to_tp_to_view in $h).

Ltac2 to_view p (h : ident) :=
  let to_view := p.(to_view) in
  apply (f_equal $to_view) in $h; p.(tp_simpl) (one_hyp h).

Ltac2 tp_injection p (h : ident) :=
  to_view p h;
  let c := Control.hyp h in
  let no := List.length (Control.hyps ()) in
  Std.move h Std.MoveLast; injection $c as ?;
  List.iter (
    fun (x, _, _) => try (to_tp p x);
    let cx := Control.hyp x in rewrite $cx in *; clear $x
  ) (List.skipn (Int.sub no 1) (Control.hyps ())).

Ltac2 tp_discriminate p (h : ident) :=
  let c := Control.hyp h in
  lazy_match! (Constr.type c) with
  | _ = _ => to_view p h; discriminate $c
  | _ => p.(discriminate_other) c
  end.

Ltac2 tp_discriminate_all p :=
  match! goal with
  | [h : _ |- _] => tp_discriminate p h
  end.
