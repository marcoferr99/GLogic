Require Export base.
From Stdlib Require Import Lia.


(*
Ltac2 choices (l : (unit -> unit) list) :=
  List.fold_right (fun t1 t2 => Control.plus t1 (fun _ => t2)) l (fun () => fail).
  *)

Ltac2 rec and_unfold c :=
  lazy_match! Constr.type c with
  | _ /\ _ => List.append (and_unfold '(proj1 $c)) (and_unfold '(proj2 $c))
  | _ => [c]
  end.

Ltac2 rec c_first f l :=
  match l with
  | [] => Control.zero No_value
  | h :: t => Control.plus (fun () => f h) (fun _ => c_first f t)
  end.

Ltac2 rec c_injection l e :=
  let a := c_first (fun f => let f1 := f () in '($f1 $e)) l in
  let m := and_unfold a in
  List.iter (fun x =>
    Control.plus (fun () => c_injection l x) (fun _ => try (rewrite $x in *))
  ) m.

Ltac2 rec c_iter (f : 'a -> 'a list) (c : 'a list) : 'a list :=
  match c with
  | [] => []
  | h :: t => Control.plus
    (fun () => c_iter f (List.append (f h) t)) (fun _ => h :: c_iter f t)
  end.

Ltac2 rec i_iter (f : 'a -> 'a list) (l : 'a list) : unit :=
  match l with
  | [] => ()
  | h :: t => Control.plus
      (fun () => i_iter f (List.append (f h) t)) (fun _ => i_iter f t)
  end.

(*
Ltac2 f x :=
  lazy_match! x with
  | S ?x => [x; x]
  end.

Ltac2 Eval c_iter f ['2].
*)


(*
Ltac2 Eval c_injection ['ax] '(ax1).
  let h1 := Fresh.in_goal @IA in let h2 := Fresh.in_goal @IB in
  first0 (List.map (fun x () => apply $x in $h as [$h1 $h2]) l);
  let f x := Control.plus (fun () => c_injection l x) (
    fun _ => let c := Control.hyp x in try (rewrite $c in * ); clear $x
  ) in
  f h1; f h2.

Ltac2 rec c_injection l h :=
  let h1 := Fresh.in_goal @IA in let h2 := Fresh.in_goal @IB in
  first0 (List.map (fun x () => apply $x in $h as [$h1 $h2]) l);
  let f x := Control.plus (fun () => c_injection l x) (
    fun _ => let c := Control.hyp x in try (rewrite $c in * ); clear $x
  ) in
  f h1; f h2.
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
  c.

Ltac2 all_hyps t :=
  List.iter (
    fun (x, _, _) => t x
  ) (Control.hyps ()).

Ltac2 try_all (t : ident -> unit) :=
  match! goal with
  | [h : _ |- _] => t h
  end.

Ltac2 autorewrite (dt : ident) (c : Std.clause) :=
  let f x := ltac1:(dt x |- autorewrite with dt in x) (Ltac1.of_ident dt) (Ltac1.of_ident x) in
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


(* TODO: rew should be a Strategy.t *)
Ltac2 c_discriminate f (rew : ident -> unit) h :=
  let c := Control.hyp h in
  lazy_match! (Constr.type c) with
    ?a = _ => let g := f a in
      apply (f_equal $g) in $h; rew h; exfalso; rewrite <- $c; apply I
  end.

Ltac2 c_discriminate_all f rew :=
  match! goal with
  | [h : _ |- _] => c_discriminate f rew h
  end.




(*
Ltac2 Type view_parameters := {
  to_tp : constr;
  to_view : constr;
  to_tp_to_view : constr;
  tp_simpl : Std.clause -> unit;
  discriminate_other : constr -> unit
}.

(*
Ltac2 to_tp p h :=
  let to_tp := p.(to_tp) in let to_tp_to_view := p.(to_tp_to_view) in
  apply (f_equal $to_tp) in $h; repeat (rewrite $to_tp_to_view in $h).
  *)

Ltac2 to_view p (h : ident) :=
  let to_view := p.(to_view) in
  apply (f_equal $to_view) in $h; p.(tp_simpl) (one_hyp h).

(*
Ltac2 tp_injection p (h : ident) :=
  to_view p h;
  let c := Control.hyp h in
  let no := List.length (Control.hyps ()) in
  Std.move h Std.MoveLast; injection $c as ?;
  List.iter (
    fun (x, _, _) => try (to_tp p x);
    let cx := Control.hyp x in rewrite $cx in *; clear $x
  ) (List.skipn (Int.sub no 1) (Control.hyps ())).
*)

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
  *)
