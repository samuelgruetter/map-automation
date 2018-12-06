(* ** ../bedrock2/compiler/src/../lib/fiat_crypto_tactics/Test.v *)
(** Test if a tactic succeeds, but always roll-back the results *)
Tactic Notation "test" tactic3(tac) :=
  try (first [ tac | fail 2 tac "does not succeed" ]; fail 0 tac "succeeds"; [](* test for [t] solved all goals *)).

(* ** ../bedrock2/compiler/src/../lib/fiat_crypto_tactics/Not.v *)
(* Require Import lib.fiat_crypto_tactics.Test. *)

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").


(* ** ../bedrock2/compiler/src/Decidable.v *)
(** Typeclass for decidable propositions *)
(** simplification of  fiat-crypto/src/Util/Decidable.v *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.NArith.

Class Decidable (P : Prop) := dec : {P} + {~P}.
Arguments dec _%type_scope {_}.

Notation DecidableRel R := (forall x y, Decidable (R x y)).
Notation DecidableEq T := (forall (x y: T), Decidable (x = y)).

Global Instance dec_eq_nat : DecidableEq nat := Nat.eq_dec.
Global Instance dec_le_nat : DecidableRel le := Compare_dec.le_dec.
Global Instance dec_lt_nat : DecidableRel lt := Compare_dec.lt_dec.
Global Instance dec_ge_nat : DecidableRel ge := Compare_dec.ge_dec.
Global Instance dec_gt_nat : DecidableRel gt := Compare_dec.gt_dec.

Global Instance dec_eq_Z : DecidableEq Z := Z.eq_dec.
Global Instance dec_lt_Z : DecidableRel BinInt.Z.lt := ZArith_dec.Z_lt_dec.
Global Instance dec_le_Z : DecidableRel BinInt.Z.le := ZArith_dec.Z_le_dec.
Global Instance dec_gt_Z : DecidableRel BinInt.Z.gt := ZArith_dec.Z_gt_dec.
Global Instance dec_ge_Z : DecidableRel BinInt.Z.ge := ZArith_dec.Z_ge_dec.

Global Instance dec_eq_N : DecidableEq N := N.eq_dec.

Global Instance dec_Empty_set: DecidableEq Empty_set.
  intro x. destruct x.
Defined.

Global Instance decidable_eq_option {A} `{DecidableEq A}: DecidableEq (option A).
  intros. unfold Decidable. destruct x; destruct y.
  - destruct (DecidableEq0 a a0).
    + subst. left. reflexivity.
    + right. unfold not in *. intro E. inversion E. auto.
  - right. intro. discriminate.
  - right. intro. discriminate.
  - left. reflexivity.
Defined.

Global Instance dec_eq_pair{T1 T2: Type}(eq1: DecidableEq T1)(eq2: DecidableEq T2):
  DecidableEq (T1 * T2).
refine (fun '(x1, x2) '(y1, y2) => match eq1 x1 y1, eq2 x2 y2 with
                                   | left E1, left E2 => left _
                                   | right N1, _ => right _
                                   | _, right N2 => right _
                                   end).
all: congruence.
Defined.

Global Instance dec_and {A B} `{Decidable A, Decidable B} : Decidable (A /\ B).
  unfold Decidable in *; destruct H; destruct H0; tauto.
Defined.

Global Instance dec_or {A B} `{Decidable A, Decidable B} : Decidable (A \/ B).
  unfold Decidable in *; destruct H; destruct H0; tauto.
Defined.

Global Instance dec_not {A} `{Decidable A} : Decidable (~ A).
  unfold Decidable in *. destruct H; tauto.
Defined.

(* ** ../bedrock2/compiler/src/util/Tactics.v *)
Require Export Coq.Program.Tactics.
(* Require Import lib.fiat_crypto_tactics.Not. *)
(* Require Import compiler.Decidable. *)
(* Require Import lib.LibTacticsMin. *)

Ltac destruct_one_match :=
  match goal with
  | [ |- context[match ?e with _ => _ end] ] =>
      is_var e; destruct e
  | [ |- context[match ?e with _ => _ end] ] =>
      let E := fresh "E" in destruct e eqn: E
  end.

Ltac destruct_one_dec_eq :=
  match goal with
  (* we use an explicit type T because otherwise the inferred type might differ *)
  | |- context[dec (@eq ?T ?t1 ?t2)] => destruct (dec (@eq T t1 t2)); [subst *|]
  end.

Ltac destruct_one_match_hyp_test type_test :=
  match goal with
  | H: context[match ?e with _ => _ end] |- _ =>
      is_var e;
      let T := type of e in type_test T;
      destruct e
  | H: context[if ?e then _ else _] |- _ =>
      is_var e;
      let T := type of e in type_test T;
      destruct e
  | H: context[match ?e with _ => _ end] |- _ =>
      let T := type of e in type_test T;
      let E := fresh "E" in destruct e eqn: E
  | H: context[if ?e then _ else _] |- _ =>
      let T := type of e in type_test T;
      let E := fresh "E" in destruct e eqn: E
  end.

Ltac destruct_one_match_hyp_of_type T :=
  destruct_one_match_hyp_test ltac:(fun t => unify t T).

Ltac destruct_one_match_hyp :=
  destruct_one_match_hyp_test ltac:(fun t => idtac).

Ltac repeat_at_least_once tac := tac; repeat tac.
Tactic Notation "repeatplus" tactic(t) := (repeat_at_least_once t).

Ltac destruct_pair_eqs := repeatplus
 (idtac; (* to make sure match is only executed later *)
  match goal with
  | H: (_, _) = (_, _) |- _ => inversion H; clear H
  end).

Ltac ensure_new H :=
  let t := type of H in
  not (clear H; match goal with
                | A: t |- _ => idtac
                end).

Tactic Notation "forget" constr(X) "as" ident(y) := set (y:=X) in *; clearbody y.

Ltac destruct_products :=
  repeat match goal with
  | p: _ * _  |- _ => destruct p
  | H: _ /\ _ |- _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
  | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
  end.

(** [pose proof defn], but only if no hypothesis of the same type exists.
    most useful for proofs of a proposition *)
Tactic Notation "unique" "pose" "proof" constr(defn) "as" ident(H) :=
  let T := type of defn in
  match goal with
  | [ H : T |- _ ] => fail 1
  | _ => pose proof defn as H
  end.

Ltac assert_is_type E :=
  let T := type of E in
  first
  [ unify T Set
  | unify T Prop
  | unify T Type
  (* this error is almost certainly a bug, so we let it bubble up with level 10000, instead
     of being swallowed by try, repeat, ||, etc *)
  | fail 10000 "type of" E "is" T "but should be Set, Prop or Type" ].

Ltac specialize_with E :=
  (* Catch errors such as E is something like "@name: NameWithEq -> Set" instead of "name: Set" *)
  assert_is_type E;
  repeat match goal with
  | H: forall (x: E), _, y: E |- _ =>
    match type of H with
    | DecidableEq E => fail 1
    | _ => let H' := fresh H y in unique pose proof (H y) as H'
    end
  end.

Tactic Notation "unique" "eapply" constr(p) "in" "copy" "of" ident(H) :=
  let H' := fresh H "_uac" in
  pose proof H as H';
  unshelve eapply p in H';
  try assumption;
  ensure_new H'.

Ltac deep_destruct H :=
  lazymatch type of H with
  | exists x, _ => let x' := fresh x in destruct H as [x' H]; deep_destruct H
  | _ /\ _ => let H' := fresh H in destruct H as [H' H]; deep_destruct H'; deep_destruct H
  | _ \/ _ => destruct H as [H | H]; deep_destruct H
  | _ => idtac
  end.

(* simplify an "if then else" where only one branch is possible *)
Ltac simpl_if :=
  let E := fresh "E" in
  match goal with
  | |- context[if ?e then _ else _]      => destruct e eqn: E; [contradiction|]
  | |- context[if ?e then _ else _]      => destruct e eqn: E; [|contradiction]
  | _: context[if ?e then _ else _] |- _ => destruct e eqn: E; [contradiction|]
  | _: context[if ?e then _ else _] |- _ => destruct e eqn: E; [|contradiction]
  end;
  clear E.

Ltac rewrite_match :=
  repeat match goal with
  | E: ?A = _ |- context[match ?A with | _ => _ end] => rewrite E
  end.

Tactic Notation "so" tactic(f) :=
  match goal with
  | _: ?A |- _  => f A
  |       |- ?A => f A
  end.

Ltac exists_to_forall H :=
  match type of H with
  | (exists k: ?A, @?P k) -> ?Q =>
    let Horig := fresh in
    rename H into Horig;
    assert (forall k: A, P k -> Q) as H by eauto;
    clear Horig;
    cbv beta in H
  end.

Ltac destructE d :=
  match type of d with
  | {?x1 = ?x2} + {?x1 <> ?x2} => destruct d; [subst x2|]
  | {_} + {_} => destruct d
  | _ => is_var d; destruct d
  | _ => let E := fresh "E" in destruct d eqn: E
  end.

Ltac destruct_one_match_hyporgoal_test check cleanup :=
  match goal with
  | |- context[match ?d with _ => _ end]      => check d; destructE d
  | H: context[match ?d with _ => _ end] |- _ => check d; destructE d; cleanup H
  end.

Lemma invert_Some_eq_Some: forall (A: Type) (x1 x2: A),
    Some x1 = Some x2 ->
    x1 = x2.
Proof.
  congruence.
Qed.

Lemma forall_Some_eq_Some : forall A (y z: A),
    (forall x, Some y = Some x -> Some z = Some x) ->
    z = y.
Proof.
  intros.
  specialize (H _ eq_refl); inversion H; auto.
Qed.

Ltac invert_Some_eq_Some :=
  repeat match goal with
         | H: Some ?x1 = Some ?x2 |- _ => apply invert_Some_eq_Some in H; subst x2
         | H: forall _, Some ?y = Some _ -> Some _ = Some _ |- _ =>
              apply forall_Some_eq_Some in H; subst y
         end.


Notation "x '\in' s" := (s x) (at level 70, no associativity, only parsing).

Section PropSet.
  Context {E: Type}.

  Definition empty_set: E -> Prop := fun _ => False.
  Definition singleton_set: E -> (E -> Prop) := eq.
  Definition union: (E -> Prop) -> (E -> Prop) -> (E -> Prop) :=
    fun s1 s2 x => s1 x \/ s2 x.
  Definition intersect: (E -> Prop) -> (E -> Prop) -> (E -> Prop) :=
    fun s1 s2 x => s1 x /\ s2 x.
  Definition diff: (E -> Prop) -> (E -> Prop) -> (E -> Prop) :=
    fun s1 s2 x => s1 x /\ ~ s2 x.

  Definition add(s: E -> Prop)(e: E) := union (singleton_set e) s.
  Definition remove(s: E -> Prop)(e: E) := diff s (singleton_set e).
  Definition subset(s1 s2: E -> Prop) := forall x, x \in s1 -> x \in s2.
  Definition disjoint(s1 s2: E -> Prop) := forall x, (~ x \in s1) \/ (~ x \in s2).
  Definition of_list l := List.fold_right union empty_set (List.map singleton_set l).

End PropSet.

Hint Unfold
     empty_set
     singleton_set
     union
     intersect
     diff
     add
     remove
     subset
     disjoint
     of_list
  : unf_set_defs.


(* ** ../bedrock2/compiler/src/util/Map.v *)
(* Require Import lib.fiat_crypto_tactics.Not. *)
(* Require Import compiler.util.Set. *)
(* Require Import compiler.util.Tactics. *)
(* Require Import compiler.Decidable. *)

Class MapFunctions(K V: Type) := mkMap {
  map: Type;

  (* fundamental operation, all others are axiomatized in terms of this one *)
  get: map -> K -> option V;

  empty_map: map;
  empty_is_empty: forall (k: K), get empty_map k = None;

  remove_key: map -> K -> map;
  get_remove_same: forall m k, get (remove_key m k) k = None;
  get_remove_diff: forall m k1 k2, k1 <> k2 -> get (remove_key m k1) k2 = get m k2;

  put: map -> K -> V -> map;
  get_put_same: forall (m: map) (k: K) (v: V), get (put m k v) k = Some v;
  get_put_diff: forall (m: map) (k1 k2: K) (v: V), k1 <> k2 -> get (put m k1 v) k2 = get m k2;

  intersect_map: map -> map -> map;
  intersect_map_spec: forall k v m1 m2,
      get (intersect_map m1 m2) k = Some v <-> get m1 k = Some v /\ get m2 k = Some v;

  put_map: map -> map -> map;
  get_put_map_l: forall m1 m2 k,
      get m2 k = None ->
      get (put_map m1 m2) k = get m1 k;
  get_put_map_r: forall m1 m2 k v,
      get m2 k = Some v ->
      get (put_map m1 m2) k = Some v;

}.

Arguments map _ _ {_}.


Hint Resolve
  empty_is_empty
  get_remove_same
  get_remove_diff
  get_put_same
  get_put_diff
  intersect_map_spec
  get_put_map_l
  get_put_map_r
: map_spec_hints_separate.


Section MapDefinitions.

  Context {K V: Type}.
  Context {KVmap: MapFunctions K V}.

  Context {keq: DecidableEq K}.
  Context {veq: DecidableEq V}.

  (* however, "rewrite get_intersect_map" (and probably others) won't pick up a veq typeclass
     in scope, and the rewrite will fail, so we prefer to hardcode an instance derived from
     KVMap: *)

  Definition extends(s1 s2: map K V) := forall x w, get s2 x = Some w -> get s1 x = Some w.

  Definition only_differ(s1: map K V)(ks: K -> Prop)(s2: map K V) :=
    forall x, ks x \/ get s1 x = get s2 x.

  Definition agree_on(s1: map K V)(ks: K -> Prop)(s2: map K V) :=
    forall x, ks x -> get s1 x = get s2 x.

  Definition undef_on(s: map K V)(ks: K -> Prop) := forall x, ks x -> get s x = None.

  Ltac prover :=
    intros;
    repeat match goal with
    | |- context[match ?d with _ => _ end] =>
      match type of d with
      | {_} + {_} => destruct d
      | _ => let E := fresh "E" in destruct d eqn: E
      end
    end;
    subst;
    eauto with map_spec_hints_separate.

  Lemma get_empty: forall (k: K),
      get empty_map k = None.
  Proof. prover. Qed.

  Lemma get_remove_key: forall (m: map K V) (x y: K),
    get (remove_key m x) y = if dec (x = y) then None else get m y.
  Proof. prover. Qed.

  Lemma get_put: forall (s: map K V) (x y: K) (v: V),
    get (put s x v) y = if dec (x = y) then Some v else get s y.
  Proof. prover. Qed.

  Lemma get_intersect_map: forall k m1 m2,
      get (intersect_map m1 m2) k =
      match get m1 k, get m2 k with
      | Some v1, Some v2 => if dec (v1 = v2) then Some v1 else None
      | _, _ => None
      end.
  Proof.
    clear keq. (* The proof term does not contain keq it even if we keep it, but after closing
      the section, it's added as a section var. And with "Proof using .", it seems it's used
      when attempting to Qed. Why?? *)
    (* Challenge: what's the minimal change to "prover" needed to make it work here too? *)
    intros.
    destruct (get (intersect_map m1 m2) k) eqn: E.
    - apply intersect_map_spec in E. destruct E as [E1 E2].
      rewrite E1. rewrite E2. destruct (dec (v = v)); congruence.
    - destruct (get m1 k) eqn: E1; destruct (get m2 k) eqn: E2; auto.
      destruct (dec (v = v0)); auto.
      subst v0.
      pose proof (intersect_map_spec k v m1 m2) as P.
      firstorder congruence.
  Qed.

  Lemma get_put_map: forall m1 m2 k,
      get (put_map m1 m2) k =
      match get m2 k with
      | Some v => Some v
      | None => get m1 k
      end.
  Proof. prover. Qed.

End MapDefinitions.

Hint Unfold extends only_differ agree_on undef_on : unf_map_defs.

Ltac one_rew_map_specs e rewriter :=
  match e with
  | context[get ?m] =>
    lazymatch m with
    | empty_map => rewriter get_empty
    | remove_key _ _ => rewriter (get_remove_key (keq := _))
    | put _ _ _ => rewriter (get_put (keq := _))
    | intersect_map _ _ => rewriter (get_intersect_map (veq := _))
    | put_map _ _ => rewriter get_put_map
    end
  end.

Ltac rew_map_specs_in H :=
  let rewriter lemma := rewrite lemma in H in
  repeat (let e := type of H in one_rew_map_specs e rewriter).

Ltac rew_map_specs_in_goal :=
  let rewriter lemma := (rewrite lemma) in
  repeat match goal with
         | |- ?G => one_rew_map_specs G rewriter
         end.

Ltac canonicalize_map_hyp H :=
  rew_map_specs_in H;
  try exists_to_forall H;
  try specialize (H eq_refl).

Ltac canonicalize_all K V :=
  repeat match goal with
         | H: _ |- _ => progress canonicalize_map_hyp H
         end;
  invert_Some_eq_Some;
  rew_map_specs_in_goal.

Ltac map_solver_should_destruct K V d :=
  let T := type of d in
  first [ unify T (option K)
        | unify T (option V)
        | match T with
          | {?x1 = ?x2} + {?x1 <> ?x2} =>
            let T' := type of x1 in
            first [ unify T' K
                  | unify T' V
                  | unify T' (option K)
                  | unify T' (option V) ]
          end ].

Ltac destruct_one_map_match K V :=
  destruct_one_match_hyporgoal_test ltac:(map_solver_should_destruct K V) ltac:(fun H => rew_map_specs_in H).

Ltac propositional :=
  repeat match goal with
         | |- forall _, _ => progress intros until 0
         | |- _ -> _ => let H := fresh "Hyp" in intro H
         | [ H: _ /\ _ |- _ ] =>
           let H1 := fresh H "_l" in
           let H2 := fresh H "_r" in
           destruct H as [H1 H2]
         | [ H: _ <-> _ |- _ ] =>
           let H1 := fresh H "_fwd" in
           let H2 := fresh H "_bwd" in
           destruct H as [H1 H2]
         | [ H: False |- _ ] => solve [ destruct H ]
         | [ H: True |- _ ] => clear H
         | [ H: exists (varname : _), _ |- _ ] =>
           let newvar := fresh varname in
           destruct H as [newvar H]
         | [ H: ?P |- ?P ] => exact H
         | |- _ /\ _ => split
         | [ H: ?P -> _, H': ?P |- _ ] =>
           match type of P with
           | Prop => specialize (H H')
           end
         | |- _ => progress subst *
         end.

Ltac propositional_ors :=
  repeat match goal with
         | [ H: _ \/ _ |- _ ] => destruct H as [H | H]
         | [ |- _ \/ _ ] => (left + right); congruence
         end.

Ltac ensure_no_body H := not (clearbody H).

Ltac pick_one_existential :=
  multimatch goal with
  | x: ?T |- exists (_: ?T), _ => exists x
  end.

Ltac map_solver K V :=
  assert_is_type K;
  assert_is_type V;
  repeat autounfold with unf_set_defs unf_map_defs in *;
  destruct_products;
  repeat match goal with
         | |- forall _, _ => progress intros until 0
         | |- _ -> _ => let H := fresh "Hyp" in intro H
         end;
  canonicalize_all K V;
  repeat match goal with
  | H: forall (x: ?E), _, y: ?E |- _ =>
    first [ unify E K | unify E V ];
    ensure_no_body H;
    match type of H with
    | DecidableEq E => fail 1
    | _ => let H' := fresh H y in
           pose proof (H y) as H';
           canonicalize_map_hyp H';
           ensure_new H'
    end
  | H: forall (x: _), _, y: ?E |- _ =>
    let T := type of E in unify T Prop;
    ensure_no_body H;
    let H' := fresh H y in
    pose proof H as H';
    specialize H' with (1 := y); (* might instantiate a few universally quantified vars *)
    canonicalize_map_hyp H';
    ensure_new H'
  | H: ?P -> _ |- _ =>
    let T := type of P in unify T Prop;
    let F := fresh in
    assert P as F by eauto;
    let H' := fresh H "_eauto" in
    pose proof (H F) as H';
    clear F;
    canonicalize_map_hyp H';
    ensure_new H'
  end;
  let solver := congruence || auto || (exfalso; eauto) ||
                match goal with
                | H: ~ _ |- False => solve [apply H; intuition (auto || congruence || eauto)]
                end in
  let fallback := (destruct_one_map_match K V || pick_one_existential);
                  canonicalize_all K V in
  repeat (propositional;
          propositional_ors;
          try solve [ solver ];
          try fallback).


(* ** ../bedrock2/compiler/src/util/MapSolverTest.v *)
(* Require Import compiler.Decidable. *)
(* Require Import compiler.util.Set. *)
(* Require Import compiler.util.Map. *)

Section Tests.

  Context {var: Type}. (* variable name (key) *)
  Context {dec_eq_var: DecidableEq var}.
  Context {val: Type}. (* value *)
  Context {dec_eq_val: DecidableEq val}.

  Context {stateMap: MapFunctions var val}.
  Notation state := (map var val).

  Ltac t := map_solver var val.

  Lemma extends_refl: forall s, extends s s.
  Proof. t. Qed.

  Lemma extends_trans: forall s1 s2 s3,
      extends s1 s2 ->
      extends s2 s3 ->
      extends s1 s3.
  Proof. t. Qed.

  Lemma extends_intersect_map_l: forall r1 r2,
      extends r1 (intersect_map r1 r2).
  Proof. t. Qed.

  Lemma extends_intersect_map_r:
    forall r1 r2, extends r2 (intersect_map r1 r2).
  Proof. t. Qed.

  Lemma extends_intersect_map_lr: forall m11 m12 m21 m22,
      extends m11 m21 ->
      extends m12 m22 ->
      extends (intersect_map m11 m12) (intersect_map m21 m22).
  Proof. t. Qed.

  Lemma intersect_map_extends: forall m1 m2 m,
      extends m1 m ->
      extends m2 m ->
      extends (intersect_map m1 m2) m.
  Proof. t. Qed.

  Lemma only_differ_union_l: forall s1 s2 r1 r2,
    only_differ s1 r1 s2 ->
    only_differ s1 (fun x => r1 x \/ r2 x) s2.
  Proof. t. Qed.

  Lemma only_differ_union_r: forall s1 s2 r1 r2,
    only_differ s1 r2 s2 ->
    only_differ s1 (fun x => r1 x \/ r2 x) s2.
  Proof. t. Qed.

  Lemma only_differ_one: forall s x v,
    only_differ s (fun y => x = y) (put s x v).
  Proof. t. Qed.

  Lemma only_differ_refl: forall s1 r,
    only_differ s1 r s1.
  Proof. t. Qed.

  Lemma only_differ_sym: forall s1 s2 r,
    only_differ s1 r s2 ->
    only_differ s2 r s1.
  Proof. t. Qed.

  Lemma only_differ_trans: forall s1 s2 s3 r,
    only_differ s1 r s2 ->
    only_differ s2 r s3 ->
    only_differ s1 r s3.
  Proof. t. Qed.

  Lemma undef_on_shrink: forall st (vs1 vs2: var -> Prop),
    undef_on st vs1 ->
    (forall v, vs2 v -> vs1 v) ->
    undef_on st vs2.
  Proof. t. Qed.

  Lemma only_differ_subset: forall s1 s2 (r1 r2: var -> Prop),
    (forall x, r1 x -> r2 x) ->
    only_differ s1 r1 s2 ->
    only_differ s1 r2 s2.
  Proof. t. Qed.

  Lemma extends_if_only_differ_in_undef: forall s1 s2 s vs,
    extends s1 s ->
    undef_on s vs ->
    only_differ s1 vs s2 ->
    extends s2 s.
  Proof. t. Qed.

  Lemma extends_if_only_differ_is_undef: forall s1 s2 vs,
    undef_on s1 vs ->
    only_differ s1 vs s2 ->
    extends s2 s1.
  Proof. t. Qed.

  Lemma extends_put_same: forall s1 s2 x v,
    extends s2 s1 ->
    extends (put s2 x v) (put s1 x v).
  Proof. t. Qed.

  Lemma only_differ_get_unchanged: forall s1 s2 x v d,
    get s1 x = v ->
    only_differ s1 d s2 ->
    ~  d x ->
    get s2 x = v.
  Proof. t. Qed.

  Lemma only_differ_put: forall s (d: var -> Prop) x v,
    d x ->
    only_differ s d (put s x v).
  Proof. t. Qed.

End Tests.


Set Ltac Profiling.

(** ** BEGIN LEMMAS *)

Section Lemmas.
  Context {K V: Type}.
  Context {Map: MapFunctions K V}.
  Context {K_eq_dec: DecidableEq K}.
  Context {V_eq_dec: DecidableEq V}.

  (** *** Part 1: Lemmas which hold *)

  Goal False. idtac "Part 1a: Small goals (originally took <5s each)". Abort.

  Lemma flattenExpr_correct_aux_lemma1:
    forall (resVar : K) (initialH initialL : map K V) (fvngs1 : K -> Prop) (v0 : V),
      extends initialL initialH ->
      undef_on initialH fvngs1 -> get (put initialL resVar v0) resVar = Some v0.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenExpr_correct_aux_lemma2:
    forall (x resVar : K) (initialH initialL : map K V) (res : V) (fvngs1 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs1 ->
      get initialH x = Some res -> get (put initialL resVar res) resVar = get initialH x.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenExpr_correct_aux_lemma3:
    forall (initialH initialL : map K V) (v : K) (fvngs1 : K -> Prop) (v0 : K)
           (fvn fvn0 mvs1 mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs1 ->
      subset fvn0 fvn ->
      subset fvn fvngs1 ->
      v0 \in mvs1 ->
      v \in mvs0 ->
      subset mvs1 (diff fvn fvn0) -> subset mvs0 (diff fvngs1 fvn) -> undef_on initialH fvngs1.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenExpr_correct_aux_lemma4:
    forall (initialH initialL : map K V) (v v0 : K) (midL : map K V) (fvngs1 : K -> Prop)
           (w : V) (fvn fvn0 mvs1 mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs1 ->
      subset fvn0 fvn ->
      subset fvn fvngs1 ->
      v0 \in mvs1 ->
      v \in mvs0 ->
      subset mvs1 (diff fvn fvn0) ->
      subset mvs0 (diff fvngs1 fvn) ->
      get midL v = Some w -> only_differ initialL mvs0 midL -> extends midL initialH.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenExpr_correct_aux_lemma5:
    forall (initialH initialL : map K V) (v v0 : K) (midL : map K V) (fvngs1 : K -> Prop)
           (w : V) (fvn fvn0 mvs1 mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs1 ->
      subset fvn0 fvn ->
      subset fvn fvngs1 ->
      v0 \in mvs1 ->
      v \in mvs0 ->
      subset mvs1 (diff fvn fvn0) ->
      subset mvs0 (diff fvngs1 fvn) ->
      get midL v = Some w -> only_differ initialL mvs0 midL -> undef_on initialH fvn.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenExpr_correct_aux_lemma6:
    forall (initialH initialL : map K V) (v v0 : K) (midL : map K V) (fvngs1 : K -> Prop)
           (w w0 : V) (fvn fvn0 mvs1 mvs0 : K -> Prop) (preFinalL : map K V),
      extends initialL initialH ->
      undef_on initialH fvngs1 ->
      subset fvn0 fvn ->
      subset fvn fvngs1 ->
      v0 \in mvs1 ->
      v \in mvs0 ->
      subset mvs1 (diff fvn fvn0) ->
      subset mvs0 (diff fvngs1 fvn) ->
      get midL v = Some w ->
      only_differ initialL mvs0 midL ->
      get preFinalL v0 = Some w0 -> only_differ midL mvs1 preFinalL -> get preFinalL v = Some w.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenStmt_correct_aux_lemma7:
    forall (initialH initial2L initialL : map K V) (fvngs emv : K -> Prop)
           (cv Z0 : V) (v : K) (fvn mvcondL fvn0 fvngs' : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      disjoint emv fvngs ->
      cv <> Z0 ->
      subset fvn fvngs ->
      v \in mvcondL ->
      subset mvcondL (diff fvngs fvn) ->
      subset fvngs' fvn0 ->
      subset fvn0 fvn ->
      get initial2L v = Some cv ->
      only_differ initialL mvcondL initial2L -> extends initial2L initialH.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenStmt_correct_aux_lemma8:
    forall (initialH initial2L initialL : map K V) (fvngs emv : K -> Prop)
           (cv Z0 : V) (v : K) (fvn mvcondL fvn0 fvngs' : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      disjoint emv fvngs ->
      cv <> Z0 ->
      subset fvn fvngs ->
      v \in mvcondL ->
      subset mvcondL (diff fvngs fvn) ->
      subset fvngs' fvn0 ->
      subset fvn0 fvn ->
      get initial2L v = Some cv ->
      only_differ initialL mvcondL initial2L ->
      undef_on initialH fvn.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenStmt_correct_aux_lemma_rewrite_get_key:
    forall (lhs : K) (initialH initialL : map K V) (fvngs' emv : K -> Prop),
      extends initialL initialH ->
      disjoint emv fvngs' ->
      undef_on initialH fvngs' ->
      extends initialL (remove_key initialH lhs).
  Proof.
    Time map_solver K V.
  Qed.


  Goal False. idtac "Part 1b: Medium goals (originally took >5s each)". Abort.

  Lemma flattenStmt_correct_aux_lemma1:
    forall (lhs : K) (initialH initialL : map K V) (fvngs emv : K -> Prop)
           (v : V) (v0 : K) (prefinalL : map K V) (fvngs' mvs : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      disjoint emv fvngs ->
      get prefinalL v0 = Some v ->
      subset fvngs' fvngs ->
      only_differ initialL mvs prefinalL ->
      v0 \in mvs ->
      subset mvs (diff fvngs fvngs') -> extends (put prefinalL lhs v) (put initialH lhs v).
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenStmt_correct_aux_lemma2:
    forall (initialH initialL : map K V) (fvngs emv : K -> Prop) (av : V)
           (v v0 : K) (prefinalL : map K V) (fvn fvngs' mvs mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      disjoint emv fvngs ->
      get prefinalL v = Some av ->
      subset fvngs' fvn ->
      subset fvn fvngs ->
      only_differ initialL mvs prefinalL ->
      v0 \in mvs0 ->
      v \in mvs ->
      subset mvs0 (diff fvn fvngs') ->
      subset mvs (diff fvngs fvn) ->
      extends prefinalL initialH.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenStmt_correct_aux_lemma3:
    forall (initialH initialL : map K V) (fvngs emv : K -> Prop) (av : V)
           (v v0 : K) (prefinalL : map K V) (fvn fvngs' mvs mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      disjoint emv fvngs ->
      get prefinalL v = Some av ->
      subset fvngs' fvn ->
      subset fvn fvngs ->
      only_differ initialL mvs prefinalL ->
      v0 \in mvs0 ->
      v \in mvs ->
      subset mvs0 (diff fvn fvngs') -> subset mvs (diff fvngs fvn) -> undef_on initialH fvn.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenStmt_correct_aux_lemma4:
    forall (initialH initialL : map K V) (fvngs : K -> Prop) (av vv : V) (v v0 : K)
           (prefinalL finalL : map K V) (fvn fvngs' mvs mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      disjoint empty_set fvngs ->
      get prefinalL v = Some av ->
      get finalL v0 = Some vv ->
      subset fvngs' fvn ->
      subset fvn fvngs ->
      only_differ initialL mvs prefinalL ->
      only_differ prefinalL mvs0 finalL ->
      v0 \in mvs0 ->
      v \in mvs ->
      subset mvs0 (diff fvn fvngs') -> subset mvs (diff fvngs fvn) -> get finalL v = Some av.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenStmt_correct_aux_lemma5:
    forall (initialH initialL : map K V) (fvngs : K -> Prop) (av vv : V) (v v0 : K)
           (prefinalL finalL : map K V) (fvn fvngs' mvs mvs0 : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      disjoint empty_set fvngs ->
      get prefinalL v = Some av ->
      get finalL v0 = Some vv ->
      subset fvngs' fvn ->
      subset fvn fvngs ->
      only_differ initialL mvs prefinalL ->
      only_differ prefinalL mvs0 finalL ->
      v0 \in mvs0 ->
      v \in mvs ->
      subset mvs0 (diff fvn fvngs') -> subset mvs (diff fvngs fvn) -> get finalL v = Some av.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenStmt_correct_aux_lemma9:
    forall (v : K) (st2 middleL initialH initialL : map K V) (fvngs emv : K -> Prop)
           (cv Z0 : V) (initial2L : map K V) (fvn mvsCond fvngs' mvsBody : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      disjoint emv fvngs ->
      cv <> Z0 ->
      get initial2L v = Some cv ->
      subset fvn fvngs ->
      only_differ initialL mvsCond initial2L ->
      v \in mvsCond ->
      subset mvsCond (diff fvngs fvn) ->
      subset fvngs' fvngs ->
      subset fvngs' fvn ->
      extends middleL st2 -> only_differ initial2L mvsBody middleL -> extends middleL st2.
  Proof.
    Time map_solver K V.
  Qed.

  Lemma flattenStmt_correct_aux_lemma10:
    forall (v : K) (st2 middleL initialH initialL : map K V) (fvngs emv : K -> Prop)
           (cv Z0 : V) (initial2L : map K V) (fvn mvsCond fvngs' mvsBody : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      disjoint emv fvngs ->
      cv <> Z0 ->
      get initial2L v = Some cv ->
      subset fvn fvngs ->
      only_differ initialL mvsCond initial2L ->
      v \in mvsCond ->
      subset mvsCond (diff fvngs fvn) ->
      subset fvngs' fvngs ->
      subset fvngs' fvn ->
      extends middleL st2 ->
      only_differ initial2L mvsBody middleL ->
      only_differ initialH emv st2 ->
      undef_on st2 fvngs.
  Proof.
    Time map_solver K V.
  Qed.

  Goal False. idtac "Part 1c: Large goals (originally took >50s each)". Abort.

  Lemma flattenStmt_correct_aux_lemma6:
    forall (initialH initialL : map K V) (fvngs emv : K -> Prop) (av vv : V)
           (v v0 : K) (prefinalL finalL : map K V) (fvn fvngs' mvs0 mvs : K -> Prop),
      extends initialL initialH ->
      undef_on initialH fvngs ->
      disjoint emv fvngs ->
      get prefinalL v = Some av ->
      get finalL v0 = Some vv ->
      subset fvngs' fvn ->
      subset fvn fvngs ->
      only_differ prefinalL mvs0 finalL ->
      only_differ initialL mvs prefinalL ->
      v0 \in mvs0 ->
      v \in mvs ->
      subset mvs0 (diff fvn fvngs') -> subset mvs (diff fvngs fvn) -> extends finalL initialH.
  Proof.
    Time map_solver K V.
  Qed.

End Lemmas.

Show Ltac Profile.
