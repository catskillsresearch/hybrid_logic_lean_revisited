import Mathlib.Logic.Basic
import Mathlib.Data.List.Sort
open Classical

-- Compatibility shim: mathlib removed `List.Sorted` (which was definitionally
-- `List.Pairwise`). We restore it as a reducible abbreviation so that the
-- existing development and the current mathlib `Pairwise` lemmas interoperate.
abbrev List.Sorted {a : Type _} (r : a  ->  a  ->  Prop) (l : List a) : Prop := l.Pairwise r

theorem test (a b : Nat) : a = b  ->  a + 1 = b + 1 := by intro h; simp [h]

def TypeIff (a : Type u) (b : Type v) := Prod (a  ->  b) (b  ->  a)
def TypeIff.intro (a : Type u) (b : Type v) : (a  ->  b)  ->  (b  ->  a)  ->  (TypeIff a b) := by
  apply Prod.mk
def TypeIff.mp  (p : TypeIff a b) : a  ->  b := p.1
def TypeIff.mpr (p : TypeIff a b) : b  ->  a := p.2
def TypeIff.refl : TypeIff a a := by
  apply TypeIff.intro <;> (intro; assumption)
def TypeIff.trans {h1 : TypeIff a b} {h2 : TypeIff b c} : TypeIff a c := by
  apply TypeIff.intro
  . intro h
    exact h2.mp (h1.mp h)
  . intro h
    exact h1.mpr (h2.mpr h)
infix:300 "iff" => TypeIff

noncomputable def choice_intro (q : a  ->  Sort u) (p : a  ->  Prop) (P : exists  a, p a) : (forall  a, p a  ->  q a)  ->  q P.choose := by
  intro h
  exact (h P.choose P.choose_spec)

theorem eq_symm : (a = b)  <->  (b = a) := by
  apply Iff.intro <;> intro h <;> exact h.symm

@[simp]
theorem double_negation : not not p  <->  p :=
  Iff.intro
  (fun  h =>
    Or.elim (Classical.em p)
    (fun  hp  => hp)
    (fun  hnp => absurd hnp h)
  )
  (fun  p => fun  np => absurd p np)

@[simp]
theorem implication_disjunction : (p  ->  q)  <->  (not p  \/  q) := by
  apply Iff.intro
  . intro impl
    exact byCases
      (fun  hp  :  p => Or.inr (impl hp))
      (fun  hnp : not p => Or.inl hnp)
  . intros disj hp
    exact Or.elim disj
      (fun  hnp : not p => False.elim (hnp hp))
      (fun  hq  :  q => hq)

@[simp]
theorem negated_disjunction : not (p  \/  q)  <->  not p  /\  not q :=
  Iff.intro
    (fun hpq : not (p  \/  q) =>
      And.intro
        (fun hp : p =>
          show False from hpq (Or.intro_left q hp)
        )
        (fun hq : q =>
          show False from hpq (Or.intro_right p hq)
        )
    )
    (fun hpq : not p  /\  not q =>
      (fun disj : p  \/  q =>
        show False from
          Or.elim
           disj
           (fun hp : p => hpq.left hp)
           (fun hq : q => hpq.right hq)
      )
    )

@[simp]
theorem negated_conjunction : not (p  /\  q)  <->  not p  \/  not q := by
  apply Iff.intro
  . intro h
    by_cases hp : p
    . by_cases hq : q
      . exact False.elim (h <hp, hq>)
      . apply Or.inr
        assumption
    . apply Or.inl
      assumption
  . intro h
    intro hpq
    apply Or.elim h
    . intro hnp
      exact hnp hpq.left
    . intro hnq
      exact hnq hpq.right

@[simp]
theorem negated_impl : not (p  ->  q)  <->  p  /\  not q :=
  Iff.intro
    (fun hyp : not (p  ->  q) =>
      byCases
      -- case 1 : p
        (fun hp : p =>
          byCases
          -- case 1.a : p and q
            (fun hq : q =>
              <
                hp, show not q from (fun _ => show False from hyp (fun _ => hq))
              >
            )
          -- case 1.b : p and non q
            (fun hnq : not q => <hp, hnq>)
        )
      -- case 2 : non p
        (fun hnp : not p => show (p  /\  not q) from False.elim
          (show False from hyp
            (show (p  ->  q) from fun p : p =>
              (show q from False.elim (hnp p))
            )
          )
        )
    )
    (fun hyp : p  /\  not  q =>
      fun impl : p  ->  q =>
        absurd (impl hyp.left) hyp.right
    )

universe u
@[simp]
theorem negated_universal {a : Type u} {p : a  ->  Prop} : (not  forall  x, p x)  <->  (exists  x, not  p x) :=
    Iff.intro
    (fun h1 : not  forall  x, p x =>
      byContradiction
      (fun hcon1 : not  exists  x, not  p x =>
        have neg_h1 := (fun a : a =>
          byContradiction
          (fun hcon2 : not  p a => show False from hcon1 (<a, hcon2>))
        )
        show False from h1 neg_h1
      )
    )
    (fun h2 : exists  x, not  p x =>
      (fun hxp : forall  x, p x =>
        match h2 with
        | <w, hw> => show False from hw (hxp w)
      )
    )

@[simp]
theorem negated_existential {a : Type u} {p : a  ->  Prop} : (not  exists  x, p x)  <->  (forall  x, not  p x) :=
    Iff.intro
    (fun h1 : not  exists  x, p x =>
      (fun a : a =>
        fun hpa: p a => show False from h1 <a, hpa>
      )
    )
    (fun h2 : forall  x, not  p x =>
      (fun hex : exists  x, p x =>
        match hex with
        | <w, hw> => show False from (h2 w) hw
      )
    )

@[simp]
theorem conj_comm : p  /\  q  <->  q  /\  p :=
  Iff.intro
    (fun hpq : p  /\  q =>
      <hpq.right, hpq.left>
    )
    (fun hqp : q  /\  p =>
      <hqp.right, hqp.left>
    )

theorem disj_comm : p  \/  q  <->  q  \/  p :=
  Iff.intro
    (fun hpq : p  \/  q =>
      Or.elim
        hpq
        (fun hp : p => Or.intro_right q hp)
        (fun hq : q => Or.intro_left p hq)
    )
    (fun hqp : q  \/  p =>
      Or.elim
        hqp
        (fun hq : q => Or.intro_right p hq)
        (fun hp : p => Or.intro_left q hp)
    )

theorem contraposition (p q : Prop) : (p  ->  q)  <->  (not q  ->  not p) := by
  apply Iff.intro
  . intro hpq
    intro hnq hp
    exact hnq (hpq hp)
  . intro hnqp
    intro hp
    by_cases c : q
    . exact c
    . exact False.elim ((hnqp c) hp)
