import Hybrid.Tautology

theorem empty_list (L : List {x : Form N | False}) : L = [] := by
  match L with
  | [] => rfl
  | h :: t =>
      exact h.2.elim

def List.max_form {Gamma : Set (Form N)} : List Gamma  ->  (Form N  ->  Nat)  ->  Nat
| .nil, f      => f False
| .cons h t, f => if (f h) > (t.max_form f) then (f h) else (t.max_form f)

theorem List.max_is_max {Gamma : Set (Form N)} (L : List Gamma) (f : Form N  ->  Nat) : forall  phi, phi  in  L  ->  f phi  <=  L.max_form f := by
  intro phi in_list
  induction L with
  | nil => contradiction
  | cons h t ih =>
      simp at in_list
      apply Or.elim in_list
      . intro hyp
        rw [hyp, max_form]
        split
        . apply Nat.le.refl
        . simp at *
          assumption
      . intro hyp
        rw [max_form]
        have ih := ih hyp
        by_cases hc : f h > max_form t f
        . simp [hc]
          exact Nat.le_trans ih (Nat.le_of_lt hc)
        . simp [hc]
          exact ih

-- The standard implementation of these coerces the list
-- to the type of element we are filtering / searching.
-- It's overkill to coerce the whole list. We can use
-- h.val to compare an formula h : Set (Form N) to a formula
-- phi : Form.
def filter' {Gamma : Set (Form N)} : List Gamma  ->  Form N  ->  List Gamma
| [],   _   => []
| h::t, phi => match h.val == phi with
  | true  => filter' t phi
  | false => h::(filter' t phi)

def elem' {Gamma : Set (Form N)} : List Gamma  ->  Form N  ->  Bool
| [], _    => false
| h::t, phi => match h.val == phi with
  | true  => true
  | false => elem' t phi

theorem filter'_filters {Gamma : Set (Form N)} {phi : Form N} {L : List (Gamma  U  {phi})} : not elem' (filter' L phi) phi := by
  induction L with
  | nil           => simp [filter', elem']
  | cons h t ih   => cases c : h == phi
                     repeat simp [filter', c, elem', ih]

theorem filter'_doesnt_filter {Gamma : Set (Form N)} {L : List Gamma} (hyp : not elem' L phi) : (filter' L phi) = L := by
  induction L with
  | nil         => simp [filter']
  | cons h t ih => cases c : h == phi
                   . simp [elem', c] at hyp
                     simp [filter', elem', c, ih, hyp]
                   . simp [elem', c] at hyp

-- Trivial fact, ugly implementation (but it works!):
--    Let Gamma and Delta be two sets of formulas s.t. Gamma  subseteq  Delta.
--    Then, any list L of formulas taken from Gamma can be
--      converted to a list L' of formulas from Delta
--      s.t. L and L' have the same elements.
def list_convert_general {Gamma Delta : Set (Form N)} (h_incl : Gamma  subseteq  Delta) (L : List Gamma) : List Delta :=
  match L with
  | []      => []
  | h :: t  => <h.val, (h_incl h.prop)> :: list_convert_general h_incl t

--  And any conjunction of elements from Gamma is a conjunction
--    of elements from Delta.
theorem conj_incl_general {Gamma Delta : Set (Form N)} (h_incl : Gamma  subseteq  Delta) (L : List Gamma) : conjunction Gamma L = conjunction Delta (list_convert_general h_incl L) := by
  match L with
  | []      =>
      simp [conjunction, list_convert_general]
  | h :: t  =>
      simp only [conjunction, list_convert_general]
      rw [conj_incl_general h_incl t]

--    Let Gamma be a set of formulas and psi a formula.
--    Then, any list L of formulas taken from Gamma can be
--      converted to a list L' of formulas from Gamma  U  {psi}
--      s.t. L and L' have the same elements.
def list_convert {Gamma : Set (Form N)} {psi : Form N} (L : List Gamma) : List (Gamma  U  {psi}) := by
  have incl : Gamma  subseteq  (Gamma  U  {psi}) := by simp
  apply list_convert_general incl L

-- Any conjunction of formulas from Gamma is a conjunction
-- of formulas from Gamma  U  {psi}.
theorem conj_incl {Gamma : Set (Form N)} {psi : Form N} (L : List Gamma) : conjunction Gamma L = conjunction (Gamma  U  {psi}) (list_convert L) := by
  have incl : Gamma  subseteq  (Gamma  U  {psi}) := by simp
  exact conj_incl_general incl L


-- If L is a list of elements from Gamma  U  {phi}, and phi  notin  L,
-- then we can convert L to a list L' of elements from Gamma,
--   s.t. L and L' have the same elements.
--   duuuh
theorem help {a : Type u} {Gamma : Set a} {phi psi : a} (h1 : phi  in  (Gamma  U  {psi})) (h2 : phi  !=  psi) : phi  in  Gamma := by
  simp [h2] at h1
  exact h1

theorem help2 {Gamma : Set (Form N)} {h : Gamma} {a : Form N} {t : List Gamma} : elem' (h::t) a = false  ->  (elem' t a) = false := by
  intro hyp
  cases c : h.val == a
  . simp [elem', c] at hyp
    exact hyp
  . simp [elem', c] at hyp

def list_convert_rev {Gamma : Set (Form N)} {psi : Form N} (L : List (Gamma  U  {psi})) (hyp : elem' L psi = false) : List Gamma :=
  match L with
  | []     => []
  | h ::t  => dite (psi = h)
                (fun  _ => list_convert_rev t (help2 hyp))
                (fun  neq => by
                    have prop := help h.prop (Ne.symm neq)
                    exact <h.val, prop> :: (list_convert_rev t (help2 hyp))
                )

-- Any conjunction of formulas from Gamma  U  {psi} that doesn't include psi
-- is a conjunction of formulas from Gamma.
theorem conj_incl_rev {Gamma : Set (Form N)} {psi : Form N} (L : List (Gamma  U  {psi})) (hyp : elem' L psi = false): conjunction (Gamma  U  {psi}) L = conjunction Gamma (list_convert_rev L hyp) := by
  match L with
  | []      =>
      simp [conjunction, list_convert_rev]
  | h :: t  =>
      by_cases eq : psi = h
      . simp [elem', eq] at hyp
      . simp [list_convert_rev, eq, conjunction]
        exact conj_incl_rev t (help2 hyp)

-- This might be the ugliest Lean code I've written.
-- What this says is that if you have two sets of formulas, Gamma and Delta,
--  and some conjunction of formulas in Gamma such that all formulas in that
--  conjunction belong to Delta as well;
--    then that conjunction of Gamma-formulas is also a conjunction of Delta-formulas.
-- *So* trivially sounding, but such a pain to prove! Due to the typing system
--    which makes Gamma and Delta behave as different (sub)types.
--
-- This is used in Lemma LindenbaumConsistent.
theorem conj_incl_linden {Gamma Delta : Set (Form N)} (L : List Gamma) (hyp : {phi | phi  in  L}  subseteq  Delta): exists  L', conjunction Gamma L = conjunction Delta L' := by
  induction L with
  | nil =>
      let L' : List Delta := []
      exists L'
  | cons h t ih =>
      rw [conjunction]
      have : {x | exists  phi, phi  in  t  /\  phi = x}  subseteq  Delta := by
        intro x x_mem
        simp only [Set.mem_setOf_eq] at x_mem
        simp only [List.mem_cons] at hyp
        let <phi, a, b> := x_mem
        have : exists  phi, (phi = h  \/  phi  in  t)  /\  phi = x := by
          exists phi
          apply And.intro
          . apply Or.inr a
          . exact b
        clear phi a b
        exact hyp this
      let <L'', conj> := ih this
      let h_d : Delta := <h, by
          have h_d_mem : exists  phi, phi  in  (h :: t)  /\  phi.val = h := by simp
          exact hyp h_d_mem
        >
      have : h_d.val = h.val := rfl
      let L' := h_d :: L''
      exists L'
      rw [conjunction, this, conj]

theorem conj_idempotent {e : Eval N} {Gamma : Set (Form N)} {L : List Gamma} (hyp : elem' L phi) : e.f (conjunction Gamma L)  /\  e.f phi  <->  e.f (conjunction Gamma L) := by
  induction L with
  | nil => simp [elem'] at hyp
  | cons h t ih =>
      by_cases eq : h.val == phi
      . have := Eq.symm (beq_iff_eq.mp eq)
        simp only [conjunction, e_conj, this, conj_comm, and_self_left]
      . simp [elem', show (h.val == phi) = false by simp [eq]] at hyp
        simp only [conjunction, e_conj, and_assoc, ih hyp]

-- Instead of proving conjunction is associative, commutative and idempotent, we do 3-in-1:
theorem conj_helper {e : Eval N} {Gamma : Set (Form N)} {L : List Gamma} (hyp : elem' L phi) : e.f (conjunction Gamma (filter' L phi) /\ phi) = true  <->  e.f (conjunction Gamma L) = true := by
  induction L with
  | nil         =>
      simp [elem'] at hyp
  | cons h t ih =>
      by_cases eq : h.val == phi
      . simp only [filter', eq, conjunction]
        have := beq_iff_eq.mp eq
        rw [this]
        by_cases phi_in_t : elem' t phi
        . conv => rhs; rw [e_conj, and_comm, conj_idempotent phi_in_t]
          simp only [ih, phi_in_t]
        . simp only [filter'_doesnt_filter phi_in_t, e_conj, and_comm]
      . simp [elem', eq] at hyp
        simp only [hyp, e_conj, conj_comm, forall_true_left] at ih
        rw [and_comm] at ih
        simp only [filter', eq, conjunction, e_conj, and_assoc, ih]

theorem deduction_helper {Gamma : Set (Form N)} (L : List Gamma) (phi psi : Form N) (h : elem' L phi) :
  Tautology ((conjunction Gamma L  -->  psi)  -->  (conjunction Gamma (filter' L phi)  -->  phi  -->  psi)) := by
  intro e
  rw [e_impl, e_impl, e_impl, e_impl]
  intro h1 h2 h3
  have l1 := (@e_conj N (conjunction Gamma (filter' L phi)) phi e).mpr <h2, h3>
  rw [conj_helper h] at l1
  exact h1 l1
