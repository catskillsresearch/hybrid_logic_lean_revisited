import Hybrid.Substitutions
import Hybrid.ProofUtils
import Hybrid.FormCountable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Group.Even

open Classical

-- First, we define how to obtain Γᵢ₊₁ from Γᵢ, given a formula φ:
def lindenbaum_next (Γ : Set (Form N)) (φ : Form N) : Set (Form N) :=
  if consistent (Γ ∪ {φ}) then
    match φ with
    | ex x, ψ =>
        if c : ∃ i : NOM N, all_nocc i (Γ ∪ {φ}) then
          Γ ∪ {φ} ∪ {ψ[c.choose // x]}
        else
          Γ ∪ {φ}
    | _       =>  Γ ∪ {φ}
  else
    Γ

-- Now we define the whole indexed family Γᵢ.
-- Usually, the enumeration of formulas starts from 1 (φ₁, φ₂, ...), and
--    Γ₀ = Γ .
-- However, in Lean it's much tidier to enumerate from 0 (φ₀, φ₁, ...), so
--    Γ₀ = Γ ∪ {φ₀} if it is consistent and Γ₀ = Γ otherwise.
def lindenbaum_family (enum : Nat → Form N) (Γ : Set (Form N)) : Nat → Set (Form N)
| .zero   => lindenbaum_next Γ (enum 0)
| .succ n =>
    let prev_set := lindenbaum_family enum Γ n
    lindenbaum_next prev_set (enum (n+1))

notation Γ "(" i "," e ")" => lindenbaum_family e Γ i

def LindenbaumMCS (enum : Nat → Form N) (Γ : Set (Form N)) (_ : consistent Γ) : Set (Form N) :=
    {φ | ∃ i : Nat, φ ∈ Γ (i, enum)}

-- Lemma: All Γᵢ belong to LindenbaumMCS Γ
lemma all_sets_in_family{enum : ℕ → Form N} {Γ : Set (Form N)} {c : consistent Γ} : ∀ n, Γ (n, enum) ⊆ LindenbaumMCS enum Γ c := by
  intro i φ h
  exists i

lemma all_sets_in_family_tollens {enum : ℕ → Form N} {Γ : Set (Form N)} {c : consistent Γ} : φ ∉ (LindenbaumMCS enum Γ c) → ∀ n, φ ∉ Γ (n, enum) := by
  rw [contraposition, not_not, not_forall]
  intro h
  let ⟨i, hi⟩ := h
  rw [not_not] at hi
  exact all_sets_in_family i hi

-- Lemma: If Γ is consistent, then for all φ, lindenbaum_next Γ φ is consistent
lemma consistent_lindenbaum_next (Γ : Set (Form N)) (hc : consistent Γ) (φ : Form N) : consistent (lindenbaum_next Γ φ) := by
  unfold lindenbaum_next
  split
  . split
    . next x ψ h =>
      split
      . next hnom =>
        let i := Exists.choose hnom
        have not1 : i = Exists.choose hnom := rfl
        have i_sat := Exists.choose_spec hnom
        have not2 : (ex x, ψ) = ((all x, ψ⟶⊥)⟶⊥) := by simp
        rw [←not1, ←not2, consistent]
        intro hyp
        have ⟨L, habs⟩ := Proof.Deduction.mpr hyp
        let χ := conjunction (Γ ∪ {ex x, ψ}) L
        have not3 : χ = conjunction (Γ ∪ {ex x, ψ}) L := rfl
        rw [←not3] at habs
        let y := (χ⟶ψ).new_var
        have y_ge : y ≥ (χ⟶ψ).new_var := Nat.le.refl
        have : y ≥ (χ⟶(ψ[i//x])⟶⊥).new_var := ge_new_var_subst_helpr y_ge
        have habs := (Proof.generalize_constants i this) habs
        rw [nom_subst_svar, nom_subst_svar] at habs
        have nocc0 : occurs y χ = false := by apply ge_new_var_is_new; exact (new_var_geq1 y_ge).left
        have nocc1 : nom_occurs i χ = false := all_noc_conj i_sat L
        conv at i_sat =>
          rw [←not1, ←not2, all_nocc, Set.union_singleton]
          intro φ; rw [Set.mem_insert_iff]
        have nocc2 : nom_occurs i (ex x, ψ) = false := by apply (i_sat (ex x, ψ)); simp
        rw [not2] at nocc2
        simp only [nom_occurs, or_false, Bool.or_false] at nocc2
        rw [nom_subst_nocc nocc1, subst_collect_all_nocc nocc2] at habs
        have := Proof.ax_q1 χ (ψ[y//x]⟶⊥) (notoccurs_notfree nocc0)
        have habs := Proof.mp this habs
        have habs : Σ L, ⊢(conjunction (Γ ∪ {ex x, ψ}) L⟶all y, ψ[y//x]⟶⊥) := ⟨L, habs⟩
        rw [←SyntacticConsequence, ←Form.neg] at habs
        have : ⊢((all y, ∼(ψ[y//x])) ⟶ (all x, ∼ψ)) := by
          apply Proof.iff_mpr
          apply Proof.rename_bound
          apply ge_new_var_is_new
          rw [new_var_neg]
          exact (new_var_geq1 y_ge).right
          rw [subst_neg]
          apply new_var_subst'' (new_var_geq1 y_ge).right
        have := Proof.Γ_theorem this (Γ ∪ {ex x, ψ})
        have habs := Proof.Γ_mp this habs
        have : (Γ ∪ {ex x, ψ}) ⊢ (ex x, ψ) := by apply Proof.Γ_premise; simp
        have := Proof.Γ_mp this habs
        exact h this
      . assumption
    . assumption
  . assumption


-- Lemma: If you can consistently extend (lindenbaum_next Γ φ) with φ, then
--    φ already belongs to (lindenbaum_next Γ φ)
lemma maximal_lindenbaum_next {Γ : Set (Form N)} (hc : consistent ((lindenbaum_next Γ φ) ∪ {φ})) : φ ∈ lindenbaum_next Γ φ := by
  revert hc
  unfold lindenbaum_next
  split
  . split
    . split <;> simp
    . intro; simp
  . intro; contradiction

--
-- Now apply the previous lemmas to the family as a whole.
--

-- Lemma: If Γ is consistent, then all Γᵢ are consistent.
lemma consistent_family {Γ : Set (Form N)} (e : ℕ → Form N) (c : consistent Γ) : ∀ n, consistent (Γ (n, e)) := by
  intro n
  induction n <;> (
      simp only [lindenbaum_family]
      apply consistent_lindenbaum_next
      assumption
  )

-- Lemma: If φ doesn't belong to the set in the family corresponding to its place in the enumeration,
--     (i.e., φ ∉ Γᵢ, where i = f φ),
--    then Γᵢ ∪ {φ} must be inconsistent.
lemma maximal_family {Γ : Set (Form N)} {f : Form N → ℕ} (f_inj : f.Injective) {e : ℕ → Form N} (e_inv : e = f.invFun) :
    ¬φ ∈ Γ (f φ, e) → ¬consistent (Γ (f φ, e) ∪ {φ}) := by
    rw [contraposition, not_not, not_not]
    unfold lindenbaum_family
    cases heq : f φ with
    | zero =>
        simp only
        have by_inv : e (f φ) = φ := by simp [f.leftInverse_invFun f_inj φ, e_inv]
        rw [show 0 = f φ by simp [heq], by_inv]
        intro h
        apply maximal_lindenbaum_next
        exact h
    | succ n =>
        simp only
        have by_inv : e (f φ) = φ := by simp [f.leftInverse_invFun f_inj φ, e_inv]
        simp only [show (n+1) = f φ by simp [heq], by_inv]
        intro h
        apply maximal_lindenbaum_next
        exact h

-- todo: Include here that Γ ⊆ Γᵢ for all i
lemma increasing_family : i ≤ j → Γ (i, e) ⊆ Γ (j, e) := by
  intro h
  induction h with
  | refl => simp [subset_of_eq]
  | @step m _ ih =>
      simp only [lindenbaum_family, lindenbaum_next]
      split
      . intro _ φ_member
        have incl : Γ(m, e) ⊆ (Γ(m, e) ∪ {e (m + 1)}) := by simp
        split ; split
        . rw [Set.union_singleton]
          apply Set.subset_insert
          exact incl (ih φ_member)
        . exact incl (ih φ_member)
        . exact incl (ih φ_member)
      . assumption

lemma Γ_in_family : Γ ⊆ Γ (i, e) := by
  induction i with
  | zero =>
      simp only [lindenbaum_family, lindenbaum_next]
      split ; split ; split
      . apply subset_trans
        have : Γ ⊆ Γ ∪ {e 0} := by simp
        exact this
        simp
      . simp
      . simp
      . apply subset_of_eq
        simp
  | succ n ih =>
      apply subset_trans
      apply ih
      apply increasing_family
      apply Nat.le_succ

-- Now we want to show that Γ' = LindenbaumMCS e Γ is consistent.
--
-- (f is an injection Form → ℕ  ; e is its (left) inverse ℕ → Form N)
--
-- Assume Γ' is inconsistent.
--  That means that there is list of elements L of that set
--  such that their conjunction proves a contradiction.
--
-- L : List (LindenbaumMCS e Γ)
--   there is a "maximum formula" in L, (Prove!)
--   i.e. a formula φ s.t. for all ψ ≠ φ in L f(φ) > f(ψ)
-- Clearly, φ ∈ lindenbaum_family e Γ f(φ). (lemma in_set)
-- Now, we know that for all formulas ψ, if f(ψ) <= n, then
--    ψ ∈ lindenbaum_family e Γ n. (Prove!)
-- So since φ is the greatest element in L, then all elements in L
--    are elements in lindenbaum_family e Γ f(φ).
-- So in fact L only contains elements from lindenbaum_family e Γ f(φ),
--    not from the whole MCS.
--
-- We know that if Γ is consistent, then for all n, lindenbaum_family e Γ n
--    is consistent. (lemma consistent_family).
-- So lindenbaum_family e Γ f(φ) is consistent.
-- So no conjunction of elements in L can prove a contradiction.
--
--    This completes our reductio proof.
--    We conclude LindenbaumMCS e Γ is consistent after all.

-- Needed, but unrelated.
lemma incl_insert {A B : Set α} (h1 : A ⊆ B) (h2 : x ∈ B) : (A ∪ {x}) ⊆ B := by
  intro a h
  simp at h
  apply Or.elim h
  . intro ax
    rw [ax]
    assumption
  . apply h1

-- If φ is a formula that belongs to the infinite union Γ' = LindenbaumMCS e Γ,
--    then φ must belong to some Γᵢ from Γ'.
-- More specifically, i = f φ; i.e. the place of φ in the enumeration.
lemma at_finite_step {Γ : Set (Form N)} (c : consistent Γ) (f : Form N → ℕ) (f_inj : f.Injective) (e : ℕ → Form N) (e_inv : e = f.invFun) :
    φ ∈ LindenbaumMCS e Γ c → φ ∈ Γ (f φ, e) := by
  rw [contraposition]
  simp only [LindenbaumMCS, Set.mem_setOf_eq, not_exists, not_not]
  intro h n habs
  by_cases order : n ≤ (f φ)
  . have incl := increasing_family order habs
    contradiction
  . simp only [not_le] at order
    have order := Nat.le_of_lt order
    have incl := incl_insert ((@increasing_family (f φ)) order) habs
    have n_consistent := consistent_family e c n
    have ⟨phi_inconsistent, _⟩ := not_forall.mp (maximal_family f_inj e_inv h)
    clear h
    have n_inconsistent := Proof.increasing_consequence phi_inconsistent incl
    exact n_consistent n_inconsistent

-- Given a finite list of elements in (LindenbaumMCS e Γ c), all elements of that list
--    occur in some Γᵢ that makes up the infinite union.
lemma list_at_finite_step {Γ : Set (Form N)} {c : consistent Γ} (f : Form N → ℕ) (f_inj : f.Injective) (e : ℕ → Form N) (e_inv : e = f.invFun) (L : List (LindenbaumMCS e Γ c)) :
    {↑φ | φ ∈ L} ⊆ (Γ (L.max_form f, e)) := by
    intro φ_val hmem
    simp only [Set.mem_setOf_eq] at hmem
    let ⟨φ, φ_property, φ_is_val⟩ := hmem
    rw [←φ_is_val]
    clear hmem φ_val φ_is_val
    have φ_in_MCS : ↑φ ∈ LindenbaumMCS e Γ c := by simp
    have φ_in_own_set := at_finite_step c f f_inj e e_inv φ_in_MCS
    have := L.max_is_max f φ φ_property
    exact increasing_family this φ_in_own_set

lemma LindenbaumConsistent {Γ : Set (Form N)} (c : consistent Γ) {f : Form N → ℕ} (f_inj : f.Injective) {e : ℕ → Form N} (e_inv : e = f.invFun) :
  consistent (LindenbaumMCS e Γ c) := by
  rw [←@not_not (consistent (LindenbaumMCS e Γ c))]
  intro habs
  let ⟨⟨L, L_incons⟩, _⟩ := not_forall.mp habs
  clear habs
  let ⟨L', conj_L'⟩ := conj_incl_linden L (list_at_finite_step f f_inj e e_inv L)
  rw [conj_L'] at L_incons
  clear conj_L'
  have : ((⊢(conjunction (Γ(L.max_form f, e)) L'⟶⊥) → (Γ(L.max_form f, e)) ⊢ ⊥)) := by intro h; simp [SyntacticConsequence]; exists L'
  exact consistent_family e c (L.max_form f) (this L_incons)

lemma LindenbaumMaximal {Γ : Set (Form N)} (c : consistent Γ) {f : Form N → ℕ} (f_inj : f.Injective) {e : ℕ → Form N} (e_inv : e = f.invFun) :
  ∀ φ, φ ∉ (LindenbaumMCS e Γ c) → ¬consistent ((LindenbaumMCS e Γ c) ∪ {φ}) := by
  intro φ not_mem
  have := all_sets_in_family_tollens not_mem (f φ)
  have ⟨pf_bot, _⟩ := not_forall.mp (maximal_family f_inj e_inv this)
  intro habs
  apply habs
  apply Proof.Deduction.mp
  apply Proof.increasing_consequence
  exact Proof.Deduction.mpr pf_bot
  apply all_sets_in_family

theorem RegularLindenbaumLemma : ∀ Γ : Set (Form N), consistent Γ → ∃ Γ' : Set (Form N), Γ ⊆ Γ' ∧ MCS Γ' := by
  intro Γ cons
  let ⟨f, f_inj⟩ := exists_injective_nat (Form N)
  let enum       := f.invFun
  let Γ' := LindenbaumMCS enum Γ cons
  have enum_inv : enum = f.invFun := rfl
  exists Γ'
  apply And.intro
  . -- Γ is included in Γ'
    let Γ₀ := Γ (0, enum)
    have Γ_in_Γ₀ : Γ ⊆ Γ₀ := Γ_in_family
    have Γ₀_in_family := @all_sets_in_family N enum Γ cons 0
    rw [show LindenbaumMCS enum Γ cons = Γ' from rfl, show Γ (0, enum) = Γ₀ from rfl] at Γ₀_in_family
    intro _ φ_in_Γ
    exact Γ₀_in_family (Γ_in_Γ₀ φ_in_Γ)
  . rw [MCS]
    apply And.intro
    . exact LindenbaumConsistent cons f_inj enum_inv
    . intro φ
      exact LindenbaumMaximal cons f_inj enum_inv φ

def enough_noms (Γ : Set (Form N)) := (∃ i, all_nocc i Γ) ∧ ∀ (e : ℕ → Form N) (n : ℕ), ∃ i, all_nocc i (Γ (n, e))

-- The previous set is always contained in the next Lindenbaum step (whatever branch fires).
lemma prev_subset_lindenbaum_next {prev : Set (Form N)} {φ : Form N} : prev ⊆ lindenbaum_next prev φ := by
  intro a ha
  unfold lindenbaum_next
  repeat' split
  all_goals first
    | exact ha
    | (simp only [Set.mem_union, Set.mem_singleton_iff]; tauto)

-- Witness-extraction step. If the existential `ex x, ψ` survives one Lindenbaum step
-- (so the consistent branch fired) and a fresh nominal exists for that step, then the
-- witness `ψ[i // x]` (for the *constructed* nominal `i`) lands in the next set.
lemma witness_in_next {prev : Set (Form N)} {x : SVAR} {ψ : Form N}
    (hcons : consistent prev)
    (hmem : (ex x, ψ) ∈ lindenbaum_next prev (ex x, ψ))
    (hfresh : ∃ i : NOM N, all_nocc i (prev ∪ {ex x, ψ})) :
    ∃ i : NOM N, ψ[i // x] ∈ lindenbaum_next prev (ex x, ψ) := by
  -- Force the definitional reduction of the `match` arm for `ex x, ψ`.
  have hmem' : (ex x, ψ) ∈ (if consistent (prev ∪ {ex x, ψ}) then
        (if c : ∃ i : NOM N, all_nocc i (prev ∪ {ex x, ψ}) then
          prev ∪ {ex x, ψ} ∪ {ψ[c.choose // x]} else prev ∪ {ex x, ψ}) else prev) := hmem
  suffices hgoal : ∃ i : NOM N, ψ[i // x] ∈ (if consistent (prev ∪ {ex x, ψ}) then
        (if c : ∃ i : NOM N, all_nocc i (prev ∪ {ex x, ψ}) then
          prev ∪ {ex x, ψ} ∪ {ψ[c.choose // x]} else prev ∪ {ex x, ψ}) else prev) from hgoal
  by_cases hc : consistent (prev ∪ {ex x, ψ})
  · rw [if_pos hc] at hmem' ⊢
    by_cases hfr : ∃ i : NOM N, all_nocc i (prev ∪ {ex x, ψ})
    · rw [dif_pos hfr] at hmem' ⊢
      exact ⟨hfr.choose, by simp⟩
    · exact absurd hfresh hfr
  · rw [if_neg hc] at hmem' ⊢
    exfalso
    apply hc
    rw [Set.union_singleton, Set.insert_eq_self.mpr hmem']
    exact hcons

-- One step of the witnessed-Lindenbaum argument, abstracted over the concrete set `S`
-- and the previous set `prev`.  Given freshness for `S` and that `ex x, ψ` survives, the
-- witness lands in `S`.
lemma witness_at_step {S prev : Set (Form N)} {x : SVAR} {ψ : Form N}
    (hprev_cons : consistent prev)
    (S_eq : S = lindenbaum_next prev (ex x, ψ))
    (φ_at : (ex x, ψ) ∈ S)
    (hfresh : ∃ j : NOM N, all_nocc j S) :
    ∃ i : NOM N, ψ[i // x] ∈ S := by
  subst S_eq
  have hf : ∃ j : NOM N, all_nocc j (prev ∪ {ex x, ψ}) := by
    obtain ⟨j, hj⟩ := hfresh
    refine ⟨j, fun χ hχ => ?_⟩
    rw [Set.mem_union] at hχ
    rcases hχ with hp | he
    · exact hj χ (prev_subset_lindenbaum_next hp)
    · rw [Set.mem_singleton_iff] at he; rw [he]; exact hj _ φ_at
  exact witness_in_next hprev_cons φ_at hf

lemma LindenbaumWitnessed {Γ : Set (Form N)} (c : consistent Γ) {f : Form N → ℕ} (f_inj : f.Injective) {e : ℕ → Form N} (e_inv : e = f.invFun)
    (h : enough_noms Γ) : witnessed (LindenbaumMCS e Γ c) := by
    intro φ φ_mem
    split
    . next x ψ =>
        -- `φ = ex x, ψ`. It lands in the set at its own enumeration index `f φ`.
        -- The matcher hands us the unfolded form `(all x, ψ⟶⊥)⟶⊥`; normalise to `ex x, ψ`.
        have eqform : ((all x, ψ⟶⊥)⟶⊥) = (ex x, ψ) := rfl
        have φ_at := at_finite_step c f f_inj e e_inv φ_mem
        rw [eqform] at φ_at
        have en : e (f (ex x, ψ)) = (ex x, ψ) := by rw [e_inv]; exact f.leftInverse_invFun f_inj _
        have hfresh := h.right e (f (ex x, ψ))
        have main : ∃ i : NOM N, ψ[i // x] ∈ Γ (f (ex x, ψ), e) := by
          cases hcase : f (ex x, ψ) with
          | zero =>
              rw [hcase] at φ_at hfresh
              refine witness_at_step c ?_ φ_at hfresh
              show lindenbaum_next Γ (e 0) = lindenbaum_next Γ (ex x, ψ)
              rw [show e 0 = e (f (ex x, ψ)) by rw [hcase], en]
          | succ m =>
              rw [hcase] at φ_at hfresh
              refine witness_at_step (consistent_family e c m) ?_ φ_at hfresh
              show lindenbaum_next (Γ (m, e)) (e (m+1)) = lindenbaum_next (Γ (m, e)) (ex x, ψ)
              rw [show e (m+1) = e (f (ex x, ψ)) by rw [hcase], en]
        obtain ⟨i, hi⟩ := main
        exact ⟨i, all_sets_in_family _ hi⟩
    . assumption

-- The nominal `0` (even) never occurs in an odd-nominal image, since `odd_noms` maps every
-- nominal `i ↦ 2·i+1`.
theorem zero_nocc_odd : ∀ φ : Form TotalSet, nom_occurs 0 φ.odd_noms = false := by
  intro φ
  induction φ with
  | bttm => rw [odd_bttm]; rfl
  | prop p => simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst, nom_occurs]
  | svar x => simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst, nom_occurs]
  | nom i =>
      rw [odd_nom]
      have hne : (0 : NOM TotalSet) ≠ 2 * i + 1 := by
        intro h
        rw [NOM_eq] at h
        have hval : (0 : ℕ) = (i.letter : ℕ) * 2 + 1 := congrArg Subtype.val h
        omega
      simp only [nom_occurs, decide_eq_false_iff_not]
      exact hne
  | impl a b iha ihb => rw [odd_impl]; simp only [nom_occurs, iha, ihb, Bool.or_self]
  | box a ih => rw [odd_box]; simp only [nom_occurs, ih]
  | bind x a ih => rw [odd_bind]; simp only [nom_occurs, ih]

-- Generalisation of `zero_nocc_odd`: *any* even nominal is fresh for an odd-nominal image,
-- since `odd_noms` sends every nominal `i ↦ 2·i+1` (always odd).
theorem even_nocc_odd {j : NOM TotalSet} (heven : Even (j.letter : ℕ)) :
    ∀ φ : Form TotalSet, nom_occurs j φ.odd_noms = false := by
  intro φ
  induction φ with
  | bttm => rw [odd_bttm]; rfl
  | prop p => simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst, nom_occurs]
  | svar x => simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst, nom_occurs]
  | nom i =>
      rw [odd_nom]
      have hne : j ≠ 2 * i + 1 := by
        intro h
        rw [NOM_eq] at h
        have hval : (j.letter : ℕ) = (i.letter : ℕ) * 2 + 1 := congrArg Subtype.val h
        obtain ⟨t, ht⟩ := heven
        omega
      simp only [nom_occurs, decide_eq_false_iff_not]
      exact hne
  | impl a b iha ihb => rw [odd_impl]; simp only [nom_occurs, iha, ihb, Bool.or_self]
  | box a ih => rw [odd_box]; simp only [nom_occurs, ih]
  | bind x a ih => rw [odd_bind]; simp only [nom_occurs, ih]

-- Base case of structural freshness: the even nominal `0` is fresh for the whole image set.
theorem enough_noms_odd_base (Γ : Set (Form TotalSet)) : ∃ i : NOM TotalSet, all_nocc i Γ.odd_noms := by
  refine ⟨0, ?_⟩
  rintro φ ⟨ψ, _, rfl⟩
  exact zero_nocc_odd ψ

-- A single Lindenbaum step only enlarges the previous set by a *finite* number of formulas
-- (the enumerated formula `φ` itself, plus at most one existential witness).
lemma lindenbaum_next_subset (prev : Set (Form N)) (φ : Form N) :
    ∃ A : Finset (Form N), lindenbaum_next prev φ ⊆ prev ∪ ↑A := by
  unfold lindenbaum_next
  split
  · split
    · next x ψ _ =>
        split
        · next c =>
            refine ⟨{(ex x, ψ), ψ[c.choose // x]}, ?_⟩
            intro a ha
            simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_union,
                       Finset.coe_insert, Finset.coe_singleton, Set.mem_singleton_iff] at ha ⊢
            tauto
        · refine ⟨{(ex x, ψ)}, ?_⟩
          intro a ha
          simp only [Set.union_singleton, Set.mem_insert_iff,
                     Finset.coe_singleton] at ha ⊢
          tauto
    · refine ⟨{φ}, ?_⟩
      intro a ha
      simp only [Set.union_singleton, Set.mem_insert_iff,
                 Finset.coe_singleton] at ha ⊢
      tauto
  · exact ⟨∅, fun a ha => Or.inl ha⟩

-- Hence each finite stage `Γ (n, e)` is contained in the base `Γ` together with a finite set.
lemma family_subset {Γ : Set (Form N)} (e : ℕ → Form N) :
    ∀ n, ∃ A : Finset (Form N), Γ (n, e) ⊆ Γ ∪ ↑A := by
  intro n
  induction n with
  | zero =>
      simp only [lindenbaum_family]
      exact lindenbaum_next_subset Γ (e 0)
  | succ m ih =>
      obtain ⟨A, hA⟩ := ih
      obtain ⟨A', hA'⟩ := lindenbaum_next_subset (Γ (m, e)) (e (m+1))
      refine ⟨A ∪ A', ?_⟩
      calc Γ ((m+1), e) ⊆ Γ (m, e) ∪ ↑A' := hA'
        _ ⊆ (Γ ∪ ↑A) ∪ ↑A' := Set.union_subset_union hA (subset_refl _)
        _ = Γ ∪ (↑A ∪ ↑A') := by rw [Set.union_assoc]
        _ = Γ ∪ ↑(A ∪ A') := by rw [Finset.coe_union]

-- For any finite set of formulas there is an even nominal that occurs in none of them.
-- (Take a letter that is both even and larger than every nominal appearing in the set.)
lemma fresh_even_dominating (A : Finset (Form TotalSet)) :
    ∃ j : NOM TotalSet, Even (j.letter : ℕ) ∧ (∀ φ ∈ A, nom_occurs j φ = false) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ φ ∈ A, (φ.new_nom.letter : ℕ) ≤ M := by
    refine ⟨A.sup (fun φ => (φ.new_nom.letter : ℕ)), fun φ hφ => ?_⟩
    exact Finset.le_sup (f := fun φ => (φ.new_nom.letter : ℕ)) hφ
  refine ⟨⟨2 * M + 2, trivial⟩, ?_, ?_⟩
  · show Even (2 * M + 2)
    exact ⟨M + 1, by omega⟩
  intro φ hφ
  apply ge_new_nom_is_new
  show (φ.new_nom.letter : ℕ) ≤ (2 * M + 2 : ℕ)
  have := hM φ hφ
  omega

-- Inductive (per-stage) case of structural freshness.  This is the heart of the completeness
-- proof and the obstacle on which Oltean's original development stalled.  At every finite
-- stage of the Lindenbaum construction only finitely many further formulas (hence finitely
-- many further nominals) have been added to the odd-only base set, so an unused even nominal
-- always remains.
theorem enough_noms_odd_step (Γ : Set (Form TotalSet)) :
    ∀ (e : ℕ → Form TotalSet) (n : ℕ), ∃ i : NOM TotalSet, all_nocc i (Γ.odd_noms (n, e)) := by
  intro e n
  obtain ⟨A, hA⟩ := family_subset (Γ := Γ.odd_noms) e n
  obtain ⟨j, hjeven, hjA⟩ := fresh_even_dominating A
  refine ⟨j, ?_⟩
  intro φ hφ
  rcases hA hφ with hbase | hAmem
  · obtain ⟨ψ, _, rfl⟩ := hbase
    exact even_nocc_odd hjeven ψ
  · exact hjA φ hAmem

theorem enough_noms_odd (Γ : Set (Form TotalSet)) : enough_noms Γ.odd_noms :=
  ⟨enough_noms_odd_base Γ, enough_noms_odd_step Γ⟩

theorem ExtendedLindenbaumLemma : ∀ Γ : Set (Form TotalSet), consistent Γ → ∃ Γ' : Set (Form TotalSet), Γ.odd_noms ⊆ Γ' ∧ MCS Γ' ∧ witnessed Γ' := by
  intro Γ cons
  have cons' : consistent Γ.odd_noms := (Proof.odd_noms_set_cons Γ).mp cons
  obtain ⟨f, f_inj⟩ := exists_injective_nat (Form TotalSet)
  let enum := f.invFun
  have enum_inv : enum = f.invFun := rfl
  refine ⟨LindenbaumMCS enum Γ.odd_noms cons', ?_, ⟨?_, ?_⟩, ?_⟩
  · -- `Γ.odd_noms ⊆ Γ'`
    intro φ hφ
    exact all_sets_in_family 0 (Γ_in_family hφ)
  · -- consistency of the MCS
    exact LindenbaumConsistent cons' f_inj enum_inv
  · -- maximality of the MCS
    intro φ
    exact LindenbaumMaximal cons' f_inj enum_inv φ
  · -- witnessing
    exact LindenbaumWitnessed cons' f_inj enum_inv (enough_noms_odd Γ)

/-- Witnessed Lindenbaum on a set that already carries `enough_noms` (not just on `odd_noms`). -/
theorem WitnessedLindenbaumLemma : ∀ Γ : Set (Form TotalSet), consistent Γ → enough_noms Γ →
    ∃ Γ' : Set (Form TotalSet), Γ ⊆ Γ' ∧ MCS Γ' ∧ witnessed Γ' := by
  intro Γ cons hnom
  obtain ⟨f, f_inj⟩ := exists_injective_nat (Form TotalSet)
  let enum := f.invFun
  have enum_inv : enum = f.invFun := rfl
  let Γ' := LindenbaumMCS enum Γ cons
  refine ⟨Γ', ?_, ⟨?_, ?_⟩, ?_⟩
  · intro φ hφ
    exact all_sets_in_family 0 (Γ_in_family hφ)
  · exact LindenbaumConsistent cons f_inj enum_inv
  · intro φ
    exact LindenbaumMaximal cons f_inj enum_inv φ
  · exact LindenbaumWitnessed cons f_inj enum_inv hnom
