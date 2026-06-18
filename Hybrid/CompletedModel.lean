import Hybrid.ProofUtils
import Hybrid.Truth
import Hybrid.Soundness
import Hybrid.Tautology
-- Interface for proofs to be filled
-- about renaming bound vars:
import Hybrid.RenameBound
import Hybrid.Lindenbaum

open Classical

def restrict_by : (Set (Form N) → Prop) → (Set (Form N) → Set (Form N) → Prop) → (Set (Form N) → Set (Form N) → Prop) :=
  λ restriction => λ R => λ Γ => λ Δ => restriction Γ ∧ restriction Δ ∧ R Γ Δ

theorem path_conj {R : α → Prop} : path (λ a b => R a ∧ R b) a b n → (R a → R b) := by
  cases n with
  | zero =>
      unfold path; intro; simp [*]
  | succ n =>
      unfold path
      intro ⟨_, h⟩ _
      exact h.1.2

theorem path_restr : path (restrict_by R₁ R₂) Γ Δ n → path R₂ Γ Δ n := by
  induction n generalizing Δ with
  | zero => simp only [path, imp_self]
  | succ n ih =>
      simp only [path]
      intro ⟨Θ, ⟨⟨_, _, h1⟩, h2⟩⟩
      exists Θ
      apply And.intro
      assumption
      apply ih
      assumption

theorem path_restr' : path (restrict_by R₁ R₂) Γ Δ n → (R₁ Γ → R₁ Δ) := by
  cases n with
  | zero =>
      unfold path; intro; simp [*]
  | succ n =>
      unfold path
      intro ⟨_, h⟩ _
      exact h.1.2.1

structure GeneralModel (N : Set ℕ) where
  W : Type
  R : W → W  → Prop
  Vₚ: PROP   → Set W
  Vₙ: NOM N  → Set W

def GeneralI (W : Type) := SVAR → Set W

def Canonical : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := restrict_by MCS (λ Γ => λ Δ => (∀ {φ : Form TotalSet}, □φ ∈ Γ → φ ∈ Δ))
--  R := λ Γ => λ Δ => Γ.MCS ∧ Δ.MCS ∧ (∀ φ : Form, □φ ∈ Γ → φ ∈ Δ)
  Vₚ:= λ p => {Γ | MCS Γ ∧ ↑p ∈ Γ}
  Vₙ:= λ i => {Γ | MCS Γ ∧ ↑i ∈ Γ}

def CanonicalI : SVAR → Set (Set (Form TotalSet)) := λ x => {Γ | MCS Γ ∧ ↑x ∈ Γ}

instance : Membership (Form TotalSet) Canonical.W := ⟨Set.Mem⟩

theorem R_nec : □φ ∈ Γ → Canonical.R Γ Δ → φ ∈ Δ := by
  intro h1 h2
  simp only [Canonical, restrict_by] at h2
  apply h2.right.right
  assumption

theorem R_pos : Canonical.R Γ Δ ↔ (MCS Γ ∧ MCS Δ ∧ ∀ {φ}, (φ ∈ Δ → ◇φ ∈ Γ)) := by
  simp only [Canonical, restrict_by]
  apply Iff.intro
  . intro ⟨h1, h2, h3⟩
    simp only [*, true_and]
    intro φ φ_mem
    by_contra habs
    have ⟨habs, _⟩ := not_forall.mp (h1.right habs)
    have habs := Proof.Deduction.mpr habs
    rw [←Form.neg, Form.diamond] at habs
    have habs : ∼φ ∈ Δ := by
      apply h3
      apply Proof.MCS_pf h1
      apply Proof.Γ_mp
      apply Proof.Γ_theorem
      apply Proof.tautology
      apply dne
      assumption
    unfold MCS consistent at h1 h2
    apply h2.left
    apply Proof.Γ_mp
    repeat (apply Proof.Γ_premise; assumption)
  . intro ⟨h1, h2, h3⟩
    simp only [*, true_and]
    intro φ φ_mem
    by_contra habs
    have ⟨habs, _⟩ := not_forall.mp (h2.right habs)
    have habs := Proof.Deduction.mpr habs
    rw [←Form.neg] at habs
    have habs : ◇∼φ ∈ Γ := by
      apply h3
      apply Proof.MCS_pf h2
      assumption
    unfold MCS consistent at h1 h2
    apply h1.left
    apply Proof.Γ_mp
    apply Proof.Γ_premise
    assumption
    apply Proof.Γ_mp
    apply Proof.Γ_theorem
    apply Proof.mp
    apply Proof.tautology
    apply iff_elim_l
    apply Proof.dn_nec
    apply Proof.Γ_premise
    assumption

theorem R_iter_nec (n : ℕ) : (iterate_nec n φ) ∈ Γ → path Canonical.R Γ Δ n → φ ∈ Δ := by
  intro h1 h2
  induction n generalizing φ Δ with
  | zero =>
      simp only [iterate_nec, iterate_nec.loop, path] at h1 h2
      rw [←h2]
      assumption
  | succ n ih =>
      simp only [path, iter_nec_succ] at ih h1 h2
      have ⟨Κ, hk1, hk2⟩ := h2
      apply R_nec
      exact (ih h1 hk2)
      assumption

theorem R_iter_pos (n : ℕ) : path Canonical.R Γ Δ n → ∀ {φ}, (φ ∈ Δ → (iterate_pos n φ) ∈ Γ) := by
  intro h1 φ h2
  induction n generalizing φ Δ with
  | zero =>
      simp [path, iterate_pos, iterate_pos.loop] at h1 ⊢
      rw [h1]
      assumption
  | succ n ih =>
      simp only [path, iter_pos_succ] at ih h1 ⊢
      have ⟨Κ, hk1, hk2⟩ := h1
      rw [R_pos] at hk1
      apply ih hk2
      exact hk1.right.right h2

theorem restrict_R_iter_nec {n : ℕ} : (iterate_nec n φ) ∈ Γ → path (restrict_by R Canonical.R) Γ Δ n → φ ∈ Δ := by
  intro h1 h2
  apply R_iter_nec
  assumption
  apply path_restr
  assumption

theorem restrict_R_iter_pos {n : ℕ} : path (restrict_by R Canonical.R) Γ Δ n → ∀ {φ}, (φ ∈ Δ → (iterate_pos n φ) ∈ Γ) := by
  intro h1 φ h2
  apply R_iter_pos
  apply path_restr
  repeat assumption

-- implicitly we mean generated submodels *of the canonical model*
def Set.GeneratedSubmodel (Θ : Set (Form TotalSet)) (restriction : Set (Form TotalSet) → Prop) : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := λ Γ => λ Δ =>
    (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧
    (∃ m, path (restrict_by restriction Canonical.R) Θ Δ m) ∧
    Canonical.R Γ Δ
  Vₚ:= λ p => {Γ | (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧ Γ ∈ Canonical.Vₚ p}
  Vₙ:= λ i => {Γ | (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧ Γ ∈ Canonical.Vₙ i}

def Set.GeneratedSubI (Θ : Set (Form TotalSet)) (restriction : Set (Form TotalSet) → Prop) : GeneralI (Set (Form TotalSet)) := λ x =>
  {Γ | (∃ n, path (restrict_by restriction Canonical.R) Θ Γ n) ∧ Γ ∈ CanonicalI x}

theorem submodel_canonical_path (Θ : Set (Form TotalSet)) (r : Set (Form TotalSet) → Prop) (rt : r Θ) : path (Θ.GeneratedSubmodel r).R Γ Δ n → path (restrict_by r Canonical.R) Γ Δ n := by
  intro h
  induction n generalizing Γ Δ with
  | zero =>
      simp [path] at h ⊢
      exact h
  | succ n ih =>
      have ⟨Η, ⟨h1, h2⟩⟩ := h
      have := ih h2
      clear h h2
      exists Η
      apply And.intro
      . simp [Set.GeneratedSubmodel] at h1
        have ⟨⟨n, l1⟩, ⟨⟨m, l2⟩, l3⟩⟩ := h1
        simp [restrict_by, l3]
        apply And.intro <;>
        . apply path_restr'
          repeat assumption
      . exact this

theorem path_root (Θ : Set (Form TotalSet)) (r : Set (Form TotalSet) → Prop) : path (restrict_by r Canonical.R) Θ Γ n → path (Θ.GeneratedSubmodel r).R Θ Γ n := by
  induction n generalizing Θ Γ with
  | zero => intro h; exact h
  | succ n ih =>
      simp only [path]
      intro ⟨Δ, ⟨h1, h2⟩⟩
      exists Δ
      apply And.intro
      . simp [Set.GeneratedSubmodel]
        apply And.intro
        . exists n
        . apply And.intro
          . exists (n+1)
            simp [path]
            exists Δ
          . exact h1.2.2
      . apply ih
        exact h2

def WitnessedModel {Θ : Set (Form TotalSet)} (_ : MCS Θ) (_ : witnessed Θ) : GeneralModel TotalSet := Θ.GeneratedSubmodel witnessed
def WitnessedI {Θ : Set (Form TotalSet)} (_ : MCS Θ) (_ : witnessed Θ) : GeneralI (Set (Form TotalSet)) := Θ.GeneratedSubI witnessed

def CompletedModel {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := λ Γ => λ Δ => ((WitnessedModel mcs wit).R Γ Δ) ∨ (Γ = {Form.bttm} ∧ Δ = Θ)
  Vₚ:= λ p => (WitnessedModel mcs wit).Vₚ p
  Vₙ:= λ i => if (WitnessedModel mcs wit).Vₙ i ≠ ∅
              then  (WitnessedModel mcs wit).Vₙ i
              else { {Form.bttm} }
def CompletedI {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : GeneralI (Set (Form TotalSet)) := λ x =>
  if (WitnessedI mcs wit) x ≠ ∅
              then  (WitnessedI mcs wit) x
              else { {Form.bttm} }

-- Lemma 3.11, Blackburn 1998, pg. 637
lemma subsingleton_valuation : ∀ {Θ : Set (Form TotalSet)} {R : Set (Form TotalSet) → Prop} (i : NOM TotalSet), MCS Θ → ((Θ.GeneratedSubmodel R).Vₙ i).Subsingleton := by
  -- the hypothesis MCS Θ is not necessary
  --  but to prove the theorem without it would complicate
  --  the code, and anyway, we'll only ever use MCS-generated submodels
  simp only [Set.Subsingleton, Set.GeneratedSubmodel]
  intro Θ restr i Θ_MCS Γ ⟨⟨n, h1⟩, ⟨Γ_MCS, Γ_i⟩⟩  Δ ⟨⟨m, h2⟩, ⟨Δ_MCS, Δ_i⟩⟩
  rw [←(@not_not (Γ = Δ))]
  simp only [Set.ext_iff, not_forall, iff_iff_implies_and_implies,
      implication_disjunction, not_and, negated_disjunction, not_not, conj_comm]
  intro ⟨φ, h⟩
  apply Or.elim h
  . clear h
    intro ⟨h3, h4⟩
    apply h4
    have := restrict_R_iter_pos h1 ((Proof.MCS_conj Γ_MCS i φ).mp ⟨Γ_i, h3⟩)
    have := Proof.MCS_mp Θ_MCS (Proof.MCS_thm Θ_MCS (Proof.ax_nom_instance i n m)) this
    have := restrict_R_iter_nec this h2
    apply Proof.MCS_mp
    repeat assumption
  . clear h
    intro ⟨h3, h4⟩
    apply h3
    have := restrict_R_iter_pos h2 ((Proof.MCS_conj Δ_MCS i φ).mp ⟨Δ_i, h4⟩)
    have := Proof.MCS_mp Θ_MCS (Proof.MCS_thm Θ_MCS (Proof.ax_nom_instance i m n)) this
    have := restrict_R_iter_nec this h1
    apply Proof.MCS_mp
    repeat assumption

lemma subsingleton_i : ∀ {Θ : Set (Form TotalSet)} {R : Set (Form TotalSet) → Prop} (x : SVAR), MCS Θ → ((Θ.GeneratedSubI R) x).Subsingleton := by
  simp only [Set.Subsingleton, Set.GeneratedSubmodel]
  intro Θ restr x Θ_MCS Γ ⟨⟨n, h1⟩, ⟨Γ_MCS, Γ_i⟩⟩  Δ ⟨⟨m, h2⟩, ⟨Δ_MCS, Δ_i⟩⟩
  rw [←(@not_not (Γ = Δ))]
  simp only [Set.ext_iff, not_forall, iff_iff_implies_and_implies,
      implication_disjunction, not_and, negated_disjunction, not_not, conj_comm]
  intro ⟨φ, h⟩
  apply Or.elim h
  . clear h
    intro ⟨h3, h4⟩
    apply h4
    have := restrict_R_iter_pos h1 ((Proof.MCS_conj Γ_MCS x φ).mp ⟨Γ_i, h3⟩)
    have := Proof.MCS_mp Θ_MCS (Proof.MCS_thm Θ_MCS (Proof.ax_nom_instance' x n m)) this
    have := restrict_R_iter_nec this h2
    apply Proof.MCS_mp
    repeat assumption
  . clear h
    intro ⟨h3, h4⟩
    apply h3
    have := restrict_R_iter_pos h2 ((Proof.MCS_conj Δ_MCS x φ).mp ⟨Δ_i, h4⟩)
    have := Proof.MCS_mp Θ_MCS (Proof.MCS_thm Θ_MCS (Proof.ax_nom_instance' x m n)) this
    have := restrict_R_iter_nec this h1
    apply Proof.MCS_mp
    repeat assumption

lemma wit_subsingleton_valuation {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (i : NOM TotalSet) : ((WitnessedModel mcs wit).Vₙ i).Subsingleton := by
  rw [WitnessedModel]
  apply subsingleton_valuation
  assumption

lemma wit_subsingleton_i {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (x : SVAR) : ((WitnessedI mcs wit) x).Subsingleton := by
  rw [WitnessedI]
  apply subsingleton_i
  assumption

lemma completed_singleton_valuation {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (i : NOM TotalSet) : ∃ Γ : Set (Form TotalSet), (CompletedModel mcs wit).Vₙ i = {Γ} := by
  simp only [CompletedModel]
  split
  . next h =>
      have ⟨Γ, hΓ⟩ := Set.nonempty_iff_ne_empty.mpr h
      exists Γ
      apply (Set.subsingleton_iff_singleton hΓ).mp
      apply wit_subsingleton_valuation
  . exact ⟨_, rfl⟩

lemma completed_singleton_i {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (x : SVAR) : ∃ Γ : Set (Form TotalSet), (CompletedI mcs wit) x = {Γ} := by
  simp only [CompletedI]
  split
  . next h =>
      have ⟨Γ, hΓ⟩ := Set.nonempty_iff_ne_empty.mpr h
      exists Γ
      apply (Set.subsingleton_iff_singleton hΓ).mp
      apply wit_subsingleton_i
  . exact ⟨_, rfl⟩

def Set.MCS_in (Γ : Set (Form TotalSet)) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Prop := ∃ n, path (WitnessedModel mcs wit).R Θ Γ n

theorem mcs_in_prop {Γ Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Γ.MCS_in mcs wit → (MCS Γ ∧ witnessed Γ) := by
  intro ⟨n, h⟩
  cases n with
  | zero =>
      simp [path] at h
      simp [←h, mcs, wit]
  | succ n =>
      have ⟨Δ, h1, h2⟩ := h
      clear h2
      simp [WitnessedModel, Set.GeneratedSubmodel, Canonical] at h1
      have ⟨h3, ⟨m, h4⟩, h5⟩ := h1
      clear h1 h3
      simp [h5.2.1]
      apply path_restr' h4
      exact wit

theorem mcs_in_wit {Γ Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Γ.MCS_in mcs wit → (∃ n, path (restrict_by witnessed Canonical.R) Θ Γ n) := by
  intro ⟨n, h⟩
  exists n
  cases n with
  | zero =>
      simp [path] at h ⊢
      exact h
  | succ n =>
      simp [path]
      have ⟨Δ, h1, h2⟩ := h
      exists Δ
      apply And.intro
      . apply submodel_canonical_path
        repeat assumption
      . have ⟨⟨_, l⟩, ⟨⟨_, r1⟩, r2⟩⟩ := h1
        simp [restrict_by, r2]
        apply And.intro <;>
        . apply path_restr'
          repeat assumption

def needs_dummy {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) := (∃ i, ((CompletedModel mcs wit).Vₙ i) = { (Set.singleton Form.bttm) }) ∨
                                                                                 (∃ x, ((CompletedI mcs wit) x) = { (Set.singleton Form.bttm) })

def Set.is_dummy (Γ : Set (Form TotalSet)) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) := needs_dummy mcs wit ∧ Γ = {Form.bttm}


theorem choose_subtype {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ)  : ((completed_singleton_valuation mcs wit i).choose.MCS_in mcs wit) ∨ (completed_singleton_valuation mcs wit i).choose.is_dummy mcs wit := by
  apply choice_intro (λ Γ => (Set.MCS_in Γ mcs wit) ∨ (Set.is_dummy Γ mcs wit))
  intro Γ h
  simp [CompletedModel, WitnessedModel, Set.GeneratedSubmodel] at h
  split at h
  . next c =>
      apply Or.inr
      apply And.intro
      . apply Or.inl
        exists i
        simp [CompletedModel, WitnessedModel, Set.GeneratedSubmodel, c]
        apply Eq.refl
      . exact (Set.singleton_eq_singleton_iff.mp h).symm
  . apply Or.inl
    have Γ_mem : Γ ∈ {Γ | (∃ n, path (restrict_by witnessed Canonical.R) Θ Γ n) ∧ Γ ∈ Canonical.Vₙ i} := by
      rw [h]; exact Set.mem_singleton _
    simp only [Set.mem_setOf_eq] at Γ_mem
    have ⟨⟨n, pth⟩, _⟩ := Γ_mem
    simp [Set.MCS_in, WitnessedModel]
    exists n
    apply path_root
    exact pth

theorem choose_subtype' {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : ((completed_singleton_i mcs wit i).choose.MCS_in mcs wit) ∨ (completed_singleton_i mcs wit i).choose.is_dummy mcs wit := by
  apply choice_intro (λ Γ => (Set.MCS_in Γ mcs wit) ∨ (Set.is_dummy Γ mcs wit))
  intro Γ h
  simp [CompletedI, WitnessedI, Set.GeneratedSubI] at h
  split at h
  . next c =>
      apply Or.inr
      apply And.intro
      . apply Or.inr
        exists i
        simp [CompletedI, WitnessedI, Set.GeneratedSubI, c]
        apply Eq.refl
      . apply Eq.symm
        simp at h
        exact h
  . apply Or.inl
    have Γ_mem : Γ ∈ {Γ | (∃ n, path (restrict_by witnessed Canonical.R) Θ Γ n) ∧ Γ ∈ CanonicalI i} := by simp [h]
    simp at Γ_mem
    have ⟨⟨n, pth⟩, _⟩ := Γ_mem
    simp [Set.MCS_in, WitnessedModel]
    exists n
    apply path_root
    exact pth


-- pg. 638: "we only glue on a dummy state when we are forced to"
--    we define the set of states as Γ.MCS_in ∨ Γ.is_dummy
--    where is_dummy contains the assumption that we are *forced*
--    to glue a dummy
noncomputable def StandardCompletedModel {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : Model TotalSet :=
    ⟨{Γ : Set (Form TotalSet) // Γ.MCS_in mcs wit ∨ Γ.is_dummy mcs wit},
      λ Γ => λ Δ => (CompletedModel mcs wit).R Γ.1 Δ.1,
      λ p => {Γ | Γ.1 ∈ ((CompletedModel mcs wit).Vₚ p)},
      λ i => ⟨(completed_singleton_valuation mcs wit i).choose, choose_subtype mcs wit⟩⟩

noncomputable def StandardCompletedI {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) : I (StandardCompletedModel mcs wit).W :=
    λ x => ⟨(completed_singleton_i mcs wit x).choose, choose_subtype' mcs wit⟩

theorem sat_dual_all_ex : ((M,s,g) ⊨ (all x, φ)) ↔ (M,s,g) ⊨ ∼(ex x, ∼φ) := by
  apply Iff.intro
  . intro h; simp only [Form.bind_dual, neg_sat, not_not] at *
    intro g' var
    simp only [Form.bind_dual, neg_sat, not_not] at *
    apply h
    repeat assumption
  . intro h; simp only [Form.bind_dual, neg_sat, not_not] at *
    intro g' var
    have := h g' var
    simp only [Form.bind_dual, neg_sat, not_not] at this
    exact this

theorem sat_dual_nec_pos : ((M,s,g) ⊨ (□ φ)) ↔ (M,s,g) ⊨ ∼(◇ ∼φ) := by
  apply Iff.intro
  . intro h; simp only [Form.diamond, neg_sat, not_not] at *
    intro _ _
    simp only [neg_sat, not_not] at *
    apply h
    repeat assumption
  . intro h; simp only [Form.diamond, neg_sat, not_not] at *
    intro s' r
    have := h s' r
    simp only [neg_sat, not_not] at this
    exact this

@[simp]
def coe (Δ : Set (Form TotalSet)) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) (h : Δ.MCS_in mcs wit) : (StandardCompletedModel mcs wit).W := ⟨Δ, Or.inl h⟩

def statement (φ : Form TotalSet) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) := ∀ {Δ : Set (Form TotalSet)}, (h : Δ.MCS_in mcs wit) → φ ∈ Δ ↔ (StandardCompletedModel mcs wit, coe Δ mcs wit h, StandardCompletedI mcs wit) ⊨ φ


lemma truth_bttm : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement ⊥ mcs wit) := by
  intro _ mcs' wit' Δ h
  have := (mcs_in_prop mcs' wit' h).1
  apply Iff.intro
  . intro h
    exact this.1 (Proof.Γ_premise h)
  . simp

lemma truth_prop : ∀ {Θ : Set (Form TotalSet)} {p : PROP}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement p mcs wit) := by
  intro Θ  _ mcs wit Δ h
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h)
  apply Iff.intro
  . intro hl
    apply And.intro
    . apply mcs_in_wit
      exact h
    . exact ⟨D_mcs, hl⟩
  . intro a
    exact a.2.2

lemma truth_nom_help : ∀ {Θ : Set (Form TotalSet)} {i : NOM TotalSet}, (mcs : MCS Θ) → (wit : witnessed Θ) → ∀ {Δ : Set (Form TotalSet)}, Δ.MCS_in mcs wit → (↑i ∈ Δ ↔ ((StandardCompletedModel mcs wit).Vₙ ↑i).1 = Δ) := by
  intro Θ i mcs wit Δ h_in
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h_in)
  simp [StandardCompletedModel, CompletedModel, WitnessedModel]
  apply Iff.intro
  . intro h
    apply choice_intro (λ Γ : Set (Form TotalSet) => Γ = Δ)
    intro Η eta_eq
    have delta_mem : Δ ∈ (Θ.GeneratedSubmodel witnessed).Vₙ i := by
      simp [Set.GeneratedSubmodel, WitnessedModel] at h_in ⊢
      apply And.intro
      . have ⟨n, h_in⟩ := h_in
        exists n
        exact submodel_canonical_path Θ witnessed wit h_in
      . exact ⟨D_mcs, h⟩
    split at eta_eq
    . next fls =>
        exfalso
        rw [fls] at delta_mem
        exact (Set.mem_empty_iff_false Δ).mp delta_mem
    . have eta_mem : Η ∈ (Θ.GeneratedSubmodel witnessed).Vₙ i := by
        rw [eta_eq]; exact Set.mem_singleton _
      apply subsingleton_valuation i mcs
      exact eta_mem
      exact delta_mem
  . intro h
    rw [←h] at h_in D_mcs ⊢
    clear h
    apply choice_intro (λ Γ : Set (Form TotalSet) => ↑i ∈ Γ)
    intro Η eta_eq
    split at eta_eq
    . next fls =>
        exfalso
        apply D_mcs.left
        apply choice_intro (λ Γ => Γ ⊢ ⊥)
        intro _ a
        simp only [fls, if_pos] at a
        apply Proof.Γ_premise
        rw [← Set.singleton_eq_singleton_iff.mp a]
        exact Set.mem_singleton _
    . have eta_mem : Η ∈ (Θ.GeneratedSubmodel witnessed).Vₙ i := by
        rw [eta_eq]; exact Set.mem_singleton _
      simp [Set.GeneratedSubmodel, Canonical] at eta_mem
      exact eta_mem.left.right

lemma truth_svar_help : ∀ {Θ : Set (Form TotalSet)} {i : SVAR}, (mcs : MCS Θ) → (wit : witnessed Θ) → ∀ {Δ : Set (Form TotalSet)}, Δ.MCS_in mcs wit → (↑i ∈ Δ ↔ (StandardCompletedI mcs wit ↑i).1 = Δ) := by
  intro Θ i mcs wit Δ h_in
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h_in)
  simp [StandardCompletedI, CompletedI, WitnessedI]
  apply Iff.intro
  . intro h
    apply choice_intro (λ Γ : Set (Form TotalSet) => Γ = Δ)
    intro Η eta_eq
    have delta_mem : Δ ∈ Θ.GeneratedSubI witnessed i := by
      simp [Set.GeneratedSubI, WitnessedI] at h_in ⊢
      apply And.intro
      . have ⟨n, h_in⟩ := h_in
        exists n
        exact submodel_canonical_path Θ witnessed wit h_in
      . simp [CanonicalI, h, D_mcs]
    split at eta_eq
    . next fls =>
        exfalso
        rw [←@not_not ((Θ.GeneratedSubI witnessed i) = ∅), ←Ne,
          ←Set.nonempty_iff_ne_empty, Set.nonempty_def, not_exists] at fls
        apply fls Δ
        exact delta_mem
    . have eta_mem : Η ∈ Θ.GeneratedSubI witnessed i := by simp [eta_eq]
      apply subsingleton_i i mcs
      exact eta_mem
      exact delta_mem
  . intro h
    rw [←h] at h_in D_mcs ⊢
    clear h
    apply choice_intro (λ Γ : Set (Form TotalSet) => ↑i ∈ Γ)
    intro Η eta_eq
    split at eta_eq
    . next fls =>
        exfalso
        apply D_mcs.left
        apply choice_intro (λ Γ => Γ ⊢ ⊥)
        intro _ a
        simp [fls, Set.eq_singleton_iff_unique_mem] at a
        apply Proof.Γ_premise
        exact a.left.left
    . have eta_mem : Η ∈ Θ.GeneratedSubI witnessed i := by simp [eta_eq]
      simp [Set.GeneratedSubI, CanonicalI] at eta_mem
      exact eta_mem.right.right

lemma truth_nom : ∀ {Θ : Set (Form TotalSet)} {i : NOM TotalSet}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement i mcs wit) := by
  intro Θ i mcs wit Δ h_in
  apply Iff.intro
  . intro h
    simp only [Sat, coe]
    apply Subtype.eq
    simp only
    apply Eq.symm
    apply (truth_nom_help mcs wit h_in).mp
    exact h
  . simp only [coe, Sat]
    intro h
    apply (truth_nom_help mcs wit h_in).mpr
    rw [Subtype.coe_eq_iff]
    exists (Or.inl h_in)
    apply Eq.symm
    exact h

lemma truth_svar : ∀ {Θ : Set (Form TotalSet)} {i : SVAR}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement i mcs wit) := by
  intro Θ i mcs wit Δ h_in
  apply Iff.intro
  . intro h
    simp only [Sat, coe]
    apply Subtype.eq
    simp only
    apply Eq.symm
    apply (truth_svar_help mcs wit h_in).mp
    exact h
  . simp only [coe, Sat]
    intro h
    apply (truth_svar_help mcs wit h_in).mpr
    rw [Subtype.coe_eq_iff]
    exists (Or.inl h_in)
    apply Eq.symm
    exact h

lemma truth_impl : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) → (statement φ mcs wit) → (statement ψ mcs wit) → statement (φ ⟶ ψ) mcs wit := by
  intro Θ mcs wit ih_φ ih_ψ Δ h_in
  have ⟨D_mcs, _⟩ := (mcs_in_prop mcs wit h_in)
  apply Iff.intro
  . intro h1 h2
    apply (ih_ψ h_in).mp
    apply Proof.MCS_mp
    repeat assumption
    exact (ih_φ h_in).mpr h2
  . intro sat_φ_ψ
    unfold statement at ih_φ ih_ψ
    rw [Sat, ←ih_φ, ←ih_ψ, Proof.MCS_impl] at sat_φ_ψ
    repeat assumption

lemma has_state_symbol (s : (StandardCompletedModel mcs wit).W) : (∃ i, (StandardCompletedModel mcs wit).Vₙ i = s) ∨ (∃ x, StandardCompletedI mcs wit x = s) := by
  apply Or.elim s.2
  . intro s_in
    apply Or.inl
    have ⟨s_mcs, s_wit⟩ := (mcs_in_prop mcs wit s_in)
    have ⟨i, sat_i⟩ := Proof.MCS_rich s_mcs s_wit
    simp [truth_nom mcs wit s_in] at sat_i
    exists i
    apply Eq.symm
    exact sat_i
  -- absolutely unnecesarily ugly, but at least it works
  . intro ⟨needs_dummy, s_is_dummy⟩
    apply Or.elim needs_dummy
    . intro ⟨i, h⟩
      apply Or.inl
      exists i
      simp [StandardCompletedModel]
      apply Subtype.eq
      apply choice_intro (λ Γ => Γ = s.1)
      rw [h,]
      intro s' eq
      rw [←Set.singleton_eq_singleton_iff]
      apply Eq.symm
      rw [s_is_dummy]
      exact eq
    . intro ⟨i, h⟩
      apply Or.inr
      exists i
      simp [StandardCompletedI]
      apply Subtype.eq
      apply choice_intro (λ Γ => Γ = s.1)
      rw [h]
      intro s' eq
      rw [←Set.singleton_eq_singleton_iff]
      apply Eq.symm
      rw [s_is_dummy]
      exact eq

lemma truth_ex : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) → (∀ {χ : Form TotalSet}, χ.depth < (ex x, ψ).depth → statement χ mcs wit) → statement (ex x, ψ) mcs wit := by
  intro Θ mcs wit ih
  intro Δ Δ_in
  have ⟨Δ_mcs, Δ_wit⟩ := (mcs_in_prop mcs wit Δ_in)
  apply Iff.intro
  . intro h
    have ⟨i, mem⟩ := Δ_wit h
    have ih_s := @ih (ψ[i//x]) subst_depth''
    rw [ih_s Δ_in] at mem
    apply WeakSoundness Proof.ax_q2_contrap
    exact mem
  . simp only [ex_sat]
    intro ⟨g', g'_var, g'_ψ⟩
    let s := g' x
    apply Or.elim (has_state_symbol s)
    . intro ⟨i, sat_i⟩
      have ih_s := @ih (ψ[i//x]) subst_depth''
      rw [←nom_substitution (is_variant_symm.mp g'_var) (Eq.symm sat_i), ←ih_s] at g'_ψ
      have g'_ψ := Proof.Γ_premise g'_ψ
      clear g'_var sat_i
      apply Proof.MCS_pf Δ_mcs
      apply Proof.Γ_mp
      . apply Proof.Γ_theorem
        apply Proof.ax_q2_contrap
        exact i
      . exact g'_ψ
    . intro ⟨y, sat_y⟩
      have := rename_all_bound ψ y (StandardCompletedModel mcs wit) (coe Δ mcs wit Δ_in) g'
      rw [iff_sat] at this
      rw [this] at g'_ψ
      clear this
      rw [←svar_substitution (substable_after_replace ψ) (is_variant_symm.mp g'_var) (Eq.symm sat_y)] at g'_ψ
      have r_ih := @ih ((ψ.replace_bound y)[y//x]) replace_bound_depth'
      rw [←r_ih] at g'_ψ
      have := Proof.MCS_with_svar_witness (substable_after_replace ψ) Δ_mcs g'_ψ
      apply Proof.MCS_mp Δ_mcs; apply Proof.MCS_thm Δ_mcs
    --  exact @exists_replace x ψ y
      apply exists_replace; exact y; exact this

/-- Extend `MCS_in` along a witnessed-model edge (`path_root` on the second path component). -/
lemma mcs_in_witnessed_succ {Θ Δ Δ' : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ)
    (_hΔ : Δ.MCS_in mcs wit) (hR : (WitnessedModel mcs wit).R Δ Δ') : Δ'.MCS_in mcs wit := by
  simp only [WitnessedModel, Set.GeneratedSubmodel] at hR
  obtain ⟨_, ⟨m, hpath⟩, _⟩ := hR
  exists m
  exact path_root Θ witnessed hpath

/-- Extract the witnessed edge from a completed-model step (no dummy glue). -/
lemma completed_to_witnessed {Θ Δ Δ' : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ)
    (_hΔ : Δ.MCS_in mcs wit) (hR : (CompletedModel mcs wit).R Δ Δ') :
    (WitnessedModel mcs wit).R Δ Δ' := by
  simp only [CompletedModel] at hR
  cases hR with
  | inl hW => exact hW
  | inr h =>
    exfalso
    rw [h.1] at _hΔ
    exact (mcs_in_prop mcs wit _hΔ).1.1 (Proof.Γ_premise (Set.mem_singleton Form.bttm))

lemma mcs_in_completed_succ {Θ Δ Δ' : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ)
    (hΔ : Δ.MCS_in mcs wit) (hR : (CompletedModel mcs wit).R Δ Δ') : Δ'.MCS_in mcs wit :=
  mcs_in_witnessed_succ mcs wit hΔ (completed_to_witnessed mcs wit hΔ hR)

lemma completed_canonical {Θ Δ Δ' : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ)
    (hΔ : Δ.MCS_in mcs wit) (hR : (CompletedModel mcs wit).R Δ Δ') : Canonical.R Δ Δ' :=
  (completed_to_witnessed mcs wit hΔ hR).2.2

/-- Freshness for the diamond successor seed `{ψ} ∪ {χ | □χ ∈ Δ}`.
    Requires the Henkin `set_family` infrastructure (`witnessed Δ`, `◇ψ ∈ Δ`). -/
lemma enough_noms_diamond_seed {Δ : Set (Form TotalSet)} (ψ : Form TotalSet)
    (wit : witnessed Δ) (hdia : ◇ψ ∈ Δ) :
    enough_noms ({ψ} ∪ {χ | □χ ∈ Δ}) := by
  admit

/-- K-distribution lifted to theorems: `□` is monotone under provable implication. -/
def nec_mono {N : Set ℕ} {a b : Form N} (h : ⊢ (a ⟶ b)) : ⊢ (□ a ⟶ □ b) :=
  Proof.mp Proof.ax_k (Proof.necess h)

/-- `□` distributes over conjunction inside an MCS. -/
lemma box_conj_mem {Δ : Set (Form TotalSet)} (mcs : MCS Δ) {a b : Form TotalSet}
    (h1 : □ a ∈ Δ) (h2 : □ b ∈ Δ) : □ (a ⋀ b) ∈ Δ := by
  have s1 : (□ a ⟶ □ (b ⟶ (a ⋀ b))) ∈ Δ :=
    Proof.MCS_thm mcs (nec_mono (Proof.tautology conj_intro))
  have s2 : □ (b ⟶ (a ⋀ b)) ∈ Δ := Proof.MCS_mp mcs s1 h1
  have s3 : (□ (b ⟶ (a ⋀ b)) ⟶ (□ b ⟶ □ (a ⋀ b))) ∈ Δ := Proof.MCS_thm mcs Proof.ax_k
  have s4 : (□ b ⟶ □ (a ⋀ b)) ∈ Δ := Proof.MCS_mp mcs s3 s2
  exact Proof.MCS_mp mcs s4 h2

/-- The conjunction of any finite list of `{χ | □χ ∈ Δ}`-members has its box in `Δ`. -/
lemma box_conjunction_mem {Δ : Set (Form TotalSet)} (mcs : MCS Δ)
    (L : List ↥{χ : Form TotalSet | □ χ ∈ Δ}) :
    □ (conjunction {χ : Form TotalSet | □ χ ∈ Δ} L) ∈ Δ := by
  induction L with
  | nil => exact Proof.MCS_thm mcs (Proof.necess (Proof.tautology imp_refl))
  | cons c t ih =>
      have hc : □ c.val ∈ Δ := c.2
      exact box_conj_mem mcs hc ih

/-- If everything provable from `{χ | □χ ∈ Δ}` boxes back into `Δ`: `□`-introduction
    over the canonical predecessor set. -/
lemma box_of_consequence {Δ : Set (Form TotalSet)} (mcs : MCS Δ) {α : Form TotalSet}
    (h : {χ : Form TotalSet | □ χ ∈ Δ} ⊢ α) : □ α ∈ Δ := by
  obtain ⟨L, pf⟩ := h
  have hconjbox := box_conjunction_mem mcs L
  have hmono : (□ (conjunction {χ : Form TotalSet | □ χ ∈ Δ} L) ⟶ □ α) ∈ Δ :=
    Proof.MCS_thm mcs (nec_mono pf)
  exact Proof.MCS_mp mcs hmono hconjbox

/-- If `◇ψ ∈ Δ` and `Δ` is MCS, the one-step successor seed
    `{ψ} ∪ {χ | □χ ∈ Δ}` is consistent.  (Oltean's `set_family` base case.) -/
theorem diamond_extension_consistent {Δ : Set (Form TotalSet)} (mcs : MCS Δ) (ψ : Form TotalSet)
    (hdia : ◇ψ ∈ Δ) : consistent ({ψ} ∪ {χ | □χ ∈ Δ}) := by
  intro hcon
  rw [Set.union_comm] at hcon
  have hB : {χ : Form TotalSet | □ χ ∈ Δ} ⊢ (ψ ⟶ ⊥) := Proof.Deduction.mpr hcon
  have hbox : □ (ψ ⟶ ⊥) ∈ Δ := box_of_consequence mcs hB
  have hdia' : (□ (ψ ⟶ ⊥) ⟶ ⊥) ∈ Δ := hdia
  exact mcs.1 (Proof.Γ_premise (Proof.MCS_mp mcs hdia' hbox))

/-- Lindenbaum extension of the successor seed: an MCS `Γ'` with `Canonical.R Δ Γ'` and `ψ ∈ Γ'`. -/
theorem diamond_succ_mcs {Δ : Set (Form TotalSet)} (mcs : MCS Δ) (wit : witnessed Δ) (ψ : Form TotalSet)
    (hdia : ◇ψ ∈ Δ) :
    ∃ Γ' : Set (Form TotalSet),
      Canonical.R Δ Γ' ∧ ψ ∈ Γ' ∧ MCS Γ' ∧ witnessed Γ' := by
  let Γ₀ := {ψ} ∪ {χ | □χ ∈ Δ}
  have hcons := diamond_extension_consistent mcs ψ hdia
  have hnom := enough_noms_diamond_seed ψ wit hdia
  obtain ⟨Γ', hsub, hmcs, hwit⟩ := WitnessedLindenbaumLemma Γ₀ hcons hnom
  refine ⟨Γ', ?_, hsub (Or.inl (Set.mem_singleton ψ)), hmcs, hwit⟩
  simp only [Canonical, restrict_by, mcs, hmcs, true_and]
  intro φ hbox
  exact hsub (Or.inr (by simp [hbox]))

/-- Extend a restrict-by-witnessed path along one canonical step. -/
lemma restrict_canonical_succ {Θ Δ Δ' : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ)
    (hΔ : Δ.MCS_in mcs wit) (hR : Canonical.R Δ Δ') (hΔ' : witnessed Δ') :
    ∃ n, path (restrict_by witnessed Canonical.R) Θ Δ' n := by
  obtain ⟨n, hpath⟩ := mcs_in_wit mcs wit hΔ
  have hw : witnessed Δ := (mcs_in_prop mcs wit hΔ).2
  refine ⟨n + 1, Δ, ⟨hw, hΔ', hR⟩, hpath⟩

/-- From `◇ψ ∈ Δ` build a completed-model successor of `Δ` that contains `ψ`. -/
lemma diamond_completed_succ {Θ Δ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ)
    (hΔ : Δ.MCS_in mcs wit) (ψ : Form TotalSet) (hdia : ◇ψ ∈ Δ) :
    ∃ Δ' : Set (Form TotalSet),
      Δ'.MCS_in mcs wit ∧ (CompletedModel mcs wit).R Δ Δ' ∧ (ψ ∈ Δ') := by
  have ⟨Δ_mcs, hwitΔ⟩ := mcs_in_prop mcs wit hΔ
  obtain ⟨Γ', hcan, hψ, hmcs, hwitΓ'⟩ := diamond_succ_mcs Δ_mcs hwitΔ ψ hdia
  obtain ⟨m, hpath⟩ := restrict_canonical_succ mcs wit hΔ hcan hwitΓ'
  have hW : (WitnessedModel mcs wit).R Δ Γ' := by
    simp only [WitnessedModel, Set.GeneratedSubmodel]
    obtain ⟨n, hΔpath⟩ := mcs_in_wit mcs wit hΔ
    exact ⟨⟨n, hΔpath⟩, ⟨m, hpath⟩, hcan⟩
  refine ⟨Γ', mcs_in_witnessed_succ mcs wit hΔ hW, Or.inl hW, hψ⟩

-- Truth lemma, □ case.  Oltean's original development never formalized this case (nor
-- `truth_all` for `∀`); the arxiv blueprint lists `truth_box` as TL work.  The → direction
-- uses `R_nec` on witnessed/canonical successors and the subformula IH; the ← direction
-- uses MCS maximality + `diamond_completed_succ` (blocked on `diamond_extension_consistent`
-- and witnessed lift in `diamond_succ_mcs`).
lemma truth_box {ψ : Form TotalSet} : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) →
    (statement ψ mcs wit) → statement (□ψ) mcs wit := by
  intro Θ mcs wit ih Δ h_in
  have ⟨Δ_mcs, _⟩ := mcs_in_prop mcs wit h_in
  apply Iff.intro
  · intro h_box
    simp only [Sat]
    intro s' hR
    have hR' : (CompletedModel mcs wit).R Δ s'.1 := hR
    cases s'.2 with
    | inl _ =>
      have hΔ' := mcs_in_completed_succ mcs wit h_in hR'
      have hmem := R_nec h_box (completed_canonical mcs wit h_in hR')
      exact (ih hΔ').mp hmem
    | inr hdummy =>
      exfalso
      rcases hdummy with ⟨_, hbot⟩
      have hbot_in := mcs_in_completed_succ mcs wit h_in hR'
      rw [hbot] at hbot_in
      exact (mcs_in_prop mcs wit hbot_in).1.1 (Proof.Γ_premise (Set.mem_singleton Form.bttm))
  · intro h_sat
    by_cases h : □ψ ∈ Δ
    · exact h
    · exfalso
      have hnec : ∼(□ψ) ∈ Δ := (Proof.MCS_max Δ_mcs).mp h
      have hdia : ◇∼ψ ∈ Δ :=
        Proof.MCS_pf Δ_mcs (Proof.Γ_mp (Proof.Γ_theorem (@Proof.not_nec_to_diamond TotalSet ψ) Δ) (Proof.Γ_premise hnec))
      obtain ⟨Δ', hΔ'in, hR', hneg⟩ := diamond_completed_succ mcs wit h_in (∼ψ) hdia
      have hsatψ : (StandardCompletedModel mcs wit, coe Δ' mcs wit hΔ'in, StandardCompletedI mcs wit) ⊨ ψ := by
        simp only [Sat] at h_sat
        exact h_sat (coe Δ' mcs wit hΔ'in) (by simpa [StandardCompletedModel, CompletedModel, coe] using hR')
      have hψmem : ψ ∈ Δ' := (ih hΔ'in).mpr hsatψ
      have ⟨Δ'_mcs, _⟩ := mcs_in_prop mcs wit hΔ'in
      have hbot : Form.bttm ∈ Δ' := Proof.MCS_mp Δ'_mcs hneg hψmem
      exact Δ'_mcs.1 (Proof.Γ_premise hbot)

-- Truth lemma, `∀` case.  Handled uniformly (free and non-free `x`) by the dual of the
-- `truth_ex` machinery: in the completed model every state is named by a nominal or an
-- svar (`has_state_symbol`), so each variant reduces to a substitution instance of `ψ`
-- whose statement is available through the depth-indexed `ih`.  Forward uses the `ax_q2`
-- instances; backward uses `witnessed` on `ex x, ∼ψ` (via `bind_dual`) for a contradiction.
lemma truth_all {ψ : Form TotalSet} {x : SVAR} : ∀ {Θ : Set (Form TotalSet)}, (mcs : MCS Θ) → (wit : witnessed Θ) →
    (∀ {χ : Form TotalSet}, χ.depth < (all x, ψ).depth → statement χ mcs wit) → statement (all x, ψ) mcs wit := by
  intro Θ mcs wit ih Δ h_in
  have ⟨Δ_mcs, Δ_wit⟩ := (mcs_in_prop mcs wit h_in)
  apply Iff.intro
  · -- forward: `(all x, ψ) ∈ Δ → satisfaction`
    intro hall
    simp only [Sat]
    intro g' hvar
    apply Or.elim (has_state_symbol (g' x))
    · -- the variant value is named by a nominal `i`
      intro ⟨i, sat_i⟩
      have hmem : ψ[i//x] ∈ Δ :=
        Proof.MCS_pf Δ_mcs (Proof.Γ_mp (Proof.Γ_theorem (Proof.ax_q2_nom ψ x i) Δ) (Proof.Γ_premise hall))
      have hsatsub := ((@ih (ψ[i//x]) subst_depth_bind) h_in).mp hmem
      exact (nom_substitution (is_variant_symm.mp hvar) sat_i.symm).mp hsatsub
    · -- the variant value is named by an svar `y`; rename bound vars to substitute safely
      intro ⟨y, sat_y⟩
      have hpf : ⊢ ((all x, ψ) ⟶ ((ψ.replace_bound y)[y//x])) :=
        Proof.hs
          (Proof.mp Proof.b363 (Proof.general x (Proof.mp (Proof.tautology iff_elim_l) (rename_all_bound_pf ψ y))))
          (Proof.ax_q2_svar (ψ.replace_bound y) x y (substable_after_replace ψ))
      have hmem : ((ψ.replace_bound y)[y//x]) ∈ Δ :=
        Proof.MCS_pf Δ_mcs (Proof.Γ_mp (Proof.Γ_theorem hpf Δ) (Proof.Γ_premise hall))
      have hdepth : ((ψ.replace_bound y)[y//x]).depth < (all x, ψ).depth := by
        rw [subst_depth', replace_bound_depth]; exact sub_depth_bind x ψ
      have hsatsub := ((@ih ((ψ.replace_bound y)[y//x]) hdepth) h_in).mp hmem
      have hsatrepl :=
        (svar_substitution (substable_after_replace ψ) (is_variant_symm.mp hvar) sat_y.symm).mp hsatsub
      have hren := rename_all_bound ψ y (StandardCompletedModel mcs wit) (coe Δ mcs wit h_in) g'
      rw [iff_sat] at hren
      exact hren.mpr hsatrepl
  · -- backward: `satisfaction → (all x, ψ) ∈ Δ`
    intro hsat
    by_contra hnotmem
    have hex : (ex x, ∼ψ) ∈ Δ := by
      by_contra hc
      have h2 : (∼(ex x, ∼ψ)) ∈ Δ := (Proof.MCS_max Δ_mcs).mp hc
      exact hnotmem ((Proof.MCS_rw Δ_mcs Proof.bind_dual).mpr h2)
    obtain ⟨i, hwit⟩ := Δ_wit hex
    have hwit' : (∼(ψ[i//x])) ∈ Δ := by
      have heq : (∼ψ)[i//x] = ∼(ψ[i//x]) := rfl
      rwa [heq] at hwit
    let g := Function.update (StandardCompletedI mcs wit) x ((StandardCompletedModel mcs wit).Vₙ i)
    have hgvar : is_variant g (StandardCompletedI mcs wit) x := by
      intro z hz; exact Function.update_of_ne (Ne.symm hz) _ _
    have hgx : g x = (StandardCompletedModel mcs wit).Vₙ i := Function.update_self x _ _
    have hsatg := hsat g hgvar
    have hsatsub := (nom_substitution (is_variant_symm.mp hgvar) hgx).mpr hsatg
    have hmem : ψ[i//x] ∈ Δ := ((@ih (ψ[i//x]) subst_depth_bind) h_in).mpr hsatsub
    exact (Proof.MCS_max Δ_mcs).mpr hwit' hmem

/-- The truth lemma: membership in an `MCS_in` state coincides with satisfaction in the
    completed model.  Structural cases use the `truth_*` lemmas; `ex` uses `truth_ex`. -/
theorem TruthLemma (φ : Form TotalSet) {Θ : Set (Form TotalSet)} (mcs : MCS Θ) (wit : witnessed Θ) :
    statement φ mcs wit := by
  cases φ with
  | bttm => exact truth_bttm mcs wit
  | prop p => exact truth_prop mcs wit
  | nom i => exact truth_nom mcs wit
  | svar x => exact truth_svar mcs wit
  | impl ψ χ => exact truth_impl (φ := ψ) (ψ := χ) mcs wit (TruthLemma ψ mcs wit) (TruthLemma χ mcs wit)
  | box ψ => exact truth_box mcs wit (TruthLemma ψ mcs wit)
  | bind x ψ => exact truth_all (ψ := ψ) (x := x) mcs wit (fun {χ} _ => TruthLemma χ mcs wit)
termination_by φ.depth
decreasing_by
  all_goals first
    | exact sub_depth_impl_l _ _
    | exact sub_depth_impl_r _ _
    | exact sub_depth_box _
    | assumption
