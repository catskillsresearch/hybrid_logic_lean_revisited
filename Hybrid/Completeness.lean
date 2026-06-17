import Hybrid.Soundness
import Hybrid.ProofUtils
import Hybrid.Lindenbaum
import Hybrid.LanguageExtension
import Hybrid.CompletedModel

section Lemmas
  theorem satisfiable_iff_nocontradiction (Γ : Set (Form N)) : satisfiable Γ ↔ Γ ⊭ ⊥ := by
    apply Iff.intro <;> {
    . intro h
      simp at h ⊢
      conv => rhs; intro M; rhs; intro s; rhs; intro g; intro φ; rw [disj_comm]
      exact h
    }
  
  theorem unsatisfiable_iff_contradiction (Γ : Set (Form N)) : ¬satisfiable Γ ↔ Γ ⊨ ⊥ := by
    conv => rhs; rw [←@not_not (Γ ⊨ ⊥)]
    apply Iff.not
    apply satisfiable_iff_nocontradiction
  
  theorem notsatnot {Γ : Set (Form N)} {φ : Form N} : (Γ⊨φ) ↔ ¬satisfiable (Γ ∪ {∼φ}) := by
    rw [unsatisfiable_iff_contradiction, ←SemanticDeduction, ←Form.neg, Entails, Entails]
    conv => rhs; intro M s g h; rw [neg_sat, neg_sat, not_not]

  theorem notprove_consistentnot : (Γ ⊬ φ) → consistent (Γ ∪ {∼φ}) := by
    intro h
    rw [←@not_not (consistent (Γ ∪ {∼φ}))]
    intro habs
    have ⟨habs, _⟩ := not_forall.mp habs
    apply h
    exact Proof.dn_equiv_premise.mp (Proof.Deduction.mpr habs)

end Lemmas


def completeness_statement := λ (N : Set ℕ) => (∀ (Γ : Set (Form N)) (φ : Form N), Γ ⊨ φ → (∃ _ : Γ ⊢ φ, True))
def cons_sat_statement     := λ (N : Set ℕ) => (∀ (Γ : Set (Form N)), consistent Γ → satisfiable Γ)

theorem ModelExistence {N : Set ℕ} : completeness_statement N ↔ cons_sat_statement N := by
  apply Iff.intro
  . intro h
    rw [←@not_not (cons_sat_statement N)]
    intro habs
    rw [cons_sat_statement, negated_universal] at habs
    match habs with
    | ⟨Δ, hw⟩ =>
      rw [negated_impl] at hw
      have ⟨consistent, not_satisfiable⟩  := hw
      rw [unsatisfiable_iff_contradiction] at not_satisfiable
      have ⟨by_completeness, _⟩ := (h Δ ⊥) not_satisfiable
      exact consistent by_completeness
  . rw [contraposition (cons_sat_statement N) (completeness_statement N)]
    intro h
    simp only [completeness_statement, not_forall, negated_impl, notsatnot, ←conj_comm] at h
    have ⟨Γ, φ, wit_l, wit_r⟩ := h
    intro hcontra
    apply wit_l
    apply hcontra
    apply notprove_consistentnot
    intro pf
    apply wit_r
    exact ⟨pf, trivial⟩

section ConsSat

/-- Lift consistency from the base language to the totalized set on `TotalSet`.
    **Blocker:** needs `pf_extended` backward (conservativity) on `SyntacticConsequence`. -/
lemma consistent_total (Γ : Set (Form N)) (h : consistent Γ) : consistent (Set.total Γ) := by
  admit

/-- **Model-existence / `cons_sat` core.**  Pipeline:
    1. `consistent_total` — lift consistency to `Set.total Γ`
    2. `ExtendedLindenbaumLemma` — extend to a witnessed MCS `Θ` with `(Set.total Γ).odd_noms ⊆ Θ`
    3. `TruthLemma` at the root state `Θ`
    4. `sat_odd_noms'` + `sat_total` — pull satisfaction back to `Form N` / `Model N` -/
theorem cons_sat (Γ : Set (Form N)) (h : consistent Γ) : satisfiable Γ := by
  have hcons' := consistent_total Γ h
  obtain ⟨Θ, hsub, hmcs, hwit⟩ := ExtendedLindenbaumLemma (Set.total Γ) hcons'
  let M := StandardCompletedModel hmcs hwit
  let g := StandardCompletedI hmcs hwit
  have hΘ_in : Θ.MCS_in hmcs hwit := by
    simp [Set.MCS_in, WitnessedModel, path]
    exact ⟨0, rfl⟩
  let s : M.W := ⟨Θ, Or.inl hΘ_in⟩
  refine ⟨Model.ofTotal M.odd_noms_inv, s, g, ?_⟩
  intro φ hφ
  have hmem' : φ.total.odd_noms ∈ (Set.total Γ).odd_noms := by
    refine ⟨φ.total, ⟨φ, hφ, rfl⟩, rfl⟩
  have hmem : φ.total.odd_noms ∈ Θ := hsub hmem'
  have hsat_odd : @Sat TotalSet M s g (φ.total).odd_noms :=
    (TruthLemma (φ.total.odd_noms) hmcs hwit (Δ := Θ) hΘ_in).mp hmem
  have hsat_total : @Sat TotalSet M.odd_noms_inv s g φ.total :=
    (sat_odd_noms' (M := M) (s := s) (g := g) (φ := φ.total)).mp hsat_odd
  exact (sat_total M.odd_noms_inv s g φ).mp hsat_total

end ConsSat

noncomputable def Completeness : (∀ (Γ : Set (Form N)) (φ : Form N), Γ ⊨ φ → Γ ⊢ φ) := by
  intros h1 h2 h3; apply Exists.choose
  revert h1 h2 h3
  rw [←completeness_statement, ModelExistence]
  unfold cons_sat_statement
  intro Γ h
  exact cons_sat Γ h
