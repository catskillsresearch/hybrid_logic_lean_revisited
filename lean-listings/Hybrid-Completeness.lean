import Hybrid.Soundness
import Hybrid.ProofUtils
import Hybrid.Lindenbaum
import Hybrid.LanguageExtension
import Hybrid.CompletedModel

section Lemmas
  theorem satisfiable_iff_nocontradiction (Gamma : Set (Form N)) : satisfiable Gamma  <->  Gamma  |/=  False := by
    apply Iff.intro <;> {
    . intro h
      simp at h  |- 
      conv => rhs; intro M; rhs; intro s; rhs; intro g; intro phi; rw [disj_comm]
      exact h
    }
  
  theorem unsatisfiable_iff_contradiction (Gamma : Set (Form N)) : not satisfiable Gamma  <->  Gamma  |=  False := by
    conv => rhs; rw [ <- @not_not (Gamma  |=  False)]
    apply Iff.not
    apply satisfiable_iff_nocontradiction
  
  theorem notsatnot {Gamma : Set (Form N)} {phi : Form N} : (Gamma |= phi)  <->  not satisfiable (Gamma  U  {~phi}) := by
    rw [unsatisfiable_iff_contradiction,  <- SemanticDeduction,  <- Form.neg, Entails, Entails]
    conv => rhs; intro M s g h; rw [neg_sat, neg_sat, not_not]

  theorem notprove_consistentnot : (Gamma  |/-  phi)  ->  consistent (Gamma  U  {~phi}) := by
    intro h
    rw [ <- @not_not (consistent (Gamma  U  {~phi}))]
    intro habs
    have <habs, _> := not_forall.mp habs
    apply h
    exact Proof.dn_equiv_premise.mp (Proof.Deduction.mpr habs)

end Lemmas


def completeness_statement := fun  (N : Set Nat) => (forall  (Gamma : Set (Form N)) (phi : Form N), Gamma  |=  phi  ->  (exists  _ : Gamma  |-  phi, True))
def cons_sat_statement     := fun  (N : Set Nat) => (forall  (Gamma : Set (Form N)), consistent Gamma  ->  satisfiable Gamma)

theorem ModelExistence {N : Set Nat} : completeness_statement N  <->  cons_sat_statement N := by
  apply Iff.intro
  . intro h
    rw [ <- @not_not (cons_sat_statement N)]
    intro habs
    rw [cons_sat_statement, negated_universal] at habs
    match habs with
    | <Delta, hw> =>
      rw [negated_impl] at hw
      have <consistent, not_satisfiable>  := hw
      rw [unsatisfiable_iff_contradiction] at not_satisfiable
      have <by_completeness, _> := (h Delta False) not_satisfiable
      exact consistent by_completeness
  . rw [contraposition (cons_sat_statement N) (completeness_statement N)]
    intro h
    simp only [completeness_statement, not_forall, negated_impl, notsatnot,  <- conj_comm] at h
    have <Gamma, phi, wit_l, wit_r> := h
    intro hcontra
    apply wit_l
    apply hcontra
    apply notprove_consistentnot
    intro pf
    apply wit_r
    exact <pf, trivial>

section ConsSat

/-- Lift consistency from the base language to the totalized set on `TotalSet`.
    Backward conservativity (`syntactic_conservativity`) pulls a hypothetical
    `Set.total Gamma  |-  False` back to `Gamma  |-  False`.  Requires `N` nonempty to pick a base
    nominal for alien elimination. -/
lemma consistent_total (Gamma : Set (Form N)) (hN : N.Nonempty) (h : consistent Gamma) :
    consistent (Set.total Gamma) := by
  intro hcon
  exact h (syntactic_conservativity hN (phi := (False : Form N)) hcon)

/-- **Model-existence / `cons_sat` core.**  Pipeline:
    1. `consistent_total` -- lift consistency to `Set.total Gamma`
    2. `ExtendedLindenbaumLemma` -- extend to a witnessed MCS `Theta` with `(Set.total Gamma).odd_noms  subseteq  Theta`
    3. `TruthLemma` at the root state `Theta`
    4. `sat_odd_noms'` + `sat_total` -- pull satisfaction back to `Form N` / `Model N` -/
theorem cons_sat (Gamma : Set (Form N)) (hN : N.Nonempty) (h : consistent Gamma) : satisfiable Gamma := by
  have hcons' := consistent_total Gamma hN h
  obtain <Theta, hsub, hmcs, hwit> := ExtendedLindenbaumLemma (Set.total Gamma) hcons'
  let M := StandardCompletedModel hmcs hwit
  let g := StandardCompletedI hmcs hwit
  have hTheta_in : Theta.MCS_in hmcs hwit := by
    simp [Set.MCS_in, WitnessedModel, path]
    exact <0, rfl>
  let s : M.W := <Theta, Or.inl hTheta_in>
  refine <Model.ofTotal M.odd_noms_inv, s, g, ?_>
  intro phi hphi
  have hmem' : phi.total.odd_noms  in  (Set.total Gamma).odd_noms := by
    refine <phi.total, <phi, hphi, rfl>, rfl>
  have hmem : phi.total.odd_noms  in  Theta := hsub hmem'
  have hsat_odd : @Sat TotalSet M s g (phi.total).odd_noms :=
    (TruthLemma (phi.total.odd_noms) hmcs hwit (Delta := Theta) hTheta_in).mp hmem
  have hsat_total : @Sat TotalSet M.odd_noms_inv s g phi.total :=
    (sat_odd_noms' (M := M) (s := s) (g := g) (phi := phi.total)).mp hsat_odd
  exact (sat_total M.odd_noms_inv s g phi).mp hsat_total

end ConsSat

noncomputable def Completeness (hN : N.Nonempty) :
    (forall  (Gamma : Set (Form N)) (phi : Form N), Gamma  |=  phi  ->  Gamma  |-  phi) := by
  intros h1 h2 h3; apply Exists.choose
  revert h1 h2 h3
  rw [ <- completeness_statement, ModelExistence]
  unfold cons_sat_statement
  intro Gamma h
  exact cons_sat Gamma hN h
