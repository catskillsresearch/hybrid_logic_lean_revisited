import Hybrid.Substitutions
import Hybrid.Proof
import Hybrid.ListUtils

namespace Proof

noncomputable section

def iff_mp (h : ⊢ (φ ⟷ ψ)) : ⊢ (φ ⟶ ψ) :=
  mp (tautology conj_elim_l) h

def iff_mpr (h : ⊢ (φ ⟷ ψ)) : ⊢ (ψ ⟶ φ) :=
  mp (tautology conj_elim_r) h

def hs (h1 : ⊢ (φ ⟶ ψ)) (h2 : ⊢ (ψ ⟶ χ)) : ⊢ (φ ⟶ χ) :=
  mp (mp (tautology hs_taut) h1) h2

def rename_bound {φ : Form N} (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ ((all x, φ) ⟷ all y, φ[y // x]) := by
  rw [Form.iff]
  apply mp
  . apply mp
    . apply tautology
      apply conj_intro
    . have l1 := ax_q2_svar φ x y h2
      have l2 := general y l1
      have l3 := ax_q1 (all x, φ) (φ[y // x]) (notoccurs_notfree h1)
      have l4 := mp l3 l2
      exact l4
  . have ⟨resubst, reid⟩ := rereplacement φ x y h1 h2
    have l1 := ax_q2_svar (φ[y//x]) y x resubst
    rw [reid] at l1
    have l3 := general x l1
    by_cases xy : x = y
    . rw [←xy] at h1
      have notf := preserve_notfree x y (notoccurs_notfree (@notocc_beforeafter_subst N φ x y h1))
      have l4 := ax_q1 (all y, φ[y//x]) φ notf
      have l5 := mp l4 l3
      exact l5
    . have notf := preserve_notfree x y (@notfree_after_subst N φ x y xy)
      have l4 := ax_q1 (all y, φ[y//x]) φ notf
      have l5 := mp l4 l3
      exact l5

def rename_bound_ex (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ ((ex x, φ) ⟷ ex y, φ[y // x]) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply mp
    . apply tautology
      apply iff_elim_l
    . apply tautology
      apply iff_not
  .
    apply rename_bound
    repeat { simp [occurs, is_substable]; assumption }

-- Quite bothersome to work with subtypes and coerce properly.
-- The code looks ugly, but in essence it follows the proof given
-- in LaTeX.
def Deduction {Γ : Set (Form N)} : Γ ⊢ (ψ ⟶ φ) iff (Γ ∪ {ψ}) ⊢ φ := by
  apply TypeIff.intro
  . intro h
    match h with
    | ⟨L, hpf⟩ =>
        have l1 := mp (tautology com12) hpf
        have l2 := mp (tautology imp) l1
        have pfmem : ψ ∈ Γ ∪ {ψ} := by simp
        let L' : List ↑(Γ ∪ {ψ}) := ⟨ψ, pfmem⟩ :: list_convert L
        rw [conj_incl] at l2
        exact ⟨L', l2⟩
  . intro h
    match h with
    | ⟨L', hpf⟩ =>
      have t_ax1 := tautology (@ax_1 N (conjunction (Γ ∪ {ψ}) L'⟶φ) ψ)
      have l1 := mp t_ax1 hpf
      have l2 := mp (tautology com12) l1
      by_cases elem : elem' L' ψ
      . have t_help := tautology (deduction_helper L' ψ (ψ⟶φ) elem)
        have l3 := mp t_help l2
        have l4 := mp (tautology idem) l3
        have not_elem_L' := eq_false_of_ne_true (@filter'_filters N Γ ψ L')
        let L : List Γ := list_convert_rev (filter' L' ψ) not_elem_L'
        rw [conj_incl_rev (filter' L' ψ) not_elem_L'] at l4
        exact ⟨L, l4⟩
      . have elem : elem' L' ψ = false := by simp only [elem]
        let L : List Γ := list_convert_rev L' elem
        rw [conj_incl_rev L' elem] at l2
        exact ⟨L, l2⟩

def increasing_consequence (h1 : Γ ⊢ φ) (h2 : Γ ⊆ Δ) : Δ ⊢ φ := by
  simp [SyntacticConsequence] at h1 ⊢
  let ⟨L, pf⟩ := h1
  clear h1
  let L' := list_convert_general h2 L
  exists L'
  rw [conj_incl_general h2 L] at pf
  exact pf

def Γ_empty {φ : Form N} : ∅ ⊢ φ iff ⊢ φ := by
  unfold SyntacticConsequence
  apply TypeIff.intro
  . intro pf
    have ⟨L, pf⟩ := pf
    have := empty_list L
    simp [this, conjunction] at pf
    apply mp
    . have : ⊢(((⊥⟶⊥)⟶φ)⟶φ) := by
        apply tautology
        apply imp_taut
        eval
      exact this
    . exact pf
  . intro pf
    exists ([] : List ↑{x : Form N | False})
    simp only [conjunction]
    apply mp
    . apply tautology
      apply ax_1
    . exact pf

def Γ_theorem : ⊢ φ → (∀ Γ, Γ ⊢ φ) := by
  intro h Γ
  apply increasing_consequence
  apply Γ_empty.mpr h
  simp

def Γ_theorem_rev : (∀ Γ, Γ ⊢ φ) → ⊢ φ := by
  intro h
  apply Γ_empty.mp
  apply h

def Γ_theorem_iff : ⊢ φ iff (∀ Γ, Γ ⊢ φ) := by
  apply TypeIff.intro <;> first | apply Γ_theorem | apply Γ_theorem_rev

def Γ_premise : φ ∈ Γ → Γ ⊢ φ := by
  intro mem
  have : Γ = Γ ∪ {φ} := by simp [mem]
  rw [this]
  apply Deduction.mp
  apply Γ_theorem
  apply tautology
  eval

def Γ_mp_helper1 {Γ : Set (Form N)} {φ ψ χ : Form N} : (Γ ⊢ ((φ ⋀ ψ) ⟶ χ)) iff ((Γ ∪ {φ}) ⊢ (ψ ⟶ χ)) := by
  apply TypeIff.intro
  . intro h
    match h with
    | ⟨L, hL⟩ =>
        have l1 := hs hL (tautology exp)
        have l2 : Γ ⊢ (φ ⟶ ψ ⟶ χ) := ⟨L, l1⟩
        have l3 := Deduction.mp l2
        exact l3
  . intro h
    have h := Deduction.mpr h
    match h with
    | ⟨L, hL⟩ =>
        have l1 := hs hL (tautology imp)
        have l2 : Γ ⊢ (φ ⋀ ψ ⟶ χ) := ⟨L, l1⟩
        exact l2

def Γ_mp_helper2 {Γ : Set (Form N)} {L : List Γ} (h : Γ⊢(conjunction Γ L⟶ψ)) : Γ ⊢ ψ := by
  induction L with
  | nil =>
      rw [conjunction] at h
      have ⟨L, hL⟩ := h
      have l1 := mp (tautology com12) hL
      have l2 := mp (tautology (imp_taut imp_refl)) l1
      exists L
  | cons head tail ih =>
      have h := Γ_mp_helper1.mp h
      have : (Γ ∪ {↑head}) = Γ := by simp [head.2]
      rw [this] at h
      exact ih h

def Γ_mp (h1: Γ ⊢ (φ ⟶ ψ)) (h2 : Γ ⊢ φ) : Γ ⊢ ψ := by
  match h1 with
  | ⟨L1, hL1⟩ =>
    match h2 with
    | ⟨L2, hL2⟩ =>
        have := mp (mp (tautology mp_help) hL1) hL2
        have : Γ ⊢ (conjunction Γ L2⟶ψ) := ⟨L1, this⟩
        exact Γ_mp_helper2 this

def Γ_neg_intro {φ : Form N} (h1 : Γ ⊢ (φ ⟶ ψ)) (h2 : Γ ⊢ (φ ⟶ ∼ψ)) : Γ ⊢ (∼φ) := by
  have l1 := tautology (@neg_intro N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  exact l4

def Γ_neg_elim {φ : Form N} {φ : Form N} (h : Γ ⊢ (∼∼φ)) : Γ ⊢ φ := by
  have l1 := tautology (@dne N φ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h
  exact l3

def Γ_conj_intro {φ : Form N} (h1 : Γ ⊢ φ) (h2 : Γ ⊢ ψ) : Γ ⊢ (φ ⋀ ψ) := by
  have l1 := tautology (@conj_intro N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  exact l4

def Γ_conj_elim_l {φ : Form N} (h : Γ ⊢ (φ ⋀ ψ)) : Γ ⊢ φ := by
  have l1 := tautology (@conj_elim_l N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h
  exact l3

def Γ_conj_elim_r {φ : Form N} (h : Γ ⊢ (φ ⋀ ψ)) : Γ ⊢ ψ := by
  have l1 := tautology (@conj_elim_r N φ ψ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h
  exact l3

def Γ_disj_intro_l {φ : Form N} (h : Γ ⊢ φ) : Γ ⊢ (φ ⋁ ψ) := by
  have l1 := tautology (@disj_intro_l N φ ψ)
  have l2 := Γ_theorem l1 Γ
  exact Γ_mp l2 h

def Γ_disj_intro_r {φ : Form N} (h : Γ ⊢ φ) : Γ ⊢ (ψ ⋁ φ) := by
  have l1 := tautology (@disj_intro_r N φ ψ)
  have l2 := Γ_theorem l1 Γ
  exact Γ_mp l2 h

def Γ_disj_elim {φ : Form N} (h1 : Γ ⊢ (φ ⋁ ψ)) (h2 : Γ ⊢ (φ ⟶ χ)) (h3 : Γ ⊢ (ψ ⟶ χ)) : Γ ⊢ χ := by
  have l1 := tautology (@disj_elim N φ ψ χ)
  have l2 := Γ_theorem l1 Γ
  have l3 := Γ_mp l2 h1
  have l4 := Γ_mp l3 h2
  have l5 := Γ_mp l4 h3
  exact l5

def Γ_univ_intro {Γ : Set (Form N)} {φ : Form N} (h1 : ∀ ψ : Γ, is_free x ψ.1 = false) (h2 : occurs y φ = false) (h3 : is_substable φ y x) : Γ ⊢ φ → Γ ⊢ (all y, φ[y // x]) := by
  intro Γ_pf_φ
  match Γ_pf_φ with
  | ⟨L, l1⟩ =>
      have l2 := general x l1
      have := notfreeset L h1
      have l3 := ax_q1 (conjunction Γ L) φ this
      have l4 := mp l3 l2
      have l5 := iff_mp (rename_bound h2 h3)
      have l6 := hs l4 l5
      exact ⟨L, l6⟩

def Γ_univ_intro' {Γ : Set (Form N)} {φ : Form N} (h1 : ∀ ψ : Γ, is_free x ψ.1 = false) : Γ ⊢ φ → Γ ⊢ (all x, φ) := by
  intro Γ_pf_φ
  match Γ_pf_φ with
  | ⟨L, l1⟩ =>
      have l2 := general x l1
      have := notfreeset L h1
      have l3 := ax_q1 (conjunction Γ L) φ this
      have l4 := mp l3 l2
      exists L

def dn_equiv_premise {φ : Form N} : Γ ⊢ (∼∼φ) iff Γ ⊢ φ := by
  have l1 := tautology (@dne N φ)
  have l2 := tautology (@dni N φ)
  rw [SyntacticConsequence, SyntacticConsequence]
  apply TypeIff.intro
  repeat (
    intro ⟨L, _⟩;
    exists L;
    apply hs;
    repeat assumption
  )

section Nominals

def generalize_constants {φ : Form N} {x : SVAR} (i : NOM N) (h : x ≥ φ.new_var) : ⊢ φ → ⊢ (all x, φ[x // i]) := by
    intro pf
    apply general x
    induction pf generalizing x with
    | @tautology φ ht      =>
        apply tautology
        simp [Tautology] at ht ⊢
        intro e
        let f'  : Form N → Bool := λ φ => if (e.f <| φ[x//i]) then true else false
        let e'  : Eval N := ⟨f', by simp [f', e.p1, nom_subst_svar], by simp [f', e.p2, nom_subst_svar]⟩
        have h2 := ht e'
        have e_eq : e'.f φ = (if (e.f <| φ[x//i]) then true else false) := rfl
        rw [e_eq] at h2
        simpa using h2
    | @general φ v _ ih   =>
        simp only [nom_subst_svar, Form.new_var, max] at h ⊢
        by_cases hc : (v + 1).letter > (Form.new_var φ).letter
        . simp [hc] at h
          simp only [gt_iff_lt] at hc
          have := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
          exact general v this
        . simp [hc] at h
          exact general v (ih h)
    | @necess   ψ _ ih     =>
        simp only [nom_subst_svar, occurs] at h ⊢
        apply necess; apply ih; assumption
    | @mp φ ψ _ _ ih1 ih2  =>
        simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false, not_and,
          Bool.not_eq_false] at ih1
        -- show ψ[y // i] for some y that does not
        --    occur in either φ or ψ
        -- generalize, get  all y, ψ[y // i]
        -- then apply axiom Q2 and get:
        --                   (ψ[y // i])[x // y]
        -- this should bring you to:
        --                   ψ[x // i]
        let y := (φ ⟶ ψ).new_var
        have ih1_cond : y ≥ (φ⟶ψ).new_var := Nat.le.refl
        have ⟨ih2_cond, sub_cond⟩ := new_var_geq1 ih1_cond
        have ih1 := ih1 ih1_cond
        have ih2 := ih2 ih2_cond
        rw [nom_subst_svar] at ih1
        have l1  := general y (mp ih1 ih2)
        have l2  := ax_q2_svar (ψ[y//i]) y x (new_var_subst h)
        have l3  := mp l2 l1
        rw [nom_subst_trans i x y sub_cond] at l3
        exact l3
    | @ax_k φ ψ            =>
        simp only [nom_subst_svar]
        apply ax_k
    | @ax_q1 φ ψ v h2       =>
        simp only [nom_subst_svar]
        apply ax_q1
        have := new_var_geq2 (new_var_geq1 h).left
        have ha : x ≥ φ.new_var := (new_var_geq1 this.right).left
        have hb : v ≠ x := diffsvar this.left
        have := (scz i ha hb).mpr
        rw [contraposition, Bool.not_eq_true, Bool.not_eq_true] at this
        apply this
        exact h2
    | @ax_q2_svar φ y v h2  =>
        have := new_var_geq2 (new_var_geq1 h).left
        have c2 : x ≥ φ.new_var := this.right
        have c3 : y ≠ x := diffsvar this.left
        have c  := new_var_subst' i h2 c2 c3
        have l1 := ax_q2_svar (φ[x//i]) y v c
        rw [nom_svar_subst_symm c3] at l1
        exact l1
    | @ax_q2_nom  φ v j    =>
        simp [nom_subst_svar]
        have f3 := diffsvar (new_var_geq2 (new_var_geq1 h).left).left
        by_cases ji : j = i
        . rw [ji] at h ⊢
          have f2 := (new_var_geq2 (new_var_geq1 h).left).right
          have f1 := @new_var_subst'' N φ x v f2
          have := new_var_subst' i f1 f2 f3
          have := ax_q2_svar (φ[x//i]) v x this
          rw [subst_collect_all]
          exact this
        . rw [←(nom_nom_subst_symm ji f3)]
          exact ax_q2_nom (φ[x//i]) v j
    | @ax_name    v        =>
        exact ax_name v
    | @ax_nom   φ v m n    =>
        simp only [nom_subst_svar, nec_subst_nom, pos_subst_nom]
        apply ax_nom
    | @ax_brcn  φ v        =>
        apply ax_brcn

  def generalize_constants_rev {φ : Form N} {x : SVAR} (i : NOM N) (h : x ≥ φ.new_var) : ⊢ (all x, φ[x // i]) → ⊢ φ := by
    intro pf
    have l1 := ax_q2_nom (φ[x//i]) x i
    have l2 := mp l1 pf
    rw [svar_svar_nom_subst h, nom_subst_self] at l2
    exact l2

  def generalize_constants_iff {φ : Form N} {x : SVAR} (i : NOM N) (h : x ≥ φ.new_var) : ⊢ φ iff ⊢ (all x, φ[x // i]) := by
    apply TypeIff.intro
    . apply generalize_constants; assumption
    . apply generalize_constants_rev; assumption

  /-- Forward direction only: rename nominal `j` to `i` throughout a derivation. -/
  def rename_constants_fwd {φ : Form N} (j i : NOM N) (pf : Proof φ) : Proof (φ[j // i]) := by
    let x := φ.new_var
    have x_geq : x ≥ φ.new_var := Nat.le.refl
    have l1 := generalize_constants i x_geq pf
    have l2 := ax_q2_nom (φ[x // i]) x j
    exact svar_svar_nom_subst x_geq ▸ mp l2 l1

  lemma mem_formulasIn_self {φ : Form N} (pf : Proof φ) : φ ∈ pf.formulasIn := by
    induction pf with
    | tautology _ | ax_k | ax_q1 _ _ _ | ax_q2_svar _ _ _ _ | ax_q2_nom _ _ _ | ax_name _ | ax_nom _ _ | ax_brcn =>
        simp [formulasIn]
    | general _ _ => simp [formulasIn]
    | necess _ => simp [formulasIn]
    | mp _ _ _ _ => simp [formulasIn]

  lemma proof_noms_cast {α β : Form N} (h : α = β) (pf : Proof α) :
      (h ▸ pf).proof_noms = pf.proof_noms := by
    subst h; rfl

  private lemma mem_of_list_noms_subst {φ : Form N} (new old : NOM N) (pf : Proof φ) {k : NOM N}
      (hk : k ∈ (φ[new // old]).list_noms) : k ∈ pf.proof_noms ∨ k = new := by
    rcases list_noms_subst hk with ⟨hkφ, _⟩ | hknew
    · exact Or.inl (by
        simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
        exact ⟨φ, mem_formulasIn_self pf, hkφ⟩)
    · exact Or.inr hknew

  private lemma not_mem_old_of_list_noms_subst {φ : Form N} (new old : NOM N) (hne : new ≠ old) {k : NOM N}
      (hk : k ∈ (φ[new // old]).list_noms) (hj : k = old) : False := by
    rcases list_noms_subst hk with ⟨_, hne'⟩ | hnew
    · exact hne' hj
    · exact hne (Eq.symm (Eq.trans (Eq.symm hj) hnew))

  private lemma mem_of_list_noms_q2_implication {ψ : Form N} {x : SVAR} (new old : NOM N) (hx : x ≥ ψ.new_var)
      (pf : Proof ψ) {k : NOM N}
      (hk : k ∈ ((all x, ψ[x // old]) ⟶ (ψ[x // old][new // x])).list_noms) :
      k ∈ pf.proof_noms ∨ k = new := by
    simp only [Form.list_noms, List.mem_dedup, List.mem_merge] at hk
    rcases hk with hk | hk
    · exact Or.inl (by
        simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
        exact ⟨ψ, mem_formulasIn_self pf, (list_noms_nom_subst_svar hx hk).left⟩)
    · exact mem_of_list_noms_subst new old pf (by
        have : k ∈ (ψ[new // old]).list_noms := by rw [← svar_svar_nom_subst (φ := ψ) hx]; exact hk
        exact this)

  private lemma not_mem_old_of_list_noms_q2_implication {ψ : Form N} {x : SVAR} (new old : NOM N)
      (hx : x ≥ ψ.new_var) (hne : new ≠ old) :
      old ∉ ((all x, ψ[x // old]) ⟶ (ψ[x // old][new // x])).list_noms := by
    intro h
    simp only [Form.list_noms, List.mem_dedup, List.mem_merge] at h
    rcases h with h | h
    · exact (list_noms_nom_subst_svar hx h).2 rfl
    · exact not_mem_old_of_list_noms_subst new old hne (by
        have : old ∈ (ψ[new // old]).list_noms := by rw [← svar_svar_nom_subst (φ := ψ) hx]; exact h
        exact this) rfl

  private lemma mem_proof_noms_of_subst_list_noms {φ : Form N} {x : SVAR} (old : NOM N)
      (h : x ≥ φ.new_var) (pf : Proof φ) {k : NOM N} (hk : k ∈ (φ[x // old]).list_noms) :
      k ∈ pf.proof_noms := by
    simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
    exact ⟨φ, mem_formulasIn_self pf, (list_noms_nom_subst_svar h hk).left⟩

  private lemma mem_formulasIn_general {α : Form N} (v : SVAR) (pf : Proof α) {χ : Form N}
      (hχ : χ ∈ pf.formulasIn) : χ ∈ (general v pf).formulasIn := by
    simp [Proof.formulasIn, List.mem_cons]
    exact Or.inr hχ

  private theorem not_mem_proof_noms_generalize_constants {φ : Form N} {x : SVAR} (new old : NOM N)
      (h : x ≥ φ.new_var) (hne : new ≠ old) (pf : Proof φ) :
      old ∉ (generalize_constants old h pf).proof_noms := by
    induction pf generalizing x with
    | tautology _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · rw [hχ] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        · rw [hχ] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        · simp at hχ
    | @general ψ v pf ih =>
        unfold generalize_constants
        have hφ := h
        simp only [nom_subst_svar, Form.new_var, max] at h ⊢
        by_cases hc : (v + 1).letter > (Form.new_var ψ).letter
        · simp [hc] at h
          simp only [gt_iff_lt, ge_iff_le] at hc
          have ih_h := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
          intro hk
          dsimp [proof_noms, formulasIn] at hk
          simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
          obtain ⟨χ, hχ, hkχ⟩ := hk
          rcases hχ with hχ | hχ
          · exact (list_noms_nom_subst_svar hφ (hχ ▸ hkχ)).2 rfl
          · have hχ' := hχ
            simp only [hc, if_pos hc, generalize_constants, Proof.formulasIn, general] at hχ'
            rcases List.mem_cons.mp hχ' with heq | hmem''
            · exact (list_noms_nom_subst_svar hφ (heq ▸ hkχ)).2 rfl
            · have hχ'' := List.mem_cons_of_mem (List.mem_cons_of_mem hmem'')
              exact absurd (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap, generalize_constants, hc, if_pos hc,
                  Proof.formulasIn, general, List.mem_cons]
                exact ⟨χ, hχ'', hkχ⟩) (ih ih_h)
        · simp [hc] at h
          have hxψ : x ≥ ψ.new_var := (new_var_geq2 hφ).2
          intro hk
          dsimp [proof_noms, formulasIn] at hk
          simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
          obtain ⟨χ, hχ, hkχ⟩ := hk
          rcases hχ with hχ | hχ
          · exact (list_noms_nom_subst_svar hφ (hχ ▸ hkχ)).2 rfl
          · have hχ' := hχ
            simp only [hc, if_neg hc, generalize_constants, Proof.formulasIn, general] at hχ'
            rcases List.mem_cons.mp hχ' with heq | hmem''
            · exact (list_noms_nom_subst_svar hφ (heq ▸ hkχ)).2 rfl
            · have hχ'' := List.mem_cons_of_mem (List.mem_cons_of_mem hmem'')
              exact absurd (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap, generalize_constants, hc, if_neg hc,
                  Proof.formulasIn, general, List.mem_cons]
                exact ⟨χ, hχ'', hkχ⟩) (ih hxψ)
    | @necess ψ pf ih =>
        unfold generalize_constants
        have hφ := h
        simp only [nom_subst_svar, occurs] at h ⊢
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ
        · exact (list_noms_nom_subst_svar hφ (hχ ▸ hkχ)).2 rfl
        · have hχ' := hχ
          simp only [Proof.formulasIn, general, generalize_constants] at hχ'
          rcases List.mem_cons.mp hχ' with heq | hmem'
          · exact (list_noms_nom_subst_svar hφ (heq ▸ hkχ)).2 rfl
          · rcases List.mem_cons.mp hmem' with heq | hmem''
            · exact (list_noms_nom_subst_svar hφ (heq ▸ hkχ)).2 rfl
            · have hχ'' := List.mem_cons_of_mem (List.mem_cons_of_mem hmem'')
              exact absurd (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap, generalize_constants,
                  Proof.formulasIn, general, List.mem_cons]
                exact ⟨χ, hχ'', hkχ⟩) (ih h)
    | @mp φ ψ pf1 pf2 ih1 ih2 =>
        unfold generalize_constants
        have hφ := h
        let y := (φ ⟶ ψ).new_var
        have ⟨ih1_x, ih2_x⟩ := new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ
        · exact (list_noms_nom_subst_svar hφ (hχ ▸ hkχ)).2 rfl
        · have hmem := hχ
          simp only [List.mem_append, List.mem_cons] at hmem
          rcases hmem with heq | hmem'
          · exact (list_noms_nom_subst_svar hφ (heq ▸ hkχ)).2 rfl
          · rcases hmem' with hmem' | hmem'
            · exact absurd (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                exact ⟨χ, hmem', hkχ⟩) (ih1 ih1_x)
            · exact absurd (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                exact ⟨χ, hmem', hkχ⟩) (ih2 ih2_x)
    | ax_k =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · rw [hχ] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        · rw [hχ] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        · simp at hχ
    | ax_q1 _ _ _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · rw [hχ] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        · rw [hχ] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        · simp at hχ
    | ax_q2_svar _ _ _ _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · exact (list_noms_nom_subst_svar h (hχ ▸ hkχ)).2 rfl
        · exact (list_noms_nom_subst_svar h (hχ ▸ hkχ)).2 rfl
        · exact hχ.elim
    | ax_q2_nom _ _ _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · exact (list_noms_nom_subst_svar h (hχ ▸ hkχ)).2 rfl
        · exact (list_noms_nom_subst_svar h (hχ ▸ hkχ)).2 rfl
        · exact hχ.elim
    | ax_name _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn, Form.list_noms, nom_subst_svar] at hk
        rcases hk with ⟨_, _, hkχ⟩
        exact hkχ
    | ax_nom _ _ =>
        unfold generalize_constants
        simp only [nom_subst_svar, nec_subst_nom, pos_subst_nom] at h
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · rw [hχ] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        · rw [hχ] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        · simp at hχ
    | ax_brcn =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · rw [hχ] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        · rw [hχ] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        · simp at hχ

  private theorem mem_proof_noms_generalize_constants {φ : Form N} {x : SVAR} (old : NOM N)
      (h : x ≥ φ.new_var) (pf : Proof φ) {k : NOM N}
      (hk : k ∈ (generalize_constants old h pf).proof_noms) :
      k ∈ pf.proof_noms ∨ k = old := by
    induction pf generalizing x with
    | @tautology φ ht =>
        unfold generalize_constants at hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (tautology ht) hkχ)
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (tautology ht) hkχ)
        · simp at hχ
    | @general ψ v pf ih =>
        unfold generalize_constants at hk
        have hφ := h
        simp only [nom_subst_svar, Form.new_var, max] at h ⊢
        by_cases hc : (v + 1).letter > (Form.new_var ψ).letter
        · simp [hc] at h
          simp only [gt_iff_lt, ge_iff_le] at hc
          have ih_h := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
          have hk' : k ∈ (generalize_constants old ih_h pf).proof_noms := by
            unfold generalize_constants at hk ⊢
            simp [hc, if_pos hc]
          exact ih ih_h hk'
        · simp [hc] at h
          have hxψ : x ≥ ψ.new_var := (new_var_geq2 hφ).2
          dsimp [proof_noms, formulasIn] at hk
          obtain ⟨χ, hχ, hkχ⟩ := hk
          rcases hχ with hχ | hχ
          · rw [hχ] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ pf hkχ)
          · have hmem := hχ
            simp only [hc, if_neg hc, List.mem_cons] at hmem
            rcases hmem with heq | hmem'
            · rw [heq] at hkχ
              exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ pf hkχ)
            · rcases ih hxψ (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                exact ⟨χ, hmem', hkχ⟩) with h | h
              exact Or.inl h
              exact Or.inr h
    | @necess ψ pf ih =>
        unfold generalize_constants at hk
        have hφ := h
        simp only [nom_subst_svar, occurs] at h ⊢
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ pf hkχ)
        · have hmem := hχ
          simp only [List.mem_cons] at hmem
          rcases hmem with heq | hmem'
          · rw [heq] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ pf hkχ)
          · rcases ih h (by
              simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
              exact ⟨χ, hmem', hkχ⟩) with h | h
            exact Or.inl h
            exact Or.inr h
    | @mp φ ψ pf1 pf2 ih1 ih2 =>
        unfold generalize_constants at hk
        have hφ := h
        let y := (φ ⟶ ψ).new_var
        have ⟨ih1_x, ih2_x⟩ := new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (mp pf1 pf2) hkχ)
        · have hmem := hχ
          simp only [List.mem_append, List.mem_cons] at hmem
          rcases hmem with heq | hmem'
          · rw [heq] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (mp pf1 pf2) hkχ)
          · rcases hmem' with hmem' | hmem'
            · rcases ih1 ih1_x (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                exact ⟨χ, hmem', hkχ⟩) with h | h
              exact Or.inl h
              exact Or.inr h
            · rcases ih2 ih2_x (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                exact ⟨χ, hmem', hkχ⟩) with h | h
              exact Or.inl h
              exact Or.inr h
    | ax_k =>
        unfold generalize_constants at hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h ax_k hkχ)
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h ax_k hkχ)
        · simp at hχ
    | @ax_q1 φ ψ v h2 =>
        unfold generalize_constants at hk
        simp only [nom_subst_svar] at h
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q1 φ ψ h2) hkχ)
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q1 φ ψ h2) hkχ)
        · simp at hχ
    | @ax_q2_svar φ y v h2 =>
        unfold generalize_constants at hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        have hmem := hχ
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem | hmem
        · rw [hmem] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q2_svar φ y v h2) hkχ)
        · rw [hmem] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q2_svar φ y v h2) hkχ)
        · simp at hmem
    | @ax_q2_nom φ v j =>
        unfold generalize_constants at hk
        simp [nom_subst_svar] at h
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        have hmem := hχ
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem | hmem
        · rw [hmem] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q2_nom φ v j) hkχ)
        · rw [hmem] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q2_nom φ v j) hkχ)
        · simp at hmem
    | ax_name _ =>
        unfold generalize_constants at hk
        dsimp [proof_noms, formulasIn, Form.list_noms, nom_subst_svar] at hk
        rcases hk with ⟨_, _, hkχ⟩
        exact False.elim hkχ
    | @ax_nom φ v m n =>
        unfold generalize_constants at hk
        simp only [nom_subst_svar, nec_subst_nom, pos_subst_nom] at h
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_nom m n) hkχ)
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_nom m n) hkχ)
        · simp at hχ
    | ax_brcn =>
        unfold generalize_constants at hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        rcases hχ with hχ | hχ | hχ
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h ax_brcn hkχ)
        · rw [hχ] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h ax_brcn hkχ)
        · simp at hχ

  private lemma mem_proof_noms_mp_ax_q2 {ψ : Form N} {x : SVAR} (new old : NOM N) (hx : x ≥ ψ.new_var)
      (pf' : Proof (all x, ψ[x // old])) (pf : Proof ψ)
      (hgc : pf' = generalize_constants old hx pf) {k : NOM N}
      (hk : k ∈ (Proof.mp (ax_q2_nom (ψ[x // old]) x new) pf').proof_noms) :
      k ∈ pf.proof_noms ∨ k = new := by
    dsimp [proof_noms, formulasIn] at hk
    simp only [List.mem_dedup, List.mem_flatMap] at hk
    obtain ⟨χ, hχ, hkχ⟩ := hk
    simp only [List.mem_append, List.mem_cons, List.mem_singleton] at hχ
    rcases hχ with hχ | hχ | hχ
    · have hkψ : k ∈ ψ[new // old].list_noms := by
        rw [← svar_svar_nom_subst (φ := ψ) hx]
        exact hχ ▸ hkχ
      rcases mem_of_list_noms_subst new old pf hkψ with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases mem_of_list_noms_q2_implication new old hx pf (hχ ▸ hkχ) with h | h
      · exact Or.inl h
      · exact Or.inr h
    · have hk' : k ∈ (generalize_constants old hx pf).proof_noms := by
        simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
        exact ⟨χ, hgc.symm ▸ hχ, hkχ⟩
      rcases mem_proof_noms_generalize_constants old hx pf hk' with h | hkold
      · exact Or.inl h
      · by_cases heq : new = old
        · exact Or.inr (Eq.trans hkold (Eq.symm heq))
        · have hkpf' : k ∈ pf'.proof_noms := by
            simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
            exact ⟨χ, hχ, hkχ⟩
          exact absurd (hgc ▸ (hkold ▸ hkpf'))
            (not_mem_proof_noms_generalize_constants new old hx heq pf)

  private lemma not_mem_proof_noms_mp_ax_q2 {ψ : Form N} {x : SVAR} (new old : NOM N) (hx : x ≥ ψ.new_var)
      (hne : new ≠ old) (pf' : Proof (all x, ψ[x // old])) (pf : Proof ψ)
      (hgc : pf' = generalize_constants old hx pf) :
      old ∉ (Proof.mp (ax_q2_nom (ψ[x // old]) x new) pf').proof_noms := by
    intro hk
    dsimp [proof_noms, formulasIn] at hk
    simp only [List.mem_dedup, List.mem_flatMap] at hk
    obtain ⟨χ, hχ, hkχ⟩ := hk
    simp only [List.mem_append, List.mem_cons, List.mem_singleton] at hχ
    rcases hχ with hχ | hχ | hχ
    · rw [hχ] at hkχ
      have h' : old ∈ ψ[new // old].list_noms := by rw [← svar_svar_nom_subst (φ := ψ) hx]; exact hkχ
      exact not_mem_old_of_list_noms_subst new old hne h' rfl
    · have hχ' := by simpa [formulasIn] using hχ
      rw [hχ'] at hkχ
      exact not_mem_old_of_list_noms_q2_implication new old hx hne hkχ
    · have hmem : old ∈ pf'.proof_noms := by
        simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
        exact ⟨χ, hχ, hkχ⟩
      rw [hgc] at hmem
      exact not_mem_proof_noms_generalize_constants new old hx hne pf hmem

  lemma mem_proof_noms_rename_constants_fwd {φ : Form N} (new old : NOM N) (pf : Proof φ)
      {k : NOM N} (hk : k ∈ (rename_constants_fwd new old pf).proof_noms) :
      k ∈ pf.proof_noms ∨ k = new := by
    have hx : φ.new_var ≥ φ.new_var := Nat.le.refl
    unfold rename_constants_fwd at hk
    simp_rw [proof_noms_cast (svar_svar_nom_subst hx (φ := φ))] at hk
    have hgc : generalize_constants old hx pf = generalize_constants old hx pf := rfl
    exact mem_proof_noms_mp_ax_q2 new old hx (generalize_constants old hx pf) pf hgc hk

  lemma not_mem_proof_noms_rename_constants_fwd {φ : Form N} (new old : NOM N) (pf : Proof φ)
      (hne : new ≠ old) : old ∉ (rename_constants_fwd new old pf).proof_noms := by
    have hx : φ.new_var ≥ φ.new_var := Nat.le.refl
    have hgc : generalize_constants old hx pf = generalize_constants old hx pf := rfl
    intro hk
    unfold rename_constants_fwd at hk
    simp_rw [proof_noms_cast (svar_svar_nom_subst hx (φ := φ))] at hk
    exact not_mem_proof_noms_mp_ax_q2 new old hx hne (generalize_constants old hx pf) pf hgc hk

  def rename_constants (j i : NOM N) (h : nom_occurs j φ = false) : ⊢ φ iff ⊢ (φ[j // i]) := by
    apply TypeIff.intro
    . exact rename_constants_fwd j i
    . intro pf
      let x := (φ[j//i]).new_var
      have x_geq : x ≥ (φ[j//i]).new_var := by simp; apply Nat.le_refl
      have l1 := generalize_constants j x_geq pf
      have : φ[j//i][x//j] = φ[x//i] := dbl_subst_nom i h
      rw [this] at l1
      have l2 := ax_q2_nom (φ[x // i]) x i
      have l3 := mp l2 l1
      rw [←eq_new_var] at x_geq
      have : φ[x//i][i//x] = φ[i//i] := svar_svar_nom_subst x_geq
      rw [nom_subst_self] at this
      rw [this] at l3
      exact l3

  def proof_sketch (h : nocc_bulk_property l₁ l₂ φ) : ⊢ φ iff ⊢ (φ.bulk_subst l₁ l₂) := by
    induction l₁ generalizing φ l₂ with
    | nil => cases l₂ <;> (simp [Form.bulk_subst]; apply TypeIff.refl)
    | cons h_new t_new ih =>
        cases l₂ with
        | nil => simp [Form.bulk_subst]; apply TypeIff.refl
        | cons h_old t_old =>
            simp [Form.bulk_subst]
            have : nom_occurs h_new φ = false := by
                apply @nocc_bulk TotalSet h_new [] []
                simp
                unfold nocc_bulk_property at h
                let n: Fin (List.length (h_new :: t_new)) := ⟨0, by simp⟩
                have : h_new = (h_new :: t_new)[n] := by get_elem_tactic
                have := @h n h_new this
                simp [show ((↑n : ℕ) = 0) from rfl] at this
                simp
                assumption
            have := rename_constants h_new h_old this
            apply this.trans
            apply ih
            apply nocc_bulk_property_induction
            assumption

  def pf_odd_noms : ⊢ φ iff ⊢ φ.odd_noms := by
    apply proof_sketch
    apply has_nocc_bulk_property

  def pf_odd_noms_set : Γ ⊢ φ iff Γ.odd_noms ⊢ φ.odd_noms := by
    simp [SyntacticConsequence]
    apply TypeIff.intro
    . intro ⟨L, h⟩
      have h := (odd_conj Γ L) ▸ odd_impl ▸ pf_odd_noms.mp h
      exists L.to_odd
    . intro ⟨L', h'⟩
      have h' := pf_odd_noms.mpr (odd_impl.symm ▸ (odd_conj_rev Γ L').symm ▸ h')
      exists L'.odd_to

  def odd_noms_set_cons (Γ : Set (Form TotalSet)) : consistent Γ ↔ consistent Γ.odd_noms := by
    unfold consistent
    have : Form.bttm = Form.bttm.odd_noms := by simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst]
    conv => rhs; rw [this]
    apply Iff.intro <;> (
      intro h1 h2
      apply h1
      first | apply pf_odd_noms_set.mp | apply pf_odd_noms_set.mpr
      assumption
    )

end Nominals

def ax_nom_instance {φ : Form N} (i : NOM N) (m n : ℕ) : ⊢ (iterate_pos m (i ⋀ φ) ⟶ iterate_nec n (i ⟶ φ)) := by
  let x := φ.new_var
  have x_geq : x ≥ φ.new_var := by exact Nat.le.refl
  have l1 := @ax_nom N (φ[x//i]) x m n
  have l2 := ax_q2_nom (iterate_pos m (x⋀(φ[x//i]))⟶iterate_nec n (x⟶(φ[x//i]))) x i
  have l3 := mp l2 l1
  clear l1 l2
  rw [subst_nom, pos_subst, nec_subst, nom_svar_rereplacement x_geq] at l3
  exact l3

def ax_q2_svar_instance : ⊢ ((all x, φ) ⟶ φ) := by
  have : φ.new_var ≥ φ.new_var := by exact Nat.le.refl
  apply hs
  apply mp
  . apply tautology
    apply iff_elim_l
  apply rename_bound
  apply new_var_is_new
  apply new_var_subst''
  assumption
  have ⟨l, r⟩ := (rereplacement φ x (φ.new_var) new_var_is_new (new_var_subst'' this))
  conv => rhs; rhs; rw [←r]
  apply ax_q2_svar
  assumption

def Γ_univ_elim (h : Γ ⊢ (all x, φ)) : Γ ⊢ φ := by
  exact Γ_mp (Γ_theorem ax_q2_svar_instance Γ) h

def rename_var (h1 : occurs y φ = false) (h2 : is_substable φ y x) : ⊢ φ iff ⊢ (φ[y // x]) := by
  apply TypeIff.intro
  . intro h
    apply mp
    apply ax_q2_svar_instance
    exact y
    apply mp
    . apply mp
      apply tautology
      apply iff_elim_l
      apply rename_bound
      repeat assumption
    . apply general
      assumption
  . intro h
    apply mp
    apply ax_q2_svar_instance
    exact x
    apply mp
    . apply mp
      apply tautology
      apply iff_elim_r
      apply rename_bound
      repeat assumption
    . apply general
      assumption

def ax_q2_contrap {i : NOM N} {x : SVAR} : ⊢ (φ[i//x] ⟶ ex x, φ) := by
  rw [Form.bind_dual]
  apply hs
  . apply tautology
    apply dni
  . apply mp
    apply tautology
    apply contrapositive
    apply ax_q2_nom

def ax_q2_svar_contrap {x y : SVAR} (h : is_substable φ y x) : ⊢ (φ[y//x] ⟶ ex x, φ) := by
  rw [Form.bind_dual]
  apply hs
  . apply tautology
    apply dni
  . apply mp
    apply tautology
    apply contrapositive
    apply ax_q2_svar
    simp [is_substable]
    exact h

def ax_nom_instance' (x : SVAR) (m n : ℕ) : ⊢ (iterate_pos m (x ⋀ φ) ⟶ iterate_nec n (x ⟶ φ)) := by
  apply mp
  apply ax_q2_svar_instance
  assumption
  apply ax_nom

-- Lemma 3.6.1
def b361 {φ : Form N} : ⊢ ((φ ⟶ ex x, ψ) ⟶ ex x, (φ ⟶ ψ)) := by
  apply mp
  . apply tautology
    apply contrapositive'
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.empty_union]
    let Γ : Set (Form N) := {∼(ex x, φ⟶ψ)}
    have l1 : Γ ⊢ (∼(ex x, φ⟶ψ)) := by apply Γ_premise; simp [Γ]
    rw [Form.bind_dual] at l1
    have l2 := Γ_theorem (tautology (@dne N (all x, ∼(φ⟶ψ)))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_theorem (@ax_q2_svar_instance x N (∼(φ⟶ψ))) Γ
    have l5 := Γ_mp l4 l3
    have l6 := Γ_theorem (tautology (taut_iff_mp (@imp_neg N φ ψ))) Γ
    have l7 := Γ_mp l6 l5
    have l8 := Γ_conj_elim_l l7
    have l9 := Γ_conj_elim_r l7
    have l10 : Γ ⊢ (∼(ex x, ψ)) := by
      rw [Form.bind_dual]
      apply Γ_mp; apply Γ_theorem; apply tautology; apply dni
      apply Γ_univ_intro'
      . simp [Γ, is_free, -implication_disjunction]
      . exact l9
    have l11 := Γ_conj_intro l8 l10
    have l12 := Γ_mp (Γ_theorem (tautology (taut_iff_mpr (@imp_neg N φ (ex x, ψ)))) Γ) l11
    exact l12

-- Lemma 3.6.2
def b362 {φ : Form N} (h : is_free x φ = false) : ⊢ ((φ ⋀ ex x, ψ) ⟶ ex x, (φ ⋀ ψ)) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply tautology
    apply contrapositive'
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.empty_union]
    let Γ : Set (Form N) :=  {∼∼(all x, ∼(φ⋀ψ))}
    have l1 : Γ ⊢ (all x, ∼(φ⋀ψ)) := by
      apply Γ_mp; apply Γ_theorem; apply tautology; apply dne
      apply Γ_premise; simp [Γ]
    have l2 := Γ_theorem (@ax_q2_svar_instance x N (∼(φ⋀ψ))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_mp (Γ_theorem (tautology (taut_iff_mpr (@neg_conj N φ ψ))) Γ) l3
    have l5 : Γ⊢ (all x, (φ⟶∼ψ)) := by
      apply Γ_univ_intro'
      simp [Γ, is_free, -implication_disjunction]
      exact l4
    have l6 := Deduction.mp (Γ_mp (Γ_theorem (ax_q1 φ (∼ψ) h) Γ) l5)
    have l7 := Deduction.mpr (Γ_mp (Γ_theorem (tautology (@dni N (all x, ∼ψ))) (Γ ∪ {φ})) l6)
    have l8 := Γ_mp (Γ_theorem (tautology (taut_iff_mp (@neg_conj N φ (∼(all x, ∼ψ))))) Γ) l7
    exact l8

def ex_conj_comm {φ : Form N} : ⊢ ((ex x, (φ ⋀ ψ)) ⟶ (ex x, (ψ ⋀ φ))) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply tautology
    apply contrapositive'
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.empty_union]
    let Γ : Set (Form N) := {∼∼(all x, ∼(ψ⋀φ))}
    have l1 : Γ ⊢ (∼∼(all x, ∼(ψ⋀φ))) := by apply Γ_premise; simp [Γ]
    have l2 := Γ_theorem (tautology (@dne N (all x, ∼(ψ⋀φ)))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_theorem (@ax_q2_svar_instance x N (∼(ψ⋀φ))) Γ
    have l5 := Γ_mp l4 l3
    have l6 := Γ_theorem (tautology (@conj_comm_t' N ψ φ)) Γ
    have l7 := Γ_mp l6 l5
    have l8 : Γ⊢(all x, ∼(φ⋀ψ)) := by
      apply Γ_univ_intro'
      simp [Γ, is_free, -implication_disjunction]
      exact l7
    have l9 := Γ_theorem (tautology (@dni N (all x, ∼(φ⋀ψ)))) Γ
    have l10 := Γ_mp l9 l8
    exact l10

def b362' {φ : Form N} (h : is_free x φ = false) : ⊢ (((ex x, ψ) ⋀ φ) ⟶ ex x, (ψ ⋀ φ)) := by
  have l1 := tautology (@conj_comm_t N (ex x, ψ) φ)
  have l2 := @b362 N x ψ φ h
  have l3 := hs l2 ex_conj_comm
  have l4 := hs l1 l3
  exact l4

-- Lemma 3.6.3
def b363  {φ : Form N} : ⊢ ((all x, (φ ⟶ ψ)) ⟶ ((all x, φ) ⟶ (all x, ψ))) := by
  let Γ : Set (Form N) := ∅ ∪ {all x, φ⟶ψ} ∪ {all x, φ}
  have l1 : Γ ⊢ (all x, (φ ⟶ ψ)) := by apply Γ_premise; simp [Γ]
  have l2 : Γ⊢(φ⟶ψ) := by
    apply Γ_mp
    apply Γ_theorem
    apply ax_q2_svar_instance
    exact x
    exact l1
  have l3 : Γ⊢(all x, φ) := by apply Γ_premise; simp [Γ]
  have l4 : Γ⊢φ := by
    apply Γ_mp
    apply Γ_theorem
    apply ax_q2_svar_instance
    exact x
    exact l3
  have l5 : ⊢((all x, φ⟶ψ)⟶((all x, φ) ⟶ ψ)) := by
    apply Γ_empty.mp; apply Deduction.mpr; apply Deduction.mpr
    apply Γ_mp
    repeat assumption
  have l6 := general x l5
  have : is_free x (all x, φ⟶ψ) = false := by simp [is_free]
  have l7 := @ax_q1 N (all x, φ⟶ψ) ((all x, φ)⟶ψ) x this
  have l8 := mp l7 l6
  have : is_free x (all x, φ) = false := by simp [is_free]
  have l9 := @ax_q1 N (all x, φ) ψ x this
  have l10 := hs l8 l9
  exact l10

def dn_nec : ⊢ (□ φ ⟷ □ ∼∼φ) := by
  rw [Form.iff]
  apply mp
  apply mp
  apply tautology
  apply conj_intro
  repeat (
    apply mp
    apply ax_k
    apply necess
    apply tautology
    first | apply dni | apply dne
  )

def dn_all : ⊢ ((all x, φ) ⟷ all x, ∼∼φ) := by
  rw [Form.iff]
  apply mp
  apply mp
  apply tautology
  apply conj_intro
  repeat (
    apply mp
    apply b363
    apply general
    apply tautology
    first | apply dni | apply dne
  )

def bind_dual : ⊢((all x, ψ)⟷∼(ex x, ∼ψ)) := by
    rw [Form.bind_dual]
    apply mp; apply mp
    apply tautology
    apply iff_intro
    . apply hs
      . apply mp
        apply tautology
        apply iff_elim_l
        apply dn_all
      . apply tautology
        apply dni
    . apply hs
      . apply tautology
        apply dne
      . apply mp
        apply tautology
        apply iff_elim_r
        apply dn_all

def nec_dual : ⊢((□ ψ)⟷∼(◇ ∼ψ)) := by
    rw [Form.diamond]
    apply mp; apply mp
    apply tautology
    apply iff_intro
    . apply hs
      . apply mp
        apply tautology
        apply iff_elim_l
        apply dn_nec
      . apply tautology
        apply dni
    . apply hs
      . apply tautology
        apply dne
      . apply mp
        apply tautology
        apply iff_elim_r
        apply dn_nec

/-- When `x` is not free in `ψ`, `∀x.ψ` and `ψ` are provably equivalent (Henkin / Q1). -/
def all_iff_notfree {x : SVAR} {ψ : Form N} (h : is_free x ψ = false) : ⊢ ((all x, ψ) ⟷ ψ) := by
  apply mp; apply mp
  apply tautology
  apply iff_intro
  · exact @ax_q2_svar_instance x N ψ
  · apply mp (ax_q1 (φ := ψ) (ψ := ψ) (by simp [is_free, h]))
    apply general x
    apply tautology imp_refl

/-- From `∼(□φ)` derive `◇∼φ` (contrapositive of `nec_dual` + double-negation). -/
def not_nec_to_diamond {φ : Form N} : ⊢ ((∼(□φ)) ⟶ (◇∼φ)) := by
  have h1 : ⊢ ((□φ) ⟷ ∼(◇ ∼φ)) := nec_dual
  have h2 : ⊢ ((∼(□φ)) ⟷ ∼∼(◇ ∼φ)) :=
    mp (mp (tautology iff_elim_l) (tautology iff_not)) h1
  have h3 : ⊢ ((∼(□φ)) ⟶ ∼∼(◇ ∼φ)) := mp (tautology iff_elim_l) h2
  exact hs h3 (tautology (@dne N (◇ ∼φ)))

def diw_impl (h : ⊢(φ ⟶ ψ)) : ⊢ (◇φ ⟶ ◇ψ) := by
  have l1 := mp (tautology contrapositive) h
  have l2 := necess l1
  have l3 := mp ax_k l2
  have l4 := mp (tautology contrapositive) l3
  exact l4

def ax_brcn_contrap {φ : Form N} : ⊢ ((◇ ex x, φ) ⟶ (ex x, ◇ φ)) := by
  simp only [Form.diamond, Form.bind_dual]
  apply mp
  . apply tautology
    apply contrapositive
  . apply Γ_empty.mp; apply Deduction.mpr
    simp only [Set.empty_union]
    let Γ : Set (Form N) := {all x, ∼∼(□∼φ)}
    have l1 : Γ ⊢ (all x, ∼∼(□∼φ)) := by apply Γ_premise; simp [Γ]
    have l2 := Γ_theorem (mp (tautology iff_elim_r) (@dn_all x N (□∼φ))) Γ
    have l3 := Γ_mp l2 l1
    have l4 := Γ_theorem (@ax_brcn N (∼φ) x) Γ
    have l5 := Γ_mp l4 l3
    have l6 := Γ_theorem (mp (tautology iff_elim_l) (@dn_nec N (all x, ∼φ))) Γ
    have l7 := Γ_mp l6 l5
    exact l7

section MCS

def MCS_pf (h : MCS Γ) : Γ ⊢ φ → φ ∈ Γ := by
  intro pf
  rw [←(@not_not (φ ∈ Γ))]
  intro habs
  have ⟨cons, pf_bot⟩ := h
  have ⟨pf_bot, _⟩ := not_forall.mp (pf_bot habs)
  clear h
  apply cons
  apply Γ_mp
  apply Deduction.mpr
  assumption
  assumption

def MCS_thm (h : MCS Γ) : ⊢ φ → φ ∈ Γ := by
  intro
  apply MCS_pf h
  apply Γ_theorem
  assumption

def MCS_mp (h : MCS Γ) (h1 : φ ⟶ ψ ∈ Γ) (h2 : φ ∈ Γ) : ψ ∈ Γ := by
  rw [←@not_not (ψ ∈ Γ)]
  intro habs
  have ⟨pf_bot, _⟩ := not_forall.mp (h.right habs)
  apply h.left
  apply Γ_mp
  apply Deduction.mpr
  assumption
  apply Γ_mp
  repeat (apply Γ_premise; assumption)

def MCS_conj {Γ : Set (Form N)} (hmcs : MCS Γ) (φ ψ : Form N) : (φ ∈ Γ ∧ ψ ∈ Γ) ↔ (φ ⋀ ψ) ∈ Γ := by
  apply Iff.intro
  . intro ⟨l, r⟩
    apply MCS_pf hmcs
    exact Γ_conj_intro (Γ_premise l) (Γ_premise r)
  . intro h
    apply And.intro <;> apply MCS_pf hmcs
    exact Γ_conj_elim_l (Γ_premise h)
    exact Γ_conj_elim_r (Γ_premise h)

def MCS_max {Γ : Set (Form N)} (hmcs : MCS Γ) : (φ ∉ Γ ↔ (∼φ) ∈ Γ) := by
  apply Iff.intro
  . intro h
    have ⟨pf_bot, _⟩ := not_forall.mp (hmcs.2 h)
    apply MCS_pf hmcs; apply Deduction.mpr
    exact pf_bot
  . intro h habs
    apply hmcs.1
    apply Γ_mp (Γ_premise h) (Γ_premise habs)

def MCS_impl {Γ : Set (Form N)} (hmcs : MCS Γ) : (φ ∈ Γ → ψ ∈ Γ) ↔ ((φ⟶ψ) ∈ Γ) := by
  apply Iff.intro
  . intro h
    by_cases hc : φ ∈ Γ
    . apply MCS_pf hmcs
      apply Deduction.mpr
      apply increasing_consequence
      exact Γ_premise (h hc)
      simp
    . simp only [MCS_max, hmcs, Form.neg] at hc
      apply MCS_pf hmcs; apply Deduction.mpr
      apply Γ_mp
      apply @Γ_theorem N (⊥ ⟶ ψ)
      apply tautology
      eval
      exact Deduction.mp (Γ_premise hc)
  . intro h1 h2
    apply MCS_pf hmcs
    exact Γ_mp (Γ_premise h1) (Γ_premise h2)

def MCS_iff {Γ : Set (Form N)} (hmcs : MCS Γ) : ((φ⟷ψ) ∈ Γ) ↔ (φ ∈ Γ ↔ ψ ∈ Γ) := by
  simp only [Form.iff, ←MCS_conj, ←MCS_impl, hmcs]
  apply Iff.intro
  <;> intros; apply Iff.intro
  . apply And.left
    assumption
  . apply And.right
    assumption
  apply And.intro <;> simp [*]

def MCS_rw {Γ : Set (Form N)} (hmcs : MCS Γ) (pf : ⊢ (φ ⟷ ψ)) : φ ∈ Γ ↔ ψ ∈ Γ := by
  rw [←MCS_iff hmcs]
  apply MCS_pf hmcs
  exact Γ_theorem pf Γ

def MCS_rich : ∀ {Θ : Set (Form N)}, (MCS Θ) → (witnessed Θ) → ∃ i : NOM N, ↑i ∈ Θ := by
  intro Θ mcs wit
  have := Proof.MCS_thm mcs (Proof.ax_name ⟨0⟩)
  have := wit this
  simp [subst_nom] at this
  exact this

def MCS_with_svar_witness : ∀ {Θ : Set (Form N)} {x y : SVAR} (_ : is_substable φ y x), (MCS Θ) → φ[y//x] ∈ Θ → (ex x, φ) ∈ Θ := by
  intro Θ x y h1 mcs h2
  apply MCS_mp mcs
  apply MCS_thm mcs
  apply ax_q2_svar_contrap h1
  repeat assumption

end MCS

def iff_subst : ⊢ ((φ ⟷ ψ) ⟶ (ψ ⟷ χ) ⟶ (φ ⟷ χ)) := by
  exact tautology iff_rw

def pf_iff_subst : ⊢ (φ ⟷ ψ) → ⊢ (ψ ⟷ χ) → ⊢ (φ ⟷ χ) := by
  intro h1 h2
  apply mp
  apply mp
  apply iff_subst
  exact ψ
  repeat assumption

end
