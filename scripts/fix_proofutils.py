#!/usr/bin/env python3
"""Apply conservativity nominal lemma fixes to ProofUtils.lean (stash base)."""
from pathlib import Path

p = Path(__file__).resolve().parent.parent / "Hybrid/ProofUtils.lean"
text = p.read_text()

# 1. generalize_constants_thm
if "generalize_constants_thm" not in text:
    text = text.replace(
        """def generalize_constants {φ : Form N} {x : SVAR} (i : NOM N) (h : x ≥ φ.new_var) (pf : Proof φ) :
    Proof (all x, φ[x // i]) :=
  general x (generalize_constants_body i h pf)

  def generalize_constants_rev""",
        """def generalize_constants {φ : Form N} {x : SVAR} (i : NOM N) (h : x ≥ φ.new_var) (pf : Proof φ) :
    Proof (all x, φ[x // i]) :=
  general x (generalize_constants_body i h pf)

def generalize_constants_thm {φ : Form N} {x : SVAR} (i : NOM N) (h : x ≥ φ.new_var)
    (pf : Proof φ) : Proof (all x, φ[x // i]) :=
  generalize_constants i h pf

  def generalize_constants_rev""",
    )

text = text.replace(
    "    . apply generalize_constants; assumption",
    "    . intro pf; exact generalize_constants_thm i h pf",
)

text = text.replace(
    "      have l1 := generalize_constants j x_geq pf",
    "      have l1 := generalize_constants_thm j x_geq pf",
)

# 2. gc_body_mp_formulasIn + mp helpers
if "gc_body_mp_formulasIn" not in text:
    insert = '''
  private lemma gc_body_mp_formulasIn {φ ψ : Form N} {x : SVAR} (old : NOM N)
      (h : x ≥ ψ.new_var) (pf1 : Proof (φ ⟶ ψ)) (pf2 : Proof φ) :
      (generalize_constants_body old h (mp pf1 pf2)).formulasIn =
        ψ[x // old] ::
          (ax_q2_svar (ψ[(φ ⟶ ψ).new_var // old]) (φ ⟶ ψ).new_var x (new_var_subst h)).formulasIn ++
          (general (φ ⟶ ψ).new_var
            (mp (generalize_constants_body old (Nat.le.refl : (φ ⟶ ψ).new_var ≥ (φ ⟶ ψ).new_var) pf1)
              (generalize_constants_body old (new_var_geq1 (Nat.le.refl : (φ ⟶ ψ).new_var ≥ (φ ⟶ ψ).new_var)).1 pf2))).formulasIn := by
    sorry

'''
    text = text.replace(
        "  private lemma gc_formulasIn {φ : Form N}",
        insert + "  private lemma gc_formulasIn {φ : Form N}",
    )

if "mem_proof_noms_of_mem_proof_noms_mp_left" not in text:
    helpers = '''
  private lemma mem_proof_noms_of_mem_proof_noms_mp_left {φ ψ : Form N} (pf1 : Proof (φ ⟶ ψ)) (pf2 : Proof φ) {k : NOM N}
      (hk : k ∈ pf1.proof_noms) : k ∈ (mp pf1 pf2).proof_noms := by
    have hk' := hk
    simp only [proof_noms, List.mem_dedup, List.mem_flatMap] at hk'
    obtain ⟨χ, hχ, hkχ⟩ := hk'
    simp only [proof_noms, List.mem_dedup, List.mem_flatMap, Proof.formulasIn]
    exact ⟨χ, List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hχ))), hkχ⟩

  private lemma mem_proof_noms_of_mem_proof_noms_mp_right {φ ψ : Form N} (pf1 : Proof (φ ⟶ ψ)) (pf2 : Proof φ) {k : NOM N}
      (hk : k ∈ pf2.proof_noms) : k ∈ (mp pf1 pf2).proof_noms := by
    have hk' := hk
    simp only [proof_noms, List.mem_dedup, List.mem_flatMap] at hk'
    obtain ⟨χ, hχ, hkχ⟩ := hk'
    simp only [proof_noms, List.mem_dedup, List.mem_flatMap, Proof.formulasIn]
    exact ⟨χ, List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr hχ))), hkχ⟩

'''
    text = text.replace(
        "  private lemma not_mem_old_head_all",
        helpers + "  private lemma not_mem_old_head_all",
    )

# 3. not_mem mp case
not_mem_mp_old = """        | inr hmem =>
          simp only [generalize_constants_body, Proof.formulasIn, Proof.mp, Proof.general,
            formulasIn_cast, nom_subst_trans, List.mem_append, List.mem_cons] at hmem
          rcases hmem with heq | hmem'
          · exact (list_noms_nom_subst_svar hφ (heq ▸ hkχ)).2 rfl
          · rcases List.mem_append.mp hmem' with hmem1 | hmem2
            · exact absurd (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                exact ⟨χ, hmem1, hkχ⟩) (ih1 ih1_x)
            · exact absurd (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                exact ⟨χ, hmem2, hkχ⟩) (ih2 ih2_x)"""

not_mem_mp_new = """        | inr hmem =>
          rw [gc_body_mp_formulasIn old hφ pf1 pf2] at hmem
          rcases List.mem_cons.mp hmem with heq | hmem'
          · exact (list_noms_nom_subst_svar hφ (heq ▸ hkχ)).2 rfl
          · rcases List.mem_append.mp hmem' with hmem_ax | hmem_gen
            · rcases List.mem_singleton.mp hmem_ax with rfl
              simp [Form.list_noms, List.mem_merge, List.mem_dedup] at hkχ
              rcases hkχ with hkχ | hkχ
              · exact (list_noms_nom_subst_svar hφ hkχ).2 rfl
              · rcases list_noms_subst (φ := ψ) (old := old) (new := old) hkχ with ⟨_, hne'⟩ | heq'
                · exact hne' rfl
                · exact hne heq'.symm
            · rcases List.mem_cons.mp hmem_gen with heq_all | hmem_tail
              · rw [heq_all, Form.list_noms] at hkχ
                cases hkχ
              · rcases List.mem_cons.mp hmem_tail with heq_phi | hmem_append
                · exact (list_noms_nom_subst_svar ((new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)).2) (heq_phi ▸ hkχ)).2 rfl
                · rcases List.mem_append.mp hmem_append with hmem_pf1 | hmem_pf2
                  · exact absurd (by
                      simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                      exact ⟨χ, mem_formulasIn_gc_body old pf1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var) hmem_pf1, hkχ⟩) (ih1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var))
                  · exact absurd (by
                      simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                      exact ⟨χ, mem_formulasIn_gc_body old pf2 ih1_x hmem_pf2, hkχ⟩) (ih2 ih1_x)"""

if not_mem_mp_old in text:
    text = text.replace(not_mem_mp_old, not_mem_mp_new)

# 4. not_mem ax_q2_svar
text = text.replace(
    """        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          conv at h1 => rw [formulasIn_cast]
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · exact (list_noms_nom_subst_svar h (heq2 ▸ hkχ)).2 rfl
          · nomatch hfalse
    | @ax_q2_nom φ v j =>""",
    """        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          have heq2 : χ = _ := by simpa [formulasIn_cast, List.mem_singleton] using h1
          exact (list_noms_nom_subst_svar h (heq2 ▸ hkχ)).2 rfl
    | @ax_q2_nom φ v j =>""",
)

# 5. not_mem ax_q2_nom
text = text.replace(
    """        | inr h1 =>
          dsimp [generalize_constants_body] at h1
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · exact (list_noms_nom_subst_svar h (heq2 ▸ hkχ)).2 rfl
          · nomatch hfalse
    | ax_name _ =>""",
    """        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          split at h1
          · have heq2 : χ = _ := by simpa [formulasIn_cast, List.mem_singleton] using h1
            exact (list_noms_nom_subst_svar h (heq2 ▸ hkχ)).2 rfl
          · have heq2 : χ = _ := by simpa [formulasIn_cast, List.mem_singleton] using h1
            exact (list_noms_nom_subst_svar h (heq2 ▸ hkχ)).2 rfl
    | ax_name _ =>""",
    1,
)

# 6. not_mem ax_name
text = text.replace(
    """    | ax_name _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn, Form.list_noms, nom_subst_svar] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨_, _, hkχ⟩ := hk
        exact (list_noms_nom_subst_svar h hkχ).2 rfl""",
    """    | ax_name _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq1 =>
          rw [heq1, Form.list_noms] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        | inr h1 =>
          dsimp [generalize_constants_body] at h1
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · rw [heq2, Form.list_noms] at hkχ
            exact (list_noms_nom_subst_svar h hkχ).2 rfl
          · nomatch hfalse""",
)

# 7. not_mem ax_nom
text = text.replace(
    """        | inr h1 =>
          dsimp [generalize_constants_body] at h1
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · rw [heq2] at hkχ
            exact (list_noms_nom_subst_svar h hkχ).2 rfl
          · nomatch hfalse
    | ax_brcn =>""",
    """        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          have heq2 : χ = _ := by simpa [formulasIn_cast, List.mem_singleton] using h1
          rw [heq2] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
    | ax_brcn =>""",
    1,
)

# 8. mem general neg
text = text.replace(
    """          | inr htail =>
            have hmem := htail
            simp only [hc, if_neg hc, generalize_constants, generalize_constants_body, Proof.formulasIn, Proof.general, List.mem_cons] at hmem
            rcases List.mem_cons.mp hmem with heq | hmem''
            · rw [heq] at hkχ
              exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (general v pf) hkχ)
            · rcases ih hxψ (mem_proof_noms_gc_witness old pf hxψ hmem'' hkχ) with h | h""",
    """          | inr htail =>
            rw [gc_body_general_neg old pf hφ hxψ (by simpa using hc)] at htail
            dsimp [Proof.formulasIn, Proof.general] at htail
            rcases List.mem_cons.mp htail with heq | hmem''
            · exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (general v pf) (heq ▸ hkχ))
            · rcases ih hxψ (mem_proof_noms_gc_witness old pf hxψ hmem'' hkχ) with h | h""",
)

# 9. mem necess
text = text.replace(
    """    | @necess ψ pf ih =>
        unfold generalize_constants at hk
        have hφ := h
        simp only [nom_subst_svar, occurs] at h ⊢
        dsimp [proof_noms, formulasIn] at hk""",
    """    | @necess ψ pf ih =>
        unfold generalize_constants at hk
        have hφ := h
        have ih_h : x ≥ ψ.new_var := by simp [Form.new_var] at h; exact h
        dsimp [proof_noms, formulasIn] at hk""",
)

text = text.replace(
    """        | inl heq =>
          rw [heq] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ pf hkχ)
        | inr htail =>
          have hmem := htail
          simp only [generalize_constants, generalize_constants_body, Proof.formulasIn, Proof.necess,
            Proof.general, List.mem_cons, id, ↓reduceIte] at hmem
          rcases List.mem_cons.mp hmem with heq | hmem'
          · rw [heq] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ pf hkχ)
          · rcases List.mem_cons.mp hmem' with heq | hmem''
            · rw [heq] at hkχ
              exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ pf hkχ)
            · rcases ih h (mem_proof_noms_gc_witness old pf h hmem'' hkχ) with h | h
              · exact Or.inl (mem_proof_noms_of_mem_proof_noms_necess pf h)
              · exact Or.inr h
    | @mp φ ψ pf1 pf2 ih1 ih2 =>""",
    """        | inl heq =>
          rw [heq] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (necess pf) hkχ)
        | inr htail =>
          rw [gc_body_necess old pf hφ ih_h] at htail
          dsimp [Proof.formulasIn, Proof.necess] at htail
          rcases List.mem_cons.mp htail with heq | hmem'
          · rw [heq] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (necess pf) hkχ)
          · rcases ih ih_h (mem_proof_noms_gc_witness old pf ih_h hmem' hkχ) with h | h
            · exact Or.inl (mem_proof_noms_of_mem_proof_noms_necess pf h)
            · exact Or.inr h
    | @mp φ ψ pf1 pf2 ih1 ih2 =>""",
)

# 10. mem mp
mem_mp_old = """        | inr htail =>
          have hmem := htail
          simp only [generalize_constants_body, Proof.formulasIn, Proof.mp, Proof.general,
            formulasIn_cast, nom_subst_trans, List.mem_append, List.mem_cons] at hmem
          rcases hmem with heq | hmem'
          · rw [heq] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (mp pf1 pf2) hkχ)
          · rcases List.mem_append.mp hmem' with hmem1 | hmem2
            · rcases ih1 ih1_x (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                exact ⟨χ, hmem1, hkχ⟩) with h | h
              · exact Or.inl h
              · exact Or.inr h
            · rcases ih2 ih2_x (by
                simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                exact ⟨χ, hmem2, hkχ⟩) with h | h
              · exact Or.inl h
              · exact Or.inr h"""

mem_mp_new = """        | inr htail =>
          rw [gc_body_mp_formulasIn old hφ pf1 pf2] at htail
          rcases List.mem_cons.mp htail with heq | hmem'
          · rw [heq] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (mp pf1 pf2) hkχ)
          · rcases List.mem_append.mp hmem' with hmem_ax | hmem_gen
            · rcases List.mem_singleton.mp hmem_ax with rfl
              simp [Form.list_noms, List.mem_merge, List.mem_dedup] at hkχ
              rcases hkχ with hkχ | hkχ
              · exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (mp pf1 pf2) hkχ)
              · rcases list_noms_subst (φ := ψ) (old := old) (new := old) hkχ with h | h
                · exact Or.inl h.left
                · exact Or.inr h
            · rcases List.mem_cons.mp hmem_gen with heq_all | hmem_tail
              · rw [heq_all, Form.list_noms] at hkχ
                exact False.elim hkχ
              · rcases List.mem_cons.mp hmem_tail with heq_phi | hmem_append
                · rw [heq_phi] at hkχ
                  exact Or.inl (mem_proof_noms_of_subst_list_noms old ((new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)).2) (mp pf1 pf2) hkχ)
                · rcases List.mem_append.mp hmem_append with hmem_pf1 | hmem_pf2
                  · rcases ih1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)
                      (mem_proof_noms_gc_witness old pf1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var) hmem_pf1 hkχ) with h | h
                    · exact Or.inl (mem_proof_noms_of_mem_proof_noms_mp_left pf1 pf2 h)
                    · exact Or.inr h
                  · rcases ih2 ih1_x (mem_proof_noms_gc_witness old pf2 ih1_x hmem_pf2 hkχ) with h | h
                    · exact Or.inl (mem_proof_noms_of_mem_proof_noms_mp_right pf1 pf2 h)
                    · exact Or.inr h"""

if mem_mp_old in text:
    text = text.replace(mem_mp_old, mem_mp_new)

# 11. mem ax_q2_svar / ax_q2_nom / ax_name / ax_nom (in mem theorem)
text = text.replace(
    """        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          conv at h1 => rw [formulasIn_cast]
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · rw [heq2] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q2_svar φ y v h2) hkχ)
          · nomatch hfalse
    | @ax_q2_nom φ v j =>""",
    """        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          have heq2 : χ = _ := by simpa [formulasIn_cast, List.mem_singleton] using h1
          rw [heq2] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q2_svar φ y v h2) hkχ)
    | @ax_q2_nom φ v j =>""",
)

text = text.replace(
    """        | inr h1 =>
          dsimp [generalize_constants_body] at h1
          split at h1
          · conv at h1 => rw [formulasIn_cast]
            rcases List.mem_cons.mp h1 with heq2 | hfalse
            · rw [heq2] at hkχ
              exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q2_nom φ v j) hkχ)
            · nomatch hfalse
          · conv at h1 => rw [formulasIn_cast]
            rcases List.mem_cons.mp h1 with heq2 | hfalse
            · rw [heq2] at hkχ
              exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q2_nom φ v j) hkχ)
            · nomatch hfalse
    | ax_name _ =>""",
    """        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          split at h1
          · have heq2 : χ = _ := by simpa [formulasIn_cast, List.mem_singleton] using h1
            rw [heq2] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q2_nom φ v j) hkχ)
          · have heq2 : χ = _ := by simpa [formulasIn_cast, List.mem_singleton] using h1
            rw [heq2] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_q2_nom φ v j) hkχ)
    | ax_name _ =>""",
)

text = text.replace(
    """    | ax_name _ =>
        unfold generalize_constants at hk
        dsimp [proof_noms, formulasIn, Form.list_noms, nom_subst_svar, generalize_constants_body,
          Proof.general, Proof.formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq =>
          rw [heq] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_name _) hkχ)
        | inr h1 =>
          have heq2 : χ = _ := by simpa [List.mem_singleton] using h1
          rw [heq2, Form.list_noms] at hkχ
          exact hkχ.elim
    | @ax_nom φ v m n =>""",
    """    | ax_name _ =>
        unfold generalize_constants at hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq =>
          rw [heq, Form.list_noms] at hkχ
          exact False.elim hkχ
        | inr h1 =>
          dsimp [generalize_constants_body] at h1
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · rw [heq2, Form.list_noms] at hkχ
            exact False.elim hkχ
          · nomatch hfalse
    | @ax_nom φ v m n =>""",
)

text = text.replace(
    """          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_nom φ v m n) hkχ)
        | inr h1 =>
          dsimp [generalize_constants_body] at h1
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · rw [heq2] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_nom φ v m n) hkχ)
          · nomatch hfalse
    | ax_brcn =>""",
    """          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_nom m n) hkχ)
        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          have heq2 : χ = _ := by simpa [formulasIn_cast, List.mem_singleton] using h1
          rw [heq2] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_nom m n) hkχ)
    | ax_brcn =>""",
)

p.write_text(text)
print("Patched", p)
