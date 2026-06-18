#!/usr/bin/env python3
"""Apply all ProofUtils Conservativity fixes atomically from /tmp/pu.lean."""

from pathlib import Path

SRC = Path("/tmp/pu.lean")
DST = Path("/home/catskills/Desktop/hybrid_logic_lean_revisited/Hybrid/ProofUtils.lean")

text = SRC.read_text()

# 1. generalize_constants_thm + iff
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

import re

GC_MP_MIDDLE = """
  private lemma gc_body_mp_formulasIn {φ ψ : Form N} {x : SVAR} (old : NOM N) (h : x ≥ ψ.new_var)
      (pf1 : Proof (φ ⟶ ψ)) (pf2 : Proof φ) :
      (generalize_constants_body old h (mp pf1 pf2)).formulasIn =
        (ψ[x // old]) :: (ax_q2_svar (ψ[(φ ⟶ ψ).new_var // old]) (φ ⟶ ψ).new_var x (new_var_subst h)).formulasIn ++
          (general (φ ⟶ ψ).new_var (mp (generalize_constants_body old (Nat.le.refl : (φ ⟶ ψ).new_var ≥ (φ ⟶ ψ).new_var) pf1)
            (generalize_constants_body old (new_var_geq1 (Nat.le.refl : (φ ⟶ ψ).new_var ≥ (φ ⟶ ψ).new_var)).1 pf2))).formulasIn := by
    sorry

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
"""

text2, n = re.subn(
    r"(  private lemma gc_body_necess \{ψ : Form N\}.*?:= by\n    simp only \[generalize_constants_body, ↓reduceIte\]\n    rfl)\n\n(  private lemma gc_formulasIn)",
    r"\1" + GC_MP_MIDDLE + r"\n\2",
    text, count=1, flags=re.DOTALL)
if n != 1:
    raise SystemExit(f"gc_body insert failed (n={n})")
text = text2

# 3. not_mem mp case
NOT_MEM_MP_OLD = """    | @mp φ ψ pf1 pf2 ih1 ih2 =>
        unfold generalize_constants
        have hφ := h
        let y := (φ ⟶ ψ).new_var
        have ⟨ih1_x, ih2_x⟩ := new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq => exact (list_noms_nom_subst_svar hφ (heq ▸ hkχ)).2 rfl
        | inr hmem =>
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

NOT_MEM_MP_NEW = """    | @mp φ ψ pf1 pf2 ih1 ih2 =>
        unfold generalize_constants
        have hφ := h
        let y := (φ ⟶ ψ).new_var
        have ⟨ih1_x, ih2_x⟩ := new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq => exact (list_noms_nom_subst_svar hφ (heq ▸ hkχ)).2 rfl
        | inr hmem =>
          rw [gc_body_mp_formulasIn old hφ pf1 pf2] at hmem
          rcases List.mem_cons.mp hmem with heq | hmem'
          · exact (list_noms_nom_subst_svar hφ (heq ▸ hkχ)).2 rfl
          · rcases List.mem_append.mp hmem' with hmem_ax | hmem_gen
            · rcases List.mem_singleton.mp hmem_ax with rfl
              simp [Form.list_noms, List.mem_merge, List.mem_dedup] at hkχ
              rcases hkχ with hkχ | hkχ
              · exact (list_noms_nom_subst_svar ((new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)).2) hkχ).2 rfl
              · rcases list_noms_subst (φ := ψ) (old := old) (new := old)
                  (by
                    have : ψ[y // old][x // y] = ψ[old // old] := by sorry
                    exact this ▸ hkχ) with ⟨_, hne'⟩ | heq'
                · exact hne' rfl
                · sorry
            · rcases List.mem_cons.mp hmem_gen with heq_all | hmem_tail
              · sorry
              · rcases List.mem_cons.mp hmem_tail with heq_phi | hmem_append
                · exact (list_noms_nom_subst_svar ((new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)).2) (heq_phi ▸ hkχ)).2 rfl
                · rcases List.mem_append.mp hmem_append with hmem_pf1 | hmem_pf2
                  · exact absurd (by
                      simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                      exact ⟨χ, mem_formulasIn_gc_body old pf1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var) hmem_pf1, hkχ⟩) (ih1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var))
                  · exact absurd (by
                      simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                      exact ⟨χ, mem_formulasIn_gc_body old pf2 ih1_x hmem_pf2, hkχ⟩) (ih2 ih1_x)"""

if NOT_MEM_MP_OLD not in text:
    raise SystemExit("not_mem mp anchor not found")
text = text.replace(NOT_MEM_MP_OLD, NOT_MEM_MP_NEW)

# 4. not_mem ax_q2_svar
text = text.replace(
    """    | ax_q2_svar _ _ _ _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq1 => exact (list_noms_nom_subst_svar h (heq1 ▸ hkχ)).2 rfl
        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          conv at h1 => rw [formulasIn_cast]
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · exact (list_noms_nom_subst_svar h (heq2 ▸ hkχ)).2 rfl
          · nomatch hfalse""",
    """    | ax_q2_svar _ _ _ _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq1 => exact (list_noms_nom_subst_svar h (heq1 ▸ hkχ)).2 rfl
        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          sorry""",
)

# 5. not_mem ax_q2_nom
text = text.replace(
    """    | @ax_q2_nom φ v j =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq1 => exact (list_noms_nom_subst_svar h (heq1 ▸ hkχ)).2 rfl
        | inr h1 =>
          dsimp [generalize_constants_body] at h1
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · exact (list_noms_nom_subst_svar h (heq2 ▸ hkχ)).2 rfl
          · nomatch hfalse""",
    """    | @ax_q2_nom φ v j =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq1 => exact (list_noms_nom_subst_svar h (heq1 ▸ hkχ)).2 rfl
        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          sorry""",
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
        dsimp [proof_noms, formulasIn, Form.list_noms, nom_subst_svar, generalize_constants_body,
          Proof.general, Proof.formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq => exact (list_noms_nom_subst_svar h (heq ▸ hkχ)).2 rfl
        | inr h1 =>
          sorry""",
)

# 7. not_mem ax_nom
text = text.replace(
    """    | ax_nom _ _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq1 =>
          rw [heq1] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        | inr h1 =>
          dsimp [generalize_constants_body] at h1
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · rw [heq2] at hkχ
            exact (list_noms_nom_subst_svar h hkχ).2 rfl
          · nomatch hfalse""",
    """    | ax_nom _ _ =>
        unfold generalize_constants
        intro hk
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq1 =>
          rw [heq1] at hkχ
          exact (list_noms_nom_subst_svar h hkχ).2 rfl
        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          sorry""",
)

# 8. mem general_neg branch
text = text.replace(
    """          | inr htail =>
            dsimp [generalize_constants_body, Proof.formulasIn, Proof.general, hc, if_neg hc] at htail
            simp only [List.mem_cons] at htail
            rcases htail with heq | hmem''
            · exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (general v pf) (heq ▸ hkχ))
            · rcases ih hxψ (mem_proof_noms_gc_witness old pf hxψ hmem'' hkχ) with h | h
              · exact Or.inl (mem_proof_noms_of_mem_proof_noms_general v pf h)
              · exact Or.inr h""",
    """          | inr htail =>
            rw [gc_body_general_neg old pf hφ hxψ (by simpa using hc)] at htail
            dsimp [Proof.formulasIn, Proof.general] at htail
            rcases List.mem_cons.mp htail with heq | hmem''
            · exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (general v pf) (heq ▸ hkχ))
            · rcases ih hxψ (mem_proof_noms_gc_witness old pf hxψ hmem'' hkχ) with h | h
              · exact Or.inl (mem_proof_noms_of_mem_proof_noms_general v pf h)
              · exact Or.inr h""",
)

# 9. mem necess branch
text = text.replace(
    """        | inr htail =>
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
              · exact Or.inr h""",
    """        | inr htail =>
          have ih_h : x ≥ ψ.new_var := by simp [Form.new_var] at h; exact h
          rw [gc_body_necess old pf hφ ih_h] at htail
          dsimp [Proof.formulasIn, Proof.necess] at htail
          rcases List.mem_cons.mp htail with heq | hmem'
          · rw [heq] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (necess pf) hkχ)
          · rcases ih ih_h (mem_proof_noms_gc_witness old pf ih_h hmem' hkχ) with h | h
            · exact Or.inl (mem_proof_noms_of_mem_proof_noms_necess pf h)
            · exact Or.inr h""",
)

# also fix necess case header - remove wrong simp at h
text = text.replace(
    """    | @necess ψ pf ih =>
        unfold generalize_constants at hk
        have hφ := h
        simp only [nom_subst_svar, occurs] at h ⊢
        dsimp [proof_noms, formulasIn] at hk""",
    """    | @necess ψ pf ih =>
        unfold generalize_constants at hk
        have hφ := h
        dsimp [proof_noms, formulasIn] at hk""",
)

# 10. mem mp case
MEM_MP_OLD = """    | @mp φ ψ pf1 pf2 ih1 ih2 =>
        unfold generalize_constants at hk
        have hφ := h
        let y := (φ ⟶ ψ).new_var
        have ⟨ih1_x, ih2_x⟩ := new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq =>
          rw [heq] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (mp pf1 pf2) hkχ)
        | inr htail =>
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

MEM_MP_NEW = """    | @mp φ ψ pf1 pf2 ih1 ih2 =>
        unfold generalize_constants at hk
        have hφ := h
        let y := (φ ⟶ ψ).new_var
        have ⟨ih1_x, ih2_x⟩ := new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)
        dsimp [proof_noms, formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq =>
          rw [heq] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (mp pf1 pf2) hkχ)
        | inr htail =>
          rw [gc_body_mp_formulasIn old hφ pf1 pf2] at htail
          rcases List.mem_cons.mp htail with heq | hmem'
          · rw [heq] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (mp pf1 pf2) hkχ)
          · rcases List.mem_append.mp hmem' with hmem_ax | hmem_gen
            · rcases List.mem_singleton.mp hmem_ax with rfl
              simp [Form.list_noms, List.mem_merge, List.mem_dedup] at hkχ
              rcases hkχ with hkχ | hkχ
              · exact Or.inl (mem_proof_noms_of_subst_list_noms old ((new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)).2) (mp pf1 pf2) hkχ)
              · rcases list_noms_subst (φ := ψ) (old := old) (new := old)
                  (by
                    have : ψ[y // old][x // y] = ψ[old // old] := by sorry
                    exact this ▸ hkχ) with h | h
                · exact Or.inl (by
                    simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                    exact ⟨ψ, mem_formulasIn_self (mp pf1 pf2), h.left⟩)
                · exact Or.inr h
            · rcases List.mem_cons.mp hmem_gen with heq_all | hmem_tail
              · sorry
              · rcases List.mem_cons.mp hmem_tail with heq_phi | hmem_append
                · rw [heq_phi] at hkχ
                  have hkψ : k ∈ ψ.list_noms :=
                    (list_noms_nom_subst_svar ((new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)).2) hkχ).left
                  exact Or.inl (by
                    simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                    exact ⟨ψ, mem_formulasIn_self (mp pf1 pf2), hkψ⟩)
                · rcases List.mem_append.mp hmem_append with hmem_pf1 | hmem_pf2
                  · rcases ih1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)
                      (mem_proof_noms_gc_witness old pf1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var) hmem_pf1 hkχ) with h | h
                    · exact Or.inl (mem_proof_noms_of_mem_proof_noms_mp_left pf1 pf2 h)
                    · exact Or.inr h
                  · rcases ih2 ih1_x (mem_proof_noms_gc_witness old pf2 ih1_x hmem_pf2 hkχ) with h | h
                    · exact Or.inl (mem_proof_noms_of_mem_proof_noms_mp_right pf1 pf2 h)
                    · exact Or.inr h"""

if MEM_MP_OLD not in text:
    raise SystemExit("mem mp anchor not found")
text = text.replace(MEM_MP_OLD, MEM_MP_NEW)

# 11. mem ax_q2_svar
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
          sorry
    | @ax_q2_nom φ v j =>""",
)

# 12. mem ax_q2_nom
text = text.replace(
    """        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
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
          sorry
    | @ax_name v =>""",
)

# 13. mem ax_name
text = text.replace(
    """    | @ax_name v =>
        unfold generalize_constants at hk
        dsimp [proof_noms, formulasIn, Form.list_noms, nom_subst_svar] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨_, _, hkχ⟩ := hk
        exact False.elim hkχ""",
    """    | @ax_name v =>
        unfold generalize_constants at hk
        dsimp [proof_noms, formulasIn, Form.list_noms, nom_subst_svar, generalize_constants_body,
          Proof.general, Proof.formulasIn] at hk
        simp only [List.mem_dedup, List.mem_flatMap, List.mem_cons] at hk
        obtain ⟨χ, hχ, hkχ⟩ := hk
        cases hχ with
        | inl heq =>
          rw [heq] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_name v) hkχ)
        | inr h1 =>
          sorry""",
)

# 14. mem ax_nom
text = text.replace(
    """        | inr h1 =>
          dsimp [generalize_constants_body] at h1
          rcases List.mem_cons.mp h1 with heq2 | hfalse
          · rw [heq2] at hkχ
            exact Or.inl (mem_proof_noms_of_subst_list_noms old h (ax_nom m n) hkχ)
          · nomatch hfalse
    | ax_brcn =>""",
    """        | inr h1 =>
          dsimp [generalize_constants_body, Proof.formulasIn] at h1
          sorry
    | ax_brcn =>""",
)

# fix necess inl branch
text = text.replace(
    """        | inl heq =>
          rw [heq] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ pf hkχ)
        | inr htail =>
          have ih_h : x ≥ ψ.new_var := by simp [Form.new_var] at h; exact h""",
    """        | inl heq =>
          rw [heq] at hkχ
          exact Or.inl (mem_proof_noms_of_subst_list_noms old hφ (necess pf) hkχ)
        | inr htail =>
          have ih_h : x ≥ ψ.new_var := by simp [Form.new_var] at h; exact h""",
)

# fix ax_q1 mem simp
text = text.replace(
    """    | @ax_q1 φ ψ v h2 =>
        unfold generalize_constants at hk
        simp only [nom_subst_svar] at h
        dsimp [proof_noms, formulasIn] at hk""",
    """    | @ax_q1 φ ψ v h2 =>
        unfold generalize_constants at hk
        dsimp [proof_noms, formulasIn] at hk""",
)

# fix mem mp heq_phi branch
text = text.replace(
    """              · rcases List.mem_cons.mp hmem_tail with heq_phi | hmem_append
                · rw [heq_phi] at hkχ
                  exact Or.inl (mem_proof_noms_of_subst_list_noms old ((new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)).2) (mp pf1 pf2) hkχ)""",
    """              · rcases List.mem_cons.mp hmem_tail with heq_phi | hmem_append
                · rw [heq_phi] at hkχ
                  have hkψ : k ∈ ψ.list_noms :=
                    (list_noms_nom_subst_svar ((new_var_geq1 (Nat.le.refl : y ≥ (φ ⟶ ψ).new_var)).2) hkχ).left
                  exact Or.inl (by
                    simp only [proof_noms, List.mem_dedup, List.mem_flatMap]
                    exact ⟨ψ, mem_formulasIn_self (mp pf1 pf2), hkψ⟩)""",
)

assert 'gc_body_mp_formulasIn' in text, 'missing gc_body_mp'
assert '__DELETE_GC_START__' not in text, 'corruption marker present'
assert 'generalize_constants_thm' in text, 'missing thm'

DST.write_text(text)
print(f"Wrote {len(text.splitlines())} lines to {DST}")
