import Hybrid.Form

-- Helper simp lemmas to reduce SVAR ordering / max / addition to `Nat`,
-- so that `omega` can finish arithmetic goals. (mathlib upgrade: the old
-- `simp [SVAR.le, max, SVAR.add]` patterns no longer unfold reliably.)
theorem svar_le_letter {x y : SVAR} : (x ≤ y) = (x.letter ≤ y.letter) := rfl
theorem svar_lt_letter {x y : SVAR} : (x < y) = (x.letter < y.letter) := rfl
theorem svar_add_letter {x : SVAR} {n : Nat} : (x + n).letter = x.letter + n := rfl
theorem svar_max_letter {x y : SVAR} : (max x y).letter = max x.letter y.letter := by
  change (ite (x.letter > y.letter) x y).letter = max x.letter y.letter
  split <;> omega

theorem subst_depth {i : NOM N} {x : SVAR} {φ : Form N} : φ[i // x].depth = φ.depth := by
  induction φ <;> simp [subst_nom, Form.depth, *] at *
  <;> (split <;> simp [Form.depth, *])

theorem subst_depth' {x y : SVAR} {φ : Form N} : φ[y // x].depth = φ.depth := by
  induction φ <;> simp [subst_svar, Form.depth, *] at *
  <;> (split <;> simp [Form.depth, *])

theorem subst_depth'' {x : SVAR} {i : NOM N} {φ : Form N} : (φ[i//x]).depth < (ex x, φ).depth := by
  apply Nat.lt_of_le_of_lt
  apply Nat.le_of_eq
  apply subst_depth
  apply ex_depth

theorem subst_depth_bind {x : SVAR} {i : NOM N} {φ : Form N} : (φ[i//x]).depth < (all x, φ).depth := by
  apply Nat.lt_of_le_of_lt
  apply Nat.le_of_eq
  apply subst_depth
  apply sub_depth_bind

theorem iff_subst_svar {y x : SVAR} : (φ ⟷ ψ)[y // x] = (φ[y//x] ⟷ ψ[y//x]) := by
  simp [subst_svar]

section Variables
  lemma svar_eq {ψ χ : SVAR} : ψ = χ ↔ ψ.1 = χ.1 := by
    have l1 : ψ = ⟨ψ.letter⟩ := by simp
    have l2 : χ = ⟨χ.letter⟩ := by simp
    rw [l1, l2]
    simp

  lemma new_var_neg : (∼ψ).new_var = ψ.new_var := by
    simp [Form.new_var, max, -implication_disjunction]
    rw [←svar_eq]
    intro _
    simp [*]
  
  lemma subst_neg : is_substable (∼ψ) y x ↔ is_substable ψ y x := by
    simp [is_substable]

  lemma new_var_gt      : occurs x φ → x < φ.new_var   := by
    induction φ with
    | svar y          =>
        simp [occurs, Form.new_var, -implication_disjunction]
        intro h
        rw [h]
        exact Nat.lt_succ_self y.letter
    | impl ψ χ ih1 ih2 =>
        simp only [occurs, Form.new_var, Bool.or_eq_true, max]
        intro h
        apply Or.elim h
        . intro ha
          clear ih2 h
          have ih1 := ih1 ha
          by_cases hc : (Form.new_var ψ).letter > (Form.new_var χ).letter
          . simp [hc]
            assumption
          . simp [hc]
            simp at hc 
            exact Nat.lt_of_lt_of_le ih1 hc
        . intro hb
          clear ih1 h
          have ih2 := ih2 hb
          by_cases hc : (Form.new_var ψ).letter > (Form.new_var χ).letter
          . simp [hc]
            simp at hc
            exact Nat.lt_trans ih2 hc
          . simp [hc]
            assumption
    | box ψ ih      =>
        simp only [occurs, Form.new_var]
        assumption
    | bind y ψ ih   =>
        simp only [occurs, Form.new_var, max]
        intro h
        have ih := ih h
        by_cases hc : (y + 1).letter > (Form.new_var ψ).letter
        . simp [hc]
          simp at hc
          exact Nat.lt_trans ih hc
        . simp [hc]
          assumption
    | _ => simp [occurs]

  lemma new_var_is_new  : occurs (φ.new_var) φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro h
    have a := new_var_gt h
    have b := Nat.lt_irrefl φ.new_var.letter
    exact b a
  
  lemma ge_new_var_is_new (h : x ≥ φ.new_var) : occurs x φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro habs
    have := new_var_gt habs
    have a := Nat.lt_of_le_of_lt h this
    have b := Nat.lt_irrefl φ.new_var.letter
    exact b a
  
  lemma ge_new_var_subst_nom {i : NOM N} {y : SVAR} : φ.new_var ≥ φ[i // y].new_var := by
    induction φ with
    | svar z =>
        simp only [subst_nom]
        split <;> simp [Form.new_var, svar_le_letter, svar_add_letter]
    | impl ψ χ ih1 ih2 =>
        simp only [subst_nom, Form.new_var, ge_iff_le, svar_le_letter, svar_max_letter] at *
        omega
    | bind z ψ ih =>
        simp only [subst_nom]
        split <;>
          simp only [Form.new_var, ge_iff_le, svar_le_letter, svar_max_letter, svar_add_letter] at * <;>
          omega
    | box ψ ih =>
        simpa only [subst_nom, Form.new_var, ge_iff_le, svar_le_letter] using ih
    | _ => simp [Form.new_var, subst_nom, svar_le_letter]

lemma new_var_geq1 : x ≥ (φ ⟶ ψ).new_var → (x ≥ φ.new_var ∧ x ≥ ψ.new_var) := by
  intro h
  simp [Form.new_var, max] at *
  split at h
  . apply And.intro
    . assumption
    . apply Nat.le_trans _ h
      apply Nat.le_of_lt
      assumption
  . apply And.intro
    . simp at *
      apply Nat.le_trans _ h
      assumption
    . assumption

lemma new_var_geq2 : x ≥ (all y, ψ).new_var → (x ≥ (y+1) ∧ x ≥ ψ.new_var) := by
  intro h
  simp [Form.new_var, max] at *
  split at h
  . apply And.intro
    . apply Nat.le_trans _ h
      apply Nat.le_of_lt
      assumption
    . assumption
  . apply And.intro
    . assumption
    . simp at *
      apply Nat.le_trans _ h
      assumption

lemma new_var_geq3 : x ≥ (□ φ).new_var → (x ≥ φ.new_var) := by simp [Form.new_var]

lemma new_var_subst {φ : Form N} {i : NOM N} {x y : SVAR} (h : x ≥ φ.new_var) : is_substable (φ[y//i]) x y := by
  induction φ with
  | nom  j  =>
      simp [nom_subst_svar]
      split <;> simp [is_substable]
  | bind z ψ ih =>
      simp only [nom_subst_svar, Form.new_var, max, is_substable, beq_iff_eq, ite_eq_left_iff,
          bne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
          Bool.not_eq_false, Bool.and_eq_true] at h ⊢
      intro _
      by_cases hc : (z + 1).letter > (Form.new_var ψ).letter
      . simp [hc] at h
        simp only [gt_iff_lt, ge_iff_le] at hc ih
        have ih := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
        have ne := Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact ⟨ne, ih⟩
      . simp [hc] at h
        simp only [gt_iff_lt, not_lt, ge_iff_le] at hc ih 
        have ih := ih h
        have ne := Nat.ne_of_lt (Nat.le_trans (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) hc) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact ⟨ne, ih⟩
  | impl ψ χ ih1 ih2 =>
      simp [Form.new_var, max, is_substable, nom_subst_svar] at h ⊢
      by_cases hc : (Form.new_var χ).letter < (Form.new_var ψ).letter
      . simp [hc] at h
        have := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
        exact ⟨ih1 h, ih2 this⟩
      . simp [hc] at h
        simp at hc
        have := Nat.le_trans hc h
        exact ⟨ih1 this, ih2 h⟩
  | box ψ ih         =>
      simp [Form.new_var, is_substable, nom_subst_svar] at h ⊢
      exact ih h
  | _  =>
      simp [nom_subst_svar, is_substable]

lemma new_var_subst'' {φ : Form N} {x y : SVAR} (h : x ≥ φ.new_var) : is_substable φ x y := by
  induction φ with
  | bind z ψ ih =>
      simp only [Form.new_var, max, is_substable, beq_iff_eq, ite_eq_left_iff,
          bne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
          Bool.not_eq_false, Bool.and_eq_true] at h ⊢
      intro _
      by_cases hc : (z + 1).letter > (Form.new_var ψ).letter
      . simp [hc] at h
        simp only [gt_iff_lt, ge_iff_le] at hc ih
        have ih := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
        have ne := Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact ⟨ne, ih⟩
      . simp [hc] at h
        simp only [gt_iff_lt, not_lt, ge_iff_le] at hc ih 
        have ih := ih h
        have ne := Nat.ne_of_lt (Nat.le_trans (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) hc) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact ⟨ne, ih⟩
  | impl ψ χ ih1 ih2 =>
      simp [Form.new_var, max, is_substable, nom_subst_svar] at h ⊢
      by_cases hc : (Form.new_var χ).letter < (Form.new_var ψ).letter
      . simp [hc] at h
        have := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
        exact ⟨ih1 h, ih2 this⟩
      . simp [hc] at h
        simp at hc
        have := Nat.le_trans hc h
        exact ⟨ih1 this, ih2 h⟩
  | box ψ ih         =>
      simp [Form.new_var, is_substable, nom_subst_svar] at h ⊢
      exact ih h
  | _  =>
      simp [is_substable]

lemma scz {φ : Form N} (i : NOM N) (h : x ≥ φ.new_var) (hy : y ≠ x) : (is_free y φ) ↔ (is_free y (φ[x // i])) := by
  induction φ with
  | nom a       =>
      simp [nom_subst_svar] ; split <;> simp [is_free, hy]
  | bind z ψ ih =>
      simp [is_free, nom_subst_svar, -implication_disjunction]
      simp [new_var_geq2 h] at ih
      simp [nom_subst_svar, is_free, ih]
  | impl ψ χ ih1 ih2 =>
      have ⟨ih1_cond, ih2_cond⟩ := new_var_geq1 h
      simp [ih1_cond, ih2_cond] at ih1 ih2
      simp [is_free, nom_subst_svar, ih1, ih2]
  | box ψ ih         =>
      simp [Form.new_var] at h
      simp [h] at ih
      simp [is_free, nom_subst_svar, ih]
  | _ => simp [is_free, nom_subst_svar]

lemma new_var_subst' {φ : Form N} (i : NOM N) {x y : SVAR} (h1 : is_substable φ v y) (h2 : x ≥ φ.new_var) (h3 : y ≠ x) : is_substable (φ[x//i]) v y := by
  induction φ with
  | nom  a      => simp [nom_subst_svar]; split <;> simp [is_substable]
  | bind z ψ ih =>
      have xge := (new_var_geq2 h2).right
      have hsc := @scz N x y ψ i xge h3
      have heq : is_free y (ψ[x//i]) = is_free y ψ := by
        cases h' : is_free y ψ <;> cases h'' : is_free y (ψ[x//i]) <;> simp_all
      simp only [nom_subst_svar]
      simp [is_substable] at h1 ⊢
      rcases h1 with hf | ⟨hzv, hsub⟩
      · left; rw [heq]; exact hf
      · right; exact ⟨hzv, ih hsub xge⟩
  | impl ψ χ ih1 ih2  =>
      simp [is_substable] at h1
      simp [Form.new_var] at h2
      have ⟨ih1_cond, ih2_cond⟩ := new_var_geq1 h2 
      simp [h1, h2, ih1_cond, ih2_cond] at ih1 ih2
      simp [is_substable, nom_subst_svar, ih1, ih2]
  | box ψ ih          =>
      simp [is_substable] at h1
      simp [Form.new_var] at h2
      simp [h1, h2] at ih
      simp [is_substable, nom_subst_svar, ih]
  | _       =>  simp [nom_subst_svar, h1]

lemma nom_subst_trans (i : NOM N) (x y : SVAR) (h : y ≥ φ.new_var) : φ[y // i][x // y] = φ[x // i] := by
  induction φ with
  | bttm => simp [nom_subst_svar, subst_svar]
  | prop => simp [nom_subst_svar, subst_svar]
  | nom _ =>
    simp [nom_subst_svar]
    split <;> simp [subst_svar]
  | svar z =>
    have nocc := ge_new_var_is_new h
    simp only [nom_subst_svar, subst_svar]
    split <;> simp_all [occurs]
  | bind z ψ ih =>
    simp only [nom_subst_svar, subst_svar]
    have := new_var_geq2 h
    by_cases hc : y = z
    . exfalso
      have := this.left
      simp [hc] at this
      have := Nat.ne_of_lt (Nat.lt_succ_of_le this)
      contradiction
    . simp [nom_subst_svar, ih this.right, hc]
  | impl ψ χ ih1 ih2 =>
      simp [nom_subst_svar, subst_svar, ih1, ih2, new_var_geq1 h]
  | box ψ ih         =>
      simp [Form.new_var] at h
      simp [nom_subst_svar, subst_svar, ih, h]

  lemma subst_nom_noop {φ : Form N} {i : NOM N} {y : SVAR} (h : occurs y φ = false) : φ[i // y] = φ := by
    induction φ with
    | svar z => simp only [subst_nom]; split <;> simp_all [occurs]
    | impl a b iha ihb =>
        simp only [occurs, Bool.or_eq_false_iff] at h
        simp only [subst_nom, iha h.1, ihb h.2]
    | box a ih => simp only [occurs] at h; simp only [subst_nom, ih h]
    | bind w a ih => simp only [occurs] at h; simp only [subst_nom]; split <;> simp_all [ih h]
    | _ => rfl

  -- Substituting `x` by a fresh `y` and then renaming `y` to a nominal `i` is the
  -- same as directly substituting `x` by `i`.  Freshness of `y` (it exceeds the
  -- new-variable bound, so it differs from every free *and bound* variable of `φ`)
  -- is what prevents capture.
  lemma rename_svar_nom {φ : Form N} (i : NOM N) (x y : SVAR) (h : y ≥ φ.new_var) : φ[y // x][i // y] = φ[i // x] := by
    induction φ with
    | bttm => simp [subst_svar, subst_nom]
    | prop => simp [subst_svar, subst_nom]
    | nom _ => simp [subst_svar, subst_nom]
    | svar z =>
        have hyz : y ≠ z := by
          have := ge_new_var_is_new h; simpa [occurs] using this
        by_cases hxz : x = z
        · subst hxz; simp [subst_svar, subst_nom]
        · simp [subst_svar, subst_nom, hxz, hyz]
    | impl ψ χ ih1 ih2 =>
        simp [subst_svar, subst_nom, ih1 (new_var_geq1 h).1, ih2 (new_var_geq1 h).2]
    | box ψ ih =>
        simp only [Form.new_var] at h
        simp [subst_svar, subst_nom, ih h]
    | bind z ψ ih =>
        have hb := new_var_geq2 h
        have hyz : y ≠ z := by
          intro habs; have hle := hb.left; rw [habs] at hle
          simp only [svar_le_letter, svar_add_letter] at hle; omega
        by_cases hxz : x = z
        · subst hxz
          have hnoop : ψ[i // y] = ψ := subst_nom_noop (ge_new_var_is_new hb.right)
          simp [subst_svar, subst_nom, hyz, hnoop]
        · simp [subst_svar, subst_nom, hxz, hyz, ih hb.right]

  lemma ge_new_var_subst_helpr {i : NOM N} {x : SVAR} (h : y ≥ Form.new_var (χ⟶ψ)) : y ≥ Form.new_var (χ⟶ψ[i//x]⟶⊥) := by
    simp [Form.new_var, max]
    split <;> split
    . exact (new_var_geq1 h).left
    . apply Nat.le_trans
      apply ge_new_var_subst_nom
      exact (new_var_geq1 h).right
    . exact (new_var_geq1 h).left
    . simp [svar_le_letter]

  lemma notfreeset {Γ : Set (Form N)} (L : List Γ) (hyp : ∀ ψ : Γ, is_free x ψ.1 = false) : is_free x (conjunction Γ L) = false := by
    induction L with
    | nil         =>
        simp [conjunction, is_free]
    | cons hd tl ih =>
        have hhd := hyp hd
        simp [conjunction, is_free, hhd, ih]

  lemma notfree_after_subst {φ : Form N} {x y : SVAR} (h : x ≠ y) : is_free x (φ[y // x]) = false := by
    induction φ with
    | svar z   =>
        by_cases xz : x = z
        . simp [subst_svar, if_pos xz, is_free, h]
        . simp [subst_svar, if_neg xz, is_free, xz]
    | impl _ _ ih1 ih2 =>
        simp [subst_svar, is_free, ih1, ih2]
    | box _ ih    =>
        simp [subst_svar, is_free, ih]
    | bind z _ ih =>
        by_cases xz : x = z
        . simp [subst_svar, xz, is_free]
        . simp [subst_svar, if_neg xz, is_free, ih]
    | _        => simp [subst_svar, is_free]

  lemma notocc_beforeafter_subst {φ : Form N} {x y : SVAR} (h : occurs x φ = false) : occurs x (φ[y // x]) = false := by
    induction φ with
    | svar z   =>
        by_cases xz : x = z
        <;> simp [subst_svar, if_pos xz, xz, occurs, h] at *
    | impl _ _ ih1 ih2 =>
        simp [subst_svar, occurs, not_or, ih1, ih2, -implication_disjunction] at *
        exact ⟨ih1 h.left, ih2 h.right⟩ 
    | box _ ih    =>
        simp [subst_svar, occurs, ih, -implication_disjunction] at *
        exact ih h
    | bind z ψ ih =>
        by_cases xz : x = z
        . simp [subst_svar, xz, occurs] at *
          exact h
        . simp [subst_svar, if_neg xz, occurs, ih, xz, h, -implication_disjunction] at *
    | _        => simp [subst_svar, occurs]

  lemma notoccursbind : occurs x φ = false → occurs x (all v, φ) = false := by
    simp [occurs]

  lemma notoccurs_notfree : (occurs x φ = false) → (is_free x φ = false) := by
    induction φ with
    | svar _ => simp [occurs, is_free]
    | impl _ _ ih1 ih2 =>
        intro h
        simp [occurs] at h
        simp [is_free, ih1, ih2, h]
    | box _ ih        =>
        intro h
        rw [occurs] at h
        simp [is_free, ih, h]
    | bind _ _ ih     =>
        intro h
        rw [occurs] at h
        simp [is_free, ih, h]
    | _ => 
        intro h
        rfl

  lemma preserve_notfree {φ : Form N} (x v : SVAR) : (is_free x φ = false) → (is_free x (all v, φ) = false) := by
    intro h
    simp only [is_free, h, Bool.and_false]

  lemma subst_notfree_var {φ : Form N} {x y : SVAR} (h : is_free x φ = false) : (φ[y // x] = φ) ∧ (occurs x φ = false → is_substable φ y x) := by
    induction φ with
    | svar z =>
        by_cases heq : x = z
        . simp [is_free, heq] at h
        . simp [subst_svar, heq, occurs, is_substable]
    | impl ψ χ ih1 ih2 =>
        simp only [is_free, Bool.or_eq_false_eq_eq_false_and_eq_false] at h 
        apply And.intro
        . simp [subst_svar, h, ih1, ih2]
        . intro nocc
          simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at nocc 
          simp [is_substable, h, nocc, ih1, ih2]
    | box ψ ih  =>
        rw [is_free] at h
        apply And.intro
        . simp [subst_svar, ih, h]
        . intro nocc
          rw [occurs] at nocc
          simp [is_substable, ih, nocc, h]
    | bind z ψ ih =>
        apply And.intro
        . by_cases heq : x = z
          . rw [←heq, subst_svar, if_pos (Eq.refl x)]
          . simp only [is_free, bne, Bool.and_eq_false_eq_eq_false_or_eq_false, Bool.not_eq_false', beq_iff_eq,
            Ne.symm heq, false_or] at h 
            simp [subst_svar, heq, ih, h]
        . intro nocc
          rw [occurs] at nocc
          simp [is_substable, notoccurs_notfree, nocc]
    | _   =>
        simp [subst_svar, is_substable]

    lemma rereplacement (φ : Form N) (x y : SVAR) (h1 : occurs y φ = false) (h2 : is_substable φ y x) : (is_substable (φ[y // x]) x y) ∧ φ[y // x][x // y] = φ := by
      induction φ with
      | svar z =>
          simp [occurs] at h1
          by_cases xz : x = z
          repeat simp [subst_svar, xz, h1, is_substable]
      | impl ψ χ ih1 ih2 =>
          simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at h1 
          simp only [is_substable, Bool.and_eq_true] at h2
          simp [subst_svar, ih1, ih2, h1, h2, is_substable]
      | box ψ ih =>
          simp only [occurs] at h1
          simp only [is_substable] at h2
          simp [subst_svar, ih, h1, h2, is_substable]
      | bind z ψ ih =>
          by_cases yz : y = z
          . rw [←yz]
            rw [←yz] at h1

            simp only [is_substable, beq_iff_eq, ←yz, bne_self_eq_false, Bool.false_and, ite_eq_left_iff,
              Bool.not_eq_false, implication_disjunction, Bool.not_eq_true, or_false] at h2 
            rw [or_iff_left (show ¬(false = true) by decide)] at h2
            have h2 := @preserve_notfree N ψ x y h2
            simp [subst_notfree_var, h2]

            have := @subst_notfree_var N (all y, ψ) y x (notoccurs_notfree h1)
            simp [@subst_notfree_var N (all y, ψ) y x, notoccurs_notfree, h1]
          . by_cases xz : x = z
            . have : is_free x (all x, ψ) = false := by simp [is_free]
              rw [←xz] at h1
              simp [←xz, subst_notfree_var, this, notoccurs_notfree, h1]
            . simp only [occurs] at h1
              simp [subst_svar, xz, yz]
              by_cases xfree : is_free x ψ
              . simp [is_substable, xfree, Ne.symm yz, bne] at h2
                simp [ih, h1, h2, is_substable, bne, Ne.symm xz]
              . rw [show (¬is_free x ψ = true ↔ is_free x ψ = false) by simp] at xfree
                simp [subst_notfree_var, xfree, is_substable, (notoccurs_notfree h1)]
      | _     =>
          apply And.intro
          repeat rfl
  
  lemma subst_self_is_self (φ : Form N) (x : SVAR) : φ [x // x] = φ := by
    induction φ with
    | svar y   =>
        by_cases xy : x = y
        . rw [subst_svar, if_pos xy, xy]
        . rw [subst_svar, if_neg xy]
    | impl φ ψ ih1 ih2 =>
        rw [subst_svar, ih1, ih2]
    | box  φ ih  =>
        rw [subst_svar, ih]
    | bind y φ ih =>
        by_cases xy : x = y
        . rw [subst_svar, if_pos xy]
        . rw [subst_svar, if_neg xy, ih]
    | _        => rfl

  lemma pos_subst {m : ℕ} {i : NOM N} {v : SVAR} : (iterate_pos m (v⋀φ))[i//v] = iterate_pos m (i⋀φ[i//v]) := by
    induction m with
    | zero =>
        simp [iterate_pos, iterate_pos.loop, subst_nom]
    | succ n ih =>
        simp [iterate_pos, iterate_pos.loop, subst_nom] at ih ⊢
        rw [ih]

  lemma nec_subst {m : ℕ} {i : NOM N} {v : SVAR} : (iterate_nec m (v⟶φ))[i//v] = iterate_nec m (i⟶φ[i//v]) := by
    induction m with
    | zero =>
        simp [iterate_nec, iterate_nec.loop, subst_nom]
    | succ n ih =>
        simp [iterate_nec, iterate_nec.loop, subst_nom] at ih ⊢
        rw [ih]

  theorem Form.new_var_properties (φ : Form N) : ∃ x : SVAR, x ≥ φ.new_var ∧ occurs x φ = false ∧ (∀ y : SVAR, is_substable φ x y) := by
    exists φ.new_var
    refine ⟨?_, new_var_is_new, fun y => ?_⟩
    · simp [ge_iff_le, svar_le_letter]
    · apply new_var_subst''
      simp [ge_iff_le, svar_le_letter]
end Variables

section Nominals
  lemma nom_svar_subst_symm {v x y : SVAR} {i : NOM N} (h : y ≠ x) : φ[x//i][v//y] = φ[v//y][x//i] := by
    induction φ <;> simp [subst_svar, nom_subst_svar, *] at *
    . split <;> simp[nom_subst_svar]
    . split <;> simp [subst_svar, h]
    . split <;> simp [nom_subst_svar]

  lemma nom_nom_subst_symm {x y : SVAR} {j i : NOM N} (h1 : j ≠ i) (h2 : y ≠ x) : φ[x//i][j//y] = φ[j//y][x//i] := by
    induction φ <;> simp [nom_subst_svar, subst_nom, *] at *
    . split <;> simp [nom_subst_svar, *]
    . split <;> simp [subst_nom, *]
    . split <;> simp [nom_subst_svar]

  lemma subst_collect_all {x y : SVAR} {i : NOM N} : φ[i//y][x//i] = φ[x//i][x//y] := by
    induction φ <;> simp [subst_svar, subst_nom, nom_subst_svar, *] at *
    . split <;> simp [nom_subst_svar]
    . split <;> simp [subst_svar]
    . split <;> simp [nom_subst_svar, *]

  theorem nom_subst_nocc (h : nom_occurs i χ = false) (y : SVAR) : χ[y // i] = χ := by
    induction χ <;> simp [nom_occurs, nom_subst_svar, *, -implication_disjunction] at *
    . intro; apply h; apply Eq.symm; assumption
    . simp [h] at *
      apply And.intro <;> assumption

  theorem subst_collect_all_nocc (h : nom_occurs i χ = false) (x y : SVAR) : χ[i // x][y // i] = χ[y // x] := by
    rw [subst_collect_all, nom_subst_nocc h y]

  lemma nom_svar_rereplacement {φ : Form N} {i : NOM N} (h : x ≥ φ.new_var) : φ[x // i][i // x] = φ := by
    induction φ <;> simp [nom_subst_svar, subst_nom] 
    . have := ge_new_var_is_new h
      simp [occurs] at this
      exact this
    . split <;> simp [subst_nom, *]
    . simp [new_var_geq1 h, *]
    . simp [new_var_geq3 h, *]
    . split
      . next h2 =>
          have l1 := (new_var_geq2 h).left
          rw [←h2] at l1
          have l2 := Nat.le_succ x
          have := Nat.le_antisymm l1 l2
          simp only [svar_add_letter] at this
          omega
      . simp [new_var_geq2 h, *]

  lemma pos_subst_nom {m : ℕ} {i : NOM N} {v x : SVAR} : (iterate_pos m (v⋀φ))[x//i] = iterate_pos m (Form.svar v⋀φ[x//i]) := by
    induction m with
    | zero =>
        simp [iterate_pos, iterate_pos.loop, nom_subst_svar]
    | succ n ih =>
        simp [iterate_pos, iterate_pos.loop, nom_subst_svar] at ih ⊢
        rw [ih]

  lemma nec_subst_nom {m : ℕ} {i : NOM N} {v x : SVAR} : (iterate_nec m (v⟶φ))[x//i] = iterate_nec m (Form.svar v⟶φ[x//i]) := by
    induction m with
    | zero =>
        simp [iterate_nec, iterate_nec.loop, nom_subst_svar]
    | succ n ih =>
        simp [iterate_nec, iterate_nec.loop, nom_subst_svar] at ih ⊢
        rw [ih]

  lemma diffsvar {v x : SVAR} (h : x ≥ v+1) : v ≠ x := by
    simp; intro abs; exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self v.letter) h)) (SVAR.mk.inj abs)  

  theorem is_free_nom_subst_nom {ψ : Form N} {v : SVAR} {new old : NOM N} :
      is_free v (ψ[new // old]) = is_free v ψ := by
    induction ψ generalizing v with
    | nom a =>
        by_cases ha : a = old <;> simp [nom_subst_nom, is_free, ha]
    | bind y ψ ih =>
        by_cases hy : y = v
        · simp [nom_subst_nom, is_free, hy]
        · simp [nom_subst_nom, is_free, hy, ih]
    | impl a b iha ihb => simp [nom_subst_nom, is_free, iha, ihb]
    | box a ih => simp [nom_subst_nom, is_free, ih]
    | _ => simp [nom_subst_nom, is_free]

  theorem is_substable_nom_subst_nom {ψ : Form N} {s v : SVAR} {new old : NOM N} :
      is_substable (ψ[new // old]) s v = is_substable ψ s v := by
    induction ψ generalizing s v with
    | nom a =>
        by_cases ha : a = old <;> simp [nom_subst_nom, is_substable, ha]
    | bind y ψ ih =>
        simp only [nom_subst_nom, is_substable, is_free_nom_subst_nom]
        by_cases hy : y = v
        · by_cases hf : is_free v ψ <;> simp [hy, hf, ih]
        · by_cases hf : is_free v ψ <;> simp [hy, hf, ih]
    | impl a b iha ihb => simp [nom_subst_nom, is_substable, iha, ihb]
    | box a ih => simp [nom_subst_nom, is_substable, ih]
    | _ => simp [nom_subst_nom, is_substable]

  theorem nom_svar_subst_comm_nom {ψ : Form N} {new old : NOM N} {s v : SVAR} :
      (ψ[s // v])[new // old] = (ψ[new // old])[s // v] := by
    induction ψ generalizing s v with
    | svar z =>
        by_cases hv : v = z <;> simp [subst_svar, nom_subst_nom, hv]
    | impl a b iha ihb => simp [subst_svar, nom_subst_nom, iha, ihb]
    | box a ih => simp [subst_svar, nom_subst_nom, ih]
    | nom a =>
        simp only [subst_svar, subst_nom, nom_subst_nom]
        by_cases ha : a = old <;> simp [ha, subst_svar, subst_nom]
    | bind z a ih =>
        simp only [subst_svar, nom_subst_nom]
        split_ifs <;> simp [subst_svar, nom_subst_nom, ih, *]
    | _ => simp [subst_svar, nom_subst_nom]

  theorem subst_nom_nom_subst {ψ : Form N} {s : NOM N} {v : SVAR} {new old : NOM N} :
      (ψ[s // v])[new // old] = (ψ[new // old])[(if s = old then new else s) // v] := by
    induction ψ generalizing s v with
    | svar a =>
        by_cases ha : v = a <;> by_cases hs : s = old <;> simp [subst_nom, nom_subst_nom, ha, hs, ↓reduceIte]
    | nom a =>
        by_cases ha : a = old <;> by_cases hs : s = old <;> simp [subst_nom, nom_subst_nom, ha, hs, ↓reduceIte]
    | impl a b iha ihb => simp [subst_nom, nom_subst_nom, iha, ihb]
    | box a ih => simp [subst_nom, nom_subst_nom, ih]
    | bind z a ih =>
        simp [subst_nom, nom_subst_nom, ↓reduceIte]
        split_ifs <;> simp [subst_nom, nom_subst_nom, ih, *]
    | _ => simp [subst_nom, nom_subst_nom]

  lemma nom_subst_box {ψ : Form N} {new old : NOM N} :
      nom_subst_nom (□ ψ) new old = □ (nom_subst_nom ψ new old) := by
    simp [nom_subst_nom]

  lemma nom_subst_diamond {ψ : Form N} {new old : NOM N} :
      nom_subst_nom (◇ ψ) new old = ◇ (nom_subst_nom ψ new old) := by
    simp [Form.diamond, nom_subst_nom, nom_subst_box]

  theorem nom_subst_iterate_pos {ψ : Form N} {new old : NOM N} {m : ℕ} :
      nom_subst_nom (iterate_pos m ψ) new old = iterate_pos m (nom_subst_nom ψ new old) := by
    induction m generalizing ψ with
    | zero => rfl
    | succ k ih =>
        conv_lhs => rw [iterate_pos, iterate_pos.loop]
        conv_rhs => rw [iterate_pos, iterate_pos.loop]
        rw [nom_subst_diamond]
        simpa using ih

  theorem nom_subst_iterate_nec {ψ : Form N} {new old : NOM N} {n : ℕ} :
      nom_subst_nom (iterate_nec n ψ) new old = iterate_nec n (nom_subst_nom ψ new old) := by
    induction n generalizing ψ with
    | zero => rfl
    | succ k ih =>
        conv_lhs => rw [iterate_nec, iterate_nec.loop]
        conv_rhs => rw [iterate_nec, iterate_nec.loop]
        rw [nom_subst_box]
        simpa using ih

  lemma nom_subst_conj_svar {φ : Form N} {new old : NOM N} (v : SVAR) :
      nom_subst_nom (v ⋀ φ) new old = v ⋀ nom_subst_nom φ new old := by
    simp [Form.conj, Form.neg, Form.impl, nom_subst_nom]

  lemma nom_subst_imp_svar {φ : Form N} {new old : NOM N} (v : SVAR) :
      nom_subst_nom (v ⟶ φ) new old = v ⟶ nom_subst_nom φ new old := by
    simp only [Form.impl, nom_subst_nom]

  lemma nom_subst_iterate_pos_svar {φ : Form N} {new old : NOM N} (m : ℕ) (v : SVAR) :
      nom_subst_nom (iterate_pos m (v ⋀ φ)) new old =
        iterate_pos m (v ⋀ nom_subst_nom φ new old) := by
    induction m generalizing φ with
    | zero => simp [iterate_pos, iterate_pos.loop, Form.conj, Form.neg, Form.impl, nom_subst_nom]
    | succ k ih =>
        conv_lhs => rw [iterate_pos, iterate_pos.loop]
        conv_rhs => rw [iterate_pos, iterate_pos.loop]
        rw [nom_subst_diamond]
        simpa using ih

  lemma nom_subst_iterate_nec_svar {φ : Form N} {new old : NOM N} (n : ℕ) (v : SVAR) :
      nom_subst_nom (iterate_nec n (v ⟶ φ)) new old =
        iterate_nec n (v ⟶ nom_subst_nom φ new old) := by
    induction n generalizing φ with
    | zero => simp [iterate_nec, iterate_nec.loop, Form.impl, nom_subst_nom]
    | succ k ih =>
        conv_lhs => rw [iterate_nec, iterate_nec.loop]
        conv_rhs => rw [iterate_nec, iterate_nec.loop]
        rw [nom_subst_box]
        simpa using ih

  theorem nom_subst_ax_nom {φ : Form N} {v : SVAR} {m n : ℕ} {new old : NOM N} :
      (all v, (iterate_pos m (v ⋀ φ) ⟶ iterate_nec n (v ⟶ φ)))[new // old] =
        all v, (iterate_pos m (v ⋀ φ[new // old]) ⟶ iterate_nec n (v ⟶ φ[new // old])) := by
    simp only [nom_subst_nom, nom_subst_iterate_pos_svar, nom_subst_iterate_nec_svar]

  theorem nom_subst_ax_q2_nom {φ : Form N} {v : SVAR} {s new old : NOM N} :
      ((all v, φ) ⟶ φ[s // v])[new // old] =
        (all v, φ[new // old]) ⟶ (φ[new // old])[(if s = old then new else s) // v] := by
    simp only [nom_subst_nom, subst_nom_nom_subst]

  section New_NOM
  lemma new_nom_gt      : nom_occurs i φ → i.letter < φ.new_nom.letter   := by
    induction φ with
    | nom i          =>
        simp [nom_occurs, Form.new_nom, -implication_disjunction]
        intro h
        rw [h]
        exact Nat.lt_succ_self i.letter
    | impl ψ χ ih1 ih2 =>
        simp only [nom_occurs, Form.new_nom, Bool.or_eq_true, max]
        intro h
        apply Or.elim h
        . intro ha
          clear ih2 h
          have ih1 := ih1 ha
          by_cases hc : (Form.new_nom ψ).letter > (Form.new_nom χ).letter
          . simp [hc]
            assumption
          . simp [hc]
            simp at hc 
            exact Nat.lt_of_lt_of_le ih1 hc
        . intro hb
          clear ih1 h
          have ih2 := ih2 hb
          by_cases hc : (Form.new_nom ψ).letter > (Form.new_nom χ).letter
          . simp [hc]
            simp at hc
            exact Nat.lt_trans ih2 hc
          . simp [hc]
            assumption
    | box      =>
        assumption
    | bind     =>
        assumption
    | _ => simp [nom_occurs]

  lemma new_nom_is_nom  : nom_occurs (φ.new_nom) φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro h
    have a := new_nom_gt h
    have b := Nat.lt_irrefl φ.new_nom.letter
    exact b a
  
  lemma ge_new_nom_is_new (h : x ≥ φ.new_nom) : nom_occurs x φ = false := by
    rw [←Bool.eq_false_eq_not_eq_true]
    intro habs
    have := new_nom_gt habs
    have a := Nat.lt_of_le_of_lt h this
    have b := Nat.lt_irrefl φ.new_nom.letter
    exact b a
  end New_NOM

-- just remove this definition, it is completely redundant...
  def descending (l : List (NOM N)) : Prop :=
    match l with
    | []        =>    True
    | h :: t    =>    (∀ i ∈ t, h > i) ∧ descending t

  def descending' (l : List (NOM N)) : Prop := List.IsChain GT.gt l

  theorem eq_len {φ : Form TotalSet} : φ.list_noms.length = φ.odd_list_noms.length := by simp [Form.odd_list_noms]

  theorem odd_is_odd {φ : Form TotalSet} (h1 : n < φ.list_noms.length) (h2 : n < φ.odd_list_noms.length) : φ.odd_list_noms.get ⟨n, h2⟩ = 2 * φ.list_noms.get ⟨n, h1⟩ + 1 := by
    simp [Form.odd_list_noms, Form.list_noms]

  theorem descending_equiv (l : List (NOM N)) : descending l ↔ descending' l := by
    induction l with
    | nil         =>  simp [descending, descending']
    | cons h t ih =>
        simp only [descending]
        rw [ih]
        simp only [descending', List.isChain_iff_pairwise, List.pairwise_cons]

  theorem descending_property (desc : descending l) (h0 : pos < l.length) (h1 : i ∈ l) (h2 : i > l[pos]) : i ∈ l.take pos := by
    match l with
    | []     => simp at h1
    | h :: t =>
        simp at h0 h1
        cases pos with
        | zero =>
            simp at h2 ⊢
            apply Or.elim h1
            . intro eq
              rw [eq] at h2
              apply Nat.lt_irrefl h.letter
              assumption
            . intro i_mem_t
              apply Nat.lt_asymm h2
              exact (desc.left i i_mem_t)
        | succ pos =>
            apply Or.elim h1
            . intro i_h
              simp [i_h]
            . intro h1_new
              simp
              apply Or.inr
              have desc_new := desc.right
              have h0_new : pos < t.length := by apply Nat.lt_of_succ_lt_succ; assumption
              have h2_new : i > t[pos] := by simp at h2 ⊢; simp [h2]
              exact descending_property desc_new h0_new h1_new h2_new

  theorem descending_ndup (desc : descending l) (h0 : pos < l.length) (h1 : i = l[pos]) : ¬i ∈ l.take pos := by
    rw [descending_equiv, descending', List.isChain_iff_pairwise, List.pairwise_iff_getElem] at desc
    intro habs
    rw [List.mem_iff_getElem] at habs
    obtain ⟨k, hk, hik⟩ := habs
    rw [List.length_take] at hk
    have hkpos : k < pos := lt_of_lt_of_le hk (Nat.min_le_left _ _)
    have hklen : k < l.length := lt_of_lt_of_le hk (Nat.min_le_right _ _)
    rw [List.getElem_take] at hik
    have hgt := desc k pos hklen h0 hkpos
    rw [hik, h1] at hgt
    apply Nat.lt_irrefl l[pos].letter
    exact hgt

  theorem descending_list_noms {φ : Form TotalSet} : descending φ.list_noms := by
    rw [descending_equiv, descending']
    exact list_noms_chain'
  
  theorem descending_odd_list_noms {φ : Form TotalSet} : descending φ.odd_list_noms := by
    have dln := @descending_list_noms φ
    have : ∀ a b : NOM TotalSet, (2 * b + 1 < 2 * a + 1) ↔ (b < a) := by
      intro a b
      change ((b.letter : ℕ) * 2 + 1 < (a.letter : ℕ) * 2 + 1) ↔ ((b.letter : ℕ) < (a.letter : ℕ))
      omega
    have := @List.Pairwise.iff (NOM TotalSet) (fun a b => 2 * b + 1 < 2 * a + 1) (fun a b => b < a) this
    simp only [Form.odd_list_noms, descending_equiv, descending', List.isChain_iff_pairwise, List.pairwise_map, GT.gt, this] at dln ⊢
    assumption

  theorem occurs_list_noms : nom_occurs i φ ↔ i ∈ φ.list_noms := by
    induction φ with
    | impl φ ψ ih1 ih2 =>
        simp only [Form.list_noms, nom_occurs, Bool.or_eq_true, ih1, ih2, List.mem_dedup,
          List.mem_merge]
    | box _ ih    => exact ih
    | bind _ _ ih => exact ih
    | _        => simp [Form.list_noms, nom_occurs]

  /-- After substituting a fresh state variable for a nominal, no new nominals appear and the
      replaced nominal disappears from the inventory. -/
  theorem list_noms_nom_subst_svar {x : SVAR} {old : NOM N} (hx : x ≥ φ.new_var) :
      ∀ {k : NOM N}, k ∈ (φ[x // old]).list_noms → k ∈ φ.list_noms ∧ k ≠ old := by
    intro k hk
    induction φ generalizing x with
    | nom a =>
        by_cases heq : a = old
        · subst heq
          simp [nom_subst_svar, Form.list_noms] at hk
        · simp [nom_subst_svar, Form.list_noms, heq] at hk
          subst hk
          exact ⟨List.mem_singleton.mpr rfl, heq⟩
    | impl ψ χ ih1 ih2 =>
        have hx1 := (new_var_geq1 hx).1
        have hx2 := (new_var_geq1 hx).2
        simp only [nom_subst_svar, Form.list_noms, List.mem_dedup, List.mem_merge] at hk
        rcases hk with h | h
        · rcases ih1 hx1 h with ⟨hk', hne⟩
          exact ⟨by
            rw [Form.list_noms, List.mem_dedup, List.mem_merge]
            exact Or.inl hk', hne⟩
        · rcases ih2 hx2 h with ⟨hk', hne⟩
          exact ⟨by
            rw [Form.list_noms, List.mem_dedup, List.mem_merge]
            exact Or.inr hk', hne⟩
    | box ψ ih =>
        have hx' := new_var_geq3 hx
        simp only [nom_subst_svar, Form.list_noms] at hk
        exact ih hx' hk
    | bind y ψ ih =>
        have hx' := (new_var_geq2 hx).2
        simp only [nom_subst_svar, Form.new_var, max, Form.list_noms] at hk
        exact ih hx' hk
    | _ => simp [nom_subst_svar, Form.list_noms] at hk

  theorem list_noms_subst {old new : NOM N} : i ∈ (φ[new // old]).list_noms → ((i ∈ φ.list_noms ∧ i ≠ old) ∨ i = new) := by
    rw [←occurs_list_noms, ←occurs_list_noms]
    intro h
    induction φ with
    | nom j =>
        simp [nom_subst_nom] at h
        split at h
        . simp [nom_occurs] at h; apply Or.inr; assumption
        . apply Or.inl
          apply And.intro
          . assumption
          . simp [nom_occurs] at h
            rw [h]
            assumption
    | impl ψ χ ih1 ih2 =>
        simp [nom_subst_nom, nom_occurs] at h ⊢
        apply Or.elim h
        . intro hyp
          apply Or.elim (ih1 hyp)
          . intro hl
            simp [hl]
          . intro hr
            simp [hr]
        . intro hyp
          apply Or.elim (ih2 hyp)
          . intro hl
            simp [hl]
          . intro hr
            simp [hr]
    | box ψ ih =>
        simp [nom_subst_nom, nom_occurs] at h
        exact ih h
    | bind _ ψ ih =>
        simp [nom_subst_nom, nom_occurs] at h
        exact ih h
    | _     => simp [nom_subst_nom, nom_occurs] at h

  theorem occ_bulk {l_new l_old : List (NOM N)} {φ : Form N} (eq_len : l_new.length = l_old.length) : nom_occurs i (φ.bulk_subst l_new l_old) → ((i ∈ φ.list_noms ∧ i ∉ l_old) ∨ i ∈ l_new) := by
    intro h
    induction l_new generalizing φ l_old with
    | nil => cases l_old <;> simp [Form.bulk_subst] at *; repeat exact occurs_list_noms.mp h
    | cons h_new t_new ih =>
        cases l_old with
        | nil =>
            simp [Form.bulk_subst] at h ⊢
            apply Or.inl
            exact occurs_list_noms.mp h
        | cons h_old t_old =>
            simp [Form.bulk_subst] at eq_len h ⊢
            have := ih eq_len h
            apply Or.elim this
            . intro hyp
              clear this ih
              cases t_new
              . have := List.length_eq_zero_iff.mp (Eq.symm (Eq.subst eq_len (@List.length_nil (NOM N))))
                simp [this, Form.bulk_subst] at h ⊢
                apply Or.elim (list_noms_subst (occurs_list_noms.mp h))
                . intro c1
                  simp [c1]
                . intro c2
                  exact Or.inr c2
              . cases t_old
                . simp at eq_len
                . simp [Form.bulk_subst] at hyp ⊢
                  have ⟨a, b⟩ := hyp
                  apply Or.elim (list_noms_subst b)
                  . intro c1
                    apply Or.inl
                    simp [c1, a]
                  . intro c2
                    simp [c2]
            . intro hyp
              clear this ih
              apply Or.inr
              apply Or.inr
              assumption

  theorem nocc_bulk {l_new l_old : List (NOM N)} {φ : Form N} (eq_len : l_new.length = l_old.length) : ((i ∉ φ.list_noms ∨ i ∈ l_old) ∧ i ∉ l_new) → nom_occurs i (φ.bulk_subst l_new l_old) = false := by
    rw [contraposition]
    simp [-implication_disjunction]
    intro h1 h2
    apply Or.elim (occ_bulk eq_len h1)
    . simp
    . simp [h2]

  theorem has_nocc_bulk_property : ∀ φ : Form TotalSet, nocc_bulk_property φ.odd_list_noms φ.list_noms φ := by
    unfold nocc_bulk_property
    intro φ n i h
    match n with
    | ⟨pos, lt_pos⟩ =>
        apply And.intro
        . by_cases c : i ∈ φ.list_noms
          . apply Or.inr
            simp only
            -- by h, we know that i > φ.list_noms[pos]
            have lt_pos_2 := (Eq.subst (Eq.symm eq_len) lt_pos)
            have hpos : i = 2 * φ.list_noms[pos] + 1 := by
                rw [h]; exact odd_is_odd lt_pos_2 lt_pos
            have : φ.list_noms[pos].letter < i.letter := by
                rw [hpos]
                change (φ.list_noms[pos].letter : ℕ) < (φ.list_noms[pos].letter : ℕ) * 2 + 1
                omega
            -- since φ.list_noms is in descending order
            --  and i ∈ φ.list_noms by assumption,
            -- then i ∈ φ.list_noms[:pos]
            apply descending_property
            apply descending_list_noms
            repeat assumption
          . exact Or.inl c
        . simp
          apply descending_ndup
          apply descending_odd_list_noms
          assumption
  
    theorem nocc_bulk_property_induction : nocc_bulk_property (h_new :: t_new) (h_old :: t_old) φ → nocc_bulk_property t_new t_old (φ[h_new//h_old]) := by
      unfold nocc_bulk_property
      intro h n i eq_i
      let m : Fin (List.length (h_new :: t_new)) := ⟨n.val+1, Nat.succ_lt_succ_iff.mpr n.2⟩
      have m_n : m.val = n.val + 1 := rfl
      have hmem : i = (h_new :: t_new)[m] := eq_i
      have ⟨l, r⟩ := h hmem
      apply And.intro
      . simp [m_n, ←or_assoc] at l
        apply Or.elim l
        . intro disj
          apply Or.inl
          apply not_imp_not.mpr (list_noms_subst (i := i) (φ := φ) (old := h_old) (new := h_new))
          simp
          apply And.intro
          . intro habs
            have l2 : h_new ∈ List.take (↑m) (h_new :: t_new) := by simp [m_n]
            rw [←habs] at r l2
            contradiction
          . rw [Or.comm]; exact disj
        . intro
          apply Or.inr
          assumption
      . simp [m_n] at r
        exact r.right

end Nominals

  lemma dbl_subst_nom {j : NOM N} {x : SVAR} (i : NOM N) (h : nom_occurs j φ = false) : φ[j//i][x//j] = φ[x//i] := by
    induction φ <;> simp [nom_occurs, nom_subst_nom, nom_subst_svar, -implication_disjunction, *] at *
    . split <;> simp [nom_subst_svar, Ne.symm h]
    repeat simp [h, *] at *

  lemma svar_svar_nom_subst {i j : NOM N} {x : SVAR} (h : x ≥ φ.new_var) : φ[x//i][j//x] = φ[j//i] := by
    induction φ <;> simp [nom_subst_svar, nom_subst_nom, subst_nom, -implication_disjunction, *] at *
    . apply Ne.symm; apply diffsvar; assumption
    . split <;> simp [subst_nom]
    . simp [new_var_geq1 h, *] at *
    . simp [Form.new_var] at h
      simp [h, *] at *
    . split
      . exfalso
        have := Ne.symm (diffsvar (new_var_geq2 h).left)
        contradiction
      . simp [new_var_geq2 h, *] at *
  
  lemma nom_subst_self {i : NOM N} : φ[i // i] = φ := by
    induction φ <;> simp [nom_subst_nom, -implication_disjunction, *] at * 
    . intro h ; apply Eq.symm; assumption

  lemma eq_new_var {i j : NOM N} : φ.new_var = (φ[i // j]).new_var := by
    induction φ <;> simp [Form.new_var, nom_subst_nom, *] at * 
    . split <;> simp [Form.new_var]



  theorem odd_nom {i : NOM TotalSet} : (Form.nom i).odd_noms = Form.nom (2 * i + 1) := by
    simp [Form.odd_noms, Form.odd_list_noms, Form.list_noms, Form.bulk_subst, nom_subst_nom, NOM_eq, NOM.hmul, NOM.add, Nat.mul_comm]

  theorem bulk_subst_impl {φ ψ : Form TotalSet} : (φ ⟶ ψ).bulk_subst l₁ l₂ = φ.bulk_subst l₁ l₂ ⟶ ψ.bulk_subst l₁ l₂ := by
    induction l₁ generalizing φ ψ l₂ with
    | nil => cases l₂ <;> rfl
    | cons h t ih =>
        cases l₂ with
        | nil => rfl
        | cons h2 t2 => simp only [Form.bulk_subst, nom_subst_nom]; exact ih

  theorem bulk_subst_box {φ : Form TotalSet} : (□φ).bulk_subst l₁ l₂ = □(φ.bulk_subst l₁ l₂) := by
    induction l₁ generalizing φ l₂ with
    | nil => cases l₂ <;> rfl
    | cons h t ih =>
        cases l₂ with
        | nil => rfl
        | cons h2 t2 => simp only [Form.bulk_subst, nom_subst_nom]; exact ih

  theorem bulk_subst_bind {φ : Form TotalSet} {x : SVAR} : (all x, φ).bulk_subst l₁ l₂ = all x, (φ.bulk_subst l₁ l₂) := by
    induction l₁ generalizing φ l₂ with
    | nil => cases l₂ <;> rfl
    | cons h t ih =>
        cases l₂ with
        | nil => rfl
        | cons h2 t2 => simp only [Form.bulk_subst, nom_subst_nom]; exact ih

  -- A structural characterisation of `odd_noms`: rename every nominal `i ↦ 2i+1`,
  -- recursing through the syntax tree.  We prove below that `bulk_subst` over any
  -- descending list that contains all of `φ`'s nominals computes exactly this map,
  -- which is what makes the homomorphism lemmas `list_noms_impl_*` go through.
  def Form.odd_map : Form TotalSet → Form TotalSet
    | .nom i    => Form.nom (2 * i + 1)
    | .impl φ ψ => φ.odd_map ⟶ ψ.odd_map
    | .box φ    => □ φ.odd_map
    | .bind x φ => all x, φ.odd_map
    | φ         => φ

  theorem bulk_subst_const {φ : Form TotalSet} (h : ∀ (i j : NOM TotalSet), φ[i // j] = φ) {L₁ L₂ : List (NOM TotalSet)} : φ.bulk_subst L₁ L₂ = φ := by
    induction L₁ generalizing L₂ with
    | nil => cases L₂ <;> rfl
    | cons a as ih =>
        cases L₂ with
        | nil => rfl
        | cons o os => rw [Form.bulk_subst, h]; exact ih

  theorem nom_bulk_noop {j : NOM TotalSet} {L₁ L₂ : List (NOM TotalSet)} (h : j ∉ L₂) : (Form.nom j).bulk_subst L₁ L₂ = Form.nom j := by
    induction L₁ generalizing L₂ with
    | nil => cases L₂ <;> rfl
    | cons a as ih =>
        cases L₂ with
        | nil => rfl
        | cons o os =>
            simp only [List.mem_cons, not_or] at h
            simp only [Form.bulk_subst, nom_subst_nom]
            rw [if_neg h.1]
            exact ih h.2

  theorem nom_bulk {i : NOM TotalSet} : ∀ {L : List (NOM TotalSet)}, i ∈ L → descending L → (Form.nom i).bulk_subst (L.map (fun j => 2 * j + 1)) L = Form.nom (2 * i + 1) := by
    intro L
    induction L with
    | nil => intro hmem _; simp at hmem
    | cons o os ih =>
        intro hmem hdesc
        rw [List.map_cons]
        by_cases hio : i = o
        · subst hio
          have hnotin : (2 * i + 1) ∉ os := by
            intro habs
            have h : i > 2 * i + 1 := hdesc.left _ habs
            change ((i.letter : ℕ) * 2 + 1 < (i.letter : ℕ)) at h
            omega
          simp only [Form.bulk_subst, nom_subst_nom, if_pos]
          exact nom_bulk_noop hnotin
        · have hios : i ∈ os := (List.mem_cons.mp hmem).resolve_left hio
          simp only [Form.bulk_subst, nom_subst_nom]
          rw [if_neg hio]
          exact ih hios hdesc.right

  theorem bulk_eq_odd_map {L : List (NOM TotalSet)} (hdesc : descending L) :
      ∀ φ : Form TotalSet, (∀ i ∈ φ.list_noms, i ∈ L) → φ.bulk_subst (L.map (fun j => 2 * j + 1)) L = φ.odd_map := by
    intro φ
    induction φ with
    | bttm => intro _; exact bulk_subst_const (fun _ _ => rfl)
    | prop p => intro _; exact bulk_subst_const (fun _ _ => rfl)
    | svar x => intro _; exact bulk_subst_const (fun _ _ => rfl)
    | nom i => intro hsub; exact nom_bulk (hsub i (by simp [Form.list_noms])) hdesc
    | impl φ ψ ihφ ihψ =>
        intro hsub
        simp only [Form.odd_map]
        have mφ : ∀ i ∈ φ.list_noms, i ∈ L := by
          intro i hi; apply hsub i
          rw [← occurs_list_noms] at hi ⊢
          simp only [nom_occurs, hi, Bool.true_or]
        have mψ : ∀ i ∈ ψ.list_noms, i ∈ L := by
          intro i hi; apply hsub i
          rw [← occurs_list_noms] at hi ⊢
          simp only [nom_occurs, hi, Bool.or_true]
        rw [bulk_subst_impl, ihφ mφ, ihψ mψ]
    | box φ ih => intro hsub; simp only [Form.odd_map]; rw [bulk_subst_box, ih hsub]
    | bind x φ ih => intro hsub; simp only [Form.odd_map]; rw [bulk_subst_bind, ih hsub]

  theorem list_noms_impl_r {φ ψ : Form TotalSet} : φ.bulk_subst φ.odd_list_noms φ.list_noms = φ.bulk_subst (φ ⟶ ψ).odd_list_noms (φ ⟶ ψ).list_noms := by
    simp only [Form.odd_list_noms]
    rw [bulk_eq_odd_map (@descending_list_noms φ) φ (fun i hi => hi),
        bulk_eq_odd_map (@descending_list_noms (φ ⟶ ψ)) φ
          (by intro i hi; rw [← occurs_list_noms] at hi ⊢; simp only [nom_occurs, hi, Bool.true_or])]

  theorem list_noms_impl_l {φ ψ : Form TotalSet} : φ.bulk_subst φ.odd_list_noms φ.list_noms = φ.bulk_subst (ψ ⟶ φ).odd_list_noms (ψ ⟶ φ).list_noms := by
    simp only [Form.odd_list_noms]
    rw [bulk_eq_odd_map (@descending_list_noms φ) φ (fun i hi => hi),
        bulk_eq_odd_map (@descending_list_noms (ψ ⟶ φ)) φ
          (by intro i hi; rw [← occurs_list_noms] at hi ⊢; simp only [nom_occurs, hi, Bool.or_true])]

  theorem odd_impl : (φ ⟶ ψ).odd_noms = φ.odd_noms ⟶ ψ.odd_noms := by
    unfold Form.odd_noms
    conv => rhs; rw [@list_noms_impl_r φ ψ, @list_noms_impl_l ψ φ]
    simp [bulk_subst_impl]

  theorem odd_bttm : (Form.bttm : Form TotalSet).odd_noms = Form.bttm := by
    simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst]

  theorem odd_box : (□φ).odd_noms = □(φ.odd_noms) := by
    show (□φ).bulk_subst (□φ).odd_list_noms (□φ).list_noms = □(φ.bulk_subst φ.odd_list_noms φ.list_noms)
    exact bulk_subst_box

  theorem odd_bind : (all x, φ).odd_noms = all x, (φ.odd_noms) := by
    show (all x, φ).bulk_subst (all x, φ).odd_list_noms (all x, φ).list_noms = all x, (φ.bulk_subst φ.odd_list_noms φ.list_noms)
    exact bulk_subst_bind

  theorem odd_conj_two {φ ψ : Form TotalSet} : (φ ⋀ ψ).odd_noms = φ.odd_noms ⋀ ψ.odd_noms := by
    simp only [Form.conj, Form.neg, odd_impl, odd_bttm]

  def List.to_odd {Γ : Set (Form TotalSet)} : List Γ → List Γ.odd_noms
    | [] => []
    | (h :: t) => ⟨h.val.odd_noms, ⟨h.val, h.2, rfl⟩⟩ :: t.to_odd

  noncomputable def List.odd_to {Γ : Set (Form TotalSet)} : List Γ.odd_noms → List Γ
    | [] => []
    | (h :: t) => ⟨h.2.choose, h.2.choose_spec.1⟩ :: t.odd_to

  theorem odd_conj (Γ : Set (Form TotalSet)) (L : List Γ) : (conjunction Γ L).odd_noms = conjunction Γ.odd_noms L.to_odd := by
    induction L with
    | nil => simp only [conjunction, List.to_odd, odd_impl, odd_bttm]
    | cons head tail ih =>
        show (head.val ⋀ conjunction Γ tail).odd_noms
            = head.val.odd_noms ⋀ conjunction Γ.odd_noms tail.to_odd
        rw [odd_conj_two, ih]

  theorem odd_conj_rev (Γ : Set (Form TotalSet)) (L' : List Γ.odd_noms) : (conjunction Γ L'.odd_to).odd_noms = conjunction Γ.odd_noms L' := by
    induction L' with
    | nil => simp only [conjunction, List.odd_to, odd_impl, odd_bttm]
    | cons head tail ih =>
        show (head.2.choose ⋀ conjunction Γ tail.odd_to).odd_noms
            = head.val ⋀ conjunction Γ.odd_noms tail
        rw [odd_conj_two, ih, head.2.choose_spec.2]
