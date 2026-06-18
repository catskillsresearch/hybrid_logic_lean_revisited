import Hybrid.Form

-- Helper simp lemmas to reduce SVAR ordering / max / addition to `Nat`,
-- so that `omega` can finish arithmetic goals. (mathlib upgrade: the old
-- `simp [SVAR.le, max, SVAR.add]` patterns no longer unfold reliably.)
theorem svar_le_letter {x y : SVAR} : (x  <=  y) = (x.letter  <=  y.letter) := rfl
theorem svar_lt_letter {x y : SVAR} : (x < y) = (x.letter < y.letter) := rfl
theorem svar_add_letter {x : SVAR} {n : Nat} : (x + n).letter = x.letter + n := rfl
theorem svar_max_letter {x y : SVAR} : (max x y).letter = max x.letter y.letter := by
  change (ite (x.letter > y.letter) x y).letter = max x.letter y.letter
  split <;> omega

theorem subst_depth {i : NOM N} {x : SVAR} {phi : Form N} : phi[i // x].depth = phi.depth := by
  induction phi <;> simp [subst_nom, Form.depth, *] at *
  <;> (split <;> simp [Form.depth, *])

theorem subst_depth' {x y : SVAR} {phi : Form N} : phi[y // x].depth = phi.depth := by
  induction phi <;> simp [subst_svar, Form.depth, *] at *
  <;> (split <;> simp [Form.depth, *])

theorem subst_depth'' {x : SVAR} {i : NOM N} {phi : Form N} : (phi[i//x]).depth < (ex x, phi).depth := by
  apply Nat.lt_of_le_of_lt
  apply Nat.le_of_eq
  apply subst_depth
  apply ex_depth

theorem subst_depth_bind {x : SVAR} {i : NOM N} {phi : Form N} : (phi[i//x]).depth < (all x, phi).depth := by
  apply Nat.lt_of_le_of_lt
  apply Nat.le_of_eq
  apply subst_depth
  apply sub_depth_bind

theorem iff_subst_svar {y x : SVAR} : (phi  <->  psi)[y // x] = (phi[y//x]  <->  psi[y//x]) := by
  simp [subst_svar]

section Variables
  lemma svar_eq {psi chi : SVAR} : psi = chi  <->  psi.1 = chi.1 := by
    have l1 : psi = <psi.letter> := by simp
    have l2 : chi = <chi.letter> := by simp
    rw [l1, l2]
    simp

  lemma new_var_neg : (~psi).new_var = psi.new_var := by
    simp [Form.new_var, max, -implication_disjunction]
    rw [ <- svar_eq]
    intro _
    simp [*]
  
  lemma subst_neg : is_substable (~psi) y x  <->  is_substable psi y x := by
    simp [is_substable]

  lemma new_var_gt      : occurs x phi  ->  x < phi.new_var   := by
    induction phi with
    | svar y          =>
        simp [occurs, Form.new_var, -implication_disjunction]
        intro h
        rw [h]
        exact Nat.lt_succ_self y.letter
    | impl psi chi ih1 ih2 =>
        simp only [occurs, Form.new_var, Bool.or_eq_true, max]
        intro h
        apply Or.elim h
        . intro ha
          clear ih2 h
          have ih1 := ih1 ha
          by_cases hc : (Form.new_var psi).letter > (Form.new_var chi).letter
          . simp [hc]
            assumption
          . simp [hc]
            simp at hc 
            exact Nat.lt_of_lt_of_le ih1 hc
        . intro hb
          clear ih1 h
          have ih2 := ih2 hb
          by_cases hc : (Form.new_var psi).letter > (Form.new_var chi).letter
          . simp [hc]
            simp at hc
            exact Nat.lt_trans ih2 hc
          . simp [hc]
            assumption
    | box psi ih      =>
        simp only [occurs, Form.new_var]
        assumption
    | bind y psi ih   =>
        simp only [occurs, Form.new_var, max]
        intro h
        have ih := ih h
        by_cases hc : (y + 1).letter > (Form.new_var psi).letter
        . simp [hc]
          simp at hc
          exact Nat.lt_trans ih hc
        . simp [hc]
          assumption
    | _ => simp [occurs]

  lemma new_var_is_new  : occurs (phi.new_var) phi = false := by
    rw [ <- Bool.eq_false_eq_not_eq_true]
    intro h
    have a := new_var_gt h
    have b := Nat.lt_irrefl phi.new_var.letter
    exact b a
  
  lemma ge_new_var_is_new (h : x  >=  phi.new_var) : occurs x phi = false := by
    rw [ <- Bool.eq_false_eq_not_eq_true]
    intro habs
    have := new_var_gt habs
    have a := Nat.lt_of_le_of_lt h this
    have b := Nat.lt_irrefl phi.new_var.letter
    exact b a
  
  lemma ge_new_var_subst_nom {i : NOM N} {y : SVAR} : phi.new_var  >=  phi[i // y].new_var := by
    induction phi with
    | svar z =>
        simp only [subst_nom]
        split <;> simp [Form.new_var, svar_le_letter, svar_add_letter]
    | impl psi chi ih1 ih2 =>
        simp only [subst_nom, Form.new_var, ge_iff_le, svar_le_letter, svar_max_letter] at *
        omega
    | bind z psi ih =>
        simp only [subst_nom]
        split <;>
          simp only [Form.new_var, ge_iff_le, svar_le_letter, svar_max_letter, svar_add_letter] at * <;>
          omega
    | box psi ih =>
        simpa only [subst_nom, Form.new_var, ge_iff_le, svar_le_letter] using ih
    | _ => simp [Form.new_var, subst_nom, svar_le_letter]

lemma new_var_geq1 : x  >=  (phi  -->  psi).new_var  ->  (x  >=  phi.new_var  /\  x  >=  psi.new_var) := by
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

lemma new_var_geq2 : x  >=  (all y, psi).new_var  ->  (x  >=  (y+1)  /\  x  >=  psi.new_var) := by
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

lemma new_var_geq3 : x  >=  ([]  phi).new_var  ->  (x  >=  phi.new_var) := by simp [Form.new_var]

lemma new_var_subst {phi : Form N} {i : NOM N} {x y : SVAR} (h : x  >=  phi.new_var) : is_substable (phi[y//i]) x y := by
  induction phi with
  | nom  j  =>
      simp [nom_subst_svar]
      split <;> simp [is_substable]
  | bind z psi ih =>
      simp only [nom_subst_svar, Form.new_var, max, is_substable, beq_iff_eq, ite_eq_left_iff,
          bne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
          Bool.not_eq_false, Bool.and_eq_true] at h  |- 
      intro _
      by_cases hc : (z + 1).letter > (Form.new_var psi).letter
      . simp [hc] at h
        simp only [gt_iff_lt, ge_iff_le] at hc ih
        have ih := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
        have ne := Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact <ne, ih>
      . simp [hc] at h
        simp only [gt_iff_lt, not_lt, ge_iff_le] at hc ih 
        have ih := ih h
        have ne := Nat.ne_of_lt (Nat.le_trans (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) hc) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact <ne, ih>
  | impl psi chi ih1 ih2 =>
      simp [Form.new_var, max, is_substable, nom_subst_svar] at h  |- 
      by_cases hc : (Form.new_var chi).letter < (Form.new_var psi).letter
      . simp [hc] at h
        have := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
        exact <ih1 h, ih2 this>
      . simp [hc] at h
        simp at hc
        have := Nat.le_trans hc h
        exact <ih1 this, ih2 h>
  | box psi ih         =>
      simp [Form.new_var, is_substable, nom_subst_svar] at h  |- 
      exact ih h
  | _  =>
      simp [nom_subst_svar, is_substable]

lemma new_var_subst'' {phi : Form N} {x y : SVAR} (h : x  >=  phi.new_var) : is_substable phi x y := by
  induction phi with
  | bind z psi ih =>
      simp only [Form.new_var, max, is_substable, beq_iff_eq, ite_eq_left_iff,
          bne, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
          Bool.not_eq_false, Bool.and_eq_true] at h  |- 
      intro _
      by_cases hc : (z + 1).letter > (Form.new_var psi).letter
      . simp [hc] at h
        simp only [gt_iff_lt, ge_iff_le] at hc ih
        have ih := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
        have ne := Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact <ne, ih>
      . simp [hc] at h
        simp only [gt_iff_lt, not_lt, ge_iff_le] at hc ih 
        have ih := ih h
        have ne := Nat.ne_of_lt (Nat.le_trans (Nat.lt_of_lt_of_le (Nat.lt_succ_self z.letter) hc) h)
        rw [of_eq_true (eq_self z), of_eq_true (eq_self x), SVAR.mk.injEq]
        exact <ne, ih>
  | impl psi chi ih1 ih2 =>
      simp [Form.new_var, max, is_substable, nom_subst_svar] at h  |- 
      by_cases hc : (Form.new_var chi).letter < (Form.new_var psi).letter
      . simp [hc] at h
        have := Nat.le_of_lt (Nat.lt_of_lt_of_le hc h)
        exact <ih1 h, ih2 this>
      . simp [hc] at h
        simp at hc
        have := Nat.le_trans hc h
        exact <ih1 this, ih2 h>
  | box psi ih         =>
      simp [Form.new_var, is_substable, nom_subst_svar] at h  |- 
      exact ih h
  | _  =>
      simp [is_substable]

lemma scz {phi : Form N} (i : NOM N) (h : x  >=  phi.new_var) (hy : y  !=  x) : (is_free y phi)  <->  (is_free y (phi[x // i])) := by
  induction phi with
  | nom a       =>
      simp [nom_subst_svar] ; split <;> simp [is_free, hy]
  | bind z psi ih =>
      simp [is_free, nom_subst_svar, -implication_disjunction]
      simp [new_var_geq2 h] at ih
      simp [nom_subst_svar, is_free, ih]
  | impl psi chi ih1 ih2 =>
      have <ih1_cond, ih2_cond> := new_var_geq1 h
      simp [ih1_cond, ih2_cond] at ih1 ih2
      simp [is_free, nom_subst_svar, ih1, ih2]
  | box psi ih         =>
      simp [Form.new_var] at h
      simp [h] at ih
      simp [is_free, nom_subst_svar, ih]
  | _ => simp [is_free, nom_subst_svar]

lemma new_var_subst' {phi : Form N} (i : NOM N) {x y : SVAR} (h1 : is_substable phi v y) (h2 : x  >=  phi.new_var) (h3 : y  !=  x) : is_substable (phi[x//i]) v y := by
  induction phi with
  | nom  a      => simp [nom_subst_svar]; split <;> simp [is_substable]
  | bind z psi ih =>
      have xge := (new_var_geq2 h2).right
      have hsc := @scz N x y psi i xge h3
      have heq : is_free y (psi[x//i]) = is_free y psi := by
        cases h' : is_free y psi <;> cases h'' : is_free y (psi[x//i]) <;> simp_all
      simp only [nom_subst_svar]
      simp [is_substable] at h1  |- 
      rcases h1 with hf | <hzv, hsub>
      * left; rw [heq]; exact hf
      * right; exact <hzv, ih hsub xge>
  | impl psi chi ih1 ih2  =>
      simp [is_substable] at h1
      simp [Form.new_var] at h2
      have <ih1_cond, ih2_cond> := new_var_geq1 h2 
      simp [h1, h2, ih1_cond, ih2_cond] at ih1 ih2
      simp [is_substable, nom_subst_svar, ih1, ih2]
  | box psi ih          =>
      simp [is_substable] at h1
      simp [Form.new_var] at h2
      simp [h1, h2] at ih
      simp [is_substable, nom_subst_svar, ih]
  | _       =>  simp [nom_subst_svar, h1]

lemma nom_subst_trans (i : NOM N) (x y : SVAR) (h : y  >=  phi.new_var) : phi[y // i][x // y] = phi[x // i] := by
  induction phi with
  | bttm => simp [nom_subst_svar, subst_svar]
  | prop => simp [nom_subst_svar, subst_svar]
  | nom _ =>
    simp [nom_subst_svar]
    split <;> simp [subst_svar]
  | svar z =>
    have nocc := ge_new_var_is_new h
    simp only [nom_subst_svar, subst_svar]
    split <;> simp_all [occurs]
  | bind z psi ih =>
    simp only [nom_subst_svar, subst_svar]
    have := new_var_geq2 h
    by_cases hc : y = z
    . exfalso
      have := this.left
      simp [hc] at this
      have := Nat.ne_of_lt (Nat.lt_succ_of_le this)
      contradiction
    . simp [nom_subst_svar, ih this.right, hc]
  | impl psi chi ih1 ih2 =>
      simp [nom_subst_svar, subst_svar, ih1, ih2, new_var_geq1 h]
  | box psi ih         =>
      simp [Form.new_var] at h
      simp [nom_subst_svar, subst_svar, ih, h]

  lemma subst_nom_noop {phi : Form N} {i : NOM N} {y : SVAR} (h : occurs y phi = false) : phi[i // y] = phi := by
    induction phi with
    | svar z => simp only [subst_nom]; split <;> simp_all [occurs]
    | impl a b iha ihb =>
        simp only [occurs, Bool.or_eq_false_iff] at h
        simp only [subst_nom, iha h.1, ihb h.2]
    | box a ih => simp only [occurs] at h; simp only [subst_nom, ih h]
    | bind w a ih => simp only [occurs] at h; simp only [subst_nom]; split <;> simp_all [ih h]
    | _ => rfl

  -- Substituting `x` by a fresh `y` and then renaming `y` to a nominal `i` is the
  -- same as directly substituting `x` by `i`.  Freshness of `y` (it exceeds the
  -- new-variable bound, so it differs from every free *and bound* variable of `phi`)
  -- is what prevents capture.
  lemma rename_svar_nom {phi : Form N} (i : NOM N) (x y : SVAR) (h : y  >=  phi.new_var) : phi[y // x][i // y] = phi[i // x] := by
    induction phi with
    | bttm => simp [subst_svar, subst_nom]
    | prop => simp [subst_svar, subst_nom]
    | nom _ => simp [subst_svar, subst_nom]
    | svar z =>
        have hyz : y  !=  z := by
          have := ge_new_var_is_new h; simpa [occurs] using this
        by_cases hxz : x = z
        * subst hxz; simp [subst_svar, subst_nom]
        * simp [subst_svar, subst_nom, hxz, hyz]
    | impl psi chi ih1 ih2 =>
        simp [subst_svar, subst_nom, ih1 (new_var_geq1 h).1, ih2 (new_var_geq1 h).2]
    | box psi ih =>
        simp only [Form.new_var] at h
        simp [subst_svar, subst_nom, ih h]
    | bind z psi ih =>
        have hb := new_var_geq2 h
        have hyz : y  !=  z := by
          intro habs; have hle := hb.left; rw [habs] at hle
          simp only [svar_le_letter, svar_add_letter] at hle; omega
        by_cases hxz : x = z
        * subst hxz
          have hnoop : psi[i // y] = psi := subst_nom_noop (ge_new_var_is_new hb.right)
          simp [subst_svar, subst_nom, hyz, hnoop]
        * simp [subst_svar, subst_nom, hxz, hyz, ih hb.right]

  lemma ge_new_var_subst_helpr {i : NOM N} {x : SVAR} (h : y  >=  Form.new_var (chi --> psi)) : y  >=  Form.new_var (chi --> psi[i//x] --> False) := by
    simp [Form.new_var, max]
    split <;> split
    . exact (new_var_geq1 h).left
    . apply Nat.le_trans
      apply ge_new_var_subst_nom
      exact (new_var_geq1 h).right
    . exact (new_var_geq1 h).left
    . simp [svar_le_letter]

  lemma notfreeset {Gamma : Set (Form N)} (L : List Gamma) (hyp : forall  psi : Gamma, is_free x psi.1 = false) : is_free x (conjunction Gamma L) = false := by
    induction L with
    | nil         =>
        simp [conjunction, is_free]
    | cons hd tl ih =>
        have hhd := hyp hd
        simp [conjunction, is_free, hhd, ih]

  lemma notfree_after_subst {phi : Form N} {x y : SVAR} (h : x  !=  y) : is_free x (phi[y // x]) = false := by
    induction phi with
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

  lemma notocc_beforeafter_subst {phi : Form N} {x y : SVAR} (h : occurs x phi = false) : occurs x (phi[y // x]) = false := by
    induction phi with
    | svar z   =>
        by_cases xz : x = z
        <;> simp [subst_svar, if_pos xz, xz, occurs, h] at *
    | impl _ _ ih1 ih2 =>
        simp [subst_svar, occurs, not_or, ih1, ih2, -implication_disjunction] at *
        exact <ih1 h.left, ih2 h.right> 
    | box _ ih    =>
        simp [subst_svar, occurs, ih, -implication_disjunction] at *
        exact ih h
    | bind z psi ih =>
        by_cases xz : x = z
        . simp [subst_svar, xz, occurs] at *
          exact h
        . simp [subst_svar, if_neg xz, occurs, ih, xz, h, -implication_disjunction] at *
    | _        => simp [subst_svar, occurs]

  lemma notoccursbind : occurs x phi = false  ->  occurs x (all v, phi) = false := by
    simp [occurs]

  lemma notoccurs_notfree : (occurs x phi = false)  ->  (is_free x phi = false) := by
    induction phi with
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

  lemma preserve_notfree {phi : Form N} (x v : SVAR) : (is_free x phi = false)  ->  (is_free x (all v, phi) = false) := by
    intro h
    simp only [is_free, h, Bool.and_false]

  lemma subst_notfree_var {phi : Form N} {x y : SVAR} (h : is_free x phi = false) : (phi[y // x] = phi)  /\  (occurs x phi = false  ->  is_substable phi y x) := by
    induction phi with
    | svar z =>
        by_cases heq : x = z
        . simp [is_free, heq] at h
        . simp [subst_svar, heq, occurs, is_substable]
    | impl psi chi ih1 ih2 =>
        simp only [is_free, Bool.or_eq_false_eq_eq_false_and_eq_false] at h 
        apply And.intro
        . simp [subst_svar, h, ih1, ih2]
        . intro nocc
          simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at nocc 
          simp [is_substable, h, nocc, ih1, ih2]
    | box psi ih  =>
        rw [is_free] at h
        apply And.intro
        . simp [subst_svar, ih, h]
        . intro nocc
          rw [occurs] at nocc
          simp [is_substable, ih, nocc, h]
    | bind z psi ih =>
        apply And.intro
        . by_cases heq : x = z
          . rw [ <- heq, subst_svar, if_pos (Eq.refl x)]
          . simp only [is_free, bne, Bool.and_eq_false_eq_eq_false_or_eq_false, Bool.not_eq_false', beq_iff_eq,
            Ne.symm heq, false_or] at h 
            simp [subst_svar, heq, ih, h]
        . intro nocc
          rw [occurs] at nocc
          simp [is_substable, notoccurs_notfree, nocc]
    | _   =>
        simp [subst_svar, is_substable]

    lemma rereplacement (phi : Form N) (x y : SVAR) (h1 : occurs y phi = false) (h2 : is_substable phi y x) : (is_substable (phi[y // x]) x y)  /\  phi[y // x][x // y] = phi := by
      induction phi with
      | svar z =>
          simp [occurs] at h1
          by_cases xz : x = z
          repeat simp [subst_svar, xz, h1, is_substable]
      | impl psi chi ih1 ih2 =>
          simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false] at h1 
          simp only [is_substable, Bool.and_eq_true] at h2
          simp [subst_svar, ih1, ih2, h1, h2, is_substable]
      | box psi ih =>
          simp only [occurs] at h1
          simp only [is_substable] at h2
          simp [subst_svar, ih, h1, h2, is_substable]
      | bind z psi ih =>
          by_cases yz : y = z
          . rw [ <- yz]
            rw [ <- yz] at h1

            simp only [is_substable, beq_iff_eq,  <- yz, bne_self_eq_false, Bool.false_and, ite_eq_left_iff,
              Bool.not_eq_false, implication_disjunction, Bool.not_eq_true, or_false] at h2 
            rw [or_iff_left (show not (false = true) by decide)] at h2
            have h2 := @preserve_notfree N psi x y h2
            simp [subst_notfree_var, h2]

            have := @subst_notfree_var N (all y, psi) y x (notoccurs_notfree h1)
            simp [@subst_notfree_var N (all y, psi) y x, notoccurs_notfree, h1]
          . by_cases xz : x = z
            . have : is_free x (all x, psi) = false := by simp [is_free]
              rw [ <- xz] at h1
              simp [ <- xz, subst_notfree_var, this, notoccurs_notfree, h1]
            . simp only [occurs] at h1
              simp [subst_svar, xz, yz]
              by_cases xfree : is_free x psi
              . simp [is_substable, xfree, Ne.symm yz, bne] at h2
                simp [ih, h1, h2, is_substable, bne, Ne.symm xz]
              . rw [show (not is_free x psi = true  <->  is_free x psi = false) by simp] at xfree
                simp [subst_notfree_var, xfree, is_substable, (notoccurs_notfree h1)]
      | _     =>
          apply And.intro
          repeat rfl
  
  lemma subst_self_is_self (phi : Form N) (x : SVAR) : phi [x // x] = phi := by
    induction phi with
    | svar y   =>
        by_cases xy : x = y
        . rw [subst_svar, if_pos xy, xy]
        . rw [subst_svar, if_neg xy]
    | impl phi psi ih1 ih2 =>
        rw [subst_svar, ih1, ih2]
    | box  phi ih  =>
        rw [subst_svar, ih]
    | bind y phi ih =>
        by_cases xy : x = y
        . rw [subst_svar, if_pos xy]
        . rw [subst_svar, if_neg xy, ih]
    | _        => rfl

  lemma pos_subst {m : Nat} {i : NOM N} {v : SVAR} : (iterate_pos m (v /\ phi))[i//v] = iterate_pos m (i /\ phi[i//v]) := by
    induction m with
    | zero =>
        simp [iterate_pos, iterate_pos.loop, subst_nom]
    | succ n ih =>
        simp [iterate_pos, iterate_pos.loop, subst_nom] at ih  |- 
        rw [ih]

  lemma nec_subst {m : Nat} {i : NOM N} {v : SVAR} : (iterate_nec m (v --> phi))[i//v] = iterate_nec m (i --> phi[i//v]) := by
    induction m with
    | zero =>
        simp [iterate_nec, iterate_nec.loop, subst_nom]
    | succ n ih =>
        simp [iterate_nec, iterate_nec.loop, subst_nom] at ih  |- 
        rw [ih]

  theorem Form.new_var_properties (phi : Form N) : exists  x : SVAR, x  >=  phi.new_var  /\  occurs x phi = false  /\  (forall  y : SVAR, is_substable phi x y) := by
    exists phi.new_var
    refine <?_, new_var_is_new, fun y => ?_>
    * simp [ge_iff_le, svar_le_letter]
    * apply new_var_subst''
      simp [ge_iff_le, svar_le_letter]
end Variables

section Nominals
  lemma nom_svar_subst_symm {v x y : SVAR} {i : NOM N} (h : y  !=  x) : phi[x//i][v//y] = phi[v//y][x//i] := by
    induction phi <;> simp [subst_svar, nom_subst_svar, *] at *
    . split <;> simp[nom_subst_svar]
    . split <;> simp [subst_svar, h]
    . split <;> simp [nom_subst_svar]

  lemma nom_nom_subst_symm {x y : SVAR} {j i : NOM N} (h1 : j  !=  i) (h2 : y  !=  x) : phi[x//i][j//y] = phi[j//y][x//i] := by
    induction phi <;> simp [nom_subst_svar, subst_nom, *] at *
    . split <;> simp [nom_subst_svar, *]
    . split <;> simp [subst_nom, *]
    . split <;> simp [nom_subst_svar]

  lemma subst_collect_all {x y : SVAR} {i : NOM N} : phi[i//y][x//i] = phi[x//i][x//y] := by
    induction phi <;> simp [subst_svar, subst_nom, nom_subst_svar, *] at *
    . split <;> simp [nom_subst_svar]
    . split <;> simp [subst_svar]
    . split <;> simp [nom_subst_svar, *]

  theorem nom_subst_nocc (h : nom_occurs i chi = false) (y : SVAR) : chi[y // i] = chi := by
    induction chi <;> simp [nom_occurs, nom_subst_svar, *, -implication_disjunction] at *
    . intro; apply h; apply Eq.symm; assumption
    . simp [h] at *
      apply And.intro <;> assumption

  theorem subst_collect_all_nocc (h : nom_occurs i chi = false) (x y : SVAR) : chi[i // x][y // i] = chi[y // x] := by
    rw [subst_collect_all, nom_subst_nocc h y]

  lemma nom_svar_rereplacement {phi : Form N} {i : NOM N} (h : x  >=  phi.new_var) : phi[x // i][i // x] = phi := by
    induction phi <;> simp [nom_subst_svar, subst_nom] 
    . have := ge_new_var_is_new h
      simp [occurs] at this
      exact this
    . split <;> simp [subst_nom, *]
    . simp [new_var_geq1 h, *]
    . simp [new_var_geq3 h, *]
    . split
      . next h2 =>
          have l1 := (new_var_geq2 h).left
          rw [ <- h2] at l1
          have l2 := Nat.le_succ x
          have := Nat.le_antisymm l1 l2
          simp only [svar_add_letter] at this
          omega
      . simp [new_var_geq2 h, *]

  lemma pos_subst_nom {m : Nat} {i : NOM N} {v x : SVAR} : (iterate_pos m (v /\ phi))[x//i] = iterate_pos m (Form.svar v /\ phi[x//i]) := by
    induction m with
    | zero =>
        simp [iterate_pos, iterate_pos.loop, nom_subst_svar]
    | succ n ih =>
        simp [iterate_pos, iterate_pos.loop, nom_subst_svar] at ih  |- 
        rw [ih]

  lemma nec_subst_nom {m : Nat} {i : NOM N} {v x : SVAR} : (iterate_nec m (v --> phi))[x//i] = iterate_nec m (Form.svar v --> phi[x//i]) := by
    induction m with
    | zero =>
        simp [iterate_nec, iterate_nec.loop, nom_subst_svar]
    | succ n ih =>
        simp [iterate_nec, iterate_nec.loop, nom_subst_svar] at ih  |- 
        rw [ih]

  lemma diffsvar {v x : SVAR} (h : x  >=  v+1) : v  !=  x := by
    simp; intro abs; exact (Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self v.letter) h)) (SVAR.mk.inj abs)  

  theorem is_free_nom_subst_nom {psi : Form N} {v : SVAR} {new old : NOM N} :
      is_free v (psi[new // old]) = is_free v psi := by
    induction psi generalizing v with
    | nom a =>
        by_cases ha : a = old <;> simp [nom_subst_nom, is_free, ha]
    | bind y psi ih =>
        by_cases hy : y = v
        * simp [nom_subst_nom, is_free, hy]
        * simp [nom_subst_nom, is_free, hy, ih]
    | impl a b iha ihb => simp [nom_subst_nom, is_free, iha, ihb]
    | box a ih => simp [nom_subst_nom, is_free, ih]
    | _ => simp [nom_subst_nom, is_free]

  theorem is_substable_nom_subst_nom {psi : Form N} {s v : SVAR} {new old : NOM N} :
      is_substable (psi[new // old]) s v = is_substable psi s v := by
    induction psi generalizing s v with
    | nom a =>
        by_cases ha : a = old <;> simp [nom_subst_nom, is_substable, ha]
    | bind y psi ih =>
        simp only [nom_subst_nom, is_substable, is_free_nom_subst_nom]
        by_cases hy : y = v
        * by_cases hf : is_free v psi <;> simp [hy, hf, ih]
        * by_cases hf : is_free v psi <;> simp [hy, hf, ih]
    | impl a b iha ihb => simp [nom_subst_nom, is_substable, iha, ihb]
    | box a ih => simp [nom_subst_nom, is_substable, ih]
    | _ => simp [nom_subst_nom, is_substable]

  theorem nom_svar_subst_comm_nom {psi : Form N} {new old : NOM N} {s v : SVAR} :
      (psi[s // v])[new // old] = (psi[new // old])[s // v] := by
    induction psi generalizing s v with
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

  theorem subst_nom_nom_subst {psi : Form N} {s : NOM N} {v : SVAR} {new old : NOM N} :
      (psi[s // v])[new // old] = (psi[new // old])[(if s = old then new else s) // v] := by
    induction psi generalizing s v with
    | svar a =>
        by_cases ha : v = a <;> by_cases hs : s = old <;> simp [subst_nom, nom_subst_nom, ha, hs, reduceIte]
    | nom a =>
        by_cases ha : a = old <;> by_cases hs : s = old <;> simp [subst_nom, nom_subst_nom, ha, hs, reduceIte]
    | impl a b iha ihb => simp [subst_nom, nom_subst_nom, iha, ihb]
    | box a ih => simp [subst_nom, nom_subst_nom, ih]
    | bind z a ih =>
        simp [subst_nom, nom_subst_nom, reduceIte]
        split_ifs <;> simp [subst_nom, nom_subst_nom, ih, *]
    | _ => simp [subst_nom, nom_subst_nom]

  lemma nom_subst_box {psi : Form N} {new old : NOM N} :
      nom_subst_nom ([]  psi) new old = []  (nom_subst_nom psi new old) := by
    simp [nom_subst_nom]

  lemma nom_subst_diamond {psi : Form N} {new old : NOM N} :
      nom_subst_nom (<>  psi) new old = <>  (nom_subst_nom psi new old) := by
    simp [Form.diamond, nom_subst_nom, nom_subst_box]

  theorem nom_subst_iterate_pos {psi : Form N} {new old : NOM N} {m : Nat} :
      nom_subst_nom (iterate_pos m psi) new old = iterate_pos m (nom_subst_nom psi new old) := by
    induction m generalizing psi with
    | zero => rfl
    | succ k ih =>
        conv_lhs => rw [iterate_pos, iterate_pos.loop]
        conv_rhs => rw [iterate_pos, iterate_pos.loop]
        rw [nom_subst_diamond]
        simpa using ih

  theorem nom_subst_iterate_nec {psi : Form N} {new old : NOM N} {n : Nat} :
      nom_subst_nom (iterate_nec n psi) new old = iterate_nec n (nom_subst_nom psi new old) := by
    induction n generalizing psi with
    | zero => rfl
    | succ k ih =>
        conv_lhs => rw [iterate_nec, iterate_nec.loop]
        conv_rhs => rw [iterate_nec, iterate_nec.loop]
        rw [nom_subst_box]
        simpa using ih

  lemma nom_subst_conj_svar {phi : Form N} {new old : NOM N} (v : SVAR) :
      nom_subst_nom (v  /\  phi) new old = v  /\  nom_subst_nom phi new old := by
    simp [Form.conj, Form.neg, Form.impl, nom_subst_nom]

  lemma nom_subst_imp_svar {phi : Form N} {new old : NOM N} (v : SVAR) :
      nom_subst_nom (v  -->  phi) new old = v  -->  nom_subst_nom phi new old := by
    simp only [Form.impl, nom_subst_nom]

  lemma nom_subst_iterate_pos_svar {phi : Form N} {new old : NOM N} (m : Nat) (v : SVAR) :
      nom_subst_nom (iterate_pos m (v  /\  phi)) new old =
        iterate_pos m (v  /\  nom_subst_nom phi new old) := by
    induction m generalizing phi with
    | zero => simp [iterate_pos, iterate_pos.loop, Form.conj, Form.neg, Form.impl, nom_subst_nom]
    | succ k ih =>
        conv_lhs => rw [iterate_pos, iterate_pos.loop]
        conv_rhs => rw [iterate_pos, iterate_pos.loop]
        rw [nom_subst_diamond]
        simpa using ih

  lemma nom_subst_iterate_nec_svar {phi : Form N} {new old : NOM N} (n : Nat) (v : SVAR) :
      nom_subst_nom (iterate_nec n (v  -->  phi)) new old =
        iterate_nec n (v  -->  nom_subst_nom phi new old) := by
    induction n generalizing phi with
    | zero => simp [iterate_nec, iterate_nec.loop, Form.impl, nom_subst_nom]
    | succ k ih =>
        conv_lhs => rw [iterate_nec, iterate_nec.loop]
        conv_rhs => rw [iterate_nec, iterate_nec.loop]
        rw [nom_subst_box]
        simpa using ih

  theorem nom_subst_ax_nom {phi : Form N} {v : SVAR} {m n : Nat} {new old : NOM N} :
      (all v, (iterate_pos m (v  /\  phi)  -->  iterate_nec n (v  -->  phi)))[new // old] =
        all v, (iterate_pos m (v  /\  phi[new // old])  -->  iterate_nec n (v  -->  phi[new // old])) := by
    simp only [nom_subst_nom, nom_subst_iterate_pos_svar, nom_subst_iterate_nec_svar]

  theorem nom_subst_ax_q2_nom {phi : Form N} {v : SVAR} {s new old : NOM N} :
      ((all v, phi)  -->  phi[s // v])[new // old] =
        (all v, phi[new // old])  -->  (phi[new // old])[(if s = old then new else s) // v] := by
    simp only [nom_subst_nom, subst_nom_nom_subst]

  section New_NOM
  lemma new_nom_gt      : nom_occurs i phi  ->  i.letter < phi.new_nom.letter   := by
    induction phi with
    | nom i          =>
        simp [nom_occurs, Form.new_nom, -implication_disjunction]
        intro h
        rw [h]
        exact Nat.lt_succ_self i.letter
    | impl psi chi ih1 ih2 =>
        simp only [nom_occurs, Form.new_nom, Bool.or_eq_true, max]
        intro h
        apply Or.elim h
        . intro ha
          clear ih2 h
          have ih1 := ih1 ha
          by_cases hc : (Form.new_nom psi).letter > (Form.new_nom chi).letter
          . simp [hc]
            assumption
          . simp [hc]
            simp at hc 
            exact Nat.lt_of_lt_of_le ih1 hc
        . intro hb
          clear ih1 h
          have ih2 := ih2 hb
          by_cases hc : (Form.new_nom psi).letter > (Form.new_nom chi).letter
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

  lemma new_nom_is_nom  : nom_occurs (phi.new_nom) phi = false := by
    rw [ <- Bool.eq_false_eq_not_eq_true]
    intro h
    have a := new_nom_gt h
    have b := Nat.lt_irrefl phi.new_nom.letter
    exact b a
  
  lemma ge_new_nom_is_new (h : x  >=  phi.new_nom) : nom_occurs x phi = false := by
    rw [ <- Bool.eq_false_eq_not_eq_true]
    intro habs
    have := new_nom_gt habs
    have a := Nat.lt_of_le_of_lt h this
    have b := Nat.lt_irrefl phi.new_nom.letter
    exact b a
  end New_NOM

-- just remove this definition, it is completely redundant...
  def descending (l : List (NOM N)) : Prop :=
    match l with
    | []        =>    True
    | h :: t    =>    (forall  i  in  t, h > i)  /\  descending t

  def descending' (l : List (NOM N)) : Prop := List.IsChain GT.gt l

  theorem eq_len {phi : Form TotalSet} : phi.list_noms.length = phi.odd_list_noms.length := by simp [Form.odd_list_noms]

  theorem odd_is_odd {phi : Form TotalSet} (h1 : n < phi.list_noms.length) (h2 : n < phi.odd_list_noms.length) : phi.odd_list_noms.get <n, h2> = 2 * phi.list_noms.get <n, h1> + 1 := by
    simp [Form.odd_list_noms, Form.list_noms]

  theorem descending_equiv (l : List (NOM N)) : descending l  <->  descending' l := by
    induction l with
    | nil         =>  simp [descending, descending']
    | cons h t ih =>
        simp only [descending]
        rw [ih]
        simp only [descending', List.isChain_iff_pairwise, List.pairwise_cons]

  theorem descending_property (desc : descending l) (h0 : pos < l.length) (h1 : i  in  l) (h2 : i > l[pos]) : i  in  l.take pos := by
    match l with
    | []     => simp at h1
    | h :: t =>
        simp at h0 h1
        cases pos with
        | zero =>
            simp at h2  |- 
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
              have h2_new : i > t[pos] := by simp at h2  |- ; simp [h2]
              exact descending_property desc_new h0_new h1_new h2_new

  theorem descending_ndup (desc : descending l) (h0 : pos < l.length) (h1 : i = l[pos]) : not i  in  l.take pos := by
    rw [descending_equiv, descending', List.isChain_iff_pairwise, List.pairwise_iff_getElem] at desc
    intro habs
    rw [List.mem_iff_getElem] at habs
    obtain <k, hk, hik> := habs
    rw [List.length_take] at hk
    have hkpos : k < pos := lt_of_lt_of_le hk (Nat.min_le_left _ _)
    have hklen : k < l.length := lt_of_lt_of_le hk (Nat.min_le_right _ _)
    rw [List.getElem_take] at hik
    have hgt := desc k pos hklen h0 hkpos
    rw [hik, h1] at hgt
    apply Nat.lt_irrefl l[pos].letter
    exact hgt

  theorem descending_list_noms {phi : Form TotalSet} : descending phi.list_noms := by
    rw [descending_equiv, descending']
    exact list_noms_chain'
  
  theorem descending_odd_list_noms {phi : Form TotalSet} : descending phi.odd_list_noms := by
    have dln := @descending_list_noms phi
    have : forall  a b : NOM TotalSet, (2 * b + 1 < 2 * a + 1)  <->  (b < a) := by
      intro a b
      change ((b.letter : Nat) * 2 + 1 < (a.letter : Nat) * 2 + 1)  <->  ((b.letter : Nat) < (a.letter : Nat))
      omega
    have := @List.Pairwise.iff (NOM TotalSet) (fun a b => 2 * b + 1 < 2 * a + 1) (fun a b => b < a) this
    simp only [Form.odd_list_noms, descending_equiv, descending', List.isChain_iff_pairwise, List.pairwise_map, GT.gt, this] at dln  |- 
    assumption

  theorem occurs_list_noms : nom_occurs i phi  <->  i  in  phi.list_noms := by
    induction phi with
    | impl phi psi ih1 ih2 =>
        simp only [Form.list_noms, nom_occurs, Bool.or_eq_true, ih1, ih2, List.mem_dedup,
          List.mem_merge]
    | box _ ih    => exact ih
    | bind _ _ ih => exact ih
    | _        => simp [Form.list_noms, nom_occurs]

  /-- After substituting a fresh state variable for a nominal, no new nominals appear and the
      replaced nominal disappears from the inventory. -/
  theorem list_noms_nom_subst_svar {x : SVAR} {old : NOM N} (hx : x  >=  phi.new_var) :
      forall  {k : NOM N}, k  in  (phi[x // old]).list_noms  ->  k  in  phi.list_noms  /\  k  !=  old := by
    intro k hk
    induction phi generalizing x with
    | nom a =>
        by_cases heq : a = old
        * subst heq
          simp [nom_subst_svar, Form.list_noms] at hk
        * simp [nom_subst_svar, Form.list_noms, heq] at hk
          subst hk
          exact <List.mem_singleton.mpr rfl, heq>
    | impl psi chi ih1 ih2 =>
        have hx1 := (new_var_geq1 hx).1
        have hx2 := (new_var_geq1 hx).2
        simp only [nom_subst_svar, Form.list_noms, List.mem_dedup, List.mem_merge] at hk
        rcases hk with h | h
        * rcases ih1 hx1 h with <hk', hne>
          exact <by
            rw [Form.list_noms, List.mem_dedup, List.mem_merge]
            exact Or.inl hk', hne>
        * rcases ih2 hx2 h with <hk', hne>
          exact <by
            rw [Form.list_noms, List.mem_dedup, List.mem_merge]
            exact Or.inr hk', hne>
    | box psi ih =>
        have hx' := new_var_geq3 hx
        simp only [nom_subst_svar, Form.list_noms] at hk
        exact ih hx' hk
    | bind y psi ih =>
        have hx' := (new_var_geq2 hx).2
        simp only [nom_subst_svar, Form.new_var, max, Form.list_noms] at hk
        exact ih hx' hk
    | _ => simp [nom_subst_svar, Form.list_noms] at hk

  theorem list_noms_subst {old new : NOM N} : i  in  (phi[new // old]).list_noms  ->  ((i  in  phi.list_noms  /\  i  !=  old)  \/  i = new) := by
    rw [ <- occurs_list_noms,  <- occurs_list_noms]
    intro h
    induction phi with
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
    | impl psi chi ih1 ih2 =>
        simp [nom_subst_nom, nom_occurs] at h  |- 
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
    | box psi ih =>
        simp [nom_subst_nom, nom_occurs] at h
        exact ih h
    | bind _ psi ih =>
        simp [nom_subst_nom, nom_occurs] at h
        exact ih h
    | _     => simp [nom_subst_nom, nom_occurs] at h

  theorem occ_bulk {l_new l_old : List (NOM N)} {phi : Form N} (eq_len : l_new.length = l_old.length) : nom_occurs i (phi.bulk_subst l_new l_old)  ->  ((i  in  phi.list_noms  /\  i  notin  l_old)  \/  i  in  l_new) := by
    intro h
    induction l_new generalizing phi l_old with
    | nil => cases l_old <;> simp [Form.bulk_subst] at *; repeat exact occurs_list_noms.mp h
    | cons h_new t_new ih =>
        cases l_old with
        | nil =>
            simp [Form.bulk_subst] at h  |- 
            apply Or.inl
            exact occurs_list_noms.mp h
        | cons h_old t_old =>
            simp [Form.bulk_subst] at eq_len h  |- 
            have := ih eq_len h
            apply Or.elim this
            . intro hyp
              clear this ih
              cases t_new
              . have := List.length_eq_zero_iff.mp (Eq.symm (Eq.subst eq_len (@List.length_nil (NOM N))))
                simp [this, Form.bulk_subst] at h  |- 
                apply Or.elim (list_noms_subst (occurs_list_noms.mp h))
                . intro c1
                  simp [c1]
                . intro c2
                  exact Or.inr c2
              . cases t_old
                . simp at eq_len
                . simp [Form.bulk_subst] at hyp  |- 
                  have <a, b> := hyp
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

  theorem nocc_bulk {l_new l_old : List (NOM N)} {phi : Form N} (eq_len : l_new.length = l_old.length) : ((i  notin  phi.list_noms  \/  i  in  l_old)  /\  i  notin  l_new)  ->  nom_occurs i (phi.bulk_subst l_new l_old) = false := by
    rw [contraposition]
    simp [-implication_disjunction]
    intro h1 h2
    apply Or.elim (occ_bulk eq_len h1)
    . simp
    . simp [h2]

  theorem has_nocc_bulk_property : forall  phi : Form TotalSet, nocc_bulk_property phi.odd_list_noms phi.list_noms phi := by
    unfold nocc_bulk_property
    intro phi n i h
    match n with
    | <pos, lt_pos> =>
        apply And.intro
        . by_cases c : i  in  phi.list_noms
          . apply Or.inr
            simp only
            -- by h, we know that i > phi.list_noms[pos]
            have lt_pos_2 := (Eq.subst (Eq.symm eq_len) lt_pos)
            have hpos : i = 2 * phi.list_noms[pos] + 1 := by
                rw [h]; exact odd_is_odd lt_pos_2 lt_pos
            have : phi.list_noms[pos].letter < i.letter := by
                rw [hpos]
                change (phi.list_noms[pos].letter : Nat) < (phi.list_noms[pos].letter : Nat) * 2 + 1
                omega
            -- since phi.list_noms is in descending order
            --  and i  in  phi.list_noms by assumption,
            -- then i  in  phi.list_noms[:pos]
            apply descending_property
            apply descending_list_noms
            repeat assumption
          . exact Or.inl c
        . simp
          apply descending_ndup
          apply descending_odd_list_noms
          assumption
  
    theorem nocc_bulk_property_induction : nocc_bulk_property (h_new :: t_new) (h_old :: t_old) phi  ->  nocc_bulk_property t_new t_old (phi[h_new//h_old]) := by
      unfold nocc_bulk_property
      intro h n i eq_i
      let m : Fin (List.length (h_new :: t_new)) := <n.val+1, Nat.succ_lt_succ_iff.mpr n.2>
      have m_n : m.val = n.val + 1 := rfl
      have hmem : i = (h_new :: t_new)[m] := eq_i
      have <l, r> := h hmem
      apply And.intro
      . simp [m_n,  <- or_assoc] at l
        apply Or.elim l
        . intro disj
          apply Or.inl
          apply not_imp_not.mpr (list_noms_subst (i := i) (phi := phi) (old := h_old) (new := h_new))
          simp
          apply And.intro
          . intro habs
            have l2 : h_new  in  List.take (m) (h_new :: t_new) := by simp [m_n]
            rw [ <- habs] at r l2
            contradiction
          . rw [Or.comm]; exact disj
        . intro
          apply Or.inr
          assumption
      . simp [m_n] at r
        exact r.right

end Nominals

  lemma dbl_subst_nom {j : NOM N} {x : SVAR} (i : NOM N) (h : nom_occurs j phi = false) : phi[j//i][x//j] = phi[x//i] := by
    induction phi <;> simp [nom_occurs, nom_subst_nom, nom_subst_svar, -implication_disjunction, *] at *
    . split <;> simp [nom_subst_svar, Ne.symm h]
    repeat simp [h, *] at *

  lemma svar_svar_nom_subst {i j : NOM N} {x : SVAR} (h : x  >=  phi.new_var) : phi[x//i][j//x] = phi[j//i] := by
    induction phi <;> simp [nom_subst_svar, nom_subst_nom, subst_nom, -implication_disjunction, *] at *
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
  
  lemma nom_subst_self {i : NOM N} : phi[i // i] = phi := by
    induction phi <;> simp [nom_subst_nom, -implication_disjunction, *] at * 
    . intro h ; apply Eq.symm; assumption

  lemma eq_new_var {i j : NOM N} : phi.new_var = (phi[i // j]).new_var := by
    induction phi <;> simp [Form.new_var, nom_subst_nom, *] at * 
    . split <;> simp [Form.new_var]



  theorem odd_nom {i : NOM TotalSet} : (Form.nom i).odd_noms = Form.nom (2 * i + 1) := by
    simp [Form.odd_noms, Form.odd_list_noms, Form.list_noms, Form.bulk_subst, nom_subst_nom, NOM_eq, NOM.hmul, NOM.add, Nat.mul_comm]

  theorem bulk_subst_impl {phi psi : Form TotalSet} : (phi  -->  psi).bulk_subst l_1 l_2 = phi.bulk_subst l_1 l_2  -->  psi.bulk_subst l_1 l_2 := by
    induction l_1 generalizing phi psi l_2 with
    | nil => cases l_2 <;> rfl
    | cons h t ih =>
        cases l_2 with
        | nil => rfl
        | cons h2 t2 => simp only [Form.bulk_subst, nom_subst_nom]; exact ih

  theorem bulk_subst_box {phi : Form TotalSet} : ([] phi).bulk_subst l_1 l_2 = [] (phi.bulk_subst l_1 l_2) := by
    induction l_1 generalizing phi l_2 with
    | nil => cases l_2 <;> rfl
    | cons h t ih =>
        cases l_2 with
        | nil => rfl
        | cons h2 t2 => simp only [Form.bulk_subst, nom_subst_nom]; exact ih

  theorem bulk_subst_bind {phi : Form TotalSet} {x : SVAR} : (all x, phi).bulk_subst l_1 l_2 = all x, (phi.bulk_subst l_1 l_2) := by
    induction l_1 generalizing phi l_2 with
    | nil => cases l_2 <;> rfl
    | cons h t ih =>
        cases l_2 with
        | nil => rfl
        | cons h2 t2 => simp only [Form.bulk_subst, nom_subst_nom]; exact ih

  -- A structural characterisation of `odd_noms`: rename every nominal `i  |->  2i+1`,
  -- recursing through the syntax tree.  We prove below that `bulk_subst` over any
  -- descending list that contains all of `phi`'s nominals computes exactly this map,
  -- which is what makes the homomorphism lemmas `list_noms_impl_*` go through.
  def Form.odd_map : Form TotalSet  ->  Form TotalSet
    | .nom i    => Form.nom (2 * i + 1)
    | .impl phi psi => phi.odd_map  -->  psi.odd_map
    | .box phi    => []  phi.odd_map
    | .bind x phi => all x, phi.odd_map
    | phi         => phi

  theorem bulk_subst_const {phi : Form TotalSet} (h : forall  (i j : NOM TotalSet), phi[i // j] = phi) {L_1 L_2 : List (NOM TotalSet)} : phi.bulk_subst L_1 L_2 = phi := by
    induction L_1 generalizing L_2 with
    | nil => cases L_2 <;> rfl
    | cons a as ih =>
        cases L_2 with
        | nil => rfl
        | cons o os => rw [Form.bulk_subst, h]; exact ih

  theorem nom_bulk_noop {j : NOM TotalSet} {L_1 L_2 : List (NOM TotalSet)} (h : j  notin  L_2) : (Form.nom j).bulk_subst L_1 L_2 = Form.nom j := by
    induction L_1 generalizing L_2 with
    | nil => cases L_2 <;> rfl
    | cons a as ih =>
        cases L_2 with
        | nil => rfl
        | cons o os =>
            simp only [List.mem_cons, not_or] at h
            simp only [Form.bulk_subst, nom_subst_nom]
            rw [if_neg h.1]
            exact ih h.2

  theorem nom_bulk {i : NOM TotalSet} : forall  {L : List (NOM TotalSet)}, i  in  L  ->  descending L  ->  (Form.nom i).bulk_subst (L.map (fun j => 2 * j + 1)) L = Form.nom (2 * i + 1) := by
    intro L
    induction L with
    | nil => intro hmem _; simp at hmem
    | cons o os ih =>
        intro hmem hdesc
        rw [List.map_cons]
        by_cases hio : i = o
        * subst hio
          have hnotin : (2 * i + 1)  notin  os := by
            intro habs
            have h : i > 2 * i + 1 := hdesc.left _ habs
            change ((i.letter : Nat) * 2 + 1 < (i.letter : Nat)) at h
            omega
          simp only [Form.bulk_subst, nom_subst_nom, if_pos]
          exact nom_bulk_noop hnotin
        * have hios : i  in  os := (List.mem_cons.mp hmem).resolve_left hio
          simp only [Form.bulk_subst, nom_subst_nom]
          rw [if_neg hio]
          exact ih hios hdesc.right

  theorem bulk_eq_odd_map {L : List (NOM TotalSet)} (hdesc : descending L) :
      forall  phi : Form TotalSet, (forall  i  in  phi.list_noms, i  in  L)  ->  phi.bulk_subst (L.map (fun j => 2 * j + 1)) L = phi.odd_map := by
    intro phi
    induction phi with
    | bttm => intro _; exact bulk_subst_const (fun _ _ => rfl)
    | prop p => intro _; exact bulk_subst_const (fun _ _ => rfl)
    | svar x => intro _; exact bulk_subst_const (fun _ _ => rfl)
    | nom i => intro hsub; exact nom_bulk (hsub i (by simp [Form.list_noms])) hdesc
    | impl phi psi ihphi ihpsi =>
        intro hsub
        simp only [Form.odd_map]
        have mphi : forall  i  in  phi.list_noms, i  in  L := by
          intro i hi; apply hsub i
          rw [ <-  occurs_list_noms] at hi  |- 
          simp only [nom_occurs, hi, Bool.true_or]
        have mpsi : forall  i  in  psi.list_noms, i  in  L := by
          intro i hi; apply hsub i
          rw [ <-  occurs_list_noms] at hi  |- 
          simp only [nom_occurs, hi, Bool.or_true]
        rw [bulk_subst_impl, ihphi mphi, ihpsi mpsi]
    | box phi ih => intro hsub; simp only [Form.odd_map]; rw [bulk_subst_box, ih hsub]
    | bind x phi ih => intro hsub; simp only [Form.odd_map]; rw [bulk_subst_bind, ih hsub]

  theorem list_noms_impl_r {phi psi : Form TotalSet} : phi.bulk_subst phi.odd_list_noms phi.list_noms = phi.bulk_subst (phi  -->  psi).odd_list_noms (phi  -->  psi).list_noms := by
    simp only [Form.odd_list_noms]
    rw [bulk_eq_odd_map (@descending_list_noms phi) phi (fun i hi => hi),
        bulk_eq_odd_map (@descending_list_noms (phi  -->  psi)) phi
          (by intro i hi; rw [ <-  occurs_list_noms] at hi  |- ; simp only [nom_occurs, hi, Bool.true_or])]

  theorem list_noms_impl_l {phi psi : Form TotalSet} : phi.bulk_subst phi.odd_list_noms phi.list_noms = phi.bulk_subst (psi  -->  phi).odd_list_noms (psi  -->  phi).list_noms := by
    simp only [Form.odd_list_noms]
    rw [bulk_eq_odd_map (@descending_list_noms phi) phi (fun i hi => hi),
        bulk_eq_odd_map (@descending_list_noms (psi  -->  phi)) phi
          (by intro i hi; rw [ <-  occurs_list_noms] at hi  |- ; simp only [nom_occurs, hi, Bool.or_true])]

  theorem odd_impl : (phi  -->  psi).odd_noms = phi.odd_noms  -->  psi.odd_noms := by
    unfold Form.odd_noms
    conv => rhs; rw [@list_noms_impl_r phi psi, @list_noms_impl_l psi phi]
    simp [bulk_subst_impl]

  theorem odd_bttm : (Form.bttm : Form TotalSet).odd_noms = Form.bttm := by
    simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst]

  theorem odd_box : ([] phi).odd_noms = [] (phi.odd_noms) := by
    show ([] phi).bulk_subst ([] phi).odd_list_noms ([] phi).list_noms = [] (phi.bulk_subst phi.odd_list_noms phi.list_noms)
    exact bulk_subst_box

  theorem odd_bind : (all x, phi).odd_noms = all x, (phi.odd_noms) := by
    show (all x, phi).bulk_subst (all x, phi).odd_list_noms (all x, phi).list_noms = all x, (phi.bulk_subst phi.odd_list_noms phi.list_noms)
    exact bulk_subst_bind

  theorem odd_conj_two {phi psi : Form TotalSet} : (phi  /\  psi).odd_noms = phi.odd_noms  /\  psi.odd_noms := by
    simp only [Form.conj, Form.neg, odd_impl, odd_bttm]

  def List.to_odd {Gamma : Set (Form TotalSet)} : List Gamma  ->  List Gamma.odd_noms
    | [] => []
    | (h :: t) => <h.val.odd_noms, <h.val, h.2, rfl>> :: t.to_odd

  noncomputable def List.odd_to {Gamma : Set (Form TotalSet)} : List Gamma.odd_noms  ->  List Gamma
    | [] => []
    | (h :: t) => <h.2.choose, h.2.choose_spec.1> :: t.odd_to

  theorem odd_conj (Gamma : Set (Form TotalSet)) (L : List Gamma) : (conjunction Gamma L).odd_noms = conjunction Gamma.odd_noms L.to_odd := by
    induction L with
    | nil => simp only [conjunction, List.to_odd, odd_impl, odd_bttm]
    | cons head tail ih =>
        show (head.val  /\  conjunction Gamma tail).odd_noms
            = head.val.odd_noms  /\  conjunction Gamma.odd_noms tail.to_odd
        rw [odd_conj_two, ih]

  theorem odd_conj_rev (Gamma : Set (Form TotalSet)) (L' : List Gamma.odd_noms) : (conjunction Gamma L'.odd_to).odd_noms = conjunction Gamma.odd_noms L' := by
    induction L' with
    | nil => simp only [conjunction, List.odd_to, odd_impl, odd_bttm]
    | cons head tail ih =>
        show (head.2.choose  /\  conjunction Gamma tail.odd_to).odd_noms
            = head.val  /\  conjunction Gamma.odd_noms tail
        rw [odd_conj_two, ih, head.2.choose_spec.2]
