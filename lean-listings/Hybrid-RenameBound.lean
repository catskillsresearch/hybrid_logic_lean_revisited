import Hybrid.Soundness
import Hybrid.Substitutions
import Hybrid.ProofUtils

def Form.replace_bound : Form N  ->  SVAR  ->  Form N
  | (all z, phi), x =>
        if z = x then
          let y := (phi.replace_bound x).new_var + x.letter + 1
          all y, (phi.replace_bound x)[y//x]
        else all z, phi.replace_bound x
  | (phi  -->  psi), x => (phi.replace_bound x)  -->  (psi.replace_bound x)
  | ([] phi), x     => []  (phi.replace_bound x)
  | phi, _        => phi

theorem replace_neg : (~phi).replace_bound x = ~(phi.replace_bound x) := by
  rfl

theorem replace_bound_depth {phi : Form N} {x : SVAR} : (phi.replace_bound x).depth = phi.depth := by
  induction phi with
  | bind z psi ih =>
      simp only [Form.replace_bound]
      split
      . simp only [Form.depth, subst_depth', ih]
      . simp only [Form.depth, ih]
  | impl phi psi ih1 ih2 =>
      simp only [Form.replace_bound, Form.depth, ih1, ih2]
  | box phi ih =>
      simp only [Form.replace_bound, Form.depth, ih]
  | _ => rfl

theorem replace_bound_depth' {psi : Form N} {x z : SVAR} : ((psi.replace_bound x)[x//z]).depth < (ex x, psi).depth := by
  rw [subst_depth', replace_bound_depth]
  apply ex_depth

-- `phi.no_bind y` records that no binder in `phi` is the variable `y`.  This is
-- exactly the structural invariant that `replace_bound y` establishes, and it
-- is precisely what makes a substitution of `y` capture-free.
def Form.no_bind (y : SVAR) : Form N  ->  Prop
  | .impl phi psi => phi.no_bind y  /\  psi.no_bind y
  | .box phi    => phi.no_bind y
  | .bind z phi => z  !=  y  /\  phi.no_bind y
  | _         => True

theorem no_bind_substable {phi : Form N} {y x : SVAR} : phi.no_bind y  ->  is_substable phi y x = true := by
  induction phi with
  | impl phi psi ih1 ih2 =>
      intro h
      simp only [Form.no_bind] at h
      simp [is_substable, ih1 h.1, ih2 h.2]
  | box phi ih =>
      intro h
      simp only [Form.no_bind] at h
      simp [is_substable, ih h]
  | bind z psi ih =>
      intro h
      simp only [Form.no_bind] at h
      simp only [is_substable]
      split
      . rfl
      . simp only [bne_iff_ne, Bool.and_eq_true]
        exact <h.1, ih h.2>
  | _ => intro _; simp only [is_substable]

theorem no_bind_subst {phi : Form N} {y w : SVAR} : phi.no_bind y  ->  (phi[w//y]).no_bind y := by
  induction phi with
  | svar z => intro _; simp only [subst_svar]; split <;> exact True.intro
  | impl phi psi ih1 ih2 =>
      intro h
      simp only [Form.no_bind] at h
      simp only [subst_svar, Form.no_bind]
      exact <ih1 h.1, ih2 h.2>
  | box phi ih =>
      intro h
      simp only [Form.no_bind] at h
      simp only [subst_svar, Form.no_bind]
      exact ih h
  | bind z psi ih =>
      intro h
      simp only [Form.no_bind] at h
      simp only [subst_svar]
      split
      . simp only [Form.no_bind]; exact h
      . simp only [Form.no_bind]; exact <h.1, ih h.2>
  | _ => intro _; exact True.intro

theorem replace_bound_no_bind {phi : Form N} {y : SVAR} : (phi.replace_bound y).no_bind y := by
  induction phi with
  | impl phi psi ih1 ih2 =>
      simp only [Form.replace_bound, Form.no_bind]
      exact <ih1, ih2>
  | box phi ih =>
      simp only [Form.replace_bound, Form.no_bind]
      exact ih
  | bind z psi ih =>
      simp only [Form.replace_bound]
      split
      . simp only [Form.no_bind]
        refine <?_, no_bind_subst ih>
        simp only [ne_eq, svar_eq, svar_add_letter]
        omega
      . rename_i hzy
        simp only [Form.no_bind]
        exact <hzy, ih>
  | _ => exact True.intro

theorem substable_after_replace (phi : Form N) : is_substable (phi.replace_bound y) y x :=
  no_bind_substable replace_bound_no_bind

noncomputable def rename_all_bound_pf (phi : Form N) (x : SVAR) :  |-  (phi  <->  (phi.replace_bound x)) := by
  induction phi with
  | bind z phi ih =>
      rw [Form.replace_bound]
      by_cases h : z = x
      . simp only [h, ite_true]
        let l1 := Proof.mp Proof.b363 (Proof.general x (Proof.mp (Proof.tautology iff_elim_l) ih))
        let l2 := Proof.mp Proof.b363 (Proof.general x (Proof.mp (Proof.tautology iff_elim_r) ih))
        let l3 := Proof.mp (Proof.mp (Proof.tautology iff_intro) l1) l2
        let y := (phi.replace_bound x).new_var + x.letter + 1
        have : y  >=  (phi.replace_bound x).new_var := by
          simp only [y, ge_iff_le, svar_le_letter, svar_add_letter]; omega
        let l4 := @Proof.rename_bound N y x (phi.replace_bound x) (ge_new_var_is_new this) (new_var_subst'' this)
        let l5 := Proof.mp (Proof.mp (Proof.tautology iff_rw) l3) l4
        exact l5
      . simp only [h, ite_false]
        let l1 := Proof.mp Proof.b363 (Proof.general z (Proof.mp (Proof.tautology iff_elim_l) ih))
        let l2 := Proof.mp Proof.b363 (Proof.general z (Proof.mp (Proof.tautology iff_elim_r) ih))
        let l3 := Proof.mp (Proof.mp (Proof.tautology iff_intro) l1) l2
        exact l3
  | impl phi psi ih1 ih2 =>
      exact Proof.mp (Proof.mp (Proof.tautology iff_imp) ih1) ih2
  | box phi ih =>
      let l1 := Proof.mp Proof.ax_k (Proof.necess (Proof.mp (Proof.tautology iff_elim_l) ih))
      let l2 := Proof.mp Proof.ax_k (Proof.necess (Proof.mp (Proof.tautology iff_elim_r) ih))
      let l3 := Proof.mp (Proof.mp (Proof.tautology iff_intro) l1) l2
      exact l3
  | _ =>
      exact Proof.mp (Proof.mp (Proof.tautology iff_intro) (Proof.tautology imp_refl)) (Proof.tautology imp_refl)

theorem rename_all_bound (phi : Form N) (x : SVAR) :  |=  (phi  <->  (phi.replace_bound x)) := by
  exact WeakSoundness (rename_all_bound_pf phi x)

noncomputable def exists_replace :  |-  ((ex x, phi.replace_bound y)  -->  (ex x, phi)) := by
  let l1 := replace_neg  |>  Proof.mp (Proof.tautology iff_elim_l) (rename_all_bound_pf (~phi) y)
  let l2 := Proof.mp Proof.b363 (Proof.general x l1)
  let l3 := Proof.mp (Proof.tautology contrapositive) l2
  exact l3
