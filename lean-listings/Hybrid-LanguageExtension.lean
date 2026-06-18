import Hybrid.Proof
import Hybrid.Substitutions
import Hybrid.ProofUtils
import Hybrid.Truth

open Proof

def Form.total : Form N  ->  Form TotalSet
  | .bttm     => Form.bttm
  | .prop p   => Form.prop p
  | .svar v   => Form.svar v
  | .nom i    => Form.nom <i.1.1, trivial>
  | .impl psi chi => Form.impl psi.total chi.total
  | .box psi    => Form.box psi.total
  | .bind v psi => Form.bind v psi.total

theorem total_inj' {phi psi : Form N} : phi.total = psi.total  ->  phi = psi := by
  induction phi generalizing psi with
  | impl a b ih1 ih2 =>
        cases psi with
        | impl c d => simp [Form.total, -implication_disjunction]
                      intros
                      apply And.intro <;> (first | apply ih1 | apply ih2) <;> assumption
        | _    => simp [Form.total]
  | box a ih | bind v a ih =>
      cases psi with
      | box b    => simp [Form.total, -implication_disjunction]; try apply ih
      | bind u b => simp [Form.total, -implication_disjunction];
                    try (intro; simp only [*, true_and]; apply ih)
      | _     => simp  [Form.total]
  | _    => cases psi <;> simp [Form.total, NOM_eq, -implication_disjunction] <;>
                        (intros; apply Subtype.eq; assumption)

lemma total_inj {N : Set Nat} : (@Form.total N).Injective := by
  unfold Function.Injective
  apply total_inj'

noncomputable def Form.inv_t : Form TotalSet  ->  Form N := Function.invFun Form.total

lemma total_inv_is_inv : Function.LeftInverse (@Form.inv_t N) Form.total := by
  apply Function.leftInverse_invFun
  apply total_inj'

notation phi"^+" => Form.total phi
notation phi"^-" => Form.inv_t phi

/-- The image of a base-language set under `Form.total`. -/
noncomputable def Set.total (Gamma : Set (Form N)) : Set (Form TotalSet) :=
  {psi | exists  phi  in  Gamma, psi = phi.total}

/-- Restrict a `TotalSet` model to the nominal type `N` (same world, same `V_p`, nominals
    embedded via `Subtype`).  Used to pull a completed `TotalSet` model back to `Model N`. -/
noncomputable def Model.ofTotal (M : Model TotalSet) : Model N where
  W := M.W
  R := M.R
  V_p := M.V_p
  V_n := fun i => M.V_n <i.letter, trivial>

/-- Satisfaction commutes with `Form.total` under `Model.ofTotal`. -/
theorem sat_total (M : Model TotalSet) (s : M.W) (g : I M.W) (phi : Form N) :
    (@Sat TotalSet M s g phi.total)  <->  (@Sat N (Model.ofTotal M) s g phi) := by
  induction phi generalizing s g with
  | bttm => simp [Form.total, Model.ofTotal, Sat]
  | prop p => simp [Form.total, Model.ofTotal, Sat]; rfl
  | svar v => simp [Form.total, Sat]; rfl
  | nom i => simp [Form.total, Model.ofTotal, Sat]
  | impl a b iha ihb => simp [Form.total, Model.ofTotal, Sat, iha, ihb]
  | box a ih =>
      simp only [Form.total, Model.ofTotal, Sat]
      constructor
      * intro h s' hs'
        exact (ih s' g).mp (h s' hs')
      * intro h s' hs'
        exact (ih s' g).mpr (h s' hs')
  | bind x a ih =>
      simp only [Form.total, Model.ofTotal, Sat]
      constructor
      * intro h g' hg'
        exact (ih s g').mp (h g' hg')
      * intro h g' hg'
        exact (ih s g').mpr (h g' hg')

theorem total_impl {phi : Form N} : phi^+ = (psi  -->  chi)  ->  phi = (psi^-  -->  chi^-) := by
  intro h
  cases phi with
  | impl phi psi =>
    simp [Form.total] at h  |- 
    apply And.intro
    . rw [ <- total_inv_is_inv phi]
      exact congr_arg (@Form.inv_t N) h.1
    . rw [ <- total_inv_is_inv psi]
      exact congr_arg (@Form.inv_t N) h.2
  | _ => simp [Form.total] at *

theorem total_box {phi : Form N} : phi^+ = []  psi  ->  phi = []  psi^- := by
  intro h
  cases phi with
  | box phi =>
    simp [Form.total] at h  |- 
    rw [ <- total_inv_is_inv phi]
    exact congr_arg (@Form.inv_t N) h
  | _ => simp [Form.total] at *

theorem total_bind {phi : Form N} : phi^+ = (all x, psi)  ->  phi = (all x, psi^-) := by
  intro h
  cases phi with
  | bind x phi =>
    simp [Form.total] at h  |- 
    apply And.intro
    . exact h.1
    . rw [ <- total_inv_is_inv phi]
      exact congr_arg (@Form.inv_t N) h.2
  | _ => simp [Form.total] at *

lemma total_subst_svar' {phi : Form N} {x y : SVAR} : (phi[y // x]).total = (phi.total)[y // x] := by
  induction phi with
  | svar z => by_cases h : x = z <;> simp [subst_svar, Form.total, h, -implication_disjunction]
  | impl phi psi ih1 ih2 => simp only [subst_svar, Form.total, ih1, ih2]
  | box phi ih => simp only [subst_svar, Form.total, ih]
  | bind v phi ih => by_cases h : x = v <;> simp [subst_svar, Form.total, ih, h, -implication_disjunction]
  | _ => rfl

-- The image of `Form.total` is closed under taking subformulas through a
-- variable substitution: substituting an SVAR never touches nominals, so if
-- `psi[y//x]` arises from an `N`-formula then so does `psi`.
lemma range_of_subst {psi : Form TotalSet} {y x : SVAR} : (exists  chi : Form N, chi.total = psi[y // x])  ->  exists  chi' : Form N, chi'.total = psi := by
  induction psi with
  | bttm => intro _; exact <Form.bttm, rfl>
  | prop p => intro _; exact <Form.prop p, rfl>
  | svar z => intro _; exact <Form.svar z, rfl>
  | nom i => intro h; exact h
  | impl a b iha ihb =>
      intro <chi, hchi>
      cases chi with
      | impl c d =>
          simp only [Form.total, subst_svar, Form.impl.injEq] at hchi
          obtain <c', hc'> := iha <c, hchi.1>
          obtain <d', hd'> := ihb <d, hchi.2>
          exact <c'  -->  d', by simp only [Form.total, hc', hd']>
      | _ => simp [Form.total, subst_svar] at hchi
  | box a ih =>
      intro <chi, hchi>
      cases chi with
      | box c =>
          simp only [Form.total, subst_svar, Form.box.injEq] at hchi
          obtain <c', hc'> := ih <c, hchi>
          exact <[]  c', by simp only [Form.total, hc']>
      | _ => simp [Form.total, subst_svar] at hchi
  | bind z a ih =>
      intro <chi, hchi>
      by_cases hxz : x = z
      * simp only [subst_svar, hxz] at hchi
        exact <chi, hchi>
      * simp only [subst_svar, hxz] at hchi
        cases chi with
        | bind w c =>
            simp only [Form.total] at hchi
            injection hchi with hw hc
            obtain <c', hc'> := ih <c, hc>
            exact <Form.bind z c', by simp only [Form.total, hc']>
        | _ => simp [Form.total] at hchi

lemma inv_t_subst {psi : Form TotalSet} {y x : SVAR} (h : exists  chi : Form N, chi.total = psi) : (@Form.inv_t N) (psi[y // x]) = ((@Form.inv_t N) psi)[y // x] := by
  obtain <chi, rfl> := h
  rw [ <-  total_subst_svar', total_inv_is_inv, total_inv_is_inv]

theorem total_subst_svar {phi : Form N} {x y : SVAR} : phi^+ = psi[y//x]  ->  phi = psi^-[y//x] := by
  intro h
  have hr : exists  chi : Form N, chi.total = psi := range_of_subst <phi, h>
  rw [ <-  total_inv_is_inv phi, h, inv_t_subst hr]

theorem total_ax_k {phi : Form N} (h : phi^+ = [] (psi  -->  chi)  -->  ([] psi  -->  [] chi)) : phi = [] (psi^-  -->  chi^-)  -->  ([] psi^-  -->  [] chi^-) := by
  cases phi with
  | impl phi_l phi_r =>
      simp [Form.total] at h  |- 
      apply And.intro
      . have hyp := h.1
        clear h
        cases phi_l with
        | box phi_l_b =>
            simp [Form.total] at hyp  |- 
            cases phi_l_b with
            | impl phi_l_b_l phi_l_b_r =>
                apply total_impl
                assumption
            | _ =>  simp [Form.total] at *
        | _ => simp [Form.total] at *
      . have hyp := h.2
        clear h
        cases phi_r with
        | impl phi_r_l phi_r_r =>
            simp [Form.total] at hyp  |- 
            apply And.intro
            . apply total_box hyp.1
            . apply total_box hyp.2
        | _ => simp [Form.total] at hyp  |- 
  | _ => simp [Form.total] at *

theorem total_ax_q1 {phi : Form N} {x : SVAR} (h : phi^+ = (all x, psi  -->  chi)  -->  (psi  -->  all x, chi)) : phi = (all x, psi^-  -->  chi^-)  -->  (psi^-  -->  all x, chi^-) := by
  cases phi with
  | impl l r =>
      simp [Form.total] at h  |- 
      apply And.intro
      . have h := h.1
        cases l with
        | bind x l =>
            simp [Form.total] at h  |- 
            simp [h]
            apply total_impl h.2
        | _ => simp [Form.total] at *
      . have h := h.2
        cases r with
        | impl rl rr =>
            simp [Form.total] at h  |- 
            apply And.intro
            . rw [ <- total_inv_is_inv rl]
              exact congr_arg (@Form.inv_t N) h.1
            . apply total_bind h.2
        | _ => simp [Form.total] at h  |- 
  | _ => simp [Form.total] at *

theorem total_ax_q2_svar {phi : Form N} {x y : SVAR} (h : phi^+ = (all x, psi)  -->  psi[y // x]) : phi = (all x, psi^-)  -->  psi^-[y//x] := by
  cases phi with
  | impl l r =>
      simp [Form.total] at h  |- 
      apply And.intro
      . apply total_subst_svar h.2
      . apply total_bind h.1
  | _ => simp [Form.total] at h  |- 




-- Given an `Eval N`, build a Boolean valuation on `Form TotalSet` that mirrors
-- `e` structurally on ` --> `/`False` and falls back to `e  comp  inv_t` on atoms.  On the
-- image of `Form.total` (which is entirely in range) this recovers `e` exactly.
noncomputable def evalN_to_T (e : Eval N) : Form TotalSet  ->  Bool
  | .bttm     => false
  | .prop p   => e.f (Form.prop p)
  | .svar v   => e.f (Form.svar v)
  | .nom i    => e.f (Form.inv_t (Form.nom i))
  | .impl psi chi => !(evalN_to_T e psi) || (evalN_to_T e chi)
  | .box psi    => e.f (Form.inv_t (Form.box psi))
  | .bind x psi => e.f (Form.inv_t (Form.bind x psi))

noncomputable def evalT (e : Eval N) : Eval TotalSet where
  f  := evalN_to_T e
  p1 := rfl
  p2 := by
    intro psi chi
    show (!(evalN_to_T e psi) || evalN_to_T e chi) = true  <->  _
    cases evalN_to_T e psi <;> cases evalN_to_T e chi <;> simp

theorem evalT_total {e : Eval N} (phi : Form N) : evalN_to_T e (phi.total) = e.f phi := by
  induction phi with
  | bttm => simp only [Form.total, evalN_to_T, e.p1]
  | prop p => rfl
  | svar v => rfl
  | nom i => show e.f (Form.inv_t ((Form.nom i).total)) = _; rw [total_inv_is_inv]
  | box a _ => show e.f (Form.inv_t ((Form.box a).total)) = _; rw [total_inv_is_inv]
  | bind x a _ => show e.f (Form.inv_t ((Form.bind x a).total)) = _; rw [total_inv_is_inv]
  | impl a b iha ihb =>
      show (!(evalN_to_T e a.total) || evalN_to_T e b.total) = e.f (a  -->  b)
      rw [iha, ihb]
      have h := e.p2 a b
      cases ha : e.f a <;> cases hb : e.f b <;> cases hab : e.f (a  -->  b) <;> simp_all

lemma total_tautology {phi : Form N} : Tautology phi  <->  Tautology phi.total := by
  constructor
  * intro h e'
    have gp1 : (fun psi : Form N => e'.f psi.total) False = false := e'.p1
    have gp2 : forall  psi chi : Form N, ((fun psi : Form N => e'.f psi.total) (psi  -->  chi) = true)
         <->  (not ((fun psi : Form N => e'.f psi.total) psi) = true  \/  ((fun psi : Form N => e'.f psi.total) chi) = true) := by
      intro psi chi
      show e'.f (psi.total  -->  chi.total) = true  <->  _
      exact e'.p2 psi.total chi.total
    exact h <fun psi => e'.f psi.total, gp1, gp2>
  * intro h e
    have := h (evalT e)
    rw [show (evalT e).f phi.total = evalN_to_T e phi.total from rfl, evalT_total] at this
    exact this

lemma total_subst_nom {phi : Form N} {i : NOM N} {x : SVAR} : (phi[i // x]).total = (phi.total)[<i.1.1, trivial> // x] := by
  induction phi with
  | svar z => by_cases h : x = z <;> simp [subst_nom, Form.total, h, -implication_disjunction]
  | impl phi psi ih1 ih2 => simp only [subst_nom, Form.total, ih1, ih2]
  | box phi ih => simp only [subst_nom, Form.total, ih]
  | bind v phi ih => by_cases h : x = v <;> simp [subst_nom, Form.total, ih, h, -implication_disjunction]
  | _ => rfl

lemma total_diamond {psi : Form N} : (<>  psi).total = <>  (psi.total) := by
  simp [Form.diamond, Form.neg, Form.total]

lemma total_iterate_pos {phi : Form N} : (iterate_pos n phi).total = iterate_pos n (phi.total) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show <>  ((iterate_pos k phi).total) = <>  (iterate_pos k (phi.total))
      rw [ih]

lemma total_iterate_nec {phi : Form N} : (iterate_nec n phi).total = iterate_nec n (phi.total) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show []  ((iterate_nec k phi).total) = []  (iterate_nec k (phi.total))
      rw [ih]

-- Totalization only renames nominals, so it preserves the free-variable and
-- substitutability predicates (both of which depend solely on the SVAR structure).
lemma total_is_free {phi : Form N} {x : SVAR} : is_free x phi.total = is_free x phi := by
  induction phi with
  | impl a b iha ihb => simp only [Form.total, is_free, iha, ihb]
  | box a ih => simp only [Form.total, is_free, ih]
  | bind y a ih => simp only [Form.total, is_free, ih]
  | _ => rfl

lemma total_is_substable {phi : Form N} {s v : SVAR} : is_substable phi.total s v = is_substable phi s v := by
  induction phi with
  | impl a b iha ihb => simp only [Form.total, is_substable, iha, ihb]
  | box a ih => simp only [Form.total, is_substable, ih]
  | bind y a ih => simp only [Form.total, is_substable, total_is_free, ih]
  | _ => rfl

-- Generalizing a nominal constant `i` to a fresh variable `x` preserves theoremhood
-- (Oltean's Lemma 4.1.6).  Rather than re-running the structural induction, we obtain it
-- from the already-proven universal version `generalize_constants` (` |-  phi  ->   |-  all x, phi[x // i]`)
-- by instantiating the universal back at `x`: since `x` is fresh, `phi[x // i]` is substable
-- for `x`, and `(phi[x // i])[x // x] = phi[x // i]`.
noncomputable def l416 {phi : Form N} {x : SVAR} (i : NOM N) (pf :  |-  phi) (h : pf.fresh_var x) :  |-  (phi[x // i]) := by
  have hcon : pf.contains phi := by unfold Proof.contains; simp only [beq_self_eq_true, Bool.true_or]
  have hx : x  >=  phi.new_var := h phi hcon
  have gc := generalize_constants i hx pf
  have hsub : is_substable (phi[x // i]) x x := new_var_subst hx
  have key := mp (ax_q2_svar (phi[x // i]) x x hsub) gc
  rwa [subst_self_is_self] at key

-- ===========================================================================
-- Helpers for the backward direction of `pf_extended` (conservativity).
-- ===========================================================================

/-- Embed a base-language nominal into `TotalSet`. -/
noncomputable def NOM.toTotal {N : Set Nat} (j : NOM N) : NOM TotalSet := <j.letter, trivial>

/-- Reconstruct a base-language nominal from a `TotalSet` one whose letter lies in `N`. -/
noncomputable def NOM.fromTotal {N : Set Nat} (j : NOM TotalSet) (hj : (j.letter : Nat)  in  N) : NOM N :=
  <j.letter, hj>

lemma NOM.toTotal_total {N : Set Nat} (j : NOM N) :
    (Form.nom j).total = Form.nom (NOM.toTotal j) := by
  simp [Form.total, NOM.toTotal, NOM_eq]

lemma NOM.fromTotal_total {N : Set Nat} (j : NOM TotalSet) (hj : (j.letter : Nat)  in  N) :
    (Form.nom (NOM.fromTotal j hj)).total = Form.nom j := by
  simp [Form.total, NOM.fromTotal, NOM_eq]

def nom_in_base {N : Set Nat} (j : NOM TotalSet) : Prop := (j.letter : Nat)  in  N

lemma NOM.toTotal_fromTotal {N : Set Nat} {j : NOM TotalSet} (hj : nom_in_base (N := N) j) :
    NOM.toTotal (NOM.fromTotal j hj) = j := by
  apply NOM_eq.mpr; rfl

def form_noms_in_base {N : Set Nat} (psi : Form TotalSet) : Prop :=
  forall  j  in  psi.list_noms, nom_in_base (N := N) j

lemma form_noms_in_base_nom {N : Set Nat} {i : NOM TotalSet} (hi : nom_in_base (N := N) i) :
    form_noms_in_base (N := N) (Form.nom i) := by
  intro j hj; simp [Form.list_noms] at hj; subst hj; exact hi

lemma form_noms_in_base_impl {N : Set Nat} {a b : Form TotalSet}
    (ha : form_noms_in_base (N := N) a) (hb : form_noms_in_base (N := N) b) :
    form_noms_in_base (N := N) (a  -->  b) := by
  intro j hj
  rw [ <-  occurs_list_noms] at hj
  simp only [Form.list_noms, nom_occurs, Bool.or_eq_true, List.mem_dedup, List.mem_merge] at hj
  rcases hj with h | h
  * exact ha j (by rw [ <-  occurs_list_noms]; exact h)
  * exact hb j (by rw [ <-  occurs_list_noms]; exact h)

lemma form_noms_in_base_box {N : Set Nat} {a : Form TotalSet} (ha : form_noms_in_base (N := N) a) :
    form_noms_in_base (N := N) ([]  a) := ha

lemma form_noms_in_base_bind {N : Set Nat} {v : SVAR} {a : Form TotalSet} (ha : form_noms_in_base (N := N) a) :
    form_noms_in_base (N := N) (all v, a) := ha

/-- If every nominal letter lies in `N`, the formula is in the image of `Form.total`. -/
lemma range_of_form {N : Set Nat} {psi : Form TotalSet} (h : form_noms_in_base (N := N) psi) :
    exists  chi : Form N, chi.total = psi := by
  induction psi with
  | bttm => exact <Form.bttm, rfl>
  | prop p => exact <Form.prop p, rfl>
  | svar v => exact <Form.svar v, rfl>
  | nom i =>
      have hi := h i (by simp [Form.list_noms])
      exact <Form.nom (NOM.fromTotal i hi), NOM.fromTotal_total i hi>
  | impl a b iha ihb =>
      obtain <a', ha'> := iha (fun j (hj : j  in  a.list_noms) => h j (by
        have this := (occurs_list_noms (phi := a)).mpr hj
        rw [ <-  occurs_list_noms]
        simp [Form.list_noms, nom_occurs, this, Bool.or_true]))
      obtain <b', hb'> := ihb (fun j (hj : j  in  b.list_noms) => h j (by
        have this := (occurs_list_noms (phi := b)).mpr hj
        rw [ <-  occurs_list_noms]
        simp [Form.list_noms, nom_occurs, this, Bool.true_or]))
      exact <a'  -->  b', by simp [Form.total, ha', hb']>
  | box a ih =>
      obtain <a', ha'> := ih h
      exact <[]  a', by simp [Form.total, ha']>
  | bind v a ih =>
      obtain <a', ha'> := ih h
      exact <all v, a', by simp [Form.total, ha']>

lemma inv_t_eq_of_range' {N : Set Nat} {psi : Form TotalSet} (h : form_noms_in_base (N := N) psi) :
    ((@Form.inv_t N) psi).total = psi := by
  obtain <chi, hchi> := range_of_form h
  rw [ <-  hchi, total_inv_is_inv]

lemma subst_nom_toTotal {N : Set Nat} {s : NOM TotalSet} (hs : nom_in_base (N := N) s) (v : SVAR)
    (a : Form TotalSet) :
    a[NOM.toTotal (NOM.fromTotal s hs) // v] = a[s // v] :=
  congrArg (fun n : NOM TotalSet => a[n // v]) (NOM.toTotal_fromTotal hs)

theorem total_subst_nom_pullback {N : Set Nat} {a : Form TotalSet} {s : NOM TotalSet} {v : SVAR}
    (ha : form_noms_in_base (N := N) a) (hs : nom_in_base (N := N) s) {phi : Form N}
    (h : Form.total phi = a[s // v]) :
    phi = ((@Form.inv_t N) a)[NOM.fromTotal s hs // v] := by
  apply total_inj'
  rw [h]
  rw [total_subst_nom, inv_t_eq_of_range' ha]
  exact subst_nom_toTotal hs v a

theorem total_ax_q2_nom {N : Set Nat} {phi : Form N} {v : SVAR} {a : Form TotalSet} {s : NOM TotalSet}
    (ha : form_noms_in_base (N := N) a) (hs : nom_in_base (N := N) s)
    (h : phi^+ = (all v, a)  -->  a[s // v]) :
    phi = (all v, ((@Form.inv_t N) a))  -->  ((@Form.inv_t N) a)[NOM.fromTotal s hs // v] := by
  cases phi with
  | impl l r =>
      simp only [Form.total] at h  |- 
      injection h with h1 h2
      rw [total_bind (phi := l) h1]
      rw [total_subst_nom_pullback ha hs h2]
  | _ => simp [Form.total] at h

theorem total_ax_q2_nom_end {N : Set Nat} {phi : Form N} {v : SVAR} {a : Form TotalSet}
    (ha : form_noms_in_base (N := N) a) (h : phi^+ = (all v, a)  -->  a) :
    phi = (all v, ((@Form.inv_t N) a))  -->  ((@Form.inv_t N) a) := by
  cases phi with
  | impl l r =>
      simp only [Form.total] at h  |- 
      injection h with h1 h2
      rw [total_bind (phi := l) h1]
      apply total_inj'
      simp only [Form.total, h2, inv_t_eq_of_range' ha]
  | _ => simp [Form.total] at h

-- ===========================================================================
-- F2 / F3: alien-nominal elimination + in-range proof pullback (Blackburn).
-- ===========================================================================

section Conservativity
variable {NBase : Set Nat}
open Classical

/-- Every base-language formula has only base nominal letters after totalization. -/
lemma form_noms_in_base_total (phi : Form NBase) : form_noms_in_base (N := NBase) phi.total := by
  induction phi with
  | nom i =>
      intro j hj
      have hj' := List.mem_singleton.mp (by simpa [Form.list_noms, Form.total] using hj)
      subst hj'
      simpa [nom_in_base, NOM.toTotal] using i.letter.2
  | impl a b iha ihb => exact form_noms_in_base_impl (N := NBase) iha ihb
  | box a ih => exact form_noms_in_base_box (N := NBase) ih
  | bind v a ih => exact form_noms_in_base_bind (N := NBase) ih
  | bttm | prop _ | svar _ => intro j hj; simp [Form.list_noms, Form.total] at hj

/-- `phi[new // old]` leaves `phi` unchanged when `old` does not occur
    (`nom_subst_nom phi new old` replaces `old` with `new`). -/
lemma nom_subst_nom_nocc {psi : Form TotalSet} {new old : NOM TotalSet}
    (h : nom_occurs old psi = false) : nom_subst_nom psi new old = psi := by
  induction psi with
  | nom a =>
      by_cases heq : a = old
      * exfalso
        exact Bool.eq_false_iff.mp h (by simp [nom_occurs, heq])
      * simp [nom_subst_nom, heq]
  | impl a b iha ihb =>
      simp [nom_occurs, nom_subst_nom, Bool.or_eq_false_iff] at h  |- 
      simp [iha h.1, ihb h.2]
  | box a ih => simp [nom_occurs, nom_subst_nom] at h  |- ; exact ih h
  | bind v a ih => simp [nom_occurs, nom_subst_nom] at h  |- ; exact ih h
  | _ => rfl

lemma nom_occurs_false_of_form_noms_in_base {psi : Form TotalSet} (hpsi : form_noms_in_base (N := NBase) psi)
    {j : NOM TotalSet} (hjb : not nom_in_base (N := NBase) j) : nom_occurs j psi = false := by
  by_cases h : nom_occurs j psi = true
  * exfalso
    have hocc : nom_occurs j psi := h  |>  rfl
    exact hjb (hpsi j ((occurs_list_noms (phi := psi)).mp hocc))
  * rw [ <-  Bool.eq_false_eq_not_eq_true]
    exact h

def Proof.all_noms_in_base (NBase : Set Nat) {psi : Form TotalSet} (pf : @Proof TotalSet psi) : Prop :=
  forall  j  in  pf.proof_noms, nom_in_base (N := NBase) j

lemma Proof.all_noms_in_base_root (NBase : Set Nat) {psi : Form TotalSet} (pf : @Proof TotalSet psi)
    (h : Proof.all_noms_in_base NBase pf) : form_noms_in_base (N := NBase) psi := by
  intro j hj
  exact h j (by
    simp only [Proof.proof_noms, List.mem_dedup, List.mem_flatMap]
    refine <psi, ?_, hj>
    cases pf <;> simp [Proof.formulasIn])

lemma Proof.mem_formulasIn_of_list_noms {psi : Form TotalSet} (pf : @Proof TotalSet psi) (chi : Form TotalSet)
    (hchi : chi  in  pf.formulasIn) {j : NOM TotalSet} (hj : j  in  chi.list_noms) :
    j  in  pf.proof_noms := by
  simp only [Proof.proof_noms, List.mem_dedup, List.mem_flatMap]
  exact <chi, hchi, hj>

lemma Proof.form_noms_in_base_of_all_noms (NBase : Set Nat) {psi : Form TotalSet} (pf : @Proof TotalSet psi)
    (h : Proof.all_noms_in_base NBase pf) : forall  chi  in  pf.formulasIn, form_noms_in_base (N := NBase) chi := by
  intro chi hchi j hj
  exact h j (Proof.mem_formulasIn_of_list_noms pf chi hchi hj)

noncomputable def base_nom_total (hN : NBase.Nonempty) : NOM TotalSet :=
  <Classical.choose hN, trivial>

lemma base_nom_total_in_base (hN : NBase.Nonempty) : nom_in_base (N := NBase) (base_nom_total hN) :=
  Classical.choose_spec hN

/-- Globally rename one alien nominal to a fixed base nominal throughout a derivation. -/
noncomputable def Proof.eliminate_one_alien {psi : Form TotalSet} (pf : @Proof TotalSet psi)
    (hpsi : form_noms_in_base (N := NBase) psi) (j base : NOM TotalSet) (hjb : not nom_in_base (N := NBase) j)
    (hb : nom_in_base (N := NBase) base) : @Proof TotalSet psi := by
  have hnocc := nom_occurs_false_of_form_noms_in_base hpsi hjb
  exact nom_subst_nom_nocc (new := base) (old := j) hnocc  |>  rename_constants_fwd base j pf

/-- Iterated alien elimination over `proof_noms`; the root formula is unchanged. -/
noncomputable def Proof.eliminate_aliens {psi : Form TotalSet} (pf : @Proof TotalSet psi)
    (hpsi : form_noms_in_base (N := NBase) psi) (base : NOM TotalSet) (_hb : nom_in_base (N := NBase) base) :
    List (NOM TotalSet)  ->  @Proof TotalSet psi
  | [] => pf
  | j :: rest =>
      if hjb : nom_in_base (N := NBase) j then
        Proof.eliminate_aliens pf hpsi base _hb rest
      else
        have hAlien : not nom_in_base (N := NBase) j := fun h => hjb h
        Proof.eliminate_aliens (pf.eliminate_one_alien hpsi j base hAlien _hb) hpsi base _hb rest

lemma Proof.mem_proof_noms_eliminate_one_alien {psi : Form TotalSet} (pf : @Proof TotalSet psi)
    (hpsi : form_noms_in_base (N := NBase) psi) (j base : NOM TotalSet)
    (hAlien : not nom_in_base (N := NBase) j) (_hb : nom_in_base (N := NBase) base) {k : NOM TotalSet}
    (hk : k  in  (pf.eliminate_one_alien hpsi j base hAlien _hb).proof_noms) :
    k  in  pf.proof_noms  \/  k = base := by
  have hnocc := nom_occurs_false_of_form_noms_in_base hpsi hAlien
  have hk' : k  in  (rename_constants_fwd base j pf).proof_noms := by
    simpa [Proof.eliminate_one_alien, hnocc, proof_noms_cast] using hk
  exact mem_proof_noms_rename_constants_fwd (new := base) (old := j) (pf := pf) hk'

lemma Proof.not_mem_proof_noms_eliminate_one_alien {psi : Form TotalSet} (pf : @Proof TotalSet psi)
    (hpsi : form_noms_in_base (N := NBase) psi) (j base : NOM TotalSet)
    (hAlien : not nom_in_base (N := NBase) j) (_hb : nom_in_base (N := NBase) base) :
    j  notin  (pf.eliminate_one_alien hpsi j base hAlien _hb).proof_noms := by
  have hnocc := nom_occurs_false_of_form_noms_in_base hpsi hAlien
  intro h
  have h' : j  in  (rename_constants_fwd base j pf).proof_noms := by
    simpa [Proof.eliminate_one_alien, hnocc, proof_noms_cast] using h
  have hne : base  !=  j := fun heq => hAlien (heq  |>  _hb)
  exact not_mem_proof_noms_rename_constants_fwd (new := base) (old := j) (pf := pf) hne h'

lemma Proof.all_noms_in_base_eliminate_go {psi : Form TotalSet}
    (hpsi : form_noms_in_base (N := NBase) psi) (base : NOM TotalSet) (hb : nom_in_base (N := NBase) base) :
    forall  (L : List (NOM TotalSet)) (pf' : @Proof TotalSet psi),
      (forall  k, k  in  pf'.proof_noms  ->  k  in  L  \/  nom_in_base (N := NBase) k)  -> 
      Proof.all_noms_in_base NBase (pf'.eliminate_aliens hpsi base hb L) := by
  intro L pf' hsub
  induction L generalizing pf' with
  | nil =>
      intro k hk
      simp only [Proof.all_noms_in_base, Proof.eliminate_aliens] at hk  |- 
      exact (hsub k hk).resolve_left (by simp)
  | cons j rest ih =>
      simp only [Proof.eliminate_aliens]
      split_ifs with hjb
      * exact ih pf' (by
          intro k hk
          rcases hsub k hk with hL | hbk
          * simp only [List.mem_cons] at hL
            rcases hL with (rfl) | hkrest
            * exact Or.inr hjb
            * exact Or.inl hkrest
          * exact Or.inr hbk)
      * have hAlien : not nom_in_base (N := NBase) j := fun h => hjb h
        exact ih (pf'.eliminate_one_alien hpsi j base hAlien hb) (by
          intro k hk
          by_cases hkbase : nom_in_base (N := NBase) k
          * exact Or.inr hkbase
          * exact Or.inl (by
              have hmem := Proof.mem_proof_noms_eliminate_one_alien pf' hpsi j base hAlien hb hk
              have hkpf : k  in  pf'.proof_noms := by
                rcases hmem with hkpf | hkb
                * exact hkpf
                * exact absurd (hkb  |>  hb) hkbase
              have := hsub k hkpf
              simp only [List.mem_cons, Bool.not_eq_true] at this
              rcases this with hL | hbk
              * rcases hL with hj | hkrest
                * rw [hj] at hk
                  exact absurd hk (Proof.not_mem_proof_noms_eliminate_one_alien pf' hpsi j base hAlien hb)
                * exact hkrest
              * exact absurd hbk hkbase))

/-- After eliminating every alien in `proof_noms`, all remaining nominals lie in `N`. -/
lemma Proof.all_noms_in_base_eliminate_aliens {psi : Form TotalSet} (pf : @Proof TotalSet psi)
    (hpsi : form_noms_in_base (N := NBase) psi) (base : NOM TotalSet) (hb : nom_in_base (N := NBase) base) :
    Proof.all_noms_in_base NBase (pf.eliminate_aliens hpsi base hb pf.proof_noms) :=
  Proof.all_noms_in_base_eliminate_go hpsi base hb pf.proof_noms pf (by
    intro k hk
    exact Or.inl hk)

lemma Proof.form_noms_in_base_of_eliminate_aliens (NBase : Set Nat) {psi : Form TotalSet} (pf : @Proof TotalSet psi)
    (hpsi : form_noms_in_base (N := NBase) psi) (base : NOM TotalSet) (hb : nom_in_base (N := NBase) base) :
    forall  chi  in  (pf.eliminate_aliens hpsi base hb pf.proof_noms).formulasIn,
      form_noms_in_base (N := NBase) chi := by
  intro chi hchi j hj
  let pf' := pf.eliminate_aliens hpsi base hb pf.proof_noms
  have hAll := Proof.all_noms_in_base_eliminate_aliens pf hpsi base hb
  exact hAll j (Proof.mem_formulasIn_of_list_noms pf' chi hchi hj)

lemma inv_t_impl {a b : Form TotalSet} (ha : form_noms_in_base (N := NBase) a) (hb : form_noms_in_base (N := NBase) b) :
    ((@Form.inv_t NBase) (a  -->  b)) = ((@Form.inv_t NBase) a)  -->  ((@Form.inv_t NBase) b) := by
  apply total_inj'
  simp only [Form.total, inv_t_eq_of_range' (form_noms_in_base_impl (N := NBase) ha hb),
    inv_t_eq_of_range' ha, inv_t_eq_of_range' hb]

lemma inv_t_box {a : Form TotalSet} (ha : form_noms_in_base (N := NBase) a) :
    ((@Form.inv_t NBase) ([]  a)) = []  ((@Form.inv_t NBase) a) := by
  apply total_inj'
  simp only [Form.total, inv_t_eq_of_range' (form_noms_in_base_box (N := NBase) ha), inv_t_eq_of_range' ha]

lemma inv_t_bind {v : SVAR} {a : Form TotalSet} (ha : form_noms_in_base (N := NBase) a) :
    ((@Form.inv_t NBase) (all v, a)) = all v, ((@Form.inv_t NBase) a) := by
  apply total_inj'
  simp only [Form.total, inv_t_eq_of_range' (form_noms_in_base_bind (N := NBase) ha), inv_t_eq_of_range' ha]

lemma form_noms_in_base_impl_left {a b : Form TotalSet} (h : form_noms_in_base (N := NBase) (a  -->  b)) :
    form_noms_in_base (N := NBase) a := by
  intro j hj
  exact h j (by
    rw [ <-  occurs_list_noms]
    simp only [Form.list_noms, nom_occurs, Bool.or_eq_true, List.mem_dedup, List.mem_merge]
    exact Or.inl ((occurs_list_noms (phi := a)).mpr hj))

lemma form_noms_in_base_impl_right {a b : Form TotalSet} (h : form_noms_in_base (N := NBase) (a  -->  b)) :
    form_noms_in_base (N := NBase) b := by
  intro j hj
  exact h j (by
    rw [ <-  occurs_list_noms]
    simp only [Form.list_noms, nom_occurs, Bool.or_eq_true, List.mem_dedup, List.mem_merge]
    exact Or.inr ((occurs_list_noms (phi := b)).mpr hj))

/-- Nominal substitution for a non-free variable is the identity. -/
lemma subst_nom_notfree {N : Set Nat} {a : Form N} {s : NOM N} {v : SVAR}
    (h : is_free v a = false) : a[s // v] = a := by
  induction a with
  | svar z =>
      simp only [is_free, beq_eq_false_iff_ne, ne_eq] at h
      simp only [subst_nom]
      rw [if_neg h]
  | impl p q ihp ihq =>
      simp only [is_free, Bool.or_eq_false_iff] at h
      simp only [subst_nom, ihp h.1, ihq h.2]
  | box p ih =>
      simp only [is_free] at h
      simp only [subst_nom, ih h]
  | bind w p ih =>
      simp only [subst_nom]
      by_cases hvw : v = w
      * rw [if_pos hvw]
      * rw [if_neg hvw]
        have hp : is_free v p = false := by
          by_cases hf : is_free v p = true
          * simp only [is_free, hf, Bool.and_true] at h
            simp only [bne_eq_false_iff_eq] at h
            exact absurd h.symm hvw
          * simpa using hf
        rw [ih hp]
  | _ => rfl

/-- If `v` occurs free in `a`, the substituted nominal `s` appears in `a[s // v]`. -/
lemma nom_occurs_subst_nom_of_free {N : Set Nat} {a : Form N} {s : NOM N} {v : SVAR}
    (h : is_free v a = true) : nom_occurs s (a[s // v]) = true := by
  induction a with
  | svar z =>
      simp only [is_free, beq_iff_eq] at h
      subst h
      simp [subst_nom, nom_occurs]
  | impl p q ihp ihq =>
      simp only [is_free, Bool.or_eq_true] at h
      simp only [subst_nom, nom_occurs, Bool.or_eq_true]
      rcases h with hp | hq
      * exact Or.inl (ihp hp)
      * exact Or.inr (ihq hq)
  | box p ih =>
      simp only [is_free] at h
      simp only [subst_nom, nom_occurs]
      exact ih h
  | bind w p ih =>
      simp only [is_free, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      have hvw : v  !=  w := fun e => h.1 e.symm
      simp only [subst_nom, if_neg hvw, nom_occurs]
      exact ih h.2
  | _ => simp [is_free] at h

end Conservativity

-- Peel `total` back through the connectives: a totalized formula matching a
-- connective decomposes into totalizations of `N`-formulas.
lemma total_eq_impl {phi : Form N} {a b : Form TotalSet} (h : phi.total = a  -->  b) :
    exists  a' b' : Form N, a'.total = a  /\  b'.total = b := by
  cases phi with
  | impl l r => simp only [Form.total, Form.impl.injEq] at h; exact <l, r, h.1, h.2>
  | _ => simp [Form.total] at h

lemma total_eq_box {phi : Form N} {a : Form TotalSet} (h : phi.total = []  a) :
    exists  a' : Form N, a'.total = a := by
  cases phi with
  | box r => simp only [Form.total, Form.box.injEq] at h; exact <r, h>
  | _ => simp [Form.total] at h

lemma total_eq_bind {phi : Form N} {v : SVAR} {a : Form TotalSet} (h : phi.total = all v, a) :
    exists  a' : Form N, a'.total = a := by
  cases phi with
  | bind u r => simp only [Form.total, Form.bind.injEq] at h; exact <r, h.2>
  | _ => simp [Form.total] at h

-- On the range of `total`, `inv_t` is a genuine right inverse.
lemma total_in_range {psi : Form TotalSet} (h : exists  a : Form N, a.total = psi) :
    ((@Form.inv_t N) psi).total = psi :=
  Function.invFun_eq h

-- Reconstruction lemmas (no side condition) for the remaining axioms, mirroring
-- `total_ax_k`/`total_ax_q1`/`total_ax_q2_svar` above.
theorem total_ax_name {phi : Form N} {v : SVAR} (h : phi.total = ex v, v) : phi = ex v, v := by
  apply total_inj'
  rw [h]; rfl

theorem total_ax_brcn {phi : Form N} {v : SVAR} {psi : Form TotalSet}
    (h : phi.total = (all v, [] psi)  -->  ([]  all v, psi)) : phi = (all v, [] psi^-)  -->  ([]  all v, psi^-) := by
  obtain <l, r, hl, _> := total_eq_impl h
  obtain <lb, hlb> := total_eq_bind hl
  obtain <lbb, hlbb> := total_eq_box hlb
  apply total_inj'
  rw [h]
  simp only [Form.total, total_in_range <lbb, hlbb>]

-- Peel `total` back through an `iterate_nec` stack (n boxes).
lemma total_eq_iterate_nec :
    forall  {n : Nat} {phi : Form N} {a : Form TotalSet}, phi.total = iterate_nec n a  ->  exists  a' : Form N, a'.total = a := by
  intro n
  induction n with
  | zero => intro phi a h; exact <phi, h>
  | succ k ih =>
      intro phi a h
      have hstep : iterate_nec (k+1) a = []  (iterate_nec k a) := rfl
      rw [hstep] at h
      obtain <b, hb> := total_eq_box h
      exact ih hb

theorem total_ax_nom {phi : Form N} {v : SVAR} {psi : Form TotalSet} {m n : Nat}
    (h : phi.total = (all v, iterate_pos m (v  /\  psi)  -->  iterate_nec n (v  -->  psi))) :
    phi = (all v, iterate_pos m (v  /\  psi^-)  -->  iterate_nec n (v  -->  psi^-)) := by
  obtain <c, hcb> := total_eq_bind h
  obtain <c1, c2, _, hc2> := total_eq_impl hcb
  obtain <d, hd> := total_eq_iterate_nec hc2
  obtain <e1, e2, _, he2> := total_eq_impl hd
  apply total_inj'
  rw [h]
  simp only [Form.total, Form.conj, Form.neg, Form.diamond, total_iterate_pos,
             total_iterate_nec, total_in_range <e2, he2>]

/-- Pull an in-range `TotalSet` derivation back to the base language via `inv_t`.
    Structural induction on the derivation: deduction rules recurse through
    `inv_t_impl`/`inv_t_box`/`inv_t_bind`; axioms reconstruct via the `total_ax_*`
    lemmas.  The `ax_q2_nom` case splits on whether the substituted nominal is in
    the base language (it vanishes exactly when the bound variable is not free). -/
noncomputable def in_range_proof_back {NBase : Set Nat} {psi : Form TotalSet} (pf : @Proof TotalSet psi)
    (hall : forall  chi  in  pf.formulasIn, form_noms_in_base (N := NBase) chi) :
    @Proof NBase ((@Form.inv_t NBase) psi) := by
  revert hall
  induction pf with
  | @tautology a ht =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) a := hall a (by simp [Proof.formulasIn])
      apply Proof.tautology
      rw [total_tautology, inv_t_eq_of_range' hbase]
      exact ht
  | @general chi v pf' ih =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) chi :=
        hall (all v, chi) (by simp [Proof.formulasIn])
      have ihp := ih (fun c hc => hall c (by
        simp only [Proof.formulasIn, List.mem_cons]; exact Or.inr hc))
      rw [inv_t_bind hbase]
      exact general v ihp
  | @necess chi pf' ih =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) chi :=
        hall ([]  chi) (by simp [Proof.formulasIn])
      have ihp := ih (fun c hc => hall c (by
        simp only [Proof.formulasIn, List.mem_cons]; exact Or.inr hc))
      rw [inv_t_box hbase]
      exact necess ihp
  | @mp a b pf1 pf2 ih1 ih2 =>
      intro hall
      have hab : form_noms_in_base (N := NBase) (a  -->  b) :=
        hall (a  -->  b) (by
          simp only [Proof.formulasIn, List.mem_append, List.mem_cons]
          exact Or.inl (Or.inr (mem_formulasIn_self pf1)))
      have ha : form_noms_in_base (N := NBase) a :=
        form_noms_in_base_impl_left hab
      have hb : form_noms_in_base (N := NBase) b :=
        form_noms_in_base_impl_right hab
      have ihp1 := ih1 (fun c hc => hall c (by
        simp only [Proof.formulasIn, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr hc)))
      have ihp2 := ih2 (fun c hc => hall c (by
        simp only [Proof.formulasIn, List.mem_append, List.mem_cons]
        exact Or.inr hc))
      rw [inv_t_impl ha hb] at ihp1
      exact mp ihp1 ihp2
  | @ax_k a b =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) ([] (a  -->  b)  -->  ([] a  -->  [] b)) :=
        hall _ (by simp [Proof.formulasIn])
      rw [total_ax_k (inv_t_eq_of_range' hbase)]
      exact ax_k
  | @ax_q1 a b v p =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) ((all v, a  -->  b)  -->  (a  -->  all v, b)) :=
        hall _ (by simp [Proof.formulasIn])
      have hab : form_noms_in_base (N := NBase) (a  -->  b) :=
        form_noms_in_base_impl_left hbase
      have ha : form_noms_in_base (N := NBase) a :=
        form_noms_in_base_impl_left hab
      rw [total_ax_q1 (inv_t_eq_of_range' hbase)]
      apply ax_q1
      rw [ <-  total_is_free, inv_t_eq_of_range' ha]
      exact p
  | @ax_q2_svar a v s p =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) ((all v, a)  -->  a[s // v]) :=
        hall _ (by simp [Proof.formulasIn])
      have ha : form_noms_in_base (N := NBase) a :=
        form_noms_in_base_impl_left hbase
      rw [total_ax_q2_svar (inv_t_eq_of_range' hbase)]
      apply ax_q2_svar
      rw [ <-  total_is_substable, inv_t_eq_of_range' ha]
      exact p
  | @ax_q2_nom a v s =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) ((all v, a)  -->  a[s // v]) :=
        hall _ (by simp [Proof.formulasIn])
      have ha : form_noms_in_base (N := NBase) a :=
        form_noms_in_base_impl_left hbase
      have heq : ((@Form.inv_t NBase) ((all v, a)  -->  a[s // v])).total = (all v, a)  -->  a[s // v] :=
        inv_t_eq_of_range' hbase
      by_cases hfree : is_free v a = true
      * have hsocc : nom_occurs s (a[s // v]) = true := nom_occurs_subst_nom_of_free hfree
        have hslist : s  in  (a[s // v]).list_noms := (occurs_list_noms (phi := a[s // v])).mp hsocc
        have hs : nom_in_base (N := NBase) s :=
          (form_noms_in_base_impl_right hbase) s hslist
        rw [total_ax_q2_nom ha hs heq]
        exact ax_q2_nom ((@Form.inv_t NBase) a) v (NOM.fromTotal s hs)
      * have hnf : is_free v a = false := by simpa using hfree
        have hav : a[s // v] = a := subst_nom_notfree hnf
        rw [hav] at heq  |- 
        rw [total_ax_q2_nom_end ha heq]
        have hnf' : is_free v ((@Form.inv_t NBase) a) = false := by
          rw [ <-  total_is_free, inv_t_eq_of_range' ha]; exact hnf
        exact iff_mp (all_iff_notfree hnf')
  | @ax_name v =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) (ex v, v) :=
        hall _ (by simp [Proof.formulasIn])
      rw [total_ax_name (inv_t_eq_of_range' hbase)]
      exact ax_name v
  | @ax_nom a v m n =>
      intro hall
      have hbase : form_noms_in_base (N := NBase)
          (all v, iterate_pos m (v  /\  a)  -->  iterate_nec n (v  -->  a)) :=
        hall _ (by simp [Proof.formulasIn])
      rw [total_ax_nom (inv_t_eq_of_range' hbase)]
      exact ax_nom m n
  | @ax_brcn a v =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) ((all v, []  a)  -->  ([]  all v, a)) :=
        hall _ (by simp [Proof.formulasIn])
      rw [total_ax_brcn (inv_t_eq_of_range' hbase)]
      exact ax_brcn

noncomputable def pf_extended {phi : Form N} (hN : N.Nonempty) :  |-  phi iff  |-  phi.total := by
  apply TypeIff.intro
  . intro pf
    induction pf with
    | tautology =>
        apply Proof.tautology
        rw [ <- total_tautology]
        assumption
    | ax_k =>
        apply Proof.ax_k
    | ax_q1 a b p =>
        apply Proof.ax_q1
        rw [total_is_free]; exact p
    | ax_q2_svar a v s p =>
        simp [Form.total, total_subst_svar']
        apply Proof.ax_q2_svar
        rw [total_is_substable]; exact p
    | ax_q2_nom =>
        simp [Form.total, total_subst_nom]
        apply Proof.ax_q2_nom
    | ax_name =>
        apply Proof.ax_name
    | ax_nom  =>
        simp [Form.total, total_iterate_pos, total_iterate_nec]
        apply Proof.ax_nom
    | ax_brcn =>
        apply Proof.ax_brcn
    | mp   =>
        apply Proof.mp
        repeat assumption
    | general =>
        apply Proof.general
        assumption
    | necess  =>
        apply Proof.necess
        assumption
  . intro pf
    -- Blackburn pipeline (F4): `phi.total` has only base nominals, so eliminate the
    -- alien nominals introduced inside `pf` (F2), pull the resulting in-range
    -- derivation back to the base language (F3), and rewrite `(phi.total)^- = phi`.
    have hpsi : form_noms_in_base (N := N) phi.total := form_noms_in_base_total phi
    have result :=
      in_range_proof_back
        (pf.eliminate_aliens hpsi (base_nom_total hN) (base_nom_total_in_base hN) pf.proof_noms)
        (Proof.form_noms_in_base_of_eliminate_aliens N pf hpsi
          (base_nom_total hN) (base_nom_total_in_base hN))
    rwa [total_inv_is_inv phi] at result

/-- Totalization distributes over conjunction. -/
lemma total_conj {a b : Form N} : (a  /\  b).total = a.total  /\  b.total := by
  simp [Form.conj, Form.neg, Form.total]

/-- A conjunction of `Set.total Gamma`-members is itself the totalization of a
    conjunction of `Gamma`-members.  Returns the base list as data (via choice) so it
    can feed the `SyntacticConsequence` Sigma-type. -/
noncomputable def base_conjunction {Gamma : Set (Form N)} (L : List (Set.total Gamma)) :
    { L' : List Gamma // conjunction (Set.total Gamma) L = (conjunction Gamma L').total } := by
  induction L with
  | nil => exact <[], by simp [conjunction, Form.total]>
  | cons h t ih =>
      obtain <L', hL'> := ih
      have hspec := h.2.choose_spec
      exact <<h.2.choose, hspec.1> :: L',
        (congrArg_2 Form.conj hspec.2 hL').trans total_conj.symm>

/-- **Backward conservativity on `SyntacticConsequence`.**  A totalized
    consequence `Set.total Gamma  |-  phi.total` pulls back to `Gamma  |-  phi` (needs `N` nonempty
    to eliminate alien nominals via `pf_extended`). -/
noncomputable def syntactic_conservativity {Gamma : Set (Form N)} {phi : Form N}
    (hN : N.Nonempty) (h : (Set.total Gamma)  |-  phi.total) : Gamma  |-  phi := by
  obtain <L, pf> := h
  obtain <L', hL'> := base_conjunction L
  rw [hL'] at pf
  have pf' :  |-  ((conjunction Gamma L'  -->  phi).total) := pf
  exact <L', (pf_extended hN).mpr pf'>
