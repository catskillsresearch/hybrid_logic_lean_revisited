import Hybrid.Proof
import Hybrid.Substitutions
import Hybrid.ProofUtils
import Hybrid.Truth

open Proof

def Form.total : Form N → Form TotalSet
  | .bttm     => Form.bttm
  | .prop p   => Form.prop p
  | .svar v   => Form.svar v
  | .nom i    => Form.nom ⟨i.1.1, trivial⟩
  | .impl ψ χ => Form.impl ψ.total χ.total
  | .box ψ    => Form.box ψ.total
  | .bind v ψ => Form.bind v ψ.total

theorem total_inj' {φ ψ : Form N} : φ.total = ψ.total → φ = ψ := by
  induction φ generalizing ψ with
  | impl a b ih1 ih2 =>
        cases ψ with
        | impl c d => simp [Form.total, -implication_disjunction]
                      intros
                      apply And.intro <;> (first | apply ih1 | apply ih2) <;> assumption
        | _    => simp [Form.total]
  | box a ih | bind v a ih =>
      cases ψ with
      | box b    => simp [Form.total, -implication_disjunction]; try apply ih
      | bind u b => simp [Form.total, -implication_disjunction];
                    try (intro; simp only [*, true_and]; apply ih)
      | _     => simp  [Form.total]
  | _    => cases ψ <;> simp [Form.total, NOM_eq, -implication_disjunction] <;>
                        (intros; apply Subtype.eq; assumption)

lemma total_inj {N : Set ℕ} : (@Form.total N).Injective := by
  unfold Function.Injective
  apply total_inj'

noncomputable def Form.inv_t : Form TotalSet → Form N := Function.invFun Form.total

lemma total_inv_is_inv : Function.LeftInverse (@Form.inv_t N) Form.total := by
  apply Function.leftInverse_invFun
  apply total_inj'

notation φ"⁺" => Form.total φ
notation φ"⁻" => Form.inv_t φ

/-- The image of a base-language set under `Form.total`. -/
noncomputable def Set.total (Γ : Set (Form N)) : Set (Form TotalSet) :=
  {ψ | ∃ φ ∈ Γ, ψ = φ.total}

/-- Restrict a `TotalSet` model to the nominal type `N` (same world, same `Vₚ`, nominals
    embedded via `Subtype`).  Used to pull a completed `TotalSet` model back to `Model N`. -/
noncomputable def Model.ofTotal (M : Model TotalSet) : Model N where
  W := M.W
  R := M.R
  Vₚ := M.Vₚ
  Vₙ := fun i => M.Vₙ ⟨i.letter, trivial⟩

/-- Satisfaction commutes with `Form.total` under `Model.ofTotal`. -/
theorem sat_total (M : Model TotalSet) (s : M.W) (g : I M.W) (φ : Form N) :
    (@Sat TotalSet M s g φ.total) ↔ (@Sat N (Model.ofTotal M) s g φ) := by
  induction φ generalizing s g with
  | bttm => simp [Form.total, Model.ofTotal, Sat]
  | prop p => simp [Form.total, Model.ofTotal, Sat]; rfl
  | svar v => simp [Form.total, Sat]; rfl
  | nom i => simp [Form.total, Model.ofTotal, Sat]
  | impl a b iha ihb => simp [Form.total, Model.ofTotal, Sat, iha, ihb]
  | box a ih =>
      simp only [Form.total, Model.ofTotal, Sat]
      constructor
      · intro h s' hs'
        exact (ih s' g).mp (h s' hs')
      · intro h s' hs'
        exact (ih s' g).mpr (h s' hs')
  | bind x a ih =>
      simp only [Form.total, Model.ofTotal, Sat]
      constructor
      · intro h g' hg'
        exact (ih s g').mp (h g' hg')
      · intro h g' hg'
        exact (ih s g').mpr (h g' hg')

theorem total_impl {φ : Form N} : φ⁺ = (ψ ⟶ χ) → φ = (ψ⁻ ⟶ χ⁻) := by
  intro h
  cases φ with
  | impl φ ψ =>
    simp [Form.total] at h ⊢
    apply And.intro
    . rw [←total_inv_is_inv φ]
      exact congr_arg (@Form.inv_t N) h.1
    . rw [←total_inv_is_inv ψ]
      exact congr_arg (@Form.inv_t N) h.2
  | _ => simp [Form.total] at *

theorem total_box {φ : Form N} : φ⁺ = □ ψ → φ = □ ψ⁻ := by
  intro h
  cases φ with
  | box φ =>
    simp [Form.total] at h ⊢
    rw [←total_inv_is_inv φ]
    exact congr_arg (@Form.inv_t N) h
  | _ => simp [Form.total] at *

theorem total_bind {φ : Form N} : φ⁺ = (all x, ψ) → φ = (all x, ψ⁻) := by
  intro h
  cases φ with
  | bind x φ =>
    simp [Form.total] at h ⊢
    apply And.intro
    . exact h.1
    . rw [←total_inv_is_inv φ]
      exact congr_arg (@Form.inv_t N) h.2
  | _ => simp [Form.total] at *

lemma total_subst_svar' {φ : Form N} {x y : SVAR} : (φ[y // x]).total = (φ.total)[y // x] := by
  induction φ with
  | svar z => by_cases h : x = z <;> simp [subst_svar, Form.total, h, -implication_disjunction]
  | impl φ ψ ih1 ih2 => simp only [subst_svar, Form.total, ih1, ih2]
  | box φ ih => simp only [subst_svar, Form.total, ih]
  | bind v φ ih => by_cases h : x = v <;> simp [subst_svar, Form.total, ih, h, -implication_disjunction]
  | _ => rfl

-- The image of `Form.total` is closed under taking subformulas through a
-- variable substitution: substituting an SVAR never touches nominals, so if
-- `ψ[y//x]` arises from an `N`-formula then so does `ψ`.
lemma range_of_subst {ψ : Form TotalSet} {y x : SVAR} : (∃ χ : Form N, χ.total = ψ[y // x]) → ∃ χ' : Form N, χ'.total = ψ := by
  induction ψ with
  | bttm => intro _; exact ⟨Form.bttm, rfl⟩
  | prop p => intro _; exact ⟨Form.prop p, rfl⟩
  | svar z => intro _; exact ⟨Form.svar z, rfl⟩
  | nom i => intro h; exact h
  | impl a b iha ihb =>
      intro ⟨χ, hχ⟩
      cases χ with
      | impl c d =>
          simp only [Form.total, subst_svar, Form.impl.injEq] at hχ
          obtain ⟨c', hc'⟩ := iha ⟨c, hχ.1⟩
          obtain ⟨d', hd'⟩ := ihb ⟨d, hχ.2⟩
          exact ⟨c' ⟶ d', by simp only [Form.total, hc', hd']⟩
      | _ => simp [Form.total, subst_svar] at hχ
  | box a ih =>
      intro ⟨χ, hχ⟩
      cases χ with
      | box c =>
          simp only [Form.total, subst_svar, Form.box.injEq] at hχ
          obtain ⟨c', hc'⟩ := ih ⟨c, hχ⟩
          exact ⟨□ c', by simp only [Form.total, hc']⟩
      | _ => simp [Form.total, subst_svar] at hχ
  | bind z a ih =>
      intro ⟨χ, hχ⟩
      by_cases hxz : x = z
      · simp only [subst_svar, hxz] at hχ
        exact ⟨χ, hχ⟩
      · simp only [subst_svar, hxz] at hχ
        cases χ with
        | bind w c =>
            simp only [Form.total] at hχ
            injection hχ with hw hc
            obtain ⟨c', hc'⟩ := ih ⟨c, hc⟩
            exact ⟨Form.bind z c', by simp only [Form.total, hc']⟩
        | _ => simp [Form.total] at hχ

lemma inv_t_subst {ψ : Form TotalSet} {y x : SVAR} (h : ∃ χ : Form N, χ.total = ψ) : (@Form.inv_t N) (ψ[y // x]) = ((@Form.inv_t N) ψ)[y // x] := by
  obtain ⟨χ, rfl⟩ := h
  rw [← total_subst_svar', total_inv_is_inv, total_inv_is_inv]

theorem total_subst_svar {φ : Form N} {x y : SVAR} : φ⁺ = ψ[y//x] → φ = ψ⁻[y//x] := by
  intro h
  have hr : ∃ χ : Form N, χ.total = ψ := range_of_subst ⟨φ, h⟩
  rw [← total_inv_is_inv φ, h, inv_t_subst hr]

theorem total_ax_k {φ : Form N} (h : φ⁺ = □(ψ ⟶ χ) ⟶ (□ψ ⟶ □χ)) : φ = □(ψ⁻ ⟶ χ⁻) ⟶ (□ψ⁻ ⟶ □χ⁻) := by
  cases φ with
  | impl φ_l φ_r =>
      simp [Form.total] at h ⊢
      apply And.intro
      . have hyp := h.1
        clear h
        cases φ_l with
        | box φ_l_b =>
            simp [Form.total] at hyp ⊢
            cases φ_l_b with
            | impl φ_l_b_l φ_l_b_r =>
                apply total_impl
                assumption
            | _ =>  simp [Form.total] at *
        | _ => simp [Form.total] at *
      . have hyp := h.2
        clear h
        cases φ_r with
        | impl φ_r_l φ_r_r =>
            simp [Form.total] at hyp ⊢
            apply And.intro
            . apply total_box hyp.1
            . apply total_box hyp.2
        | _ => simp [Form.total] at hyp ⊢
  | _ => simp [Form.total] at *

theorem total_ax_q1 {φ : Form N} {x : SVAR} (h : φ⁺ = (all x, ψ ⟶ χ) ⟶ (ψ ⟶ all x, χ)) : φ = (all x, ψ⁻ ⟶ χ⁻) ⟶ (ψ⁻ ⟶ all x, χ⁻) := by
  cases φ with
  | impl l r =>
      simp [Form.total] at h ⊢
      apply And.intro
      . have h := h.1
        cases l with
        | bind x l =>
            simp [Form.total] at h ⊢
            simp [h]
            apply total_impl h.2
        | _ => simp [Form.total] at *
      . have h := h.2
        cases r with
        | impl rl rr =>
            simp [Form.total] at h ⊢
            apply And.intro
            . rw [←total_inv_is_inv rl]
              exact congr_arg (@Form.inv_t N) h.1
            . apply total_bind h.2
        | _ => simp [Form.total] at h ⊢
  | _ => simp [Form.total] at *

theorem total_ax_q2_svar {φ : Form N} {x y : SVAR} (h : φ⁺ = (all x, ψ) ⟶ ψ[y // x]) : φ = (all x, ψ⁻) ⟶ ψ⁻[y//x] := by
  cases φ with
  | impl l r =>
      simp [Form.total] at h ⊢
      apply And.intro
      . apply total_subst_svar h.2
      . apply total_bind h.1
  | _ => simp [Form.total] at h ⊢




-- Given an `Eval N`, build a Boolean valuation on `Form TotalSet` that mirrors
-- `e` structurally on `⟶`/`⊥` and falls back to `e ∘ inv_t` on atoms.  On the
-- image of `Form.total` (which is entirely in range) this recovers `e` exactly.
noncomputable def evalN_to_T (e : Eval N) : Form TotalSet → Bool
  | .bttm     => false
  | .prop p   => e.f (Form.prop p)
  | .svar v   => e.f (Form.svar v)
  | .nom i    => e.f (Form.inv_t (Form.nom i))
  | .impl ψ χ => !(evalN_to_T e ψ) || (evalN_to_T e χ)
  | .box ψ    => e.f (Form.inv_t (Form.box ψ))
  | .bind x ψ => e.f (Form.inv_t (Form.bind x ψ))

noncomputable def evalT (e : Eval N) : Eval TotalSet where
  f  := evalN_to_T e
  p1 := rfl
  p2 := by
    intro ψ χ
    show (!(evalN_to_T e ψ) || evalN_to_T e χ) = true ↔ _
    cases evalN_to_T e ψ <;> cases evalN_to_T e χ <;> simp

theorem evalT_total {e : Eval N} (φ : Form N) : evalN_to_T e (φ.total) = e.f φ := by
  induction φ with
  | bttm => simp only [Form.total, evalN_to_T, e.p1]
  | prop p => rfl
  | svar v => rfl
  | nom i => show e.f (Form.inv_t ((Form.nom i).total)) = _; rw [total_inv_is_inv]
  | box a _ => show e.f (Form.inv_t ((Form.box a).total)) = _; rw [total_inv_is_inv]
  | bind x a _ => show e.f (Form.inv_t ((Form.bind x a).total)) = _; rw [total_inv_is_inv]
  | impl a b iha ihb =>
      show (!(evalN_to_T e a.total) || evalN_to_T e b.total) = e.f (a ⟶ b)
      rw [iha, ihb]
      have h := e.p2 a b
      cases ha : e.f a <;> cases hb : e.f b <;> cases hab : e.f (a ⟶ b) <;> simp_all

lemma total_tautology {φ : Form N} : Tautology φ ↔ Tautology φ.total := by
  constructor
  · intro h e'
    have gp1 : (fun ψ : Form N => e'.f ψ.total) ⊥ = false := e'.p1
    have gp2 : ∀ ψ χ : Form N, ((fun ψ : Form N => e'.f ψ.total) (ψ ⟶ χ) = true)
        ↔ (¬((fun ψ : Form N => e'.f ψ.total) ψ) = true ∨ ((fun ψ : Form N => e'.f ψ.total) χ) = true) := by
      intro ψ χ
      show e'.f (ψ.total ⟶ χ.total) = true ↔ _
      exact e'.p2 ψ.total χ.total
    exact h ⟨fun ψ => e'.f ψ.total, gp1, gp2⟩
  · intro h e
    have := h (evalT e)
    rw [show (evalT e).f φ.total = evalN_to_T e φ.total from rfl, evalT_total] at this
    exact this

lemma total_subst_nom {φ : Form N} {i : NOM N} {x : SVAR} : (φ[i // x]).total = (φ.total)[⟨i.1.1, trivial⟩ // x] := by
  induction φ with
  | svar z => by_cases h : x = z <;> simp [subst_nom, Form.total, h, -implication_disjunction]
  | impl φ ψ ih1 ih2 => simp only [subst_nom, Form.total, ih1, ih2]
  | box φ ih => simp only [subst_nom, Form.total, ih]
  | bind v φ ih => by_cases h : x = v <;> simp [subst_nom, Form.total, ih, h, -implication_disjunction]
  | _ => rfl

lemma total_diamond {ψ : Form N} : (◇ ψ).total = ◇ (ψ.total) := by
  simp [Form.diamond, Form.neg, Form.total]

lemma total_iterate_pos {φ : Form N} : (iterate_pos n φ).total = iterate_pos n (φ.total) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show ◇ ((iterate_pos k φ).total) = ◇ (iterate_pos k (φ.total))
      rw [ih]

lemma total_iterate_nec {φ : Form N} : (iterate_nec n φ).total = iterate_nec n (φ.total) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      show □ ((iterate_nec k φ).total) = □ (iterate_nec k (φ.total))
      rw [ih]

-- Totalization only renames nominals, so it preserves the free-variable and
-- substitutability predicates (both of which depend solely on the SVAR structure).
lemma total_is_free {φ : Form N} {x : SVAR} : is_free x φ.total = is_free x φ := by
  induction φ with
  | impl a b iha ihb => simp only [Form.total, is_free, iha, ihb]
  | box a ih => simp only [Form.total, is_free, ih]
  | bind y a ih => simp only [Form.total, is_free, ih]
  | _ => rfl

lemma total_is_substable {φ : Form N} {s v : SVAR} : is_substable φ.total s v = is_substable φ s v := by
  induction φ with
  | impl a b iha ihb => simp only [Form.total, is_substable, iha, ihb]
  | box a ih => simp only [Form.total, is_substable, ih]
  | bind y a ih => simp only [Form.total, is_substable, total_is_free, ih]
  | _ => rfl

-- Generalizing a nominal constant `i` to a fresh variable `x` preserves theoremhood
-- (Oltean's Lemma 4.1.6).  Rather than re-running the structural induction, we obtain it
-- from the already-proven universal version `generalize_constants` (`⊢ φ → ⊢ all x, φ[x // i]`)
-- by instantiating the universal back at `x`: since `x` is fresh, `φ[x // i]` is substable
-- for `x`, and `(φ[x // i])[x // x] = φ[x // i]`.
noncomputable def l416 {φ : Form N} {x : SVAR} (i : NOM N) (pf : ⊢ φ) (h : pf.fresh_var x) : ⊢ (φ[x // i]) := by
  have hcon : pf.contains φ := by unfold Proof.contains; simp only [beq_self_eq_true, Bool.true_or]
  have hx : x ≥ φ.new_var := h φ hcon
  have gc := generalize_constants i hx pf
  have hsub : is_substable (φ[x // i]) x x := new_var_subst hx
  have key := mp (ax_q2_svar (φ[x // i]) x x hsub) gc
  rwa [subst_self_is_self] at key

-- ===========================================================================
-- Helpers for the backward direction of `pf_extended` (conservativity).
-- ===========================================================================

/-- Embed a base-language nominal into `TotalSet`. -/
noncomputable def NOM.toTotal {N : Set ℕ} (j : NOM N) : NOM TotalSet := ⟨j.letter, trivial⟩

/-- Reconstruct a base-language nominal from a `TotalSet` one whose letter lies in `N`. -/
noncomputable def NOM.fromTotal {N : Set ℕ} (j : NOM TotalSet) (hj : (j.letter : ℕ) ∈ N) : NOM N :=
  ⟨j.letter, hj⟩

lemma NOM.toTotal_total {N : Set ℕ} (j : NOM N) :
    (Form.nom j).total = Form.nom (NOM.toTotal j) := by
  simp [Form.total, NOM.toTotal, NOM_eq]

lemma NOM.fromTotal_total {N : Set ℕ} (j : NOM TotalSet) (hj : (j.letter : ℕ) ∈ N) :
    (Form.nom (NOM.fromTotal j hj)).total = Form.nom j := by
  simp [Form.total, NOM.fromTotal, NOM_eq]

def nom_in_base {N : Set ℕ} (j : NOM TotalSet) : Prop := (j.letter : ℕ) ∈ N

lemma NOM.toTotal_fromTotal {N : Set ℕ} {j : NOM TotalSet} (hj : nom_in_base (N := N) j) :
    NOM.toTotal (NOM.fromTotal j hj) = j := by
  apply NOM_eq.mpr; rfl

def form_noms_in_base {N : Set ℕ} (ψ : Form TotalSet) : Prop :=
  ∀ j ∈ ψ.list_noms, nom_in_base (N := N) j

lemma form_noms_in_base_nom {N : Set ℕ} {i : NOM TotalSet} (hi : nom_in_base (N := N) i) :
    form_noms_in_base (N := N) (Form.nom i) := by
  intro j hj; simp [Form.list_noms] at hj; subst hj; exact hi

lemma form_noms_in_base_impl {N : Set ℕ} {a b : Form TotalSet}
    (ha : form_noms_in_base (N := N) a) (hb : form_noms_in_base (N := N) b) :
    form_noms_in_base (N := N) (a ⟶ b) := by
  intro j hj
  rw [← occurs_list_noms] at hj
  simp only [Form.list_noms, nom_occurs, Bool.or_eq_true, List.mem_dedup, List.mem_merge] at hj
  rcases hj with h | h
  · exact ha j (by rw [← occurs_list_noms]; exact h)
  · exact hb j (by rw [← occurs_list_noms]; exact h)

lemma form_noms_in_base_box {N : Set ℕ} {a : Form TotalSet} (ha : form_noms_in_base (N := N) a) :
    form_noms_in_base (N := N) (□ a) := ha

lemma form_noms_in_base_bind {N : Set ℕ} {v : SVAR} {a : Form TotalSet} (ha : form_noms_in_base (N := N) a) :
    form_noms_in_base (N := N) (all v, a) := ha

/-- If every nominal letter lies in `N`, the formula is in the image of `Form.total`. -/
lemma range_of_form {N : Set ℕ} {ψ : Form TotalSet} (h : form_noms_in_base (N := N) ψ) :
    ∃ χ : Form N, χ.total = ψ := by
  induction ψ with
  | bttm => exact ⟨Form.bttm, rfl⟩
  | prop p => exact ⟨Form.prop p, rfl⟩
  | svar v => exact ⟨Form.svar v, rfl⟩
  | nom i =>
      have hi := h i (by simp [Form.list_noms])
      exact ⟨Form.nom (NOM.fromTotal i hi), NOM.fromTotal_total i hi⟩
  | impl a b iha ihb =>
      obtain ⟨a', ha'⟩ := iha (fun j (hj : j ∈ a.list_noms) => h j (by
        have this := (occurs_list_noms (φ := a)).mpr hj
        rw [← occurs_list_noms]
        simp [Form.list_noms, nom_occurs, this, Bool.or_true]))
      obtain ⟨b', hb'⟩ := ihb (fun j (hj : j ∈ b.list_noms) => h j (by
        have this := (occurs_list_noms (φ := b)).mpr hj
        rw [← occurs_list_noms]
        simp [Form.list_noms, nom_occurs, this, Bool.true_or]))
      exact ⟨a' ⟶ b', by simp [Form.total, ha', hb']⟩
  | box a ih =>
      obtain ⟨a', ha'⟩ := ih h
      exact ⟨□ a', by simp [Form.total, ha']⟩
  | bind v a ih =>
      obtain ⟨a', ha'⟩ := ih h
      exact ⟨all v, a', by simp [Form.total, ha']⟩

lemma inv_t_eq_of_range' {N : Set ℕ} {ψ : Form TotalSet} (h : form_noms_in_base (N := N) ψ) :
    ((@Form.inv_t N) ψ).total = ψ := by
  obtain ⟨χ, hχ⟩ := range_of_form h
  rw [← hχ, total_inv_is_inv]

lemma subst_nom_toTotal {N : Set ℕ} {s : NOM TotalSet} (hs : nom_in_base (N := N) s) (v : SVAR)
    (a : Form TotalSet) :
    a[NOM.toTotal (NOM.fromTotal s hs) // v] = a[s // v] :=
  congrArg (fun n : NOM TotalSet => a[n // v]) (NOM.toTotal_fromTotal hs)

theorem total_subst_nom_pullback {N : Set ℕ} {a : Form TotalSet} {s : NOM TotalSet} {v : SVAR}
    (ha : form_noms_in_base (N := N) a) (hs : nom_in_base (N := N) s) {φ : Form N}
    (h : Form.total φ = a[s // v]) :
    φ = ((@Form.inv_t N) a)[NOM.fromTotal s hs // v] := by
  apply total_inj'
  rw [h]
  rw [total_subst_nom, inv_t_eq_of_range' ha]
  exact subst_nom_toTotal hs v a

theorem total_ax_q2_nom {N : Set ℕ} {φ : Form N} {v : SVAR} {a : Form TotalSet} {s : NOM TotalSet}
    (ha : form_noms_in_base (N := N) a) (hs : nom_in_base (N := N) s)
    (h : φ⁺ = (all v, a) ⟶ a[s // v]) :
    φ = (all v, ((@Form.inv_t N) a)) ⟶ ((@Form.inv_t N) a)[NOM.fromTotal s hs // v] := by
  cases φ with
  | impl l r =>
      simp only [Form.total] at h ⊢
      injection h with h1 h2
      rw [total_bind (φ := l) h1]
      rw [total_subst_nom_pullback ha hs h2]
  | _ => simp [Form.total] at h

theorem total_ax_q2_nom_end {N : Set ℕ} {φ : Form N} {v : SVAR} {a : Form TotalSet}
    (ha : form_noms_in_base (N := N) a) (h : φ⁺ = (all v, a) ⟶ a) :
    φ = (all v, ((@Form.inv_t N) a)) ⟶ ((@Form.inv_t N) a) := by
  cases φ with
  | impl l r =>
      simp only [Form.total] at h ⊢
      injection h with h1 h2
      rw [total_bind (φ := l) h1]
      apply total_inj'
      simp only [Form.total, h2, inv_t_eq_of_range' ha]
  | _ => simp [Form.total] at h

-- ===========================================================================
-- F2 / F3: alien-nominal elimination + in-range proof pullback (Blackburn).
-- ===========================================================================

section Conservativity
variable {NBase : Set ℕ}
open Classical

/-- Every base-language formula has only base nominal letters after totalization. -/
lemma form_noms_in_base_total (φ : Form NBase) : form_noms_in_base (N := NBase) φ.total := by
  induction φ with
  | nom i =>
      intro j hj
      have hj' := List.mem_singleton.mp (by simpa [Form.list_noms, Form.total] using hj)
      subst hj'
      simpa [nom_in_base, NOM.toTotal] using i.letter.2
  | impl a b iha ihb => exact form_noms_in_base_impl (N := NBase) iha ihb
  | box a ih => exact form_noms_in_base_box (N := NBase) ih
  | bind v a ih => exact form_noms_in_base_bind (N := NBase) ih
  | bttm | prop _ | svar _ => intro j hj; simp [Form.list_noms, Form.total] at hj

/-- `φ[new // old]` leaves `φ` unchanged when `old` does not occur
    (`nom_subst_nom φ new old` replaces `old` with `new`). -/
lemma nom_subst_nom_nocc {ψ : Form TotalSet} {new old : NOM TotalSet}
    (h : nom_occurs old ψ = false) : nom_subst_nom ψ new old = ψ := by
  induction ψ with
  | nom a =>
      by_cases heq : a = old
      · exfalso
        exact Bool.eq_false_iff.mp h (by simp [nom_occurs, heq])
      · simp [nom_subst_nom, heq]
  | impl a b iha ihb =>
      simp [nom_occurs, nom_subst_nom, Bool.or_eq_false_iff] at h ⊢
      simp [iha h.1, ihb h.2]
  | box a ih => simp [nom_occurs, nom_subst_nom] at h ⊢; exact ih h
  | bind v a ih => simp [nom_occurs, nom_subst_nom] at h ⊢; exact ih h
  | _ => rfl

lemma nom_occurs_false_of_form_noms_in_base {ψ : Form TotalSet} (hψ : form_noms_in_base (N := NBase) ψ)
    {j : NOM TotalSet} (hjb : ¬nom_in_base (N := NBase) j) : nom_occurs j ψ = false := by
  by_cases h : nom_occurs j ψ = true
  · exfalso
    have hocc : nom_occurs j ψ := h ▸ rfl
    exact hjb (hψ j ((occurs_list_noms (φ := ψ)).mp hocc))
  · rw [← Bool.eq_false_eq_not_eq_true]
    exact h

def Proof.all_noms_in_base (NBase : Set ℕ) {ψ : Form TotalSet} (pf : @Proof TotalSet ψ) : Prop :=
  ∀ j ∈ pf.proof_noms, nom_in_base (N := NBase) j

lemma Proof.all_noms_in_base_root (NBase : Set ℕ) {ψ : Form TotalSet} (pf : @Proof TotalSet ψ)
    (h : Proof.all_noms_in_base NBase pf) : form_noms_in_base (N := NBase) ψ := by
  intro j hj
  exact h j (by
    simp only [Proof.proof_noms, List.mem_dedup, List.mem_flatMap]
    refine ⟨ψ, ?_, hj⟩
    cases pf <;> simp [Proof.formulasIn])

lemma Proof.mem_formulasIn_of_list_noms {ψ : Form TotalSet} (pf : @Proof TotalSet ψ) (χ : Form TotalSet)
    (hχ : χ ∈ pf.formulasIn) {j : NOM TotalSet} (hj : j ∈ χ.list_noms) :
    j ∈ pf.proof_noms := by
  simp only [Proof.proof_noms, List.mem_dedup, List.mem_flatMap]
  exact ⟨χ, hχ, hj⟩

lemma Proof.form_noms_in_base_of_all_noms (NBase : Set ℕ) {ψ : Form TotalSet} (pf : @Proof TotalSet ψ)
    (h : Proof.all_noms_in_base NBase pf) : ∀ χ ∈ pf.formulasIn, form_noms_in_base (N := NBase) χ := by
  intro χ hχ j hj
  exact h j (Proof.mem_formulasIn_of_list_noms pf χ hχ hj)

noncomputable def base_nom_total (hN : NBase.Nonempty) : NOM TotalSet :=
  ⟨Classical.choose hN, trivial⟩

lemma base_nom_total_in_base (hN : NBase.Nonempty) : nom_in_base (N := NBase) (base_nom_total hN) :=
  Classical.choose_spec hN

/-- Globally rename one alien nominal to a fixed base nominal throughout a derivation. -/
noncomputable def Proof.eliminate_one_alien {ψ : Form TotalSet} (pf : @Proof TotalSet ψ)
    (hψ : form_noms_in_base (N := NBase) ψ) (j base : NOM TotalSet) (hjb : ¬nom_in_base (N := NBase) j)
    (hb : nom_in_base (N := NBase) base) : @Proof TotalSet ψ := by
  have hnocc := nom_occurs_false_of_form_noms_in_base hψ hjb
  exact nom_subst_nom_nocc (new := base) (old := j) hnocc ▸ rename_constants_fwd base j pf

/-- Iterated alien elimination over `proof_noms`; the root formula is unchanged. -/
noncomputable def Proof.eliminate_aliens {ψ : Form TotalSet} (pf : @Proof TotalSet ψ)
    (hψ : form_noms_in_base (N := NBase) ψ) (base : NOM TotalSet) (_hb : nom_in_base (N := NBase) base) :
    List (NOM TotalSet) → @Proof TotalSet ψ
  | [] => pf
  | j :: rest =>
      if hjb : nom_in_base (N := NBase) j then
        Proof.eliminate_aliens pf hψ base _hb rest
      else
        have hAlien : ¬nom_in_base (N := NBase) j := fun h => hjb h
        Proof.eliminate_aliens (pf.eliminate_one_alien hψ j base hAlien _hb) hψ base _hb rest

lemma Proof.mem_proof_noms_eliminate_one_alien {ψ : Form TotalSet} (pf : @Proof TotalSet ψ)
    (hψ : form_noms_in_base (N := NBase) ψ) (j base : NOM TotalSet)
    (hAlien : ¬nom_in_base (N := NBase) j) (_hb : nom_in_base (N := NBase) base) {k : NOM TotalSet}
    (hk : k ∈ (pf.eliminate_one_alien hψ j base hAlien _hb).proof_noms) :
    k ∈ pf.proof_noms ∨ k = base := by
  have hnocc := nom_occurs_false_of_form_noms_in_base hψ hAlien
  have hk' : k ∈ (rename_constants_fwd base j pf).proof_noms := by
    simpa [Proof.eliminate_one_alien, hnocc, proof_noms_cast] using hk
  exact mem_proof_noms_rename_constants_fwd (new := base) (old := j) (pf := pf) hk'

lemma Proof.not_mem_proof_noms_eliminate_one_alien {ψ : Form TotalSet} (pf : @Proof TotalSet ψ)
    (hψ : form_noms_in_base (N := NBase) ψ) (j base : NOM TotalSet)
    (hAlien : ¬nom_in_base (N := NBase) j) (_hb : nom_in_base (N := NBase) base) :
    j ∉ (pf.eliminate_one_alien hψ j base hAlien _hb).proof_noms := by
  have hnocc := nom_occurs_false_of_form_noms_in_base hψ hAlien
  intro h
  have h' : j ∈ (rename_constants_fwd base j pf).proof_noms := by
    simpa [Proof.eliminate_one_alien, hnocc, proof_noms_cast] using h
  have hne : base ≠ j := fun heq => hAlien (heq ▸ _hb)
  exact not_mem_proof_noms_rename_constants_fwd (new := base) (old := j) (pf := pf) hne h'

lemma Proof.all_noms_in_base_eliminate_go {ψ : Form TotalSet}
    (hψ : form_noms_in_base (N := NBase) ψ) (base : NOM TotalSet) (hb : nom_in_base (N := NBase) base) :
    ∀ (L : List (NOM TotalSet)) (pf' : @Proof TotalSet ψ),
      (∀ k, k ∈ pf'.proof_noms → k ∈ L ∨ nom_in_base (N := NBase) k) →
      Proof.all_noms_in_base NBase (pf'.eliminate_aliens hψ base hb L) := by
  intro L pf' hsub
  induction L generalizing pf' with
  | nil =>
      intro k hk
      simp only [Proof.all_noms_in_base, Proof.eliminate_aliens] at hk ⊢
      exact (hsub k hk).resolve_left (by simp)
  | cons j rest ih =>
      simp only [Proof.eliminate_aliens]
      split_ifs with hjb
      · exact ih pf' (by
          intro k hk
          rcases hsub k hk with hL | hbk
          · simp only [List.mem_cons] at hL
            rcases hL with (rfl) | hkrest
            · exact Or.inr hjb
            · exact Or.inl hkrest
          · exact Or.inr hbk)
      · have hAlien : ¬nom_in_base (N := NBase) j := fun h => hjb h
        exact ih (pf'.eliminate_one_alien hψ j base hAlien hb) (by
          intro k hk
          by_cases hkbase : nom_in_base (N := NBase) k
          · exact Or.inr hkbase
          · exact Or.inl (by
              have hmem := Proof.mem_proof_noms_eliminate_one_alien pf' hψ j base hAlien hb hk
              have hkpf : k ∈ pf'.proof_noms := by
                rcases hmem with hkpf | hkb
                · exact hkpf
                · exact absurd (hkb ▸ hb) hkbase
              have := hsub k hkpf
              simp only [List.mem_cons, Bool.not_eq_true] at this
              rcases this with hL | hbk
              · rcases hL with hj | hkrest
                · rw [hj] at hk
                  exact absurd hk (Proof.not_mem_proof_noms_eliminate_one_alien pf' hψ j base hAlien hb)
                · exact hkrest
              · exact absurd hbk hkbase))

/-- After eliminating every alien in `proof_noms`, all remaining nominals lie in `N`. -/
lemma Proof.all_noms_in_base_eliminate_aliens {ψ : Form TotalSet} (pf : @Proof TotalSet ψ)
    (hψ : form_noms_in_base (N := NBase) ψ) (base : NOM TotalSet) (hb : nom_in_base (N := NBase) base) :
    Proof.all_noms_in_base NBase (pf.eliminate_aliens hψ base hb pf.proof_noms) :=
  Proof.all_noms_in_base_eliminate_go hψ base hb pf.proof_noms pf (by
    intro k hk
    exact Or.inl hk)

lemma Proof.form_noms_in_base_of_eliminate_aliens (NBase : Set ℕ) {ψ : Form TotalSet} (pf : @Proof TotalSet ψ)
    (hψ : form_noms_in_base (N := NBase) ψ) (base : NOM TotalSet) (hb : nom_in_base (N := NBase) base) :
    ∀ χ ∈ (pf.eliminate_aliens hψ base hb pf.proof_noms).formulasIn,
      form_noms_in_base (N := NBase) χ := by
  intro χ hχ j hj
  let pf' := pf.eliminate_aliens hψ base hb pf.proof_noms
  have hAll := Proof.all_noms_in_base_eliminate_aliens pf hψ base hb
  exact hAll j (Proof.mem_formulasIn_of_list_noms pf' χ hχ hj)

lemma inv_t_impl {a b : Form TotalSet} (ha : form_noms_in_base (N := NBase) a) (hb : form_noms_in_base (N := NBase) b) :
    ((@Form.inv_t NBase) (a ⟶ b)) = ((@Form.inv_t NBase) a) ⟶ ((@Form.inv_t NBase) b) := by
  apply total_inj'
  simp only [Form.total, inv_t_eq_of_range' (form_noms_in_base_impl (N := NBase) ha hb),
    inv_t_eq_of_range' ha, inv_t_eq_of_range' hb]

lemma inv_t_box {a : Form TotalSet} (ha : form_noms_in_base (N := NBase) a) :
    ((@Form.inv_t NBase) (□ a)) = □ ((@Form.inv_t NBase) a) := by
  apply total_inj'
  simp only [Form.total, inv_t_eq_of_range' (form_noms_in_base_box (N := NBase) ha), inv_t_eq_of_range' ha]

lemma inv_t_bind {v : SVAR} {a : Form TotalSet} (ha : form_noms_in_base (N := NBase) a) :
    ((@Form.inv_t NBase) (all v, a)) = all v, ((@Form.inv_t NBase) a) := by
  apply total_inj'
  simp only [Form.total, inv_t_eq_of_range' (form_noms_in_base_bind (N := NBase) ha), inv_t_eq_of_range' ha]

lemma form_noms_in_base_impl_left {a b : Form TotalSet} (h : form_noms_in_base (N := NBase) (a ⟶ b)) :
    form_noms_in_base (N := NBase) a := by
  intro j hj
  exact h j (by
    rw [← occurs_list_noms]
    simp only [Form.list_noms, nom_occurs, Bool.or_eq_true, List.mem_dedup, List.mem_merge]
    exact Or.inl ((occurs_list_noms (φ := a)).mpr hj))

lemma form_noms_in_base_impl_right {a b : Form TotalSet} (h : form_noms_in_base (N := NBase) (a ⟶ b)) :
    form_noms_in_base (N := NBase) b := by
  intro j hj
  exact h j (by
    rw [← occurs_list_noms]
    simp only [Form.list_noms, nom_occurs, Bool.or_eq_true, List.mem_dedup, List.mem_merge]
    exact Or.inr ((occurs_list_noms (φ := b)).mpr hj))

/-- Nominal substitution for a non-free variable is the identity. -/
lemma subst_nom_notfree {N : Set ℕ} {a : Form N} {s : NOM N} {v : SVAR}
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
      · rw [if_pos hvw]
      · rw [if_neg hvw]
        have hp : is_free v p = false := by
          by_cases hf : is_free v p = true
          · simp only [is_free, hf, Bool.and_true] at h
            simp only [bne_eq_false_iff_eq] at h
            exact absurd h.symm hvw
          · simpa using hf
        rw [ih hp]
  | _ => rfl

/-- If `v` occurs free in `a`, the substituted nominal `s` appears in `a[s // v]`. -/
lemma nom_occurs_subst_nom_of_free {N : Set ℕ} {a : Form N} {s : NOM N} {v : SVAR}
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
      · exact Or.inl (ihp hp)
      · exact Or.inr (ihq hq)
  | box p ih =>
      simp only [is_free] at h
      simp only [subst_nom, nom_occurs]
      exact ih h
  | bind w p ih =>
      simp only [is_free, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
      have hvw : v ≠ w := fun e => h.1 e.symm
      simp only [subst_nom, if_neg hvw, nom_occurs]
      exact ih h.2
  | _ => simp [is_free] at h

end Conservativity

-- Peel `total` back through the connectives: a totalized formula matching a
-- connective decomposes into totalizations of `N`-formulas.
lemma total_eq_impl {φ : Form N} {a b : Form TotalSet} (h : φ.total = a ⟶ b) :
    ∃ a' b' : Form N, a'.total = a ∧ b'.total = b := by
  cases φ with
  | impl l r => simp only [Form.total, Form.impl.injEq] at h; exact ⟨l, r, h.1, h.2⟩
  | _ => simp [Form.total] at h

lemma total_eq_box {φ : Form N} {a : Form TotalSet} (h : φ.total = □ a) :
    ∃ a' : Form N, a'.total = a := by
  cases φ with
  | box r => simp only [Form.total, Form.box.injEq] at h; exact ⟨r, h⟩
  | _ => simp [Form.total] at h

lemma total_eq_bind {φ : Form N} {v : SVAR} {a : Form TotalSet} (h : φ.total = all v, a) :
    ∃ a' : Form N, a'.total = a := by
  cases φ with
  | bind u r => simp only [Form.total, Form.bind.injEq] at h; exact ⟨r, h.2⟩
  | _ => simp [Form.total] at h

-- On the range of `total`, `inv_t` is a genuine right inverse.
lemma total_in_range {ψ : Form TotalSet} (h : ∃ α : Form N, α.total = ψ) :
    ((@Form.inv_t N) ψ).total = ψ :=
  Function.invFun_eq h

-- Reconstruction lemmas (no side condition) for the remaining axioms, mirroring
-- `total_ax_k`/`total_ax_q1`/`total_ax_q2_svar` above.
theorem total_ax_name {φ : Form N} {v : SVAR} (h : φ.total = ex v, v) : φ = ex v, v := by
  apply total_inj'
  rw [h]; rfl

theorem total_ax_brcn {φ : Form N} {v : SVAR} {ψ : Form TotalSet}
    (h : φ.total = (all v, □ψ) ⟶ (□ all v, ψ)) : φ = (all v, □ψ⁻) ⟶ (□ all v, ψ⁻) := by
  obtain ⟨l, r, hl, _⟩ := total_eq_impl h
  obtain ⟨lb, hlb⟩ := total_eq_bind hl
  obtain ⟨lbb, hlbb⟩ := total_eq_box hlb
  apply total_inj'
  rw [h]
  simp only [Form.total, total_in_range ⟨lbb, hlbb⟩]

-- Peel `total` back through an `iterate_nec` stack (n boxes).
lemma total_eq_iterate_nec :
    ∀ {n : ℕ} {φ : Form N} {a : Form TotalSet}, φ.total = iterate_nec n a → ∃ a' : Form N, a'.total = a := by
  intro n
  induction n with
  | zero => intro φ a h; exact ⟨φ, h⟩
  | succ k ih =>
      intro φ a h
      have hstep : iterate_nec (k+1) a = □ (iterate_nec k a) := rfl
      rw [hstep] at h
      obtain ⟨b, hb⟩ := total_eq_box h
      exact ih hb

theorem total_ax_nom {φ : Form N} {v : SVAR} {ψ : Form TotalSet} {m n : ℕ}
    (h : φ.total = (all v, iterate_pos m (v ⋀ ψ) ⟶ iterate_nec n (v ⟶ ψ))) :
    φ = (all v, iterate_pos m (v ⋀ ψ⁻) ⟶ iterate_nec n (v ⟶ ψ⁻)) := by
  obtain ⟨c, hcb⟩ := total_eq_bind h
  obtain ⟨c1, c2, _, hc2⟩ := total_eq_impl hcb
  obtain ⟨d, hd⟩ := total_eq_iterate_nec hc2
  obtain ⟨e1, e2, _, he2⟩ := total_eq_impl hd
  apply total_inj'
  rw [h]
  simp only [Form.total, Form.conj, Form.neg, Form.diamond, total_iterate_pos,
             total_iterate_nec, total_in_range ⟨e2, he2⟩]

/-- Pull an in-range `TotalSet` derivation back to the base language via `inv_t`.
    Structural induction on the derivation: deduction rules recurse through
    `inv_t_impl`/`inv_t_box`/`inv_t_bind`; axioms reconstruct via the `total_ax_*`
    lemmas.  The `ax_q2_nom` case splits on whether the substituted nominal is in
    the base language (it vanishes exactly when the bound variable is not free). -/
noncomputable def in_range_proof_back {NBase : Set ℕ} {ψ : Form TotalSet} (pf : @Proof TotalSet ψ)
    (hall : ∀ χ ∈ pf.formulasIn, form_noms_in_base (N := NBase) χ) :
    @Proof NBase ((@Form.inv_t NBase) ψ) := by
  revert hall
  induction pf with
  | @tautology a ht =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) a := hall a (by simp [Proof.formulasIn])
      apply Proof.tautology
      rw [total_tautology, inv_t_eq_of_range' hbase]
      exact ht
  | @general χ v pf' ih =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) χ :=
        hall (all v, χ) (by simp [Proof.formulasIn])
      have ihp := ih (fun c hc => hall c (by
        simp only [Proof.formulasIn, List.mem_cons]; exact Or.inr hc))
      rw [inv_t_bind hbase]
      exact general v ihp
  | @necess χ pf' ih =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) χ :=
        hall (□ χ) (by simp [Proof.formulasIn])
      have ihp := ih (fun c hc => hall c (by
        simp only [Proof.formulasIn, List.mem_cons]; exact Or.inr hc))
      rw [inv_t_box hbase]
      exact necess ihp
  | @mp a b pf1 pf2 ih1 ih2 =>
      intro hall
      have hab : form_noms_in_base (N := NBase) (a ⟶ b) :=
        hall (a ⟶ b) (by
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
      have hbase : form_noms_in_base (N := NBase) (□(a ⟶ b) ⟶ (□a ⟶ □b)) :=
        hall _ (by simp [Proof.formulasIn])
      rw [total_ax_k (inv_t_eq_of_range' hbase)]
      exact ax_k
  | @ax_q1 a b v p =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) ((all v, a ⟶ b) ⟶ (a ⟶ all v, b)) :=
        hall _ (by simp [Proof.formulasIn])
      have hab : form_noms_in_base (N := NBase) (a ⟶ b) :=
        form_noms_in_base_impl_left hbase
      have ha : form_noms_in_base (N := NBase) a :=
        form_noms_in_base_impl_left hab
      rw [total_ax_q1 (inv_t_eq_of_range' hbase)]
      apply ax_q1
      rw [← total_is_free, inv_t_eq_of_range' ha]
      exact p
  | @ax_q2_svar a v s p =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) ((all v, a) ⟶ a[s // v]) :=
        hall _ (by simp [Proof.formulasIn])
      have ha : form_noms_in_base (N := NBase) a :=
        form_noms_in_base_impl_left hbase
      rw [total_ax_q2_svar (inv_t_eq_of_range' hbase)]
      apply ax_q2_svar
      rw [← total_is_substable, inv_t_eq_of_range' ha]
      exact p
  | @ax_q2_nom a v s =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) ((all v, a) ⟶ a[s // v]) :=
        hall _ (by simp [Proof.formulasIn])
      have ha : form_noms_in_base (N := NBase) a :=
        form_noms_in_base_impl_left hbase
      have heq : ((@Form.inv_t NBase) ((all v, a) ⟶ a[s // v])).total = (all v, a) ⟶ a[s // v] :=
        inv_t_eq_of_range' hbase
      by_cases hfree : is_free v a = true
      · have hsocc : nom_occurs s (a[s // v]) = true := nom_occurs_subst_nom_of_free hfree
        have hslist : s ∈ (a[s // v]).list_noms := (occurs_list_noms (φ := a[s // v])).mp hsocc
        have hs : nom_in_base (N := NBase) s :=
          (form_noms_in_base_impl_right hbase) s hslist
        rw [total_ax_q2_nom ha hs heq]
        exact ax_q2_nom ((@Form.inv_t NBase) a) v (NOM.fromTotal s hs)
      · have hnf : is_free v a = false := by simpa using hfree
        have hav : a[s // v] = a := subst_nom_notfree hnf
        rw [hav] at heq ⊢
        rw [total_ax_q2_nom_end ha heq]
        have hnf' : is_free v ((@Form.inv_t NBase) a) = false := by
          rw [← total_is_free, inv_t_eq_of_range' ha]; exact hnf
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
          (all v, iterate_pos m (v ⋀ a) ⟶ iterate_nec n (v ⟶ a)) :=
        hall _ (by simp [Proof.formulasIn])
      rw [total_ax_nom (inv_t_eq_of_range' hbase)]
      exact ax_nom m n
  | @ax_brcn a v =>
      intro hall
      have hbase : form_noms_in_base (N := NBase) ((all v, □ a) ⟶ (□ all v, a)) :=
        hall _ (by simp [Proof.formulasIn])
      rw [total_ax_brcn (inv_t_eq_of_range' hbase)]
      exact ax_brcn

noncomputable def pf_extended {φ : Form N} (hN : N.Nonempty) : ⊢ φ iff ⊢ φ.total := by
  apply TypeIff.intro
  . intro pf
    induction pf with
    | tautology =>
        apply Proof.tautology
        rw [←total_tautology]
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
    -- Blackburn pipeline (F4): `φ.total` has only base nominals, so eliminate the
    -- alien nominals introduced inside `pf` (F2), pull the resulting in-range
    -- derivation back to the base language (F3), and rewrite `(φ.total)⁻ = φ`.
    have hψ : form_noms_in_base (N := N) φ.total := form_noms_in_base_total φ
    have result :=
      in_range_proof_back
        (pf.eliminate_aliens hψ (base_nom_total hN) (base_nom_total_in_base hN) pf.proof_noms)
        (Proof.form_noms_in_base_of_eliminate_aliens N pf hψ
          (base_nom_total hN) (base_nom_total_in_base hN))
    rwa [total_inv_is_inv φ] at result

/-- Totalization distributes over conjunction. -/
lemma total_conj {a b : Form N} : (a ⋀ b).total = a.total ⋀ b.total := by
  simp [Form.conj, Form.neg, Form.total]

/-- A conjunction of `Set.total Γ`-members is itself the totalization of a
    conjunction of `Γ`-members.  Returns the base list as data (via choice) so it
    can feed the `SyntacticConsequence` Σ-type. -/
noncomputable def base_conjunction {Γ : Set (Form N)} (L : List (Set.total Γ)) :
    { L' : List Γ // conjunction (Set.total Γ) L = (conjunction Γ L').total } := by
  induction L with
  | nil => exact ⟨[], by simp [conjunction, Form.total]⟩
  | cons h t ih =>
      obtain ⟨L', hL'⟩ := ih
      have hspec := h.2.choose_spec
      exact ⟨⟨h.2.choose, hspec.1⟩ :: L',
        (congrArg₂ Form.conj hspec.2 hL').trans total_conj.symm⟩

/-- **Backward conservativity on `SyntacticConsequence`.**  A totalized
    consequence `Set.total Γ ⊢ φ.total` pulls back to `Γ ⊢ φ` (needs `N` nonempty
    to eliminate alien nominals via `pf_extended`). -/
noncomputable def syntactic_conservativity {Γ : Set (Form N)} {φ : Form N}
    (hN : N.Nonempty) (h : (Set.total Γ) ⊢ φ.total) : Γ ⊢ φ := by
  obtain ⟨L, pf⟩ := h
  obtain ⟨L', hL'⟩ := base_conjunction L
  rw [hL'] at pf
  have pf' : ⊢ ((conjunction Γ L' ⟶ φ).total) := pf
  exact ⟨L', (pf_extended hN).mpr pf'⟩
