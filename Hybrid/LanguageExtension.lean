import Hybrid.Proof
import Hybrid.Substitutions

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

noncomputable def l416 {φ : Form N} {x : SVAR} (i : NOM N) (pf : ⊢ φ) (h : pf.fresh_var x) : ⊢ (φ[x // i]) := by
  induction pf with
  | ax_k =>
      simp [nom_subst_svar]
      apply ax_k
  | ax_name =>
      simp [nom_subst_svar]
      apply ax_name
  | ax_nom =>
      simp only [nom_subst_svar, nec_subst_nom, pos_subst_nom]
      apply ax_nom
  | ax_brcn =>
      simp [nom_subst_svar]
      apply ax_brcn
  | ax_q2_svar =>
      simp [fresh_var] at h
      admit
  | _ => admit

noncomputable def pf_extended {φ : Form N} : ⊢ φ iff ⊢ φ.total := by
  apply TypeIff.intro
  . intro pf
    induction pf with
    | tautology =>
        apply Proof.tautology
        rw [←total_tautology]
        assumption
    | ax_k =>
        apply Proof.ax_k
    | ax_q1 =>
        apply Proof.ax_q1
        admit
    | ax_q2_svar =>
        simp [Form.total, total_subst_svar']
        apply Proof.ax_q2_svar
        admit
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
    generalize hc : φ.total = φ_t at *
    induction pf with
    | tautology =>
        apply Proof.tautology
        rw [total_tautology, hc]
        assumption
    | @ax_k ψ_t χ_t =>
        rw [(total_ax_k hc)]
        apply Proof.ax_k
    | ax_q1 =>
        rw [total_ax_q1 hc]
        apply Proof.ax_q1
        admit
    | ax_q2_svar =>
        rw [total_ax_q2_svar hc]
        apply Proof.ax_q2_svar
        admit
    | ax_q2_nom =>
        admit
    | ax_name =>
        admit
    | ax_nom  =>
        admit
    | ax_brcn =>
        admit
    | mp pf1 pf2 ih1 ih2   =>
        rename_i ψ _
        rw [←hc] at pf1 ih1

        admit
    | general =>
        admit
    | necess  =>
        admit
