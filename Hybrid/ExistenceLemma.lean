import Hybrid.Lindenbaum
import Hybrid.ProofUtils

open Proof

def conjunction' (L : List (Form N)) : Form N :=
  match L with
    | []     => ⊥ ⟶ ⊥
    | [h]    => h
    | h :: t => h ⋀ conjunction' t

def has_wit_conj (Γ : Set (Form N)) : Form N → Form N → Prop
  | (ex x, ψ), φ => ∃ i : NOM N, ◇(((ex x, ψ) ⟶ ψ[i//x]) ⋀ φ) ∈ Γ
  | _, _         => True

noncomputable def l313 {τ χ : Form N} (h1 : is_substable χ y x) (h2 : occurs y τ = false) (h3 : occurs y χ = false) :
  ⊢ (◇ τ ⟶ ex y, ◇(((ex x, χ) ⟶ χ[y//x]) ⋀ τ)) := by
  have l1 := Γ_empty.mpr (rename_bound_ex h3 h1)
  have l2 := Γ_empty.mp (Γ_conj_elim_l l1)
  have l3 := @b361 N y (χ[y//x]) (ex x, χ)
  have l4 := mp l3 l2
  have l5 := tautology (@ax_1 N ((ex y, (ex x, χ)⟶χ[y//x])) τ)
  have l6 := mp l5 l4
  have l7 := tautology (@imp_refl N τ)
  have l8 := tautology (@conj_intro_hs N τ ((ex y, (ex x, χ)⟶χ[y//x])) τ)
  have l9 := mp (mp l8 l6) l7
  have l10 := @b362' N y ((ex x, χ)⟶χ[y//x]) τ (notoccurs_notfree h2)
  have l11 := hs l9 l10
  have l12 := diw_impl l11
  have l13 := hs l12 ax_brcn_contrap
  exact l13

lemma l313' {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ) (mem : ◇φ ∈ Δ) : ∀ ψ : Form N, has_wit_conj Δ ψ φ := by
  intro ψ
  unfold has_wit_conj
  split
  . next _ _ x ψ =>
      have ⟨y, geq, nocc, subst⟩ := (φ ⟶ ψ ⟶ all x, ⊥).new_var_properties
      have y_ne_x : y ≠ x := by
        intro habs
        have := habs ▸ (new_var_geq2 (new_var_geq1 (new_var_geq1 geq).2).2).1
        simp only [svar_le_letter, svar_add_letter] at this; omega
      have subst := subst x
      simp [occurs, is_substable, is_free] at nocc subst
      have := Γ_theorem (l313 subst.2 nocc.1 nocc.2) Δ
      have mem' := MCS_pf mcs (Γ_mp this (Γ_premise mem))
      have has_wit := wit mem'
      have hgeψ : y ≥ ψ.new_var := (new_var_geq1 (new_var_geq1 geq).2).1
      have hgeφ : y ≥ φ.new_var := (new_var_geq1 geq).1
      have hψ : occurs y ψ = false := ge_new_var_is_new hgeψ
      have hφ : occurs y φ = false := ge_new_var_is_new hgeφ
      have hren : ∀ j : NOM N, ψ[y // x][j // y] = ψ[j // x] := fun j => rename_svar_nom j x y hgeψ
      simp [subst_nom, y_ne_x] at has_wit ⊢
      simp only [subst_nom_noop hψ, subst_nom_noop hφ, hren] at has_wit
      exact has_wit
  . trivial

-- ◇ (((ex x, ψ)⟶ψ[y//x])⋀φ)
-- ◇ ((ex x, ψ⟶ψ[i//x])⋀φ)

-- ===========================================================================
-- §TL-fix · Witnessed ◇-successor existence lemma (the Henkin construction).
--
-- `enough_noms_diamond_seed` is FALSE (the box-reduct `{χ│□χ∈Δ}` mentions every
-- nominal, since `□(nom j ⟶ nom j) ∈ Δ`).  The correct route is Oltean's
-- existence-lemma direction: build the witnessed successor incrementally from
-- `Δ`'s own witnessedness via `l313'`, accumulating Henkin *witness conditionals*
-- `((ex x,σ) ⟶ σ[i//x])`.  The accumulator must carry *data* (the actual list),
-- so we return a `Subtype`, not a `Prop` (the latter, with `.choose`, loses the
-- structured list and is exactly why the original `set_family` stalled).
-- ===========================================================================

-- `conjunction'` on a nonempty tail is a top-level conjunction.
lemma conjunction'_cons {a : Form N} {l : List (Form N)} (h : l ≠ []) :
    conjunction' (a :: l) = a ⋀ conjunction' l := by
  cases l with
  | nil => exact absurd rfl h
  | cons b l' => rfl

-- Every member of a list is provable from the list's conjunction.
def conj'_imp_mem {a : Form N} : ∀ {l : List (Form N)}, a ∈ l → ⊢ (conjunction' l ⟶ a) := by
  intro l hmem
  induction l with
  | nil => exact absurd hmem (by simp)
  | cons h t ih =>
      cases t with
      | nil =>
          have hah : a = h := by simpa using hmem
          subst hah
          simp only [conjunction']
          exact tautology imp_refl
      | cons b t' =>
          rw [conjunction'_cons (by simp)]
          by_cases hc : a = h
          · subst hc; exact tautology conj_elim_l
          · have htl : a ∈ b :: t' := by
              rcases List.mem_cons.mp hmem with h' | h'
              · exact absurd h' hc
              · exact h'
            exact hs (tautology conj_elim_r) (ih htl)

-- One incremental step: if `φ = ex x,ψ`, prepend a Henkin witness conditional
-- (whose existence is `l313'`); otherwise leave the accumulator unchanged.
noncomputable def wcond_step {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ)
    (p : { l : List (Form N) // l ≠ [] ∧ ◇conjunction' l ∈ Δ }) (φ : Form N) :
    { l : List (Form N) // l ≠ [] ∧ ◇conjunction' l ∈ Δ } :=
  match φ with
  | ex x, ψ =>
      let hwc := l313' mcs wit p.2.2 (ex x, ψ)
      ⟨((ex x, ψ) ⟶ ψ[hwc.choose // x]) :: p.val,
        ⟨by simp, by rw [conjunction'_cons p.2.1]; exact hwc.choose_spec⟩⟩
  | _ => p

-- The accumulating family of witness-conditional lists (data, indexed by ℕ).
noncomputable def wcond (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ)
    {φ : Form N} (mem : ◇φ ∈ Δ) : (n : ℕ) → { l : List (Form N) // l ≠ [] ∧ ◇conjunction' l ∈ Δ }
  | 0     => ⟨[φ], ⟨by simp, by simpa only [conjunction'] using mem⟩⟩
  | n + 1 => wcond_step mcs wit (wcond enum mcs wit mem n) (enum n)

-- Each stage is contained in the next (membership is monotone in the index).
lemma wcond_succ_mem (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ)
    {φ : Form N} (mem : ◇φ ∈ Δ) {a : Form N} {n : ℕ}
    (h : a ∈ (wcond enum mcs wit mem n).val) : a ∈ (wcond enum mcs wit mem (n + 1)).val := by
  show a ∈ (wcond_step mcs wit (wcond enum mcs wit mem n) (enum n)).val
  unfold wcond_step
  split <;> first | exact List.mem_cons_of_mem _ h | exact h

lemma wcond_mono (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ)
    {φ : Form N} (mem : ◇φ ∈ Δ) {a : Form N} {m n : ℕ} (hmn : m ≤ n)
    (h : a ∈ (wcond enum mcs wit mem m).val) : a ∈ (wcond enum mcs wit mem n).val := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact wcond_succ_mem enum mcs wit mem ih

-- If `enum n` is the existential `ex x,σ`, the next stage carries a witness
-- conditional `(ex x,σ) ⟶ σ[i//x]` for some nominal `i`.
lemma wcond_step_mem (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ)
    {φ : Form N} (mem : ◇φ ∈ Δ) (n : ℕ) (x : SVAR) (σ : Form N) (h : enum n = (ex x, σ)) :
    ∃ i : NOM N, ((ex x, σ) ⟶ σ[i // x]) ∈ (wcond enum mcs wit mem (n + 1)).val := by
  show ∃ i : NOM N, ((ex x, σ) ⟶ σ[i // x]) ∈
      (wcond_step mcs wit (wcond enum mcs wit mem n) (enum n)).val
  rw [h]
  exact ⟨(l313' mcs wit (wcond enum mcs wit mem n).2.2 (ex x, σ)).choose,
         List.mem_cons_self⟩

-- Conjoin a derivable family of premises into one derivation of their conjunction.
def Γ_conjunction_of_premises {Γ S : Set (Form N)} (L : List S)
    (h : ∀ x ∈ L, Γ ⊢ x.val) : Γ ⊢ conjunction S L := by
  induction L with
  | nil =>
      show Γ ⊢ (⊥ ⟶ ⊥)
      exact Γ_theorem (tautology imp_refl) Γ
  | cons hd tl ih =>
      rw [conjunction]
      exact Γ_conj_intro (h hd (List.mem_cons_self))
        (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

-- The diamond-successor seed: the canonical box-reduct of `Δ` together with the
-- accumulated Henkin witness conditionals (and the diamond formula `φ` at stage 0).
noncomputable def succ_seed (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ)
    {φ : Form N} (mem : ◇φ ∈ Δ) : Set (Form N) :=
  {χ | □χ ∈ Δ} ∪ {χ | ∃ n : ℕ, χ ∈ (wcond enum mcs wit mem n).val}

-- Compactness bookkeeping: any finite list drawn from `succ_seed` is bounded —
-- every element is in the box-reduct or in a single stage `wcond N`.
lemma seed_list_bound (enum : ℕ → Form N) {Δ : Set (Form N)} (mcs : MCS Δ) (wit : witnessed Δ)
    {φ : Form N} (mem : ◇φ ∈ Δ) (L : List ↑(succ_seed enum mcs wit mem)) :
    ∃ N : ℕ, ∀ x ∈ L, (□ x.val ∈ Δ) ∨ x.val ∈ (wcond enum mcs wit mem N).val := by
  induction L with
  | nil => exact ⟨0, by simp⟩
  | cons h t ih =>
      obtain ⟨N, hN⟩ := ih
      rcases h.2 with hbox | ⟨n, hn⟩
      · refine ⟨N, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact Or.inl hbox
        · exact hN x hxt
      · refine ⟨max n N, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hxt
        · exact Or.inr (wcond_mono enum mcs wit mem (le_max_left n N) hn)
        · rcases hN x hxt with hb | hw
          · exact Or.inl hb
          · exact Or.inr (wcond_mono enum mcs wit mem (le_max_right n N) hw)
