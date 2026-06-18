import Hybrid.Lindenbaum
import Hybrid.ProofUtils

open Proof

def conjunction' (L : List (Form N)) : Form N :=
  match L with
    | []     => False  -->  False
    | [h]    => h
    | h :: t => h  /\  conjunction' t

def has_wit_conj (Gamma : Set (Form N)) : Form N  ->  Form N  ->  Prop
  | (ex x, psi), phi => exists  i : NOM N, <> (((ex x, psi)  -->  psi[i//x])  /\  phi)  in  Gamma
  | _, _         => True

noncomputable def l313 {tau chi : Form N} (h1 : is_substable chi y x) (h2 : occurs y tau = false) (h3 : occurs y chi = false) :
   |-  (<>  tau  -->  ex y, <> (((ex x, chi)  -->  chi[y//x])  /\  tau)) := by
  have l1 := Gamma_empty.mpr (rename_bound_ex h3 h1)
  have l2 := Gamma_empty.mp (Gamma_conj_elim_l l1)
  have l3 := @b361 N y (chi[y//x]) (ex x, chi)
  have l4 := mp l3 l2
  have l5 := tautology (@ax_1 N ((ex y, (ex x, chi) --> chi[y//x])) tau)
  have l6 := mp l5 l4
  have l7 := tautology (@imp_refl N tau)
  have l8 := tautology (@conj_intro_hs N tau ((ex y, (ex x, chi) --> chi[y//x])) tau)
  have l9 := mp (mp l8 l6) l7
  have l10 := @b362' N y ((ex x, chi) --> chi[y//x]) tau (notoccurs_notfree h2)
  have l11 := hs l9 l10
  have l12 := diw_impl l11
  have l13 := hs l12 ax_brcn_contrap
  exact l13

lemma l313' {Delta : Set (Form N)} (mcs : MCS Delta) (wit : witnessed Delta) (mem : <> phi  in  Delta) : forall  psi : Form N, has_wit_conj Delta psi phi := by
  intro psi
  unfold has_wit_conj
  split
  . next _ _ x psi =>
      have <y, geq, nocc, subst> := (phi  -->  psi  -->  all x, False).new_var_properties
      have y_ne_x : y  !=  x := by
        intro habs
        have := habs  |>  (new_var_geq2 (new_var_geq1 (new_var_geq1 geq).2).2).1
        simp only [svar_le_letter, svar_add_letter] at this; omega
      have subst := subst x
      simp [occurs, is_substable, is_free] at nocc subst
      have := Gamma_theorem (l313 subst.2 nocc.1 nocc.2) Delta
      have mem' := MCS_pf mcs (Gamma_mp this (Gamma_premise mem))
      have has_wit := wit mem'
      have hgepsi : y  >=  psi.new_var := (new_var_geq1 (new_var_geq1 geq).2).1
      have hgephi : y  >=  phi.new_var := (new_var_geq1 geq).1
      have hpsi : occurs y psi = false := ge_new_var_is_new hgepsi
      have hphi : occurs y phi = false := ge_new_var_is_new hgephi
      have hren : forall  j : NOM N, psi[y // x][j // y] = psi[j // x] := fun j => rename_svar_nom j x y hgepsi
      simp [subst_nom, y_ne_x] at has_wit  |- 
      simp only [subst_nom_noop hpsi, subst_nom_noop hphi, hren] at has_wit
      exact has_wit
  . trivial

-- <>  (((ex x, psi) --> psi[y//x]) /\ phi)
-- <>  ((ex x, psi --> psi[i//x]) /\ phi)

-- ===========================================================================
-- STL-fix * Witnessed <> -successor existence lemma (the Henkin construction).
--
-- `enough_noms_diamond_seed` is FALSE (the box-reduct `{chi|[] chi in Delta}` mentions every
-- nominal, since `[] (nom j  -->  nom j)  in  Delta`).  The correct route is Oltean's
-- existence-lemma direction: build the witnessed successor incrementally from
-- `Delta`'s own witnessedness via `l313'`, accumulating Henkin *witness conditionals*
-- `((ex x,sigma)  -->  sigma[i//x])`.  The accumulator must carry *data* (the actual list),
-- so we return a `Subtype`, not a `Prop` (the latter, with `.choose`, loses the
-- structured list and is exactly why the original `set_family` stalled).
-- ===========================================================================

-- `conjunction'` on a nonempty tail is a top-level conjunction.
lemma conjunction'_cons {a : Form N} {l : List (Form N)} (h : l  !=  []) :
    conjunction' (a :: l) = a  /\  conjunction' l := by
  cases l with
  | nil => exact absurd rfl h
  | cons b l' => rfl

-- Every member of a list is provable from the list's conjunction.
def conj'_imp_mem {a : Form N} : forall  {l : List (Form N)}, a  in  l  ->   |-  (conjunction' l  -->  a) := by
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
          * subst hc; exact tautology conj_elim_l
          * have htl : a  in  b :: t' := by
              rcases List.mem_cons.mp hmem with h' | h'
              * exact absurd h' hc
              * exact h'
            exact hs (tautology conj_elim_r) (ih htl)

-- One incremental step: if `phi = ex x,psi`, prepend a Henkin witness conditional
-- (whose existence is `l313'`); otherwise leave the accumulator unchanged.
noncomputable def wcond_step {Delta : Set (Form N)} (mcs : MCS Delta) (wit : witnessed Delta)
    (p : { l : List (Form N) // l  !=  []  /\  <> conjunction' l  in  Delta }) (phi : Form N) :
    { l : List (Form N) // l  !=  []  /\  <> conjunction' l  in  Delta } :=
  match phi with
  | ex x, psi =>
      let hwc := l313' mcs wit p.2.2 (ex x, psi)
      <((ex x, psi)  -->  psi[hwc.choose // x]) :: p.val,
        <by simp, by rw [conjunction'_cons p.2.1]; exact hwc.choose_spec>>
  | _ => p

-- The accumulating family of witness-conditional lists (data, indexed by Nat).
noncomputable def wcond (enum : Nat  ->  Form N) {Delta : Set (Form N)} (mcs : MCS Delta) (wit : witnessed Delta)
    {phi : Form N} (mem : <> phi  in  Delta) : (n : Nat)  ->  { l : List (Form N) // l  !=  []  /\  <> conjunction' l  in  Delta }
  | 0     => <[phi], <by simp, by simpa only [conjunction'] using mem>>
  | n + 1 => wcond_step mcs wit (wcond enum mcs wit mem n) (enum n)

-- Each stage is contained in the next (membership is monotone in the index).
lemma wcond_succ_mem (enum : Nat  ->  Form N) {Delta : Set (Form N)} (mcs : MCS Delta) (wit : witnessed Delta)
    {phi : Form N} (mem : <> phi  in  Delta) {a : Form N} {n : Nat}
    (h : a  in  (wcond enum mcs wit mem n).val) : a  in  (wcond enum mcs wit mem (n + 1)).val := by
  show a  in  (wcond_step mcs wit (wcond enum mcs wit mem n) (enum n)).val
  unfold wcond_step
  split <;> first | exact List.mem_cons_of_mem _ h | exact h

lemma wcond_mono (enum : Nat  ->  Form N) {Delta : Set (Form N)} (mcs : MCS Delta) (wit : witnessed Delta)
    {phi : Form N} (mem : <> phi  in  Delta) {a : Form N} {m n : Nat} (hmn : m  <=  n)
    (h : a  in  (wcond enum mcs wit mem m).val) : a  in  (wcond enum mcs wit mem n).val := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact wcond_succ_mem enum mcs wit mem ih

-- If `enum n` is the existential `ex x,sigma`, the next stage carries a witness
-- conditional `(ex x,sigma)  -->  sigma[i//x]` for some nominal `i`.
lemma wcond_step_mem (enum : Nat  ->  Form N) {Delta : Set (Form N)} (mcs : MCS Delta) (wit : witnessed Delta)
    {phi : Form N} (mem : <> phi  in  Delta) (n : Nat) (x : SVAR) (sigma : Form N) (h : enum n = (ex x, sigma)) :
    exists  i : NOM N, ((ex x, sigma)  -->  sigma[i // x])  in  (wcond enum mcs wit mem (n + 1)).val := by
  show exists  i : NOM N, ((ex x, sigma)  -->  sigma[i // x])  in 
      (wcond_step mcs wit (wcond enum mcs wit mem n) (enum n)).val
  rw [h]
  exact <(l313' mcs wit (wcond enum mcs wit mem n).2.2 (ex x, sigma)).choose,
         List.mem_cons_self>

-- Conjoin a derivable family of premises into one derivation of their conjunction.
def Gamma_conjunction_of_premises {Gamma S : Set (Form N)} (L : List S)
    (h : forall  x  in  L, Gamma  |-  x.val) : Gamma  |-  conjunction S L := by
  induction L with
  | nil =>
      show Gamma  |-  (False  -->  False)
      exact Gamma_theorem (tautology imp_refl) Gamma
  | cons hd tl ih =>
      rw [conjunction]
      exact Gamma_conj_intro (h hd (List.mem_cons_self))
        (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

-- The diamond-successor seed: the canonical box-reduct of `Delta` together with the
-- accumulated Henkin witness conditionals (and the diamond formula `phi` at stage 0).
noncomputable def succ_seed (enum : Nat  ->  Form N) {Delta : Set (Form N)} (mcs : MCS Delta) (wit : witnessed Delta)
    {phi : Form N} (mem : <> phi  in  Delta) : Set (Form N) :=
  {chi | [] chi  in  Delta}  U  {chi | exists  n : Nat, chi  in  (wcond enum mcs wit mem n).val}

-- Compactness bookkeeping: any finite list drawn from `succ_seed` is bounded --
-- every element is in the box-reduct or in a single stage `wcond N`.
lemma seed_list_bound (enum : Nat  ->  Form N) {Delta : Set (Form N)} (mcs : MCS Delta) (wit : witnessed Delta)
    {phi : Form N} (mem : <> phi  in  Delta) (L : List (succ_seed enum mcs wit mem)) :
    exists  N : Nat, forall  x  in  L, ([]  x.val  in  Delta)  \/  x.val  in  (wcond enum mcs wit mem N).val := by
  induction L with
  | nil => exact <0, by simp>
  | cons h t ih =>
      obtain <N, hN> := ih
      rcases h.2 with hbox | <n, hn>
      * refine <N, fun x hx => ?_>
        rcases List.mem_cons.mp hx with rfl | hxt
        * exact Or.inl hbox
        * exact hN x hxt
      * refine <max n N, fun x hx => ?_>
        rcases List.mem_cons.mp hx with rfl | hxt
        * exact Or.inr (wcond_mono enum mcs wit mem (le_max_left n N) hn)
        * rcases hN x hxt with hb | hw
          * exact Or.inl hb
          * exact Or.inr (wcond_mono enum mcs wit mem (le_max_right n N) hw)
