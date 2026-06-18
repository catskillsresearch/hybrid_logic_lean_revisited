import Hybrid.Substitutions
import Hybrid.ProofUtils
import Hybrid.FormCountable
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Group.Even

open Classical

-- First, we define how to obtain Gamma_i_+_1 from Gamma_i, given a formula phi:
def lindenbaum_next (Gamma : Set (Form N)) (phi : Form N) : Set (Form N) :=
  if consistent (Gamma  U  {phi}) then
    match phi with
    | ex x, psi =>
        if c : exists  i : NOM N, all_nocc i (Gamma  U  {phi}) then
          Gamma  U  {phi}  U  {psi[c.choose // x]}
        else
          Gamma  U  {phi}
    | _       =>  Gamma  U  {phi}
  else
    Gamma

-- Now we define the whole indexed family Gamma_i.
-- Usually, the enumeration of formulas starts from 1 (phi_1, phi_2, ...), and
--    Gamma_0 = Gamma .
-- However, in Lean it's much tidier to enumerate from 0 (phi_0, phi_1, ...), so
--    Gamma_0 = Gamma  U  {phi_0} if it is consistent and Gamma_0 = Gamma otherwise.
def lindenbaum_family (enum : Nat  ->  Form N) (Gamma : Set (Form N)) : Nat  ->  Set (Form N)
| .zero   => lindenbaum_next Gamma (enum 0)
| .succ n =>
    let prev_set := lindenbaum_family enum Gamma n
    lindenbaum_next prev_set (enum (n+1))

notation Gamma "(" i "," e ")" => lindenbaum_family e Gamma i

def LindenbaumMCS (enum : Nat  ->  Form N) (Gamma : Set (Form N)) (_ : consistent Gamma) : Set (Form N) :=
    {phi | exists  i : Nat, phi  in  Gamma (i, enum)}

-- Lemma: All Gamma_i belong to LindenbaumMCS Gamma
lemma all_sets_in_family{enum : Nat  ->  Form N} {Gamma : Set (Form N)} {c : consistent Gamma} : forall  n, Gamma (n, enum)  subseteq  LindenbaumMCS enum Gamma c := by
  intro i phi h
  exists i

lemma all_sets_in_family_tollens {enum : Nat  ->  Form N} {Gamma : Set (Form N)} {c : consistent Gamma} : phi  notin  (LindenbaumMCS enum Gamma c)  ->  forall  n, phi  notin  Gamma (n, enum) := by
  rw [contraposition, not_not, not_forall]
  intro h
  let <i, hi> := h
  rw [not_not] at hi
  exact all_sets_in_family i hi

-- Lemma: If Gamma is consistent, then for all phi, lindenbaum_next Gamma phi is consistent
lemma consistent_lindenbaum_next (Gamma : Set (Form N)) (hc : consistent Gamma) (phi : Form N) : consistent (lindenbaum_next Gamma phi) := by
  unfold lindenbaum_next
  split
  . split
    . next x psi h =>
      split
      . next hnom =>
        let i := Exists.choose hnom
        have not1 : i = Exists.choose hnom := rfl
        have i_sat := Exists.choose_spec hnom
        have not2 : (ex x, psi) = ((all x, psi --> False) --> False) := by simp
        rw [ <- not1,  <- not2, consistent]
        intro hyp
        have <L, habs> := Proof.Deduction.mpr hyp
        let chi := conjunction (Gamma  U  {ex x, psi}) L
        have not3 : chi = conjunction (Gamma  U  {ex x, psi}) L := rfl
        rw [ <- not3] at habs
        let y := (chi --> psi).new_var
        have y_ge : y  >=  (chi --> psi).new_var := Nat.le.refl
        have : y  >=  (chi --> (psi[i//x]) --> False).new_var := ge_new_var_subst_helpr y_ge
        have habs := (Proof.generalize_constants i this) habs
        rw [nom_subst_svar, nom_subst_svar] at habs
        have nocc0 : occurs y chi = false := by apply ge_new_var_is_new; exact (new_var_geq1 y_ge).left
        have nocc1 : nom_occurs i chi = false := all_noc_conj i_sat L
        conv at i_sat =>
          rw [ <- not1,  <- not2, all_nocc, Set.union_singleton]
          intro phi; rw [Set.mem_insert_iff]
        have nocc2 : nom_occurs i (ex x, psi) = false := by apply (i_sat (ex x, psi)); simp
        rw [not2] at nocc2
        simp only [nom_occurs, or_false, Bool.or_false] at nocc2
        rw [nom_subst_nocc nocc1, subst_collect_all_nocc nocc2] at habs
        have := Proof.ax_q1 chi (psi[y//x] --> False) (notoccurs_notfree nocc0)
        have habs := Proof.mp this habs
        have habs : Sigma L,  |- (conjunction (Gamma  U  {ex x, psi}) L --> all y, psi[y//x] --> False) := <L, habs>
        rw [ <- SyntacticConsequence,  <- Form.neg] at habs
        have :  |- ((all y, ~(psi[y//x]))  -->  (all x, ~psi)) := by
          apply Proof.iff_mpr
          apply Proof.rename_bound
          apply ge_new_var_is_new
          rw [new_var_neg]
          exact (new_var_geq1 y_ge).right
          rw [subst_neg]
          apply new_var_subst'' (new_var_geq1 y_ge).right
        have := Proof.Gamma_theorem this (Gamma  U  {ex x, psi})
        have habs := Proof.Gamma_mp this habs
        have : (Gamma  U  {ex x, psi})  |-  (ex x, psi) := by apply Proof.Gamma_premise; simp
        have := Proof.Gamma_mp this habs
        exact h this
      . assumption
    . assumption
  . assumption


-- Lemma: If you can consistently extend (lindenbaum_next Gamma phi) with phi, then
--    phi already belongs to (lindenbaum_next Gamma phi)
lemma maximal_lindenbaum_next {Gamma : Set (Form N)} (hc : consistent ((lindenbaum_next Gamma phi)  U  {phi})) : phi  in  lindenbaum_next Gamma phi := by
  revert hc
  unfold lindenbaum_next
  split
  . split
    . split <;> simp
    . intro; simp
  . intro; contradiction

--
-- Now apply the previous lemmas to the family as a whole.
--

-- Lemma: If Gamma is consistent, then all Gamma_i are consistent.
lemma consistent_family {Gamma : Set (Form N)} (e : Nat  ->  Form N) (c : consistent Gamma) : forall  n, consistent (Gamma (n, e)) := by
  intro n
  induction n <;> (
      simp only [lindenbaum_family]
      apply consistent_lindenbaum_next
      assumption
  )

-- Lemma: If phi doesn't belong to the set in the family corresponding to its place in the enumeration,
--     (i.e., phi  notin  Gamma_i, where i = f phi),
--    then Gamma_i  U  {phi} must be inconsistent.
lemma maximal_family {Gamma : Set (Form N)} {f : Form N  ->  Nat} (f_inj : f.Injective) {e : Nat  ->  Form N} (e_inv : e = f.invFun) :
    not phi  in  Gamma (f phi, e)  ->  not consistent (Gamma (f phi, e)  U  {phi}) := by
    rw [contraposition, not_not, not_not]
    unfold lindenbaum_family
    cases heq : f phi with
    | zero =>
        simp only
        have by_inv : e (f phi) = phi := by simp [f.leftInverse_invFun f_inj phi, e_inv]
        rw [show 0 = f phi by simp [heq], by_inv]
        intro h
        apply maximal_lindenbaum_next
        exact h
    | succ n =>
        simp only
        have by_inv : e (f phi) = phi := by simp [f.leftInverse_invFun f_inj phi, e_inv]
        simp only [show (n+1) = f phi by simp [heq], by_inv]
        intro h
        apply maximal_lindenbaum_next
        exact h

-- todo: Include here that Gamma  subseteq  Gamma_i for all i
lemma increasing_family : i  <=  j  ->  Gamma (i, e)  subseteq  Gamma (j, e) := by
  intro h
  induction h with
  | refl => simp [subset_of_eq]
  | @step m _ ih =>
      simp only [lindenbaum_family, lindenbaum_next]
      split
      . intro _ phi_member
        have incl : Gamma(m, e)  subseteq  (Gamma(m, e)  U  {e (m + 1)}) := by simp
        split ; split
        . rw [Set.union_singleton]
          apply Set.subset_insert
          exact incl (ih phi_member)
        . exact incl (ih phi_member)
        . exact incl (ih phi_member)
      . assumption

lemma Gamma_in_family : Gamma  subseteq  Gamma (i, e) := by
  induction i with
  | zero =>
      simp only [lindenbaum_family, lindenbaum_next]
      split ; split ; split
      . apply subset_trans
        have : Gamma  subseteq  Gamma  U  {e 0} := by simp
        exact this
        simp
      . simp
      . simp
      . apply subset_of_eq
        simp
  | succ n ih =>
      apply subset_trans
      apply ih
      apply increasing_family
      apply Nat.le_succ

-- Now we want to show that Gamma' = LindenbaumMCS e Gamma is consistent.
--
-- (f is an injection Form  ->  Nat  ; e is its (left) inverse Nat  ->  Form N)
--
-- Assume Gamma' is inconsistent.
--  That means that there is list of elements L of that set
--  such that their conjunction proves a contradiction.
--
-- L : List (LindenbaumMCS e Gamma)
--   there is a "maximum formula" in L, (Prove!)
--   i.e. a formula phi s.t. for all psi  !=  phi in L f(phi) > f(psi)
-- Clearly, phi  in  lindenbaum_family e Gamma f(phi). (lemma in_set)
-- Now, we know that for all formulas psi, if f(psi) <= n, then
--    psi  in  lindenbaum_family e Gamma n. (Prove!)
-- So since phi is the greatest element in L, then all elements in L
--    are elements in lindenbaum_family e Gamma f(phi).
-- So in fact L only contains elements from lindenbaum_family e Gamma f(phi),
--    not from the whole MCS.
--
-- We know that if Gamma is consistent, then for all n, lindenbaum_family e Gamma n
--    is consistent. (lemma consistent_family).
-- So lindenbaum_family e Gamma f(phi) is consistent.
-- So no conjunction of elements in L can prove a contradiction.
--
--    This completes our reductio proof.
--    We conclude LindenbaumMCS e Gamma is consistent after all.

-- Needed, but unrelated.
lemma incl_insert {A B : Set a} (h1 : A  subseteq  B) (h2 : x  in  B) : (A  U  {x})  subseteq  B := by
  intro a h
  simp at h
  apply Or.elim h
  . intro ax
    rw [ax]
    assumption
  . apply h1

-- If phi is a formula that belongs to the infinite union Gamma' = LindenbaumMCS e Gamma,
--    then phi must belong to some Gamma_i from Gamma'.
-- More specifically, i = f phi; i.e. the place of phi in the enumeration.
lemma at_finite_step {Gamma : Set (Form N)} (c : consistent Gamma) (f : Form N  ->  Nat) (f_inj : f.Injective) (e : Nat  ->  Form N) (e_inv : e = f.invFun) :
    phi  in  LindenbaumMCS e Gamma c  ->  phi  in  Gamma (f phi, e) := by
  rw [contraposition]
  simp only [LindenbaumMCS, Set.mem_setOf_eq, not_exists, not_not]
  intro h n habs
  by_cases order : n  <=  (f phi)
  . have incl := increasing_family order habs
    contradiction
  . simp only [not_le] at order
    have order := Nat.le_of_lt order
    have incl := incl_insert ((@increasing_family (f phi)) order) habs
    have n_consistent := consistent_family e c n
    have <phi_inconsistent, _> := not_forall.mp (maximal_family f_inj e_inv h)
    clear h
    have n_inconsistent := Proof.increasing_consequence phi_inconsistent incl
    exact n_consistent n_inconsistent

-- Given a finite list of elements in (LindenbaumMCS e Gamma c), all elements of that list
--    occur in some Gamma_i that makes up the infinite union.
lemma list_at_finite_step {Gamma : Set (Form N)} {c : consistent Gamma} (f : Form N  ->  Nat) (f_inj : f.Injective) (e : Nat  ->  Form N) (e_inv : e = f.invFun) (L : List (LindenbaumMCS e Gamma c)) :
    {phi | phi  in  L}  subseteq  (Gamma (L.max_form f, e)) := by
    intro phi_val hmem
    simp only [Set.mem_setOf_eq] at hmem
    let <phi, phi_property, phi_is_val> := hmem
    rw [ <- phi_is_val]
    clear hmem phi_val phi_is_val
    have phi_in_MCS : phi  in  LindenbaumMCS e Gamma c := by simp
    have phi_in_own_set := at_finite_step c f f_inj e e_inv phi_in_MCS
    have := L.max_is_max f phi phi_property
    exact increasing_family this phi_in_own_set

lemma LindenbaumConsistent {Gamma : Set (Form N)} (c : consistent Gamma) {f : Form N  ->  Nat} (f_inj : f.Injective) {e : Nat  ->  Form N} (e_inv : e = f.invFun) :
  consistent (LindenbaumMCS e Gamma c) := by
  rw [ <- @not_not (consistent (LindenbaumMCS e Gamma c))]
  intro habs
  let <<L, L_incons>, _> := not_forall.mp habs
  clear habs
  let <L', conj_L'> := conj_incl_linden L (list_at_finite_step f f_inj e e_inv L)
  rw [conj_L'] at L_incons
  clear conj_L'
  have : (( |- (conjunction (Gamma(L.max_form f, e)) L' --> False)  ->  (Gamma(L.max_form f, e))  |-  False)) := by intro h; simp [SyntacticConsequence]; exists L'
  exact consistent_family e c (L.max_form f) (this L_incons)

lemma LindenbaumMaximal {Gamma : Set (Form N)} (c : consistent Gamma) {f : Form N  ->  Nat} (f_inj : f.Injective) {e : Nat  ->  Form N} (e_inv : e = f.invFun) :
  forall  phi, phi  notin  (LindenbaumMCS e Gamma c)  ->  not consistent ((LindenbaumMCS e Gamma c)  U  {phi}) := by
  intro phi not_mem
  have := all_sets_in_family_tollens not_mem (f phi)
  have <pf_bot, _> := not_forall.mp (maximal_family f_inj e_inv this)
  intro habs
  apply habs
  apply Proof.Deduction.mp
  apply Proof.increasing_consequence
  exact Proof.Deduction.mpr pf_bot
  apply all_sets_in_family

theorem RegularLindenbaumLemma : forall  Gamma : Set (Form N), consistent Gamma  ->  exists  Gamma' : Set (Form N), Gamma  subseteq  Gamma'  /\  MCS Gamma' := by
  intro Gamma cons
  let <f, f_inj> := exists_injective_nat (Form N)
  let enum       := f.invFun
  let Gamma' := LindenbaumMCS enum Gamma cons
  have enum_inv : enum = f.invFun := rfl
  exists Gamma'
  apply And.intro
  . -- Gamma is included in Gamma'
    let Gamma_0 := Gamma (0, enum)
    have Gamma_in_Gamma_0 : Gamma  subseteq  Gamma_0 := Gamma_in_family
    have Gamma_0_in_family := @all_sets_in_family N enum Gamma cons 0
    rw [show LindenbaumMCS enum Gamma cons = Gamma' from rfl, show Gamma (0, enum) = Gamma_0 from rfl] at Gamma_0_in_family
    intro _ phi_in_Gamma
    exact Gamma_0_in_family (Gamma_in_Gamma_0 phi_in_Gamma)
  . rw [MCS]
    apply And.intro
    . exact LindenbaumConsistent cons f_inj enum_inv
    . intro phi
      exact LindenbaumMaximal cons f_inj enum_inv phi

def enough_noms (Gamma : Set (Form N)) := (exists  i, all_nocc i Gamma)  /\  forall  (e : Nat  ->  Form N) (n : Nat), exists  i, all_nocc i (Gamma (n, e))

-- The previous set is always contained in the next Lindenbaum step (whatever branch fires).
lemma prev_subset_lindenbaum_next {prev : Set (Form N)} {phi : Form N} : prev  subseteq  lindenbaum_next prev phi := by
  intro a ha
  unfold lindenbaum_next
  repeat' split
  all_goals first
    | exact ha
    | (simp only [Set.mem_union, Set.mem_singleton_iff]; tauto)

-- Witness-extraction step. If the existential `ex x, psi` survives one Lindenbaum step
-- (so the consistent branch fired) and a fresh nominal exists for that step, then the
-- witness `psi[i // x]` (for the *constructed* nominal `i`) lands in the next set.
lemma witness_in_next {prev : Set (Form N)} {x : SVAR} {psi : Form N}
    (hcons : consistent prev)
    (hmem : (ex x, psi)  in  lindenbaum_next prev (ex x, psi))
    (hfresh : exists  i : NOM N, all_nocc i (prev  U  {ex x, psi})) :
    exists  i : NOM N, psi[i // x]  in  lindenbaum_next prev (ex x, psi) := by
  -- Force the definitional reduction of the `match` arm for `ex x, psi`.
  have hmem' : (ex x, psi)  in  (if consistent (prev  U  {ex x, psi}) then
        (if c : exists  i : NOM N, all_nocc i (prev  U  {ex x, psi}) then
          prev  U  {ex x, psi}  U  {psi[c.choose // x]} else prev  U  {ex x, psi}) else prev) := hmem
  suffices hgoal : exists  i : NOM N, psi[i // x]  in  (if consistent (prev  U  {ex x, psi}) then
        (if c : exists  i : NOM N, all_nocc i (prev  U  {ex x, psi}) then
          prev  U  {ex x, psi}  U  {psi[c.choose // x]} else prev  U  {ex x, psi}) else prev) from hgoal
  by_cases hc : consistent (prev  U  {ex x, psi})
  * rw [if_pos hc] at hmem'  |- 
    by_cases hfr : exists  i : NOM N, all_nocc i (prev  U  {ex x, psi})
    * rw [dif_pos hfr] at hmem'  |- 
      exact <hfr.choose, by simp>
    * exact absurd hfresh hfr
  * rw [if_neg hc] at hmem'  |- 
    exfalso
    apply hc
    rw [Set.union_singleton, Set.insert_eq_self.mpr hmem']
    exact hcons

-- One step of the witnessed-Lindenbaum argument, abstracted over the concrete set `S`
-- and the previous set `prev`.  Given freshness for `S` and that `ex x, psi` survives, the
-- witness lands in `S`.
lemma witness_at_step {S prev : Set (Form N)} {x : SVAR} {psi : Form N}
    (hprev_cons : consistent prev)
    (S_eq : S = lindenbaum_next prev (ex x, psi))
    (phi_at : (ex x, psi)  in  S)
    (hfresh : exists  j : NOM N, all_nocc j S) :
    exists  i : NOM N, psi[i // x]  in  S := by
  subst S_eq
  have hf : exists  j : NOM N, all_nocc j (prev  U  {ex x, psi}) := by
    obtain <j, hj> := hfresh
    refine <j, fun chi hchi => ?_>
    rw [Set.mem_union] at hchi
    rcases hchi with hp | he
    * exact hj chi (prev_subset_lindenbaum_next hp)
    * rw [Set.mem_singleton_iff] at he; rw [he]; exact hj _ phi_at
  exact witness_in_next hprev_cons phi_at hf

lemma LindenbaumWitnessed {Gamma : Set (Form N)} (c : consistent Gamma) {f : Form N  ->  Nat} (f_inj : f.Injective) {e : Nat  ->  Form N} (e_inv : e = f.invFun)
    (h : enough_noms Gamma) : witnessed (LindenbaumMCS e Gamma c) := by
    intro phi phi_mem
    split
    . next x psi =>
        -- `phi = ex x, psi`. It lands in the set at its own enumeration index `f phi`.
        -- The matcher hands us the unfolded form `(all x, psi --> False) --> False`; normalise to `ex x, psi`.
        have eqform : ((all x, psi --> False) --> False) = (ex x, psi) := rfl
        have phi_at := at_finite_step c f f_inj e e_inv phi_mem
        rw [eqform] at phi_at
        have en : e (f (ex x, psi)) = (ex x, psi) := by rw [e_inv]; exact f.leftInverse_invFun f_inj _
        have hfresh := h.right e (f (ex x, psi))
        have main : exists  i : NOM N, psi[i // x]  in  Gamma (f (ex x, psi), e) := by
          cases hcase : f (ex x, psi) with
          | zero =>
              rw [hcase] at phi_at hfresh
              refine witness_at_step c ?_ phi_at hfresh
              show lindenbaum_next Gamma (e 0) = lindenbaum_next Gamma (ex x, psi)
              rw [show e 0 = e (f (ex x, psi)) by rw [hcase], en]
          | succ m =>
              rw [hcase] at phi_at hfresh
              refine witness_at_step (consistent_family e c m) ?_ phi_at hfresh
              show lindenbaum_next (Gamma (m, e)) (e (m+1)) = lindenbaum_next (Gamma (m, e)) (ex x, psi)
              rw [show e (m+1) = e (f (ex x, psi)) by rw [hcase], en]
        obtain <i, hi> := main
        exact <i, all_sets_in_family _ hi>
    . assumption

-- The nominal `0` (even) never occurs in an odd-nominal image, since `odd_noms` maps every
-- nominal `i  |->  2*i+1`.
theorem zero_nocc_odd : forall  phi : Form TotalSet, nom_occurs 0 phi.odd_noms = false := by
  intro phi
  induction phi with
  | bttm => rw [odd_bttm]; rfl
  | prop p => simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst, nom_occurs]
  | svar x => simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst, nom_occurs]
  | nom i =>
      rw [odd_nom]
      have hne : (0 : NOM TotalSet)  !=  2 * i + 1 := by
        intro h
        rw [NOM_eq] at h
        have hval : (0 : Nat) = (i.letter : Nat) * 2 + 1 := congrArg Subtype.val h
        omega
      simp only [nom_occurs, decide_eq_false_iff_not]
      exact hne
  | impl a b iha ihb => rw [odd_impl]; simp only [nom_occurs, iha, ihb, Bool.or_self]
  | box a ih => rw [odd_box]; simp only [nom_occurs, ih]
  | bind x a ih => rw [odd_bind]; simp only [nom_occurs, ih]

-- Generalisation of `zero_nocc_odd`: *any* even nominal is fresh for an odd-nominal image,
-- since `odd_noms` sends every nominal `i  |->  2*i+1` (always odd).
theorem even_nocc_odd {j : NOM TotalSet} (heven : Even (j.letter : Nat)) :
    forall  phi : Form TotalSet, nom_occurs j phi.odd_noms = false := by
  intro phi
  induction phi with
  | bttm => rw [odd_bttm]; rfl
  | prop p => simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst, nom_occurs]
  | svar x => simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst, nom_occurs]
  | nom i =>
      rw [odd_nom]
      have hne : j  !=  2 * i + 1 := by
        intro h
        rw [NOM_eq] at h
        have hval : (j.letter : Nat) = (i.letter : Nat) * 2 + 1 := congrArg Subtype.val h
        obtain <t, ht> := heven
        omega
      simp only [nom_occurs, decide_eq_false_iff_not]
      exact hne
  | impl a b iha ihb => rw [odd_impl]; simp only [nom_occurs, iha, ihb, Bool.or_self]
  | box a ih => rw [odd_box]; simp only [nom_occurs, ih]
  | bind x a ih => rw [odd_bind]; simp only [nom_occurs, ih]

-- Base case of structural freshness: the even nominal `0` is fresh for the whole image set.
theorem enough_noms_odd_base (Gamma : Set (Form TotalSet)) : exists  i : NOM TotalSet, all_nocc i Gamma.odd_noms := by
  refine <0, ?_>
  rintro phi <psi, _, rfl>
  exact zero_nocc_odd psi

-- A single Lindenbaum step only enlarges the previous set by a *finite* number of formulas
-- (the enumerated formula `phi` itself, plus at most one existential witness).
lemma lindenbaum_next_subset (prev : Set (Form N)) (phi : Form N) :
    exists  A : Finset (Form N), lindenbaum_next prev phi  subseteq  prev  U  A := by
  unfold lindenbaum_next
  split
  * split
    * next x psi _ =>
        split
        * next c =>
            refine <{(ex x, psi), psi[c.choose // x]}, ?_>
            intro a ha
            simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_union,
                       Finset.coe_insert, Finset.coe_singleton, Set.mem_singleton_iff] at ha  |- 
            tauto
        * refine <{(ex x, psi)}, ?_>
          intro a ha
          simp only [Set.union_singleton, Set.mem_insert_iff,
                     Finset.coe_singleton] at ha  |- 
          tauto
    * refine <{phi}, ?_>
      intro a ha
      simp only [Set.union_singleton, Set.mem_insert_iff,
                 Finset.coe_singleton] at ha  |- 
      tauto
  * exact <{}, fun a ha => Or.inl ha>

-- Hence each finite stage `Gamma (n, e)` is contained in the base `Gamma` together with a finite set.
lemma family_subset {Gamma : Set (Form N)} (e : Nat  ->  Form N) :
    forall  n, exists  A : Finset (Form N), Gamma (n, e)  subseteq  Gamma  U  A := by
  intro n
  induction n with
  | zero =>
      simp only [lindenbaum_family]
      exact lindenbaum_next_subset Gamma (e 0)
  | succ m ih =>
      obtain <A, hA> := ih
      obtain <A', hA'> := lindenbaum_next_subset (Gamma (m, e)) (e (m+1))
      refine <A  U  A', ?_>
      calc Gamma ((m+1), e)  subseteq  Gamma (m, e)  U  A' := hA'
        _  subseteq  (Gamma  U  A)  U  A' := Set.union_subset_union hA (subset_refl _)
        _ = Gamma  U  (A  U  A') := by rw [Set.union_assoc]
        _ = Gamma  U  (A  U  A') := by rw [Finset.coe_union]

-- For any finite set of formulas there is an even nominal that occurs in none of them.
-- (Take a letter that is both even and larger than every nominal appearing in the set.)
lemma fresh_even_dominating (A : Finset (Form TotalSet)) :
    exists  j : NOM TotalSet, Even (j.letter : Nat)  /\  (forall  phi  in  A, nom_occurs j phi = false) := by
  obtain <M, hM> : exists  M : Nat, forall  phi  in  A, (phi.new_nom.letter : Nat)  <=  M := by
    refine <A.sup (fun phi => (phi.new_nom.letter : Nat)), fun phi hphi => ?_>
    exact Finset.le_sup (f := fun phi => (phi.new_nom.letter : Nat)) hphi
  refine <<2 * M + 2, trivial>, ?_, ?_>
  * show Even (2 * M + 2)
    exact <M + 1, by omega>
  intro phi hphi
  apply ge_new_nom_is_new
  show (phi.new_nom.letter : Nat)  <=  (2 * M + 2 : Nat)
  have := hM phi hphi
  omega

-- Inductive (per-stage) case of structural freshness.  This is the heart of the completeness
-- proof and the obstacle on which Oltean's original development stalled.  At every finite
-- stage of the Lindenbaum construction only finitely many further formulas (hence finitely
-- many further nominals) have been added to the odd-only base set, so an unused even nominal
-- always remains.
theorem enough_noms_odd_step (Gamma : Set (Form TotalSet)) :
    forall  (e : Nat  ->  Form TotalSet) (n : Nat), exists  i : NOM TotalSet, all_nocc i (Gamma.odd_noms (n, e)) := by
  intro e n
  obtain <A, hA> := family_subset (Gamma := Gamma.odd_noms) e n
  obtain <j, hjeven, hjA> := fresh_even_dominating A
  refine <j, ?_>
  intro phi hphi
  rcases hA hphi with hbase | hAmem
  * obtain <psi, _, rfl> := hbase
    exact even_nocc_odd hjeven psi
  * exact hjA phi hAmem

theorem enough_noms_odd (Gamma : Set (Form TotalSet)) : enough_noms Gamma.odd_noms :=
  <enough_noms_odd_base Gamma, enough_noms_odd_step Gamma>

theorem ExtendedLindenbaumLemma : forall  Gamma : Set (Form TotalSet), consistent Gamma  ->  exists  Gamma' : Set (Form TotalSet), Gamma.odd_noms  subseteq  Gamma'  /\  MCS Gamma'  /\  witnessed Gamma' := by
  intro Gamma cons
  have cons' : consistent Gamma.odd_noms := (Proof.odd_noms_set_cons Gamma).mp cons
  obtain <f, f_inj> := exists_injective_nat (Form TotalSet)
  let enum := f.invFun
  have enum_inv : enum = f.invFun := rfl
  refine <LindenbaumMCS enum Gamma.odd_noms cons', ?_, <?_, ?_>, ?_>
  * -- `Gamma.odd_noms  subseteq  Gamma'`
    intro phi hphi
    exact all_sets_in_family 0 (Gamma_in_family hphi)
  * -- consistency of the MCS
    exact LindenbaumConsistent cons' f_inj enum_inv
  * -- maximality of the MCS
    intro phi
    exact LindenbaumMaximal cons' f_inj enum_inv phi
  * -- witnessing
    exact LindenbaumWitnessed cons' f_inj enum_inv (enough_noms_odd Gamma)

/-- Witnessed Lindenbaum on a set that already carries `enough_noms` (not just on `odd_noms`). -/
theorem WitnessedLindenbaumLemma : forall  Gamma : Set (Form TotalSet), consistent Gamma  ->  enough_noms Gamma  -> 
    exists  Gamma' : Set (Form TotalSet), Gamma  subseteq  Gamma'  /\  MCS Gamma'  /\  witnessed Gamma' := by
  intro Gamma cons hnom
  obtain <f, f_inj> := exists_injective_nat (Form TotalSet)
  let enum := f.invFun
  have enum_inv : enum = f.invFun := rfl
  let Gamma' := LindenbaumMCS enum Gamma cons
  refine <Gamma', ?_, <?_, ?_>, ?_>
  * intro phi hphi
    exact all_sets_in_family 0 (Gamma_in_family hphi)
  * exact LindenbaumConsistent cons f_inj enum_inv
  * intro phi
    exact LindenbaumMaximal cons f_inj enum_inv phi
  * exact LindenbaumWitnessed cons f_inj enum_inv hnom
