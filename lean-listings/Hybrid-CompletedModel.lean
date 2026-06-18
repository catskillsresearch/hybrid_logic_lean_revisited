import Hybrid.ProofUtils
import Hybrid.Truth
import Hybrid.Soundness
import Hybrid.Tautology
-- Interface for proofs to be filled
-- about renaming bound vars:
import Hybrid.RenameBound
import Hybrid.Lindenbaum
import Hybrid.ExistenceLemma

open Classical

def restrict_by : (Set (Form N)  ->  Prop)  ->  (Set (Form N)  ->  Set (Form N)  ->  Prop)  ->  (Set (Form N)  ->  Set (Form N)  ->  Prop) :=
  fun  restriction => fun  R => fun  Gamma => fun  Delta => restriction Gamma  /\  restriction Delta  /\  R Gamma Delta

theorem path_conj {R : a  ->  Prop} : path (fun  a b => R a  /\  R b) a b n  ->  (R a  ->  R b) := by
  cases n with
  | zero =>
      unfold path; intro; simp [*]
  | succ n =>
      unfold path
      intro <_, h> _
      exact h.1.2

theorem path_restr : path (restrict_by R_1 R_2) Gamma Delta n  ->  path R_2 Gamma Delta n := by
  induction n generalizing Delta with
  | zero => simp only [path, imp_self]
  | succ n ih =>
      simp only [path]
      intro <Theta, <<_, _, h1>, h2>>
      exists Theta
      apply And.intro
      assumption
      apply ih
      assumption

theorem path_restr' : path (restrict_by R_1 R_2) Gamma Delta n  ->  (R_1 Gamma  ->  R_1 Delta) := by
  cases n with
  | zero =>
      unfold path; intro; simp [*]
  | succ n =>
      unfold path
      intro <_, h> _
      exact h.1.2.1

structure GeneralModel (N : Set Nat) where
  W : Type
  R : W  ->  W   ->  Prop
  V_p: PROP    ->  Set W
  V_n: NOM N   ->  Set W

def GeneralI (W : Type) := SVAR  ->  Set W

def Canonical : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := restrict_by MCS (fun  Gamma => fun  Delta => (forall  {phi : Form TotalSet}, [] phi  in  Gamma  ->  phi  in  Delta))
--  R := fun  Gamma => fun  Delta => Gamma.MCS  /\  Delta.MCS  /\  (forall  phi : Form, [] phi  in  Gamma  ->  phi  in  Delta)
  V_p:= fun  p => {Gamma | MCS Gamma  /\  p  in  Gamma}
  V_n:= fun  i => {Gamma | MCS Gamma  /\  i  in  Gamma}

def CanonicalI : SVAR  ->  Set (Set (Form TotalSet)) := fun  x => {Gamma | MCS Gamma  /\  x  in  Gamma}

instance : Membership (Form TotalSet) Canonical.W := <Set.Mem>

theorem R_nec : [] phi  in  Gamma  ->  Canonical.R Gamma Delta  ->  phi  in  Delta := by
  intro h1 h2
  simp only [Canonical, restrict_by] at h2
  apply h2.right.right
  assumption

theorem R_pos : Canonical.R Gamma Delta  <->  (MCS Gamma  /\  MCS Delta  /\  forall  {phi}, (phi  in  Delta  ->  <> phi  in  Gamma)) := by
  simp only [Canonical, restrict_by]
  apply Iff.intro
  . intro <h1, h2, h3>
    simp only [*, true_and]
    intro phi phi_mem
    by_contra habs
    have <habs, _> := not_forall.mp (h1.right habs)
    have habs := Proof.Deduction.mpr habs
    rw [ <- Form.neg, Form.diamond] at habs
    have habs : ~phi  in  Delta := by
      apply h3
      apply Proof.MCS_pf h1
      apply Proof.Gamma_mp
      apply Proof.Gamma_theorem
      apply Proof.tautology
      apply dne
      assumption
    unfold MCS consistent at h1 h2
    apply h2.left
    apply Proof.Gamma_mp
    repeat (apply Proof.Gamma_premise; assumption)
  . intro <h1, h2, h3>
    simp only [*, true_and]
    intro phi phi_mem
    by_contra habs
    have <habs, _> := not_forall.mp (h2.right habs)
    have habs := Proof.Deduction.mpr habs
    rw [ <- Form.neg] at habs
    have habs : <> ~phi  in  Gamma := by
      apply h3
      apply Proof.MCS_pf h2
      assumption
    unfold MCS consistent at h1 h2
    apply h1.left
    apply Proof.Gamma_mp
    apply Proof.Gamma_premise
    assumption
    apply Proof.Gamma_mp
    apply Proof.Gamma_theorem
    apply Proof.mp
    apply Proof.tautology
    apply iff_elim_l
    apply Proof.dn_nec
    apply Proof.Gamma_premise
    assumption

theorem R_iter_nec (n : Nat) : (iterate_nec n phi)  in  Gamma  ->  path Canonical.R Gamma Delta n  ->  phi  in  Delta := by
  intro h1 h2
  induction n generalizing phi Delta with
  | zero =>
      simp only [iterate_nec, iterate_nec.loop, path] at h1 h2
      rw [ <- h2]
      assumption
  | succ n ih =>
      simp only [path, iter_nec_succ] at ih h1 h2
      have <Kappa, hk1, hk2> := h2
      apply R_nec
      exact (ih h1 hk2)
      assumption

theorem R_iter_pos (n : Nat) : path Canonical.R Gamma Delta n  ->  forall  {phi}, (phi  in  Delta  ->  (iterate_pos n phi)  in  Gamma) := by
  intro h1 phi h2
  induction n generalizing phi Delta with
  | zero =>
      simp [path, iterate_pos, iterate_pos.loop] at h1  |- 
      rw [h1]
      assumption
  | succ n ih =>
      simp only [path, iter_pos_succ] at ih h1  |- 
      have <Kappa, hk1, hk2> := h1
      rw [R_pos] at hk1
      apply ih hk2
      exact hk1.right.right h2

theorem restrict_R_iter_nec {n : Nat} : (iterate_nec n phi)  in  Gamma  ->  path (restrict_by R Canonical.R) Gamma Delta n  ->  phi  in  Delta := by
  intro h1 h2
  apply R_iter_nec
  assumption
  apply path_restr
  assumption

theorem restrict_R_iter_pos {n : Nat} : path (restrict_by R Canonical.R) Gamma Delta n  ->  forall  {phi}, (phi  in  Delta  ->  (iterate_pos n phi)  in  Gamma) := by
  intro h1 phi h2
  apply R_iter_pos
  apply path_restr
  repeat assumption

-- implicitly we mean generated submodels *of the canonical model*
def Set.GeneratedSubmodel (Theta : Set (Form TotalSet)) (restriction : Set (Form TotalSet)  ->  Prop) : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := fun  Gamma => fun  Delta =>
    (exists  n, path (restrict_by restriction Canonical.R) Theta Gamma n)  /\ 
    (exists  m, path (restrict_by restriction Canonical.R) Theta Delta m)  /\ 
    Canonical.R Gamma Delta
  V_p:= fun  p => {Gamma | (exists  n, path (restrict_by restriction Canonical.R) Theta Gamma n)  /\  Gamma  in  Canonical.V_p p}
  V_n:= fun  i => {Gamma | (exists  n, path (restrict_by restriction Canonical.R) Theta Gamma n)  /\  Gamma  in  Canonical.V_n i}

def Set.GeneratedSubI (Theta : Set (Form TotalSet)) (restriction : Set (Form TotalSet)  ->  Prop) : GeneralI (Set (Form TotalSet)) := fun  x =>
  {Gamma | (exists  n, path (restrict_by restriction Canonical.R) Theta Gamma n)  /\  Gamma  in  CanonicalI x}

theorem submodel_canonical_path (Theta : Set (Form TotalSet)) (r : Set (Form TotalSet)  ->  Prop) (rt : r Theta) : path (Theta.GeneratedSubmodel r).R Gamma Delta n  ->  path (restrict_by r Canonical.R) Gamma Delta n := by
  intro h
  induction n generalizing Gamma Delta with
  | zero =>
      simp [path] at h  |- 
      exact h
  | succ n ih =>
      have <Eta, <h1, h2>> := h
      have := ih h2
      clear h h2
      exists Eta
      apply And.intro
      . simp [Set.GeneratedSubmodel] at h1
        have <<n, l1>, <<m, l2>, l3>> := h1
        simp [restrict_by, l3]
        apply And.intro <;>
        . apply path_restr'
          repeat assumption
      . exact this

theorem path_root (Theta : Set (Form TotalSet)) (r : Set (Form TotalSet)  ->  Prop) : path (restrict_by r Canonical.R) Theta Gamma n  ->  path (Theta.GeneratedSubmodel r).R Theta Gamma n := by
  induction n generalizing Theta Gamma with
  | zero => intro h; exact h
  | succ n ih =>
      simp only [path]
      intro <Delta, <h1, h2>>
      exists Delta
      apply And.intro
      . simp [Set.GeneratedSubmodel]
        apply And.intro
        . exists n
        . apply And.intro
          . exists (n+1)
            simp [path]
            exists Delta
          . exact h1.2.2
      . apply ih
        exact h2

def WitnessedModel {Theta : Set (Form TotalSet)} (_ : MCS Theta) (_ : witnessed Theta) : GeneralModel TotalSet := Theta.GeneratedSubmodel witnessed
def WitnessedI {Theta : Set (Form TotalSet)} (_ : MCS Theta) (_ : witnessed Theta) : GeneralI (Set (Form TotalSet)) := Theta.GeneratedSubI witnessed

def CompletedModel {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) : GeneralModel TotalSet where
  W := Set (Form TotalSet)
  R := fun  Gamma => fun  Delta => ((WitnessedModel mcs wit).R Gamma Delta)  \/  (Gamma = {Form.bttm}  /\  Delta = Theta)
  V_p:= fun  p => (WitnessedModel mcs wit).V_p p
  V_n:= fun  i => if (WitnessedModel mcs wit).V_n i  !=  {}
              then  (WitnessedModel mcs wit).V_n i
              else { {Form.bttm} }
def CompletedI {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) : GeneralI (Set (Form TotalSet)) := fun  x =>
  if (WitnessedI mcs wit) x  !=  {}
              then  (WitnessedI mcs wit) x
              else { {Form.bttm} }

-- Lemma 3.11, Blackburn 1998, pg. 637
lemma subsingleton_valuation : forall  {Theta : Set (Form TotalSet)} {R : Set (Form TotalSet)  ->  Prop} (i : NOM TotalSet), MCS Theta  ->  ((Theta.GeneratedSubmodel R).V_n i).Subsingleton := by
  -- the hypothesis MCS Theta is not necessary
  --  but to prove the theorem without it would complicate
  --  the code, and anyway, we'll only ever use MCS-generated submodels
  simp only [Set.Subsingleton, Set.GeneratedSubmodel]
  intro Theta restr i Theta_MCS Gamma <<n, h1>, <Gamma_MCS, Gamma_i>>  Delta <<m, h2>, <Delta_MCS, Delta_i>>
  rw [ <- (@not_not (Gamma = Delta))]
  simp only [Set.ext_iff, not_forall, iff_iff_implies_and_implies,
      implication_disjunction, not_and, negated_disjunction, not_not, conj_comm]
  intro <phi, h>
  apply Or.elim h
  . clear h
    intro <h3, h4>
    apply h4
    have := restrict_R_iter_pos h1 ((Proof.MCS_conj Gamma_MCS i phi).mp <Gamma_i, h3>)
    have := Proof.MCS_mp Theta_MCS (Proof.MCS_thm Theta_MCS (Proof.ax_nom_instance i n m)) this
    have := restrict_R_iter_nec this h2
    apply Proof.MCS_mp
    repeat assumption
  . clear h
    intro <h3, h4>
    apply h3
    have := restrict_R_iter_pos h2 ((Proof.MCS_conj Delta_MCS i phi).mp <Delta_i, h4>)
    have := Proof.MCS_mp Theta_MCS (Proof.MCS_thm Theta_MCS (Proof.ax_nom_instance i m n)) this
    have := restrict_R_iter_nec this h1
    apply Proof.MCS_mp
    repeat assumption

lemma subsingleton_i : forall  {Theta : Set (Form TotalSet)} {R : Set (Form TotalSet)  ->  Prop} (x : SVAR), MCS Theta  ->  ((Theta.GeneratedSubI R) x).Subsingleton := by
  simp only [Set.Subsingleton, Set.GeneratedSubmodel]
  intro Theta restr x Theta_MCS Gamma <<n, h1>, <Gamma_MCS, Gamma_i>>  Delta <<m, h2>, <Delta_MCS, Delta_i>>
  rw [ <- (@not_not (Gamma = Delta))]
  simp only [Set.ext_iff, not_forall, iff_iff_implies_and_implies,
      implication_disjunction, not_and, negated_disjunction, not_not, conj_comm]
  intro <phi, h>
  apply Or.elim h
  . clear h
    intro <h3, h4>
    apply h4
    have := restrict_R_iter_pos h1 ((Proof.MCS_conj Gamma_MCS x phi).mp <Gamma_i, h3>)
    have := Proof.MCS_mp Theta_MCS (Proof.MCS_thm Theta_MCS (Proof.ax_nom_instance' x n m)) this
    have := restrict_R_iter_nec this h2
    apply Proof.MCS_mp
    repeat assumption
  . clear h
    intro <h3, h4>
    apply h3
    have := restrict_R_iter_pos h2 ((Proof.MCS_conj Delta_MCS x phi).mp <Delta_i, h4>)
    have := Proof.MCS_mp Theta_MCS (Proof.MCS_thm Theta_MCS (Proof.ax_nom_instance' x m n)) this
    have := restrict_R_iter_nec this h1
    apply Proof.MCS_mp
    repeat assumption

lemma wit_subsingleton_valuation {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) (i : NOM TotalSet) : ((WitnessedModel mcs wit).V_n i).Subsingleton := by
  rw [WitnessedModel]
  apply subsingleton_valuation
  assumption

lemma wit_subsingleton_i {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) (x : SVAR) : ((WitnessedI mcs wit) x).Subsingleton := by
  rw [WitnessedI]
  apply subsingleton_i
  assumption

lemma completed_singleton_valuation {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) (i : NOM TotalSet) : exists  Gamma : Set (Form TotalSet), (CompletedModel mcs wit).V_n i = {Gamma} := by
  simp only [CompletedModel]
  split
  . next h =>
      have <Gamma, hGamma> := Set.nonempty_iff_ne_empty.mpr h
      exists Gamma
      apply (Set.subsingleton_iff_singleton hGamma).mp
      apply wit_subsingleton_valuation
  . exact <_, rfl>

lemma completed_singleton_i {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) (x : SVAR) : exists  Gamma : Set (Form TotalSet), (CompletedI mcs wit) x = {Gamma} := by
  simp only [CompletedI]
  split
  . next h =>
      have <Gamma, hGamma> := Set.nonempty_iff_ne_empty.mpr h
      exists Gamma
      apply (Set.subsingleton_iff_singleton hGamma).mp
      apply wit_subsingleton_i
  . exact <_, rfl>

def Set.MCS_in (Gamma : Set (Form TotalSet)) {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) : Prop := exists  n, path (WitnessedModel mcs wit).R Theta Gamma n

theorem mcs_in_prop {Gamma Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) : Gamma.MCS_in mcs wit  ->  (MCS Gamma  /\  witnessed Gamma) := by
  intro <n, h>
  cases n with
  | zero =>
      simp [path] at h
      simp [ <- h, mcs, wit]
  | succ n =>
      have <Delta, h1, h2> := h
      clear h2
      simp [WitnessedModel, Set.GeneratedSubmodel, Canonical] at h1
      have <h3, <m, h4>, h5> := h1
      clear h1 h3
      simp [h5.2.1]
      apply path_restr' h4
      exact wit

theorem mcs_in_wit {Gamma Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) : Gamma.MCS_in mcs wit  ->  (exists  n, path (restrict_by witnessed Canonical.R) Theta Gamma n) := by
  intro <n, h>
  exists n
  cases n with
  | zero =>
      simp [path] at h  |- 
      exact h
  | succ n =>
      simp [path]
      have <Delta, h1, h2> := h
      exists Delta
      apply And.intro
      . apply submodel_canonical_path
        repeat assumption
      . have <<_, l>, <<_, r1>, r2>> := h1
        simp [restrict_by, r2]
        apply And.intro <;>
        . apply path_restr'
          repeat assumption

def needs_dummy {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) := (exists  i, ((CompletedModel mcs wit).V_n i) = { (Set.singleton Form.bttm) })  \/ 
                                                                                 (exists  x, ((CompletedI mcs wit) x) = { (Set.singleton Form.bttm) })

def Set.is_dummy (Gamma : Set (Form TotalSet)) {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) := needs_dummy mcs wit  /\  Gamma = {Form.bttm}


theorem choose_subtype {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta)  : ((completed_singleton_valuation mcs wit i).choose.MCS_in mcs wit)  \/  (completed_singleton_valuation mcs wit i).choose.is_dummy mcs wit := by
  apply choice_intro (fun  Gamma => (Set.MCS_in Gamma mcs wit)  \/  (Set.is_dummy Gamma mcs wit))
  intro Gamma h
  simp [CompletedModel, WitnessedModel, Set.GeneratedSubmodel] at h
  split at h
  . next c =>
      apply Or.inr
      apply And.intro
      . apply Or.inl
        exists i
        simp [CompletedModel, WitnessedModel, Set.GeneratedSubmodel, c]
        apply Eq.refl
      . exact (Set.singleton_eq_singleton_iff.mp h).symm
  . apply Or.inl
    have Gamma_mem : Gamma  in  {Gamma | (exists  n, path (restrict_by witnessed Canonical.R) Theta Gamma n)  /\  Gamma  in  Canonical.V_n i} := by
      rw [h]; exact Set.mem_singleton _
    simp only [Set.mem_setOf_eq] at Gamma_mem
    have <<n, pth>, _> := Gamma_mem
    simp [Set.MCS_in, WitnessedModel]
    exists n
    apply path_root
    exact pth

theorem choose_subtype' {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) : ((completed_singleton_i mcs wit i).choose.MCS_in mcs wit)  \/  (completed_singleton_i mcs wit i).choose.is_dummy mcs wit := by
  apply choice_intro (fun  Gamma => (Set.MCS_in Gamma mcs wit)  \/  (Set.is_dummy Gamma mcs wit))
  intro Gamma h
  simp [CompletedI, WitnessedI, Set.GeneratedSubI] at h
  split at h
  . next c =>
      apply Or.inr
      apply And.intro
      . apply Or.inr
        exists i
        simp [CompletedI, WitnessedI, Set.GeneratedSubI, c]
        apply Eq.refl
      . apply Eq.symm
        simp at h
        exact h
  . apply Or.inl
    have Gamma_mem : Gamma  in  {Gamma | (exists  n, path (restrict_by witnessed Canonical.R) Theta Gamma n)  /\  Gamma  in  CanonicalI i} := by simp [h]
    simp at Gamma_mem
    have <<n, pth>, _> := Gamma_mem
    simp [Set.MCS_in, WitnessedModel]
    exists n
    apply path_root
    exact pth


-- pg. 638: "we only glue on a dummy state when we are forced to"
--    we define the set of states as Gamma.MCS_in  \/  Gamma.is_dummy
--    where is_dummy contains the assumption that we are *forced*
--    to glue a dummy
noncomputable def StandardCompletedModel {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) : Model TotalSet :=
    <{Gamma : Set (Form TotalSet) // Gamma.MCS_in mcs wit  \/  Gamma.is_dummy mcs wit},
      fun  Gamma => fun  Delta => (CompletedModel mcs wit).R Gamma.1 Delta.1,
      fun  p => {Gamma | Gamma.1  in  ((CompletedModel mcs wit).V_p p)},
      fun  i => <(completed_singleton_valuation mcs wit i).choose, choose_subtype mcs wit>>

noncomputable def StandardCompletedI {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) : I (StandardCompletedModel mcs wit).W :=
    fun  x => <(completed_singleton_i mcs wit x).choose, choose_subtype' mcs wit>

theorem sat_dual_all_ex : ((M,s,g)  |=  (all x, phi))  <->  (M,s,g)  |=  ~(ex x, ~phi) := by
  apply Iff.intro
  . intro h; simp only [Form.bind_dual, neg_sat, not_not] at *
    intro g' var
    simp only [Form.bind_dual, neg_sat, not_not] at *
    apply h
    repeat assumption
  . intro h; simp only [Form.bind_dual, neg_sat, not_not] at *
    intro g' var
    have := h g' var
    simp only [Form.bind_dual, neg_sat, not_not] at this
    exact this

theorem sat_dual_nec_pos : ((M,s,g)  |=  ([]  phi))  <->  (M,s,g)  |=  ~(<>  ~phi) := by
  apply Iff.intro
  . intro h; simp only [Form.diamond, neg_sat, not_not] at *
    intro _ _
    simp only [neg_sat, not_not] at *
    apply h
    repeat assumption
  . intro h; simp only [Form.diamond, neg_sat, not_not] at *
    intro s' r
    have := h s' r
    simp only [neg_sat, not_not] at this
    exact this

@[simp]
def coe (Delta : Set (Form TotalSet)) {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) (h : Delta.MCS_in mcs wit) : (StandardCompletedModel mcs wit).W := <Delta, Or.inl h>

def statement (phi : Form TotalSet) {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) := forall  {Delta : Set (Form TotalSet)}, (h : Delta.MCS_in mcs wit)  ->  phi  in  Delta  <->  (StandardCompletedModel mcs wit, coe Delta mcs wit h, StandardCompletedI mcs wit)  |=  phi


lemma truth_bttm : forall  {Theta : Set (Form TotalSet)}, (mcs : MCS Theta)  ->  (wit : witnessed Theta)  ->  (statement False mcs wit) := by
  intro _ mcs' wit' Delta h
  have := (mcs_in_prop mcs' wit' h).1
  apply Iff.intro
  . intro h
    exact this.1 (Proof.Gamma_premise h)
  . simp

lemma truth_prop : forall  {Theta : Set (Form TotalSet)} {p : PROP}, (mcs : MCS Theta)  ->  (wit : witnessed Theta)  ->  (statement p mcs wit) := by
  intro Theta  _ mcs wit Delta h
  have <D_mcs, _> := (mcs_in_prop mcs wit h)
  apply Iff.intro
  . intro hl
    apply And.intro
    . apply mcs_in_wit
      exact h
    . exact <D_mcs, hl>
  . intro a
    exact a.2.2

lemma truth_nom_help : forall  {Theta : Set (Form TotalSet)} {i : NOM TotalSet}, (mcs : MCS Theta)  ->  (wit : witnessed Theta)  ->  forall  {Delta : Set (Form TotalSet)}, Delta.MCS_in mcs wit  ->  (i  in  Delta  <->  ((StandardCompletedModel mcs wit).V_n i).1 = Delta) := by
  intro Theta i mcs wit Delta h_in
  have <D_mcs, _> := (mcs_in_prop mcs wit h_in)
  simp [StandardCompletedModel, CompletedModel, WitnessedModel]
  apply Iff.intro
  . intro h
    apply choice_intro (fun  Gamma : Set (Form TotalSet) => Gamma = Delta)
    intro Eta eta_eq
    have delta_mem : Delta  in  (Theta.GeneratedSubmodel witnessed).V_n i := by
      simp [Set.GeneratedSubmodel, WitnessedModel] at h_in  |- 
      apply And.intro
      . have <n, h_in> := h_in
        exists n
        exact submodel_canonical_path Theta witnessed wit h_in
      . exact <D_mcs, h>
    split at eta_eq
    . next fls =>
        exfalso
        rw [fls] at delta_mem
        exact (Set.mem_empty_iff_false Delta).mp delta_mem
    . have eta_mem : Eta  in  (Theta.GeneratedSubmodel witnessed).V_n i := by
        rw [eta_eq]; exact Set.mem_singleton _
      apply subsingleton_valuation i mcs
      exact eta_mem
      exact delta_mem
  . intro h
    rw [ <- h] at h_in D_mcs  |- 
    clear h
    apply choice_intro (fun  Gamma : Set (Form TotalSet) => i  in  Gamma)
    intro Eta eta_eq
    split at eta_eq
    . next fls =>
        exfalso
        apply D_mcs.left
        apply choice_intro (fun  Gamma => Gamma  |-  False)
        intro _ a
        simp only [fls, if_pos] at a
        apply Proof.Gamma_premise
        rw [ <-  Set.singleton_eq_singleton_iff.mp a]
        exact Set.mem_singleton _
    . have eta_mem : Eta  in  (Theta.GeneratedSubmodel witnessed).V_n i := by
        rw [eta_eq]; exact Set.mem_singleton _
      simp [Set.GeneratedSubmodel, Canonical] at eta_mem
      exact eta_mem.left.right

lemma truth_svar_help : forall  {Theta : Set (Form TotalSet)} {i : SVAR}, (mcs : MCS Theta)  ->  (wit : witnessed Theta)  ->  forall  {Delta : Set (Form TotalSet)}, Delta.MCS_in mcs wit  ->  (i  in  Delta  <->  (StandardCompletedI mcs wit i).1 = Delta) := by
  intro Theta i mcs wit Delta h_in
  have <D_mcs, _> := (mcs_in_prop mcs wit h_in)
  simp [StandardCompletedI, CompletedI, WitnessedI]
  apply Iff.intro
  . intro h
    apply choice_intro (fun  Gamma : Set (Form TotalSet) => Gamma = Delta)
    intro Eta eta_eq
    have delta_mem : Delta  in  Theta.GeneratedSubI witnessed i := by
      simp [Set.GeneratedSubI, WitnessedI] at h_in  |- 
      apply And.intro
      . have <n, h_in> := h_in
        exists n
        exact submodel_canonical_path Theta witnessed wit h_in
      . simp [CanonicalI, h, D_mcs]
    split at eta_eq
    . next fls =>
        exfalso
        rw [ <- @not_not ((Theta.GeneratedSubI witnessed i) = {}),  <- Ne,
           <- Set.nonempty_iff_ne_empty, Set.nonempty_def, not_exists] at fls
        apply fls Delta
        exact delta_mem
    . have eta_mem : Eta  in  Theta.GeneratedSubI witnessed i := by simp [eta_eq]
      apply subsingleton_i i mcs
      exact eta_mem
      exact delta_mem
  . intro h
    rw [ <- h] at h_in D_mcs  |- 
    clear h
    apply choice_intro (fun  Gamma : Set (Form TotalSet) => i  in  Gamma)
    intro Eta eta_eq
    split at eta_eq
    . next fls =>
        exfalso
        apply D_mcs.left
        apply choice_intro (fun  Gamma => Gamma  |-  False)
        intro _ a
        simp [fls, Set.eq_singleton_iff_unique_mem] at a
        apply Proof.Gamma_premise
        exact a.left.left
    . have eta_mem : Eta  in  Theta.GeneratedSubI witnessed i := by simp [eta_eq]
      simp [Set.GeneratedSubI, CanonicalI] at eta_mem
      exact eta_mem.right.right

lemma truth_nom : forall  {Theta : Set (Form TotalSet)} {i : NOM TotalSet}, (mcs : MCS Theta)  ->  (wit : witnessed Theta)  ->  (statement i mcs wit) := by
  intro Theta i mcs wit Delta h_in
  apply Iff.intro
  . intro h
    simp only [Sat, coe]
    apply Subtype.eq
    simp only
    apply Eq.symm
    apply (truth_nom_help mcs wit h_in).mp
    exact h
  . simp only [coe, Sat]
    intro h
    apply (truth_nom_help mcs wit h_in).mpr
    rw [Subtype.coe_eq_iff]
    exists (Or.inl h_in)
    apply Eq.symm
    exact h

lemma truth_svar : forall  {Theta : Set (Form TotalSet)} {i : SVAR}, (mcs : MCS Theta)  ->  (wit : witnessed Theta)  ->  (statement i mcs wit) := by
  intro Theta i mcs wit Delta h_in
  apply Iff.intro
  . intro h
    simp only [Sat, coe]
    apply Subtype.eq
    simp only
    apply Eq.symm
    apply (truth_svar_help mcs wit h_in).mp
    exact h
  . simp only [coe, Sat]
    intro h
    apply (truth_svar_help mcs wit h_in).mpr
    rw [Subtype.coe_eq_iff]
    exists (Or.inl h_in)
    apply Eq.symm
    exact h

lemma truth_impl : forall  {Theta : Set (Form TotalSet)}, (mcs : MCS Theta)  ->  (wit : witnessed Theta)  ->  (statement phi mcs wit)  ->  (statement psi mcs wit)  ->  statement (phi  -->  psi) mcs wit := by
  intro Theta mcs wit ih_phi ih_psi Delta h_in
  have <D_mcs, _> := (mcs_in_prop mcs wit h_in)
  apply Iff.intro
  . intro h1 h2
    apply (ih_psi h_in).mp
    apply Proof.MCS_mp
    repeat assumption
    exact (ih_phi h_in).mpr h2
  . intro sat_phi_psi
    unfold statement at ih_phi ih_psi
    rw [Sat,  <- ih_phi,  <- ih_psi, Proof.MCS_impl] at sat_phi_psi
    repeat assumption

lemma has_state_symbol (s : (StandardCompletedModel mcs wit).W) : (exists  i, (StandardCompletedModel mcs wit).V_n i = s)  \/  (exists  x, StandardCompletedI mcs wit x = s) := by
  apply Or.elim s.2
  . intro s_in
    apply Or.inl
    have <s_mcs, s_wit> := (mcs_in_prop mcs wit s_in)
    have <i, sat_i> := Proof.MCS_rich s_mcs s_wit
    simp [truth_nom mcs wit s_in] at sat_i
    exists i
    apply Eq.symm
    exact sat_i
  -- absolutely unnecesarily ugly, but at least it works
  . intro <needs_dummy, s_is_dummy>
    apply Or.elim needs_dummy
    . intro <i, h>
      apply Or.inl
      exists i
      simp [StandardCompletedModel]
      apply Subtype.eq
      apply choice_intro (fun  Gamma => Gamma = s.1)
      rw [h,]
      intro s' eq
      rw [ <- Set.singleton_eq_singleton_iff]
      apply Eq.symm
      rw [s_is_dummy]
      exact eq
    . intro <i, h>
      apply Or.inr
      exists i
      simp [StandardCompletedI]
      apply Subtype.eq
      apply choice_intro (fun  Gamma => Gamma = s.1)
      rw [h]
      intro s' eq
      rw [ <- Set.singleton_eq_singleton_iff]
      apply Eq.symm
      rw [s_is_dummy]
      exact eq

lemma truth_ex : forall  {Theta : Set (Form TotalSet)}, (mcs : MCS Theta)  ->  (wit : witnessed Theta)  ->  (forall  {chi : Form TotalSet}, chi.depth < (ex x, psi).depth  ->  statement chi mcs wit)  ->  statement (ex x, psi) mcs wit := by
  intro Theta mcs wit ih
  intro Delta Delta_in
  have <Delta_mcs, Delta_wit> := (mcs_in_prop mcs wit Delta_in)
  apply Iff.intro
  . intro h
    have <i, mem> := Delta_wit h
    have ih_s := @ih (psi[i//x]) subst_depth''
    rw [ih_s Delta_in] at mem
    apply WeakSoundness Proof.ax_q2_contrap
    exact mem
  . simp only [ex_sat]
    intro <g', g'_var, g'_psi>
    let s := g' x
    apply Or.elim (has_state_symbol s)
    . intro <i, sat_i>
      have ih_s := @ih (psi[i//x]) subst_depth''
      rw [ <- nom_substitution (is_variant_symm.mp g'_var) (Eq.symm sat_i),  <- ih_s] at g'_psi
      have g'_psi := Proof.Gamma_premise g'_psi
      clear g'_var sat_i
      apply Proof.MCS_pf Delta_mcs
      apply Proof.Gamma_mp
      . apply Proof.Gamma_theorem
        apply Proof.ax_q2_contrap
        exact i
      . exact g'_psi
    . intro <y, sat_y>
      have := rename_all_bound psi y (StandardCompletedModel mcs wit) (coe Delta mcs wit Delta_in) g'
      rw [iff_sat] at this
      rw [this] at g'_psi
      clear this
      rw [ <- svar_substitution (substable_after_replace psi) (is_variant_symm.mp g'_var) (Eq.symm sat_y)] at g'_psi
      have r_ih := @ih ((psi.replace_bound y)[y//x]) replace_bound_depth'
      rw [ <- r_ih] at g'_psi
      have := Proof.MCS_with_svar_witness (substable_after_replace psi) Delta_mcs g'_psi
      apply Proof.MCS_mp Delta_mcs; apply Proof.MCS_thm Delta_mcs
    --  exact @exists_replace x psi y
      apply exists_replace; exact y; exact this

/-- Extend `MCS_in` along a witnessed-model edge (`path_root` on the second path component). -/
lemma mcs_in_witnessed_succ {Theta Delta Delta' : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta)
    (_hDelta : Delta.MCS_in mcs wit) (hR : (WitnessedModel mcs wit).R Delta Delta') : Delta'.MCS_in mcs wit := by
  simp only [WitnessedModel, Set.GeneratedSubmodel] at hR
  obtain <_, <m, hpath>, _> := hR
  exists m
  exact path_root Theta witnessed hpath

/-- Extract the witnessed edge from a completed-model step (no dummy glue). -/
lemma completed_to_witnessed {Theta Delta Delta' : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta)
    (_hDelta : Delta.MCS_in mcs wit) (hR : (CompletedModel mcs wit).R Delta Delta') :
    (WitnessedModel mcs wit).R Delta Delta' := by
  simp only [CompletedModel] at hR
  cases hR with
  | inl hW => exact hW
  | inr h =>
    exfalso
    rw [h.1] at _hDelta
    exact (mcs_in_prop mcs wit _hDelta).1.1 (Proof.Gamma_premise (Set.mem_singleton Form.bttm))

lemma mcs_in_completed_succ {Theta Delta Delta' : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta)
    (hDelta : Delta.MCS_in mcs wit) (hR : (CompletedModel mcs wit).R Delta Delta') : Delta'.MCS_in mcs wit :=
  mcs_in_witnessed_succ mcs wit hDelta (completed_to_witnessed mcs wit hDelta hR)

lemma completed_canonical {Theta Delta Delta' : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta)
    (hDelta : Delta.MCS_in mcs wit) (hR : (CompletedModel mcs wit).R Delta Delta') : Canonical.R Delta Delta' :=
  (completed_to_witnessed mcs wit hDelta hR).2.2

/-- K-distribution lifted to theorems: `[] ` is monotone under provable implication. -/
def nec_mono {N : Set Nat} {a b : Form N} (h :  |-  (a  -->  b)) :  |-  ([]  a  -->  []  b) :=
  Proof.mp Proof.ax_k (Proof.necess h)

/-- `[] ` distributes over conjunction inside an MCS. -/
lemma box_conj_mem {Delta : Set (Form TotalSet)} (mcs : MCS Delta) {a b : Form TotalSet}
    (h1 : []  a  in  Delta) (h2 : []  b  in  Delta) : []  (a  /\  b)  in  Delta := by
  have s1 : ([]  a  -->  []  (b  -->  (a  /\  b)))  in  Delta :=
    Proof.MCS_thm mcs (nec_mono (Proof.tautology conj_intro))
  have s2 : []  (b  -->  (a  /\  b))  in  Delta := Proof.MCS_mp mcs s1 h1
  have s3 : ([]  (b  -->  (a  /\  b))  -->  ([]  b  -->  []  (a  /\  b)))  in  Delta := Proof.MCS_thm mcs Proof.ax_k
  have s4 : ([]  b  -->  []  (a  /\  b))  in  Delta := Proof.MCS_mp mcs s3 s2
  exact Proof.MCS_mp mcs s4 h2

/-- The conjunction of any finite list of `{chi | [] chi  in  Delta}`-members has its box in `Delta`. -/
lemma box_conjunction_mem {Delta : Set (Form TotalSet)} (mcs : MCS Delta)
    (L : List {chi : Form TotalSet | []  chi  in  Delta}) :
    []  (conjunction {chi : Form TotalSet | []  chi  in  Delta} L)  in  Delta := by
  induction L with
  | nil => exact Proof.MCS_thm mcs (Proof.necess (Proof.tautology imp_refl))
  | cons c t ih =>
      have hc : []  c.val  in  Delta := c.2
      exact box_conj_mem mcs hc ih

/-- If everything provable from `{chi | [] chi  in  Delta}` boxes back into `Delta`: `[] `-introduction
    over the canonical predecessor set. -/
lemma box_of_consequence {Delta : Set (Form TotalSet)} (mcs : MCS Delta) {a : Form TotalSet}
    (h : {chi : Form TotalSet | []  chi  in  Delta}  |-  a) : []  a  in  Delta := by
  obtain <L, pf> := h
  have hconjbox := box_conjunction_mem mcs L
  have hmono : ([]  (conjunction {chi : Form TotalSet | []  chi  in  Delta} L)  -->  []  a)  in  Delta :=
    Proof.MCS_thm mcs (nec_mono pf)
  exact Proof.MCS_mp mcs hmono hconjbox

/-- If `<> psi  in  Delta` and `Delta` is MCS, the one-step successor seed
    `{psi}  U  {chi | [] chi  in  Delta}` is consistent.  (Oltean's `set_family` base case.) -/
theorem diamond_extension_consistent {Delta : Set (Form TotalSet)} (mcs : MCS Delta) (psi : Form TotalSet)
    (hdia : <> psi  in  Delta) : consistent ({psi}  U  {chi | [] chi  in  Delta}) := by
  intro hcon
  rw [Set.union_comm] at hcon
  have hB : {chi : Form TotalSet | []  chi  in  Delta}  |-  (psi  -->  False) := Proof.Deduction.mpr hcon
  have hbox : []  (psi  -->  False)  in  Delta := box_of_consequence mcs hB
  have hdia' : ([]  (psi  -->  False)  -->  False)  in  Delta := hdia
  exact mcs.1 (Proof.Gamma_premise (Proof.MCS_mp mcs hdia' hbox))

/-- Consistency of the witnessed-successor seed `succ_seed` (the canonical box-reduct
    together with all accumulated Henkin witness conditionals).  This is the compactness
    step of the STL-fix construction: any finite subset lands in a single stage `wcond N`,
    whose conjunction `<> `-belongs to `Delta`, so `diamond_extension_consistent` applies. -/
theorem succ_seed_consistent {Delta : Set (Form TotalSet)} (mcs : MCS Delta) (wit : witnessed Delta)
    {psi : Form TotalSet} (hdia : <> psi  in  Delta) (enum : Nat  ->  Form TotalSet) :
    consistent (succ_seed enum mcs wit hdia) := by
  intro hbot
  obtain <L, pf> := hbot
  obtain <N, hbound> := seed_list_bound enum mcs wit hdia L
  set cN := conjunction' (wcond enum mcs wit hdia N).val with hcN
  -- `box-reduct  U  {cN}` derives every premise in `L`, hence their conjunction.
  have hconj : ({chi | []  chi  in  Delta}  U  {cN})  |-  conjunction (succ_seed enum mcs wit hdia) L := by
    apply Gamma_conjunction_of_premises
    intro x hx
    by_cases hw : x.val  in  (wcond enum mcs wit hdia N).val
    * have h1 : ({cN} : Set (Form TotalSet))  |-  x.val :=
        Proof.Gamma_mp (Proof.Gamma_theorem (conj'_imp_mem hw) {cN}) (Proof.Gamma_premise rfl)
      exact Proof.increasing_consequence h1 (fun a ha => Or.inr ha)
    * have hb : []  x.val  in  Delta := (hbound x hx).resolve_right hw
      exact Proof.Gamma_premise (Or.inl hb)
  have hbox_bot : ({chi | []  chi  in  Delta}  U  {cN})  |-  (False : Form TotalSet) :=
    Proof.Gamma_mp (Proof.Gamma_theorem pf _) hconj
  have hB : {chi | []  chi  in  Delta}  |-  (cN  -->  False) := Proof.Deduction.mpr hbox_bot
  have hbox : []  (cN  -->  False)  in  Delta := box_of_consequence mcs hB
  have hdiaN : ([]  (cN  -->  False)  -->  False)  in  Delta := (wcond enum mcs wit hdia N).2.2
  exact mcs.1 (Proof.Gamma_premise (Proof.MCS_mp mcs hdiaN hbox))

/-- Witnessed <> -successor existence lemma (replaces the false `enough_noms_diamond_seed`).
    From `<> psi  in  Delta` build an MCS `Gamma'` with `Canonical.R Delta Gamma'`, `psi  in  Gamma'`, and `witnessed Gamma'`,
    via Oltean's Henkin construction (`succ_seed` + `RegularLindenbaumLemma`). -/
theorem diamond_succ_mcs {Delta : Set (Form TotalSet)} (mcs : MCS Delta) (wit : witnessed Delta) (psi : Form TotalSet)
    (hdia : <> psi  in  Delta) :
    exists  Gamma' : Set (Form TotalSet),
      Canonical.R Delta Gamma'  /\  psi  in  Gamma'  /\  MCS Gamma'  /\  witnessed Gamma' := by
  obtain <f, f_inj> := exists_injective_nat (Form TotalSet)
  let enum := f.invFun
  have enum_inv : forall  phi, enum (f phi) = phi := fun phi => f.leftInverse_invFun f_inj phi
  have hcons := succ_seed_consistent mcs wit hdia enum
  obtain <Gamma', hsub, hmcs> := RegularLindenbaumLemma (succ_seed enum mcs wit hdia) hcons
  refine <Gamma', ?_, ?_, hmcs, ?_>
  * -- `Canonical.R Delta Gamma'`: the box-reduct of `Delta` is contained in `Gamma'`.
    simp only [Canonical, restrict_by, mcs, hmcs, true_and]
    intro chi hbox
    exact hsub (Or.inl hbox)
  * -- `psi  in  Gamma'`: `psi` is at stage 0 of the witness family.
    refine hsub (Or.inr <0, ?_>)
    show psi  in  [psi]
    exact List.mem_cons_self
  * -- `witnessed Gamma'`: every existential in `Gamma'` is `enum n`, and stage `n+1` carries its witness.
    intro chi hchi
    split
    * next x sigma =>
        have hchi' : (ex x, sigma)  in  Gamma' := hchi
        obtain <i, hi> :=
          wcond_step_mem enum mcs wit hdia (f (ex x, sigma)) x sigma (enum_inv (ex x, sigma))
        have hcond : ((ex x, sigma)  -->  sigma[i // x])  in  Gamma' := hsub (Or.inr <f (ex x, sigma) + 1, hi>)
        exact <i, Proof.MCS_mp hmcs hcond hchi'>
    * assumption

/-- Extend a restrict-by-witnessed path along one canonical step. -/
lemma restrict_canonical_succ {Theta Delta Delta' : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta)
    (hDelta : Delta.MCS_in mcs wit) (hR : Canonical.R Delta Delta') (hDelta' : witnessed Delta') :
    exists  n, path (restrict_by witnessed Canonical.R) Theta Delta' n := by
  obtain <n, hpath> := mcs_in_wit mcs wit hDelta
  have hw : witnessed Delta := (mcs_in_prop mcs wit hDelta).2
  refine <n + 1, Delta, <hw, hDelta', hR>, hpath>

/-- From `<> psi  in  Delta` build a completed-model successor of `Delta` that contains `psi`. -/
lemma diamond_completed_succ {Theta Delta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta)
    (hDelta : Delta.MCS_in mcs wit) (psi : Form TotalSet) (hdia : <> psi  in  Delta) :
    exists  Delta' : Set (Form TotalSet),
      Delta'.MCS_in mcs wit  /\  (CompletedModel mcs wit).R Delta Delta'  /\  (psi  in  Delta') := by
  have <Delta_mcs, hwitDelta> := mcs_in_prop mcs wit hDelta
  obtain <Gamma', hcan, hpsi, hmcs, hwitGamma'> := diamond_succ_mcs Delta_mcs hwitDelta psi hdia
  obtain <m, hpath> := restrict_canonical_succ mcs wit hDelta hcan hwitGamma'
  have hW : (WitnessedModel mcs wit).R Delta Gamma' := by
    simp only [WitnessedModel, Set.GeneratedSubmodel]
    obtain <n, hDeltapath> := mcs_in_wit mcs wit hDelta
    exact <<n, hDeltapath>, <m, hpath>, hcan>
  refine <Gamma', mcs_in_witnessed_succ mcs wit hDelta hW, Or.inl hW, hpsi>

-- Truth lemma, []  case.  Oltean's original development never formalized this case (nor
-- `truth_all` for `forall `); the arxiv blueprint lists `truth_box` as TL work.  The  ->  direction
-- uses `R_nec` on witnessed/canonical successors and the subformula IH; the  <-  direction
-- uses MCS maximality + `diamond_completed_succ` (blocked on `diamond_extension_consistent`
-- and witnessed lift in `diamond_succ_mcs`).
lemma truth_box {psi : Form TotalSet} : forall  {Theta : Set (Form TotalSet)}, (mcs : MCS Theta)  ->  (wit : witnessed Theta)  -> 
    (statement psi mcs wit)  ->  statement ([] psi) mcs wit := by
  intro Theta mcs wit ih Delta h_in
  have <Delta_mcs, _> := mcs_in_prop mcs wit h_in
  apply Iff.intro
  * intro h_box
    simp only [Sat]
    intro s' hR
    have hR' : (CompletedModel mcs wit).R Delta s'.1 := hR
    cases s'.2 with
    | inl _ =>
      have hDelta' := mcs_in_completed_succ mcs wit h_in hR'
      have hmem := R_nec h_box (completed_canonical mcs wit h_in hR')
      exact (ih hDelta').mp hmem
    | inr hdummy =>
      exfalso
      rcases hdummy with <_, hbot>
      have hbot_in := mcs_in_completed_succ mcs wit h_in hR'
      rw [hbot] at hbot_in
      exact (mcs_in_prop mcs wit hbot_in).1.1 (Proof.Gamma_premise (Set.mem_singleton Form.bttm))
  * intro h_sat
    by_cases h : [] psi  in  Delta
    * exact h
    * exfalso
      have hnec : ~([] psi)  in  Delta := (Proof.MCS_max Delta_mcs).mp h
      have hdia : <> ~psi  in  Delta :=
        Proof.MCS_pf Delta_mcs (Proof.Gamma_mp (Proof.Gamma_theorem (@Proof.not_nec_to_diamond TotalSet psi) Delta) (Proof.Gamma_premise hnec))
      obtain <Delta', hDelta'in, hR', hneg> := diamond_completed_succ mcs wit h_in (~psi) hdia
      have hsatpsi : (StandardCompletedModel mcs wit, coe Delta' mcs wit hDelta'in, StandardCompletedI mcs wit)  |=  psi := by
        simp only [Sat] at h_sat
        exact h_sat (coe Delta' mcs wit hDelta'in) (by simpa [StandardCompletedModel, CompletedModel, coe] using hR')
      have hpsimem : psi  in  Delta' := (ih hDelta'in).mpr hsatpsi
      have <Delta'_mcs, _> := mcs_in_prop mcs wit hDelta'in
      have hbot : Form.bttm  in  Delta' := Proof.MCS_mp Delta'_mcs hneg hpsimem
      exact Delta'_mcs.1 (Proof.Gamma_premise hbot)

-- Truth lemma, `forall ` case.  Handled uniformly (free and non-free `x`) by the dual of the
-- `truth_ex` machinery: in the completed model every state is named by a nominal or an
-- svar (`has_state_symbol`), so each variant reduces to a substitution instance of `psi`
-- whose statement is available through the depth-indexed `ih`.  Forward uses the `ax_q2`
-- instances; backward uses `witnessed` on `ex x, ~psi` (via `bind_dual`) for a contradiction.
lemma truth_all {psi : Form TotalSet} {x : SVAR} : forall  {Theta : Set (Form TotalSet)}, (mcs : MCS Theta)  ->  (wit : witnessed Theta)  -> 
    (forall  {chi : Form TotalSet}, chi.depth < (all x, psi).depth  ->  statement chi mcs wit)  ->  statement (all x, psi) mcs wit := by
  intro Theta mcs wit ih Delta h_in
  have <Delta_mcs, Delta_wit> := (mcs_in_prop mcs wit h_in)
  apply Iff.intro
  * -- forward: `(all x, psi)  in  Delta  ->  satisfaction`
    intro hall
    simp only [Sat]
    intro g' hvar
    apply Or.elim (has_state_symbol (g' x))
    * -- the variant value is named by a nominal `i`
      intro <i, sat_i>
      have hmem : psi[i//x]  in  Delta :=
        Proof.MCS_pf Delta_mcs (Proof.Gamma_mp (Proof.Gamma_theorem (Proof.ax_q2_nom psi x i) Delta) (Proof.Gamma_premise hall))
      have hsatsub := ((@ih (psi[i//x]) subst_depth_bind) h_in).mp hmem
      exact (nom_substitution (is_variant_symm.mp hvar) sat_i.symm).mp hsatsub
    * -- the variant value is named by an svar `y`; rename bound vars to substitute safely
      intro <y, sat_y>
      have hpf :  |-  ((all x, psi)  -->  ((psi.replace_bound y)[y//x])) :=
        Proof.hs
          (Proof.mp Proof.b363 (Proof.general x (Proof.mp (Proof.tautology iff_elim_l) (rename_all_bound_pf psi y))))
          (Proof.ax_q2_svar (psi.replace_bound y) x y (substable_after_replace psi))
      have hmem : ((psi.replace_bound y)[y//x])  in  Delta :=
        Proof.MCS_pf Delta_mcs (Proof.Gamma_mp (Proof.Gamma_theorem hpf Delta) (Proof.Gamma_premise hall))
      have hdepth : ((psi.replace_bound y)[y//x]).depth < (all x, psi).depth := by
        rw [subst_depth', replace_bound_depth]; exact sub_depth_bind x psi
      have hsatsub := ((@ih ((psi.replace_bound y)[y//x]) hdepth) h_in).mp hmem
      have hsatrepl :=
        (svar_substitution (substable_after_replace psi) (is_variant_symm.mp hvar) sat_y.symm).mp hsatsub
      have hren := rename_all_bound psi y (StandardCompletedModel mcs wit) (coe Delta mcs wit h_in) g'
      rw [iff_sat] at hren
      exact hren.mpr hsatrepl
  * -- backward: `satisfaction  ->  (all x, psi)  in  Delta`
    intro hsat
    by_contra hnotmem
    have hex : (ex x, ~psi)  in  Delta := by
      by_contra hc
      have h2 : (~(ex x, ~psi))  in  Delta := (Proof.MCS_max Delta_mcs).mp hc
      exact hnotmem ((Proof.MCS_rw Delta_mcs Proof.bind_dual).mpr h2)
    obtain <i, hwit> := Delta_wit hex
    have hwit' : (~(psi[i//x]))  in  Delta := by
      have heq : (~psi)[i//x] = ~(psi[i//x]) := rfl
      rwa [heq] at hwit
    let g := Function.update (StandardCompletedI mcs wit) x ((StandardCompletedModel mcs wit).V_n i)
    have hgvar : is_variant g (StandardCompletedI mcs wit) x := by
      intro z hz; exact Function.update_of_ne (Ne.symm hz) _ _
    have hgx : g x = (StandardCompletedModel mcs wit).V_n i := Function.update_self x _ _
    have hsatg := hsat g hgvar
    have hsatsub := (nom_substitution (is_variant_symm.mp hgvar) hgx).mpr hsatg
    have hmem : psi[i//x]  in  Delta := ((@ih (psi[i//x]) subst_depth_bind) h_in).mpr hsatsub
    exact (Proof.MCS_max Delta_mcs).mpr hwit' hmem

/-- The truth lemma: membership in an `MCS_in` state coincides with satisfaction in the
    completed model.  Structural cases use the `truth_*` lemmas; `ex` uses `truth_ex`. -/
theorem TruthLemma (phi : Form TotalSet) {Theta : Set (Form TotalSet)} (mcs : MCS Theta) (wit : witnessed Theta) :
    statement phi mcs wit := by
  cases phi with
  | bttm => exact truth_bttm mcs wit
  | prop p => exact truth_prop mcs wit
  | nom i => exact truth_nom mcs wit
  | svar x => exact truth_svar mcs wit
  | impl psi chi => exact truth_impl (phi := psi) (psi := chi) mcs wit (TruthLemma psi mcs wit) (TruthLemma chi mcs wit)
  | box psi => exact truth_box mcs wit (TruthLemma psi mcs wit)
  | bind x psi => exact truth_all (psi := psi) (x := x) mcs wit (fun {chi} _ => TruthLemma chi mcs wit)
termination_by phi.depth
decreasing_by
  all_goals first
    | exact sub_depth_impl_l _ _
    | exact sub_depth_impl_r _ _
    | exact sub_depth_box _
    | assumption
