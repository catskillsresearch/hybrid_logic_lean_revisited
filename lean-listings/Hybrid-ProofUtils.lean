import Hybrid.Substitutions
import Hybrid.Proof
import Hybrid.Tautology
import Hybrid.ListUtils

namespace Proof

noncomputable section

def iff_mp (h :  |-  (phi  <->  psi)) :  |-  (phi  -->  psi) :=
  mp (tautology conj_elim_l) h

def iff_mpr (h :  |-  (phi  <->  psi)) :  |-  (psi  -->  phi) :=
  mp (tautology conj_elim_r) h

def hs (h1 :  |-  (phi  -->  psi)) (h2 :  |-  (psi  -->  chi)) :  |-  (phi  -->  chi) :=
  mp (mp (tautology hs_taut) h1) h2

def rename_bound {phi : Form N} (h1 : occurs y phi = false) (h2 : is_substable phi y x) :  |-  ((all x, phi)  <->  all y, phi[y // x]) := by
  rw [Form.iff]
  apply mp
  . apply mp
    . apply tautology
      apply conj_intro
    . have l1 := ax_q2_svar phi x y h2
      have l2 := general y l1
      have l3 := ax_q1 (all x, phi) (phi[y // x]) (notoccurs_notfree h1)
      have l4 := mp l3 l2
      exact l4
  . have <resubst, reid> := rereplacement phi x y h1 h2
    have l1 := ax_q2_svar (phi[y//x]) y x resubst
    rw [reid] at l1
    have l3 := general x l1
    by_cases xy : x = y
    . rw [ <- xy] at h1
      have notf := preserve_notfree x y (notoccurs_notfree (@notocc_beforeafter_subst N phi x y h1))
      have l4 := ax_q1 (all y, phi[y//x]) phi notf
      have l5 := mp l4 l3
      exact l5
    . have notf := preserve_notfree x y (@notfree_after_subst N phi x y xy)
      have l4 := ax_q1 (all y, phi[y//x]) phi notf
      have l5 := mp l4 l3
      exact l5

def rename_bound_ex (h1 : occurs y phi = false) (h2 : is_substable phi y x) :  |-  ((ex x, phi)  <->  ex y, phi[y // x]) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply mp
    . apply tautology
      apply iff_elim_l
    . apply tautology
      apply iff_not
  .
    apply rename_bound
    repeat { simp [occurs, is_substable]; assumption }

-- Quite bothersome to work with subtypes and coerce properly.
-- The code looks ugly, but in essence it follows the proof given
-- in LaTeX.
def Deduction {Gamma : Set (Form N)} : Gamma  |-  (psi  -->  phi) iff (Gamma  U  {psi})  |-  phi := by
  apply TypeIff.intro
  . intro h
    match h with
    | <L, hpf> =>
        have l1 := mp (tautology com12) hpf
        have l2 := mp (tautology imp) l1
        have pfmem : psi  in  Gamma  U  {psi} := by simp
        let L' : List (Gamma  U  {psi}) := <psi, pfmem> :: list_convert L
        rw [conj_incl] at l2
        exact <L', l2>
  . intro h
    match h with
    | <L', hpf> =>
      have t_ax1 := tautology (@ax_1 N (conjunction (Gamma  U  {psi}) L' --> phi) psi)
      have l1 := mp t_ax1 hpf
      have l2 := mp (tautology com12) l1
      by_cases elem : elem' L' psi
      . have t_help := tautology (deduction_helper L' psi (psi --> phi) elem)
        have l3 := mp t_help l2
        have l4 := mp (tautology idem) l3
        have not_elem_L' := eq_false_of_ne_true (@filter'_filters N Gamma psi L')
        let L : List Gamma := list_convert_rev (filter' L' psi) not_elem_L'
        rw [conj_incl_rev (filter' L' psi) not_elem_L'] at l4
        exact <L, l4>
      . have elem : elem' L' psi = false := by simp only [elem]
        let L : List Gamma := list_convert_rev L' elem
        rw [conj_incl_rev L' elem] at l2
        exact <L, l2>

def increasing_consequence (h1 : Gamma  |-  phi) (h2 : Gamma  subseteq  Delta) : Delta  |-  phi := by
  simp [SyntacticConsequence] at h1  |- 
  let <L, pf> := h1
  clear h1
  let L' := list_convert_general h2 L
  exists L'
  rw [conj_incl_general h2 L] at pf
  exact pf

def Gamma_empty {phi : Form N} : {}  |-  phi iff  |-  phi := by
  unfold SyntacticConsequence
  apply TypeIff.intro
  . intro pf
    have <L, pf> := pf
    have := empty_list L
    simp [this, conjunction] at pf
    apply mp
    . have :  |- (((False --> False) --> phi) --> phi) := by
        apply tautology
        apply imp_taut
        eval
      exact this
    . exact pf
  . intro pf
    exists ([] : List {x : Form N | False})
    simp only [conjunction]
    apply mp
    . apply tautology
      apply ax_1
    . exact pf

def Gamma_theorem :  |-  phi  ->  (forall  Gamma, Gamma  |-  phi) := by
  intro h Gamma
  apply increasing_consequence
  apply Gamma_empty.mpr h
  simp

def Gamma_theorem_rev : (forall  Gamma, Gamma  |-  phi)  ->   |-  phi := by
  intro h
  apply Gamma_empty.mp
  apply h

def Gamma_theorem_iff :  |-  phi iff (forall  Gamma, Gamma  |-  phi) := by
  apply TypeIff.intro <;> first | apply Gamma_theorem | apply Gamma_theorem_rev

def Gamma_premise : phi  in  Gamma  ->  Gamma  |-  phi := by
  intro mem
  have : Gamma = Gamma  U  {phi} := by simp [mem]
  rw [this]
  apply Deduction.mp
  apply Gamma_theorem
  apply tautology
  eval

def Gamma_mp_helper1 {Gamma : Set (Form N)} {phi psi chi : Form N} : (Gamma  |-  ((phi  /\  psi)  -->  chi)) iff ((Gamma  U  {phi})  |-  (psi  -->  chi)) := by
  apply TypeIff.intro
  . intro h
    match h with
    | <L, hL> =>
        have l1 := hs hL (tautology exp)
        have l2 : Gamma  |-  (phi  -->  psi  -->  chi) := <L, l1>
        have l3 := Deduction.mp l2
        exact l3
  . intro h
    have h := Deduction.mpr h
    match h with
    | <L, hL> =>
        have l1 := hs hL (tautology imp)
        have l2 : Gamma  |-  (phi  /\  psi  -->  chi) := <L, l1>
        exact l2

def Gamma_mp_helper2 {Gamma : Set (Form N)} {L : List Gamma} (h : Gamma |- (conjunction Gamma L --> psi)) : Gamma  |-  psi := by
  induction L with
  | nil =>
      rw [conjunction] at h
      have <L, hL> := h
      have l1 := mp (tautology com12) hL
      have l2 := mp (tautology (imp_taut imp_refl)) l1
      exists L
  | cons head tail ih =>
      have h := Gamma_mp_helper1.mp h
      have : (Gamma  U  {head}) = Gamma := by simp [head.2]
      rw [this] at h
      exact ih h

def Gamma_mp (h1: Gamma  |-  (phi  -->  psi)) (h2 : Gamma  |-  phi) : Gamma  |-  psi := by
  match h1 with
  | <L1, hL1> =>
    match h2 with
    | <L2, hL2> =>
        have := mp (mp (tautology mp_help) hL1) hL2
        have : Gamma  |-  (conjunction Gamma L2 --> psi) := <L1, this>
        exact Gamma_mp_helper2 this

def Gamma_neg_intro {phi : Form N} (h1 : Gamma  |-  (phi  -->  psi)) (h2 : Gamma  |-  (phi  -->  ~psi)) : Gamma  |-  (~phi) := by
  have l1 := tautology (@neg_intro N phi psi)
  have l2 := Gamma_theorem l1 Gamma
  have l3 := Gamma_mp l2 h1
  have l4 := Gamma_mp l3 h2
  exact l4

def Gamma_neg_elim {phi : Form N} {phi : Form N} (h : Gamma  |-  (~~phi)) : Gamma  |-  phi := by
  have l1 := tautology (@dne N phi)
  have l2 := Gamma_theorem l1 Gamma
  have l3 := Gamma_mp l2 h
  exact l3

def Gamma_conj_intro {phi : Form N} (h1 : Gamma  |-  phi) (h2 : Gamma  |-  psi) : Gamma  |-  (phi  /\  psi) := by
  have l1 := tautology (@conj_intro N phi psi)
  have l2 := Gamma_theorem l1 Gamma
  have l3 := Gamma_mp l2 h1
  have l4 := Gamma_mp l3 h2
  exact l4

def Gamma_conj_elim_l {phi : Form N} (h : Gamma  |-  (phi  /\  psi)) : Gamma  |-  phi := by
  have l1 := tautology (@conj_elim_l N phi psi)
  have l2 := Gamma_theorem l1 Gamma
  have l3 := Gamma_mp l2 h
  exact l3

def Gamma_conj_elim_r {phi : Form N} (h : Gamma  |-  (phi  /\  psi)) : Gamma  |-  psi := by
  have l1 := tautology (@conj_elim_r N phi psi)
  have l2 := Gamma_theorem l1 Gamma
  have l3 := Gamma_mp l2 h
  exact l3

def Gamma_disj_intro_l {phi : Form N} (h : Gamma  |-  phi) : Gamma  |-  (phi  \/  psi) := by
  have l1 := tautology (@disj_intro_l N phi psi)
  have l2 := Gamma_theorem l1 Gamma
  exact Gamma_mp l2 h

def Gamma_disj_intro_r {phi : Form N} (h : Gamma  |-  phi) : Gamma  |-  (psi  \/  phi) := by
  have l1 := tautology (@disj_intro_r N phi psi)
  have l2 := Gamma_theorem l1 Gamma
  exact Gamma_mp l2 h

def Gamma_disj_elim {phi : Form N} (h1 : Gamma  |-  (phi  \/  psi)) (h2 : Gamma  |-  (phi  -->  chi)) (h3 : Gamma  |-  (psi  -->  chi)) : Gamma  |-  chi := by
  have l1 := tautology (@disj_elim N phi psi chi)
  have l2 := Gamma_theorem l1 Gamma
  have l3 := Gamma_mp l2 h1
  have l4 := Gamma_mp l3 h2
  have l5 := Gamma_mp l4 h3
  exact l5

def Gamma_univ_intro {Gamma : Set (Form N)} {phi : Form N} (h1 : forall  psi : Gamma, is_free x psi.1 = false) (h2 : occurs y phi = false) (h3 : is_substable phi y x) : Gamma  |-  phi  ->  Gamma  |-  (all y, phi[y // x]) := by
  intro Gamma_pf_phi
  match Gamma_pf_phi with
  | <L, l1> =>
      have l2 := general x l1
      have := notfreeset L h1
      have l3 := ax_q1 (conjunction Gamma L) phi this
      have l4 := mp l3 l2
      have l5 := iff_mp (rename_bound h2 h3)
      have l6 := hs l4 l5
      exact <L, l6>

def Gamma_univ_intro' {Gamma : Set (Form N)} {phi : Form N} (h1 : forall  psi : Gamma, is_free x psi.1 = false) : Gamma  |-  phi  ->  Gamma  |-  (all x, phi) := by
  intro Gamma_pf_phi
  match Gamma_pf_phi with
  | <L, l1> =>
      have l2 := general x l1
      have := notfreeset L h1
      have l3 := ax_q1 (conjunction Gamma L) phi this
      have l4 := mp l3 l2
      exists L

def dn_equiv_premise {phi : Form N} : Gamma  |-  (~~phi) iff Gamma  |-  phi := by
  have l1 := tautology (@dne N phi)
  have l2 := tautology (@dni N phi)
  rw [SyntacticConsequence, SyntacticConsequence]
  apply TypeIff.intro
  repeat (
    intro <L, _>;
    exists L;
    apply hs;
    repeat assumption
  )

section Nominals

def generalize_constants {phi : Form N} {x : SVAR} (i : NOM N) (h : x  >=  phi.new_var) :  |-  phi  ->   |-  (all x, phi[x // i]) := by
    intro pf
    apply general x
    induction pf generalizing x with
    | @tautology phi ht      =>
        apply tautology
        simp [Tautology] at ht  |- 
        intro e
        let f'  : Form N  ->  Bool := fun  phi => if (e.f <| phi[x//i]) then true else false
        let e'  : Eval N := <f', by simp [f', e.p1, nom_subst_svar], by simp [f', e.p2, nom_subst_svar]>
        have h2 := ht e'
        have e_eq : e'.f phi = (if (e.f <| phi[x//i]) then true else false) := rfl
        rw [e_eq] at h2
        simpa using h2
    | @general phi v _ ih   =>
        simp only [nom_subst_svar, Form.new_var, max] at h  |- 
        by_cases hc : (v + 1).letter > (Form.new_var phi).letter
        . simp [hc] at h
          simp only [gt_iff_lt] at hc
          have := ih (Nat.le_of_lt (Nat.lt_of_lt_of_le hc h))
          exact general v this
        . simp [hc] at h
          exact general v (ih h)
    | @necess   psi _ ih     =>
        simp only [nom_subst_svar, occurs] at h  |- 
        apply necess; apply ih; assumption
    | @mp phi psi _ _ ih1 ih2  =>
        simp only [occurs, Bool.or_eq_false_eq_eq_false_and_eq_false, not_and,
          Bool.not_eq_false] at ih1
        -- show psi[y // i] for some y that does not
        --    occur in either phi or psi
        -- generalize, get  all y, psi[y // i]
        -- then apply axiom Q2 and get:
        --                   (psi[y // i])[x // y]
        -- this should bring you to:
        --                   psi[x // i]
        let y := (phi  -->  psi).new_var
        have ih1_cond : y  >=  (phi --> psi).new_var := Nat.le.refl
        have <ih2_cond, sub_cond> := new_var_geq1 ih1_cond
        have ih1 := ih1 ih1_cond
        have ih2 := ih2 ih2_cond
        rw [nom_subst_svar] at ih1
        have l1  := general y (mp ih1 ih2)
        have l2  := ax_q2_svar (psi[y//i]) y x (new_var_subst h)
        have l3  := mp l2 l1
        rw [nom_subst_trans i x y sub_cond] at l3
        exact l3
    | @ax_k phi psi            =>
        simp only [nom_subst_svar]
        apply ax_k
    | @ax_q1 phi psi v h2       =>
        simp only [nom_subst_svar]
        apply ax_q1
        have := new_var_geq2 (new_var_geq1 h).left
        have ha : x  >=  phi.new_var := (new_var_geq1 this.right).left
        have hb : v  !=  x := diffsvar this.left
        have := (scz i ha hb).mpr
        rw [contraposition, Bool.not_eq_true, Bool.not_eq_true] at this
        apply this
        exact h2
    | @ax_q2_svar phi y v h2  =>
        have := new_var_geq2 (new_var_geq1 h).left
        have c2 : x  >=  phi.new_var := this.right
        have c3 : y  !=  x := diffsvar this.left
        have c  := new_var_subst' i h2 c2 c3
        have l1 := ax_q2_svar (phi[x//i]) y v c
        rw [nom_svar_subst_symm c3] at l1
        exact l1
    | @ax_q2_nom  phi v j    =>
        simp [nom_subst_svar]
        have f3 := diffsvar (new_var_geq2 (new_var_geq1 h).left).left
        by_cases ji : j = i
        . rw [ji] at h  |- 
          have f2 := (new_var_geq2 (new_var_geq1 h).left).right
          have f1 := @new_var_subst'' N phi x v f2
          have := new_var_subst' i f1 f2 f3
          have := ax_q2_svar (phi[x//i]) v x this
          rw [subst_collect_all]
          exact this
        . rw [ <- (nom_nom_subst_symm ji f3)]
          exact ax_q2_nom (phi[x//i]) v j
    | @ax_name    v        =>
        exact ax_name v
    | @ax_nom   phi v m n    =>
        simp only [nom_subst_svar, nec_subst_nom, pos_subst_nom]
        apply ax_nom
    | @ax_brcn  phi v        =>
        apply ax_brcn

  def generalize_constants_rev {phi : Form N} {x : SVAR} (i : NOM N) (h : x  >=  phi.new_var) :  |-  (all x, phi[x // i])  ->   |-  phi := by
    intro pf
    have l1 := ax_q2_nom (phi[x//i]) x i
    have l2 := mp l1 pf
    rw [svar_svar_nom_subst h, nom_subst_self] at l2
    exact l2

  def generalize_constants_iff {phi : Form N} {x : SVAR} (i : NOM N) (h : x  >=  phi.new_var) :  |-  phi iff  |-  (all x, phi[x // i]) := by
    apply TypeIff.intro
    . apply generalize_constants; assumption
    . apply generalize_constants_rev; assumption

  lemma formulasIn_cast {a b : Form N} (h : a = b) (pf : Proof a) :
      (h  |>  pf).formulasIn = pf.formulasIn := by subst h; rfl

  lemma proof_noms_cast {a b : Form N} (h : a = b) (pf : Proof a) :
      (h  |>  pf).proof_noms = pf.proof_noms := by subst h; rfl

  /-- Forward rename: substitute nominal `new` for `old` structurally on `Proof`
      (no `generalize_constants` + `ax_q2_nom` wrapper). -/
  def rename_constants_fwd {phi : Form N} (new old : NOM N) (pf : Proof phi) : Proof (phi[new // old]) :=
    match pf with
    | .general v pf' => general v (rename_constants_fwd new old pf')
    | .necess pf' => necess (rename_constants_fwd new old pf')
    | .mp pf1 pf2 => mp (rename_constants_fwd new old pf1) (rename_constants_fwd new old pf2)
    | .tautology ht => tautology (tautology_nom_subst ht new old)
    | .ax_k => ax_k
    | .ax_q1 phi' psi h =>
        ax_q1 (phi'[new // old]) (psi[new // old]) (by simpa [is_free_nom_subst_nom] using h)
    | .ax_q2_svar phi' v s p =>
        (by
          have eq : ((all v, phi')  -->  phi'[s // v])[new // old] =
              (all v, phi'[new // old])  -->  (phi'[new // old])[s // v] := by
            simp only [nom_subst_nom, nom_svar_subst_comm_nom]
          exact eq  |>  ax_q2_svar (phi'[new // old]) v s (by simpa [is_substable_nom_subst_nom] using p))
    | .ax_q2_nom phi' v s =>
        nom_subst_ax_q2_nom (phi := phi') (v := v) (s := s) (new := new) (old := old)  |> 
          ax_q2_nom (phi'[new // old]) v (if s = old then new else s)
    | .ax_name v => ax_name v
    | @ax_nom _ phi' v m n =>
        nom_subst_ax_nom (phi := phi') (v := v) (m := m) (n := n) (new := new) (old := old)  |> 
          ax_nom (phi := phi'[new // old]) (v := v) m n
    | .ax_brcn => ax_brcn


  lemma mem_formulasIn_self {phi : Form N} (pf : Proof phi) : phi  in  pf.formulasIn := by
    induction pf with
    | tautology _ | ax_k | ax_q1 _ _ _ | ax_q2_svar _ _ _ _ | ax_q2_nom _ _ _ | ax_name _ | ax_nom _ _ | ax_brcn =>
        simp [formulasIn]
    | general _ _ => simp [formulasIn]
    | necess _ => simp [formulasIn]
    | mp _ _ _ _ => simp [formulasIn]

  theorem formulasIn_rename_constants_fwd {phi : Form N} (new old : NOM N) (pf : Proof phi) :
      (rename_constants_fwd new old pf).formulasIn = pf.formulasIn.map (*[new // old]) := by
    induction pf with
    | general v pf ih => simp [rename_constants_fwd, Proof.formulasIn, ih]
    | necess pf ih => simp [rename_constants_fwd, Proof.formulasIn, ih]
    | @mp phi' psi' pf1 pf2 ih1 ih2 =>
        have htail :
            (rename_constants_fwd new old pf1).formulasIn ++
                (rename_constants_fwd new old pf2).formulasIn =
              List.map (fun x => x[new // old]) pf1.formulasIn ++
                List.map (fun x => x[new // old]) pf2.formulasIn := by
              rw [ih1, ih2]
        have h :=
            show (mp (rename_constants_fwd new old pf1) (rename_constants_fwd new old pf2)).formulasIn =
                (mp pf1 pf2).formulasIn.map (*[new // old]) from by
              simp only [Proof.formulasIn, List.map, List.map_append]
              exact congrArg (fun l => psi'[new // old] :: l) htail
        simpa [rename_constants_fwd] using h
    | tautology _ => simp [rename_constants_fwd, Proof.formulasIn]
    | ax_k => simp [rename_constants_fwd, Proof.formulasIn]
    | ax_q1 _ _ _ => simp [rename_constants_fwd, Proof.formulasIn, nom_subst_nom]
    | ax_q2_svar phi' v s p =>
        have eq : ((all v, phi')  -->  phi'[s // v])[new // old] =
            (all v, phi'[new // old])  -->  (phi'[new // old])[s // v] := by
          simp only [nom_subst_nom, nom_svar_subst_comm_nom]
        have hfi := formulasIn_cast eq.symm (ax_q2_svar (phi'[new // old]) v s (by simpa [is_substable_nom_subst_nom] using p))
        simp only [rename_constants_fwd, Proof.formulasIn, List.map, hfi, eq]
    | ax_q2_nom phi' v s =>
        have eq := nom_subst_ax_q2_nom (phi := phi') (v := v) (s := s) (new := new) (old := old)
        have hfi := formulasIn_cast eq.symm (ax_q2_nom (phi'[new // old]) v (if s = old then new else s))
        simp only [rename_constants_fwd, Proof.formulasIn, List.map, hfi, eq]
    | ax_name _ => simp [rename_constants_fwd, Proof.formulasIn]
    | @ax_nom phi' v m n =>
        have eq := nom_subst_ax_nom (phi := phi') (v := v) (m := m) (n := n) (new := new) (old := old)
        have hfi := formulasIn_cast eq.symm (ax_nom (phi := phi'[new // old]) (v := v) m n)
        simp only [rename_constants_fwd, Proof.formulasIn, List.map, hfi, eq]
    | ax_brcn => simp [rename_constants_fwd, Proof.formulasIn]

  lemma mem_proof_noms_rename_constants_fwd {phi : Form N} (new old : NOM N) (pf : Proof phi)
      {k : NOM N} (hk : k  in  (rename_constants_fwd new old pf).proof_noms) :
      k  in  pf.proof_noms  \/  k = new := by
    simp only [Proof.proof_noms, List.mem_dedup, List.mem_flatMap] at hk  |- 
    obtain <chi, hchi, hkchi> := hk
    rw [formulasIn_rename_constants_fwd] at hchi
    obtain <chi', hchi', hchieq> := List.mem_map.mp hchi
    subst hchieq
    rcases list_noms_subst hkchi with <hk', _> | hknew
    * exact Or.inl <chi', hchi', hk'>
    * exact Or.inr hknew

  lemma not_mem_proof_noms_rename_constants_fwd {phi : Form N} (new old : NOM N) (pf : Proof phi)
      (hne : new  !=  old) : old  notin  (rename_constants_fwd new old pf).proof_noms := by
    intro hk
    simp only [Proof.proof_noms, List.mem_dedup, List.mem_flatMap] at hk
    obtain <chi, hchi, hkchi> := hk
    rw [formulasIn_rename_constants_fwd] at hchi
    obtain <chi', _, hchieq> := List.mem_map.mp hchi
    subst hchieq
    cases list_noms_subst hkchi with
    | inl h => exact False.elim (h.2 rfl)
    | inr h => exact hne h.symm

  def rename_constants (j i : NOM N) (h : nom_occurs j phi = false) :  |-  phi iff  |-  (phi[j // i]) := by
    apply TypeIff.intro
    . exact rename_constants_fwd j i
    . intro pf
      let x := (phi[j//i]).new_var
      have x_geq : x  >=  (phi[j//i]).new_var := by simp; apply Nat.le_refl
      have l1 := generalize_constants j x_geq pf
      have : phi[j//i][x//j] = phi[x//i] := dbl_subst_nom i h
      rw [this] at l1
      have l2 := ax_q2_nom (phi[x // i]) x i
      have l3 := mp l2 l1
      rw [ <- eq_new_var] at x_geq
      have : phi[x//i][i//x] = phi[i//i] := svar_svar_nom_subst x_geq
      rw [nom_subst_self] at this
      rw [this] at l3
      exact l3

  def proof_sketch (h : nocc_bulk_property l_1 l_2 phi) :  |-  phi iff  |-  (phi.bulk_subst l_1 l_2) := by
    induction l_1 generalizing phi l_2 with
    | nil => cases l_2 <;> (simp [Form.bulk_subst]; apply TypeIff.refl)
    | cons h_new t_new ih =>
        cases l_2 with
        | nil => simp [Form.bulk_subst]; apply TypeIff.refl
        | cons h_old t_old =>
            simp [Form.bulk_subst]
            have : nom_occurs h_new phi = false := by
                apply @nocc_bulk TotalSet h_new [] []
                simp
                unfold nocc_bulk_property at h
                let n: Fin (List.length (h_new :: t_new)) := <0, by simp>
                have : h_new = (h_new :: t_new)[n] := by get_elem_tactic
                have := @h n h_new this
                simp [show ((n : Nat) = 0) from rfl] at this
                simp
                assumption
            have := rename_constants h_new h_old this
            apply this.trans
            apply ih
            apply nocc_bulk_property_induction
            assumption

  def pf_odd_noms :  |-  phi iff  |-  phi.odd_noms := by
    apply proof_sketch
    apply has_nocc_bulk_property

  def pf_odd_noms_set : Gamma  |-  phi iff Gamma.odd_noms  |-  phi.odd_noms := by
    simp [SyntacticConsequence]
    apply TypeIff.intro
    . intro <L, h>
      have h := (odd_conj Gamma L)  |>  odd_impl  |>  pf_odd_noms.mp h
      exists L.to_odd
    . intro <L', h'>
      have h' := pf_odd_noms.mpr (odd_impl.symm  |>  (odd_conj_rev Gamma L').symm  |>  h')
      exists L'.odd_to

  def odd_noms_set_cons (Gamma : Set (Form TotalSet)) : consistent Gamma  <->  consistent Gamma.odd_noms := by
    unfold consistent
    have : Form.bttm = Form.bttm.odd_noms := by simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst]
    conv => rhs; rw [this]
    apply Iff.intro <;> (
      intro h1 h2
      apply h1
      first | apply pf_odd_noms_set.mp | apply pf_odd_noms_set.mpr
      assumption
    )

end Nominals

def ax_nom_instance {phi : Form N} (i : NOM N) (m n : Nat) :  |-  (iterate_pos m (i  /\  phi)  -->  iterate_nec n (i  -->  phi)) := by
  let x := phi.new_var
  have x_geq : x  >=  phi.new_var := by exact Nat.le.refl
  have l1 := @ax_nom N (phi[x//i]) x m n
  have l2 := ax_q2_nom (iterate_pos m (x /\ (phi[x//i])) --> iterate_nec n (x --> (phi[x//i]))) x i
  have l3 := mp l2 l1
  clear l1 l2
  rw [subst_nom, pos_subst, nec_subst, nom_svar_rereplacement x_geq] at l3
  exact l3

def ax_q2_svar_instance :  |-  ((all x, phi)  -->  phi) := by
  have : phi.new_var  >=  phi.new_var := by exact Nat.le.refl
  apply hs
  apply mp
  . apply tautology
    apply iff_elim_l
  apply rename_bound
  apply new_var_is_new
  apply new_var_subst''
  assumption
  have <l, r> := (rereplacement phi x (phi.new_var) new_var_is_new (new_var_subst'' this))
  conv => rhs; rhs; rw [ <- r]
  apply ax_q2_svar
  assumption

def Gamma_univ_elim (h : Gamma  |-  (all x, phi)) : Gamma  |-  phi := by
  exact Gamma_mp (Gamma_theorem ax_q2_svar_instance Gamma) h

def rename_var (h1 : occurs y phi = false) (h2 : is_substable phi y x) :  |-  phi iff  |-  (phi[y // x]) := by
  apply TypeIff.intro
  . intro h
    apply mp
    apply ax_q2_svar_instance
    exact y
    apply mp
    . apply mp
      apply tautology
      apply iff_elim_l
      apply rename_bound
      repeat assumption
    . apply general
      assumption
  . intro h
    apply mp
    apply ax_q2_svar_instance
    exact x
    apply mp
    . apply mp
      apply tautology
      apply iff_elim_r
      apply rename_bound
      repeat assumption
    . apply general
      assumption

def ax_q2_contrap {i : NOM N} {x : SVAR} :  |-  (phi[i//x]  -->  ex x, phi) := by
  rw [Form.bind_dual]
  apply hs
  . apply tautology
    apply dni
  . apply mp
    apply tautology
    apply contrapositive
    apply ax_q2_nom

def ax_q2_svar_contrap {x y : SVAR} (h : is_substable phi y x) :  |-  (phi[y//x]  -->  ex x, phi) := by
  rw [Form.bind_dual]
  apply hs
  . apply tautology
    apply dni
  . apply mp
    apply tautology
    apply contrapositive
    apply ax_q2_svar
    simp [is_substable]
    exact h

def ax_nom_instance' (x : SVAR) (m n : Nat) :  |-  (iterate_pos m (x  /\  phi)  -->  iterate_nec n (x  -->  phi)) := by
  apply mp
  apply ax_q2_svar_instance
  assumption
  apply ax_nom

-- Lemma 3.6.1
def b361 {phi : Form N} :  |-  ((phi  -->  ex x, psi)  -->  ex x, (phi  -->  psi)) := by
  apply mp
  . apply tautology
    apply contrapositive'
  . apply Gamma_empty.mp; apply Deduction.mpr
    simp only [Set.empty_union]
    let Gamma : Set (Form N) := {~(ex x, phi --> psi)}
    have l1 : Gamma  |-  (~(ex x, phi --> psi)) := by apply Gamma_premise; simp [Gamma]
    rw [Form.bind_dual] at l1
    have l2 := Gamma_theorem (tautology (@dne N (all x, ~(phi --> psi)))) Gamma
    have l3 := Gamma_mp l2 l1
    have l4 := Gamma_theorem (@ax_q2_svar_instance x N (~(phi --> psi))) Gamma
    have l5 := Gamma_mp l4 l3
    have l6 := Gamma_theorem (tautology (taut_iff_mp (@imp_neg N phi psi))) Gamma
    have l7 := Gamma_mp l6 l5
    have l8 := Gamma_conj_elim_l l7
    have l9 := Gamma_conj_elim_r l7
    have l10 : Gamma  |-  (~(ex x, psi)) := by
      rw [Form.bind_dual]
      apply Gamma_mp; apply Gamma_theorem; apply tautology; apply dni
      apply Gamma_univ_intro'
      . simp [Gamma, is_free, -implication_disjunction]
      . exact l9
    have l11 := Gamma_conj_intro l8 l10
    have l12 := Gamma_mp (Gamma_theorem (tautology (taut_iff_mpr (@imp_neg N phi (ex x, psi)))) Gamma) l11
    exact l12

-- Lemma 3.6.2
def b362 {phi : Form N} (h : is_free x phi = false) :  |-  ((phi  /\  ex x, psi)  -->  ex x, (phi  /\  psi)) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply tautology
    apply contrapositive'
  . apply Gamma_empty.mp; apply Deduction.mpr
    simp only [Set.empty_union]
    let Gamma : Set (Form N) :=  {~~(all x, ~(phi /\ psi))}
    have l1 : Gamma  |-  (all x, ~(phi /\ psi)) := by
      apply Gamma_mp; apply Gamma_theorem; apply tautology; apply dne
      apply Gamma_premise; simp [Gamma]
    have l2 := Gamma_theorem (@ax_q2_svar_instance x N (~(phi /\ psi))) Gamma
    have l3 := Gamma_mp l2 l1
    have l4 := Gamma_mp (Gamma_theorem (tautology (taut_iff_mpr (@neg_conj N phi psi))) Gamma) l3
    have l5 : Gamma |-  (all x, (phi --> ~psi)) := by
      apply Gamma_univ_intro'
      simp [Gamma, is_free, -implication_disjunction]
      exact l4
    have l6 := Deduction.mp (Gamma_mp (Gamma_theorem (ax_q1 phi (~psi) h) Gamma) l5)
    have l7 := Deduction.mpr (Gamma_mp (Gamma_theorem (tautology (@dni N (all x, ~psi))) (Gamma  U  {phi})) l6)
    have l8 := Gamma_mp (Gamma_theorem (tautology (taut_iff_mp (@neg_conj N phi (~(all x, ~psi))))) Gamma) l7
    exact l8

def ex_conj_comm {phi : Form N} :  |-  ((ex x, (phi  /\  psi))  -->  (ex x, (psi  /\  phi))) := by
  rw [Form.bind_dual, Form.bind_dual]
  apply mp
  . apply tautology
    apply contrapositive'
  . apply Gamma_empty.mp; apply Deduction.mpr
    simp only [Set.empty_union]
    let Gamma : Set (Form N) := {~~(all x, ~(psi /\ phi))}
    have l1 : Gamma  |-  (~~(all x, ~(psi /\ phi))) := by apply Gamma_premise; simp [Gamma]
    have l2 := Gamma_theorem (tautology (@dne N (all x, ~(psi /\ phi)))) Gamma
    have l3 := Gamma_mp l2 l1
    have l4 := Gamma_theorem (@ax_q2_svar_instance x N (~(psi /\ phi))) Gamma
    have l5 := Gamma_mp l4 l3
    have l6 := Gamma_theorem (tautology (@conj_comm_t' N psi phi)) Gamma
    have l7 := Gamma_mp l6 l5
    have l8 : Gamma |- (all x, ~(phi /\ psi)) := by
      apply Gamma_univ_intro'
      simp [Gamma, is_free, -implication_disjunction]
      exact l7
    have l9 := Gamma_theorem (tautology (@dni N (all x, ~(phi /\ psi)))) Gamma
    have l10 := Gamma_mp l9 l8
    exact l10

def b362' {phi : Form N} (h : is_free x phi = false) :  |-  (((ex x, psi)  /\  phi)  -->  ex x, (psi  /\  phi)) := by
  have l1 := tautology (@conj_comm_t N (ex x, psi) phi)
  have l2 := @b362 N x psi phi h
  have l3 := hs l2 ex_conj_comm
  have l4 := hs l1 l3
  exact l4

-- Lemma 3.6.3
def b363  {phi : Form N} :  |-  ((all x, (phi  -->  psi))  -->  ((all x, phi)  -->  (all x, psi))) := by
  let Gamma : Set (Form N) := {}  U  {all x, phi --> psi}  U  {all x, phi}
  have l1 : Gamma  |-  (all x, (phi  -->  psi)) := by apply Gamma_premise; simp [Gamma]
  have l2 : Gamma |- (phi --> psi) := by
    apply Gamma_mp
    apply Gamma_theorem
    apply ax_q2_svar_instance
    exact x
    exact l1
  have l3 : Gamma |- (all x, phi) := by apply Gamma_premise; simp [Gamma]
  have l4 : Gamma |- phi := by
    apply Gamma_mp
    apply Gamma_theorem
    apply ax_q2_svar_instance
    exact x
    exact l3
  have l5 :  |- ((all x, phi --> psi) --> ((all x, phi)  -->  psi)) := by
    apply Gamma_empty.mp; apply Deduction.mpr; apply Deduction.mpr
    apply Gamma_mp
    repeat assumption
  have l6 := general x l5
  have : is_free x (all x, phi --> psi) = false := by simp [is_free]
  have l7 := @ax_q1 N (all x, phi --> psi) ((all x, phi) --> psi) x this
  have l8 := mp l7 l6
  have : is_free x (all x, phi) = false := by simp [is_free]
  have l9 := @ax_q1 N (all x, phi) psi x this
  have l10 := hs l8 l9
  exact l10

def dn_nec :  |-  ([]  phi  <->  []  ~~phi) := by
  rw [Form.iff]
  apply mp
  apply mp
  apply tautology
  apply conj_intro
  repeat (
    apply mp
    apply ax_k
    apply necess
    apply tautology
    first | apply dni | apply dne
  )

def dn_all :  |-  ((all x, phi)  <->  all x, ~~phi) := by
  rw [Form.iff]
  apply mp
  apply mp
  apply tautology
  apply conj_intro
  repeat (
    apply mp
    apply b363
    apply general
    apply tautology
    first | apply dni | apply dne
  )

def bind_dual :  |- ((all x, psi) <-> ~(ex x, ~psi)) := by
    rw [Form.bind_dual]
    apply mp; apply mp
    apply tautology
    apply iff_intro
    . apply hs
      . apply mp
        apply tautology
        apply iff_elim_l
        apply dn_all
      . apply tautology
        apply dni
    . apply hs
      . apply tautology
        apply dne
      . apply mp
        apply tautology
        apply iff_elim_r
        apply dn_all

def nec_dual :  |- (([]  psi) <-> ~(<>  ~psi)) := by
    rw [Form.diamond]
    apply mp; apply mp
    apply tautology
    apply iff_intro
    . apply hs
      . apply mp
        apply tautology
        apply iff_elim_l
        apply dn_nec
      . apply tautology
        apply dni
    . apply hs
      . apply tautology
        apply dne
      . apply mp
        apply tautology
        apply iff_elim_r
        apply dn_nec

/-- When `x` is not free in `psi`, `forall x.psi` and `psi` are provably equivalent (Henkin / Q1). -/
def all_iff_notfree {x : SVAR} {psi : Form N} (h : is_free x psi = false) :  |-  ((all x, psi)  <->  psi) := by
  apply mp; apply mp
  apply tautology
  apply iff_intro
  * exact @ax_q2_svar_instance x N psi
  * apply mp (ax_q1 (phi := psi) (psi := psi) (by simp [is_free, h]))
    apply general x
    apply tautology imp_refl

/-- From `~([] phi)` derive `<> ~phi` (contrapositive of `nec_dual` + double-negation). -/
def not_nec_to_diamond {phi : Form N} :  |-  ((~([] phi))  -->  (<> ~phi)) := by
  have h1 :  |-  (([] phi)  <->  ~(<>  ~phi)) := nec_dual
  have h2 :  |-  ((~([] phi))  <->  ~~(<>  ~phi)) :=
    mp (mp (tautology iff_elim_l) (tautology iff_not)) h1
  have h3 :  |-  ((~([] phi))  -->  ~~(<>  ~phi)) := mp (tautology iff_elim_l) h2
  exact hs h3 (tautology (@dne N (<>  ~phi)))

def diw_impl (h :  |- (phi  -->  psi)) :  |-  (<> phi  -->  <> psi) := by
  have l1 := mp (tautology contrapositive) h
  have l2 := necess l1
  have l3 := mp ax_k l2
  have l4 := mp (tautology contrapositive) l3
  exact l4

def ax_brcn_contrap {phi : Form N} :  |-  ((<>  ex x, phi)  -->  (ex x, <>  phi)) := by
  simp only [Form.diamond, Form.bind_dual]
  apply mp
  . apply tautology
    apply contrapositive
  . apply Gamma_empty.mp; apply Deduction.mpr
    simp only [Set.empty_union]
    let Gamma : Set (Form N) := {all x, ~~([] ~phi)}
    have l1 : Gamma  |-  (all x, ~~([] ~phi)) := by apply Gamma_premise; simp [Gamma]
    have l2 := Gamma_theorem (mp (tautology iff_elim_r) (@dn_all x N ([] ~phi))) Gamma
    have l3 := Gamma_mp l2 l1
    have l4 := Gamma_theorem (@ax_brcn N (~phi) x) Gamma
    have l5 := Gamma_mp l4 l3
    have l6 := Gamma_theorem (mp (tautology iff_elim_l) (@dn_nec N (all x, ~phi))) Gamma
    have l7 := Gamma_mp l6 l5
    exact l7

section MCS

def MCS_pf (h : MCS Gamma) : Gamma  |-  phi  ->  phi  in  Gamma := by
  intro pf
  rw [ <- (@not_not (phi  in  Gamma))]
  intro habs
  have <cons, pf_bot> := h
  have <pf_bot, _> := not_forall.mp (pf_bot habs)
  clear h
  apply cons
  apply Gamma_mp
  apply Deduction.mpr
  assumption
  assumption

def MCS_thm (h : MCS Gamma) :  |-  phi  ->  phi  in  Gamma := by
  intro
  apply MCS_pf h
  apply Gamma_theorem
  assumption

def MCS_mp (h : MCS Gamma) (h1 : phi  -->  psi  in  Gamma) (h2 : phi  in  Gamma) : psi  in  Gamma := by
  rw [ <- @not_not (psi  in  Gamma)]
  intro habs
  have <pf_bot, _> := not_forall.mp (h.right habs)
  apply h.left
  apply Gamma_mp
  apply Deduction.mpr
  assumption
  apply Gamma_mp
  repeat (apply Gamma_premise; assumption)

def MCS_conj {Gamma : Set (Form N)} (hmcs : MCS Gamma) (phi psi : Form N) : (phi  in  Gamma  /\  psi  in  Gamma)  <->  (phi  /\  psi)  in  Gamma := by
  apply Iff.intro
  . intro <l, r>
    apply MCS_pf hmcs
    exact Gamma_conj_intro (Gamma_premise l) (Gamma_premise r)
  . intro h
    apply And.intro <;> apply MCS_pf hmcs
    exact Gamma_conj_elim_l (Gamma_premise h)
    exact Gamma_conj_elim_r (Gamma_premise h)

def MCS_max {Gamma : Set (Form N)} (hmcs : MCS Gamma) : (phi  notin  Gamma  <->  (~phi)  in  Gamma) := by
  apply Iff.intro
  . intro h
    have <pf_bot, _> := not_forall.mp (hmcs.2 h)
    apply MCS_pf hmcs; apply Deduction.mpr
    exact pf_bot
  . intro h habs
    apply hmcs.1
    apply Gamma_mp (Gamma_premise h) (Gamma_premise habs)

def MCS_impl {Gamma : Set (Form N)} (hmcs : MCS Gamma) : (phi  in  Gamma  ->  psi  in  Gamma)  <->  ((phi --> psi)  in  Gamma) := by
  apply Iff.intro
  . intro h
    by_cases hc : phi  in  Gamma
    . apply MCS_pf hmcs
      apply Deduction.mpr
      apply increasing_consequence
      exact Gamma_premise (h hc)
      simp
    . simp only [MCS_max, hmcs, Form.neg] at hc
      apply MCS_pf hmcs; apply Deduction.mpr
      apply Gamma_mp
      apply @Gamma_theorem N (False  -->  psi)
      apply tautology
      eval
      exact Deduction.mp (Gamma_premise hc)
  . intro h1 h2
    apply MCS_pf hmcs
    exact Gamma_mp (Gamma_premise h1) (Gamma_premise h2)

def MCS_iff {Gamma : Set (Form N)} (hmcs : MCS Gamma) : ((phi <-> psi)  in  Gamma)  <->  (phi  in  Gamma  <->  psi  in  Gamma) := by
  simp only [Form.iff,  <- MCS_conj,  <- MCS_impl, hmcs]
  apply Iff.intro
  <;> intros; apply Iff.intro
  . apply And.left
    assumption
  . apply And.right
    assumption
  apply And.intro <;> simp [*]

def MCS_rw {Gamma : Set (Form N)} (hmcs : MCS Gamma) (pf :  |-  (phi  <->  psi)) : phi  in  Gamma  <->  psi  in  Gamma := by
  rw [ <- MCS_iff hmcs]
  apply MCS_pf hmcs
  exact Gamma_theorem pf Gamma

def MCS_rich : forall  {Theta : Set (Form N)}, (MCS Theta)  ->  (witnessed Theta)  ->  exists  i : NOM N, i  in  Theta := by
  intro Theta mcs wit
  have := Proof.MCS_thm mcs (Proof.ax_name <0>)
  have := wit this
  simp [subst_nom] at this
  exact this

def MCS_with_svar_witness : forall  {Theta : Set (Form N)} {x y : SVAR} (_ : is_substable phi y x), (MCS Theta)  ->  phi[y//x]  in  Theta  ->  (ex x, phi)  in  Theta := by
  intro Theta x y h1 mcs h2
  apply MCS_mp mcs
  apply MCS_thm mcs
  apply ax_q2_svar_contrap h1
  repeat assumption

end MCS

def iff_subst :  |-  ((phi  <->  psi)  -->  (psi  <->  chi)  -->  (phi  <->  chi)) := by
  exact tautology iff_rw

def pf_iff_subst :  |-  (phi  <->  psi)  ->   |-  (psi  <->  chi)  ->   |-  (phi  <->  chi) := by
  intro h1 h2
  apply mp
  apply mp
  apply iff_subst
  exact psi
  repeat assumption

end
