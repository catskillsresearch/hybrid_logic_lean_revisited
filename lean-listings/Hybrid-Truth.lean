import Hybrid.Form
import Hybrid.Util
import Hybrid.Substitutions

section Definitions

  structure Model (N : Set Nat) where
    W : Type
    R : W  ->  W  ->  Prop
    V_p: PROP  ->  Set W
    V_n: NOM N   ->  W

  -- interpretation function
  -- from any state variable, to exactly ONE world
  def I (W : Type) := SVAR  ->  W

  -- let's define what it means to have a path between two elements
  -- under a relation R
  -- we will need this in proofs
  def path {a : Type} (R : a  ->  a  ->  Prop) (a b : a) (n : Nat) : Prop :=
    match n with
    | Nat.zero   => a = b
    | Nat.succ m => exists  i : a, (R i b)  /\  (path R a i m)

  @[simp]
  def is_variant (g_1 g_2 : I W) (x : SVAR) := forall  y : SVAR, ((x  !=  y)  ->  (g_1 y = g_2 y))

  @[simp]
  def Sat (M : Model N) (s : M.W) (g : I M.W) : (phi : Form N)  ->  Prop
    | Form.bttm     => False
    | Form.prop p   => s  in  (M.V_p p)
    | Form.nom  i   => s = (M.V_n i)
    | Form.svar x   => s = (g x)
    | Form.impl psi chi => (Sat M s g psi)  ->  (Sat M s g chi)
    | Form.box  psi   => forall  s' : M.W, (M.R s s'  ->  (Sat M s' g psi))
    | Form.bind x psi => forall  g' : I M.W, ((is_variant g' g x)  ->  Sat M s g' psi)

  notation "(" M "," s "," g ")" " |= " phi => Sat M s g phi
  notation "(" M "," s "," g ")" " |/= " phi => not  Sat M s g phi

  theorem neg_sat : ((M,s,g)  |=  ~phi)  <->  ((M,s,g)  |/=  phi) := by
    simp only [Form.neg, Sat]
  theorem and_sat : ((M,s,g)  |=  phi  /\  psi)  <->  (((M,s,g)  |=  phi)  /\  (M,s,g)  |=  psi) := by
    simp
  theorem or_sat  : ((M,s,g)  |=  phi  \/  psi)  <->  (((M,s,g)  |=  phi)  \/  (M,s,g)  |=  psi) := by
    simp
  theorem pos_sat : (((M,s,g)  |=  <> phi)  <->  (exists  s' : M.W, (M.R s s'  /\  (M,s',g)  |=  phi))) := by
    simp
  theorem ex_sat  : ((M,s,g)  |=  ex x, phi)  <->  (exists  g' : I M.W, (is_variant g' g x)  /\  ((M,s,g')  |=  phi)) := by
    simp [-is_variant]
  theorem iff_sat : ((M,s,g)  |=  (phi  <->  psi))  <->  (((M,s,g)  |=  phi)  <->  (M,s,g)  |=  psi) := by
    rw [Form.iff, and_sat, Sat, Sat]
    apply Iff.intro
    . intro <h1, h2>
      apply Iff.intro <;> assumption
    . intro h1
      apply And.intro <;> simp [h1]

  @[simp]
  def Valid (phi : Form N) := forall  (M : Model N) (s : M.W) (g : I M.W), ((M, s, g)  |=  phi)

  prefix:1000 " |= " => Valid
  prefix:1000 " |/= " => not  Valid

  @[simp]
  def Sat_Set (M : Model N) (s : M.W) (g : I M.W) (Gamma : Set (Form N)) := forall  (phi : Form N), (phi  in  Gamma)  ->  ((M, s, g)  |=  phi)

  notation "(" M "," s "," g ")" " |= " Gamma => Sat_Set M s g Gamma
  notation "(" M "," s "," g ")" " |/= " Gamma => not  Sat_Set M s g Gamma

  --def Entails (Gamma : set Form) (phi : Form) := forall  M : Model, (M  |=  Gamma)  ->  (M  |=  phi)
  @[simp]
  def Entails (Gamma : Set (Form N)) (phi : Form N) := forall  (M : Model N) (s : M.W) (g : I M.W), ((M,s,g)  |=  Gamma)  ->  ((M,s,g)  |=  phi)


  infix:1000 " |= " => Entails
  notation Gamma " |/= " phi => not  (Entails Gamma phi)

  @[simp]
  def satisfiable (Gamma : Set (Form N)) := exists  (M : Model N) (s : M.W) (g : I M.W), (M,s,g)  |=  Gamma

end Definitions

section Theorems

  section Variants
    @[simp]
    theorem is_variant_refl {g : I W} (x : SVAR) : is_variant g g x := by simp

    @[simp]
    theorem is_variant_symm {g_1 : I W} {g_2 : I W} {x : SVAR} : is_variant g_1 g_2 x  <->  is_variant g_2 g_1 x := by
      -- bit annoying that it simplified the implication
      -- maybe prove again using simp [-implication_disjunction]
      simp
      apply Iff.intro
      . intro h1 hy
        apply Or.elim (h1 hy)
        . intro x_eq_y
          exact Or.inl x_eq_y
        . intro g1_eq_g2
          exact Or.inr (Eq.symm g1_eq_g2)
      . intro h2 hy
        apply Or.elim (h2 hy)
        . intro x_eq_y
          exact Or.inl x_eq_y
        . intro g2_eq_g1
          exact Or.inr (Eq.symm g2_eq_g1)

    theorem is_variant_trans {g_1 g_2 g_3 : I W} {x : SVAR} : is_variant g_1 g_2 x  ->  is_variant g_2 g_3 x  ->  is_variant g_1 g_3 x := by
      rw [is_variant, is_variant, is_variant]
      intros a b y x_not_y
      have g1_is_g2 := a y x_not_y
      have g2_is_g3 := b y x_not_y
      exact Eq.trans g1_is_g2 g2_is_g3

    theorem two_step_variant {g_1 g_2 g_3 : I W} {x y : SVAR} (g_1_2x : is_variant g_1 g_2 x) (g_2_3y : is_variant g_2 g_3 y) : forall  v : SVAR, (v  !=  x  /\  v  !=  y)  ->  g_1 v = g_3 v := by
      intro v <v_not_x, v_not_y>
      have one_eq_two   := g_1_2x v (Ne.symm v_not_x)
      have two_eq_three := g_2_3y v (Ne.symm v_not_y)
      exact Eq.trans one_eq_two two_eq_three

    theorem two_step_variant_rev (g_1 g_3 : I W) {x y : SVAR} (two_step : forall  v : SVAR, (v  !=  x  /\  v  !=  y)  ->  g_1 v = g_3 v) : exists  g_2 : I W, (is_variant g_1 g_2 x  /\  is_variant g_2 g_3 y) := by
      let g_2 : I W := (fun  v : SVAR => if (v = x) then (g_3 v) else if (v = y) then (g_1 v) else (g_3 v))
      exists g_2
      apply And.intro
      . rw [is_variant]
        intro v v_x
        have v_x := Ne.symm v_x
        show g_1 v = (if v = x then g_3 v else if v = y then g_1 v else g_3 v)
        rw [if_neg v_x]
        by_cases v_y : v = y
        . rw [if_pos v_y]
        . rw [if_neg v_y]
          exact two_step v (And.intro v_x v_y)
      . rw [is_variant]
        intro v v_y
        have v_y := Ne.symm v_y
        show (if v = x then g_3 v else if v = y then g_1 v else g_3 v) = g_3 v
        by_cases v_x : v = x
        . rw [if_pos v_x]
        . rw [if_neg v_x, if_neg v_y]

    theorem variant_mirror_property (g_1 g_2 g_3 : I W) {x y : SVAR} (g_1_2x : is_variant g_1 g_2 x) (g_2_3y : is_variant g_2 g_3 y) :
      exists  g_2_mirror : I W, (is_variant g_1 g_2_mirror y  /\  is_variant g_2_mirror g_3 x) := by
      have two_step := two_step_variant g_1_2x g_2_3y
      conv at two_step =>
        intro v
        conv => lhs ; rw [conj_comm]
      exact two_step_variant_rev g_1 g_3 two_step

  end Variants

  section Satisfaction

    theorem bind_comm {M : Model N} {s : M.W} {g : I M.W} {phi : Form N} {x y : SVAR} : ((M,s,g)  |=  all x, (all y, phi))  <->  ((M,s,g)  |=  all y, (all x, phi)) := by
      apply Iff.intro
      . intro h1
        intros h var_h_g i var_i_h
        have two_step : forall  (v : SVAR), v  !=  x  /\  v  !=  y  ->  g v = i v := (fun  a => fun  b => Eq.symm ((two_step_variant var_i_h var_h_g) a b))
        have exist_mid_g := two_step_variant_rev g i two_step
        match exist_mid_g with
        | <mid_g, mid_g_var_g, mid_g_var_i> =>
          have mid_g_sat := h1 mid_g (is_variant_symm.mp mid_g_var_g)
          exact mid_g_sat i (is_variant_symm.mp mid_g_var_i)
      . intro h2
        intros h var_h_g i var_i_h
        have two_step : forall  (v : SVAR), v  !=  y  /\  v  !=  x  ->  g v = i v := (fun  a => fun  b => Eq.symm ((two_step_variant var_i_h var_h_g) a b))
        have exist_mid_g := two_step_variant_rev g i two_step
        match exist_mid_g with
        | <mid_g, mid_g_var_g, mid_g_var_i> =>
          have mid_g_sat := h2 mid_g (is_variant_symm.mp mid_g_var_g)
          exact mid_g_sat i (is_variant_symm.mp mid_g_var_i)

    theorem SatConjunction (Gamma : Set (Form N)) (L : List Gamma) : Gamma  |=  conjunction Gamma L := by
      intro M s g M_sat_Gamma
      induction L with
      | nil =>
          simp [conjunction, Sat]
      | cons h t ih =>
          simp only [conjunction, and_sat, ih, and_true]
          exact M_sat_Gamma h h.prop

    theorem SetEntailment (Gamma : Set (Form N)) : (exists  L,  |=  (conjunction Gamma L  -->  psi))  ->  Gamma  |=  psi := by
      intro h
      intro M s g M_sat_Gamma
      match h with
      | <L, hw> =>
          have l1 := hw M s g
          have l2 := SatConjunction Gamma L M s g M_sat_Gamma
          rw [Sat] at l1
          exact l1 l2

    end Satisfaction

  theorem D_help {Gamma : Set (Form N)} : ((M,s,g) |= Gamma  U  {phi})  <->  (((M,s,g) |= Gamma)  /\  (M,s,g)  |=  {phi}) := by
    apply Iff.intro
    . intro h
      rw [Sat_Set] at h
      apply And.intro
      . intro chi mem; apply h; simp [mem]
      . intro chi mem; apply h; simp at mem; simp [mem]
    . intro <hl, hr>
      intro chi mem; simp at mem
      apply Or.elim mem <;> {
        intros; first | {apply hl; assumption} | {apply hr; assumption}
      }

  theorem SemanticDeduction {Gamma : Set (Form N)} : (Gamma  |=  (phi  -->  psi))  <->  ((Gamma  U  {phi})  |=  psi) := by
    apply Iff.intro <;> {
      intro h M s g sat_set
      try (intro sat_phi;
            have sat_phi : (M,s,g)  |=  {phi} := by simp only [Sat_Set, Set.mem_singleton_iff, forall_eq,
              sat_phi])
      try (have := h M s g (D_help.mpr <sat_set, sat_phi>))
      try (have <sat_l, sat_r> := D_help.mp sat_set;
            simp only [Sat_Set, Set.mem_singleton_iff, forall_eq] at sat_r ;
            have := (h M s g sat_l) sat_r)
      assumption
    }

end Theorems

def Model.odd_noms (M : Model TotalSet) : Model TotalSet where
  W := M.W
  R := M.R
  V_p:= M.V_p
  V_n:= fun  i => M.V_n ((i-1)/2)

def Model.odd_noms_inv (M : Model TotalSet) : Model TotalSet where
  W := M.W
  R := M.R
  V_p:= M.V_p
  V_n:= fun  i => M.V_n (i*2+1)

theorem sat_odd_noms {phi : Form TotalSet} : ((M,s,g)  |=  phi)  <->  ((M.odd_noms,s,g)  |=  phi.odd_noms) := by
  induction phi generalizing s g with
  | nom i =>
      have h : ((2 * i + 1 - 1) / 2 : NOM TotalSet) = i := by
        rw [NOM_eq, Subtype.ext_iff]
        show ((i.letter : Nat) * 2 + 1 - 1) / 2 = (i.letter : Nat)
        omega
      simp [odd_nom, Model.odd_noms, h]
  | impl phi psi ih1 ih2 =>
      rw [odd_impl, Sat, Sat, ih1, ih2]
  | box phi ih =>
      rw [odd_box, Sat, Sat]
      apply Iff.intro
      . intro h1 s' h2
        rw [ <- @ih s' g]
        exact h1 s' h2
      . intro h1 s' h2
        rw [@ih s' g]
        exact h1 s' h2
  | bind x phi ih =>
      rw [odd_bind, Sat, Sat]
      apply Iff.intro
      . intro h1 g' h2
        rw [ <- @ih s g']
        exact h1 g' h2
      . intro h1 g' h2
        rw [@ih s g']
        exact h1 g' h2
  | _ => simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst, Model.odd_noms]

theorem sat_odd_noms' {phi : Form TotalSet} : ((M,s,g)  |=  phi.odd_noms)  <->  ((M.odd_noms_inv,s,g)  |=  phi) := by
--  conv => rhs; rw [sat_odd_noms]
  induction phi generalizing s g with
  | nom i =>
      have h : (2 * i + 1 : NOM TotalSet) = i * 2 + 1 := by
        rw [NOM_eq, Subtype.ext_iff]; rfl
      simp [odd_nom, Model.odd_noms, Model.odd_noms_inv, h]
  | impl phi psi ih1 ih2 =>
      rw [odd_impl, Sat, Sat, ih1, ih2]
  | box phi ih =>
      rw [odd_box, Sat, Sat]
      apply Iff.intro
      . intro h1 s' h2
        rw [ <- @ih s' g]
        exact h1 s' h2
      . intro h1 s' h2
        rw [@ih s' g]
        exact h1 s' h2
  | bind x phi ih =>
      rw [odd_bind, Sat, Sat]
      apply Iff.intro
      . intro h1 g' h2
        rw [ <- @ih s g']
        exact h1 g' h2
      . intro h1 g' h2
        rw [@ih s g']
        exact h1 g' h2
  | _ => simp [Form.odd_noms, Form.list_noms, Form.odd_list_noms, Form.bulk_subst, Model.odd_noms, Model.odd_noms_inv] <;> rfl

/-
theorem testtt {Gamma : Set Form} : ((M,s,g)  |=  Gamma)  <->  ((M.odd_noms,s,g)  |=  Gamma.odd_noms) := by
  apply Iff.intro
  . intro h phi_odd phi_odd_prop
    have <phi, mem, is_odd> := phi_odd_prop
    rw [ <- is_odd,  <- sat_odd_noms]
    exact h phi mem
  . intro h phi mem
    rw [sat_odd_noms]
    have phi_odd_mem : phi.odd_noms  in  Gamma.odd_noms := by exists phi
    exact h phi.odd_noms phi_odd_mem

theorem testtt' {Gamma : Set Form} : ((M,s,g)  |=  Gamma.odd_noms)  <->  ((M.odd_noms_inv,s,g)  |=  Gamma) := by
  apply Iff.intro
  . intro h phi mem
    rw [ <- sat_odd_noms']
    have phi_odd_mem : phi.odd_noms  in  Gamma.odd_noms := by exists phi
    exact h phi.odd_noms phi_odd_mem
  . intro h phi_odd phi_odd_prop
    have <phi, mem, is_odd> := phi_odd_prop
    rw [ <- is_odd, sat_odd_noms']
    exact h phi mem

theorem plang : Gamma  |=  phi  <->  Gamma.odd_noms  |=  phi.odd_noms := by
  apply Iff.intro
  . intro h M s g sat_odd_set
    rw [testtt'] at sat_odd_set
    have := h M.odd_noms_inv s g sat_odd_set
    rw [sat_odd_noms']
    exact this
  . intro h M s g sat_set
    rw [testtt] at sat_set
    have := h M.odd_noms s g sat_set
    rw [sat_odd_noms]
    exact this

#print axioms plang
-/
