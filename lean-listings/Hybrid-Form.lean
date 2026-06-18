import Mathlib.Data.Set.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Chain
import Mathlib.Data.Fin.Basic
import Hybrid.Util

open Classical

section Basics
  def TotalSet := {n : Nat | True}

  structure PROP where
    letter : Nat
  deriving DecidableEq, Repr

  structure SVAR where
    letter : Nat
  deriving DecidableEq, Repr

  structure NOM (N : Set Nat) where
    letter : N
  deriving DecidableEq, Repr

  instance : Max PROP where
    max := fun  p => fun  q => ite (p.letter > q.letter) p q
  instance svarmax : Max SVAR where
    max := fun  x => fun  y => ite (x.letter > y.letter) x y
  instance : Max (NOM S) where
    max := fun  i => fun  j => ite (i.letter > j.letter) i j

  theorem NOM_eq {i j : NOM S} : (i = j)  <->  (i.letter = j.letter) := by
    cases i
    cases j
    simp
  theorem NOM_eq' {i j : NOM S} : (i = j)  <->  (j.letter = i.letter) := by
    cases i
    cases j
    simp
    apply Iff.intro <;> {intro; simp [*]}

--  instance ofNatSVAR : OfNat SVAR n    where
--    ofNat := SVAR.mk n
  instance : OfNat (NOM TotalSet) n     where
    ofNat := NOM.mk  <n, trivial>
  instance : Coe SVAR Nat  := <SVAR.letter>
--  instance : Coe NOM Nat   := <NOM.letter>
  instance : Coe Nat SVAR  := <SVAR.mk>
--  instance : Coe Nat NOM   := <NOM.mk>
  instance SVAR.le : LE SVAR         where
    le    := fun  x => fun  y =>  x.letter  <=  y.letter
  instance SVAR.lt : LT SVAR         where
    lt    := fun  x => fun  y =>  x.letter < y.letter
  instance NOM.le : LE (NOM S)       where
    le    := fun  x => fun  y =>  x.letter  <=  y.letter
  instance NOM.lt : LT (NOM S)         where
    lt    := fun  x => fun  y =>  x.letter < y.letter
  instance SVAR.add : HAdd SVAR Nat SVAR where
    hAdd  := fun  x => fun  n => (x.letter + n)
  @[simp] instance NOM.add : HAdd (NOM TotalSet) Nat (NOM TotalSet) where
    hAdd  := fun  x => fun  n => <(x.letter + n), trivial>
  @[simp] instance : HSub (NOM TotalSet) Nat (NOM TotalSet) where
    hSub  := fun  x => fun  n => <(x.letter - n), trivial>
  @[simp] instance : HMul (NOM TotalSet) Nat (NOM TotalSet) where
    hMul  := fun  x => fun  n => <(x.letter * n), trivial>
  @[simp] instance : HDiv (NOM TotalSet) Nat (NOM TotalSet) where
    hDiv  := fun  x => fun  n => <(x.letter / n), trivial>
  @[simp] instance NOM.hmul : HMul Nat (NOM TotalSet) (NOM TotalSet) where
    hMul  := fun  n => fun  x => <(x.letter * n), trivial>
  @[simp] instance : HMul (NOM TotalSet) Nat Nat where
    hMul  := fun  x => fun  n => x.letter * n

  instance : IsTrans (NOM S) GT.gt where
    trans := fun  _ _ _ h1 h2 => Nat.lt_trans h2 h1

  instance : IsTotal (NOM S) GE.ge where
    total := fun a b => Nat.le_total b.letter a.letter

  instance : IsTrans (NOM S) GE.ge where
    trans := fun  _ _ _ h1 h2 => Nat.le_trans h2 h1

  theorem NOM.gt_iff_ge_and_ne {a b : (NOM S)} : a > b  <->  (a  >=  b  /\  a  !=  b) := by
    simp only [GT.gt, GE.ge, NOM.lt, NOM.le, LE.le, LT.lt, NOM.mk, ne_eq, NOM_eq']
    apply Iff.intro
    . intro h
      apply And.intro
      . exact (Nat.lt_iff_le_and_ne.mp h).1
      . have := (Nat.lt_iff_le_and_ne.mp h).2
        intro habs
        simp [habs] at this
    . rw [ <- ne_eq]
      intro <h1, h2>
      apply Nat.lt_iff_le_and_ne.mpr
      apply And.intro
      . exact h1
      . intro habs
        apply h2
        apply Subtype.eq
        assumption

  inductive Form (N : Set Nat) where
    -- atomic formulas:
    | bttm : Form N
    | prop : PROP    ->  Form N
    | svar : SVAR    ->  Form N
    | nom  :  NOM N  ->  Form N
    -- connectives:
    | impl : Form N  ->  Form N  ->  Form N
    -- modal:
    | box  : Form N  ->  Form N
    -- hybrid:
    | bind :   SVAR  ->  Form N  ->  Form N
  deriving DecidableEq, Repr

  def Form.depth : Form N  ->  Nat
    | .impl phi psi =>  1 + Form.depth phi + Form.depth psi
    | .box  phi   =>  1 + Form.depth phi
    | .bind _ phi =>  2 + Form.depth phi
    | _       =>    0

  theorem sub_depth_impl_l (phi psi : Form N) : phi.depth < (Form.impl phi psi).depth := by
    simp [Form.depth]; omega

  theorem sub_depth_impl_r (phi psi : Form N) : psi.depth < (Form.impl phi psi).depth := by
    simp [Form.depth]; omega

  theorem sub_depth_box (phi : Form N) : phi.depth < (Form.box phi).depth := by
    simp [Form.depth]

  theorem sub_depth_bind (x : SVAR) (phi : Form N) : phi.depth < (Form.bind x phi).depth := by
    simp [Form.depth]

  instance : Nonempty (Form N) := <Form.bttm>

  @[simp]
  def Form.neg      : Form N  ->  Form N := fun  phi => Form.impl phi Form.bttm
  @[simp]
  def Form.conj     : Form N  ->  Form N  ->  Form N := fun  phi => fun  psi => Form.neg (Form.impl phi (Form.neg psi))
  @[simp]
  def Form.iff      : Form N  ->  Form N  ->  Form N := fun  phi => fun  psi => Form.conj (Form.impl phi psi) (Form.impl psi phi)
  @[simp]
  def Form.disj     : Form N  ->  Form N  ->  Form N := fun  phi => fun  psi => Form.impl (Form.neg phi) psi
  @[simp]
  def Form.diamond  : Form N  ->  Form N := fun  phi => Form.neg (Form.box (Form.neg phi))
  @[simp,match_pattern]
  def Form.bind_dual: SVAR  ->  Form N  ->  Form N := fun  x => fun  phi => Form.neg (Form.bind x (Form.neg phi))

  instance : Coe PROP     (Form N)  := <Form.prop>
  instance : Coe SVAR     (Form N)  := <Form.svar>
  instance : Coe (NOM N)  (Form N)  := <Form.nom>

  infixr:60 " --> " => Form.impl
  infixl:65 " /\ " => Form.conj
  infixl:65 " \/ " => Form.disj
  prefix:100 "[] " => Form.box
  prefix:100 "<>  " => Form.diamond
  notation:120 "all " x ", " phi => Form.bind x phi
  notation:120 "ex " x ", " phi => Form.bind_dual x phi
  prefix:170 "~" => Form.neg
  infixr:60 " <-> " => Form.iff
  notation "False"  => Form.bttm

  def conjunction (Gamma : Set (Form N)) (L : List Gamma) : Form N :=
  match L with
    | []     => False  -->  False
    | h :: t => h.val  /\  conjunction Gamma t

  def Form.new_var  : Form N  ->  SVAR
  | .svar x   => x+1
  | .impl psi chi => max (psi.new_var) (chi.new_var)
  | .box  psi   => psi.new_var
  | .bind x psi => max (x+1) (psi.new_var)
  | _         => <0>


  def Form.new_nom  : Form TotalSet  ->  NOM TotalSet
  | .nom  i   => i+1
  | .impl psi chi => max (psi.new_nom) (chi.new_nom)
  | .box  psi   => psi.new_nom
  | .bind _ psi => psi.new_nom
  | _         => <0, trivial>

end Basics

section Substitutions
  def occurs (x : SVAR) (phi : Form N) : Bool :=
    match phi with
    | Form.bttm     => false
    | Form.prop _   => false
    | Form.svar y   => x = y
    | Form.nom  _   => false
    | Form.impl phi psi => (occurs x phi) || (occurs x psi)
    | Form.box  phi   => occurs x phi
    | Form.bind _ phi => occurs x phi

  def is_free (x : SVAR) (phi : Form N) : Bool :=
    match phi with
    | Form.bttm     => false
    | Form.prop _   => false
    | Form.svar y   => x == y
    | Form.nom  _   => false
    | Form.impl phi psi => (is_free x phi) || (is_free x psi)
    | Form.box  phi   => is_free x phi
    | Form.bind y phi => (y != x) && (is_free x phi)

  def is_bound (x : SVAR) (phi : Form N) := (occurs x phi) && !(is_free x phi)

  -- conventions for substitutions can get confusing
  -- "phi[s // x], the formula obtained by substituting s for all *free* occurrences of x in phi"
  -- for reference: Blackburn 1998, pg. 628
  def subst_svar (phi : Form N) (s : SVAR) (x : SVAR) : Form N :=
    match phi with
    | Form.bttm     => phi
    | Form.prop _   => phi
    | Form.svar y   => ite (x = y) s y
    | Form.nom  _   => phi
    | Form.impl phi psi => (subst_svar phi s x)  -->  (subst_svar psi s x)
    | Form.box  phi   => []  (subst_svar phi s x)
    | Form.bind y phi => ite (x = y) (Form.bind y phi) (Form.bind y (subst_svar phi s x))

  def subst_nom (phi : Form N) (s : NOM N) (x : SVAR) : Form N :=
    match phi with
    | Form.bttm     => phi
    | Form.prop _   => phi
    | Form.svar y   => ite (x = y) s y
    | Form.nom  _   => phi
    | Form.impl phi psi => (subst_nom phi s x)  -->  (subst_nom psi s x)
    | Form.box  phi   => []  (subst_nom phi s x)
    | Form.bind y phi => ite (x = y) (Form.bind y phi) (Form.bind y (subst_nom phi s x))

  def is_substable (phi : Form N) (y : SVAR) (x : SVAR) : Bool :=
    match phi with
    | Form.bttm     => true
    | Form.prop _   => true
    | Form.svar _   => true
    | Form.nom  _   => true
    | Form.impl phi psi => (is_substable phi y x) && (is_substable psi y x)
    | Form.box  phi   => is_substable phi y x
    | Form.bind z phi =>
        if (is_free x phi == false) then true
        else z != y && is_substable phi y x
    -- all s, s  -->  (all x, x)  : safe,   substitution won't do anything
    -- all x, x                : safe,   substitution won't do anything
    -- all y, y  -->  x           : safe,   result will be   all y, y  -->  s
    -- all s, y  -->  x           : UNSAFE, substitution would make x bound
    --                                      where it was previously free
    --
    -- Takeaway: s is substable for all free occurences of x only as long
    --         as x *does not occur free in the scope of an s-quantifier*

  notation:150 phi "[" s "//" x "]" => subst_svar phi s x
  notation:150 phi "[" s "//" x "]" => subst_nom  phi s x

end Substitutions

section NominalSubstitution

  def nom_subst_nom : Form N  ->  NOM N  ->  NOM N  ->  Form N
  | .nom a, i, j     => if a = j then i else a
  | .impl phi psi, i, j  => nom_subst_nom phi i j  -->  nom_subst_nom psi i j
  | .box phi, i, j     => []  nom_subst_nom phi i j
  | .bind y phi, i, j  => all y, nom_subst_nom phi i j
  | phi, _, _          => phi

  def nom_subst_svar : Form N  ->  SVAR  ->  NOM N  ->  Form N
  | .nom a, i, j     => if a = j then i else a
  | .impl phi psi, i, j  => nom_subst_svar phi i j  -->  nom_subst_svar psi i j
  | .box phi, i, j     => []  nom_subst_svar phi i j
  | .bind y phi, i, j  => all y, nom_subst_svar phi i j
  | phi, _, _          => phi

  notation:150 phi "[" i "//" a "]" => nom_subst_nom phi i a
  notation:150 phi "[" i "//" a "]" => nom_subst_svar phi i a

  def nom_occurs : NOM N  ->  Form N  ->  Bool
  | i, .nom j    => i = j
  | i, .impl psi chi => (nom_occurs i psi) || (nom_occurs i chi)
  | i, .box psi    => nom_occurs i psi
  | i, .bind _ psi => nom_occurs i psi
  | _, _         => false

  def all_nocc (i : NOM N) (Gamma : Set (Form N)) := forall  (phi : Form N), phi  in  Gamma  ->  nom_occurs i phi = false

  theorem nom_occurs_conj {i : NOM N} {phi psi : Form N} : nom_occurs i (phi  /\  psi) = (nom_occurs i phi || nom_occurs i psi) := by
    show nom_occurs i ((phi  -->  (psi  -->  False))  -->  False) = _
    simp only [nom_occurs, Bool.or_false]

  theorem all_noc_conj (h : all_nocc i Gamma) (L : List Gamma) : nom_occurs i (conjunction Gamma L) = false := by
    induction L with
    | nil => simp [conjunction, nom_occurs]
    | cons head tail ih =>
        have hd : nom_occurs i head.val = false := h head head.2
        show nom_occurs i (head.val  /\  conjunction Gamma tail) = false
        rw [nom_occurs_conj, hd, ih]; rfl

  def Form.bulk_subst : Form N  ->  List (NOM N)  ->  List (NOM N)  ->  Form N
  | phi, h_1 :: t_1, h_2 :: t_2 => bulk_subst (phi[h_1 // h_2]) t_1 t_2
  | phi, _, []    =>  phi
  | phi, [], _    =>  phi

  def Form.list_noms : (Form N)  ->  List (NOM N)
  | nom  i   => [i]
  | impl phi psi => (List.merge phi.list_noms psi.list_noms (GE.ge * *)).dedup
  | box phi    => phi.list_noms
  | bind _ phi => phi.list_noms
  | _        => []

  def Form.odd_list_noms : Form TotalSet  ->  List (NOM TotalSet) := fun  phi => phi.list_noms.map (fun  i => 2*i+1)

  def Form.odd_noms : Form TotalSet  ->  Form TotalSet := fun  phi => phi.bulk_subst phi.odd_list_noms phi.list_noms

  def Set.odd_noms : Set (Form TotalSet)  ->  Set (Form TotalSet) := fun  Gamma => {Form.odd_noms phi | phi  in  Gamma}

  def nocc_bulk_property (l1 l2 : List (NOM TotalSet)) (phi : Form TotalSet) := forall  {n : Fin l1.length} {i : NOM TotalSet}, (i = l1[n])  ->  (i  notin  phi.list_noms  \/  i  in  l2.take n)  /\  i  notin  l1.take n

  theorem list_noms_sorted_ge {phi : Form N} : phi.list_noms.Sorted GE.ge := by
    induction phi with
    | nom  i   => simp [Form.list_noms]
    | impl phi psi ih1 ih2 =>
        exact List.Pairwise.sublist ((List.merge phi.list_noms psi.list_noms (GE.ge * *)).dedup_sublist) (List.Pairwise.merge ih1 ih2)
    | box _ ih    => exact ih
    | bind _ _ ih => exact ih
    | _        => simp [Form.list_noms]

  theorem list_noms_nodup {phi : Form N} : phi.list_noms.Nodup := by
    induction phi <;> simp [Form.list_noms, List.nodup_dedup, *]

  theorem list_noms_sorted_gt {phi : Form N} : phi.list_noms.Sorted GT.gt := by
    have h := List.Pairwise.and (@list_noms_sorted_ge N phi) (@list_noms_nodup N phi)
    apply List.Pairwise.imp _ h
    intro a b hab
    exact NOM.gt_iff_ge_and_ne.mpr hab

  theorem list_noms_chain' {phi : Form N} : phi.list_noms.Chain' GT.gt := by
    show List.IsChain GT.gt phi.list_noms
    rw [List.isChain_iff_pairwise]
    exact list_noms_sorted_gt

end NominalSubstitution

section IteratedModalities

  -- Axiom utils. Since we won't be assuming a transitive frame,
  -- it will make sense to be able to construct formulas with
  -- iterated modal operators at their beginning (ex., for axiom nom)
  def iterate_nec (n : Nat) (phi : Form N) : Form N :=
    let rec loop : Nat  ->  Form  N  ->  Form N
      | 0, phi   => phi
      | n+1, phi => []  (loop n phi)
    loop n phi

  theorem iter_nec_one : []  phi = iterate_nec 1 phi := by
    rw [iterate_nec, iterate_nec.loop, iterate_nec.loop]

  theorem iter_nec_one_m_comm : iterate_nec 1 (iterate_nec m phi) = iterate_nec m (iterate_nec 1 phi) := by
    induction m with
    | zero =>
        simp [iterate_nec, iterate_nec.loop]
    | succ n ih =>
        simp [iterate_nec, iterate_nec.loop]
        exact ih

  theorem iter_nec_compose : iterate_nec (m + 1) phi = iterate_nec m (iterate_nec 1 phi) := by
    rw [iterate_nec, iterate_nec.loop, iter_nec_one,  <- iterate_nec, iter_nec_one_m_comm]

  theorem iter_nec_succ : iterate_nec (m + 1) phi = iterate_nec m ([]  phi) := by
    rw [iter_nec_one, iter_nec_compose]



  def iterate_pos (n : Nat) (phi : Form N) : Form N :=
    let rec loop : Nat  ->  Form N  ->  Form N
      | 0, phi   => phi
      | n+1, phi => <>  (loop n phi)
    loop n phi

  theorem iter_pos_one : <>  phi = iterate_pos 1 phi := by
    rw [iterate_pos, iterate_pos.loop, iterate_pos.loop]

  theorem iter_pos_one_m_comm : iterate_pos 1 (iterate_pos m phi) = iterate_pos m (iterate_pos 1 phi) := by
    induction m with
    | zero =>
        simp [iterate_pos, iterate_pos.loop]
    | succ n ih =>
        simp [iterate_pos, iterate_pos.loop]
        exact ih

  theorem iter_pos_compose : iterate_pos (m + 1) phi = iterate_pos m (iterate_pos 1 phi) := by
    rw [iterate_pos, iterate_pos.loop, iter_pos_one,  <- iterate_pos, iter_pos_one_m_comm]

  theorem iter_pos_succ : iterate_pos (m + 1) phi = iterate_pos m (<>  phi) := by
    rw [iter_pos_one, iter_pos_compose]


end IteratedModalities

  theorem ex_depth {x : SVAR} : Form.depth phi < Form.depth (ex x, phi) := by
    simp [Form.depth]
    rw [ <- Nat.add_assoc,  <- Nat.add_assoc, Nat.add_comm]
    apply Nat.lt_add_of_pos_right
    simp
