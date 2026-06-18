import Hybrid.Form

structure Eval (N : Set Nat) where
  f  : Form N  ->  Bool
  p1 : f False = false
  p2 : forall  phi psi : Form N, (f (phi  -->  psi) = true)  <->  (not (f phi) = true  \/  (f psi) = true)

def Tautology (phi : Form N) : Prop := forall  e : Eval N, e.f phi = true

theorem tautology_nom_subst {phi : Form N} (h : Tautology phi) (new old : NOM N) :
    Tautology (phi[new // old]) := by
  intro e
  let f : Form N  ->  Bool := fun psi => e.f (psi[new // old])
  have p1 : f False = false := by simp [f, nom_subst_nom, e.p1]
  have p2 : forall  psi chi, f (psi  -->  chi) = true  <->  (not  f psi = true  \/  f chi = true) := by
    intro psi chi
    show e.f ((psi  -->  chi)[new // old]) = true  <->  _
    simp only [nom_subst_nom, f]
    exact e.p2 (psi[new // old]) (chi[new // old])
  exact h <f, p1, p2>

theorem e_dn {e : Eval N} : e.f (~phi) = false  <->  e.f phi = true := by
  rw [Form.neg,  <-  Bool.not_eq_true, e.p2, e.p1]
  simp [Bool.not_eq_true]

theorem e_neg {e : Eval N} : e.f (~phi) = true  <->  e.f phi = false := by
  have c := @not_congr (e.f (~phi) = false) (e.f phi = true) e_dn
  rw [Bool.not_eq_false, Bool.not_eq_true] at c
  exact c

theorem e_conj {e : Eval N} : e.f (phi  /\  psi) = true  <->  (e.f phi = true  /\  e.f psi = true) := by
  rw [Form.conj,  <- Bool.not_eq_false, e_dn, e.p2, not_or, not_not, Bool.not_eq_true, e_dn]

theorem e_disj {e : Eval N} : e.f (phi  \/  psi) = true  <->  (e.f phi = true  \/  e.f psi = true) := by
  rw [Form.disj, e.p2, Bool.not_eq_true, e_dn]

theorem e_impl {e : Eval N} : e.f (phi  -->  psi) = true  <->  (e.f phi = true  ->  e.f psi = true) := by
  simp only [e.p2, implication_disjunction]

syntax "eval" : tactic
macro_rules
  | `(tactic| eval) => `(tactic| intro e; simp [e.p1, e.p2, e_dn, e_neg, e_conj, e_disj, e_impl, -Form.neg, -Form.conj, -Form.disj, -Form.iff])

theorem hs_taut : Tautology ((phi  -->  psi)  -->  (psi  -->  chi)  -->  (phi  -->  chi)) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem ax_1 : Tautology (phi  -->  psi  -->  phi) := by
  intro e
  simp only [e.p2, Bool.not_eq_true, or_comm,  <- or_assoc, Bool.dichotomy, true_or]

theorem neg_conj : Tautology ((phi  -->  ~psi)  <->  ~(phi  /\  psi)) := by
  simp
  eval

theorem contrapositive : Tautology ((phi  -->  psi)  -->  (~psi  -->  ~phi)) := by
  eval
  simp only [or_comm]
  simp only [and_or_right]
  apply And.intro
  . rw [ <- or_assoc,  <- Bool.not_eq_true]
    apply Or.inl
    apply em
  . rw [ <- or_comm, or_assoc, or_comm,  <- Bool.not_eq_true]
    apply Or.inl
    apply em

theorem contrapositive' : Tautology ((~psi  -->  ~phi)  -->  (phi  -->  psi)) := by
  eval
  simp only [or_comm]
  simp only [and_or_right]
  apply And.intro
  . rw [ <- or_assoc,  <- Bool.not_eq_true]
    apply Or.inl
    rw [or_comm]
    apply em
  . rw [ <- or_comm, or_assoc, or_comm,  <- Bool.not_eq_true]
    apply Or.inl
    rw [or_comm]
    apply em

theorem neg_intro : Tautology ((phi  -->  psi)  -->  (phi  -->  ~psi)  -->  ~phi) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem imp_refl : Tautology (phi  -->  phi) := by
  eval

theorem imp_neg : Tautology (~(phi  -->  psi)  <->  (phi  /\  ~psi)) := by
  simp only [Form.iff, Form.conj, Form.neg]
  eval

theorem dne : Tautology (~~phi  -->  phi) := by
  eval

theorem dni : Tautology (phi  -->  ~~phi) := by
  eval

theorem dn : Tautology (phi  <->  ~~phi) := by
  intro e
  rw [Form.iff, e_conj]
  exact <dni e, dne e> 

theorem conj_intro : Tautology (phi  -->  psi  -->  (phi  /\  psi)) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem conj_intro_hs : Tautology ((phi  -->  psi)  -->  (phi  -->  chi)  -->  (phi  -->  (psi  /\  chi))) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem conj_elim_l : Tautology ((phi  /\  psi)  -->  phi) := by
  eval
  simp [ <- or_assoc, or_comm, Bool.dichotomy]

theorem conj_elim_r : Tautology ((phi  /\  psi)  -->  psi) := by
  eval
  simp [or_assoc, Bool.dichotomy]

theorem conj_comm_t : Tautology ((phi  /\  psi)  -->  (psi  /\  phi)) := by
  intro e
  simp only [e_impl, e_conj]
  tauto

theorem conj_comm_t' : Tautology (~(phi  /\  psi)  -->  ~(psi  /\  phi)) := by
  intro e
  simp only [e_impl, e_neg,  <-  Bool.not_eq_true, e_conj]
  tauto

theorem iff_intro : Tautology ((phi  -->  psi)  -->  (psi  -->  phi)  -->  (phi  <->  psi)) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem iff_elim_l : Tautology ((phi  <->  psi)  -->  (phi  -->  psi)) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem iff_elim_r : Tautology ((phi  <->  psi)  -->  (psi  -->  phi)) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem iff_rw : Tautology ((phi  <->  psi)  -->  (psi  <->  chi)  -->  (phi  <->  chi)) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem iff_imp : Tautology ((phi  <->  psi)  -->  (chi  <->  tau)  -->  ((phi  -->  chi)  <->  (psi  -->  tau))) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem taut_iff_mp : Tautology (phi  <->  psi)  ->  Tautology (phi  -->  psi) := by
  rw [Form.iff]
  intro h e
  have := h e
  rw [e_conj] at this
  exact this.left

theorem taut_iff_mpr : Tautology (phi  <->  psi)  ->  Tautology (psi  -->  phi) := by
  rw [Form.iff]
  intro h e
  have := h e
  rw [e_conj] at this
  exact this.right

theorem disj_intro_l : Tautology (phi  -->  (phi  \/  psi)) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem disj_intro_r : Tautology (phi  -->  (psi  \/  phi)) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem disj_elim : Tautology ((phi  \/  psi)  -->  (phi  -->  chi)  -->  (psi  -->  chi)  -->  chi) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

theorem idem : Tautology ((chi  -->  psi  -->  psi  -->  phi)  -->  (chi  -->  psi  -->  phi)) := by
  intro e
  simp only [e_impl]
  tauto

theorem exp : Tautology (((phi  /\  psi)  -->  chi)  -->  (phi  -->  psi  -->  chi)) := by
  intro e
  simp only [e_impl, e_conj]
  tauto

theorem imp : Tautology ((phi  -->  psi  -->  chi)  -->  ((phi  /\  psi))  -->  chi) := by
  intro e
  simp only [e_impl, e_conj]
  tauto

theorem impexp : Tautology (((phi  /\  psi)  -->  chi)  <->  (phi  -->  psi  -->  chi)) := by
  intro e
  rw [Form.iff, e_conj]
  exact <exp e, imp e>

theorem com12 : Tautology ((phi  -->  (psi  -->  chi))  -->  (psi  -->  (phi  -->  chi))) := by
  intro e
  simp only [e_impl]
  intro h1 h2 h3
  exact h1 h3 h2

theorem mp_help : Tautology ((a  -->  (phi  -->  psi))  -->  ((b  -->  phi)  -->  (a  -->  b  -->  psi))) := by
  intro e
  simp only [Form.iff, e_impl, e_neg, e_conj, e_disj,  <-  Bool.not_eq_true]
  tauto

def Eval.nom_variant (e e' : Eval N) (i : NOM N) (x : SVAR) : Prop :=
  e'.f = (fun  phi : Form N => if phi = i then (e.f x) else (e.f phi))

theorem iff_not : Tautology ((phi  <->  psi)  <->  (~phi  <->  ~psi)) := by
  simp only [Form.iff, Form.conj, Form.neg]
  eval
 
theorem imp_taut (h : Tautology phi) : Tautology ((phi  -->  psi)  -->  psi) := by
  unfold Tautology at h  |- 
  intro e
  have := h e
  simp [this, e.p1, e.p2, e_dn, e_neg, e_conj, e_disj, e_impl, -Form.neg, -Form.conj, -Form.disj, -Form.iff]
