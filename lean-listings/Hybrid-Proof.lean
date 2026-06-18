import Hybrid.Form
import Hybrid.Tautology

inductive Proof : Form N  ->  Type where
  -- Deduction rules:

  -- if phi is a theorem, forall  v, phi is a theorem
  | general {phi : Form N} (v : SVAR):
        Proof phi  ->  Proof (all v, phi)

  -- if phi is a theorem, []  phi is a theorem
  | necess {phi : Form N}:
        Proof phi  ->  Proof ([]  phi)

  -- modus ponens:
  | mp {phi psi : Form N}:
        Proof (phi  -->  psi)  ->  Proof phi  ->  Proof psi

  -- All propositional tautologies
  | tautology {phi : Form N}:
        Tautology phi  ->  Proof phi

  -- Axioms for modal + hybrid logic:
  -- distribution schema (axiom K)
  | ax_k {phi psi : Form N}:
        Proof ([]  (phi  -->  psi)  -->  ([]  phi  -->  []  psi))

  | ax_q1 (phi psi : Form N) {v : SVAR} (p : is_free v phi = false):
        Proof ((all v, phi  -->  psi)  -->  (phi  -->  all v, psi))

  -- two different instances of Axiom Q2: one for SVAR, one for NOM
  | ax_q2_svar (phi : Form N) (v s : SVAR) (p : is_substable phi s v):
      Proof ((all v, phi)  -->  phi[s // v])

  | ax_q2_nom (phi : Form N) (v : SVAR) (s : NOM N):
      Proof ((all v, phi)  -->  phi[s // v])

  | ax_name (v : SVAR):
      Proof (ex v, v)

  | ax_nom {phi : Form N} {v : SVAR} (m n : Nat):
      Proof (all v, (iterate_pos m (v  /\  phi)  -->  iterate_nec n (v  -->  phi)))

  | ax_brcn {phi : Form N} {v : SVAR}:
      Proof ((all v, []  phi)  -->  ([]  all v, phi))

def Proof.size : Proof phi  ->  Nat
  | .general _ pf => pf.size + 1
  | .necess pf    => pf.size + 1
  | .mp pf1 pf2   => pf1.size + pf2.size + 1
  | _ => 1

lemma Proof.size_lt_mp {a b : Form N} (pf1 : Proof (a  -->  b)) (pf2 : Proof a) :
    pf1.size < (mp pf1 pf2).size := by simp [Proof.size]; omega

lemma Proof.size_lt_mp_2 {a b : Form N} (pf1 : Proof (a  -->  b)) (pf2 : Proof a) :
    pf2.size < (mp pf1 pf2).size := by simp [Proof.size]; omega

lemma Proof.size_lt_general {phi : Form N} (v : SVAR) (pf : Proof phi) :
    pf.size < (general v pf).size := by simp [Proof.size]

lemma Proof.size_lt_necess {phi : Form N} (pf : Proof phi) :
    pf.size < (necess pf).size := by simp [Proof.size]

def Proof.contains {phi : Form N} : Proof phi  ->  Form N  ->  Bool :=
  fun  pf psi => phi == psi ||
    match pf with
    | .general _ pf' => pf'.contains phi
    | .necess pf'    => pf'.contains phi
    | .mp pf1 pf2    => pf1.contains phi || pf2.contains phi
    | _ => false

def Proof.fresh_var : Proof phi  ->  SVAR  ->  Prop := fun  pf x => forall  psi, pf.contains psi  ->  x  >=  psi.new_var

/-- Every formula root appearing in a derivation (for nominal inventory / conservativity). -/
def Proof.formulasIn {phi : Form N} : Proof phi  ->  List (Form N)
  | .tautology _ => [phi]
  | .ax_k => [phi]
  | .ax_q1 _ _ _ => [phi]
  | .ax_q2_svar _ _ _ _ => [phi]
  | .ax_q2_nom _ _ _ => [phi]
  | .ax_name _ => [phi]
  | .ax_nom _ _ => [phi]
  | .ax_brcn => [phi]
  | .general _ pf => phi :: pf.formulasIn
  | .necess pf => phi :: pf.formulasIn
  | .mp pf1 pf2 => phi :: pf1.formulasIn ++ pf2.formulasIn

/-- Nominals occurring in any formula of a derivation (deduped, descending merge order). -/
def Proof.proof_noms {phi : Form N} (pf : Proof phi) : List (NOM N) :=
  (pf.formulasIn.flatMap Form.list_noms).dedup

def SyntacticConsequence (Gamma : Set (Form N)) (phi : Form N) := Sigma L, Proof ((conjunction Gamma L)  -->  phi)

prefix:500 " |- "  => Proof
infix:500 " |- "   => SyntacticConsequence

notation " |/- " phi    => (Proof phi)  ->  False
notation Gamma " |/- " phi  => (SyntacticConsequence Gamma phi)  ->  False


def consistent (Gamma : Set (Form N)) := forall  (_ : SyntacticConsequence Gamma False), False

def MCS (Gamma : Set (Form N)) := consistent Gamma  /\  (forall  {phi : Form N}, (not phi  in  Gamma)  ->  not consistent (Gamma  U  {phi}))

def witnessed (Gamma : Set (Form N)) : Prop := forall  {phi : Form N},
  phi  in  Gamma  -> 
    match phi with
--      | ex x, psi => exists  i : NOM, ((ex x, psi)  -->  psi[i // x])  in  Gamma
      | ex x, psi => exists  i : NOM N, psi[i // x]  in  Gamma
      | _   => phi  in  Gamma
