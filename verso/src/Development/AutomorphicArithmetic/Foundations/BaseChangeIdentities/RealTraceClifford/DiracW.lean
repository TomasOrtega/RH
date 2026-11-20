import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracCh
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.Conclusion2
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.MSymm
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.IrrCh
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws.

Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem uf_kF {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} (hP : IsPair E1 E2) : UF (kF E1 E2) := by
  refine ⟨?_, hP.unitK⟩
  intro a b c d
  have g1 := hP.gl1 a b c d
  have g2 := hP.gl2 a b c d
  have h3 := hP.comm a b c d
  have h4 := hP.comm c d a b
  have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add]
    rw [h3, h4]
    abel
  rw [e, g1, g2]
  split_ifs <;> (try simp only [kF]) <;> abel

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.RealTr.diracW :
    ∀ (n : ℕ) (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V),
      IsPair E1 E2 → LocF (kF E1 E2) → (∀ m (x : V), gelA E1 m x = GlobalTheory.Dec.gelfVal (infOf lam true) m • x) →
      (∀ m (x : V), gelA (barF E2) m x = GlobalTheory.Dec.gelfVal (infOf lam false) m • x) → ∀ ν : Wt n, hwSp E1 E2 ν ≠ ⊥ → LSq lam ≤ spinSq ν := by
  intro n lam V _ _ E1 E2 hP hL h1 h2 ν hν
  have hν' : hw (kF E1 E2) ν ≠ ⊥ := by rwa [hwSp_eq] at hν
  have hD : Dom ν := (irrCh n V (kF E1 E2) (uf_kF hP) hL ν hν').1
  have hR := rearr n
  have hx : StrictAnti (domC (ν - rhoV n) + rhoV n) := by
    intro a b hab
    exact add_lt_add_of_le_of_lt ((hR.2.1 (ν - rhoV n)).1 hab.le) (hR.2.2.1 hab)
  have hc : cf (chR n * alt (ν + rhoV n)) (domC (ν - rhoV n) + rhoV n) ≠ 0 := by
    rw [mSymm, aux₃ n ν hD]
    exact one_ne_zero
  exact diracCh n lam V E1 E2 hP hL h1 h2 ν _ hν hx hc
