import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLiftCompatibleBdRPrisms
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LiftMatK

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem pow_mul_mem_integers (K : FinExt l) (a : ↥K.1) : ∃ k : ℕ, (l : ↥K.1) ^ k * a ∈ OL K := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have h1 : IsAlgebraic ℚ_[l] a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ_[l] a := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥K.1).2 h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy
    (PadicInt.irreducible_p (p := l))
  refine ⟨k, ?_⟩
  have h3 := hi.smul ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])
  rw [smul_smul, ← mul_assoc, Units.inv_mul, one_mul, Algebra.smul_def, map_pow, map_natCast] at h3
  exact h3

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem lift_one (K : FinExt l) (bk : BK K) (C : Core l) (x : Om l) (hx : x ∈ K.1) (n : ℕ) :
    ∃ (m : ℕ) (s : bk.S), aDp l (bk.ev s) - (l : Per.BdRp l) ^ m * C.o x ∈ Per.FilP l n := by
  obtain ⟨a, ha⟩ := pow_mul_mem_integers K ⟨x, hx⟩
  obtain ⟨k, s, hs, -⟩ := GlobalTheory.BSP.RingHomLiftCongruence.exists_lift l K bk C n ⟨_, ha⟩
  refine ⟨k + a, s, ?_⟩
  have e : ((((⟨_, ha⟩ : ↥(OL K)) : ↥K.1)) : Om l) = (l : Om l) ^ a * x := by
    simp
  rw [e, map_mul, map_pow, map_natCast, ← mul_assoc, ← pow_add] at hs
  exact hs

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Apply an available result and prove the equalities needed to match it to the conclusion. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem lift_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (d : ℕ) (c : Matrix (Fin d) (Fin d) (Om l)), (∀ i j, c i j ∈ K.1) → ∀ n : ℕ, ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * C.o (c i j) ∈ Per.FilP l n := by
  intro l _ K bk C d c hc n
  choose m s hs using fun i j => lift_one K bk C (c i j) (hc i j) n
  let M := Finset.univ.sup (fun p : Fin d × Fin d => m p.1 p.2)
  refine ⟨M, fun i j => (l : bk.S) ^ (M - m i j) * s i j, fun i j => ?_⟩
  have hle : m i j ≤ M := Finset.le_sup (f := fun p : Fin d × Fin d => m p.1 p.2) (Finset.mem_univ (i, j))
  have h := Ideal.mul_mem_left _ ((l : Per.BdRp l) ^ (M - m i j)) (hs i j)
  simp only [map_mul, map_pow, map_natCast]
  convert h using 1
  rw [mul_sub, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

end GlobalTheory.LiftMatK
