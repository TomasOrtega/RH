import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHtFunGenericIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InterNumRedCloPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegFlLamAPowVdmCl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDeterminantIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRootDivisorRelation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoDetAffDetOm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseOfFlagCpt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseDimEqCmTypeCardMulPq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodChernWeilOfGoodTopChernForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeil

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArithmeticHeightTower.TowerCopy

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.VdmRec GlobalTheory.ProjVar

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem topSelf_eq_finrank_mul {X : Scheme.{0}} (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra K Γ(X, ⊤)]
    [Algebra k Γ(X, ⊤)] (hk : ∀ a : k, algebraMap k Γ(X, ⊤) a = algebraMap K Γ(X, ⊤) (algebraMap k K a))
    (M : LB X) (d : ℕ) : topSelfIntersection k M d = (Module.finrank k K : ℤ) * topSelfIntersection K M d := by
  have hχ (F : X.Modules) : chi k F = (Module.finrank k K : ℤ) * chi K F := by
    have hT (n : ℕ) : IsScalarTower k K (coh F n) := by
      refine ⟨fun a b x => ?_⟩
      change cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) (a • b)) x =
        cohOn.action F ⊤ n (algebraMap k Γ(X, ⊤) a) (cohOn.action F ⊤ n (algebraMap K Γ(X, ⊤) b) x)
      rw [Algebra.smul_def, map_mul, map_mul, hk]
      rfl
    have e (n : ℕ) : ((-1 : ℤ) ^ n * hdim k F n) = (Module.finrank k K : ℤ) * ((-1 : ℤ) ^ n * hdim K F n) := by
      rw [hdim_def, hdim_def, ← Module.finrank_mul_finrank k K (coh F n)]
      push_cast
      ring
    rw [chi_def, chi_def]
    simp_rw [e]
    exact (mul_finsum _ _).symm
  rw [topSelf_def, topSelf_def, interNum_def, interNum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [hχ]
  ring

end GlobalTheory.ArithmeticHeightTower.TowerCopy
