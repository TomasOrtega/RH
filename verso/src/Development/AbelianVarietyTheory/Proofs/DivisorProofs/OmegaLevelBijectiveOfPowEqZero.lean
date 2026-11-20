import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup

/- English proof (translation)
Introduce `p R _ N hN G n hn`. Use `⟨fun w w' h => ?_, G.omegaLevel_surjective n⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Establish `h0 : (w - w').1 n = 0`. Simplify using `only [omegaLevel_apply] at h`.

Express the relevant statement in the definitionally equal form `w.1 n - w'.1 n = 0`. Rewrite using `[h, sub_self]`. Take `⟨v, hv⟩` from `(G.omega_val_eq_zero_iff n (w - w')).1 h0`. Rewrite using `[hv, ← Nat.add_sub_cancel' hn, pow_add, hN, zero_mul, zero_smul]`.
-/
theorem omegaLevel_bijective_of_pow_eq_zero : ∀ (p : ℕ)  (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 → ∀ (G : PDivGroup p R) (n : ℕ), N ≤ n → Function.Bijective (G.omegaLevel n) := by
  intro p R _ N hN G n hn
  refine ⟨fun w w' h => ?_, G.omegaLevel_surjective n⟩
  rw [← sub_eq_zero]
  have h0 : (w - w').1 n = 0 := by
    simp only [omegaLevel_apply] at h
    change w.1 n - w'.1 n = 0
    rw [h, sub_self]
  obtain ⟨v, hv⟩ := (G.omega_val_eq_zero_iff n (w - w')).1 h0
  rw [hv, ← Nat.add_sub_cancel' hn, pow_add, hN, zero_mul, zero_smul]

end GlobalTheory.PDivGroup
