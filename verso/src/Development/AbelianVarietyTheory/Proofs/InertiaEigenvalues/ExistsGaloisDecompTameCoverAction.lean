import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisQlEqGaloisKPrimeMulGaloisKinftyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KummerMemFqOfMemGKinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoversTameOfFrobeniusTeichmullerStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TameCoverGen

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g`. Establish `he : e + 1 = l ^ a` using `TameDescentExponentData.succ_eq (K := K)`. Take `⟨h, hh, k, hk, hg⟩` from `GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ he (sQ l g)`. Set `h' : Gl l` to `⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩`. Use `⟨h', h'⁻¹ * g, by rw [mul_inv_cancel_left], hh, ?_⟩` and prove the remaining obligations.

Establish `hk' : sQ l (h'⁻¹ * g) = k`. Rewrite using `[map_mul, map_inv, show sQ l g = h * k from hg]`. Express the relevant statement in the definitionally equal form `h⁻¹ * (h * k) = k`. Rewrite using `[inv_mul_cancel_left]`. Rewrite using `[hk']`.

Take `⟨s, hs⟩` from `GlobalTheory.T.galois_action_cyclotomic_power l a k`. Take `⟨z, hz, hkz⟩` from `GlobalTheory.T.exists_root_of_unity_kummer_eq l a e ϖ he k hk`. Conclude with `GlobalTheory.T.exists_coversTame_of_frobenius_teichmuller l a e O K t ϖ k s z hz hs hkz`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (g : Gl l), ∃ h k : Gl l, g = h * k ∧ sQ l h ∈ GK (ϖ.field a) ∧ ∃ γ : TameGal K l e a, Covers K t ϖ (sQ l k) γ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ g
  have he : e + 1 = l ^ a := TameDescentExponentData.succ_eq (K := K)
  obtain ⟨h, hh, k, hk, hg⟩ := GlobalTheory.T.galoisQl_eq_galoisKPrime_mul_galoisKinfty l a e ϖ he (sQ l g)
  let h' : Gl l := ⟨h, GK_le (K := Formalism.MainNotions.ElementDenominator.qlExt l) (K' := ϖ.field a) bot_le hh⟩
  refine ⟨h', h'⁻¹ * g, by rw [mul_inv_cancel_left], hh, ?_⟩
  have hk' : sQ l (h'⁻¹ * g) = k := by
    rw [map_mul, map_inv, show sQ l g = h * k from hg]
    change h⁻¹ * (h * k) = k
    rw [inv_mul_cancel_left]
  rw [hk']
  obtain ⟨s, hs⟩ := GlobalTheory.T.galois_action_cyclotomic_power l a k
  obtain ⟨z, hz, hkz⟩ := GlobalTheory.T.exists_root_of_unity_kummer_eq l a e ϖ he k hk
  exact GlobalTheory.T.exists_coversTame_of_frobenius_teichmuller l a e O K t ϖ k s z hz hs hkz

end GlobalTheory.TameCoverGen
