import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevels

/- English proof (translation)
Introduce `x`. Use `⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict x, ?_⟩` and prove the remaining obligations. Unfold `pInv`. Conclude with `(RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply x`.
-/
theorem pInv_surjective (l : ℕ) [Fact l.Prime] : Function.Surjective (pInv l) := by
  intro x
  refine ⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict x, ?_⟩
  unfold pInv
  exact (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply x

/- English proof (translation)
Establish `h1 : Function.Surjective ((pk l k).comp (pInv l))`. Rewrite using `[RingHom.coe_comp]`. Conclude with `(Ideal.Quotient.mk_surjective).comp (pInv_surjective l)`. Conclude with `h1`.
-/
theorem toB_surjective {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : Function.Surjective (lev h k).toB := by
  have h1 : Function.Surjective ((pk l k).comp (pInv l)) := by
    rw [RingHom.coe_comp]
    exact (Ideal.Quotient.mk_surjective).comp (pInv_surjective l)
  exact h1

end GlobalTheory.CompanionTheory.LatLevels
