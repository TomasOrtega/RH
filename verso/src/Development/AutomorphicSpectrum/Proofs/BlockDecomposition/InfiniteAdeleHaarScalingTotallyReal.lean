import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.HaarUnit

/- English proof (translation)
Establish `hmult : ∀ w : InfinitePlace F, w.mult = 1` using `fun w => by`. Rewrite using `[InfinitePlace.mult, if_pos (hF.isReal w)]`. Establish `hw : ∀ w : InfinitePlace F, ‖((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ = ‖(n : InfiniteAdeleRing F) w‖⁻¹` using `fun w => by`. Establish `h1 : ((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w * (n : InfiniteAdeleRing F) w = 1` using `congrFun n.inv_mul w`. Establish `h2` using `congrArg norm h1`.

Rewrite `h2` using `[norm_mul, norm_one]`. Conclude with `eq_inv_of_mul_eq_one_left h2`. Rewrite using `[InfiniteAdeleRing.norm_def]`. Simplify using `only [hmult, pow_one, hw, NNReal.coe_inv, NNReal.coe_prod, coe_nnnorm]`. Rewrite using `[Finset.prod_inv_distrib]`.
-/
theorem norm_inv_unit (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    (n : (InfiniteAdeleRing F)ˣ) :
    ‖((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F)‖ =
      ((∏ w : InfinitePlace F, ‖(n : InfiniteAdeleRing F) w‖₊)⁻¹ : ℝ≥0) := by
  have hmult : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, if_pos (hF.isReal w)]
  have hw : ∀ w : InfinitePlace F,
      ‖((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ =
        ‖(n : InfiniteAdeleRing F) w‖⁻¹ := fun w => by
    have h1 : ((n⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w *
        (n : InfiniteAdeleRing F) w = 1 := congrFun n.inv_mul w
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    exact eq_inv_of_mul_eq_one_left h2
  rw [InfiniteAdeleRing.norm_def]
  simp only [hmult, pow_one, hw, NNReal.coe_inv, NNReal.coe_prod, coe_nnnorm]
  rw [Finset.prod_inv_distrib]

section Borel

attribute [local instance 100000] GroundTheory.Global.measurableSpace_infiniteAdeleRing

/- English proof (translation)
Take `rfl : m = GroundTheory.Global.measurableSpace_infiniteAdeleRing F` from `hm.measurable_eq.trans (GroundTheory.Global.borelSpace_infiniteAdeleRing (K := F)).measurable_eq.symm`. Establish `h` using `Measure.isAddLeftInvariant_eq_smul li (infiniteAdeleMeasure F)`. Rewrite using `[h, Measure.map_smul, map_mul_left_infiniteAdeleMeasure, smul_comm, norm_inv_unit F hF n, ENNReal.ofReal_coe_nnreal]`. Both sides reduce to the same expression.
-/
theorem infinite_adele_haar_scaling_by_unit (F : Type) [Field F] [NumberField F] (hF : IsTotallyReal F)
    {m : MeasurableSpace (InfiniteAdeleRing F)} (hm : @BorelSpace _ _ m)
    (li : Measure (InfiniteAdeleRing F)) (hli : li.IsAddHaarMeasure)
    (n : (InfiniteAdeleRing F)ˣ) :
    li.map (fun t => (n : InfiniteAdeleRing F) * t) =
      (∏ w : InfinitePlace F, ‖(n : InfiniteAdeleRing F) w‖₊)⁻¹ • li := by
  obtain rfl : m = GroundTheory.Global.measurableSpace_infiniteAdeleRing F :=
    hm.measurable_eq.trans (GroundTheory.Global.borelSpace_infiniteAdeleRing (K := F)).measurable_eq.symm
  have h := Measure.isAddLeftInvariant_eq_smul li (infiniteAdeleMeasure F)
  rw [h, Measure.map_smul, map_mul_left_infiniteAdeleMeasure, smul_comm, norm_inv_unit F hF n,
    ENNReal.ofReal_coe_nnreal]
  rfl

end Borel

/- English proof (translation)
Introduce `F _ _ hF li hli n`. Conclude with `infinite_adele_haar_scaling_by_unit F hF (m := measAinf) ⟨rfl⟩ li hli n`.
-/
theorem map_mul_unit : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
    ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ n : (Ainf F)ˣ,
      li.map (fun t => (n : Ainf F) * t) =
        (∏ w : InfinitePlace F, ‖(n : Ainf F) w‖₊)⁻¹ • li := by
  intro F _ _ hF li hli n
  exact infinite_adele_haar_scaling_by_unit F hF (m := measAinf) ⟨rfl⟩ li hli n

end GlobalTheory.CompanionTheory.SW.HaarUnit

end
