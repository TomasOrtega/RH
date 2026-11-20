import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

open NumberField.Units IsCMField in

/- English proof (translation)
Establish `hrank : 0 < rank E`. Establish `h1` using `IsTotallyComplex.finrank (K := E)`. Establish `h2` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)`. Establish `h3` using `IsTotallyComplex.nrRealPlaces_eq_zero (K := E)`. Unfold `rank`.

Use linear arithmetic over natural numbers and integers. Set `i : Fin (rank E)` to `⟨0, hrank⟩`. Use `⟨realFundSystem E i, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [realFundSystem, cc]`. Conclude with `complexConj_apply_eq_self E _`.

Introduce `n hn hpow set v := fundSystem (maximalRealSubfield E) (finCongr (units_rank_eq_units_rank E).symm i)`. Establish `hv : v ^ n = 1`. Establish `hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) E)` using `(FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) E)`. Apply `Units.ext` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one, IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (𝓞 E) E]`. Conclude with `hpow`. Establish `htor : v ∈ torsion (maximalRealSubfield E)` using `(CommGroup.mem_torsion _).mpr ((isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, hv⟩)`. Establish `hmk` using `fundSystem_mk (maximalRealSubfield E) (finCongr (units_rank_eq_units_rank E).symm i)`. Rewrite `hmk` using `[(QuotientGroup.eq_one_iff _).mpr htor]`.

Conclude with `(basisModTorsion (maximalRealSubfield E)).ne_zero _ hmk.symm`.
-/
theorem exists_real_unit_infinite_order (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hE : 1 < Module.finrank ℚ E / 2) :
    ∃ u : (𝓞 E)ˣ, cc (u : E) = u ∧ ∀ n : ℕ, 0 < n → (u : E) ^ n ≠ 1 := by
  have hrank : 0 < rank E := by
    have h1 := IsTotallyComplex.finrank (K := E)
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
    have h3 := IsTotallyComplex.nrRealPlaces_eq_zero (K := E)
    unfold rank
    omega
  let i : Fin (rank E) := ⟨0, hrank⟩
  refine ⟨realFundSystem E i, ?_, ?_⟩
  · simp only [realFundSystem, cc]
    exact complexConj_apply_eq_self E _
  · intro n hn hpow
    set v := fundSystem (maximalRealSubfield E) (finCongr (units_rank_eq_units_rank E).symm i)
    have hv : v ^ n = 1 := by
      have hinj : Function.Injective (algebraMap (𝓞 (maximalRealSubfield E)) E) :=
        (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) E)
      apply Units.ext
      apply hinj
      rw [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one,
        IsScalarTower.algebraMap_apply (𝓞 (maximalRealSubfield E)) (𝓞 E) E]
      exact hpow
    have htor : v ∈ torsion (maximalRealSubfield E) := (CommGroup.mem_torsion _).mpr
      ((isOfFinOrder_iff_pow_eq_one).mpr ⟨n, hn, hv⟩)
    have hmk := fundSystem_mk (maximalRealSubfield E) (finCongr (units_rank_eq_units_rank E).symm i)
    rw [(QuotientGroup.eq_one_iff _).mpr htor] at hmk
    exact (basisModTorsion (maximalRealSubfield E)).ne_zero _ hmk.symm

end GlobalTheory.UnipKill
