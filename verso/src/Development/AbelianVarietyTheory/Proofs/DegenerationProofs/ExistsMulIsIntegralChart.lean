import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOverStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsIntegralMulPowOfSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNmOfIsClVeronese

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

/- English proof (translation)
Use `set A := Algebra.adjoin o (Set.range fun j => t j / t i) with hA`. Use `set K := Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) with hKdef`. Establish `hK : K ≤ Subfield.closure (A : Set Ω)`. Use `Subfield.closure_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `x (⟨a, rfl⟩ | ⟨k, j, rfl⟩)`.

Conclude with `Subfield.subset_closure (A.algebraMap_mem a)`. Establish `: t j / t k = (t j / t i) / (t k / t i)`. Rewrite using `[div_div_div_cancel_right₀ hi]`. Rewrite using `[this]`. Conclude with `div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩)) (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))`.

Establish `hAK : ∀ y ∈ A, y ∈ K`. Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`.

Conclude with `Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩)`. Consider the case `algebraMap a => exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `mul x y _ _ hx hy => exact mul_mem hx hy`. Use `letI : Algebra A K := (A.val.toRingHom.codRestrict K fun y => hAK y y.2).toAlgebra`.

Use `haveI : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).2 fun a b h => Subtype.ext (congrArg (fun c : K => (c : Ω)) h)`. Use `haveI : IsFractionRing A K := by`. Use `IsFractionRing.of_field _ _ fun c => ?_` and prove the remaining obligations. Take `⟨y, hy, w, hw, hc⟩` from `Subfield.mem_closure_iff.mp (hK c.2)`.

Establish `hAA : Subring.closure (A : Set Ω) = A.toSubring` using `Subring.closure_eq A.toSubring`. Rewrite `hy`, `hw` using `[hAA]`. Conclude with `⟨⟨y, hy⟩, ⟨w, hw⟩, Subtype.ext hc.symm⟩`. Establish `h1 : IsAlgebraic A x` using `(IsFractionRing.isAlgebraic_iff A K Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)`. Take `⟨a, ha, h⟩` from `h1.exists_integral_multiple`.

Conclude with `⟨a, a.2, fun h0 => ha (Subtype.ext h0), h⟩`.
-/
theorem exists_mul_isIntegral_chart {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {J : Type} (t : J → Ω)
    {i : J} (hi : t i ≠ 0)
    (hfin : Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω)
    (x : Ω) : ∃ a ∈ Algebra.adjoin o (Set.range fun j => t j / t i), a ≠ 0 ∧
      IsIntegral (Algebra.adjoin o (Set.range fun j => t j / t i)) (a * x) := by
  set A := Algebra.adjoin o (Set.range fun j => t j / t i) with hA
  set K := Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i}) with hKdef
  have hK : K ≤ Subfield.closure (A : Set Ω) := by
    refine Subfield.closure_le.mpr ?_
    rintro x (⟨a, rfl⟩ | ⟨k, j, rfl⟩)
    · exact Subfield.subset_closure (A.algebraMap_mem a)
    · have : t j / t k = (t j / t i) / (t k / t i) := by
        rw [div_div_div_cancel_right₀ hi]
      rw [this]
      exact div_mem (Subfield.subset_closure (Algebra.subset_adjoin ⟨j, rfl⟩))
        (Subfield.subset_closure (Algebra.subset_adjoin ⟨k, rfl⟩))
  have hAK : ∀ y ∈ A, y ∈ K := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩)
    | algebraMap a => exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  letI : Algebra A K := (A.val.toRingHom.codRestrict K fun y => hAK y y.2).toAlgebra
  haveI : IsScalarTower A K Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective A K).2 fun a b h =>
    Subtype.ext (congrArg (fun c : K => (c : Ω)) h)
  haveI : IsFractionRing A K := by
    refine IsFractionRing.of_field _ _ fun c => ?_
    obtain ⟨y, hy, w, hw, hc⟩ := Subfield.mem_closure_iff.mp (hK c.2)
    have hAA : Subring.closure (A : Set Ω) = A.toSubring := Subring.closure_eq A.toSubring
    rw [hAA] at hy hw
    exact ⟨⟨y, hy⟩, ⟨w, hw⟩, Subtype.ext hc.symm⟩
  have h1 : IsAlgebraic A x := (IsFractionRing.isAlgebraic_iff A K Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨a, ha, h⟩ := h1.exists_integral_multiple
  exact ⟨a, a.2, fun h0 => ha (Subtype.ext h0), h⟩

/- English proof (translation)
Introduce `o Ω _ _ _ _ _ hinj J _ t ht hfin`. Take `⟨e, n, z, he, hk, hint, hsum⟩` from `GlobalTheory.exists_tuple_normalisation_charts o Ω hinj J t ht hfin`. Take `⟨i, hi⟩` from `ht`. Take `⟨k, hzk⟩` from `hk i`. Establish `hL : ∀ y ∈ Algebra.adjoin o (Set.range fun l => z l / t i ^ e), y ∈ Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = z j / z i})`.

Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Conclude with `Subfield.subset_closure (Or.inr ⟨k, j, by rw [hzk]⟩)`.

Consider the case `algebraMap a => exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `mul x y _ _ hx hy => exact mul_mem hx hy`. Take `⟨M, hM, hP⟩` from `GlobalTheory.T.exists_projectiveClosure_isProjOver o Ω n z ⟨k, by rw [hzk]; exact pow_ne_zero _ hi⟩ (by`. Use `top_unique fun x _ => ?_` and prove the remaining obligations.

Take `⟨a, ha, ha0, h⟩` from `exists_mul_isIntegral_chart t hi hfin x`. Establish `h1` using `hL _ ((hint i hi _).2 h)`. Establish `h2` using `hL _ ((hint i hi a).2 (isIntegral_algebraMap (R := Algebra.adjoin o (Set.range fun j => t j / t i)) (x := ⟨a, ha⟩)))`. Establish `h3` using `div_mem h1 h2`. Rewrite using `[mul_div_cancel_left₀ _ ha0] at h3)` and apply the resulting hypothesis.

Conclude with `⟨M, isNm_of_isCl_veronese o Ω M J t e n z he hM hk hint hsum, hP⟩`.
-/
theorem exists_isNm_isProjOver : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsDedekindDomain o] [CharZero Ω], Function.Injective (algebraMap o Ω) → ∀ (J : Type) [Fintype J] (t : J → Ω), (∃ i, t i ≠ 0) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω → ∃ M : RatModel o Ω, M.IsNm t ∧ IsProjOver M.s := by
  intro o Ω _ _ _ _ _ hinj J _ t ht hfin
  obtain ⟨e, n, z, he, hk, hint, hsum⟩ := GlobalTheory.exists_tuple_normalisation_charts o Ω hinj J t ht hfin
  obtain ⟨i, hi⟩ := ht
  obtain ⟨k, hzk⟩ := hk i
  have hL : ∀ y ∈ Algebra.adjoin o (Set.range fun l => z l / t i ^ e),
      y ∈ Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = z j / z i}) := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      exact Subfield.subset_closure (Or.inr ⟨k, j, by rw [hzk]⟩)
    | algebraMap a => exact Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  obtain ⟨M, hM, hP⟩ := GlobalTheory.T.exists_projectiveClosure_isProjOver o Ω n z ⟨k, by rw [hzk]; exact pow_ne_zero _ hi⟩ (by
    refine top_unique fun x _ => ?_
    obtain ⟨a, ha, ha0, h⟩ := exists_mul_isIntegral_chart t hi hfin x
    have h1 := hL _ ((hint i hi _).2 h)
    have h2 := hL _ ((hint i hi a).2 (isIntegral_algebraMap
      (R := Algebra.adjoin o (Set.range fun j => t j / t i)) (x := ⟨a, ha⟩)))
    have h3 := div_mem h1 h2
    rwa [mul_div_cancel_left₀ _ ha0] at h3)
  exact ⟨M, isNm_of_isCl_veronese o Ω M J t e n z he hM hk hint hsum, hP⟩

end GlobalTheory.ZH
