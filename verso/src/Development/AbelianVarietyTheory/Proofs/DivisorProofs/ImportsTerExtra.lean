import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistChoiceExample
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

open NumberField

namespace GlobalTheory.StarIntegralityLemmas

/- English proof (translation)
Establish `hi : IsIntegral ℤ (star (r : K))`. Use `(RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom` as an intermediate fact. Simplify `this` using `[starRingEnd_apply]`. Conclude with `⟨⟨star (r : K), (mem_integralClosure_iff ℤ K).mpr hi⟩, rfl⟩`.
-/
theorem star_int {K : Type} [Field K] [NumberField K] [StarRing K] (r : 𝓞 K) :
    ∃ r' : 𝓞 K, (r' : K) = star (r : K) := by
  have hi : IsIntegral ℤ (star (r : K)) := by
    have := (RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom
    simpa [starRingEnd_apply] using this
  exact ⟨⟨star (r : K), (mem_integralClosure_iff ℤ K).mpr hi⟩, rfl⟩

/- English proof (translation)
Introduce `K _ _ _ d h T hT x`. Take `⟨S, rfl⟩` from `hT`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (S.image fun v => h v x)`. Use `⟨(b : 𝓞 K), nonZeroDivisors.coe_ne_zero b, ?_⟩` and prove the remaining obligations. Establish `key : ∀ y : Fin d → K, h y ((b : 𝓞 K) • x) = algebraMap (𝓞 K) K (b : 𝓞 K) * h y x`.

Introduce `y`. Rewrite using `[← algebraMap_smul K (b : 𝓞 K) x, map_smul, smul_eq_mul]`. Unfold `Formalism.HermitianLatticesTheory.dual Formalism.E.hdual`. Simplify using `only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]`. Introduce `y hy`.

Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨c, hc⟩` from `hb (h v x) (Finset.mem_image_of_mem _ hv)`. Rewrite using `[key, Submodule.mem_one]`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Rewrite using `[hc, Algebra.smul_def]`. Consider the case `zero => simp`. Consider the case `add u w _ _ hu hw`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `Submodule.add_mem _ hu hw`.

Consider the case `smul r u _ hu`. Take `⟨r', hr'⟩` from `star_int r`. Rewrite using `[← algebraMap_smul K r u, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]`. Take `⟨c, hc⟩` from `Submodule.mem_one.mp hu`. Rewrite using `[Submodule.mem_one]`.

Use `⟨r' * c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hc]`. Simplify using `[hr']`.
-/
theorem main : ∀ {K : Type} [inst : Field K] [NumberField K] [inst_2 : StarRing K] {d : ℕ}
    (h : (Fin d → K) →ₗ⋆[K] (Fin d → K) →ₗ[K] K)
    (T : Submodule (NumberField.RingOfIntegers K) (Fin d → K)), Submodule.FG T →
    ∀ (x : Fin d → K), ∃ (s : NumberField.RingOfIntegers K),
      s ≠ (0 : NumberField.RingOfIntegers K) ∧ s • x ∈ Formalism.HermitianLatticesTheory.dual h T := by
  intro K _ _ _ d h T hT x
  classical
  obtain ⟨S, rfl⟩ := hT
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (S.image fun v => h v x)
  refine ⟨(b : 𝓞 K), nonZeroDivisors.coe_ne_zero b, ?_⟩
  have key : ∀ y : Fin d → K, h y ((b : 𝓞 K) • x) = algebraMap (𝓞 K) K (b : 𝓞 K) * h y x := by
    intro y
    rw [← algebraMap_smul K (b : 𝓞 K) x, map_smul, smul_eq_mul]
  unfold Formalism.HermitianLatticesTheory.dual Formalism.E.hdual
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨c, hc⟩ := hb (h v x) (Finset.mem_image_of_mem _ hv)
    rw [key, Submodule.mem_one]
    refine ⟨c, ?_⟩
    rw [hc, Algebra.smul_def]
  | zero => simp
  | add u w _ _ hu hw =>
    rw [map_add, LinearMap.add_apply]
    exact Submodule.add_mem _ hu hw
  | smul r u _ hu =>
    obtain ⟨r', hr'⟩ := star_int r
    rw [← algebraMap_smul K r u, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply]
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp hu
    rw [Submodule.mem_one]
    refine ⟨r' * c, ?_⟩
    rw [map_mul, hc]
    simp [hr']

end GlobalTheory.StarIntegralityLemmas
