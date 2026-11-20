import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use `haveI := D.freeO`. Use `haveI := D.finO`. Use `haveI : Nontrivial D.O := by`. Apply `Module.nontrivial_of_finrank_pos (R := ℤ)` to reduce the goal to its premises. Rewrite using `[D.rankO, hm]`.

Simplify using `using Module.finrank_pos (R := ℚ) (M := D.F)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `ha0`. Establish `hF : (a : D.F) ≠ 0` using `by exact_mod_cast ha0`.

Take `⟨y, hy0, hyint⟩` from `IsAlgebraic.exists_integral_multiple (a.2.isAlgebraic.inv)`. Use `set b : 𝓞 D.F := ⟨_, hyint⟩`. Establish `hab : a * b = (y : 𝓞 D.F)`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises. Simplify using `only [map_mul, map_intCast]`.

Use `show (a : D.F) * ((y : ℤ) • (a : D.F)⁻¹) = _`. Rewrite using `[zsmul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Establish `h1 : algebraMap (𝓞 D.F) D.O (y : 𝓞 D.F) = 0` using `by rw [← hab, map_mul, ha, zero_mul]`. Rewrite `h1` using `[map_intCast]`.

Establish `: (y : ℤ) • (1 : D.O) = 0` using `by rw [zsmul_eq_mul, _root_.mul_one, h1]`. Break down `smul_eq_zero.mp this with h | h` into its components or cases. Conclude with `hy0 h`. Conclude with `one_ne_zero h`.
-/
theorem Datum.algebraMap_injective (D : Datum p) (hm : D.m = 1) :
    Function.Injective (algebraMap (𝓞 D.F) D.O) := by
  haveI := D.freeO
  haveI := D.finO
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]; simpa using Module.finrank_pos (R := ℚ) (M := D.F)
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra ha0
  have hF : (a : D.F) ≠ 0 := by exact_mod_cast ha0
  obtain ⟨y, hy0, hyint⟩ := IsAlgebraic.exists_integral_multiple
    (a.2.isAlgebraic.inv)
  set b : 𝓞 D.F := ⟨_, hyint⟩
  have hab : a * b = (y : 𝓞 D.F) := by
    apply RingOfIntegers.coe_injective
    simp only [map_mul, map_intCast]
    show (a : D.F) * ((y : ℤ) • (a : D.F)⁻¹) = _
    rw [zsmul_eq_mul]
    field_simp
  have h1 : algebraMap (𝓞 D.F) D.O (y : 𝓞 D.F) = 0 := by rw [← hab, map_mul, ha, zero_mul]
  rw [map_intCast] at h1
  have : (y : ℤ) • (1 : D.O) = 0 := by rw [zsmul_eq_mul, _root_.mul_one, h1]
  rcases smul_eq_zero.mp this with h | h
  · exact hy0 h
  · exact one_ne_zero h

/- English proof (translation)
Use `haveI := D.freeO`. Use `haveI := D.finO`. Set `f : 𝓞 D.F →ₗ[ℤ] D.O` to `(algebraMap (𝓞 D.F) D.O).toAddMonoidHom.toIntLinearMap`. Establish `hf : Function.Injective f` using `D.algebraMap_injective hm`. Set `M` to `LinearMap.range f`.

Establish `h1` using `rank_quotient_add_rank_of_isDomain M`. Rewrite `h1` using `[rank_range_of_injective f hf, ← Module.finrank_eq_rank (R := ℤ) (M := 𝓞 D.F), ← Module.finrank_eq_rank (R := ℤ) (M := D.O), RingOfIntegers.rank, D.rankO, hm, one_pow, _root_.one_mul]`. Take `⟨k, hk⟩` from `Cardinal.lt_aleph0.mp (Module.rank_lt_aleph0 (R := ℤ) (M := D.O ⧸ M))`. Rewrite `h1` using `[hk]`. Normalize the coercions in `at h1`.

Establish `h0 : Module.rank ℤ (D.O ⧸ M) = 0` using `by rw [hk]; norm_cast; omega`. Take `⟨e, he, hex⟩` from `(rank_eq_zero_iff.mp h0) (Submodule.Quotient.mk x)`. Rewrite `hex` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Take `⟨a, ha⟩` from `hex`. Conclude with `⟨e, he, a, ha.symm⟩`.
-/
theorem Datum.exists_zsmul_eq_algebraMap (D : Datum p) (hm : D.m = 1) (x : D.O) :
    ∃ e : ℤ, e ≠ 0 ∧ ∃ a : 𝓞 D.F, e • x = algebraMap (𝓞 D.F) D.O a := by
  haveI := D.freeO
  haveI := D.finO
  let f : 𝓞 D.F →ₗ[ℤ] D.O := (algebraMap (𝓞 D.F) D.O).toAddMonoidHom.toIntLinearMap
  have hf : Function.Injective f := D.algebraMap_injective hm
  let M := LinearMap.range f
  have h1 := rank_quotient_add_rank_of_isDomain M
  rw [rank_range_of_injective f hf, ← Module.finrank_eq_rank (R := ℤ) (M := 𝓞 D.F),
    ← Module.finrank_eq_rank (R := ℤ) (M := D.O), RingOfIntegers.rank, D.rankO, hm, one_pow,
    _root_.one_mul] at h1
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.mp (Module.rank_lt_aleph0 (R := ℤ) (M := D.O ⧸ M))
  rw [hk] at h1
  norm_cast at h1
  have h0 : Module.rank ℤ (D.O ⧸ M) = 0 := by rw [hk]; norm_cast; omega
  obtain ⟨e, he, hex⟩ := (rank_eq_zero_iff.mp h0) (Submodule.Quotient.mk x)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hex
  obtain ⟨a, ha⟩ := hex
  exact ⟨e, he, a, ha.symm⟩

/- English proof (translation)
Introduce `p _ D hm x`. Use `haveI := D.freeO`. Use `haveI := D.finO`. Take `⟨e, he, a, ha⟩` from `D.exists_zsmul_eq_algebraMap hm x`. Use `haveI : Algebra.IsIntegral ℤ D.O := Algebra.IsIntegral.of_finite ℤ D.O`.

Take `⟨P, hPm, hP⟩` from `Algebra.IsIntegral.isIntegral (R := ℤ) x`. Establish `h1 : Polynomial.aeval (algebraMap ℤ D.O e * x) (P.scaleRoots e) = 0` using `Polynomial.scaleRoots_aeval_eq_zero (by rwa [Polynomial.aeval_def])`. Rewrite `h1` using `[← Algebra.smul_def, ha, Polynomial.aeval_algebraMap_apply]`. Establish `h2 : Polynomial.aeval a (P.scaleRoots e) = 0` using `D.algebraMap_injective hm (by rw [h1, map_zero])`. Establish `he' : (e : D.F) ≠ 0` using `by exact_mod_cast he`.

Establish `h4 : Polynomial.aeval (a : D.F) (P.scaleRoots e) = 0`. Use `congrArg (algebraMap (𝓞 D.F) D.F) h2` as an intermediate fact. Rewrite `this` using `[← Polynomial.aeval_algebraMap_apply, map_zero]`. Then use the resulting hypothesis. Establish `h3 : Polynomial.eval₂ (algebraMap ℤ D.F) ((a : D.F) / e) P = 0`. Use `Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ D.F) ((a : D.F) / e) e` as an intermediate fact.

Rewrite using `[show algebraMap ℤ D.F e * ((a : D.F) / e) = (a : D.F) by`. Rewrite using `[algebraMap_int_eq, eq_intCast]`. Use the proof step `field_simp] at this`. Rewrite `this` using `[← Polynomial.aeval_def, h4]`. Conclude with `(mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ (by simpa using he'))`.

Establish `hint : IsIntegral ℤ ((a : D.F) / e)` using `⟨P, hPm, h3⟩`. Take `⟨a', ha'⟩ : ∃ a' : 𝓞 D.F, (a' : D.F) = (a : D.F) / e` from `⟨⟨_, hint⟩, rfl⟩`. Use `⟨a', ?_⟩` and prove the remaining obligations. Establish `hae : a = e • a'`. Apply `RingOfIntegers.coe_injective` to reduce the goal to its premises.

Rewrite using `[zsmul_eq_mul, map_mul, map_intCast]`. Express the relevant statement in the definitionally equal form `(a : D.F) = (e : D.F) * (a' : D.F)`. Rewrite using `[ha']`. Clear the denominators using the available nonvanishing facts. Apply `smul_right_injective D.O he` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `e • algebraMap (𝓞 D.F) D.O a' = e • x`. Rewrite using `[ha, ← map_zsmul, ← hae]`.
-/
theorem Datum.algebraMap_surjective_of_m_eq_one :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), D.m = 1 → Function.Surjective (algebraMap (𝓞 D.F) D.O) := by
  intro p _ D hm x
  haveI := D.freeO
  haveI := D.finO
  obtain ⟨e, he, a, ha⟩ := D.exists_zsmul_eq_algebraMap hm x
  haveI : Algebra.IsIntegral ℤ D.O := Algebra.IsIntegral.of_finite ℤ D.O
  obtain ⟨P, hPm, hP⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) x
  have h1 : Polynomial.aeval (algebraMap ℤ D.O e * x) (P.scaleRoots e) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero (by rwa [Polynomial.aeval_def])
  rw [← Algebra.smul_def, ha, Polynomial.aeval_algebraMap_apply] at h1
  have h2 : Polynomial.aeval a (P.scaleRoots e) = 0 :=
    D.algebraMap_injective hm (by rw [h1, map_zero])
  have he' : (e : D.F) ≠ 0 := by exact_mod_cast he
  have h4 : Polynomial.aeval (a : D.F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 D.F) D.F) h2
    rwa [← Polynomial.aeval_algebraMap_apply, map_zero] at this
  have h3 : Polynomial.eval₂ (algebraMap ℤ D.F) ((a : D.F) / e) P = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := P) (algebraMap ℤ D.F) ((a : D.F) / e) e
    rw [show algebraMap ℤ D.F e * ((a : D.F) / e) = (a : D.F) by
      rw [algebraMap_int_eq, eq_intCast]; field_simp] at this
    rw [← Polynomial.aeval_def, h4] at this
    exact (mul_eq_zero.mp this.symm).resolve_left (pow_ne_zero _ (by simpa using he'))
  have hint : IsIntegral ℤ ((a : D.F) / e) := ⟨P, hPm, h3⟩
  obtain ⟨a', ha'⟩ : ∃ a' : 𝓞 D.F, (a' : D.F) = (a : D.F) / e := ⟨⟨_, hint⟩, rfl⟩
  refine ⟨a', ?_⟩
  have hae : a = e • a' := by
    apply RingOfIntegers.coe_injective
    rw [zsmul_eq_mul, map_mul, map_intCast]
    change (a : D.F) = (e : D.F) * (a' : D.F)
    rw [ha']
    field_simp
  apply smul_right_injective D.O he
  change e • algebraMap (𝓞 D.F) D.O a' = e • x
  rw [ha, ← map_zsmul, ← hae]

end GlobalTheory.UPel.HT
