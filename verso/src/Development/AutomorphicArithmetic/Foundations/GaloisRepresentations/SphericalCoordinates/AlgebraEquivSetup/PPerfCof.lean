import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `E _ _ _ A`. Establish `hδ : A.δ ≠ 0`. Introduce `h`. Establish `h2` using `A.δ_sign A.τ₀ rfl`. Rewrite `h2` using `[h, map_zero, Complex.zero_im]`.

Conclude with `lt_irrefl _ h2`. Set `Ψ : E →ₗ[ℚ] Module.Dual ℚ E` to `((LinearMap.mul ℚ E).compr₂ (Algebra.trace ℚ E)) ∘ₗ LinearMap.mulLeft ℚ A.δ`. Establish `hΨ : ∀ x z, Ψ x z = Algebra.trace ℚ E (A.δ * x * z)` using `fun x z => rfl`. Establish `hinj : Function.Injective Ψ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `x hx`. Assume the negation of the conclusion as `hx0`. Establish `h1` using `LinearMap.congr_fun hx (A.δ * x)⁻¹`. Rewrite `h1` using `[hΨ, mul_inv_cancel₀ (mul_ne_zero hδ hx0), LinearMap.zero_apply, show (1 : E) = algebraMap ℚ E 1 from (map_one _).symm, Algebra.trace_algebraMap]`. Establish `hpos : 0 < Module.finrank ℚ E` using `Module.finrank_pos`.

Simplify using `at h1`. Use linear arithmetic over natural numbers and integers. Establish `hsurj : Function.Surjective Ψ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hinj`. Set `bQ` to `NumberField.integralBasis E`. Set `b` to `NumberField.RingOfIntegers.basis E`.

Use `choose ξ hξ using fun i => hsurj (bQ.coord i)`. Take `⟨y, hy0, hyint⟩` from `exists_integral_multiples ℤ ℚ (Finset.univ.image ξ)`. Establish `hint : ∀ i, ∃ w : 𝓞 E, algebraMap (𝓞 E) E w = y • ξ i` using `fun i => (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp (hyint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))`. Use `choose w hw using hint`. Set `η : _ → 𝓞 E` to `fun i => (y : 𝓞 E) * w i`.

Establish `hηc : ∀ i, algebraMap (𝓞 E) E (η i) = (y : E) * ((y : E) * ξ i)`. Introduce `i`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E ((y : 𝓞 E) * w i) = _`. Rewrite using `[map_mul, map_intCast, hw i, zsmul_eq_mul]`. Establish `hDz : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y` using `Int.natAbs_mul_self`.

Establish `hDpos : 0 < y.natAbs * y.natAbs` using `Nat.mul_pos (Int.natAbs_pos.mpr hy0) (Int.natAbs_pos.mpr hy0)`. Establish `key : ∀ i z, A.trd (η i * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * b.coord i z`. Introduce `i`. Establish `hlin : A.trd ∘ₗ LinearMap.mulLeft ℤ (η i) = ((y.natAbs * y.natAbs : ℕ) : ℤ) • b.coord i`. Use `b.ext fun j => ?_` and prove the remaining obligations.

Apply `Int.cast_injective (α := ℚ)` to reduce the goal to its premises. Establish `hb : bQ j = algebraMap (𝓞 E) E (b j)` using `NumberField.integralBasis_apply E j`. Establish `hc : (((η i * b j : 𝓞 E)) : E) = (y : E) * ((y : E) * ξ i) * bQ j`. Express the relevant statement in the definitionally equal form `algebraMap (𝓞 E) E (η i * b j) = _`. Rewrite using `[map_mul, hηc, hb]`.

Rewrite using `[LinearMap.comp_apply, LinearMap.mulLeft_apply, A.trd_spec, hc, LinearMap.smul_apply, smul_eq_mul, hDz, show A.δ * ((y : E) * ((y : E) * ξ i) * bQ j) = ((y * y : ℤ) : ℚ) • (A.δ * ξ i * bQ j) by`. Rewrite using `[Algebra.smul_def, map_intCast]`. Use `push_cast`. Use the proof step `ring,`. Use the proof step `map_smul, smul_eq_mul, ← hΨ, hξ]`.

Rewrite using `[Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self, Module.Basis.repr_self]`. Break down `eq_or_ne j i with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, h]`.

Introduce `z`. Conclude with `LinearMap.congr_fun hlin z`. Establish `hdual : ∀ f : 𝓞 E →ₗ[ℤ] ℤ, ∃ x : 𝓞 E, ∀ z, A.trd (x * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * f z`. Introduce `f`. Use `⟨∑ i, f (b i) • η i, fun z => ?_⟩` and prove the remaining obligations.

Use `conv_rhs => rw [← b.sum_dual_apply_smul_coord f]`. Rewrite using `[Finset.sum_mul, map_sum, LinearMap.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, key, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hc0 : A.c ≠ 0`. Introduce `h`. Conclude with `A.c_ne (by rw [h]; rfl)`. Establish `hN0 : 0 < Ideal.absNorm (Ideal.span {A.c})`. Use `Nat.pos_of_ne_zero ?_` and prove the remaining obligations.

Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hc0`. Take `⟨c', hc'⟩` from `Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {A.c}))`. Use `⟨y.natAbs * y.natAbs * Ideal.absNorm (Ideal.span {A.c}), Nat.mul_pos hDpos hN0, fun q hq => ⟨_, hq, fun f => ?_, ⟨c' * ((y.natAbs * y.natAbs : ℕ) : 𝓞 E), ?_⟩⟩⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hdual ((Ideal.absNorm (Ideal.span {A.c}) : ℤ) • f)`.

Use `⟨x, fun z => ?_⟩` and prove the remaining obligations. Rewrite using `[hx, LinearMap.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← mul_assoc, ← hc']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Gal.W2.Seed.pPerfCof :
    PerfCof := by
  intro E _ _ _ A
  classical
  have hδ : A.δ ≠ 0 := by
    intro h
    have h2 := A.δ_sign A.τ₀ rfl
    rw [h, map_zero, Complex.zero_im] at h2
    exact lt_irrefl _ h2
  let Ψ : E →ₗ[ℚ] Module.Dual ℚ E :=
    ((LinearMap.mul ℚ E).compr₂ (Algebra.trace ℚ E)) ∘ₗ LinearMap.mulLeft ℚ A.δ
  have hΨ : ∀ x z, Ψ x z = Algebra.trace ℚ E (A.δ * x * z) := fun x z => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have h1 := LinearMap.congr_fun hx (A.δ * x)⁻¹
    rw [hΨ, mul_inv_cancel₀ (mul_ne_zero hδ hx0), LinearMap.zero_apply,
      show (1 : E) = algebraMap ℚ E 1 from (map_one _).symm, Algebra.trace_algebraMap] at h1
    have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
    simp at h1
    omega
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hinj
  let bQ := NumberField.integralBasis E
  let b := NumberField.RingOfIntegers.basis E
  choose ξ hξ using fun i => hsurj (bQ.coord i)
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image ξ)
  have hint : ∀ i, ∃ w : 𝓞 E, algebraMap (𝓞 E) E w = y • ξ i := fun i =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp
      (hyint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  choose w hw using hint
  let η : _ → 𝓞 E := fun i => (y : 𝓞 E) * w i
  have hηc : ∀ i, algebraMap (𝓞 E) E (η i) = (y : E) * ((y : E) * ξ i) := by
    intro i
    change algebraMap (𝓞 E) E ((y : 𝓞 E) * w i) = _
    rw [map_mul, map_intCast, hw i, zsmul_eq_mul]
  have hDz : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
  have hDpos : 0 < y.natAbs * y.natAbs :=
    Nat.mul_pos (Int.natAbs_pos.mpr hy0) (Int.natAbs_pos.mpr hy0)
  have key : ∀ i z, A.trd (η i * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * b.coord i z := by
    intro i
    have hlin : A.trd ∘ₗ LinearMap.mulLeft ℤ (η i) = ((y.natAbs * y.natAbs : ℕ) : ℤ) • b.coord i := by
      refine b.ext fun j => ?_
      apply Int.cast_injective (α := ℚ)
      have hb : bQ j = algebraMap (𝓞 E) E (b j) := NumberField.integralBasis_apply E j
      have hc : (((η i * b j : 𝓞 E)) : E) = (y : E) * ((y : E) * ξ i) * bQ j := by
        change algebraMap (𝓞 E) E (η i * b j) = _
        rw [map_mul, hηc, hb]
      rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, A.trd_spec, hc, LinearMap.smul_apply,
        smul_eq_mul, hDz,
        show A.δ * ((y : E) * ((y : E) * ξ i) * bQ j) = ((y * y : ℤ) : ℚ) • (A.δ * ξ i * bQ j) by
          rw [Algebra.smul_def, map_intCast]
          push_cast
          ring,
        map_smul, smul_eq_mul, ← hΨ, hξ]
      rw [Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Module.Basis.repr_self]
      rcases eq_or_ne j i with h | h
      · subst h
        simp
      · simp [Finsupp.single_apply, h]
    intro z
    exact LinearMap.congr_fun hlin z
  have hdual : ∀ f : 𝓞 E →ₗ[ℤ] ℤ, ∃ x : 𝓞 E, ∀ z,
      A.trd (x * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * f z := by
    intro f
    refine ⟨∑ i, f (b i) • η i, fun z => ?_⟩
    conv_rhs => rw [← b.sum_dual_apply_smul_coord f]
    rw [Finset.sum_mul, map_sum, LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, key, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hc0 : A.c ≠ 0 := by
    intro h
    exact A.c_ne (by rw [h]; rfl)
  have hN0 : 0 < Ideal.absNorm (Ideal.span {A.c}) := by
    refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {A.c}))
  refine ⟨y.natAbs * y.natAbs * Ideal.absNorm (Ideal.span {A.c}), Nat.mul_pos hDpos hN0,
    fun q hq => ⟨_, hq, fun f => ?_, ⟨c' * ((y.natAbs * y.natAbs : ℕ) : 𝓞 E), ?_⟩⟩⟩
  · obtain ⟨x, hx⟩ := hdual ((Ideal.absNorm (Ideal.span {A.c}) : ℤ) • f)
    refine ⟨x, fun z => ?_⟩
    rw [hx, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  · rw [← mul_assoc, ← hc']
    push_cast
    ring
