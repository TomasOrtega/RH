import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RembApply
import Formalism.LatticeTheta.Statement
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨f, hf0, hle⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)`. Establish `hli` using `(linearIndependent_monoidHom F ℝ).comp (fun τ : F →+* ℝ => (τ : F →* ℝ)) (fun τ₁ τ₂ h => by`. Use extensionality with `a`. Conclude with `congrArg (fun g : F →* ℝ => g a) h)`.

Establish `hsum : ∀ a : F, ∑ τ : F →+* ℝ, f (EuclideanSpace.single τ 1) * τ a = 0`. Introduce `a`. Establish `h1 : f (remb F a) = 0` using `hle (Submodule.subset_span ⟨a, rfl⟩)`. Establish `h2 : remb F a = ∑ τ : F →+* ℝ, τ a • EuclideanSpace.single τ (1 : ℝ)`. Use extensionality with `σ`.

Simplify using `[EuclideanSpace.single_apply, Pi.single_apply]`. Rewrite `h1` using `[h2, map_sum]`. Simplify `h1` using `[mul_comm]`. Establish `hcoef` using `Fintype.linearIndependent_iff.mp hli (fun τ => f (EuclideanSpace.single τ 1)) (by`. Use function extensionality and compare the values at `a`.

Simplify `hsum a)` using `[Finset.sum_apply]`. Apply `hf0` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Establish `hx : x = ∑ τ : F →+* ℝ, x τ • EuclideanSpace.single τ (1 : ℝ)`.

Use extensionality with `σ`. Simplify using `[EuclideanSpace.single_apply, Pi.single_apply]`. Rewrite using `[hx, map_sum]`. Simplify using `[hcoef]`.
-/
theorem span_range_remb (F : Type) [Field F] [NumberField F] :
    Submodule.span ℝ (Set.range (remb F)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hli := (linearIndependent_monoidHom F ℝ).comp
    (fun τ : F →+* ℝ => (τ : F →* ℝ)) (fun τ₁ τ₂ h => by
      ext a; exact congrArg (fun g : F →* ℝ => g a) h)
  have hsum : ∀ a : F, ∑ τ : F →+* ℝ, f (EuclideanSpace.single τ 1) * τ a = 0 := by
    intro a
    have h1 : f (remb F a) = 0 := hle (Submodule.subset_span ⟨a, rfl⟩)
    have h2 : remb F a = ∑ τ : F →+* ℝ, τ a • EuclideanSpace.single τ (1 : ℝ) := by
      ext σ
      simp [EuclideanSpace.single_apply, Pi.single_apply]
    rw [h2, map_sum] at h1
    simpa [mul_comm] using h1
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun τ => f (EuclideanSpace.single τ 1))
    (by
      funext a
      simpa [Finset.sum_apply] using hsum a)
  apply hf0
  apply LinearMap.ext
  intro x
  have hx : x = ∑ τ : F →+* ℝ, x τ • EuclideanSpace.single τ (1 : ℝ) := by
    ext σ
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  rw [hx, map_sum]
  simp [hcoef]

end GlobalTheory.LipschitzTR

namespace GlobalTheory.LipschitzTR

/- English proof (translation)
Introduce `F _ _ _ N hN _`. Use `⟨?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← span_range_remb F, Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Establish `hc : ∃ c ∈ N, c ≠ 0`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hN` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[FractionalIdeal.mem_zero_iff]`.

Conclude with `⟨h x, fun hx => hx ▸ (N : Submodule (𝓞 F) F).zero_mem⟩`. Take `⟨c, hcN, hc0⟩` from `hc`. Take `⟨y, hy0, hint⟩` from `exists_integral_multiples ℤ ℚ (L := F) {a / c}`. Set `α : 𝓞 F` to `⟨y • (a / c), hint _ (Finset.mem_singleton_self _)⟩`. Establish `hmem : (y : F) * a ∈ N`.

Establish `h` using `Submodule.smul_mem (N : Submodule (𝓞 F) F) α hcN`. Establish `he : α • c = (y : F) * a`. Rewrite using `[Algebra.smul_def]`. Use `show (y • (a / c)) * c = (y : F) * a`. Rewrite using `[zsmul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Rewrite `h` using `[he]`. Conclude with `h`. Establish `hy : (y : ℝ) ≠ 0` using `by exact_mod_cast hy0`. Establish `heq : remb F a = (y : ℝ)⁻¹ • remb F ((y : F) * a)`.

Use extensionality with `τ`. Simplify using `only [remb_apply, PiLp.smul_apply, smul_eq_mul, map_mul, map_intCast]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[heq]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latOf N _).2 ⟨_, hmem, rfl⟩))`.
-/
theorem isZLattice_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)],
    IsZLattice ℝ (latOf N) := by
  intro F _ _ _ N hN _
  refine ⟨?_⟩
  rw [eq_top_iff, ← span_range_remb F, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hc : ∃ c ∈ N, c ≠ 0 := by
    by_contra h
    push_neg at h
    apply hN
    ext x
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h x, fun hx => hx ▸ (N : Submodule (𝓞 F) F).zero_mem⟩
  obtain ⟨c, hcN, hc0⟩ := hc
  obtain ⟨y, hy0, hint⟩ := exists_integral_multiples ℤ ℚ (L := F) {a / c}
  let α : 𝓞 F := ⟨y • (a / c), hint _ (Finset.mem_singleton_self _)⟩
  have hmem : (y : F) * a ∈ N := by
    have h := Submodule.smul_mem (N : Submodule (𝓞 F) F) α hcN
    have he : α • c = (y : F) * a := by
      rw [Algebra.smul_def]
      show (y • (a / c)) * c = (y : F) * a
      rw [zsmul_eq_mul]
      field_simp
    rw [he] at h
    exact h
  have hy : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
  have heq : remb F a = (y : ℝ)⁻¹ • remb F ((y : F) * a) := by
    ext τ
    simp only [remb_apply, PiLp.smul_apply, smul_eq_mul, map_mul, map_intCast]
    field_simp
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latOf N _).2 ⟨_, hmem, rfl⟩))

end GlobalTheory.LipschitzTR
