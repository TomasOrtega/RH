import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentTraceSeparatingElement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootsOfUnityAndPValuation
open NumberField
open scoped Classical

namespace GlobalTheory.EigenDivide

/- English proof (translation)
Set `f : 𝓞 E →+* Module.End ℤ (Fin N → ℤ)` to `(Matrix.toLinAlgEquiv' (R := ℤ) (n := Fin N)).toRingEquiv.toRingHom.comp ρ`. Use `letI : Module (𝓞 E) (Fin N → ℤ) := Module.compHom _ f`. Establish `hsm : ∀ (a : 𝓞 E) (v : Fin N → ℤ), a • v = (ρ a).mulVec v` using `fun a v => by show f a v = _`. Simplify using `[f]`. Establish `hint : ∀ (n : ℤ) (v : Fin N → ℤ), (n : 𝓞 E) • v = n • v` using `fun n v => Int.cast_smul_eq_zsmul _ n v`.

Set `e : Fin N → Fin N → ℤ` to `fun j => Pi.single j 1`. Set `π : (Fin N → 𝓞 E) →ₗ[𝓞 E] (Fin N → ℤ)` to `Fintype.linearCombination (𝓞 E) e`. Establish `hπ : Function.Surjective π`. Introduce `v`. Use `⟨fun j => (v j : 𝓞 E), ?_⟩` and prove the remaining obligations.

Simplify using `only [π, Fintype.linearCombination_apply, hint]`. Use function extensionality and compare the values at `m`. Simplify using `[e, Finset.sum_apply, Pi.single_apply]`. Use `haveI : Module.Finite (𝓞 E) (Fin N → ℤ) := Module.Finite.of_surjective π hπ`. Use `haveI : Module.Flat (𝓞 E) (Fin N → ℤ) := by`.

Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce and unpack `v ⟨⟨a, ha⟩, hv⟩`. Establish `ha0 : a ≠ 0` using `nonZeroDivisors.ne_zero ha`. Establish `hv' : a • v = 0` using `hv`. Establish `hI : Ideal.span {a} ≠ ⊥` using `by simpa using ha0`.

Establish `hm` using `Ideal.absNorm_mem (Ideal.span {a})`. Establish `hn : Ideal.absNorm (Ideal.span {a}) ≠ 0` using `by rwa [Ne, Ideal.absNorm_eq_zero_iff]`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 hm`. Establish `h2 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 E) • v = 0`. Rewrite using `[← hb, mul_smul, hv', smul_zero]`.

Rewrite `h2` using `[Nat.cast_smul_eq_nsmul]`. Conclude with `(smul_eq_zero.1 h2).resolve_left hn`. Use `haveI : Module.FinitePresentation (𝓞 E) (Fin N → ℤ) := Module.finitePresentation_of_finite _ _`. Use `haveI : Module.Projective (𝓞 E) (Fin N → ℤ) := Module.Flat.projective_of_finitePresentation`. Take `⟨s, hs⟩` from `Module.projective_lifting_property π LinearMap.id hπ`.

Use `⟨fun j i => s (e i) j, fun i m => ?_, fun a j i => ?_⟩` and prove the remaining obligations. Establish `h` using `congrFun (LinearMap.congr_fun hs (e i)) m`. Simplify using `only [LinearMap.comp_apply, π, Fintype.linearCombination_apply, hsm, LinearMap.id_apply, Finset.sum_apply] at h`. Simplify `h` using `[e, Matrix.one_apply, Pi.single_apply]`. Establish `h1 : a • e i = ∑ i', ((ρ a i' i : ℤ) : 𝓞 E) • e i'`.

Rewrite using `[hsm]`. Simplify using `only [hint]`. Use function extensionality and compare the values at `m`. Simplify using `[e, Finset.sum_apply, Pi.single_apply]`. Establish `h2` using `congrFun (s.map_smul a (e i)) j`.

Rewrite `h2` using `[h1, map_sum]`. Simplify `h2` using `[Finset.sum_apply]`.
-/
theorem exists_dual_coeff {E : Type} [Field E] [NumberField E] {N : ℕ}
    (ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ) :
    ∃ l : Fin N → Fin N → 𝓞 E,
      (∀ i m, ∑ j, ρ (l j i) m j = (1 : Matrix (Fin N) (Fin N) ℤ) m i) ∧
      ∀ a j i, ∑ i', ((ρ a i' i : ℤ) : 𝓞 E) * l j i' = a * l j i := by
  let f : 𝓞 E →+* Module.End ℤ (Fin N → ℤ) :=
    (Matrix.toLinAlgEquiv' (R := ℤ) (n := Fin N)).toRingEquiv.toRingHom.comp ρ
  letI : Module (𝓞 E) (Fin N → ℤ) := Module.compHom _ f
  have hsm : ∀ (a : 𝓞 E) (v : Fin N → ℤ), a • v = (ρ a).mulVec v := fun a v => by
    show f a v = _
    simp [f]
  have hint : ∀ (n : ℤ) (v : Fin N → ℤ), (n : 𝓞 E) • v = n • v := fun n v =>
    Int.cast_smul_eq_zsmul _ n v
  let e : Fin N → Fin N → ℤ := fun j => Pi.single j 1
  let π : (Fin N → 𝓞 E) →ₗ[𝓞 E] (Fin N → ℤ) := Fintype.linearCombination (𝓞 E) e
  have hπ : Function.Surjective π := by
    intro v
    refine ⟨fun j => (v j : 𝓞 E), ?_⟩
    simp only [π, Fintype.linearCombination_apply, hint]
    funext m
    simp [e, Finset.sum_apply, Pi.single_apply]
  haveI : Module.Finite (𝓞 E) (Fin N → ℤ) := Module.Finite.of_surjective π hπ
  haveI : Module.Flat (𝓞 E) (Fin N → ℤ) := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro v ⟨⟨a, ha⟩, hv⟩
    have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
    have hv' : a • v = 0 := hv
    have hI : Ideal.span {a} ≠ ⊥ := by simpa using ha0
    have hm := Ideal.absNorm_mem (Ideal.span {a})
    have hn : Ideal.absNorm (Ideal.span {a}) ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 hm
    have h2 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 E) • v = 0 := by
      rw [← hb, mul_smul, hv', smul_zero]
    rw [Nat.cast_smul_eq_nsmul] at h2
    exact (smul_eq_zero.1 h2).resolve_left hn
  haveI : Module.FinitePresentation (𝓞 E) (Fin N → ℤ) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (Fin N → ℤ) := Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨fun j i => s (e i) j, fun i m => ?_, fun a j i => ?_⟩
  · have h := congrFun (LinearMap.congr_fun hs (e i)) m
    simp only [LinearMap.comp_apply, π, Fintype.linearCombination_apply, hsm, LinearMap.id_apply,
      Finset.sum_apply] at h
    simpa [e, Matrix.one_apply, Pi.single_apply] using h
  · have h1 : a • e i = ∑ i', ((ρ a i' i : ℤ) : 𝓞 E) • e i' := by
      rw [hsm]
      simp only [hint]
      funext m
      simp [e, Finset.sum_apply, Pi.single_apply]
    have h2 := congrFun (s.map_smul a (e i)) j
    rw [h1, map_sum] at h2
    simpa [Finset.sum_apply] using h2

/- English proof (translation)
Introduce `E _ _ _ F _ _ R N ρ τ y hy hρ r hr`. Take `⟨l, hl1, hl2⟩` from `exists_dual_coeff ρ`. Set `S : Fin N → (E ≃ₐ[ℚ] E) → F` to `fun j g => ∑ i, y i * τ (g (l j i : E))`. Establish `hS : ∀ j g (a : 𝓞 E), τ (g (a : E)) * S j g = τ (a : E) * S j g`. Introduce `j g a`.

Establish `e1 : ∀ i, τ (g (a : E)) * (y i * τ (g (l j i : E))) = ∑ i', ((ρ a i' i : ℤ) : F) * y i * τ (g (l j i' : E))`. Introduce `i`. Establish `h` using `congrArg (fun x : 𝓞 E => τ (g (algebraMap (𝓞 E) E x))) (hl2 a j i)`. Simplify using `only [map_sum, map_mul, map_intCast] at h`. Rewrite using `[mul_left_comm]`.

Use `erw [← h]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, mul_assoc]`. Simplify using `only [S, Finset.mul_sum, e1]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Establish `h` using `congrFun (hρ a) i'`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, eq_intCast, Pi.smul_apply, smul_eq_mul] at h`. Rewrite using `[← Finset.sum_mul, h, mul_assoc]`.

Establish `hS0 : ∀ j g, g ≠ 1 → S j g = 0`. Introduce `j g hg`. Assume the negation of the conclusion as `h0`. Apply `hg` to reduce the goal to its premises. Establish `h1 : ∀ a : 𝓞 E, g (a : E) = a` using `fun a => τ.injective (mul_right_cancel₀ h0 (hS j g a))`.

Use extensionality with `x`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Rewrite using `[map_div₀]`. Use `erw [h1 a, h1 b]`. Both sides reduce to the same expression.

Establish `hmem : ∀ j k, τ ((integralBasis E).traceDual k) * S j 1 ∈ R`. Introduce `j k`. Establish `e1 : τ ((integralBasis E).traceDual k) * S j 1 = ∑ g : E ≃ₐ[ℚ] E, τ (g ((integralBasis E).traceDual k)) * S j g`. Rewrite using `[Finset.sum_eq_single 1]`. Both sides reduce to the same expression.

Introduce `g _ hg`. Rewrite using `[hS0 j g hg, mul_zero]`. Simplify using the standard rewrite rules. Establish `e2 : ∀ (g : E ≃ₐ[ℚ] E) i, τ (g ((integralBasis E).traceDual k)) * (y i * τ (g (l j i : E))) = y i * τ (g ((l j i : E) * (integralBasis E).traceDual k))`. Introduce `g i`.

Rewrite using `[map_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1]`. Simplify using `only [S, Finset.mul_sum, e2]`. Rewrite using `[Finset.sum_comm]`.

Use `R.sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, GlobalTheory.InvDifferentArith.sum_aut_eq_trace, GlobalTheory.InvDifferentArith.trace_mul_traceDual, map_intCast]`. Conclude with `R.mul_mem (hy i) (intCast_mem R _)`. Use `⟨fun j => (∑ k, r k * τ ((integralBasis E).traceDual k)) * S j 1, fun j => ?_, fun P hP => ?_⟩` and prove the remaining obligations. Use `beta_reduce`.

Rewrite using `[Finset.sum_mul]`. Use `R.sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `R.mul_mem (hr k) (hmem j k)`. Establish `key : P.mulVec (fun j => S j 1) = P.mulVec y`.

Use function extensionality and compare the values at `m`. Establish `e1 : ∀ i, P m i = ∑ j, τ (l j i : E) * P m j`. Introduce `i`. Establish `e2 : ∀ j, τ (l j i : E) * P m j = ∑ n, P m n * ((ρ (l j i) n j : ℤ) : F)`. Introduce `j`.

Establish `h` using `congrFun (congrFun (hP (l j i)) m) j`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, eq_intCast, Matrix.smul_apply, smul_eq_mul] at h`. Conclude with `h.symm`. Simplify using `only [e2]`. Rewrite using `[Finset.sum_comm]`.

Simplify using `only [← Finset.mul_sum, ← Int.cast_sum, hl1]`. Simplify using `[Matrix.one_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, S, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[e1 i, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[AlgEquiv.one_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← key, ← Matrix.mulVec_smul]`.

Both sides reduce to the same expression.
-/
theorem exists_projection_eq : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (F : Type) [Field F] [CharZero F] (R : Subring F)
    (N : ℕ) (ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ) (τ : E →+* F) (y : Fin N → F), (∀ i, y i ∈ R) →
    (∀ a : 𝓞 E, ((ρ a).map (Int.castRingHom F)).mulVec y = τ (a : E) • y) →
    ∀ r : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → F, (∀ k, r k ∈ R) →
    ∃ z : Fin N → F, (∀ i, z i ∈ R) ∧ ∀ P : Matrix (Fin N) (Fin N) F,
      (∀ a : 𝓞 E, P * (ρ a).map (Int.castRingHom F) = τ (a : E) • P) →
      P.mulVec z = (∑ k, r k * τ ((integralBasis E).traceDual k)) • P.mulVec y := by
  intro E _ _ _ F _ _ R N ρ τ y hy hρ r hr
  obtain ⟨l, hl1, hl2⟩ := exists_dual_coeff ρ
  let S : Fin N → (E ≃ₐ[ℚ] E) → F := fun j g => ∑ i, y i * τ (g (l j i : E))
  have hS : ∀ j g (a : 𝓞 E), τ (g (a : E)) * S j g = τ (a : E) * S j g := by
    intro j g a
    have e1 : ∀ i, τ (g (a : E)) * (y i * τ (g (l j i : E))) =
        ∑ i', ((ρ a i' i : ℤ) : F) * y i * τ (g (l j i' : E)) := by
      intro i
      have h := congrArg (fun x : 𝓞 E => τ (g (algebraMap (𝓞 E) E x))) (hl2 a j i)
      simp only [map_sum, map_mul, map_intCast] at h
      rw [mul_left_comm]
      erw [← h]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [mul_left_comm, mul_assoc]
    simp only [S, Finset.mul_sum, e1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i' _ => ?_
    have h := congrFun (hρ a) i'
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, eq_intCast, Pi.smul_apply,
      smul_eq_mul] at h
    rw [← Finset.sum_mul, h, mul_assoc]
  have hS0 : ∀ j g, g ≠ 1 → S j g = 0 := by
    intro j g hg
    by_contra h0
    apply hg
    have h1 : ∀ a : 𝓞 E, g (a : E) = a := fun a =>
      τ.injective (mul_right_cancel₀ h0 (hS j g a))
    ext x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀]
    erw [h1 a, h1 b]
    rfl
  have hmem : ∀ j k, τ ((integralBasis E).traceDual k) * S j 1 ∈ R := by
    intro j k
    have e1 : τ ((integralBasis E).traceDual k) * S j 1 =
        ∑ g : E ≃ₐ[ℚ] E, τ (g ((integralBasis E).traceDual k)) * S j g := by
      rw [Finset.sum_eq_single 1]
      · rfl
      · intro g _ hg
        rw [hS0 j g hg, mul_zero]
      · simp
    have e2 : ∀ (g : E ≃ₐ[ℚ] E) i, τ (g ((integralBasis E).traceDual k)) * (y i * τ (g (l j i : E))) =
        y i * τ (g ((l j i : E) * (integralBasis E).traceDual k)) := by
      intro g i
      rw [map_mul, map_mul]; ring
    rw [e1]
    simp only [S, Finset.mul_sum, e2]
    rw [Finset.sum_comm]
    refine R.sum_mem fun i _ => ?_
    rw [← Finset.mul_sum, GlobalTheory.InvDifferentArith.sum_aut_eq_trace,
      GlobalTheory.InvDifferentArith.trace_mul_traceDual, map_intCast]
    exact R.mul_mem (hy i) (intCast_mem R _)
  refine ⟨fun j => (∑ k, r k * τ ((integralBasis E).traceDual k)) * S j 1, fun j => ?_, fun P hP => ?_⟩
  · beta_reduce
    rw [Finset.sum_mul]
    refine R.sum_mem fun k _ => ?_
    rw [mul_assoc]
    exact R.mul_mem (hr k) (hmem j k)
  · have key : P.mulVec (fun j => S j 1) = P.mulVec y := by
      funext m
      have e1 : ∀ i, P m i = ∑ j, τ (l j i : E) * P m j := by
        intro i
        have e2 : ∀ j, τ (l j i : E) * P m j = ∑ n, P m n * ((ρ (l j i) n j : ℤ) : F) := by
          intro j
          have h := congrFun (congrFun (hP (l j i)) m) j
          simp only [Matrix.mul_apply, Matrix.map_apply, eq_intCast, Matrix.smul_apply,
            smul_eq_mul] at h
          exact h.symm
        simp only [e2]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, ← Int.cast_sum, hl1]
        simp [Matrix.one_apply]
      simp only [Matrix.mulVec, dotProduct, S, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [e1 i, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [AlgEquiv.one_apply]; ring
    rw [← key, ← Matrix.mulVec_smul]
    rfl

end GlobalTheory.EigenDivide
