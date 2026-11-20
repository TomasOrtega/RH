import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntBTmulBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicTensorExistsRationalAddIntegralMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisIffExistsIntegralMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorLocalizedIntegersIdealInFieldStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

/- English proof (translation)
Introduce `L _ _ κ ℓ`. Take `⟨S₁, hS₁⟩` from `isIntB_mul_star_eventually L (RingHom.toOpposite (RingHom.id L) fun x y => mul_comm x y) κ ℓ`. Take `⟨S₂, hS₂⟩` from `GlobalTheory.T.adicIntegralTensorBasis_iff_exists_integral_multiple L κ ℓ`. Use `⟨S₁ ∪ S₂, fun v hv I h0 hadd hmul ⟨D, hD0, hDI, hIO⟩ => ?_⟩` and prove the remaining obligations. Establish `hv₁ : v ∉ S₁` using `fun h => hv (Finset.mem_union_left _ h)`.

Establish `hv₂ : v ∉ S₂` using `fun h => hv (Finset.mem_union_right _ h)`. Establish `hOmul` using `(hS₁ v hv₁).1`. Establish `hloc` using `hS₂ v hv₂`. Establish `hOadd : ∀ y z, IsIntB v ℓ y → IsIntB v ℓ z → IsIntB v ℓ (y + z)` using `fun y z hy hz i => by`. Rewrite using `[map_add, Finsupp.add_apply]`.

Conclude with `add_mem (hy i) (hz i)`. Establish `hone : (1 : ℤ) ∉ v.asIdeal` using `fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Establish `hloc1 : ∀ c : ℤ, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * (c : L))` using `fun c => ⟨1, hone, by rw [Int.cast_one, one_mul, ← eq_intCast (algebraMap ℤ L)]; exact isIntegral_algebraMap⟩`. Establish `hcast : ∀ c : ℤ, ((c : v.adicCompletion ℚ ⊗[ℚ] L)) = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (c : L)` using `fun c => by rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]`. Establish `hO : ∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c)` using `fun c hc => (hloc c).2 hc`.

Establish `htm : ∀ a b : L, ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b) = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (a * b)` using `fun a b => by`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Establish `hDL : (D : L) ≠ 0` using `Int.cast_ne_zero.2 hD0`. Set `K : Set L` to `{a | (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (a / D) ∈ I}`. Establish `hK0 : (0 : L) ∈ K` using `by show _ ∈ I; rw [zero_div, TensorProduct.tmul_zero]; exact h0`.

Establish `hKadd : ∀ a ∈ K, ∀ b ∈ K, a + b ∈ K` using `fun a ha b hb => by show _ ∈ I; rw [add_div, TensorProduct.tmul_add]; exact hadd _ ha _ hb`. Establish `hKmul : ∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K` using `fun c hc a ha => by show _ ∈ I; rw [mul_div_assoc, ← htm]; exact hmul _ (hO c hc) _ ha`. Establish `hKloc : ∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a)` using `fun a ha => by`. Apply `(hloc a).1` to reduce the goal to its premises. Use `hIO _ ha` as an intermediate fact.

Rewrite `this` using `[hcast, htm, mul_div_cancel₀ _ hDL]`. Then use the resulting hypothesis. Take `⟨g, hgK, hg⟩` from `GlobalTheory.T.exists_generator_localized_integers_ideal_in_field L v K hK0 hKadd hKmul hKloc`. Establish `hDK : (D : L) * D ∈ K` using `by show _ ∈ I`. Establish `h1` using `hDI _ (hO _ (hloc1 1))`. Rewrite `h1` using `[Int.cast_one, ← Algebra.TensorProduct.one_def, mul_one, hcast, ← mul_div_cancel_right₀ (D : L) hDL]`. Then use the resulting hypothesis.

Take `⟨c₀, hc₀, hc₀g⟩` from `hg _ hDK`. Establish `hg0 : g ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc₀g` using `[mul_zero]`. Conclude with `hDL (mul_self_eq_zero.1 hc₀g)`.

Establish `e1 : g / D * (D / g) = 1` using `by field_simp`. Establish `e1' : D / g * (g / D) = 1` using `by field_simp`. Set `m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ` to `{ val := (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (g / D), inv := (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (D / g), val_inv := by rw [htm, e1]; rfl inv_val := by rw [htm, e1']; rfl }`. Use `⟨m, fun x => ⟨fun hx => ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨y, ρ₁, hρ₁, rfl⟩` from `GlobalTheory.T.adicTensor_exists_rational_add_integral_mul L κ ℓ v x D hD0`.

Establish `hy : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y ∈ I`. Establish `h2 : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ((-1 : ℤ) : L) * ((D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ₁) ∈ I` using `hmul _ (hO _ (hloc1 _)) _ (hDI _ hρ₁)`. Use `hadd _ hx _ h2` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← hcast]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hyK : (D : L) * y ∈ K` using `by show _ ∈ I; rwa [mul_div_cancel_left₀ _ hDL]`. Take `⟨c, hc, hcg⟩` from `hg _ hyK`. Establish `e2 : g / D * c = y`.

Rewrite using `[div_mul_eq_mul_div, mul_comm g c, ← hcg, mul_div_cancel_left₀ _ hDL]`. Establish `e3 : g / D * c₀ = D`. Rewrite using `[div_mul_eq_mul_div, mul_comm g c₀, ← hc₀g, mul_div_cancel_left₀ _ hDL]`. Use `⟨(1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c + (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c₀ * ρ₁, hOadd _ _ (hO c hc) (hOmul _ _ (hO c₀ hc₀) hρ₁), ?_⟩` and prove the remaining obligations. Use `show _ = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (g / D) * _`.

Rewrite using `[mul_add, htm, ← mul_assoc, htm, e2, e3, hcast]`. Introduce and unpack `⟨ρ, hρ, rfl⟩`. Rewrite using `[mul_comm]`. Conclude with `hmul ρ hρ _ hgK`.
-/
theorem isIntB_lattice_principal_eventually : ∀ (L : Type) [Field L] [NumberField L] (κ : Type) (ℓ : Module.Basis κ ℚ L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ I : Set (v.adicCompletion ℚ ⊗[ℚ] L), 0 ∈ I →
      (∀ x ∈ I, ∀ y ∈ I, x + y ∈ I) → (∀ ρ, IsIntB v ℓ ρ → ∀ x ∈ I, ρ * x ∈ I) →
      (∃ D : ℤ, D ≠ 0 ∧ (∀ x, IsIntB v ℓ x → (D : v.adicCompletion ℚ ⊗[ℚ] L) * x ∈ I) ∧
        ∀ x ∈ I, IsIntB v ℓ ((D : v.adicCompletion ℚ ⊗[ℚ] L) * x)) →
      ∃ m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, ∀ x, x ∈ I ↔ ∃ ρ, IsIntB v ℓ ρ ∧ x = ↑m * ρ := by
  intro L _ _ κ ℓ
  obtain ⟨S₁, hS₁⟩ := isIntB_mul_star_eventually L
    (RingHom.toOpposite (RingHom.id L) fun x y => mul_comm x y) κ ℓ
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.adicIntegralTensorBasis_iff_exists_integral_multiple L κ ℓ
  refine ⟨S₁ ∪ S₂, fun v hv I h0 hadd hmul ⟨D, hD0, hDI, hIO⟩ => ?_⟩
  have hv₁ : v ∉ S₁ := fun h => hv (Finset.mem_union_left _ h)
  have hv₂ : v ∉ S₂ := fun h => hv (Finset.mem_union_right _ h)
  have hOmul := (hS₁ v hv₁).1
  have hloc := hS₂ v hv₂
  have hOadd : ∀ y z, IsIntB v ℓ y → IsIntB v ℓ z → IsIntB v ℓ (y + z) := fun y z hy hz i => by
    rw [map_add, Finsupp.add_apply]; exact add_mem (hy i) (hz i)
  have hone : (1 : ℤ) ∉ v.asIdeal := fun h => v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hloc1 : ∀ c : ℤ, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * (c : L)) := fun c =>
    ⟨1, hone, by rw [Int.cast_one, one_mul, ← eq_intCast (algebraMap ℤ L)]; exact isIntegral_algebraMap⟩
  have hcast : ∀ c : ℤ, ((c : v.adicCompletion ℚ ⊗[ℚ] L)) = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (c : L) :=
    fun c => by rw [← Algebra.TensorProduct.includeRight_apply, map_intCast]
  have hO : ∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) →
      IsIntB v ℓ ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c) := fun c hc => (hloc c).2 hc
  have htm : ∀ a b : L, ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] a) * ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] b) =
      (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (a * b) := fun a b => by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  have hDL : (D : L) ≠ 0 := Int.cast_ne_zero.2 hD0
  let K : Set L := {a | (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (a / D) ∈ I}
  have hK0 : (0 : L) ∈ K := by
    show _ ∈ I; rw [zero_div, TensorProduct.tmul_zero]; exact h0
  have hKadd : ∀ a ∈ K, ∀ b ∈ K, a + b ∈ K := fun a ha b hb => by
    show _ ∈ I; rw [add_div, TensorProduct.tmul_add]; exact hadd _ ha _ hb
  have hKmul : ∀ c : L, (∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * c)) → ∀ a ∈ K, c * a ∈ K :=
    fun c hc a ha => by
      show _ ∈ I; rw [mul_div_assoc, ← htm]; exact hmul _ (hO c hc) _ ha
  have hKloc : ∀ a ∈ K, ∃ s : ℤ, s ∉ v.asIdeal ∧ IsIntegral ℤ ((s : L) * a) := fun a ha => by
    apply (hloc a).1
    have := hIO _ ha
    rwa [hcast, htm, mul_div_cancel₀ _ hDL] at this
  obtain ⟨g, hgK, hg⟩ := GlobalTheory.T.exists_generator_localized_integers_ideal_in_field L v K hK0 hKadd hKmul hKloc
  have hDK : (D : L) * D ∈ K := by
    show _ ∈ I
    have h1 := hDI _ (hO _ (hloc1 1))
    rwa [Int.cast_one, ← Algebra.TensorProduct.one_def, mul_one, hcast,
      ← mul_div_cancel_right₀ (D : L) hDL] at h1
  obtain ⟨c₀, hc₀, hc₀g⟩ := hg _ hDK
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [mul_zero] at hc₀g; exact hDL (mul_self_eq_zero.1 hc₀g)
  have e1 : g / D * (D / g) = 1 := by field_simp
  have e1' : D / g * (g / D) = 1 := by field_simp
  let m : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ :=
    { val := (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (g / D), inv := (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (D / g),
      val_inv := by rw [htm, e1]; rfl
      inv_val := by rw [htm, e1']; rfl }
  refine ⟨m, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨y, ρ₁, hρ₁, rfl⟩ := GlobalTheory.T.adicTensor_exists_rational_add_integral_mul L κ ℓ v x D hD0
    have hy : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] y ∈ I := by
      have h2 : (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ((-1 : ℤ) : L) * ((D : v.adicCompletion ℚ ⊗[ℚ] L) * ρ₁) ∈ I :=
        hmul _ (hO _ (hloc1 _)) _ (hDI _ hρ₁)
      have := hadd _ hx _ h2
      convert this using 1
      rw [← hcast]; push_cast; ring
    have hyK : (D : L) * y ∈ K := by
      show _ ∈ I; rwa [mul_div_cancel_left₀ _ hDL]
    obtain ⟨c, hc, hcg⟩ := hg _ hyK
    have e2 : g / D * c = y := by
      rw [div_mul_eq_mul_div, mul_comm g c, ← hcg, mul_div_cancel_left₀ _ hDL]
    have e3 : g / D * c₀ = D := by
      rw [div_mul_eq_mul_div, mul_comm g c₀, ← hc₀g, mul_div_cancel_left₀ _ hDL]
    refine ⟨(1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c + (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] c₀ * ρ₁,
      hOadd _ _ (hO c hc) (hOmul _ _ (hO c₀ hc₀) hρ₁), ?_⟩
    show _ = (1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] (g / D) * _
    rw [mul_add, htm, ← mul_assoc, htm, e2, e3, hcast]
  · rintro ⟨ρ, hρ, rfl⟩
    rw [mul_comm]
    exact hmul ρ hρ _ hgK

end GlobalTheory.AdicSpan
