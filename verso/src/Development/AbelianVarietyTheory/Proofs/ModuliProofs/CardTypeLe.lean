import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SymSignature

/- English proof (translation)
The claim follows from `Finite.of_injective (fun τ : 𝓞 E →+* K => τ.toIntAlgHom) RingHom.toIntAlgHom_injective`.
-/
theorem finite_hom (E : Type) [Field E] [NumberField E] (K : Type) [Field K] :
    Finite (𝓞 E →+* K) :=
  Finite.of_injective (fun τ : 𝓞 E →+* K => τ.toIntAlgHom) RingHom.toIntAlgHom_injective

/- English proof (translation)
Rewrite using `[← RingOfIntegers.rank E]`. Conclude with `(Nat.card_le_card_of_injective (fun τ : 𝓞 E →+* K => τ.toIntAlgHom) RingHom.toIntAlgHom_injective).trans (card_algHom_le_finrank ℤ (𝓞 E) K)`.
-/
theorem card_hom_le (E : Type) [Field E] [NumberField E] (K : Type) [Field K] :
    Nat.card (𝓞 E →+* K) ≤ Module.finrank ℚ E := by
  rw [← RingOfIntegers.rank E]
  exact (Nat.card_le_card_of_injective (fun τ : 𝓞 E →+* K => τ.toIntAlgHom)
    RingHom.toIntAlgHom_injective).trans (card_algHom_le_finrank ℤ (𝓞 E) K)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `h`. Establish `h0 : ρ = 0` using `by linear_combination (-1 / 2 : K) * h`. Rewrite `hρ` using `[h0]`. Establish `: (H.d : K) = 0` using `by linear_combination hρ`. Conclude with `H.d_prime.ne_zero (by exact_mod_cast this)`.
-/
theorem root_ne_neg (H : Host E) {K : Type} [Field K] [CharZero K] {ρ : K}
    (hρ : ρ ^ 2 = -(H.d : K)) : -ρ ≠ ρ := by
  intro h
  have h0 : ρ = 0 := by linear_combination (-1 / 2 : K) * h
  rw [h0] at hρ
  have : (H.d : K) = 0 := by linear_combination hρ
  exact H.d_prime.ne_zero (by exact_mod_cast this)

/- English proof (translation)
Use `congrArg τ H.rt_sq` as an intermediate fact. Rewrite `this` using `[map_pow, map_neg, map_natCast, ← hρ]`. Conclude with `sq_eq_sq_iff_eq_or_eq_neg.mp this`.
-/
theorem map_rt (H : Host E) {K : Type} [Field K] {ρ : K} (hρ : ρ ^ 2 = -(H.d : K))
    (τ : 𝓞 E →+* K) : τ H.rt = ρ ∨ τ H.rt = -ρ := by
  have := congrArg τ H.rt_sq
  rw [map_pow, map_neg, map_natCast, ← hρ] at this
  exact sq_eq_sq_iff_eq_or_eq_neg.mp this

/- English proof (translation)
Use `haveI := finite_hom E K`. Establish `hne` using `root_ne_neg H hρ`. Set `f : {τ : 𝓞 E →+* K // τ H.rt = ρ} ⊕ {τ : 𝓞 E →+* K // τ H.rt = ρ} → (𝓞 E →+* K)` to `Sum.elim (fun τ => τ.1) (fun τ => τ.1.comp (H.bar : 𝓞 E →+* 𝓞 E))`. Establish `hf : Function.Injective f`. Introduce and unpack `(a | a) (b | b) h`.

Conclude with `congrArg Sum.inl (Subtype.ext h)`. It suffices to derive a contradiction. Use `RingHom.congr_fun h H.rt` as an intermediate fact. Simplify using `[f, HostModel.bar_rt, a.2, b.2] at this`. Conclude with `hne this.symm`.

It suffices to derive a contradiction. Use `RingHom.congr_fun h H.rt` as an intermediate fact. Simplify using `[f, HostModel.bar_rt, a.2, b.2] at this`. Conclude with `hne this`. Use `congrArg Sum.inr (Subtype.ext (RingHom.ext fun x => ?_))` and prove the remaining obligations.

Use `RingHom.congr_fun h (H.bar x)` as an intermediate fact. Simplify `this` using `[f, HostModel.bar_bar]`. Establish `h1` using `(Nat.card_le_card_of_injective f hf).trans (card_hom_le E K)`. Rewrite `h1` using `[Nat.card_sum]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_type_le (H : Host E) {K : Type} [Field K] [CharZero K] {ρ : K}
    (hρ : ρ ^ 2 = -(H.d : K)) :
    Nat.card {τ : 𝓞 E →+* K // τ H.rt = ρ} ≤ Module.finrank ℚ E / 2 := by
  haveI := finite_hom E K
  have hne := root_ne_neg H hρ
  let f : {τ : 𝓞 E →+* K // τ H.rt = ρ} ⊕ {τ : 𝓞 E →+* K // τ H.rt = ρ} → (𝓞 E →+* K) :=
    Sum.elim (fun τ => τ.1) (fun τ => τ.1.comp (H.bar : 𝓞 E →+* 𝓞 E))
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exfalso
      have := RingHom.congr_fun h H.rt
      simp [f, HostModel.bar_rt, a.2, b.2] at this
      exact hne this.symm
    · exfalso
      have := RingHom.congr_fun h H.rt
      simp [f, HostModel.bar_rt, a.2, b.2] at this
      exact hne this
    · refine congrArg Sum.inr (Subtype.ext (RingHom.ext fun x => ?_))
      have := RingHom.congr_fun h (H.bar x)
      simpa [f, HostModel.bar_bar] using this
  have h1 := (Nat.card_le_card_of_injective f hf).trans (card_hom_le E K)
  rw [Nat.card_sum] at h1
  omega

/- English proof (translation)
Introduce `E _ _ _ H p q g K _ _ ρ ty V hρ hty hV`. Use `haveI := finite_hom E K`. Establish `hne` using `root_ne_neg H hρ`. Set `S : Type` to `Σ τ : {τ : 𝓞 E →+* K // τ H.rt = ρ}, {i // ty i = τ.1} × {j // ty j = τ.1.comp (H.bar : 𝓞 E →+* 𝓞 E)}`. Use `haveI : Fintype S := Fintype.ofFinite S`.

Use `haveI : Fintype {τ : 𝓞 E →+* K // τ H.rt = ρ} := Fintype.ofFinite _`. Establish `hS : Nat.card S = Nat.card {τ : 𝓞 E →+* K // τ H.rt = ρ} * p * q`. Rewrite using `[Nat.card_sigma, Finset.sum_congr rfl (g := fun _ => p * q)]`. Rewrite using `[Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, Nat.mul_assoc]`. Introduce `τ _`.

Rewrite using `[Nat.card_prod, (hty τ.1).1 τ.2, (hty _).2]`. Simplify `hne` using `[HostModel.bar_rt, τ.2]`. Set `f : V →ₗ[K] (S → K)` to `{ toFun := fun Θ s => Θ.1 s.2.1.1 s.2.2.1 map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hf : Function.Injective f`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `Θ h0`. Take `⟨hs, hc⟩` from `hV Θ.1 Θ.2`. Establish `key : ∀ i j, ty i H.rt = ρ → Θ.1 i j = 0`. Introduce `i j hi`. Assume the negation of the conclusion as `hij`.

Use `hij (congrFun h0 ⟨⟨ty i, hi⟩, ⟨i, rfl⟩, ⟨j, RingHom.ext fun a => ?_⟩⟩)` and prove the remaining obligations. Use `congrFun (congrFun (hc (H.bar a)) i) j` as an intermediate fact. Rewrite `this` using `[Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal, HostModel.bar_bar, mul_comm]`. Conclude with `(mul_left_cancel₀ hij this).symm`. Use `Subtype.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations.

Use `show Θ.1 i j = 0`. Break down `map_rt H hρ (ty i) with hi | hi` into its components or cases. Conclude with `key i j hi`. Assume the negation of the conclusion as `hij`. Use `congrFun (congrFun (hc H.rt) i) j` as an intermediate fact.

Rewrite `this` using `[Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal, HostModel.bar_rt, mul_comm, map_neg, hi]`. Establish `hj : ty j H.rt = ρ` using `(neg_injective (mul_left_cancel₀ hij this)).symm`. Conclude with `hij ((hs.apply j i).trans (key j i hj))`. Establish `h1` using `LinearMap.finrank_le_finrank_of_injective hf`. Rewrite `h1` using `[Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hS]`.

Conclude with `h1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (card_type_le H hρ)))`.
-/
theorem finrank_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q g : ℕ) (K : Type) [Field K] [CharZero K] (ρ : K) (ty : Fin g → (𝓞 E →+* K)) (V : Submodule K (Matrix (Fin g) (Fin g) K)), ρ ^ 2 = -(H.d : K) → (∀ τ : 𝓞 E →+* K, (τ H.rt = ρ → Nat.card {i // ty i = τ} = p) ∧ (τ H.rt ≠ ρ → Nat.card {i // ty i = τ} = q)) → (∀ Θ ∈ V, Θ.IsSymm ∧ ∀ a : 𝓞 E, Matrix.diagonal (fun i => ty i a) * Θ = Θ * (Matrix.diagonal (fun i => ty i (H.bar a))).transpose) → Module.finrank K V ≤ Module.finrank ℚ E / 2 * p * q := by
  intro E _ _ _ H p q g K _ _ ρ ty V hρ hty hV
  classical
  haveI := finite_hom E K
  have hne := root_ne_neg H hρ
  let S : Type := Σ τ : {τ : 𝓞 E →+* K // τ H.rt = ρ},
    {i // ty i = τ.1} × {j // ty j = τ.1.comp (H.bar : 𝓞 E →+* 𝓞 E)}
  haveI : Fintype S := Fintype.ofFinite S
  haveI : Fintype {τ : 𝓞 E →+* K // τ H.rt = ρ} := Fintype.ofFinite _
  have hS : Nat.card S = Nat.card {τ : 𝓞 E →+* K // τ H.rt = ρ} * p * q := by
    rw [Nat.card_sigma, Finset.sum_congr rfl (g := fun _ => p * q)]
    · rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card, Nat.mul_assoc]
    · intro τ _
      rw [Nat.card_prod, (hty τ.1).1 τ.2, (hty _).2]
      simpa [HostModel.bar_rt, τ.2] using hne
  let f : V →ₗ[K] (S → K) :=
    { toFun := fun Θ s => Θ.1 s.2.1.1 s.2.2.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro Θ h0
    obtain ⟨hs, hc⟩ := hV Θ.1 Θ.2
    have key : ∀ i j, ty i H.rt = ρ → Θ.1 i j = 0 := by
      intro i j hi
      by_contra hij
      refine hij (congrFun h0 ⟨⟨ty i, hi⟩, ⟨i, rfl⟩, ⟨j, RingHom.ext fun a => ?_⟩⟩)
      have := congrFun (congrFun (hc (H.bar a)) i) j
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
        HostModel.bar_bar, mul_comm] at this
      exact (mul_left_cancel₀ hij this).symm
    refine Subtype.ext (Matrix.ext fun i j => ?_)
    show Θ.1 i j = 0
    rcases map_rt H hρ (ty i) with hi | hi
    · exact key i j hi
    · by_contra hij
      have := congrFun (congrFun (hc H.rt) i) j
      rw [Matrix.diagonal_transpose, Matrix.diagonal_mul, Matrix.mul_diagonal,
        HostModel.bar_rt, mul_comm, map_neg, hi] at this
      have hj : ty j H.rt = ρ := (neg_injective (mul_left_cancel₀ hij this)).symm
      exact hij ((hs.apply j i).trans (key j i hj))
  have h1 := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hS] at h1
  exact h1.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (card_type_le H hρ)))

end GlobalTheory.SymSignature
