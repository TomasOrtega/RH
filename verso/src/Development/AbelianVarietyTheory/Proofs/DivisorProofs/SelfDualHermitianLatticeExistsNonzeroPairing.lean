import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n J x w hJ`. Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sesquilinearFormOfGram_eq_conj_swap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (x w : Fin n → E),
    (∀ i j, σ (J j i) = J i j) → form σ J x w = σ (form σ J w x) := by
  intro F E _ _ _ _ _ σ hσ n J x w hJ
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Introduce `h`. Use `haveI : Module.Finite (𝓞 E) E := ⟨h⟩`. Use `haveI : Module.Finite ℤ E := Module.Finite.trans (𝓞 E) E`. Establish `hi : IsIntegral ℤ (algebraMap ℚ E (2⁻¹ : ℚ))` using `Algebra.IsIntegral.isIntegral _`. Rewrite `hi` using `[isIntegral_algebraMap_iff (algebraMap ℚ E).injective]`.

Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hi`. Establish `h2 : ((2 * y : ℤ) : ℚ) = 1`. Use `push_cast`. Rewrite `hy` using `[show (algebraMap ℤ ℚ y) = (y : ℚ) from rfl]`. Rewrite using `[hy]`.

Evaluate the numerical expressions. Establish `: 2 * y = 1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem not_fg_top_ringOfIntegers (E : Type) [Field E] [NumberField E] :
    ¬ (⊤ : Submodule (𝓞 E) E).FG := by
  intro h
  haveI : Module.Finite (𝓞 E) E := ⟨h⟩
  haveI : Module.Finite ℤ E := Module.Finite.trans (𝓞 E) E
  have hi : IsIntegral ℤ (algebraMap ℚ E (2⁻¹ : ℚ)) := Algebra.IsIntegral.isIntegral _
  rw [isIntegral_algebraMap_iff (algebraMap ℚ E).injective] at hi
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hi
  have h2 : ((2 * y : ℤ) : ℚ) = 1 := by
    push_cast
    rw [show (algebraMap ℤ ℚ y) = (y : ℚ) from rfl] at hy
    rw [hy]; norm_num
  have : 2 * y = 1 := by exact_mod_cast h2
  omega

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n J L hL hJ hdual x hx`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hxw : ∀ w ∈ L, form σ J x w = 0` using `fun w hw => by`. Rewrite using `[sesquilinearFormOfGram_eq_conj_swap F E σ hσ n J x w hJ, hcon w hw, map_zero]`.

Establish `hmem : ∀ c : E, c • x ∈ L` using `fun c => by`. Rewrite using `[hdual]`. Introduce `w hw`. Establish `: form σ J (c • x) w = c * form σ J x w`. Simplify using `[form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]`.

Rewrite using `[this, hxw w hw, mul_zero]`. Conclude with `isIntegral_zero`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, x i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hx (funext h)`. Set `f : (Fin n → E) →ₗ[𝓞 E] E` to `(LinearMap.proj i : (Fin n → E) →ₗ[E] E).restrictScalars (𝓞 E)`. Establish `htop : L.map f = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `e _`.

Use `⟨(e / x i) • x, hmem _, ?_⟩` and prove the remaining obligations. Simplify using `[f, div_mul_cancel₀ _ hi]`. Conclude with `not_fg_top_ringOfIntegers E (htop ▸ hL.map f)`.
-/
theorem selfDual_pair_nondeg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    (∀ e, σ (σ e) = e) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    (∀ i j, σ (J j i) = J i j) → (∀ y, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (form σ J y x)) →
    ∀ x : Fin n → E, x ≠ 0 → ∃ z ∈ L, form σ J z x ≠ 0 := by
  intro F E _ _ _ _ _ σ hσ n J L hL hJ hdual x hx
  by_contra hcon
  push_neg at hcon
  have hxw : ∀ w ∈ L, form σ J x w = 0 := fun w hw => by
    rw [sesquilinearFormOfGram_eq_conj_swap F E σ hσ n J x w hJ, hcon w hw, map_zero]
  have hmem : ∀ c : E, c • x ∈ L := fun c => by
    rw [hdual]
    intro w hw
    have : form σ J (c • x) w = c * form σ J x w := by
      simp [form, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
    rw [this, hxw w hw, mul_zero]
    exact isIntegral_zero
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push_neg at h; exact hx (funext h)
  let f : (Fin n → E) →ₗ[𝓞 E] E := (LinearMap.proj i : (Fin n → E) →ₗ[E] E).restrictScalars (𝓞 E)
  have htop : L.map f = ⊤ := by
    rw [eq_top_iff]
    intro e _
    refine ⟨(e / x i) • x, hmem _, ?_⟩
    simp [f, div_mul_cancel₀ _ hi]
  exact not_fg_top_ringOfIntegers E (htop ▸ hL.map f)

end GlobalTheory
