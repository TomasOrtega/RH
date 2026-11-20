import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker σ hσ`. Establish `h2 : ∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y`. Introduce `b y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul y' b₀`. Take `⟨b', rfl⟩` from `hp b₀`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← map_mul, hσ, hσ, mul_smul_comm]`. Consider the case `add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]`. Use `⟨?_, h2, ?_, ?_⟩` and prove the remaining obligations.

Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul y' b₀`. Take `⟨b', rfl⟩` from `hp b₀`.

Rewrite using `[hσ, Algebra.smul_def]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem y'))`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `Ideal.add_mem _ hx hy`. Introduce `b₀`.

Take `⟨b', rfl⟩` from `hp b₀`. Rewrite using `[hσ, α.one, zero_smul]`. Introduce `x hx`. Rewrite `hx` using `[Ideal.map, Ideal.span]`. Proceed by induction on `hx using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨i, hi, rfl⟩` from `hx`. Take `⟨y, hy0, hyk⟩` from `α.surj i hi`. Use `⟨y ⊗ₜ 1, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[Obs.Aug.KerQ, hy0]`.

Rewrite using `[← map_one p, hσ, hyk, Algebra.smul_def, _root_.mul_one]`. Consider the case `zero => exact ⟨0, by simp [Obs.Aug.KerQ], by simp⟩`. Consider the case `add x x' _ _ hx hx'`. Take `⟨y, hy, rfl⟩` from `hx`. Take `⟨y', hy', rfl⟩` from `hx'`.

Use `⟨y + y', ?_, by rw [map_add]⟩` and prove the remaining obligations. Simplify using `only [Obs.Aug.KerQ, map_add] at *`. Rewrite using `[hy, hy', add_zero]`. Consider the case `smul b x _ hx`. Take `⟨y, hy, rfl⟩` from `hx`.

Use `⟨(1 ⊗ₜ p b) * y, ?_, by rw [h2, smul_eq_mul]⟩` and prove the remaining obligations. Simplify using `only [Obs.Aug.KerQ, map_mul] at *`. Rewrite using `[hy, mul_zero]`.
-/
theorem Obs.sig_basic : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → (∀ y, σ y ∈ I.map (algebraMap R B)) ∧ (∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y) ∧ (∀ b₀ : B₀, σ (1 ⊗ₜ b₀) = 0) ∧ ∀ x ∈ I.map (algebraMap R B), ∃ y, α.KerQ y ∧ σ y = x := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker σ hσ
  have h2 : ∀ b y, σ ((1 ⊗ₜ p b) * y) = b * σ y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← map_mul, hσ, hσ, mul_smul_comm]
    | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]
  refine ⟨?_, h2, ?_, ?_⟩
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y' b₀ =>
      obtain ⟨b', rfl⟩ := hp b₀
      rw [hσ, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (α.mem y'))
    | add x y hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
  · intro b₀
    obtain ⟨b', rfl⟩ := hp b₀
    rw [hσ, α.one, zero_smul]
  · intro x hx
    rw [Ideal.map, Ideal.span] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      obtain ⟨y, hy0, hyk⟩ := α.surj i hi
      refine ⟨y ⊗ₜ 1, ?_, ?_⟩
      · simp [Obs.Aug.KerQ, hy0]
      · rw [← map_one p, hσ, hyk, Algebra.smul_def, _root_.mul_one]
    | zero => exact ⟨0, by simp [Obs.Aug.KerQ], by simp⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hx'
      refine ⟨y + y', ?_, by rw [map_add]⟩
      simp only [Obs.Aug.KerQ, map_add] at *; rw [hy, hy', add_zero]
    | smul b x _ hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨(1 ⊗ₜ p b) * y, ?_, by rw [h2, smul_eq_mul]⟩
      simp only [Obs.Aug.KerQ, map_mul] at *; rw [hy, mul_zero]

end GlobalTheory
