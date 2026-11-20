import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open GroundTheory.Heights₂.Heights.Regular
open scoped Matrix ComplexOrder

def basePoint (n a : ℕ) : Fin n → ℂ := fun k => if k.val < a then -1 else 0

/- English proof (translation)
Use `⟨fun i => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Establish `: (Fin.castLE h i).val < a` using `i.isLt`. Simplify using `[basePoint, this]`. Establish `: ¬ k.val < a` using `by omega`. Simplify using `[basePoint, this]`.
-/
theorem basePoint_mem {n a : ℕ} (h : a ≤ n) : basePoint n a ∈ logCover h := by
  refine ⟨fun i => ?_, fun k hk => ?_⟩
  · have : (Fin.castLE h i).val < a := i.isLt
    simp [basePoint, this]
  · have : ¬ k.val < a := by omega
    simp [basePoint, this]

/- English proof (translation)
Use `⟨fun j => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hj : (Fin.castLE h j).val < a` using `j.isLt`. Distinguish the cases in `hji : Fin.castLE h j = Fin.castLE h i`. Simplify using `[basePoint, hj, hji, Pi.single_apply]`. Simplify using `[basePoint, hj, Pi.single_apply, hji]`.

Establish `hk' : ¬ k.val < a` using `by omega`. Establish `hne : k ≠ Fin.castLE h i`. Introduce `e`. Apply `hk'` to reduce the goal to its premises. Rewrite using `[e]`.

Conclude with `i.isLt`. Simplify using `[basePoint, hk', Pi.single_apply, hne]`.
-/
theorem shift_mem {n a : ℕ} (h : a ≤ n) (i : Fin a) :
    basePoint n a + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I) ∈ logCover h := by
  refine ⟨fun j => ?_, fun k hk => ?_⟩
  · have hj : (Fin.castLE h j).val < a := j.isLt
    by_cases hji : Fin.castLE h j = Fin.castLE h i
    · simp [basePoint, hj, hji, Pi.single_apply]
    · simp [basePoint, hj, Pi.single_apply, hji]
  · have hk' : ¬ k.val < a := by omega
    have hne : k ≠ Fin.castLE h i := by
      intro e
      apply hk'
      rw [e]
      exact i.isLt
    simp [basePoint, hk', Pi.single_apply, hne]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Distinguish the cases in `hk : k = Fin.castLE h i`. Substitute `hk` using the available equality. Establish `: (Fin.castLE h i).val < a` using `i.isLt`. Simplify using `[expCover, this, Complex.exp_add, Complex.exp_two_pi_mul_I]`.

Simplify using `[expCover, Pi.single_apply, hk]`.
-/
theorem expCover_shift {n a : ℕ} (h : a ≤ n) (i : Fin a) (w : Fin n → ℂ) :
    expCover a (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = expCover a w := by
  funext k
  by_cases hk : k = Fin.castLE h i
  · subst hk
    have : (Fin.castLE h i).val < a := i.isLt
    simp [expCover, this, Complex.exp_add, Complex.exp_two_pi_mul_I]
  · simp [expCover, Pi.single_apply, hk]

/- English proof (translation)
Establish `hw` using `basePoint_mem L.a_le`. Establish `h1` using `L.im _ (shift_mem L.a_le i) x y`. Rewrite `h1` using `[expCover_shift, L.mono i _ hw x, L.mono i _ hw y]`. Establish `h2` using `L.im _ hw (L.T i x) (L.T i y)`. Conclude with `h2.symm.trans h1` after adjusting the coercions.
-/
theorem monodromy_preserves_form {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (i : Fin a) (x y : Λ) :
    L.E (L.T i x) (L.T i y) = L.E x y := by
  have hw := basePoint_mem L.a_le
  have h1 := L.im _ (shift_mem L.a_le i) x y
  rw [expCover_shift, L.mono i _ hw x, L.mono i _ hw y] at h1
  have h2 := L.im _ hw (L.T i x) (L.T i y)
  exact_mod_cast h2.symm.trans h1

/- English proof (translation)
Introduce `n a g Λ _ L i`. Use `haveI := L.fin`. Set `e : Λ ≃ₗ[ℤ] Module.Dual ℤ Λ` to `LinearEquiv.ofBijective L.E L.unimod`. Set `S : Λ →ₗ[ℤ] Λ` to `e.symm.toLinearMap ∘ₗ (L.T i).dualMap ∘ₗ e.toLinearMap`. Establish `hS : ∀ x, S (L.T i x) = x`.

Introduce `x`. Apply `e.injective` to reduce the goal to its premises. Simplify using `only [S, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]`. Use extensionality with `y`. Simplify `monodromy_preserves_form L i x y` using `[e, LinearMap.dualMap_apply]`.

Establish `hSsurj : Function.Surjective S` using `fun x => ⟨_, hS x⟩`. Establish `hSinj : Function.Injective S` using `OrzechProperty.injective_of_surjective_endomorphism S hSsurj`. Use `⟨Function.LeftInverse.injective hS, fun y => ⟨S y, hSinj (hS (S y))⟩⟩` and prove the remaining obligations.
-/
theorem T_bijective : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (i : Fin a),
    Function.Bijective (L.T i) := by
  intro n a g Λ _ L i
  haveI := L.fin
  let e : Λ ≃ₗ[ℤ] Module.Dual ℤ Λ := LinearEquiv.ofBijective L.E L.unimod
  let S : Λ →ₗ[ℤ] Λ := e.symm.toLinearMap ∘ₗ (L.T i).dualMap ∘ₗ e.toLinearMap
  have hS : ∀ x, S (L.T i x) = x := by
    intro x
    apply e.injective
    simp only [S, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    ext y
    simpa [e, LinearMap.dualMap_apply] using monodromy_preserves_form L i x y
  have hSsurj : Function.Surjective S := fun x => ⟨_, hS x⟩
  have hSinj : Function.Injective S := OrzechProperty.injective_of_surjective_endomorphism S hSsurj
  refine ⟨Function.LeftInverse.injective hS, fun y => ⟨S y, hSinj (hS (S y))⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat.MonodromyBij
