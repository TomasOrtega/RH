import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmooth
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

/- English proof (translation)
Introduce `R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ e₀ he₀`. Take `⟨e, he⟩` from `homLift R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' B' B₀' p' hs' hp' hker' e₀`. Use `set J : Ideal B' := I.map (algebraMap R B') with hJ`. Establish `hJ2 : ∀ x ∈ J, ∀ y ∈ J, x * y = 0`. Introduce `x hx y hy`.

Establish `: x * y ∈ J ^ 2` using `by rw [pow_two]; exact Ideal.mul_mem_mul hx hy`. Rewrite `this` using `[hJ, ← Ideal.map_pow, hI]`. Simplify using `using this`. Establish `hu : ∀ c, e (e c) - e c ∈ J`. Introduce `c`.

Rewrite using `[← hker']`. Simplify using `[map_sub, he, he₀]`. Establish `hkill : ∀ x ∈ J, ∀ c, e (e (c * x)) - e (c * x) = 0`. Introduce `x hx`. Rewrite `hx` using `[hJ, Ideal.map]`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨r, hr, rfl⟩` from `hy`. Introduce `c`. Establish `h1 : e (c * algebraMap R B' r) = e c * algebraMap R B' r`.

Rewrite using `[map_mul, AlgHom.commutes]`. Establish `h2 : e (e c * algebraMap R B' r) = e (e c) * algebraMap R B' r`. Rewrite using `[map_mul, AlgHom.commutes]`. Rewrite using `[h1, h2, ← sub_mul]`. Conclude with `hJ2 _ (hu c) _ (Ideal.mem_map_of_mem _ hr)`.

Consider the case `zero => intro c`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Introduce `c`. Use `hx c` as an intermediate fact.

Use `hy c` as an intermediate fact. Rewrite using `[mul_add, map_add, map_add]`. Take the linear combination `hx c + hy c`. Consider the case `smul a x _ hx`. Introduce `c`.

Rewrite using `[smul_eq_mul, ← _root_.mul_assoc]`. Conclude with `hx (c * a)`. Establish `hrec : ∀ c, e (e (e (e c))) - 2 * e (e (e c)) + e (e c) = 0`. Introduce `c`. Use `hkill _ (hu c) 1` as an intermediate fact.

Simplify using `only [_root_.one_mul, map_sub] at this`. Take the linear combination `this`. Set `e' : B' →ₐ[R] B'` to `{ toFun := fun b => 3 * e (e b) - 2 * e (e (e b)) map_one' := by simp; norm_num map_mul' := by`. Introduce `x y`. Establish `h` using `hJ2 _ (hu (e x)) _ (hu (e y))`.

Simplify using `only [map_mul]`. Take the linear combination `(-6 : B') * h`. Use the proof step `map_zero' := by simp`. Use the proof step `map_add' := by intro x y; simp only [map_add]; ring`. Use the proof step `commutes' := by intro r; simp only [AlgHom.commutes]; ring }`.

Use `⟨e', ?_, ?_⟩` and prove the remaining obligations. Introduce `b show 3 * e (e (3 * e (e b) - 2 * e (e (e b)))) - 2 * e (e (e (3 * e (e b) - 2 * e (e (e b))))) = 3 * e (e b) - 2 * e (e (e b))`. Simplify using `only [map_sub, map_mul, map_ofNat]`. Take the linear combination `(-3 : B') * hrec b + (-4 : B') * hrec (e b) + (4 : B') * hrec (e (e b))`. Introduce `b show p' (3 * e (e b) - 2 * e (e (e b))) = e₀ (p' b)`.

Simplify using `only [map_sub, map_mul, map_ofNat, he, he₀]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem idemLift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) [Algebra.FormallySmooth R B'] (e₀ : B₀' →ₐ[R₀] B₀'), (∀ x, e₀ (e₀ x) = e₀ x) → ∃ e : B' →ₐ[R] B', (∀ b, e (e b) = e b) ∧ ∀ b, p' (e b) = e₀ (p' b) := by
  intro R R₀ _ _ I hI π hπ hk B' B₀' _ _ _ _ p' hs' hp' hker' _ e₀ he₀
  obtain ⟨e, he⟩ := homLift R R₀ I hI π hπ hk B' B₀' p' hs' hp' hker' B' B₀' p' hs' hp' hker' e₀
  set J : Ideal B' := I.map (algebraMap R B') with hJ
  have hJ2 : ∀ x ∈ J, ∀ y ∈ J, x * y = 0 := by
    intro x hx y hy
    have : x * y ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
    rw [hJ, ← Ideal.map_pow, hI] at this
    simpa using this
  have hu : ∀ c, e (e c) - e c ∈ J := by
    intro c
    rw [← hker']
    simp [map_sub, he, he₀]
  have hkill : ∀ x ∈ J, ∀ c, e (e (c * x)) - e (c * x) = 0 := by
    intro x hx
    rw [hJ, Ideal.map] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      intro c
      have h1 : e (c * algebraMap R B' r) = e c * algebraMap R B' r := by
        rw [map_mul, AlgHom.commutes]
      have h2 : e (e c * algebraMap R B' r) = e (e c) * algebraMap R B' r := by
        rw [map_mul, AlgHom.commutes]
      rw [h1, h2, ← sub_mul]
      exact hJ2 _ (hu c) _ (Ideal.mem_map_of_mem _ hr)
    | zero => intro c; simp
    | add x y _ _ hx hy =>
      intro c
      have := hx c
      have := hy c
      rw [mul_add, map_add, map_add]
      linear_combination hx c + hy c
    | smul a x _ hx =>
      intro c
      rw [smul_eq_mul, ← _root_.mul_assoc]
      exact hx (c * a)
  have hrec : ∀ c, e (e (e (e c))) - 2 * e (e (e c)) + e (e c) = 0 := by
    intro c
    have := hkill _ (hu c) 1
    simp only [_root_.one_mul, map_sub] at this
    linear_combination this
  let e' : B' →ₐ[R] B' :=
    { toFun := fun b => 3 * e (e b) - 2 * e (e (e b))
      map_one' := by simp; norm_num
      map_mul' := by
        intro x y
        have h := hJ2 _ (hu (e x)) _ (hu (e y))
        simp only [map_mul]
        linear_combination (-6 : B') * h
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add]; ring
      commutes' := by intro r; simp only [AlgHom.commutes]; ring }
  refine ⟨e', ?_, ?_⟩
  · intro b
    show 3 * e (e (3 * e (e b) - 2 * e (e (e b)))) - 2 * e (e (e (3 * e (e b) - 2 * e (e (e b))))) = 3 * e (e b) - 2 * e (e (e b))
    simp only [map_sub, map_mul, map_ofNat]
    linear_combination (-3 : B') * hrec b + (-4 : B') * hrec (e b) + (4 : B') * hrec (e (e b))
  · intro b
    show p' (3 * e (e b) - 2 * e (e (e b))) = e₀ (p' b)
    simp only [map_sub, map_mul, map_ofNat, he, he₀]
    ring

end GlobalTheory.Obs
