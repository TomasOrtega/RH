import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLen

/- English proof (translation)
Rewrite `hA`, `hC`, the goal using `[isFiniteLength_iff_isNoetherian_isArtinian]`. Take `⟨_, _⟩` from `hA`. Take `⟨_, _⟩` from `hC`. Establish `n1 : IsNoetherian W (LinearMap.range v)` using `isNoetherian_of_surjective v.rangeRestrict (LinearMap.range_rangeRestrict v)`. Establish `a1 : IsArtinian W (LinearMap.range v)` using `isArtinian_of_surjective A v.rangeRestrict v.surjective_rangeRestrict`.

Establish `n2 : IsNoetherian W (LinearMap.ker f)` using `isNoetherian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)`. Establish `a2 : IsArtinian W (LinearMap.ker f)` using `isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)`. Establish `hr : LinearMap.range (LinearMap.ker f).subtype = LinearMap.ker f.rangeRestrict`. Rewrite using `[Submodule.range_subtype, LinearMap.ker_rangeRestrict]`. Conclude with `⟨isNoetherian_of_range_eq_ker _ _ hr, isArtinian_of_range_eq_ker _ _ hr⟩`.
-/
theorem isFiniteLength_of_ker_le_range {W : Type} [CommRing W] {A B C : Type 1}
    [AddCommGroup A] [Module W A] [AddCommGroup B] [Module W B] [AddCommGroup C] [Module W C]
    (v : A →ₗ[W] B) (f : B →ₗ[W] C) (h : LinearMap.ker f ≤ LinearMap.range v)
    (hA : IsFiniteLength W A) (hC : IsFiniteLength W C) : IsFiniteLength W B := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hA hC ⊢
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hC
  have n1 : IsNoetherian W (LinearMap.range v) :=
    isNoetherian_of_surjective v.rangeRestrict (LinearMap.range_rangeRestrict v)
  have a1 : IsArtinian W (LinearMap.range v) :=
    isArtinian_of_surjective A v.rangeRestrict v.surjective_rangeRestrict
  have n2 : IsNoetherian W (LinearMap.ker f) :=
    isNoetherian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have a2 : IsArtinian W (LinearMap.ker f) :=
    isArtinian_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have hr : LinearMap.range (LinearMap.ker f).subtype = LinearMap.ker f.rangeRestrict := by
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict]
  exact ⟨isNoetherian_of_range_eq_ker _ _ hr, isArtinian_of_range_eq_ker _ _ hr⟩

/- English proof (translation)
Introduce `W _ l S S' L h1 n`. Proceed by induction on `n with`. Consider the case `zero`. Establish `: Subsingleton (S.M 0)` using `⟨fun x y => by`. Establish `hx` using `L.kill 0 x`.

Establish `hy` using `L.kill 0 y`. Simplify using `only [pow_zero, one_smul] at hx hy`. Rewrite using `[hx, hy]⟩`. Conclude with `IsFiniteLength.of_subsingleton`. Consider the case `succ n ih`.

Use `isFiniteLength_of_ker_le_range (L.ν 1 (n + 1)) (L.ρ (n + 1) n) ?_ h1 ih` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, hy⟩` from `L.ex₁ 1 n (n + 1) (by omega) x hx`. Conclude with `⟨y, hy⟩`.
-/
theorem isFiniteLength_level : ∀ (W : Type) [CommRing W] (l : ℕ) (S S' : Sys.{1} W) (_ : LSeq l S S'),
    IsFiniteLength W (S.M 1) → ∀ n, IsFiniteLength W (S.M n) := by
  intro W _ l S S' L h1 n
  induction n with
  | zero =>
    have : Subsingleton (S.M 0) := ⟨fun x y => by
      have hx := L.kill 0 x
      have hy := L.kill 0 y
      simp only [pow_zero, one_smul] at hx hy
      rw [hx, hy]⟩
    exact IsFiniteLength.of_subsingleton
  | succ n ih =>
    refine isFiniteLength_of_ker_le_range (L.ν 1 (n + 1)) (L.ρ (n + 1) n) ?_ h1 ih
    intro x hx
    obtain ⟨y, hy⟩ := L.ex₁ 1 n (n + 1) (by omega) x hx
    exact ⟨y, hy⟩

end GlobalTheory.CompanionTheory.TowerLen
