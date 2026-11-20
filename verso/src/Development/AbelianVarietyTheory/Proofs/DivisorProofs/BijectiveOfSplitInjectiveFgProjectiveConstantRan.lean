import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `R _ M N _ _ _ _ n hM hN f r hrf`. Take `⟨hMf, hMp, hMr⟩` from `hM`. Take `⟨hNf, hNp, hNr⟩` from `hN`. Establish `hinj : Function.Injective f` using `fun a b h => by`. Use `congrArg r h` as an intermediate fact.

Rewrite `this` using `[hrf, hrf]`. Then use the resulting hypothesis. Set `K` to `LinearMap.ker r`. Set `π : N →ₗ[R] K` to `LinearMap.codRestrict K (LinearMap.id - f ∘ₗ r) (fun x => by show r (x - f (r x)) = 0`. Simplify using `[hrf])`. Establish `hπ : ∀ k : K, π (k : N) = k` using `fun k => by ext; simp [π, LinearMap.mem_ker.1 k.2]`.

Use `haveI : Module.Finite R K := Module.Finite.of_surjective π (fun k => ⟨k, hπ k⟩)`. Use `haveI : Module.Projective R K := Module.Projective.of_split K.subtype π (by ext k; simp [hπ])`. Set `e : N ≃ₗ[R] M × K` to `{ toFun := fun x => (r x, π x) map_add' := fun x y => by simp map_smul' := fun c x => by simp invFun := fun p => f p.1 + (p.2 : N) left_inv := fun x => by simp [π] right_inv := fun p => by`. Take `⟨m, k⟩` from `p`. Establish `hk : r (k : N) = 0` using `k.2`.

Use `ext`. Simplify using `[hrf, hk]`. Simplify using `[π, hrf, hk] }`. Establish `hK : Module.rankAtStalk (R` using `R) K = 0 := by`. Establish `h1` using `Module.rankAtStalk_eq_of_equiv e`.

Rewrite `h1` using `[Module.rankAtStalk_prod]`. Use function extensionality and compare the values at `p`. Establish `h2` using `congrFun h1 p`. Simplify using `only [Pi.add_apply, hMr p, hNr p] at h2`. Simplify using `only [Pi.zero_apply]`.

Use linear arithmetic over natural numbers and integers. Use `haveI : Subsingleton K := Module.rankAtStalk_eq_zero_iff_subsingleton.1 hK`. Use `⟨hinj, fun y => ⟨r y, ?_⟩⟩` and prove the remaining obligations. Establish `: π y = 0` using `Subsingleton.elim _ _`. Establish `h3` using `congrArg Subtype.val this`.

Simplify using `[π, sub_eq_zero] at h3`. Conclude with `h3.symm`.
-/
theorem bijective_of_split_of_FP : ∀ (R : Type) [CommRing R] (M N : Type) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (n : ℕ), FP R M n → FP R N n → ∀ (f : M →ₗ[R] N) (r : N →ₗ[R] M), (∀ x, r (f x) = x) → Function.Bijective f := by
  intro R _ M N _ _ _ _ n hM hN f r hrf
  obtain ⟨hMf, hMp, hMr⟩ := hM
  obtain ⟨hNf, hNp, hNr⟩ := hN
  have hinj : Function.Injective f := fun a b h => by
    have := congrArg r h; rwa [hrf, hrf] at this
  let K := LinearMap.ker r
  let π : N →ₗ[R] K := LinearMap.codRestrict K (LinearMap.id - f ∘ₗ r) (fun x => by
    show r (x - f (r x)) = 0
    simp [hrf])
  have hπ : ∀ k : K, π (k : N) = k := fun k => by
    ext; simp [π, LinearMap.mem_ker.1 k.2]
  haveI : Module.Finite R K := Module.Finite.of_surjective π (fun k => ⟨k, hπ k⟩)
  haveI : Module.Projective R K := Module.Projective.of_split K.subtype π (by ext k; simp [hπ])
  let e : N ≃ₗ[R] M × K :=
    { toFun := fun x => (r x, π x)
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp
      invFun := fun p => f p.1 + (p.2 : N)
      left_inv := fun x => by simp [π]
      right_inv := fun p => by
        obtain ⟨m, k⟩ := p
        have hk : r (k : N) = 0 := k.2
        ext
        · simp [hrf, hk]
        · simp [π, hrf, hk] }
  have hK : Module.rankAtStalk (R := R) K = 0 := by
    have h1 := Module.rankAtStalk_eq_of_equiv e
    rw [Module.rankAtStalk_prod] at h1
    funext p
    have h2 := congrFun h1 p
    simp only [Pi.add_apply, hMr p, hNr p] at h2
    simp only [Pi.zero_apply]; omega
  haveI : Subsingleton K := Module.rankAtStalk_eq_zero_iff_subsingleton.1 hK
  refine ⟨hinj, fun y => ⟨r y, ?_⟩⟩
  have : π y = 0 := Subsingleton.elim _ _
  have h3 := congrArg Subtype.val this
  simp [π, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory.AbCoh
