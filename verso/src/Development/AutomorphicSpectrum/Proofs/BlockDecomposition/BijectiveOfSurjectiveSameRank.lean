import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IotaQInjective

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.WedgeOf

namespace GlobalTheory.CompanionTheory.WedgeOf

/- English proof (translation)
Introduce `R A B _ _ _ _ _ n hA hB f hf`. Take `⟨fA, pA, rA⟩` from `hA`. Take `⟨fB, pB, rB⟩` from `hB`. Take `⟨g, hg⟩` from `Module.projective_lifting_property f LinearMap.id hf`. Establish `hg' : ∀ b, f (g b) = b` using `fun b => LinearMap.congr_fun hg b`.

Set `s : A →ₗ[R] LinearMap.ker f` to `LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - g ∘ₗ f) (fun a => by`. Simplify using `[LinearMap.mem_ker, hg'])`. Establish `hs : s ∘ₗ (LinearMap.ker f).subtype = LinearMap.id`. Use extensionality with `x`. Establish `hx : f x.1 = 0` using `x.2`.

Simplify using `[s, hx]`. Establish `hsurj : Function.Surjective s` using `fun x => ⟨x.1, LinearMap.congr_fun hs x⟩`. Use `haveI : Module.Finite R (LinearMap.ker f) := Module.Finite.of_surjective s hsurj`. Use `haveI : Module.Projective R (LinearMap.ker f) := Module.Projective.of_split (LinearMap.ker f).subtype s hs`. Set `E : (LinearMap.ker f × B) ≃ₗ[R] A` to `LinearEquiv.ofLinear ((LinearMap.ker f).subtype.coprod g) (s.prod f) (by`.

Apply the tactic sequence `ext a <;> simp [s, hg'])`. Use the proof step `(by`. Apply the tactic sequence `ext x <;> simp [s, hg'])`. Establish `hsub : Subsingleton (LinearMap.ker f)`. Rewrite using `[← Module.rankAtStalk_eq_zero_iff_subsingleton (R := R)]`.

Use function extensionality and compare the values at `p`. Establish `h1` using `congrFun (Module.rankAtStalk_prod (R := R) (LinearMap.ker f) B) p`. Establish `h2` using `Module.rankAtStalk_eq_of_equiv (R := R) E`. Establish `h3` using `congrFun h2 p`. Simplify using `only [Pi.add_apply] at h1`.

Rewrite `h3` using `[h1, rA p, rB p]`. Simplify using `using h3`. Use `⟨?_, hf⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`.

Establish `: (⟨a, ha⟩ : LinearMap.ker f) = 0` using `Subsingleton.elim _ _`. Simplify using `using congrArg Subtype.val this`.
-/
theorem bijective_of_surjective_of_VB : ∀ (R A B : Type) [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (n : ℕ), VB R A n → VB R B n → ∀ f : A →ₗ[R] B,
    Function.Surjective f → Function.Bijective f := by
  intro R A B _ _ _ _ _ n hA hB f hf
  obtain ⟨fA, pA, rA⟩ := hA
  obtain ⟨fB, pB, rB⟩ := hB
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hg' : ∀ b, f (g b) = b := fun b => LinearMap.congr_fun hg b

  let s : A →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) (LinearMap.id - g ∘ₗ f) (fun a => by
      simp [LinearMap.mem_ker, hg'])
  have hs : s ∘ₗ (LinearMap.ker f).subtype = LinearMap.id := by
    ext x
    have hx : f x.1 = 0 := x.2
    simp [s, hx]
  have hsurj : Function.Surjective s := fun x => ⟨x.1, LinearMap.congr_fun hs x⟩
  haveI : Module.Finite R (LinearMap.ker f) := Module.Finite.of_surjective s hsurj
  haveI : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype s hs

  let E : (LinearMap.ker f × B) ≃ₗ[R] A :=
    LinearEquiv.ofLinear ((LinearMap.ker f).subtype.coprod g) (s.prod f)
      (by
        ext a <;> simp [s, hg'])
      (by
        ext x <;> simp [s, hg'])
  have hsub : Subsingleton (LinearMap.ker f) := by
    rw [← Module.rankAtStalk_eq_zero_iff_subsingleton (R := R)]
    funext p
    have h1 := congrFun (Module.rankAtStalk_prod (R := R) (LinearMap.ker f) B) p
    have h2 := Module.rankAtStalk_eq_of_equiv (R := R) E
    have h3 := congrFun h2 p
    simp only [Pi.add_apply] at h1
    rw [h1, rA p, rB p] at h3
    simpa using h3
  refine ⟨?_, hf⟩
  rw [injective_iff_map_eq_zero]
  intro a ha
  have : (⟨a, ha⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
  simpa using congrArg Subtype.val this

end GlobalTheory.CompanionTheory.WedgeOf
