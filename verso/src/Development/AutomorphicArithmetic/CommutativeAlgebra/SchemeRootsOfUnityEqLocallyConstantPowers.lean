import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.GoodRoot
import Development.EtaleCohomology.EtaleSheaves.StandardChartsLineOne
import Development.AutomorphicArithmetic.CommutativeAlgebra.RootsOfUnityEqLocallyConstantPowersSpectrum

noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing GlobalTheory.EtC UpperTheory.Et LateralTheory.E.t_E2Cut LateralTheory.E.LineOneCut LateralTheory.E.StandardEtaleChartsMultivariableHensel

/- English proof (translation)
Introduce `X _ q _ ζ hζ`. Establish `hb : ∀ (x : X) (f : Γ(X, ⊤)), x ∉ X.basicOpen f ↔ f ∈ (X.toSpecΓ x).asIdeal`. Introduce `x f`. Rewrite using `[← Scheme.toSpecΓ_preimage_basicOpen]`. Conclude with `not_not`.

Set `h` to `X.isoSpec.hom.homeomorph`. Take `⟨h1, h2, h3⟩` from `UpperTheory.roots_of_unity_eq_locallyConstant_powers_spectrum Γ(X, ⊤) q ζ hζ`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Take `⟨w, hwq, hw⟩` from `h1 (LocallyConstant.comap ⟨h.symm, h.symm.continuous⟩ g)`.

Use `⟨w, hwq, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`. Establish `hx` using `hw (h x)`. Express the relevant statement in the definitionally equal form `w - ζ ^ (g (h.symm (h x))).val ∈ (h x).asIdeal at hx`. Rewrite `hx` using `[h.symm_apply_apply]`.

Conclude with `hx`. Introduce `w hw`. Take `⟨g, hg⟩` from `h2 w hw`. Use `⟨LocallyConstant.comap ⟨h, h.continuous⟩ g, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hb]`.

Conclude with `hg (h x)`. Introduce `a b x hx`. Rewrite `hx` using `[hb]`. Conclude with `h3 a b _ hx`. Introduce `x`.

Conclude with `⟨(X.toSpecΓ x).asIdeal, fun f => (hb x f).symm⟩`.
-/
theorem UpperTheory.scheme_roots_of_unity_eq_locallyConstant_powers :
    ∀ (X : Scheme.{0}) [IsAffine X] (q : ℕ) [NeZero q] (ζ : Γ(X, ⊤)), GoodRoot q ζ →
      (∀ g : LocallyConstant X (ZMod q), ∃ w : Γ(X, ⊤), w ^ q = 1 ∧ ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ w : Γ(X, ⊤), w ^ q = 1 → ∃ g : LocallyConstant X (ZMod q), ∀ x : X, x ∉ X.basicOpen (w - ζ ^ (g x).val)) ∧
      (∀ (a b : ZMod q) (x : X), x ∉ X.basicOpen (ζ ^ a.val - ζ ^ b.val) → a = b) ∧
      ∀ x : X, ∃ P : Ideal Γ(X, ⊤), ∀ f, f ∈ P ↔ x ∉ X.basicOpen f := by
  intro X _ q _ ζ hζ
  have hb : ∀ (x : X) (f : Γ(X, ⊤)), x ∉ X.basicOpen f ↔ f ∈ (X.toSpecΓ x).asIdeal := by
    intro x f
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    exact not_not
  let h := X.isoSpec.hom.homeomorph
  obtain ⟨h1, h2, h3⟩ := UpperTheory.roots_of_unity_eq_locallyConstant_powers_spectrum Γ(X, ⊤) q ζ hζ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨w, hwq, hw⟩ := h1 (LocallyConstant.comap ⟨h.symm, h.symm.continuous⟩ g)
    refine ⟨w, hwq, fun x => ?_⟩
    rw [hb]
    have hx := hw (h x)
    change w - ζ ^ (g (h.symm (h x))).val ∈ (h x).asIdeal at hx
    rw [h.symm_apply_apply] at hx
    exact hx
  · intro w hw
    obtain ⟨g, hg⟩ := h2 w hw
    refine ⟨LocallyConstant.comap ⟨h, h.continuous⟩ g, fun x => ?_⟩
    rw [hb]
    exact hg (h x)
  · intro a b x hx
    rw [hb] at hx
    exact h3 a b _ hx
  · intro x
    exact ⟨(X.toSpecΓ x).asIdeal, fun f => (hb x f).symm⟩

end
