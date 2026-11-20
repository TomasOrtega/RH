import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.StageLift
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSatakeParameterOfIsSubquotientOfInjective

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel MeasureTheory

namespace PositivityTheory.Rg.BcB.N3.PseSat

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use `hi` as an intermediate fact. Set `S : Subrepresentation π` to `⟨LinearMap.ker f.toLinearMap, fun g v hv => by show f (π g v) = 0`. Rewrite using `[f.isIntertwining]`. Simplify using `only [LinearMap.mem_ker] at hv`. Simplify using `[show f v = 0 from hv]⟩`.

Break down `IsSimpleOrder.eq_bot_or_eq_top S with h | h` into its components or cases. Introduce `a b hab`. Establish `: a - b ∈ S.toSubmodule` using `by show f.toLinearMap (a - b) = 0`. Rewrite using `[map_sub]`. Conclude with `sub_eq_zero.2 hab`.

Rewrite `this` using `[h]`. Conclude with `sub_eq_zero.1 this`. It suffices to derive a contradiction. Apply `hf` to reduce the goal to its premises. Use extensionality with `v`.

Establish `: v ∈ S.toSubmodule` using `by rw [h]; trivial`. Conclude with `this`.
-/
theorem injective_of_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (hi : π.IsIrreducible) (f : π.IntertwiningMap σ)
    (hf : f ≠ 0) : Function.Injective f := by
  have := hi
  let S : Subrepresentation π := ⟨LinearMap.ker f.toLinearMap, fun g v hv => by
    show f (π g v) = 0
    rw [f.isIntertwining]
    simp only [LinearMap.mem_ker] at hv
    simp [show f v = 0 from hv]⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top S with h | h
  · intro a b hab
    have : a - b ∈ S.toSubmodule := by
      show f.toLinearMap (a - b) = 0
      rw [map_sub]
      exact sub_eq_zero.2 hab
    rw [h] at this
    exact sub_eq_zero.1 this
  · exfalso
    apply hf
    ext v
    have : v ∈ S.toSubmodule := by rw [h]; trivial
    exact this

/- English proof (translation)
Set `R : Subrepresentation σ` to `⟨LinearMap.range f.toLinearMap, by`. Introduce and unpack `g _ ⟨v, rfl⟩`. Conclude with `⟨π g v, by simpa using Representation.IntertwiningMap.isIntertwining _ _ f g v⟩⟩`. Set `e` to `LinearEquiv.ofInjective f.toLinearMap hf`. Use `⟨R, ⟨e.symm.toLinearMap, fun g => ?_⟩, e.symm.surjective⟩` and prove the remaining obligations.

Use extensionality with `⟨w, v, rfl⟩`. Apply `e.injective` to reduce the goal to its premises. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show _ = f (π g (e.symm ⟨f v, v, rfl⟩))`.

Establish `h1 : e.symm ⟨f v, v, rfl⟩ = v` using `e.symm_apply_eq.2 rfl`. Rewrite using `[h1, f.isIntertwining]`. Both sides reduce to the same expression.
-/
theorem isSubquotient_of_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ G V} {σ : Representation ℂ G W} (f : π.IntertwiningMap σ) (hf : Function.Injective f) :
    IsSubquotient π σ := by
  let R : Subrepresentation σ := ⟨LinearMap.range f.toLinearMap, by
    rintro g _ ⟨v, rfl⟩
    exact ⟨π g v, by simpa using Representation.IntertwiningMap.isIntertwining _ _ f g v⟩⟩
  let e := LinearEquiv.ofInjective f.toLinearMap hf
  refine ⟨R, ⟨e.symm.toLinearMap, fun g => ?_⟩, e.symm.surjective⟩
  ext ⟨w, v, rfl⟩
  apply e.injective
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  apply Subtype.ext
  show _ = f (π g (e.symm ⟨f v, v, rfl⟩))
  have h1 : e.symm ⟨f v, v, rfl⟩ = v := e.symm_apply_eq.2 rfl
  rw [h1, f.isIntertwining]
  rfl

/- English proof (translation)
Introduce `n ξ η V _ _ π hs hi hsph hq ⟨f, hf⟩`. Establish `hinj` using `injective_of_ne_zero hi f hf`. Establish `hq'` using `isSubquotient_of_injective f hinj`. Use `borelize (GL (Fin n) k)`. Establish `h1` using `GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) ξ hq (μ := Measure.haar)`.

Establish `h2` using `GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) η hq' (μ := Measure.haar)`. Establish `hK` using `(GlobalTheory.CompanionTheory.SphSupp.isSpherical_iff_fixedVectors π).1 hsph`. Conclude with `GroundTheory.Automorphic.Spherical.satakeParameter_unique hK h1 h2`.
-/
theorem satPerm : SatPerm k := by
  intro n ξ η V _ _ π hs hi hsph hq ⟨f, hf⟩
  have hinj := injective_of_ne_zero hi f hf
  have hq' := isSubquotient_of_injective f hinj
  borelize (GL (Fin n) k)
  have h1 := GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) ξ hq (μ := Measure.haar)
  have h2 := GlobalTheory.CompanionTheory.SphSupp.isSatakeParameter_of_isSubquotient (k := k) η hq' (μ := Measure.haar)
  have hK := (GlobalTheory.CompanionTheory.SphSupp.isSpherical_iff_fixedVectors π).1 hsph
  exact GroundTheory.Automorphic.Spherical.satakeParameter_unique hK h1 h2

end PositivityTheory.Rg.BcB.N3.PseSat
