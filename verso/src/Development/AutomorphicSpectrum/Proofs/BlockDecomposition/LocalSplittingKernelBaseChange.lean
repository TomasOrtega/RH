import Mathlib
open TensorProduct

namespace GlobalTheory.CompanionTheory.RegularLocal

/- English proof (translation)
Introduce `R Q P _ _ _ _ _ _ _ _ _ d h`. Establish `hex : Function.Exact d (LinearMap.range d).mkQ` using `LinearMap.exact_map_mkQ_range d`. Establish `hsurj : Function.Surjective (LinearMap.range d).mkQ` using `Submodule.mkQ_surjective _`. Establish `hloc : ∀ (p : Ideal R) [p.IsMaximal], Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] (P ⧸ LinearMap.range d))`. Introduce `p _`.

Take `⟨r, hr⟩` from `h p`. Use `set A := Localization.AtPrime p`. Use `set dA := d.baseChange A with hdA`. Use `set πA := (LinearMap.range d).mkQ.baseChange A with hπA`. Establish `hexA : Function.Exact dA πA`.

Use `lTensor_exact A hex hsurj` as an intermediate fact. Simplify `this` using `[hdA, hπA, LinearMap.baseChange_eq_ltensor]`. Establish `hsA : Function.Surjective πA`. Use `LinearMap.lTensor_surjective A hsurj` as an intermediate fact. Simplify `this` using `[hπA, LinearMap.baseChange_eq_ltensor]`.

Set `e : A ⊗[R] P →ₗ[A] A ⊗[R] P` to `LinearMap.id - dA ∘ₗ r`. Establish `he : ∀ x ∈ LinearMap.range dA, e x = 0`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `LinearMap.congr_fun hr y` as an intermediate fact. Simplify using `only [LinearMap.comp_apply] at this`.

Simplify using `[e, this]`. Set `s : A ⊗[R] (P ⧸ LinearMap.range d) →ₗ[A] A ⊗[R] P` to `((LinearMap.range dA).liftQ e (fun x hx => he x hx)) ∘ₗ (hexA.linearEquivOfSurjective hsA).symm.toLinearMap`. Establish `hs : ∀ x, s (πA x) = e x`. Introduce `x`. Establish `: (hexA.linearEquivOfSurjective hsA).symm (πA x) = (LinearMap.range dA).mkQ x`.

Rewrite using `[LinearEquiv.symm_apply_eq]`. Both sides reduce to the same expression. Simplify using `only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]`. Both sides reduce to the same expression. Establish `hsec : πA ∘ₗ s = LinearMap.id`.

Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hsA z`. Rewrite using `[LinearMap.comp_apply, hs, LinearMap.id_apply]`. Establish `h0 : πA (dA (r x)) = 0` using `hexA.apply_apply_eq_zero (r x)`. Simplify using `[e, h0]`.

Conclude with `Module.Flat.of_retract s πA hsec`. Establish `hflat : Module.Flat R (P ⧸ LinearMap.range d)` using `Module.flat_of_isLocalized_maximal R (P ⧸ LinearMap.range d) (fun p _ => Localization.AtPrime p ⊗[R] (P ⧸ LinearMap.range d)) (fun p _ => TensorProduct.mk R (Localization.AtPrime p) (P ⧸ LinearMap.range d) 1) (fun p _ => by`. Use `hloc p` as an intermediate fact. Conclude with `Module.Flat.trans R (Localization.AtPrime p) _)`. Establish `hfp : Module.FinitePresentation R (P ⧸ LinearMap.range d)`.

Establish `: Module.FinitePresentation R P` using `Module.finitePresentation_of_projective R P`. Use `Module.finitePresentation_of_surjective (LinearMap.range d).mkQ hsurj ?_` and prove the remaining obligations. Rewrite using `[Submodule.ker_mkQ]`. Conclude with `Module.Finite.iff_fg.mp inferInstance`. Establish `hproj : Module.Projective R (P ⧸ LinearMap.range d)` using `Module.Flat.projective_of_finitePresentation`.

Take `⟨s, hs⟩` from `Module.projective_lifting_property (LinearMap.range d).mkQ LinearMap.id hsurj`. Set `f : P →ₗ[R] P` to `LinearMap.id - s ∘ₗ (LinearMap.range d).mkQ`. Establish `hf : ∀ x, f x ∈ LinearMap.range d`. Introduce `x`. Rewrite using `[← Submodule.ker_mkQ (LinearMap.range d), LinearMap.mem_ker]`.

Use `LinearMap.congr_fun hs ((LinearMap.range d).mkQ x)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Simplify using `only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, this, sub_self]`. Set `g : P →ₗ[R] LinearMap.range d` to `f.codRestrict _ hf`. Establish `hg : ∀ y : LinearMap.range d, f y = y`.

Introduce and unpack `⟨_, y, rfl⟩`. Establish `h0 : (LinearMap.range d).mkQ (d y) = 0` using `hex.apply_apply_eq_zero y`. Simplify using `only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero, sub_zero]`. Establish `hrp : Module.Projective R (LinearMap.range d)` using `Module.Projective.of_split (LinearMap.range d).subtype g (by`. Use extensionality with `y`.

Simplify `hg y)` using `[g]`. Take `⟨t, ht⟩` from `Module.projective_lifting_property d.rangeRestrict LinearMap.id d.surjective_rangeRestrict`. Use `⟨t ∘ₗ g, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Establish `h1 : g (d y) = d.rangeRestrict y`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify `hg (d.rangeRestrict y)` using `[g]`. Establish `h2` using `LinearMap.congr_fun ht (d.rangeRestrict y)`. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at h2`. Establish `h3 : d (t (d.rangeRestrict y)) = d y`.

Use `congrArg Subtype.val h2` as an intermediate fact. Simplify using `using this`. Simplify using `[h1, h3]`.
-/
theorem regular_of_regular_at_maximal : ∀ (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P] [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P), (∀ (p : Ideal R) [p.IsMaximal], ∃ r : Localization.AtPrime p ⊗[R] P →ₗ[Localization.AtPrime p] Localization.AtPrime p ⊗[R] Q, d.baseChange (Localization.AtPrime p) ∘ₗ r ∘ₗ d.baseChange (Localization.AtPrime p) = d.baseChange (Localization.AtPrime p)) → ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by
  intro R Q P _ _ _ _ _ _ _ _ _ d h
  have hex : Function.Exact d (LinearMap.range d).mkQ := LinearMap.exact_map_mkQ_range d
  have hsurj : Function.Surjective (LinearMap.range d).mkQ := Submodule.mkQ_surjective _

  have hloc : ∀ (p : Ideal R) [p.IsMaximal], Module.Flat (Localization.AtPrime p)
      (Localization.AtPrime p ⊗[R] (P ⧸ LinearMap.range d)) := by
    intro p _
    obtain ⟨r, hr⟩ := h p
    set A := Localization.AtPrime p
    set dA := d.baseChange A with hdA
    set πA := (LinearMap.range d).mkQ.baseChange A with hπA
    have hexA : Function.Exact dA πA := by
      have := lTensor_exact A hex hsurj
      simpa [hdA, hπA, LinearMap.baseChange_eq_ltensor] using this
    have hsA : Function.Surjective πA := by
      have := LinearMap.lTensor_surjective A hsurj
      simpa [hπA, LinearMap.baseChange_eq_ltensor] using this
    let e : A ⊗[R] P →ₗ[A] A ⊗[R] P := LinearMap.id - dA ∘ₗ r
    have he : ∀ x ∈ LinearMap.range dA, e x = 0 := by
      rintro _ ⟨y, rfl⟩
      have := LinearMap.congr_fun hr y
      simp only [LinearMap.comp_apply] at this
      simp [e, this]
    let s : A ⊗[R] (P ⧸ LinearMap.range d) →ₗ[A] A ⊗[R] P :=
      ((LinearMap.range dA).liftQ e (fun x hx => he x hx)) ∘ₗ
        (hexA.linearEquivOfSurjective hsA).symm.toLinearMap
    have hs : ∀ x, s (πA x) = e x := by
      intro x
      have : (hexA.linearEquivOfSurjective hsA).symm (πA x) = (LinearMap.range dA).mkQ x := by
        rw [LinearEquiv.symm_apply_eq]
        rfl
      simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
      rfl
    have hsec : πA ∘ₗ s = LinearMap.id := by
      refine LinearMap.ext fun z => ?_
      obtain ⟨x, rfl⟩ := hsA z
      rw [LinearMap.comp_apply, hs, LinearMap.id_apply]
      have h0 : πA (dA (r x)) = 0 := hexA.apply_apply_eq_zero (r x)
      simp [e, h0]
    exact Module.Flat.of_retract s πA hsec
  have hflat : Module.Flat R (P ⧸ LinearMap.range d) :=
    Module.flat_of_isLocalized_maximal R (P ⧸ LinearMap.range d)
      (fun p _ => Localization.AtPrime p ⊗[R] (P ⧸ LinearMap.range d))
      (fun p _ => TensorProduct.mk R (Localization.AtPrime p) (P ⧸ LinearMap.range d) 1)
      (fun p _ => by
        have := hloc p
        exact Module.Flat.trans R (Localization.AtPrime p) _)
  have hfp : Module.FinitePresentation R (P ⧸ LinearMap.range d) := by
    have : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
    refine Module.finitePresentation_of_surjective (LinearMap.range d).mkQ hsurj ?_
    rw [Submodule.ker_mkQ]
    exact Module.Finite.iff_fg.mp inferInstance
  have hproj : Module.Projective R (P ⧸ LinearMap.range d) :=
    Module.Flat.projective_of_finitePresentation
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range d).mkQ LinearMap.id hsurj
  let f : P →ₗ[R] P := LinearMap.id - s ∘ₗ (LinearMap.range d).mkQ
  have hf : ∀ x, f x ∈ LinearMap.range d := by
    intro x
    rw [← Submodule.ker_mkQ (LinearMap.range d), LinearMap.mem_ker]
    have := LinearMap.congr_fun hs ((LinearMap.range d).mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, this,
      sub_self]
  let g : P →ₗ[R] LinearMap.range d := f.codRestrict _ hf
  have hg : ∀ y : LinearMap.range d, f y = y := by
    rintro ⟨_, y, rfl⟩
    have h0 : (LinearMap.range d).mkQ (d y) = 0 := hex.apply_apply_eq_zero y
    simp only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, h0, map_zero,
      sub_zero]
  have hrp : Module.Projective R (LinearMap.range d) :=
    Module.Projective.of_split (LinearMap.range d).subtype g (by
      ext y
      simpa [g] using hg y)
  obtain ⟨t, ht⟩ := Module.projective_lifting_property d.rangeRestrict LinearMap.id
    d.surjective_rangeRestrict
  refine ⟨t ∘ₗ g, ?_⟩
  ext y
  have h1 : g (d y) = d.rangeRestrict y := by
    apply Subtype.ext
    simpa [g] using hg (d.rangeRestrict y)
  have h2 := LinearMap.congr_fun ht (d.rangeRestrict y)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
  have h3 : d (t (d.rangeRestrict y)) = d y := by
    have := congrArg Subtype.val h2
    simpa using this
  simp [h1, h3]

end GlobalTheory.CompanionTheory.RegularLocal
