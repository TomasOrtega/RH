import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupClosedFibreFinsetInAffineOpenStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Establish `hiso : ∀ σ, IsIso (act σ)` using `fun σ => ⟨act σ⁻¹, by rw [← act_mul, mul_inv_cancel, act_one], by rw [← act_mul, inv_mul_cancel, act_one]⟩`. Establish `hmul : ∀ σ τ (x : X), act (σ * τ) x = act τ (act σ x)` using `fun σ τ x => by`. Rewrite using `[act_mul, Scheme.Hom.comp_apply]`. Establish `hone : ∀ x : X, act 1 x = x` using `fun x => by rw [act_one]; rfl`. Establish `hW : ∀ z : Z, ∃ V : X.Opens, IsAffineOpen V ∧ z.1 ∈ V ∧ ∀ σ, ∀ x ∈ V, act σ x ∈ V`.

Introduce `z`. Take `⟨O, hO, hz⟩` from `horb z.1 z.2`. Establish `hmem : ∀ x : X, x ∈ (⨅ σ, act σ ⁻¹ᵁ O) ↔ ∀ σ, act σ x ∈ O` using `fun x => by`. Rewrite using `[← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]`. Both sides reduce to the same expression.

Use `⟨⨅ σ, act σ ⁻¹ᵁ O, IsAffineOpen.iInf fun σ => ?_, (hmem _).2 hz, fun σ x hx => (hmem _).2 fun τ => ?_⟩` and prove the remaining obligations. Use `hiso σ` as an intermediate fact. Conclude with `hO.preimage (act σ)`. Rewrite using `[← hmul]`. Conclude with `(hmem _).1 hx _`.

Use `choose V hV hzV hVa using hW`. Take `⟨t, ht⟩` from `hZ.elim_finite_subcover (fun z : Z => (V z : Set X)) (fun z => (V z).isOpen) (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩)`. Establish `hH : ∀ x : X, x ∈ (⨆ z ∈ t, V z) ↔ ∃ z ∈ t, x ∈ V z` using `fun x => by`. Simplify using `[TopologicalSpace.Opens.mem_iSup]`. Use `⟨⨆ z ∈ t, V z, fun σ => ?_, fun z hz => ?_, ?_, fun x hx => ?_⟩` and prove the remaining obligations.

Use extensionality with `x`. Express the relevant statement in the definitionally equal form `act σ x ∈ (⨆ z ∈ t, V z) ↔ x ∈ (⨆ z ∈ t, V z)`. Rewrite using `[hH, hH]`. Use `⟨fun ⟨z, hz, hx⟩ => ⟨z, hz, ?_⟩, fun ⟨z, hz, hx⟩ => ⟨z, hz, hVa z σ x hx⟩⟩` and prove the remaining obligations. Use `hVa z σ⁻¹ _ hx` as an intermediate fact.

Rewrite `this` using `[← hmul, mul_inv_cancel, hone]`. Then use the resulting hypothesis. Rewrite using `[hH]`. Simplify using `using ht hz`. Establish `: ((⨆ z ∈ t, V z : X.Opens) : Set X) = ⋃ z ∈ t, (V z : Set X)`. Use extensionality with `x`.

Rewrite using `[SetLike.mem_coe, hH]`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `t.isCompact_biUnion fun z _ => (hV z).isCompact`. Take `⟨z, hz, hx⟩` from `(hH x).1 hx`.

Conclude with `⟨V z, hV z, fun y hy => (hH y).2 ⟨z, hz, hy⟩, fun σ => hVa z σ x hx⟩`.
-/
theorem exists_invariant_nbhd_of_orbits {X : Scheme.{0}} [X.IsSeparated] {Γ : Type} [Group Γ] [Finite Γ]
    (act : Γ → (X ⟶ X)) (act_one : act 1 = 𝟙 X) (act_mul : ∀ σ τ, act (σ * τ) = act σ ≫ act τ)
    (Z : Set X) (hZ : IsCompact Z)
    (horb : ∀ z ∈ Z, ∃ O : X.Opens, IsAffineOpen O ∧ ∀ σ, act σ z ∈ O) :
    ∃ H : X.Opens, (∀ σ, act σ ⁻¹ᵁ H = H) ∧ (∀ z ∈ Z, z ∈ H) ∧ IsCompact (H : Set X) ∧
      (∀ x ∈ H, ∃ O : X.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, act σ x ∈ O) := by
  classical
  have hiso : ∀ σ, IsIso (act σ) := fun σ =>
    ⟨act σ⁻¹, by rw [← act_mul, mul_inv_cancel, act_one], by rw [← act_mul, inv_mul_cancel, act_one]⟩
  have hmul : ∀ σ τ (x : X), act (σ * τ) x = act τ (act σ x) := fun σ τ x => by
    rw [act_mul, Scheme.Hom.comp_apply]
  have hone : ∀ x : X, act 1 x = x := fun x => by rw [act_one]; rfl
  have hW : ∀ z : Z, ∃ V : X.Opens, IsAffineOpen V ∧ z.1 ∈ V ∧ ∀ σ, ∀ x ∈ V, act σ x ∈ V := by
    intro z
    obtain ⟨O, hO, hz⟩ := horb z.1 z.2
    have hmem : ∀ x : X, x ∈ (⨅ σ, act σ ⁻¹ᵁ O) ↔ ∀ σ, act σ x ∈ O := fun x => by
      rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
      rfl
    refine ⟨⨅ σ, act σ ⁻¹ᵁ O, IsAffineOpen.iInf fun σ => ?_, (hmem _).2 hz, fun σ x hx => (hmem _).2 fun τ => ?_⟩
    · have := hiso σ
      exact hO.preimage (act σ)
    · rw [← hmul]
      exact (hmem _).1 hx _
  choose V hV hzV hVa using hW
  obtain ⟨t, ht⟩ := hZ.elim_finite_subcover (fun z : Z => (V z : Set X)) (fun z => (V z).isOpen)
    (fun z hz => Set.mem_iUnion.2 ⟨⟨z, hz⟩, hzV ⟨z, hz⟩⟩)
  have hH : ∀ x : X, x ∈ (⨆ z ∈ t, V z) ↔ ∃ z ∈ t, x ∈ V z := fun x => by
    simp [TopologicalSpace.Opens.mem_iSup]
  refine ⟨⨆ z ∈ t, V z, fun σ => ?_, fun z hz => ?_, ?_, fun x hx => ?_⟩
  · ext x
    change act σ x ∈ (⨆ z ∈ t, V z) ↔ x ∈ (⨆ z ∈ t, V z)
    rw [hH, hH]
    refine ⟨fun ⟨z, hz, hx⟩ => ⟨z, hz, ?_⟩, fun ⟨z, hz, hx⟩ => ⟨z, hz, hVa z σ x hx⟩⟩
    have := hVa z σ⁻¹ _ hx
    rwa [← hmul, mul_inv_cancel, hone] at this
  · rw [hH]
    simpa using ht hz
  · have : ((⨆ z ∈ t, V z : X.Opens) : Set X) = ⋃ z ∈ t, (V z : Set X) := by
      ext x
      rw [SetLike.mem_coe, hH]
      simp
    rw [this]
    exact t.isCompact_biUnion fun z _ => (hV z).isCompact
  · obtain ⟨z, hz, hx⟩ := (hH x).1 hx
    exact ⟨V z, hV z, fun y hy => (hH y).2 ⟨z, hz, hy⟩, fun σ => hVa z σ x hx⟩

/- English proof (translation)
Establish `h₁ : Ideal.comap ρ (PrimeSpectrum.asIdeal p) = maximalIdeal R` using `congrArg PrimeSpectrum.asIdeal hp`. Establish `h₂ : (PrimeSpectrum.asIdeal p).IsMaximal`. Use `PrimeSpectrum.isPrime p` as an intermediate fact. Use `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hρ.to_isIntegral _ ?_` and prove the remaining obligations. Rewrite using `[h₁]`.

Use `infer_instance`. Conclude with `PrimeSpectrum.ext (eq_maximalIdeal h₂)`.
-/
theorem eq_closedPoint_of_finite {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    {ρ : R →+* R'} (hρ : ρ.Finite) (p : Sp R') (hp : spMap ρ p = closedPoint R) : p = closedPoint R' := by
  have h₁ : Ideal.comap ρ (PrimeSpectrum.asIdeal p) = maximalIdeal R := congrArg PrimeSpectrum.asIdeal hp
  have h₂ : (PrimeSpectrum.asIdeal p).IsMaximal := by
    have := PrimeSpectrum.isPrime p
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hρ.to_isIntegral _ ?_
    rw [h₁]
    infer_instance
  exact PrimeSpectrum.ext (eq_maximalIdeal h₂)

/- English proof (translation)
Introduce `R _ _ _ hR R' _ _ _ ρ hρ hG D D' hD A' G' _ _ hS U' a`. Use `hR.2` as an intermediate fact. Establish `hR' : Base R'` using `⟨hρ.1, charZero_of_injective_ringHom hρ.2.1⟩`. Use `hG.1` as an intermediate fact. Use `Fintype.ofFinite (Gal ρ)` as an intermediate fact.

Use `hS.separated` as an intermediate fact. Use `hS.quasiCompact` as an intermediate fact. Establish `: G'.left.IsSeparated` using `⟨by`. Rewrite using `[← terminal.comp_from G'.hom]`. Use the proof step `infer_instance⟩`.

Establish `: CompactSpace G'.left` using `QuasiCompact.compactSpace_of_compactSpace G'.hom`. Establish `hover : ∀ (σ : Gal ρ) (g : G'.left), spMap ρ (G'.hom (a.act σ g)) = spMap ρ (G'.hom g)` using `fun σ g => by`. Establish `h₁ : a.act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ)` using `(a.cart σ).1.w`. Establish `h₂ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ`. Rewrite using `[← Spec.map_comp]`.

Use `congr 1`. Use extensionality with `r`. Conclude with `σ.2 r`. Rewrite using `[← Scheme.Hom.comp_apply (a.act σ), h₁, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (spMap (Gal.hom σ)), h₂]`. Establish `hZ : IsClosed {g : G'.left | spMap ρ (G'.hom g) = closedPoint R}` using `(isClosed_singleton_closedPoint R).preimage ((spMap ρ).continuous.comp G'.hom.continuous)`.

Use `exists_invariant_nbhd_of_orbits a.act a.act_one a.act_mul _ hZ.isCompact fun z hz => ?_` and prove the remaining obligations. Take `⟨O, hO, h⟩` from `GlobalTheory.T.uniformisedGroup_closedFibre_finset_in_affineOpen R' hR' D' A' G' hS U' (Finset.univ.image fun σ => a.act σ z) (fun x hx => by`. Take `⟨σ, -, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `eq_closedPoint_of_finite hρ.2.2 _ ((hover σ z).trans hz))`. Conclude with `⟨O, hO, fun σ => h _ (Finset.mem_image.2 ⟨σ, Finset.mem_univ _, rfl⟩)⟩`.
-/
theorem exists_invariant_nbhd_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U'), ∃ H : G'.left.Opens, (∀ σ, a.act σ ⁻¹ᵁ H = H) ∧ (∀ g : G'.left, spMap ρ (G'.hom g) = closedPoint R → g ∈ H) ∧ IsCompact (H : Set G'.left) ∧ (∀ x ∈ H, ∃ O : G'.left.Opens, IsAffineOpen O ∧ O ≤ H ∧ ∀ σ, a.act σ x ∈ O) := by
  intro R _ _ _ hR R' _ _ _ ρ hρ hG D D' hD A' G' _ _ hS U' a
  classical
  have := hR.2
  have hR' : Base R' := ⟨hρ.1, charZero_of_injective_ringHom hρ.2.1⟩
  have := hG.1
  have := Fintype.ofFinite (Gal ρ)
  have := hS.separated
  have := hS.quasiCompact
  have : G'.left.IsSeparated := ⟨by
    rw [← terminal.comp_from G'.hom]
    infer_instance⟩
  have : CompactSpace G'.left := QuasiCompact.compactSpace_of_compactSpace G'.hom
  have hover : ∀ (σ : Gal ρ) (g : G'.left), spMap ρ (G'.hom (a.act σ g)) = spMap ρ (G'.hom g) := fun σ g => by
    have h₁ : a.act σ ≫ G'.hom = G'.hom ≫ spMap (Gal.hom σ) := (a.cart σ).1.w
    have h₂ : spMap (Gal.hom σ) ≫ spMap ρ = spMap ρ := by
      rw [← Spec.map_comp]
      congr 1
      ext r
      exact σ.2 r
    rw [← Scheme.Hom.comp_apply (a.act σ), h₁, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (spMap (Gal.hom σ)), h₂]
  have hZ : IsClosed {g : G'.left | spMap ρ (G'.hom g) = closedPoint R} :=
    (isClosed_singleton_closedPoint R).preimage ((spMap ρ).continuous.comp G'.hom.continuous)
  refine exists_invariant_nbhd_of_orbits a.act a.act_one a.act_mul _ hZ.isCompact fun z hz => ?_
  obtain ⟨O, hO, h⟩ := GlobalTheory.T.uniformisedGroup_closedFibre_finset_in_affineOpen R' hR' D' A' G' hS U' (Finset.univ.image fun σ => a.act σ z) (fun x hx => by
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 hx
    exact eq_closedPoint_of_finite hρ.2.2 _ ((hover σ z).trans hz))
  exact ⟨O, hO, fun σ => h _ (Finset.mem_image.2 ⟨σ, Finset.mem_univ _, rfl⟩)⟩

end GlobalTheory.Mum
