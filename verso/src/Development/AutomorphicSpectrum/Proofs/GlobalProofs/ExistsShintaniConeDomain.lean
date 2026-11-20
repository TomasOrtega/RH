import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTilingStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniConeDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UniqueReducedOrbitRepresentativeStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PlaceApplyStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsTotallyPositiveBasisPositiveCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyPositiveBasisRatioBoundStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteUnitsBoundedEmbeddingRatioStatement

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani

/- English proof (translation)
Introduce `F _ _ _ 𝔣 h𝔣`. Take `⟨M, hM⟩` from `GlobalTheory.T.exists_congruence_unit_balancing_embeddings F 𝔣 h𝔣`. Take `⟨κ, _, b, hbpos, hbcov⟩` from `GlobalTheory.T.exists_totally_positive_basis_positive_coords F M`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.T.totally_positive_basis_ratio_bound F b hbpos`. Choose the witnesses or unpack the hypotheses as in `⟨σ₁⟩ : Nonempty (F →+* ℝ) := by`.

Establish `w : InfinitePlace F` using `Classical.choice inferInstance`. Conclude with `⟨w.embedding_of_isReal (IsTotallyReal.isReal w)⟩`. Set `G` to `↥(congSubgroup 𝔣)`. Set `φ : G →* F` to `((algebraMap (𝓞 F) F : 𝓞 F →+* F) : 𝓞 F →* F).comp ((Units.coeHom (𝓞 F)).comp (congSubgroup 𝔣).subtype)`. Establish `hφ : ∀ g : G, φ g = (((g : (𝓞 F)ˣ) : 𝓞 F) : F)` using `fun g => rfl`.

Establish `hgpos : ∀ g : G, TotPos F (φ g)` using `fun g => g.2.2`. Set `f : G →* ℝ` to `(σ₁ : F →* ℝ).comp φ`. Establish `hf : ∀ g : G, f g = σ₁ (φ g)` using `fun g => rfl`. Establish `hfpos : ∀ g, 0 < f g` using `fun g => hgpos g σ₁`. Establish `hφinj : Function.Injective φ`.

Introduce `g g' h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `RingOfIntegers.coe_injective h`. Establish `hfinj : Function.Injective f` using `fun g g' h => hφinj (σ₁.injective h)`.

Set `D : Set F` to `{x | ∀ i, 0 < b.repr x i}`. Establish `hDpos : ∀ x ∈ D, TotPos F x`. Introduce `x hx σ`. Establish `hk : Nonempty κ` using `b.index_nonempty`. Rewrite using `[← b.sum_repr x, map_sum]`.

Use `Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty` and prove the remaining obligations. Rewrite using `[Rat.smul_def, map_mul, map_ratCast]`. Conclude with `mul_pos (by exact_mod_cast hx i) (hbpos i σ)`. Establish `hfin : {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite`. Establish `hfin0` using `GlobalTheory.T.finite_units_bounded_embedding_ratio F (R * R)`.

Use `Set.Finite.of_finite_image (f := fun g : G => (g : (𝓞 F)ˣ)) (hfin0.subset ?_) (Subtype.val_injective.injOn)` and prove the remaining obligations. Introduce and unpack `_ ⟨g, ⟨x, hx, hgx⟩, rfl⟩`. Use `⟨hgpos g, fun σ τ => ?_⟩` and prove the remaining obligations. Establish `h1` using `hR _ hgx σ τ`. Establish `h2` using `hR x hx τ σ`.

Establish `hxσ` using `hDpos x hx σ`. Establish `hgτ` using `hgpos g τ`. Rewrite `h1` using `[map_mul, map_mul]`. Establish `h3 : σ (φ g) * σ x ≤ (R * R * τ (φ g)) * σ x`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `le_of_mul_le_mul_right h3 hxσ`. Set `E : Set F` to `{y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D}`. Set `T` to `{g : G | ∃ x ∈ D, φ g * x ∈ D}`. Set `Λ : Set (F →ₗ[ℚ] ℚ)` to `(fun p : G × κ => (b.coord p.2).comp (LinearMap.mulLeft ℚ (φ p.1))) '' (T ×ˢ Set.univ)`. Establish `hΛ : Λ.Finite` using `(hfin.prod Set.finite_univ).image _`.

Establish `hsign : ∀ (p q : ℚ), SignType.sign p = SignType.sign q → 0 < p → 0 < q`. Introduce `p q h hp`. Rewrite `h` using `[sign_pos hp]`. Conclude with `sign_eq_one_iff.mp h.symm`. Establish `htile : Tile ((posCone F : ConvexCone ℚ F) : Set F) (fun _ => True) E`.

Use `GlobalTheory.T.cone_tiling_by_sign_regions (posCone F) b hbpos Λ hΛ E (fun x hx => hx.1) ?_` and prove the remaining obligations. Introduce `x y hx hy hs hxE`. Use `⟨hy, fun g' hg' hyD => ?_⟩` and prove the remaining obligations. Use `hxE.2 g' hg' ?_` and prove the remaining obligations. Establish `hgT : g' ∈ T` using `⟨y, hy, hyD⟩`.

Introduce `i`. Use `hs _ ⟨(g', i), ⟨hgT, trivial⟩, rfl⟩` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.mulLeft_apply] at this`. Conclude with `hsign _ _ this.symm (hyD i)`. Establish `h0 : (0 : F) ∉ E`.

Introduce `h`. Use `hDpos 0 h.1 σ₁` as an intermediate fact. Simplify using `at this`. Take `⟨ι, hι, r, v, hr, hli, hvP, hsub, hun⟩` from `GlobalTheory.T.shintani_cone_decomposition _ _ E htile h0`. Use `⟨ι, hι, r, v, hr, hli, hvP, ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Take `⟨u, hu, hub⟩` from `hM x hx`. Establish `hxD : ∃ g : G, φ g * x ∈ D`. Use `⟨⟨u, hu⟩, hbcov _ ?_ hub⟩` and prove the remaining obligations. Introduce `σ`.

Rewrite using `[map_mul]`. Conclude with `mul_pos (hu.2 σ) (hx σ)`. Take `⟨g, hg, hguniq⟩` from `GlobalTheory.T.unique_reduced_orbit_representative φ f hfpos hfinj D hfin x hxD`. Take `⟨c, hc, hcuniq⟩` from `hun _ hg`. Use `⟨(⟨g.1, g.2⟩, c), hc, ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨⟨u', hu'⟩, c'⟩ hp`. Establish `hp' : φ ⟨u', hu'⟩ * x ∈ openCone (v c')` using `hp`. Establish `hg' : (⟨u', hu'⟩ : G) = g` using `hguniq _ (hsub c' hp')`. Establish `hc' : c' = c`. Apply `hcuniq` to reduce the goal to its premises.

Rewrite using `[← hg']`. Conclude with `hp'`. Substitute `hc'` using the available equality. Use `congrArg Subtype.val hg'` as an intermediate fact. Simplify using `only at this`.

Simplify using `[this]`.
-/
theorem exists_coneDomain : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔣 : Ideal (𝓞 F)), 𝔣 ≠ ⊥ →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), IsConeDomain 𝔣 r v := by
  intro F _ _ _ 𝔣 h𝔣
  classical
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_congruence_unit_balancing_embeddings F 𝔣 h𝔣
  obtain ⟨κ, _, b, hbpos, hbcov⟩ := GlobalTheory.T.exists_totally_positive_basis_positive_coords F M
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.totally_positive_basis_ratio_bound F b hbpos

  obtain ⟨σ₁⟩ : Nonempty (F →+* ℝ) := by
    have w : InfinitePlace F := Classical.choice inferInstance
    exact ⟨w.embedding_of_isReal (IsTotallyReal.isReal w)⟩

  let G := ↥(congSubgroup 𝔣)
  let φ : G →* F := ((algebraMap (𝓞 F) F : 𝓞 F →+* F) : 𝓞 F →* F).comp ((Units.coeHom (𝓞 F)).comp (congSubgroup 𝔣).subtype)
  have hφ : ∀ g : G, φ g = (((g : (𝓞 F)ˣ) : 𝓞 F) : F) := fun g => rfl
  have hgpos : ∀ g : G, TotPos F (φ g) := fun g => g.2.2
  let f : G →* ℝ := (σ₁ : F →* ℝ).comp φ
  have hf : ∀ g : G, f g = σ₁ (φ g) := fun g => rfl
  have hfpos : ∀ g, 0 < f g := fun g => hgpos g σ₁
  have hφinj : Function.Injective φ := by
    intro g g' h
    apply Subtype.ext
    apply Units.ext
    exact RingOfIntegers.coe_injective h
  have hfinj : Function.Injective f := fun g g' h => hφinj (σ₁.injective h)
  let D : Set F := {x | ∀ i, 0 < b.repr x i}

  have hDpos : ∀ x ∈ D, TotPos F x := by
    intro x hx σ
    have hk : Nonempty κ := b.index_nonempty
    rw [← b.sum_repr x, map_sum]
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_pos (by exact_mod_cast hx i) (hbpos i σ)
  have hfin : {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite := by
    have hfin0 := GlobalTheory.T.finite_units_bounded_embedding_ratio F (R * R)
    refine Set.Finite.of_finite_image (f := fun g : G => (g : (𝓞 F)ˣ)) (hfin0.subset ?_) (Subtype.val_injective.injOn)
    rintro _ ⟨g, ⟨x, hx, hgx⟩, rfl⟩
    refine ⟨hgpos g, fun σ τ => ?_⟩
    have h1 := hR _ hgx σ τ
    have h2 := hR x hx τ σ
    have hxσ := hDpos x hx σ
    have hgτ := hgpos g τ
    rw [map_mul, map_mul] at h1
    have h3 : σ (φ g) * σ x ≤ (R * R * τ (φ g)) * σ x := by
      calc σ (φ g) * σ x ≤ R * (τ (φ g) * τ x) := h1
        _ ≤ R * (τ (φ g) * (R * σ x)) := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right h3 hxσ
  let E : Set F := {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D}
  let T := {g : G | ∃ x ∈ D, φ g * x ∈ D}
  let Λ : Set (F →ₗ[ℚ] ℚ) := (fun p : G × κ => (b.coord p.2).comp (LinearMap.mulLeft ℚ (φ p.1))) '' (T ×ˢ Set.univ)
  have hΛ : Λ.Finite := (hfin.prod Set.finite_univ).image _
  have hsign : ∀ (p q : ℚ), SignType.sign p = SignType.sign q → 0 < p → 0 < q := by
    intro p q h hp
    rw [sign_pos hp] at h
    exact sign_eq_one_iff.mp h.symm
  have htile : Tile ((posCone F : ConvexCone ℚ F) : Set F) (fun _ => True) E := by
    refine GlobalTheory.T.cone_tiling_by_sign_regions (posCone F) b hbpos Λ hΛ E (fun x hx => hx.1) ?_
    intro x y hx hy hs hxE
    refine ⟨hy, fun g' hg' hyD => ?_⟩
    refine hxE.2 g' hg' ?_
    have hgT : g' ∈ T := ⟨y, hy, hyD⟩
    intro i
    have := hs _ ⟨(g', i), ⟨hgT, trivial⟩, rfl⟩
    simp only [LinearMap.comp_apply, Module.Basis.coord_apply, LinearMap.mulLeft_apply] at this
    exact hsign _ _ this.symm (hyD i)
  have h0 : (0 : F) ∉ E := by
    intro h
    have := hDpos 0 h.1 σ₁
    simp at this
  obtain ⟨ι, hι, r, v, hr, hli, hvP, hsub, hun⟩ := GlobalTheory.T.shintani_cone_decomposition _ _ E htile h0
  refine ⟨ι, hι, r, v, hr, hli, hvP, ?_⟩
  intro x hx

  obtain ⟨u, hu, hub⟩ := hM x hx
  have hxD : ∃ g : G, φ g * x ∈ D := by
    refine ⟨⟨u, hu⟩, hbcov _ ?_ hub⟩
    intro σ
    rw [map_mul]
    exact mul_pos (hu.2 σ) (hx σ)
  obtain ⟨g, hg, hguniq⟩ := GlobalTheory.T.unique_reduced_orbit_representative φ f hfpos hfinj D hfin x hxD
  obtain ⟨c, hc, hcuniq⟩ := hun _ hg
  refine ⟨(⟨g.1, g.2⟩, c), hc, ?_⟩
  rintro ⟨⟨u', hu'⟩, c'⟩ hp
  have hp' : φ ⟨u', hu'⟩ * x ∈ openCone (v c') := hp
  have hg' : (⟨u', hu'⟩ : G) = g := hguniq _ (hsub c' hp')
  have hc' : c' = c := by
    apply hcuniq
    rw [← hg']
    exact hp'
  subst hc'
  have := congrArg Subtype.val hg'
  simp only at this
  simp [this]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani
