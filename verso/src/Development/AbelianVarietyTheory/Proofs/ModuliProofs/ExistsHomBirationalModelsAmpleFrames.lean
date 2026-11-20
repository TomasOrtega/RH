import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLiftOfDensePart
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapIdOfCommonGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelObjectDescendsFgSubfield
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocallyQuasiFiniteOfTrivialOnFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleIsoOfAmpleDeterminantFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.AmpUniq

/- English proof (translation)
Use `(isNoetherianRing_iff_ideal_fg B).2 fun J => ?_` and prove the remaining obligations. Establish `e : (J.comap f).map f = J`. Use `le_antisymm Ideal.map_comap_le fun b hb => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Establish `hne : ((J.comap f).map f).colon {b} ≠ ⊤` using `fun h => hn (by`.

Establish `h1 : (1 : B) ∈ ((J.comap f).map f).colon {b}` using `h ▸ Submodule.mem_top`. Simplify using `using Submodule.mem_colon_singleton.1 h1)`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Take `⟨x, r, c, hc, hr, hx⟩` from `RingHom.surjectiveOnStalks_iff_forall_maximal'.1 hf P hP b`. Set `p : PrimeSpectrum B` to `⟨P, hP.isPrime⟩`.

Take `⟨U, hU, hUc⟩` from `hi.isOpen_iff.1 (PrimeSpectrum.basicOpen c).isOpen`. Establish `hpU : PrimeSpectrum.comap f p ∈ U`. Establish `: p ∈ PrimeSpectrum.comap f ⁻¹' U` using `hUc ▸ hc`. Conclude with `this`. Take `⟨_, ⟨a, rfl⟩, ha, haU⟩` from `PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU`.

Establish `hac : PrimeSpectrum.basicOpen (f a) ≤ PrimeSpectrum.basicOpen c` using `fun q hq => by`. Establish `: q ∈ PrimeSpectrum.comap f ⁻¹' U` using `haU hq`. Conclude with `hUc.subset this`. Take `⟨n, hn⟩` from `(PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 hac`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton'.1 hn`.

Establish `key : f (a ^ n * r) * b = f (a ^ n * x)`. Rewrite using `[map_mul, map_mul, map_pow, ← hd]`. Take the linear combination `d * hx`. Establish `hmem : f (a ^ n * r) ∈ P` using `hle (Submodule.mem_colon_singleton.2 (by`. Rewrite using `[smul_eq_mul, key]`.

Conclude with `Ideal.mem_map_of_mem f (Ideal.mem_comap.2 (key ▸ J.mul_mem_left _ hb))))`. Rewrite `hmem` using `[map_mul, map_pow]`. Break down `hP.isPrime.mem_or_mem hmem with h | h` into its components or cases. Conclude with `ha (hP.isPrime.mem_of_pow_mem n h)`. Conclude with `hr h`.

Rewrite using `[← e]`. Conclude with `Ideal.FG.map (IsNoetherian.noetherian _) f`.
-/
theorem isNoetherianRing_of_isInducing {A B : Type*} [CommRing A] [CommRing B] [IsNoetherianRing A]
    (f : A →+* B) (hi : Topology.IsInducing (PrimeSpectrum.comap f)) (hf : f.SurjectiveOnStalks) :
    IsNoetherianRing B := by
  refine (isNoetherianRing_iff_ideal_fg B).2 fun J => ?_
  have e : (J.comap f).map f = J := by
    refine le_antisymm Ideal.map_comap_le fun b hb => ?_
    by_contra hn
    have hne : ((J.comap f).map f).colon {b} ≠ ⊤ := fun h => hn (by
      have h1 : (1 : B) ∈ ((J.comap f).map f).colon {b} := h ▸ Submodule.mem_top
      simpa using Submodule.mem_colon_singleton.1 h1)
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨x, r, c, hc, hr, hx⟩ := RingHom.surjectiveOnStalks_iff_forall_maximal'.1 hf P hP b
    let p : PrimeSpectrum B := ⟨P, hP.isPrime⟩
    obtain ⟨U, hU, hUc⟩ := hi.isOpen_iff.1 (PrimeSpectrum.basicOpen c).isOpen
    have hpU : PrimeSpectrum.comap f p ∈ U := by
      have : p ∈ PrimeSpectrum.comap f ⁻¹' U := hUc ▸ hc
      exact this
    obtain ⟨_, ⟨a, rfl⟩, ha, haU⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hpU hU
    have hac : PrimeSpectrum.basicOpen (f a) ≤ PrimeSpectrum.basicOpen c := fun q hq => by
      have : q ∈ PrimeSpectrum.comap f ⁻¹' U := haU hq
      exact hUc.subset this
    obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 hac
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hn
    have key : f (a ^ n * r) * b = f (a ^ n * x) := by
      rw [map_mul, map_mul, map_pow, ← hd]
      linear_combination d * hx
    have hmem : f (a ^ n * r) ∈ P := hle (Submodule.mem_colon_singleton.2 (by
      rw [smul_eq_mul, key]
      exact Ideal.mem_map_of_mem f (Ideal.mem_comap.2 (key ▸ J.mul_mem_left _ hb))))
    rw [map_mul, map_pow] at hmem
    rcases hP.isPrime.mem_or_mem hmem with h | h
    · exact ha (hP.isPrime.mem_of_pow_mem n h)
    · exact hr h
  rw [← e]
  exact Ideal.FG.map (IsNoetherian.noetherian _) f

/- English proof (translation)
Establish `H (w : W) : ∃ V : W.affineOpens, w ∈ V.1 ∧ IsNoetherianRing Γ(W, V)`. Take `⟨_, ⟨U, hU, rfl⟩, hw, -⟩` from `Z.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (j w)) isOpen_univ`. Take `⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩` from `W.isBasis_affineOpens.exists_subset_of_mem_open (show w ∈ (j ⁻¹ᵁ U : Set W) from hw) (j ⁻¹ᵁ U).isOpen`. Establish `hU' : IsAffineOpen U` using `hU`. Establish `hV' : IsAffineOpen V` using `hV`.

Establish `e` using `IsAffineOpen.SpecMap_appLE_fromSpec j hU' hV' hVU`. Establish `: IsPreimmersion (Spec.map (j.appLE U V hVU) ≫ hU'.fromSpec)`. Rewrite using `[e]`. Use `infer_instance`. Establish `h` using `(IsPreimmersion.SpecMap_iff _).1 (IsPreimmersion.of_comp (Spec.map (j.appLE U V hVU)) hU'.fromSpec)`.

Establish `: IsNoetherianRing Γ(Z, U)` using `IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Conclude with `⟨⟨V, hV⟩, hwV, isNoetherianRing_of_isInducing _ h.1.isInducing h.2⟩`. Use `choose V hV hN using H`. Conclude with `isLocallyNoetherian_of_affine_cover (S := V) (top_le_iff.1 fun w _ => TopologicalSpace.Opens.mem_iSup.2 ⟨w, hV w⟩) hN`.
-/
theorem isLocallyNoetherian_of_isPreimmersion {W Z : Scheme.{0}} (j : W ⟶ Z) [IsPreimmersion j]
    [IsLocallyNoetherian Z] : IsLocallyNoetherian W := by
  have H (w : W) : ∃ V : W.affineOpens, w ∈ V.1 ∧ IsNoetherianRing Γ(W, V) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hw, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (j w)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hwV, hVU⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show w ∈ (j ⁻¹ᵁ U : Set W) from hw) (j ⁻¹ᵁ U).isOpen
    have hU' : IsAffineOpen U := hU
    have hV' : IsAffineOpen V := hV
    have e := IsAffineOpen.SpecMap_appLE_fromSpec j hU' hV' hVU
    have : IsPreimmersion (Spec.map (j.appLE U V hVU) ≫ hU'.fromSpec) := by
      rw [e]; infer_instance
    have h := (IsPreimmersion.SpecMap_iff _).1 (IsPreimmersion.of_comp (Spec.map (j.appLE U V hVU)) hU'.fromSpec)
    have : IsNoetherianRing Γ(Z, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact ⟨⟨V, hV⟩, hwV, isNoetherianRing_of_isInducing _ h.1.isInducing h.2⟩
  choose V hV hN using H
  exact isLocallyNoetherian_of_affine_cover (S := V)
    (top_le_iff.1 fun w _ => TopologicalSpace.Opens.mem_iSup.2 ⟨w, hV w⟩) hN

/- English proof (translation)
The claim follows from `SurjectiveOnStalks.of_comp u p isEmbedding := Topology.IsEmbedding.of_comp u.continuous p.continuous (u ≫ p).isEmbedding`.
-/
theorem isPreimmersion_of_comp {W Z Y : Scheme.{0}} (u : W ⟶ Z) (p : Z ⟶ Y) [IsPreimmersion (u ≫ p)] :
    IsPreimmersion u where
  toSurjectiveOnStalks := SurjectiveOnStalks.of_comp u p
  isEmbedding := Topology.IsEmbedding.of_comp u.continuous p.continuous (u ≫ p).isEmbedding

/- English proof (translation)
Use `Flat.of_stalkMap u fun w => RingHom.Flat.of_bijective ⟨?_, u.stalkMap_surjective w⟩` and prove the remaining obligations. Use `(injective_iff_map_eq_zero _).2 fun a ha => ?_` and prove the remaining obligations. Take `⟨V, hV, s, rfl⟩` from `Z.presheaf.exists_germ_eq a`. Rewrite `ha` using `[Scheme.Hom.germ_stalkMap_apply]`. Take `⟨T, hT, iT, iT', hs⟩` from `W.presheaf.germ_eq (U := u ⁻¹ᵁ V) (V := u ⁻¹ᵁ V) w hV hV (u.app V s) 0 (by rw [ha, map_zero])`.

Take `⟨T', hT', hTT'⟩` from `u.isEmbedding.isInducing.isOpen_iff.1 T.isOpen`. Set `V' : Z.Opens` to `V ⊓ ⟨T', hT'⟩`. Establish `hw : u w ∈ V'` using `⟨hV, by`. Establish `: w ∈ u ⁻¹' T'` using `hTT' ▸ hT`. Conclude with `this⟩`.

Establish `hle : u ⁻¹ᵁ V' ≤ T` using `fun x hx => by`. Establish `: x ∈ u ⁻¹' T'` using `hx.2`. Conclude with `hTT'.subset this`. Establish `h0 : Z.presheaf.map (homOfLE (inf_le_left : V' ≤ V)).op s = 0`. Apply `u.app_injective V'` to reduce the goal to its premises.

Rewrite using `[map_zero, ← CommRingCat.comp_apply, u.naturality, CommRingCat.comp_apply]`. Use `congrArg (W.presheaf.map (homOfLE hle).op) hs` as an intermediate fact. Rewrite `this` using `[map_zero, map_zero, ← CommRingCat.comp_apply, ← Functor.map_comp]`. Conclude with `this`. Rewrite using `[← Z.presheaf.germ_res_apply (homOfLE (inf_le_left : V' ≤ V)) (u w) hw, h0, map_zero]`.
-/
theorem flat_of_isPreimmersion {W Z : Scheme.{0}} (u : W ⟶ Z) [IsPreimmersion u] [QuasiCompact u]
    [IsSchemeTheoreticallyDominant u] : Flat u := by
  refine Flat.of_stalkMap u fun w => RingHom.Flat.of_bijective ⟨?_, u.stalkMap_surjective w⟩
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨V, hV, s, rfl⟩ := Z.presheaf.exists_germ_eq a
  rw [Scheme.Hom.germ_stalkMap_apply] at ha
  obtain ⟨T, hT, iT, iT', hs⟩ := W.presheaf.germ_eq (U := u ⁻¹ᵁ V) (V := u ⁻¹ᵁ V) w hV hV (u.app V s) 0
    (by rw [ha, map_zero])
  obtain ⟨T', hT', hTT'⟩ := u.isEmbedding.isInducing.isOpen_iff.1 T.isOpen
  let V' : Z.Opens := V ⊓ ⟨T', hT'⟩
  have hw : u w ∈ V' := ⟨hV, by
    have : w ∈ u ⁻¹' T' := hTT' ▸ hT
    exact this⟩
  have hle : u ⁻¹ᵁ V' ≤ T := fun x hx => by
    have : x ∈ u ⁻¹' T' := hx.2
    exact hTT'.subset this
  have h0 : Z.presheaf.map (homOfLE (inf_le_left : V' ≤ V)).op s = 0 := by
    apply u.app_injective V'
    rw [map_zero, ← CommRingCat.comp_apply, u.naturality, CommRingCat.comp_apply]
    have := congrArg (W.presheaf.map (homOfLE hle).op) hs
    rw [map_zero, map_zero, ← CommRingCat.comp_apply, ← Functor.map_comp] at this
    exact this
  rw [← Z.presheaf.germ_res_apply (homOfLE (inf_le_left : V' ≤ V)) (u w) hw, h0, map_zero]

def chartPullPowSingle {X : Scheme.{0}} (L : LB X) (n : ℕ) :
    ChartPull (lbPow L n) (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => (n : ℤ))) (𝟙 X) where
  idx J := fun _ => J PUnit.unit
  le _ _ hy := Set.mem_iInter.2 fun _ => mem_powChart.1 hy
  g y J J' hJ hJ' := by
    have h₁ := mem_powChart.1 hJ
    have h₂ := mem_powChart.1 hJ'
    refine (gm_lbPow_g n (𝟙 X) y J J' hJ hJ').trans (Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => 𝟙 X)
      (fun _ => (n : ℤ)) (𝟙 X) y _ _ (Set.mem_iInter.2 fun _ => h₁) (Set.mem_iInter.2 fun _ => h₂)).symm)
    simp

/- English proof (translation)
Take `⟨d, s, -, hx, hs⟩` from `ha (q x)`. Establish `hq` using `pull_isLB hA q`. Establish `e₁` using `nonzeroLocus_chartSec_id (chartPullPowSingle A d) s fun y J hJ => ⟨fun _ => J 0, mem_powChart.2 (Set.mem_iInter.1 hJ 0)⟩`. Take `⟨t, ht⟩` from `exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_linComb hq _ _) (isLB_lbPow (pull_isLB hq _) d) (lbIso_lbPow_finPow hq (𝟙 X) d).symm (secPowPull (secPowPull (chartSec (chartPullPowSingle A d) s) q) (𝟙 X))`. Rewrite `ht` using `[nonzeroLocus_secPowPull, nonzeroLocus_secPowPull, e₁]`.

Use `⟨d, t, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ht]`. Conclude with `hx`. Rewrite using `[ht]`. Conclude with `hs.preimage q`.
-/
theorem exists_affine_locus_pull {X Y : Scheme.{0}} {A : LB Y} (hA : A.IsLB)
    (ha : ∀ y : Y, ∃ (d : ℕ) (s : Out.H0 A d), 1 ≤ d ∧ y ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s))
    (q : X ⟶ Y) [IsAffineHom q] (x : X) :
    ∃ (d : ℕ) (s : LB.Sec (LB.LinComb (A.pull q) (K := Fin d) (fun _ => 𝟙 X) (fun _ => 1))),
      x ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s) := by
  obtain ⟨d, s, -, hx, hs⟩ := ha (q x)
  have hq := pull_isLB hA q
  have e₁ := nonzeroLocus_chartSec_id (chartPullPowSingle A d) s fun y J hJ =>
    ⟨fun _ => J 0, mem_powChart.2 (Set.mem_iInter.1 hJ 0)⟩
  obtain ⟨t, ht⟩ := exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_linComb hq _ _)
    (isLB_lbPow (pull_isLB hq _) d) (lbIso_lbPow_finPow hq (𝟙 X) d).symm
    (secPowPull (secPowPull (chartSec (chartPullPowSingle A d) s) q) (𝟙 X))
  rw [nonzeroLocus_secPowPull, nonzeroLocus_secPowPull, e₁] at ht
  refine ⟨d, t, ?_, ?_⟩
  · rw [ht]; exact hx
  · rw [ht]; exact hs.preimage q

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Establish `: LocallyQuasiFinite (ν ≫ pullback.fst s₁ s₂)`. Use `(IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyQuasiFinite) Z₁.affineCover).2 fun i => ?_` and prove the remaining obligations. Set `g` to `Z₁.affineCover.f i`. Set `p` to `ν ≫ pullback.fst s₁ s₂`. Set `q` to `pullback.fst p g ≫ ν ≫ pullback.snd s₁ s₂`.

Express the relevant statement in the definitionally equal form `LocallyQuasiFinite (pullback.snd p g)`. Establish `hq : IsAffineHom q`. Set `m : pullback (g ≫ s₁) s₂ ⟶ pullback s₁ s₂` to `pullback.map _ _ _ _ g (𝟙 _) (𝟙 _) (by simp) (by simp)`. Establish `hm : IsPullback m (pullback.fst _ _) (pullback.fst s₁ s₂) g`. Use `IsPullback.of_right (h₁₂ := pullback.snd s₁ s₂) (v₁₃ := s₂) (h₂₂ := s₁) ?_ (by simp [m]) (IsPullback.of_hasPullback s₁ s₂).flip` and prove the remaining obligations.

Establish `: m ≫ pullback.snd s₁ s₂ = pullback.snd _ _` using `by simp [m]`. Rewrite using `[this]`. Conclude with `(IsPullback.of_hasPullback (g ≫ s₁) s₂).flip`. Set `l : pullback p g ⟶ pullback (g ≫ s₁) s₂` to `hm.lift (pullback.fst p g ≫ ν) (pullback.snd p g) (by simpa [p] using pullback.condition (f := p) (g := g))`. Establish `hl : IsPullback (pullback.fst p g) l ν m`.

Use `IsPullback.of_bot ?_ (by simp [l]) hm` and prove the remaining obligations. Establish `: l ≫ pullback.fst (g ≫ s₁) s₂ = pullback.snd p g` using `by simp [l]`. Rewrite using `[this]`. Conclude with `IsPullback.of_hasPullback p g`. Establish `: IsFinite l` using `MorphismProperty.of_isPullback hl inferInstance`.

Establish `: IsAffineHom (pullback.snd (g ≫ s₁) s₂)` using `MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ (inferInstance : IsAffineHom (g ≫ s₁))`. Establish `e : q = l ≫ pullback.snd (g ≫ s₁) s₂`. Establish `: pullback.snd (g ≫ s₁) s₂ = m ≫ pullback.snd s₁ s₂` using `by simp [m]`. Rewrite using `[this, ← hl.w_assoc]`. Rewrite using `[e]`.

Use `infer_instance`. Use `GlobalTheory.AmpleFibre.locallyQuasiFinite_of_trivial_on_fibres _ _ (pullback.snd p g) (A₂.pull q) inferInstance (pull_isLB h₂ q) (exists_affine_locus_pull h₂ ha q) fun k _ _ y C _ c _ => ?_` and prove the remaining obligations. Set `a` to `c ≫ pullback.fst (pullback.snd p g) y`. Establish `e : a ≫ pullback.fst p g ≫ p = (c ≫ pullback.snd (pullback.snd p g) y) ≫ y ≫ g`. Simplify using `only [a, Category.assoc, pullback.condition, pullback.condition_assoc]`.

Take `⟨t, ht⟩` from `DVR.exists_gen_of_local (V := k) A₁ h₁ (K := PUnit) (fun _ => y ≫ g) (fun _ => 1)`. Establish `g₁ : ∃ t : (A₁.pull ((c ≫ pullback.snd (pullback.snd p g) y) ≫ y ≫ g)).Gen, t.IsGen` using `⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩`. Establish `i₁ : LBIso (A₁.pull ((c ≫ pullback.snd (pullback.snd p g) y) ≫ y ≫ g)) (A₂.pull (a ≫ q))` using `GenSpread.lbIso_pull_comp (a ≫ pullback.fst p g) (e.symm.trans (Category.assoc _ _ _).symm) (by simp [q]) H`. Conclude with `GlobalTheory.SiegelDescent.exists_gen_of_lbIso (pull_isLB h₂ _) (pull_isLB (pull_isLB h₂ _) _) (GenSpread.lbIso_pull_pull h₂ a rfl) (GlobalTheory.SiegelDescent.exists_gen_of_lbIso (pull_isLB h₁ _) (pull_isLB h₂ _) i₁ g₁)`. Conclude with `IsFinite.of_isProper_of_locallyQuasiFinite _`.
-/
theorem isFinite_fst {Z Z₁ Z₂ S : Scheme.{0}} [IsAffine S] (s₁ : Z₁ ⟶ S) (s₂ : Z₂ ⟶ S) [IsProper s₂]
    (ν : Z ⟶ pullback s₁ s₂) [IsFinite ν] {A₁ : LB Z₁} {A₂ : LB Z₂} (h₁ : A₁.IsLB) (h₂ : A₂.IsLB)
    (ha : ∀ y : Z₂, ∃ (d : ℕ) (s : Out.H0 A₂ d), 1 ≤ d ∧ y ∈ Out.nonzeroLocus s ∧
      IsAffineOpen (Out.nonzeroLocus s))
    (H : LBIso (A₁.pull (ν ≫ pullback.fst s₁ s₂)) (A₂.pull (ν ≫ pullback.snd s₁ s₂))) :
    IsFinite (ν ≫ pullback.fst s₁ s₂) := by
  have : LocallyQuasiFinite (ν ≫ pullback.fst s₁ s₂) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := @LocallyQuasiFinite) Z₁.affineCover).2 fun i => ?_
    let g := Z₁.affineCover.f i
    let p := ν ≫ pullback.fst s₁ s₂
    let q := pullback.fst p g ≫ ν ≫ pullback.snd s₁ s₂
    change LocallyQuasiFinite (pullback.snd p g)
    have hq : IsAffineHom q := by
      let m : pullback (g ≫ s₁) s₂ ⟶ pullback s₁ s₂ := pullback.map _ _ _ _ g (𝟙 _) (𝟙 _) (by simp) (by simp)
      have hm : IsPullback m (pullback.fst _ _) (pullback.fst s₁ s₂) g := by
        refine IsPullback.of_right (h₁₂ := pullback.snd s₁ s₂) (v₁₃ := s₂) (h₂₂ := s₁) ?_ (by simp [m])
          (IsPullback.of_hasPullback s₁ s₂).flip
        have : m ≫ pullback.snd s₁ s₂ = pullback.snd _ _ := by simp [m]
        rw [this]
        exact (IsPullback.of_hasPullback (g ≫ s₁) s₂).flip
      let l : pullback p g ⟶ pullback (g ≫ s₁) s₂ :=
        hm.lift (pullback.fst p g ≫ ν) (pullback.snd p g) (by simpa [p] using pullback.condition (f := p) (g := g))
      have hl : IsPullback (pullback.fst p g) l ν m := by
        refine IsPullback.of_bot ?_ (by simp [l]) hm
        have : l ≫ pullback.fst (g ≫ s₁) s₂ = pullback.snd p g := by simp [l]
        rw [this]
        exact IsPullback.of_hasPullback p g
      have : IsFinite l := MorphismProperty.of_isPullback hl inferInstance
      have : IsAffineHom (pullback.snd (g ≫ s₁) s₂) :=
        MorphismProperty.pullback_snd (P := @IsAffineHom) _ _ (inferInstance : IsAffineHom (g ≫ s₁))
      have e : q = l ≫ pullback.snd (g ≫ s₁) s₂ := by
        have : pullback.snd (g ≫ s₁) s₂ = m ≫ pullback.snd s₁ s₂ := by simp [m]
        rw [this, ← hl.w_assoc]
      rw [e]
      infer_instance
    refine GlobalTheory.AmpleFibre.locallyQuasiFinite_of_trivial_on_fibres _ _ (pullback.snd p g) (A₂.pull q) inferInstance (pull_isLB h₂ q)
      (exists_affine_locus_pull h₂ ha q) fun k _ _ y C _ c _ => ?_
    let a := c ≫ pullback.fst (pullback.snd p g) y
    have e : a ≫ pullback.fst p g ≫ p = (c ≫ pullback.snd (pullback.snd p g) y) ≫ y ≫ g := by
      simp only [a, Category.assoc, pullback.condition, pullback.condition_assoc]
    obtain ⟨t, ht⟩ := DVR.exists_gen_of_local (V := k) A₁ h₁ (K := PUnit) (fun _ => y ≫ g) (fun _ => 1)
    have g₁ : ∃ t : (A₁.pull ((c ≫ pullback.snd (pullback.snd p g) y) ≫ y ≫ g)).Gen, t.IsGen :=
      ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
    have i₁ : LBIso (A₁.pull ((c ≫ pullback.snd (pullback.snd p g) y) ≫ y ≫ g)) (A₂.pull (a ≫ q)) :=
      GenSpread.lbIso_pull_comp (a ≫ pullback.fst p g) (e.symm.trans (Category.assoc _ _ _).symm) (by simp [q]) H
    exact GlobalTheory.SiegelDescent.exists_gen_of_lbIso (pull_isLB h₂ _) (pull_isLB (pull_isLB h₂ _) _) (GenSpread.lbIso_pull_pull h₂ a rfl)
      (GlobalTheory.SiegelDescent.exists_gen_of_lbIso (pull_isLB h₁ _) (pull_isLB h₂ _) i₁ g₁)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/- English proof (translation)
Use `isFinite_fromNormalization_of_genericPoints (o := CommRingCat.of R) f g (fun x hx => ?_) fun x _ => ?_` and prove the remaining obligations. Establish `hsp : genericPoint (Sp R) ⤳ (f ≫ g) x` using `(genericPoint_spec (Sp R)).specializes trivial`. Take `⟨x', hx', e⟩` from `Flat.generalizingMap (f ≫ g) hsp`. Take `rfl` from `eq_of_specializes_of_mem_genericPoints hx hx'`. Establish `: CharZero ((Sp R).residueField ((f ≫ g) x'))`.

Rewrite using `[e]`. Establish `: Nonempty (⊤ : (Sp R).Opens)` using `⟨⟨genericPoint (Sp R), trivial⟩⟩`. Establish `: CharZero (Sp R).functionField` using `charZero_of_injective_ringHom (R := R) (f := ((Scheme.ΓSpecIso (.of R)).inv ≫ (Sp R).germToFunctionField ⊤).hom) (((Sp R).germToFunctionField_injective ⊤).comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1)`. Conclude with `charZero_of_injective_ringHom (R := (Sp R).functionField) ((Sp R).residue (genericPoint (Sp R))).hom.injective`. Conclude with `charZero_of_injective_ringHom ((f ≫ g).residueFieldMap x').hom.injective`.

Conclude with `(RingHom.FiniteType.of_surjective _ (f.stalkMap_surjective x)).essFiniteType.residueFieldMap`.
-/
theorem isFinite_fromNormalization_graph {R : Type} [CommRing R] [IsDedekindDomain R] [CharZero R]
    {W Y : Scheme.{0}} (f : W ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [SurjectiveOnStalks f]
    (g : Y ⟶ Sp R) [LocallyOfFiniteType g] [Flat (f ≫ g)] [IsReduced W] [IsLocallyNoetherian W] :
    IsFinite f.fromNormalization := by
  refine isFinite_fromNormalization_of_genericPoints (o := CommRingCat.of R) f g (fun x hx => ?_) fun x _ => ?_
  · have hsp : genericPoint (Sp R) ⤳ (f ≫ g) x := (genericPoint_spec (Sp R)).specializes trivial
    obtain ⟨x', hx', e⟩ := Flat.generalizingMap (f ≫ g) hsp
    obtain rfl := eq_of_specializes_of_mem_genericPoints hx hx'
    have : CharZero ((Sp R).residueField ((f ≫ g) x')) := by
      rw [e]
      have : Nonempty (⊤ : (Sp R).Opens) := ⟨⟨genericPoint (Sp R), trivial⟩⟩
      have : CharZero (Sp R).functionField :=
        charZero_of_injective_ringHom (R := R)
          (f := ((Scheme.ΓSpecIso (.of R)).inv ≫ (Sp R).germToFunctionField ⊤).hom)
          (((Sp R).germToFunctionField_injective ⊤).comp
            (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).1)
      exact charZero_of_injective_ringHom (R := (Sp R).functionField)
        ((Sp R).residue (genericPoint (Sp R))).hom.injective
    exact charZero_of_injective_ringHom ((f ≫ g).residueFieldMap x').hom.injective
  · exact (RingHom.FiniteType.of_surjective _ (f.stalkMap_surjective x)).essFiniteType.residueFieldMap

/- English proof (translation)
Introduce `z hz K _ _ t ht`. Take `⟨w, rfl⟩` from `genericPoints_subset_range_of_isDominant u hz`. Take `⟨y, rfl⟩` from `HomExt.exists_lift_of_range_subset u t (by`. Introduce and unpack `_ ⟨p, rfl⟩`. Take `⟨p', hp'⟩` from `ht`.

Conclude with `⟨w, hp'.symm.trans (congrArg t (Subsingleton.elim _ _))⟩)`. Establish `P` using `(IsPullback.of_hasPullback G'.hom y).paste_horiz h`. Conclude with `(MorphismProperty.cancel_left_of_respectsIso @IsProper P.isoPullback.hom _).1 (by rw [P.isoPullback_hom_snd]; infer_instance)`.
-/
theorem genericPoints_subset_abLocus {W Z : Scheme.{0}} (u : W ⟶ Z) [IsPreimmersion u] [Flat u] [IsDominant u]
    [QuasiCompact u] {G : Over Z} {G' : Over W} {φ : G'.left ⟶ G.left} (h : IsPullback φ G'.hom G.hom u)
    [IsProper G'.hom] : genericPoints Z ⊆ abLocus G := by
  intro z hz K _ _ t ht
  obtain ⟨w, rfl⟩ := genericPoints_subset_range_of_isDominant u hz
  obtain ⟨y, rfl⟩ := HomExt.exists_lift_of_range_subset u t (by
    rintro _ ⟨p, rfl⟩
    obtain ⟨p', hp'⟩ := ht
    exact ⟨w, hp'.symm.trans (congrArg t (Subsingleton.elim _ _))⟩)
  have P := (IsPullback.of_hasPullback G'.hom y).paste_horiz h
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper P.isoPullback.hom _).1
    (by rw [P.isoPullback_hom_snd]; infer_instance)

/- English proof (translation)
Introduce `hE E _ _ _ H R _ Z₁ Z₂ W s₁ s₂ t₁ t₂ tW j j' m₁ m₂ N A₁ A₂ _ _ _ hn hp₁ hp₂ _ _ _ _ _ _ _ _ _ _ w hr hs`. Use `GlobalTheory.ThetaDescent.isProper_of_isProjOver hp₁` as an intermediate fact. Use `GlobalTheory.ThetaDescent.isProper_of_isProjOver hp₂` as an intermediate fact. Establish `: IsLocallyNoetherian Z₁` using `LocallyOfFiniteType.isLocallyNoetherian s₁`. Use `GlobalTheory.IsNormalScheme.of_pred hn` as an intermediate fact.

Use `isIso_stalkMap_of_flat_of_surjectiveOnStalks j` as an intermediate fact. Establish `: GlobalTheory.IsNormalScheme W` using `GlobalTheory.IsNormalScheme.of_isIso_stalkMap j`. Establish `: IsLocallyNoetherian W` using `isLocallyNoetherian_of_isPreimmersion j`. Set `f : W ⟶ pullback s₁ s₂` to `pullback.lift j j' w`. Establish `hf₁ : f ≫ pullback.fst s₁ s₂ = j` using `pullback.lift_fst _ _ _`.

Establish `hf₂ : f ≫ pullback.snd s₁ s₂ = j'` using `pullback.lift_snd _ _ _`. Establish `: IsPreimmersion (f ≫ pullback.fst s₁ s₂)` using `hf₁ ▸ inferInstance`. Establish `: QuasiCompact (f ≫ pullback.fst s₁ s₂)` using `hf₁ ▸ inferInstance`. Establish `: IsPreimmersion f` using `isPreimmersion_of_comp f (pullback.fst s₁ s₂)`. Establish `: QuasiCompact f` using `.of_comp f (pullback.fst s₁ s₂)`.

Establish `: Flat (f ≫ pullback.fst s₁ s₂ ≫ s₁)`. Rewrite using `[reassoc_of% hf₁]`. Use `infer_instance`. Establish `: IsFinite f.fromNormalization` using `isFinite_fromNormalization_graph f (pullback.fst s₁ s₂ ≫ s₁)`. Set `u` to `f.toNormalization`.

Set `p₁` to `f.fromNormalization ≫ pullback.fst s₁ s₂`. Set `p₂` to `f.fromNormalization ≫ pullback.snd s₁ s₂`. Establish `hu₁ : u ≫ p₁ = j` using `by simp [u, p₁, hf₁]`. Establish `hu₂ : u ≫ p₂ = j'` using `by simp [u, p₂, hf₂]`. Establish `: IsPreimmersion (u ≫ p₁)` using `hu₁ ▸ inferInstance`.

Establish `: IsPreimmersion u` using `isPreimmersion_of_comp u p₁`. Establish `: Flat u` using `flat_of_isPreimmersion u`. Establish `hZ` using `GlobalTheory.IsNormalScheme.pred f.normalization`. Establish `: IsLocallyNoetherian f.normalization` using `LocallyOfFiniteType.isLocallyNoetherian p₁`. Set `z₀ : Sp R ⟶ Sp ℤ` to `spMap (algebraMap ℤ R)`.

Establish `: LocallyOfFiniteType z₀` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 ‹_›)`. Establish `: Flat z₀` using `Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)`. Establish `: Flat (f.toNormalization ≫ p₁ ≫ s₁)`. Rewrite using `[reassoc_of% hu₁]`. Use `infer_instance`.

Establish `: Flat (p₁ ≫ s₁)` using `flat_normalization f (p₁ ≫ s₁)`. Take `⟨_, _, _, _, _, n₁, -⟩` from `sabPull Out.CubePf.cubePull p₁ t₁`. Take `⟨_, _, _, _, _, n₂, -⟩` from `sabPull Out.CubePf.cubePull p₂ t₂`. Take `⟨a₁, -⟩` from `ObjMaps.exists_sab_cancel n₁ (hu₁ ▸ m₁ : SABMap tW t₁ (u ≫ p₁))`. Take `⟨a₂, -⟩` from `ObjMaps.exists_sab_cancel n₂ (hu₂ ▸ m₂ : SABMap tW t₂ (u ≫ p₂))`.

Take `⟨b, -⟩` from `GlobalTheory.exists_sabMap_id_of_common_generic hE E H _ W u ⟨hZ, (p₁ ≫ s₁) ≫ z₀, inferInstance, inferInstance⟩ inferInstance inferInstance inferInstance inferInstance tW _ _ a₁ a₂ inferInstance`. Take `⟨n₂', -⟩` from `ObjMaps.exists_sab_comp n₂ b`. Rewrite `n₂'` using `[Category.id_comp]`. Establish `hA` using `GlobalTheory.T.lineBundleIso_of_ampleDeterminantFrames E H _ Z₁ Z₂ ((p₁ ≫ s₁) ≫ z₀) _ t₁ t₂ p₁ p₂ n₁ n₂' N A₁ A₂ hZ inferInstance (genericPoints_subset_abLocus u a₁.cart.1) hr hs`. Establish `: IsFinite p₁` using `isFinite_fst s₁ s₂ f.fromNormalization A₁.isLB A₂.isLB A₂.ample hA`.

Take `⟨h, ⟨h₁, -⟩, -⟩` from `existsUnique_lift_of_densePart Z₁ W Z₁ f.normalization j hn inferInstance inferInstance inferInstance inferInstance p₁ (𝟙 _) u inferInstance (by rw [hu₁, Category.comp_id])`. Conclude with `⟨h ≫ p₂, by rw [reassoc_of% h₁, hu₂]⟩`.
-/
theorem exists_hom_of_ampFrames : GlobalTheory.LN.HomExtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (Z₁ Z₂ W : Scheme.{0}) (s₁ : Z₁ ⟶ Sp R) (s₂ : Z₂ ⟶ Sp R) (t₁ : SAB H Z₁) (t₂ : SAB H Z₂) (tW : SAB H W) (j : W ⟶ Z₁) (j' : W ⟶ Z₂) (_ : SABMap tW t₁ j) (_ : SABMap tW t₂ j') (N : ℕ) (A₁ : GlobalTheory.LN.AmpFrames t₁.G t₁.PP.L N) (A₂ : GlobalTheory.LN.AmpFrames t₂.G t₂.PP.L N), IsDedekindDomain R → CharZero R → Algebra.FiniteType ℤ R → Geo.Tor.IsNormalScheme Z₁ → IsProjOver s₁ → IsProjOver s₂ → Flat s₁ → IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsProper tW.G.hom → j ≫ s₁ = j' ≫ s₂ → A₁.r = A₂.r → A₁.s = A₂.s → ∃ ρ : Z₁ ⟶ Z₂, j ≫ ρ = j' := by
  intro hE E _ _ _ H R _ Z₁ Z₂ W s₁ s₂ t₁ t₂ tW j j' m₁ m₂ N A₁ A₂ _ _ _ hn hp₁ hp₂ _ _ _ _ _ _ _ _ _ _ w hr hs
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver hp₁
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver hp₂
  have : IsLocallyNoetherian Z₁ := LocallyOfFiniteType.isLocallyNoetherian s₁
  have := GlobalTheory.IsNormalScheme.of_pred hn
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j
  have : GlobalTheory.IsNormalScheme W := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j
  have : IsLocallyNoetherian W := isLocallyNoetherian_of_isPreimmersion j
  let f : W ⟶ pullback s₁ s₂ := pullback.lift j j' w
  have hf₁ : f ≫ pullback.fst s₁ s₂ = j := pullback.lift_fst _ _ _
  have hf₂ : f ≫ pullback.snd s₁ s₂ = j' := pullback.lift_snd _ _ _
  have : IsPreimmersion (f ≫ pullback.fst s₁ s₂) := hf₁ ▸ inferInstance
  have : QuasiCompact (f ≫ pullback.fst s₁ s₂) := hf₁ ▸ inferInstance
  have : IsPreimmersion f := isPreimmersion_of_comp f (pullback.fst s₁ s₂)
  have : QuasiCompact f := .of_comp f (pullback.fst s₁ s₂)
  have : Flat (f ≫ pullback.fst s₁ s₂ ≫ s₁) := by
    rw [reassoc_of% hf₁]; infer_instance
  have : IsFinite f.fromNormalization := isFinite_fromNormalization_graph f (pullback.fst s₁ s₂ ≫ s₁)
  let u := f.toNormalization
  let p₁ := f.fromNormalization ≫ pullback.fst s₁ s₂
  let p₂ := f.fromNormalization ≫ pullback.snd s₁ s₂
  have hu₁ : u ≫ p₁ = j := by simp [u, p₁, hf₁]
  have hu₂ : u ≫ p₂ = j' := by simp [u, p₂, hf₂]
  have : IsPreimmersion (u ≫ p₁) := hu₁ ▸ inferInstance
  have : IsPreimmersion u := isPreimmersion_of_comp u p₁
  have : Flat u := flat_of_isPreimmersion u
  have hZ := GlobalTheory.IsNormalScheme.pred f.normalization
  have : IsLocallyNoetherian f.normalization := LocallyOfFiniteType.isLocallyNoetherian p₁
  let z₀ : Sp R ⟶ Sp ℤ := spMap (algebraMap ℤ R)
  have : LocallyOfFiniteType z₀ :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 ‹_›)
  have : Flat z₀ := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Flat (f.toNormalization ≫ p₁ ≫ s₁) := by
    rw [reassoc_of% hu₁]; infer_instance
  have : Flat (p₁ ≫ s₁) := flat_normalization f (p₁ ≫ s₁)
  obtain ⟨_, _, _, _, _, n₁, -⟩ := sabPull Out.CubePf.cubePull p₁ t₁
  obtain ⟨_, _, _, _, _, n₂, -⟩ := sabPull Out.CubePf.cubePull p₂ t₂
  obtain ⟨a₁, -⟩ := ObjMaps.exists_sab_cancel n₁ (hu₁ ▸ m₁ : SABMap tW t₁ (u ≫ p₁))
  obtain ⟨a₂, -⟩ := ObjMaps.exists_sab_cancel n₂ (hu₂ ▸ m₂ : SABMap tW t₂ (u ≫ p₂))
  obtain ⟨b, -⟩ := GlobalTheory.exists_sabMap_id_of_common_generic hE E H _ W u
    ⟨hZ, (p₁ ≫ s₁) ≫ z₀, inferInstance, inferInstance⟩ inferInstance inferInstance inferInstance inferInstance
    tW _ _ a₁ a₂ inferInstance
  obtain ⟨n₂', -⟩ := ObjMaps.exists_sab_comp n₂ b
  rw [Category.id_comp] at n₂'
  have hA := GlobalTheory.T.lineBundleIso_of_ampleDeterminantFrames E H _ Z₁ Z₂ ((p₁ ≫ s₁) ≫ z₀) _ t₁ t₂ p₁ p₂ n₁ n₂' N A₁ A₂ hZ inferInstance
    (genericPoints_subset_abLocus u a₁.cart.1) hr hs
  have : IsFinite p₁ := isFinite_fst s₁ s₂ f.fromNormalization A₁.isLB A₂.isLB A₂.ample hA
  obtain ⟨h, ⟨h₁, -⟩, -⟩ := existsUnique_lift_of_densePart Z₁ W Z₁ f.normalization j hn inferInstance inferInstance
    inferInstance inferInstance p₁ (𝟙 _) u inferInstance (by rw [hu₁, Category.comp_id])
  exact ⟨h ≫ p₂, by rw [reassoc_of% h₁, hu₂]⟩

end GlobalTheory.AmpUniq
