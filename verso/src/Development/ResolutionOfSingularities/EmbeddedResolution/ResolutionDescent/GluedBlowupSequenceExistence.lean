import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceDescentDatum
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpensPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `hA : IsStrictPullbackBlowupSeq (pullback.fst g g) (t.baseChange (pullback.fst g g)) t` using `isStrictPullbackSequenceOfBlowups_baseChange t (pullback.fst g g)`. Establish `hC : IsStrictPullbackBlowupSeq (pullback.snd g g) (t.baseChange (pullback.snd g g)) t` using `isStrictPullbackSequenceOfBlowups_baseChange t (pullback.snd g g)`. Establish `hAr : IsStrictPullbackBlowupSeq r ((t.baseChange (pullback.fst g g)).baseChange r) (t.baseChange (pullback.fst g g))` using `isStrictPullbackSequenceOfBlowups_baseChange (t.baseChange (pullback.fst g g)) r`. Establish `hCr : IsStrictPullbackBlowupSeq r ((t.baseChange (pullback.snd g g)).baseChange r) (t.baseChange (pullback.snd g g))` using `isStrictPullbackSequenceOfBlowups_baseChange (t.baseChange (pullback.snd g g)) r`. Establish `e1 : u.Isomorphic ((t.baseChange (pullback.fst g g)).baseChange r)` using `h1.isomorphic (hAr.comp hA)`.

Establish `e2 : u.Isomorphic ((t.baseChange (pullback.snd g g)).baseChange r)` using `h2.isomorphic (hCr.comp hC)`. Conclude with `exists_isStrictPullback_of_isomorphic_baseChange g t (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hAr hCr (e1.symm.trans e2))`.
-/
private theorem exists_isStrictPullback_of_pullback_cover {Y W V : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (r : V ⟶ pullback g g) [AlgebraicGeometry.Flat r]
    [AlgebraicGeometry.Surjective r] (t : SequenceOfBlowups W) (u : SequenceOfBlowups V)
    (h1 : IsStrictPullbackBlowupSeq (r ≫ pullback.fst g g) u t)
    (h2 : IsStrictPullbackBlowupSeq (r ≫ pullback.snd g g) u t) :
    ∃ B : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t B := by
  have hA : IsStrictPullbackBlowupSeq (pullback.fst g g) (t.baseChange (pullback.fst g g)) t :=
    isStrictPullbackSequenceOfBlowups_baseChange t (pullback.fst g g)
  have hC : IsStrictPullbackBlowupSeq (pullback.snd g g) (t.baseChange (pullback.snd g g)) t :=
    isStrictPullbackSequenceOfBlowups_baseChange t (pullback.snd g g)
  have hAr : IsStrictPullbackBlowupSeq r ((t.baseChange (pullback.fst g g)).baseChange r)
      (t.baseChange (pullback.fst g g)) :=
    isStrictPullbackSequenceOfBlowups_baseChange (t.baseChange (pullback.fst g g)) r
  have hCr : IsStrictPullbackBlowupSeq r ((t.baseChange (pullback.snd g g)).baseChange r)
      (t.baseChange (pullback.snd g g)) :=
    isStrictPullbackSequenceOfBlowups_baseChange (t.baseChange (pullback.snd g g)) r
  have e1 : u.Isomorphic ((t.baseChange (pullback.fst g g)).baseChange r) :=
    h1.isomorphic (hAr.comp hA)
  have e2 : u.Isomorphic ((t.baseChange (pullback.snd g g)).baseChange r) :=
    h2.isomorphic (hCr.comp hC)
  exact exists_isStrictPullback_of_isomorphic_baseChange g t
    (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hAr hCr (e1.symm.trans e2))

/- English proof (translation)
Establish `hbc : IsStrictPullbackBlowupSeq φ (B.baseChange φ) B` using `isStrictPullbackSequenceOfBlowups_baseChange B φ`. Establish `hbcα : IsStrictPullbackBlowupSeq α ((B.baseChange φ).baseChange α) (B.baseChange φ)` using `isStrictPullbackSequenceOfBlowups_baseChange (B.baseChange φ) α`. Establish `e : u.Isomorphic ((B.baseChange φ).baseChange α)` using `h2.isomorphic (hbcα.comp hbc)`. Conclude with `hbc.of_isomorphic_pullback (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic h1 hbcα e).symm`.
-/
private theorem isStrictPullback_of_comp_flat_surjective {X X' V : Scheme.{u}} (φ : X' ⟶ X)
    [AlgebraicGeometry.Flat φ] (α : V ⟶ X') [AlgebraicGeometry.Flat α]
    [AlgebraicGeometry.Surjective α] (s : SequenceOfBlowups X') (B : SequenceOfBlowups X) (u : SequenceOfBlowups V)
    (h1 : IsStrictPullbackBlowupSeq α u s) (h2 : IsStrictPullbackBlowupSeq (α ≫ φ) u B) :
    IsStrictPullbackBlowupSeq φ s B := by
  have hbc : IsStrictPullbackBlowupSeq φ (B.baseChange φ) B := isStrictPullbackSequenceOfBlowups_baseChange B φ
  have hbcα : IsStrictPullbackBlowupSeq α ((B.baseChange φ).baseChange α) (B.baseChange φ) :=
    isStrictPullbackSequenceOfBlowups_baseChange (B.baseChange φ) α
  have e : u.Isomorphic ((B.baseChange φ).baseChange α) := h2.isomorphic (hbcα.comp hbc)
  exact hbc.of_isomorphic_pullback (IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic h1 hbcα e).symm

/- English proof (translation)
Introduce `hcover k hk hk0 Y p hpft hpqc hpred`. Establish `: AlgebraicGeometry.IsLocallyNoetherian Y` using `LocallyOfFiniteType.isLocallyNoetherian p`. Establish `: CompactSpace ↥(Spec (CommRingCat.of k))` using `inferInstance`. Establish `: CompactSpace ↥Y` using `QuasiCompact.compactSpace_of_compactSpace p`. Take `⟨ι, hι, U, hUaff, hUtop⟩` from `exists_finite_affine_cover Y`.

Establish `: AlgebraicGeometry.IsAffine (sigmaOpens Y U)` using `isAffine_sigmaOpens Y U hUaff`. Establish `: CompactSpace ↥(sigmaOpens Y U)` using `inferInstance`. Establish `: AlgebraicGeometry.Surjective (sigmaOpensDesc Y U)` using `surjective_sigmaOpensDesc Y U hUtop`. Take `⟨V, sV, r, hVaff, hVred, hsft, hsqc, hret, hrsurj, hrq⟩` from `exists_affine_etale_cover_pullback_sigmaOpensDesc Y p U hUaff (sigmaOpens Y U) (sigmaOpensDesc Y U ≫ p) (sigmaOpensDesc Y U) rfl`. Establish `: AlgebraicGeometry.Etale (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U))` using `etale_comp_fst_pullback_sigmaOpensDesc Y U (sigmaOpens Y U) (sigmaOpensDesc Y U) V r`.

Establish `: AlgebraicGeometry.Etale (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U))` using `etale_comp_snd_pullback_sigmaOpensDesc Y U (sigmaOpens Y U) (sigmaOpensDesc Y U) V r`. Establish `: AlgebraicGeometry.Surjective (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U))` using `surjective_comp_fst_pullback_sigmaOpensDesc Y U hUtop (sigmaOpens Y U) (sigmaOpensDesc Y U) V r`. Establish `: AlgebraicGeometry.Surjective (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U))` using `surjective_comp_snd_pullback_sigmaOpensDesc Y U (sigmaOpens Y U) (sigmaOpensDesc Y U) V r`. Establish `hq1 : (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) ≫ (sigmaOpensDesc Y U ≫ p) = sV`. Rewrite using `[Category.assoc]`.

Conclude with `hrq`. Establish `hq2 : (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) ≫ (sigmaOpensDesc Y U ≫ p) = sV`. Establish `h` using `comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U (sigmaOpens Y U) (sigmaOpensDesc Y U) V r`. Establish `h3` using `congrArg (fun m => m ≫ p) h`. Simplify using `only [Category.assoc] at h3`.

Rewrite using `[Category.assoc, ← h3]`. Conclude with `hrq`. Establish `ht1` using `hcover k (sigmaOpens Y U) V (sigmaOpensDesc Y U ≫ p) sV (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) hq1 (fun y => AlgebraicGeometry.Surjective.surj y)`. Establish `ht2` using `hcover k (sigmaOpens Y U) V (sigmaOpensDesc Y U ≫ p) sV (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) hq2 (fun y => AlgebraicGeometry.Surjective.surj y)`. Take `⟨B, hB⟩` from `exists_isStrictPullback_of_pullback_cover (sigmaOpensDesc Y U) r (R k (sigmaOpens Y U) (sigmaOpensDesc Y U ≫ p)) (R k V sV) ht1 ht2`.

Use `⟨B, hB.center_ne_top_of_forall_center_ne_top (fun i hi => hR k (sigmaOpens Y U) (sigmaOpensDesc Y U ≫ p) i hi), ?_⟩` and prove the remaining obligations. Introduce `W' q' hq'ft hq'qc hW'red hW'aff φ hφet hφq hφsurj`. Establish `: AlgebraicGeometry.Surjective φ` using `⟨hφsurj⟩`. Take `⟨V', sV', r', hV'aff, hV'red, hs'ft, hs'qc, hr'et, hr'surj, hr'q⟩` from `exists_affine_etale_cover_pullback_sigmaOpensDesc Y p U hUaff W' q' φ hφq`. Establish `: AlgebraicGeometry.Etale (r' ≫ pullback.fst φ (sigmaOpensDesc Y U))` using `etale_comp_fst_pullback_sigmaOpensDesc Y U W' φ V' r'`.

Establish `: AlgebraicGeometry.Etale (r' ≫ pullback.snd φ (sigmaOpensDesc Y U))` using `etale_comp_snd_pullback_sigmaOpensDesc Y U W' φ V' r'`. Establish `: AlgebraicGeometry.Surjective (r' ≫ pullback.fst φ (sigmaOpensDesc Y U))` using `surjective_comp_fst_pullback_sigmaOpensDesc Y U hUtop W' φ V' r'`. Establish `: AlgebraicGeometry.Surjective (r' ≫ pullback.snd φ (sigmaOpensDesc Y U))` using `surjective_comp_snd_pullback_sigmaOpensDesc Y U W' φ V' r'`. Establish `hα : (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ q' = sV'`. Rewrite using `[Category.assoc]`.

Conclude with `hr'q`. Establish `hβ : (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) ≫ (sigmaOpensDesc Y U ≫ p) = sV'`. Establish `h` using `comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U W' φ V' r'`. Establish `h3` using `congrArg (fun m => m ≫ p) h`. Simplify using `only [Category.assoc] at h3`.

Rewrite using `[Category.assoc, ← h3, hφq]`. Conclude with `hr'q`. Establish `hu1` using `hcover k W' V' q' sV' (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) hα (fun y => AlgebraicGeometry.Surjective.surj y)`. Establish `hu2` using `hcover k (sigmaOpens Y U) V' (sigmaOpensDesc Y U ≫ p) sV' (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) hβ (fun y => AlgebraicGeometry.Surjective.surj y)`. Establish `hαφ : (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ φ = (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) ≫ sigmaOpensDesc Y U`.

Simplify using `only [Category.assoc]`. Conclude with `comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U W' φ V' r'`. Establish `hfin : IsStrictPullbackBlowupSeq ((r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ φ) (R k V' sV') B`. Rewrite using `[hαφ]`. Conclude with `hu2.comp hB`.

Conclude with `isStrictPullback_of_comp_flat_surjective φ (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) (R k W' q') B (R k V' sV') hu1 hfin`.
-/
theorem existsGluedBlowupSequence_of_center_ne_top (R : AffineResolutionRule.{u})
    (hR : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
      (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
      [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
      [AlgebraicGeometry.IsAffine Y] (i : ℕ),
      i < (R k Y p).length → (R k Y p).center i ≠ ⊤) :
    ExistsGluedBlowupSequence R := by
  intro hcover k hk hk0 Y p hpft hpqc hpred
  have : AlgebraicGeometry.IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace ↥(Spec (CommRingCat.of k)) := inferInstance
  have : CompactSpace ↥Y := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨ι, hι, U, hUaff, hUtop⟩ := exists_finite_affine_cover Y
  have : AlgebraicGeometry.IsAffine (sigmaOpens Y U) := isAffine_sigmaOpens Y U hUaff
  have : CompactSpace ↥(sigmaOpens Y U) := inferInstance
  have : AlgebraicGeometry.Surjective (sigmaOpensDesc Y U) :=
    surjective_sigmaOpensDesc Y U hUtop
  obtain ⟨V, sV, r, hVaff, hVred, hsft, hsqc, hret, hrsurj, hrq⟩ :=
    exists_affine_etale_cover_pullback_sigmaOpensDesc Y p U hUaff (sigmaOpens Y U)
      (sigmaOpensDesc Y U ≫ p) (sigmaOpensDesc Y U) rfl
  have : AlgebraicGeometry.Etale
      (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    etale_comp_fst_pullback_sigmaOpensDesc Y U (sigmaOpens Y U) (sigmaOpensDesc Y U) V r
  have : AlgebraicGeometry.Etale
      (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    etale_comp_snd_pullback_sigmaOpensDesc Y U (sigmaOpens Y U) (sigmaOpensDesc Y U) V r
  have : AlgebraicGeometry.Surjective
      (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    surjective_comp_fst_pullback_sigmaOpensDesc Y U hUtop (sigmaOpens Y U)
      (sigmaOpensDesc Y U) V r
  have : AlgebraicGeometry.Surjective
      (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) :=
    surjective_comp_snd_pullback_sigmaOpensDesc Y U (sigmaOpens Y U)
      (sigmaOpensDesc Y U) V r
  have hq1 : (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) ≫
      (sigmaOpensDesc Y U ≫ p) = sV := by
    rw [Category.assoc]
    exact hrq
  have hq2 : (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) ≫
      (sigmaOpensDesc Y U ≫ p) = sV := by
    have h := comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U (sigmaOpens Y U)
      (sigmaOpensDesc Y U) V r
    have h3 := congrArg (fun m => m ≫ p) h
    simp only [Category.assoc] at h3
    rw [Category.assoc, ← h3]
    exact hrq
  have ht1 := hcover k (sigmaOpens Y U) V (sigmaOpensDesc Y U ≫ p) sV
    (r ≫ pullback.fst (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) hq1
    (fun y => AlgebraicGeometry.Surjective.surj y)
  have ht2 := hcover k (sigmaOpens Y U) V (sigmaOpensDesc Y U ≫ p) sV
    (r ≫ pullback.snd (sigmaOpensDesc Y U) (sigmaOpensDesc Y U)) hq2
    (fun y => AlgebraicGeometry.Surjective.surj y)
  obtain ⟨B, hB⟩ := exists_isStrictPullback_of_pullback_cover (sigmaOpensDesc Y U) r
    (R k (sigmaOpens Y U) (sigmaOpensDesc Y U ≫ p)) (R k V sV) ht1 ht2
  refine ⟨B, hB.center_ne_top_of_forall_center_ne_top
    (fun i hi => hR k (sigmaOpens Y U) (sigmaOpensDesc Y U ≫ p) i hi), ?_⟩
  intro W' q' hq'ft hq'qc hW'red hW'aff φ hφet hφq hφsurj
  have : AlgebraicGeometry.Surjective φ := ⟨hφsurj⟩
  obtain ⟨V', sV', r', hV'aff, hV'red, hs'ft, hs'qc, hr'et, hr'surj, hr'q⟩ :=
    exists_affine_etale_cover_pullback_sigmaOpensDesc Y p U hUaff W' q' φ hφq
  have : AlgebraicGeometry.Etale (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) :=
    etale_comp_fst_pullback_sigmaOpensDesc Y U W' φ V' r'
  have : AlgebraicGeometry.Etale (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) :=
    etale_comp_snd_pullback_sigmaOpensDesc Y U W' φ V' r'
  have : AlgebraicGeometry.Surjective (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) :=
    surjective_comp_fst_pullback_sigmaOpensDesc Y U hUtop W' φ V' r'
  have : AlgebraicGeometry.Surjective (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) :=
    surjective_comp_snd_pullback_sigmaOpensDesc Y U W' φ V' r'
  have hα : (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ q' = sV' := by
    rw [Category.assoc]
    exact hr'q
  have hβ : (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) ≫ (sigmaOpensDesc Y U ≫ p) = sV' := by
    have h := comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U W' φ V' r'
    have h3 := congrArg (fun m => m ≫ p) h
    simp only [Category.assoc] at h3
    rw [Category.assoc, ← h3, hφq]
    exact hr'q
  have hu1 := hcover k W' V' q' sV' (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) hα
    (fun y => AlgebraicGeometry.Surjective.surj y)
  have hu2 := hcover k (sigmaOpens Y U) V' (sigmaOpensDesc Y U ≫ p) sV'
    (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) hβ
    (fun y => AlgebraicGeometry.Surjective.surj y)
  have hαφ : (r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ φ
      = (r' ≫ pullback.snd φ (sigmaOpensDesc Y U)) ≫ sigmaOpensDesc Y U := by
    simp only [Category.assoc]
    exact comp_fst_comp_eq_comp_snd_comp_sigmaOpensDesc Y U W' φ V' r'
  have hfin : IsStrictPullbackBlowupSeq ((r' ≫ pullback.fst φ (sigmaOpensDesc Y U)) ≫ φ)
      (R k V' sV') B := by
    rw [hαφ]
    exact hu2.comp hB
  exact isStrictPullback_of_comp_flat_surjective φ (r' ≫ pullback.fst φ (sigmaOpensDesc Y U))
    (R k W' q') B (R k V' sV') hu1 hfin

end FunctorialResolution.EmbeddedResolution

end
