import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FubiniStudyChowHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ChowFormHeightOfArch
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IntegralOfLintegral
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MahlerSectionStatementHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ProjSpace ChowFormHeightComparison₂.CF

attribute [local instance] MvPolynomial.gradedAlgebra

namespace FubiniStudyChowHeightFormula₂.Fs

variable (R : Type) [CommRing R] (N : ℕ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eval₂Hom_eq (U : (PSpace R N).Opens) (t : Fin (N + 1) → Γ(PSpace R N, U)) (g : MvPolynomial (Fin (N + 1)) R) :
    eval₂Hom (algX (PSpace.str R N) U) t g = aeval t g := rfl

/- English proof (translation)
Use `⟨O1_isLB R N, ?_, fun k => ?_⟩` and prove the remaining obligations. Simplify using `only [nonzeroLocus_coord]`. Conclude with `(O1_isLB R N).cover`. Establish `hk : nonzeroLocus (coord R N k) = chart R N k` using `by rw [nonzeroLocus_coord, twistingSheafOne_chart_eq_preimage_standardChart]`. Use `⟨hk ▸ isAffineOpen_chart R N k, ?_⟩` and prove the remaining obligations.

Rewrite using `[hk]`. Use `⟨ratio R N k, ?_, ?_⟩` and prove the remaining obligations. Establish `e : ⇑(eval₂Hom (algX (PSpace.str R N) (chart R N k)) (ratio R N k)) = ⇑(aeval (ratio R N k))`. Use function extensionality and compare the values at `(eval₂Hom_eq R N _ _)`. Rewrite using `[e]`.

Conclude with `aeval_ratio_surjective R N k`. Introduce `j i erw [coord_f R N j i, coord_f R N k i, resG_ratioOn, resG_ratioOn]`. Rewrite using `[mul_comm]`. Conclude with `(ratioOn_mul_ratioOn (R := R) (N := N) (U := chart R N k ⊓ chart R N i) (i := i) (j := k) (k := j)).symm`.
-/
theorem emb : Emb (PSpace.str R N) (coord R N) := by
  refine ⟨O1_isLB R N, ?_, fun k => ?_⟩
  · simp only [nonzeroLocus_coord]
    exact (O1_isLB R N).cover
  · have hk : nonzeroLocus (coord R N k) = chart R N k := by rw [nonzeroLocus_coord, twistingSheafOne_chart_eq_preimage_standardChart]
    refine ⟨hk ▸ isAffineOpen_chart R N k, ?_⟩
    rw [hk]
    refine ⟨ratio R N k, ?_, ?_⟩
    · have e : ⇑(eval₂Hom (algX (PSpace.str R N) (chart R N k)) (ratio R N k)) = ⇑(aeval (ratio R N k)) :=
        funext (eval₂Hom_eq R N _ _)
      rw [e]
      exact aeval_ratio_surjective R N k
    · intro j i
      erw [coord_f R N j i, coord_f R N k i, resG_ratioOn, resG_ratioOn]
      rw [mul_comm]
      exact (ratioOn_mul_ratioOn (R := R) (N := N) (U := chart R N k ⊓ chart R N i) (i := i) (j := k) (k := j)).symm

/- English proof (translation)
Establish `key : ∀ (i : (O1 R N).ι) (h : (z : PSpace R N) ∈ (O1 R N).U i) (q : MvPolynomial (Fin (N + 1)) R), (coneHom (PSpace.str R N) (coord R N) z i h q = 0 ↔ ∀ d, homogeneousComponent d q ∈ (z : ProjectiveSpectrum (homogeneousSubmodule (Fin (N + 1)) R)).asHomogeneousIdeal)`. Introduce `i h q`. Rewrite using `[C.coneHom_eq, Polynomial.ext_iff]`. Apply `forall_congr'` to reduce the goal to its premises. Introduce `d`.

Rewrite using `[Polynomial.coeff_map, Polynomial.coeff_zero]`. Use `erw [A.coeff_cone]`. Use `erw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]`. Establish `hd` using `homogeneousComponent_isHomogeneous d q`. Establish `e : (eval₂Hom (algX (PSpace.str R N) ((O1 R N).U i)) fun n => (coord R N n).f i) (homogeneousComponent d q) = formOn (chart R N i) i le_rfl d _ hd` using `((formOn_eq_aeval (R := R) (N := N) (U := chart R N i) (i := i) (hi := le_rfl) hd).trans (eval₂Hom_eq R N ((O1 R N).U i) _ _).symm).symm`.

Use `erw [e, basicOpen_formOn]`. Prove the components needed by the constructor for the conclusion. Introduce `hn`. Assume the negation of the conclusion as `hc`. Conclude with `hn ⟨h, (Proj.mem_basicOpen _ _ _).2 hc⟩`.

Introduce and unpack `hm ⟨_, hb⟩`. Conclude with `(Proj.mem_basicOpen _ _ _).1 hb hm`. Establish `hom : ∀ q : MvPolynomial (Fin (N + 1)) R, q ∈ (z : ProjectiveSpectrum (homogeneousSubmodule (Fin (N + 1)) R)).asHomogeneousIdeal.toIdeal ↔ ∀ d, homogeneousComponent d q ∈ (z : ProjectiveSpectrum (homogeneousSubmodule (Fin (N + 1)) R)).asHomogeneousIdeal`. Introduce `q`. Rewrite using `[(z : ProjectiveSpectrum (homogeneousSubmodule (Fin (N + 1)) R)).asHomogeneousIdeal.isHomogeneous.mem_iff]`.

Conclude with `forall_congr' fun d => by`. Rewrite using `[show ((DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) q d : MvPolynomial (Fin (N + 1)) R)) = homogeneousComponent d q from decomposition.decompose'_apply q d]`. Both sides reduce to the same expression. Use extensionality with `q`. Simplify using `only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker]`.

Rewrite using `[hom]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Establish `hz : (z : PSpace R N) ∈ ⨆ i, (O1 R N).U i`. Rewrite using `[(O1_isLB R N).cover]`.

Discharge the goal by the elementary cases of `trivial`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hz`. Conclude with `(key i hi q).1 (H i hi)`. Introduce `H i hi`. Conclude with `(key i hi q).2 H`.
-/
theorem ptIdeal_eq (z : PSpace R N) :
    ptIdeal (PSpace.str R N) (coord R N) z =
      (z : ProjectiveSpectrum (homogeneousSubmodule (Fin (N + 1)) R)).asHomogeneousIdeal.toIdeal := by
  have key : ∀ (i : (O1 R N).ι) (h : (z : PSpace R N) ∈ (O1 R N).U i) (q : MvPolynomial (Fin (N + 1)) R),
      (coneHom (PSpace.str R N) (coord R N) z i h q = 0 ↔
        ∀ d, homogeneousComponent d q ∈ (z : ProjectiveSpectrum (homogeneousSubmodule (Fin (N + 1)) R)).asHomogeneousIdeal) := by
    intro i h q
    rw [C.coneHom_eq, Polynomial.ext_iff]
    apply forall_congr'
    intro d
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    erw [A.coeff_cone]
    erw [Scheme.evaluation_eq_zero_iff_notMem_basicOpen]
    have hd := homogeneousComponent_isHomogeneous d q
    have e : (eval₂Hom (algX (PSpace.str R N) ((O1 R N).U i)) fun n => (coord R N n).f i) (homogeneousComponent d q) =
        formOn (chart R N i) i le_rfl d _ hd :=
      ((formOn_eq_aeval (R := R) (N := N) (U := chart R N i) (i := i) (hi := le_rfl) hd).trans
        (eval₂Hom_eq R N ((O1 R N).U i) _ _).symm).symm
    erw [e, basicOpen_formOn]
    constructor
    · intro hn
      by_contra hc
      exact hn ⟨h, (Proj.mem_basicOpen _ _ _).2 hc⟩
    · rintro hm ⟨_, hb⟩
      exact (Proj.mem_basicOpen _ _ _).1 hb hm
  have hom : ∀ q : MvPolynomial (Fin (N + 1)) R,
      q ∈ (z : ProjectiveSpectrum (homogeneousSubmodule (Fin (N + 1)) R)).asHomogeneousIdeal.toIdeal ↔
        ∀ d, homogeneousComponent d q ∈ (z : ProjectiveSpectrum (homogeneousSubmodule (Fin (N + 1)) R)).asHomogeneousIdeal := by
    intro q
    rw [(z : ProjectiveSpectrum (homogeneousSubmodule (Fin (N + 1)) R)).asHomogeneousIdeal.isHomogeneous.mem_iff]
    exact forall_congr' fun d => by
      rw [show ((DirectSum.decompose (homogeneousSubmodule (Fin (N + 1)) R) q d : MvPolynomial (Fin (N + 1)) R)) =
        homogeneousComponent d q from decomposition.decompose'_apply q d]
      rfl
  ext q
  simp only [ptIdeal, Ideal.mem_iInf, RingHom.mem_ker]
  rw [hom]
  constructor
  · intro H
    have hz : (z : PSpace R N) ∈ ⨆ i, (O1 R N).U i := by
      rw [(O1_isLB R N).cover]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact (key i hi q).1 (H i hi)
  · intro H i hi
    exact (key i hi q).2 H

open GroundTheory.Heights₂.Heights in
/- English proof (translation)
The claim follows from `stMain_of (stVert stPts stPull stDiv) (stArch stPts (stCharts stPts)) (ChowHeightRecursion.of_leaves ChowFormSectionVertical.full GlobalTheory.CompanionTheory.Ar.Short.mahlerSection ChowFormBaseChange.full BaseChangeAvoid.full) ChowFormSection.full ChowHeightMul.full ProjPrimeHas …`.
-/
theorem stMain : StMain :=
  stMain_of (stVert stPts stPull stDiv) (stArch stPts (stCharts stPts))
    (ChowHeightRecursion.of_leaves ChowFormSectionVertical.full GlobalTheory.CompanionTheory.Ar.Short.mahlerSection ChowFormBaseChange.full
      BaseChangeAvoid.full) ChowFormSection.full ChowHeightMul.full ProjPrimeHasPoint.full

end FubiniStudyChowHeightFormula₂.Fs

/- English proof (translation)
Introduce `i y _`. Rewrite using `[Weight.fsBasis_φ, dualNorm_normOf, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Both sides reduce to the same expression.
-/
private theorem isFS_fsBasis_normOf {k : Type} [CommRing k] {Z : Scheme} (p : Z ⟶ Sp k) (σ : k →+* ℂ)
    {B : LB Z} {m : ℕ} (hB : B.IsLB) (b : Fin m → B.Sec) (hb : ⨆ (j : Fin m), nonzeroLocus (b j) = ⊤)
    (M : Matrix (Fin m) (Fin m) ℂ) (hM : M.det ≠ 0) :
    IsFS (Weight.fsBasis p σ hB b hb M hM) b (normOf M hM) := by
  intro i y _
  rw [Weight.fsBasis_φ, dualNorm_normOf, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  rfl

open FubiniStudyChowHeightFormula₂.Fs GroundTheory.Heights₂.Heights in

/- English proof (translation)
Introduce `K _ _ N e δ Y _ i _ hvar A hA hc f hf`. Set `Lfs` to `HermLB.fs (PSpace.str (𝓞 K) N) (O1_isLB (𝓞 K) N) (coord (𝓞 K) N) (FubiniStudyChowHeightFormula₂.Fs.emb (𝓞 K) N).cover A hA hc`. Set `L` to `Lfs.pull i (rfl : i ≫ PSpace.str (𝓞 K) N = i ≫ PSpace.str (𝓞 K) N)`. Use `show L.IsSelfInter _`. Take `⟨ht, hht⟩` from `(hE (𝓞 K) Y (i ≫ PSpace.str (𝓞 K) N) e hvar).1 L`.

Set `H : ArchData K (N + 1)` to `⟨fun σ => normOf (A (σ.comp (algebraMap (𝓞 K) K))) (hA _), fun σ u => by`. Take `⟨U, hU, hAU⟩` from `hc (σ.comp (algebraMap (𝓞 K) K))`. Conclude with `norm_normOf_conj (hA _) (hA _) hU hAU u⟩`. Establish `hs` using `stPull (𝓞 K) (PSpace (𝓞 K) N) Y (PSpace.str (𝓞 K) N) (O1 (𝓞 K) N) (N + 1) (coord (𝓞 K) N) i (FubiniStudyChowHeightFormula₂.Fs.emb (𝓞 K) N)`. Establish `hFS : ∀ σ : K →+* ℂ, IsFS (L.φ (σ.comp (algebraMap (𝓞 K) K))) (fun k => secPull (coord (𝓞 K) N k) i) (H.normAt σ)` using `fun σ => M.isFS_pull (isFS_fsBasis_normOf (PSpace.str (𝓞 K) N) (σ.comp (algebraMap (𝓞 K) K)) (O1_isLB (𝓞 K) N) (coord (𝓞 K) N) (FubiniStudyChowHeightFormula₂.Fs.emb (𝓞 K) N).cover (A (σ.comp (algebraMap (𝓞 K) K))) (hA _)) i`.

Establish `hgen : genIdeal (i ≫ PSpace.str (𝓞 K) N) (fun k => secPull (coord (𝓞 K) N k) i) = Ideal.map (MvPolynomial.map (algebraMap (𝓞 K) K)) (i (genericPoint Y)).asHomogeneousIdeal.toIdeal`. Simplify using `only [genIdeal]`. Rewrite using `[hs.2.1, FubiniStudyChowHeightFormula₂.Fs.ptIdeal_eq]`. Establish `hCF : IsChowForm (genIdeal (i ≫ PSpace.str (𝓞 K) N) (fun k => secPull (coord (𝓞 K) N k) i)) (e + 1) f`. Rewrite using `[hgen]`.

Use `⟨hf.ne_zero, fun g => ⟨fun hg => hf.dvd_of_forall_aeval_eq_zero (fun u hu => hg u ((hf.zero_iff u).1 hu)), ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨c, rfl⟩ u hu`. Rewrite using `[map_mul, (hf.zero_iff u).2 hu, zero_mul]`. Establish `hMH : IsMultiHomog δ f`. Introduce `d hd`.

Establish `h : ∀ b, ∑ j : Fin (N + 1), d (b, j) = δ` using `hf.homog d (MvPolynomial.mem_support_iff.2 hd)`. Use function extensionality and compare the values at `b`. Rewrite using `[← h b, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]`. Simplify using `only [Finset.sum_apply, groupWeight, Pi.single_apply, Fintype.sum_prod_type, smul_eq_mul]`. Rewrite using `[Finset.sum_eq_single b (fun a _ hab => by simp [Ne.symm hab]) (by simp)]`.

Simplify using the standard rewrite rules. Establish `key` using `FubiniStudyChowHeightFormula₂.Fs.stMain K (N + 1) H e Y (i ≫ PSpace.str (𝓞 K) N) L (fun k => secPull (coord (𝓞 K) N k) i) hvar hs.1 hFS δ f hCF hMH _ ⟨ht, hht, rfl⟩`. Establish `hfh` using `D.formHeight_one_eq (by omega : 1 ≤ N + 1) H δ hf.ne_zero`. Establish `hmat : (fun σ : K →+* ℂ => (H.normAt σ).mat⁻¹) = fun σ => A (σ.comp (algebraMap (𝓞 K) K))`. Use function extensionality and compare the values at `fun σ => Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 (hA _))`.

Rewrite `hfh` using `[hmat]`. Rewrite using `[hfh, ← key]`. Conclude with `⟨ht, hht, rfl⟩`.
-/
theorem FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of_arExists (hE : GlobalTheory.Published.ArExists) : GlobalTheory.Published.FubiniStudyChowHeight := by
  intro K _ _ N e δ Y _ i _ hvar A hA hc f hf
  let Lfs := HermLB.fs (PSpace.str (𝓞 K) N) (O1_isLB (𝓞 K) N) (coord (𝓞 K) N) (FubiniStudyChowHeightFormula₂.Fs.emb (𝓞 K) N).cover A hA hc
  let L := Lfs.pull i (rfl : i ≫ PSpace.str (𝓞 K) N = i ≫ PSpace.str (𝓞 K) N)
  show L.IsSelfInter _
  obtain ⟨ht, hht⟩ := (hE (𝓞 K) Y (i ≫ PSpace.str (𝓞 K) N) e hvar).1 L
  let H : ArchData K (N + 1) :=
    ⟨fun σ => normOf (A (σ.comp (algebraMap (𝓞 K) K))) (hA _), fun σ u => by
      obtain ⟨U, hU, hAU⟩ := hc (σ.comp (algebraMap (𝓞 K) K))
      exact norm_normOf_conj (hA _) (hA _) hU hAU u⟩
  have hs := stPull (𝓞 K) (PSpace (𝓞 K) N) Y (PSpace.str (𝓞 K) N) (O1 (𝓞 K) N) (N + 1) (coord (𝓞 K) N) i
    (FubiniStudyChowHeightFormula₂.Fs.emb (𝓞 K) N)
  have hFS : ∀ σ : K →+* ℂ, IsFS (L.φ (σ.comp (algebraMap (𝓞 K) K)))
      (fun k => secPull (coord (𝓞 K) N k) i) (H.normAt σ) := fun σ =>
    M.isFS_pull (isFS_fsBasis_normOf (PSpace.str (𝓞 K) N) (σ.comp (algebraMap (𝓞 K) K)) (O1_isLB (𝓞 K) N)
      (coord (𝓞 K) N) (FubiniStudyChowHeightFormula₂.Fs.emb (𝓞 K) N).cover (A (σ.comp (algebraMap (𝓞 K) K))) (hA _)) i
  have hgen : genIdeal (i ≫ PSpace.str (𝓞 K) N) (fun k => secPull (coord (𝓞 K) N k) i) =
      Ideal.map (MvPolynomial.map (algebraMap (𝓞 K) K)) (i (genericPoint Y)).asHomogeneousIdeal.toIdeal := by
    simp only [genIdeal]
    rw [hs.2.1, FubiniStudyChowHeightFormula₂.Fs.ptIdeal_eq]
  have hCF : IsChowForm (genIdeal (i ≫ PSpace.str (𝓞 K) N) (fun k => secPull (coord (𝓞 K) N k) i)) (e + 1) f := by
    rw [hgen]
    refine ⟨hf.ne_zero, fun g => ⟨fun hg => hf.dvd_of_forall_aeval_eq_zero
      (fun u hu => hg u ((hf.zero_iff u).1 hu)), ?_⟩⟩
    rintro ⟨c, rfl⟩ u hu
    rw [map_mul, (hf.zero_iff u).2 hu, zero_mul]
  have hMH : IsMultiHomog δ f := by
    intro d hd
    have h : ∀ b, ∑ j : Fin (N + 1), d (b, j) = δ := hf.homog d (MvPolynomial.mem_support_iff.2 hd)
    funext b
    rw [← h b, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp)]
    simp only [Finset.sum_apply, groupWeight, Pi.single_apply, Fintype.sum_prod_type, smul_eq_mul]
    rw [Finset.sum_eq_single b (fun a _ hab => by simp [Ne.symm hab]) (by simp)]
    simp
  have key := FubiniStudyChowHeightFormula₂.Fs.stMain K (N + 1) H e Y (i ≫ PSpace.str (𝓞 K) N) L
    (fun k => secPull (coord (𝓞 K) N k) i) hvar hs.1 hFS δ f hCF hMH _ ⟨ht, hht, rfl⟩
  have hfh := D.formHeight_one_eq (by omega : 1 ≤ N + 1) H δ hf.ne_zero
  have hmat : (fun σ : K →+* ℂ => (H.normAt σ).mat⁻¹) = fun σ => A (σ.comp (algebraMap (𝓞 K) K)) :=
    funext fun σ => Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.2 (hA _))
  rw [hmat] at hfh
  rw [hfh, ← key]
  exact ⟨ht, hht, rfl⟩

/- English proof (translation)
The claim follows from `FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of_arExists h.arExists`.
-/
theorem FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of (h : GlobalTheory.Published.ArCalc) : GlobalTheory.Published.FubiniStudyChowHeight :=
  FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of_arExists h.arExists

/- English proof (translation)
The claim follows from `FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of h.p4`.
-/
theorem FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of_hypotheses (h : GlobalTheory.CovTop.Hypotheses2) : GlobalTheory.Published.FubiniStudyChowHeight :=
  FubiniStudyChowHeightFormula₂.fubiniStudyChowHeight_of h.p4
