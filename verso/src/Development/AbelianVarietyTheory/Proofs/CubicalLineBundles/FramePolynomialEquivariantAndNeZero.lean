import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

/- English proof (translation)
The claim follows from `(GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 S hS a n F hF t y y' (((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2 ⟨g, h0, hd, h⟩)`.
-/
theorem evR_frChg_tri {S : Type} [CommRing S] [Algebra c.F S] (hS : IsReduced S) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) (t : Ix Dw → Sˣ)
    (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (h0 : ∀ τ i j, i < j → g τ i j = 0)
    (hd : ∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) {y y' : FrPt Xo c S} (h : FrChg g (t none : S) y y') :
    evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y :=
  (GlobalTheory.Frames.algebraic_laws GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c).2.2.2.2.2.2 S hS a n F hF t y y'
    (((GlobalTheory.Frames.frBor_calculus E H Dw l Xo c S y y' y').1 t).2 ⟨g, h0, hd, h⟩)

/- English proof (translation)
Take `⟨z, hz⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K S φ y`. Take `⟨z1, h1, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (X b).transpose) 1 (fun b => by rw [Matrix.det_transpose]; exact hX b)`. Take `⟨z2, h2, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z1 (fun b => (T b).transpose) 1 (fun b => by rw [Matrix.det_transpose]; exact hT b)`. Establish `h3` using `(GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S z z1 z2).2 _ _ _ _ h1 h2`. Simplify using `only [Units.val_one, _root_.mul_one, ← Matrix.transpose_mul] at h1 h2 h3`.

Rewrite using `[← hG S φ z z1 X hX hz h1, ← hG S φ z z2 (fun b => X b * T b) (fun b => by rw [Matrix.det_mul]; exact (hX b).mul (hT b)) hz h3]`. Set `t : Ix Dw → Sˣ` to `fun i => match i with`. Consider the case `none => 1`. Consider the case `some p => (hd p.1 p.2).unit`. Rewrite using `[evR_frChg_tri hS hF t (fun b => (T b).transpose) h0 (fun _ _ => rfl) h2]`.

Use `congr 1`. Simplify using `[wchar, Fintype.prod_option, Fintype.prod_sigma, t, ex]`.
-/
theorem evalFr_mul_tri {K : Type} [CommRing K] [Algebra c.F K] {y : FrPt Xo c K} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {G : MvPolynomial (FrVar Dw.mult) K} (hG : IsFrPoly F y G)
    {S : Type} [CommRing S] [Algebra c.F S] (hS : IsReduced S) (φ : K →ₐ[c.F] S)
    (X T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (hX : ∀ b, IsUnit (X b).det)
    (hT : ∀ b, IsUnit (T b).det) (h0 : ∀ τ i j, i < j → T τ j i = 0) (hd : ∀ τ i, IsUnit (T τ i i)) :
    evalFr (MvPolynomial.map φ.toRingHom G) (fun b => X b * T b) =
      (∏ b, ∏ i : Fin (Dw.mult b), T b i i ^ a (b, i)) * evalFr (MvPolynomial.map φ.toRingHom G) X := by
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K S φ y
  obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z (fun b => (X b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hX b)
  obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S z1 (fun b => (T b).transpose) 1
    (fun b => by rw [Matrix.det_transpose]; exact hT b)
  have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c S z z1 z2).2 _ _ _ _ h1 h2
  simp only [Units.val_one, _root_.mul_one, ← Matrix.transpose_mul] at h1 h2 h3
  rw [← hG S φ z z1 X hX hz h1, ← hG S φ z z2 (fun b => X b * T b)
    (fun b => by rw [Matrix.det_mul]; exact (hX b).mul (hT b)) hz h3]
  let t : Ix Dw → Sˣ := fun i => match i with
    | none => 1
    | some p => (hd p.1 p.2).unit
  rw [evR_frChg_tri hS hF t (fun b => (T b).transpose) h0 (fun _ _ => rfl) h2]
  congr 1
  simp [wchar, Fintype.prod_option, Fintype.prod_sigma, t, ex]

end

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c K _ _ y a n F hF G hG`. Use `⟨fun σ X b t hX ht htri => ?_, fun σ σ₁ w hw hne hG0 => hne ?_⟩` and prove the remaining obligations. Establish `hred : IsReduced (CAt (σ.comp (algebraMap c.F K)))` using `inferInstanceAs (IsReduced ℂ)`. Establish `hdiag : ∀ i, t i i ≠ 0`. Rewrite `ht` using `[Matrix.det_of_upperTriangular htri]`.

Conclude with `fun i => Finset.prod_ne_zero_iff.1 ht i (Finset.mem_univ i)`. Set `T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ` to `Function.update (fun _ => 1) b t`. Establish `hT : ∀ b', IsUnit (T b').det`. Introduce `b'`. Distinguish the cases in `hb : b' = b`.

Substitute `hb` using the available equality. Simplify `ht` using `[T]`. Simplify using `[T, Function.update_of_ne hb]`. Establish `h0 : ∀ τ i j, i < j → T τ j i = 0`. Introduce `b' i j hij`.

Distinguish the cases in `hb : b' = b`. Substitute `hb` using the available equality. Simplify `htri hij` using `[T]`. Simplify using `[T, Function.update_of_ne hb, Matrix.one_apply_ne hij.ne']`. Establish `hd : ∀ τ i, IsUnit (T τ i i)`.

Introduce `b' i`. Distinguish the cases in `hb : b' = b`. Substitute `hb` using the available equality. Simplify `hdiag i` using `[T]`. Simplify using `[T, Function.update_of_ne hb]`.

Establish `key : evalFr (MvPolynomial.map σ G) (fun b => X b * T b) = (∏ b, ∏ i : Fin (Dw.mult b), T b i i ^ a (b, i)) * evalFr (MvPolynomial.map σ G) X` using `evalFr_mul_tri hF hG hred (embAlg (c := c) σ) X T (fun b' => (Ne.isUnit (hX b') : IsUnit (X b').det)) hT h0 hd`. Establish `e1 : Function.update X b (X b * t) = fun b => X b * T b`. Use function extensionality and compare the values at `b'`. Distinguish the cases in `hb : b' = b`. Substitute `hb` using the available equality.

Simplify using `[T]`. Simplify using `[T, Function.update_of_ne hb]`. Rewrite using `[e1, key]`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single b]`.

Simplify using `[T, ReciprocityTheory.MultiplicativeHeights.triChar]`. Introduce `b' _ hb`. Simplify using `[T, Function.update_of_ne hb]`. Simplify using the standard rewrite rules. Establish `hred : IsReduced (CAt σ)` using `inferInstanceAs (IsReduced ℂ)`.

Take `⟨z, hz⟩` from `GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K _ σ₁ y`. Take `⟨g, s, hg, hzw⟩` from `(GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c _ z w).1 (hw.symm.trans hz.1.symm)`. Take `⟨z1, h1, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g 1 hg`. Take `⟨z2, h2, -⟩` from `GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)`. Establish `h3` using `(GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c _ z z1 z2).2 _ _ _ _ h1 h2`.

Simplify using `only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3`. Establish `e : z2 = w` using `(GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g s hg).unique h3 hzw`. Substitute `e` using the available equality. Establish `hv` using `hG _ σ₁ z z1 (fun b => (g b).transpose) (fun b => by rw [Matrix.det_transpose]; exact hg b) hz h1`. Set `t : Ix Dw → (CAt σ)ˣ` to `fun i => match i with`.

Consider the case `none => s`. Consider the case `some _ => 1`. Rewrite using `[evR_frChg_tri hred hF t (fun _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne) (fun τ i => Matrix.one_apply_eq i) h2, hv, hG0]`. Simplify using `[evalFr]`.
-/
theorem isFrPoly_equiv_and_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ F ∈ sec Xo c a n, ∀ G : MvPolynomial (FrVar Dw.mult) K, IsFrPoly F y G → (∀ [DecidableEq (E →+* ℂ)] (σ : K →+* ℂ), IsEquiv (fun b (i : Fin (Dw.mult b)) => a (b, i)) (MvPolynomial.map σ G)) ∧ ∀ (σ : c.F →+* ℂ) (σ₁ : K →ₐ[c.F] CAt σ) (w : FrPt Xo c (CAt σ)), spMap σ₁.toRingHom ≫ y.x = w.x → evR Xo c F w ≠ 0 → G ≠ 0 := by
  intro E _ _ _ H Dw l Xo c K _ _ y a n F hF G hG
  refine ⟨fun σ X b t hX ht htri => ?_, fun σ σ₁ w hw hne hG0 => hne ?_⟩
  · have hred : IsReduced (CAt (σ.comp (algebraMap c.F K))) := inferInstanceAs (IsReduced ℂ)
    have hdiag : ∀ i, t i i ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri] at ht
      exact fun i => Finset.prod_ne_zero_iff.1 ht i (Finset.mem_univ i)
    let T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := Function.update (fun _ => 1) b t
    have hT : ∀ b', IsUnit (T b').det := by
      intro b'
      by_cases hb : b' = b
      · subst hb; simpa [T] using ht
      · simp [T, Function.update_of_ne hb]
    have h0 : ∀ τ i j, i < j → T τ j i = 0 := by
      intro b' i j hij
      by_cases hb : b' = b
      · subst hb; simpa [T] using htri hij
      · simp [T, Function.update_of_ne hb, Matrix.one_apply_ne hij.ne']
    have hd : ∀ τ i, IsUnit (T τ i i) := by
      intro b' i
      by_cases hb : b' = b
      · subst hb; simpa [T] using hdiag i
      · simp [T, Function.update_of_ne hb]
    have key : evalFr (MvPolynomial.map σ G) (fun b => X b * T b) =
        (∏ b, ∏ i : Fin (Dw.mult b), T b i i ^ a (b, i)) * evalFr (MvPolynomial.map σ G) X :=
      evalFr_mul_tri hF hG hred (embAlg (c := c) σ) X T (fun b' => (Ne.isUnit (hX b') : IsUnit (X b').det)) hT h0 hd
    have e1 : Function.update X b (X b * t) = fun b => X b * T b := by
      funext b'
      by_cases hb : b' = b
      · subst hb; simp [T]
      · simp [T, Function.update_of_ne hb]
    rw [e1, key]
    congr 1
    rw [Finset.prod_eq_single b]
    · simp [T, ReciprocityTheory.MultiplicativeHeights.triChar]
    · intro b' _ hb
      simp [T, Function.update_of_ne hb]
    · simp
  · have hred : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
    obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K _ σ₁ y
    obtain ⟨g, s, hg, hzw⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c _ z w).1 (hw.symm.trans hz.1.symm)
    obtain ⟨z1, h1, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g 1 hg
    obtain ⟨z2, h2, -⟩ := GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z1 (fun _ => 1) s (fun _ => by simp)
    have h3 := (GlobalTheory.Frames.frChg_refl_and_comp E H Dw l Xo c _ z z1 z2).2 _ _ _ _ h1 h2
    simp only [Units.val_one, _root_.mul_one, _root_.one_mul] at h1 h3
    have e : z2 = w := (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c _ z g s hg).unique h3 hzw
    subst e
    have hv := hG _ σ₁ z z1 (fun b => (g b).transpose) (fun b => by rw [Matrix.det_transpose]; exact hg b) hz h1
    let t : Ix Dw → (CAt σ)ˣ := fun i => match i with
      | none => s
      | some _ => 1
    rw [evR_frChg_tri hred hF t (fun _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne)
      (fun τ i => Matrix.one_apply_eq i) h2, hv, hG0]
    simp [evalFr]

end GlobalTheory.LamT
