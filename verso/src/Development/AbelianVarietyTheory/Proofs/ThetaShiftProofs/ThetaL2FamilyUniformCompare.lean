import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.WeilEqIffHermFormEqComplex
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAddFundamentalDomainLatticeDomain

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.GeneratorNorm

section Analytic

open MeasureTheory

variable {g : ℕ} {ι L : Type} [AddCommGroup L]

/- English proof (translation)
Use `haveI : DiscreteTopology Λ.toIntSubmodule := dP`. Use `haveI : IsZLattice ℝ Λ.toIntSubmodule := ⟨sP⟩`. Take `⟨x₀, hx₀⟩` from `exists_forall_le_of_periodic Λ.toIntSubmodule hf.continuous.norm (fun a ha x => hp x a ha)`. Use `hf.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.2 ⟨‖f x₀‖, ?_⟩) z w` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`.

Conclude with `hx₀ x`.
-/
theorem const_of_norm_periodic (Λ : AddSubgroup (Fin g → ℂ)) (dP : DiscreteTopology Λ)
    (sP : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (f : (Fin g → ℂ) → ℂ) (hf : Differentiable ℂ f)
    (hp : ∀ z, ∀ a ∈ Λ, ‖f (z + a)‖ = ‖f z‖) (z w : Fin g → ℂ) : f z = f w := by
  haveI : DiscreteTopology Λ.toIntSubmodule := dP
  haveI : IsZLattice ℝ Λ.toIntSubmodule := ⟨sP⟩
  obtain ⟨x₀, hx₀⟩ := exists_forall_le_of_periodic Λ.toIntSubmodule hf.continuous.norm (fun a ha x => hp x a ha)
  refine hf.apply_eq_apply_of_bounded (isBounded_iff_forall_norm_le.2 ⟨‖f x₀‖, ?_⟩) z w
  rintro _ ⟨x, rfl⟩
  exact hx₀ x

/- English proof (translation)
Use `choose k hk using Uc`. Use `set q : (Fin g → ℂ) → ℂ := fun z => fr' (k z) z / fr (k z) z with hqdef`. Establish `hq : ∀ j z, U j z → q z = fr' j z / fr j z` using `fun j z hz => by`. Establish `h1` using `n j z hz`. Rewrite `h1` using `[c j (k z) z hz (hk z)]`.

Rewrite using `[c j (k z) z hz (hk z), c' j (k z) z hz (hk z), mul_div_mul_left _ _ (left_ne_zero_of_mul h1)]`. Establish `hd : Differentiable ℂ q` using `fun z => by`. Establish `hm : {w | U (k z) w} ∈ nhds z` using `(Uo _).mem_nhds (hk z)`. Use `((((d' (k z)).differentiableAt hm).mul (((d (k z)).differentiableAt hm).inv (n _ _ (hk z))))).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [hm] with w hw using (hq _ _ hw).trans (div_eq_mul_inv _ _)`.

Establish `hc` using `const_of_norm_periodic P.range dP sP q hd (by`. Introduce and unpack `z _ ⟨a, rfl⟩`. Establish `h1` using `norm_ne_zero_iff.2 (n _ _ (hk z))`. Rewrite `h1` using `[p a _ _ (hk z)]`. Rewrite using `[hq _ _ (hk z), hq _ _ (Up _ _ a (hk z)), norm_div, norm_div, p a _ _ (hk z), p' a _ _ (hk z), mul_div_mul_left _ _ (left_ne_zero_of_mul h1)]) z 0`.

Rewrite `hc` using `[hq j z hz, hq _ _ (hk 0), o _ (hk 0), div_self (n _ _ (hk 0)), div_eq_one_iff_eq (n j z hz)]`. Conclude with `hc`.
-/
theorem frames_eq (P : L →+ (Fin g → ℂ)) (dP : DiscreteTopology P.range) (sP : Submodule.span ℝ (Set.range P) = ⊤)
    (U : ι → (Fin g → ℂ) → Prop) (Uo : ∀ j, IsOpen {z | U j z}) (Uc : ∀ z, ∃ j, U j z)
    (Up : ∀ j z a, U j z → U j (z + P a)) (tr : ι → ι → (Fin g → ℂ) → ℂ) (fr fr' : ι → (Fin g → ℂ) → ℂ)
    (A : L → (Fin g → ℂ) → ℝ)
    (d : ∀ j, DifferentiableOn ℂ (fr j) {z | U j z}) (d' : ∀ j, DifferentiableOn ℂ (fr' j) {z | U j z})
    (n : ∀ j z, U j z → fr j z ≠ 0)
    (c : ∀ j j' z, U j z → U j' z → fr j z = tr j j' z * fr j' z)
    (c' : ∀ j j' z, U j z → U j' z → fr' j z = tr j j' z * fr' j' z)
    (o : ∀ j, U j 0 → fr' j 0 = fr j 0)
    (p : ∀ a j z, U j z → ‖fr j z‖ = A a z * ‖fr j (z + P a)‖)
    (p' : ∀ a j z, U j z → ‖fr' j z‖ = A a z * ‖fr' j (z + P a)‖) (j z) (hz : U j z) : fr' j z = fr j z := by
  choose k hk using Uc
  set q : (Fin g → ℂ) → ℂ := fun z => fr' (k z) z / fr (k z) z with hqdef
  have hq : ∀ j z, U j z → q z = fr' j z / fr j z := fun j z hz => by
    have h1 := n j z hz
    rw [c j (k z) z hz (hk z)] at h1
    rw [c j (k z) z hz (hk z), c' j (k z) z hz (hk z), mul_div_mul_left _ _ (left_ne_zero_of_mul h1)]
  have hd : Differentiable ℂ q := fun z => by
    have hm : {w | U (k z) w} ∈ nhds z := (Uo _).mem_nhds (hk z)
    refine ((((d' (k z)).differentiableAt hm).mul
      (((d (k z)).differentiableAt hm).inv (n _ _ (hk z))))).congr_of_eventuallyEq ?_
    filter_upwards [hm] with w hw using (hq _ _ hw).trans (div_eq_mul_inv _ _)
  have hc := const_of_norm_periodic P.range dP sP q hd (by
    rintro z _ ⟨a, rfl⟩
    have h1 := norm_ne_zero_iff.2 (n _ _ (hk z))
    rw [p a _ _ (hk z)] at h1
    rw [hq _ _ (hk z), hq _ _ (Up _ _ a (hk z)), norm_div, norm_div, p a _ _ (hk z), p' a _ _ (hk z),
      mul_div_mul_left _ _ (left_ne_zero_of_mul h1)]) z 0
  rw [hq j z hz, hq _ _ (hk 0), o _ (hk 0), div_self (n _ _ (hk 0)), div_eq_one_iff_eq (n j z hz)] at hc
  exact hc

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Use `congr 1`. Rewrite using `[show (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]`.
-/
theorem norm_factor (Hm : Matrix (Fin g) (Fin g) ℂ) (z a : Fin g → ℂ) :
    ‖Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a)‖ =
      Real.exp (Real.pi * (hermForm Hm z a).re + Real.pi / 2 * (hermForm Hm a a).re) := by
  rw [Complex.norm_exp]
  congr 1
  rw [show (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.add_re, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]

/- English proof (translation)
Establish `h : hermForm Hm a z = star (hermForm Hm z a)`. Rewrite using `[hermForm, hermForm, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, ← Matrix.dotProduct_mulVec]`. Establish `e : hermForm Hm (z + a) (z + a) = hermForm Hm z z + hermForm Hm z a + hermForm Hm a z + hermForm Hm a a`. Simplify using `only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, h]`. Simplify using `only [Complex.add_re, Complex.star_def, Complex.conj_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem re_hermForm_add {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z a : Fin g → ℂ) :
    (hermForm Hm (z + a) (z + a)).re =
      (hermForm Hm z z).re + 2 * (hermForm Hm z a).re + (hermForm Hm a a).re := by
  have h : hermForm Hm a z = star (hermForm Hm z a) := by
    rw [hermForm, hermForm, ← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq,
      ← Matrix.dotProduct_mulVec]
  have e : hermForm Hm (z + a) (z + a) = hermForm Hm z z + hermForm Hm z a + hermForm Hm a z + hermForm Hm a a := by
    simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct]
    ring
  rw [e, h]
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re]
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `hc : Continuous θ` using `continuous_iff_continuousAt.2 fun z => by`. Take `⟨j, hj⟩` from `Uc z`. Establish `hm : {w | U j w} ∈ nhds z` using `(Uo _).mem_nhds hj`. Use `(((dS j).differentiableAt hm).continuousAt.div ((d j).differentiableAt hm).continuousAt (n _ _ hj)).congr ?_` and prove the remaining obligations.

Use `filter_upwards [hm] with w hw`. Rewrite using `[Pi.div_apply, hθ j w hw, mul_div_cancel_right₀ _ (n j w hw)]`. Establish `hh : Continuous fun z : Fin g → ℂ => hermForm Hm z z`. Unfold `hermForm`. Conclude with `continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star)`.

Use `fun_prop`. Introduce `a z`. Take `⟨j, hj⟩` from `Uc z`. Establish `h1` using `congrArg norm (Sp a j z)`. Rewrite `h1` using `[hθ j z hj, hθ j _ (Up j z a hj), norm_mul, norm_mul, p a j z hj, ← mul_assoc]`.

Establish `h2` using `mul_right_cancel₀ (norm_ne_zero_iff.2 (n _ _ (Up j z a hj))) h1`. Rewrite using `[h2, re_hermForm_add hH, mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem density (P : L →+ (Fin g → ℂ)) {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (U : ι → (Fin g → ℂ) → Prop) (Uo : ∀ j, IsOpen {z | U j z}) (Uc : ∀ z, ∃ j, U j z)
    (Up : ∀ j z a, U j z → U j (z + P a)) (fr S : ι → (Fin g → ℂ) → ℂ) (θ : (Fin g → ℂ) → ℂ)
    (d : ∀ j, DifferentiableOn ℂ (fr j) {z | U j z}) (dS : ∀ j, DifferentiableOn ℂ (S j) {z | U j z})
    (n : ∀ j z, U j z → fr j z ≠ 0)
    (p : ∀ a j z, U j z → ‖fr j z‖ =
      Real.exp (Real.pi * (hermForm Hm z (P a)).re + Real.pi / 2 * (hermForm Hm (P a) (P a)).re) * ‖fr j (z + P a)‖)
    (Sp : ∀ a j z, S j (z + P a) = S j z) (hθ : ∀ j z, U j z → S j z = θ z * fr j z) :
    Continuous (fun z => ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) ∧
      ∀ a z, ‖θ (z + P a)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm (z + P a) (z + P a)).re) =
        ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re) := by
  constructor
  · have hc : Continuous θ := continuous_iff_continuousAt.2 fun z => by
      obtain ⟨j, hj⟩ := Uc z
      have hm : {w | U j w} ∈ nhds z := (Uo _).mem_nhds hj
      refine (((dS j).differentiableAt hm).continuousAt.div ((d j).differentiableAt hm).continuousAt
        (n _ _ hj)).congr ?_
      filter_upwards [hm] with w hw
      rw [Pi.div_apply, hθ j w hw, mul_div_cancel_right₀ _ (n j w hw)]
    have hh : Continuous fun z : Fin g → ℂ => hermForm Hm z z := by
      unfold hermForm
      exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_star)
    fun_prop
  · intro a z
    obtain ⟨j, hj⟩ := Uc z
    have h1 := congrArg norm (Sp a j z)
    rw [hθ j z hj, hθ j _ (Up j z a hj), norm_mul, norm_mul, p a j z hj, ← mul_assoc] at h1
    have h2 := mul_right_cancel₀ (norm_ne_zero_iff.2 (n _ _ (Up j z a hj))) h1
    rw [h2, re_hermForm_add hH, mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring

/- English proof (translation)
Establish `hF' : IsAddFundamentalDomain Λ.toIntSubmodule Fd volume` using `hF`. Rewrite using `[latticeMean_eq Λ.toIntSubmodule volume hF' hf, ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF', smul_eq_mul, div_eq_inv_mul]`. Both sides reduce to the same expression.
-/
theorem mean_eq (Λ : AddSubgroup (Fin g → ℂ)) [DiscreteTopology Λ.toIntSubmodule] [IsZLattice ℝ Λ.toIntSubmodule]
    {Fd : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain Λ Fd volume) {f : (Fin g → ℂ) → ℝ}
    (hf : ∀ a ∈ Λ, ∀ x, f (x + a) = f x) :
    (∫ z in Fd, f z) / (volume Fd).toReal = latticeMean Λ.toIntSubmodule f := by
  have hF' : IsAddFundamentalDomain Λ.toIntSubmodule Fd volume := hF
  rw [latticeMean_eq Λ.toIntSubmodule volume hF' hf,
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ hF', smul_eq_mul, div_eq_inv_mul]
  rfl

/- English proof (translation)
Use `haveI : DiscreteTopology Λ.toIntSubmodule := dP`. Use `haveI : DiscreteTopology Λ'.toIntSubmodule := dP'`. Use `haveI : IsZLattice ℝ Λ.toIntSubmodule := ⟨sP⟩`. Use `haveI : IsZLattice ℝ Λ'.toIntSubmodule := ⟨sP'⟩`. Establish `hf' : ∀ a ∈ Λ', ∀ x, f' (x + a) = f' x` using `fun a ha x => by`.

Take `⟨a, rfl⟩` from `h.surjective a`. Take `⟨x, rfl⟩` from `h.surjective x`. Rewrite using `[← map_add, hff, hff, hf a ((hh a).1 ha)]`. Rewrite using `[mean_eq Λ hF hf, mean_eq Λ' hF' hf']`. Use `⟨lt_of_le_of_ne (latticeMean_nonneg _ h0) fun e => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨x, hx⟩` from `hne`. Conclude with `hx (congrFun (eq_zero_of_latticeMean_eq_zero _ hc h0 hf e.symm) x)`. Rewrite using `[← latticeMean_comp_equiv Λ.toIntSubmodule Λ'.toIntSubmodule (h.restrictScalars ℝ).toContinuousLinearEquiv hh hf', ← latticeMean_const_mul]`. Conclude with `congrArg _ (funext hff)`.
-/
theorem mean_pos_and_scale (Λ Λ' : AddSubgroup (Fin g → ℂ)) (dP : DiscreteTopology Λ) (dP' : DiscreteTopology Λ')
    (sP : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (sP' : Submodule.span ℝ (Λ' : Set (Fin g → ℂ)) = ⊤)
    (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (hh : ∀ x, h x ∈ Λ' ↔ x ∈ Λ)
    {Fd Fd' : Set (Fin g → ℂ)} (hF : IsAddFundamentalDomain Λ Fd volume) (hF' : IsAddFundamentalDomain Λ' Fd' volume)
    {f f' : (Fin g → ℂ) → ℝ} (t : ℝ) (hc : Continuous f) (h0 : ∀ x, 0 ≤ f x) (hne : ∃ x, f x ≠ 0)
    (hf : ∀ a ∈ Λ, ∀ x, f (x + a) = f x) (hff : ∀ x, f' (h x) = t * f x) :
    0 < (∫ z in Fd, f z) / (volume Fd).toReal ∧
      (∫ z in Fd', f' z) / (volume Fd').toReal = t * ((∫ z in Fd, f z) / (volume Fd).toReal) := by
  haveI : DiscreteTopology Λ.toIntSubmodule := dP
  haveI : DiscreteTopology Λ'.toIntSubmodule := dP'
  haveI : IsZLattice ℝ Λ.toIntSubmodule := ⟨sP⟩
  haveI : IsZLattice ℝ Λ'.toIntSubmodule := ⟨sP'⟩
  have hf' : ∀ a ∈ Λ', ∀ x, f' (x + a) = f' x := fun a ha x => by
    obtain ⟨a, rfl⟩ := h.surjective a
    obtain ⟨x, rfl⟩ := h.surjective x
    rw [← map_add, hff, hff, hf a ((hh a).1 ha)]
  rw [mean_eq Λ hF hf, mean_eq Λ' hF' hf']
  refine ⟨lt_of_le_of_ne (latticeMean_nonneg _ h0) fun e => ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact hx (congrFun (eq_zero_of_latticeMean_eq_zero _ hc h0 hf e.symm) x)
  · rw [← latticeMean_comp_equiv Λ.toIntSubmodule Λ'.toIntSubmodule
      (h.restrictScalars ℝ).toContinuousLinearEquiv hh hf', ← latticeMean_const_mul]
    exact congrArg _ (funext hff)

end Analytic

section Fibre

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

noncomputable def fibLift (x : Sp ℂ ⟶ Xo.X) (e : Sp ℂ ⟶ Xo.univ.t.G.left) (he : e ≫ Xo.univ.t.G.hom = x) :
    Sp ℂ ⟶ Gx x :=
  pullback.lift (f := x) (g := Xo.univ.t.G.hom) (𝟙 _) e (by rw [Category.id_comp, he])

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
theorem fibLift_fst (x : Sp ℂ ⟶ Xo.X) (e : Sp ℂ ⟶ Xo.univ.t.G.left) (he : e ≫ Xo.univ.t.G.hom = x) :
    fibLift x e he ≫ gxFst x = e := pullback.lift_snd _ _ _

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
theorem fibLift_snd (x : Sp ℂ ⟶ Xo.X) (e : Sp ℂ ⟶ Xo.univ.t.G.left) (he : e ≫ Xo.univ.t.G.hom = x) :
    fibLift x e he ≫ gxSnd x = 𝟙 _ := pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `IsPullback.of_hasPullback x Xo.univ.t.G.hom`.
-/
theorem isPullback_gx (x : Sp ℂ ⟶ Xo.X) : IsPullback (gxSnd x) (gxFst x) x Xo.univ.t.G.hom :=
  IsPullback.of_hasPullback x Xo.univ.t.G.hom

/- English proof (translation)
Use `HolFibre.isHolTo_of_isPullback (isPullback_gx x) ?_ ?_` and prove the remaining obligations. Simplify using `only [fibLift_snd]`. Conclude with `HolFibre.isHolTo_const isOpen_univ _`. Simplify using `only [fibLift_fst]`. Conclude with `hol`.
-/
theorem isHolTo_fibLift {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (x : Sp ℂ ⟶ Xo.X)
    (e : V → (Sp ℂ ⟶ Xo.univ.t.G.left)) (he : ∀ z, e z ≫ Xo.univ.t.G.hom = x) (hol : IsHolTo Set.univ e) :
    IsHolTo Set.univ fun z => fibLift x (e z) (he z) := by
  refine HolFibre.isHolTo_of_isPullback (isPullback_gx x) ?_ ?_
  · simp only [fibLift_snd]
    exact HolFibre.isHolTo_const isOpen_univ _
  · simp only [fibLift_fst]
    exact hol

/- English proof (translation)
Rewrite using `[Category.assoc, ← (isPullback_gx x).w, ← Category.assoc, h, Category.id_comp]`.
-/
theorem over_of_snd (x : Sp ℂ ⟶ Xo.X) (pt : Sp ℂ ⟶ Gx x) (h : pt ≫ gxSnd x = 𝟙 _) :
    (pt ≫ gxFst x) ≫ Xo.univ.t.G.hom = x := by
  rw [Category.assoc, ← (isPullback_gx x).w, ← Category.assoc, h, Category.id_comp]

open MonObj in
/- English proof (translation)
Rewrite using `[Fu.ex_add i P hP, (Fu.ex_ker i P hP _).2 ⟨a, rfl⟩, _root_.mul_one]`.
-/
theorem ex_periodic {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty P) (z a) : Fu.ex i P (z + P a) = Fu.ex i P z := by
  rw [Fu.ex_add i P hP, (Fu.ex_ker i P hP _).2 ⟨a, rfl⟩, _root_.mul_one]

/- English proof (translation)
Substitute `he` using the available equality. Conclude with `⟨fun h _ hp => Set.mem_iInter.1 (h hp) 0, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩`.
-/
theorem chart_iff (x : Sp ℂ ⟶ Xo.X) (pt : Sp ℂ ⟶ Gx x) (j : Xo.univ.t.PP.L.ι) {e : Sp ℂ ⟶ Xo.univ.t.G.left}
    (he : pt ≫ gxFst x = e) : ⊤ ≤ pt ⁻¹ᵁ (PPx x).U (fun _ => j) ↔ ⊤ ≤ e ⁻¹ᵁ Xo.univ.t.PP.L.U j := by
  subst he
  exact ⟨fun h _ hp => Set.mem_iInter.1 (h hp) 0, fun h _ hp => Set.mem_iInter.2 fun _ => h hp⟩

/- English proof (translation)
Take `⟨pm, h1, h2, h3⟩` from `h`. Establish `hid : spMap (RingHom.id ℂ) = 𝟙 _` using `by simp [spMap]`. Establish `: pm = 𝟙 _` using `(isPullback_gx x).hom_ext (by rw [Category.id_comp]; exact h2.trans (by rw [hid]; exact Category.comp_id _)) (by rw [Category.id_comp]; exact h1)`. Substitute `this` using the available equality. Establish `e : ∀ h, Scheme.Hom.appLE (𝟙 (Gx x)) ((PPx x).U i) ((PPx x).U i) h = 𝟙 _` using `fun h => by`.

Rewrite using `[Scheme.Hom.appLE, Scheme.Hom.id_app]`. Use `(Category.id_comp _).trans ?_` and prove the remaining obligations. Rewrite using `[← (Gx x).presheaf.map_id]`. Both sides reduce to the same expression. Conclude with `(h3 i le_rfl).symm.trans (congrArg (fun φ => φ.hom (scal x a i * s.f i)) (e _))`.
-/
theorem sec_eq_of_secBC {x : Sp ℂ ⟶ Xo.X} {a : ℂ} {s s' : LB.Sec (PPx x)} (h : SecBC (RingHom.id ℂ) a x x s s') (i) :
    s'.f i = scal x a i * s.f i := by
  obtain ⟨pm, h1, h2, h3⟩ := h
  have hid : spMap (RingHom.id ℂ) = 𝟙 _ := by simp [spMap]
  have : pm = 𝟙 _ := (isPullback_gx x).hom_ext
    (by rw [Category.id_comp]; exact h2.trans (by rw [hid]; exact Category.comp_id _))
    (by rw [Category.id_comp]; exact h1)
  subst this
  have e : ∀ h, Scheme.Hom.appLE (𝟙 (Gx x)) ((PPx x).U i) ((PPx x).U i) h = 𝟙 _ := fun h => by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    refine (Category.id_comp _).trans ?_
    rw [← (Gx x).presheaf.map_id]
    rfl
  exact (h3 i le_rfl).symm.trans (congrArg (fun φ => φ.hom (scal x a i * s.f i)) (e _))

end Fibre

/- English proof (translation)
Introduce `_ laws2 E _ _ _ H Dw l Xo c σ g ty Fu i i' Pm Pm' y y' G s v v' hP hP' hy hy' ⟨hx, _, hBC⟩ ⟨Hm, χ, fr, θ, Fd, hH, _, him, d, n, cp, o, p, hθ, hF, hv⟩ ⟨Hm', χ', fr', θ', Fd', hH', _, him', d', n', cp', o', p', hθ', hF', hv'⟩`. Take `⟨x, _, _, _, _, _, sc, gen⟩` from `y`. Take `⟨x', _, _, _, _, _, sc', gen'⟩` from `y'`. Simplify using `only at hx hBC hy hy' o o' hθ hθ'`. Substitute `hx` using the available equality.

Take `⟨h, gam, hex, hg, hEF, -⟩` from `familyUnif_exp_unique E H Dw l Xo _ g ty Fu i i' Pm Pm' hP hP' (hy.symm.trans hy')`. Take `⟨sv, sg, -⟩` from `sec_values_complex_fibre laws2.secTwist E H Dw l Xo x' sc`. Establish `hs` using `sec_eq_of_secBC (x := x') hBC`. Establish `hHH : ∀ z w, hermForm Hm' (h z) (h w) = hermForm Hm z w` using `fun z w => CM.HermWeil.hermForm_eq_of_im Hm' Hm h.toLinearMap h.toLinearMap LinearMap.id LinearMap.id hP.2.2.2.1 hP.2.2.2.1 (by`. Introduce and unpack `_ ⟨a, rfl⟩ _ ⟨b, rfl⟩`.

Use `show (hermForm Hm' (h (Pm a)) (h (Pm b))).im = (hermForm Hm (Pm a) (Pm b)).im`. Rewrite using `[← hg, ← hg, him', him, hEF]) z w`. Establish `hol` using `ExpUniqFamily.isHolTo_ex Fu i Pm hP`. Establish `per` using `ex_periodic Fu i Pm hP`. Establish `ov : ∀ z, (Fu.ex i Pm z).left ≫ Xo.univ.t.G.hom = x'` using `fun z => (Over.w (Fu.ex i Pm z)).trans hy.symm`.

Set `U : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → Prop` to `fun j z => ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j`. Establish `Uo : ∀ j, IsOpen {z | U j z}` using `fun j => by`. Simplify `(hol (Xo.univ.t.PP.L.U j) 0).1` using `only [Set.mem_univ, true_and]`. Establish `Uc : ∀ z, ∃ j, U j z` using `fun z => by`. Use `Xo.univ.t.PP.isLB.cover.ge (Set.mem_univ ((Fu.ex i Pm z).left (default : PrimeSpectrum ℂ)))` as an intermediate fact.

Take `⟨j, hj⟩` from `TopologicalSpace.Opens.mem_iSup.1 this`. Conclude with `⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩`. Establish `Up : ∀ j z a, U j z → U j (z + Pm a)` using `fun j z a hz => by`. Simplify using `only [U, per]`. Conclude with `hz`.

Establish `U' : ∀ j z, U j z → ⊤ ≤ (Fu.ex i' Pm' (h z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j` using `fun j z hz => by`. Rewrite using `[hex]`. Conclude with `hz`. Establish `q : ∀ a j z, U j z → ‖fr j z‖ = Real.exp (Real.pi * (hermForm Hm z (Pm a)).re + Real.pi / 2 * (hermForm Hm (Pm a) (Pm a)).re) * ‖fr j (z + Pm a)‖` using `fun a j z hz => by`. Rewrite using `[(p a j z).2 hz, norm_mul, norm_mul, (p a j z).1, _root_.one_mul, norm_factor]`.

Establish `hfr : ∀ j z, U j z → fr' j (h z) = fr j z` using `frames_eq Pm hP.2.2.1 hP.2.2.2.1 U Uo Uc Up (fun j j' z => valAt' (Fu.ex i Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val) fr (fun j z => fr' j (h z)) _ d (fun j => (d' j).comp h.toContinuousLinearEquiv.differentiable.differentiableOn (U' j)) n …`. Use `cp' j j' (h z) (le_inf (U' j z h1) (U' j' z h2))` as an intermediate fact. Rewrite using `[hex] at this)` and apply the resulting hypothesis. Use the proof step `(fun j hj => by`. Establish `h0` using `U' j 0 hj`.

Rewrite `h0` using `[map_zero]`. Use `show fr' j (h 0) = _`. Rewrite using `[map_zero, o' j h0, o j hj])`. Use `q`. Use the proof step `(fun a j z hz => by show ‖fr' j (h z)‖ = _ * ‖fr' j (h (z + Pm a))‖`.

Rewrite using `[(p' (gam a) j (h z)).2 (U' j z hz), norm_mul, norm_mul, (p' (gam a) j (h z)).1, _root_.one_mul, norm_factor, hg, hHH, hHH, map_add])`. Set `pt : (Fin g → ℂ) → (Sp ℂ ⟶ Gx (S` to `ℂ) x') := fun z => fibLift x' _ (ov z)`. Establish `holp : IsHolTo Set.univ pt` using `isHolTo_fibLift x' _ ov hol`. Set `S : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ` to `fun j z => valAt' (pt z) ((PPx (S := ℂ) x').U (fun _ => j)) (sc.f (fun _ => j))`. Establish `hS : ∀ j z, U j z → S j z = θ z * fr j z` using `fun j z hz => hθ j z (pt z) (fibLift_fst _ _ _) (fibLift_snd _ _ _) hz`.

Take `⟨hc, hper⟩` from `density Pm hH U Uo Uc Up fr S θ d (fun j => (holp _ _).2.mono fun z hz => ⟨trivial, (chart_iff x' (pt z) j (fibLift_fst _ _ _)).2 hz⟩) n q (fun a j z => by simp only [S, pt, per]) hS`. Establish `hθθ : ∀ z, θ' (h z) = toC s * θ z` using `fun z => by`. Take `⟨j, hj⟩` from `Uc z`. Establish `h1` using `hθ' j (h z) (pt z) ((fibLift_fst _ _ _).trans (hex z).symm) (fibLift_snd _ _ _) (U' j z hj)`. Establish `h2` using `sv (toC s) (fun _ => j) (pt z) (fibLift_snd _ _ _)`.

Rewrite `h1` using `[hfr j z hj]`. Use `mul_right_cancel₀ (n j z hj) ?_` and prove the remaining obligations. Rewrite using `[← h1, _root_.mul_assoc, ← hS j z hj]`. Conclude with `(congrArg _ (hs _)).trans h2`. Rewrite using `[← hv, ← hv']`.

Use `mean_pos_and_scale Pm.range Pm'.range hP.2.2.1 hP'.2.2.1 hP.2.2.2.1 hP'.2.2.2.1 h (fun z => ⟨?_, ?_⟩) hF hF' _ hc (fun z => by positivity) ?_ ?_ (fun z => ?_)` and prove the remaining obligations. Introduce and unpack `⟨b, hb⟩`. Take `⟨a, rfl⟩` from `gam.surjective b`. Conclude with `⟨a, h.injective ((hg a).symm.trans hb)⟩`. Introduce and unpack `⟨a, rfl⟩`.

Conclude with `⟨gam a, hg a⟩`. Take `⟨J, r, hr, hne⟩` from `sg.1 gen`. Take `⟨j, rfl⟩ : ∃ j, J = fun _ => j` from `⟨J 0, funext fun k => by rw [Subsingleton.elim k 0]⟩`. Take `⟨z, hz⟩` from `Fu.ex_onto i Pm hP (Over.homMk (r ≫ gxFst (S := ℂ) x') ((over_of_snd x' r hr).trans hy))`. Establish `hz' : r ≫ gxFst (S` using `ℂ) x' = (Fu.ex i Pm z).left := by rw [hz]; rfl`.

Establish `hU` using `(chart_iff x' r j hz').1 (top_le_preimage_of_valAt'_ne_zero _ hne)`. Establish `h1` using `hθ j z r hz' hr hU`. Establish `h2 : θ z ≠ 0` using `left_ne_zero_of_mul (h1 ▸ hne)`. Conclude with `⟨z, by positivity⟩`. Introduce and unpack `_ ⟨a, rfl⟩ z`.

Conclude with `hper a z`. Use `show ‖θ' (h z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' (h z) (h z)).re) = _`. Rewrite using `[hθθ, hHH, norm_mul, mul_pow, _root_.mul_assoc]`.
-/
theorem theta_l2_positive_and_scaling : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i i' : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Pm' : (Fu.Di i').La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (s : CAt σ) (v v' : ℝ), IsPeriod (Fu.Di i) ty Pm → IsPeriod (Fu.Di i') ty Pm' → y.x = Fu.u i Pm → y'.x = Fu.u i' Pm' → FrChg G s y y' → IsThetaL2NormSquared Fu i Pm y v → IsThetaL2NormSquared Fu i' Pm' y' v' → 0 < v ∧ v' = ‖toC s‖ ^ 2 * v := by
  intro _ laws2 E _ _ _ H Dw l Xo c σ g ty Fu i i' Pm Pm' y y' G s v v' hP hP' hy hy' ⟨hx, _, hBC⟩
    ⟨Hm, χ, fr, θ, Fd, hH, _, him, d, n, cp, o, p, hθ, hF, hv⟩
    ⟨Hm', χ', fr', θ', Fd', hH', _, him', d', n', cp', o', p', hθ', hF', hv'⟩
  obtain ⟨x, _, _, _, _, _, sc, gen⟩ := y
  obtain ⟨x', _, _, _, _, _, sc', gen'⟩ := y'
  dsimp only at hx hBC hy hy' o o' hθ hθ'
  subst hx
  obtain ⟨h, gam, hex, hg, hEF, -⟩ := familyUnif_exp_unique E H Dw l Xo _ g ty Fu i i' Pm Pm' hP hP' (hy.symm.trans hy')
  obtain ⟨sv, sg, -⟩ := sec_values_complex_fibre laws2.secTwist E H Dw l Xo x' sc
  have hs := sec_eq_of_secBC (x := x') hBC
  have hHH : ∀ z w, hermForm Hm' (h z) (h w) = hermForm Hm z w := fun z w =>
    CM.HermWeil.hermForm_eq_of_im Hm' Hm h.toLinearMap h.toLinearMap LinearMap.id LinearMap.id hP.2.2.2.1 hP.2.2.2.1
      (by
        rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
        show (hermForm Hm' (h (Pm a)) (h (Pm b))).im = (hermForm Hm (Pm a) (Pm b)).im
        rw [← hg, ← hg, him', him, hEF]) z w
  have hol := ExpUniqFamily.isHolTo_ex Fu i Pm hP
  have per := ex_periodic Fu i Pm hP
  have ov : ∀ z, (Fu.ex i Pm z).left ≫ Xo.univ.t.G.hom = x' := fun z => (Over.w (Fu.ex i Pm z)).trans hy.symm
  let U : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → Prop := fun j z => ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j
  have Uo : ∀ j, IsOpen {z | U j z} := fun j => by
    simpa only [Set.mem_univ, true_and] using (hol (Xo.univ.t.PP.L.U j) 0).1
  have Uc : ∀ z, ∃ j, U j z := fun z => by
    have := Xo.univ.t.PP.isLB.cover.ge (Set.mem_univ ((Fu.ex i Pm z).left (default : PrimeSpectrum ℂ)))
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  have Up : ∀ j z a, U j z → U j (z + Pm a) := fun j z a hz => by
    simp only [U, per]
    exact hz
  have U' : ∀ j z, U j z → ⊤ ≤ (Fu.ex i' Pm' (h z)).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun j z hz => by
    rw [hex]
    exact hz
  have q : ∀ a j z, U j z → ‖fr j z‖ = Real.exp (Real.pi * (hermForm Hm z (Pm a)).re +
      Real.pi / 2 * (hermForm Hm (Pm a) (Pm a)).re) * ‖fr j (z + Pm a)‖ := fun a j z hz => by
    rw [(p a j z).2 hz, norm_mul, norm_mul, (p a j z).1, _root_.one_mul, norm_factor]
  have hfr : ∀ j z, U j z → fr' j (h z) = fr j z :=
    frames_eq Pm hP.2.2.1 hP.2.2.2.1 U Uo Uc Up
      (fun j j' z => valAt' (Fu.ex i Pm z).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val)
      fr (fun j z => fr' j (h z)) _ d
      (fun j => (d' j).comp h.toContinuousLinearEquiv.differentiable.differentiableOn (U' j)) n
      (fun j j' z h1 h2 => cp j j' z (le_inf h1 h2))
      (fun j j' z h1 h2 => by
        have := cp' j j' (h z) (le_inf (U' j z h1) (U' j' z h2))
        rwa [hex] at this)
      (fun j hj => by
        have h0 := U' j 0 hj
        rw [map_zero] at h0
        show fr' j (h 0) = _
        rw [map_zero, o' j h0, o j hj])
      q
      (fun a j z hz => by
        show ‖fr' j (h z)‖ = _ * ‖fr' j (h (z + Pm a))‖
        rw [(p' (gam a) j (h z)).2 (U' j z hz), norm_mul, norm_mul, (p' (gam a) j (h z)).1, _root_.one_mul,
          norm_factor, hg, hHH, hHH, map_add])
  let pt : (Fin g → ℂ) → (Sp ℂ ⟶ Gx (S := ℂ) x') := fun z => fibLift x' _ (ov z)
  have holp : IsHolTo Set.univ pt := isHolTo_fibLift x' _ ov hol
  let S : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ := fun j z =>
    valAt' (pt z) ((PPx (S := ℂ) x').U (fun _ => j)) (sc.f (fun _ => j))
  have hS : ∀ j z, U j z → S j z = θ z * fr j z := fun j z hz =>
    hθ j z (pt z) (fibLift_fst _ _ _) (fibLift_snd _ _ _) hz
  obtain ⟨hc, hper⟩ := density Pm hH U Uo Uc Up fr S θ d
    (fun j => (holp _ _).2.mono fun z hz => ⟨trivial, (chart_iff x' (pt z) j (fibLift_fst _ _ _)).2 hz⟩)
    n q (fun a j z => by simp only [S, pt, per]) hS
  have hθθ : ∀ z, θ' (h z) = toC s * θ z := fun z => by
    obtain ⟨j, hj⟩ := Uc z
    have h1 := hθ' j (h z) (pt z) ((fibLift_fst _ _ _).trans (hex z).symm) (fibLift_snd _ _ _) (U' j z hj)
    have h2 := sv (toC s) (fun _ => j) (pt z) (fibLift_snd _ _ _)
    rw [hfr j z hj] at h1
    refine mul_right_cancel₀ (n j z hj) ?_
    rw [← h1, _root_.mul_assoc, ← hS j z hj]
    exact (congrArg _ (hs _)).trans h2
  rw [← hv, ← hv']
  refine mean_pos_and_scale Pm.range Pm'.range hP.2.2.1 hP'.2.2.1 hP.2.2.2.1 hP'.2.2.2.1 h (fun z => ⟨?_, ?_⟩) hF hF' _ hc
    (fun z => by positivity) ?_ ?_ (fun z => ?_)
  · rintro ⟨b, hb⟩
    obtain ⟨a, rfl⟩ := gam.surjective b
    exact ⟨a, h.injective ((hg a).symm.trans hb)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨gam a, hg a⟩
  · obtain ⟨J, r, hr, hne⟩ := sg.1 gen
    obtain ⟨j, rfl⟩ : ∃ j, J = fun _ => j := ⟨J 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
    obtain ⟨z, hz⟩ := Fu.ex_onto i Pm hP (Over.homMk (r ≫ gxFst (S := ℂ) x') ((over_of_snd x' r hr).trans hy))
    have hz' : r ≫ gxFst (S := ℂ) x' = (Fu.ex i Pm z).left := by rw [hz]; rfl
    have hU := (chart_iff x' r j hz').1 (top_le_preimage_of_valAt'_ne_zero _ hne)
    have h1 := hθ j z r hz' hr hU
    have h2 : θ z ≠ 0 := left_ne_zero_of_mul (h1 ▸ hne)
    exact ⟨z, by positivity⟩
  · rintro _ ⟨a, rfl⟩ z
    exact hper a z
  · show ‖θ' (h z)‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm' (h z) (h z)).re) = _
    rw [hθθ, hHH, norm_mul, mul_pow, _root_.mul_assoc]

end GlobalTheory.GeneratorNorm
