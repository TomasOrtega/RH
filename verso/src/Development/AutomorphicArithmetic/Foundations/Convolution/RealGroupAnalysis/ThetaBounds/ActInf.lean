import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

/- English proof (translation)
The claim follows from `AddMonoidHomClass.continuous_of_bound (coord τ) 1 fun x => by simpa using UpperTheory.V.FieldIso.norm_coord_le τ x`.
-/
private theorem cont_coord (τ : E →+* ℂ) : Continuous (coord (E := E) τ) :=
  AddMonoidHomClass.continuous_of_bound (coord τ) 1 fun x => by
    simpa using UpperTheory.V.FieldIso.norm_coord_le τ x

/- English proof (translation)
The claim follows from `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp ((continuous_apply w).comp continuous_fst)`.
-/
private theorem cont_pInfE : Continuous (pInf E) := continuous_pi fun w =>
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
    ((continuous_apply w).comp continuous_fst)

/- English proof (translation)
The claim follows from `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp ((continuous_apply w).comp continuous_fst)`.
-/
private theorem cont_pInfF : Continuous (TR.pInf F) := continuous_pi fun w =>
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
    ((continuous_apply w).comp continuous_fst)

/- English proof (translation)
Establish `hv` using `IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)`. Rewrite using `[InfinitePlace.embedding_of_isReal_apply hv]`. Establish `hr : ComplexEmbedding.conjugate (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding = (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding` using `InfinitePlace.isReal_iff.1 hv`. Break down `InfinitePlace.embedding_mk_eq (τ.comp (algebraMap F E)) with h | h` into its components or cases. Conclude with `(congrArg (fun f : F →+* ℂ => f k) h).symm`.

Establish `h' : (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding = ComplexEmbedding.conjugate (τ.comp (algebraMap F E))` using `h`. Establish `h2 : τ.comp (algebraMap F E) = (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding`. Rewrite using `[← hr, h']`. Conclude with `(star_star _).symm`. Conclude with `congrArg (fun f : F →+* ℂ => f k) h2`.
-/
private theorem tau_real (τ : E →+* ℂ) (k : F) :
    τ (algebraMap F E k) =
      ((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)) k : ℝ) : ℂ) := by
  have hv := IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)
  rw [InfinitePlace.embedding_of_isReal_apply hv]
  have hr : ComplexEmbedding.conjugate (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding = (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding :=
    InfinitePlace.isReal_iff.1 hv
  rcases InfinitePlace.embedding_mk_eq (τ.comp (algebraMap F E)) with h | h
  · exact (congrArg (fun f : F →+* ℂ => f k) h).symm
  · have h' : (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding = ComplexEmbedding.conjugate (τ.comp (algebraMap F E)) := h
    have h2 : τ.comp (algebraMap F E) = (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding := by
      rw [← hr, h']
      exact (star_star _).symm
    exact congrArg (fun f : F →+* ℂ => f k) h2

/- English proof (translation)
Establish `hw` using `IsTotallyReal.isReal w`. Express the relevant statement in the definitionally equal form `(InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap F (InfiniteAdeleRing F) k w) = _`. Rewrite using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfiniteAdeleRing.algebraMap_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw]`. Both sides reduce to the same expression.
-/
private theorem pInfF_rat (k : F) (w : InfinitePlace F) :
    TR.pInf F (rt k) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) k := by
  have hw := IsTotallyReal.isReal w
  change (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap F (InfiniteAdeleRing F) k w) = _
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfiniteAdeleRing.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw]
  rfl

/- English proof (translation)
Establish `key : (fun x : InfiniteAdeleRing F => coord τ (pInf E (am E ((x, 0) : A F)))) = fun x => ((TR.pInf F ((x, 0) : A F) (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ)`. Establish `hc : Continuous fun x : InfiniteAdeleRing F => ((x, 0) : A F)` using `Continuous.prodMk_left 0`. Use `(InfiniteAdeleRing.denseRange_algebraMap (K := F)).equalizer ((cont_coord τ).comp (cont_pInfE.comp (continuous_am.comp hc))) (Complex.continuous_ofReal.comp ((continuous_apply _).comp (cont_pInfF.comp hc))) (funext fun k => ?_)` and prove the remaining obligations. Establish `e1 : pInf E (am E ((algebraMap F (InfiniteAdeleRing F) k, 0) : A F)) = pInf E (am E (rt k))` using `rfl`. Establish `e2 : TR.pInf F ((algebraMap F (InfiniteAdeleRing F) k, 0) : A F) = TR.pInf F (rt k)` using `rfl`.

Simplify using `only [Function.comp_apply]`. Rewrite using `[e1, e2, am_rt, pInfF_rat, ← tau_real]`. Conclude with `coord_algebraMap τ _`. Conclude with `congrFun key a.1`.
-/
private theorem r_am (τ : E →+* ℂ) (a : A F) :
    coord τ (pInf E (am E a)) = ((TR.pInf F a (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) := by
  have key : (fun x : InfiniteAdeleRing F => coord τ (pInf E (am E ((x, 0) : A F)))) =
      fun x => ((TR.pInf F ((x, 0) : A F) (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) := by
    have hc : Continuous fun x : InfiniteAdeleRing F => ((x, 0) : A F) := Continuous.prodMk_left 0
    refine (InfiniteAdeleRing.denseRange_algebraMap (K := F)).equalizer
      ((cont_coord τ).comp (cont_pInfE.comp (continuous_am.comp hc)))
      (Complex.continuous_ofReal.comp ((continuous_apply _).comp (cont_pInfF.comp hc))) (funext fun k => ?_)
    have e1 : pInf E (am E ((algebraMap F (InfiniteAdeleRing F) k, 0) : A F)) = pInf E (am E (rt k)) := rfl
    have e2 : TR.pInf F ((algebraMap F (InfiniteAdeleRing F) k, 0) : A F) = TR.pInf F (rt k) := rfl
    simp only [Function.comp_apply]
    rw [e1, e2, am_rt, pInfF_rat, ← tau_real]
    exact coord_algebraMap τ _
  exact congrFun key a.1

variable (D : Dat F E)

/- English proof (translation)
Establish `e : coord τ (pInf E (rt D.θ)) = τ D.θ` using `coord_algebraMap τ _`. Rewrite using `[D.mkE_def, map_add, map_add, map_mul, map_mul, r_am, r_am, e, mul_comm]`.
-/
private theorem r_mk (τ : E →+* ℂ) (u t : A F) :
    coord τ (pInf E (D.mkE u t)) = ((TR.pInf F u (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) +
      τ D.θ * ((TR.pInf F t (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) := by
  have e : coord τ (pInf E (rt D.θ)) = τ D.θ := coord_algebraMap τ _
  rw [D.mkE_def, map_add, map_add, map_mul, map_mul, r_am, r_am, e, mul_comm]

/- English proof (translation)
Establish `hv` using `IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)`. Establish `hc` using `D.neg (InfinitePlace.embedding_of_isReal hv)`. Establish `hz : τ D.θ ^ 2 = ((InfinitePlace.embedding_of_isReal hv D.δ : ℝ) : ℂ)`. Rewrite using `[← map_pow, D.sq, tau_real]`. Generalize the expression as in `τ D.θ = z at hz`.

Generalize the expression as in `InfinitePlace.embedding_of_isReal hv D.δ = c at hz hc`. Establish `h1` using `congrArg Complex.re hz`. Establish `h2` using `congrArg Complex.im hz`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2`. Establish `hre : z.re = 0`.

Assume the negation of the conclusion as `h`. Establish `h3 : z.im = 0`. Establish `: z.re * z.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left h`. Rewrite `h1` using `[h3]`.

Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hre]`. Simplify using the standard rewrite rules.
-/
private theorem conj_θ (τ : E →+* ℂ) : starRingEnd ℂ (τ D.θ) = -τ D.θ := by
  have hv := IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)
  have hc := D.neg (InfinitePlace.embedding_of_isReal hv)
  have hz : τ D.θ ^ 2 = ((InfinitePlace.embedding_of_isReal hv D.δ : ℝ) : ℂ) := by
    rw [← map_pow, D.sq, tau_real]
  generalize τ D.θ = z at hz
  generalize InfinitePlace.embedding_of_isReal hv D.δ = c at hz hc
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  have hre : z.re = 0 := by
    by_contra h
    have h3 : z.im = 0 := by
      have : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h
    rw [h3] at h1
    nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [hre]
  · simp

/- English proof (translation)
Take `⟨u, t, rfl⟩` from `D.exists_mkE z`. Rewrite using `[D.bar_mkE, r_mk, r_mk, map_add, map_mul, conj_θ, Complex.conj_ofReal, Complex.conj_ofReal, map_neg, Pi.neg_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem r_bar (τ : E →+* ℂ) (z : A E) :
    coord τ (pInf E (D.bar z)) = starRingEnd ℂ (coord τ (pInf E z)) := by
  obtain ⟨u, t, rfl⟩ := D.exists_mkE z
  rw [D.bar_mkE, r_mk, r_mk, map_add, map_mul, conj_θ, Complex.conj_ofReal, Complex.conj_ofReal, map_neg, Pi.neg_apply]
  push_cast
  ring

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Simplify using `[Dat.herm, Hm, r_mk, r_am, sub_eq_add_neg]`.
-/
private theorem map_herm (τ : E →+* ℂ) (v : V4 F) :
    (D.herm v).map ((coord τ).comp (pInf E)) =
      Hm (τ D.θ) (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) fun i => TR.pInf F (v i) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dat.herm, Hm, r_mk, r_am, sub_eq_add_neg]

/- English proof (translation)
Set `eF : A F` to `((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)`. Establish `heF : eF * eF = eF` using `Prod.ext (mul_zero _) (mul_one _)`. Use `set e : A E := am E eF with he`. Establish `he2 : e * e = e` using `by rw [he, ← map_mul, heF]`. Establish `hbar : D.bar e = e` using `D.bar_am eF`.

Establish `hfst : e.1 = 0` using `map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))`. Establish `hsnd : e.2 = 1` using `map_one (AdeleBaseChange.finiteAdeleMap F E)`. Establish `hM : e • (infGL E 2 y).val = e • (1 : Matrix (Fin 2) (Fin 2) (A E))` using `by ext1 i j`. Establish `h` using `congrArg (fun g : GL (Fin 2) (Af E) => g.val i j) (pFin_infGL y)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `e.1 * _ = e.1 * _`. Rewrite using `[hfst, zero_mul, zero_mul]`. Express the relevant statement in the definitionally equal form `e.2 * _ = e.2 * _`. Rewrite using `[hsnd, one_mul, one_mul]`. Conclude with `h.trans (by`.

Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = _`. Distinguish the cases in `hij : i = j`. Apply the tactic sequence `subst hij; simp <;> rfl`. Apply the tactic sequence `simp [Matrix.one_apply_ne hij] <;> rfl)`. Establish `hS : e • D.star2 (infGL E 2 y).val = e • (1 : Matrix (Fin 2) (Fin 2) (A E))`.

Establish `hs : ∀ X : Matrix (Fin 2) (Fin 2) (A E), D.star2 (e • X) = e • D.star2 X` using `fun X => by ext1 i j`. Simplify using `[Dat.conjTransposeGal_apply, hbar]`. Rewrite using `[← hs, hM, hs, Dat.conjTransposeGal_one]`. Establish `L : ∀ X Y : Matrix (Fin 2) (Fin 2) (A E), (e • X) * D.herm v * (e • Y) = e • (X * D.herm v * Y)` using `fun X Y => by`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he2]`.

Establish `main : D.act (infGL E 2 y) (eF • v) = eF • v` using `D.herm_injective (by`. Rewrite using `[D.herm_act, D.herm_smul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, he]`. Use `_ = (e • (infGL E 2 y).val) * D.herm v * (e • D.star2 (infGL E 2 y).val) := (L _ _).symm`.

Use `_ = (e • 1) * D.herm v * (e • 1) := by rw [hM, hS]`. Use `_ = am E eF • D.herm v := by rw [L]; simp [he])`. Rewrite `main` using `[D.act_smul]`. Use function extensionality and compare the values at `i`. Establish `h` using `congrArg (fun x : V4 F => (x i).2) main`.

Conclude with `(one_mul _).symm.trans (h.trans (one_mul _))`.
-/
private theorem fin_part (y : GL (Fin 2) (Cinf E)) (v : V4 F) :
    finPartPi (D.act (infGL E 2 y) v) = finPartPi v := by
  let eF : A F := ((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have heF : eF * eF = eF := Prod.ext (mul_zero _) (mul_one _)
  set e : A E := am E eF with he
  have he2 : e * e = e := by rw [he, ← map_mul, heF]
  have hbar : D.bar e = e := D.bar_am eF
  have hfst : e.1 = 0 := map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))
  have hsnd : e.2 = 1 := map_one (AdeleBaseChange.finiteAdeleMap F E)
  have hM : e • (infGL E 2 y).val = e • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
    ext1 i j
    have h := congrArg (fun g : GL (Fin 2) (Af E) => g.val i j) (pFin_infGL y)
    refine Prod.ext ?_ ?_
    · change e.1 * _ = e.1 * _
      rw [hfst, zero_mul, zero_mul]
    · change e.2 * _ = e.2 * _
      rw [hsnd, one_mul, one_mul]
      exact h.trans (by
        change (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = _
        by_cases hij : i = j
        · subst hij; simp <;> rfl
        · simp [Matrix.one_apply_ne hij] <;> rfl)
  have hS : e • D.star2 (infGL E 2 y).val = e • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
    have hs : ∀ X : Matrix (Fin 2) (Fin 2) (A E), D.star2 (e • X) = e • D.star2 X := fun X => by
      ext1 i j
      simp [Dat.conjTransposeGal_apply, hbar]
    rw [← hs, hM, hs, Dat.conjTransposeGal_one]
  have L : ∀ X Y : Matrix (Fin 2) (Fin 2) (A E), (e • X) * D.herm v * (e • Y) = e • (X * D.herm v * Y) := fun X Y => by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he2]
  have main : D.act (infGL E 2 y) (eF • v) = eF • v := D.herm_injective (by
    rw [D.herm_act, D.herm_smul]
    calc (infGL E 2 y).val * (am E eF • D.herm v) * D.star2 (infGL E 2 y).val
        = e • ((infGL E 2 y).val * D.herm v * D.star2 (infGL E 2 y).val) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, he]
      _ = (e • (infGL E 2 y).val) * D.herm v * (e • D.star2 (infGL E 2 y).val) := (L _ _).symm
      _ = (e • 1) * D.herm v * (e • 1) := by rw [hM, hS]
      _ = am E eF • D.herm v := by rw [L]; simp [he])
  rw [D.act_smul] at main
  funext i
  have h := congrArg (fun x : V4 F => (x i).2) main
  exact (one_mul _).symm.trans (h.trans (one_mul _))

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ D y v`. Use `⟨fin_part D y v, fun τ => ?_⟩` and prove the remaining obligations. Establish `hy : ((infGL E 2 y).val).map ((coord τ).comp (pInf E)) = y.val.map (coord τ)` using `by ext1 i j`. Conclude with `congrArg (coord τ) (congrArg (fun g : GL (Fin 2) (Cinf E) => g.val i j) (pInf_infGL y))`. Establish `hs : (D.star2 (infGL E 2 y).val).map ((coord τ).comp (pInf E)) = (y.val.map (coord τ))ᴴ`.

Rewrite using `[← hy]`. Use `ext1 i j`. Conclude with `r_bar D τ _`. Establish `h` using `congrArg (fun X => X.map ((coord τ).comp (pInf E))) (D.herm_act (infGL E 2 y) v)`. Simplify using `only [Matrix.map_mul, map_herm, hy, hs] at h`.

Conclude with `h`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.actInf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), ActInf D := by
  intro F E _ _ _ _ _ _ _ D y v
  refine ⟨fin_part D y v, fun τ => ?_⟩
  have hy : ((infGL E 2 y).val).map ((coord τ).comp (pInf E)) = y.val.map (coord τ) := by
    ext1 i j
    exact congrArg (coord τ) (congrArg (fun g : GL (Fin 2) (Cinf E) => g.val i j) (pInf_infGL y))
  have hs : (D.star2 (infGL E 2 y).val).map ((coord τ).comp (pInf E)) = (y.val.map (coord τ))ᴴ := by
    rw [← hy]
    ext1 i j
    exact r_bar D τ _
  have h := congrArg (fun X => X.map ((coord τ).comp (pInf E))) (D.herm_act (infGL E 2 y) v)
  simp only [Matrix.map_mul, map_herm, hy, hs] at h
  exact h
