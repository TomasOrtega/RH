import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

/- English proof (translation)
Use function extensionality and compare the values at `w`. Set `f : ℝ →+* w.Completion` to `(Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp ((GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E)).comp ((TR.infEq ℚ).toRingHom.comp (Pi.constRingHom (InfinitePlace ℚ) ℝ)))`. Set `g : ℝ →+* w.Completion` to `(Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp ((infEq E).toRingHom.comp ((Pi.constRingHom (InfinitePlace E) ℂ).comp Complex.ofRealHom))`. Establish `hf : Continuous f` using `(continuous_apply w).comp (GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap.comp ((TR.continuous_infEq ℚ).comp (continuous_pi fun _ => continuous_id)))`. Establish `hg : Continuous g` using `(continuous_apply w).comp ((continuous_infEq E).comp (continuous_pi fun _ => Complex.continuous_ofReal))`.

Establish `h` using `Rat.denseRange_cast (𝕜 := ℝ) |>.equalizer hf hg (funext fun q => by simp)`. Conclude with `congrFun h c`.
-/
private theorem inf_const (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (c : ℝ) :
    GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E) (TR.infEq ℚ fun _ => c) =
      infEq E fun _ => (c : ℂ) := by
  funext w
  let f : ℝ →+* w.Completion := (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
    ((GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E)).comp
      ((TR.infEq ℚ).toRingHom.comp (Pi.constRingHom (InfinitePlace ℚ) ℝ)))
  let g : ℝ →+* w.Completion := (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w).comp
    ((infEq E).toRingHom.comp ((Pi.constRingHom (InfinitePlace E) ℂ).comp Complex.ofRealHom))
  have hf : Continuous f := (continuous_apply w).comp
    (GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap.comp
      ((TR.continuous_infEq ℚ).comp (continuous_pi fun _ => continuous_id)))
  have hg : Continuous g := (continuous_apply w).comp
    ((continuous_infEq E).comp (continuous_pi fun _ => Complex.continuous_ofReal))
  have h := Rat.denseRange_cast (𝕜 := ℝ) |>.equalizer hf hg (funext fun q => by simp)
  exact congrFun h c

/- English proof (translation)
Use function extensionality and compare the values at `v`. Rewrite using `[Subsingleton.elim v Rat.infinitePlace]`. Both sides reduce to the same expression.
-/
private theorem re_const (x : A ℚ) : TR.pInf ℚ x = fun _ => re x := by
  funext v
  rw [Subsingleton.elim v Rat.infinitePlace]
  rfl

/- English proof (translation)
Establish `h : x.1 = TR.infEq ℚ fun _ => re x`. Rewrite using `[← re_const]`. Conclude with `((TR.infEq ℚ).apply_symm_apply x.1).symm`. Express the relevant statement in the definitionally equal form `(infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap x.1) = _`. Rewrite using `[h, inf_const, RingEquiv.symm_apply_apply]`.
-/
private theorem pInf_adeleMap (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (x : A ℚ) :
    pInf E (AdeleBaseChange.adeleMap ℚ E x) = fun _ => (re x : ℂ) := by
  have h : x.1 = TR.infEq ℚ fun _ => re x := by
    rw [← re_const]
    exact ((TR.infEq ℚ).apply_symm_apply x.1).symm
  change (infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap x.1) = _
  rw [h, inf_const, RingEquiv.symm_apply_apply]

/- English proof (translation)
The claim follows from `(infEq E).symm_apply_apply x`.
-/
private theorem pInf_s {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (x : Cinf E) :
    pInf E (GlobalTheory.CuspRep.sInf E x) = x := (infEq E).symm_apply_apply x

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem pFin_s {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (x : Cinf E) :
    pFin E (GlobalTheory.CuspRep.sInf E x) = 0 := rfl

/- English proof (translation)
The claim follows from `congrFun ((TR.infEq ℚ).symm_apply_apply fun _ => c) Rat.infinitePlace`.
-/
private theorem re_s (c : ℝ) : re (TR.sInf ℚ fun _ => c) = c :=
  congrFun ((TR.infEq ℚ).symm_apply_apply fun _ => c) Rat.infinitePlace

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[hh]`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `f (g.val i j) = _`. Rewrite using `[hg]`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem map_n {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : Matrix.GeneralLinearGroup (Fin 2) R) (z : R)
    (hg : g.val = !![1, z; 0, 1]) (h : Matrix.GeneralLinearGroup (Fin 2) S) (hh : h.val = !![1, f z; 0, 1]) :
    Matrix.GeneralLinearGroup.map f g = h := by
  refine Units.ext ?_
  rw [hh]
  ext i j
  change f (g.val i j) = _
  rw [hg]
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Use `ga_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, pInf_infGL]`. Establish `h : Matrix.GeneralLinearGroup.map (pInf E) (gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D)))) = nC (t • thInf D)` using `map_n _ _ _ rfl _ (by rw [pInf_s]; rfl)`. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `kInf k * cv D k t = nC (t • thInf D) * kInf k`.

Simplify using `only [cv, mul_assoc, mul_inv_cancel_left]`. Rewrite using `[map_mul, map_mul, pFin_infGL, mul_one]`. Establish `h : Matrix.GeneralLinearGroup.map (pFin E) (gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D)))) = 1`. Use `map_n _ _ _ rfl _ ?_` and prove the remaining obligations. Rewrite using `[pFin_s]`.

Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`. Rewrite using `[h, one_mul]`.
-/
private theorem step1 {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (k : GL (Fin 2) (A E)) (t : ℝ) :
    k * infGL E 2 (cv D k t) = gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D))) * k := by
  refine ga_ext ?_ ?_
  · rw [map_mul, map_mul, pInf_infGL]
    have h : Matrix.GeneralLinearGroup.map (pInf E) (gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D)))) = nC (t • thInf D) :=
      map_n _ _ _ rfl _ (by rw [pInf_s]; rfl)
    rw [h]
    change kInf k * cv D k t = nC (t • thInf D) * kInf k
    simp only [cv, mul_assoc, mul_inv_cancel_left]
  · rw [map_mul, map_mul, pFin_infGL, mul_one]
    have h : Matrix.GeneralLinearGroup.map (pFin E) (gl (nU (GlobalTheory.CuspRep.sInf E (t • thInf D)))) = 1 := by
      refine map_n _ _ _ rfl _ ?_
      rw [pFin_s]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [h, one_mul]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `AdeleBaseChange.adeleMap ℚ E ((aE y).val i j) = _`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [aE]`.
-/
private theorem em_aE {E : Type} [Field E] [NumberField E] (y : (A ℚ)ˣ) :
    em E (aE y) = aE (Units.map (AdeleBaseChange.adeleMap ℚ E : A ℚ →* A E) y) := by
  refine Units.ext ?_
  ext i j
  change AdeleBaseChange.adeleMap ℚ E ((aE y).val i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE]

/- English proof (translation)
Use `ad_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Dat.mkE, map_zero, zero_add, map_mul, map_mul, pInf_s, pInf_adeleMap, pInf_adeleMap, re_s]`. Express the relevant statement in the definitionally equal form `_ = _ * thInf D`. Use function extensionality and compare the values at `w`. Simplify using `[Pi.mul_apply, Pi.smul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Dat.mkE, map_zero, zero_add, map_mul, map_mul, pFin_s, mul_zero]`. Establish `: pFin E (AdeleBaseChange.adeleMap ℚ E (TR.sInf ℚ fun _ => t * re (y : A ℚ))) = 0` using `map_zero (AdeleBaseChange.finiteAdeleMap ℚ E)`. Rewrite using `[this, zero_mul]`.
-/
private theorem step3 {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (t : ℝ) :
    AdeleBaseChange.adeleMap ℚ E (y : A ℚ) * GlobalTheory.CuspRep.sInf E (t • thInf D) =
      D.mkE 0 (TR.sInf ℚ fun _ => t * re (y : A ℚ)) := by
  refine ad_ext ?_ ?_
  · rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, pInf_s, pInf_adeleMap, pInf_adeleMap, re_s]
    change _ = _ * thInf D
    funext w
    simp [Pi.mul_apply, Pi.smul_apply]
    ring
  · rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, pFin_s, mul_zero]
    have : pFin E (AdeleBaseChange.adeleMap ℚ E (TR.sInf ℚ fun _ => t * re (y : A ℚ))) = 0 :=
      map_zero (AdeleBaseChange.finiteAdeleMap ℚ E)
    rw [this, zero_mul]

/- English proof (translation)
Introduce `E _ _ _ D y k t`. Establish `h3` using `step3 D y t`. Establish `hn : nE D ![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] = gl (nU (AdeleBaseChange.adeleMap ℚ E (y : A ℚ) * GlobalTheory.CuspRep.sInf E (t • thInf D)))`. Rewrite using `[h3]`. Both sides reduce to the same expression.

Rewrite using `[mul_assoc, step1, hn, ← mul_assoc, ← mul_assoc, em_aE, Pp.a_n]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.diagonal_mul_archimedeanCurve_eq_unipotent_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (y : (A ℚ)ˣ) (k : GL (Fin 2) (A E)) (t : ℝ),
        em E (aE y) * k * infGL E 2 (cv D k t) = nE D ![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] * (em E (aE y) * k) := by
  intro E _ _ _ D y k t
  have h3 := step3 D y t
  have hn : nE D ![0, TR.sInf ℚ fun _ => t * re (y : A ℚ)] =
      gl (nU (AdeleBaseChange.adeleMap ℚ E (y : A ℚ) * GlobalTheory.CuspRep.sInf E (t • thInf D))) := by
    rw [h3]
    rfl
  rw [mul_assoc, step1, hn, ← mul_assoc, ← mul_assoc, em_aE, Pp.a_n]
  rfl
