import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelNegTAndQdet

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open scoped ContDiff

namespace GlobalTheory.ThetaPull

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {a : ℕ}

/- English proof (translation)
Establish `h : ∀ (k : Fin a) (f : Fin a → R), ∑ l, GlobalTheory.Tw.Phi a R k l * f l = (-1) ^ (k : ℕ) * f k.rev` using `fun k f => by`. Rewrite using `[Finset.sum_eq_single k.rev]`. Rewrite using `[GlobalTheory.Tw.Phi, Matrix.of_apply, if_pos (by rw [Fin.val_rev]; omega)]`. Introduce `l _ hl`. Rewrite using `[GlobalTheory.Tw.Phi, Matrix.of_apply, if_neg (fun h => hl (Fin.ext (by rw [Fin.val_rev]; omega))), zero_mul]`.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.transpose_apply, mul_comm _ (GlobalTheory.Tw.Phi a R j _)]`. Rewrite using `[h, Matrix.mul_apply, h, pow_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi_mul_apply (M : Matrix (Fin a) (Fin a) R) (i j : Fin a) :
    (GlobalTheory.Tw.Phi a R * M * (GlobalTheory.Tw.Phi a R)ᵀ) i j = (-1) ^ ((i : ℕ) + j) * M i.rev j.rev := by
  have h : ∀ (k : Fin a) (f : Fin a → R), ∑ l, GlobalTheory.Tw.Phi a R k l * f l = (-1) ^ (k : ℕ) * f k.rev := fun k f => by
    rw [Finset.sum_eq_single k.rev]
    · rw [GlobalTheory.Tw.Phi, Matrix.of_apply, if_pos (by rw [Fin.val_rev]; omega)]
    · intro l _ hl
      rw [GlobalTheory.Tw.Phi, Matrix.of_apply, if_neg (fun h => hl (Fin.ext (by rw [Fin.val_rev]; omega))), zero_mul]
    · simp
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, mul_comm _ (GlobalTheory.Tw.Phi a R j _)]
  rw [h, Matrix.mul_apply, h, pow_add]
  ring

/- English proof (translation)
The claim follows from `phi_mul_apply _ i j`.
-/
theorem thetaGL_apply (c : R →+* R) (g : GL (Fin a) R) (i j : Fin a) :
    (thetaGL a c g).val i j = (-1) ^ ((i : ℕ) + j) * c ((g⁻¹).val j.rev i.rev) :=
  phi_mul_apply _ i j

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[thetaGL_apply, ← map_inv]`. Express the relevant statement in the definitionally equal form `p ((thetaGL a c g).val i j) = _ * c' (p _)`. Rewrite using `[thetaGL_apply, map_mul, h]`. Simplify using the standard rewrite rules.
-/
theorem map_thetaGL (p : R →+* S) (c : R →+* R) (c' : S →+* S) (h : ∀ x, p (c x) = c' (p x)) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (thetaGL a c g) = thetaGL a c' (GeneralLinearGroup.map p g) := by
  ext i j
  rw [thetaGL_apply, ← map_inv]
  change p ((thetaGL a c g).val i j) = _ * c' (p _)
  rw [thetaGL_apply, map_mul, h]
  simp

/- English proof (translation)
Rewrite using `[← pow_add]`. Conclude with `Even.neg_one_pow ⟨a - 1, by rw [Fin.val_rev, Fin.val_rev]; omega⟩`.
-/
theorem sign_rev (i j : Fin a) : (-1 : R) ^ ((i : ℕ) + j) * (-1) ^ ((j.rev : ℕ) + i.rev) = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨a - 1, by rw [Fin.val_rev, Fin.val_rev]; omega⟩

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[thetaGL_apply, ← map_inv, thetaGL_apply, inv_inv, map_mul, h, Fin.rev_rev, Fin.rev_rev, map_pow, map_neg, map_one, ← mul_assoc, sign_rev, one_mul]`.
-/
theorem thetaGL_thetaGL (c : R →+* R) (h : ∀ x, c (c x) = x) (g : GL (Fin a) R) : thetaGL a c (thetaGL a c g) = g := by
  ext i j
  rw [thetaGL_apply, ← map_inv, thetaGL_apply, inv_inv, map_mul, h, Fin.rev_rev, Fin.rev_rev, map_pow, map_neg, map_one,
    ← mul_assoc, sign_rev, one_mul]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩` and prove the remaining obligations. Simplify using `only [Function.comp_apply, thetaGL_apply]`. Conclude with `continuous_const.mul (h.comp (Units.continuous_coe_inv.matrix_elem _ _))`. Simplify using `only [← map_inv, thetaGL_apply, inv_inv]`. Conclude with `continuous_const.mul (h.comp (Units.continuous_val.matrix_elem _ _))`.
-/
theorem continuous_thetaGL [TopologicalSpace R] [IsTopologicalRing R] (c : R →+* R) (h : Continuous c) :
    Continuous (thetaGL a c) := by
  refine Units.continuous_iff.2 ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · simp only [Function.comp_apply, thetaGL_apply]
    exact continuous_const.mul (h.comp (Units.continuous_coe_inv.matrix_elem _ _))
  · simp only [← map_inv, thetaGL_apply, inv_inv]
    exact continuous_const.mul (h.comp (Units.continuous_val.matrix_elem _ _))

end Ring

section Inverse

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def invL (x : Lie E a) : Lie E a := toL (Matrix.of x)⁻¹

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

/- English proof (translation)
Set `e : Lie E a ≃L[ℝ] Matrix (Fin a) (Fin a) (Cinf E)` to `(Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv`. Establish `: CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E))` using `FiniteDimensional.complete ℝ _`. Establish `h : (invL : Lie E a → Lie E a) = e.symm ∘ Ring.inverse ∘ e` using `funext fun x => Matrix.nonsing_inv_eq_ringInverse (Matrix.of x)`. Rewrite using `[h]`. Use `⟨fun x hx => e.symm.contDiff.contDiffAt.comp _ (ContDiffAt.comp _ ?_ e.contDiff.contDiffAt), ?_⟩` and prove the remaining obligations.

Take `⟨u, hu⟩` from `hx`. Use `contDiffAt_ringInverse ℝ (n := ∞) u` as an intermediate fact. Rewrite `this` using `[hu]`. Conclude with `this`. Establish `h1` using `hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)`.

Establish `h2` using `e.symm.hasFDerivAt.comp (oneL E a) (HasFDerivAt.comp (oneL E a) (f := e) h1 e.hasFDerivAt)`. Use `h2.congr_fderiv ?_` and prove the remaining obligations. Use `ext1 x`. Simplify using `only [inv_one, Units.val_one, ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, one_mul, mul_one, map_neg, ContinuousLinearMap.id_apply]`. Both sides reduce to the same expression.
-/
theorem invL_smooth : (∀ x ∈ invSet E a, ContDiffAt ℝ ∞ invL x) ∧
    HasFDerivAt (invL : Lie E a → Lie E a) (-ContinuousLinearMap.id ℝ _) (oneL E a) := by
  let e : Lie E a ≃L[ℝ] Matrix (Fin a) (Fin a) (Cinf E) := (Matrix.ofLinearEquiv ℝ).toContinuousLinearEquiv
  have : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  have h : (invL : Lie E a → Lie E a) = e.symm ∘ Ring.inverse ∘ e := funext fun x =>
    Matrix.nonsing_inv_eq_ringInverse (Matrix.of x)
  rw [h]
  refine ⟨fun x hx => e.symm.contDiff.contDiffAt.comp _ (ContDiffAt.comp _ ?_ e.contDiff.contDiffAt), ?_⟩
  · obtain ⟨u, hu⟩ := hx
    have := contDiffAt_ringInverse ℝ (n := ∞) u
    rw [hu] at this
    exact this
  · have h1 := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)
    have h2 := e.symm.hasFDerivAt.comp (oneL E a) (HasFDerivAt.comp (oneL E a) (f := e) h1 e.hasFDerivAt)
    refine h2.congr_fderiv ?_
    ext1 x
    simp only [inv_one, Units.val_one, ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
      ContinuousLinearMap.mulLeftRight_apply, one_mul, mul_one, map_neg, ContinuousLinearMap.id_apply]
    rfl

def adjL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (GlobalTheory.Tw.Phi a (Cinf E) * (Matrix.of X)ᴴ * (GlobalTheory.Tw.Phi a (Cinf E))ᵀ)
      map_add' := fun X Y => by
        rw [show Matrix.of (X + Y) = Matrix.of X + Matrix.of Y from rfl, Matrix.conjTranspose_add, mul_add, add_mul]; rfl
      map_smul' := fun t X => by
        rw [show Matrix.of (t • X) = t • Matrix.of X from rfl, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul,
          Matrix.smul_mul]; rfl }

/- English proof (translation)
Rewrite using `[thetaGL_val]`. Both sides reduce to the same expression.
-/
theorem toL_thetaGL (y : GL (Fin a) (Cinf E)) :
    toL (thetaGL a (starRingEnd (Cinf E)) y).val = adjL (invL (toL y.val)) := by
  rw [thetaGL_val]; rfl

end Inverse

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

abbrev cFin (E : Type) [Field E] [NumberField E] [IsCMField E] : Af E →+* Af E :=
  conjFin (IsCMField.complexConj E).toRingEquiv

/- English proof (translation)
The claim follows from `(infEq E).symm_apply_apply _`.
-/
theorem pInf_conjAd (x : Ad E) : pInf E (conjAd E x) = starRingEnd (Cinf E) (pInf E x) := (infEq E).symm_apply_apply _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pFin_conjAd (x : Ad E) : pFin E (conjAd E x) = cFin E (pFin E x) := rfl

/- English proof (translation)
The claim follows from `(eq_conjSrc fun x => by rw [← conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v ((IsCMField.complexConj E).toRingEquiv x)] exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm`.
-/
theorem conjSrc_conjSrc (v : HeightOneSpectrum (𝓞 E)) :
    conjSrc (IsCMField.complexConj E).toRingEquiv (conjSrc (IsCMField.complexConj E).toRingEquiv v) = v :=
  (eq_conjSrc fun x => by
    rw [← conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v ((IsCMField.complexConj E).toRingEquiv x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm

/- English proof (translation)
Establish `key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E), Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x`. Introduce and unpack `_ v rfl f hf h`. Conclude with `congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _`. Use `FiniteAdeleRing.ext _ fun v => key v _ (conjSrc_conjSrc v) (conjLoc _ v ∘ conjLoc _ _) ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_` and prove the remaining obligations. Rewrite using `[Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]`.

Conclude with `congrArg _ (IsCMField.complexConj_apply_apply E k)`.
-/
theorem cFin_cFin (x : Af E) : cFin E (cFin E x) = x := by
  have key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E),
      Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x := by
    rintro _ v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _
  refine FiniteAdeleRing.ext _ fun v => key v _ (conjSrc_conjSrc v) (conjLoc _ v ∘ conjLoc _ _)
    ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_
  rw [Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

/- English proof (translation)
The claim follows from `ad_ext (by rw [pInf_conjAd, pInf_conjAd, starRingEnd_self_apply]) (cFin_cFin _)`.
-/
theorem conjAd_conjAd (x : Ad E) : conjAd E (conjAd E x) = x :=
  ad_ext (by rw [pInf_conjAd, pInf_conjAd, starRingEnd_self_apply]) (cFin_cFin _)

/- English proof (translation)
Establish `h : Continuous (infEq E).symm` using `continuous_pi fun w => (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)`. Conclude with `((continuous_infEq E).comp (continuous_star.comp h)).prodMap (continuous_conjFin _)`.
-/
theorem continuous_conjAd : Continuous (conjAd E) := by
  have h : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact ((continuous_infEq E).comp (continuous_star.comp h)).prodMap (continuous_conjFin _)

variable (E a) in

def thetaA : GA E a →* GA E a := thetaGL a (conjAd E)

/- English proof (translation)
The claim follows from `thetaGL_thetaGL _ conjAd_conjAd g`.
-/
theorem thetaA_thetaA (g : GA E a) : thetaA E a (thetaA E a g) = g := thetaGL_thetaGL _ conjAd_conjAd g

/- English proof (translation)
The claim follows from `ga_ext (by rw [thetaA, map_thetaGL _ _ _ pInf_conjAd, pInf_infGL, pInf_infGL]) (by rw [thetaA, map_thetaGL _ _ _ pFin_conjAd, pFin_infGL, pFin_infGL, map_one])`.
-/
theorem thetaA_infGL (y : GL (Fin a) (Cinf E)) :
    thetaA E a (infGL E a y) = infGL E a (thetaGL a (starRingEnd (Cinf E)) y) :=
  ga_ext (by rw [thetaA, map_thetaGL _ _ _ pInf_conjAd, pInf_infGL, pInf_infGL])
    (by rw [thetaA, map_thetaGL _ _ _ pFin_conjAd, pFin_infGL, pFin_infGL, map_one])

/- English proof (translation)
The claim follows from `ga_ext (by rw [thetaA, map_thetaGL _ _ _ pInf_conjAd, pInf_finGL, pInf_finGL, map_one]) (by rw [thetaA, map_thetaGL _ _ _ pFin_conjAd, pFin_finGL, pFin_finGL])`.
-/
theorem thetaA_finGL (k : GL (Fin a) (Af E)) : thetaA E a (finGL E a k) = finGL E a (thetaGL a (cFin E) k) :=
  ga_ext (by rw [thetaA, map_thetaGL _ _ _ pInf_conjAd, pInf_finGL, pInf_finGL, map_one])
    (by rw [thetaA, map_thetaGL _ _ _ pFin_conjAd, pFin_finGL, pFin_finGL])

/- English proof (translation)
The claim follows from `(map_thetaGL _ _ _ (fun x => (conjAd_algebraMap x).symm) γ).symm`.
-/
theorem thetaA_ratGL (γ : GL (Fin a) E) :
    thetaA E a (ratGL E a γ) = ratGL E a (thetaGL a (IsCMField.complexConj E).toRingEquiv.toRingHom γ) :=
  (map_thetaGL _ _ _ (fun x => (conjAd_algebraMap x).symm) γ).symm

/- English proof (translation)
Rewrite using `[splitCentre, thetaA_infGL, splitCentre]`. Use `congr 1`. Use extensionality with `i j : 2`. Rewrite using `[thetaGL_apply]`. Express the relevant statement in the definitionally equal form `_ * starRingEnd (Cinf E) (Matrix.diagonal _ _ _) = Matrix.diagonal _ _ _`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Even.neg_one_pow ⟨_, rfl⟩, one_mul]`. Use function extensionality and compare the values at `w`. Express the relevant statement in the definitionally equal form `starRingEnd ℂ (Complex.exp (-(t : ℂ))) = Complex.exp ((-t : ℝ) : ℂ)`.

Rewrite using `[← Complex.exp_conj]`. Simplify using the standard rewrite rules. Rewrite using `[Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), map_zero, mul_zero]`.
-/
theorem thetaA_splitCentre (t : ℝ) : thetaA E a (splitCentre E a t) = splitCentre E a (-t) := by
  rw [splitCentre, thetaA_infGL, splitCentre]
  congr 1
  ext i j : 2
  rw [thetaGL_apply]
  change _ * starRingEnd (Cinf E) (Matrix.diagonal _ _ _) = Matrix.diagonal _ _ _
  by_cases h : i = j
  · subst h
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Even.neg_one_pow ⟨_, rfl⟩, one_mul]
    funext w
    change starRingEnd ℂ (Complex.exp (-(t : ℂ))) = Complex.exp ((-t : ℝ) : ℂ)
    rw [← Complex.exp_conj]
    simp
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (fun e => h (Fin.rev_injective e).symm), map_zero, mul_zero]

/- English proof (translation)
Take `⟨u, hu⟩` from `id hx`. Take `rfl : x = toL u.val` from `hu.symm`. Rewrite using `[← toL_thetaGL, chart_val, chart_val, map_mul, thetaA_infGL]`. Conclude with `⟨rfl, val_mem_invSet _⟩`.
-/
theorem chart_theta (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => φ (thetaA E a g)) g x = chart φ (thetaA E a g) (adjL (invL x)) ∧ adjL (invL x) ∈ invSet E a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_thetaGL, chart_val, chart_val, map_mul, thetaA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

/- English proof (translation)
Introduce `g` and use `((hφ (thetaA E a g)).comp (fun x hx => (adjL.contDiff.contDiffAt.comp x (invL_smooth.1 x hx)).contDiffWithinAt) fun _ hx => (chart_theta φ g hx).2).congr fun _ hx => (chart_theta φ g hx).1`.
-/
theorem theta_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : (fun g => φ (thetaA E a g)) ∈ Sm E a := fun g =>
  ((hφ (thetaA E a g)).comp (fun x hx => (adjL.contDiff.contDiffAt.comp x (invL_smooth.1 x hx)).contDiffWithinAt)
    fun _ hx => (chart_theta φ g hx).2).congr fun _ hx => (chart_theta φ g hx).1

variable (E a) in

def pull : Sm E a ≃ₗ[ℂ] Sm E a where
  toFun φ := ⟨fun g => φ.1 (thetaA E a g), theta_mem_Sm φ.2⟩
  invFun φ := ⟨fun g => φ.1 (thetaA E a g), theta_mem_Sm φ.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (thetaA_thetaA g)
  right_inv φ := Subtype.ext <| funext fun g => congrArg φ.1 (thetaA_thetaA g)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem pull_apply (φ : Sm E a) (g : GA E a) : (pull E a φ).1 g = φ.1 (thetaA E a g) := rfl

/- English proof (translation)
The claim follows from `(pull E a).left_inv φ`.
-/
@[simp] theorem pull_pull (φ : Sm E a) : pull E a (pull E a φ) = φ := (pull E a).left_inv φ

/- English proof (translation)
The claim follows from `Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (thetaA E a) g h)`.
-/
theorem rt_pull (h : GA E a) (φ : Sm E a) : rt E a h (pull E a φ) = pull E a (rt E a (thetaA E a h) φ) :=
  Subtype.ext <| funext fun g => congrArg φ.1 (map_mul (thetaA E a) g h)

/- English proof (translation)
Use `Subtype.ext <| funext fun g => ?_` and prove the remaining obligations. Establish `e : chart (pull E a φ).1 g =ᶠ[𝓝 (oneL E a)] chart φ.1 (thetaA E a g) ∘ adjL ∘ invL` using `Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_theta φ.1 g hx).1`. Establish `h1 : (adjL ∘ invL) (oneL E a) = oneL E a` using `(toL_thetaGL 1).symm.trans (by rw [map_one]; rfl)`. Establish `h2` using `HasFDerivAt.comp (oneL E a) (f := adjL ∘ invL) (by rw [h1]; exact (differentiableAt_chart φ.2 (thetaA E a g)).hasFDerivAt) (adjL.hasFDerivAt.comp (oneL E a) invL_smooth.2)`. Express the relevant statement in the definitionally equal form `fderiv ℝ _ _ X = fderiv ℝ _ _ _`.

Rewrite using `[e.fderiv_eq, h2.fderiv]`. Simplify using the standard rewrite rules.
-/
theorem lie_pull (X : Lie E a) (φ : Sm E a) : lie E a X (pull E a φ) = pull E a (lie E a (-adjL X) φ) := by
  refine Subtype.ext <| funext fun g => ?_
  have e : chart (pull E a φ).1 g =ᶠ[𝓝 (oneL E a)] chart φ.1 (thetaA E a g) ∘ adjL ∘ invL :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => (chart_theta φ.1 g hx).1
  have h1 : (adjL ∘ invL) (oneL E a) = oneL E a :=
    (toL_thetaGL 1).symm.trans (by rw [map_one]; rfl)
  have h2 := HasFDerivAt.comp (oneL E a) (f := adjL ∘ invL)
    (by rw [h1]; exact (differentiableAt_chart φ.2 (thetaA E a g)).hasFDerivAt)
    (adjL.hasFDerivAt.comp (oneL E a) invL_smooth.2)
  change fderiv ℝ _ _ X = fderiv ℝ _ _ _
  rw [e.fderiv_eq, h2.fderiv]
  simp

/- English proof (translation)
Consider the cases of `o with`. Consider the case `fin k => exact (rt_pull _ φ).trans (by rw [thetaA_finGL]; rfl)`. Consider the case `cpt k => exact (rt_pull (infGL E a (Unitary.toUnits k)) φ).trans (by rw [thetaA_infGL, ← toUnits_conj_PhiK]; rfl)`. Consider the case `lie X => exact lie_pull X φ`.
-/
theorem act_pull (o : Op E a) (φ : Sm E a) : act o (pull E a φ) = pull E a (act (thetaOp o) φ) := by
  cases o with
  | fin k => exact (rt_pull _ φ).trans (by rw [thetaA_finGL]; rfl)
  | cpt k => exact (rt_pull (infGL E a (Unitary.toUnits k)) φ).trans (by rw [thetaA_infGL, ← toUnits_conj_PhiK]; rfl)
  | lie X => exact lie_pull X φ

/- English proof (translation)
Use `conv_lhs => rw [← pull_pull φ, act_pull, pull_pull]`.
-/
theorem pull_act (o : Op E a) (φ : Sm E a) : pull E a (act o φ) = act (thetaOp o) (pull E a φ) := by
  conv_lhs => rw [← pull_pull φ, act_pull, pull_pull]

def thetaChar (χ : HChar E) : HChar E :=
  ⟨(χ.1.comp (Units.map (conjAd E).toMonoidHom))⁻¹, (χ.2.1.comp (Continuous.units_map _ continuous_conjAd)).inv, fun k => by
    have h := χ.2.2 (Units.map (IsCMField.complexConj E).toRingEquiv.toMonoidHom k)
    rw [MonoidHom.inv_apply, inv_eq_one, ← h]
    exact congrArg χ.1 (Units.ext (conjAd_algebraMap (k : E)))⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem thetaChar_apply (χ : HChar E) (x : Ideles E) :
    (thetaChar χ).1 x = (χ.1 (Units.map (conjAd E).toMonoidHom x))⁻¹ := rfl

/- English proof (translation)
The claim follows from `Subtype.ext <| funext fun g => congrArg (fun u : ℂˣ => φ.1 (thetaA E a g) * u) ((congrArg χ.1 (det_thetaGL _ g)).trans (map_inv χ.1 _))`.
-/
theorem pull_mulChi (χ : HChar E) (φ : Sm E a) : pull E a (mulChi a χ φ) = mulChi a (thetaChar χ) (pull E a φ) :=
  Subtype.ext <| funext fun g => congrArg (fun u : ℂˣ => φ.1 (thetaA E a g) * u)
    ((congrArg χ.1 (det_thetaGL _ g)).trans (map_inv χ.1 _))

/- English proof (translation)
Use `set R := (pull E a).toLinearMap * rt E a (infGL E a (PhiU a (Cinf E))) with hR`. Establish `h1 : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), lie E a (toL X) * R = -(R * lie E a (toL Xᴴ))` using `fun X => by`. Rewrite using `[hR, mul_assoc, GlobalTheory.CapAdInv.rt_lie]`. Use `LinearMap.ext fun φ => (lie_pull (toL X) _).trans ?_` and prove the remaining obligations. Rewrite using `[map_neg, LinearMap.neg_apply, map_neg]`.

Both sides reduce to the same expression. Establish `h2 : ∀ z, lieS E a i j (atEmb τ z) * R = -(R * lieS E a j i (atEmb (ComplexEmbedding.conjugate τ) z))` using `fun z => by`. Establish `e : star (atEmb τ z) = atEmb (ComplexEmbedding.conjugate τ) z` using `by classical`. Rewrite using `[atEmb_conj]`. Unfold `atEmb`.

Rewrite using `[Pi.star_single]`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[lieS_apply, h1, Matrix.conjTranspose_single, e, lieS_apply]`. Simplify using `only [Eop, smul_mul_assoc, sub_mul, h2, mul_neg, mul_smul_comm, mul_sub]`. Use `module`.
-/
theorem pull_Eop (τ : E →+* ℂ) (i j : Fin a) :
    ((pull E a).toLinearMap * rt E a (infGL E a (PhiU a (Cinf E)))) * (-Eop (ComplexEmbedding.conjugate τ) j i) =
      Eop τ i j * ((pull E a).toLinearMap * rt E a (infGL E a (PhiU a (Cinf E)))) := by
  set R := (pull E a).toLinearMap * rt E a (infGL E a (PhiU a (Cinf E))) with hR
  have h1 : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), lie E a (toL X) * R = -(R * lie E a (toL Xᴴ)) := fun X => by
    rw [hR, mul_assoc, GlobalTheory.CapAdInv.rt_lie]
    refine LinearMap.ext fun φ => (lie_pull (toL X) _).trans ?_
    rw [map_neg, LinearMap.neg_apply, map_neg]
    rfl
  have h2 : ∀ z, lieS E a i j (atEmb τ z) * R = -(R * lieS E a j i (atEmb (ComplexEmbedding.conjugate τ) z)) := fun z => by
    have e : star (atEmb τ z) = atEmb (ComplexEmbedding.conjugate τ) z := by
      classical
      rw [atEmb_conj]
      unfold atEmb
      rw [Pi.star_single]
      split_ifs <;> rfl
    rw [lieS_apply, h1, Matrix.conjTranspose_single, e, lieS_apply]
  simp only [Eop, smul_mul_assoc, sub_mul, h2, mul_neg, mul_smul_comm, mul_sub]
  module

/- English proof (translation)
Establish `h` using `GlobalTheory.CapAdInv.qdet_semiconj (fun i j => -Eop (ComplexEmbedding.conjugate τ) j i) (Eop τ) _ (pull_Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2)`. Establish `e : (a : ℂ) - 1 - (u + ((a : ℂ) - 1) / 2) = -u + ((a : ℂ) - 1) / 2` using `by ring`. Rewrite `h` using `[(GlobalTheory.CapelliNegT.glRel_negT_and_qdet _ a _ (glRel_Eop (ComplexEmbedding.conjugate τ))).2, e, ← cap, ← cap]`. Establish `h2` using `(GlobalTheory.CapAdInv.cap_commute_rt_infGL E a (ComplexEmbedding.conjugate τ) (-u) (PhiU a (Cinf E))).smul_left ((-1 : ℂ) ^ a)`. Generalize the expression as in `(-1 : ℂ) ^ a • cap (a := a) (ComplexEmbedding.conjugate τ) (-u) = z at h h2 ⊢`.

Generalize the expression as in `cap (a := a) τ u = z' at h ⊢`. Take `⟨ψ, rfl⟩ : ∃ ψ, rt E a (infGL E a (PhiU a (Cinf E))) ψ = φ` from `⟨rt E a (infGL E a (PhiU a (Cinf E)))⁻¹ φ, Subtype.ext (funext fun g => congrArg φ.1 (mul_inv_cancel_right g _))⟩`. Conclude with `(LinearMap.congr_fun h ψ).symm.trans (congrArg (pull E a) (LinearMap.congr_fun h2.eq ψ).symm)`.
-/
theorem cap_pull (τ : E →+* ℂ) (u : ℂ) (φ : Sm E a) :
    cap τ u (pull E a φ) = pull E a (((-1 : ℂ) ^ a • cap (a := a) (ComplexEmbedding.conjugate τ) (-u) : Module.End ℂ (Sm E a)) φ) := by
  have h := GlobalTheory.CapAdInv.qdet_semiconj (fun i j => -Eop (ComplexEmbedding.conjugate τ) j i) (Eop τ) _
    (pull_Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2)
  have e : (a : ℂ) - 1 - (u + ((a : ℂ) - 1) / 2) = -u + ((a : ℂ) - 1) / 2 := by ring
  rw [(GlobalTheory.CapelliNegT.glRel_negT_and_qdet _ a _ (glRel_Eop (ComplexEmbedding.conjugate τ))).2, e, ← cap, ← cap] at h
  have h2 := (GlobalTheory.CapAdInv.cap_commute_rt_infGL E a (ComplexEmbedding.conjugate τ) (-u) (PhiU a (Cinf E))).smul_left
    ((-1 : ℂ) ^ a)
  generalize (-1 : ℂ) ^ a • cap (a := a) (ComplexEmbedding.conjugate τ) (-u) = z at h h2 ⊢
  generalize cap (a := a) τ u = z' at h ⊢
  obtain ⟨ψ, rfl⟩ : ∃ ψ, rt E a (infGL E a (PhiU a (Cinf E))) ψ = φ :=
    ⟨rt E a (infGL E a (PhiU a (Cinf E)))⁻¹ φ, Subtype.ext (funext fun g => congrArg φ.1 (mul_inv_cancel_right g _))⟩
  exact (LinearMap.congr_fun h ψ).symm.trans (congrArg (pull E a) (LinearMap.congr_fun h2.eq ψ).symm)

/- English proof (translation)
Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨τ, u, rfl⟩` from `hx`. Conclude with `⟨_, Subalgebra.smul_mem _ (Algebra.subset_adjoin (by exact ⟨_, _, rfl⟩)) _, cap_pull τ u⟩`. Consider the case `algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨x', h1, h2⟩` from `hx`. Take `⟨y', h3, h4⟩` from `hy`. Conclude with `⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩`. Consider the case `mul x y _ _ hx hy`.

Take `⟨x', h1, h2⟩` from `hx`. Take `⟨y', h3, h4⟩` from `hy`. Conclude with `⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩`.
-/
theorem Zalg_pull {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    ∃ z' ∈ Zalg E a, ∀ φ, z (pull E a φ) = pull E a (z' φ) := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨τ, u, rfl⟩ := hx
    exact ⟨_, Subalgebra.smul_mem _ (Algebra.subset_adjoin (by exact ⟨_, _, rfl⟩)) _, cap_pull τ u⟩
  | algebraMap c => exact ⟨_, Subalgebra.algebraMap_mem _ c, fun φ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' + y', add_mem h1 h3, fun φ => by simp [h2, h4]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', h1, h2⟩ := hx
    obtain ⟨y', h3, h4⟩ := hy
    exact ⟨x' * y', mul_mem h1 h3, fun φ => by simp [h2, h4]⟩

omit [IsCMField E] in

/- English proof (translation)
Establish `h1 : ∀ y : GL (Fin a) (Cinf E), ‖toL (thetaGL a (starRingEnd (Cinf E)) y).val‖ ≤ ‖toL (y⁻¹).val‖` using `fun y => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by`. Express the relevant statement in the definitionally equal form `‖(thetaGL a (starRingEnd (Cinf E)) y).val i j‖ ≤ _`. Establish `e : ‖(thetaGL a (starRingEnd (Cinf E)) y).val i j‖ = ‖toL (y⁻¹).val j.rev i.rev‖`. Rewrite using `[thetaGL_apply]`. Break down `neg_one_pow_eq_or (Cinf E) ((i : ℕ) + j) with h | h` into its components or cases.

Rewrite using `[h, one_mul]`. Conclude with `norm_star _`. Rewrite using `[h, neg_one_mul, norm_neg]`. Conclude with `norm_star _`. Conclude with `e.trans_le ((norm_le_pi_norm _ _).trans (norm_le_pi_norm (toL (y⁻¹).val) _))`.

Establish `h2 : ∀ y : GL (Fin a) (Cinf E), height (thetaGL a (starRingEnd (Cinf E)) y) ≤ height y` using `fun y => by`. Establish `h3` using `h1 y⁻¹`. Rewrite `h3` using `[inv_inv, map_inv]`. Unfold `height`. Combine the linear relations using `[h1 y]`.

Use `le_antisymm (h2 y) ?_` and prove the remaining obligations. Use `conv_lhs => rw [← thetaGL_thetaGL _ starRingEnd_self_apply y]`. Conclude with `h2 _`.
-/
theorem height_theta (y : GL (Fin a) (Cinf E)) : height (thetaGL a (starRingEnd (Cinf E)) y) = height y := by
  have h1 : ∀ y : GL (Fin a) (Cinf E), ‖toL (thetaGL a (starRingEnd (Cinf E)) y).val‖ ≤ ‖toL (y⁻¹).val‖ := fun y =>
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by
      change ‖(thetaGL a (starRingEnd (Cinf E)) y).val i j‖ ≤ _
      have e : ‖(thetaGL a (starRingEnd (Cinf E)) y).val i j‖ = ‖toL (y⁻¹).val j.rev i.rev‖ := by
        rw [thetaGL_apply]
        rcases neg_one_pow_eq_or (Cinf E) ((i : ℕ) + j) with h | h
        · rw [h, one_mul]; exact norm_star _
        · rw [h, neg_one_mul, norm_neg]; exact norm_star _
      exact e.trans_le ((norm_le_pi_norm _ _).trans (norm_le_pi_norm (toL (y⁻¹).val) _))
  have h2 : ∀ y : GL (Fin a) (Cinf E), height (thetaGL a (starRingEnd (Cinf E)) y) ≤ height y := fun y => by
    have h3 := h1 y⁻¹
    rw [inv_inv, map_inv] at h3
    unfold height
    linarith [h1 y]
  refine le_antisymm (h2 y) ?_
  conv_lhs => rw [← thetaGL_thetaGL _ starRingEnd_self_apply y]
  exact h2 _

/- English proof (translation)
Use `h.preimage (continuous_thetaGL (cFin E) (continuous_conjFin _)) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`. Conclude with `(Eq.congr_left (act_pull (.fin k) φ)).trans (pull E a).injective.eq_iff`.
-/
theorem level_pull {φ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ}) :
    IsOpen {k | finRep E a k (pull E a φ) = pull E a φ} := by
  convert h.preimage (continuous_thetaGL (cFin E) (continuous_conjFin _)) using 1
  ext k
  exact (Eq.congr_left (act_pull (.fin k) φ)).trans (pull E a).injective.eq_iff

/- English proof (translation)
Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map (pull E a).toLinearMap) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull (.cpt k) φ).symm⟩`.
-/
theorem kfin_pull {φ : Sm E a} (h : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ))) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k (pull E a φ))) := by
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map
    (pull E a).toLinearMap) (Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨_, Submodule.subset_span ⟨_, rfl⟩, (act_pull (.cpt k) φ).symm⟩

/- English proof (translation)
Rewrite using `[pull_apply, map_mul, thetaA_ratGL, h.left, pull_apply] level := level_pull h.level kfin := kfin_pull h.kfin zfin := by`. Use `h.zfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)).map (pull E a).toLinearMap) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨z', h1, h2⟩` from `Zalg_pull hz`.

Conclude with `⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩`. Use `growth g := by`. Take `⟨C, N, h1⟩` from `h.growth (thetaA E a g)`. Use `⟨C, N, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[pull_apply, map_mul, thetaA_infGL, ← height_theta]`.

Conclude with `h1 _`.
-/
theorem isAutForm_pull {φ : Sm E a} (h : IsAutForm φ) : IsAutForm (pull E a φ) where
  left γ g := by rw [pull_apply, map_mul, thetaA_ratGL, h.left, pull_apply]
  level := level_pull h.level
  kfin := kfin_pull h.kfin
  zfin := by
    have := h.zfin
    refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
      Zalg E a)).map (pull E a).toLinearMap) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨z', h1, h2⟩ := Zalg_pull hz
    exact ⟨_, Submodule.subset_span ⟨z', h1, rfl⟩, (h2 φ).symm⟩
  growth g := by
    obtain ⟨C, N, h1⟩ := h.growth (thetaA E a g)
    refine ⟨C, N, fun y => ?_⟩
    rw [pull_apply, map_mul, thetaA_infGL, ← height_theta]
    exact h1 _

section Block

variable {R : Type} [CommRing R] {r s : ℕ}

def revIx (h : r + s = a) (p : BlockIx a s) : BlockIx a r :=
  ⟨(p.1.2.rev, p.1.1.rev), by have := p.2; have := p.1.2.2; simp only [Fin.val_rev]; omega⟩

def blockMap (h : r + s = a) (c : R →+* R) : (BlockIx a r → R) →+ (BlockIx a s → R) where
  toFun x p := (-1) ^ ((p.1.1 : ℕ) + p.1.2) * c (-x (revIx h p))
  map_zero' := funext fun p => by simp
  map_add' x y := funext fun p => by simp only [Pi.add_apply, neg_add, map_add, mul_add]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[thetaGL_apply]`. Express the relevant statement in the definitionally equal form `_ * c ((1 - nilM x : Matrix (Fin a) (Fin a) R) j.rev i.rev) = (1 + nilM (blockMap h c x) : Matrix (Fin a) (Fin a) R) i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`.

Simplify using `only [Matrix.sub_apply, Matrix.add_apply, nilM, Matrix.of_apply, Matrix.one_apply, Fin.rev_inj]`. Distinguish the cases in `h1 : (i : ℕ) < s ∧ s ≤ (j : ℕ)`. Rewrite using `[dif_pos h1, dif_pos (by simp only [Fin.val_rev]; omega), if_neg (fun e => by subst e; omega), if_neg (fun e => by subst e; omega), zero_sub, zero_add]`. Both sides reduce to the same expression. Rewrite using `[dif_neg h1, dif_neg (by simp only [Fin.val_rev]; omega), sub_zero, add_zero]`.

Distinguish the cases in `h2 : i = j`. Substitute `h2` using the available equality. Rewrite using `[if_pos rfl, map_one, mul_one, Even.neg_one_pow ⟨_, rfl⟩]`. Rewrite using `[if_neg h2, if_neg (Ne.symm h2), map_zero, mul_zero]`.
-/
theorem thetaGL_unip (h : r + s = a) (c : R →+* R) (x : BlockIx a r → R) :
    thetaGL a c (unip x) = unip (blockMap h c x) := by
  ext i j
  rw [thetaGL_apply]
  change _ * c ((1 - nilM x : Matrix (Fin a) (Fin a) R) j.rev i.rev) =
    (1 + nilM (blockMap h c x) : Matrix (Fin a) (Fin a) R) i j
  have hi := i.2
  have hj := j.2
  simp only [Matrix.sub_apply, Matrix.add_apply, nilM, Matrix.of_apply, Matrix.one_apply, Fin.rev_inj]
  by_cases h1 : (i : ℕ) < s ∧ s ≤ (j : ℕ)
  · rw [dif_pos h1, dif_pos (by simp only [Fin.val_rev]; omega), if_neg (fun e => by subst e; omega),
      if_neg (fun e => by subst e; omega), zero_sub, zero_add]
    rfl
  · rw [dif_neg h1, dif_neg (by simp only [Fin.val_rev]; omega), sub_zero, add_zero]
    by_cases h2 : i = j
    · subst h2
      rw [if_pos rfl, map_one, mul_one, Even.neg_one_pow ⟨_, rfl⟩]
    · rw [if_neg h2, if_neg (Ne.symm h2), map_zero, mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Establish `e : revIx h (revIx h' p) = p` using `Subtype.ext (Prod.ext (Fin.rev_rev _) (Fin.rev_rev _))`. Express the relevant statement in the definitionally equal form `_ * c (-((-1) ^ ((p.1.2.rev : ℕ) + p.1.1.rev) * c (-x (revIx h (revIx h' p))))) = _`. Rewrite using `[e, map_neg, map_mul, hc, map_pow, map_neg, map_one, mul_neg, ← mul_assoc, sign_rev, one_mul, neg_neg]`.
-/
theorem blockMap_blockMap (h : r + s = a) (h' : s + r = a) (c : R →+* R) (hc : ∀ x, c (c x) = x) (x : BlockIx a r → R) :
    blockMap h' c (blockMap h c x) = x := by
  funext p
  have e : revIx h (revIx h' p) = p := Subtype.ext (Prod.ext (Fin.rev_rev _) (Fin.rev_rev _))
  change _ * c (-((-1) ^ ((p.1.2.rev : ℕ) + p.1.1.rev) * c (-x (revIx h (revIx h' p))))) = _
  rw [e, map_neg, map_mul, hc, map_pow, map_neg, map_one, mul_neg, ← mul_assoc, sign_rev, one_mul, neg_neg]

/- English proof (translation)
The claim follows from `continuous_pi fun p => continuous_const.mul (hc.comp (continuous_apply (revIx h p)).neg)`.
-/
theorem continuous_blockMap [TopologicalSpace R] [IsTopologicalRing R] (h : r + s = a) (c : R →+* R) (hc : Continuous c) :
    Continuous (blockMap h c) :=
  continuous_pi fun p => continuous_const.mul (hc.comp (continuous_apply (revIx h p)).neg)

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Use `⟨blockMap h (IsCMField.complexConj E).toRingEquiv.toRingHom y, funext fun p => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) (_ * IsCMField.complexConj E _) = _ * conjAd E (-algebraMap E (Ad E) _)`. Rewrite using `[map_mul, ← conjAd_algebraMap, map_neg, map_pow, map_neg, map_one]`.
-/
theorem blockMap_mem_ratN (h : r + s = a) {x : BlockIx a r → Ad E} (hx : x ∈ ratN E a r) :
    blockMap h (conjAd E) x ∈ ratN E a s := by
  obtain ⟨y, rfl⟩ := hx
  refine ⟨blockMap h (IsCMField.complexConj E).toRingEquiv.toRingHom y, funext fun p => ?_⟩
  change algebraMap E (Ad E) (_ * IsCMField.complexConj E _) = _ * conjAd E (-algebraMap E (Ad E) _)
  rw [map_mul, ← conjAd_algebraMap, map_neg, map_pow, map_neg, map_one]

end Block

open MeasureTheory in

/- English proof (translation)
Introduce `r h0 h1 _ _ μ 𝓕 hμ hF g`. Take `⟨s, h⟩ : ∃ s, r + s = a` from `⟨a - r, by omega⟩`. Establish `h' : s + r = a` using `by omega`. Set `β : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a s → Ad E)` to `{ toFun := blockMap h (conjAd E) invFun := blockMap h' (conjAd E) left_inv := blockMap_blockMap h h' _ conjAd_conjAd right_inv := blockMap_blockMap h' h _ conjAd_conjAd map_add' := map_add _ continuous_toFun := continuous_blockMap h _ continuous_conjAd continuous_invFun := contin …`. Set `e : ratN E a s ≃ ratN E a r` to `{ toFun := fun y => ⟨β.symm y, blockMap_mem_ratN h' y.2⟩ invFun := fun x => ⟨β x, blockMap_mem_ratN h x.2⟩ left_inv := fun y => Subtype.ext (β.apply_symm_apply y) right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }`.

Use `borelize (BlockIx a s → Ad E)`. Set `m` to `β.toHomeomorph.toMeasurableEquiv`. Establish `h2` using `hφ s (by omega) (by omega) (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ) (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by`. Express the relevant statement in the definitionally equal form `β (β.symm y + x) = y + β x`. Rewrite using `[map_add, β.apply_symm_apply]) (thetaA E a g)`.

Rewrite `h2` using `[m.measurableEmbedding.setIntegral_map, m.injective.preimage_image]`. Rewrite using `[← h2]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Use `beta_reduce`.

Rewrite using `[map_mul, thetaA, thetaGL_unip h]`. Both sides reduce to the same expression.
-/
theorem isCuspidal_pull {φ : GA E a → ℂ} (hφ : IsCuspidal φ) : IsCuspidal fun g => φ (thetaA E a g) := by
  intro r h0 h1 _ _ μ 𝓕 hμ hF g
  obtain ⟨s, h⟩ : ∃ s, r + s = a := ⟨a - r, by omega⟩
  have h' : s + r = a := by omega
  let β : (BlockIx a r → Ad E) ≃ₜ+ (BlockIx a s → Ad E) :=
    { toFun := blockMap h (conjAd E)
      invFun := blockMap h' (conjAd E)
      left_inv := blockMap_blockMap h h' _ conjAd_conjAd
      right_inv := blockMap_blockMap h' h _ conjAd_conjAd
      map_add' := map_add _
      continuous_toFun := continuous_blockMap h _ continuous_conjAd
      continuous_invFun := continuous_blockMap h' _ continuous_conjAd }
  let e : ratN E a s ≃ ratN E a r :=
    { toFun := fun y => ⟨β.symm y, blockMap_mem_ratN h' y.2⟩
      invFun := fun x => ⟨β x, blockMap_mem_ratN h x.2⟩
      left_inv := fun y => Subtype.ext (β.apply_symm_apply y)
      right_inv := fun x => Subtype.ext (β.symm_apply_apply x) }
  borelize (BlockIx a s → Ad E)
  let m := β.toHomeomorph.toMeasurableEquiv
  have h2 := hφ s (by omega) (by omega) (μ.map m) (m '' 𝓕) (β.isAddHaarMeasure_map μ)
    (hF.image_of_equiv m.toEquiv (MeasurePreserving.symm m ⟨m.measurable, rfl⟩).quasiMeasurePreserving e fun y x => by
      change β (β.symm y + x) = y + β x
      rw [map_add, β.apply_symm_apply]) (thetaA E a g)
  rw [m.measurableEmbedding.setIntegral_map, m.injective.preimage_image] at h2
  rw [← h2]
  congr 1
  funext x
  beta_reduce
  rw [map_mul, thetaA, thetaGL_unip h]
  rfl

def thetaSub (π : CuspSub E a) : CuspSub E a where
  V := π.V.map (pull E a).toLinearMap
  cusp := by rintro _ ⟨φ, hφ, rfl⟩; exact ⟨isAutForm_pull (π.cusp φ hφ).1, isCuspidal_pull (π.cusp φ hφ).2⟩
  stable := by
    rintro o _ ⟨φ, hφ, rfl⟩
    exact ⟨_, π.stable _ φ hφ, (act_pull o φ).symm⟩
  ne_bot h := π.ne_bot ((Submodule.map_eq_bot_iff (e := pull E a)).1 h)
  irred W hW hs := by
    have h := π.irred (W.comap (pull E a).toLinearMap) (fun φ hφ => by
      obtain ⟨ψ, h1, h2⟩ := hW hφ
      rwa [← (pull E a).injective h2]) fun o φ hφ => by
      change pull E a (act o φ) ∈ W
      rw [pull_act]
      exact hs _ _ hφ
    have e := Submodule.map_comap_eq_of_surjective (f := (pull E a).toLinearMap) (pull E a).surjective W
    exact h.imp (fun h => by rw [← e, h, Submodule.map_bot]) fun h => by rw [← e, h]

/- English proof (translation)
The claim follows from `CuspSub.ext <| by ext φ exact ⟨fun ⟨_, ⟨ψ, h, rfl⟩, e⟩ => e ▸ (pull_pull ψ).symm ▸ h, fun h => ⟨_, ⟨φ, h, rfl⟩, pull_pull φ⟩⟩`.
-/
theorem thetaSub_thetaSub (π : CuspSub E a) : thetaSub (thetaSub π) = π := CuspSub.ext <| by
  ext φ
  exact ⟨fun ⟨_, ⟨ψ, h, rfl⟩, e⟩ => e ▸ (pull_pull ψ).symm ▸ h, fun h => ⟨_, ⟨φ, h, rfl⟩, pull_pull φ⟩⟩

/- English proof (translation)
The claim follows from `CuspSub.ext <| by change (π.V.map _).map _ = (π.V.map _).map _ rw [← Submodule.map_comp, ← Submodule.map_comp] exact congrArg (fun f => π.V.map f) (LinearMap.ext (pull_mulChi χ))`.
-/
theorem thetaSub_twist (π : CuspSub E a) (χ : HChar E) : thetaSub (π.twist χ) = (thetaSub π).twist (thetaChar χ) :=
  CuspSub.ext <| by
    change (π.V.map _).map _ = (π.V.map _).map _
    rw [← Submodule.map_comp, ← Submodule.map_comp]
    exact congrArg (fun f => π.V.map f) (LinearMap.ext (pull_mulChi χ))

/- English proof (translation)
Take `⟨T, hT⟩` from `h`. Use `⟨((pull E a).submoduleMap π.V).trans T, fun o φ => ?_⟩` and prove the remaining obligations. Conclude with `(congrArg T (Subtype.ext (act_pull o φ.1).symm)).trans (hT o ((pull E a).submoduleMap π.V φ))`.
-/
theorem isCsd_of_iso {π : CuspSub E a} (h : (thetaSub π).Iso π) : π.IsCsd := by
  obtain ⟨T, hT⟩ := h
  refine ⟨((pull E a).submoduleMap π.V).trans T, fun o φ => ?_⟩
  exact (congrArg T (Subtype.ext (act_pull o φ.1).symm)).trans (hT o ((pull E a).submoduleMap π.V φ))

/- English proof (translation)
Use `Units.ext (Prod.ext (map_one ((infEq E).toRingHom.comp ((starRingEnd (Cinf E)).comp (infEq E).symm.toRingHom))) ?_)` and prove the remaining obligations. Conclude with `Subtype.ext (GlobalTheory.Mem.Chr.map_update_one (conjSrc_injective _) (conjLoc _) v _)`.
-/
theorem conjAd_localIdele (v : HeightOneSpectrum (𝓞 E))
    (x : ((conjSrc (IsCMField.complexConj E).toRingEquiv v).adicCompletion E)ˣ) :
    Units.map (conjAd E).toMonoidHom (localIdele E _ x) = localIdele E v (Units.map (conjLoc _ v).toMonoidHom x) := by
  classical
  refine Units.ext (Prod.ext (map_one ((infEq E).toRingHom.comp ((starRingEnd (Cinf E)).comp (infEq E).symm.toRingHom))) ?_)
  exact Subtype.ext (GlobalTheory.Mem.Chr.map_update_one (conjSrc_injective _) (conjLoc _) v _)

/- English proof (translation)
Establish `h : ∀ k : Eˣ, infDiag k = infId E (Units.map (pInf E).toMonoidHom (diagUnits E k))` using `fun k => by`. Rewrite using `[NormTriv.infId_pInf, infDiag, MonoidHom.finsetProd_apply]`. Both sides reduce to the same expression. Establish `h1 : ∀ y : (Cinf E)ˣ, pInf E (infId E y).val = y` using `fun y => by`. Express the relevant statement in the definitionally equal form `(infEq E).symm (1 - infEq E 1 + infEq E y) = y`.

Simplify using the standard rewrite rules. Establish `h2 : ∀ y : (Cinf E)ˣ, pFin E (infId E y).val = 1` using `fun y => by`. Express the relevant statement in the definitionally equal form `(1 : Af E) - 0 + 0 = 1`. Simplify using the standard rewrite rules. Rewrite using `[h, h]`.

Use `Units.ext (ad_ext ((pInf_conjAd _).trans ?_) ((pFin_conjAd _).trans ?_))` and prove the remaining obligations. Rewrite using `[h1, h1]`. Conclude with `(pInf_complexConj (k : E)).symm`. Rewrite using `[h2, h2, map_one]`.
-/
theorem conjAd_infDiag (k : Eˣ) : Units.map (conjAd E).toMonoidHom (infDiag k) =
    infDiag (Units.map (IsCMField.complexConj E).toRingEquiv.toMonoidHom k) := by
  have h : ∀ k : Eˣ, infDiag k = infId E (Units.map (pInf E).toMonoidHom (diagUnits E k)) := fun k => by
    rw [NormTriv.infId_pInf, infDiag, MonoidHom.finsetProd_apply]; rfl
  have h1 : ∀ y : (Cinf E)ˣ, pInf E (infId E y).val = y := fun y => by
    change (infEq E).symm (1 - infEq E 1 + infEq E y) = y
    simp
  have h2 : ∀ y : (Cinf E)ˣ, pFin E (infId E y).val = 1 := fun y => by
    change (1 : Af E) - 0 + 0 = 1
    simp
  rw [h, h]
  refine Units.ext (ad_ext ((pInf_conjAd _).trans ?_) ((pFin_conjAd _).trans ?_))
  · rw [h1, h1]
    exact (pInf_complexConj (k : E)).symm
  · rw [h2, h2, map_one]

/- English proof (translation)
Establish `hs : ∀ v, ∃ v', conjSrc (IsCMField.complexConj E).toRingEquiv v' = v` using `fun v => ⟨_, conjSrc_conjSrc v⟩`. Establish `hl : ∀ v x, (thetaChar χ).loc (conjSrc (IsCMField.complexConj E).toRingEquiv v) x = (χ.loc v (Units.map (conjLoc _ v).toMonoidHom x))⁻¹` using `fun v x => congrArg (fun y => (χ.1 y)⁻¹) (conjAd_localIdele v x)`. Use `⟨fun v => ?_, fun v => ?_, fun k => ?_⟩` and prove the remaining obligations. Take `⟨v, rfl⟩` from `hs v`. Introduce `x hx`.

Establish `hx' : IsUnitAt v (Units.map (conjLoc _ v).toMonoidHom x)` using `((conjLoc_spec _ v).2.2 x.val).trans hx`. Rewrite using `[hl, h.1 v _ hx', inv_one]`. Take `⟨v, rfl⟩` from `hs v`. Establish `e : Ideal.absNorm (conjSrc (IsCMField.complexConj E).toRingEquiv v).asIdeal = Ideal.absNorm v.asIdeal`. Rewrite using `[(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v)]`.

Conclude with `Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv _) (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv`. Establish `hu : ∀ x, IsUnifAt (conjSrc (IsCMField.complexConj E).toRingEquiv v) x → IsUnifAt v (Units.map (conjLoc _ v).toMonoidHom x)` using `fun x hx => ((conjLoc_spec _ v).2.2 x.val).trans hx`. Rewrite using `[HChar.val, HChar.locK, MonoidHom.comp_apply, hl, χ.val_eq (h.1 v) _ (hu _ (unif_spec _)), Units.val_inv_eq_inv_val, h.2.1, e, Complex.ofReal_neg, Complex.cpow_neg _ (-(s : ℂ))]`. Rewrite using `[HChar.inf, MonoidHom.comp_apply, thetaChar_apply, conjAd_infDiag, Units.val_inv_eq_inv_val]`. Use `(congrArg Inv.inv (h.2.2 _)).trans ?_` and prove the remaining obligations.

Rewrite using `[← Finset.prod_inv_distrib]`. Use `Finset.prod_congr rfl fun φ _ => ?_` and prove the remaining obligations. Establish `e : ‖φ (IsCMField.complexConj E (k : E))‖ = ‖φ (k : E)‖`. Rewrite using `[IsCMField.complexEmbedding_complexConj, Complex.norm_conj]`. Rewrite using `[Complex.ofReal_neg, Complex.cpow_neg, ← e]`.

Both sides reduce to the same expression.
-/
theorem isAbsPow_thetaChar {χ : HChar E} {s : ℝ} (h : χ.IsAbsPow s) : (thetaChar χ).IsAbsPow (-s) := by
  have hs : ∀ v, ∃ v', conjSrc (IsCMField.complexConj E).toRingEquiv v' = v := fun v => ⟨_, conjSrc_conjSrc v⟩
  have hl : ∀ v x, (thetaChar χ).loc (conjSrc (IsCMField.complexConj E).toRingEquiv v) x =
      (χ.loc v (Units.map (conjLoc _ v).toMonoidHom x))⁻¹ := fun v x =>
    congrArg (fun y => (χ.1 y)⁻¹) (conjAd_localIdele v x)
  refine ⟨fun v => ?_, fun v => ?_, fun k => ?_⟩
  · obtain ⟨v, rfl⟩ := hs v
    intro x hx
    have hx' : IsUnitAt v (Units.map (conjLoc _ v).toMonoidHom x) := ((conjLoc_spec _ v).2.2 x.val).trans hx
    rw [hl, h.1 v _ hx', inv_one]
  · obtain ⟨v, rfl⟩ := hs v
    have e : Ideal.absNorm (conjSrc (IsCMField.complexConj E).toRingEquiv v).asIdeal = Ideal.absNorm v.asIdeal := by
      rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v)]
      exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv _)
        (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv
    have hu : ∀ x, IsUnifAt (conjSrc (IsCMField.complexConj E).toRingEquiv v) x →
        IsUnifAt v (Units.map (conjLoc _ v).toMonoidHom x) := fun x hx => ((conjLoc_spec _ v).2.2 x.val).trans hx
    rw [HChar.val, HChar.locK, MonoidHom.comp_apply, hl, χ.val_eq (h.1 v) _ (hu _ (unif_spec _)), Units.val_inv_eq_inv_val, h.2.1, e,
      Complex.ofReal_neg, Complex.cpow_neg _ (-(s : ℂ))]
  · rw [HChar.inf, MonoidHom.comp_apply, thetaChar_apply, conjAd_infDiag, Units.val_inv_eq_inv_val]
    refine (congrArg Inv.inv (h.2.2 _)).trans ?_
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun φ _ => ?_
    have e : ‖φ (IsCMField.complexConj E (k : E))‖ = ‖φ (k : E)‖ := by
      rw [IsCMField.complexEmbedding_complexConj, Complex.norm_conj]
    rw [Complex.ofReal_neg, Complex.cpow_neg, ← e]
    rfl

section Levi

variable {R : Type} [CommRing R] {d N : ℕ}

/- English proof (translation)
Rewrite using `[stdBlocks_val]`. Simplify using the standard rewrite rules.
-/
theorem blocks_val (h : ∑ _ : Fin d, a = N) (b : Fin d) (i : Fin a) :
    (stdBlocks (fun _ : Fin d => a) h ⟨b, i⟩ : ℕ) = b * a + i := by
  rw [stdBlocks_val]; simp

/- English proof (translation)
Establish `h1 : d * a = N` using `by simpa using h`. Establish `h2 : (b.rev : ℕ) + b + 1 = d` using `by have := b.2; rw [Fin.val_rev]; omega`. Establish `h3 : (b.rev : ℕ) * a + b * a + a = N` using `by rw [← h1]; conv_rhs => rw [← h2]; ring_nf`. Use `i.2` as an intermediate fact. Use `Fin.ext ?_` and prove the remaining obligations.

Rewrite using `[Fin.val_rev, blocks_val, blocks_val, Fin.val_rev (i := i)]`. Use linear arithmetic over natural numbers and integers.
-/
theorem blocks_rev (h : ∑ _ : Fin d, a = N) (b : Fin d) (i : Fin a) :
    (stdBlocks (fun _ : Fin d => a) h ⟨b, i⟩).rev = stdBlocks (fun _ : Fin d => a) h ⟨b.rev, i.rev⟩ := by
  have h1 : d * a = N := by simpa using h
  have h2 : (b.rev : ℕ) + b + 1 = d := by have := b.2; rw [Fin.val_rev]; omega
  have h3 : (b.rev : ℕ) * a + b * a + a = N := by rw [← h1]; conv_rhs => rw [← h2]; ring_nf
  have := i.2
  refine Fin.ext ?_
  rw [Fin.val_rev, blocks_val, blocks_val, Fin.val_rev (i := i)]
  omega

/- English proof (translation)
Rewrite using `[blocks_val, blocks_val, show b * a + i + (b * a + j) = 2 * (b * a) + (i + j) by ring, pow_add, pow_mul]`. Simplify using the standard rewrite rules.
-/
theorem blocks_sign (h : ∑ _ : Fin d, a = N) (b : Fin d) (i j : Fin a) :
    (-1 : R) ^ ((stdBlocks (fun _ : Fin d => a) h ⟨b, i⟩ : ℕ) + stdBlocks (fun _ : Fin d => a) h ⟨b, j⟩) =
      (-1) ^ ((i : ℕ) + j) := by
  rw [blocks_val, blocks_val, show b * a + i + (b * a + j) = 2 * (b * a) + (i + j) by ring, pow_add, pow_mul]
  simp

/- English proof (translation)
Use extensionality with `i j`. Take `⟨⟨b, i⟩, rfl⟩` from `(stdBlocks (fun _ : Fin d => a) h).surjective i`. Take `⟨⟨b', j⟩, rfl⟩` from `(stdBlocks (fun _ : Fin d => a) h).surjective j`. Rewrite using `[thetaGL_apply, blocks_rev, blocks_rev, ← map_inv]`. Distinguish the cases in `e : b = b'`.

Substitute `e` using the available equality. Rewrite using `[leviEmb_apply_same, leviEmb_apply_same, thetaGL_apply, blocks_sign]`. Both sides reduce to the same expression. Rewrite using `[leviEmb_apply_ne _ _ _ e, leviEmb_apply_ne _ _ _ (fun e' => e (Fin.rev_injective e').symm), map_zero, mul_zero]`.
-/
theorem thetaGL_leviEmb (h : ∑ _ : Fin d, a = N) (c : R →+* R) (m : Fin d → GL (Fin a) R) :
    thetaGL N c (leviEmb R (stdBlocks (fun _ : Fin d => a) h) m) =
      leviEmb R (stdBlocks (fun _ : Fin d => a) h) fun b => thetaGL a c (m b.rev) := by
  ext i j
  obtain ⟨⟨b, i⟩, rfl⟩ := (stdBlocks (fun _ : Fin d => a) h).surjective i
  obtain ⟨⟨b', j⟩, rfl⟩ := (stdBlocks (fun _ : Fin d => a) h).surjective j
  rw [thetaGL_apply, blocks_rev, blocks_rev, ← map_inv]
  by_cases e : b = b'
  · subst e
    rw [leviEmb_apply_same, leviEmb_apply_same, thetaGL_apply, blocks_sign]
    rfl
  · rw [leviEmb_apply_ne _ _ _ e, leviEmb_apply_ne _ _ _ (fun e' => e (Fin.rev_injective e').symm), map_zero, mul_zero]

/- English proof (translation)
Take `⟨h1, h2⟩` from `mem_unipRad.1 (inv_mem hu)`. Use `mem_unipRad.2 ⟨mem_parab_iff.2 fun b b' i j e => ?_, fun b i j => ?_⟩` and prove the remaining obligations. Rewrite using `[thetaGL_apply, blocks_rev, blocks_rev, mem_parab_iff.1 h1 _ _ _ _ (Fin.rev_lt_rev.2 e), map_zero, mul_zero]`. Rewrite using `[thetaGL_apply, blocks_rev, blocks_rev, h2, blocks_sign]`. Distinguish the cases in `e : i = j`.

Substitute `e` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, mul_one, Even.neg_one_pow ⟨_, rfl⟩]`. Rewrite using `[Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e (Fin.rev_injective e').symm), map_zero, mul_zero]`.
-/
theorem thetaGL_mem_unipRad (h : ∑ _ : Fin d, a = N) (c : R →+* R) {u : GL (Fin N) R}
    (hu : u ∈ unipRad R (stdBlocks (fun _ : Fin d => a) h)) :
    thetaGL N c u ∈ unipRad R (stdBlocks (fun _ : Fin d => a) h) := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 (inv_mem hu)
  refine mem_unipRad.2 ⟨mem_parab_iff.2 fun b b' i j e => ?_, fun b i j => ?_⟩
  · rw [thetaGL_apply, blocks_rev, blocks_rev, mem_parab_iff.1 h1 _ _ _ _ (Fin.rev_lt_rev.2 e), map_zero, mul_zero]
  · rw [thetaGL_apply, blocks_rev, blocks_rev, h2, blocks_sign]
    by_cases e : i = j
    · subst e
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, mul_one, Even.neg_one_pow ⟨_, rfl⟩]
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne (fun e' => e (Fin.rev_injective e').symm), map_zero, mul_zero]

end Levi

/- English proof (translation)
Use `⟨fun u hu g => ?_, level_pull hφ.2.1, kfin_pull hφ.2.2.1, fun k g => ?_⟩` and prove the remaining obligations. Rewrite using `[pull_apply, map_mul]`. Conclude with `hφ.1 _ (thetaGL_mem_unipRad h _ hu) _`. Establish `key : (tensorForms ρ).map (LinearMap.funLeft ℂ ℂ fun (m : Fin d → GA E a) b => thetaA E a (m b.rev)) ≤ tensorForms fun i => thetaSub (ρ i.rev)`. Rewrite using `[tensorForms, Submodule.map_span_le]`.

Introduce and unpack `_ ⟨ψ, rfl⟩`. Conclude with `Submodule.subset_span ⟨fun i => ⟨_, _, (ψ i.rev).2, rfl⟩, funext fun m => Fintype.prod_equiv Fin.revPerm _ _ fun i => by`. Take `⟨i, rfl⟩` from `Fin.rev_surjective i`. Express the relevant statement in the definitionally equal form `(ψ i.rev).1.1 (thetaA E a (m i.rev.rev)) = (ψ i.rev.rev.rev).1.1 (thetaA E a (m i.rev.rev))`. Rewrite using `[Fin.rev_rev]⟩`.

Use `key ⟨_, hφ.2.2.2 (PhiK E N * k * (PhiK E N)⁻¹) (thetaGL N (cFin E) g), rfl⟩ using 2 with m` and compare the differences between its conclusion and the goal. Rewrite using `[pull_apply, map_mul, map_mul, thetaA_infGL, thetaA_finGL, ← toUnits_conj_PhiK, thetaA, thetaGL_leviEmb]`. Both sides reduce to the same expression.
-/
theorem pull_mem_indForms {d N : ℕ} (h : ∑ _ : Fin d, a = N) (ρ : Fin d → CuspSub E a) {φ : Sm E N}
    (hφ : φ ∈ indForms h ρ) : pull E N φ ∈ indForms h fun i => thetaSub (ρ i.rev) := by
  refine ⟨fun u hu g => ?_, level_pull hφ.2.1, kfin_pull hφ.2.2.1, fun k g => ?_⟩
  · rw [pull_apply, map_mul]
    exact hφ.1 _ (thetaGL_mem_unipRad h _ hu) _
  · have key : (tensorForms ρ).map (LinearMap.funLeft ℂ ℂ fun (m : Fin d → GA E a) b => thetaA E a (m b.rev)) ≤
        tensorForms fun i => thetaSub (ρ i.rev) := by
      rw [tensorForms, Submodule.map_span_le]
      rintro _ ⟨ψ, rfl⟩
      exact Submodule.subset_span ⟨fun i => ⟨_, _, (ψ i.rev).2, rfl⟩, funext fun m =>
        Fintype.prod_equiv Fin.revPerm _ _ fun i => by
          obtain ⟨i, rfl⟩ := Fin.rev_surjective i
          change (ψ i.rev).1.1 (thetaA E a (m i.rev.rev)) = (ψ i.rev.rev.rev).1.1 (thetaA E a (m i.rev.rev))
          rw [Fin.rev_rev]⟩
    convert key ⟨_, hφ.2.2.2 (PhiK E N * k * (PhiK E N)⁻¹) (thetaGL N (cFin E) g), rfl⟩ using 2 with m
    rw [pull_apply, map_mul, map_mul, thetaA_infGL, thetaA_finGL, ← toUnits_conj_PhiK, thetaA, thetaGL_leviEmb]
    rfl

/- English proof (translation)
Use `le_antisymm ?_ fun φ hφ => ⟨_, pull_mem_indForms h ρ hφ, pull_pull φ⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Establish `h1` using `pull_mem_indForms h _ hφ`. Simplify using `only [Fin.rev_rev, thetaSub_thetaSub] at h1`. Conclude with `h1`.
-/
theorem map_pull_indForms {d N : ℕ} (h : ∑ _ : Fin d, a = N) (ρ : Fin d → CuspSub E a) :
    (indForms h fun i => thetaSub (ρ i.rev)).map (pull E N).toLinearMap = indForms h ρ := by
  refine le_antisymm ?_ fun φ hφ => ⟨_, pull_mem_indForms h ρ hφ, pull_pull φ⟩
  rintro _ ⟨φ, hφ, rfl⟩
  have h1 := pull_mem_indForms h _ hφ
  simp only [Fin.rev_rev, thetaSub_thetaSub] at h1
  exact h1

/- English proof (translation)
Introduce and unpack `_ ⟨φ, hφ, rfl⟩ t g`. Express the relevant statement in the definitionally equal form `φ.1 (thetaA E a _) = φ.1 (thetaA E a g)`. Rewrite using `[map_mul, thetaA_splitCentre, h φ hφ]`.
-/
theorem isNormalised_thetaSub {π : CuspSub E a} (h : IsNormalised π) : IsNormalised (thetaSub π) := by
  rintro _ ⟨φ, hφ, rfl⟩ t g
  change φ.1 (thetaA E a _) = φ.1 (thetaA E a g)
  rw [map_mul, thetaA_splitCentre, h φ hφ]

/- English proof (translation)
Take `⟨h, ν, hν, f, hf, hf'⟩` from `h`. Take `⟨T, hT⟩` from `hc`. Take `⟨S, hS⟩` from `LinearMap.exists_extend (V.subtype ∘ₗ T.toLinearMap)`. Establish `hS' : ∀ φ : V, S φ.1 = (T φ).1` using `LinearMap.congr_fun hS`. Establish `hI` using `map_pull_indForms h fun i => π.twist (ν i)`.

Simplify using `only [thetaSub_twist] at hI`. Use `⟨h, fun i => thetaChar (ν i.rev), fun i => ?_, S ∘ₗ f ∘ₗ (pull E N).toLinearMap, ?_, fun o φ hφ => ?_⟩` and prove the remaining obligations. Use `isAbsPow_thetaChar (hν i.rev) using 1` and compare the differences between its conclusion and the goal. Establish `e : spehExp d i.rev = -spehExp d i`. Use `i.2` as an intermediate fact.

Simplify using `only [spehExp, Fin.val_rev]`. Rewrite using `[Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Submodule.map_comp, Submodule.map_comp, hI, hf]`. Use `le_antisymm ?_ fun φ hφ => ⟨_, (T.symm ⟨φ, hφ⟩).2, by rw [hS', T.apply_symm_apply]⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Conclude with `hS' ⟨φ, hφ⟩ ▸ (T _).2`.

Establish `h1 : pull E N φ ∈ indForms h fun i => π.twist (ν i)` using `hI ▸ ⟨φ, hφ, rfl⟩`. Establish `h2 : f (pull E N φ) ∈ V` using `hf ▸ ⟨_, h1, rfl⟩`. Express the relevant statement in the definitionally equal form `S (f (pull E N (act o φ))) = act o (S (f (pull E N φ)))`. Rewrite using `[pull_act, hf' _ _ h1, hS' ⟨_, h2⟩, hS' ⟨_, hV _ _ h2⟩]`. Conclude with `hT o _ _ rfl`.
-/
theorem isSpehOf_thetaSub {N d : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsStable V) (hc : IsCsdGL V) {π : CuspSub E a}
    (h : IsSpehOf V π d) : IsSpehOf V (thetaSub π) d := by
  obtain ⟨h, ν, hν, f, hf, hf'⟩ := h
  obtain ⟨T, hT⟩ := hc
  obtain ⟨S, hS⟩ := LinearMap.exists_extend (V.subtype ∘ₗ T.toLinearMap)
  have hS' : ∀ φ : V, S φ.1 = (T φ).1 := LinearMap.congr_fun hS
  have hI := map_pull_indForms h fun i => π.twist (ν i)
  simp only [thetaSub_twist] at hI
  refine ⟨h, fun i => thetaChar (ν i.rev), fun i => ?_, S ∘ₗ f ∘ₗ (pull E N).toLinearMap, ?_, fun o φ hφ => ?_⟩
  · convert isAbsPow_thetaChar (hν i.rev) using 1
    have e : spehExp d i.rev = -spehExp d i := by
      have := i.2
      simp only [spehExp, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [e]
    ring
  · rw [Submodule.map_comp, Submodule.map_comp, hI, hf]
    refine le_antisymm ?_ fun φ hφ => ⟨_, (T.symm ⟨φ, hφ⟩).2, by rw [hS', T.apply_symm_apply]⟩
    rintro _ ⟨φ, hφ, rfl⟩
    exact hS' ⟨φ, hφ⟩ ▸ (T _).2
  · have h1 : pull E N φ ∈ indForms h fun i => π.twist (ν i) := hI ▸ ⟨φ, hφ, rfl⟩
    have h2 : f (pull E N φ) ∈ V := hf ▸ ⟨_, h1, rfl⟩
    change S (f (pull E N (act o φ))) = act o (S (f (pull E N φ)))
    rw [pull_act, hf' _ _ h1, hS' ⟨_, h2⟩, hS' ⟨_, hV _ _ h2⟩]
    exact hT o _ _ rfl

end GlobalTheory.ThetaPull

/- English proof (translation)
The claim follows from `GlobalTheory.ThetaPull.isCsd_of_iso (H.iso hN hV (GlobalTheory.ThetaPull.isNormalised_thetaSub hπ) hπ (GlobalTheory.ThetaPull.isSpehOf_thetaSub hV.stable hc h) h)`.
-/
theorem GlobalTheory.DiscSpec.isCsd_of_isSpehOf (H : GlobalTheory.Published.DiscreteSpectrumGL) {E : Type} [Field E] [NumberField E]
    [IsCMField E] {N a d : ℕ} (hN : 1 ≤ N) {V : Submodule ℂ (GlobalTheory.CuspRep.Sm E N)} (hV : GlobalTheory.UnitaryBC.IsDiscrete V)
    (hc : GlobalTheory.UnitaryBC.IsCsdGL V) {π : GlobalTheory.CuspRep.CuspSub E a} (hπ : GlobalTheory.DiscSpec.IsNormalised π)
    (h : GlobalTheory.DiscSpec.IsSpehOf V π d) : π.IsCsd :=
  GlobalTheory.ThetaPull.isCsd_of_iso (H.iso hN hV (GlobalTheory.ThetaPull.isNormalised_thetaSub hπ) hπ
    (GlobalTheory.ThetaPull.isSpehOf_thetaSub hV.stable hc h) h)

end
