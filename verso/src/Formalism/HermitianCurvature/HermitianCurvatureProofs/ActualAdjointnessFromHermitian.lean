import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator

open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace

noncomputable section

namespace Formalism.FourierDecayAlt.P.Qx5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Gen

variable {X Y E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def partialFDerivFst (F : X × Y → E) (x : X × Y) : X →L[ℝ] E := (fderiv ℝ F x).comp (ContinuousLinearMap.inl ℝ X Y)

/- English proof (translation)
Establish `h1 : DifferentiableAt ℝ F x` using `(hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)`. Establish `h2 : HasFDerivAt (fun c' : X => (c', x.2)) (ContinuousLinearMap.inl ℝ X Y) x.1` using `hasFDerivAt_prodMk_left x.1 x.2`. Conclude with `HasFDerivAt.comp (g := F) x.1 h1.hasFDerivAt h2`.
-/
theorem hasFDerivAt_partial_fst {F : X × Y → E} {U : Set (X × Y)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {x : X × Y}
    (hx : x ∈ U) : HasFDerivAt (fun c' => F (c', x.2)) (partialFDerivFst F x) x.1 := by
  have h1 : DifferentiableAt ℝ F x := (hF.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have h2 : HasFDerivAt (fun c' : X => (c', x.2)) (ContinuousLinearMap.inl ℝ X Y) x.1 :=
    hasFDerivAt_prodMk_left x.1 x.2
  exact HasFDerivAt.comp (g := F) x.1 h1.hasFDerivAt h2

/- English proof (translation)
Establish `h1 : ContDiffOn ℝ ∞ (fderiv ℝ F) U` using `hF.fderiv_of_isOpen hU (by simp)`. Conclude with `h1.clm_apply contDiffOn_const`.
-/
theorem contDiffOn_partial_fderiv_fst {F : X × Y → E} {U : Set (X × Y)} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (v : X) :
    ContDiffOn ℝ ∞ (fun x => partialFDerivFst F x v) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply contDiffOn_const

/- English proof (translation)
Establish `hc : Continuous (fun c' : X => (c', x.2))` using `by fun_prop`. Conclude with `hc.continuousAt.eventually (hU.mem_nhds hx)`.
-/
theorem eventually_slice {U : Set (X × Y)} (hU : IsOpen U) {x : X × Y} (hx : x ∈ U) :
    ∀ᶠ c' in nhds x.1, (c', x.2) ∈ U := by
  have hc : Continuous (fun c' : X => (c', x.2)) := by fun_prop
  exact hc.continuousAt.eventually (hU.mem_nhds hx)

end Gen

section Rad

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Establish `: OmX m = ⋂ l : Fin m, {x : Fin m → ℂ | x l ≠ 0}`. Use extensionality with `x`. Simplify using `[OmX]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const`.
-/
theorem isOpen_OmX (m : ℕ) : IsOpen (OmX m) := by
  have : OmX m = ⋂ l : Fin m, {x : Fin m → ℂ | x l ≠ 0} := by
    ext x; simp [OmX]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const

def zetaLin (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) : Mx k r →ₗ[ℂ] ℂ where
  toFun := zetaL k r z z' i
  map_add' a b := by simp [zetaL, herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
  map_smul' a b := by simp [zetaL, herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
The claim follows from `((LinearMap.toContinuousLinearMap (zetaLin k r z z' i)).contDiff (n := ∞)).restrict_scalars ℝ`.
-/
theorem zetaL_contDiff (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) :
    ContDiff ℝ ∞ (zetaL k r z z' i) :=
  ((LinearMap.toContinuousLinearMap (zetaLin k r z z' i)).contDiff (n := ∞)).restrict_scalars ℝ

/- English proof (translation)
Unfold `GGl`. Rewrite using `[Complex.ofReal_sub, Complex.star_def, Complex.mul_conj]`.
-/
theorem GGl_cast (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    (GGl k r z z' g : ℂ) = zetaL k r z z' (Fin.last r) g * star (zetaL k r z z' (Fin.last r) g) -
      ((Tz k r z * Tz k r z' : ℝ) : ℂ) := by
  unfold GGl
  rw [Complex.ofReal_sub, Complex.star_def, Complex.mul_conj]

/- English proof (translation)
Unfold `GGl`. Conclude with `(Complex.continuous_normSq.comp (zetaL_contDiff k r z z' (Fin.last r)).continuous).sub continuous_const`.
-/
theorem GGl_continuous (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous (GGl k r z z') := by
  unfold GGl
  exact (Complex.continuous_normSq.comp (zetaL_contDiff k r z z' (Fin.last r)).continuous).sub continuous_const

def OpR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set ((Fin r → ℂ) × Mx k r) :=
  {x | x.1 ∈ OmX r ∧ 0 < GGl k r z z' x.2}

/- English proof (translation)
The claim follows from `((isOpen_OmX r).preimage continuous_fst).inter (isOpen_lt continuous_const ((GGl_continuous k r z z').comp continuous_snd))`.
-/
theorem isOpen_OpR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (OpR k r z z') :=
  ((isOpen_OmX r).preimage continuous_fst).inter
    (isOpen_lt continuous_const ((GGl_continuous k r z z').comp continuous_snd))

/- English proof (translation)
Introduce `_ hx` and use `⟨hx.1, hx.2.2⟩`.
-/
theorem DomR_sub_OpR : DomR k r z z' ⊆ OpR k r z z' := fun _ hx => ⟨hx.1, hx.2.2⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hx.1, hg, hx.2⟩`.
-/
theorem mem_DomR_of_OpR {x : (Fin r → ℂ) × Mx k r} (hx : x ∈ OpR k r z z') (hg : x.2 ∈ Glev k r (Fin.last r)) :
    x ∈ DomR k r z z' := ⟨hx.1, hg, hx.2⟩

/- English proof (translation)
Use `(hasFDerivAt_partial_fst hU hF hx).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [eventually_slice hU hx] with c' hc'`. Conclude with `hΦ (c', x.2) hc' hg`.
-/
theorem slice_hasFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {Φ : Fn k r E}
    {U : Set ((Fin r → ℂ) × Mx k r)} {F : (Fin r → ℂ) × Mx k r → E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hΦ : ∀ x ∈ U, x.2 ∈ Glev k r i → Φ x.1 x.2 = F x) {x : (Fin r → ℂ) × Mx k r} (hx : x ∈ U)
    (hg : x.2 ∈ Glev k r i) : HasFDerivAt (fun c' => Φ c' x.2) (partialFDerivFst F x) x.1 := by
  refine (hasFDerivAt_partial_fst hU hF hx).congr_of_eventuallyEq ?_
  filter_upwards [eventually_slice hU hx] with c' hc'
  exact hΦ (c', x.2) hc' hg

/- English proof (translation)
Use function extensionality and compare the values at `c'`. Conclude with `hΦ.1 (c', g) fun h => hg h.2`.
-/
theorem slice_zero {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') {g : Mx k r}
    (hg : ¬ (g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g)) : (fun c' => Φ c' g) = fun _ => 0 := by
  funext c'
  exact hΦ.1 (c', g) fun h => hg h.2

/- English proof (translation)
Distinguish the cases in `hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g`. Take `⟨U, F, hU, hxU, hF, hΦF⟩` from `hΦ.2.1 (c, g) ⟨hc, hg⟩`. Conclude with `(slice_hasFDerivAt hU hF hΦF hxU hg.1).differentiableAt`. Rewrite using `[slice_zero hΦ hg]`. Conclude with `differentiableAt_const _`.
-/
theorem slice_diff {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (g : Mx k r) : DifferentiableAt ℝ (fun c' => Φ c' g) c := by
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 (c, g) ⟨hc, hg⟩
    exact (slice_hasFDerivAt hU hF hΦF hxU hg.1).differentiableAt
  · rw [slice_zero hΦ hg]
    exact differentiableAt_const _

open Classical in

def dirD {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : Fin r → ℂ) (Φ : Fn k r E) : Fn k r E :=
  fun c g => if c ∈ OmX r then fderiv ℝ (fun c' => Φ c' g) c v else 0

def sandCLM (A : Wp →L[ℂ] Wp) (B : Wq →L[ℂ] Wq) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp A).comp ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip B)

/- English proof (translation)
Use `⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩` and prove the remaining obligations. Unfold `dirD split_ifs with hc`. Establish `hg : ¬ (x.2 ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' x.2)` using `fun h => hx ⟨hc, h⟩`. Rewrite using `[slice_zero hΦ hg]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Take `⟨U, F, hU, hxU, hF, hΦF⟩` from `hΦ.2.1 x₀ hx₀`. Use `⟨U ∩ {x | x.1 ∈ OmX r}, fun x => partialFDerivFst F x v, hU.inter ((isOpen_OmX r).preimage continuous_fst), ⟨hxU, hx₀.1⟩, ?_, fun x hx hg => ?_⟩` and prove the remaining obligations. Conclude with `(contDiffOn_partial_fderiv_fst hU hF v).mono Set.inter_subset_left`. Unfold `dirD`.

Rewrite using `[if_pos (show x.1 ∈ OmX r from hx.2), (slice_hasFDerivAt hU hF hΦF hx.1 hg).fderiv]`. Unfold `dirD`. Rewrite using `[if_pos hx.1, if_pos hx.1]`. Establish `he : (fun c' => Φ c' (h * x.2 * h')) =ᶠ[nhds x.1] fun c' => sandCLM (π h) (π' h') (Φ c' x.2)` using `by filter_upwards [(isOpen_OmX r).mem_nhds hx.1] with c' hc'`. Conclude with `hΦ.2.2 (c', x.2) ⟨hc', hx.2⟩ h hh h' hh'`.

Rewrite using `[he.fderiv_eq]`. Establish `hd` using `(slice_diff hΦ hx.1 x.2).hasFDerivAt`. Use `(((sandCLM (π h) (π' h')).restrictScalars ℝ).hasFDerivAt.comp x.1 hd).fderiv` as an intermediate fact. Establish `h2 : (fun c' => sandCLM (π h) (π' h') (Φ c' x.2)) = (⇑((sandCLM (π h) (π' h')).restrictScalars ℝ) ∘ fun c' => Φ c' x.2)` using `rfl`. Rewrite using `[h2, this]`.

Both sides reduce to the same expression.
-/
theorem dirD_mem (v : Fin r → ℂ) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    dirD v Φ ∈ RadSp k r z z' π π' := by
  refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
  · unfold dirD
    split_ifs with hc
    · have hg : ¬ (x.2 ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' x.2) := fun h => hx ⟨hc, h⟩
      rw [slice_zero hΦ hg]
      simp
    · rfl
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 x₀ hx₀
    refine ⟨U ∩ {x | x.1 ∈ OmX r}, fun x => partialFDerivFst F x v, hU.inter ((isOpen_OmX r).preimage continuous_fst),
      ⟨hxU, hx₀.1⟩, ?_, fun x hx hg => ?_⟩
    · exact (contDiffOn_partial_fderiv_fst hU hF v).mono Set.inter_subset_left
    · unfold dirD
      rw [if_pos (show x.1 ∈ OmX r from hx.2), (slice_hasFDerivAt hU hF hΦF hx.1 hg).fderiv]
  · unfold dirD
    rw [if_pos hx.1, if_pos hx.1]
    have he : (fun c' => Φ c' (h * x.2 * h')) =ᶠ[nhds x.1] fun c' => sandCLM (π h) (π' h') (Φ c' x.2) := by
      filter_upwards [(isOpen_OmX r).mem_nhds hx.1] with c' hc'
      exact hΦ.2.2 (c', x.2) ⟨hc', hx.2⟩ h hh h' hh'
    rw [he.fderiv_eq]
    have hd := (slice_diff hΦ hx.1 x.2).hasFDerivAt
    have := (((sandCLM (π h) (π' h')).restrictScalars ℝ).hasFDerivAt.comp x.1 hd).fderiv
    have h2 : (fun c' => sandCLM (π h) (π' h') (Φ c' x.2)) =
        (⇑((sandCLM (π h) (π' h')).restrictScalars ℝ) ∘ fun c' => Φ c' x.2) := rfl
    rw [h2, this]
    rfl

/- English proof (translation)
Use function extensionality and compare the values at `c g`. Simplify using `only [dirD, Pi.add_apply, Pi.smul_apply]`. Use `split_ifs with hc`. Establish `h1` using `(slice_diff hΦ hc g).hasFDerivAt`. Establish `h2` using `(slice_diff hΨ hc g).hasFDerivAt`.

Establish `h3` using `(h1.add (h2.const_smul s)).fderiv`. Establish `h4 : (fun c' => Φ c' g + s • Ψ c' g) = ((fun c' => Φ c' g) + s • fun c' => Ψ c' g)` using `rfl`. Rewrite using `[h4, h3]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem dirD_lin (v : Fin r → ℂ) {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π')
    (hΨ : Ψ ∈ RadSp k r z z' π π') (s : ℂ) : dirD v (Φ + s • Ψ) = dirD v Φ + s • dirD v Ψ := by
  funext c g
  simp only [dirD, Pi.add_apply, Pi.smul_apply]
  split_ifs with hc
  · have h1 := (slice_diff hΦ hc g).hasFDerivAt
    have h2 := (slice_diff hΨ hc g).hasFDerivAt
    have h3 := (h1.add (h2.const_smul s)).fderiv
    have h4 : (fun c' => Φ c' g + s • Ψ c' g) = ((fun c' => Φ c' g) + s • fun c' => Ψ c' g) := rfl
    rw [h4, h3]
    rfl
  · simp

/- English proof (translation)
Use `⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩` and prove the remaining obligations. Simplify using `[hΦ.1 x hx]`. Take `⟨U, F, hU, hxU, hF, hΦF⟩` from `hΦ.2.1 x₀ hx₀`. Use `⟨U ∩ OpR k r z z', fun x => a x • F x, hU.inter (isOpen_OpR k r z z'), ⟨hxU, DomR_sub_OpR hx₀⟩, (ha.mono Set.inter_subset_right).smul (hF.mono Set.inter_subset_left), fun x hx hg => ?_⟩` and prove the remaining obligations. Simplify using `[hΦF x hx.1 hg]`.

Simplify using `only`. Rewrite using `[hinv x hx h hh h' hh', hΦ.2.2 x hx h hh h' hh']`. Use extensionality with `w`. Simplify using the standard rewrite rules.
-/
theorem smul_mem {a : (Fin r → ℂ) × Mx k r → ℂ} (ha : ContDiffOn ℝ ∞ a (OpR k r z z'))
    (hinv : ∀ x ∈ DomR k r z z', ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', a (x.1, h * x.2 * h') = a x)
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    (fun c g => a (c, g) • Φ c g) ∈ RadSp k r z z' π π' := by
  refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
  · simp [hΦ.1 x hx]
  · obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 x₀ hx₀
    refine ⟨U ∩ OpR k r z z', fun x => a x • F x, hU.inter (isOpen_OpR k r z z'), ⟨hxU, DomR_sub_OpR hx₀⟩,
      (ha.mono Set.inter_subset_right).smul (hF.mono Set.inter_subset_left), fun x hx hg => ?_⟩
    simp [hΦF x hx.1 hg]
  · simp only
    rw [hinv x hx h hh h' hh', hΦ.2.2 x hx h hh h' hh']
    ext w
    simp

end Rad

section Rad2

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Establish `hg' : gᴴ * H * g = H` using `hg`. Unfold `herm`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']`.
-/
theorem herm_UH {ι : Type*} [Fintype ι] [DecidableEq ι] {H g : Matrix ι ι ℂ} (hg : g ∈ UH H) (x w : ι → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ w) = herm H x w := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

/- English proof (translation)
Simplify using `[fvec]`.
-/
theorem fvec_last (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

/- English proof (translation)
Establish `ha' : aᴴ * H * a = H` using `ha`. Establish `hb' : bᴴ * H * b = H` using `hb`. Express the relevant statement in the definitionally equal form `(a * b)ᴴ * H * (a * b) = H`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UH_mul {ι : Type*} [Fintype ι] [DecidableEq ι] {H a b : Matrix ι ι ℂ} (ha : a ∈ UH H) (hb : b ∈ UH H) :
    a * b ∈ UH H := by
  have ha' : aᴴ * H * a = H := ha
  have hb' : bᴴ * H * b = H := hb
  change (a * b)ᴴ * H * (a * b) = H
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * H * (a * b) = bᴴ * (aᴴ * H * a) * b := by simp only [Matrix.mul_assoc]
    _ = H := by rw [ha', hb']

/- English proof (translation)
Use `⟨UH_mul ha.1 hb.1, fun l hl => ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hb.2 l hl).1, (hb.2 l hl).2]`. Conclude with `ha.2 l hl`.
-/
theorem Glev_mul {i : Fin (r + 1)} {a b : Mx k r} (ha : a ∈ Glev k r i) (hb : b ∈ Glev k r i) :
    a * b ∈ Glev k r i := by
  refine ⟨UH_mul ha.1 hb.1, fun l hl => ?_⟩
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hb.2 l hl).1, (hb.2 l hl).2]
  exact ha.2 l hl

/- English proof (translation)
Assemble the required witnesses or components as `⟨hh.1, fun a _ => hh.2.1 a⟩`.
-/
theorem UW_Glev {h : Mx k r} (hh : h ∈ UWset k r z) (i : Fin (r + 1)) : h ∈ Glev k r i :=
  ⟨hh.1, fun a _ => hh.2.1 a⟩

/- English proof (translation)
Unfold `zetaL`. Rewrite using `[fvec_last, fvec_last, ← Matrix.mulVec_mulVec, hh'.2.2, ← Matrix.mulVec_mulVec]`. Use `conv_lhs => rw [← hh.2.2]`. Conclude with `herm_UH hh.1 _ _`.
-/
theorem zeta_inv {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (g : Mx k r) :
    zetaL k r z z' (Fin.last r) (h * g * h') = zetaL k r z z' (Fin.last r) g := by
  unfold zetaL
  rw [fvec_last, fvec_last, ← Matrix.mulVec_mulVec, hh'.2.2, ← Matrix.mulVec_mulVec]
  conv_lhs => rw [← hh.2.2]
  exact herm_UH hh.1 _ _

/- English proof (translation)
Unfold `GGl`. Rewrite using `[zeta_inv hh hh']`.
-/
theorem GG_inv {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (g : Mx k r) :
    GGl k r z z' (h * g * h') = GGl k r z z' g := by
  unfold GGl
  rw [zeta_inv hh hh']

/- English proof (translation)
Assemble the required witnesses or components as `⟨hx.1, Glev_mul (Glev_mul (UW_Glev hh _) hx.2.1) (UW_Glev hh' _), by change 0 < GGl k r z z' (h * x.2 * h'); rw [GG_inv hh hh']; exact hx.2.2⟩`.
-/
theorem DomR_inv {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') {x : (Fin r → ℂ) × Mx k r}
    (hx : x ∈ DomR k r z z') : (x.1, h * x.2 * h') ∈ DomR k r z z' :=
  ⟨hx.1, Glev_mul (Glev_mul (UW_Glev hh _) hx.2.1) (UW_Glev hh' _), by
    change 0 < GGl k r z z' (h * x.2 * h'); rw [GG_inv hh hh']; exact hx.2.2⟩

/- English proof (translation)
Introduce `h0`. Unfold `GGl at hg`. Rewrite `hg` using `[h0]`. Simplify using `at hg`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem zeta_ne (hT : 0 ≤ Tz k r z * Tz k r z') {g : Mx k r} (hg : 0 < GGl k r z z' g) :
    zetaL k r z z' (Fin.last r) g ≠ 0 := by
  intro h0
  unfold GGl at hg
  rw [h0] at hg
  simp at hg
  linarith

/- English proof (translation)
Use function extensionality and compare the values at `c g`. Simplify using `only [crd, pOp, wirt, dirD, Pi.smul_apply, Pi.sub_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem crd_p (l : Fin r) (Φ : Fn k r (Wq →L[ℂ] Wp)) :
    crd (pOp l) Φ = fun c g => c l • ((1 / 2 : ℂ) • (dirD (Pi.single l 1) Φ - Complex.I • dirD (Pi.single l Complex.I) Φ)) c g := by
  funext c g
  simp only [crd, pOp, wirt, dirD, Pi.smul_apply, Pi.sub_apply]
  split_ifs <;> simp

/- English proof (translation)
Use function extensionality and compare the values at `c g`. Simplify using `only [crd, pbOp, wirtBar, dirD, Pi.smul_apply, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem crd_pb (l : Fin r) (Φ : Fn k r (Wq →L[ℂ] Wp)) :
    crd (pbOp l) Φ = fun c g => star (c l) • ((1 / 2 : ℂ) • (dirD (Pi.single l 1) Φ + Complex.I • dirD (Pi.single l Complex.I) Φ)) c g := by
  funext c g
  simp only [crd, pbOp, wirtBar, dirD, Pi.smul_apply, Pi.add_apply]
  split_ifs <;> simp

/- English proof (translation)
The claim follows from `(contDiff_apply ℝ ℂ l).comp contDiff_fst`.
-/
theorem coord_contDiff (l : Fin r) : ContDiff ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => x.1 l) :=
  (contDiff_apply ℝ ℂ l).comp contDiff_fst

/- English proof (translation)
The claim follows from `Complex.conjCLE.contDiff.comp_contDiffOn hf`.
-/
theorem star_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {f : X → ℂ} {s : Set X}
    (hf : ContDiffOn ℝ ∞ f s) : ContDiffOn ℝ ∞ (fun x => star (f x)) s :=
  Complex.conjCLE.contDiff.comp_contDiffOn hf

/- English proof (translation)
Establish `h0 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => x.1 l) (OpR k r z z')` using `(coord_contDiff l).contDiffOn`. Establish `hne : ∀ x ∈ OpR k r z z', x.1 l ≠ 0` using `fun x hx => hx.1 l`. Use `⟨smul_mem (a := fun x => x.1 l) h0 (fun _ _ _ _ _ _ => rfl) hΦ, smul_mem (a := fun x => (x.1 l)⁻¹) (h0.inv hne) (fun _ _ _ _ _ _ => rfl) hΦ, smul_mem (a := fun x => star (x.1 l)) (star_contDiff h0) (fun _ _ _ _ _ _ => rfl) hΦ, smul_mem (a := fun x => (star (x.1 l))⁻¹) ((star_cont …` and prove the remaining obligations.
-/
theorem cmul_mem (l : Fin r) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    (fun c g => c l • Φ c g) ∈ RadSp k r z z' π π' ∧ (fun c g => (c l)⁻¹ • Φ c g) ∈ RadSp k r z z' π π' ∧
    (fun c g => star (c l) • Φ c g) ∈ RadSp k r z z' π π' ∧
    (fun c g => (star (c l))⁻¹ • Φ c g) ∈ RadSp k r z z' π π' := by
  have h0 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => x.1 l) (OpR k r z z') := (coord_contDiff l).contDiffOn
  have hne : ∀ x ∈ OpR k r z z', x.1 l ≠ 0 := fun x hx => hx.1 l
  refine ⟨smul_mem (a := fun x => x.1 l) h0 (fun _ _ _ _ _ _ => rfl) hΦ,
    smul_mem (a := fun x => (x.1 l)⁻¹) (h0.inv hne) (fun _ _ _ _ _ _ => rfl) hΦ,
    smul_mem (a := fun x => star (x.1 l)) (star_contDiff h0) (fun _ _ _ _ _ _ => rfl) hΦ,
    smul_mem (a := fun x => (star (x.1 l))⁻¹) ((star_contDiff h0).inv fun x hx => by simpa using hne x hx)
      (fun _ _ _ _ _ _ => rfl) hΦ⟩

/- English proof (translation)
Establish `h1 : dirD (Pi.single l 1) Φ ∈ RadSp k r z z' π π'` using `dirD_mem _ hΦ`. Establish `h2 : Complex.I • dirD (Pi.single l Complex.I) Φ ∈ RadSp k r z z' π π'` using `(RadSp k r z z' π π').smul_mem _ (dirD_mem _ hΦ)`. Use `fin_cases j`. Express the relevant statement in the definitionally equal form `crd (pOp l) Φ ∈ _`. Rewrite using `[crd_p]`.

Establish `h3 : (1 / 2 : ℂ) • (dirD (Pi.single l 1) Φ - Complex.I • dirD (Pi.single l Complex.I) Φ) ∈ RadSp k r z z' π π'` using `(RadSp k r z z' π π').smul_mem _ ((RadSp k r z z' π π').sub_mem h1 h2)`. Conclude with `(cmul_mem l h3).1`. Conclude with `(cmul_mem l hΦ).1`. Conclude with `(cmul_mem l hΦ).2.1`. Express the relevant statement in the definitionally equal form `crd (pbOp l) Φ ∈ _`.

Rewrite using `[crd_pb]`. Establish `h3 : (1 / 2 : ℂ) • (dirD (Pi.single l 1) Φ + Complex.I • dirD (Pi.single l Complex.I) Φ) ∈ RadSp k r z z' π π'` using `(RadSp k r z z' π π').smul_mem _ ((RadSp k r z z' π π').add_mem h1 h2)`. Conclude with `(cmul_mem l h3).2.2.1`. Conclude with `(cmul_mem l hΦ).2.2.1`. Conclude with `(cmul_mem l hΦ).2.2.2`.
-/
theorem crd_mem (l : Fin r) (j : Fin 6) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    crd (opL l j) Φ ∈ RadSp k r z z' π π' := by
  have h1 : dirD (Pi.single l 1) Φ ∈ RadSp k r z z' π π' := dirD_mem _ hΦ
  have h2 : Complex.I • dirD (Pi.single l Complex.I) Φ ∈ RadSp k r z z' π π' :=
    (RadSp k r z z' π π').smul_mem _ (dirD_mem _ hΦ)
  fin_cases j
  · change crd (pOp l) Φ ∈ _
    rw [crd_p]
    have h3 : (1 / 2 : ℂ) • (dirD (Pi.single l 1) Φ - Complex.I • dirD (Pi.single l Complex.I) Φ) ∈
        RadSp k r z z' π π' := (RadSp k r z z' π π').smul_mem _ ((RadSp k r z z' π π').sub_mem h1 h2)
    exact (cmul_mem l h3).1
  · exact (cmul_mem l hΦ).1
  · exact (cmul_mem l hΦ).2.1
  · change crd (pbOp l) Φ ∈ _
    rw [crd_pb]
    have h3 : (1 / 2 : ℂ) • (dirD (Pi.single l 1) Φ + Complex.I • dirD (Pi.single l Complex.I) Φ) ∈
        RadSp k r z z' π π' := (RadSp k r z z' π π').smul_mem _ ((RadSp k r z z' π π').add_mem h1 h2)
    exact (cmul_mem l h3).2.2.1
  · exact (cmul_mem l hΦ).2.2.1
  · exact (cmul_mem l hΦ).2.2.2

/- English proof (translation)
Use `fin_cases j`. Express the relevant statement in the definitionally equal form `crd (pOp l) _ = crd (pOp l) _ + s • crd (pOp l) _`. Rewrite using `[crd_p, crd_p, crd_p, dirD_lin _ hΦ hΨ, dirD_lin _ hΦ hΨ]`. Use function extensionality and compare the values at `c g`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_add, smul_sub, smul_smul]`.

Use `module`. Use function extensionality and compare the values at `c g`. Express the relevant statement in the definitionally equal form `c l • (Φ c g + s • Ψ c g) = c l • Φ c g + s • (c l • Ψ c g)`. Use `module`. Use function extensionality and compare the values at `c g`.

Express the relevant statement in the definitionally equal form `(c l)⁻¹ • (Φ c g + s • Ψ c g) = (c l)⁻¹ • Φ c g + s • ((c l)⁻¹ • Ψ c g)`. Use `module`. Express the relevant statement in the definitionally equal form `crd (pbOp l) _ = crd (pbOp l) _ + s • crd (pbOp l) _`. Rewrite using `[crd_pb, crd_pb, crd_pb, dirD_lin _ hΦ hΨ, dirD_lin _ hΦ hΨ]`. Use function extensionality and compare the values at `c g`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]`. Use `module`. Use function extensionality and compare the values at `c g`. Express the relevant statement in the definitionally equal form `star (c l) • (Φ c g + s • Ψ c g) = star (c l) • Φ c g + s • (star (c l) • Ψ c g)`. Use `module`.

Use function extensionality and compare the values at `c g`. Express the relevant statement in the definitionally equal form `(star (c l))⁻¹ • (Φ c g + s • Ψ c g) = (star (c l))⁻¹ • Φ c g + s • ((star (c l))⁻¹ • Ψ c g)`. Use `module`.
-/
theorem crd_lin (l : Fin r) (j : Fin 6) {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π')
    (hΨ : Ψ ∈ RadSp k r z z' π π') (s : ℂ) :
    crd (opL l j) (Φ + s • Ψ) = crd (opL l j) Φ + s • crd (opL l j) Ψ := by
  fin_cases j
  · change crd (pOp l) _ = crd (pOp l) _ + s • crd (pOp l) _
    rw [crd_p, crd_p, crd_p, dirD_lin _ hΦ hΨ, dirD_lin _ hΦ hΨ]
    funext c g
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_add, smul_sub, smul_smul]
    module
  · funext c g
    change c l • (Φ c g + s • Ψ c g) = c l • Φ c g + s • (c l • Ψ c g)
    module
  · funext c g
    change (c l)⁻¹ • (Φ c g + s • Ψ c g) = (c l)⁻¹ • Φ c g + s • ((c l)⁻¹ • Ψ c g)
    module
  · change crd (pbOp l) _ = crd (pbOp l) _ + s • crd (pbOp l) _
    rw [crd_pb, crd_pb, crd_pb, dirD_lin _ hΦ hΨ, dirD_lin _ hΦ hΨ]
    funext c g
    simp only [Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
    module
  · funext c g
    change star (c l) • (Φ c g + s • Ψ c g) = star (c l) • Φ c g + s • (star (c l) • Ψ c g)
    module
  · funext c g
    change (star (c l))⁻¹ • (Φ c g + s • Ψ c g) = (star (c l))⁻¹ • Φ c g + s • ((star (c l))⁻¹ • Ψ c g)
    module

/- English proof (translation)
Establish `h0 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => zetaL k r z z' (Fin.last r) x.2) (OpR k r z z')` using `((zetaL_contDiff k r z z' (Fin.last r)).comp contDiff_snd).contDiffOn`. Establish `hne : ∀ x ∈ OpR k r z z', zetaL k r z z' (Fin.last r) x.2 ≠ 0` using `fun x hx => zeta_ne hT hx.2`. Establish `h4 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => (GGl k r z z' x.2 : ℂ)) (OpR k r z z')`. Simplify using `only [GGl_cast]`. Conclude with `(h0.mul (star_contDiff h0)).sub contDiffOn_const`.

Use `fin_cases j`. Conclude with `h0`. Conclude with `h0.inv hne`. Conclude with `star_contDiff h0`. Conclude with `(star_contDiff h0).inv fun x hx => by simpa using hne x hx`.

Conclude with `h4`. Conclude with `h4.inv fun x hx => by`. Establish `: (0 : ℝ) < GGl k r z z' x.2` using `hx.2`. Conclude with `this.ne'` after adjusting the coercions.
-/
theorem fnVal_contDiffOn (hT : 0 ≤ Tz k r z * Tz k r z') (j : Fin 6) :
    ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => fnVal k r z z' j x.2) (OpR k r z z') := by
  have h0 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => zetaL k r z z' (Fin.last r) x.2) (OpR k r z z') :=
    ((zetaL_contDiff k r z z' (Fin.last r)).comp contDiff_snd).contDiffOn
  have hne : ∀ x ∈ OpR k r z z', zetaL k r z z' (Fin.last r) x.2 ≠ 0 := fun x hx => zeta_ne hT hx.2
  have h4 : ContDiffOn ℝ ∞ (fun x : (Fin r → ℂ) × Mx k r => (GGl k r z z' x.2 : ℂ)) (OpR k r z z') := by
    simp only [GGl_cast]
    exact (h0.mul (star_contDiff h0)).sub contDiffOn_const
  fin_cases j
  · exact h0
  · exact h0.inv hne
  · exact star_contDiff h0
  · exact (star_contDiff h0).inv fun x hx => by simpa using hne x hx
  · exact h4
  · exact h4.inv fun x hx => by
      have : (0 : ℝ) < GGl k r z z' x.2 := hx.2
      exact_mod_cast this.ne'

/- English proof (translation)
Apply the tactic sequence `fin_cases j <;> simp only [fnVal, zeta_inv hh hh', GG_inv hh hh']`.
-/
theorem fnVal_inv {h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') (j : Fin 6) (g : Mx k r) :
    fnVal k r z z' j (h * g * h') = fnVal k r z z' j g := by
  fin_cases j <;> simp only [fnVal, zeta_inv hh hh', GG_inv hh hh']

/- English proof (translation)
Use function extensionality and compare the values at `c g`. Distinguish the cases in `hx : (c, g) ∈ DomR k r z z'`. Rewrite using `[Set.indicator_of_mem hx]`. Rewrite using `[Set.indicator_of_notMem hx, hΦ.1 (c, g) hx, smul_zero]`.
-/
theorem fn_ind (j : Fin 6) {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    (fun c g => (DomR k r z z').indicator (fun x => fnVal k r z z' j x.2 • Φ x.1 x.2) (c, g)) =
      fun c g => fnVal k r z z' j g • Φ c g := by
  funext c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, hΦ.1 (c, g) hx, smul_zero]

/- English proof (translation)
The claim follows from `smul_mem (a := fun x => fnVal k r z z' j x.2) (fnVal_contDiffOn hT j) (fun _ _ _ hh _ hh' => fnVal_inv hh hh' j _) hΦ`.
-/
theorem fn_mem (hT : 0 ≤ Tz k r z * Tz k r z') (j : Fin 6) {Φ : Fn k r (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k r z z' π π') : (fun c g => fnVal k r z z' j g • Φ c g) ∈ RadSp k r z z' π π' :=
  smul_mem (a := fun x => fnVal k r z z' j x.2) (fnVal_contDiffOn hT j)
    (fun _ _ _ hh _ hh' => fnVal_inv hh hh' j _) hΦ

end Rad2

/- English proof (translation)
Take `⟨hOK, -, -, h1, h2, -, -⟩` from `h`. Rewrite using `[h1, h2]`. Conclude with `(mul_pos hOK.T_pos hOK.T'_pos).le`.
-/
theorem place_alt_alt {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
    {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} (h : IsPlace P z z' π π') : 0 ≤ Tz P.k P.r z * Tz P.k P.r z' := by
  obtain ⟨hOK, -, -, h1, h2, -, -⟩ := h
  rw [h1, h2]
  exact (mul_pos hOK.T_pos hOK.T'_pos).le

section Geo

/- English proof (translation)
Simplify using `[herm, bvec, dotProduct, Pi.single_apply]`.
-/
theorem herm_bvec_right {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ) (p : Fin m) :
    herm H v (bvec p) = (H *ᵥ v) p := by
  simp [herm, bvec, dotProduct, Pi.single_apply]

/- English proof (translation)
Simplify using `[mulVec, dotProduct, GBasic.Hpk_eq]`.
-/
theorem Hpk_mulVec (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) p = GBasic.sgn k r p * v (GBasic.sig k r p) := by
  simp [mulVec, dotProduct, GBasic.Hpk_eq]

/- English proof (translation)
Simplify using `[mulVec, dotProduct, bvec, Pi.single_apply]`.
-/
theorem mulVec_bvec {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (i j : Fin m) : (g *ᵥ bvec j) i = g i j := by
  simp [mulVec, dotProduct, bvec, Pi.single_apply]

/- English proof (translation)
Take `⟨⟨hU, -, h3⟩, -, hfix⟩` from `hn`. Use extensionality with `i j`. Distinguish the cases in `hj1 : j.val < r`. Establish `h` using `(hfix ⟨j.val, hj1⟩ (by simpa using hj1)).1`. Establish `e : eI k r ⟨j.val, hj1⟩ = j` using `Fin.ext rfl`.

Rewrite `h` using `[e]`. Use `congrFun h i` as an intermediate fact. Rewrite `this` using `[mulVec_bvec]`. Rewrite using `[this, Matrix.one_apply, bvec, Pi.single_apply]`. Distinguish the cases in `hj2 : r + k < j.val`.

Establish `hjl` using `j.isLt`. Establish `ha : 2 * r + k - j.val < r` using `by omega`. Establish `h` using `(hfix ⟨2 * r + k - j.val, ha⟩ (by simpa using ha)).2`. Establish `e : esI k r ⟨2 * r + k - j.val, ha⟩ = j` using `Fin.ext (by simp only [esI]; omega)`. Rewrite `h` using `[e]`.

Use `congrFun h i` as an intermediate fact. Rewrite `this` using `[mulVec_bvec]`. Rewrite using `[this, Matrix.one_apply, bvec, Pi.single_apply]`. Distinguish the cases in `hi : r ≤ i.val`. Rewrite using `[h3 i j (by omega) (by omega) hi, Matrix.one_apply]`.

Establish `hi' : i.val < r` using `by omega`. Establish `h` using `(hfix ⟨i.val, hi'⟩ (by simpa using hi')).2`. Establish `h1` using `herm_UH hU (bvec j) (bvec (esI k r ⟨i.val, hi'⟩))`. Rewrite `h1` using `[h, herm_bvec_right, herm_bvec_right, Hpk_mulVec, Hpk_mulVec]`. Establish `es : GBasic.sig k r (esI k r ⟨i.val, hi'⟩) = i`.

Apply `Fin.ext` to reduce the goal to its premises. Establish `hv : (esI k r ⟨i.val, hi'⟩).val = 2 * r + k - i.val` using `rfl`. Rewrite using `[GBasic.sig_hi k r _ (by rw [hv]; omega), hv]`. Use linear arithmetic over natural numbers and integers. Establish `sg : GBasic.sgn k r (esI k r ⟨i.val, hi'⟩) = 1`.

Establish `hv : (esI k r ⟨i.val, hi'⟩).val = 2 * r + k - i.val` using `rfl`. Unfold `GBasic.sgn`. Rewrite using `[if_neg (by rw [hv]; omega)]`. Rewrite `h1` using `[es, sg, one_mul, one_mul, mulVec_bvec]`. Rewrite using `[h1, Matrix.one_apply, bvec, Pi.single_apply]`.
-/
theorem Nlev_last {k r : ℕ} {n : Mx k r} (hn : n ∈ Nlev k r (Fin.last r)) : n = 1 := by
  obtain ⟨⟨hU, -, h3⟩, -, hfix⟩ := hn
  ext i j
  by_cases hj1 : j.val < r
  · have h := (hfix ⟨j.val, hj1⟩ (by simpa using hj1)).1
    have e : eI k r ⟨j.val, hj1⟩ = j := Fin.ext rfl
    rw [e] at h
    have := congrFun h i
    rw [mulVec_bvec] at this
    rw [this, Matrix.one_apply, bvec, Pi.single_apply]
  by_cases hj2 : r + k < j.val
  · have hjl := j.isLt
    have ha : 2 * r + k - j.val < r := by omega
    have h := (hfix ⟨2 * r + k - j.val, ha⟩ (by simpa using ha)).2
    have e : esI k r ⟨2 * r + k - j.val, ha⟩ = j := Fin.ext (by simp only [esI]; omega)
    rw [e] at h
    have := congrFun h i
    rw [mulVec_bvec] at this
    rw [this, Matrix.one_apply, bvec, Pi.single_apply]
  by_cases hi : r ≤ i.val
  · rw [h3 i j (by omega) (by omega) hi, Matrix.one_apply]
  · have hi' : i.val < r := by omega
    have h := (hfix ⟨i.val, hi'⟩ (by simpa using hi')).2
    have h1 := herm_UH hU (bvec j) (bvec (esI k r ⟨i.val, hi'⟩))
    rw [h, herm_bvec_right, herm_bvec_right, Hpk_mulVec, Hpk_mulVec] at h1
    have es : GBasic.sig k r (esI k r ⟨i.val, hi'⟩) = i := by
      apply Fin.ext
      have hv : (esI k r ⟨i.val, hi'⟩).val = 2 * r + k - i.val := rfl
      rw [GBasic.sig_hi k r _ (by rw [hv]; omega), hv]
      omega
    have sg : GBasic.sgn k r (esI k r ⟨i.val, hi'⟩) = 1 := by
      have hv : (esI k r ⟨i.val, hi'⟩).val = 2 * r + k - i.val := rfl
      unfold GBasic.sgn
      rw [if_neg (by rw [hv]; omega)]
    rw [es, sg, one_mul, one_mul, mulVec_bvec] at h1
    rw [h1, Matrix.one_apply, bvec, Pi.single_apply]

/- English proof (translation)
Establish `: ell k r z 1 = 0`. Unfold `ell`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `a _`. Use `split_ifs with h`.

Rewrite using `[Matrix.one_apply, if_neg]`. Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Simplify using `[eI] at this`. Rewrite using `[Matrix.one_mulVec]`.

Conclude with `hz _ (Or.inl a.isLt)`. Unfold `psi`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem psi_one {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : ℂ) : psi k r z c 1 = 1 := by
  have : ell k r z 1 = 0 := by
    unfold ell
    apply Finset.sum_eq_zero
    intro a _
    split_ifs with h
    · rw [Matrix.one_apply, if_neg]
      intro e
      have := congrArg Fin.val e
      simp [eI] at this
    · rw [Matrix.one_mulVec]
      exact hz _ (Or.inl a.isLt)
  unfold psi
  rw [this]
  simp

def Dp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Mx k r) := {g | 0 < GGl k r z z' g}

/- English proof (translation)
The claim follows from `isOpen_lt continuous_const (GGl_continuous k r z z')`.
-/
theorem Dp_open (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsOpen (Dp k r z z') :=
  isOpen_lt continuous_const (GGl_continuous k r z z')

/- English proof (translation)
Take `⟨h, hh, m, hm, rfl⟩` from `hs`. Rewrite using `[Nlev_last hm, mul_one]`. Conclude with `hh`.
-/
theorem Slev_last {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {s : Mx k r} (hs : s ∈ Slev k r z (Fin.last r)) :
    s ∈ UWset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  rw [Nlev_last hm, mul_one]
  exact hh

/- English proof (translation)
Use `⟨Dp_open k r z z', ?_⟩` and prove the remaining obligations. Introduce and unpack `g ⟨-, hg⟩ s hs s' hs'`. Use `show 0 < GGl k r z z' (s * g * s')`. Rewrite using `[GG_inv (Slev_last hs) (Slev_last hs')]`. Conclude with `hg`.
-/
theorem Dp_dom (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : IsDom k r z z' (Fin.last r) (Dp k r z z') := by
  refine ⟨Dp_open k r z z', ?_⟩
  rintro g ⟨-, hg⟩ s hs s' hs'
  show 0 < GGl k r z z' (s * g * s')
  rw [GG_inv (Slev_last hs) (Slev_last hs')]
  exact hg

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

/- English proof (translation)
Introduce and unpack `g₀ ⟨hg, hD⟩`. Take `⟨U, F, hU, hx, hF, hΦF⟩` from `hΦ.2.1 (c, g₀) ⟨hc, hg, hD⟩`. Use `⟨(fun g => (c, g)) ⁻¹' U, fun g => F (c, g), hU.preimage (by fun_prop), hx, ?_, fun g hg hgl => hΦF (c, g) hg hgl⟩` and prove the remaining obligations. Conclude with `hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun g hg => hg)`.
-/
theorem slice_smooth {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) :
    SmoothLev k r (Fin.last r) (Dp k r z z') (Φ c) := by
  rintro g₀ ⟨hg, hD⟩
  obtain ⟨U, F, hU, hx, hF, hΦF⟩ := hΦ.2.1 (c, g₀) ⟨hc, hg, hD⟩
  refine ⟨(fun g => (c, g)) ⁻¹' U, fun g => F (c, g), hU.preimage (by fun_prop), hx, ?_,
    fun g hg hgl => hΦF (c, g) hg hgl⟩
  exact hF.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun g hg => hg)

/- English proof (translation)
Use `⟨slice_smooth hΦ hc, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g _ n hn`. Rewrite using `[Nlev_last hn, one_mul, psi_one hz, one_smul]`. Introduce `g _ n hn`. Rewrite using `[Nlev_last hn, mul_one, psi_one hz', one_smul]`.

Introduce and unpack `g ⟨hg, hD⟩ h hh h' hh'`. Conclude with `hΦ.2.2 (c, g) ⟨hc, hg, hD⟩ h hh h' hh'`.
-/
theorem slice_FF (hz : inWb k r z) (hz' : inWb k r z') {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π')
    {c : Fin r → ℂ} (hc : c ∈ OmX r) : Φ c ∈ FFl k r z z' π π' (Fin.last r) (Dp k r z z') := by
  refine ⟨slice_smooth hΦ hc, ?_, ?_, ?_⟩
  · intro g _ n hn
    rw [Nlev_last hn, one_mul, psi_one hz, one_smul]
  · intro g _ n hn
    rw [Nlev_last hn, mul_one, psi_one hz', one_smul]
  · rintro g ⟨hg, hD⟩ h hh h' hh'
    exact hΦ.2.2 (c, g) ⟨hc, hg, hD⟩ h hh h' hh'

end Geo

section Exist

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def tFun (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (a b : Fin 2) (Φ : Fn k r (Wq →L[ℂ] Wp)) :
    Fn k r (Wq →L[ℂ] Wp) :=
  fun c g => (DomR k r z z').indicator (fun x => tL k r z z' (Fin.last r) Y a b (Φ x.1) x.2) (c, g)

/- English proof (translation)
Use `⟨fun x hx => Set.indicator_of_notMem hx _, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩` and prove the remaining obligations. Establish `hS : SmoothFam k r (Fin.last r) (OpR k r z z') Φ` using `fun x hx hg => hΦ.2.1 x (mem_DomR_of_OpR hx hg)`. Take `⟨U, F, hU, hxU, hF, hE⟩` from `hJS _ k r z z' (Fin.last r) (OpR k r z z') Φ Y a b (isOpen_OpR k r z z') hS x₀ (DomR_sub_OpR hx₀) hx₀.2.1`. Use `⟨U ∩ OpR k r z z', F, hU.inter (isOpen_OpR k r z z'), ⟨hxU, DomR_sub_OpR hx₀⟩, hF.mono Set.inter_subset_left, fun x hx hg => ?_⟩` and prove the remaining obligations. Rewrite using `[← hE x hx.1 hg]`.

Conclude with `Set.indicator_of_mem (mem_DomR_of_OpR hx.2 hg) _`. Establish `h1` using `hTP Wp Wq k r z z' π π' (Fin.last r) (Dp k r z z') Y a b hz hz' (Dp_dom k r z z') _ (slice_FF hz hz' hΦ hx.1)`. Establish `h2` using `h1.2.2.2 x.2 ⟨hx.2.1, hx.2.2⟩ h hh h' hh'`. Unfold `tFun`. Rewrite using `[Set.indicator_of_mem (DomR_inv hh hh' hx), Set.indicator_of_mem (show (x.1, x.2) ∈ DomR k r z z' from hx)]`.

Conclude with `h2`.
-/
theorem tFun_mem (hTP : TPreservesFF) (hJS : TJointSmooth) (hz : inWb k r z) (hz' : inWb k r z') (Y : ℂ) (a b : Fin 2)
    {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') : tFun k r z z' Y a b Φ ∈ RadSp k r z z' π π' := by
  refine ⟨fun x hx => Set.indicator_of_notMem hx _, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
  · have hS : SmoothFam k r (Fin.last r) (OpR k r z z') Φ := fun x hx hg => hΦ.2.1 x (mem_DomR_of_OpR hx hg)
    obtain ⟨U, F, hU, hxU, hF, hE⟩ := hJS _ k r z z' (Fin.last r) (OpR k r z z') Φ Y a b (isOpen_OpR k r z z') hS
      x₀ (DomR_sub_OpR hx₀) hx₀.2.1
    refine ⟨U ∩ OpR k r z z', F, hU.inter (isOpen_OpR k r z z'), ⟨hxU, DomR_sub_OpR hx₀⟩,
      hF.mono Set.inter_subset_left, fun x hx hg => ?_⟩
    rw [← hE x hx.1 hg]
    exact Set.indicator_of_mem (mem_DomR_of_OpR hx.2 hg) _
  · have h1 := hTP Wp Wq k r z z' π π' (Fin.last r) (Dp k r z z') Y a b hz hz' (Dp_dom k r z z') _
      (slice_FF hz hz' hΦ hx.1)
    have h2 := h1.2.2.2 x.2 ⟨hx.2.1, hx.2.2⟩ h hh h' hh'
    unfold tFun
    rw [Set.indicator_of_mem (DomR_inv hh hh' hx), Set.indicator_of_mem (show (x.1, x.2) ∈ DomR k r z z' from hx)]
    exact h2

/- English proof (translation)
Use function extensionality and compare the values at `c g`. Distinguish the cases in `hx : (c, g) ∈ DomR k r z z'`. Simplify using `only [tFun, Pi.add_apply, Pi.smul_apply]`. Rewrite using `[Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]`. Conclude with `(hLL _ k r z z' (Fin.last r) (Dp k r z z') Y a b (Φ c) (Ψ c) s (Dp_open k r z z') (slice_smooth hΦ hx.1) (slice_smooth hΨ hx.1) g ⟨hx.2.1, hx.2.2⟩).1`.

Simplify using `only [tFun, Pi.add_apply, Pi.smul_apply]`. Rewrite using `[Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]`. Simplify using the standard rewrite rules.
-/
theorem tFun_lin (hLL : TLinLoc) (Y : ℂ) (a b : Fin 2) {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)}
    (hΦ : Φ ∈ RadSp k r z z' π π') (hΨ : Ψ ∈ RadSp k r z z' π π') (s : ℂ) :
    tFun k r z z' Y a b (Φ + s • Ψ) = tFun k r z z' Y a b Φ + s • tFun k r z z' Y a b Ψ := by
  funext c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · simp only [tFun, Pi.add_apply, Pi.smul_apply]
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    exact (hLL _ k r z z' (Fin.last r) (Dp k r z z') Y a b (Φ c) (Ψ c) s (Dp_open k r z z') (slice_smooth hΦ hx.1)
      (slice_smooth hΨ hx.1) g ⟨hx.2.1, hx.2.2⟩).1
  · simp only [tFun, Pi.add_apply, Pi.smul_apply]
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

def mkEnd {V : Type*} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (T : V → V) (hm : ∀ x ∈ S, T x ∈ S)
    (hl : ∀ x ∈ S, ∀ y ∈ S, ∀ s : ℂ, T (x + s • y) = T x + s • T y) : Module.End ℂ S where
  toFun x := ⟨T x, hm x x.2⟩
  map_add' x y := by
    apply Subtype.ext
    have := hl x x.2 y y.2 1
    simpa using this
  map_smul' s x := by
    apply Subtype.ext
    have h0 : T 0 = 0 := by
      have := hl 0 S.zero_mem 0 S.zero_mem 1
      simpa using this
    have := hl 0 S.zero_mem x x.2 s
    simpa [h0] using this

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mkEnd_apply {V : Type*} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) (T : V → V) (hm : ∀ x ∈ S, T x ∈ S)
    (hl : ∀ x ∈ S, ∀ y ∈ S, ∀ s : ℂ, T (x + s • y) = T x + s • T y) (x : S) : (mkEnd S T hm hl x : V) = T x := rfl

def actualOps (hTP : TPreservesFF) (hLL : TLinLoc) (hJS : TJointSmooth) (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 ≤ Tz k r z * Tz k r z') : ActualOps k r z z' π π' where
  t Y a b := mkEnd (RadSp k r z z' π π') (tFun k r z z' Y a b) (fun _ h => tFun_mem hTP hJS hz hz' Y a b h)
    (fun _ hx _ hy s => tFun_lin hLL Y a b hx hy s)
  op l j := mkEnd (RadSp k r z z' π π') (crd (opL l j)) (fun _ h => crd_mem l j h)
    (fun _ hx _ hy s => crd_lin l j hx hy s)
  fn j := mkEnd (RadSp k r z z' π π') (fun Φ c g => fnVal k r z z' j g • Φ c g) (fun _ h => fn_mem hT j h)
    (fun x _ y _ s => by
      funext c g
      simp only [Pi.add_apply, Pi.smul_apply]
      module)
  t_apply Y a b Φ x hx := by
    rw [mkEnd_apply]
    exact Set.indicator_of_mem (show (x.1, x.2) ∈ DomR k r z z' from hx) _
  op_apply l j Φ := rfl
  fn_apply j Φ x hx := rfl

end Exist

section Nat

open Qx2

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
  {i : Fin (r + 1)} {D : Set (Mx k r)}

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g₀ hg₀`. Use `⟨U, fun x => φ (F x), hU, hgU, (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, fun x hx hxG => ?_⟩` and prove the remaining obligations. Use `show φ (f x) = φ (F x)`. Rewrite using `[he x hx hxG]`.
-/
theorem smooth_clm (φ : E →L[ℂ] E') {f : Mx k r → E} (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (fun x => φ (f x)) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  refine ⟨U, fun x => φ (F x), hU, hgU, (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF, fun x hx hxG => ?_⟩
  show φ (f x) = φ (F x)
  rw [he x hx hxG]

def Ntw (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (φ : E →L[ℂ] E') (T : (Mx k r → E) → Mx k r → E)
    (T' : (Mx k r → E') → Mx k r → E') : Prop :=
  ∀ f, SmoothLev k r i D f → ∀ x ∈ Glev k r i ∩ D, T' (fun y => φ (f y)) x = φ (T f x)

/- English proof (translation)
Introduce `_ hf _ hx` and use `((φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (rd_hasDeriv hf hx hX)).deriv`.
-/
theorem ntw_rd (φ : E →L[ℂ] E') {X : Mx k r} (hX : inLieLev k r i X) :
    Ntw k r i D φ (fun f => RdV X f) (fun f => RdV X f) := fun _ hf _ hx =>
  ((φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (rd_hasDeriv hf hx hX)).deriv

/- English proof (translation)
Introduce `f hf x hx`. Use `show RdV _ _ x + Complex.I • RdV _ _ x = φ (RdV _ f x + Complex.I • RdV _ f x)`. Establish `e1 : RdV (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) (fun y => φ (f y)) x = φ (RdV _ f x)` using `ntw_rd φ (hpart_lev i a b).1 f hf x hx`. Establish `e2 : RdV (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) (fun y => φ (f y)) x = φ (RdV _ f x)` using `ntw_rd φ (hpart_lev i a b).2 f hf x hx`. Rewrite using `[e1, e2, map_add, map_smul]`.
-/
theorem ntw_eh (φ : E →L[ℂ] E') (a b : Fin (mdim k r i)) :
    Ntw k r i D φ (fun f => EH k r (posL k r i a) (posL k r i b) f)
      (fun f => EH k r (posL k r i a) (posL k r i b) f) := by
  intro f hf x hx
  show RdV _ _ x + Complex.I • RdV _ _ x = φ (RdV _ f x + Complex.I • RdV _ f x)
  have e1 : RdV (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) (fun y => φ (f y)) x = φ (RdV _ f x) :=
    ntw_rd φ (hpart_lev i a b).1 f hf x hx
  have e2 : RdV (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) (fun y => φ (f y)) x = φ (RdV _ f x) :=
    ntw_rd φ (hpart_lev i a b).2 f hf x hx
  rw [e1, e2, map_add, map_smul]

/- English proof (translation)
Introduce `f hf x hx`. Simplify using `only [QuantumDeterminants.Top]`. Establish `e1 : EH k r (posL k r i a) (posL k r i b) (fun y => φ (f y)) x = φ (EH k r (posL k r i a) (posL k r i b) f x)` using `ntw_eh φ a b f hf x hx`. Rewrite using `[e1, map_add]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ntw_top (φ : E →L[ℂ] E') (u : ℂ) (a b : Fin (mdim k r i)) :
    Ntw k r i D φ (fun f => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f)
      (fun f => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f) := by
  intro f hf x hx
  simp only [QuantumDeterminants.Top]
  have e1 : EH k r (posL k r i a) (posL k r i b) (fun y => φ (f y)) x = φ (EH k r (posL k r i a) (posL k r i b) f x) :=
    ntw_eh φ a b f hf x hx
  rw [e1, map_add]
  split_ifs <;> simp

/- English proof (translation)
Introduce `f hf x hx`. Use `show T' (S' fun y => φ (f y)) x = φ (T (S f) x)`. Rewrite using `[hT'g.loc _ (fun y => φ (S f y)) (hS f hf) x hx]`. Conclude with `hT _ (hSg.sm _ hf) x hx`.
-/
theorem Ntw.comp {φ : E →L[ℂ] E'} {T S : (Mx k r → E) → Mx k r → E} {T' S' : (Mx k r → E') → Mx k r → E'}
    (hT : Ntw k r i D φ T T') (hS : Ntw k r i D φ S S') (hSg : Good k r i D S) (hT'g : Good k r i D T') :
    Ntw k r i D φ (fun f => T (S f)) (fun f => T' (S' f)) := by
  intro f hf x hx
  show T' (S' fun y => φ (f y)) x = φ (T (S f) x)
  rw [hT'g.loc _ (fun y => φ (S f y)) (hS f hf) x hx]
  exact hT _ (hSg.sm _ hf) x hx

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact fun _ _ _ _ => rfl`. Consider the case `cons p L ih`. Simplify using `only [List.map_cons, List.foldr_cons]`. Use `Ntw.comp (ntw_top φ p.1 p.2.1 p.2.2) ih (good_foldr _ ?_) (good_top hD _ _ _)` and prove the remaining obligations.

Introduce `T hT`. Take `⟨q, -, rfl⟩` from `List.mem_map.1 hT`. Conclude with `good_top hD _ _ _`.
-/
theorem ntw_foldr (hD : IsOpen D) (φ : E →L[ℂ] E') (L : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) :
    Ntw k r i D φ
      (fun f => (L.map fun p => QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T h => T h) f)
      (fun f => (L.map fun p => QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact fun _ _ _ _ => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.foldr_cons]
    refine Ntw.comp (ntw_top φ p.1 p.2.1 p.2.2) ih (good_foldr _ ?_) (good_top hD _ _ _)
    intro T hT
    obtain ⟨q, -, rfl⟩ := List.mem_map.1 hT
    exact good_top hD _ _ _

/- English proof (translation)
Introduce `f hf x hx`. Simplify using `only [qminorOp, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `h` using `ntw_foldr hD φ (List.ofFn fun l : Fin t => ((u - ((l : ℕ) : ℂ), a (σ l), b l) : ℂ × Fin (mdim k r i) × Fin (mdim k r i))) f hf x hx`.

Simplify using `only [List.map_ofFn] at h`. Conclude with `h`.
-/
theorem ntw_qminor (hD : IsOpen D) (φ : E →L[ℂ] E') {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    Ntw k r i D φ (fun f => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u f)
      (fun f => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u f) := by
  intro f hf x hx
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have h := ntw_foldr hD φ (List.ofFn fun l : Fin t => ((u - ((l : ℕ) : ℂ), a (σ l), b l) :
    ℂ × Fin (mdim k r i) × Fin (mdim k r i))) f hf x hx
  simp only [List.map_ofFn] at h
  exact h

/- English proof (translation)
Introduce `f hf x hx`. Apply the tactic sequence `fin_cases p <;> fin_cases q`. Conclude with `ntw_qminor hD φ id id _ f hf x hx`. Use `show -(chatL _ _ _ _ _ _ x) = φ (-(chatL _ _ _ _ _ f x))`. Simplify using `only [chatL, map_neg, map_sum, map_smul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun j₁ _ => ?_` and prove the remaining obligations. Conclude with `congrArg _ (ntw_qminor hD φ (skip1 i₁) (skip1 j₁) _ f hf x hx)`. Use `show -(chatL _ _ _ _ _ _ x) = φ (-(chatL _ _ _ _ _ f x))`. Simplify using `only [chatL, map_neg, map_sum, map_smul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun j₁ _ => ?_` and prove the remaining obligations. Conclude with `congrArg _ (ntw_qminor hD φ (skip1 i₁) (skip1 j₁) _ f hf x hx)`. Use `show -(chat2L _ _ _ _ _ _ _ _ x) = φ (-(chat2L _ _ _ _ _ _ _ f x))`. Simplify using `only [chat2L, map_neg, map_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[map_smul]`. Conclude with `congrArg _ (ntw_qminor hD φ (skip2 i₁ i₂) (skip2 j₁ j₂) _ f hf x hx)`.

Simplify using the standard rewrite rules.
-/
theorem ntw_tL (hD : IsOpen D) (φ : E →L[ℂ] E') (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    Ntw k r i D φ (fun f => tL k r z z' i Y p q f) (fun f => tL k r z z' i Y p q f) := by
  intro f hf x hx
  fin_cases p <;> fin_cases q
  · exact ntw_qminor hD φ id id _ f hf x hx
  · show -(chatL _ _ _ _ _ _ x) = φ (-(chatL _ _ _ _ _ f x))
    simp only [chatL, map_neg, map_sum, map_smul]
    congr 1
    refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun j₁ _ => ?_
    exact congrArg _ (ntw_qminor hD φ (skip1 i₁) (skip1 j₁) _ f hf x hx)
  · show -(chatL _ _ _ _ _ _ x) = φ (-(chatL _ _ _ _ _ f x))
    simp only [chatL, map_neg, map_sum, map_smul]
    congr 1
    refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun j₁ _ => ?_
    exact congrArg _ (ntw_qminor hD φ (skip1 i₁) (skip1 j₁) _ f hf x hx)
  · show -(chat2L _ _ _ _ _ _ _ _ x) = φ (-(chat2L _ _ _ _ _ _ _ f x))
    simp only [chat2L, map_neg, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i₁ _ => Finset.sum_congr rfl fun i₂ _ => Finset.sum_congr rfl fun j₁ _ =>
      Finset.sum_congr rfl fun j₂ _ => ?_
    split_ifs
    · rw [map_smul]
      exact congrArg _ (ntw_qminor hD φ (skip2 i₁ i₂) (skip2 j₁ j₂) _ f hf x hx)
    · simp

end Nat

section Adj

open Qx2

variable {k r : ℕ}

/- English proof (translation)
Establish `h : Glev k r i = UH (Hpk k r) ∩ ⋂ a : Fin r, {g : Mx k r | a.val < i.val → g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)}`. Use extensionality with `g`. Simplify using `[Glev]`. Rewrite using `[h]`. Use `IsClosed.inter B5.GV_closed (isClosed_iInter fun a => ?_)` and prove the remaining obligations.

Distinguish the cases in `ha : a.val < i.val`. Establish `: {g : Mx k r | a.val < i.val → g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} = {g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩ {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)}`. Use extensionality with `g`. Simplify using `[ha]`. Rewrite using `[this]`.

Conclude with `(isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)`. Establish `: {g : Mx k r | a.val < i.val → g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} = Set.univ`. Use extensionality with `g`. Simplify using `[ha]`. Rewrite using `[this]`.

Conclude with `isClosed_univ`.
-/
theorem Glev_closed (i : Fin (r + 1)) : IsClosed (Glev k r i) := by
  have h : Glev k r i = UH (Hpk k r) ∩ ⋂ a : Fin r, {g : Mx k r | a.val < i.val →
      g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
    ext g
    simp [Glev]
  rw [h]
  refine IsClosed.inter B5.GV_closed (isClosed_iInter fun a => ?_)
  by_cases ha : a.val < i.val
  · have : {g : Mx k r | a.val < i.val →
        g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} =
        {g : Mx k r | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩ {g : Mx k r | g *ᵥ bvec (esI k r a) = bvec (esI k r a)} := by
      ext g
      simp [ha]
    rw [this]
    exact (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter
      (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)
  · have : {g : Mx k r | a.val < i.val →
        g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)} = Set.univ := by
      ext g
      simp [ha]
    rw [this]
    exact isClosed_univ

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, he⟩` from `h g₀ hg₀`. Establish `h1 : ContinuousWithinAt F (Glev k r i ∩ D) g₀` using `(hF.continuousOn.continuousAt (hU.mem_nhds hgU)).continuousWithinAt`. Use `h1.congr_of_eventuallyEq ?_ (he g₀ hgU hg₀.1)` and prove the remaining obligations. Use `filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g a b`.

Conclude with `he g a b.1`.
-/
theorem smoothLev_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
    {D : Set (Mx k r)} {f : Mx k r → E} (h : SmoothLev k r i D f) : ContinuousOn f (Glev k r i ∩ D) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := h g₀ hg₀
  have h1 : ContinuousWithinAt F (Glev k r i ∩ D) g₀ :=
    (hF.continuousOn.continuousAt (hU.mem_nhds hgU)).continuousWithinAt
  refine h1.congr_of_eventuallyEq ?_ (he g₀ hgU hg₀.1)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g a b
  exact he g a b.1

/- English proof (translation)
Establish `: IsFiniteMeasureOnCompacts μ` using `⟨fun K hK => hμ.finite_compact K hK⟩`. Establish `hS : IsCompact (Glev k r i ∩ K)` using `hK.inter_left (Glev_closed i)`. Establish `hS' : IsCompact ({x : Mt k r | (Matrix.of x : Mx k r) ∈ Glev k r i ∩ K})` using `hS`. Establish `hc : ContinuousOn (fun x : Mt k r => p (Matrix.of x)) {x : Mt k r | (Matrix.of x : Mx k r) ∈ Glev k r i ∩ K}` using `hp.mono fun x hx => ⟨hx.1, hKD hx.2⟩`. Establish `hi` using `hc.integrableOn_compact (μ := μ) hS'`.

Use `hi.integrable_of_ae_notMem_eq_zero ?_` and prove the remaining obligations. Use `filter_upwards [B5.haar_ae hμ] with x hx hxS`. Conclude with `h0 _ hx fun hxK => hxS ⟨hx, hxK⟩`.
-/
theorem integrable_cpt {i : Fin (r + 1)} {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r i) μ) {D K : Set (Mx k r)}
    {p : Mx k r → ℂ} (hK : IsCompact K) (hKD : K ⊆ D) (hp : ContinuousOn p (Glev k r i ∩ D))
    (h0 : ∀ g ∈ Glev k r i, g ∉ K → p g = 0) : Integrable (fun x : Mt k r => p (Matrix.of x)) μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hμ.finite_compact K hK⟩
  have hS : IsCompact (Glev k r i ∩ K) := hK.inter_left (Glev_closed i)
  have hS' : IsCompact ({x : Mt k r | (Matrix.of x : Mx k r) ∈ Glev k r i ∩ K}) := hS
  have hc : ContinuousOn (fun x : Mt k r => p (Matrix.of x)) {x : Mt k r | (Matrix.of x : Mx k r) ∈ Glev k r i ∩ K} :=
    hp.mono fun x hx => ⟨hx.1, hKD hx.2⟩
  have hi := hc.integrableOn_compact (μ := μ) hS'
  refine hi.integrable_of_ae_notMem_eq_zero ?_
  filter_upwards [B5.haar_ae hμ] with x hx hxS
  exact h0 _ hx fun hxK => hxS ⟨hx, hxK⟩

variable {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def coefL (e : Wp) (v : Wq) : (Wq →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ e).comp (ContinuousLinearMap.apply ℂ Wp v)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coefL_apply (e : Wp) (v : Wq) (T : Wq →L[ℂ] Wp) : coefL e v T = ⟪e, T v⟫_ℂ := rfl

/- English proof (translation)
Rewrite using `[← (stdOrthonormalBasis ℂ Wp).sum_inner_mul_inner (S v) (T v)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[coefL_apply, coefL_apply, mul_comm, Complex.star_def, inner_conj_symm]`.
-/
theorem inner_coef [FiniteDimensional ℂ Wp] (v : Wq) (S T : Wq →L[ℂ] Wp) :
    ⟪S v, T v⟫_ℂ = ∑ j, coefL (stdOrthonormalBasis ℂ Wp j) v T * star (coefL (stdOrthonormalBasis ℂ Wp j) v S) := by
  rw [← (stdOrthonormalBasis ℂ Wp).sum_inner_mul_inner (S v) (T v)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coefL_apply, coefL_apply, mul_comm, Complex.star_def, inner_conj_symm]

/- English proof (translation)
Introduce `g₀ hg₀`. Distinguish the cases in `hgK : g₀ ∈ K`. Conclude with `slice_smooth hΦ hc g₀ ⟨hg₀.1, hKD hgK⟩`. Conclude with `⟨Kᶜ, fun _ => 0, hK.isClosed.isOpen_compl, hgK, contDiffOn_const, fun g hg hgl => h0 g hgl hg⟩`.
-/
theorem smooth_univ {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r)
    {K : Set (Mx k r)} (hK : IsCompact K) (hKD : K ⊆ Dp k r z z')
    (h0 : ∀ g ∈ Glev k r (Fin.last r), g ∉ K → Φ c g = 0) : SmoothLev k r (Fin.last r) Set.univ (Φ c) := by
  intro g₀ hg₀
  by_cases hgK : g₀ ∈ K
  · exact slice_smooth hΦ hc g₀ ⟨hg₀.1, hKD hgK⟩
  · exact ⟨Kᶜ, fun _ => 0, hK.isClosed.isOpen_compl, hgK, contDiffOn_const, fun g hg hgl => h0 g hgl hg⟩

/- English proof (translation)
Distinguish the cases in `hx : (c, x) ∈ DomR k r z z'`. Establish `e1` using `X.t_apply Y a b Φ (c, x) hx`. Establish `e2 : tL k r z z' (Fin.last r) Y a b (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)) x = φ (tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) x)` using `ntw_tL (Dp_open k r z z') φ z z' Y a b _ (slice_smooth Φ.2 hc) x ⟨hx.2.1, hx.2.2⟩`. Rewrite using `[e2, ← e1]`. Rewrite using `[Ψ.2.1 (c, x) hx, map_zero, zero_mul, zero_mul]`.
-/
theorem key_pt (X : ActualOps k r z z' π π') (Φ Ψ : RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) (Y : ℂ)
    (a b : Fin 2) (φ : (Wq →L[ℂ] Wp) →L[ℂ] ℂ) (x : Mx k r) :
    φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c x)) =
      φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) *
        star (tL k r z z' (Fin.last r) Y a b (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)) x) := by
  by_cases hx : (c, x) ∈ DomR k r z z'
  · have e1 := X.t_apply Y a b Φ (c, x) hx
    have e2 : tL k r z z' (Fin.last r) Y a b (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)) x =
        φ (tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c) x) :=
      ntw_tL (Dp_open k r z z') φ z z' Y a b _ (slice_smooth Φ.2 hc) x ⟨hx.2.1, hx.2.2⟩
    rw [e2, ← e1]
  · rw [Ψ.2.1 (c, x) hx, map_zero, zero_mul, zero_mul]

/- English proof (translation)
Establish `c1` using `smoothLev_continuousOn (smooth_clm φ (slice_smooth Φ.2 hc))`. Establish `c2` using `smoothLev_continuousOn (smooth_clm φ (slice_smooth Ψ.2 hc))`. Prove the components needed by the constructor for the conclusion. Use `integrable_cpt hμ (p := fun x => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x))) hK hKD (c2.mul (continuous_star.comp_continuousOn c1)) ?_` and prove the remaining obligations. Introduce `g hg hgK`.

Simplify using `[h0 g hg hgK]`. Use `integrable_cpt hμ (p := fun x => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x) * star (φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x))) hK hKD (c1.mul (continuous_star.comp_continuousOn c2)) ?_` and prove the remaining obligations. Introduce `g hg hgK`. Simplify using `[h0 g hg hgK]`.
-/
theorem integrable_pair {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Ψ : RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) {K : Set (Mx k r)} (hK : IsCompact K)
    (hKD : K ⊆ Dp k r z z') (h0 : ∀ g ∈ Glev k r (Fin.last r), g ∉ K → (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0)
    (φ : (Wq →L[ℂ] Wp) →L[ℂ] ℂ) :
    Integrable (fun x : Mt k r => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) *
      star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)))) μ ∧
    Integrable (fun x : Mt k r => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) *
      star (φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)))) μ := by
  have c1 := smoothLev_continuousOn (smooth_clm φ (slice_smooth Φ.2 hc))
  have c2 := smoothLev_continuousOn (smooth_clm φ (slice_smooth Ψ.2 hc))
  constructor
  · refine integrable_cpt hμ (p := fun x => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x) *
      star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x))) hK hKD (c2.mul (continuous_star.comp_continuousOn c1)) ?_
    intro g hg hgK
    simp [h0 g hg hgK]
  · refine integrable_cpt hμ (p := fun x => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c x) *
      star (φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c x))) hK hKD (c1.mul (continuous_star.comp_continuousOn c2)) ?_
    intro g hg hgK
    simp [h0 g hg hgK]

/- English proof (translation)
Simplify using `only [inner_coef]`. Rewrite using `[integral_finsetSum _ fun j _ => (integrable_pair hμ (X.t Y a b Φ) Ψ hc hK hKD (fun g hg hgK => (h0 g hg hgK).2) _).1, integral_finsetSum _ fun j _ => (integrable_pair hμ (X.t (star Y) b a Ψ) Φ hc hK hKD (fun g hg hgK => (h0 g hg hgK).1) _).2]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `set φ := coefL (stdOrthonormalBasis ℂ Wp j) v with hφ`. Establish `hs1 : SmoothLev k r (Fin.last r) Set.univ (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y))` using `smooth_clm φ (smooth_univ Φ.2 hc hK hKD fun g hg hgK => (h0 g hg hgK).1)`.

Establish `hs2 : SmoothLev k r (Fin.last r) Set.univ (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y))` using `smooth_clm φ (smooth_univ Ψ.2 hc hK hKD fun g hg hgK => (h0 g hg hgK).2)`. Establish `hc1 : CptOn k r (Fin.last r) (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y))` using `⟨K, hK, fun g hg hgK => by simp [(h0 g hg hgK).1]⟩`. Establish `hc2 : CptOn k r (Fin.last r) (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y))` using `⟨K, hK, fun g hg hgK => by simp [(h0 g hg hgK).2]⟩`. Establish `hh` using `hH k r z z' (Fin.last r) μ hμ hz hz' _ _ hs2 hs1 hc2 hc1 (star Y) b a`. Rewrite `hh` using `[star_star]`.

Establish `e1 : ∀ x : Mt k r, φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) * star (φ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) = _` using `fun x => key_pt X Φ Ψ hc Y a b φ (Matrix.of x)`. Establish `e2 : ∀ x : Mt k r, φ ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) * star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) = tL k r z z' (Fin.last r) (star Y) b a (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)) (Matrix.of x) * star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c ( …`. Introduce `x`. Use `congrArg star (key_pt X Ψ Φ hc (star Y) b a φ (Matrix.of x))` as an intermediate fact. Simplify `this` using `[mul_comm]`.

Simplify using `only [e1, e2]`. Conclude with `hh.symm`.
-/
theorem adjoint_main [FiniteDimensional ℂ Wp] (hH : HermHaar) (hz : inWb k r z) (hz' : inWb k r z')
    (X : ActualOps k r z z' π π') {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Ψ : RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r) {K : Set (Mx k r)} (hK : IsCompact K)
    (hKD : K ⊆ Dp k r z z')
    (h0 : ∀ g ∈ Glev k r (Fin.last r), g ∉ K →
      (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 ∧ (Ψ : Fn k r (Wq →L[ℂ] Wp)) c g = 0) (Y : ℂ) (a b : Fin 2) (v : Wq) :
    (∫ x : Mt k r, ⟪(X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ ∂μ) =
      ∫ x : Mt k r, ⟪(Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v,
        (X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x) v⟫_ℂ ∂μ := by
  simp only [inner_coef]
  rw [integral_finsetSum _ fun j _ => (integrable_pair hμ (X.t Y a b Φ) Ψ hc hK hKD (fun g hg hgK => (h0 g hg hgK).2) _).1,
    integral_finsetSum _ fun j _ => (integrable_pair hμ (X.t (star Y) b a Ψ) Φ hc hK hKD
      (fun g hg hgK => (h0 g hg hgK).1) _).2]
  refine Finset.sum_congr rfl fun j _ => ?_
  set φ := coefL (stdOrthonormalBasis ℂ Wp j) v with hφ
  have hs1 : SmoothLev k r (Fin.last r) Set.univ (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)) :=
    smooth_clm φ (smooth_univ Φ.2 hc hK hKD fun g hg hgK => (h0 g hg hgK).1)
  have hs2 : SmoothLev k r (Fin.last r) Set.univ (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)) :=
    smooth_clm φ (smooth_univ Ψ.2 hc hK hKD fun g hg hgK => (h0 g hg hgK).2)
  have hc1 : CptOn k r (Fin.last r) (fun y => φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c y)) :=
    ⟨K, hK, fun g hg hgK => by simp [(h0 g hg hgK).1]⟩
  have hc2 : CptOn k r (Fin.last r) (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)) :=
    ⟨K, hK, fun g hg hgK => by simp [(h0 g hg hgK).2]⟩
  have hh := hH k r z z' (Fin.last r) μ hμ hz hz' _ _ hs2 hs1 hc2 hc1 (star Y) b a
  rw [star_star] at hh
  have e1 : ∀ x : Mt k r, φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) *
      star (φ ((X.t Y a b Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) = _ :=
    fun x => key_pt X Φ Ψ hc Y a b φ (Matrix.of x)
  have e2 : ∀ x : Mt k r, φ ((X.t (star Y) b a Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x)) *
      star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) =
      tL k r z z' (Fin.last r) (star Y) b a (fun y => φ ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c y)) (Matrix.of x) *
        star (φ ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) := by
    intro x
    have := congrArg star (key_pt X Ψ Φ hc (star Y) b a φ (Matrix.of x))
    simpa [mul_comm] using this
  simp only [e1, e2]
  exact hh.symm

end Adj

section Alg

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

/- English proof (translation)
Rewrite using `[Algebra.smul_def]`. Simplify using the standard rewrite rules.
-/
theorem intCast_smul (z : ℤ) (X : A) : ((z : ℤ) : A) * X = ((z : ℤ) : ℂ) • X := by
  rw [Algebra.smul_def]
  simp

/- English proof (translation)
Simplify using `[qminor]`.
-/
theorem qminor_zero (E : Fin n → Fin n → A) (a b : Fin 0 → Fin n) (u : ℂ) : qminor E a b u = 1 := by
  simp [qminor]

/- English proof (translation)
Unfold `qminor`. Rewrite using `[(Fintype.sum_bijective _ (Qx6.firstColumnSplit_bijective t) _ _ (fun _ => rfl)).symm, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations.

Rewrite using `[List.ofFn_succ, List.prod_cons]`. Simplify using `only [Qx6.sign_insert_perm, Qx6.firstColumnSplit_zero, Qx6.firstColumnSplit_succ, Function.comp, Fin.val_zero, Fin.val_succ]`. Establish `e1 : u - ((0 : ℕ) : ℂ) = u` using `by simp`. Establish `e2 : ∀ i : Fin t, u - (((i : ℕ) + 1 : ℕ) : ℂ) = u - 1 - ((i : ℕ) : ℂ)`. Introduce `i`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [e1, e2, intCast_smul, mul_smul_comm, smul_smul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem expFirstCol (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin (t + 1) → Fin n) (u : ℂ) :
    qminor E a b u = ∑ l : Fin (t + 1), ((-1 : ℂ) ^ (l : ℕ)) •
      (Tm E u (a l) (b 0) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (u - 1)) := by
  unfold qminor
  rw [(Fintype.sum_bijective _ (Qx6.firstColumnSplit_bijective t) _ _ (fun _ => rfl)).symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun τ _ => ?_)
  rw [List.ofFn_succ, List.prod_cons]
  simp only [Qx6.sign_insert_perm, Qx6.firstColumnSplit_zero, Qx6.firstColumnSplit_succ, Function.comp, Fin.val_zero, Fin.val_succ]
  have e1 : u - ((0 : ℕ) : ℂ) = u := by simp
  have e2 : ∀ i : Fin t, u - (((i : ℕ) + 1 : ℕ) : ℂ) = u - 1 - ((i : ℕ) : ℂ) := by
    intro i; push_cast; ring
  simp only [e1, e2, intCast_smul, mul_smul_comm, smul_smul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Set `e : Fin (t + 1) × Fin t → Fin (t + 1) × Fin t` to `fun x => (x.1.succAbove x.2, x.2.predAbove x.1)`. Establish `he : Function.Involutive e`. Introduce and unpack `⟨p, l⟩`. Simplify using `only [e, Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]`. Rewrite using `[← Fintype.sum_prod_type' F, ← Fintype.sum_prod_type' fun (p : Fin (t + 1)) (l : Fin t) => F (p.succAbove l) (l.predAbove p)]`.

Conclude with `(Equiv.sum_comp he.toPerm fun x : Fin (t + 1) × Fin t => F x.1 x.2).symm`.
-/
theorem swapSum {M : Type*} [AddCommMonoid M] {t : ℕ} (F : Fin (t + 1) → Fin t → M) :
    ∑ l, ∑ p, F l p = ∑ p : Fin (t + 1), ∑ l : Fin t, F (p.succAbove l) (l.predAbove p) := by
  let e : Fin (t + 1) × Fin t → Fin (t + 1) × Fin t := fun x => (x.1.succAbove x.2, x.2.predAbove x.1)
  have he : Function.Involutive e := by
    rintro ⟨p, l⟩
    simp only [e, Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]
  rw [← Fintype.sum_prod_type' F, ← Fintype.sum_prod_type' fun (p : Fin (t + 1)) (l : Fin t) => F (p.succAbove l) (l.predAbove p)]
  exact (Equiv.sum_comp he.toPerm fun x : Fin (t + 1) × Fin t => F x.1 x.2).symm

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp, Fin.succAbove_succAbove_succAbove_predAbove]`.
-/
theorem swap_list {α : Type*} {t : ℕ} (a : Fin (t + 2) → α) (p : Fin (t + 2)) (l : Fin (t + 1)) :
    (a ∘ (p.succAbove l).succAbove) ∘ (l.predAbove p).succAbove = (a ∘ p.succAbove) ∘ l.succAbove := by
  funext k
  simp only [Function.comp, Fin.succAbove_succAbove_succAbove_predAbove]

/- English proof (translation)
The claim follows from `Fin.neg_one_pow_succAbove_add_predAbove p l`.
-/
theorem swap_sign {t : ℕ} (p : Fin (t + 1)) (l : Fin t) :
    (-1 : ℂ) ^ ((p.succAbove l : ℕ) + (l.predAbove p : ℕ)) = -(-1) ^ ((p : ℕ) + (l : ℕ)) :=
  Fin.neg_one_pow_succAbove_add_predAbove p l

structure CovRel (E : Fin n → Fin n → A) (η : Fin n → A) (x : Fin n → ℂ) (ζ : A) : Prop where
  Eη : ∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0
  Eζ : ∀ a b, E a b * ζ - ζ * E a b = x b • η a

variable {E : Fin n → Fin n → A} {η : Fin n → A} {x : Fin n → ℂ} {ζ : A}

/- English proof (translation)
Establish `h1` using `h.Eζ a b`. Establish `h2 : E a b * ζ = ζ * E a b + x b • η a` using `by rw [← h1]; abel`. Unfold `Tm`. Rewrite using `[add_mul, mul_add, h2]`. Use `split_ifs`.

Rewrite using `[Algebra.commutes]`. Normalize the expressions using the abelian group laws. Simplify using the standard rewrite rules.
-/
theorem CovRel.Tζ (h : CovRel E η x ζ) (w : ℂ) (a b : Fin n) :
    Tm E w a b * ζ = ζ * Tm E w a b + x b • η a := by
  have h1 := h.Eζ a b
  have h2 : E a b * ζ = ζ * E a b + x b • η a := by rw [← h1]; abel
  unfold Tm
  rw [add_mul, mul_add, h2]
  split_ifs
  · rw [Algebra.commutes]; abel
  · simp

/- English proof (translation)
Establish `h1` using `h.Eη a b c`. Establish `h2 : E a b * η c = η c * E a b + (if b = c then η a else 0)` using `by rw [← h1]; abel`. Unfold `Tm`. Rewrite using `[add_mul, mul_add, h2]`. Distinguish the cases in `hab : a = b`.

Simplify using `only [hab, if_true]`. Rewrite using `[Algebra.commutes, map_sub, map_one, mul_sub, mul_one]`. Normalize the expressions using the abelian group laws. Simplify using `[hab]`.
-/
theorem CovRel.Tη (h : CovRel E η x ζ) (w : ℂ) (a b c : Fin n) :
    Tm E w a b * η c = η c * Tm E (w - 1) a b + (if a = b then η c else 0) + (if b = c then η a else 0) := by
  have h1 := h.Eη a b c
  have h2 : E a b * η c = η c * E a b + (if b = c then η a else 0) := by rw [← h1]; abel
  unfold Tm
  rw [add_mul, mul_add, h2]
  by_cases hab : a = b
  · simp only [hab, if_true]
    rw [Algebra.commutes, map_sub, map_one, mul_sub, mul_one]
    abel
  · simp [hab]

/- English proof (translation)
Establish `e : ∀ (l : Fin (t + 2)) (p : Fin (t + 1)), ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • (Tm E w (a l) c * (η (a (l.succAbove p)) * M l p)) = ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • (η (a (l.succAbove p)) * (Tm E (w - 1) (a l) c * M l p)) + (((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • ((if a l = c then η …`. Introduce `l p`. Rewrite using `[← mul_assoc, h.Tη, add_mul, add_mul, smul_add, smul_add, mul_assoc, add_assoc]`. Simplify using `only [e, Finset.sum_add_distrib]`. Establish `s1` using `swapSum fun (l : Fin (t + 2)) (p : Fin (t + 1)) => ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • (η (a (l.succAbove p)) * (Tm E (w - 1) (a l) c * M l p))`.

Establish `s3` using `swapSum fun (l : Fin (t + 2)) (p : Fin (t + 1)) => ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • ((if c = a (l.succAbove p) then η (a l) else 0) * M l p)`. Simplify using `only [swap_sign, hM, Fin.succAbove_succAbove_predAbove, neg_smul, Finset.sum_neg_distrib] at s1 s3`. Rewrite using `[s1, s3]`. Simplify using `only [eq_comm (a := c)]`. Normalize the expressions using the abelian group laws.
-/
theorem core_swap (h : CovRel E η x ζ) {t : ℕ} (a : Fin (t + 2) → Fin n) (c : Fin n) (w : ℂ)
    (M : Fin (t + 2) → Fin (t + 1) → A) (hM : ∀ p l, M (p.succAbove l) (l.predAbove p) = M p l) :
    ∑ l : Fin (t + 2), ∑ p : Fin (t + 1),
        ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • (Tm E w (a l) c * (η (a (l.succAbove p)) * M l p)) =
      -∑ p : Fin (t + 2), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (l : ℕ))) • (η (a p) * (Tm E (w - 1) (a (p.succAbove l)) c * M p l)) := by
  have e : ∀ (l : Fin (t + 2)) (p : Fin (t + 1)), ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • (Tm E w (a l) c * (η (a (l.succAbove p)) * M l p)) =
      ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • (η (a (l.succAbove p)) * (Tm E (w - 1) (a l) c * M l p)) +
      (((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • ((if a l = c then η (a (l.succAbove p)) else 0) * M l p) +
       ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • ((if c = a (l.succAbove p) then η (a l) else 0) * M l p)) := by
    intro l p
    rw [← mul_assoc, h.Tη, add_mul, add_mul, smul_add, smul_add, mul_assoc, add_assoc]
  simp only [e, Finset.sum_add_distrib]
  have s1 := swapSum fun (l : Fin (t + 2)) (p : Fin (t + 1)) => ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) •
    (η (a (l.succAbove p)) * (Tm E (w - 1) (a l) c * M l p))
  have s3 := swapSum fun (l : Fin (t + 2)) (p : Fin (t + 1)) => ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) •
    ((if c = a (l.succAbove p) then η (a l) else 0) * M l p)
  simp only [swap_sign, hM, Fin.succAbove_succAbove_predAbove, neg_smul, Finset.sum_neg_distrib] at s1 s3
  rw [s1, s3]
  simp only [eq_comm (a := c)]
  abel

end Alg

section Alg2

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} {η : Fin n → A} {x : Fin n → ℂ} {ζ : A}

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp, Fin.succ_succAbove_succ]`.
-/
theorem comp_succ_succAbove {α : Type*} {t : ℕ} (b : Fin (t + 2) → α) (q : Fin (t + 1)) :
    (b ∘ q.succ.succAbove) ∘ Fin.succ = (b ∘ Fin.succ) ∘ q.succAbove := by
  funext k
  simp only [Function.comp, Fin.succ_succAbove_succ]

/- English proof (translation)
Establish `hc` using `core_swap h a (b 0) w (fun l p => qminor E ((a ∘ l.succAbove) ∘ p.succAbove) ((b ∘ Fin.succ) ∘ q.succAbove) (w - 1 - 1)) (fun p l => by simp only [swap_list])`. Establish `L1 : ∑ l : Fin (t + 2), ((-1 : ℂ) ^ (l : ℕ)) • (Tm E w (a l) (b 0) * ∑ p : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * x ((b ∘ Fin.succ) q)) • (η ((a ∘ l.succAbove) p) * qminor E ((a ∘ l.succAbove) ∘ p.succAbove) ((b ∘ Fin.succ) ∘ q.succAbove) (w - 1 - 1))) = ((-1 : ℂ) ^ (q : …`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, Finset.smul_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm, smul_smul, smul_smul]`. Simplify using `only [Function.comp]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `R1 : ∑ p : Fin (t + 2), ((-1 : ℂ) ^ ((p : ℕ) + (q.succ : ℕ)) * x (b q.succ)) • (η (a p) * qminor E (a ∘ p.succAbove) (b ∘ q.succ.succAbove) (w - 1)) = ((-1 : ℂ) ^ (q : ℕ) * x (b q.succ)) • -∑ p : Fin (t + 2), ∑ l : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (l : ℕ))) • (η (a p) * (Tm E …`. Rewrite using `[← Finset.sum_neg_distrib, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[expFirstCol E (a ∘ p.succAbove) (b ∘ q.succ.succAbove) (w - 1), comp_succ_succAbove, Finset.mul_sum, ← Finset.sum_neg_distrib, Finset.smul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_smul_comm, smul_smul, ← neg_smul, smul_smul]`. Simplify using `only [Function.comp, Fin.succ_succAbove_zero, Fin.val_succ]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[L1, R1, hc]`.
-/
theorem minor_expansion_key_identity (h : CovRel E η x ζ) {t : ℕ} (a b : Fin (t + 2) → Fin n) (w : ℂ) (q : Fin (t + 1)) :
    ∑ l : Fin (t + 2), ((-1 : ℂ) ^ (l : ℕ)) • (Tm E w (a l) (b 0) *
        ∑ p : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * x ((b ∘ Fin.succ) q)) •
          (η ((a ∘ l.succAbove) p) * qminor E ((a ∘ l.succAbove) ∘ p.succAbove) ((b ∘ Fin.succ) ∘ q.succAbove) (w - 1 - 1))) =
      ∑ p : Fin (t + 2), ((-1 : ℂ) ^ ((p : ℕ) + (q.succ : ℕ)) * x (b q.succ)) •
        (η (a p) * qminor E (a ∘ p.succAbove) (b ∘ q.succ.succAbove) (w - 1)) := by
  have hc := core_swap h a (b 0) w
    (fun l p => qminor E ((a ∘ l.succAbove) ∘ p.succAbove) ((b ∘ Fin.succ) ∘ q.succAbove) (w - 1 - 1))
    (fun p l => by simp only [swap_list])
  have L1 : ∑ l : Fin (t + 2), ((-1 : ℂ) ^ (l : ℕ)) • (Tm E w (a l) (b 0) *
        ∑ p : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * x ((b ∘ Fin.succ) q)) •
          (η ((a ∘ l.succAbove) p) * qminor E ((a ∘ l.succAbove) ∘ p.succAbove) ((b ∘ Fin.succ) ∘ q.succAbove) (w - 1 - 1))) =
      ((-1 : ℂ) ^ (q : ℕ) * x (b q.succ)) • ∑ l : Fin (t + 2), ∑ p : Fin (t + 1),
        ((-1 : ℂ) ^ ((l : ℕ) + (p : ℕ))) • (Tm E w (a l) (b 0) * (η (a (l.succAbove p)) *
          qminor E ((a ∘ l.succAbove) ∘ p.succAbove) ((b ∘ Fin.succ) ∘ q.succAbove) (w - 1 - 1))) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [mul_smul_comm, smul_smul, smul_smul]
    simp only [Function.comp]
    congr 1
    ring
  have R1 : ∑ p : Fin (t + 2), ((-1 : ℂ) ^ ((p : ℕ) + (q.succ : ℕ)) * x (b q.succ)) •
        (η (a p) * qminor E (a ∘ p.succAbove) (b ∘ q.succ.succAbove) (w - 1)) =
      ((-1 : ℂ) ^ (q : ℕ) * x (b q.succ)) • -∑ p : Fin (t + 2), ∑ l : Fin (t + 1),
        ((-1 : ℂ) ^ ((p : ℕ) + (l : ℕ))) • (η (a p) * (Tm E (w - 1) (a (p.succAbove l)) (b 0) *
          qminor E ((a ∘ p.succAbove) ∘ l.succAbove) ((b ∘ Fin.succ) ∘ q.succAbove) (w - 1 - 1))) := by
    rw [← Finset.sum_neg_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [expFirstCol E (a ∘ p.succAbove) (b ∘ q.succ.succAbove) (w - 1), comp_succ_succAbove, Finset.mul_sum,
      ← Finset.sum_neg_distrib, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, smul_smul, ← neg_smul, smul_smul]
    simp only [Function.comp, Fin.succ_succAbove_zero, Fin.val_succ]
    congr 1
    ring
  rw [L1, R1, hc]

/- English proof (translation)
Introduce `t`. Proceed by induction on `t with`. Consider the case `zero`. Introduce `a b w`. Rewrite using `[expFirstCol E a b w]`.

Simplify using `only [qminor_zero, mul_one, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_smul, one_mul]`. Conclude with `h.Tζ w _ _`. Consider the case `succ t ih`. Introduce `a b w`. Establish `step : ∀ l : Fin (t + 2), (Tm E w (a l) (b 0) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (w - 1)) * ζ = ζ * (Tm E w (a l) (b 0) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (w - 1)) + x (b 0) • (η (a l) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (w - 1)) + Tm E w (a l) (b 0) * ∑ …`.

Introduce `l`. Rewrite using `[mul_assoc, ih, mul_add, ← mul_assoc, h.Tζ, add_mul, smul_mul_assoc, mul_assoc, Finset.sum_comm]`. Establish `hR : ∑ p : Fin (t + 2), ∑ q : Fin (t + 2), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * x (b q)) • (η (a p) * qminor E (a ∘ p.succAbove) (b ∘ q.succAbove) (w - 1)) = ∑ l : Fin (t + 2), ((-1 : ℂ) ^ (l : ℕ)) • (x (b 0) • (η (a l) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (w - 1))) + ∑ q : F …`. Simplify using `only [Fin.sum_univ_succ (n := t + 1) (f := fun q : Fin (t + 2) => ((-1 : ℂ) ^ ((_ : ℕ) + (q : ℕ)) * x (b q)) • _)]`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, Fin.succAbove_zero]`. Simplify using the standard rewrite rules. Rewrite using `[hR, expFirstCol E a b w, Finset.sum_mul, Finset.mul_sum]`.

Simplify using `only [smul_mul_assoc, step, smul_add, Finset.sum_add_distrib, mul_smul_comm]`. Rewrite using `[add_assoc]`. Use `congr 2`. Rewrite using `[← Finset.sum_congr rfl fun q _ => minor_expansion_key_identity h a b w q, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, Finset.smul_sum]`.
-/
theorem Z1 (h : CovRel E η x ζ) : ∀ (t : ℕ) (a b : Fin (t + 1) → Fin n) (w : ℂ),
    qminor E a b w * ζ = ζ * qminor E a b w + ∑ p : Fin (t + 1), ∑ q : Fin (t + 1),
      ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * x (b q)) •
        (η (a p) * qminor E (a ∘ p.succAbove) (b ∘ q.succAbove) (w - 1)) := by
  intro t
  induction t with
  | zero =>
    intro a b w
    rw [expFirstCol E a b w]
    simp only [qminor_zero, mul_one, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, pow_zero, one_smul,
      one_mul]
    exact h.Tζ w _ _
  | succ t ih =>
    intro a b w
    have step : ∀ l : Fin (t + 2), (Tm E w (a l) (b 0) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (w - 1)) * ζ =
        ζ * (Tm E w (a l) (b 0) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (w - 1)) +
        x (b 0) • (η (a l) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (w - 1)) +
        Tm E w (a l) (b 0) * ∑ q : Fin (t + 1), ∑ p : Fin (t + 1),
          ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * x ((b ∘ Fin.succ) q)) •
            (η ((a ∘ l.succAbove) p) * qminor E ((a ∘ l.succAbove) ∘ p.succAbove) ((b ∘ Fin.succ) ∘ q.succAbove) (w - 1 - 1)) := by
      intro l
      rw [mul_assoc, ih, mul_add, ← mul_assoc, h.Tζ, add_mul, smul_mul_assoc, mul_assoc, Finset.sum_comm]
    have hR : ∑ p : Fin (t + 2), ∑ q : Fin (t + 2), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * x (b q)) •
          (η (a p) * qminor E (a ∘ p.succAbove) (b ∘ q.succAbove) (w - 1)) =
        ∑ l : Fin (t + 2), ((-1 : ℂ) ^ (l : ℕ)) • (x (b 0) • (η (a l) * qminor E (a ∘ l.succAbove) (b ∘ Fin.succ) (w - 1))) +
        ∑ q : Fin (t + 1), ∑ p : Fin (t + 2), ((-1 : ℂ) ^ ((p : ℕ) + (q.succ : ℕ)) * x (b q.succ)) •
          (η (a p) * qminor E (a ∘ p.succAbove) (b ∘ q.succ.succAbove) (w - 1)) := by
      simp only [Fin.sum_univ_succ (n := t + 1) (f := fun q : Fin (t + 2) => ((-1 : ℂ) ^ ((_ : ℕ) + (q : ℕ)) * x (b q)) • _)]
      rw [Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, Fin.succAbove_zero]
      simp
    rw [hR, expFirstCol E a b w, Finset.sum_mul, Finset.mul_sum]
    simp only [smul_mul_assoc, step, smul_add, Finset.sum_add_distrib, mul_smul_comm]
    rw [add_assoc]
    congr 2
    rw [← Finset.sum_congr rfl fun q _ => minor_expansion_key_identity h a b w q, Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]

end Alg2

section Dual

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

def Eop (E : Fin n → Fin n → A) : Fin n → Fin n → A := fun a b => -E b a

/- English proof (translation)
Introduce `a b c d`. Establish `h` using `hE d c b a`. Simplify using `only [Eop, neg_mul_neg]`. Establish `h2 : E b a * E d c - E d c * E b a = -(E d c * E b a - E b a * E d c)` using `by abel`. Rewrite using `[h2, h]`.

Establish `e1 : (c = b) = (b = c)` using `propext eq_comm`. Establish `e2 : (a = d) = (d = a)` using `propext eq_comm`. Simplify using `only [e1, e2]`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h3 : d = a <;> (simp [h1, h3]; try abel)`.
-/
theorem Eop_gl {E : Fin n → Fin n → A} (hE : GlRel E) : GlRel (Eop E) := by
  intro a b c d
  have h := hE d c b a
  simp only [Eop, neg_mul_neg]
  have h2 : E b a * E d c - E d c * E b a = -(E d c * E b a - E b a * E d c) := by abel
  rw [h2, h]
  have e1 : (c = b) = (b = c) := propext eq_comm
  have e2 : (a = d) = (d = a) := propext eq_comm
  simp only [e1, e2]
  by_cases h1 : b = c <;> by_cases h3 : d = a <;> (simp [h1, h3]; try abel)

/- English proof (translation)
Unfold `Tm Eop`. Distinguish the cases in `h : a = b`. Simplify using `[h, add_comm]`. Simplify using `[h, Ne.symm h]`.
-/
theorem Tm_Eop (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) : Tm (Eop E) v a b = -Tm E (-v) b a := by
  unfold Tm Eop
  by_cases h : a = b
  · simp [h, add_comm]
  · simp [h, Ne.symm h]

def dP (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (θ : Fin t → ℂ) (σ τ : Equiv.Perm (Fin t)) : A :=
  (List.ofFn fun k : Fin t => Tm E (θ k) (a (σ k)) (b (τ k))).prod

def dsum (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (θ : Fin t → ℂ) : A :=
  ∑ τ : Equiv.Perm (Fin t), ∑ σ : Equiv.Perm (Fin t),
    ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * dP E a b θ σ τ)

/- English proof (translation)
Rewrite using `[← mul_assoc, ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one, one_mul]`.
-/
theorem sign_sq (τ : Equiv.Perm (Fin n)) (X : A) :
    ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign τ : ℤ) : A) * X) = X := by
  rw [← mul_assoc, ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one, one_mul]

/- English proof (translation)
Establish `h : ∀ τ : Equiv.Perm (Fin t), ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * dP E a b (fun k => w - ((k : ℕ) : ℂ)) σ τ) = qminor E a b w`. Introduce `τ`. Rewrite using `[← Finset.mul_sum]`. Establish `: ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) * dP E a b (fun k => w - ((k : ℕ) : ℂ)) σ τ = qminor E a (b ∘ τ) w` using `rfl`. Rewrite using `[this, quantumMinorColSkew_holds A n t E hE a b τ w, sign_sq]`.

Unfold `dsum`. Simplify using `only [h, Finset.sum_const, Finset.card_univ]`. Rewrite using `[Nat.cast_smul_eq_nsmul]`.
-/
theorem dsum_qminor {E : Fin n → Fin n → A} (hE : GlRel E) {t : ℕ} (a b : Fin t → Fin n) (w : ℂ) :
    dsum E a b (fun k => w - ((k : ℕ) : ℂ)) = (Fintype.card (Equiv.Perm (Fin t)) : ℂ) • qminor E a b w := by
  have h : ∀ τ : Equiv.Perm (Fin t), ∑ σ : Equiv.Perm (Fin t),
      ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * dP E a b (fun k => w - ((k : ℕ) : ℂ)) σ τ) =
      qminor E a b w := by
    intro τ
    rw [← Finset.mul_sum]
    have : ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) * dP E a b (fun k => w - ((k : ℕ) : ℂ)) σ τ =
        qminor E a (b ∘ τ) w := rfl
    rw [this, quantumMinorColSkew_holds A n t E hE a b τ w, sign_sq]
  unfold dsum
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Simplify using `only [shiftedGenerator_eq_ite_smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]`. Use `module`.
-/
theorem mid_id (E : Fin n → Fin n → A) (x y : ℂ) (p c q d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E y p c * Tm E x q d + Tm E x q d * Tm E y p c - Tm E y q d * Tm E x p c = 0 := by
  simp only [shiftedGenerator_eq_ite_smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

/- English proof (translation)
Establish `hs : ∀ k : Fin (m + 1), (k : ℕ) ≠ (i : ℕ) → (k : ℕ) ≠ (i : ℕ) + 1 → Equiv.swap i.castSucc i.succ k = k`. Introduce `k h1 h2`. Apply `Equiv.swap_apply_of_ne_of_ne` to reduce the goal to its premises. Introduce `h`. Apply `h1` to reduce the goal to its premises.

Rewrite using `[h]`. Simplify using the standard rewrite rules. Introduce `h`. Apply `h2` to reduce the goal to its premises. Rewrite using `[h]`.

Simplify using the standard rewrite rules. Unfold `dP`. Apply `prod_ofFn_alternating_sum _ _ _ _ (i : ℕ) (by omega)` to reduce the goal to its premises. Introduce `k h1 h2`. Simplify using `[hs k h1 h2]`.

Introduce `k h1 h2`. Simplify using `[Equiv.Perm.mul_apply, hs k h1 h2]`. Introduce `k h1 h2`. Simplify using `[Equiv.Perm.mul_apply, hs k h1 h2]`. Establish `e1 : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc` using `rfl`.

Establish `e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)) = i.succ` using `rfl`. Simplify using `only [e1, e2, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left, Equiv.swap_apply_right]`. Conclude with `mid_id E _ _ _ _ _ _`.
-/
theorem dP_four (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (θ : Fin (m + 1) → ℂ) (i : Fin m)
    (σ τ : Equiv.Perm (Fin (m + 1))) :
    dP E a b θ σ τ - dP E a b (θ ∘ Equiv.swap i.castSucc i.succ) σ τ
      + dP E a b θ (σ * Equiv.swap i.castSucc i.succ) (τ * Equiv.swap i.castSucc i.succ)
      - dP E a b (θ ∘ Equiv.swap i.castSucc i.succ) (σ * Equiv.swap i.castSucc i.succ)
          (τ * Equiv.swap i.castSucc i.succ) = 0 := by
  have hs : ∀ k : Fin (m + 1), (k : ℕ) ≠ (i : ℕ) → (k : ℕ) ≠ (i : ℕ) + 1 →
      Equiv.swap i.castSucc i.succ k = k := by
    intro k h1 h2
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; apply h1; rw [h]; simp
    · intro h; apply h2; rw [h]; simp
  unfold dP
  apply prod_ofFn_alternating_sum _ _ _ _ (i : ℕ) (by omega)
  · intro k h1 h2; simp [hs k h1 h2]
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]
  · have e1 : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := rfl
    have e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)) = i.succ := rfl
    simp only [e1, e2, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    exact mid_id E _ _ _ _ _ _

/- English proof (translation)
Use `set s := Equiv.swap i.castSucc i.succ with hs_def`. Establish `hsgn : Equiv.Perm.sign s = -1` using `Equiv.Perm.sign_swap (by simp [Fin.ext_iff])`. Use `set G : Equiv.Perm (Fin (m + 1)) → Equiv.Perm (Fin (m + 1)) → A := fun τ σ => ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * (dP E a b θ σ τ - dP E a b (θ ∘ s) σ τ)) with hG`. Establish `hsum : dsum E a b θ - dsum E a b (θ ∘ s) = ∑ τ, ∑ σ, G τ σ`. Unfold `dsum`.

Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [hG, mul_sub]`.

Establish `hre : ∑ τ, ∑ σ, G (τ * s) (σ * s) = ∑ τ, ∑ σ, G τ σ`. Rewrite using `[Fintype.sum_equiv (Equiv.mulRight s) (fun τ => ∑ σ, G (τ * s) (σ * s)) (fun τ => ∑ σ, G τ (σ * s)) (fun τ => rfl)]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Conclude with `Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun σ => rfl)`. Establish `hpair : ∀ τ σ, G τ σ + G (τ * s) (σ * s) = 0`.

Introduce `τ σ`. Simplify using `only [hG, Equiv.Perm.sign_mul, hsgn, mul_neg, mul_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg]`. Establish `k` using `dP_four E a b θ i σ τ`. Rewrite `k` using `[← hs_def]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h0 : (∑ τ, ∑ σ, G τ σ) + (∑ τ, ∑ σ, G τ σ) = 0`. Combine the equalities or inequalities in the displayed calculation. Use `eq_zero_of_add_self_eq_zero _ h0` as an intermediate fact. Rewrite `this` using `[← hsum]`. Conclude with `(sub_eq_zero.1 this).symm`.
-/
theorem dsum_adj (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (θ : Fin (m + 1) → ℂ) (i : Fin m) :
    dsum E a b (θ ∘ Equiv.swap i.castSucc i.succ) = dsum E a b θ := by
  set s := Equiv.swap i.castSucc i.succ with hs_def
  have hsgn : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap (by simp [Fin.ext_iff])
  set G : Equiv.Perm (Fin (m + 1)) → Equiv.Perm (Fin (m + 1)) → A := fun τ σ =>
    ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * (dP E a b θ σ τ - dP E a b (θ ∘ s) σ τ)) with hG
  have hsum : dsum E a b θ - dsum E a b (θ ∘ s) = ∑ τ, ∑ σ, G τ σ := by
    unfold dsum
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [hG, mul_sub]
  have hre : ∑ τ, ∑ σ, G (τ * s) (σ * s) = ∑ τ, ∑ σ, G τ σ := by
    rw [Fintype.sum_equiv (Equiv.mulRight s) (fun τ => ∑ σ, G (τ * s) (σ * s)) (fun τ => ∑ σ, G τ (σ * s))
      (fun τ => rfl)]
    refine Finset.sum_congr rfl fun τ _ => ?_
    exact Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun σ => rfl)
  have hpair : ∀ τ σ, G τ σ + G (τ * s) (σ * s) = 0 := by
    intro τ σ
    simp only [hG, Equiv.Perm.sign_mul, hsgn, mul_neg, mul_one, Units.val_neg, Int.cast_neg, neg_mul, neg_neg]
    have k := dP_four E a b θ i σ τ
    rw [← hs_def] at k
    calc _ = ((Equiv.Perm.sign τ : ℤ) : A) * (((Equiv.Perm.sign σ : ℤ) : A) * (dP E a b θ σ τ - dP E a b (θ ∘ s) σ τ
        + dP E a b θ (σ * s) (τ * s) - dP E a b (θ ∘ s) (σ * s) (τ * s))) := by noncomm_ring
      _ = 0 := by rw [k, mul_zero, mul_zero]
  have h0 : (∑ τ, ∑ σ, G τ σ) + (∑ τ, ∑ σ, G τ σ) = 0 := by
    calc (∑ τ, ∑ σ, G τ σ) + (∑ τ, ∑ σ, G τ σ) = (∑ τ, ∑ σ, G τ σ) + ∑ τ, ∑ σ, G (τ * s) (σ * s) := by rw [hre]
      _ = ∑ τ, ∑ σ, (G τ σ + G (τ * s) (σ * s)) := by simp only [Finset.sum_add_distrib]
      _ = 0 := by simp only [hpair, Finset.sum_const_zero]
  have := eq_zero_of_add_self_eq_zero _ h0
  rw [← hsum] at this
  exact (sub_eq_zero.1 this).symm

/- English proof (translation)
Consider the cases of `t with`. Consider the case `zero`. Establish `: π = 1` using `Subsingleton.elim _ _`. Substitute `this` using the available equality. Both sides reduce to the same expression.

Consider the case `succ m`. Establish `hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ)`. Rewrite using `[Equiv.Perm.mclosure_swap_castSucc_succ m]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hπ using Submonoid.closure_induction generalizing θ with`.

Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Conclude with `dsum_adj E a b θ i`. Consider the case `one => rfl`. Consider the case `mul x y _ _ hx hy`.

Establish `hc : θ ∘ ⇑(x * y) = (θ ∘ ⇑x) ∘ ⇑y` using `by ext k; simp`. Rewrite using `[hc, hy (θ ∘ ⇑x), hx θ]`.
-/
theorem dsum_perm (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (θ : Fin t → ℂ) (π : Equiv.Perm (Fin t)) :
    dsum E a b (θ ∘ π) = dsum E a b θ := by
  cases t with
  | zero =>
    have : π = 1 := Subsingleton.elim _ _
    subst this; rfl
  | succ m =>
    have hπ : π ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ m]; trivial
    induction hπ using Submonoid.closure_induction generalizing θ with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact dsum_adj E a b θ i
    | one => rfl
    | mul x y _ _ hx hy =>
      have hc : θ ∘ ⇑(x * y) = (θ ∘ ⇑x) ∘ ⇑y := by ext k; simp
      rw [hc, hy (θ ∘ ⇑x), hx θ]

/- English proof (translation)
Establish `h : ∀ σ τ : Equiv.Perm (Fin t), dP (Eop E) b a θ σ τ = ((-1 : ℂ) ^ t) • dP E a b (fun k => -θ k) τ σ`. Introduce `σ τ`. Unfold `dP`. Simplify using `only [Tm_Eop]`. Establish `: (List.ofFn fun k : Fin t => -Tm E (-θ k) (a (τ k)) (b (σ k))) = (List.ofFn fun k : Fin t => Tm E (-θ k) (a (τ k)) (b (σ k))).map Neg.neg`.

Rewrite using `[List.map_ofFn]`. Both sides reduce to the same expression. Rewrite using `[this, List.prod_map_neg, List.length_ofFn, Algebra.smul_def]`. Simplify using the standard rewrite rules. Unfold `dsum`.

Rewrite using `[Finset.sum_comm, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[h, mul_smul_comm, mul_smul_comm, ← mul_assoc, ← mul_assoc, (Int.cast_commute _ _).eq]`.
-/
theorem dsum_Eop (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (θ : Fin t → ℂ) :
    dsum (Eop E) b a θ = ((-1 : ℂ) ^ t) • dsum E a b (fun k => -θ k) := by
  have h : ∀ σ τ : Equiv.Perm (Fin t), dP (Eop E) b a θ σ τ = ((-1 : ℂ) ^ t) • dP E a b (fun k => -θ k) τ σ := by
    intro σ τ
    unfold dP
    simp only [Tm_Eop]
    have : (List.ofFn fun k : Fin t => -Tm E (-θ k) (a (τ k)) (b (σ k))) =
        (List.ofFn fun k : Fin t => Tm E (-θ k) (a (τ k)) (b (σ k))).map Neg.neg := by
      rw [List.map_ofFn]; rfl
    rw [this, List.prod_map_neg, List.length_ofFn, Algebra.smul_def]
    simp
  unfold dsum
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [h, mul_smul_comm, mul_smul_comm, ← mul_assoc, ← mul_assoc, (Int.cast_commute _ _).eq]

/- English proof (translation)
Establish `h1` using `dsum_qminor hE a b w`. Establish `h2` using `dsum_qminor (Eop_gl hE) b a ((t : ℂ) - 1 - w)`. Rewrite `h2` using `[dsum_Eop]`. Establish `h3 : (fun k : Fin t => -((t : ℂ) - 1 - w - ((k : ℕ) : ℂ))) = (fun k : Fin t => w - ((k : ℕ) : ℂ)) ∘ Fin.revPerm`. Use function extensionality and compare the values at `k`.

Establish `hk : (k : ℕ) + 1 ≤ t` using `k.isLt`. Simplify using `only [Function.comp, Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub hk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[h3, dsum_perm, h1]`.

Establish `hN : (Fintype.card (Equiv.Perm (Fin t)) : ℂ) ≠ 0`. Conclude with `Fintype.card_ne_zero` after adjusting the coercions. Establish `h4 : (Fintype.card (Equiv.Perm (Fin t)) : ℂ) • (((-1 : ℂ) ^ t) • qminor E a b w) = (Fintype.card (Equiv.Perm (Fin t)) : ℂ) • qminor (Eop E) b a ((t : ℂ) - 1 - w)`. Rewrite using `[← h2, smul_comm]`. Establish `h5` using `smul_right_injective A hN h4`.

Rewrite using `[← h5, smul_smul, ← mul_pow]`. Simplify using the standard rewrite rules.
-/
theorem duality {E : Fin n → Fin n → A} (hE : GlRel E) {t : ℕ} (a b : Fin t → Fin n) (w : ℂ) :
    qminor E a b w = ((-1 : ℂ) ^ t) • qminor (Eop E) b a ((t : ℂ) - 1 - w) := by
  have h1 := dsum_qminor hE a b w
  have h2 := dsum_qminor (Eop_gl hE) b a ((t : ℂ) - 1 - w)
  rw [dsum_Eop] at h2
  have h3 : (fun k : Fin t => -((t : ℂ) - 1 - w - ((k : ℕ) : ℂ))) = (fun k : Fin t => w - ((k : ℕ) : ℂ)) ∘ Fin.revPerm := by
    funext k
    have hk : (k : ℕ) + 1 ≤ t := k.isLt
    simp only [Function.comp, Fin.revPerm_apply, Fin.val_rev, Nat.cast_sub hk]
    push_cast
    ring
  rw [h3, dsum_perm, h1] at h2
  have hN : (Fintype.card (Equiv.Perm (Fin t)) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h4 : (Fintype.card (Equiv.Perm (Fin t)) : ℂ) • (((-1 : ℂ) ^ t) • qminor E a b w) =
      (Fintype.card (Equiv.Perm (Fin t)) : ℂ) • qminor (Eop E) b a ((t : ℂ) - 1 - w) := by
    rw [← h2, smul_comm]
  have h5 := smul_right_injective A hN h4
  rw [← h5, smul_smul, ← mul_pow]
  simp

end Dual

section Alg4

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} {E : Fin n → Fin n → A} {y : Fin n → A} {ξ : Fin n → ℂ} {ζb : A}

structure VecRel (E : Fin n → Fin n → A) (y : Fin n → A) (ξ : Fin n → ℂ) (ζb : A) : Prop where
  Ey : ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0
  Eζ : ∀ a b, E a b * ζb - ζb * E a b = -(ξ a • y b)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b c`. Use `h.Ey b a c` as an intermediate fact. Simplify using `only [Eop, neg_mul, mul_neg]`. Rewrite using `[show -(E b a * y c) - -(y c * E b a) = -(E b a * y c - y c * E b a) by abel, this]`.

Apply the tactic sequence `split_ifs <;> simp`. Introduce `a b`. Use `h.Eζ b a` as an intermediate fact. Simplify using `only [Eop, neg_mul, mul_neg]`. Rewrite using `[show -(E b a * ζb) - -(ζb * E b a) = -(E b a * ζb - ζb * E b a) by abel, this, neg_neg]`.
-/
theorem VecRel.cov (h : VecRel E y ξ ζb) : CovRel (Eop E) y ξ ζb := by
  constructor
  · intro a b c
    have := h.Ey b a c
    simp only [Eop, neg_mul, mul_neg]
    rw [show -(E b a * y c) - -(y c * E b a) = -(E b a * y c - y c * E b a) by abel, this]
    split_ifs <;> simp
  · intro a b
    have := h.Eζ b a
    simp only [Eop, neg_mul, mul_neg]
    rw [show -(E b a * ζb) - -(ζb * E b a) = -(E b a * ζb - ζb * E b a) by abel, this, neg_neg]

/- English proof (translation)
Establish `d0` using `duality hE a b w`. Establish `z` using `Z1 h.cov t b a (((t + 1 : ℕ) : ℂ) - 1 - w)`. Establish `hs : (-1 : ℂ) ^ t * (-1) ^ t = 1` using `by rw [← mul_pow]; simp`. Establish `d1 : ∀ p q : Fin (t + 1), qminor (Eop E) (b ∘ p.succAbove) (a ∘ q.succAbove) (((t + 1 : ℕ) : ℂ) - 1 - w - 1) = ((-1 : ℂ) ^ t) • qminor E (a ∘ q.succAbove) (b ∘ p.succAbove) w`. Introduce `p q`.

Rewrite using `[duality hE (a ∘ q.succAbove) (b ∘ p.succAbove) w, smul_smul, hs, one_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ((-1 : ℂ) ^ (t + 1)) • ∑ p : Fin (t + 1), ∑ q : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ξ (a q)) • (y (b p) * qminor (Eop E) (b ∘ p.succAbove) (a ∘ q.succAbove) (((t + 1 : ℕ) : ℂ) - 1 - w - 1)) = -∑ p : Fin (t + 1), ∑ q : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) …`.

Rewrite using `[Finset.sum_comm, Finset.smul_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[d1, mul_smul_comm, smul_smul, smul_smul, ← neg_smul]`.

Use `congr 1`. Take the linear combination `(-((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ξ (a p))) * hs`. Rewrite using `[d0, smul_mul_assoc, z, mul_smul_comm, smul_add, key, ← sub_eq_add_neg]`.
-/
theorem Z2 (hE : GlRel E) (h : VecRel E y ξ ζb) (t : ℕ) (a b : Fin (t + 1) → Fin n) (w : ℂ) :
    qminor E a b w * ζb = ζb * qminor E a b w - ∑ p : Fin (t + 1), ∑ q : Fin (t + 1),
      ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ξ (a p)) •
        (y (b q) * qminor E (a ∘ p.succAbove) (b ∘ q.succAbove) w) := by
  have d0 := duality hE a b w
  have z := Z1 h.cov t b a (((t + 1 : ℕ) : ℂ) - 1 - w)
  have hs : (-1 : ℂ) ^ t * (-1) ^ t = 1 := by rw [← mul_pow]; simp
  have d1 : ∀ p q : Fin (t + 1), qminor (Eop E) (b ∘ p.succAbove) (a ∘ q.succAbove) (((t + 1 : ℕ) : ℂ) - 1 - w - 1) =
      ((-1 : ℂ) ^ t) • qminor E (a ∘ q.succAbove) (b ∘ p.succAbove) w := by
    intro p q
    rw [duality hE (a ∘ q.succAbove) (b ∘ p.succAbove) w, smul_smul, hs, one_smul]
    congr 1
    push_cast
    ring
  have key : ((-1 : ℂ) ^ (t + 1)) • ∑ p : Fin (t + 1), ∑ q : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ξ (a q)) •
        (y (b p) * qminor (Eop E) (b ∘ p.succAbove) (a ∘ q.succAbove) (((t + 1 : ℕ) : ℂ) - 1 - w - 1)) =
      -∑ p : Fin (t + 1), ∑ q : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ξ (a p)) •
        (y (b q) * qminor E (a ∘ p.succAbove) (b ∘ q.succAbove) w) := by
    rw [Finset.sum_comm, Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [d1, mul_smul_comm, smul_smul, smul_smul, ← neg_smul]
    congr 1
    linear_combination (-((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ξ (a p))) * hs
  rw [d0, smul_mul_assoc, z, mul_smul_comm, smul_add, key, ← sub_eq_add_neg]

end Alg4

section GlLev

open Qx2

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

/- English proof (translation)
Use `⟨?_, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_add, Matrix.add_mul, Matrix.mul_add]`. Establish `h1` using `hX.1`. Establish `h2` using `hY.1`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.add_mulVec, (hX.2 a ha).1, (hY.2 a ha).1, add_zero]`. Rewrite using `[Matrix.add_mulVec, (hX.2 a ha).2, (hY.2 a ha).2, add_zero]`.
-/
theorem lie_add {X Y : Mx k r} (hX : inLieLev k r i X) (hY : inLieLev k r i Y) : inLieLev k r i (X + Y) := by
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    have h1 := hX.1
    have h2 := hY.1
    calc _ = (Xᴴ * Hpk k r + Hpk k r * X) + (Yᴴ * Hpk k r + Hpk k r * Y) := by abel
      _ = 0 := by rw [h1, h2, add_zero]
  · rw [Matrix.add_mulVec, (hX.2 a ha).1, (hY.2 a ha).1, add_zero]
  · rw [Matrix.add_mulVec, (hX.2 a ha).2, (hY.2 a ha).2, add_zero]

/- English proof (translation)
Use `⟨?_, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX.1, neg_zero]`. Rewrite using `[Matrix.neg_mulVec, (hX.2 a ha).1, neg_zero]`. Rewrite using `[Matrix.neg_mulVec, (hX.2 a ha).2, neg_zero]`.
-/
theorem lie_neg {X : Mx k r} (hX : inLieLev k r i X) : inLieLev k r i (-X) := by
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hX.1, neg_zero]
  · rw [Matrix.neg_mulVec, (hX.2 a ha).1, neg_zero]
  · rw [Matrix.neg_mulVec, (hX.2 a ha).2, neg_zero]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `lie_add hX (lie_neg hY)`.
-/
theorem lie_sub {X Y : Mx k r} (hX : inLieLev k r i X) (hY : inLieLev k r i Y) : inLieLev k r i (X - Y) := by
  rw [sub_eq_add_neg]
  exact lie_add hX (lie_neg hY)

/- English proof (translation)
Use `⟨?_, fun a ha => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `hX' : Xᴴ * Hpk k r = -(Hpk k r * X)` using `eq_neg_of_add_eq_zero_left hX.1`. Establish `hY' : Yᴴ * Hpk k r = -(Hpk k r * Y)` using `eq_neg_of_add_eq_zero_left hY.1`. Establish `e1 : Yᴴ * Xᴴ * Hpk k r = Hpk k r * Y * X`. Rewrite using `[Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]`.

Establish `e2 : Xᴴ * Yᴴ * Hpk k r = Hpk k r * X * Y`. Rewrite using `[Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]`. Rewrite using `[conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Rewrite using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hX.2 a ha).1, (hY.2 a ha).1]`.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hX.2 a ha).2, (hY.2 a ha).2]`. Simplify using the standard rewrite rules.
-/
theorem lie_bracket {X Y : Mx k r} (hX : inLieLev k r i X) (hY : inLieLev k r i Y) :
    inLieLev k r i (X * Y - Y * X) := by
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · have hX' : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX.1
    have hY' : Yᴴ * Hpk k r = -(Hpk k r * Y) := eq_neg_of_add_eq_zero_left hY.1
    have e1 : Yᴴ * Xᴴ * Hpk k r = Hpk k r * Y * X := by
      rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hY', Matrix.neg_mul, neg_neg]
    have e2 : Xᴴ * Yᴴ * Hpk k r = Hpk k r * X * Y := by
      rw [Matrix.mul_assoc, hY', Matrix.mul_neg, ← Matrix.mul_assoc, hX', Matrix.neg_mul, neg_neg]
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Matrix.sub_mul, e1, e2,
      Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    abel
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hX.2 a ha).1, (hY.2 a ha).1]
    simp
  · rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, (hX.2 a ha).2, (hY.2 a ha).2]
    simp

/- English proof (translation)
The claim follows from `(hasDeriv_ext hU hgU hg hX ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)) he).deriv`.
-/
theorem rd_ext {f F : Mx k r → E} {U : Set (Mx k r)} (hU : IsOpen U) {g X : Mx k r} (hgU : g ∈ U)
    (hg : g ∈ Glev k r i) (hX : inLieLev k r i X) (hF : ContDiffOn ℝ ∞ F U)
    (he : ∀ x ∈ U, x ∈ Glev k r i → f x = F x) : RdV X f g = fderiv ℝ F g (g * X) :=
  (hasDeriv_ext hU hgU hg hX ((hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)) he).deriv

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g hg`. Rewrite using `[rd_ext hU hgU hg.1 (lie_add hX hY) hF he, rd_ext hU hgU hg.1 hX hF he, rd_ext hU hgU hg.1 hY hF he, Matrix.mul_add, map_add]`.
-/
theorem rd_addX {f : Mx k r → E} (hf : SmoothLev k r i D f) {g X Y : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hX : inLieLev k r i X) (hY : inLieLev k r i Y) : RdV (X + Y) f g = RdV X f g + RdV Y f g := by
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g hg
  rw [rd_ext hU hgU hg.1 (lie_add hX hY) hF he, rd_ext hU hgU hg.1 hX hF he, rd_ext hU hgU hg.1 hY hF he,
    Matrix.mul_add, map_add]

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g hg`. Rewrite using `[rd_ext hU hgU hg.1 (lie_sub hX hY) hF he, rd_ext hU hgU hg.1 hX hF he, rd_ext hU hgU hg.1 hY hF he, Matrix.mul_sub, map_sub]`.
-/
theorem rd_subX {f : Mx k r → E} (hf : SmoothLev k r i D f) {g X Y : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hX : inLieLev k r i X) (hY : inLieLev k r i Y) : RdV (X - Y) f g = RdV X f g - RdV Y f g := by
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g hg
  rw [rd_ext hU hgU hg.1 (lie_sub hX hY) hF he, rd_ext hU hgU hg.1 hX hF he, rd_ext hU hgU hg.1 hY hF he,
    Matrix.mul_sub, map_sub]

/- English proof (translation)
Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g hg`. Establish `hFa : ContDiffAt ℝ ∞ F g` using `hF.contDiffAt (hU.mem_nhds hgU)`. Establish `ext : ∀ Z, inLieLev k r i Z → ∀ x ∈ U, x ∈ Glev k r i → RdV Z f x = fderiv ℝ F x (x * Z)` using `fun Z hZ x hx hxG => rd_ext hU hx hxG hZ hF hfF`. Establish `hsm : ∀ Z : Mx k r, ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x (x * Z)) U` using `fun Z => (hF.fderiv_of_isOpen hU withTop_enat_infty_add_one_le_infty).clm_apply (mulRightRealCLM Z).contDiff.contDiffOn`. Establish `hc : DifferentiableAt ℝ (fderiv ℝ F) g` using `(hFa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)`.

Establish `hd : ∀ Z W : Mx k r, fderiv ℝ (fun x => fderiv ℝ F x (x * Z)) g W = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z)`. Introduce `Z W`. Establish `H` using `(hc.hasFDerivAt.clm_apply (mulRightRealCLM Z).hasFDerivAt).fderiv`. Use `erw [H]`. Conclude with `add_comm _ _`.

Establish `e1 : RdV X (RdV Y f) g = fderiv ℝ (fun x => fderiv ℝ F x (x * Y)) g (g * X)` using `rd_ext hU hgU hg.1 hX (hsm Y) (ext Y hY)`. Establish `e2 : RdV Y (RdV X f) g = fderiv ℝ (fun x => fderiv ℝ F x (x * X)) g (g * Y)` using `rd_ext hU hgU hg.1 hY (hsm X) (ext X hX)`. Establish `e3` using `ext _ (lie_bracket hX hY) g hgU hg.1`. Establish `hsym : IsSymmSndFDerivAt ℝ F g` using `hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)`. Establish `hs2` using `hsym (g * X) (g * Y)`.

Rewrite using `[e1, e2, e3, hd, hd]`. Simplify using `only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]`. Use `erw [hs2]`. Conclude with `add_sub_add_left_eq_sub _ _ _`.
-/
theorem rd_bracket {f : Mx k r → E} (hf : SmoothLev k r i D f) {g X Y : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hX : inLieLev k r i X) (hY : inLieLev k r i Y) :
    RdV X (RdV Y f) g - RdV Y (RdV X f) g = RdV (X * Y - Y * X) f g := by
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hFa : ContDiffAt ℝ ∞ F g := hF.contDiffAt (hU.mem_nhds hgU)
  have ext : ∀ Z, inLieLev k r i Z → ∀ x ∈ U, x ∈ Glev k r i → RdV Z f x = fderiv ℝ F x (x * Z) :=
    fun Z hZ x hx hxG => rd_ext hU hx hxG hZ hF hfF
  have hsm : ∀ Z : Mx k r, ContDiffOn ℝ ∞ (fun x => fderiv ℝ F x (x * Z)) U := fun Z =>
    (hF.fderiv_of_isOpen hU withTop_enat_infty_add_one_le_infty).clm_apply (mulRightRealCLM Z).contDiff.contDiffOn
  have hc : DifferentiableAt ℝ (fderiv ℝ F) g :=
    (hFa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
  have hd : ∀ Z W : Mx k r, fderiv ℝ (fun x => fderiv ℝ F x (x * Z)) g W
      = fderiv ℝ (fderiv ℝ F) g W (g * Z) + fderiv ℝ F g (W * Z) := by
    intro Z W
    have H := (hc.hasFDerivAt.clm_apply (mulRightRealCLM Z).hasFDerivAt).fderiv
    erw [H]
    exact add_comm _ _
  have e1 : RdV X (RdV Y f) g = fderiv ℝ (fun x => fderiv ℝ F x (x * Y)) g (g * X) :=
    rd_ext hU hgU hg.1 hX (hsm Y) (ext Y hY)
  have e2 : RdV Y (RdV X f) g = fderiv ℝ (fun x => fderiv ℝ F x (x * X)) g (g * Y) :=
    rd_ext hU hgU hg.1 hY (hsm X) (ext X hX)
  have e3 := ext _ (lie_bracket hX hY) g hgU hg.1
  have hsym : IsSymmSndFDerivAt ℝ F g :=
    hFa.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
  have hs2 := hsym (g * X) (g * Y)
  rw [e1, e2, e3, hd, hd]
  simp only [Matrix.mul_sub, Matrix.mul_assoc, map_sub]
  erw [hs2]
  exact add_sub_add_left_eq_sub _ _ _

/- English proof (translation)
Unfold `hpart1 hpart2`. Rewrite using `[smul_smul]`. Establish `: Complex.I * (1 / (2 * Complex.I)) = 1 / 2`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Use `module`.
-/
theorem hpart_sum (Z : Mx k r) : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    field_simp
  rw [this]
  module

/- English proof (translation)
Establish `hX' : Xᴴ * Hpk k r = -(Hpk k r * X)` using `eq_neg_of_add_eq_zero_left hX.1`. Rewrite using `[Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]`.
-/
theorem lie_HXH {X : Mx k r} (hX : inLieLev k r i X) : Hpk k r * Xᴴ * Hpk k r = -X := by
  have hX' : Xᴴ * Hpk k r = -(Hpk k r * X) := eq_neg_of_add_eq_zero_left hX.1
  rw [Matrix.mul_assoc, hX', Matrix.mul_neg, ← Matrix.mul_assoc, hpk_sq', Matrix.one_mul]

/- English proof (translation)
Establish `hZ : Hpk k r * (P + Complex.I • Q)ᴴ * Hpk k r = -P + Complex.I • Q`. Rewrite using `[conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, lie_HXH hP, lie_HXH hQ, Complex.star_def, Complex.conj_I]`. Use `module`. Unfold `hpart1 hpart2`. Rewrite using `[hpk_inv, hZ]`.

Prove the components needed by the constructor for the conclusion. Use `module`. Establish `: P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q` using `by module`. Rewrite using `[this, smul_smul, one_div, inv_mul_cancel₀ (by simp), one_smul]`.
-/
theorem hpart_unique {P Q : Mx k r} (hP : inLieLev k r i P) (hQ : inLieLev k r i Q) :
    hpart1 (Hpk k r) (P + Complex.I • Q) = P ∧ hpart2 (Hpk k r) (P + Complex.I • Q) = Q := by
  have hZ : Hpk k r * (P + Complex.I • Q)ᴴ * Hpk k r = -P + Complex.I • Q := by
    rw [conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, lie_HXH hP, lie_HXH hQ, Complex.star_def, Complex.conj_I]
    module
  unfold hpart1 hpart2
  rw [hpk_inv, hZ]
  constructor
  · module
  · have : P + Complex.I • Q + (-P + Complex.I • Q) = (2 * Complex.I) • Q := by module
    rw [this, smul_smul, one_div, inv_mul_cancel₀ (by simp), one_smul]

def LieC (k r : ℕ) (i : Fin (r + 1)) (Z : Mx k r) : Prop :=
  inLieLev k r i (hpart1 (Hpk k r) Z) ∧ inLieLev k r i (hpart2 (Hpk k r) Z)

/- English proof (translation)
Take `⟨hX1, hX2⟩` from `hZ`. Take `⟨hY1, hY2⟩` from `hW`. Establish `hEc : ∀ (Z' : Mx k r) (f' : Mx k r → E), RZ (Hpk k r) Z' f' g = RdV (hpart1 (Hpk k r) Z') f' g + Complex.I • RdV (hpart2 (Hpk k r) Z') f' g` using `fun _ _ => rfl`. Establish `hE : ∀ V, inLieLev k r i V → ∀ W' : Mx k r, LieC k r i W' → RdV V (RZ (Hpk k r) W' f) g = RdV V (RdV (hpart1 (Hpk k r) W') f) g + Complex.I • RdV V (RdV (hpart2 (Hpk k r) W') f) g` using `fun V hV W' hW' => rd_lin (rd_smooth hf hW'.1) (rd_smooth hf hW'.2) Complex.I hg hV`. Establish `hZW` using `commutator_complex_expand (hpart1 (Hpk k r) Z) (hpart2 (Hpk k r) Z) (hpart1 (Hpk k r) W) (hpart2 (Hpk k r) W)`.

Rewrite `hZW` using `[hpart_sum, hpart_sum]`. Establish `hP` using `lie_sub (lie_bracket hX1 hY1) (lie_bracket hX2 hY2)`. Establish `hQ` using `lie_add (lie_bracket hX1 hY2) (lie_bracket hX2 hY1)`. Take `⟨h1, h2⟩` from `hpart_unique hP hQ`. Rewrite using `[hEc Z, hEc W, hE _ hX1 _ ⟨hY1, hY2⟩, hE _ hX2 _ ⟨hY1, hY2⟩, hE _ hY1 _ ⟨hX1, hX2⟩, hE _ hY2 _ ⟨hX1, hX2⟩, hZW, hEc, h1, h2, rd_subX hf hg (lie_bracket hX1 hY1) (lie_bracket hX2 hY2), rd_addX hf hg (lie_bracket hX1 hY2) (lie_bracket hX2 hY1), ← rd_bracket hf hg hX1 hY1, ← rd_brac …`.

Simplify using `only [smul_add, smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul]`. Normalize the expressions using the abelian group laws.
-/
theorem RZ_comm {f : Mx k r → E} (hf : SmoothLev k r i D f) {g Z W : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hZ : LieC k r i Z) (hW : LieC k r i W) :
    RZ (Hpk k r) Z (RZ (Hpk k r) W f) g - RZ (Hpk k r) W (RZ (Hpk k r) Z f) g = RZ (Hpk k r) (Z * W - W * Z) f g := by
  obtain ⟨hX1, hX2⟩ := hZ
  obtain ⟨hY1, hY2⟩ := hW
  have hEc : ∀ (Z' : Mx k r) (f' : Mx k r → E),
      RZ (Hpk k r) Z' f' g = RdV (hpart1 (Hpk k r) Z') f' g + Complex.I • RdV (hpart2 (Hpk k r) Z') f' g :=
    fun _ _ => rfl
  have hE : ∀ V, inLieLev k r i V → ∀ W' : Mx k r, LieC k r i W' →
      RdV V (RZ (Hpk k r) W' f) g =
        RdV V (RdV (hpart1 (Hpk k r) W') f) g + Complex.I • RdV V (RdV (hpart2 (Hpk k r) W') f) g :=
    fun V hV W' hW' => rd_lin (rd_smooth hf hW'.1) (rd_smooth hf hW'.2) Complex.I hg hV
  have hZW := commutator_complex_expand (hpart1 (Hpk k r) Z) (hpart2 (Hpk k r) Z) (hpart1 (Hpk k r) W) (hpart2 (Hpk k r) W)
  rw [hpart_sum, hpart_sum] at hZW
  have hP := lie_sub (lie_bracket hX1 hY1) (lie_bracket hX2 hY2)
  have hQ := lie_add (lie_bracket hX1 hY2) (lie_bracket hX2 hY1)
  obtain ⟨h1, h2⟩ := hpart_unique hP hQ
  rw [hEc Z, hEc W, hE _ hX1 _ ⟨hY1, hY2⟩, hE _ hX2 _ ⟨hY1, hY2⟩, hE _ hY1 _ ⟨hX1, hX2⟩, hE _ hY2 _ ⟨hX1, hX2⟩, hZW, hEc,
    h1, h2, rd_subX hf hg (lie_bracket hX1 hY1) (lie_bracket hX2 hY2),
    rd_addX hf hg (lie_bracket hX1 hY2) (lie_bracket hX2 hY1),
    ← rd_bracket hf hg hX1 hY1, ← rd_bracket hf hg hX2 hY2, ← rd_bracket hf hg hX1 hY2, ← rd_bracket hf hg hX2 hY1]
  simp only [smul_add, smul_sub, smul_smul, Complex.I_mul_I, neg_smul, one_smul]
  abel

/- English proof (translation)
Unfold `hpart1`. Rewrite using `[conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]`. Use `module`.
-/
theorem hpart1_sub (Z W : Mx k r) : hpart1 (Hpk k r) (Z - W) = hpart1 (Hpk k r) Z - hpart1 (Hpk k r) W := by
  unfold hpart1
  rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

/- English proof (translation)
Unfold `hpart2`. Rewrite using `[conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]`. Use `module`.
-/
theorem hpart2_sub (Z W : Mx k r) : hpart2 (Hpk k r) (Z - W) = hpart2 (Hpk k r) Z - hpart2 (Hpk k r) W := by
  unfold hpart2
  rw [conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
  module

/- English proof (translation)
Unfold `RZ`. Rewrite using `[hpart1_sub, hpart2_sub, rd_subX hf hg hZ.1 hW.1, rd_subX hf hg hZ.2 hW.2, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem RZ_sub {f : Mx k r → E} (hf : SmoothLev k r i D f) {g Z W : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (hZ : LieC k r i Z) (hW : LieC k r i W) :
    RZ (Hpk k r) (Z - W) f g = RZ (Hpk k r) Z f g - RZ (Hpk k r) W f g := by
  unfold RZ
  rw [hpart1_sub, hpart2_sub, rd_subX hf hg hZ.1 hW.1, rd_subX hf hg hZ.2 hW.2, smul_sub]
  abel

/- English proof (translation)
Simplify using `[RZ, hpart1, hpart2, RdV]`.
-/
theorem RZ_zero (f : Mx k r → E) (g : Mx k r) : RZ (Hpk k r) 0 f g = 0 := by
  simp [RZ, hpart1, hpart2, RdV]

/- English proof (translation)
Establish `h : inLieLev k r i (0 : Mx k r)` using `⟨by simp, fun a _ => by simp⟩`. Prove the components needed by the constructor for the conclusion. Simplify `h` using `[hpart1]`. Simplify `h` using `[hpart2]`.
-/
theorem lieC_zero : LieC k r i 0 := by
  have h : inLieLev k r i (0 : Mx k r) := ⟨by simp, fun a _ => by simp⟩
  constructor
  · simpa [hpart1] using h
  · simpa [hpart2] using h

/- English proof (translation)
Establish `hL : ∀ p q : Fin (mdim k r i), LieC k r i (Matrix.single (posL k r i p) (posL k r i q) 1)` using `fun p q => hpart_lev i p q`. Establish `h` using `RZ_comm hf hg (hL a b) (hL c d)`. Establish `hm : Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * Matrix.single (posL k r i c) (posL k r i d) 1 - Matrix.single (posL k r i c) (posL k r i d) 1 * Matrix.single (posL k r i a) (posL k r i b) 1 = (if b = c then Matrix.single (posL k r i a) (posL k r i d) 1 else 0) - (if d …`. Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a`. Substitute `h1` using the available equality.

Substitute `h2` using the available equality. Simplify using the standard rewrite rules. Substitute `h1` using the available equality. Simplify using `[h2, (posL_inj i).ne h2]`. Substitute `h2` using the available equality.

Simplify using `[h1, (posL_inj i).ne h1]`. Simplify using `[h1, h2, (posL_inj i).ne h1, (posL_inj i).ne h2]`. Rewrite `h` using `[hm]`. Establish `h3 : RZ (Hpk k r) ((if b = c then Matrix.single (posL k r i a) (posL k r i d) 1 else 0) - (if d = a then Matrix.single (posL k r i c) (posL k r i b) 1 else 0)) f g = (if b = c then EH k r (posL k r i a) (posL k r i d) f g else 0) - (if d = a then EH k r (posL k r i c) (posL k r i …`. Rewrite using `[RZ_sub hf hg (by split_ifs; exacts [hL _ _, lieC_zero]) (by split_ifs; exacts [hL _ _, lieC_zero])]`.

Apply the tactic sequence `split_ifs <;> first | rfl | (simp only [RZ_zero]; done) | (simp only [RZ_zero]; rfl)`. Rewrite using `[← h3, ← h]`. Both sides reduce to the same expression.
-/
theorem eh_gl {f : Mx k r → E} (hf : SmoothLev k r i D f) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D)
    (a b c d : Fin (mdim k r i)) :
    EH k r (posL k r i a) (posL k r i b) (EH k r (posL k r i c) (posL k r i d) f) g -
        EH k r (posL k r i c) (posL k r i d) (EH k r (posL k r i a) (posL k r i b) f) g =
      (if b = c then EH k r (posL k r i a) (posL k r i d) f g else 0) -
        (if d = a then EH k r (posL k r i c) (posL k r i b) f g else 0) := by
  have hL : ∀ p q : Fin (mdim k r i), LieC k r i (Matrix.single (posL k r i p) (posL k r i q) 1) := fun p q => hpart_lev i p q
  have h := RZ_comm hf hg (hL a b) (hL c d)
  have hm : Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ) * Matrix.single (posL k r i c) (posL k r i d) 1 -
      Matrix.single (posL k r i c) (posL k r i d) 1 * Matrix.single (posL k r i a) (posL k r i b) 1 =
      (if b = c then Matrix.single (posL k r i a) (posL k r i d) 1 else 0) -
        (if d = a then Matrix.single (posL k r i c) (posL k r i b) 1 else 0) := by
    by_cases h1 : b = c <;> by_cases h2 : d = a
    · subst h1; subst h2; simp
    · subst h1; simp [h2, (posL_inj i).ne h2]
    · subst h2; simp [h1, (posL_inj i).ne h1]
    · simp [h1, h2, (posL_inj i).ne h1, (posL_inj i).ne h2]
  rw [hm] at h
  have h3 : RZ (Hpk k r) ((if b = c then Matrix.single (posL k r i a) (posL k r i d) 1 else 0) -
        (if d = a then Matrix.single (posL k r i c) (posL k r i b) 1 else 0)) f g =
      (if b = c then EH k r (posL k r i a) (posL k r i d) f g else 0) -
        (if d = a then EH k r (posL k r i c) (posL k r i b) f g else 0) := by
    rw [RZ_sub hf hg (by split_ifs; exacts [hL _ _, lieC_zero]) (by split_ifs; exacts [hL _ _, lieC_zero])]
    split_ifs <;> first | rfl | (simp only [RZ_zero]; done) | (simp only [RZ_zero]; rfl)
  rw [← h3, ← h]
  rfl

end GlLev

section Leib

open Qx2

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g₀ hg₀`. Take `⟨U₂, C, hU₂, hgU₂, hC, he₂⟩` from `hc g₀ hg₀`. Use `⟨U ∩ U₂, fun x => C x • F x, hU.inter hU₂, ⟨hgU, hgU₂⟩, (hC.mono Set.inter_subset_right).smul (hF.mono Set.inter_subset_left), fun x hx hxG => ?_⟩` and prove the remaining obligations. Use `show c x • f x = C x • F x`.

Rewrite using `[he x hx.1 hxG, he₂ x hx.2 hxG]`.
-/
theorem smooth_mul {c : Mx k r → ℂ} {f : Mx k r → E} (hc : SmoothLev k r i D c) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (fun y => c y • f y) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  obtain ⟨U₂, C, hU₂, hgU₂, hC, he₂⟩ := hc g₀ hg₀
  refine ⟨U ∩ U₂, fun x => C x • F x, hU.inter hU₂, ⟨hgU, hgU₂⟩,
    (hC.mono Set.inter_subset_right).smul (hF.mono Set.inter_subset_left), fun x hx hxG => ?_⟩
  show c x • f x = C x • F x
  rw [he x hx.1 hxG, he₂ x hx.2 hxG]

/- English proof (translation)
Establish `h` using `((rd_hasDeriv hc hg hX).smul (rd_hasDeriv hf hg hX)).deriv`. Rewrite `h` using `[B5.curve_zero]`. Conclude with `h`.
-/
theorem rd_leib {c : Mx k r → ℂ} {f : Mx k r → E} (hc : SmoothLev k r i D c) (hf : SmoothLev k r i D f)
    {g X : Mx k r} (hg : g ∈ Glev k r i ∩ D) (hX : inLieLev k r i X) :
    RdV X (fun y => c y • f y) g = c g • RdV X f g + RdV X c g • f g := by
  have h := ((rd_hasDeriv hc hg hX).smul (rd_hasDeriv hf hg hX)).deriv
  rw [B5.curve_zero] at h
  exact h

/- English proof (translation)
Use `show RdV _ _ g + Complex.I • RdV _ _ g = c g • (RdV _ f g + Complex.I • RdV _ f g) + (RdV _ c g + Complex.I • RdV _ c g) • f g`. Rewrite using `[rd_leib hc hf hg (hpart_lev i a b).1, rd_leib hc hf hg (hpart_lev i a b).2]`. Simplify using `only [smul_eq_mul]`. Use `module`.
-/
theorem eh_leib {c : Mx k r → ℂ} {f : Mx k r → E} (hc : SmoothLev k r i D c) (hf : SmoothLev k r i D f)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) (a b : Fin (mdim k r i)) :
    EH k r (posL k r i a) (posL k r i b) (fun y => c y • f y) g =
      c g • EH k r (posL k r i a) (posL k r i b) f g + EH k r (posL k r i a) (posL k r i b) c g • f g := by
  show RdV _ _ g + Complex.I • RdV _ _ g = c g • (RdV _ f g + Complex.I • RdV _ f g) +
    (RdV _ c g + Complex.I • RdV _ c g) • f g
  rw [rd_leib hc hf hg (hpart_lev i a b).1, rd_leib hc hf hg (hpart_lev i a b).2]
  simp only [smul_eq_mul]
  module

/- English proof (translation)
The claim follows from `(((LinearMap.toContinuousLinearMap L).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_mul_exp_smul_zero g X)).deriv`.
-/
theorem rd_linear (L : Mx k r →ₗ[ℂ] ℂ) (g X : Mx k r) : RdV X (fun y => L y) g = L (g * X) :=
  (((LinearMap.toContinuousLinearMap L).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_mul_exp_smul_zero g X)).deriv

/- English proof (translation)
Use `show RdV _ _ g + Complex.I • RdV _ _ g = _`. Rewrite using `[rd_linear, rd_linear, ← map_smul, ← map_add, ← Matrix.mul_smul, ← Matrix.mul_add, hpart_sum]`.
-/
theorem eh_linear (L : Mx k r →ₗ[ℂ] ℂ) (g : Mx k r) (p q : Fin (2 * r + k + 1)) :
    EH k r p q (fun y => L y) g = L (g * Matrix.single p q 1) := by
  show RdV _ _ g + Complex.I • RdV _ _ g = _
  rw [rd_linear, rd_linear, ← map_smul, ← map_add, ← Matrix.mul_smul, ← Matrix.mul_add, hpart_sum]

/- English proof (translation)
Introduce `_ _` and use `⟨Set.univ, fun y => L y, isOpen_univ, trivial, (((LinearMap.toContinuousLinearMap L).contDiff (n := ∞)).restrict_scalars ℝ).contDiffOn, fun _ _ _ => rfl⟩`.
-/
theorem smooth_linear (L : Mx k r →ₗ[ℂ] ℂ) : SmoothLev k r i D (fun y => L y) := fun _ _ =>
  ⟨Set.univ, fun y => L y, isOpen_univ, trivial,
    (((LinearMap.toContinuousLinearMap L).contDiff (n := ∞)).restrict_scalars ℝ).contDiffOn, fun _ _ _ => rfl⟩

def actL (Λ : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (u : Fin (2 * r + k + 1) → ℂ) : Mx k r →ₗ[ℂ] ℂ where
  toFun M := Λ (M *ᵥ u)
  map_add' a b := by rw [Matrix.add_mulVec, map_add]
  map_smul' a b := by rw [Matrix.smul_mulVec, map_smul]; rfl

/- English proof (translation)
Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[smul_neg, ← Matrix.exp_add_of_commute ((t : ℂ) • X) (-((t : ℂ) • X)) (Commute.neg_right (Commute.refl ((t : ℂ) • X))), add_neg_cancel, NormedSpace.exp_zero]`.
-/
theorem exp_inv (X : Mx k r) (t : ℝ) : (NormedSpace.exp ((t : ℂ) • X))⁻¹ = NormedSpace.exp ((t : ℂ) • (-X)) := by
  apply Matrix.inv_eq_right_inv
  rw [smul_neg, ← Matrix.exp_add_of_commute ((t : ℂ) • X) (-((t : ℂ) • X)) (Commute.neg_right (Commute.refl ((t : ℂ) • X))),
    add_neg_cancel, NormedSpace.exp_zero]

/- English proof (translation)
Establish `h` using `rd_linear (actL Λ (g⁻¹ *ᵥ v)) 1 (-X)`. Establish `e : RdV X (fun y => Λ (y⁻¹ *ᵥ v)) g = RdV (-X) (fun y => actL Λ (g⁻¹ *ᵥ v) y) 1`. Unfold `RdV`. Use `congr 1`. Use function extensionality and compare the values at `t`.

Use `show Λ ((g * NormedSpace.exp ((t : ℂ) • X))⁻¹ *ᵥ v) = Λ ((1 * NormedSpace.exp ((t : ℂ) • (-X))) *ᵥ (g⁻¹ *ᵥ v))`. Rewrite using `[Matrix.mul_inv_rev, exp_inv, Matrix.one_mul, Matrix.mulVec_mulVec]`. Rewrite using `[e, h]`. Use `show Λ ((1 * -X) *ᵥ (g⁻¹ *ᵥ v)) = _`. Rewrite using `[Matrix.one_mul, Matrix.neg_mulVec, map_neg]`.
-/
theorem rd_inv (Λ : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (v : Fin (2 * r + k + 1) → ℂ) (g X : Mx k r) :
    RdV X (fun y => Λ (y⁻¹ *ᵥ v)) g = -Λ (X *ᵥ (g⁻¹ *ᵥ v)) := by
  have h := rd_linear (actL Λ (g⁻¹ *ᵥ v)) 1 (-X)
  have e : RdV X (fun y => Λ (y⁻¹ *ᵥ v)) g = RdV (-X) (fun y => actL Λ (g⁻¹ *ᵥ v) y) 1 := by
    unfold RdV
    congr 1
    funext t
    show Λ ((g * NormedSpace.exp ((t : ℂ) • X))⁻¹ *ᵥ v) = Λ ((1 * NormedSpace.exp ((t : ℂ) • (-X))) *ᵥ (g⁻¹ *ᵥ v))
    rw [Matrix.mul_inv_rev, exp_inv, Matrix.one_mul, Matrix.mulVec_mulVec]
  rw [e, h]
  show Λ ((1 * -X) *ᵥ (g⁻¹ *ᵥ v)) = _
  rw [Matrix.one_mul, Matrix.neg_mulVec, map_neg]

/- English proof (translation)
Use `show RdV _ _ g + Complex.I • RdV _ _ g = _`. Rewrite using `[rd_inv, rd_inv, smul_neg, ← neg_add, ← map_smul, ← map_add, ← Matrix.smul_mulVec, ← Matrix.add_mulVec, hpart_sum]`.
-/
theorem eh_inv (Λ : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (v : Fin (2 * r + k + 1) → ℂ) (g : Mx k r)
    (p q : Fin (2 * r + k + 1)) :
    EH k r p q (fun y => Λ (y⁻¹ *ᵥ v)) g = -Λ ((Matrix.single p q 1 : Mx k r) *ᵥ (g⁻¹ *ᵥ v)) := by
  show RdV _ _ g + Complex.I • RdV _ _ g = _
  rw [rd_inv, rd_inv, smul_neg, ← neg_add, ← map_smul, ← map_add, ← Matrix.smul_mulVec, ← Matrix.add_mulVec,
    hpart_sum]

/- English proof (translation)
Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uh_inv_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', hpk_sq']

/- English proof (translation)
Set `L : Mx k r →ₗ[ℝ] ℂ` to `{ toFun := fun g => Λ ((Hpk k r * gᴴ * Hpk k r) *ᵥ v) map_add' := fun x y => by`. Simplify using `[Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]`. Use the proof step `map_smul' := fun c x => by`. Simplify using `[Matrix.conjTranspose_smul, Matrix.smul_mulVec] }`. Introduce `g₀ _`.

Use `⟨Set.univ, fun y => L y, isOpen_univ, trivial, (LinearMap.toContinuousLinearMap L).contDiff.contDiffOn, fun y _ hy => ?_⟩` and prove the remaining obligations. Use `show Λ (y⁻¹ *ᵥ v) = Λ ((Hpk k r * yᴴ * Hpk k r) *ᵥ v)`. Rewrite using `[uh_inv_eq hy.1]`.
-/
theorem smooth_inv (Λ : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    SmoothLev k r i D (fun y => Λ (y⁻¹ *ᵥ v)) := by
  let L : Mx k r →ₗ[ℝ] ℂ :=
    { toFun := fun g => Λ ((Hpk k r * gᴴ * Hpk k r) *ᵥ v)
      map_add' := fun x y => by
        simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
      map_smul' := fun c x => by
        simp [Matrix.conjTranspose_smul, Matrix.smul_mulVec] }
  intro g₀ _
  refine ⟨Set.univ, fun y => L y, isOpen_univ, trivial, (LinearMap.toContinuousLinearMap L).contDiff.contDiffOn,
    fun y _ hy => ?_⟩
  show Λ (y⁻¹ *ᵥ v) = Λ ((Hpk k r * yᴴ * Hpk k r) *ᵥ v)
  rw [uh_inv_eq hy.1]

end Leib

section OpRing

open Qx2

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

def VS (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Submodule ℂ (Mx k r → E) where
  carrier := {f | SmoothLev k r i D f ∧ ∀ x, x ∉ Glev k r i ∩ D → f x = 0}
  zero_mem' := ⟨smooth_zero, fun _ _ => rfl⟩
  add_mem' := fun {f g} hf hg => ⟨smooth_add hf.1 hg.1, fun x hx => by simp [hf.2 x hx, hg.2 x hx]⟩
  smul_mem' := fun c f hf => ⟨smooth_smul hf.1 c, fun x hx => by simp [hf.2 x hx]⟩

def cut (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (f : Mx k r → E) : Mx k r → E := (Glev k r i ∩ D).indicator f

/- English proof (translation)
The claim follows from `Set.indicator_of_mem hg f`.
-/
theorem cut_of_mem (f : Mx k r → E) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : cut k r i D f g = f g :=
  Set.indicator_of_mem hg f

/- English proof (translation)
Use `⟨fun g₀ hg₀ => ?_, fun x hx => Set.indicator_of_notMem hx f⟩` and prove the remaining obligations. Take `⟨U, F, hU, hgU, hF, he⟩` from `hf g₀ hg₀`. Conclude with `⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgl => by rw [cut_of_mem f ⟨hgl, hg.2⟩, he g hg.1 hgl]⟩`.
-/
theorem cut_mem (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) : cut k r i D f ∈ VS k r i D E := by
  refine ⟨fun g₀ hg₀ => ?_, fun x hx => Set.indicator_of_notMem hx f⟩
  obtain ⟨U, F, hU, hgU, hF, he⟩ := hf g₀ hg₀
  exact ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left,
    fun g hg hgl => by rw [cut_of_mem f ⟨hgl, hg.2⟩, he g hg.1 hgl]⟩

def hat (hD : IsOpen D) (T : (Mx k r → E) → Mx k r → E) (hT : Good k r i D T) : Module.End ℂ (VS k r i D E) :=
  mkEnd (VS k r i D E) (fun f => cut k r i D (T f)) (fun f hf => cut_mem hD (hT.sm f hf.1))
    (fun x hx y hy s => by
      funext g
      by_cases hg : g ∈ Glev k r i ∩ D
      · show cut k r i D (T (x + s • y)) g = cut k r i D (T x) g + s • cut k r i D (T y) g
        rw [cut_of_mem _ hg, cut_of_mem _ hg, cut_of_mem _ hg]
        exact hT.lin x y s hx.1 hy.1 g hg
      · show cut k r i D (T (x + s • y)) g = cut k r i D (T x) g + s • cut k r i D (T y) g
        simp [cut, Set.indicator_of_notMem hg])

def Rep (X : Module.End ℂ (VS k r i D E)) (T : (Mx k r → E) → Mx k r → E) : Prop :=
  ∀ v : VS k r i D E, ∀ g ∈ Glev k r i ∩ D, (X v : Mx k r → E) g = T (v : Mx k r → E) g

/- English proof (translation)
Introduce `_ _ hg` and use `cut_of_mem _ hg`.
-/
theorem rep_hat (hD : IsOpen D) (T : (Mx k r → E) → Mx k r → E) (hT : Good k r i D T) : Rep (hat hD T hT) T :=
  fun _ _ hg => cut_of_mem _ hg

/- English proof (translation)
Introduce `v g hg` and use `by rw [Module.End.mul_apply, hX _ g hg] exact hT.loc _ _ (hY v) g hg`.
-/
theorem Rep.mul {X Y : Module.End ℂ (VS k r i D E)} {T U : (Mx k r → E) → Mx k r → E} (hX : Rep X T) (hY : Rep Y U)
    (hT : Good k r i D T) : Rep (X * Y) (fun f => T (U f)) := fun v g hg => by
  rw [Module.End.mul_apply, hX _ g hg]
  exact hT.loc _ _ (hY v) g hg

/- English proof (translation)
Use `LinearMap.ext fun v => Subtype.ext (funext fun g => ?_)` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ Glev k r i ∩ D`. Conclude with `h v g hg`. Rewrite using `[(X v).2.2 g hg, (Y v).2.2 g hg]`.
-/
theorem end_ext {X Y : Module.End ℂ (VS k r i D E)}
    (h : ∀ v : VS k r i D E, ∀ g ∈ Glev k r i ∩ D, (X v : Mx k r → E) g = (Y v : Mx k r → E) g) : X = Y := by
  refine LinearMap.ext fun v => Subtype.ext (funext fun g => ?_)
  by_cases hg : g ∈ Glev k r i ∩ D
  · exact h v g hg
  · rw [(X v).2.2 g hg, (Y v).2.2 g hg]

def Eh (hD : IsOpen D) (a b : Fin (mdim k r i)) : Module.End ℂ (VS k r i D E) := hat hD _ (good_eh hD a b)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ hf => smooth_mul hc hf, fun f f₂ h x hx => by simp only [h x hx], fun f f₂ s _ _ x _ => by simp only [smul_add, smul_comm (c x) s]⟩`.
-/
theorem good_mul {c : Mx k r → ℂ} (hc : SmoothLev k r i D c) :
    Good k r i D (fun (f : Mx k r → E) y => c y • f y) :=
  ⟨fun _ hf => smooth_mul hc hf, fun f f₂ h x hx => by simp only [h x hx],
    fun f f₂ s _ _ x _ => by simp only [smul_add, smul_comm (c x) s]⟩

def Mh (hD : IsOpen D) (c : Mx k r → ℂ) (hc : SmoothLev k r i D c) : Module.End ℂ (VS k r i D E) :=
  hat hD _ (good_mul hc)

/- English proof (translation)
The claim follows from `rep_hat hD _ _ v g hg`.
-/
theorem ev_E (hD : IsOpen D) (a b : Fin (mdim k r i)) (v : VS k r i D E) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (Eh hD a b v : Mx k r → E) g = EH k r (posL k r i a) (posL k r i b) (v : Mx k r → E) g := rep_hat hD _ _ v g hg

/- English proof (translation)
The claim follows from `rep_hat hD _ _ v g hg`.
-/
theorem ev_M (hD : IsOpen D) {c : Mx k r → ℂ} (hc : SmoothLev k r i D c) (v : VS k r i D E) {g : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) : (Mh hD c hc v : Mx k r → E) g = c g • (v : Mx k r → E) g := rep_hat hD _ _ v g hg

/- English proof (translation)
Rewrite using `[ev_E hD a b _ hg, (good_eh hD a b).loc _ (fun y => c y • (v : Mx k r → E) y) (fun x hx => ev_M hD hc v hx) g hg]`. Conclude with `eh_leib hc v.2.1 hg a b`.
-/
theorem ev_EM (hD : IsOpen D) (a b : Fin (mdim k r i)) {c : Mx k r → ℂ} (hc : SmoothLev k r i D c) (v : VS k r i D E)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (Eh hD a b (Mh hD c hc v) : Mx k r → E) g =
      c g • EH k r (posL k r i a) (posL k r i b) (v : Mx k r → E) g +
        EH k r (posL k r i a) (posL k r i b) c g • (v : Mx k r → E) g := by
  rw [ev_E hD a b _ hg, (good_eh hD a b).loc _ (fun y => c y • (v : Mx k r → E) y) (fun x hx => ev_M hD hc v hx) g hg]
  exact eh_leib hc v.2.1 hg a b

/- English proof (translation)
Rewrite using `[LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, ev_EM hD a b hc v hg, ev_M hD hc _ hg, ev_E hD a b v hg]`. Normalize the expressions using the abelian group laws.
-/
theorem comm_EM (hD : IsOpen D) (a b : Fin (mdim k r i)) {c : Mx k r → ℂ} (hc : SmoothLev k r i D c) (v : VS k r i D E)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (((Eh hD a b * Mh hD c hc - Mh hD c hc * Eh hD a b : Module.End ℂ (VS k r i D E)) v : VS k r i D E) : Mx k r → E) g =
      EH k r (posL k r i a) (posL k r i b) c g • (v : Mx k r → E) g := by
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, ev_EM hD a b hc v hg,
    ev_M hD hc _ hg, ev_E hD a b v hg]
  abel

/- English proof (translation)
Introduce `a b c d`. Use `end_ext fun v g hg => ?_` and prove the remaining obligations. Establish `h` using `eh_gl v.2.1 hg a b c d`. Establish `e1 : (Eh hD a b (Eh hD c d v) : Mx k r → E) g = EH k r (posL k r i a) (posL k r i b) (EH k r (posL k r i c) (posL k r i d) (v : Mx k r → E)) g`. Rewrite using `[ev_E hD a b _ hg]`.

Conclude with `(good_eh hD a b).loc _ _ (fun x hx => ev_E hD c d v hx) g hg`. Establish `e2 : (Eh hD c d (Eh hD a b v) : Mx k r → E) g = EH k r (posL k r i c) (posL k r i d) (EH k r (posL k r i a) (posL k r i b) (v : Mx k r → E)) g`. Rewrite using `[ev_E hD c d _ hg]`. Conclude with `(good_eh hD c d).loc _ _ (fun x hx => ev_E hD a b v hx) g hg`. Rewrite using `[LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, e1, e2, h, LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply]`.

Use `congr 1`. Use `split_ifs`. Conclude with `(ev_E hD a d v hg).symm`. Both sides reduce to the same expression. Use `split_ifs`.

Conclude with `(ev_E hD c b v hg).symm`. Both sides reduce to the same expression.
-/
theorem Eh_gl (hD : IsOpen D) : GlRel (Eh (E := E) (i := i) hD) := by
  intro a b c d
  refine end_ext fun v g hg => ?_
  have h := eh_gl v.2.1 hg a b c d
  have e1 : (Eh hD a b (Eh hD c d v) : Mx k r → E) g =
      EH k r (posL k r i a) (posL k r i b) (EH k r (posL k r i c) (posL k r i d) (v : Mx k r → E)) g := by
    rw [ev_E hD a b _ hg]
    exact (good_eh hD a b).loc _ _ (fun x hx => ev_E hD c d v hx) g hg
  have e2 : (Eh hD c d (Eh hD a b v) : Mx k r → E) g =
      EH k r (posL k r i c) (posL k r i d) (EH k r (posL k r i a) (posL k r i b) (v : Mx k r → E)) g := by
    rw [ev_E hD c d _ hg]
    exact (good_eh hD c d).loc _ _ (fun x hx => ev_E hD a b v hx) g hg
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply, e1, e2, h,
    LinearMap.sub_apply, Submodule.coe_sub, Pi.sub_apply]
  congr 1
  · split_ifs
    · exact (ev_E hD a d v hg).symm
    · rfl
  · split_ifs
    · exact (ev_E hD c b v hg).symm
    · rfl

/- English proof (translation)
Introduce `v g hg`. Unfold `Tm QuantumDeterminants.Top`. Rewrite using `[LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, ev_E hD a b v hg]`. Use `congr 1`. Distinguish the cases in `h : a = b`.

Rewrite using `[if_pos h, if_pos (congrArg _ h), Module.algebraMap_end_apply]`. Both sides reduce to the same expression. Rewrite using `[if_neg h, if_neg ((posL_inj i).ne h)]`. Both sides reduce to the same expression.
-/
theorem rep_Tm (hD : IsOpen D) (u : ℂ) (a b : Fin (mdim k r i)) :
    Rep (Tm (Eh (E := E) hD) u a b) (QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b)) := by
  intro v g hg
  unfold Tm QuantumDeterminants.Top
  rw [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, ev_E hD a b v hg]
  congr 1
  by_cases h : a = b
  · rw [if_pos h, if_pos (congrArg _ h), Module.algebraMap_end_apply]
    rfl
  · rw [if_neg h, if_neg ((posL_inj i).ne h)]
    rfl

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => exact fun _ _ _ => rfl`. Consider the case `cons p L ih`. Simplify using `only [List.map_cons, List.prod_cons, List.foldr_cons]`. Conclude with `(rep_Tm hD p.1 p.2.1 p.2.2).mul ih (good_top hD _ _ _)`.
-/
theorem rep_prod (hD : IsOpen D) (L : List (ℂ × Fin (mdim k r i) × Fin (mdim k r i))) :
    Rep ((L.map fun p => Tm (Eh (E := E) hD) p.1 p.2.1 p.2.2).prod)
      (fun f => (L.map fun p => QuantumDeterminants.Top (EH k r) p.1 (posL k r i p.2.1) (posL k r i p.2.2)).foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact fun _ _ _ => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.prod_cons, List.foldr_cons]
    exact (rep_Tm hD p.1 p.2.1 p.2.2).mul ih (good_top hD _ _ _)

/- English proof (translation)
Introduce `v g hg`. Unfold `qminor qminorOp`. Simplify using `only [intCast_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Use `congr 1`.

Establish `h` using `rep_prod (E := E) hD (List.ofFn fun l : Fin t => ((u - ((l : ℕ) : ℂ), a (σ l), b l) : ℂ × Fin (mdim k r i) × Fin (mdim k r i))) v g hg`. Simplify using `only [List.map_ofFn] at h`. Conclude with `h`.
-/
theorem rep_qminor (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    Rep (qminor (Eh (E := E) hD) a b u) (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u) := by
  intro v g hg
  unfold qminor qminorOp
  simp only [intCast_smul, LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
    Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have h := rep_prod (E := E) hD (List.ofFn fun l : Fin t => ((u - ((l : ℕ) : ℂ), a (σ l), b l) :
    ℂ × Fin (mdim k r i) × Fin (mdim k r i))) v g hg
  simp only [List.map_ofFn] at h
  exact h

end OpRing

section Concrete

open Qx2

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

def hermL (k r : ℕ) (x₀ : Fin (2 * r + k + 1) → ℂ) : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun v := herm (Hpk k r) v x₀
  map_add' a b := by simp [herm, Matrix.mulVec_add, dotProduct_add]
  map_smul' a b := by simp [herm, Matrix.mulVec_smul, dotProduct_smul]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.single_apply, bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul]`. Distinguish the cases in `h : p = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h, Ne.symm h]`.
-/
theorem single_mulVec' (p q : Fin (2 * r + k + 1)) (u : Fin (2 * r + k + 1) → ℂ) :
    (Matrix.single p q (1 : ℂ) : Mx k r) *ᵥ u = u q • bvec p := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, bvec, Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases h : p = j
  · subst h
    simp
  · simp [h, Ne.symm h]

/- English proof (translation)
Establish `h` using `eh_linear (actL Λ u) g p q`. Establish `e : actL Λ u (g * Matrix.single p q 1) = u q * Λ (g *ᵥ bvec p)` using `by show Λ ((g * Matrix.single p q 1) *ᵥ u) = _`. Rewrite using `[← Matrix.mulVec_mulVec, single_mulVec', Matrix.mulVec_smul, map_smul, smul_eq_mul]`. Rewrite using `[← e, ← h]`. Both sides reduce to the same expression.
-/
theorem eh_act (Λ : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] ℂ) (u : Fin (2 * r + k + 1) → ℂ) (g : Mx k r)
    (p q : Fin (2 * r + k + 1)) : EH k r p q (fun y => Λ (y *ᵥ u)) g = u q * Λ (g *ᵥ bvec p) := by
  have h := eh_linear (actL Λ u) g p q
  have e : actL Λ u (g * Matrix.single p q 1) = u q * Λ (g *ᵥ bvec p) := by
    show Λ ((g * Matrix.single p q 1) *ᵥ u) = _
    rw [← Matrix.mulVec_mulVec, single_mulVec', Matrix.mulVec_smul, map_smul, smul_eq_mul]
  rw [← e, ← h]
  rfl

/- English proof (translation)
Unfold `bvec`. Rewrite using `[Pi.single_apply]`. Distinguish the cases in `h : b = a`. Simplify using `[h]`. Simplify using `[h, (posL_inj i).ne h]`.
-/
theorem bvec_posL (a b : Fin (mdim k r i)) : bvec (posL k r i a) (posL k r i b) = if b = a then (1 : ℂ) else 0 := by
  unfold bvec
  rw [Pi.single_apply]
  by_cases h : b = a
  · simp [h]
  · simp [h, (posL_inj i).ne h]

variable (z z' : Fin (2 * r + k + 1) → ℂ)

/- English proof (translation)
The claim follows from `smooth_linear (actL (hermL k r (fvec k r z i)) (bvec (posL k r i c)))`.
-/
theorem sm_eta (c : Fin (mdim k r i)) : SmoothLev k r i D (fun g => ybv k r z i g c) :=
  smooth_linear (actL (hermL k r (fvec k r z i)) (bvec (posL k r i c)))

/- English proof (translation)
The claim follows from `smooth_linear (actL (hermL k r (fvec k r z i)) (fvec k r z' i))`.
-/
theorem sm_zeta : SmoothLev k r i D (zetaL k r z z' i) :=
  smooth_linear (actL (hermL k r (fvec k r z i)) (fvec k r z' i))

/- English proof (translation)
The claim follows from `smooth_inv (LinearMap.proj (posL k r i c)) (fvec k r z i)`.
-/
theorem sm_y (c : Fin (mdim k r i)) : SmoothLev k r i D (fun g => yv k r z i g c) :=
  smooth_inv (LinearMap.proj (posL k r i c)) (fvec k r z i)

def zbF (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (g : Mx k r) : ℂ :=
  herm (Hpk k r) (g⁻¹ *ᵥ fvec k r z i) (fvec k r z' i)

/- English proof (translation)
The claim follows from `smooth_inv (hermL k r (fvec k r z' i)) (fvec k r z i)`.
-/
theorem sm_zb : SmoothLev k r i D (zbF k r z z' i) := smooth_inv (hermL k r (fvec k r z' i)) (fvec k r z i)

/- English proof (translation)
Establish `h` using `eh_act (hermL k r (fvec k r z i)) (bvec (posL k r i c)) g (posL k r i a) (posL k r i b)`. Rewrite `h` using `[bvec_posL]`. Use `Eq.trans h ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[one_mul]`.

Both sides reduce to the same expression. Rewrite using `[zero_mul]`.
-/
theorem eh_eta (a b c : Fin (mdim k r i)) (g : Mx k r) :
    EH k r (posL k r i a) (posL k r i b) (fun g => ybv k r z i g c) g = if b = c then ybv k r z i g a else 0 := by
  have h := eh_act (hermL k r (fvec k r z i)) (bvec (posL k r i c)) g (posL k r i a) (posL k r i b)
  rw [bvec_posL] at h
  refine Eq.trans h ?_
  split_ifs
  · rw [one_mul]; rfl
  · rw [zero_mul]

/- English proof (translation)
The claim follows from `eh_act (hermL k r (fvec k r z i)) (fvec k r z' i) g (posL k r i a) (posL k r i b)`.
-/
theorem eh_zeta (a b : Fin (mdim k r i)) (g : Mx k r) :
    EH k r (posL k r i a) (posL k r i b) (zetaL k r z z' i) g = xv k r z' i b * ybv k r z i g a :=
  eh_act (hermL k r (fvec k r z i)) (fvec k r z' i) g (posL k r i a) (posL k r i b)

/- English proof (translation)
Establish `h` using `eh_inv (LinearMap.proj (posL k r i c)) (fvec k r z i) g (posL k r i a) (posL k r i b)`. Use `Eq.trans h ?_` and prove the remaining obligations. Rewrite using `[single_mulVec', LinearMap.proj_apply, Pi.smul_apply, bvec_posL, smul_eq_mul]`. Distinguish the cases in `hac : a = c`. Rewrite using `[if_pos hac, if_pos hac.symm, mul_one]`.

Both sides reduce to the same expression. Rewrite using `[if_neg hac, if_neg (Ne.symm hac), mul_zero, neg_zero]`.
-/
theorem eh_y (a b c : Fin (mdim k r i)) (g : Mx k r) :
    EH k r (posL k r i a) (posL k r i b) (fun g => yv k r z i g c) g = if a = c then -yv k r z i g b else 0 := by
  have h := eh_inv (LinearMap.proj (posL k r i c)) (fvec k r z i) g (posL k r i a) (posL k r i b)
  refine Eq.trans h ?_
  rw [single_mulVec', LinearMap.proj_apply, Pi.smul_apply, bvec_posL, smul_eq_mul]
  by_cases hac : a = c
  · rw [if_pos hac, if_pos hac.symm, mul_one]; rfl
  · rw [if_neg hac, if_neg (Ne.symm hac), mul_zero, neg_zero]

/- English proof (translation)
Establish `h` using `eh_inv (hermL k r (fvec k r z' i)) (fvec k r z i) g (posL k r i a) (posL k r i b)`. Use `Eq.trans h ?_` and prove the remaining obligations. Rewrite using `[single_mulVec', map_smul, smul_eq_mul, mul_comm]`. Both sides reduce to the same expression.
-/
theorem eh_zb (a b : Fin (mdim k r i)) (g : Mx k r) :
    EH k r (posL k r i a) (posL k r i b) (zbF k r z z' i) g = -(xbv k r z' i a * yv k r z i g b) := by
  have h := eh_inv (hermL k r (fvec k r z' i)) (fvec k r z i) g (posL k r i a) (posL k r i b)
  refine Eq.trans h ?_
  rw [single_mulVec', map_smul, smul_eq_mul, mul_comm]
  rfl

/- English proof (translation)
Establish `h1 : g⁻¹ * g = 1`. Rewrite using `[uh_inv_eq hg.1]`. Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg.1`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : g * g⁻¹ = 1` using `mul_eq_one_comm.1 h1`.

Establish `hs : ∀ u w : Fin (2 * r + k + 1) → ℂ, star (herm (Hpk k r) u w) = herm (Hpk k r) w u`. Introduce `u w`. Unfold `herm`. Rewrite using `[← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hpk_h, ← Matrix.dotProduct_mulVec]`. Unfold `zetaL zbF`.

Rewrite using `[hs, ← herm_UH hg.1 (g⁻¹ *ᵥ fvec k r z i), Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]`.
-/
theorem zb_eq {g : Mx k r} (hg : g ∈ Glev k r i) : star (zetaL k r z z' i g) = zbF k r z z' i g := by
  have h1 : g⁻¹ * g = 1 := by
    rw [uh_inv_eq hg.1]
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg.1
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hpk_sq']
  have h2 : g * g⁻¹ = 1 := mul_eq_one_comm.1 h1
  have hs : ∀ u w : Fin (2 * r + k + 1) → ℂ, star (herm (Hpk k r) u w) = herm (Hpk k r) w u := by
    intro u w
    unfold herm
    rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hpk_h, ← Matrix.dotProduct_mulVec]
  unfold zetaL zbF
  rw [hs, ← herm_UH hg.1 (g⁻¹ *ᵥ fvec k r z i), Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b c`. Use `end_ext fun v g hg => ?_` and prove the remaining obligations. Rewrite using `[comm_EM hD a b _ v hg, eh_eta]`. Use `split_ifs`.

Conclude with `(ev_M hD (sm_eta z a) v hg).symm`. Rewrite using `[zero_smul]`. Both sides reduce to the same expression. Introduce `a b`. Use `end_ext fun v g hg => ?_` and prove the remaining obligations.

Rewrite using `[comm_EM hD a b _ v hg, eh_zeta, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, ev_M hD _ v hg, smul_smul]`.
-/
theorem cov_rel (hD : IsOpen D) : CovRel (Eh (E := E) hD) (fun c => Mh hD (fun g => ybv k r z i g c) (sm_eta z c))
    (xv k r z' i) (Mh hD (zetaL k r z z' i) (sm_zeta z z')) := by
  constructor
  · intro a b c
    refine end_ext fun v g hg => ?_
    rw [comm_EM hD a b _ v hg, eh_eta]
    split_ifs
    · exact (ev_M hD (sm_eta z a) v hg).symm
    · rw [zero_smul]; rfl
  · intro a b
    refine end_ext fun v g hg => ?_
    rw [comm_EM hD a b _ v hg, eh_zeta, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, ev_M hD _ v hg, smul_smul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b c`. Use `end_ext fun v g hg => ?_` and prove the remaining obligations. Rewrite using `[comm_EM hD a b _ v hg, eh_y]`. Use `split_ifs`.

Rewrite using `[LinearMap.neg_apply, Submodule.coe_neg, Pi.neg_apply, ev_M hD _ v hg, neg_smul]`. Rewrite using `[zero_smul]`. Both sides reduce to the same expression. Introduce `a b`. Use `end_ext fun v g hg => ?_` and prove the remaining obligations.

Rewrite using `[comm_EM hD a b _ v hg, eh_zb, LinearMap.neg_apply, Submodule.coe_neg, Pi.neg_apply, LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, ev_M hD _ v hg, smul_smul, neg_smul]`.
-/
theorem vec_rel (hD : IsOpen D) : VecRel (Eh (E := E) hD) (fun c => Mh hD (fun g => yv k r z i g c) (sm_y z c))
    (xbv k r z' i) (Mh hD (zbF k r z z' i) (sm_zb z z')) := by
  constructor
  · intro a b c
    refine end_ext fun v g hg => ?_
    rw [comm_EM hD a b _ v hg, eh_y]
    split_ifs
    · rw [LinearMap.neg_apply, Submodule.coe_neg, Pi.neg_apply, ev_M hD _ v hg, neg_smul]
    · rw [zero_smul]; rfl
  · intro a b
    refine end_ext fun v g hg => ?_
    rw [comm_EM hD a b _ v hg, eh_zb, LinearMap.neg_apply, Submodule.coe_neg, Pi.neg_apply, LinearMap.smul_apply,
      Submodule.coe_smul, Pi.smul_apply, ev_M hD _ v hg, smul_smul, neg_smul]

abbrev Mop (k r : ℕ) (i : Fin (r + 1)) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) (f : Mx k r → E) : Mx k r → E :=
  qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) w f

/- English proof (translation)
Rewrite using `[rep_qminor hD a b w _ g hg]`. Conclude with `(good_qminor hD a b w).loc _ _ (fun x hx => cut_of_mem f hx) g hg`.
-/
theorem ev_Q (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) {f : Mx k r → E}
    (hf : SmoothLev k r i D f) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (qminor (Eh (E := E) hD) a b w ⟨cut k r i D f, cut_mem hD hf⟩ : Mx k r → E) g = Mop k r i a b w f g := by
  rw [rep_qminor hD a b w _ g hg]
  exact (good_qminor hD a b w).loc _ _ (fun x hx => cut_of_mem f hx) g hg

/- English proof (translation)
Rewrite using `[rep_qminor hD a b w _ g hg]`. Use `(good_qminor hD a b w).loc _ _ (fun x hx => ?_) g hg` and prove the remaining obligations. Rewrite using `[ev_M hD hc _ hx]`. Use `show c x • cut k r i D f x = c x • f x`. Rewrite using `[cut_of_mem f hx]`.
-/
theorem ev_QM (hD : IsOpen D) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (w : ℂ) {c : Mx k r → ℂ}
    (hc : SmoothLev k r i D c) {f : Mx k r → E} (hf : SmoothLev k r i D f) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    (qminor (Eh (E := E) hD) a b w (Mh hD c hc ⟨cut k r i D f, cut_mem hD hf⟩) : Mx k r → E) g =
      Mop k r i a b w (fun y => c y • f y) g := by
  rw [rep_qminor hD a b w _ g hg]
  refine (good_qminor hD a b w).loc _ _ (fun x hx => ?_) g hg
  rw [ev_M hD hc _ hx]
  show c x • cut k r i D f x = c x • f x
  rw [cut_of_mem f hx]

/- English proof (translation)
Establish `h` using `congrArg (fun X : Module.End ℂ (VS k r i D E) => (X ⟨cut k r i D f, cut_mem hD hf⟩ : Mx k r → E) g) (Z1 (cov_rel (E := E) z z' hD) t a b w)`. Simplify using `only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply] at h`. Rewrite `h` using `[ev_QM hD a b w _ hf hg, ev_M hD _ _ hg, ev_Q hD a b w hf hg]`. Rewrite using `[h]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[ev_M hD _ _ hg, ev_Q hD _ _ _ hf hg, smul_smul]`.
-/
theorem finiteCocycles (hD : IsOpen D) {t : ℕ} (a b : Fin (t + 1) → Fin (mdim k r i)) (w : ℂ) {f : Mx k r → E}
    (hf : SmoothLev k r i D f) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    Mop k r i a b w (fun y => zetaL k r z z' i y • f y) g = zetaL k r z z' i g • Mop k r i a b w f g +
      ∑ p : Fin (t + 1), ∑ q : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * xv k r z' i (b q) * ybv k r z i g (a p)) •
        Mop k r i (a ∘ p.succAbove) (b ∘ q.succAbove) (w - 1) f g := by
  have h := congrArg (fun X : Module.End ℂ (VS k r i D E) => (X ⟨cut k r i D f, cut_mem hD hf⟩ : Mx k r → E) g)
    (Z1 (cov_rel (E := E) z z' hD) t a b w)
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, Submodule.coe_add,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.add_apply, Pi.smul_apply] at h
  rw [ev_QM hD a b w _ hf hg, ev_M hD _ _ hg, ev_Q hD a b w hf hg] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [ev_M hD _ _ hg, ev_Q hD _ _ _ hf hg, smul_smul]

/- English proof (translation)
Establish `h` using `congrArg (fun X : Module.End ℂ (VS k r i D E) => (X ⟨cut k r i D f, cut_mem hD hf⟩ : Mx k r → E) g) (Z2 (Eh_gl hD) (vec_rel (E := E) z z' hD) t a b w)`. Simplify using `only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply] at h`. Rewrite `h` using `[ev_QM hD a b w _ hf hg, ev_M hD _ _ hg, ev_Q hD a b w hf hg]`. Rewrite using `[h]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[ev_M hD _ _ hg, ev_Q hD _ _ _ hf hg, smul_smul]`.
-/
theorem minor_operator_zeta_commutation (hD : IsOpen D) {t : ℕ} (a b : Fin (t + 1) → Fin (mdim k r i)) (w : ℂ) {f : Mx k r → E}
    (hf : SmoothLev k r i D f) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    Mop k r i a b w (fun y => zbF k r z z' i y • f y) g = zbF k r z z' i g • Mop k r i a b w f g -
      ∑ p : Fin (t + 1), ∑ q : Fin (t + 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * xbv k r z' i (a p) * yv k r z i g (b q)) •
        Mop k r i (a ∘ p.succAbove) (b ∘ q.succAbove) w f g := by
  have h := congrArg (fun X : Module.End ℂ (VS k r i D E) => (X ⟨cut k r i D f, cut_mem hD hf⟩ : Mx k r → E) g)
    (Z2 (Eh_gl hD) (vec_rel (E := E) z z' hD) t a b w)
  simp only [LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply, Submodule.coe_sub,
    Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.sub_apply, Pi.smul_apply] at h
  rw [ev_QM hD a b w _ hf hg, ev_M hD _ _ hg, ev_Q hD a b w hf hg] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [ev_M hD _ _ hg, ev_Q hD _ _ _ hf hg, smul_smul]

end Concrete

section Comb

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/- English proof (translation)
Use `set T : Fin (M + 2) → Fin (M + 2) → X := fun i W => (((sg2 i W : ℤ) : ℂ) * α i * β W) • H (skip2 (min W i) (max W i)) with hT`. Establish `s1 : ∀ i : Fin (M + 2), ∑ p : Fin (M + 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β (i.succAbove p)) • H (i.succAbove ∘ p.succAbove) = ∑ W : Fin (M + 2), if W ≠ i then T i W else 0`. Introduce `i`. Rewrite using `[Qx6.sum_ne_succAbove i (fun W => T i W)]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Simplify using `only [hT, Qx6.sign_pair_succAbove_right, Qx6.skip_two_succAbove_comp_alt]`. Use `push_cast`. Both sides reduce to the same expression. Establish `s2 : ∀ i W : Fin (M + 2), (if W ≠ i then T i W else 0) = (if i < W then T i W else 0) + (if W < i then T i W else 0)`. Introduce `i W`.

Break down `lt_trichotomy i W with h | h | h` into its components or cases. Simplify using `[h, h.ne', not_lt.2 h.le]`. Simplify using `[h]`. Simplify using `[h, h.ne, not_lt.2 h.le]`. Simplify using `only [s1, s2, Finset.sum_add_distrib]`.

Rewrite using `[Finset.sum_comm (f := fun i W => if W < i then T i W else 0), ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : i < i'`.

Establish `h' : (i : ℕ) < (i' : ℕ)` using `h`. Simplify using `only [h, if_true, hT, sg2, min_eq_right h.le, max_eq_left h.le, min_eq_left h.le, max_eq_right h.le, if_neg (not_lt.2 h'.le), if_pos h', ← add_smul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[h]`.
-/
theorem oneSide_succ (M : ℕ) (α β : Fin (M + 2) → ℂ) (H : (Fin M → Fin (M + 2)) → X) :
    ∑ i : Fin (M + 2), ∑ p : Fin (M + 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β (i.succAbove p)) •
        H (i.succAbove ∘ p.succAbove) =
      ∑ i : Fin (M + 2), ∑ i' : Fin (M + 2),
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (α i' * β i - α i * β i')) • H (skip2 i i') else 0 := by
  set T : Fin (M + 2) → Fin (M + 2) → X := fun i W =>
    (((sg2 i W : ℤ) : ℂ) * α i * β W) • H (skip2 (min W i) (max W i)) with hT
  have s1 : ∀ i : Fin (M + 2), ∑ p : Fin (M + 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β (i.succAbove p)) •
      H (i.succAbove ∘ p.succAbove) = ∑ W : Fin (M + 2), if W ≠ i then T i W else 0 := by
    intro i
    rw [Qx6.sum_ne_succAbove i (fun W => T i W)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [hT, Qx6.sign_pair_succAbove_right, Qx6.skip_two_succAbove_comp_alt]
    push_cast
    rfl
  have s2 : ∀ i W : Fin (M + 2), (if W ≠ i then T i W else 0) =
      (if i < W then T i W else 0) + (if W < i then T i W else 0) := by
    intro i W
    rcases lt_trichotomy i W with h | h | h
    · simp [h, h.ne', not_lt.2 h.le]
    · simp [h]
    · simp [h, h.ne, not_lt.2 h.le]
  simp only [s1, s2, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i W => if W < i then T i W else 0), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i' _ => ?_
  by_cases h : i < i'
  · have h' : (i : ℕ) < (i' : ℕ) := h
    simp only [h, if_true, hT, sg2, min_eq_right h.le, max_eq_left h.le, min_eq_left h.le, max_eq_right h.le,
      if_neg (not_lt.2 h'.le), if_pos h', ← add_smul]
    congr 1
    push_cast
    ring
  · simp [h]

/- English proof (translation)
The claim follows from `| 0, _, _, _ => by simp | 1, _, _, _ => by have : ∀ i i' : Fin 1, ¬ i < i' := fun i i' => by rw [Subsingleton.elim i i']; exact lt_irrefl _ simp [this] | M + 2, α, β, H => by have h := oneSide_succ M α β H have e1 : ∀ i : Fin (M + 2), (skip1 i : Fin (M + 1) → Fin (M + 2)) = i.suc …`.
-/
theorem oneSide : ∀ (n : ℕ) (α β : Fin n → ℂ) (H : (Fin (n - 2) → Fin n) → X),
    ∑ i : Fin n, ∑ p : Fin (n - 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β (skip1 i p)) •
        H (skip1 i ∘ skip1 p) =
      ∑ i : Fin n, ∑ i' : Fin n,
        if i < i' then ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ)) * (α i' * β i - α i * β i')) • H (skip2 i i') else 0
  | 0, _, _, _ => by simp
  | 1, _, _, _ => by
    have : ∀ i i' : Fin 1, ¬ i < i' := fun i i' => by rw [Subsingleton.elim i i']; exact lt_irrefl _
    simp [this]
  | M + 2, α, β, H => by
    have h := oneSide_succ M α β H
    have e1 : ∀ i : Fin (M + 2), (skip1 i : Fin (M + 1) → Fin (M + 2)) = i.succAbove := Qx6.skip_one_eq_succAbove
    have e2 : ∀ p : Fin (M + 1), (skip1 p : Fin M → Fin (M + 1)) = p.succAbove := Qx6.skip_one_eq_succAbove
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p _ => ?_
    show ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * α i * β ((skip1 i : Fin (M + 1) → Fin (M + 2)) p)) •
      H ((skip1 i : Fin (M + 1) → Fin (M + 2)) ∘ (skip1 p : Fin M → Fin (M + 1))) = _
    rw [e1, e2]

/- English proof (translation)
Establish `h1 : ∀ l : Fin (n - 2) → Fin n, _` using `fun l => oneSide n B κ (fun l' => G l l')`. Establish `h2` using `oneSide n A ρ (fun l => ∑ j : Fin n, ∑ q : Fin (n - 1), ((-1 : ℂ) ^ ((j : ℕ) + (q : ℕ)) * B j * κ (skip1 j q)) • G l (skip1 j ∘ skip1 q))`. Establish `L : ∑ i : Fin n, ∑ j : Fin n, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * A i * B j) • ∑ p : Fin (n - 1), ∑ q : Fin (n - 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (skip1 i p) * κ (skip1 j q)) • G (skip1 i ∘ skip1 p) (skip1 j ∘ skip1 q) = ∑ i : Fin n, ∑ p : Fin (n - 1), ((-1 : ℂ) ^ ((i : ℕ) + …`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.smul_sum, smul_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[L, h2]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i < i'`. Simplify using `only [hi, if_true, true_and, h1, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Rewrite using `[smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[smul_zero]`. Simplify using `[hi]`.
-/
theorem pairSum (n : ℕ) (A ρ B κ : Fin n → ℂ) (G : (Fin (n - 2) → Fin n) → (Fin (n - 2) → Fin n) → X) :
    ∑ i : Fin n, ∑ j : Fin n, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * A i * B j) •
        ∑ p : Fin (n - 1), ∑ q : Fin (n - 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (skip1 i p) * κ (skip1 j q)) •
          G (skip1 i ∘ skip1 p) (skip1 j ∘ skip1 q) =
      ∑ i : Fin n, ∑ i' : Fin n, ∑ j : Fin n, ∑ j' : Fin n,
        if i < i' ∧ j < j' then
          ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ)) * (A i * ρ i' - A i' * ρ i) * (B j * κ j' - B j' * κ j)) •
            G (skip2 i i') (skip2 j j')
        else 0 := by
  have h1 : ∀ l : Fin (n - 2) → Fin n, _ := fun l => oneSide n B κ (fun l' => G l l')
  have h2 := oneSide n A ρ (fun l => ∑ j : Fin n, ∑ q : Fin (n - 1),
    ((-1 : ℂ) ^ ((j : ℕ) + (q : ℕ)) * B j * κ (skip1 j q)) • G l (skip1 j ∘ skip1 q))
  have L : ∑ i : Fin n, ∑ j : Fin n, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * A i * B j) •
        ∑ p : Fin (n - 1), ∑ q : Fin (n - 1), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (skip1 i p) * κ (skip1 j q)) •
          G (skip1 i ∘ skip1 p) (skip1 j ∘ skip1 q) =
      ∑ i : Fin n, ∑ p : Fin (n - 1), ((-1 : ℂ) ^ ((i : ℕ) + (p : ℕ)) * A i * ρ (skip1 i p)) •
        ∑ j : Fin n, ∑ q : Fin (n - 1), ((-1 : ℂ) ^ ((j : ℕ) + (q : ℕ)) * B j * κ (skip1 j q)) •
          G (skip1 i ∘ skip1 p) (skip1 j ∘ skip1 q) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun q _ => ?_
    congr 1
    ring
  rw [L, h2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  by_cases hi : i < i'
  · simp only [hi, if_true, true_and, h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    split_ifs
    · rw [smul_smul]
      congr 1
      ring
    · rw [smul_zero]
  · simp [hi]

end Comb

section Final

open Qx2

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}

/- English proof (translation)
Simplify using `[Mop, qminorOp]`.
-/
theorem Mop_zero (a b : Fin 0 → Fin (mdim k r i)) (w : ℂ) (f : Mx k r → E) : Mop k r i a b w f = f := by
  simp [Mop, qminorOp]

def ComRule (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (c : Mx k r → ℂ) (g : Mx k r) (ρ κ : Fin (mdim k r i) → ℂ) (s d : ℂ) : Prop :=
  ∀ (t : ℕ) (a b : Fin t → Fin (mdim k r i)) (w : ℂ) (f : Mx k r → E), SmoothLev k r i D f →
    Mop k r i a b w (fun y => c y • f y) g = c g • Mop k r i a b w f g +
      s • ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) •
        Mop k r i (a ∘ skip1 p) (b ∘ skip1 q) (w - d) f g

/- English proof (translation)
Introduce `t a b w f hf`. Consider the cases of `t with`. Consider the case `zero => simp [Mop_zero]`. Consider the case `succ t`. Rewrite using `[finiteCocycles z z' hD a b w hf hg, one_smul]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Establish `e1 : (skip1 p : Fin t → Fin (t + 1)) = p.succAbove` using `Qx6.skip_one_eq_succAbove p`. Establish `e2 : (skip1 q : Fin t → Fin (t + 1)) = q.succAbove` using `Qx6.skip_one_eq_succAbove q`. Use `show _ = _ • Mop k r i (a ∘ (skip1 p : Fin t → Fin (t + 1))) (b ∘ (skip1 q : Fin t → Fin (t + 1))) (w - 1) f g`.

Rewrite using `[e1, e2]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comRule_zeta (z z' : Fin (2 * r + k + 1) → ℂ) (hD : IsOpen D) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    ComRule k r i D E (zetaL k r z z' i) g (fun a => ybv k r z i g a) (xv k r z' i) 1 1 := by
  intro t a b w f hf
  cases t with
  | zero => simp [Mop_zero]
  | succ t =>
    rw [finiteCocycles z z' hD a b w hf hg, one_smul]
    congr 1
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    have e1 : (skip1 p : Fin t → Fin (t + 1)) = p.succAbove := Qx6.skip_one_eq_succAbove p
    have e2 : (skip1 q : Fin t → Fin (t + 1)) = q.succAbove := Qx6.skip_one_eq_succAbove q
    show _ = _ • Mop k r i (a ∘ (skip1 p : Fin t → Fin (t + 1))) (b ∘ (skip1 q : Fin t → Fin (t + 1))) (w - 1) f g
    rw [e1, e2]
    congr 1
    ring

/- English proof (translation)
Introduce `t a b w f hf`. Consider the cases of `t with`. Consider the case `zero => simp [Mop_zero]`. Consider the case `succ t`. Rewrite using `[minor_operator_zeta_commutation z z' hD a b w hf hg, neg_one_smul, sub_eq_add_neg, sub_zero]`.

Use `congr 2`.
-/
theorem comRule_zb (z z' : Fin (2 * r + k + 1) → ℂ) (hD : IsOpen D) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) :
    ComRule k r i D E (zbF k r z z' i) g (xbv k r z' i) (fun b => yv k r z i g b) (-1) 0 := by
  intro t a b w f hf
  cases t with
  | zero => simp [Mop_zero]
  | succ t =>
    rw [minor_operator_zeta_commutation z z' hD a b w hf hg, neg_one_smul, sub_eq_add_neg, sub_zero]
    congr 2

def ch (k r : ℕ) (i : Fin (r + 1)) (A B : Fin (mdim k r i) → ℂ) (w : ℂ) (f : Mx k r → E) (g : Mx k r) : E :=
  ∑ p : Fin (mdim k r i), ∑ q : Fin (mdim k r i), ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * A p * B q) •
    Mop k r i (skip1 p) (skip1 q) w f g

def ch2 (k r : ℕ) (i : Fin (r + 1)) (A A' B B' : Fin (mdim k r i) → ℂ) (w : ℂ) (f : Mx k r → E) (g : Mx k r) : E :=
  ∑ p : Fin (mdim k r i), ∑ p' : Fin (mdim k r i), ∑ q : Fin (mdim k r i), ∑ q' : Fin (mdim k r i),
    if p < p' ∧ q < q' then
      ((-1 : ℂ) ^ ((p : ℕ) + (p' : ℕ) + (q : ℕ) + (q' : ℕ)) * (A p * A' p' - A p' * A' p) * (B q * B' q' - B q' * B' q)) •
        Mop k r i (skip2 p p') (skip2 q q') w f g
    else 0

/- English proof (translation)
Unfold `ch2`. Simplify using `only [← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[← neg_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem capelli_two_swap_left (A A' B B' : Fin (mdim k r i) → ℂ) (w : ℂ) (f : Mx k r → E) (g : Mx k r) :
    ch2 k r i A' A B B' w f g = -ch2 k r i A A' B B' w f g := by
  unfold ch2
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun q' _ => ?_
  split_ifs
  · rw [← neg_smul]
    congr 1
    ring
  · simp

/- English proof (translation)
Unfold `ch2`. Simplify using `only [← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[← neg_smul]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem capelli_two_swap_right (A A' B B' : Fin (mdim k r i) → ℂ) (w : ℂ) (f : Mx k r → E) (g : Mx k r) :
    ch2 k r i A A' B' B w f g = -ch2 k r i A A' B B' w f g := by
  unfold ch2
  simp only [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun q' _ => ?_
  split_ifs
  · rw [← neg_smul]
    congr 1
    ring
  · simp

/- English proof (translation)
Unfold `ch2`. Use `Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun q' _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[show A p * A p' - A p' * A p = 0 by ring]`. Simplify using the standard rewrite rules.

Both sides reduce to the same expression.
-/
theorem capelli_two_same_left (A B B' : Fin (mdim k r i) → ℂ) (w : ℂ) (f : Mx k r → E) (g : Mx k r) :
    ch2 k r i A A B B' w f g = 0 := by
  unfold ch2
  refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q _ =>
    Finset.sum_eq_zero fun q' _ => ?_
  split_ifs
  · rw [show A p * A p' - A p' * A p = 0 by ring]
    simp
  · rfl

variable {c : Mx k r → ℂ} {g : Mx k r} {ρ κ : Fin (mdim k r i) → ℂ} {s d : ℂ}

/- English proof (translation)
Establish `hp` using `pairSum (mdim k r i) A ρ B κ (fun l l' => Mop k r i l l' (w - d) f g)`. Unfold `ch ch2`. Rewrite using `[← hp]`. Simplify using `only [h _ _ _ _ f hf, smul_add, Finset.sum_add_distrib, Finset.smul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q' _ => ?_` and prove the remaining obligations. Simplify using `only [smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ch_rule (h : ComRule k r i D E c g ρ κ s d) (A B : Fin (mdim k r i) → ℂ) (w : ℂ) {f : Mx k r → E}
    (hf : SmoothLev k r i D f) :
    ch k r i A B w (fun y => c y • f y) g = c g • ch k r i A B w f g + s • ch2 k r i A ρ B κ (w - d) f g := by
  have hp := pairSum (mdim k r i) A ρ B κ (fun l l' => Mop k r i l l' (w - d) f g)
  unfold ch ch2
  rw [← hp]
  simp only [h _ _ _ _ f hf, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [smul_comm]
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ =>
      Finset.sum_congr rfl fun q' _ => ?_
    simp only [smul_smul]
    congr 1
    ring

/- English proof (translation)
Establish `e1` using `h t a b w (fun y => c y • f y) (smooth_mul hc hf)`. Establish `e2` using `h t a b w f hf`. Establish `hp` using `pairSum t (ρ ∘ a) (ρ ∘ a) (κ ∘ b) (κ ∘ b) (fun l l' => Mop k r i (a ∘ l) (b ∘ l') (w - d - d) f g)`. Establish `hz : ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * (ρ ∘ a) p * (κ ∘ b) q) • ∑ p' : Fin (t - 1), ∑ q' : Fin (t - 1), ((-1 : ℂ) ^ ((p' : ℕ) + (q' : ℕ)) * (ρ ∘ a) (skip1 p p') * (κ ∘ b) (skip1 q q')) • Mop k r i (a ∘ (skip1 p ∘ skip1 p')) (b ∘ (skip1 q ∘ skip1 q')) (w …`. Rewrite using `[hp]`.

Use `Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun q' _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[show (ρ ∘ a) p * (ρ ∘ a) p' - (ρ ∘ a) p' * (ρ ∘ a) p = 0 by ring]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Establish `e3 : ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) • Mop k r i (a ∘ skip1 p) (b ∘ skip1 q) (w - d) (fun y => c y • f y) g = c g • ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) • Mop k r i (a ∘ skip1 p) (b ∘ skip1 q …`. Simplify using `only [h _ _ _ _ f hf, smul_add, Finset.sum_add_distrib]`. Establish `: ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) • s • ∑ p' : Fin (t - 1), ∑ q' : Fin (t - 1), ((-1 : ℂ) ^ ((p' : ℕ) + (q' : ℕ)) * ρ ((a ∘ skip1 p) p') * κ ((b ∘ skip1 q) q')) • Mop k r i ((a ∘ skip1 p) ∘ skip1 p') ((b ∘ skip1 q) ∘ skip1 q') (w - d …`. Use `congrArg (fun X => s • X) hz` as an intermediate fact. Simplify using `only [Finset.smul_sum, smul_zero] at this`.

Rewrite using `[← this]`. Simplify using `only [Finset.smul_sum]`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun q' _ => ?_` and prove the remaining obligations. Simplify using `only [smul_smul, Function.comp_apply]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, add_zero, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[smul_comm]`. Rewrite `e1` using `[e3]`. Rewrite using `[e1]`. Establish `e4 : s • ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) • Mop k r i (a ∘ skip1 p) (b ∘ skip1 q) (w - d) f g = Mop k r i a b w (fun y => c y • f y) g - c g • Mop k r i a b w f g`. Rewrite using `[e2]`.

Normalize the expressions using the abelian group laws. Rewrite using `[smul_comm s, e4]`. Use `module`.
-/
theorem dc_rule (h : ComRule k r i D E c g ρ κ s d) (hc : SmoothLev k r i D c) {t : ℕ}
    (a b : Fin t → Fin (mdim k r i)) (w : ℂ) {f : Mx k r → E} (hf : SmoothLev k r i D f) :
    Mop k r i a b w (fun y => c y • c y • f y) g =
      (2 * c g) • Mop k r i a b w (fun y => c y • f y) g - (c g ^ 2) • Mop k r i a b w f g := by
  have e1 := h t a b w (fun y => c y • f y) (smooth_mul hc hf)
  have e2 := h t a b w f hf
  have hp := pairSum t (ρ ∘ a) (ρ ∘ a) (κ ∘ b) (κ ∘ b) (fun l l' => Mop k r i (a ∘ l) (b ∘ l') (w - d - d) f g)
  have hz : ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * (ρ ∘ a) p * (κ ∘ b) q) •
        ∑ p' : Fin (t - 1), ∑ q' : Fin (t - 1),
          ((-1 : ℂ) ^ ((p' : ℕ) + (q' : ℕ)) * (ρ ∘ a) (skip1 p p') * (κ ∘ b) (skip1 q q')) •
            Mop k r i (a ∘ (skip1 p ∘ skip1 p')) (b ∘ (skip1 q ∘ skip1 q')) (w - d - d) f g = 0 := by
    rw [hp]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q _ =>
      Finset.sum_eq_zero fun q' _ => ?_
    split_ifs
    · rw [show (ρ ∘ a) p * (ρ ∘ a) p' - (ρ ∘ a) p' * (ρ ∘ a) p = 0 by ring]
      simp
    · rfl
  have e3 : ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) •
        Mop k r i (a ∘ skip1 p) (b ∘ skip1 q) (w - d) (fun y => c y • f y) g =
      c g • ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) •
        Mop k r i (a ∘ skip1 p) (b ∘ skip1 q) (w - d) f g := by
    simp only [h _ _ _ _ f hf, smul_add, Finset.sum_add_distrib]
    have : ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) • s •
        ∑ p' : Fin (t - 1), ∑ q' : Fin (t - 1),
          ((-1 : ℂ) ^ ((p' : ℕ) + (q' : ℕ)) * ρ ((a ∘ skip1 p) p') * κ ((b ∘ skip1 q) q')) •
            Mop k r i ((a ∘ skip1 p) ∘ skip1 p') ((b ∘ skip1 q) ∘ skip1 q') (w - d - d) f g = 0 := by
      have := congrArg (fun X => s • X) hz
      simp only [Finset.smul_sum, smul_zero] at this
      rw [← this]
      simp only [Finset.smul_sum]
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun p' _ =>
        Finset.sum_congr rfl fun q' _ => ?_
      simp only [smul_smul, Function.comp_apply]
      congr 1
      ring
    rw [this, add_zero, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_comm]
  rw [e3] at e1
  rw [e1]
  have e4 : s • ∑ p : Fin t, ∑ q : Fin t, ((-1 : ℂ) ^ ((p : ℕ) + (q : ℕ)) * ρ (a p) * κ (b q)) •
        Mop k r i (a ∘ skip1 p) (b ∘ skip1 q) (w - d) f g =
      Mop k r i a b w (fun y => c y • f y) g - c g • Mop k r i a b w f g := by
    rw [e2]; abel
  rw [smul_comm s, e4]
  module

/- English proof (translation)
Unfold `ch`. Simplify using `only [dc_rule h hc _ _ _ hf, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`.

Use `Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm]`.
-/
theorem ch_dc (h : ComRule k r i D E c g ρ κ s d) (hc : SmoothLev k r i D c) (A B : Fin (mdim k r i) → ℂ) (w : ℂ)
    {f : Mx k r → E} (hf : SmoothLev k r i D f) :
    ch k r i A B w (fun y => c y • c y • f y) g =
      (2 * c g) • ch k r i A B w (fun y => c y • f y) g - (c g ^ 2) • ch k r i A B w f g := by
  unfold ch
  simp only [dc_rule h hc _ _ _ hf, smul_sub, Finset.sum_sub_distrib, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [smul_comm]
  · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [smul_comm]

/- English proof (translation)
Establish `e1` using `ch_rule h A B w (smooth_mul hc hf)`. Establish `e2` using `ch_rule h A B w hf`. Rewrite `e1` using `[ch_dc h hc A B w hf]`. Establish `e3 : s • ch2 k r i A ρ B κ (w - d) (fun y => c y • f y) g = s • (c g • ch2 k r i A ρ B κ (w - d) f g)`. Establish `e4 : s • ch2 k r i A ρ B κ (w - d) f g = ch k r i A B w (fun y => c y • f y) g - c g • ch k r i A B w f g`.

Rewrite using `[e2]`. Normalize the expressions using the abelian group laws. Establish `e5 : s • ch2 k r i A ρ B κ (w - d) (fun y => c y • f y) g = (2 * c g) • ch k r i A B w (fun y => c y • f y) g - (c g ^ 2) • ch k r i A B w f g - c g • ch k r i A B w (fun y => c y • f y) g`. Rewrite using `[e1]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e5, smul_comm s, e4]`. Use `module`. Conclude with `smul_right_injective E hs e3`.
-/
theorem capelli_two_commutation_rule (h : ComRule k r i D E c g ρ κ s d) (hs : s ≠ 0) (hc : SmoothLev k r i D c)
    (A B : Fin (mdim k r i) → ℂ) (w : ℂ) {f : Mx k r → E} (hf : SmoothLev k r i D f) :
    ch2 k r i A ρ B κ (w - d) (fun y => c y • f y) g = c g • ch2 k r i A ρ B κ (w - d) f g := by
  have e1 := ch_rule h A B w (smooth_mul hc hf)
  have e2 := ch_rule h A B w hf
  rw [ch_dc h hc A B w hf] at e1
  have e3 : s • ch2 k r i A ρ B κ (w - d) (fun y => c y • f y) g = s • (c g • ch2 k r i A ρ B κ (w - d) f g) := by
    have e4 : s • ch2 k r i A ρ B κ (w - d) f g = ch k r i A B w (fun y => c y • f y) g - c g • ch k r i A B w f g := by
      rw [e2]; abel
    have e5 : s • ch2 k r i A ρ B κ (w - d) (fun y => c y • f y) g =
        (2 * c g) • ch k r i A B w (fun y => c y • f y) g - (c g ^ 2) • ch k r i A B w f g -
          c g • ch k r i A B w (fun y => c y • f y) g := by
      rw [e1]; abel
    rw [e5, smul_comm s, e4]
    module
  exact smul_right_injective E hs e3

/- English proof (translation)
Use `set η : Fin (mdim k r i) → ℂ := fun a => ybv k r z i g a with hη`. Use `set y : Fin (mdim k r i) → ℂ := fun b => yv k r z i g b with hy`. Use `set x : Fin (mdim k r i) → ℂ := xv k r z' i with hx`. Use `set ξ : Fin (mdim k r i) → ℂ := xbv k r z' i with hξ`. Use `set u : ℂ := uC k r i Y with hu`.

Establish `t01 : ∀ h : Mx k r → E, tL k r z z' i Y 0 1 h g = -ch k r i η x (u - 1) h g` using `fun _ => rfl`. Establish `t10 : ∀ h : Mx k r → E, tL k r z z' i Y 1 0 h g = -ch k r i ξ y u h g` using `fun _ => rfl`. Establish `t11 : ∀ h : Mx k r → E, tL k r z z' i Y 1 1 h g = -ch2 k r i η ξ y x (u - 1) h g` using `fun _ => rfl`. Establish `R1 : ComRule k r i D E (zetaL k r z z' i) g η x 1 1` using `comRule_zeta z z' hD hg`. Establish `R2 : ComRule k r i D E (zbF k r z z' i) g ξ y (-1) 0` using `comRule_zb z z' hD hg`.

Establish `hloc : ∀ p q : Fin 2, tL k r z z' i Y p q (fun x => star (zetaL k r z z' i x) • f x) g = tL k r z z' i Y p q (fun x => zbF k r z z' i x • f x) g` using `fun p q => (ll_tL hD z z' Y p q).loc _ _ (fun x hx => by rw [zb_eq z z' hx.1]) g hg`. Rewrite using `[hloc, hloc, hloc, zb_eq z z' hg.1]`. Simplify using `only [t01, t10, t11]`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ch_rule R1 ξ y u hf, capelli_two_swap_left η ξ y x] module`.

Establish `h` using `capelli_two_commutation_rule R1 one_ne_zero (sm_zeta z z') ξ y u hf`. Rewrite `h` using `[capelli_two_swap_left η ξ y x, capelli_two_swap_left η ξ y x]`. Conclude with `h`. Rewrite using `[ch_rule R1 η x (u - 1) hf, capelli_two_same_left] module`. Rewrite using `[ch_rule R2 η x (u - 1) hf, sub_zero, capelli_two_swap_right η ξ y x] module`.

Rewrite using `[ch_rule R2 ξ y u hf, capelli_two_same_left] module`. Establish `h` using `capelli_two_commutation_rule R2 (neg_ne_zero.2 one_ne_zero) (sm_zb z z') η x (u - 1) hf`. Rewrite `h` using `[sub_zero, capelli_two_swap_right η ξ y x, capelli_two_swap_right η ξ y x]`. Conclude with `h`.
-/
theorem zeta_comm_level (z z' : Fin (2 * r + k + 1) → ℂ) (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f)
    {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) (Y : ℂ) :
    tL k r z z' i Y 1 0 (fun x => zetaL k r z z' i x • f x) g =
        zetaL k r z z' i g • tL k r z z' i Y 1 0 f g - tL k r z z' i Y 1 1 f g ∧
    tL k r z z' i Y 1 1 (fun x => zetaL k r z z' i x • f x) g = zetaL k r z z' i g • tL k r z z' i Y 1 1 f g ∧
    tL k r z z' i Y 0 1 (fun x => zetaL k r z z' i x • f x) g = zetaL k r z z' i g • tL k r z z' i Y 0 1 f g ∧
    tL k r z z' i Y 0 1 (fun x => star (zetaL k r z z' i x) • f x) g =
        star (zetaL k r z z' i g) • tL k r z z' i Y 0 1 f g + tL k r z z' i Y 1 1 f g ∧
    tL k r z z' i Y 1 0 (fun x => star (zetaL k r z z' i x) • f x) g =
        star (zetaL k r z z' i g) • tL k r z z' i Y 1 0 f g ∧
    tL k r z z' i Y 1 1 (fun x => star (zetaL k r z z' i x) • f x) g =
        star (zetaL k r z z' i g) • tL k r z z' i Y 1 1 f g := by
  set η : Fin (mdim k r i) → ℂ := fun a => ybv k r z i g a with hη
  set y : Fin (mdim k r i) → ℂ := fun b => yv k r z i g b with hy
  set x : Fin (mdim k r i) → ℂ := xv k r z' i with hx
  set ξ : Fin (mdim k r i) → ℂ := xbv k r z' i with hξ
  set u : ℂ := uC k r i Y with hu
  have t01 : ∀ h : Mx k r → E, tL k r z z' i Y 0 1 h g = -ch k r i η x (u - 1) h g := fun _ => rfl
  have t10 : ∀ h : Mx k r → E, tL k r z z' i Y 1 0 h g = -ch k r i ξ y u h g := fun _ => rfl
  have t11 : ∀ h : Mx k r → E, tL k r z z' i Y 1 1 h g = -ch2 k r i η ξ y x (u - 1) h g := fun _ => rfl
  have R1 : ComRule k r i D E (zetaL k r z z' i) g η x 1 1 := comRule_zeta z z' hD hg
  have R2 : ComRule k r i D E (zbF k r z z' i) g ξ y (-1) 0 := comRule_zb z z' hD hg
  have hloc : ∀ p q : Fin 2, tL k r z z' i Y p q (fun x => star (zetaL k r z z' i x) • f x) g =
      tL k r z z' i Y p q (fun x => zbF k r z z' i x • f x) g := fun p q =>
    (ll_tL hD z z' Y p q).loc _ _ (fun x hx => by rw [zb_eq z z' hx.1]) g hg
  rw [hloc, hloc, hloc, zb_eq z z' hg.1]
  simp only [t01, t10, t11]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ch_rule R1 ξ y u hf, capelli_two_swap_left η ξ y x]
    module
  · have h := capelli_two_commutation_rule R1 one_ne_zero (sm_zeta z z') ξ y u hf
    rw [capelli_two_swap_left η ξ y x, capelli_two_swap_left η ξ y x] at h
    exact h
  · rw [ch_rule R1 η x (u - 1) hf, capelli_two_same_left]
    module
  · rw [ch_rule R2 η x (u - 1) hf, sub_zero, capelli_two_swap_right η ξ y x]
    module
  · rw [ch_rule R2 ξ y u hf, capelli_two_same_left]
    module
  · have h := capelli_two_commutation_rule R2 (neg_ne_zero.2 one_ne_zero) (sm_zb z z') η x (u - 1) hf
    rw [sub_zero, capelli_two_swap_right η ξ y x, capelli_two_swap_right η ξ y x] at h
    exact h

end Final

end Formalism.FourierDecayAlt.P.Qx5

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P z z' π π' hP Φ hΦ`. Use `⟨fun l j => ⟨Qx5.crd_mem l j hΦ, fun Ψ hΨ s => Qx5.crd_lin l j hΦ hΨ s⟩, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[Qx5.fn_ind j hΦ]`. Conclude with `Qx5.fn_mem (Qx5.place_alt_alt hP) j hΦ`.
-/
theorem radial_operators : Formalism.FourierDecayAlt.Q.RadOps := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hP Φ hΦ
  refine ⟨fun l j => ⟨Qx5.crd_mem l j hΦ, fun Ψ hΨ s => Qx5.crd_lin l j hΦ hΨ s⟩, fun j => ?_⟩
  rw [Qx5.fn_ind j hΦ]
  exact Qx5.fn_mem (Qx5.place_alt_alt hP) j hΦ

/- English proof (translation)
Introduce `E _ _ k r z z' D f _ _ hD hf g hg Y`. Conclude with `Qx5.zeta_comm_level z z' hD hf hg Y`.
-/
theorem zeta_commutes : Formalism.FourierDecayAlt.Q.ZetaComm := by
  intro E _ _ k r z z' D f _ _ hD hf g hg Y
  exact Qx5.zeta_comm_level z z' hD hf hg Y

/- English proof (translation)
Introduce `hH Wp Wq _ _ _ _ _ _ P z z' π π' hP X μ hμ Φ Ψ c hc hK Y a b v`. Take `⟨K, hK, hKD, h0⟩` from `hK`. Conclude with `Qx5.adjoint_main hH hP.2.1 hP.2.2.1 X hμ Φ Ψ hc hK hKD h0 Y a b v`.
-/
theorem actual_adjointness_from_hermitian : Formalism.FourierDecayAlt.Q.ActualAdjointFromHerm := by
  intro hH Wp Wq _ _ _ _ _ _ P z z' π π' hP X μ hμ Φ Ψ c hc hK Y a b v
  obtain ⟨K, hK, hKD, h0⟩ := hK
  exact Qx5.adjoint_main hH hP.2.1 hP.2.2.1 X hμ Φ Ψ hc hK hKD h0 Y a b v

/- English proof (translation)
Introduce `hTP hLL hJS _ Wp Wq _ _ _ _ _ _ P z z' π π' hP`. Conclude with `⟨Qx5.actualOps hTP hLL hJS hP.2.1 hP.2.2.1 (Qx5.place_alt_alt hP)⟩`.
-/
theorem actual_operators_from_parts : Formalism.FourierDecayAlt.Q.ActualOpsFromSteps := by
  intro hTP hLL hJS _ Wp Wq _ _ _ _ _ _ P z z' π π' hP
  exact ⟨Qx5.actualOps hTP hLL hJS hP.2.1 hP.2.2.1 (Qx5.place_alt_alt hP)⟩

end Formalism.FourierDecayAlt.P
