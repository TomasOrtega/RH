import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TranslatedLatticeAtInfinityFullCovolumeDualStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

noncomputable section

namespace GlobalTheory.LatMeasurable

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

def oneInf : MatInf E j := fun _ a b => (1 : Matrix (Fin j) (Fin j) ℂ) a b

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem of_oneInf (w : InfinitePlace E) : Matrix.of (oneInf E j w) = 1 := rfl

/- English proof (translation)
Unfold `detNorm`. Simplify using `[of_oneInf]`.
-/
theorem detNorm_oneInf : 0 < detNorm E j (oneInf E j) := by
  unfold detNorm
  simp [of_oneInf]

variable {E j}

/- English proof (translation)
Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Establish `hz : detNorm E j g = 0`. Unfold `detNorm`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ w) (by simp [h0])`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isUnit_det_of_pos {g : MatInf E j} (hg : 0 < detNorm E j g) (w : InfinitePlace E) :
    IsUnit (Matrix.of (g w)).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hz : detNorm E j g = 0 := by
    unfold detNorm
    exact Finset.prod_eq_zero (Finset.mem_univ w) (by simp [h0])
  linarith

def act (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) : VecInf E j →ₗ[ℤ] VecInf E j where
  toFun x w := A w *ᵥ x w
  map_add' x y := by funext w; simp [Matrix.mulVec_add]
  map_smul' c x := by funext w; exact Matrix.mulVec_smul (A w) c (x w)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem act_apply (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) (x : VecInf E j) (w : InfinitePlace E) :
    act A x w = A w *ᵥ x w := rfl

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [act_apply, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]`.
-/
theorem act_act {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ} (h : ∀ w, A w * B w = 1) (x : VecInf E j) :
    act A (act B x) = x := by
  funext w
  simp only [act_apply, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/- English proof (translation)
Unfold `latAt`. Rewrite using `[Submodule.map_span, ← Set.image_comp]`. Use `congr 2`. Use function extensionality and compare the values at `y w`. Simplify using `[act_apply, of_oneInf]`.
-/
theorem latAt_eq (Λ : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) :
    latAt E j Λ g = (latAt E j Λ (oneInf E j)).map (act fun w => (Matrix.of (g w))⁻¹) := by
  unfold latAt
  rw [Submodule.map_span, ← Set.image_comp]
  congr 2
  funext y w
  simp [act_apply, of_oneInf]

/- English proof (translation)
Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [act_apply]`. Rewrite using `[dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]`.
-/
private lemma dualAt_act_transpose (A : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ) (x y : VecInf E j) :
    ∑ w, (act A x w ⬝ᵥ y w).re = ∑ w, (x w ⬝ᵥ act (fun w => (A w)ᵀ) y w).re := by
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [act_apply]
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

/- English proof (translation)
Establish `hBA : ∀ w, B w * A w = 1` using `fun w => mul_eq_one_comm.mp (h w)`. Establish `hT : ∀ y, act (fun w => (B w)ᵀ) (act (fun w => (A w)ᵀ) y) = y` using `fun y => act_act (fun w => by rw [← Matrix.transpose_mul, h w, Matrix.transpose_one]) y`. Establish `hT' : ∀ y, act (fun w => (A w)ᵀ) (act (fun w => (B w)ᵀ) y) = y` using `fun y => act_act (fun w => by rw [← Matrix.transpose_mul, hBA w, Matrix.transpose_one]) y`. Unfold `dualAt`. Rewrite using `[Submodule.map_span]`.

Use `congr 1`. Use extensionality with `y`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Use `⟨act (fun w => (A w)ᵀ) y, fun x hx => ?_, hT y⟩` and prove the remaining obligations. Take `⟨z, hz⟩` from `hy _ (Submodule.mem_map_of_mem hx)`. Conclude with `⟨z, by rw [← dualAt_act_transpose A x y]; exact hz⟩`. Introduce and unpack `⟨y', hy', rfl⟩ x hx`. Take `⟨x', hx', rfl⟩` from `Submodule.mem_map.mp hx`.

Take `⟨z, hz⟩` from `hy' x' hx'`. Conclude with `⟨z, by rw [dualAt_act_transpose A x' _, hT' y']; exact hz⟩`.
-/
theorem dualAt_map (L : Submodule ℤ (VecInf E j)) {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ}
    (h : ∀ w, A w * B w = 1) :
    dualAt E j (L.map (act A)) = (dualAt E j L).map (act fun w => (B w)ᵀ) := by
  have hBA : ∀ w, B w * A w = 1 := fun w => mul_eq_one_comm.mp (h w)
  have hT : ∀ y, act (fun w => (B w)ᵀ) (act (fun w => (A w)ᵀ) y) = y := fun y =>
    act_act (fun w => by rw [← Matrix.transpose_mul, h w, Matrix.transpose_one]) y
  have hT' : ∀ y, act (fun w => (A w)ᵀ) (act (fun w => (B w)ᵀ) y) = y := fun y =>
    act_act (fun w => by rw [← Matrix.transpose_mul, hBA w, Matrix.transpose_one]) y
  unfold dualAt
  rw [Submodule.map_span]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hy
    refine ⟨act (fun w => (A w)ᵀ) y, fun x hx => ?_, hT y⟩
    obtain ⟨z, hz⟩ := hy _ (Submodule.mem_map_of_mem hx)
    exact ⟨z, by rw [← dualAt_act_transpose A x y]; exact hz⟩
  · rintro ⟨y', hy', rfl⟩ x hx
    obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
    obtain ⟨z, hz⟩ := hy' x' hx'
    exact ⟨z, by rw [dualAt_act_transpose A x' _, hT' y']; exact hz⟩

/- English proof (translation)
Establish `hBA : ∀ w, B w * A w = 1` using `fun w => mul_eq_one_comm.mp (h w)`. Set `e : {x : VecInf E j // x ∈ L ∧ x ≠ 0} ≃ {x : VecInf E j // x ∈ L.map (act A) ∧ x ≠ 0}` to `{ toFun := fun x => ⟨act A x.1, Submodule.mem_map_of_mem x.2.1, fun h0 => x.2.2 (by`. Rewrite using `[← act_act hBA x.1, h0, map_zero])⟩`. Use `invFun := fun y => ⟨act B y.1, by`. Take `⟨x, hx, hxy⟩` from `Submodule.mem_map.mp y.2.1`.

Rewrite using `[← hxy, act_act hBA]`. Conclude with `hx, fun h0 => y.2.2 (by rw [← act_act h y.1, h0, map_zero])⟩`. Use `left_inv := fun x => Subtype.ext (act_act hBA x.1)`. Use `right_inv := fun y => Subtype.ext (act_act h y.1) }`. Conclude with `(e.tsum_eq (fun x => Φ x.1)).symm`.
-/
theorem tsum_map (L : Submodule ℤ (VecInf E j)) {A B : InfinitePlace E → Matrix (Fin j) (Fin j) ℂ}
    (h : ∀ w, A w * B w = 1) (Φ : VecInf E j → ENNReal) :
    ∑' x : {x : VecInf E j // x ∈ L.map (act A) ∧ x ≠ 0}, Φ x.1 =
      ∑' x : {x : VecInf E j // x ∈ L ∧ x ≠ 0}, Φ (act A x.1) := by
  have hBA : ∀ w, B w * A w = 1 := fun w => mul_eq_one_comm.mp (h w)
  let e : {x : VecInf E j // x ∈ L ∧ x ≠ 0} ≃ {x : VecInf E j // x ∈ L.map (act A) ∧ x ≠ 0} :=
    { toFun := fun x => ⟨act A x.1, Submodule.mem_map_of_mem x.2.1, fun h0 => x.2.2 (by
          rw [← act_act hBA x.1, h0, map_zero])⟩
      invFun := fun y => ⟨act B y.1, by
          obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp y.2.1
          rw [← hxy, act_act hBA]
          exact hx, fun h0 => y.2.2 (by rw [← act_act h y.1, h0, map_zero])⟩
      left_inv := fun x => Subtype.ext (act_act hBA x.1)
      right_inv := fun y => Subtype.ext (act_act h y.1) }
  exact (e.tsum_eq (fun x => Φ x.1)).symm

def pairL (y : VecInf E j) : VecInf E j →ₗ[ℝ] ℝ where
  toFun x := ∑ w, (x w ⬝ᵥ y w).re
  map_add' x x' := by simp [add_dotProduct, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_dotProduct, Finset.mul_sum]

/- English proof (translation)
Introduce `y y' hyy`. Establish `key : ∀ (w : InfinitePlace E) (a : Fin j) (c : ℂ), (c * y w a).re = (c * y' w a).re`. Introduce `w a c`. Establish `hv : ∀ z : VecInf E j, pairL z (Pi.single w (Pi.single a c)) = (c * z w a).re`. Introduce `z`.

Use `show ∑ v, ((Pi.single w (Pi.single a c) : VecInf E j) v ⬝ᵥ z v).re = _`. Rewrite using `[Finset.sum_eq_single w (fun v _ hne => by simp [hne]) (by simp)]`. Simplify using `[single_dotProduct]`. Rewrite using `[← hv y, ← hv y', hyy]`. Use function extensionality and compare the values at `w a`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using key w a 1`. Simplify using `using key w a Complex.I`.
-/
theorem pairL_injective : Function.Injective (pairL : VecInf E j → _) := by
  classical
  intro y y' hyy
  have key : ∀ (w : InfinitePlace E) (a : Fin j) (c : ℂ), (c * y w a).re = (c * y' w a).re := by
    intro w a c
    have hv : ∀ z : VecInf E j, pairL z (Pi.single w (Pi.single a c)) = (c * z w a).re := by
      intro z
      show ∑ v, ((Pi.single w (Pi.single a c) : VecInf E j) v ⬝ᵥ z v).re = _
      rw [Finset.sum_eq_single w (fun v _ hne => by simp [hne]) (by simp)]
      simp [single_dotProduct]
    rw [← hv y, ← hv y', hyy]
  funext w a
  apply Complex.ext
  · simpa using key w a 1
  · simpa using key w a Complex.I

/- English proof (translation)
Establish `hsym : ∀ x y : VecInf E j, pairL y x = pairL x y` using `fun x y => by show ∑ w, (x w ⬝ᵥ y w).re = ∑ w, (y w ⬝ᵥ x w).re`. Conclude with `Finset.sum_congr rfl fun w _ => by rw [dotProduct_comm]`. Establish `hint : ∀ y ∈ dualAt E j L, ∀ x ∈ L, ∃ z : ℤ, pairL x y = z`. Introduce `y hy x hx`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy'`. Take `⟨z, hz⟩` from `hy' x hx`. Conclude with `⟨z, by rw [← hsym x y]; exact hz⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add y y' _ _ h1 h2`.

Take `⟨a, ha⟩` from `h1`. Take `⟨c, hc⟩` from `h2`. Conclude with `⟨a + c, by rw [map_add, ha, hc]; push_cast; ring⟩`. Consider the case `smul n y _ h1`. Take `⟨a, ha⟩` from `h1`.

Conclude with `⟨n * a, by rw [map_zsmul, ha, zsmul_eq_mul]; push_cast; ring⟩`. Take `⟨b, hbL, hbspan, hbli⟩` from `exists_linearIndependent ℝ (L : Set (VecInf E j))`. Use `haveI : Finite b := hbli.finite`. Use `choose φ hφ using fun (y : dualAt E j L) (i : b) => hint y.1 y.2 i.1 (hbL i.2)`. Use `Function.Injective.countable (f := φ) ?_` and prove the remaining obligations.

Introduce `y y' hyy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `pairL_injective` to reduce the goal to its premises. Use `LinearMap.ext_on (s := (b : Set (VecInf E j))) (hbspan.trans hL) ?_` and prove the remaining obligations. Introduce `x hx`.

Establish `e1` using `hφ y ⟨x, hx⟩`. Establish `e2` using `hφ y' ⟨x, hx⟩`. Simplify using `only at e1 e2`. Rewrite using `[hsym x y.1, hsym x y'.1, e1, e2, hyy]`.
-/
theorem countable_dualAt (L : Submodule ℤ (VecInf E j)) (hL : Submodule.span ℝ (L : Set (VecInf E j)) = ⊤) :
    Countable (dualAt E j L) := by
  have hsym : ∀ x y : VecInf E j, pairL y x = pairL x y := fun x y => by
    show ∑ w, (x w ⬝ᵥ y w).re = ∑ w, (y w ⬝ᵥ x w).re
    exact Finset.sum_congr rfl fun w _ => by rw [dotProduct_comm]
  have hint : ∀ y ∈ dualAt E j L, ∀ x ∈ L, ∃ z : ℤ, pairL x y = z := by
    intro y hy x hx
    induction hy using Submodule.span_induction with
    | mem y hy' =>
      obtain ⟨z, hz⟩ := hy' x hx
      exact ⟨z, by rw [← hsym x y]; exact hz⟩
    | zero => exact ⟨0, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨a, ha⟩ := h1
      obtain ⟨c, hc⟩ := h2
      exact ⟨a + c, by rw [map_add, ha, hc]; push_cast; ring⟩
    | smul n y _ h1 =>
      obtain ⟨a, ha⟩ := h1
      exact ⟨n * a, by rw [map_zsmul, ha, zsmul_eq_mul]; push_cast; ring⟩
  obtain ⟨b, hbL, hbspan, hbli⟩ := exists_linearIndependent ℝ (L : Set (VecInf E j))
  haveI : Finite b := hbli.finite
  choose φ hφ using fun (y : dualAt E j L) (i : b) => hint y.1 y.2 i.1 (hbL i.2)
  refine Function.Injective.countable (f := φ) ?_
  intro y y' hyy
  apply Subtype.ext
  apply pairL_injective
  refine LinearMap.ext_on (s := (b : Set (VecInf E j))) (hbspan.trans hL) ?_
  intro x hx
  have e1 := hφ y ⟨x, hx⟩
  have e2 := hφ y' ⟨x, hx⟩
  dsimp only at e1 e2
  rw [hsym x y.1, hsym x y'.1, e1, e2, hyy]

/- English proof (translation)
Establish `hc : Continuous fun g : InfinitePlace E → Fin j → Fin j → ℂ => f (Matrix.of (g w))` using `hf.comp (continuous_apply w)`. Conclude with `hc.measurable`.
-/
theorem measurable_of_continuous {β : Type} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]
    (w : InfinitePlace E) (f : Matrix (Fin j) (Fin j) ℂ → β) (hf : Continuous f) :
    Measurable fun g : MatInf E j => f (Matrix.of (g w)) := by
  have hc : Continuous fun g : InfinitePlace E → Fin j → Fin j → ℂ => f (Matrix.of (g w)) :=
    hf.comp (continuous_apply w)
  exact hc.measurable

/- English proof (translation)
Unfold `detNorm`. Conclude with `Finset.measurable_prod _ fun w _ => measurable_of_continuous w (fun M => ‖M.det‖ ^ 2) (continuous_id.matrix_det.norm.pow 2)`.
-/
theorem measurable_detNorm : Measurable (detNorm E j) := by
  unfold detNorm
  exact Finset.measurable_prod _ fun w _ =>
    measurable_of_continuous w (fun M => ‖M.det‖ ^ 2) (continuous_id.matrix_det.norm.pow 2)

/- English proof (translation)
Use `measurable_pi_lambda _ fun w => ?_` and prove the remaining obligations. Simplify using `only [act_apply]`. Establish `hinv : ∀ M : Matrix (Fin j) (Fin j) ℂ, M⁻¹ = (M.det)⁻¹ • M.adjugate` using `fun M => by`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Simplify using `only [hinv]`.

Establish `hd : Measurable fun g : MatInf E j => (Matrix.of (g w)).det` using `measurable_of_continuous w (fun M => M.det) continuous_id.matrix_det`. Use `measurable_pi_lambda _ fun a => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]`. Use `Finset.measurable_sum _ fun b _ => ?_` and prove the remaining obligations. Conclude with `(hd.inv.mul (measurable_of_continuous w (fun M => M.adjugate a b) (continuous_id.matrix_adjugate.matrix_elem a b))).mul_const _`.
-/
theorem measurable_act_inv (x : VecInf E j) :
    Measurable fun g : MatInf E j => act (fun w => (Matrix.of (g w))⁻¹) x := by
  refine measurable_pi_lambda _ fun w => ?_
  simp only [act_apply]
  have hinv : ∀ M : Matrix (Fin j) (Fin j) ℂ, M⁻¹ = (M.det)⁻¹ • M.adjugate := fun M => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  simp only [hinv]
  have hd : Measurable fun g : MatInf E j => (Matrix.of (g w)).det :=
    measurable_of_continuous w (fun M => M.det) continuous_id.matrix_det
  refine measurable_pi_lambda _ fun a => ?_
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul]
  refine Finset.measurable_sum _ fun b _ => ?_
  exact (hd.inv.mul (measurable_of_continuous w (fun M => M.adjugate a b)
    (continuous_id.matrix_adjugate.matrix_elem a b))).mul_const _

/- English proof (translation)
Use `measurable_pi_lambda _ fun w => ?_` and prove the remaining obligations. Simplify using `only [act_apply]`. Conclude with `measurable_of_continuous w (fun M => Mᵀ *ᵥ x w) (continuous_id.matrix_transpose.matrix_mulVec continuous_const)`.
-/
theorem measurable_act_transpose (x : VecInf E j) :
    Measurable fun g : MatInf E j => act (fun w => (Matrix.of (g w))ᵀ) x := by
  refine measurable_pi_lambda _ fun w => ?_
  simp only [act_apply]
  exact measurable_of_continuous w (fun M => Mᵀ *ᵥ x w)
    (continuous_id.matrix_transpose.matrix_mulVec continuous_const)

/- English proof (translation)
Establish `hS : MeasurableSet {g : MatInf E j | 0 < detNorm E j g}` using `measurableSet_lt measurable_const measurable_detNorm`. Use `hf'.indicator hS using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `g`. Conclude with `congrFun (Set.indicator_congr fun g hg => h g hg) g`.
-/
theorem measurable_indicator_of_eqOn {f f' : MatInf E j → ENNReal} (hf' : Measurable f')
    (h : ∀ g, 0 < detNorm E j g → f g = f' g) :
    Measurable fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator f g := by
  have hS : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} :=
    measurableSet_lt measurable_const measurable_detNorm
  convert hf'.indicator hS using 1
  funext g
  exact congrFun (Set.indicator_congr fun g hg => h g hg) g

/- English proof (translation)
The claim follows from `Function.Injective.countable (f := fun x : {x : VecInf E j // x ∈ L ∧ x ≠ 0} => (⟨x.1, x.2.1⟩ : L)) fun _ _ hab => Subtype.ext (congrArg (fun y : L => (y : VecInf E j)) hab)`.
-/
private lemma countable_nonzero_lattice_vectors (L : Submodule ℤ (VecInf E j)) [Countable L] :
    Countable {x : VecInf E j // x ∈ L ∧ x ≠ 0} :=
  Function.Injective.countable (f := fun x : {x : VecInf E j // x ∈ L ∧ x ≠ 0} => (⟨x.1, x.2.1⟩ : L))
    fun _ _ hab => Subtype.ext (congrArg (fun y : L => (y : VecInf E j)) hab)

/- English proof (translation)
Introduce `E _ _ hE j wt Φ hw hΦ Λ hΛ`. Take `⟨κ, -, hK⟩` from `(GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE j).1 Λ hΛ`. Take `⟨⟨hd, hz⟩, -, -, -⟩` from `hK (oneInf E j) (detNorm_oneInf E j)`. Use `haveI : Countable (latAt E j Λ (oneInf E j)) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance`. Use `haveI : Countable (dualAt E j (latAt E j Λ (oneInf E j))) := countable_dualAt _ hz.span_top`.

Use `haveI := countable_nonzero_lattice_vectors (latAt E j Λ (oneInf E j))`. Use `haveI := countable_nonzero_lattice_vectors (dualAt E j (latAt E j Λ (oneInf E j)))`. Establish `hinv : ∀ g : MatInf E j, 0 < detNorm E j g → ∀ w, (Matrix.of (g w))⁻¹ * Matrix.of (g w) = 1` using `fun g hg w => Matrix.nonsing_inv_mul _ (isUnit_det_of_pos hg w)`. Establish `htr : ∀ g : MatInf E j, 0 < detNorm E j g → ∀ w, (Matrix.of (g w))ᵀ * ((Matrix.of (g w))⁻¹)ᵀ = 1`. Introduce `g hg w`.

Rewrite using `[← Matrix.transpose_mul, hinv g hg w, Matrix.transpose_one]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `measurable_indicator_of_eqOn (f' := fun g => wt (κ / detNorm E j g)) (hw.comp (measurable_const.div measurable_detNorm)) fun g hg => by simp only [(hK g hg).2.1]`. Apply the tactic sequence `refine measurable_indicator_of_eqOn (f' := fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ (oneInf E j) ∧ x ≠ 0}, Φ (act (fun w => (Matrix.of (g w))⁻¹) x.1)) (Measurable.ennreal_tsum fun x => hΦ.comp (measurable_act_inv x.1)) fun g hg => ?_ try dsimp only`. Rewrite using `[latAt_eq Λ g, tsum_map _ (hinv g hg) Φ]`.

Apply the tactic sequence `refine measurable_indicator_of_eqOn (f' := fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ (oneInf E j)) ∧ x ≠ 0}, Φ (act (fun w => (Matrix.of (g w))ᵀ) x.1)) (Measurable.ennreal_tsum fun x => hΦ.comp (measurable_act_transpose x.1)) fun g hg => ?_ try dsimp only`. Rewrite using `[latAt_eq Λ g, dualAt_map _ (hinv g hg), tsum_map _ (htr g hg) Φ]`.
-/
theorem measurable_latFun : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ j : ℕ, ∀ (w : ℝ → ENNReal) (Φ : VecInf E j → ENNReal), Measurable w → Measurable Φ → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => w (covAt E j (latAt E j Λ g))) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ g ∧ x ≠ 0}, Φ x.1) g) ∧ Measurable (fun g : MatInf E j => {g | 0 < detNorm E j g}.indicator (fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ g) ∧ x ≠ 0}, Φ x.1) g) := by
  intro E _ _ hE j wt Φ hw hΦ Λ hΛ
  obtain ⟨κ, -, hK⟩ := (GlobalTheory.T.translatedLatticeAtInfinity_full_covolume_dual E hE j).1 Λ hΛ
  obtain ⟨⟨hd, hz⟩, -, -, -⟩ := hK (oneInf E j) (detNorm_oneInf E j)
  haveI : Countable (latAt E j Λ (oneInf E j)) :=
    TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  haveI : Countable (dualAt E j (latAt E j Λ (oneInf E j))) := countable_dualAt _ hz.span_top
  haveI := countable_nonzero_lattice_vectors (latAt E j Λ (oneInf E j))
  haveI := countable_nonzero_lattice_vectors (dualAt E j (latAt E j Λ (oneInf E j)))
  have hinv : ∀ g : MatInf E j, 0 < detNorm E j g → ∀ w, (Matrix.of (g w))⁻¹ * Matrix.of (g w) = 1 :=
    fun g hg w => Matrix.nonsing_inv_mul _ (isUnit_det_of_pos hg w)
  have htr : ∀ g : MatInf E j, 0 < detNorm E j g →
      ∀ w, (Matrix.of (g w))ᵀ * ((Matrix.of (g w))⁻¹)ᵀ = 1 := by
    intro g hg w
    rw [← Matrix.transpose_mul, hinv g hg w, Matrix.transpose_one]
  refine ⟨?_, ?_, ?_⟩
  · exact measurable_indicator_of_eqOn (f' := fun g => wt (κ / detNorm E j g))
      (hw.comp (measurable_const.div measurable_detNorm)) fun g hg => by simp only [(hK g hg).2.1]
  · refine measurable_indicator_of_eqOn
      (f' := fun g => ∑' x : {x : VecInf E j // x ∈ latAt E j Λ (oneInf E j) ∧ x ≠ 0},
        Φ (act (fun w => (Matrix.of (g w))⁻¹) x.1))
      (Measurable.ennreal_tsum fun x => hΦ.comp (measurable_act_inv x.1)) fun g hg => ?_
    try dsimp only
    rw [latAt_eq Λ g, tsum_map _ (hinv g hg) Φ]
  · refine measurable_indicator_of_eqOn
      (f' := fun g => ∑' x : {x : VecInf E j // x ∈ dualAt E j (latAt E j Λ (oneInf E j)) ∧ x ≠ 0},
        Φ (act (fun w => (Matrix.of (g w))ᵀ) x.1))
      (Measurable.ennreal_tsum fun x => hΦ.comp (measurable_act_transpose x.1)) fun g hg => ?_
    try dsimp only
    rw [latAt_eq Λ g, dualAt_map _ (hinv g hg), tsum_map _ (htr g hg) Φ]

end GlobalTheory.LatMeasurable
