import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.AutomorphicForms.MacdonaldWhittakerHecke

noncomputable section

open NumberField IsDedekindDomain Matrix GroundTheory.Automorphic UpperTheory.V.Af
open GlobalTheory.CuspRep (GA Af Ad pFin pLoc)

namespace GlobalTheory.HenQ.Basic

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

abbrev locAt (w : HeightOneSpectrum (𝓞 K)) (g : GA K n) : GL (Fin n) (w.adicCompletion K) :=
  GeneralLinearGroup.map (pLoc K w) (gFin g)

/- English proof (translation)
The claim follows from `(Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))).comp (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin K))))`.
-/
theorem continuous_locAt (w : HeightOneSpectrum (𝓞 K)) : Continuous (locAt (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map (RestrictedProduct.continuous_eval w))).comp
    (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin K))))

/- English proof (translation)
Assemble the required witnesses or components as `⟨GroundTheory.Global.isClosed_adicCompletionIntegers w, GroundTheory.Global.isOpen_adicCompletionIntegers w⟩`.
-/
theorem isClopen_Ov (w : HeightOneSpectrum (𝓞 K)) : IsClopen (Formalism.UG.Ov K w : Set (w.adicCompletion K)) :=
  ⟨GroundTheory.Global.isClosed_adicCompletionIntegers w, GroundTheory.Global.isOpen_adicCompletionIntegers w⟩

/- English proof (translation)
Rewrite using `[GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`. Use `⟨fun i j => (z.val i j).2, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`.

Conclude with `((z⁻¹).val i j).2`. Introduce and unpack `⟨h1, h2⟩`. Set `M : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w)` to `Matrix.of fun i j => ⟨_, h1 i j⟩`. Set `N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w)` to `Matrix.of fun i j => ⟨_, h2 i j⟩`. Establish `hM : M.map (Formalism.UG.Ov K w).subtype = y.val` using `by ext i j; rfl`.

Establish `hN : N.map (Formalism.UG.Ov K w).subtype = (y⁻¹).val` using `by ext i j; rfl`. Establish `inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) => A.map (Formalism.UG.Ov K w).subtype)` using `Matrix.map_injective Subtype.val_injective`. Use `⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]`.

Simplify using `only`. Rewrite using `[Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `hM`.
-/
theorem mem_KGL_iff (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K)) :
    y ∈ GlobalTheory.LFun.KGL w n ↔ (∀ i j, y.val i j ∈ Formalism.UG.Ov K w) ∧ ∀ i j, (y⁻¹).val i j ∈ Formalism.UG.Ov K w := by
  rw [GlobalTheory.LFun.KGL, Formalism.UG.GLint, MonoidHom.mem_range]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨fun i j => (z.val i j).2, fun i j => ?_⟩
    rw [← map_inv]
    exact ((z⁻¹).val i j).2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let N : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h2 i j⟩
    have hM : M.map (Formalism.UG.Ov K w).subtype = y.val := by ext i j; rfl
    have hN : N.map (Formalism.UG.Ov K w).subtype = (y⁻¹).val := by ext i j; rfl
    have inj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) => A.map (Formalism.UG.Ov K w).subtype) :=
      Matrix.map_injective Subtype.val_injective
    refine ⟨⟨M, N, inj ?_, inj ?_⟩, Units.ext ?_⟩
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    · simp only
      rw [Matrix.map_mul, hM, hN, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    · exact hM

/- English proof (translation)
Establish `: {g : GA K n | ∀ i j, (locAt w g).val i j ∈ Formalism.UG.Ov K w} = ⋂ i, ⋂ j, (fun g : GA K n => (locAt w g).val i j) ⁻¹' (Formalism.UG.Ov K w : Set (w.adicCompletion K))`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Rewrite using `[this]`. Conclude with `isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => (isClopen_Ov w).preimage ((continuous_apply_apply i j).comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion K))).comp (continuous_locAt w)))`.
-/
theorem isClopen_KGL_entries (w : HeightOneSpectrum (𝓞 K)) :
    IsClopen {g : GA K n | ∀ i j, (locAt w g).val i j ∈ Formalism.UG.Ov K w} := by
  have : {g : GA K n | ∀ i j, (locAt w g).val i j ∈ Formalism.UG.Ov K w} =
      ⋂ i, ⋂ j, (fun g : GA K n => (locAt w g).val i j) ⁻¹' (Formalism.UG.Ov K w : Set (w.adicCompletion K)) := by
    ext g; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [this]
  exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
    (isClopen_Ov w).preimage ((continuous_apply_apply i j).comp ((Units.continuous_val (M := Matrix (Fin n) (Fin n) (w.adicCompletion K))).comp (continuous_locAt w)))

/- English proof (translation)
Establish `: {g : GA K n | ∀ i j, ((locAt w g)⁻¹).val i j ∈ Formalism.UG.Ov K w} = ⋂ i, ⋂ j, (fun g : GA K n => ((locAt w g)⁻¹).val i j) ⁻¹' (Formalism.UG.Ov K w : Set (w.adicCompletion K))`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Rewrite using `[this]`. Conclude with `isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => (isClopen_Ov w).preimage ((continuous_apply_apply i j).comp ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (w.adicCompletion K))).comp (continuous_locAt w)))`.
-/
theorem isClopen_KGL_inv_entries (w : HeightOneSpectrum (𝓞 K)) :
    IsClopen {g : GA K n | ∀ i j, ((locAt w g)⁻¹).val i j ∈ Formalism.UG.Ov K w} := by
  have : {g : GA K n | ∀ i j, ((locAt w g)⁻¹).val i j ∈ Formalism.UG.Ov K w} =
      ⋂ i, ⋂ j, (fun g : GA K n => ((locAt w g)⁻¹).val i j) ⁻¹' (Formalism.UG.Ov K w : Set (w.adicCompletion K)) := by
    ext g; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [this]
  exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j =>
    (isClopen_Ov w).preimage ((continuous_apply_apply i j).comp ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (w.adicCompletion K))).comp (continuous_locAt w)))

/- English proof (translation)
Establish `: {g : GA K n | locAt w g ∈ GlobalTheory.LFun.KGL w n} = {g : GA K n | ∀ i j, (locAt w g).val i j ∈ Formalism.UG.Ov K w} ∩ {g : GA K n | ∀ i j, ((locAt w g)⁻¹).val i j ∈ Formalism.UG.Ov K w}`. Use extensionality with `g`. Conclude with `mem_KGL_iff w _`. Rewrite using `[this]`. Conclude with `(isClopen_KGL_entries w).inter (isClopen_KGL_inv_entries w)`.
-/
theorem isClopen_KGL (w : HeightOneSpectrum (𝓞 K)) :
    IsClopen {g : GA K n | locAt w g ∈ GlobalTheory.LFun.KGL w n} := by
  have : {g : GA K n | locAt w g ∈ GlobalTheory.LFun.KGL w n} =
      {g : GA K n | ∀ i j, (locAt w g).val i j ∈ Formalism.UG.Ov K w} ∩
        {g : GA K n | ∀ i j, ((locAt w g)⁻¹).val i j ∈ Formalism.UG.Ov K w} := by
    ext g; exact mem_KGL_iff w _
  rw [this]
  exact (isClopen_KGL_entries w).inter (isClopen_KGL_inv_entries w)

/- English proof (translation)
Set `y` to `gFin g`. Establish `hf : ∀ x : Af K, {w : HeightOneSpectrum (𝓞 K) | ¬ x w ∈ w.adicCompletionIntegers K}.Finite` using `fun x => Filter.eventually_cofinite.1 x.2`. Use `((Set.finite_iUnion fun i => Set.finite_iUnion fun j => (hf (y.val i j)).union (hf ((y⁻¹).val i j)))).subset ?_` and prove the remaining obligations. Introduce `w hw`. Assume the negation of the conclusion as `hc`.

Simplify using `only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq, not_exists, not_or, not_not] at hc`. Apply `hw` to reduce the goal to its premises. Rewrite using `[mem_KGL_iff]`. Use `⟨fun i j => (hc i j).1, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`.

Conclude with `(hc i j).2`.
-/
theorem finite_not_KGL (g : GA K n) : {w : HeightOneSpectrum (𝓞 K) | locAt w g ∉ GlobalTheory.LFun.KGL w n}.Finite := by
  let y := gFin g
  have hf : ∀ x : Af K, {w : HeightOneSpectrum (𝓞 K) | ¬ x w ∈ w.adicCompletionIntegers K}.Finite :=
    fun x => Filter.eventually_cofinite.1 x.2
  refine ((Set.finite_iUnion fun i => Set.finite_iUnion fun j => (hf (y.val i j)).union (hf ((y⁻¹).val i j)))).subset ?_
  intro w hw
  by_contra hc
  simp only [Set.mem_iUnion, Set.mem_union, Set.mem_setOf_eq, not_exists, not_or, not_not] at hc
  apply hw
  rw [mem_KGL_iff]
  refine ⟨fun i j => (hc i j).1, fun i j => ?_⟩
  rw [← map_inv]
  exact (hc i j).2

/- English proof (translation)
Set `M' : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w)` to `Matrix.of fun i j => ⟨_, h i j⟩`. Establish `hM : M'.map (Formalism.UG.Ov K w).subtype = M` using `by ext i j; rfl`. Establish `e : (M'.map (Formalism.UG.Ov K w).subtype).det = (Formalism.UG.Ov K w).subtype M'.det` using `(RingHom.map_det (Formalism.UG.Ov K w).subtype M').symm`. Rewrite using `[← hM, e]`. Conclude with `(M'.det).2`.
-/
theorem det_mem_Ov (w : HeightOneSpectrum (𝓞 K)) (M : Matrix (Fin n) (Fin n) (w.adicCompletion K))
    (h : ∀ i j, M i j ∈ Formalism.UG.Ov K w) : M.det ∈ Formalism.UG.Ov K w := by
  let M' : Matrix (Fin n) (Fin n) (Formalism.UG.Ov K w) := Matrix.of fun i j => ⟨_, h i j⟩
  have hM : M'.map (Formalism.UG.Ov K w).subtype = M := by ext i j; rfl
  have e : (M'.map (Formalism.UG.Ov K w).subtype).det = (Formalism.UG.Ov K w).subtype M'.det :=
    (RingHom.map_det (Formalism.UG.Ov K w).subtype M').symm
  rw [← hM, e]
  exact (M'.det).2

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.mul_apply] exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)`.
-/
theorem mul_mem_Ov (w : HeightOneSpectrum (𝓞 K)) (M N : Matrix (Fin n) (Fin n) (w.adicCompletion K))
    (hM : ∀ i j, M i j ∈ Formalism.UG.Ov K w) (hN : ∀ i j, N i j ∈ Formalism.UG.Ov K w) :
    ∀ i j, (M * N) i j ∈ Formalism.UG.Ov K w := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hN k j)

/- English proof (translation)
Establish `hv : Valued.v x ≠ 0` using `(Valuation.ne_zero_iff _).2 h0`. Establish `hle : Valued.v x ≤ 1` using `hx`. Establish `he : Valued.v x = ((Multiplicative.ofAdd (Multiplicative.toAdd (WithZero.unzero hv)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Rewrite using `[ofAdd_toAdd, WithZero.coe_unzero]`. Establish `hm : Multiplicative.toAdd (WithZero.unzero hv) ≤ 0`.

Rewrite `hle` using `[he]`. Conclude with `hle` after adjusting the coercions. Use `⟨(-Multiplicative.toAdd (WithZero.unzero hv)).toNat, ?_⟩` and prove the remaining obligations. Rewrite using `[FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow, NNReal.coe_natCast, ← zpow_natCast, ← _root_.zpow_neg, Int.toNat_of_nonneg (by omega), neg_neg]`.
-/
theorem norm_eq_inv_pow (w : HeightOneSpectrum (𝓞 K)) {x : w.adicCompletion K} (h0 : x ≠ 0)
    (hx : x ∈ Formalism.UG.Ov K w) : ∃ k : ℕ, ‖x‖ = ((Ideal.absNorm w.asIdeal : ℝ) ^ k)⁻¹ := by
  have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  have hle : Valued.v x ≤ 1 := hx
  have he : Valued.v x = ((Multiplicative.ofAdd (Multiplicative.toAdd (WithZero.unzero hv)) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) := by
    rw [ofAdd_toAdd, WithZero.coe_unzero]
  have hm : Multiplicative.toAdd (WithZero.unzero hv) ≤ 0 := by
    rw [he] at hle
    exact_mod_cast hle
  refine ⟨(-Multiplicative.toAdd (WithZero.unzero hv)).toNat, ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _ hv, NNReal.coe_zpow, NNReal.coe_natCast,
    ← zpow_natCast, ← _root_.zpow_neg, Int.toNat_of_nonneg (by omega), neg_neg]

/- English proof (translation)
Take `⟨h1, h2⟩` from `(mem_KGL_iff w a).1 ha`. Establish `d1 : ‖a.val.det‖ ≤ 1` using `Valued.toNormedField.norm_le_one_iff.2 (det_mem_Ov w _ h1)`. Establish `d2 : ‖(a⁻¹).val.det‖ ≤ 1` using `Valued.toNormedField.norm_le_one_iff.2 (det_mem_Ov w _ h2)`. Establish `hp : ‖a.val.det‖ * ‖(a⁻¹).val.det‖ = 1`. Rewrite using `[← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]`.

Use polynomial arithmetic with `[norm_nonneg a.val.det, norm_nonneg (a⁻¹).val.det]`.
-/
theorem norm_eq_one_of_mem_KGL (w : HeightOneSpectrum (𝓞 K)) {a : GL (Fin n) (w.adicCompletion K)}
    (ha : a ∈ GlobalTheory.LFun.KGL w n) : ‖a.val.det‖ = 1 := by
  obtain ⟨h1, h2⟩ := (mem_KGL_iff w a).1 ha
  have d1 : ‖a.val.det‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 (det_mem_Ov w _ h1)
  have d2 : ‖(a⁻¹).val.det‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 (det_mem_Ov w _ h2)
  have hp : ‖a.val.det‖ * ‖(a⁻¹).val.det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
  nlinarith [norm_nonneg a.val.det, norm_nonneg (a⁻¹).val.det]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul]`. Conclude with `mul_mem_Ov w _ _ (mul_mem_Ov w _ _ ((mem_KGL_iff w a).1 ha).1 hy.1) ((mem_KGL_iff w b).1 hb).1`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, norm_eq_one_of_mem_KGL w ha, norm_eq_one_of_mem_KGL w hb, one_mul, mul_one]`. Conclude with `hy.2`.
-/
theorem shell_mul_of (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (y a b : GL (Fin n) (w.adicCompletion K))
    (ha : a ∈ GlobalTheory.LFun.KGL w n) (hb : b ∈ GlobalTheory.LFun.KGL w n) (hy : y ∈ Shell w n k) : a * y * b ∈ Shell w n k := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact mul_mem_Ov w _ _ (mul_mem_Ov w _ _ ((mem_KGL_iff w a).1 ha).1 hy.1) ((mem_KGL_iff w b).1 hb).1
  · rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul,
      norm_eq_one_of_mem_KGL w ha, norm_eq_one_of_mem_KGL w hb, one_mul, mul_one]
    exact hy.2

/- English proof (translation)
Take `⟨k, hk⟩` from `norm_eq_inv_pow w (Matrix.isUnits_det_units y).ne_zero (det_mem_Ov w _ hy)`. Use `⟨k, ⟨hy, hk⟩, fun k' hk' => ?_⟩` and prove the remaining obligations. Establish `e` using `hk'.2.symm.trans hk`. Rewrite `e` using `[_root_.inv_inj, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_inj]`. Conclude with `Nat.pow_right_injective (HeightOneSpectrum.one_lt_absNorm w) e`.
-/
theorem shell_exists_unique (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K))
    (hy : ∀ i j, y.val i j ∈ Formalism.UG.Ov K w) : ∃! k, y ∈ Shell w n k := by
  obtain ⟨k, hk⟩ := norm_eq_inv_pow w (Matrix.isUnits_det_units y).ne_zero (det_mem_Ov w _ hy)
  refine ⟨k, ⟨hy, hk⟩, fun k' hk' => ?_⟩
  have e := hk'.2.symm.trans hk
  rw [_root_.inv_inj, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_inj] at e
  exact Nat.pow_right_injective (HeightOneSpectrum.one_lt_absNorm w) e

/- English proof (translation)
Introduce `K _ _ n`. Use `⟨fun g h => ?_, fun g => (Reduction.detModule K n g).2, ?_, fun w => ⟨isClopen_KGL_entries w, isClopen_KGL w⟩, fun S => ?_, finite_not_KGL, shell_exists_unique, fun w k y a b ha hb => ⟨fun h => ?_, shell_mul_of w k y a b ha hb⟩⟩` and prove the remaining obligations. Simplify using `only [absDet, map_mul, Positive.val_mul]`. Conclude with `continuous_subtype_val.comp Reduction.continuous_detModule`. Establish `: {g : GA K n | UnitOff S (gFin g)} = ⋂ w, ⋂ (_ : w ∉ S), {g : GA K n | locAt w g ∈ GlobalTheory.LFun.KGL w n}`.

Use extensionality with `g`. Simplify using `only [UnitOff, Set.mem_setOf_eq, Set.mem_iInter]`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun w => isClosed_iInter fun _ => (isClopen_KGL w).isClosed`. Establish `e` using `shell_mul_of w k (a * y * b) a⁻¹ b⁻¹ (inv_mem ha) (inv_mem hb) h`.

Rewrite `e` using `[show a⁻¹ * (a * y * b) * b⁻¹ = y by group]`. Then use the resulting hypothesis.
-/
theorem main : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ),
    (∀ g h : GA K n, absDet (g * h) = absDet g * absDet h) ∧ (∀ g : GA K n, 0 < absDet g) ∧
    Continuous (absDet : GA K n → ℝ) ∧
    (∀ w : HeightOneSpectrum (𝓞 K), IsClopen {g : GA K n | IntAt w (gFin g)} ∧
      IsClopen {g : GA K n | GeneralLinearGroup.map (pLoc K w) (gFin g) ∈ GlobalTheory.LFun.KGL w n}) ∧
    (∀ S : Set (HeightOneSpectrum (𝓞 K)), IsClosed {g : GA K n | UnitOff S (gFin g)}) ∧
    (∀ g : GA K n, {w | GeneralLinearGroup.map (pLoc K w) (gFin g) ∉ GlobalTheory.LFun.KGL w n}.Finite) ∧
    (∀ (w : HeightOneSpectrum (𝓞 K)) (y : GL (Fin n) (w.adicCompletion K)),
      (∀ i j, y.val i j ∈ Formalism.UG.Ov K w) → ∃! k, y ∈ Shell w n k) ∧
    ∀ (w : HeightOneSpectrum (𝓞 K)) (k : ℕ) (y a b : GL (Fin n) (w.adicCompletion K)),
      a ∈ GlobalTheory.LFun.KGL w n → b ∈ GlobalTheory.LFun.KGL w n → (a * y * b ∈ Shell w n k ↔ y ∈ Shell w n k) := by
  intro K _ _ n
  refine ⟨fun g h => ?_, fun g => (Reduction.detModule K n g).2, ?_, fun w => ⟨isClopen_KGL_entries w, isClopen_KGL w⟩,
    fun S => ?_, finite_not_KGL, shell_exists_unique, fun w k y a b ha hb => ⟨fun h => ?_, shell_mul_of w k y a b ha hb⟩⟩
  · simp only [absDet, map_mul, Positive.val_mul]
  · exact continuous_subtype_val.comp Reduction.continuous_detModule
  · have : {g : GA K n | UnitOff S (gFin g)} = ⋂ w, ⋂ (_ : w ∉ S), {g : GA K n | locAt w g ∈ GlobalTheory.LFun.KGL w n} := by
      ext g; simp only [UnitOff, Set.mem_setOf_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun w => isClosed_iInter fun _ => (isClopen_KGL w).isClosed
  · have e := shell_mul_of w k (a * y * b) a⁻¹ b⁻¹ (inv_mem ha) (inv_mem hb) h
    rwa [show a⁻¹ * (a * y * b) * b⁻¹ = y by group] at e

end GlobalTheory.HenQ.Basic
