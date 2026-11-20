import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJFEDefs
import GroundTheory.AutomorphicForms.GL2.GJLeviZetaBlocks
import GroundTheory.AutomorphicForms.MeasuresGL

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal MeasureTheory Measure GJMatrix
open scoped NNReal ENNReal Pointwise

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[centralUnif, Matrix.diagonal_apply, Matrix.one_apply]`.
-/
theorem coe_centralUnif :
    ((centralUnif F m : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      (uniformizer F : F) • (1 : Matrix (Fin m) (Fin m) F) := by
  ext i j
  simp [centralUnif, Matrix.diagonal_apply, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `: 1`. Simplify using `[Units.val_mul, coe_centralUnif]`.
-/
theorem centralUnif_mul_comm (g : GL (Fin m) F) : centralUnif F m * g = g * centralUnif F m := by
  ext : 1
  simp [Units.val_mul, coe_centralUnif]

/- English proof (translation)
The claim follows from `((Commute.zpow_left (centralUnif_mul_comm g) j)).eq`.
-/
theorem centralUnif_zpow_mul_comm (j : ℤ) (g : GL (Fin m) F) :
    centralUnif F m ^ j * g = g * centralUnif F m ^ j :=
  ((Commute.zpow_left (centralUnif_mul_comm g) j)).eq

/- English proof (translation)
Simplify using `[centralUnif, ordDet_diagPow]`.
-/
theorem ordDet_centralUnif : ordDet (centralUnif F m) = m := by
  simp [centralUnif, ordDet_diagPow]

/- English proof (translation)
Proceed by induction on `j using Int.induction_on with`. Consider the case `zero => simp [ordDet_one]`. Consider the case `succ k ih => rw [_root_.zpow_add_one, ordDet_mul, ih]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `pred k ih => rw [_root_.zpow_sub_one, ordDet_mul, ih, ordDet_inv]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ordDet_zpow (g : GL (Fin m) F) (j : ℤ) : ordDet (g ^ j) = j * ordDet g := by
  induction j using Int.induction_on with
  | zero => simp [ordDet_one]
  | succ k ih => rw [_root_.zpow_add_one, ordDet_mul, ih]; ring
  | pred k ih => rw [_root_.zpow_sub_one, ordDet_mul, ih, ordDet_inv]; ring

/- English proof (translation)
Rewrite using `[ordDet_mul, ordDet_zpow, ordDet_centralUnif]`.
-/
theorem ordDet_centralUnif_zpow_mul (j : ℤ) (g : GL (Fin m) F) :
    ordDet (centralUnif F m ^ j * g) = j * m + ordDet g := by
  rw [ordDet_mul, ordDet_zpow, ordDet_centralUnif]

/- English proof (translation)
Rewrite using `[detPow_eq_qs_zpow, detPow_eq_qs_zpow, ordDet_centralUnif_zpow_mul, zpow_add₀ (qs_ne_zero s)]`.
-/
theorem detPow_centralUnif_zpow_mul (j : ℤ) (g : GL (Fin m) F) (s : ℂ) :
    detPow (centralUnif F m ^ j * g) s = qs F s ^ (j * (m : ℤ)) * detPow g s := by
  rw [detPow_eq_qs_zpow, detPow_eq_qs_zpow, ordDet_centralUnif_zpow_mul,
    zpow_add₀ (qs_ne_zero s)]

/- English proof (translation)
Rewrite using `[detPow_eq_qs_zpow, norm_zpow, norm_qs]`.
-/
theorem norm_detPow (g : GL (Fin m) F) (s : ℂ) :
    ‖detPow g s‖ = ((LocalField.residueCard F : ℝ) ^ (-s.re)) ^ ordDet g := by
  rw [detPow_eq_qs_zpow, norm_zpow, norm_qs]

variable (F m) in

def tile (j : ℤ) : Set (GL (Fin m) F) := {g | j * m ≤ ordDet g ∧ ordDet g < j * m + m}

/- English proof (translation)
The claim follows from `(IsLocallyConstant.iff_isOpen_fiber).2 fun k => (isClopen_shell F m k).isOpen`.
-/
theorem isLocallyConstant_ordDet_GL : IsLocallyConstant (ordDet : GL (Fin m) F → ℤ) :=
  (IsLocallyConstant.iff_isOpen_fiber).2 fun k => (isClopen_shell F m k).isOpen

/- English proof (translation)
The claim follows from `isLocallyConstant_ordDet_GL {k : ℤ | j * m ≤ k ∧ k < j * m + m}`.
-/
theorem isOpen_tile (j : ℤ) : IsOpen (tile F m j) :=
  isLocallyConstant_ordDet_GL {k : ℤ | j * m ≤ k ∧ k < j * m + m}

/- English proof (translation)
The claim follows from `(isOpen_tile j).measurableSet`.
-/
theorem measurableSet_tile [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)] (j : ℤ) :
    MeasurableSet (tile F m j) :=
  (isOpen_tile j).measurableSet

/- English proof (translation)
Establish `hm : (0 : ℤ) < m` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)`. Take `⟨h1, h2⟩` from `h`. Take `⟨h1', h2'⟩` from `h'`. Establish `a : (j - j') * m < m` using `by linarith`. Establish `b : (j' - j) * m < m` using `by linarith`.

Establish `a' : j - j' < 1`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use the polynomial consequences of the given equalities and inequalities. Establish `b' : j' - j < 1`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use the polynomial consequences of the given equalities and inequalities. Use linear arithmetic over natural numbers and integers.
-/
theorem tile_eq_of_mem [NeZero m] {j j' : ℤ} {g : GL (Fin m) F} (h : g ∈ tile F m j)
    (h' : g ∈ tile F m j') : j = j' := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  have a : (j - j') * m < m := by linarith
  have b : (j' - j) * m < m := by linarith
  have a' : j - j' < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  have b' : j' - j < 1 := by
    by_contra hc
    push Not at hc
    nlinarith
  omega

/- English proof (translation)
Introduce `_ _ hjj` and use `Set.disjoint_left.2 fun _ h h' => hjj (tile_eq_of_mem h h')`.
-/
theorem pairwise_disjoint_tile [NeZero m] : Pairwise (Function.onFun Disjoint (tile F m)) :=
  fun _ _ hjj => Set.disjoint_left.2 fun _ h h' => hjj (tile_eq_of_mem h h')

/- English proof (translation)
Establish `hm : (0 : ℤ) < m` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm]`. Conclude with `Int.mul_ediv_self_le hm.ne'`. Rewrite using `[mul_comm]`.

Conclude with `Int.lt_mul_ediv_self_add hm`.
-/
theorem mem_tile_div [NeZero m] (g : GL (Fin m) F) : g ∈ tile F m (ordDet g / m) := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine ⟨?_, ?_⟩
  · rw [mul_comm]; exact Int.mul_ediv_self_le hm.ne'
  · rw [mul_comm]; exact Int.lt_mul_ediv_self_add hm

/- English proof (translation)
The claim follows from `Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, mem_tile_div g⟩`.
-/
theorem iUnion_tile [NeZero m] : (⋃ j : ℤ, tile F m j) = Set.univ :=
  Set.eq_univ_of_forall fun g => Set.mem_iUnion.2 ⟨_, mem_tile_div g⟩

/- English proof (translation)
Simplify using `only [tile, Set.mem_ofPred_eq, ordDet_centralUnif_zpow_mul, zero_mul, zero_add]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩`. Introduce and unpack `⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩`.
-/
theorem centralUnif_zpow_mul_mem_tile_iff (j : ℤ) (g : GL (Fin m) F) :
    centralUnif F m ^ j * g ∈ tile F m j ↔ g ∈ tile F m 0 := by
  simp only [tile, Set.mem_ofPred_eq, ordDet_centralUnif_zpow_mul, zero_mul, zero_add]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

variable [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)]

/- English proof (translation)
Rewrite using `[← setLIntegral_univ, ← iUnion_tile, lintegral_iUnion measurableSet_tile pairwise_disjoint_tile]`. Use `tsum_congr fun j => ?_` and prove the remaining obligations. Rewrite using `[← lintegral_indicator (measurableSet_tile j), ← lintegral_indicator (measurableSet_tile 0), ← lintegral_mul_left_eq_self _ (centralUnif F m ^ j)]`. Use `lintegral_congr fun g => ?_` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ tile F m 0`.

Rewrite using `[Set.indicator_of_mem ((centralUnif_zpow_mul_mem_tile_iff j g).2 hg), Set.indicator_of_mem hg]`. Rewrite using `[Set.indicator_of_notMem (mt (centralUnif_zpow_mul_mem_tile_iff j g).1 hg), Set.indicator_of_notMem hg]`.
-/
theorem lintegral_eq_tsum_tile [NeZero m] (μ : Measure (GL (Fin m) F)) [μ.IsMulLeftInvariant]
    (f : GL (Fin m) F → ℝ≥0∞) :
    ∫⁻ g, f g ∂μ = ∑' j : ℤ, ∫⁻ g in tile F m 0, f (centralUnif F m ^ j * g) ∂μ := by
  rw [← setLIntegral_univ, ← iUnion_tile, lintegral_iUnion measurableSet_tile pairwise_disjoint_tile]
  refine tsum_congr fun j => ?_
  rw [← lintegral_indicator (measurableSet_tile j), ← lintegral_indicator (measurableSet_tile 0),
    ← lintegral_mul_left_eq_self _ (centralUnif F m ^ j)]
  refine lintegral_congr fun g => ?_
  by_cases hg : g ∈ tile F m 0
  · rw [Set.indicator_of_mem ((centralUnif_zpow_mul_mem_tile_iff j g).2 hg),
      Set.indicator_of_mem hg]
  · rw [Set.indicator_of_notMem (mt (centralUnif_zpow_mul_mem_tile_iff j g).1 hg),
      Set.indicator_of_notMem hg]

/- English proof (translation)
Establish `h` using `hasSum_integral_iUnion (μ := μ) (f := f) measurableSet_tile pairwise_disjoint_tile hf.integrableOn`. Rewrite `h` using `[iUnion_tile, Measure.restrict_univ]`. Establish `e : (fun j : ℤ => ∫ g in tile F m 0, f (centralUnif F m ^ j * g) ∂μ) = fun j : ℤ => ∫ g in tile F m j, f g ∂μ`. Use function extensionality and compare the values at `j`. Rewrite using `[← integral_indicator (measurableSet_tile 0), ← integral_indicator (measurableSet_tile j), ← integral_mul_left_eq_self ((tile F m j).indicator f) (centralUnif F m ^ j)]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Use `show _ = (tile F m j).indicator f (centralUnif F m ^ j * g)`. Distinguish the cases in `hg : g ∈ tile F m 0`. Rewrite using `[Set.indicator_of_mem hg, Set.indicator_of_mem ((centralUnif_zpow_mul_mem_tile_iff j g).2 hg)]`. Rewrite using `[Set.indicator_of_notMem hg, Set.indicator_of_notMem (mt (centralUnif_zpow_mul_mem_tile_iff j g).1 hg)]`.

Rewrite using `[e]`. Conclude with `h`.
-/
theorem hasSum_integral_tile [NeZero m] (μ : Measure (GL (Fin m) F)) [μ.IsMulLeftInvariant]
    {f : GL (Fin m) F → ℂ} (hf : Integrable f μ) :
    HasSum (fun j : ℤ => ∫ g in tile F m 0, f (centralUnif F m ^ j * g) ∂μ) (∫ g, f g ∂μ) := by
  have h := hasSum_integral_iUnion (μ := μ) (f := f) measurableSet_tile pairwise_disjoint_tile
    hf.integrableOn
  rw [iUnion_tile, Measure.restrict_univ] at h
  have e : (fun j : ℤ => ∫ g in tile F m 0, f (centralUnif F m ^ j * g) ∂μ) =
      fun j : ℤ => ∫ g in tile F m j, f g ∂μ := by
    funext j
    rw [← integral_indicator (measurableSet_tile 0), ← integral_indicator (measurableSet_tile j),
      ← integral_mul_left_eq_self ((tile F m j).indicator f) (centralUnif F m ^ j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    show _ = (tile F m j).indicator f (centralUnif F m ^ j * g)
    by_cases hg : g ∈ tile F m 0
    · rw [Set.indicator_of_mem hg,
        Set.indicator_of_mem ((centralUnif_zpow_mul_mem_tile_iff j g).2 hg)]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem (mt (centralUnif_zpow_mul_mem_tile_iff j g).1 hg)]
  rw [e]
  exact h

section Null

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `h0 : μ₁ {a} = μ₁ {0}`. Rewrite using `[show ({a} : Set F) = (fun x => x + -a) ⁻¹' {0} by`. Use extensionality with `x`. Simplify using `[← sub_eq_add_neg, sub_eq_zero]]`. Conclude with `measure_preimage_add_right μ₁ (-a) {0}`.

Rewrite using `[h0]`. Establish `hq : (1 : ℝ≥0∞) < (LocalField.residueCard F : ℝ≥0∞)`. Conclude with `LocalField.one_lt_residueCard (K := F)` after adjusting the coercions. Establish `hq0 : (LocalField.residueCard F : ℝ≥0∞) ≠ 0` using `(zero_lt_one.trans hq).ne'`. Use `set C := μ₁ (LocalField.valBall F 0)`.

Establish `hC : C ≠ ∞` using `(LocalField.isCompact_valBall 0).measure_lt_top.ne`. Establish `hle : ∀ k : ℕ, μ₁ {0} ≤ ((LocalField.residueCard F : ℝ≥0∞)⁻¹) ^ k * C` using `fun k => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[LocalField.measure_valBall μ₁ k]`. Use `congr 1`.

Establish `e : ((LocalField.residueCard F : ℝ≥0) ^ (-(k : ℤ)) : ℝ≥0) = ((LocalField.residueCard F : ℝ≥0)⁻¹) ^ k`. Rewrite using `[_root_.zpow_neg, zpow_natCast, inv_pow]`. Rewrite using `[e, ENNReal.coe_pow, ENNReal.coe_inv (by exact_mod_cast LocalField.residueCard_nnreal_ne_zero)]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `ht : Filter.Tendsto (fun k : ℕ => ((LocalField.residueCard F : ℝ≥0∞)⁻¹) ^ k * C) Filter.atTop (nhds 0)`. Establish `h1` using `ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (LocalField.residueCard F : ℝ≥0∞)⁻¹) (ENNReal.inv_lt_one.2 hq)`. Simplify using `using ENNReal.Tendsto.mul_const h1 (Or.inr hC)`. Conclude with `le_antisymm (ge_of_tendsto' ht hle) bot_le`.
-/
theorem measure_singleton_eq_zero (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (a : F) : μ₁ {a} = 0 := by
  have h0 : μ₁ {a} = μ₁ {0} := by
    rw [show ({a} : Set F) = (fun x => x + -a) ⁻¹' {0} by
      ext x; simp [← sub_eq_add_neg, sub_eq_zero]]
    exact measure_preimage_add_right μ₁ (-a) {0}
  rw [h0]
  have hq : (1 : ℝ≥0∞) < (LocalField.residueCard F : ℝ≥0∞) := by
    exact_mod_cast LocalField.one_lt_residueCard (K := F)
  have hq0 : (LocalField.residueCard F : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans hq).ne'
  set C := μ₁ (LocalField.valBall F 0)
  have hC : C ≠ ∞ := (LocalField.isCompact_valBall 0).measure_lt_top.ne
  have hle : ∀ k : ℕ, μ₁ {0} ≤ ((LocalField.residueCard F : ℝ≥0∞)⁻¹) ^ k * C := fun k => by
    calc μ₁ {0} ≤ μ₁ (LocalField.valBall F k) :=
          measure_mono (Set.singleton_subset_iff.2 (zero_mem _))
      _ = _ := by
          rw [LocalField.measure_valBall μ₁ k]
          congr 1
          have e : ((LocalField.residueCard F : ℝ≥0) ^ (-(k : ℤ)) : ℝ≥0) =
              ((LocalField.residueCard F : ℝ≥0)⁻¹) ^ k := by
            rw [_root_.zpow_neg, zpow_natCast, inv_pow]
          rw [e, ENNReal.coe_pow, ENNReal.coe_inv
            (by exact_mod_cast LocalField.residueCard_nnreal_ne_zero)]
          push_cast
          rfl
  have ht : Filter.Tendsto (fun k : ℕ => ((LocalField.residueCard F : ℝ≥0∞)⁻¹) ^ k * C)
      Filter.atTop (nhds 0) := by
    have h1 := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (LocalField.residueCard F : ℝ≥0∞)⁻¹)
      (ENNReal.inv_lt_one.2 hq)
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hC)
  exact le_antisymm (ge_of_tendsto' ht hle) bot_le

/- English proof (translation)
Establish `: s = ⋃ a ∈ s, ({a} : Set F)` using `by simp`. Rewrite using `[this, measure_biUnion_null_iff hs.countable]`. Conclude with `fun a _ => measure_singleton_eq_zero μ₁ a`.
-/
theorem measure_finite_eq_zero (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] {s : Set F} (hs : s.Finite) :
    μ₁ s = 0 := by
  have : s = ⋃ a ∈ s, ({a} : Set F) := by simp
  rw [this, measure_biUnion_null_iff hs.countable]
  exact fun a _ => measure_singleton_eq_zero μ₁ a

instance isAddHaarMeasure_matrixMeasure_finSq (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    (matrixMeasure (n := Fin m) μ₁).IsAddHaarMeasure := by
  have : (Measure.pi fun _ : Fin m => μ₁).IsAddHaarMeasure := inferInstance
  unfold matrixMeasure
  exact Measure.pi.isAddHaarMeasure _

instance : SecondCountableTopology (Matrix (Fin m) (Fin m) F) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin m → F))

/- English proof (translation)
Use `set μ := matrixMeasure (n := Fin m) μ₁`. Use `set ν := μ₁.restrict (LocalField.valBall F 0)`. Use `set S : Set (Matrix (Fin m) (Fin m) F) := {X | X.det = 0} with hS`. Use `set P : Set (Matrix (Fin m) (Fin m) F × F) := {p | (p.1 + p.2 • (1 : Matrix (Fin m) (Fin m) F)).det = 0} with hPdef`. Establish `hcont : Continuous fun p : Matrix (Fin m) (Fin m) F × F => (p.1 + p.2 • (1 : Matrix (Fin m) (Fin m) F)).det` using `(continuous_fst.add (continuous_snd.smul continuous_const)).matrix_det`.

Establish `hP : MeasurableSet P` using `(isClosed_singleton.preimage hcont).measurableSet`. Establish `h1 : (μ.prod ν) P = 0`. Rewrite using `[Measure.prod_apply hP]`. Establish `hz : ∀ X : Matrix (Fin m) (Fin m) F, ν (Prod.mk X ⁻¹' P) = 0` using `fun X => by`. Establish `hsub : Prod.mk X ⁻¹' P ⊆ {t : F | (Matrix.charpoly (-X)).IsRoot t}`.

Introduce `t ht`. Simplify using `only [Set.mem_preimage, hPdef, Set.mem_ofPred_eq] at ht`. Simplify using `only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly]`. Rewrite using `[← ht]`. Use `congr 1`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Matrix.scalar_apply]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `[Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]`. Establish `hfin` using `Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-X)).ne_zero`. Establish `hle : ν {t : F | (Matrix.charpoly (-X)).IsRoot t} ≤ μ₁ {t : F | (Matrix.charpoly (-X)).IsRoot t}` using `Measure.restrict_apply_le _ _`. Conclude with `measure_mono_null hsub (le_antisymm (hle.trans (measure_finite_eq_zero μ₁ hfin).le) bot_le)`. Simplify using `[hz]`.

Establish `h2 : (μ.prod ν) P = μ S * ν Set.univ`. Rewrite using `[Measure.prod_apply_symm hP]`. Establish `hz : ∀ t : F, μ ((fun X => (X, t)) ⁻¹' P) = μ S` using `fun t => by`. Establish `: (fun X => (X, t)) ⁻¹' P = (fun X => X + t • (1 : Matrix (Fin m) (Fin m) F)) ⁻¹' S`. Use extensionality with `X`.

Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `measure_preimage_add_right μ _ S`. Simplify using `only [hz, lintegral_const, mul_comm]`. Establish `hν : ν Set.univ ≠ 0`.

Rewrite using `[Measure.restrict_apply_univ]`. Conclude with `((LocalField.isOpen_valBall 0).measure_pos μ₁ ⟨0, zero_mem _⟩).ne'`. Use `h2.symm.trans h1` as an intermediate fact. Conclude with `(mul_eq_zero.1 this).resolve_right hν`.
-/
theorem matrixMeasure_det_eq_zero (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    matrixMeasure (n := Fin m) μ₁ {X : Matrix (Fin m) (Fin m) F | X.det = 0} = 0 := by
  set μ := matrixMeasure (n := Fin m) μ₁
  set ν := μ₁.restrict (LocalField.valBall F 0)
  set S : Set (Matrix (Fin m) (Fin m) F) := {X | X.det = 0} with hS
  set P : Set (Matrix (Fin m) (Fin m) F × F) := {p | (p.1 + p.2 • (1 : Matrix (Fin m) (Fin m) F)).det = 0}
    with hPdef
  have hcont : Continuous fun p : Matrix (Fin m) (Fin m) F × F =>
      (p.1 + p.2 • (1 : Matrix (Fin m) (Fin m) F)).det :=
    (continuous_fst.add (continuous_snd.smul continuous_const)).matrix_det
  have hP : MeasurableSet P := (isClosed_singleton.preimage hcont).measurableSet
  have h1 : (μ.prod ν) P = 0 := by
    rw [Measure.prod_apply hP]
    have hz : ∀ X : Matrix (Fin m) (Fin m) F, ν (Prod.mk X ⁻¹' P) = 0 := fun X => by
      have hsub : Prod.mk X ⁻¹' P ⊆ {t : F | (Matrix.charpoly (-X)).IsRoot t} := by
        intro t ht
        simp only [Set.mem_preimage, hPdef, Set.mem_ofPred_eq] at ht
        simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Matrix.eval_charpoly]
        rw [← ht]
        congr 1
        ext i j
        by_cases hij : i = j
        · subst hij; simp [Matrix.scalar_apply]; ring
        · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
      have hfin := Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-X)).ne_zero
      have hle : ν {t : F | (Matrix.charpoly (-X)).IsRoot t} ≤
          μ₁ {t : F | (Matrix.charpoly (-X)).IsRoot t} := Measure.restrict_apply_le _ _
      exact measure_mono_null hsub (le_antisymm (hle.trans (measure_finite_eq_zero μ₁ hfin).le) bot_le)
    simp [hz]
  have h2 : (μ.prod ν) P = μ S * ν Set.univ := by
    rw [Measure.prod_apply_symm hP]
    have hz : ∀ t : F, μ ((fun X => (X, t)) ⁻¹' P) = μ S := fun t => by
      have : (fun X => (X, t)) ⁻¹' P = (fun X => X + t • (1 : Matrix (Fin m) (Fin m) F)) ⁻¹' S := by
        ext X; rfl
      rw [this]
      exact measure_preimage_add_right μ _ S
    simp only [hz, lintegral_const, mul_comm]
  have hν : ν Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ]
    exact ((LocalField.isOpen_valBall 0).measure_pos μ₁ ⟨0, zero_mem _⟩).ne'
  have := h2.symm.trans h1
  exact (mul_eq_zero.1 this).resolve_right hν

end Null

section Change

variable [MeasurableSpace F] [BorelSpace F]

/- English proof (translation)
Establish `hLc : Continuous L` using `L.toLinearMap.continuous_on_pi`. Establish `hLic : Continuous L.symm` using `L.symm.toLinearMap.continuous_on_pi`. Set `e : (ι → F) ≃ₜ (ι → F)` to `⟨L.toEquiv, hLc, hLic⟩`. Establish `hmap : Measure.map L μ₀ = ((distribHaarChar (ι → F) L)⁻¹ : ℝ≥0) • μ₀`. Use extensionality with `S hS`.

Rewrite using `[Measure.map_apply hLc.measurable hS, Measure.smul_apply]`. Establish `h` using `distribHaarChar_mul μ₀ L⁻¹ S`. Establish `hpre : (L : (ι → F) → (ι → F)) ⁻¹' S = L⁻¹ • S`. Use extensionality with `x`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, inv_inv, LinearEquiv.smul_def]`.

Both sides reduce to the same expression. Rewrite using `[hpre, ← h, map_inv, ENNReal.smul_def, smul_eq_mul]`. Use `e.measurableEmbedding.integral_map (μ := μ₀) f` as an intermediate fact. Express the relevant statement in the definitionally equal form `∫ y, f y ∂(Measure.map L μ₀) = _ at this`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem integral_comp_linearEquiv {ι : Type*} [Fintype ι] (μ₀ : Measure (ι → F))
    [μ₀.IsAddHaarMeasure] (L : (ι → F) ≃ₗ[F] (ι → F)) (f : (ι → F) → ℂ) :
    ∫ x, f (L x) ∂μ₀ = ((distribHaarChar (ι → F) L : ℝ≥0) : ℝ)⁻¹ • ∫ x, f x ∂μ₀ := by
  have hLc : Continuous L := L.toLinearMap.continuous_on_pi
  have hLic : Continuous L.symm := L.symm.toLinearMap.continuous_on_pi
  let e : (ι → F) ≃ₜ (ι → F) := ⟨L.toEquiv, hLc, hLic⟩
  have hmap : Measure.map L μ₀ = ((distribHaarChar (ι → F) L)⁻¹ : ℝ≥0) • μ₀ := by
    ext S hS
    rw [Measure.map_apply hLc.measurable hS, Measure.smul_apply]
    have h := distribHaarChar_mul μ₀ L⁻¹ S
    have hpre : (L : (ι → F) → (ι → F)) ⁻¹' S = L⁻¹ • S := by
      ext x
      rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, LinearEquiv.smul_def]
      rfl
    rw [hpre, ← h, map_inv, ENNReal.smul_def, smul_eq_mul]
  have := e.measurableEmbedding.integral_map (μ := μ₀) f
  change ∫ y, f y ∂(Measure.map L μ₀) = _ at this
  calc ∫ x, f (L x) ∂μ₀ = ∫ x, f (e x) ∂μ₀ := rfl
    _ = _ := by rw [← this, hmap, integral_smul_nnreal_measure, NNReal.smul_def, NNReal.coe_inv]

/- English proof (translation)
Establish `hmp` using `measurePreserving_matrixCoord (n := Fin m) μ₁`. Establish `hinj : Function.Injective (matrixCoord : Matrix (Fin m) (Fin m) F → Fin m × Fin m → F)` using `(Measures.entries F m).injective`. Establish `himg : MeasurableSet ((matrixCoord : Matrix (Fin m) (Fin m) F → Fin m × Fin m → F) '' X)` using `(Measures.entriesHomeomorph F m).measurableEmbedding.measurableSet_image.2 hX`. Express the relevant statement in the definitionally equal form `_ = (Measure.pi fun _ : Fin m × Fin m => μ₁) ((matrixCoord : Matrix (Fin m) (Fin m) F → Fin m × Fin m → F) '' X)`. Rewrite using `[← hmp.measure_preimage himg.nullMeasurableSet, Set.preimage_image_eq _ hinj]`.
-/
theorem matrixMeasure_apply_eq_pi (μ₁ : Measure F) [μ₁.IsAddHaarMeasure]
    {X : Set (Matrix (Fin m) (Fin m) F)} (hX : MeasurableSet X) :
    matrixMeasure (n := Fin m) μ₁ X =
      (Measure.pi fun _ : Fin m × Fin m => μ₁) (Measures.entries F m '' X) := by
  have hmp := measurePreserving_matrixCoord (n := Fin m) μ₁
  have hinj : Function.Injective (matrixCoord : Matrix (Fin m) (Fin m) F → Fin m × Fin m → F) :=
    (Measures.entries F m).injective
  have himg : MeasurableSet ((matrixCoord : Matrix (Fin m) (Fin m) F → Fin m × Fin m → F) '' X) :=
    (Measures.entriesHomeomorph F m).measurableEmbedding.measurableSet_image.2 hX
  change _ = (Measure.pi fun _ : Fin m × Fin m => μ₁)
    ((matrixCoord : Matrix (Fin m) (Fin m) F → Fin m × Fin m → F) '' X)
  rw [← hmp.measure_preimage himg.nullMeasurableSet, Set.preimage_image_eq _ hinj]

/- English proof (translation)
Establish `hmp` using `measurePreserving_matrixCoord (n := Fin m) μ₁`. Rewrite using `[← hmp.integral_comp (Measures.entriesHomeomorph F m).measurableEmbedding]`. Both sides reduce to the same expression.
-/
theorem integral_matrixMeasure_eq_pi (μ₁ : Measure F) [μ₁.IsAddHaarMeasure]
    (f : Matrix (Fin m) (Fin m) F → ℂ) :
    ∫ X, f X ∂matrixMeasure (n := Fin m) μ₁ =
      ∫ x, f ((Measures.entries F m).symm x) ∂(Measure.pi fun _ : Fin m × Fin m => μ₁) := by
  have hmp := measurePreserving_matrixCoord (n := Fin m) μ₁
  rw [← hmp.integral_comp (Measures.entriesHomeomorph F m).measurableEmbedding]
  rfl

/- English proof (translation)
Rewrite using `[integral_matrixMeasure_eq_pi, integral_matrixMeasure_eq_pi]`. Establish `h` using `integral_comp_linearEquiv (Measure.pi fun _ : Fin m × Fin m => μ₁) ((Measures.glChart F m).right y) (fun x => f ((Measures.entries F m).symm x))`. Establish `hR : ∀ x, (Measures.entries F m).symm ((Measures.glChart F m).right y x) = (Measures.entries F m).symm x * (y : Matrix (Fin m) (Fin m) F)` using `fun x => by`. Simplify using `[Measures.glChart]`. Simplify using `only [hR] at h`.

Rewrite using `[h]`. Use `congr 2`. Establish `hc` using `Measures.glChart_rightModulus F m y`. Rewrite `hc` using `[Measures.LinearChart.rightModulus]`. Rewrite using `[hc, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem integral_comp_mul_right_matrix (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (y : GL (Fin m) F)
    (f : Matrix (Fin m) (Fin m) F → ℂ) :
    ∫ X, f (X * (y : Matrix (Fin m) (Fin m) F)) ∂matrixMeasure (n := Fin m) μ₁ =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m)⁻¹ •
        ∫ X, f X ∂matrixMeasure (n := Fin m) μ₁ := by
  rw [integral_matrixMeasure_eq_pi, integral_matrixMeasure_eq_pi]
  have h := integral_comp_linearEquiv (Measure.pi fun _ : Fin m × Fin m => μ₁)
    ((Measures.glChart F m).right y) (fun x => f ((Measures.entries F m).symm x))
  have hR : ∀ x, (Measures.entries F m).symm ((Measures.glChart F m).right y x) =
      (Measures.entries F m).symm x * (y : Matrix (Fin m) (Fin m) F) := fun x => by
    simp [Measures.glChart]
  simp only [hR] at h
  rw [h]
  congr 2
  have hc := Measures.glChart_rightModulus F m y
  rw [Measures.LinearChart.rightModulus] at hc
  rw [hc, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]
  push_cast
  rfl

/- English proof (translation)
Rewrite using `[integral_matrixMeasure_eq_pi, integral_matrixMeasure_eq_pi]`. Establish `h` using `integral_comp_linearEquiv (Measure.pi fun _ : Fin m × Fin m => μ₁) ((Measures.glChart F m).left y) (fun x => f ((Measures.entries F m).symm x))`. Establish `hL : ∀ x, (Measures.entries F m).symm ((Measures.glChart F m).left y x) = (y : Matrix (Fin m) (Fin m) F) * (Measures.entries F m).symm x` using `fun x => by`. Simplify using `[Measures.glChart]`. Simplify using `only [hL] at h`.

Rewrite using `[h]`. Use `congr 2`. Establish `hc` using `Measures.glChart_leftModulus F m y`. Rewrite `hc` using `[Measures.LinearChart.leftModulus]`. Rewrite using `[hc, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem integral_comp_mul_left_matrix (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] (y : GL (Fin m) F)
    (f : Matrix (Fin m) (Fin m) F → ℂ) :
    ∫ X, f ((y : Matrix (Fin m) (Fin m) F) * X) ∂matrixMeasure (n := Fin m) μ₁ =
      ((LocalField.modulus (y : Matrix (Fin m) (Fin m) F).det : ℝ) ^ m)⁻¹ •
        ∫ X, f X ∂matrixMeasure (n := Fin m) μ₁ := by
  rw [integral_matrixMeasure_eq_pi, integral_matrixMeasure_eq_pi]
  have h := integral_comp_linearEquiv (Measure.pi fun _ : Fin m × Fin m => μ₁)
    ((Measures.glChart F m).left y) (fun x => f ((Measures.entries F m).symm x))
  have hL : ∀ x, (Measures.entries F m).symm ((Measures.glChart F m).left y x) =
      (y : Matrix (Fin m) (Fin m) F) * (Measures.entries F m).symm x := fun x => by
    simp [Measures.glChart]
  simp only [hL] at h
  rw [h]
  congr 2
  have hc := Measures.glChart_leftModulus F m y
  rw [Measures.LinearChart.leftModulus] at hc
  rw [hc, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply]
  push_cast
  rfl

def detModulusPow (g : GL (Fin m) F) : ℝ≥0 :=
  LocalField.modulus (g : Matrix (Fin m) (Fin m) F).det ^ m

/- English proof (translation)
Rewrite using `[Measures.glChart_leftModulus, LocalField.distribHaarChar_eq_modulus, Matrix.GeneralLinearGroup.val_det_apply, detModulusPow]`.
-/
theorem detModulusPow_eq_leftModulus (g : GL (Fin m) F) :
    detModulusPow g = (Measures.glChart F m).leftModulus g := by
  rw [Measures.glChart_leftModulus, LocalField.distribHaarChar_eq_modulus,
    Matrix.GeneralLinearGroup.val_det_apply, detModulusPow]

/- English proof (translation)
Rewrite using `[detModulusPow_eq_leftModulus]`. Conclude with `Measures.LinearChart.leftModulus_pos _ g`.
-/
theorem detModulusPow_pos (g : GL (Fin m) F) : 0 < detModulusPow g := by
  rw [detModulusPow_eq_leftModulus]; exact Measures.LinearChart.leftModulus_pos _ g

/- English proof (translation)
Establish `: (detModulusPow (F` using `F) (m := m)) = fun g => (Measures.glChart F m).leftModulus g :=`. Use function extensionality and compare the values at `detModulusPow_eq_leftModulus`. Rewrite using `[this]`. Use `borelize F (GL (Fin m) F)`. Conclude with `Measures.LinearChart.continuous_leftModulus _`.
-/
theorem continuous_detModulusPow : Continuous (detModulusPow (F := F) (m := m)) := by
  have : (detModulusPow (F := F) (m := m)) = fun g => (Measures.glChart F m).leftModulus g :=
    funext detModulusPow_eq_leftModulus
  rw [this]
  borelize F (GL (Fin m) F)
  exact Measures.LinearChart.continuous_leftModulus _

/- English proof (translation)
Rewrite using `[detPow, absDet, detModulusPow, Complex.cpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem detPow_natCast (g : GL (Fin m) F) : detPow g (m : ℂ) = ((detModulusPow g : ℝ) : ℂ) := by
  rw [detPow, absDet, detModulusPow, Complex.cpow_natCast]
  push_cast
  rfl

/- English proof (translation)
Use `set μ₀ := Measure.pi fun _ : Fin m × Fin m => μ₁ with hμ₀`. Use `set C := Measures.glChart F m`. Use `set c := haarScalarFactor μ (Measures.haarGL F m μ₀) with hcdef`. Establish `hc : c ≠ 0` using `(haarScalarFactor_pos_of_isHaarMeasure μ _).ne'`. Establish `hμ : μ = c • Measures.haarGL F m μ₀` using `Measures.eq_smul_haarGL F m μ₀ μ`.

Establish `hρm : Measurable fun g : GL (Fin m) F => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)` using `(ENNReal.continuous_coe.comp continuous_detModulusPow).measurable`. Establish `hρim : Measurable fun g : GL (Fin m) F => (((C.leftModulus g)⁻¹ : ℝ≥0) : ℝ≥0∞)` using `C.measurable_density`. Establish `hwd : μ.withDensity (fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) = c • μ₀.comap C.toFun`. Rewrite using `[hμ, ENNReal.smul_def, withDensity_smul_measure, Measures.haarGL, Measures.LinearChart.haar, ← withDensity_mul _ hρim hρm, ENNReal.smul_def]`. Use `congr 1`.

Use `conv_rhs => rw [← withDensity_one (μ := μ₀.comap C.toFun)]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [Pi.mul_apply, Pi.one_apply, detModulusPow_eq_leftModulus]`. Rewrite using `[← ENNReal.coe_mul, inv_mul_cancel₀ (C.leftModulus_pos g).ne', ENNReal.coe_one]`.

Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[hwd, Measure.map_smul]`. Use `congr 1`. Establish `hv : MeasurableEmbedding (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F)` using `(Measures.isOpenEmbedding_val F m).measurableEmbedding`. Establish `hE : MeasurableEmbedding C.toFun` using `C.measurableEmbedding`.

Use extensionality with `S hS`. Rewrite using `[Measure.map_apply hv.measurable hS, hE.comap_apply]`. Establish `himg : C.toFun '' (Units.val ⁻¹' S) = Measures.entries F m '' (S ∩ Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨g, hg, rfl⟩`. Conclude with `⟨g, ⟨hg, g, rfl⟩, rfl⟩`. Introduce and unpack `⟨X, ⟨hX, g, rfl⟩, rfl⟩`. Conclude with `⟨g, hX, rfl⟩`. Establish `hrange : MeasurableSet (Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F))` using `hv.measurableSet_range`.

Rewrite using `[himg, ← matrixMeasure_apply_eq_pi μ₁ (hS.inter hrange)]`. Use `measure_congr ?_` and prove the remaining obligations. Establish `hnull : matrixMeasure (n` using `Fin m) μ₁ (Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F))ᶜ = 0 := by`. Use `measure_mono_null (fun X hX => ?_) (matrixMeasure_det_eq_zero μ₁)` and prove the remaining obligations. Assume the negation of the conclusion as `hdet`.

Conclude with `hX ⟨((Matrix.isUnit_iff_isUnit_det X).2 (isUnit_iff_ne_zero.2 hdet)).unit, rfl⟩`. Establish `h3 : (S ∩ Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F) : Set (Matrix (Fin m) (Fin m) F)) =ᵐ[matrixMeasure (n` using `Fin m) μ₁] S := by`. Use `(ae_eq_refl S).inter (ae_eq_univ.2 hnull)` as an intermediate fact. Rewrite `this` using `[Set.inter_univ]`. Then use the resulting hypothesis. Conclude with `h3`.
-/
theorem exists_map_val_withDensity [NeZero m] (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure]
    (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    ∃ κ : ℝ≥0, κ ≠ 0 ∧ Measure.map (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F)
      (μ.withDensity fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) =
        κ • matrixMeasure (n := Fin m) μ₁ := by
  set μ₀ := Measure.pi fun _ : Fin m × Fin m => μ₁ with hμ₀
  set C := Measures.glChart F m
  set c := haarScalarFactor μ (Measures.haarGL F m μ₀) with hcdef
  have hc : c ≠ 0 := (haarScalarFactor_pos_of_isHaarMeasure μ _).ne'
  have hμ : μ = c • Measures.haarGL F m μ₀ := Measures.eq_smul_haarGL F m μ₀ μ
  have hρm : Measurable fun g : GL (Fin m) F => ((detModulusPow g : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.continuous_coe.comp continuous_detModulusPow).measurable
  have hρim : Measurable fun g : GL (Fin m) F => (((C.leftModulus g)⁻¹ : ℝ≥0) : ℝ≥0∞) :=
    C.measurable_density
  have hwd : μ.withDensity (fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) =
      c • μ₀.comap C.toFun := by
    rw [hμ, ENNReal.smul_def, withDensity_smul_measure, Measures.haarGL, Measures.LinearChart.haar,
      ← withDensity_mul _ hρim hρm, ENNReal.smul_def]
    congr 1
    conv_rhs => rw [← withDensity_one (μ := μ₀.comap C.toFun)]
    congr 1
    funext g
    simp only [Pi.mul_apply, Pi.one_apply, detModulusPow_eq_leftModulus]
    rw [← ENNReal.coe_mul, inv_mul_cancel₀ (C.leftModulus_pos g).ne', ENNReal.coe_one]
  refine ⟨c, hc, ?_⟩
  rw [hwd, Measure.map_smul]
  congr 1
  have hv : MeasurableEmbedding (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F) :=
    (Measures.isOpenEmbedding_val F m).measurableEmbedding
  have hE : MeasurableEmbedding C.toFun := C.measurableEmbedding
  ext S hS
  rw [Measure.map_apply hv.measurable hS, hE.comap_apply]
  have himg : C.toFun '' (Units.val ⁻¹' S) =
      Measures.entries F m '' (S ∩ Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F)) := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, ⟨hg, g, rfl⟩, rfl⟩
    · rintro ⟨X, ⟨hX, g, rfl⟩, rfl⟩
      exact ⟨g, hX, rfl⟩
  have hrange : MeasurableSet (Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F)) :=
    hv.measurableSet_range
  rw [himg, ← matrixMeasure_apply_eq_pi μ₁ (hS.inter hrange)]
  refine measure_congr ?_
  have hnull : matrixMeasure (n := Fin m) μ₁
      (Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F))ᶜ = 0 := by
    refine measure_mono_null (fun X hX => ?_) (matrixMeasure_det_eq_zero μ₁)
    by_contra hdet
    exact hX ⟨((Matrix.isUnit_iff_isUnit_det X).2 (isUnit_iff_ne_zero.2 hdet)).unit, rfl⟩
  have h3 : (S ∩ Set.range (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F) :
      Set (Matrix (Fin m) (Fin m) F)) =ᵐ[matrixMeasure (n := Fin m) μ₁] S := by
    have := (ae_eq_refl S).inter (ae_eq_univ.2 hnull)
    rwa [Set.inter_univ] at this
  exact h3

/- English proof (translation)
Take `⟨κ, hκ, hmap⟩` from `exists_map_val_withDensity μ μ₁`. Establish `hv : MeasurableEmbedding (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F)` using `(Measures.isOpenEmbedding_val F m).measurableEmbedding`. Establish `hρ : Measurable (detModulusPow (F` using `F) (m := m)) := continuous_detModulusPow.measurable`. Use `⟨κ, hκ, fun f => ?_, fun f hf => ?_⟩` and prove the remaining obligations. Establish `h1` using `integral_withDensity_eq_integral_smul hρ (μ := μ) (fun g : GL (Fin m) F => f (g : Matrix (Fin m) (Fin m) F))`.

Establish `h2` using `hv.integral_map (μ := μ.withDensity fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) f`. Rewrite `h2` using `[hmap, integral_smul_nnreal_measure]`. Rewrite `h2` using `[NNReal.smul_def]`. Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Use `show f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) = detModulusPow g • f (g : Matrix (Fin m) (Fin m) F)`. Rewrite using `[detPow_natCast, NNReal.smul_def, Complex.real_smul, mul_comm]`. Use `_ = _ := by rw [← h1, ← h2]`. Establish `h1` using `lintegral_withDensity_eq_lintegral_mul μ (ENNReal.continuous_coe.comp continuous_detModulusPow).measurable (hf.comp hv.measurable)`. Establish `h2` using `hv.lintegral_map (μ := μ.withDensity fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) f`.

Rewrite `h2` using `[hmap, ENNReal.smul_def, lintegral_smul_measure]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `g`. Simplify using `only [Pi.mul_apply, Function.comp_apply]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by`. Use `h1.symm.trans h2.symm` as an intermediate fact. Rewrite `this` using `[smul_eq_mul]`. Conclude with `this`.
-/
theorem exists_integral_GL_eq [NeZero m] (μ : Measure (GL (Fin m) F)) [μ.IsHaarMeasure]
    (μ₁ : Measure F) [μ₁.IsAddHaarMeasure] :
    ∃ κ : ℝ≥0, κ ≠ 0 ∧
      (∀ f : Matrix (Fin m) (Fin m) F → ℂ,
        ∫ g, f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) ∂μ =
          (κ : ℝ) • ∫ X, f X ∂matrixMeasure (n := Fin m) μ₁) ∧
      (∀ f : Matrix (Fin m) (Fin m) F → ℝ≥0∞, Measurable f →
        ∫⁻ g, f (g : Matrix (Fin m) (Fin m) F) * (detModulusPow g : ℝ≥0∞) ∂μ =
          κ * ∫⁻ X, f X ∂matrixMeasure (n := Fin m) μ₁) := by
  obtain ⟨κ, hκ, hmap⟩ := exists_map_val_withDensity μ μ₁
  have hv : MeasurableEmbedding (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F) :=
    (Measures.isOpenEmbedding_val F m).measurableEmbedding
  have hρ : Measurable (detModulusPow (F := F) (m := m)) := continuous_detModulusPow.measurable
  refine ⟨κ, hκ, fun f => ?_, fun f hf => ?_⟩
  · have h1 := integral_withDensity_eq_integral_smul hρ (μ := μ)
      (fun g : GL (Fin m) F => f (g : Matrix (Fin m) (Fin m) F))
    have h2 := hv.integral_map (μ := μ.withDensity fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) f
    rw [hmap, integral_smul_nnreal_measure] at h2
    rw [NNReal.smul_def] at h2
    calc ∫ g, f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) ∂μ
        = ∫ g, detModulusPow g • f (g : Matrix (Fin m) (Fin m) F) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
          show f (g : Matrix (Fin m) (Fin m) F) * detPow g (m : ℂ) =
            detModulusPow g • f (g : Matrix (Fin m) (Fin m) F)
          rw [detPow_natCast, NNReal.smul_def, Complex.real_smul, mul_comm]
      _ = _ := by rw [← h1, ← h2]
  · have h1 := lintegral_withDensity_eq_lintegral_mul μ (ENNReal.continuous_coe.comp
      continuous_detModulusPow).measurable (hf.comp hv.measurable)
    have h2 := hv.lintegral_map (μ := μ.withDensity fun g => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) f
    rw [hmap, ENNReal.smul_def, lintegral_smul_measure] at h2
    calc ∫⁻ g, f (g : Matrix (Fin m) (Fin m) F) * (detModulusPow g : ℝ≥0∞) ∂μ
        = ∫⁻ g, (((fun g : GL (Fin m) F => ((detModulusPow g : ℝ≥0) : ℝ≥0∞)) *
            (f ∘ (Units.val : GL (Fin m) F → Matrix (Fin m) (Fin m) F))) g) ∂μ := by
          congr 1; funext g; simp only [Pi.mul_apply, Function.comp_apply]; ring
      _ = _ := by
          have := h1.symm.trans h2.symm
          rw [smul_eq_mul] at this
          exact this

end Change

end GodementJacquet

end GroundTheory.Automorphic
