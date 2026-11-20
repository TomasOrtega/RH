import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitQuotientTopology.MeasurableStabActOne

open Matrix MeasureTheory Measure Topology Set
open scoped ENNReal

noncomputable section

namespace PI.AmpOrbQuot

open Formalism.QuantumDeterminants Formalism.MainNotions.S PI.AmpRootCommon

variable {k r : ℕ}

/- English proof (translation)
Establish `e : (Inv.inv : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → _) = fun b => (b.det)⁻¹ • b.adjugate`. Use function extensionality and compare the values at `b`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv]`. Rewrite using `[e]`. Conclude with `((continuous_id.matrix_det.continuousAt).inv₀ h).smul continuous_id.matrix_adjugate.continuousAt`.
-/
theorem continuousAt_inv_of_det {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (h : a.det ≠ 0) :
    ContinuousAt (Inv.inv : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → _) a := by
  have e : (Inv.inv : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → _) =
      fun b => (b.det)⁻¹ • b.adjugate := by
    funext b
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [e]
  exact ((continuous_id.matrix_det.continuousAt).inv₀ h).smul continuous_id.matrix_adjugate.continuousAt

/- English proof (translation)
Use `⟨fun n => Metric.closedBall 0 n, fun n => isCompact_closedBall 0 n, fun x => ?_⟩` and prove the remaining obligations. Take `⟨n, hn⟩` from `exists_nat_gt (dist x 0)`. Conclude with `⟨n, mem_interior.mpr ⟨Metric.ball 0 n, Metric.ball_subset_closedBall, Metric.isOpen_ball, hn⟩⟩`.
-/
theorem exists_cover' : ∃ K : ℕ → Set (Mt k r), (∀ n, IsCompact (K n)) ∧ ∀ x, ∃ n, x ∈ interior (K n) := by
  refine ⟨fun n => Metric.closedBall 0 n, fun n => isCompact_closedBall 0 n, fun x => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (dist x 0)
  exact ⟨n, mem_interior.mpr ⟨Metric.ball 0 n, Metric.ball_subset_closedBall, Metric.isOpen_ball, hn⟩⟩

section Cut

variable (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR : Measure (Mt k r)) (K : ℕ → Set (Mt k r))

def nInv (a : Mt k r) (y : PairSp k r) : Mt k r := (stabAct g (Matrix.of a)⁻¹ y).1.2

def Phi (m : ℕ) (y : PairSp k r) : ℝ≥0∞ := μR {a | nInv g a y ∈ K m}

def Eset (m : ℕ) : Set (PairSp k r) := {y | Phi g μR K m y ≠ 0 ∧ ∀ j < m, Phi g μR K j y = 0}

def theta (y : PairSp k r) : ℝ≥0∞ :=
  ∑' m, (Eset g μR K m).indicator (fun y => (K m).indicator 1 y.1.2 * (Phi g μR K m y)⁻¹) y

/- English proof (translation)
The claim follows from `(measurable_stabAct_inv g).fst.snd`.
-/
theorem measurable_nInv : Measurable (fun p : Mt k r × PairSp k r => nInv g p.1 p.2) := (measurable_stabAct_inv g).fst.snd

/- English proof (translation)
Establish `hs : MeasurableSet ((fun p : Mt k r × PairSp k r => nInv g p.1 p.2) ⁻¹' K m)` using `measurable_nInv g (hK m).measurableSet`. Use `first`. Consider the case `exact measurable_measure_prodMk_right hs`. Consider the case `exact measurable_measure_prod_mk_right hs`.
-/
theorem measurable_Phi [SFinite μR] (hK : ∀ m, IsClosed (K m)) (m : ℕ) : Measurable (Phi g μR K m) := by
  have hs : MeasurableSet ((fun p : Mt k r × PairSp k r => nInv g p.1 p.2) ⁻¹' K m) :=
    measurable_nInv g (hK m).measurableSet
  first
    | exact measurable_measure_prodMk_right hs
    | exact measurable_measure_prod_mk_right hs

/- English proof (translation)
Establish `h1 : MeasurableSet {y | Phi g μR K m y ≠ 0}` using `((measurable_Phi g μR K hK m) (measurableSet_singleton 0)).compl`. Establish `h2 : MeasurableSet {y | ∀ j < m, Phi g μR K j y = 0}`. Establish `e : {y | ∀ j < m, Phi g μR K j y = 0} = ⋂ j ∈ Finset.range m, (Phi g μR K j) ⁻¹' {0}`. Use extensionality with `y`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `Finset.measurableSet_biInter _ (fun j _ => measurable_Phi g μR K hK j (measurableSet_singleton 0))`. Conclude with `h1.inter h2`.
-/
theorem measurable_Eset [SFinite μR] (hK : ∀ m, IsClosed (K m)) (m : ℕ) : MeasurableSet (Eset g μR K m) := by
  have h1 : MeasurableSet {y | Phi g μR K m y ≠ 0} :=
    ((measurable_Phi g μR K hK m) (measurableSet_singleton 0)).compl
  have h2 : MeasurableSet {y | ∀ j < m, Phi g μR K j y = 0} := by
    have e : {y | ∀ j < m, Phi g μR K j y = 0} = ⋂ j ∈ Finset.range m, (Phi g μR K j) ⁻¹' {0} := by
      ext y; simp
    rw [e]
    exact Finset.measurableSet_biInter _ (fun j _ => measurable_Phi g μR K hK j (measurableSet_singleton 0))
  exact h1.inter h2

/- English proof (translation)
Use `Measurable.ennreal_tsum (fun m => ?_)` and prove the remaining obligations. Use `Measurable.indicator ?_ (measurable_Eset g μR K hK m)` and prove the remaining obligations. Apply the tactic sequence `refine Measurable.mul ?_ (by first | exact (measurable_Phi g μR K hK m).inv | exact measurable_inv.comp (measurable_Phi g μR K hK m))`. Conclude with `(measurable_one.indicator (hK m).measurableSet).comp measurable_fst.snd`.
-/
theorem measurable_theta [SFinite μR] (hK : ∀ m, IsClosed (K m)) : Measurable (theta g μR K) := by
  refine Measurable.ennreal_tsum (fun m => ?_)
  refine Measurable.indicator ?_ (measurable_Eset g μR K hK m)
  refine Measurable.mul ?_ (by first | exact (measurable_Phi g μR K hK m).inv | exact measurable_inv.comp (measurable_Phi g μR K hK m))
  exact (measurable_one.indicator (hK m).measurableSet).comp measurable_fst.snd

variable {g μR K}

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Apply the tactic sequence `have hs : (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) < 2 * r + k + 1 := by split_ifs <;> omega`. Rewrite using `[Finset.sum_eq_single (⟨_, hs⟩ : Fin (2 * r + k + 1))]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Rewrite using `[if_pos rfl]`. Simplify using `only [Hpk, Fin.ext_iff, Fin.val_mk, eq_self_iff_true, and_true]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num`. Rewrite using `[if_neg hij]`.

Rewrite `hij` using `[Fin.ext_iff]`. Simplify using `only [Hpk, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num`. Introduce `l _ hl`. Rewrite `hl` using `[Ne, Fin.ext_iff, Fin.val_mk]`.

Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs at * <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private theorem hpk_sq_lemma (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hs : (if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val) < 2 * r + k + 1 := by
    split_ifs <;> omega
  rw [Finset.sum_eq_single (⟨_, hs⟩ : Fin (2 * r + k + 1))]
  · by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      simp only [Hpk, Fin.ext_iff, Fin.val_mk, eq_self_iff_true, and_true]
      split_ifs <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num
    · rw [if_neg hij]
      rw [Fin.ext_iff] at hij
      simp only [Hpk, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num
  · intro l _ hl
    rw [Ne, Fin.ext_iff, Fin.val_mk] at hl
    simp only [Hpk, Fin.ext_iff]
    split_ifs at * <;> first | (exfalso; (try simp only [Fin.val_mk] at *); omega) | (simp_all; done) | norm_num
  · intro h
    exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Establish `hg' : gᴴ * Hpk k r * g = Hpk k r` using `hg`. Establish `h : Hpk k r * gᴴ * Hpk k r * g = 1`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Matrix.isUnit_det_of_left_inverse h`.
-/
private theorem isUnit_det_of_mem_UH' {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UH (Hpk k r)) :
    IsUnit g.det := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have h : Hpk k r * gᴴ * Hpk k r * g = 1 := by
    calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg', hpk_sq_lemma k r]
  exact Matrix.isUnit_det_of_left_inverse h

/- English proof (translation)
Establish `hd` using `isUnit_det_of_mem_UH' hb`. Use `show (Matrix.of a)⁻¹ * (b * Matrix.of y.1.2) = (b⁻¹ * Matrix.of a)⁻¹ * Matrix.of y.1.2`. Rewrite using `[Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv b hd, Matrix.mul_assoc]`.
-/
theorem nInv_act {b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hb : b ∈ UH (Hpk k r)) (a : Mt k r) (y : PairSp k r) :
    nInv g a (stabAct g b y) = nInv g (lmulM b⁻¹ a) y := by
  have hd := isUnit_det_of_mem_UH' hb
  show (Matrix.of a)⁻¹ * (b * Matrix.of y.1.2) = (b⁻¹ * Matrix.of a)⁻¹ * Matrix.of y.1.2
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv b hd, Matrix.mul_assoc]

/- English proof (translation)
Establish `hbU : b ∈ UH (Hpk k r)` using `hb.1.1`. Establish `hd` using `isUnit_det_of_mem_UH' hbU`. Establish `hof : Continuous (fun x : Mt k r => Matrix.of x)` using `continuous_id`. Establish `hl : ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Measurable (lmulM (k` using `k) (r := r) s) := by`. Introduce `s`.

Establish `hc : Continuous (lmulM (k` using `k) (r := r) s) := by`. Unfold `lmulM`. Use `first`. Consider the case `fun_prop`. Consider the case `continuity`.

Conclude with `hc.measurable`. Establish `hmk : Measurable (fun a : Mt k r => (a, y))` using `by first`. Consider the case `exact measurable_prodMk_right`. Consider the case `exact measurable_prod_mk_right`. Consider the case `fun_prop`.

Establish `hS : MeasurableSet {a : Mt k r | nInv g a y ∈ K m}` using `((measurable_nInv g).comp hmk) (hK m).measurableSet`. Establish `hT : MeasurableSet ((lmulM b⁻¹) ⁻¹' {a : Mt k r | nInv g a y ∈ K m})` using `hl b⁻¹ hS`. Establish `hcomp : (lmulM (k` using `k) (r := r) b) ⁻¹' ((lmulM b⁻¹) ⁻¹' {a : Mt k r | nInv g a y ∈ K m}) = {a | nInv g a y ∈ K m} := by`. Use extensionality with `a`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`.

Establish `e : lmulM (k` using `k) (r := r) b⁻¹ (lmulM b a) = a := by show b⁻¹ * (b * Matrix.of a) = Matrix.of a`. Rewrite using `[← Matrix.mul_assoc, Matrix.nonsing_inv_mul b hd, Matrix.one_mul]`. Rewrite using `[e]`. Use `show μR {a | nInv g a (stabAct g b y) ∈ K m} = μR {a | nInv g a y ∈ K m}`. Repeatedly rewrite using `[nInv_act hbU]`.

Use `conv_rhs => rw [← hcomp, ← Measure.map_apply (hl b) hT, hμ.2.2.2 b hb]`. Both sides reduce to the same expression.
-/
theorem Phi_inv (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR) (hK : ∀ m, IsClosed (K m))
    {b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hb : b ∈ RStab k r g) (m : ℕ) (y : PairSp k r) :
    Phi g μR K m (stabAct g b y) = Phi g μR K m y := by
  have hbU : b ∈ UH (Hpk k r) := hb.1.1
  have hd := isUnit_det_of_mem_UH' hbU
  have hof : Continuous (fun x : Mt k r => Matrix.of x) := continuous_id
  have hl : ∀ s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ,
      Measurable (lmulM (k := k) (r := r) s) := by
    intro s
    have hc : Continuous (lmulM (k := k) (r := r) s) := by
      unfold lmulM
      first
        | fun_prop
        | continuity
    exact hc.measurable
  have hmk : Measurable (fun a : Mt k r => (a, y)) := by
    first
      | exact measurable_prodMk_right
      | exact measurable_prod_mk_right
      | fun_prop
  have hS : MeasurableSet {a : Mt k r | nInv g a y ∈ K m} :=
    ((measurable_nInv g).comp hmk) (hK m).measurableSet
  have hT : MeasurableSet ((lmulM b⁻¹) ⁻¹' {a : Mt k r | nInv g a y ∈ K m}) := hl b⁻¹ hS
  have hcomp : (lmulM (k := k) (r := r) b) ⁻¹' ((lmulM b⁻¹) ⁻¹' {a : Mt k r | nInv g a y ∈ K m}) =
      {a | nInv g a y ∈ K m} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have e : lmulM (k := k) (r := r) b⁻¹ (lmulM b a) = a := by
      show b⁻¹ * (b * Matrix.of a) = Matrix.of a
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul b hd, Matrix.one_mul]
    rw [e]
  show μR {a | nInv g a (stabAct g b y) ∈ K m} = μR {a | nInv g a y ∈ K m}
  simp_rw [nInv_act hbU]
  conv_rhs => rw [← hcomp, ← Measure.map_apply (hl b) hT, hμ.2.2.2 b hb]
  rfl

/- English proof (translation)
Use `set n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of y.1.2`. Establish `hnU : n ∈ UH (Hpk k r)` using `hy.1`. Set `F : Mt k r → Mt k r` to `fun x => fun i j => (n * (Matrix.of x)⁻¹) i j`. Establish `hF : ContinuousOn F (K m ∩ NS k r)`. Introduce `x hx`.

Establish `hout : Continuous (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => (fun i j => (n * M) i j : Mt k r))` using `continuous_toMt (continuous_const.matrix_mul continuous_id)`. Conclude with `(hout.continuousAt.comp ((continuousAt_inv_of_uh hx.2.1).comp (continuous_ofM continuous_id).continuousAt)).continuousWithinAt`. Establish `hC : IsCompact (F '' (K m ∩ NS k r))` using `((hKc m).inter_right isClosed_NS).image_of_continuousOn hF`. Establish `hsub : {a | nInv g a y ∈ K m} ∩ RS k r g ⊆ F '' (K m ∩ NS k r)`. Introduce and unpack `a ⟨ha, haR⟩`.

Establish `haU : Matrix.of a ∈ UH (Hpk k r)` using `haR.1.1`. Use `⟨nInv g a y, ⟨ha, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show (Matrix.of a)⁻¹ * n ∈ Nset k r`. Conclude with `nset_mul (nset_inv haR.1) hy`. Establish `hu : IsUnit (Matrix.of a).det` using `isUnit_iff_ne_zero.2 (det_ne_of_uh haU)`.

Establish `hm : n * ((Matrix.of a)⁻¹ * n)⁻¹ = Matrix.of a`. Rewrite using `[Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, ← Matrix.mul_assoc, uh_mul_inv hnU, Matrix.one_mul]`. Use function extensionality and compare the values at `i j`. Conclude with `congrFun (congrFun hm i) j`. Establish `hc : μR (RS k r g)ᶜ = 0` using `hμ.2.2.1`.

Unfold `Phi`. Rewrite using `[← measure_inter_conull hc]`. Conclude with `lt_of_le_of_lt (measure_mono hsub) ((rhaar_props hg hμ).1 _ hC)`.
-/
theorem Phi_lt_top (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR) (hKc : ∀ m, IsCompact (K m))
    (m : ℕ) {y : PairSp k r} (hy : y.1.2 ∈ NS k r) : Phi g μR K m y < ⊤ := by
  set n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Matrix.of y.1.2
  have hnU : n ∈ UH (Hpk k r) := hy.1
  let F : Mt k r → Mt k r := fun x => fun i j => (n * (Matrix.of x)⁻¹) i j
  have hF : ContinuousOn F (K m ∩ NS k r) := by
    intro x hx
    have hout : Continuous (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => (fun i j => (n * M) i j : Mt k r)) :=
      continuous_toMt (continuous_const.matrix_mul continuous_id)
    exact (hout.continuousAt.comp ((continuousAt_inv_of_uh hx.2.1).comp
      (continuous_ofM continuous_id).continuousAt)).continuousWithinAt
  have hC : IsCompact (F '' (K m ∩ NS k r)) := ((hKc m).inter_right isClosed_NS).image_of_continuousOn hF
  have hsub : {a | nInv g a y ∈ K m} ∩ RS k r g ⊆ F '' (K m ∩ NS k r) := by
    rintro a ⟨ha, haR⟩
    have haU : Matrix.of a ∈ UH (Hpk k r) := haR.1.1
    refine ⟨nInv g a y, ⟨ha, ?_⟩, ?_⟩
    · show (Matrix.of a)⁻¹ * n ∈ Nset k r
      exact nset_mul (nset_inv haR.1) hy
    · have hu : IsUnit (Matrix.of a).det := isUnit_iff_ne_zero.2 (det_ne_of_uh haU)
      have hm : n * ((Matrix.of a)⁻¹ * n)⁻¹ = Matrix.of a := by
        rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, ← Matrix.mul_assoc, uh_mul_inv hnU,
          Matrix.one_mul]
      funext i j
      exact congrFun (congrFun hm i) j
  have hc : μR (RS k r g)ᶜ = 0 := hμ.2.2.1
  unfold Phi
  rw [← measure_inter_conull hc]
  exact lt_of_le_of_lt (measure_mono hsub) ((rhaar_props hg hμ).1 _ hC)

/- English proof (translation)
Set `G : Mt k r → Mt k r` to `fun a => fun i j => ((Matrix.of a)⁻¹ * Matrix.of y.1.2) i j`. Establish `hdet : Continuous (fun a : Mt k r => (Matrix.of a).det)` using `(continuous_ofM continuous_id).matrix_det`. Establish `hO : IsOpen {a : Mt k r | (Matrix.of a).det ≠ 0}` using `isOpen_ne_fun hdet continuous_const`. Establish `hG : ContinuousOn G {a : Mt k r | (Matrix.of a).det ≠ 0}`. Introduce `x hx`.

Establish `hout : Continuous (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => (fun i j => (M * Matrix.of y.1.2) i j : Mt k r))` using `continuous_toMt (continuous_id.matrix_mul continuous_const)`. Conclude with `(hout.continuousAt.comp ((continuousAt_inv_of_det hx).comp (continuous_ofM continuous_id).continuousAt)).continuousWithinAt`. Establish `hV` using `hG.isOpen_inter_preimage hO (isOpen_interior (s := K m))`. Establish `h1 : (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j : Mt k r) ∈ ({a : Mt k r | (Matrix.of a).det ≠ 0} ∩ G ⁻¹' interior (K m)) ∩ RS k r g`. Use `⟨⟨?_, ?_⟩, rstab_one hg⟩` and prove the remaining obligations.

Use `show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det ≠ 0`. Rewrite using `[Matrix.det_one]`. Conclude with `one_ne_zero`. Use `show (fun i j => ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ * Matrix.of y.1.2) i j) ∈ interior (K m)`. Rewrite using `[inv_one, Matrix.one_mul]`.

Conclude with `hy`. Establish `hpos` using `(rhaar_props hg hμ).2 _ hV ⟨_, h1⟩`. Introduce `h0`. Apply `hpos` to reduce the goal to its premises. Use `measure_mono_null ?_ h0` and prove the remaining obligations.

Introduce and unpack `a ⟨-, ha⟩`. Conclude with `interior_subset (s := K m) ha`.
-/
theorem Phi_ne_zero (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR)
    (m : ℕ) {y : PairSp k r} (hy : y.1.2 ∈ interior (K m)) : Phi g μR K m y ≠ 0 := by
  let G : Mt k r → Mt k r := fun a => fun i j => ((Matrix.of a)⁻¹ * Matrix.of y.1.2) i j
  have hdet : Continuous (fun a : Mt k r => (Matrix.of a).det) := (continuous_ofM continuous_id).matrix_det
  have hO : IsOpen {a : Mt k r | (Matrix.of a).det ≠ 0} := isOpen_ne_fun hdet continuous_const
  have hG : ContinuousOn G {a : Mt k r | (Matrix.of a).det ≠ 0} := by
    intro x hx
    have hout : Continuous (fun M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
        (fun i j => (M * Matrix.of y.1.2) i j : Mt k r)) :=
      continuous_toMt (continuous_id.matrix_mul continuous_const)
    exact (hout.continuousAt.comp ((continuousAt_inv_of_det hx).comp
      (continuous_ofM continuous_id).continuousAt)).continuousWithinAt
  have hV := hG.isOpen_inter_preimage hO (isOpen_interior (s := K m))
  have h1 : (fun i j => (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j : Mt k r) ∈
      ({a : Mt k r | (Matrix.of a).det ≠ 0} ∩ G ⁻¹' interior (K m)) ∩ RS k r g := by
    refine ⟨⟨?_, ?_⟩, rstab_one hg⟩
    · show (1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).det ≠ 0
      rw [Matrix.det_one]; exact one_ne_zero
    · show (fun i j => ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)⁻¹ * Matrix.of y.1.2) i j) ∈ interior (K m)
      rw [inv_one, Matrix.one_mul]; exact hy
  have hpos := (rhaar_props hg hμ).2 _ hV ⟨_, h1⟩
  intro h0
  apply hpos
  refine measure_mono_null ?_ h0
  rintro a ⟨-, ha⟩
  exact interior_subset (s := K m) ha

/- English proof (translation)
Take `⟨hm1, hm2⟩` from `hm`. Take `⟨hj1, hj2⟩` from `hj`. Break down `lt_trichotomy m j with h | h | h` into its components or cases. Conclude with `absurd (hj2 m h) hm1`. Conclude with `h`.

Conclude with `absurd (hm2 j h) hj1`.
-/
theorem Eset_unique {m j : ℕ} {y : PairSp k r} (hm : y ∈ Eset g μR K m) (hj : y ∈ Eset g μR K j) : m = j := by
  obtain ⟨hm1, hm2⟩ := hm
  obtain ⟨hj1, hj2⟩ := hj
  rcases lt_trichotomy m j with h | h | h
  · exact absurd (hj2 m h) hm1
  · exact h
  · exact absurd (hm2 j h) hj1

/- English proof (translation)
Conclude with `⟨Nat.find h, Nat.find_spec h, fun j hj => not_not.mp (Nat.find_min h hj)⟩`.
-/
theorem Eset_exists {y : PairSp k r} (h : ∃ m, Phi g μR K m y ≠ 0) : ∃ m, y ∈ Eset g μR K m := by
  classical
  exact ⟨Nat.find h, Nat.find_spec h, fun j hj => not_not.mp (Nat.find_min h hj)⟩

/- English proof (translation)
Establish `hinvR` using `rstab_inv hg ha`. Establish `hPhi : ∀ j, Phi g μR K j (stabAct g (Matrix.of a)⁻¹ y) = Phi g μR K j y` using `fun j => Phi_inv hg hμ hK hinvR j y`. Establish `hE : ∀ j, stabAct g (Matrix.of a)⁻¹ y ∈ Eset g μR K j ↔ y ∈ Eset g μR K j`. Introduce `j`. Use `show (Phi g μR K j (stabAct g (Matrix.of a)⁻¹ y) ≠ 0 ∧ ∀ i < j, Phi g μR K i (stabAct g (Matrix.of a)⁻¹ y) = 0) ↔ (Phi g μR K j y ≠ 0 ∧ ∀ i < j, Phi g μR K i y = 0)`.

Simplify using `only [hPhi]`. Unfold `theta`. Rewrite using `[tsum_eq_single m]`. Rewrite using `[indicator_of_mem ((hE m).2 hm)] show (K m).indicator 1 (stabAct g (Matrix.of a)⁻¹ y).1.2 * (Phi g μR K m (stabAct g (Matrix.of a)⁻¹ y))⁻¹ = _`. Rewrite using `[hPhi m]`.

Both sides reduce to the same expression. Introduce `j hj`. Use `indicator_of_notMem (fun h => hj ?_) _` and prove the remaining obligations. Conclude with `(Eset_unique hm ((hE j).1 h)).symm`.
-/
theorem theta_at (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR) (hK : ∀ m, IsClosed (K m))
    {m : ℕ} {y : PairSp k r} (hm : y ∈ Eset g μR K m) {a : Mt k r} (ha : Matrix.of a ∈ RStab k r g) :
    theta g μR K (stabAct g (Matrix.of a)⁻¹ y) = (K m).indicator 1 (nInv g a y) * (Phi g μR K m y)⁻¹ := by
  have hinvR := rstab_inv hg ha
  have hPhi : ∀ j, Phi g μR K j (stabAct g (Matrix.of a)⁻¹ y) = Phi g μR K j y :=
    fun j => Phi_inv hg hμ hK hinvR j y
  have hE : ∀ j, stabAct g (Matrix.of a)⁻¹ y ∈ Eset g μR K j ↔ y ∈ Eset g μR K j := by
    intro j
    show (Phi g μR K j (stabAct g (Matrix.of a)⁻¹ y) ≠ 0 ∧ ∀ i < j, Phi g μR K i (stabAct g (Matrix.of a)⁻¹ y) = 0) ↔
      (Phi g μR K j y ≠ 0 ∧ ∀ i < j, Phi g μR K i y = 0)
    simp only [hPhi]
  unfold theta
  rw [tsum_eq_single m]
  · rw [indicator_of_mem ((hE m).2 hm)]
    show (K m).indicator 1 (stabAct g (Matrix.of a)⁻¹ y).1.2 * (Phi g μR K m (stabAct g (Matrix.of a)⁻¹ y))⁻¹ = _
    rw [hPhi m]; rfl
  · intro j hj
    refine indicator_of_notMem (fun h => hj ?_) _
    exact (Eset_unique hm ((hE j).1 h)).symm

/- English proof (translation)
Establish `hm : Measurable (fun a : Mt k r => (a, y))` using `by first`. Consider the case `exact measurable_prodMk_right`. Consider the case `exact measurable_prod_mk_right`. Consider the case `fun_prop`. Establish `e : (fun a : Mt k r => nInv g a y) = (fun p : Mt k r × PairSp k r => nInv g p.1 p.2) ∘ (fun a => (a, y))` using `rfl`.

Rewrite using `[e]`. Conclude with `(measurable_nInv g).comp hm`.
-/
theorem measurable_nInv_left (y : PairSp k r) : Measurable (fun a : Mt k r => nInv g a y) := by
  have hm : Measurable (fun a : Mt k r => (a, y)) := by
    first
      | exact measurable_prodMk_right
      | exact measurable_prod_mk_right
      | fun_prop
  have e : (fun a : Mt k r => nInv g a y) = (fun p : Mt k r × PairSp k r => nInv g p.1 p.2) ∘ (fun a => (a, y)) := rfl
  rw [e]
  exact (measurable_nInv g).comp hm

/- English proof (translation)
Establish `hs : MeasurableSet ((fun a : Mt k r => nInv g a y) ⁻¹' K m)` using `measurable_nInv_left y (hK m).measurableSet`. Use `show _ = μR ((fun a : Mt k r => nInv g a y) ⁻¹' K m)`. Rewrite using `[← lintegral_indicator_one hs]`. Both sides reduce to the same expression.
-/
theorem lint_ind (y : PairSp k r) (hK : ∀ m, IsClosed (K m)) (m : ℕ) :
    ∫⁻ a, (K m).indicator (1 : Mt k r → ℝ≥0∞) (nInv g a y) ∂μR = Phi g μR K m y := by
  have hs : MeasurableSet ((fun a : Mt k r => nInv g a y) ⁻¹' K m) :=
    measurable_nInv_left y (hK m).measurableSet
  show _ = μR ((fun a : Mt k r => nInv g a y) ⁻¹' K m)
  rw [← lintegral_indicator_one hs]
  rfl

/- English proof (translation)
Establish `hae : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r g` using `ae_iff.mpr hμ.2.2.1`. Apply `lintegral_congr_ae` to reduce the goal to its premises. Use `filter_upwards [hae] with a ha`. Conclude with `theta_at hg hμ hK hm ha`.
-/
theorem theta_norm_A (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR) (hK : ∀ m, IsClosed (K m))
    {m : ℕ} {y : PairSp k r} (hm : y ∈ Eset g μR K m) :
    ∫⁻ a, theta g μR K (stabAct g (Matrix.of a)⁻¹ y) ∂μR =
      ∫⁻ a, (K m).indicator 1 (nInv g a y) * (Phi g μR K m y)⁻¹ ∂μR := by
  have hae : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r g := ae_iff.mpr hμ.2.2.1
  apply lintegral_congr_ae
  filter_upwards [hae] with a ha
  exact theta_at hg hμ hK hm ha

/- English proof (translation)
Establish `hK : ∀ m, IsClosed (K m)` using `fun m => (hKc m).isClosed`. Take `⟨m0, hm0⟩` from `hKi y.1.2`. Take `⟨m, hm⟩` from `Eset_exists ⟨m0, Phi_ne_zero hg hμ m0 hm0⟩`. Rewrite using `[theta_norm_A hg hμ hK hm, lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hm.1), lint_ind y hK m]`. Conclude with `ENNReal.mul_inv_cancel hm.1 (Phi_lt_top hg hμ hKc m hy).ne`.
-/
theorem theta_norm (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR) (hKc : ∀ m, IsCompact (K m))
    (hKi : ∀ x, ∃ m, x ∈ interior (K m)) {y : PairSp k r} (hy : y.1.2 ∈ NS k r) :
    ∫⁻ a, theta g μR K (stabAct g (Matrix.of a)⁻¹ y) ∂μR = 1 := by
  have hK : ∀ m, IsClosed (K m) := fun m => (hKc m).isClosed
  obtain ⟨m0, hm0⟩ := hKi y.1.2
  obtain ⟨m, hm⟩ := Eset_exists ⟨m0, Phi_ne_zero hg hμ m0 hm0⟩
  rw [theta_norm_A hg hμ hK hm, lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hm.1), lint_ind y hK m]
  exact ENNReal.mul_inv_cancel hm.1 (Phi_lt_top hg hμ hKc m hy).ne

end Cut

/- English proof (translation)
Use `haveI : SigmaFinite μR := hμ.1`. Take `⟨K, hKc, hKi⟩` from `exists_cover' (k := k) (r := r)`. Conclude with `⟨theta g μR K, measurable_theta g μR K (fun m => (hKc m).isClosed), fun y hy => theta_norm hg hμ hKc hKi hy⟩`.
-/
theorem cutoff_exists {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μR : Measure (Mt k r)}
    (hg : g ∈ UH (Hpk k r)) (hμ : IsHaarOn (RStab k r g) μR) :
    ∃ θ : PairSp k r → ℝ≥0∞, Measurable θ ∧
      ∀ y : PairSp k r, y.1.2 ∈ NS k r → ∫⁻ a, θ (stabAct g (Matrix.of a)⁻¹ y) ∂μR = 1 := by
  haveI : SigmaFinite μR := hμ.1
  obtain ⟨K, hKc, hKi⟩ := exists_cover' (k := k) (r := r)
  exact ⟨theta g μR K, measurable_theta g μR K (fun m => (hKc m).isClosed),
    fun y hy => theta_norm hg hμ hKc hKi hy⟩

end PI.AmpOrbQuot
