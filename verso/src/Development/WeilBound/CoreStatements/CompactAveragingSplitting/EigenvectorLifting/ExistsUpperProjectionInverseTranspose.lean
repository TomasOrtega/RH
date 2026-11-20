import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.SplitDict
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyDeepSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyConstantExtensionByZero

open MeasureTheory ValuativeRel Matrix Topology Filter
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace PositivityTheory.ThK.SplitLoc

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.GLDoubling
open GlobalTheory.IwahoriInj (Deep)

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
attribute [local instance 10000] GlobalTheory.SplitWeil.matrixMeasurableSpace

section Group
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Rewrite using `[← integral_indicator hS, ← integral_indicator hS, ← integral_mul_left_eq_self (S.indicator F) w]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Distinguish the cases in `h : g ∈ S`. Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem ((hw g).2 h)]`.

Rewrite using `[Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hw g).1 h'))]`.
-/
theorem setIntegral_left (μ : Measure G) [μ.IsMulLeftInvariant] {S : Set G} (hS : MeasurableSet S) (w : G)
    (hw : ∀ g, w * g ∈ S ↔ g ∈ S) (F : G → ℂ) : ∫ g in S, F (w * g) ∂μ = ∫ g in S, F g ∂μ := by
  rw [← integral_indicator hS, ← integral_indicator hS, ← integral_mul_left_eq_self (S.indicator F) w]
  congr 1
  funext g
  by_cases h : g ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hw g).2 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hw g).1 h'))]

/- English proof (translation)
Rewrite using `[← integral_indicator hS, ← integral_indicator hS, ← integral_mul_right_eq_self (S.indicator F) w]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Distinguish the cases in `h : g ∈ S`. Rewrite using `[Set.indicator_of_mem h, Set.indicator_of_mem ((hw g).2 h)]`.

Rewrite using `[Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hw g).1 h'))]`.
-/
theorem setIntegral_right (μ : Measure G) [μ.IsMulRightInvariant] {S : Set G} (hS : MeasurableSet S) (w : G)
    (hw : ∀ g, g * w ∈ S ↔ g ∈ S) (F : G → ℂ) : ∫ g in S, F (g * w) ∂μ = ∫ g in S, F g ∂μ := by
  rw [← integral_indicator hS, ← integral_indicator hS, ← integral_mul_right_eq_self (S.indicator F) w]
  congr 1
  funext g
  by_cases h : g ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hw g).2 h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hw g).1 h'))]

omit [Group G] [IsTopologicalGroup G] in
/- English proof (translation)
Establish `hI : Integrable (Function.uncurry F) ((μ.restrict K).prod (μ.restrict S))`. Rewrite using `[Measure.prod_restrict]`. Conclude with `hF.continuousOn.integrableOn_compact (hK.prod hS)`. Rewrite using `[← integral_integral_swap hI, setIntegral_congr_fun hK.measurableSet (g := fun _ => I) hinv]`. Simplify using the standard rewrite rules.
-/
theorem avg_setIntegral [SecondCountableTopology G] [T2Space G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [SFinite μ]
    {K S : Set G} (hK : IsCompact K) (hS : IsCompact S) (F : G → G → ℂ) (hF : Continuous (Function.uncurry F)) (I : ℂ)
    (hinv : ∀ x ∈ K, ∫ g in S, F x g ∂μ = I) : (μ.real K : ℂ) * I = ∫ g in S, ∫ x in K, F x g ∂μ ∂μ := by
  have hI : Integrable (Function.uncurry F) ((μ.restrict K).prod (μ.restrict S)) := by
    rw [Measure.prod_restrict]
    exact hF.continuousOn.integrableOn_compact (hK.prod hS)
  rw [← integral_integral_swap hI, setIntegral_congr_fun hK.measurableSet (g := fun _ => I) hinv]
  simp

end Group

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Integrand
variable {n : Type} [Fintype n] [DecidableEq n]

def zint (ν : kˣ →* ℂˣ) (z : ℂ) (φ : Matrix n n k → ℂ) (g : GL n k) : ℂ :=
  φ g.val * (ν (gdet g) : ℂ) * apow (gdet g) z

/- English proof (translation)
Use `(IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_` and prove the remaining obligations. Establish `hn : (fun g => g0⁻¹ * g) ⁻¹' (detCong (ϖ ^ e) n : Set (GL n k)) ∈ 𝓝 g0` using `((isOpen_detCong _ n).preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)`. Use `filter_upwards [hn] with g hg`. Establish `h1 : ν (gdet (g0⁻¹ * g)) = 1` using `hν _ hg.2`. Establish `h2 : g = g0 * (g0⁻¹ * g)` using `by simp`.

Rewrite using `[h2, gdet_mul, map_mul, h1, mul_one]`.
-/
theorem lc_char {ϖ : kˣ} {e : ℕ} {ν : kˣ →* ℂˣ} (hν : CondLE ϖ e ν) :
    IsLocallyConstant fun g : GL n k => (ν (gdet g) : ℂ) := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
  have hn : (fun g => g0⁻¹ * g) ⁻¹' (detCong (ϖ ^ e) n : Set (GL n k)) ∈ 𝓝 g0 :=
    ((isOpen_detCong _ n).preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [hn] with g hg
  have h1 : ν (gdet (g0⁻¹ * g)) = 1 := hν _ hg.2
  have h2 : g = g0 * (g0⁻¹ * g) := by simp
  rw [h2, gdet_mul, map_mul, h1, mul_one]

/- English proof (translation)
The claim follows from `((isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp fun t : ℝ => (t : ℂ) ^ z`.
-/
theorem lc_apow (z : ℂ) : IsLocallyConstant fun g : GL n k => apow (gdet g) z :=
  ((isLocallyConstant_nabs k).comp_continuous GeneralLinearGroup.continuous_det).comp fun t : ℝ => (t : ℂ) ^ z

/- English proof (translation)
The claim follows from `(((hφ.1.comp_continuous Units.continuous_val).mul (lc_char hν)).mul (lc_apow z)).continuous`.
-/
theorem continuous_zint {ϖ : kˣ} {e : ℕ} {ν : kˣ →* ℂˣ} (hν : CondLE ϖ e ν) (z : ℂ) {φ : Matrix n n k → ℂ}
    (hφ : φ ∈ SB (Matrix n n k)) : Continuous (zint ν z φ) :=
  (((hφ.1.comp_continuous Units.continuous_val).mul (lc_char hν)).mul (lc_apow z)).continuous

/- English proof (translation)
Simplify using `only [zint, Units.val_mul, map_mul, apow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zint_right (ν : kˣ →* ℂˣ) (z : ℂ) (φ : Matrix n n k → ℂ) (g₀ g : GL n k) :
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) z * zint ν z (fun X => φ (X * g₀.val)) g = zint ν z φ (g * g₀) := by
  simp only [zint, Units.val_mul, map_mul, apow_mul]
  ring

/- English proof (translation)
Simplify using `only [zint, Units.val_mul, map_mul, apow_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zint_left (ν : kˣ →* ℂˣ) (z : ℂ) (φ : Matrix n n k → ℂ) (g₀ g : GL n k) :
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) z * zint ν z (fun X => φ (g₀.val * X)) g = zint ν z φ (g₀ * g) := by
  simp only [zint, Units.val_mul, map_mul, apow_mul]
  ring

/- English proof (translation)
Rewrite `hx`, `hy` using `[mem_KO_iff]`. Simplify using `only [Matrix.mul_apply]`. Use `Deep.sum fun l _ => ?_` and prove the remaining obligations. Establish `h1 : Deep m (∑ p, x.val i p * Z p l)` using `Deep.sum fun p _ => by`. Simplify using `using (GlobalTheory.IwahoriInj.deep_zero_iff.2 (hx.1 i p)).mul (hZ p l)`.

Simplify using `using h1.mul (GlobalTheory.IwahoriInj.deep_zero_iff.2 (hy.1 l j))`.
-/
theorem deep_mul_mul {m : ℤ} {x y : GL n k} (hx : x ∈ KO k n) (hy : y ∈ KO k n) {Z : Matrix n n k}
    (hZ : ∀ i j, Deep m (Z i j)) (i j : n) : Deep m ((x.val * Z * y.val) i j) := by
  rw [mem_KO_iff] at hx hy
  simp only [Matrix.mul_apply]
  refine Deep.sum fun l _ => ?_
  have h1 : Deep m (∑ p, x.val i p * Z p l) := Deep.sum fun p _ => by
    simpa using (GlobalTheory.IwahoriInj.deep_zero_iff.2 (hx.1 i p)).mul (hZ p l)
  simpa using h1.mul (GlobalTheory.IwahoriInj.deep_zero_iff.2 (hy.1 l j))

/- English proof (translation)
Unfold `Deep`. Rewrite using `[map_zpow₀, hϖ]`. Conclude with `zpow_le_zpow_iff_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one`.
-/
theorem deep_zpow {ϖ : kˣ} (hϖ : IsUnif ϖ) (a b : ℤ) : Deep a ((ϖ : k) ^ b) ↔ a ≤ b := by
  unfold Deep
  rw [map_zpow₀, hϖ]
  exact zpow_le_zpow_iff_right_of_lt_one₀ uniformizer_pos uniformizer_lt_one

/- English proof (translation)
Establish `h : ∀ j, valuation k ((Pi.mulSingle i u : n → kˣ) j : k) = 1` using `fun j => by`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `using hu`. Simplify using `[Pi.mulSingle_eq_of_ne hj]`.

Rewrite using `[mem_KO_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `a b`. Rewrite using `[diagGL_val, diagonal_apply]`. Use `split_ifs`.

Conclude with `(h a).le`. Conclude with `zero_mem _`. Introduce `a b show (diagonal fun j => ((((Pi.mulSingle i u : n → kˣ) j)⁻¹ : kˣ) : k)) a b ∈ _`. Rewrite using `[diagonal_apply]`. Use `split_ifs`.

Rewrite using `[Valuation.mem_integer_iff]`. Simplify using `[h a]`. Conclude with `zero_mem _`.
-/
theorem diagGL_single_mem {u : kˣ} (hu : valuation k (u : k) = 1) (i : n) :
    diagGL (Pi.mulSingle i u : n → kˣ) ∈ KO k n := by
  have h : ∀ j, valuation k ((Pi.mulSingle i u : n → kˣ) j : k) = 1 := fun j => by
    by_cases hj : j = i
    · subst hj; simpa using hu
    · simp [Pi.mulSingle_eq_of_ne hj]
  rw [mem_KO_iff]
  constructor
  · intro a b
    rw [diagGL_val, diagonal_apply]
    split_ifs
    · exact (h a).le
    · exact zero_mem _
  · intro a b
    show (diagonal fun j => ((((Pi.mulSingle i u : n → kˣ) j)⁻¹ : kˣ) : k)) a b ∈ _
    rw [diagonal_apply]
    split_ifs
    · rw [Valuation.mem_integer_iff]; simp [h a]
    · exact zero_mem _

/- English proof (translation)
Establish `hd : gdet (diagGL (Pi.mulSingle i u : n → kˣ)) = u`. Rewrite using `[gdet, det_diagGL, Finset.prod_pi_mulSingle']`. Simplify using the standard rewrite rules. Establish `h1 : (x * diagGL (Pi.mulSingle i u : n → kˣ) * torusElt k n ϖ m * y).val = (x * torusElt k n ϖ m * y).val + x.val * (diagonal fun j => (((Pi.mulSingle i u : n → kˣ) j : k) - 1) * (ϖ : k) ^ m j) * y.val`. Simplify using `only [Units.val_mul, diagGL_val, val_torusElt, Matrix.mul_assoc x.val, diagonal_mul_diagonal, ← Matrix.mul_add, ← Matrix.add_mul, diagonal_add]`.

Use `congr 3`. Use function extensionality and compare the values at `j`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : φ (x * diagGL (Pi.mulSingle i u : n → kˣ) * torusElt k n ϖ m * y).val = φ (x * torusElt k n ϖ m * y).val`. Rewrite using `[h1]`.

Use `hM _ _ (deep_mul_mul hx hy fun a b => ?_)` and prove the remaining obligations. Rewrite using `[diagonal_apply]`. Use `split_ifs`. Distinguish the cases in `ha : a = i`. Substitute `ha` using the available equality.

Establish `: Deep 0 ((u : k) - 1)` using `GlobalTheory.IwahoriInj.deep_zero_iff.2 (Valuation.map_sub_le _ hu.le (by simp))`. Simplify using `using this.mul ((deep_zpow hϖ M _).2 hi)`. Simplify `GlobalTheory.IwahoriInj.deep_zero M` using `[Pi.mulSingle_eq_of_ne ha]`. Conclude with `GlobalTheory.IwahoriInj.deep_zero M`. Unfold `zint`.

Rewrite using `[h2]`. Simplify using `only [hd, map_mul, apow_mul, apow_of_valuation_eq_one hu, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zint_unit {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν : kˣ →* ℂˣ) (z : ℂ) {φ : Matrix n n k → ℂ} {M : ℤ}
    (hM : ∀ x y : Matrix n n k, (∀ i j, Deep M (y i j)) → φ (x + y) = φ x) {u : kˣ} (hu : valuation k (u : k) = 1)
    {m : n → ℤ} {i : n} (hi : M ≤ m i) {x y : GL n k} (hx : x ∈ KO k n) (hy : y ∈ KO k n) :
    zint ν z φ (x * diagGL (Pi.mulSingle i u : n → kˣ) * torusElt k n ϖ m * y) =
      ν u * zint ν z φ (x * torusElt k n ϖ m * y) := by
  have hd : gdet (diagGL (Pi.mulSingle i u : n → kˣ)) = u := by
    rw [gdet, det_diagGL, Finset.prod_pi_mulSingle']; simp
  have h1 : (x * diagGL (Pi.mulSingle i u : n → kˣ) * torusElt k n ϖ m * y).val = (x * torusElt k n ϖ m * y).val +
      x.val * (diagonal fun j => (((Pi.mulSingle i u : n → kˣ) j : k) - 1) * (ϖ : k) ^ m j) * y.val := by
    simp only [Units.val_mul, diagGL_val, val_torusElt, Matrix.mul_assoc x.val, diagonal_mul_diagonal,
      ← Matrix.mul_add, ← Matrix.add_mul, diagonal_add]
    congr 3
    funext j
    ring
  have h2 : φ (x * diagGL (Pi.mulSingle i u : n → kˣ) * torusElt k n ϖ m * y).val = φ (x * torusElt k n ϖ m * y).val := by
    rw [h1]
    refine hM _ _ (deep_mul_mul hx hy fun a b => ?_)
    rw [diagonal_apply]
    split_ifs
    · by_cases ha : a = i
      · subst ha
        have : Deep 0 ((u : k) - 1) := GlobalTheory.IwahoriInj.deep_zero_iff.2
          (Valuation.map_sub_le _ hu.le (by simp))
        simpa using this.mul ((deep_zpow hϖ M _).2 hi)
      · simpa [Pi.mulSingle_eq_of_ne ha] using GlobalTheory.IwahoriInj.deep_zero M
    · exact GlobalTheory.IwahoriInj.deep_zero M
  unfold zint
  rw [h2]
  simp only [hd, map_mul, apow_mul, apow_of_valuation_eq_one hu, Units.val_mul]
  ring

/- English proof (translation)
Establish `: φ (x * torusElt k n ϖ m * y).val = 0`. Assume the negation of the conclusion as `h`. Establish `h1` using `deep_mul_mul (inv_mem hx) (inv_mem hy) (hN _ h) i i`. Rewrite `h1` using `[← Units.val_mul, ← Units.val_mul, show x⁻¹ * (x * torusElt k n ϖ m * y) * y⁻¹ = torusElt k n ϖ m by group, val_torusElt, diagonal_apply_eq, deep_zpow hϖ]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[zint, this, zero_mul, zero_mul]`.
-/
theorem zint_low {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν : kˣ →* ℂˣ) (z : ℂ) {φ : Matrix n n k → ℂ} {N : ℤ}
    (hN : ∀ x, φ x ≠ 0 → ∀ i j, Deep N (x i j)) {m : n → ℤ} {i : n} (hi : m i < N) {x y : GL n k}
    (hx : x ∈ KO k n) (hy : y ∈ KO k n) : zint ν z φ (x * torusElt k n ϖ m * y) = 0 := by
  have : φ (x * torusElt k n ϖ m * y).val = 0 := by
    by_contra h
    have h1 := deep_mul_mul (inv_mem hx) (inv_mem hy) (hN _ h) i i
    rw [← Units.val_mul, ← Units.val_mul, show x⁻¹ * (x * torusElt k n ϖ m * y) * y⁻¹ = torusElt k n ϖ m by group,
      val_torusElt, diagonal_apply_eq, deep_zpow hϖ] at h1
    omega
  rw [zint, this, zero_mul, zero_mul]

end Integrand

section Shells
variable [MeasurableSpace k] [BorelSpace k] {a : ℕ}

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Unfold `shellSet cell`. Use `congr 1`. Conclude with `Units.ext (by simp [val_torusElt])`.
-/
theorem shellSet_eq_cell (ϖ : kˣ) (m : Fin a → ℤ) : shellSet ϖ m = cell k (Fin a) ϖ m := by
  unfold shellSet cell
  congr 1
  exact Units.ext (by simp [val_torusElt])

omit [BorelSpace k] in
/- English proof (translation)
Simplify using `only [shellSum, shell, shellSet_eq_cell, zint]`.
-/
theorem shellSum_eq (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (ν : kˣ →* ℂˣ) (z : ℂ) (φ : Matrix (Fin a) (Fin a) k → ℂ) :
    shellSum μ ϖ ν z φ = ∑ᶠ m : {m : Fin a → ℤ // Antitone m}, ∫ g in cell k (Fin a) ϖ m.1, zint ν z φ g ∂μ := by
  simp only [shellSum, shell, shellSet_eq_cell, zint]

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Establish `h1 : ∀ x ∈ KO k (Fin a), ∀ g ∈ cell k (Fin a) ϖ m, x * g ∈ cell k (Fin a) ϖ m ∧ g * x ∈ cell k (Fin a) ϖ m`. Introduce `x hx g hg`. Take `⟨p, hp, q, hq, rfl⟩` from `DoubleCoset.mem_doubleCoset.1 hg`. Conclude with `⟨DoubleCoset.mem_doubleCoset.2 ⟨x * p, mul_mem hx hp, q, hq, by group⟩, DoubleCoset.mem_doubleCoset.2 ⟨p, hp, q * x, mul_mem hq hx, by group⟩⟩`. Conclude with `⟨⟨fun h => by simpa using (h1 _ (inv_mem hx) _ h).1, fun h => (h1 _ hx _ h).1⟩, ⟨fun h => by simpa using (h1 _ (inv_mem hx) _ h).2, fun h => (h1 _ hx _ h).2⟩⟩`.
-/
theorem cell_inv (ϖ : kˣ) (m : Fin a → ℤ) {x : GL (Fin a) k} (hx : x ∈ KO k (Fin a)) (g : GL (Fin a) k) :
    (x * g ∈ cell k (Fin a) ϖ m ↔ g ∈ cell k (Fin a) ϖ m) ∧ (g * x ∈ cell k (Fin a) ϖ m ↔ g ∈ cell k (Fin a) ϖ m) := by
  have h1 : ∀ x ∈ KO k (Fin a), ∀ g ∈ cell k (Fin a) ϖ m, x * g ∈ cell k (Fin a) ϖ m ∧ g * x ∈ cell k (Fin a) ϖ m := by
    intro x hx g hg
    obtain ⟨p, hp, q, hq, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
    exact ⟨DoubleCoset.mem_doubleCoset.2 ⟨x * p, mul_mem hx hp, q, hq, by group⟩,
      DoubleCoset.mem_doubleCoset.2 ⟨p, hp, q * x, mul_mem hq hx, by group⟩⟩
  exact ⟨⟨fun h => by simpa using (h1 _ (inv_mem hx) _ h).1, fun h => (h1 _ hx _ h).1⟩,
    ⟨fun h => by simpa using (h1 _ (inv_mem hx) _ h).2, fun h => (h1 _ hx _ h).2⟩⟩

/- English proof (translation)
Take `⟨T, hT⟩` from `hC.elim_finite_subcover (fun m : {m : Fin a → ℤ // Antitone m} => cell k (Fin a) ϖ m.1) (fun m => isOpen_cell ϖ m.1) (by rw [iUnion_cell hϖ]; exact Set.subset_univ _)`. Establish `hdisj` using `pairwise_disjoint_cell (N := a) hϖ`. Establish `hsupp : (Function.support fun m : {m : Fin a → ℤ // Antitone m} => ∫ g in cell k (Fin a) ϖ m.1, f g ∂μ) ⊆ T`. Introduce `m hm`. Assume the negation of the conclusion as `hmT`.

Use `hm (mul_left_cancel₀ hc ?_)` and prove the remaining obligations. Rewrite using `[hS _ (isCompact_cell ϖ m.1) fun x hx g => cell_inv ϖ m.1 hx g, mul_zero]`. Use `setIntegral_eq_zero_of_forall_eq_zero fun g hg => h0 g fun hgC => ?_` and prove the remaining obligations. Take `⟨m', hm', hg'⟩` from `Set.mem_iUnion₂.1 (hT hgC)`. Conclude with `Set.disjoint_left.1 (hdisj (show m ≠ m' from fun e => hmT (e ▸ hm'))) hg hg'`.

Use `⟨T.finite_toSet.subset hsupp, ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_support_subset _ hsupp, ← integral_biUnion_finset T (fun m _ => (isOpen_cell ϖ m.1).measurableSet) (fun m _ m' _ hne => hdisj hne) (fun m _ => hf.continuousOn.integrableOn_compact (isCompact_cell ϖ m.1)), hS _ (T.isCompact_biUnion fun m _ => isCompact_cell ϖ m.1 …`. Conclude with `setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => h0 g fun hgC => hg (hT hgC)`. Introduce `x hx g`. Simplify using `only [Set.mem_iUnion, (cell_inv ϖ _ hx g).1, (cell_inv ϖ _ hx g).2, and_self]`.
-/
theorem finsum_cells (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] {ϖ : kˣ} (hϖ : IsUnif ϖ) {f h : GL (Fin a) k → ℂ}
    (hf : Continuous f) {C : Set (GL (Fin a) k)} (hC : IsCompact C) (h0 : ∀ g, g ∉ C → h g = 0) {c : ℂ} (hc : c ≠ 0)
    (hS : ∀ S : Set (GL (Fin a) k), IsCompact S →
      (∀ x ∈ KO k (Fin a), ∀ g, (x * g ∈ S ↔ g ∈ S) ∧ (g * x ∈ S ↔ g ∈ S)) → c * ∫ g in S, f g ∂μ = ∫ g in S, h g ∂μ) :
    (Function.support fun m : {m : Fin a → ℤ // Antitone m} => ∫ g in cell k (Fin a) ϖ m.1, f g ∂μ).Finite ∧
      c * ∑ᶠ m : {m : Fin a → ℤ // Antitone m}, ∫ g in cell k (Fin a) ϖ m.1, f g ∂μ = ∫ g, h g ∂μ := by
  obtain ⟨T, hT⟩ := hC.elim_finite_subcover (fun m : {m : Fin a → ℤ // Antitone m} => cell k (Fin a) ϖ m.1)
    (fun m => isOpen_cell ϖ m.1) (by rw [iUnion_cell hϖ]; exact Set.subset_univ _)
  have hdisj := pairwise_disjoint_cell (N := a) hϖ
  have hsupp : (Function.support fun m : {m : Fin a → ℤ // Antitone m} => ∫ g in cell k (Fin a) ϖ m.1, f g ∂μ) ⊆ T := by
    intro m hm
    by_contra hmT
    refine hm (mul_left_cancel₀ hc ?_)
    rw [hS _ (isCompact_cell ϖ m.1) fun x hx g => cell_inv ϖ m.1 hx g, mul_zero]
    refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => h0 g fun hgC => ?_
    obtain ⟨m', hm', hg'⟩ := Set.mem_iUnion₂.1 (hT hgC)
    exact Set.disjoint_left.1 (hdisj (show m ≠ m' from fun e => hmT (e ▸ hm'))) hg hg'
  refine ⟨T.finite_toSet.subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, ← integral_biUnion_finset T (fun m _ => (isOpen_cell ϖ m.1).measurableSet)
    (fun m _ m' _ hne => hdisj hne) (fun m _ => hf.continuousOn.integrableOn_compact (isCompact_cell ϖ m.1)),
    hS _ (T.isCompact_biUnion fun m _ => isCompact_cell ϖ m.1)]
  · exact setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => h0 g fun hgC => hg (hT hgC)
  · intro x hx g
    simp only [Set.mem_iUnion, (cell_inv ϖ _ hx g).1, (cell_inv ϖ _ hx g).2, and_self]

/- English proof (translation)
Take `⟨N, M, hN, hM⟩` from `GlobalTheory.SBUniform.exists_bound_period k (Fin a) φ hφ`. Choose the witnesses or unpack the hypotheses as in `⟨u, hu, hνu⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by`. Assume the negation of the conclusion as `h`. Conclude with `hν fun x hx => by_contra fun h' => h ⟨x, hx, h'⟩`. Establish `hνu' : (ν u : ℂ) ≠ 1` using `fun h => hνu (Units.ext h)`.

Establish `hK : MeasurableSet (KO k (Fin a) : Set (GL (Fin a) k))` using `isOpen_KO.measurableSet`. Use `⟨⋃ m ∈ Set.Icc (fun _ : Fin a => -(N : ℤ)) (fun _ => (M : ℤ)), cell k (Fin a) ϖ m, (Set.finite_Icc _ _).isCompact_biUnion fun m _ => isCompact_cell ϖ m, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨⟨m, hma⟩, hm⟩` from `Set.mem_iUnion.1 ((iUnion_cell (N := a) hϖ).ge (Set.mem_univ g))`. Use `replace hm : g ∈ cell k (Fin a) ϖ m := hm`. Establish `hm' : ¬ ((fun _ : Fin a => -(N : ℤ)) ≤ m ∧ m ≤ fun _ => (M : ℤ))` using `fun h => hg (Set.mem_biUnion h hm)`.

Take `⟨x, hx, y, hy, rfl⟩` from `DoubleCoset.mem_doubleCoset.1 hm`. Simplify using `only [Pi.le_def, not_and_or, not_forall, not_le] at hm'`. Break down `hm' with ⟨i, hi⟩ | ⟨i, hi⟩` into its components or cases. Prove the components needed by the constructor for the conclusion. Use `setIntegral_eq_zero_of_forall_eq_zero fun w hw => ?_` and prove the remaining obligations.

Rewrite using `[show w * (x * torusElt k (Fin a) ϖ m * y) = w * x * torusElt k (Fin a) ϖ m * y by group]`. Conclude with `zint_low hϖ ν z hN hi (mul_mem hw hx) hy`. Use `setIntegral_eq_zero_of_forall_eq_zero fun w hw => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `zint_low hϖ ν z hN hi hx (mul_mem hy hw)`.

Use `set d := diagGL (Pi.mulSingle i u : Fin a → kˣ) with hd`. Establish `hdK : d ∈ KO k (Fin a)` using `diagGL_single_mem hu i`. Establish `key : ∀ I : ℂ, I = ν u * I → I = 0` using `fun I hI => by`. Assume the negation of the conclusion as `h`. Conclude with `hνu' (mul_right_cancel₀ h (by rw [one_mul]; exact hI.symm))`.

Prove the components needed by the constructor for the conclusion. Use `key _ ?_` and prove the remaining obligations. Establish `hw : x * d * x⁻¹ ∈ KO k (Fin a)` using `mul_mem (mul_mem hx hdK) (inv_mem hx)`. Use `conv_lhs => rw [← setIntegral_right μ hK (x * d * x⁻¹) (fun g => Subgroup.mul_mem_cancel_right _ hw)]`. Rewrite using `[← integral_const_mul]`.

Use `setIntegral_congr_fun hK fun w hw => ?_` and prove the remaining obligations. Rewrite using `[show w * (x * d * x⁻¹) * (x * torusElt k (Fin a) ϖ m * y) = w * x * d * torusElt k (Fin a) ϖ m * y by group, zint_unit hϖ ν z hM hu hi.le (mul_mem hw hx) hy]`. Use `congr 2`. Use `group`. Use `key _ ?_` and prove the remaining obligations.

Establish `hw : y⁻¹ * d * y ∈ KO k (Fin a)` using `mul_mem (mul_mem (inv_mem hy) hdK) hy`. Establish `hc : torusElt k (Fin a) ϖ m * d = d * torusElt k (Fin a) ϖ m` using `Units.ext (by simp [hd, val_torusElt, diagonal_mul_diagonal, mul_comm])`. Use `conv_lhs => rw [← setIntegral_left μ hK (y⁻¹ * d * y) (fun g => Subgroup.mul_mem_cancel_left _ hw)]`. Rewrite using `[← integral_const_mul]`. Use `setIntegral_congr_fun hK fun w hw => ?_` and prove the remaining obligations.

Rewrite using `[show x * torusElt k (Fin a) ϖ m * y * (y⁻¹ * d * y * w) = x * (torusElt k (Fin a) ϖ m * d) * (y * w) by group, hc, ← mul_assoc x, zint_unit hϖ ν z hM hu hi.le hx (mul_mem hy hw)]`. Use `congr 2`. Use `group`.
-/
theorem exists_compact_avg (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ}
    (hν : ¬ IsUnram ν) (z : ℂ) {φ : Matrix (Fin a) (Fin a) k → ℂ} (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) :
    ∃ C : Set (GL (Fin a) k), IsCompact C ∧ ∀ g, g ∉ C →
      ∫ x in KO k (Fin a), zint ν z φ (x * g) ∂μ = 0 ∧ ∫ x in KO k (Fin a), zint ν z φ (g * x) ∂μ = 0 := by
  obtain ⟨N, M, hN, hM⟩ := GlobalTheory.SBUniform.exists_bound_period k (Fin a) φ hφ
  obtain ⟨u, hu, hνu⟩ : ∃ u : kˣ, valuation k (u : k) = 1 ∧ ν u ≠ 1 := by
    by_contra h
    exact hν fun x hx => by_contra fun h' => h ⟨x, hx, h'⟩
  have hνu' : (ν u : ℂ) ≠ 1 := fun h => hνu (Units.ext h)
  have hK : MeasurableSet (KO k (Fin a) : Set (GL (Fin a) k)) := isOpen_KO.measurableSet
  refine ⟨⋃ m ∈ Set.Icc (fun _ : Fin a => -(N : ℤ)) (fun _ => (M : ℤ)), cell k (Fin a) ϖ m,
    (Set.finite_Icc _ _).isCompact_biUnion fun m _ => isCompact_cell ϖ m, fun g hg => ?_⟩
  obtain ⟨⟨m, hma⟩, hm⟩ := Set.mem_iUnion.1 ((iUnion_cell (N := a) hϖ).ge (Set.mem_univ g))
  replace hm : g ∈ cell k (Fin a) ϖ m := hm
  have hm' : ¬ ((fun _ : Fin a => -(N : ℤ)) ≤ m ∧ m ≤ fun _ => (M : ℤ)) := fun h => hg (Set.mem_biUnion h hm)
  obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hm
  simp only [Pi.le_def, not_and_or, not_forall, not_le] at hm'
  rcases hm' with ⟨i, hi⟩ | ⟨i, hi⟩
  · constructor
    · refine setIntegral_eq_zero_of_forall_eq_zero fun w hw => ?_
      rw [show w * (x * torusElt k (Fin a) ϖ m * y) = w * x * torusElt k (Fin a) ϖ m * y by group]
      exact zint_low hϖ ν z hN hi (mul_mem hw hx) hy
    · refine setIntegral_eq_zero_of_forall_eq_zero fun w hw => ?_
      rw [mul_assoc]
      exact zint_low hϖ ν z hN hi hx (mul_mem hy hw)
  · set d := diagGL (Pi.mulSingle i u : Fin a → kˣ) with hd
    have hdK : d ∈ KO k (Fin a) := diagGL_single_mem hu i
    have key : ∀ I : ℂ, I = ν u * I → I = 0 := fun I hI => by
      by_contra h
      exact hνu' (mul_right_cancel₀ h (by rw [one_mul]; exact hI.symm))
    constructor
    · refine key _ ?_
      have hw : x * d * x⁻¹ ∈ KO k (Fin a) := mul_mem (mul_mem hx hdK) (inv_mem hx)
      conv_lhs => rw [← setIntegral_right μ hK (x * d * x⁻¹) (fun g => Subgroup.mul_mem_cancel_right _ hw)]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun hK fun w hw => ?_
      rw [show w * (x * d * x⁻¹) * (x * torusElt k (Fin a) ϖ m * y) = w * x * d * torusElt k (Fin a) ϖ m * y by group,
        zint_unit hϖ ν z hM hu hi.le (mul_mem hw hx) hy]
      congr 2
      group
    · refine key _ ?_
      have hw : y⁻¹ * d * y ∈ KO k (Fin a) := mul_mem (mul_mem (inv_mem hy) hdK) hy
      have hc : torusElt k (Fin a) ϖ m * d = d * torusElt k (Fin a) ϖ m :=
        Units.ext (by simp [hd, val_torusElt, diagonal_mul_diagonal, mul_comm])
      conv_lhs => rw [← setIntegral_left μ hK (y⁻¹ * d * y) (fun g => Subgroup.mul_mem_cancel_left _ hw)]
      rw [← integral_const_mul]
      refine setIntegral_congr_fun hK fun w hw => ?_
      rw [show x * torusElt k (Fin a) ϖ m * y * (y⁻¹ * d * y * w) = x * (torusElt k (Fin a) ϖ m * d) * (y * w) by group,
        hc, ← mul_assoc x, zint_unit hϖ ν z hM hu hi.le hx (mul_mem hy hw)]
      congr 2
      group

/- English proof (translation)
Use `haar_ne_zero_ne_top μ (isOpen_KO (k := k) (n := Fin a)) le_rfl` as an intermediate fact. Rewrite using `[Complex.ofReal_ne_zero, Measure.real, ENNReal.toReal_ne_zero]`. Conclude with `this`.
-/
theorem measureReal_KO_ne (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] : (μ.real (KO k (Fin a)) : ℂ) ≠ 0 := by
  have := haar_ne_zero_ne_top μ (isOpen_KO (k := k) (n := Fin a)) le_rfl
  rw [Complex.ofReal_ne_zero, Measure.real, ENNReal.toReal_ne_zero]
  exact this

/- English proof (translation)
Take `⟨C, hC, h0⟩` from `exists_compact_avg μ hϖ hν z hφ`. Establish `hf` using `continuous_zint he z hφ`. Rewrite using `[shellSum_eq]`. Use `finsum_cells μ hϖ hf hC (fun g hg => (h0 g hg).1) (measureReal_KO_ne μ) fun S hS hinv => ?_` and prove the remaining obligations. Conclude with `avg_setIntegral μ isCompact_KO hS (fun x g => zint ν z φ (x * g)) (hf.comp continuous_mul) _ fun x hx => setIntegral_left μ hS.measurableSet x (fun g => (hinv x hx g).1) _`.
-/
theorem shells_left (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} {e : ℕ}
    (hν : ¬ IsUnram ν) (he : CondLE ϖ e ν) (z : ℂ) {φ : Matrix (Fin a) (Fin a) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) :
    (Function.support fun m : {m : Fin a → ℤ // Antitone m} => ∫ g in cell k (Fin a) ϖ m.1, zint ν z φ g ∂μ).Finite ∧
      (μ.real (KO k (Fin a)) : ℂ) * shellSum μ ϖ ν z φ = ∫ g, ∫ x in KO k (Fin a), zint ν z φ (x * g) ∂μ ∂μ := by
  obtain ⟨C, hC, h0⟩ := exists_compact_avg μ hϖ hν z hφ
  have hf := continuous_zint he z hφ
  rw [shellSum_eq]
  refine finsum_cells μ hϖ hf hC (fun g hg => (h0 g hg).1) (measureReal_KO_ne μ) fun S hS hinv => ?_
  exact avg_setIntegral μ isCompact_KO hS (fun x g => zint ν z φ (x * g)) (hf.comp continuous_mul) _
    fun x hx => setIntegral_left μ hS.measurableSet x (fun g => (hinv x hx g).1) _

/- English proof (translation)
Take `⟨C, hC, h0⟩` from `exists_compact_avg μ hϖ hν z hφ`. Establish `hf` using `continuous_zint he z hφ`. Rewrite using `[shellSum_eq]`. Use `(finsum_cells μ hϖ hf hC (fun g hg => (h0 g hg).2) (measureReal_KO_ne μ) fun S hS hinv => ?_).2` and prove the remaining obligations. Conclude with `avg_setIntegral μ isCompact_KO hS (fun x g => zint ν z φ (g * x)) (hf.comp (continuous_snd.mul continuous_fst)) _ fun x hx => setIntegral_right μ hS.measurableSet x (fun g => (hinv x hx g).2) _`.
-/
theorem shells_right (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} {e : ℕ}
    (hν : ¬ IsUnram ν) (he : CondLE ϖ e ν) (z : ℂ) {φ : Matrix (Fin a) (Fin a) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) :
      (μ.real (KO k (Fin a)) : ℂ) * shellSum μ ϖ ν z φ = ∫ g, ∫ x in KO k (Fin a), zint ν z φ (g * x) ∂μ ∂μ := by
  obtain ⟨C, hC, h0⟩ := exists_compact_avg μ hϖ hν z hφ
  have hf := continuous_zint he z hφ
  rw [shellSum_eq]
  refine (finsum_cells μ hϖ hf hC (fun g hg => (h0 g hg).2) (measureReal_KO_ne μ) fun S hS hinv => ?_).2
  exact avg_setIntegral μ isCompact_KO hS (fun x g => zint ν z φ (g * x)) (hf.comp (continuous_snd.mul continuous_fst)) _
    fun x hx => setIntegral_right μ hS.measurableSet x (fun g => (hinv x hx g).2) _

/- English proof (translation)
Simplify using `only [shellSum_eq]`. Rewrite using `[← finsum_add_distrib (shells_left μ hϖ hν he z hφ).1 (shells_left μ hϖ hν he z hφ').1]`. Use `congr 1`. Use function extensionality and compare the values at `m`. Rewrite using `[← integral_add ((continuous_zint he z hφ).continuousOn.integrableOn_compact (isCompact_cell ϖ m.1)) ((continuous_zint he z hφ').continuousOn.integrableOn_compact (isCompact_cell ϖ m.1))]`.

Simplify using `only [zint, add_mul]`.
-/
theorem shellSum_add (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ} {e : ℕ}
    (hν : ¬ IsUnram ν) (he : CondLE ϖ e ν) (z : ℂ) {φ φ' : Matrix (Fin a) (Fin a) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (hφ' : φ' ∈ SB (Matrix (Fin a) (Fin a) k)) :
    shellSum μ ϖ ν z (fun X => φ X + φ' X) = shellSum μ ϖ ν z φ + shellSum μ ϖ ν z φ' := by
  simp only [shellSum_eq]
  rw [← finsum_add_distrib (shells_left μ hϖ hν he z hφ).1 (shells_left μ hϖ hν he z hφ').1]
  congr 1
  funext m
  rw [← integral_add ((continuous_zint he z hφ).continuousOn.integrableOn_compact (isCompact_cell ϖ m.1))
    ((continuous_zint he z hφ').continuousOn.integrableOn_compact (isCompact_cell ϖ m.1))]
  simp only [zint, add_mul]

/- English proof (translation)
Establish `hφ' : (fun X => φ (X * g₀.val)) ∈ SB (Matrix (Fin a) (Fin a) k)`. Simplify using `using comp_mul_mem_SB 1 g₀ hφ`. Use `mul_left_cancel₀ (measureReal_KO_ne μ) ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, (shells_left μ hϖ hν he z hφ).2, (shells_left μ hϖ hν he z hφ').2, ← integral_mul_right_eq_self (fun g => ∫ x in KO k (Fin a), zint ν z φ (x * g) ∂μ) g₀, ← integral_const_mul]`. Simplify using `only [← integral_const_mul, zint_right, mul_assoc _ _ g₀]`.
-/
theorem shellSum_mul_right (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ}
    {e : ℕ} (hν : ¬ IsUnram ν) (he : CondLE ϖ e ν) (z : ℂ) {φ : Matrix (Fin a) (Fin a) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (g₀ : GL (Fin a) k) :
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) z * shellSum μ ϖ ν z (fun X => φ (X * g₀.val)) = shellSum μ ϖ ν z φ := by
  have hφ' : (fun X => φ (X * g₀.val)) ∈ SB (Matrix (Fin a) (Fin a) k) := by
    simpa using comp_mul_mem_SB 1 g₀ hφ
  refine mul_left_cancel₀ (measureReal_KO_ne μ) ?_
  rw [mul_left_comm, (shells_left μ hϖ hν he z hφ).2, (shells_left μ hϖ hν he z hφ').2,
    ← integral_mul_right_eq_self (fun g => ∫ x in KO k (Fin a), zint ν z φ (x * g) ∂μ) g₀, ← integral_const_mul]
  simp only [← integral_const_mul, zint_right, mul_assoc _ _ g₀]

/- English proof (translation)
Establish `hφ' : (fun X => φ (g₀.val * X)) ∈ SB (Matrix (Fin a) (Fin a) k)`. Simplify using `using comp_mul_mem_SB g₀ 1 hφ`. Use `mul_left_cancel₀ (measureReal_KO_ne μ) ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, shells_right μ hϖ hν he z hφ, shells_right μ hϖ hν he z hφ', ← integral_mul_left_eq_self (fun g => ∫ x in KO k (Fin a), zint ν z φ (g * x) ∂μ) g₀, ← integral_const_mul]`. Simplify using `only [← integral_const_mul, zint_left, mul_assoc g₀]`.
-/
theorem shellSum_mul_left (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ}
    {e : ℕ} (hν : ¬ IsUnram ν) (he : CondLE ϖ e ν) (z : ℂ) {φ : Matrix (Fin a) (Fin a) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (g₀ : GL (Fin a) k) :
    (ν (gdet g₀) : ℂ) * apow (gdet g₀) z * shellSum μ ϖ ν z (fun X => φ (g₀.val * X)) = shellSum μ ϖ ν z φ := by
  have hφ' : (fun X => φ (g₀.val * X)) ∈ SB (Matrix (Fin a) (Fin a) k) := by
    simpa using comp_mul_mem_SB g₀ 1 hφ
  refine mul_left_cancel₀ (measureReal_KO_ne μ) ?_
  rw [mul_left_comm, shells_right μ hϖ hν he z hφ, shells_right μ hϖ hν he z hφ',
    ← integral_mul_left_eq_self (fun g => ∫ x in KO k (Fin a), zint ν z φ (g * x) ∂μ) g₀, ← integral_const_mul]
  simp only [← integral_const_mul, zint_left, mul_assoc g₀]

/- English proof (translation)
Use `(finsum_cells μ hϖ (continuous_zint he z hφ) isCompact_KO h0 one_ne_zero fun S _ _ => one_mul _).2` as an intermediate fact. Rewrite `this` using `[one_mul, ← shellSum_eq]`. Then use the resulting hypothesis.
-/
theorem shellSum_of_KO (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] {ϖ : kˣ} (hϖ : IsUnif ϖ) {ν : kˣ →* ℂˣ}
    {e : ℕ} (he : CondLE ϖ e ν) (z : ℂ) {φ : Matrix (Fin a) (Fin a) k → ℂ}
    (hφ : φ ∈ SB (Matrix (Fin a) (Fin a) k)) (h0 : ∀ g, g ∉ KO k (Fin a) → zint ν z φ g = 0) :
    shellSum μ ϖ ν z φ = ∫ g, zint ν z φ g ∂μ := by
  have := (finsum_cells μ hϖ (continuous_zint he z hφ) isCompact_KO h0 one_ne_zero fun S _ _ => one_mul _).2
  rwa [one_mul, ← shellSum_eq] at this

end Shells

section SBfun
variable {n D : Type} [Fintype n] [DecidableEq n] [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
/- English proof (translation)
Take `⟨_, _⟩` from `Model.secondCountable_and_t2_local_field (k := k)`. Use `⟨hΦ.1.comp_continuous (continuous_id.matrix_mul continuous_const), ?_⟩` and prove the remaining obligations. Use `HasCompactSupport.intro (hΦ.2.image (f := fun y => y * R) (continuous_id.matrix_mul continuous_const)) fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Conclude with `hx ⟨_, subset_tsupport _ h0, by simp only [Matrix.mul_assoc, hR, Matrix.mul_one]⟩`.
-/
theorem comp_SB {X : Matrix n D k} {R : Matrix D n k} (hR : X * R = 1) {Φ : Matrix n D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix n D k)) : (fun g : Matrix n n k => Φ (g * X)) ∈ SB (Matrix n n k) := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨hΦ.1.comp_continuous (continuous_id.matrix_mul continuous_const), ?_⟩
  refine HasCompactSupport.intro (hΦ.2.image (f := fun y => y * R) (continuous_id.matrix_mul continuous_const))
    fun x hx => ?_
  by_contra h0
  exact hx ⟨_, subset_tsupport _ h0, by simp only [Matrix.mul_assoc, hR, Matrix.mul_one]⟩

omit [DecidableEq n] in
/- English proof (translation)
Establish `hK : IsCompact (tsupport Φ)` using `hΦ.2`. Establish `hev : ∀ᶠ u in 𝓝 (1 : GL D k), ∀ X ∈ tsupport Φ, Φ (X * u.val) = Φ X`. Use `hK.eventually_forall_of_forall_eventually fun x _ => ?_` and prove the remaining obligations. Establish `h1 : IsLocallyConstant fun z : GL D k × Matrix n D k => Φ (z.2 * z.1.val)` using `hΦ.1.comp_continuous (continuous_snd.matrix_mul (Units.continuous_val.comp continuous_fst))`. Establish `h2 : IsLocallyConstant fun z : GL D k × Matrix n D k => Φ z.2` using `hΦ.1.comp_continuous continuous_snd`.

Use `filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x)] with z e1 e2`. Rewrite using `[e1, e2, Units.val_one, Matrix.mul_one]`. Establish `hev' : ∀ᶠ u in 𝓝 (1 : GL D k), ∀ X ∈ tsupport Φ, Φ (X * (u⁻¹).val) = Φ X` using `(continuous_inv.tendsto' (1 : GL D k) 1 inv_one).eventually hev`. Use `filter_upwards [hev, hev'] with u h1 h2 X`. Distinguish the cases in `hx : X ∈ tsupport Φ`.

Conclude with `h1 X hx`. Distinguish the cases in `hxy : X * u.val ∈ tsupport Φ`. Use `h2 _ hxy` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]`. Conclude with `this.symm`.

Rewrite using `[image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxy]`.
-/
theorem eventually_mul_eq {Φ : Matrix n D k → ℂ} (hΦ : Φ ∈ SB (Matrix n D k)) :
    ∀ᶠ u in 𝓝 (1 : GL D k), ∀ X, Φ (X * u.val) = Φ X := by
  have hK : IsCompact (tsupport Φ) := hΦ.2
  have hev : ∀ᶠ u in 𝓝 (1 : GL D k), ∀ X ∈ tsupport Φ, Φ (X * u.val) = Φ X := by
    refine hK.eventually_forall_of_forall_eventually fun x _ => ?_
    have h1 : IsLocallyConstant fun z : GL D k × Matrix n D k => Φ (z.2 * z.1.val) :=
      hΦ.1.comp_continuous (continuous_snd.matrix_mul (Units.continuous_val.comp continuous_fst))
    have h2 : IsLocallyConstant fun z : GL D k × Matrix n D k => Φ z.2 := hΦ.1.comp_continuous continuous_snd
    filter_upwards [h1.eventually_eq (1, x), h2.eventually_eq (1, x)] with z e1 e2
    rw [e1, e2, Units.val_one, Matrix.mul_one]
  have hev' : ∀ᶠ u in 𝓝 (1 : GL D k), ∀ X ∈ tsupport Φ, Φ (X * (u⁻¹).val) = Φ X :=
    (continuous_inv.tendsto' (1 : GL D k) 1 inv_one).eventually hev
  filter_upwards [hev, hev'] with u h1 h2 X
  by_cases hx : X ∈ tsupport Φ
  · exact h1 X hx
  by_cases hxy : X * u.val ∈ tsupport Φ
  · have := h2 _ hxy
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hxy]

/- English proof (translation)
The claim follows from `Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩`.
-/
theorem continuous_invT : Continuous (invT : GL D k → GL D k) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

/- English proof (translation)
Set `U : Subgroup (GL D k)` to `{ carrier := {u | omA ν β 1 u Φ = Φ} one_mem' := LinearMap.congr_fun (repA ν β).map_one Φ mul_mem' := fun {u v} hu hv => by`. Use `omA_mul ν β 1 1 u v Φ` as an intermediate fact. Rewrite `this` using `[mul_one, show omA ν β 1 v Φ = Φ from hv, show omA ν β 1 u Φ = Φ from hu]`. Conclude with `this`. Use the proof step `inv_mem' := fun {u} hu => by`.

Use `omA_mul ν β 1 1 u⁻¹ u Φ` as an intermediate fact. Rewrite `this` using `[mul_one, inv_mul_cancel, show omA ν β 1 u Φ = Φ from hu]`. Conclude with `this.symm.trans (LinearMap.congr_fun (repA ν β).map_one Φ) }`. Use `⟨U, U.isOpen_of_mem_nhds (g := 1) ?_, fun u hu => hu⟩` and prove the remaining obligations. Use `filter_upwards [(isOpen_detCong (ϖ ^ e) D).mem_nhds (one_mem _), (continuous_invT.tendsto' (1 : GL D k) 1 (map_one _)).eventually (eventually_mul_eq hΦ)] with u h1 h2`.

Use function extensionality and compare the values at `X`. Simplify using `[omA, h2, hβ _ h1.2, apow_of_valuation_eq_one h1.2.1]`.
-/
theorem exists_open_omA {ϖ : kˣ} {e : ℕ} (ν : kˣ →* ℂˣ) {β : kˣ →* ℂˣ} (hβ : CondLE ϖ e β) {Φ : Matrix n D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix n D k)) :
    ∃ U : Subgroup (GL D k), IsOpen (U : Set (GL D k)) ∧ ∀ u ∈ U, omA ν β 1 u Φ = Φ := by
  let U : Subgroup (GL D k) :=
    { carrier := {u | omA ν β 1 u Φ = Φ}
      one_mem' := LinearMap.congr_fun (repA ν β).map_one Φ
      mul_mem' := fun {u v} hu hv => by
        have := omA_mul ν β 1 1 u v Φ
        rw [mul_one, show omA ν β 1 v Φ = Φ from hv, show omA ν β 1 u Φ = Φ from hu] at this
        exact this
      inv_mem' := fun {u} hu => by
        have := omA_mul ν β 1 1 u⁻¹ u Φ
        rw [mul_one, inv_mul_cancel, show omA ν β 1 u Φ = Φ from hu] at this
        exact this.symm.trans (LinearMap.congr_fun (repA ν β).map_one Φ) }
  refine ⟨U, U.isOpen_of_mem_nhds (g := 1) ?_, fun u hu => hu⟩
  filter_upwards [(isOpen_detCong (ϖ ^ e) D).mem_nhds (one_mem _),
    (continuous_invT.tendsto' (1 : GL D k) 1 (map_one _)).eventually (eventually_mul_eq hΦ)] with u h1 h2
  funext X
  simp [omA, h2, hβ _ h1.2, apow_of_valuation_eq_one h1.2.1]

/- English proof (translation)
Set `U : Subgroup (GL D k)` to `{ carrier := {u | omB ν α 1 u Φ = Φ} one_mem' := LinearMap.congr_fun (repB ν α).map_one Φ mul_mem' := fun {u v} hu hv => by`. Use `omB_mul ν α 1 1 u v Φ` as an intermediate fact. Rewrite `this` using `[mul_one, show omB ν α 1 v Φ = Φ from hv, show omB ν α 1 u Φ = Φ from hu]`. Conclude with `this`. Use the proof step `inv_mem' := fun {u} hu => by`.

Use `omB_mul ν α 1 1 u⁻¹ u Φ` as an intermediate fact. Rewrite `this` using `[mul_one, inv_mul_cancel, show omB ν α 1 u Φ = Φ from hu]`. Conclude with `this.symm.trans (LinearMap.congr_fun (repB ν α).map_one Φ) }`. Use `⟨U, U.isOpen_of_mem_nhds (g := 1) ?_, fun u hu => hu⟩` and prove the remaining obligations. Use `filter_upwards [(isOpen_detCong (ϖ ^ e) D).mem_nhds (one_mem _), eventually_mul_eq hΦ] with u h1 h2`.

Use function extensionality and compare the values at `X`. Simplify using `[omB, h2, hα _ h1.2, apow_of_valuation_eq_one h1.2.1]`.
-/
theorem exists_open_omB {ϖ : kˣ} {e : ℕ} (ν : kˣ →* ℂˣ) {α : kˣ →* ℂˣ} (hα : CondLE ϖ e α) {Φ : Matrix n D k → ℂ}
    (hΦ : Φ ∈ SB (Matrix n D k)) :
    ∃ U : Subgroup (GL D k), IsOpen (U : Set (GL D k)) ∧ ∀ u ∈ U, omB ν α 1 u Φ = Φ := by
  let U : Subgroup (GL D k) :=
    { carrier := {u | omB ν α 1 u Φ = Φ}
      one_mem' := LinearMap.congr_fun (repB ν α).map_one Φ
      mul_mem' := fun {u v} hu hv => by
        have := omB_mul ν α 1 1 u v Φ
        rw [mul_one, show omB ν α 1 v Φ = Φ from hv, show omB ν α 1 u Φ = Φ from hu] at this
        exact this
      inv_mem' := fun {u} hu => by
        have := omB_mul ν α 1 1 u⁻¹ u Φ
        rw [mul_one, inv_mul_cancel, show omB ν α 1 u Φ = Φ from hu] at this
        exact this.symm.trans (LinearMap.congr_fun (repB ν α).map_one Φ) }
  refine ⟨U, U.isOpen_of_mem_nhds (g := 1) ?_, fun u hu => hu⟩
  filter_upwards [(isOpen_detCong (ϖ ^ e) D).mem_nhds (one_mem _), eventually_mul_eq hΦ] with u h1 h2
  funext X
  simp [omB, h2, hα _ h1.2, apow_of_valuation_eq_one h1.2.1]

variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Take `⟨m, hm, -⟩` from `Model.exists_isUnitVol (k := k)`. Use `isHaarMeasure_volGL (n := n) m` as an intermediate fact. Rewrite using `[Measure.isMulLeftInvariant_eq_smul μ (volGL m n)]`. Use `Integrable.smul_measure_nnreal ?_` and prove the remaining obligations. Take `⟨B, hB⟩` from `GlobalTheory.ZetaConvergence.exists_nabs_le (IsCompact.image hφ.2 (f := fun x : Matrix n n k => x.det) continuous_id.matrix_det)`.

Take `⟨_, _⟩` from `Model.secondCountable_and_t2_local_field (k := k)`. Establish `: BorelSpace (Matrix n n k)` using `inferInstanceAs (BorelSpace (n → n → k))`. Establish `: (volM m n n).IsAddHaarMeasure` using `Measure.pi.isAddHaarMeasure _`. Establish `hE` using `Model.measurableEmbedding_val (k := k) n`. Establish `hd` using `continuous_density_volGL (k := k) (n := n)`.

Establish `hI : Integrable (fun g : GL n k => φ g.val) ((volM m n n).comap fun g : GL n k => g.val)`. Establish `h1 : Integrable φ (volM m n n)` using `hφ.1.continuous.integrable_of_hasCompactSupport hφ.2`. Use `(hE.integrable_map_iff (g := φ)).1 ?_` and prove the remaining obligations. Rewrite using `[hE.map_comap]`. Conclude with `h1.restrict`.

Unfold `volGL`. Rewrite using `[integrable_withDensity_iff_integrable_smul' hd.measurable (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]`. Use `(hI.norm.mul_const (B ^ (z.re - Fintype.card n))).mono' (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul (continuous_zint he z hφ).aestronglyMeasurable) (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Establish `hp` using `Model.nabs_pos (GeneralLinearGroup.det g)`. Distinguish the cases in `h0 : φ g.val = 0`.

Simplify using `[zint, h0]`. Establish `h1 : nabs k (GeneralLinearGroup.det g) ≤ B` using `hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩`. Establish `e1 : ‖zint ν z φ g‖ = ‖φ g.val‖ * nabs k (GeneralLinearGroup.det g) ^ z.re`. Rewrite using `[zint, norm_mul, norm_mul, hu, mul_one, apow, Complex.norm_cpow_eq_rpow_re_of_pos hp]`. Rewrite using `[norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), e1, mul_left_comm, ← Real.rpow_add hp, neg_add_eq_sub]`.

Conclude with `mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.le h1 (sub_nonneg.2 hz)) (norm_nonneg _)`.
-/
theorem integrable_zint (μ : Measure (GL n k)) [μ.IsHaarMeasure] {ϖ : kˣ} {e : ℕ} {ν : kˣ →* ℂˣ} (he : CondLE ϖ e ν)
    (hu : ∀ x, ‖(ν x : ℂ)‖ = 1) {z : ℂ} (hz : (Fintype.card n : ℝ) ≤ z.re) {φ : Matrix n n k → ℂ}
    (hφ : φ ∈ SB (Matrix n n k)) : Integrable (zint ν z φ) μ := by
  obtain ⟨m, hm, -⟩ := Model.exists_isUnitVol (k := k)
  have := isHaarMeasure_volGL (n := n) m
  rw [Measure.isMulLeftInvariant_eq_smul μ (volGL m n)]
  refine Integrable.smul_measure_nnreal ?_
  obtain ⟨B, hB⟩ := GlobalTheory.ZetaConvergence.exists_nabs_le (IsCompact.image hφ.2
    (f := fun x : Matrix n n k => x.det) continuous_id.matrix_det)
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : BorelSpace (Matrix n n k) := inferInstanceAs (BorelSpace (n → n → k))
  have : (volM m n n).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hE := Model.measurableEmbedding_val (k := k) n
  have hd := continuous_density_volGL (k := k) (n := n)
  have hI : Integrable (fun g : GL n k => φ g.val) ((volM m n n).comap fun g : GL n k => g.val) := by
    have h1 : Integrable φ (volM m n n) := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2
    refine (hE.integrable_map_iff (g := φ)).1 ?_
    rw [hE.map_comap]
    exact h1.restrict
  unfold volGL
  rw [integrable_withDensity_iff_integrable_smul' hd.measurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine (hI.norm.mul_const (B ^ (z.re - Fintype.card n))).mono'
    (hd.measurable.ennreal_toReal.aestronglyMeasurable.smul (continuous_zint he z hφ).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun g => ?_)
  have hp := Model.nabs_pos (GeneralLinearGroup.det g)
  by_cases h0 : φ g.val = 0
  · simp [zint, h0]
  have h1 : nabs k (GeneralLinearGroup.det g) ≤ B := hB _ ⟨g.val, subset_tsupport _ h0, rfl⟩
  have e1 : ‖zint ν z φ g‖ = ‖φ g.val‖ * nabs k (GeneralLinearGroup.det g) ^ z.re := by
    rw [zint, norm_mul, norm_mul, hu, mul_one, apow, Complex.norm_cpow_eq_rpow_re_of_pos hp]
  rw [norm_smul, ENNReal.toReal_ofReal (Real.rpow_nonneg hp.le _), Real.norm_of_nonneg (Real.rpow_nonneg hp.le _), e1,
    mul_left_comm, ← Real.rpow_add hp, neg_add_eq_sub]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hp.le h1 (sub_nonneg.2 hz)) (norm_nonneg _)

omit [DecidableEq D] in
/- English proof (translation)
Take `⟨_, _⟩` from `Model.secondCountable_and_t2_local_field (k := k)`. Establish `: NonarchimedeanAddGroup k` using `⟨fun V hV => by`. Take `⟨s, hs⟩` from `exists_cball_subset hV`. Conclude with `⟨⟨⟨⟨⟨cball s, add_mem_cball⟩, by simp [cball]⟩, neg_mem_cball⟩, isOpen_cball s⟩, hs⟩⟩`. Establish `: TotallyDisconnectedSpace k` using `inferInstance`.

Establish `: TotallyDisconnectedSpace (Matrix n D k)` using `inferInstanceAs (TotallyDisconnectedSpace (n → D → k))`. Establish `: LocallyCompactSpace (Matrix n D k)` using `inferInstanceAs (LocallyCompactSpace (n → D → k))`. Take `⟨t, ht, hV⟩` from `(isEmbedding_val_GL (k := k) (n := n)).isInducing.isOpen_iff.1 (isOpen_detCong (ϖ ^ e) n)`. Establish `h1 : (1 : Matrix n n k) ∈ t`. Establish `: (1 : GL n k) ∈ (fun g : GL n k => g.val) ⁻¹' t` using `hV ▸ one_mem (detCong (ϖ ^ e) n)`.

Conclude with `this`. Take `⟨W, hWc, hWo, hXW, hW⟩` from `GlobalTheory.SBExtend.exists_isCompact_isClopen_between (K := {X}) (W := (fun Y : Matrix n D k => Y * R) ⁻¹' t) isCompact_singleton (ht.preimage (continuous_id.matrix_mul continuous_const)) (by simpa [hR] using h1)`. Use `set S : Set (GL n k) := {g | g.val * X ∈ W} with hS`. Establish `hSo : IsOpen S` using `hWo.isOpen.preimage (Units.continuous_val.matrix_mul continuous_const)`. Establish `hSV : S ⊆ detCong (ϖ ^ e) n` using `fun g hg => by`.

Use `hW hg` as an intermediate fact. Simplify using `only [Set.mem_preimage, Matrix.mul_assoc, hR, Matrix.mul_one] at this`. Rewrite using `[← hV]`. Conclude with `this`. Establish `hz : zint ν z (fun g => W.indicator (fun _ => (1 : ℂ)) (g * X)) = S.indicator fun _ => 1`.

Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g ∈ S`. Rewrite using `[zint, Set.indicator_of_mem hg, Set.indicator_of_mem (show g.val * X ∈ W from hg), he _ (hSV hg).2, apow_of_valuation_eq_one (hSV hg).2.1]`. Simplify using the standard rewrite rules. Rewrite using `[zint, Set.indicator_of_notMem hg, Set.indicator_of_notMem (show g.val * X ∉ W from hg), zero_mul, zero_mul]`.

Use `⟨W.indicator fun _ => 1, GlobalTheory.SBExtend.indicator_mem_SB hWc hWo, fun g hg => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hz, Set.indicator_of_notMem fun h => hg (hSV h).1]`. Rewrite using `[hz, integral_indicator hSo.measurableSet, setIntegral_const, Complex.real_smul, mul_one, Complex.ofReal_ne_zero, Measure.real, ENNReal.toReal_ne_zero]`. Conclude with `⟨(hSo.measure_pos μ ⟨1, by simpa [hS] using hXW⟩).ne', ((measure_mono fun g hg => (hSV hg).1).trans_lt isCompact_KO.measure_lt_top).ne⟩`.
-/
theorem exists_bump (μ : Measure (GL n k)) [μ.IsHaarMeasure] {ϖ : kˣ} {e : ℕ} {ν : kˣ →* ℂˣ} (he : CondLE ϖ e ν) (z : ℂ)
    {X : Matrix n D k} {R : Matrix D n k} (hR : X * R = 1) :
    ∃ Φ ∈ SB (Matrix n D k), (∀ g, g ∉ KO k n → zint ν z (fun g => Φ (g * X)) g = 0) ∧
      ∫ g, zint ν z (fun g => Φ (g * X)) g ∂μ ≠ 0 := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  have : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨cball s, add_mem_cball⟩, by simp [cball]⟩, neg_mem_cball⟩, isOpen_cball s⟩, hs⟩⟩
  have : TotallyDisconnectedSpace k := inferInstance
  have : TotallyDisconnectedSpace (Matrix n D k) := inferInstanceAs (TotallyDisconnectedSpace (n → D → k))
  have : LocallyCompactSpace (Matrix n D k) := inferInstanceAs (LocallyCompactSpace (n → D → k))
  obtain ⟨t, ht, hV⟩ := (isEmbedding_val_GL (k := k) (n := n)).isInducing.isOpen_iff.1 (isOpen_detCong (ϖ ^ e) n)
  have h1 : (1 : Matrix n n k) ∈ t := by
    have : (1 : GL n k) ∈ (fun g : GL n k => g.val) ⁻¹' t := hV ▸ one_mem (detCong (ϖ ^ e) n)
    exact this
  obtain ⟨W, hWc, hWo, hXW, hW⟩ := GlobalTheory.SBExtend.exists_isCompact_isClopen_between (K := {X})
    (W := (fun Y : Matrix n D k => Y * R) ⁻¹' t) isCompact_singleton
    (ht.preimage (continuous_id.matrix_mul continuous_const)) (by simpa [hR] using h1)
  set S : Set (GL n k) := {g | g.val * X ∈ W} with hS
  have hSo : IsOpen S := hWo.isOpen.preimage (Units.continuous_val.matrix_mul continuous_const)
  have hSV : S ⊆ detCong (ϖ ^ e) n := fun g hg => by
    have := hW hg
    simp only [Set.mem_preimage, Matrix.mul_assoc, hR, Matrix.mul_one] at this
    rw [← hV]
    exact this
  have hz : zint ν z (fun g => W.indicator (fun _ => (1 : ℂ)) (g * X)) = S.indicator fun _ => 1 := by
    funext g
    by_cases hg : g ∈ S
    · rw [zint, Set.indicator_of_mem hg, Set.indicator_of_mem (show g.val * X ∈ W from hg), he _ (hSV hg).2,
        apow_of_valuation_eq_one (hSV hg).2.1]
      simp
    · rw [zint, Set.indicator_of_notMem hg, Set.indicator_of_notMem (show g.val * X ∉ W from hg), zero_mul, zero_mul]
  refine ⟨W.indicator fun _ => 1, GlobalTheory.SBExtend.indicator_mem_SB hWc hWo, fun g hg => ?_, ?_⟩
  · rw [hz, Set.indicator_of_notMem fun h => hg (hSV h).1]
  · rw [hz, integral_indicator hSo.measurableSet, setIntegral_const, Complex.real_smul, mul_one, Complex.ofReal_ne_zero,
      Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨(hSo.measure_pos μ ⟨1, by simpa [hS] using hXW⟩).ne',
      ((measure_mono fun g hg => (hSV hg).1).trans_lt isCompact_KO.measure_lt_top).ne⟩

end SBfun

section Blocks
variable {a a' : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc h.val, Units.mul_inv, Matrix.one_mul]`. Use extensionality with `i j`. Rewrite using `[frameMatrixFirstColumnBlock_mul_apply]`. Simplify using `only [X0, transpose_apply, of_apply, one_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, eq_comm]`.
-/
theorem upperProjection_right_inverse (h : GL (Fin (a + a')) k) : X0 k (finSumFinEquiv (m := a) (n := a')) * h.val *
    ((h⁻¹).val * (X0 k (finSumFinEquiv (m := a) (n := a')))ᵀ) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc h.val, Units.mul_inv, Matrix.one_mul]
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply]
  simp only [X0, transpose_apply, of_apply, one_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, eq_comm]

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc h.val, Units.mul_inv, Matrix.one_mul]`. Use extensionality with `i j`. Rewrite using `[frameMatrixSecondColumnBlock_mul_apply]`. Simplify using `only [Y0, transpose_apply, of_apply, one_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, eq_comm]`.
-/
theorem lowerProjection_right_inverse (h : GL (Fin (a + a')) k) : Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val *
    ((h⁻¹).val * (Y0 k (finSumFinEquiv (m := a) (n := a')))ᵀ) = 1 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc h.val, Units.mul_inv, Matrix.one_mul]
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply]
  simp only [Y0, transpose_apply, of_apply, one_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, eq_comm]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, h1, h2, gdet, GeneralLinearGroup.val_det_apply, ← det_submatrix_equiv_self (finSumFinEquiv (m := a) (n := a')), show b.val.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (blkA b) (Matrix.of fun i j => b.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.i …`. Use extensionality with `(i | i) (j | j)`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Conclude with `hb i j`. Both sides reduce to the same expression.
-/
theorem gdet_block {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) {dA dD : kˣ} (h1 : (dA : k) = (blkA b).det)
    (h2 : (dD : k) = (blkD b).det) : gdet b = dA * dD := by
  refine Units.ext ?_
  rw [Units.val_mul, h1, h2, gdet, GeneralLinearGroup.val_det_apply,
    ← det_submatrix_equiv_self (finSumFinEquiv (m := a) (n := a')),
    show b.val.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks (blkA b)
      (Matrix.of fun i j => b.val (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j))) 0 (blkD b) from ?_,
    det_fromBlocks_zero₂₁]
  ext (i | i) (j | j)
  · rfl
  · rfl
  · exact hb i j
  · rfl

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[frameMatrixFirstColumnBlock_mul_apply]`. Take `⟨j | j, rfl⟩` from `(finSumFinEquiv (m := a) (n := a')).surjective j`. Simplify using `only [Matrix.mul_apply, X0, of_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Both sides reduce to the same expression.

Simplify using `only [Matrix.mul_apply, X0, of_apply, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero]`. Conclude with `hb j i`.
-/
theorem upperProjection_blockUpper_transpose {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) :
    X0 k (finSumFinEquiv (m := a) (n := a')) * b.valᵀ = (blkA b)ᵀ * X0 k (finSumFinEquiv (m := a) (n := a')) := by
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply]
  obtain ⟨j | j, rfl⟩ := (finSumFinEquiv (m := a) (n := a')).surjective j
  · simp only [Matrix.mul_apply, X0, of_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inl.injEq, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · simp only [Matrix.mul_apply, X0, of_apply, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, if_false, mul_zero,
      Finset.sum_const_zero]
    exact hb j i

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[frameMatrixSecondColumnBlock_mul_apply]`. Take `⟨j | j, rfl⟩` from `(finSumFinEquiv (m := a) (n := a')).surjective j`. Simplify using `only [Matrix.mul_apply, Y0, of_apply, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero]`. Conclude with `hb i j`.

Simplify using `only [Matrix.mul_apply, Y0, of_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Both sides reduce to the same expression.
-/
theorem lowerProjection_blockUpper {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) :
    Y0 k (finSumFinEquiv (m := a) (n := a')) * b.val = blkD b * Y0 k (finSumFinEquiv (m := a) (n := a')) := by
  ext i j
  rw [frameMatrixSecondColumnBlock_mul_apply]
  obtain ⟨j | j, rfl⟩ := (finSumFinEquiv (m := a) (n := a')).surjective j
  · simp only [Matrix.mul_apply, Y0, of_apply, EmbeddingLike.apply_eq_iff_eq, reduceCtorEq, if_false, mul_zero,
      Finset.sum_const_zero]
    exact hb i j
  · simp only [Matrix.mul_apply, Y0, of_apply, EmbeddingLike.apply_eq_iff_eq, Sum.inr.injEq, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl

/- English proof (translation)
Establish `hd : ((blkA b)ᵀ).det ≠ 0` using `by rw [det_transpose, ← h1]; exact dA.ne_zero`. Use `⟨GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext ((det_transpose _).trans h1.symm), ?_⟩` and prove the remaining obligations. Rewrite using `[show (GeneralLinearGroup.mkOfDetNeZero _ hd).val = (blkA b)ᵀ from rfl, ← Matrix.mul_assoc, ← upperProjection_blockUpper_transpose hb, Matrix.mul_assoc, ← invT_inv_val, Units.inv_mul, Matrix.mul_one]`.
-/
theorem exists_upperProjection_inverse_transpose {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) {dA : kˣ} (h1 : (dA : k) = (blkA b).det) :
    ∃ C : GL (Fin a) k, gdet C = dA ∧
      C.val * (X0 k (finSumFinEquiv (m := a) (n := a')) * (invT b).val) = X0 k (finSumFinEquiv (m := a) (n := a')) := by
  have hd : ((blkA b)ᵀ).det ≠ 0 := by rw [det_transpose, ← h1]; exact dA.ne_zero
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hd, Units.ext ((det_transpose _).trans h1.symm), ?_⟩
  rw [show (GeneralLinearGroup.mkOfDetNeZero _ hd).val = (blkA b)ᵀ from rfl, ← Matrix.mul_assoc,
    ← upperProjection_blockUpper_transpose hb, Matrix.mul_assoc, ← invT_inv_val, Units.inv_mul, Matrix.mul_one]

/- English proof (translation)
Assemble the required witnesses or components as `⟨GeneralLinearGroup.mkOfDetNeZero _ (h2 ▸ dD.ne_zero), Units.ext h2.symm, lowerProjection_blockUpper hb⟩`.
-/
theorem exists_lowerProjection_conj {b : GL (Fin (a + a')) k} (hb : IsBlockUpper b) {dD : kˣ} (h2 : (dD : k) = (blkD b).det) :
    ∃ C : GL (Fin a') k, gdet C = dD ∧
      Y0 k (finSumFinEquiv (m := a) (n := a')) * b.val = C.val * Y0 k (finSumFinEquiv (m := a) (n := a')) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero _ (h2 ▸ dD.ne_zero), Units.ext h2.symm, lowerProjection_blockUpper hb⟩

end Blocks

section Maps
variable [MeasurableSpace k] [BorelSpace k] {a a' : ℕ} {ϖ : kˣ} {α β ν : kˣ →* ℂˣ}

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Take `⟨e, h1, h2⟩` from `H.cond`. Conclude with `⟨e, H.quot ▸ h1.div h2⟩`.
-/
theorem HidaSetting.condν (H : HidaSetting a a' ϖ α β ν) : ∃ e, CondLE ϖ e ν := by
  obtain ⟨e, h1, h2⟩ := H.cond
  exact ⟨e, H.quot ▸ h1.div h2⟩

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Rewrite using `[H.quot]`. Simplify using `[H.unitα, H.unitβ]`.
-/
theorem HidaSetting.unitν (H : HidaSetting a a' ϖ α β ν) (x : kˣ) : ‖(ν x : ℂ)‖ = 1 := by
  rw [H.quot]; simp [H.unitα, H.unitβ]

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Rewrite using `[H.quot]`. Simplify using the standard rewrite rules.
-/
theorem HidaSetting.alpha_eq (H : HidaSetting a a' ϖ α β ν) (x : kˣ) : (α x : ℂ) = ν x * β x := by
  rw [H.quot]; simp

/- English proof (translation)
Use function extensionality and compare the values at `h`. Simplify using `only [pRam, rtr, bigP, ← omA_mul, mul_one]`.
-/
theorem pRam_equiv (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (h₁ : GL (Fin (a + a')) k) :
    pRam a a' ϖ ν β (omA ν β 1 h₁ Φ) = rtr h₁ (pRam a a' ϖ ν β Φ) := by
  funext h
  simp only [pRam, rtr, bigP, ← omA_mul, mul_one]

/- English proof (translation)
Use function extensionality and compare the values at `h`. Simplify using `only [pRam', rtr, smallP_eq, ← omB_mul, mul_one]`.
-/
theorem pRam'_equiv (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ) (h₁ : GL (Fin (a + a')) k) :
    pRam' a a' ν α (omB ν α 1 h₁ Ψ) = rtr h₁ (pRam' a a' ν α Ψ) := by
  funext h
  simp only [pRam', rtr, smallP_eq, ← omB_mul, mul_one]

/- English proof (translation)
Take `⟨e, he⟩` from `H.condν`. Use function extensionality and compare the values at `h`. Establish `h1` using `shellSum_add (haarVol (KO k (Fin a))) H.unif hν he ((Fintype.card (Fin (a + a')) : ℂ) / 2) (comp_SB (upperProjection_right_inverse (invT h)) hΦ) (comp_SB (upperProjection_right_inverse (invT h)) ((SB _).smul_mem c hΦ₁))`. Simplify using `only [Pi.smul_apply, smul_eq_mul, shellSum_smul] at h1`. Simplify using `only [pRam, bigZetaIntegral_eq, bigF, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pRam_add (H : HidaSetting a a' ϖ α β ν) (hν : ¬ IsUnram ν) {Φ Φ₁ : Matrix (Fin a) (Fin (a + a')) k → ℂ}
    (hΦ : Φ ∈ SB _) (hΦ₁ : Φ₁ ∈ SB _) (c : ℂ) :
    pRam a a' ϖ ν β (Φ + c • Φ₁) = pRam a a' ϖ ν β Φ + c • pRam a a' ϖ ν β Φ₁ := by
  obtain ⟨e, he⟩ := H.condν
  funext h
  have h1 := shellSum_add (haarVol (KO k (Fin a))) H.unif hν he ((Fintype.card (Fin (a + a')) : ℂ) / 2)
    (comp_SB (upperProjection_right_inverse (invT h)) hΦ) (comp_SB (upperProjection_right_inverse (invT h)) ((SB _).smul_mem c hΦ₁))
  simp only [Pi.smul_apply, smul_eq_mul, shellSum_smul] at h1
  simp only [pRam, bigZetaIntegral_eq, bigF, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1]
  ring

/- English proof (translation)
Take `⟨e, he⟩` from `H.condν`. Use function extensionality and compare the values at `h`. Establish `hz : (Fintype.card (Fin a') : ℝ) ≤ ((Fintype.card (Fin (a + a')) : ℂ) / 2).re`. Establish `: (a' : ℝ) < a` using `by exact_mod_cast H.lt`. Simplify using `only [Fintype.card_fin, Complex.div_ofNat_re, Complex.natCast_re]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `integral_add (integrable_zint (haarVol (KO k (Fin a'))) he H.unitν hz (comp_SB (lowerProjection_right_inverse h) hΨ)) ((integrable_zint (haarVol (KO k (Fin a'))) he H.unitν hz (comp_SB (lowerProjection_right_inverse h) hΨ₁)).const_mul c)`. Rewrite `h1` using `[integral_const_mul]`. Simplify using `only [zint] at h1`.

Simplify using `only [pRam', smallP, smallF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[mul_left_comm c, ← mul_add, ← h1]`. Use `congr 2`. Use function extensionality and compare the values at `g`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pRam'_add (H : HidaSetting a a' ϖ α β ν) {Ψ Ψ₁ : Matrix (Fin a') (Fin (a + a')) k → ℂ}
    (hΨ : Ψ ∈ SB _) (hΨ₁ : Ψ₁ ∈ SB _) (c : ℂ) :
    pRam' a a' ν α (Ψ + c • Ψ₁) = pRam' a a' ν α Ψ + c • pRam' a a' ν α Ψ₁ := by
  obtain ⟨e, he⟩ := H.condν
  funext h
  have hz : (Fintype.card (Fin a') : ℝ) ≤ ((Fintype.card (Fin (a + a')) : ℂ) / 2).re := by
    have : (a' : ℝ) < a := by exact_mod_cast H.lt
    simp only [Fintype.card_fin, Complex.div_ofNat_re, Complex.natCast_re]
    push_cast
    linarith
  have h1 := integral_add (integrable_zint (haarVol (KO k (Fin a'))) he H.unitν hz (comp_SB (lowerProjection_right_inverse h) hΨ))
    ((integrable_zint (haarVol (KO k (Fin a'))) he H.unitν hz (comp_SB (lowerProjection_right_inverse h) hΨ₁)).const_mul c)
  rw [integral_const_mul] at h1
  simp only [zint] at h1
  simp only [pRam', smallP, smallF, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_left_comm c, ← mul_add, ← h1]
  congr 2
  funext g
  ring

/- English proof (translation)
Take `⟨e, he⟩` from `H.condν`. Take `⟨e', -, hβ⟩` from `H.cond`. Take `⟨U, hU, hinv⟩` from `exists_open_omA ν hβ hΦ`. Use `⟨⟨U, hU, fun u hu h => ?_⟩, fun b h hb dA dD h1 h2 => ?_⟩` and prove the remaining obligations. Use `congrFun (pRam_equiv (ϖ := ϖ) (ν := ν) (β := β) Φ u) h` as an intermediate fact.

Rewrite `this` using `[hinv u hu]`. Conclude with `this.symm`. Take `⟨C, hC, hX⟩` from `exists_upperProjection_inverse_transpose hb h1`. Establish `h3` using `shellSum_mul_right (haarVol (KO k (Fin a))) H.unif hν he ((Fintype.card (Fin (a + a')) : ℂ) / 2) (comp_SB (upperProjection_right_inverse (invT (b * h))) hΦ) C`. Establish `h4 : C.val * (X0 k (finSumFinEquiv (m` using `a) (n := a')) * (invT (b * h)).val) = X0 k (finSumFinEquiv (m := a) (n := a')) * (invT h).val := by`.

Rewrite using `[map_mul, Units.val_mul, ← Matrix.mul_assoc (X0 k _), ← Matrix.mul_assoc, hX]`. Simplify using `only [Matrix.mul_assoc _ C.val, h4, hC] at h3`. Establish `h5 : apow dA (-(a : ℂ) / 2) * apow dA ((Fintype.card (Fin (a + a')) : ℂ) / 2) = apow dA ((a' : ℂ) / 2)`. Rewrite using `[← apow_add]`. Use `congr 1`.

Simplify using `only [Fintype.card_fin, Nat.cast_add]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [pRam, bigZetaIntegral_eq, bigF]`. Rewrite using `[← h3]`. Simplify using `only [indFac, gdet_block hb h1 h2, map_mul, apow_mul, Units.val_mul, H.alpha_eq, ← h5]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pRam_mem (H : HidaSetting a a' ϖ α β ν) (hν : ¬ IsUnram ν) {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ}
    (hΦ : Φ ∈ SB _) : pRam a a' ϖ ν β Φ ∈ indSp a a' α β := by
  obtain ⟨e, he⟩ := H.condν
  obtain ⟨e', -, hβ⟩ := H.cond
  obtain ⟨U, hU, hinv⟩ := exists_open_omA ν hβ hΦ
  refine ⟨⟨U, hU, fun u hu h => ?_⟩, fun b h hb dA dD h1 h2 => ?_⟩
  · have := congrFun (pRam_equiv (ϖ := ϖ) (ν := ν) (β := β) Φ u) h
    rw [hinv u hu] at this
    exact this.symm
  · obtain ⟨C, hC, hX⟩ := exists_upperProjection_inverse_transpose hb h1
    have h3 := shellSum_mul_right (haarVol (KO k (Fin a))) H.unif hν he ((Fintype.card (Fin (a + a')) : ℂ) / 2)
      (comp_SB (upperProjection_right_inverse (invT (b * h))) hΦ) C
    have h4 : C.val * (X0 k (finSumFinEquiv (m := a) (n := a')) * (invT (b * h)).val) = X0 k (finSumFinEquiv (m := a) (n := a')) * (invT h).val := by
      rw [map_mul, Units.val_mul, ← Matrix.mul_assoc (X0 k _), ← Matrix.mul_assoc, hX]
    simp only [Matrix.mul_assoc _ C.val, h4, hC] at h3
    have h5 : apow dA (-(a : ℂ) / 2) * apow dA ((Fintype.card (Fin (a + a')) : ℂ) / 2) = apow dA ((a' : ℂ) / 2) := by
      rw [← apow_add]; congr 1; simp only [Fintype.card_fin, Nat.cast_add]; ring
    simp only [pRam, bigZetaIntegral_eq, bigF]
    rw [← h3]
    simp only [indFac, gdet_block hb h1 h2, map_mul, apow_mul, Units.val_mul,
      H.alpha_eq, ← h5]
    ring

/- English proof (translation)
Take `⟨e', hα, -⟩` from `H.cond`. Take `⟨U, hU, hinv⟩` from `exists_open_omB ν hα hΨ`. Use `⟨⟨U, hU, fun u hu h => ?_⟩, fun b h hb dA dD h1 h2 => ?_⟩` and prove the remaining obligations. Use `congrFun (pRam'_equiv (ν := ν) (α := α) Ψ u) h` as an intermediate fact. Rewrite `this` using `[hinv u hu]`.

Conclude with `this.symm`. Take `⟨C, hC, hY⟩` from `exists_lowerProjection_conj hb h2`. Establish `h3` using `smallF_mul_left (haarVol (KO k (Fin a'))) ν Ψ C (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)`. Rewrite `h3` using `[← Matrix.mul_assoc, ← hY, hC, Matrix.mul_assoc, ← Units.val_mul]`. Establish `h5 : apow dD (-(a : ℂ) / 2) * apow dD ((Fintype.card (Fin (a + a')) : ℂ) / 2) = apow dD ((a' : ℂ) / 2)`.

Rewrite using `[← apow_add]`. Use `congr 1`. Simplify using `only [Fintype.card_fin, Nat.cast_add]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [pRam', smallP, indFac]`.

Rewrite using `[← h3, gdet_mul, gdet_block hb h1 h2, Fintype.card_fin a']`. Simplify using `only [map_mul, apow_mul, Units.val_mul, H.alpha_eq dD, ← h5]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pRam'_mem (H : HidaSetting a a' ϖ α β ν) {Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ}
    (hΨ : Ψ ∈ SB _) : pRam' a a' ν α Ψ ∈ indSp a a' α β := by
  obtain ⟨e', hα, -⟩ := H.cond
  obtain ⟨U, hU, hinv⟩ := exists_open_omB ν hα hΨ
  refine ⟨⟨U, hU, fun u hu h => ?_⟩, fun b h hb dA dD h1 h2 => ?_⟩
  · have := congrFun (pRam'_equiv (ν := ν) (α := α) Ψ u) h
    rw [hinv u hu] at this
    exact this.symm
  · obtain ⟨C, hC, hY⟩ := exists_lowerProjection_conj hb h2
    have h3 := smallF_mul_left (haarVol (KO k (Fin a'))) ν Ψ C (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)
    rw [← Matrix.mul_assoc, ← hY, hC, Matrix.mul_assoc, ← Units.val_mul] at h3
    have h5 : apow dD (-(a : ℂ) / 2) * apow dD ((Fintype.card (Fin (a + a')) : ℂ) / 2) = apow dD ((a' : ℂ) / 2) := by
      rw [← apow_add]; congr 1; simp only [Fintype.card_fin, Nat.cast_add]; ring
    simp only [pRam', smallP, indFac]
    rw [← h3, gdet_mul, gdet_block hb h1 h2, Fintype.card_fin a']
    simp only [map_mul, apow_mul, Units.val_mul, H.alpha_eq dD, ← h5]
    ring

/- English proof (translation)
Take `⟨e, he⟩` from `H.condν`. Use function extensionality and compare the values at `h`. Establish `h3` using `shellSum_mul_left (haarVol (KO k (Fin a))) H.unif hν he ((Fintype.card (Fin (a + a')) : ℂ) / 2) (comp_SB (upperProjection_right_inverse (invT h)) hΦ) g⁻¹`. Simplify using `only [pRam, bigZetaIntegral_eq, bigF]`. Use `congr 1`.

Rewrite using `[← h3, ← shellSum_smul]`. Use `congr 1`. Use function extensionality and compare the values at `X`. Simplify using `only [omA, map_one, map_inv, Units.val_one, apow_one, mul_one, Matrix.mul_one, apow_inv, Matrix.mul_assoc, neg_div]`.
-/
theorem pRam_inv (H : HidaSetting a a' ϖ α β ν) (hν : ¬ IsUnram ν) {Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ}
    (hΦ : Φ ∈ SB _) (g : GL (Fin a) k) : pRam a a' ϖ ν β (omA ν β g 1 Φ) = pRam a a' ϖ ν β Φ := by
  obtain ⟨e, he⟩ := H.condν
  funext h
  have h3 := shellSum_mul_left (haarVol (KO k (Fin a))) H.unif hν he ((Fintype.card (Fin (a + a')) : ℂ) / 2)
    (comp_SB (upperProjection_right_inverse (invT h)) hΦ) g⁻¹
  simp only [pRam, bigZetaIntegral_eq, bigF]
  congr 1
  rw [← h3, ← shellSum_smul]
  congr 1
  funext X
  simp only [omA, map_one, map_inv, Units.val_one, apow_one, mul_one, Matrix.mul_one, apow_inv, Matrix.mul_assoc,
    neg_div]

/- English proof (translation)
Use function extensionality and compare the values at `h`. Establish `h3` using `integral_mul_left_eq_self (μ := haarVol (KO k (Fin a'))) (zint ν ((Fintype.card (Fin (a + a')) : ℂ) / 2) fun X => Ψ (X * (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val))) (invT g)⁻¹`. Simplify using `only [pRam', smallP]`. Use `congr 1`. Use `Eq.trans ?_ h3` and prove the remaining obligations.

Unfold `smallF`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[← zint_left]`. Simplify using `only [zint, omB, invT_inv_val, map_inv, gdet_invT, inv_inv, map_one, Units.val_one, apow_one, mul_one, Matrix.mul_one, Matrix.mul_assoc]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pRam'_inv (Ψ : Matrix (Fin a') (Fin (a + a')) k → ℂ) (g : GL (Fin a') k) :
    pRam' a a' ν α (omB ν α g 1 Ψ) = pRam' a a' ν α Ψ := by
  funext h
  have h3 := integral_mul_left_eq_self (μ := haarVol (KO k (Fin a'))) (zint ν ((Fintype.card (Fin (a + a')) : ℂ) / 2)
    fun X => Ψ (X * (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val))) (invT g)⁻¹
  simp only [pRam', smallP]
  congr 1
  refine Eq.trans ?_ h3
  unfold smallF
  congr 1
  funext x
  rw [← zint_left]
  simp only [zint, omB, invT_inv_val, map_inv, gdet_invT, inv_inv, map_one, Units.val_one, apow_one, mul_one,
    Matrix.mul_one, Matrix.mul_assoc]
  ring

/- English proof (translation)
Take `⟨e, he⟩` from `H.condν`. Take `⟨Φ, hΦ, h0, h1⟩` from `exists_bump (haarVol (KO k (Fin a))) he ((Fintype.card (Fin (a + a')) : ℂ) / 2) (upperProjection_right_inverse (a' := a') (invT 1))`. Use `⟨Φ, hΦ, fun h => h1 ?_⟩` and prove the remaining obligations. Use `congrFun h 1` as an intermediate fact. Rewrite `this` using `[pRam, bigZetaIntegral_eq, bigF, shellSum_of_KO _ H.unif he _ (comp_SB (upperProjection_right_inverse _) hΦ) h0, Pi.zero_apply]`.

Conclude with `(mul_eq_zero.1 this).resolve_left (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _))`.
-/
theorem pRam_ne_zero (H : HidaSetting a a' ϖ α β ν) : ∃ Φ ∈ SB _, pRam a a' ϖ ν β Φ ≠ 0 := by
  obtain ⟨e, he⟩ := H.condν
  obtain ⟨Φ, hΦ, h0, h1⟩ := exists_bump (haarVol (KO k (Fin a))) he ((Fintype.card (Fin (a + a')) : ℂ) / 2)
    (upperProjection_right_inverse (a' := a') (invT 1))
  refine ⟨Φ, hΦ, fun h => h1 ?_⟩
  have := congrFun h 1
  rw [pRam, bigZetaIntegral_eq, bigF, shellSum_of_KO _ H.unif he _ (comp_SB (upperProjection_right_inverse _) hΦ) h0, Pi.zero_apply] at this
  exact (mul_eq_zero.1 this).resolve_left (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _))

/- English proof (translation)
Take `⟨e, he⟩` from `H.condν`. Take `⟨Ψ, hΨ, -, h1⟩` from `exists_bump (haarVol (KO k (Fin a'))) he ((Fintype.card (Fin (a + a')) : ℂ) / 2) (lowerProjection_right_inverse (a := a) 1)`. Use `⟨Ψ, hΨ, fun h => h1 ?_⟩` and prove the remaining obligations. Conclude with `(mul_eq_zero.1 (congrFun h 1)).resolve_left (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _))`.
-/
theorem pRam'_ne_zero (H : HidaSetting a a' ϖ α β ν) : ∃ Ψ ∈ SB _, pRam' a a' ν α Ψ ≠ 0 := by
  obtain ⟨e, he⟩ := H.condν
  obtain ⟨Ψ, hΨ, -, h1⟩ := exists_bump (haarVol (KO k (Fin a'))) he ((Fintype.card (Fin (a + a')) : ℂ) / 2)
    (lowerProjection_right_inverse (a := a) 1)
  refine ⟨Ψ, hΨ, fun h => h1 ?_⟩
  exact (mul_eq_zero.1 (congrFun h 1)).resolve_left (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _))

omit [MeasurableSpace k] [BorelSpace k] in
/- English proof (translation)
Establish `h0 : p 0 = 0`. Use `hadd 0 (zero_mem _) 0 (zero_mem _) 1` as an intermediate fact. Simplify using `using this`. Set `N : Submodule ℂ (GL (Fin (a + a')) k → ℂ)` to `{ carrier := {F | ∃ Φ ∈ SB X, p Φ = F} add_mem' := by`. Introduce and unpack `_ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩`.

Conclude with `⟨Φ + Φ₁, add_mem hΦ hΦ₁, by simpa using hadd Φ hΦ Φ₁ hΦ₁ 1⟩`. Use the proof step `zero_mem' := ⟨0, zero_mem _, h0⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c _ ⟨Φ, hΦ, rfl⟩`. Conclude with `⟨c • Φ, (SB X).smul_mem c hΦ, by simpa [h0] using hadd 0 (zero_mem _) Φ hΦ c⟩ }`.

Break down `hI k a a' α β H.unitα H.unitβ N (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hmem Φ hΦ) (by rintro h₁ _ ⟨Φ, hΦ, rfl⟩; exact heq Φ hΦ h₁) with h | h` into its components or cases. Take `⟨Φ, hΦ, hne⟩` from `hne`. Conclude with `absurd ((Submodule.eq_bot_iff N).1 h _ ⟨Φ, hΦ, rfl⟩) hne`. Introduce `F hF`. Rewrite `hF` using `[← h]`.

Conclude with `hF`.
-/
theorem onto_of_irred (hI : IndIrred) (H : HidaSetting a a' ϖ α β ν) {X : Type} [TopologicalSpace X]
    (p : (X → ℂ) → GL (Fin (a + a')) k → ℂ)
    (hadd : ∀ Φ ∈ SB X, ∀ Φ₁ ∈ SB X, ∀ c : ℂ, p (Φ + c • Φ₁) = p Φ + c • p Φ₁) (hmem : ∀ Φ ∈ SB X, p Φ ∈ indSp a a' α β)
    (heq : ∀ Φ ∈ SB X, ∀ h₁, ∃ Φ' ∈ SB X, p Φ' = rtr h₁ (p Φ)) (hne : ∃ Φ ∈ SB X, p Φ ≠ 0) :
    ∀ F ∈ indSp a a' α β, ∃ Φ ∈ SB X, p Φ = F := by
  have h0 : p 0 = 0 := by
    have := hadd 0 (zero_mem _) 0 (zero_mem _) 1
    simpa using this
  let N : Submodule ℂ (GL (Fin (a + a')) k → ℂ) :=
    { carrier := {F | ∃ Φ ∈ SB X, p Φ = F}
      add_mem' := by
        rintro _ _ ⟨Φ, hΦ, rfl⟩ ⟨Φ₁, hΦ₁, rfl⟩
        exact ⟨Φ + Φ₁, add_mem hΦ hΦ₁, by simpa using hadd Φ hΦ Φ₁ hΦ₁ 1⟩
      zero_mem' := ⟨0, zero_mem _, h0⟩
      smul_mem' := by
        rintro c _ ⟨Φ, hΦ, rfl⟩
        exact ⟨c • Φ, (SB X).smul_mem c hΦ, by simpa [h0] using hadd 0 (zero_mem _) Φ hΦ c⟩ }
  rcases hI k a a' α β H.unitα H.unitβ N (by rintro _ ⟨Φ, hΦ, rfl⟩; exact hmem Φ hΦ)
    (by rintro h₁ _ ⟨Φ, hΦ, rfl⟩; exact heq Φ hΦ h₁) with h | h
  · obtain ⟨Φ, hΦ, hne⟩ := hne
    exact absurd ((Submodule.eq_bot_iff N).1 h _ ⟨Φ, hΦ, rfl⟩) hne
  · intro F hF
    rw [← h] at hF
    exact hF

end Maps

/- English proof (translation)
Introduce `k _ _ _ _ _ _ a a' ϖ α β ν H hν`. Conclude with `⟨fun _ h _ h₁ c => pRam_add H hν h h₁ c, fun _ h _ h₁ c => pRam'_add H h h₁ c, fun _ h => pRam_mem H hν h, fun _ h => pRam'_mem H h, fun _ h g => pRam_inv H hν h g, fun Ψ _ g => pRam'_inv Ψ g, fun Φ _ h => pRam_equiv Φ h, fun Ψ _ h => pRam'_equiv Ψ h, onto_of_irred hI H _ (fun _ …`.
-/
theorem ramMaps_of (hI : IndIrred) : RamMaps := by
  intro k _ _ _ _ _ _ a a' ϖ α β ν H hν
  exact ⟨fun _ h _ h₁ c => pRam_add H hν h h₁ c, fun _ h _ h₁ c => pRam'_add H h h₁ c, fun _ h => pRam_mem H hν h,
    fun _ h => pRam'_mem H h, fun _ h g => pRam_inv H hν h g, fun Ψ _ g => pRam'_inv Ψ g, fun Φ _ h => pRam_equiv Φ h,
    fun Ψ _ h => pRam'_equiv Ψ h,
    onto_of_irred hI H _ (fun _ h _ h₁ c => pRam_add H hν h h₁ c) (fun _ h => pRam_mem H hν h)
      (fun Φ h h₁ => ⟨_, omA_mem_SB ν β 1 h₁ h, pRam_equiv Φ h₁⟩) (pRam_ne_zero H),
    onto_of_irred hI H _ (fun _ h _ h₁ c => pRam'_add H h h₁ c) (fun _ h => pRam'_mem H h)
      (fun Ψ h h₁ => ⟨_, omB_mem_SB ν α 1 h₁ h, pRam'_equiv Ψ h₁⟩) (pRam'_ne_zero H)⟩

end PositivityTheory.ThK.SplitLoc

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ _ H _` and use `PositivityTheory.ThK.SplitLoc.pRam_ne_zero H`.
-/
theorem PositivityTheory.ThK.SplitDict.ramified_map_ne_zero : PositivityTheory.ThK.SplitDict.RamNonzero :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ H _ => PositivityTheory.ThK.SplitLoc.pRam_ne_zero H
