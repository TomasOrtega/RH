import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG GlobalTheory.GLDoubling
open scoped NNReal Pointwise

namespace GlobalTheory.GLDoubling.Model

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `ho : IsOpen (KO k (Fin n) : Set (GL (Fin n) k))` using `SplitFlip.isOpen_KO`. Establish `hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k))` using `SplitFlip.isCompact_KO`. Set `K : TopologicalSpace.PositiveCompacts (GL (Fin n) k)` to `⟨⟨_, hc⟩, by`. Rewrite using `[show interior ((⟨_, hc⟩ : TopologicalSpace.Compacts (GL (Fin n) k)).carrier) = _ from ho.interior_eq]`. Conclude with `⟨1, one_mem _⟩⟩`.

Conclude with `⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩`.
-/
theorem exists_haar (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)] :
    ∃ μ : Measure (GL (Fin n) k), μ.IsHaarMeasure ∧ μ (KO k (Fin n)) = 1 := by
  have ho : IsOpen (KO k (Fin n) : Set (GL (Fin n) k)) := SplitFlip.isOpen_KO
  have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := SplitFlip.isCompact_KO
  let K : TopologicalSpace.PositiveCompacts (GL (Fin n) k) := ⟨⟨_, hc⟩, by
    rw [show interior ((⟨_, hc⟩ : TopologicalSpace.Compacts (GL (Fin n) k)).carrier) = _ from ho.interior_eq]
    exact ⟨1, one_mem _⟩⟩
  exact ⟨Measure.haarMeasure K, inferInstance, Measure.haarMeasure_self⟩

/- English proof (translation)
Establish `s1` using `hasSum_geometric_of_norm_lt_one h1`. Establish `s2` using `(hasSum_geometric_of_norm_lt_one h2).mul_left (a⁻¹ * Y)`. Establish `n1 : 1 - a * Y ≠ 0` using `sub_ne_zero.2 fun h => by rw [← h] at h1; simp at h1`. Establish `n2 : 1 - a⁻¹ * Y ≠ 0` using `sub_ne_zero.2 fun h => by rw [← h] at h2; simp at h2`. Establish `t1 : (fun m : ℕ => Y ^ |(m : ℤ)| * a ^ (m : ℤ)) = fun m => (a * Y) ^ m` using `funext fun m => by`.

Simplify using `[mul_pow, mul_comm]`. Establish `t2 : (fun m : ℕ => Y ^ |-((m : ℤ) + 1)| * a ^ (-((m : ℤ) + 1))) = fun m => a⁻¹ * Y * (a⁻¹ * Y) ^ m`. Use function extensionality and compare the values at `fun m => by`. Rewrite using `[abs_neg, abs_of_nonneg (by positivity), ← pow_succ', mul_pow, _root_.zpow_neg, inv_pow, mul_comm]`. Use `norm_cast`.

Use `HasSum.of_nat_of_neg_add_one (f := fun e : ℤ => Y ^ |e| * a ^ e) (t1 ▸ s1) (t2 ▸ s2)` as an intermediate fact. Establish `hb : a * a⁻¹ = 1` using `mul_inv_cancel₀ ha`. Establish `e : (1 - a * Y)⁻¹ * (1 - a⁻¹ * Y)⁻¹ * (1 - Y ^ 2) = (1 - a * Y)⁻¹ + a⁻¹ * Y * (1 - a⁻¹ * Y)⁻¹`. Establish `i1` using `mul_inv_cancel₀ n1`. Establish `i2` using `mul_inv_cancel₀ n2`.

Generalize the expression as in `(1 - a * Y)⁻¹ = u at *`. Generalize the expression as in `(1 - a⁻¹ * Y)⁻¹ = w at *`. Generalize the expression as in `a⁻¹ = b at *`. Take the linear combination `u * i2 + b * Y * w * i1 + u * w * Y ^ 2 * hb`. Rewrite using `[e]`.

Conclude with `this`.
-/
theorem hasSum_bilateral {a Y : ℂ} (ha : a ≠ 0) (h1 : ‖a * Y‖ < 1) (h2 : ‖a⁻¹ * Y‖ < 1) :
    HasSum (fun e : ℤ => Y ^ |e| * a ^ e) ((1 - a * Y)⁻¹ * (1 - a⁻¹ * Y)⁻¹ * (1 - Y ^ 2)) := by
  have s1 := hasSum_geometric_of_norm_lt_one h1
  have s2 := (hasSum_geometric_of_norm_lt_one h2).mul_left (a⁻¹ * Y)
  have n1 : 1 - a * Y ≠ 0 := sub_ne_zero.2 fun h => by rw [← h] at h1; simp at h1
  have n2 : 1 - a⁻¹ * Y ≠ 0 := sub_ne_zero.2 fun h => by rw [← h] at h2; simp at h2
  have t1 : (fun m : ℕ => Y ^ |(m : ℤ)| * a ^ (m : ℤ)) = fun m => (a * Y) ^ m := funext fun m => by
    simp [mul_pow, mul_comm]
  have t2 : (fun m : ℕ => Y ^ |-((m : ℤ) + 1)| * a ^ (-((m : ℤ) + 1))) = fun m => a⁻¹ * Y * (a⁻¹ * Y) ^ m :=
    funext fun m => by
      rw [abs_neg, abs_of_nonneg (by positivity), ← pow_succ', mul_pow, _root_.zpow_neg, inv_pow, mul_comm]
      norm_cast
  have := HasSum.of_nat_of_neg_add_one (f := fun e : ℤ => Y ^ |e| * a ^ e) (t1 ▸ s1) (t2 ▸ s2)
  have hb : a * a⁻¹ = 1 := mul_inv_cancel₀ ha
  have e : (1 - a * Y)⁻¹ * (1 - a⁻¹ * Y)⁻¹ * (1 - Y ^ 2) =
      (1 - a * Y)⁻¹ + a⁻¹ * Y * (1 - a⁻¹ * Y)⁻¹ := by
    have i1 := mul_inv_cancel₀ n1
    have i2 := mul_inv_cancel₀ n2
    generalize (1 - a * Y)⁻¹ = u at *
    generalize (1 - a⁻¹ * Y)⁻¹ = w at *
    generalize a⁻¹ = b at *
    linear_combination u * i2 + b * Y * w * i1 + u * w * Y ^ 2 * hb
  rw [e]
  exact this

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use `GlobalTheory.SmGL.Model.scalar_of_isSubquotient ha.2.2 (fun f => ?_) v` and prove the remaining obligations. Use extensionality with `x`. Establish `h1` using `parInd_law (points (Fin 1)) _ f ⟨_, leviEmb_mem_parab k _ (leviTorus k _ fun _ => y)⟩ x`. Rewrite `h1` using `[leviProj_leviEmb]`. Establish `hc : x * (diagT k (Fin 1) fun _ => y) = (diagT k (Fin 1) fun _ => y) * x`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0]`. Use `show f.1.1 (x * (diagT k (Fin 1) fun _ => y)) = (unrChar k (a 0) y : ℂ) • f.1.1 x`. Rewrite using `[hc]`. Use `h1.trans ?_` and prove the remaining obligations.

Establish `hm : modExp (fun _ : Fin 1 => Unit) 0 = 0` using `by rw [modExp_fin _ (fun _ => by simp)]; simp`. Simplify using `[deltaHalf_apply, hm]`.
-/
theorem act_one {π : Representation ℂ (GL (Fin 1) k) V} {a : Fin 1 → ℂˣ} (ha : HasSatake π a) (y : kˣ) (v : V) :
    π (diagT k (Fin 1) fun _ => y) v = (unrChar k (a 0) y : ℂ) • v := by
  refine GlobalTheory.SmGL.Model.scalar_of_isSubquotient ha.2.2 (fun f => ?_) v
  ext x
  have h1 := parInd_law (points (Fin 1)) _ f ⟨_, leviEmb_mem_parab k _ (leviTorus k _ fun _ => y)⟩ x
  rw [leviProj_leviEmb] at h1
  have hc : x * (diagT k (Fin 1) fun _ => y) = (diagT k (Fin 1) fun _ => y) * x := by
    ext i j
    simp [Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0]
  show f.1.1 (x * (diagT k (Fin 1) fun _ => y)) = (unrChar k (a 0) y : ℂ) • f.1.1 x
  rw [hc]
  refine h1.trans ?_
  have hm : modExp (fun _ : Fin 1 => Unit) 0 = 0 := by rw [modExp_fin _ (fun _ => by simp)]; simp
  simp [deltaHalf_apply, hm]

/- English proof (translation)
Take `⟨x, hx⟩` from `valuation_surjective (uniformizer k)`. Conclude with `⟨Units.mk0 x (by rintro rfl; simp at hx; exact uniformizer_ne_zero hx.symm), hx⟩`.
-/
theorem exists_unif : ∃ ϖ : kˣ, valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
  exact ⟨Units.mk0 x (by rintro rfl; simp at hx; exact uniformizer_ne_zero hx.symm), hx⟩

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `exists_unif (k := k)`. Establish `hq1 : (1 : ℝ) < resCard k` using `by exact_mod_cast one_lt_resCard k`. Establish `hq0 : 0 < resCard k` using `zero_lt_one.trans (one_lt_resCard k)`. Establish `hqc : (resCard k : ℂ) ≠ 0` using `by exact_mod_cast hq0.ne'`. Use `set M : ℝ := max ‖(α 0 : ℂ)‖ ‖(α 0 : ℂ)⁻¹‖ with hM`.

Establish `hM0 : 0 < M` using `lt_max_of_lt_left (norm_pos_iff.2 (α 0).ne_zero)`. Use `⟨Real.logb (resCard k) M, fun s hs => ?_⟩` and prove the remaining obligations. Use `set Y : ℂ := (resCard k : ℂ) ^ (-(s + 1 / 2)) with hY`. Establish `hMY : M * ‖Y‖ < 1`. Rewrite using `[hY, Complex.norm_natCast_cpow_of_pos hq0]`.

Establish `: M < (resCard k : ℝ) ^ (s.re + 1 / 2)`. Rewrite using `[← Real.logb_lt_iff_lt_rpow hq1 hM0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : (-(s + 1 / 2)).re = -(s.re + 1 / 2)` using `by simp`. Rewrite using `[e, Real.rpow_neg (by positivity), mul_inv_lt_iff₀ (by positivity), one_mul]`.

Conclude with `this`. Establish `h1 : ‖(α 0 : ℂ) * Y‖ < 1`. Rewrite using `[norm_mul]; exact lt_of_le_of_lt (by gcongr; exact le_max_left _ _) hMY`. Establish `h2 : ‖(α 0 : ℂ)⁻¹ * Y‖ < 1`. Rewrite using `[norm_mul]; exact lt_of_le_of_lt (by gcongr; exact le_max_right _ _) hMY`.

Establish `hS` using `hasSum_bilateral (α 0).ne_zero h1 h2`. Set `E : {e : Fin 1 → ℤ // Antitone e} ≃ ℤ` to `{ toFun := fun e => e.1 0 invFun := fun m => ⟨fun _ => m, antitone_const⟩ left_inv := fun e => by ext i; simp [Subsingleton.elim i 0] right_inv := fun _ => rfl }`. Use `set f : GL (Fin 1) k → ℂ := fun g => sphSection k (Fin 1) s (io k (Fin 1) (g, 1)) * ω g with hf`. Establish `hb : ∀ g, ∀ x ∈ KO k (Fin 1), ∀ y ∈ KO k (Fin 1), f (x * g * y) = f g` using `fun g x hx y hy => by`. Simplify using `only [hf]`.

Rewrite using `[sphSection_io_biinv s g hx hy, zonal_biinv hω g hx hy]`. Establish `hval : ∀ e : Fin 1 → ℤ, f (torusElt k (Fin 1) ϖ e) = Y ^ |e 0| * (α 0 : ℂ) ^ e 0` using `fun e => by`. Simplify using `only [hf]`. Rewrite using `[sphSection_torusElt hϖ]`. Take `⟨v, -, l, -, hl, hω⟩` from `hω`.

Establish `e1 : torusElt k (Fin 1) ϖ e = diagT k (Fin 1) fun _ => ϖ ^ e 0`. Unfold `torusElt`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Subsingleton.elim i 0]`.

Rewrite using `[hω, e1, act_one hπ, map_smul, hl, map_zpow, unrChar_uniformizer k _ hϖ, hY, ← Complex.cpow_mul_int]`. Simplify using `[add_comm]`. Establish `hvol : ∀ e : Fin 1 → ℤ, μ (cell k (Fin 1) ϖ e) = 1` using `fun e => by`. Establish `: cell k (Fin 1) ϖ e = torusElt k (Fin 1) ϖ e • (KO k (Fin 1) : Set (GL (Fin 1) k))`. Use extensionality with `g`.

Rewrite using `[cell, DoubleCoset.mem_doubleCoset]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, y, hy, rfl⟩`. Use `⟨x * y, mul_mem hx hy, ?_⟩` and prove the remaining obligations. Establish `hc : x * torusElt k (Fin 1) ϖ e = torusElt k (Fin 1) ϖ e * x`.

Use extensionality with `i j`. Simplify using `[Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0]`. Use `show torusElt k (Fin 1) ϖ e * (x * y) = _`. Rewrite using `[hc, mul_assoc]`. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨1, one_mem _, y, hy, by simp⟩`. Rewrite using `[this, measure_smul, hμ]`. Establish `hconst : ∀ e : Fin 1 → ℤ, Set.EqOn f (fun _ => f (torusElt k (Fin 1) ϖ e)) (cell k (Fin 1) ϖ e)` using `fun e g hg => by`. Take `⟨x, hx, y, hy, rfl⟩` from `DoubleCoset.mem_doubleCoset.1 hg`. Conclude with `hb _ x hx y hy`.

Establish `hint : Integrable f μ`. Rewrite using `[← integrableOn_univ, ← iUnion_cell hϖ]`. Use `integrableOn_iUnion_of_summable_integral_norm (fun e => ?_) ?_` and prove the remaining obligations. Conclude with `(integrableOn_const (by simp [hvol])).congr_fun (hconst e.1).symm (isOpen_cell ϖ e.1).measurableSet`. Use `((E.summable_iff (f := fun m : ℤ => ‖Y ^ |m| * (α 0 : ℂ) ^ m‖)).2 hS.summable.norm).congr fun e => ?_` and prove the remaining obligations.

Rewrite using `[setIntegral_congr_fun (isOpen_cell ϖ e.1).measurableSet (g := fun _ => ‖f (torusElt k (Fin 1) ϖ e)‖) fun g hg => congrArg norm (hconst e.1 hg)]`. Simplify using `[Measure.real, hvol, hval, E]`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Establish `h3` using `hasSum_cell μ hϖ hint hb`. Simplify using `only [Measure.real, hvol, hval, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at h3`.

Rewrite using `[h3.unique ((E.hasSum_iff (f := fun m : ℤ => Y ^ |m| * (α 0 : ℂ) ^ m)).2 hS)]`. Establish `hY2 : Y ^ 2 = (resCard k : ℂ) ^ (-(2 * s + 1))`. Rewrite using `[hY, ← Complex.cpow_mul_nat]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hY2]`. Simplify using `only [lFactor, invNormFactor, Finset.Icc_self, Finset.prod_singleton, Fin.prod_univ_one, Pi.inv_apply, Units.val_inv_eq_inv_val, Nat.cast_one, ← hY]`.
-/
theorem rank_one [MeasurableSpace (GL (Fin 1) k)] [BorelSpace (GL (Fin 1) k)]
    (μ : Measure (GL (Fin 1) k)) [μ.IsHaarMeasure] (hμ : μ (KO k (Fin 1)) = 1)
    (π : Representation ℂ (GL (Fin 1) k) V) (α : Fin 1 → ℂˣ) (hπ : HasSatake π α)
    (ω : GL (Fin 1) k → ℂ) (hω : IsZonal π (KO k (Fin 1)) ω) :
    ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      Integrable (fun g => sphSection k (Fin 1) s (io k (Fin 1) (g, 1)) * ω g) μ ∧
      ∫ g, sphSection k (Fin 1) s (io k (Fin 1) (g, 1)) * ω g ∂μ =
        lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) *
          invNormFactor (resCard k) 1 s := by
  obtain ⟨ϖ, hϖ⟩ := exists_unif (k := k)
  have hq1 : (1 : ℝ) < resCard k := by exact_mod_cast one_lt_resCard k
  have hq0 : 0 < resCard k := zero_lt_one.trans (one_lt_resCard k)
  have hqc : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  set M : ℝ := max ‖(α 0 : ℂ)‖ ‖(α 0 : ℂ)⁻¹‖ with hM
  have hM0 : 0 < M := lt_max_of_lt_left (norm_pos_iff.2 (α 0).ne_zero)
  refine ⟨Real.logb (resCard k) M, fun s hs => ?_⟩
  set Y : ℂ := (resCard k : ℂ) ^ (-(s + 1 / 2)) with hY
  have hMY : M * ‖Y‖ < 1 := by
    rw [hY, Complex.norm_natCast_cpow_of_pos hq0]
    have : M < (resCard k : ℝ) ^ (s.re + 1 / 2) := by
      rw [← Real.logb_lt_iff_lt_rpow hq1 hM0]; linarith
    have e : (-(s + 1 / 2)).re = -(s.re + 1 / 2) := by simp
    rw [e, Real.rpow_neg (by positivity), mul_inv_lt_iff₀ (by positivity), one_mul]
    exact this
  have h1 : ‖(α 0 : ℂ) * Y‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (by gcongr; exact le_max_left _ _) hMY
  have h2 : ‖(α 0 : ℂ)⁻¹ * Y‖ < 1 := by
    rw [norm_mul]; exact lt_of_le_of_lt (by gcongr; exact le_max_right _ _) hMY
  have hS := hasSum_bilateral (α 0).ne_zero h1 h2
  let E : {e : Fin 1 → ℤ // Antitone e} ≃ ℤ :=
    { toFun := fun e => e.1 0
      invFun := fun m => ⟨fun _ => m, antitone_const⟩
      left_inv := fun e => by ext i; simp [Subsingleton.elim i 0]
      right_inv := fun _ => rfl }
  set f : GL (Fin 1) k → ℂ := fun g => sphSection k (Fin 1) s (io k (Fin 1) (g, 1)) * ω g with hf
  have hb : ∀ g, ∀ x ∈ KO k (Fin 1), ∀ y ∈ KO k (Fin 1), f (x * g * y) = f g := fun g x hx y hy => by
    simp only [hf]
    rw [sphSection_io_biinv s g hx hy, zonal_biinv hω g hx hy]
  have hval : ∀ e : Fin 1 → ℤ, f (torusElt k (Fin 1) ϖ e) = Y ^ |e 0| * (α 0 : ℂ) ^ e 0 := fun e => by
    simp only [hf]
    rw [sphSection_torusElt hϖ]
    obtain ⟨v, -, l, -, hl, hω⟩ := hω
    have e1 : torusElt k (Fin 1) ϖ e = diagT k (Fin 1) fun _ => ϖ ^ e 0 := by
      unfold torusElt; congr 1; funext i; rw [Subsingleton.elim i 0]
    rw [hω, e1, act_one hπ, map_smul, hl, map_zpow, unrChar_uniformizer k _ hϖ, hY, ← Complex.cpow_mul_int]
    simp [add_comm]
  have hvol : ∀ e : Fin 1 → ℤ, μ (cell k (Fin 1) ϖ e) = 1 := fun e => by
    have : cell k (Fin 1) ϖ e = torusElt k (Fin 1) ϖ e • (KO k (Fin 1) : Set (GL (Fin 1) k)) := by
      ext g
      rw [cell, DoubleCoset.mem_doubleCoset]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        refine ⟨x * y, mul_mem hx hy, ?_⟩
        have hc : x * torusElt k (Fin 1) ϖ e = torusElt k (Fin 1) ϖ e * x := by
          ext i j
          simp [Matrix.mul_apply, mul_comm, Subsingleton.elim i 0, Subsingleton.elim j 0]
        show torusElt k (Fin 1) ϖ e * (x * y) = _
        rw [hc, mul_assoc]
      · rintro ⟨y, hy, rfl⟩
        exact ⟨1, one_mem _, y, hy, by simp⟩
    rw [this, measure_smul, hμ]
  have hconst : ∀ e : Fin 1 → ℤ, Set.EqOn f (fun _ => f (torusElt k (Fin 1) ϖ e)) (cell k (Fin 1) ϖ e) :=
    fun e g hg => by
      obtain ⟨x, hx, y, hy, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
      exact hb _ x hx y hy
  have hint : Integrable f μ := by
    rw [← integrableOn_univ, ← iUnion_cell hϖ]
    refine integrableOn_iUnion_of_summable_integral_norm (fun e => ?_) ?_
    · exact (integrableOn_const (by simp [hvol])).congr_fun (hconst e.1).symm (isOpen_cell ϖ e.1).measurableSet
    · refine ((E.summable_iff (f := fun m : ℤ => ‖Y ^ |m| * (α 0 : ℂ) ^ m‖)).2 hS.summable.norm).congr
        fun e => ?_
      rw [setIntegral_congr_fun (isOpen_cell ϖ e.1).measurableSet
        (g := fun _ => ‖f (torusElt k (Fin 1) ϖ e)‖) fun g hg => congrArg norm (hconst e.1 hg)]
      simp [Measure.real, hvol, hval, E]
  refine ⟨hint, ?_⟩
  have h3 := hasSum_cell μ hϖ hint hb
  simp only [Measure.real, hvol, hval, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at h3
  rw [h3.unique ((E.hasSum_iff (f := fun m : ℤ => Y ^ |m| * (α 0 : ℂ) ^ m)).2 hS)]
  have hY2 : Y ^ 2 = (resCard k : ℂ) ^ (-(2 * s + 1)) := by
    rw [hY, ← Complex.cpow_mul_nat]; congr 1; push_cast; ring
  rw [hY2]
  simp only [lFactor, invNormFactor, Finset.Icc_self, Finset.prod_singleton, Fin.prod_univ_one, Pi.inv_apply,
    Units.val_inv_eq_inv_val, Nat.cast_one, ← hY]

/- English proof (translation)
Establish `hs : ∀ g : GL (Fin 0) k, g = 1` using `fun g => by ext i; exact i.elim0`. Establish `hu : (KO k (Fin 0) : Set (GL (Fin 0) k)) = Set.univ` using `Set.eq_univ_of_forall fun g => by rw [hs g]; exact one_mem _`. Rewrite `hμ` using `[hu]`. Use `haveI : IsProbabilityMeasure μ := ⟨hμ⟩`. Take `⟨v, -, l, -, hl, hω⟩` from `hω`.

Establish `: (fun g => sphSection k (Fin 0) s (io k (Fin 0) (g, 1)) * ω g) = fun _ => 1` using `funext fun g => by`. Rewrite using `[hs g, hω, show ((1 : GL (Fin 0) k), (1 : GL (Fin 0) k)) = 1 from rfl, map_one, sphSection_one]`. Simplify using `using hl`. Rewrite using `[this]`. Simplify using `[lFactor, invNormFactor]`.
-/
theorem rank_zero [MeasurableSpace (GL (Fin 0) k)] [BorelSpace (GL (Fin 0) k)]
    (μ : Measure (GL (Fin 0) k)) [μ.IsHaarMeasure] (hμ : μ (KO k (Fin 0)) = 1)
    (π : Representation ℂ (GL (Fin 0) k) V) (α : Fin 0 → ℂˣ)
    (ω : GL (Fin 0) k → ℂ) (hω : IsZonal π (KO k (Fin 0)) ω) (s : ℂ) :
      Integrable (fun g => sphSection k (Fin 0) s (io k (Fin 0) (g, 1)) * ω g) μ ∧
      ∫ g, sphSection k (Fin 0) s (io k (Fin 0) (g, 1)) * ω g ∂μ =
        lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) *
          invNormFactor (resCard k) 0 s := by
  have hs : ∀ g : GL (Fin 0) k, g = 1 := fun g => by ext i; exact i.elim0
  have hu : (KO k (Fin 0) : Set (GL (Fin 0) k)) = Set.univ :=
    Set.eq_univ_of_forall fun g => by rw [hs g]; exact one_mem _
  rw [hu] at hμ
  haveI : IsProbabilityMeasure μ := ⟨hμ⟩
  obtain ⟨v, -, l, -, hl, hω⟩ := hω
  have : (fun g => sphSection k (Fin 0) s (io k (Fin 0) (g, 1)) * ω g) = fun _ => 1 := funext fun g => by
    rw [hs g, hω, show ((1 : GL (Fin 0) k), (1 : GL (Fin 0) k)) = 1 from rfl, map_one, sphSection_one]
    simpa using hl
  rw [this]
  simp [lFactor, invNormFactor]

end GlobalTheory.GLDoubling.Model
