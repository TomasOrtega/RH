import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TwoLe
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.ZK UpperTheory.V.ZK.Ct

section
open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace

open scoped Classical in

private noncomputable def extS (F : Type) [Field F] [NumberField F] :
    logSpace F →ₗ[ℝ] (InfinitePlace F → ℝ) where
  toFun y w := if h : w = w₀ then -(∑ v, y v) / 2 else y ⟨w, h⟩ / 2
  map_add' y z := by
    ext w
    by_cases h : w = w₀
    · simp only [h, dif_pos, Pi.add_apply, Finset.sum_add_distrib]; ring
    · simp only [h, dif_neg, not_false_eq_true, Pi.add_apply]; ring
  map_smul' c y := by
    ext w
    by_cases h : w = w₀
    · simp only [h, dif_pos, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]; ring
    · simp only [h, dif_neg, not_false_eq_true, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/- English proof (translation)
Rewrite using `[show mult w = 2 from mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩]`. Evaluate the numerical expressions.
-/
private theorem mult_two {F : Type} [Field F] [IsTotallyComplex F] (w : InfinitePlace F) :
    (mult w : ℝ) = 2 := by
  rw [show mult w = 2 from mult_isComplex ⟨w, IsTotallyComplex.isComplex w⟩]
  norm_num

/- English proof (translation)
Distinguish the cases in `h : w = w₀`. Substitute `h` using the available equality. Simplify using `only [extS, LinearMap.coe_mk, AddHom.coe_mk, dif_pos rfl, logEmbedding_component, mult_two, dite_true]`. Establish `hs` using `NumberField.Units.sum_mult_mul_log u`. Establish `e : (algebraMap (𝓞 F) F) (u : 𝓞 F) = ((u : 𝓞 F) : F)` using `rfl`.

Simplify using `only [mult_two, e] at hs`. Rewrite `hs` using `[Fintype.sum_eq_add_sum_subtype_ne _ w₀]`. Rewrite `hs`, the goal using `[← Finset.mul_sum]`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `only [extS, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h, logEmbedding_component, mult_two]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem extS_log {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] (u : (𝓞 F)ˣ)
    (w : InfinitePlace F) :
    extS F (logEmbedding F (Additive.ofMul u)) w = Real.log (w ((u : 𝓞 F) : F)) := by
  classical
  by_cases h : w = w₀
  · subst h
    simp only [extS, LinearMap.coe_mk, AddHom.coe_mk, dif_pos rfl, logEmbedding_component, mult_two, dite_true]
    have hs := NumberField.Units.sum_mult_mul_log u
    have e : (algebraMap (𝓞 F) F) (u : 𝓞 F) = ((u : 𝓞 F) : F) := rfl
    simp only [mult_two, e] at hs
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀] at hs
    rw [← Finset.mul_sum] at hs ⊢
    linarith
  · simp only [extS, LinearMap.coe_mk, AddHom.coe_mk, dif_neg h, logEmbedding_component, mult_two]
    ring

/- English proof (translation)
Establish `h` using `NumberField.Units.sum_mult_mul_log u`. Simplify using `only [mult_two, ← Finset.mul_sum, mul_eq_zero, two_ne_zero, false_or] at h`. Conclude with `h`.
-/
private theorem sum_log {F : Type} [Field F] [NumberField F] [IsTotallyComplex F] (u : (𝓞 F)ˣ) :
    ∑ w : InfinitePlace F, Real.log (w ((u : 𝓞 F) : F)) = 0 := by
  have h := NumberField.Units.sum_mult_mul_log u
  simp only [mult_two, ← Finset.mul_sum, mul_eq_zero, two_ne_zero, false_or] at h
  exact h

/- English proof (translation)
The claim follows from `|m| ≤ r := by have hN : (0 : ℝ) < Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos have hsum : ∑ w : InfinitePlace F, (Real.log (w ((u : 𝓞 F) : F)) + m) = Fintype.card (InfinitePlace F) * m := by rw [Finset.sum_add_distrib, sum_log, zero_add, Finset.sum_const, …`.
-/
private theorem abs_le_of_bound {F : Type} [Field F] [NumberField F] [IsTotallyComplex F]
    (u : (𝓞 F)ˣ) (m r : ℝ) (h : ∀ w : InfinitePlace F, |Real.log (w ((u : 𝓞 F) : F)) + m| ≤ r) :
    |m| ≤ r := by
  have hN : (0 : ℝ) < Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ w : InfinitePlace F, (Real.log (w ((u : 𝓞 F) : F)) + m)
      = Fintype.card (InfinitePlace F) * m := by
    rw [Finset.sum_add_distrib, sum_log, zero_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : |(Fintype.card (InfinitePlace F) : ℝ) * m| ≤ Fintype.card (InfinitePlace F) * r := by
    rw [← hsum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ w : InfinitePlace F, |Real.log (w ((u : 𝓞 F) : F)) + m|
        ≤ ∑ _w : InfinitePlace F, r := Finset.sum_le_sum (fun w _ => h w)
      _ = Fintype.card (InfinitePlace F) * r := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [abs_mul, abs_of_pos hN] at h1
  exact le_of_mul_le_mul_left h1 hN

/- English proof (translation)
Establish `hN : (0 : ℝ) < Fintype.card (InfinitePlace F)` using `by exact_mod_cast Fintype.card_pos`. Use `⟨fun w => 2 * (v w.1 - (∑ x, v x) / Fintype.card (InfinitePlace F)), (∑ x, v x) / Fintype.card (InfinitePlace F), ?_⟩` and prove the remaining obligations. Establish `hNc : (Fintype.card (InfinitePlace F) : ℝ) * ((∑ x, v x) / Fintype.card (InfinitePlace F)) = ∑ x, v x`. Clear the denominators using the available nonvanishing facts. Use function extensionality and compare the values at `w`.

Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, extS, LinearMap.coe_mk, AddHom.coe_mk]`. Use `split_ifs with h`. Substitute `h` using the available equality. Establish `h1` using `Fintype.sum_eq_add_sum_subtype_ne v w₀`. Establish `h2` using `Fintype.sum_eq_add_sum_subtype_ne (fun _ : InfinitePlace F => (∑ x, v x) / Fintype.card (InfinitePlace F)) w₀`.

Rewrite `h2` using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[← Finset.mul_sum, Finset.sum_sub_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem extS_surj {F : Type} [Field F] [NumberField F] (v : InfinitePlace F → ℝ) :
    ∃ (y : logSpace F) (c : ℝ), v = extS F y + c • (fun _ => (1 : ℝ)) := by
  classical
  have hN : (0 : ℝ) < Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
  refine ⟨fun w => 2 * (v w.1 - (∑ x, v x) / Fintype.card (InfinitePlace F)),
    (∑ x, v x) / Fintype.card (InfinitePlace F), ?_⟩
  have hNc : (Fintype.card (InfinitePlace F) : ℝ) * ((∑ x, v x) / Fintype.card (InfinitePlace F))
      = ∑ x, v x := by
    field_simp
  funext w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, extS, LinearMap.coe_mk,
    AddHom.coe_mk]
  split_ifs with h
  · subst h
    have h1 := Fintype.sum_eq_add_sum_subtype_ne v w₀
    have h2 := Fintype.sum_eq_add_sum_subtype_ne
      (fun _ : InfinitePlace F => (∑ x, v x) / Fintype.card (InfinitePlace F)) w₀
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    linarith
  · ring

end

/- English proof (translation)
Use `open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace in ( classical`. Introduce `F _ _ hF lam hlam`. Use `haveI := hF`. Establish `hlam' : ∀ (x : Additive (𝓞 F)ˣ) (m : ℤ), lam (x, m) = extS F (logEmbedding F x) + (m : ℝ) • (fun _ => (1 : ℝ))`. Introduce `x m`.

Use function extensionality and compare the values at `w`. Establish `h1` using `hlam (Additive.toMul x) m w`. Rewrite `h1` using `[ofMul_toMul]`. Rewrite using `[h1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, ← extS_log (Additive.toMul x) w, ofMul_toMul]`. Establish `hcomp : ∀ (x : Additive (𝓞 F)ˣ) (m : ℤ) (w : InfinitePlace F), lam (x, m) w = Real.log (w (((Additive.toMul x : (𝓞 F)ˣ) : 𝓞 F) : F)) + m`.

Introduce `x m w`. Establish `h1` using `hlam (Additive.toMul x) m w`. Rewrite `h1` using `[ofMul_toMul]`. Then use the resulting hypothesis. Establish `hm0 : ∀ (x : Additive (𝓞 F)ˣ) (m : ℤ) (r : ℝ), r < 1 → (∀ w, |lam (x, m) w| ≤ r) → m = 0`. Introduce `x m r hr h`.

Establish `hb` using `abs_le_of_bound (Additive.toMul x) (m : ℝ) r (fun w => by rw [← hcomp]; exact h w)`. Establish `: |m| < 1`. Establish `: ((|m| : ℤ) : ℝ) < 1` using `by rw [Int.cast_abs]; linarith`. Conclude with `this` after adjusting the coercions. Conclude with `Int.abs_lt_one_iff.mp this`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `⟨a, m⟩`. Rewrite using `[LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `hm : m = 0` using `hm0 a m 0 (by norm_num) (fun w => by rw [hx]; simp)`. Substitute `hm` using the available equality. Establish `hlog : logEmbedding F a = 0`. Use function extensionality and compare the values at `w`. Establish `h2` using `hcomp a 0 w.1`.

Rewrite `h2` using `[hx]`. Simplify using `only [Pi.zero_apply, Int.cast_zero, add_zero] at h2`. Establish `h3` using `logEmbedding_component (Additive.toMul a) w`. Rewrite `h3` using `[ofMul_toMul]`. Rewrite using `[h3, ← h2, mul_zero, Pi.zero_apply]`.

Establish `ht : Additive.toMul a ∈ torsion F`. Rewrite using `[← logEmbedding_eq_zero_iff, ofMul_toMul]`. Conclude with `hlog`. Take `⟨n, hn, hpow⟩` from `isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion _).mp ht)`. Establish `hne : (n : ℤ) ≠ 0` using `by exact_mod_cast hn.ne'`.

Use `(Submodule.mem_torsion_iff _).mpr ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero hne⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submonoid.smul_def]`. Use `show (n : ℤ) • (a, (0 : ℤ)) = 0`. Rewrite using `[Prod.smul_mk, Prod.mk_eq_zero]`. Use `⟨?_, by simp⟩` and prove the remaining obligations.

Apply `Additive.toMul.injective` to reduce the goal to its premises. Rewrite using `[toMul_zsmul, zpow_natCast, hpow, toMul_zero]`. Introduce `hx`. Take `⟨c, hc⟩` from `(Submodule.mem_torsion_iff _).mp hx`. Rewrite `hc` using `[Submonoid.smul_def]`.

Establish `h1` using `congrArg lam hc`. Rewrite `h1` using `[map_smul, map_zero]`. Conclude with `(smul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero c)`. Establish `hd : IsOpen ({0} : Set (unitLattice F))` using `isOpen_discrete _`. Take `⟨ε, hε, hεz⟩` from `(Metric.isOpen_singleton_iff (α := unitLattice F) (x := 0)).mp hd`.

Use `discreteTopology_of_isOpen_singleton_zero (Metric.isOpen_singleton_iff.mpr ⟨min (1 / 2) (ε / 2), by positivity, ?_⟩)` and prove the remaining obligations. Introduce and unpack `⟨_, ⟨⟨a, m⟩, rfl⟩⟩ hy`. Establish `hpos : (0 : ℝ) < min (1 / 2) (ε / 2)` using `by positivity`. Establish `hy' : ‖lam (a, m)‖ < min (1 / 2) (ε / 2)`. Rewrite using `[← dist_zero_right]`.

Conclude with `hy`. Establish `hw : ∀ w, |lam (a, m) w| < min (1 / 2) (ε / 2)`. Introduce `w`. Rewrite using `[← Real.norm_eq_abs]`. Conclude with `(pi_norm_lt_iff hpos).mp hy' w`.

Establish `hm : m = 0` using `hm0 a m (1 / 2) (by norm_num) (fun w => (hw w).le.trans (min_le_left _ _))`. Substitute `hm` using the available equality. Establish `hsmall : ∀ w : {w : InfinitePlace F // w ≠ w₀}, |logEmbedding F a w| < ε`. Introduce `w`. Establish `h3` using `logEmbedding_component (Additive.toMul a) w`.

Rewrite `h3` using `[ofMul_toMul]`. Establish `h4` using `hcomp a 0 w.1`. Simplify using `only [Int.cast_zero, add_zero] at h4`. Rewrite using `[h3, mult_two, ← h4, abs_mul]`. Use `(hw w.1).trans_le (min_le_right _ _)` as an intermediate fact.

Evaluate the numerical expressions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmem : logEmbedding F a ∈ unitLattice F` using `⟨a, Submodule.mem_top, rfl⟩`. Establish `hz` using `hεz ⟨logEmbedding F a, hmem⟩ (by`. Rewrite using `[dist_zero_right]`.

Conclude with `(pi_norm_lt_iff hε).mpr (fun w => by rw [Real.norm_eq_abs]; exact hsmall w))`. Establish `hlog : logEmbedding F a = 0` using `congrArg Subtype.val hz`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show lam (a, 0) = 0`. Rewrite using `[hlam', hlog, map_zero]`.

Simplify using the standard rewrite rules. Rewrite using `[eq_top_iff]`. Introduce `v _`. Take `⟨y, c, rfl⟩` from `extS_surj v`. Use `Submodule.add_mem _ ?_ (Submodule.smul_mem _ c (Submodule.subset_span ⟨(0, 1), ?_⟩))` and prove the remaining obligations.

Establish `hy : y ∈ Submodule.span ℝ (unitLattice F : Set (logSpace F))`. Rewrite using `[unitLattice_span_eq_top]`. Discharge the goal by the elementary cases of `trivial`. Establish `hle : Submodule.map (extS F) (Submodule.span ℝ (unitLattice F : Set (logSpace F))) ≤ Submodule.span ℝ (LinearMap.range lam : Set (InfinitePlace F → ℝ))`. Rewrite using `[Submodule.map_span]`.

Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨_, ⟨a, _, rfl⟩, rfl⟩`. Conclude with `⟨(a, 0), by rw [hlam']; simp⟩`. Conclude with `hle ⟨y, hy, rfl⟩`. Rewrite using `[hlam'] simp)`.
-/
theorem UpperTheory.V.ZK.Ct.unitLat :
    ∀ (F : Type) [Field F] [NumberField F], IsTotallyComplex F → ∀ lam : Additive (𝓞 F)ˣ × ℤ →ₗ[ℤ] (InfinitePlace F → ℝ), (∀ (u : (𝓞 F)ˣ) (m : ℤ) (w : InfinitePlace F), lam (Additive.ofMul u, m) w = Real.log (w ((u : 𝓞 F) : F)) + m) → LinearMap.ker lam = Submodule.torsion ℤ _ ∧ DiscreteTopology (LinearMap.range lam) ∧ Submodule.span ℝ (LinearMap.range lam : Set (InfinitePlace F → ℝ)) = ⊤ := by
  open NumberField.Units NumberField.Units.dirichletUnitTheorem NumberField.InfinitePlace in (
    classical
    intro F _ _ hF lam hlam
    haveI := hF
    have hlam' : ∀ (x : Additive (𝓞 F)ˣ) (m : ℤ),
        lam (x, m) = extS F (logEmbedding F x) + (m : ℝ) • (fun _ => (1 : ℝ)) := by
      intro x m
      funext w
      have h1 := hlam (Additive.toMul x) m w
      rw [ofMul_toMul] at h1
      rw [h1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one, ← extS_log (Additive.toMul x) w,
        ofMul_toMul]
    have hcomp : ∀ (x : Additive (𝓞 F)ˣ) (m : ℤ) (w : InfinitePlace F),
        lam (x, m) w = Real.log (w (((Additive.toMul x : (𝓞 F)ˣ) : 𝓞 F) : F)) + m := by
      intro x m w
      have h1 := hlam (Additive.toMul x) m w
      rwa [ofMul_toMul] at h1
    have hm0 : ∀ (x : Additive (𝓞 F)ˣ) (m : ℤ) (r : ℝ), r < 1 →
        (∀ w, |lam (x, m) w| ≤ r) → m = 0 := by
      intro x m r hr h
      have hb := abs_le_of_bound (Additive.toMul x) (m : ℝ) r (fun w => by rw [← hcomp]; exact h w)
      have : |m| < 1 := by
        have : ((|m| : ℤ) : ℝ) < 1 := by rw [Int.cast_abs]; linarith
        exact_mod_cast this
      exact Int.abs_lt_one_iff.mp this
    refine ⟨?_, ?_, ?_⟩
    · ext ⟨a, m⟩
      rw [LinearMap.mem_ker]
      constructor
      · intro hx
        have hm : m = 0 := hm0 a m 0 (by norm_num) (fun w => by rw [hx]; simp)
        subst hm
        have hlog : logEmbedding F a = 0 := by
          funext w
          have h2 := hcomp a 0 w.1
          rw [hx] at h2
          simp only [Pi.zero_apply, Int.cast_zero, add_zero] at h2
          have h3 := logEmbedding_component (Additive.toMul a) w
          rw [ofMul_toMul] at h3
          rw [h3, ← h2, mul_zero, Pi.zero_apply]
        have ht : Additive.toMul a ∈ torsion F := by
          rw [← logEmbedding_eq_zero_iff, ofMul_toMul]
          exact hlog
        obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp ((CommGroup.mem_torsion _).mp ht)
        have hne : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
        refine (Submodule.mem_torsion_iff _).mpr ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero hne⟩, ?_⟩
        rw [Submonoid.smul_def]
        show (n : ℤ) • (a, (0 : ℤ)) = 0
        rw [Prod.smul_mk, Prod.mk_eq_zero]
        refine ⟨?_, by simp⟩
        apply Additive.toMul.injective
        rw [toMul_zsmul, zpow_natCast, hpow, toMul_zero]
      · intro hx
        obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff _).mp hx
        rw [Submonoid.smul_def] at hc
        have h1 := congrArg lam hc
        rw [map_smul, map_zero] at h1
        exact (smul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero c)
    · have hd : IsOpen ({0} : Set (unitLattice F)) := isOpen_discrete _
      obtain ⟨ε, hε, hεz⟩ := (Metric.isOpen_singleton_iff (α := unitLattice F) (x := 0)).mp hd
      refine discreteTopology_of_isOpen_singleton_zero
        (Metric.isOpen_singleton_iff.mpr ⟨min (1 / 2) (ε / 2), by positivity, ?_⟩)
      rintro ⟨_, ⟨⟨a, m⟩, rfl⟩⟩ hy
      have hpos : (0 : ℝ) < min (1 / 2) (ε / 2) := by positivity
      have hy' : ‖lam (a, m)‖ < min (1 / 2) (ε / 2) := by
        rw [← dist_zero_right]
        exact hy
      have hw : ∀ w, |lam (a, m) w| < min (1 / 2) (ε / 2) := by
        intro w
        rw [← Real.norm_eq_abs]
        exact (pi_norm_lt_iff hpos).mp hy' w
      have hm : m = 0 := hm0 a m (1 / 2) (by norm_num)
        (fun w => (hw w).le.trans (min_le_left _ _))
      subst hm
      have hsmall : ∀ w : {w : InfinitePlace F // w ≠ w₀}, |logEmbedding F a w| < ε := by
        intro w
        have h3 := logEmbedding_component (Additive.toMul a) w
        rw [ofMul_toMul] at h3
        have h4 := hcomp a 0 w.1
        simp only [Int.cast_zero, add_zero] at h4
        rw [h3, mult_two, ← h4, abs_mul]
        have := (hw w.1).trans_le (min_le_right _ _)
        norm_num
        linarith
      have hmem : logEmbedding F a ∈ unitLattice F := ⟨a, Submodule.mem_top, rfl⟩
      have hz := hεz ⟨logEmbedding F a, hmem⟩ (by
        rw [dist_zero_right]
        exact (pi_norm_lt_iff hε).mpr (fun w => by rw [Real.norm_eq_abs]; exact hsmall w))
      have hlog : logEmbedding F a = 0 := congrArg Subtype.val hz
      apply Subtype.ext
      show lam (a, 0) = 0
      rw [hlam', hlog, map_zero]
      simp
    · rw [eq_top_iff]
      intro v _
      obtain ⟨y, c, rfl⟩ := extS_surj v
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ c (Submodule.subset_span ⟨(0, 1), ?_⟩))
      · have hy : y ∈ Submodule.span ℝ (unitLattice F : Set (logSpace F)) := by
          rw [unitLattice_span_eq_top]
          trivial
        have hle : Submodule.map (extS F) (Submodule.span ℝ (unitLattice F : Set (logSpace F)))
            ≤ Submodule.span ℝ (LinearMap.range lam : Set (InfinitePlace F → ℝ)) := by
          rw [Submodule.map_span]
          apply Submodule.span_mono
          rintro _ ⟨_, ⟨a, _, rfl⟩, rfl⟩
          exact ⟨(a, 0), by rw [hlam']; simp⟩
        exact hle ⟨y, hy, rfl⟩
      · rw [hlam']
        simp)
