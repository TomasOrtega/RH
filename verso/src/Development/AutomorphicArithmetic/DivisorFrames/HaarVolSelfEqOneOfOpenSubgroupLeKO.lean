import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n _ _ J hJ hJK`. Establish `hc : Continuous (invT : GL n k →* GL n k)`. Rewrite using `[Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Conclude with `(Units.continuous_coe_inv).matrix_transpose`.

Conclude with `(Units.continuous_val).matrix_transpose`. Set `e : GL n k ≃* GL n k` to `{ toFun := invT, invFun := invT, left_inv := invT_invT, right_inv := invT_invT, map_mul' := invT.map_mul }`. Establish `hec : Continuous e` using `hc`. Establish `hes : Continuous e.symm` using `hc`. Establish `hem : Measurable e` using `hec.measurable`.

Use `haveI : (Measure.map e (Measure.haar : Measure (GL n k))).IsHaarMeasure := MulEquiv.isHaarMeasure_map _ e hec hes`. Establish `hKOpre : e ⁻¹' (KO k n : Set (GL n k)) = KO k n`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`.

Use `invT_mem_KO (k := k) (g := invT g) hg` as an intermediate fact. Rewrite `this` using `[invT_invT]`. Then use the resulting hypothesis. Introduce `hg`. Conclude with `invT_mem_KO hg`. Establish `hJpre : e ⁻¹' ((J.map invT : Subgroup (GL n k)) : Set (GL n k)) = J`.

Use extensionality with `g`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, hxg⟩`. Establish `hxg' : invT x = invT g` using `hxg`.

Establish `: x = g`. Establish `h2` using `congrArg invT hxg'`. Rewrite `h2` using `[invT_invT, invT_invT]`. Then use the resulting hypothesis. Conclude with `this ▸ hx`. Introduce `hg`.

Conclude with `⟨g, hg, rfl⟩`. Take `⟨hA0, hAt⟩` from `haar_ne_zero_ne_top (Measure.haar : Measure (GL n k)) (isOpen_KO (k := k) (n := n)) le_rfl`. Use `set A := (Measure.haar : Measure (GL n k)) (KO k n) with hA`. Establish `hmapKO : Measure.map e (Measure.haar : Measure (GL n k)) (KO k n) = A`. Rewrite using `[Measure.map_apply hem isOpen_KO.measurableSet, hKOpre]`.

Establish `hinv0 : A⁻¹ ≠ 0` using `ENNReal.inv_ne_zero.mpr hAt`. Establish `hinvt : A⁻¹ ≠ ⊤` using `ENNReal.inv_ne_top.mpr hA0`. Use `haveI : (A⁻¹ • Measure.map e (Measure.haar : Measure (GL n k))).IsHaarMeasure := Measure.IsHaarMeasure.smul (μ := _) hinv0 hinvt`. Use `haveI : (A⁻¹ • (Measure.haar : Measure (GL n k))).IsHaarMeasure := Measure.IsHaarMeasure.smul (μ := _) hinv0 hinvt`. Establish `h1` using `eq_haarVol (A⁻¹ • Measure.map e (Measure.haar : Measure (GL n k))) (isOpen_KO (k := k) (n := n)) le_rfl (by rw [Measure.smul_apply, hmapKO, smul_eq_mul, ENNReal.inv_mul_cancel hA0 hAt])`.

Establish `h2` using `eq_haarVol (A⁻¹ • (Measure.haar : Measure (GL n k))) (isOpen_KO (k := k) (n := n)) le_rfl (by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hA0 hAt])`. Establish `hmap : Measure.map e (Measure.haar : Measure (GL n k)) = Measure.haar`. Establish `h3` using `h1.trans h2.symm`. Use extensionality with `s hs`. Establish `h4` using `congrArg (fun μ : Measure (GL n k) => A • μ s) h3`.

Simplify using `only [Measure.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hA0 hAt, one_mul] at h4`. Conclude with `h4`. Establish `hJ'` using `(isOpen_map_invT hJ hJK).1`. Establish `heq : (Measure.haar : Measure (GL n k)) ((J.map invT : Subgroup (GL n k)) : Set (GL n k)) = (Measure.haar : Measure (GL n k)) J`. Rewrite using `[← hmap, Measure.map_apply hem hJ'.measurableSet, hJpre]`.

Rewrite using `[hmap]`. Take `⟨hJ0, hJt⟩` from `haar_ne_zero_ne_top (Measure.haar : Measure (GL n k)) hJ hJK`. Unfold `haarVol`. Rewrite using `[Measure.smul_apply, smul_eq_mul, heq, ENNReal.inv_mul_cancel hJ0 hJt]`.
-/
theorem UpperTheory.haarVol_self_eq_one_of_openSubgroup_le_KO :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] (J : Subgroup (GL n k)), IsOpen (J : Set (GL n k)) → J ≤ KO k n → haarVol (J.map invT) (J : Set (GL n k)) = 1 := by
  intro k _ _ _ _ _ _ n _ _ J hJ hJK
  have hc : Continuous (invT : GL n k →* GL n k) := by
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_coe_inv).matrix_transpose
    · exact (Units.continuous_val).matrix_transpose
  let e : GL n k ≃* GL n k :=
    { toFun := invT, invFun := invT, left_inv := invT_invT, right_inv := invT_invT,
      map_mul' := invT.map_mul }
  have hec : Continuous e := hc
  have hes : Continuous e.symm := hc
  have hem : Measurable e := hec.measurable
  haveI : (Measure.map e (Measure.haar : Measure (GL n k))).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ e hec hes
  have hKOpre : e ⁻¹' (KO k n : Set (GL n k)) = KO k n := by
    ext g
    constructor
    · intro hg
      have := invT_mem_KO (k := k) (g := invT g) hg
      rwa [invT_invT] at this
    · intro hg
      exact invT_mem_KO hg
  have hJpre : e ⁻¹' ((J.map invT : Subgroup (GL n k)) : Set (GL n k)) = J := by
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxg⟩
      have hxg' : invT x = invT g := hxg
      have : x = g := by
        have h2 := congrArg invT hxg'
        rwa [invT_invT, invT_invT] at h2
      exact this ▸ hx
    · intro hg
      exact ⟨g, hg, rfl⟩
  obtain ⟨hA0, hAt⟩ := haar_ne_zero_ne_top (Measure.haar : Measure (GL n k)) (isOpen_KO (k := k) (n := n)) le_rfl
  set A := (Measure.haar : Measure (GL n k)) (KO k n) with hA
  have hmapKO : Measure.map e (Measure.haar : Measure (GL n k)) (KO k n) = A := by
    rw [Measure.map_apply hem isOpen_KO.measurableSet, hKOpre]
  have hinv0 : A⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hAt
  have hinvt : A⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hA0
  haveI : (A⁻¹ • Measure.map e (Measure.haar : Measure (GL n k))).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul (μ := _) hinv0 hinvt
  haveI : (A⁻¹ • (Measure.haar : Measure (GL n k))).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul (μ := _) hinv0 hinvt
  have h1 := eq_haarVol (A⁻¹ • Measure.map e (Measure.haar : Measure (GL n k))) (isOpen_KO (k := k) (n := n)) le_rfl
    (by rw [Measure.smul_apply, hmapKO, smul_eq_mul, ENNReal.inv_mul_cancel hA0 hAt])
  have h2 := eq_haarVol (A⁻¹ • (Measure.haar : Measure (GL n k))) (isOpen_KO (k := k) (n := n)) le_rfl
    (by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hA0 hAt])
  have hmap : Measure.map e (Measure.haar : Measure (GL n k)) = Measure.haar := by
    have h3 := h1.trans h2.symm
    ext s hs
    have h4 := congrArg (fun μ : Measure (GL n k) => A • μ s) h3
    simp only [Measure.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hA0 hAt, one_mul] at h4
    exact h4
  have hJ' := (isOpen_map_invT hJ hJK).1
  have heq : (Measure.haar : Measure (GL n k)) ((J.map invT : Subgroup (GL n k)) : Set (GL n k)) =
      (Measure.haar : Measure (GL n k)) J := by
    rw [← hmap, Measure.map_apply hem hJ'.measurableSet, hJpre]
    rw [hmap]
  obtain ⟨hJ0, hJt⟩ := haar_ne_zero_ne_top (Measure.haar : Measure (GL n k)) hJ hJK
  unfold haarVol
  rw [Measure.smul_apply, smul_eq_mul, heq, ENNReal.inv_mul_cancel hJ0 hJt]
