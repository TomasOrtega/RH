import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUpperNormalisation
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfInjOn
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Topology

noncomputable section

namespace UpperNormalisation

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Use `charZero_of_inj_zero fun n hn => ?_` and prove the remaining obligations. Establish `hmem : (C (n : ℤ) : MRing ι) ∈ mCoordIdeal y` using `by show _ ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker, mConeMap, aeval_C]`. Establish `e : (algebraMap ℤ (MvPolynomial K Ω) (n : ℤ)) = C ((n : ℕ) : Ω)` using `by simp`. Rewrite using `[e, hn, C_0]`.

Establish `hh : (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥` using `h.2.2.1`. Establish `: (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι)` using `hmem`. Rewrite `this` using `[hh, Ideal.mem_bot]`. Conclude with `this` after adjusting the coercions.
-/
theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (C (n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
    show _ ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, mConeMap, aeval_C]
    have e : (algebraMap ℤ (MvPolynomial K Ω) (n : ℤ)) = C ((n : ℕ) : Ω) := by simp
    rw [e, hn, C_0]
  have hh : (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ := h.2.2.1
  have : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hmem
  rw [hh, Ideal.mem_bot] at this
  exact_mod_cast this

/- English proof (translation)
Take `⟨i, hi⟩` from `h.2.1.2.2 k`. Use `⟨i, fun h0 => hi ?_⟩` and prove the remaining obligations. Rewrite using `[mCoordIdeal, RingHom.mem_ker]`. Simplify using `[mConeMap, h0]`.
-/
theorem exists_coord_ne_zero {y : (Σ k, ι k) → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal y) d) (k : K) :
    ∃ i, y ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h.2.1.2.2 k
  refine ⟨i, fun h0 => hi ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h0]

/- English proof (translation)
Introduce `s hs`. Establish `hle : Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = s} ≤ (chartLat y a τ).toIntSubmodule`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, hg, rfl⟩ c _`. Establish `key : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g` using `by conv_lhs => rw [g.as_sum] conv_rhs => rw [g.as_sum]`.

Rewrite using `[map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]`. Simplify using `only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib, mul_assoc]`. Use `congr 2`.

Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = ∏ i, (y ⟨k, c k⟩)⁻¹ ^ m ⟨k, i⟩`. Rewrite using `[Finset.prod_pow_eq_pow_sum, hg m hm k, ← hd k, zpow_neg, zpow_natCast, inv_pow]`. Rewrite using `[key, chartRingZ, Algebra.adjoin_range_eq_range_aeval]`.

Conclude with `⟨g, rfl⟩`. Conclude with `hle hs`.
-/
theorem secM_le_chartLat (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) {d : K → ℕ}
    (hd : ∀ k, (d k : ℤ) = τ * a k) : secM y d ≤ chartLat y a τ := by
  intro s hs
  have hle : Submodule.span ℤ {s | ∃ g : MRing ι, IsMultiHomog g d ∧ aeval y g = s} ≤
      (chartLat y a τ).toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩ c _
    have key : aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) =
        aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
      conv_lhs => rw [g.as_sum]
      conv_rhs => rw [g.as_sum]
      rw [map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [aeval_monomial, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib, mul_assoc]
      congr 2
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show y ⟨k, c k⟩ ^ (-((τ : ℤ) * a k)) = ∏ i, (y ⟨k, c k⟩)⁻¹ ^ m ⟨k, i⟩
      rw [Finset.prod_pow_eq_pow_sum, hg m hm k, ← hd k, zpow_neg, zpow_natCast, inv_pow]
    rw [key, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨g, rfl⟩
  exact hle hs

end UpperNormalisation

open UpperNormalisation Mono in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D B P0 II hD hII har hb hsg hconj hBa ε hε`. Establish `: CharZero Ω` using `charZero_of_isArithVar har`. Use `set F : ℝ := ((D + 1).factorial : ℝ) with hF`. Establish `hFpos : 0 < F` using `by rw [hF]; exact_mod_cast Nat.factorial_pos _`. Use `set a : K → ℕ := fun k => (B.a k).toNat with hadef`.

Establish `ha : ∀ k, (a k : ℤ) = B.a k` using `fun k => Int.toNat_of_nonneg (by linarith [hBa k])`. Establish `ha1 : ∀ k, 1 ≤ a k` using `fun k => by have := hBa k; have := ha k; omega`. Establish `hBa' : B.a = fun k => (a k : ℤ)` using `funext fun k => (ha k).symm`. Take `⟨k0, c, hc, hc0, hcs⟩` from `hCond K ι Ω y a ha1 (exists_coord_ne_zero har) hb`. Take `⟨q, w, hw, hgen, hwsm⟩` from `hsg.gen`.

Establish `hcy : aeval y c ∈ chartLat y B.a k0` using `secM_le_chartLat y B.a k0 (d := fun κ => k0 * a κ) (fun κ => by push_cast; rw [ha]) (Submodule.subset_span ⟨c, hc, rfl⟩)`. Take `⟨Cc, hCc⟩` from `SectionBounded.proof K ι Ω y B q w hw hgen hwsm k0 (aeval y c) hcy`. Use `set Ib := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hIb`. Use `set G := geomDeg (mCoordIdeal y) B D with hG`. Use `set η : ℝ := ε / (4 * (((D : ℝ) + 1) * (|G| + 1))) with hηdef`.

Establish `hη : 0 < η` using `by positivity`. Use `set B' := HermLine.constShift B (-η) with hB'def`. Establish `hB'a : B'.a = B.a` using `constShift_a B (-η)`. Establish `hB'h : ∀ z, B'.h z = Real.exp η * B.h z` using `fun z => by show B.h z * Real.exp (-(-η)) = _`. Rewrite using `[neg_neg, mul_comm]`.

Establish `hB'sm : IsSmoothHerm B'` using `(semipos_constShift hsg.semipos (-η)).1`. Take `⟨hfin, Cp, hCp⟩` from `hPack K ι Ω y D B' (chartLat y B'.a) har hb hB'sm (fun τ => chartLat_le_nm y B'.a τ)`. Establish `hG7` using `h7 K ι Ω y D B' P0 II hD hII har hb (smallGen_constShift hsg (by linarith)) (conj_constShift hconj (-η))`. Establish `hCS` using `ConstantShift.proof K ι (II K ι) (mCoordIdeal y) D B (-η) (hII K ι) har hsg.semipos.1`. Establish `hI' : II K ι (mCoordIdeal y) (D + 1) (fun _ => B') ≤ Ib + ε / 4`.

Rewrite using `[hCS]`. Establish `h1 : ((D : ℝ) + 1) * η * G ≤ ((D : ℝ) + 1) * η * (|G| + 1)` using `mul_le_mul_of_nonneg_left ((le_abs_self G).trans (by linarith)) (by positivity)`. Establish `h2 : ((D : ℝ) + 1) * η * (|G| + 1) = ε / 4`. Rewrite using `[hηdef]`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set v : ℕ → ℝ := fun n => smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) n / ((n : ℝ) ^ (D + 1) / F) with hv`. Establish `hv_bdd : ∀ n, v n ≤ |Cp| * F * 2 ^ (D + 1)`. Introduce `n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Rewrite using `[hv]`. Simplify using `only [Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow, zero_div, div_zero]`. Check the signs of the components of the expression. Establish `hn' : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hnpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) / F` using `by positivity`.

Rewrite using `[hv]`. Simplify using `only`. Rewrite using `[div_le_iff₀ hnpos]`. Establish `h1` using `(hCp n).trans (mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity))`. Establish `h2 : ((n : ℝ) + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1)` using `pow_le_pow_left₀ (by positivity) (by linarith) _`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow]`. Clear the denominators using the available nonvanishing facts. Establish `hvB : IsBoundedUnder (· ≤ ·) atTop v` using `isBoundedUnder_of ⟨_, hv_bdd⟩`. Establish `hev1 : ∀ᶠ m in atTop, v m < Ib + ε / 2` using `eventually_lt_of_limsup_lt (lt_of_le_of_lt (hG7.trans hI') (by linarith)) hvB`.

Establish `hcmp : ∀ n : ℕ, Cc ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) → smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0)`. Introduce `n hCn`. Use `smallSectionCount_le_of_injOn (Q := fun m => IsSmallH (mCoordIdeal y) y B' (m + k0)) (La' := fun m => chartLat y B'.a (m + k0)) (fun s => aeval y c * s) (fun s _ t _ hst => mul_left_cancel₀ hc0 hst) (fun s hs hsm => ⟨?_, ?_⟩) (hfin (n + k0))` and prove the remaining obligations. Establish `hs' : s ∈ chartLatNm y (fun κ => (a κ : ℤ)) n` using `by rw [← hBa']; exact hs`. Use `hcs n s hs'` as an intermediate fact.

Use `show aeval y c * s ∈ chartLat y B'.a (n + k0)`. Rewrite using `[hB'a]`. Conclude with `secM_le_chartLat y B.a (n + k0) (fun κ => by push_cast; rw [ha]) this`. Introduce `dg dh g h z hg hh hd he hz`. Rewrite `hd` using `[hB'a]`.

Establish `hch : IsMultiHomog (c * h) ((fun κ => k0 * a κ) + dh)` using `SectionBounded.homog_mul hc hh`. Establish `h1` using `hsm dg ((fun κ => k0 * a κ) + dh) g (c * h) z hg hch (fun κ => by simp only [Pi.add_apply]; push_cast; rw [hd κ, ha]; push_cast; ring) (by rw [he, map_mul]; ring) hz`. Establish `h2` using `hCc (fun κ => k0 * a κ) 0 c 1 z hc SectionBounded.homog_one (fun κ => by simp only [Pi.zero_apply]; push_cast; rw [ha]; ring) (by rw [map_one, mul_one]) hz`. Rewrite `h2` using `[map_one, map_one, norm_one, mul_one]`. Establish `hBz : 0 ≤ B.h z` using `(B.pos z hz.1).le`.

Rewrite `h1` using `[map_mul, eval_mul, norm_mul]`. Rewrite using `[hB'h, mul_pow, ← Real.exp_nat_mul, pow_add]`. Establish `hhn : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, mul_assoc (Cc * _)]`.

Conclude with `mul_le_mul_of_nonneg_right h2 hhn`. Use `_ ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) * B.h z ^ k0 * ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := by gcongr`. Use `_ = _ := by`. Rewrite using `[show ((n + k0 : ℕ) : ℝ) * η = η * ((n + k0 : ℕ) : ℝ) from mul_comm _ _]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hlim : Tendsto (fun n : ℕ => (Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1)) atTop (𝓝 (Ib + ε / 2))`. Establish `h0 : Tendsto (fun n : ℕ => (k0 : ℝ) / n) atTop (𝓝 0)` using `tendsto_const_div_atTop_nhds_zero_nat _`. Simplify using `using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul (Ib + ε / 2)`. Establish `hev3 : ∀ᶠ n : ℕ in atTop, (Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1) < Ib + ε` using `hlim.eventually (gt_mem_nhds (by linarith))`. Establish `hev2 : ∀ᶠ n : ℕ in atTop, v (n + k0) < Ib + ε / 2` using `(tendsto_add_atTop_nat k0).eventually hev1`.

Establish `hevC : ∀ᶠ n : ℕ in atTop, Cc ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ))` using `by filter_upwards [eventually_ge_atTop (⌈|Cc| / η⌉₊)] with n hn`. Establish `h1 : |Cc| / η ≤ ((n + k0 : ℕ) : ℝ)` using `(Nat.le_ceil _).trans (by exact_mod_cast (show ⌈|Cc| / η⌉₊ ≤ n + k0 by omega))`. Establish `h2 : |Cc| ≤ η * ((n + k0 : ℕ) : ℝ)` using `by rw [div_le_iff₀ hη] at h1; linarith`. Establish `h3` using `Real.add_one_le_exp (η * ((n + k0 : ℕ) : ℝ))`. Combine the linear relations using `[le_abs_self Cc]`.

Use `filter_upwards [hev2, hev3, hevC, eventually_ge_atTop 1] with n h2 h3 hC hn1`. Establish `hnpos : (0 : ℝ) < n` using `by exact_mod_cast hn1`. Establish `hmpos : (0 : ℝ) < ((n + k0 : ℕ) : ℝ) ^ (D + 1) / F`. Establish `: (0 : ℝ) < ((n + k0 : ℕ) : ℝ)` using `by exact_mod_cast (show 0 < n + k0 by omega)`. Check the signs of the components of the expression.

Establish `hcount : smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) ≤ (Ib + ε / 2) * (((n + k0 : ℕ) : ℝ) ^ (D + 1) / F)`. Use `h2` as an intermediate fact. Rewrite `this` using `[hv]`. Simplify using `only at this`. Rewrite `this` using `[div_lt_iff₀ hmpos]`.

Conclude with `this.le`. Establish `hratio : ((n + k0 : ℕ) : ℝ) ^ (D + 1) = (1 + (k0 : ℝ) / n) ^ (D + 1) * (n : ℝ) ^ (D + 1)`. Rewrite using `[← mul_pow]`. Use `congr 1`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hratio]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (Ib + ε) * ((n : ℝ) ^ (D + 1) / F) := mul_le_mul_of_nonneg_right h3.le (by positivity)`.
-/
theorem UpperNormalisation.proof (h7 : G7.Statement) (hPack : PackingStatement) (hCond : KH.CondStatement) :
    UpperNormalisation.Statement := by
  intro K _ ι _ Ω _ y D B P0 II hD hII har hb hsg hconj hBa ε hε
  have : CharZero Ω := charZero_of_isArithVar har
  set F : ℝ := ((D + 1).factorial : ℝ) with hF
  have hFpos : 0 < F := by rw [hF]; exact_mod_cast Nat.factorial_pos _

  set a : K → ℕ := fun k => (B.a k).toNat with hadef
  have ha : ∀ k, (a k : ℤ) = B.a k := fun k => Int.toNat_of_nonneg (by linarith [hBa k])
  have ha1 : ∀ k, 1 ≤ a k := fun k => by have := hBa k; have := ha k; omega
  have hBa' : B.a = fun k => (a k : ℤ) := funext fun k => (ha k).symm

  obtain ⟨k0, c, hc, hc0, hcs⟩ := hCond K ι Ω y a ha1 (exists_coord_ne_zero har) hb
  obtain ⟨q, w, hw, hgen, hwsm⟩ := hsg.gen
  have hcy : aeval y c ∈ chartLat y B.a k0 :=
    secM_le_chartLat y B.a k0 (d := fun κ => k0 * a κ) (fun κ => by push_cast; rw [ha])
      (Submodule.subset_span ⟨c, hc, rfl⟩)
  obtain ⟨Cc, hCc⟩ := SectionBounded.proof K ι Ω y B q w hw hgen hwsm k0 (aeval y c) hcy

  set Ib := II K ι (mCoordIdeal y) (D + 1) (fun _ => B) with hIb
  set G := geomDeg (mCoordIdeal y) B D with hG
  set η : ℝ := ε / (4 * (((D : ℝ) + 1) * (|G| + 1))) with hηdef
  have hη : 0 < η := by positivity
  set B' := HermLine.constShift B (-η) with hB'def
  have hB'a : B'.a = B.a := constShift_a B (-η)
  have hB'h : ∀ z, B'.h z = Real.exp η * B.h z := fun z => by
    show B.h z * Real.exp (-(-η)) = _
    rw [neg_neg, mul_comm]
  have hB'sm : IsSmoothHerm B' := (semipos_constShift hsg.semipos (-η)).1
  obtain ⟨hfin, Cp, hCp⟩ := hPack K ι Ω y D B' (chartLat y B'.a) har hb hB'sm
    (fun τ => chartLat_le_nm y B'.a τ)
  have hG7 := h7 K ι Ω y D B' P0 II hD hII har hb (smallGen_constShift hsg (by linarith))
    (conj_constShift hconj (-η))
  have hCS := ConstantShift.proof K ι (II K ι) (mCoordIdeal y) D B (-η) (hII K ι) har hsg.semipos.1
  have hI' : II K ι (mCoordIdeal y) (D + 1) (fun _ => B') ≤ Ib + ε / 4 := by
    rw [hCS]
    have h1 : ((D : ℝ) + 1) * η * G ≤ ((D : ℝ) + 1) * η * (|G| + 1) :=
      mul_le_mul_of_nonneg_left ((le_abs_self G).trans (by linarith)) (by positivity)
    have h2 : ((D : ℝ) + 1) * η * (|G| + 1) = ε / 4 := by
      rw [hηdef]; field_simp
    linarith

  set v : ℕ → ℝ := fun n => smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) n /
    ((n : ℝ) ^ (D + 1) / F) with hv
  have hv_bdd : ∀ n, v n ≤ |Cp| * F * 2 ^ (D + 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hv]
      simp only [Nat.cast_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
        zero_pow, zero_div, div_zero]
      positivity
    · have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) ^ (D + 1) / F := by positivity
      rw [hv]
      dsimp only
      rw [div_le_iff₀ hnpos]
      have h1 := (hCp n).trans (mul_le_mul_of_nonneg_right (le_abs_self Cp) (by positivity))
      have h2 : ((n : ℝ) + 1) ^ (D + 1) ≤ (2 * n) ^ (D + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
      calc _ ≤ |Cp| * ((n : ℝ) + 1) ^ (D + 1) := h1
        _ ≤ |Cp| * (2 * n) ^ (D + 1) := mul_le_mul_of_nonneg_left h2 (abs_nonneg Cp)
        _ = |Cp| * F * 2 ^ (D + 1) * ((n : ℝ) ^ (D + 1) / F) := by
          rw [mul_pow]
          field_simp
  have hvB : IsBoundedUnder (· ≤ ·) atTop v := isBoundedUnder_of ⟨_, hv_bdd⟩
  have hev1 : ∀ᶠ m in atTop, v m < Ib + ε / 2 :=
    eventually_lt_of_limsup_lt (lt_of_le_of_lt (hG7.trans hI') (by linarith)) hvB

  have hcmp : ∀ n : ℕ, Cc ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) →
      smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) := by
    intro n hCn
    refine smallSectionCount_le_of_injOn (Q := fun m => IsSmallH (mCoordIdeal y) y B' (m + k0))
      (La' := fun m => chartLat y B'.a (m + k0)) (fun s => aeval y c * s)
      (fun s _ t _ hst => mul_left_cancel₀ hc0 hst) (fun s hs hsm => ⟨?_, ?_⟩) (hfin (n + k0))
    · have hs' : s ∈ chartLatNm y (fun κ => (a κ : ℤ)) n := by rw [← hBa']; exact hs
      have := hcs n s hs'
      show aeval y c * s ∈ chartLat y B'.a (n + k0)
      rw [hB'a]
      exact secM_le_chartLat y B.a (n + k0) (fun κ => by push_cast; rw [ha]) this
    · intro dg dh g h z hg hh hd he hz
      rw [hB'a] at hd
      have hch : IsMultiHomog (c * h) ((fun κ => k0 * a κ) + dh) := SectionBounded.homog_mul hc hh
      have h1 := hsm dg ((fun κ => k0 * a κ) + dh) g (c * h) z hg hch
        (fun κ => by simp only [Pi.add_apply]; push_cast; rw [hd κ, ha]; push_cast; ring)
        (by rw [he, map_mul]; ring) hz
      have h2 := hCc (fun κ => k0 * a κ) 0 c 1 z hc SectionBounded.homog_one
        (fun κ => by simp only [Pi.zero_apply]; push_cast; rw [ha]; ring) (by rw [map_one, mul_one]) hz
      rw [map_one, map_one, norm_one, mul_one] at h2
      have hBz : 0 ≤ B.h z := (B.pos z hz.1).le
      rw [map_mul, eval_mul, norm_mul] at h1
      rw [hB'h, mul_pow, ← Real.exp_nat_mul, pow_add]
      have hhn : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := by positivity
      calc ‖eval z (map (Int.castRingHom ℂ) g)‖
          ≤ ‖eval z (map (Int.castRingHom ℂ) c)‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := h1
        _ ≤ Cc * B.h z ^ k0 * ‖eval z (map (Int.castRingHom ℂ) h)‖ * B.h z ^ n := by
          rw [mul_assoc, mul_assoc (Cc * _)]
          exact mul_le_mul_of_nonneg_right h2 hhn
        _ ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) * B.h z ^ k0 * ‖eval z (map (Int.castRingHom ℂ) h)‖ *
            B.h z ^ n := by
          gcongr
        _ = _ := by
          rw [show ((n + k0 : ℕ) : ℝ) * η = η * ((n + k0 : ℕ) : ℝ) from mul_comm _ _]
          ring

  have hlim : Tendsto (fun n : ℕ => (Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1)) atTop (𝓝 (Ib + ε / 2)) := by
    have h0 : Tendsto (fun n : ℕ => (k0 : ℝ) / n) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h0).pow (D + 1) |>.const_mul (Ib + ε / 2)
  have hev3 : ∀ᶠ n : ℕ in atTop, (Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1) < Ib + ε :=
    hlim.eventually (gt_mem_nhds (by linarith))
  have hev2 : ∀ᶠ n : ℕ in atTop, v (n + k0) < Ib + ε / 2 :=
    (tendsto_add_atTop_nat k0).eventually hev1
  have hevC : ∀ᶠ n : ℕ in atTop, Cc ≤ Real.exp (η * ((n + k0 : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (⌈|Cc| / η⌉₊)] with n hn
    have h1 : |Cc| / η ≤ ((n + k0 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈|Cc| / η⌉₊ ≤ n + k0 by omega))
    have h2 : |Cc| ≤ η * ((n + k0 : ℕ) : ℝ) := by rw [div_le_iff₀ hη] at h1; linarith
    have h3 := Real.add_one_le_exp (η * ((n + k0 : ℕ) : ℝ))
    linarith [le_abs_self Cc]
  filter_upwards [hev2, hev3, hevC, eventually_ge_atTop 1] with n h2 h3 hC hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hmpos : (0 : ℝ) < ((n + k0 : ℕ) : ℝ) ^ (D + 1) / F := by
    have : (0 : ℝ) < ((n + k0 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n + k0 by omega)
    positivity
  have hcount : smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) ≤
      (Ib + ε / 2) * (((n + k0 : ℕ) : ℝ) ^ (D + 1) / F) := by
    have := h2
    rw [hv] at this
    dsimp only at this
    rw [div_lt_iff₀ hmpos] at this
    exact this.le
  have hratio : ((n + k0 : ℕ) : ℝ) ^ (D + 1) = (1 + (k0 : ℝ) / n) ^ (D + 1) * (n : ℝ) ^ (D + 1) := by
    rw [← mul_pow]
    congr 1
    push_cast
    field_simp
  calc smallSectionCount (IsSmallH (mCoordIdeal y) y B) (chartLatNm y B.a) n
      ≤ smallSectionCount (IsSmallH (mCoordIdeal y) y B') (chartLat y B'.a) (n + k0) := hcmp n hC
    _ ≤ (Ib + ε / 2) * (((n + k0 : ℕ) : ℝ) ^ (D + 1) / F) := hcount
    _ = ((Ib + ε / 2) * (1 + (k0 : ℝ) / n) ^ (D + 1)) * ((n : ℝ) ^ (D + 1) / F) := by
      rw [hratio]; ring
    _ ≤ (Ib + ε) * ((n : ℝ) ^ (D + 1) / F) :=
      mul_le_mul_of_nonneg_right h3.le (by positivity)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
