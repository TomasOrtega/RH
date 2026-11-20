import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionPointHeight
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionOrderAtPoint
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedF
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

set_option linter.unusedSectionVars false

namespace SmallSectionPointHeight

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C c => simp [mConeMap]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, hp, hq]`. Consider the case `mul_X p n hp`. Rewrite using `[map_mul, map_mul, map_mul, hp]`.

Simplify using `[mConeMap]`.
-/
theorem aeval_eq_eval_mConeMap (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    aeval y f = eval (fun _ ↦ (1 : Ω)) (mConeMap y f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [mConeMap]

/- English proof (translation)
Introduce `h`. Rewrite `h` using `[mCoordIdeal, RingHom.mem_ker]`. Conclude with `hf (by rw [aeval_eq_eval_mConeMap, h, map_zero])`.
-/
theorem notMem_mCoordIdeal {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : aeval y f ≠ 0) :
    f ∉ mCoordIdeal y := by
  intro h
  rw [mCoordIdeal, RingHom.mem_ker] at h
  exact hf (by rw [aeval_eq_eval_mConeMap, h, map_zero])

/- English proof (translation)
Introduce `h0`. Apply `hp` to reduce the goal to its premises. Rewrite using `[mCoordIdeal, RingHom.mem_ker]`. Simplify using `[mConeMap, h0]`.
-/
theorem coord_ne_zero {y : (Σ k, ι k) → Ω} {p : Σ k, ι k} (hp : (X p : MRing ι) ∉ mCoordIdeal y) :
    y p ≠ 0 := by
  intro h0
  apply hp
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h0]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, IndefiniteRowSideFullHecke.HeightsSet.constLine]`. Consider the case `succ m ih => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ih, pow_succ]`.
-/
theorem powLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m : ℕ) (z : (Σ k, ι k) → ℂ) :
    (IndefiniteRowSideFullHecke.HeightsSet.powLine A m).h z = A.h z ^ m := by
  induction m with
  | zero => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, IndefiniteRowSideFullHecke.HeightsSet.constLine]
  | succ m ih => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ih, pow_succ]

/- English proof (translation)
Simplify using `[IndefiniteRowSideFullHecke.HeightsSet.chartMon, map_prod, map_pow]`.
-/
theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (e : K → ℕ) :
    aeval y (IndefiniteRowSideFullHecke.HeightsSet.chartMon c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [IndefiniteRowSideFullHecke.HeightsSet.chartMon, map_prod, map_pow]

/- English proof (translation)
Unfold `vertR`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W H), finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W G)]`. Establish `hsub : (divSupp_finite W H).toFinset ⊆ (divSupp_finite W G).toFinset` using `fun V hV ↦ by`. Rewrite `hV`, the goal using `[Set.Finite.mem_toFinset]`. Conclude with `(h V hV).1`.

Establish `hc : ∀ V : Ideal (MRing ι), 0 ≤ (if IsHorizontal V then (0 : ℝ) else (geoNum 0 V (fun j ↦ ((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).a) : ℝ) * Real.log (charOf V))`. Introduce `V`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `mul_nonneg (by exact_mod_cast IndefiniteRowSideFullHecke.HeightsSet.geoNum_zero_nonneg V _) (Real.log_natCast_nonneg _)`.

Use `le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun V _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (hc V))` and prove the remaining obligations. Use `Finset.sum_le_sum fun V hV ↦ ?_` and prove the remaining obligations. Rewrite `hV` using `[Set.Finite.mem_toFinset]`. Conclude with `mul_le_mul_of_nonneg_right (by exact_mod_cast (h V hV).2) (hc V)`.
-/
theorem vertR_le {W : Ideal (MRing ι)} {G H : MRing ι}
    (h : ∀ V ∈ divSupp W H, V ∈ divSupp W G ∧
      multAt (W ⊔ Ideal.span {H}) V ≤ multAt (W ⊔ Ideal.span {G}) V) :
    vertR W (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) H ≤ vertR W (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) G := by
  classical
  unfold vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W H),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W G)]
  have hsub : (divSupp_finite W H).toFinset ⊆ (divSupp_finite W G).toFinset := fun V hV ↦ by
    rw [Set.Finite.mem_toFinset] at hV ⊢
    exact (h V hV).1
  have hc : ∀ V : Ideal (MRing ι), 0 ≤ (if IsHorizontal V then (0 : ℝ) else
      (geoNum 0 V (fun j ↦ ((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).a) : ℝ) * Real.log (charOf V)) := by
    intro V
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by exact_mod_cast IndefiniteRowSideFullHecke.HeightsSet.geoNum_zero_nonneg V _)
        (Real.log_natCast_nonneg _)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun V _ _ ↦
    mul_nonneg (Nat.cast_nonneg _) (hc V))
  refine Finset.sum_le_sum fun V hV ↦ ?_
  rw [Set.Finite.mem_toFinset] at hV
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (h V hV).2) (hc V)

end SmallSectionPointHeight

open SmallSectionPointHeight in

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D A τ s II hII hP hbir hA hτ hs hs0 hsmall`. Use `choose c hc using hP.2.1.2.2`. Establish `hyc : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k ↦ coord_ne_zero (hc k)`. Use `set ap : K → ℕ := fun k ↦ ((τ : ℤ) * A.a k).toNat with hap`. Use `set an : K → ℕ := fun k ↦ (-((τ : ℤ) * A.a k)).toNat with han`.

Establish `hpn : ∀ k, (ap k : ℤ) = an k + τ * A.a k` using `fun k ↦ by`. Use `Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)` as an intermediate fact. Simplify using `only [hap, han]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨d, g0, h0, hg0, hh0, hh0y, hgh0⟩` from `hbir (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k)))`.

Use `set G := g0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c ap with hGdef`. Use `set H := h0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c an with hHdef`. Establish `hG : IsMultiHomog G (d + ap)` using `IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hg0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c ap)`. Establish `hH : IsMultiHomog H (d + an)` using `IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hh0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c an)`. Establish `hdeg : ∀ k, ((d + ap) k : ℤ) = (d + an) k + τ * A.a k` using `fun k ↦ by`.

Simplify using `only [Pi.add_apply, Nat.cast_add, hpn k]`. Expand and normalize the polynomial expressions, which then agree. Establish `hGH : aeval y G = s * aeval y H`. Establish `hprod : ∀ k, y ⟨k, c k⟩ ^ ap k = y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) * y ⟨k, c k⟩ ^ an k` using `fun k ↦ by`. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), hpn k, add_comm]`.

Establish `h1 : (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) = 1`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_eq_one fun k _ ↦ by rw [← zpow_add₀ (hyc k), neg_add_cancel, zpow_zero]`. Rewrite using `[hGdef, hHdef, map_mul, map_mul, aeval_chartMon, aeval_chartMon, hgh0, Finset.prod_congr rfl fun k _ ↦ hprod k, Finset.prod_mul_distrib]`. Take the linear combination `(s * aeval y h0 * ∏ k, y ⟨k, c k⟩ ^ an k) * h1`.

Establish `hHy : aeval y H ≠ 0`. Rewrite using `[hHdef, map_mul, aeval_chartMon]`. Conclude with `mul_ne_zero hh0y (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc k))`. Establish `hGy : aeval y G ≠ 0`. Rewrite using `[hGH]`.

Conclude with `mul_ne_zero hs0 hHy`. Use `⟨G * H, ⟨_, IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hG hH⟩, notMem_mCoordIdeal (by rw [map_mul]; exact mul_ne_zero hGy hHy), ?_⟩` and prove the remaining obligations. Introduce `W hW hPW hfW`. Establish `hGW : G ∉ W` using `fun h ↦ hfW (W.mul_mem_right H h)`. Establish `hHW : H ∉ W` using `fun h ↦ hfW (W.mul_mem_left G h)`.

Establish `hI : IsIntersectionFamily (II K ι)` using `hII K ι`. Use `set E := IndefiniteRowSideFullHecke.HeightsSet.powLine A τ with hEdef`. Establish `hE : IsSmoothHerm E` using `IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_powLine hA τ`. Use `set B := HermLine.sqMetric (ι := ι) (d + an) with hBdef`. Establish `hB : IsSmoothHerm B` using `isSmoothHerm_sqMetric _`.

Establish `hEB : IsSmoothHerm (E.tensor B)` using `IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hE hB`. Establish `hEBa : ∀ k, (E.tensor B).a k = ((d + ap) k : ℕ)` using `fun k ↦ by show E.a k + B.a k = _`. Rewrite using `[hEdef, IndefiniteRowSideFullHecke.HeightsSet.powLine_a, hdeg k]`. Use `show _ + ((d + an) k : ℤ) = _`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsecG : IsSectionOn W (E.tensor B) G` using `⟨_, hEBa, hG, hGW⟩`. Establish `hsecH : IsSectionOn W B H` using `⟨_, fun k ↦ rfl, hH, hHW⟩`. Establish `hRG` using `IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hEB hEBa hG hGW`. Establish `hRH` using `IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hB (fun k ↦ rfl) hH hHW`. Establish `hadd` using `IndefiniteRowSideFullHecke.HeightsSet.inter_tensor (II K ι) hI hW hE hB`.

Establish `hpow` using `IndefiniteRowSideFullHecke.HeightsSet.inter_powLine (II K ι) hI hW hA τ`. Rewrite `hRG` using `[recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecG]`. Rewrite `hRH` using `[recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecH]`. Establish `hvert` using `vertR_le (hOrd K ι Ω y A.a τ s W G H (d + ap) (d + an) hW hPW hs hG hH hdeg hGH hGW hHW)`. Establish `harch : arInt W G (E.tensor B) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) ≤ arInt W H B (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)`.

Unfold `arInt`. Rewrite using `[Inter.ptsIntegral_add_of_dimOne fibreFinite hW _ (g₁ := logNorm B H) (g₂ := fun z ↦ logNorm (E.tensor B) G z - logNorm B H z) fun z _ ↦ by ring]`. Use `add_le_of_nonpos_right (IndefiniteRowSideFullHecke.HeightsSet.ptsIntegral_nonpos W _ fun z hz ↦ ?_)` and prove the remaining obligations. Use `show logNorm (E.tensor B) G z - logNorm B H z ≤ 0`. Establish `hGz` using `norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecG hz)`.

Establish `hHz` using `norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecH hz)`. Establish `hAz` using `A.pos z hz.1`. Establish `hBz` using `B.pos z hz.1`. Establish `hEz : E.h z = A.h z ^ τ` using `powLine_h A τ z`. Establish `hEz0 : 0 < E.h z` using `hEz ▸ pow_pos hAz τ`.

Establish `hzP : z ∈ mcPts (mCoordIdeal y)` using `⟨hz.1, fun f hf ↦ hz.2 f (hPW hf)⟩`. Establish `hsm` using `hsmall (d + ap) (d + an) G H z hG hH hdeg hGH hzP`. Rewrite `hsm` using `[← hEz]`. Use `sub_nonpos.mpr (Real.log_le_log (div_pos hGz (mul_pos hEz0 hBz)) ?_)` and prove the remaining obligations. Use `show _ / (E.h z * B.h z) ≤ _ / B.h z`.

Rewrite using `[div_le_div_iff₀ (mul_pos hEz0 hBz) hBz]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hsm hBz.le]`. Establish `hτI : 0 ≤ (τ : ℝ) * II K ι W 1 ![A]`. Rewrite using `[← hpow]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hτ0 : (0 : ℝ) < τ` using `by exact_mod_cast hτ`. Conclude with `le_of_mul_le_mul_left (by rw [mul_zero]; exact hτI) hτ0`.
-/
theorem SmallSectionPointHeight.proof (hOrd : SectionOrderAtPoint.Statement) :
    SmallSectionPointHeight.Statement := by
  intro K _ ι _ Ω _ y D A τ s II hII hP hbir hA hτ hs hs0 hsmall
  classical

  choose c hc using hP.2.1.2.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦ coord_ne_zero (hc k)

  set ap : K → ℕ := fun k ↦ ((τ : ℤ) * A.a k).toNat with hap
  set an : K → ℕ := fun k ↦ (-((τ : ℤ) * A.a k)).toNat with han
  have hpn : ∀ k, (ap k : ℤ) = an k + τ * A.a k := fun k ↦ by
    have := Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)
    simp only [hap, han]
    linarith
  obtain ⟨d, g0, h0, hg0, hh0, hh0y, hgh0⟩ := hbir (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k)))
  set G := g0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c ap with hGdef
  set H := h0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c an with hHdef
  have hG : IsMultiHomog G (d + ap) :=
    IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hg0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c ap)
  have hH : IsMultiHomog H (d + an) :=
    IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hh0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c an)
  have hdeg : ∀ k, ((d + ap) k : ℤ) = (d + an) k + τ * A.a k := fun k ↦ by
    simp only [Pi.add_apply, Nat.cast_add, hpn k]
    ring
  have hGH : aeval y G = s * aeval y H := by
    have hprod : ∀ k, y ⟨k, c k⟩ ^ ap k = y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) * y ⟨k, c k⟩ ^ an k := fun k ↦ by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), hpn k, add_comm]
    have h1 : (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun k _ ↦ by rw [← zpow_add₀ (hyc k), neg_add_cancel, zpow_zero]
    rw [hGdef, hHdef, map_mul, map_mul, aeval_chartMon, aeval_chartMon, hgh0,
      Finset.prod_congr rfl fun k _ ↦ hprod k, Finset.prod_mul_distrib]
    linear_combination (s * aeval y h0 * ∏ k, y ⟨k, c k⟩ ^ an k) * h1
  have hHy : aeval y H ≠ 0 := by
    rw [hHdef, map_mul, aeval_chartMon]
    exact mul_ne_zero hh0y (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc k))
  have hGy : aeval y G ≠ 0 := by
    rw [hGH]
    exact mul_ne_zero hs0 hHy
  refine ⟨G * H, ⟨_, IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hG hH⟩,
    notMem_mCoordIdeal (by rw [map_mul]; exact mul_ne_zero hGy hHy), ?_⟩
  intro W hW hPW hfW
  have hGW : G ∉ W := fun h ↦ hfW (W.mul_mem_right H h)
  have hHW : H ∉ W := fun h ↦ hfW (W.mul_mem_left G h)

  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set E := IndefiniteRowSideFullHecke.HeightsSet.powLine A τ with hEdef
  have hE : IsSmoothHerm E := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_powLine hA τ
  set B := HermLine.sqMetric (ι := ι) (d + an) with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric _
  have hEB : IsSmoothHerm (E.tensor B) := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hE hB
  have hEBa : ∀ k, (E.tensor B).a k = ((d + ap) k : ℕ) := fun k ↦ by
    show E.a k + B.a k = _
    rw [hEdef, IndefiniteRowSideFullHecke.HeightsSet.powLine_a, hdeg k]
    show _ + ((d + an) k : ℤ) = _
    ring
  have hsecG : IsSectionOn W (E.tensor B) G := ⟨_, hEBa, hG, hGW⟩
  have hsecH : IsSectionOn W B H := ⟨_, fun k ↦ rfl, hH, hHW⟩
  have hRG := IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hEB hEBa hG hGW
  have hRH := IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hB (fun k ↦ rfl) hH hHW
  have hadd := IndefiniteRowSideFullHecke.HeightsSet.inter_tensor (II K ι) hI hW hE hB
  have hpow := IndefiniteRowSideFullHecke.HeightsSet.inter_powLine (II K ι) hI hW hA τ
  rw [recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecG] at hRG
  rw [recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecH] at hRH

  have hvert := vertR_le (hOrd K ι Ω y A.a τ s W G H (d + ap) (d + an) hW hPW hs hG hH hdeg hGH hGW hHW)

  have harch : arInt W G (E.tensor B) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) ≤
      arInt W H B (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := by
    unfold arInt
    rw [Inter.ptsIntegral_add_of_dimOne fibreFinite hW _ (g₁ := logNorm B H)
      (g₂ := fun z ↦ logNorm (E.tensor B) G z - logNorm B H z) fun z _ ↦ by ring]
    refine add_le_of_nonpos_right (IndefiniteRowSideFullHecke.HeightsSet.ptsIntegral_nonpos W _ fun z hz ↦ ?_)
    show logNorm (E.tensor B) G z - logNorm B H z ≤ 0
    have hGz := norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecG hz)
    have hHz := norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecH hz)
    have hAz := A.pos z hz.1
    have hBz := B.pos z hz.1
    have hEz : E.h z = A.h z ^ τ := powLine_h A τ z
    have hEz0 : 0 < E.h z := hEz ▸ pow_pos hAz τ
    have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf ↦ hz.2 f (hPW hf)⟩
    have hsm := hsmall (d + ap) (d + an) G H z hG hH hdeg hGH hzP
    rw [← hEz] at hsm
    refine sub_nonpos.mpr (Real.log_le_log (div_pos hGz (mul_pos hEz0 hBz)) ?_)
    show _ / (E.h z * B.h z) ≤ _ / B.h z
    rw [div_le_div_iff₀ (mul_pos hEz0 hBz) hBz]
    nlinarith [mul_le_mul_of_nonneg_right hsm hBz.le]

  have hτI : 0 ≤ (τ : ℝ) * II K ι W 1 ![A] := by
    rw [← hpow]
    linarith
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hτI) hτ0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
