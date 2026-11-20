import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExponentInequalityNondegenerateMid
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Deg

/- English proof (translation)
The claim follows from `(Real.rpow_le_rpow_of_exponent_le hx huw).trans (Real.rpow_le_rpow (by linarith) hxy (hu.trans huw))`.
-/
theorem rpow_le_rpow_both {x y u w : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) (hu : 0 ≤ u) (huw : u ≤ w) :
    x ^ u ≤ y ^ w :=
  (Real.rpow_le_rpow_of_exponent_le hx huw).trans
    (Real.rpow_le_rpow (by linarith) hxy (hu.trans huw))

/- English proof (translation)
Unfold `Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH`. Conclude with `Real.one_le_rpow hb (by positivity)`.
-/
theorem bigH_one_le (C : ℝ) (hC : 0 ≤ C) (m f : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    1 ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
  exact Real.one_le_rpow hb (by positivity)

/- English proof (translation)
Unfold `Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH`. Apply `Real.rpow_le_rpow_of_exponent_le hb` to reduce the goal to its premises. Establish `: (0:ℝ) ≤ (m:ℝ)^2 * f` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem bigH_mono {C D : ℝ} (hC : 0 ≤ C) (hCD : C ≤ D) (m f : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH C m f b ≤ Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH D m f b := by
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.bigH
  apply Real.rpow_le_rpow_of_exponent_le hb
  have : (0:ℝ) ≤ (m:ℝ)^2 * f := by positivity
  nlinarith

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
/- English proof (translation)
Establish `hC0 : (0:ℝ) ≤ C` using `by linarith`. Establish `hD0 : (0:ℝ) ≤ D` using `by linarith`. Establish `hH1` using `bigH_one_le C hC0 m f hb`. Establish `hHD1` using `bigH_one_le D hD0 m f hb`. Establish `hHm` using `bigH_mono hC0 hCD m f hb`.

Use `⟨fun s hs hsk => ?_, fun s hs => ?_⟩` and prove the remaining obligations. Take `⟨h0, h1⟩` from `h.1 s hs hsk`. Use `⟨h0, h1.trans ?_⟩` and prove the remaining obligations. Establish `e1 : bigH C m f b ^ C ≤ bigH D m f b ^ D` using `rpow_le_rpow_both hH1 hHm hC0 hCD`. Establish `e2 : C ^ (s * k * f) ≤ D ^ (s * k * f)` using `pow_le_pow_left₀ hC0 hCD _`.

Conclude with `mul_le_mul e1 e2 (by positivity) (by positivity)`. Take `⟨h0, h1⟩` from `h.2 s hs`. Use `⟨h0, h1.trans ?_⟩` and prove the remaining obligations. Establish `hk0 : (0:ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `hm0 : (0:ℝ) ≤ m` using `Nat.cast_nonneg m`.

Establish `e1 : (C * k) ^ (k * f) ≤ (D * k) ^ (k * f)` using `pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCD hk0) _`. Establish `a1 : 1 ≤ bigH C m f b ^ (C * m)` using `Real.one_le_rpow hH1 (by positivity)`. Establish `a2 : bigH C m f b ^ (C * m) ≤ bigH D m f b ^ (D * m)` using `rpow_le_rpow_both hH1 hHm (by positivity) (mul_le_mul_of_nonneg_right hCD hm0)`. Establish `e2 : (bigH C m f b ^ (C * m) * NT) ^ (C * k) ≤ (bigH D m f b ^ (D * m) * NT) ^ (D * k)`. Apply `rpow_le_rpow_both` to reduce the goal to its premises.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `mul_le_mul_of_nonneg_right a2 (by linarith)`. Check the signs of the components of the expression. Conclude with `mul_le_mul_of_nonneg_right hCD hk0`. Conclude with `mul_le_mul e1 e2 (by positivity) (by positivity)`.
-/
theorem xiHyp_mono {C D : ℝ} (hC : 1 ≤ C) (hCD : C ≤ D) {k m f : ℕ} {b v NT : ℝ} {Xi : ℕ → ℝ}
    (hb : 1 ≤ b) (hNT : 1 ≤ NT) (h : XiHyp C k m f b v NT Xi) : XiHyp D k m f b v NT Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hD0 : (0:ℝ) ≤ D := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHD1 := bigH_one_le D hD0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  refine ⟨fun s hs hsk => ?_, fun s hs => ?_⟩
  · obtain ⟨h0, h1⟩ := h.1 s hs hsk
    refine ⟨h0, h1.trans ?_⟩
    have e1 : bigH C m f b ^ C ≤ bigH D m f b ^ D := rpow_le_rpow_both hH1 hHm hC0 hCD
    have e2 : C ^ (s * k * f) ≤ D ^ (s * k * f) := pow_le_pow_left₀ hC0 hCD _
    exact mul_le_mul e1 e2 (by positivity) (by positivity)
  · obtain ⟨h0, h1⟩ := h.2 s hs
    refine ⟨h0, h1.trans ?_⟩
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have e1 : (C * k) ^ (k * f) ≤ (D * k) ^ (k * f) :=
      pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hCD hk0) _
    have a1 : 1 ≤ bigH C m f b ^ (C * m) := Real.one_le_rpow hH1 (by positivity)
    have a2 : bigH C m f b ^ (C * m) ≤ bigH D m f b ^ (D * m) :=
      rpow_le_rpow_both hH1 hHm (by positivity) (mul_le_mul_of_nonneg_right hCD hm0)
    have e2 : (bigH C m f b ^ (C * m) * NT) ^ (C * k) ≤ (bigH D m f b ^ (D * m) * NT) ^ (D * k) := by
      apply rpow_le_rpow_both
      · nlinarith
      · exact mul_le_mul_of_nonneg_right a2 (by linarith)
      · positivity
      · exact mul_le_mul_of_nonneg_right hCD hk0
    exact mul_le_mul e1 e2 (by positivity) (by positivity)

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩` from `h`. Establish `hlb : 0 ≤ Real.log b` using `Real.log_nonneg (by linarith)`. Establish `hX : (0:ℝ) ≤ (m:ℝ) ^ 5 * f * Real.log b` using `by positivity`. Use `⟨h1, h2, h3, h4, h5, ?_, h7, h8, h9, ?_, le_rfl, ?_⟩` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_right hK hX` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Use `h10.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_)` and prove the remaining obligations. Establish `: (0:ℝ) ≤ (m:ℝ) * f` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `: (0:ℝ) ≤ D` using `by linarith`.

Conclude with `Real.one_le_exp (by positivity)`.
-/
theorem params_mono {C D K K₀ : ℝ} (hC : 1 ≤ C) (hCD : C ≤ D) (hK : K ≤ K₀) {k m f : ℕ} {b g v NT : ℝ}
    (h : Params C K₀ k m f b g v NT 1) : Params D K k m f b g v NT 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have hlb : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hX : (0:ℝ) ≤ (m:ℝ) ^ 5 * f * Real.log b := by positivity
  refine ⟨h1, h2, h3, h4, h5, ?_, h7, h8, h9, ?_, le_rfl, ?_⟩
  · have := mul_le_mul_of_nonneg_right hK hX
    nlinarith
  · refine h10.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) ?_)
    have : (0:ℝ) ≤ (m:ℝ) * f := by positivity
    nlinarith
  · have : (0:ℝ) ≤ D := by linarith
    exact Real.one_le_exp (by positivity)

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

/- English proof (translation)
Rewrite using `[mul_pow, ← Real.exp_nat_mul, mul_one, mul_comm (Real.exp _)]`. Use `mul_le_mul_of_nonneg_left (hG.trans (Real.exp_le_exp.2 ?_)) (by positivity)` and prove the remaining obligations. Establish `hf' : (1:ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hk : (0:ℝ) ≤ k` using `Nat.cast_nonneg k`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gam_absorb {C Gam : ℝ} (hC : 0 ≤ C) {k f : ℕ} (hf : 1 ≤ f) (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    C ^ (k * f) * Gam ≤ (Real.exp 1 * C) ^ (k * f) := by
  rw [mul_pow, ← Real.exp_nat_mul, mul_one, mul_comm (Real.exp _)]
  refine mul_le_mul_of_nonneg_left (hG.trans (Real.exp_le_exp.2 ?_)) (by positivity)
  have hf' : (1:ℝ) ≤ f := by exact_mod_cast hf
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
  push_cast
  nlinarith

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
/- English proof (translation)
Establish `hC0 : (0:ℝ) ≤ C` using `by linarith`. Establish `hCD : C ≤ Real.exp 1 * C` using `le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))`. Establish `hD0 : (0:ℝ) ≤ Real.exp 1 * C` using `by linarith`. Establish `hH1` using `bigH_one_le C hC0 m f hb`. Establish `hHm` using `bigH_mono hC0 hCD m f hb`.

Establish `hHDpos : 0 < bigH (Real.exp 1 * C) m f b` using `lt_of_lt_of_le zero_lt_one (hH1.trans hHm)`. Establish `hHCpos : 0 < bigH C m f b` using `lt_of_lt_of_le zero_lt_one hH1`. Establish `e0 : 0 ≤ (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s` using `by positivity`. Establish `eH : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) ≤ bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2)`. Apply `rpow_le_rpow_both hH1 hHm (by positivity)` to reduce the goal to its premises.

Establish `: (0:ℝ) ≤ ((s : ℝ) + m) * (m : ℝ) ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `eP : (C * s * f) ^ (6 * s * f) ≤ (Real.exp 1 * C * s * f) ^ (6 * s * f)`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Establish `: (0:ℝ) ≤ (s : ℝ) * f` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `eG` using `gam_absorb hC0 hf hG (k := k)`. Unfold `ndRow`. Combine the equalities or inequalities in the displayed calculation. Establish `hH0 : 0 ≤ bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2)` using `le_trans zero_le_one (Real.one_le_rpow hH1 (by positivity))`.

Use `gcongr`. Use `_ = _ := by ring`.
-/
theorem ndRow_mono {C Gam : ℝ} (hC : 1 ≤ C) {k m f s : ℕ} {b g v : ℝ} {Xi : ℕ → ℝ}
    (hf : 1 ≤ f) (hb : 1 ≤ b) (hg : 0 < g) (hv : 0 ≤ v) (hXi : 0 ≤ Xi s)
    (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    ndRow C k m f s b g v Gam Xi ≤ ndRow (Real.exp 1 * C) k m f s b g v 1 Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD0 : (0:ℝ) ≤ Real.exp 1 * C := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  have hHDpos : 0 < bigH (Real.exp 1 * C) m f b := lt_of_lt_of_le zero_lt_one (hH1.trans hHm)
  have hHCpos : 0 < bigH C m f b := lt_of_lt_of_le zero_lt_one hH1
  have e0 : 0 ≤ (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s := by positivity
  have eH : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) ≤
      bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    apply rpow_le_rpow_both hH1 hHm (by positivity)
    have : (0:ℝ) ≤ ((s : ℝ) + m) * (m : ℝ) ^ 2 := by positivity
    nlinarith
  have eP : (C * s * f) ^ (6 * s * f) ≤ (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0:ℝ) ≤ (s : ℝ) * f := by positivity
    nlinarith
  have eG := gam_absorb hC0 hf hG (k := k)
  unfold ndRow
  calc (2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam
      = ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (C ^ (k * f) * Gam) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) := by ring
    _ ≤ ((2 / g) ^ ((s - 1) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (Real.exp 1 * C) ^ (k * f) *
        bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) *
        (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
      have hH0 : 0 ≤ bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) :=
        le_trans zero_le_one (Real.one_le_rpow hH1 (by positivity))
      gcongr
    _ = _ := by ring

open Formalism.HermitianLatticeCounting.LatticeSumBounds in
/- English proof (translation)
Establish `hC0 : (0:ℝ) ≤ C` using `by linarith`. Establish `hCD : C ≤ Real.exp 1 * C` using `le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))`. Establish `hD0 : (0:ℝ) ≤ Real.exp 1 * C` using `by linarith`. Establish `hH1` using `bigH_one_le C hC0 m f hb`. Establish `hHm` using `bigH_mono hC0 hCD m f hb`.

Establish `hHDpos : 0 < bigH (Real.exp 1 * C) m f b` using `lt_of_lt_of_le zero_lt_one (hH1.trans hHm)`. Establish `hHCpos : 0 < bigH C m f b` using `lt_of_lt_of_le zero_lt_one hH1`. Establish `hlb : 0 ≤ Real.log b` using `Real.log_nonneg hb`. Establish `e0 : 0 ≤ (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s` using `by positivity`. Establish `eH : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) ≤ bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2)`.

Apply `rpow_le_rpow_both hH1 hHm (by positivity)` to reduce the goal to its premises. Establish `: (0:ℝ) ≤ ((s : ℝ) + m) * (m : ℝ) ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `eP : (C * s * f) ^ (6 * s * f) ≤ (Real.exp 1 * C * s * f) ^ (6 * s * f)`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises.

Establish `: (0:ℝ) ≤ (s : ℝ) * f` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `eE : Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) ≤ Real.exp (Real.exp 1 * C * (m : ℝ) ^ 6 * f * Real.log b)`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `: (0:ℝ) ≤ (m : ℝ) ^ 6 * f * Real.log b` using `by positivity`.

Use the polynomial consequences of the given equalities and inequalities. Establish `eQ : (C / k) ^ (k * f) ≤ (Real.exp 1 * C / k) ^ (k * f)`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Conclude with `div_le_div_of_nonneg_right hCD (Nat.cast_nonneg k)`. Establish `eG` using `gam_absorb hC0 hf hG (k := k)`.

Establish `hH0 : 0 ≤ bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2)` using `le_trans zero_le_one (Real.one_le_rpow hH1 (by positivity))`. Unfold `degRow`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem degRow_mono {C Gam : ℝ} (hC : 1 ≤ C) {k m f s : ℕ} {b g v : ℝ} {Xi : ℕ → ℝ}
    (hf : 1 ≤ f) (hb : 1 ≤ b) (hg : 0 < g) (hv : 0 ≤ v) (hXi : 0 ≤ Xi s)
    (hG : Gam ≤ Real.exp ((k : ℝ) / 8)) :
    degRow C k m f s b g v Gam Xi ≤ degRow (Real.exp 1 * C) k m f s b g v 1 Xi := by
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD0 : (0:ℝ) ≤ Real.exp 1 * C := by linarith
  have hH1 := bigH_one_le C hC0 m f hb
  have hHm := bigH_mono hC0 hCD m f hb
  have hHDpos : 0 < bigH (Real.exp 1 * C) m f b := lt_of_lt_of_le zero_lt_one (hH1.trans hHm)
  have hHCpos : 0 < bigH C m f b := lt_of_lt_of_le zero_lt_one hH1
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb
  have e0 : 0 ≤ (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s := by positivity
  have eH : bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) ≤
      bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) := by
    apply rpow_le_rpow_both hH1 hHm (by positivity)
    have : (0:ℝ) ≤ ((s : ℝ) + m) * (m : ℝ) ^ 2 := by positivity
    nlinarith
  have eP : (C * s * f) ^ (6 * s * f) ≤ (Real.exp 1 * C * s * f) ^ (6 * s * f) := by
    apply pow_le_pow_left₀ (by positivity)
    have : (0:ℝ) ≤ (s : ℝ) * f := by positivity
    nlinarith
  have eE : Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) ≤
      Real.exp (Real.exp 1 * C * (m : ℝ) ^ 6 * f * Real.log b) := by
    apply Real.exp_le_exp.2
    have : (0:ℝ) ≤ (m : ℝ) ^ 6 * f * Real.log b := by positivity
    nlinarith
  have eQ : (C / k) ^ (k * f) ≤ (Real.exp 1 * C / k) ^ (k * f) := by
    apply pow_le_pow_left₀ (by positivity)
    exact div_le_div_of_nonneg_right hCD (Nat.cast_nonneg k)
  have eG := gam_absorb hC0 hf hG (k := k)
  have hH0 : 0 ≤ bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) :=
    le_trans zero_le_one (Real.one_le_rpow hH1 (by positivity))
  unfold degRow
  calc (2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s * C ^ (k * f) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) * Gam *
        Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f)
      = ((2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (C ^ (k * f) * Gam) *
        bigH C m f b ^ (C * ((s : ℝ) + m) * (m : ℝ) ^ 2) * (C * s * f) ^ (6 * s * f) *
        Real.exp (C * (m : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (k * f) := by ring
    _ ≤ ((2 / g) ^ ((s - 2) * k * f) * ((k : ℝ) * v) ^ (k * f) * Xi s) * (Real.exp 1 * C) ^ (k * f) *
        bigH (Real.exp 1 * C) m f b ^ (Real.exp 1 * C * ((s : ℝ) + m) * (m : ℝ) ^ 2) *
        (Real.exp 1 * C * s * f) ^ (6 * s * f) *
        Real.exp (Real.exp 1 * C * (m : ℝ) ^ 6 * f * Real.log b) * (Real.exp 1 * C / k) ^ (k * f) := by
      gcongr
    _ = _ := by ring

end GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Deg

open Formalism.HermitianLatticeCounting.LatticeSumBounds in

/- English proof (translation)
Introduce `C hC`. Establish `hC0 : (0:ℝ) ≤ C` using `by linarith`. Establish `hCD : C ≤ Real.exp 1 * C` using `le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))`. Establish `hD : 1 ≤ Real.exp 1 * C` using `hC.trans hCD`. Take `⟨K1, H1⟩` from `Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe (Real.exp 1 * C) hD`.

Take `⟨K2, H2⟩` from `Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe (Real.exp 1 * C) hD`. Use `⟨max K1 K2, ?_⟩` and prove the remaining obligations. Introduce `k m f b g v NT Gam Xi hP hXi _hG0 hG`. Take `⟨hm4, hmf, hfk, hb2, hg8, -, hv1, -, hNT1, -⟩` from `id hP`. Establish `hb1 : (1:ℝ) ≤ b` using `by linarith`.

Establish `hf : 1 ≤ f` using `by omega`. Establish `hk : (1:ℝ) ≤ k` using `by exact_mod_cast (show 1 ≤ k by omega)`. Establish `hkb : 0 < (k:ℝ) * b` using `mul_pos (by linarith) (by linarith)`. Establish `hg : 0 < g` using `lt_of_lt_of_le (pow_pos hkb 8) hg8`. Establish `hv : (0:ℝ) ≤ v` using `by linarith`.

Establish `P1` using `params_mono hC hCD (le_max_left K1 K2) hP`. Establish `P2` using `params_mono hC hCD (le_max_right K1 K2) hP`. Establish `X'` using `xiHyp_mono hC hCD hb1 hNT1 hXi`. Establish `hXs : ∀ s ∈ Finset.Icc 2 k, 0 ≤ Xi s`. Introduce `s hs`.

Rewrite `hs` using `[Finset.mem_Icc]`. Distinguish the cases in `h2 : s + 2 ≤ k`. Conclude with `(hXi.1 s hs.1 h2).1`. Conclude with `(hXi.2 s (by omega)).1`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `le_trans (Finset.sum_le_sum fun s hs => ?_) (H1 k m f b g v NT 1 Xi P1 X')` and prove the remaining obligations. Conclude with `ndRow_mono hC hf hb1 hg hv (hXs s hs) hG`. Establish `E2` using `H2 k m f b g v NT 1 Xi P2 X'`. Rewrite `E2` using `[one_pow, inv_one, mul_one]`. Use `le_trans (Finset.sum_le_sum fun s hs => ?_) E2` and prove the remaining obligations.

Conclude with `degRow_mono hC hf hb1 hg hv (hXs s hs) hG`.
-/
theorem corankSums_expLoss : ∀ C : ℝ, 1 ≤ C → ∃ K₀ : ℝ, ∀ (k m f : ℕ) (b g v NT Gam : ℝ) (Xi : ℕ → ℝ),
    Formalism.HermitianLatticeCounting.LatticeSumBounds.Params C K₀ k m f b g v NT 1 → Formalism.HermitianLatticeCounting.LatticeSumBounds.XiHyp C k m f b v NT Xi → 0 ≤ Gam →
    Gam ≤ Real.exp ((k : ℝ) / 8) →
    ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.ndRow C k m f s b g v Gam Xi ≤ (Real.sqrt g)⁻¹ ^ (k * f) ∧
    ∑ s ∈ Finset.Icc 2 k, Formalism.HermitianLatticeCounting.LatticeSumBounds.degRow C k m f s b g v Gam Xi ≤
      Real.exp (-((k : ℝ) * f * Real.log k) / 2) := by
  intro C hC
  have hC0 : (0:ℝ) ≤ C := by linarith
  have hCD : C ≤ Real.exp 1 * C := le_mul_of_one_le_left hC0 (Real.one_le_exp (by norm_num))
  have hD : 1 ≤ Real.exp 1 * C := hC.trans hCD
  obtain ⟨K1, H1⟩ := Formalism.HermitianLatticeCounting.P.sumNondegenerateRowsLe (Real.exp 1 * C) hD
  obtain ⟨K2, H2⟩ := Formalism.HermitianLatticeCounting.P.sumDegenerateRowsLe (Real.exp 1 * C) hD
  refine ⟨max K1 K2, ?_⟩
  intro k m f b g v NT Gam Xi hP hXi _hG0 hG
  obtain ⟨hm4, hmf, hfk, hb2, hg8, -, hv1, -, hNT1, -⟩ := id hP
  have hb1 : (1:ℝ) ≤ b := by linarith
  have hf : 1 ≤ f := by omega
  have hk : (1:ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hkb : 0 < (k:ℝ) * b := mul_pos (by linarith) (by linarith)
  have hg : 0 < g := lt_of_lt_of_le (pow_pos hkb 8) hg8
  have hv : (0:ℝ) ≤ v := by linarith
  have P1 := params_mono hC hCD (le_max_left K1 K2) hP
  have P2 := params_mono hC hCD (le_max_right K1 K2) hP
  have X' := xiHyp_mono hC hCD hb1 hNT1 hXi
  have hXs : ∀ s ∈ Finset.Icc 2 k, 0 ≤ Xi s := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    by_cases h2 : s + 2 ≤ k
    · exact (hXi.1 s hs.1 h2).1
    · exact (hXi.2 s (by omega)).1
  refine ⟨?_, ?_⟩
  · refine le_trans (Finset.sum_le_sum fun s hs => ?_) (H1 k m f b g v NT 1 Xi P1 X')
    exact ndRow_mono hC hf hb1 hg hv (hXs s hs) hG
  · have E2 := H2 k m f b g v NT 1 Xi P2 X'
    rw [one_pow, inv_one, mul_one] at E2
    refine le_trans (Finset.sum_le_sum fun s hs => ?_) E2
    exact degRow_mono hC hf hb1 hg hv (hXs s hs) hG

end GlobalTheory.Core.Deg
