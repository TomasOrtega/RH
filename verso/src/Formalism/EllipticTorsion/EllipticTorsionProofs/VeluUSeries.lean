import Formalism.EllipticTorsion.VeluIntegralModel
import Formalism.EllipticTorsion.EllipticTorsionProofs.WPoint
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsParamDef

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace VeluCoordinateMaps

open Formalism.G

section Map

variable {K L : Type*} [Field K] [Field L] (f : K →+* L) (W : WeierstrassCurve K) (a b : K)

/- English proof (translation)
Simplify using `[veluGx, map_sub, map_add, map_mul, map_ofNat]`.
-/
theorem gx_map : veluGx (W.map f) (f a) (f b) = f (veluGx W a b) := by
  simp [veluGx, map_sub, map_add, map_mul, map_ofNat]

/- English proof (translation)
Simplify using `[veluGy, map_sub, map_mul, map_neg, map_ofNat]`.
-/
theorem gy_map : veluGy (W.map f) (f a) (f b) = f (veluGy W a b) := by
  simp [veluGy, map_sub, map_mul, map_neg, map_ofNat]

/- English proof (translation)
Unfold `veluV`. Rewrite using `[gx_map, gy_map]`. Distinguish the cases in `h : veluGy W a b = 0`. Rewrite using `[if_pos (by rw [h, map_zero]), if_pos h]`. Rewrite using `[if_neg (by rwa [map_eq_zero_iff f f.injective]), if_neg h]`.

Simplify using `[map_sub, map_mul, map_ofNat]`.
-/
theorem v_map : veluV (W.map f) (f a) (f b) = f (veluV W a b) := by
  unfold veluV
  rw [gx_map, gy_map]
  by_cases h : veluGy W a b = 0
  · rw [if_pos (by rw [h, map_zero]), if_pos h]
  · rw [if_neg (by rwa [map_eq_zero_iff f f.injective]), if_neg h]
    simp [map_sub, map_mul, map_ofNat]

/- English proof (translation)
Simplify using `[veluU, gy_map]`.
-/
theorem u_map : veluU (W.map f) (f a) (f b) = f (veluU W a b) := by
  simp [veluU, gy_map]

end Map

section Ball

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem {a : K} : a ∈ unitBall K ↔ ‖a‖ ≤ 1 := Iff.rfl

/- English proof (translation)
The claim follows from `mem.mpr FormalGroupPointsParam.norm_two_le`.
-/
theorem two_mem : (2 : K) ∈ unitBall K := mem.mpr FormalGroupPointsParam.norm_two_le

/- English proof (translation)
The claim follows from `mem.mpr FormalGroupPointsParam.norm_three_le`.
-/
theorem three_mem : (3 : K) ∈ unitBall K := mem.mpr FormalGroupPointsParam.norm_three_le

variable {W : WeierstrassCurve K} (hW : IntegralModel W) {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
include hW ha hb

/- English proof (translation)
Unfold `veluGx`. Conclude with `sub_mem (add_mem (add_mem (mul_mem three_mem (pow_mem (mem.mpr ha) 2)) (mul_mem (mul_mem two_mem (mem.mpr hW.2.1)) (mem.mpr ha))) (mem.mpr hW.2.2.2.1)) (mul_mem (mem.mpr hW.1) (mem.mpr hb))`.
-/
theorem gx_mem : veluGx W a b ∈ unitBall K := by
  unfold veluGx
  exact sub_mem (add_mem (add_mem (mul_mem three_mem (pow_mem (mem.mpr ha) 2))
    (mul_mem (mul_mem two_mem (mem.mpr hW.2.1)) (mem.mpr ha))) (mem.mpr hW.2.2.2.1))
    (mul_mem (mem.mpr hW.1) (mem.mpr hb))

/- English proof (translation)
Unfold `veluGy`. Conclude with `sub_mem (sub_mem (mul_mem (neg_mem two_mem) (mem.mpr hb)) (mul_mem (mem.mpr hW.1) (mem.mpr ha))) (mem.mpr hW.2.2.1)`.
-/
theorem gy_mem : veluGy W a b ∈ unitBall K := by
  unfold veluGy
  exact sub_mem (sub_mem (mul_mem (neg_mem two_mem) (mem.mpr hb)) (mul_mem (mem.mpr hW.1) (mem.mpr ha)))
    (mem.mpr hW.2.2.1)

/- English proof (translation)
Unfold `veluV`. Use `split_ifs`. Conclude with `gx_mem hW ha hb`. Conclude with `sub_mem (mul_mem two_mem (gx_mem hW ha hb)) (mul_mem (mem.mpr hW.1) (gy_mem hW ha hb))`.
-/
theorem v_mem : veluV W a b ∈ unitBall K := by
  unfold veluV
  split_ifs
  · exact gx_mem hW ha hb
  · exact sub_mem (mul_mem two_mem (gx_mem hW ha hb)) (mul_mem (mem.mpr hW.1) (gy_mem hW ha hb))

/- English proof (translation)
The claim follows from `pow_mem (gy_mem hW ha hb) 2`.
-/
theorem u_mem : veluU W a b ∈ unitBall K := pow_mem (gy_mem hW ha hb) 2

/- English proof (translation)
The claim follows from `sub_mem (mul_mem (mem.mpr hW.1) (u_mem hW ha hb)) (mul_mem (gx_mem hW ha hb) (gy_mem hW ha hb))`.
-/
theorem c_mem : W.a₁ * veluU W a b - veluGx W a b * veluGy W a b ∈ unitBall K :=
  sub_mem (mul_mem (mem.mpr hW.1) (u_mem hW ha hb)) (mul_mem (gx_mem hW ha hb) (gy_mem hW ha hb))

end Ball

section Terms

variable {F : Type*} [Field F]

/- English proof (translation)
Simplify using `only [div_eq_mul_inv, ← inv_pow, h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem termX (x xQ u Di v uQ : F) (h : (x - xQ)⁻¹ = u ^ 2 * Di) :
    (v / (x - xQ) + uQ / (x - xQ) ^ 2) * u ^ 2 = u ^ 4 * (v * Di + uQ * u ^ 2 * Di ^ 2) := by
  simp only [div_eq_mul_inv, ← inv_pow, h]
  ring

/- English proof (translation)
Simplify using `only [div_eq_mul_inv, ← inv_pow, h]`. Take the linear combination `(uQ * Di ^ 3 * a1 * u ^ 7 + v * Di ^ 2 * a1 * u ^ 5) * hx + (2 * uQ * Di ^ 3 * u ^ 6 + v * Di ^ 2 * u ^ 4) * hy`.
-/
theorem termY (x y xQ yQ u Di Ui v uQ c a1 a3 : F) (h : (x - xQ)⁻¹ = u ^ 2 * Di)
    (hx : x * u ^ 2 = Ui) (hy : y * u ^ 3 = -Ui) :
    (uQ * (2 * y + a1 * x + a3) / (x - xQ) ^ 3 + v * (a1 * (x - xQ) + y - yQ) / (x - xQ) ^ 2
        + c / (x - xQ) ^ 2) * u ^ 3 =
      u ^ 4 * (uQ * (-2 * Ui * u ^ 2 + a1 * Ui * u ^ 3 + a3 * u ^ 5) * Di ^ 3
        + v * (a1 * (Ui - xQ * u ^ 2) * u - Ui - yQ * u ^ 3) * Di ^ 2 + c * u ^ 3 * Di ^ 2) := by
  simp only [div_eq_mul_inv, ← inv_pow, h]
  linear_combination (uQ * Di ^ 3 * a1 * u ^ 7 + v * Di ^ 2 * a1 * u ^ 5) * hx
    + (2 * uQ * Di ^ 3 * u ^ 6 + v * Di ^ 2 * u ^ 4) * hy

end Terms

end VeluCoordinateMaps

open Formalism.G VeluCoordinateMaps in
/- English proof (translation)
Introduce `K _ _ W w k S hW hw hS L WL SL x y`. Set `φ : PowerSeries (unitBall K) →+* PowerSeries K` to `PowerSeries.map (unitBall K).subtype`. Set `ι : MvPowerSeries Unit K →+* L` to `algebraMap (MvPowerSeries Unit K) L`. Set `ψ : PowerSeries (unitBall K) →+* L` to `ι.comp φ`. Establish `hφcoeff : ∀ (g : PowerSeries (unitBall K)) (n : ℕ), coeff n (φ g) = ((coeff n g : unitBall K) : K)` using `fun g n => coeff_map _ n g`.

Establish `hψC : ∀ (a : K) (h : a ∈ unitBall K), ψ (C ⟨a, h⟩) = algebraMap K L a`. Introduce `a h`. Use `show ι (PowerSeries.map (unitBall K).subtype (C ⟨a, h⟩)) = _`. Rewrite using `[map_C]`. Use `show algebraMap (MvPowerSeries Unit K) L (C a) = _`.

Rewrite using `[C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]`. Take `⟨u, hu⟩ : ∃ u : L, ι (PowerSeries.X : PowerSeries K) = u` from `⟨_, rfl⟩`. Establish `hψX : ψ X = u` using `by show ι (PowerSeries.map (unitBall K).subtype X) = u`. Rewrite using `[map_X, hu]`. Establish `hinj : Function.Injective ι` using `IsFractionRing.injective _ _`.

Establish `hu0 : u ≠ 0`. Rewrite using `[← hu]`. Introduce `h`. Conclude with `PowerSeries.X_ne_zero (hinj (by rw [h, map_zero]))`. Take `⟨e, he⟩` from `WeierstrassPointSeriesTail.factor W w hw`.

Establish `hwI` using `FormalGroupPointsParam.integral_w hW hw`. Establish `hUI : ∀ n, ‖coeff n (1 + X * e)‖ ≤ 1`. Introduce `n`. Establish `h` using `coeff_X_pow_mul (1 + X * e) 3 n`. Rewrite `h` using `[← he]`.

Rewrite using `[← h]`. Conclude with `hwI _`. Take `⟨U', hU'⟩ : ∃ U' : PowerSeries (unitBall K), φ U' = 1 + X * e` from `⟨PowerSeries.mk fun n => ⟨coeff n (1 + X * e), mem.mpr (hUI n)⟩, by`. Use extensionality with `n`. Rewrite using `[hφcoeff, coeff_mk]⟩`.

Establish `hcU : constantCoeff U' = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h` using `hφcoeff U' 0`. Rewrite `h` using `[hU']`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, ← h]`.

Simplify using the standard rewrite rules. Take `⟨Ui', hUU'⟩ : ∃ Ui' : PowerSeries (unitBall K), U' * Ui' = 1` from `⟨invOfUnit U' 1, mul_invOfUnit _ _ (by rw [hcU]; rfl)⟩`. Establish `hcUi : constantCoeff Ui' = 1`. Establish `h` using `congrArg constantCoeff hUU'`. Rewrite `h` using `[map_mul, hcU, one_mul, map_one]`. Then use the resulting hypothesis.

Set `xq : Fin k → unitBall K` to `fun i => ⟨(S i).1, mem.mpr (hS i).1⟩`. Set `yq : Fin k → unitBall K` to `fun i => ⟨(S i).2, mem.mpr (hS i).2⟩`. Establish `hcD : ∀ i, constantCoeff (Ui' - C (xq i) * X ^ 2) = 1`. Introduce `i`. Rewrite using `[map_sub, map_mul, map_pow, constantCoeff_X, hcUi]`.

Simplify using the standard rewrite rules. Establish `hDex : ∀ i, ∃ D : PowerSeries (unitBall K), (Ui' - C (xq i) * X ^ 2) * D = 1` using `fun i => ⟨_, mul_invOfUnit (Ui' - C (xq i) * X ^ 2) 1 (by rw [hcD i]; rfl)⟩`. Use `choose Di hDD using hDex`. Set `a1' : unitBall K` to `⟨W.a₁, mem.mpr hW.1⟩`. Set `a3' : unitBall K` to `⟨W.a₃, mem.mpr hW.2.2.1⟩`.

Set `vq : Fin k → unitBall K` to `fun i => ⟨veluV W (S i).1 (S i).2, v_mem hW (hS i).1 (hS i).2⟩`. Set `uq : Fin k → unitBall K` to `fun i => ⟨veluU W (S i).1 (S i).2, u_mem hW (hS i).1 (hS i).2⟩`. Set `cq : Fin k → unitBall K` to `fun i => ⟨W.a₁ * veluU W (S i).1 (S i).2 - veluGx W (S i).1 (S i).2 * veluGy W (S i).1 (S i).2, c_mem hW (hS i).1 (hS i).2⟩`. Take `⟨EX, hEX⟩ : ∃ EX : PowerSeries (unitBall K), EX = Ui' + X ^ 4 * ∑ i, (C (vq i) * Di i + C (uq i) * X ^ 2 * Di i ^ 2)` from `⟨_, rfl⟩`. Take `⟨EY, hEY⟩ : ∃ EY : PowerSeries (unitBall K), EY = Ui' + X ^ 4 * ∑ i, (C (uq i) * (-2 * Ui' * X ^ 2 + C a1' * Ui' * X ^ 3 + C a3' * X ^ 5) * Di i ^ 3 + C (vq i) * (C a1' * (Ui' - C (xq i) * X ^ 2) * X - Ui' - C (yq i) * X ^ 3) * Di i ^ 2 + C (cq i) * X ^ 3 * Di i ^ 2)` from `⟨_, rfl⟩`.

Establish `hcEX : constantCoeff EX = 1` using `by simp [hEX, hcUi]`. Establish `hcEY : constantCoeff EY = 1` using `by simp [hEY, hcUi]`. Take `⟨EYi, hEE⟩ : ∃ EYi : PowerSeries (unitBall K), EY * EYi = 1` from `⟨invOfUnit EY 1, mul_invOfUnit _ _ (by rw [hcEY]; rfl)⟩`. Establish `hcEYi : constantCoeff EYi = 1`. Establish `h` using `congrArg constantCoeff hEE`.

Rewrite `h` using `[map_mul, hcEY, one_mul, map_one]`. Then use the resulting hypothesis. Use `⟨φ (X * EX * EYi), fun n => by rw [hφcoeff]; exact (coeff n (X * EX * EYi)).2, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hφcoeff, mul_assoc, coeff_zero_X_mul]`. Both sides reduce to the same expression. Rewrite using `[hφcoeff, mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, map_mul, hcEX, hcEYi, one_mul]`.

Both sides reduce to the same expression. Establish `hsub : w.subst (X : PowerSeries K) = w` using `X_subst w`. Establish `hιw : ι w = u ^ 3 * ψ U'` using `by show ι w = u ^ 3 * ι (φ U')`. Rewrite using `[hU', ← hu, ← map_pow, ← map_mul, ← he]`. Establish `hUUl : ψ U' * ψ Ui' = 1` using `by rw [← map_mul, hUU', map_one]`.

Establish `hU0 : ψ U' ≠ 0` using `left_ne_zero_of_mul_eq_one hUUl`. Establish `hu30 : u ^ 3 * ψ U' ≠ 0` using `mul_ne_zero (pow_ne_zero 3 hu0) hU0`. Establish `hx : x * u ^ 2 = ψ Ui'` using `by show ι (X : PowerSeries K) / ι (w.subst (X : PowerSeries K)) * u ^ 2 = ψ Ui'`. Rewrite using `[hsub, hιw, hu, div_mul_eq_mul_div, div_eq_iff hu30]`. Take the linear combination `(-u ^ 3) * hUUl`.

Establish `hy : y * u ^ 3 = -ψ Ui'` using `by show -1 / ι (w.subst (X : PowerSeries K)) * u ^ 3 = -ψ Ui'`. Rewrite using `[hsub, hιw, div_mul_eq_mul_div, div_eq_iff hu30]`. Take the linear combination `u ^ 3 * hUUl`. Establish `hxq : ∀ i, ψ (C (xq i)) = (SL i).1` using `fun i => hψC _ _`. Establish `hyq : ∀ i, ψ (C (yq i)) = (SL i).2` using `fun i => hψC _ _`.

Establish `hinv : ∀ i, (x - (SL i).1)⁻¹ = u ^ 2 * ψ (Di i)`. Introduce `i`. Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Establish `h` using `congrArg ψ (hDD i)`. Rewrite `h` using `[map_mul, map_sub, map_mul, map_pow, hψX, map_one, hxq]`.

Take the linear combination `ψ (Di i) * hx + h`. Establish `hv : ∀ i, veluV WL (SL i).1 (SL i).2 = ψ (C (vq i))` using `fun i => (v_map (algebraMap K L) W _ _).trans (hψC _ _).symm`. Establish `hU : ∀ i, veluU WL (SL i).1 (SL i).2 = ψ (C (uq i))` using `fun i => (u_map (algebraMap K L) W _ _).trans (hψC _ _).symm`. Establish `hc : ∀ i, WL.a₁ * veluU WL (SL i).1 (SL i).2 - veluGx WL (SL i).1 (SL i).2 * veluGy WL (SL i).1 (SL i).2 = ψ (C (cq i))`. Introduce `i`.

Rewrite using `[hψC, map_sub, map_mul, map_mul, ← u_map, ← gx_map, ← gy_map]`. Both sides reduce to the same expression. Establish `ha1 : WL.a₁ = ψ (C a1')` using `(hψC _ _).symm`. Establish `ha3 : WL.a₃ = ψ (C a3')` using `(hψC _ _).symm`. Establish `hXe : veluX WL SL x * u ^ 2 = ψ EX`.

Establish `e1 : ψ EX = ψ Ui' + u ^ 4 * ∑ i, (ψ (C (vq i)) * ψ (Di i) + ψ (C (uq i)) * u ^ 2 * ψ (Di i) ^ 2)`. Rewrite using `[hEX]`. Simplify using `only [map_add, map_mul, map_pow, map_sum, hψX]`. Rewrite using `[e1]`. Simplify using `only [veluX]`.

Rewrite using `[add_mul, Finset.sum_mul, hx, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[termX _ _ _ _ _ _ (hinv i), hv i, hU i]`. Establish `hYe : veluY WL SL x y * u ^ 3 = -ψ EY`.

Establish `e2 : ψ EY = ψ Ui' + u ^ 4 * ∑ i, (ψ (C (uq i)) * (-2 * ψ Ui' * u ^ 2 + ψ (C a1') * ψ Ui' * u ^ 3 + ψ (C a3') * u ^ 5) * ψ (Di i) ^ 3 + ψ (C (vq i)) * (ψ (C a1') * (ψ Ui' - ψ (C (xq i)) * u ^ 2) * u - ψ Ui' - ψ (C (yq i)) * u ^ 3) * ψ (Di i) ^ 2 + ψ (C (cq i)) * u ^ 3 * ψ (Di i) ^ …`. Rewrite using `[hEY]`. Simplify using `only [map_add, map_mul, map_pow, map_sum, map_sub, map_neg, map_ofNat, hψX]`. Establish `hs : ∀ i ∈ Finset.univ, (veluU WL (SL i).1 (SL i).2 * (2 * y + WL.a₁ * x + WL.a₃) / (x - (SL i).1) ^ 3 + veluV WL (SL i).1 (SL i).2 * (WL.a₁ * (x - (SL i).1) + y - (SL i).2) / (x - (SL i).1) ^ 2 + (WL.a₁ * veluU WL (SL i).1 (SL i).2 - veluGx WL (SL i).1 (SL i).2 * veluGy WL (SL i …`. Introduce `i _`.

Rewrite using `[termY _ _ _ _ _ _ _ _ _ _ _ _ (hinv i) hx hy, hc i, hv i, hU i, ha1, ha3, hxq i, hyq i]`. Rewrite using `[e2]`. Simplify using `only [veluY]`. Rewrite using `[sub_mul, Finset.sum_mul, Finset.sum_congr rfl hs, hy, ← Finset.mul_sum]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hEYl : ψ EY * ψ EYi = 1` using `by rw [← map_mul, hEE, map_one]`. Establish `hY0 : veluY WL SL x y ≠ 0`. Introduce `h`. Rewrite `hYe` using `[h, zero_mul]`. Establish `h2 : ψ EY = 0` using `by linear_combination hYe`.

Rewrite `hEYl` using `[h2, zero_mul]`. Conclude with `zero_ne_one hEYl`. Use `show ψ (X * EX * EYi) = _`. Rewrite using `[map_mul, map_mul, hψX, eq_div_iff hY0]`. Apply `mul_right_cancel₀ (pow_ne_zero 3 hu0)` to reduce the goal to its premises.

Take the linear combination `(u * ψ EX * ψ EYi) * hYe - (u * ψ EX) * hEYl + u * hXe`.
-/
theorem velu_u_series : VeluUSeries.{u} := by
  intro K _ _ W w k S hW hw hS L WL SL x y

  let φ : PowerSeries (unitBall K) →+* PowerSeries K := PowerSeries.map (unitBall K).subtype
  let ι : MvPowerSeries Unit K →+* L := algebraMap (MvPowerSeries Unit K) L
  let ψ : PowerSeries (unitBall K) →+* L := ι.comp φ
  have hφcoeff : ∀ (g : PowerSeries (unitBall K)) (n : ℕ), coeff n (φ g) = ((coeff n g : unitBall K) : K) :=
    fun g n => coeff_map _ n g
  have hψC : ∀ (a : K) (h : a ∈ unitBall K), ψ (C ⟨a, h⟩) = algebraMap K L a := by
    intro a h
    show ι (PowerSeries.map (unitBall K).subtype (C ⟨a, h⟩)) = _
    rw [map_C]
    show algebraMap (MvPowerSeries Unit K) L (C a) = _
    rw [C_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  obtain ⟨u, hu⟩ : ∃ u : L, ι (PowerSeries.X : PowerSeries K) = u := ⟨_, rfl⟩
  have hψX : ψ X = u := by
    show ι (PowerSeries.map (unitBall K).subtype X) = u
    rw [map_X, hu]
  have hinj : Function.Injective ι := IsFractionRing.injective _ _
  have hu0 : u ≠ 0 := by
    rw [← hu]; intro h
    exact PowerSeries.X_ne_zero (hinj (by rw [h, map_zero]))

  obtain ⟨e, he⟩ := WeierstrassPointSeriesTail.factor W w hw
  have hwI := FormalGroupPointsParam.integral_w hW hw
  have hUI : ∀ n, ‖coeff n (1 + X * e)‖ ≤ 1 := by
    intro n
    have h := coeff_X_pow_mul (1 + X * e) 3 n
    rw [← he] at h
    rw [← h]; exact hwI _
  obtain ⟨U', hU'⟩ : ∃ U' : PowerSeries (unitBall K), φ U' = 1 + X * e :=
    ⟨PowerSeries.mk fun n => ⟨coeff n (1 + X * e), mem.mpr (hUI n)⟩, by
      ext n; rw [hφcoeff, coeff_mk]⟩
  have hcU : constantCoeff U' = 1 := by
    apply Subtype.ext
    have h := hφcoeff U' 0
    rw [hU'] at h
    rw [← coeff_zero_eq_constantCoeff_apply, ← h]
    simp
  obtain ⟨Ui', hUU'⟩ : ∃ Ui' : PowerSeries (unitBall K), U' * Ui' = 1 :=
    ⟨invOfUnit U' 1, mul_invOfUnit _ _ (by rw [hcU]; rfl)⟩
  have hcUi : constantCoeff Ui' = 1 := by
    have h := congrArg constantCoeff hUU'
    rwa [map_mul, hcU, one_mul, map_one] at h

  let xq : Fin k → unitBall K := fun i => ⟨(S i).1, mem.mpr (hS i).1⟩
  let yq : Fin k → unitBall K := fun i => ⟨(S i).2, mem.mpr (hS i).2⟩
  have hcD : ∀ i, constantCoeff (Ui' - C (xq i) * X ^ 2) = 1 := by
    intro i
    rw [map_sub, map_mul, map_pow, constantCoeff_X, hcUi]
    simp
  have hDex : ∀ i, ∃ D : PowerSeries (unitBall K), (Ui' - C (xq i) * X ^ 2) * D = 1 :=
    fun i => ⟨_, mul_invOfUnit (Ui' - C (xq i) * X ^ 2) 1 (by rw [hcD i]; rfl)⟩
  choose Di hDD using hDex
  let a1' : unitBall K := ⟨W.a₁, mem.mpr hW.1⟩
  let a3' : unitBall K := ⟨W.a₃, mem.mpr hW.2.2.1⟩
  let vq : Fin k → unitBall K := fun i => ⟨veluV W (S i).1 (S i).2, v_mem hW (hS i).1 (hS i).2⟩
  let uq : Fin k → unitBall K := fun i => ⟨veluU W (S i).1 (S i).2, u_mem hW (hS i).1 (hS i).2⟩
  let cq : Fin k → unitBall K := fun i =>
    ⟨W.a₁ * veluU W (S i).1 (S i).2 - veluGx W (S i).1 (S i).2 * veluGy W (S i).1 (S i).2,
      c_mem hW (hS i).1 (hS i).2⟩
  obtain ⟨EX, hEX⟩ : ∃ EX : PowerSeries (unitBall K), EX = Ui' + X ^ 4 *
      ∑ i, (C (vq i) * Di i + C (uq i) * X ^ 2 * Di i ^ 2) := ⟨_, rfl⟩
  obtain ⟨EY, hEY⟩ : ∃ EY : PowerSeries (unitBall K), EY = Ui' + X ^ 4 *
      ∑ i, (C (uq i) * (-2 * Ui' * X ^ 2 + C a1' * Ui' * X ^ 3 + C a3' * X ^ 5) * Di i ^ 3
        + C (vq i) * (C a1' * (Ui' - C (xq i) * X ^ 2) * X - Ui' - C (yq i) * X ^ 3) * Di i ^ 2
        + C (cq i) * X ^ 3 * Di i ^ 2) := ⟨_, rfl⟩
  have hcEX : constantCoeff EX = 1 := by simp [hEX, hcUi]
  have hcEY : constantCoeff EY = 1 := by simp [hEY, hcUi]
  obtain ⟨EYi, hEE⟩ : ∃ EYi : PowerSeries (unitBall K), EY * EYi = 1 :=
    ⟨invOfUnit EY 1, mul_invOfUnit _ _ (by rw [hcEY]; rfl)⟩
  have hcEYi : constantCoeff EYi = 1 := by
    have h := congrArg constantCoeff hEE
    rwa [map_mul, hcEY, one_mul, map_one] at h
  refine ⟨φ (X * EX * EYi), fun n => by rw [hφcoeff]; exact (coeff n (X * EX * EYi)).2, ?_, ?_, ?_⟩
  · rw [hφcoeff, mul_assoc, coeff_zero_X_mul]; rfl
  · rw [hφcoeff, mul_assoc, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply, map_mul, hcEX, hcEYi, one_mul]
    rfl

  have hsub : w.subst (X : PowerSeries K) = w := X_subst w
  have hιw : ι w = u ^ 3 * ψ U' := by
    show ι w = u ^ 3 * ι (φ U')
    rw [hU', ← hu, ← map_pow, ← map_mul, ← he]
  have hUUl : ψ U' * ψ Ui' = 1 := by rw [← map_mul, hUU', map_one]
  have hU0 : ψ U' ≠ 0 := left_ne_zero_of_mul_eq_one hUUl
  have hu30 : u ^ 3 * ψ U' ≠ 0 := mul_ne_zero (pow_ne_zero 3 hu0) hU0
  have hx : x * u ^ 2 = ψ Ui' := by
    show ι (X : PowerSeries K) / ι (w.subst (X : PowerSeries K)) * u ^ 2 = ψ Ui'
    rw [hsub, hιw, hu, div_mul_eq_mul_div, div_eq_iff hu30]
    linear_combination (-u ^ 3) * hUUl
  have hy : y * u ^ 3 = -ψ Ui' := by
    show -1 / ι (w.subst (X : PowerSeries K)) * u ^ 3 = -ψ Ui'
    rw [hsub, hιw, div_mul_eq_mul_div, div_eq_iff hu30]
    linear_combination u ^ 3 * hUUl
  have hxq : ∀ i, ψ (C (xq i)) = (SL i).1 := fun i => hψC _ _
  have hyq : ∀ i, ψ (C (yq i)) = (SL i).2 := fun i => hψC _ _
  have hinv : ∀ i, (x - (SL i).1)⁻¹ = u ^ 2 * ψ (Di i) := by
    intro i
    apply inv_eq_of_mul_eq_one_right
    have h := congrArg ψ (hDD i)
    rw [map_mul, map_sub, map_mul, map_pow, hψX, map_one, hxq] at h
    linear_combination ψ (Di i) * hx + h
  have hv : ∀ i, veluV WL (SL i).1 (SL i).2 = ψ (C (vq i)) := fun i =>
    (v_map (algebraMap K L) W _ _).trans (hψC _ _).symm
  have hU : ∀ i, veluU WL (SL i).1 (SL i).2 = ψ (C (uq i)) := fun i =>
    (u_map (algebraMap K L) W _ _).trans (hψC _ _).symm
  have hc : ∀ i, WL.a₁ * veluU WL (SL i).1 (SL i).2
      - veluGx WL (SL i).1 (SL i).2 * veluGy WL (SL i).1 (SL i).2 = ψ (C (cq i)) := by
    intro i
    rw [hψC, map_sub, map_mul, map_mul, ← u_map, ← gx_map, ← gy_map]
    rfl
  have ha1 : WL.a₁ = ψ (C a1') := (hψC _ _).symm
  have ha3 : WL.a₃ = ψ (C a3') := (hψC _ _).symm
  have hXe : veluX WL SL x * u ^ 2 = ψ EX := by
    have e1 : ψ EX = ψ Ui' + u ^ 4 * ∑ i, (ψ (C (vq i)) * ψ (Di i)
        + ψ (C (uq i)) * u ^ 2 * ψ (Di i) ^ 2) := by
      rw [hEX]; simp only [map_add, map_mul, map_pow, map_sum, hψX]
    rw [e1]
    simp only [veluX]
    rw [add_mul, Finset.sum_mul, hx, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [termX _ _ _ _ _ _ (hinv i), hv i, hU i]
  have hYe : veluY WL SL x y * u ^ 3 = -ψ EY := by
    have e2 : ψ EY = ψ Ui' + u ^ 4 * ∑ i, (ψ (C (uq i)) * (-2 * ψ Ui' * u ^ 2
        + ψ (C a1') * ψ Ui' * u ^ 3 + ψ (C a3') * u ^ 5) * ψ (Di i) ^ 3
        + ψ (C (vq i)) * (ψ (C a1') * (ψ Ui' - ψ (C (xq i)) * u ^ 2) * u - ψ Ui'
          - ψ (C (yq i)) * u ^ 3) * ψ (Di i) ^ 2
        + ψ (C (cq i)) * u ^ 3 * ψ (Di i) ^ 2) := by
      rw [hEY]; simp only [map_add, map_mul, map_pow, map_sum, map_sub, map_neg, map_ofNat, hψX]
    have hs : ∀ i ∈ Finset.univ, (veluU WL (SL i).1 (SL i).2 * (2 * y + WL.a₁ * x + WL.a₃)
          / (x - (SL i).1) ^ 3
        + veluV WL (SL i).1 (SL i).2 * (WL.a₁ * (x - (SL i).1) + y - (SL i).2) / (x - (SL i).1) ^ 2
        + (WL.a₁ * veluU WL (SL i).1 (SL i).2
            - veluGx WL (SL i).1 (SL i).2 * veluGy WL (SL i).1 (SL i).2) / (x - (SL i).1) ^ 2)
          * u ^ 3 =
        u ^ 4 * (ψ (C (uq i)) * (-2 * ψ Ui' * u ^ 2
        + ψ (C a1') * ψ Ui' * u ^ 3 + ψ (C a3') * u ^ 5) * ψ (Di i) ^ 3
        + ψ (C (vq i)) * (ψ (C a1') * (ψ Ui' - ψ (C (xq i)) * u ^ 2) * u - ψ Ui'
          - ψ (C (yq i)) * u ^ 3) * ψ (Di i) ^ 2
        + ψ (C (cq i)) * u ^ 3 * ψ (Di i) ^ 2) := by
      intro i _
      rw [termY _ _ _ _ _ _ _ _ _ _ _ _ (hinv i) hx hy, hc i, hv i, hU i, ha1, ha3, hxq i, hyq i]
    rw [e2]
    simp only [veluY]
    rw [sub_mul, Finset.sum_mul, Finset.sum_congr rfl hs, hy, ← Finset.mul_sum]
    ring
  have hEYl : ψ EY * ψ EYi = 1 := by rw [← map_mul, hEE, map_one]
  have hY0 : veluY WL SL x y ≠ 0 := by
    intro h
    rw [h, zero_mul] at hYe
    have h2 : ψ EY = 0 := by linear_combination hYe
    rw [h2, zero_mul] at hEYl
    exact zero_ne_one hEYl
  show ψ (X * EX * EYi) = _
  rw [map_mul, map_mul, hψX, eq_div_iff hY0]
  apply mul_right_cancel₀ (pow_ne_zero 3 hu0)
  linear_combination (u * ψ EX * ψ EYi) * hYe - (u * ψ EX) * hEYl + u * hXe

end Formalism.ELL
