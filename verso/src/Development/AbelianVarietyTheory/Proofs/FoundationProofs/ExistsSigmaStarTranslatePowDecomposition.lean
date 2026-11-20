import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqThD
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsAnalyticOfTendsto
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open GlobalTheory.EvenTheta GlobalTheory.ThetaTransl

open Filter
open scoped Topology

noncomputable section

namespace GlobalTheory.ThetaTranslDecomp

variable {Λ : AddSubgroup ℂ}

/- English proof (translation)
Simplify using `only [U1, one_mul]`.
-/
private lemma u1_apply_eq_mul_u1_one (ω : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω G z = G (z + ω) * U1 Λ ω (fun _ => (1 : ℂ)) z := by
  simp only [U1, one_mul]

/- English proof (translation)
Simplify using `only [U1, one_mul]`. Conclude with `Complex.exp_ne_zero _`.
-/
private lemma u1_one_ne_zero (ω z : ℂ) : U1 Λ ω (fun _ => (1 : ℂ)) z ≠ 0 := by
  simp only [U1, one_mul]
  exact Complex.exp_ne_zero _

/- English proof (translation)
Simplify using `only [U1, one_mul, ← Complex.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma u1_one_add_mul_comm_cexp (a b z : ℂ) :
    U1 Λ a (fun _ => (1 : ℂ)) (z + b) * U1 Λ b (fun _ => (1 : ℂ)) z =
      U1 Λ a (fun _ => (1 : ℂ)) z * U1 Λ b (fun _ => (1 : ℂ)) (z + a) *
        Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ)) := by
  simp only [U1, one_mul, ← Complex.exp_add]
  congr 1
  ring

/- English proof (translation)
Simplify using `only [U1, one_mul, ← Complex.exp_add, map_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma u1_one_add_mul_eq_u1_one_add_mul_cexp (a b z : ℂ) :
    U1 Λ a (fun _ => (1 : ℂ)) (z + b) * U1 Λ b (fun _ => (1 : ℂ)) z =
      U1 Λ (a + b) (fun _ => (1 : ℂ)) z *
        Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) := by
  simp only [U1, one_mul, ← Complex.exp_add, map_add]
  congr 1
  ring

/- English proof (translation)
Take `⟨z0, hz0⟩` from `hΛ.dense_compl.nonempty`. Establish `hs0 : sgStar Λ z0 ≠ 0` using `fun h0 => hz0 ((hΛ.sg_eq_zero z0).1 h0)`. Establish `hsq : ∀ c : ℂ, (if c / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 = 1`. Introduce `c`. Apply the tactic sequence `split_ifs <;> norm_num`.

Establish `l1` using `hΛ.sg_law (add_mem ha hb) z0`. Establish `l2` using `hΛ.sg_law ha (z0 + b)`. Establish `l3` using `hΛ.sg_law hb z0`. Rewrite `l1`, `l2`, `l3` using `[u1_apply_eq_mul_u1_one]`. Establish `key : (if (a + b) / 2 ∈ Λ then (1 : ℂ) else -1) * Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) = (if a / 2 ∈ Λ then (1 : ℂ) else -1) * (if b / 2 ∈ Λ then (1 : ℂ) else -1)`.

Apply `mul_right_cancel₀ hs0` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[l1]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = sgStar Λ (z0 + b + a) * (U1 Λ a (fun _ => (1 : ℂ)) (z0 + b) * U1 Λ b (fun _ => (1 : ℂ)) z0) := by`.

Rewrite using `[u1_one_add_mul_eq_u1_one_add_mul_cexp, show z0 + b + a = z0 + (a + b) by ring]; ring`. Use `_ = _ := by rw [← mul_assoc, l2, mul_assoc, l3]; ring`. Establish `h2 : Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) ^ 2 = 1`. Use `congrArg (· ^ 2) key` as an intermediate fact. Simplify using `only [mul_pow, hsq, one_mul] at this`.

Conclude with `this`. Rewrite using `[show (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ) = (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ)) + (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ)) by ring, Complex.exp_ …`.
-/
private lemma cexp_pi_mul_conj_sub_div_area_eq_one_of_mem (hΛ : IsLat Λ) {a b : ℂ} (ha : a ∈ Λ) (hb : b ∈ Λ) :
    Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ)) = 1 := by
  obtain ⟨z0, hz0⟩ := hΛ.dense_compl.nonempty
  have hs0 : sgStar Λ z0 ≠ 0 := fun h0 => hz0 ((hΛ.sg_eq_zero z0).1 h0)
  have hsq : ∀ c : ℂ, (if c / 2 ∈ Λ then (1 : ℂ) else -1) ^ 2 = 1 := by
    intro c
    split_ifs <;> norm_num
  have l1 := hΛ.sg_law (add_mem ha hb) z0
  have l2 := hΛ.sg_law ha (z0 + b)
  have l3 := hΛ.sg_law hb z0
  rw [u1_apply_eq_mul_u1_one] at l1 l2 l3
  have key : (if (a + b) / 2 ∈ Λ then (1 : ℂ) else -1) *
      Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) =
      (if a / 2 ∈ Λ then (1 : ℂ) else -1) * (if b / 2 ∈ Λ then (1 : ℂ) else -1) := by
    apply mul_right_cancel₀ hs0
    calc _ = sgStar Λ (z0 + (a + b)) * U1 Λ (a + b) (fun _ => (1 : ℂ)) z0 *
          Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ))) := by
          rw [l1]; ring
      _ = sgStar Λ (z0 + b + a) * (U1 Λ a (fun _ => (1 : ℂ)) (z0 + b) * U1 Λ b (fun _ => (1 : ℂ)) z0) := by
          rw [u1_one_add_mul_eq_u1_one_add_mul_cexp, show z0 + b + a = z0 + (a + b) by ring]; ring
      _ = _ := by rw [← mul_assoc, l2, mul_assoc, l3]; ring
  have h2 : Complex.exp ((Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) /
      (2 * (area Λ : ℂ))) ^ 2 = 1 := by
    have := congrArg (· ^ 2) key
    simp only [mul_pow, hsq, one_mul] at this
    exact this
  rw [show (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (area Λ : ℂ) =
      (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ)) +
      (Real.pi : ℂ) * (a * (starRingEnd ℂ) b - b * (starRingEnd ℂ) a) / (2 * (area Λ : ℂ)) by ring,
    Complex.exp_add, ← sq, h2]

/- English proof (translation)
Distinguish the cases in `hz : z ∈ Λ`. Establish `h1 : sgStar Λ z = 0` using `(hΛ.sg_eq_zero z).2 hz`. Establish `h2 : sgStar Λ (z + l) = 0` using `(hΛ.sg_eq_zero _).2 (add_mem hz hl)`. Rewrite using `[h1, h2, div_zero, div_zero]`. Establish `hs : sgStar Λ z ≠ 0` using `fun h0 => hz ((hΛ.sg_eq_zero z).1 h0)`.

Establish `hzl : z + l ∉ Λ` using `fun h' => hz (by simpa using sub_mem h' hl)`. Establish `hsl : sgStar Λ (z + l) ≠ 0` using `fun h0 => hzl ((hΛ.sg_eq_zero _).1 h0)`. Apply the tactic sequence `have hsn : (if l / 2 ∈ Λ then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num`. Establish `la` using `hΛ.sg_law hl (z + t)`. Establish `lb` using `hΛ.sg_law hl z`.

Rewrite `la`, `lb` using `[u1_apply_eq_mul_u1_one]`. Establish `hK` using `u1_one_add_mul_comm_cexp (Λ := Λ) t l z`. Establish `e3` using `u1_one_ne_zero (Λ := Λ) l z`. Establish `e4` using `u1_one_ne_zero (Λ := Λ) l (z + t)`. Establish `hA : sgStar Λ (z + l + t) = (if l / 2 ∈ Λ then (1 : ℂ) else -1) * sgStar Λ (z + t) / U1 Λ l (fun _ => (1 : ℂ)) (z + t)`.

Rewrite using `[eq_div_iff e4, show z + l + t = z + t + l by ring]`. Conclude with `la`. Establish `hB : sgStar Λ (z + l) = (if l / 2 ∈ Λ then (1 : ℂ) else -1) * sgStar Λ z / U1 Λ l (fun _ => (1 : ℂ)) z`. Rewrite using `[eq_div_iff e3]`. Conclude with `lb`.

Establish `hF : U1 Λ t (fun _ => (1 : ℂ)) (z + l) = U1 Λ t (fun _ => (1 : ℂ)) z * U1 Λ l (fun _ => (1 : ℂ)) (z + t) * Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) / U1 Λ l (fun _ => (1 : ℂ)) z`. Rewrite using `[eq_div_iff e3]`. Conclude with `hK`. Establish `hbase : U1 Λ t (sgStar Λ) (z + l) / sgStar Λ (z + l) = U1 Λ t (sgStar Λ) z / sgStar Λ z * Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ))`. Rewrite using `[u1_apply_eq_mul_u1_one, u1_apply_eq_mul_u1_one t (sgStar Λ) z, hA, hF, hB]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hbase, mul_pow, ← Complex.exp_nat_mul, show (N : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) = (Real.pi : ℂ) * ((N : ℂ) * t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) ((N : ℂ) * t)) / (area Λ : ℂ) by`. Rewrite using `[map_mul, map_natCast]`. Use the proof step `ring,`. Use `cexp_pi_mul_conj_sub_div_area_eq_one_of_mem hΛ ht hl, mul_one]`.
-/
theorem ratio_pow_add (hΛ : IsLat Λ) {t : ℂ} {N : ℕ} (hN : 0 < N) (ht : (N : ℂ) * t ∈ Λ)
    (z : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    (U1 Λ t (sgStar Λ) (z + l) / sgStar Λ (z + l)) ^ N = (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N := by
  by_cases hz : z ∈ Λ
  · have h1 : sgStar Λ z = 0 := (hΛ.sg_eq_zero z).2 hz
    have h2 : sgStar Λ (z + l) = 0 := (hΛ.sg_eq_zero _).2 (add_mem hz hl)
    rw [h1, h2, div_zero, div_zero]
  · have hs : sgStar Λ z ≠ 0 := fun h0 => hz ((hΛ.sg_eq_zero z).1 h0)
    have hzl : z + l ∉ Λ := fun h' => hz (by simpa using sub_mem h' hl)
    have hsl : sgStar Λ (z + l) ≠ 0 := fun h0 => hzl ((hΛ.sg_eq_zero _).1 h0)
    have hsn : (if l / 2 ∈ Λ then (1 : ℂ) else -1) ≠ 0 := by split_ifs <;> norm_num
    have la := hΛ.sg_law hl (z + t)
    have lb := hΛ.sg_law hl z
    rw [u1_apply_eq_mul_u1_one] at la lb
    have hK := u1_one_add_mul_comm_cexp (Λ := Λ) t l z
    have e3 := u1_one_ne_zero (Λ := Λ) l z
    have e4 := u1_one_ne_zero (Λ := Λ) l (z + t)
    have hA : sgStar Λ (z + l + t) = (if l / 2 ∈ Λ then (1 : ℂ) else -1) * sgStar Λ (z + t) /
        U1 Λ l (fun _ => (1 : ℂ)) (z + t) := by
      rw [eq_div_iff e4, show z + l + t = z + t + l by ring]
      exact la
    have hB : sgStar Λ (z + l) = (if l / 2 ∈ Λ then (1 : ℂ) else -1) * sgStar Λ z /
        U1 Λ l (fun _ => (1 : ℂ)) z := by
      rw [eq_div_iff e3]
      exact lb
    have hF : U1 Λ t (fun _ => (1 : ℂ)) (z + l) = U1 Λ t (fun _ => (1 : ℂ)) z *
        U1 Λ l (fun _ => (1 : ℂ)) (z + t) *
        Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) /
        U1 Λ l (fun _ => (1 : ℂ)) z := by
      rw [eq_div_iff e3]
      exact hK
    have hbase : U1 Λ t (sgStar Λ) (z + l) / sgStar Λ (z + l) = U1 Λ t (sgStar Λ) z / sgStar Λ z *
        Complex.exp ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) := by
      rw [u1_apply_eq_mul_u1_one, u1_apply_eq_mul_u1_one t (sgStar Λ) z, hA, hF, hB]
      field_simp
    rw [hbase, mul_pow, ← Complex.exp_nat_mul,
      show (N : ℂ) * ((Real.pi : ℂ) * (t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) t) / (area Λ : ℂ)) =
        (Real.pi : ℂ) * ((N : ℂ) * t * (starRingEnd ℂ) l - l * (starRingEnd ℂ) ((N : ℂ) * t)) / (area Λ : ℂ) by
        rw [map_mul, map_natCast]; ring,
      cexp_pi_mul_conj_sub_div_area_eq_one_of_mem hΛ ht hl, mul_one]

/- English proof (translation)
Establish `hU : IsOpen (L.lattice : Set ℂ)ᶜ` using `L.isClosed_lattice.isOpen_compl`. Establish `hzL : z ∉ L.lattice` using `fun hz' => hz ((h z).2 hz')`. Establish `hev : sqTh Λ v =ᶠ[𝓝 z] fun w => sgStar Λ w ^ 2 * (L.weierstrassP w - L.weierstrassP v)` using `by filter_upwards [hU.mem_nhds hzL] with w hw`. Establish `hwΛ : w ∉ Λ` using `fun h' => hw ((h w).1 h')`. Rewrite using `[hΛ.sqTh_eq hv hwΛ, GlobalTheory.OddTheta.wpF_eq L Λ h, GlobalTheory.OddTheta.wpF_eq L Λ h]`.

Establish `hsg : HasDerivAt (sgStar Λ) (deriv (sgStar Λ) z) z` using `(hΛ.differentiable z).hasDerivAt`. Establish `hwp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z`. Establish `hd : DifferentiableAt ℂ L.weierstrassP z` using `(L.analyticOnNhd_weierstrassP z hzL).differentiableAt`. Use `hd.hasDerivAt` as an intermediate fact. Rewrite `this` using `[L.deriv_weierstrassP]`. Then use the resulting hypothesis.

Establish `hD : HasDerivAt (fun w => sgStar Λ w ^ 2 * (L.weierstrassP w - L.weierstrassP v)) _ z` using `(hsg.pow 2).mul (hwp.sub_const (L.weierstrassP v))`. Unfold `sqThD`. Rewrite using `[hev.deriv_eq, hD.deriv, hΛ.sqTh_eq hv hz, GlobalTheory.OddTheta.wpF_eq L Λ h, GlobalTheory.OddTheta.wpF_eq L Λ h]`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqThD_eq (hΛ : IsLat Λ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {v z : ℂ}
    (hv : v ∉ Λ) (hz : z ∉ Λ) : sqThD Λ v z = sgStar Λ z ^ 3 * L.derivWeierstrassP z := by
  have hU : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hzL : z ∉ L.lattice := fun hz' => hz ((h z).2 hz')
  have hev : sqTh Λ v =ᶠ[𝓝 z] fun w => sgStar Λ w ^ 2 * (L.weierstrassP w - L.weierstrassP v) := by
    filter_upwards [hU.mem_nhds hzL] with w hw
    have hwΛ : w ∉ Λ := fun h' => hw ((h w).1 h')
    rw [hΛ.sqTh_eq hv hwΛ, GlobalTheory.OddTheta.wpF_eq L Λ h, GlobalTheory.OddTheta.wpF_eq L Λ h]
  have hsg : HasDerivAt (sgStar Λ) (deriv (sgStar Λ) z) z := (hΛ.differentiable z).hasDerivAt
  have hwp : HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    have hd : DifferentiableAt ℂ L.weierstrassP z :=
      (L.analyticOnNhd_weierstrassP z hzL).differentiableAt
    have := hd.hasDerivAt
    rwa [L.deriv_weierstrassP] at this
  have hD : HasDerivAt (fun w => sgStar Λ w ^ 2 * (L.weierstrassP w - L.weierstrassP v)) _ z :=
    (hsg.pow 2).mul (hwp.sub_const (L.weierstrassP v))
  unfold sqThD
  rw [hev.deriv_eq, hD.deriv, hΛ.sqTh_eq hv hz,
    GlobalTheory.OddTheta.wpF_eq L Λ h, GlobalTheory.OddTheta.wpF_eq L Λ h]
  norm_num
  ring

/- English proof (translation)
Introduce `Λ hΛ t N hN ht v hv`. Take `⟨L, hL⟩` from `GlobalTheory.OddTheta.exists_periodPair Λ hΛ`. Establish `hσ : Differentiable ℂ (sgStar Λ)` using `hΛ.differentiable`. Establish `hσ0 : ∀ w, sgStar Λ w = 0 ↔ w ∈ Λ` using `hΛ.sg_eq_zero`. Establish `hU : Differentiable ℂ (U1 Λ t (sgStar Λ))`.

Unfold `U1`. Use `fun_prop`. Establish `hmer : Meromorphic (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N)` using `fun x => ((hU.analyticAt x).meromorphicAt.div (hσ.analyticAt x).meromorphicAt).pow N`. Establish `hcont : ∀ a, a ∉ Λ → ContinuousAt (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) a` using `fun a ha => ((hU a).continuousAt.div (hσ a).continuousAt (fun h0 => ha ((hσ0 a).1 h0))).pow N`. Establish `hd : ∀ a ∉ L.lattice, ∃ c, Tendsto (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) (𝓝[≠] a) (𝓝 c)` using `fun a ha => ⟨_, (hcont a (fun h' => ha ((hL a).1 h'))).tendsto.mono_left nhdsWithin_le_nhds⟩`.

Establish `hp : ∀ z, ∀ l ∈ L.lattice, (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) (z + l) = (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) z` using `fun z l hl => ratio_pow_add hΛ hN ht z ((hL l).2 hl)`. Take `⟨A, B, hAB⟩` from `GlobalTheory.EllipticPoles.no_pole_case L hmer hd hp`. Establish `hpt : ∀ z, z ∉ Λ → (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N = A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z`. Introduce `z hzΛ`. Establish `hz : z ∉ L.lattice` using `fun h' => hzΛ ((hL z).2 h')`.

Establish `t1` using `(hcont z hzΛ).tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))`. Establish `hc2 : ContinuousAt (fun w => A.eval (L.weierstrassP w) + B.eval (L.weierstrassP w) * L.derivWeierstrassP w) z` using `(A.continuous.continuousAt.comp (L.analyticOnNhd_weierstrassP z hz).continuousAt).add ((B.continuous.continuousAt.comp (L.analyticOnNhd_weierstrassP z hz).continuousAt).mul (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt)`. Conclude with `tendsto_nhds_unique (t1.congr' (hAB z)) (hc2.tendsto.mono_left nhdsWithin_le_nhds)`. Establish `hS : Differentiable ℂ (sqTh Λ v)` using `hΛ.differentiable_sqTh v`. Establish `hdS : Continuous (deriv (sqTh Λ v))` using `(hS.contDiff (n := 1)).continuous_deriv le_rfl`.

Establish `hdσ : Continuous (deriv (sgStar Λ))` using `(hσ.contDiff (n := 1)).continuous_deriv le_rfl`. Establish `hT : Continuous (sqThD Λ v)`. Unfold `sqThD`. Conclude with `(hσ.continuous.mul hdS).sub ((continuous_const.mul hdσ).mul hS.continuous)`. Use `set P := A.comp (Polynomial.X + Polynomial.C (L.weierstrassP v)) with hP`.

Use `set Q := B.comp (Polynomial.X + Polynomial.C (L.weierstrassP v)) with hQ`. Use `⟨max (max P.natDegree Q.natDegree) N, fun i => P.coeff i, fun j => Q.coeff j, ?_, ?_⟩` and prove the remaining obligations. Use `le_max_right (max P.natDegree Q.natDegree) N` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hIP : P.natDegree < max (max P.natDegree Q.natDegree) N + 1`.

Use `le_max_left (max P.natDegree Q.natDegree) N` as an intermediate fact. Use `le_max_left P.natDegree Q.natDegree` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hIQ : Q.natDegree < max (max P.natDegree Q.natDegree) N + 1`. Use `le_max_left (max P.natDegree Q.natDegree) N` as an intermediate fact.

Use `le_max_right P.natDegree Q.natDegree` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hNI : N ≤ 2 * max (max P.natDegree Q.natDegree) N + 3`. Use `le_max_right (max P.natDegree Q.natDegree) N` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Generalize the expression as in `max (max P.natDegree Q.natDegree) N = I at hIP hIQ hNI ⊢`. Establish `heq : (fun z => sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N) = fun z => ∑ i ∈ Finset.range (I + 1), P.coeff i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) + ∑ j ∈ Finset.range (I + 1), Q.coeff j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z)`. Use `Continuous.ext_on hΛ.dense_compl ((hσ.continuous.pow _).mul (hU.continuous.pow _)) ((continuous_finsetSum _ fun i _ => continuous_const.mul ((hσ.continuous.pow _).mul (hS.continuous.pow _))).add (continuous_finsetSum _ fun j _ => continuous_const.mul (((hσ.continuous.pow _).mul ( …` and prove the remaining obligations. Introduce `z hz`. Establish `hzΛ : z ∉ Λ` using `hz`.

Establish `hs : sgStar Λ z ≠ 0` using `fun h0 => hzΛ ((hσ0 z).1 h0)`. Establish `hz' : z ∉ L.lattice` using `fun h' => hzΛ ((hL z).2 h')`. Establish `hq` using `hpt z hzΛ`. Establish `hApt : A.eval (L.weierstrassP z) = P.eval (L.weierstrassP z - L.weierstrassP v)`. Rewrite using `[hP, Polynomial.eval_comp]`.

Simplify using the standard rewrite rules. Establish `hBpt : B.eval (L.weierstrassP z) = Q.eval (L.weierstrassP z - L.weierstrassP v)`. Rewrite using `[hQ, Polynomial.eval_comp]`. Simplify using the standard rewrite rules. Rewrite `hq` using `[hApt, hBpt, Polynomial.eval_eq_sum_range' hIP, Polynomial.eval_eq_sum_range' hIQ]`.

Establish `hUN : U1 Λ t (sgStar Λ) z ^ N = sgStar Λ z ^ N * (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N`. Rewrite using `[div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hs)]`. Simplify using `only`. Rewrite using `[hUN, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hNI, hq, sqThD_eq hΛ L hL hv hzΛ, hΛ.sqTh_eq hv hzΛ, GlobalTheory.OddTheta.wpF_eq L Λ hL, GlobalTheory.OddTheta.wpF_eq L Λ hL, mul_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hi' : i ≤ I` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Rewrite using `[mul_pow, ← pow_mul, show 2 * I + 3 = (2 * (I - i) + 3) + 2 * i by omega]`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations.

Establish `hj' : j ≤ I` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`. Rewrite using `[mul_pow, ← pow_mul, show 2 * I + 3 = 2 * (I - j) + 2 * j + 3 by omega]`. Expand and normalize the polynomial expressions, which then agree. Introduce `z`. Conclude with `congrFun heq z`.
-/
theorem exists_decomp : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (t : ℂ) (N : ℕ), 0 < N → (N : ℂ) * t ∈ Λ →
    ∀ v : ℂ, v ∉ Λ → ∃ (I : ℕ) (a b : ℕ → ℂ), N ≤ 2 * I + 3 ∧
      ∀ z, sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N =
        ∑ i ∈ Finset.range (I + 1), a i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), b j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
  intro Λ hΛ t N hN ht v hv
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have hσ : Differentiable ℂ (sgStar Λ) := hΛ.differentiable
  have hσ0 : ∀ w, sgStar Λ w = 0 ↔ w ∈ Λ := hΛ.sg_eq_zero
  have hU : Differentiable ℂ (U1 Λ t (sgStar Λ)) := by
    unfold U1
    fun_prop
  have hmer : Meromorphic (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) := fun x =>
    ((hU.analyticAt x).meromorphicAt.div (hσ.analyticAt x).meromorphicAt).pow N
  have hcont : ∀ a, a ∉ Λ → ContinuousAt (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) a :=
    fun a ha => ((hU a).continuousAt.div (hσ a).continuousAt (fun h0 => ha ((hσ0 a).1 h0))).pow N
  have hd : ∀ a ∉ L.lattice, ∃ c, Tendsto (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) (𝓝[≠] a) (𝓝 c) :=
    fun a ha => ⟨_, (hcont a (fun h' => ha ((hL a).1 h'))).tendsto.mono_left nhdsWithin_le_nhds⟩
  have hp : ∀ z, ∀ l ∈ L.lattice, (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) (z + l) =
      (fun z => (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N) z :=
    fun z l hl => ratio_pow_add hΛ hN ht z ((hL l).2 hl)
  obtain ⟨A, B, hAB⟩ := GlobalTheory.EllipticPoles.no_pole_case L hmer hd hp
  have hpt : ∀ z, z ∉ Λ → (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N =
      A.eval (L.weierstrassP z) + B.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    intro z hzΛ
    have hz : z ∉ L.lattice := fun h' => hzΛ ((hL z).2 h')
    have t1 := (hcont z hzΛ).tendsto.mono_left (nhdsWithin_le_nhds (s := {z}ᶜ))
    have hc2 : ContinuousAt (fun w => A.eval (L.weierstrassP w) + B.eval (L.weierstrassP w) * L.derivWeierstrassP w) z :=
      (A.continuous.continuousAt.comp (L.analyticOnNhd_weierstrassP z hz).continuousAt).add
        ((B.continuous.continuousAt.comp (L.analyticOnNhd_weierstrassP z hz).continuousAt).mul
          (L.analyticOnNhd_derivWeierstrassP z hz).continuousAt)
    exact tendsto_nhds_unique (t1.congr' (hAB z)) (hc2.tendsto.mono_left nhdsWithin_le_nhds)
  have hS : Differentiable ℂ (sqTh Λ v) := hΛ.differentiable_sqTh v
  have hdS : Continuous (deriv (sqTh Λ v)) := (hS.contDiff (n := 1)).continuous_deriv le_rfl
  have hdσ : Continuous (deriv (sgStar Λ)) := (hσ.contDiff (n := 1)).continuous_deriv le_rfl
  have hT : Continuous (sqThD Λ v) := by
    unfold sqThD
    exact (hσ.continuous.mul hdS).sub ((continuous_const.mul hdσ).mul hS.continuous)
  set P := A.comp (Polynomial.X + Polynomial.C (L.weierstrassP v)) with hP
  set Q := B.comp (Polynomial.X + Polynomial.C (L.weierstrassP v)) with hQ
  refine ⟨max (max P.natDegree Q.natDegree) N, fun i => P.coeff i, fun j => Q.coeff j, ?_, ?_⟩
  · have := le_max_right (max P.natDegree Q.natDegree) N
    omega
  have hIP : P.natDegree < max (max P.natDegree Q.natDegree) N + 1 := by
    have := le_max_left (max P.natDegree Q.natDegree) N
    have := le_max_left P.natDegree Q.natDegree
    omega
  have hIQ : Q.natDegree < max (max P.natDegree Q.natDegree) N + 1 := by
    have := le_max_left (max P.natDegree Q.natDegree) N
    have := le_max_right P.natDegree Q.natDegree
    omega
  have hNI : N ≤ 2 * max (max P.natDegree Q.natDegree) N + 3 := by
    have := le_max_right (max P.natDegree Q.natDegree) N
    omega
  generalize max (max P.natDegree Q.natDegree) N = I at hIP hIQ hNI ⊢
  have heq : (fun z => sgStar Λ z ^ (2 * I + 3 - N) * U1 Λ t (sgStar Λ) z ^ N) =
      fun z => ∑ i ∈ Finset.range (I + 1), P.coeff i * (sgStar Λ z ^ (2 * (I - i) + 3) * sqTh Λ v z ^ i) +
        ∑ j ∈ Finset.range (I + 1), Q.coeff j * (sgStar Λ z ^ (2 * (I - j)) * sqTh Λ v z ^ j * sqThD Λ v z) := by
    refine Continuous.ext_on hΛ.dense_compl ((hσ.continuous.pow _).mul (hU.continuous.pow _))
      ((continuous_finsetSum _ fun i _ => continuous_const.mul ((hσ.continuous.pow _).mul (hS.continuous.pow _))).add
        (continuous_finsetSum _ fun j _ =>
          continuous_const.mul (((hσ.continuous.pow _).mul (hS.continuous.pow _)).mul hT))) ?_
    intro z hz
    have hzΛ : z ∉ Λ := hz
    have hs : sgStar Λ z ≠ 0 := fun h0 => hzΛ ((hσ0 z).1 h0)
    have hz' : z ∉ L.lattice := fun h' => hzΛ ((hL z).2 h')
    have hq := hpt z hzΛ
    have hApt : A.eval (L.weierstrassP z) = P.eval (L.weierstrassP z - L.weierstrassP v) := by
      rw [hP, Polynomial.eval_comp]; simp
    have hBpt : B.eval (L.weierstrassP z) = Q.eval (L.weierstrassP z - L.weierstrassP v) := by
      rw [hQ, Polynomial.eval_comp]; simp
    rw [hApt, hBpt, Polynomial.eval_eq_sum_range' hIP, Polynomial.eval_eq_sum_range' hIQ] at hq
    have hUN : U1 Λ t (sgStar Λ) z ^ N = sgStar Λ z ^ N * (U1 Λ t (sgStar Λ) z / sgStar Λ z) ^ N := by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero _ hs)]
    simp only
    rw [hUN, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hNI, hq,
      sqThD_eq hΛ L hL hv hzΛ, hΛ.sqTh_eq hv hzΛ, GlobalTheory.OddTheta.wpF_eq L Λ hL, GlobalTheory.OddTheta.wpF_eq L Λ hL,
      mul_add, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ I := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [mul_pow, ← pow_mul, show 2 * I + 3 = (2 * (I - i) + 3) + 2 * i by omega]
      ring
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j ≤ I := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_pow, ← pow_mul, show 2 * I + 3 = 2 * (I - j) + 2 * j + 3 by omega]
      ring
  intro z
  exact congrFun heq z

end GlobalTheory.ThetaTranslDecomp
