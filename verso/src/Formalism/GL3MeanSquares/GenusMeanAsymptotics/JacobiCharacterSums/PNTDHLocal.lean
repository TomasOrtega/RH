import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHLocalB

open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

/- English proof (translation)
Introduce `h`. Rewrite `hs` using `[h, Complex.one_re]`. Conclude with `lt_irrefl _ hs`.
-/
lemma dhl_ne_one {s : ℂ} (hs : 1 < s.re) : s ≠ 1 := by
  intro h
  rw [h, Complex.one_re] at hs
  exact lt_irrefl _ hs

/- English proof (translation)
Establish `hz1 : z ≠ 1` using `dhl_ne_one hz`. Establish `hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w = (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w`. Introduce `w hw`. Simplify using `[DirichletCharacter.LFunctionTrivChar₁, hw]`. Establish `hev : DirichletCharacter.LFunctionTrivChar₁ M =ᶠ[nhds z] fun w => (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w` using `by filter_upwards [eventually_ne_nhds hz1] with w hw`.

Conclude with `hf w hw`. Establish `hd` using `DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ M) z (Or.inl hz1)`. Establish `hL0` using `DirichletCharacter.LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ M) (Or.inr hz1) hz.le`. Establish `hlin : DifferentiableAt ℂ (fun w : ℂ => w - 1) z` using `differentiableAt_id.sub_const 1`. Establish `hder : deriv (DirichletCharacter.LFunctionTrivChar₁ M) z = DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) z + (z - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) z`.

Rewrite using `[hev.deriv_eq, deriv_fun_mul hlin hd]`. Simplify using the standard rewrite rules. Rewrite using `[hder, hf z hz1]`. Unfold `negLD`. Establish `hz1' : z - 1 ≠ 0` using `sub_ne_zero.mpr hz1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma dhl_triv_ld (M : ℕ) [NeZero M] (z : ℂ) (hz : 1 < z.re) :
    -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z / DirichletCharacter.LFunctionTrivChar₁ M z)
      = negLD (1 : DirichletCharacter ℂ M) z - 1 / (z - 1) := by
  have hz1 : z ≠ 1 := dhl_ne_one hz
  have hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w =
      (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    intro w hw
    simp [DirichletCharacter.LFunctionTrivChar₁, hw]
  have hev : DirichletCharacter.LFunctionTrivChar₁ M =ᶠ[nhds z]
      fun w => (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    filter_upwards [eventually_ne_nhds hz1] with w hw
    exact hf w hw
  have hd := DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ M) z (Or.inl hz1)
  have hL0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ M)
    (Or.inr hz1) hz.le
  have hlin : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := differentiableAt_id.sub_const 1
  have hder : deriv (DirichletCharacter.LFunctionTrivChar₁ M) z =
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) z +
        (z - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) z := by
    rw [hev.deriv_eq, deriv_fun_mul hlin hd]
    simp
  rw [hder, hf z hz1]
  unfold negLD
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp
  ring

/- English proof (translation)
Establish `hU : IsOpen {w : ℂ | 1 < w.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hLd : DifferentiableOn ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) {w : ℂ | 1 < w.re}`. Introduce `w hw`. Conclude with `(DirichletCharacter.differentiableAt_LFunction _ w (Or.inl (dhl_ne_one hw))).differentiableWithinAt`. Establish `hD : DifferentiableOn ℂ (negLD (1 : DirichletCharacter ℂ M)) {w : ℂ | 1 < w.re}`.

Unfold `negLD`. Use `((hLd.deriv hU).div hLd ?_).neg` and prove the remaining obligations. Introduce `w hw`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr (dhl_ne_one hw)) (le_of_lt hw)`. Conclude with `(hD.contDiffOn hU).contDiffAt (hU.mem_nhds hs)`.
-/
lemma dhl_negLD_contDiffAt (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 < s.re) (k : ℕ) :
    ContDiffAt ℂ k (negLD (1 : DirichletCharacter ℂ M)) s := by
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hLd : DifferentiableOn ℂ (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M))
      {w : ℂ | 1 < w.re} := by
    intro w hw
    exact (DirichletCharacter.differentiableAt_LFunction _ w
      (Or.inl (dhl_ne_one hw))).differentiableWithinAt
  have hD : DifferentiableOn ℂ (negLD (1 : DirichletCharacter ℂ M)) {w : ℂ | 1 < w.re} := by
    unfold negLD
    refine ((hLd.deriv hU).div hLd ?_).neg
    intro w hw
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr (dhl_ne_one hw)) (le_of_lt hw)
  exact (hD.contDiffOn hU).contDiffAt (hU.mem_nhds hs)

/- English proof (translation)
Conclude with `contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hs)`.
-/
lemma dhl_pole_contDiffAt (s : ℂ) (hs : s ≠ 1) (k : ℕ) :
    ContDiffAt ℂ k (fun z : ℂ => 1 / (z - 1)) s := by
  exact contDiffAt_const.div (contDiffAt_id.sub contDiffAt_const) (sub_ne_zero.mpr hs)

/- English proof (translation)
Establish `hU : IsOpen {w : ℂ | 1 < w.re}` using `isOpen_lt continuous_const Complex.continuous_re`. Establish `hev : (fun z => -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z / DirichletCharacter.LFunctionTrivChar₁ M z)) =ᶠ[nhds s] (negLD (1 : DirichletCharacter ℂ M) - fun z : ℂ => 1 / (z - 1))` using `by filter_upwards [hU.mem_nhds hs] with z hz`. Rewrite using `[Pi.sub_apply]`. Conclude with `dhl_triv_ld M z hz`. Rewrite using `[hev.iteratedDeriv_eq k, iteratedDeriv_sub (dhl_negLD_contDiffAt M s hs k) (dhl_pole_contDiffAt s (dhl_ne_one hs) k), mul_sub, dhl_pole k s (dhl_ne_one hs)]`.
-/
lemma dhl_triv_iter (M : ℕ) [NeZero M] (s : ℂ) (hs : 1 < s.re) (k : ℕ) :
    (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z =>
      -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z / DirichletCharacter.LFunctionTrivChar₁ M z)) s
      = (-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) s
        - 1 / (s - 1) ^ (k + 1) := by
  have hU : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun z => -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z /
      DirichletCharacter.LFunctionTrivChar₁ M z)) =ᶠ[nhds s]
      (negLD (1 : DirichletCharacter ℂ M) - fun z : ℂ => 1 / (z - 1)) := by
    filter_upwards [hU.mem_nhds hs] with z hz
    rw [Pi.sub_apply]
    exact dhl_triv_ld M z hz
  rw [hev.iteratedDeriv_eq k, iteratedDeriv_sub (dhl_negLD_contDiffAt M s hs k)
    (dhl_pole_contDiffAt s (dhl_ne_one hs) k), mul_sub, dhl_pole k s (dhl_ne_one hs)]

/- English proof (translation)
Establish `hX3 : 3 ≤ (M : ℝ) * (|t| + 2)` using `dhl_X M t hM`. Establish `hK1 : 1 ≤ K` using `by linarith`. Establish `hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w = (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w`. Introduce `w hw`. Simplify using `[DirichletCharacter.LFunctionTrivChar₁, hw]`.

Establish `hf1 : DirichletCharacter.LFunctionTrivChar₁ M 1 ≠ 0`. Simplify using `only [DirichletCharacter.LFunctionTrivChar₁, Function.update_self]`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `p hp h`. Establish `hp2` using `(Nat.prime_of_mem_primeFactors hp).two_le`.

Establish `h1 : (p : ℂ)⁻¹ = 1` using `(sub_eq_zero.mp h).symm`. Establish `h2 : (p : ℂ) = 1` using `inv_eq_one.mp h1`. Establish `h3 : p = 1` using `by exact_mod_cast h2`. Use linear arithmetic over natural numbers and integers. Establish `hz0re : ((26 / 25 : ℂ) + ↑t * I).re = 26 / 25` using `dhl_z0re t`.

Establish `hz0ne : (26 / 25 : ℂ) + ↑t * I ≠ 1` using `dhl_ne_one (by rw [hz0re]; norm_num)`. Establish `hLz0` using `dhl_inv M (1 : DirichletCharacter ℂ M) t`. Establish `hnz0 : 1 / 650 ≤ ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖`. Rewrite using `[hf _ hz0ne, norm_mul]`. Establish `ha : 1 / 25 ≤ ‖(26 / 25 : ℂ) + ↑t * I - 1‖`.

Use `Complex.re_le_norm ((26 / 25 : ℂ) + ↑t * I - 1)` as an intermediate fact. Rewrite `this` using `[Complex.sub_re, hz0re, Complex.one_re]`. Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[norm_nonneg (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) ((26 / 25 : ℂ) + ↑t * I))]`. Establish `hfz0 : DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I) ≠ 0`.

Introduce `h`. Rewrite `hnz0` using `[h, norm_zero]`. Evaluate the numerical expressions using `at hnz0`. Establish `hgrowth : ∀ z : ℂ, ‖z - ((26 / 25 : ℂ) + ↑t * I)‖ ≤ 12 / 25 → ‖DirichletCharacter.LFunctionTrivChar₁ M z‖ ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖`. Introduce `z hz`.

Take `⟨hre, hn⟩` from `dhl_geom t z hz`. Establish `h1` using `dhl_triv_growth M z hre`. Establish `hM1 : (1 : ℝ) ≤ M` using `by exact_mod_cast (by omega : 1 ≤ M)`. Establish `h2 : ‖DirichletCharacter.LFunctionTrivChar₁ M z‖ ≤ 16 * M * (|t| + 2) ^ 2`. Establish `hsq : (1 + ‖z‖) ^ 2 ≤ (2 * (|t| + 2)) ^ 2`.

Establish `: 0 ≤ 1 + ‖z‖` using `by positivity`. Use `gcongr`. Use `mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 4 * M)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : 16 * M * (|t| + 2) ^ 2 ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650)`.

Establish `hKM : 10400 ≤ K * M` using `by nlinarith`. Establish `hT : 0 ≤ (M : ℝ) * (|t| + 2) ^ 2` using `by positivity`. Establish `e : K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) = (K * M) * (M * (|t| + 2) ^ 2) / 650` using `by ring`. Rewrite using `[e]`. Use `mul_le_mul_of_nonneg_right hKM hT` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h4 : K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖`. Apply `mul_le_mul_of_nonneg_left hnz0` to reduce the goal to its premises. Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨Z, m, hZ, hm, hcount, hbd⟩` from `dhl_core hCau (DirichletCharacter.LFunctionTrivChar₁ M) t K ((M : ℝ) * (|t| + 2)) hK1 hX3 (DirichletCharacter.differentiable_LFunctionTrivChar₁ M) hfz0 hgrowth`. Establish `hzero : ∀ ρ : ℂ, DirichletCharacter.LFunctionTrivChar₁ M ρ = 0 ↔ IsLZero (1 : DirichletCharacter ℂ M) ρ`. Introduce `ρ`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hρ : ρ ≠ 1` using `fun e => hf1 (e ▸ h)`. Use `⟨Or.inr hρ, ?_⟩` and prove the remaining obligations. Rewrite `h` using `[hf ρ hρ]`. Conclude with `(mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hρ)`. Introduce and unpack `⟨h1, h2⟩`.

Establish `hρ : ρ ≠ 1` using `h1.resolve_left (fun h => h rfl)`. Rewrite using `[hf ρ hρ, h2, mul_zero]`. Unfold `DHLocalAt`. Use `⟨Z, m, ?_, hm, ?_, hcount, ?_⟩` and prove the remaining obligations. Introduce `ρ`.

Rewrite using `[hZ ρ, hzero ρ]`. Introduce `ρ hρ`. Take `⟨_, hfρ⟩` from `(hZ ρ).mp hρ`. Take `⟨h1, h2⟩` from `(hzero ρ).mp hfρ`. Assume the negation of the conclusion as `hge`.

Use `push_neg at hge`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re _ h1 hge h2`. Introduce `k s hs hsd`. Establish `hs1 : s ≠ 1` using `dhl_ne_one hs`. Establish `hfs : DirichletCharacter.LFunctionTrivChar₁ M s ≠ 0`.

Rewrite using `[hf s hs1]`. Conclude with `mul_ne_zero (sub_ne_zero.mpr hs1) (DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr hs1) hs.le)`. Establish `hb` using `hbd k s hsd hfs`. Rewrite using `[if_pos rfl, ← dhl_triv_iter M s hs k]`. Conclude with `hb`.
-/
lemma dhl_triv (hCau : DHCauchy) (K : ℝ) (hK : 10400 ≤ K) (M : ℕ) [NeZero M]
    (t : ℝ) (hM : 3 ≤ M) : DHLocalAt (150 * (Real.log K + 2)) M (1 : DirichletCharacter ℂ M) t := by
  have hX3 : 3 ≤ (M : ℝ) * (|t| + 2) := dhl_X M t hM
  have hK1 : 1 ≤ K := by linarith
  have hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w =
      (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    intro w hw
    simp [DirichletCharacter.LFunctionTrivChar₁, hw]
  have hf1 : DirichletCharacter.LFunctionTrivChar₁ M 1 ≠ 0 := by
    simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_self]
    rw [Finset.prod_ne_zero_iff]
    intro p hp h
    have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : (p : ℂ)⁻¹ = 1 := (sub_eq_zero.mp h).symm
    have h2 : (p : ℂ) = 1 := inv_eq_one.mp h1
    have h3 : p = 1 := by exact_mod_cast h2
    omega
  have hz0re : ((26 / 25 : ℂ) + ↑t * I).re = 26 / 25 := dhl_z0re t
  have hz0ne : (26 / 25 : ℂ) + ↑t * I ≠ 1 := dhl_ne_one (by rw [hz0re]; norm_num)
  have hLz0 := dhl_inv M (1 : DirichletCharacter ℂ M) t
  have hnz0 : 1 / 650 ≤ ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
    rw [hf _ hz0ne, norm_mul]
    have ha : 1 / 25 ≤ ‖(26 / 25 : ℂ) + ↑t * I - 1‖ := by
      have := Complex.re_le_norm ((26 / 25 : ℂ) + ↑t * I - 1)
      rw [Complex.sub_re, hz0re, Complex.one_re] at this
      linarith
    nlinarith [norm_nonneg (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) ((26 / 25 : ℂ) + ↑t * I))]
  have hfz0 : DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnz0
    norm_num at hnz0
  have hgrowth : ∀ z : ℂ, ‖z - ((26 / 25 : ℂ) + ↑t * I)‖ ≤ 12 / 25 →
      ‖DirichletCharacter.LFunctionTrivChar₁ M z‖ ≤
        K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
    intro z hz
    obtain ⟨hre, hn⟩ := dhl_geom t z hz
    have h1 := dhl_triv_growth M z hre
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    have h2 : ‖DirichletCharacter.LFunctionTrivChar₁ M z‖ ≤ 16 * M * (|t| + 2) ^ 2 := by
      have hsq : (1 + ‖z‖) ^ 2 ≤ (2 * (|t| + 2)) ^ 2 := by
        have : 0 ≤ 1 + ‖z‖ := by positivity
        gcongr
      have := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 4 * M)
      nlinarith
    have h3 : 16 * M * (|t| + 2) ^ 2 ≤ K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) := by
      have hKM : 10400 ≤ K * M := by nlinarith
      have hT : 0 ≤ (M : ℝ) * (|t| + 2) ^ 2 := by positivity
      have e : K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) = (K * M) * (M * (|t| + 2) ^ 2) / 650 := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_right hKM hT
      linarith
    have h4 : K * ((M : ℝ) * (|t| + 2)) ^ 2 * (1 / 650) ≤
        K * ((M : ℝ) * (|t| + 2)) ^ 2 * ‖DirichletCharacter.LFunctionTrivChar₁ M ((26 / 25 : ℂ) + ↑t * I)‖ := by
      apply mul_le_mul_of_nonneg_left hnz0
      positivity
    linarith
  obtain ⟨Z, m, hZ, hm, hcount, hbd⟩ := dhl_core hCau (DirichletCharacter.LFunctionTrivChar₁ M) t K
    ((M : ℝ) * (|t| + 2)) hK1 hX3 (DirichletCharacter.differentiable_LFunctionTrivChar₁ M) hfz0 hgrowth
  have hzero : ∀ ρ : ℂ, DirichletCharacter.LFunctionTrivChar₁ M ρ = 0 ↔
      IsLZero (1 : DirichletCharacter ℂ M) ρ := by
    intro ρ
    constructor
    · intro h
      have hρ : ρ ≠ 1 := fun e => hf1 (e ▸ h)
      refine ⟨Or.inr hρ, ?_⟩
      rw [hf ρ hρ] at h
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hρ)
    · rintro ⟨h1, h2⟩
      have hρ : ρ ≠ 1 := h1.resolve_left (fun h => h rfl)
      rw [hf ρ hρ, h2, mul_zero]
  unfold DHLocalAt
  refine ⟨Z, m, ?_, hm, ?_, hcount, ?_⟩
  · intro ρ
    rw [hZ ρ, hzero ρ]
  · intro ρ hρ
    obtain ⟨_, hfρ⟩ := (hZ ρ).mp hρ
    obtain ⟨h1, h2⟩ := (hzero ρ).mp hfρ
    by_contra hge
    push_neg at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ h1 hge h2
  · intro k s hs hsd
    have hs1 : s ≠ 1 := dhl_ne_one hs
    have hfs : DirichletCharacter.LFunctionTrivChar₁ M s ≠ 0 := by
      rw [hf s hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inr hs1) hs.le)
    have hb := hbd k s hsd hfs
    rw [if_pos rfl, ← dhl_triv_iter M s hs k]
    exact hb

/- English proof (translation)
Unfold `DHLocalOf DHLocal`. Introduce `hCau`. Take `⟨C0, hC0⟩` from `lfunction_polynomial_growth`. Establish `hlog : 0 ≤ Real.log (max 10400 (52 * C0))` using `Real.log_nonneg (by linarith [le_max_left (10400 : ℝ) (52 * C0)])`. Use `⟨150 * (Real.log (max 10400 (52 * C0)) + 2), by linarith, ?_⟩` and prove the remaining obligations.

Introduce `M inst ψ t hM`. Distinguish the cases in `hψ : ψ = 1`. Substitute `hψ` using the available equality. Conclude with `dhl_triv hCau _ (le_max_left _ _) M t hM`. Conclude with `dhl_nontriv hCau C0 _ hC0 (by linarith [le_max_left (10400 : ℝ) (52 * C0)]) (le_max_right _ _) M ψ hψ t hM`.
-/
theorem deuring_heilbronn_local : DHLocalOf := by
  unfold DHLocalOf DHLocal
  intro hCau
  obtain ⟨C0, hC0⟩ := lfunction_polynomial_growth
  have hlog : 0 ≤ Real.log (max 10400 (52 * C0)) :=
    Real.log_nonneg (by linarith [le_max_left (10400 : ℝ) (52 * C0)])
  refine ⟨150 * (Real.log (max 10400 (52 * C0)) + 2), by linarith, ?_⟩
  intro M inst ψ t hM
  by_cases hψ : ψ = 1
  · subst hψ
    exact dhl_triv hCau _ (le_max_left _ _) M t hM
  · exact dhl_nontriv hCau C0 _ hC0 (by linarith [le_max_left (10400 : ℝ) (52 * C0)])
      (le_max_right _ _) M ψ hψ t hM

end Formalism.HermitianLattices.Ext.PrimesInProgressions
