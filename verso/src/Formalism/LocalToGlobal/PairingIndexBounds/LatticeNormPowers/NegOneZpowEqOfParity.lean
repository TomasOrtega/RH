import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.MemLamOfIff

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Xf

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {D : D7} {N N' : ℕ}

/- English proof (translation)
Introduce and unpack `rfl`. Apply `Formalism.L2.PairingIndexBounds.Rec.discrNZ D cc hcc` to reduce the goal to its premises. Unfold `IsDiscriminantTwelfthRootOfIdealLattice at hδ`. Rewrite using `[← hδ]`. Evaluate the numerical expressions.
-/
theorem delta_ne_zero (D : D7) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hcc : IsCurveIdeal D cc)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : δ ≠ 0 := by
  rintro rfl
  apply Formalism.L2.PairingIndexBounds.Rec.discrNZ D cc hcc
  unfold IsDiscriminantTwelfthRootOfIdealLattice at hδ
  rw [← hδ]
  norm_num

/- English proof (translation)
The claim follows from `hA D cc hcc δ hδ (delta_ne_zero D hcc hδ) N N' L L' hL`.
-/
theorem hfInt_of (hA : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.HfIntRec) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}
    (hcc : IsCurveIdeal D cc) (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hL : admitted D N N' L L') :
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt (tor0 D cc δ) (La D (tor0 D cc δ) L L') :=
  hA D cc hcc δ hδ (delta_ne_zero D hcc hδ) N N' L L' hL

/- English proof (translation)
Simplify using `only [Hf, Pi.smul_apply, nsmul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]`.
-/
theorem Hf_nsmul_left (T : Tor D) (n : ℕ) (x y : VC D N N') :
    Hf D T (n • x) y = (n : ℂ) * Hf D T x y := by
  simp only [Hf, Pi.smul_apply, nsmul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

/- English proof (translation)
Rewrite using `[Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T (n • y) x, Hf_nsmul_left, map_mul, Complex.conj_natCast, ← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm]`.
-/
theorem Hf_nsmul_right (T : Tor D) (n : ℕ) (x y : VC D N N') :
    Hf D T x (n • y) = (n : ℂ) * Hf D T x y := by
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T (n • y) x, Hf_nsmul_left, map_mul, Complex.conj_natCast,
    ← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm]

/- English proof (translation)
Simplify using `only [qH, Hf_nsmul_left, Hf_nsmul_right]`. Establish `: ((n : ℂ) * ((n : ℂ) * Hf D T x x)).re = (n : ℝ) ^ 2 * (Hf D T x x).re`. Rewrite using `[← mul_assoc, ← Nat.cast_mul]`. Rewrite using `[show ((n * n : ℕ) : ℂ) = (((n * n : ℕ) : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qH_nsmul (T : Tor D) (n : ℕ) (x : VC D N N') :
    qH D T (n • x) = (n : ℝ) ^ 2 * qH D T x := by
  simp only [qH, Hf_nsmul_left, Hf_nsmul_right]
  have : ((n : ℂ) * ((n : ℂ) * Hf D T x x)).re = (n : ℝ) ^ 2 * (Hf D T x x).re := by
    rw [← mul_assoc, ← Nat.cast_mul]
    rw [show ((n * n : ℕ) : ℂ) = (((n * n : ℕ) : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    push_cast; ring
  rw [this]; ring

/- English proof (translation)
Take `⟨m, hre, hr⟩` from `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.self_int T hI hx`. Establish `hs` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D`. Use `⟨m, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [qH]`. Rewrite using `[hre]`.

Clear the denominators using the available nonvanishing facts. Simplify using `only [al]`. Rewrite using `[hr]`.
-/
theorem qH_int (T : Tor D) {La' : AddSubgroup (VC D N N')} (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T La')
    {x : VC D N N'} (hx : x ∈ La') :
    ∃ m : ℤ, qH D T x = m ∧ al D T x = (-1 : ℂ) ^ m := by
  obtain ⟨m, hre, hr⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.self_int T hI hx
  have hs := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
  refine ⟨m, ?_, ?_⟩
  · simp only [qH]; rw [hre]; field_simp
  · simp only [al]; rw [hr]

/- English proof (translation)
Apply `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.neg_one_zpow_congr` to reduce the goal to its premises. Rewrite using `[Int.even_sub]`. Conclude with `h`.
-/
theorem neg_one_zpow_eq_of_parity {m m' : ℤ} (h : (Even m ↔ Even m')) : (-1 : ℂ) ^ m = (-1 : ℂ) ^ m' := by
  apply Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.neg_one_zpow_congr
  rw [Int.even_sub]; exact h

/- English proof (translation)
Rewrite using `[Int.even_mul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | h)`. Conclude with `absurd h (Int.not_even_iff_odd.mpr hu)`. Conclude with `h`.

Conclude with `Or.inr`.
-/
theorem even_odd_mul {u m : ℤ} (hu : Odd u) : (Even (u * m) ↔ Even m) := by
  rw [Int.even_mul]
  constructor
  · rintro (h | h)
    · exact absurd h (Int.not_even_iff_odd.mpr hu)
    · exact h
  · exact Or.inr

/- English proof (translation)
Unfold `wPh`. Rewrite using `[if_neg hp2]`. Establish `hex : ∃ s : ℂ, ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m` using `⟨_, k, m, h, rfl⟩`. Take `⟨k', m', h', hs⟩` from `Classical.epsilon_spec hex`. Rewrite using `[hs]`.

Establish `hodd : Odd (p : ℤ)`. Break down `hp.eq_two_or_odd' with h2 | ho` into its components or cases. Conclude with `absurd h2 hp2`. Conclude with `ho` after adjusting the coercions. Establish `key : ((p : ℤ) ^ k * m' : ℤ) = (p : ℤ) ^ k' * m`.

Establish `: ((p : ℝ) ^ k * m' : ℝ) = (p : ℝ) ^ k' * m`. Rewrite using `[← h', ← h]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Apply `neg_one_zpow_eq_of_parity` to reduce the goal to its premises.

Rewrite using `[← even_odd_mul (hodd.pow (n := k)), key, even_odd_mul (hodd.pow (n := k'))]`.
-/
theorem wPh_eq_of (T : Tor D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : VC D N N'} {k : ℕ} {m : ℤ}
    (h : (p : ℝ) ^ k * qH D T x = (m : ℝ)) : wPh D T p x = (-1 : ℂ) ^ m := by
  unfold wPh
  rw [if_neg hp2]
  have hex : ∃ s : ℂ, ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m :=
    ⟨_, k, m, h, rfl⟩
  obtain ⟨k', m', h', hs⟩ := Classical.epsilon_spec hex
  rw [hs]
  have hodd : Odd (p : ℤ) := by
    rcases hp.eq_two_or_odd' with h2 | ho
    · exact absurd h2 hp2
    · exact_mod_cast ho
  have key : ((p : ℤ) ^ k * m' : ℤ) = (p : ℤ) ^ k' * m := by
    have : ((p : ℝ) ^ k * m' : ℝ) = (p : ℝ) ^ k' * m := by
      rw [← h', ← h]; ring
    exact_mod_cast this
  apply neg_one_zpow_eq_of_parity
  rw [← even_odd_mul (hodd.pow (n := k)), key, even_odd_mul (hodd.pow (n := k'))]

/- English proof (translation)
Rewrite using `[show (Real.pi : ℂ) * Complex.I * (m : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]`.
-/
theorem exp_pi_int (m : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * (m : ℂ)) = (-1 : ℂ) ^ m := by
  rw [show (Real.pi : ℂ) * Complex.I * (m : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

/- English proof (translation)
Introduce `p hpF cc δ hcc hδ N N' L L' hL x hx`. Take `⟨m, hq, hal⟩` from `qH_int _ (hfInt_of hA hcc hδ hL) hx`. Rewrite using `[hal]`. Distinguish the cases in `hp2 : p = 2`. Unfold `wPh`.

Rewrite using `[if_pos hp2, hq]`. Use `push_cast`. Conclude with `exp_pi_int m`. Conclude with `wPh_eq_of _ hpF.out hp2 (k := 0) (by rw [hq]; simp)`.
-/
theorem wOnLattice_of (hA : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.HfIntRec) (D : D7) : wOnLattice D := by
  intro p hpF cc δ hcc hδ N N' L L' hL x hx
  obtain ⟨m, hq, hal⟩ := qH_int _ (hfInt_of hA hcc hδ hL) hx
  rw [hal]
  by_cases hp2 : p = 2
  · unfold wPh
    rw [if_pos hp2, hq]
    push_cast
    exact exp_pi_int m
  · exact wPh_eq_of _ hpF.out hp2 (k := 0) (by rw [hq]; simp)

/- English proof (translation)
Rewrite using `[pow_add, mul_nsmul]`. Conclude with `AddSubgroup.nsmul_mem _ hx _`.
-/
theorem pow_add_smul_mem_lattice {T : Tor D} {p : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {x : VC D N N'} {k j : ℕ}
    (hx : (p ^ k : ℕ) • x ∈ La D T L L') : (p ^ (k + j) : ℕ) • x ∈ La D T L L' := by
  rw [pow_add, mul_nsmul]
  exact AddSubgroup.nsmul_mem _ hx _

/- English proof (translation)
Introduce `p hpF cc δ hcc hδ hp2 N N' L L' hL x ⟨k, hk⟩`. Take `⟨m, hq, -⟩` from `qH_int _ (hfInt_of hA hcc hδ hL) hk`. Establish `h : (p : ℝ) ^ (2 * k) * qH D (tor0 D cc δ) x = (m : ℝ)`. Rewrite using `[← hq, qH_nsmul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨2 * k, m, h, wPh_eq_of _ hpF.out hp2 h⟩`.
-/
theorem wPhase_of (hA : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.HfIntRec) (D : D7) : wPhase D := by
  intro p hpF cc δ hcc hδ hp2 N N' L L' hL x ⟨k, hk⟩
  obtain ⟨m, hq, -⟩ := qH_int _ (hfInt_of hA hcc hδ hL) hk
  have h : (p : ℝ) ^ (2 * k) * qH D (tor0 D cc δ) x = (m : ℝ) := by
    rw [← hq, qH_nsmul]; push_cast; ring
  exact ⟨2 * k, m, h, wPh_eq_of _ hpF.out hp2 h⟩

end Formalism.L2.PairingIndexBounds.Xf

namespace Formalism.L2.PairingIndexBounds.Xf

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {D : D7} {N N' : ℕ}

/- English proof (translation)
The claim follows from `wPh_eq_of T hp hp2 (k := 2 * j) (by rw [← h, qH_nsmul]; push_cast; ring)`.
-/
theorem wPh_pow_eq (T : Tor D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {x : VC D N N'} {j : ℕ} {m : ℤ}
    (h : qH D T ((p ^ j : ℕ) • x) = m) : wPh D T p x = (-1 : ℂ) ^ m :=
  wPh_eq_of T hp hp2 (k := 2 * j) (by rw [← h, qH_nsmul]; push_cast; ring)

/- English proof (translation)
Unfold `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf kap`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cf_sq (T : Tor D) (x y : VC D N N') :
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf T x y ^ 2 = kap D T x y := by
  unfold Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf kap
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/- English proof (translation)
Unfold `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf`. Rewrite using `[← Complex.exp_nat_mul, ← exp_pi_int (-b)]`. Use `congr 1`. Establish `h' : (Q : ℂ) * ((Hf D T x y).im : ℂ) = (b : ℂ)` using `by exact_mod_cast h`. Use `push_cast`.

Take the linear combination `(-(Real.pi : ℂ) * Complex.I) * h'`.
-/
theorem cf_pow (T : Tor D) (x y : VC D N N') (Q : ℕ) (b : ℤ) (h : (Q : ℝ) * (Hf D T x y).im = b) :
    Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf T x y ^ Q = (-1 : ℂ) ^ (-b) := by
  unfold Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf
  rw [← Complex.exp_nat_mul, ← exp_pi_int (-b)]
  congr 1
  have h' : (Q : ℂ) * ((Hf D T x y).im : ℂ) = (b : ℂ) := by exact_mod_cast h
  push_cast
  linear_combination (-(Real.pi : ℂ) * Complex.I) * h'

/- English proof (translation)
Introduce `p hpF cc δ hcc hδ hp2 N N' L L' hL x y ⟨kx, hx⟩ ⟨ky, hy⟩`. Establish `hp` using `hpF.out`. Establish `hI` using `hfInt_of hA hcc hδ hL`. Establish `hX : (p ^ (kx + ky) : ℕ) • x ∈ La D (tor0 D cc δ) L L'` using `pow_add_smul_mem_lattice hx`. Establish `hY : (p ^ (kx + ky) : ℕ) • y ∈ La D (tor0 D cc δ) L L'`.

Use `pow_add_smul_mem_lattice (j := kx) hy` as an intermediate fact. Rewrite `this` using `[Nat.add_comm ky kx]`. Then use the resulting hypothesis. Establish `hS : (p ^ (kx + ky) : ℕ) • (x + y) ∈ La D (tor0 D cc δ) L L'`. Rewrite using `[nsmul_add]`. Conclude with `add_mem hX hY`.

Take `⟨mX, hqX, -⟩` from `qH_int _ hI hX`. Take `⟨mY, hqY, -⟩` from `qH_int _ hI hY`. Take `⟨mS, hqS, -⟩` from `qH_int _ hI hS`. Take `⟨a, b, hab, hH⟩` from `hI _ hX _ hY`. Establish `hwx` using `wPh_pow_eq _ hp hp2 hqX`.

Establish `hwy` using `wPh_pow_eq _ hp hp2 hqY`. Establish `hws` using `wPh_pow_eq _ hp hp2 hqS`. Use `set P : ℕ := p ^ (kx + ky) with hPdef`. Use `set T := tor0 D cc δ with hT`. Establish `hs` using `Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D`.

Establish `e1 : (Hf D T (P • x + P • y) (P • x + P • y)).re = (Hf D T (P • x) (P • x)).re + (Hf D T (P • y) (P • y)).re + 2 * (Hf D T (P • x) (P • y)).re`. Rewrite using `[Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_left, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_right, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_right, Complex.add_re, Complex.add_re, Complex.add_re, Formalism.L2.Glo …`. Expand and normalize the polynomial expressions, which then agree. Establish `ere : (Hf D T (P • x) (P • y)).re = a / Real.sqrt D.host.d` using `by rw [hH]; simp`. Establish `hrel : (mS : ℝ) = mX + mY + a`.

Rewrite using `[← hqS, ← hqX, ← hqY, nsmul_add]`. Simplify using `only [qH]`. Rewrite using `[e1, ere]`. Clear the denominators using the available nonvanishing facts. Establish `hrelZ : mS = mX + mY + a` using `by exact_mod_cast hrel`.

Establish `him : ((P ^ 2 : ℕ) : ℝ) * (Hf D T x y).im = b`. Establish `h0` using `congrArg Complex.im hH`. Rewrite `h0` using `[Hf_nsmul_left, Hf_nsmul_right]`. Establish `h1 : ((P : ℂ) * ((P : ℂ) * Hf D T x y)).im = (P : ℝ) * ((P : ℝ) * (Hf D T x y).im)`. Rewrite using `[show (P : ℂ) = ((P : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul, Complex.im_ofReal_mul]`.

Rewrite `h0` using `[h1]`. Establish `h2 : ((((a : ℝ) / Real.sqrt D.host.d : ℝ) : ℂ) + (b : ℂ) * Complex.I).im = b` using `by simp`. Rewrite `h0` using `[h2]`. Rewrite using `[← h0]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `set cf0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf T x y with hcf0`. Establish `hS2 : wPh D T p (x + y) * wPh D T p (x + y) = 1`. Rewrite using `[hws, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul]`. Conclude with `(even_two_mul mS).neg_one_zpow`.

Establish `hc : wPh D T p x * wPh D T p y * wPh D T p (x + y) * cf0 = (-1 : ℂ) ^ (mX + mY + mS) * cf0`. Rewrite using `[hwx, hwy, hws, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]`. Establish `hQodd : Odd ((P ^ 2 : ℕ) : ℤ)`. Establish `: Odd (p : ℤ)`. Break down `hp.eq_two_or_odd' with h2 | ho` into its components or cases.

Conclude with `absurd h2 hp2`. Conclude with `ho` after adjusting the coercions. Use `push_cast`. Conclude with `(this.pow).pow`. Use `⟨wPh D T p x * wPh D T p y * wPh D T p (x + y) * cf0, 2 * (kx + ky), ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hc, mul_pow, show p ^ (2 * (kx + ky)) = P ^ 2 by rw [hPdef]; ring, hcf0, cf_pow T x y (P ^ 2) b him, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]`. Apply `Even.neg_one_zpow` to reduce the goal to its premises. Take `⟨t, ht⟩` from `hQodd`. Take `⟨e, he⟩` from `hab`. Rewrite using `[ht, hrelZ]`.

Conclude with `⟨(mX + mY) * (2 * t + 1) + a * t + e, by linear_combination he⟩`. Rewrite using `[hc, mul_pow, hcf0, cf_sq, ← zpow_natCast, ← zpow_mul]`. Rewrite using `[(show Even ((mX + mY + mS) * ((2 : ℕ) : ℤ)) from ⟨mX + mY + mS, by push_cast; ring⟩).neg_one_zpow, one_mul]`. Introduce `G`. Use function extensionality and compare the values at `z`.

Simplify using `only [Wop]`. Rewrite using `[show Wop D T p y G = fun w => wPh D T p y * U D T y G w from rfl, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_smul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_U]`. Take the linear combination `(-(wPh D T p x * wPh D T p y * cf0 * U D T (x + y) G z)) * hS2`.
-/
theorem wCocycle_of (hA : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.HfIntRec) (D : D7) : wCocycle D := by
  intro p hpF cc δ hcc hδ hp2 N N' L L' hL x y ⟨kx, hx⟩ ⟨ky, hy⟩
  have hp := hpF.out
  have hI := hfInt_of hA hcc hδ hL
  have hX : (p ^ (kx + ky) : ℕ) • x ∈ La D (tor0 D cc δ) L L' := pow_add_smul_mem_lattice hx
  have hY : (p ^ (kx + ky) : ℕ) • y ∈ La D (tor0 D cc δ) L L' := by
    have := pow_add_smul_mem_lattice (j := kx) hy
    rwa [Nat.add_comm ky kx] at this
  have hS : (p ^ (kx + ky) : ℕ) • (x + y) ∈ La D (tor0 D cc δ) L L' := by
    rw [nsmul_add]; exact add_mem hX hY
  obtain ⟨mX, hqX, -⟩ := qH_int _ hI hX
  obtain ⟨mY, hqY, -⟩ := qH_int _ hI hY
  obtain ⟨mS, hqS, -⟩ := qH_int _ hI hS
  obtain ⟨a, b, hab, hH⟩ := hI _ hX _ hY
  have hwx := wPh_pow_eq _ hp hp2 hqX
  have hwy := wPh_pow_eq _ hp hp2 hqY
  have hws := wPh_pow_eq _ hp hp2 hqS
  set P : ℕ := p ^ (kx + ky) with hPdef
  set T := tor0 D cc δ with hT
  have hs := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D

  have e1 : (Hf D T (P • x + P • y) (P • x + P • y)).re =
      (Hf D T (P • x) (P • x)).re + (Hf D T (P • y) (P • y)).re + 2 * (Hf D T (P • x) (P • y)).re := by
    rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_left, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_right,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_right, Complex.add_re, Complex.add_re, Complex.add_re,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_re_swap T (P • x) (P • y)]
    ring
  have ere : (Hf D T (P • x) (P • y)).re = a / Real.sqrt D.host.d := by rw [hH]; simp
  have hrel : (mS : ℝ) = mX + mY + a := by
    rw [← hqS, ← hqX, ← hqY, nsmul_add]
    simp only [qH]
    rw [e1, ere]
    field_simp
  have hrelZ : mS = mX + mY + a := by exact_mod_cast hrel

  have him : ((P ^ 2 : ℕ) : ℝ) * (Hf D T x y).im = b := by
    have h0 := congrArg Complex.im hH
    rw [Hf_nsmul_left, Hf_nsmul_right] at h0
    have h1 : ((P : ℂ) * ((P : ℂ) * Hf D T x y)).im = (P : ℝ) * ((P : ℝ) * (Hf D T x y).im) := by
      rw [show (P : ℂ) = ((P : ℝ) : ℂ) by push_cast; rfl, Complex.im_ofReal_mul, Complex.im_ofReal_mul]
    rw [h1] at h0
    have h2 : ((((a : ℝ) / Real.sqrt D.host.d : ℝ) : ℂ) + (b : ℂ) * Complex.I).im = b := by simp
    rw [h2] at h0
    rw [← h0]; push_cast; ring
  set cf0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf T x y with hcf0
  have hS2 : wPh D T p (x + y) * wPh D T p (x + y) = 1 := by
    rw [hws, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), ← two_mul]
    exact (even_two_mul mS).neg_one_zpow
  have hc : wPh D T p x * wPh D T p y * wPh D T p (x + y) * cf0 =
      (-1 : ℂ) ^ (mX + mY + mS) * cf0 := by
    rw [hwx, hwy, hws, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  have hQodd : Odd ((P ^ 2 : ℕ) : ℤ) := by
    have : Odd (p : ℤ) := by
      rcases hp.eq_two_or_odd' with h2 | ho
      · exact absurd h2 hp2
      · exact_mod_cast ho
    push_cast
    exact (this.pow).pow
  refine ⟨wPh D T p x * wPh D T p y * wPh D T p (x + y) * cf0, 2 * (kx + ky), ?_, ?_, ?_⟩
  · rw [hc, mul_pow, show p ^ (2 * (kx + ky)) = P ^ 2 by rw [hPdef]; ring,
      hcf0, cf_pow T x y (P ^ 2) b him, ← zpow_natCast, ← zpow_mul,
      ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
    apply Even.neg_one_zpow
    obtain ⟨t, ht⟩ := hQodd
    obtain ⟨e, he⟩ := hab
    rw [ht, hrelZ]
    exact ⟨(mX + mY) * (2 * t + 1) + a * t + e, by linear_combination he⟩
  · rw [hc, mul_pow, hcf0, cf_sq, ← zpow_natCast, ← zpow_mul]
    rw [(show Even ((mX + mY + mS) * ((2 : ℕ) : ℤ)) from ⟨mX + mY + mS, by push_cast; ring⟩).neg_one_zpow,
      one_mul]
  · intro G
    funext z
    simp only [Wop]
    rw [show Wop D T p y G = fun w => wPh D T p y * U D T y G w from rfl, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_smul, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.U_U]
    linear_combination (-(wPh D T p x * wPh D T p y * cf0 * U D T (x + y) G z)) * hS2

end Formalism.L2.PairingIndexBounds.Xf
