import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactAltForm
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Ker.KS

open Formalism.L2.Th1.H (cmL CmOK)

section Pt

variable (a : ℕ) (b c : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) (lam : ℂ) (hlam : lam ≠ 0)

def pt (u v : ℝ) : ℂ := lam * ((u : ℂ) * (a : ℂ) + (v : ℂ) * Formalism.L2.Th1.F.cmTheta b d)

/- English proof (translation)
Rewrite using `[PeriodPair.mem_lattice]`. Establish `e1 : (cmL a b d ha hd lam hlam).ω₁ = lam * (a : ℂ)` using `rfl`. Establish `e2 : (cmL a b d ha hd lam hlam).ω₂ = lam * Formalism.L2.Th1.F.cmTheta b d` using `rfl`. Rewrite using `[e1, e2]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨m, n, by simp only [pt]; push_cast; ring⟩`. Introduce and unpack `⟨r, s, rfl⟩`. Conclude with `⟨r, s, by simp only [pt]; push_cast; ring⟩`.
-/
theorem mem_cmL (z : ℂ) : z ∈ (cmL a b d ha hd lam hlam).lattice ↔ ∃ r s : ℤ, z = pt a b d lam r s := by
  rw [PeriodPair.mem_lattice]
  have e1 : (cmL a b d ha hd lam hlam).ω₁ = lam * (a : ℂ) := rfl
  have e2 : (cmL a b d ha hd lam hlam).ω₂ = lam * Formalism.L2.Th1.F.cmTheta b d := rfl
  rw [e1, e2]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m, n, by simp only [pt]; push_cast; ring⟩
  · rintro ⟨r, s, rfl⟩
    exact ⟨r, s, by simp only [pt]; push_cast; ring⟩

include ha hd hlam in
/- English proof (translation)
Establish `h' : (u : ℂ) * a + (v : ℂ) * Formalism.L2.Th1.F.cmTheta b d = (u' : ℂ) * a + (v' : ℂ) * Formalism.L2.Th1.F.cmTheta b d`. Unfold `pt at h`. Conclude with `mul_left_cancel₀ hlam h`. Establish `hind` using `(Formalism.L2.Th1.F.cmPair a b d ha hd).indep`. Rewrite `hind` using `[LinearIndependent.pair_iff]`.

Take `⟨h1, h2⟩` from `hind (u - u') (v - v') (by show (u - u') • (a : ℂ) + (v - v') • Formalism.L2.Th1.F.cmTheta b d = 0`. Rewrite using `[Complex.real_smul, Complex.real_smul]`. Use `push_cast`. Take the linear combination `h')`. Conclude with `⟨by linarith, by linarith⟩`.
-/
theorem pt_inj {u v u' v' : ℝ} (h : pt a b d lam u v = pt a b d lam u' v') : u = u' ∧ v = v' := by
  have h' : (u : ℂ) * a + (v : ℂ) * Formalism.L2.Th1.F.cmTheta b d
      = (u' : ℂ) * a + (v' : ℂ) * Formalism.L2.Th1.F.cmTheta b d := by
    unfold pt at h
    exact mul_left_cancel₀ hlam h
  have hind := (Formalism.L2.Th1.F.cmPair a b d ha hd).indep
  rw [LinearIndependent.pair_iff] at hind
  obtain ⟨h1, h2⟩ := hind (u - u') (v - v') (by
    show (u - u') • (a : ℂ) + (v - v') • Formalism.L2.Th1.F.cmTheta b d = 0
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    linear_combination h')
  exact ⟨by linarith, by linarith⟩

/- English proof (translation)
Rewrite using `[mem_cmL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, s, h⟩`. Take `⟨h1, h2⟩` from `pt_inj a b d ha hd lam hlam h`. Conclude with `⟨⟨r, h1⟩, ⟨s, h2⟩⟩`.

Introduce and unpack `⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩`. Conclude with `⟨r, s, rfl⟩`.
-/
theorem pt_mem_iff (u v : ℝ) : pt a b d lam u v ∈ (cmL a b d ha hd lam hlam).lattice ↔ (∃ r : ℤ, u = r) ∧ ∃ s : ℤ, v = s := by
  rw [mem_cmL]
  constructor
  · rintro ⟨r, s, h⟩
    obtain ⟨h1, h2⟩ := pt_inj a b d ha hd lam hlam h
    exact ⟨⟨r, h1⟩, ⟨s, h2⟩⟩
  · rintro ⟨⟨r, rfl⟩, ⟨s, rfl⟩⟩
    exact ⟨r, s, rfl⟩

/- English proof (translation)
Simplify using `only [pt]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pt_sub (u v u' v' : ℝ) : pt a b d lam u v - pt a b d lam u' v' = pt a b d lam (u - u') (v - v') := by
  simp only [pt]
  push_cast
  ring

/- English proof (translation)
Establish `h' : 4 * (a : ℂ) * (c : ℂ) = (b : ℂ) ^ 2 + (d : ℂ)` using `by exact_mod_cast h`. Establish `hS : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ)`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]`. Unfold `Formalism.L2.Th1.F.cmTheta`. Take the linear combination `(1 / 4 : ℂ) * h' + (1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq - (1 / 4 : ℂ) * hS`.
-/
theorem theta_sq (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    Formalism.L2.Th1.F.cmTheta b d * Formalism.L2.Th1.F.cmTheta b d = (b : ℂ) * Formalism.L2.Th1.F.cmTheta b d - (a : ℂ) * (c : ℂ) := by
  have h' : 4 * (a : ℂ) * (c : ℂ) = (b : ℂ) ^ 2 + (d : ℂ) := by exact_mod_cast h
  have hS : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  unfold Formalism.L2.Th1.F.cmTheta
  linear_combination (1 / 4 : ℂ) * h' + (1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq
    - (1 / 4 : ℂ) * hS

/- English proof (translation)
Substitute `hb` using the available equality. Unfold `Formalism.L2.Th1.F.cmTheta`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_one (k : ℤ) (hb : b = 2 * k + 1) : Formalism.L2.Th1.F.cmTheta 1 d = Formalism.L2.Th1.F.cmTheta b d - (k : ℂ) := by
  subst hb
  unfold Formalism.L2.Th1.F.cmTheta
  push_cast
  ring

/- English proof (translation)
Establish `hsq` using `theta_sq a b c d h`. Establish `hbC : (b : ℂ) = 2 * (k : ℂ) + 1` using `by exact_mod_cast hb`. Rewrite using `[theta_one b d k hb]`. Simplify using `only [pt]`. Use `push_cast`.

Take the linear combination `(lam * (v : ℂ)) * hsq + (lam * (v : ℂ) * Formalism.L2.Th1.F.cmTheta b d) * hbC`.
-/
theorem theta_pt (h : 4 * (a : ℤ) * c = b ^ 2 + d) (k : ℤ) (hb : b = 2 * k + 1) (u v : ℝ) :
    Formalism.L2.Th1.F.cmTheta 1 d * pt a b d lam u v = pt a b d lam (-v * c - k * u) (u * a + v * (k + 1)) := by
  have hsq := theta_sq a b c d h
  have hbC : (b : ℂ) = 2 * (k : ℂ) + 1 := by exact_mod_cast hb
  rw [theta_one b d k hb]
  simp only [pt]
  push_cast
  linear_combination (lam * (v : ℂ)) * hsq + (lam * (v : ℂ) * Formalism.L2.Th1.F.cmTheta b d) * hbC

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm⟩`. Establish `e : ((x : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ)` using `by push_cast; linarith`. Establish `hx : x = 2 * m` using `by exact_mod_cast e`. Conclude with `⟨m, by omega⟩`.

Introduce and unpack `⟨m, rfl⟩`. Conclude with `⟨m, by push_cast; ring⟩`.
-/
theorem half_int (x : ℤ) : (∃ m : ℤ, ((x : ℝ)) / 2 = m) ↔ Even x := by
  constructor
  · rintro ⟨m, hm⟩
    have e : ((x : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) := by push_cast; linarith
    have hx : x = 2 * m := by exact_mod_cast e
    exact ⟨m, by omega⟩
  · rintro ⟨m, rfl⟩
    exact ⟨m, by push_cast; ring⟩

/- English proof (translation)
Take `⟨h, ⟨a', ha'⟩, hd8, -⟩` from `hcm`. Break down `Int.even_or_odd b with ⟨t, ht⟩ | ⟨t, ht⟩` into its components or cases. It suffices to derive a contradiction. Establish `e : 4 * ((a : ℤ) * c) = 4 * (t * t) + (d : ℤ)`. Take the linear combination `h + (b + t + t) * ht`.

Generalize the expression as in `(a : ℤ) * c = P at e`. Generalize the expression as in `t * t = Q at e`. Use linear arithmetic over natural numbers and integers. Establish `e : 4 * ((a : ℤ) * c) = 4 * (t * t + t) + 1 + (d : ℤ)`. Take the linear combination `h + (b + 2 * t + 1) * ht`.

Establish `hev : Even (t * t + t)`. Use `Int.even_mul_succ_self t` as an intermediate fact. Rewrite `this` using `[mul_add, mul_one]`. Conclude with `this`. Take `⟨m, hm⟩` from `hev`.

Rewrite `e` using `[hm]`. Establish `hP : ((a : ℤ) * c) % 2 = 0`. Generalize the expression as in `(a : ℤ) * c = P at e ⊢`. Use linear arithmetic over natural numbers and integers. Break down `Int.even_mul.mp (Int.even_iff.mpr hP) with ⟨e', he'⟩ | hce` into its components or cases.

It suffices to derive a contradiction. Use linear arithmetic over natural numbers and integers. Conclude with `⟨hce, ⟨t, ht⟩⟩`.
-/
theorem even_c (hcm : CmOK a b c d) : Even c ∧ Odd b := by
  obtain ⟨h, ⟨a', ha'⟩, hd8, -⟩ := hcm
  rcases Int.even_or_odd b with ⟨t, ht⟩ | ⟨t, ht⟩
  · exfalso
    have e : 4 * ((a : ℤ) * c) = 4 * (t * t) + (d : ℤ) := by
      linear_combination h + (b + t + t) * ht
    generalize (a : ℤ) * c = P at e
    generalize t * t = Q at e
    omega
  · have e : 4 * ((a : ℤ) * c) = 4 * (t * t + t) + 1 + (d : ℤ) := by
      linear_combination h + (b + 2 * t + 1) * ht
    have hev : Even (t * t + t) := by
      have := Int.even_mul_succ_self t
      rw [mul_add, mul_one] at this
      exact this
    obtain ⟨m, hm⟩ := hev
    rw [hm] at e
    have hP : ((a : ℤ) * c) % 2 = 0 := by
      generalize (a : ℤ) * c = P at e ⊢
      omega
    rcases Int.even_mul.mp (Int.even_iff.mpr hP) with ⟨e', he'⟩ | hce
    · exfalso
      omega
    · exact ⟨hce, ⟨t, ht⟩⟩

/- English proof (translation)
Take `⟨hc2, k, hk⟩` from `even_c a b c d hcm`. Take `⟨a', ha2⟩` from `hcm.2.1`. Establish `hpt : lam * (a : ℂ) / 2 = pt a b d lam (1 / 2) 0`. Simplify using `only [pt]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hθ : Formalism.L2.Th1.F.cmTheta 1 d * (lam * (a : ℂ) / 2) = pt a b d lam (-(k : ℝ) / 2) ((a : ℝ) / 2)`. Rewrite using `[theta_one b d k hk]`. Simplify using `only [pt]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_cmL]`. Conclude with `⟨1, 0, by simp only [pt]; push_cast; ring⟩`. Rewrite using `[hθ, pt_mem_iff]`.

Introduce and unpack `⟨-, s, hs⟩`. Establish `e : ((a : ℤ) : ℝ) = ((2 * s : ℤ) : ℝ)` using `by push_cast; linarith`. Establish `e' : (a : ℤ) = 2 * s` using `by exact_mod_cast e`. Use linear arithmetic over natural numbers and integers. Rewrite using `[sub_mul, one_mul, hθ, hpt, pt_sub, pt_mem_iff]`.

Introduce and unpack `⟨-, s, hs⟩`. Establish `e : ((a : ℤ) : ℝ) = ((-2 * s : ℤ) : ℝ)` using `by push_cast; linarith`. Establish `e' : (a : ℤ) = -2 * s` using `by exact_mod_cast e`. Use linear arithmetic over natural numbers and integers.
-/
theorem half_period_standard_CM (hcm : CmOK a b c d) :
    2 * (lam * a / 2) ∈ (cmL a b d ha hd lam hlam).lattice ∧
    Formalism.L2.Th1.F.cmTheta 1 d * (lam * a / 2) ∉ (cmL a b d ha hd lam hlam).lattice ∧
    (1 - Formalism.L2.Th1.F.cmTheta 1 d) * (lam * a / 2) ∉ (cmL a b d ha hd lam hlam).lattice := by
  obtain ⟨hc2, k, hk⟩ := even_c a b c d hcm
  obtain ⟨a', ha2⟩ := hcm.2.1
  have hpt : lam * (a : ℂ) / 2 = pt a b d lam (1 / 2) 0 := by
    simp only [pt]; push_cast; ring
  have hθ : Formalism.L2.Th1.F.cmTheta 1 d * (lam * (a : ℂ) / 2) = pt a b d lam (-(k : ℝ) / 2) ((a : ℝ) / 2) := by
    rw [theta_one b d k hk]
    simp only [pt]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_cmL]
    exact ⟨1, 0, by simp only [pt]; push_cast; ring⟩
  · rw [hθ, pt_mem_iff]
    rintro ⟨-, s, hs⟩
    have e : ((a : ℤ) : ℝ) = ((2 * s : ℤ) : ℝ) := by push_cast; linarith
    have e' : (a : ℤ) = 2 * s := by exact_mod_cast e
    omega
  · rw [sub_mul, one_mul, hθ, hpt, pt_sub, pt_mem_iff]
    rintro ⟨-, s, hs⟩
    have e : ((a : ℤ) : ℝ) = ((-2 * s : ℤ) : ℝ) := by push_cast; linarith
    have e' : (a : ℤ) = -2 * s := by exact_mod_cast e
    omega

omit a b c d lam in
/- English proof (translation)
Simplify using `[Int.even_sub, Int.even_add, Int.even_mul, Int.even_add_one, hc, ha] at h3 h4 ⊢`. Simplify using `only [← Int.not_even_iff_odd] at h3 h4 ⊢`. The claim follows by propositional logic.
-/
theorem parity_key (r s k a c : ℤ) (hc : Even c) (ha : ¬ Even a) (h3 : ¬ (Even (-s * c - k * r) ∧ Even (r * a + s * (k + 1))))
    (h4 : ¬ (Even (r - (-s * c - k * r)) ∧ Even (s - (r * a + s * (k + 1))))) : Even (r - 1) ∧ Even s := by
  simp [Int.even_sub, Int.even_add, Int.even_mul, Int.even_add_one, hc, ha] at h3 h4 ⊢
  simp only [← Int.not_even_iff_odd] at h3 h4 ⊢
  tauto

/- English proof (translation)
Take `⟨hc2, k, hk⟩` from `even_c a b c d hcm`. Establish `hform` using `hcm.1`. Establish `hao : ¬ Even (a : ℤ)`. Introduce and unpack `⟨e, he⟩`. Take `⟨a', ha2⟩` from `hcm.2.1`.

Use linear arithmetic over natural numbers and integers. Rewrite `h2` using `[mem_cmL]`. Take `⟨r, s, hrs⟩` from `h2`. Establish `ht : t = pt a b d lam ((r : ℝ) / 2) ((s : ℝ) / 2)`. Simplify using `only [pt] at hrs ⊢`.

Move the coercions through the operations in `at hrs ⊢`. Take the linear combination `hrs / 2`. Establish `e3 : Formalism.L2.Th1.F.cmTheta 1 d * t = pt a b d lam (((-s * c - k * r : ℤ) : ℝ) / 2) (((r * (a : ℤ) + s * (k + 1) : ℤ) : ℝ) / 2)`. Rewrite using `[ht, theta_pt a b c d lam hform k hk]`. Simplify using `only [pt]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e4 : (1 - Formalism.L2.Th1.F.cmTheta 1 d) * t = pt a b d lam (((r - (-s * c - k * r) : ℤ) : ℝ) / 2) (((s - (r * (a : ℤ) + s * (k + 1)) : ℤ) : ℝ) / 2)`. Rewrite using `[sub_mul, one_mul, e3, ht]`. Simplify using `only [pt]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h3` using `[e3, pt_mem_iff, half_int, half_int]`. Rewrite `h4` using `[e4, pt_mem_iff, half_int, half_int]`. Take `⟨⟨m, hm⟩, ⟨n, hn⟩⟩` from `parity_key r s k (a : ℤ) c hc2 hao h3 h4`.

Establish `hpt : lam * (a : ℂ) / 2 = pt a b d lam (1 / 2) 0`. Simplify using `only [pt]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ht, hpt, pt_sub, pt_mem_iff]`.

Establish `em : ((r - 1 : ℤ) : ℝ) = ((m + m : ℤ) : ℝ)` using `by exact_mod_cast hm`. Establish `en : ((s : ℤ) : ℝ) = ((n + n : ℤ) : ℝ)` using `by exact_mod_cast hn`. Move the coercions through the operations in `at em en`. Conclude with `⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩`.
-/
theorem half_period_unique_CM (hcm : CmOK a b c d) (t : ℂ) (h2 : 2 * t ∈ (cmL a b d ha hd lam hlam).lattice)
    (h3 : Formalism.L2.Th1.F.cmTheta 1 d * t ∉ (cmL a b d ha hd lam hlam).lattice)
    (h4 : (1 - Formalism.L2.Th1.F.cmTheta 1 d) * t ∉ (cmL a b d ha hd lam hlam).lattice) :
    t - lam * a / 2 ∈ (cmL a b d ha hd lam hlam).lattice := by
  obtain ⟨hc2, k, hk⟩ := even_c a b c d hcm
  have hform := hcm.1
  have hao : ¬ Even (a : ℤ) := by
    rintro ⟨e, he⟩
    obtain ⟨a', ha2⟩ := hcm.2.1
    omega
  rw [mem_cmL] at h2
  obtain ⟨r, s, hrs⟩ := h2
  have ht : t = pt a b d lam ((r : ℝ) / 2) ((s : ℝ) / 2) := by
    simp only [pt] at hrs ⊢
    push_cast at hrs ⊢
    linear_combination hrs / 2
  have e3 : Formalism.L2.Th1.F.cmTheta 1 d * t
      = pt a b d lam (((-s * c - k * r : ℤ) : ℝ) / 2) (((r * (a : ℤ) + s * (k + 1) : ℤ) : ℝ) / 2) := by
    rw [ht, theta_pt a b c d lam hform k hk]
    simp only [pt]
    push_cast
    ring
  have e4 : (1 - Formalism.L2.Th1.F.cmTheta 1 d) * t
      = pt a b d lam (((r - (-s * c - k * r) : ℤ) : ℝ) / 2)
          (((s - (r * (a : ℤ) + s * (k + 1)) : ℤ) : ℝ) / 2) := by
    rw [sub_mul, one_mul, e3, ht]
    simp only [pt]
    push_cast
    ring
  rw [e3, pt_mem_iff, half_int, half_int] at h3
  rw [e4, pt_mem_iff, half_int, half_int] at h4
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := parity_key r s k (a : ℤ) c hc2 hao h3 h4
  have hpt : lam * (a : ℂ) / 2 = pt a b d lam (1 / 2) 0 := by
    simp only [pt]; push_cast; ring
  rw [ht, hpt, pt_sub, pt_mem_iff]
  have em : ((r - 1 : ℤ) : ℝ) = ((m + m : ℤ) : ℝ) := by exact_mod_cast hm
  have en : ((s : ℤ) : ℝ) = ((n + n : ℤ) : ℝ) := by exact_mod_cast hn
  push_cast at em en
  exact ⟨⟨m, by linarith⟩, ⟨n, by linarith⟩⟩

/- English proof (translation)
The claim follows from `Submodule.ext h`.
-/
theorem lattice_ext {L L' : PeriodPair} (h : ∀ z, z ∈ L.lattice ↔ z ∈ L'.lattice) : L.lattice = L'.lattice := Submodule.ext h

/- English proof (translation)
Establish `hind` using `(Formalism.L2.Th1.F.cmPair a b d ha hd).indep`. Rewrite `hind` using `[LinearIndependent.pair_iff]`. Establish `hθ : Formalism.L2.Th1.F.cmTheta b d ≠ 0`. Introduce `h0`. Use `(hind 0 1 (by show (0 : ℝ) • (a : ℂ) + (1 : ℝ) • Formalism.L2.Th1.F.cmTheta b d = 0` as an intermediate fact.

Rewrite using `[h0]`. Use the proof step `simp)).2`. Evaluate the numerical expressions using `at this`. Establish `hc' : (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`. Establish `hcc : (c : ℂ) * (c : ℂ)⁻¹ = 1` using `mul_inv_cancel₀ hc'`.

Establish `hct : ((c.toNat : ℕ) : ℂ) = (c : ℂ)`. Establish `e : ((c.toNat : ℕ) : ℤ) = c` using `Int.toNat_of_nonneg hc.le`. Conclude with `e` after adjusting the coercions. Establish `h' : 4 * (a : ℂ) * (c : ℂ) = (b : ℂ) ^ 2 + (d : ℂ)` using `by exact_mod_cast h`. Establish `hS : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ)`.

Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]`. Establish `hprod : Formalism.L2.Th1.F.cmTheta b d * Formalism.L2.Th1.F.cmTheta (-b) d = -((a : ℂ) * (c : ℂ))`. Unfold `Formalism.L2.Th1.F.cmTheta`. Use `push_cast`. Take the linear combination `(1 / 4 : ℂ) * h' + (1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq - (1 / 4 : ℂ) * hS`.

Use `⟨lam * Formalism.L2.Th1.F.cmTheta b d / (c : ℂ), div_ne_zero (mul_ne_zero hlam hθ) hc', ?_⟩` and prove the remaining obligations. Apply `lattice_ext` to reduce the goal to its premises. Introduce `z`. Rewrite using `[mem_cmL, mem_cmL]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨r, s, rfl⟩`. Use `⟨-s, r, ?_⟩` and prove the remaining obligations. Simplify using `only [pt]`. Rewrite using `[hct]`. Use `push_cast`.

Take the linear combination `(lam * Formalism.L2.Th1.F.cmTheta b d * (r : ℂ) - lam * (s : ℂ) * (a : ℂ)) * hcc + (lam * (s : ℂ) * (c : ℂ)⁻¹) * hprod`. Introduce and unpack `⟨r, s, rfl⟩`. Use `⟨s, -r, ?_⟩` and prove the remaining obligations. Simplify using `only [pt]`. Rewrite using `[hct]`.

Use `push_cast`. Take the linear combination `(-(lam * (s : ℂ) * Formalism.L2.Th1.F.cmTheta b d) - lam * (r : ℂ) * (a : ℂ)) * hcc + (lam * (r : ℂ) * (c : ℂ)⁻¹) * hprod`.
-/
theorem cmL_swap (hc : 0 < c) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    ∃ (lam' : ℂ) (hlam' : lam' ≠ 0), (cmL c.toNat (-b) d (by omega) hd lam' hlam').lattice = (cmL a b d ha hd lam hlam).lattice := by
  have hind := (Formalism.L2.Th1.F.cmPair a b d ha hd).indep
  rw [LinearIndependent.pair_iff] at hind
  have hθ : Formalism.L2.Th1.F.cmTheta b d ≠ 0 := by
    intro h0
    have := (hind 0 1 (by
      show (0 : ℝ) • (a : ℂ) + (1 : ℝ) • Formalism.L2.Th1.F.cmTheta b d = 0
      rw [h0]; simp)).2
    norm_num at this
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcc : (c : ℂ) * (c : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hc'
  have hct : ((c.toNat : ℕ) : ℂ) = (c : ℂ) := by
    have e : ((c.toNat : ℕ) : ℤ) = c := Int.toNat_of_nonneg hc.le
    exact_mod_cast e
  have h' : 4 * (a : ℂ) * (c : ℂ) = (b : ℂ) ^ 2 + (d : ℂ) := by exact_mod_cast h
  have hS : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hprod : Formalism.L2.Th1.F.cmTheta b d * Formalism.L2.Th1.F.cmTheta (-b) d = -((a : ℂ) * (c : ℂ)) := by
    unfold Formalism.L2.Th1.F.cmTheta
    push_cast
    linear_combination (1 / 4 : ℂ) * h' + (1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq
      - (1 / 4 : ℂ) * hS
  refine ⟨lam * Formalism.L2.Th1.F.cmTheta b d / (c : ℂ), div_ne_zero (mul_ne_zero hlam hθ) hc', ?_⟩
  apply lattice_ext
  intro z
  rw [mem_cmL, mem_cmL]
  constructor
  · rintro ⟨r, s, rfl⟩
    refine ⟨-s, r, ?_⟩
    simp only [pt]
    rw [hct]
    push_cast
    linear_combination (lam * Formalism.L2.Th1.F.cmTheta b d * (r : ℂ) - lam * (s : ℂ) * (a : ℂ)) * hcc
      + (lam * (s : ℂ) * (c : ℂ)⁻¹) * hprod
  · rintro ⟨r, s, rfl⟩
    refine ⟨s, -r, ?_⟩
    simp only [pt]
    rw [hct]
    push_cast
    linear_combination (-(lam * (s : ℂ) * Formalism.L2.Th1.F.cmTheta b d) - lam * (r : ℂ) * (a : ℂ)) * hcc
      + (lam * (r : ℂ) * (c : ℂ)⁻¹) * hprod

/- English proof (translation)
Establish `hind` using `(Formalism.L2.Th1.F.cmPair a b d ha hd).indep`. Rewrite `hind` using `[LinearIndependent.pair_iff]`. Establish `hne : (a : ℂ) + Formalism.L2.Th1.F.cmTheta b d ≠ 0`. Introduce `h0`. Use `(hind 1 1 (by show (1 : ℝ) • (a : ℂ) + (1 : ℝ) • Formalism.L2.Th1.F.cmTheta b d = 0` as an intermediate fact.

Rewrite using `[one_smul, one_smul]`. Conclude with `h0)).1`. Evaluate the numerical expressions using `at this`. Establish `hA : (a : ℂ) + (b : ℂ) + (c : ℂ) ≠ 0`. Establish `e : (((a : ℤ) + b + c : ℤ) : ℂ) ≠ 0` using `by exact_mod_cast hs.ne'`.

Move the coercions through the operations in `at e`. Conclude with `e`. Establish `hAA : ((a : ℂ) + (b : ℂ) + (c : ℂ)) * ((a : ℂ) + (b : ℂ) + (c : ℂ))⁻¹ = 1` using `mul_inv_cancel₀ hA`. Establish `hAt : ((((a : ℤ) + b + c).toNat : ℕ) : ℂ) = (a : ℂ) + (b : ℂ) + (c : ℂ)`. Establish `e : ((((a : ℤ) + b + c).toNat : ℕ) : ℤ) = (a : ℤ) + b + c` using `Int.toNat_of_nonneg hs.le`.

Establish `e' : (((((a : ℤ) + b + c).toNat : ℕ) : ℤ) : ℂ) = (((a : ℤ) + b + c : ℤ) : ℂ)` using `by rw [e]`. Move the coercions through the operations in `at e'`. Conclude with `e'`. Establish `hθ' : Formalism.L2.Th1.F.cmTheta (b + 2 * c) d = Formalism.L2.Th1.F.cmTheta b d + (c : ℂ)`. Unfold `Formalism.L2.Th1.F.cmTheta`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hsq` using `theta_sq a b c d h`. Use `⟨lam * ((a : ℂ) + Formalism.L2.Th1.F.cmTheta b d) / ((a : ℂ) + (b : ℂ) + (c : ℂ)), div_ne_zero (mul_ne_zero hlam hne) hA, ?_⟩` and prove the remaining obligations. Apply `lattice_ext` to reduce the goal to its premises.

Introduce `z`. Rewrite using `[mem_cmL, mem_cmL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, s, rfl⟩`. Use `⟨r, r + s, ?_⟩` and prove the remaining obligations.

Simplify using `only [pt]`. Rewrite using `[hAt, hθ']`. Use `push_cast`. Take the linear combination `(lam * (r : ℂ) * ((a : ℂ) + Formalism.L2.Th1.F.cmTheta b d) + lam * (s : ℂ) * Formalism.L2.Th1.F.cmTheta b d) * hAA + (lam * (s : ℂ) * ((a : ℂ) + (b : ℂ) + (c : ℂ))⁻¹) * hsq`. Introduce and unpack `⟨r, s, rfl⟩`.

Use `⟨r, s - r, ?_⟩` and prove the remaining obligations. Simplify using `only [pt]`. Rewrite using `[hAt, hθ']`. Use `push_cast`. Take the linear combination `(-(lam * (r : ℂ) * ((a : ℂ) + Formalism.L2.Th1.F.cmTheta b d)) - lam * ((s : ℂ) - (r : ℂ)) * Formalism.L2.Th1.F.cmTheta b d) * hAA - (lam * ((s : ℂ) - (r : ℂ)) * ((a : ℂ) + (b : ℂ) + (c : ℂ))⁻¹) * hsq`.
-/
theorem cmL_shift (hs : 0 < (a : ℤ) + b + c) (h : 4 * (a : ℤ) * c = b ^ 2 + d) :
    ∃ (lam' : ℂ) (hlam' : lam' ≠ 0),
      (cmL ((a : ℤ) + b + c).toNat (b + 2 * c) d (by omega) hd lam' hlam').lattice = (cmL a b d ha hd lam hlam).lattice := by
  have hind := (Formalism.L2.Th1.F.cmPair a b d ha hd).indep
  rw [LinearIndependent.pair_iff] at hind
  have hne : (a : ℂ) + Formalism.L2.Th1.F.cmTheta b d ≠ 0 := by
    intro h0
    have := (hind 1 1 (by
      show (1 : ℝ) • (a : ℂ) + (1 : ℝ) • Formalism.L2.Th1.F.cmTheta b d = 0
      rw [one_smul, one_smul]; exact h0)).1
    norm_num at this
  have hA : (a : ℂ) + (b : ℂ) + (c : ℂ) ≠ 0 := by
    have e : (((a : ℤ) + b + c : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
    push_cast at e
    exact e
  have hAA : ((a : ℂ) + (b : ℂ) + (c : ℂ)) * ((a : ℂ) + (b : ℂ) + (c : ℂ))⁻¹ = 1 := mul_inv_cancel₀ hA
  have hAt : ((((a : ℤ) + b + c).toNat : ℕ) : ℂ) = (a : ℂ) + (b : ℂ) + (c : ℂ) := by
    have e : ((((a : ℤ) + b + c).toNat : ℕ) : ℤ) = (a : ℤ) + b + c := Int.toNat_of_nonneg hs.le
    have e' : (((((a : ℤ) + b + c).toNat : ℕ) : ℤ) : ℂ) = (((a : ℤ) + b + c : ℤ) : ℂ) := by rw [e]
    push_cast at e'
    exact e'
  have hθ' : Formalism.L2.Th1.F.cmTheta (b + 2 * c) d = Formalism.L2.Th1.F.cmTheta b d + (c : ℂ) := by
    unfold Formalism.L2.Th1.F.cmTheta
    push_cast
    ring
  have hsq := theta_sq a b c d h
  refine ⟨lam * ((a : ℂ) + Formalism.L2.Th1.F.cmTheta b d) / ((a : ℂ) + (b : ℂ) + (c : ℂ)),
    div_ne_zero (mul_ne_zero hlam hne) hA, ?_⟩
  apply lattice_ext
  intro z
  rw [mem_cmL, mem_cmL]
  constructor
  · rintro ⟨r, s, rfl⟩
    refine ⟨r, r + s, ?_⟩
    simp only [pt]
    rw [hAt, hθ']
    push_cast
    linear_combination (lam * (r : ℂ) * ((a : ℂ) + Formalism.L2.Th1.F.cmTheta b d)
        + lam * (s : ℂ) * Formalism.L2.Th1.F.cmTheta b d) * hAA
      + (lam * (s : ℂ) * ((a : ℂ) + (b : ℂ) + (c : ℂ))⁻¹) * hsq
  · rintro ⟨r, s, rfl⟩
    refine ⟨r, s - r, ?_⟩
    simp only [pt]
    rw [hAt, hθ']
    push_cast
    linear_combination (-(lam * (r : ℂ) * ((a : ℂ) + Formalism.L2.Th1.F.cmTheta b d))
        - lam * ((s : ℂ) - (r : ℂ)) * Formalism.L2.Th1.F.cmTheta b d) * hAA
      - (lam * ((s : ℂ) - (r : ℂ)) * ((a : ℂ) + (b : ℂ) + (c : ℂ))⁻¹) * hsq

end Pt

/- English proof (translation)
Establish `hS : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ)`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]`. Establish `hθsq : Formalism.L2.Th1.F.cmTheta 1 d * Formalism.L2.Th1.F.cmTheta 1 d = Formalism.L2.Th1.F.cmTheta 1 d - (1 + (d : ℂ)) / 4`. Unfold `Formalism.L2.Th1.F.cmTheta`. Use `push_cast`.

Take the linear combination `(1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq - (1 / 4 : ℂ) * hS`. Establish `hkey : ((Formalism.L2.Th1.F.cmTheta 1 d - s) * (Formalism.L2.Th1.F.cmTheta 1 d - p) - r * q) * w1 = 0`. Take the linear combination `(-(Formalism.L2.Th1.F.cmTheta 1 d - s)) * h1 - (q : ℂ) * h2`. Establish `hE` using `(mul_eq_zero.mp hkey).resolve_right hw1`. Establish `hind` using `(Formalism.L2.Th1.F.cmPair 1 1 d one_pos hd).indep`.

Rewrite `hind` using `[LinearIndependent.pair_iff]`. Take `⟨e1, e2⟩` from `hind (((4 * (p * s - r * q) - (1 + d) : ℤ) : ℝ)) (((4 * (1 - p - s) : ℤ) : ℝ)) (by show (((4 * (p * s - r * q) - (1 + d) : ℤ) : ℝ)) • (((1 : ℕ) : ℂ)) + (((4 * (1 - p - s) : ℤ) : ℝ)) • Formalism.L2.Th1.F.cmTheta 1 d = 0`. Rewrite using `[Complex.real_smul, Complex.real_smul]`. Use `push_cast`. Take the linear combination `4 * hE - 4 * hθsq)`.

Establish `e1' : 4 * (p * s - r * q) - (1 + (d : ℤ)) = 0` using `by exact_mod_cast e1`. Establish `e2' : 4 * (1 - p - s) = 0` using `by exact_mod_cast e2`. Establish `hs : s = 1 - p` using `by omega`. Establish `hq' : (q : ℂ) ≠ 0` using `by exact_mod_cast hq.ne'`. Establish `hqq : (q : ℂ) * (q : ℂ)⁻¹ = 1` using `mul_inv_cancel₀ hq'`.

Establish `hθp : Formalism.L2.Th1.F.cmTheta (1 - 2 * p) d = Formalism.L2.Th1.F.cmTheta 1 d - (p : ℂ)`. Unfold `Formalism.L2.Th1.F.cmTheta`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨?_, div_ne_zero hw1 hq', by field_simp, ?_⟩` and prove the remaining obligations.

Substitute `hs` using the available equality. Take the linear combination `e1'`. Rewrite using `[hθp]`. Take the linear combination `(q : ℂ)⁻¹ * h1 - w2 * hqq`.
-/
theorem form_core (d : ℕ) (hd : 0 < d) (w1 w2 : ℂ) (hw1 : w1 ≠ 0) (p q r s : ℤ) (hq : 0 < q)
    (h1 : (p : ℂ) * w1 + (q : ℂ) * w2 = Formalism.L2.Th1.F.cmTheta 1 d * w1)
    (h2 : (r : ℂ) * w1 + (s : ℂ) * w2 = Formalism.L2.Th1.F.cmTheta 1 d * w2) :
    4 * q * (-r) = (1 - 2 * p) ^ 2 + d ∧ w1 / q ≠ 0 ∧ w1 = w1 / q * q ∧ w2 = w1 / q * Formalism.L2.Th1.F.cmTheta (1 - 2 * p) d := by
  have hS : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = (d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]
  have hθsq : Formalism.L2.Th1.F.cmTheta 1 d * Formalism.L2.Th1.F.cmTheta 1 d
      = Formalism.L2.Th1.F.cmTheta 1 d - (1 + (d : ℂ)) / 4 := by
    unfold Formalism.L2.Th1.F.cmTheta
    push_cast
    linear_combination (1 / 4 : ℂ) * ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq - (1 / 4 : ℂ) * hS
  have hkey : ((Formalism.L2.Th1.F.cmTheta 1 d - s) * (Formalism.L2.Th1.F.cmTheta 1 d - p) - r * q) * w1 = 0 := by
    linear_combination (-(Formalism.L2.Th1.F.cmTheta 1 d - s)) * h1 - (q : ℂ) * h2
  have hE := (mul_eq_zero.mp hkey).resolve_right hw1
  have hind := (Formalism.L2.Th1.F.cmPair 1 1 d one_pos hd).indep
  rw [LinearIndependent.pair_iff] at hind
  obtain ⟨e1, e2⟩ := hind (((4 * (p * s - r * q) - (1 + d) : ℤ) : ℝ)) (((4 * (1 - p - s) : ℤ) : ℝ)) (by
    show (((4 * (p * s - r * q) - (1 + d) : ℤ) : ℝ)) • (((1 : ℕ) : ℂ))
      + (((4 * (1 - p - s) : ℤ) : ℝ)) • Formalism.L2.Th1.F.cmTheta 1 d = 0
    rw [Complex.real_smul, Complex.real_smul]
    push_cast
    linear_combination 4 * hE - 4 * hθsq)
  have e1' : 4 * (p * s - r * q) - (1 + (d : ℤ)) = 0 := by exact_mod_cast e1
  have e2' : 4 * (1 - p - s) = 0 := by exact_mod_cast e2
  have hs : s = 1 - p := by omega
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqq : (q : ℂ) * (q : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hq'
  have hθp : Formalism.L2.Th1.F.cmTheta (1 - 2 * p) d = Formalism.L2.Th1.F.cmTheta 1 d - (p : ℂ) := by
    unfold Formalism.L2.Th1.F.cmTheta
    push_cast
    ring
  refine ⟨?_, div_ne_zero hw1 hq', by field_simp, ?_⟩
  · subst hs
    linear_combination e1'
  · rw [hθp]
    linear_combination (q : ℂ)⁻¹ * h1 - w2 * hqq

/- English proof (translation)
Take `⟨hf, hne, he1, he2⟩` from `form_core d hd w1 w2 hw1 p q r s hq h1 h2`. Establish `hqz : ((q.toNat : ℕ) : ℤ) = q` using `Int.toNat_of_nonneg hq.le`. Establish `hqt : ((q.toNat : ℕ) : ℂ) = (q : ℂ)`. Establish `e : (((q.toNat : ℕ) : ℤ) : ℂ) = ((q : ℤ) : ℂ)` using `by rw [hqz]`. Move the coercions through the operations in `at e`.

Conclude with `e`. Use `⟨q.toNat, 1 - 2 * p, -r, by omega, w1 / q, hne, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hqz]`. Take the linear combination `hf`. Apply `lattice_ext` to reduce the goal to its premises.

Introduce `z`. Rewrite using `[PeriodPair.mem_lattice, hL]`. Establish `e1 : (cmL q.toNat (1 - 2 * p) d (by omega) hd (w1 / q) hne).ω₁ = w1` using `by show w1 / q * ((q.toNat : ℕ) : ℂ) = w1`. Rewrite using `[hqt]`. Conclude with `he1.symm`.

Establish `e2 : (cmL q.toNat (1 - 2 * p) d (by omega) hd (w1 / q) hne).ω₂ = w2` using `he2.symm`. Rewrite using `[e1, e2]`.
-/
private theorem exists_cmL_lattice_eq_of_cm_action (d : ℕ) (hd : 0 < d) (L : PeriodPair) (w1 w2 : ℂ) (hw1 : w1 ≠ 0)
    (hL : ∀ z, z ∈ L.lattice ↔ ∃ m n : ℤ, (m : ℂ) * w1 + (n : ℂ) * w2 = z)
    (p q r s : ℤ) (hq : 0 < q)
    (h1 : (p : ℂ) * w1 + (q : ℂ) * w2 = Formalism.L2.Th1.F.cmTheta 1 d * w1)
    (h2 : (r : ℂ) * w1 + (s : ℂ) * w2 = Formalism.L2.Th1.F.cmTheta 1 d * w2) :
    ∃ (a : ℕ) (b c : ℤ) (ha : 0 < a) (lam : ℂ) (hlam : lam ≠ 0), 4 * (a : ℤ) * c = b ^ 2 + d ∧
      (cmL a b d ha hd lam hlam).lattice = L.lattice := by
  obtain ⟨hf, hne, he1, he2⟩ := form_core d hd w1 w2 hw1 p q r s hq h1 h2
  have hqz : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq.le
  have hqt : ((q.toNat : ℕ) : ℂ) = (q : ℂ) := by
    have e : (((q.toNat : ℕ) : ℤ) : ℂ) = ((q : ℤ) : ℂ) := by rw [hqz]
    push_cast at e
    exact e
  refine ⟨q.toNat, 1 - 2 * p, -r, by omega, w1 / q, hne, ?_, ?_⟩
  · rw [hqz]
    linear_combination hf
  · apply lattice_ext
    intro z
    rw [PeriodPair.mem_lattice, hL]
    have e1 : (cmL q.toNat (1 - 2 * p) d (by omega) hd (w1 / q) hne).ω₁ = w1 := by
      show w1 / q * ((q.toNat : ℕ) : ℂ) = w1
      rw [hqt]
      exact he1.symm
    have e2 : (cmL q.toNat (1 - 2 * p) d (by omega) hd (w1 / q) hne).ω₂ = w2 := he2.symm
    rw [e1, e2]

/- English proof (translation)
Establish `hw1 : L.ω₁ ≠ 0`. Introduce `h0`. Establish `hind` using `L.indep`. Rewrite `hind` using `[LinearIndependent.pair_iff]`. Use `(hind 1 0 (by rw [h0]; simp)).1` as an intermediate fact.

Evaluate the numerical expressions using `at this`. Take `⟨p, q, hpq⟩` from `PeriodPair.mem_lattice.mp (hst _ L.ω₁_mem_lattice)`. Take `⟨r, s, hrs⟩` from `PeriodPair.mem_lattice.mp (hst _ L.ω₂_mem_lattice)`. Establish `hq0 : q ≠ 0`. Introduce and unpack `rfl`.

Establish `hθ : Formalism.L2.Th1.F.cmTheta 1 d = (p : ℂ)`. Establish `e : (Formalism.L2.Th1.F.cmTheta 1 d - p) * L.ω₁ = 0`. Move the coercions through the operations in `at hpq`. Take the linear combination `-hpq`. Establish `e'` using `(mul_eq_zero.mp e).resolve_right hw1`.

Take the linear combination `e'`. Establish `hind` using `(Formalism.L2.Th1.F.cmPair 1 1 d one_pos hd).indep`. Rewrite `hind` using `[LinearIndependent.pair_iff]`. Use `(hind (p : ℝ) (-1) (by show (p : ℝ) • (((1 : ℕ) : ℂ)) + (-1 : ℝ) • Formalism.L2.Th1.F.cmTheta 1 d = 0` as an intermediate fact. Rewrite using `[hθ, Complex.real_smul, Complex.real_smul]`.

Use `push_cast`. Use the proof step `ring)).2`. Evaluate the numerical expressions using `at this`. Break down `lt_or_gt_of_ne hq0 with hneg | hpos` into its components or cases. Use `exists_cmL_lattice_eq_of_cm_action d hd L L.ω₁ (-L.ω₂) hw1 (fun z => ?_) p (-q) (-r) s (by omega) (by push_cast; linear_combination hpq) (by push_cast; linear_combination -hrs)` and prove the remaining obligations.

Rewrite using `[PeriodPair.mem_lattice]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, n, h⟩`. Conclude with `⟨m, -n, by push_cast; rw [← h]; ring⟩`. Introduce and unpack `⟨m, n, h⟩`.

Conclude with `⟨m, -n, by push_cast; rw [← h]; ring⟩`. Conclude with `exists_cmL_lattice_eq_of_cm_action d hd L L.ω₁ L.ω₂ hw1 (fun z => PeriodPair.mem_lattice) p q r s hpos hpq hrs`.
-/
theorem exists_form (d : ℕ) (hd : 0 < d) (L : PeriodPair) (hst : ∀ x ∈ L.lattice, Formalism.L2.Th1.F.cmTheta 1 d * x ∈ L.lattice) :
    ∃ (a : ℕ) (b c : ℤ) (ha : 0 < a) (lam : ℂ) (hlam : lam ≠ 0), 4 * (a : ℤ) * c = b ^ 2 + d ∧
      (cmL a b d ha hd lam hlam).lattice = L.lattice := by
  have hw1 : L.ω₁ ≠ 0 := by
    intro h0
    have hind := L.indep
    rw [LinearIndependent.pair_iff] at hind
    have := (hind 1 0 (by rw [h0]; simp)).1
    norm_num at this
  obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.mp (hst _ L.ω₁_mem_lattice)
  obtain ⟨r, s, hrs⟩ := PeriodPair.mem_lattice.mp (hst _ L.ω₂_mem_lattice)
  have hq0 : q ≠ 0 := by
    rintro rfl
    have hθ : Formalism.L2.Th1.F.cmTheta 1 d = (p : ℂ) := by
      have e : (Formalism.L2.Th1.F.cmTheta 1 d - p) * L.ω₁ = 0 := by
        push_cast at hpq
        linear_combination -hpq
      have e' := (mul_eq_zero.mp e).resolve_right hw1
      linear_combination e'
    have hind := (Formalism.L2.Th1.F.cmPair 1 1 d one_pos hd).indep
    rw [LinearIndependent.pair_iff] at hind
    have := (hind (p : ℝ) (-1) (by
      show (p : ℝ) • (((1 : ℕ) : ℂ)) + (-1 : ℝ) • Formalism.L2.Th1.F.cmTheta 1 d = 0
      rw [hθ, Complex.real_smul, Complex.real_smul]
      push_cast
      ring)).2
    norm_num at this
  rcases lt_or_gt_of_ne hq0 with hneg | hpos
  · refine exists_cmL_lattice_eq_of_cm_action d hd L L.ω₁ (-L.ω₂) hw1 (fun z => ?_) p (-q) (-r) s (by omega)
      (by push_cast; linear_combination hpq) (by push_cast; linear_combination -hrs)
    rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, h⟩
      exact ⟨m, -n, by push_cast; rw [← h]; ring⟩
    · rintro ⟨m, n, h⟩
      exact ⟨m, -n, by push_cast; rw [← h]; ring⟩
  · exact exists_cmL_lattice_eq_of_cm_action d hd L L.ω₁ L.ω₂ hw1 (fun z => PeriodPair.mem_lattice) p q r s hpos hpq hrs

/- English proof (translation)
Take `⟨a, b, c, ha, lam, hlam, h, hL⟩` from `exists_form d hd L hst`. Establish `hd' : (0 : ℤ) < d` using `by exact_mod_cast hd`. Establish `ha' : (0 : ℤ) < a` using `by exact_mod_cast ha`. Establish `hc : 0 < c`. Assume the negation of the conclusion as `hcn`.

Use `push_neg at hcn`. Establish `h0 : 0 < 4 * (a : ℤ) * c` using `by rw [h]; linarith [sq_nonneg b]`. Use the polynomial consequences of the given equalities and inequalities. Break down `Nat.even_or_odd a with hae | hao` into its components or cases. Break down `Int.even_or_odd c with hce | hco` into its components or cases.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : Odd b := by`. Break down `Int.even_or_odd b with ⟨t, ht⟩ | hbo` into its components or cases. It suffices to derive a contradiction. Establish `e : 4 * ((a : ℤ) * c) = 4 * (t * t) + (d : ℤ)`. Take the linear combination `h + (b + t + t) * ht`.

Generalize the expression as in `(a : ℤ) * c = P at e`. Generalize the expression as in `t * t = Q at e`. Use linear arithmetic over natural numbers and integers. Conclude with `hbo`. Establish `hs : 0 < (a : ℤ) + b + c`.

Establish `h4 : 0 < 4 * (((a : ℤ) + b + c) * c)`. Rewrite using `[show 4 * (((a : ℤ) + b + c) * c) = (b + 2 * c) ^ 2 + d by linear_combination h]`. Combine the linear relations using `[sq_nonneg (b + 2 * c)]`. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨lam', hlam', hL'⟩` from `cmL_shift a b c d ha hd lam hlam hs h`. Take `⟨m, hm⟩` from `hae`. Take `⟨n, hn⟩` from `hce`. Use `⟨((a : ℤ) + b + c).toNat, b + 2 * c, c, by omega, lam', hlam', ⟨?_, ?_, hd8, hp⟩, hL'.trans hL⟩` and prove the remaining obligations.

Rewrite using `[Int.toNat_of_nonneg hs.le]`. Take the linear combination `h`. Conclude with `⟨((a : ℤ) + b + c).toNat / 2, by omega⟩`. Take `⟨lam', hlam', hL'⟩` from `cmL_swap a b c d ha hd lam hlam hc h`. Take `⟨k, hk⟩` from `hco`.

Use `⟨c.toNat, -b, a, by omega, lam', hlam', ⟨?_, ?_, hd8, hp⟩, hL'.trans hL⟩` and prove the remaining obligations. Rewrite using `[Int.toNat_of_nonneg hc.le]`. Take the linear combination `h`. Conclude with `⟨c.toNat / 2, by omega⟩`. Conclude with `⟨a, b, c, ha, lam, hlam, ⟨h, hao, hd8, hp⟩, hL⟩`.
-/
theorem exists_cmOK (d : ℕ) (hd : 0 < d) (hd8 : d % 8 = 7) (hp : d.Prime) (L : PeriodPair)
    (hst : ∀ x ∈ L.lattice, Formalism.L2.Th1.F.cmTheta 1 d * x ∈ L.lattice) :
    ∃ (a : ℕ) (b c : ℤ) (ha : 0 < a) (lam : ℂ) (hlam : lam ≠ 0), CmOK a b c d ∧ (cmL a b d ha hd lam hlam).lattice = L.lattice := by
  obtain ⟨a, b, c, ha, lam, hlam, h, hL⟩ := exists_form d hd L hst
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have ha' : (0 : ℤ) < a := by exact_mod_cast ha
  have hc : 0 < c := by
    by_contra hcn
    push_neg at hcn
    have h0 : 0 < 4 * (a : ℤ) * c := by rw [h]; linarith [sq_nonneg b]
    nlinarith
  rcases Nat.even_or_odd a with hae | hao
  · rcases Int.even_or_odd c with hce | hco
    · obtain ⟨t, ht⟩ : Odd b := by
        rcases Int.even_or_odd b with ⟨t, ht⟩ | hbo
        · exfalso
          have e : 4 * ((a : ℤ) * c) = 4 * (t * t) + (d : ℤ) := by
            linear_combination h + (b + t + t) * ht
          generalize (a : ℤ) * c = P at e
          generalize t * t = Q at e
          omega
        · exact hbo
      have hs : 0 < (a : ℤ) + b + c := by
        have h4 : 0 < 4 * (((a : ℤ) + b + c) * c) := by
          rw [show 4 * (((a : ℤ) + b + c) * c) = (b + 2 * c) ^ 2 + d by linear_combination h]
          linarith [sq_nonneg (b + 2 * c)]
        by_contra hn
        push_neg at hn
        nlinarith
      obtain ⟨lam', hlam', hL'⟩ := cmL_shift a b c d ha hd lam hlam hs h
      obtain ⟨m, hm⟩ := hae
      obtain ⟨n, hn⟩ := hce
      refine ⟨((a : ℤ) + b + c).toNat, b + 2 * c, c, by omega, lam', hlam', ⟨?_, ?_, hd8, hp⟩, hL'.trans hL⟩
      · rw [Int.toNat_of_nonneg hs.le]
        linear_combination h
      · exact ⟨((a : ℤ) + b + c).toNat / 2, by omega⟩
    · obtain ⟨lam', hlam', hL'⟩ := cmL_swap a b c d ha hd lam hlam hc h
      obtain ⟨k, hk⟩ := hco
      refine ⟨c.toNat, -b, a, by omega, lam', hlam', ⟨?_, ?_, hd8, hp⟩, hL'.trans hL⟩
      · rw [Int.toNat_of_nonneg hc.le]
        linear_combination h
      · exact ⟨c.toNat / 2, by omega⟩
  · exact ⟨a, b, c, ha, lam, hlam, ⟨h, hao, hd8, hp⟩, hL⟩

end Formalism.L2.Ker.KS
