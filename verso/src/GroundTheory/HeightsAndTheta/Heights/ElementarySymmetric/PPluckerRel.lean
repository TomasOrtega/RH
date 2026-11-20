import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.XiPluckerRel
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace PluckerRelations

section Homog

variable {K : Type*} [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hf m h k`. Conclude with `hg m h k`.
-/
theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [DecidableEq K] in
/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

/- English proof (translation)
Introduce `m hm k`. Establish `hm0 : m = 0`. Assume the negation of the conclusion as `h`. Conclude with `(mem_support_iff.1 hm) (by rw [coeff_C, if_neg (Ne.symm h)])`. Substitute `hm0` using the available equality.

Simplify using the standard rewrite rules.
-/
theorem homog_C (r : ℤ) (b : K) : IsMultiHomog (C r : MRing ι) (Pi.single b 0) := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    by_contra h
    exact (mem_support_iff.1 hm) (by rw [coeff_C, if_neg (Ne.symm h)])
  subst hm0
  simp

end Homog

variable {D : ℕ} (S : ProjectiveLineBundle D)

def wedgeVal (k m : S.κ) : S.Ω :=
  S.φ k (S.e 0) * S.φ m (S.e 1) - S.φ k (S.e 1) * S.φ m (S.e 0)

/- English proof (translation)
Establish `h` using `congrArg ψ (S.e.sum_repr u)`. Rewrite `h` using `[Fin.sum_univ_two, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]`. Conclude with `h.symm`.
-/
theorem apply_eq (ψ : S.E →ₗ[S.Ω] S.Ω) (u : S.E) :
    ψ u = S.e.repr u 0 * ψ (S.e 0) + S.e.repr u 1 * ψ (S.e 1) := by
  have h := congrArg ψ (S.e.sum_repr u)
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  exact h.symm

/- English proof (translation)
Rewrite using `[apply_eq S (S.φ k) u, apply_eq S (S.φ m) w, apply_eq S (S.φ k) w, apply_eq S (S.φ m) u]`. Simplify using `only [wedgeVal, T.detE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wedge_mul_detE (k m : S.κ) (u w : S.E) :
    wedgeVal S k m * T.detE S.e u w = S.φ k u * S.φ m w - S.φ k w * S.φ m u := by
  rw [apply_eq S (S.φ k) u, apply_eq S (S.φ m) w, apply_eq S (S.φ k) w, apply_eq S (S.φ m) u]
  simp only [wedgeVal, T.detE]
  ring

/- English proof (translation)
It suffices to establish `h : ∀ y ∈ Submodule.span (chartRing ℤ S.x i) {d | ∃ u ∈ S.B.lat i, ∃ w ∈ S.B.lat i, d = S.x i * T.detE S.e u w}, ∃ a ∈ chartRing ℤ S.x i, wedgeVal S k m * y = S.x i ^ 3 * a from h _ ((S.detGen i hi).1 l)`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, hu, w, hw, rfl⟩` from `hy`.

Take `⟨a₁, ha₁, e₁⟩` from `(mem_lineLat S.x 1 i _).1 (S.dualSec i hi k u hu)`. Take `⟨a₂, ha₂, e₂⟩` from `(mem_lineLat S.x 1 i _).1 (S.dualSec i hi m w hw)`. Take `⟨a₃, ha₃, e₃⟩` from `(mem_lineLat S.x 1 i _).1 (S.dualSec i hi k w hw)`. Take `⟨a₄, ha₄, e₄⟩` from `(mem_lineLat S.x 1 i _).1 (S.dualSec i hi m u hu)`. Use `⟨a₁ * a₂ - a₃ * a₄, sub_mem (mul_mem ha₁ ha₂) (mul_mem ha₃ ha₄), ?_⟩` and prove the remaining obligations.

Establish `h` using `wedge_mul_detE S k m u w`. Rewrite `h` using `[← e₁, ← e₂, ← e₃, ← e₄]`. Take the linear combination `(S.x i) * h`. Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨a, ha, hya⟩` from `hy`. Take `⟨b, hb, hzb⟩` from `hz`. Conclude with `⟨a + b, add_mem ha hb, by rw [mul_add, hya, hzb, mul_add]⟩`. Consider the case `smul r y _ hy`. Take `⟨a, ha, hya⟩` from `hy`.

Use `⟨(r : S.Ω) * a, mul_mem r.2 ha, ?_⟩` and prove the remaining obligations. Rewrite using `[Subalgebra.smul_def, smul_eq_mul]`. Take the linear combination `(r : S.Ω) * hya`.
-/
theorem wedge_mul_delta (i : S.ι) (hi : S.x i ≠ 0) (l : S.ν) (k m : S.κ) :
    ∃ a ∈ chartRing ℤ S.x i, wedgeVal S k m * S.δ l = S.x i ^ 3 * a := by
  suffices h : ∀ y ∈ Submodule.span (chartRing ℤ S.x i)
      {d | ∃ u ∈ S.B.lat i, ∃ w ∈ S.B.lat i, d = S.x i * T.detE S.e u w},
      ∃ a ∈ chartRing ℤ S.x i, wedgeVal S k m * y = S.x i ^ 3 * a from
    h _ ((S.detGen i hi).1 l)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    obtain ⟨a₁, ha₁, e₁⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi k u hu)
    obtain ⟨a₂, ha₂, e₂⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi m w hw)
    obtain ⟨a₃, ha₃, e₃⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi k w hw)
    obtain ⟨a₄, ha₄, e₄⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi m u hu)
    refine ⟨a₁ * a₂ - a₃ * a₄, sub_mem (mul_mem ha₁ ha₂) (mul_mem ha₃ ha₄), ?_⟩
    have h := wedge_mul_detE S k m u w
    rw [← e₁, ← e₂, ← e₃, ← e₄] at h
    linear_combination (S.x i) * h
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hya⟩ := hy
    obtain ⟨b, hb, hzb⟩ := hz
    exact ⟨a + b, add_mem ha hb, by rw [mul_add, hya, hzb, mul_add]⟩
  | smul r y _ hy =>
    obtain ⟨a, ha, hya⟩ := hy
    refine ⟨(r : S.Ω) * a, mul_mem r.2 ha, ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul]
    linear_combination (r : S.Ω) * hya

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coord_base (j : S.ι) :
    T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1) ⟨T.WBlk.base, j⟩ = algebraMap S.Ω S.Φ (S.x j) :=
  rfl

/- English proof (translation)
The claim follows from `rename_X _ _`.
-/
theorem rename_X_base (j : S.ι) :
    (rename (T.yyEmb 0) (X ⟨T.YBlk.base, j⟩ : MRing S.YIdx) : MRing S.WIdx) = X ⟨T.WBlk.base, j⟩ :=
  rename_X _ _

/- English proof (translation)
Proceed by induction on `ha using Algebra.adjoin_induction with`. Consider the case `mem y hy`. Take `⟨j, rfl⟩` from `hy`. Use `⟨1, X ⟨T.YBlk.base, j⟩, exHomog_X _ _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[rename_X_base]`.

Conclude with `exHomog_X (ι := S.WIdx) T.WBlk.base j`. Rewrite using `[rename_X_base, aeval_X, coord_base]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Consider the case `algebraMap r`.

Use `⟨0, C r, homog_C _ _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[rename_C]`. Conclude with `homog_C _ _`. Simplify using the standard rewrite rules. Consider the case `add y z _ _ hy hz`.

Take `⟨d₁, Q₁, h₁, h₁', e₁⟩` from `hy`. Take `⟨d₂, Q₂, h₂, h₂', e₂⟩` from `hz`. Use `⟨d₁ + d₂, Q₁ * X ⟨T.YBlk.base, i⟩ ^ d₂ + Q₂ * X ⟨T.YBlk.base, i⟩ ^ d₁, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `homog_add ?_ ?_` and prove the remaining obligations. Use `exHomog_mul h₁ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) d₂) using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `funext b; cases b <;> simp`. Use `exHomog_mul h₂ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) d₁) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext b; cases b <;> simp [add_comm]`. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, rename_X_base]`. Use `homog_add ?_ ?_` and prove the remaining obligations.

Use `exHomog_mul h₁' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) d₂) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext b; cases b <;> simp`. Use `exHomog_mul h₂' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) d₁) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext b; cases b <;> simp [add_comm]`. Rewrite using `[map_add, map_mul, map_mul, map_pow, map_pow, rename_X_base, map_add, map_mul, map_mul, map_pow, map_pow, aeval_X, e₁, e₂, coord_base]`.

Simplify using `only [map_add, map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul y z _ _ hy hz`. Take `⟨d₁, Q₁, h₁, h₁', e₁⟩` from `hy`. Take `⟨d₂, Q₂, h₂, h₂', e₂⟩` from `hz`.

Use `⟨d₁ + d₂, Q₁ * Q₂, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `exHomog_mul h₁ h₂ using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext b; cases b <;> simp`. Rewrite using `[map_mul]`. Use `exHomog_mul h₁' h₂' using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `funext b; cases b <;> simp`. Rewrite using `[map_mul, map_mul, e₁, e₂]`. Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chart_form (i : S.ι) (hi : S.x i ≠ 0) {a : S.Ω} (ha : a ∈ chartRing ℤ S.x i) :
    ∃ (d : ℕ) (Q : MRing S.YIdx), IsMultiHomog Q (Pi.single T.YBlk.base d) ∧
      IsMultiHomog (rename (T.yyEmb 0) Q : MRing S.WIdx) (Pi.single T.WBlk.base d) ∧
      aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) Q) =
        algebraMap S.Ω S.Φ (S.x i ^ d * a) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine ⟨1, X ⟨T.YBlk.base, j⟩, exHomog_X _ _, ?_, ?_⟩
    · rw [rename_X_base]
      exact exHomog_X (ι := S.WIdx) T.WBlk.base j
    · rw [rename_X_base, aeval_X, coord_base]
      congr 1
      field_simp
  | algebraMap r =>
    refine ⟨0, C r, homog_C _ _, ?_, ?_⟩
    · rw [rename_C]
      exact homog_C _ _
    · simp
  | add y z _ _ hy hz =>
    obtain ⟨d₁, Q₁, h₁, h₁', e₁⟩ := hy
    obtain ⟨d₂, Q₂, h₂, h₂', e₂⟩ := hz
    refine ⟨d₁ + d₂, Q₁ * X ⟨T.YBlk.base, i⟩ ^ d₂ + Q₂ * X ⟨T.YBlk.base, i⟩ ^ d₁, ?_, ?_, ?_⟩
    · refine homog_add ?_ ?_
      · convert exHomog_mul h₁ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) d₂) using 1
        funext b; cases b <;> simp
      · convert exHomog_mul h₂ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) d₁) using 1
        funext b; cases b <;> simp [add_comm]
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, rename_X_base]
      refine homog_add ?_ ?_
      · convert exHomog_mul h₁' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) d₂) using 1
        funext b; cases b <;> simp
      · convert exHomog_mul h₂' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) d₁) using 1
        funext b; cases b <;> simp [add_comm]
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, rename_X_base, map_add, map_mul, map_mul, map_pow, map_pow,
        aeval_X, e₁, e₂, coord_base]
      simp only [map_add, map_mul, map_pow]
      ring
  | mul y z _ _ hy hz =>
    obtain ⟨d₁, Q₁, h₁, h₁', e₁⟩ := hy
    obtain ⟨d₂, Q₂, h₂, h₂', e₂⟩ := hz
    refine ⟨d₁ + d₂, Q₁ * Q₂, ?_, ?_, ?_⟩
    · convert exHomog_mul h₁ h₂ using 1
      funext b; cases b <;> simp
    · rw [map_mul]
      convert exHomog_mul h₁' h₂' using 1
      funext b; cases b <;> simp
    · rw [map_mul, map_mul, e₁, e₂]
      simp only [map_mul, map_pow]
      ring

/- English proof (translation)
Distinguish the cases in `hi : S.x i = 0`. Use `⟨0, 0, homog_zero _, homog_zero _, ?_⟩` and prove the remaining obligations. Simplify using `[hi]`. Take `⟨a, ha, hpa⟩` from `wedge_mul_delta S i hi l k m`. Take `⟨d, Q, hQ, hQ', hv⟩` from `chart_form S i hi ha`.

Use `⟨d, Q * X ⟨T.YBlk.base, i⟩ ^ 4, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `exHomog_mul hQ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) 4) using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext b; cases b <;> simp`. Rewrite using `[map_mul, map_pow, rename_X_base]`. Use `exHomog_mul hQ' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) 4) using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `funext b; cases b <;> simp`. Rewrite using `[map_mul, map_pow, rename_X_base, map_mul, map_pow, aeval_X, hv, coord_base, hpa]`. Simplify using `only [map_mul, map_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem key (i : S.ι) (l : S.ν) (k m : S.κ) :
    ∃ (d : ℕ) (Q : MRing S.YIdx), IsMultiHomog Q (Pi.single T.YBlk.base (d + 4)) ∧
      IsMultiHomog (rename (T.yyEmb 0) Q : MRing S.WIdx) (Pi.single T.WBlk.base (d + 4)) ∧
      aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) Q) =
        algebraMap S.Ω S.Φ (S.x i ^ (d + 1) * (wedgeVal S k m * S.δ l)) := by
  by_cases hi : S.x i = 0
  · refine ⟨0, 0, homog_zero _, homog_zero _, ?_⟩
    simp [hi]
  · obtain ⟨a, ha, hpa⟩ := wedge_mul_delta S i hi l k m
    obtain ⟨d, Q, hQ, hQ', hv⟩ := chart_form S i hi ha
    refine ⟨d, Q * X ⟨T.YBlk.base, i⟩ ^ 4, ?_, ?_, ?_⟩
    · convert exHomog_mul hQ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) 4) using 1
      funext b; cases b <;> simp
    · rw [map_mul, map_pow, rename_X_base]
      convert exHomog_mul hQ' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) 4) using 1
      funext b; cases b <;> simp
    · rw [map_mul, map_pow, rename_X_base, map_mul, map_pow, aeval_X, hv, coord_base, hpa]
      simp only [map_mul, map_pow]
      ring

end PluckerRelations

open PluckerRelations in

/- English proof (translation)
Introduce `D S`. Use `choose d Q hQ hQ' hv using PluckerRelations.key S`. Use `set N : ℕ := (Finset.univ.sup fun t : S.ι × S.ν × S.κ × S.κ => d t.1 t.2.1 t.2.2.1 t.2.2.2) + 1 with hN`. Establish `hle : ∀ i l k m, d i l k m + 1 ≤ N` using `fun i l k m => by`. Use `Finset.le_sup (f := fun t : S.ι × S.ν × S.κ × S.κ => d t.1 t.2.1 t.2.2.1 t.2.2.2) (Finset.mem_univ (i, l, k, m))` as an intermediate fact.

Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Use `⟨N, fun i l k m => Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1)), fun i l k m => ?_, fun i l k m => ?_⟩` and prove the remaining obligations. Establish `h` using `hle i l k m`. Use `exHomog_mul (hQ i l k m) (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) (N - (d i l k m + 1))) using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `funext b; cases b <;> simp; omega`. Establish `h` using `hle i l k m`. Establish `hRF : IsMultiHomog (rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1))) : MRing S.WIdx) (Pi.single T.WBlk.base (N + 3))`. Rewrite using `[map_mul, map_pow, rename_X_base]`. Use `exHomog_mul (hQ' i l k m) (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) (N - (d i l k m + 1))) using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `funext b; cases b <;> simp; omega`. Establish `hpl : IsMultiHomog (S.pluckerWW k m) (Pi.single T.WBlk.line0 1 + Pi.single T.WBlk.line1 1)` using `exHomog_sub (exHomog_mul (exHomog_X (ι := S.WIdx) T.WBlk.line0 k) (exHomog_X (ι := S.WIdx) T.WBlk.line1 m)) (exHomog_mul (exHomog_X (ι := S.WIdx) T.WBlk.line0 m) (exHomog_X (ι := S.WIdx) T.WBlk.line1 k))`. Establish `hP : IsMultiHomog (S.g * rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1))) - S.h * S.pluckerWW k m * X ⟨.det, l⟩ * X ⟨.base, i⟩ ^ N) (T.wwDeg S.n 1 + Pi.single T.WBlk.base (N + 3))`. Use `exHomog_sub (exHomog_mul S.g_deg hRF) ?_` and prove the remaining obligations. Use `exHomog_mul (exHomog_mul (exHomog_mul S.h_deg hpl) (exHomog_X (ι := S.WIdx) T.WBlk.det l)) (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) N) using 1` and compare the differences between its conclusion and the goal.

Apply the tactic sequence `funext b; cases b <;> simp [T.wwDeg] <;> omega`. Establish `hF : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1)))) = algebraMap S.Ω S.Φ (S.x i ^ N * (wedgeVal S k m * S.δ l))`. Rewrite using `[map_mul, map_pow, rename_X_base, map_mul, map_pow, aeval_X, hv, coord_base, ← map_pow, ← map_mul]`. Use `congr 1`. Use `conv_rhs => rw [← Nat.sub_add_cancel h, pow_add]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hpv : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (S.pluckerWW k m) = (S.a 1 - S.a 0) * algebraMap S.Ω S.Φ (wedgeVal S k m)`. Simplify using `only [ProjectiveLineBundle.pluckerWW, map_sub, map_mul, aeval_X, T.wwCoord, T.lineVal, wedgeVal]`. Expand and normalize the polynomial expressions, which then agree. Use `show _ ∈ RingHom.ker (T.multiConeMap (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)))`.

Rewrite using `[RingHom.mem_ker, DiagRAux.multiConeMap_of_homog _ _ _ hP]`. It suffices to establish `h0 : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (S.g * rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1))) - S.h * S.pluckerWW k m * X ⟨.det, l⟩ * X ⟨.base, i⟩ ^ N) = 0 by`. Rewrite using `[h0, C_0, zero_mul]`. Rewrite using `[map_sub, map_mul (aeval _) S.g, hF]`. Simplify using `only [map_mul, map_pow, aeval_X, hpv, S.quot]`.

Simplify using `only [T.wwCoord, T.diagSec]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem PluckerRel.proof : PluckerRel.Statement := by
  intro D S
  classical
  choose d Q hQ hQ' hv using PluckerRelations.key S
  set N : ℕ := (Finset.univ.sup fun t : S.ι × S.ν × S.κ × S.κ => d t.1 t.2.1 t.2.2.1 t.2.2.2) + 1 with hN
  have hle : ∀ i l k m, d i l k m + 1 ≤ N := fun i l k m => by
    have := Finset.le_sup (f := fun t : S.ι × S.ν × S.κ × S.κ => d t.1 t.2.1 t.2.2.1 t.2.2.2)
      (Finset.mem_univ (i, l, k, m))
    simp only at this
    omega
  refine ⟨N, fun i l k m => Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1)), fun i l k m => ?_,
    fun i l k m => ?_⟩
  · have h := hle i l k m
    convert exHomog_mul (hQ i l k m) (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) (N - (d i l k m + 1)))
      using 1
    funext b; cases b <;> simp; omega
  · have h := hle i l k m
    have hRF : IsMultiHomog (rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1))) :
        MRing S.WIdx) (Pi.single T.WBlk.base (N + 3)) := by
      rw [map_mul, map_pow, rename_X_base]
      convert exHomog_mul (hQ' i l k m) (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i)
        (N - (d i l k m + 1))) using 1
      funext b; cases b <;> simp; omega
    have hpl : IsMultiHomog (S.pluckerWW k m) (Pi.single T.WBlk.line0 1 + Pi.single T.WBlk.line1 1) :=
      exHomog_sub (exHomog_mul (exHomog_X (ι := S.WIdx) T.WBlk.line0 k) (exHomog_X (ι := S.WIdx) T.WBlk.line1 m))
        (exHomog_mul (exHomog_X (ι := S.WIdx) T.WBlk.line0 m) (exHomog_X (ι := S.WIdx) T.WBlk.line1 k))
    have hP : IsMultiHomog (S.g * rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1))) -
        S.h * S.pluckerWW k m * X ⟨.det, l⟩ * X ⟨.base, i⟩ ^ N)
        (T.wwDeg S.n 1 + Pi.single T.WBlk.base (N + 3)) := by
      refine exHomog_sub (exHomog_mul S.g_deg hRF) ?_
      convert exHomog_mul (exHomog_mul (exHomog_mul S.h_deg hpl) (exHomog_X (ι := S.WIdx) T.WBlk.det l))
        (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) N) using 1
      funext b; cases b <;> simp [T.wwDeg] <;> omega
    have hF : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1)))) =
        algebraMap S.Ω S.Φ (S.x i ^ N * (wedgeVal S k m * S.δ l)) := by
      rw [map_mul, map_pow, rename_X_base, map_mul, map_pow, aeval_X, hv, coord_base, ← map_pow, ← map_mul]
      congr 1
      conv_rhs => rw [← Nat.sub_add_cancel h, pow_add]
      ring
    have hpv : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (S.pluckerWW k m) = (S.a 1 - S.a 0) * algebraMap S.Ω S.Φ (wedgeVal S k m) := by
      simp only [ProjectiveLineBundle.pluckerWW, map_sub, map_mul, aeval_X, T.wwCoord, T.lineVal, wedgeVal]
      ring
    show _ ∈ RingHom.ker (T.multiConeMap (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)))
    rw [RingHom.mem_ker, DiagRAux.multiConeMap_of_homog _ _ _ hP]
    suffices h0 : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (S.g * rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1))) -
        S.h * S.pluckerWW k m * X ⟨.det, l⟩ * X ⟨.base, i⟩ ^ N) = 0 by
      rw [h0, C_0, zero_mul]
    rw [map_sub, map_mul (aeval _) S.g, hF]
    simp only [map_mul, map_pow, aeval_X, hpv, S.quot]
    simp only [T.wwCoord, T.diagSec]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
