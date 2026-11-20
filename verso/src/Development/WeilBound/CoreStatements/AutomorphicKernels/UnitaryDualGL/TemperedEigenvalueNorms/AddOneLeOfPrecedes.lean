import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitaryDualGL.TemperedEigenvalueNorms.Centred

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace PositivityTheory.UdReth2

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨⟨-, -, hnsub⟩, j, hj, hfirst⟩` from `hP`. Establish `hf : Δ'.first.nu (y : ℂ) = (Δ.first.nu (x : ℂ)).nu (j : ℂ)` using `hfirst`. Establish `hρ' : Δ'.first = Δ.first.nu (((x + j - y : ℝ)) : ℂ)`. Establish `h1` using `congrArg (fun r => r.nu (-(y : ℂ))) hf`. Simplify using `only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h1`.

Rewrite using `[h1]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hd : Δ'.d = Δ.d` using `congrArg Sigma.fst hρ'`.

Take `⟨ω, -, hω⟩` from `exists_smooth_hasCentralChar Δ.first.2.rep.smooth Δ.first.2.rep.irr`. Establish `hω' : HasCentralChar Δ'.first.rep (ω * absPow k (((x + j - y : ℝ)) : ℂ) ^ Δ.first.1)`. Rewrite using `[hρ']`. Conclude with `GlobalTheory.LocGL.UnitaryOrder.hasCentralChar_nu _ hω _`. Take `⟨ϖ, hϖ⟩` from `exists_uniformizer k`.

Establish `hne : nabs k ϖ ≠ 1` using `fun e => uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)`. Establish `hL0 : Real.log (nabs k ϖ) ≠ 0` using `Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) hne`. Establish `hA` using `hΔ ω hω ϖ`. Establish `hA'` using `hΔ' _ hω' ϖ`. Rewrite `hA'` using `[GlobalTheory.LocGL.UnitaryOrder.log_norm_mul_absPow, hd]`.

Establish `hdL : (Δ.d : ℝ) * Real.log (nabs k ϖ) ≠ 0` using `mul_ne_zero (Nat.cast_ne_zero.2 Δ.d_pos.ne') hL0`. Establish `ht : x + j - y = ((Δ.len : ℝ) - Δ'.len) / 2`. Apply `mul_left_cancel₀ hdL` to reduce the goal to its premises. Establish `e1 : (Δ.first.1 : ℝ) = Δ.d` using `rfl`. Rewrite `hA'` using `[e1]`.

Take the linear combination `hA' - hA`. Establish `hlen : Δ.len < j + Δ'.len`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hnsub` to reduce the goal to its premises.

Introduce `w hw`. Take `⟨a, ha, rfl⟩` from `Segment.mem_carrier.1 hw`. Use `Segment.mem_carrier.2 ⟨j + a, ?_, ?_⟩` and prove the remaining obligations. Establish `ha' : a < Δ'.len` using `ha show j + a < Δ.len`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hfirst, IrrGL.nu_nu]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hj1 : (1 : ℝ) ≤ j` using `by exact_mod_cast hj`. Establish `hl1 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len` using `by exact_mod_cast hlen`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem add_one_le_of_precedes (Δ Δ' : Segment k) (hΔ : IsCentred Δ) (hΔ' : IsCentred Δ') (x y : ℝ)
    (hP : (Δ.nu x).Precedes (Δ'.nu y)) : x + 1 ≤ y := by
  obtain ⟨⟨-, -, hnsub⟩, j, hj, hfirst⟩ := hP
  have hf : Δ'.first.nu (y : ℂ) = (Δ.first.nu (x : ℂ)).nu (j : ℂ) := hfirst
  have hρ' : Δ'.first = Δ.first.nu (((x + j - y : ℝ)) : ℂ) := by
    have h1 := congrArg (fun r => r.nu (-(y : ℂ))) hf
    simp only [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h1
    rw [h1]
    congr 1
    push_cast
    ring
  have hd : Δ'.d = Δ.d := congrArg Sigma.fst hρ'
  obtain ⟨ω, -, hω⟩ := exists_smooth_hasCentralChar Δ.first.2.rep.smooth Δ.first.2.rep.irr
  have hω' : HasCentralChar Δ'.first.rep (ω * absPow k (((x + j - y : ℝ)) : ℂ) ^ Δ.first.1) := by
    rw [hρ']
    exact GlobalTheory.LocGL.UnitaryOrder.hasCentralChar_nu _ hω _
  obtain ⟨ϖ, hϖ⟩ := exists_uniformizer k
  have hne : nabs k ϖ ≠ 1 := fun e => uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 e)
  have hL0 : Real.log (nabs k ϖ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) hne
  have hA := hΔ ω hω ϖ
  have hA' := hΔ' _ hω' ϖ
  rw [GlobalTheory.LocGL.UnitaryOrder.log_norm_mul_absPow, hd] at hA'
  have hdL : (Δ.d : ℝ) * Real.log (nabs k ϖ) ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 Δ.d_pos.ne') hL0
  have ht : x + j - y = ((Δ.len : ℝ) - Δ'.len) / 2 := by
    apply mul_left_cancel₀ hdL
    have e1 : (Δ.first.1 : ℝ) = Δ.d := rfl
    rw [e1] at hA'
    linear_combination hA' - hA
  have hlen : Δ.len < j + Δ'.len := by
    by_contra hcon
    push_neg at hcon
    apply hnsub
    intro w hw
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hw
    refine Segment.mem_carrier.2 ⟨j + a, ?_, ?_⟩
    · have ha' : a < Δ'.len := ha
      show j + a < Δ.len
      omega
    · rw [hfirst, IrrGL.nu_nu]
      push_cast
      rfl
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hl1 : (Δ.len : ℝ) + 1 ≤ j + Δ'.len := by exact_mod_cast hlen
  linarith

end Local

end PositivityTheory.UdReth2
