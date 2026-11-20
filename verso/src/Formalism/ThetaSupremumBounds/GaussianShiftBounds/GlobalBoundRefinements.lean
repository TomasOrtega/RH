import Mathlib
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.ThetaSupremumBounds.DivIneqExplicit6
import Formalism.ThetaSupremumBounds.FinalJ

open Finset
open scoped Real

namespace Formalism.DimensionVariation

open Formalism.LatticeIndexTer (ph)

/- English proof (translation)
Introduce `J Pl Emb _ _ _ _ r ν g0 logK MainNotions logOmτ logth0 logh logh' hK logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 h32 hmean hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0`. Establish `main : ∀ j, hK j ≤ sizeB ν logOm f m N L La C0 j`. Introduce `j`. Unfold `liftedMapLogSize at h32`. Unfold `sizeB`.

Establish `hE : (0 : ℝ) < (Fintype.card Emb : ℝ)` using `by exact_mod_cast Fintype.card_pos`. Use `set E : ℝ := (Fintype.card Emb : ℝ) with hEdef`. Use `set F : ℝ := (Fintype.card Pl : ℝ) with hFdef`. Establish `hF0 : 0 ≤ F` using `Nat.cast_nonneg _`. Establish `hf0 : 0 ≤ f` using `le_trans hF0 hcard`.

Establish `hLa0 : 0 ≤ La` using `le_trans hL hLLa`. Take `⟨hG0, hGN⟩` from `hg0 j`. Establish `hOm' : ∀ τ, ∑ s, logOmτ τ s = logOm * E` using `fun τ => (div_eq_iff hE.ne').mp (hOm τ)`. Establish `hth' : ∑ s, logth0 s ≤ C3 * L * E` using `(div_le_iff₀ hE).mp hth`. Use `set X : ℝ := F * g0 j * (c5 * La) + 2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) + F * (1 + 2 * g0 j * (c6 * La)) + 2 * (C4 * f * N ^ 2 * (L + logT + logg)) with hX`.

Establish `hs : ∀ s, logK j s ≤ (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) + F * g0 j * logth0 s + X`. Introduce `s`. Establish `a1 : F * g0 j * Real.log (8 + 32 * (F * g0 j) * v) ≤ F * g0 j * (c5 * La)` using `mul_le_mul_of_nonneg_left (h5 j) (mul_nonneg hF0 hG0)`. Establish `a2 : (∑ τ : Pl, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) ≤ F * (1 + 2 * g0 j * (c6 * La))`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum (fun τ _ => ?_)` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left (h6 j τ) (by linarith : 0 ≤ 2 * g0 j)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = F * (1 + 2 * g0 j * (c6 * La)) := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Establish `a3` using `hSK j s`. Establish `a4` using `hh j`. Establish `a5` using `hh' j`. Establish `a6` using `h32 j s`. Rewrite using `[hX]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum : ∑ s, logK j s ≤ E * (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOm)) + F * g0 j * (C3 * L * E) + E * X`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]`. Simplify using `[hEdef]`.

Use `_ = E * (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOm)) + F * g0 j * (∑ s, logth0 s) + E * X := by`. Use `congr 2`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum, hOm' τ]`.

Simplify using `[hEdef]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := by`. Use `mul_le_mul_of_nonneg_left hth' (mul_nonneg hF0 hG0)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hN2 : 0 ≤ N ^ 2` using `by positivity`. Establish `hN21 : 1 ≤ N ^ 2` using `one_le_pow₀ hN`. Establish `hm2 : 0 ≤ m ^ 2` using `by positivity`. Establish `hm3 : m ≤ m ^ 3` using `le_self_pow₀ hm (by norm_num)`. Establish `hFG : F * g0 j ≤ f * N ^ 2` using `mul_le_mul hcard hGN hG0 hf0`.

Establish `hfN : 0 ≤ f * N ^ 2` using `mul_nonneg hf0 hN2`. Establish `t1 : F * g0 j * (C3 * L) ≤ C3 * (f * N ^ 2 * La)`. Establish `b1 : C3 * L ≤ C3 * La` using `mul_le_mul_of_nonneg_left hLLa p3`. Use `mul_le_mul hFG b1 (mul_nonneg p3 hL) hfN` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `t2 : F * g0 j * (c5 * La) ≤ c5 * (f * N ^ 2 * La)`. Use `mul_le_mul_of_nonneg_right hFG (mul_nonneg p5 hLa0)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmL : L ≤ m * L` using `le_mul_of_one_le_left hL hm`. Establish `hmL0 : 0 ≤ m * L` using `by positivity`.

Establish `hC8 : C8 * L ≤ C8 * (m * L)` using `mul_le_mul_of_nonneg_left hmL p8`. Establish `t3 : 2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) ≤ 2 * C2 * (C7 + C8) * (f * m ^ 3 * N ^ 2 * L)`. Establish `b0 : (C7 + C8) * (m * L) = C7 * m * L + C8 * (m * L)` using `by ring`. Establish `b1 : logg + logT ≤ (C7 + C8) * (m * L)` using `by rw [b0]; linarith`. Establish `b2 : 0 ≤ C2 * f * m ^ 2 * N ^ 2` using `by positivity`.

Establish `b3` using `mul_le_mul_of_nonneg_left b1 b2`. Establish `b4 : C2 * f * m ^ 2 * N ^ 2 * ((C7 + C8) * (m * L)) = C2 * (C7 + C8) * (f * m ^ 3 * N ^ 2 * L)` using `by ring`. Rewrite `b3` using `[b4]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `t4 : F * (1 + 2 * g0 j * (c6 * La)) ≤ f * N ^ 2 * La + 2 * c6 * (f * N ^ 2 * La)`.

Establish `c0 : 0 ≤ c6 * La` using `mul_nonneg p6 hLa0`. Establish `b0` using `mul_le_mul_of_nonneg_right hGN c0`. Establish `b1 : 1 + 2 * g0 j * (c6 * La) ≤ 1 + 2 * N ^ 2 * (c6 * La)` using `by linarith`. Establish `b2 : F * (1 + 2 * g0 j * (c6 * La)) ≤ f * (1 + 2 * N ^ 2 * (c6 * La))` using `mul_le_mul hcard b1 (by positivity) hf0`. Establish `b3 : f ≤ f * N ^ 2 * La`.

Establish `b5 : 1 ≤ N ^ 2 * La` using `one_le_mul_of_one_le_of_one_le hN21 hLa`. Establish `b6` using `mul_le_mul_of_nonneg_left b5 hf0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `b4 : f * (1 + 2 * N ^ 2 * (c6 * La)) = f + 2 * c6 * (f * N ^ 2 * La)` using `by ring`. Rewrite `b2` using `[b4]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `t5 : 2 * (C4 * f * N ^ 2 * (L + logT + logg)) ≤ 2 * C4 * (1 + C7 + C8) * (f * m ^ 3 * N ^ 2 * L)`. Establish `b0 : (1 + C7 + C8) * (m * L) = m * L + C7 * m * L + C8 * (m * L)` using `by ring`. Establish `b1 : L + logT + logg ≤ (1 + C7 + C8) * (m * L)` using `by rw [b0]; linarith`. Establish `b3 : (1 + C7 + C8) * (m * L) ≤ (1 + C7 + C8) * (m ^ 3 * L)` using `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm3 hL) (by linarith)`.

Establish `b2 : 0 ≤ C4 * f * N ^ 2` using `by positivity`. Establish `b4` using `mul_le_mul_of_nonneg_left (le_trans b1 b3) b2`. Establish `b5 : C4 * f * N ^ 2 * ((1 + C7 + C8) * (m ^ 3 * L)) = C4 * (1 + C7 + C8) * (f * m ^ 3 * N ^ 2 * L)` using `by ring`. Rewrite `b4` using `[b5]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hU : 0 ≤ f * N ^ 2 * La` using `mul_nonneg hfN hLa0`. Establish `hW : 0 ≤ f * m ^ 3 * N ^ 2 * L` using `by positivity`. Establish `k1 : 0 ≤ 2 * C2 * (C7 + C8)` using `by positivity`. Establish `k2 : 0 ≤ 2 * C4 * (1 + C7 + C8)` using `by positivity`. Establish `u1 : (C3 + c5 + 2 * c6 + 1) * (f * N ^ 2 * La) ≤ C0 * (f * N ^ 2 * La)` using `mul_le_mul_of_nonneg_right (by linarith) hU`.

Establish `u3 : (2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8)) * (f * m ^ 3 * N ^ 2 * L) ≤ C0 * (f * m ^ 3 * N ^ 2 * L)` using `mul_le_mul_of_nonneg_right (by linarith) hW`. Establish `hfin : F * g0 j * (C3 * L) + X ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)`. Establish `e0 : C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L) = C0 * (f * N ^ 2 * La) + C0 * (f * m ^ 3 * N ^ 2 * L)` using `by ring`. Rewrite using `[hX, e0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `show hK j ≤ (∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm)) + C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)`. Rewrite using `[hmean j, div_le_iff₀ hE]`. Establish `hfinE` using `mul_le_mul_of_nonneg_left hfin hE.le`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨main, fun _ => C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L), ?_, fun j => le_rfl⟩` and prove the remaining obligations.

Introduce `j`. Use `main j` as an intermediate fact. Unfold `sizeB at this`. Conclude with `this`.
-/
theorem first_descent_explicit : StepDi6 := by
  intro J Pl Emb _ _ _ _ r ν g0 logK MainNotions logOmτ logth0 logh logh' hK logOm v f m N L La logT logg
    C2 C3 C4 c5 c6 C7 C8 C0 h32 hmean hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  have main : ∀ j, hK j ≤ sizeB ν logOm f m N L La C0 j := by
    intro j
    unfold liftedMapLogSize at h32
    unfold sizeB
    have hE : (0 : ℝ) < (Fintype.card Emb : ℝ) := by exact_mod_cast Fintype.card_pos
    set E : ℝ := (Fintype.card Emb : ℝ) with hEdef
    set F : ℝ := (Fintype.card Pl : ℝ) with hFdef
    have hF0 : 0 ≤ F := Nat.cast_nonneg _
    have hf0 : 0 ≤ f := le_trans hF0 hcard
    have hLa0 : 0 ≤ La := le_trans hL hLLa
    obtain ⟨hG0, hGN⟩ := hg0 j
    have hOm' : ∀ τ, ∑ s, logOmτ τ s = logOm * E := fun τ => (div_eq_iff hE.ne').mp (hOm τ)
    have hth' : ∑ s, logth0 s ≤ C3 * L * E := (div_le_iff₀ hE).mp hth

    set X : ℝ := F * g0 j * (c5 * La) + 2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) +
      F * (1 + 2 * g0 j * (c6 * La)) + 2 * (C4 * f * N ^ 2 * (L + logT + logg)) with hX
    have hs : ∀ s, logK j s ≤ (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
        F * g0 j * logth0 s + X := by
      intro s
      have a1 : F * g0 j * Real.log (8 + 32 * (F * g0 j) * v) ≤ F * g0 j * (c5 * La) :=
        mul_le_mul_of_nonneg_left (h5 j) (mul_nonneg hF0 hG0)
      have a2 : (∑ τ : Pl, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2))) ≤
          F * (1 + 2 * g0 j * (c6 * La)) := by
        calc (∑ τ : Pl, (1 + 2 * g0 j * Real.log (2 * (∑ i, ν j τ i) + 2)))
            ≤ ∑ _τ : Pl, (1 + 2 * g0 j * (c6 * La)) := by
              refine Finset.sum_le_sum (fun τ _ => ?_)
              have := mul_le_mul_of_nonneg_left (h6 j τ) (by linarith : 0 ≤ 2 * g0 j)
              linarith
          _ = F * (1 + 2 * g0 j * (c6 * La)) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have a3 := hSK j s
      have a4 := hh j
      have a5 := hh' j
      have a6 := h32 j s
      rw [hX]; linarith
    have hsum : ∑ s, logK j s ≤
        E * (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOm)) + F * g0 j * (C3 * L * E) + E * X := by
      calc ∑ s, logK j s ≤ ∑ s, ((∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
            F * g0 j * logth0 s + X) := Finset.sum_le_sum (fun s _ => hs s)
        _ = (∑ τ, ∑ s, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOmτ τ s)) +
            F * g0 j * (∑ s, logth0 s) + E * X := by
              rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_comm, ← Finset.mul_sum]
              simp [hEdef]
        _ = E * (∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * logOm)) +
            F * g0 j * (∑ s, logth0 s) + E * X := by
              congr 2
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl (fun τ _ => ?_)
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hOm' τ]
              simp [hEdef]; ring
        _ ≤ _ := by
              have := mul_le_mul_of_nonneg_left hth' (mul_nonneg hF0 hG0)
              linarith

    have hN2 : 0 ≤ N ^ 2 := by positivity
    have hN21 : 1 ≤ N ^ 2 := one_le_pow₀ hN
    have hm2 : 0 ≤ m ^ 2 := by positivity
    have hm3 : m ≤ m ^ 3 := le_self_pow₀ hm (by norm_num)
    have hFG : F * g0 j ≤ f * N ^ 2 := mul_le_mul hcard hGN hG0 hf0
    have hfN : 0 ≤ f * N ^ 2 := mul_nonneg hf0 hN2
    have t1 : F * g0 j * (C3 * L) ≤ C3 * (f * N ^ 2 * La) := by
      have b1 : C3 * L ≤ C3 * La := mul_le_mul_of_nonneg_left hLLa p3
      have := mul_le_mul hFG b1 (mul_nonneg p3 hL) hfN
      linarith
    have t2 : F * g0 j * (c5 * La) ≤ c5 * (f * N ^ 2 * La) := by
      have := mul_le_mul_of_nonneg_right hFG (mul_nonneg p5 hLa0)
      linarith
    have hmL : L ≤ m * L := le_mul_of_one_le_left hL hm
    have hmL0 : 0 ≤ m * L := by positivity
    have hC8 : C8 * L ≤ C8 * (m * L) := mul_le_mul_of_nonneg_left hmL p8
    have t3 : 2 * (C2 * f * m ^ 2 * N ^ 2 * (logg + logT)) ≤
        2 * C2 * (C7 + C8) * (f * m ^ 3 * N ^ 2 * L) := by
      have b0 : (C7 + C8) * (m * L) = C7 * m * L + C8 * (m * L) := by ring
      have b1 : logg + logT ≤ (C7 + C8) * (m * L) := by rw [b0]; linarith
      have b2 : 0 ≤ C2 * f * m ^ 2 * N ^ 2 := by positivity
      have b3 := mul_le_mul_of_nonneg_left b1 b2
      have b4 : C2 * f * m ^ 2 * N ^ 2 * ((C7 + C8) * (m * L)) =
          C2 * (C7 + C8) * (f * m ^ 3 * N ^ 2 * L) := by ring
      rw [b4] at b3
      linarith
    have t4 : F * (1 + 2 * g0 j * (c6 * La)) ≤ f * N ^ 2 * La + 2 * c6 * (f * N ^ 2 * La) := by
      have c0 : 0 ≤ c6 * La := mul_nonneg p6 hLa0
      have b0 := mul_le_mul_of_nonneg_right hGN c0
      have b1 : 1 + 2 * g0 j * (c6 * La) ≤ 1 + 2 * N ^ 2 * (c6 * La) := by linarith
      have b2 : F * (1 + 2 * g0 j * (c6 * La)) ≤ f * (1 + 2 * N ^ 2 * (c6 * La)) :=
        mul_le_mul hcard b1 (by positivity) hf0
      have b3 : f ≤ f * N ^ 2 * La := by
        have b5 : 1 ≤ N ^ 2 * La := one_le_mul_of_one_le_of_one_le hN21 hLa
        have b6 := mul_le_mul_of_nonneg_left b5 hf0
        linarith
      have b4 : f * (1 + 2 * N ^ 2 * (c6 * La)) = f + 2 * c6 * (f * N ^ 2 * La) := by ring
      rw [b4] at b2
      linarith
    have t5 : 2 * (C4 * f * N ^ 2 * (L + logT + logg)) ≤
        2 * C4 * (1 + C7 + C8) * (f * m ^ 3 * N ^ 2 * L) := by
      have b0 : (1 + C7 + C8) * (m * L) = m * L + C7 * m * L + C8 * (m * L) := by ring
      have b1 : L + logT + logg ≤ (1 + C7 + C8) * (m * L) := by rw [b0]; linarith
      have b3 : (1 + C7 + C8) * (m * L) ≤ (1 + C7 + C8) * (m ^ 3 * L) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm3 hL) (by linarith)
      have b2 : 0 ≤ C4 * f * N ^ 2 := by positivity
      have b4 := mul_le_mul_of_nonneg_left (le_trans b1 b3) b2
      have b5 : C4 * f * N ^ 2 * ((1 + C7 + C8) * (m ^ 3 * L)) =
          C4 * (1 + C7 + C8) * (f * m ^ 3 * N ^ 2 * L) := by ring
      rw [b5] at b4
      linarith
    have hU : 0 ≤ f * N ^ 2 * La := mul_nonneg hfN hLa0
    have hW : 0 ≤ f * m ^ 3 * N ^ 2 * L := by positivity
    have k1 : 0 ≤ 2 * C2 * (C7 + C8) := by positivity
    have k2 : 0 ≤ 2 * C4 * (1 + C7 + C8) := by positivity
    have u1 : (C3 + c5 + 2 * c6 + 1) * (f * N ^ 2 * La) ≤ C0 * (f * N ^ 2 * La) :=
      mul_le_mul_of_nonneg_right (by linarith) hU
    have u3 : (2 * C2 * (C7 + C8) + 2 * C4 * (1 + C7 + C8)) * (f * m ^ 3 * N ^ 2 * L) ≤
        C0 * (f * m ^ 3 * N ^ 2 * L) := mul_le_mul_of_nonneg_right (by linarith) hW
    have hfin : F * g0 j * (C3 * L) + X ≤ C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L) := by
      have e0 : C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L) =
          C0 * (f * N ^ 2 * La) + C0 * (f * m ^ 3 * N ^ 2 * L) := by ring
      rw [hX, e0]; linarith
    show hK j ≤ (∑ ρ, ((∑ i, ph (ν j ρ i)) - (∑ i, ν j ρ i) * logOm)) +
      C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)
    rw [hmean j, div_le_iff₀ hE]
    have hfinE := mul_le_mul_of_nonneg_left hfin hE.le
    linarith

  refine ⟨main, fun _ => C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L), ?_, fun j => le_rfl⟩
  intro j
  have := main j
  unfold sizeB at this
  exact this

/- English proof (translation)
Introduce `J Pl Emb _ _ _ _ r ν g0 logK MainNotions logOmτ logth0 logh logh' logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 h32 hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0`. Take `⟨d1, -⟩` from `first_descent_explicit J Pl Emb r ν g0 (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v) MainNotions logOmτ logth0 logh logh' (fun j => (∑ s, liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s) / (Fintype.card Emb : ℝ)) logOm v f m N L La logT logg C2 C …`. Establish `hE : (0 : ℝ) < (Fintype.card Emb : ℝ)` using `Nat.cast_pos.mpr Fintype.card_pos`. Use `⟨fun j => sizeB ν logOm f m N L La C0 j - (∑ s, liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s) / (Fintype.card Emb : ℝ), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j`.

Establish `e1` using `d1 j`. Simplify using `only at e1 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `j s`. Establish `e1` using `d1 j`.

Establish `e3` using `h32 j s`. Simplify using `only at e1 e3 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `j`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div, mul_div_cancel_left₀ _ hE.ne']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem per_embedding_explicit : PerEmbedding6 := by
  intro J Pl Emb _ _ _ _ r ν g0 logK MainNotions logOmτ logth0 logh logh' logOm v f m N L La logT logg
    C2 C3 C4 c5 c6 C7 C8 C0 h32 hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  obtain ⟨d1, -⟩ := first_descent_explicit J Pl Emb r ν g0 (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v) MainNotions logOmτ
    logth0 logh logh'
    (fun j => (∑ s, liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s) / (Fintype.card Emb : ℝ))
    logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 (fun j s => le_refl _) (fun j => rfl)
    hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  have hE : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨fun j => sizeB ν logOm f m N L La C0 j -
      (∑ s, liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s) / (Fintype.card Emb : ℝ), ?_, ?_, ?_⟩
  · intro j
    have e1 := d1 j
    simp only at e1 ⊢
    linarith
  · intro j s
    have e1 := d1 j
    have e3 := h32 j s
    simp only at e1 e3 ⊢
    linarith
  · intro j
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, add_div,
      mul_div_cancel_left₀ _ hE.ne']
    ring

/- English proof (translation)
Introduce `J Pl Emb Frm _ _ _ _ _ _ r ν g0 logB logP logK MainNotions loglam logOmτ logth0 logh logh' hlam hP logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 hC1 hPs h32 hlm hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0`. Take `⟨cst, c0, c1, c2⟩` from `per_embedding_explicit J Pl Emb r ν g0 logK MainNotions logOmτ logth0 logh logh' logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 h32 hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0`. Establish `hE : (0 : ℝ) < (Fintype.card Emb : ℝ)` using `Nat.cast_pos.mpr Fintype.card_pos`. Establish `hpt : ∀ s, logB s ≤ hP + ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j)`. Introduce `s`.

Establish `m1 : (∑ j, hlam j) ≤ Finset.univ.inf' Finset.univ_nonempty (fun y : Frm => ∑ j, loglam j y s)`. Use `Finset.le_inf' _ _ (fun y _ => ?_)` and prove the remaining obligations. Conclude with `Finset.sum_le_sum (fun j _ => hlm j y s)`. Establish `m2 : (∑ j, logK j s) ≤ ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j)` using `Finset.sum_le_sum (fun j _ => c1 j s)`. Establish `m3` using `hC1 s`.

Establish `m4` using `hPs s`. Rewrite using `[Finset.sum_sub_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hmean : (∑ s, (hP + ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j))) / (Fintype.card Emb : ℝ) = hP + ∑ j, (sizeB ν logOm f m N L La C0 j - hlam j)`. Establish `c2' : ∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j)) = sizeB ν logOm f m N L La C0 j * (Fintype.card Emb : ℝ)` using `fun j => (div_eq_iff hE.ne').mp (c2 j)`.

Rewrite using `[div_eq_iff hE.ne', Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm]`. Establish `: ∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j)) = (sizeB ν logOm f m N L La C0 j - hlam j) * (Fintype.card Emb : ℝ)`. Introduce `j`. Rewrite using `[Finset.sum_sub_distrib, c2' j, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨cst, c0, c2, hpt, hmean, ?_⟩` and prove the remaining obligations. Rewrite using `[← hmean]`. Conclude with `div_le_div_of_nonneg_right (Finset.sum_le_sum (fun s _ => hpt s)) hE.le`.
-/
theorem heightBound6_statement : HeightBound6 := by
  intro J Pl Emb Frm _ _ _ _ _ _ r ν g0 logB logP logK MainNotions loglam logOmτ logth0 logh logh' hlam
    hP logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 hC1 hPs h32 hlm hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  obtain ⟨cst, c0, c1, c2⟩ := per_embedding_explicit J Pl Emb r ν g0 logK MainNotions logOmτ logth0 logh logh'
    logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 h32 hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  have hE : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hpt : ∀ s, logB s ≤
      hP + ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j) := by
    intro s
    have m1 : (∑ j, hlam j) ≤
        Finset.univ.inf' Finset.univ_nonempty (fun y : Frm => ∑ j, loglam j y s) := by
      refine Finset.le_inf' _ _ (fun y _ => ?_)
      exact Finset.sum_le_sum (fun j _ => hlm j y s)
    have m2 : (∑ j, logK j s) ≤
        ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j) :=
      Finset.sum_le_sum (fun j _ => c1 j s)
    have m3 := hC1 s
    have m4 := hPs s
    rw [Finset.sum_sub_distrib]
    linarith
  have hmean : (∑ s, (hP + ∑ j, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j))) /
      (Fintype.card Emb : ℝ) = hP + ∑ j, (sizeB ν logOm f m N L La C0 j - hlam j) := by
    have c2' : ∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j)) =
        sizeB ν logOm f m N L La C0 j * (Fintype.card Emb : ℝ) :=
      fun j => (div_eq_iff hE.ne').mp (c2 j)
    rw [div_eq_iff hE.ne', Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Finset.sum_comm]
    have : ∀ j, (∑ s, (liftedMapLogSize ν g0 MainNotions logOmτ logth0 logh logh' v j s + cst j - hlam j)) =
        (sizeB ν logOm f m N L La C0 j - hlam j) * (Fintype.card Emb : ℝ) := by
      intro j
      rw [Finset.sum_sub_distrib, c2' j, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.sum_mul]
    ring
  refine ⟨cst, c0, c2, hpt, hmean, ?_⟩
  rw [← hmean]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun s _ => hpt s)) hE.le

/- English proof (translation)
Introduce `J Pl _ _ TT _ r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' lam0 C0 Lpass Eb e6 eP logOm pq w eE δ`. Introduce `q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC y1 y2 y3 y4 y5 y6`. Use `Formalism.DivisionValues.divisor_inequality J Pl TT muC mu0 Fo hu hP mlam logT (fun j => sizeB ν logOm f m N L La C0 j) aT (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i) fa x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' 1 lam0 C0 Lpass Eb e6 eP logOm (fun _ => C0 * (f …` and prove the remaining obligations. Introduce `j`. Apply `mul_le_mul_of_nonneg_left _ hC` to reduce the goal to its premises.

Establish `: 0 ≤ f * N ^ 2` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem division_inequality_explicit : DivIneqExplicit6 := by
  intro J Pl _ _ TT _ r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc xe m f k N S tt η
    w'' b' lam0 C0 Lpass Eb e6 eP logOm pq w eE δ
  intro q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21
    z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC y1 y2 y3 y4 y5 y6
  refine Formalism.DivisionValues.divisor_inequality J Pl TT muC mu0 Fo hu hP mlam logT
    (fun j => sizeB ν logOm f m N L La C0 j) aT
    (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i) fa
    x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' 1 lam0 C0 Lpass Eb e6 eP logOm
    (fun _ => C0 * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) pq w eE δ
    q1 q2 q3 (fun j => le_refl _) q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18
    z19 z20 z21 le_rfl z23 z24 z25 z26 (by simpa using z27) z28 z29 z30 z31 z32 z33 z34 z35 hC y1 y2 ?_ y3 y4 y5 y6
  intro j
  apply mul_le_mul_of_nonneg_left _ hC
  have : 0 ≤ f * N ^ 2 := by positivity
  nlinarith

/- English proof (translation)
Introduce `J Pl _ _ TT _ r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 c Lpass Eb e6 eP logOm pq w eE δ`. Introduce `q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z13 z14 z15 z16 z17 z18 z19 z20 z21 z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC1 hCc y1 y2 y3 y4 y5 y6`. Establish `hC0 : 0 < C0` using `by linarith`. Establish `hxe : 0 ≤ x ^ eps` using `Real.rpow_nonneg (by linarith) _`. Establish `hr : 1 ≤ c / C0` using `(one_le_div hC0).mpr hCc`.

Establish `hb : 0 ≤ b` using `by rw [z4]; exact (Real.exp_pos _).le`. Establish `hB0 : 0 ≤ B0` using `by rw [z10]; positivity`. Establish `key` using `division_inequality_explicit J Pl TT r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc (c / C0 * x ^ eps) m f k N S tt η w'' b' lam0 C0 Lpass Eb e6 eP logOm pq w eE δ q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 (le_mul_of_one_le_left hxe hr) z13 z14 z15 z16 …`. Establish `: C0 * m * (c / C0 * x ^ eps) * (B0 + Nc) = c * m * x ^ eps * (B0 + Nc)`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[this]`. Conclude with `y2) y3 y4 y5 y6`. Establish `hY : 0 ≤ m * (B0 + Nc) * x ^ eps` using `by positivity`. Establish `h1 : (50 * C0 + 10) * (m * (B0 + Nc) * (c / C0 * x ^ eps)) = (50 * c + 10 * (c / C0)) * (m * (B0 + Nc) * x ^ eps)`. Clear the denominators using the available nonvanishing facts.

Establish `h2 : c / C0 ≤ c` using `div_le_self (by linarith) hC1`. Establish `h3 : (50 * c + 10 * (c / C0)) * (m * (B0 + Nc) * x ^ eps) ≤ 60 * c * (m * (B0 + Nc) * x ^ eps)` using `mul_le_mul_of_nonneg_right (by linarith) hY`. Establish `h4 : (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * (c / C0 * x ^ eps)) = (50 * C0 + 10) * ((TT.card : ℝ) * a * La) + (50 * C0 + 10) * (m * (B0 + Nc) * (c / C0 * x ^ eps))` using `by ring`. Rewrite `key` using `[h4, h1]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem division_inequality_two_constants : DivIneqTwoConst6 := by
  intro J Pl _ _ TT _ r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc m f k N S tt η
    w'' b' lam0 C0 c Lpass Eb e6 eP logOm pq w eE δ
  intro q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z13 z14 z15 z16 z17 z18 z19 z20 z21
    z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC1 hCc y1 y2 y3 y4 y5 y6
  have hC0 : 0 < C0 := by linarith
  have hxe : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
  have hr : 1 ≤ c / C0 := (one_le_div hC0).mpr hCc
  have hb : 0 ≤ b := by rw [z4]; exact (Real.exp_pos _).le
  have hB0 : 0 ≤ B0 := by rw [z10]; positivity
  have key := division_inequality_explicit J Pl TT r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc
    (c / C0 * x ^ eps) m f k N S tt η w'' b' lam0 C0 Lpass Eb e6 eP logOm pq w eE δ
    q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 (le_mul_of_one_le_left hxe hr)
    z13 z14 z15 z16 z17 z18 z19 z20 z21
    z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC0.le y1
    (by
      have : C0 * m * (c / C0 * x ^ eps) * (B0 + Nc) = c * m * x ^ eps * (B0 + Nc) := by
        field_simp
      rw [this]; exact y2) y3 y4 y5 y6
  have hY : 0 ≤ m * (B0 + Nc) * x ^ eps := by positivity
  have h1 : (50 * C0 + 10) * (m * (B0 + Nc) * (c / C0 * x ^ eps)) =
      (50 * c + 10 * (c / C0)) * (m * (B0 + Nc) * x ^ eps) := by
    field_simp
  have h2 : c / C0 ≤ c := div_le_self (by linarith) hC1
  have h3 : (50 * c + 10 * (c / C0)) * (m * (B0 + Nc) * x ^ eps) ≤
      60 * c * (m * (B0 + Nc) * x ^ eps) := mul_le_mul_of_nonneg_right (by linarith) hY
  have h4 : (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * (c / C0 * x ^ eps)) =
      (50 * C0 + 10) * ((TT.card : ℝ) * a * La) +
        (50 * C0 + 10) * (m * (B0 + Nc) * (c / C0 * x ^ eps)) := by ring
  rw [h4, h1] at key
  linarith

/- English proof (translation)
Introduce `J Pl Emb _ _ _ _ r ν n g0 Ksq kc Om th0sq hcl hcl' hK logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 hn hK0 hkc hOm0 hth0 hh0 hh0' hv hprod hmean hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0`. Use `first_descent_explicit J Pl Emb r ν (fun j => (g0 j : ℝ)) (fun j s => Real.log (Ksq j s)) (fun j s => Real.log (kc j s)) (fun τ s => Real.log (Om τ s)) (fun s => Real.log (th0sq s)) (fun j => Real.log (hcl j)) (fun j => Real.log (hcl' j)) hK logOm v f m N L La logT logg C2 C3 C4 …` and prove the remaining obligations. Introduce `j s`. Establish `hM : (0 : ℝ) < 8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v` using `by positivity`. Use `size_at_embedding Pl r (g0 j) (ν j) (n j) (fun τ => Om τ s) (Ksq j s) (kc j s) ((8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j)) (th0sq s ^ (Fintype.card Pl * g0 j)) (hcl j * hcl' j) (hK0 j s) (hkc j s) (pow_pos hM _) (pow_pos (hth0 s) _) (mul_pos (hh …` as an intermediate fact.

Rewrite `this` using `[Real.log_pow, Real.log_pow, Real.log_mul (hh0 j).ne' (hh0' j).ne']`. Unfold `liftedMapLogSize`. Simplify using `only [hn]`. Move the coercions through the operations in `at this ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `j`. Use `h5 j` as an intermediate fact. Move the coercions through the operations in `at this ⊢`. Conclude with `this`. Introduce `j τ`.

Rewrite using `[hn]`. Conclude with `h6 j τ`.
-/
theorem first_descent_product_explicit : StepDiProd6 := by
  intro J Pl Emb _ _ _ _ r ν n g0 Ksq kc Om th0sq hcl hcl' hK logOm v f m N L La logT logg
    C2 C3 C4 c5 c6 C7 C8 C0 hn hK0 hkc hOm0 hth0 hh0 hh0' hv hprod hmean hOm hSK hth hh hh' hcard hg0
    hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  refine first_descent_explicit J Pl Emb r ν (fun j => (g0 j : ℝ)) (fun j s => Real.log (Ksq j s))
    (fun j s => Real.log (kc j s)) (fun τ s => Real.log (Om τ s)) (fun s => Real.log (th0sq s))
    (fun j => Real.log (hcl j)) (fun j => Real.log (hcl' j)) hK logOm v f m N L La logT logg
    C2 C3 C4 c5 c6 C7 C8 C0 ?_ hmean hOm hSK hth hh hh' hcard
    (fun j => ⟨Nat.cast_nonneg _, hg0 j⟩) hm hN hL hLLa hLa ?_ ?_ hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  · intro j s
    have hM : (0 : ℝ) < 8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v := by positivity
    have := size_at_embedding Pl r (g0 j) (ν j) (n j) (fun τ => Om τ s) (Ksq j s) (kc j s)
      ((8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j))
      (th0sq s ^ (Fintype.card Pl * g0 j)) (hcl j * hcl' j) (hK0 j s) (hkc j s) (pow_pos hM _)
      (pow_pos (hth0 s) _) (mul_pos (hh0 j) (hh0' j)) (fun τ => hOm0 τ s) (hprod j s)
    rw [Real.log_pow, Real.log_pow, Real.log_mul (hh0 j).ne' (hh0' j).ne'] at this
    unfold liftedMapLogSize
    simp only [hn]
    push_cast at this ⊢
    linarith
  · intro j
    have := h5 j
    push_cast at this ⊢
    exact this
  · intro j τ
    rw [hn]; exact h6 j τ

/- English proof (translation)
Introduce `J Pl Emb _ _ _ _ ι Cl Cl' _ _ _ _ _ A B _ _ _ _ _ r ν n s Th c Rc lam Om S kc th0sq γ γ' ε hK logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hS hK0 hkc hth0 hv hmean hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5' h6' hT hg …`. Conclude with `(first_descent_product_explicit J Pl Emb r ν n (fun j => Fintype.card (ι j)) (fun j σ => liftNormSq (γ j) (γ' j) (ε j σ) (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ))) kc Om th0sq (fun j => (Fintype.card (Cl j) : ℝ)) (fun j => (Fintype.card (Cl' j) : ℝ)) hK log …`.
-/
theorem lift_first_descent : LiftStepDi6 := by
  intro J Pl Emb _ _ _ _ ι Cl Cl' _ _ _ _ _ A B _ _ _ _ _ r ν n s Th c Rc lam Om S kc th0sq γ γ' ε hK
    logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0
    h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hS hK0 hkc hth0 hv hmean hOm hSK hth hh hh' hcard hg0
    hm hN hL hLLa hLa h5' h6' hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  exact (first_descent_product_explicit J Pl Emb r ν n (fun j => Fintype.card (ι j))
    (fun j σ => liftNormSq (γ j) (γ' j) (ε j σ)
      (fun L L' => liftBlock (c j σ L L') (Rc j σ) (fun τ => lam τ σ)))
    kc Om th0sq (fun j => (Fintype.card (Cl j) : ℝ)) (fun j => (Fintype.card (Cl' j) : ℝ)) hK
    logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C0 h2 hK0 hkc h10 hth0
    (fun j => Nat.cast_pos.mpr Fintype.card_pos) (fun j => Nat.cast_pos.mpr Fintype.card_pos) hv
    (fun j σ => liftProduct Pl (ι j) (Cl j) (Cl' j) (A j σ) (B j σ) r (ν j) (n j) (s j σ) (Th j σ) (c j σ)
      (Rc j σ) (fun τ => lam τ σ) (fun τ => Om τ σ) (S j σ) (γ j) (γ' j) (ε j σ) (kc j σ) v (th0sq σ)
      (h1 j) (h2 j) (h3 j σ) (h4 j σ) (h5 j σ) (h6 j σ) (h7 j σ) (h8 j σ) (h9 j σ)
      (fun τ => h10 τ σ) (fun τ => h11 τ σ) (h12 j) (h13 j) (h14 j σ) (hS j σ))
    hmean hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5' h6' hT hg p2 p3 p4 p5 p6 p7 p8 hC0).1

/- English proof (translation)
Introduce `k m j p q' h1 h2 hp hq`. Substitute `hp hq` using the available equality. Use `⟨⟨by ring, abs_le.mpr ⟨by linarith, by linarith⟩⟩, ⟨by ring, abs_le.mpr ⟨by linarith, by linarith⟩⟩⟩` and prove the remaining obligations.
-/
theorem top_net : TopNet6 := by
  intro k m j p q' h1 h2 hp hq
  subst hp hq
  refine ⟨⟨by ring, abs_le.mpr ⟨by linarith, by linarith⟩⟩,
    ⟨by ring, abs_le.mpr ⟨by linarith, by linarith⟩⟩⟩

/- English proof (translation)
Introduce `p q' logOm lrdK lrdE dfl c1 hq hK hKE hd hc`. Establish `e2 : c1 + (p - q') * logOm / 2 = -(q' * (2 * lrdK - lrdE))` using `by rw [hc, hd]; ring`. Establish `e3 : |2 * lrdK - lrdE| ≤ lrdE` using `abs_le.mpr ⟨by linarith, by linarith⟩`. Use `⟨by rw [hd]; ring, e2, e3, ?_⟩` and prove the remaining obligations. Rewrite using `[e2, abs_neg, abs_mul, abs_of_nonneg hq]`.

Conclude with `mul_le_mul_of_nonneg_left e3 hq`.
-/
theorem flat_line_degree : FlatLineDegree6 := by
  intro p q' logOm lrdK lrdE dfl c1 hq hK hKE hd hc
  have e2 : c1 + (p - q') * logOm / 2 = -(q' * (2 * lrdK - lrdE)) := by rw [hc, hd]; ring
  have e3 : |2 * lrdK - lrdE| ≤ lrdE := abs_le.mpr ⟨by linarith, by linarith⟩
  refine ⟨by rw [hd]; ring, e2, e3, ?_⟩
  rw [e2, abs_neg, abs_mul, abs_of_nonneg hq]
  exact mul_le_mul_of_nonneg_left e3 hq

/- English proof (translation)
Introduce `Emb _ _ φ C0 M hφ hM`. Establish `hE : (0 : ℝ) < (Fintype.card Emb : ℝ)` using `Nat.cast_pos.mpr Fintype.card_pos`. Establish `hS : (∑ s, φ s) = M * (Fintype.card Emb : ℝ)` using `by rw [hM]; field_simp`. Establish `hM0 : 0 ≤ M + C0`. Establish `: (∑ _s : Emb, (-C0)) ≤ ∑ s, φ s` using `Finset.sum_le_sum (fun s _ => hφ s)`.

Rewrite `this` using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hS]`. Assume the negation of the conclusion as `hneg`. Rewrite `hneg` using `[not_le]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hpt : ∀ s, |φ s - M| ≤ (φ s + C0) + (M + C0)`.

Introduce `s`. Use `hφ s` as an intermediate fact. Conclude with `abs_le.mpr ⟨by linarith, by linarith⟩`. Rewrite using `[div_le_iff₀ hE]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, hS, Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mean_deviation : MeanDev6 := by
  intro Emb _ _ φ C0 M hφ hM
  have hE : (0 : ℝ) < (Fintype.card Emb : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hS : (∑ s, φ s) = M * (Fintype.card Emb : ℝ) := by rw [hM]; field_simp
  have hM0 : 0 ≤ M + C0 := by
    have : (∑ _s : Emb, (-C0)) ≤ ∑ s, φ s := Finset.sum_le_sum (fun s _ => hφ s)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hS] at this
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
  have hpt : ∀ s, |φ s - M| ≤ (φ s + C0) + (M + C0) := by
    intro s
    have := hφ s
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [div_le_iff₀ hE]
  calc (∑ s, |φ s - M|) ≤ ∑ s, ((φ s + C0) + (M + C0)) := Finset.sum_le_sum (fun s _ => hpt s)
    _ = 2 * (M + C0) * (Fintype.card Emb : ℝ) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hS, Finset.sum_const, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
        ring

/- English proof (translation)
Introduce `J Pl Emb Frm _ _ _ _ _ _ TT r ν g0 logB logP logK MainNotions loglam logOmτ logth0 logh logh' aT logH logOm v f m N S η b' nV L La L' logT logg C2 C3 C4 c5 c6 C7 C8 C hC1 hPs h32 hlm hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0`. Take `⟨cst, -, -, k1, k2, k3⟩` from `heightBound6_statement J Pl Emb Frm r ν g0 logB logP logK MainNotions loglam logOmτ logth0 logh logh' (recordX logH f nV L' C) (recordA TT aT logT f m N S η b' La C) logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C hC1 hPs h32 hlm hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa …`. Establish `e : recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C = recordA TT aT logT f m N S η b' La C + ∑ j, (sizeB ν logOm f m N L La C j - recordX logH f nV L' C j)`. Unfold `recordHu`. Rewrite using `[Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `⟨_, k1, k2, k3⟩`.
-/
theorem height_bound_complete : HeightRecord6 := by
  intro J Pl Emb Frm _ _ _ _ _ _ TT r ν g0 logB logP logK MainNotions loglam logOmτ logth0 logh logh' aT logH
    logOm v f m N S η b' nV L La L' logT logg C2 C3 C4 c5 c6 C7 C8 C hC1 hPs h32 hlm hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  obtain ⟨cst, -, -, k1, k2, k3⟩ := heightBound6_statement J Pl Emb Frm r ν g0 logB logP logK MainNotions loglam logOmτ
    logth0 logh logh' (recordX logH f nV L' C) (recordA TT aT logT f m N S η b' La C)
    logOm v f m N L La logT logg C2 C3 C4 c5 c6 C7 C8 C hC1 hPs h32 hlm hOm hSK hth hh hh' hcard hg0 hm hN hL hLLa hLa h5 h6 hT hg p2 p3 p4 p5 p6 p7 p8 hC0
  have e : recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C =
      recordA TT aT logT f m N S η b' La C +
        ∑ j, (sizeB ν logOm f m N L La C j - recordX logH f nV L' C j) := by
    unfold recordHu
    rw [Finset.sum_sub_distrib]
    ring
  rw [e]
  exact ⟨_, k1, k2, k3⟩

/- English proof (translation)
Introduce `J Pl _ _ TT _ r ν muC mu0 Fo logT aT logH x eps L b a rd La L' B0 Nc xe m f k N nV S tt η w'' b' lam0 C C0 Lpass Eb logOm pq w eE δ q1 q2 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 zb z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC hCC …`. Establish `hx0 : 0 < x` using `by linarith`. Establish `hL0 : 0 ≤ L` using `by rw [z3]; exact Real.rpow_nonneg hx0.le _`. Establish `hLa0 : 0 ≤ La`. Rewrite using `[z9, z5, z4, Real.log_mul (by positivity) (by linarith), Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]`.

Use `Real.log_nonneg z1` as an intermediate fact. Use `Real.log_nonneg z6` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hC0 : 0 ≤ C0` using `le_trans hC hCC`. Establish `hfN : 0 ≤ f * N ^ 2` using `by positivity`.

Use `Formalism.DivisionValues.divisor_inequality J Pl TT muC mu0 Fo (recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C) (recordA TT aT logT f m N S η b' La C) (∑ j, recordX logH f nV L' C j) logT (fun j => sizeB ν logOm f m N L La C j) aT (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j …` and prove the remaining obligations. Unfold `recordX`. Rewrite using `[Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, z13]`. Introduce `j`. Establish `a1 : 0 ≤ f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L` using `by positivity`.

Establish `a2 : f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L ≤ f * N ^ 2 * (La + 1) + f * m ^ 3 * N ^ 2 * L` using `by nlinarith`. Conclude with `mul_le_mul hCC a2 a1 hC0`. Establish `a1 : nV ^ 2 ≤ N ^ 2` using `pow_le_pow_left₀ hnV hnVN 2`. Establish `a2 : f * nV ^ 2 ≤ f * N ^ 2` using `mul_le_mul_of_nonneg_left a1 (by linarith)`. Establish `a3 : f * nV ^ 2 * (C * L') ≤ f * N ^ 2 * (C0 * La)` using `mul_le_mul a2 hCL (mul_nonneg hC hL') hfN`.

Establish `a4` using `mul_le_mul_of_nonneg_left a3 (by linarith : (0 : ℝ) ≤ m)`. Combine the equalities or inequalities in the displayed calculation. Establish `a1 : 0 ≤ ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2)` using `by positivity`. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC a1) hLa0`.
-/
theorem division_inequality_complete : DivIneqRecord6 := by
  intro J Pl _ _ TT _ r ν muC mu0 Fo logT aT logH x eps L b a rd La L' B0 Nc xe m f k N nV S tt η
    w'' b' lam0 C C0 Lpass Eb logOm pq w eE δ q1 q2 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13
    z14 z15 z16 z17 z18 z19 z20 z21 zb z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35
    hC hCC hnV hnVN hL' hCL y1 y2 y5 y6
  have hx0 : 0 < x := by linarith
  have hL0 : 0 ≤ L := by rw [z3]; exact Real.rpow_nonneg hx0.le _
  have hLa0 : 0 ≤ La := by
    rw [z9, z5, z4, Real.log_mul (by positivity) (by linarith),
      Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
    have := Real.log_nonneg z1
    have := Real.log_nonneg z6
    linarith
  have hC0 : 0 ≤ C0 := le_trans hC hCC
  have hfN : 0 ≤ f * N ^ 2 := by positivity
  refine Formalism.DivisionValues.divisor_inequality J Pl TT muC mu0 Fo
    (recordHu TT ν aT logH logT logOm f m N S η b' nV L La L' C)
    (recordA TT aT logT f m N S η b' La C) (∑ j, recordX logH f nV L' C j) logT
    (fun j => sizeB ν logOm f m N L La C j) aT
    (fun j ρ => ∑ i, ph (ν j ρ i)) (fun j ρ => ∑ i, ν j ρ i) logH
    x eps L b a rd La B0 Nc xe m f k N S tt η w'' b' 1 lam0 C0 Lpass Eb (m * (C * f * nV ^ 2 * L'))
    (C * ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) * La) logOm
    (fun _ => C * (f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L)) pq w eE δ
    q1 q2 rfl (fun j => le_refl _) ?_ (le_refl _) q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15
    z16 z17 z18 z19 z20 z21 le_rfl z23 z24 z25 z26 (by simpa using z27) z28 z29 z30 z31 z32 z33 z34 z35
    hC0 y1 y2 ?_ ?_ ?_ y5 y6
  · unfold recordX
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, z13]
  · intro j
    have a1 : 0 ≤ f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L := by positivity
    have a2 : f * N ^ 2 * La + f * m ^ 3 * N ^ 2 * L ≤
        f * N ^ 2 * (La + 1) + f * m ^ 3 * N ^ 2 * L := by nlinarith
    exact mul_le_mul hCC a2 a1 hC0
  · have a1 : nV ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hnV hnVN 2
    have a2 : f * nV ^ 2 ≤ f * N ^ 2 := mul_le_mul_of_nonneg_left a1 (by linarith)
    have a3 : f * nV ^ 2 * (C * L') ≤ f * N ^ 2 * (C0 * La) :=
      mul_le_mul a2 hCL (mul_nonneg hC hL') hfN
    have a4 := mul_le_mul_of_nonneg_left a3 (by linarith : (0 : ℝ) ≤ m)
    calc m * (C * f * nV ^ 2 * L') = m * (f * nV ^ 2 * (C * L')) := by ring
      _ ≤ m * (f * N ^ 2 * (C0 * La)) := a4
      _ = C0 * m * f * N ^ 2 * La := by ring
  · have a1 : 0 ≤ ((TT.card : ℝ) * b' * N + f * (m * η + S) * N + f * N ^ 2) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC a1) hLa0

/- English proof (translation)
Introduce `k m t N S Sc w η hk hm ht hN hS hSc`. Establish `h1 : (k - 1) * S ≤ k * Sc` using `by nlinarith`. Establish `hmt : 0 ≤ m * (t + 1)` using `by positivity`. Establish `h2 : (k - 1) * (N + t + 1) ≤ (N + t) ^ 2`. Establish `a1 : k - 1 ≤ N + t - 1` using `by linarith`.

Establish `a2 : 0 ≤ N + t + 1` using `by linarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right a1 a2]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem weight_size : WeightSize6 := by
  intro k m t N S Sc w η hk hm ht hN hS hSc
  have h1 : (k - 1) * S ≤ k * Sc := by nlinarith
  have hmt : 0 ≤ m * (t + 1) := by positivity
  have h2 : (k - 1) * (N + t + 1) ≤ (N + t) ^ 2 := by
    have a1 : k - 1 ≤ N + t - 1 := by linarith
    have a2 : 0 ≤ N + t + 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right a1 a2]
  nlinarith

/- English proof (translation)
Introduce `J Pl _ _ TT _ r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc m f k N S tt η w'' b' lam0 C0 c Lpass Eb e6 eP logOm pq w eE δ q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z13 z14 z15 z16 z17 z18 z19 z20 z21 z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z3 …`. Establish `hxe : 0 ≤ x ^ eps` using `Real.rpow_nonneg (by linarith) _`. Establish `hb : 0 ≤ b` using `by rw [z4]; exact (Real.exp_pos _).le`. Establish `hB0 : 0 ≤ B0` using `by rw [z10]; positivity`. Establish `key` using `division_inequality_explicit J Pl TT r ν (muC - Eb) (mu0 - Eb) Fo hu hP mlam logT aT fa x eps L b a rd La B0 0 (x ^ eps) m f k N S tt η w'' b' lam0 C0 Lpass 0 e6 eP logOm pq w eE δ (by linarith) (by linarith) q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 le_rfl le_rfl z13 z14 z15 …`.

Establish `h1 : 0 ≤ m * (Real.log x ^ 2 * Nc)` using `by positivity`. Establish `h2 : (50 * C0 + 10) * (m * (B0 + 0) * x ^ eps) ≤ (50 * C0 + 10) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc))`. Apply `mul_le_mul_of_nonneg_left _ (by linarith)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + 0) * x ^ eps) = (50 * C0 + 10) * ((TT.card : ℝ) * a * La) + (50 * C0 + 10) * (m * (B0 + 0) * x ^ eps)` using `by ring`.

Establish `h4 : (50 * C0 + 10 + c) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) = (50 * C0 + 10) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) + c * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc))` using `by ring`. Rewrite `key` using `[h3]`. Rewrite using `[h4]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem division_inequality_fine : DivIneqFine6 := by
  intro J Pl _ _ TT _ r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc m f k N S tt η
    w'' b' lam0 C0 c Lpass Eb e6 eP logOm pq w eE δ q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
    z11 z13 z14 z15 z16 z17 z18 z19 z20 z21 z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC y1 y2
    y3 y4 y5 y6
  have hxe : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
  have hb : 0 ≤ b := by rw [z4]; exact (Real.exp_pos _).le
  have hB0 : 0 ≤ B0 := by rw [z10]; positivity
  have key := division_inequality_explicit J Pl TT r ν (muC - Eb) (mu0 - Eb) Fo hu hP mlam logT aT fa x eps L b a
    rd La B0 0 (x ^ eps) m f k N S tt η w'' b' lam0 C0 Lpass 0 e6 eP logOm pq w eE δ
    (by linarith) (by linarith) q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 le_rfl le_rfl
    z13 z14 z15 z16 z17 z18 z19 z20 z21
    z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC y1 (by positivity) y3 y4 y5 y6
  have h1 : 0 ≤ m * (Real.log x ^ 2 * Nc) := by positivity
  have h2 : (50 * C0 + 10) * (m * (B0 + 0) * x ^ eps) ≤
      (50 * C0 + 10) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have h3 : (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + 0) * x ^ eps) =
      (50 * C0 + 10) * ((TT.card : ℝ) * a * La) + (50 * C0 + 10) * (m * (B0 + 0) * x ^ eps) := by ring
  have h4 : (50 * C0 + 10 + c) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) =
      (50 * C0 + 10) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) +
        c * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) := by ring
  rw [h3] at key
  rw [h4]
  linarith

end Formalism.DimensionVariation
