import Formalism.HermitianCurvature.HermitianCurvatureProofs.BuiltBoundsCompactOfParts

namespace Formalism.FourierDecayAlt.P.PBASM

open Formalism.FourierDecayAlt NumberField

noncomputable section

section thr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

/- English proof (translation)
Establish `hB'` using `hB`. Take `⟨-, -, -, -, -, -, -, -, -, -, hGo, hGR, -⟩` from `hB'`. Establish `hcard : 1 ≤ (S.grid1 v).card`. Establish `h1` using `(hGR v).1`. Establish `h20` using `PBD.ntop_ge S`.

Establish `: (1 : ℝ) ≤ S.Ntop` using `by linarith`. Establish `: 1 ≤ S.Ntop` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers. Take `⟨y, hy⟩` from `Finset.card_pos.1 hcard`. Take `⟨-, -, hI1, -, -, hnode⟩` from `hGo v`.

Take `⟨hyI, -, hP0, hP1⟩` from `hnode y (Or.inr hy)`. Establish `hy1` using `(hI1 y hy).1`. Establish `hq : (S.G.place (S.pl v)).q S.de S.de' S.T S.T' y ≠ 0`. Rewrite using `[← PBL.qC_re]`. Use `(PBL.q_pos_cut hB v y ?_).ne'` and prove the remaining obligations.

Rewrite using `[← PBL.cutI_eq]`. Conclude with `hyI`. Establish `hcore : 0 < (S.G.place (S.pl v)).core S.de S.de' S.T S.T' y`. Unfold `Sz.Cfg.core`. Conclude with `Real.sqrt_pos.2 (abs_pos.2 (div_ne_zero (mul_ne_zero hP0 hP1) hq))`.

Use `lt_of_lt_of_le hcore (PBL.core_le_supA hB v one y ?_)` and prove the remaining obligations. Consider the cases of `one`. Simplify using `using hyI`. Simplify using `only [if_true]`. Rewrite using `[← PBL.ntop_eq_N']`.

Conclude with `hy1`.
-/
theorem supA_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (one : Bool) :
    0 < J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v) := by
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGR, -⟩ := hB'
  have hcard : 1 ≤ (S.grid1 v).card := by
    have h1 := (hGR v).1
    have h20 := PBD.ntop_ge S
    have : (1 : ℝ) ≤ S.Ntop := by linarith
    have : 1 ≤ S.Ntop := by exact_mod_cast this
    omega
  obtain ⟨y, hy⟩ := Finset.card_pos.1 hcard
  obtain ⟨-, -, hI1, -, -, hnode⟩ := hGo v
  obtain ⟨hyI, -, hP0, hP1⟩ := hnode y (Or.inr hy)
  have hy1 := (hI1 y hy).1
  have hq : (S.G.place (S.pl v)).q S.de S.de' S.T S.T' y ≠ 0 := by
    rw [← PBL.qC_re]
    refine (PBL.q_pos_cut hB v y ?_).ne'
    rw [← PBL.cutI_eq]; exact hyI
  have hcore : 0 < (S.G.place (S.pl v)).core S.de S.de' S.T S.T' y := by
    unfold Sz.Cfg.core
    exact Real.sqrt_pos.2 (abs_pos.2 (div_ne_zero (mul_ne_zero hP0 hP1) hq))
  refine lt_of_lt_of_le hcore (PBL.core_le_supA hB v one y ?_)
  cases one
  · simpa using hyI
  · simp only [if_true]
    rw [← PBL.ntop_eq_N']
    exact hy1

/- English proof (translation)
Take `⟨hg1, hg2, -⟩` from `hB`. Unfold `Sz.Glob.g`. Conclude with `Nat.mul_pos hg1 hg2` after adjusting the coercions.
-/
theorem glob_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g := by
  obtain ⟨hg1, hg2, -⟩ := hB
  unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩` from `hB`. Take `⟨hlen, -⟩` from `hG ⟨0, hS⟩`. Establish `he : S.cutHi ⟨0, hS⟩ - S.cutLo ⟨0, hS⟩ = S.G.lenI`. Simplify using `only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hlen` using `[he]`. Establish `h20` using `PBD.ntop_ge S`. Establish `h6 : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lenI_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (hS : 0 < S.f) : 0 < S.G.lenI := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hB
  obtain ⟨hlen, -⟩ := hG ⟨0, hS⟩
  have he : S.cutHi ⟨0, hS⟩ - S.cutLo ⟨0, hS⟩ = S.G.lenI := by
    simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring
  rw [he] at hlen
  have h20 := PBD.ntop_ge S
  have h6 : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by positivity
  linarith

/- English proof (translation)
Establish `hg` using `glob_pos' hB`. Establish `hI` using `lenI_pos' hB (Fin.pos v)`. Establish `hA` using `supA_pos hB v (decide (b = 1 ∧ s = 1))`. Establish `hN : (0 : ℝ) < S.G.N` using `by rw [← PBL.ntop_eq_N']; linarith [PBD.ntop_ge S]`. Establish `hB'` using `hB`.

Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCA, -⟩` from `hB'`. Establish `hC' : 0 < S.CA` using `lt_of_lt_of_le hC hCA`. Unfold `J.thrS Sz.lamThreshold`. Establish `hk : 0 < 2 * Real.pi / S.G.g` using `by positivity`. Check the signs of the components of the expression.
-/
theorem thrS_pos (hC : 0 < Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (v : Fin S.f) :
    0 < J.thrS S.G S.CA S.de S.de' S.T S.T' S.l b s (S.pl v) := by
  have hg := glob_pos' hB
  have hI := lenI_pos' hB (Fin.pos v)
  have hA := supA_pos hB v (decide (b = 1 ∧ s = 1))
  have hN : (0 : ℝ) < S.G.N := by rw [← PBL.ntop_eq_N']; linarith [PBD.ntop_ge S]
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCA, -⟩ := hB'
  have hC' : 0 < S.CA := lt_of_lt_of_le hC hCA
  unfold J.thrS Sz.lamThreshold
  have hk : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

end thr

/- English proof (translation)
Introduce `Cb`. Use `⟨1, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB b s v _ _`. Conclude with `thrS_pos one_pos hB b s v`.
-/
theorem thrPos : ThresholdsPositive := by
  intro Cb
  refine ⟨1, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB b s v _ _
  exact thrS_pos one_pos hB b s v

end

end Formalism.FourierDecayAlt.P.PBASM

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
