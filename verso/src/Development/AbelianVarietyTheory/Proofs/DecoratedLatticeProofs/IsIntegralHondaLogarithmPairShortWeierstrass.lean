import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU

open PowerSeries GlobalTheory.Honda

namespace GlobalTheory.Honda

/- English proof (translation)
Use `set W := Formalism.L2.Th1.A.shortW g2 g3 with hW`. Establish `h4 : ‖(4 : K)‖ = 1`. Establish `: (4 : K) = 2 * 2` using `by norm_num`. Rewrite using `[this, norm_mul, h2, one_mul]`. Establish `hmem : ∀ x : K, ‖x‖ ≤ 1 → x ∈ Formalism.G.unitBall K` using `fun x hx => hx`.

Establish `ha4 : W.a₄ ∈ Formalism.G.unitBall K`. Apply `hmem` to reduce the goal to its premises. Use `show ‖-g2 / 4‖ ≤ 1`. Rewrite using `[norm_div, norm_neg, h4, div_one]`. Conclude with `hg2`.

Establish `ha6 : W.a₆ ∈ Formalism.G.unitBall K`. Apply `hmem` to reduce the goal to its premises. Use `show ‖-g3 / 4‖ ≤ 1`. Rewrite using `[norm_div, norm_neg, h4, div_one]`. Conclude with `hg3`.

Establish `h0 : (0 : K) ∈ Formalism.G.unitBall K` using `(Formalism.G.unitBall K).zero_mem`. Establish `hcm` using `Formalism.L2.Th1.A.coeffMem K W (Formalism.G.unitBall K) h0 h0 h0 ha4 ha6`. Take `⟨hl0, hl1, hlom, -⟩` from `Formalism.L2.Th1.A.logSpec K W`. Take `⟨he0, -, hle, hel, -⟩` from `Formalism.L2.Th1.A.expSpec K W`. Take `⟨-, hfgl⟩` from `Formalism.L2.Th1.A.fglLog K W`.

Use `⟨⟨hl0, hl1, he0, hel, hle⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `n`. Rewrite using `[hlom]`. Conclude with `hcm.2.2.2.2.1 n`. Introduce `n`.

Unfold `Formalism.L2.Th1.C.fadd`. Rewrite using `[← hfgl]`. Conclude with `hcm.2.2.2.2.2.2.1 n`.
-/
theorem intLog_shortW (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (g2 g3 : K)
    (h2 : ‖(2 : K)‖ = 1) (hg2 : ‖g2‖ ≤ 1) (hg3 : ‖g3‖ ≤ 1) :
    IntLog (Formalism.L2.Th1.A.logSer (Formalism.L2.Th1.A.shortW g2 g3))
      (Formalism.L2.Th1.A.expSer (Formalism.L2.Th1.A.shortW g2 g3)) := by
  set W := Formalism.L2.Th1.A.shortW g2 g3 with hW
  have h4 : ‖(4 : K)‖ = 1 := by
    have : (4 : K) = 2 * 2 := by norm_num
    rw [this, norm_mul, h2, one_mul]
  have hmem : ∀ x : K, ‖x‖ ≤ 1 → x ∈ Formalism.G.unitBall K := fun x hx => hx
  have ha4 : W.a₄ ∈ Formalism.G.unitBall K := by
    apply hmem
    show ‖-g2 / 4‖ ≤ 1
    rw [norm_div, norm_neg, h4, div_one]; exact hg2
  have ha6 : W.a₆ ∈ Formalism.G.unitBall K := by
    apply hmem
    show ‖-g3 / 4‖ ≤ 1
    rw [norm_div, norm_neg, h4, div_one]; exact hg3
  have h0 : (0 : K) ∈ Formalism.G.unitBall K := (Formalism.G.unitBall K).zero_mem
  have hcm := Formalism.L2.Th1.A.coeffMem K W (Formalism.G.unitBall K) h0 h0 h0 ha4 ha6
  obtain ⟨hl0, hl1, hlom, -⟩ := Formalism.L2.Th1.A.logSpec K W
  obtain ⟨he0, -, hle, hel, -⟩ := Formalism.L2.Th1.A.expSpec K W
  obtain ⟨-, hfgl⟩ := Formalism.L2.Th1.A.fglLog K W
  refine ⟨⟨hl0, hl1, he0, hel, hle⟩, ?_, ?_⟩
  · intro n
    rw [hlom]
    exact hcm.2.2.2.2.1 n
  · intro n
    unfold Formalism.L2.Th1.C.fadd
    rw [← hfgl]
    exact hcm.2.2.2.2.2.2.1 n

end GlobalTheory.Honda
