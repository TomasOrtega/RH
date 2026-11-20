import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.ConcreteSettingExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNodeGapGeRankPow

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.Mem GlobalTheory.Mem.Top

namespace GlobalTheory.Mem.Top.NodeGap

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `D.R.m_add_three_le_k show 1801 ≤ D.R.k + D.R.m - 1`. Use linear arithmetic over natural numbers and integers. Introduce `τ j hj`. Take `⟨b1, hb1⟩` from `hb τ`.

Rewrite using `[hb1 ⟨j.1 + 1, hj⟩, hb1 j]`. Establish `h2 : 16 * D.R.r ^ 19 ≤ h` using `by exact_mod_cast hh`. Establish `h3 : (16 * (D.R.r : ℚ) ^ 19) ≤ (h : ℚ)` using `by exact_mod_cast h2`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gapHyp_of_nodes (D : D7) (hm : 1801 ≤ D.R.m) (h : ℕ) (hh : 16 * (D.R.r : ℝ) ^ 19 ≤ (h : ℝ))
    (hb : ∀ τ, ∃ b1 : ℤ, ∀ j : Fin D.R.m, (D.hc τ).b j = (b1 : ℚ) + (j.1 : ℚ) * (h : ℚ)) :
    Formalism.L2.SG.ConcreteSettingExists.GapHyp D := by
  refine ⟨?_, ?_⟩
  · have h1 := D.R.m_add_three_le_k
    show 1801 ≤ D.R.k + D.R.m - 1
    omega
  · intro τ j hj
    obtain ⟨b1, hb1⟩ := hb τ
    rw [hb1 ⟨j.1 + 1, hj⟩, hb1 j]
    have h2 : 16 * D.R.r ^ 19 ≤ h := by exact_mod_cast hh
    have h3 : (16 * (D.R.r : ℚ) ^ 19) ≤ (h : ℚ) := by exact_mod_cast h2
    push_cast
    linarith

/- English proof (translation)
Unfold `Ev at hp ⊢`. Take `⟨w, hw, H⟩` from `hp`. Use `⟨w, hw, fun eps C8 a b c d => ?_⟩` and prove the remaining obligations. Take `⟨K0, H1⟩` from `H eps C8 a b c d`. Use `⟨K0, fun C e f g => ?_⟩` and prove the remaining obligations.

Take `⟨c1, H2⟩` from `H1 C e f g`. Use `⟨c1, fun cD hc => ?_⟩` and prove the remaining obligations. Take `⟨c2, H3⟩` from `H2 cD hc`. Use `⟨c2, fun ch hch => ?_⟩` and prove the remaining obligations. Take `⟨x0, H4⟩` from `H3 ch hch`.

Conclude with `⟨x0, fun K k1 k2 k3 k4 k5 => h K (H4 K k1 k2 k3 k4 k5)⟩`.
-/
private theorem ev_mono_of_forall_imp {p q : Ctx → Prop} (h : ∀ K, p K → q K) (hp : Ev p) : Ev q := by
  unfold Ev at hp ⊢
  obtain ⟨w, hw, H⟩ := hp
  refine ⟨w, hw, fun eps C8 a b c d => ?_⟩
  obtain ⟨K0, H1⟩ := H eps C8 a b c d
  refine ⟨K0, fun C e f g => ?_⟩
  obtain ⟨c1, H2⟩ := H1 C e f g
  refine ⟨c1, fun cD hc => ?_⟩
  obtain ⟨c2, H3⟩ := H2 cD hc
  refine ⟨c2, fun ch hch => ?_⟩
  obtain ⟨x0, H4⟩ := H3 ch hch
  exact ⟨x0, fun K k1 k2 k3 k4 k5 => h K (H4 K k1 k2 k3 k4 k5)⟩

/- English proof (translation)
Use `ev_mono_of_forall_imp ?_ (ev_nodes 16 19 1801)` and prove the remaining obligations. Introduce `K hK X hX`. Take `⟨hm, h, hh, hb⟩` from `hK X hX`. Conclude with `gapHyp_of_nodes X.toD7 hm h hh fun τ => (hb τ).imp fun b1 hb1 j => (hb1 j).1`.
-/
theorem ev_gapHyp : Ev fun K => ∀ X : Stages, K.Over X.B.toPre → Formalism.L2.SG.ConcreteSettingExists.GapHyp X.toD7 := by
  refine ev_mono_of_forall_imp ?_ (ev_nodes 16 19 1801)
  intro K hK X hX
  obtain ⟨hm, h, hh, hb⟩ := hK X hX
  exact gapHyp_of_nodes X.toD7 hm h hh fun τ => (hb τ).imp fun b1 hb1 j => (hb1 j).1

end GlobalTheory.Mem.Top.NodeGap
