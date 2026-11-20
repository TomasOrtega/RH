import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SpanInst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsVanishingOffFramesLeSpanShortThetaStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitCOfFiniteCharacter
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.Dict

/- English proof (translation)
Take `⟨-, -, -, h4⟩` from `h`. Take `⟨hp, hq, -⟩` from `h4 j hj`. Rewrite using `[hp, hq]`. Take `⟨h1, h2⟩` from `hj`. Simplify using `only [Formalism.BasicNotions.Ranks.sigW, Formalism.BasicNotions.Ranks.r]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem sig_add_of_pins {D : D7} (Q : Par D) (h : Q.Pins) {j : ℕ} (hj : InR D j) :
    (Q.Dw j).p + (Q.Dw j).q = D.R.r := by
  obtain ⟨-, -, -, h4⟩ := h
  obtain ⟨hp, hq, -⟩ := h4 j hj
  rw [hp, hq]
  obtain ⟨h1, h2⟩ := hj
  simp only [Formalism.BasicNotions.Ranks.sigW, Formalism.BasicNotions.Ranks.r]
  omega

/- English proof (translation)
Unfold `Dom wtA`. Use `⟨fun τ => ?_, ka.n_even⟩` and prove the remaining obligations. Introduce `a b hab`. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `t _`.

Apply `add_le_add` to reduce the goal to its premises. Use `split_ifs with h`. Apply the tactic sequence `unfold Formalism.L2.Pj.ext0 split_ifs with h1 h2 <;> first | omega | exact Nat.zero_le _ | exact le_refl _ | exact ka.aPlus_antitone t (Fin.mk_le_mk.2 hab)`. Conclude with `le_refl _`. Use `split_ifs with h`.

Apply the tactic sequence `unfold Formalism.L2.Pj.ext0 split_ifs with h1 h2 <;> first | omega | exact Nat.zero_le _ | exact le_refl _ | exact ka.aM_anti t (Fin.mk_le_mk.2 hab)`. Conclude with `le_refl _`.
-/
private theorem dom_wtA_of_wt {D : D7} {j : ℕ} (ka : WeightFamilies.Wt D j) : Dom (wtA ka) ka.n := by
  unfold Dom wtA
  refine ⟨fun τ => ?_, ka.n_even⟩
  intro a b hab
  apply Finset.sum_le_sum
  intro t _
  apply add_le_add
  · split_ifs with h
    · unfold Formalism.L2.Pj.ext0
      split_ifs with h1 h2 <;> first | omega | exact Nat.zero_le _ | exact le_refl _ | exact ka.aPlus_antitone t (Fin.mk_le_mk.2 hab)
    · exact le_refl _
  · split_ifs with h
    · unfold Formalism.L2.Pj.ext0
      split_ifs with h1 h2 <;> first | omega | exact Nat.zero_le _ | exact le_refl _ | exact ka.aM_anti t (Fin.mk_le_mk.2 hab)
    · exact le_refl _

/- English proof (translation)
Take `⟨-, hL, -⟩` from `h`. Unfold `Par.PinLevel at hL`. Conclude with `hL.2`.
-/
private theorem par_l_A_eq_one_of_pins {D : D7} (Q : Par D) (h : Q.Pins) : Q.l.A = 1 := by
  obtain ⟨-, hL, -⟩ := h
  unfold Par.PinLevel at hL
  exact hL.2

/- English proof (translation)
Introduce `hC D T hM hSh hG hb hX j hj ka hn`. Take `⟨-, dLev, dNab, dPd, dPhi, dRoot, shTot, -, -⟩` from `hSh`. Establish `hgood : GoodEmb T.Q.c T.σ₀` using `T.toCore.good_σ₀`. Establish `hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r` using `sig_add_of_pins T.Q hM.pins hj`. Establish `hr1 : 1 ≤ D.R.r`.

Use `D.R.m_add_three_le_k` as an intermediate fact. Simplify using `only [Formalism.BasicNotions.Ranks.r]`. Use linear arithmetic over natural numbers and integers. Establish `hDom : Dom (wtA ka) ka.n` using `dom_wtA_of_wt ka`. Establish `hl : T.Q.l.A = 1` using `par_l_A_eq_one_of_pins T.Q hM.pins`.

Establish `hn' : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ ka.n`. Rewrite using `[hostSize_finrank D]`. Combine the equalities or inequalities in the displayed calculation. Establish `hP3 : ¬ 3 ∣ (T.dδ j ka.n).pd`. Take `⟨p, hp, hpd⟩` from `dPd`.

Rewrite using `[hpd j hj ka.n]`. Establish `h15` using `D.host.pde_mod`. Apply the tactic sequence `rcases hp with rfl | rfl <;> omega`. Establish `hUnit : UnitC (T.dδ j ka.n)`. Take `⟨Cls, x, hF, δ, gdet, hCMP⟩` from `dRoot j hj ka.n`.

Conclude with `unitC_of_finite_character _ _ _ _ _ _ _ _ Cls δ gdet (by rw [hpq]; exact hr1) hCMP`. Establish `hPhi : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ ka.n → ∃ ph ψ x₀, (T.dδ j ka.n).PhiPin ph ψ x₀`. Introduce `h`. Take `⟨ph, ψ, x₀, -, hph, -⟩` from `dPhi j hj ka.n (hpq ▸ h)`. Conclude with `⟨ph, ψ, x₀, hph⟩`.

Establish `hPr : ∀ k, HasPrinc ((T.U j T.σ₀).X k) T.Q.l.M`. Introduce `k ga hga hcong`. Apply `hG j hj T.σ₀ hgood k ga hga` to reduce the goal to its premises. Introduce `x hx`. Take `⟨u, hu, he⟩` from `hcong x hx`.

Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[he, Nat.cast_smul_eq_nsmul]`. Normalize the expressions using the abelian group laws. Establish `hChi : ∀ k, ChiOne ((Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)).X k) (Formalism.L2.PjFree.laU (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) (wtA ka) ka.n k)`. Introduce `k γ hγ`.

Use `erw [Formalism.L2.PjFree.laU_ofPj]`. Conclude with `hM.chiTriv j hj T.σ₀ hgood _ _ hDom k γ hγ`. Establish `key` using `GlobalTheory.T.cuspForms_vanishing_off_frames_le_span_shortTheta hC _ _ _ _ (T.Q.Xo j) T.Q.c ka.n (T.dδ j ka.n) T.σ₀ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) ((Formalism.L2.PjFree.goodEmb_iff _).2 hgood) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hM.unf j hj _ hgood)) hr1 hl …`. Apply the tactic sequence `convert key using 3 <;> rfl`.
-/
theorem holSub0_le_span_short_rec : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D), LawsM T.toCore → LawsSh T → GamAt T.toCore → 0 < badN D → (∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧ ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0) → ∀ (j : ℕ) (_hj : InR D j) (ka : WeightFamilies.Wt D j), 8 * D.R.f * D.R.r + 4 ≤ ka.n → GlobalTheory.Dict.holSub0 (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA ka) ka.n) ≤ Submodule.span ℂ (rdU (T.U j T.σ₀) '' T.sh j ka) := by
  intro hC D T hM hSh hG hb hX j hj ka hn
  obtain ⟨-, dLev, dNab, dPd, dPhi, dRoot, shTot, -, -⟩ := hSh
  have hgood : GoodEmb T.Q.c T.σ₀ := T.toCore.good_σ₀
  have hpq : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := sig_add_of_pins T.Q hM.pins hj
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    simp only [Formalism.BasicNotions.Ranks.r]
    omega
  have hDom : Dom (wtA ka) ka.n := dom_wtA_of_wt ka
  have hl : T.Q.l.A = 1 := par_l_A_eq_one_of_pins T.Q hM.pins
  have hn' : 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ ka.n := by
    rw [hostSize_finrank D]
    calc 4 * (2 * D.R.f * D.R.r) + 4 = 8 * D.R.f * D.R.r + 4 := by ring
      _ ≤ ka.n := hn
  have hP3 : ¬ 3 ∣ (T.dδ j ka.n).pd := by
    obtain ⟨p, hp, hpd⟩ := dPd
    rw [hpd j hj ka.n]
    have h15 := D.host.pde_mod
    rcases hp with rfl | rfl <;> omega
  have hUnit : UnitC (T.dδ j ka.n) := by
    obtain ⟨Cls, x, hF, δ, gdet, hCMP⟩ := dRoot j hj ka.n
    exact unitC_of_finite_character _ _ _ _ _ _ _ _ Cls δ gdet (by rw [hpq]; exact hr1) hCMP
  have hPhi : (T.Q.Dw j).p + (T.Q.Dw j).q ≤ ka.n → ∃ ph ψ x₀, (T.dδ j ka.n).PhiPin ph ψ x₀ := by
    intro h
    obtain ⟨ph, ψ, x₀, -, hph, -⟩ := dPhi j hj ka.n (hpq ▸ h)
    exact ⟨ph, ψ, x₀, hph⟩
  have hPr : ∀ k, HasPrinc ((T.U j T.σ₀).X k) T.Q.l.M := by
    intro k ga hga hcong
    apply hG j hj T.σ₀ hgood k ga hga
    intro x hx
    obtain ⟨u, hu, he⟩ := hcong x hx
    refine ⟨u, hu, ?_⟩
    rw [he, Nat.cast_smul_eq_nsmul]
    abel
  have hChi : ∀ k, ChiOne ((Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)).X k)
      (Formalism.L2.PjFree.laU (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) (wtA ka) ka.n k) := by
    intro k γ hγ
    erw [Formalism.L2.PjFree.laU_ofPj]
    exact hM.chiTriv j hj T.σ₀ hgood _ _ hDom k γ hγ
  have key := GlobalTheory.T.cuspForms_vanishing_off_frames_le_span_shortTheta hC _ _ _ _ (T.Q.Xo j) T.Q.c ka.n (T.dδ j ka.n) T.σ₀ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j T.σ₀)) ((Formalism.L2.PjFree.goodEmb_iff _).2 hgood)
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hM.unf j hj _ hgood)) hr1 hl (hX j hj) hPr (dLev j hj ka.n)
    (dNab j hj ka.n) hUnit hP3 hPhi (T.nab j) (badN D) D.R.nV (wtA ka) hb hDom hn' hChi (shTot j hj _ _ hDom)
  convert key using 3 <;> rfl

end GlobalTheory.Dict
