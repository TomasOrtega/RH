import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibility
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceFacts
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreExtraStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
noncomputable section
namespace GlobalTheory.NLinkTyp
end GlobalTheory.NLinkTyp
namespace GlobalTheory.NLinkTyp
end GlobalTheory.NLinkTyp
namespace GlobalTheory.NLinkTyp
end GlobalTheory.NLinkTyp
namespace GlobalTheory.NLinkTyp
/- English proof (translation)
Distinguish the cases in `hHG : HG D.nd D.naut i`. Establish `hX` using `_root_.GlobalTheory.T.split_bound_of_params_alt hPr.font hPr.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 CT hS.canon P (by linarith [hS.big]) (by norm_num) hCT (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA hS.facts.Conclusion1.1 hS.facts.Conclusion …`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, hT, -⟩` from `hX`. Take `⟨hgood, hZρ, s, S, sg, U, hs, hCTg, hsg, hHJ⟩` from `hT i k hi hlk hHG`. Establish `hAN : SumRepresentations.adm5 D` using `hS.facts.toCore.admA.2.2.2.2.2.2`.

Establish `hl2 : 2 < D.nd.l i` using `hlk ▸ g_two_lt L hG k`. Establish `hodd : Odd (D.nd.l i)` using `(D.nd.lPrime i).out.odd_of_ne_two (by omega)`. Establish `hlog : Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ)`. Establish `h1` using `(hG k' k).2.1`. Establish `hg0 : (0 : ℝ) < D.host.g k'` using `by exact_mod_cast (D.host.g_prime k').pos`.

Establish `hg2 : (2 : ℝ) ≤ D.host.g k` using `by exact_mod_cast (D.host.g_prime k).two_le`. Establish `h2` using `Real.log_le_log hg0 h1`. Rewrite `h2` using `[Real.log_mul (by norm_num) (by linarith)]`. Establish `h3 : Real.log 2 ≤ Real.log (D.host.g k : ℝ)` using `Real.log_le_log (by norm_num) hg2`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤`. Introduce `e he`. Rewrite `he` using `[Finset.mem_Ioo]`. Conclude with `lt_top_iff_ne_top.2 (hS.sha (D.nd.l i) e he.1 he.2)`. Conclude with `h68 i k k' hkk hlk (X.r i) (X.ρ i) hgood (fun π hπ => semisimple_decomposition_of D i (X.r i) (X.ρ i) π hAN hgood (hZρ π hπ).1 (hZρ π hπ).2) X.eta s S sg U hs hlog hCTg hsg hHJ (fun π hπ => ((hS.kill i hi).1 π hπ).1) hsha`.

Establish `hZ : D.nd.Zgood i = ∅` using `Finset.eq_empty_of_forall_notMem fun x hx => hHG ⟨x, (D.Zgood_tie i x).1 hx⟩`. Establish `hP` using `TruncatedSeriesCountingIdentities.endomorphism_index_bound i (D.nd.Zgood i) (Formalism.L2.zgoodSub D i) 0 1 one_ne_zero (fun f => by simp) (fun x hx => by rw [hZ] at hx; simp at hx) (fun x _ _ u _ => by simp)`. Rewrite `hP` using `[← TruncatedSeriesCountingIdentities.Br.etaLoc_eq, hZ, Finset.sum_empty]`. Rewrite using `[hZ, Finset.sum_empty]`. Conclude with `hP` after adjusting the coercions.
-/
theorem etaLoc_le_rhs_alt (hPr : Hypotheses₂) (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc)
    (F : FonOf D.loc D.locA HW) (X : KillingConditions.HubData D) (C₂ : ℝ) (hS : _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂) (constantSecondHub : ℝ) (CT : ℕ)
    (hCT : (CT : ℝ) ≤ L.sc.b) (h68 : _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) constantSecondHub CT) (hG : SizeG L)
    (i : D.nd.Loc) (hi : TwistedPlaces.TwLoc D i) (k k' : Fin 2) (hkk : k ≠ k') (hlk : D.nd.l i = D.host.g k) :
    (D.nd.etaLoc i : ℝ) ≤ ∑ π ∈ D.nd.Zgood i, (D.nd.mult i π : ℝ) * PairedCharacterCondition.rhs constantSecondHub X.eta i (X.ρ i) π := by
  by_cases hHG : HG D.nd D.naut i
  · have hX := _root_.GlobalTheory.T.split_bound_of_params_alt hPr.font hPr.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 CT hS.canon P
      (by linarith [hS.big]) (by norm_num) hCT (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
      hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
      hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hT, -⟩ := hX
    obtain ⟨hgood, hZρ, s, S, sg, U, hs, hCTg, hsg, hHJ⟩ := hT i k hi hlk hHG
    have hAN : SumRepresentations.adm5 D := hS.facts.toCore.admA.2.2.2.2.2.2
    have hl2 : 2 < D.nd.l i := hlk ▸ g_two_lt L hG k
    have hodd : Odd (D.nd.l i) := (D.nd.lPrime i).out.odd_of_ne_two (by omega)
    have hlog : Real.log (D.host.g k' : ℝ) ≤ 2 * Real.log (D.host.g k : ℝ) := by
      have h1 := (hG k' k).2.1
      have hg0 : (0 : ℝ) < D.host.g k' := by exact_mod_cast (D.host.g_prime k').pos
      have hg2 : (2 : ℝ) ≤ D.host.g k := by exact_mod_cast (D.host.g_prime k).two_le
      have h2 := Real.log_le_log hg0 h1
      rw [Real.log_mul (by norm_num) (by linarith)] at h2
      have h3 : Real.log 2 ≤ Real.log (D.host.g k : ℝ) := Real.log_le_log (by norm_num) hg2
      linarith
    have hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
      intro e he
      rw [Finset.mem_Ioo] at he
      exact lt_top_iff_ne_top.2 (hS.sha (D.nd.l i) e he.1 he.2)
    exact h68 i k k' hkk hlk (X.r i) (X.ρ i) hgood
      (fun π hπ => semisimple_decomposition_of D i (X.r i) (X.ρ i) π hAN hgood (hZρ π hπ).1 (hZρ π hπ).2)
      X.eta s S sg U hs hlog hCTg hsg hHJ (fun π hπ => ((hS.kill i hi).1 π hπ).1) hsha
  · have hZ : D.nd.Zgood i = ∅ :=
      Finset.eq_empty_of_forall_notMem fun x hx => hHG ⟨x, (D.Zgood_tie i x).1 hx⟩
    have hP := TruncatedSeriesCountingIdentities.endomorphism_index_bound i (D.nd.Zgood i) (Formalism.L2.zgoodSub D i) 0 1 one_ne_zero
      (fun f => by simp) (fun x hx => by rw [hZ] at hx; simp at hx) (fun x _ _ u _ => by simp)
    rw [← TruncatedSeriesCountingIdentities.Br.etaLoc_eq, hZ, Finset.sum_empty] at hP
    rw [hZ, Finset.sum_empty]
    exact_mod_cast hP
end GlobalTheory.NLinkTyp
namespace GlobalTheory.NLinkTyp
/- English proof (translation)
Introduce `hPr D L P nch HW F _ X C₂ hS constantSecondHub C1 CT hC68 hC1 hCT h68 hmult hpar hG`. Establish `heta : (X.eta : ℝ) ≤ L.etaSz`. Rewrite using `[hS.canon.eta]`. Conclude with `Nat.floor_le (by linarith [TwistedPlaces.one_le_eta L P])`. Establish `hM : ∀ l ∈ TwistedPlaces.gset D, 0 ≤ (2000 * (constantSecondHub + 1) + 5 * C1) * L.sc.x ^ (2000 * (constantSecondHub + 1) + 5 * C1) * L.etaSz + TwistedPlaces.epsL l + TwistedPlaces.VVr D l + TwistedPlaces.vhE D l + TwistedPlaces.epsL l`.

Introduce `l _`. Establish `h1 : 0 ≤ L.sc.x ^ (2000 * (constantSecondHub + 1) + 5 * C1)` using `Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _`. Establish `h2 : 0 ≤ L.etaSz` using `by linarith [TwistedPlaces.one_le_eta L P]`. Establish `h3 : 0 ≤ TwistedPlaces.epsL l` using `by unfold TwistedPlaces.epsL; positivity`. Establish `h4 : 0 ≤ TwistedPlaces.VVr D l` using `by show (0 : ℝ) ≤ ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen l e : ℚ) : ℝ)`.

Conclude with `Finset.sum_nonneg fun e _ => D.what₂.shaLen_nonneg l e` after adjusting the coercions. Establish `h5 : 0 ≤ TwistedPlaces.vhE D l` using `by unfold TwistedPlaces.vhE; positivity`. Establish `h6 : 0 ≤ 2000 * (constantSecondHub + 1) + 5 * C1` using `by linarith`. Use `mul_nonneg (mul_nonneg h6 h1) h2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `starH_of_local L _ (fun i hi hl => ?_) hM hmult (hS.facts.toCore.a3 L)` and prove the remaining obligations. Establish `hk : ∃ k k' : Fin 2, k ≠ k' ∧ D.nd.l i = D.host.g k`. Unfold `TwistedPlaces.gset at hl`. Break down `Finset.mem_insert.1 hl with h | h` into its components or cases. Conclude with `⟨0, 1, by decide, h⟩`.

Conclude with `⟨1, 0, by decide, Finset.mem_singleton.1 h⟩`. Take `⟨k, k', hkk, hlk⟩` from `hk`. Establish `hl2 : D.nd.l i ≠ 2` using `by have := g_two_lt L hG k; omega`. Use `(_root_.GlobalTheory.NLinkTyp.etaLoc_le_rhs_alt hPr D L P nch HW F X C₂ hS constantSecondHub CT hCT h68 hG i hi k k' hkk hlk).trans ?_` and prove the remaining obligations. Use `Finset.sum_le_sum fun π hπ => ?_` and prove the remaining obligations.

Apply the tactic sequence `exact mul_le_mul_of_nonneg_left (rhs_le L P X constantSecondHub C1 hC68 hC1 hpar heta hS.kill i hi (by rw [hlk]; exact UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k)) (UpperTheory.KStar.nuL_eq_zero_of_g D _ (by rw [hlk]; fin_cases k <;> simp [TwistedPlaces.gset]) hl2 …`.
-/
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ (constantSecondHub C1 : ℝ) (CT : ℕ), 0 ≤ constantSecondHub → 1 ≤ C1 → (CT : ℝ) ≤ L.sc.b → _root_.Formalism.MainNotions.PairedCharacterCondition.PairedCharacterConditionAlt (D := D) constantSecondHub CT → MultLe L → TwistedPlaces.ParametersPolynomiallyBounded L C1 P → SizeG L → StarH L (2000 * (constantSecondHub + 1) + 5 * C1) := by
  intro hPr D L P nch HW F _ X C₂ hS constantSecondHub C1 CT hC68 hC1 hCT h68 hmult hpar hG
  have heta : (X.eta : ℝ) ≤ L.etaSz := by
    rw [hS.canon.eta]
    exact Nat.floor_le (by linarith [TwistedPlaces.one_le_eta L P])
  have hM : ∀ l ∈ TwistedPlaces.gset D, 0 ≤ (2000 * (constantSecondHub + 1) + 5 * C1) * L.sc.x ^ (2000 * (constantSecondHub + 1) + 5 * C1) * L.etaSz +
      TwistedPlaces.epsL l + TwistedPlaces.VVr D l + TwistedPlaces.vhE D l + TwistedPlaces.epsL l := by
    intro l _
    have h1 : 0 ≤ L.sc.x ^ (2000 * (constantSecondHub + 1) + 5 * C1) := Real.rpow_nonneg (by linarith [L.sc.one_lt_alt]) _
    have h2 : 0 ≤ L.etaSz := by linarith [TwistedPlaces.one_le_eta L P]
    have h3 : 0 ≤ TwistedPlaces.epsL l := by unfold TwistedPlaces.epsL; positivity
    have h4 : 0 ≤ TwistedPlaces.VVr D l := by
      show (0 : ℝ) ≤ ((∑ e ∈ Finset.Ico 1 D.R.t, D.what₂.shaLen l e : ℚ) : ℝ)
      exact_mod_cast Finset.sum_nonneg fun e _ => D.what₂.shaLen_nonneg l e
    have h5 : 0 ≤ TwistedPlaces.vhE D l := by unfold TwistedPlaces.vhE; positivity
    have h6 : 0 ≤ 2000 * (constantSecondHub + 1) + 5 * C1 := by linarith
    have := mul_nonneg (mul_nonneg h6 h1) h2
    linarith
  refine starH_of_local L _ (fun i hi hl => ?_) hM hmult (hS.facts.toCore.a3 L)
  have hk : ∃ k k' : Fin 2, k ≠ k' ∧ D.nd.l i = D.host.g k := by
    unfold TwistedPlaces.gset at hl
    rcases Finset.mem_insert.1 hl with h | h
    · exact ⟨0, 1, by decide, h⟩
    · exact ⟨1, 0, by decide, Finset.mem_singleton.1 h⟩
  obtain ⟨k, k', hkk, hlk⟩ := hk
  have hl2 : D.nd.l i ≠ 2 := by have := g_two_lt L hG k; omega
  refine (_root_.GlobalTheory.NLinkTyp.etaLoc_le_rhs_alt hPr D L P nch HW F X C₂ hS constantSecondHub CT hCT h68 hG i hi k k' hkk hlk).trans ?_
  refine Finset.sum_le_sum fun π hπ => ?_
  exact mul_le_mul_of_nonneg_left (rhs_le L P X constantSecondHub C1 hC68 hC1 hpar heta hS.kill i hi
    (by rw [hlk]; exact UpperTheory.Small.not_mem_of_mod D.host (D.ntypes.g_cond k))
    (UpperTheory.KStar.nuL_eq_zero_of_g D _ (by rw [hlk]; fin_cases k <;> simp [TwistedPlaces.gset]) hl2) π hπ) (Nat.cast_nonneg _)
end GlobalTheory.NLinkTyp
end
end
