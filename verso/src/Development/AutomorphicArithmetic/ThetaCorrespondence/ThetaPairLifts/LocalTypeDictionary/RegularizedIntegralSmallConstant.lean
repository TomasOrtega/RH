import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsStripCombinationTrivialOutsideSet
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsRegulariserAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValueStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.SmallConst
/- English proof (translation)
Introduce `h1 h2 h3 h4 h5`. Take `⟨C1, H1⟩` from `_root_.GlobalTheory.T.exists_strip_combination_trivial_outside_set h1 h2 h3 h4 h5`. Take `⟨C2, H2⟩` from `_root_.GlobalTheory.T.exists_regulariser_local h1 h2 h3 h4 h5`. Use `⟨max C1 C2, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨x1, K1⟩` from `H1 ε CF (le_trans (le_max_left _ _) hCF)`.

Take `⟨x2, K2⟩` from `H2 ε CF (le_trans (le_max_right _ _) hCF)`. Use `⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩` and prove the remaining obligations. Establish `k1` using `K1 D large₂ he (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS`. Establish `k2` using `K2 D large₂ he (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS`. Introduce `G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁`.

Use `set f := kerSmall W Θ' g g₁ with hf`. Establish `hfd` using `(hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund`. Use `haveI := hfd.1`. Establish `hinv : ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, f (γ * u) = f u` using `kerSmall_rat_mid W B ρ t i j Θ Θ' hΘ g g₁`. Establish `key` using `zdeg_mul_integral_comm (G.V (.grid i j)) (M.ν _) (M.fd _) hfd.2 f hinv`.

Take `⟨v₀, -, w₀, hw₀, hi₀, hs₀⟩` from `k2 G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁ ∅`. Use `⟨(∫ u in M.fd _, translates w₀ f u ∂M.ν _) / zdeg w₀, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨z', P, hz'f, hz'd, hz'P⟩` from `k1 G W hW B ρ hρ t i j Θ Θ' hΘ g g₁ z`. Take `⟨v, hv, w, hw, hi, hs⟩` from `k2 G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁ (insert v₀ P)`. Establish `hvP : v ∉ P` using `fun h => hv (Finset.mem_insert_of_mem h)`.

Establish `hv0 : v ≠ v₀` using `fun h => hv (h ▸ Finset.mem_insert_self _ _)`. Establish `c1 : ∀ x ∈ w.support, ∀ y ∈ z'.support, x * y = y * x`. Introduce `x hx y hy`. Take `⟨x', rfl⟩` from `hs x hx`. Conclude with `GlobalTheory.AdelicU.commute_emb _ _ x' (hz'P y hy v hvP)`.

Establish `c2 : ∀ x ∈ w.support, ∀ y ∈ w₀.support, x * y = y * x`. Introduce `x hx y hy`. Take `⟨x', rfl⟩` from `hs x hx`. Take `⟨y', rfl⟩` from `hs₀ y hy`. Conclude with `GlobalTheory.AdelicU.commute_emb _ _ x' (GlobalTheory.AdelicU.proj_emb_ne _ _ hv0 y')`.

Establish `hz'i : IntegrableOn (translates z' f) (M.fd _) (M.ν _)` using `by rw [hz'f]; exact hz`. Establish `e1` using `key w z' c1 hi hz'i`. Establish `e2` using `key w w₀ c2 hi hi₀`. Rewrite `e1` using `[hz'f, hz'd]`. Rewrite using `[mul_div_assoc', eq_div_iff hw₀]`.

Apply `mul_left_cancel₀ hw` to reduce the goal to its premises. Take the linear combination `zdeg w₀ * e1 - zdeg z * e2`.
-/
theorem regularizedIntegral_const_of_small : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁,
  ∃ J : ℂ, ∀ z, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _) →
    ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ = zdeg z * J := by
  intro h1 h2 h3 h4 h5
  obtain ⟨C1, H1⟩ := _root_.GlobalTheory.T.exists_strip_combination_trivial_outside_set h1 h2 h3 h4 h5
  obtain ⟨C2, H2⟩ := _root_.GlobalTheory.T.exists_regulariser_local h1 h2 h3 h4 h5
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, K1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x2, K2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  have k1 := K1 D large₂ he (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS
  have k2 := K2 D large₂ he (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS
  intro G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁
  set f := kerSmall W Θ' g g₁ with hf
  have hfd := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI := hfd.1
  have hinv : ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, f (γ * u) = f u := kerSmall_rat_mid W B ρ t i j Θ Θ' hΘ g g₁
  have key := zdeg_mul_integral_comm (G.V (.grid i j)) (M.ν _) (M.fd _) hfd.2 f hinv
  obtain ⟨v₀, -, w₀, hw₀, hi₀, hs₀⟩ := k2 G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁ ∅
  refine ⟨(∫ u in M.fd _, translates w₀ f u ∂M.ν _) / zdeg w₀, fun z hz => ?_⟩
  obtain ⟨z', P, hz'f, hz'd, hz'P⟩ := k1 G W hW B ρ hρ t i j Θ Θ' hΘ g g₁ z
  classical
  obtain ⟨v, hv, w, hw, hi, hs⟩ := k2 G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁ (insert v₀ P)
  have hvP : v ∉ P := fun h => hv (Finset.mem_insert_of_mem h)
  have hv0 : v ≠ v₀ := fun h => hv (h ▸ Finset.mem_insert_self _ _)
  have c1 : ∀ x ∈ w.support, ∀ y ∈ z'.support, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', rfl⟩ := hs x hx
    exact GlobalTheory.AdelicU.commute_emb _ _ x' (hz'P y hy v hvP)
  have c2 : ∀ x ∈ w.support, ∀ y ∈ w₀.support, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x', rfl⟩ := hs x hx
    obtain ⟨y', rfl⟩ := hs₀ y hy
    exact GlobalTheory.AdelicU.commute_emb _ _ x' (GlobalTheory.AdelicU.proj_emb_ne _ _ hv0 y')
  have hz'i : IntegrableOn (translates z' f) (M.fd _) (M.ν _) := by rw [hz'f]; exact hz
  have e1 := key w z' c1 hi hz'i
  have e2 := key w w₀ c2 hi hi₀
  rw [hz'f, hz'd] at e1
  rw [mul_div_assoc', eq_div_iff hw₀]
  apply mul_left_cancel₀ hw
  linear_combination zdeg w₀ * e1 - zdeg z * e2
end GlobalTheory.SmallConst
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.SmallConst.regularizedIntegral_const_of_small | exact _root_.GlobalTheory.SmallConst.regularizedIntegral_const_of_small | (intros; apply _root_.GlobalTheory.SmallConst.regularizedIntegral_const_of_small <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.regularized_integral_small_constant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁,
  ∃ J : ℂ, ∀ z, IntegrableOn (translates z (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _) →
    ∫ u in M.fd _, translates z (kerSmall W Θ' g g₁) u ∂M.ν _ = zdeg z * J := by
  first | exact @_root_.GlobalTheory.SmallConst.regularizedIntegral_const_of_small | exact _root_.GlobalTheory.SmallConst.regularizedIntegral_const_of_small | (intros; apply _root_.GlobalTheory.SmallConst.regularizedIntegral_const_of_small <;> assumption)
end
