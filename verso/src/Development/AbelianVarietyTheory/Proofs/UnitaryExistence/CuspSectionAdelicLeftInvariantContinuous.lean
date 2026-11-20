import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Formalism.LocalToGlobal.ProjectiveLattices.ParCanon
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.ValSetAlgSubset
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryInvariantRationalLevelStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnitStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpenStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStableStatement

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

/- English proof (translation)
Introduce `D H Dw l Xo c σ V r C hC dict hd mu hmul hrat hm la P hP`. Establish `: IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E)` using `⟨rfl⟩`. Establish `: Module.Finite D.host.F D.host.E` using `Module.Finite.of_restrictScalars_finite ℚ _ _`. Establish `: IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E)` using `IsModuleTopology.isTopologicalRing (AF D.host.F) _`. Establish `: IsTopologicalGroup (GA D V)` using `inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))`.

Establish `hM : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Take `⟨⟨Kf, hKf⟩, hnb⟩` from `GlobalTheory.T.exists_principalLevel_subgroup_open D V l.M`. Take `⟨h1, -, h3, -, h5⟩` from `GlobalTheory.T.memberDictionary_invariant_rational_level D H Dw l Xo c σ V r C hC dict hd Kf hKf`. Establish `hχ` using `hC.base.chi`. Establish `hsec : ∀ k, (C.M.X k).IsSec (la k) (P k)` using `fun k => (hP k).1.1`.

Prove the components needed by the constructor for the conclusion. Introduce `γ hγ g`. Take `⟨γ', hγ', he⟩` from `h1 γ hγ g`. Use `show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2`. Rewrite using `[he, hmul, hrat γ hγ, one_mul]`.

Use `show mu g * P (dict g).1 (lact γ' (dict g).2) = _`. Rewrite using `[(hsec _).2.2 γ' hγ' _ (h3 g), hχ, one_mul]`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`. Take `⟨γ, hmk, -⟩` from `hd.1 g₀`.

Generalize the expression as in `(dict g₀).1 = k at hmk`. Establish `hfr` using `fun h => GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC h k`. Establish `hPc : ContinuousOn (P k) (C.M.X k).dom` using `(hsec k).1.continuousOn`. Establish `hx : Continuous (fun g : GA D V => C.fr (γ * g) k)` using `(hfr 1).2.2.2.1.comp (continuous_const.mul continuous_id)`. Establish `hc : Continuous (fun g => mu g * P k (C.fr (γ * g) k))` using `hm.mul (hPc.comp_continuous hx fun g => (hfr _).2.1)`.

Establish `hN : {g : GA D V | FinCong V l.M (g₀⁻¹ * g)} ∈ 𝓝 g₀`. Establish `hcont : ContinuousAt (fun g : GA D V => g₀⁻¹ * g) g₀` using `(continuous_const.mul continuous_id).continuousAt`. Establish `h0` using `hnb hM`. Rewrite `h0` using `[← inv_mul_cancel g₀]`. Conclude with `hcont h0`.

Establish `heq : (fun g => mu g * P k (C.fr (γ * g) k)) =ᶠ[𝓝 g₀] adel V dict mu P` using `by filter_upwards [hN] with g hg`. Establish `hmk'` using `(GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g₀ k γ hmk).2.1 _ hg`. Rewrite `hmk'` using `[mul_inv_cancel_left]`. Take `⟨δ, hδ, he⟩` from `h5 g k γ hmk'`. Use `show mu g * P k (C.fr (γ * g) k) = mu g * P (dict g).1 (dict g).2`.

Rewrite using `[he]`. Use `show _ = mu g * P k (lact δ (C.fr (γ * g) k))`. Rewrite using `[(hsec k).2.2 δ hδ _ (hfr _).2.1, hχ, one_mul]`. Conclude with `hc.continuousAt.congr heq`.
-/
theorem adel_leftInv_and_continuous : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ dict, C.IsDict dict → ∀ mu : GA D V → ℂ, (∀ g g', mu (g * g') = mu g * mu g') → (∀ γ ∈ GQ V, mu γ = 1) → Continuous mu → ∀ (la : ∀ k, Wt (C.M.X k).Ψ r) (P : FDSec C.M.X), IsHolCusp C.M.X la P → (∀ γ ∈ GQ V, ∀ g, adel V dict mu P (γ * g) = adel V dict mu P g) ∧ Continuous (adel V dict mu P) := by
  intro D H Dw l Xo c σ V r C hC dict hd mu hmul hrat hm la P hP
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : IsTopologicalGroup (GA D V) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig V.gram))
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  obtain ⟨⟨Kf, hKf⟩, hnb⟩ := GlobalTheory.T.exists_principalLevel_subgroup_open D V l.M
  obtain ⟨h1, -, h3, -, h5⟩ := GlobalTheory.T.memberDictionary_invariant_rational_level D H Dw l Xo c σ V r C hC dict hd Kf hKf
  have hχ := hC.base.chi
  have hsec : ∀ k, (C.M.X k).IsSec (la k) (P k) := fun k => (hP k).1.1
  constructor
  · intro γ hγ g
    obtain ⟨γ', hγ', he⟩ := h1 γ hγ g
    show mu (γ * g) * P (dict (γ * g)).1 (dict (γ * g)).2 = mu g * P (dict g).1 (dict g).2
    rw [he, hmul, hrat γ hγ, one_mul]
    show mu g * P (dict g).1 (lact γ' (dict g).2) = _
    rw [(hsec _).2.2 γ' hγ' _ (h3 g), hχ, one_mul]
  · rw [continuous_iff_continuousAt]
    intro g₀
    obtain ⟨γ, hmk, -⟩ := hd.1 g₀
    generalize (dict g₀).1 = k at hmk
    have hfr := fun h => GlobalTheory.T.memberDictionary_frames_orthonormal_unit D H Dw l Xo c σ V r C hC h k
    have hPc : ContinuousOn (P k) (C.M.X k).dom := (hsec k).1.continuousOn
    have hx : Continuous (fun g : GA D V => C.fr (γ * g) k) :=
      (hfr 1).2.2.2.1.comp (continuous_const.mul continuous_id)
    have hc : Continuous (fun g => mu g * P k (C.fr (γ * g) k)) :=
      hm.mul (hPc.comp_continuous hx fun g => (hfr _).2.1)
    have hN : {g : GA D V | FinCong V l.M (g₀⁻¹ * g)} ∈ 𝓝 g₀ := by
      have hcont : ContinuousAt (fun g : GA D V => g₀⁻¹ * g) g₀ :=
        (continuous_const.mul continuous_id).continuousAt
      have h0 := hnb hM
      rw [← inv_mul_cancel g₀] at h0
      exact hcont h0
    have heq : (fun g => mu g * P k (C.fr (γ * g) k)) =ᶠ[𝓝 g₀] adel V dict mu P := by
      filter_upwards [hN] with g hg
      have hmk' := (GlobalTheory.T.markingRule_translate_stable D H Dw l Xo c σ V r C hC g₀ k γ hmk).2.1 _ hg
      rw [mul_inv_cancel_left] at hmk'
      obtain ⟨δ, hδ, he⟩ := h5 g k γ hmk'
      show mu g * P k (C.fr (γ * g) k) = mu g * P (dict g).1 (dict g).2
      rw [he]
      show _ = mu g * P k (lact δ (C.fr (γ * g) k))
      rw [(hsec k).2.2 δ hδ _ (hfr _).2.1, hχ, one_mul]
    exact hc.continuousAt.congr heq

end GlobalTheory.Member
