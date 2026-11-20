import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelArchimedeanUnipotentSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierOpenSubgroupSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSupportPartialFourierIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnitaryPreservesSchwartzSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupInNeighbourhoodStatement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.FixPure

open GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology ComplexConjugate

open scoped Classical in

/- English proof (translation)
Establish `hl : (LinearMap.proj x0 : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm (Fin n × Fin d)`. Introduce `g _`. Use `⟨g (fun i => (x0 i).2) • ((BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x0 i).1)).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.proj_apply, pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]`. Rewrite using `[mul_comm]`.

Both sides reduce to the same expression. Conclude with `hW.2.2 _ hl Φ hΦ`.
-/
theorem continuous_eval {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil ψ χX χW om) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) (x0 : Fin n × Fin d → AF F) :
    Continuous fun p : UA σ X.J × UA σ W.J => om p Φ x0 := by
  have hl : (LinearMap.proj x0 : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨g (fun i => (x0 i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x0 i).1)).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    rw [mul_comm]
    rfl
  exact hW.2.2 _ hl Φ hΦ

/- English proof (translation)
Use `letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _`. Use `haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`.

Distinguish the cases in `h0 : Φ = 0`. Conclude with `⟨⊤, isOpen_univ, fun k _ _ => by rw [h0, map_zero]⟩`. Take `⟨x0, hx0⟩` from `Function.ne_iff.1 h0`. Establish `hx0' : Φ x0 ≠ 0` using `hx0`. Establish `hF : IsTotallyReal F` using `hP.base.cm.1`.

Establish `hψ` using `GlobalTheory.StdCharFromIsStd.isCharAF hP.base.std`. Establish `hσ` using `GlobalTheory.SiegelSet.sigma_sigma hP.base.cm`. Establish `hW` using `GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil`. Take `⟨Mo, hMo, hper⟩` from `GlobalTheory.T.partial_fourier_open_subgroup_support B.ψ hP.base.std Φ hΦ`. Take `⟨K, hK, hsupp⟩` from `GlobalTheory.T.compact_support_partial_fourier_integral B.ψ hP.base.std Φ hΦ`.

Establish `hS2` using `GlobalTheory.T.small_unitary_preserves_schwartz_support σ X W M Mo K hMo hK`. Establish `hc : Continuous fun k : UA σ W.J => om (1, k) Φ x0` using `(continuous_eval hP.weil Φ hΦ x0).comp (continuous_const.prodMk continuous_id)`. Establish `hnear : ∀ᶠ k in 𝓝 (1 : UA σ W.J), ‖om (1, k) Φ x0 / Φ x0 - 1‖ < 1 / 2`. Use `(((hc.div_const _).sub continuous_const).norm.continuousAt (x := 1)).eventually_lt continuousAt_const ?_` and prove the remaining obligations. Establish `e1 : om ((1 : UA σ X.J), (1 : UA σ W.J)) = 1` using `map_one om`.

Use `show ‖om ((1 : UA σ X.J), (1 : UA σ W.J)) Φ x0 / Φ x0 - 1‖ < 1 / 2`. Rewrite using `[e1, Module.End.one_apply, div_self hx0', sub_self, norm_zero]`. Evaluate the numerical expressions. Establish `hi : Tendsto (fun k : UA σ W.J => k⁻¹) (𝓝 1) (𝓝 1)`. Use `(continuous_inv (G := UA σ W.J)).tendsto 1` as an intermediate fact.

Rewrite `this` using `[inv_one]`. Then use the resulting hypothesis. Take `⟨U, hUo, hUN⟩` from `GlobalTheory.T.exists_open_subgroup_in_neighbourhood σ hσ W.J _ ((hS2.and (hi.eventually hS2)).and hnear)`. Establish `hfinv : ∀ k : UA σ W.J, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → (mat k⁻¹).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1`. Introduce `k hk`. Establish `e : mat k⁻¹ * mat k = 1` using `by show ((k⁻¹ * k : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1`.

Rewrite using `[inv_mul_cancel]`. Both sides reduce to the same expression. Establish `h1 : (mat k⁻¹ * mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = (mat k⁻¹).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) * (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))` using `Matrix.map_mul (f := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom)`. Rewrite `h1` using `[e, Matrix.map_one _ (map_zero _) (map_one _), hk, mul_one]`. Conclude with `h1.symm`.

Establish `hfpow : ∀ k : UA σ W.J, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → ∀ m : ℕ, (mat (k ^ m)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1`. Introduce `k hk m`. Proceed by induction on `m with`. Consider the case `zero => show ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1.map _ = 1`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.

Consider the case `succ m ih`. Establish `e : mat (k ^ (m + 1)) = mat (k ^ m) * mat k` using `by show ((k ^ m * k : UA σ W.J) : GL (Fin d) (AE F E)).1 = _`. Both sides reduce to the same expression. Establish `h1 : (mat (k ^ m) * mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = (mat (k ^ m)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) * (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))` using `Matrix.map_mul (f := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom)`. Rewrite using `[e, h1, ih, hk, mul_one]`.

Establish `key : ∀ k ∈ U, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → om (1, k) Φ = (om (1, k) Φ x0 / Φ x0) • Φ`. Introduce `k hk hfk`. Take `⟨⟨hPk, hPk'⟩, -⟩` from `hUN k hk hfk`. Establish `hfk'` using `hfinv k hfk`. Take `⟨c1, b1, i1⟩` from `GlobalTheory.SplitSvN.schA_facts hF hΦ`.

Take `⟨c2, b2, i2⟩` from `GlobalTheory.SplitSvN.schA_facts hF (hW.pres (1, k) Φ hΦ)`. Take `⟨c, hc⟩` from `GlobalTheory.SplitSvN.proportional_of_coeff B.ψ hψ.1 hψ.2.1 (GlobalTheory.SWQ.Annihilator.self_annihilator F hF B.ψ hψ).1 1 (one_mul 1) Φ (om (1, k) Φ) (fun _ => 1) Φ (om (1, k) Φ) (fun x => by simp) (fun x => by simp) c1 c2 b1 b2 i1 i2 (fun x₁ y₁ _ _ μ hμ => by set w : (Fin n × …`. Establish `hact : actAB (cA σ) ((1 : UA σ X.J), k) u' = u`. Establish `e2 : mat k * mat k⁻¹ = 1` using `by show ((k * k⁻¹ : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1`. Rewrite using `[mul_inv_cancel]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin n) (Fin n) (AE F E)) * ((1 : Matrix (Fin n) (Fin n) (AE F E)) * u * Matrix.transpose (mat k⁻¹)) * Matrix.transpose (mat k) = u`. Rewrite using `[Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e2, Matrix.transpose_one, Matrix.mul_one]`. Establish `e1 : schr B.ψ w (om (1, k) Φ) = om (1, k) (M.co.rho B.ψ u' Φ)`. Rewrite using `[hW.impl (1, k) u' Φ hΦ, hact]`.

Simplify using `only [Darboux.rho, hu, LinearEquiv.apply_symm_apply]`. Use `show ∫ x, om (1, k) Φ x * conj (schr B.ψ w (om (1, k) Φ) x) ∂μ = ∫ x, Φ x * conj (schr B.ψ w Φ x) ∂μ`. Rewrite using `[e1, GlobalTheory.CptCoeff.integral_mul_conj_map (μ := μ) (schA F _) (fun f hf => GlobalTheory.T.adelic_schwartz_mem_L2 F _ μ hμ f hf) (om (1, k)) (fun f hf => hW.pres _ f hf) (fun f hf => hW.unit μ hμ _ f hf) hΦ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std u' Φ hΦ)]`. Use `show ∫ x, Φ x * conj (schr B.ψ (M.co.e u') Φ x) ∂μ = _`. Distinguish the cases in `hcw : ∫ x, Φ x * conj (schr B.ψ w Φ x) ∂μ = 0`.

Distinguish the cases in `hcw2 : ∫ x, Φ x * conj (schr B.ψ (M.co.e u') Φ x) ∂μ = 0`. Rewrite using `[hcw, hcw2]`. Take `⟨h1, h2⟩` from `hsupp μ hμ _ hcw2`. Take `⟨ha, hb1, hb2⟩` from `hPk hfk _ h1 h2`. Establish `hback : M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm (M.co.e u'))) = w`.

Rewrite using `[LinearEquiv.symm_apply_apply, hact, hu, LinearEquiv.apply_symm_apply]`. Rewrite `ha`, `hb1`, `hb2` using `[hback]`. Use `hper μ hμ (M.co.e u') (w - M.co.e u') ha hb1 hb2` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Conclude with `this.symm`.

Take `⟨h1, h2⟩` from `hsupp μ hμ w hcw`. Take `⟨ha, hb1, hb2⟩` from `hPk' hfk' w h1 h2`. Use `hper μ hμ w (M.co.e u' - w) ha hb1 hb2` as an intermediate fact. Rewrite using `[add_sub_cancel] at this)` and apply the resulting hypothesis. Establish `hcx : c = om (1, k) Φ x0 / Φ x0`.

Rewrite using `[hc, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hx0']`. Use `conv_lhs => rw [hc]`. Rewrite using `[hcx]`. Use `⟨U, hUo, fun k hk hfk => ?_⟩` and prove the remaining obligations. Use `set c := om (1, k) Φ x0 / Φ x0 with hcdef`.

Establish `hpow : ∀ m : ℕ, om (1, k ^ m) Φ = c ^ m • Φ`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Rewrite using `[pow_zero, pow_zero, one_smul]`.

Conclude with `congrArg (· Φ) (map_one om)`. Consider the case `succ m ih`. Establish `e : ((1 : UA σ X.J), k ^ (m + 1)) = ((1 : UA σ X.J), k ^ m) * (1, k)`. Rewrite using `[Prod.mk_mul_mk, one_mul, pow_succ]`. Rewrite using `[e, map_mul, Module.End.mul_apply, key k hk hfk, map_smul, ih, smul_smul, pow_succ, mul_comm]`.

Establish `hc1 : c = 1` using `GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le fun m => by`. Establish `hm` using `(hUN (k ^ m) (pow_mem hk m) (hfpow k hfk m)).2`. Rewrite `hm` using `[hpow m, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hx0']`. Conclude with `hm.le`. Rewrite using `[key k hk hfk, ← hcdef, hc1, one_smul]`.
-/
theorem fix_schA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (hP : GlobalTheory.ThK.IsPair B M χX χW om r s r' s') (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) ∧ ∀ k ∈ U,
      (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → om (1, k) Φ = Φ := by
  classical
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  by_cases h0 : Φ = 0
  · exact ⟨⊤, isOpen_univ, fun k _ _ => by rw [h0, map_zero]⟩
  obtain ⟨x0, hx0⟩ := Function.ne_iff.1 h0
  have hx0' : Φ x0 ≠ 0 := hx0
  have hF : IsTotallyReal F := hP.base.cm.1
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hP.base.std
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  obtain ⟨Mo, hMo, hper⟩ := GlobalTheory.T.partial_fourier_open_subgroup_support B.ψ hP.base.std Φ hΦ
  obtain ⟨K, hK, hsupp⟩ := GlobalTheory.T.compact_support_partial_fourier_integral B.ψ hP.base.std Φ hΦ
  have hS2 := GlobalTheory.T.small_unitary_preserves_schwartz_support σ X W M Mo K hMo hK
  have hc : Continuous fun k : UA σ W.J => om (1, k) Φ x0 :=
    (continuous_eval hP.weil Φ hΦ x0).comp (continuous_const.prodMk continuous_id)
  have hnear : ∀ᶠ k in 𝓝 (1 : UA σ W.J), ‖om (1, k) Φ x0 / Φ x0 - 1‖ < 1 / 2 := by
    refine (((hc.div_const _).sub continuous_const).norm.continuousAt (x := 1)).eventually_lt continuousAt_const ?_
    have e1 : om ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 := map_one om
    show ‖om ((1 : UA σ X.J), (1 : UA σ W.J)) Φ x0 / Φ x0 - 1‖ < 1 / 2
    rw [e1, Module.End.one_apply, div_self hx0', sub_self, norm_zero]
    norm_num
  have hi : Tendsto (fun k : UA σ W.J => k⁻¹) (𝓝 1) (𝓝 1) := by
    have := (continuous_inv (G := UA σ W.J)).tendsto 1
    rwa [inv_one] at this
  obtain ⟨U, hUo, hUN⟩ := GlobalTheory.T.exists_open_subgroup_in_neighbourhood σ hσ W.J _ ((hS2.and (hi.eventually hS2)).and hnear)
  have hfinv : ∀ k : UA σ W.J, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 →
      (mat k⁻¹).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
    intro k hk
    have e : mat k⁻¹ * mat k = 1 := by
      show ((k⁻¹ * k : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1
      rw [inv_mul_cancel]; rfl
    have h1 : (mat k⁻¹ * mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) =
        (mat k⁻¹).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) *
          (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) :=
      Matrix.map_mul (f := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom)
    rw [e, Matrix.map_one _ (map_zero _) (map_one _), hk, mul_one] at h1
    exact h1.symm
  have hfpow : ∀ k : UA σ W.J, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → ∀ m : ℕ,
      (mat (k ^ m)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
    intro k hk m
    induction m with
    | zero =>
      show ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1.map _ = 1
      exact Matrix.map_one _ (map_zero _) (map_one _)
    | succ m ih =>
      have e : mat (k ^ (m + 1)) = mat (k ^ m) * mat k := by
        show ((k ^ m * k : UA σ W.J) : GL (Fin d) (AE F E)).1 = _
        rfl
      have h1 : (mat (k ^ m) * mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) =
          (mat (k ^ m)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) *
            (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) :=
        Matrix.map_mul (f := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom)
      rw [e, h1, ih, hk, mul_one]
  have key : ∀ k ∈ U, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 →
      om (1, k) Φ = (om (1, k) Φ x0 / Φ x0) • Φ := by
    intro k hk hfk
    obtain ⟨⟨hPk, hPk'⟩, -⟩ := hUN k hk hfk
    have hfk' := hfinv k hfk
    obtain ⟨c1, b1, i1⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
    obtain ⟨c2, b2, i2⟩ := GlobalTheory.SplitSvN.schA_facts hF (hW.pres (1, k) Φ hΦ)
    obtain ⟨c, hc⟩ := GlobalTheory.SplitSvN.proportional_of_coeff B.ψ hψ.1 hψ.2.1
      (GlobalTheory.SWQ.Annihilator.self_annihilator F hF B.ψ hψ).1 1 (one_mul 1) Φ (om (1, k) Φ) (fun _ => 1) Φ (om (1, k) Φ)
      (fun x => by simp) (fun x => by simp) c1 c2 b1 b2 i1 i2 (fun x₁ y₁ _ _ μ hμ => by
        set w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) := (x₁, y₁) with hw
        set u := M.co.e.symm w with hu
        set u' := actAB (cA σ) ((1 : UA σ X.J), k⁻¹) u with hu'
        have hact : actAB (cA σ) ((1 : UA σ X.J), k) u' = u := by
          have e2 : mat k * mat k⁻¹ = 1 := by
            show ((k * k⁻¹ : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1
            rw [mul_inv_cancel]; rfl
          change (1 : Matrix (Fin n) (Fin n) (AE F E)) * ((1 : Matrix (Fin n) (Fin n) (AE F E)) * u * Matrix.transpose (mat k⁻¹)) * Matrix.transpose (mat k) = u
          rw [Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e2, Matrix.transpose_one,
            Matrix.mul_one]
        have e1 : schr B.ψ w (om (1, k) Φ) = om (1, k) (M.co.rho B.ψ u' Φ) := by
          rw [hW.impl (1, k) u' Φ hΦ, hact]
          simp only [Darboux.rho, hu, LinearEquiv.apply_symm_apply]
        show ∫ x, om (1, k) Φ x * conj (schr B.ψ w (om (1, k) Φ) x) ∂μ = ∫ x, Φ x * conj (schr B.ψ w Φ x) ∂μ
        rw [e1, GlobalTheory.CptCoeff.integral_mul_conj_map (μ := μ) (schA F _) (fun f hf => GlobalTheory.T.adelic_schwartz_mem_L2 F _ μ hμ f hf)
          (om (1, k)) (fun f hf => hW.pres _ f hf) (fun f hf => hW.unit μ hμ _ f hf) hΦ
          (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std u' Φ hΦ)]
        show ∫ x, Φ x * conj (schr B.ψ (M.co.e u') Φ x) ∂μ = _
        by_cases hcw : ∫ x, Φ x * conj (schr B.ψ w Φ x) ∂μ = 0
        · by_cases hcw2 : ∫ x, Φ x * conj (schr B.ψ (M.co.e u') Φ x) ∂μ = 0
          · rw [hcw, hcw2]
          · obtain ⟨h1, h2⟩ := hsupp μ hμ _ hcw2
            obtain ⟨ha, hb1, hb2⟩ := hPk hfk _ h1 h2
            have hback : M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm (M.co.e u'))) = w := by
              rw [LinearEquiv.symm_apply_apply, hact, hu, LinearEquiv.apply_symm_apply]
            rw [hback] at ha hb1 hb2
            have := hper μ hμ (M.co.e u') (w - M.co.e u') ha hb1 hb2
            rw [add_sub_cancel] at this
            exact this.symm
        · obtain ⟨h1, h2⟩ := hsupp μ hμ w hcw
          obtain ⟨ha, hb1, hb2⟩ := hPk' hfk' w h1 h2
          have := hper μ hμ w (M.co.e u' - w) ha hb1 hb2
          rwa [add_sub_cancel] at this)
    have hcx : c = om (1, k) Φ x0 / Φ x0 := by
      rw [hc, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hx0']
    conv_lhs => rw [hc]
    rw [hcx]
  refine ⟨U, hUo, fun k hk hfk => ?_⟩
  set c := om (1, k) Φ x0 / Φ x0 with hcdef
  have hpow : ∀ m : ℕ, om (1, k ^ m) Φ = c ^ m • Φ := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, pow_zero, one_smul]
      exact congrArg (· Φ) (map_one om)
    | succ m ih =>
      have e : ((1 : UA σ X.J), k ^ (m + 1)) = ((1 : UA σ X.J), k ^ m) * (1, k) := by
        rw [Prod.mk_mul_mk, one_mul, pow_succ]
      rw [e, map_mul, Module.End.mul_apply, key k hk hfk, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hc1 : c = 1 := GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le fun m => by
    have hm := (hUN (k ^ m) (pow_mem hk m) (hfpow k hfk m)).2
    rw [hpow m, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hx0'] at hm
    exact hm.le
  rw [key k hk hfk, ← hcdef, hc1, one_smul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' _ hP f φ hφ hvac`. Establish `hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1` using `by filter_upwards [hvac, hP.good.std] with v h1 h2`. Rewrite using `[h1, h2]`. Conclude with `fix_schA hP _ (GlobalTheory.TensUniq.pure_mem_schA f φ hφ hstd)`.
-/
theorem fix_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.KP → GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) ∧ ∀ k ∈ U,
        (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → om (1, k) (pure f φ) = pure f φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' _ hP f φ hφ hvac
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hvac, hP.good.std] with v h1 h2
    rw [h1, h2]
  exact fix_schA hP _ (GlobalTheory.TensUniq.pure_mem_schA f φ hφ hstd)

end GlobalTheory.FixPure
