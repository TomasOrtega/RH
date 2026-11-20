import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CtxExists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDerivAtInverseThetaTransformHeisenbergOneParaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformInverseTransformEqQuasiPeriodicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseThetaTransformHasLevelCompactFiniteSupporStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InverseAdelicThetaTransformRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzInverseThetaTransformOnRealTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesContinuousFiniteRealPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLinearCoordinatesRationalSurjectiveOfCMStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtZeroHeisenbergCMRealLineThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMThetaQuasiInvariantRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMRealLineFiniteInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffDerivHeisenbergCMRealLineThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftStandardCharacterIndefiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergCMRealLineAddNoPhaseStatement

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaOntoF

open Formalism.IndefR.DatumF GlobalTheory.ThetaTransform GlobalTheory.SWQ

/- English proof (translation)
Use `(invOf_eq_right_inv ?_).symm` and prove the remaining obligations. Establish `h : (2 : AF F) * algebraMap F (AF F) (1 / 2) = algebraMap F (AF F) (2 * (1 / 2))`. Rewrite using `[map_mul, map_ofNat]`. Rewrite using `[h]`. Evaluate the numerical expressions.
-/
theorem algebraMap_half (F : Type) [Field F] [NumberField F] [Invertible (2 : AF F)] :
    algebraMap F (AF F) (1 / 2) = ⅟2 := by
  refine (invOf_eq_right_inv ?_).symm
  have h : (2 : AF F) * algebraMap F (AF F) (1 / 2) = algebraMap F (AF F) (2 * (1 / 2)) := by
    rw [map_mul, map_ofNat]
  rw [h]
  norm_num

/- English proof (translation)
Use function extensionality and compare the values at `w`. Simplify using `only [heisV, heisOF, symplOHF, Function.comp_apply, he, LinearEquiv.apply_symm_apply, map_add, algebraMap_half]`.
-/
theorem heisV_comp_symm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {N : ℕ} {e : WOF F E nS nT ≃ₗ[AF F] VA F N} (ψ : AddChar (AF F) ℂ)
    (he : ∀ w w', symplOF σ JS JT ξ₀ w w' = symV (e w) (e w')) (u : VA F N) (f : WOF F E nS nT → ℂ) :
    heisV ψ u (f ∘ e.symm) = heisOF σ JS JT ξ₀ ψ (e.symm u) f ∘ e.symm := by
  funext w
  simp only [heisV, heisOF, symplOHF, Function.comp_apply, he, LinearEquiv.apply_symm_apply, map_add,
    algebraMap_half]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd N e he hrat f hf`. Establish `hR : IsTotallyReal F` using `hB.cm.1`. Establish `hψ : IsCharAF F B.ψ` using `hstd.1`. Take `⟨hc, hcs, hfin, hinf⟩` from `GlobalTheory.T.adelicLinearCoordinates_continuous_finite_real_points F E nS nT N e`. Take `⟨lam, ν, hC⟩` from `GlobalTheory.SWQ.ctx_exists F hR B.ψ hψ N (half F N) half_ne_zero`.

Take `⟨-, -, -, ⟨K, hK, hKc⟩, 𝓓, -, hD, h1⟩` from `GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1`. Establish `hsymm : ∀ (u : VA F N) (g : WOF F E nS nT → ℂ), heisV B.ψ u (g ∘ e.symm) = heisOF σ JS JT ξ₀ B.ψ (e.symm u) g ∘ e.symm` using `fun u g => heisV_comp_symm B.ψ he u g`. Establish `hquasi : ∀ g, IsThetaFunOF σ JS JT ξ₀ B.ψ g → QuasiV B.ψ (g ∘ e.symm)`. Introduce `g hg a b w`. Take `⟨x, hx⟩` from `GlobalTheory.T.adelicLinearCoordinates_rational_surjective_of_CM F E nS nT N e hrat a b`.

Establish `hx' : e.symm (rat a, rat b) = ratWF x` using `by rw [← hx]; exact e.symm_apply_apply _`. Simplify using `only [Function.comp_apply, map_add, hx', hg.quasi, symplOHF, he, hx, LinearEquiv.apply_symm_apply, algebraMap_half]`. Establish `hbdd : ∀ g : VA F N → ℂ, Continuous g → QuasiV B.ψ g → ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C`. Introduce `g hg hq`. Take `⟨C, hC'⟩` from `(hK.prod hK).exists_bound_of_continuousOn hg.continuousOn`.

Use `⟨C, fun w => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hKc w.1`. Take `⟨b, hb⟩` from `hKc w.2`. Establish `e1 : w = (rat a, rat b) + (w.1 - rat a, w.2 - rat b)` using `Prod.ext (by simp) (by simp)`. Rewrite using `[e1, hq, norm_mul, hψ.2.1, one_mul]`.

Conclude with `hC' _ ⟨ha, hb⟩`. Set `𝒱 : Set (VA F N → ℂ)` to `{g | ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ g = f ∘ e.symm}`. Establish `hV : ∀ g ∈ 𝒱, Continuous g ∧ QuasiV B.ψ g ∧ ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Conclude with `⟨hg.cont.comp hcs, hquasi g hg, hbdd _ (hg.cont.comp hcs) (hquasi g hg)⟩`.

Establish `hder : ∀ g ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ g' ∈ 𝒱, ∀ x, HasDerivAt (fun t : ℝ => invV B.ψ ν 𝓓 (heisV B.ψ (M t) g) x) (invV B.ψ ν 𝓓 g' x) 0`. Introduce and unpack `_ ⟨g, hg, rfl⟩ M hM`. Set `L : ℝ →+ WOF F E nS nT` to `e.symm.toLinearMap.toAddMonoidHom.comp M`. Establish `hL : Continuous L` using `hcs.comp hM.1`. Establish `hL0 : ∀ t, (L t).map (finPartF F E) = 0` using `fun t => (hfin _).2 (by`.

Establish `: e (L t) = M t` using `e.apply_symm_apply _`. Rewrite using `[this]`. Conclude with `hM.2 t)`. Set `g' : WOF F E nS nT → ℂ` to `fun w => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) 0`. Establish `hlev' : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧ ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u g' = g'`.

Take `⟨U, hUo, hU⟩` from `hg.level`. Conclude with `⟨U, hUo, fun u hu h0 => GlobalTheory.T.deriv_heisenbergCM_real_line_finite_invariant F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g L hL hL0 u h0 (hU u hu h0)⟩`. Establish `hsm'` using `GlobalTheory.T.contDiff_deriv_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0`. Establish `hg' : IsThetaFunOF σ JS JT ξ₀ B.ψ g'` using `⟨GlobalTheory.T.deriv_heisenbergCM_theta_quasiInvariant_rational F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0, hlev', GlobalTheory.T.theta_lift_standard_character_indefinite F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g' hlev' hsm', hsm'⟩`. Establish `hds : ∀ w s, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) (heisOF σ JS JT ξ₀ B.ψ (L s) g' w) s`.

Introduce `w s`. Establish `h1' : HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w) (heisOF σ JS JT ξ₀ B.ψ (L s) g' w) 0`. Establish `e2 : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w) = fun t => B.ψ (symplOHF σ JS JT ξ₀ w (L s)) * heisOF σ JS JT ξ₀ B.ψ (L t) g (w + L s)`. Use function extensionality and compare the values at `fun t => GlobalTheory.T.heisenbergOp_realLine_add_eq_phase_mul_shifted F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd L hL hL0 g w s t`. Rewrite using `[e2]`.

Conclude with `((GlobalTheory.T.differentiableAt_zero_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0 (w + L s)).hasDerivAt).const_mul _`. Establish `h2` using `HasDerivAt.comp_sub_const s s (by rwa [sub_self]) (f := fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w)`. Establish `e3 : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) = fun x => heisOF σ JS JT ξ₀ B.ψ (L (s + (x - s))) g w`. Use function extensionality and compare the values at `x`. Rewrite using `[add_sub_cancel]`.

Rewrite using `[e3]`. Conclude with `h2`. Use `⟨_, ⟨g', hg', rfl⟩, ?_⟩` and prove the remaining obligations. Take `⟨c1, -, C₁, hC₁⟩` from `hV _ ⟨g, hg, rfl⟩`. Take `⟨c2, -, C₂, hC₂⟩` from `hV _ ⟨g', hg', rfl⟩`.

Use `GlobalTheory.T.hasDerivAt_inverseThetaTransform_heisenberg_oneParam F N B.ψ lam ν hC 𝓓 hD h1 _ _ (max C₁ C₂) c1 c2 (fun w => (hC₁ w).trans (le_max_left _ _)) (fun w => (hC₂ w).trans (le_max_right _ _)) M hM.1 fun w s => ?_` and prove the remaining obligations. Simplify using `only [hsymm, Function.comp_apply]`. Conclude with `hds (e.symm w) s`. Establish `hmem : f ∘ e.symm ∈ 𝒱` using `⟨f, hf, rfl⟩`. Establish `hlev : LevelV B.ψ (f ∘ e.symm)`.

Take `⟨U, hUo, hU⟩` from `hf.level`. Use `⟨U.comap e.symm.toLinearMap.toAddMonoidHom, hUo.preimage hcs, fun u hu h0 h0' => ?_⟩` and prove the remaining obligations. Rewrite using `[hsymm, hU (e.symm u) hu ((hinf _).2 (by rw [e.apply_symm_apply]; exact ⟨h0, h0'⟩))]`. Take `⟨hl, hs⟩` from `GlobalTheory.T.inverseThetaTransform_has_level_compact_finite_support F N B.ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).2.1 hlev`. Establish `hS : invV B.ψ ν 𝓓 (f ∘ e.symm) ∈ GlobalTheory.WeilM.schA F (Fin N)` using `GlobalTheory.T.mem_adelicSchwartzSpace_of_level_compact_schwartz F N _ hl hs (GlobalTheory.T.schwartz_inverse_theta_transform_on_real_translates F N B.ψ lam ν hC 𝓓 hD h1 𝒱 hV hder (GlobalTheory.T.inverseAdelicThetaTransform_rapid_decay F N B.ψ lam ν hC 𝓓 hD h1 𝒱 (fun g hg => (hV …`.

Use `⟨_, hS, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.T.thetaTransform_inverseTransform_eq_quasiPeriodic F N B.ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).1 (hV _ hmem).2.1 (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N _ hS)]`. Use function extensionality and compare the values at `w`. Simplify using the standard rewrite rules.
-/
theorem exists_thV_eqF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ (N : ℕ) (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
        (∀ w w', Formalism.IndefR.DatumF.symplOF σ JS JT ξ₀ w w' = GlobalTheory.ThetaTransform.symV (e w) (e w')) →
        (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F,
          e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
        ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f →
          ∃ Φ ∈ GlobalTheory.WeilM.schA F (Fin N), GlobalTheory.ThetaTransform.thV B.ψ Φ ∘ e = f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd N e he hrat f hf
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := hstd.1
  obtain ⟨hc, hcs, hfin, hinf⟩ := GlobalTheory.T.adelicLinearCoordinates_continuous_finite_real_points F E nS nT N e
  obtain ⟨lam, ν, hC⟩ := GlobalTheory.SWQ.ctx_exists F hR B.ψ hψ N (half F N) half_ne_zero
  obtain ⟨-, -, -, ⟨K, hK, hKc⟩, 𝓓, -, hD, h1⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hC.2.2.2.1
  have hsymm : ∀ (u : VA F N) (g : WOF F E nS nT → ℂ),
      heisV B.ψ u (g ∘ e.symm) = heisOF σ JS JT ξ₀ B.ψ (e.symm u) g ∘ e.symm :=
    fun u g => heisV_comp_symm B.ψ he u g
  have hquasi : ∀ g, IsThetaFunOF σ JS JT ξ₀ B.ψ g → QuasiV B.ψ (g ∘ e.symm) := by
    intro g hg a b w
    obtain ⟨x, hx⟩ := GlobalTheory.T.adelicLinearCoordinates_rational_surjective_of_CM F E nS nT N e hrat a b
    have hx' : e.symm (rat a, rat b) = ratWF x := by rw [← hx]; exact e.symm_apply_apply _
    simp only [Function.comp_apply, map_add, hx', hg.quasi, symplOHF, he, hx, LinearEquiv.apply_symm_apply,
      algebraMap_half]
  have hbdd : ∀ g : VA F N → ℂ, Continuous g → QuasiV B.ψ g → ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    intro g hg hq
    obtain ⟨C, hC'⟩ := (hK.prod hK).exists_bound_of_continuousOn hg.continuousOn
    refine ⟨C, fun w => ?_⟩
    obtain ⟨a, ha⟩ := hKc w.1
    obtain ⟨b, hb⟩ := hKc w.2
    have e1 : w = (rat a, rat b) + (w.1 - rat a, w.2 - rat b) :=
      Prod.ext (by simp) (by simp)
    rw [e1, hq, norm_mul, hψ.2.1, one_mul]
    exact hC' _ ⟨ha, hb⟩
  let 𝒱 : Set (VA F N → ℂ) := {g | ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ g = f ∘ e.symm}
  have hV : ∀ g ∈ 𝒱, Continuous g ∧ QuasiV B.ψ g ∧ ∃ C : ℝ, ∀ w, ‖g w‖ ≤ C := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨hg.cont.comp hcs, hquasi g hg, hbdd _ (hg.cont.comp hcs) (hquasi g hg)⟩
  have hder : ∀ g ∈ 𝒱, ∀ M : ℝ →+ VA F N, IsRealLine M → ∃ g' ∈ 𝒱, ∀ x,
      HasDerivAt (fun t : ℝ => invV B.ψ ν 𝓓 (heisV B.ψ (M t) g) x) (invV B.ψ ν 𝓓 g' x) 0 := by
    rintro _ ⟨g, hg, rfl⟩ M hM
    let L : ℝ →+ WOF F E nS nT := e.symm.toLinearMap.toAddMonoidHom.comp M
    have hL : Continuous L := hcs.comp hM.1
    have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => (hfin _).2 (by
      have : e (L t) = M t := e.apply_symm_apply _
      rw [this]; exact hM.2 t)
    let g' : WOF F E nS nT → ℂ := fun w => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) 0
    have hlev' : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u g' = g' := by
      obtain ⟨U, hUo, hU⟩ := hg.level
      exact ⟨U, hUo, fun u hu h0 =>
        GlobalTheory.T.deriv_heisenbergCM_real_line_finite_invariant F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g L hL hL0 u h0 (hU u hu h0)⟩
    have hsm' := GlobalTheory.T.contDiff_deriv_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0
    have hg' : IsThetaFunOF σ JS JT ξ₀ B.ψ g' :=
      ⟨GlobalTheory.T.deriv_heisenbergCM_theta_quasiInvariant_rational F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0, hlev',
        GlobalTheory.T.theta_lift_standard_character_indefinite F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g' hlev' hsm', hsm'⟩
    have hds : ∀ w s, HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w)
        (heisOF σ JS JT ξ₀ B.ψ (L s) g' w) s := by
      intro w s
      have h1' : HasDerivAt (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w)
          (heisOF σ JS JT ξ₀ B.ψ (L s) g' w) 0 := by
        have e2 : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w) = fun t =>
            B.ψ (symplOHF σ JS JT ξ₀ w (L s)) * heisOF σ JS JT ξ₀ B.ψ (L t) g (w + L s) :=
          funext fun t => GlobalTheory.T.heisenbergOp_realLine_add_eq_phase_mul_shifted F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd L hL hL0 g w s t
        rw [e2]
        exact ((GlobalTheory.T.differentiableAt_zero_heisenbergCM_real_line_theta F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ hσξ hstd g hg L hL hL0 (w + L s)).hasDerivAt).const_mul _
      have h2 := HasDerivAt.comp_sub_const s s (by rwa [sub_self])
        (f := fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L (s + t)) g w)
      have e3 : (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g w) =
          fun x => heisOF σ JS JT ξ₀ B.ψ (L (s + (x - s))) g w := by
        funext x; rw [add_sub_cancel]
      rw [e3]
      exact h2
    refine ⟨_, ⟨g', hg', rfl⟩, ?_⟩
    obtain ⟨c1, -, C₁, hC₁⟩ := hV _ ⟨g, hg, rfl⟩
    obtain ⟨c2, -, C₂, hC₂⟩ := hV _ ⟨g', hg', rfl⟩
    refine GlobalTheory.T.hasDerivAt_inverseThetaTransform_heisenberg_oneParam F N B.ψ lam ν hC 𝓓 hD h1 _ _ (max C₁ C₂) c1 c2 (fun w => (hC₁ w).trans (le_max_left _ _))
      (fun w => (hC₂ w).trans (le_max_right _ _)) M hM.1 fun w s => ?_
    simp only [hsymm, Function.comp_apply]
    exact hds (e.symm w) s
  have hmem : f ∘ e.symm ∈ 𝒱 := ⟨f, hf, rfl⟩
  have hlev : LevelV B.ψ (f ∘ e.symm) := by
    obtain ⟨U, hUo, hU⟩ := hf.level
    refine ⟨U.comap e.symm.toLinearMap.toAddMonoidHom, hUo.preimage hcs, fun u hu h0 h0' => ?_⟩
    rw [hsymm, hU (e.symm u) hu ((hinf _).2 (by rw [e.apply_symm_apply]; exact ⟨h0, h0'⟩))]
  obtain ⟨hl, hs⟩ := GlobalTheory.T.inverseThetaTransform_has_level_compact_finite_support F N B.ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).2.1 hlev
  have hS : invV B.ψ ν 𝓓 (f ∘ e.symm) ∈ GlobalTheory.WeilM.schA F (Fin N) :=
    GlobalTheory.T.mem_adelicSchwartzSpace_of_level_compact_schwartz F N _ hl hs (GlobalTheory.T.schwartz_inverse_theta_transform_on_real_translates F N B.ψ lam ν hC 𝓓 hD h1 𝒱 hV hder
      (GlobalTheory.T.inverseAdelicThetaTransform_rapid_decay F N B.ψ lam ν hC 𝓓 hD h1 𝒱 (fun g hg => (hV g hg).2) hder) _ hmem)
  refine ⟨_, hS, ?_⟩
  rw [GlobalTheory.T.thetaTransform_inverseTransform_eq_quasiPeriodic F N B.ψ lam ν hC 𝓓 hD h1 _ (hV _ hmem).1 (hV _ hmem).2.1 (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N _ hS)]
  funext w
  simp

end GlobalTheory.ThetaOntoF

end
