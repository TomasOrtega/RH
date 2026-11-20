import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDualityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguezStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomDictionaryFramesExponentsKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteChainFrameBottomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegralFiniteRelationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchingTripleSignatureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleMatchExistenceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.BottomFactor

open GlobalTheory.SquareComm in
/- English proof (translation)
Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, Ψ, hΨ, rfl⟩`. Simplify using `[map_sub, h u hu Ψ hΨ]`.
-/
theorem finRel_le_ker {D : D7} {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {S : Submodule ℂ (WO M X → ℂ)} {Pi : Type} [AddCommGroup Pi]
    [Module ℂ Pi] (p : (WO M X → ℂ) →ₗ[ℂ] Pi) (h : ∀ g ∈ GfC M, ∀ Φ ∈ S, p (ω (g, 1) Φ) = p Φ) : finRel ω S ≤ LinearMap.ker p := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
  simp [map_sub, h u hu Ψ hΨ]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)`. Introduce `h0`.

Use `congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this`. Conclude with `hx ((smul_eq_zero.1 this).resolve_left hφ)`.
-/
theorem tmul_ne_zero' {Pr Pf : Type} [AddCommGroup Pr] [Module ℂ Pr] [AddCommGroup Pf] [Module ℂ Pf] {x : Pr} {y : Pf}
    (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℂ] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ Pf, φ y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hy ((Module.forall_dual_apply_eq_zero_iff ℂ y).1 hc)
  intro h0
  have := congrArg ((TensorProduct.rid ℂ Pr).toLinearMap ∘ₗ LinearMap.lTensor Pr φ) h0
  simp only [LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, TensorProduct.rid_tmul, map_zero] at this
  exact hx ((smul_eq_zero.1 this).resolve_left hφ)

/- English proof (translation)
Simplify using `[thetaKO, map_smul]`.
-/
theorem thetaKO_smul {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    (c : ℂ) (f : WO S T → ℂ) : thetaKO om g h (c • f) = c * thetaKO om g h f := by
  simp [thetaKO, map_smul]

/- English proof (translation)
Simplify using `[thetaKO, map_sub]`.
-/
theorem thetaKO_sub {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    (f f' : WO S T → ℂ) : thetaKO om g h (f - f') = thetaKO om g h f - thetaKO om g h f' := by
  simp [thetaKO, map_sub]

/- English proof (translation)
Simplify using `[thetaKO, map_add]`.
-/
theorem thetaKO_add {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    (f f' : WO S T → ℂ) : thetaKO om g h (f + f') = thetaKO om g h f + thetaKO om g h f' := by
  simp [thetaKO, map_add]

/- English proof (translation)
Simplify using `[thetaKO]`.
-/
theorem thetaKO_zero {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T) :
    thetaKO om g h 0 = 0 := by
  simp [thetaKO]

open GlobalTheory.SquareComm in

/- English proof (translation)
Introduce `hH hP hK hM _`. Establish `hLM` using `GlobalTheory.T.local_matching_of_howe_duality hH hP hK hM`. Establish `hTA` using `GlobalTheory.T.theta_integrals_of_minguez hP.minguezThetaGL hP hK hM`. Take `⟨CF1, H1⟩` from `GlobalTheory.T.definiteBottom_dictionary_frames_exponents_kernel`. Take `⟨CF2, H2⟩` from `GlobalTheory.T.finite_chain_frame_bottom hH hP hK hM`.

Use `⟨max CF1 CF2, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C1, x1, G1⟩` from `H1 ε CF (le_trans (le_max_left _ _) hCF)`. Take `⟨C2, x2, G2⟩` from `H2 ε CF (le_trans (le_max_right _ _) hCF)`. Use `⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W i j A A' WW X hX => ?_⟩` and prove the remaining obligations. Take `⟨FA, FA', FW, a, b, hdA, hdef, hdW, hD⟩` from `G1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX`.

Establish `hF` using `G2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX`. Take `⟨Pr, q, q', hq, hq', hLMt⟩` from `hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b`. Establish `eI : ∀ t P, thetaInt (X.ω t) X.m X.fd (fockF W.ψ W.θ true FA FW (X.f t) P) = X.I W.ψ W.θ t P` using `fun t P => by`. Use function extensionality and compare the values at `h`. Simplify using `only [thetaInt, Tri.I, (hD t).2.2.2.2.1]`.

Establish `eI' : ∀ t P, thetaInt (X.ω' t) X.m' X.fd' (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.I' W.ψ W.θ t P` using `fun t P => by`. Use function extensionality and compare the values at `h`. Simplify using `only [thetaInt, Tri.I', (hD t).2.2.2.2.2]`. Establish `iI' : ∀ t P h, IntegrableOn (fun g => thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P)) X.fd' X.m'` using `fun t P h => by simp only [(hD t).2.2.2.2.2]; exact (hX.integrable t).2 P h`. Establish `key : ∀ t, (∀ P', q' P' = 0 → X.I' W.ψ W.θ t P' = 0) ∧ ((∀ P', X.I' W.ψ W.θ t P' = 0) ∨ ∀ P', X.I' W.ψ W.θ t P' = 0 → q' P' = 0) ∧ (∃ lam : ℂ, ∀ P P', q P = q' P' → X.I W.ψ W.θ t P = lam • X.I' W.ψ W.θ t P') ∧ Nontrivial Pr`.

Introduce `t`. Take `⟨hTr, hInf, hf, hf', -, -⟩` from `hD t`. Take `⟨hex, hfac⟩` from `hLMt _ _ hTr hInf`. Take `⟨Pm, rf, rl, p, p', hm⟩` from `GlobalTheory.T.triple_match_existence hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex (X.ω t) (X.ω' t) (hX.is.weil t) (hX.is.weil' t)`. Take `⟨Pf, r, r', e, -, -, hr, hr'⟩` from `hfac _ _ _ _ _ _ _ hm`.

Take `⟨c, hc0, hc⟩` from `hTA D W.ψ W.θ W.θ_is A A' WW FA FA' FW _ _ hTr X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas' (X.ω t) (X.ω' t) Pm rf rl p p' hm`. Establish `hrel` using `GlobalTheory.T.theta_integral_finite_relation hP D W.ψ W.θ W.ψ_std W.θ_is A' WW FA' FW _ _ (X.ω' t) (hX.is.weil' t) hdef X.m' X.fd' hX.is.meas'`. Establish `kerp'` using `finRel_le_ker p' hm.mapB.invf`. Establish `memF : ∀ P', fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ algF W.ψ W.θ false FA' FW` using `fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩`. Establish `same : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') → ∀ Φ₀, Ψ - Φ₀ ∈ finRel (X.ω' t) (algF W.ψ W.θ false FA' FW) → ModInt W.θ (X.ω' t) X.m' X.fd' Φ₀ → thetaInt (X.ω' t) X.m' X.fd' Ψ = thetaInt (X.ω' t) X.m' X.fd' Φ₀`.

Introduce `Ψ _ hΨ Φ₀ hd hmod`. Take `⟨N, K, hmod⟩` from `hmod`. Use function extensionality and compare the values at `h`. Establish `h0` using `congrFun (hrel _ hd) h`. Simplify using `only [thetaInt, thetaKO_sub] at h0 ⊢`.

Rewrite `h0` using `[integral_sub (hΨ h) (hmod h).1]`. Conclude with `sub_eq_zero.1 h0`. Establish `kill : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') → p' Ψ = 0 → thetaInt (X.ω' t) X.m' X.fd' Ψ = 0`. Introduce `Ψ hΨ hi hp`. Take `⟨Φ₀, hΦ₀, hd, hmod, hI⟩` from `hc Ψ hΨ`.

Establish `hp0 : p' Φ₀ = 0`. Use `kerp' hd` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, map_sub, hp, zero_sub, neg_eq_zero]`. Conclude with `this`. Establish `h1` using `hI 0 (zero_mem _) (by rw [map_zero, hp0])`.

Establish `h2 : thetaInt (X.ω t) X.m X.fd 0 = 0` using `by funext h; simp [thetaInt, thetaKO_zero]`. Rewrite `h1` using `[h2]`. Rewrite using `[same Ψ hΨ hi Φ₀ hd hmod]`. Conclude with `((smul_eq_zero.1 h1.symm).resolve_left hc0)`. Establish `hp'F : ∀ P', p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') = e (q' P' ⊗ₜ r' (X.f' t))` using `hr' _ hf'`.

Use `⟨fun P' h0 => ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← eI']`. Conclude with `kill _ (memF P') (iI' t P') (by rw [hp'F, h0, TensorProduct.zero_tmul, map_zero])`. Distinguish the cases in `hall : ∀ P', X.I' W.ψ W.θ t P' = 0`. Conclude with `Or.inl hall`.

Use `Or.inr fun P' h0 => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hq0`. Use `hall fun P'' => ?_` and prove the remaining obligations. Rewrite using `[← eI']`. Distinguish the cases in `hy : r' (X.f' t) = 0`.

Conclude with `kill _ (memF P'') (iI' t P'') (by rw [hp'F, hy, TensorProduct.tmul_zero, map_zero])`. Establish `hne : p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0`. Rewrite using `[hp'F]`. Conclude with `e.map_ne_zero_iff.2 (tmul_ne_zero' hq0 hy)`. Conclude with `GlobalTheory.T.matching_triple_signature hH hP hK hM hTA D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdA hdef hdW X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas' (X.ω t) (X.ω' t) Pm rf rl p p' hm _ (memF P') hne (by rw [eI']; exact h0) _ (memF P'')`.

Take `⟨κ, hκ⟩` from `hF FA FA' FW t hf hf' Pm rf rl p p' hm Pr Pf q q' r r' e hq hq' hr hr'`. Use `⟨c * κ, fun P P' hPP => ?_⟩` and prove the remaining obligations. Use `set Ψ := κ • fockF W.ψ W.θ false FA' FW (X.f' t) P' with hΨdef`. Establish `hΨ : Ψ ∈ algF W.ψ W.θ false FA' FW` using `Submodule.smul_mem _ _ (memF P')`. Establish `hΨi : ∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m'` using `fun h => by`.

Simplify using `only [hΨdef, thetaKO_smul]`. Conclude with `(iI' t P' h).const_mul κ`. Take `⟨Φ₀, -, hd, hmod, hI⟩` from `hc Ψ hΨ`. Establish `hpp : p (fockF W.ψ W.θ true FA FW (X.f t) P) = p' Φ₀`. Establish `h1 : p' Φ₀ = p' Ψ`.

Use `kerp' hd` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Conclude with `this.symm`. Rewrite using `[h1, hΨdef, map_smul, hp'F, hr _ hf, hκ, hPP, TensorProduct.tmul_smul, map_smul]`. Establish `h2` using `hI _ (Submodule.subset_span ⟨_, P, hf, rfl⟩) hpp`.

Rewrite `h2` using `[eI, ← same Ψ hΨ hΨi Φ₀ hd hmod]`. Rewrite using `[h2, ← eI', mul_smul]`. Use `congr 1`. Use function extensionality and compare the values at `h`. Simplify using `[hΨdef, thetaInt, thetaKO_smul, integral_const_mul]`.

Take `⟨hnt, -⟩` from `hm.irred`. Assume the negation of the conclusion as `hP0`. Rewrite `hP0` using `[not_nontrivial_iff_subsingleton]`. Establish `hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => rfl`. Consider the case `tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`. Take `⟨u, v, huv⟩` from `hnt.exists_pair_ne`. Conclude with `huv (by rw [← e.apply_symm_apply u, ← e.apply_symm_apply v, hz (e.symm u), hz (e.symm v)])`.

Use `choose hker hirr hlam hnt using key`. Set `Il : T → PolF D WW.rank A'.rank →ₗ[ℂ] (GA D WW → ℂ)` to `fun t => { toFun := fun P' => X.I' W.ψ W.θ t P' map_add' := fun P Q => by show X.I' W.ψ W.θ t (P + Q) = X.I' W.ψ W.θ t P + X.I' W.ψ W.θ t Q`. Rewrite using `[← eI', ← eI', ← eI', map_add]`. Use function extensionality and compare the values at `h`. Simplify using `only [thetaInt, thetaKO_add, Pi.add_apply]`.

Conclude with `integral_add (iI' t P h) (iI' t Q h)`. Use the proof step `map_smul' := fun c P => by show X.I' W.ψ W.θ t (c • P) = c • X.I' W.ψ W.θ t P`. Rewrite using `[← eI', ← eI', map_smul]`. Use function extensionality and compare the values at `h`. Simplify using `[thetaInt, thetaKO_smul, integral_const_mul] }`.

Establish `hK : ∀ t, LinearMap.ker q' ≤ LinearMap.ker (Il t)` using `fun t P' h0 => hker t P' h0`. Set `J : T → (Pr →ₗ[ℂ] (GA D WW → ℂ))` to `fun t => ((LinearMap.ker q').liftQ (Il t) (hK t)) ∘ₗ (q'.quotKerEquivOfSurjective hq').symm.toLinearMap`. Establish `hJ : ∀ t P', J t (q' P') = X.I' W.ψ W.θ t P'` using `fun t P' => by`. Establish `: (q'.quotKerEquivOfSurjective hq').symm (q' P') = Submodule.Quotient.mk P'`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Conclude with `(LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm`. Simplify using `only [J, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]`. Both sides reduce to the same expression. Use `haveI := hnt μ₀`. Take `⟨x, hx⟩` from `exists_ne (0 : Pr)`.

Take `⟨P0, rfl⟩` from `hq' x`. Use `⟨Pr, q, q', J, hq, ⟨P0, hx⟩, fun t => ?_, fun t => ?_, fun t P' => (hJ t P').symm⟩` and prove the remaining obligations. Break down `hirr t with h | h` into its components or cases. Use `left`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Take `⟨P', rfl⟩` from `hq' x`. Rewrite using `[hJ, h P']`. Both sides reduce to the same expression. Use `right`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce `x hx0`. Take `⟨P', rfl⟩` from `hq' x`. Rewrite `hx0` using `[hJ]`. Conclude with `h P' hx0`. Take `⟨lam, hl⟩` from `hlam t`.

Use `⟨lam, fun P => ?_⟩` and prove the remaining obligations. Take `⟨P', hP'⟩` from `hq' (q P)`. Rewrite using `[← hP', hJ]`. Conclude with `hl P P' hP'.symm`.
-/
theorem factor : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe →
    GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW), IsBottomTri W i j X →
      ∃ (Pi : ModuleCat.{0} ℂ) (p : PolF D WW.rank A.rank →ₗ[ℂ] Pi) (p' : PolF D WW.rank A'.rank →ₗ[ℂ] Pi)
        (J : T → (Pi →ₗ[ℂ] (GA D WW → ℂ))), Function.Surjective p ∧ (∃ P', p' P' ≠ 0) ∧
        (∀ t, J t = 0 ∨ Function.Injective (J t)) ∧ (∀ t, ∃ lam : ℂ, ∀ P, X.I W.ψ W.θ t P = lam • J t (p P)) ∧
        ∀ t P', X.I' W.ψ W.θ t P' = J t (p' P') := by
  intro hH hP hK hM _
  have hLM := GlobalTheory.T.local_matching_of_howe_duality hH hP hK hM
  have hTA := GlobalTheory.T.theta_integrals_of_minguez hP.minguezThetaGL hP hK hM
  obtain ⟨CF1, H1⟩ := GlobalTheory.T.definiteBottom_dictionary_frames_exponents_kernel
  obtain ⟨CF2, H2⟩ := GlobalTheory.T.finite_chain_frame_bottom hH hP hK hM
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, G1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, G2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W i j A A' WW X hX => ?_⟩
  obtain ⟨FA, FA', FW, a, b, hdA, hdef, hdW, hD⟩ :=
    G1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  have hF := G2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b

  have eI : ∀ t P, thetaInt (X.ω t) X.m X.fd (fockF W.ψ W.θ true FA FW (X.f t) P) = X.I W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I, (hD t).2.2.2.2.1]
  have eI' : ∀ t P, thetaInt (X.ω' t) X.m' X.fd' (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.I' W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I', (hD t).2.2.2.2.2]
  have iI' : ∀ t P h, IntegrableOn (fun g => thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P)) X.fd' X.m' :=
    fun t P h => by simp only [(hD t).2.2.2.2.2]; exact (hX.integrable t).2 P h

  have key : ∀ t, (∀ P', q' P' = 0 → X.I' W.ψ W.θ t P' = 0) ∧
      ((∀ P', X.I' W.ψ W.θ t P' = 0) ∨ ∀ P', X.I' W.ψ W.θ t P' = 0 → q' P' = 0) ∧
      (∃ lam : ℂ, ∀ P P', q P = q' P' → X.I W.ψ W.θ t P = lam • X.I' W.ψ W.θ t P') ∧ Nontrivial Pr := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, -⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, p, p', hm⟩ := GlobalTheory.T.triple_match_existence hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex (X.ω t) (X.ω' t)
      (hX.is.weil t) (hX.is.weil' t)
    obtain ⟨Pf, r, r', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    obtain ⟨c, hc0, hc⟩ := hTA D W.ψ W.θ W.θ_is A A' WW FA FA' FW _ _ hTr X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas'
      (X.ω t) (X.ω' t) Pm rf rl p p' hm
    have hrel := GlobalTheory.T.theta_integral_finite_relation hP D W.ψ W.θ W.ψ_std W.θ_is A' WW FA' FW _ _ (X.ω' t) (hX.is.weil' t) hdef X.m' X.fd' hX.is.meas'
    have kerp' := finRel_le_ker p' hm.mapB.invf
    have memF : ∀ P', fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ algF W.ψ W.θ false FA' FW :=
      fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩

    have same : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') →
        ∀ Φ₀, Ψ - Φ₀ ∈ finRel (X.ω' t) (algF W.ψ W.θ false FA' FW) → ModInt W.θ (X.ω' t) X.m' X.fd' Φ₀ →
        thetaInt (X.ω' t) X.m' X.fd' Ψ = thetaInt (X.ω' t) X.m' X.fd' Φ₀ := by
      intro Ψ _ hΨ Φ₀ hd hmod
      obtain ⟨N, K, hmod⟩ := hmod
      funext h
      have h0 := congrFun (hrel _ hd) h
      simp only [thetaInt, thetaKO_sub] at h0 ⊢
      rw [integral_sub (hΨ h) (hmod h).1] at h0
      exact sub_eq_zero.1 h0

    have kill : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') →
        p' Ψ = 0 → thetaInt (X.ω' t) X.m' X.fd' Ψ = 0 := by
      intro Ψ hΨ hi hp
      obtain ⟨Φ₀, hΦ₀, hd, hmod, hI⟩ := hc Ψ hΨ
      have hp0 : p' Φ₀ = 0 := by
        have := kerp' hd
        rw [LinearMap.mem_ker, map_sub, hp, zero_sub, neg_eq_zero] at this
        exact this
      have h1 := hI 0 (zero_mem _) (by rw [map_zero, hp0])
      have h2 : thetaInt (X.ω t) X.m X.fd 0 = 0 := by funext h; simp [thetaInt, thetaKO_zero]
      rw [h2] at h1
      rw [same Ψ hΨ hi Φ₀ hd hmod]
      exact ((smul_eq_zero.1 h1.symm).resolve_left hc0)
    have hp'F : ∀ P', p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') = e (q' P' ⊗ₜ r' (X.f' t)) := hr' _ hf'
    refine ⟨fun P' h0 => ?_, ?_, ?_, ?_⟩
    · rw [← eI']
      exact kill _ (memF P') (iI' t P') (by rw [hp'F, h0, TensorProduct.zero_tmul, map_zero])
    · by_cases hall : ∀ P', X.I' W.ψ W.θ t P' = 0
      · exact Or.inl hall
      refine Or.inr fun P' h0 => ?_
      by_contra hq0
      refine hall fun P'' => ?_
      rw [← eI']
      by_cases hy : r' (X.f' t) = 0
      · exact kill _ (memF P'') (iI' t P'') (by rw [hp'F, hy, TensorProduct.tmul_zero, map_zero])
      · have hne : p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0 := by
          rw [hp'F]; exact e.map_ne_zero_iff.2 (tmul_ne_zero' hq0 hy)
        exact GlobalTheory.T.matching_triple_signature hH hP hK hM hTA D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdA hdef hdW X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas'
          (X.ω t) (X.ω' t) Pm rf rl p p' hm _ (memF P') hne (by rw [eI']; exact h0) _ (memF P'')
    · obtain ⟨κ, hκ⟩ := hF FA FA' FW t hf hf' Pm rf rl p p' hm Pr Pf q q' r r' e hq hq' hr hr'
      refine ⟨c * κ, fun P P' hPP => ?_⟩
      set Ψ := κ • fockF W.ψ W.θ false FA' FW (X.f' t) P' with hΨdef
      have hΨ : Ψ ∈ algF W.ψ W.θ false FA' FW := Submodule.smul_mem _ _ (memF P')
      have hΨi : ∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m' := fun h => by
        simp only [hΨdef, thetaKO_smul]; exact (iI' t P' h).const_mul κ
      obtain ⟨Φ₀, -, hd, hmod, hI⟩ := hc Ψ hΨ
      have hpp : p (fockF W.ψ W.θ true FA FW (X.f t) P) = p' Φ₀ := by
        have h1 : p' Φ₀ = p' Ψ := by
          have := kerp' hd
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
          exact this.symm
        rw [h1, hΨdef, map_smul, hp'F, hr _ hf, hκ, hPP, TensorProduct.tmul_smul, map_smul]
      have h2 := hI _ (Submodule.subset_span ⟨_, P, hf, rfl⟩) hpp
      rw [eI, ← same Ψ hΨ hΨi Φ₀ hd hmod] at h2
      rw [h2, ← eI', mul_smul]
      congr 1
      funext h
      simp [hΨdef, thetaInt, thetaKO_smul, integral_const_mul]
    · obtain ⟨hnt, -⟩ := hm.irred
      by_contra hP0
      rw [not_nontrivial_iff_subsingleton] at hP0
      have hz : ∀ z : Pr ⊗[ℂ] Pf, z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
        | add x y hx hy => rw [hx, hy, add_zero]
      obtain ⟨u, v, huv⟩ := hnt.exists_pair_ne
      exact huv (by rw [← e.apply_symm_apply u, ← e.apply_symm_apply v, hz (e.symm u), hz (e.symm v)])
  choose hker hirr hlam hnt using key
  let Il : T → PolF D WW.rank A'.rank →ₗ[ℂ] (GA D WW → ℂ) := fun t =>
    { toFun := fun P' => X.I' W.ψ W.θ t P'
      map_add' := fun P Q => by
        show X.I' W.ψ W.θ t (P + Q) = X.I' W.ψ W.θ t P + X.I' W.ψ W.θ t Q
        rw [← eI', ← eI', ← eI', map_add]; funext h
        simp only [thetaInt, thetaKO_add, Pi.add_apply]
        exact integral_add (iI' t P h) (iI' t Q h)
      map_smul' := fun c P => by
        show X.I' W.ψ W.θ t (c • P) = c • X.I' W.ψ W.θ t P
        rw [← eI', ← eI', map_smul]; funext h
        simp [thetaInt, thetaKO_smul, integral_const_mul] }
  have hK : ∀ t, LinearMap.ker q' ≤ LinearMap.ker (Il t) := fun t P' h0 => hker t P' h0
  let J : T → (Pr →ₗ[ℂ] (GA D WW → ℂ)) := fun t =>
    ((LinearMap.ker q').liftQ (Il t) (hK t)) ∘ₗ (q'.quotKerEquivOfSurjective hq').symm.toLinearMap
  have hJ : ∀ t P', J t (q' P') = X.I' W.ψ W.θ t P' := fun t P' => by
    have : (q'.quotKerEquivOfSurjective hq').symm (q' P') = Submodule.Quotient.mk P' := by
      rw [LinearEquiv.symm_apply_eq]; exact (LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm
    simp only [J, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]; rfl
  haveI := hnt μ₀
  obtain ⟨x, hx⟩ := exists_ne (0 : Pr)
  obtain ⟨P0, rfl⟩ := hq' x
  refine ⟨Pr, q, q', J, hq, ⟨P0, hx⟩, fun t => ?_, fun t => ?_, fun t P' => (hJ t P').symm⟩
  · rcases hirr t with h | h
    · left; refine LinearMap.ext fun x => ?_; obtain ⟨P', rfl⟩ := hq' x; rw [hJ, h P']; rfl
    · right; rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']; intro x hx0; obtain ⟨P', rfl⟩ := hq' x
      rw [hJ] at hx0; exact h P' hx0
  · obtain ⟨lam, hl⟩ := hlam t
    refine ⟨lam, fun P => ?_⟩
    obtain ⟨P', hP'⟩ := hq' (q P)
    rw [← hP', hJ]; exact hl P P' hP'.symm

end GlobalTheory.BottomFactor

end
