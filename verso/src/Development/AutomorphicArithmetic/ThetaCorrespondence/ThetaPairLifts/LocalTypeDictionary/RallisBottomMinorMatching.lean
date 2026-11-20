import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantTripleCoefficient
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareThetaIntegralsEq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaBottomFinitePlaceMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomDegreeMatchRealQuotient
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleWeilTransferMatching
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralVanishesOnFiniteRelations
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftVanishesOfIrreducibleDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantTripleCoefficientStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.BotMatch
set_option maxHeartbeats 1000000 in
open GlobalTheory.SqTop GlobalTheory.SquareComm in
/- English proof (translation)
Introduce `hP hK hM _ _`. Establish `hH : GlobalTheory.Published.HoweDualityReal` using `hP.howeDualityReal`. Establish `hLM` using `_root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hM`. Establish `hTA` using `_root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hM`. Take `⟨CF1, H1⟩` from `GlobalTheory.T.definiteBottom_dictionary_frames_exponents_kernel`.

Take `⟨CF2, H2⟩` from `_root_.GlobalTheory.T.theta_bottom_finite_place_matching hH hP hK hM`. Use `⟨max CF1 CF2, fun ε CF hCF => ?_⟩` and prove the remaining obligations. Take `⟨C1, x1, G1⟩` from `H1 ε CF (le_trans (le_max_left _ _) hCF)`. Take `⟨C2, x2, G2⟩` from `H2 ε CF (le_trans (le_max_right _ _) hCF)`. Use `⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W _ i j A A' WW X c0 hX hc => ?_⟩` and prove the remaining obligations.

Take `⟨FA, FA', FW, a, b, hdA, hdef, hdW, hD⟩` from `G1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX`. Establish `hF` using `G2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX`. Take `⟨Pr, q, q', hq, hq', hLMt⟩` from `hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b`. Take `⟨ρ, hρ, hrel⟩` from `_root_.GlobalTheory.T.bottom_degree_match_real_quotient hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b hX.is.rank hdA hdef hdW ⟨_, _, (hD μ₀).1, (hD μ₀).2.1⟩ Pr q q' hq hq' hLMt`. Use `choose εf hεf using hrel`.

Establish `eI : ∀ t P, thetaInt (X.ω t) X.m X.fd (fockF W.ψ W.θ true FA FW (X.f t) P) = X.I W.ψ W.θ t P` using `fun t P => by`. Use function extensionality and compare the values at `h`. Simplify using `only [thetaInt, Tri.I, (hD t).2.2.2.2.1]`. Establish `eI' : ∀ t P, thetaInt (X.ω' t) X.m' X.fd' (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.I' W.ψ W.θ t P` using `fun t P => by`. Use function extensionality and compare the values at `h`.

Simplify using `only [thetaInt, Tri.I', (hD t).2.2.2.2.2]`. Establish `iI' : ∀ t P h, IntegrableOn (fun g => thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P)) X.fd' X.m'` using `fun t P h => by simp only [(hD t).2.2.2.2.2]; exact (hX.integrable t).2 P h`. Establish `key : ∀ t, (∀ P', q' P' = 0 → X.I' W.ψ W.θ t P' = 0) ∧ ((∀ P', X.I' W.ψ W.θ t P' = 0) ∨ ∀ P', X.I' W.ψ W.θ t P' = 0 → q' P' = 0) ∧ (∃ lam : ℂ, ∀ P P', q P = q' P' → X.I W.ψ W.θ t P = lam • X.I' W.ψ W.θ t P')`. Introduce `t`. Take `⟨hTr, hInf, hf, hf', -, -⟩` from `hD t`.

Take `⟨hex, hfac⟩` from `hLMt _ _ hTr hInf`. Take `⟨Pm, rf, rl, p, p', hm⟩` from `_root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex (X.ω t) (X.ω' t) (hX.is.weil t) (hX.is.weil' t)`. Take `⟨Pf, r, r', e, -, -, hr, hr'⟩` from `hfac _ _ _ _ _ _ _ hm`. Take `⟨c, hc0, hc⟩` from `hTA D W.ψ W.θ W.θ_is A A' WW FA FA' FW _ _ hTr X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas' (X.ω t) (X.ω' t) Pm rf rl p p' hm`. Establish `hrel` using `_root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations hP D W.ψ W.θ W.ψ_std W.θ_is A' WW FA' FW _ _ (X.ω' t) (hX.is.weil' t) hdef X.m' X.fd' hX.is.meas'`.

Establish `kerp'` using `finRel_le_ker p' hm.mapB.invf`. Establish `memF : ∀ P', fockF W.ψ W.θ false FA' FW (X.f' t) P' ∈ algF W.ψ W.θ false FA' FW` using `fun P' => Submodule.subset_span ⟨_, P', hf', rfl⟩`. Establish `same : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') → ∀ Φ₀, Ψ - Φ₀ ∈ finRel (X.ω' t) (algF W.ψ W.θ false FA' FW) → ModInt W.θ (X.ω' t) X.m' X.fd' Φ₀ → thetaInt (X.ω' t) X.m' X.fd' Ψ = thetaInt (X.ω' t) X.m' X.fd' Φ₀`. Introduce `Ψ _ hΨ Φ₀ hd hmod`. Take `⟨N, K, hmod⟩` from `hmod`.

Use function extensionality and compare the values at `h`. Establish `h0` using `congrFun (hrel _ hd) h`. Simplify using `only [thetaInt, thetaKO_sub] at h0 ⊢`. Rewrite `h0` using `[integral_sub (hΨ h) (hmod h).1]`. Conclude with `sub_eq_zero.1 h0`.

Establish `kill : ∀ Ψ ∈ algF W.ψ W.θ false FA' FW, (∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m') → p' Ψ = 0 → thetaInt (X.ω' t) X.m' X.fd' Ψ = 0`. Introduce `Ψ hΨ hi hp`. Take `⟨Φ₀, hΦ₀, hd, hmod, hI⟩` from `hc Ψ hΨ`. Establish `hp0 : p' Φ₀ = 0`. Use `kerp' hd` as an intermediate fact.

Rewrite `this` using `[LinearMap.mem_ker, map_sub, hp, zero_sub, neg_eq_zero]`. Conclude with `this`. Establish `h1` using `hI 0 (zero_mem _) (by rw [map_zero, hp0])`. Establish `h2 : thetaInt (X.ω t) X.m X.fd 0 = 0` using `by funext h; simp [thetaInt, thetaKO_zero]`. Rewrite `h1` using `[h2]`.

Rewrite using `[same Ψ hΨ hi Φ₀ hd hmod]`. Conclude with `((smul_eq_zero.1 h1.symm).resolve_left hc0)`. Establish `hp'F : ∀ P', p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') = e (q' P' ⊗ₜ r' (X.f' t))` using `hr' _ hf'`. Use `⟨fun P' h0 => ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← eI']`.

Conclude with `kill _ (memF P') (iI' t P') (by rw [hp'F, h0, TensorProduct.zero_tmul, map_zero])`. Distinguish the cases in `hall : ∀ P', X.I' W.ψ W.θ t P' = 0`. Conclude with `Or.inl hall`. Use `Or.inr fun P' h0 => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hq0`.

Use `hall fun P'' => ?_` and prove the remaining obligations. Rewrite using `[← eI']`. Distinguish the cases in `hy : r' (X.f' t) = 0`. Conclude with `kill _ (memF P'') (iI' t P'') (by rw [hp'F, hy, TensorProduct.tmul_zero, map_zero])`. Establish `hne : p' (fockF W.ψ W.θ false FA' FW (X.f' t) P') ≠ 0`.

Rewrite using `[hp'F]`. Conclude with `e.map_ne_zero_iff.2 (tmul_ne_zero' hq0 hy)`. Conclude with `_root_.GlobalTheory.T.theta_lift_vanishes_of_irreducible_defect hH hP hK hM hTA D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdA hdef hdW X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas' (X.ω t) (X.ω' t) Pm rf rl p p' hm _ (memF P') hne (by rw [eI']; exact h0) _ (memF P'')`. Take `⟨κ, hκ⟩` from `hF FA FA' FW t hf hf' Pm rf rl p p' hm Pr Pf q q' r r' e hq hq' hr hr'`. Use `⟨c * κ, fun P P' hPP => ?_⟩` and prove the remaining obligations.

Use `set Ψ := κ • fockF W.ψ W.θ false FA' FW (X.f' t) P' with hΨdef`. Establish `hΨ : Ψ ∈ algF W.ψ W.θ false FA' FW` using `Submodule.smul_mem _ _ (memF P')`. Establish `hΨi : ∀ h, IntegrableOn (fun g => thetaKO (X.ω' t) g h Ψ) X.fd' X.m'` using `fun h => by`. Simplify using `only [hΨdef, thetaKO_smul]`. Conclude with `(iI' t P' h).const_mul κ`.

Take `⟨Φ₀, -, hd, hmod, hI⟩` from `hc Ψ hΨ`. Establish `hpp : p (fockF W.ψ W.θ true FA FW (X.f t) P) = p' Φ₀`. Establish `h1 : p' Φ₀ = p' Ψ`. Use `kerp' hd` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`.

Conclude with `this.symm`. Rewrite using `[h1, hΨdef, map_smul, hp'F, hr _ hf, hκ, hPP, TensorProduct.tmul_smul, map_smul]`. Establish `h2` using `hI _ (Submodule.subset_span ⟨_, P, hf, rfl⟩) hpp`. Rewrite `h2` using `[eI, ← same Ψ hΨ hΨi Φ₀ hd hmod]`. Rewrite using `[h2, ← eI', mul_smul]`.

Use `congr 1`. Use function extensionality and compare the values at `h`. Simplify using `[hΨdef, thetaInt, thetaKO_smul, integral_const_mul]`. Use `choose hker hirr hlam using key`. Set `Il : T → PolF D WW.rank A'.rank →ₗ[ℂ] (GA D WW → ℂ)` to `fun t => { toFun := fun P' => X.I' W.ψ W.θ t P' map_add' := fun P Q => by show X.I' W.ψ W.θ t (P + Q) = X.I' W.ψ W.θ t P + X.I' W.ψ W.θ t Q`.

Rewrite using `[← eI', ← eI', ← eI', map_add]`. Use function extensionality and compare the values at `h`. Simplify using `only [thetaInt, thetaKO_add, Pi.add_apply]`. Conclude with `integral_add (iI' t P h) (iI' t Q h)`. Use the proof step `map_smul' := fun c P => by show X.I' W.ψ W.θ t (c • P) = c • X.I' W.ψ W.θ t P`.

Rewrite using `[← eI', ← eI', map_smul]`. Use function extensionality and compare the values at `h`. Simplify using `[thetaInt, thetaKO_smul, integral_const_mul] }`. Establish `hK : ∀ t, LinearMap.ker q' ≤ LinearMap.ker (Il t)` using `fun t P' h0 => hker t P' h0`. Set `J : T → (Pr →ₗ[ℂ] (GA D WW → ℂ))` to `fun t => ((LinearMap.ker q').liftQ (Il t) (hK t)) ∘ₗ (q'.quotKerEquivOfSurjective hq').symm.toLinearMap`.

Establish `hJ : ∀ t P', J t (q' P') = X.I' W.ψ W.θ t P'` using `fun t P' => by`. Establish `: (q'.quotKerEquivOfSurjective hq').symm (q' P') = Submodule.Quotient.mk P'`. Rewrite using `[LinearEquiv.symm_apply_eq]`. Conclude with `(LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _).symm`. Simplify using `only [J, LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]`.

Both sides reduce to the same expression. Establish `hJI : ∀ t, ∃ lam : ℂ, ∀ P, X.I W.ψ W.θ t P = lam • J t (q P)` using `fun t => by`. Take `⟨lam, hl⟩` from `hlam t`. Use `⟨lam, fun P => ?_⟩` and prove the remaining obligations. Take `⟨P', hP'⟩` from `hq' (q P)`.

Rewrite using `[← hP', hJ]`. Conclude with `hl P P' hP'.symm`. Use `choose lam hlamJ using hJI`. Take `⟨⟨t₁, ht₁⟩, P0, P0', hc⟩` from `hc`. Establish `hJne : ∀ t, J t (q' P0') ≠ 0` using `fun t h0 => by`.

Take `⟨h, hh⟩` from `(hc t).2.1`. Conclude with `hh (by rw [← hJ, h0]; rfl)`. Establish `hq0 : q' P0' ≠ 0` using `fun h0 => hJne t₁ (by rw [h0, map_zero])`. Establish `hinj : ∀ t, Function.Injective (J t)` using `fun t => by`. Break down `hirr t with h | h` into its components or cases.

Conclude with `absurd (by rw [hJ]; exact h P0') (hJne t)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx0`. Take `⟨P', rfl⟩` from `hq' x`. Rewrite `hx0` using `[hJ]`.

Conclude with `h P' hx0`. Establish `heq : ∀ t, lam t • q P0 = c0 t • q' P0'` using `fun t => by`. Apply `hinj t` to reduce the goal to its premises. Rewrite using `[map_smul, map_smul, ← hlamJ, hJ]`. Use function extensionality and compare the values at `h`.

Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Conclude with `(hc t).2.2 h`. Establish `hlam1 : lam t₁ ≠ 0` using `fun h0 => by`. Use `heq t₁` as an intermediate fact. Rewrite `this` using `[h0, zero_smul]`.

Conclude with `(smul_eq_zero.1 this.symm).elim ht₁ hq0`. Use `set κ := c0 t₁ / lam t₁ with hκdef`. Establish `hκ0 : κ ≠ 0` using `div_ne_zero ht₁ hlam1`. Establish `hqP0 : q P0 = κ • q' P0'`. Rewrite using `[hκdef, div_eq_inv_mul, mul_smul, ← heq t₁, smul_smul, inv_mul_cancel₀ hlam1, one_smul]`.

Establish `hlc : ∀ t, lam t = c0 t / κ` using `fun t => by`. Establish `h1` using `heq t`. Rewrite `h1` using `[hqP0, smul_smul, ← sub_eq_zero, ← sub_smul]`. Establish `h2` using `(smul_eq_zero.1 h1).resolve_right hq0`. Rewrite using `[eq_div_iff hκ0]`.

Conclude with `sub_eq_zero.1 h2`. Use `⟨ρ / κ, div_ne_zero hρ hκ0, fun s Q δ t0 P P' hB ea ea' ed ed' => ?_⟩` and prove the remaining obligations. Establish `hn : P'.n = P.n` using `GlobalTheory.T.squareBottomPairs_weights_eq G s i j _ P P' hB`. Establish `core : ∀ (a₁ a₁' d₁ d₁' : ℕ) (n n' : D.what₂.Tau → ℕ) (ea : a₁ = A.rank) (ea' : a₁' = A'.rank) (ed : d₁ = WW.rank) (ed' : d₁' = WW.rank) (hn : n' = n), ∃ (M : Tup D a₁ d₁ n → Tup D a₁' d₁' n' → ℤ) (M' : Tup D a₁' d₁' n' → Tup D a₁ d₁ n → ℤ), (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T …`. Introduce `a₁ a₁' d₁ d₁' n n' ea ea' ed ed' hn`.

Substitute `ea ea' ed ed' hn` using the available equality. Take `⟨M, M', hMM, hMf⟩` from `exists_signed_perm (complTup D hX.is.rank) (complTup_bijective D hX.is.rank) (εf _)`. Use `⟨M, M', fun T₁ T₂ => by rw [hMM T₁ T₂]; congr, fun g T => ?_⟩` and prove the remaining obligations. Rewrite using `[hMf T (fun T' => X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF rfl rfl T') g), hlamJ, hεf, map_smul, ← hJ, hlc]`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`.

Clear the denominators using the available nonvanishing facts. Conclude with `core P.a P'.a P.d P'.d P.n P'.n ea ea' ed ed' hn`.
-/
theorem theta_bottom_minor_match : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (δ t0 : ℂ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ea' : P'.a = A'.rank) (ed : P.d = WW.rank) (ed' : P'.d = WW.rank),
        ∃ (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
          ∀ (g : GA D WW) T, X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
            κ₀ * c0 s * ∑ T', (M T T' : ℂ) * X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea' ed' T') g := by
  intro hP hK hM _ _
  have hH : GlobalTheory.Published.HoweDualityReal := hP.howeDualityReal
  have hLM := _root_.GlobalTheory.T.twisted_local_factors_match hH hP hK hM
  have hTA := _root_.GlobalTheory.T.twisted_square_theta_integrals_eq hP hK hM
  obtain ⟨CF1, H1⟩ := GlobalTheory.T.definiteBottom_dictionary_frames_exponents_kernel
  obtain ⟨CF2, H2⟩ := _root_.GlobalTheory.T.theta_bottom_finite_place_matching hH hP hK hM
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, G1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, G2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W _ i j A A' WW X c0 hX hc => ?_⟩
  obtain ⟨FA, FA', FW, a, b, hdA, hdef, hdW, hD⟩ :=
    G1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  have hF := G2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  obtain ⟨Pr, q, q', hq, hq', hLMt⟩ := hLM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b
  obtain ⟨ρ, hρ, hrel⟩ := _root_.GlobalTheory.T.bottom_degree_match_real_quotient hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW a b hX.is.rank hdA hdef hdW
    ⟨_, _, (hD μ₀).1, (hD μ₀).2.1⟩ Pr q q' hq hq' hLMt
  choose εf hεf using hrel
  have eI : ∀ t P, thetaInt (X.ω t) X.m X.fd (fockF W.ψ W.θ true FA FW (X.f t) P) = X.I W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I, (hD t).2.2.2.2.1]
  have eI' : ∀ t P, thetaInt (X.ω' t) X.m' X.fd' (fockF W.ψ W.θ false FA' FW (X.f' t) P) = X.I' W.ψ W.θ t P := fun t P => by
    funext h; simp only [thetaInt, Tri.I', (hD t).2.2.2.2.2]
  have iI' : ∀ t P h, IntegrableOn (fun g => thetaKO (X.ω' t) g h (fockF W.ψ W.θ false FA' FW (X.f' t) P)) X.fd' X.m' :=
    fun t P h => by simp only [(hD t).2.2.2.2.2]; exact (hX.integrable t).2 P h
  have key : ∀ t, (∀ P', q' P' = 0 → X.I' W.ψ W.θ t P' = 0) ∧
      ((∀ P', X.I' W.ψ W.θ t P' = 0) ∨ ∀ P', X.I' W.ψ W.θ t P' = 0 → q' P' = 0) ∧
      (∃ lam : ℂ, ∀ P P', q P = q' P' → X.I W.ψ W.θ t P = lam • X.I' W.ψ W.θ t P') := by
    intro t
    obtain ⟨hTr, hInf, hf, hf', -, -⟩ := hD t
    obtain ⟨hex, hfac⟩ := hLMt _ _ hTr hInf
    obtain ⟨Pm, rf, rl, p, p', hm⟩ := _root_.GlobalTheory.T.triple_weil_transfer_matching hH hP hK hM D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hex (X.ω t) (X.ω' t)
      (hX.is.weil t) (hX.is.weil' t)
    obtain ⟨Pf, r, r', e, -, -, hr, hr'⟩ := hfac _ _ _ _ _ _ _ hm
    obtain ⟨c, hc0, hc⟩ := hTA D W.ψ W.θ W.θ_is A A' WW FA FA' FW _ _ hTr X.m X.fd X.m' X.fd' hX.is.meas hX.is.meas'
      (X.ω t) (X.ω' t) Pm rf rl p p' hm
    have hrel := _root_.GlobalTheory.T.theta_integral_vanishes_on_finite_relations hP D W.ψ W.θ W.ψ_std W.θ_is A' WW FA' FW _ _ (X.ω' t) (hX.is.weil' t) hdef X.m' X.fd' hX.is.meas'
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
    refine ⟨fun P' h0 => ?_, ?_, ?_⟩
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
        exact _root_.GlobalTheory.T.theta_lift_vanishes_of_irreducible_defect hH hP hK hM hTA D W.ψ W.θ W.ψ_std W.θ_is A A' WW FA FA' FW _ _ hTr hdA hdef hdW X.m X.fd X.m' X.fd'
          hX.is.meas hX.is.meas' (X.ω t) (X.ω' t) Pm rf rl p p' hm _ (memF P') hne (by rw [eI']; exact h0) _ (memF P'')
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
  choose hker hirr hlam using key
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
  have hJI : ∀ t, ∃ lam : ℂ, ∀ P, X.I W.ψ W.θ t P = lam • J t (q P) := fun t => by
    obtain ⟨lam, hl⟩ := hlam t
    refine ⟨lam, fun P => ?_⟩
    obtain ⟨P', hP'⟩ := hq' (q P)
    rw [← hP', hJ]; exact hl P P' hP'.symm
  choose lam hlamJ using hJI
  obtain ⟨⟨t₁, ht₁⟩, P0, P0', hc⟩ := hc
  have hJne : ∀ t, J t (q' P0') ≠ 0 := fun t h0 => by
    obtain ⟨h, hh⟩ := (hc t).2.1
    exact hh (by rw [← hJ, h0]; rfl)
  have hq0 : q' P0' ≠ 0 := fun h0 => hJne t₁ (by rw [h0, map_zero])
  have hinj : ∀ t, Function.Injective (J t) := fun t => by
    rcases hirr t with h | h
    · exact absurd (by rw [hJ]; exact h P0') (hJne t)
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro x hx0
      obtain ⟨P', rfl⟩ := hq' x
      rw [hJ] at hx0
      exact h P' hx0
  have heq : ∀ t, lam t • q P0 = c0 t • q' P0' := fun t => by
    apply hinj t
    rw [map_smul, map_smul, ← hlamJ, hJ]
    funext h
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (hc t).2.2 h
  have hlam1 : lam t₁ ≠ 0 := fun h0 => by
    have := heq t₁
    rw [h0, zero_smul] at this
    exact (smul_eq_zero.1 this.symm).elim ht₁ hq0
  set κ := c0 t₁ / lam t₁ with hκdef
  have hκ0 : κ ≠ 0 := div_ne_zero ht₁ hlam1
  have hqP0 : q P0 = κ • q' P0' := by
    rw [hκdef, div_eq_inv_mul, mul_smul, ← heq t₁, smul_smul, inv_mul_cancel₀ hlam1, one_smul]
  have hlc : ∀ t, lam t = c0 t / κ := fun t => by
    have h1 := heq t
    rw [hqP0, smul_smul, ← sub_eq_zero, ← sub_smul] at h1
    have h2 := (smul_eq_zero.1 h1).resolve_right hq0
    rw [eq_div_iff hκ0]; exact sub_eq_zero.1 h2
  refine ⟨ρ / κ, div_ne_zero hρ hκ0, fun s Q δ t0 P P' hB ea ea' ed ed' => ?_⟩
  have hn : P'.n = P.n := GlobalTheory.T.squareBottomPairs_weights_eq G s i j _ P P' hB
  have core : ∀ (a₁ a₁' d₁ d₁' : ℕ) (n n' : D.what₂.Tau → ℕ) (ea : a₁ = A.rank) (ea' : a₁' = A'.rank) (ed : d₁ = WW.rank)
      (ed' : d₁' = WW.rank) (hn : n' = n), ∃ (M : Tup D a₁ d₁ n → Tup D a₁' d₁' n' → ℤ) (M' : Tup D a₁' d₁' n' → Tup D a₁ d₁ n → ℤ),
        (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
        ∀ (g : GA D WW) T, X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
          ρ / κ * c0 s * ∑ T', (M T T' : ℂ) * X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea' ed' T') g := by
    intro a₁ a₁' d₁ d₁' n n' ea ea' ed ed' hn
    subst ea ea' ed ed' hn
    obtain ⟨M, M', hMM, hMf⟩ := exists_signed_perm (complTup D hX.is.rank) (complTup_bijective D hX.is.rank) (εf _)
    refine ⟨M, M', fun T₁ T₂ => by rw [hMM T₁ T₂]; congr, fun g T => ?_⟩
    rw [hMf T (fun T' => X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF rfl rfl T') g), hlamJ, hεf, map_smul, ← hJ, hlc]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  exact core P.a P'.a P.d P'.d P.n P'.n ea ea' ed ed' hn
end GlobalTheory.BotMatch
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.BotMatch.theta_bottom_minor_match | exact _root_.GlobalTheory.BotMatch.theta_bottom_minor_match | (intros; apply _root_.GlobalTheory.BotMatch.theta_bottom_minor_match <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.rallis_bottom_minor_matching : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (c0 : T → ℂ), IsBottomTri W i j X → X.IsConst W.ψ W.θ c0 →
      ∃ κ₀ : ℂ, κ₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (δ t0 : ℂ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ea' : P'.a = A'.rank) (ed : P.d = WW.rank) (ed' : P'.d = WW.rank),
        ∃ (M : Tup D P.a P.d P.n → Tup D P'.a P'.d P'.n → ℤ) (M' : Tup D P'.a P'.d P'.n → Tup D P.a P.d P.n → ℤ),
          (∀ T₁ T₂, ∑ T, M' T₁ T * M T T₂ = if T₁ = T₂ then 1 else 0) ∧
          ∀ (g : GA D WW) T, X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
            κ₀ * c0 s * ∑ T', (M T T' : ℂ) * X.I' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea' ed' T') g := by
  first | exact @_root_.GlobalTheory.BotMatch.theta_bottom_minor_match | exact _root_.GlobalTheory.BotMatch.theta_bottom_minor_match | (intros; apply _root_.GlobalTheory.BotMatch.theta_bottom_minor_match <;> assumption)
end
