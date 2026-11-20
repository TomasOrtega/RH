import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldLP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalDarbouxFixesThetaDistributionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticHermitianSkewStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicIntegrableOnDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSpanLocalTensorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticWeilActionStatement

noncomputable section

namespace GlobalTheory.ThK.LiftPair

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

attribute [local instance] GlobalTheory.LocalData.complRel

local instance locFieldLP' (v : Pl F) : IsNonarchimedeanLocalField (Fv F v) := GlobalTheory.LocalData.isLocalField v

/- English proof (translation)
Assemble the required witnesses or components as `⟨hΨ.1.comp _, hΨ.2.comp_left (map_zero _)⟩`.
-/
theorem conj_mem_SB {X : Type} [TopologicalSpace X] {Ψ : X → ℂ} (hΨ : Ψ ∈ GlobalTheory.SplitWeil.SB X) :
    (fun x => (starRingEnd ℂ) (Ψ x)) ∈ GlobalTheory.SplitWeil.SB X :=
  ⟨hΨ.1.comp _, hΨ.2.comp_left (map_zero _)⟩

/- English proof (translation)
Simplify using `only [chrW, GlobalTheory.LFun.locChar, MonoidHom.comp_apply, Circle.toUnits_apply, Units.val_mk]`. Apply the tactic sequence `first | exact Circle.norm_coe _ | simp`.
-/
theorem norm_chrW (χ : Chr F E) {v : Pl F} (τ : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ) : ‖((chrW χ τ x : ℂˣ) : ℂ)‖ = 1 := by
  simp only [chrW, GlobalTheory.LFun.locChar, MonoidHom.comp_apply, Circle.toUnits_apply, Units.val_mk]
  first | exact Circle.norm_coe _ | simp

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[tens, add_mul]`.
-/
theorem tens_add {R κ : Type} (ev : AF F → R) (φ₁ φ₂ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (φ₁ + φ₂) r = tens ev φ₁ r + tens ev φ₂ r := by
  funext x; simp [tens, add_mul]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[tens, mul_assoc]`.
-/
theorem tens_smul {R κ : Type} (ev : AF F → R) (c : ℂ) (φ : (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (c • φ) r = c • tens ev φ r := by
  funext x; simp [tens, mul_assoc]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use `set L := liftSk hcm τ JY hY hYd with hL`. Use `set M := trSpan L f with hM`. Simplify using `only [GlobalTheory.ThK.FlagPar.LiftZero] at hne`. Use `push_neg at hne`. Take `⟨co, hco, om, hom, Φ₀, hΦ₀, g, μ, 𝓕, hμ, h𝓕, hI⟩` from `hne`.

Establish `pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin m), om x Φ ∈ schA F (Fin n × Fin m)` using `fun x Φ hΦ => (IsUWeilPair.isUSplitting hom).pres x Φ hΦ`. Establish `omg : ∀ (h x : UA σ JY) Φ, om (g, h) (om (1, x) Φ) = om (g, h * x) Φ` using `fun h x Φ => by`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]`. Establish `thInv : ∀ γ ∈ ratU σ JY, ∀ Φ ∈ schA F (Fin n × Fin m), ∀ h, thetaSum F (om (g, γ * h) Φ) = thetaSum F (om (g, h) Φ)` using `fun γ hγ Φ hΦ h => by`. Establish `e : om (g, γ * h) Φ = om (1, γ) (om (g, h) Φ)`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]`. Rewrite using `[e]`. Conclude with `GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hom 1 (one_mem _) γ hγ _ (pres _ _ hΦ)`. Establish `memL : ∀ u ∈ M, ∀ γ ∈ ratU σ JY, ∀ h, u (γ * h) = u h`. Introduce `u hu`.

Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u h`. Take `⟨a, rfl⟩` from `h`. Introduce `γ hγ h`. Simplify using `only [rtr, mul_assoc]`.

Conclude with `hfl γ hγ _`. Consider the case `zero => intro γ _ h`. Both sides reduce to the same expression. Consider the case `add u w _ _ hu hw => intro γ hγ h`. Simplify using `[hu γ hγ h, hw γ hγ h]`.

Consider the case `smul c u _ hu => intro γ hγ h`. Simplify using `[hu γ hγ h]`. Establish `intg : ∀ u ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m), IntegrableOn (fun h => u h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ))) 𝓕 μ`. Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`.

Consider the case `mem u h`. Take `⟨a, rfl⟩` from `h`. Introduce `Φ hΦ`. Establish `h1` using `GlobalTheory.T.darboux_symplectic_hermitian_skew F E σ hK hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hom f hfc hfl hfd (om (1, (L a)⁻¹) Φ) (pres _ _ hΦ) g μ 𝓕 hμ h𝓕`. Establish `h2` using `(GlobalTheory.T.automorphic_integrable_on_domain F E σ hcm m JY hY hYd μ 𝓕 hμ h𝓕 _ (fun γ hγ h => by`.

Rewrite using `[hfl γ hγ h, thInv γ hγ _ (pres _ _ hΦ) h]) (L a)).1 h1`. Establish `e : (fun h => f (h * L a) * (starRingEnd ℂ) (thetaSum F (om (g, h * L a) (om (1, (L a)⁻¹) Φ)))) = fun h => rtr (L a) f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ))` using `funext fun h => by`. Rewrite using `[omg, mul_inv_cancel_right]`. Both sides reduce to the same expression. Rewrite `h2` using `[e]`. Then use the resulting hypothesis.

Consider the case `zero => intro Φ _`. Simplify using `[integrableOn_zero]`. Consider the case `add u w _ _ hu hw`. Introduce `Φ hΦ`. Use `((hu Φ hΦ).add (hw Φ hΦ)).congr (Eventually.of_forall fun h => ?_)` and prove the remaining obligations.

Simplify using `[add_mul]`. Consider the case `smul c u _ hu`. Introduce `Φ hΦ`. Use `((hu Φ hΦ).const_mul c).congr (Eventually.of_forall fun h => ?_)` and prove the remaining obligations. Simplify using `[mul_assoc]`.

Use `set Λ := fun (u : UA σ JY → ℂ) (Φ : (Fin n × Fin m → AF F) → ℂ) => thPair om g μ 𝓕 u Φ with hΛ`. Establish `Λaddu : ∀ u ∈ M, ∀ w ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m), Λ (u + w) Φ = Λ u Φ + Λ w Φ`. Introduce `u hu w hw Φ hΦ`. Simplify using `only [hΛ, thPair, ← integral_add (intg u hu Φ hΦ) (intg w hw Φ hΦ)]`. Use `integral_congr_ae (Eventually.of_forall fun h => ?_)` and prove the remaining obligations.

Simplify using `[add_mul]`. Establish `Λsmulu : ∀ (c : ℂ) (u : UA σ JY → ℂ) Φ, Λ (c • u) Φ = c * Λ u Φ`. Introduce `c u Φ`. Simplify using `only [hΛ, thPair, ← integral_const_mul]`. Use `integral_congr_ae (Eventually.of_forall fun h => ?_)` and prove the remaining obligations.

Simplify using `[mul_assoc]`. Establish `ΛaddΦ : ∀ u ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m), ∀ Ψ ∈ schA F (Fin n × Fin m), Λ u (Φ + Ψ) = Λ u Φ + Λ u Ψ`. Introduce `u hu Φ hΦ Ψ hΨ`. Simplify using `only [hΛ, thPair, ← integral_add (intg u hu Φ hΦ) (intg u hu Ψ hΨ)]`. Use `integral_congr_ae (Eventually.of_forall fun h => ?_)` and prove the remaining obligations.

Simplify using `only [map_add]`. Rewrite using `[thetaSum_add F (pres _ _ hΦ) (pres _ _ hΨ), map_add, mul_add]`. Establish `ΛsmulΦ : ∀ (c : ℂ) u Φ, Λ u (c • Φ) = (starRingEnd ℂ) c * Λ u Φ`. Introduce `c u Φ`. Simplify using `only [hΛ, thPair, ← integral_const_mul]`.

Use `integral_congr_ae (Eventually.of_forall fun h => ?_)` and prove the remaining obligations. Simplify using `only [map_smul]`. Rewrite using `[thetaSum_smul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `Λinv : ∀ u ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m), ∀ x, Λ (rtr x u) (om (1, x) Φ) = Λ u Φ`.

Introduce `u hu Φ hΦ x`. Establish `h2` using `(GlobalTheory.T.automorphic_integrable_on_domain F E σ hcm m JY hY hYd μ 𝓕 hμ h𝓕 (fun h => u h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ))) (fun γ hγ h => by rw [memL u hu γ hγ h, thInv γ hγ Φ hΦ h]) x).2`. Simplify using `only [hΛ, thPair, rtr, omg]`. Conclude with `h2`. Establish `hfM : f ∈ M` using `Submodule.subset_span ⟨1, by funext x; simp [rtr]⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨φ₀, r₀, hφ₀, hr₀, hne₀⟩ : ∃ (φ : (Fin n × Fin m → Fv F v) → ℂ) (r : (Fin n × Fin m → AF F) → ℂ), φ ∈ SB (Fin n × Fin m → Fv F v) ∧ (∀ φ' ∈ SB (Fin n × Fin m → Fv F v), Rest (evFin F v) φ' r) ∧ Λ f (tens (evFin F v) φ r) ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `key : ∀ Φ ∈ Submodule.span ℂ {Φ | ∃ (φ : (Fin n × Fin m → Fv F v) → ℂ) (r : (Fin n × Fin m → AF F) → ℂ), φ ∈ SB (Fin n × Fin m → Fv F v) ∧ (∀ φ' ∈ SB (Fin n × Fin m → Fv F v), Rest (evFin F v) φ' r) ∧ Φ = tens (evFin F v) φ r}, Φ ∈ schA F (Fin n × Fin m) ∧ Λ f Φ = 0`. Introduce `Φ hΦ`.

Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨φ, r, hφ, hr, rfl⟩` from `h`. Conclude with `⟨(hr φ hφ).2, hall φ r hφ hr⟩`. Consider the case `zero`.

Use `⟨zero_mem _, ?_⟩` and prove the remaining obligations. Use `ΛsmulΦ 0 f 0` as an intermediate fact. Simplify using `using this`. Consider the case `add Φ Ψ _ _ hΦ hΨ => exact ⟨add_mem hΦ.1 hΨ.1, by rw [ΛaddΦ f hfM Φ hΦ.1 Ψ hΨ.1, hΦ.2, hΨ.2, add_zero]⟩`. Consider the case `smul c Φ _ hΦ => exact ⟨Submodule.smul_mem _ c hΦ.1, by rw [ΛsmulΦ, hΦ.2, mul_zero]⟩`.

Conclude with `hI (key Φ₀ (GlobalTheory.T.schwartz_span_local_tensors F v (Fin n × Fin m) hΦ₀)).2`. Take `⟨ι, hbij, hmod⟩` from `GlobalTheory.T.darboux_symplectic_weil_action F E σ hK hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hom v τ`. Establish `kex : ∀ Ψ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)), ∃ φ ∈ SB (Fin n × Fin m → Fv F v), ι φ = fun X => (starRingEnd ℂ) ((Ψ : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) X)` using `fun Ψ => by`. Take `⟨φ, hφ, e⟩` from `hbij.surjOn (conj_mem_SB Ψ.2)`. Conclude with `⟨φ, hφ, e⟩`.

Use `choose kap hkapSB hkap using kex`. Establish `kapEq : ∀ (Ψ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v))) φ, φ ∈ SB (Fin n × Fin m → Fv F v) → ι φ = (fun X => (starRingEnd ℂ) ((Ψ : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) X)) → kap Ψ = φ` using `fun Ψ φ hφ e => hbij.injOn (hkapSB Ψ) hφ ((hkap Ψ).trans e.symm)`. Establish `kapAdd : ∀ Ψ₁ Ψ₂, kap (Ψ₁ + Ψ₂) = kap Ψ₁ + kap Ψ₂` using `fun Ψ₁ Ψ₂ => kapEq _ _ (add_mem (hkapSB Ψ₁) (hkapSB Ψ₂)) (by`. Rewrite using `[map_add, hkap, hkap]`. Use function extensionality and compare the values at `X`.

Use the proof step `simp)`. Establish `kapSmul : ∀ (c : ℂ) Ψ, kap (c • Ψ) = (starRingEnd ℂ) c • kap Ψ` using `fun c Ψ => kapEq _ _ (Submodule.smul_mem _ _ (hkapSB Ψ)) (by`. Rewrite using `[map_smul, hkap]`. Use function extensionality and compare the values at `X`. Use the proof step `simp)`.

Establish `tmem : ∀ Ψ, tens (evFin F v) (kap Ψ) r₀ ∈ schA F (Fin n × Fin m)` using `fun Ψ => (hr₀ _ (hkapSB Ψ)).2`. Set `P : M →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)) →ₗ[ℂ] ℂ` to `LinearMap.mk₂ ℂ (fun u Ψ => Λ u.1 (tens (evFin F v) (kap Ψ) r₀)) (fun u w Ψ => Λaddu u.1 u.2 w.1 w.2 _ (tmem Ψ)) (fun c u Ψ => Λsmulu c u.1 _) (fun u Ψ₁ Ψ₂ => by`. Simplify using `only [kapAdd, tens_add]`. Conclude with `ΛaddΦ u.1 u.2 _ (tmem Ψ₁) _ (tmem Ψ₂))`. Use the proof step `(fun c u Ψ => by`.

Simplify using `only [kapSmul, tens_smul, smul_eq_mul]`. Rewrite using `[ΛsmulΦ, Complex.conj_conj])`. Use `⟨P, ?_, ?_⟩` and prove the remaining obligations. Introduce `hP`. Establish `hΨ₀ : (fun X => (starRingEnd ℂ) (ι φ₀ X)) ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v))` using `conj_mem_SB (hbij.mapsTo hφ₀)`.

Establish `hk : kap ⟨_, hΨ₀⟩ = φ₀` using `kapEq _ _ hφ₀ (by funext X; simp)`. Use `LinearMap.congr_fun (LinearMap.congr_fun hP ⟨f, hfM⟩) ⟨_, hΨ₀⟩` as an intermediate fact. Express the relevant statement in the definitionally equal form `Λ f (tens (evFin F v) (kap ⟨_, hΨ₀⟩) r₀) = 0 at this`. Rewrite `this` using `[hk]`. Conclude with `hne₀ this`.

Introduce `h u hu hu' Φ Φ' hΦ'`. Take `⟨φ₁, hφ₁, e₁, hact⟩` from `hmod h (kap Φ) (hkapSB Φ)`. Establish `hk : kap Φ' = φ₁` using `kapEq _ _ hφ₁ (by`. Rewrite using `[e₁, hkap]`. Use function extensionality and compare the values at `X`.

Establish `hn` using `norm_chrW χX τ (Matrix.GeneralLinearGroup.det h)`. Simplify using `only [modelA]`. Rewrite using `[hΦ', map_mul, map_mul, Units.val_inv_eq_inv_val, Complex.inv_eq_conj hn, Complex.conj_conj, Complex.conj_ofReal])`. Express the relevant statement in the definitionally equal form `Λ (rtr (L h) u) (tens (evFin F v) (kap Φ') r₀) = Λ u (tens (evFin F v) (kap Φ) r₀)`. Rewrite using `[hk]`.

Rewrite using `[← hact r₀ (hr₀ _ (hkapSB Φ))]`. Conclude with `Λinv u hu _ (tmem Φ) _`.
-/
theorem exists_pairing (hK : GlobalTheory.ThK.KP) (hcm : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {n m : ℕ}
    (JX : Matrix (Fin n) (Fin n) E) (JY : Matrix (Fin m) (Fin m) E) (hX : ∀ i j, σ (JX j i) = JX i j) (hXd : JX.det ≠ 0)
    (hY : ∀ i j, σ (JY j i) = -JY i j) (hYd : JY.det ≠ 0) (χX χY : Chr F E) (hχX : IsHecke F E χX)
    (hχY : IsHecke F E χY) (f : UA σ JY → ℂ) (hfc : Continuous f) (hfl : ∀ γ ∈ ratU σ JY, ∀ h, f (γ * h) = f h)
    (hfd : ∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C)
    (hne : ¬ GlobalTheory.ThK.FlagPar.LiftZero ψ JX JY χX χY f) (v : Pl F) (τ : E →ₐ[F] Fv F v) :
    ∃ P : trSpan (liftSk hcm τ JY hY hYd) f →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)) →ₗ[ℂ] ℂ,
      P ≠ 0 ∧ ∀ (h : GL (Fin m) (Fv F v)) (u : UA σ JY → ℂ) (hu : u ∈ trSpan (liftSk hcm τ JY hY hYd) f)
        (hu' : rtr (liftSk hcm τ JY hY hYd h) u ∈ trSpan (liftSk hcm τ JY hY hYd) f)
        (Φ Φ' : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v))),
        (∀ X, (Φ' : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) X =
          ((chrW χX τ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) *
          ((GlobalTheory.SplitWeil.nabs (Fv F v) (Matrix.GeneralLinearGroup.det h) ^ (-(n : ℝ) / 2) : ℝ) : ℂ) *
          (Φ : Matrix (Fin n) (Fin m) (Fv F v) → ℂ)
            (X * ((h⁻¹ : GL (Fin m) (Fv F v)) : Matrix (Fin m) (Fin m) (Fv F v))ᵀ)) →
        P ⟨rtr (liftSk hcm τ JY hY hYd h) u, hu'⟩ Φ' = P ⟨u, hu⟩ Φ := by
  classical
  set L := liftSk hcm τ JY hY hYd with hL
  set M := trSpan L f with hM
  simp only [GlobalTheory.ThK.FlagPar.LiftZero] at hne
  push_neg at hne
  obtain ⟨co, hco, om, hom, Φ₀, hΦ₀, g, μ, 𝓕, hμ, h𝓕, hI⟩ := hne
  have pres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin m), om x Φ ∈ schA F (Fin n × Fin m) := fun x Φ hΦ =>
    (IsUWeilPair.isUSplitting hom).pres x Φ hΦ
  have omg : ∀ (h x : UA σ JY) Φ, om (g, h) (om (1, x) Φ) = om (g, h * x) Φ := fun h x Φ => by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have thInv : ∀ γ ∈ ratU σ JY, ∀ Φ ∈ schA F (Fin n × Fin m), ∀ h,
      thetaSum F (om (g, γ * h) Φ) = thetaSum F (om (g, h) Φ) := fun γ hγ Φ hΦ h => by
    have e : om (g, γ * h) Φ = om (1, γ) (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e]
    exact GlobalTheory.T.weilRep_rationalDarboux_fixes_thetaDistribution F E σ hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hom 1 (one_mem _) γ hγ _
      (pres _ _ hΦ)
  have memL : ∀ u ∈ M, ∀ γ ∈ ratU σ JY, ∀ h, u (γ * h) = u h := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u h =>
      obtain ⟨a, rfl⟩ := h
      intro γ hγ h
      simp only [rtr, mul_assoc]
      exact hfl γ hγ _
    | zero => intro γ _ h; rfl
    | add u w _ _ hu hw => intro γ hγ h; simp [hu γ hγ h, hw γ hγ h]
    | smul c u _ hu => intro γ hγ h; simp [hu γ hγ h]
  have intg : ∀ u ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m),
      IntegrableOn (fun h => u h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ))) 𝓕 μ := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u h =>
      obtain ⟨a, rfl⟩ := h
      intro Φ hΦ
      have h1 := GlobalTheory.T.darboux_symplectic_hermitian_skew F E σ hK hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hom f hfc hfl hfd
        (om (1, (L a)⁻¹) Φ) (pres _ _ hΦ) g μ 𝓕 hμ h𝓕
      have h2 := (GlobalTheory.T.automorphic_integrable_on_domain F E σ hcm m JY hY hYd μ 𝓕 hμ h𝓕 _ (fun γ hγ h => by
        rw [hfl γ hγ h, thInv γ hγ _ (pres _ _ hΦ) h]) (L a)).1 h1
      have e : (fun h => f (h * L a) * (starRingEnd ℂ) (thetaSum F (om (g, h * L a) (om (1, (L a)⁻¹) Φ)))) =
          fun h => rtr (L a) f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) := funext fun h => by
        rw [omg, mul_inv_cancel_right]; rfl
      rwa [e] at h2
    | zero => intro Φ _; simp [integrableOn_zero]
    | add u w _ _ hu hw =>
      intro Φ hΦ
      refine ((hu Φ hΦ).add (hw Φ hΦ)).congr (Eventually.of_forall fun h => ?_)
      simp [add_mul]
    | smul c u _ hu =>
      intro Φ hΦ
      refine ((hu Φ hΦ).const_mul c).congr (Eventually.of_forall fun h => ?_)
      simp [mul_assoc]

  set Λ := fun (u : UA σ JY → ℂ) (Φ : (Fin n × Fin m → AF F) → ℂ) => thPair om g μ 𝓕 u Φ with hΛ
  have Λaddu : ∀ u ∈ M, ∀ w ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m), Λ (u + w) Φ = Λ u Φ + Λ w Φ := by
    intro u hu w hw Φ hΦ
    simp only [hΛ, thPair, ← integral_add (intg u hu Φ hΦ) (intg w hw Φ hΦ)]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp [add_mul]
  have Λsmulu : ∀ (c : ℂ) (u : UA σ JY → ℂ) Φ, Λ (c • u) Φ = c * Λ u Φ := by
    intro c u Φ
    simp only [hΛ, thPair, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp [mul_assoc]
  have ΛaddΦ : ∀ u ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m), ∀ Ψ ∈ schA F (Fin n × Fin m), Λ u (Φ + Ψ) = Λ u Φ + Λ u Ψ := by
    intro u hu Φ hΦ Ψ hΨ
    simp only [hΛ, thPair, ← integral_add (intg u hu Φ hΦ) (intg u hu Ψ hΨ)]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [map_add]
    rw [thetaSum_add F (pres _ _ hΦ) (pres _ _ hΨ), map_add, mul_add]
  have ΛsmulΦ : ∀ (c : ℂ) u Φ, Λ u (c • Φ) = (starRingEnd ℂ) c * Λ u Φ := by
    intro c u Φ
    simp only [hΛ, thPair, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    simp only [map_smul]
    rw [thetaSum_smul, map_mul]
    ring
  have Λinv : ∀ u ∈ M, ∀ Φ ∈ schA F (Fin n × Fin m), ∀ x, Λ (rtr x u) (om (1, x) Φ) = Λ u Φ := by
    intro u hu Φ hΦ x
    have h2 := (GlobalTheory.T.automorphic_integrable_on_domain F E σ hcm m JY hY hYd μ 𝓕 hμ h𝓕 (fun h => u h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)))
      (fun γ hγ h => by rw [memL u hu γ hγ h, thInv γ hγ Φ hΦ h]) x).2
    simp only [hΛ, thPair, rtr, omg]
    exact h2
  have hfM : f ∈ M := Submodule.subset_span ⟨1, by funext x; simp [rtr]⟩

  obtain ⟨φ₀, r₀, hφ₀, hr₀, hne₀⟩ : ∃ (φ : (Fin n × Fin m → Fv F v) → ℂ) (r : (Fin n × Fin m → AF F) → ℂ),
      φ ∈ SB (Fin n × Fin m → Fv F v) ∧ (∀ φ' ∈ SB (Fin n × Fin m → Fv F v), Rest (evFin F v) φ' r) ∧
        Λ f (tens (evFin F v) φ r) ≠ 0 := by
    by_contra hall
    push_neg at hall
    have key : ∀ Φ ∈ Submodule.span ℂ {Φ | ∃ (φ : (Fin n × Fin m → Fv F v) → ℂ) (r : (Fin n × Fin m → AF F) → ℂ),
        φ ∈ SB (Fin n × Fin m → Fv F v) ∧ (∀ φ' ∈ SB (Fin n × Fin m → Fv F v), Rest (evFin F v) φ' r) ∧
          Φ = tens (evFin F v) φ r}, Φ ∈ schA F (Fin n × Fin m) ∧ Λ f Φ = 0 := by
      intro Φ hΦ
      induction hΦ using Submodule.span_induction with
      | mem Φ h =>
        obtain ⟨φ, r, hφ, hr, rfl⟩ := h
        exact ⟨(hr φ hφ).2, hall φ r hφ hr⟩
      | zero =>
        refine ⟨zero_mem _, ?_⟩
        have := ΛsmulΦ 0 f 0
        simpa using this
      | add Φ Ψ _ _ hΦ hΨ => exact ⟨add_mem hΦ.1 hΨ.1, by rw [ΛaddΦ f hfM Φ hΦ.1 Ψ hΨ.1, hΦ.2, hΨ.2, add_zero]⟩
      | smul c Φ _ hΦ => exact ⟨Submodule.smul_mem _ c hΦ.1, by rw [ΛsmulΦ, hΦ.2, mul_zero]⟩
    exact hI (key Φ₀ (GlobalTheory.T.schwartz_span_local_tensors F v (Fin n × Fin m) hΦ₀)).2

  obtain ⟨ι, hbij, hmod⟩ := GlobalTheory.T.darboux_symplectic_weil_action F E σ hK hcm ψ hψ n m JX JY hX hXd hY hYd co hco χX χY hχX hχY om hom v τ
  have kex : ∀ Ψ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)), ∃ φ ∈ SB (Fin n × Fin m → Fv F v),
      ι φ = fun X => (starRingEnd ℂ) ((Ψ : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) X) := fun Ψ => by
    obtain ⟨φ, hφ, e⟩ := hbij.surjOn (conj_mem_SB Ψ.2)
    exact ⟨φ, hφ, e⟩
  choose kap hkapSB hkap using kex
  have kapEq : ∀ (Ψ : GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v))) φ, φ ∈ SB (Fin n × Fin m → Fv F v) →
      ι φ = (fun X => (starRingEnd ℂ) ((Ψ : Matrix (Fin n) (Fin m) (Fv F v) → ℂ) X)) → kap Ψ = φ :=
    fun Ψ φ hφ e => hbij.injOn (hkapSB Ψ) hφ ((hkap Ψ).trans e.symm)
  have kapAdd : ∀ Ψ₁ Ψ₂, kap (Ψ₁ + Ψ₂) = kap Ψ₁ + kap Ψ₂ := fun Ψ₁ Ψ₂ =>
    kapEq _ _ (add_mem (hkapSB Ψ₁) (hkapSB Ψ₂)) (by
      rw [map_add, hkap, hkap]; funext X; simp)
  have kapSmul : ∀ (c : ℂ) Ψ, kap (c • Ψ) = (starRingEnd ℂ) c • kap Ψ := fun c Ψ =>
    kapEq _ _ (Submodule.smul_mem _ _ (hkapSB Ψ)) (by
      rw [map_smul, hkap]; funext X; simp)
  have tmem : ∀ Ψ, tens (evFin F v) (kap Ψ) r₀ ∈ schA F (Fin n × Fin m) := fun Ψ => (hr₀ _ (hkapSB Ψ)).2
  let P : M →ₗ[ℂ] GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun u Ψ => Λ u.1 (tens (evFin F v) (kap Ψ) r₀))
      (fun u w Ψ => Λaddu u.1 u.2 w.1 w.2 _ (tmem Ψ))
      (fun c u Ψ => Λsmulu c u.1 _)
      (fun u Ψ₁ Ψ₂ => by
        simp only [kapAdd, tens_add]
        exact ΛaddΦ u.1 u.2 _ (tmem Ψ₁) _ (tmem Ψ₂))
      (fun c u Ψ => by
        simp only [kapSmul, tens_smul, smul_eq_mul]
        rw [ΛsmulΦ, Complex.conj_conj])
  refine ⟨P, ?_, ?_⟩
  · intro hP
    have hΨ₀ : (fun X => (starRingEnd ℂ) (ι φ₀ X)) ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin n) (Fin m) (Fv F v)) :=
      conj_mem_SB (hbij.mapsTo hφ₀)
    have hk : kap ⟨_, hΨ₀⟩ = φ₀ := kapEq _ _ hφ₀ (by funext X; simp)
    have := LinearMap.congr_fun (LinearMap.congr_fun hP ⟨f, hfM⟩) ⟨_, hΨ₀⟩
    change Λ f (tens (evFin F v) (kap ⟨_, hΨ₀⟩) r₀) = 0 at this
    rw [hk] at this
    exact hne₀ this
  · intro h u hu hu' Φ Φ' hΦ'
    obtain ⟨φ₁, hφ₁, e₁, hact⟩ := hmod h (kap Φ) (hkapSB Φ)
    have hk : kap Φ' = φ₁ := kapEq _ _ hφ₁ (by
      rw [e₁, hkap]
      funext X
      have hn := norm_chrW χX τ (Matrix.GeneralLinearGroup.det h)
      simp only [modelA]
      rw [hΦ', map_mul, map_mul, Units.val_inv_eq_inv_val, Complex.inv_eq_conj hn, Complex.conj_conj,
        Complex.conj_ofReal])
    change Λ (rtr (L h) u) (tens (evFin F v) (kap Φ') r₀) = Λ u (tens (evFin F v) (kap Φ) r₀)
    rw [hk]
    rw [← hact r₀ (hr₀ _ (hkapSB Φ))]
    exact Λinv u hu _ (tmem Φ) _

end GlobalTheory.ThK.LiftPair

end
