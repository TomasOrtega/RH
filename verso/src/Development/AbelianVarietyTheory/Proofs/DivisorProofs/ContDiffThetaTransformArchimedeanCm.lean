import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformAdelicSchwartzRealDirection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanStandardCharEqExpRealLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRealFamilyArchimedeanLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLintegralSqEqMulSetLIntegralThetaTransformStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

open scoped Classical ContDiff

noncomputable section

namespace GlobalTheory.ThetaSmoothF

/- English proof (translation)
Take `⟨-, ⟨θ, hθ⟩, hall⟩` from `h`. Establish `hform` using `hall θ hθ`. Use `set e := InfiniteAdeleRing.ringEquiv_mixedSpace F`. Set `c : ℂ` to `2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ)`. Set `g : mixedEmbedding.mixedSpace F →+ ℂ` to `{ toFun := fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[F] (1 : E)) map_zero' := by simp map_add' := by`.

Introduce `a b`. Simplify using `[TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }`. Establish `hg : Continuous g` using `by show Continuous fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[F] (1 : E))`. Use `continuous_const.mul (continuous_finset_sum _ fun ρ _ => ?_)` and prove the remaining obligations. Conclude with `(hθ ρ).2.comp (GlobalTheory.PsiInfLinear.continuous_ringEquiv_mixedSpace_symm F)`.

Use `⟨AddMonoidHom.toRealLinearMap g hg, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[hform x]`. Use `congr 1`. Use `show _ = c * ∑ ρ, θ ρ (e.symm (e x) ⊗ₜ[F] (1 : E))`. Rewrite using `[e.symm_apply_apply]`.
-/
theorem psiInf_eq_exp_linearF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {Tau : Type} [Fintype Tau] (tauE : Tau → (E →+* ℂ)) (ψ : AddChar (AF F) ℂ) (h : IsStdCharF tauE ψ (-1)) :
    ∃ Λ : mixedEmbedding.mixedSpace F →L[ℝ] ℂ, ∀ x : InfiniteAdeleRing F,
      psiInf F ψ x = Complex.exp (Λ (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) := by
  obtain ⟨-, ⟨θ, hθ⟩, hall⟩ := h
  have hform := hall θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let c : ℂ := 2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ)
  let g : mixedEmbedding.mixedSpace F →+ ℂ :=
    { toFun := fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[F] (1 : E))
      map_zero' := by simp
      map_add' := by
        intro a b
        simp [TensorProduct.add_tmul, Finset.sum_add_distrib, mul_add] }
  have hg : Continuous g := by
    show Continuous fun m => c * ∑ ρ, θ ρ (e.symm m ⊗ₜ[F] (1 : E))
    refine continuous_const.mul (continuous_finset_sum _ fun ρ _ => ?_)
    exact (hθ ρ).2.comp (GlobalTheory.PsiInfLinear.continuous_ringEquiv_mixedSpace_symm F)
  refine ⟨AddMonoidHom.toRealLinearMap g hg, fun x => ?_⟩
  rw [hform x]
  congr 1
  show _ = c * ∑ ρ, θ ρ (e.symm (e x) ⊗ₜ[F] (1 : E))
  rw [e.symm_apply_apply]

/- English proof (translation)
Establish `hε : ∀ t, (pairA F 0 1) • L t = 0`. Introduce `t`. Use extensionality with `i j`. Establish `h0 : finPartF F E (L t i j) = 0` using `congrFun (congrFun (hfin t) i) j`. Rewrite using `[Matrix.smul_apply, GlobalTheory.RealDirCoord.eps_smul_gen]`.

Express the relevant statement in the definitionally equal form `LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F)) (finPartF F E (L t i j)) = 0`. Rewrite using `[h0, LinearMap.map_zero]`. Establish `hsnd : ∀ t i, ((e (L t)).1 i).2 = 0 ∧ ((e (L t)).2 i).2 = 0`. Introduce `t i`. Establish `h` using `congrArg e (hε t)`.

Rewrite `h` using `[LinearEquiv.map_smul, LinearEquiv.map_zero]`. Establish `h1` using `congrArg Prod.snd (congrFun (congrArg Prod.fst h) i)`. Establish `h2` using `congrArg Prod.snd (congrFun (congrArg Prod.snd h) i)`. Conclude with `⟨(GlobalTheory.RealDirCoord.eps_mul_snd _).symm.trans h1, (GlobalTheory.RealDirCoord.eps_mul_snd _).symm.trans h2⟩`. Establish `he : Continuous e` using `by haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩ haveI : IsModuleTopology (AF F) (WOF F E nS nT) := inferInstanceAs (IsModuleTopology (AF F) (Fin _ → Fin _ → AF F ⊗[F] E))`.

Conclude with `IsModuleTopology.continuous_of_linearMap e.toLinearMap`. Establish `hc : ∀ (p : ((κ → AF F) × (κ → AF F)) → (κ → AF F)), Continuous p → (∀ x y, p (x + y) = p x + p y) → ∃ P : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace F), ∀ t i, P t i = InfiniteAdeleRing.ringEquiv_mixedSpace F (p (e (L t)) i).1`. Introduce `p hp hadd`. Set `f : (Fin k → ℝ) →+ (κ → mixedEmbedding.mixedSpace F)` to `{ toFun := fun t i => InfiniteAdeleRing.ringEquiv_mixedSpace F (p (e (L t)) i).1 map_zero' := by`. Use function extensionality and compare the values at `i`.

Establish `h0 : p 0 = 0` using `by simpa using hadd 0 0`. Rewrite using `[map_zero, LinearEquiv.map_zero, h0]`. Conclude with `map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)`. Use the proof step `map_add' := by`. Introduce `a b`.

Use function extensionality and compare the values at `i`. Rewrite using `[map_add, LinearEquiv.map_add, hadd]`. Conclude with `map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _ }`. Establish `hf : Continuous f`. Use `continuous_pi fun i => ?_` and prove the remaining obligations.

Conclude with `(GlobalTheory.RealDirCoord.continuous_ringEquiv_mixed F).comp (continuous_fst.comp ((continuous_apply i).comp (hp.comp (he.comp hL))))`. Conclude with `⟨f.toRealLinearMap hf, fun t i => rfl⟩`. Take `⟨P, hP⟩` from `hc Prod.fst continuous_fst (fun _ _ => rfl)`. Take `⟨Q, hQ⟩` from `hc Prod.snd continuous_snd (fun _ _ => rfl)`. Use `⟨P, Q, fun t => ?_⟩` and prove the remaining obligations.

Use `Prod.ext (funext fun i => ?_) (funext fun i => ?_)` and prove the remaining obligations. Use `show (e (L t)).1 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (P t i), 0)`. Rewrite using `[hP, RingEquiv.symm_apply_apply]`. Conclude with `Prod.ext rfl (hsnd t i).1`. Use `show (e (L t)).2 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Q t i), 0)`.

Rewrite using `[hQ, RingEquiv.symm_apply_apply]`. Conclude with `Prod.ext rfl (hsnd t i).2`.
-/
theorem darboux_real_coordsF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (nS nT : ℕ) (κ : Type) [Fintype κ] (e : WOF F E nS nT ≃ₗ[AF F] (κ → AF F) × (κ → AF F)) (k : ℕ)
    (L : (Fin k → ℝ) →+ WOF F E nS nT) (hL : Continuous L) (hfin : ∀ t, (L t).map (finPartF F E) = 0) :
    ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace F), ∀ t, e (L t) =
      (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (P t i)) 0,
        fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Q t i)) 0) := by
  have hε : ∀ t, (pairA F 0 1) • L t = 0 := by
    intro t
    ext i j
    have h0 : finPartF F E (L t i j) = 0 := congrFun (congrFun (hfin t) i) j
    rw [Matrix.smul_apply, GlobalTheory.RealDirCoord.eps_smul_gen]
    change LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F)) (finPartF F E (L t i j)) = 0
    rw [h0, LinearMap.map_zero]
  have hsnd : ∀ t i, ((e (L t)).1 i).2 = 0 ∧ ((e (L t)).2 i).2 = 0 := by
    intro t i
    have h := congrArg e (hε t)
    rw [LinearEquiv.map_smul, LinearEquiv.map_zero] at h
    have h1 := congrArg Prod.snd (congrFun (congrArg Prod.fst h) i)
    have h2 := congrArg Prod.snd (congrFun (congrArg Prod.snd h) i)
    exact ⟨(GlobalTheory.RealDirCoord.eps_mul_snd _).symm.trans h1, (GlobalTheory.RealDirCoord.eps_mul_snd _).symm.trans h2⟩
  have he : Continuous e := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsModuleTopology (AF F) (WOF F E nS nT) :=
      inferInstanceAs (IsModuleTopology (AF F) (Fin _ → Fin _ → AF F ⊗[F] E))
    exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc : ∀ (p : ((κ → AF F) × (κ → AF F)) → (κ → AF F)), Continuous p →
      (∀ x y, p (x + y) = p x + p y) →
      ∃ P : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace F),
        ∀ t i, P t i = InfiniteAdeleRing.ringEquiv_mixedSpace F (p (e (L t)) i).1 := by
    intro p hp hadd
    let f : (Fin k → ℝ) →+ (κ → mixedEmbedding.mixedSpace F) :=
      { toFun := fun t i => InfiniteAdeleRing.ringEquiv_mixedSpace F (p (e (L t)) i).1
        map_zero' := by
          funext i
          have h0 : p 0 = 0 := by simpa using hadd 0 0
          rw [map_zero, LinearEquiv.map_zero, h0]
          exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
        map_add' := by
          intro a b
          funext i
          rw [map_add, LinearEquiv.map_add, hadd]
          exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _ }
    have hf : Continuous f := by
      refine continuous_pi fun i => ?_
      exact (GlobalTheory.RealDirCoord.continuous_ringEquiv_mixed F).comp
        (continuous_fst.comp ((continuous_apply i).comp (hp.comp (he.comp hL))))
    exact ⟨f.toRealLinearMap hf, fun t i => rfl⟩
  obtain ⟨P, hP⟩ := hc Prod.fst continuous_fst (fun _ _ => rfl)
  obtain ⟨Q, hQ⟩ := hc Prod.snd continuous_snd (fun _ _ => rfl)
  refine ⟨P, Q, fun t => ?_⟩
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show (e (L t)).1 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (P t i), 0)
    rw [hP, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).1
  · show (e (L t)).2 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (Q t i), 0)
    rw [hQ, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).2

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B0' hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA JB ξ0 hJA hJB κ _ co hrat Φ hΦ k L hLc hLf w0`. Use `set ψ := B0'.ψ`. Take `⟨P, Q, hPQ⟩` from `darboux_real_coordsF (F := F) (E := E) nS nT κ co.e k L hLc hLf`. Take `⟨Λ, hΛ⟩` from `psiInf_eq_exp_linearF _ ψ hψ`. Establish `hψ1 : ∀ x, ‖ψ x‖ = 1` using `hψ.1.2.1`.

Establish `hΛre : ∀ m, (Λ m).re = 0`. Introduce `m`. Establish `h1` using `hψ1 (pairA _ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) 0)`. Establish `h2` using `hΛ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m)`. Unfold `psiInf at h2`.

Rewrite `h1` using `[h2, RingEquiv.apply_symm_apply, Complex.norm_exp]`. Conclude with `Real.exp_eq_one_iff _ |>.mp h1`. It suffices to establish `key : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ w, Summable (fun x : κ → F => co.rho ψ w Φ (fun i => algebraMap F (AF F) (x i))) ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ (w + L t) from (key Φ hΦ w0).2`. Establish `rho_add : ∀ w (Φ₁ Φ₂ : (κ → AF F) → ℂ), co.rho ψ w (Φ₁ + Φ₂) = co.rho ψ w Φ₁ + co.rho ψ w Φ₂`. Introduce `w Φ₁ Φ₂`.

Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]`. Establish `rho_smul : ∀ w (c : ℂ) (Φ₁ : (κ → AF F) → ℂ), co.rho ψ w (c • Φ₁) = c • co.rho ψ w Φ₁`. Introduce `w c Φ₁`. Use function extensionality and compare the values at `x`.

Simplify using `[GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]`. Expand and normalize the polynomial expressions, which then agree. Establish `rho_zero : ∀ w, co.rho ψ w (0 : (κ → AF F) → ℂ) = 0`. Introduce `w`. Use function extensionality and compare the values at `x`.

Simplify using `[GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]`. Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`.

Introduce `w`. Take `⟨M, hM⟩` from `GlobalTheory.T.summable_rational_schwartzBruhat_mul_polynomial_decay F κ g hg (fun i => ((co.e w).1 i).2)`. Set `eM` to `InfiniteAdeleRing.ringEquiv_mixedSpace F`. Set `yv : (κ → F) → (κ → mixedEmbedding.mixedSpace F)` to `fun x i => mixedEmbedding F (x i)`. Set `ah : κ → mixedEmbedding.mixedSpace F` to `fun i => eM ((co.e w).1 i).1`.

Set `bh : κ → mixedEmbedding.mixedSpace F` to `fun i => eM ((co.e w).2 i).1`. Set `c2 : mixedEmbedding.mixedSpace F` to `eM (⅟(2 : AF F)).1`. Set `B0 : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin k → ℝ) →ₗ[ℝ] ℂ` to `LinearMap.mk₂ ℝ (fun y t => Λ (∑ i, y i * Q t i)) (fun y₁ y₂ t => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add]) (fun r y t => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul]) (fun y t₁ t₂ => by simp only [map_add, Pi.add_apply, m …`. Set `B : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℂ` to `LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : ((Fin k → ℝ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B0)`. Establish `hB : ∀ y t, B y t = Λ (∑ i, y i * Q t i)` using `fun y t => rfl`.

Set `hfun : (Fin k → ℝ) → ℂ` to `fun t => Λ (c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i))`. Establish `hPi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => P t i` using `fun i => ((ContinuousLinearMap.proj i).comp P).contDiff`. Establish `hQi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => Q t i` using `fun i => ((ContinuousLinearMap.proj i).comp Q).contDiff`. Establish `hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hfun` using `Λ.contDiff.comp (contDiff_const.mul (ContDiff.sum fun i _ => ((contDiff_const.mul (hQi i)).add ((hPi i).mul contDiff_const)).add ((hPi i).mul (hQi i))))`. Establish `hre : ∀ y t, (B y t + hfun t).re = 0`.

Introduce `y t`. Rewrite using `[hB, ← map_add]`. Conclude with `hΛre _`. Set `K : (κ → F) → ℂ` to `fun x => ψ ((fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)) * g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2)`. Set `G : (κ → F) → (Fin k → ℝ) → ℂ` to `fun x t => Complex.exp (B (yv x) t + hfun t) * f (yv x + ah + P t)`.

Set `term : (κ → F) → (Fin k → ℝ) → ℂ` to `fun x t => K x * G x t`. Establish `hid : ∀ x t, co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA F f g) (fun i => algebraMap F (AF F) (x i)) = term x t`. Introduce `x t`. Establish `he : co.e (w + L t) = ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0, (co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0)`. Rewrite using `[map_add, hPQ t]`.

Both sides reduce to the same expression. Establish `hy : ∀ i, eM (algebraMap F (AF F) (x i)).1 = yv x i`. Introduce `i`. Simplify using `only [yv, eM]`. Rewrite using `[InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]`.

Both sides reduce to the same expression. Establish `h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (((fun i => algebraMap F (AF F) (x i)) + ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0)) i).1) = yv x + ah + P t`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `eM ((algebraMap F (AF F) (x i)).1 + (((co.e w).1 i).1 + eM.symm (P t i))) = _`. Rewrite using `[map_add, map_add, RingEquiv.apply_symm_apply, hy i, ← add_assoc]`.

Both sides reduce to the same expression. Establish `h2 : (fun i => (((fun i => algebraMap F (AF F) (x i)) + ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0)) i).2) = fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2`. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(algebraMap F (AF F) (x i)).2 + (((co.e w).1 i).2 + 0) = _`. Rewrite using `[add_zero]`.

Both sides reduce to the same expression. Establish `hL : co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA F f g) (fun i => algebraMap F (AF F) (x i)) = ψ ((fun i => algebraMap F (AF F) (x i)) ⬝ᵥ ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) + ⅟2 * (((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ ((co.e w).2 + fun i => pai …`. Rewrite using `[← h1, ← h2]`. Use `show GlobalTheory.WeilM.schr ψ (co.e (w + L t)) _ _ = _`. Rewrite using `[he]`.

Both sides reduce to the same expression. Rewrite using `[hL]`. Set `φ : AF F →+* mixedEmbedding.mixedSpace F` to `eM.toRingHom.comp (fstA F).toRingHom`. Set `φf : AF F →+* FiniteAdeleRing (𝓞 F) F` to `(sndA F).toRingHom`. Establish `hφx : ∀ i, φ (algebraMap F (AF F) (x i)) = yv x i` using `hy`.

Establish `hφP : ∀ i, φ (pairA F (eM.symm (P t i)) 0) = P t i` using `fun i => eM.apply_symm_apply _`. Establish `hφQ : ∀ i, φ (pairA F (eM.symm (Q t i)) 0) = Q t i` using `fun i => eM.apply_symm_apply _`. Establish `hφa : ∀ i, φ ((co.e w).1 i) = ah i` using `fun i => rfl`. Establish `hφb : ∀ i, φ ((co.e w).2 i) = bh i` using `fun i => rfl`. Establish `hφ2 : φ ⅟2 = c2` using `rfl`.

Establish `hφdef : ∀ z : AF F, eM z.1 = φ z` using `fun _ => rfl`. Establish `hφfdef : ∀ z : AF F, z.2 = φf z` using `fun _ => rfl`. Establish `hφpair : ∀ n, φ (pairA F (eM.symm n) 0) = n` using `fun n => eM.apply_symm_apply _`. Establish `hφfpair : ∀ n, φf (pairA F (eM.symm n) 0) = 0` using `fun n => rfl`. Establish `hφfP : ∀ i, φf (pairA F (eM.symm (P t i)) 0) = 0` using `fun i => rfl`.

Establish `hφfQ : ∀ i, φf (pairA F (eM.symm (Q t i)) 0) = 0` using `fun i => rfl`. Use `set X := (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2) with hX`. Use `set m := ∑ i, yv x i * Q t i + c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i) with hm`. Establish `hsplit : (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) + ⅟2 * (((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0)) = X + pairA F (eM.symm m) 0`. Establish `hY : (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0) + ⅟2 * ((co.e w).1 ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0) + (fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ (co.e w).2 + (fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) …`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Apply `eM.injective` to reduce the goal to its premises. Rewrite using `[hφdef, hφdef, hφpair, hm]`. Simplify using `only [dotProduct, map_add, map_mul, map_sum, hφx, hφP, hφQ, hφa, hφb, hφ2, Finset.sum_add_distrib]`. Rewrite using `[hφfdef, hφfdef, hφfpair]`.

Simplify using `only [dotProduct, map_add, map_mul, map_sum, hφfP, hφfQ, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]`. Rewrite using `[← hY, hX]`. Simplify using `only [dotProduct_add, add_dotProduct]`. Expand and normalize the polynomial expressions, which then agree. Establish `hψY : ψ (pairA F (eM.symm m) 0) = Complex.exp (B (yv x) t + hfun t)`.

Express the relevant statement in the definitionally equal form `psiInf F ψ (eM.symm m) = _`. Rewrite using `[hΛ, show InfiniteAdeleRing.ringEquiv_mixedSpace F = eM from rfl, RingEquiv.apply_symm_apply, hm, map_add]`. Both sides reduce to the same expression. Rewrite using `[hsplit, AddChar.map_add_eq_mul, hψY]`. Simplify using `only [term, K, G]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hK : ∀ x, ‖K x‖ = ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2)‖`. Introduce `x`. Simplify using `only [K, norm_mul, hψ1, one_mul]`. Establish `hG : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G x)` using `fun x => (Complex.contDiff_exp.comp ((B (yv x)).contDiff.add hsm)).mul ((f.smooth ⊤).comp (contDiff_const.add P.contDiff))`.

Establish `hsmooth : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (term x)` using `fun x => contDiff_const.mul (hG x)`. Establish `hbd : ∀ (n : ℕ) (R : ℝ), ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ x t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (term x) t‖ ≤ u x`. Introduce `n R`. Take `⟨C, hC⟩` from `GlobalTheory.ThetaSmooth.norm_iteratedFDeriv_exp_mul_schwartz_le f B hfun hsm hre ah P n M R`. Use `⟨fun x => C * (‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2)‖ * ((1 + ‖yv x + 0‖) ^ M)⁻¹), (hM 0).mul_left C, fun x t ht => ?_⟩` and prove the remaining obligations.

Establish `e : term x = K x • G x` using `rfl`. Rewrite using `[e, iteratedFDeriv_const_smul_apply ((hG x).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul, hK]`. Establish `h1` using `hC (yv x) t ht`. Combine the equalities or inequalities in the displayed calculation. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Take `⟨u, hu, hu'⟩` from `hbd 0 0`. Use `Summable.of_norm_bounded hu fun x => ?_` and prove the remaining obligations. Establish `h1` using `hu' x 0 (by simp)`. Rewrite `h1` using `[norm_iteratedFDeriv_zero, ← hid x 0]`. Simplify using `using h1`.

Establish `e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (GlobalTheory.WeilM.pureA F f g) (w + L t)) = fun t => ∑' x, term x t` using `funext fun t => tsum_congr fun x => hid x t`. Rewrite using `[e]`. Conclude with `GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds term hsmooth hbd`. Consider the case `zero`. Introduce `w`.

Simplify using `only [GlobalTheory.WeilSchrodinger.thetaTr, rho_zero, Pi.zero_apply]`. Conclude with `⟨summable_zero, by simpa [GlobalTheory.WeilM.thetaSum] using contDiff_const⟩`. Consider the case `add Φ₁ Φ₂ _ _ h1 h2`. Introduce `w`. Use `⟨by rw [rho_add]; exact (h1 w).1.add (h2 w).1, ?_⟩` and prove the remaining obligations.

Establish `e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (Φ₁ + Φ₂) (w + L t)) = fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₁ (w + L t) + GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₂ (w + L t)`. Use function extensionality and compare the values at `t`. Simplify using `only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_add, Pi.add_apply]`. Conclude with `(h1 (w + L t)).1.tsum_add (h2 (w + L t)).1`. Rewrite using `[e]`.

Conclude with `(h1 w).2.add (h2 w).2`. Consider the case `smul c Φ₁ _ h1`. Introduce `w`. Use `⟨by rw [rho_smul]; exact (h1 w).1.const_smul c, ?_⟩` and prove the remaining obligations. Establish `e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (c • Φ₁) (w + L t)) = fun t => c * GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₁ (w + L t)`.

Use function extensionality and compare the values at `t`. Simplify using `only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `tsum_mul_left`. Rewrite using `[e]`. Conclude with `contDiff_const.mul (h1 w).2`.
-/
theorem contDiff_thetaTr_realF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L →
            (∀ t, (L t).map (finPartF F E) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (w + L t) := by
  intro F E _ _ _ _ _ σ B0' hgood hψ nS nT JS JT hJS hJT ξ₀ hξ₀ hσξ JA JB ξ0 hJA hJB κ _ co hrat Φ hΦ k L hLc hLf w0
  set ψ := B0'.ψ
  obtain ⟨P, Q, hPQ⟩ := darboux_real_coordsF (F := F) (E := E) nS nT κ co.e k L hLc hLf
  obtain ⟨Λ, hΛ⟩ := psiInf_eq_exp_linearF _ ψ hψ
  have hψ1 : ∀ x, ‖ψ x‖ = 1 := hψ.1.2.1
  have hΛre : ∀ m, (Λ m).re = 0 := by
    intro m
    have h1 := hψ1 (pairA _ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m) 0)
    have h2 := hΛ ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm m)
    unfold psiInf at h2
    rw [h2, RingEquiv.apply_symm_apply, Complex.norm_exp] at h1
    exact Real.exp_eq_one_iff _ |>.mp h1

  suffices key : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ w,
      Summable (fun x : κ → F => co.rho ψ w Φ (fun i => algebraMap F (AF F) (x i))) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ (w + L t) from
    (key Φ hΦ w0).2
  have rho_add : ∀ w (Φ₁ Φ₂ : (κ → AF F) → ℂ), co.rho ψ w (Φ₁ + Φ₂) = co.rho ψ w Φ₁ + co.rho ψ w Φ₂ := by
    intro w Φ₁ Φ₂; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]
  have rho_smul : ∀ w (c : ℂ) (Φ₁ : (κ → AF F) → ℂ), co.rho ψ w (c • Φ₁) = c • co.rho ψ w Φ₁ := by
    intro w c Φ₁; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]; ring
  have rho_zero : ∀ w, co.rho ψ w (0 : (κ → AF F) → ℂ) = 0 := by
    intro w; funext x; simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    intro w
    obtain ⟨M, hM⟩ := GlobalTheory.T.summable_rational_schwartzBruhat_mul_polynomial_decay F κ g hg (fun i => ((co.e w).1 i).2)
    let eM := InfiniteAdeleRing.ringEquiv_mixedSpace F
    let yv : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun x i => mixedEmbedding F (x i)
    let ah : κ → mixedEmbedding.mixedSpace F := fun i => eM ((co.e w).1 i).1
    let bh : κ → mixedEmbedding.mixedSpace F := fun i => eM ((co.e w).2 i).1
    let c2 : mixedEmbedding.mixedSpace F := eM (⅟(2 : AF F)).1
    let B0 : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin k → ℝ) →ₗ[ℝ] ℂ :=
      LinearMap.mk₂ ℝ (fun y t => Λ (∑ i, y i * Q t i))
        (fun y₁ y₂ t => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add])
        (fun r y t => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul])
        (fun y t₁ t₂ => by simp only [map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib])
        (fun r y t => by simp only [map_smul, Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum])
    let B : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin k → ℝ) →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        ((LinearMap.toContinuousLinearMap : ((Fin k → ℝ) →ₗ[ℝ] ℂ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ B0)
    have hB : ∀ y t, B y t = Λ (∑ i, y i * Q t i) := fun y t => rfl
    let hfun : (Fin k → ℝ) → ℂ := fun t => Λ (c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i))
    have hPi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => P t i :=
      fun i => ((ContinuousLinearMap.proj i).comp P).contDiff
    have hQi : ∀ i, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin k → ℝ => Q t i :=
      fun i => ((ContinuousLinearMap.proj i).comp Q).contDiff
    have hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) hfun :=
      Λ.contDiff.comp (contDiff_const.mul (ContDiff.sum fun i _ =>
        ((contDiff_const.mul (hQi i)).add ((hPi i).mul contDiff_const)).add ((hPi i).mul (hQi i))))
    have hre : ∀ y t, (B y t + hfun t).re = 0 := by
      intro y t; rw [hB, ← map_add]; exact hΛre _
    let K : (κ → F) → ℂ := fun x =>
      ψ ((fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)) *
        g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2)
    let G : (κ → F) → (Fin k → ℝ) → ℂ := fun x t => Complex.exp (B (yv x) t + hfun t) * f (yv x + ah + P t)
    let term : (κ → F) → (Fin k → ℝ) → ℂ := fun x t => K x * G x t

    have hid : ∀ x t, co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA F f g)
        (fun i => algebraMap F (AF F) (x i)) = term x t := by
      intro x t
      have he : co.e (w + L t) = ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0,
          (co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) := by
        rw [map_add, hPQ t]; rfl
      have hy : ∀ i, eM (algebraMap F (AF F) (x i)).1 = yv x i := by
        intro i; simp only [yv, eM]; rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl
      have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
          (((fun i => algebraMap F (AF F) (x i)) +
            ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0)) i).1) = yv x + ah + P t := by
        funext i
        change eM ((algebraMap F (AF F) (x i)).1 + (((co.e w).1 i).1 + eM.symm (P t i))) = _
        rw [map_add, map_add, RingEquiv.apply_symm_apply, hy i, ← add_assoc]
        rfl
      have h2 : (fun i => (((fun i => algebraMap F (AF F) (x i)) +
            ((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0)) i).2) =
          fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2 := by
        funext i
        change (algebraMap F (AF F) (x i)).2 + (((co.e w).1 i).2 + 0) = _
        rw [add_zero]
        rfl
      have hL : co.rho ψ (w + L t) (GlobalTheory.WeilM.pureA F f g) (fun i => algebraMap F (AF F) (x i)) =
          ψ ((fun i => algebraMap F (AF F) (x i)) ⬝ᵥ ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) +
            ⅟2 * (((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ
              ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0))) *
          (f (yv x + ah + P t) * g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) +
            ((co.e w).1 i).2)) := by
        rw [← h1, ← h2]
        show GlobalTheory.WeilM.schr ψ (co.e (w + L t)) _ _ = _
        rw [he]
        rfl
      rw [hL]
      let φ : AF F →+* mixedEmbedding.mixedSpace F := eM.toRingHom.comp (fstA F).toRingHom
      let φf : AF F →+* FiniteAdeleRing (𝓞 F) F := (sndA F).toRingHom
      have hφx : ∀ i, φ (algebraMap F (AF F) (x i)) = yv x i := hy
      have hφP : ∀ i, φ (pairA F (eM.symm (P t i)) 0) = P t i := fun i => eM.apply_symm_apply _
      have hφQ : ∀ i, φ (pairA F (eM.symm (Q t i)) 0) = Q t i := fun i => eM.apply_symm_apply _
      have hφa : ∀ i, φ ((co.e w).1 i) = ah i := fun i => rfl
      have hφb : ∀ i, φ ((co.e w).2 i) = bh i := fun i => rfl
      have hφ2 : φ ⅟2 = c2 := rfl
      have hφdef : ∀ z : AF F, eM z.1 = φ z := fun _ => rfl
      have hφfdef : ∀ z : AF F, z.2 = φf z := fun _ => rfl
      have hφpair : ∀ n, φ (pairA F (eM.symm n) 0) = n := fun n => eM.apply_symm_apply _
      have hφfpair : ∀ n, φf (pairA F (eM.symm n) 0) = 0 := fun n => rfl
      have hφfP : ∀ i, φf (pairA F (eM.symm (P t i)) 0) = 0 := fun i => rfl
      have hφfQ : ∀ i, φf (pairA F (eM.symm (Q t i)) 0) = 0 := fun i => rfl
      set X := (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (co.e w).2 + ⅟2 * ((co.e w).1 ⬝ᵥ (co.e w).2)
        with hX
      set m := ∑ i, yv x i * Q t i + c2 * ∑ i, (ah i * Q t i + P t i * bh i + P t i * Q t i) with hm
      have hsplit : (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ
            ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0) +
          ⅟2 * (((co.e w).1 + fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ
            ((co.e w).2 + fun i => pairA F (eM.symm (Q t i)) 0)) = X + pairA F (eM.symm m) 0 := by
        have hY : (fun i => algebraMap F (AF F) (x i)) ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0) +
            ⅟2 * ((co.e w).1 ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0) +
              (fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ (co.e w).2 +
              (fun i => pairA F (eM.symm (P t i)) 0) ⬝ᵥ (fun i => pairA F (eM.symm (Q t i)) 0)) =
            pairA F (eM.symm m) 0 := by
          refine Prod.ext ?_ ?_
          · apply eM.injective
            rw [hφdef, hφdef, hφpair, hm]
            simp only [dotProduct, map_add, map_mul, map_sum, hφx, hφP, hφQ, hφa, hφb, hφ2, Finset.sum_add_distrib]
          · rw [hφfdef, hφfdef, hφfpair]
            simp only [dotProduct, map_add, map_mul, map_sum, hφfP, hφfQ, mul_zero, zero_mul, Finset.sum_const_zero,
              add_zero]
        rw [← hY, hX]
        simp only [dotProduct_add, add_dotProduct]
        ring
      have hψY : ψ (pairA F (eM.symm m) 0) = Complex.exp (B (yv x) t + hfun t) := by
        change psiInf F ψ (eM.symm m) = _
        rw [hΛ, show InfiniteAdeleRing.ringEquiv_mixedSpace F = eM from rfl, RingEquiv.apply_symm_apply, hm,
          map_add]
        rfl
      rw [hsplit, AddChar.map_add_eq_mul, hψY]
      simp only [term, K, G]
      ring
    have hK : ∀ x, ‖K x‖ =
        ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) + ((co.e w).1 i).2)‖ := by
      intro x; simp only [K, norm_mul, hψ1, one_mul]
    have hG : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (G x) := fun x =>
      (Complex.contDiff_exp.comp ((B (yv x)).contDiff.add hsm)).mul
        ((f.smooth ⊤).comp (contDiff_const.add P.contDiff))
    have hsmooth : ∀ x, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (term x) := fun x => contDiff_const.mul (hG x)
    have hbd : ∀ (n : ℕ) (R : ℝ), ∃ u : (κ → F) → ℝ, Summable u ∧
        ∀ x t, ‖t‖ ≤ R → ‖iteratedFDeriv ℝ n (term x) t‖ ≤ u x := by
      intro n R
      obtain ⟨C, hC⟩ := GlobalTheory.ThetaSmooth.norm_iteratedFDeriv_exp_mul_schwartz_le f B hfun hsm hre ah P n M R
      refine ⟨fun x => C * (‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) +
        ((co.e w).1 i).2)‖ * ((1 + ‖yv x + 0‖) ^ M)⁻¹), (hM 0).mul_left C, fun x t ht => ?_⟩
      have e : term x = K x • G x := rfl
      rw [e, iteratedFDeriv_const_smul_apply ((hG x).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul, hK]
      have h1 := hC (yv x) t ht
      calc _ ≤ ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (x i) +
            ((co.e w).1 i).2)‖ * (C * ((1 + ‖yv x‖) ^ M)⁻¹) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = _ := by simp only [add_zero]; ring
    refine ⟨?_, ?_⟩
    · obtain ⟨u, hu, hu'⟩ := hbd 0 0
      refine Summable.of_norm_bounded hu fun x => ?_
      have h1 := hu' x 0 (by simp)
      rw [norm_iteratedFDeriv_zero, ← hid x 0] at h1
      simpa using h1
    · have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (GlobalTheory.WeilM.pureA F f g) (w + L t)) =
          fun t => ∑' x, term x t := funext fun t => tsum_congr fun x => hid x t
      rw [e]
      exact GlobalTheory.T.contDiff_tsum_of_summable_iteratedFDeriv_bounds term hsmooth hbd
  | zero =>
    intro w
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, rho_zero, Pi.zero_apply]
    exact ⟨summable_zero, by simpa [GlobalTheory.WeilM.thetaSum] using contDiff_const⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    intro w
    refine ⟨by rw [rho_add]; exact (h1 w).1.add (h2 w).1, ?_⟩
    have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (Φ₁ + Φ₂) (w + L t)) =
        fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₁ (w + L t) +
          GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₂ (w + L t) := by
      funext t
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_add, Pi.add_apply]
      exact (h1 (w + L t)).1.tsum_add (h2 (w + L t)).1
    rw [e]; exact (h1 w).2.add (h2 w).2
  | smul c Φ₁ _ h1 =>
    intro w
    refine ⟨by rw [rho_smul]; exact (h1 w).1.const_smul c, ?_⟩
    have e : (fun t => GlobalTheory.WeilSchrodinger.thetaTr F co ψ (c • Φ₁) (w + L t)) =
        fun t => c * GlobalTheory.WeilSchrodinger.thetaTr F co ψ Φ₁ (w + L t) := by
      funext t
      simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, rho_smul, Pi.smul_apply, smul_eq_mul]
      exact tsum_mul_left
    rw [e]; exact contDiff_const.mul (h1 w).2

end GlobalTheory.ThetaSmoothF

end
