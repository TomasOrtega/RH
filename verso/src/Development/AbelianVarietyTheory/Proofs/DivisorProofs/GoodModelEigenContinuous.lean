import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocCharEqValZpow
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfTensEqOfNeZero

noncomputable section

open scoped TensorProduct NNReal Matrix nonZeroDivisors
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnrEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)
open scoped GlobalTheory.VacAny

namespace GlobalTheory.ThK.EvLocInv

open scoped Classical in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d n₁ d₁ X W X₁ W₁ B M M₁ ι ι' I e hE hψ hM hM₁ ei ev hei hev hloc v γ hγ hat φ hφ`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hei (ContinuousLinearMap.ext h)`.

Take `⟨r₀, hr₀, hr₀t⟩` from `GlobalTheory.PureFactor.exists_rest_factor v f M.vac hM.std`. Take `⟨r₁, hr₁, hr₁t⟩` from `GlobalTheory.PureFactor.exists_rest_factor v (ei f) M₁.vac hM₁.std`. Establish `hr₁0 : r₁ ≠ 0`. Establish `ht : tens (evFin F v) (fun _ => (1 : ℂ)) r₁ = r₁`. Use function extensionality and compare the values at `x`.

Simplify using `[tens]`. Establish `h1` using `hr₁t (fun _ => 1)`. Rewrite `h1` using `[ht]`. Rewrite using `[h1]`. Use `GlobalTheory.EvNonzero.pure_ne_zero (ei f) hf _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v _ hM₁.std)` and prove the remaining obligations.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`. Introduce `h`. Conclude with `one_ne_zero (congrFun h 0)`.

Rewrite using `[Function.update_of_ne hw]`. Conclude with `(hM₁.vac w).2.1`. Establish `hupd : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ w, Function.update M.vac v φ w ∈ SB _`. Introduce `φ hφ w`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `hφ`. Rewrite using `[Function.update_of_ne hw]`. Conclude with `(hM.vac w).1`.

Establish `hRest : Rest (evFin F v) φ r₀` using `⟨hr₀, by`. Rewrite using `[hr₀t φ]`. Conclude with `GlobalTheory.TensUniq.pure_mem_schA f _ (hupd φ hφ) (GlobalTheory.PureFactor.update_eventually _ v φ hM.std)⟩`. Establish `hev_pure : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), e (tens (evFin F v) φ r₀) = tens (evFin F v) (ev v φ) r₁`. Introduce `φ hφ`.

Establish `hc : ∀ᶠ w in cofinite, Function.update M.vac v φ w = M.vac w` using `by filter_upwards [Filter.eventually_cofinite_ne v] with w hw`. Rewrite using `[Function.update_of_ne hw]`. Establish `hfun : (fun w => ev w (Function.update M.vac v φ w)) = Function.update M₁.vac v (ev v φ)`. Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Simplify using `only [Function.update_self]`. Simplify using `only [Function.update_of_ne hw, (hev w).1]`. Rewrite using `[hr₀t φ, hloc f _ (hupd φ hφ) hc, hfun, hr₁t]`. Establish `hA` using `GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hat φ`.

Establish `hφ₁` using `GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v (GlobalTheory.LatVac.locCo M.co v γ) φ hφ`. Apply `GlobalTheory.ThK.EvZeroFinLoc.eq_of_tens_eq_of_ne_zero v r₁ hr₁ hr₁0` to reduce the goal to its premises. Rewrite using `[← hev_pure _ hφ₁, ← hA r₀ hRest, hE.inv γ hγ _ hRest.2, hev_pure φ hφ]`.
-/
theorem ev_schr_of_mem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d n₁ d₁ : ℕ}
    {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (B : Base F E) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (I : Set (Matrix (Fin n) (Fin d) (AE F E)))
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁), IsEv B M M₁ ι ι' I e → Continuous B.ψ → M.IsGood B.ψ → M₁.IsGood B.ψ →
    ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
      (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ), ei ≠ 0 →
      (∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
      ∀ (v : Pl F) (γ : Matrix (Fin n) (Fin d) (AE F E)), γ ∈ I → At (evFin F v) γ →
      ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev v (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ) = ev v φ := by
  intro F E _ _ _ _ _ σ n d n₁ d₁ X W X₁ W₁ B M M₁ ι ι' I e hE hψ hM hM₁ ei ev hei hev hloc v γ hγ hat φ hφ
  obtain ⟨f, hf⟩ : ∃ f, ei f ≠ 0 := by
    by_contra h
    push_neg at h
    exact hei (ContinuousLinearMap.ext h)
  obtain ⟨r₀, hr₀, hr₀t⟩ := GlobalTheory.PureFactor.exists_rest_factor v f M.vac hM.std
  obtain ⟨r₁, hr₁, hr₁t⟩ := GlobalTheory.PureFactor.exists_rest_factor v (ei f) M₁.vac hM₁.std
  have hr₁0 : r₁ ≠ 0 := by
    have ht : tens (evFin F v) (fun _ => (1 : ℂ)) r₁ = r₁ := by
      funext x
      simp [tens]
    have h1 := hr₁t (fun _ => 1)
    rw [ht] at h1
    rw [h1]
    refine GlobalTheory.EvNonzero.pure_ne_zero (ei f) hf _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually _ v _ hM₁.std)
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      intro h
      exact one_ne_zero (congrFun h 0)
    · rw [Function.update_of_ne hw]
      exact (hM₁.vac w).2.1
  have hupd : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ w, Function.update M.vac v φ w ∈ SB _ := by
    intro φ hφ w
    by_cases hw : w = v
    · subst hw
      rw [Function.update_self]
      exact hφ
    · rw [Function.update_of_ne hw]
      exact (hM.vac w).1
  have hRest : Rest (evFin F v) φ r₀ :=
    ⟨hr₀, by
      rw [hr₀t φ]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ (hupd φ hφ) (GlobalTheory.PureFactor.update_eventually _ v φ hM.std)⟩
  have hev_pure : ∀ φ ∈ SB (Fin n × Fin d → Fv F v), e (tens (evFin F v) φ r₀) = tens (evFin F v) (ev v φ) r₁ := by
    intro φ hφ
    have hc : ∀ᶠ w in cofinite, Function.update M.vac v φ w = M.vac w := by
      filter_upwards [Filter.eventually_cofinite_ne v] with w hw
      rw [Function.update_of_ne hw]
    have hfun : (fun w => ev w (Function.update M.vac v φ w)) = Function.update M₁.vac v (ev v φ) := by
      funext w
      by_cases hw : w = v
      · subst hw
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hw, (hev w).1]
    rw [hr₀t φ, hloc f _ (hupd φ hφ) hc, hfun, hr₁t]
  have hA := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hat φ
  have hφ₁ := GlobalTheory.SchrSB.schr_mem_SB B.ψ hψ v (GlobalTheory.LatVac.locCo M.co v γ) φ hφ
  apply GlobalTheory.ThK.EvZeroFinLoc.eq_of_tens_eq_of_ne_zero v r₁ hr₁ hr₁0
  rw [← hev_pure _ hφ₁, ← hA r₀ hRest, hE.inv γ hγ _ hRest.2, hev_pure φ hφ]

end GlobalTheory.ThK.EvLocInv

end
