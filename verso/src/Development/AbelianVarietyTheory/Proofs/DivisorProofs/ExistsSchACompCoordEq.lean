import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilEisensteinSiegelConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilSiegelFormula
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCoordinatesInInfiniteFamily

open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SchwartzCoord

variable {D : D7}

/- English proof (translation)
Set `b` to `Algebra.TensorProduct.basis (AF D.host.F) ε`. Set `c : Fin m × Fin n × Fin d → AF D.host.F` to `fun p => ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (y p), 0)`. Use `⟨fun i j => b.equivFun.symm fun k => c (i, j, k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Establish `h : coord ε (fun i j => b.equivFun.symm fun k => c (i, j, k) : Mx D m n) p = c p` using `congrFun (b.equivFun.apply_symm_apply fun k => c (p.1, p.2.1, k)) p.2.2`.

Rewrite using `[h]`. Conclude with `(InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).apply_symm_apply (y p)`.
-/
theorem exists_inf_coord {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E)
    (y : Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F) :
    ∃ x : Mx D m n, (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) = y := by
  let b := Algebra.TensorProduct.basis (AF D.host.F) ε
  let c : Fin m × Fin n × Fin d → AF D.host.F := fun p =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (y p), 0)
  refine ⟨fun i j => b.equivFun.symm fun k => c (i, j, k), ?_⟩
  funext p
  have h : coord ε (fun i j => b.equivFun.symm fun k => c (i, j, k) : Mx D m n) p = c p :=
    congrFun (b.equivFun.apply_symm_apply fun k => c (p.1, p.2.1, k)) p.2.2
  rw [h]
  exact (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).apply_symm_apply (y p)

/- English proof (translation)
Take `⟨s, -, hsf, hsi⟩` from `GlobalTheory.SchwartzBruhatTensor.exists_finSection D`. Introduce `y`. Take `⟨x, hx⟩` from `exists_inf_coord ε y`. Conclude with `⟨_, (realCoord_compAt hσ hsf hsi ε x).symm.trans hx⟩`.
-/
theorem surjective_realCoord {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ)
    {m n d : ℕ} (ε : Module.Basis (Fin d) D.host.F D.host.E) :
    Function.Surjective (realCoord σ (m := m) (n := n) ε) := by
  obtain ⟨s, -, hsf, hsi⟩ := GlobalTheory.SchwartzBruhatTensor.exists_finSection D
  intro y
  obtain ⟨x, hx⟩ := exists_inf_coord ε y
  exact ⟨_, (realCoord_compAt hσ hsf hsi ε x).symm.trans hx⟩

/- English proof (translation)
Introduce `D θ hθ m n d ε Φ hΦ`. Take `⟨σ, hσ⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Take `⟨s, -, hsf, hsi⟩` from `GlobalTheory.SchwartzBruhatTensor.exists_finSection D`. Take `⟨M, hM⟩ : ∃ M : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ] (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F), ⇑M = ⇑(realCoord σ ε)` from `⟨(realCoord σ ε).toRealLinearMap (continuous_realCoord hσ.cont ε), rfl⟩`. Establish `hMb : Function.Bijective M.toLinearMap`.

Establish `h : Function.Bijective M`. Rewrite using `[hM]`. Conclude with `⟨injective_realCoord hσ ε, surjective_realCoord hσ ε⟩`. Conclude with `h`. Take `⟨L, hL⟩ : ∃ L : (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F) ≃L[ℝ] (D.what₂.Tau → Fin m → Fin n → ℂ), ∀ c, L (M c) = c` from `⟨(LinearEquiv.ofBijective M.toLinearMap hMb).toContinuousLinearEquiv.symm, fun c => (LinearEquiv.ofBijective M.toLinearMap hMb).symm_apply_apply c⟩`.

Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `mem Φ h`. Take `⟨f, g, hg, rfl⟩` from `h`. Set `f' : SchwartzMap (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ` to `SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f`. Establish `hf' : ∀ c, f' c = f (L c)` using `fun c => rfl`.

Set `g' : (Fin m × Fin n × Fin d → Af D.host.F) → ℂ` to `g ∘ (finCoord ε).symm`. Establish `hg' : g' ∈ WeilM.SB (Fin m × Fin n × Fin d → Af D.host.F)` using `⟨hg.1.comp_continuous (finCoord ε).symm.continuous, hg.2.comp_homeomorph _⟩`. Use `⟨⟨WeilM.pureA D.host.F f' g', Submodule.subset_span ⟨f', g', hg', rfl⟩⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Use `show f' (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) * g ((finCoord ε).symm (fun p => (coord ε x p).2)) = f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))`.

Rewrite using `[realCoord_compAt hσ hsf hsi ε x, finCoord_coord ε x, ← hM, hf', hL, Homeomorph.symm_apply_apply]`. Consider the case `zero => exact ⟨0, rfl⟩`. Consider the case `add Φ Ψ _ _ h1 h2`. Take `⟨φ, rfl⟩` from `h1`. Take `⟨ψ, rfl⟩` from `h2`.

Conclude with `⟨φ + ψ, rfl⟩`. Consider the case `smul a Φ _ h`. Take `⟨φ, rfl⟩` from `h`. Conclude with `⟨a • φ, rfl⟩`.
-/
theorem exists_schA_comp_coord_eq : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n d : ℕ)
    (ε : Module.Basis (Fin d) D.host.F D.host.E), ∀ Φ ∈ schwartzA θ m n,
    ∃ φ : WeilM.schA D.host.F (Fin m × Fin n × Fin d), φ.1 ∘ coord ε = Φ := by
  intro D θ hθ m n d ε Φ hΦ
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨s, -, hsf, hsi⟩ := GlobalTheory.SchwartzBruhatTensor.exists_finSection D
  obtain ⟨M, hM⟩ : ∃ M : (D.what₂.Tau → Fin m → Fin n → ℂ) →L[ℝ]
      (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F),
      ⇑M = ⇑(realCoord σ ε) := ⟨(realCoord σ ε).toRealLinearMap (continuous_realCoord hσ.cont ε), rfl⟩
  have hMb : Function.Bijective M.toLinearMap := by
    have h : Function.Bijective M := by
      rw [hM]
      exact ⟨injective_realCoord hσ ε, surjective_realCoord hσ ε⟩
    exact h
  obtain ⟨L, hL⟩ : ∃ L : (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F) ≃L[ℝ]
      (D.what₂.Tau → Fin m → Fin n → ℂ), ∀ c, L (M c) = c :=
    ⟨(LinearEquiv.ofBijective M.toLinearMap hMb).toContinuousLinearEquiv.symm, fun c =>
      (LinearEquiv.ofBijective M.toLinearMap hMb).symm_apply_apply c⟩
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    let f' : SchwartzMap (Fin m × Fin n × Fin d → mixedEmbedding.mixedSpace D.host.F) ℂ :=
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f
    have hf' : ∀ c, f' c = f (L c) := fun c => rfl
    let g' : (Fin m × Fin n × Fin d → Af D.host.F) → ℂ := g ∘ (finCoord ε).symm
    have hg' : g' ∈ WeilM.SB (Fin m × Fin n × Fin d → Af D.host.F) :=
      ⟨hg.1.comp_continuous (finCoord ε).symm.continuous, hg.2.comp_homeomorph _⟩
    refine ⟨⟨WeilM.pureA D.host.F f' g', Submodule.subset_span ⟨f', g', hg', rfl⟩⟩, ?_⟩
    funext x
    show f' (fun p => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (coord ε x p).1) *
        g ((finCoord ε).symm (fun p => (coord ε x p).2)) =
      f (fun τ i j => compAt θ τ x i j) * g (fun i j => finPart D (x i j))
    rw [realCoord_compAt hσ hsf hsi ε x, finCoord_coord ε x, ← hM, hf', hL, Homeomorph.symm_apply_apply]
  | zero => exact ⟨0, rfl⟩
  | add Φ Ψ _ _ h1 h2 =>
    obtain ⟨φ, rfl⟩ := h1
    obtain ⟨ψ, rfl⟩ := h2
    exact ⟨φ + ψ, rfl⟩
  | smul a Φ _ h =>
    obtain ⟨φ, rfl⟩ := h
    exact ⟨a • φ, rfl⟩

end GlobalTheory.SchwartzCoord
