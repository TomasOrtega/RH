import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PAnalyticGermsNoetherian
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def coordGerm {σ : Type} [Fintype σ] (w : σ → ℂ) (i : σ) : holGerms w :=
  ⟨↑(fun z : σ → ℂ => z i), fun z => z i,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w, rfl⟩

def IsFiniteGermProjection {σ : Type} [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) : Prop :=
  (∀ φ : holGerms (A w), germPull A (A.analyticAt w) rfl φ ∈ P → φ = 0) ∧
  (∀ ψ : holGerms w, ∃ F : MvPolynomial σ (holGerms (A w)),
      ψ - MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F ∈ P) ∧
  (∀ i : σ, ∃ q : Polynomial (holGerms (A w)), q.Monic ∧
      q.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w i) ∈ P)

/- English proof (translation)
Set `e : (σ → ℂ) ≃L[ℂ] (Fin (Fintype.card σ) → ℂ)` to `(LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm).toContinuousLinearEquiv`. Set `A : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ)` to `e`. Establish `hA : AnalyticAt ℂ (⇑A) w` using `A.analyticAt w`. Establish `hB : AnalyticAt ℂ (⇑e.symm) (A w)` using `e.symm.analyticAt _`. Establish `hBe : e.symm (A w) = w` using `e.symm_apply_apply w`.

Establish `back : ∀ φ : holGerms (A w), germPull e.symm hB hBe (germPull A hA rfl φ) = φ` using `fun φ => germPull_germPull _ _ hA rfl hB hBe (fun y => e.apply_symm_apply y) φ`. Establish `fwd : ∀ ψ : holGerms w, germPull A hA rfl (germPull e.symm hB hBe ψ) = ψ` using `fun ψ => germPull_germPull _ _ hB hBe hA rfl (fun z => e.symm_apply_apply z) ψ`. Use `⟨Fintype.card σ, A, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `φ hφ`. Rewrite `hφ` using `[Ideal.mem_bot]`.

Rewrite using `[← back φ, hφ, map_zero]`. Introduce `ψ`. Use `⟨MvPolynomial.C (germPull e.symm hB hBe ψ), ?_⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval₂_C, fwd, sub_self]`. Conclude with `Ideal.zero_mem _`.

Introduce `i`. Establish `hc : AnalyticAt ℂ (fun y : Fin (Fintype.card σ) → ℂ => e.symm y i) (A w)` using `((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).comp (e.symm : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))).analyticAt _`. Set `c : holGerms (A w)` to `⟨↑(fun y : Fin (Fintype.card σ) → ℂ => e.symm y i), _, hc, rfl⟩`. Use `⟨Polynomial.X - Polynomial.C c, Polynomial.monic_X_sub_C c, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_bot, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[germPull_coe _ hA rfl c _ rfl]`. Use `show (↑(fun z : σ → ℂ => z i) : Germ (𝓝 w) ℂ) = ↑((fun y => e.symm y i) ∘ ⇑A)`. Use `congr 1`. Use function extensionality and compare the values at `z`.

Simplify using `[A]`.
-/
theorem isFiniteGermProjection_bot {σ : Type} [Fintype σ] (w : σ → ℂ) :
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w ⊥ A := by
  classical
  let e : (σ → ℂ) ≃L[ℂ] (Fin (Fintype.card σ) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm).toContinuousLinearEquiv
  let A : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ) := e
  have hA : AnalyticAt ℂ (⇑A) w := A.analyticAt w
  have hB : AnalyticAt ℂ (⇑e.symm) (A w) := e.symm.analyticAt _
  have hBe : e.symm (A w) = w := e.symm_apply_apply w
  have back : ∀ φ : holGerms (A w), germPull e.symm hB hBe (germPull A hA rfl φ) = φ := fun φ =>
    germPull_germPull _ _ hA rfl hB hBe (fun y => e.apply_symm_apply y) φ
  have fwd : ∀ ψ : holGerms w, germPull A hA rfl (germPull e.symm hB hBe ψ) = ψ := fun ψ =>
    germPull_germPull _ _ hB hBe hA rfl (fun z => e.symm_apply_apply z) ψ
  refine ⟨Fintype.card σ, A, ?_, ?_, ?_⟩
  · intro φ hφ
    rw [Ideal.mem_bot] at hφ
    rw [← back φ, hφ, map_zero]
  · intro ψ
    refine ⟨MvPolynomial.C (germPull e.symm hB hBe ψ), ?_⟩
    rw [MvPolynomial.eval₂_C, fwd, sub_self]
    exact Ideal.zero_mem _
  · intro i
    have hc : AnalyticAt ℂ (fun y : Fin (Fintype.card σ) → ℂ => e.symm y i) (A w) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).comp
        (e.symm : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))).analyticAt _
    let c : holGerms (A w) := ⟨↑(fun y : Fin (Fintype.card σ) → ℂ => e.symm y i), _, hc, rfl⟩
    refine ⟨Polynomial.X - Polynomial.C c, Polynomial.monic_X_sub_C c, ?_⟩
    rw [Ideal.mem_bot, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]
    apply Subtype.ext
    rw [germPull_coe _ hA rfl c _ rfl]
    show (↑(fun z : σ → ℂ => z i) : Germ (𝓝 w) ℂ) = ↑((fun y => e.symm y i) ∘ ⇑A)
    congr 1
    funext z
    simp [A]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
