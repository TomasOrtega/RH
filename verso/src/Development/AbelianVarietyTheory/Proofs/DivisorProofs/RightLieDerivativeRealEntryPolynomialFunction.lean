import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct

namespace GlobalTheory.PolyRightDeriv

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simpa [MvPolynomial.derivation_C] using hasDerivAt_const (0 : ℝ) a`. Consider the case `add P Q hP hQ => simp only [map_add]`. Conclude with `hP.add hQ`. Consider the case `mul_X P p hP`.

Use `hP.mul (h p)` as an intermediate fact. Simplify using `only [map_mul, MvPolynomial.eval_X, Derivation.leibniz, smul_eq_mul, map_add]`. Conclude with `this.congr_deriv (by ring)`.
-/
theorem hasDerivAt_eval {σ : Type} (δ : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (c : ℝ → σ → ℂ)
    (h : ∀ p, HasDerivAt (fun t => c t p) (MvPolynomial.eval (c 0) (δ (MvPolynomial.X p))) 0) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (c t) P) (MvPolynomial.eval (c 0) (δ P)) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.derivation_C] using hasDerivAt_const (0 : ℝ) a
  | add P Q hP hQ => simp only [map_add]; exact hP.add hQ
  | mul_X P p hP =>
    have := hP.mul (h p)
    simp only [map_mul, MvPolynomial.eval_X, Derivation.leibniz, smul_eq_mul, map_add]
    exact this.congr_deriv (by ring)

/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Use `haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _`. Establish `h` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ` to `{ toFun := fun B => (A * B) i j map_add' := fun B C => by simp [mul_add] map_smul' := fun c B => by simp }`.

Establish `h2` using `(LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h`. Rewrite `h2` using `[zero_smul, NormedSpace.exp_zero, one_mul]`. Conclude with `h2`.
-/
theorem hasDerivAt_entry {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (A * NormedSpace.exp (t • X)) i j) ((A * X) i j) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun B => (A * B) i j
      map_add' := fun B C => by simp [mul_add]
      map_smul' := fun c B => by simp }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

/- English proof (translation)
Use function extensionality and compare the values at `g`. Set `c : ℝ → D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ` to `fun t => realEntries θ V (g * expInf θ V (t • atPlace V τ X))`. Establish `hc : ∀ t p, c t p = (infMat D.sp.cm.sig V.gram (θ p.1) g * NormedSpace.exp (t • (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) p.2.1 p.2.2` using `fun t p => by`. Simplify using `only [c, realEntries]`. Rewrite using `[R.2.2.2.1, (isExpFam_expInf R (t • atPlace V τ X)).2]`.

Both sides reduce to the same expression. Establish `h0 : c 0 = realEntries θ V g` using `funext fun p => by`. Rewrite using `[hc, zero_smul, NormedSpace.exp_zero, mul_one]`. Both sides reduce to the same expression. Establish `h` using `hasDerivAt_eval (matDer τ X.1) c (fun p => by`.

Simplify using `only [hc]`. Apply the tactic sequence `convert hasDerivAt_entry (infMat D.sp.cm.sig V.gram (θ p.1) g) (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) p.2.1 p.2.2 using 1`. Rewrite using `[h0, matDer_X]`. Take `⟨τ', i, j⟩` from `p`. Distinguish the cases in `e : τ' = τ`.

Substitute `e` using the available equality. Simplify using `[atPlace, Matrix.mul_apply, realEntries]`. Simplify using `[atPlace, e, Pi.single_eq_of_ne e]) P`. Rewrite `h` using `[h0]`. Conclude with `h.deriv`.
-/
theorem lieDer_polyFun (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V) :
    lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := by
  classical
  funext g
  let c : ℝ → D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ :=
    fun t => realEntries θ V (g * expInf θ V (t • atPlace V τ X))
  have hc : ∀ t p, c t p = (infMat D.sp.cm.sig V.gram (θ p.1) g *
      NormedSpace.exp (t • (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) p.2.1 p.2.2 := fun t p => by
    simp only [c, realEntries]
    rw [R.2.2.2.1, (isExpFam_expInf R (t • atPlace V τ X)).2]
    rfl
  have h0 : c 0 = realEntries θ V g := funext fun p => by
    rw [hc, zero_smul, NormedSpace.exp_zero, mul_one]; rfl
  have h := hasDerivAt_eval (matDer τ X.1) c (fun p => by
    simp only [hc]
    convert hasDerivAt_entry (infMat D.sp.cm.sig V.gram (θ p.1) g)
      (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) p.2.1 p.2.2 using 1
    rw [h0, matDer_X]
    obtain ⟨τ', i, j⟩ := p
    by_cases e : τ' = τ
    · subst e
      simp [atPlace, Matrix.mul_apply, realEntries]
    · simp [atPlace, e, Pi.single_eq_of_ne e]) P
  rw [h0] at h
  exact h.deriv

end GlobalTheory.PolyRightDeriv

end
