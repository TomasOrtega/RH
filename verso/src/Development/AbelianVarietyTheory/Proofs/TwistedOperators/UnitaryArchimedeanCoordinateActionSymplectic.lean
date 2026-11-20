import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

namespace GlobalTheory.ArchLine

/- English proof (translation)
Establish `tr : ∀ N : Matrix α α E, ∑ i, ∑ k, JA i k * N i k = (JAᵀ * N).trace` using `fun N => by`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]`. Conclude with `Finset.sum_comm`. Establish `h1 : ((p.1 : GL α E) : Matrix α α E)ᵀ * JA * ((p.1 : GL α E) : Matrix α α E).map c = JA` using `p.1.2`. Establish `h2 : ((p.2 : GL β E) : Matrix β β E)ᵀ * JB * ((p.2 : GL β E) : Matrix β β E).map c = JB` using `p.2.2`.

Rewrite using `[Coord.hTens_eq, Coord.hTens_eq, tr, tr, actAB, actAB]`. Generalize the expression as in `((p.1 : GL α E) : Matrix α α E) = g at h1 ⊢`. Generalize the expression as in `((p.2 : GL β E) : Matrix β β E) = h at h2 ⊢`. Establish `e1 : ((g * y * hᵀ).map c)ᵀ = h.map c * (y.map c)ᵀ * (g.map c)ᵀ`. Rewrite using `[Matrix.map_mul (f := c), Matrix.map_mul (f := c), Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]`.

Both sides reduce to the same expression. Establish `e2 : JAᵀ * (g * x * hᵀ * JB * (h.map c * (y.map c)ᵀ * (g.map c)ᵀ)) = JAᵀ * g * (x * (hᵀ * JB * h.map c) * (y.map c)ᵀ) * (g.map c)ᵀ` using `by simp only [Matrix.mul_assoc]`. Establish `e3 : (g.map c)ᵀ * (JAᵀ * g) = JAᵀ` using `by conv_rhs => rw [← h1]`. Simplify using `only [Matrix.transpose_mul, Matrix.transpose_transpose]`. Rewrite using `[e1, e2, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, e3]`.
-/
theorem hTens_actAB_unitary {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {JA : Matrix α α E} {JB : Matrix β β E}
    (p : UG c JA × UG c JB) (x y : Matrix α β E) :
    hTens c JA JB (actAB c p x) (actAB c p y) = hTens c JA JB x y := by
  have tr : ∀ N : Matrix α α E, ∑ i, ∑ k, JA i k * N i k = (JAᵀ * N).trace := fun N => by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_comm
  have h1 : ((p.1 : GL α E) : Matrix α α E)ᵀ * JA * ((p.1 : GL α E) : Matrix α α E).map c = JA := p.1.2
  have h2 : ((p.2 : GL β E) : Matrix β β E)ᵀ * JB * ((p.2 : GL β E) : Matrix β β E).map c = JB := p.2.2
  rw [Coord.hTens_eq, Coord.hTens_eq, tr, tr, actAB, actAB]
  generalize ((p.1 : GL α E) : Matrix α α E) = g at h1 ⊢
  generalize ((p.2 : GL β E) : Matrix β β E) = h at h2 ⊢
  have e1 : ((g * y * hᵀ).map c)ᵀ = h.map c * (y.map c)ᵀ * (g.map c)ᵀ := by
    rw [Matrix.map_mul (f := c), Matrix.map_mul (f := c), Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rfl
  have e2 : JAᵀ * (g * x * hᵀ * JB * (h.map c * (y.map c)ᵀ * (g.map c)ᵀ)) =
      JAᵀ * g * (x * (hᵀ * JB * h.map c) * (y.map c)ᵀ) * (g.map c)ᵀ := by simp only [Matrix.mul_assoc]
  have e3 : (g.map c)ᵀ * (JAᵀ * g) = JAᵀ := by
    conv_rhs => rw [← h1]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [e1, e2, h2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, e3]

/- English proof (translation)
Establish `hv` using `coordI_lift M v`. Establish `hv'` using `coordI_lift M v'`. Use `conv_rhs => rw [← hv, ← hv']`. Rewrite using `[archAct, archAct, omega_coordI, omega_coordI]`. Simplify using `only [sympM, symp, hTens_actAB_unitary]`.
-/
theorem omega_archAct {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (h : UA σ W.J)
    (v v' : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    omega (trP F (Fin n × Fin d)) (archAct M h v) (archAct M h v') = omega (trP F (Fin n × Fin d)) v v' := by
  have hv := coordI_lift M v
  have hv' := coordI_lift M v'
  conv_rhs => rw [← hv, ← hv']
  rw [archAct, archAct, omega_coordI, omega_coordI]
  simp only [sympM, symp, hTens_actAB_unitary]

end GlobalTheory.ArchLine
