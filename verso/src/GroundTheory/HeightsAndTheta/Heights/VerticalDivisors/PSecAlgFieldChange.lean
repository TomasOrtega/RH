import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial
open scoped TensorProduct

noncomputable section

namespace SecAlgFieldChange

/- English proof (translation)
Use `letI : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) := MvPolynomial.algebraMvPolynomial`. Set `e₀ : MvPolynomial (Fin n) R ⊗[R] A ≃ₐ[R] MvPolynomial (Fin n) A` to `(Algebra.TensorProduct.comm R _ A).trans ((MvPolynomial.algebraTensorAlgEquiv R A).restrictScalars R)`. Establish `he₀ : ∀ a : A, e₀ (1 ⊗ₜ a) = C a`. Introduce `a`. Simplify using `[e₀, MvPolynomial.smul_eq_C_mul]`.

Establish `he₁ : ∀ p, e₀ (p ⊗ₜ 1) = MvPolynomial.map (algebraMap R A) p`. Introduce `p`. Simplify using `[e₀]`. Set `e : MvPolynomial (Fin n) R ⊗[R] A ≃ₐ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A` to `AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (fun p => by`. Simplify using `[Algebra.TensorProduct.algebraMap_apply, he₁])`.

Set `B` to `(Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map e.toLinearEquiv`. Establish `hB : ∀ i, B i = C (b i)`. Introduce `i`. Simplify using `only [B, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]`. Conclude with `he₀ (b i)`.

Unfold `normForm`. Rewrite using `[Algebra.norm_eq_matrix_det B]`. Use `congr 1`. Use extensionality with `i k`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, Matrix.of_apply]`.

Establish `key : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * B k = ∑ i, (∑ j, X j * C (b.repr (x j * b k) i)) • B i`. Simplify using `only [hB, Algebra.smul_def, MvPolynomial.algebraMap_def, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, ← C_mul]`.

Use `conv_lhs => rw [← b.sum_repr (x j * b k)]`. Simplify using `only [map_sum, Finset.mul_sum, Algebra.smul_def, C_mul, mul_assoc]`. Rewrite using `[key, B.repr_sum_self]`.
-/
theorem normForm_eq_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) {n : ℕ} (x : Fin n → A) :
    normForm A x = Matrix.det (Matrix.of fun i k => ∑ j, X j * C (b.repr (x j * b k) i)) := by
  letI : Algebra (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
    MvPolynomial.algebraMvPolynomial
  let e₀ : MvPolynomial (Fin n) R ⊗[R] A ≃ₐ[R] MvPolynomial (Fin n) A :=
    (Algebra.TensorProduct.comm R _ A).trans
      ((MvPolynomial.algebraTensorAlgEquiv R A).restrictScalars R)
  have he₀ : ∀ a : A, e₀ (1 ⊗ₜ a) = C a := by
    intro a; simp [e₀, MvPolynomial.smul_eq_C_mul]
  have he₁ : ∀ p, e₀ (p ⊗ₜ 1) = MvPolynomial.map (algebraMap R A) p := by
    intro p; simp [e₀]
  let e : MvPolynomial (Fin n) R ⊗[R] A ≃ₐ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A :=
    AlgEquiv.ofRingEquiv (f := e₀.toRingEquiv) (fun p => by
      simp [Algebra.TensorProduct.algebraMap_apply, he₁])
  let B := (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map e.toLinearEquiv
  have hB : ∀ i, B i = C (b i) := by
    intro i
    simp only [B, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
    exact he₀ (b i)
  unfold normForm
  rw [Algebra.norm_eq_matrix_det B]
  congr 1
  ext i k
  rw [Algebra.leftMulMatrix_eq_repr_mul, Matrix.of_apply]
  have key : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * B k =
      ∑ i, (∑ j, X j * C (b.repr (x j * b k) i)) • B i := by
    simp only [hB, Algebra.smul_def, MvPolynomial.algebraMap_def, map_sum, map_mul,
      MvPolynomial.map_X, MvPolynomial.map_C, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← C_mul]
    conv_lhs => rw [← b.sum_repr (x j * b k)]
    simp only [map_sum, Finset.mul_sum, Algebra.smul_def, C_mul, mul_assoc]
  rw [key, B.repr_sum_self]

/- English proof (translation)
Simplify using `[linForm]`.
-/
theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (u : Fin n → R) : MvPolynomial.map φ (linForm u) = linForm (φ ∘ u) := by
  simp [linForm]

/- English proof (translation)
Establish `h1 : (MvPolynomial.map φ) ∘ secForm y₀ = secForm (φ ∘ y₀)`. Use function extensionality and compare the values at `i`. Simplify using `[secForm, map_linForm]`. Both sides reduce to the same expression. Establish `h2 : MvPolynomial.map φ (chartForm y₀) = chartForm (φ ∘ y₀)`.

Simplify using `[chartForm, map_linForm]`. Both sides reduce to the same expression. Simplify using `only [secIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_sub, map_one, h2, ← Set.range_comp, h1]`.
-/
theorem secIdeal_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n e : ℕ}
    (Q₀ : Ideal (MvPolynomial (Fin n) R)) (y₀ : Par e n → R) :
    secIdeal (Q₀.map (MvPolynomial.map φ)) (φ ∘ y₀) =
      (secIdeal Q₀ y₀).map (MvPolynomial.map φ) := by
  have h1 : (MvPolynomial.map φ) ∘ secForm y₀ = secForm (φ ∘ y₀) := by
    funext i; simp [secForm, map_linForm]; rfl
  have h2 : MvPolynomial.map φ (chartForm y₀) = chartForm (φ ∘ y₀) := by
    simp [chartForm, map_linForm]; rfl
  simp only [secIdeal, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_sub, map_one, h2,
    ← Set.range_comp, h1]

end SecAlgFieldChange

/- English proof (translation)
Introduce `E₀ E _ _ φ n e Q₀ y₀ hfin`. Use `letI : Algebra E₀ E := φ.toAlgebra`. Establish `hI` using `SecAlgFieldChange.secIdeal_map φ Q₀ y₀`. Use `set Q := Q₀.map (MvPolynomial.map φ)`. Use `set y : Par e n → E := φ ∘ y₀`.

Set `g : SecAlg Q₀ y₀ →ₐ[E₀] SecAlg Q y` to `Ideal.quotientMapₐ (secIdeal Q y) (MvPolynomial.mapAlgHom (Algebra.ofId E₀ E)) (by rw [hI]; exact Ideal.le_comap_map)`. Establish `hg : ∀ p, g (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map φ p)`. Introduce `p`. Both sides reduce to the same expression. Set `ψ : SecAlg Q y →ₐ[E] E ⊗[E₀] SecAlg Q₀ y₀` to `Ideal.Quotient.liftₐ (secIdeal Q y) (aeval fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) (by`.

Introduce `a ha`. Rewrite `ha` using `[hI]`. Establish `hle : (secIdeal Q₀ y₀).map (MvPolynomial.map φ) ≤ RingHom.ker (MvPolynomial.aeval (R` using `E) fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j).toRingHom := by`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `p hp`.

Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `aeval (fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) (MvPolynomial.map (algebraMap E₀ E) p) = 0`. Rewrite using `[MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_one_tmul]`. Establish `h0 : aeval (secCoord Q₀ y₀) p = 0`. Rewrite using `[show secCoord Q₀ y₀ = (Ideal.Quotient.mkₐ E₀ (secIdeal Q₀ y₀)) ∘ X from rfl, ← MvPolynomial.aeval_unique, Ideal.Quotient.mkₐ_eq_mk]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hp`. Rewrite using `[h0, TensorProduct.tmul_zero]`. Conclude with `RingHom.mem_ker.mp (hle ha))`. Establish `hψ : ∀ p, ψ (Ideal.Quotient.mk _ p) = aeval (fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) p` using `fun p => rfl`. Set `θ : E ⊗[E₀] SecAlg Q₀ y₀ →ₐ[E] SecAlg Q y` to `Algebra.TensorProduct.lift (Algebra.ofId E _) g (fun _ _ => Commute.all _ _)`.

Establish `hθ : ∀ a, θ (1 ⊗ₜ a) = g a`. Introduce `a`. Simplify using `[θ]`. Set `eqv : E ⊗[E₀] SecAlg Q₀ y₀ ≃ₐ[E] SecAlg Q y` to `AlgEquiv.ofAlgHom θ ψ (by`. Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `j`. Use `show θ (ψ (Ideal.Quotient.mk _ (X j))) = Ideal.Quotient.mk _ (X j)`. Rewrite using `[hψ, aeval_X, hθ, secCoord, hg, map_X])`. Use the proof step `(by`.

Apply `Algebra.TensorProduct.ext` to reduce the goal to its premises. Conclude with `Subsingleton.elim _ _`. Apply `Ideal.Quotient.algHom_ext` to reduce the goal to its premises. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `j`.

Use `show ψ (θ (1 ⊗ₜ Ideal.Quotient.mk _ (X j))) = 1 ⊗ₜ Ideal.Quotient.mk _ (X j)`. Rewrite using `[hθ, hg, map_X, hψ, aeval_X]`. Use the proof step `rfl)`. Use `haveI := hfin`. Set `b` to `Module.Free.chooseBasis E₀ (SecAlg Q₀ y₀)`.

Set `B` to `(Algebra.TensorProduct.basis E b).map eqv.toLinearEquiv`. Establish `hB : ∀ a i, B.repr (g a) i = φ (b.repr a i)`. Introduce `a i`. Establish `: g a = eqv.toLinearEquiv (1 ⊗ₜ a)` using `(hθ a).symm`. Simplify using `[B, this]`.

Both sides reduce to the same expression. Establish `hBk : ∀ k, B k = g (b k)`. Introduce `k`. Simplify using `[B, eqv, hθ]`. Establish `hx : ∀ j, secCoord Q y j = g (secCoord Q₀ y₀ j)`.

Introduce `j`. Simplify using `[secCoord, hg]`. Use `⟨Module.Finite.of_basis B, ?_⟩` and prove the remaining obligations. Rewrite using `[SecAlgFieldChange.normForm_eq_det b, SecAlgFieldChange.normForm_eq_det B, RingHom.map_det]`. Use `congr 1`.

Use `Matrix.ext fun i k => ?_` and prove the remaining obligations. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C, hx, hBk]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← map_mul, hB]`.
-/
theorem SecAlgFieldChange.proof : SecAlgFieldChange.Statement := by
  intro E₀ E _ _ φ n e Q₀ y₀ hfin
  classical
  letI : Algebra E₀ E := φ.toAlgebra
  have hI := SecAlgFieldChange.secIdeal_map φ Q₀ y₀
  set Q := Q₀.map (MvPolynomial.map φ)
  set y : Par e n → E := φ ∘ y₀

  let g : SecAlg Q₀ y₀ →ₐ[E₀] SecAlg Q y :=
    Ideal.quotientMapₐ (secIdeal Q y) (MvPolynomial.mapAlgHom (Algebra.ofId E₀ E))
      (by rw [hI]; exact Ideal.le_comap_map)
  have hg : ∀ p, g (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map φ p) := by
    intro p; rfl

  let ψ : SecAlg Q y →ₐ[E] E ⊗[E₀] SecAlg Q₀ y₀ :=
    Ideal.Quotient.liftₐ (secIdeal Q y)
      (aeval fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) (by
        intro a ha
        rw [hI] at ha
        have hle : (secIdeal Q₀ y₀).map (MvPolynomial.map φ) ≤
            RingHom.ker
              (MvPolynomial.aeval (R := E) fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j).toRingHom := by
          rw [Ideal.map_le_iff_le_comap]
          intro p hp
          rw [Ideal.mem_comap, RingHom.mem_ker]
          change aeval (fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j)
            (MvPolynomial.map (algebraMap E₀ E) p) = 0
          rw [MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_one_tmul]
          have h0 : aeval (secCoord Q₀ y₀) p = 0 := by
            rw [show secCoord Q₀ y₀ = (Ideal.Quotient.mkₐ E₀ (secIdeal Q₀ y₀)) ∘ X from rfl,
              ← MvPolynomial.aeval_unique, Ideal.Quotient.mkₐ_eq_mk]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
          rw [h0, TensorProduct.tmul_zero]
        exact RingHom.mem_ker.mp (hle ha))
  have hψ : ∀ p, ψ (Ideal.Quotient.mk _ p) = aeval (fun j => (1 : E) ⊗ₜ[E₀] secCoord Q₀ y₀ j) p :=
    fun p => rfl
  let θ : E ⊗[E₀] SecAlg Q₀ y₀ →ₐ[E] SecAlg Q y :=
    Algebra.TensorProduct.lift (Algebra.ofId E _) g (fun _ _ => Commute.all _ _)
  have hθ : ∀ a, θ (1 ⊗ₜ a) = g a := by
    intro a; simp [θ]
  let eqv : E ⊗[E₀] SecAlg Q₀ y₀ ≃ₐ[E] SecAlg Q y :=
    AlgEquiv.ofAlgHom θ ψ
      (by
        apply Ideal.Quotient.algHom_ext
        apply MvPolynomial.algHom_ext
        intro j
        show θ (ψ (Ideal.Quotient.mk _ (X j))) = Ideal.Quotient.mk _ (X j)
        rw [hψ, aeval_X, hθ, secCoord, hg, map_X])
      (by
        apply Algebra.TensorProduct.ext
        · exact Subsingleton.elim _ _
        · apply Ideal.Quotient.algHom_ext
          apply MvPolynomial.algHom_ext
          intro j
          show ψ (θ (1 ⊗ₜ Ideal.Quotient.mk _ (X j))) = 1 ⊗ₜ Ideal.Quotient.mk _ (X j)
          rw [hθ, hg, map_X, hψ, aeval_X]
          rfl)
  haveI := hfin
  let b := Module.Free.chooseBasis E₀ (SecAlg Q₀ y₀)
  let B := (Algebra.TensorProduct.basis E b).map eqv.toLinearEquiv
  have hB : ∀ a i, B.repr (g a) i = φ (b.repr a i) := by
    intro a i
    have : g a = eqv.toLinearEquiv (1 ⊗ₜ a) := (hθ a).symm
    simp [B, this]
    rfl
  have hBk : ∀ k, B k = g (b k) := by
    intro k; simp [B, eqv, hθ]
  have hx : ∀ j, secCoord Q y j = g (secCoord Q₀ y₀ j) := by
    intro j; simp [secCoord, hg]
  refine ⟨Module.Finite.of_basis B, ?_⟩
  rw [SecAlgFieldChange.normForm_eq_det b, SecAlgFieldChange.normForm_eq_det B, RingHom.map_det]
  congr 1
  refine Matrix.ext fun i k => ?_
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
    MvPolynomial.map_X, MvPolynomial.map_C, hx, hBk]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← map_mul, hB]

end

end GroundTheory.Heights₂.Heights.Vertical
