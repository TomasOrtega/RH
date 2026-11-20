import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoreR
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GaussQ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexCoordinatesExistAtInfinity
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec

open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.CoordCM

/- English proof (translation)
Take `⟨θ₀, hθ₀⟩` from `exists_moved h`. Establish `hb0 : b 0 ≠ 0` using `b.ne_zero 0`. Take `⟨θ, hθ⟩ : ∃ θ : E, θ * b 0 = b 1` from `⟨b 1 / b 0, div_mul_cancel₀ _ hb0⟩`. Establish `hmoved : σ θ ≠ θ`. Introduce `hfix`.

Apply `hθ₀` to reduce the goal to its premises. Take `⟨A, B, hAB⟩ : ∃ A B : F, θ₀ * b 0 = algebraMap F E A * b 0 + algebraMap F E B * b 1` from `⟨_, _, by`. Use `b.sum_repr (θ₀ * b 0)` as an intermediate fact. Rewrite `this` using `[Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def]`. Conclude with `this.symm⟩`.

Establish `h1 : θ₀ = algebraMap F E A + algebraMap F E B * θ`. Apply `mul_right_cancel₀ hb0` to reduce the goal to its premises. Rewrite using `[add_mul, mul_assoc, hθ]`. Conclude with `hAB`. Rewrite using `[h1, map_add, map_mul, hfix, AlgHom.commutes, AlgHom.commutes]`.

Establish `him : (τ θ).im ≠ 0` using `im_ne_zero h hmoved τ`. Establish `hb1 : τ (b 1) = τ θ * τ (b 0)` using `by rw [← map_mul, hθ]`. Establish `ht0 : τ (b 0) ≠ 0` using `(map_ne_zero τ).2 hb0`. Establish `h2 : (s : ℂ) + t * τ θ = 0`. Apply `mul_right_cancel₀ ht0` to reduce the goal to its premises.

Rewrite using `[zero_mul, add_mul, mul_assoc, ← hb1]`. Conclude with `hst`. Establish `hi` using `congrArg Complex.im h2`. Simplify using `only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add, zero_mul, add_zero, Complex.zero_im] at hi`. Establish `ht : t = 0` using `(mul_eq_zero.1 hi).resolve_right him`.

Substitute `ht` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Simplify using `using h2`.
-/
theorem real_indep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (b : Module.Basis (Fin 2) F E) (τ : E →+* ℂ) (s t : ℝ)
    (hst : (s : ℂ) * τ (b 0) + (t : ℂ) * τ (b 1) = 0) : s = 0 ∧ t = 0 := by
  obtain ⟨θ₀, hθ₀⟩ := exists_moved h
  have hb0 : b 0 ≠ 0 := b.ne_zero 0
  obtain ⟨θ, hθ⟩ : ∃ θ : E, θ * b 0 = b 1 := ⟨b 1 / b 0, div_mul_cancel₀ _ hb0⟩
  have hmoved : σ θ ≠ θ := by
    intro hfix
    apply hθ₀
    obtain ⟨A, B, hAB⟩ : ∃ A B : F,
        θ₀ * b 0 = algebraMap F E A * b 0 + algebraMap F E B * b 1 :=
      ⟨_, _, by
        have := b.sum_repr (θ₀ * b 0)
        rw [Fin.sum_univ_two, Algebra.smul_def, Algebra.smul_def] at this
        exact this.symm⟩
    have h1 : θ₀ = algebraMap F E A + algebraMap F E B * θ := by
      apply mul_right_cancel₀ hb0
      rw [add_mul, mul_assoc, hθ]
      exact hAB
    rw [h1, map_add, map_mul, hfix, AlgHom.commutes, AlgHom.commutes]
  have him : (τ θ).im ≠ 0 := im_ne_zero h hmoved τ
  have hb1 : τ (b 1) = τ θ * τ (b 0) := by rw [← map_mul, hθ]
  have ht0 : τ (b 0) ≠ 0 := (map_ne_zero τ).2 hb0
  have h2 : (s : ℂ) + t * τ θ = 0 := by
    apply mul_right_cancel₀ ht0
    rw [zero_mul, add_mul, mul_assoc, ← hb1]
    exact hst
  have hi := congrArg Complex.im h2
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_add,
    zero_mul, add_zero, Complex.zero_im] at hi
  have ht : t = 0 := (mul_eq_zero.1 hi).resolve_right him
  subst ht
  refine ⟨?_, rfl⟩
  simpa using h2

/- English proof (translation)
Use `conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]`. Rewrite using `[Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', TensorProduct.smul_tmul']`. Simplify using the standard rewrite rules.
-/
theorem eq_coord {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (b : Module.Basis (Fin 2) F E) (y : R ⊗[F] E) :
    y = (Algebra.TensorProduct.basis R b).repr y 0 ⊗ₜ[F] b 0 +
      (Algebra.TensorProduct.basis R b).repr y 1 ⊗ₜ[F] b 1 := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]
  rw [Fin.sum_univ_two, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.basis_apply,
    TensorProduct.smul_tmul', TensorProduct.smul_tmul']
  simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h M d b ρ e hρ he hx X hX`. Use `haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)`. Choose the witnesses or unpack the hypotheses as in `rfl : d = 2 := by`. Use `Module.finrank_eq_card_basis b` as an intermediate fact. Rewrite `this` using `[h.2.2.1]`.

Simplify using `using this.symm`. Establish `hex : ∀ w : InfinitePlace F, ∃ t : E →+* ℂ, ∀ x, t (algebraMap F E x) = w.embedding x`. Introduce `w`. Use `letI : Algebra F ℂ := w.embedding.toAlgebra`. Set `t : E →ₐ[F] ℂ` to `IsAlgClosed.lift`.

Conclude with `⟨t, fun x => t.commutes x⟩`. Use `choose τ hτ using hex`. Take `⟨Θ, hΘ⟩` from `exists_hom e τ (fun x w => by rw [hx, hρ, hτ])`. Establish `key : ∀ (y : Ainf F ⊗[F] E) (w : InfinitePlace F), Θ y w = 0 → ∀ k, e ((Algebra.TensorProduct.basis (Ainf F) b).repr y k) w = 0`. Introduce `y w hy k`.

Establish `h1 : Θ y w = (e ((Algebra.TensorProduct.basis (Ainf F) b).repr y 0) w : ℂ) * τ w (b 0) + (e ((Algebra.TensorProduct.basis (Ainf F) b).repr y 1) w : ℂ) * τ w (b 1)` using `by conv_lhs => rw [eq_coord b y, map_add, Pi.add_apply, hΘ, hΘ]`. Rewrite `h1` using `[hy]`. Take `⟨h0, h1'⟩` from `real_indep h b (τ w) _ _ h1.symm`. Use `fin_cases k`. Conclude with `h0`.

Conclude with `h1'`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Establish `hg' : ∀ j, g 0 * X 0 j = 0` using `fun j => by simpa using congrFun hg j`.

Establish `hw : ∀ w, Θ (g 0) w = 0`. Introduce `w`. Take `⟨⟨j, k⟩, hjk⟩` from `Function.ne_iff.1 (hX w)`. Establish `hne : Θ (X 0 j) w ≠ 0` using `fun h0 => hjk (key _ _ h0 k)`. Establish `h3` using `congrFun (congrArg Θ (hg' j)) w`.

Rewrite `h3` using `[map_mul, Pi.mul_apply, map_zero]`. Conclude with `(mul_eq_zero.1 h3).resolve_right hne`. Use `(Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_` and prove the remaining obligations. Rewrite using `[map_zero, Finsupp.zero_apply]`. Apply `e.injective` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use function extensionality and compare the values at `w`. Conclude with `key _ _ (hw w) k`.
-/
theorem linearIndependent_of_xw_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M d : ℕ) (b : Module.Basis (Fin d) F E) (ρ : InfinitePlace F → (F →+* ℝ)) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → IsHomeomorph e → (∀ x w, e (algebraMap F (Ainf F) x) w = ρ w x) → ∀ X : Fin 1 → Fin M → Ainf F ⊗[F] E, (∀ w, xw e b X w ≠ 0) → LinearIndependent (Ainf F ⊗[F] E) X := by
  intro F E _ _ _ _ _ σ h M d b ρ e hρ he hx X hX
  classical
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [h.2.2.1]; norm_num)
  obtain rfl : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [h.2.2.1] at this
    simpa using this.symm
  have hex : ∀ w : InfinitePlace F, ∃ t : E →+* ℂ, ∀ x, t (algebraMap F E x) = w.embedding x := by
    intro w
    letI : Algebra F ℂ := w.embedding.toAlgebra
    let t : E →ₐ[F] ℂ := IsAlgClosed.lift
    exact ⟨t, fun x => t.commutes x⟩
  choose τ hτ using hex
  obtain ⟨Θ, hΘ⟩ := exists_hom e τ (fun x w => by rw [hx, hρ, hτ])
  have key : ∀ (y : Ainf F ⊗[F] E) (w : InfinitePlace F), Θ y w = 0 →
      ∀ k, e ((Algebra.TensorProduct.basis (Ainf F) b).repr y k) w = 0 := by
    intro y w hy k
    have h1 : Θ y w = (e ((Algebra.TensorProduct.basis (Ainf F) b).repr y 0) w : ℂ) * τ w (b 0) +
        (e ((Algebra.TensorProduct.basis (Ainf F) b).repr y 1) w : ℂ) * τ w (b 1) := by
      conv_lhs => rw [eq_coord b y, map_add, Pi.add_apply, hΘ, hΘ]
    rw [hy] at h1
    obtain ⟨h0, h1'⟩ := real_indep h b (τ w) _ _ h1.symm
    fin_cases k
    · exact h0
    · exact h1'
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain rfl : i = 0 := Subsingleton.elim _ _
  have hg' : ∀ j, g 0 * X 0 j = 0 := fun j => by simpa using congrFun hg j
  have hw : ∀ w, Θ (g 0) w = 0 := by
    intro w
    obtain ⟨⟨j, k⟩, hjk⟩ := Function.ne_iff.1 (hX w)
    have hne : Θ (X 0 j) w ≠ 0 := fun h0 => hjk (key _ _ h0 k)
    have h3 := congrFun (congrArg Θ (hg' j)) w
    rw [map_mul, Pi.mul_apply, map_zero] at h3
    exact (mul_eq_zero.1 h3).resolve_right hne
  refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply e.injective
  rw [map_zero]
  funext w
  exact key _ _ (hw w) k

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0.FreeVec
