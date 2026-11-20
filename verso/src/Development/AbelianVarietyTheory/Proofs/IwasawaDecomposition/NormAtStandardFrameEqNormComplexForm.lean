import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrmOfPosDef
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TargetMtOfAmbTie
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbNormTie

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Simplify using `only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hform_eq_sum {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    Formalism.DivisionValues.hform H x y = ∑ i, ∑ j, star (x i) * H i j * y j := by
  simp only [Formalism.DivisionValues.hform, Matrix.toLinearMapₛₗ₂'_apply, starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use `conv_lhs => rw [← Finset.univ_sum_single x]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `: (Pi.single i (x i) : Fin n → K) = x i • Pi.single i 1`. Rewrite using `[← Pi.single_smul, smul_eq_mul, mul_one]`.

Rewrite using `[this, LinearMap.map_smulₛₗ]`.
-/
theorem j_eq_sum {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ i, σ (x i) • j (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (x i) : Fin n → K) = x i • Pi.single i 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [this, LinearMap.map_smulₛₗ]

/- English proof (translation)
Introduce `h0`. Apply `hx` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Rewrite `h0` using `[j_eq_sum]`. Use `Fintype.linearIndependent_iff.mp hli (fun i => σ (x i)) h0 i` as an intermediate fact.

Simplify using `using this`.
-/
theorem j_ne_zero {σ : K →+* ℂ} {W : Type} [AddCommGroup W] [Module ℂ W] {n : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    {x : Fin n → K} (hx : x ≠ 0) : j x ≠ 0 := by
  intro h0
  apply hx
  funext i
  rw [j_eq_sum] at h0
  have := Fintype.linearIndependent_iff.mp hli (fun i => σ (x i)) h0 i
  simpa using this

/- English proof (translation)
Unfold `Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt`. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]`.
-/
theorem normAt_sq {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι K V) (Xf : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b Xf v x ^ 2 = (Formalism.HermitianLatticesTheory.majAt b Xf v x x).re := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm Formalism.HermitianLatticesTheory.majAt
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/- English proof (translation)
Break down `InfinitePlace.embedding_mk_eq σ with he | he` into its components or cases. Use `left`. Introduce `x y`. Rewrite using `[hin, hform_eq_sum, hAt, he]`. Simplify using `only [map_sum, map_mul, hσ]`.

Both sides reduce to the same expression. Use `right`. Introduce `x y`. Rewrite using `[hin, hform_eq_sum, hAt, he]`. Simplify using `only [map_sum, map_mul, hσ, star_sum, star_mul', ComplexEmbedding.conjugate_coe_eq, Complex.star_def]`.
-/
theorem hAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H : Matrix (Fin n) (Fin n) K)
    (hin : ∀ x y, inner ℂ (j x) (j y) = σ (Formalism.DivisionValues.hform H x y)) :
    (∀ x y, hAt H (InfinitePlace.mk σ) x y = inner ℂ (j x) (j y)) ∨
      (∀ x y, hAt H (InfinitePlace.mk σ) x y = star (inner ℂ (j x) (j y))) := by
  rcases InfinitePlace.embedding_mk_eq σ with he | he
  · left
    intro x y
    rw [hin, hform_eq_sum, hAt, he]
    simp only [map_sum, map_mul, hσ]
    rfl
  · right
    intro x y
    rw [hin, hform_eq_sum, hAt, he]
    simp only [map_sum, map_mul, hσ, star_sum, star_mul', ComplexEmbedding.conjugate_coe_eq, Complex.star_def]

/- English proof (translation)
Establish `hd : ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ)`. Introduce `x`. Break down `hAt_mk hσ j H hT.inner with h | h` into its components or cases. Rewrite using `[h, inner_self_eq_norm_sq_to_K]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite using `[h, inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Simplify using `[Complex.star_def]`. Use `⟨⟨fun x y => ?_, fun x hx => ?_⟩, hd⟩` and prove the remaining obligations.

Break down `hAt_mk hσ j H hT.inner with h | h` into its components or cases. Rewrite using `[h, h]`. Conclude with `(inner_conj_symm (j y) (j x)).symm`. Rewrite using `[h, h, star_star]`. Conclude with `inner_conj_symm (j x) (j y)`.

Rewrite using `[hd, Complex.ofReal_re]`. Conclude with `pow_pos (norm_pos_iff.mpr (j_ne_zero j hT.li hx)) 2`.
-/
theorem posAt_mk {σ : K →+* ℂ} (hσ : ∀ a, σ (star a) = starRingEnd ℂ (σ a)) {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K)
    (op : W →ₗ[ℂ] W) (hT : FormsTie σ j H E op) :
    PosAt H (InfinitePlace.mk σ) ∧ ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
  have hd : ∀ x, hAt H (InfinitePlace.mk σ) x x = ((‖j x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    · rw [h, inner_self_eq_norm_sq_to_K]; push_cast; simp [Complex.star_def]
  refine ⟨⟨fun x y => ?_, fun x hx => ?_⟩, hd⟩
  · rcases hAt_mk hσ j H hT.inner with h | h
    · rw [h, h]; exact (inner_conj_symm (j y) (j x)).symm
    · rw [h, h, star_star]; exact inner_conj_symm (j x) (j y)
  · rw [hd, Complex.ofReal_re]
    exact pow_pos (norm_pos_iff.mpr (j_ne_zero j hT.li hx)) 2

end GlobalTheory.AmbNormTie

open GlobalTheory.AmbNormTie in

/- English proof (translation)
Introduce `K _ _ _ _ σ hσ W _ _ n j H E op hT x`. Take `⟨hP, hd⟩` from `posAt_mk hσ j H E op hT`. Establish `hPD` using `GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H (InfinitePlace.mk σ) hP`. Establish `hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x x = hAt H (InfinitePlace.mk σ) x x`. Rewrite using `[Formalism.L2.DIV.majAt_eq, GlobalTheory.AmbCrd.frm_of_posDef H _ hPD, (Formalism.L2.DIV.frameOfSpec _ _ hPD).2, GlobalTheory.Core.AmbTieStep.hAt_eq_dot]`.

Establish `h2` using `normAt_sq (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x`. Rewrite `h2` using `[hmaj, hd, Complex.ofReal_re]`. Establish `h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x` using `Real.sqrt_nonneg _`. Conclude with `(pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).mp h2`.
-/
theorem GlobalTheory.AmbNormTie.normAt_frm_mk : ∀ {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (σ : K →+* ℂ), (∀ a, σ (star a) = starRingEnd ℂ (σ a)) → ∀ {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W), Formalism.L2.DIV.FormsTie σ j H E op → ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x = ‖j x‖ := by
  intro K _ _ _ _ σ hσ W _ _ n j H E op hT x
  obtain ⟨hP, hd⟩ := posAt_mk hσ j H E op hT
  have hPD := GlobalTheory.T.posDef_map_embedding_of_positiveAtPlace H (InfinitePlace.mk σ) hP
  have hmaj : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x x =
      hAt H (InfinitePlace.mk σ) x x := by
    rw [Formalism.L2.DIV.majAt_eq, GlobalTheory.AmbCrd.frm_of_posDef H _ hPD, (Formalism.L2.DIV.frameOfSpec _ _ hPD).2,
      GlobalTheory.Core.AmbTieStep.hAt_eq_dot]
  have h2 := normAt_sq (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x
  rw [hmaj, hd, Complex.ofReal_re] at h2
  have h0 : 0 ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) (GlobalTheory.AmbCrd.frm H) (InfinitePlace.mk σ) x :=
    Real.sqrt_nonneg _
  exact (pow_left_inj₀ h0 (norm_nonneg _) two_ne_zero).mp h2
