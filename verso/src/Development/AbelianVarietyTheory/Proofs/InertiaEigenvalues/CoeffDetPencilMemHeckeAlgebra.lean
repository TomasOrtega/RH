import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ResidualConstruction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDetGenericSumMemHeckeAlgebraStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.SpanRing

/- English proof (translation)
Rewrite using `[← MvPolynomial.mem_homogeneousSubmodule, Matrix.det_apply]`. Use `Submodule.sum_mem _ fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def]`. Use `Submodule.smul_of_tower_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.mem_homogeneousSubmodule]`.

Use `MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n)) (fun i => M (τ i) i) (fun _ => 1) (fun i _ => h (τ i) i)` as an intermediate fact. Simplify using `using this`.
-/
theorem isHomogeneous_det_of_linear {σ R : Type} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ R)) (h : ∀ i j, (M i j).IsHomogeneous 1) :
    M.det.IsHomogeneous n := by
  rw [← MvPolynomial.mem_homogeneousSubmodule, Matrix.det_apply]
  refine Submodule.sum_mem _ fun τ _ => ?_
  rw [Units.smul_def]
  refine Submodule.smul_of_tower_mem _ _ ?_
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin n))
    (fun i => M (τ i) i) (fun _ => 1) (fun i _ => h (τ i) i)
  simpa using this

/- English proof (translation)
Use `conv_lhs => rw [MvPolynomial.as_sum P]`. Rewrite using `[map_sum, Polynomial.finsetSum_coeff]`. Establish `hterm : ∀ d : Fin 2 →₀ ℕ, (MvPolynomial.aeval ![(Polynomial.X : Polynomial R), 1] (MvPolynomial.monomial d (MvPolynomial.coeff d P))).coeff j = if d 0 = j then MvPolynomial.coeff d P else 0`. Introduce `d`. Rewrite using `[MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]`.

Simplify using `[Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, eq_comm]`. Repeatedly rewrite using `[hterm]`. Use `Finset.sum_subset ?_ ?_` and prove the remaining obligations. Introduce `d hd`. Rewrite using `[Finset.mem_finsuppAntidiag]`.

Use `⟨?_, by simp⟩` and prove the remaining obligations. Establish `hd' : MvPolynomial.coeff d P ≠ 0` using `MvPolynomial.mem_support_iff.mp hd`. Use `h hd'` as an intermediate fact. Simplify `this` using `[Finsupp.weight_apply, Finsupp.sum_fintype]`. Introduce `d _ hd`.

Rewrite using `[MvPolynomial.notMem_support_iff.mp hd]`. Simplify using the standard rewrite rules.
-/
theorem coeff_aeval_of_isHomogeneous {R : Type} [CommRing R] {n : ℕ}
    (P : MvPolynomial (Fin 2) R) (h : P.IsHomogeneous n) (j : ℕ) :
    (MvPolynomial.aeval ![(Polynomial.X : Polynomial R), 1] P).coeff j =
      ∑ d ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin 2)) n,
        if d 0 = j then MvPolynomial.coeff d P else 0 := by
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum, Polynomial.finsetSum_coeff]
  have hterm : ∀ d : Fin 2 →₀ ℕ,
      (MvPolynomial.aeval ![(Polynomial.X : Polynomial R), 1]
        (MvPolynomial.monomial d (MvPolynomial.coeff d P))).coeff j =
        if d 0 = j then MvPolynomial.coeff d P else 0 := by
    intro d
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_two]
    simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, eq_comm]
  simp_rw [hterm]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, by simp⟩
    have hd' : MvPolynomial.coeff d P ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have := h hd'
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  · intro d _ hd
    rw [MvPolynomial.notMem_support_iff.mp hd]
    simp

/- English proof (translation)
Introduce `Γ X O _ _ n T rep hT a b ha hb j`. Use `set c : Fin 2 → X → Matrix (Fin n) (Fin n) O := ![a, b] with hc`. Establish `hcR : ∀ k, InRing T rep (c k)`. Introduce `k`. Use `fin_cases k`.

Conclude with `ha`. Conclude with `hb`. Establish `key` using `GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T rep hT 2 c hcR`. Use `set P : X → MvPolynomial (Fin 2) O := fun x => Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin 2) O) • (c k x).map MvPolynomial.C) with hP`. Establish `hhom : ∀ x, (P x).IsHomogeneous n`.

Introduce `x`. Use `isHomogeneous_det_of_linear _ fun i j => ?_` and prove the remaining obligations. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]`. Use `MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_` and prove the remaining obligations. Simplify using `using (MvPolynomial.isHomogeneous_X O k).mul (MvPolynomial.isHomogeneous_C (Fin 2) (c k x i j))`.

Establish `hdet : ∀ x, Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R` using `O)) + (b x).map (Polynomial.C (R := O))) = MvPolynomial.aeval ![(Polynomial.X : Polynomial O), 1] (P x) := by`. Introduce `x`. Rewrite using `[hP, AlgHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Simplify using `[hc, Fin.sum_univ_two, Matrix.map_apply]`. Establish `hfun : (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R` using `O)) + (b x).map (Polynomial.C (R := O)))).coeff j) = ∑ d ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin 2)) n, (fun x => if d 0 = j then MvPolynomial.coeff d (P x) else 0) := by`. Use function extensionality and compare the values at `x`. Rewrite using `[hdet x, coeff_aeval_of_isHomogeneous _ (hhom x) j, Finset.sum_apply]`. Rewrite using `[hfun]`.

Use `Subalgebra.sum_mem _ fun d _ => ?_` and prove the remaining obligations. Distinguish the cases in `hd : d 0 = j`. Simplify using `only [hd, if_true]`. Conclude with `key d`. Simplify using `only [hd, if_false]`.

Conclude with `T.zero_mem`.
-/
theorem coeff_det_pencil_mem : ∀ {Γ X O : Type} [Group Γ] [CommRing O] {n : ℕ} (T : Subalgebra O (X → O)) (rep : X → (Γ →* GL (Fin n) O)), CharPolyIn T rep → ∀ a b : X → Matrix (Fin n) (Fin n) O, InRing T rep a → InRing T rep b → ∀ j : ℕ, (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) + (b x).map (Polynomial.C (R := O)))).coeff j) ∈ T := by
  intro Γ X O _ _ n T rep hT a b ha hb j
  set c : Fin 2 → X → Matrix (Fin n) (Fin n) O := ![a, b] with hc
  have hcR : ∀ k, InRing T rep (c k) := by
    intro k; fin_cases k
    · exact ha
    · exact hb
  have key := GlobalTheory.T.coeff_det_generic_sum_mem_heckeAlgebra T rep hT 2 c hcR
  set P : X → MvPolynomial (Fin 2) O := fun x =>
    Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin 2) O) • (c k x).map MvPolynomial.C) with hP
  have hhom : ∀ x, (P x).IsHomogeneous n := by
    intro x
    refine isHomogeneous_det_of_linear _ fun i j => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
    simpa using (MvPolynomial.isHomogeneous_X O k).mul (MvPolynomial.isHomogeneous_C (Fin 2) (c k x i j))
  have hdet : ∀ x, Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) +
      (b x).map (Polynomial.C (R := O))) =
      MvPolynomial.aeval ![(Polynomial.X : Polynomial O), 1] (P x) := by
    intro x
    rw [hP, AlgHom.map_det]
    congr 1
    ext i j
    simp [hc, Fin.sum_univ_two, Matrix.map_apply]
  have hfun : (fun x => (Matrix.det ((Polynomial.X : Polynomial O) • (a x).map (Polynomial.C (R := O)) +
      (b x).map (Polynomial.C (R := O)))).coeff j) =
      ∑ d ∈ Finset.finsuppAntidiag (Finset.univ : Finset (Fin 2)) n,
        (fun x => if d 0 = j then MvPolynomial.coeff d (P x) else 0) := by
    funext x
    rw [hdet x, coeff_aeval_of_isHomogeneous _ (hhom x) j, Finset.sum_apply]
  rw [hfun]
  refine Subalgebra.sum_mem _ fun d _ => ?_
  by_cases hd : d 0 = j
  · simp only [hd, if_true]
    exact key d
  · simp only [hd, if_false]
    exact T.zero_mem

end GlobalTheory.SpanRing
