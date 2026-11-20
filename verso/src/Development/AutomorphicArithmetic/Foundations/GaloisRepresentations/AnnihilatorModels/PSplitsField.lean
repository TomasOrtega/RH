import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Establish `hex : ∃ p, ψ (Pi.single p 1) ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `Fintype.ofFinite P` as an intermediate fact. Establish `h1 : (1 : P → K) = ∑ p, Pi.single p 1`.

Simplify using `using (Finset.univ_sum_single (1 : P → K)).symm`. Establish `h2 : ψ 1 = 0`. Rewrite using `[h1, map_sum]`. Simplify using `[h]`. Simplify using `at h2`.

Take `⟨p, hp⟩` from `hex`. Use `⟨p, fun x => ?_⟩` and prove the remaining obligations. Establish `hid : ψ (Pi.single p 1) = 1`. Establish `h2 : ψ (Pi.single p 1) * ψ (Pi.single p 1) = ψ (Pi.single p 1)`. Rewrite using `[← map_mul]`.

Use `congr 1`. Use extensionality with `i`. Apply the tactic sequence `by_cases h : i = p <;> simp [Pi.single_apply, h]`. Conclude with `(mul_left_inj' hp).1 (h2.trans (one_mul _).symm)`. Establish `hx : x * Pi.single p 1 = algebraMap K (P → K) (x p) * Pi.single p 1`.

Use extensionality with `i`. Apply the tactic sequence `by_cases h : i = p <;> simp [Pi.single_apply, h]`. Establish `h3` using `congrArg ψ hx`. Rewrite `h3` using `[map_mul, map_mul, AlgHom.commutes, hid]`. Simplify using `using h3`.
-/
private theorem exists_forall_algHom_pi_eq_apply_of_finite {K P : Type} [Field K] [Finite P] (ψ : (P → K) →ₐ[K] K) :
    ∃ p, ∀ x, ψ x = x p := by
  classical
  have hex : ∃ p, ψ (Pi.single p 1) ≠ 0 := by
    by_contra h
    push_neg at h
    have := Fintype.ofFinite P
    have h1 : (1 : P → K) = ∑ p, Pi.single p 1 := by
      simpa using (Finset.univ_sum_single (1 : P → K)).symm
    have h2 : ψ 1 = 0 := by
      rw [h1, map_sum]
      simp [h]
    simp at h2
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, fun x => ?_⟩
  have hid : ψ (Pi.single p 1) = 1 := by
    have h2 : ψ (Pi.single p 1) * ψ (Pi.single p 1) = ψ (Pi.single p 1) := by
      rw [← map_mul]
      congr 1
      ext i
      by_cases h : i = p <;> simp [Pi.single_apply, h]
    exact (mul_left_inj' hp).1 (h2.trans (one_mul _).symm)
  have hx : x * Pi.single p 1 = algebraMap K (P → K) (x p) * Pi.single p 1 := by
    ext i
    by_cases h : i = p <;> simp [Pi.single_apply, h]
  have h3 := congrArg ψ hx
  rw [map_mul, map_mul, AlgHom.commutes, hid] at h3
  simpa using h3

/- English proof (translation)
Introduce `R S K _ _ _ _ _ _ hE`. Establish `hfin : Module.Finite K (K ⊗[R] S)` using `Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)`. Use `haveI : IsArtinianRing (K ⊗[R] S) := isArtinian_of_tower K inferInstance`. Use `haveI : Finite (PrimeSpectrum (K ⊗[R] S)) := inferInstance`. Set `e` to `Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[R] S)`.

Set `F` to `splitMap (R := R) (S := S) (B := K) (I := S →ₐ[R] K) (fun z => z)`. Set `L : (S →ₐ[R] K) → ((K ⊗[R] S) →ₐ[K] K)` to `fun ψ => (Pi.evalAlgHom K (fun _ => K) ψ).comp F`. Establish `hL : ∀ ψ x, L ψ x = F x ψ` using `fun _ _ => rfl`. Establish `hLs : ∀ ψ (s : S), L ψ (1 ⊗ₜ s) = ψ s`. Introduce `ψ s`.

Simplify using `[L, F, splitMap]`. Use `choose q hq using fun ψ => exists_forall_algHom_pi_eq_apply_of_finite ((L ψ).comp e.symm.toAlgHom)`. Establish `hLe : ∀ ψ x, L ψ x = e x (q ψ)`. Introduce `ψ x`. Simplify using `using hq ψ (e x)`.

Establish `qinj : Function.Injective q`. Introduce `ψ1 ψ2 h`. Use extensionality with `s`. Rewrite using `[← hLs, ← hLs, hLe, hLe, h]`. Establish `hsec : ∀ p, ∃ ψ, q ψ = p`.

Introduce `p`. Set `g : (K ⊗[R] S) →ₐ[K] K` to `(Pi.evalAlgHom K (fun _ => K) p).comp e.toAlgHom`. Set `ψ : S →ₐ[R] K` to `(g.restrictScalars R).comp Algebra.TensorProduct.includeRight`. Establish `hg : L ψ = g`. Apply `Algebra.TensorProduct.ext` to reduce the goal to its premises.

Conclude with `Subsingleton.elim _ _`. Use extensionality with `s`. Simplify using `[hLs, ψ]`. Use `⟨ψ, ?_⟩` and prove the remaining obligations. Establish `h1` using `hLe ψ (e.symm (Pi.single p 1))`.

Rewrite `h1` using `[hg]`. Simplify using `only [g, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe, AlgEquiv.apply_symm_apply, Pi.evalAlgHom_apply] at h1`. Assume the negation of the conclusion as `hne`. Simplify using `[Pi.single_apply, hne] at h1`. Use `⟨Finite.of_injective q qinj, ?_⟩` and prove the remaining obligations.

Use `show Function.Bijective F`. Prove the components needed by the constructor for the conclusion. Introduce `x y h`. Apply `e.injective` to reduce the goal to its premises. Use function extensionality and compare the values at `p`.

Take `⟨ψ, rfl⟩` from `hsec p`. Rewrite using `[← hLe, ← hLe, hL, hL, h]`. Introduce `v`. Use `⟨e.symm (Function.extend q v 0), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `ψ`.

Rewrite using `[← hL, hLe, e.apply_symm_apply, qinj.extend_apply]`.
-/
theorem UpperTheory.Gal.crystallineComparison.splitsField_of :
    SplitsField := by
  intro R S K _ _ _ _ _ _ hE
  classical
  have hfin : Module.Finite K (K ⊗[R] S) := Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
  haveI : IsArtinianRing (K ⊗[R] S) := isArtinian_of_tower K inferInstance
  haveI : Finite (PrimeSpectrum (K ⊗[R] S)) := inferInstance
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed K (K ⊗[R] S)
  let F := splitMap (R := R) (S := S) (B := K) (I := S →ₐ[R] K) (fun z => z)
  let L : (S →ₐ[R] K) → ((K ⊗[R] S) →ₐ[K] K) := fun ψ => (Pi.evalAlgHom K (fun _ => K) ψ).comp F
  have hL : ∀ ψ x, L ψ x = F x ψ := fun _ _ => rfl
  have hLs : ∀ ψ (s : S), L ψ (1 ⊗ₜ s) = ψ s := by
    intro ψ s
    simp [L, F, splitMap]
  choose q hq using fun ψ => exists_forall_algHom_pi_eq_apply_of_finite ((L ψ).comp e.symm.toAlgHom)
  have hLe : ∀ ψ x, L ψ x = e x (q ψ) := by
    intro ψ x
    simpa using hq ψ (e x)
  have qinj : Function.Injective q := by
    intro ψ1 ψ2 h
    ext s
    rw [← hLs, ← hLs, hLe, hLe, h]
  have hsec : ∀ p, ∃ ψ, q ψ = p := by
    intro p
    let g : (K ⊗[R] S) →ₐ[K] K := (Pi.evalAlgHom K (fun _ => K) p).comp e.toAlgHom
    let ψ : S →ₐ[R] K := (g.restrictScalars R).comp Algebra.TensorProduct.includeRight
    have hg : L ψ = g := by
      apply Algebra.TensorProduct.ext
      · exact Subsingleton.elim _ _
      · ext s
        simp [hLs, ψ]
    refine ⟨ψ, ?_⟩
    have h1 := hLe ψ (e.symm (Pi.single p 1))
    rw [hg] at h1
    simp only [g, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
      AlgEquiv.apply_symm_apply, Pi.evalAlgHom_apply] at h1
    by_contra hne
    simp [Pi.single_apply, hne] at h1
  refine ⟨Finite.of_injective q qinj, ?_⟩
  show Function.Bijective F
  constructor
  · intro x y h
    apply e.injective
    funext p
    obtain ⟨ψ, rfl⟩ := hsec p
    rw [← hLe, ← hLe, hL, hL, h]
  · intro v
    refine ⟨e.symm (Function.extend q v 0), ?_⟩
    funext ψ
    rw [← hL, hLe, e.apply_symm_apply, qinj.extend_apply]
