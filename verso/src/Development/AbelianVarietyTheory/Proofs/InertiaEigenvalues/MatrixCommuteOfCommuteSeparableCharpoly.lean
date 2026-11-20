import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeftMulMatrixTransfer

open Matrix Polynomial

namespace GlobalTheory.CommSep

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `hp.add_right hq`. Consider the case `monomial k a`. Rewrite using `[aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]`.

Conclude with `(h.pow_right k).smul_right a`.
-/
theorem commute_aeval_of_commute {E : Type} [Field E] {r : ℕ} {m A : Matrix (Fin r) (Fin r) E}
    (h : Commute m A) (p : E[X]) : Commute m (aeval A p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact hp.add_right hq
  | monomial k a =>
    rw [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact (h.pow_right k).smul_right a

/- English proof (translation)
Use extensionality with `i`. Simplify using `[GlobalTheory.ClassParam.krylov, map_sum, aeval_monomial, Matrix.sum_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.sum_apply, Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem aeval_mulVec_eq_krylov {E : Type} [Field E] {r : ℕ} (A : Matrix (Fin r) (Fin r) E)
    (v c : Fin r → E) :
    aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) *ᵥ v = GlobalTheory.ClassParam.krylov A v *ᵥ c := by
  ext i
  simp [GlobalTheory.ClassParam.krylov, map_sum, aeval_monomial, Matrix.sum_mulVec,
    Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.mulVec, dotProduct, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Take `⟨v, hv⟩` from `GlobalTheory.ClassParam.exists_cyclic_field A hs`. Use `set K := GlobalTheory.ClassParam.krylov A v with hK`. Establish `hKu : IsUnit K.det` using `isUnit_iff_ne_zero.2 hv`. Set `c` to `K⁻¹ *ᵥ (n *ᵥ v)`. Use `⟨∑ j : Fin r, monomial (j : ℕ) (c j), ?_⟩` and prove the remaining obligations.

Use `set p := aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) with hp`. Establish `hpv : p *ᵥ v = n *ᵥ v`. Rewrite using `[hp, aeval_mulVec_eq_krylov, ← hK]`. Simplify using `only [c, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.one_mul]`. Establish `hpA : Commute p A` using `(commute_aeval_of_commute (Commute.refl A) _).symm`.

Establish `hnA : Commute n A` using `hn`. Establish `hcol : n * K = p * K`. Use extensionality with `i j`. Establish `e1 : ∀ M : Matrix (Fin r) (Fin r) E, Commute M A → (M * K) i j = (A ^ (j : ℕ) *ᵥ (M *ᵥ v)) i`. Introduce `M hM`.

Establish `: (M * K) i j = (M *ᵥ (A ^ (j : ℕ) *ᵥ v)) i`. Simplify using `[hK, GlobalTheory.ClassParam.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hM.pow_right _).eq]`. Rewrite using `[e1 n hnA, e1 p hpA, hpv]`. Use `congrArg (· * K⁻¹) hcol` as an intermediate fact.

Simplify `this` using `[Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu]`.
-/
theorem eq_aeval_of_commute_of_separable {E : Type} [Field E] {r : ℕ}
    (A : Matrix (Fin r) (Fin r) E) (hs : A.charpoly.Separable) (n : Matrix (Fin r) (Fin r) E)
    (hn : n * A = A * n) : ∃ q : E[X], n = aeval A q := by
  classical
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field A hs
  set K := GlobalTheory.ClassParam.krylov A v with hK
  have hKu : IsUnit K.det := isUnit_iff_ne_zero.2 hv
  let c := K⁻¹ *ᵥ (n *ᵥ v)
  refine ⟨∑ j : Fin r, monomial (j : ℕ) (c j), ?_⟩
  set p := aeval A (∑ j : Fin r, monomial (j : ℕ) (c j)) with hp
  have hpv : p *ᵥ v = n *ᵥ v := by
    rw [hp, aeval_mulVec_eq_krylov, ← hK]
    simp only [c, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu, Matrix.one_mul]
  have hpA : Commute p A := (commute_aeval_of_commute (Commute.refl A) _).symm
  have hnA : Commute n A := hn
  have hcol : n * K = p * K := by
    ext i j
    have e1 : ∀ M : Matrix (Fin r) (Fin r) E, Commute M A →
        (M * K) i j = (A ^ (j : ℕ) *ᵥ (M *ᵥ v)) i := by
      intro M hM
      have : (M * K) i j = (M *ᵥ (A ^ (j : ℕ) *ᵥ v)) i := by
        simp [hK, GlobalTheory.ClassParam.krylov, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (hM.pow_right _).eq]
    rw [e1 n hnA, e1 p hpA, hpv]
  have := congrArg (· * K⁻¹) hcol
  simpa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hKu] using this

/- English proof (translation)
Introduce `E _ r A₀ hs m n hm hn`. Take `⟨q, rfl⟩` from `eq_aeval_of_commute_of_separable A₀ hs n hn`. Conclude with `(commute_aeval_of_commute (m := m) hm q).eq`.
-/
theorem commute_of_commute_separable : ∀ (E : Type) [Field E] (r : ℕ)
    (A₀ : Matrix (Fin r) (Fin r) E), A₀.charpoly.Separable → ∀ m n : Matrix (Fin r) (Fin r) E,
    m * A₀ = A₀ * m → n * A₀ = A₀ * n → m * n = n * m := by
  intro E _ r A₀ hs m n hm hn
  obtain ⟨q, rfl⟩ := eq_aeval_of_commute_of_separable A₀ hs n hn
  exact (commute_aeval_of_commute (m := m) hm q).eq

end GlobalTheory.CommSep
