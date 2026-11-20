import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.UnipFlip

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, longElt, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]`. Simplify using `only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[Finset.sum_eq_single j.rev]`. Simplify using the standard rewrite rules. Introduce `b _ hb; rw [if_neg]; intro e; exact hb (by rw [e, Fin.rev_rev])`.

Simplify using the standard rewrite rules.
-/
theorem longElt_conj_apply {R : Type} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ((longElt n R : Matrix (Fin n) (Fin n) R) * A * (longElt n R : Matrix (Fin n) (Fin n) R)) i j
      = A i.rev j.rev := by
  simp only [Matrix.mul_apply, longElt, Matrix.of_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro b _ hb; rw [if_neg]; intro e; exact hb (by rw [e, Fin.rev_rev])
  · simp

/- English proof (translation)
Establish `hv : u⁻¹ ∈ unipB R (Fin n)` using `inv_mem hu`. Rewrite `hu`, `hv` using `[mem_unipB]`. Establish `hpq : p ≠ q` using `by intro e; subst e; omega`. Establish `key` using `congrFun (congrFun (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R)) (mul_inv_cancel u)) p) q`. Simplify using `only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_ne hpq] at key`.

Rewrite `key` using `[Fintype.sum_eq_add p q hpq]`. Rewrite `key` using `[hu.2 p, hv.2 q, one_mul, mul_one]`. Take the linear combination `key`. Introduce `c ⟨hcp, hcq⟩`. Break down `lt_or_gt_of_ne hcp with hlt | hgt` into its components or cases.

Rewrite using `[hu.1 p c hlt, zero_mul]`. Establish `: q < c`. Establish `h1 : (p : ℕ) < c` using `hgt`. Establish `h2 : (c : ℕ) ≠ q` using `fun e => hcq (Fin.ext e)`. Use `show (q : ℕ) < c`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hv.1 c q this, mul_zero]`.
-/
theorem inv_apply_succ {R : Type} [CommRing R] {n : ℕ} {u : GL (Fin n) R} (hu : u ∈ unipB R (Fin n))
    (p q : Fin n) (h : (q : ℕ) = p + 1) :
    ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) p q = - (u : Matrix (Fin n) (Fin n) R) p q := by
  have hv : u⁻¹ ∈ unipB R (Fin n) := inv_mem hu
  rw [mem_unipB] at hu hv
  have hpq : p ≠ q := by intro e; subst e; omega
  have key := congrFun (congrFun (congrArg (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R)) (mul_inv_cancel u)) p) q
  simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_ne hpq] at key
  rw [Fintype.sum_eq_add p q hpq] at key
  · rw [hu.2 p, hv.2 q, one_mul, mul_one] at key
    linear_combination key
  · intro c ⟨hcp, hcq⟩
    rcases lt_or_gt_of_ne hcp with hlt | hgt
    · rw [hu.1 p c hlt, zero_mul]
    · have : q < c := by
        have h1 : (p : ℕ) < c := hgt
        have h2 : (c : ℕ) ≠ q := fun e => hcq (Fin.ext e)
        show (q : ℕ) < c
        omega
      rw [hv.1 c q this, mul_zero]

/- English proof (translation)
Introduce `R _ n u hu`. Establish `hv : u⁻¹ ∈ unipB R (Fin n)` using `inv_mem hu`. Establish `hval : ∀ i j : Fin n, ((longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j = ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j.rev i.rev`. Introduce `i j`. Rewrite using `[Units.val_mul, Units.val_mul]`.

Rewrite using `[longElt_conj_apply]`. Both sides reduce to the same expression. Rewrite `hv` using `[mem_unipB]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_unipB]`.

Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`. Conclude with `hv.1 _ _ (Fin.rev_lt_rev.2 hij)`. Rewrite using `[hval]`. Conclude with `hv.2 _`.

Simplify using `only [superDiag, Finset.sum_filter]`. Repeatedly rewrite using `[hval]`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Fintype.sum_equiv Fin.revPerm _ _ fun p => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_neg_distrib]`. Use `Fintype.sum_equiv Fin.revPerm _ _ fun q => ?_` and prove the remaining obligations. Simplify using `only [Fin.revPerm_apply, Fin.rev_rev]`. Establish `hiff : ((q.rev : Fin n) : ℕ) = (p.rev : ℕ) + 1 ↔ (p : ℕ) = q + 1`. Simplify using `only [Fin.val_rev]`.

Use `p.isLt` as an intermediate fact. Use `q.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Distinguish the cases in `h : (p : ℕ) = q + 1`. Rewrite using `[if_pos h, if_pos (hiff.2 h), inv_apply_succ hu p.rev q.rev (hiff.2 h)]`.

Rewrite using `[if_neg h, if_neg (mt hiff.1 h), neg_zero]`.
-/
theorem longElt_invT_conj_unipB : ∀ (R : Type) [CommRing R] (n : ℕ) (u : GL (Fin n) R), u ∈ unipB R (Fin n) →
    longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipB R (Fin n) ∧
      superDiag (longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R) = -superDiag u := by
  intro R _ n u hu
  have hv : u⁻¹ ∈ unipB R (Fin n) := inv_mem hu
  have hval : ∀ i j : Fin n,
      ((longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j
        = ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j.rev i.rev := by
    intro i j
    rw [Units.val_mul, Units.val_mul]
    rw [longElt_conj_apply]
    rfl
  rw [mem_unipB] at hv
  refine ⟨?_, ?_⟩
  · rw [mem_unipB]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval]; exact hv.1 _ _ (Fin.rev_lt_rev.2 hij)
    · rw [hval]; exact hv.2 _
  · simp only [superDiag, Finset.sum_filter]
    simp_rw [hval]
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun p => ?_
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv Fin.revPerm _ _ fun q => ?_
    simp only [Fin.revPerm_apply, Fin.rev_rev]

    have hiff : ((q.rev : Fin n) : ℕ) = (p.rev : ℕ) + 1 ↔ (p : ℕ) = q + 1 := by
      simp only [Fin.val_rev]; have := p.isLt; have := q.isLt; omega
    by_cases h : (p : ℕ) = q + 1
    · rw [if_pos h, if_pos (hiff.2 h), inv_apply_succ hu p.rev q.rev (hiff.2 h)]
    · rw [if_neg h, if_neg (mt hiff.1 h), neg_zero]

end GlobalTheory.UnipFlip
