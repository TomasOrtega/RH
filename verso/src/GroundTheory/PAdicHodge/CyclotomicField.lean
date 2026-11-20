import Mathlib
import GroundTheory.PAdicHodge.NormalizedTrace
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open IntermediateField Polynomial

noncomputable section

variable (p : ℕ) [Fact p.Prime]

def cycl (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  adjoin ℚ_[p] {x : PadicAlgCl p | x ^ (p ^ n) = 1}

variable {p}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pow_eq_one_mem_cycl {n : ℕ} {x : PadicAlgCl p} (hx : x ^ (p ^ n) = 1) : x ∈ cycl p n :=
  subset_adjoin _ _ hx

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem cycl_mono : Monotone (cycl p) := fun n m h =>
  adjoin.mono _ _ _ fun x (hx : x ^ (p ^ n) = 1) => by
    show x ^ (p ^ m) = 1
    obtain ⟨k, hk⟩ := Nat.pow_dvd_pow p h
    rw [hk, pow_mul, hx, one_pow]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem finite_setOf_pow_eq_one (n : ℕ) : {x : PadicAlgCl p | x ^ (p ^ n) = 1}.Finite := by
  classical
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  refine (nthRoots (p ^ n) (1 : PadicAlgCl p)).toFinset.finite_toSet.subset fun x hx => ?_
  simpa [Finset.mem_coe, Multiset.mem_toFinset, mem_nthRoots hpos] using hx

instance finiteDimensional_cycl (n : ℕ) : FiniteDimensional ℚ_[p] (cycl p n) := by
  haveI : Finite {x : PadicAlgCl p | x ^ (p ^ n) = 1} := (finite_setOf_pow_eq_one n).to_subtype
  exact finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_isPrimitiveRoot (n : ℕ) : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) := by
  haveI : NeZero ((p ^ n : ℕ) : PadicAlgCl p) :=
    ⟨Nat.cast_ne_zero.2 (pow_ne_zero n (Fact.out : p.Prime).ne_zero)⟩
  have hpos : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (cyclotomic (p ^ n) (PadicAlgCl p))
    (degree_cyclotomic_pos (p ^ n) (PadicAlgCl p) hpos).ne'
  exact ⟨ζ, (isRoot_cyclotomic_iff).1 hζ⟩

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem cycl_eq_adjoin {n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ n)) :
    cycl p n = ℚ_[p]⟮ζ⟯ := by
  apply le_antisymm
  · rw [cycl, adjoin_le_iff]
    intro x (hx : x ^ (p ^ n) = 1)
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
    exact pow_mem (mem_adjoin_simple_self ℚ_[p] ζ) i
  · rw [adjoin_simple_le_iff]
    exact pow_eq_one_mem_cycl hζ.pow_eq_one

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cycl_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (n : ℕ) :
    (cycl p n).map (σ : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) = cycl p n := by
  rw [cycl, adjoin_map]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    show (σ y) ^ (p ^ n) = 1
    rw [← map_pow, show y ^ (p ^ n) = 1 from hy, map_one]
  · intro (hx : x ^ (p ^ n) = 1)
    refine ⟨σ.symm x, ?_, by simp⟩
    show (σ.symm x) ^ (p ^ n) = 1
    rw [← map_pow, hx, map_one]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem map_mem_cycl (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) {n : ℕ} {x : PadicAlgCl p}
    (hx : x ∈ cycl p n) : σ x ∈ cycl p n := by
  rw [← cycl_map σ n]
  exact ⟨x, hx, rfl⟩

end

end GroundTheory.PAdicHodge
