import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.WildChar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Move the embeddings inside the algebraic operations.

Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem val_natCast_not_lt {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l p : ℕ}
    (hcop : Nat.Coprime l p) (hp : A.valuation (p : Ω) < 1) : ¬ A.valuation (l : Ω) < 1 := by
  intro hl
  have e : ((l : ℤ) * l.gcdA p + (p : ℤ) * l.gcdB p : ℤ) = 1 := by
    have := Nat.gcd_eq_gcd_ab l p
    rw [hcop.gcd_eq_one] at this
    push_cast at this
    exact this.symm
  have e' : (l : Ω) * (l.gcdA p : Ω) + (p : Ω) * (l.gcdB p : Ω) = 1 := by
    have := congrArg (Int.cast : ℤ → Ω) e
    push_cast at this
    exact this
  have ha : A.valuation (l.gcdA p : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have hb : A.valuation (l.gcdB p : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
  have h1 : A.valuation ((l : Ω) * (l.gcdA p : Ω) + (p : Ω) * (l.gcdB p : Ω)) < 1 := by
    refine lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt ?_ ?_)
    · rw [map_mul]; exact (mul_le_of_le_one_right' ha).trans_lt hl
    · rw [map_mul]; exact (mul_le_of_le_one_right' hb).trans_lt hp
  rw [e', map_one] at h1
  exact lt_irrefl _ h1

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem sub_lt_of_wild {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (τ : Gal(Ω/F)) (hτ : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) (y : Ω) (hy : y ≠ 0) :
    A.valuation (τ y - y) < A.valuation y := by
  have hv : A.valuation y ≠ 0 := by simpa using hy
  have h := hτ y hy
  have e : τ y / y - 1 = (τ y - y) / y := by field_simp
  rw [e, map_div₀] at h
  have hpos : 0 < A.valuation y := zero_lt_iff.mpr hv
  calc A.valuation (τ y - y) = A.valuation (τ y - y) / A.valuation y * A.valuation y := by
        rw [div_mul_cancel₀ _ hv]
    _ < 1 * A.valuation y := by
        exact mul_lt_mul_of_pos_right h hpos
    _ = A.valuation y := one_mul _

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Treat this case separately.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pow_sub_lt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)
    (τ : Gal(Ω/F)) (hτ : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1) (y : Ω) (hy : y ≠ 0) :
    ∀ i : ℕ, A.valuation ((τ ^ i) y - y) < A.valuation y := by
  have hv : A.valuation y ≠ 0 := by simpa using hy
  intro i
  induction i with
  | zero => simpa using zero_lt_iff.mpr hv
  | succ i ih =>
    have hne : (τ ^ i) y ≠ 0 := fun h0 => hy ((τ ^ i).injective (h0.trans (map_zero _).symm))
    have heq : A.valuation ((τ ^ i) y) = A.valuation y := Valuation.map_eq_of_sub_lt _ ih
    have h1 := sub_lt_of_wild A τ hτ _ hne
    rw [heq] at h1
    have e : (τ ^ (i + 1)) y - y = (τ ((τ ^ i) y) - (τ ^ i) y) + ((τ ^ i) y - y) := by
      rw [pow_succ', AlgEquiv.mul_apply]; ring
    rw [e]
    exact lt_of_le_of_lt (A.valuation.map_add _ _) (max_lt h1 ih)

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem fix_of_pow_fix {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (p : ℕ)
    (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1)
    (τ : Gal(Ω/F)) (hτ : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1)
    (n : ℕ) (hn : Nat.Coprime n p) (y : Ω) (hy : (τ ^ n) y = y) : τ y = y := by
  by_contra hne
  set e := τ y - y with he
  have he0 : e ≠ 0 := sub_ne_zero.mpr hne
  have hsum : ∑ i ∈ Finset.range n, (τ ^ i) e = 0 := by
    have : ∀ i, (τ ^ i) e = (τ ^ (i + 1)) y - (τ ^ i) y := by
      intro i; rw [he, map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [this]
    rw [Finset.sum_range_sub (fun i => (τ ^ i) y) n, hy]; simp
  have hsplit : ∑ i ∈ Finset.range n, (τ ^ i) e =
      (n : Ω) * e + ∑ i ∈ Finset.range n, ((τ ^ i) e - e) := by
    rw [Finset.sum_sub_distrib]; simp
  have hlt : A.valuation (∑ i ∈ Finset.range n, ((τ ^ i) e - e)) < A.valuation e :=
    Valuation.map_sum_lt _ (by simpa using he0) (fun i _ => pow_sub_lt A τ hτ e he0 i)
  have hn1 : A.valuation (n : Ω) = 1 := by
    have hle : A.valuation (n : Ω) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A _)
    exact le_antisymm hle (not_lt.mp (val_natCast_not_lt A hn hp))
  have key : (n : Ω) * e = - ∑ i ∈ Finset.range n, ((τ ^ i) e - e) := by
    rw [hsplit] at hsum; linear_combination hsum
  have := congrArg A.valuation key
  rw [map_mul, hn1, one_mul, Valuation.map_neg] at this
  rw [this] at hlt
  exact lt_irrefl _ hlt

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem main : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 →
    ∀ (R : Type) [CommRing R] (χ : G F Ω →* Rˣ), IsOpen (χ.ker : Set (G F Ω)) →
    ∀ σ : G F Ω, (∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1) →
    ∀ m : ℕ, 0 < m → Nat.Coprime m p → χ σ ^ m = 1 → χ σ = 1 := by
  intro F Ω _ _ _ _ _ p hpr A hp R _ χ hK σ hσ m _ hmp hχm
  have : Normal F Ω := IsAlgClosure.normal F Ω
  obtain ⟨E, hfin, hnorm, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal F Ω _).mp (hK.mem_nhds χ.ker.one_mem)
  set k := orderOf (AlgEquiv.restrictNormalHom E σ) with hk
  have hk0 : k ≠ 0 := (orderOf_pos _).ne'
  have hfixE : ∀ τ : Gal(Ω/F), AlgEquiv.restrictNormalHom E τ = 1 → ∀ a ∈ E, τ a = a := by
    intro τ h1 a ha
    have := AlgEquiv.restrictNormal_commutes τ E ⟨a, ha⟩
    have h2 : (AlgEquiv.restrictNormal τ E) ⟨a, ha⟩ = ⟨a, ha⟩ := by
      have h3 : AlgEquiv.restrictNormalHom E τ = AlgEquiv.restrictNormal τ E := rfl
      rw [← h3, h1]; rfl
    rw [h2] at this
    exact this.symm
  have hσk : ∀ a ∈ E, (σ ^ k) a = a := by
    apply hfixE
    rw [map_pow, hk, pow_orderOf_eq_one]
  set a := k.factorization p
  set n := k / p ^ a
  have hkan : p ^ a * n = k := Nat.ordProj_mul_ordCompl_eq_self k p
  have hnp : Nat.Coprime n p := (Nat.coprime_ordCompl hpr.out hk0).symm
  set τ := σ ^ (p ^ a)
  have hτw : ∀ y : Ω, y ≠ 0 → A.valuation (τ y / y - 1) < 1 := by
    intro y hy
    have hv : A.valuation y ≠ 0 := by simpa using hy
    have h := pow_sub_lt A σ hσ y hy (p ^ a)
    have e : τ y / y - 1 = (τ y - y) / y := by field_simp
    rw [e, map_div₀]
    exact (div_lt_one₀ (zero_lt_iff.mpr hv)).mpr h
  have hτE : τ ∈ E.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro b hb
    apply fix_of_pow_fix p A hp τ hτw n hnp b
    rw [← pow_mul, hkan]
    exact hσk b hb
  have h1 : χ σ ^ (p ^ a) = 1 := by rw [← map_pow]; exact MonoidHom.mem_ker.mp (hE hτE)
  have hcop : Nat.Coprime m (p ^ a) := Nat.Coprime.pow_right _ hmp
  have h3 : χ σ ^ Nat.gcd m (p ^ a) = 1 := pow_gcd_eq_one.mpr ⟨hχm, h1⟩
  rwa [hcop.gcd_eq_one, pow_one] at h3

end GlobalTheory.WildChar
