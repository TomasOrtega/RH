import Mathlib
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.ExistsMaxMinorNeZeroOfLinearIndependentAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Matrix Finset Equiv

abbrev KSubset (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n := s.1.orderEmbOfFin s.2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem KSubset.range_emb {n k : ℕ} (s : KSubset n k) : Set.range s.emb = (s.1 : Set (Fin n)) :=
  Finset.range_orderEmbOfFin _ _

variable {R : Type*} [CommRing R]

section CauchyBinet

variable {k n : ℕ}

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
private theorem det_mul_eq_sum_fun (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ p : Fin k → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id, sum_mul, prod_mul_distrib, mul_assoc]
  rw [Finset.sum_comm]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Use symmetry to reverse the relation. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Substitute using the available equality. Establish an intermediate fact. By extensionality, compare the relevant components.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. Fix the arbitrary inputs or assume the hypotheses.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem det_mul_eq_sum_minors (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det := by
  classical
  set F : (Fin k → Fin n) → R := fun p => (A.submatrix id p).det * ∏ i, B (p i) i with hF
  have hzero : ∀ p, ¬ Function.Injective p → F p = 0 := by
    intro p hp
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hp
      obtain ⟨i, j, h, hne⟩ := hp
      exact ⟨i, j, h, hne⟩
    simp only [hF]
    rw [det_zero_of_column_eq hne (fun r => by simp [hij]), zero_mul]
  have hterm : ∀ (s : KSubset n k) (σ : Perm (Fin k)),
      F (s.emb ∘ σ) = (A.submatrix id s.emb).det * (Perm.sign σ * ∏ i, B (s.emb (σ i)) i) := by
    intro s σ
    simp only [hF]
    have : A.submatrix id (s.emb ∘ σ) = (A.submatrix id s.emb).submatrix id σ := rfl
    rw [this, det_permute']
    simp only [Function.comp_apply]
    ring
  have hs : ∀ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det =
      ∑ σ : Perm (Fin k), F (s.emb ∘ σ) := by
    intro s
    simp only [hterm, ← mul_sum]
    congr 1
    rw [det_apply']
    rfl
  have hprod := Fintype.sum_prod_type (fun x : KSubset n k × Perm (Fin k) => F (x.1.emb ∘ x.2))
  simp only at hprod
  rw [det_mul_eq_sum_fun, Finset.sum_congr rfl (fun s _ => hs s)]
  change ∑ p, F p = _
  rw [← hprod, ← Finset.sum_filter_of_ne (p := Function.Injective) (fun p _ h => by
      by_contra hp; exact h (hzero p hp))]
  symm
  refine Finset.sum_bij (fun x _ => x.1.emb ∘ x.2) ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.1.emb.injective.comp x.2.injective
  · rintro ⟨s, σ⟩ _ ⟨t, τ⟩ _ h
    simp only at h
    have hst : s = t := by
      apply Subtype.ext
      have h1 : Set.range (s.emb ∘ σ) = Set.range (t.emb ∘ τ) := by rw [h]
      rw [Set.range_comp, Set.range_comp, σ.range_eq_univ, τ.range_eq_univ, Set.image_univ,
        Set.image_univ, KSubset.range_emb, KSubset.range_emb] at h1
      exact_mod_cast h1
    subst hst
    have : σ = τ := by
      ext i
      have := congrFun h i
      simp only [Function.comp_apply] at this
      exact congrArg Fin.val (s.emb.injective this)
    rw [this]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hcard : (Finset.univ.image p).card = k := by
      rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin]
    let s : KSubset n k := ⟨Finset.univ.image p, hcard⟩
    have hex : ∀ i, ∃ j, s.emb j = p i := by
      intro i
      have : p i ∈ (s.1 : Set (Fin n)) := by simp [s]
      rw [← KSubset.range_emb] at this
      exact this
    choose f hf using hex
    have hfinj : Function.Injective f := by
      intro i j hij
      apply hp
      rw [← hf i, ← hf j, hij]
    let σ : Perm (Fin k) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
    refine ⟨(s, σ), Finset.mem_univ _, ?_⟩
    funext i
    exact hf i
  · intro x _
    rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. It suffices to derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers.
-/
theorem det_mul_eq_zero_of_lt (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R)
    (h : n < k) : (A * B).det = 0 := by
  rw [det_mul_eq_sum_minors]
  refine Finset.sum_eq_zero fun s _ => ?_
  exfalso
  have := s.1.card_le_univ
  rw [Fintype.card_fin, s.2] at this
  omega

end CauchyBinet

section Minors

variable {m n k : ℕ}

def maxMinor (B : Matrix (Fin n) (Fin k) R) (s : KSubset n k) : R :=
  (B.submatrix s.emb id).det

def compound (k : ℕ) (P : Matrix (Fin m) (Fin n) R) : Matrix (KSubset m k) (KSubset n k) R :=
  Matrix.of fun s t => (P.submatrix s.emb t.emb).det

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem compound_apply (k : ℕ) (P : Matrix (Fin m) (Fin n) R) (s : KSubset m k)
    (t : KSubset n k) : compound k P s t = (P.submatrix s.emb t.emb).det := rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.
-/
theorem maxMinor_mul_right (B : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R)
    (s : KSubset n k) : maxMinor (B * C) s = maxMinor B s * C.det := by
  unfold maxMinor
  rw [← det_mul]
  congr 1

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem maxMinor_mul_left (P : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset m k) :
    maxMinor (P * B) s = ∑ t : KSubset n k, compound k P s t * maxMinor B t := by
  unfold maxMinor
  have : (P * B).submatrix s.emb id = P.submatrix s.emb id * B := by
    ext i j; simp [mul_apply]
  rw [this, det_mul_eq_sum_minors]
  rfl

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem maxMinor_mul_left_eq_mulVec (P : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    maxMinor (P * B) = compound k P *ᵥ maxMinor B := by
  funext s
  rw [maxMinor_mul_left]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem compound_mul {l : ℕ} (P : Matrix (Fin m) (Fin n) R) (Q : Matrix (Fin n) (Fin l) R) :
    compound k (P * Q) = compound k P * compound k Q := by
  ext s u
  rw [compound_apply, mul_apply]
  have : (P * Q).submatrix s.emb u.emb = P.submatrix s.emb id * Q.submatrix id u.emb := by
    ext i j; simp [mul_apply]
  rw [this, det_mul_eq_sum_minors]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem maxMinor_map {S : Type*} [CommRing S] (f : R →+* S) (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) : maxMinor (B.map f) s = f (maxMinor B s) := by
  unfold maxMinor
  rw [RingHom.map_det]
  rfl

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem compound_map {S : Type*} [CommRing S] (f : R →+* S) (P : Matrix (Fin m) (Fin n) R) :
    compound k (P.map f) = (compound k P).map f := by
  ext s t
  rw [compound_apply, map_apply, compound_apply, RingHom.map_det]
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem compound_mulVec_maxMinor_of_mul_eq (A : Matrix (Fin n) (Fin n) R)
    (B B' : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R) (h : A * B' = B * C) :
    compound k A *ᵥ maxMinor B' = C.det • maxMinor B := by
  rw [← maxMinor_mul_left_eq_mulVec, h]
  funext s
  rw [maxMinor_mul_right, Pi.smul_apply, smul_eq_mul, mul_comm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.
-/
theorem compound_mulVec_map_maxMinor_of_mul_eq (φ : R →+* R) (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R) (h : A * B.map φ = B * C) :
    compound k A *ᵥ (fun s => φ (maxMinor B s)) = C.det • maxMinor B := by
  rw [← compound_mulVec_maxMinor_of_mul_eq A B (B.map φ) C h]
  congr 1
  funext s
  rw [maxMinor_map]

end Minors

section Independence

variable {n k : ℕ}

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem linearIndependent_col_iff_mulVec_eq_zero (B : Matrix (Fin n) (Fin k) R) :
    LinearIndependent R B.col ↔ ∀ v, B *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  have key : ∀ v : Fin k → R, ∑ j, v j • B.col j = B *ᵥ v := by
    intro v; ext i; simp [mulVec, dotProduct, Finset.sum_apply, col, mul_comm]
  constructor
  · intro h v hv
    funext j
    exact h v (by rw [key, hv]) j
  · intro h g hg j
    have := h g (by rw [← key, hg])
    exact congrFun this j

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem linearIndependent_col_of_maxMinor_ne_zero [IsDomain R] (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) (hs : maxMinor B s ≠ 0) : LinearIndependent R B.col := by
  rw [linearIndependent_col_iff_mulVec_eq_zero]
  intro v hv
  apply eq_zero_of_mulVec_eq_zero hs
  have : B.submatrix s.emb id *ᵥ v = fun i => (B *ᵥ v) (s.emb i) := by
    ext i; simp [mulVec, dotProduct]
  rw [this, hv]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_maxMinor_ne_zero_of_linearIndependent [IsDomain R]
    (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 :=
  _root_.GroundTheory.Variant₂.N1.exists_maxMinor_ne_zero_of_linearIndependent_alt B hB

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem exists_maxMinor_ne_zero_iff_linearIndependent [IsDomain R]
    (B : Matrix (Fin n) (Fin k) R) :
    (∃ s : KSubset n k, maxMinor B s ≠ 0) ↔ LinearIndependent R B.col :=
  ⟨fun ⟨s, hs⟩ => linearIndependent_col_of_maxMinor_ne_zero B s hs,
    exists_maxMinor_ne_zero_of_linearIndependent B⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem maxMinor_ne_zero_iff_linearIndependent [IsDomain R] (B : Matrix (Fin n) (Fin k) R) :
    maxMinor B ≠ 0 ↔ LinearIndependent R B.col := by
  rw [← exists_maxMinor_ne_zero_iff_linearIndependent, Ne, funext_iff, not_forall]
  rfl

end Independence

end GroundTheory.PAdicHodge
