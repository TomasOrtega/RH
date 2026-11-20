import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open UpperTheory.Gal UpperTheory.Gal.Int.Geo

/- English proof (translation)
Proceed by induction. Treat this case separately. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Substitute using the available equality.

Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
private theorem exists_linearIndep_levels_span_eq_of_monotone {k : Type} [Field k] {V : Type*} [AddCommGroup V] [Module k V]
    (W : ℕ → Submodule k V) (hW : Monotone W) (h0 : W 0 = ⊥) (n : ℕ) :
    ∃ (s : Set V) (lev : V → ℕ), LinearIndepOn k id s ∧ (∀ x ∈ s, lev x < n) ∧
      ∀ i ≤ n, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i := by
  induction n with
  | zero =>
    refine ⟨∅, fun _ => 0, linearIndepOn_empty k id, by simp, ?_⟩
    intro i hi
    obtain rfl : i = 0 := Nat.le_zero.mp hi
    simp [h0]
  | succ n ih =>
    obtain ⟨s, lev, hs, hlev, hspan⟩ := ih
    have hsW : s ⊆ (W (n + 1) : Set V) := by
      intro x hx
      have hx' : x ∈ W n := by
        rw [← hspan n le_rfl]
        exact Submodule.subset_span ⟨hx, hlev x hx⟩
      exact hW (Nat.le_succ n) hx'
    obtain ⟨b, hbt, hsb, htb, hb⟩ := exists_linearIndepOn_id_extension hs hsW
    classical
    refine ⟨b, fun x => if x ∈ s then lev x else n, hb, ?_, ?_⟩
    · intro x hx
      by_cases h : x ∈ s
      · simp only [h, if_true]
        exact Nat.lt_succ_of_lt (hlev x h)
      · simp [h]
    · intro i hi
      rcases Nat.lt_or_ge i (n + 1) with hi' | hi'
      · have hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < i} = {x | x ∈ s ∧ lev x < i} := by
          ext x
          by_cases h : x ∈ s
          · simp [h, hsb h]
          · simp only [Set.mem_setOf_eq, h, if_false, false_and, iff_false]
            rintro ⟨-, h'⟩
            omega
        rw [hset]
        exact hspan i (Nat.lt_succ_iff.mp hi')
      · have hi2 : i = n + 1 := le_antisymm hi hi'
        subst hi2
        have hset : {x | x ∈ b ∧ (if x ∈ s then lev x else n) < n + 1} = b := by
          ext x
          constructor
          · exact fun h => h.1
          · intro hx
            refine ⟨hx, ?_⟩
            by_cases h : x ∈ s
            · simp only [h, if_true]
              exact Nat.lt_succ_of_lt (hlev x h)
            · simp [h]
        rw [hset]
        apply le_antisymm
        · exact Submodule.span_le.mpr hbt
        · intro y hy
          exact htb hy

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components.

Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.Int.Geo.flagBasis_of :
    FlagBasis := by
  intro k _ d m W hW h0 hm
  obtain ⟨s, lev, hs, hlev, hspan⟩ := exists_linearIndep_levels_span_eq_of_monotone W hW h0 m
  have hall : ∀ i, Submodule.span k {x | x ∈ s ∧ lev x < i} = W i := by
    intro i
    rcases le_or_gt i m with h | h
    · exact hspan i h
    · have e1 : {x | x ∈ s ∧ lev x < i} = {x | x ∈ s ∧ lev x < m} := by
        ext x
        constructor
        · rintro ⟨hx, -⟩
          exact ⟨hx, hlev x hx⟩
        · rintro ⟨hx, h'⟩
          exact ⟨hx, by omega⟩
      have hle := hW h.le
      rw [hm] at hle
      rw [e1, hspan m le_rfl, hm]
      exact (top_le_iff.mp hle).symm
  have hsall : Submodule.span k s = ⊤ := by
    have e1 : {x | x ∈ s ∧ lev x < m} = s := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, hlev x h⟩⟩
    rw [← e1, hspan m le_rfl, hm]
  let b0 : Module.Basis s k (Fin d → k) :=
    Module.Basis.mk (v := ((↑) : s → Fin d → k)) hs (by rw [Subtype.range_coe]; exact hsall.ge)
  let e : s ≃ Fin d := b0.indexEquiv (Pi.basisFun k (Fin d))
  let b : Module.Basis (Fin d) k (Fin d → k) := b0.reindex e
  have hb : ∀ j, b j = (e.symm j : Fin d → k) := by
    intro j
    simp only [b, Module.Basis.reindex_apply]
    exact Module.Basis.mk_apply _ _ _
  let L := b.equivFun.symm
  let P : GL (Fin d) k :=
    ⟨LinearMap.toMatrix' (L : (Fin d → k) →ₗ[k] (Fin d → k)),
      LinearMap.toMatrix' (L.symm : (Fin d → k) →ₗ[k] (Fin d → k)),
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id],
      by rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]⟩
  refine ⟨P, fun j => lev (e.symm j), ?_⟩
  intro i v
  have hPv : (↑P : Matrix (Fin d) (Fin d) k).mulVec v = L v := LinearMap.toMatrix'_mulVec _ v
  rw [hPv, ← hall i]
  have himg : (⇑b '' {j | lev (e.symm j) < i}) = {x | x ∈ s ∧ lev x < i} := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      rw [hb]
      exact ⟨(e.symm j).2, hj⟩
    · rintro ⟨hx, hl⟩
      refine ⟨e ⟨x, hx⟩, ?_, ?_⟩
      · simpa using hl
      · rw [hb]
        simp
  rw [← himg, Module.Basis.mem_span_image]
  have hrep : ⇑(b.repr (L v)) = v := by
    rw [← Module.Basis.equivFun_apply]
    exact b.equivFun.apply_symm_apply v
  constructor
  · intro hv j hj
    change ∀ j, i ≤ lev (e.symm j) → v j = 0 at hv
    rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep] at hj
    show lev (e.symm j) < i
    by_contra hlt
    exact hj (hv j (not_lt.mp hlt))
  · intro hsub
    change ∀ j, i ≤ lev (e.symm j) → v j = 0
    intro j hj
    by_contra hne
    have hmem : j ∈ ((b.repr (L v)).support : Set (Fin d)) := by
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hrep]
      exact hne
    have h2 := hsub hmem
    simp only [Set.mem_setOf_eq] at h2
    omega
