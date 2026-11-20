import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private theorem ker_gen_closed {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (I : Ideal A)
    (f : A) (h : ∀ N : ℕ, ∃ g ∈ I, f - g ∈ maximalIdeal A ^ N) : f ∈ I := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ I) (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top
  have hmem : Ideal.Quotient.mk I f ∈ ⨅ i, (maximalIdeal A) ^ i • (⊤ : Submodule A (A ⧸ I)) := by
    rw [Submodule.mem_iInf]
    intro N
    obtain ⟨g, hg, hfg⟩ := h N
    have heq : Ideal.Quotient.mk I f = (f - g) • (1 : A ⧸ I) := by
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one, map_sub,
        Ideal.Quotient.eq_zero_iff_mem.mpr hg, sub_zero]
    rw [heq]
    exact Submodule.smul_mem_smul hfg Submodule.mem_top
  rw [hbot, Submodule.mem_bot] at hmem
  exact Ideal.Quotient.eq_zero_iff_mem.mp hmem

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem ker_gen_approx {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X]
    {σ : Type} [Finite σ] (wt : σ → X) (f : MvPowerSeries σ O) (N : ℕ) :
    ∃ T : Finset X, f - ∑ j ∈ T, wcomp O wt j f ∈ maximalIdeal (MvPowerSeries σ O) ^ N := by
  classical
  set D := (Finsupp.finite_of_degree_lt (σ := σ) N).toFinset with hD
  refine ⟨D.image (Finsupp.weight wt), ?_⟩
  have hX : ∀ i : σ, (AlgHom.id O (MvPowerSeries σ O)) (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries σ O) := by
    intro i
    rw [AlgHom.id_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have hord : ((N : ℕ) : ℕ∞) ≤ (f - ∑ j ∈ D.image (Finsupp.weight wt), wcomp O wt j f).order := by
    apply MvPowerSeries.nat_le_order
    intro d hd
    rw [map_sub, map_sum]
    simp only [coeff_wcomp]
    rw [Finset.sum_ite_eq, if_pos, sub_self]
    exact Finset.mem_image_of_mem _ (by simpa [hD] using hd)
  have key := GlobalTheory.algHom_mem_pow_of_le_order (AlgHom.id O (MvPowerSeries σ O)) hX hord
  simpa using key

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.Alg.ker_gen :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] (σ : Type) [Finite σ] (wt : σ → X) (J : Ideal (MvPowerSeries σ O)), IsHomog O wt J →
      ∃ (n : ℕ) (f : Fin n → MvPowerSeries σ O) (c : Fin n → X), (∀ i, f i ∈ wtPart O wt (c i)) ∧ J = Ideal.span (Set.range f) := by
  intro O _ _ _ _ X _ σ _ wt J hJ
  classical
  set G : Set (MvPowerSeries σ O) := {g | ∃ f ∈ J, ∃ j : X, g = wcomp O wt j f} with hG
  have hGJ : Ideal.span G ≤ J := by
    rw [Ideal.span_le]
    rintro g ⟨f, hf, j, rfl⟩
    exact hJ f hf j
  have hJG : J ≤ Ideal.span G := by
    intro f hf
    apply ker_gen_closed (Ideal.span G) f
    intro N
    obtain ⟨T, hT⟩ := ker_gen_approx wt f N
    exact ⟨_, Ideal.sum_mem _ (fun j _ => Ideal.subset_span ⟨f, hf, j, rfl⟩), hT⟩
  have hfg : (Submodule.span (MvPowerSeries σ O) G).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsG, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg
  have hchoice : ∀ g : s, ∃ j : X, g.1 ∈ wtPart O wt j := by
    rintro ⟨g, hg⟩
    obtain ⟨f, _, j, rfl⟩ := hsG hg
    exact ⟨j, wcomp_mem O wt j f⟩
  choose c hc using hchoice
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, fun i => c (s.equivFin.symm i), fun i => hc _, ?_⟩
  have hrange : Set.range (fun i => (s.equivFin.symm i).1) = (s : Set (MvPowerSeries σ O)) := by
    ext g
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hg
      exact ⟨s.equivFin ⟨g, hg⟩, by simp⟩
  rw [hrange]
  calc J = Ideal.span G := le_antisymm hJG hGJ
    _ = Ideal.span (s : Set (MvPowerSeries σ O)) := hspan
