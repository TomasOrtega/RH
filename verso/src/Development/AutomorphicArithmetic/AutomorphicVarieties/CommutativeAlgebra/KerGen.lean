import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Establish `hbot` using `Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := A ⧸ I) (maximalIdeal A) (maximalIdeal.isMaximal A).ne_top`. Establish `hmem : Ideal.Quotient.mk I f ∈ ⨅ i, (maximalIdeal A) ^ i • (⊤ : Submodule A (A ⧸ I))`. Rewrite using `[Submodule.mem_iInf]`. Introduce `N`. Take `⟨g, hg, hfg⟩` from `h N`.

Establish `heq : Ideal.Quotient.mk I f = (f - g) • (1 : A ⧸ I)`. Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_one, map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hg, sub_zero]`. Rewrite using `[heq]`. Conclude with `Submodule.smul_mem_smul hfg Submodule.mem_top`. Rewrite `hmem` using `[hbot, Submodule.mem_bot]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp hmem`.
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
Use `set D := (Finsupp.finite_of_degree_lt (σ := σ) N).toFinset with hD`. Use `⟨D.image (Finsupp.weight wt), ?_⟩` and prove the remaining obligations. Establish `hX : ∀ i : σ, (AlgHom.id O (MvPowerSeries σ O)) (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries σ O)`. Introduce `i`. Rewrite using `[AlgHom.id_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]`.

Simplify using the standard rewrite rules. Establish `hord : ((N : ℕ) : ℕ∞) ≤ (f - ∑ j ∈ D.image (Finsupp.weight wt), wcomp O wt j f).order`. Apply `MvPowerSeries.nat_le_order` to reduce the goal to its premises. Introduce `d hd`. Rewrite using `[map_sub, map_sum]`.

Simplify using `only [coeff_wcomp]`. Rewrite using `[Finset.sum_ite_eq, if_pos, sub_self]`. Conclude with `Finset.mem_image_of_mem _ (by simpa [hD] using hd)`. Establish `key` using `GlobalTheory.algHom_mem_pow_of_le_order (AlgHom.id O (MvPowerSeries σ O)) hX hord`. Simplify using `using key`.
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
Introduce `O _ _ _ _ X _ σ _ wt J hJ`. Use `set G : Set (MvPowerSeries σ O) := {g | ∃ f ∈ J, ∃ j : X, g = wcomp O wt j f} with hG`. Establish `hGJ : Ideal.span G ≤ J`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `g ⟨f, hf, j, rfl⟩`.

Conclude with `hJ f hf j`. Establish `hJG : J ≤ Ideal.span G`. Introduce `f hf`. Apply `ker_gen_closed (Ideal.span G) f` to reduce the goal to its premises. Introduce `N`.

Take `⟨T, hT⟩` from `ker_gen_approx wt f N`. Conclude with `⟨_, Ideal.sum_mem _ (fun j _ => Ideal.subset_span ⟨f, hf, j, rfl⟩), hT⟩`. Establish `hfg : (Submodule.span (MvPowerSeries σ O) G).FG` using `IsNoetherian.noetherian _`. Take `⟨s, hsG, hspan⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset G).mp hfg`. Establish `hchoice : ∀ g : s, ∃ j : X, g.1 ∈ wtPart O wt j`.

Introduce and unpack `⟨g, hg⟩`. Take `⟨f, _, j, rfl⟩` from `hsG hg`. Conclude with `⟨j, wcomp_mem O wt j f⟩`. Use `choose c hc using hchoice`. Use `⟨s.card, fun i => (s.equivFin.symm i).1, fun i => c (s.equivFin.symm i), fun i => hc _, ?_⟩` and prove the remaining obligations.

Establish `hrange : Set.range (fun i => (s.equivFin.symm i).1) = (s : Set (MvPowerSeries σ O))`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `(s.equivFin.symm i).2`.

Introduce `hg`. Conclude with `⟨s.equivFin ⟨g, hg⟩, by simp⟩`. Rewrite using `[hrange]`. Combine the equalities or inequalities in the displayed calculation.
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
