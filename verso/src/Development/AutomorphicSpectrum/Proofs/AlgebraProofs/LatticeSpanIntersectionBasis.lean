import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocalRingModTEmbedsStrictHenselian
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigCoordApply

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `V C _ _ _ _ _ _ W _ _ _ _ _ Lie n w hfg _ hw hsat j`. Set `W' : Submodule C W` to `Submodule.span C (Set.range w)`. Take `⟨p, q, u, t, -, hu, ht, -, -, hspan⟩` from `exists_basis_split_of_exact_of_fg_valuationRing V C W' W (W ⧸ W') W'.subtype W'.mkQ W'.injective_subtype (LinearMap.exact_subtype_mkQ W') Lie hfg`. Establish `hwW : ∀ i, w i ∈ W'` using `fun i => Submodule.subset_span ⟨i, rfl⟩`. Establish `hli : LinearIndependent C (Sum.elim w t)`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `f hf`. Rewrite `hf` using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at hf`. Establish `h1 : ∀ i, f (Sum.inr i) = 0`.

Establish `h` using `congrArg W'.mkQ hf`. Establish `hz : ∀ i, W'.mkQ (w i) = 0` using `fun i => by`. Simplify using `using hwW i`. Simplify using `only [map_add, map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero, zero_add, map_zero] at h`. Conclude with `Fintype.linearIndependent_iff.mp ht _ h`.

Establish `h2 : ∀ i, f (Sum.inl i) = 0`. Simplify using `only [h1, zero_smul, Finset.sum_const_zero, add_zero] at hf`. Conclude with `Fintype.linearIndependent_iff.mp hw _ hf`. Introduce and unpack `(i | i)`. Conclude with `h2 i`.

Conclude with `h1 i`. Take `⟨g, hg⟩` from `(Finsupp.linearCombination C (Sum.elim w t)).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hli)`. Establish `hgs : ∀ a, g (Sum.elim w t a) = Finsupp.single a 1` using `fun a => by`. Establish `h1` using `LinearMap.congr_fun hg (Finsupp.single a 1)`. Simplify `h1` using `[Finsupp.linearCombination_single]`.

Set `φ : Module.Dual C W` to `Finsupp.lapply (Sum.inl j) ∘ₗ g`. Establish `hφw : ∀ k, φ (w k) = if k = j then 1 else 0` using `fun k => by`. Establish `h` using `hgs (Sum.inl k)`. Simplify using `only [Sum.elim_inl] at h`. Simplify using `[φ, h, Finsupp.single_apply]`.

Establish `hφt : ∀ i, φ (t i) = 0` using `fun i => by`. Establish `h` using `hgs (Sum.inr i)`. Simplify using `only [Sum.elim_inr] at h`. Simplify using `[φ, h, Finsupp.single_apply]`. Set `R : Submodule V C` to `LinearMap.range (Algebra.linearMap V C)`.

Establish `hone : (1 : C) ∈ R` using `⟨1, by simp⟩`. Establish `hzero : (0 : C) ∈ R` using `R.zero_mem`. Establish `hspw : Submodule.span V (Set.range w) ≤ R.comap (φ.restrictScalars V)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`.

Express the relevant statement in the definitionally equal form `φ (w k) ∈ R`. Rewrite using `[hφw]`. Use `split_ifs`. Conclude with `hone`. Conclude with `hzero`.

Establish `hle : Lie ≤ R.comap (φ.restrictScalars V)`. Rewrite using `[← hspan, Submodule.span_le]`. Introduce and unpack `_ ⟨i | i, rfl⟩`. Apply `hspw` to reduce the goal to its premises. Establish `hmem : u i ∈ Lie.comap (W'.subtype.restrictScalars V)`.

Rewrite using `[← hu]`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Conclude with `(hsat _).mpr ⟨hmem, (u i).2⟩`. Express the relevant statement in the definitionally equal form `φ (t i) ∈ R`. Rewrite using `[hφt]`.

Conclude with `hzero`. Use `⟨φ, fun y hy => ?_, hφw⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hle hy`. Conclude with `⟨a, by simpa using ha⟩`.
-/
theorem exists_dual_integral_of_saturated_free_part :
    ∀ (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [Algebra V C]
      [IsFractionRing V C] (W : Type) [AddCommGroup W] [Module C W] [Module V W]
      [IsScalarTower V C W] [FiniteDimensional C W] (Lie : Submodule V W) (n : ℕ) (w : Fin n → W),
      Lie.FG → Submodule.span C (Lie : Set W) = ⊤ → LinearIndependent C w →
      (∀ y, y ∈ Submodule.span V (Set.range w) ↔ y ∈ Lie ∧ y ∈ Submodule.span C (Set.range w)) →
      ∀ j, ∃ φ : Module.Dual C W, (∀ y ∈ Lie, φ y ∈ (algebraMap V C).range) ∧
        ∀ k, φ (w k) = if k = j then 1 else 0 := by
  intro V C _ _ _ _ _ _ W _ _ _ _ _ Lie n w hfg _ hw hsat j
  classical
  let W' : Submodule C W := Submodule.span C (Set.range w)
  obtain ⟨p, q, u, t, -, hu, ht, -, -, hspan⟩ :=
    exists_basis_split_of_exact_of_fg_valuationRing V C W' W (W ⧸ W') W'.subtype W'.mkQ
      W'.injective_subtype (LinearMap.exact_subtype_mkQ W') Lie hfg
  have hwW : ∀ i, w i ∈ W' := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hli : LinearIndependent C (Sum.elim w t) := by
    rw [Fintype.linearIndependent_iff]
    intro f hf
    rw [Fintype.sum_sum_type] at hf
    simp only [Sum.elim_inl, Sum.elim_inr] at hf
    have h1 : ∀ i, f (Sum.inr i) = 0 := by
      have h := congrArg W'.mkQ hf
      have hz : ∀ i, W'.mkQ (w i) = 0 := fun i => by
        simpa using hwW i
      simp only [map_add, map_sum, map_smul, hz, smul_zero, Finset.sum_const_zero, zero_add,
        map_zero] at h
      exact Fintype.linearIndependent_iff.mp ht _ h
    have h2 : ∀ i, f (Sum.inl i) = 0 := by
      simp only [h1, zero_smul, Finset.sum_const_zero, add_zero] at hf
      exact Fintype.linearIndependent_iff.mp hw _ hf
    rintro (i | i)
    · exact h2 i
    · exact h1 i
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination C (Sum.elim w t)).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hli)
  have hgs : ∀ a, g (Sum.elim w t a) = Finsupp.single a 1 := fun a => by
    have h1 := LinearMap.congr_fun hg (Finsupp.single a 1)
    simpa [Finsupp.linearCombination_single] using h1
  let φ : Module.Dual C W := Finsupp.lapply (Sum.inl j) ∘ₗ g
  have hφw : ∀ k, φ (w k) = if k = j then 1 else 0 := fun k => by
    have h := hgs (Sum.inl k)
    simp only [Sum.elim_inl] at h
    simp [φ, h, Finsupp.single_apply]
  have hφt : ∀ i, φ (t i) = 0 := fun i => by
    have h := hgs (Sum.inr i)
    simp only [Sum.elim_inr] at h
    simp [φ, h, Finsupp.single_apply]
  let R : Submodule V C := LinearMap.range (Algebra.linearMap V C)
  have hone : (1 : C) ∈ R := ⟨1, by simp⟩
  have hzero : (0 : C) ∈ R := R.zero_mem
  have hspw : Submodule.span V (Set.range w) ≤ R.comap (φ.restrictScalars V) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    change φ (w k) ∈ R
    rw [hφw]
    split_ifs
    · exact hone
    · exact hzero
  have hle : Lie ≤ R.comap (φ.restrictScalars V) := by
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨i | i, rfl⟩
    · apply hspw
      have hmem : u i ∈ Lie.comap (W'.subtype.restrictScalars V) := by
        rw [← hu]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact (hsat _).mpr ⟨hmem, (u i).2⟩
    · change φ (t i) ∈ R
      rw [hφt]
      exact hzero
  refine ⟨φ, fun y hy => ?_, hφw⟩
  obtain ⟨a, ha⟩ := hle hy
  exact ⟨a, by simpa using ha⟩

end GlobalTheory.CompanionTheory.Ar.Flat
