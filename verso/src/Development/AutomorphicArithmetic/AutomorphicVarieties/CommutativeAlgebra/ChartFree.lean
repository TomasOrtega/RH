import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PartSpan

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Set `sel : (σ →₀ ℕ) → Option σ` to `fun n => if hn : n.support.Nonempty then some hn.choose else none`. Set `H : σ → MvPowerSeries σ O` to `fun i k => if sel (k + Finsupp.single i 1) = some i then coeff (k + Finsupp.single i 1) g else 0`. Establish `hc : ∀ i m, coeff m (H i) = if sel (m + Finsupp.single i 1) = some i then coeff (m + Finsupp.single i 1) g else 0` using `fun _ _ => rfl`. Use `⟨H, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `n`.

Rewrite using `[map_sum]`. Simplify using `only [coeff_monomial_mul, one_mul]`. Distinguish the cases in `hn : n.support.Nonempty`. Establish `hi0 : hn.choose ∈ n.support` using `hn.choose_spec`. Establish `hsel : sel n = some hn.choose` using `dif_pos hn`.

Establish `hle0 : Finsupp.single hn.choose 1 ≤ n`. Rewrite using `[Finsupp.single_le_iff]`. Conclude with `Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi0)`. Rewrite using `[Finset.sum_eq_single hn.choose]`. Rewrite using `[if_pos hle0, hc, tsub_add_cancel_of_le hle0, if_pos hsel]`.

Introduce `i _ hi`. Distinguish the cases in `hle : Finsupp.single i 1 ≤ n`. Rewrite using `[if_pos hle, hc, tsub_add_cancel_of_le hle, if_neg]`. Rewrite using `[hsel]`. Introduce `heq`.

Conclude with `hi (Option.some_injective _ heq).symm`. Rewrite using `[if_neg hle]`. Introduce `hnot`. Conclude with `absurd (Finset.mem_univ _) hnot`. Establish `hn0 : n = 0`.

Rewrite `hn` using `[Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty]`. Conclude with `hn`. Substitute `hn0` using the available equality. Rewrite using `[Finset.sum_eq_zero]`. Rewrite using `[coeff_zero_eq_constantCoeff_apply]`.

Conclude with `hg`. Introduce `i _`. Rewrite using `[if_neg]`. Introduce `hle`. Establish `h1` using `Finsupp.single_le_iff.1 hle`.

Simplify using `at h1`. Introduce `i`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, hc, zero_add, if_pos]`. Establish `hn : (Finsupp.single i 1 : σ →₀ ℕ).support.Nonempty` using `⟨i, by simp⟩`. Use `show (if hn : (Finsupp.single i 1 : σ →₀ ℕ).support.Nonempty then some hn.choose else none) = some i`.

Rewrite using `[dif_pos hn]`. Establish `hs : hn.choose ∈ ({i} : Finset σ)`. Rewrite using `[← Finsupp.support_single_ne_zero i (one_ne_zero : (1 : ℕ) ≠ 0)]`. Conclude with `hn.choose_spec`. Rewrite using `[Finset.mem_singleton.1 hs]`.
-/
private theorem exists_intertwiner_decomp_of_kernel_intertwines {σ O : Type} [Fintype σ] [CommRing O] (g : MvPowerSeries σ O)
    (hg : constantCoeff g = 0) :
    ∃ h : σ → MvPowerSeries σ O, g = ∑ i, monomial (Finsupp.single i 1) 1 * h i ∧
      ∀ i, constantCoeff (h i) = coeff (Finsupp.single i 1) g := by
  classical
  let sel : (σ →₀ ℕ) → Option σ := fun n =>
    if hn : n.support.Nonempty then some hn.choose else none
  let H : σ → MvPowerSeries σ O := fun i k =>
    if sel (k + Finsupp.single i 1) = some i then coeff (k + Finsupp.single i 1) g else 0
  have hc : ∀ i m, coeff m (H i) =
      if sel (m + Finsupp.single i 1) = some i then coeff (m + Finsupp.single i 1) g else 0 :=
    fun _ _ => rfl
  refine ⟨H, ?_, ?_⟩
  · ext n
    rw [map_sum]
    simp only [coeff_monomial_mul, one_mul]
    by_cases hn : n.support.Nonempty
    · have hi0 : hn.choose ∈ n.support := hn.choose_spec
      have hsel : sel n = some hn.choose := dif_pos hn
      have hle0 : Finsupp.single hn.choose 1 ≤ n := by
        rw [Finsupp.single_le_iff]
        exact Nat.one_le_iff_ne_zero.2 (Finsupp.mem_support_iff.1 hi0)
      rw [Finset.sum_eq_single hn.choose]
      · rw [if_pos hle0, hc, tsub_add_cancel_of_le hle0, if_pos hsel]
      · intro i _ hi
        by_cases hle : Finsupp.single i 1 ≤ n
        · rw [if_pos hle, hc, tsub_add_cancel_of_le hle, if_neg]
          rw [hsel]
          intro heq
          exact hi (Option.some_injective _ heq).symm
        · rw [if_neg hle]
      · intro hnot
        exact absurd (Finset.mem_univ _) hnot
    · have hn0 : n = 0 := by
        rw [Finset.not_nonempty_iff_eq_empty, Finsupp.support_eq_empty] at hn
        exact hn
      subst hn0
      rw [Finset.sum_eq_zero]
      · rw [coeff_zero_eq_constantCoeff_apply]
        exact hg
      · intro i _
        rw [if_neg]
        intro hle
        have h1 := Finsupp.single_le_iff.1 hle
        simp at h1
  · intro i
    rw [← coeff_zero_eq_constantCoeff_apply, hc, zero_add, if_pos]
    have hn : (Finsupp.single i 1 : σ →₀ ℕ).support.Nonempty := ⟨i, by simp⟩
    show (if hn : (Finsupp.single i 1 : σ →₀ ℕ).support.Nonempty then some hn.choose else none) = some i
    rw [dif_pos hn]
    have hs : hn.choose ∈ ({i} : Finset σ) := by
      rw [← Finsupp.support_single_ne_zero i (one_ne_zero : (1 : ℕ) ≠ 0)]
      exact hn.choose_spec
    rw [Finset.mem_singleton.1 hs]

/- English proof (translation)
Take `⟨g, hf, hg⟩` from `exists_intertwiner_decomp_of_kernel_intertwines f h0`. Establish `hg0 : ∀ i, constantCoeff (g i) = 0` using `fun i => (hg i).trans (h1 i)`. Use `choose k hk _ using fun i => exists_intertwiner_decomp_of_kernel_intertwines (g i) (hg0 i)`. Establish `hz : ∀ i, W.π (monomial (Finsupp.single i 1) 1) ∈ RingHom.ker (W.origin h)`. Introduce `i`.

Rewrite using `[RingHom.mem_ker]`. Use `erw [WPres.origin_π]`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg]`. Conclude with `(Finsupp.single_ne_zero.2 one_ne_zero).symm`. Rewrite using `[hf, map_sum]`.

Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hk i, Finset.mul_sum, map_sum]`. Use `Ideal.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, map_mul, map_mul, pow_two]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (hz i) (hz j))`.
-/
private lemma π_mem_sq {O X R : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    (W : WPres O X R) (h : W.HasOrigin) (f : MvPowerSeries W.σ O) (h0 : constantCoeff f = 0)
    (h1 : ∀ i, coeff (Finsupp.single i 1) f = 0) : W.π f ∈ RingHom.ker (W.origin h) ^ 2 := by
  classical
  obtain ⟨g, hf, hg⟩ := exists_intertwiner_decomp_of_kernel_intertwines f h0
  have hg0 : ∀ i, constantCoeff (g i) = 0 := fun i => (hg i).trans (h1 i)
  choose k hk _ using fun i => exists_intertwiner_decomp_of_kernel_intertwines (g i) (hg0 i)
  have hz : ∀ i, W.π (monomial (Finsupp.single i 1) 1) ∈ RingHom.ker (W.origin h) := by
    intro i
    rw [RingHom.mem_ker]
    erw [WPres.origin_π]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_monomial, if_neg]
    exact (Finsupp.single_ne_zero.2 one_ne_zero).symm
  rw [hf, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [hk i, Finset.mul_sum, map_sum]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [← mul_assoc, map_mul, map_mul, pow_two]
  exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_mul (hz i) (hz j))

/- English proof (translation)
Introduce `O X R _ _ _ _ _ _ W h hinj`. Set `e : MvPowerSeries W.σ O ≃ₐ[O] R` to `AlgEquiv.ofBijective W.π ⟨hinj, W.surj⟩`. Set `μ : MvPowerSeries W.σ O →ₐ[O] MvPowerSeries W.σ (FractionRing O)` to `{ MvPowerSeries.map (algebraMap O (FractionRing O)) with commutes' := fun r => by`. Use extensionality with `n`. Simplify using `[MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C] }`.

Set `φ : R →ₐ[O] MvPowerSeries W.σ (FractionRing O)` to `μ.comp e.symm.toAlgHom`. Establish `hφ : ∀ g, φ (W.π g) = MvPowerSeries.map (algebraMap O (FractionRing O)) g`. Introduce `g`. Use `show μ (e.symm (e g)) = _`. Rewrite using `[e.symm_apply_apply]`.

Both sides reduce to the same expression. Use `⟨φ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `j f hf`. Establish `hf' : f ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt j)` using `hf`. Take `⟨g, hg, rfl⟩` from `hf'`.

Establish `hg' : ∀ n, Finsupp.weight W.wt n ≠ j → coeff n g = 0` using `hg`. Use `show ∀ n, Finsupp.weight W.wt n ≠ j → coeff n (φ (W.π g)) = 0`. Introduce `n hn`. Rewrite using `[hφ, MvPowerSeries.coeff_map, hg' n hn, map_zero]`. Introduce `f`.

Take `⟨g, rfl⟩` from `W.surj f`. Rewrite using `[hφ, WPres.origin_π, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map]`. Introduce `i`. Use `⟨W.π (MvPowerSeries.X i), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hφ, MvPowerSeries.map_X, MvPowerSeries.coeff_X, if_pos rfl]`.

Conclude with `one_ne_zero`. Introduce `i' hi'`. Rewrite using `[hφ, MvPowerSeries.map_X, MvPowerSeries.coeff_X, if_neg]`. Introduce `heq`. Conclude with `hi' (Finsupp.single_left_injective one_ne_zero heq)`.

Introduce `f hf0 hlin`. Take `⟨g, rfl⟩` from `W.surj f`. Unfold `satSq`. Use `show ∃ c : O, c ≠ 0 ∧ c • W.π g ∈ RingHom.ker (W.origin h) ^ 2`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations.

Rewrite using `[one_smul]`. Apply `π_mem_sq W h g` to reduce the goal to its premises. Rewrite using `[← WPres.origin_π W h]`. Conclude with `hf0`. Introduce `i`.

Establish `hi` using `hlin i`. Rewrite `hi` using `[hφ, MvPowerSeries.coeff_map]`. Conclude with `IsFractionRing.injective O (FractionRing O) (hi.trans (map_zero _).symm)`. Introduce `s show φ (W.π (MvPowerSeries.X s)) = MvPowerSeries.X s`. Rewrite using `[hφ, MvPowerSeries.map_X]`.
-/
theorem UpperTheory.V.Alg.chart_free :
    ∀ (O X R : Type) [CommRing O] [IsDomain O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R) (h : W.HasOrigin), Function.Injective W.π → ∃ φ : R →ₐ[O] MvPowerSeries W.σ (FractionRing O), IsChart W.part (W.origin h) W.wt φ ∧ ∀ s, φ (W.z s) = MvPowerSeries.X s := by
  intro O X R _ _ _ _ _ _ W h hinj
  classical
  let e : MvPowerSeries W.σ O ≃ₐ[O] R := AlgEquiv.ofBijective W.π ⟨hinj, W.surj⟩
  let μ : MvPowerSeries W.σ O →ₐ[O] MvPowerSeries W.σ (FractionRing O) :=
    { MvPowerSeries.map (algebraMap O (FractionRing O)) with
      commutes' := fun r => by
        ext n
        simp [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C] }
  let φ : R →ₐ[O] MvPowerSeries W.σ (FractionRing O) := μ.comp e.symm.toAlgHom
  have hφ : ∀ g, φ (W.π g) = MvPowerSeries.map (algebraMap O (FractionRing O)) g := by
    intro g
    show μ (e.symm (e g)) = _
    rw [e.symm_apply_apply]
    rfl
  refine ⟨φ, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro j f hf
    have hf' : f ∈ Submodule.map W.π.toLinearMap (wtPart O W.wt j) := hf
    obtain ⟨g, hg, rfl⟩ := hf'
    have hg' : ∀ n, Finsupp.weight W.wt n ≠ j → coeff n g = 0 := hg
    show ∀ n, Finsupp.weight W.wt n ≠ j → coeff n (φ (W.π g)) = 0
    intro n hn
    rw [hφ, MvPowerSeries.coeff_map, hg' n hn, map_zero]
  · intro f
    obtain ⟨g, rfl⟩ := W.surj f
    rw [hφ, WPres.origin_π, ← coeff_zero_eq_constantCoeff_apply,
      ← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map]
  · intro i
    refine ⟨W.π (MvPowerSeries.X i), ?_, ?_⟩
    · rw [hφ, MvPowerSeries.map_X, MvPowerSeries.coeff_X, if_pos rfl]
      exact one_ne_zero
    · intro i' hi'
      rw [hφ, MvPowerSeries.map_X, MvPowerSeries.coeff_X, if_neg]
      intro heq
      exact hi' (Finsupp.single_left_injective one_ne_zero heq)
  · intro f hf0 hlin
    obtain ⟨g, rfl⟩ := W.surj f
    unfold satSq
    show ∃ c : O, c ≠ 0 ∧ c • W.π g ∈ RingHom.ker (W.origin h) ^ 2
    refine ⟨1, one_ne_zero, ?_⟩
    rw [one_smul]
    apply π_mem_sq W h g
    · rw [← WPres.origin_π W h]
      exact hf0
    · intro i
      have hi := hlin i
      rw [hφ, MvPowerSeries.coeff_map] at hi
      exact IsFractionRing.injective O (FractionRing O) (hi.trans (map_zero _).symm)
  · intro s
    show φ (W.π (MvPowerSeries.X s)) = MvPowerSeries.X s
    rw [hφ, MvPowerSeries.map_X]
