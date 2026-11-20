import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CountCoeEqMultiplicity

open NumberField Module IsDedekindDomain

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Dedekind

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/- English proof (translation)
Establish `hs0 : s ≠ 0` using `fun h => hs (h ▸ v.asIdeal.zero_mem)`. Establish `hsp : Ideal.span {s} ≠ ⊥` using `by simpa using hs0`. Rewrite using `[← FractionalIdeal.coeIdeal_span_singleton, count_coe_eq_multiplicity v hsp]`. Establish `: multiplicity v.asIdeal (Ideal.span {s}) = 0`. Rewrite using `[multiplicity_eq_zero, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`.

Conclude with `hs`. Simplify using `[this]`.
-/
theorem count_span_unit (v : HeightOneSpectrum R) (s : R) (hs : s ∉ v.asIdeal) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K s)) = 0 := by
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  have hsp : Ideal.span {s} ≠ ⊥ := by simpa using hs0
  rw [← FractionalIdeal.coeIdeal_span_singleton, count_coe_eq_multiplicity v hsp]
  have : multiplicity v.asIdeal (Ideal.span {s}) = 0 := by
    rw [multiplicity_eq_zero, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hs
  simp [this]

/- English proof (translation)
The claim follows from `FractionalIdeal.count_mono K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy0) (FractionalIdeal.spanSingleton_le_iff_mem.mpr hy)`.
-/
theorem count_le_of_mem (v : HeightOneSpectrum R) {I : FractionalIdeal (nonZeroDivisors R) K} {y : K}
    (hy : y ∈ I) (hy0 : y ≠ 0) :
    FractionalIdeal.count K v I ≤ FractionalIdeal.count K v (FractionalIdeal.spanSingleton _ y) :=
  FractionalIdeal.count_mono K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy0)
    (FractionalIdeal.spanSingleton_le_iff_mem.mpr hy)

/- English proof (translation)
Proceed by induction on `hT using Finset.Nonempty.cons_induction with`. Consider the case `singleton a => exact ⟨a, Finset.mem_singleton_self a, by simp⟩`. Consider the case `cons a T ha hT ih`. Establish `hT0 : ∀ g ∈ T, g ≠ 0` using `fun g hg => h0 g (Finset.mem_cons_of_mem hg)`. Take `⟨g, hg, hgm⟩` from `ih hT0`.

Establish `ha0 : Ideal.span {a} ≠ ⊥` using `by simpa using h0 a (Finset.mem_cons_self a T)`. Establish `hT' : Ideal.span (T : Set R) ≠ ⊥`. Introduce `hb`. Establish `: g ∈ Ideal.span (T : Set R)` using `Ideal.subset_span hg`. Rewrite `this` using `[hb, Ideal.mem_bot]`.

Conclude with `hT0 g hg this`. Establish `hspan : Ideal.span ((Finset.cons a T ha : Finset R) : Set R) = Ideal.span {a} ⊔ Ideal.span (T : Set R)`. Rewrite using `[Finset.coe_cons, Ideal.span_insert]`. Rewrite using `[hspan, HeightOneSpectrum.multiplicity_sup v ha0 hT']`. Break down `le_total (multiplicity v.asIdeal (Ideal.span {a})) (multiplicity v.asIdeal (Ideal.span (T : Set R))) with h | h` into its components or cases.

Conclude with `⟨a, Finset.mem_cons_self a T, (min_eq_left h).symm⟩`. Conclude with `⟨g, Finset.mem_cons_of_mem hg, by rw [min_eq_right h, hgm]⟩`.
-/
theorem exists_exact_ideal (v : HeightOneSpectrum R) (T : Finset R) (hT : T.Nonempty) (h0 : ∀ g ∈ T, g ≠ 0) :
    ∃ g ∈ T, multiplicity v.asIdeal (Ideal.span {g}) = multiplicity v.asIdeal (Ideal.span (T : Set R)) := by
  classical
  induction hT using Finset.Nonempty.cons_induction with
  | singleton a => exact ⟨a, Finset.mem_singleton_self a, by simp⟩
  | cons a T ha hT ih =>
    have hT0 : ∀ g ∈ T, g ≠ 0 := fun g hg => h0 g (Finset.mem_cons_of_mem hg)
    obtain ⟨g, hg, hgm⟩ := ih hT0
    have ha0 : Ideal.span {a} ≠ ⊥ := by simpa using h0 a (Finset.mem_cons_self a T)
    have hT' : Ideal.span (T : Set R) ≠ ⊥ := by
      intro hb
      have : g ∈ Ideal.span (T : Set R) := Ideal.subset_span hg
      rw [hb, Ideal.mem_bot] at this
      exact hT0 g hg this
    have hspan : Ideal.span ((Finset.cons a T ha : Finset R) : Set R) = Ideal.span {a} ⊔ Ideal.span (T : Set R) := by
      rw [Finset.coe_cons, Ideal.span_insert]
    rw [hspan, HeightOneSpectrum.multiplicity_sup v ha0 hT']
    rcases le_total (multiplicity v.asIdeal (Ideal.span {a})) (multiplicity v.asIdeal (Ideal.span (T : Set R))) with h | h
    · exact ⟨a, Finset.mem_cons_self a T, (min_eq_left h).symm⟩
    · exact ⟨g, Finset.mem_cons_of_mem hg, by rw [min_eq_right h, hgm]⟩

/- English proof (translation)
Take `⟨a, J, ha, hIJ⟩` from `FractionalIdeal.exists_eq_spanSingleton_mul I`. Establish `hJ0 : J ≠ ⊥`. Introduce and unpack `rfl`. Apply `hI` to reduce the goal to its premises. Rewrite using `[hIJ, FractionalIdeal.coeIdeal_bot, mul_zero]`.

Take `⟨T, hT⟩` from `(IsNoetherian.noetherian J : J.FG)`. Use `set T' := T.filter (· ≠ 0)`. Establish `hT' : Ideal.span (T' : Set R) = J`. Rewrite using `[← hT]`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `Ideal.span_mono (by intro z hz; exact (Finset.mem_filter.mp hz).1)`. Rewrite using `[Ideal.span_le]`. Introduce `z hz`. Distinguish the cases in `hz0 : z = 0`. Rewrite using `[hz0]`.

Conclude with `Ideal.zero_mem _`. Conclude with `Ideal.subset_span (Finset.mem_filter.mpr ⟨hz, hz0⟩)`. Establish `hne : T'.Nonempty`. Assume the negation of the conclusion as `hemp`. Rewrite `hemp` using `[Finset.not_nonempty_iff_eq_empty]`.

Apply `hJ0` to reduce the goal to its premises. Rewrite using `[← hT', hemp, Finset.coe_empty, Ideal.span_empty]`. Take `⟨g, hgT, hgm⟩` from `exists_exact_ideal v T' hne (fun g hg => (Finset.mem_filter.mp hg).2)`. Establish `hg0 : g ≠ 0` using `(Finset.mem_filter.mp hgT).2`. Establish `hgJ : g ∈ J` using `hT' ▸ Ideal.subset_span hgT`.

Establish `ha' : algebraMap R K a ≠ 0` using `(IsFractionRing.injective R K).ne_iff.mpr ha |>.trans_eq (map_zero _) |> fun h => by`. Simplify using `using (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr ha`. Establish `hg' : algebraMap R K g ≠ 0` using `(map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hg0`. Use `⟨(algebraMap R K a)⁻¹ * algebraMap R K g, ?_, mul_ne_zero (inv_ne_zero ha') hg', ?_⟩` and prove the remaining obligations. Rewrite using `[hIJ]`.

Conclude with `FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) (FractionalIdeal.mem_coeIdeal_of_mem _ hgJ)`. Establish `hsa : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a)⁻¹ ≠ 0` using `FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero ha')`. Establish `hsg : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K g) ≠ 0` using `FractionalIdeal.spanSingleton_ne_zero_iff.mpr hg'`. Establish `hJc : (J : FractionalIdeal (nonZeroDivisors R) K) ≠ 0`. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero]` and apply the resulting hypothesis.

Establish `hsp : Ideal.span {g} ≠ ⊥` using `by simpa using hg0`. Rewrite using `[← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v hsa hsg, hIJ, FractionalIdeal.count_mul K v hsa hJc, ← FractionalIdeal.coeIdeal_span_singleton, count_coe_eq_multiplicity v hsp, count_coe_eq_multiplicity v hJ0, hgm, hT']`.
-/
theorem exists_exact (v : HeightOneSpectrum R) {I : FractionalIdeal (nonZeroDivisors R) K} (hI : I ≠ 0) :
    ∃ y ∈ I, y ≠ 0 ∧
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) y) = FractionalIdeal.count K v I := by
  classical
  obtain ⟨a, J, ha, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    apply hI
    rw [hIJ, FractionalIdeal.coeIdeal_bot, mul_zero]
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian J : J.FG)
  set T' := T.filter (· ≠ 0)
  have hT' : Ideal.span (T' : Set R) = J := by
    rw [← hT]
    apply le_antisymm
    · exact Ideal.span_mono (by intro z hz; exact (Finset.mem_filter.mp hz).1)
    · rw [Ideal.span_le]
      intro z hz
      by_cases hz0 : z = 0
      · rw [hz0]; exact Ideal.zero_mem _
      · exact Ideal.subset_span (Finset.mem_filter.mpr ⟨hz, hz0⟩)
  have hne : T'.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    apply hJ0
    rw [← hT', hemp, Finset.coe_empty, Ideal.span_empty]
  obtain ⟨g, hgT, hgm⟩ := exists_exact_ideal v T' hne (fun g hg => (Finset.mem_filter.mp hg).2)
  have hg0 : g ≠ 0 := (Finset.mem_filter.mp hgT).2
  have hgJ : g ∈ J := hT' ▸ Ideal.subset_span hgT
  have ha' : algebraMap R K a ≠ 0 := (IsFractionRing.injective R K).ne_iff.mpr ha |>.trans_eq (map_zero _) |> fun h => by
    simpa using (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr ha
  have hg' : algebraMap R K g ≠ 0 := (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hg0
  refine ⟨(algebraMap R K a)⁻¹ * algebraMap R K g, ?_, mul_ne_zero (inv_ne_zero ha') hg', ?_⟩
  · rw [hIJ]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hgJ)
  · have hsa : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K a)⁻¹ ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero ha')
    have hsg : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K g) ≠ 0 :=
      FractionalIdeal.spanSingleton_ne_zero_iff.mpr hg'
    have hJc : (J : FractionalIdeal (nonZeroDivisors R) K) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have hsp : Ideal.span {g} ≠ ⊥ := by simpa using hg0
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K v hsa hsg, hIJ,
      FractionalIdeal.count_mul K v hsa hJc, ← FractionalIdeal.coeIdeal_span_singleton,
      count_coe_eq_multiplicity v hsp, count_coe_eq_multiplicity v hJ0, hgm, hT']

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.prod_empty]`. Conclude with `(FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩`. Consider the case `insert j s hj ih`.

Rewrite using `[Finset.prod_insert hj, Finset.prod_insert hj]`. Conclude with `FractionalIdeal.mul_mem_mul (hm j) ih`.
-/
theorem prod_mem_prod' {ι : Type*} (s : Finset ι) (𝔞 : ι → FractionalIdeal (nonZeroDivisors R) K)
    (m : ι → K) (hm : ∀ i, m i ∈ 𝔞 i) : ∏ i ∈ s, m i ∈ ∏ i ∈ s, 𝔞 i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨1, map_one _⟩
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj]
    exact FractionalIdeal.mul_mem_mul (hm j) ih

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `Submodule.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Establish `hp : ∏ i, M (σ i) i ∈ ∏ i, 𝔞 i`. Establish `: ∏ i, M (σ i) i = ∏ j, M j (σ.symm j)`. Rewrite using `[← Equiv.prod_comp σ (fun j => M j (σ.symm j))]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `prod_mem_prod' _ 𝔞 _ fun j => hM j _`. Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h` into its components or cases. Rewrite using `[h, one_smul]`.

Conclude with `hp`. Rewrite using `[h, Units.neg_smul, one_smul]`. Conclude with `Submodule.neg_mem _ hp`.
-/
theorem det_mem_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (𝔞 : ι → FractionalIdeal (nonZeroDivisors R) K)
    (M : Matrix ι ι K) (hM : ∀ i k, M i k ∈ 𝔞 i) : M.det ∈ ∏ i, 𝔞 i := by
  rw [Matrix.det_apply]
  refine Submodule.sum_mem _ fun σ _ => ?_
  have hp : ∏ i, M (σ i) i ∈ ∏ i, 𝔞 i := by
    have : ∏ i, M (σ i) i = ∏ j, M j (σ.symm j) := by
      rw [← Equiv.prod_comp σ (fun j => M j (σ.symm j))]
      simp
    rw [this]
    exact prod_mem_prod' _ 𝔞 _ fun j => hM j _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul]; exact Submodule.neg_mem _ hp

end Dedekind

end PI.UnitaryGroupMassFormula.CntFormula.R6
