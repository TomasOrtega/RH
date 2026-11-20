import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ActSingleNeZero
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivedModuleCoefficientsAndStableFlowsStatement

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.Jet.KType

/- English proof (translation)
Take `⟨c, hc, hs⟩` from `h`. Use `⟨fun i j => c i j + (if j = b then if i = a then 1 else 0 else 0), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Distinguish the cases in `h0 : c i j = 0`. Distinguish the cases in `hj : j = b`.

Distinguish the cases in `hi : i = a`. Substitute `hi` using the available equality. Substitute `hj` using the available equality. Conclude with `⟨hab, he⟩`. Simplify using `[h0, hi] at hij`.

Simplify using `[h0, hj] at hij`. Conclude with `hc i j h0`. Establish `: μ - (ν - Formalism.REAL.root a b) = (μ - ν) + Formalism.REAL.root a b` using `by abel`. Rewrite using `[this, hs]`. Simplify using `only [Nat.cast_add, add_smul, Finset.sum_add_distrib, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
theorem cdom_step {n : ℕ} {ε : Fin n → Bool} {ν μ : Fin n → ℝ} (h : CDom ε ν μ) {a b : Fin n}
    (hab : a < b) (he : ε a = ε b) : CDom ε (ν - Formalism.REAL.root a b) μ := by
  obtain ⟨c, hc, hs⟩ := h
  refine ⟨fun i j => c i j + (if j = b then if i = a then 1 else 0 else 0), ?_, ?_⟩
  · intro i j hij
    by_cases h0 : c i j = 0
    · by_cases hj : j = b
      · by_cases hi : i = a
        · subst hi; subst hj; exact ⟨hab, he⟩
        · simp [h0, hi] at hij
      · simp [h0, hj] at hij
    · exact hc i j h0
  · have : μ - (ν - Formalism.REAL.root a b) = (μ - ν) + Formalism.REAL.root a b := by abel
    rw [this, hs]
    simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, Nat.cast_ite, Nat.cast_one,
      Nat.cast_zero, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => exact ⟨fun _ _ => 0, by simp, by simp [wordWeightShift]⟩`. Consider the case `cons p w ih`. Establish `hp` using `hw p List.mem_cons_self`. Use `cdom_step (ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))) hp.2 hp.1.symm` as an intermediate fact.

Establish `e : μ + wordWeightShift (p :: w) = μ + wordWeightShift w - Formalism.REAL.root p.2 p.1`. Simplify using `only [wordWeightShift, Formalism.REAL.root]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `this`.
-/
theorem cdom_word {n : ℕ} {ε : Fin n → Bool} (μ : Fin n → ℝ) (w : List (Fin n × Fin n))
    (hw : ∀ p ∈ w, ε p.1 = ε p.2 ∧ p.2 < p.1) : CDom ε (μ + wordWeightShift w) μ := by
  induction w with
  | nil => exact ⟨fun _ _ => 0, by simp, by simp [wordWeightShift]⟩
  | cons p w ih =>
    have hp := hw p List.mem_cons_self
    have := cdom_step (ih (fun q hq => hw q (List.mem_cons_of_mem _ hq))) hp.2 hp.1.symm
    have e : μ + wordWeightShift (p :: w) = μ + wordWeightShift w - Formalism.REAL.root p.2 p.1 := by
      simp only [wordWeightShift, Formalism.REAL.root]; abel
    rw [e]; exact this

/- English proof (translation)
Introduce and unpack `⟨c, hc, hs⟩`. Establish `e : μ - (μ + Pi.single a 1 - Pi.single b 1) = Pi.single b (1 : ℝ) - Pi.single a 1` using `by abel`. Rewrite `hs` using `[e]`. Establish `h1` using `congrArg heightFunctional hs`. Rewrite `h1` using `[height_functional_root]`.

Establish `hsum : heightFunctional (∑ i, ∑ j, (c i j : ℝ) • Formalism.REAL.root i j) ≤ 0`. Use `Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_` and prove the remaining obligations. Introduce `x y hx hy`. Rewrite using `[height_functional_add]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `i _`. Use `Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_` and prove the remaining obligations. Introduce `x y hx hy`. Rewrite using `[height_functional_add]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `j _`. Establish `h2 : heightFunctional ((c i j : ℝ) • Formalism.REAL.root i j) = (c i j : ℝ) * ((i : ℝ) - j)`. Rewrite using `[← height_functional_root i j]`. Simplify using `only [heightFunctional, Formalism.REAL.root, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun k _ => by ring)`.

Rewrite using `[h2]`. Distinguish the cases in `h0 : c i j = 0`. Simplify using `[h0]`. Establish `: ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ)` using `by exact_mod_cast (hc i j h0).1`. Conclude with `mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)`.

Establish `: ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem not_cdom_add {n : ℕ} {ε : Fin n → Bool} (μ : Fin n → ℝ) {a b : Fin n} (hab : a < b) :
    ¬ CDom ε (μ + Pi.single a 1 - Pi.single b 1) μ := by
  rintro ⟨c, hc, hs⟩
  have e : μ - (μ + Pi.single a 1 - Pi.single b 1) = Pi.single b (1 : ℝ) - Pi.single a 1 := by abel
  rw [e] at hs
  have h1 := congrArg heightFunctional hs
  rw [height_functional_root] at h1
  have hsum : heightFunctional (∑ i, ∑ j, (c i j : ℝ) • Formalism.REAL.root i j) ≤ 0 := by
    refine Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_
    · intro x y hx hy; rw [height_functional_add]; linarith
    · intro i _
      refine Finset.sum_induction _ (fun v => heightFunctional v ≤ 0) ?_ (by simp [heightFunctional]) ?_
      · intro x y hx hy; rw [height_functional_add]; linarith
      · intro j _
        have h2 : heightFunctional ((c i j : ℝ) • Formalism.REAL.root i j) = (c i j : ℝ) * ((i : ℝ) - j) := by
          rw [← height_functional_root i j]
          simp only [heightFunctional, Formalism.REAL.root, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl (fun k _ => by ring)
        rw [h2]
        by_cases h0 : c i j = 0
        · simp [h0]
        · have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast (hc i j h0).1
          exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Rewrite `hy` using `[compact_span_eq_lowering hR hx]`. Establish `: lowSpan ε F x ≤ (ℂ ∙ y)ᗮ`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `u ⟨w, hw', rfl⟩`.

Rewrite using `[SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]`. Use `compact_weight_orthogonal V n ε F ν (μ + wordWeightShift w) y _ hU hw (word_action_weight hR hx.1 w (fun q hq => (hw' q hq).1)) ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hn (cdom_word μ w hw')`. Conclude with `hy0 (inner_self_eq_zero.mp (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (this hy)))`.
-/
theorem cdom_of_mem {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ} {ε : Fin n → Bool}
    {F : Fin n → Fin n → Module.End ℂ V} (hR : KRel ε F) (hU : KUnit ε F) {μ ν : Fin n → ℝ} {x y : V}
    (hx : KHighest ε F μ x) (hy : y ∈ kSpan ε F x) (hy0 : y ≠ 0) (hw : IsWeight F ν y) :
    CDom ε ν μ := by
  by_contra hn
  rw [compact_span_eq_lowering hR hx] at hy
  have : lowSpan ε F x ≤ (ℂ ∙ y)ᗮ := by
    refine Submodule.span_le.mpr ?_
    rintro u ⟨w, hw', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    refine compact_weight_orthogonal V n ε F ν (μ + wordWeightShift w) y _ hU hw
      (word_action_weight hR hx.1 w (fun q hq => (hw' q hq).1)) ?_
    rintro rfl
    exact hn (cdom_word μ w hw')
  exact hy0 (inner_self_eq_zero.mp (Submodule.mem_orthogonal_singleton_iff_inner_right.mp (this hy)))

/- English proof (translation)
Introduce `n ε H _ _ _ σ V E hσ hD`. Take `⟨-, hst, hwt⟩` from `GlobalTheory.T.derivedModule_coefficients_and_stable_flows n ε H σ V E hσ hD`. Establish `hR : KRel ε E` using `glRel_kRel ε E hD.1`. Establish `hU : KUnit ε E` using `isUnitary_kUnit ε E hD.2.1`. Establish `hIrr : KIrr` using `kIrr_of highestWeightExists_holds (kHiUniq_of compact_lowering_holds compact_weight_orthogonal (kOrth_of compact_lowering_holds compact_weight_orthogonal))`.

Establish `hmc : ∀ S : Submodule ℂ H, S ≤ V → (S.comap V.subtype).map V.subtype = S`. Introduce `S hS`. Rewrite using `[Submodule.map_comap_subtype, inf_eq_right.mpr hS]`. Establish `hfd : ∀ S : Submodule ℂ H, S ≤ V → FiniteDimensional ℂ S → FiniteDimensional ℂ (S.comap V.subtype)`. Introduce `S hS _`.

Conclude with `(Submodule.comapSubtypeEquivOfLe hS).symm.finiteDimensional`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `μ u hu0 hu hf`. Establish `hfm : FiniteDimensional ℂ ((kSpan ε E u).map V.subtype)` using `inferInstance`. Use `⟨hfm, (hst _ hf).1 (compact_span_stable u), ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `S' hS' hK`. Establish `hV : S' ≤ V` using `hS'.trans (Submodule.map_subtype_le V _)`. Establish `hf' : FiniteDimensional ℂ S'` using `Submodule.finiteDimensional_of_le hS'`. Establish `hk : KStable ε E (S'.comap V.subtype)` using `(hst _ (hfd S' hV hf')).2 (by rw [hmc S' hV]; exact hK)`. Establish `hle : S'.comap V.subtype ≤ kSpan ε E u`.

Use `Submodule.comap_mono (f := V.subtype) hS'` as an intermediate fact. Rewrite `this` using `[Submodule.comap_map_eq_of_injective V.injective_subtype]`. Then use the resulting hypothesis. Break down `hIrr V n ε E μ u hf hR hU hu _ hle hk with h | h` into its components or cases. Use `left`. Rewrite using `[← hmc S' hV, h, Submodule.map_bot]`.

Use `right`. Rewrite using `[← hmc S' hV, h]`. Conclude with `⟨u, ⟨u, mem_compact_span_self u, rfl⟩, fun h => hu0 (Subtype.ext h), (hwt μ u).1 hu.1⟩`. Introduce and unpack `ν _ ⟨y, hy, rfl⟩ hy0 hw`. Conclude with `cdom_of_mem hR hU hu hy (fun h => hy0 (by rw [h]; rfl)) ((hwt ν y).2 hw)`.

Introduce and unpack `μ S u ⟨hf, hK, hI, -, hC⟩ hV huS hu0 hw`. Establish `hw' : IsWeight E μ u` using `(hwt μ u).2 hw`. Establish `hfc` using `hfd S hV hf`. Establish `hk : KStable ε E (S.comap V.subtype)` using `(hst _ hfc).2 (by rw [hmc S hV]; exact hK)`. Establish `hle : kSpan ε E u ≤ S.comap V.subtype` using `compact_span_le_stable huS hk`.

Establish `hfk : FiniteDimensional ℂ (kSpan ε E u)` using `Submodule.finiteDimensional_of_le hle`. Use `⟨⟨hw', ?_⟩, ?_, hfk⟩` and prove the remaining obligations. Introduce `a b hab he`. Assume the negation of the conclusion as `hne`. Conclude with `not_cdom_add μ hab (hC _ (E a b u : V) (hk a b he u huS) (fun h => hne (Subtype.ext h)) ((hwt _ _).1 (compact_weight_shift hR hw' he)))`.

Break down `hI _ (Submodule.map_le_iff_le_comap.mpr hle) ((hst _ hfk).1 (compact_span_stable u)) with h | h` into its components or cases. It suffices to derive a contradiction. Establish `: (u : H) ∈ (kSpan ε E u).map V.subtype` using `⟨u, mem_compact_span_self u, rfl⟩`. Rewrite `this` using `[h, Submodule.mem_bot]`. Conclude with `hu0 (Subtype.ext this)`.

Conclude with `h`.
-/
theorem kType_iff : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V), IsURepOn (UJset ε) σ → IsDer ε σ V E → (∀ (μ : Fin n → ℝ) (u : V), u ≠ 0 → KHighest ε E μ u → FiniteDimensional ℂ (kSpan ε E u) → IsKTypeOf ε σ μ ((kSpan ε E u).map V.subtype)) ∧ ∀ (μ : Fin n → ℝ) (S : Submodule ℂ H) (u : V), IsKTypeOf ε σ μ S → S ≤ V → (u : H) ∈ S → u ≠ 0 → IsWtOn (Kset ε) σ μ (u : H) → KHighest ε E μ u ∧ (kSpan ε E u).map V.subtype = S ∧ FiniteDimensional ℂ (kSpan ε E u) := by
  intro n ε H _ _ _ σ V E hσ hD
  obtain ⟨-, hst, hwt⟩ := GlobalTheory.T.derivedModule_coefficients_and_stable_flows n ε H σ V E hσ hD
  have hR : KRel ε E := glRel_kRel ε E hD.1
  have hU : KUnit ε E := isUnitary_kUnit ε E hD.2.1
  have hIrr : KIrr := kIrr_of highestWeightExists_holds
    (kHiUniq_of compact_lowering_holds compact_weight_orthogonal (kOrth_of compact_lowering_holds compact_weight_orthogonal))
  have hmc : ∀ S : Submodule ℂ H, S ≤ V → (S.comap V.subtype).map V.subtype = S := by
    intro S hS
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hS]
  have hfd : ∀ S : Submodule ℂ H, S ≤ V → FiniteDimensional ℂ S →
      FiniteDimensional ℂ (S.comap V.subtype) := by
    intro S hS _
    exact (Submodule.comapSubtypeEquivOfLe hS).symm.finiteDimensional
  refine ⟨?_, ?_⟩
  · intro μ u hu0 hu hf
    have hfm : FiniteDimensional ℂ ((kSpan ε E u).map V.subtype) := inferInstance
    refine ⟨hfm, (hst _ hf).1 (compact_span_stable u), ?_, ?_, ?_⟩
    · intro S' hS' hK
      have hV : S' ≤ V := hS'.trans (Submodule.map_subtype_le V _)
      have hf' : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
      have hk : KStable ε E (S'.comap V.subtype) :=
        (hst _ (hfd S' hV hf')).2 (by rw [hmc S' hV]; exact hK)
      have hle : S'.comap V.subtype ≤ kSpan ε E u := by
        have := Submodule.comap_mono (f := V.subtype) hS'
        rwa [Submodule.comap_map_eq_of_injective V.injective_subtype] at this
      rcases hIrr V n ε E μ u hf hR hU hu _ hle hk with h | h
      · left; rw [← hmc S' hV, h, Submodule.map_bot]
      · right; rw [← hmc S' hV, h]
    · exact ⟨u, ⟨u, mem_compact_span_self u, rfl⟩, fun h => hu0 (Subtype.ext h), (hwt μ u).1 hu.1⟩
    · rintro ν _ ⟨y, hy, rfl⟩ hy0 hw
      exact cdom_of_mem hR hU hu hy (fun h => hy0 (by rw [h]; rfl)) ((hwt ν y).2 hw)
  · rintro μ S u ⟨hf, hK, hI, -, hC⟩ hV huS hu0 hw
    have hw' : IsWeight E μ u := (hwt μ u).2 hw
    have hfc := hfd S hV hf
    have hk : KStable ε E (S.comap V.subtype) := (hst _ hfc).2 (by rw [hmc S hV]; exact hK)
    have hle : kSpan ε E u ≤ S.comap V.subtype := compact_span_le_stable huS hk
    have hfk : FiniteDimensional ℂ (kSpan ε E u) := Submodule.finiteDimensional_of_le hle
    refine ⟨⟨hw', ?_⟩, ?_, hfk⟩
    · intro a b hab he
      by_contra hne
      exact not_cdom_add μ hab (hC _ (E a b u : V) (hk a b he u huS) (fun h => hne (Subtype.ext h))
        ((hwt _ _).1 (compact_weight_shift hR hw' he)))
    · rcases hI _ (Submodule.map_le_iff_le_comap.mpr hle) ((hst _ hfk).1 (compact_span_stable u)) with h | h
      · exfalso
        have : (u : H) ∈ (kSpan ε E u).map V.subtype := ⟨u, mem_compact_span_self u, rfl⟩
        rw [h, Submodule.mem_bot] at this
        exact hu0 (Subtype.ext this)
      · exact h

end GlobalTheory.Jet.KType
