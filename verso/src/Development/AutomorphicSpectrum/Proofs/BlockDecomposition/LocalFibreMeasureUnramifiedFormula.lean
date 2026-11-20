import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EMatMulNegCol
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FibreMassEq
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree.FibMass

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hCM.2.2.2 τ, hCM.2.2.2 τ]`. Simplify using the standard rewrite rules.
-/
theorem sig_inv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hCM.2.2.2 τ, hCM.2.2.2 τ]
  simp

/- English proof (translation)
Introduce `a c`. Establish `hi : ∀ y : E, sigR R σ (inclR R y) = inclR R (σ y)` using `fun y => by simp [sigR, inclR]`. Express the relevant statement in the definitionally equal form `sigR R σ (hR R σ J (X c) (X a)) = hR R σ J (X a) (X c)`. Simplify using `only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R σ hs, hi, hJ]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_mem {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} (R : Type) [CommRing R]
    [Algebra F R] (hs : ∀ x, σ (σ x) = x) {M n : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X ∈ HermR R σ n := by
  intro a c
  have hi : ∀ y : E, sigR R σ (inclR R y) = inclR R (σ y) := fun y => by simp [sigR, inclR]
  change sigR R σ (hR R σ J (X c) (X a)) = hR R σ J (X a) (X c)
  simp only [hR, hform, JR, map_sum, map_mul, Matrix.map_apply, sigR_sigR R σ hs, hi, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end GlobalTheory.CompanionTheory.AvgFree.FibMass

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ d b v lv hlv M J hJ n mv hmv Tt hTc hTo hTf`. Take `⟨r1, r2, r3, r4, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI := r1`. Use `haveI := r2`. Use `haveI := r3`.

Use `haveI := r4`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Take `⟨a1, a2, a3, a4, -, -, -, a8, -, a10⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)`. Use `haveI := a1`. Use `haveI := a2`.

Use `haveI := a3`. Use `haveI := a4`. Use `haveI := a8 n M`. Use `haveI hBH : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩`. Take `⟨h1, h2, h3⟩` from `hmv`.

Establish `hinv : ∀ e, σ (σ e) = e` using `GlobalTheory.CompanionTheory.AvgFree.FibMass.sig_inv hσ`. Establish `hgc : Continuous (gramR (Fv F v) σ J : (Fin n → Fin M → Fv F v ⊗[F] E) → _)` using `a10 n M J`. Set `q : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n` to `fun X => ⟨gramR (Fv F v) σ J X, GlobalTheory.CompanionTheory.AvgFree.FibMass.gram_mem (Fv F v) hinv hJ.1 X⟩`. Establish `hqc : Continuous q` using `hgc.subtype_mk _`. Establish `hTm : MeasurableSet Tt` using `hTo.measurableSet`.

Establish `hae : ∀ y, ∀ᵐ x ∂(mv y), q x = y` using `fun y => by`. Use `measure_mono_null ?_ (h1 y)` and prove the remaining obligations. Introduce `x hx hx'`. Conclude with `hx (Subtype.ext hx'.1)`. Set `φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ` to `Tt.indicator fun _ => 1`.

Establish `hφc : Continuous φ`. Use `continuous_indicator ?_ continuous_const.continuousOn` and prove the remaining obligations. Simplify using `[hTo.frontier_eq, hTc.isClosed.closure_eq]`. Establish `hφs : HasCompactSupport φ` using `HasCompactSupport.intro hTc fun x hx => Set.indicator_of_notMem hx _`. Establish `hφt : tsupport φ ⊆ {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X}`.

Use `subset_trans (closure_minimal ?_ hTc.isClosed) hTf` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `h`. Conclude with `hx (Set.indicator_of_notMem h _)`. Take `⟨hI, hC⟩` from `h3 φ hφc hφs hφt`.

Establish `hint : ∀ y, ∫ X, φ X ∂(mv y) = (mv y Tt).toReal` using `fun y => by`. Simplify using `[φ, integral_indicator hTm, Measure.real]`. Establish `hfin : ∀ y, mv y Tt ≠ ⊤` using `fun y => by`. Establish `h` using `hI y (Set.mem_univ y)`. Rewrite `h` using `[integrable_indicator_iff hTm]`.

Break down `(integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h` into its components or cases. Simplify using `at h`. Conclude with `h.ne`. Establish `hcont : Continuous fun y => (mv y Tt).toReal`. Establish `h` using `continuousOn_univ.1 hC`.

Simplify `h` using `only [hint]`. Use `⟨fun Y hY => ?_, hcont, hfin, ?_⟩` and prove the remaining obligations. Establish `hG : gramIn (Fv F v) σ J Y = q ⁻¹' Y`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, e⟩`. Establish `: q X = y` using `Subtype.ext e`. Use `show q X ∈ Y`. Rewrite using `[this]` and apply the resulting hypothesis. Introduce `hX`.

Conclude with `⟨q X, hX, rfl⟩`. Rewrite using `[hG]`. Establish `hqY : MeasurableSet (q ⁻¹' Y)` using `hqc.measurable hY`. Establish `hT : MeasurableSet (Tt ∩ q ⁻¹' Y)` using `hTm.inter hqY`. Establish `e` using `h2 ((Tt ∩ q ⁻¹' Y).indicator 1) (measurable_one.indicator hT)`.

Rewrite `e` using `[lintegral_indicator_one hT, Measure.restrict_apply hT, Set.inter_eq_left.2 (Set.inter_subset_left.trans hTf)]`. Rewrite using `[e, ← lintegral_indicator hY]`. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Rewrite using `[lintegral_indicator_one hT]`. Distinguish the cases in `hy : y ∈ Y`.

Rewrite using `[Set.indicator_of_mem hy]`. Use `measure_congr ?_` and prove the remaining obligations. Use `filter_upwards [hae y] with x hx`. Use `propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩` and prove the remaining obligations. Use `show q x ∈ Y`.

Rewrite using `[hx]` and apply the resulting hypothesis. Rewrite using `[Set.indicator_of_notMem hy]`. Use `measure_mono_null (t := {x | ¬ q x = y}) ?_ (hae y)` and prove the remaining obligations. Introduce `x hx hxy`. Apply `hy` to reduce the goal to its premises.

Rewrite using `[← hxy]`. Conclude with `hx.2`. Take `⟨C, hC'⟩` from `(hTc.image hqc).exists_bound_of_continuousOn hcont.continuousOn`. Use `⟨Real.toNNReal C, fun y => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ q '' Tt`.

Establish `h` using `hC' y hy`. Rewrite `h` using `[Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]`. Use `show mv y Tt ≤ ENNReal.ofReal C`. Conclude with `(ENNReal.le_ofReal_iff_toReal_le (hfin y) (ENNReal.toReal_nonneg.trans h)).2 h`. Establish `h0 : mv y Tt = 0`.

Use `measure_mono_null ?_ (h1 y)` and prove the remaining obligations. Introduce `x hx hx'`. Conclude with `hy ⟨x, hx, Subtype.ext hx'.1⟩`. Rewrite using `[h0]`. Conclude with `bot_le`.
-/
theorem GlobalTheory.CompanionTheory.AvgFree.free_fibre_masses : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ Tt : Set (Fin n → Fin M → (Fv F v ⊗[F] E)), IsCompact Tt → IsOpen Tt → Tt ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} → (∀ Y : Set (HermR (Fv F v) σ n), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (Tt ∩ gramIn (Fv F v) σ J Y) = ∫⁻ y in Y, mv y Tt ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n)) ∧ Continuous (fun y => (mv y Tt).toReal) ∧ (∀ y, mv y Tt ≠ ⊤) ∧ ∃ C : ℝ≥0, ∀ y, mv y Tt ≤ C := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv M J hJ n mv hmv Tt hTc hTo hTf
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, -, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI hBH : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  obtain ⟨h1, h2, h3⟩ := hmv
  have hinv : ∀ e, σ (σ e) = e := GlobalTheory.CompanionTheory.AvgFree.FibMass.sig_inv hσ
  have hgc : Continuous (gramR (Fv F v) σ J : (Fin n → Fin M → Fv F v ⊗[F] E) → _) := a10 n M J

  let q : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n := fun X =>
    ⟨gramR (Fv F v) σ J X, GlobalTheory.CompanionTheory.AvgFree.FibMass.gram_mem (Fv F v) hinv hJ.1 X⟩
  have hqc : Continuous q := hgc.subtype_mk _
  have hTm : MeasurableSet Tt := hTo.measurableSet

  have hae : ∀ y, ∀ᵐ x ∂(mv y), q x = y := fun y => by
    refine measure_mono_null ?_ (h1 y)
    intro x hx hx'
    exact hx (Subtype.ext hx'.1)

  let φ : (Fin n → Fin M → Fv F v ⊗[F] E) → ℝ := Tt.indicator fun _ => 1
  have hφc : Continuous φ := by
    refine continuous_indicator ?_ continuous_const.continuousOn
    simp [hTo.frontier_eq, hTc.isClosed.closure_eq]
  have hφs : HasCompactSupport φ :=
    HasCompactSupport.intro hTc fun x hx => Set.indicator_of_notMem hx _
  have hφt : tsupport φ ⊆ {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := by
    refine subset_trans (closure_minimal ?_ hTc.isClosed) hTf
    intro x hx
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  obtain ⟨hI, hC⟩ := h3 φ hφc hφs hφt
  have hint : ∀ y, ∫ X, φ X ∂(mv y) = (mv y Tt).toReal := fun y => by
    simp [φ, integral_indicator hTm, Measure.real]
  have hfin : ∀ y, mv y Tt ≠ ⊤ := fun y => by
    have h := hI y (Set.mem_univ y)
    rw [integrable_indicator_iff hTm] at h
    rcases (integrableOn_const_iff (C := (1 : ℝ)) (by simp)).1 h with h | h
    · simp at h
    · exact h.ne
  have hcont : Continuous fun y => (mv y Tt).toReal := by
    have h := continuousOn_univ.1 hC
    simpa only [hint] using h
  refine ⟨fun Y hY => ?_, hcont, hfin, ?_⟩
  · have hG : gramIn (Fv F v) σ J Y = q ⁻¹' Y := by
      ext X
      constructor
      · rintro ⟨y, hy, e⟩
        have : q X = y := Subtype.ext e
        show q X ∈ Y
        rwa [this]
      · intro hX
        exact ⟨q X, hX, rfl⟩
    rw [hG]
    have hqY : MeasurableSet (q ⁻¹' Y) := hqc.measurable hY
    have hT : MeasurableSet (Tt ∩ q ⁻¹' Y) := hTm.inter hqY
    have e := h2 ((Tt ∩ q ⁻¹' Y).indicator 1) (measurable_one.indicator hT)
    rw [lintegral_indicator_one hT, Measure.restrict_apply hT,
      Set.inter_eq_left.2 (Set.inter_subset_left.trans hTf)] at e
    rw [e, ← lintegral_indicator hY]
    refine lintegral_congr fun y => ?_
    rw [lintegral_indicator_one hT]
    by_cases hy : y ∈ Y
    · rw [Set.indicator_of_mem hy]
      refine measure_congr ?_
      filter_upwards [hae y] with x hx
      refine propext ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      show q x ∈ Y
      rwa [hx]
    · rw [Set.indicator_of_notMem hy]
      refine measure_mono_null (t := {x | ¬ q x = y}) ?_ (hae y)
      intro x hx hxy
      apply hy
      rw [← hxy]
      exact hx.2
  · obtain ⟨C, hC'⟩ := (hTc.image hqc).exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨Real.toNNReal C, fun y => ?_⟩
    by_cases hy : y ∈ q '' Tt
    · have h := hC' y hy
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at h
      show mv y Tt ≤ ENNReal.ofReal C
      exact (ENNReal.le_ofReal_iff_toReal_le (hfin y) (ENNReal.toReal_nonneg.trans h)).2 h
    · have h0 : mv y Tt = 0 := by
        refine measure_mono_null ?_ (h1 y)
        intro x hx hx'
        exact hy ⟨x, hx, Subtype.ext hx'.1⟩
      rw [h0]
      exact bot_le
