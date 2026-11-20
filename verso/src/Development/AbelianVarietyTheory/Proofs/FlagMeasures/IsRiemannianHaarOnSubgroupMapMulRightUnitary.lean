import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeRightInv

open Topology

/- English proof (translation)
Establish `hU : (interior B).Nonempty` using `⟨1, mem_interior_iff_mem_nhds.2 hB⟩`. Establish `hmeas : Measurable (fun g : G => g * l)` using `measurable_mul_const l`. Use `haveI : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant' hU ht hK⟩`. Establish `hVo : IsOpen ((fun g : G => g * l⁻¹) ⁻¹' interior B)` using `isOpen_interior.preimage (continuous_mul_right l⁻¹)`. Establish `hV : ν.map (fun g => g * l) ((fun g : G => g * l⁻¹) ⁻¹' interior B) = ν (interior B)`.

Rewrite using `[Measure.map_apply hmeas hVo.measurableSet]`. Use `congr 1`. Use extensionality with `g`. Simplify using `[mul_assoc]`. Use `haveI : IsFiniteMeasureOnCompacts (ν.map (fun g => g * l)) := ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant _ hVo ⟨l, by simpa using mem_interior_iff_mem_nhds.2 hB⟩ (by rw [hV]; exact ((measure_mono interior_subset).trans_lt ht.lt_top).ne) hK⟩`.

Take `⟨c₁, e₁⟩ : ∃ c : NNReal, ν = c • (Measure.haar : Measure G)` from `⟨_, Measure.isMulLeftInvariant_eq_smul ν Measure.haar⟩`. Take `⟨c₂, e₂⟩ : ∃ c : NNReal, ν.map (fun g => g * l) = c • (Measure.haar : Measure G)` from `⟨_, Measure.isMulLeftInvariant_eq_smul _ Measure.haar⟩`. Establish `hBB : ν.map (fun g => g * l) B = ν B`. Rewrite using `[Measure.map_apply hmeas hBm, show (fun g => g * l) ⁻¹' B = (fun g => l * g) ⁻¹' B from Set.ext hl]`. Conclude with `measure_preimage_mul ν l B`.

Establish `hpos : (Measure.haar : Measure G) B ≠ 0` using `(Measure.measure_pos_of_mem_nhds _ hB).ne'`. Establish `hc₁ : (c₁ : ENNReal) ≠ 0`. Introduce and unpack `h`. Apply `h0` to reduce the goal to its premises. Rewrite using `[e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, zero_mul]`.

Establish `hfin : (Measure.haar : Measure G) B ≠ ⊤`. Introduce `h`. Apply `ht` to reduce the goal to its premises. Rewrite using `[e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, ENNReal.mul_top hc₁]`. Rewrite `hBB` using `[e₂, e₁, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.mul_left_inj hpos hfin]`.

Rewrite using `[e₂, e₁, ENNReal.coe_injective hBB]`.
-/
theorem map_mul_right_of_conj_nhds {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (B : Set G) (hBm : MeasurableSet B) (hB : B ∈ 𝓝 (1 : G))
    (h0 : ν B ≠ 0) (ht : ν B ≠ ⊤) (l : G) (hl : ∀ g, g * l ∈ B ↔ l * g ∈ B) :
    ν.map (fun g => g * l) = ν := by
  have hU : (interior B).Nonempty := ⟨1, mem_interior_iff_mem_nhds.2 hB⟩
  have hmeas : Measurable (fun g : G => g * l) := measurable_mul_const l
  haveI : IsFiniteMeasureOnCompacts ν :=
    ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant' hU ht hK⟩

  have hVo : IsOpen ((fun g : G => g * l⁻¹) ⁻¹' interior B) :=
    isOpen_interior.preimage (continuous_mul_right l⁻¹)
  have hV : ν.map (fun g => g * l) ((fun g : G => g * l⁻¹) ⁻¹' interior B) = ν (interior B) := by
    rw [Measure.map_apply hmeas hVo.measurableSet]
    congr 1
    ext g
    simp [mul_assoc]
  haveI : IsFiniteMeasureOnCompacts (ν.map (fun g => g * l)) :=
    ⟨fun K hK => measure_lt_top_of_isCompact_of_isMulLeftInvariant _ hVo
      ⟨l, by simpa using mem_interior_iff_mem_nhds.2 hB⟩
      (by rw [hV]; exact ((measure_mono interior_subset).trans_lt ht.lt_top).ne) hK⟩

  obtain ⟨c₁, e₁⟩ : ∃ c : NNReal, ν = c • (Measure.haar : Measure G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul ν Measure.haar⟩
  obtain ⟨c₂, e₂⟩ : ∃ c : NNReal, ν.map (fun g => g * l) = c • (Measure.haar : Measure G) :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ Measure.haar⟩

  have hBB : ν.map (fun g => g * l) B = ν B := by
    rw [Measure.map_apply hmeas hBm,
      show (fun g => g * l) ⁻¹' B = (fun g => l * g) ⁻¹' B from Set.ext hl]
    exact measure_preimage_mul ν l B
  have hpos : (Measure.haar : Measure G) B ≠ 0 := (Measure.measure_pos_of_mem_nhds _ hB).ne'
  have hc₁ : (c₁ : ENNReal) ≠ 0 := by
    rintro h
    apply h0
    rw [e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, zero_mul]
  have hfin : (Measure.haar : Measure G) B ≠ ⊤ := by
    intro h
    apply ht
    rw [e₁, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, h, ENNReal.mul_top hc₁]
  rw [e₂, e₁, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def,
    smul_eq_mul, smul_eq_mul, ENNReal.mul_left_inj hpos hfin] at hBB
  rw [e₂, e₁, ENNReal.coe_injective hBB]

/- English proof (translation)
Use `haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (M : Set G))`. Use `haveI : BorelSpace M := inferInstanceAs (BorelSpace (M : Set G))`. Establish `emb : MeasurableEmbedding (Subtype.val : M → G)` using `MeasurableEmbedding.subtype_coe hM.measurableSet`. Use `set ν : Measure M := μ.comap Subtype.val with hν`.

Establish `hμν : ν.map Subtype.val = μ`. Rewrite using `[hν, emb.map_comap, Subtype.range_coe]`. Conclude with `Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ)`. Use `haveI : ν.IsMulLeftInvariant := ⟨fun s => by`. Use extensionality with `A hA`.

Rewrite using `[Measure.map_apply (measurable_const_mul s) hA, hν, emb.comap_apply, emb.comap_apply]`. Establish `himg : Subtype.val '' ((fun x => s * x) ⁻¹' A) = (fun x : G => (s : G) * x) ⁻¹' (Subtype.val '' A)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨s * y, hy, rfl⟩`. Introduce and unpack `⟨y, hy, hyx⟩`. Establish `hx : x ∈ M`. Establish `: x = (s : G)⁻¹ * y` using `by rw [hyx, ← mul_assoc, inv_mul_cancel, one_mul]`. Rewrite using `[this]`.

Conclude with `M.mul_mem (M.inv_mem s.2) y.2`. Use `⟨⟨x, hx⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show s * (⟨x, hx⟩ : M) ∈ A`. Rewrite using `[show s * (⟨x, hx⟩ : M) = y from Subtype.ext hyx.symm]`. Conclude with `hy`.

Rewrite using `[himg, ← Measure.map_apply (measurable_const_mul (s : G)) (emb.measurableSet_image' hA), hinv s s.2]⟩`. Establish `hνB : ν (Subtype.val ⁻¹' B) = μ B` using `by conv_rhs => rw [← hμν]`. Rewrite using `[Measure.map_apply measurable_subtype_coe hBm]`. Establish `key` using `map_mul_right_of_conj_nhds ν (Subtype.val ⁻¹' B) (hBm.preimage measurable_subtype_coe) (continuous_subtype_val.continuousAt.preimage_mem_nhds hB) (by rwa [hνB]) (by rwa [hνB]) ⟨l, hlM⟩ (fun g => hl g)`. Rewrite using `[← hμν, Measure.map_map (measurable_mul_const l) measurable_subtype_coe, show (fun g : G => g * l) ∘ Subtype.val = Subtype.val ∘ (fun g : M => g * ⟨l, hlM⟩) from rfl, ← Measure.map_map measurable_subtype_coe (measurable_mul_const _), key]`.
-/
theorem map_mul_right_of_conj_nhds_subgroup {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (M : Subgroup G) (hM : IsClosed (M : Set G)) (μ : Measure G) (hμ : μ (M : Set G)ᶜ = 0)
    (hinv : ∀ s ∈ M, μ.map (fun g => s * g) = μ) (B : Set G) (hBm : MeasurableSet B) (hB : B ∈ 𝓝 (1 : G))
    (h0 : μ B ≠ 0) (ht : μ B ≠ ⊤) (l : G) (hlM : l ∈ M) (hl : ∀ g, g * l ∈ B ↔ l * g ∈ B) :
    μ.map (fun g => g * l) = μ := by
  haveI : LocallyCompactSpace M := hM.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology M := inferInstanceAs (SecondCountableTopology (M : Set G))
  haveI : BorelSpace M := inferInstanceAs (BorelSpace (M : Set G))
  have emb : MeasurableEmbedding (Subtype.val : M → G) :=
    MeasurableEmbedding.subtype_coe hM.measurableSet

  set ν : Measure M := μ.comap Subtype.val with hν
  have hμν : ν.map Subtype.val = μ := by
    rw [hν, emb.map_comap, Subtype.range_coe]
    exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ)
  haveI : ν.IsMulLeftInvariant := ⟨fun s => by
    ext A hA
    rw [Measure.map_apply (measurable_const_mul s) hA, hν, emb.comap_apply, emb.comap_apply]
    have himg : Subtype.val '' ((fun x => s * x) ⁻¹' A) =
        (fun x : G => (s : G) * x) ⁻¹' (Subtype.val '' A) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨s * y, hy, rfl⟩
      · rintro ⟨y, hy, hyx⟩
        have hx : x ∈ M := by
          have : x = (s : G)⁻¹ * y := by rw [hyx, ← mul_assoc, inv_mul_cancel, one_mul]
          rw [this]
          exact M.mul_mem (M.inv_mem s.2) y.2
        refine ⟨⟨x, hx⟩, ?_, rfl⟩
        show s * (⟨x, hx⟩ : M) ∈ A
        rw [show s * (⟨x, hx⟩ : M) = y from Subtype.ext hyx.symm]
        exact hy
    rw [himg, ← Measure.map_apply (measurable_const_mul (s : G)) (emb.measurableSet_image' hA),
      hinv s s.2]⟩
  have hνB : ν (Subtype.val ⁻¹' B) = μ B := by
    conv_rhs => rw [← hμν]
    rw [Measure.map_apply measurable_subtype_coe hBm]
  have key := map_mul_right_of_conj_nhds ν (Subtype.val ⁻¹' B)
    (hBm.preimage measurable_subtype_coe)
    (continuous_subtype_val.continuousAt.preimage_mem_nhds hB)
    (by rwa [hνB]) (by rwa [hνB]) ⟨l, hlM⟩ (fun g => hl g)
  rw [← hμν, Measure.map_map (measurable_mul_const l) measurable_subtype_coe,
    show (fun g : G => g * l) ∘ Subtype.val = Subtype.val ∘ (fun g : M => g * ⟨l, hlM⟩) from rfl,
    ← Measure.map_map measurable_subtype_coe (measurable_mul_const _), key]

/- English proof (translation)
Simplify using `only [Formalism.REAL.hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]`.
-/
theorem hs_eq_re_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Formalism.REAL.hs X = (trace (X * Xᴴ)).re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/- English proof (translation)
Rewrite using `[hs_eq_re_trace, hs_eq_re_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Lᴴ L, hL, Matrix.one_mul]`.

Use `_ = trace (Lᴴ * (L * (M * Mᴴ))) := Matrix.trace_mul_comm _ _`. Use `_ = trace (M * Mᴴ) := by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]`.
-/
private theorem hs_mul_mul_conjTranspose_of_unitary {n : ℕ} (L M : Matrix (Fin n) (Fin n) ℂ) (hL : Lᴴ * L = 1) :
    Formalism.REAL.hs (L * M * Lᴴ) = Formalism.REAL.hs M := by
  rw [hs_eq_re_trace, hs_eq_re_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  congr 1
  calc trace (L * M * Lᴴ * (L * (Mᴴ * Lᴴ))) = trace (L * (M * Mᴴ) * Lᴴ) := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Lᴴ L, hL, Matrix.one_mul]
    _ = trace (Lᴴ * (L * (M * Mᴴ))) := Matrix.trace_mul_comm _ _
    _ = trace (M * Mᴴ) := by rw [← Matrix.mul_assoc, hL, Matrix.one_mul]

/- English proof (translation)
Establish `hL' : L * Lᴴ = 1` using `mul_eq_one_comm.mp hL`. Establish `h : L * X - 1 = L * (X * L - 1) * Lᴴ`. Simplify using `only [mul_sub, sub_mul, mul_one, mul_assoc, hL']`. Rewrite using `[h, hs_mul_mul_conjTranspose_of_unitary L _ hL]`.
-/
theorem hs_conj {n : ℕ} (L X : Matrix (Fin n) (Fin n) ℂ) (hL : Lᴴ * L = 1) :
    Formalism.REAL.hs (L * X - 1) = Formalism.REAL.hs (X * L - 1) := by
  have hL' : L * Lᴴ = 1 := mul_eq_one_comm.mp hL

  have h : L * X - 1 = L * (X * L - 1) * Lᴴ := by
    simp only [mul_sub, sub_mul, mul_one, mul_assoc, hL']
  rw [h, hs_mul_mul_conjTranspose_of_unitary L _ hL]

/- English proof (translation)
Unfold `IsGaugeSub at hμ`. Take `⟨hμc, hinv, hlim⟩` from `hμ`. Establish `hlU : (uMat l)ᴴ * uMat l = 1` using `by unfold maxK at hlK; exact hlK`. Choose the witnesses or unpack the hypotheses as in `⟨r, ⟨h1, h2⟩, hr⟩ : ∃ r : ℝ, μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} / ENNReal.ofReal (r ^ d) ∈ Set.Ioo 0 ⊤ ∧ 0 < r := by`. Use `((hlim.eventually (Ioo_mem_nhds ?_ ?_)).and self_mem_nhdsWithin).exists` and prove the remaining obligations.

Conclude with `Metric.measure_ball_pos _ _ one_pos`. Conclude with `measure_ball_lt_top`. Establish `hB0 : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ 0`. Introduce `h`. Rewrite `h1` using `[h, ENNReal.zero_div]`.

Conclude with `lt_irrefl _ h1`. Establish `hBt : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤`. Introduce `h`. Rewrite `h2` using `[h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]`. Conclude with `lt_irrefl _ h2`.

Establish `hu : Continuous fun g : Formalism.REAL.UJ ε => uMat g`. Unfold `uMat`. Use `fun_prop`. Establish `hc : Continuous fun g : Formalism.REAL.UJ ε => √(Formalism.REAL.hs (uMat g - 1))`. Unfold `Formalism.REAL.hs`.

Use `fun_prop`. Establish `hBn : {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ∈ 𝓝 (1 : Formalism.REAL.UJ ε)`. Establish `h1' : √(Formalism.REAL.hs (uMat (1 : Formalism.REAL.UJ ε) - 1)) < r`. Rewrite using `[show uMat (1 : Formalism.REAL.UJ ε) = 1 from rfl, sub_self]`. Simplify using `[Formalism.REAL.hs, hr]`.

Conclude with `Filter.mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds h1') fun g hg => show √(Formalism.REAL.hs (uMat g - 1)) ≤ r from le_of_lt hg`. Establish `hcomm : ∀ g, g * l ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ↔ l * g ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r}`. Introduce `g`. Use `show √(Formalism.REAL.hs (uMat (g * l) - 1)) ≤ r ↔ √(Formalism.REAL.hs (uMat (l * g) - 1)) ≤ r`. Rewrite using `[show uMat (g * l) = uMat g * uMat l from rfl, show uMat (l * g) = uMat l * uMat g from rfl, hs_conj (uMat l) (uMat g) hlU]`.

Conclude with `map_mul_right_of_conj_nhds_subgroup M hM μ hμc hinv _ (isClosed_le hc continuous_const).measurableSet hBn hB0 hBt l hlM hcomm`.
-/
theorem isGaugeSub_map_mul_right (n : ℕ) (ε : Fin n → Bool) (M : Subgroup (Formalism.REAL.UJ ε)) (d : ℕ)
    (μ : Measure (Formalism.REAL.UJ ε)) (hM : IsClosed (M : Set (Formalism.REAL.UJ ε)))
    (hμ : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) d μ) (l : Formalism.REAL.UJ ε) (hlM : l ∈ M) (hlK : l ∈ maxK ε) :
    μ.map (fun g => g * l) = μ := by
  unfold IsGaugeSub at hμ
  obtain ⟨hμc, hinv, hlim⟩ := hμ
  have hlU : (uMat l)ᴴ * uMat l = 1 := by unfold maxK at hlK; exact hlK

  obtain ⟨r, ⟨h1, h2⟩, hr⟩ : ∃ r : ℝ,
      μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} / ENNReal.ofReal (r ^ d) ∈ Set.Ioo 0 ⊤ ∧ 0 < r := by
    refine ((hlim.eventually (Ioo_mem_nhds ?_ ?_)).and self_mem_nhdsWithin).exists
    · exact Metric.measure_ball_pos _ _ one_pos
    · exact measure_ball_lt_top
  have hB0 : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ 0 := by
    intro h
    rw [h, ENNReal.zero_div] at h1
    exact lt_irrefl _ h1
  have hBt : μ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at h2
    exact lt_irrefl _ h2
  have hu : Continuous fun g : Formalism.REAL.UJ ε => uMat g := by
    unfold uMat
    fun_prop
  have hc : Continuous fun g : Formalism.REAL.UJ ε => √(Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    fun_prop
  have hBn : {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ∈ 𝓝 (1 : Formalism.REAL.UJ ε) := by
    have h1' : √(Formalism.REAL.hs (uMat (1 : Formalism.REAL.UJ ε) - 1)) < r := by
      rw [show uMat (1 : Formalism.REAL.UJ ε) = 1 from rfl, sub_self]
      simp [Formalism.REAL.hs, hr]
    exact Filter.mem_of_superset ((isOpen_lt hc continuous_const).mem_nhds h1') fun g hg =>
      show √(Formalism.REAL.hs (uMat g - 1)) ≤ r from le_of_lt hg

  have hcomm : ∀ g, g * l ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} ↔
      l * g ∈ {g | √(Formalism.REAL.hs (uMat g - 1)) ≤ r} := by
    intro g
    show √(Formalism.REAL.hs (uMat (g * l) - 1)) ≤ r ↔ √(Formalism.REAL.hs (uMat (l * g) - 1)) ≤ r
    rw [show uMat (g * l) = uMat g * uMat l from rfl, show uMat (l * g) = uMat l * uMat g from rfl,
      hs_conj (uMat l) (uMat g) hlU]
  exact map_mul_right_of_conj_nhds_subgroup M hM μ hμc hinv _
    (isClosed_le hc continuous_const).measurableSet hBn hB0 hBt l hlM hcomm

end GlobalTheory.GaugeRightInv
