import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarMeasureOfSigmaFinite
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotExist

/- English proof (translation)
Set `K : ℕ → Set G` to `compactCovering G`. Establish `hK : ∀ n, IsCompact (K n)` using `isCompact_compactCovering G`. Establish `hKm : ∀ n, MeasurableSet (K n)` using `fun n => (hK n).isClosed.measurableSet`. Set `φ : ℕ → G → ℝ≥0∞` to `fun n => (K n).indicator 1`. Establish `hφ : ∀ n, Measurable (φ n)` using `fun n => measurable_one.indicator (hKm n)`.

Establish `hjm : Measurable j` using `hj.continuous.measurable`. Set `F : ℕ → G → ℝ≥0∞` to `fun n g => ∫⁻ h, φ n ((j h)⁻¹ * g) ∂ν`. Establish `hFm : ∀ n, Measurable (F n)`. Introduce `n`. Establish `: Measurable (fun p : G × H => φ n ((j p.2)⁻¹ * p.1))` using `(hφ n).comp ((hjm.comp measurable_snd).inv.mul measurable_fst)`.

Conclude with `this.lintegral_prod_right'`. Establish `key : ∀ n k g, F n ((j k)⁻¹ * g) = F n g`. Introduce `n k g`. Use `lintegral_mul_left_eq_self (μ := ν) (fun h => φ n ((j h)⁻¹ * g)) k` as an intermediate fact. Simplify `this` using `only [F, map_mul, _root_.mul_inv_rev, mul_assoc]`.

Establish `hpre : ∀ n g, MeasurableSet ((fun h => (j h)⁻¹ * g) ⁻¹' K n)` using `fun n g => (hjm.inv.mul_const g) (hKm n)`. Establish `hFeq : ∀ n g, F n g = ν ((fun h => (j h)⁻¹ * g) ⁻¹' K n)`. Introduce `n g`. Rewrite using `[← lintegral_indicator_one (hpre n g)]`. Both sides reduce to the same expression.

Establish `hFfin : ∀ n g, F n g ≠ ⊤`. Introduce `n g`. Rewrite using `[hFeq]`. Establish `hc : Topology.IsClosedEmbedding (fun h => (j h)⁻¹ * g)` using `(Homeomorph.mulRight g).isClosedEmbedding.comp ((Homeomorph.inv G).isClosedEmbedding.comp hj)`. Conclude with `(hc.isCompact_preimage (hK n)).measure_lt_top.ne`.

Establish `hFpos : ∀ g, ∃ n, F n g ≠ 0`. Introduce `g`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h0 : ν (⋃ n, (fun h => (j h)⁻¹ * g) ⁻¹' K n) = 0` using `measure_iUnion_null fun n => by rw [← hFeq]; exact hcon n`.

Rewrite `h0` using `[← Set.preimage_iUnion, iUnion_compactCovering, Set.preimage_univ]`. Conclude with `hν (Measure.measure_univ_eq_zero.1 h0)`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN, hNinv, hNm⟩ : ∃ N : G → ℕ, (∀ g, F (N g) g ≠ 0) ∧ (∀ k g, N ((j k)⁻¹ * g) = N g) ∧ Measurable (fun g => φ (N g) g * (F (N g) g)⁻¹) := by`. Use `⟨fun g => Nat.find (hFpos g), fun g => Nat.find_spec (hFpos g), ?_, ?_⟩` and prove the remaining obligations. Introduce `k g`.

Apply `Nat.find_congr'` to reduce the goal to its premises. Introduce `n`. Rewrite using `[key]`. Use `Measurable.find (p := fun n g => F n g ≠ 0) (f := fun n g => φ n g * (F n g)⁻¹) (fun n => (hφ n).mul (hFm n).inv) (fun n => ((hFm n) (measurableSet_singleton 0)).compl) hFpos using 4` and compare the differences between its conclusion and the goal. Use `⟨fun g => φ (N g) g * (F (N g) g)⁻¹, hNm, fun g => ?_⟩` and prove the remaining obligations.

Simplify using `only [hNinv, key]`. Establish `hm : Measurable fun h => φ (N g) ((j h)⁻¹ * g)` using `(hφ _).comp (hjm.inv.mul_const g)`. Rewrite using `[lintegral_mul_const _ hm]`. Conclude with `ENNReal.mul_inv_cancel (hN g) (hFfin _ g)`.
-/
theorem bruhat_left (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (ν : Measure H)
    [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν] (hν : ν ≠ 0) (j : H →* G)
    (hj : Topology.IsClosedEmbedding j) :
    ∃ b : G → ℝ≥0∞, Measurable b ∧ ∀ g, ∫⁻ h, b ((j h)⁻¹ * g) ∂ν = 1 := by
  classical
  let K : ℕ → Set G := compactCovering G
  have hK : ∀ n, IsCompact (K n) := isCompact_compactCovering G
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (hK n).isClosed.measurableSet
  let φ : ℕ → G → ℝ≥0∞ := fun n => (K n).indicator 1
  have hφ : ∀ n, Measurable (φ n) := fun n => measurable_one.indicator (hKm n)
  have hjm : Measurable j := hj.continuous.measurable
  let F : ℕ → G → ℝ≥0∞ := fun n g => ∫⁻ h, φ n ((j h)⁻¹ * g) ∂ν
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    have : Measurable (fun p : G × H => φ n ((j p.2)⁻¹ * p.1)) :=
      (hφ n).comp ((hjm.comp measurable_snd).inv.mul measurable_fst)
    exact this.lintegral_prod_right'
  have key : ∀ n k g, F n ((j k)⁻¹ * g) = F n g := by
    intro n k g
    have := lintegral_mul_left_eq_self (μ := ν) (fun h => φ n ((j h)⁻¹ * g)) k
    simpa only [F, map_mul, _root_.mul_inv_rev, mul_assoc] using this
  have hpre : ∀ n g, MeasurableSet ((fun h => (j h)⁻¹ * g) ⁻¹' K n) := fun n g =>
    (hjm.inv.mul_const g) (hKm n)
  have hFeq : ∀ n g, F n g = ν ((fun h => (j h)⁻¹ * g) ⁻¹' K n) := by
    intro n g
    rw [← lintegral_indicator_one (hpre n g)]
    rfl
  have hFfin : ∀ n g, F n g ≠ ⊤ := by
    intro n g
    rw [hFeq]
    have hc : Topology.IsClosedEmbedding (fun h => (j h)⁻¹ * g) :=
      (Homeomorph.mulRight g).isClosedEmbedding.comp ((Homeomorph.inv G).isClosedEmbedding.comp hj)
    exact (hc.isCompact_preimage (hK n)).measure_lt_top.ne
  have hFpos : ∀ g, ∃ n, F n g ≠ 0 := by
    intro g
    by_contra hcon
    push Not at hcon
    have h0 : ν (⋃ n, (fun h => (j h)⁻¹ * g) ⁻¹' K n) = 0 :=
      measure_iUnion_null fun n => by rw [← hFeq]; exact hcon n
    rw [← Set.preimage_iUnion, iUnion_compactCovering, Set.preimage_univ] at h0
    exact hν (Measure.measure_univ_eq_zero.1 h0)
  obtain ⟨N, hN, hNinv, hNm⟩ : ∃ N : G → ℕ, (∀ g, F (N g) g ≠ 0) ∧ (∀ k g, N ((j k)⁻¹ * g) = N g) ∧
      Measurable (fun g => φ (N g) g * (F (N g) g)⁻¹) := by
    refine ⟨fun g => Nat.find (hFpos g), fun g => Nat.find_spec (hFpos g), ?_, ?_⟩
    · intro k g
      apply Nat.find_congr'
      intro n
      rw [key]
    · convert Measurable.find (p := fun n g => F n g ≠ 0) (f := fun n g => φ n g * (F n g)⁻¹)
        (fun n => (hφ n).mul (hFm n).inv)
        (fun n => ((hFm n) (measurableSet_singleton 0)).compl) hFpos using 4
  refine ⟨fun g => φ (N g) g * (F (N g) g)⁻¹, hNm, fun g => ?_⟩
  simp only [hNinv, key]
  have hm : Measurable fun h => φ (N g) ((j h)⁻¹ * g) := (hφ _).comp (hjm.inv.mul_const g)
  rw [lintegral_mul_const _ hm]
  exact ENNReal.mul_inv_cancel (hN g) (hFfin _ g)

/- English proof (translation)
Establish `hce : Topology.IsClosedEmbedding R.subtype` using `hR.isClosedEmbedding_subtypeVal`. Establish `hφ : MeasurableEmbedding R.subtype` using `hce.measurableEmbedding`. Use `haveI : LocallyCompactSpace R := hce.locallyCompactSpace`. Use `haveI : SecondCountableTopology R := hce.isEmbedding.secondCountableTopology`. Establish `h2 : (μ.comap R.subtype).map R.subtype = μ`.

Rewrite using `[hφ.map_comap]`. Use `Measure.restrict_eq_self_of_ae_mem ?_` and prove the remaining obligations. Establish `: Set.range R.subtype = (R : Set G)` using `Subtype.range_coe`. Rewrite using `[this]`. Conclude with `hc`.

Use `set ν : Measure R := μ.comap R.subtype with hν`. Use `haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])`. Use `haveI : ν.IsMulLeftInvariant := ⟨fun g => by`. Apply `hφ.map_injective` to reduce the goal to its premises. Establish `hm : Measurable fun x : G => (g : G) * x` using `measurable_const_mul _`.

Rewrite using `[Measure.map_map hφ.measurable (measurable_const_mul g), h2]`. Use `conv_rhs => rw [← hi g g.2, ← h2, Measure.map_map hm hφ.measurable]`. Use the proof step `rfl⟩`. Establish `hν0 : ν ≠ 0` using `fun h => h0 (by rw [← h2, h, Measure.map_zero])`. Use `haveI : ν.IsHaarMeasure := GlobalTheory.SnMass.ProdQuot.isHaarMeasure_of_sigmaFinite ν hν0`.

Take `⟨b, hb, h1⟩` from `bruhat_left G R ν hν0 R.subtype hce`. Use `⟨b, hb, fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[← h2, hφ.lintegral_map]`. Conclude with `h1 g`.
-/
theorem cutoff_left {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (R : Subgroup G) (μ : Measure G)
    [SigmaFinite μ] (hR : IsClosed (R : Set G)) (h0 : μ ≠ 0) (hc : μ (R : Set G)ᶜ = 0)
    (hi : ∀ s ∈ R, μ.map (fun x => s * x) = μ) :
    ∃ b : G → ℝ≥0∞, Measurable b ∧ ∀ g, ∫⁻ s, b (s⁻¹ * g) ∂μ = 1 := by
  have hce : Topology.IsClosedEmbedding R.subtype := hR.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding R.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : SecondCountableTopology R := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap R.subtype).map R.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range R.subtype = (R : Set G) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure R := μ.comap R.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => (g : G) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← hi g g.2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  have hν0 : ν ≠ 0 := fun h => h0 (by rw [← h2, h, Measure.map_zero])
  haveI : ν.IsHaarMeasure := GlobalTheory.SnMass.ProdQuot.isHaarMeasure_of_sigmaFinite ν hν0
  obtain ⟨b, hb, h1⟩ := bruhat_left G R ν hν0 R.subtype hce
  refine ⟨b, hb, fun g => ?_⟩
  rw [← h2, hφ.lintegral_map]
  exact h1 g

/- English proof (translation)
Establish `hinv : Measurable (Inv.inv : G → G)` using `measurable_inv`. Establish `hf2 : Measurable fun p : G × G => f (p.2 * p.1)` using `hf.comp (measurable_snd.mul measurable_fst)`. Rewrite using `[lintegral_withDensity_eq_lintegral_mul _ hb hf2.lintegral_prod_right']`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_congr fun x => ?_` and prove the remaining obligations.

Rewrite using `[lintegral_mul_const (f := fun s => b (s⁻¹ * x)) _ (hb.comp (hinv.mul_const x)), h2, one_mul]`. Use `_ = ∫⁻ s, ∫⁻ x, b (s⁻¹ * x) * f x ∂μG ∂μ := lintegral_lintegral_swap ((hb.comp (measurable_snd.inv.mul measurable_fst)).mul (hf.comp measurable_fst)).aemeasurable`. Use `_ = ∫⁻ s, ∫⁻ x, b x * f (s * x) ∂μG ∂μ := by`. Use `lintegral_congr fun s => ?_` and prove the remaining obligations. Rewrite using `[← lintegral_mul_left_eq_self _ s]`.

Simplify using the standard rewrite rules. Use `_ = ∫⁻ x, ∫⁻ s, b x * f (s * x) ∂μ ∂μG := (lintegral_lintegral_swap ((hb.comp measurable_fst).mul hf2).aemeasurable).symm`. Use `_ = _ := by`. Use `lintegral_congr fun x => ?_` and prove the remaining obligations. Rewrite using `[lintegral_const_mul (f := fun s => f (s * x)) _ (hf.comp (measurable_mul_const x))]`.

Both sides reduce to the same expression.
-/
theorem weil_of_cutoff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μG μ : Measure G) [SigmaFinite μG] [μG.IsMulLeftInvariant] [SigmaFinite μ] {b : G → ℝ≥0∞}
    (hb : Measurable b) (h2 : ∀ g, ∫⁻ s, b (s⁻¹ * g) ∂μ = 1) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂(μG.withDensity b) := by
  have hinv : Measurable (Inv.inv : G → G) := measurable_inv
  have hf2 : Measurable fun p : G × G => f (p.2 * p.1) := hf.comp (measurable_snd.mul measurable_fst)
  rw [lintegral_withDensity_eq_lintegral_mul _ hb hf2.lintegral_prod_right']
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, b (s⁻¹ * x) * f x ∂μ ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_mul_const (f := fun s => b (s⁻¹ * x)) _ (hb.comp (hinv.mul_const x)), h2, one_mul]
    _ = ∫⁻ s, ∫⁻ x, b (s⁻¹ * x) * f x ∂μG ∂μ :=
        lintegral_lintegral_swap ((hb.comp (measurable_snd.inv.mul measurable_fst)).mul
          (hf.comp measurable_fst)).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, b x * f (s * x) ∂μG ∂μ := by
        refine lintegral_congr fun s => ?_
        rw [← lintegral_mul_left_eq_self _ s]
        simp
    _ = ∫⁻ x, ∫⁻ s, b x * f (s * x) ∂μ ∂μG :=
        (lintegral_lintegral_swap ((hb.comp measurable_fst).mul hf2).aemeasurable).symm
    _ = _ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul (f := fun s => f (s * x)) _ (hf.comp (measurable_mul_const x))]
        rfl

section Sub

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun c (hc : c.1 < a) => lt_of_lt_of_le hc h)`.
-/
theorem spanLt_mono {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b :=
  Submodule.span_mono (Set.image_mono fun c (hc : c.1 < a) => lt_of_lt_of_le hc h)

def Pres (M : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ a : ℕ, ∀ v ∈ spanLt e a, M *ᵥ v ∈ spanLt e a

/- English proof (translation)
Introduce `a v hv`. Establish `: spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin M)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨c, hc, rfl⟩`. Use `show Matrix.mulVecLin M (e c) ∈ spanLt e a`.

Rewrite using `[Matrix.mulVecLin_apply]`. Conclude with `spanLt_mono e (Nat.succ_le_of_lt hc) (h c)`. Establish `h2` using `this hv`. Rewrite `h2` using `[Submodule.mem_comap, Matrix.mulVecLin_apply]`. Conclude with `h2`.
-/
theorem pres_of (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ b : Fin r, M *ᵥ e b ∈ spanLt e (b.1 + 1)) : Pres e M := by
  intro a v hv
  have : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin M) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    show Matrix.mulVecLin M (e c) ∈ spanLt e a
    rw [Matrix.mulVecLin_apply]
    exact spanLt_mono e (Nat.succ_le_of_lt hc) (h c)
  have h2 := this hv
  rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at h2
  exact h2

def Good (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ((∀ a : Fin r, M *ᵥ e a ∈ spanLt e a.1) ∧ M *ᵥ z ∈ spanLt e r) ∧
    ∀ y, (∀ a, hJ ε (e a) y = 0) → M *ᵥ y ∈ spanLt e r

variable {ε e z}

/- English proof (translation)
The claim follows from `pres_of e M fun b => spanLt_mono e (Nat.le_succ _) (hM.1.1 b)`.
-/
theorem Good.pres {M : Matrix (Fin n) (Fin n) ℂ} (hM : Good ε e z M) : Pres e M :=
  pres_of e M fun b => spanLt_mono e (Nat.le_succ _) (hM.1.1 b)

/- English proof (translation)
Apply the tactic sequence `refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [← Matrix.mulVec_mulVec]`. Conclude with `hP _ _ (hM.1.1 a)`. Conclude with `hP _ _ hM.1.2`. Conclude with `hP _ _ (hM.2 y hy)`.
-/
theorem Good.pres_mul {P M : Matrix (Fin n) (Fin n) ℂ} (hP : Pres e P) (hM : Good ε e z M) :
    Good ε e z (P * M) := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [← Matrix.mulVec_mulVec]
  · exact hP _ _ (hM.1.1 a)
  · exact hP _ _ hM.1.2
  · exact hP _ _ (hM.2 y hy)

/- English proof (translation)
Apply the tactic sequence `refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [Matrix.add_mulVec]`. Conclude with `add_mem (hM.1.1 a) (hM'.1.1 a)`. Conclude with `add_mem hM.1.2 hM'.1.2`. Conclude with `add_mem (hM.2 y hy) (hM'.2 y hy)`.
-/
theorem Good.add {M M' : Matrix (Fin n) (Fin n) ℂ} (hM : Good ε e z M) (hM' : Good ε e z M') :
    Good ε e z (M + M') := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [Matrix.add_mulVec]
  · exact add_mem (hM.1.1 a) (hM'.1.1 a)
  · exact add_mem hM.1.2 hM'.1.2
  · exact add_mem (hM.2 y hy) (hM'.2 y hy)

/- English proof (translation)
Apply the tactic sequence `refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [Matrix.neg_mulVec]`. Conclude with `neg_mem (hM.1.1 a)`. Conclude with `neg_mem hM.1.2`. Conclude with `neg_mem (hM.2 y hy)`.
-/
theorem Good.neg {M : Matrix (Fin n) (Fin n) ℂ} (hM : Good ε e z M) : Good ε e z (-M) := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [Matrix.neg_mulVec]
  · exact neg_mem (hM.1.1 a)
  · exact neg_mem hM.1.2
  · exact neg_mem (hM.2 y hy)

/- English proof (translation)
Apply the tactic sequence `refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> rw [Matrix.zero_mulVec] <;> exact zero_mem _`.
-/
theorem good_zero : Good ε e z (0 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> rw [Matrix.zero_mulVec] <;> exact zero_mem _

/- English proof (translation)
Use `pres_of e g fun b => ?_` and prove the remaining obligations. Establish `e1 : g *ᵥ e b = (g - 1) *ᵥ e b + e b`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]`. Rewrite using `[e1]`. Conclude with `add_mem (spanLt_mono e (Nat.le_succ _) (h.1.1 b)) (Submodule.subset_span ⟨b, Nat.lt_succ_self _, rfl⟩)`.
-/
theorem pres_of_good {g : Matrix (Fin n) (Fin n) ℂ} (h : Good ε e z (g - 1)) : Pres e g := by
  refine pres_of e g fun b => ?_
  have e1 : g *ᵥ e b = (g - 1) *ᵥ e b + e b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  rw [e1]
  exact add_mem (spanLt_mono e (Nat.le_succ _) (h.1.1 b)) (Submodule.subset_span ⟨b, Nat.lt_succ_self _, rfl⟩)

/- English proof (translation)
Introduce `a v hv`. Set `f : spanLt e a →ₗ[ℂ] spanLt e a` to `(Matrix.mulVecLin g).restrict (fun x hx => hP a x hx)`. Establish `hf : ∀ w : spanLt e a, ((f w : spanLt e a) : Fin n → ℂ) = g *ᵥ (w : Fin n → ℂ)` using `fun w => rfl`. Establish `hinj : Function.Injective f`. Introduce `x y hxy`.

Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (fun w : spanLt e a => g' *ᵥ (w : Fin n → ℂ)) hxy` as an intermediate fact. Simplify using `only [hf, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this`. Conclude with `this`. Take `⟨w, hw⟩` from `(LinearMap.injective_iff_surjective.1 hinj) ⟨v, hv⟩`.

Establish `: g' *ᵥ v = w`. Use `congrArg (fun w : spanLt e a => g' *ᵥ (w : Fin n → ℂ)) hw` as an intermediate fact. Simplify using `only [hf, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this`. Conclude with `this.symm`. Rewrite using `[this]`.

Conclude with `w.2`.
-/
theorem pres_inv {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1) (hP : Pres e g) : Pres e g' := by
  intro a v hv
  let f : spanLt e a →ₗ[ℂ] spanLt e a := (Matrix.mulVecLin g).restrict (fun x hx => hP a x hx)
  have hf : ∀ w : spanLt e a, ((f w : spanLt e a) : Fin n → ℂ) = g *ᵥ (w : Fin n → ℂ) := fun w => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun w : spanLt e a => g' *ᵥ (w : Fin n → ℂ)) hxy
    simp only [hf, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
    exact this
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨v, hv⟩
  have : g' *ᵥ v = w := by
    have := congrArg (fun w : spanLt e a => g' *ᵥ (w : Fin n → ℂ)) hw
    simp only [hf, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
    exact this.symm
  rw [this]
  exact w.2

/- English proof (translation)
Establish `e1 : g' - 1 = -(g' * (g - 1))` using `by rw [Matrix.mul_sub, h1, Matrix.mul_one, neg_sub]`. Rewrite using `[e1]`. Conclude with `(Good.pres_mul (pres_inv h1 (pres_of_good h)) h).neg`.
-/
theorem Good.inv {g g' : Matrix (Fin n) (Fin n) ℂ} (h : Good ε e z (g - 1)) (h1 : g' * g = 1) :
    Good ε e z (g' - 1) := by
  have e1 : g' - 1 = -(g' * (g - 1)) := by rw [Matrix.mul_sub, h1, Matrix.mul_one, neg_sub]
  rw [e1]
  exact (Good.pres_mul (pres_inv h1 (pres_of_good h)) h).neg

/- English proof (translation)
Establish `e1 : g * g' - 1 = (g - 1) * (g' - 1) + (g - 1) + (g' - 1)` using `by noncomm_ring`. Rewrite using `[e1]`. Conclude with `((Good.pres_mul h.pres h').add h).add h'`.
-/
theorem Good.mul {g g' : Matrix (Fin n) (Fin n) ℂ} (h : Good ε e z (g - 1)) (h' : Good ε e z (g' - 1)) :
    Good ε e z (g * g' - 1) := by
  have e1 : g * g' - 1 = (g - 1) * (g' - 1) + (g - 1) + (g' - 1) := by noncomm_ring
  rw [e1]
  exact ((Good.pres_mul h.pres h').add h).add h'

variable (ε e z)

def nSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := NLoc ε e z
  one_mem' := by
    show Good ε e z (uMat (1 : Formalism.REAL.UJ ε) - 1)
    have : uMat (1 : Formalism.REAL.UJ ε) - 1 = 0 := sub_self _
    rw [this]
    exact good_zero
  mul_mem' := fun {x y} hx hy => Good.mul hx hy
  inv_mem' := fun {x} hx => Good.inv hx (Units.inv_mul (x : (Matrix (Fin n) (Fin n) ℂ)ˣ))

/- English proof (translation)
Establish `hW : ∀ a, IsClosed ((spanLt e a : Set (Fin n → ℂ)))` using `fun a => Submodule.closed_of_finiteDimensional _`. Establish `hc : ∀ (v : Fin n → ℂ) (a : ℕ), IsClosed {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ v ∈ spanLt e a}` using `fun v a => (hW a).preimage ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)`. Establish `hM : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | InN ε e z M}`. Simplify using `only [InN, InS, Set.setOf_and, Set.setOf_forall]`. Conclude with `((isClosed_iInter fun a => hc _ _).inter (hc _ _)).inter (isClosed_iInter fun y => isClosed_iInter fun _ => hc _ _)`.

Conclude with `hM.preimage (Units.continuous_val.comp continuous_subtype_val)`.
-/
theorem isClosed_nLoc : IsClosed (NLoc ε e z) := by
  have hW : ∀ a, IsClosed ((spanLt e a : Set (Fin n → ℂ))) := fun a => Submodule.closed_of_finiteDimensional _
  have hc : ∀ (v : Fin n → ℂ) (a : ℕ), IsClosed {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ v ∈ spanLt e a} :=
    fun v a => (hW a).preimage ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)
  have hM : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | InN ε e z M} := by
    simp only [InN, InS, Set.setOf_and, Set.setOf_forall]
    exact ((isClosed_iInter fun a => hc _ _).inter (hc _ _)).inter
      (isClosed_iInter fun y => isClosed_iInter fun _ => hc _ _)
  exact hM.preimage (Units.continuous_val.comp continuous_subtype_val)

variable (z' : Fin n → ℂ) (γ : Formalism.REAL.UJ ε)

def stSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := StSet (NLoc ε e z) (NLoc ε e z') γ
  one_mem' := ⟨(nSub ε e z).one_mem, by
    have : γ⁻¹ * 1 * γ = 1 := by group
    rw [this]; exact (nSub ε e z').one_mem⟩
  mul_mem' := fun {x y} hx hy => ⟨(nSub ε e z).mul_mem hx.1 hy.1, by
    have : γ⁻¹ * (x * y) * γ = (γ⁻¹ * x * γ) * (γ⁻¹ * y * γ) := by group
    rw [this]; exact (nSub ε e z').mul_mem hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨(nSub ε e z).inv_mem hx.1, by
    have : γ⁻¹ * x⁻¹ * γ = (γ⁻¹ * x * γ)⁻¹ := by group
    rw [this]; exact (nSub ε e z').inv_mem hx.2⟩

/- English proof (translation)
Establish `h1 : (stSub ε e z z' γ : Set (Formalism.REAL.UJ ε)) = NLoc ε e z ∩ (fun y => γ⁻¹ * y * γ) ⁻¹' NLoc ε e z'` using `rfl`. Establish `h2 : Continuous (fun y : Formalism.REAL.UJ ε => γ⁻¹ * y * γ)` using `(continuous_mul_right γ).comp (continuous_mul_left γ⁻¹)`. Rewrite using `[h1]`. Conclude with `(isClosed_nLoc ε e z).inter ((isClosed_nLoc ε e z').preimage h2)`.
-/
theorem isClosed_stSub : IsClosed (stSub ε e z z' γ : Set (Formalism.REAL.UJ ε)) := by
  have h1 : (stSub ε e z z' γ : Set (Formalism.REAL.UJ ε)) =
      NLoc ε e z ∩ (fun y => γ⁻¹ * y * γ) ⁻¹' NLoc ε e z' := rfl
  have h2 : Continuous (fun y : Formalism.REAL.UJ ε => γ⁻¹ * y * γ) :=
    (continuous_mul_right γ).comp (continuous_mul_left γ⁻¹)
  rw [h1]
  exact (isClosed_nLoc ε e z).inter ((isClosed_nLoc ε e z').preimage h2)

end Sub

/- English proof (translation)
Introduce `D X u u' γ μl hμ`. Establish `hloc : ∀ v, ∃ b : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable b ∧ ∀ g, ∫⁻ s, b (s⁻¹ * g) ∂(μl v) = 1`. Introduce `v`. Use `haveI := (hμ v).1`. Conclude with `cutoff_left (stSub (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u')) (γ v)) (μl v) (isClosed_stSub _ _ _ _ _) (hμ v).2.1 (hμ v).2.2.1 (fun s hs => (hμ v).2.2.2 s hs)`.

Use `choose b hb h1 using hloc`. Use `haveI : ∀ v, SigmaFinite (μl v) := fun v => (hμ v).1`. Use `⟨fun v => ⟨(Formalism.REAL.muG _).withDensity (b v), fun f hf => weil_of_cutoff _ _ (hb v) (h1 v) f hf⟩, (Formalism.L2.SG.ProjRows.muInf X.B.I).withDensity (fun x => ∏ v, b v (x v)), fun f hf => weil_of_cutoff _ _ ?_ ?_ f hf⟩` and prove the remaining obligations. Conclude with `Finset.measurable_prod _ fun v _ => (hb v).comp (measurable_pi_apply v)`. Introduce `g`.

Use `GlobalTheory.SnMass.Push.lintegral_fintype_prod (μ := μl) (fun v s => b v (s⁻¹ * g v)) fun v => (hb v).comp (measurable_inv.mul_const _)` as an intermediate fact. Simplify using `only [Pi.mul_apply, Pi.inv_apply]`. Rewrite using `[this]`. Simplify using `[h1]`.
-/
theorem quot_exists : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, ∃ νv, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) νv) ∧ ∃ ν, IsQuotMeasS X.B.I (Measure.pi μl) ν := by
  intro D X u u' γ μl hμ
  have hloc : ∀ v, ∃ b : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable b ∧
      ∀ g, ∫⁻ s, b (s⁻¹ * g) ∂(μl v) = 1 := by
    intro v
    haveI := (hμ v).1
    exact cutoff_left (stSub (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))
      (rv X.B.I v (X.zR u')) (γ v)) (μl v) (isClosed_stSub _ _ _ _ _) (hμ v).2.1 (hμ v).2.2.1
      (fun s hs => (hμ v).2.2.2 s hs)
  choose b hb h1 using hloc
  haveI : ∀ v, SigmaFinite (μl v) := fun v => (hμ v).1
  refine ⟨fun v => ⟨(Formalism.REAL.muG _).withDensity (b v), fun f hf => weil_of_cutoff _ _ (hb v) (h1 v) f hf⟩,
    (Formalism.L2.SG.ProjRows.muInf X.B.I).withDensity (fun x => ∏ v, b v (x v)),
    fun f hf => weil_of_cutoff _ _ ?_ ?_ f hf⟩
  · exact Finset.measurable_prod _ fun v _ => (hb v).comp (measurable_pi_apply v)
  · intro g
    have := GlobalTheory.SnMass.Push.lintegral_fintype_prod (μ := μl) (fun v s => b v (s⁻¹ * g v))
      fun v => (hb v).comp (measurable_inv.mul_const _)
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [this]
    simp [h1]

end GlobalTheory.QuotExist
