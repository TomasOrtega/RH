import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

/- English proof (translation)
Introduce `n Y _ _ _ _ _ ι La _ A`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `la mu a b ha hb`. Use `⟨⟨fun i => ?_, fun i j y _ hi hj => ?_⟩, fun y => ?_⟩` and prove the remaining obligations. Conclude with `(ha.1 i).mul (hb.1 i)`.

Use `beta_reduce`. Rewrite using `[A.g_add la mu i j y hi hj, ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [WeightedAtlas.nsq]`. Rewrite using `[A.ph_add la mu _ y (A.mem_pick y), norm_mul, mul_pow, neg_add, Real.exp_add]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `la a ha`. Establish `hc : Continuous (A.nsq la a)` using `bsA_nsq_cont A ha`. Establish `: nz A a = A.nsq la a ⁻¹' {0}ᶜ`. Use extensionality with `y`.

Simplify using `only [nz, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, WeightedAtlas.nsq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr h)) (Real.exp_pos _).ne'`. Introduce `h h0`.

Apply `h` to reduce the goal to its premises. Simplify using `[h0]`. Rewrite using `[this]`. Conclude with `isOpen_compl_singleton.preimage hc`. Introduce `B la a b U ha hb hU`.

Establish `hbne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → b i y ≠ 0`. Introduce `i y hy hi`. Rewrite using `[hb.2 i (A.pick y) y trivial hi (A.mem_pick y)]`. Conclude with `mul_ne_zero (A.g_ne B i (A.pick y) y hi (A.mem_pick y)) (hU y hy).2`. Use `⟨⟨fun i => ?_, fun i j y hy hi hj => ?_⟩, fun y hy => div_ne_zero (hU y hy).1 (hU y hy).2⟩` and prove the remaining obligations.

Establish `hS : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆ (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ` using `fun v hv => ⟨hv.1, trivial⟩`. Establish `h1 : DifferentiableOn ℂ (a i ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)` using `(ha.1 i).mono hS`. Establish `h2 : DifferentiableOn ℂ (b i ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U)` using `(hb.1 i).mono hS`. Establish `h3` using `h1.mul (h2.inv (fun v (hv : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U) => hbne i _ hv.2 ((A.chart i).map_target hv.1)))`. Use `h3.congr (fun v _ => ?_)` and prove the remaining obligations.

Simplify using `[div_eq_mul_inv]`. Establish `hgB` using `A.g_ne B i j y hi hj`. Establish `hbj` using `hbne j y hy hj`. Use `beta_reduce`. Rewrite using `[ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj, A.g_add B la i j y hi hj]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem sections_prod_quot_open : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), (∀ (la mu : La) (a b : ι → Y → ℂ), A.IsSec la a → A.IsSec mu b → A.IsSec (la + mu) (fun i y => a i y * b i y) ∧ ∀ y, A.nsq (la + mu) (fun i y => a i y * b i y) y = A.nsq la a y * A.nsq mu b y) ∧ (∀ (la : La) (a : ι → Y → ℂ), A.IsSec la a → IsOpen (nz A a)) ∧ (∀ (B la : La) (a b : ι → Y → ℂ) (U : Set Y), A.IsSec (B + la) a → A.IsSec B b → (∀ y ∈ U, a (A.pick y) y ≠ 0 ∧ b (A.pick y) y ≠ 0) → A.IsFrameOn la U (fun i y => a i y / b i y)) := by
  intro n Y _ _ _ _ _ ι La _ A
  refine ⟨?_, ?_, ?_⟩
  · intro la mu a b ha hb
    refine ⟨⟨fun i => ?_, fun i j y _ hi hj => ?_⟩, fun y => ?_⟩
    · exact (ha.1 i).mul (hb.1 i)
    · beta_reduce
      rw [A.g_add la mu i j y hi hj, ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj]
      ring
    · simp only [WeightedAtlas.nsq]
      rw [A.ph_add la mu _ y (A.mem_pick y), norm_mul, mul_pow, neg_add, Real.exp_add]
      ring
  · intro la a ha
    have hc : Continuous (A.nsq la a) := bsA_nsq_cont A ha
    have : nz A a = A.nsq la a ⁻¹' {0}ᶜ := by
      ext y
      simp only [nz, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff, WeightedAtlas.nsq]
      constructor
      · intro h
        exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr h)) (Real.exp_pos _).ne'
      · intro h h0
        apply h
        simp [h0]
    rw [this]
    exact isOpen_compl_singleton.preimage hc
  · intro B la a b U ha hb hU
    have hbne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → b i y ≠ 0 := by
      intro i y hy hi
      rw [hb.2 i (A.pick y) y trivial hi (A.mem_pick y)]
      exact mul_ne_zero (A.g_ne B i (A.pick y) y hi (A.mem_pick y)) (hU y hy).2
    refine ⟨⟨fun i => ?_, fun i j y hy hi hj => ?_⟩, fun y hy => div_ne_zero (hU y hy).1 (hU y hy).2⟩
    · have hS : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆
          (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ := fun v hv => ⟨hv.1, trivial⟩
      have h1 : DifferentiableOn ℂ (a i ∘ (A.chart i).symm)
          ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (ha.1 i).mono hS
      have h2 : DifferentiableOn ℂ (b i ∘ (A.chart i).symm)
          ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (hb.1 i).mono hS
      have h3 := h1.mul (h2.inv (fun v (hv : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U) =>
        hbne i _ hv.2 ((A.chart i).map_target hv.1)))
      refine h3.congr (fun v _ => ?_)
      simp [div_eq_mul_inv]
    · have hgB := A.g_ne B i j y hi hj
      have hbj := hbne j y hy hj
      beta_reduce
      rw [ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj, A.g_add B la i j y hi hj]
      field_simp

end GlobalTheory.OTY
