import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsPointVertRSteps
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsInvertibleIdealIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualLineIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FieldChange
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionBounded
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace SectionIndexNormAlt

variable {T : Type} {K' : Type} [Field K'] {y : (Σ _ : Unit, T) → K'}

/- English proof (translation)
The claim follows from `Algebra.subset_adjoin ⟨p, rfl⟩`.
-/
theorem ratio_mem (p : Σ _ : Unit, T) (t : T) :
    y p / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) :=
  Algebra.subset_adjoin ⟨p, rfl⟩

/- English proof (translation)
Rewrite using `[mem_curveRing]`. Use `⟨fun h t ht => h (fun _ => t) (fun _ => ht), fun h c hc => ?_⟩` and prove the remaining obligations. Establish `hc' : c = fun _ => c ()` using `funext fun u => by cases u; rfl`. Rewrite using `[hc']`. Conclude with `h (c ()) (hc ())`.
-/
theorem mem_curveRing_iff {b : K'} :
    b ∈ curveRing y ↔ ∀ t : T, y ⟨(), t⟩ ≠ 0 → b ∈ chartRingZ y (fun _ => t) := by
  rw [mem_curveRing]
  refine ⟨fun h t ht => h (fun _ => t) (fun _ => ht), fun h c hc => ?_⟩
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  rw [hc']
  exact h (c ()) (hc ())

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(∀ c : Unit → T, _ → _) ↔ _`. Use `⟨fun h t ht => ?_, fun h c hc => ?_⟩` and prove the remaining obligations. Use `h (fun _ => t) (fun _ => ht)` as an intermediate fact. Simplify `this` using `[div_eq_mul_inv]`. Establish `hc' : c = fun _ => c ()` using `funext fun u => by cases u; rfl`.

Rewrite using `[hc']`. Simplify `h (c ()) (hc ())` using `[div_eq_mul_inv]`.
-/
theorem mem_chartLat_iff [Fintype T] {z : K'} :
    z ∈ chartLat y (fun _ => 1) 1 ↔ ∀ t : T, y ⟨(), t⟩ ≠ 0 → z / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) := by
  change (∀ c : Unit → T, _ → _) ↔ _
  refine ⟨fun h t ht => ?_, fun h c hc => ?_⟩
  · have := h (fun _ => t) (fun _ => ht)
    simpa [div_eq_mul_inv] using this
  · have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
    rw [hc']
    simpa [div_eq_mul_inv] using h (c ()) (hc ())

/- English proof (translation)
Rewrite using `[s.as_sum, map_sum, Finset.sum_div]`. Use `Subalgebra.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Rewrite using `[aeval_monomial, mul_div_assoc]`. Use `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_` and prove the remaining obligations. Establish `hsum : ∑ p, m p = 1`.

Rewrite using `[Fintype.sum_sigma, Fintype.sum_unique]`. Conclude with `hs m hm ()`. Establish `key : m.prod (fun p e => y p ^ e) / y ⟨(), t⟩ = ∏ p, (y p / y ⟨(), t⟩) ^ m p`. Rewrite using `[Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `only [div_pow]`.

Rewrite using `[Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsum, pow_one]`. Rewrite using `[key]`. Conclude with `Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _ (ratio_mem p t) _`.
-/
theorem aeval_div_mem [Fintype T] {s : MRing (fun _ : Unit => T)} (hs : IsMultiHomog s (fun _ => 1))
    (t : T) : aeval y s / y ⟨(), t⟩ ∈ chartRingZ y (fun _ => t) := by
  classical
  rw [s.as_sum, map_sum, Finset.sum_div]
  refine Subalgebra.sum_mem _ fun m hm => ?_
  rw [aeval_monomial, mul_div_assoc]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
  have hsum : ∑ p, m p = 1 := by
    rw [Fintype.sum_sigma, Fintype.sum_unique]
    exact hs m hm ()
  have key : m.prod (fun p e => y p ^ e) / y ⟨(), t⟩ = ∏ p, (y p / y ⟨(), t⟩) ^ m p := by
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp only [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsum, pow_one]
  rw [key]
  exact Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _ (ratio_mem p t) _

/- English proof (translation)
Establish `h1 : (1 : curveRing y) ∉ m` using `fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h)`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Take `⟨⟨⟨⟩, u⟩, rfl⟩` from `hx`. Take `⟨a, b, hb, hab⟩` from `ht u`.

Conclude with `⟨b, hb, by convert a.2 using 1⟩`. Consider the case `algebraMap r`. Conclude with `⟨1, h1, by simp⟩`. Consider the case `add x z _ _ hx hz`. Take `⟨b1, hb1, h1'⟩` from `hx`.

Take `⟨b2, hb2, h2'⟩` from `hz`. Use `⟨b1 * b2, fun h => (hm.mem_or_mem h).elim hb1 hb2, ?_⟩` and prove the remaining obligations. Establish `e : ((b1 * b2 : curveRing y) : K') * (x + z) = b2 * (b1 * x) + b1 * (b2 * z)` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `add_mem (mul_mem b2.2 h1') (mul_mem b1.2 h2')`.

Consider the case `mul x z _ _ hx hz`. Take `⟨b1, hb1, h1'⟩` from `hx`. Take `⟨b2, hb2, h2'⟩` from `hz`. Use `⟨b1 * b2, fun h => (hm.mem_or_mem h).elim hb1 hb2, ?_⟩` and prove the remaining obligations. Establish `e : ((b1 * b2 : curveRing y) : K') * (x * z) = (b1 * x) * (b2 * z)` using `by push_cast; ring`.

Rewrite using `[e]`. Conclude with `mul_mem h1' h2'`.
-/
theorem exists_mul_mem {m : Ideal (curveRing y)} (hm : m.IsPrime) {t : T}
    (ht : ∀ u, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) {z : K'}
    (hz : z ∈ chartRingZ y (fun _ => t)) : ∃ b : curveRing y, b ∉ m ∧ (b : K') * z ∈ curveRing y := by
  have h1 : (1 : curveRing y) ∉ m := fun h => hm.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨⟨⟩, u⟩, rfl⟩ := hx
    obtain ⟨a, b, hb, hab⟩ := ht u
    exact ⟨b, hb, by convert a.2 using 1⟩
  | algebraMap r =>
    exact ⟨1, h1, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨b1, hb1, h1'⟩ := hx
    obtain ⟨b2, hb2, h2'⟩ := hz
    refine ⟨b1 * b2, fun h => (hm.mem_or_mem h).elim hb1 hb2, ?_⟩
    have e : ((b1 * b2 : curveRing y) : K') * (x + z) = b2 * (b1 * x) + b1 * (b2 * z) := by
      push_cast; ring
    rw [e]
    exact add_mem (mul_mem b2.2 h1') (mul_mem b1.2 h2')
  | mul x z _ _ hx hz =>
    obtain ⟨b1, hb1, h1'⟩ := hx
    obtain ⟨b2, hb2, h2'⟩ := hz
    refine ⟨b1 * b2, fun h => (hm.mem_or_mem h).elim hb1 hb2, ?_⟩
    have e : ((b1 * b2 : curveRing y) : K') * (x * z) = (b1 * x) * (b2 * z) := by
      push_cast; ring
    rw [e]
    exact mul_mem h1' h2'

/- English proof (translation)
Introduce `h` and use `hb (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)`.
-/
theorem coe_ne_zero_of_notMem {m : Ideal (curveRing y)} {b : curveRing y} (hb : b ∉ m) : (b : K') ≠ 0 :=
  fun h => hb (by rw [show b = 0 from Subtype.ext h]; exact m.zero_mem)

/- English proof (translation)
The claim follows from `|((Algebra.norm ℚ x : ℚ) : ℝ)| := by have hy' : (fun p => y p / x) ≠ 0 := by obtain ⟨p, hp⟩ := Function.ne_iff.mp hy exact Function.ne_iff.mpr ⟨p, div_ne_zero hp hx⟩ rw [DualLineIndexAlt.genIndex_span_eq_finprod hy', DualLineIndexAlt.genIndex_span_eq_finprod hy] have e : ∀ w : Fi …`.
-/
theorem genIndex_span_div [NumberField K'] [Fintype T] (hy : y ≠ 0) {x : K'} (hx : x ≠ 0) :
    genIndex (Submodule.span (𝓞 K') (Set.range fun p => y p / x)).toAddSubgroup
        (1 : Submodule (𝓞 K') K').toAddSubgroup =
      genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 K') K').toAddSubgroup *
        |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have hy' : (fun p => y p / x) ≠ 0 := by
    obtain ⟨p, hp⟩ := Function.ne_iff.mp hy
    exact Function.ne_iff.mpr ⟨p, div_ne_zero hp hx⟩
  rw [DualLineIndexAlt.genIndex_span_eq_finprod hy', DualLineIndexAlt.genIndex_span_eq_finprod hy]
  have e : ∀ w : FinitePlace K', ⨆ p, w (y p / x) = (⨆ p, w (y p)) * w x⁻¹ := by
    intro w
    simp only [div_eq_mul_inv, map_mul]
    exact (Real.iSup_mul_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [e]
  rw [finprod_mul_distrib (hasFiniteMulSupport_iSup_place hy)
    (FinitePlace.hasFiniteMulSupport (inv_ne_zero hx)), FinitePlace.prod_eq_inv_abs_norm (inv_ne_zero hx)]
  have hN : Algebra.norm ℚ x⁻¹ = (Algebra.norm ℚ x)⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel₀ hx, map_one])
  rw [hN]
  push_cast
  rw [abs_inv, inv_inv]

/- English proof (translation)
Establish `hy : y ≠ 0` using `fun h => hp0 (by rw [h, Pi.zero_apply])`. Rewrite using `[DualLineIndexAlt.genIndex_span_eq_finprod hy, finprod_eq_prod _ (hasFiniteMulSupport_iSup_place hy)]`. Use `Finset.prod_pos fun w _ => ?_` and prove the remaining obligations. Conclude with `lt_of_lt_of_le (FinitePlace.pos_iff.mpr hp0) (le_ciSup (f := fun p => w (y p)) (Finite.bddAbove_range _) p0)`.
-/
theorem genIndex_span_pos [NumberField K'] [Fintype T] {p0 : Σ _ : Unit, T} (hp0 : y p0 ≠ 0) :
    0 < genIndex (Submodule.span (𝓞 K') (Set.range y)).toAddSubgroup
      (1 : Submodule (𝓞 K') K').toAddSubgroup := by
  have hy : y ≠ 0 := fun h => hp0 (by rw [h, Pi.zero_apply])
  rw [DualLineIndexAlt.genIndex_span_eq_finprod hy,
    finprod_eq_prod _ (hasFiniteMulSupport_iSup_place hy)]
  refine Finset.prod_pos fun w _ => ?_
  exact lt_of_lt_of_le (FinitePlace.pos_iff.mpr hp0) (le_ciSup (f := fun p => w (y p)) (Finite.bddAbove_range _) p0)

end SectionIndexNormAlt

open SectionIndexNormAlt in

/- English proof (translation)
Introduce `T _ K' _ _ y s hP hs hsP`. Take `⟨hfin, hrank, hloc⟩` from `hC T K' y hP`. Use `set x := aeval y s with hxdef`. Establish `hx0 : x ≠ 0`. Introduce `h0`.

Apply `hsP` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `s ∈ RingHom.ker (mConeMap y)`. Rewrite using `[RingHom.mem_ker]`. Use `erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]`. Rewrite using `[← hxdef, h0, map_zero, zero_mul]`.

Take `⟨m0, hm0⟩` from `Ideal.exists_maximal (curveRing y)`. Take `⟨t1, ht1, hl1⟩` from `hloc m0 hm0`. Set `f : K' →+ K'` to `AddMonoidHom.mulLeft x⁻¹`. Establish `hf : ∀ z, f z = x⁻¹ * z` using `fun _ => rfl`. Set `a : (Σ _ : Unit, T) → K'` to `fun p => y p / x`.

Establish `key` using `hI K' (curveRing y) ((chartLat y (fun _ => 1) 1).map f) (Σ _ : Unit, T) a hfin ?_ ?_ ?_ ?_`. Establish `hB : (curveRing y).toAddSubgroup = (curveMul y x).map f`. Rewrite using `[curveMul, AddSubgroup.map_map]`. Use extensionality with `z`. Simplify using `[hf, hx0]`.

Establish `hinj : Function.Injective f` using `fun u v h => mul_left_cancel₀ (inv_ne_zero hx0) h`. Rewrite `key` using `[hB, KLinesLineDegree.genIndex_map_of_injective f hinj, genIndex_span_div ?_ hx0, Real.log_mul (genIndex_span_pos (p0 := ⟨(), t1⟩) ht1).ne' (abs_pos.mpr (by exact_mod_cast Algebra.norm_ne_zero_iff.mpr hx0)).ne', hrank, ← Module.finrank_mul_finrank ℚ (blockFnField y) K']`. Establish `hF : (0 : ℝ) < Module.finrank ℚ (blockFnField y)` using `Nat.cast_pos.mpr Module.finrank_pos`. Apply `mul_left_cancel₀ hF.ne'` to reduce the goal to its premises. Move the coercions through the operations in `at key`.

Take the linear combination `key`. Conclude with `fun h => ht1 (by rw [h, Pi.zero_apply])`. Introduce `b hb z hz`. Take `⟨w, hw, rfl⟩` from `AddSubgroup.mem_map.mp hz`. Use `AddSubgroup.mem_map.mpr ⟨b * w, ?_, by rw [hf, hf]; ring⟩` and prove the remaining obligations.

Rewrite `hw`, the goal using `[mem_chartLat_iff]`. Introduce `t ht`. Rewrite using `[mul_div_assoc]`. Conclude with `mul_mem (mem_curveRing_iff.mp hb t ht) (hw t ht)`. Introduce `p`.

Use `AddSubgroup.mem_map.mpr ⟨y p, ?_, by rw [hf]; simp [a, div_eq_inv_mul]⟩` and prove the remaining obligations. Conclude with `mem_chartLat_iff.mpr fun t _ => ratio_mem p t`. Introduce and unpack `⟨⟨⟩, u⟩`. Take `⟨β, hβ, hβx⟩` from `exists_mul_mem hm0.isPrime hl1 (aeval_div_mem hs t1)`. Take `⟨c, b, hb, hbc⟩` from `hl1 u`.

Use `⟨(β : K') * (x / y ⟨(), t1⟩) * b, mul_mem hβx b.2, ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_ne_zero (mul_ne_zero (coe_ne_zero_of_notMem hβ) (div_ne_zero hx0 ht1)) (coe_ne_zero_of_notMem hb)`. Establish `e : (β : K') * (x / y ⟨(), t1⟩) * b * a ⟨(), u⟩ = β * c`. Rewrite using `[← hbc]`. Simplify using `only [a]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `mul_mem β.2 c.2`. Introduce `m hm`. Take `⟨t, ht, hl⟩` from `hloc m hm`.

Use `⟨⟨(), t⟩, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨w, hw, rfl⟩` from `AddSubgroup.mem_map.mp hz`. Take `⟨b, hb, hbw⟩` from `exists_mul_mem hm.isPrime hl (mem_chartLat_iff.mp hw t ht)`. Use `⟨b, ⟨_, hbw⟩, hb, ?_⟩` and prove the remaining obligations. Simplify using `only [hf, a]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem SectionIndexNorm.proof (hC : CurveCharts.Statement) (hI : InvertibleIdealIndex.Statement) :
    SectionIndexNorm.Statement := by
  intro T _ K' _ _ y s hP hs hsP
  obtain ⟨hfin, hrank, hloc⟩ := hC T K' y hP
  set x := aeval y s with hxdef
  have hx0 : x ≠ 0 := by
    intro h0
    apply hsP
    change s ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker]
    erw [HilbertSamuel.SectionBounded.mConeMap_homog y hs]
    rw [← hxdef, h0, map_zero, zero_mul]
  obtain ⟨m0, hm0⟩ := Ideal.exists_maximal (curveRing y)
  obtain ⟨t1, ht1, hl1⟩ := hloc m0 hm0
  let f : K' →+ K' := AddMonoidHom.mulLeft x⁻¹
  have hf : ∀ z, f z = x⁻¹ * z := fun _ => rfl
  let a : (Σ _ : Unit, T) → K' := fun p => y p / x
  have key := hI K' (curveRing y) ((chartLat y (fun _ => 1) 1).map f) (Σ _ : Unit, T) a hfin ?_ ?_ ?_ ?_
  ·
    have hB : (curveRing y).toAddSubgroup = (curveMul y x).map f := by
      rw [curveMul, AddSubgroup.map_map]
      ext z
      simp [hf, hx0]
    have hinj : Function.Injective f := fun u v h => mul_left_cancel₀ (inv_ne_zero hx0) h
    rw [hB, KLinesLineDegree.genIndex_map_of_injective f hinj, genIndex_span_div ?_ hx0,
      Real.log_mul (genIndex_span_pos (p0 := ⟨(), t1⟩) ht1).ne'
        (abs_pos.mpr (by exact_mod_cast Algebra.norm_ne_zero_iff.mpr hx0)).ne',
      hrank, ← Module.finrank_mul_finrank ℚ (blockFnField y) K'] at key
    · have hF : (0 : ℝ) < Module.finrank ℚ (blockFnField y) := Nat.cast_pos.mpr Module.finrank_pos
      apply mul_left_cancel₀ hF.ne'
      push_cast at key
      linear_combination key
    · exact fun h => ht1 (by rw [h, Pi.zero_apply])
  ·
    intro b hb z hz
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hz
    refine AddSubgroup.mem_map.mpr ⟨b * w, ?_, by rw [hf, hf]; ring⟩
    rw [mem_chartLat_iff] at hw ⊢
    intro t ht
    rw [mul_div_assoc]
    exact mul_mem (mem_curveRing_iff.mp hb t ht) (hw t ht)
  ·
    intro p
    refine AddSubgroup.mem_map.mpr ⟨y p, ?_, by rw [hf]; simp [a, div_eq_inv_mul]⟩
    exact mem_chartLat_iff.mpr fun t _ => ratio_mem p t
  ·
    rintro ⟨⟨⟩, u⟩
    obtain ⟨β, hβ, hβx⟩ := exists_mul_mem hm0.isPrime hl1 (aeval_div_mem hs t1)
    obtain ⟨c, b, hb, hbc⟩ := hl1 u
    refine ⟨(β : K') * (x / y ⟨(), t1⟩) * b, mul_mem hβx b.2, ?_, ?_⟩
    · exact mul_ne_zero (mul_ne_zero (coe_ne_zero_of_notMem hβ) (div_ne_zero hx0 ht1))
        (coe_ne_zero_of_notMem hb)
    · have e : (β : K') * (x / y ⟨(), t1⟩) * b * a ⟨(), u⟩ = β * c := by
        rw [← hbc]
        simp only [a]
        field_simp
      rw [e]
      exact mul_mem β.2 c.2
  ·
    intro m hm
    obtain ⟨t, ht, hl⟩ := hloc m hm
    refine ⟨⟨(), t⟩, fun z hz => ?_⟩
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.mp hz
    obtain ⟨b, hb, hbw⟩ := exists_mul_mem hm.isPrime hl (mem_chartLat_iff.mp hw t ht)
    refine ⟨b, ⟨_, hbw⟩, hb, ?_⟩
    simp only [hf, a]
    field_simp

end

end GroundTheory.Heights₂.Heights
