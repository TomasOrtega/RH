import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDualUnram

noncomputable section

open ValuativeRel

namespace PI.LocDualGen.FpD

open PI.LocDualGen.W

section

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]

def P (x : K) : Prop := ∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (x * (b : K))‖ ≤ 1

/- English proof (translation)
Rewrite using `[← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]`.
-/
theorem tr_alg_mul (q : ℚ_[l]) (z : K) :
    Algebra.trace ℚ_[l] K (algebraMap ℚ_[l] K q * z) = q * Algebra.trace ℚ_[l] K z := by
  rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]

/- English proof (translation)
The claim follows from `norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`.
-/
theorem norm_l_pos : (0 : ℝ) < ‖(l : ℚ_[l])‖ :=
  norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)

/- English proof (translation)
Establish `hn : ((Module.finrank ℚ_[l] K : ℕ) : ℚ_[l]) ≠ 0`. Establish `: 0 < Module.finrank ℚ_[l] K` using `Module.finrank_pos`. Conclude with `this.ne'` after adjusting the coercions. Take `⟨m, hm⟩` from `exists_pow_lt_of_lt_one (norm_pos_iff.mpr hn) (Padic.norm_p_lt_one (p := l))`. Use `⟨m, fun x hx => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hcx`. Rewrite `hcx` using `[Valuation.mem_integer_iff, not_le]`. Establish `hcx0 : algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ≠ 0`. Introduce `h`. Rewrite `hcx` using `[h, map_zero]`.

Conclude with `absurd hcx (not_lt.mpr zero_le)`. Establish `hb : (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹ ∈ 𝒪[K]`. Rewrite using `[Valuation.mem_integer_iff, map_inv₀]`. Conclude with `inv_le_one_of_one_le₀ hcx.le`. Establish `hx0 : x ≠ 0` using `right_ne_zero_of_mul hcx0`.

Establish `hc0 : algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) ≠ 0` using `left_ne_zero_of_mul hcx0`. Establish `h1` using `hx ⟨_, hb⟩`. Express the relevant statement in the definitionally equal form `‖Algebra.trace ℚ_[l] K (x * (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹)‖ ≤ 1 at h1`. Establish `e : x * (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹ = algebraMap ℚ_[l] K (((l : ℚ_[l]) ^ m)⁻¹)`. Rewrite using `[map_inv₀]`.

Clear the denominators using the available nonvanishing facts. Rewrite `h1` using `[e, Algebra.trace_algebraMap, nsmul_eq_mul, norm_mul, norm_inv, norm_pow]`. Establish `hpos : 0 < ‖(l : ℚ_[l])‖ ^ m` using `pow_pos (norm_l_pos l) m`. Rewrite `h1` using `[mul_inv_le_iff₀ hpos, one_mul]`. Conclude with `absurd hm (not_lt.mpr h1)`.
-/
theorem bound : ∃ m : ℕ, ∀ x : K, P l x → algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ∈ 𝒪[K] := by
  have hn : ((Module.finrank ℚ_[l] K : ℕ) : ℚ_[l]) ≠ 0 := by
    have : 0 < Module.finrank ℚ_[l] K := Module.finrank_pos
    exact_mod_cast this.ne'
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hn) (Padic.norm_p_lt_one (p := l))
  refine ⟨m, fun x hx => ?_⟩
  by_contra hcx
  rw [Valuation.mem_integer_iff, not_le] at hcx
  have hcx0 : algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ≠ 0 := by
    intro h
    rw [h, map_zero] at hcx
    exact absurd hcx (not_lt.mpr zero_le)
  have hb : (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹ ∈ 𝒪[K] := by
    rw [Valuation.mem_integer_iff, map_inv₀]
    exact inv_le_one_of_one_le₀ hcx.le
  have hx0 : x ≠ 0 := right_ne_zero_of_mul hcx0
  have hc0 : algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) ≠ 0 := left_ne_zero_of_mul hcx0
  have h1 := hx ⟨_, hb⟩
  change ‖Algebra.trace ℚ_[l] K (x * (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹)‖ ≤ 1 at h1
  have e : x * (algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x)⁻¹ =
      algebraMap ℚ_[l] K (((l : ℚ_[l]) ^ m)⁻¹) := by
    rw [map_inv₀]
    field_simp
  rw [e, Algebra.trace_algebraMap, nsmul_eq_mul, norm_mul, norm_inv, norm_pow] at h1
  have hpos : 0 < ‖(l : ℚ_[l])‖ ^ m := pow_pos (norm_l_pos l) m
  rw [mul_inv_le_iff₀ hpos, one_mul] at h1
  exact absurd hm (not_lt.mpr h1)

/- English proof (translation)
Use `IsTopologicalAddGroup.t2Space_of_zero_sep ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hv : ValuativeRel.valuation K x ≠ 0` using `(Valuation.ne_zero_iff _).2 hx`. Use `⟨{z | ValuativeRel.valuation K z < ValuativeRel.valuation K x}, ?_, fun h => lt_irrefl (ValuativeRel.valuation K x) h⟩` and prove the remaining obligations. Conclude with `(IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hv, fun z hz => hz⟩`.
-/
private theorem t2_lemma : T2Space K := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep ?_
  intro x hx
  have hv : ValuativeRel.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  refine ⟨{z | ValuativeRel.valuation K z < ValuativeRel.valuation K x}, ?_, fun h => lt_irrefl (ValuativeRel.valuation K x) h⟩
  exact (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨Units.mk0 _ hv, fun z hz => hz⟩

/- English proof (translation)
Establish `h0 : ((𝒪[K]).toAddSubgroup : Set K) ∈ nhds (0 : K)`. Use `(IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hz' : ValuativeRel.valuation K z < 1` using `by simpa using hz`. Conclude with `(Valuation.mem_integer_iff _ _).2 hz'.le`. Conclude with `AddSubgroup.isOpen_of_mem_nhds _ h0`.
-/
private theorem isOpen_lemma_2 : IsOpen (𝒪[K] : Set K) := by
  have h0 : ((𝒪[K]).toAddSubgroup : Set K) ∈ nhds (0 : K) := by
    refine (IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨1, fun z hz => ?_⟩
    have hz' : ValuativeRel.valuation K z < 1 := by simpa using hz
    exact (Valuation.mem_integer_iff _ _).2 hz'.le
  exact AddSubgroup.isOpen_of_mem_nhds _ h0

/- English proof (translation)
Use `haveI := t2_lemma (K := K)`. Use `haveI : ContinuousSMul ℚ_[l] K := ⟨by`. Simplify using `only [Algebra.smul_def]`. Conclude with `(hcont.comp continuous_fst).mul continuous_snd⟩`. Conclude with `LinearMap.continuous_of_finiteDimensional _`.
-/
private theorem trace_cont_lemma_3 (hcont : Continuous (algebraMap ℚ_[l] K)) :
    Continuous (Algebra.trace ℚ_[l] K) := by
  haveI := t2_lemma (K := K)
  haveI : ContinuousSMul ℚ_[l] K := ⟨by
    simp only [Algebra.smul_def]
    exact (hcont.comp continuous_fst).mul continuous_snd⟩
  exact LinearMap.continuous_of_finiteDimensional _

/- English proof (translation)
Establish `hcl : IsClosed (𝒪[K] : Set K)` using `AddSubgroup.isClosed_of_isOpen ((𝒪[K]).toAddSubgroup) (isOpen_lemma_2 (K := K))`. Set `w : ℤ_[l]` to `⟨z, hz⟩`. Establish `key : algebraMap ℚ_[l] K (w : ℚ_[l]) ∈ 𝒪[K]`. Use `PadicInt.denseRange_natCast.induction_on w ?_ ?_` and prove the remaining obligations. Conclude with `hcl.preimage (hcont.comp continuous_subtype_val)`.

Introduce `n`. Rewrite using `[PadicInt.coe_natCast, map_natCast]`. Conclude with `natCast_mem _ n`. Conclude with `key`.
-/
private theorem int_lemma_4 (hcont : Continuous (algebraMap ℚ_[l] K)) (z : ℚ_[l]) (hz : ‖z‖ ≤ 1) :
    algebraMap ℚ_[l] K z ∈ 𝒪[K] := by
  have hcl : IsClosed (𝒪[K] : Set K) :=
    AddSubgroup.isClosed_of_isOpen ((𝒪[K]).toAddSubgroup) (isOpen_lemma_2 (K := K))
  let w : ℤ_[l] := ⟨z, hz⟩
  have key : algebraMap ℚ_[l] K (w : ℚ_[l]) ∈ 𝒪[K] := by
    refine PadicInt.denseRange_natCast.induction_on w ?_ ?_
    · exact hcl.preimage (hcont.comp continuous_subtype_val)
    · intro n
      rw [PadicInt.coe_natCast, map_natCast]
      exact natCast_mem _ n

  exact key

/- English proof (translation)
Establish `h1 : Filter.Tendsto (fun k : ℕ => (l : ℚ_[l]) ^ k) Filter.atTop (nhds 0)` using `tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by first`. Consider the case `exact Padic.norm_p_lt_one`. Consider the case `(rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))`. Establish `h2 : Filter.Tendsto (fun k : ℕ => algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y) Filter.atTop (nhds 0)`. Use `((hcont.tendsto 0).comp h1).mul_const y` as an intermediate fact.

Rewrite `this` using `[map_zero, zero_mul]`. Conclude with `this`. Establish `h3 : (𝒪[K] : Set K) ∈ nhds (0 : K)` using `(isOpen_lemma_2 (K := K)).mem_nhds (zero_mem _)`. Conclude with `Filter.eventually_atTop.1 (h2.eventually_mem h3)`.
-/
private theorem small_lemma_5 (hcont : Continuous (algebraMap ℚ_[l] K)) (y : K) :
    ∃ N : ℕ, ∀ k ≥ N, algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y ∈ 𝒪[K] := by
  have h1 : Filter.Tendsto (fun k : ℕ => (l : ℚ_[l]) ^ k) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by first
      | exact Padic.norm_p_lt_one
      | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))
  have h2 : Filter.Tendsto (fun k : ℕ => algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ k) * y)
      Filter.atTop (nhds 0) := by
    have := ((hcont.tendsto 0).comp h1).mul_const y
    rw [map_zero, zero_mul] at this
    exact this
  have h3 : (𝒪[K] : Set K) ∈ nhds (0 : K) := (isOpen_lemma_2 (K := K)).mem_nhds (zero_mem _)
  exact Filter.eventually_atTop.1 (h2.eventually_mem h3)

/- English proof (translation)
Introduce `b` and use `by rw [add_mul, map_add] exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx b) (hy b))`.
-/
private theorem P_add_mem {x y : K} (hx : P l x) (hy : P l y) : P l (x + y) := fun b => by
  rw [add_mul, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx b) (hy b))

/- English proof (translation)
Introduce `b` and use `by rw [mul_assoc] exact hx (c * b)`.
-/
private theorem mul_mem_dual₂ {x : K} (hx : P l x) (c : 𝒪[K]) : P l (x * c) := fun b => by
  rw [mul_assoc]
  exact hx (c * b)

/- English proof (translation)
Establish `hl0 : (l : ℚ_[l]) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `hnd` using `traceForm_nondegenerate ℚ_[l] K`. Set `B` to `Module.finBasis ℚ_[l] K`. Use `choose N hN using fun i => small_lemma_5 l hcont (B i)`. Set `b` to `B.isUnitSMul (w := fun i => (l : ℚ_[l]) ^ N i) (fun i => (isUnit_iff_ne_zero.2 hl0).pow _)`.

Establish `hb : ∀ i, b i ∈ 𝒪[K]` using `fun i => by`. Simplify using `only [b, Module.Basis.isUnitSMul_apply, Algebra.smul_def]`. Conclude with `hN i (N i) le_rfl`. Set `D` to `(Algebra.traceForm ℚ_[l] K).dualBasis hnd b`. Use `choose N' hN' using fun i => small_lemma_5 l hcont (D i)`.

Use `⟨Finset.univ.sup N', fun x hx => ?_⟩` and prove the remaining obligations. Establish `hc : ∀ i, algebraMap ℚ_[l] K (D.repr x i) ∈ 𝒪[K]` using `fun i => by`. Apply `int_lemma_4 l hcont` to reduce the goal to its premises. Rewrite using `[LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]`. Conclude with `hx ⟨b i, hb i⟩`.

Rewrite using `[← D.sum_repr x, Finset.mul_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_left_comm]`. Conclude with `mul_mem (hc i) (hN' i _ (Finset.le_sup (Finset.mem_univ i)))`.
-/
private theorem bound_lemma_8 (hcont : Continuous (algebraMap ℚ_[l] K)) :
    ∃ m : ℕ, ∀ x : K, P l x → algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) * x ∈ 𝒪[K] := by
  classical
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hnd := traceForm_nondegenerate ℚ_[l] K
  let B := Module.finBasis ℚ_[l] K
  choose N hN using fun i => small_lemma_5 l hcont (B i)
  let b := B.isUnitSMul (w := fun i => (l : ℚ_[l]) ^ N i)
    (fun i => (isUnit_iff_ne_zero.2 hl0).pow _)
  have hb : ∀ i, b i ∈ 𝒪[K] := fun i => by
    simp only [b, Module.Basis.isUnitSMul_apply, Algebra.smul_def]
    exact hN i (N i) le_rfl
  let D := (Algebra.traceForm ℚ_[l] K).dualBasis hnd b
  choose N' hN' using fun i => small_lemma_5 l hcont (D i)
  refine ⟨Finset.univ.sup N', fun x hx => ?_⟩
  have hc : ∀ i, algebraMap ℚ_[l] K (D.repr x i) ∈ 𝒪[K] := fun i => by
    apply int_lemma_4 l hcont
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
    exact hx ⟨b i, hb i⟩
  rw [← D.sum_repr x, Finset.mul_sum]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, mul_left_comm]
  exact mul_mem (hc i) (hN' i _ (Finset.le_sup (Finset.mem_univ i)))

/- English proof (translation)
Establish `hT` using `trace_cont_lemma_3 l hcont`. Establish `hcpt : IsCompact (𝒪[K] : Set K)`. Establish `h : CompactSpace 𝒪[K]` using `inferInstance`. Conclude with `isCompact_iff_compactSpace.2 h`. Take `⟨C, hC⟩` from `hcpt.exists_bound_of_continuousOn hT.continuousOn`.

Establish `hl1 : ‖(l : ℚ_[l])‖ < 1` using `(by first`. Consider the case `exact Padic.norm_p_lt_one`. Consider the case `(rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))`. Establish `hpos : (0 : ℝ) < max C 1` using `lt_of_lt_of_le one_pos (le_max_right C 1)`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (inv_pos.2 hpos) hl1`.

Use `⟨algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ n), ?_, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]`. Conclude with `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Rewrite using `[tr_alg_mul, norm_mul, norm_pow]`. Establish `h1 : ‖Algebra.trace ℚ_[l] K (b : K)‖ ≤ max C 1` using `(hC b b.2).trans (le_max_left _ _)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_ne_zero (hcont : Continuous (algebraMap ℚ_[l] K)) : ∃ x : K, x ≠ 0 ∧ P l x := by
  have hT := trace_cont_lemma_3 l hcont
  have hcpt : IsCompact (𝒪[K] : Set K) := by
    have h : CompactSpace 𝒪[K] := inferInstance
    exact isCompact_iff_compactSpace.2 h
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn hT.continuousOn
  have hl1 : ‖(l : ℚ_[l])‖ < 1 := (by first
      | exact Padic.norm_p_lt_one
      | (rw [Padic.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)))
  have hpos : (0 : ℝ) < max C 1 := lt_of_lt_of_le one_pos (le_max_right C 1)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hl1
  refine ⟨algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ n), ?_, fun b => ?_⟩
  · rw [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  · rw [tr_alg_mul, norm_mul, norm_pow]
    have h1 : ‖Algebra.trace ℚ_[l] K (b : K)‖ ≤ max C 1 := (hC b b.2).trans (le_max_left _ _)
    calc ‖(l : ℚ_[l])‖ ^ n * ‖Algebra.trace ℚ_[l] K (b : K)‖
        ≤ ‖(l : ℚ_[l])‖ ^ n * max C 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (max C 1)⁻¹ * max C 1 := mul_le_mul_of_nonneg_right hn.le hpos.le
      _ = 1 := inv_mul_cancel₀ hpos.ne'

end

/- English proof (translation)
Take `⟨m, hm⟩` from `bound_lemma_8 l hcont`. Take `⟨x0, hx0, hPx0⟩` from `exists_ne_zero l hcont`. Use `set t : K := algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) with ht`. Establish `ht0 : t ≠ 0`. Rewrite using `[ht, Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]`.

Conclude with `pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)`. Set `I : Ideal 𝒪[K]` to `{ carrier := {c | P l ((c : K) * t⁻¹)} add_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Use `push_cast`. Rewrite using `[add_mul]`.

Conclude with `P_add_mem l ha hb`. Use the proof step `zero_mem' := by`. Simplify using `only [Set.mem_setOf_eq]`. Introduce `b`. Simplify using the standard rewrite rules.

Use the proof step `smul_mem' := fun c a ha => by`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul] at *`. Establish `h` using `mul_mem_dual₂ l ha c`. Establish `e : ((c * a : 𝒪[K]) : K) * t⁻¹ = (a : K) * t⁻¹ * (c : K)`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `h }`. Take `⟨g0, hg0⟩` from `Submodule.IsPrincipal.principal I`. Establish `hmem : ∀ c : 𝒪[K], c ∈ I ↔ P l ((c : K) * t⁻¹)` using `fun c => Iff.rfl`.

Establish `hspan : ∀ c : 𝒪[K], c ∈ I ↔ ∃ r : 𝒪[K], r * g0 = c` using `fun c => by`. Rewrite using `[hg0, Submodule.mem_span_singleton]`. Both sides reduce to the same expression. Establish `hc0 : (⟨t * x0, hm x0 hPx0⟩ : 𝒪[K]) ∈ I`. Rewrite using `[hmem]`.

Establish `e : t * x0 * t⁻¹ = x0` using `by field_simp`. Simplify `hPx0` using `only [e]`. Establish `hg0I : g0 ∈ I` using `(hspan g0).2 ⟨1, one_mul _⟩`. Establish `hg0ne : (g0 : K) ≠ 0`. Introduce `h`.

Take `⟨r, hr⟩` from `(hspan _).1 hc0`. Use `congrArg (fun u : 𝒪[K] => (u : K)) hr` as an intermediate fact. Simplify using `only [Subring.coe_mul, h, mul_zero] at this`. Conclude with `mul_ne_zero ht0 hx0 this.symm`. Use `set g : K := (g0 : K) * t⁻¹ with hg`.

Establish `hPg : P l g` using `(hmem g0).1 hg0I`. Establish `hgne : g ≠ 0` using `mul_ne_zero hg0ne (inv_ne_zero ht0)`. Use `⟨g⁻¹, inv_ne_zero hgne, fun a => ?_⟩` and prove the remaining obligations. Simplify using `only [inv_inv]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `hPa : P l (a * g)` using `fun b => by`. Establish `e : a * g * (b : K) = a * (b : K) * g` using `by ring`. Rewrite using `[e]`. Conclude with `h b`.

Establish `hc : (⟨t * (a * g), hm _ hPa⟩ : 𝒪[K]) ∈ I`. Rewrite using `[hmem]`. Establish `e : t * (a * g) * t⁻¹ = a * g` using `by field_simp`. Simplify `hPa` using `only [e]`. Take `⟨r, hr⟩` from `(hspan _).1 hc`.

Establish `h2` using `congrArg (fun u : 𝒪[K] => (u : K)) hr`. Simplify using `only [Subring.coe_mul] at h2`. Establish `h3 : (r : K) = a`. Establish `e : t * (a * g) = a * (g0 : K)`. Rewrite using `[hg]`.

Clear the denominators using the available nonvanishing facts. Rewrite `h2` using `[e]`. Conclude with `mul_right_cancel₀ hg0ne h2`. Rewrite using `[← h3]`. Conclude with `r.2`.

Introduce `ha b`. Establish `h` using `mul_mem_dual₂ l hPg ⟨a, ha⟩ b`. Establish `e : a * (b : K) * g = g * a * (b : K)` using `by ring`. Rewrite using `[e]`. Conclude with `h`.
-/
private theorem main_lemma_9 {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (l : ℕ) [Fact l.Prime] [Algebra ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (hcont : Continuous (algebraMap ℚ_[l] K)) :
    ∃ d : K, d ≠ 0 ∧ ∀ a : K,
      (∀ b : 𝒪[K], ‖Algebra.trace ℚ_[l] K (a * (b : K) * d⁻¹)‖ ≤ 1) ↔ a ∈ 𝒪[K] := by
  classical
  obtain ⟨m, hm⟩ := bound_lemma_8 l hcont
  obtain ⟨x0, hx0, hPx0⟩ := exists_ne_zero l hcont
  set t : K := algebraMap ℚ_[l] K ((l : ℚ_[l]) ^ m) with ht
  have ht0 : t ≠ 0 := by
    rw [ht, Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] K).injective]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  let I : Ideal 𝒪[K] :=
    { carrier := {c | P l ((c : K) * t⁻¹)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        push_cast
        rw [add_mul]
        exact P_add_mem l ha hb
      zero_mem' := by
        simp only [Set.mem_setOf_eq]
        intro b
        simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at *
        have h := mul_mem_dual₂ l ha c
        have e : ((c * a : 𝒪[K]) : K) * t⁻¹ = (a : K) * t⁻¹ * (c : K) := by
          push_cast
          ring
        rw [e]
        exact h }
  obtain ⟨g0, hg0⟩ := Submodule.IsPrincipal.principal I
  have hmem : ∀ c : 𝒪[K], c ∈ I ↔ P l ((c : K) * t⁻¹) := fun c => Iff.rfl
  have hspan : ∀ c : 𝒪[K], c ∈ I ↔ ∃ r : 𝒪[K], r * g0 = c := fun c => by
    rw [hg0, Submodule.mem_span_singleton]
    rfl
  have hc0 : (⟨t * x0, hm x0 hPx0⟩ : 𝒪[K]) ∈ I := by
    rw [hmem]
    have e : t * x0 * t⁻¹ = x0 := by field_simp
    simpa only [e] using hPx0
  have hg0I : g0 ∈ I := (hspan g0).2 ⟨1, one_mul _⟩
  have hg0ne : (g0 : K) ≠ 0 := by
    intro h
    obtain ⟨r, hr⟩ := (hspan _).1 hc0
    have := congrArg (fun u : 𝒪[K] => (u : K)) hr
    simp only [Subring.coe_mul, h, mul_zero] at this
    exact mul_ne_zero ht0 hx0 this.symm
  set g : K := (g0 : K) * t⁻¹ with hg
  have hPg : P l g := (hmem g0).1 hg0I
  have hgne : g ≠ 0 := mul_ne_zero hg0ne (inv_ne_zero ht0)
  refine ⟨g⁻¹, inv_ne_zero hgne, fun a => ?_⟩
  simp only [inv_inv]
  constructor
  · intro h
    have hPa : P l (a * g) := fun b => by
      have e : a * g * (b : K) = a * (b : K) * g := by ring
      rw [e]
      exact h b
    have hc : (⟨t * (a * g), hm _ hPa⟩ : 𝒪[K]) ∈ I := by
      rw [hmem]
      have e : t * (a * g) * t⁻¹ = a * g := by field_simp
      simpa only [e] using hPa
    obtain ⟨r, hr⟩ := (hspan _).1 hc
    have h2 := congrArg (fun u : 𝒪[K] => (u : K)) hr
    simp only [Subring.coe_mul] at h2
    have h3 : (r : K) = a := by
      have e : t * (a * g) = a * (g0 : K) := by
        rw [hg]
        field_simp
      rw [e] at h2
      exact mul_right_cancel₀ hg0ne h2
    rw [← h3]
    exact r.2
  · intro ha b
    have h := mul_mem_dual₂ l hPg ⟨a, ha⟩ b
    have e : a * (b : K) * g = g * a * (b : K) := by ring
    rw [e]
    exact h

/- English proof (translation)
Introduce `K _ _ _ l _ _ hK _ hcont hfin`. Use `haveI := hK`. Use `haveI := hfin`. Conclude with `main_lemma_9 l hcont`.
-/
theorem existsDifferentGenerator : FpDual := by
  intro K _ _ _ l _ _ hK _ hcont hfin
  haveI := hK
  haveI := hfin
  exact main_lemma_9 l hcont

end PI.LocDualGen.FpD
