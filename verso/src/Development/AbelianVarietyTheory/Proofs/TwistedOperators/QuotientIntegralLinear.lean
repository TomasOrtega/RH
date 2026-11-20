import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx Topology
open scoped Pointwise

namespace GlobalTheory.RootEx.QuotLinear

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}

/- English proof (translation)
Take `⟨_, _⟩` from `GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Establish `e : (N k n c p : Set (GL (n ⊕ Fin c) k)) = ⋂ r, ⋂ s, ⋂ (_ : lev p s ≤ lev p r), {g : GL (n ⊕ Fin c) k | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s}`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, Radical.mem_N_iff, Set.mem_iInter, Set.mem_setOf_eq]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Use `isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const` and prove the remaining obligations. Use `Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)` as an intermediate fact. Use `fun_prop`.
-/
theorem isClosed_N : IsClosed (N k n c p : Set (GL (n ⊕ Fin c) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  have e : (N k n c p : Set (GL (n ⊕ Fin c) k)) = ⋂ r, ⋂ s, ⋂ (_ : lev p s ≤ lev p r),
      {g : GL (n ⊕ Fin c) k | g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s} := by
    ext g
    simp only [SetLike.mem_coe, Radical.mem_N_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rfl
  rw [e]
  refine isClosed_iInter fun r => isClosed_iInter fun s => isClosed_iInter fun _ =>
    isClosed_eq ?_ continuous_const
  have := Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  fun_prop

/- English proof (translation)
Rewrite using `[SplitFlip.isEmbedding_val_GL.continuous_iff]`. Express the relevant statement in the definitionally equal form `Continuous fun x : GL n k => (fromBlocks x.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)`. Conclude with `Continuous.matrix_fromBlocks Units.continuous_val continuous_const continuous_const continuous_const`.
-/
theorem continuous_embX : Continuous (embX c : GL n k → GL (n ⊕ Fin c) k) := by
  rw [SplitFlip.isEmbedding_val_GL.continuous_iff]
  change Continuous fun x : GL n k => (fromBlocks x.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  exact Continuous.matrix_fromBlocks Units.continuous_val continuous_const continuous_const continuous_const

/- English proof (translation)
Take `⟨_, _⟩` from `GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Set `φ : GL (n ⊕ Fin c) k → Matrix n n k × (Matrix n n k)ᵐᵒᵖ` to `fun g => (g.val.toBlocks₁₁, MulOpposite.op (g⁻¹).val.toBlocks₁₁)`. Establish `hb : Continuous fun M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => M.toBlocks₁₁` using `continuous_matrix fun i j => continuous_id.matrix_elem _ _`. Establish `hφ : Continuous φ` using `(hb.comp Units.continuous_val).prodMk (MulOpposite.continuous_op.comp (hb.comp Units.continuous_coe_inv))`. Establish `hA` using `(Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hK.image hφ)`.

Establish `hB` using `(isClosed_N (k := k) (n := n) (c := c) (p := p)).isClosedEmbedding_subtypeVal.isCompact_preimage ((hA.image (continuous_embX (c := c))).inv.mul hK)`. Use `⟨_, _, hA, hB, fun x u h => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ (Units.embedProduct (Matrix n n k)) ⁻¹' (φ '' K)`. Use `⟨_, h, ?_⟩` and prove the remaining obligations. Establish `e : (embX c x * (u : GL (n ⊕ Fin c) k))⁻¹ = embX c x⁻¹ * (embX c x * (u : GL (n ⊕ Fin c) k)⁻¹ * (embX c x)⁻¹)`.

Rewrite using `[map_inv]`. Use `group`. Simplify using `only [φ]`. Rewrite using `[e, Radical.toBlocks₁₁_embX_mul x u.2, Radical.toBlocks₁₁_embX_mul x⁻¹ (Radical.conj_mem x (inv_mem u.2))]`. Both sides reduce to the same expression.

Use `⟨hx, ?_⟩` and prove the remaining obligations. Use `⟨(embX c x)⁻¹, ?_, _, h, by simp⟩` and prove the remaining obligations. Rewrite using `[Set.mem_inv, inv_inv]`. Conclude with `⟨x, hx, rfl⟩`.
-/
theorem exists_compact_prod {K : Set (GL (n ⊕ Fin c) k)} (hK : IsCompact K) :
    ∃ (A : Set (GL n k)) (B : Set (N k n c p)), IsCompact A ∧ IsCompact B ∧
      ∀ (x : GL n k) (u : N k n c p), embX c x * (u : GL (n ⊕ Fin c) k) ∈ K → x ∈ A ∧ u ∈ B := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  let φ : GL (n ⊕ Fin c) k → Matrix n n k × (Matrix n n k)ᵐᵒᵖ :=
    fun g => (g.val.toBlocks₁₁, MulOpposite.op (g⁻¹).val.toBlocks₁₁)
  have hb : Continuous fun M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k => M.toBlocks₁₁ :=
    continuous_matrix fun i j => continuous_id.matrix_elem _ _
  have hφ : Continuous φ :=
    (hb.comp Units.continuous_val).prodMk
      (MulOpposite.continuous_op.comp (hb.comp Units.continuous_coe_inv))
  have hA := (Units.isClosedEmbedding_embedProduct (α := Matrix n n k)).isCompact_preimage (hK.image hφ)
  have hB := (isClosed_N (k := k) (n := n) (c := c) (p := p)).isClosedEmbedding_subtypeVal.isCompact_preimage
    ((hA.image (continuous_embX (c := c))).inv.mul hK)
  refine ⟨_, _, hA, hB, fun x u h => ?_⟩
  have hx : x ∈ (Units.embedProduct (Matrix n n k)) ⁻¹' (φ '' K) := by
    refine ⟨_, h, ?_⟩
    have e : (embX c x * (u : GL (n ⊕ Fin c) k))⁻¹ =
        embX c x⁻¹ * (embX c x * (u : GL (n ⊕ Fin c) k)⁻¹ * (embX c x)⁻¹) := by
      rw [map_inv]; group
    simp only [φ]
    rw [e, Radical.toBlocks₁₁_embX_mul x u.2,
      Radical.toBlocks₁₁_embX_mul x⁻¹ (Radical.conj_mem x (inv_mem u.2))]
    rfl
  refine ⟨hx, ?_⟩
  refine ⟨(embX c x)⁻¹, ?_, _, h, by simp⟩
  rw [Set.mem_inv, inv_inv]
  exact ⟨x, hx, rfl⟩

variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Take `⟨_, _⟩` from `GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Unfold `volN`. Rewrite using `[(Model.coord_embedding (k := k) (n := n) (c := c) p).1.comap_apply]`. Use `(hK.image ?_).measure_lt_top` and prove the remaining obligations.

Use `Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)` as an intermediate fact. Use `fun_prop`.
-/
theorem finiteOnCompacts_volN (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsFiniteMeasureOnCompacts (volN ν n c p) := by
  classical
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  refine ⟨fun K hK => ?_⟩
  unfold volN
  rw [(Model.coord_embedding (k := k) (n := n) (c := c) p).1.comap_apply]
  refine (hK.image ?_).measure_lt_top
  have := Units.continuous_val (M := Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)
  fun_prop

/- English proof (translation)
Use `haveI := finiteOnCompacts_volN (n := n) (c := c) (p := p) ν`. Use `haveI : LocallyCompactSpace (N k n c p) := (isClosed_N (k := k) (n := n) (c := c) (p := p)).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : IsLocallyFiniteMeasure (volN ν n c p) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts`. Use `haveI : SigmaFinite (volN ν n c p) := sigmaFinite_of_locallyFinite`.

Establish `hK : IsCompact ((fun g => g * h⁻¹) '' tsupport F)` using `hF.2.isCompact.image (by fun_prop)`. Take `⟨A, B, hA, hB, hAB⟩` from `exists_compact_prod (p := p) hK`. Establish `hz : ∀ (x : GL n k) (u : N k n c p), ¬ (x ∈ A ∧ u ∈ B) → F (embX c x * (u : GL (n ⊕ Fin c) k) * h) = 0` using `fun x u hn => by`. Assume the negation of the conclusion as `h0`. Conclude with `hn (hAB x u ⟨_, subset_tsupport _ h0, by simp⟩)`.

Establish `hc : Continuous fun z : GL n k × N k n c p => F (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) * h)` using `hF.1.continuous.comp (((continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul continuous_const)`. Use `⟨fun x => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hc.comp (Continuous.prodMk_right x)).integrable_of_hasCompactSupport (HasCompactSupport.intro hB fun u hu => hz x u fun h => hu h.2)`. Establish `hi : Integrable (fun z : GL n k × N k n c p => F (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) * h)) (μX.prod (volN ν n c p))` using `hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (hA.prod hB) fun z hz' => hz z.1 z.2 hz')`. Conclude with `hi.integral_prod_left`.
-/
theorem integrable_average (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure]
    {F : GL (n ⊕ Fin c) k → ℂ} (hF : F ∈ SB (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k) :
    (∀ x : GL n k, Integrable (fun u : N k n c p => F (embX c x * (u : GL (n ⊕ Fin c) k) * h)) (volN ν n c p)) ∧
    Integrable (fun x : GL n k =>
      ∫ u : N k n c p, F (embX c x * (u : GL (n ⊕ Fin c) k) * h) ∂(volN ν n c p)) μX := by
  haveI := finiteOnCompacts_volN (n := n) (c := c) (p := p) ν
  haveI : LocallyCompactSpace (N k n c p) :=
    (isClosed_N (k := k) (n := n) (c := c) (p := p)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : IsLocallyFiniteMeasure (volN ν n c p) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SigmaFinite (volN ν n c p) := sigmaFinite_of_locallyFinite
  have hK : IsCompact ((fun g => g * h⁻¹) '' tsupport F) := hF.2.isCompact.image (by fun_prop)
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_compact_prod (p := p) hK
  have hz : ∀ (x : GL n k) (u : N k n c p), ¬ (x ∈ A ∧ u ∈ B) →
      F (embX c x * (u : GL (n ⊕ Fin c) k) * h) = 0 := fun x u hn => by
    by_contra h0
    exact hn (hAB x u ⟨_, subset_tsupport _ h0, by simp⟩)
  have hc : Continuous fun z : GL n k × N k n c p => F (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) * h) :=
    hF.1.continuous.comp (((continuous_embX.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul continuous_const)
  refine ⟨fun x => ?_, ?_⟩
  · exact (hc.comp (Continuous.prodMk_right x)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hB fun u hu => hz x u fun h => hu h.2)
  · have hi : Integrable (fun z : GL n k × N k n c p => F (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k) * h))
        (μX.prod (volN ν n c p)) :=
      hc.integrable_of_hasCompactSupport (HasCompactSupport.intro (hA.prod hB) fun z hz' => hz z.1 z.2 hz')
    exact hi.integral_prod_left

/- English proof (translation)
Introduce `k _ _ _ _ _ _ n _ _ c p _ _ ν _ μX _ μG _ f f' a z z' ⟨F, hF, h1, h2⟩ ⟨F', hF', h1', h2'⟩`. Use `⟨a • F + F', add_mem (Submodule.smul_mem _ a hF) hF', fun h => ?_, ?_⟩` and prove the remaining obligations. Take `⟨i1, i2⟩` from `integrable_average (p := p) ν μX hF h`. Take `⟨j1, j2⟩` from `integrable_average (p := p) ν μX hF' h`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[h1, h1', ← integral_const_mul, ← integral_add (i2.const_mul a) j2]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[integral_add ((i1 x).const_mul a) (j1 x), integral_const_mul]`. Establish `i : Integrable F μG` using `hF.1.continuous.integrable_of_hasCompactSupport hF.2`.

Establish `j : Integrable F' μG` using `hF'.1.continuous.integrable_of_hasCompactSupport hF'.2`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[integral_add (i.const_mul a) j, integral_const_mul, h2, h2']`.
-/
theorem isQuotInt_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (f f' : GL (n ⊕ Fin c) k → ℂ) (a z z' : ℂ), IsQuotInt ν μX μG p f z → IsQuotInt ν μX μG p f' z' → IsQuotInt ν μX μG p (fun h => a * f h + f' h) (a * z + z') := by
  intro k _ _ _ _ _ _ n _ _ c p _ _ ν _ μX _ μG _ f f' a z z' ⟨F, hF, h1, h2⟩ ⟨F', hF', h1', h2'⟩
  refine ⟨a • F + F', add_mem (Submodule.smul_mem _ a hF) hF', fun h => ?_, ?_⟩
  · obtain ⟨i1, i2⟩ := integrable_average (p := p) ν μX hF h
    obtain ⟨j1, j2⟩ := integrable_average (p := p) ν μX hF' h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h1, h1', ← integral_const_mul, ← integral_add (i2.const_mul a) j2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_add ((i1 x).const_mul a) (j1 x), integral_const_mul]
  · have i : Integrable F μG := hF.1.continuous.integrable_of_hasCompactSupport hF.2
    have j : Integrable F' μG := hF'.1.continuous.integrable_of_hasCompactSupport hF'.2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_add (i.const_mul a) j, integral_const_mul, h2, h2']

end GlobalTheory.RootEx.QuotLinear
