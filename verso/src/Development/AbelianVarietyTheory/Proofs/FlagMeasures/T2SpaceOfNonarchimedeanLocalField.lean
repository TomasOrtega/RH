import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIntegersLocalisationIffSumCmDataStatement
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors

namespace GlobalTheory.LocAtTopology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Use `letI : (Valued.v (R := k)).RankOne :=`. Use the proof step `{ hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding strictMono' := IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }`. Use `open scoped Valued in`.

Use `haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k`. Conclude with `secondCountable_of_proper`.
-/
theorem secondCountable_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact secondCountable_of_proper

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Use `infer_instance`.
-/
theorem t2Space_of_nonarchimedeanLocalField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  infer_instance

/- English proof (translation)
Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`. Conclude with `Valued.isOpen_integer k`.
-/
theorem isOpen_integer_localField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : IsOpen (𝒪[k] : Set k) := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  exact Valued.isOpen_integer k

/- English proof (translation)
Rewrite using `[← T.val, (valuation T.Fp).vle_iff_le]`.
-/
theorem val_le_iff (T : LocAt F E sig p) (x y : F) :
    valuation T.Fp (T.ιF x) ≤ valuation T.Fp (T.ιF y) ↔ p.valuation F x ≤ p.valuation F y := by
  rw [← T.val, (valuation T.Fp).vle_iff_le]

/- English proof (translation)
Use `haveI := T.lf`. Establish `hc' : valuation T.Fp c ≤ 1` using `hc`. Rewrite using `[mem_closure_iff_nhds]`. Introduce `U hU`. Take `⟨γ, hγ⟩` from `IsValuativeTopology.mem_nhds_iff'.1 hU`.

Take `⟨t, ht⟩` from `ValuativeRel.valuation_surjective (γ : ValueGroupWithZero T.Fp)`. Establish `hn : ∀ (y : T.Fp) (δ : (ValueGroupWithZero T.Fp)ˣ), {z : T.Fp | valuation T.Fp (z - y) < δ} ∈ nhds y` using `fun y δ => IsValuativeTopology.mem_nhds_iff'.2 ⟨δ, fun z hz => hz⟩`. Take `⟨b, hb⟩` from `T.dense.mem_nhds (hn t γ)`. Establish `hb' : valuation T.Fp (T.ιF b - t) < valuation T.Fp t` using `by rw [ht]; exact hb`. Establish `hbv : valuation T.Fp (T.ιF b) = γ`.

Rewrite using `[← ht]`. Conclude with `Valuation.map_eq_of_sub_lt _ hb'`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Simplify using `only [map_zero] at hbv`.

Conclude with `γ.ne_zero hbv.symm`. Take `⟨x, hx1, hx2⟩` from `T.dense.mem_nhds (Filter.inter_mem (hn c γ) (hn c 1))`. Establish `hx1' : valuation T.Fp (T.ιF x - c) < γ` using `hx1`. Establish `hx2' : valuation T.Fp (T.ιF x - c) < 1` using `by simpa using hx2`. Establish `hx : valuation T.Fp (T.ιF x) ≤ 1`.

Establish `: T.ιF x = (T.ιF x - c) + c` using `by ring`. Rewrite using `[this]`. Conclude with `(valuation T.Fp).map_add_le hx2'.le hc'`. Establish `hxF : p.valuation F x ≤ 1`. Establish `h` using `val_le_iff T x 1`.

Simplify using `only [map_one] at h`. Conclude with `h.1 hx`. Take `⟨a, ha⟩` from `p.exists_valuation_sub_lt_of_integer hxF (Units.mk0 (p.valuation F b) (by simpa using hb0))`. Use `⟨T.ιF (algebraMap (𝓞 F) F a), hγ ?_, a, rfl⟩` and prove the remaining obligations. Establish `ha' : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a - x)) < γ`.

Rewrite using `[← hbv, ← not_le, val_le_iff, not_le]`. Conclude with `ha`. Establish `: T.ιF (algebraMap (𝓞 F) F a) - c = T.ιF (algebraMap (𝓞 F) F a - x) + (T.ιF x - c)`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Express the relevant statement in the definitionally equal form `valuation T.Fp (_ - c) < γ`. Rewrite using `[this]`. Conclude with `(valuation T.Fp).map_add_lt ha' hx1'`.
-/
theorem mem_closure_int (T : LocAt F E sig p) (c : T.Fp) (hc : c ∈ 𝒪[T.Fp]) :
    c ∈ closure (Set.range fun a : 𝓞 F => T.ιF (algebraMap (𝓞 F) F a)) := by
  haveI := T.lf
  have hc' : valuation T.Fp c ≤ 1 := hc
  rw [mem_closure_iff_nhds]
  intro U hU
  obtain ⟨γ, hγ⟩ := IsValuativeTopology.mem_nhds_iff'.1 hU
  obtain ⟨t, ht⟩ := ValuativeRel.valuation_surjective (γ : ValueGroupWithZero T.Fp)
  have hn : ∀ (y : T.Fp) (δ : (ValueGroupWithZero T.Fp)ˣ),
      {z : T.Fp | valuation T.Fp (z - y) < δ} ∈ nhds y := fun y δ =>
    IsValuativeTopology.mem_nhds_iff'.2 ⟨δ, fun z hz => hz⟩
  obtain ⟨b, hb⟩ := T.dense.mem_nhds (hn t γ)
  have hb' : valuation T.Fp (T.ιF b - t) < valuation T.Fp t := by rw [ht]; exact hb
  have hbv : valuation T.Fp (T.ιF b) = γ := by
    rw [← ht]; exact Valuation.map_eq_of_sub_lt _ hb'
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hbv
    exact γ.ne_zero hbv.symm
  obtain ⟨x, hx1, hx2⟩ := T.dense.mem_nhds (Filter.inter_mem (hn c γ) (hn c 1))
  have hx1' : valuation T.Fp (T.ιF x - c) < γ := hx1
  have hx2' : valuation T.Fp (T.ιF x - c) < 1 := by simpa using hx2
  have hx : valuation T.Fp (T.ιF x) ≤ 1 := by
    have : T.ιF x = (T.ιF x - c) + c := by ring
    rw [this]
    exact (valuation T.Fp).map_add_le hx2'.le hc'
  have hxF : p.valuation F x ≤ 1 := by
    have h := val_le_iff T x 1
    simp only [map_one] at h
    exact h.1 hx
  obtain ⟨a, ha⟩ := p.exists_valuation_sub_lt_of_integer hxF
    (Units.mk0 (p.valuation F b) (by simpa using hb0))
  refine ⟨T.ιF (algebraMap (𝓞 F) F a), hγ ?_, a, rfl⟩
  have ha' : valuation T.Fp (T.ιF (algebraMap (𝓞 F) F a - x)) < γ := by
    rw [← hbv, ← not_le, val_le_iff, not_le]
    exact ha
  have : T.ιF (algebraMap (𝓞 F) F a) - c = T.ιF (algebraMap (𝓞 F) F a - x) + (T.ιF x - c) := by
    rw [map_sub]; ring
  change valuation T.Fp (_ - c) < γ
  rw [this]
  exact (valuation T.Fp).map_add_lt ha' hx1'

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc sig hsig p A`. Establish `hO` using `GlobalTheory.T.mem_integers_localisation_iff_sum_cmData hc sig hsig p A`. Use `haveI := A.lf`. Use `haveI := A.char0`. Use `haveI := A.free`.

Use `haveI := A.top`. Use `haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)`. Use `haveI : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)`. Use `haveI := secondCountable_localField A.Fp`. Use `haveI := t2Space_of_nonarchimedeanLocalField A.Fp`.

Use `haveI hR : IsTopologicalRing A.Ep := IsModuleTopology.isTopologicalRing A.Fp A.Ep`. Use `haveI : ContinuousSMul A.Fp A.Ep := IsModuleTopology.toContinuousSMul A.Fp A.Ep`. Establish `hcont : Continuous (algebraMap A.Fp A.Ep)` using `continuous_algebraMap _ _`. Set `b` to `Module.finBasis A.Fp A.Ep`. Set `h : A.Ep ≃ₜ (Fin (Module.finrank A.Fp A.Ep) → A.Fp)` to `{ toEquiv := b.equivFun.toEquiv continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }`.

Use `haveI hT2 : T2Space A.Ep := h.symm.t2Space`. Establish `hLC : LocallyCompactSpace A.Ep` using `h.isClosedEmbedding.locallyCompactSpace`. Establish `hSC : SecondCountableTopology A.Ep` using `h.secondCountableTopology`. Set `w` to `RingOfIntegers.basis E`. Set `L : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A.Fp) →ₗ[A.Fp] A.Ep` to `Fintype.linearCombination A.Fp (fun i => A.ιE (w i : E))`.

Establish `hL : ∀ c, L c = ∑ i, c i • A.ιE (w i : E)` using `fun c => Fintype.linearCombination_apply _ _ _`. Establish `hint : ∀ x : 𝓞 E, A.ιE (x : E) = L (fun i => (w.repr x i : A.Fp))`. Introduce `x`. Rewrite using `[hL]`. Use `conv_lhs => rw [← w.sum_repr x]`.

Simplify using `[Int.cast_smul_eq_zsmul]`. Establish `hsurj : Function.Surjective L`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← A.span, Submodule.span_le]`. Introduce and unpack `_ ⟨x, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨n, y, hn, hy⟩ : ∃ (n : ℤ) (y : 𝓞 E), n ≠ 0 ∧ (y : E) = n • x := by`.

Take `⟨n, hn, hi⟩` from `((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple`. Conclude with `⟨n, ⟨_, hi⟩, hn, rfl⟩`. Establish `h1 : A.ιE x = ((n : A.Fp)⁻¹) • A.ιE (y : E)`. Rewrite using `[hy, map_zsmul, ← Int.cast_smul_eq_zsmul A.Fp, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]`. Rewrite using `[h1, hint]`.

Conclude with `Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)`. Establish `hOeq : (A.O : Set A.Ep) = L '' (Set.univ.pi fun _ => (𝒪[A.Fp] : Set A.Fp))`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Take `⟨n, c, x, rfl⟩` from `(hO y).1 hy`. Use `⟨∑ j, (c j : A.Fp) • (fun i => (w.repr (x j) i : A.Fp)), ?_, ?_⟩` and prove the remaining obligations. Introduce `i _`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `Subring.sum_mem _ fun j _ => Subring.mul_mem _ (c j).2 (intCast_mem _ _)`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← hint, Algebra.smul_def]`. Introduce and unpack `⟨c, hc, rfl⟩`. Rewrite using `[hL]`.

Use `Subring.sum_mem _ fun i _ => (hO _).2 ⟨1, fun _ => ⟨c i, hc i trivial⟩, fun _ => w i, ?_⟩` and prove the remaining obligations. Simplify using `[Algebra.smul_def]`. Establish `hopen : IsOpen (A.O : Set A.Ep)`. Rewrite using `[hOeq]`. Conclude with `IsModuleTopology.isOpenMap_of_surjective hsurj _ (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integer_localField A.Fp)`.

Establish `hcomp : IsCompact (A.O : Set A.Ep)`. Rewrite using `[hOeq]`. Conclude with `(isCompact_univ_pi fun _ => isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[A.Fp]))).image (IsModuleTopology.continuous_of_linearMap L)`. Use `⟨hR, hT2, hLC, hSC, hopen, hcomp, ?_, A.ιE.injective, fun x hx => (IsUnit.mk0 x hx).map A.ιE, ?_⟩` and prove the remaining obligations. Set `S : Subring A.Ep` to `A.ιE.range.topologicalClosure`.

Establish `hS : ∀ a : A.Fp, algebraMap A.Fp A.Ep a ∈ S`. Introduce `a`. Use `map_mem_closure (t := Set.range A.ιE) hcont (A.dense a) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨r, rfl⟩`. Conclude with `⟨_, A.compat r⟩`.

Introduce `y`. Establish `hy : y ∈ Submodule.span A.Fp (Set.range A.ιE)` using `by rw [A.span]; trivial`. Express the relevant statement in the definitionally equal form `y ∈ S`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact subset_closure hx`.

Consider the case `zero => exact S.zero_mem`. Consider the case `add x y _ _ hx hy => exact S.add_mem hx hy`. Consider the case `smul a x _ hx => rw [Algebra.smul_def]`. Conclude with `S.mul_mem (hS a) hx`. Apply `le_antisymm` to reduce the goal to its premises.

Use `closure_minimal ?_ hcomp.isClosed` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `(hO _).2 ⟨1, fun _ => 1, fun _ => x, by simp⟩`. Set `S : Subring A.Ep` to `(A.ιE.comp (algebraMap (𝓞 E) E)).range.topologicalClosure`. Introduce `y hy`.

Take `⟨n, c, x, rfl⟩` from `(hO y).1 hy`. Express the relevant statement in the definitionally equal form `_ ∈ S`. Use `S.sum_mem fun j _ => S.mul_mem ?_ (subset_closure ⟨x j, rfl⟩)` and prove the remaining obligations. Use `map_mem_closure (t := Set.range (A.ιE.comp (algebraMap (𝓞 E) E))) hcont (mem_closure_int A _ (c j).2) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨r, rfl⟩`.

Use `⟨algebraMap (𝓞 F) (𝓞 E) r, ?_⟩` and prove the remaining obligations. Rewrite using `[← A.compat]`. Both sides reduce to the same expression.
-/
theorem locAt_topology : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], Formalism.BasicNotions.CMData F E → ∀ (sig : E →ₐ[F] E), (∀ x, sig x = star x) → ∀ (p : HeightOneSpectrum (𝓞 F)) (A : LocAt F E sig p), IsTopologicalRing A.Ep ∧ T2Space A.Ep ∧ LocallyCompactSpace A.Ep ∧ SecondCountableTopology A.Ep ∧ IsOpen (A.O : Set A.Ep) ∧ IsCompact (A.O : Set A.Ep) ∧ DenseRange A.ιE ∧ Function.Injective A.ιE ∧ (∀ x : E, x ≠ 0 → IsUnit (A.ιE x)) ∧ closure (Set.range fun x : 𝓞 E => A.ιE (x : E)) = (A.O : Set A.Ep) := by
  intro F E _ _ _ _ _ _ hc sig hsig p A
  have hO := GlobalTheory.T.mem_integers_localisation_iff_sum_cmData hc sig hsig p A
  haveI := A.lf
  haveI := A.char0
  haveI := A.free
  haveI := A.top
  haveI : Module.Finite A.Fp A.Ep := Module.finite_of_finrank_pos (by rw [A.rank]; norm_num)
  haveI : Nontrivial A.Ep := Module.nontrivial_of_finrank_pos (R := A.Fp) (by rw [A.rank]; norm_num)
  haveI := secondCountable_localField A.Fp
  haveI := t2Space_of_nonarchimedeanLocalField A.Fp
  haveI hR : IsTopologicalRing A.Ep := IsModuleTopology.isTopologicalRing A.Fp A.Ep
  haveI : ContinuousSMul A.Fp A.Ep := IsModuleTopology.toContinuousSMul A.Fp A.Ep
  have hcont : Continuous (algebraMap A.Fp A.Ep) := continuous_algebraMap _ _
  let b := Module.finBasis A.Fp A.Ep
  let h : A.Ep ≃ₜ (Fin (Module.finrank A.Fp A.Ep) → A.Fp) :=
    { toEquiv := b.equivFun.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap }
  haveI hT2 : T2Space A.Ep := h.symm.t2Space
  have hLC : LocallyCompactSpace A.Ep := h.isClosedEmbedding.locallyCompactSpace
  have hSC : SecondCountableTopology A.Ep := h.secondCountableTopology
  let w := RingOfIntegers.basis E
  let L : (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A.Fp) →ₗ[A.Fp] A.Ep :=
    Fintype.linearCombination A.Fp (fun i => A.ιE (w i : E))
  have hL : ∀ c, L c = ∑ i, c i • A.ιE (w i : E) := fun c => Fintype.linearCombination_apply _ _ _
  have hint : ∀ x : 𝓞 E, A.ιE (x : E) = L (fun i => (w.repr x i : A.Fp)) := by
    intro x
    rw [hL]
    conv_lhs => rw [← w.sum_repr x]
    simp [Int.cast_smul_eq_zsmul]
  have hsurj : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← A.span, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    obtain ⟨n, y, hn, hy⟩ : ∃ (n : ℤ) (y : 𝓞 E), n ≠ 0 ∧ (y : E) = n • x := by
      obtain ⟨n, hn, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
        (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x)).exists_integral_multiple
      exact ⟨n, ⟨_, hi⟩, hn, rfl⟩
    have h1 : A.ιE x = ((n : A.Fp)⁻¹) • A.ιE (y : E) := by
      rw [hy, map_zsmul, ← Int.cast_smul_eq_zsmul A.Fp, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
    rw [h1, hint]
    exact Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _)
  have hOeq : (A.O : Set A.Ep) = L '' (Set.univ.pi fun _ => (𝒪[A.Fp] : Set A.Fp)) := by
    ext y
    constructor
    · intro hy
      obtain ⟨n, c, x, rfl⟩ := (hO y).1 hy
      refine ⟨∑ j, (c j : A.Fp) • (fun i => (w.repr (x j) i : A.Fp)), ?_, ?_⟩
      · intro i _
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (c j).2 (intCast_mem _ _)
      · rw [map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, ← hint, Algebra.smul_def]
    · rintro ⟨c, hc, rfl⟩
      rw [hL]
      refine Subring.sum_mem _ fun i _ => (hO _).2 ⟨1, fun _ => ⟨c i, hc i trivial⟩, fun _ => w i, ?_⟩
      simp [Algebra.smul_def]
  have hopen : IsOpen (A.O : Set A.Ep) := by
    rw [hOeq]
    exact IsModuleTopology.isOpenMap_of_surjective hsurj _
      (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integer_localField A.Fp)
  have hcomp : IsCompact (A.O : Set A.Ep) := by
    rw [hOeq]
    exact (isCompact_univ_pi fun _ =>
      isCompact_iff_compactSpace.2 (inferInstanceAs (CompactSpace 𝒪[A.Fp]))).image
      (IsModuleTopology.continuous_of_linearMap L)
  refine ⟨hR, hT2, hLC, hSC, hopen, hcomp, ?_, A.ιE.injective,
    fun x hx => (IsUnit.mk0 x hx).map A.ιE, ?_⟩
  · let S : Subring A.Ep := A.ιE.range.topologicalClosure
    have hS : ∀ a : A.Fp, algebraMap A.Fp A.Ep a ∈ S := by
      intro a
      refine map_mem_closure (t := Set.range A.ιE) hcont (A.dense a) ?_
      rintro _ ⟨r, rfl⟩
      exact ⟨_, A.compat r⟩
    intro y
    have hy : y ∈ Submodule.span A.Fp (Set.range A.ιE) := by rw [A.span]; trivial
    change y ∈ S
    induction hy using Submodule.span_induction with
    | mem x hx => exact subset_closure hx
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul a x _ hx => rw [Algebra.smul_def]; exact S.mul_mem (hS a) hx
  · apply le_antisymm
    · refine closure_minimal ?_ hcomp.isClosed
      rintro _ ⟨x, rfl⟩
      exact (hO _).2 ⟨1, fun _ => 1, fun _ => x, by simp⟩
    · let S : Subring A.Ep := (A.ιE.comp (algebraMap (𝓞 E) E)).range.topologicalClosure
      intro y hy
      obtain ⟨n, c, x, rfl⟩ := (hO y).1 hy
      change _ ∈ S
      refine S.sum_mem fun j _ => S.mul_mem ?_ (subset_closure ⟨x j, rfl⟩)
      refine map_mem_closure (t := Set.range (A.ιE.comp (algebraMap (𝓞 E) E))) hcont
        (mem_closure_int A _ (c j).2) ?_
      rintro _ ⟨r, rfl⟩
      refine ⟨algebraMap (𝓞 F) (𝓞 E) r, ?_⟩
      rw [← A.compat]
      rfl

end GlobalTheory.LocAtTopology
