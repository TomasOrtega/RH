import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice

noncomputable section

open MeasureTheory Measure Set Filter Topology
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.CovariantRepresentation

section Conj

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `hinv : Measurable (fun x : G => x⁻¹)` using `measurable_inv`. Establish `hr : ν.map (fun x => x * n) = ν`. Establish `e : (fun x : G => x * n) = (fun x => x⁻¹) ∘ ((fun x => n⁻¹ * x) ∘ (fun x => x⁻¹))`. Use function extensionality and compare the values at `x`. Simplify using `[mul_inv_rev]`.

Rewrite using `[e, ← map_map hinv ((measurable_const_mul _).comp hinv), ← map_map (measurable_const_mul _) hinv, hi, hl _ (R.inv_mem hn), hi]`. Establish `e : (fun x : G => n⁻¹ * x * n) = (fun x => x * n) ∘ (fun x => n⁻¹ * x)` using `rfl`. Rewrite using `[e, ← map_map (measurable_mul_const n) (measurable_const_mul _), hl _ (R.inv_mem hn), hr]`.
-/
theorem map_conj_of_mem (R : Subgroup G) (ν : Measure G) (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν)
    (hi : ν.map (fun x => x⁻¹) = ν) {n : G} (hn : n ∈ R) : ν.map (fun x => n⁻¹ * x * n) = ν := by
  have hinv : Measurable (fun x : G => x⁻¹) := measurable_inv
  have hr : ν.map (fun x => x * n) = ν := by
    have e : (fun x : G => x * n) = (fun x => x⁻¹) ∘ ((fun x => n⁻¹ * x) ∘ (fun x => x⁻¹)) := by
      funext x; simp [mul_inv_rev]
    rw [e, ← map_map hinv ((measurable_const_mul _).comp hinv), ← map_map (measurable_const_mul _) hinv, hi,
      hl _ (R.inv_mem hn), hi]
  have e : (fun x : G => n⁻¹ * x * n) = (fun x => x * n) ∘ (fun x => n⁻¹ * x) := rfl
  rw [e, ← map_map (measurable_mul_const n) (measurable_const_mul _), hl _ (R.inv_mem hn), hr]

/- English proof (translation)
Take `⟨C, hCc, hCm⟩` from `hC`. Establish `hce : IsClosedEmbedding (Subtype.val : R → G)` using `hR.isClosedEmbedding_subtypeVal`. Use `haveI : LocallyCompactSpace R := hce.locallyCompactSpace`. Use `haveI : BorelSpace R := Subtype.borelSpace _`. Use `haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology _`.

Establish `hemb : MeasurableEmbedding (Subtype.val : R → G)` using `MeasurableEmbedding.subtype_coe hR.measurableSet`. Use `set μ : Measure R := ν.comap Subtype.val with hμ`. Establish `hν : μ.map Subtype.val = ν`. Rewrite using `[hemb.map_comap, Subtype.range_coe]`. Use `Measure.restrict_eq_self_of_ae_mem ?_` and prove the remaining obligations.

Rewrite using `[ae_iff]`. Conclude with `hc`. Establish `hcm : ∀ μ' : Measure R, (μ'.map Subtype.val).comap Subtype.val = μ'` using `fun μ' => hemb.comap_map μ'`. Use `haveI : μ.IsMulLeftInvariant := ⟨fun r => by`. Establish `h1 : (μ.map (r * ·)).map Subtype.val = μ.map Subtype.val`.

Rewrite using `[map_map hemb.measurable (measurable_const_mul r)]`. Establish `e : (Subtype.val ∘ (r * ·) : R → G) = (fun x : G => (r : G) * x) ∘ Subtype.val` using `rfl`. Rewrite using `[e, ← map_map (measurable_const_mul (r : G)) hemb.measurable, hν, hl _ r.2]`. Rewrite using `[← hcm (μ.map (r * ·)), h1, hcm]⟩`. Use `haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hKc => by`.

Rewrite using `[hμ, hemb.comap_apply]`. Conclude with `hK _ (hKc.image continuous_subtype_val)⟩`. Use `haveI : NeZero μ := ⟨fun h => h0 (by rw [← hν, h, Measure.map_zero])⟩`. Use `haveI : IsOpenPosMeasure μ := by`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, μ (compactCovering R n) ≠ 0 := by`.

Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Apply `NeZero.ne μ` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]`. Conclude with `measure_iUnion_null hall`.

Conclude with `isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering R n) hn`. Use `haveI : IsHaarMeasure μ := { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance, toIsOpenPosMeasure := inferInstance }`. Set `α : R ≃ₜ* R` to `{ toFun := fun r => ⟨k⁻¹ * r * k, (hk r).1 r.2⟩ invFun := fun r => ⟨k * r * k⁻¹, (hk _).2 (by simpa [mul_assoc] using r.2)⟩ left_inv := fun r => Subtype.ext (by simp [mul_assoc]) right_inv := fun r => Subtype.ext (by simp [mul_assoc]) map_mul' := fun a b => Subtype.ext (by simp [ …`. Establish `hit : ∀ (n : ℕ) (x : R), (((⇑α)^[n] x : R) : G) = k ^ (-(n : ℤ)) * x * k ^ (n : ℤ)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `x`.

Rewrite using `[Function.iterate_succ_apply']`. Express the relevant statement in the definitionally equal form `k⁻¹ * (((⇑α)^[n] x : R) : G) * k = _`. Rewrite using `[ih]`. Use `push_cast`. Use `group`.

Establish `hit' : ∀ (n : ℕ) (x : R), (((⇑α.symm)^[n] x : R) : G) = k ^ (n : ℤ) * x * k ^ (-(n : ℤ))`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `x`. Rewrite using `[Function.iterate_succ_apply']`. Express the relevant statement in the definitionally equal form `k * (((⇑α.symm)^[n] x : R) : G) * k⁻¹ = _`. Rewrite using `[ih]`.

Use `push_cast`. Use `group`. Take `⟨V, hV, hV1⟩` from `exists_compact_mem_nhds (1 : R)`. Establish `hL : IsCompact (Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) : Set R)` using `hce.isCompact_preimage ((hCc.mul (hV.image continuous_subtype_val)).mul hCc)`. Establish `hb : ∀ n : ℕ, (⇑α)^[n] '' V ⊆ Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) ∧ (⇑α.symm)^[n] '' V ⊆ Subtype.val ⁻¹' (C * (Subtype.val '' V) * C)`.

Introduce `n`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `_ ⟨x, hx, rfl⟩ show (((⇑α)^[n] x : R) : G) ∈ C * (Subtype.val '' V) * C`. Rewrite using `[hit n x]`. Conclude with `Set.mul_mem_mul (Set.mul_mem_mul (hCm _) ⟨x, hx, rfl⟩) (hCm _)`.

Introduce and unpack `_ ⟨x, hx, rfl⟩ show (((⇑α.symm)^[n] x : R) : G) ∈ C * (Subtype.val '' V) * C`. Rewrite using `[hit' n x]`. Conclude with `Set.mul_mem_mul (Set.mul_mem_mul (hCm _) ⟨x, hx, rfl⟩) (hCm _)`. Establish `hμα : μ.map α = μ` using `haar_map_equiv_of_bounded μ α hV hV1 hL hb`. Establish `hmc : Measurable (fun x : G => k⁻¹ * x * k)` using `(measurable_const_mul _).mul_const _`.

Establish `hma : Measurable (⇑α)` using `α.continuous.measurable`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_map hmc hemb.measurable, map_map hemb.measurable hma]`. Both sides reduce to the same expression. Use `_ = ν := by rw [hμα, hν]`.
-/
theorem map_conj_of_bounded (R : Subgroup G) (hR : IsClosed (R : Set G)) (ν : Measure G) (h0 : ν ≠ 0)
    (hc : ν (R : Set G)ᶜ = 0) (hK : ∀ K : Set G, IsCompact K → ν K < ⊤)
    (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν) (k : G) (hk : ∀ r, r ∈ R ↔ k⁻¹ * r * k ∈ R)
    (hC : ∃ C : Set G, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C) : ν.map (fun x => k⁻¹ * x * k) = ν := by
  obtain ⟨C, hCc, hCm⟩ := hC
  have hce : IsClosedEmbedding (Subtype.val : R → G) := hR.isClosedEmbedding_subtypeVal
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : BorelSpace R := Subtype.borelSpace _
  haveI : SecondCountableTopology R := TopologicalSpace.Subtype.secondCountableTopology _
  have hemb : MeasurableEmbedding (Subtype.val : R → G) := MeasurableEmbedding.subtype_coe hR.measurableSet
  set μ : Measure R := ν.comap Subtype.val with hμ
  have hν : μ.map Subtype.val = ν := by
    rw [hemb.map_comap, Subtype.range_coe]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    rw [ae_iff]
    exact hc
  have hcm : ∀ μ' : Measure R, (μ'.map Subtype.val).comap Subtype.val = μ' := fun μ' => hemb.comap_map μ'
  haveI : μ.IsMulLeftInvariant := ⟨fun r => by
    have h1 : (μ.map (r * ·)).map Subtype.val = μ.map Subtype.val := by
      rw [map_map hemb.measurable (measurable_const_mul r)]
      have e : (Subtype.val ∘ (r * ·) : R → G) = (fun x : G => (r : G) * x) ∘ Subtype.val := rfl
      rw [e, ← map_map (measurable_const_mul (r : G)) hemb.measurable, hν, hl _ r.2]
    rw [← hcm (μ.map (r * ·)), h1, hcm]⟩
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hKc => by
    rw [hμ, hemb.comap_apply]
    exact hK _ (hKc.image continuous_subtype_val)⟩
  haveI : NeZero μ := ⟨fun h => h0 (by rw [← hν, h, Measure.map_zero])⟩
  haveI : IsOpenPosMeasure μ := by
    obtain ⟨n, hn⟩ : ∃ n, μ (compactCovering R n) ≠ 0 := by
      by_contra hall
      push Not at hall
      apply NeZero.ne μ
      rw [← Measure.measure_univ_eq_zero, ← iUnion_compactCovering]
      exact measure_iUnion_null hall
    exact isOpenPosMeasure_of_mulLeftInvariant_of_compact _ (isCompact_compactCovering R n) hn
  haveI : IsHaarMeasure μ :=
    { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
      toIsOpenPosMeasure := inferInstance }
  let α : R ≃ₜ* R :=
    { toFun := fun r => ⟨k⁻¹ * r * k, (hk r).1 r.2⟩
      invFun := fun r => ⟨k * r * k⁻¹, (hk _).2 (by simpa [mul_assoc] using r.2)⟩
      left_inv := fun r => Subtype.ext (by simp [mul_assoc])
      right_inv := fun r => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
      continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ }
  have hit : ∀ (n : ℕ) (x : R), (((⇑α)^[n] x : R) : G) = k ^ (-(n : ℤ)) * x * k ^ (n : ℤ) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change k⁻¹ * (((⇑α)^[n] x : R) : G) * k = _
      rw [ih]
      push_cast
      group
  have hit' : ∀ (n : ℕ) (x : R), (((⇑α.symm)^[n] x : R) : G) = k ^ (n : ℤ) * x * k ^ (-(n : ℤ)) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      change k * (((⇑α.symm)^[n] x : R) : G) * k⁻¹ = _
      rw [ih]
      push_cast
      group
  obtain ⟨V, hV, hV1⟩ := exists_compact_mem_nhds (1 : R)
  have hL : IsCompact (Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) : Set R) :=
    hce.isCompact_preimage ((hCc.mul (hV.image continuous_subtype_val)).mul hCc)
  have hb : ∀ n : ℕ, (⇑α)^[n] '' V ⊆ Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) ∧
      (⇑α.symm)^[n] '' V ⊆ Subtype.val ⁻¹' (C * (Subtype.val '' V) * C) := by
    intro n
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      show (((⇑α)^[n] x : R) : G) ∈ C * (Subtype.val '' V) * C
      rw [hit n x]
      exact Set.mul_mem_mul (Set.mul_mem_mul (hCm _) ⟨x, hx, rfl⟩) (hCm _)
    · rintro _ ⟨x, hx, rfl⟩
      show (((⇑α.symm)^[n] x : R) : G) ∈ C * (Subtype.val '' V) * C
      rw [hit' n x]
      exact Set.mul_mem_mul (Set.mul_mem_mul (hCm _) ⟨x, hx, rfl⟩) (hCm _)
  have hμα : μ.map α = μ := haar_map_equiv_of_bounded μ α hV hV1 hL hb
  have hmc : Measurable (fun x : G => k⁻¹ * x * k) := (measurable_const_mul _).mul_const _
  have hma : Measurable (⇑α) := α.continuous.measurable
  calc ν.map (fun x => k⁻¹ * x * k) = (μ.map Subtype.val).map (fun x => k⁻¹ * x * k) := by rw [hν]
    _ = (μ.map α).map Subtype.val := by
        rw [map_map hmc hemb.measurable, map_map hemb.measurable hma]
        rfl
    _ = ν := by rw [hμα, hν]

/- English proof (translation)
Establish `e : (fun x : G => (k * n)⁻¹ * x * (k * n)) = (fun x => n⁻¹ * x * n) ∘ (fun x => k⁻¹ * x * k)`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp]`. Use `group`. Rewrite using `[e, ← map_map ((measurable_const_mul _).mul_const _) ((measurable_const_mul _).mul_const _), map_conj_of_bounded R hR ν h0 hc hK hl k hk hC, map_conj_of_mem R ν hl hi hn]`.
-/
theorem conj_of_decomp (R : Subgroup G) (hR : IsClosed (R : Set G)) (ν : Measure G) (_hs : SigmaFinite ν)
    (h0 : ν ≠ 0) (hc : ν (R : Set G)ᶜ = 0) (hK : ∀ K : Set G, IsCompact K → ν K < ⊤)
    (hl : ∀ r ∈ R, ν.map (fun x => r * x) = ν) (hi : ν.map (fun x => x⁻¹) = ν) (k n : G)
    (hk : ∀ r, r ∈ R ↔ k⁻¹ * r * k ∈ R) (hn : n ∈ R) (hC : ∃ C : Set G, IsCompact C ∧ ∀ m : ℤ, k ^ m ∈ C) :
    ν.map (fun x => (k * n)⁻¹ * x * (k * n)) = ν := by
  have e : (fun x : G => (k * n)⁻¹ * x * (k * n)) = (fun x => n⁻¹ * x * n) ∘ (fun x => k⁻¹ * x * k) := by
    funext x
    simp only [Function.comp]
    group
  rw [e, ← map_map ((measurable_const_mul _).mul_const _) ((measurable_const_mul _).mul_const _),
    map_conj_of_bounded R hR ν h0 hc hK hl k hk hC, map_conj_of_mem R ν hl hi hn]

end Conj

end Formalism.L2.SG.CovariantRepresentation
