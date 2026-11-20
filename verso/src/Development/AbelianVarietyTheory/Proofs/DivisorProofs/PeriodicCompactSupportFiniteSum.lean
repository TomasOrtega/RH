import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.EvAdm

/- English proof (translation)
Introduce `F _ _ κ _ d _ g hg hinv`. Use `set U := GlobalTheory.EvAdm.scaledInt F κ d with hU`. Establish `hUo : IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F))` using `GlobalTheory.EvAdm.isOpen_scaledInt d`. Establish `hcov : tsupport g ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U}`. Introduce `x _`.

Conclude with `Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩`. Take `⟨t, ht⟩` from `hg.isCompact.elim_finite_subcover (fun y => {x | x - y ∈ U}) (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov`. Set `R : Finset (κ → FiniteAdeleRing (𝓞 F) F)` to `(t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out`. Establish `hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r'`. Introduce `r hr r' hr' x h h'`.

Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 hr`. Take `⟨q', -, rfl⟩` from `Finset.mem_image.1 hr'`. Establish `e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x` using `QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])`. Establish `e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x` using `QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])`. Rewrite `e1`, `e2` using `[QuotientAddGroup.out_eq']`.

Rewrite using `[e1, e2]`. Establish `hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U`. Introduce `x hx`. Take `⟨y, hy, hxy⟩` from `Set.mem_iUnion₂.1 (ht hx)`. Use `⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩` and prove the remaining obligations.

Establish `e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U` using `QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)`. Use `U.add_mem hxy e` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Use `⟨R, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply]`. Distinguish the cases in `hx : ∃ r ∈ R, x - r ∈ U`. Take `⟨r0, hr0, hxr0⟩` from `hx`. Rewrite using `[Finset.sum_eq_single_of_mem r0 hr0]`.

Establish `hm : x ∈ {y | y - r0 ∈ U}` using `hxr0`. Simplify using `only [Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul, mul_one]`. Establish `e` using `hinv r0 (x - r0) hxr0`. Rewrite `e` using `[add_sub_cancel]`. Conclude with `e`.

Introduce `r hr hne`. Establish `hm : x ∉ {y | y - r ∈ U}` using `fun h => hne (hdist r hr r0 hr0 _ h hxr0)`. Simplify using `only [Pi.smul_apply, Set.indicator_of_notMem hm, smul_eq_mul, mul_zero]`. Use `push_neg at hx`. Establish `hK' : x ∉ tsupport g` using `fun h => by`.

Take `⟨r, hr, h'⟩` from `hcover _ h`. Conclude with `hx r hr h'`. Rewrite using `[image_eq_zero_of_notMem_tsupport hK']`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `r hr`. Establish `hm : x ∉ {y | y - r ∈ U}` using `hx r hr`. Simplify using `only [Pi.smul_apply, Set.indicator_of_notMem hm, smul_eq_mul, mul_zero]`.
-/
theorem eq_sum_coset_indicator_scaledInt : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (d : F), d ≠ 0 →
    ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
    (∀ y, ∀ u ∈ GlobalTheory.EvAdm.scaledInt F κ d, g (y + u) = g y) →
    ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
      g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ d} (fun _ => (1 : ℂ)) := by
  intro F _ _ κ _ d _ g hg hinv
  classical
  set U := GlobalTheory.EvAdm.scaledInt F κ d with hU
  have hUo : IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) := GlobalTheory.EvAdm.isOpen_scaledInt d
  have hcov : tsupport g ⊆ ⋃ y : (κ → FiniteAdeleRing (𝓞 F) F), {x | x - y ∈ U} := by
    intro x _
    exact Set.mem_iUnion.2 ⟨x, by simp [U.zero_mem]⟩
  obtain ⟨t, ht⟩ := hg.isCompact.elim_finite_subcover (fun y => {x | x - y ∈ U})
    (fun y => hUo.preimage (continuous_id.sub continuous_const)) hcov
  let R : Finset (κ → FiniteAdeleRing (𝓞 F) F) :=
    (t.image (QuotientAddGroup.mk : (κ → FiniteAdeleRing (𝓞 F) F) → _ ⧸ U)).image Quotient.out
  have hdist : ∀ r ∈ R, ∀ r' ∈ R, ∀ x, x - r ∈ U → x - r' ∈ U → r = r' := by
    intro r hr r' hr' x h h'
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hr'
    have e1 : (QuotientAddGroup.mk q.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    have e2 : (QuotientAddGroup.mk q'.out : _ ⧸ U) = QuotientAddGroup.mk x :=
      QuotientAddGroup.eq.2 (by rwa [neg_add_eq_sub])
    rw [QuotientAddGroup.out_eq'] at e1 e2
    rw [e1, e2]
  have hcover : ∀ x ∈ tsupport g, ∃ r ∈ R, x - r ∈ U := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hx)
    refine ⟨(QuotientAddGroup.mk y : _ ⧸ U).out, Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hy), ?_⟩
    have e : -(QuotientAddGroup.mk y : _ ⧸ U).out + y ∈ U :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _)
    have := U.add_mem hxy e
    convert this using 1
    abel
  refine ⟨R, ?_⟩
  funext x
  rw [Finset.sum_apply]
  by_cases hx : ∃ r ∈ R, x - r ∈ U
  · obtain ⟨r0, hr0, hxr0⟩ := hx
    rw [Finset.sum_eq_single_of_mem r0 hr0]
    · have hm : x ∈ {y | y - r0 ∈ U} := hxr0
      simp only [Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul, mul_one]
      have e := hinv r0 (x - r0) hxr0
      rw [add_sub_cancel] at e
      exact e
    · intro r hr hne
      have hm : x ∉ {y | y - r ∈ U} := fun h => hne (hdist r hr r0 hr0 _ h hxr0)
      simp only [Pi.smul_apply, Set.indicator_of_notMem hm, smul_eq_mul, mul_zero]
  · push_neg at hx
    have hK' : x ∉ tsupport g := fun h => by
      obtain ⟨r, hr, h'⟩ := hcover _ h
      exact hx r hr h'
    rw [image_eq_zero_of_notMem_tsupport hK']
    symm
    apply Finset.sum_eq_zero
    intro r hr
    have hm : x ∉ {y | y - r ∈ U} := hx r hr
    simp only [Pi.smul_apply, Set.indicator_of_notMem hm, smul_eq_mul, mul_zero]

end GlobalTheory.EvAdm

end
