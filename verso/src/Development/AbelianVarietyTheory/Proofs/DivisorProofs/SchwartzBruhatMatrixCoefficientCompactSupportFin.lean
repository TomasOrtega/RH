import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny
open MeasureTheory

noncomputable section

namespace GlobalTheory.SchrSuppFin

/- English proof (translation)
Establish `hW : ∀ x : V, ∃ W : OpenAddSubgroup V, ∀ w ∈ (W : Set V), f (x + w) = f x`. Introduce `x`. Establish `h1 : {w : V | f (x + w) = f x} ∈ nhds (0 : V)`. Establish `h2` using `(hf.comp_continuous (continuous_add_left x)).eventually_eq 0`. Simplify using `only [Function.comp, add_zero] at h2`.

Conclude with `h2`. Take `⟨W, hW⟩` from `NonarchimedeanAddGroup.is_nonarchimedean _ h1`. Conclude with `⟨W, fun w hw => hW hw⟩`. Use `choose W hW using hW`. Take `⟨t, -, ht⟩` from `hc.isCompact.elim_nhds_subcover (fun x => {z : V | z - x ∈ (W x : Set V)}) (fun x _ => by`.

Use `(continuous_sub_right x).continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Simplify using `using (W x).isOpen.mem_nhds (W x).zero_mem)`. Use `⟨⋂ x ∈ t, (W x : Set V), (Filter.biInter_finset_mem t).2 fun x _ => (W x).isOpen.mem_nhds (W x).zero_mem, fun u hu z => ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_iInter] at hu`. Distinguish the cases in `hz : ∃ x ∈ t, z - x ∈ (W x : Set V)`.

Take `⟨x, hx, hzx⟩` from `hz`. Establish `e1` using `hW x (z - x) hzx`. Establish `e2` using `hW x (z + u - x) (by`. Rewrite using `[show z + u - x = (z - x) + u by abel]; exact (W x).add_mem hzx (hu x hx))`. Rewrite `e1` using `[show x + (z - x) = z by abel]`.

Rewrite `e2` using `[show x + (z + u - x) = z + u by abel]`. Rewrite using `[e1, e2]`. Use `push_neg at hz`. Establish `h1 : z ∉ tsupport f` using `fun h => by`. Take `⟨x, hx, hzx⟩` from `Set.mem_iUnion₂.mp (ht h)`.

Conclude with `hz x hx hzx`. Establish `h2 : z + u ∉ tsupport f` using `fun h => by`. Take `⟨x, hx, hzx⟩` from `Set.mem_iUnion₂.mp (ht h)`. Use `hz x hx ?_` and prove the remaining obligations. Use `(W x).sub_mem hzx (hu x hx)` as an intermediate fact.

Rewrite `this` using `[show z + u - x - u = z - x by abel]`. Then use the resulting hypothesis. Rewrite using `[image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]`.
-/
theorem exists_nhds_translate_eq {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [NonarchimedeanAddGroup V] {f : V → ℂ} (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    ∃ U ∈ nhds (0 : V), ∀ u ∈ U, ∀ z, f (z + u) = f z := by
  have hW : ∀ x : V, ∃ W : OpenAddSubgroup V, ∀ w ∈ (W : Set V), f (x + w) = f x := by
    intro x
    have h1 : {w : V | f (x + w) = f x} ∈ nhds (0 : V) := by
      have h2 := (hf.comp_continuous (continuous_add_left x)).eventually_eq 0
      simp only [Function.comp, add_zero] at h2
      exact h2
    obtain ⟨W, hW⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h1
    exact ⟨W, fun w hw => hW hw⟩
  choose W hW using hW
  obtain ⟨t, -, ht⟩ := hc.isCompact.elim_nhds_subcover (fun x => {z : V | z - x ∈ (W x : Set V)}) (fun x _ => by
    refine (continuous_sub_right x).continuousAt.preimage_mem_nhds ?_
    simpa using (W x).isOpen.mem_nhds (W x).zero_mem)
  refine ⟨⋂ x ∈ t, (W x : Set V), (Filter.biInter_finset_mem t).2 fun x _ => (W x).isOpen.mem_nhds (W x).zero_mem,
    fun u hu z => ?_⟩
  simp only [Set.mem_iInter] at hu
  by_cases hz : ∃ x ∈ t, z - x ∈ (W x : Set V)
  · obtain ⟨x, hx, hzx⟩ := hz
    have e1 := hW x (z - x) hzx
    have e2 := hW x (z + u - x) (by
      rw [show z + u - x = (z - x) + u by abel]; exact (W x).add_mem hzx (hu x hx))
    rw [show x + (z - x) = z by abel] at e1
    rw [show x + (z + u - x) = z + u by abel] at e2
    rw [e1, e2]
  · push_neg at hz
    have h1 : z ∉ tsupport f := fun h => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (ht h)
      exact hz x hx hzx
    have h2 : z + u ∉ tsupport f := fun h => by
      obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (ht h)
      refine hz x hx ?_
      have := (W x).sub_mem hzx (hu x hx)
      rwa [show z + u - x - u = z - x by abel] at this
    rw [image_eq_zero_of_notMem_tsupport h1, image_eq_zero_of_notMem_tsupport h2]

/- English proof (translation)
Use `⟨fun h => ?_⟩` and prove the remaining obligations. Establish `hopen : IsOpen ({0} : Set (Fv F v))` using `(isOpen_singleton_iff_punctured_nhds _).2 h`. Use `haveI := discreteTopology_of_isOpen_singleton_zero hopen`. Use `haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`. Establish `hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v)))` using `isCompact_iff_compactSpace.2 inferInstance`.

Use `haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective`. Establish `hinf : ((v.adicCompletionIntegers F : Set (Fv F v))).Infinite` using `Set.infinite_of_injective_forall_mem (Nat.cast_injective (R := Fv F v)) fun n => natCast_mem _ n`. Conclude with `hinf (hO.finite_of_discrete)`.
-/
theorem nhdsNE_neBot {F : Type} [Field F] [NumberField F] (v : Pl F) : (nhdsWithin (0 : Fv F v) {0}ᶜ).NeBot := by
  refine ⟨fun h => ?_⟩
  have hopen : IsOpen ({0} : Set (Fv F v)) := (isOpen_singleton_iff_punctured_nhds _).2 h
  haveI := discreteTopology_of_isOpen_singleton_zero hopen
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 inferInstance
  haveI : CharZero (Fv F v) := charZero_of_injective_algebraMap (algebraMap F (Fv F v)).injective
  have hinf : ((v.adicCompletionIntegers F : Set (Fv F v))).Infinite :=
    Set.infinite_of_injective_forall_mem (Nat.cast_injective (R := Fv F v)) fun n => natCast_mem _ n
  exact hinf (hO.finite_of_discrete)

end GlobalTheory.SchrSuppFin

namespace GlobalTheory.SchrSuppFin

/- English proof (translation)
Introduce `F _ _ v ψ₀ κ _ _ _ μ _ hψ hcond φ hφ g hg`. Take `⟨hφl, hφc⟩` from `hφ`. Take `⟨hgl, hgc⟩` from `hg`. Take `⟨Uφ, hUφ, hφU⟩` from `exists_nhds_translate_eq hφl hφc`. Take `⟨Ug, hUg, hgU⟩` from `exists_nhds_translate_eq hgl hgc`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v`. Establish `hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v)))` using `isCompact_iff_compactSpace.2 inferInstance`. Establish `hP : ∀ᶠ s in nhds (0 : Fv F v), ∀ y ∈ (v.adicCompletionIntegers F : Set (Fv F v)), ∀ i : κ, (Pi.single i (s * y) : κ → Fv F v) ∈ Uφ ∩ Ug`. Use `hO.eventually_forall_of_forall_eventually fun y _ => ?_` and prove the remaining obligations. Use `Filter.eventually_all.2 fun i => ?_` and prove the remaining obligations.

Establish `hc : Continuous fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v)` using `(continuous_single i).comp continuous_mul`. Establish `hmem : Uφ ∩ Ug ∈ nhds ((fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v)) (0, y))`. Simplify using `using Filter.inter_mem hUφ hUg`. Conclude with `hc.continuousAt.preimage_mem_nhds hmem`. Use `haveI := nhdsNE_neBot v`.

Take `⟨t, ht, ht0⟩` from `((hP.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and (self_mem_nhdsWithin (s := ({0}ᶜ : Set (Fv F v))))).exists`. Establish `ht0' : t ≠ 0` using `ht0`. Use `⟨((fun p : (κ → Fv F v) × (κ → Fv F v) => p.1 - p.2) '' (tsupport φ ×ˢ tsupport g)) ×ˢ Set.pi Set.univ (fun _ => (fun y => t⁻¹ * y) '' (v.adicCompletionIntegers F : Set (Fv F v))), ?_, ?_⟩` and prove the remaining obligations. Conclude with `((hφc.isCompact.prod hgc.isCompact).image continuous_sub).prod (isCompact_univ_pi fun _ => hO.image (continuous_const_mul _))`. Introduce and unpack `⟨a, b⟩ hne`.

Establish `key : ∀ u ∈ Uφ ∩ Ug, ψ₀ (u ⬝ᵥ b) = 1`. Introduce `u hu`. Establish `hG : ∀ y, schr ψ₀ (a, b) φ (y + u) * (starRingEnd ℂ) (g (y + u)) = ψ₀ (u ⬝ᵥ b) * (schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y))`. Introduce `y`. Simplify using `only [schr]`.

Rewrite using `[show y + u + a = (y + a) + u by abel, hφU u hu.1, hgU u hu.2, add_dotProduct, show y ⬝ᵥ b + u ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b) = u ⬝ᵥ b + (y ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b)) by ring, AddChar.map_add_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e` using `integral_add_right_eq_self (μ := μ) (fun y => schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) u`. Simplify using `only [hG] at e`. Rewrite `e` using `[integral_const_mul]`.

Establish `h0 : (ψ₀ (u ⬝ᵥ b) - 1) * ∫ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ∂μ = 0`. Rewrite using `[sub_mul, e]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hne)`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `hex : ∃ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hne (by simp [h])`. Take `⟨y, hy⟩` from `hex`.

Establish `h1 : φ (y + a) ≠ 0` using `fun h => hy (by simp [schr, h])`. Establish `h2 : g y ≠ 0` using `fun h => hy (by simp [h])`. Conclude with `⟨(y + a, y), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, by simp⟩`. Introduce `i _`. Establish `hb : t * b i ∈ v.adicCompletionIntegers F` using `hcond _ fun y hy => by`.

Use `key _ (ht y hy i)` as an intermediate fact. Rewrite `this` using `[single_dotProduct, show t * y * b i = t * b i * y by ring]`. Then use the resulting hypothesis. Conclude with `⟨t * b i, hb, by field_simp⟩`.
-/
theorem support_compact : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) (ψ₀ : AddChar (Fv F v) ℂ) (κ : Type) [Fintype κ]
    [MeasurableSpace (κ → Fv F v)] [BorelSpace (κ → Fv F v)] (μ : MeasureTheory.Measure (κ → Fv F v))
    [μ.IsAddHaarMeasure], Continuous ψ₀ →
    (∀ x : Fv F v, (∀ y ∈ v.adicCompletionIntegers F, ψ₀ (x * y) = 1) → x ∈ v.adicCompletionIntegers F) →
    ∀ φ ∈ SB (κ → Fv F v), ∀ g ∈ SB (κ → Fv F v),
    ∃ C : Set ((κ → Fv F v) × (κ → Fv F v)), IsCompact C ∧
      ∀ w, ∫ y, schr ψ₀ w φ y * (starRingEnd ℂ) (g y) ∂μ ≠ 0 → w ∈ C := by
  intro F _ _ v ψ₀ κ _ _ _ μ _ hψ hcond φ hφ g hg
  classical
  obtain ⟨hφl, hφc⟩ := hφ
  obtain ⟨hgl, hgc⟩ := hg
  obtain ⟨Uφ, hUφ, hφU⟩ := exists_nhds_translate_eq hφl hφc
  obtain ⟨Ug, hUg, hgU⟩ := exists_nhds_translate_eq hgl hgc
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  have hO : IsCompact ((v.adicCompletionIntegers F : Set (Fv F v))) := isCompact_iff_compactSpace.2 inferInstance
  have hP : ∀ᶠ s in nhds (0 : Fv F v), ∀ y ∈ (v.adicCompletionIntegers F : Set (Fv F v)), ∀ i : κ,
      (Pi.single i (s * y) : κ → Fv F v) ∈ Uφ ∩ Ug := by
    refine hO.eventually_forall_of_forall_eventually fun y _ => ?_
    refine Filter.eventually_all.2 fun i => ?_
    have hc : Continuous fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v) :=
      (continuous_single i).comp continuous_mul
    have hmem : Uφ ∩ Ug ∈ nhds ((fun p : Fv F v × Fv F v => (Pi.single i (p.1 * p.2) : κ → Fv F v)) (0, y)) := by
      simpa using Filter.inter_mem hUφ hUg
    exact hc.continuousAt.preimage_mem_nhds hmem
  haveI := nhdsNE_neBot v
  obtain ⟨t, ht, ht0⟩ := ((hP.filter_mono (nhdsWithin_le_nhds (s := {0}ᶜ))).and
    (self_mem_nhdsWithin (s := ({0}ᶜ : Set (Fv F v))))).exists
  have ht0' : t ≠ 0 := ht0
  refine ⟨((fun p : (κ → Fv F v) × (κ → Fv F v) => p.1 - p.2) '' (tsupport φ ×ˢ tsupport g)) ×ˢ
    Set.pi Set.univ (fun _ => (fun y => t⁻¹ * y) '' (v.adicCompletionIntegers F : Set (Fv F v))), ?_, ?_⟩
  · exact ((hφc.isCompact.prod hgc.isCompact).image continuous_sub).prod
      (isCompact_univ_pi fun _ => hO.image (continuous_const_mul _))
  · rintro ⟨a, b⟩ hne
    have key : ∀ u ∈ Uφ ∩ Ug, ψ₀ (u ⬝ᵥ b) = 1 := by
      intro u hu
      have hG : ∀ y, schr ψ₀ (a, b) φ (y + u) * (starRingEnd ℂ) (g (y + u)) =
          ψ₀ (u ⬝ᵥ b) * (schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) := by
        intro y
        simp only [schr]
        rw [show y + u + a = (y + a) + u by abel, hφU u hu.1, hgU u hu.2, add_dotProduct,
          show y ⬝ᵥ b + u ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b) = u ⬝ᵥ b + (y ⬝ᵥ b + ⅟(2 : Fv F v) * (a ⬝ᵥ b)) by ring,
          AddChar.map_add_eq_mul]
        ring
      have e := integral_add_right_eq_self (μ := μ)
        (fun y => schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y)) u
      simp only [hG] at e
      rw [integral_const_mul] at e
      have h0 : (ψ₀ (u ⬝ᵥ b) - 1) * ∫ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ∂μ = 0 := by
        rw [sub_mul, e]; ring
      exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_right hne)
    refine ⟨?_, ?_⟩
    · have hex : ∃ y, schr ψ₀ (a, b) φ y * (starRingEnd ℂ) (g y) ≠ 0 := by
        by_contra h
        push_neg at h
        exact hne (by simp [h])
      obtain ⟨y, hy⟩ := hex
      have h1 : φ (y + a) ≠ 0 := fun h => hy (by simp [schr, h])
      have h2 : g y ≠ 0 := fun h => hy (by simp [h])
      exact ⟨(y + a, y), ⟨subset_tsupport _ h1, subset_tsupport _ h2⟩, by simp⟩
    · intro i _
      have hb : t * b i ∈ v.adicCompletionIntegers F := hcond _ fun y hy => by
        have := key _ (ht y hy i)
        rwa [single_dotProduct, show t * y * b i = t * b i * y by ring] at this
      exact ⟨t * b i, hb, by field_simp⟩

end GlobalTheory.SchrSuppFin

end
