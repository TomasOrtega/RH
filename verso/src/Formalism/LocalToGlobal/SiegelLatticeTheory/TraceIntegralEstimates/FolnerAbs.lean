import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HaarOn

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.FolnerAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

def subOf (S : Set G) (h1 : (1 : G) ∈ S) (hm : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) (hi : ∀ a ∈ S, a⁻¹ ∈ S) :
    Subgroup G where
  carrier := S
  mul_mem' := fun ha hb => hm _ ha _ hb
  one_mem' := h1
  inv_mem' := fun ha => hi _ ha

def LeftHaarSub (S : Set G) (μS : Measure G) : Prop :=
  IsClosed S ∧ (1 : G) ∈ S ∧ (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) ∧ (∀ a ∈ S, a⁻¹ ∈ S) ∧
    SigmaFinite μS ∧ μS ≠ 0 ∧ μS Sᶜ = 0 ∧ (∀ s ∈ S, μS.map (fun x => s * x) = μS)

/- English proof (translation)
Take `⟨a, b, c, d, e, f, g, h', -⟩` from `h`. Conclude with `⟨a, b, c, d, e, f, g, h'⟩`.
-/
theorem leftOf {S : Set G} {μS : Measure G} (h : IsHaarSub S μS) : LeftHaarSub S μS := by
  obtain ⟨a, b, c, d, e, f, g, h', -⟩ := h
  exact ⟨a, b, c, d, e, f, g, h'⟩

/- English proof (translation)
Take `⟨hC, h1, hm, hi, -, -, -, -⟩` from `id hμ`. Set `H : Subgroup G` to `subOf S h1 hm hi`. Establish `hemb : MeasurableEmbedding (Subtype.val : H → G)` using `MeasurableEmbedding.subtype_coe hC.measurableSet`. Establish `key : ∀ ρ : Measure G, LeftHaarSub S ρ → (ρ.comap (Subtype.val : H → G)).map Subtype.val = ρ ∧ IsMulLeftInvariant (ρ.comap (Subtype.val : H → G)) ∧ SigmaFinite (ρ.comap (Subtype.val : H → G)) ∧ ρ.comap (Subtype.val : H → G) ≠ 0`. Introduce `ρ hρ`.

Take `⟨-, -, -, -, hσ, h0, hc, hl⟩` from `hρ`. Establish `hmap : (ρ.comap (Subtype.val : H → G)).map Subtype.val = ρ`. Rewrite using `[hemb.map_comap, Subtype.range_coe_subtype]`. Conclude with `Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hc)`. Use `⟨hmap, ⟨fun s => ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `A hA`. Rewrite using `[Measure.map_apply (measurable_const_mul s) hA, hemb.comap_apply, hemb.comap_apply]`. Establish `e : Subtype.val '' ((fun x : H => s * x) ⁻¹' A) = (fun y : G => (s : G) * y) ⁻¹' (Subtype.val '' A)`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨s * x, hx, rfl⟩`. Introduce and unpack `⟨a, ha, hay⟩`. Use `⟨s⁻¹ * a, ?_, ?_⟩` and prove the remaining obligations. Use `show s * (s⁻¹ * a) ∈ A`.

Rewrite using `[mul_inv_cancel_left]` and apply the resulting hypothesis. Use `show (s : G)⁻¹ * a = y`. Rewrite using `[hay, inv_mul_cancel_left]`. Rewrite using `[e, ← Measure.map_apply (measurable_const_mul (s : G)) (hemb.measurableSet_image' hA), hl _ s.2]`. Conclude with `SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap]; exact hσ)`.

Introduce `h`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← hmap, h, Measure.map_zero]`. Take `⟨hμm, hμi, hμσ, hμ0⟩` from `key μ hμ`. Take `⟨hνm, hνi, hνσ, hν0⟩` from `key ν hν`.

Use `set μ' := μ.comap (Subtype.val : H → G) with hμ'`. Use `set ν' := ν.comap (Subtype.val : H → G) with hν'`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n, ν' (spanningSets (μ' + ν') n) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hν0` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (μ' + ν')]`. Conclude with `measure_iUnion_null hcon`. Use `set A := spanningSets (μ' + ν') n with hA`. Establish `hAm : MeasurableSet A` using `measurableSet_spanningSets _ n`.

Establish `hAfin : (μ' + ν') A < ⊤` using `measure_spanningSets_lt_top _ n`. Rewrite `hAfin` using `[Measure.add_apply]`. Establish `hμA : μ' A ≠ ⊤` using `(lt_of_le_of_lt le_self_add hAfin).ne`. Establish `hνA : ν' A ≠ ⊤` using `(lt_of_le_of_lt le_add_self hAfin).ne`. Use `haveI : BorelSpace H := Subtype.borelSpace (H : Set G)`.

Use `haveI : SecondCountableTopology H := by first`. Consider the case `exact inferInstanceAs (SecondCountableTopology (H : Set G))`. Consider the case `exact TopologicalSpace.Subtype.secondCountableTopology (H : Set G)`. Use `haveI : MeasurableMul₂ H := ContinuousMul.measurableMul₂`. Use `haveI : MeasurableInv H := ContinuousInv.measurableInv`.

Establish `heq : μ' = (μ' A / ν' A) • ν'` using `measure_eq_div_smul μ' ν' hn hνA`. Use `⟨μ' A / ν' A, ?_, ENNReal.div_ne_top hμA hn, ?_⟩` and prove the remaining obligations. Introduce `hc`. Apply `hμ0` to reduce the goal to its premises. Rewrite using `[heq, hc, zero_smul]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem haarSub_prop {S : Set G} {μ ν : Measure G} (hμ : LeftHaarSub S μ) (hν : LeftHaarSub S ν) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ = c • ν := by
  obtain ⟨hC, h1, hm, hi, -, -, -, -⟩ := id hμ
  let H : Subgroup G := subOf S h1 hm hi
  have hemb : MeasurableEmbedding (Subtype.val : H → G) := MeasurableEmbedding.subtype_coe hC.measurableSet
  have key : ∀ ρ : Measure G, LeftHaarSub S ρ →
      (ρ.comap (Subtype.val : H → G)).map Subtype.val = ρ ∧
      IsMulLeftInvariant (ρ.comap (Subtype.val : H → G)) ∧
      SigmaFinite (ρ.comap (Subtype.val : H → G)) ∧ ρ.comap (Subtype.val : H → G) ≠ 0 := by
    intro ρ hρ
    obtain ⟨-, -, -, -, hσ, h0, hc, hl⟩ := hρ
    have hmap : (ρ.comap (Subtype.val : H → G)).map Subtype.val = ρ := by
      rw [hemb.map_comap, Subtype.range_coe_subtype]
      exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hc)
    refine ⟨hmap, ⟨fun s => ?_⟩, ?_, ?_⟩
    · ext A hA
      rw [Measure.map_apply (measurable_const_mul s) hA, hemb.comap_apply, hemb.comap_apply]
      have e : Subtype.val '' ((fun x : H => s * x) ⁻¹' A) =
          (fun y : G => (s : G) * y) ⁻¹' (Subtype.val '' A) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨s * x, hx, rfl⟩
        · rintro ⟨a, ha, hay⟩
          refine ⟨s⁻¹ * a, ?_, ?_⟩
          · show s * (s⁻¹ * a) ∈ A
            rwa [mul_inv_cancel_left]
          · show (s : G)⁻¹ * a = y
            rw [hay, inv_mul_cancel_left]
      rw [e, ← Measure.map_apply (measurable_const_mul (s : G)) (hemb.measurableSet_image' hA),
        hl _ s.2]
    · exact SigmaFinite.of_map _ hemb.measurable.aemeasurable (by rw [hmap]; exact hσ)
    · intro h
      apply h0
      rw [← hmap, h, Measure.map_zero]
  obtain ⟨hμm, hμi, hμσ, hμ0⟩ := key μ hμ
  obtain ⟨hνm, hνi, hνσ, hν0⟩ := key ν hν
  set μ' := μ.comap (Subtype.val : H → G) with hμ'
  set ν' := ν.comap (Subtype.val : H → G) with hν'
  obtain ⟨n, hn⟩ : ∃ n, ν' (spanningSets (μ' + ν') n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hν0
    rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets (μ' + ν')]
    exact measure_iUnion_null hcon
  set A := spanningSets (μ' + ν') n with hA
  have hAm : MeasurableSet A := measurableSet_spanningSets _ n
  have hAfin : (μ' + ν') A < ⊤ := measure_spanningSets_lt_top _ n
  rw [Measure.add_apply] at hAfin
  have hμA : μ' A ≠ ⊤ := (lt_of_le_of_lt le_self_add hAfin).ne
  have hνA : ν' A ≠ ⊤ := (lt_of_le_of_lt le_add_self hAfin).ne
  haveI : BorelSpace H := Subtype.borelSpace (H : Set G)
  haveI : SecondCountableTopology H := by
    first
      | exact inferInstanceAs (SecondCountableTopology (H : Set G))
      | exact TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
  haveI : MeasurableMul₂ H := ContinuousMul.measurableMul₂
  haveI : MeasurableInv H := ContinuousInv.measurableInv
  have heq : μ' = (μ' A / ν' A) • ν' := measure_eq_div_smul μ' ν' hn hνA
  refine ⟨μ' A / ν' A, ?_, ENNReal.div_ne_top hμA hn, ?_⟩
  · intro hc
    apply hμ0
    rw [heq, hc, zero_smul]
  · calc μ = μ'.map Subtype.val := hμm.symm
      _ = ((μ' A / ν' A) • ν').map Subtype.val := by rw [← heq]
      _ = (μ' A / ν' A) • ν'.map Subtype.val := Measure.map_smul _ _ _
      _ = (μ' A / ν' A) • ν := by rw [hνm]

def cjB (b : G) (y : G) : G := b⁻¹ * y * b

/- English proof (translation)
Simplify using `only [cjB, mul_assoc, mul_inv_cancel_left]`.
-/
theorem cjB_mul (b x y : G) : cjB b (x * y) = cjB b x * cjB b y := by
  simp only [cjB, mul_assoc, mul_inv_cancel_left]

/- English proof (translation)
Conclude with `(continuous_const.mul continuous_id).mul continuous_const`.
-/
theorem continuous_cjB (b : G) : Continuous (cjB b) := by
  exact (continuous_const.mul continuous_id).mul continuous_const

/- English proof (translation)
Establish `hcont : Continuous (cjB b)` using `continuous_cjB b`. Establish `hinv1 : ∀ y, cjB b⁻¹ (cjB b y) = y`. Introduce `y`. Simplify using `[cjB, mul_assoc]`. Establish `hinv2 : ∀ y, cjB b (cjB b⁻¹ y) = y`.

Introduce `y`. Simplify using `[cjB, mul_assoc]`. Set `E : G ≃ₜ G` to `{ toFun := cjB b, invFun := cjB b⁻¹, left_inv := hinv1, right_inv := hinv2, continuous_toFun := hcont, continuous_invFun := continuous_cjB _ }`. Set `M : G ≃ᵐ G` to `E.toMeasurableEquiv`. Establish `hmap : ∀ A : Set G, (μ.map (cjB b)) A = μ (cjB b ⁻¹' A)` using `fun A => by`.

Conclude with `MeasurableEquiv.map_apply M A`. Take `⟨hC, h1, hm, hi, hσ, h0, hc, hl⟩` from `hμ`. Establish `hL : LeftHaarSub S (μ.map (cjB b))`. Use `⟨hC, h1, hm, hi, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hσ show SigmaFinite (μ.map M) first`.

Consider the case `exact M.sigmaFinite_map`. Consider the case `exact MeasurableEquiv.sigmaFinite_map M`. Consider the case `(refine SigmaFinite.of_map _ M.measurable.aemeasurable ?_`. Rewrite using `[Measure.map_map M.symm.measurable M.measurable, M.symm_comp_self, Measure.map_id]`. Conclude with `hσ)`.

Introduce `h`. Conclude with `h0 ((Measure.map_eq_zero_iff hcont.measurable.aemeasurable).1 h)`. Rewrite using `[hmap]`. Use `hc using 2` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, Set.mem_compl_iff, hb x]`. Introduce `s hs`. Rewrite using `[Measure.map_map (continuous_mul_left s).measurable hcont.measurable]`. Establish `e1 : (fun x => s * x) ∘ cjB b = cjB b ∘ (fun y => (b * s * b⁻¹) * y)`. Use function extensionality and compare the values at `y`.

Simplify using `[cjB, mul_assoc]`. Establish `hs' : b * s * b⁻¹ ∈ S`. Rewrite using `[hb]`. Simplify `hs` using `[cjB, mul_assoc]`. Rewrite using `[e1, ← Measure.map_map hcont.measurable (continuous_mul_left _).measurable, hl _ hs']`.

Conclude with `haarSub_prop hL ⟨hC, h1, hm, hi, hσ, h0, hc, hl⟩`.
-/
theorem map_cjB {S : Set G} {μ : Measure G} (hμ : LeftHaarSub S μ) (b : G) (hb : ∀ s, s ∈ S ↔ cjB b s ∈ S) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map (cjB b) = c • μ := by
  have hcont : Continuous (cjB b) := continuous_cjB b
  have hinv1 : ∀ y, cjB b⁻¹ (cjB b y) = y := by
    intro y
    simp [cjB, mul_assoc]
  have hinv2 : ∀ y, cjB b (cjB b⁻¹ y) = y := by
    intro y
    simp [cjB, mul_assoc]
  let E : G ≃ₜ G :=
    { toFun := cjB b, invFun := cjB b⁻¹, left_inv := hinv1, right_inv := hinv2,
      continuous_toFun := hcont, continuous_invFun := continuous_cjB _ }
  let M : G ≃ᵐ G := E.toMeasurableEquiv
  have hmap : ∀ A : Set G, (μ.map (cjB b)) A = μ (cjB b ⁻¹' A) := fun A => by
    exact MeasurableEquiv.map_apply M A
  obtain ⟨hC, h1, hm, hi, hσ, h0, hc, hl⟩ := hμ
  have hL : LeftHaarSub S (μ.map (cjB b)) := by
    refine ⟨hC, h1, hm, hi, ?_, ?_, ?_, ?_⟩
    · haveI := hσ
      show SigmaFinite (μ.map M)
      first
        | exact M.sigmaFinite_map
        | exact MeasurableEquiv.sigmaFinite_map M
        | (refine SigmaFinite.of_map _ M.measurable.aemeasurable ?_
           rw [Measure.map_map M.symm.measurable M.measurable, M.symm_comp_self, Measure.map_id]
           exact hσ)
    · intro h
      exact h0 ((Measure.map_eq_zero_iff hcont.measurable.aemeasurable).1 h)
    · rw [hmap]
      convert hc using 2
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, hb x]
    · intro s hs
      rw [Measure.map_map (continuous_mul_left s).measurable hcont.measurable]
      have e1 : (fun x => s * x) ∘ cjB b = cjB b ∘ (fun y => (b * s * b⁻¹) * y) := by
        funext y
        simp [cjB, mul_assoc]
      have hs' : b * s * b⁻¹ ∈ S := by
        rw [hb]
        simpa [cjB, mul_assoc] using hs
      rw [e1, ← Measure.map_map hcont.measurable (continuous_mul_left _).measurable, hl _ hs']
  exact haarSub_prop hL ⟨hC, h1, hm, hi, hσ, h0, hc, hl⟩

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [cjB]`. Consider the case `succ m ih`. Rewrite using `[ih, ha (cjB (a ^ m) s)]`. Establish `e : cjB a (cjB (a ^ m) s) = cjB (a ^ (m + 1)) s`.

Simplify using `[cjB, pow_succ, mul_assoc]`. Rewrite using `[e]`.
-/
theorem cjB_pow_iff {S : Set G} {a : G} (ha : ∀ s, s ∈ S ↔ cjB a s ∈ S) (m : ℕ) (s : G) :
    s ∈ S ↔ cjB (a ^ m) s ∈ S := by
  induction m with
  | zero => simp [cjB]
  | succ m ih =>
    rw [ih, ha (cjB (a ^ m) s)]
    have e : cjB a (cjB (a ^ m) s) = cjB (a ^ (m + 1)) s := by
      simp [cjB, pow_succ, mul_assoc]
    rw [e]

/- English proof (translation)
Take `⟨c, hc0, hctop, hceq⟩` from `map_cjB hμ b hb`. Establish `hinv1 : ∀ y, cjB b⁻¹ (cjB b y) = y`. Introduce `y`. Simplify using `[cjB, mul_assoc]`. Establish `hinv2 : ∀ y, cjB b (cjB b⁻¹ y) = y`.

Introduce `y`. Simplify using `[cjB, mul_assoc]`. Set `E : G ≃ₜ G` to `{ toFun := cjB b, invFun := cjB b⁻¹, left_inv := hinv1, right_inv := hinv2, continuous_toFun := continuous_cjB b, continuous_invFun := continuous_cjB _ }`. Set `M : G ≃ᵐ G` to `E.toMeasurableEquiv`. Use `⟨c, hc0, hctop, fun A => ?_⟩` and prove the remaining obligations.

Establish `h1 : (μ.map (cjB b)) A = μ (cjB b ⁻¹' A)`. Conclude with `MeasurableEquiv.map_apply M A`. Rewrite using `[← h1, hceq, Measure.smul_apply, smul_eq_mul]`.
-/
private theorem preimage_cjB_lemma {S : Set G} {μ : Measure G} (hμ : LeftHaarSub S μ) (b : G)
    (hb : ∀ s, s ∈ S ↔ cjB b s ∈ S) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ A : Set G, μ (cjB b ⁻¹' A) = c * μ A := by
  obtain ⟨c, hc0, hctop, hceq⟩ := map_cjB hμ b hb
  have hinv1 : ∀ y, cjB b⁻¹ (cjB b y) = y := by
    intro y
    simp [cjB, mul_assoc]
  have hinv2 : ∀ y, cjB b (cjB b⁻¹ y) = y := by
    intro y
    simp [cjB, mul_assoc]
  let E : G ≃ₜ G :=
    { toFun := cjB b, invFun := cjB b⁻¹, left_inv := hinv1, right_inv := hinv2,
      continuous_toFun := continuous_cjB b, continuous_invFun := continuous_cjB _ }
  let M : G ≃ᵐ G := E.toMeasurableEquiv
  refine ⟨c, hc0, hctop, fun A => ?_⟩
  have h1 : (μ.map (cjB b)) A = μ (cjB b ⁻¹' A) := by
    exact MeasurableEquiv.map_apply M A
  rw [← h1, hceq, Measure.smul_apply, smul_eq_mul]

/- English proof (translation)
Take `⟨hSC, hS1, hSm, hSi, hSσ, hS0, hSc, hSl, hSK, -, -⟩` from `id hS`. Take `⟨L, hLdef⟩ : ∃ L : ℝ → Set G, L = fun ρ => {x | f x ≤ ρ} ∩ S` from `⟨_, rfl⟩`. Establish `hLmem : ∀ ρ x, x ∈ L ρ ↔ f x ≤ ρ ∧ x ∈ S`. Introduce `ρ x`. Rewrite using `[hLdef]`.

Both sides reduce to the same expression. Establish `hLc : ∀ ρ, IsCompact (L ρ)`. Rewrite using `[hLdef]`. Conclude with `hfK`. Establish `hLm : ∀ ρ, MeasurableSet (L ρ)` using `fun ρ => (hLc ρ).isClosed.measurableSet`.

Establish `hLfin : ∀ ρ, μS (L ρ) ≠ ⊤` using `fun ρ => (hSK _ (hLc ρ)).ne`. Establish `hLmono : Monotone L`. Introduce `ρ₁ ρ₂ h x hx`. Rewrite `hx`, the goal using `[hLmem]`. Conclude with `⟨hx.1.trans h, hx.2⟩`.

Introduce `K hK hKS ε hε`. Choose the witnesses or unpack the hypotheses as in `⟨n₀, hn₀⟩ : ∃ n : ℕ, μS (L n) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hS0` to reduce the goal to its premises.

Establish `hsub : (Set.univ : Set G) ⊆ (⋃ n : ℕ, L n) ∪ Sᶜ`. Introduce `x _`. Distinguish the cases in `hx : x ∈ S`. Use `left`. Take `⟨n, hn⟩` from `exists_nat_ge (f x)`.

Conclude with `Set.mem_iUnion.2 ⟨n, (hLmem _ _).2 ⟨hn, hx⟩⟩`. Use `right`. Conclude with `hx`. Rewrite using `[← Measure.measure_univ_eq_zero]`. Conclude with `measure_mono_null hsub (measure_union_null (measure_iUnion_null hcon) hSc)`.

Establish `hcount : Set.Countable {t : ℝ | 0 < μS {x | f x = t}}` using `Measure.countable_meas_level_set_pos hf.measurable`. Choose the witnesses or unpack the hypotheses as in `⟨ρ, hρI, hρN⟩ : ∃ ρ ∈ Set.Icc (n₀ : ℝ) (n₀ + 1), ρ ∉ {t : ℝ | 0 < μS {x | f x = t}} := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `h0 : volume (Set.Icc (n₀ : ℝ) (n₀ + 1)) = 0` using `measure_mono_null hcon (hcount.measure_zero volume)`.

Rewrite `h0` using `[Real.volume_Icc]`. Simplify using `at h0`. Establish `hlevel : μS {x | f x = ρ} = 0`. Simplify using `only [Set.mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at hρN`. Conclude with `hρN`.

Establish `hV0 : μS (L ρ) ≠ 0`. Introduce `h`. Conclude with `hn₀ (measure_mono_null (hLmono hρI.1) h)`. Establish `hmonoSeq : Monotone fun n : ℕ => L (ρ - 1 / ((n : ℝ) + 1))`. Introduce `i j hij`.

Apply `hLmono` to reduce the goal to its premises. Establish `hij' : (i : ℝ) ≤ j` using `by exact_mod_cast hij`. Establish `: (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1)`. Apply `one_div_le_one_div_of_le` to reduce the goal to its premises. Check the signs of the components of the expression.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hunion : (⋃ n : ℕ, L (ρ - 1 / ((n : ℝ) + 1))) = {x | f x < ρ} ∩ S`. Use extensionality with `x`. Simplify using `only [Set.mem_iUnion, hLmem, Set.mem_inter_iff, Set.mem_setOf_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, hx⟩`. Use `⟨?_, hx⟩` and prove the remaining obligations. Establish `: (0 : ℝ) < 1 / ((n : ℝ) + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce and unpack `⟨hx, hxS⟩`. Take `⟨n, hn⟩` from `exists_nat_one_div_lt (sub_pos.2 hx)`. Conclude with `⟨n, by linarith, hxS⟩`. Establish `hVeq : μS ({x | f x < ρ} ∩ S) = μS (L ρ)`. Apply `le_antisymm` to reduce the goal to its premises.

Apply `measure_mono` to reduce the goal to its premises. Introduce `x hx`. Conclude with `(hLmem _ _).2 ⟨le_of_lt hx.1, hx.2⟩`. Combine the equalities or inequalities in the displayed calculation. Apply `measure_mono` to reduce the goal to its premises.

Introduce `x hx`. Rewrite `hx` using `[hLmem]`. Break down `hx.1.lt_or_eq with h | h` into its components or cases. Conclude with `Or.inl ⟨h, hx.2⟩`. Conclude with `Or.inr h`.

Use `_ ≤ μS ({x | f x < ρ} ∩ S) + μS {x | f x = ρ} := measure_union_le _ _`. Use `_ = μS ({x | f x < ρ} ∩ S) := by rw [hlevel, add_zero]`. Establish `hlim : Tendsto (fun n : ℕ => μS (L (ρ - 1 / ((n : ℝ) + 1)))) atTop (𝓝 (μS (L ρ)))`. Rewrite using `[← hVeq, ← hunion]`. Use `first`.

Consider the case `exact tendsto_measure_iUnion_atTop hmonoSeq`. Consider the case `exact tendsto_measure_iUnion hmonoSeq`. Establish `hlt : μS (L ρ) < (1 + ε) * μS (L ρ)`. Rewrite using `[add_mul, one_mul]`. Conclude with `ENNReal.lt_add_right (hLfin ρ) (mul_ne_zero hε.ne' hV0)`.

Take `⟨n, hn⟩` from `((ENNReal.Tendsto.const_mul hlim (Or.inl hV0)).eventually (lt_mem_nhds hlt)).exists`. Establish `hn' : μS (L ρ) < (1 + ε) * μS (L (ρ - 1 / ((n : ℝ) + 1)))` using `hn`. Establish `hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1)` using `by positivity`. Use `set ρ' := ρ - 1 / ((n : ℝ) + 1) with hρ'`. Use `set U : Set G := {x | ∀ t ∈ L ρ', f (x * t) < f t + 1 / ((n : ℝ) + 1)} with hUdef`.

Establish `hUo : IsOpen U`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x₀ hx₀`. Establish `hx0' : ∀ t ∈ L ρ', f (x₀ * t) < f t + 1 / ((n : ℝ) + 1)` using `hx₀`. Establish `hcont : Continuous fun z : G × G => f (z.1 * z.2) - f z.2` using `(hf.comp (continuous_fst.mul continuous_snd)).sub (hf.comp continuous_snd)`.

Establish `hev : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ L ρ', f (x * y) < f y + 1 / ((n : ℝ) + 1)` using `(hLc ρ').eventually_forall_of_forall_eventually fun y hy => by`. Establish `hxy : f (x₀ * y) - f y < 1 / ((n : ℝ) + 1)`. Use `hx0' y hy` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `((hcont.tendsto (x₀, y)).eventually (gt_mem_nhds hxy)).mono fun z hz => by`.

Establish `hz' : f (z.1 * z.2) - f z.2 < 1 / ((n : ℝ) + 1)` using `hz`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hev`. Establish `hCU : C ⊆ U`. Introduce `c hc`.

Use `show ∀ t ∈ L ρ', f (c * t) < f t + 1 / ((n : ℝ) + 1)`. Introduce `t _`. Rewrite using `[hfC c hc t]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨m, hmU⟩` from `(hcontr K hK hKS U hUo hCU).exists`.

Establish `hb` using `cjB_pow_iff ha m`. Take `⟨c, hc0, hctop, hpre⟩` from `preimage_cjB_lemma (leftOf hS) (a ^ m) hb`. Use `⟨cjB (a ^ m) ⁻¹' L ρ, (continuous_cjB _).measurable (hLm ρ), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Establish `hx' : cjB (a ^ m) x ∈ L ρ` using `hx`.

Conclude with `(hb x).2 ((hLmem _ _).1 hx').2`. Rewrite using `[hpre]`. Conclude with `pos_iff_ne_zero.2 (mul_ne_zero hc0 hV0)`. Rewrite using `[hpre]`. Conclude with `ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hctop) (lt_top_iff_ne_top.2 (hLfin ρ))`.

Establish `hρρ : ρ' ≤ ρ` using `by linarith`. Establish `hsub : cjB (a ^ m) ⁻¹' L ρ' ⊆ {t | t ∈ cjB (a ^ m) ⁻¹' L ρ ∧ ∀ k ∈ K, k * t ∈ cjB (a ^ m) ⁻¹' L ρ}`. Introduce `t ht`. Establish `ht0 : cjB (a ^ m) t ∈ L ρ'` using `ht`. Establish `ht'` using `(hLmem _ _).1 ht0`.

Use `⟨hLmono hρρ ht0, fun k hk => ?_⟩` and prove the remaining obligations. Use `show cjB (a ^ m) (k * t) ∈ L ρ`. Rewrite using `[cjB_mul, hLmem]`. Use `⟨?_, hSm _ ((hb k).1 (hKS hk)) _ ht'.2⟩` and prove the remaining obligations. Establish `hkU : ∀ t ∈ L ρ', f (cjB (a ^ m) k * t) < f t + 1 / ((n : ℝ) + 1)` using `hmU k hk`.

Use `hkU _ ht0` as an intermediate fact. Combine the linear relations using `[ht'.1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isFolner_of_contract {S : Set G} {μS : Measure G} (hS : IsHaarSub S μS) (C : Set G) (f : G → ℝ)
    (hf : Continuous f) (hfC : ∀ c ∈ C, ∀ x, f (c * x) = f x) (hfK : ∀ ρ : ℝ, IsCompact ({x | f x ≤ ρ} ∩ S))
    (a : G) (ha : ∀ s, s ∈ S ↔ cjB a s ∈ S)
    (hcontr : ∀ K : Set G, IsCompact K → K ⊆ S → ∀ U : Set G, IsOpen U → C ⊆ U →
      ∀ᶠ m : ℕ in atTop, ∀ k ∈ K, cjB (a ^ m) k ∈ U) :
    IsFolner S μS := by
  obtain ⟨hSC, hS1, hSm, hSi, hSσ, hS0, hSc, hSl, hSK, -, -⟩ := id hS
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ → Set G, L = fun ρ => {x | f x ≤ ρ} ∩ S := ⟨_, rfl⟩
  have hLmem : ∀ ρ x, x ∈ L ρ ↔ f x ≤ ρ ∧ x ∈ S := by
    intro ρ x
    rw [hLdef]
    rfl
  have hLc : ∀ ρ, IsCompact (L ρ) := by
    rw [hLdef]
    exact hfK
  have hLm : ∀ ρ, MeasurableSet (L ρ) := fun ρ => (hLc ρ).isClosed.measurableSet
  have hLfin : ∀ ρ, μS (L ρ) ≠ ⊤ := fun ρ => (hSK _ (hLc ρ)).ne
  have hLmono : Monotone L := by
    intro ρ₁ ρ₂ h x hx
    rw [hLmem] at hx ⊢
    exact ⟨hx.1.trans h, hx.2⟩
  intro K hK hKS ε hε
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, μS (L n) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hS0
    have hsub : (Set.univ : Set G) ⊆ (⋃ n : ℕ, L n) ∪ Sᶜ := by
      intro x _
      by_cases hx : x ∈ S
      · left
        obtain ⟨n, hn⟩ := exists_nat_ge (f x)
        exact Set.mem_iUnion.2 ⟨n, (hLmem _ _).2 ⟨hn, hx⟩⟩
      · right
        exact hx
    rw [← Measure.measure_univ_eq_zero]
    exact measure_mono_null hsub (measure_union_null (measure_iUnion_null hcon) hSc)
  have hcount : Set.Countable {t : ℝ | 0 < μS {x | f x = t}} :=
    Measure.countable_meas_level_set_pos hf.measurable
  obtain ⟨ρ, hρI, hρN⟩ : ∃ ρ ∈ Set.Icc (n₀ : ℝ) (n₀ + 1), ρ ∉ {t : ℝ | 0 < μS {x | f x = t}} := by
    by_contra hcon
    push_neg at hcon
    have h0 : volume (Set.Icc (n₀ : ℝ) (n₀ + 1)) = 0 :=
      measure_mono_null hcon (hcount.measure_zero volume)
    rw [Real.volume_Icc] at h0
    simp at h0
  have hlevel : μS {x | f x = ρ} = 0 := by
    simp only [Set.mem_setOf_eq, not_lt, nonpos_iff_eq_zero] at hρN
    exact hρN
  have hV0 : μS (L ρ) ≠ 0 := by
    intro h
    exact hn₀ (measure_mono_null (hLmono hρI.1) h)
  have hmonoSeq : Monotone fun n : ℕ => L (ρ - 1 / ((n : ℝ) + 1)) := by
    intro i j hij
    apply hLmono
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have : (1 : ℝ) / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) := by
      apply one_div_le_one_div_of_le
      · positivity
      · linarith
    linarith
  have hunion : (⋃ n : ℕ, L (ρ - 1 / ((n : ℝ) + 1))) = {x | f x < ρ} ∩ S := by
    ext x
    simp only [Set.mem_iUnion, hLmem, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, hn, hx⟩
      refine ⟨?_, hx⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · rintro ⟨hx, hxS⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hx)
      exact ⟨n, by linarith, hxS⟩
  have hVeq : μS ({x | f x < ρ} ∩ S) = μS (L ρ) := by
    apply le_antisymm
    · apply measure_mono
      intro x hx
      exact (hLmem _ _).2 ⟨le_of_lt hx.1, hx.2⟩
    · calc μS (L ρ) ≤ μS (({x | f x < ρ} ∩ S) ∪ {x | f x = ρ}) := by
            apply measure_mono
            intro x hx
            rw [hLmem] at hx
            rcases hx.1.lt_or_eq with h | h
            · exact Or.inl ⟨h, hx.2⟩
            · exact Or.inr h
        _ ≤ μS ({x | f x < ρ} ∩ S) + μS {x | f x = ρ} := measure_union_le _ _
        _ = μS ({x | f x < ρ} ∩ S) := by rw [hlevel, add_zero]
  have hlim : Tendsto (fun n : ℕ => μS (L (ρ - 1 / ((n : ℝ) + 1)))) atTop (𝓝 (μS (L ρ))) := by
    rw [← hVeq, ← hunion]
    first
      | exact tendsto_measure_iUnion_atTop hmonoSeq
      | exact tendsto_measure_iUnion hmonoSeq
  have hlt : μS (L ρ) < (1 + ε) * μS (L ρ) := by
    rw [add_mul, one_mul]
    exact ENNReal.lt_add_right (hLfin ρ) (mul_ne_zero hε.ne' hV0)
  obtain ⟨n, hn⟩ := ((ENNReal.Tendsto.const_mul hlim (Or.inl hV0)).eventually (lt_mem_nhds hlt)).exists
  have hn' : μS (L ρ) < (1 + ε) * μS (L (ρ - 1 / ((n : ℝ) + 1))) := hn
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  set ρ' := ρ - 1 / ((n : ℝ) + 1) with hρ'
  set U : Set G := {x | ∀ t ∈ L ρ', f (x * t) < f t + 1 / ((n : ℝ) + 1)} with hUdef
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro x₀ hx₀
    have hx0' : ∀ t ∈ L ρ', f (x₀ * t) < f t + 1 / ((n : ℝ) + 1) := hx₀
    have hcont : Continuous fun z : G × G => f (z.1 * z.2) - f z.2 :=
      (hf.comp (continuous_fst.mul continuous_snd)).sub (hf.comp continuous_snd)
    have hev : ∀ᶠ x in 𝓝 x₀, ∀ y ∈ L ρ', f (x * y) < f y + 1 / ((n : ℝ) + 1) :=
      (hLc ρ').eventually_forall_of_forall_eventually fun y hy => by
        have hxy : f (x₀ * y) - f y < 1 / ((n : ℝ) + 1) := by
          have := hx0' y hy
          linarith
        exact ((hcont.tendsto (x₀, y)).eventually (gt_mem_nhds hxy)).mono fun z hz => by
          have hz' : f (z.1 * z.2) - f z.2 < 1 / ((n : ℝ) + 1) := hz
          linarith
    exact hev
  have hCU : C ⊆ U := by
    intro c hc
    show ∀ t ∈ L ρ', f (c * t) < f t + 1 / ((n : ℝ) + 1)
    intro t _
    rw [hfC c hc t]
    linarith
  obtain ⟨m, hmU⟩ := (hcontr K hK hKS U hUo hCU).exists
  have hb := cjB_pow_iff ha m
  obtain ⟨c, hc0, hctop, hpre⟩ := preimage_cjB_lemma (leftOf hS) (a ^ m) hb
  refine ⟨cjB (a ^ m) ⁻¹' L ρ, (continuous_cjB _).measurable (hLm ρ), ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : cjB (a ^ m) x ∈ L ρ := hx
    exact (hb x).2 ((hLmem _ _).1 hx').2
  · rw [hpre]
    exact pos_iff_ne_zero.2 (mul_ne_zero hc0 hV0)
  · rw [hpre]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hctop) (lt_top_iff_ne_top.2 (hLfin ρ))
  · have hρρ : ρ' ≤ ρ := by linarith
    have hsub : cjB (a ^ m) ⁻¹' L ρ' ⊆
        {t | t ∈ cjB (a ^ m) ⁻¹' L ρ ∧ ∀ k ∈ K, k * t ∈ cjB (a ^ m) ⁻¹' L ρ} := by
      intro t ht
      have ht0 : cjB (a ^ m) t ∈ L ρ' := ht
      have ht' := (hLmem _ _).1 ht0
      refine ⟨hLmono hρρ ht0, fun k hk => ?_⟩
      show cjB (a ^ m) (k * t) ∈ L ρ
      rw [cjB_mul, hLmem]
      refine ⟨?_, hSm _ ((hb k).1 (hKS hk)) _ ht'.2⟩
      have hkU : ∀ t ∈ L ρ', f (cjB (a ^ m) k * t) < f t + 1 / ((n : ℝ) + 1) := hmU k hk
      have := hkU _ ht0
      linarith [ht'.1]
    calc μS (cjB (a ^ m) ⁻¹' L ρ) = c * μS (L ρ) := hpre _
      _ ≤ c * ((1 + ε) * μS (L ρ')) := mul_le_mul_of_nonneg_left hn'.le zero_le
      _ = (1 + ε) * (c * μS (L ρ')) := by ring
      _ = (1 + ε) * μS (cjB (a ^ m) ⁻¹' L ρ') := by rw [hpre]
      _ ≤ (1 + ε) * μS {t | t ∈ cjB (a ^ m) ⁻¹' L ρ ∧ ∀ k ∈ K, k * t ∈ cjB (a ^ m) ⁻¹' L ρ} :=
        mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le

end Formalism.L2.S.Pv.FolnerAbs
