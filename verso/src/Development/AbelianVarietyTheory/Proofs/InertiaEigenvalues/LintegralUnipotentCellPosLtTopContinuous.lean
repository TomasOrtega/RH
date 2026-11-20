import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Definitions.Divisors.MirSet
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CellDec GlobalTheory.RSTheta GlobalTheory.ThetaPoisson
  GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic
open scoped ComplexConjugate nonZeroDivisors ENNReal Pointwise ComplexOrder

namespace GlobalTheory.RSLocalPart

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Use `haveI : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩`. Use `haveI : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩`. Use `set A : Set G := ⋃ γ : Γ, γ • closure K with hA`. Establish `hAm : MeasurableSet A` using `.iUnion fun γ => isClosed_closure.measurableSet.const_smul γ`. Establish `hfin : μ (A ∩ 𝓕) < ⊤`.

Use `lt_of_le_of_lt ?_ (hK.closure.measure_lt_top (μ := μ))` and prove the remaining obligations. Rewrite using `[h𝓕.measure_eq_tsum (closure K), hA, Set.iUnion_inter]`. Conclude with `measure_iUnion_le _`. Establish `hcx : ∀ x, Continuous (B x)` using `fun x => hc.comp (Continuous.prodMk_right x)`. Establish `hm : ∀ x : ℝ, AEStronglyMeasurable (B x) (μ.restrict (𝓕 ∩ O))` using `fun x => (hcx x).aestronglyMeasurable`.

Establish `hO' : ∀ᵐ g ∂μ.restrict (𝓕 ∩ O), g ∈ O`. Rewrite using `[Set.inter_comm, ← Measure.restrict_restrict hO.measurableSet]`. Conclude with `ae_restrict_mem hO.measurableSet`. Establish `hb : ∀ x₀ : ℝ, ∃ M : G → ℝ, Integrable M (μ.restrict (𝓕 ∩ O)) ∧ ∀ x ∈ Set.Icc (x₀ - 1) (x₀ + 1), ∀ᵐ g ∂μ.restrict (𝓕 ∩ O), ‖B x g‖ ≤ M g`. Introduce `x₀`.

Take `⟨M, hM⟩` from `((isCompact_Icc (a := x₀ - 1) (b := x₀ + 1)).prod hK).exists_bound_of_continuousOn hc.continuousOn`. Use `⟨A.indicator fun _ => max M 0, ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[integrable_indicator_iff hAm]`. Use `integrableOn_const (ne_of_lt ?_)` and prove the remaining obligations. Rewrite using `[Measure.restrict_apply hAm]`.

Conclude with `lt_of_le_of_lt (measure_mono fun g hg => (⟨hg.1, hg.2.1⟩ : g ∈ A ∩ 𝓕)) hfin`. Use `filter_upwards [hO'] with g hg`. Distinguish the cases in `h : B x g = 0`. Rewrite using `[h, norm_zero]`. Conclude with `Set.indicator_nonneg (fun _ _ => le_max_right _ _) g`.

Take `⟨γ, hγ, hk⟩` from `hs x g hg h`. Establish `hgA : g ∈ A` using `Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹, Set.mem_smul_set_iff_inv_smul_mem.2 (by rw [inv_inv]; exact subset_closure hk)⟩`. Rewrite using `[Set.indicator_of_mem hgA, ← hBΓ x γ hγ]`. Conclude with `(hM (x, γ * g) ⟨hx, hk⟩).trans (le_max_left _ _)`. Establish `hI : ∀ x : ℝ, IntegrableOn (B x) (𝓕 ∩ O) μ` using `fun x => by`.

Take `⟨M, hM, h⟩` from `hb x`. Conclude with `hM.mono' (hm x) (h x ⟨by linarith, by linarith⟩)`. Use `⟨hI, continuous_iff_continuousAt.2 fun x₀ => ?_, fun x => ?_⟩` and prove the remaining obligations. Take `⟨M, hM, h⟩` from `hb x₀`. Use `continuousAt_of_dominated (.of_forall hm) ?_ hM (.of_forall fun g => ?_)` and prove the remaining obligations.

Use `filter_upwards [Icc_mem_nhds (show x₀ - 1 < x₀ by linarith) (show x₀ < x₀ + 1 by linarith)] with x hx`. Conclude with `h x hx`. Conclude with `(hc.comp (Continuous.prodMk_left g)).continuousAt`. Establish `hso : IsOpen (Function.support (B x))` using `isOpen_ne_fun (hcx x) continuous_const`. Rewrite using `[integral_pos_iff_support_of_nonneg (hB0 x) (hI x), Measure.restrict_apply hso.measurableSet, pos_iff_ne_zero]`.

Introduce `h0`. Establish `hinv : ∀ γ : Γ, γ • (O ∩ Function.support (B x)) = O ∩ Function.support (B x)`. Establish `key : ∀ γ : Γ, ∀ g ∈ O ∩ Function.support (B x), γ • g ∈ O ∩ Function.support (B x)` using `fun γ g hg => ⟨hOΓ γ γ.2 g hg.1, fun h => hg.2 ((hBΓ x γ γ.2 g).symm.trans h)⟩`. Introduce `γ`. Use extensionality with `g`.

Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem]`. Conclude with `⟨fun h => by simpa using key γ _ h, key _ g⟩`. Use `h𝓕.measure_zero_of_invariant _ hinv (measure_mono_null (fun g hg => by exact ⟨hg.1.2, hg.2, hg.1.1⟩) h0)` as an intermediate fact. Take `⟨g, hg, hg'⟩` from `h1 x`. Conclude with `((hO.inter hso).measure_pos μ ⟨g, hg, hg'⟩).ne' this`.
-/
theorem integral_family_pos (μ : Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {O K : Set G} (hO : IsOpen O) (hK : IsCompact K)
    (hOΓ : ∀ γ ∈ Γ, ∀ g ∈ O, γ * g ∈ O) {B : ℝ → G → ℝ} (hc : Continuous (Function.uncurry B))
    (hB0 : ∀ x g, 0 ≤ B x g) (hBΓ : ∀ x, ∀ γ ∈ Γ, ∀ g, B x (γ * g) = B x g)
    (hs : ∀ x, ∀ g ∈ O, B x g ≠ 0 → ∃ γ ∈ Γ, γ * g ∈ K) (h1 : ∀ x, ∃ g ∈ O, B x g ≠ 0) :
    (∀ x : ℝ, IntegrableOn (B x) (𝓕 ∩ O) μ) ∧
      (Continuous fun x : ℝ => ∫ g in 𝓕 ∩ O, B x g ∂μ) ∧ ∀ x : ℝ, 0 < ∫ g in 𝓕 ∩ O, B x g ∂μ := by
  haveI : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  set A : Set G := ⋃ γ : Γ, γ • closure K with hA
  have hAm : MeasurableSet A := .iUnion fun γ => isClosed_closure.measurableSet.const_smul γ
  have hfin : μ (A ∩ 𝓕) < ⊤ := by
    refine lt_of_le_of_lt ?_ (hK.closure.measure_lt_top (μ := μ))
    rw [h𝓕.measure_eq_tsum (closure K), hA, Set.iUnion_inter]
    exact measure_iUnion_le _
  have hcx : ∀ x, Continuous (B x) := fun x => hc.comp (Continuous.prodMk_right x)
  have hm : ∀ x : ℝ, AEStronglyMeasurable (B x) (μ.restrict (𝓕 ∩ O)) := fun x => (hcx x).aestronglyMeasurable
  have hO' : ∀ᵐ g ∂μ.restrict (𝓕 ∩ O), g ∈ O := by
    rw [Set.inter_comm, ← Measure.restrict_restrict hO.measurableSet]
    exact ae_restrict_mem hO.measurableSet
  have hb : ∀ x₀ : ℝ, ∃ M : G → ℝ, Integrable M (μ.restrict (𝓕 ∩ O)) ∧
      ∀ x ∈ Set.Icc (x₀ - 1) (x₀ + 1), ∀ᵐ g ∂μ.restrict (𝓕 ∩ O), ‖B x g‖ ≤ M g := by
    intro x₀
    obtain ⟨M, hM⟩ := ((isCompact_Icc (a := x₀ - 1) (b := x₀ + 1)).prod hK).exists_bound_of_continuousOn hc.continuousOn
    refine ⟨A.indicator fun _ => max M 0, ?_, fun x hx => ?_⟩
    · rw [integrable_indicator_iff hAm]
      refine integrableOn_const (ne_of_lt ?_)
      rw [Measure.restrict_apply hAm]
      exact lt_of_le_of_lt (measure_mono fun g hg => (⟨hg.1, hg.2.1⟩ : g ∈ A ∩ 𝓕)) hfin
    · filter_upwards [hO'] with g hg
      by_cases h : B x g = 0
      · rw [h, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) g
      · obtain ⟨γ, hγ, hk⟩ := hs x g hg h
        have hgA : g ∈ A := Set.mem_iUnion.2 ⟨(⟨γ, hγ⟩ : Γ)⁻¹,
          Set.mem_smul_set_iff_inv_smul_mem.2 (by rw [inv_inv]; exact subset_closure hk)⟩
        rw [Set.indicator_of_mem hgA, ← hBΓ x γ hγ]
        exact (hM (x, γ * g) ⟨hx, hk⟩).trans (le_max_left _ _)
  have hI : ∀ x : ℝ, IntegrableOn (B x) (𝓕 ∩ O) μ := fun x => by
    obtain ⟨M, hM, h⟩ := hb x
    exact hM.mono' (hm x) (h x ⟨by linarith, by linarith⟩)
  refine ⟨hI, continuous_iff_continuousAt.2 fun x₀ => ?_, fun x => ?_⟩
  · obtain ⟨M, hM, h⟩ := hb x₀
    refine continuousAt_of_dominated (.of_forall hm) ?_ hM (.of_forall fun g => ?_)
    · filter_upwards [Icc_mem_nhds (show x₀ - 1 < x₀ by linarith) (show x₀ < x₀ + 1 by linarith)] with x hx
      exact h x hx
    · exact (hc.comp (Continuous.prodMk_left g)).continuousAt
  · have hso : IsOpen (Function.support (B x)) := isOpen_ne_fun (hcx x) continuous_const
    rw [integral_pos_iff_support_of_nonneg (hB0 x) (hI x), Measure.restrict_apply hso.measurableSet, pos_iff_ne_zero]
    intro h0
    have hinv : ∀ γ : Γ, γ • (O ∩ Function.support (B x)) = O ∩ Function.support (B x) := by
      have key : ∀ γ : Γ, ∀ g ∈ O ∩ Function.support (B x), γ • g ∈ O ∩ Function.support (B x) := fun γ g hg =>
        ⟨hOΓ γ γ.2 g hg.1, fun h => hg.2 ((hBΓ x γ γ.2 g).symm.trans h)⟩
      intro γ
      ext g
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      exact ⟨fun h => by simpa using key γ _ h, key _ g⟩
    have := h𝓕.measure_zero_of_invariant _ hinv (measure_mono_null (fun g hg => by exact ⟨hg.1.2, hg.2, hg.1.1⟩) h0)
    obtain ⟨g, hg, hg'⟩ := h1 x
    exact ((hO.inter hso).measure_pos μ ⟨g, hg, hg'⟩).ne' this

end Abstract

section Cocompact

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Take `⟨δ, hδ, rfl⟩` from `hγ`. Take `⟨h1, h2⟩` from `(GlobalTheory.SmGL.mem_unipB E).1 hδ`. Use `(GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) (δ.val i j) = 0`. Rewrite using `[h1 i j hij, map_zero]`.

Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) (δ.val i i) = 1`. Rewrite using `[h2 i, map_one]`.
-/
theorem NE_le {γ : GA E a} (hγ : γ ∈ NE E a) : γ ∈ NA E a := by
  obtain ⟨δ, hδ, rfl⟩ := hγ
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB E).1 hδ
  refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · change algebraMap E (Ad E) (δ.val i j) = 0
    rw [h1 i j hij, map_zero]
  · change algebraMap E (Ad E) (δ.val i i) = 1
    rw [h2 i, map_one]

/- English proof (translation)
Take `⟨h1, h2⟩` from `(GlobalTheory.SmGL.mem_unipB _).1 hu`. Rewrite using `[Matrix.det_of_isUpperTriangular fun i j hij => h1 i j hij]`. Conclude with `Finset.prod_eq_one fun i _ => h2 i`.
-/
theorem det_eq_one {u : GA E a} (hu : u ∈ NA E a) : u.val.det = 1 := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  rw [Matrix.det_of_isUpperTriangular fun i j hij => h1 i j hij]
  exact Finset.prod_eq_one fun i _ => h2 i

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨1, one_mem _, fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩`. Consider the case `succ m ih`. Take `⟨γ, hγ, h⟩` from `ih`. Distinguish the cases in `hm : m < a`.

Use `swap`. Conclude with `⟨γ, hγ, fun i j hij _ => h i j hij (by omega)⟩`. Establish `hw : γ * u ∈ NA E a` using `mul_mem (NE_le hγ) hu`. Take `⟨h1, h2⟩` from `(GlobalTheory.SmGL.mem_unipB _).1 hw`. Use `choose y hy using fun i : Fin a => hK ((γ * u).val i ⟨m, hm⟩)`.

Use `⟨ratGL E a (GlobalTheory.JSW.colGL m fun i => -y i) * γ, mul_mem ⟨_, (GlobalTheory.SmGL.mem_unipB E).2 ⟨fun i j hij => ?_, fun i => ?_⟩, rfl⟩ hγ, fun i j hij hj => ?_⟩` and prove the remaining obligations. Establish `: ¬ ((j : ℕ) = m ∧ (i : ℕ) < m)` using `by have : (j : ℕ) < i := hij; omega`. Simplify using `[GlobalTheory.JSW.colGL, this, hij.ne']`. Establish `: ¬ ((i : ℕ) = m ∧ (i : ℕ) < m)` using `by omega`. Simplify using `[GlobalTheory.JSW.colGL, this]`.

Rewrite using `[mul_assoc]`. Generalize the expression as in `γ * u = w at *`. Establish `e : (ratGL E a (GlobalTheory.JSW.colGL m fun i => -y i) * w).val i j = w.val i j - if (i : ℕ) < m then algebraMap E (Ad E) (y i) * w.val ⟨m, hm⟩ j else 0`. Establish `e1 : (ratGL E a (GlobalTheory.JSW.colGL m fun i => -y i)).val = 1 + Matrix.of (fun i j : Fin a => if j = ⟨m, hm⟩ then (if (i : ℕ) < m then -algebraMap E (Ad E) (y i) else 0) else 0)`. Use extensionality with `i j : 1`.

Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) ((GlobalTheory.JSW.colGL m fun i => -y i).val i j) = _`. Simplify using `only [GlobalTheory.JSW.colGL, Matrix.add_apply, Matrix.of_apply, map_add, Matrix.one_apply, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> simp_all`. Rewrite using `[Units.val_mul, e1, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Apply the tactic sequence `split_ifs <;> ring`. Rewrite using `[e]`. Establish `hij' : (i : ℕ) < j` using `hij`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj` into its components or cases. Rewrite using `[h1 ⟨m, hm⟩ j hj, mul_zero, ite_self, sub_zero]`.

Conclude with `h i j hij hj`. Take `rfl : j = ⟨m, hm⟩` from `Fin.ext hj`. Rewrite using `[if_pos hij', h2, mul_one]`. Conclude with `hy i`.
-/
theorem exists_rat_mul_entries_mem {K : Set (Ad E)} (hK : ∀ x : Ad E, ∃ y : E, x - algebraMap E (Ad E) y ∈ K)
    {u : GA E a} (hu : u ∈ NA E a) (m : ℕ) :
    ∃ γ ∈ NE E a, ∀ i j : Fin a, i < j → (j : ℕ) < m → (γ * u).val i j ∈ K := by
  induction m with
  | zero => exact ⟨1, one_mem _, fun _ _ _ h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨γ, hγ, h⟩ := ih
    by_cases hm : m < a
    swap
    · exact ⟨γ, hγ, fun i j hij _ => h i j hij (by omega)⟩
    have hw : γ * u ∈ NA E a := mul_mem (NE_le hγ) hu
    obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hw
    choose y hy using fun i : Fin a => hK ((γ * u).val i ⟨m, hm⟩)
    refine ⟨ratGL E a (GlobalTheory.JSW.colGL m fun i => -y i) * γ, mul_mem ⟨_, (GlobalTheory.SmGL.mem_unipB E).2 ⟨fun i j hij => ?_, fun i => ?_⟩, rfl⟩ hγ,
      fun i j hij hj => ?_⟩
    · have : ¬ ((j : ℕ) = m ∧ (i : ℕ) < m) := by have : (j : ℕ) < i := hij; omega
      simp [GlobalTheory.JSW.colGL, this, hij.ne']
    · have : ¬ ((i : ℕ) = m ∧ (i : ℕ) < m) := by omega
      simp [GlobalTheory.JSW.colGL, this]
    · rw [mul_assoc]
      generalize γ * u = w at *
      have e : (ratGL E a (GlobalTheory.JSW.colGL m fun i => -y i) * w).val i j =
          w.val i j - if (i : ℕ) < m then algebraMap E (Ad E) (y i) * w.val ⟨m, hm⟩ j else 0 := by
        have e1 : (ratGL E a (GlobalTheory.JSW.colGL m fun i => -y i)).val = 1 + Matrix.of (fun i j : Fin a =>
            if j = ⟨m, hm⟩ then (if (i : ℕ) < m then -algebraMap E (Ad E) (y i) else 0) else 0) := by
          ext i j : 1
          change algebraMap E (Ad E) ((GlobalTheory.JSW.colGL m fun i => -y i).val i j) = _
          simp only [GlobalTheory.JSW.colGL, Matrix.add_apply, Matrix.of_apply, map_add, Matrix.one_apply, Fin.ext_iff]
          split_ifs <;> simp_all
        rw [Units.val_mul, e1, add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply]
        simp only [Matrix.of_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        split_ifs <;> ring
      rw [e]
      have hij' : (i : ℕ) < j := hij
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
      · rw [h1 ⟨m, hm⟩ j hj, mul_zero, ite_self, sub_zero]
        exact h i j hij hj
      · obtain rfl : j = ⟨m, hm⟩ := Fin.ext hj
        rw [if_pos hij', h2, mul_one]
        exact hy i

/- English proof (translation)
Take `⟨K, hK, hc⟩` from `GlobalTheory.AdeleCocompact.exists_compact_adele E`. Establish `hK' : IsCompact (insert 0 (insert 1 K))` using `(hK.insert 1).insert 0`. Establish `hM : IsCompact (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a => insert 0 (insert 1 K) : Set (Matrix (Fin a) (Fin a) (Ad E)))` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK'`. Establish `hcl : Topology.IsClosedEmbedding (Subtype.val : SpecialLinearGroup (Fin a) (Ad E) → Matrix (Fin a) (Fin a) (Ad E))` using `(isClosed_eq (continuous_id.matrix_det) continuous_const).isClosedEmbedding_subtypeVal`. Use `⟨_, (hcl.isCompact_preimage hM).image SpecialLinearGroup.continuous_toGL, fun u hu => ?_⟩` and prove the remaining obligations.

Take `⟨γ, hγ, h⟩` from `exists_rat_mul_entries_mem hc hu a`. Use `⟨γ, hγ, ?_⟩` and prove the remaining obligations. Take `⟨h1, h2⟩` from `(GlobalTheory.SmGL.mem_unipB _).1 (mul_mem (NE_le hγ) hu)`. Use `⟨⟨(γ * u).val, det_eq_one (mul_mem (NE_le hγ) hu)⟩, fun i _ j _ => ?_, Units.ext rfl⟩` and prove the remaining obligations. Break down `lt_trichotomy i j with hij | rfl | hij` into its components or cases.

Conclude with `.inr (.inr (h i j hij j.2))`. Conclude with `.inr (.inl (h2 i))`. Conclude with `.inl (h1 i j hij)`.
-/
theorem exists_isCompact_unip (E : Type) [Field E] [NumberField E] (a : ℕ) :
    ∃ D : Set (GA E a), IsCompact D ∧ ∀ u ∈ NA E a, ∃ γ ∈ NE E a, γ * u ∈ D := by
  obtain ⟨K, hK, hc⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele E
  have hK' : IsCompact (insert 0 (insert 1 K)) := (hK.insert 1).insert 0
  have hM : IsCompact (Set.univ.pi fun _ : Fin a => Set.univ.pi fun _ : Fin a => insert 0 (insert 1 K) :
      Set (Matrix (Fin a) (Fin a) (Ad E))) := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK'
  have hcl : Topology.IsClosedEmbedding (Subtype.val : SpecialLinearGroup (Fin a) (Ad E) → Matrix (Fin a) (Fin a) (Ad E)) :=
    (isClosed_eq (continuous_id.matrix_det) continuous_const).isClosedEmbedding_subtypeVal
  refine ⟨_, (hcl.isCompact_preimage hM).image SpecialLinearGroup.continuous_toGL, fun u hu => ?_⟩
  obtain ⟨γ, hγ, h⟩ := exists_rat_mul_entries_mem hc hu a
  refine ⟨γ, hγ, ?_⟩
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 (mul_mem (NE_le hγ) hu)
  refine ⟨⟨(γ * u).val, det_eq_one (mul_mem (NE_le hγ) hu)⟩, fun i _ j _ => ?_, Units.ext rfl⟩
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact .inr (.inr (h i j hij j.2))
  · exact .inr (.inl (h2 i))
  · exact .inl (h1 i j hij)

end Cocompact

section Decomposition

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Establish `h1` using `single_vecMul_rowGL (ℓ := ℓ) (y := k.val ℓ) h`. Establish `h2 : Pi.single ℓ 1 ᵥ* (k * (rowGL ℓ (k.val ℓ))⁻¹).val = Pi.single ℓ 1`. Rewrite using `[Units.val_mul, ← vecMul_vecMul, single_one_vecMul]`. Use `conv_lhs => enter [1]`. Rewrite using `[show k.val.row ℓ = k.val ℓ from rfl, ← h1]`.

Rewrite using `[vecMul_vecMul, Units.mul_inv, vecMul_one]`. Rewrite `h2` using `[single_one_vecMul]`. Conclude with `(congrFun h2 j).trans (Pi.single_apply _ _ _)`.
-/
theorem row_mul_inv_rowGL {R : Type} [CommRing R] {ℓ : Fin a} (k : GL (Fin a) R) (h : IsUnit (k.val ℓ ℓ)) (j : Fin a) :
    (k * (rowGL ℓ (k.val ℓ))⁻¹).val ℓ j = if j = ℓ then 1 else 0 := by
  have h1 := single_vecMul_rowGL (ℓ := ℓ) (y := k.val ℓ) h
  have h2 : Pi.single ℓ 1 ᵥ* (k * (rowGL ℓ (k.val ℓ))⁻¹).val = Pi.single ℓ 1 := by
    rw [Units.val_mul, ← vecMul_vecMul, single_one_vecMul]
    conv_lhs => enter [1]; rw [show k.val.row ℓ = k.val ℓ from rfl, ← h1]
    rw [vecMul_vecMul, Units.mul_inv, vecMul_one]
  rw [single_one_vecMul] at h2
  exact (congrFun h2 j).trans (Pi.single_apply _ _ _)

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, fun v _ => map_one _, fun U _ => one_mem U⟩`. Consider the case `insert w S hw ih`. Take `⟨h, h1, h2, h3⟩` from `ih`. Use `⟨locGL E a w (x w) * h, fun v hv => ?_, fun v hv => ?_, fun U hU => mul_mem (hU w (Finset.mem_insert_self _ _)) (h3 U fun v hv => hU v (Finset.mem_insert_of_mem hv))⟩` and prove the remaining obligations.

Break down `Finset.mem_insert.1 hv with rfl | hv` into its components or cases. Rewrite using `[map_mul, pLoc_locGL, h2 _ hw, mul_one]`. Rewrite using `[map_mul, pLoc_locGL_of_ne (fun e : v = w => hw (e ▸ hv)), h1 v hv, one_mul]`. Rewrite using `[map_mul, pLoc_locGL_of_ne (fun e : v = w => hv (Finset.mem_insert.2 (.inl e))), h2 v fun e => hv (Finset.mem_insert_of_mem e), mul_one]`.
-/
theorem exists_components (S : Finset (HeightOneSpectrum (𝓞 E)))
    (x : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin a) (v.adicCompletion E)) :
    ∃ h : GL (Fin a) (Af E), (∀ v ∈ S, GeneralLinearGroup.map (pLoc E v) h = x v) ∧
      (∀ v ∉ S, GeneralLinearGroup.map (pLoc E v) h = 1) ∧
      ∀ U : Subgroup (GL (Fin a) (Af E)), (∀ v ∈ S, locGL E a v (x v) ∈ U) → h ∈ U := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, fun v _ => map_one _, fun U _ => one_mem U⟩
  | insert w S hw ih =>
    obtain ⟨h, h1, h2, h3⟩ := ih
    refine ⟨locGL E a w (x w) * h, fun v hv => ?_, fun v hv => ?_, fun U hU =>
      mul_mem (hU w (Finset.mem_insert_self _ _)) (h3 U fun v hv => hU v (Finset.mem_insert_of_mem hv))⟩
    · rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [map_mul, pLoc_locGL, h2 _ hw, mul_one]
      · rw [map_mul, pLoc_locGL_of_ne (fun e : v = w => hw (e ▸ hv)), h1 v hv, one_mul]
    · rw [map_mul, pLoc_locGL_of_ne (fun e : v = w => hv (Finset.mem_insert.2 (.inl e))),
        h2 v fun e => hv (Finset.mem_insert_of_mem e), mul_one]

variable (E) in

def mirAt (ℓ : Fin a) (S : Finset (HeightOneSpectrum (𝓞 E))) : Set (GA E a) :=
  {p | (∀ j, p.val ℓ j = if j = ℓ then 1 else 0) ∧ ∀ v ∉ S, compV E a v p = 1}

variable (a) in

def levelAt (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) : Set (GL (Fin a) (Af E)) :=
  {κ | (∀ v, GeneralLinearGroup.map (pLoc E v) κ ∈ GlobalTheory.LFun.KGL v a) ∧ ∀ v ∈ S, ∀ i j,
    Valued.v ((κ.val - 1) i j v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))}

/- English proof (translation)
Simplify using `only [AdelicGLn.mem_integralFiniteGL_iff, mem_integralFiniteAdeles, mem_GLint_iff_entries_cell, ← map_inv]`. Conclude with `⟨fun h v => ⟨fun i j => h.1 i j v, fun i j => h.2 i j v⟩, fun h => ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩⟩`.
-/
theorem mem_integralFiniteGL_iff_KGL {κ : GL (Fin a) (Af E)} :
    κ ∈ AdelicGLn.integralFiniteGL E a ↔ ∀ v, GeneralLinearGroup.map (pLoc E v) κ ∈ GlobalTheory.LFun.KGL v a := by
  simp only [AdelicGLn.mem_integralFiniteGL_iff, mem_integralFiniteAdeles, mem_GLint_iff_entries_cell, ← map_inv]
  exact ⟨fun h v => ⟨fun i j => h.1 i j v, fun i j => h.2 i j v⟩, fun h => ⟨fun i j v => (h v).1 i j, fun i j v => (h v).2 i j⟩⟩

/- English proof (translation)
Introduce `_ hκ` and use `mem_integralFiniteGL_iff_KGL.2 hκ.1`.
-/
theorem levelAt_subset (S : Finset (HeightOneSpectrum (𝓞 E))) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) :
    levelAt a S J ⊆ AdelicGLn.integralFiniteGL E a := fun _ hκ => mem_integralFiniteGL_iff_KGL.2 hκ.1

/- English proof (translation)
Set `t : Finset (HeightOneSpectrum (𝓞 E)) × ℕ → Set (GL (Fin a) (Af E))` to `fun q => {κ | ∀ v ∈ q.1, ∀ i j, Valued.v ((κ.val - 1) i j v) ≤ WithZero.exp (-(q.2 : ℤ))}`. Establish `htc : ∀ q, IsClosed (t q)` using `fun q => by`. Simplify using `only [t, Set.ofPred_forall]`. Use `isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun i => isClosed_iInter fun j => ?_` and prove the remaining obligations. Establish `hc0 : Continuous fun κ : GL (Fin a) (Af E) => (κ.val - 1) i j` using `(Units.continuous_val.sub continuous_const).matrix_elem i j`.

Establish `hc1 : Continuous fun x : Af E => x v` using `RestrictedProduct.continuous_eval v`. Establish `hc : Continuous fun κ : GL (Fin a) (Af E) => (κ.val - 1) i j v` using `hc1.comp hc0`. Take `⟨π, hπ⟩` from `v.valuedAdicCompletion_surjective E (WithZero.exp (-(q.2 : ℤ)))`. Establish `hcl : IsClosed {x : v.adicCompletion E | Valued.v x ≤ WithZero.exp (-(q.2 : ℤ))}`. Use `Valued.isClosed_closedBall (v.adicCompletion E) (Valued.v.restrict π)` as an intermediate fact.

Simplify `this` using `only [Valuation.restrict_le_iff, hπ]`. Conclude with `hcl.preimage hc`. Establish `hd : Directed (· ⊇ ·) t` using `fun q q' => ⟨(q.1 ∪ q'.1, max q.2 q'.2), fun κ h v hv i j => (h v (Finset.mem_union_left _ hv) i j).trans (WithZero.exp_le_exp.2 (by simp)), fun κ h v hv i j => (h v (Finset.mem_union_right _ hv) i j).trans (WithZero.exp_le_exp.2 (by simp))⟩`. Take `⟨⟨T, m⟩, hT⟩` from `((AdelicGLn.isCompact_integralFiniteGL E a).diff hU).elim_directed_family_closed t htc (by`. Use `Set.eq_empty_of_forall_notMem fun κ ⟨h1, h2⟩ => h1.2 ?_` and prove the remaining obligations.

Establish `: κ = 1` using `Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_))`. Conclude with `this ▸ one_mem U`. Assume the negation of the conclusion as `h0`. Establish `h0' : Valued.v ((κ.val - 1) i j v) ≠ 0` using `(Valuation.ne_zero_iff _).2 h0`. Establish `h3` using `Set.mem_iInter.1 h2 ({v}, (1 - WithZero.log (Valued.v ((κ.val - 1) i j v))).toNat) v (Finset.mem_singleton_self _) i j`.

Rewrite `h3` using `[← WithZero.exp_log h0', WithZero.exp_le_exp, WithZero.log_exp]`. Use the proof step `omega) hd`. Establish `hne : ∀ v : HeightOneSpectrum (𝓞 E), ((v.asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ^ (m + 1) ≠ 0` using `fun v => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)`. Establish `hcount : ∀ v, FractionalIdeal.count E v (∏ w ∈ S, (w.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ (m + 1)) = if v ∈ S then ((m + 1 : ℕ) : ℤ) else 0` using `fun v => by`. Rewrite using `[FractionalIdeal.count_prod E v S _ fun w _ => hne w]`.

Simplify using `only [FractionalIdeal.count_pow, FractionalIdeal.count_maximal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq']`. Use `⟨Units.mk0 _ (Finset.prod_ne_zero_iff.2 fun w (_ : w ∈ S) => hne w), fun v hv => ?_, fun v hv => ?_, fun κ hκ => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk0, hcount, if_pos hv]`. Check the signs of the components of the expression. Rewrite using `[Units.val_mk0, hcount, if_neg hv]`.

Take `⟨h, h1, h2, h3⟩` from `exists_components (T \ S) fun v => GeneralLinearGroup.map (pLoc E v) κ`. Establish `hh : h ∈ U` using `h3 U fun v hv => hw v (Finset.mem_sdiff.1 hv).2 _ (hκ.1 v)`. Establish `e1 : ∀ v ∈ T \ S, GeneralLinearGroup.map (pLoc E v) (h⁻¹ * κ) = 1` using `fun v hv => by`. Rewrite using `[map_mul, map_inv, h1 v hv, inv_mul_cancel]`. Establish `e2 : ∀ v ∉ T \ S, GeneralLinearGroup.map (pLoc E v) (h⁻¹ * κ) = GeneralLinearGroup.map (pLoc E v) κ` using `fun v hv => by rw [map_mul, map_inv, h2 v hv, inv_one, one_mul]`.

Establish `e3 : ∀ (x : GL (Fin a) (Af E)) v i j, (x.val - 1) i j v = (GeneralLinearGroup.map (pLoc E v) x).val i j - pLoc E v ((1 : Matrix (Fin a) (Fin a) (Af E)) i j)` using `fun x v i j => map_sub (pLoc E v) _ _`. Assume the negation of the conclusion as `hn`. Use `Set.eq_empty_iff_forall_notMem.1 hT (h⁻¹ * κ) ⟨⟨mem_integralFiniteGL_iff_KGL.2 fun v => ?_, fun hm => hn ?_⟩, fun v hv i j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ T \ S`. Rewrite using `[e1 v hv]`.

Conclude with `one_mem _`. Rewrite using `[e2 v hv]`. Conclude with `hκ.1 v`. Simplify using `using mul_mem hh hm`. Distinguish the cases in `hv' : v ∈ T \ S`.

Rewrite using `[e3, e1 v hv', ← map_one (GeneralLinearGroup.map (n := Fin a) (pLoc E v)), ← e3]`. Simplify using the standard rewrite rules. Establish `hS : v ∈ S` using `by_contra fun hS => hv' (Finset.mem_sdiff.2 ⟨hv, hS⟩)`. Rewrite using `[e3, e2 v hv', ← e3]`. Use `(hκ.2 v hS i j).trans (WithZero.exp_le_exp.2 ?_)` and prove the remaining obligations.

Rewrite using `[Units.val_mk0, hcount, if_pos hS]`. Simplify using the standard rewrite rules.
-/
theorem exists_levelAt_subset (S : Finset (HeightOneSpectrum (𝓞 E))) (U : Subgroup (GL (Fin a) (Af E)))
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (hw : ∀ w ∉ S, ∀ k ∈ GlobalTheory.LFun.KGL w a, locGL E a w k ∈ U) :
    ∃ J : (FractionalIdeal (𝓞 E)⁰ E)ˣ, (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) ∧
      (∀ v ∉ S, FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E) = 0) ∧ levelAt a S J ⊆ U := by
  classical
  let t : Finset (HeightOneSpectrum (𝓞 E)) × ℕ → Set (GL (Fin a) (Af E)) := fun q =>
    {κ | ∀ v ∈ q.1, ∀ i j, Valued.v ((κ.val - 1) i j v) ≤ WithZero.exp (-(q.2 : ℤ))}
  have htc : ∀ q, IsClosed (t q) := fun q => by
    simp only [t, Set.ofPred_forall]
    refine isClosed_iInter fun v => isClosed_iInter fun _ => isClosed_iInter fun i => isClosed_iInter fun j => ?_
    have hc0 : Continuous fun κ : GL (Fin a) (Af E) => (κ.val - 1) i j :=
      (Units.continuous_val.sub continuous_const).matrix_elem i j
    have hc1 : Continuous fun x : Af E => x v := RestrictedProduct.continuous_eval v
    have hc : Continuous fun κ : GL (Fin a) (Af E) => (κ.val - 1) i j v := hc1.comp hc0
    obtain ⟨π, hπ⟩ := v.valuedAdicCompletion_surjective E (WithZero.exp (-(q.2 : ℤ)))
    have hcl : IsClosed {x : v.adicCompletion E | Valued.v x ≤ WithZero.exp (-(q.2 : ℤ))} := by
      have := Valued.isClosed_closedBall (v.adicCompletion E) (Valued.v.restrict π)
      simpa only [Valuation.restrict_le_iff, hπ] using this
    exact hcl.preimage hc
  have hd : Directed (· ⊇ ·) t := fun q q' => ⟨(q.1 ∪ q'.1, max q.2 q'.2),
    fun κ h v hv i j => (h v (Finset.mem_union_left _ hv) i j).trans (WithZero.exp_le_exp.2 (by simp)),
    fun κ h v hv i j => (h v (Finset.mem_union_right _ hv) i j).trans (WithZero.exp_le_exp.2 (by simp))⟩
  obtain ⟨⟨T, m⟩, hT⟩ := ((AdelicGLn.isCompact_integralFiniteGL E a).diff hU).elim_directed_family_closed t htc (by
    refine Set.eq_empty_of_forall_notMem fun κ ⟨h1, h2⟩ => h1.2 ?_
    have : κ = 1 := Units.ext (sub_eq_zero.1 (Matrix.ext fun i j => FiniteAdeleRing.ext _ fun v => ?_))
    · exact this ▸ one_mem U
    by_contra h0
    have h0' : Valued.v ((κ.val - 1) i j v) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h3 := Set.mem_iInter.1 h2 ({v}, (1 - WithZero.log (Valued.v ((κ.val - 1) i j v))).toNat) v
      (Finset.mem_singleton_self _) i j
    rw [← WithZero.exp_log h0', WithZero.exp_le_exp, WithZero.log_exp] at h3
    omega) hd
  have hne : ∀ v : HeightOneSpectrum (𝓞 E), ((v.asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ^ (m + 1) ≠ 0 := fun v =>
    pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  have hcount : ∀ v, FractionalIdeal.count E v (∏ w ∈ S, (w.asIdeal : FractionalIdeal (𝓞 E)⁰ E) ^ (m + 1)) =
      if v ∈ S then ((m + 1 : ℕ) : ℤ) else 0 := fun v => by
    rw [FractionalIdeal.count_prod E v S _ fun w _ => hne w]
    simp only [FractionalIdeal.count_pow, FractionalIdeal.count_maximal, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq']
  refine ⟨Units.mk0 _ (Finset.prod_ne_zero_iff.2 fun w (_ : w ∈ S) => hne w), fun v hv => ?_, fun v hv => ?_,
    fun κ hκ => ?_⟩
  · rw [Units.val_mk0, hcount, if_pos hv]; positivity
  · rw [Units.val_mk0, hcount, if_neg hv]
  obtain ⟨h, h1, h2, h3⟩ := exists_components (T \ S) fun v => GeneralLinearGroup.map (pLoc E v) κ
  have hh : h ∈ U := h3 U fun v hv => hw v (Finset.mem_sdiff.1 hv).2 _ (hκ.1 v)
  have e1 : ∀ v ∈ T \ S, GeneralLinearGroup.map (pLoc E v) (h⁻¹ * κ) = 1 := fun v hv => by
    rw [map_mul, map_inv, h1 v hv, inv_mul_cancel]
  have e2 : ∀ v ∉ T \ S, GeneralLinearGroup.map (pLoc E v) (h⁻¹ * κ) = GeneralLinearGroup.map (pLoc E v) κ :=
    fun v hv => by rw [map_mul, map_inv, h2 v hv, inv_one, one_mul]
  have e3 : ∀ (x : GL (Fin a) (Af E)) v i j, (x.val - 1) i j v =
      (GeneralLinearGroup.map (pLoc E v) x).val i j - pLoc E v ((1 : Matrix (Fin a) (Fin a) (Af E)) i j) :=
    fun x v i j => map_sub (pLoc E v) _ _
  by_contra hn
  refine Set.eq_empty_iff_forall_notMem.1 hT (h⁻¹ * κ) ⟨⟨mem_integralFiniteGL_iff_KGL.2 fun v => ?_, fun hm => hn ?_⟩,
    fun v hv i j => ?_⟩
  · by_cases hv : v ∈ T \ S
    · rw [e1 v hv]; exact one_mem _
    · rw [e2 v hv]; exact hκ.1 v
  · simpa using mul_mem hh hm
  · by_cases hv' : v ∈ T \ S
    · rw [e3, e1 v hv', ← map_one (GeneralLinearGroup.map (n := Fin a) (pLoc E v)), ← e3]
      simp
    · have hS : v ∈ S := by_contra fun hS => hv' (Finset.mem_sdiff.2 ⟨hv, hS⟩)
      rw [e3, e2 v hv', ← e3]
      refine (hκ.2 v hS i j).trans (WithZero.exp_le_exp.2 ?_)
      rw [Units.val_mk0, hcount, if_pos hS]
      simp

/- English proof (translation)
Establish `h1 : Valued.v (y ℓ) = 1`. Use `h ℓ` as an intermediate fact. Rewrite `this` using `[if_pos rfl]`. Simplify using `using Valuation.map_one_add_of_lt _ this`. Establish `h2 : ∀ j, y j ∈ v.adicCompletionIntegers E` using `fun j => by`.

Distinguish the cases in `hj : j = ℓ`. Conclude with `hj ▸ h1.le`. Use `h j` as an intermediate fact. Rewrite `this` using `[if_neg hj, sub_zero]`. Conclude with `this.le`.

Establish `h0 : y ℓ ≠ 0` using `fun e => by simp [e] at h1`. Establish `h3 : IsUnit (⟨y ℓ, h2 ℓ⟩ : (v.adicCompletionIntegers E).toSubring)` using `IsUnit.of_mul_eq_one ⟨(y ℓ)⁻¹, show Valued.v (y ℓ)⁻¹ ≤ 1 by rw [map_inv₀, h1, inv_one]⟩ (Subtype.ext (mul_inv_cancel₀ h0))`. Use `⟨h0.isUnit, rowGL ℓ fun j => ⟨y j, h2 j⟩, Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[val_rowGL h0.isUnit]`. Use extensionality with `i j : 1`.

Express the relevant statement in the definitionally equal form `(((rowGL ℓ fun j => (⟨y j, h2 j⟩ : (v.adicCompletionIntegers E).toSubring)).val i j : (v.adicCompletionIntegers E).toSubring) : v.adicCompletion E) = _`. Rewrite using `[val_rowGL h3]`. Distinguish the cases in `hi : i = ℓ`. Substitute `hi` using the available equality. Simplify using `[rowMat]`.

Simplify using `[rowMat, hi, Matrix.one_apply, apply_ite Subtype.val]`.
-/
theorem rowGL_mem_KGL {v : HeightOneSpectrum (𝓞 E)} {ℓ : Fin a} {y : Fin a → v.adicCompletion E}
    (h : ∀ j, Valued.v (y j - if j = ℓ then 1 else 0) < 1) : IsUnit (y ℓ) ∧ rowGL ℓ y ∈ GlobalTheory.LFun.KGL v a := by
  have h1 : Valued.v (y ℓ) = 1 := by
    have := h ℓ
    rw [if_pos rfl] at this
    simpa using Valuation.map_one_add_of_lt _ this
  have h2 : ∀ j, y j ∈ v.adicCompletionIntegers E := fun j => by
    by_cases hj : j = ℓ
    · exact hj ▸ h1.le
    · have := h j
      rw [if_neg hj, sub_zero] at this
      exact this.le
  have h0 : y ℓ ≠ 0 := fun e => by simp [e] at h1
  have h3 : IsUnit (⟨y ℓ, h2 ℓ⟩ : (v.adicCompletionIntegers E).toSubring) :=
    IsUnit.of_mul_eq_one ⟨(y ℓ)⁻¹, show Valued.v (y ℓ)⁻¹ ≤ 1 by rw [map_inv₀, h1, inv_one]⟩
      (Subtype.ext (mul_inv_cancel₀ h0))
  refine ⟨h0.isUnit, rowGL ℓ fun j => ⟨y j, h2 j⟩, Units.ext ?_⟩
  rw [val_rowGL h0.isUnit]
  ext i j : 1
  change (((rowGL ℓ fun j => (⟨y j, h2 j⟩ : (v.adicCompletionIntegers E).toSubring)).val i j :
    (v.adicCompletionIntegers E).toSubring) : v.adicCompletion E) = _
  rw [val_rowGL h3]
  by_cases hi : i = ℓ
  · subst hi; simp [rowMat]
  · simp [rowMat, hi, Matrix.one_apply, apply_ite Subtype.val]

/- English proof (translation)
Take `⟨h1, h2⟩` from `(GlobalTheory.SmGL.mem_unipB _).1 hu`. Rewrite using `[Units.val_mul, ← vecMul_vecMul, single_one_vecMul (M := u.val)]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Break down `(hℓ j).eq_or_lt with rfl | hj` into its components or cases.

Simplify using `using h2 j`. Simplify `h1 ℓ j hj` using `[hj.ne]`.
-/
theorem single_vecMul_unip {ℓ : Fin a} (hℓ : ∀ i, i ≤ ℓ) {u : GA E a} (hu : u ∈ NA E a) (g : GA E a) :
    Pi.single ℓ 1 ᵥ* (u * g).val = Pi.single ℓ 1 ᵥ* g.val := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  rw [Units.val_mul, ← vecMul_vecMul, single_one_vecMul (M := u.val)]
  congr 1
  funext j
  rcases (hℓ j).eq_or_lt with rfl | hj
  · simpa using h2 j
  · simpa [hj.ne] using h1 ℓ j hj

variable [IsTotallyComplex E]

/- English proof (translation)
Take `⟨u, hu, k, hk, rfl⟩` from `hg`. Rewrite `hi`, `hf`, the goal using `[single_vecMul_unip hℓ hu, single_one_vecMul]`. Establish `hk' : ∀ v ∉ S, compV E a v k ∈ GlobalTheory.LFun.KGL v a`. Simplify `hk` using `only [US, Subgroup.mem_iInf, Subgroup.mem_comap]`. Establish `hc : ∀ v (x : GA E a), compV E a v x = GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) x)` using `fun _ _ => rfl`.

Establish `hf' : ∀ v ∈ S, ∀ j, Valued.v ((compV E a v k).val ℓ j - if j = ℓ then 1 else 0) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))` using `fun v hv j => by`. Use `hf v hv j using 2` and compare the differences between its conclusion and the goal. Express the relevant statement in the definitionally equal form `_ = pLoc E v (_ - _)`. Rewrite using `[map_sub, Pi.single_apply, apply_ite (pLoc E v), map_one, map_zero]`. Both sides reduce to the same expression.

Establish `hr` using `fun v hv => rowGL_mem_KGL (ℓ := ℓ) (y := (compV E a v k).val ℓ) fun j => (hf' v hv j).trans_lt (by`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Conclude with `neg_neg_of_pos (hJ v hv))`. Take `⟨h, h1, h2, -⟩` from `exists_components S fun v => rowGL ℓ ((compV E a v k).val ℓ) * (compV E a v k)⁻¹`. Use `set κ := h * GeneralLinearGroup.map (pFin E) k with hκ`.

Establish `k1 : ∀ v ∈ S, GeneralLinearGroup.map (pLoc E v) κ = rowGL ℓ ((compV E a v k).val ℓ)` using `fun v hv => by`. Rewrite using `[hκ, map_mul, h1 v hv, ← hc, inv_mul_cancel_right]`. Establish `k2 : ∀ v ∉ S, GeneralLinearGroup.map (pLoc E v) κ = compV E a v k` using `fun v hv => by`. Rewrite using `[hκ, map_mul, h2 v hv, ← hc, one_mul]`. Use `set s := infGL E a (rowGL ℓ fun i => pInf E (k.val.row ℓ i)) with hs`.

Establish `p1 : ∀ v, compV E a v (k * s⁻¹ * (finGL E a κ)⁻¹) = compV E a v k * (GeneralLinearGroup.map (pLoc E v) κ)⁻¹` using `fun v => by`. Rewrite using `[map_mul, map_mul, map_inv, map_inv, hc v s, hc v (finGL E a κ), hs, pFin_infGL, pFin_finGL, map_one, inv_one, mul_one]`. Establish `p2 : ∀ v ∉ S, compV E a v (k * s⁻¹ * (finGL E a κ)⁻¹) = 1` using `fun v hv => by rw [p1, k2 v hv, mul_inv_cancel]`. Use `⟨u, hu, k * s⁻¹ * (finGL E a κ)⁻¹, ⟨fun j => ad_ext ?_ (FiniteAdeleRing.ext _ fun v => ?_), p2⟩, κ, ⟨fun v => ?_, fun v hv i j => ?_⟩, by group⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(GeneralLinearGroup.map (pInf E) (k * s⁻¹ * (finGL E a κ)⁻¹)).val ℓ j = _`.

Rewrite using `[map_mul, map_mul, map_inv, map_inv, hs, pInf_infGL, pInf_finGL, inv_one, mul_one, apply_ite (pInf E), map_one, map_zero]`. Conclude with `row_mul_inv_rowGL (GeneralLinearGroup.map (pInf E) k) (isUnit_of_mem_rowSet hi) j`. Express the relevant statement in the definitionally equal form `(compV E a v (k * s⁻¹ * (finGL E a κ)⁻¹)).val ℓ j = (pLoc E v).comp (pFin E) _`. Rewrite using `[apply_ite ((pLoc E v).comp (pFin E)), map_one, map_zero]`. Distinguish the cases in `hv : v ∈ S`.

Rewrite using `[p1, k1 v hv]`. Conclude with `row_mul_inv_rowGL _ (hr v hv).1 j`. Rewrite using `[p2 v hv]`. Simplify using `[Matrix.one_apply, eq_comm]`. Distinguish the cases in `hv : v ∈ S`.

Rewrite using `[k1 v hv]`. Conclude with `(hr v hv).2`. Rewrite using `[k2 v hv]`. Conclude with `hk' v hv`. Establish `e : (κ.val - 1) i j v = (GeneralLinearGroup.map (pLoc E v) κ).val i j - if i = j then 1 else 0`.

Express the relevant statement in the definitionally equal form `pLoc E v (_ - _) = _`. Rewrite using `[map_sub, Matrix.one_apply, apply_ite (pLoc E v), map_one, map_zero]`. Both sides reduce to the same expression. Rewrite using `[e, k1 v hv, val_rowGL (hr v hv).1]`. Distinguish the cases in `hi : i = ℓ`.

Substitute `hi` using the available equality. Simplify `hf' v hv j` using `[rowMat, eq_comm]`. Simplify using `[rowMat, hi, Matrix.one_apply]`.
-/
theorem exists_decomp {ℓ : Fin a} (hℓ : ∀ i, i ≤ ℓ) {S : Finset (HeightOneSpectrum (𝓞 E))}
    {J : (FractionalIdeal (𝓞 E)⁰ E)ˣ} (hJ : ∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))
    {g : GA E a} (hg : g ∈ C0 E a S) (hi : (fun i => pInf E ((Pi.single ℓ 1 ᵥ* g.val) i)) ∈ rowSet E ℓ)
    (hf : ∀ v ∈ S, ∀ j, Valued.v ((pFin E ((Pi.single ℓ 1 ᵥ* g.val) j) - (Pi.single ℓ 1 : Fin a → Af E) j) v) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) :
    ∃ u ∈ NA E a, ∃ p ∈ mirAt E ℓ S, ∃ κ ∈ levelAt a S J,
      g * (infGL E a (rowGL ℓ fun i => pInf E ((Pi.single ℓ 1 ᵥ* g.val) i)))⁻¹ = u * p * finGL E a κ := by
  obtain ⟨u, hu, k, hk, rfl⟩ := hg
  rw [single_vecMul_unip hℓ hu, single_one_vecMul] at hi hf ⊢
  have hk' : ∀ v ∉ S, compV E a v k ∈ GlobalTheory.LFun.KGL v a := by
    simpa only [US, Subgroup.mem_iInf, Subgroup.mem_comap] using hk
  have hc : ∀ v (x : GA E a), compV E a v x = GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) x) :=
    fun _ _ => rfl
  have hf' : ∀ v ∈ S, ∀ j, Valued.v ((compV E a v k).val ℓ j - if j = ℓ then 1 else 0) ≤
      WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := fun v hv j => by
    convert hf v hv j using 2
    change _ = pLoc E v (_ - _)
    rw [map_sub, Pi.single_apply, apply_ite (pLoc E v), map_one, map_zero]
    rfl
  have hr := fun v hv => rowGL_mem_KGL (ℓ := ℓ) (y := (compV E a v k).val ℓ) fun j => (hf' v hv j).trans_lt (by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    exact neg_neg_of_pos (hJ v hv))
  obtain ⟨h, h1, h2, -⟩ := exists_components S fun v => rowGL ℓ ((compV E a v k).val ℓ) * (compV E a v k)⁻¹
  set κ := h * GeneralLinearGroup.map (pFin E) k with hκ
  have k1 : ∀ v ∈ S, GeneralLinearGroup.map (pLoc E v) κ = rowGL ℓ ((compV E a v k).val ℓ) := fun v hv => by
    rw [hκ, map_mul, h1 v hv, ← hc, inv_mul_cancel_right]
  have k2 : ∀ v ∉ S, GeneralLinearGroup.map (pLoc E v) κ = compV E a v k := fun v hv => by
    rw [hκ, map_mul, h2 v hv, ← hc, one_mul]
  set s := infGL E a (rowGL ℓ fun i => pInf E (k.val.row ℓ i)) with hs
  have p1 : ∀ v, compV E a v (k * s⁻¹ * (finGL E a κ)⁻¹) = compV E a v k * (GeneralLinearGroup.map (pLoc E v) κ)⁻¹ :=
    fun v => by
      rw [map_mul, map_mul, map_inv, map_inv, hc v s, hc v (finGL E a κ), hs, pFin_infGL, pFin_finGL, map_one, inv_one,
        mul_one]
  have p2 : ∀ v ∉ S, compV E a v (k * s⁻¹ * (finGL E a κ)⁻¹) = 1 := fun v hv => by rw [p1, k2 v hv, mul_inv_cancel]
  refine ⟨u, hu, k * s⁻¹ * (finGL E a κ)⁻¹, ⟨fun j => ad_ext ?_ (FiniteAdeleRing.ext _ fun v => ?_), p2⟩, κ,
    ⟨fun v => ?_, fun v hv i j => ?_⟩, by group⟩
  · change (GeneralLinearGroup.map (pInf E) (k * s⁻¹ * (finGL E a κ)⁻¹)).val ℓ j = _
    rw [map_mul, map_mul, map_inv, map_inv, hs, pInf_infGL, pInf_finGL, inv_one, mul_one, apply_ite (pInf E), map_one,
      map_zero]
    exact row_mul_inv_rowGL (GeneralLinearGroup.map (pInf E) k) (isUnit_of_mem_rowSet hi) j
  · change (compV E a v (k * s⁻¹ * (finGL E a κ)⁻¹)).val ℓ j = (pLoc E v).comp (pFin E) _
    rw [apply_ite ((pLoc E v).comp (pFin E)), map_one, map_zero]
    by_cases hv : v ∈ S
    · rw [p1, k1 v hv]
      exact row_mul_inv_rowGL _ (hr v hv).1 j
    · rw [p2 v hv]
      simp [Matrix.one_apply, eq_comm]
  · by_cases hv : v ∈ S
    · rw [k1 v hv]; exact (hr v hv).2
    · rw [k2 v hv]; exact hk' v hv
  · have e : (κ.val - 1) i j v = (GeneralLinearGroup.map (pLoc E v) κ).val i j - if i = j then 1 else 0 := by
      change pLoc E v (_ - _) = _
      rw [map_sub, Matrix.one_apply, apply_ite (pLoc E v), map_one, map_zero]
      rfl
    rw [e, k1 v hv, val_rowGL (hr v hv).1]
    by_cases hi : i = ℓ
    · subst hi
      simpa [rowMat, eq_comm] using hf' v hv j
    · simp [rowMat, hi, Matrix.one_apply]

end Decomposition

section Main

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

omit [IsTotallyComplex E] in
/- English proof (translation)
Use `Continuous.units_map _ (continuous_const.add (continuous_pi fun i => continuous_pi fun j => ?_))` and prove the remaining obligations. Conclude with `(continuous_const.prodMk (continuous_apply_apply i j) : Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => ((0, x i j) : InfiniteAdeleRing E × Af E))`.
-/
theorem continuous_finGL : Continuous (finGL E a) := by
  refine Continuous.units_map _ (continuous_const.add (continuous_pi fun i => continuous_pi fun j => ?_))
  exact (continuous_const.prodMk (continuous_apply_apply i j) :
    Continuous fun x : Matrix (Fin a) (Fin a) (Af E) => ((0, x i j) : InfiniteAdeleRing E × Af E))

end Main

/- English proof (translation)
Introduce `E _ _ n μ _ S 𝓕 h𝓕 B hc hB0 hB1 hN ⟨K, hK, hs⟩`. Take `⟨D, hD, hDu⟩` from `exists_isCompact_unip E n`. Use `haveI := GlobalTheory.ThetaUnfold.countable_range_ratGL (E := E) (a := n)`. Use `haveI : Countable (NE E n) := (Subgroup.inclusion_injective (Subgroup.map_le_range (ratGL E n) _)).countable`. Take `⟨i1, i2, i3⟩` from `integral_family_pos μ (NE E n) h𝓕 (isOpen_adelicUnipotentTimesIntegralOutsideSet E n S) (hD.mul hK) (fun γ hγ g hg => adelicUnitriangular_mul_mem_unipotentTimesIntegral (NE_le hγ) hg) hc hB0 (fun x γ hγ => hN x γ (NE_le hγ)) (fun x g hg h0 => by`.

Take `⟨u, hu, hk⟩` from `hs x g hg h0`. Take `⟨γ, hγ, hd⟩` from `hDu _ (inv_mem hu)`. Conclude with `⟨γ, hγ, _, hd, _, hk, by group⟩)`. Use `fun x => ⟨1, ⟨1, one_mem _, 1, one_mem _, (mul_one _).symm⟩, (hB1 x).ne'⟩`. Establish `e : ∀ x, ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ = ENNReal.ofReal (∫ g in 𝓕 ∩ C0 E n S, B x g ∂μ)` using `fun x => (ofReal_integral_eq_lintegral_ofReal (i1 x) (.of_forall (hB0 x))).symm`.

Simplify using `only [e]`. Conclude with `⟨fun x => ⟨ENNReal.ofReal_pos.2 (i3 x), ENNReal.ofReal_lt_top⟩, i2.congr fun x => (ENNReal.toReal_ofReal (i3 x).le).symm⟩`.
-/
theorem lintegral_cell_pos_lt_top_continuous : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (μ : Measure (GA E n)) [μ.IsHaarMeasure] (S : Finset (HeightOneSpectrum (𝓞 E))) (𝓕 : Set (GA E n)), IsFundamentalDomain (NE E n) 𝓕 μ → ∀ B : ℝ → GA E n → ℝ, Continuous (Function.uncurry B) → (∀ x g, 0 ≤ B x g) → (∀ x, 0 < B x 1) → (∀ x, ∀ u ∈ NA E n, ∀ g, B x (u * g) = B x g) → (∃ K : Set (GA E n), IsCompact K ∧ ∀ x g, g ∈ C0 E n S → B x g ≠ 0 → ∃ u ∈ NA E n, u * g ∈ K) → (∀ x, 0 < ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ ∧ ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ < ⊤) ∧ Continuous fun x => (∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ).toReal := by
  intro E _ _ n μ _ S 𝓕 h𝓕 B hc hB0 hB1 hN ⟨K, hK, hs⟩
  obtain ⟨D, hD, hDu⟩ := exists_isCompact_unip E n
  haveI := GlobalTheory.ThetaUnfold.countable_range_ratGL (E := E) (a := n)
  haveI : Countable (NE E n) := (Subgroup.inclusion_injective (Subgroup.map_le_range (ratGL E n) _)).countable
  obtain ⟨i1, i2, i3⟩ := integral_family_pos μ (NE E n) h𝓕 (isOpen_adelicUnipotentTimesIntegralOutsideSet E n S) (hD.mul hK)
    (fun γ hγ g hg => adelicUnitriangular_mul_mem_unipotentTimesIntegral (NE_le hγ) hg) hc hB0 (fun x γ hγ => hN x γ (NE_le hγ))
    (fun x g hg h0 => by
      obtain ⟨u, hu, hk⟩ := hs x g hg h0
      obtain ⟨γ, hγ, hd⟩ := hDu _ (inv_mem hu)
      exact ⟨γ, hγ, _, hd, _, hk, by group⟩)
    fun x => ⟨1, ⟨1, one_mem _, 1, one_mem _, (mul_one _).symm⟩, (hB1 x).ne'⟩
  have e : ∀ x, ∫⁻ g in 𝓕 ∩ C0 E n S, ENNReal.ofReal (B x g) ∂μ = ENNReal.ofReal (∫ g in 𝓕 ∩ C0 E n S, B x g ∂μ) :=
    fun x => (ofReal_integral_eq_lintegral_ofReal (i1 x) (.of_forall (hB0 x))).symm
  simp only [e]
  exact ⟨fun x => ⟨ENNReal.ofReal_pos.2 (i3 x), ENNReal.ofReal_lt_top⟩,
    i2.congr fun x => (ENNReal.toReal_ofReal (i3 x).le).symm⟩

end GlobalTheory.RSLocalPart
