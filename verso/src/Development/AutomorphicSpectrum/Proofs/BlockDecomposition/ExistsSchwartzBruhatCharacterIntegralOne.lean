import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
import GroundTheory.AutomorphicForms.LocallyProfinite

noncomputable section

open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob Topology

namespace GlobalTheory.CompanionTheory.FrobNz

/- English proof (translation)
Establish `h1 : u ^ 2 - 1 = (u - 1) * (u + 1)` using `by ring`. Establish `h4 : ‖(2:ℂ)‖ ≤ ‖u + 1‖ + ‖u - 1‖`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : ‖(2:ℂ)‖ = 2` using `by simp`. Establish `h2 : (3:ℝ)/2 ≤ ‖u + 1‖` using `by linarith`.

Rewrite using `[h1, norm_mul]`. Use polynomial arithmetic with `[norm_nonneg (u - 1), mul_le_mul_of_nonneg_left h2 (norm_nonneg (u - 1))]`.
-/
private theorem three_halves_norm_sub_one_le_norm_sq_sub_one (u : ℂ) (hu : ‖u - 1‖ < 1/2) :
    3/2 * ‖u - 1‖ ≤ ‖u ^ 2 - 1‖ := by
  have h1 : u ^ 2 - 1 = (u - 1) * (u + 1) := by ring
  have h4 : ‖(2:ℂ)‖ ≤ ‖u + 1‖ + ‖u - 1‖ := by
    calc ‖(2:ℂ)‖ = ‖(u + 1) - (u - 1)‖ := by congr 1; ring
      _ ≤ ‖u + 1‖ + ‖u - 1‖ := norm_sub_le _ _
  have h5 : ‖(2:ℂ)‖ = 2 := by simp
  have h2 : (3:ℝ)/2 ≤ ‖u + 1‖ := by linarith
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (u - 1), mul_le_mul_of_nonneg_left h2 (norm_nonneg (u - 1))]

/- English proof (translation)
Establish `key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖w - 1‖ ≤ ‖w ^ (2 ^ n) - 1‖`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Establish `e : w ^ (2 ^ (n + 1)) = (w ^ (2 ^ n)) ^ 2` using `by rw [pow_succ, pow_mul]`. Rewrite using `[e]`. Establish `h3` using `three_halves_norm_sub_one_le_norm_sq_sub_one (w ^ (2 ^ n)) (hw n)`. Combine the equalities or inequalities in the displayed calculation. Assume the negation of the conclusion as `hne`.

Establish `hd : 0 < ‖w - 1‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt (1/2 / ‖w - 1‖) (by norm_num : (1:ℝ) < 3/2)`. Establish `h1` using `key n`. Establish `h2` using `hw n`. Rewrite `hn` using `[div_lt_iff₀ hd]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem eq_one_of_forall_norm_pow_two_pow_sub_one_lt' (w : ℂ) (hw : ∀ n : ℕ, ‖w ^ (2 ^ n) - 1‖ < 1/2) :
    w = 1 := by
  have key : ∀ n : ℕ, (3/2 : ℝ) ^ n * ‖w - 1‖ ≤ ‖w ^ (2 ^ n) - 1‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : w ^ (2 ^ (n + 1)) = (w ^ (2 ^ n)) ^ 2 := by rw [pow_succ, pow_mul]
      rw [e]
      have h3 := three_halves_norm_sub_one_le_norm_sq_sub_one (w ^ (2 ^ n)) (hw n)
      calc (3/2 : ℝ) ^ (n + 1) * ‖w - 1‖ = 3/2 * ((3/2) ^ n * ‖w - 1‖) := by ring
        _ ≤ 3/2 * ‖w ^ (2 ^ n) - 1‖ := by linarith
        _ ≤ ‖(w ^ (2 ^ n)) ^ 2 - 1‖ := h3
  by_contra hne
  have hd : 0 < ‖w - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (1/2 / ‖w - 1‖) (by norm_num : (1:ℝ) < 3/2)
  have h1 := key n
  have h2 := hw n
  rw [div_lt_iff₀ hd] at hn
  linarith

/- English proof (translation)
Set `V : Set G` to `{g | ‖(χ g : ℂ) - 1‖ < 1/2}`. Establish `hVo : IsOpen V` using `isOpen_lt ((hχ.sub continuous_const).norm) continuous_const`. Establish `h1V : (1 : G) ∈ V` using `by show ‖((χ 1 : ℂˣ) : ℂ) - 1‖ < 1/2`. Simplify using the standard rewrite rules. Take `⟨N, hNc, hN1⟩` from `exists_compact_mem_nhds (1 : G)`.

Establish `hW : interior N ∩ V ∈ 𝓝 (1 : G)` using `Filter.inter_mem (interior_mem_nhds.mpr hN1) (hVo.mem_nhds h1V)`. Take `⟨s, hs, h1s, hsW⟩` from `(loc_compact_Haus_tot_disc_of_zero_dim (H := G)).mem_nhds_iff.mp hW`. Establish `hsclo : IsClopen s` using `hs`. Establish `hsc : IsCompact s` using `hNc.of_isClosed_subset hsclo.isClosed (hsW.trans (Set.inter_subset_left.trans interior_subset))`. Take `⟨W, hW1, hWs⟩` from `compact_open_separated_mul_right hsc hsclo.isOpen subset_rfl`.

Set `H : Subgroup G` to `{ carrier := {g | ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s} mul_mem' := by`. Introduce `a b ha hb`. Express the relevant statement in the definitionally equal form `∀ x ∈ s, x * a ∈ s ∧ x * a⁻¹ ∈ s at ha`. Express the relevant statement in the definitionally equal form `∀ x ∈ s, x * b ∈ s ∧ x * b⁻¹ ∈ s at hb`. Express the relevant statement in the definitionally equal form `∀ x ∈ s, x * (a * b) ∈ s ∧ x * (a * b)⁻¹ ∈ s`.

Introduce `x hx`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Conclude with `(hb _ (ha x hx).1).1`. Rewrite using `[mul_inv_rev, ← mul_assoc]`.

Conclude with `(ha _ (hb x hx).2).2`. Use the proof step `one_mem' := by`. Express the relevant statement in the definitionally equal form `∀ x ∈ s, x * 1 ∈ s ∧ x * 1⁻¹ ∈ s`. Introduce `x hx`. Simplify using `[hx]`.

Use the proof step `inv_mem' := by`. Introduce `a ha`. Express the relevant statement in the definitionally equal form `∀ x ∈ s, x * a ∈ s ∧ x * a⁻¹ ∈ s at ha`. Express the relevant statement in the definitionally equal form `∀ x ∈ s, x * a⁻¹ ∈ s ∧ x * a⁻¹⁻¹ ∈ s`. Introduce `x hx`.

Rewrite using `[inv_inv]`. Conclude with `⟨(ha x hx).2, (ha x hx).1⟩ }`. Establish `hHn : (H : Set G) ∈ 𝓝 (1 : G)`. Establish `hWW : W ∩ W⁻¹ ∈ 𝓝 (1 : G)` using `Filter.inter_mem hW1 (inv_mem_nhds_one G hW1)`. Use `Filter.mem_of_superset hWW ?_` and prove the remaining obligations.

Introduce and unpack `g ⟨hg, hg'⟩`. Use `show ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s`. Introduce `x hx`. Conclude with `⟨hWs (Set.mul_mem_mul hx hg), hWs (Set.mul_mem_mul hx (Set.mem_inv.mp hg'))⟩`. Establish `hHo : IsOpen (H : Set G)` using `Subgroup.isOpen_of_mem_nhds H hHn`.

Establish `hHs : (H : Set G) ⊆ s`. Introduce `g hg`. Establish `hg' : ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s` using `hg`. Simplify using `using (hg' 1 h1s).1`. Establish `hHc : IsCompact (H : Set G)` using `hsc.of_isClosed_subset (Subgroup.isClosed_of_isOpen H hHo) hHs`.

Use `⟨⟨H, hHo⟩, hHc, ?_⟩` and prove the remaining obligations. Introduce `k hk`. Establish `hkH : k ∈ H` using `hk`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.val_one]`.

Apply `eq_one_of_forall_norm_pow_two_pow_sub_one_lt'` to reduce the goal to its premises. Introduce `n`. Establish `hmem : k ^ (2 ^ n) ∈ H` using `H.pow_mem hkH _`. Establish `hV : k ^ (2 ^ n) ∈ V` using `(hsW (hHs hmem)).2`. Establish `hV' : ‖((χ (k ^ (2 ^ n)) : ℂˣ) : ℂ) - 1‖ < 1/2` using `hV`.

Simplify `hV'` using `[map_pow, Units.val_pow_eq_pow_val]`.
-/
theorem exists_compact_open_subgroup_trivial {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    (χ : G →* ℂˣ) (hχ : Continuous (fun g => (χ g : ℂ))) :
    ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ ∀ k ∈ K, χ k = 1 := by
  let V : Set G := {g | ‖(χ g : ℂ) - 1‖ < 1/2}
  have hVo : IsOpen V := isOpen_lt ((hχ.sub continuous_const).norm) continuous_const
  have h1V : (1 : G) ∈ V := by
    show ‖((χ 1 : ℂˣ) : ℂ) - 1‖ < 1/2
    simp
  obtain ⟨N, hNc, hN1⟩ := exists_compact_mem_nhds (1 : G)
  have hW : interior N ∩ V ∈ 𝓝 (1 : G) :=
    Filter.inter_mem (interior_mem_nhds.mpr hN1) (hVo.mem_nhds h1V)
  obtain ⟨s, hs, h1s, hsW⟩ := (loc_compact_Haus_tot_disc_of_zero_dim (H := G)).mem_nhds_iff.mp hW
  have hsclo : IsClopen s := hs
  have hsc : IsCompact s :=
    hNc.of_isClosed_subset hsclo.isClosed
      (hsW.trans (Set.inter_subset_left.trans interior_subset))
  obtain ⟨W, hW1, hWs⟩ := compact_open_separated_mul_right hsc hsclo.isOpen subset_rfl
  let H : Subgroup G :=
    { carrier := {g | ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s}
      mul_mem' := by
        intro a b ha hb
        change ∀ x ∈ s, x * a ∈ s ∧ x * a⁻¹ ∈ s at ha
        change ∀ x ∈ s, x * b ∈ s ∧ x * b⁻¹ ∈ s at hb
        change ∀ x ∈ s, x * (a * b) ∈ s ∧ x * (a * b)⁻¹ ∈ s
        intro x hx
        refine ⟨?_, ?_⟩
        · rw [← mul_assoc]; exact (hb _ (ha x hx).1).1
        · rw [mul_inv_rev, ← mul_assoc]; exact (ha _ (hb x hx).2).2
      one_mem' := by
        change ∀ x ∈ s, x * 1 ∈ s ∧ x * 1⁻¹ ∈ s
        intro x hx
        simp [hx]
      inv_mem' := by
        intro a ha
        change ∀ x ∈ s, x * a ∈ s ∧ x * a⁻¹ ∈ s at ha
        change ∀ x ∈ s, x * a⁻¹ ∈ s ∧ x * a⁻¹⁻¹ ∈ s
        intro x hx
        rw [inv_inv]
        exact ⟨(ha x hx).2, (ha x hx).1⟩ }
  have hHn : (H : Set G) ∈ 𝓝 (1 : G) := by
    have hWW : W ∩ W⁻¹ ∈ 𝓝 (1 : G) := Filter.inter_mem hW1 (inv_mem_nhds_one G hW1)
    refine Filter.mem_of_superset hWW ?_
    rintro g ⟨hg, hg'⟩
    show ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s
    intro x hx
    exact ⟨hWs (Set.mul_mem_mul hx hg), hWs (Set.mul_mem_mul hx (Set.mem_inv.mp hg'))⟩
  have hHo : IsOpen (H : Set G) := Subgroup.isOpen_of_mem_nhds H hHn
  have hHs : (H : Set G) ⊆ s := by
    intro g hg
    have hg' : ∀ x ∈ s, x * g ∈ s ∧ x * g⁻¹ ∈ s := hg
    simpa using (hg' 1 h1s).1
  have hHc : IsCompact (H : Set G) :=
    hsc.of_isClosed_subset (Subgroup.isClosed_of_isOpen H hHo) hHs
  refine ⟨⟨H, hHo⟩, hHc, ?_⟩
  intro k hk
  have hkH : k ∈ H := hk
  apply Units.ext
  rw [Units.val_one]
  apply eq_one_of_forall_norm_pow_two_pow_sub_one_lt'
  intro n
  have hmem : k ^ (2 ^ n) ∈ H := H.pow_mem hkH _
  have hV : k ^ (2 ^ n) ∈ V := (hsW (hHs hmem)).2
  have hV' : ‖((χ (k ^ (2 ^ n)) : ℂˣ) : ℂ) - 1‖ < 1/2 := hV
  simpa [map_pow, Units.val_pow_eq_pow_val] using hV'

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ χ hχ`. Take `⟨K, hKc, hKχ⟩` from `exists_compact_open_subgroup_trivial χ hχ`. Establish `hKo : IsOpen (K : Set G)` using `K.isOpen`. Establish `hKcl : IsClosed (K : Set G)` using `K.isClosed`. Establish `hKm : MeasurableSet (K : Set G)` using `hKo.measurableSet`.

Establish `hpos : 0 < μ (K : Set G)` using `hKo.measure_pos μ ⟨1, one_mem K⟩`. Establish `hfin : μ (K : Set G) < ⊤` using `hKc.measure_lt_top`. Establish `hr : (μ (K : Set G)).toReal ≠ 0` using `ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩`. Establish `hlc : ∀ c : ℂ, IsLocallyConstant ((K : Set G).indicator (fun _ => c))`. Introduce `c s`.

Apply the tactic sequence `by_cases hc : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s`. Use `isOpen_univ using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Apply the tactic sequence `by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]`. Use `hKo using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Apply the tactic sequence `by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]`. Use `hKcl.isOpen_compl using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Apply the tactic sequence `by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]`.

Use `isOpen_empty using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Apply the tactic sequence `by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]`. Use `⟨⟨(K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹), ?_⟩, ?_⟩` and prove the remaining obligations. Use `show IsLocallyConstant _ ∧ HasCompactSupport _`.

Conclude with `⟨hlc _, HasCompactSupport.intro hKc (fun x hx => Set.indicator_of_notMem hx _)⟩`. Establish `key : ∀ x, (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x * (χ x : ℂ) = (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x`. Introduce `x`. Distinguish the cases in `hx : x ∈ (K : Set G)`. Rewrite using `[hKχ x hx, Units.val_one, mul_one]`.

Rewrite using `[Set.indicator_of_notMem hx, zero_mul]`. Use `show ∫ x, (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x * (χ x : ℂ) ∂μ = 1`. Simplify using `only [key]`. Rewrite using `[integral_indicator_const _ hKm]`. Simplify using `[Measure.real, hpos.ne', hfin.ne, hr]`.
-/
theorem exists_SB_integral_mul_char_eq_one : ∀ (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (χ : G →* ℂˣ),
    Continuous (fun g => (χ g : ℂ)) → ∃ α : SB G, ∫ x, (α : G → ℂ) x * (χ x : ℂ) ∂μ = 1 := by
  intro G _ _ _ _ _ _ _ _ μ _ χ hχ
  obtain ⟨K, hKc, hKχ⟩ := exists_compact_open_subgroup_trivial χ hχ
  have hKo : IsOpen (K : Set G) := K.isOpen
  have hKcl : IsClosed (K : Set G) := K.isClosed
  have hKm : MeasurableSet (K : Set G) := hKo.measurableSet
  have hpos : 0 < μ (K : Set G) := hKo.measure_pos μ ⟨1, one_mem K⟩
  have hfin : μ (K : Set G) < ⊤ := hKc.measure_lt_top
  have hr : (μ (K : Set G)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hpos.ne', hfin.ne⟩
  have hlc : ∀ c : ℂ, IsLocallyConstant ((K : Set G).indicator (fun _ => c)) := by
    intro c s
    by_cases hc : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
    · convert isOpen_univ using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
    · convert hKo using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
    · convert hKcl.isOpen_compl using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
    · convert isOpen_empty using 1
      ext x
      by_cases hx : x ∈ (K : Set G) <;> simp [Set.indicator, hx, hc, h0]
  refine ⟨⟨(K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹), ?_⟩, ?_⟩
  · show IsLocallyConstant _ ∧ HasCompactSupport _
    exact ⟨hlc _,
      HasCompactSupport.intro hKc (fun x hx => Set.indicator_of_notMem hx _)⟩
  · have key : ∀ x, (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x * (χ x : ℂ) =
        (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x := by
      intro x
      by_cases hx : x ∈ (K : Set G)
      · rw [hKχ x hx, Units.val_one, mul_one]
      · rw [Set.indicator_of_notMem hx, zero_mul]
    show ∫ x, (K : Set G).indicator (fun _ => (((μ (K : Set G)).toReal : ℂ))⁻¹) x * (χ x : ℂ) ∂μ = 1
    simp only [key]
    rw [integral_indicator_const _ hKm]
    simp [Measure.real, hpos.ne', hfin.ne, hr]

end GlobalTheory.CompanionTheory.FrobNz
