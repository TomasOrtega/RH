import Mathlib

open scoped ContDiff

namespace GlobalTheory.GaussCoset

/- English proof (translation)
Establish `hsq : 0 ≤ (2 * c * t - (R + 1)) ^ 2 / (4 * c)` using `by positivity`. Establish `hid : (2 * c * t - (R + 1)) ^ 2 / (4 * c) = (R + 1) ^ 2 / (4 * c) - t - (-c * t ^ 2 + R * t)`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : Real.exp (-c * t ^ 2 + R * t) ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t)`.

Rewrite using `[← Real.exp_add]`. Conclude with `Real.exp_le_exp.mpr (by linarith)`. Establish `h2 : Real.exp (-t) ≤ (n.factorial : ℝ) * t⁻¹ ^ n`. Establish `hpos : 0 < t ^ n / (n.factorial : ℝ)` using `by positivity`. Establish `hle : t ^ n / (n.factorial : ℝ) ≤ Real.exp t` using `Real.pow_div_factorial_le_exp t ht.le n`.

Rewrite using `[Real.exp_neg, inv_pow, ← div_eq_mul_inv, ← inv_div]`. Conclude with `inv_anti₀ hpos hle`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exp_le_inv_pow {c : ℝ} (hc : 0 < c) (R : ℝ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-c * t ^ 2 + R * t) ≤
      ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by
  have hsq : 0 ≤ (2 * c * t - (R + 1)) ^ 2 / (4 * c) := by positivity
  have hid : (2 * c * t - (R + 1)) ^ 2 / (4 * c) =
      (R + 1) ^ 2 / (4 * c) - t - (-c * t ^ 2 + R * t) := by
    field_simp
    ring
  have h1 : Real.exp (-c * t ^ 2 + R * t) ≤
      Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-t) ≤ (n.factorial : ℝ) * t⁻¹ ^ n := by
    have hpos : 0 < t ^ n / (n.factorial : ℝ) := by positivity
    have hle : t ^ n / (n.factorial : ℝ) ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le n
    rw [Real.exp_neg, inv_pow, ← div_eq_mul_inv, ← inv_div]
    exact inv_anti₀ hpos hle
  calc Real.exp (-c * t ^ 2 + R * t)
      ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * Real.exp (-t) := h1
    _ ≤ Real.exp ((R + 1) ^ 2 / (4 * c)) * ((n.factorial : ℝ) * t⁻¹ ^ n) := by gcongr
    _ = ((n.factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c))) * t⁻¹ ^ n := by ring

/- English proof (translation)
Establish `hmaj` using `(ZLattice.summable_norm_sub_inv_pow L (Module.finrank ℤ L + 1) (Nat.lt_succ_self _) x).mul_left (((Module.finrank ℤ L + 1).factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c)))`. Use `Summable.of_norm_bounded_eventually hmaj ?_` and prove the remaining obligations. Establish `hfin : {z : L | (z : V) = x}.Finite`. Apply `Set.Subsingleton.finite` to reduce the goal to its premises. Introduce `a ha b hb`.

Conclude with `Subtype.ext (ha.trans hb.symm)`. Use `filter_upwards [hfin.compl_mem_cofinite] with z hz`. Establish `hne : (z : V) ≠ x` using `hz`. Establish `hpos : 0 < ‖(z : V) - x‖` using `norm_pos_iff.mpr (sub_ne_zero.mpr hne)`. Rewrite using `[Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]`.

Conclude with `exp_le_inv_pow hc R (Module.finrank ℤ L + 1) hpos`.
-/
theorem summable_lattice {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L] {c : ℝ} (hc : 0 < c)
    (R : ℝ) (x : V) :
    Summable fun z : L => Real.exp (-c * ‖(z : V) - x‖ ^ 2 + R * ‖(z : V) - x‖) := by
  have hmaj := (ZLattice.summable_norm_sub_inv_pow L (Module.finrank ℤ L + 1)
    (Nat.lt_succ_self _) x).mul_left
      (((Module.finrank ℤ L + 1).factorial : ℝ) * Real.exp ((R + 1) ^ 2 / (4 * c)))
  refine Summable.of_norm_bounded_eventually hmaj ?_
  have hfin : {z : L | (z : V) = x}.Finite := by
    apply Set.Subsingleton.finite
    intro a ha b hb
    exact Subtype.ext (ha.trans hb.symm)
  filter_upwards [hfin.compl_mem_cofinite] with z hz
  have hne : (z : V) ≠ x := hz
  have hpos : 0 < ‖(z : V) - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact exp_le_inv_pow hc R (Module.finrank ℤ L + 1) hpos

/- English proof (translation)
Rewrite using `[discreteTopology_iff_isOpen_singleton_zero]`. Establish `hU : IsOpen (Metric.ball (0 : V) 1 ∩ ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ)` using `Metric.isOpen_ball.inter (h.subset Set.sdiff_subset).isClosed.isOpen_compl`. Establish `hset : ({0} : Set L) = Subtype.val ⁻¹' (Metric.ball (0 : V) 1 ∩ ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ)`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce `hz`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality. Simplify using the standard rewrite rules. Introduce and unpack `⟨h1, h2⟩`.

Rewrite using `[Set.mem_singleton_iff]`. Assume the negation of the conclusion as `hne`. Establish `h1' : ‖(z : V)‖ < 1` using `by simpa using h1`. Apply `h2` to reduce the goal to its premises. Use `⟨⟨z.2, h1'.le⟩, ?_⟩` and prove the remaining obligations.

Introduce `hz0`. Apply `hne` to reduce the goal to its premises. Simplify using `using hz0`. Rewrite using `[hset]`. Conclude with `hU.preimage continuous_subtype_val`.
-/
theorem discrete_of_finite {V : Type} [NormedAddCommGroup V] (L : AddSubgroup V)
    (h : {v : V | v ∈ L ∧ ‖v‖ ≤ 1}.Finite) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hU : IsOpen (Metric.ball (0 : V) 1 ∩ ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ) :=
    Metric.isOpen_ball.inter (h.subset Set.sdiff_subset).isClosed.isOpen_compl
  have hset : ({0} : Set L) = Subtype.val ⁻¹' (Metric.ball (0 : V) 1 ∩
      ({v : V | v ∈ L ∧ ‖v‖ ≤ 1} \ {0})ᶜ) := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      simp
    · rintro ⟨h1, h2⟩
      rw [Set.mem_singleton_iff]
      by_contra hne
      have h1' : ‖(z : V)‖ < 1 := by simpa using h1
      apply h2
      refine ⟨⟨z.2, h1'.le⟩, ?_⟩
      intro hz0
      apply hne
      simpa using hz0
  rw [hset]
  exact hU.preimage continuous_subtype_val

/- English proof (translation)
Introduce `G V _ _ _ _ p Γ U hinj hfin c hc R w y`. Distinguish the cases in `hS : ∃ g₀ : Γ, (g₀ : G) + w ∈ U`. Use `swap`. Simplify using `only [not_exists] at hS`. Establish `hzero : (fun g : Γ => Set.indicator (U : Set G) (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w)) = 0`.

Use function extensionality and compare the values at `g`. Conclude with `Set.indicator_of_notMem (hS g) _`. Rewrite using `[hzero]`. Conclude with `summable_zero`. Take `⟨g₀, hg₀⟩` from `hS`.

Take `⟨L, hL⟩ : ∃ L : Submodule ℤ V, ∀ v, v ∈ L ↔ v ∈ (Γ ⊓ U).map p` from `⟨((Γ ⊓ U).map p).toIntSubmodule, fun _ => Iff.rfl⟩`. Establish `hfin1 : {v : V | v ∈ L.toAddSubgroup ∧ ‖v‖ ≤ 1}.Finite`. Use `((hfin 1).image p).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨hv, hv1⟩`. Rewrite `hv` using `[Submodule.mem_toAddSubgroup, hL]`.

Take `⟨g, hg, rfl⟩` from `AddSubgroup.mem_map.mp hv`. Take `⟨hgΓ, hgU⟩` from `AddSubgroup.mem_inf.mp hg`. Conclude with `⟨g, ⟨hgΓ, hgU, hv1⟩, rfl⟩`. Establish `: DiscreteTopology L` using `discrete_of_finite L.toAddSubgroup hfin1`. Set `S` to `{g : Γ // (g : G) + w ∈ U}`.

Establish `hmem : ∀ s : S, p ((s.1 : G) - g₀) ∈ L`. Introduce `s`. Rewrite using `[hL]`. Use `AddSubgroup.mem_map_of_mem p (AddSubgroup.mem_inf.mpr ⟨Γ.sub_mem s.1.2 g₀.2, ?_⟩)` and prove the remaining obligations. Establish `hd` using `U.sub_mem s.2 hg₀`.

Rewrite `hd` using `[add_sub_add_right_eq_sub]`. Then use the resulting hypothesis. Set `φ : S → L` to `fun s => ⟨p ((s.1 : G) - g₀), hmem s⟩`. Establish `hφ : Function.Injective φ`. Introduce `s t hst`. Establish `h1 : p ((s.1 : G) - g₀) = p ((t.1 : G) - g₀)` using `congrArg Subtype.val hst`.

Establish `h2 : p ((s.1 : G) - t.1) = p ((s.1 : G) - g₀) - p ((t.1 : G) - g₀)`. Rewrite using `[← map_sub]`. Use `congr 1`. Normalize the expressions using the abelian group laws. Rewrite `h2` using `[h1, sub_self]`.

Establish `h3` using `hinj _ (Γ.sub_mem s.1.2 t.1.2) h2`. Conclude with `Subtype.ext (Subtype.ext (sub_eq_zero.mp h3))`. Set `F : Γ → ℝ` to `fun g => Set.indicator (U : Set G) (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w)`. Use `show Summable F`. Establish `hL' : Summable fun z : L => Real.exp (-c * ‖(z : V) - -(p g₀ + y)‖ ^ 2 + R * ‖(z : V) - -(p g₀ + y)‖)` using `summable_lattice L hc R _`.

Establish `hcomp : Summable (F ∘ (Subtype.val : S → Γ))`. Establish `heq : F ∘ (Subtype.val : S → Γ) = (fun z : L => Real.exp (-c * ‖(z : V) - -(p g₀ + y)‖ ^ 2 + R * ‖(z : V) - -(p g₀ + y)‖)) ∘ φ`. Use function extensionality and compare the values at `s`. Establish `hshift : ((φ s : L) : V) - -(p g₀ + y) = p (s.1 : G) + y` using `by show p ((s.1 : G) - g₀) - -(p g₀ + y) = p (s.1 : G) + y`. Rewrite using `[map_sub]`.

Normalize the expressions using the abelian group laws. Simplify using `only [Function.comp_apply, F]`. Rewrite using `[Set.indicator_of_mem (show (s.1 : G) + w ∈ (U : Set G) from s.2), hshift]`. Rewrite using `[heq]`. Conclude with `hL'.comp_injective hφ`.

Use `(Function.Injective.summable_iff Subtype.val_injective ?_).mp hcomp` and prove the remaining obligations. Introduce `g hg`. Establish `hnot : (g : G) + w ∉ (U : Set G)` using `fun h => hg ⟨⟨g, h⟩, rfl⟩`. Conclude with `Set.indicator_of_notMem hnot _`.
-/
theorem summable_gaussian_coset : ∀ (G V : Type) [AddCommGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (Γ U : AddSubgroup G), (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U ∧ ‖p g‖ ≤ R}.Finite) → ∀ (c : ℝ), 0 < c → ∀ (R : ℝ) (w : G) (y : V), Summable fun g : Γ => Set.indicator (U : Set G) (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w) := by
  intro G V _ _ _ _ p Γ U hinj hfin c hc R w y
  by_cases hS : ∃ g₀ : Γ, (g₀ : G) + w ∈ U
  swap
  · simp only [not_exists] at hS
    have hzero : (fun g : Γ => Set.indicator (U : Set G)
        (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w)) = 0 := by
      funext g
      exact Set.indicator_of_notMem (hS g) _
    rw [hzero]
    exact summable_zero
  obtain ⟨g₀, hg₀⟩ := hS
  obtain ⟨L, hL⟩ : ∃ L : Submodule ℤ V, ∀ v, v ∈ L ↔ v ∈ (Γ ⊓ U).map p :=
    ⟨((Γ ⊓ U).map p).toIntSubmodule, fun _ => Iff.rfl⟩
  have hfin1 : {v : V | v ∈ L.toAddSubgroup ∧ ‖v‖ ≤ 1}.Finite := by
    refine ((hfin 1).image p).subset ?_
    rintro v ⟨hv, hv1⟩
    rw [Submodule.mem_toAddSubgroup, hL] at hv
    obtain ⟨g, hg, rfl⟩ := AddSubgroup.mem_map.mp hv
    obtain ⟨hgΓ, hgU⟩ := AddSubgroup.mem_inf.mp hg
    exact ⟨g, ⟨hgΓ, hgU, hv1⟩, rfl⟩
  have : DiscreteTopology L := discrete_of_finite L.toAddSubgroup hfin1
  let S := {g : Γ // (g : G) + w ∈ U}
  have hmem : ∀ s : S, p ((s.1 : G) - g₀) ∈ L := by
    intro s
    rw [hL]
    refine AddSubgroup.mem_map_of_mem p (AddSubgroup.mem_inf.mpr ⟨Γ.sub_mem s.1.2 g₀.2, ?_⟩)
    have hd := U.sub_mem s.2 hg₀
    rwa [add_sub_add_right_eq_sub] at hd
  let φ : S → L := fun s => ⟨p ((s.1 : G) - g₀), hmem s⟩
  have hφ : Function.Injective φ := by
    intro s t hst
    have h1 : p ((s.1 : G) - g₀) = p ((t.1 : G) - g₀) := congrArg Subtype.val hst
    have h2 : p ((s.1 : G) - t.1) = p ((s.1 : G) - g₀) - p ((t.1 : G) - g₀) := by
      rw [← map_sub]
      congr 1
      abel
    rw [h1, sub_self] at h2
    have h3 := hinj _ (Γ.sub_mem s.1.2 t.1.2) h2
    exact Subtype.ext (Subtype.ext (sub_eq_zero.mp h3))
  let F : Γ → ℝ := fun g => Set.indicator (U : Set G)
    (fun _ => Real.exp (-c * ‖p g + y‖ ^ 2 + R * ‖p g + y‖)) ((g : G) + w)
  show Summable F
  have hL' : Summable fun z : L =>
      Real.exp (-c * ‖(z : V) - -(p g₀ + y)‖ ^ 2 + R * ‖(z : V) - -(p g₀ + y)‖) :=
    summable_lattice L hc R _
  have hcomp : Summable (F ∘ (Subtype.val : S → Γ)) := by
    have heq : F ∘ (Subtype.val : S → Γ) = (fun z : L =>
        Real.exp (-c * ‖(z : V) - -(p g₀ + y)‖ ^ 2 + R * ‖(z : V) - -(p g₀ + y)‖)) ∘ φ := by
      funext s
      have hshift : ((φ s : L) : V) - -(p g₀ + y) = p (s.1 : G) + y := by
        show p ((s.1 : G) - g₀) - -(p g₀ + y) = p (s.1 : G) + y
        rw [map_sub]
        abel
      simp only [Function.comp_apply, F]
      rw [Set.indicator_of_mem (show (s.1 : G) + w ∈ (U : Set G) from s.2), hshift]
    rw [heq]
    exact hL'.comp_injective hφ
  refine (Function.Injective.summable_iff Subtype.val_injective ?_).mp hcomp
  intro g hg
  have hnot : (g : G) + w ∉ (U : Set G) := fun h => hg ⟨⟨g, h⟩, rfl⟩
  exact Set.indicator_of_notMem hnot _

end GlobalTheory.GaussCoset
