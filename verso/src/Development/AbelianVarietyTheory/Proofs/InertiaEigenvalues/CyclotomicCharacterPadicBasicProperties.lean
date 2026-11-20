import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Use `haveI : NeZero ((l ^ m : ℕ) : Om l) := ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Conclude with `HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)`.
-/
theorem exists_primRoot_pow (m : ℕ) : ∃ ζ : Om l, IsPrimitiveRoot ζ (l ^ m) := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero ((l ^ m : ℕ) : Om l) := ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (l ^ m)

/- English proof (translation)
Establish `: x - z = (x - y) + (y - z)` using `by ring`. Rewrite using `[this]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)`.
-/
theorem padic_norm_sub_le_trans {x y z : ℚ_[l]} {r : ℝ} (h1 : ‖x - y‖ ≤ r) (h2 : ‖y - z‖ ≤ r) :
    ‖x - z‖ ≤ r := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

/- English proof (translation)
Rewrite using `[← Padic.norm_int_le_pow_iff_dvd]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem norm_nat_sub_one_le_iff (a m : ℕ) :
    ‖(a : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) ↔ ((l : ℤ) ^ m) ∣ (a : ℤ) - 1 := by
  rw [← Padic.norm_int_le_pow_iff_dvd]
  push_cast
  rfl

/- English proof (translation)
Take `⟨a, ha, hga⟩` from `h g m ζ hζ.pow_eq_one`. Use `padic_norm_sub_le_trans ha ?_` and prove the remaining obligations. Rewrite using `[norm_nat_sub_one_le_iff]`. Establish `h0 : ζ ≠ 0` using `hζ.ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)`. Establish `h1 : ζ ^ ((a : ℤ) - 1) = 1`.

Rewrite using `[zpow_sub₀ h0, zpow_natCast, ← hga, hg, zpow_one, div_self h0]`. Use `(hζ.zpow_eq_one_iff_dvd _).1 h1` as an intermediate fact. Conclude with `this` after adjusting the coercions.
-/
theorem IsCyc.norm_sub_one_le_of_prim {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) (m : ℕ)
    {ζ : Om l} (hζ : IsPrimitiveRoot ζ (l ^ m)) (hg : g ζ = ζ) :
    ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  obtain ⟨a, ha, hga⟩ := h g m ζ hζ.pow_eq_one
  refine padic_norm_sub_le_trans ha ?_
  rw [norm_nat_sub_one_le_iff]
  have h0 : ζ ≠ 0 := hζ.ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  have h1 : ζ ^ ((a : ℤ) - 1) = 1 := by
    rw [zpow_sub₀ h0, zpow_natCast, ← hga, hg, zpow_one, div_self h0]
  have := (hζ.zpow_eq_one_iff_dvd _).1 h1
  exact_mod_cast this

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg`. Take `⟨ζ, hζ⟩` from `exists_primRoot_pow (l := l) m`. Conclude with `h.norm_sub_one_le_of_prim g m hζ (hg ζ hζ.pow_eq_one)`. Introduce `hg ζ hζ`.

Take `⟨a, ha, hga⟩` from `h g m ζ hζ`. Rewrite `ha` using `[norm_sub_rev]`. Take `⟨c, hc⟩` from `(norm_nat_sub_one_le_iff a m).1 (padic_norm_sub_le_trans ha hg)`. Establish `h0 : ζ ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hζ` using `[zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]`. Conclude with `zero_ne_one hζ`. Establish `ha' : (a : ℤ) = ((l ^ m : ℕ) : ℤ) * c + 1` using `by push_cast; linarith`. Rewrite using `[hga, ← zpow_natCast, ha', zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, one_mul, zpow_one]`.
-/
theorem IsCyc.fix_iff {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) (m : ℕ) :
    (∀ ζ : Om l, ζ ^ (l ^ m) = 1 → g ζ = ζ) ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
  constructor
  · intro hg
    obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) m
    exact h.norm_sub_one_le_of_prim g m hζ (hg ζ hζ.pow_eq_one)
  · intro hg ζ hζ
    obtain ⟨a, ha, hga⟩ := h g m ζ hζ
    rw [norm_sub_rev] at ha
    obtain ⟨c, hc⟩ := (norm_nat_sub_one_le_iff a m).1 (padic_norm_sub_le_trans ha hg)
    have h0 : ζ ≠ 0 := by
      rintro rfl
      rw [zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hζ
      exact zero_ne_one hζ
    have ha' : (a : ℤ) = ((l ^ m : ℕ) : ℤ) * c + 1 := by push_cast; linarith
    rw [hga, ← zpow_natCast, ha', zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, one_mul,
      zpow_one]

/- English proof (translation)
Take `⟨a, ha, -⟩` from `h g 0 1 (one_pow _)`. Establish `h2 : ‖(a : ℚ_[l]) - 0‖ ≤ 1`. Rewrite using `[sub_zero]`. Conclude with `IsUltrametricDist.norm_natCast_le_one _ _`. Simplify using `only [Nat.cast_zero, neg_zero, zpow_zero] at ha`.

Simplify using `using padic_norm_sub_le_trans ha h2`.
-/
theorem IsCyc.norm_le_one {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l])‖ ≤ 1 := by
  obtain ⟨a, ha, -⟩ := h g 0 1 (one_pow _)
  have h2 : ‖(a : ℚ_[l]) - 0‖ ≤ 1 := by
    rw [sub_zero]; exact IsUltrametricDist.norm_natCast_le_one _ _
  simp only [Nat.cast_zero, neg_zero, zpow_zero] at ha
  simpa using padic_norm_sub_le_trans ha h2

/- English proof (translation)
Establish `h1` using `h.norm_le_one g`. Establish `h2` using `h.norm_le_one g⁻¹`. Establish `h3 : ‖(χ g : ℚ_[l])‖ * ‖(χ g⁻¹ : ℚ_[l])‖ = 1`. Rewrite using `[← norm_mul, ← Units.val_mul, ← map_mul]`. Simplify using the standard rewrite rules.

Establish `h4` using `norm_nonneg (χ g : ℚ_[l])`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem IsCyc.norm_eq_one {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) (g : GQ l) :
    ‖(χ g : ℚ_[l])‖ = 1 := by
  have h1 := h.norm_le_one g
  have h2 := h.norm_le_one g⁻¹
  have h3 : ‖(χ g : ℚ_[l])‖ * ‖(χ g⁻¹ : ℚ_[l])‖ = 1 := by
    rw [← norm_mul, ← Units.val_mul, ← map_mul]; simp
  have h4 := norm_nonneg (χ g : ℚ_[l])
  nlinarith

/- English proof (translation)
The claim follows from `PadicInt.exists_pow_neg_lt l hε`.
-/
theorem exists_zpow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ m : ℕ, (l : ℝ) ^ (-(m : ℤ)) < ε :=
  PadicInt.exists_pow_neg_lt l hε

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Continuous ((Units.coeHom ℚ_[l]).comp χ)`. Apply `continuous_of_continuousAt_one` to reduce the goal to its premises. Rewrite using `[ContinuousAt, Metric.tendsto_nhds]`. Introduce `ε hε`. Take `⟨m, hm⟩` from `exists_zpow_neg_lt (l := l) hε`.

Take `⟨ζ, hζ⟩` from `exists_primRoot_pow (l := l) m`. Rewrite using `[Filter.Eventually, krullTopology_mem_nhds_one_iff]`. Use `⟨IntermediateField.adjoin ℚ_[l] {ζ}, IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ), ?_⟩` and prove the remaining obligations. Introduce `g hg`. Establish `hg' : g ζ = ζ` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ (IntermediateField.mem_adjoin_simple_self _ _)`.

Use `h.norm_sub_one_le_of_prim g m hζ hg'` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq, map_one, dist_eq_norm]`. Conclude with `this.trans_lt hm`.
-/
theorem IsCyc.continuous {χ : GQ l →* ℚ_[l]ˣ} (h : IsCyc χ) :
    Continuous (fun g => (χ g : ℚ_[l])) := by
  change Continuous ((Units.coeHom ℚ_[l]).comp χ)
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hε
  obtain ⟨ζ, hζ⟩ := exists_primRoot_pow (l := l) m
  rw [Filter.Eventually, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin ℚ_[l] {ζ},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ), ?_⟩
  intro g hg
  have hg' : g ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg ζ
    (IntermediateField.mem_adjoin_simple_self _ _)
  have := h.norm_sub_one_le_of_prim g m hζ hg'
  simp only [Set.mem_setOf_eq, map_one, dist_eq_norm]
  exact this.trans_lt hm

/- English proof (translation)
Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hg x hx`. Conclude with `hg x (IntermediateField.subset_adjoin _ _ hx)`. Introduce `hg x hx`.

Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem x hx => exact hg x hx`. Consider the case `algebraMap x => exact g.commutes x`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`. Consider the case `inv x _ hx => rw [map_inv₀, hx]`.

Consider the case `mul x y _ _ hx hy => rw [map_mul, hx, hy]`.
-/
theorem mem_fixingSubgroup_adjoin_iff (S : Set (Om l)) (g : GQ l) :
    g ∈ (IntermediateField.adjoin ℚ_[l] S).fixingSubgroup ↔ ∀ x ∈ S, g x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg x hx
    exact hg x (IntermediateField.subset_adjoin _ _ hx)
  · intro hg x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx => exact hg x hx
    | algebraMap x => exact g.commutes x
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]

/- English proof (translation)
Introduce `l _ χ h`. Use `⟨h.norm_eq_one, h.continuous, fun K g hg => ⟨fun j => ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Gj, Ks, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf, mem_fixingSubgroup_adjoin_iff, ← h.fix_iff]`. Conclude with `⟨fun h => h.2, fun h => ⟨hg, h⟩⟩`. Rewrite using `[Hinf, Kinf, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf, mem_fixingSubgroup_adjoin_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h2⟩`. Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖(χ g : ℚ_[l]) - 1‖`. Rewrite using `[norm_pos_iff, sub_ne_zero]`.

Conclude with `fun e => hne (Units.ext e)`. Take `⟨m, hm⟩` from `exists_zpow_neg_lt (l := l) hpos`. Conclude with `absurd ((h.fix_iff g m).1 fun ζ hζ => h2 ζ ⟨m, hζ⟩) (not_le.2 hm)`. Introduce `h1`. Use `⟨hg, ?_⟩` and prove the remaining obligations.

Introduce and unpack `x ⟨m, hx⟩`. Use `(h.fix_iff g m).2 ?_ x hx` and prove the remaining obligations. Rewrite using `[h1, Units.val_one, sub_self, norm_zero]`. Check the signs of the components of the expression.
-/
theorem cyc_basic : ∀ (l : ℕ) [Fact l.Prime] (χ : GQ l →* ℚ_[l]ˣ), IsCyc χ → (∀ g, ‖(χ g : ℚ_[l])‖ = 1) ∧ Continuous (fun g => (χ g : ℚ_[l])) ∧ ∀ (K : FinExt l) (g : GQ l), g ∈ (K0 K).fixingSubgroup → ((∀ j : ℕ, g ∈ Gj K j ↔ ‖(χ g : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-(j : ℤ))) ∧ (g ∈ Hinf K ↔ χ g = 1)) := by
  intro l _ χ h
  refine ⟨h.norm_eq_one, h.continuous, fun K g hg => ⟨fun j => ?_, ?_⟩⟩
  · rw [Gj, Ks, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
      mem_fixingSubgroup_adjoin_iff, ← h.fix_iff]
    exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
  · rw [Hinf, Kinf, IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
      mem_fixingSubgroup_adjoin_iff]
    constructor
    · rintro ⟨-, h2⟩
      by_contra hne
      have hpos : 0 < ‖(χ g : ℚ_[l]) - 1‖ := by
        rw [norm_pos_iff, sub_ne_zero]
        exact fun e => hne (Units.ext e)
      obtain ⟨m, hm⟩ := exists_zpow_neg_lt (l := l) hpos
      exact absurd ((h.fix_iff g m).1 fun ζ hζ => h2 ζ ⟨m, hζ⟩) (not_le.2 hm)
    · intro h1
      refine ⟨hg, ?_⟩
      rintro x ⟨m, hx⟩
      refine (h.fix_iff g m).2 ?_ x hx
      rw [h1, Units.val_one, sub_self, norm_zero]
      positivity

end GlobalTheory.Cyc
