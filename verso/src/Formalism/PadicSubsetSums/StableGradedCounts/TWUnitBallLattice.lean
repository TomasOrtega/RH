import Mathlib
import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral

open Module

namespace Formalism.IrreducibleCountingLemmas.TW

namespace UnitBall

variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]

noncomputable abbrev ballRing (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] :
    ValuationSubring K :=
  (NormedField.valuation (K := K)).valuationSubring

/- English proof (translation)
Rewrite using `[Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]`. Conclude with `Iff.rfl` after adjusting the coercions.
-/
lemma mem_ballRing (x : K) : x ∈ ballRing K ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
  exact_mod_cast Iff.rfl

/- English proof (translation)
Take `⟨x, hx⟩` from `NormedField.exists_one_lt_norm K`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hx`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨n, hn⟩` from `hd x hx0`. Assume the negation of the conclusion as `h`. Establish `h0 : ‖ϖ‖ = 0` using `le_antisymm (not_lt.mp h) (norm_nonneg _)`. Rewrite `hn` using `[h0]`. Break down `eq_or_ne n 0 with rfl | hn0` into its components or cases.

Simplify using `at hn`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hn` using `[zero_zpow _ hn0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma norm_unif_pos (ϖ : K) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n) : 0 < ‖ϖ‖ := by
  obtain ⟨x, hx⟩ := NormedField.exists_one_lt_norm K
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
    linarith
  obtain ⟨n, hn⟩ := hd x hx0
  by_contra h
  have h0 : ‖ϖ‖ = 0 := le_antisymm (not_lt.mp h) (norm_nonneg _)
  rw [h0] at hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp at hn; linarith
  · rw [zero_zpow _ hn0] at hn; linarith

/- English proof (translation)
Establish `h0` using `norm_unif_pos ϖ hd`. Take `⟨n, hn⟩` from `hd x hx0`. Establish `hn0 : 0 ≤ n`. Assume the negation of the conclusion as `h`. Use `one_lt_zpow_of_neg₀ h0 h1 (not_le.mp h)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨n.toNat, ?_⟩` and prove the remaining obligations. Rewrite using `[hn, ← zpow_natCast, Int.toNat_of_nonneg hn0]`.
-/
lemma exists_nat_pow (ϖ : K) (h1 : ‖ϖ‖ < 1) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n)
    (x : K) (hx0 : x ≠ 0) (hx : ‖x‖ ≤ 1) : ∃ n : ℕ, ‖x‖ = ‖ϖ‖ ^ n := by
  have h0 := norm_unif_pos ϖ hd
  obtain ⟨n, hn⟩ := hd x hx0
  have hn0 : 0 ≤ n := by
    by_contra h
    have := one_lt_zpow_of_neg₀ h0 h1 (not_le.mp h)
    linarith
  refine ⟨n.toNat, ?_⟩
  rw [hn, ← zpow_natCast, Int.toNat_of_nonneg hn0]

/- English proof (translation)
Establish `h0` using `norm_unif_pos ϖ hd`. Use `⟨fun I => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hI : I = ⊥`. Substitute `hI` using the available equality. Conclude with `bot_isPrincipal`.

Take `⟨y, hyI, hy0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hI`. Establish `hex : ∃ n : ℕ, ∃ x ∈ I, ‖(x : K)‖ = ‖ϖ‖ ^ n`. Take `⟨n, hn⟩` from `exists_nat_pow ϖ h1 hd (y : K) (by simpa using hy0) ((mem_ballRing _).mp y.2)`. Conclude with `⟨n, y, hyI, hn⟩`. Take `⟨x0, hx0I, hx0⟩` from `Nat.find_spec hex`.

Establish `hx00 : (x0 : K) ≠ 0`. Introduce `h`. Rewrite `hx0` using `[h, norm_zero]`. Conclude with `absurd hx0 (pow_pos h0 _).ne`. Use `⟨⟨x0, le_antisymm ?_ ?_⟩⟩` and prove the remaining obligations.

Introduce `z hz`. Rewrite using `[Submodule.mem_span_singleton]`. Distinguish the cases in `hz0 : z = 0`. Conclude with `⟨0, by simp [hz0]⟩`. Take `⟨m, hm⟩` from `exists_nat_pow ϖ h1 hd (z : K) (by simpa using hz0) ((mem_ballRing _).mp z.2)`.

Establish `hle : Nat.find hex ≤ m` using `Nat.find_min' hex ⟨z, hz, hm⟩`. Establish `hq : (z : K) / x0 ∈ ballRing K`. Rewrite using `[mem_ballRing, norm_div, hm, hx0, div_le_one (pow_pos h0 _)]`. Conclude with `pow_le_pow_of_le_one h0.le h1.le hle`. Use `⟨⟨_, hq⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[div_mul_cancel₀ _ hx00]`. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Conclude with `hx0I`.
-/
lemma ballRing_pid (ϖ : K) (h1 : ‖ϖ‖ < 1) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n) :
    IsPrincipalIdealRing (ballRing K) := by
  classical
  have h0 := norm_unif_pos ϖ hd
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊥
  · subst hI; exact bot_isPrincipal
  obtain ⟨y, hyI, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hex : ∃ n : ℕ, ∃ x ∈ I, ‖(x : K)‖ = ‖ϖ‖ ^ n := by
    obtain ⟨n, hn⟩ := exists_nat_pow ϖ h1 hd (y : K) (by simpa using hy0) ((mem_ballRing _).mp y.2)
    exact ⟨n, y, hyI, hn⟩
  obtain ⟨x0, hx0I, hx0⟩ := Nat.find_spec hex
  have hx00 : (x0 : K) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx0
    exact absurd hx0 (pow_pos h0 _).ne
  refine ⟨⟨x0, le_antisymm ?_ ?_⟩⟩
  · intro z hz
    rw [Submodule.mem_span_singleton]
    by_cases hz0 : z = 0
    · exact ⟨0, by simp [hz0]⟩
    obtain ⟨m, hm⟩ := exists_nat_pow ϖ h1 hd (z : K) (by simpa using hz0) ((mem_ballRing _).mp z.2)
    have hle : Nat.find hex ≤ m := Nat.find_min' hex ⟨z, hz, hm⟩
    have hq : (z : K) / x0 ∈ ballRing K := by
      rw [mem_ballRing, norm_div, hm, hx0, div_le_one (pow_pos h0 _)]
      exact pow_le_pow_of_le_one h0.le h1.le hle
    refine ⟨⟨_, hq⟩, ?_⟩
    apply Subtype.ext
    simp [div_mul_cancel₀ _ hx00]
  · rw [Submodule.span_singleton_le_iff_mem]
    exact hx0I

end UnitBall

open UnitBall in

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ ϖ h1 hd`. Establish `h0` using `norm_unif_pos ϖ hd`. Use `ballRing_pid ϖ h1 hd` as an intermediate fact. Set `A` to `ballRing K`. Set `M : Submodule A V` to `{ carrier := {v | ‖v‖ ≤ 1} add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb) zero_mem' := by simp smul_mem' := fun c v hv => by show ‖(c : K) • v‖ ≤ 1`.

Rewrite using `[norm_smul]`. Conclude with `mul_le_one₀ ((mem_ballRing _).mp c.2) (norm_nonneg _) hv }`. Establish `hM : ∀ v : V, v ∈ M ↔ ‖v‖ ≤ 1` using `fun v => Iff.rfl`. Establish `hfg : M.FG`. Set `e` to `Module.finBasis K V`.

Set `f : Fin (finrank K V) → (V →L[K] K)` to `fun i => LinearMap.toContinuousLinearMap (e.coord i)`. Take `⟨c, hc⟩` from `NormedField.exists_lt_norm K (∑ i, ‖f i‖)`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc` using `[norm_zero]`.

Conclude with `absurd hc (not_lt.mpr (Finset.sum_nonneg fun i _ => norm_nonneg _))`. Use `Submodule.FG.of_le (T := Submodule.span A (Set.range fun i => c • e i)) (Submodule.fg_span (Set.finite_range _)) ?_` and prove the remaining obligations. Introduce `v hv`. Establish `hcoef : ∀ i, e.repr v i / c ∈ A`. Introduce `i`.

Rewrite using `[mem_ballRing, norm_div, div_le_one (norm_pos_iff.mpr hc0)]`. Establish `h2 : ‖f i v‖ ≤ ‖f i‖ * ‖v‖` using `(f i).le_opNorm v`. Establish `h3 : ‖f i‖ * ‖v‖ ≤ ‖f i‖` using `mul_le_of_le_one_right (norm_nonneg _) hv`. Establish `h4 : ‖f i‖ ≤ ∑ j, ‖f j‖` using `Finset.single_le_sum (f := fun j => ‖f j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)`. Establish `h5 : f i v = e.repr v i` using `rfl`.

Rewrite using `[← h5]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hv' : v = ∑ i, (⟨_, hcoef i⟩ : A) • (c • e i)` using `by conv_lhs => rw [← e.sum_repr v]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `show _ = (e.repr v i / c) • (c • e i)`.

Rewrite using `[smul_smul, div_mul_cancel₀ _ hc0]`. Rewrite using `[hv']`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hspan : Submodule.span K (M : Set V) = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce `v _`. Take `⟨c, hc⟩` from `NormedField.exists_lt_norm K ‖v‖`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Rewrite `hc` using `[norm_zero]`.

Conclude with `absurd hc (not_lt.mpr (norm_nonneg _))`. Establish `hmem : c⁻¹ • v ∈ M`. Rewrite using `[hM, norm_smul, norm_inv, inv_mul_le_one₀ (norm_pos_iff.mpr hc0)]`. Conclude with `hc.le`. Establish `: v = c • (c⁻¹ • v)` using `by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`. Establish `: Submodule.IsLattice K M` using `⟨hfg, hspan⟩`. Set `b0` to `Module.Free.chooseBasis A M`. Set `b1` to `b0.extendOfIsLattice K`.

Establish `hb1 : ∀ j, b1 j = (b0 j : V)` using `fun j => Module.Basis.extendOfIsLattice_apply K b0 j`. Establish `hcard : Fintype.card (Module.Free.ChooseBasisIndex A M) = finrank K V` using `(Module.finrank_eq_card_basis b1).symm`. Set `eq` to `Fintype.equivFinOfCardEq hcard`. Use `⟨b1.reindex eq, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only [Module.Basis.repr_reindex_apply]`.

Rewrite using `[eq.symm.forall_congr_right (q := fun j => ‖b1.repr v j‖ ≤ 1)]`. Prove the components needed by the constructor for the conclusion. Introduce `hv j`. Set `w : M` to `⟨v, hv⟩`. Establish `hsum : v = ∑ j, ((b0.repr w j : A) : K) • b1 j`.

Establish `h` using `congrArg (Subtype.val) (b0.sum_repr w)`. Rewrite `h` using `[Submodule.coe_sum]`. Rewrite using `[← show (w : V) = v from rfl, ← h]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hb1]`.

Both sides reduce to the same expression. Establish `hr : b1.repr v j = ((b0.repr w j : A) : K)` using `by conv_lhs => rw [hsum]`. Rewrite using `[b1.repr_sum_self]`. Rewrite using `[hr]`. Conclude with `(mem_ballRing _).mp (b0.repr w j).2`.

Introduce `h`. Rewrite using `[← hM, ← b1.sum_repr v]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hb1]`. Conclude with `M.smul_mem (⟨_, (mem_ballRing _).mpr (h j)⟩ : A) (b0 j).2`.
-/
theorem unit_ball_is_lattice : UnitBallLattice := by
  intro K V _ _ _ _ _ _ _ ϖ h1 hd
  classical
  have h0 := norm_unif_pos ϖ hd
  have := ballRing_pid ϖ h1 hd
  let A := ballRing K
  let M : Submodule A V :=
    { carrier := {v | ‖v‖ ≤ 1}
      add_mem' := fun {a b} ha hb =>
        (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
      zero_mem' := by simp
      smul_mem' := fun c v hv => by
        show ‖(c : K) • v‖ ≤ 1
        rw [norm_smul]
        exact mul_le_one₀ ((mem_ballRing _).mp c.2) (norm_nonneg _) hv }
  have hM : ∀ v : V, v ∈ M ↔ ‖v‖ ≤ 1 := fun v => Iff.rfl

  have hfg : M.FG := by
    let e := Module.finBasis K V
    let f : Fin (finrank K V) → (V →L[K] K) := fun i => LinearMap.toContinuousLinearMap (e.coord i)
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K (∑ i, ‖f i‖)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hc
      exact absurd hc (not_lt.mpr (Finset.sum_nonneg fun i _ => norm_nonneg _))
    refine Submodule.FG.of_le (T := Submodule.span A (Set.range fun i => c • e i))
      (Submodule.fg_span (Set.finite_range _)) ?_
    intro v hv
    have hcoef : ∀ i, e.repr v i / c ∈ A := by
      intro i
      rw [mem_ballRing, norm_div, div_le_one (norm_pos_iff.mpr hc0)]
      have h2 : ‖f i v‖ ≤ ‖f i‖ * ‖v‖ := (f i).le_opNorm v
      have h3 : ‖f i‖ * ‖v‖ ≤ ‖f i‖ := mul_le_of_le_one_right (norm_nonneg _) hv
      have h4 : ‖f i‖ ≤ ∑ j, ‖f j‖ :=
        Finset.single_le_sum (f := fun j => ‖f j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      have h5 : f i v = e.repr v i := rfl
      rw [← h5]
      linarith
    have hv' : v = ∑ i, (⟨_, hcoef i⟩ : A) • (c • e i) := by
      conv_lhs => rw [← e.sum_repr v]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = (e.repr v i / c) • (c • e i)
      rw [smul_smul, div_mul_cancel₀ _ hc0]
    rw [hv']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span K (M : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm K ‖v‖
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hc
      exact absurd hc (not_lt.mpr (norm_nonneg _))
    have hmem : c⁻¹ • v ∈ M := by
      rw [hM, norm_smul, norm_inv, inv_mul_le_one₀ (norm_pos_iff.mpr hc0)]
      exact hc.le
    have : v = c • (c⁻¹ • v) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have : Submodule.IsLattice K M := ⟨hfg, hspan⟩
  let b0 := Module.Free.chooseBasis A M
  let b1 := b0.extendOfIsLattice K
  have hb1 : ∀ j, b1 j = (b0 j : V) := fun j => Module.Basis.extendOfIsLattice_apply K b0 j
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A M) = finrank K V :=
    (Module.finrank_eq_card_basis b1).symm
  let eq := Fintype.equivFinOfCardEq hcard
  refine ⟨b1.reindex eq, fun v => ?_⟩
  simp only [Module.Basis.repr_reindex_apply]
  rw [eq.symm.forall_congr_right (q := fun j => ‖b1.repr v j‖ ≤ 1)]
  constructor
  · intro hv j
    let w : M := ⟨v, hv⟩
    have hsum : v = ∑ j, ((b0.repr w j : A) : K) • b1 j := by
      have h := congrArg (Subtype.val) (b0.sum_repr w)
      rw [Submodule.coe_sum] at h
      rw [← show (w : V) = v from rfl, ← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hb1]
      rfl
    have hr : b1.repr v j = ((b0.repr w j : A) : K) := by
      conv_lhs => rw [hsum]
      rw [b1.repr_sum_self]
    rw [hr]
    exact (mem_ballRing _).mp (b0.repr w j).2
  · intro h
    rw [← hM, ← b1.sum_repr v]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [hb1]
    exact M.smul_mem (⟨_, (mem_ballRing _).mpr (h j)⟩ : A) (b0 j).2

end Formalism.IrreducibleCountingLemmas.TW
