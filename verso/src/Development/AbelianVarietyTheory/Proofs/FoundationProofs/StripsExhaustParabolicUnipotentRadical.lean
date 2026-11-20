import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTrivialOnUnitsModConductorUnitCharacterValuePr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubsingletonJacquetIff

open Filter Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

/- English proof (translation)
Introduce `k _ _ _ _ r t ψ ϖ hψ _ hϖ _ y hy`. Establish `hy'` using `(GlobalTheory.CuspEntries.mem_unipRad_two_stdSum rfl y).1 hy`. Establish `hpow : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0)`. Rewrite using `[(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]`. Introduce `γ hγ`.

Establish `: MulArchimedean (ValueGroupWithZero k)` using `ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`. Take `⟨n, hn⟩` from `exists_pow_lt₀ hϖ (Units.mk0 γ hγ)`. Use `filter_upwards [eventually_ge_atTop n] with m hm`. Rewrite using `[map_pow]`. Conclude with `lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn`.

Establish `hball : {z : k | valuation k z < 1} ∈ 𝓝 (0 : k)` using `(IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.2 ⟨1, one_ne_zero, fun _ hz => hz⟩`. Establish `P` using `(triv_ev_props k)`. Establish `hev : ∀ i j : Fin (r + t), ∀ᶠ m : ℕ in atTop, (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j) else y.val i j = (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) i j)`. Introduce `i j`. Distinguish the cases in `hij : (i : ℕ) < r ∧ r ≤ (j : ℕ)`.

Simplify using `only [hij, and_self, if_true]`. Establish `hsm : IsSmoothChar (ψ i / ψ j)`. Establish `h1` using `hψ i`. Establish `h2` using `hψ j`. Unfold `IsSmoothChar at *`.

Establish `: (ψ i).ker ⊓ (ψ j).ker ≤ (ψ i / ψ j).ker`. Introduce `u hu`. Rewrite `hu` using `[Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker]`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.div_apply, hu.1, hu.2, div_one]`. Conclude with `Subgroup.isOpen_mono this (by rw [Subgroup.coe_inf]; exact h1.inter h2)`.

Establish `hopen` using `(P.2.2.2.2.2.1 _ hsm).1`. Establish `hT : {z : k | Triv (ψ i / ψ j) z} ∈ 𝓝 (0 : k)` using `hopen.mem_nhds (P.2.2.1 _)`. Establish `ht : Tendsto (fun m : ℕ => ϖ ^ m * y.val i j) atTop (𝓝 0)`. Simplify using `using hpow.mul_const (y.val i j)`. Use `filter_upwards [ht (inter_mem hball hT)] with m hm`.

Conclude with `⟨hm.1.le, hm.2⟩`. Simplify using `only [hij, if_false]`. Conclude with `Eventually.of_forall fun _ => hy' i j hij`. Establish `hall : ∀ᶠ m : ℕ in atTop, ∀ i j : Fin (r + t), (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j) else y.val i j = (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) i j)`. Rewrite using `[eventually_all]`.

Introduce `i`. Rewrite using `[eventually_all]`. Conclude with `hev i`. Take `⟨m, hm⟩` from `hall.exists`. Conclude with `⟨m, hm⟩`.
-/
theorem strip_exhaust : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 →
    (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) →
    ∀ y ∈ unipRad k (two (stdSum (rfl : r + t = r + t))), ∃ m, y ∈ strip ψ r ϖ m := by
  intro k _ _ _ _ r t ψ ϖ hψ _ hϖ _ y hy
  have hy' := (GlobalTheory.CuspEntries.mem_unipRad_two_stdSum rfl y).1 hy

  have hpow : Tendsto (fun n : ℕ => ϖ ^ n) atTop (𝓝 0) := by
    rw [(IsValuativeTopology.hasBasis_nhds_zero' k).tendsto_right_iff]
    intro γ hγ
    have : MulArchimedean (ValueGroupWithZero k) :=
      ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
    obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ (Units.mk0 γ hγ)
    filter_upwards [eventually_ge_atTop n] with m hm
    rw [map_pow]
    exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hϖ.le hm) hn
  have hball : {z : k | valuation k z < 1} ∈ 𝓝 (0 : k) :=
    (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.2 ⟨1, one_ne_zero, fun _ hz => hz⟩
  have P := (triv_ev_props k)
  have hev : ∀ i j : Fin (r + t), ∀ᶠ m : ℕ in atTop,
      (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j)
      else y.val i j = (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) i j) := by
    intro i j
    by_cases hij : (i : ℕ) < r ∧ r ≤ (j : ℕ)
    · simp only [hij, and_self, if_true]
      have hsm : IsSmoothChar (ψ i / ψ j) := by
        have h1 := hψ i
        have h2 := hψ j
        unfold IsSmoothChar at *
        have : (ψ i).ker ⊓ (ψ j).ker ≤ (ψ i / ψ j).ker := by
          intro u hu
          rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hu
          rw [MonoidHom.mem_ker, MonoidHom.div_apply, hu.1, hu.2, div_one]
        exact Subgroup.isOpen_mono this (by rw [Subgroup.coe_inf]; exact h1.inter h2)
      have hopen := (P.2.2.2.2.2.1 _ hsm).1
      have hT : {z : k | Triv (ψ i / ψ j) z} ∈ 𝓝 (0 : k) := hopen.mem_nhds (P.2.2.1 _)
      have ht : Tendsto (fun m : ℕ => ϖ ^ m * y.val i j) atTop (𝓝 0) := by
        simpa using hpow.mul_const (y.val i j)
      filter_upwards [ht (inter_mem hball hT)] with m hm
      exact ⟨hm.1.le, hm.2⟩
    · simp only [hij, if_false]
      exact Eventually.of_forall fun _ => hy' i j hij
  have hall : ∀ᶠ m : ℕ in atTop, ∀ i j : Fin (r + t),
      (if (i : ℕ) < r ∧ r ≤ (j : ℕ) then
        valuation k (ϖ ^ m * y.val i j) ≤ 1 ∧ Triv (ψ i / ψ j) (ϖ ^ m * y.val i j)
      else y.val i j = (1 : Matrix (Fin (r + t)) (Fin (r + t)) k) i j) := by
    rw [eventually_all]
    intro i
    rw [eventually_all]
    exact hev i
  obtain ⟨m, hm⟩ := hall.exists
  exact ⟨m, hm⟩

end GlobalTheory.PsType
