import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfSplit

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    [Fintype (K →ₐ[Qp] LL)]

/- English proof (translation)
Introduce `c hc`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨e, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ0 hϖ`. Distinguish the cases in `hc0 : c = 0`. Conclude with `⟨1, 0, by simp [hc0]⟩`.

Take `⟨k, w, hw⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ`. Establish `hk : 1 ≤ k`. Break down `Nat.eq_zero_or_pos k with h | h` into its components or cases. It suffices to derive a contradiction. Rewrite `hw` using `[h, pow_zero, mul_one]`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hc (hw ▸ w.isUnit)`. Conclude with `h`. Take `⟨j, hj⟩ : ∃ j, k * e = e + j` from `⟨k * e - e, by`. Establish `: e ≤ k * e` using `Nat.le_mul_of_pos_left e hk`. Use the proof step `omega⟩`.

Use `⟨e, ↑u⁻¹ * ↑w ^ e * ϖ ^ j, ?_⟩` and prove the remaining obligations. Establish `h1 : (↑w * ϖ ^ k) ^ e = (↑w : O) ^ e * ϖ ^ e * ϖ ^ j`. Rewrite using `[mul_pow, ← pow_mul, hj, pow_add, mul_assoc]`. Establish `hu1 : (↑u : O) * ↑u⁻¹ = 1` using `Units.mul_inv u`. Rewrite using `[hw, hu, h1]`.

Take the linear combination `(-((↑w : O) ^ e * ϖ ^ e * ϖ ^ j)) * hu1`.
-/
theorem hOnil_of [IsDomain O] [IsDiscreteValuationRing O] (hℓ0 : ((PD.p : ℕ) : O) ≠ 0) :
    ∀ c ∈ IsLocalRing.maximalIdeal O, ∃ (N : ℕ) (d : O), c ^ N = ((PD.p : ℕ) : O) * d := by
  intro c hc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ0 hϖ
  by_cases hc0 : c = 0
  · exact ⟨1, 0, by simp [hc0]⟩
  obtain ⟨k, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hw
      exact (IsLocalRing.mem_maximalIdeal _).1 hc (hw ▸ w.isUnit)
    · exact h
  obtain ⟨j, hj⟩ : ∃ j, k * e = e + j := ⟨k * e - e, by
    have : e ≤ k * e := Nat.le_mul_of_pos_left e hk
    omega⟩
  refine ⟨e, ↑u⁻¹ * ↑w ^ e * ϖ ^ j, ?_⟩
  have h1 : (↑w * ϖ ^ k) ^ e = (↑w : O) ^ e * ϖ ^ e * ϖ ^ j := by
    rw [mul_pow, ← pow_mul, hj, pow_add, mul_assoc]
  have hu1 : (↑u : O) * ↑u⁻¹ = 1 := Units.mul_inv u
  rw [hw, hu, h1]
  linear_combination (-((↑w : O) ^ e * ϖ ^ e * ϖ ^ j)) * hu1

end Formalism.MainNotions.N.Ln03.Pf
