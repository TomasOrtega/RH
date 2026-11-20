import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsLiftOfMemKO
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LevelType

/- English proof (translation)
Introduce `i j hij`. Rewrite using `[Units.val_mul, Matrix.mul_apply]`. Distinguish the cases in `hi : i.val ≤ a`. Establish `hj : ¬ a ≤ j.val` using `fun h => hij ⟨hi, h⟩`. Establish `: ∀ k, y.val k j = if k = j then 1 else 0` using `fun k => hy k j (fun h => hj h.2)`.

Simplify using `only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Conclude with `hx i j hij`. Establish `: ∀ k, x.val i k = if i = k then 1 else 0` using `fun k => hx i k (fun h => hi h.1)`. Simplify using `only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Conclude with `hy i j hij`.
-/
theorem StdBlock.mul {p r : ℕ} {a : ℕ} {x y : GL (Fin r) (ZMod p)} (hx : StdBlock a x) (hy : StdBlock a y) :
    StdBlock a (x * y) := by
  intro i j hij
  rw [Units.val_mul, Matrix.mul_apply]
  by_cases hi : i.val ≤ a
  · have hj : ¬ a ≤ j.val := fun h => hij ⟨hi, h⟩
    have : ∀ k, y.val k j = if k = j then 1 else 0 := fun k => hy k j (fun h => hj h.2)
    simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hx i j hij
  · have : ∀ k, x.val i k = if i = k then 1 else 0 := fun k => hx i k (fun h => hi h.1)
    simp only [this, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hy i j hij

/- English proof (translation)
Introduce `i j _`. Simplify using `[Matrix.one_apply]`.
-/
theorem stdBlock_one {p r : ℕ} (a : ℕ) : StdBlock a (1 : GL (Fin r) (ZMod p)) := by
  intro i j _
  simp [Matrix.one_apply]

/- English proof (translation)
Introduce `p _ r a θ ρ v hv0 hv`. Use `set S : Finset (GL (Fin r) (ZMod p)) := Finset.univ.filter (StdBlock a) with hS`. Use `set c : GL (Fin r) (ZMod p) → ℂ := fun x => (((θ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) with hc`. Establish `hcm : ∀ x y, c (x * y) = c x * c y` using `fun x y => by`. Simplify using `[hc, map_mul, mul_inv, Units.val_mul, mul_comm]`.

Use `set E : Module.End ℂ ρ := ∑ x ∈ S, c x • ρ.ρ x with hE`. Establish `htr : stdTrace a θ ρ.character = LinearMap.trace ℂ ρ E`. Rewrite using `[hE, map_sum, stdTrace, hS, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp [FDRep.character, hc]`.

Establish `himg : ∀ x ∈ S, S.image (x * ·) = S` using `fun x hx => by`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `Finset.mem_image.1 hz`. Simplify using `only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢`.

Conclude with `hx.mul hy`. Rewrite using `[Finset.card_image_of_injective _ (mul_right_injective x)]`. Establish `hEE : E * E = (S.card : ℂ) • E`. Establish `: ∀ x ∈ S, (c x • ρ.ρ x) * E = E` using `fun x hx => by`. Rewrite using `[hE, Finset.mul_sum]`.

Use `conv_rhs => rw [← himg x hx]`. Rewrite using `[Finset.sum_image (fun y _ z _ h => mul_left_cancel h)]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_smul_comm, ← map_mul, hcm x y]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hEv : E v = (S.card : ℂ) • v`. Rewrite using `[hE, LinearMap.sum_apply, Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]`. Introduce `x hx`. Rewrite using `[LinearMap.smul_apply, hv x (by simpa [hS] using hx), smul_smul]`. Simplify using `[hc]`.

Establish `hcard : (S.card : ℂ) ≠ 0`. Establish `: (1 : GL (Fin r) (ZMod p)) ∈ S` using `by simpa [hS] using stdBlock_one (p := p) (r := r) a`. Conclude with `Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem this)`. Use `set P : Module.End ℂ ρ := (S.card : ℂ)⁻¹ • E with hP`. Establish `hPP : IsIdempotentElem P`.

Rewrite using `[IsIdempotentElem, hP, smul_mul_smul_comm, hEE, smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Establish `hPv : P v = v`. Rewrite using `[hP, LinearMap.smul_apply, hEv, smul_smul, inv_mul_cancel₀ hcard, one_smul]`.

Establish `hP0 : P ≠ 0` using `fun h => hv0 (by rw [← hPv, h, LinearMap.zero_apply])`. Establish `htP : LinearMap.trace ℂ ρ P ≠ 0` using `fun h => hP0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hPP).1 h)`. Rewrite using `[htr]`. Establish `: E = (S.card : ℂ) • P` using `by rw [hP, smul_smul, mul_inv_cancel₀ hcard, one_smul]`. Rewrite using `[this, map_smul, smul_eq_mul]`.

Conclude with `mul_ne_zero hcard htP`.
-/
theorem stdTrace_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (r a : ℕ) (θ : (ZMod p)ˣ →* ℂˣ) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (v : ρ), v ≠ 0 → StdVec ρ.ρ a θ v → stdTrace a θ ρ.character ≠ 0 := by
  intro p _ r a θ ρ v hv0 hv
  classical
  set S : Finset (GL (Fin r) (ZMod p)) := Finset.univ.filter (StdBlock a) with hS
  set c : GL (Fin r) (ZMod p) → ℂ := fun x => (((θ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ) with hc
  have hcm : ∀ x y, c (x * y) = c x * c y := fun x y => by
    simp [hc, map_mul, mul_inv, Units.val_mul, mul_comm]
  set E : Module.End ℂ ρ := ∑ x ∈ S, c x • ρ.ρ x with hE
  have htr : stdTrace a θ ρ.character = LinearMap.trace ℂ ρ E := by
    rw [hE, map_sum, stdTrace, hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp [FDRep.character, hc]
  have himg : ∀ x ∈ S, S.image (x * ·) = S := fun x hx => by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hx hy ⊢
      exact hx.mul hy
    · rw [Finset.card_image_of_injective _ (mul_right_injective x)]
  have hEE : E * E = (S.card : ℂ) • E := by
    have : ∀ x ∈ S, (c x • ρ.ρ x) * E = E := fun x hx => by
      rw [hE, Finset.mul_sum]
      conv_rhs => rw [← himg x hx]
      rw [Finset.sum_image (fun y _ z _ h => mul_left_cancel h)]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [smul_mul_smul_comm, ← map_mul, hcm x y]
    calc E * E = ∑ x ∈ S, (c x • ρ.ρ x) * E := by rw [hE, Finset.sum_mul]
      _ = ∑ x ∈ S, E := Finset.sum_congr rfl this
      _ = (S.card : ℂ) • E := by rw [Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have hEv : E v = (S.card : ℂ) • v := by
    rw [hE, LinearMap.sum_apply, Finset.sum_congr rfl (g := fun _ => v), Finset.sum_const, Nat.cast_smul_eq_nsmul]
    intro x hx
    rw [LinearMap.smul_apply, hv x (by simpa [hS] using hx), smul_smul]
    simp [hc]
  have hcard : (S.card : ℂ) ≠ 0 := by
    have : (1 : GL (Fin r) (ZMod p)) ∈ S := by simpa [hS] using stdBlock_one (p := p) (r := r) a
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem this)
  set P : Module.End ℂ ρ := (S.card : ℂ)⁻¹ • E with hP
  have hPP : IsIdempotentElem P := by
    rw [IsIdempotentElem, hP, smul_mul_smul_comm, hEE, smul_smul]
    congr 1
    field_simp
  have hPv : P v = v := by
    rw [hP, LinearMap.smul_apply, hEv, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  have hP0 : P ≠ 0 := fun h => hv0 (by rw [← hPv, h, LinearMap.zero_apply])
  have htP : LinearMap.trace ℂ ρ P ≠ 0 := fun h => hP0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hPP).1 h)
  rw [htr]
  have : E = (S.card : ℂ) • P := by rw [hP, smul_smul, mul_inv_cancel₀ hcard, one_smul]
  rw [this, map_smul, smul_eq_mul]
  exact mul_ne_zero hcard htP

end GlobalTheory.LevelType

end
