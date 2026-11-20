import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

/- English proof (translation)
Establish `hfin : Module.Finite ℤ Y` using `Module.Finite.trans O Y`. Take `⟨s, hs⟩` from `Module.projective_def'.1 (inferInstance : Module.Projective O Y)`. Establish `hinj : Function.Injective s` using `Function.LeftInverse.injective (g := Finsupp.linearCombination O id) (fun y => by`. Simplify using `using LinearMap.congr_fun hs y)`. Establish `htf : Module.IsTorsionFree ℤ Y`.

Use `Module.IsTorsionFree.of_smul_eq_zero ?_` and prove the remaining obligations. Introduce `n y h`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `h1 : ((n : O)) • y = 0` using `by rw [Int.cast_smul_eq_zsmul]; exact h`.

Establish `h2 : (n : O) • s y = 0` using `by rw [← map_smul, h1, map_zero]`. Establish `hy : s y ≠ 0` using `fun h0 => hc.2 (hinj (by rw [h0, map_zero]))`. Take `⟨a, ha⟩` from `Finsupp.ne_iff.1 hy`. Establish `h3` using `DFunLike.congr_fun h2 a`. Simplify using `only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h3 ha`.

Conclude with `(mul_ne_zero (Int.cast_ne_zero.2 hc.1) ha) h3`. Conclude with `⟨hfin, Module.free_of_finite_type_torsion_free'⟩`.
-/
theorem free_int_of_projective (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O]
    (Y : Type) [AddCommGroup Y] [Module O Y] [Module.Finite O Y] [Module.Projective O Y] :
    Module.Finite ℤ Y ∧ Module.Free ℤ Y := by
  have hfin : Module.Finite ℤ Y := Module.Finite.trans O Y
  obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective O Y)
  have hinj : Function.Injective s := Function.LeftInverse.injective (g := Finsupp.linearCombination O id) (fun y => by
    simpa using LinearMap.congr_fun hs y)
  have htf : Module.IsTorsionFree ℤ Y := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro n y h
    by_contra hc
    push_neg at hc
    have h1 : ((n : O)) • y = 0 := by rw [Int.cast_smul_eq_zsmul]; exact h
    have h2 : (n : O) • s y = 0 := by rw [← map_smul, h1, map_zero]
    have hy : s y ≠ 0 := fun h0 => hc.2 (hinj (by rw [h0, map_zero]))
    obtain ⟨a, ha⟩ := Finsupp.ne_iff.1 hy
    have h3 := DFunLike.congr_fun h2 a
    simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply] at h3 ha
    exact (mul_ne_zero (Int.cast_ne_zero.2 hc.1) ha) h3
  exact ⟨hfin, Module.free_of_finite_type_torsion_free'⟩

/- English proof (translation)
Establish `hy : ∀ i j, B (y i) (y j) = ∑ k, ∑ l, (b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)` using `fun i j => by conv_lhs => rw [← b.sum_repr (y i), ← b.sum_repr (y j)]`. Simplify using `only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring` and prove the remaining obligations. Establish `key : ∑ i, ∑ j, c i * c j * B (y i) (y j) = ∑ k, ∑ l, (∑ i, c i * (b.repr (y i) k : ℝ)) * (∑ i, c i * (b.repr (y i) l : ℝ)) * B (b k) (b l)`.

Use `symm`. Simplify using `only [hy, Finset.mul_sum, Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.

Use `_ = ∑ k, ∑ i, ∑ j, ∑ l, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) := Finset.sum_congr rfl fun k _ => by`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_comm`. Use `_ = _ := by`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_comm`. Rewrite using `[key]`. Distinguish the cases in `hd : (fun k => ∑ i, c i * (b.repr (y i) k : ℝ)) = 0`. Establish `hd' : ∀ k, ∑ i, c i * (b.repr (y i) k : ℝ) = 0` using `fun k => congrFun hd k`. Simplify using `[hd']`.

Conclude with `((isPosDef_iff_basis b B).1 h _ hd).le`.
-/
theorem sum_nonneg_of_isPosDef {Y ι : Type} [AddCommGroup Y] [Fintype ι] (b : Module.Basis ι ℤ Y)
    {B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ} (h : IsPosDef B) {n : ℕ} (y : Fin n → Y) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * B (y i) (y j) := by
  have hy : ∀ i j, B (y i) (y j) = ∑ k, ∑ l, (b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l) := fun i j => by
    conv_lhs => rw [← b.sum_repr (y i), ← b.sum_repr (y j)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have key : ∑ i, ∑ j, c i * c j * B (y i) (y j) = ∑ k, ∑ l, (∑ i, c i * (b.repr (y i) k : ℝ)) *
      (∑ i, c i * (b.repr (y i) l : ℝ)) * B (b k) (b l) := by
    symm
    simp only [hy, Finset.mul_sum, Finset.sum_mul]
    calc _ = ∑ k, ∑ l, ∑ i, ∑ j, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ k, ∑ i, ∑ j, ∑ l, c i * c j * ((b.repr (y i) k : ℝ) * (b.repr (y j) l : ℝ) * B (b k) (b l)) :=
          Finset.sum_congr rfl fun k _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = _ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [key]
  by_cases hd : (fun k => ∑ i, c i * (b.repr (y i) k : ℝ)) = 0
  · have hd' : ∀ k, ∑ i, c i * (b.repr (y i) k : ℝ) = 0 := fun k => congrFun hd k
    simp [hd']
  · exact ((isPosDef_iff_basis b B).1 h _ hd).le

/- English proof (translation)
Take `⟨X₁, _, _, _, r, B₁, hr, -, h1, h2⟩` from `hB`. Establish `: Module.Finite O X₁` using `Module.Finite.of_surjective r hr`. Take `⟨_, _⟩` from `free_int_of_projective O X₁`. Simplify using `only [h2]`. Conclude with `sum_nonneg_of_isPosDef (Module.Free.chooseBasis ℤ X₁) h1 (fun i => r (x i)) c`.
-/
theorem sum_nonneg_of_mem_psdCone (O : Type) [CommRing O] [IsDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O}
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ} (hB : B ∈ psdCone bar X)
    {n : ℕ} (x : Fin n → X) (c : Fin n → ℝ) : 0 ≤ ∑ i, ∑ j, c i * c j * B (x i) (x j) := by
  obtain ⟨X₁, _, _, _, r, B₁, hr, -, h1, h2⟩ := hB
  have : Module.Finite O X₁ := Module.Finite.of_surjective r hr
  obtain ⟨_, _⟩ := free_int_of_projective O X₁
  simp only [h2]
  exact sum_nonneg_of_isPosDef (Module.Free.chooseBasis ℤ X₁) h1 (fun i => r (x i)) c

/- English proof (translation)
Establish `hpos : IsPosDef (B + B₀)` using `fun n x hx c hc => by`. Establish `h1` using `sum_nonneg_of_mem_psdCone O hB x c`. Establish `h2` using `h₀ n x hx c hc`. Establish `h3 : ∑ i, ∑ j, c i * c j * (B + B₀) (x i) (x j) = ∑ i, ∑ j, c i * c j * B (x i) (x j) + ∑ i, ∑ j, c i * c j * B₀ (x i) (x j)`. Simplify using `only [LinearMap.add_apply, mul_add, Finset.sum_add_distrib]`.

Rewrite using `[h3]`. Conclude with `add_pos_of_nonneg_of_pos h1 h2`. Conclude with `⟨hpos, hpos.mem_psdCone (add_mem (mem_realForms_of_mem_psdCone hB) hB₀)⟩`.
-/
theorem isPosDef_add_and_mem_psdCone (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O]
    (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (B B₀ : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (hB : B ∈ psdCone bar X) (hB₀ : B₀ ∈ realForms bar X) (h₀ : IsPosDef B₀) :
    IsPosDef (B + B₀) ∧ B + B₀ ∈ psdCone bar X := by
  have hpos : IsPosDef (B + B₀) := fun n x hx c hc => by
    have h1 := sum_nonneg_of_mem_psdCone O hB x c
    have h2 := h₀ n x hx c hc
    have h3 : ∑ i, ∑ j, c i * c j * (B + B₀) (x i) (x j) =
        ∑ i, ∑ j, c i * c j * B (x i) (x j) + ∑ i, ∑ j, c i * c j * B₀ (x i) (x j) := by
      simp only [LinearMap.add_apply, mul_add, Finset.sum_add_distrib]
    rw [h3]
    exact add_pos_of_nonneg_of_pos h1 h2
  exact ⟨hpos, hpos.mem_psdCone (add_mem (mem_realForms_of_mem_psdCone hB) hB₀)⟩

end GlobalTheory.CompanionTheory.Ar.Fan
