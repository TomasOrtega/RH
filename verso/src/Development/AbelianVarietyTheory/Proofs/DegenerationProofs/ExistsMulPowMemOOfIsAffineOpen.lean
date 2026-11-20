import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

/- English proof (translation)
Take `⟨g, rfl⟩` from `(mem_ringOn_iff_exists hne).1 (mem_ringOn.2 hu)`. Establish `hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty`. Rewrite using `[Set.nonempty_iff_ne_empty]`. Introduce `h`. Establish `h0 : g = 0` using `(basicOpen_eq_bot_iff g).1 (SetLike.coe_injective h)`.

Conclude with `hu0 (by rw [h0, ← M.res_apply V hne, map_zero])`. Take `⟨f, rfl⟩` from `(mem_ringOn_iff_exists hg (x := φ)).1 (mem_ringOn.2 fun z hz => hφ z (M.Z.basicOpen_le g hz) ((isUnit_O_iff _).1 ((isUnit_valF_iff (M.Z.basicOpen_le g hz) g).2 hz)).2)`. Use `hV.isLocalization_basicOpen g` as an intermediate fact. Take `⟨n, a, ha⟩` from `IsLocalization.Away.surj g f`. Establish `h1` using `congrArg (M.res _ hg) ha`.

Establish `h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t` using `fun t => M.res_resG (M.Z.basicOpen_le g) hg t`. Rewrite `h1` using `[map_mul, map_pow, h2, h2, res_apply, res_apply, res_apply]`. Conclude with `⟨n, fun z hz => h1 ▸ valF_mem_O hz a⟩`.
-/
theorem exists_mul_pow_mem_O_of_isAffineOpen {V : M.Z.Opens} (hV : IsAffineOpen V) (hne : (V : Set M.Z).Nonempty)
    {u φ : Ω} (hu0 : u ≠ 0) (hu : ∀ z ∈ V, u ∈ M.O z) (hφ : ∀ z ∈ V, u⁻¹ ∈ M.O z → φ ∈ M.O z) :
    ∃ n : ℕ, ∀ z ∈ V, φ * u ^ n ∈ M.O z := by
  obtain ⟨g, rfl⟩ := (mem_ringOn_iff_exists hne).1 (mem_ringOn.2 hu)
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have h0 : g = 0 := (basicOpen_eq_bot_iff g).1 (SetLike.coe_injective h)
    exact hu0 (by rw [h0, ← M.res_apply V hne, map_zero])
  obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hg (x := φ)).1 (mem_ringOn.2 fun z hz =>
    hφ z (M.Z.basicOpen_le g hz)
      ((isUnit_O_iff _).1 ((isUnit_valF_iff (M.Z.basicOpen_le g hz) g).2 hz)).2)
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g f
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, res_apply, res_apply, res_apply] at h1
  exact ⟨n, fun z hz => h1 ▸ valF_mem_O hz a⟩

variable (M) in

/- English proof (translation)
Use `M.lft` as an intermediate fact. Use `M.qc` as an intermediate fact. Establish `: IsLocallyNoetherian M.Z` using `LocallyOfFiniteType.isLocallyNoetherian M.s`. Establish `: CompactSpace M.Z` using `QuasiCompact.compactSpace_of_compactSpace M.s`. Establish `: AlgebraicGeometry.IsNoetherian M.Z` using `{}`.

Use `infer_instance`.
-/
theorem noetherianSpace_of_isNoetherianRing [IsNoetherianRing o] : TopologicalSpace.NoetherianSpace M.Z := by
  have := M.lft
  have := M.qc
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  have : CompactSpace M.Z := QuasiCompact.compactSpace_of_compactSpace M.s
  have : AlgebraicGeometry.IsNoetherian M.Z := {}
  infer_instance

/- English proof (translation)
Use `M.noetherianSpace_of_isNoetherianRing` as an intermediate fact. Establish `hmono : ∀ z ∈ W, ∀ m n : ℕ, m ≤ n → φ * u ^ m ∈ M.O z → φ * u ^ n ∈ M.O z`. Introduce `z hz m n hmn h`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hmn`. Rewrite using `[pow_add, ← _root_.mul_assoc]`.

Conclude with `mul_mem h (pow_mem (hu z hz) k)`. Establish `hcov : (W : Set M.Z) ⊆ ⋃ n : ℕ, {z | φ * u ^ n ∈ M.O z}`. Introduce `z hz`. Take `⟨V, hV, hzV, hle⟩` from `exists_isAffineOpen_mem_and_subset (U := W) (x := z) hz`. Take `⟨n, hn⟩` from `exists_mul_pow_mem_O_of_isAffineOpen hV ⟨z, hzV⟩ hu0 (fun w hw => hu w (hle hw)) (fun w hw => hφ w (hle hw))`.

Conclude with `Set.mem_iUnion.2 ⟨n, hn z hzV⟩`. Take `⟨s, hs⟩` from `(TopologicalSpace.NoetherianSpace.isCompact (W : Set M.Z)).elim_finite_subcover _ (fun n => M.isOpen_setOf_mem_O _) hcov`. Use `⟨s.sup id, fun C hC z hz => ?_⟩` and prove the remaining obligations. Take `⟨n, hn, h⟩` from `Set.mem_iUnion₂.1 (hs hz)`. Conclude with `hmono z hz n C ((Finset.le_sup (f := id) hn).trans hC) h`.
-/
theorem exists_forall_mul_pow_mem_O [IsNoetherianRing o] (W : M.Z.Opens)
    {u φ : Ω} (hu0 : u ≠ 0) (hu : ∀ z ∈ W, u ∈ M.O z) (hφ : ∀ z ∈ W, u⁻¹ ∈ M.O z → φ ∈ M.O z) :
    ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z ∈ W, φ * u ^ C ∈ M.O z := by
  have := M.noetherianSpace_of_isNoetherianRing
  have hmono : ∀ z ∈ W, ∀ m n : ℕ, m ≤ n → φ * u ^ m ∈ M.O z → φ * u ^ n ∈ M.O z := by
    intro z hz m n hmn h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [pow_add, ← _root_.mul_assoc]
    exact mul_mem h (pow_mem (hu z hz) k)
  have hcov : (W : Set M.Z) ⊆ ⋃ n : ℕ, {z | φ * u ^ n ∈ M.O z} := by
    intro z hz
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset (U := W) (x := z) hz
    obtain ⟨n, hn⟩ := exists_mul_pow_mem_O_of_isAffineOpen hV ⟨z, hzV⟩ hu0 (fun w hw => hu w (hle hw))
      (fun w hw => hφ w (hle hw))
    exact Set.mem_iUnion.2 ⟨n, hn z hzV⟩
  obtain ⟨s, hs⟩ := (TopologicalSpace.NoetherianSpace.isCompact (W : Set M.Z)).elim_finite_subcover _
    (fun n => M.isOpen_setOf_mem_O _) hcov
  refine ⟨s.sup id, fun C hC z hz => ?_⟩
  obtain ⟨n, hn, h⟩ := Set.mem_iUnion₂.1 (hs hz)
  exact hmono z hz n C ((Finset.le_sup (f := id) hn).trans hC) h

/- English proof (translation)
Introduce `o Ω _ _ _ M _ J t W j hj I φ hφ hI`. Distinguish the cases in `hW : ∃ z, z ∈ W`. Use `swap`. Conclude with `⟨0, fun _ _ z hz => (hW ⟨z, hz⟩).elim⟩`. Take `⟨z₀, hz₀⟩` from `hW`.

Establish `hj0 : t j ≠ 0` using `(hj z₀ hz₀).1`. Establish `hu0 : (∏ i ∈ I, t i / t j) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i hi => div_ne_zero (hI i hi) hj0`. Use `exists_forall_mul_pow_mem_O W hu0 (fun z hz => prod_mem fun i _ => (hj z hz).2 i) fun z hz hinv => ?_` and prove the remaining obligations. Use `hφ z hz fun i hi => ((hj z hz).div_iff_isUnit i).2 ((isUnit_O_iff _).2 ⟨div_ne_zero (hI i hi) hj0, ?_⟩)` and prove the remaining obligations. Establish `hmem` using `mul_mem (prod_mem (S := M.O z) (t := I.erase i) fun k _ => (hj z hz).2 k) hinv`.

Establish `e : (∏ k ∈ I.erase i, t k / t j) * (∏ k ∈ I, t k / t j)⁻¹ = (t i / t j)⁻¹`. Use `eq_inv_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[← _root_.mul_assoc, Finset.mul_prod_erase I (fun k => t k / t j) hi, mul_inv_cancel₀ hu0]`. Conclude with `e ▸ hmem`.
-/
theorem exists_forall_mul_prod_div_pow_mem_O :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) [IsNoetherianRing o] (J : Type)
      (t : J → Ω) (W : M.Z.Opens) (j : J), (∀ z ∈ W, M.Div t j z) → ∀ (I : Finset J) (φ : Ω),
      (∀ z ∈ W, (∀ i ∈ I, M.Div t i z) → φ ∈ M.O z) → (∀ i ∈ I, t i ≠ 0) →
      ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z ∈ W, φ * (∏ i ∈ I, t i / t j) ^ C ∈ M.O z := by
  intro o Ω _ _ _ M _ J t W j hj I φ hφ hI
  by_cases hW : ∃ z, z ∈ W
  swap
  · exact ⟨0, fun _ _ z hz => (hW ⟨z, hz⟩).elim⟩
  obtain ⟨z₀, hz₀⟩ := hW
  have hj0 : t j ≠ 0 := (hj z₀ hz₀).1
  have hu0 : (∏ i ∈ I, t i / t j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => div_ne_zero (hI i hi) hj0
  refine exists_forall_mul_pow_mem_O W hu0 (fun z hz => prod_mem fun i _ => (hj z hz).2 i) fun z hz hinv => ?_
  refine hφ z hz fun i hi => ((hj z hz).div_iff_isUnit i).2 ((isUnit_O_iff _).2 ⟨div_ne_zero (hI i hi) hj0, ?_⟩)
  have hmem := mul_mem (prod_mem (S := M.O z) (t := I.erase i) fun k _ => (hj z hz).2 k) hinv
  have e : (∏ k ∈ I.erase i, t k / t j) * (∏ k ∈ I, t k / t j)⁻¹ = (t i / t j)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← _root_.mul_assoc, Finset.mul_prod_erase I (fun k => t k / t j) hi, mul_inv_cancel₀ hu0]
  exact e ▸ hmem

end GlobalTheory.ZH.RatModel
end
