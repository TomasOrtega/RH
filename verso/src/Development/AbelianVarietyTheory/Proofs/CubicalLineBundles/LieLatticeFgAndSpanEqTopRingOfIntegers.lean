import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeLocalBasisDescriptionStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.LieLattice

/- English proof (translation)
Take `⟨x, hx⟩ : ∃ x : Fin g → K, Matrix.vecMul x M = c` from `⟨Matrix.vecMul c M⁻¹, by`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM), Matrix.vecMul_one]⟩`. Take `⟨d, hd⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x`. Use `choose a ha using hd`. Use `⟨d, nonZeroDivisors.coe_ne_zero d, a, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hx, Matrix.vecMul_eq_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_assoc, ← ha j, algebraMap_smul]`.
-/
theorem exists_smul_eq_sum_rows {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    {g : ℕ} (M : Matrix (Fin g) (Fin g) K) (hM : M.det ≠ 0) (c : Fin g → K) :
    ∃ d : O, d ≠ 0 ∧ ∃ a : Fin g → O, d • c = ∑ j, a j • M j := by
  obtain ⟨x, hx⟩ : ∃ x : Fin g → K, Matrix.vecMul x M = c :=
    ⟨Matrix.vecMul c M⁻¹, by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hM), Matrix.vecMul_one]⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O) x
  choose a ha using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, a, ?_⟩
  rw [← hx, Matrix.vecMul_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_assoc, ← ha j, algebraMap_smul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Set `N : Submodule O (Fin g → K)` to `Submodule.span O (Set.range fun p : Fin n × Fin g => M p.1 p.2)`. Establish `hN : N.FG` using `Submodule.fg_span (Set.finite_range _)`. Use `Submodule.FG.of_le hN fun c hc => ?_` and prove the remaining obligations. Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem N (Set.range r) hr c ?_` and prove the remaining obligations.

Introduce and unpack `⟨_, i, rfl⟩`. Take `⟨k, a, h⟩` from `(hL c).1 hc i`. Use `⟨k, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `r i ^ k • c ∈ N`. Rewrite using `[h]`.

Conclude with `N.sum_mem fun j _ => N.smul_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)`. Rewrite using `[eq_top_iff]`. Introduce `c _`. Use `choose d hd a ha using fun i => exists_smul_eq_sum_rows (O := O) (M i) (hM i) c`. Establish `hD : (∏ i, d i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => hd i`.

Establish `hmem : (∏ i, d i) • c ∈ L`. Use `(hL _).2 fun i => ⟨0, fun j => (∏ l ∈ Finset.univ.erase i, d l) * a i j, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, one_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, ha, Finset.smul_sum]`. Simplify using `only [mul_smul]`. Establish `hK : algebraMap O K (∏ i, d i) ≠ 0`.

Rewrite using `[Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]` and apply the resulting hypothesis. Establish `e : c = (algebraMap O K (∏ i, d i))⁻¹ • ((∏ i, d i) • c)`. Rewrite using `[← algebraMap_smul K (∏ i, d i) c, smul_smul, inv_mul_cancel₀ hK, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`.
-/
theorem fg_and_span_eq_top {O K : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {g n : ℕ} (L : Submodule O (Fin g → K)) (r : Fin n → O)
    (M : Fin n → Matrix (Fin g) (Fin g) K) (hr : Ideal.span (Set.range r) = ⊤) (hM : ∀ i, (M i).det ≠ 0)
    (hL : ∀ c, c ∈ L ↔ ∀ i, ∃ (k : ℕ) (a : Fin g → O), r i ^ k • c = ∑ j, a j • M i j) :
    L.FG ∧ Submodule.span K (L : Set (Fin g → K)) = ⊤ := by
  constructor
  · let N : Submodule O (Fin g → K) := Submodule.span O (Set.range fun p : Fin n × Fin g => M p.1 p.2)
    have hN : N.FG := Submodule.fg_span (Set.finite_range _)
    refine Submodule.FG.of_le hN fun c hc => ?_
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem N (Set.range r) hr c ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨k, a, h⟩ := (hL c).1 hc i
    refine ⟨k, ?_⟩
    change r i ^ k • c ∈ N
    rw [h]
    exact N.sum_mem fun j _ => N.smul_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  · classical
    rw [eq_top_iff]
    intro c _
    choose d hd a ha using fun i => exists_smul_eq_sum_rows (O := O) (M i) (hM i) c
    have hD : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hd i
    have hmem : (∏ i, d i) • c ∈ L := by
      refine (hL _).2 fun i => ⟨0, fun j => (∏ l ∈ Finset.univ.erase i, d l) * a i j, ?_⟩
      rw [pow_zero, one_smul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, ha, Finset.smul_sum]
      simp only [mul_smul]
    have hK : algebraMap O K (∏ i, d i) ≠ 0 := by
      rwa [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]
    have e : c = (algebraMap O K (∏ i, d i))⁻¹ • ((∏ i, d i) • c) := by
      rw [← algebraMap_smul K (∏ i, d i) c, smul_smul, inv_mul_cancel₀ hK, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

/- English proof (translation)
Introduce `K _ _ P F`. Take `⟨n, r, M, hr, hM, hL, -⟩` from `GlobalTheory.T.lie_lattice_local_basis_description K P F`. Conclude with `fg_and_span_eq_top F.lieLat r M hr (fun i => (hM i).2) hL`.
-/
theorem lieLat_fg_and_span_eq_top :
    ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P),
      F.lieLat.FG ∧ Submodule.span K (F.lieLat : Set (Fin F.P₀.g → K)) = ⊤ := by
  intro K _ _ P F
  obtain ⟨n, r, M, hr, hM, hL, -⟩ := GlobalTheory.T.lie_lattice_local_basis_description K P F
  exact fg_and_span_eq_top F.lieLat r M hr (fun i => (hM i).2) hL

end GlobalTheory.CM.LieLattice
