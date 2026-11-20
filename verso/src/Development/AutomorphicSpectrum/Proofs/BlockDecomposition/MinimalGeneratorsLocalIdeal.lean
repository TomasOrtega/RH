import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CechHOneVanishesOnOpenOfIsAffineOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMulTrInv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.FewEq
open GlobalTheory.AbLaw (rs)

namespace GlobalTheory.CompanionTheory.FewEq

/- English proof (translation)
Use `⟨fun j => t (l.succAbove j), le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Rewrite using `[← ht]`. Conclude with `Ideal.subset_span ⟨_, rfl⟩`.

Use `set N : Ideal R := Ideal.span (Set.range fun j => t (l.succAbove j)) with hN`. Establish `hmem : ∀ j, t (l.succAbove j) ∈ N` using `fun j => Ideal.subset_span ⟨j, rfl⟩`. Establish `htl : t l ∈ N ⊔ IsLocalRing.maximalIdeal R • I`. Take `⟨u, hu⟩` from `hu`. Establish `hsum : x l * t l = ∑ i, x i * t i - ∑ j, x (l.succAbove j) * t (l.succAbove j)`.

Rewrite using `[Fin.sum_univ_succAbove _ l]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : x l * t l ∈ N ⊔ IsLocalRing.maximalIdeal R • I`. Rewrite using `[hsum]`. Use `Ideal.sub_mem _ (Ideal.mem_sup_right (by simpa [smul_eq_mul] using hx)) ?_` and prove the remaining obligations.

Conclude with `Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmem j))`. Establish `h2 : t l = (↑u⁻¹ : R) * (x l * t l)`. Rewrite using `[← hu, ← mul_assoc, Units.inv_mul, one_mul]`. Rewrite using `[h2]`. Conclude with `Ideal.mul_mem_left _ _ h1`.

Establish `hle : I ≤ N ⊔ IsLocalRing.maximalIdeal R • I` using `by conv_lhs => rw [← ht]`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Break down `Fin.eq_self_or_eq_succAbove l i with h | ⟨j, h⟩` into its components or cases. Rewrite using `[h]`.

Conclude with `htl`. Rewrite using `[h]`. Conclude with `Ideal.mem_sup_left (hmem j)`. Conclude with `Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I) (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle`.
-/
theorem exists_fin_span_eq_of_unit_coeff {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (I : Ideal R) {n : ℕ} (t : Fin (n + 1) → R)
    (ht : Ideal.span (Set.range t) = I) (x : Fin (n + 1) → R)
    (hx : ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I) (l : Fin (n + 1))
    (hu : IsUnit (x l)) : ∃ s : Fin n → R, Ideal.span (Set.range s) = I := by
  refine ⟨fun j => t (l.succAbove j), le_antisymm ?_ ?_⟩
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← ht]
    exact Ideal.subset_span ⟨_, rfl⟩
  set N : Ideal R := Ideal.span (Set.range fun j => t (l.succAbove j)) with hN
  have hmem : ∀ j, t (l.succAbove j) ∈ N := fun j => Ideal.subset_span ⟨j, rfl⟩
  have htl : t l ∈ N ⊔ IsLocalRing.maximalIdeal R • I := by
    obtain ⟨u, hu⟩ := hu
    have hsum : x l * t l = ∑ i, x i * t i - ∑ j, x (l.succAbove j) * t (l.succAbove j) := by
      rw [Fin.sum_univ_succAbove _ l]
      ring
    have h1 : x l * t l ∈ N ⊔ IsLocalRing.maximalIdeal R • I := by
      rw [hsum]
      refine Ideal.sub_mem _ (Ideal.mem_sup_right (by simpa [smul_eq_mul] using hx)) ?_
      exact Ideal.mem_sup_left (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hmem j))
    have h2 : t l = (↑u⁻¹ : R) * (x l * t l) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
  have hle : I ≤ N ⊔ IsLocalRing.maximalIdeal R • I := by
    conv_lhs => rw [← ht]
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove l i with h | ⟨j, h⟩
    · rw [h]; exact htl
    · rw [h]; exact Ideal.mem_sup_left (hmem j)
  exact Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle

/- English proof (translation)
Introduce `R _ _ _ I`. Establish `hex : ∃ r : ℕ, ∃ t : Fin r → R, Ideal.span (Set.range t) = I` using `Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)`. Take `⟨t, ht⟩` from `Nat.find_spec hex`. Use `⟨_, t, ht, fun x hx l => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hl`.

Establish `hu : IsUnit (x l)`. Assume the negation of the conclusion as `h`. Conclude with `hl ((IsLocalRing.mem_maximalIdeal _).mpr h)`. Establish `hmin : ∀ m : ℕ, (∃ s : Fin m → R, Ideal.span (Set.range s) = I) → Nat.find hex ≤ m` using `fun m h => Nat.find_min' hex h`. Generalize the expression as in `Nat.find hex = r at t ht x hx l hu hmin`.

Consider the cases of `r with`. Consider the case `zero => exact l.elim0`. Consider the case `succ n`. Use `hmin n (exists_fin_span_eq_of_unit_coeff I t ht x hx l hu)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_minimal_generators : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R),
    ∃ (r : ℕ) (t : Fin r → R), Ideal.span (Set.range t) = I ∧
      ∀ x : Fin r → R, ∑ i, x i * t i ∈ IsLocalRing.maximalIdeal R * I → ∀ i, x i ∈ IsLocalRing.maximalIdeal R := by
  intro R _ _ _ I
  classical
  have hex : ∃ r : ℕ, ∃ t : Fin r → R, Ideal.span (Set.range t) = I :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  obtain ⟨t, ht⟩ := Nat.find_spec hex
  refine ⟨_, t, ht, fun x hx l => ?_⟩
  by_contra hl
  have hu : IsUnit (x l) := by
    by_contra h
    exact hl ((IsLocalRing.mem_maximalIdeal _).mpr h)
  have hmin : ∀ m : ℕ, (∃ s : Fin m → R, Ideal.span (Set.range s) = I) → Nat.find hex ≤ m :=
    fun m h => Nat.find_min' hex h
  generalize Nat.find hex = r at t ht x hx l hu hmin
  cases r with
  | zero => exact l.elim0
  | succ n =>
    have := hmin n (exists_fin_span_eq_of_unit_coeff I t ht x hx l hu)
    omega

end GlobalTheory.CompanionTheory.FewEq
