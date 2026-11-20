import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.IsClassFieldHilbert
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.GrMaxOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.AugKer

open NumberField IsDedekindDomain IntermediateField UpperTheory.V.Kum UpperTheory.V.CF
open scoped Pointwise

/- English proof (translation)
Introduce `p _ R G _ _ _ _ hpm hG`. Use `set J : Ideal (MonoidAlgebra R G) := (IsLocalRing.maximalIdeal R).comap (aug R G) with hJdef`. Establish `hJ : J.IsMaximal` using `Ideal.comap_isMaximal_of_surjective (aug R G) (UpperTheory.V.CF.augKer R G).2`. Establish `huniq : ∃! I : Ideal (MonoidAlgebra R G), I.IsMaximal` using `⟨J, hJ, fun M hM => UpperTheory.V.CF.grMaxOf p R G hpm hG M hM⟩`. Use `letI hloc : IsLocalRing (MonoidAlgebra R G) := IsLocalRing.of_unique_max_ideal huniq`.

Establish `hmax : IsLocalRing.maximalIdeal (MonoidAlgebra R G) = J` using `(IsLocalRing.eq_maximalIdeal hJ).symm`. Establish `hsec : ∀ r : R, aug R G (algebraMap R (MonoidAlgebra R G) r) = r` using `fun r => (aug R G).commutes r`. Use `⟨hloc, hmax, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hmax]`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce `x hx`. Establish `hax : aug R G x ∈ IsLocalRing.maximalIdeal R` using `hx`. Establish `h1 : algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R (MonoidAlgebra R G))` using `Ideal.mem_map_of_mem _ hax`. Establish `h2 : x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G`. Rewrite using `[← (UpperTheory.V.CF.augKer R G).1, RingHom.mem_ker]`.

Use `show aug R G (x - algebraMap R (MonoidAlgebra R G) (aug R G x)) = 0`. Rewrite using `[map_sub, hsec, sub_self]`. Establish `: x = algebraMap R (MonoidAlgebra R G) (aug R G x) + (x - algebraMap R (MonoidAlgebra R G) (aug R G x))` using `by ring`. Rewrite using `[this]`. Conclude with `Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)`.

Apply `sup_le` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `r hr`. Use `show aug R G (algebraMap R (MonoidAlgebra R G) r) ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[hsec]`.

Conclude with `hr`. Introduce `x hx`. Rewrite `hx` using `[← (UpperTheory.V.CF.augKer R G).1, RingHom.mem_ker]`. Use `show aug R G x ∈ IsLocalRing.maximalIdeal R`. Rewrite using `[show aug R G x = 0 from hx]`.

Conclude with `zero_mem _`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `hx.map (aug R G)`.

Introduce `hx`. Assume the negation of the conclusion as `hnx`. Establish `hxm : x ∈ IsLocalRing.maximalIdeal (MonoidAlgebra R G)` using `hnx`. Rewrite `hxm` using `[hmax]`. Conclude with `hxm hx`.
-/
theorem UpperTheory.V.CF.grLocal :
    ∀ (p : ℕ) [Fact p.Prime] (R G : Type) [CommRing R] [IsLocalRing R] [CommGroup G] [Finite G], (p : R) ∈ IsLocalRing.maximalIdeal R → IsPGroup p G → ∃ _ : IsLocalRing (MonoidAlgebra R G), IsLocalRing.maximalIdeal (MonoidAlgebra R G) = (IsLocalRing.maximalIdeal R).comap (aug R G) ∧ IsLocalRing.maximalIdeal (MonoidAlgebra R G) = (IsLocalRing.maximalIdeal R).map (algebraMap R (MonoidAlgebra R G)) ⊔ augIdeal R G ∧ ∀ x, IsUnit x ↔ IsUnit (aug R G x) := by
  intro p _ R G _ _ _ _ hpm hG
  set J : Ideal (MonoidAlgebra R G) := (IsLocalRing.maximalIdeal R).comap (aug R G) with hJdef
  have hJ : J.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (aug R G) (UpperTheory.V.CF.augKer R G).2
  have huniq : ∃! I : Ideal (MonoidAlgebra R G), I.IsMaximal :=
    ⟨J, hJ, fun M hM => UpperTheory.V.CF.grMaxOf p R G hpm hG M hM⟩
  letI hloc : IsLocalRing (MonoidAlgebra R G) := IsLocalRing.of_unique_max_ideal huniq
  have hmax : IsLocalRing.maximalIdeal (MonoidAlgebra R G) = J :=
    (IsLocalRing.eq_maximalIdeal hJ).symm
  have hsec : ∀ r : R, aug R G (algebraMap R (MonoidAlgebra R G) r) = r := fun r => (aug R G).commutes r
  refine ⟨hloc, hmax, ?_, ?_⟩
  · rw [hmax]
    apply le_antisymm
    · intro x hx
      have hax : aug R G x ∈ IsLocalRing.maximalIdeal R := hx
      have h1 : algebraMap R (MonoidAlgebra R G) (aug R G x) ∈
          (IsLocalRing.maximalIdeal R).map (algebraMap R (MonoidAlgebra R G)) :=
        Ideal.mem_map_of_mem _ hax
      have h2 : x - algebraMap R (MonoidAlgebra R G) (aug R G x) ∈ augIdeal R G := by
        rw [← (UpperTheory.V.CF.augKer R G).1, RingHom.mem_ker]
        show aug R G (x - algebraMap R (MonoidAlgebra R G) (aug R G x)) = 0
        rw [map_sub, hsec, sub_self]
      have : x = algebraMap R (MonoidAlgebra R G) (aug R G x) +
          (x - algebraMap R (MonoidAlgebra R G) (aug R G x)) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    · apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        intro r hr
        show aug R G (algebraMap R (MonoidAlgebra R G) r) ∈ IsLocalRing.maximalIdeal R
        rw [hsec]
        exact hr
      · intro x hx
        rw [← (UpperTheory.V.CF.augKer R G).1, RingHom.mem_ker] at hx
        show aug R G x ∈ IsLocalRing.maximalIdeal R
        rw [show aug R G x = 0 from hx]
        exact zero_mem _
  · intro x
    constructor
    · intro hx
      exact hx.map (aug R G)
    · intro hx
      by_contra hnx
      have hxm : x ∈ IsLocalRing.maximalIdeal (MonoidAlgebra R G) := hnx
      rw [hmax] at hxm
      exact hxm hx
