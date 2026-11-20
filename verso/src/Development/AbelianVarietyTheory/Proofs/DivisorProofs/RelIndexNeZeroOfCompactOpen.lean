import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
open GlobalTheory.LKCount
open scoped Classical

namespace GlobalTheory.RelIndexCompact

/- English proof (translation)
Establish `: CompactSpace L` using `isCompact_iff_compactSpace.mp hL`. Establish `ho : IsOpen ((K.subgroupOf L : Subgroup L) : Set L)` using `hK.preimage continuous_subtype_val`. Use `Subgroup.quotient_finite_of_isOpen _ ho` as an intermediate fact. Conclude with `Subgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_compact_open {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {K L : Subgroup G} (hL : IsCompact (L : Set G))
    (hK : IsOpen (K : Set G)) : K.relIndex L ≠ 0 := by
  have : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((K.subgroupOf L : Subgroup L) : Set L) := hK.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.index_ne_zero_of_finite

/- English proof (translation)
Rewrite using `[Subgroup.coe_map]`. Establish `hc : Continuous (fun g : G => x * g * x⁻¹)` using `by fun_prop`. Use `⟨hK.image hc, ?_⟩` and prove the remaining obligations. Establish `: ((MulAut.conj x).toMonoidHom : G → G) '' (K : Set G) = (fun g : G => x⁻¹ * g * x) ⁻¹' (K : Set G)`. Use extensionality with `y`.

Simplify using `[MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Simplify `ha` using `[mul_assoc]`. Introduce `hy; exact ⟨x⁻¹ * y * x, hy, by group⟩`.

Rewrite using `[this]; exact ho.preimage (by fun_prop)`.
-/
theorem conj_map_isCompact_isOpen {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K : Subgroup G) (x : G) (hK : IsCompact (K : Set G)) (ho : IsOpen (K : Set G)) :
    IsCompact ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) ∧
      IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.coe_map]
  have hc : Continuous (fun g : G => x * g * x⁻¹) := by fun_prop
  refine ⟨hK.image hc, ?_⟩
  have : ((MulAut.conj x).toMonoidHom : G → G) '' (K : Set G) =
      (fun g : G => x⁻¹ * g * x) ⁻¹' (K : Set G) := by
    ext y; simp [MulAut.conj_apply]
    constructor
    · rintro ⟨a, ha, rfl⟩; simpa [mul_assoc] using ha
    · intro hy; exact ⟨x⁻¹ * y * x, hy, by group⟩
  rw [this]; exact ho.preimage (by fun_prop)

end GlobalTheory.RelIndexCompact
