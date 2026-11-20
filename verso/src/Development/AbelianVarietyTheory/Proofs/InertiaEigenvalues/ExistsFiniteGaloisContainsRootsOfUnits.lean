import Mathlib
open NumberField Polynomial

namespace GlobalTheory.KummerUnits

/- English proof (translation)
Introduce `E F Ω _ _ _ _ _ _ _ _ _ M hM ⟨ζ, hζ⟩`. Use `haveI : NeZero M := ⟨hM.ne'⟩`. Use `haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective`. Take `⟨S, hS⟩` from `Monoid.fg_def.1 (inferInstance : Monoid.FG (𝓞 E)ˣ)`. Set `c : (𝓞 E)ˣ → F` to `fun u => algebraMap E F ((u : 𝓞 E) : E)`.

Set `p : F[X]` to `∏ s ∈ S, (X ^ M - C (c s))`. Establish `hp : p ≠ 0` using `Finset.prod_ne_zero_iff.2 fun s _ => X_pow_sub_C_ne_zero hM _`. Set `L` to `IntermediateField.adjoin F (p.rootSet Ω)`. Establish `hsp : p.IsSplittingField F L` using `IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)`. Use `haveI := Polynomial.IsSplittingField.finiteDimensional L p`.

Use `haveI := Normal.of_isSplittingField (F := F) (E := L) p`. Use `⟨L, inferInstance, ⟨⟩, ?_⟩` and prove the remaining obligations. Establish `hζΩ : IsPrimitiveRoot (algebraMap F Ω ζ) M` using `hζ.map_of_injective (algebraMap F Ω).injective`. Establish `hroot : ∀ ξ : Ω, ξ ^ M = 1 → ξ ∈ L`. Introduce `ξ hξ`.

Take `⟨i, -, rfl⟩` from `hζΩ.eq_pow_of_pow_eq_one hξ`. Conclude with `pow_mem (L.algebraMap_mem ζ) i`. Set `φ : (𝓞 E)ˣ →* Ω` to `((algebraMap E Ω).toMonoidHom.comp (algebraMap (𝓞 E) E).toMonoidHom).comp (Units.coeHom _)`. Establish `hφ : ∀ u, φ u = algebraMap E Ω ((u : 𝓞 E) : E)` using `fun u => rfl`. Establish `hφc : ∀ u, φ u = algebraMap F Ω (c u)` using `fun u => IsScalarTower.algebraMap_apply E F Ω _`.

Establish `hφ0 : ∀ u, φ u ≠ 0` using `fun u => ((Group.isUnit u).map φ).ne_zero`. Introduce `u`. Simplify using `only [← hφ]`. Establish `hall : u ∈ Submonoid.closure (S : Set (𝓞 E)ˣ)` using `by rw [hS]; trivial`. Proceed by induction on `hall using Submonoid.closure_induction with`.

Consider the case `mem s hs`. Introduce `w hw`. Apply `IntermediateField.subset_adjoin` to reduce the goal to its premises. Rewrite using `[Polynomial.mem_rootSet]`. Use `⟨hp, ?_⟩` and prove the remaining obligations.

Simplify using `only [p, map_prod]`. Use `Finset.prod_eq_zero hs ?_` and prove the remaining obligations. Simplify using `[hw, hφc]`. Consider the case `one`. Introduce `w hw`.

Conclude with `hroot w (by rw [hw, map_one])`. Consider the case `mul a b _ _ ha hb`. Introduce `w hw`. Take `⟨x, hx⟩` from `IsAlgClosed.exists_pow_nat_eq (φ a) hM`. Take `⟨y, hy⟩` from `IsAlgClosed.exists_pow_nat_eq (φ b) hM`.

Establish `hxy : x * y ≠ 0`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations. Introduce and unpack `rfl; exact hφ0 a (by rw [← hx, zero_pow hM.ne'])`. Introduce and unpack `rfl; exact hφ0 b (by rw [← hy, zero_pow hM.ne'])`. Rewrite using `[← div_mul_cancel₀ w hxy]`.

Use `mul_mem (hroot _ ?_) (mul_mem (ha x hx) (hb y hy))` and prove the remaining obligations. Rewrite using `[div_pow, mul_pow, hx, hy, hw, map_mul, div_self (mul_ne_zero (hφ0 a) (hφ0 b))]`.
-/
theorem exists_finite_galois_mem_of_pow_eq_unit : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by
  intro E F Ω _ _ _ _ _ _ _ _ _ M hM ⟨ζ, hζ⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  obtain ⟨S, hS⟩ := Monoid.fg_def.1 (inferInstance : Monoid.FG (𝓞 E)ˣ)
  let c : (𝓞 E)ˣ → F := fun u => algebraMap E F ((u : 𝓞 E) : E)
  let p : F[X] := ∏ s ∈ S, (X ^ M - C (c s))
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => X_pow_sub_C_ne_zero hM _
  let L := IntermediateField.adjoin F (p.rootSet Ω)
  have hsp : p.IsSplittingField F L :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI := Polynomial.IsSplittingField.finiteDimensional L p
  haveI := Normal.of_isSplittingField (F := F) (E := L) p
  refine ⟨L, inferInstance, ⟨⟩, ?_⟩
  have hζΩ : IsPrimitiveRoot (algebraMap F Ω ζ) M := hζ.map_of_injective (algebraMap F Ω).injective
  have hroot : ∀ ξ : Ω, ξ ^ M = 1 → ξ ∈ L := by
    intro ξ hξ
    obtain ⟨i, -, rfl⟩ := hζΩ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (L.algebraMap_mem ζ) i
  let φ : (𝓞 E)ˣ →* Ω :=
    ((algebraMap E Ω).toMonoidHom.comp (algebraMap (𝓞 E) E).toMonoidHom).comp (Units.coeHom _)
  have hφ : ∀ u, φ u = algebraMap E Ω ((u : 𝓞 E) : E) := fun u => rfl
  have hφc : ∀ u, φ u = algebraMap F Ω (c u) := fun u => IsScalarTower.algebraMap_apply E F Ω _
  have hφ0 : ∀ u, φ u ≠ 0 := fun u => ((Group.isUnit u).map φ).ne_zero
  intro u
  simp only [← hφ]
  have hall : u ∈ Submonoid.closure (S : Set (𝓞 E)ˣ) := by rw [hS]; trivial
  induction hall using Submonoid.closure_induction with
  | mem s hs =>
    intro w hw
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    simp only [p, map_prod]
    refine Finset.prod_eq_zero hs ?_
    simp [hw, hφc]
  | one =>
    intro w hw
    exact hroot w (by rw [hw, map_one])
  | mul a b _ _ ha hb =>
    intro w hw
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (φ a) hM
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (φ b) hM
    have hxy : x * y ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · rintro rfl; exact hφ0 a (by rw [← hx, zero_pow hM.ne'])
      · rintro rfl; exact hφ0 b (by rw [← hy, zero_pow hM.ne'])
    rw [← div_mul_cancel₀ w hxy]
    refine mul_mem (hroot _ ?_) (mul_mem (ha x hx) (hb y hy))
    rw [div_pow, mul_pow, hx, hy, hw, map_mul, div_self (mul_ne_zero (hφ0 a) (hφ0 b))]

end GlobalTheory.KummerUnits
