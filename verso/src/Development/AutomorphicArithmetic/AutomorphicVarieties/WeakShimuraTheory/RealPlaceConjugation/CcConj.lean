import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

/- English proof (translation)
Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ`. Use `haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic`. Set `jA : Ω →ₐ[ℚ] ℂ` to `j.toRatAlgHom`. Set `iA : Ω →ₐ[ℚ] ℂ` to `i.toRatAlgHom`. Set `K : IntermediateField ℚ ℂ` to `jA.fieldRange`.

Set `r : Ω →+* K` to `{ toFun := fun x => ⟨jA x, jA.mem_fieldRange.2 ⟨x, rfl⟩⟩ map_one' := by ext; simp map_mul' := by intro x y; ext; simp map_zero' := by ext; simp map_add' := by intro x y; ext; simp }`. Establish `hr : Function.Bijective r`. Prove the components needed by the constructor for the conclusion. Introduce `x y hxy`. Establish `: jA x = jA y` using `congrArg Subtype.val hxy`.

Conclude with `jA.toRingHom.injective this`. Introduce and unpack `⟨z, hz⟩`. Take `⟨x, rfl⟩` from `jA.mem_fieldRange.1 hz`. Conclude with `⟨x, rfl⟩`. Use `haveI : IsAlgClosed K := IsAlgClosed.of_ringEquiv Ω K (RingEquiv.ofBijective r hr)`.

Establish `hi : ∀ x, ∃ y, j y = i x`. Introduce `x`. Establish `h1 : IsIntegral ℚ (iA x)` using `(Algebra.IsIntegral.isIntegral x).map iA`. Establish `h2 : IsIntegral K (iA x)` using `h1.tower_top`. Establish `h3` using `minpoly.mem_range_of_degree_eq_one K (iA x) (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h2))`.

Take `⟨k, hk⟩` from `h3`. Take `⟨y, hy⟩` from `jA.mem_fieldRange.1 k.2`. Use `⟨y, ?_⟩` and prove the remaining obligations. Establish `: jA y = iA x` using `by rw [hy]; exact hk`. Conclude with `this`.

Use `choose φ hφ using hi`. Set `h0 : Ω →+* Ω` to `{ toFun := φ map_one' := j.injective (by rw [hφ, map_one, map_one]) map_mul' := fun x y => j.injective (by rw [hφ, map_mul, map_mul, hφ, hφ]) map_zero' := j.injective (by rw [hφ, map_zero, map_zero]) map_add' := fun x y => j.injective (by rw [hφ, map_add, map_add, hφ, hφ]) }`. Set `hA : Ω →ₐ[ℚ] Ω` to `h0.toRatAlgHom`. Establish `hb : Function.Bijective hA` using `Algebra.IsAlgebraic.algHom_bijective hA`. Conclude with `⟨AlgEquiv.ofBijective hA hb, fun x => hφ x⟩`.
-/
private theorem emb_twist {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (i j : Ω →+* ℂ) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, ∀ x, j (g x) = i x := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  let jA : Ω →ₐ[ℚ] ℂ := j.toRatAlgHom
  let iA : Ω →ₐ[ℚ] ℂ := i.toRatAlgHom
  let K : IntermediateField ℚ ℂ := jA.fieldRange
  let r : Ω →+* K :=
    { toFun := fun x => ⟨jA x, jA.mem_fieldRange.2 ⟨x, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hr : Function.Bijective r := by
    constructor
    · intro x y hxy
      have : jA x = jA y := congrArg Subtype.val hxy
      exact jA.toRingHom.injective this
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := jA.mem_fieldRange.1 hz
      exact ⟨x, rfl⟩
  haveI : IsAlgClosed K := IsAlgClosed.of_ringEquiv Ω K (RingEquiv.ofBijective r hr)
  have hi : ∀ x, ∃ y, j y = i x := by
    intro x
    have h1 : IsIntegral ℚ (iA x) := (Algebra.IsIntegral.isIntegral x).map iA
    have h2 : IsIntegral K (iA x) := h1.tower_top
    have h3 := minpoly.mem_range_of_degree_eq_one K (iA x)
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible h2))
    obtain ⟨k, hk⟩ := h3
    obtain ⟨y, hy⟩ := jA.mem_fieldRange.1 k.2
    refine ⟨y, ?_⟩
    have : jA y = iA x := by rw [hy]; exact hk
    exact this
  choose φ hφ using hi
  let h0 : Ω →+* Ω :=
    { toFun := φ
      map_one' := j.injective (by rw [hφ, map_one, map_one])
      map_mul' := fun x y => j.injective (by rw [hφ, map_mul, map_mul, hφ, hφ])
      map_zero' := j.injective (by rw [hφ, map_zero, map_zero])
      map_add' := fun x y => j.injective (by rw [hφ, map_add, map_add, hφ, hφ]) }
  let hA : Ω →ₐ[ℚ] Ω := h0.toRatAlgHom
  have hb : Function.Bijective hA := Algebra.IsAlgebraic.algHom_bijective hA
  exact ⟨AlgEquiv.ofBijective hA hb, fun x => hφ x⟩

/- English proof (translation)
Introduce `Ω _ _ _ σ τ hσ hτ`. Take `⟨jσ, hjσ⟩` from `hσ`. Take `⟨jτ, hjτ⟩` from `hτ`. Take `⟨g, hg⟩` from `emb_twist jσ jτ`. Rewrite using `[isConj_iff]`.

Use `⟨g, AlgEquiv.ext fun y => jτ.injective ?_⟩` and prove the remaining obligations. Establish `e1 : jσ (g⁻¹ y) = jτ y`. Rewrite using `[← hg]`. Use `congr 1`. Conclude with `AlgEquiv.apply_symm_apply g y`.

Use `show jτ (g (σ (g⁻¹ y))) = jτ (τ y)`. Rewrite using `[hg, hjσ, e1, hjτ]`.
-/
theorem UpperTheory.V.Ws.isConj_of_isComplexConjugation :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (σ τ : G ℚ Ω), IsCC σ → IsCC τ → IsConj σ τ := by
  intro Ω _ _ _ σ τ hσ hτ
  obtain ⟨jσ, hjσ⟩ := hσ
  obtain ⟨jτ, hjτ⟩ := hτ
  obtain ⟨g, hg⟩ := emb_twist jσ jτ
  rw [isConj_iff]
  refine ⟨g, AlgEquiv.ext fun y => jτ.injective ?_⟩
  have e1 : jσ (g⁻¹ y) = jτ y := by
    rw [← hg]
    congr 1
    exact AlgEquiv.apply_symm_apply g y
  show jτ (g (σ (g⁻¹ y))) = jτ (τ y)
  rw [hg, hjσ, e1, hjτ]
