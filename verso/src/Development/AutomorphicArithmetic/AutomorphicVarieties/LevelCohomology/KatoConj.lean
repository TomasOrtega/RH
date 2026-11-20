import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.KatoBkMap

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

/- English proof (translation)
Introduce `l _ F Ω _ _ _ _ n r r' ⟨P, hP⟩ h c hc hbk`. Set `f : (Fin n → Qbar l) →ₗ[ℚ_[l]] (Fin n → Qbar l)` to `(Matrix.mulVecLin ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))).restrictScalars ℚ_[l]`. Establish `hfa : ∀ x, f x = ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x` using `fun _ => rfl`. Establish `hcol : ∀ (ρ : G F Ω →* GL (Fin n) (Qbar l)) g x, Loc.colRep ρ g x = (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x` using `fun _ _ _ => rfl`. Establish `hf : ∀ g x, f (Loc.colRep r' g x) = Loc.colRep r g (f x)`.

Introduce `g x`. Rewrite using `[hfa, hfa, hcol, hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hP]`. Use `congr 2`. Use `group`. Establish `hinj : Function.Injective f`.

Introduce `x y hxy`. Use `congrArg ((P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec) hxy` as an intermediate fact. Rewrite `this` using `[hfa, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec]`. Then use the resulting hypothesis. Establish `hsurj : Function.Surjective f`. Introduce `y`.

Use `⟨(P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec y, ?_⟩` and prove the remaining obligations. Rewrite using `[hfa, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Establish `hcont : Continuous (fun g => f (c g))`. Simplify using `only [hfa]`. Conclude with `continuous_const.matrix_mulVec hc.1`.

Establish `hz : (fun g => f (c g)) ∈ Z1 (Loc.colRep r)`. Use `⟨hcont, fun g g' => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg f (hc.2 g g')`. Simplify `h1` using `only [map_add, hf]`. Take `⟨m, hm⟩` from `(mem_coboundaries1 _ _).1 (h _ hz (UpperTheory.V.X.Kato.bkMap l F Ω _ _ _ _ _ _ f hf c hcont hbk))`.

Take `⟨m', rfl⟩` from `hsurj m`. Use `(mem_coboundaries1 _ _).2 ⟨m', fun g => hinj ?_⟩` and prove the remaining obligations. Use `hm g` as an intermediate fact. Simplify using `only [map_sub, hf]`. Conclude with `this`.
-/
theorem UpperTheory.V.X.Kato.conj :
    ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (n : ℕ) (r r' : G F Ω →* GL (Fin n) (Qbar l)), RepIso r r' → BlochKatoSelmerVanishes l (Loc.colRep r) → BlochKatoSelmerVanishes l (Loc.colRep r') := by
  intro l _ F Ω _ _ _ _ n r r' ⟨P, hP⟩ h c hc hbk
  let f : (Fin n → Qbar l) →ₗ[ℚ_[l]] (Fin n → Qbar l) :=
    (Matrix.mulVecLin ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))).restrictScalars ℚ_[l]
  have hfa : ∀ x, f x = ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x := fun _ => rfl
  have hcol : ∀ (ρ : G F Ω →* GL (Fin n) (Qbar l)) g x,
      Loc.colRep ρ g x = (ρ g : Matrix (Fin n) (Fin n) (Qbar l)).mulVec x := fun _ _ _ => rfl
  have hf : ∀ g x, f (Loc.colRep r' g x) = Loc.colRep r g (f x) := by
    intro g x
    rw [hfa, hfa, hcol, hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hP]
    congr 2
    group
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg ((P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec) hxy
    rwa [hfa, hfa, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec, Matrix.one_mulVec] at this
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨(P : Matrix (Fin n) (Fin n) (Qbar l)).mulVec y, ?_⟩
    rw [hfa, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hcont : Continuous (fun g => f (c g)) := by
    simp only [hfa]
    exact continuous_const.matrix_mulVec hc.1
  have hz : (fun g => f (c g)) ∈ Z1 (Loc.colRep r) := by
    refine ⟨hcont, fun g g' => ?_⟩
    have h1 := congrArg f (hc.2 g g')
    simpa only [map_add, hf] using h1
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 (h _ hz (UpperTheory.V.X.Kato.bkMap l F Ω _ _ _ _ _ _ f hf c hcont hbk))
  obtain ⟨m', rfl⟩ := hsurj m
  refine (mem_coboundaries1 _ _).2 ⟨m', fun g => hinj ?_⟩
  have := hm g
  simp only [map_sub, hf]
  exact this
