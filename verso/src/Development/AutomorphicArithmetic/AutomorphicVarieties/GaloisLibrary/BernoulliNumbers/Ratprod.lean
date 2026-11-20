import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Charbij

open Finset UpperTheory.V.Bern

/- English proof (translation)
Introduce `N _ P F hF`. Use `set e := Monoid.exponent (ZMod N)ˣ with he_def`. Use `haveI he : NeZero e := ⟨Monoid.exponent_ne_zero_of_finite⟩`. Use `haveI : NeZero (e : ℚ) := ⟨by exact_mod_cast he.out⟩`. Use `haveI hcyc : IsCyclotomicExtension {e} ℚ (CyclotomicField e ℚ) := CyclotomicField.isCyclotomicExtension e ℚ`.

Use `haveI : IsGalois ℚ (CyclotomicField e ℚ) := IsCyclotomicExtension.isGalois {e} ℚ _`. Use `haveI : FiniteDimensional ℚ (CyclotomicField e ℚ) := IsCyclotomicExtension.finiteDimensional {e} ℚ _`. Establish `hζ` using `IsCyclotomicExtension.zeta_spec e ℚ (CyclotomicField e ℚ)`. Use `haveI : HasEnoughRootsOfUnity (CyclotomicField e ℚ) e := ⟨⟨_, hζ⟩, rootsOfUnity.isCyclic (CyclotomicField e ℚ) e⟩`. Establish `hfin : ∀ (Ω : Type) [Field Ω], (charSet Ω P).Finite` using `fun Ω _ => Set.toFinite _`.

Establish `hfix : ∀ σ : CyclotomicField e ℚ ≃ₐ[ℚ] CyclotomicField e ℚ, σ (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) = ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ`. Introduce `σ`. Establish `h1` using `(σ.toRingHom.toMonoidHom).map_finprod_mem (fun χ => F (CyclotomicField e ℚ) χ) (hfin (CyclotomicField e ℚ))`. Use `h1.trans ?_` and prove the remaining obligations. Conclude with `finprod_mem_eq_of_bijOn _ (b_charbij σ.toRingHom P) (fun χ _ => hF _ _ σ.toRingHom χ)`.

Establish `hbot` using `(IsGalois.mem_bot_iff_fixed _).2 hfix`. Take `⟨q, hq⟩` from `IntermediateField.mem_bot.1 hbot`. Use `⟨q, fun Ω _ _ _ => ?_⟩` and prove the remaining obligations. Take `⟨ω, hω⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω e`. Establish `hmin : Polynomial.aeval ω (minpoly ℚ (hζ.powerBasis ℚ).gen) = 0`.

Rewrite using `[IsPrimitiveRoot.powerBasis_gen, ← hζ.minpoly_eq_cyclotomic_of_irreducible (Polynomial.cyclotomic.irreducible_rat (NeZero.pos e)), Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]`. Conclude with `hω.isRoot_cyclotomic (NeZero.pos e)`. Set `g` to `(hζ.powerBasis ℚ).lift ω hmin`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hq]`.

Conclude with `g.commutes q |>.trans (eq_ratCast _ q)`.
-/
theorem UpperTheory.V.Bern.b_ratprod :
    ∀ {N : ℕ} [NeZero N] (P : Set (Subgroup (ZMod N)ˣ)) (F : ∀ (Ω : Type) [Field Ω] [CharZero Ω], DirichletCharacter Ω N → Ω), (∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [CharZero Ω] (f : K →+* Ω) (χ : DirichletCharacter K N), f (F K χ) = F Ω (χ.ringHomComp f)) → ∃ q : ℚ, ∀ (Ω : Type) [Field Ω] [CharZero Ω] [HasEnoughRootsOfUnity Ω (Monoid.exponent (ZMod N)ˣ)], ∏ᶠ χ ∈ charSet Ω P, F Ω χ = (q : Ω) := by
  intro N _ P F hF
  set e := Monoid.exponent (ZMod N)ˣ with he_def
  haveI he : NeZero e := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : NeZero (e : ℚ) := ⟨by exact_mod_cast he.out⟩
  haveI hcyc : IsCyclotomicExtension {e} ℚ (CyclotomicField e ℚ) :=
    CyclotomicField.isCyclotomicExtension e ℚ
  haveI : IsGalois ℚ (CyclotomicField e ℚ) := IsCyclotomicExtension.isGalois {e} ℚ _
  haveI : FiniteDimensional ℚ (CyclotomicField e ℚ) :=
    IsCyclotomicExtension.finiteDimensional {e} ℚ _
  have hζ := IsCyclotomicExtension.zeta_spec e ℚ (CyclotomicField e ℚ)
  haveI : HasEnoughRootsOfUnity (CyclotomicField e ℚ) e :=
    ⟨⟨_, hζ⟩, rootsOfUnity.isCyclic (CyclotomicField e ℚ) e⟩
  have hfin : ∀ (Ω : Type) [Field Ω], (charSet Ω P).Finite := fun Ω _ => Set.toFinite _
  have hfix : ∀ σ : CyclotomicField e ℚ ≃ₐ[ℚ] CyclotomicField e ℚ,
      σ (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) =
        ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ := by
    intro σ
    have h1 := (σ.toRingHom.toMonoidHom).map_finprod_mem
      (fun χ => F (CyclotomicField e ℚ) χ) (hfin (CyclotomicField e ℚ))
    refine h1.trans ?_
    exact finprod_mem_eq_of_bijOn _ (b_charbij σ.toRingHom P)
      (fun χ _ => hF _ _ σ.toRingHom χ)
  have hbot := (IsGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.1 hbot
  refine ⟨q, fun Ω _ _ _ => ?_⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω e
  have hmin : Polynomial.aeval ω (minpoly ℚ (hζ.powerBasis ℚ).gen) = 0 := by
    rw [IsPrimitiveRoot.powerBasis_gen, ← hζ.minpoly_eq_cyclotomic_of_irreducible
      (Polynomial.cyclotomic.irreducible_rat (NeZero.pos e)), Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hω.isRoot_cyclotomic (NeZero.pos e)
  let g := (hζ.powerBasis ℚ).lift ω hmin
  calc ∏ᶠ χ ∈ charSet Ω P, F Ω χ
      = ∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, g.toRingHom (F (CyclotomicField e ℚ) χ) :=
        (finprod_mem_eq_of_bijOn _ (b_charbij g.toRingHom P)
          (fun χ _ => hF _ _ g.toRingHom χ)).symm
    _ = g.toRingHom (∏ᶠ χ ∈ charSet (CyclotomicField e ℚ) P, F (CyclotomicField e ℚ) χ) :=
        (g.toRingHom.toMonoidHom.map_finprod_mem _ (hfin _)).symm
    _ = (q : Ω) := by
        rw [← hq]
        exact g.commutes q |>.trans (eq_ratCast _ q)
