import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LevelInertiaLeLevelDec
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.RestrictScalarsTwistInvOver

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology UpperTheory.V.LDataCardLeFinrank

/- English proof (translation)
Introduce `l _ U tr`. Establish `e : ZlSub l = (1 : Submodule ℤ_[l] ℚ_[l])` using `Submodule.one_eq_range.symm`. Set `f : QZ l ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.QmodZ l` to `Submodule.quotEquivOfEq _ _ e`. Establish `hmap : (KStar.TotallyRealRoots.twistInv l (QZ l) U tr).map (f : QZ l →ₗ[ℤ_[l]] KStar.TotallyRealRoots.QmodZ l) = KStar.TotallyRealRoots.twistInv l (KStar.TotallyRealRoots.QmodZ l) U tr`. Use extensionality with `y`.

Simplify using `only [Submodule.mem_map, KStar.TotallyRealRoots.mem_twistInv]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩ u hu`. Rewrite using `[LinearEquiv.coe_coe, ← f.map_smul, hx u hu]`. Introduce `hy`.

Use `⟨f.symm y, fun u hu => ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[← f.symm.map_smul, hy u hu]`. Set `g : KStar.TotallyRealRoots.twistInv l (QZ l) U tr ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.H0 l U tr` to `(f.submoduleMap _).trans (LinearEquiv.ofEq _ _ hmap)`. Establish `hnu : ¬IsUnit ((l : ℕ) : ℤ_[l])` using `PadicInt.irreducible_p.not_isUnit`. Establish `h` using `KStar.TotallyRealRoots.length_twistInvOver (O := ℤ_[l]) ℚ_[l] hnu U tr`.

Establish `hv : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) = 1` using `IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p`. Rewrite `h` using `[hv, mul_one]`. Establish `hsame : KStar.TotallyRealRoots.twistInvOver l ℤ_[l] (KStar.Selmer.FracMod ℤ_[l] ℚ_[l]) U tr = KStar.TotallyRealRoots.twistInv l (KStar.TotallyRealRoots.QmodZ l) U tr`. Use extensionality with `x`. Rewrite using `[KStar.TotallyRealRoots.mem_twistInv]`.

Both sides reduce to the same expression. Rewrite `h` using `[hsame]`. Use `⟨?_, ⟨g⟩⟩` and prove the remaining obligations. Rewrite using `[g.length_eq]`. Conclude with `h`.
-/
theorem UpperTheory.V.LDataCardLeFinrank.lenTwist :
    ∀ (l : ℕ) [Fact l.Prime] (U : Subgroup ℤ_[l]ˣ) (tr : ℕ), Module.length ℤ_[l] (KStar.TotallyRealRoots.twistInv l (QZ l) U tr) = KStar.TotallyRealRoots.nu l U tr ∧ Nonempty (KStar.TotallyRealRoots.twistInv l (QZ l) U tr ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.H0 l U tr) := by
  intro l _ U tr
  have e : ZlSub l = (1 : Submodule ℤ_[l] ℚ_[l]) := Submodule.one_eq_range.symm
  let f : QZ l ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.QmodZ l := Submodule.quotEquivOfEq _ _ e
  have hmap : (KStar.TotallyRealRoots.twistInv l (QZ l) U tr).map (f : QZ l →ₗ[ℤ_[l]] KStar.TotallyRealRoots.QmodZ l) =
      KStar.TotallyRealRoots.twistInv l (KStar.TotallyRealRoots.QmodZ l) U tr := by
    ext y
    simp only [Submodule.mem_map, KStar.TotallyRealRoots.mem_twistInv]
    constructor
    · rintro ⟨x, hx, rfl⟩ u hu
      rw [LinearEquiv.coe_coe, ← f.map_smul, hx u hu]
    · intro hy
      refine ⟨f.symm y, fun u hu => ?_, by simp⟩
      rw [← f.symm.map_smul, hy u hu]
  let g : KStar.TotallyRealRoots.twistInv l (QZ l) U tr ≃ₗ[ℤ_[l]] KStar.TotallyRealRoots.H0 l U tr :=
    (f.submoduleMap _).trans (LinearEquiv.ofEq _ _ hmap)
  have hnu : ¬IsUnit ((l : ℕ) : ℤ_[l]) := PadicInt.irreducible_p.not_isUnit
  have h := KStar.TotallyRealRoots.length_twistInvOver (O := ℤ_[l]) ℚ_[l] hnu U tr
  have hv : IsDiscreteValuationRing.addVal ℤ_[l] (l : ℤ_[l]) = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer PadicInt.irreducible_p
  rw [hv, mul_one] at h
  have hsame : KStar.TotallyRealRoots.twistInvOver l ℤ_[l] (KStar.Selmer.FracMod ℤ_[l] ℚ_[l]) U tr =
      KStar.TotallyRealRoots.twistInv l (KStar.TotallyRealRoots.QmodZ l) U tr := by
    ext x
    rw [KStar.TotallyRealRoots.mem_twistInv]
    rfl
  rw [hsame] at h
  refine ⟨?_, ⟨g⟩⟩
  rw [g.length_eq]
  exact h
