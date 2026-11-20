import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DehomogeniseBinaryPolyHomogeneousEquivSlashStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLaws
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.CocPot

/- English proof (translation)
Use `show (0 : ℝ) < Complex.I.im`. Simplify using the standard rewrite rules.
-/
theorem I_mem : Complex.I ∈ Hs := by
  show (0 : ℝ) < Complex.I.im
  simp

/- English proof (translation)
The claim follows from `(Betti.polySlash_isHomogeneous _ (hF.1 _)).sub (hF.1 z)`.
-/
theorem hom_inc {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w Γ)
    (γ : SL(2, ℤ)) (z : ℂ) :
    (slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) z)) - F z).IsHomogeneous w :=
  (Betti.polySlash_isHomogeneous _ (hF.1 _)).sub (hF.1 z)

/- English proof (translation)
Take `⟨p, hp⟩` from `hF.2 γ hγ`. Rewrite using `[hp z hz, hp _ I_mem]`.
-/
theorem inc_eq {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w Γ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) {z : ℂ} (hz : z ∈ Hs) :
    slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) z)) - F z =
      slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) Complex.I)) - F Complex.I := by
  obtain ⟨p, hp⟩ := hF.2 γ hγ
  rw [hp z hz, hp _ I_mem]

/- English proof (translation)
Establish `hδI` using `mob_laws.1 (ofSL δ) _ I_mem`. Establish `hm : mob (ofSL (γ * δ)) Complex.I = mob (ofSL γ) (mob (ofSL δ) Complex.I)`. Rewrite using `[map_mul]`. Conclude with `mob_laws.2.1 _ _ _ I_mem`. Rewrite using `[hm, Matrix.SpecialLinearGroup.coe_mul, ← Betti.polySlash_polySlash, ← inc_eq hF hγ hδI, map_sub]`.

Normalize the expressions using the abelian group laws.
-/
theorem inc_mul {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) ℂ} (hF : F ∈ Pot ℂ w Γ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (δ : SL(2, ℤ)) :
    slP ((γ * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL (γ * δ)) Complex.I)) - F Complex.I =
      slP (δ : Matrix (Fin 2) (Fin 2) ℤ)
          (slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) Complex.I)) - F Complex.I) +
        (slP (δ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL δ) Complex.I)) - F Complex.I) := by
  have hδI := mob_laws.1 (ofSL δ) _ I_mem
  have hm : mob (ofSL (γ * δ)) Complex.I = mob (ofSL γ) (mob (ofSL δ) Complex.I) := by
    rw [map_mul]
    exact mob_laws.2.1 _ _ _ I_mem
  rw [hm, Matrix.SpecialLinearGroup.coe_mul, ← Betti.polySlash_polySlash, ← inc_eq hF hγ hδI, map_sub]
  abel

end GlobalTheory.KZ.CocPot

namespace GlobalTheory.KZ

open CocPot in

/- English proof (translation)
Introduce `w N l _ _`. Take `⟨d1, d2, d3, d4⟩` from `GlobalTheory.T.dehomogeniseBinaryPoly_homogeneous_equiv_slash w`. Use `⟨fun F hF => ⟨⟨fun γ => ?_, fun γ δ => ?_⟩, fun γ τ hτ => ?_, fun hB => ?_⟩, fun F G => ?_, fun c F => ?_⟩` and prove the remaining obligations. Conclude with `d2 _ (hom_inc hF _ _)`. Establish `hγ : (γ : SL(2, ℤ)) ∈ Gam N l` using `γ.2`.

Establish `key` using `inc_mul hF hγ (δ : SL(2, ℤ))`. Establish `e1` using `d1 ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) _ (hom_inc hF (γ : SL(2, ℤ)) Complex.I)`. Use `show deh (slP (((γ * δ : GlobalTheory.HeckeFamilyMatrices.Lev N l) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL ((γ * δ : GlobalTheory.HeckeFamilyMatrices.Lev N l) : SL(2, ℤ))) Complex.I)) - F Complex.I) = _`. Rewrite using `[Subgroup.coe_mul, key, map_add, e1]`. Both sides reduce to the same expression.

Use `show _ = deh _`. Rewrite using `[inc_eq hF (show (γ : SL(2, ℤ)) ∈ Gam N l from γ.2) hτ]`. Take `⟨⟨q, hq⟩, hqe⟩` from `hB`. Take `⟨p, hp, rfl⟩` from `d3 q hq`. Use `⟨fun z => F z - p, p, fun γ hγ z hz => ?_, fun z _ => by ring⟩` and prove the remaining obligations.

Establish `e` using `congrFun hqe ⟨γ, hγ⟩`. Simplify using `only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at e`. Express the relevant statement in the definitionally equal form `_ = deh _ at e`. Rewrite `e` using `[← d1 _ _ hp, ← map_sub]`. Establish `e2` using `d4 _ _ ((Betti.polySlash_isHomogeneous _ hp).sub hp) (hom_inc hF _ _) e`.

Establish `e3` using `inc_eq hF hγ hz`. Simplify using `only [map_sub]`. Take the linear combination `e3 - e2`. Use function extensionality and compare the values at `γ`. Simplify using `only [cocP, Pi.add_apply, map_add, map_sub]`.

Normalize the expressions using the abelian group laws. Use function extensionality and compare the values at `γ`. Simplify using `only [cocP, Pi.smul_apply, map_smul, map_sub, smul_sub]`.
-/
theorem cocP_laws : ∀ (w N l : ℕ), 0 < N → 0 < l → (∀ F ∈ Pot ℂ w (Gam N l), cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.Z1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w ∧ (∀ γ : GlobalTheory.HeckeFamilyMatrices.Lev N l, ∀ τ ∈ Hs, deh (slP ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F γ) ∧ (cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F ∈ GlobalTheory.HeckeFamilyMatrices.B1 (GlobalTheory.HeckeFamilyMatrices.Lev N l) w → F ∈ Triv ℂ w (Gam N l))) ∧ (∀ F G, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (F + G) = cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F + cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) G) ∧ (∀ (c : ℂ) F, cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) (c • F) = c • cocP (GlobalTheory.HeckeFamilyMatrices.Lev N l) F) := by
  intro w N l _ _
  obtain ⟨d1, d2, d3, d4⟩ := GlobalTheory.T.dehomogeniseBinaryPoly_homogeneous_equiv_slash w
  refine ⟨fun F hF => ⟨⟨fun γ => ?_, fun γ δ => ?_⟩, fun γ τ hτ => ?_, fun hB => ?_⟩, fun F G => ?_, fun c F => ?_⟩
  · exact d2 _ (hom_inc hF _ _)
  · have hγ : (γ : SL(2, ℤ)) ∈ Gam N l := γ.2
    have key := inc_mul hF hγ (δ : SL(2, ℤ))
    have e1 := d1 ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) _ (hom_inc hF (γ : SL(2, ℤ)) Complex.I)
    show deh (slP (((γ * δ : GlobalTheory.HeckeFamilyMatrices.Lev N l) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        (F (mob (ofSL ((γ * δ : GlobalTheory.HeckeFamilyMatrices.Lev N l) : SL(2, ℤ))) Complex.I)) - F Complex.I) = _
    rw [Subgroup.coe_mul, key, map_add, e1]
    rfl
  · show _ = deh _
    rw [inc_eq hF (show (γ : SL(2, ℤ)) ∈ Gam N l from γ.2) hτ]
  · obtain ⟨⟨q, hq⟩, hqe⟩ := hB
    obtain ⟨p, hp, rfl⟩ := d3 q hq
    refine ⟨fun z => F z - p, p, fun γ hγ z hz => ?_, fun z _ => by ring⟩
    have e := congrFun hqe ⟨γ, hγ⟩
    simp only [LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.id_apply] at e
    change _ = deh _ at e
    rw [← d1 _ _ hp, ← map_sub] at e
    have e2 := d4 _ _ ((Betti.polySlash_isHomogeneous _ hp).sub hp) (hom_inc hF _ _) e
    have e3 := inc_eq hF hγ hz
    simp only [map_sub]
    linear_combination e3 - e2
  · funext γ
    simp only [cocP, Pi.add_apply, map_add, map_sub]
    abel
  · funext γ
    simp only [cocP, Pi.smul_apply, map_smul, map_sub, smul_sub]

end GlobalTheory.KZ
