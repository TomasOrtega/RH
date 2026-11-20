import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsMulPullSec
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.JKAppTopInjective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRatio

/- English proof (translation)
Use `⟨(Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom), fun c => gs_eq p z ⊤ trivial _, fun c => ?_⟩` and prove the remaining obligations. Conclude with `gs_eq (𝟙 _) z ⊤ trivial _`.
-/
theorem exists_cstHom {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) :
    ∃ φ : F →+* Z.presheaf.stalk z, (∀ c, cst p z c = φ c) ∧ ∀ c, gs (𝟙 _) z ⊤ (scal p c) = φ c := by
  refine ⟨(Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp ((p.app ⊤).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom), fun c => gs_eq p z ⊤ trivial _, fun c => ?_⟩
  exact gs_eq (𝟙 _) z ⊤ trivial _

/- English proof (translation)
Take `⟨φ, h₁, h₂⟩` from `exists_cstHom p z`. Rewrite using `[h₁, h₂]`.
-/
theorem cst_eq_scal {F : Type} [CommRing F] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of F)) (z : Z) (c : F) :
    cst p z c = gs (𝟙 _) z ⊤ (scal p c) := by
  obtain ⟨φ, h₁, h₂⟩ := exists_cstHom p z
  rw [h₁, h₂]

end GlobalTheory.PsiRatio

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ _ D ga a f th hS hR hN χ q p hq hp`. Set `B : Over (Spec (CommRingCat.of R))` to `𝟙_ _ ⊗ D.P.A`. Set `T : Over (Spec (CommRingCat.of R))` to `TK R ⊗ B`. Set `pt : Spec (CommRingCat.of (FractionRing R))` to `IsLocalRing.closedPoint (FractionRing R)`. Take `⟨z₀, hz₀, hth⟩` from `hN (jK R pt)`.

Take `⟨z, -, hz⟩` from `Scheme.Pullback.exists_preimage_pullback (f := jK R) (g := B.hom) pt z₀ hz₀.symm`. Set `z' : T.left` to `z`. Take `⟨J, hJ⟩` from `exists_good_pt D.P.isLB z'`. Set `x : T ⟶ D.P.A` to `snd (TK R) B ≫ snd _ _`. Establish `ex : lift (toUnit T) x = snd (TK R) B` using `by ext1`.

Conclude with `toUnit_unique _ _`. Conclude with `lift_snd _ _`. Establish `ey : x * (cT D T χ)⁻¹ * cT D T χ = x` using `inv_mul_cancel_right _ _`. Establish `hu : IsUnit (sval th (snd (TK R) B).left z' J)`. Use `(MulPullSec.mem_nonzeroLocus_iff th (snd (TK R) B).left z' hJ).1 ?_` and prove the remaining obligations.

Establish `: (snd (TK R) B).left z' = z₀` using `hz`. Rewrite using `[this]`. Conclude with `hth`. Establish `e₁` using `hR χ T (toUnit _) (fst (TK R) B) (x * (cT D T χ)⁻¹) z' J hJ`. Establish `e₂` using `(hS χ).2 T (fst (TK R) B) z' J hJ`.

Establish `e₃` using `hq _ (snd (TK R) B).left z' J hJ`. Establish `e₄` using `hp T (x * (cT D T χ)⁻¹) z' J hJ`. Rewrite `e₁`, `e₄` using `[ey, ex]`. Establish `e' : T.hom = (fst (TK R) B).left ≫ jK R` using `(Over.w (fst (TK R) B)).symm`. Establish `e'' : (snd (TK R) B).left ≫ B.hom = (fst (TK R) B).left ≫ jK R` using `(Over.w (snd (TK R) B)).trans e'`.

Take `⟨φ, -, hφ⟩` from `PsiRatio.exists_cstHom (F := FractionRing R) (fst (TK R) B).left z'`. Establish `hc : ∀ c : R, cst ((fst (TK R) B).left ≫ jK R) z' c = φ (algebraMap R (FractionRing R) c)` using `fun c => (PsiRatio.cst_eq_scal _ _ _).trans ((congrArg (gs (𝟙 _) z' ⊤) (PsiInt.scal_jK _ c)).trans (hφ _))`. Establish `c₃` using `(congrArg (fun s => cst s z' q) e'').trans (hc q)`. Establish `c₄` using `(congrArg (fun s => cst s z' p) e').trans (hc p)`. Establish `alg : ∀ (A : Type) [CommRing A] (s s₀ t cq cp ca cq' cp' ca' : A) (u g r : Aˣ), IsUnit t → s = (u * r).val * s₀ → u.val = ca * g.val → s₀ = cq * t → s = cp * ((g * r).val * t) → cq = cq' → cp = cp' → ca = ca' → cq' * ca' = cp'`.

Introduce `A _ s s₀ t cq cp ca cq' cp' ca' u g r ht h₁ h₂ h₃ h₄ h₅ h₆ h₇`. Substitute `h₅ h₆ h₇` using the available equality. Use `(((g * r).isUnit.mul ht).mul_left_inj).1 ?_` and prove the remaining obligations. Rewrite using `[← h₄, h₁, h₃, Units.val_mul, Units.val_mul, h₂]`. Expand and normalize the polynomial expressions, which then agree.

Apply `φ.injective` to reduce the goal to its premises. Rewrite using `[map_mul]`. Conclude with `alg _ _ _ _ _ _ _ _ _ _ _ _ _ hu e₁ e₂ e₃ e₄ c₃ c₄ (hφ _)`.
-/
theorem psiScal_eq_ratio : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), PsiScal D ga a → PsiRel D (𝟙_ _) f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ (χ : D.X) (q p : R), Mult D th (f 0) q → Coef D χ (ga χ) th (f χ) p → algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) p := by
  intro R _ _ D ga a f th hS hR hN χ q p hq hp
  let B : Over (Spec (CommRingCat.of R)) := 𝟙_ _ ⊗ D.P.A
  let T : Over (Spec (CommRingCat.of R)) := TK R ⊗ B
  let pt : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  obtain ⟨z₀, hz₀, hth⟩ := hN (jK R pt)
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback (f := jK R) (g := B.hom) pt z₀ hz₀.symm
  let z' : T.left := z
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z'
  let x : T ⟶ D.P.A := snd (TK R) B ≫ snd _ _
  have ex : lift (toUnit T) x = snd (TK R) B := by
    ext1
    · exact toUnit_unique _ _
    · exact lift_snd _ _
  have ey : x * (cT D T χ)⁻¹ * cT D T χ = x := inv_mul_cancel_right _ _
  have hu : IsUnit (sval th (snd (TK R) B).left z' J) := by
    refine (MulPullSec.mem_nonzeroLocus_iff th (snd (TK R) B).left z' hJ).1 ?_
    have : (snd (TK R) B).left z' = z₀ := hz
    rw [this]
    exact hth
  have e₁ := hR χ T (toUnit _) (fst (TK R) B) (x * (cT D T χ)⁻¹) z' J hJ
  have e₂ := (hS χ).2 T (fst (TK R) B) z' J hJ
  have e₃ := hq _ (snd (TK R) B).left z' J hJ
  have e₄ := hp T (x * (cT D T χ)⁻¹) z' J hJ
  rw [ey, ex] at e₁ e₄
  have e' : T.hom = (fst (TK R) B).left ≫ jK R := (Over.w (fst (TK R) B)).symm
  have e'' : (snd (TK R) B).left ≫ B.hom = (fst (TK R) B).left ≫ jK R := (Over.w (snd (TK R) B)).trans e'
  obtain ⟨φ, -, hφ⟩ := PsiRatio.exists_cstHom (F := FractionRing R) (fst (TK R) B).left z'
  have hc : ∀ c : R, cst ((fst (TK R) B).left ≫ jK R) z' c = φ (algebraMap R (FractionRing R) c) := fun c =>
    (PsiRatio.cst_eq_scal _ _ _).trans ((congrArg (gs (𝟙 _) z' ⊤) (PsiInt.scal_jK _ c)).trans (hφ _))
  have c₃ := (congrArg (fun s => cst s z' q) e'').trans (hc q)
  have c₄ := (congrArg (fun s => cst s z' p) e').trans (hc p)
  have alg : ∀ (A : Type) [CommRing A] (s s₀ t cq cp ca cq' cp' ca' : A) (u g r : Aˣ), IsUnit t →
      s = (u * r).val * s₀ → u.val = ca * g.val → s₀ = cq * t → s = cp * ((g * r).val * t) →
      cq = cq' → cp = cp' → ca = ca' → cq' * ca' = cp' := by
    intro A _ s s₀ t cq cp ca cq' cp' ca' u g r ht h₁ h₂ h₃ h₄ h₅ h₆ h₇
    subst h₅ h₆ h₇
    refine (((g * r).isUnit.mul ht).mul_left_inj).1 ?_
    rw [← h₄, h₁, h₃, Units.val_mul, Units.val_mul, h₂]
    ring
  apply φ.injective
  rw [map_mul]
  exact alg _ _ _ _ _ _ _ _ _ _ _ _ _ hu e₁ e₂ e₃ e₄ c₃ c₄ (hφ _)

end GlobalTheory
