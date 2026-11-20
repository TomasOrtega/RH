import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullEndo
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.EndoHom

/- English proof (translation)
Use `isMonHom_of_mul f fun T x y => ?_` and prove the remaining obligations. Take `⟨z, -, hu⟩` from `huniq T (fun a => ((x * y) ≫ f) ≫ pr a)`. Use `(hu ((x * y) ≫ f) fun a => rfl).trans (hu ((x ≫ f) * (y ≫ f)) fun a => ?_).symm` and prove the remaining obligations. Establish `hpre : ∀ {T : Over S} (w : T ⟶ A) (a : Fin 8), w ≫ f ≫ pr a = ((List.finRange 8).map fun b => (w ≫ pr b) ^ e a b).prod` using `fun {T} w a => by`. Set `φ : (A ⟶ C) →* (T ⟶ C)` to `MonoidHom.mk' (w ≫ ·) fun g₁ g₂ => MonObj.comp_mul w g₁ g₂`.

Establish `h` using `map_list_prod φ ((List.finRange 8).map fun b => pr b ^ e a b)`. Rewrite `h` using `[List.map_map]`. Rewrite using `[hf a]`. Use `h.trans (congrArg List.prod (List.map_congr_left fun b _ => ?_))` and prove the remaining obligations. Conclude with `map_zpow φ (pr b) (e a b)`.

Use `hpr` as an intermediate fact. Rewrite using `[MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hpre, hpre, hpre]`. Simplify using `only [MonObj.mul_comp, mul_zpow]`. Conclude with `(List.prod_map_mul).symm`.
-/
theorem isMonHom_of_prod_pow {S : Scheme.{0}} {A C : Over S} [GrpObj A] [GrpObj C] [IsCommMonObj C]
    (pr : Fin 8 → (A ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniq : ∀ (T' : Over S) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ A, ∀ a, x ≫ pr a = y a)
    (f : A ⟶ A) (e : Fin 8 → Fin 8 → ℤ)
    (hf : ∀ a, f ≫ pr a = ((List.finRange 8).map fun b => pr b ^ e a b).prod) : IsMonHom f := by
  refine isMonHom_of_mul f fun T x y => ?_
  obtain ⟨z, -, hu⟩ := huniq T (fun a => ((x * y) ≫ f) ≫ pr a)
  refine (hu ((x * y) ≫ f) fun a => rfl).trans (hu ((x ≫ f) * (y ≫ f)) fun a => ?_).symm
  have hpre : ∀ {T : Over S} (w : T ⟶ A) (a : Fin 8),
      w ≫ f ≫ pr a = ((List.finRange 8).map fun b => (w ≫ pr b) ^ e a b).prod := fun {T} w a => by
    let φ : (A ⟶ C) →* (T ⟶ C) := MonoidHom.mk' (w ≫ ·) fun g₁ g₂ => MonObj.comp_mul w g₁ g₂
    have h := map_list_prod φ ((List.finRange 8).map fun b => pr b ^ e a b)
    rw [List.map_map] at h
    rw [hf a]
    refine h.trans (congrArg List.prod (List.map_congr_left fun b _ => ?_))
    exact map_zpow φ (pr b) (e a b)
  have := hpr
  rw [MonObj.mul_comp, Category.assoc, Category.assoc, Category.assoc, hpre, hpre, hpre]
  simp only [MonObj.mul_comp, mul_zpow]
  exact (List.prod_map_mul).symm

/- English proof (translation)
Take `⟨f', hf', he⟩` from `GlobalTheory.Ex.Arch.exists_pull_endo hg f hf`. Establish `: f' = f₀` using `Over.OverMorphism.ext (hg.1.hom_ext (he.trans h.symm) ((Over.w f').trans (Over.w f₀).symm))`. Conclude with `this ▸ hf'`.
-/
theorem isMonHom_of_isGrpPullback_endo {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {b : S' ⟶ S} {φ : G'.left ⟶ G.left} (hg : IsGrpPullback G' G b φ) (f : G ⟶ G) (hf : IsMonHom f)
    (f₀ : G' ⟶ G') (h : f₀.left ≫ φ = φ ≫ f.left) : IsMonHom f₀ := by
  obtain ⟨f', hf', he⟩ := GlobalTheory.Ex.Arch.exists_pull_endo hg f hf
  have : f' = f₀ := Over.OverMorphism.ext (hg.1.hom_ext (he.trans h.symm) ((Over.w f').trans (Over.w f₀).symm))
  exact this ▸ hf'

end GlobalTheory.Poinc.EndoHom

open GlobalTheory.Poinc.EndoHom in

/- English proof (translation)
Introduce `g n F W Z i X ε hD c₀ hc R' fg frac hth hev ρ' ε' hS E`. Take `⟨c, -, pr, hpr, huniq, -, hε⟩` from `hD`. Establish `hE : IsMonHom (ε E)` using `isMonHom_of_prod_pow pr hpr huniq (ε E) E (hε E)`. Take `⟨P₀, a, a', ε₀, h₁, h₂, -, -, hε₀, -⟩` from `hS`. Establish `h₀ : IsMonHom (ε₀ E)` using `isMonHom_of_isGrpPullback_endo h₁ (ε E) hE (ε₀ E) (hε₀ E).1`.

Establish `: IsSchemeTheoreticallyDominant (spMap (X.S.rechart c₀ hc R' fg frac hth hev).R.val.toRingHom)` using `GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ Subtype.val_injective`. Use `ρ'.P.isAb.smooth` as an intermediate fact. Use `ρ'.P.isAb.proper` as an intermediate fact. Conclude with `GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback h₂ h₂ (ε₀ E) (ε' E) (hε₀ E).2`.
-/
theorem GlobalTheory.Poinc.isMonHom_of_same_rechart : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i) (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) → ∀ E, IsMonHom (ε' E) := by
  intro g n F W Z i X ε hD c₀ hc R' fg frac hth hev ρ' ε' hS E
  obtain ⟨c, -, pr, hpr, huniq, -, hε⟩ := hD
  have hE : IsMonHom (ε E) := isMonHom_of_prod_pow pr hpr huniq (ε E) E (hε E)
  obtain ⟨P₀, a, a', ε₀, h₁, h₂, -, -, hε₀, -⟩ := hS
  have h₀ : IsMonHom (ε₀ E) := isMonHom_of_isGrpPullback_endo h₁ (ε E) hE (ε₀ E) (hε₀ E).1
  have : IsSchemeTheoreticallyDominant (spMap (X.S.rechart c₀ hc R' fg frac hth hev).R.val.toRingHom) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ Subtype.val_injective
  have := ρ'.P.isAb.smooth
  have := ρ'.P.isAb.proper
  exact GlobalTheory.ExtUnique.isMonHom_of_isGrpPullback h₂ h₂ (ε₀ E) (ε' E) (hε₀ E).2
