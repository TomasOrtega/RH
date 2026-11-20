import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.WeilAddLeft

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]`.
-/
theorem pow_comp_hom {S : Scheme.{0}} {G H Z : Over S} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]
    (x : Z ⟶ G) (n : ℕ) : (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.mul_comp, ih]

/- English proof (translation)
The claim follows from `map_mul (Units.map _) u v`.
-/
theorem unitOn_mul {R : Type} [CommRing R] (u v : Rˣ) : unitOn (u * v) = unitOn u * unitOn v :=
  map_mul (Units.map _) u v

/- English proof (translation)
Introduce `E _ _ _ H K _ _ σ₁ A B f₁ f₂ g hf₁ hf₂ hg r₁ r₂ h₁ h₂ n x y c hn hx hy`. Establish `hL : Out.Laws` using `GlobalTheory.abelianSchemeLaws_all.1`. Use `haveI : IsCommMonObj B.pol.A := B.pol.isAb.comm`. Use `haveI : IsCommMonObj A.pol.A := A.pol.isAb.comm`. Establish `tor : ∀ (f : A.t.G ⟶ B.t.G), IsMonHom f → ((x ≫ f) ^ n = 1)` using `fun f hf => by`.

Rewrite using `[← pow_comp_hom, hx, one_comp]`. Establish `tory : (y ≫ g) ^ n = 1` using `by rw [← pow_comp_hom, hy, one_comp]`. Take `⟨c₁, hc₁⟩` from `TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₁ hf₁) tory`. Take `⟨c₂, hc₂⟩` from `TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₂ hf₂) tory`. Establish `a₁` using `(h₁ n x y c₁ hn hx hy).1 hc₁`.

Establish `a₂` using `(h₂ n x y c₂ hn hx hy).1 hc₂`. Establish `hB` using `weilIs_mul_left hL.globalFns _ B.pol n _ _ _ _ _ _ hc₁ hc₂`. Establish `hA` using `weilIs_mul_left hL.globalFns _ A.pol n _ _ _ _ _ _ a₁ a₂`. Rewrite `hB`, `hA` using `[← MonObj.comp_mul]`. Rewrite `hA` using `[← A.t.act.add]`.

Rewrite `hB`, `hA` using `[← unitOn_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `rfl` from `weilIs_unique_fieldPoint _ _ _ B.t.PP.isLB _ _ _ _ _ _ _ h hB`. Conclude with `hA`.

Introduce `h`. Take `rfl` from `weilIs_unique_fieldPoint _ _ _ A.t.PP.isLB _ _ _ _ _ _ _ h hA`. Conclude with `hB`.
-/
theorem weilEq_mul_left : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (K : Type) [Field K]
    [NumberField K] (σ₁ : K →+* ℂ) (A B : PAT H (Sp (𝓞 K))) (f₁ f₂ g : A.t.G ⟶ B.t.G), IsMonHom f₁ → IsMonHom f₂ →
    IsMonHom g → ∀ r₁ r₂ : 𝓞 E,
    WeilEq B.t.PP.L f₁ g A.t.PP.L (A.t.act.act r₁) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L f₂ g A.t.PP.L (A.t.act.act r₂) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) →
    WeilEq B.t.PP.L (f₁ * f₂) g A.t.PP.L (A.t.act.act (r₁ + r₂)) (𝟙 _) (spMap (σ₁.comp (algebraMap (𝓞 K) K))) := by
  intro E _ _ _ H K _ _ σ₁ A B f₁ f₂ g hf₁ hf₂ hg r₁ r₂ h₁ h₂ n x y c hn hx hy
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  haveI : IsCommMonObj B.pol.A := B.pol.isAb.comm
  haveI : IsCommMonObj A.pol.A := A.pol.isAb.comm
  have tor : ∀ (f : A.t.G ⟶ B.t.G), IsMonHom f → ((x ≫ f) ^ n = 1) := fun f hf => by
    rw [← pow_comp_hom, hx, one_comp]
  have tory : (y ≫ g) ^ n = 1 := by rw [← pow_comp_hom, hy, one_comp]
  obtain ⟨c₁, hc₁⟩ := TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₁ hf₁) tory
  obtain ⟨c₂, hc₂⟩ := TorsionGenerators.exists_weilIs hL B.pol (σ₁.comp (algebraMap (𝓞 K) K)) (tor f₂ hf₂) tory
  have a₁ := (h₁ n x y c₁ hn hx hy).1 hc₁
  have a₂ := (h₂ n x y c₂ hn hx hy).1 hc₂
  have hB := weilIs_mul_left hL.globalFns _ B.pol n _ _ _ _ _ _ hc₁ hc₂
  have hA := weilIs_mul_left hL.globalFns _ A.pol n _ _ _ _ _ _ a₁ a₂
  rw [← MonObj.comp_mul] at hB hA
  rw [← A.t.act.add] at hA
  rw [← unitOn_mul] at hB hA
  constructor
  · intro h
    obtain rfl := weilIs_unique_fieldPoint _ _ _ B.t.PP.isLB _ _ _ _ _ _ _ h hB
    exact hA
  · intro h
    obtain rfl := weilIs_unique_fieldPoint _ _ _ A.t.PP.isLB _ _ _ _ _ _ _ h hA
    exact hB

end GlobalTheory.CM.WeilAddLeft
end
