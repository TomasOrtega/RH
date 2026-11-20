import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSystemValueEqRootMulThetaConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevelStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSumInt

/- English proof (translation)
Use `haveI := RatModel.isIntegrallyClosed_O hn z`. Establish `hint : IsIntegral (M.O z) u` using `⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_O_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (z : M.Z) {u : Ω} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) :
    u ∈ M.O z := by
  haveI := RatModel.isIntegrallyClosed_O hn z
  have hint : IsIntegral (M.O z) u :=
    ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} in

/- English proof (translation)
Establish `h : (X₁.S.supI X₁.M z₁).Nonempty`. Take `⟨x, hx⟩` from `X₁.div z₁`. Conclude with `⟨x, hx⟩`. Rewrite using `[GSum.base, dif_pos h]`. Conclude with `h.some_mem`.
-/
theorem base_mem (X₁ : Setup F W i) (z₁ : X₁.M.Z) : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
  have h : (X₁.S.supI X₁.M z₁).Nonempty := by
    obtain ⟨x, hx⟩ := X₁.div z₁
    exact ⟨x, hx⟩
  rw [GSum.base, dif_pos h]
  exact h.some_mem

/- English proof (translation)
Introduce `g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D z₁ x j z' hz'`. Take `⟨y, u, k, hk, hu, he⟩` from `GlobalTheory.T.theta_system_value_eq_root_mul_theta_constant _ _ D.X.S D.X.ρ x j`. Establish `hd` using `GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D z₁ _ (base_mem X₁ z₁) z' hz'`. Establish `hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z` using `fun z => by haveI := D.X.normal`. Conclude with `⟨D.X.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩`.

Rewrite using `[he, mul_div_assoc]`. Conclude with `mul_mem (mem_O_of_pow_eq_one D.X.M hN z' hk hu) (hd.2 y)`.
-/
theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (x : D.X.S.Gam) (j : D.X.S.J) (z' : D.X.M.Z), D.q z' = z₁ → D.X.S.ev x j / D.X.S.th (D.lab (GSum.base X₁ z₁)) ∈ D.X.M.O z' := by
  intro g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D z₁ x j z' hz'
  obtain ⟨y, u, k, hk, hu, he⟩ := GlobalTheory.T.theta_system_value_eq_root_mul_theta_constant _ _ D.X.S D.X.ρ x j
  have hd := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D z₁ _ (base_mem X₁ z₁) z' hz'
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := fun z => by
    haveI := D.X.normal
    exact ⟨D.X.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩
  rw [he, mul_div_assoc]
  exact mul_mem (mem_O_of_pow_eq_one D.X.M hN z' hk hu) (hd.2 y)

end GlobalTheory.Poinc.GSumInt
