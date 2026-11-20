import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ReframeSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralDegenerationValues

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.ActValues
open GlobalTheory.TorusExt GlobalTheory.ValuesExist

section Val
variable {F : Type} [Field F] {X Y Y' : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']
  {J : (Sp F ⟶ X) → L.ι}

/- English proof (translation)
Establish `e` using `val_corr hJ H r`. Rewrite `e` using `[val_mul hJ, val_pull hJ]`. Rewrite using `[← coe_val t r hJ, ← coe_val u _ hJ, ← coe_val t' r hJ, ← e, map_mul, Units.val_mul]`.
-/
theorem vF_corr {z : Sp F} (hJ : Good L z J) {φ : K → (Y' ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y' ⟶ X)} {ε'' : K'' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {u : LB.Gen (LB.LinComb L φ' ε')}
    {t' : LB.Gen (LB.LinComb L φ'' ε'')} {h : Y' ⟶ Y}
    (H : LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ t (LB.pullGen L _ _ u h)) t') (r : Sp F ⟶ Y') :
    vF t r J * vF u (r ≫ h) J = vF t' r J := by
  have e := val_corr hJ H r
  rw [val_mul hJ, val_pull hJ] at e
  rw [← coe_val t r hJ, ← coe_val u _ hJ, ← coe_val t' r hJ, ← e, map_mul, Units.val_mul]
end Val

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N)

/- English proof (translation)
Introduce `ψ` and use `ν.good ψ trivial`.
-/
theorem good (z : Sp F) : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

/- English proof (translation)
Set `z : Sp F` to `IsLocalRing.closedPoint F`. Establish `hJ` using `good ν z`. Rewrite using `[ν.ψ_eq, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← Units.val_mul, ← map_mul]`. Conclude with `congrArg (fun q => (((stalkUnits z).symm q : Fˣ) : F)) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm`.
-/
theorem psi_eq (y : N.X) :
    (N.ψ y : F) = vF (LB.mulGen D.P.L _ _ _ _ (D.psi (ν.eX y)) D.rigK) (jFK (R := R) F) ν.J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  rw [ν.ψ_eq, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← coe_val _ _ hJ, ← Units.val_mul, ← map_mul]
  exact congrArg (fun q => (((stalkUnits z).symm q : Fˣ) : F))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm

/- English proof (translation)
Set `z : Sp F` to `IsLocalRing.closedPoint F`. Establish `hJ` using `good ν z`. Set `e` to `(stalkUnits z).symm`. Set `ρ : ((Sp F).presheaf.stalk z)ˣ` to `val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J`. Set `p : D.X → ((Sp F).presheaf.stalk z)ˣ` to `fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z ν.J`.

Establish `hτ : ∀ a b, val (Z` using `Sp F) (D.tau a b) (jFK (R := R) F) z ν.J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))`. Establish `hψ : ∀ y, N.ψ y = e (p (ν.eX y) * ρ)` using `fun y => Units.ext ((psi_eq ν y).trans ((coe_val _ _ hJ).symm.trans (congrArg (fun q => ((e q : Fˣ) : F)) (val_mul hJ _ _ _))))`. Use `Eq.trans ?_ (coe_val _ _ hJ)` and prove the remaining obligations. Rewrite using `[hτ, NumD.τ, hψ, hψ, hψ, ← map_div, ← map_div, map_add]`. Use `congrArg (fun q => ((e q : Fˣ) : F)) (Additive.ofMul.injective ?_)` and prove the remaining obligations.

Simplify using `only [ofMul_mul, ofMul_inv, ofMul_div]`. Normalize the expressions using the abelian group laws.
-/
theorem tau_eq (a b : N.X) : (N.τ a b : F) = vF (D.tau (ν.eX a) (ν.eX b)) (jFK (R := R) F) ν.J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ := good ν z
  let e := (stalkUnits z).symm
  let ρ : ((Sp F).presheaf.stalk z)ˣ := val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J
  let p : D.X → ((Sp F).presheaf.stalk z)ˣ := fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z ν.J
  have hτ : ∀ a b, val (Z := Sp F) (D.tau a b) (jFK (R := R) F) z ν.J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have hψ : ∀ y, N.ψ y = e (p (ν.eX y) * ρ) := fun y => Units.ext ((psi_eq ν y).trans
    ((coe_val _ _ hJ).symm.trans (congrArg (fun q => ((e q : Fˣ) : F)) (val_mul hJ _ _ _))))
  refine Eq.trans ?_ (coe_val _ _ hJ)
  rw [hτ, NumD.τ, hψ, hψ, hψ, ← map_div, ← map_div, map_add]
  refine congrArg (fun q => ((e q : Fˣ) : F)) (Additive.ofMul.injective ?_)
  simp only [ofMul_mul, ofMul_inv, ofMul_div]
  abel

/- English proof (translation)
Introduce `hL R _ _ D _ _ F _ _ _ N ν O _ _ _ oa`. Establish `hJ` using `good ν (IsLocalRing.closedPoint F)`. Use `⟨fun a => ?_, fun a => ?_, fun w₀ hw => ?_⟩` and prove the remaining obligations. Use `oa.onB.hom a` as an intermediate fact. Use `oa.onB.hom (star a)` as an intermediate fact.

Take `⟨r, hr, r₀⟩` from `exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)`. Use `⟨r, ⟨hr, r₀⟩, fun y y' => ?_⟩` and prove the remaining obligations. Establish `h` using `vF_corr hJ (oa.tau_bal a r hr r₀ (ν.eX y) (ν.eX y')) (jFK (R := R) F)`. Establish `h2 : jFK (R` using `R) F ≫ D.pt2 (ν.eX y) (ν.eX y') = (lift (ν.eA (N.c y)) (ν.eA (N.c y'))).left := by`. Rewrite using `[ν.c_eq, ν.c_eq]`.

Set `κ : TF (R` to `R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl`. Use `congrArg CommaMorphism.left (show κ ≫ lift _ _ = _ from ?_)` and prove the remaining obligations. Simplify using `only [comp_lift, comp_toUnit_assoc]`. Rewrite using `[tau_eq ν, tau_eq ν, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← h2]`. Conclude with `h`.

Use `oa.onB.hom a` as an intermediate fact. Use `oa.onB.hom (star a)` as an intermediate fact. Establish `hr` using `oa.onB.rosati (star a)`. Rewrite `hr` using `[star_star]`. Take `⟨r, hr, r₀⟩` from `exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ hr`.

Use `⟨r, ⟨hr, r₀⟩, fun g g' c c' hc hc' hg => ⟨by rw [hc.1, hc'.1, hg.1], fun χ => ?_⟩⟩` and prove the remaining obligations. Establish `h` using `vF_corr hJ (hg.2 r hr r₀ (ν.eX χ)) (𝟙 (Sp F))`. Rewrite using `[hc'.2, hc.2, AddEquiv.apply_symm_apply, ν.c_eq, hc.1]`. Conclude with `h.symm.trans (congrArg (fun q => _ * vF r q ν.J) (Category.id_comp _))`. Take `⟨t, ht, t₀, hy⟩` from `hw`.

Use `⟨t, ⟨ht, t₀⟩, fun y => ?_⟩` and prove the remaining obligations. Establish `h` using `vF_corr hJ (hy (ν.eX y)) (jFK (R := R) F)`. Establish `h2 : jFK (R` using `R) F ≫ D.xK (ν.eX y) = (ν.eA (N.c y)).left := by`. Rewrite using `[ν.c_eq]`. Conclude with `(Category.assoc _ _ _).symm`.

Rewrite using `[tau_eq ν, psi_eq ν, AddEquiv.apply_symm_apply, ← h2]`. Conclude with `h`.
-/
theorem brAct : Laws → BrActSt := by
  intro hL R _ _ D _ _ F _ _ _ N ν O _ _ _ oa
  have hJ := good ν (IsLocalRing.closedPoint F)
  refine ⟨fun a => ?_, fun a => ?_, fun w₀ hw => ?_⟩
  · have := oa.onB.hom a
    have := oa.onB.hom (star a)
    obtain ⟨r, hr, r₀⟩ := exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ (oa.onB.rosati a)
    refine ⟨r, ⟨hr, r₀⟩, fun y y' => ?_⟩
    have h := vF_corr hJ (oa.tau_bal a r hr r₀ (ν.eX y) (ν.eX y')) (jFK (R := R) F)
    have h2 : jFK (R := R) F ≫ D.pt2 (ν.eX y) (ν.eX y') = (lift (ν.eA (N.c y)) (ν.eA (N.c y'))).left := by
      rw [ν.c_eq, ν.c_eq]
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
      refine congrArg CommaMorphism.left (show κ ≫ lift _ _ = _ from ?_)
      simp only [comp_lift, comp_toUnit_assoc]
    rw [tau_eq ν, tau_eq ν, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, ← h2]
    exact h
  · have := oa.onB.hom a
    have := oa.onB.hom (star a)
    have hr := oa.onB.rosati (star a)
    rw [star_star] at hr
    obtain ⟨r, hr, r₀⟩ := exists_ros hL.globalFns D.P.isAb D.P.isLB _ _ hr
    refine ⟨r, ⟨hr, r₀⟩, fun g g' c c' hc hc' hg => ⟨by rw [hc.1, hc'.1, hg.1], fun χ => ?_⟩⟩
    have h := vF_corr hJ (hg.2 r hr r₀ (ν.eX χ)) (𝟙 (Sp F))
    rw [hc'.2, hc.2, AddEquiv.apply_symm_apply, ν.c_eq, hc.1]
    exact h.symm.trans (congrArg (fun q => _ * vF r q ν.J) (Category.id_comp _))
  · obtain ⟨t, ht, t₀, hy⟩ := hw
    refine ⟨t, ⟨ht, t₀⟩, fun y => ?_⟩
    have h := vF_corr hJ (hy (ν.eX y)) (jFK (R := R) F)
    have h2 : jFK (R := R) F ≫ D.xK (ν.eX y) = (ν.eA (N.c y)).left := by
      rw [ν.c_eq]
      exact (Category.assoc _ _ _).symm
    rw [tau_eq ν, psi_eq ν, AddEquiv.apply_symm_apply, ← h2]
    exact h

end GlobalTheory.ActValues
