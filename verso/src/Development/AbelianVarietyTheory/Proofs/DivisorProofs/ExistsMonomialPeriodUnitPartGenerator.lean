import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.UnitPart

/- English proof (translation)
Introduce `R _ _ _ Q m t gam hM χ n hn`. Take `⟨u, n', hn', hc⟩` from `hM χ`. Take `rfl : n = n'` from `funext fun i => by have := (hn' i).symm.trans (hn i); omega`. Take `⟨j, hj, h, e⟩` from `hc`. Establish `hL` using `Q.P.isLB`.

Take `⟨e₀, he₀⟩` from `exists_gen_of_local (V := R) Q.P.L hL (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1)`. Establish `le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart Q.P.L (K` using `PUnit) (fun _ => (Q.c χ).left) j := fun y hy => Set.mem_iInter.2 fun k => by cases k; exact hj hy`. Establish `hx : Q.xK χ = jK R ≫ (Q.c χ).left` using `by simp [DegPre.xK, ptK]`. Establish `hto : ∀ a, DegPre.toOpen (R` using `R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by`. Simplify using `[DegPre.toOpen]`.

Set `w : Γ(Spec (CommRingCat.of R), ⊤)ˣ` to `Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u * (res le (e₀.s j))⁻¹`. Set `v : LB.Gen (LB.LinComb Q.P.L (Y` to `Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) := ⟨fun _ => res le_top w⟩`. Establish `hv : v.IsGen` using `fun i i' => by`. Take `rfl : i = i'` from `funext fun k => k.elim`. Establish `e' : (LB.LinComb Q.P.L (Y` using `Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by dsimp only [LB.LinComb] erw [Fintype.prod_empty]`.

Both sides reduce to the same expression. Rewrite using `[e', _root_.one_mul]`. Establish `hf : FormEq (Sum.elim (fun _ : PUnit => (Q.c χ).left) (PEmpty.elim : PEmpty.{1} → _)) (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (PEmpty.elim : PEmpty.{1} → ℤ)) (fun _ : PUnit => (Q.c χ).left) (fun _ => -1)` using `fun U _ g => by`. Rewrite using `[Fintype.prod_sum_type]`. Simplify using the standard rewrite rules.

Take `⟨ψ₀, hψ₀, vψ₀⟩` from `exists_gen hL hf (LB.mulGen Q.P.L _ _ _ _ e₀ v) (mulGen_isGen _ _ _ _ _ _ _ he₀ hv)`. Use `⟨ψ₀, hψ₀, fun Z r z J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[vψ₀ _ _ z J hJ, val_mul hJ]`. Establish `m₁ : r z ∈ LB.wchart Q.P.L (K` using `PUnit) (fun _ => Q.xK χ) j := h trivial`. Establish `m₂ : (r ≫ jK R) z ∈ LB.wchart Q.P.L (K` using `PUnit) (fun _ => (Q.c χ).left) j := le trivial`.

Establish `e₁ : val (Q.psi χ) r z J = _` using `gen_trans (Q.psi_gen χ) r z (hJ.mem _ r) m₁`. Establish `e₂ : val e₀ (r ≫ jK R) z J = _` using `gen_trans he₀ (r ≫ jK R) z (hJ.mem _ _) m₂`. Establish `e₃ : trF (L` using `Q.P.L) (K := PUnit) (fun _ => Q.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ Q.xK χ)) j = trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j := by`. Establish `hq : r ≫ Q.xK χ = (r ≫ jK R) ≫ (Q.c χ).left` using `(congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm`. Simplify using `only [trF]`.

Rewrite using `[hq]`. Establish `e₄ : (gm r z (LB.wchart Q.P.L (K` using `PUnit) (fun _ => Q.xK χ) j) ((Q.psi χ).s j)).val = cst (r ≫ jK R) z (u * ∏ i, t i ^ n i) := by`. Use `(gs_unit r z _ m₁ _).symm.trans ((gs_res r z h trivial _).symm.trans ?_)` and prove the remaining obligations. Use `(congrArg (gs r z _) e.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)` and prove the remaining obligations. Rewrite using `[hto]`.

Both sides reduce to the same expression. Establish `e₅ : val v (r ≫ jK R) z J = gm (r ≫ jK R) z ⊤ w` using `gm_res _ z _ (hJ.mem PEmpty.elim _) _`. Establish `e₆ : (gm (r ≫ jK R) z ⊤ (Units.map (DegPre.toOpen (R` using `R) ⊤).toMonoidHom u)).val = cst (r ≫ jK R) z u := by`. Rewrite using `[← gs_unit _ z ⊤ trivial, Units.coe_map, cst, ← hto]`. Both sides reduce to the same expression.

Establish `e₇ : ∀ a b : R, cst (r ≫ jK R) z (a * b) = cst (r ≫ jK R) z a * cst (r ≫ jK R) z b` using `fun a b => by`. Rewrite using `[cst, map_mul, gs_mul _ z ⊤ trivial]`. Both sides reduce to the same expression. Establish `e₈ : gm (r ≫ jK R) z ⊤ (res le (e₀.s j)) = gm (r ≫ jK R) z (LB.wchart Q.P.L (K` using `PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j) := gm_res _ z le trivial _`. Establish `hg` using `Units.mul_inv (gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j))`.

Rewrite using `[e₁, e₂, e₅, Units.val_mul, Units.val_mul, e₄]`. Use `erw [e₃]`. Rewrite using `[map_mul, map_inv, e₈]`. Simplify using `only [Units.val_mul]`. Rewrite using `[e₆, e₇]`.

Take the linear combination `(-((trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j).val * cst (r ≫ jK R) z u * cst (r ≫ jK R) z (∏ i, t i ^ n i))) * hg`.
-/
theorem exists_psi_val_eq_monomial_mul : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : DegPre R) (m : ℕ)
    (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q t gam → ∀ (χ : Q.X) (n : Fin m → ℕ),
    (∀ i, gam i χ χ = 2 * n i) → ∃ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1),
      ψ₀.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι),
        Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n i) * (val ψ₀ (r ≫ jK R) z J).val := by
  intro R _ _ _ Q m t gam hM χ n hn
  obtain ⟨u, n', hn', hc⟩ := hM χ
  obtain rfl : n = n' := funext fun i => by have := (hn' i).symm.trans (hn i); omega
  obtain ⟨j, hj, h, e⟩ := hc
  have hL := Q.P.isLB
  obtain ⟨e₀, he₀⟩ := exists_gen_of_local (V := R) Q.P.L hL (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1)
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j :=
    fun y hy => Set.mem_iInter.2 fun k => by cases k; exact hj hy
  have hx : Q.xK χ = jK R ≫ (Q.c χ).left := by simp [DegPre.xK, ptK]
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  let w : Γ(Spec (CommRingCat.of R), ⊤)ˣ :=
    Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u * (res le (e₀.s j))⁻¹
  let v : LB.Gen (LB.LinComb Q.P.L (Y := Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top w⟩
  have hv : v.IsGen := fun i i' => by
    obtain rfl : i = i' := funext fun k => k.elim
    have e' : (LB.LinComb Q.P.L (Y := Spec (CommRingCat.of R)) (K := PEmpty.{1}) PEmpty.elim PEmpty.elim).g i i = 1 := by
      dsimp only [LB.LinComb]
      erw [Fintype.prod_empty]
      rfl
    rw [e', _root_.one_mul]
  have hf : FormEq (Sum.elim (fun _ : PUnit => (Q.c χ).left) (PEmpty.elim : PEmpty.{1} → _))
      (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (PEmpty.elim : PEmpty.{1} → ℤ))
      (fun _ : PUnit => (Q.c χ).left) (fun _ => -1) := fun U _ g => by
    rw [Fintype.prod_sum_type]
    simp
  obtain ⟨ψ₀, hψ₀, vψ₀⟩ := exists_gen hL hf (LB.mulGen Q.P.L _ _ _ _ e₀ v)
    (mulGen_isGen _ _ _ _ _ _ _ he₀ hv)
  refine ⟨ψ₀, hψ₀, fun Z r z J hJ => ?_⟩
  rw [vψ₀ _ _ z J hJ, val_mul hJ]
  have m₁ : r z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK χ) j := h trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j := le trivial
  have e₁ : val (Q.psi χ) r z J = _ := gen_trans (Q.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val e₀ (r ≫ jK R) z J = _ := gen_trans he₀ (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := Q.P.L) (K := PUnit) (fun _ => Q.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ Q.xK χ)) j =
      trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j := by
    have hq : r ≫ Q.xK χ = (r ≫ jK R) ≫ (Q.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart Q.P.L (K := PUnit) (fun _ => Q.xK χ) j) ((Q.psi χ).s j)).val =
      cst (r ≫ jK R) z (u * ∏ i, t i ^ n i) := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z h trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) e.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]; rfl
  have e₅ : val v (r ≫ jK R) z J = gm (r ≫ jK R) z ⊤ w := gm_res _ z _ (hJ.mem PEmpty.elim _) _
  have e₆ : (gm (r ≫ jK R) z ⊤ (Units.map (DegPre.toOpen (R := R) ⊤).toMonoidHom u)).val = cst (r ≫ jK R) z u := by
    rw [← gs_unit _ z ⊤ trivial, Units.coe_map, cst, ← hto]; rfl
  have e₇ : ∀ a b : R, cst (r ≫ jK R) z (a * b) = cst (r ≫ jK R) z a * cst (r ≫ jK R) z b := fun a b => by
    rw [cst, map_mul, gs_mul _ z ⊤ trivial]; rfl
  have e₈ : gm (r ≫ jK R) z ⊤ (res le (e₀.s j)) =
      gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j) := gm_res _ z le trivial _
  have hg := Units.mul_inv (gm (r ≫ jK R) z (LB.wchart Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) j) (e₀.s j))
  rw [e₁, e₂, e₅, Units.val_mul, Units.val_mul, e₄]
  erw [e₃]
  rw [map_mul, map_inv, e₈]
  simp only [Units.val_mul]
  rw [e₆, e₇]
  linear_combination (-((trF (L := Q.P.L) (K := PUnit) (fun _ => (Q.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (Q.c χ).left)) j).val * cst (r ≫ jK R) z u * cst (r ≫ jK R) z (∏ i, t i ^ n i))) * hg

end GlobalTheory.UnitPart
