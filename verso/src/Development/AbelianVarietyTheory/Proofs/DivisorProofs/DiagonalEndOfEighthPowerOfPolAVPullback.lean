import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpPolarizationPullbackStable
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.ExistsGenTransfer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

/- English proof (translation)
Introduce `g n F W T T' P P' u f φ ε hS hφ hL`. Take `⟨c, hc, pr, hpr, huniv, hbun, hdiag⟩` from `hS`. Take `⟨⟨c', hc'⟩, -⟩` from `GlobalTheory.siegPre_pullback g n _ (zetaAway n) T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c (by rw [Category.assoc])`. Establish `hc'u : SiegPB c' F.univ (f ≫ u)` using `GlobalTheory.SiegelPullComp.pb_comp hc hc'`. Take `⟨ψ, ψ₂, hψ, hsq, hw, -⟩` from `hc'`.

Establish `hp` using `hψ.1`. Establish `hφp` using `hφ.1`. Establish `wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f` using `fun a => by`. Rewrite using `[Category.assoc, Over.w, hφp.w]`. Set `pr' : Fin 8 → (P'.A ⟶ c'.A)` to `fun a => Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)`.

Establish `hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left` using `fun a => hp.lift_fst _ _ _`. Establish `push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a` using `fun x a => Over.OverMorphism.ext (by show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left`. Rewrite using `[Category.assoc, hpr'ψ, Category.assoc])`. Establish `pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y` using `fun x y => map_mul (pushHom hψ _) x y`. Establish `pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y` using `fun x y => map_mul (pushHom hφ _) x y`.

Establish `injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y` using `fun e => GlobalTheory.SiegelPull.push_injective hψ _ e`. Establish `injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y` using `fun e => GlobalTheory.SiegelPull.push_injective hφ _ e`. Establish `hmon : ∀ a, IsMonHom (pr' a)` using `fun a => by haveI := hpr a`. Use `isMonHom_of_mul _ fun T₁ x y => injψ ?_` and prove the remaining obligations. Rewrite using `[push_comp, pmψ, push_comp, push_comp, pmφ]`.

Conclude with `MonObj.mul_comp _ _ _`. Establish `huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a`. Introduce `T₁ y`. Take `⟨x₀, hx₀, hu₀⟩` from `huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))`. Set `x : T₁ ⟶ P'.A` to `Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)`.

Establish `hx : pushPt hφ.1.w x = x₀` using `Over.OverMorphism.ext (hφp.lift_fst _ _ _)`. Establish `key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a)` using `fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩`. Use `⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩` and prove the remaining obligations. Conclude with `(hu₀ _ ((key z).1 hz)).trans hx.symm`. Establish `hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left` using `fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A) (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2) ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))`.

Establish `hbun' : LBIso P'.L (LB.LinComb c'.P (K` using `Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left) (fun ab => W ab.1 ab.2)) := by`. Set `ε : Fin 8 × Fin 8 → ℤ` to `fun ab => W ab.1 ab.2`. Set `q` to `fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left`. Set `q'` to `fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left`. Establish `l0 : (LB.LinComb c.P q ε).IsLB` using `ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε`.

Establish `l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε).IsLB` using `ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε`. Establish `l2 : (LB.LinComb (c.P.pull ψ₂) q' ε).IsLB` using `ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε`. Establish `l3 : (LB.LinComb c'.P q' ε).IsLB` using `ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε`. Establish `refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε)` using `ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1`. Establish `i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε).pull φ)` using `GlobalTheory.SiegelPullComp.iso_pull φ hbun`.

Establish `i3 : LBIso ((LB.LinComb c.P q ε).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε)` using `LBIso.chartPull (chartPullOut c.P q ε φ _ fun _ => rfl) (chartPullId _) refl1`. Establish `i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb (c.P.pull ψ₂) q' ε)` using `LBIso.chartPull (chartPullId _) (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1`. Establish `i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε) (LB.LinComb c'.P q' ε)` using `GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε`. Establish `h1` using `pull_isLB P.isLB φ`. Establish `h2` using `pull_isLB l0 φ`.

Conclude with `LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))`. Establish `wε : ∀ E, (φ ≫ (ε E).left) ≫ P.A.hom = P'.A.hom ≫ f` using `fun E => by`. Rewrite using `[Category.assoc, Over.w, hφp.w]`. Set `ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A)` to `fun E => Over.homMk (hφp.lift (φ ≫ (ε E).left) P'.A.hom (wε E)) (hφp.lift_snd _ _ _)`. Establish `hε'φ : ∀ E, (ε' E).left ≫ φ = φ ≫ (ε E).left` using `fun E => hφp.lift_fst _ _ _`.

Set `U : Over.mk (P'.A.hom ≫ f) ⟶ P.A` to `pushPt hφ.1.w (𝟙 P'.A)`. Establish `hUl : U.left = φ`. Simplify using `[U, pushPt]`. Establish `hpushε : ∀ E, pushPt hφ.1.w (ε' E) = U ≫ ε E` using `fun E => Over.OverMorphism.ext (by show (ε' E).left ≫ φ = U.left ≫ (ε E).left`. Rewrite using `[hUl, hε'φ])`.

Establish `hpushpr : ∀ b, pushPt hψ.1.w (pr' b) = U ≫ pr b` using `fun b => by`. Rewrite using `[← push_comp]`. Simplify using the standard rewrite rules. Use `⟨ε', ⟨c', hc'u, pr', hmon, huniv', hbun', fun E a => injψ ?_⟩, hε'φ⟩` and prove the remaining obligations. Rewrite using `[push_comp, hpushε, Category.assoc, hdiag E a]`.

Express the relevant statement in the definitionally equal form `preHom (G := c.A) U _ = pushHom hψ P'.A _`. Rewrite using `[map_list_prod, map_list_prod, List.map_map, List.map_map]`. Use `congr 1`. Use `List.map_congr_left fun b _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, map_zpow]`.

Use `congr 1`. Conclude with `(hpushpr b).symm`.
-/
theorem isDiagEnd_pullback : ∀ {g n : ℕ} (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) {T T' : Scheme.{0}}
    (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (ψ : P'.A.left ⟶ P.A.left)
    (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P u ε → IsGrpPullback P'.A P.A f ψ →
    LBIso P'.L (P.L.pull ψ) → ∃ ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A),
      IsDiagEnd F W P' (f ≫ u) ε' ∧ ∀ E, (ε' E).left ≫ ψ = ψ ≫ (ε E).left := by
  intro g n F W T T' P P' u f φ ε hS hφ hL
  obtain ⟨c, hc, pr, hpr, huniv, hbun, hdiag⟩ := hS
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback g n _ (zetaAway n) T T' (u ≫ F.s) ((f ≫ u) ≫ F.s) f c
    (by rw [Category.assoc])
  have hc'u : SiegPB c' F.univ (f ≫ u) := GlobalTheory.SiegelPullComp.pb_comp hc hc'
  obtain ⟨ψ, ψ₂, hψ, hsq, hw, -⟩ := hc'
  have hp := hψ.1
  have hφp := hφ.1
  have wa : ∀ a, (φ ≫ (pr a).left) ≫ c.A.hom = P'.A.hom ≫ f := fun a => by
    rw [Category.assoc, Over.w, hφp.w]
  let pr' : Fin 8 → (P'.A ⟶ c'.A) := fun a =>
    Over.homMk (hp.lift (φ ≫ (pr a).left) P'.A.hom (wa a)) (hp.lift_snd _ _ _)
  have hpr'ψ : ∀ a, (pr' a).left ≫ ψ = φ ≫ (pr a).left := fun a => hp.lift_fst _ _ _
  have push_comp : ∀ {T₁ : Over T'} (x : T₁ ⟶ P'.A) a, pushPt hψ.1.w (x ≫ pr' a) = pushPt hφ.1.w x ≫ pr a :=
    fun x a => Over.OverMorphism.ext (by
      show (x.left ≫ (pr' a).left) ≫ ψ = (x.left ≫ φ) ≫ (pr a).left
      rw [Category.assoc, hpr'ψ, Category.assoc])
  have pmψ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ c'.A), pushPt hψ.1.w (x * y) = pushPt hψ.1.w x * pushPt hψ.1.w y :=
    fun x y => map_mul (pushHom hψ _) x y
  have pmφ : ∀ {T₁ : Over T'} (x y : T₁ ⟶ P'.A), pushPt hφ.1.w (x * y) = pushPt hφ.1.w x * pushPt hφ.1.w y :=
    fun x y => map_mul (pushHom hφ _) x y
  have injψ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ c'.A}, pushPt hψ.1.w x = pushPt hψ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hψ _ e
  have injφ : ∀ {T₁ : Over T'} {x y : T₁ ⟶ P'.A}, pushPt hφ.1.w x = pushPt hφ.1.w y → x = y :=
    fun e => GlobalTheory.SiegelPull.push_injective hφ _ e
  have hmon : ∀ a, IsMonHom (pr' a) := fun a => by
    haveI := hpr a
    refine isMonHom_of_mul _ fun T₁ x y => injψ ?_
    rw [push_comp, pmψ, push_comp, push_comp, pmφ]
    exact MonObj.mul_comp _ _ _
  have huniv' : ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ c'.A)), ∃! x : T₁ ⟶ P'.A, ∀ a, x ≫ pr' a = y a := by
    intro T₁ y
    obtain ⟨x₀, hx₀, hu₀⟩ := huniv (Over.mk (T₁.hom ≫ f)) (fun a => pushPt hψ.1.w (y a))
    let x : T₁ ⟶ P'.A := Over.homMk (hφp.lift x₀.left T₁.hom (Over.w x₀)) (hφp.lift_snd _ _ _)
    have hx : pushPt hφ.1.w x = x₀ := Over.OverMorphism.ext (hφp.lift_fst _ _ _)
    have key : ∀ z : T₁ ⟶ P'.A, (∀ a, z ≫ pr' a = y a) ↔ ∀ a, pushPt hφ.1.w z ≫ pr a = pushPt hψ.1.w (y a) :=
      fun z => forall_congr' fun a => ⟨fun h => by rw [← push_comp, h], fun h => injψ (by rw [push_comp, h])⟩
    refine ⟨x, (key x).2 (by rw [hx]; exact hx₀), fun z hz => injφ ?_⟩
    exact (hu₀ _ ((key z).1 hz)).trans hx.symm
  have hq : ∀ ab : Fin 8 × Fin 8, (lift (pr' ab.1) (pr' ab.2)).left ≫ ψ₂ = φ ≫ (lift (pr ab.1) (pr ab.2)).left :=
    fun ab => (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq hsq (T := Over.mk (φ ≫ P.A.hom)) (T' := P'.A)
      (𝟙 P'.A.left) (pr' ab.1) (pr' ab.2) (Z := P.A) φ (pr ab.1) (pr ab.2)
      ((Category.id_comp _).trans (hpr'ψ ab.1)) ((Category.id_comp _).trans (hpr'ψ ab.2)))
  have hbun' : LBIso P'.L (LB.LinComb c'.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr' ab.1) (pr' ab.2)).left)
      (fun ab => W ab.1 ab.2)) := by
    let ε : Fin 8 × Fin 8 → ℤ := fun ab => W ab.1 ab.2
    let q := fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left
    let q' := fun ab : Fin 8 × Fin 8 => (lift (pr' ab.1) (pr' ab.2)).left
    have l0 : (LB.LinComb c.P q ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB q ε
    have l1 : (LB.LinComb c.P (fun ab => φ ≫ q ab) ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c.P c.isLB _ ε
    have l2 : (LB.LinComb (c.P.pull ψ₂) q' ε).IsLB :=
      ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB (c.P.pull ψ₂) (pull_isLB c.isLB ψ₂) q' ε
    have l3 : (LB.LinComb c'.P q' ε).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB c'.P c'.isLB q' ε
    have refl1 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ l1
    have i2 : LBIso (P.L.pull φ) ((LB.LinComb c.P q ε).pull φ) := GlobalTheory.SiegelPullComp.iso_pull φ hbun
    have i3 : LBIso ((LB.LinComb c.P q ε).pull φ) (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) :=
      LBIso.chartPull (chartPullOut c.P q ε φ _ fun _ => rfl) (chartPullId _) refl1
    have i4 : LBIso (LB.LinComb c.P (fun ab => φ ≫ q ab) ε) (LB.LinComb (c.P.pull ψ₂) q' ε) :=
      LBIso.chartPull (chartPullId _)
        (chartPullLinComb c.P ψ₂ q' (fun ab => φ ≫ q ab) ε (𝟙 _) fun ab => (hq ab).trans (Category.id_comp _).symm) refl1
    have i5 : LBIso (LB.LinComb (c.P.pull ψ₂) q' ε) (LB.LinComb c'.P q' ε) :=
      GlobalTheory.PowPrimitive.lbIso_linComb hw.symm q' ε
    have h1 := pull_isLB P.isLB φ
    have h2 := pull_isLB l0 φ
    exact LBIso.trans P'.isLB h1 l3 hL (LBIso.trans h1 h2 l3 i2 (LBIso.trans h2 l1 l3 i3 (LBIso.trans l1 l2 l3 i4 i5)))

  have wε : ∀ E, (φ ≫ (ε E).left) ≫ P.A.hom = P'.A.hom ≫ f := fun E => by
    rw [Category.assoc, Over.w, hφp.w]
  let ε' : Matrix (Fin 8) (Fin 8) ℤ → (P'.A ⟶ P'.A) := fun E =>
    Over.homMk (hφp.lift (φ ≫ (ε E).left) P'.A.hom (wε E)) (hφp.lift_snd _ _ _)
  have hε'φ : ∀ E, (ε' E).left ≫ φ = φ ≫ (ε E).left := fun E => hφp.lift_fst _ _ _
  let U : Over.mk (P'.A.hom ≫ f) ⟶ P.A := pushPt hφ.1.w (𝟙 P'.A)
  have hUl : U.left = φ := by
    simp [U, pushPt]
  have hpushε : ∀ E, pushPt hφ.1.w (ε' E) = U ≫ ε E := fun E => Over.OverMorphism.ext (by
    show (ε' E).left ≫ φ = U.left ≫ (ε E).left
    rw [hUl, hε'φ])
  have hpushpr : ∀ b, pushPt hψ.1.w (pr' b) = U ≫ pr b := fun b => by
    rw [← push_comp]; simp
  refine ⟨ε', ⟨c', hc'u, pr', hmon, huniv', hbun', fun E a => injψ ?_⟩, hε'φ⟩
  rw [push_comp, hpushε, Category.assoc, hdiag E a]
  change preHom (G := c.A) U _ = pushHom hψ P'.A _
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply, map_zpow]
  congr 1
  exact (hpushpr b).symm

end GlobalTheory.Poinc
