import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFgForallOverLbIso
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LbIsoLinCombPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SqDecBC

/- English proof (translation)
Introduce `k R S _ _ _ _ _ ρ A₀ _ L M hL hM hD`. Take `⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩` from `hD`. Use `set bc := GlobalTheory.Spread.bcMap A₀.hom ρ with hbc`. Establish `hg' : ∀ i, ∃ g : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀, IsMonHom g ∧ g.left ≫ bc = bc ≫ (β i).left`. Introduce `i`.

Use `haveI := hβ i`. Take `⟨g, hg, e⟩` from `GlobalTheory.HomDescent.exists_specialise (β i) ρ`. Use `⟨g, hg, ?_⟩` and prove the remaining obligations. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, hbc, GlobalTheory.Spread.bcMap_fst, e, Category.assoc]`.

Establish `w₁` using `Over.w g`. Establish `w₂` using `Over.w (β i)`. Simplify using `only [Over.pullback_obj_hom] at w₁ w₂`. Rewrite using `[Category.assoc, hbc, GlobalTheory.Spread.bcMap_snd, ← Category.assoc, w₁, Category.assoc, w₂, GlobalTheory.Spread.bcMap_snd]`. Use `choose g hgm hgc using hg'`.

Use `⟨N, a₀, r, a, g, hN, ha₀, hgm, ?_⟩` and prove the remaining obligations. Use `set fR := pullback.fst A₀.hom (spMap (algebraMap k R)) with hfR`. Use `set fS := pullback.fst A₀.hom (spMap (algebraMap k S)) with hfS`. Establish `efS : fS = bc ≫ fR` using `(GlobalTheory.Spread.bcMap_fst A₀.hom ρ).symm`. Establish `pullIso : ∀ {X Y : Scheme.{0}} {P Q : LB X}, LBIso P Q → ∀ f : Y ⟶ X, LBIso (P.pull f) (Q.pull f)` using `fun h f => h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl)`.

Establish `i1` using `lbIso_lbPow_pull hL fS N`. Establish `i2` using `GlobalTheory.Spread.lbIso_pull_pull (isLB_lbPow hL N) bc efS`. Establish `i3` using `pullIso (lbIso_lbPow_pull hL fR N).symm bc`. Establish `i4` using `pullIso H bc`. Establish `hc : ∀ o : Option (Fin r), (o.elim (𝟙 _) fun i => (g i).left) ≫ bc = bc ≫ (o.elim (𝟙 _) fun i => (β i).left)`.

Introduce `o`. Consider the cases of `o with`. Consider the case `none => simp`. Consider the case `some i => exact hgc i`. Establish `i5` using `(GlobalTheory.SymExtend.lbIso_linComb_pull (pull_isLB hM fR) bc (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (g i).left) (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (β i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) bc hc).symm`.

Establish `i6 : LBIso (LB.LinComb ((M.pull fR).pull bc) (K` using `Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ))) (LB.LinComb (M.pull fS) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ))) := by`. Take `⟨w, hw⟩` from `(GlobalTheory.Spread.lbIso_pull_pull hM bc efS).symm`. Conclude with `⟨_, DVR.linCombIso_isGen w hw _ _⟩`. Establish `j1` using `i1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _) (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _) i2`. Establish `j2` using `j1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _) (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _) i3`.

Establish `j3` using `j2.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _) (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _) i4`. Establish `j4` using `j3.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _) (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _) i5`. Conclude with `j4.trans (isLB_lbPow (pull_isLB hL _) N) (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _) (LB.isLB_linComb (pull_isLB hM _) _ _) i6`.
-/
theorem sqDec_baseChange : ∀ (k R S : Type) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S] (ρ : R →ₐ[k] S) (A₀ : Over (Sp k)) [GrpObj A₀] (L M : LB A₀.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (algebraMap k R))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k R)))) → SqDec ((Over.pullback (spMap (algebraMap k S))).obj A₀) (L.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) (M.pull (pullback.fst A₀.hom (spMap (algebraMap k S)))) := by
  intro k R S _ _ _ _ _ ρ A₀ _ L M hL hM hD
  obtain ⟨N, a₀, r, a, β, hN, ha₀, hβ, H⟩ := hD
  set bc := GlobalTheory.Spread.bcMap A₀.hom ρ with hbc
  have hg' : ∀ i, ∃ g : (Over.pullback (spMap (algebraMap k S))).obj A₀ ⟶ (Over.pullback (spMap (algebraMap k S))).obj A₀,
      IsMonHom g ∧ g.left ≫ bc = bc ≫ (β i).left := by
    intro i
    haveI := hβ i
    obtain ⟨g, hg, e⟩ := GlobalTheory.HomDescent.exists_specialise (β i) ρ
    refine ⟨g, hg, ?_⟩
    apply pullback.hom_ext
    · rw [Category.assoc, hbc, GlobalTheory.Spread.bcMap_fst, e, Category.assoc]
    · have w₁ := Over.w g
      have w₂ := Over.w (β i)
      simp only [Over.pullback_obj_hom] at w₁ w₂
      rw [Category.assoc, hbc, GlobalTheory.Spread.bcMap_snd, ← Category.assoc, w₁, Category.assoc, w₂, GlobalTheory.Spread.bcMap_snd]
  choose g hgm hgc using hg'
  refine ⟨N, a₀, r, a, g, hN, ha₀, hgm, ?_⟩
  set fR := pullback.fst A₀.hom (spMap (algebraMap k R)) with hfR
  set fS := pullback.fst A₀.hom (spMap (algebraMap k S)) with hfS
  have efS : fS = bc ≫ fR := (GlobalTheory.Spread.bcMap_fst A₀.hom ρ).symm
  have pullIso : ∀ {X Y : Scheme.{0}} {P Q : LB X}, LBIso P Q → ∀ f : Y ⟶ X, LBIso (P.pull f) (Q.pull f) :=
    fun h f => h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ f f rfl)
  have i1 := lbIso_lbPow_pull hL fS N
  have i2 := GlobalTheory.Spread.lbIso_pull_pull (isLB_lbPow hL N) bc efS
  have i3 := pullIso (lbIso_lbPow_pull hL fR N).symm bc
  have i4 := pullIso H bc
  have hc : ∀ o : Option (Fin r), (o.elim (𝟙 _) fun i => (g i).left) ≫ bc = bc ≫ (o.elim (𝟙 _) fun i => (β i).left) := by
    intro o
    cases o with
    | none => simp
    | some i => exact hgc i
  have i5 := (GlobalTheory.SymExtend.lbIso_linComb_pull (pull_isLB hM fR) bc (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (g i).left)
    (fun o : Option (Fin r) => o.elim (𝟙 _) fun i => (β i).left) (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)) bc hc).symm
  have i6 : LBIso (LB.LinComb ((M.pull fR).pull bc) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left)
      (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ)))
      (LB.LinComb (M.pull fS) (K := Option (Fin r)) (fun o => o.elim (𝟙 _) fun i => (g i).left)
      (fun o => o.elim (a₀ : ℤ) fun i => (a i : ℤ))) := by
    obtain ⟨w, hw⟩ := (GlobalTheory.Spread.lbIso_pull_pull hM bc efS).symm
    exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩
  have j1 := i1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow hL N) _)
    (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _) i2
  have j2 := j1.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (pull_isLB (isLB_lbPow hL N) _) _)
    (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _) i3
  have j3 := j2.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (isLB_lbPow (pull_isLB hL _) N) _)
    (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _) i4
  have j4 := j3.trans (isLB_lbPow (pull_isLB hL _) N) (pull_isLB (LB.isLB_linComb (pull_isLB hM _) _ _) _)
    (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _) i5
  exact j4.trans (isLB_lbPow (pull_isLB hL _) N) (LB.isLB_linComb (pull_isLB (pull_isLB hM _) _) _ _)
    (LB.isLB_linComb (pull_isLB hM _) _ _) i6

end GlobalTheory.SqDecBC
