import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRingActionAdjointCubeBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.Mum.NormLam

/- English proof (translation)
Take `⟨w, hw⟩` from `h`. Conclude with `⟨_, DVR.linCombIso_isGen w hw _ _⟩`.
-/
theorem lbIso_cubeLB' {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L M : LB G.left} (h : LBIso L M) : LBIso (cubeLB G x L) (cubeLB G x M) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨_, DVR.linCombIso_isGen w hw _ _⟩

/- English proof (translation)
The claim follows from `DVR.linComb_isLB _ h _ _`.
-/
theorem cubeLB_isLB' {S : Scheme.{0}} {G T : Over S} [GrpObj G] [IsCommMonObj G] {n : ℕ} (x : Fin n → (T ⟶ G))
    {L : LB G.left} (h : L.IsLB) : (cubeLB G x L).IsLB := DVR.linComb_isLB _ h _ _

/- English proof (translation)
Introduce `R _ _ _ hR D A G _ _ hS U O _ _ _ o oA oG hlin w hw P hP`. Establish `hwh` using `oG.hom w`. Establish `hwh'` using `oG.hom (star w)`. Establish `hM` using `U.LG.isLB`. Establish `hT : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen` using `⟨U.cubG.t, U.cubG.isGen⟩`.

Establish `hadd : oG.act w * oG.act (star w) = 𝟙 G`. Establish `e` using `oG.map_add w (star w)`. Rewrite `e` using `[hw, oG.map_one]`. Conclude with `(e.trans rfl).symm`. Establish `hadj` using `fun a => GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star R hR.1 D A G hS U O o oA oG hlin a`.

Establish `hc` using `fun T : Over (Sp R) => GlobalTheory.PrimNorm.diff₃_ptCls (T := T) hM hT`. Establish `hq : ∀ T : Over (Sp R), (fun x : T ⟶ G => GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w) x.left) = fun x => GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act w) T x)` using `fun T => funext fun x => GlobalTheory.PrimNorm.normCls_left _ x`. Establish `hs : ∀ (T : Over (Sp R)) (y : T ⟶ G), GlobalTheory.PrimNorm.postHom (oG.act w) T y * GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y = y` using `fun T y => (MonObj.comp_mul y _ _).symm.trans (by rw [hadd, Category.comp_id])`. Establish `hadj' : ∀ (T : Over (Sp R)) (x y : T ⟶ G), GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) (GlobalTheory.PrimNorm.postHom (oG.act w) T x) y = GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act (star w)) T …` using `fun T x y => GlobalTheory.PrimNorm.diff₂_ptCls_adj hM (hadj w) x y`. Establish `iso : ∀ (T : Over (Sp R)) (x y : T ⟶ G), LBIso (cubeLB G ![x, y] (cubeLB G ![𝟙 G, oG.act w] U.LG.L)) (cubeLB G ![x, y] U.LG.L)` using `fun T x y => by`.

Use `GlobalTheory.PrimNorm.lbIso_nested hM _ _ _ _ _ _ ((GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w))).trans (Eq.trans ?_ (GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.cls U.LG.L)).symm))` and prove the remaining obligations. Rewrite using `[hq]`. Conclude with `GlobalTheory.PrimNorm.diff₂_quadratic (hc T) _ _ (hs _) (hadj' _) x y`. Establish `hN` using `cubeLB_isLB' ![𝟙 G, oG.act w] hM`. Establish `hPL` using `P.L.isLB`.

Establish `cP : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x P.L.L).IsLB` using `fun x => cubeLB_isLB' x hPL`. Establish `cN : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x (cubeLB G ![𝟙 G, oG.act w] U.LG.L)).IsLB` using `fun x => cubeLB_isLB' x hN`. Establish `cL : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x U.LG.L).IsLB` using `fun x => cubeLB_isLB' x hM`. Establish `isoP : ∀ (T : Over (Sp R)) (x y : T ⟶ G), LBIso (cubeLB G ![x, y] P.L.L) (cubeLB G ![x, y] U.LG.L)` using `fun T x y => LBIso.trans (cP _) (cN _) (cL _) (lbIso_cubeLB' _ hP) (iso T x y)`. Use `⟨isoP _ (fst G G) (snd G G), fun a => ?_, ?_⟩` and prove the remaining obligations.

Conclude with `LBIso.trans (cP _) (cL _) (cP _) (isoP _ _ _) (LBIso.trans (cL _) (cL _) (cP _) (hadj a) (isoP _ _ _).symm)`. Conclude with `LBIso.trans hPL hN (cP _) hP (LBIso.trans hN (cN _) (cP _) (iso G (𝟙 G) (oG.act w)).symm (lbIso_cubeLB' _ hP).symm)`.
-/
theorem lbIso_lam_adj_prim : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ w : O, w + star w = 1 → ∀ P : GlobalTheory.UU.CP G, LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] U.LG.L) → LBIso (abelian₂ G P.L.L) (abelian₂ G U.LG.L) ∧ (∀ a, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] P.L.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] P.L.L)) ∧ LBIso P.L.L (cubeLB G ![𝟙 G, oG.act w] P.L.L) := by
  intro R _ _ _ hR D A G _ _ hS U O _ _ _ o oA oG hlin w hw P hP
  have hwh := oG.hom w
  have hwh' := oG.hom (star w)
  have hM := U.LG.isLB
  have hT : ∃ t : LB.Gen (Theta G U.LG.L), t.IsGen := ⟨U.cubG.t, U.cubG.isGen⟩
  have hadd : oG.act w * oG.act (star w) = 𝟙 G := by
    have e := oG.map_add w (star w)
    rw [hw, oG.map_one] at e
    exact (e.trans rfl).symm
  have hadj := fun a => GlobalTheory.Mum.UnifAdjoint.lbIso_cubeLB_star R hR.1 D A G hS U O o oA oG hlin a
  have hc := fun T : Over (Sp R) => GlobalTheory.PrimNorm.diff₃_ptCls (T := T) hM hT
  have hq : ∀ T : Over (Sp R), (fun x : T ⟶ G => GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w) x.left) =
      fun x => GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act w) T x) :=
    fun T => funext fun x => GlobalTheory.PrimNorm.normCls_left _ x
  have hs : ∀ (T : Over (Sp R)) (y : T ⟶ G),
      GlobalTheory.PrimNorm.postHom (oG.act w) T y * GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y = y :=
    fun T y => (MonObj.comp_mul y _ _).symm.trans (by rw [hadd, Category.comp_id])
  have hadj' : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) (GlobalTheory.PrimNorm.postHom (oG.act w) T x) y =
      GlobalTheory.PrimNorm.diff₂ (GlobalTheory.PrimNorm.ptCls U.LG.L T) x (GlobalTheory.PrimNorm.postHom (oG.act (star w)) T y) :=
    fun T x y => GlobalTheory.PrimNorm.diff₂_ptCls_adj hM (hadj w) x y
  have iso : ∀ (T : Over (Sp R)) (x y : T ⟶ G),
      LBIso (cubeLB G ![x, y] (cubeLB G ![𝟙 G, oG.act w] U.LG.L)) (cubeLB G ![x, y] U.LG.L) := fun T x y => by
    refine GlobalTheory.PrimNorm.lbIso_nested hM _ _ _ _ _ _
      ((GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.normCls U.LG.L (oG.act w))).trans
      (Eq.trans ?_ (GlobalTheory.PrimNorm.prod_square_id x y (GlobalTheory.PrimNorm.cls U.LG.L)).symm))
    rw [hq]
    exact GlobalTheory.PrimNorm.diff₂_quadratic (hc T) _ _ (hs _) (hadj' _) x y
  have hN := cubeLB_isLB' ![𝟙 G, oG.act w] hM
  have hPL := P.L.isLB
  have cP : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x P.L.L).IsLB := fun x => cubeLB_isLB' x hPL
  have cN : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x (cubeLB G ![𝟙 G, oG.act w] U.LG.L)).IsLB :=
    fun x => cubeLB_isLB' x hN
  have cL : ∀ {T : Over (Sp R)} (x : Fin 2 → (T ⟶ G)), (cubeLB G x U.LG.L).IsLB := fun x => cubeLB_isLB' x hM

  have isoP : ∀ (T : Over (Sp R)) (x y : T ⟶ G), LBIso (cubeLB G ![x, y] P.L.L) (cubeLB G ![x, y] U.LG.L) :=
    fun T x y => LBIso.trans (cP _) (cN _) (cL _) (lbIso_cubeLB' _ hP) (iso T x y)
  refine ⟨isoP _ (fst G G) (snd G G), fun a => ?_, ?_⟩
  · exact LBIso.trans (cP _) (cL _) (cP _) (isoP _ _ _)
      (LBIso.trans (cL _) (cL _) (cP _) (hadj a) (isoP _ _ _).symm)
  · exact LBIso.trans hPL hN (cP _) hP (LBIso.trans hN (cN _) (cP _) (iso G (𝟙 G) (oG.act w)).symm
      (lbIso_cubeLB' _ hP).symm)

end GlobalTheory.Mum.NormLam
