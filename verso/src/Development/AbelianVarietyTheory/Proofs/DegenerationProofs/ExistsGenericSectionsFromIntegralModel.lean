import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCarries
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFOfIntegral
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralDegenerationFamilyBaseChangeExtensionFie
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory.UT GlobalTheory.ZH.ClassWeight

noncomputable section
namespace GlobalTheory.ZH.IntegralCarry
open GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH.ParTranslate GlobalTheory.ThetaSpecialise

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)

/- English proof (translation)
Establish `one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1` using `fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]`. Use `⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE, (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_, fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_one, one, _root_.one_mul]`. Conclude with `(sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans (congrArg (fun q => sval σ q y J) (Category.assoc _ _ _)))`. Rewrite using `[Fin.sum_univ_one, one, _root_.one_mul]`.

Conclude with `(SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm`.
-/
theorem expandsG_extend
    (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hE : ∀ e, U.ExpandsAt e k σ f) (s : Fam D.toPre F k)
    (hs : FamOf D.toPre F f s) : U.ExpandsG F k (extendSec U F k (genericSec U k σ)) s := by
  have one : ∀ {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of F)) (y : Y), gs (𝟙 Y) y ⊤ (scal π (1 : F)) = 1 :=
    fun π y => by simp only [gs_eq _ y ⊤ trivial, scal, map_one]
  refine ⟨1, fun _ => 1, fun _ => σ, fun _ => f, fun _ => hE,
    (secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_,
    fun α => (secLin_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_⟩
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
      (congrArg (fun q => sval σ q y J) (Category.assoc _ _ _)))
  · rw [Fin.sum_univ_one, one, _root_.one_mul]
    exact (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm

/- English proof (translation)
Use `sec_ext_val (s' := (0 : Fam D.toPre F k).s α) D.toPre.P.isLB (fun y J hJ => ?_) j` and prove the remaining obligations. Use `(SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm.trans (Eq.trans ?_ (sval_zero' (π := famBase D.toPre F) hJ _).symm)` and prove the remaining obligations. Conclude with `(gs_eq _ _ _ (hJ.mem _ _) _).trans ((congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _))`.
-/
theorem famOf_zero (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (s : Fam D.toPre F k)
    (hs : FamOf D.toPre F f s) (α : D.toPre.X) (h : ∀ j, (f α).f j = 0) (j) : (s.s α).f j = 0 := by
  refine sec_ext_val (s' := (0 : Fam D.toPre F k).s α) D.toPre.P.isLB (fun y J hJ => ?_) j
  refine (SectionScalarValuation.secScal_sval (hs α) _ y hJ).symm.trans (Eq.trans ?_ (sval_zero' (π := famBase D.toPre F) hJ _).symm)
  exact (gs_eq _ _ _ (hJ.mem _ _) _).trans ((congrArg _ ((congrArg _ (h _)).trans (map_zero _))).trans (map_zero _))

/- English proof (translation)
Take `⟨l', c, hl', hv⟩` from `h`. Take `⟨l, rfl⟩ : ∃ l : U.LG.L.ι, l' = fun _ : Fin 1 => l` from `⟨l' 0, funext fun i => congrArg l' (Subsingleton.elim _ _)⟩`. Set `y : Sp F` to `IsLocalRing.closedPoint F`. Set `x : Sp F ⟶ G.left` to `a.left ≫ pullback.fst G.hom (jK R)`. Establish `m : x y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => l)` using `(top_le_iff_mem _ _ y).1 hl'`.

Establish `m₀ : x y ∈ U.LG.L.U l` using `mem_wchart.1 m 0`. Take `⟨J₀, hJ⟩` from `GlobalTheory.UT.CoefBasic.exists_good' A.isLB y`. Take `⟨d, hd⟩` from `exists_unit_carries U F k w a l ((top_le_iff_mem x _ y).2 m₀) y J₀ hJ`. Take `⟨d₀, hd₀⟩` from `toStk_onto y d.val`. Establish `hd₁ : d₀ ≠ 0` using `fun h0 => by`.

Establish `: Nontrivial ((Sp F).presheaf.stalk y)` using `inferInstance`. Rewrite `hd₀` using `[h0, map_zero]`. Conclude with `Units.ne_zero _ hd₀.symm`. Set `r : Sp F ⟶ (UnifPre.GF (G` to `G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left`. Set `r' : Sp F ⟶ (TFK (R` to `R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left`.

Establish `e₀ : r ≫ (snd (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left = a.left := congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)`. Establish `e₁ : (r ≫ (snd (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) = x := by`. Rewrite using `[e₀]`. Establish `m₂ : ((r ≫ (snd (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈ U.LG.L.U l := e₁ ▸ m₀`. Establish `m'` using `hJ.mem (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) r'`.

Use `⟨fun _ : Fin 1 => J₀ (r' ≫ (snd (TFK (R := R) F) A.A).left), c * Units.mk0 d₀ hd₁, (top_le_iff_mem r' _ y).2 m', fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hv i, Units.val_mul, _root_.mul_assoc, Units.val_mk0]`. Use `congrArg _ ((toStk y).injective ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hd₀]`. Use `(toStk_valF_gs x _ y m _).trans (Eq.trans ?_ ((hd _ _ (ht i)).trans (congrArg _ (toStk_valF_gs r' _ y m' _).symm)))` and prove the remaining obligations.

Use `Eq.symm ((toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans ?_)` and prove the remaining obligations. Rewrite using `[← e₁]`. Conclude with `(gs_pullOver (isPullback_groupBase F).w (fun _ => rfl) (genericSec U k (σ i)) r y (fun _ => l) (fun _ => m₂)).trans (gs_pullOver (p := pullback.fst G.hom (jK R)) pullback.condition (fun _ => (Category.comp_id _).symm) (σ i) _ y (fun _ => l) (fun _ => m₂))`.
-/
theorem crd_carries (w : W0 U) {J : Type}
    (σ : J → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (t : J → SecA A F k) (ht : ∀ i, Carries U F k w (t i) (extendSec U F k (genericSec U k (σ i))))
    (a : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (v : J → F)
    (h : Crd _ σ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) v) :
    Crd (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) t (show Sp F ⟶ _ from (ptSecT A.A (a ≫ U.gen.hom)).left) v := by
  obtain ⟨l', c, hl', hv⟩ := h
  obtain ⟨l, rfl⟩ : ∃ l : U.LG.L.ι, l' = fun _ : Fin 1 => l := ⟨l' 0, funext fun i => congrArg l' (Subsingleton.elim _ _)⟩
  let y : Sp F := IsLocalRing.closedPoint F
  let x : Sp F ⟶ G.left := a.left ≫ pullback.fst G.hom (jK R)
  have m : x y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => l) := (top_le_iff_mem _ _ y).1 hl'
  have m₀ : x y ∈ U.LG.L.U l := mem_wchart.1 m 0
  obtain ⟨J₀, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' A.isLB y
  obtain ⟨d, hd⟩ := exists_unit_carries U F k w a l ((top_le_iff_mem x _ y).2 m₀) y J₀ hJ
  obtain ⟨d₀, hd₀⟩ := toStk_onto y d.val
  have hd₁ : d₀ ≠ 0 := fun h0 => by
    have : Nontrivial ((Sp F).presheaf.stalk y) := inferInstance
    rw [h0, map_zero] at hd₀
    exact Units.ne_zero _ hd₀.symm
  let r : Sp F ⟶ (UnifPre.GF (G := G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left
  let r' : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e₀ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = a.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)
  have e₁ : (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R) = x := by
    rw [e₀]
  have m₂ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈
      U.LG.L.U l := e₁ ▸ m₀
  have m' := hJ.mem (fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) r'
  refine ⟨fun _ : Fin 1 => J₀ (r' ≫ (snd (TFK (R := R) F) A.A).left), c * Units.mk0 d₀ hd₁,
    (top_le_iff_mem r' _ y).2 m', fun i => ?_⟩
  rw [hv i, Units.val_mul, _root_.mul_assoc, Units.val_mk0]
  refine congrArg _ ((toStk y).injective ?_)
  rw [map_mul, hd₀]
  refine (toStk_valF_gs x _ y m _).trans (Eq.trans ?_ ((hd _ _ (ht i)).trans
    (congrArg _ (toStk_valF_gs r' _ y m' _).symm)))
  refine Eq.symm ((toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans ?_)
  rw [← e₁]
  exact (gs_pullOver (isPullback_groupBase F).w (fun _ => rfl) (genericSec U k (σ i)) r y (fun _ => l)
      (fun _ => m₂)).trans (gs_pullOver (p := pullback.fst G.hom (jK R)) pullback.condition
        (fun _ => (Category.comp_id _).symm) (σ i) _ y (fun _ => l) (fun _ => m₂))

end

/- English proof (translation)
Introduce `hL o Ω _ _ _ _ S ρ p _ y₀ u k J σ f hE hf w₀ hw₀`. Establish `hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) k, FamOf u.D.toPre _ (f i) s` using `fun i => by`. Take `⟨s, hs⟩` from `hf i`. Conclude with `GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D k s (f i) hs (PadicAlgCl p)`. Use `choose s hs using hs`.

Use `choose t ht using fun i => exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀ (extendSec u.U.toUnifPre (PadicAlgCl p) k (genericSec u.U.toUnifPre k (σ i)))`. Conclude with `⟨t, s, fun i => ⟨_, ht i, expandsG_extend _ _ k (σ i) (f i) (hE i) (s i) (hs i)⟩, fun i α h j => famOf_zero _ k (f i) (s i) (hs i) α h j, fun a v h => crd_carries u.U.toUnifPre _ k w₀ σ t ht a v h⟩`.
-/
theorem exists_carry : LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (J : Type) (σ : J → (u.H k).Sec) (f : J → ∀ α, u.D.toPre.SecB k α), (∀ i e, u.U.toUnifPre.ExpandsAt e k (σ i) (f i)) → (∀ i, ∃ s : Fam u.D.toPre (FractionRing u.V) k, FamOf u.D.toPre _ (f i) s) → ∀ w₀ : W0 u.U.toUnifPre, w₀.IsGen → ∃ (t : J → SecA u.A (PadicAlgCl p) k) (s : J → Fam u.D.toPre (PadicAlgCl p) k), (∀ i, u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ (t i) (s i)) ∧ (∀ i α, (∀ j, (f i α).f j = 0) → ∀ j, ((s i).s α).f j = 0) ∧ ∀ (a : u.PtC) (v : J → PadicAlgCl p), Crd (u.H k) σ (u.toG a) v → Crd (LPow u.A.A u.A.L (k : ℤ) (TFK (R := u.V) (PadicAlgCl p))) t (show Sp (PadicAlgCl p) ⟶ _ from (ptSecT u.A.A (a ≫ u.U.gen.hom)).left) v := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k J σ f hE hf w₀ hw₀
  have hs : ∀ i, ∃ s : Fam u.D.toPre (PadicAlgCl p) k, FamOf u.D.toPre _ (f i) s := fun i => by
    obtain ⟨s, hs⟩ := hf i
    exact GlobalTheory.FamBaseChange.main hL.1.globalFns u.V _ u.D k s (f i) hs (PadicAlgCl p)
  choose s hs using hs
  choose t ht using fun i => exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀
    (extendSec u.U.toUnifPre (PadicAlgCl p) k (genericSec u.U.toUnifPre k (σ i)))
  exact ⟨t, s, fun i => ⟨_, ht i, expandsG_extend _ _ k (σ i) (f i) (hE i) (s i) (hs i)⟩,
    fun i α h j => famOf_zero _ k (f i) (s i) (hs i) α h j,
    fun a v h => crd_carries u.U.toUnifPre _ k w₀ σ t ht a v h⟩

end GlobalTheory.ZH.IntegralCarry
end
