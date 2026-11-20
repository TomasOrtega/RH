import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulEqZeroOfIsIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeBundleGeneratedOfModelIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomBirationalModelsAmpleFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothProjectiveStalkFactorial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.DenseGenericOfFlat
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelRelAmpleAndPrincipalAbelianLocus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoOfDisjointCover

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HodgeMin

open GlobalTheory.CechPic

/- English proof (translation)
Introduce `g n F Z z i OZ S π j _ G _ e hM hS hp hj hji hG hsm he`. Take `⟨o', _, β, S', s', U, c, π', G', _, e', _, N, ⟨-, hz, -, hiz, -, hO, -⟩, ⟨-, -, -, hS', -, _, _, hU, -, -, _, _⟩, ⟨hG', hsm', he'⟩, hN, hiso⟩` from `hM`. Use `GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n` as an intermediate fact. Use `GlobalTheory.ThetaDescent.isProper_of_isProjOver hp` as an intermediate fact. Establish `: QuasiSeparated π` using `.of_comp π z`.

Establish `: IsLocallyNoetherian S'` using `LocallyOfFiniteType.isLocallyNoetherian π'`. Establish `: IsLocallyNoetherian S` using `LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)`. Establish `: CompactSpace S` using `QuasiCompact.compactSpace_of_compactSpace (π ≫ z)`. Establish `: AlgebraicGeometry.IsNoetherian S` using `{}`. Establish `hd : Dense (⇑(c ≫ j) '' {x | (((c ≫ j) ≫ π ≫ z) x).asIdeal = ⊥})`.

Use `(DenseRange.dense_image hj j.continuous F.isReduced_and_dense.2).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨y, rfl⟩` from `c.surjective x`. Use `⟨y, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, reassoc_of% hji, hiz]`.

Conclude with `hx`. Take `⟨W, p, p', H, _, α, α', _, _, hw, h₁, h₂⟩` from `exists_common_cover z π π' (GlobalTheory.IsNormalScheme.pred S') (c ≫ j) U.ι (by rw [Category.assoc, hji, hU]) hd hG hG' ((isGrpPullback_pullback F.univ.A c).comp he) he'`. Use `hG.separated` as an intermediate fact. Use `hG'.separated` as an intermediate fact. Establish `v₁` using `GlobalTheory.LieVB.isVB_omega G g`.

Establish `v₂` using `GlobalTheory.LieVB.isVB_omega G' g`. Establish `l₁ : (hodge G g).IsLB` using `v₁.isLB_det`. Establish `l₂ : (hodge G' g).IsLB` using `v₂.isLB_det`. Establish `l₃ : (hodge H g).IsLB` using `(GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h₁ v₁).isLB_det`. Establish `e₁` using `(cls_eq_iff (pull_isLB l₁ p) l₃).2 (HodgeGenDesc.lbIso_hodge_pull h₁ v₁)`.

Establish `e₂` using `(cls_eq_iff (pull_isLB l₂ p') l₃).2 (HodgeGenDesc.lbIso_hodge_pull h₂ v₂)`. Establish `e₃` using `(cls_eq_iff (pull_isLB hO π') (isLB_lbPow l₂ N)).2 hiso`. Rewrite `e₁` using `[cls_pull l₁]`. Rewrite `e₂` using `[cls_pull l₂]`. Rewrite `e₃` using `[cls_pull hO, cls_lbPow l₂]`.

Take `⟨d, hd, h⟩` from `exists_nsmul_eq_zero hS p (N • cls _ l₁ - pull π (cls _ hO)) (by`. Rewrite using `[map_sub, map_nsmul, ← pull_comp, hw, pull_comp, e₃, map_nsmul, e₁, e₂, sub_self])`. Use `⟨d, d * N, hd, Nat.mul_pos hd hN, (cls_eq_iff (isLB_lbPow l₁ _) (isLB_lbPow (pull_isLB hO π) _)).1 ?_⟩` and prove the remaining obligations. Rewrite using `[cls_lbPow l₁, cls_lbPow (pull_isLB hO π), cls_pull hO, mul_smul, ← sub_eq_zero, ← smul_sub, h]`.
-/
theorem hodge_pow_iso_pull_pow_of_minimal_compactification : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left), MinAt5 F z i OZ → Geo.Tor.IsNormalScheme S → IsProjOver (π ≫ z) → Dense (Set.range j) → j ≫ π = i → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsGrpPullback F.univ.A G j e → ∃ a N : ℕ, 1 ≤ a ∧ 1 ≤ N ∧ LBIso (lbPow (hodge G g) N) (lbPow (OZ.pull π) a) := by
  intro g n F Z z i OZ S π j _ G _ e hM hS hp hj hji hG hsm he
  obtain ⟨o', _, β, S', s', U, c, π', G', _, e', _, N, ⟨-, hz, -, hiz, -, hO, -⟩,
    ⟨-, -, -, hS', -, _, _, hU, -, -, _, _⟩, ⟨hG', hsm', he'⟩, hN, hiso⟩ := hM
  have := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway n
  have := GlobalTheory.ThetaDescent.isProper_of_isProjOver hp
  have : QuasiSeparated π := .of_comp π z
  have : IsLocallyNoetherian S' := LocallyOfFiniteType.isLocallyNoetherian π'
  have : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ z)
  have : CompactSpace S := QuasiCompact.compactSpace_of_compactSpace (π ≫ z)
  have : AlgebraicGeometry.IsNoetherian S := {}
  have hd : Dense (⇑(c ≫ j) '' {x | (((c ≫ j) ≫ π ≫ z) x).asIdeal = ⊥}) := by
    refine (DenseRange.dense_image hj j.continuous F.isReduced_and_dense.2).mono ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, rfl⟩ := c.surjective x
    refine ⟨y, ?_, by simp⟩
    rw [Category.assoc, reassoc_of% hji, hiz]
    exact hx
  obtain ⟨W, p, p', H, _, α, α', _, _, hw, h₁, h₂⟩ := exists_common_cover z π π' (GlobalTheory.IsNormalScheme.pred S') (c ≫ j) U.ι
    (by rw [Category.assoc, hji, hU]) hd hG hG' ((isGrpPullback_pullback F.univ.A c).comp he) he'
  have := hG.separated
  have := hG'.separated
  have v₁ := GlobalTheory.LieVB.isVB_omega G g
  have v₂ := GlobalTheory.LieVB.isVB_omega G' g
  have l₁ : (hodge G g).IsLB := v₁.isLB_det
  have l₂ : (hodge G' g).IsLB := v₂.isLB_det
  have l₃ : (hodge H g).IsLB := (GlobalTheory.LieVB.isVB_omega_of_isGrpPullback h₁ v₁).isLB_det
  have e₁ := (cls_eq_iff (pull_isLB l₁ p) l₃).2 (HodgeGenDesc.lbIso_hodge_pull h₁ v₁)
  have e₂ := (cls_eq_iff (pull_isLB l₂ p') l₃).2 (HodgeGenDesc.lbIso_hodge_pull h₂ v₂)
  have e₃ := (cls_eq_iff (pull_isLB hO π') (isLB_lbPow l₂ N)).2 hiso
  rw [cls_pull l₁] at e₁
  rw [cls_pull l₂] at e₂
  rw [cls_pull hO, cls_lbPow l₂] at e₃
  obtain ⟨d, hd, h⟩ := exists_nsmul_eq_zero hS p (N • cls _ l₁ - pull π (cls _ hO)) (by
    rw [map_sub, map_nsmul, ← pull_comp, hw, pull_comp, e₃, map_nsmul, e₁, e₂, sub_self])
  refine ⟨d, d * N, hd, Nat.mul_pos hd hN,
    (cls_eq_iff (isLB_lbPow l₁ _) (isLB_lbPow (pull_isLB hO π) _)).1 ?_⟩
  rw [cls_lbPow l₁, cls_lbPow (pull_isLB hO π), cls_pull hO, mul_smul, ← sub_eq_zero, ← smul_sub, h]

end GlobalTheory.HodgeMin

end
