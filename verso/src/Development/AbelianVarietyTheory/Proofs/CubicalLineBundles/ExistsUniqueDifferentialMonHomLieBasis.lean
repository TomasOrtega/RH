import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqOfLieBasisComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM.DiffCoord

variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G']

/- English proof (translation)
Unfold `IsTangent at hv ⊢`. Rewrite using `[Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]`.
-/
theorem isTangent_comp_hom (f : G ⟶ G') [IsMonHom f] {v : epsR R ⟶ G} (hv : IsTangent v) : IsTangent (v ≫ f) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

/- English proof (translation)
Take `⟨u, hu, rfl⟩` from `h`. Use `⟨fun i => u i ≫ f, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Over.comp_left, Over.comp_left, hu, Category.assoc]`. Conclude with `(map_list_prod (IsMonHom.monoidHom f (epsR R)) (List.ofFn u)).trans (by rw [List.map_ofFn]; rfl)`.
-/
theorem isLieComb_comp_hom (f : G ⟶ G') [IsMonHom f] {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G)}
    {w : epsR R ⟶ G} (h : IsLieComb c v w) : IsLieComb c (fun i => v i ≫ f) (w ≫ f) := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu, Category.assoc]
  · exact (map_list_prod (IsMonHom.monoidHom f (epsR R)) (List.ofFn u)).trans (by rw [List.map_ofFn]; rfl)

/- English proof (translation)
Use `choose A hA using fun i => (hv'.2 _ (isTangent_comp_hom f (hv.1 i))).exists`. Use `⟨Fintype.linearCombination R A, fun c w h => ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearCombination_apply]`. Conclude with `(LieComb.lieComb_algebra R G' m v' hv'.1).2.2.1 n A _ c _ hA (isLieComb_comp_hom f h)`.
-/
theorem exists_linearMap [IsCommMonObj G'] (f : G ⟶ G') [IsMonHom f] {n m : ℕ} {v : Fin n → (epsR R ⟶ G)}
    {v' : Fin m → (epsR R ⟶ G')} (hv : IsLieBasis v) (hv' : IsLieBasis v') :
    ∃ M : (Fin n → R) →ₗ[R] (Fin m → R), ∀ c w, IsLieComb c v w → IsLieComb (M c) v' (w ≫ f) := by
  choose A hA using fun i => (hv'.2 _ (isTangent_comp_hom f (hv.1 i))).exists
  refine ⟨Fintype.linearCombination R A, fun c w h => ?_⟩
  rw [Fintype.linearCombination_apply]
  exact (LieComb.lieComb_algebra R G' m v' hv'.1).2.2.1 n A _ c _ hA (isLieComb_comp_hom f h)

/- English proof (translation)
Introduce `K _ _ P F P' F' f hf`. Take `⟨f₀, hf₀, e⟩` from `DerivZero.exists_lift_isMonHom F.fib.2.1 F'.fib.2.1 f`. Use `F'.P₀.isAb.comm` as an intermediate fact. Take `⟨M, hM⟩` from `exists_linearMap f₀ F.basis F'.basis`. Establish `hd : F.IsDiffOf F' f M`.

Introduce and unpack `u c ⟨hu, w, hw, hc⟩`. Use `⟨isTangent_comp_hom f hu, w ≫ f₀, ?_, hM c w hc⟩` and prove the remaining obligations. Unfold `IsVecOver at hw ⊢`. Rewrite using `[Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, hw, Category.assoc]`. Establish `hcoord : ∀ u c c', F'.IsCoord u c → F'.IsCoord u c' → c = c'`.

Introduce and unpack `u c c' ⟨-, w, hw, hc⟩ ⟨-, w', hw', hc'⟩`. Take `rfl : w = w'` from `Over.OverMorphism.ext (F'.fib.2.1.1.hom_ext (hw.trans hw'.symm) ((Over.w _).trans (Over.w _).symm))`. Conclude with `(F'.basis.2 w ((LieComb.lieComb_algebra K _ _ F'.v F'.basis.1).2.1 c w hc)).unique hc hc'`. Establish `huniq : ∀ N, F.IsDiffOf F' f N → N = M` using `fun N hN => by`. Use `LinearMap.ext_on (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).2 fun c hc => ?_` and prove the remaining obligations.

Use `Submodule.span_induction (p := fun c _ => N c = M c) ?_ ?_ ?_ ?_ hc` and prove the remaining obligations. Introduce and unpack `c ⟨u, hu⟩`. Conclude with `hcoord _ _ _ (hN u c hu) (hd u c hu)`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`.

Rewrite using `[map_add, map_add, hx, hy]`. Introduce `r x _ hx`. Rewrite using `[← algebraMap_smul K r x, map_smul, map_smul, hx]`. Use `⟨⟨M, hd, huniq⟩, f₀, hf₀, e, fun N hN => ?_⟩` and prove the remaining obligations. Rewrite using `[huniq N hN]`.

Conclude with `hM`.
-/
theorem existsUnique_isDiffOf : ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P)
    (P' : Out.PolAV (Sp (𝓞 K))) (F' : GenFib P') (f : P.A ⟶ P'.A), IsMonHom f → (∃! M, F.IsDiffOf F' f M) ∧
    ∃ f₀ : F.P₀.A ⟶ F'.P₀.A, IsMonHom f₀ ∧ f₀.left ≫ F'.φ = F.φ ≫ f.left ∧
      ∀ M, F.IsDiffOf F' f M → ∀ c w, IsLieComb c F.v w → IsLieComb (M c) F'.v (w ≫ f₀) := by
  intro K _ _ P F P' F' f hf
  obtain ⟨f₀, hf₀, e⟩ := DerivZero.exists_lift_isMonHom F.fib.2.1 F'.fib.2.1 f
  have := F'.P₀.isAb.comm
  obtain ⟨M, hM⟩ := exists_linearMap f₀ F.basis F'.basis
  have hd : F.IsDiffOf F' f M := by
    rintro u c ⟨hu, w, hw, hc⟩
    refine ⟨isTangent_comp_hom f hu, w ≫ f₀, ?_, hM c w hc⟩
    unfold IsVecOver at hw ⊢
    rw [Over.comp_left, Over.comp_left, Category.assoc, e, ← Category.assoc, hw, Category.assoc]
  have hcoord : ∀ u c c', F'.IsCoord u c → F'.IsCoord u c' → c = c' := by
    rintro u c c' ⟨-, w, hw, hc⟩ ⟨-, w', hw', hc'⟩
    obtain rfl : w = w' := Over.OverMorphism.ext (F'.fib.2.1.1.hom_ext (hw.trans hw'.symm) ((Over.w _).trans (Over.w _).symm))
    exact (F'.basis.2 w ((LieComb.lieComb_algebra K _ _ F'.v F'.basis.1).2.1 c w hc)).unique hc hc'
  have huniq : ∀ N, F.IsDiffOf F' f N → N = M := fun N hN => by
    refine LinearMap.ext_on (GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K P F).2 fun c hc => ?_
    refine Submodule.span_induction (p := fun c _ => N c = M c) ?_ ?_ ?_ ?_ hc
    · rintro c ⟨u, hu⟩
      exact hcoord _ _ _ (hN u c hu) (hd u c hu)
    · simp
    · intro x y _ _ hx hy
      rw [map_add, map_add, hx, hy]
    · intro r x _ hx
      rw [← algebraMap_smul K r x, map_smul, map_smul, hx]
  refine ⟨⟨M, hd, huniq⟩, f₀, hf₀, e, fun N hN => ?_⟩
  rw [huniq N hN]
  exact hM

end GlobalTheory.CM.DiffCoord
