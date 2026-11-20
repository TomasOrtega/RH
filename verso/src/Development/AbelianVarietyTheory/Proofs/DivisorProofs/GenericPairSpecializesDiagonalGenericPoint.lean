import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagCommonClosedPointOfGeneric
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

/- English proof (translation)
Introduce `F _ Y K _ ψ₁ ψ₂ hG`. Take `⟨hF, V, v₁, v₂, e₁, e₂, e₃, e₄⟩` from `hG`. Establish `hs : (ratOf Y).pt ≫ Y.str = spMap (algebraMap F Y.Fn)` using `(ratOf Y).pt_s`. Establish `k : ∀ ψ : Y.Fn →+* K, (spMap ψ ≫ (ratOf Y).pt) ≫ Y.str = spMap (ψ.comp (algebraMap F Y.Fn))` using `fun ψ => (Category.assoc (spMap ψ) (ratOf Y).pt Y.str).trans ((congrArg (fun g => spMap ψ ≫ g) hs).trans (by rw [← Spec.map_comp]; rfl))`. Establish `h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str`.

Rewrite using `[k, k, hF]`. Use `⟨h, ?_⟩` and prove the remaining obligations. Use `haveI : IsDominant (spMap (algebraMap V K)) := by`. Use `⟨?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `DenseRange (PrimeSpectrum.comap (algebraMap V K))`.

Rewrite using `[PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical, (RingHom.injective_iff_ker_eq_bot _).mp (show Function.Injective (algebraMap V K) from Subtype.val_injective)]`. Conclude with `bot_le`. Establish `hv : v₁ ≫ Y.str = v₂ ≫ Y.str`. Use `ext_of_isDominant (spMap (algebraMap V K)) ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Category.assoc, e₁, e₂]`.

Conclude with `h`. Set `v` to `Limits.pullback.lift v₁ v₂ hv`. Establish `hgen : spMap (algebraMap V K) ≫ v = Limits.pullback.lift (f` using `Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by`. Apply `Limits.pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [v, Category.assoc, Limits.pullback.lift_fst]`.

Conclude with `e₁.trans (Limits.pullback.lift_fst _ _ _).symm`. Simplify using `only [v, Category.assoc, Limits.pullback.lift_snd]`. Conclude with `e₂.trans (Limits.pullback.lift_snd _ _ _).symm`. Establish `hres : spMap (IsLocalRing.residue V) ≫ v = (spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str`. Apply `Limits.pullback.hom_ext` to reduce the goal to its premises.

Simplify using `only [v, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]`. Simplify using `only [v, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id]`. Conclude with `e₃.symm`. Establish `hsp` using `ClosedPt.gen_specializes v (IsLocalRing.closedPoint K)`. Rewrite `hsp` using `[hgen]`.

Establish `hc : v (IsLocalRing.closedPoint V) = Limits.pullback.diagonal Y.str (genericPoint Y.X)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hres]`. Use `_ = Limits.pullback.diagonal Y.str ((spMap (IsLocalRing.residue V) ≫ v₁) (IsLocalRing.closedPoint _)) := Scheme.Hom.comp_apply _ _ _`. Use `_ = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by rw [ClosedPt.closedPt_comp v₁, e₄]`.

Rewrite `hsp` using `[hc]`. Conclude with `hsp`.
-/
theorem genPair_specializes_diagonal : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] (ψ₁ ψ₂ : Y.Fn →+* K),
    GenPair Y ψ₁ ψ₂ → ∃ h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str,
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h
        (IsLocalRing.closedPoint K) ⤳ Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
  intro F _ Y K _ ψ₁ ψ₂ hG
  obtain ⟨hF, V, v₁, v₂, e₁, e₂, e₃, e₄⟩ := hG
  have hs : (ratOf Y).pt ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have k : ∀ ψ : Y.Fn →+* K, (spMap ψ ≫ (ratOf Y).pt) ≫ Y.str = spMap (ψ.comp (algebraMap F Y.Fn)) :=
    fun ψ => (Category.assoc (spMap ψ) (ratOf Y).pt Y.str).trans
      ((congrArg (fun g => spMap ψ ≫ g) hs).trans (by rw [← Spec.map_comp]; rfl))
  have h : (spMap ψ₁ ≫ (ratOf Y).pt) ≫ Y.str = (spMap ψ₂ ≫ (ratOf Y).pt) ≫ Y.str := by
    rw [k, k, hF]
  refine ⟨h, ?_⟩
  haveI : IsDominant (spMap (algebraMap V K)) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap V K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).mp (show Function.Injective (algebraMap V K) from Subtype.val_injective)]
    exact bot_le
  have hv : v₁ ≫ Y.str = v₂ ≫ Y.str := by
    refine ext_of_isDominant (spMap (algebraMap V K)) ?_
    rw [← Category.assoc, ← Category.assoc, e₁, e₂]
    exact h
  let v := Limits.pullback.lift v₁ v₂ hv
  have hgen : spMap (algebraMap V K) ≫ v =
      Limits.pullback.lift (f := Y.str) (g := Y.str) (spMap ψ₁ ≫ (ratOf Y).pt) (spMap ψ₂ ≫ (ratOf Y).pt) h := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst]; exact e₁.trans (Limits.pullback.lift_fst _ _ _).symm
    · simp only [v, Category.assoc, Limits.pullback.lift_snd]; exact e₂.trans (Limits.pullback.lift_snd _ _ _).symm
  have hres : spMap (IsLocalRing.residue V) ≫ v =
      (spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str := by
    apply Limits.pullback.hom_ext
    · simp only [v, Category.assoc, Limits.pullback.lift_fst, Limits.pullback.diagonal_fst, Category.comp_id]
    · simp only [v, Category.assoc, Limits.pullback.lift_snd, Limits.pullback.diagonal_snd, Category.comp_id]
      exact e₃.symm
  have hsp := ClosedPt.gen_specializes v (IsLocalRing.closedPoint K)
  rw [hgen] at hsp
  have hc : v (IsLocalRing.closedPoint V) = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by
    calc v (IsLocalRing.closedPoint V) = (spMap (IsLocalRing.residue V) ≫ v) (IsLocalRing.closedPoint _) :=
          (ClosedPt.closedPt_comp v).symm
      _ = ((spMap (IsLocalRing.residue V) ≫ v₁) ≫ Limits.pullback.diagonal Y.str) (IsLocalRing.closedPoint _) := by
          rw [hres]
      _ = Limits.pullback.diagonal Y.str ((spMap (IsLocalRing.residue V) ≫ v₁) (IsLocalRing.closedPoint _)) :=
          Scheme.Hom.comp_apply _ _ _
      _ = Limits.pullback.diagonal Y.str (genericPoint Y.X) := by rw [ClosedPt.closedPt_comp v₁, e₄]
  rw [hc] at hsp
  exact hsp

end GlobalTheory.FlagPush
