import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisLineBundleSectionsProjectiveOverDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.KerGermInj

open GlobalTheory.AbLaw

/- English proof (translation)
Rewrite using `[gs_eq _ y O hy]`. Both sides reduce to the same expression.
-/
theorem gs_id {P : Scheme.{0}} (O : P.Opens) (y : P) (hy : y ∈ O) (a : Γ(P, O)) :
    gs (𝟙 P) y O a = (P.presheaf.germ O y hy).hom a := by
  rw [gs_eq _ y O hy]; rfl

/- English proof (translation)
Rewrite using `[← gs_pull f h z U hU, gs_eq f z (h ⁻¹ᵁ U) hU, gs_eq h (f z) U hU]`. Conclude with `(Scheme.Hom.germ_stalkMap_apply f (h ⁻¹ᵁ U) z hU _).symm`.
-/
theorem gs_comp {Y Z X : Scheme.{0}} (f : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (f z) ∈ U)
    (a : Γ(X, U)) : gs (f ≫ h) z U a = (f.stalkMap z).hom (gs h (f z) U a) := by
  rw [← gs_pull f h z U hU, gs_eq f z (h ⁻¹ᵁ U) hU, gs_eq h (f z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply f (h ⁻¹ᵁ U) z hU _).symm

/- English proof (translation)
Apply `ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]`. Use extensionality with `r`. Simplify using `[GlobalTheory.FormsLocus.cstT]`.
-/
theorem fromSpecStalk_comp {R : Type} [CommRing R] {T : Scheme.{0}} (t : T ⟶ Sp R) (x : T) :
    T.fromSpecStalk x ≫ t =
      Spec.map (CommRingCat.ofHom ((T.presheaf.germ ⊤ x trivial).hom.comp (GlobalTheory.FormsLocus.cstT t))) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.FormsLocus.cstT]

/- English proof (translation)
Introduce `R _ X T X' f M Q t φ p hpb e he hz`. Use function extensionality and compare the values at `k`. Apply `TopCat.Presheaf.section_ext T.sheaf ⊤` to reduce the goal to its premises. Introduce `x hx`. Express the relevant statement in the definitionally equal form `(T.presheaf.germ ⊤ x hx).hom (e k) = (T.presheaf.germ ⊤ x hx).hom 0`.

Rewrite using `[map_zero]`. Set `ψ : Γ(T, ⊤) →+* T.presheaf.stalk x` to `(T.presheaf.germ ⊤ x hx).hom`. Set `ρ : R →+* T.presheaf.stalk x` to `ψ.comp (GlobalTheory.FormsLocus.cstT t)`. Set `g` to `T.fromSpecStalk x`. Set `fst` to `pullback.fst p g`.

Set `snd` to `pullback.snd p g`. Set `π` to `fst ≫ φ`. Establish `hsq : IsPullback π snd f (Spec.map (CommRingCat.ofHom ρ))`. Establish `hg : g ≫ t = Spec.map (CommRingCat.ofHom ρ)` using `fromSpecStalk_comp t x`. Establish `h3` using `(IsPullback.of_hasPullback p g).paste_horiz hpb`.

Rewrite `h3` using `[hg]`. Conclude with `h3`. Take `⟨E, hE⟩` from `Q.sec _ ρ _ π snd hsq`. Establish `hv : (Q.D₀.map ρ).mulVec (fun k => ψ (e k)) = 0`. Use function extensionality and compare the values at `j`.

Establish `h1` using `RingHom.map_mulVec ψ (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)) e j`. Rewrite `h1` using `[he, Pi.zero_apply, map_zero, Matrix.map_map]`. Conclude with `h1.symm`. Establish `hloc : ∀ w : {v : Fin Q.a → T.presheaf.stalk x // (Q.D₀.map ρ).mulVec v = 0}, (∀ i, ∑ k, cst snd (π ⁻¹ᵁ Q.W i) (w.1 k) * (π.app (Q.W i)).hom (Q.u k i) = 0) → E w = 0`. Use `by`.

Introduce `w hw`. Establish `hcov : ⨆ i, π ⁻¹ᵁ Q.W i = ⊤` using `Q.iSup_preimage (π := π)`. Use `sec_eq_zero_of_local (L := M.pull π) (fun i => π ⁻¹ᵁ Q.W i) hcov (fun i => (fun _ => Q.ch i : (M.pull π).ι)) (fun i => le_pull M π (Q.le i)) (E w) ?_` and prove the remaining obligations. Introduce `i`. Conclude with `(hE w i).trans (hw i)`.

Establish `h0 : E ⟨0, by rw [Matrix.mulVec_zero]⟩ = 0` using `hloc _ fun i => Finset.sum_eq_zero fun k _ => by`. Establish `hc0 : cst snd (π ⁻¹ᵁ Q.W i) 0 = 0` using `map_zero _`. Conclude with `(congrArg (· * _) hc0).trans (zero_mul _)`. Establish `h1 : E ⟨fun k => ψ (e k), hv⟩ = 0`. Use `hloc _ fun i => ?_` and prove the remaining obligations.

Apply `fn_ext` to reduce the goal to its premises. Introduce `y hy`. Establish `hyi : φ (fst y) ∈ Q.W i` using `hy`. Rewrite using `[gs_id _ y hy, gs_id _ y hy, map_zero, map_sum]`. Simplify using `only [map_mul]`.

Establish `hu : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom ((π.app (Q.W i)).hom (Q.u k i)) = (fst.stalkMap y).hom (gs φ (fst y) (Q.W i) (Q.u k i))`. Introduce `k`. Rewrite using `[← gs_id _ y hy, gs_pull (𝟙 _) π y (Q.W i) hyi, Category.id_comp]`. Conclude with `gs_comp fst φ y (Q.W i) hyi _`. Establish `hc : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom (cst snd (π ⁻¹ᵁ Q.W i) (ψ (e k))) = (fst.stalkMap y).hom (gs p (fst y) ⊤ (e k))`.

Introduce `k`. Establish `hcond : fst ≫ p = snd ≫ g` using `pullback.condition`. Establish `hA` using `congrArg (fun h => h.hom (e k)) (Scheme.fromSpecStalk_appTop (X := T) (x := x))`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at hA`. Rewrite using `[← gs_id _ y hy, ← gs_comp fst p y ⊤ trivial, hcond]`.

Use `Eq.trans ?_ (gs_pull snd g y ⊤ trivial (e k))` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (gs snd y (g ⁻¹ᵁ ⊤)) hA.symm)` and prove the remaining obligations. Use `Eq.trans ?_ (gs_res snd y _ (show snd y ∈ g ⁻¹ᵁ ⊤ from trivial) _).symm` and prove the remaining obligations. Use `Eq.trans (gs_res (𝟙 _) y le_top hy _) ?_` and prove the remaining obligations. Use `Eq.trans (gs_pull (𝟙 _) snd y ⊤ trivial _) ?_` and prove the remaining obligations.

Rewrite using `[Category.id_comp]`. Both sides reduce to the same expression. Establish `hsum : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom (cst snd (π ⁻¹ᵁ Q.W i) (ψ (e k))) * ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom ((π.app (Q.W i)).hom (Q.u k i)) = (fst.stalkMap y).hom (gs p (fst y) ⊤ (e k) * gs φ (fst y) (Q.W i) (Q.u k i))` using `fun k => by`. Rewrite using `[hc k, hu k, map_mul]`. Simplify using `only [hsum]`.

Rewrite using `[← map_sum, hz (fst y) i hyi, map_zero]`. Establish `h2` using `congrFun (congrArg Subtype.val (E.injective (h1.trans h0.symm))) k`. Conclude with `h2`.
-/
theorem eq_zero : ∀ (R : Type) [CommRing R] (X T X' : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (Q : GlobalTheory.AbLaw.Perf f M) (t : T ⟶ Sp R) (φ : X' ⟶ X) (p : X' ⟶ T), IsPullback φ p f t → ∀ e : Fin Q.a → Γ(T, ⊤), (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)).mulVec e = 0 → (∀ (z : X') (i : Q.I), φ z ∈ Q.W i → ∑ k, gs p z ⊤ (e k) * gs φ z (Q.W i) (Q.u k i) = 0) → e = 0 := by
  intro R _ X T X' f M Q t φ p hpb e he hz
  funext k
  apply TopCat.Presheaf.section_ext T.sheaf ⊤
  intro x hx
  change (T.presheaf.germ ⊤ x hx).hom (e k) = (T.presheaf.germ ⊤ x hx).hom 0
  rw [map_zero]
  let ψ : Γ(T, ⊤) →+* T.presheaf.stalk x := (T.presheaf.germ ⊤ x hx).hom
  let ρ : R →+* T.presheaf.stalk x := ψ.comp (GlobalTheory.FormsLocus.cstT t)
  let g := T.fromSpecStalk x
  let fst := pullback.fst p g
  let snd := pullback.snd p g
  let π := fst ≫ φ
  have hsq : IsPullback π snd f (Spec.map (CommRingCat.ofHom ρ)) := by
    have hg : g ≫ t = Spec.map (CommRingCat.ofHom ρ) := fromSpecStalk_comp t x
    have h3 := (IsPullback.of_hasPullback p g).paste_horiz hpb
    rw [hg] at h3
    exact h3
  obtain ⟨E, hE⟩ := Q.sec _ ρ _ π snd hsq
  have hv : (Q.D₀.map ρ).mulVec (fun k => ψ (e k)) = 0 := by
    funext j
    have h1 := RingHom.map_mulVec ψ (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)) e j
    rw [he, Pi.zero_apply, map_zero, Matrix.map_map] at h1
    exact h1.symm
  have hloc : ∀ w : {v : Fin Q.a → T.presheaf.stalk x // (Q.D₀.map ρ).mulVec v = 0},
      (∀ i, ∑ k, cst snd (π ⁻¹ᵁ Q.W i) (w.1 k) * (π.app (Q.W i)).hom (Q.u k i) = 0) → E w = 0 :=
by
    intro w hw
    have hcov : ⨆ i, π ⁻¹ᵁ Q.W i = ⊤ := Q.iSup_preimage (π := π)
    refine sec_eq_zero_of_local (L := M.pull π) (fun i => π ⁻¹ᵁ Q.W i) hcov
      (fun i => (fun _ => Q.ch i : (M.pull π).ι)) (fun i => le_pull M π (Q.le i)) (E w) ?_
    intro i
    exact (hE w i).trans (hw i)
  have h0 : E ⟨0, by rw [Matrix.mulVec_zero]⟩ = 0 :=
    hloc _ fun i => Finset.sum_eq_zero fun k _ => by
      have hc0 : cst snd (π ⁻¹ᵁ Q.W i) 0 = 0 := map_zero _
      exact (congrArg (· * _) hc0).trans (zero_mul _)
  have h1 : E ⟨fun k => ψ (e k), hv⟩ = 0 := by
    refine hloc _ fun i => ?_
    apply fn_ext
    intro y hy
    have hyi : φ (fst y) ∈ Q.W i := hy
    rw [gs_id _ y hy, gs_id _ y hy, map_zero, map_sum]
    simp only [map_mul]
    have hu : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom ((π.app (Q.W i)).hom (Q.u k i)) =
        (fst.stalkMap y).hom (gs φ (fst y) (Q.W i) (Q.u k i)) := by
      intro k
      rw [← gs_id _ y hy, gs_pull (𝟙 _) π y (Q.W i) hyi, Category.id_comp]
      exact gs_comp fst φ y (Q.W i) hyi _
    have hc : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom (cst snd (π ⁻¹ᵁ Q.W i) (ψ (e k))) =
        (fst.stalkMap y).hom (gs p (fst y) ⊤ (e k)) := by
      intro k
      have hcond : fst ≫ p = snd ≫ g := pullback.condition
      have hA := congrArg (fun h => h.hom (e k)) (Scheme.fromSpecStalk_appTop (X := T) (x := x))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hA
      rw [← gs_id _ y hy, ← gs_comp fst p y ⊤ trivial, hcond]
      refine Eq.trans ?_ (gs_pull snd g y ⊤ trivial (e k))
      refine Eq.trans ?_ (congrArg (gs snd y (g ⁻¹ᵁ ⊤)) hA.symm)
      refine Eq.trans ?_ (gs_res snd y _ (show snd y ∈ g ⁻¹ᵁ ⊤ from trivial) _).symm
      refine Eq.trans (gs_res (𝟙 _) y le_top hy _) ?_
      refine Eq.trans (gs_pull (𝟙 _) snd y ⊤ trivial _) ?_
      rw [Category.id_comp]
      rfl
    have hsum : ∀ k, ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom (cst snd (π ⁻¹ᵁ Q.W i) (ψ (e k))) *
        ((pullback p g).presheaf.germ (π ⁻¹ᵁ Q.W i) y hy).hom ((π.app (Q.W i)).hom (Q.u k i)) =
        (fst.stalkMap y).hom (gs p (fst y) ⊤ (e k) * gs φ (fst y) (Q.W i) (Q.u k i)) := fun k => by
      rw [hc k, hu k, map_mul]
    simp only [hsum]
    rw [← map_sum, hz (fst y) i hyi, map_zero]
  have h2 := congrFun (congrArg Subtype.val (E.injective (h1.trans h0.symm))) k
  exact h2

end GlobalTheory.KerGermInj
