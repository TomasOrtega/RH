import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.VeryAmpleMove

variable {k : Type} [CommRing k] {X Y : Scheme.{0}}

/- English proof (translation)
Take `⟨W, hW⟩` from `H`. Take `⟨hcov, hs⟩` from `hs`. Use `choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hL hM (s i)`. Establish `loc : ∀ i, Out.nonzeroLocus (s' i) = ψ ⁻¹ᵁ Out.nonzeroLocus (s i)` using `fun i => by`. Use extensionality with `y`.

Use `(mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (ψ y)).symm)` and prove the remaining obligations. Take `⟨j, hj⟩` from `exists_chart hL (ψ y)`. Establish `e` using `hs' i _ (𝟙 _) y j k hj hk`. Rewrite `e` using `[Category.id_comp, gs_stalkMap ψ y _ hj]`. Conclude with `⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩`.

Take `⟨k, hk⟩` from `exists_chart hM y`. Establish `e` using `hs' i _ (𝟙 _) y j k hj hk`. Rewrite `e` using `[Category.id_comp]`. Conclude with `⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩`. Use `⟨s', ?_, fun i hi => ?_⟩` and prove the remaining obligations.

Simplify using `only [loc]`. Rewrite using `[← Scheme.Hom.preimage_top ψ, ← hcov]`. Simplify using `only [Scheme.Hom.preimage_iSup]`. Take `⟨haff, r, hr, hsurj⟩` from `hs i hi`. Use `⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j), fun j k => fn_ext fun y hy => ?_, ?_⟩` and prove the remaining obligations.

Take `⟨l, hl⟩` from `exists_chart hL (ψ y)`. Establish `hm : ψ y ∈ Out.nonzeroLocus (s i) ⊓ L.U l` using `⟨(loc i).le hy.1, hl⟩`. Establish `e` using `congrArg (gs ψ y _) (hr j l)`. Rewrite `e` using `[gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm]`. Establish `e₁` using `hs' j _ (𝟙 _) y l k hl hy.2`.

Establish `e₂` using `hs' i _ (𝟙 _) y l k hl hy.2`. Rewrite `e₁`, `e₂` using `[Category.id_comp]`. Establish `e₃` using `(gw W (𝟙 _) y l k).mul_right_inj.1 (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))`. Use `(gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp]))) (gs_res _ y _ hy _)))))` and prove the remaining obligations. Establish `hsur` using `VeryAmpleCharts.appLE_surjective (ψ := ψ) _ _ (loc i)`.

Establish `hc : ∀ a, (ψ.appLE _ _ (loc i).le).hom (constFn p (Out.nonzeroLocus (s i)) a) = constFn q (Out.nonzeroLocus (s' i)) a` using `fun a => by`. Substitute `hq` using the available equality. Unfold `constFn`. Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp]`. Use `erw [Scheme.Hom.appLE_comp_appLE]`.

Establish `e` using `congrArg (Subring.map (ψ.appLE _ _ (loc i).le).hom) hsurj`. Rewrite `e` using `[RingHom.map_closure, ← RingHom.range_eq_map, RingHom.range_eq_top.2 hsur, Set.image_union, ← Set.range_comp, ← Set.range_comp]`. Rewrite using `[← e]`. Use `congr 2`. Conclude with `congrArg Set.range (funext fun a => (hc a).symm)`.
-/
theorem immBy_pull {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (ψ : Y ⟶ X) [IsIso ψ] (hq : ψ ≫ p = q) {L : LB X} {M : LB Y}
    (hL : L.IsLB) (hM : M.IsLB) (H : LBIso M (L.pull ψ)) {J : Type} (s : J → L.Sec) (J₀ : Set J)
    (hs : ImmBy p L s J₀) : ∃ t : J → M.Sec, ImmBy q M t J₀ := by
  obtain ⟨W, hW⟩ := H
  obtain ⟨hcov, hs⟩ := hs
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hL hM (s i)
  have loc : ∀ i, Out.nonzeroLocus (s' i) = ψ ⁻¹ᵁ Out.nonzeroLocus (s i) := fun i => by
    ext y
    refine (mem_nonzeroLocus _ y).trans (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩
      (mem_nonzeroLocus _ (ψ y)).symm)
    · obtain ⟨j, hj⟩ := exists_chart hL (ψ y)
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp, gs_stalkMap ψ y _ hj] at e
      exact ⟨j, hj, (isUnit_map_iff (ψ.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
    · obtain ⟨k, hk⟩ := exists_chart hM y
      have e := hs' i _ (𝟙 _) y j k hj hk
      rw [Category.id_comp] at e
      exact ⟨k, hk, isUnit_of_mul_isUnit_right
        ((congrArg IsUnit ((gs_stalkMap ψ y _ hj _).symm.trans e)).mp (u.map _))⟩
  refine ⟨s', ?_, fun i hi => ?_⟩
  · simp only [loc]
    rw [← Scheme.Hom.preimage_top ψ, ← hcov]
    simp only [Scheme.Hom.preimage_iSup]
  obtain ⟨haff, r, hr, hsurj⟩ := hs i hi
  refine ⟨by rw [loc]; exact haff.preimage ψ, fun j => (ψ.appLE _ _ (loc i).le).hom (r j),
    fun j k => fn_ext fun y hy => ?_, ?_⟩
  · obtain ⟨l, hl⟩ := exists_chart hL (ψ y)
    have hm : ψ y ∈ Out.nonzeroLocus (s i) ⊓ L.U l := ⟨(loc i).le hy.1, hl⟩
    have e := congrArg (gs ψ y _) (hr j l)
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm] at e
    have e₁ := hs' j _ (𝟙 _) y l k hl hy.2
    have e₂ := hs' i _ (𝟙 _) y l k hl hy.2
    rw [Category.id_comp] at e₁ e₂
    have e₃ := (gw W (𝟙 _) y l k).mul_right_inj.1
      (e₁.symm.trans (e.trans ((congrArg _ e₂).trans (mul_left_comm _ _ _))))
    refine (gs_res _ y _ hy _).trans (e₃.trans (Eq.symm ((gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_res _ y _ hy _).trans ((gs_appLE ψ _ _ _ (𝟙 _) y hy.1 _).trans (by rw [Category.id_comp])))
      (gs_res _ y _ hy _)))))
  · have hsur := VeryAmpleCharts.appLE_surjective (ψ := ψ) _ _ (loc i)
    have hc : ∀ a, (ψ.appLE _ _ (loc i).le).hom (constFn p (Out.nonzeroLocus (s i)) a) =
        constFn q (Out.nonzeroLocus (s' i)) a := fun a => by
      subst hq
      unfold constFn
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp]
      erw [Scheme.Hom.appLE_comp_appLE]
    have e := congrArg (Subring.map (ψ.appLE _ _ (loc i).le).hom) hsurj
    rw [RingHom.map_closure, ← RingHom.range_eq_map, RingHom.range_eq_top.2 hsur, Set.image_union,
      ← Set.range_comp, ← Set.range_comp] at e
    rw [← e]
    congr 2
    exact congrArg Set.range (funext fun a => (hc a).symm)

/- English proof (translation)
Take `⟨m, s, hcov, hs⟩` from `veryAmple_lbPow hA K P N hN`. Use `⟨m + 1, s, by simpa using hcov, fun i _ => ?_⟩` and prove the remaining obligations. Take `⟨haff, r, hr, hf⟩` from `hs i`. Use `⟨haff, r, hr, top_le_iff.1 fun f _ => ?_⟩` and prove the remaining obligations. Take `⟨F, rfl⟩` from `hf f`.

Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[MvPolynomial.eval₂_C]`. Conclude with `Subring.subset_closure (Or.inl ⟨a, rfl⟩)`. Consider the case `add F G hF hG`.

Rewrite using `[MvPolynomial.eval₂_add]`. Conclude with `add_mem (hF trivial) (hG trivial)`. Consider the case `mul_X F j hF`. Rewrite using `[MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]`. Conclude with `mul_mem (hF trivial) (Subring.subset_closure (Or.inr ⟨j, rfl⟩))`.
-/
theorem immBy_lbPow (hA : Out.AmpleSt) (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : ℕ)
    (hN : 4 ≤ N) : ∃ (m : ℕ) (s : Fin m → (lbPow P.L N).Sec), ImmBy P.A.hom (lbPow P.L N) s Set.univ := by
  obtain ⟨m, s, hcov, hs⟩ := veryAmple_lbPow hA K P N hN
  refine ⟨m + 1, s, by simpa using hcov, fun i _ => ?_⟩
  obtain ⟨haff, r, hr, hf⟩ := hs i
  refine ⟨haff, r, hr, top_le_iff.1 fun f _ => ?_⟩
  obtain ⟨F, rfl⟩ := hf f
  induction F using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂_C]
    exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
  | add F G hF hG =>
    rw [MvPolynomial.eval₂_add]
    exact add_mem (hF trivial) (hG trivial)
  | mul_X F j hF =>
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
    exact mul_mem (hF trivial) (Subring.subset_closure (Or.inr ⟨j, rfl⟩))

/- English proof (translation)
Introduce `hL _ k _ _ Φ N hN P`. Take `⟨m, s, hs⟩` from `immBy_lbPow hL.ample k P.PB N hN`. Establish `: IsIso P.β.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map P.β.hom))`. Take `⟨t, ht⟩` from `immBy_pull P.β.hom.left (Over.w P.β.hom) (DVR.linComb_isLB _ P.PB.isLB _ _) Φ.isLB P.w₀ s _ hs`. Conclude with `⟨m, t, ht⟩`.
-/
theorem exists_immBy_abelianPart : Out.Laws → Out.Laws2 → (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N : ℕ), 4 ≤ N → Φ.Pol N → ∃ (m : ℕ) (t : Fin m → Φ.N₀.Sec), ImmBy Φ.E.B.hom Φ.N₀ t Set.univ) := by
  intro hL _ k _ _ Φ N hN P
  obtain ⟨m, s, hs⟩ := immBy_lbPow hL.ample k P.PB N hN
  have : IsIso P.β.hom.left := inferInstanceAs (IsIso ((Over.forget _).map P.β.hom))
  obtain ⟨t, ht⟩ := immBy_pull P.β.hom.left (Over.w P.β.hom) (DVR.linComb_isLB _ P.PB.isLB _ _) Φ.isLB P.w₀ s _ hs
  exact ⟨m, t, ht⟩

end GlobalTheory.VeryAmpleMove
