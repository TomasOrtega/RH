import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.WtLin

/- English proof (translation)
Set `e` to `RingEquiv.ofBijective _ hb`. Establish `h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x` using `fun x => by`. Rewrite using `[RingEquiv.symm_apply_eq]`. Express the relevant statement in the definitionally equal form `_ = AddMonoidAlgebra.liftNCRingHom f g hc _`. Simplify using `[AddMonoidAlgebra.liftNCRingHom]`.

Express the relevant statement in the definitionally equal form `(e.symm _).coeff χ = ∑ i, c i * (e.symm (s i)).coeff χ`. Simplify using `[map_sum, map_mul, h1]`.
-/
theorem coeff_symm_sum {A B X : Type} [CommRing A] [CommRing B] [AddCommGroup X] (f : A →+* B)
    (g : Multiplicative X →* B) (hc : ∀ x y, Commute (f x) (g y))
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g hc)) {J : Type} [Fintype J]
    (c : J → A) (s : J → B) (χ : X) :
    ((Equiv.ofBijective _ hb).symm (∑ i, f (c i) * s i)).coeff χ =
      ∑ i, c i * ((Equiv.ofBijective _ hb).symm (s i)).coeff χ := by
  let e := RingEquiv.ofBijective _ hb
  have h1 : ∀ x, e.symm (f x) = AddMonoidAlgebra.single 0 x := fun x => by
    rw [RingEquiv.symm_apply_eq]
    change _ = AddMonoidAlgebra.liftNCRingHom f g hc _
    simp [AddMonoidAlgebra.liftNCRingHom]
  change (e.symm _).coeff χ = ∑ i, c i * (e.symm (s i)).coeff χ
  simp [map_sum, map_mul, h1]

/- English proof (translation)
Substitute `hf` using the available equality. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)) (Scheme.Hom.appLE_comp_appLE f q ⊤ U _ (fun _ _ => trivial) le_rfl)`.
-/
theorem app_constFn {R : Type} [CommRing R] {X Y : Scheme.{0}} (q : X ⟶ Sp R) (q' : Y ⟶ Sp R) (f : Y ⟶ X)
    (hf : f ≫ q = q') (U : X.Opens) (a : R) :
    (f.app U).hom (constFn q U a) = constFn q' (f ⁻¹ᵁ U) a := by
  subst hf
  rw [Scheme.Hom.app_eq_appLE]
  exact congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (Scheme.Hom.appLE_comp_appLE f q ⊤ U _ (fun _ _ => trivial) le_rfl)

/- English proof (translation)
Use `Eq.trans ?_ (coeff_symm_sum _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) (fun i => constFn Φ.E.B.hom _ (a i)) (fun i => (F i).f l) α)` and prove the remaining obligations. Simplify using `only [app_constFn _ _ _ (Over.w Φ.D.q)]`. Both sides reduce to the same expression.
-/
theorem weight_sum {k : Type} [Field k] (Φ : FibPre k) {d : ℕ} {J : Type} [Fintype J]
    (F : J → (Φ.H d).Sec) (a : J → k) (α : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α
        (∑ i, constFn Φ.G.hom ((Φ.H d).U l) (a i) * (F i).f l : Γ(Φ.G.left, (Φ.H d).U l)) =
      ∑ i, constFn Φ.E.B.hom _ (a i) * Φ.wt (F i) α l := by
  refine Eq.trans ?_ (coeff_symm_sum _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l))
    (fun i => constFn Φ.E.B.hom _ (a i)) (fun i => (F i).f l) α)
  simp only [app_constFn _ _ _ (Over.w Φ.D.q)]
  rfl

/- English proof (translation)
Use `coeff_symm_sum _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) (J := Empty) Empty.elim Empty.elim α` as an intermediate fact. Simplify `this` using `[SplitExt.GtDatum.weight]`.
-/
theorem weight_zero {k : Type} [Field k] (Φ : FibPre k) (α : Φ.E.X) (l : Φ.N₀.ι) :
    Φ.D.weight (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l) α 0 = 0 := by
  have := coeff_symm_sum _ _ _ (Φ.D.coord (Φ.ch l) _ (Φ.aff l) (Φ.le l)) (J := Empty)
    Empty.elim Empty.elim α
  simpa [SplitExt.GtDatum.weight] using this

/- English proof (translation)
Introduce `k _ Φ N q J _ cls F hG a ha`. Use function extensionality and compare the values at `i₀`. Establish `key` using `hG.inj (cls i₀) (hG.short i₀) (fun i => if ∃ m, cls i₀ = cls i + N • m then a i else 0) (fun i hi => by`. Assume the negation of the conclusion as `h`. Conclude with `hi (if_neg h))`.

Use the proof step `(fun l => by`. Establish `h` using `weight_sum Φ F a (cls i₀) l`. Rewrite `h` using `[ha l]`. Use `Eq.trans ?_ (h.symm.trans (weight_zero Φ _ l))` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `split_ifs with hi`. Both sides reduce to the same expression. Establish `h0 : Φ.wt (F i) (cls i₀) l = 0`. Assume the negation of the conclusion as `hne`. Conclude with `hi (hG.supp i _ ⟨l, hne⟩).2`.

Rewrite using `[h0, mul_zero, mul_zero])`. Use `congrFun key i₀` as an intermediate fact. Rewrite `this` using `[if_pos ⟨0, by simp⟩]`. Then use the resulting hypothesis.
-/
theorem linIndep : (∀ (k : Type) [Field k] (Φ : FibPre k) (N : ℕ) (q : QuadraticMap ℤ Φ.E.X ℝ) (J : Type) [Fintype J] (cls : J → Φ.E.X) (F : J → (Φ.H 1).Sec), Φ.Good N q cls F → ∀ a : J → k, (∀ l, ∑ i, constFn Φ.G.hom ((Φ.H 1).U l) (a i) * (F i).f l = 0) → a = 0) := by
  intro k _ Φ N q J _ cls F hG a ha
  classical
  funext i₀
  have key := hG.inj (cls i₀) (hG.short i₀)
    (fun i => if ∃ m, cls i₀ = cls i + N • m then a i else 0)
    (fun i hi => by
      by_contra h
      exact hi (if_neg h))
    (fun l => by
      have h := weight_sum Φ F a (cls i₀) l
      rw [ha l] at h
      refine Eq.trans ?_ (h.symm.trans (weight_zero Φ _ l))
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hi
      · rfl
      · have h0 : Φ.wt (F i) (cls i₀) l = 0 := by
          by_contra hne
          exact hi (hG.supp i _ ⟨l, hne⟩).2
        rw [h0, mul_zero, mul_zero])
  have := congrFun key i₀
  rwa [if_pos ⟨0, by simp⟩] at this

end GlobalTheory.ZH.WtLin
end
