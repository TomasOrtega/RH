import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ChartOfPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BOfNsmulLeft
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

/- English proof (translation)
Simplify using `only [gs, dif_pos h, map_sub]`.
-/
theorem gs_sub {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs, dif_pos h, map_sub]

def RepF {k : ℕ} {ρ : D.toPre.X} {m : ℕ}
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))) (c : Fin m → F) : Prop :=
  ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
    sval t (𝟙 _) y J = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J

/- English proof (translation)
Set `bO` to `fun i => pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) (b i) (snd (TO hϖ hv) D.toPre.P.A).left`. Establish `hBO` using `hb (Ov v) (fO v hϖ hv) bO (fun i j => rfl)`. Take `⟨r, hr, -⟩` from `hBO (pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) σ (snd (TO hϖ hv) D.toPre.P.A).left)`. Use `⟨fun i => ιr (v := v) (r i), fun i => v_ιr _, fun y J hJ => ?_⟩` and prove the remaining obligations. Establish `e` using `sval_lin (fun i => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (r i)) bO hr (jO hϖ hv (D := D)).left y hJ`.

Rewrite `e` using `[sval_pullSec _ _ _ _ _ y hJ, jO_snd]`. Rewrite using `[hσF y J hJ, e]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `g` using `gs_jO hϖ hv (D := D) (𝟙 _) y (r i)`. Rewrite `g` using `[Category.id_comp]`.

Rewrite using `[g, hbF i y J hJ]`. Use `show _ * sval (pullSec _ _ _ (b i) _) _ y J = _`. Rewrite using `[sval_pullSec _ _ _ _ _ y hJ, jO_snd]`.
-/
theorem coordsO {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J)
    (σ : D.toPre.SecB k ρ) (σF : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hσF : ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval σF (𝟙 _) y J = sval σ (DegPre.prB D.toPre F).left y J) :
    ∃ c : Fin m → F, (∀ i, (0 : WithTop ℚ) ≤ v (c i)) ∧ RepF bF σF c := by
  let bO := fun i => pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) (b i)
    (snd (TO hϖ hv) D.toPre.P.A).left
  have hBO := hb (Ov v) (fO v hϖ hv) bO (fun i j => rfl)
  obtain ⟨r, hr, -⟩ := hBO (pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) σ
    (snd (TO hϖ hv) D.toPre.P.A).left)
  refine ⟨fun i => ιr (v := v) (r i), fun i => v_ιr _, fun y J hJ => ?_⟩
  have e := sval_lin (fun i => (fst (TO hϖ hv) D.toPre.P.A).left.appTop.hom (r i)) bO hr (jO hϖ hv (D := D)).left y hJ
  rw [sval_pullSec _ _ _ _ _ y hJ, jO_snd] at e
  rw [hσF y J hJ, e]
  refine Finset.sum_congr rfl fun i _ => ?_
  have g := gs_jO hϖ hv (D := D) (𝟙 _) y (r i)
  rw [Category.id_comp] at g
  rw [g, hbF i y J hJ]
  show _ * sval (pullSec _ _ _ (b i) _) _ y J = _
  rw [sval_pullSec _ _ _ _ _ y hJ, jO_snd]

/- English proof (translation)
Apply the tactic sequence `have hsub : ∀ (y : (DegPre.BF D.toPre F).left) (a b : Γ((DegPre.BF D.toPre F).left, ⊤)), gs (𝟙 _) y ⊤ (a - b) = gs (𝟙 _) y ⊤ a - gs (𝟙 _) y ⊤ b := fun y a b => gs_sub _ y ⊤ (by first | trivial | simp) a b`. Establish `h0` using `hU (c - c') (fun y J hy => by`. Establish `e1` using `h y J hy`. Establish `e2` using `h' y J hy`. Simplify using `only [Pi.sub_apply, map_sub, hsub, sub_mul, Finset.sum_sub_distrib]`.

Rewrite using `[← e1, ← e2, sub_self])`. Conclude with `sub_eq_zero.mp h0`.
-/
theorem repF_unique {k : ℕ} {ρ : D.toPre.X} {m : ℕ}
    {bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))}
    (hU : ∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0)
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))} {c c' : Fin m → F}
    (h : RepF bF t c) (h' : RepF bF t c') : c = c' := by
  have hsub : ∀ (y : (DegPre.BF D.toPre F).left) (a b : Γ((DegPre.BF D.toPre F).left, ⊤)),
      gs (𝟙 _) y ⊤ (a - b) = gs (𝟙 _) y ⊤ a - gs (𝟙 _) y ⊤ b :=
    fun y a b => gs_sub _ y ⊤ (by first | trivial | simp) a b
  have h0 := hU (c - c') (fun y J hy => by
    have e1 := h y J hy
    have e2 := h' y J hy
    simp only [Pi.sub_apply, map_sub, hsub, sub_mul, Finset.sum_sub_distrib]
    rw [← e1, ← e2, sub_self])
  exact sub_eq_zero.mp h0

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
