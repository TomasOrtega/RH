import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCover
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTestRingInjective
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ValuesAlgIffValuesUnitOfNe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetIntegralOfDefinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtRedPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverSec

section Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameLift
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n) {S : Type} [CommRing S] [Algebra c.F S]
  [Algebra d.c₂.F S]

/- English proof (translation)
Establish `hc' : ∀ τ a, algebraMap d.c₂.F S (embK d.c₂ τ a) = algebraMap c.F S (embK c τ a)` using `fun τ a => by`. Rewrite using `[← embK_eF d, hc]`. Establish `e : y₂.x ≫ d.r = y₂.x ≫ d.r` using `rfl`. Take `⟨w, hw, hw', -⟩` from `d.m.lin`. Take `⟨p, k, p₁, p₂, hk, hk'⟩` from `exists_pm_iso d.m e`.

Establish `hL` using `Xo.univ.t.PP.isLB`. Establish `hL₂` using `d.Xo₂.univ.t.PP.isLB`. Take `⟨s, hs⟩` from `exists_up hL hL₂ hw p₁ hk hk' y₂.s`. Use `⟨⟨y₂.x ≫ d.r, by rw [Category.assoc]; exact hx, fun τ i => y₂.u τ i ≫ d.m.φ, fun τ i => (tan_iff d.m e (y₂.tan τ i).1).1 (y₂.tan τ i), fun τ i => (eig_iff d.m τ (hc' τ) (y₂.tan τ i).1).1 (y₂.eig τ i), fun τ v hv hv' => ?_, s, fun s' => ?_⟩, (frOver_iff d _ _).2 ⟨rfl, fun _ _ => r …` and prove the remaining obligations. Take `⟨v₂, h₁, h₂⟩` from `exists_lift d.m e hv.1`.

Substitute `h₁` using the available equality. Use `(existsUnique_congr fun a => ?_).1 (y₂.basis τ v₂ ((tan_iff d.m e h₂).2 hv) ((eig_iff d.m τ (hc' τ) h₂).2 hv'))` and prove the remaining obligations. Conclude with `comb_iff d.m e (fun j => (y₂.tan τ j).1) a h₂`. Take `⟨s₂', hs'⟩` from `exists_down hL hL₂ hw p₁ s'`. Use `(existsUnique_congr fun a => ?_).1 (y₂.gen s₂')` and prove the remaining obligations.

Conclude with `(scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans (scal_iff (fst (Over.mk (y₂.x ≫ d.r)) Xo.univ.t.G).left (toΓ S a) s s').symm)`.
-/
theorem exists_frOver_below (hc : ∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a)
    (y₂ : FrPt d.Xo₂ d.c₂ S) (hx : y₂.x ≫ d.r ≫ Xo.s = sOf c S) : ∃ y : FrPt Xo c S, FrOver d y₂ y := by
  have hc' : ∀ τ a, algebraMap d.c₂.F S (embK d.c₂ τ a) = algebraMap c.F S (embK c τ a) := fun τ a => by
    rw [← embK_eF d, hc]
  have e : y₂.x ≫ d.r = y₂.x ≫ d.r := rfl
  obtain ⟨w, hw, hw', -⟩ := d.m.lin
  obtain ⟨p, k, p₁, p₂, hk, hk'⟩ := exists_pm_iso d.m e
  have hL := Xo.univ.t.PP.isLB
  have hL₂ := d.Xo₂.univ.t.PP.isLB
  obtain ⟨s, hs⟩ := exists_up hL hL₂ hw p₁ hk hk' y₂.s
  refine ⟨⟨y₂.x ≫ d.r, by rw [Category.assoc]; exact hx, fun τ i => y₂.u τ i ≫ d.m.φ,
    fun τ i => (tan_iff d.m e (y₂.tan τ i).1).1 (y₂.tan τ i),
    fun τ i => (eig_iff d.m τ (hc' τ) (y₂.tan τ i).1).1 (y₂.eig τ i), fun τ v hv hv' => ?_, s, fun s' => ?_⟩,
    (frOver_iff d _ _).2 ⟨rfl, fun _ _ => rfl, w, p, ⟨hw, hw'⟩, p₁, p₂, hs⟩⟩
  · obtain ⟨v₂, h₁, h₂⟩ := exists_lift d.m e hv.1
    subst h₁
    refine (existsUnique_congr fun a => ?_).1
      (y₂.basis τ v₂ ((tan_iff d.m e h₂).2 hv) ((eig_iff d.m τ (hc' τ) h₂).2 hv'))
    exact comb_iff d.m e (fun j => (y₂.tan τ j).1) a h₂
  · obtain ⟨s₂', hs'⟩ := exists_down hL hL₂ hw p₁ s'
    refine (existsUnique_congr fun a => ?_).1 (y₂.gen s₂')
    exact (scal_iff (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S a) y₂.s s₂').trans
      ((rel_scal_iff hL hL₂ p₁ hk p₂ (toΓ S a) hs hs').trans
        (scal_iff (fst (Over.mk (y₂.x ≫ d.r)) Xo.univ.t.G).left (toΓ S a) s s').symm)

/- English proof (translation)
Take `⟨e, hu, w, p, hw, p₁, p₂, R⟩` from `(frOver_iff d _ _).1 h`. Take `⟨e', hu', w', p', hw', p₁', p₂', R'⟩` from `(frOver_iff d _ _).1 h'`. Take `rfl : w = w'` from `rigidified_iso_unique hG (UnivPol.pol d.Xo₂) Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _ hw.2 hw'.2`. Take `⟨p'', n', q₁, q₂, hn, -⟩` from `exists_pm_iso d.m e'`. Take `rfl : p'' = p'` from `pm_ext (q₁.trans p₁'.symm) (q₂.trans p₂'.symm)`.

Take `⟨ex, au, a, a₁, a₂, ha⟩` from `hb`. Establish `ex' : y'.x = y.x` using `by rw [← e, ← e', ex]`. Take `⟨b, b₁, b₂⟩` from `exists_pm (G := Xo.univ.t.G) (x := y.x) (fst (Over.mk y'.x) Xo.univ.t.G).left (snd (Over.mk y'.x) Xo.univ.t.G).left (by rw [← ex']; exact pm_cond _)`. Establish `sq : p'' ≫ b = a ≫ p`. Use `pm_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, b₁, p₁', Category.assoc, p₁, ← Category.assoc, a₁]`. Rewrite using `[Category.assoc, b₂, p₂', Category.assoc, p₂, a₂]`. Use `⟨ex', fun τ i => ?_, b, b₁, b₂, ?_⟩` and prove the remaining obligations. Take `⟨cf, c₁, c₂, hcf⟩` from `au τ i`. Use `⟨cf, c₁, c₂, ?_⟩` and prove the remaining obligations.

Establish `k` using `(comb_iff d.m e (fun j => (y₂.tan τ j).1) cf (ex ▸ (y₂'.tan τ i).1)).1 hcf`. Rewrite `k` using `[funext (hu τ), hu']`. Conclude with `k`. Use `(pull_scal_iff b₁ (fst (Over.mk y.x) Xo.univ.t.G).left (toΓ S (t none)) y.s y'.s).2 fun Z r z i hi => ?_` and prove the remaining obligations. Take `⟨r₂, rfl⟩ : ∃ r₂, r = r₂ ≫ p''` from `⟨r ≫ n', by rw [Category.assoc, hn, Category.comp_id]⟩`.

Take `⟨j, hj⟩` from `exists_chart d.Xo₂.univ.t.PP.isLB ((snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left (r₂ z))`. Establish `hi' : d.m.φ ((snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left (r₂ z)) ∈ Xo.univ.t.PP.L.U i` using `(congrArg (· ∈ Xo.univ.t.PP.L.U i) (pt_eq p₁' (r₂ z))).mp hi`. Establish `k₁` using `(pull_scal_iff a₁ (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S (t none)) y₂.s y₂'.s).1 ha Z r₂ z j hj`. Establish `k₂` using `R' Z r₂ z i j hi' hj`. Establish `k₃` using `R Z (r₂ ≫ a) z i j ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U i) (pt_eq a₁ (r₂ z))).mpr hi') ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U j) (pt_eq a₁ (r₂ z))).mpr hj)`.

Rewrite `k₃` using `[Category.assoc r₂ a (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left, a₁]`. Rewrite `k₂` using `[k₁]`. Establish `hb : (r₂ ≫ p'') ≫ b = (r₂ ≫ a) ≫ p` using `by rw [Category.assoc, sq, Category.assoc]`. Rewrite using `[k₂, hb, k₃, Category.assoc (r₂ ≫ a) p, p₂, mul_left_comm]`.
-/
theorem frBor_down (hG : GlobalFnsSt) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {y₂ y₂' : FrPt d.Xo₂ d.c₂ S}
    (h : FrOver d y₂ y) (h' : FrOver d y₂' y') (hb : FrBor t y₂ y₂') : FrBor t y y' := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, R⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', R'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique hG (UnivPol.pol d.Xo₂) Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _
    hw.2 hw'.2
  obtain ⟨p'', n', q₁, q₂, hn, -⟩ := exists_pm_iso d.m e'
  obtain rfl : p'' = p' := pm_ext (q₁.trans p₁'.symm) (q₂.trans p₂'.symm)
  obtain ⟨ex, au, a, a₁, a₂, ha⟩ := hb
  have ex' : y'.x = y.x := by rw [← e, ← e', ex]
  obtain ⟨b, b₁, b₂⟩ := exists_pm (G := Xo.univ.t.G) (x := y.x) (fst (Over.mk y'.x) Xo.univ.t.G).left
    (snd (Over.mk y'.x) Xo.univ.t.G).left (by rw [← ex']; exact pm_cond _)
  have sq : p'' ≫ b = a ≫ p := by
    refine pm_ext ?_ ?_
    · rw [Category.assoc, b₁, p₁', Category.assoc, p₁, ← Category.assoc, a₁]
    · rw [Category.assoc, b₂, p₂', Category.assoc, p₂, a₂]
  refine ⟨ex', fun τ i => ?_, b, b₁, b₂, ?_⟩
  · obtain ⟨cf, c₁, c₂, hcf⟩ := au τ i
    refine ⟨cf, c₁, c₂, ?_⟩
    have k := (comb_iff d.m e (fun j => (y₂.tan τ j).1) cf (ex ▸ (y₂'.tan τ i).1)).1 hcf
    rw [funext (hu τ), hu'] at k
    exact k
  · refine (pull_scal_iff b₁ (fst (Over.mk y.x) Xo.univ.t.G).left (toΓ S (t none)) y.s y'.s).2
      fun Z r z i hi => ?_
    obtain ⟨r₂, rfl⟩ : ∃ r₂, r = r₂ ≫ p'' := ⟨r ≫ n', by rw [Category.assoc, hn, Category.comp_id]⟩
    obtain ⟨j, hj⟩ := exists_chart d.Xo₂.univ.t.PP.isLB ((snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left (r₂ z))
    have hi' : d.m.φ ((snd (Over.mk y₂'.x) d.Xo₂.univ.t.G).left (r₂ z)) ∈ Xo.univ.t.PP.L.U i :=
      (congrArg (· ∈ Xo.univ.t.PP.L.U i) (pt_eq p₁' (r₂ z))).mp hi
    have k₁ := (pull_scal_iff a₁ (fst (Over.mk y₂.x) d.Xo₂.univ.t.G).left (toΓ S (t none)) y₂.s y₂'.s).1 ha Z r₂ z j hj
    have k₂ := R' Z r₂ z i j hi' hj
    have k₃ := R Z (r₂ ≫ a) z i j
      ((congrArg (fun t => d.m.φ t ∈ Xo.univ.t.PP.L.U i) (pt_eq a₁ (r₂ z))).mpr hi')
      ((congrArg (· ∈ d.Xo₂.univ.t.PP.L.U j) (pt_eq a₁ (r₂ z))).mpr hj)
    rw [Category.assoc r₂ a (snd (Over.mk y₂.x) d.Xo₂.univ.t.G).left, a₁] at k₃
    rw [k₁] at k₂
    have hb : (r₂ ≫ p'') ≫ b = (r₂ ≫ a) ≫ p := by rw [Category.assoc, sq, Category.assoc]
    rw [k₂, hb, k₃, Category.assoc (r₂ ≫ a) p, p₂, mul_left_comm]

/- English proof (translation)
Take `⟨e, hu, w, p, hw, p₁, p₂, R⟩` from `(frOver_iff d _ _).1 h`. Take `⟨e', hu', w', p', hw', p₁', p₂', R'⟩` from `(frOver_iff d _ _).1 h'`. Take `rfl : w = w'` from `rigidified_iso_unique hG (UnivPol.pol d.Xo₂) Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _ hw.2 hw'.2`. Take `⟨x, xo, u, tan, eig, bas, s, gen⟩` from `y`. Take `⟨x', xo', u', tan', eig', bas', s', gen'⟩` from `y'`.

Simplify using `only at e e' hu hu' p p₁ p₂ R p' p₁' p₂' R'`. Substitute `e` using the available equality. Substitute `e'` using the available equality. Take `rfl : u = u'` from `funext fun τ => funext fun i => (hu τ i).symm.trans (hu' τ i)`. Take `rfl : p = p'` from `pm_ext (p₁.trans p₁'.symm) (p₂.trans p₂'.symm)`.

Take `⟨p'', n', q₁, q₂, hn, -⟩` from `exists_pm_iso d.m (rfl : y₂.x ≫ d.r = y₂.x ≫ d.r)`. Take `rfl : p'' = p` from `pm_ext (q₁.trans p₁.symm) (q₂.trans p₂.symm)`. Establish `one : ∀ {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs r z ⊤ (1 : Γ(Y, ⊤)) = 1` using `fun r z => by`. Rewrite using `[gs_eq r z ⊤ (by trivial), map_one, map_one]`. Establish `H` using `(rel_scal_iff Xo.univ.t.PP.isLB d.Xo₂.univ.t.PP.isLB p₁ hn p₂ (1 : Γ(Sp S, ⊤)) R R').1 (fun Z r z j _ => by`.

Rewrite using `[one, _root_.one_mul])`. Establish `H₂` using `(scal_iff (fst (Over.mk (y₂.x ≫ d.r)) Xo.univ.t.G).left (1 : Γ(Sp S, ⊤)) s s').2 H`. Choose the witnesses or unpack the hypotheses as in `rfl : s = s' := by`. Consider the cases of `s`. Consider the cases of `s'`.

Reduce the equality to equality of the corresponding arguments. Use function extensionality and compare the values at `i`. Establish `k` using `H₂ i`. Simplify using `only [map_one] at k`. Conclude with `(k.trans (_root_.one_mul _)).symm`.

Both sides reduce to the same expression.
-/
theorem frOver_unique (hG : GlobalFnsSt) {y y' : FrPt Xo c S} {y₂ : FrPt d.Xo₂ d.c₂ S}
    (h : FrOver d y₂ y) (h' : FrOver d y₂ y') : y = y' := by
  obtain ⟨e, hu, w, p, hw, p₁, p₂, R⟩ := (frOver_iff d _ _).1 h
  obtain ⟨e', hu', w', p', hw', p₁', p₂', R'⟩ := (frOver_iff d _ _).1 h'
  obtain rfl : w = w' := rigidified_iso_unique hG (UnivPol.pol d.Xo₂) Xo.univ.t.PP.isLB d.m.φ w w' hw.1 hw'.1 _ _
    hw.2 hw'.2
  obtain ⟨x, xo, u, tan, eig, bas, s, gen⟩ := y
  obtain ⟨x', xo', u', tan', eig', bas', s', gen'⟩ := y'
  dsimp only at e e' hu hu' p p₁ p₂ R p' p₁' p₂' R'
  subst e
  subst e'
  obtain rfl : u = u' := funext fun τ => funext fun i => (hu τ i).symm.trans (hu' τ i)
  obtain rfl : p = p' := pm_ext (p₁.trans p₁'.symm) (p₂.trans p₂'.symm)
  obtain ⟨p'', n', q₁, q₂, hn, -⟩ := exists_pm_iso d.m (rfl : y₂.x ≫ d.r = y₂.x ≫ d.r)
  obtain rfl : p'' = p := pm_ext (q₁.trans p₁.symm) (q₂.trans p₂.symm)
  have one : ∀ {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs r z ⊤ (1 : Γ(Y, ⊤)) = 1 := fun r z => by
    rw [gs_eq r z ⊤ (by trivial), map_one, map_one]
  have H := (rel_scal_iff Xo.univ.t.PP.isLB d.Xo₂.univ.t.PP.isLB p₁ hn p₂ (1 : Γ(Sp S, ⊤)) R R').1 (fun Z r z j _ => by
    rw [one, _root_.one_mul])
  have H₂ := (scal_iff (fst (Over.mk (y₂.x ≫ d.r)) Xo.univ.t.G).left (1 : Γ(Sp S, ⊤)) s s').2 H
  obtain rfl : s = s' := by
    cases s
    cases s'
    congr
    funext i
    have k := H₂ i
    simp only [map_one] at k
    exact (k.trans (_root_.one_mul _)).symm
  rfl

end Frames

section Rules

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ}

/- English proof (translation)
Use function extensionality and compare the values at `p y`. Assume the negation of the conclusion as `hne`. Use `haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad`. Use `haveI : IsJacobsonRing p.R := inferInstance`. Establish `hJ : (⊥ : Ideal p.R).jacobson = ⊥` using `IsJacobsonRing.out ‹_› (fun x ⟨m, hm⟩ => Ideal.mem_bot.2 (IsNilpotent.eq_zero ⟨m, Ideal.mem_bot.1 hm⟩))`.

Establish `hn : f p y - g p y ∉ (⊥ : Ideal p.R).jacobson`. Rewrite using `[hJ]`. Conclude with `fun h₀ => hne (sub_eq_zero.1 (Ideal.mem_bot.1 h₀))`. Rewrite `hn` using `[Ideal.jacobson, Ideal.mem_sInf]`. Use `push Not at hn`.

Take `⟨m, ⟨-, hm⟩, ha⟩` from `hn`. Use `haveI := hm`. Use `letI := Ideal.Quotient.field m`. Set `χ : p.R →ₐ[c.F] AlgebraicClosure (p.R ⧸ m)` to `(IsScalarTower.toAlgHom c.F (p.R ⧸ m) (AlgebraicClosure (p.R ⧸ m))).comp (Ideal.Quotient.mkₐ c.F m)`. Take `⟨z, hz⟩` from `GlobalTheory.TransferCompare.frBC_framed Xo c _ _ χ y`.

Establish `e` using `h _ z`. Rewrite `e` using `[GlobalTheory.FlatLine.evR_of_frMap_test hf hz, GlobalTheory.FlatLine.evR_of_frMap_test hg hz]`. Apply `ha` to reduce the goal to its premises. Establish `e' : algebraMap (p.R ⧸ m) (AlgebraicClosure (p.R ⧸ m)) (Ideal.Quotient.mk m (f p y - g p y)) = 0`. Establish `: χ (f p y - g p y) = 0` using `by rw [map_sub, e, sub_self]`.

Conclude with `this`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (algebraMap _ _).injective).1 e')`.
-/
theorem eq_of_geometric {f g : Rul Xo c}
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    (hg : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k), evR Xo c f y = evR Xo c g y) :
    f = g := by
  funext p y
  by_contra hne
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsJacobsonRing p.R := inferInstance
  have hJ : (⊥ : Ideal p.R).jacobson = ⊥ :=
    IsJacobsonRing.out ‹_› (fun x ⟨m, hm⟩ => Ideal.mem_bot.2 (IsNilpotent.eq_zero ⟨m, Ideal.mem_bot.1 hm⟩))
  have hn : f p y - g p y ∉ (⊥ : Ideal p.R).jacobson := by
    rw [hJ]
    exact fun h₀ => hne (sub_eq_zero.1 (Ideal.mem_bot.1 h₀))
  rw [Ideal.jacobson, Ideal.mem_sInf] at hn
  push Not at hn
  obtain ⟨m, ⟨-, hm⟩, ha⟩ := hn
  haveI := hm
  letI := Ideal.Quotient.field m
  let χ : p.R →ₐ[c.F] AlgebraicClosure (p.R ⧸ m) :=
    (IsScalarTower.toAlgHom c.F (p.R ⧸ m) (AlgebraicClosure (p.R ⧸ m))).comp (Ideal.Quotient.mkₐ c.F m)
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ χ y
  have e := h _ z
  rw [GlobalTheory.FlatLine.evR_of_frMap_test hf hz, GlobalTheory.FlatLine.evR_of_frMap_test hg hz] at e
  apply ha
  have e' : algebraMap (p.R ⧸ m) (AlgebraicClosure (p.R ⧸ m)) (Ideal.Quotient.mk m (f p y - g p y)) = 0 := by
    have : χ (f p y - g p y) = 0 := by rw [map_sub, e, sub_self]
    exact this
  exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_eq_zero_iff _ (algebraMap _ _).injective).1 e')

abbrev algBelow (d : DeltaDat Xo c n) (S : Type) [CommRing S] [Algebra d.c₂.F S] : Algebra c.F S :=
  ((algebraMap d.c₂.F S).comp (d.eF : c.F →+* d.c₂.F)).toAlgebra

def AllOver (d : DeltaDat Xo c n) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra d.c₂.F S],
    (∀ a : c.F, algebraMap d.c₂.F S (d.eF a) = algebraMap c.F S a) →
    ∀ y₂ : FrPt d.Xo₂ d.c₂ S, y₂.x ≫ d.r ≫ Xo.s = sOf c S

/- English proof (translation)
Establish `hle : KA l ≤ KA d.l₂`. Rewrite using `[KA, IntermediateField.adjoin_le_iff]`. Introduce and unpack `x (rfl | rfl)`. Conclude with `(baseKA d.l₂).ρ.2`. Rewrite using `[← GlobalTheory.Moduli.LevelAction.zeta_pow_div d.l₂.A_pos hl]`.

Conclude with `pow_mem (baseKA d.l₂).ζ.2 _`. Introduce `S _ _ _ hc y₂`. Rewrite using `[h hle, ← Category.assoc, y₂.x_over, sOf, sOf, GlobalTheory.ClsVal.Cmp.spMap_comp']`. Use `congrArg spMap (RingHom.ext fun t => ?_)` and prove the remaining obligations. Conclude with `hc (IntermediateField.inclusion c.le t)`.
-/
theorem allOver_of_overBase (d : DeltaDat Xo c n) (hl : l.A ∣ d.l₂.A) (h : GlobalTheory.ClsVal.Cmp.OverBase d) : AllOver d := by
  have hle : KA l ≤ KA d.l₂ := by
    rw [KA, IntermediateField.adjoin_le_iff]
    rintro x (rfl | rfl)
    · exact (baseKA d.l₂).ρ.2
    · rw [← GlobalTheory.Moduli.LevelAction.zeta_pow_div d.l₂.A_pos hl]
      exact pow_mem (baseKA d.l₂).ζ.2 _
  intro S _ _ _ hc y₂
  rw [h hle, ← Category.assoc, y₂.x_over, sOf, sOf, GlobalTheory.ClsVal.Cmp.spMap_comp']
  refine congrArg spMap (RingHom.ext fun t => ?_)
  exact hc (IntermediateField.inclusion c.le t)

open Classical in

def ruleUp (d : DeltaDat Xo c n) (f : Rul Xo c) : Rul d.Xo₂ d.c₂ := fun p y₂ =>
  letI := algBelow d p.R
  if h : ∃ y : FrPt Xo c p.R, FrOver d y₂ y then evR Xo c f h.choose else 0

/- English proof (translation)
Use `letI := algBelow d p.R`. Introduce `y h`. Establish `hx : ∃ y : FrPt Xo c p.R, FrOver d y₂ y` using `⟨y, h⟩`. Establish `e : ruleUp d f p y₂ = evR Xo c f hx.choose` using `dif_pos hx`. Rewrite using `[e, frOver_unique d GlobalTheory.abelianSchemeLaws_all.1.globalFns hx.choose_spec h]`.
-/
theorem ruleUp_eq (d : DeltaDat Xo c n) (f : Rul Xo c) (p : TRing d.c₂.F) (y₂ : FrPt d.Xo₂ d.c₂ p.R) :
    letI := algBelow d p.R
    ∀ y : FrPt Xo c p.R, FrOver d y₂ y → ruleUp d f p y₂ = evR Xo c f y := by
  letI := algBelow d p.R
  intro y h
  have hx : ∃ y : FrPt Xo c p.R, FrOver d y₂ y := ⟨y, h⟩
  have e : ruleUp d f p y₂ = evR Xo c f hx.choose := dif_pos hx
  rw [e, frOver_unique d GlobalTheory.abelianSchemeLaws_all.1.globalFns hx.choose_spec h]

/- English proof (translation)
The claim follows from `ReciprocityTheory.ChartRestriction.G.PullbackSections.wtRed_of Xo c (GlobalTheory.TransferCompare.evalWD_framed Xo c) (GlobalTheory.TransferCompare.allTest_framed Xo c) (GlobalTheory.borDesc_and_wtField E H Dw l Xo c).2 (fun S _ _ y K _ _ ψ => GlobalTheory.TransferCompare.frBC_fr …`.
-/
theorem wtRed (Xo : Moduli Dw l) (c : Coeff l) : ReciprocityTheory.ChartRestriction.G.PullbackSections.WtRed Xo c :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.wtRed_of Xo c (GlobalTheory.TransferCompare.evalWD_framed Xo c) (GlobalTheory.TransferCompare.allTest_framed Xo c)
    (GlobalTheory.borDesc_and_wtField E H Dw l Xo c).2
    (fun S _ _ y K _ _ ψ => GlobalTheory.TransferCompare.frBC_framed Xo c S K ψ y)

/- English proof (translation)
Use `⟨fun p q φ y₂ z₂ hz₂ => ?_, fun p t y₂ y₂' hb => ?_⟩` and prove the remaining obligations. Use `letI := algBelow d p.R`. Use `letI := algBelow d q.R`. Use `haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad`. Set `φ' : p.R →ₐ[c.F] q.R` to `{ φ.toRingHom with commutes' := fun t => φ.commutes _ }`.

Take `⟨y, hy⟩` from `exists_frOver_below d (fun _ => rfl) y₂ (hO p.R (fun _ => rfl) y₂)`. Take `⟨z, hz⟩` from `GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ' y`. Establish `ho : FrOver d z₂ z` using `GlobalTheory.FrameLift.frOver_map d (ψ := φ') (ψ₂ := φ) rfl hy hz hz₂`. Rewrite using `[ruleUp_eq d f p y₂ y hy, ruleUp_eq d f q z₂ z ho]`. Conclude with `ReciprocityTheory.ChartRestriction.G.PullbackSections.evNat_of Xo c (GlobalTheory.TransferCompare.evalWD_framed Xo c) (GlobalTheory.TransferCompare.allTest_framed Xo c) f hf.1 p.R q.R φ' y z hz`.

Use `letI := algBelow d p.R haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad`. Take `⟨y, hy⟩` from `exists_frOver_below d (fun _ => rfl) y₂ (hO p.R (fun _ => rfl) y₂)`. Take `⟨y', hy'⟩` from `exists_frOver_below d (fun _ => rfl) y₂' (hO p.R (fun _ => rfl) y₂')`. Rewrite using `[ruleUp_eq d f p y₂ y hy, ruleUp_eq d f p y₂' y' hy']`. Conclude with `wtRed Xo c a m f hf p.R t y y' (frBor_down d GlobalTheory.abelianSchemeLaws_all.1.globalFns hy hy' hb)`.
-/
theorem ruleUp_mem (d : DeltaDat Xo c n) (hO : AllOver d) {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a m) : ruleUp d f ∈ sec d.Xo₂ d.c₂ a m := by
  refine ⟨fun p q φ y₂ z₂ hz₂ => ?_, fun p t y₂ y₂' hb => ?_⟩
  · letI := algBelow d p.R
    letI := algBelow d q.R
    haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
    let φ' : p.R →ₐ[c.F] q.R := { φ.toRingHom with commutes' := fun t => φ.commutes _ }
    obtain ⟨y, hy⟩ := exists_frOver_below d (fun _ => rfl) y₂ (hO p.R (fun _ => rfl) y₂)
    obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ' y
    have ho : FrOver d z₂ z := GlobalTheory.FrameLift.frOver_map d (ψ := φ') (ψ₂ := φ) rfl hy hz hz₂
    rw [ruleUp_eq d f p y₂ y hy, ruleUp_eq d f q z₂ z ho]
    exact ReciprocityTheory.ChartRestriction.G.PullbackSections.evNat_of Xo c (GlobalTheory.TransferCompare.evalWD_framed Xo c)
      (GlobalTheory.TransferCompare.allTest_framed Xo c) f hf.1 p.R q.R φ' y z hz
  · letI := algBelow d p.R
    haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
    obtain ⟨y, hy⟩ := exists_frOver_below d (fun _ => rfl) y₂ (hO p.R (fun _ => rfl) y₂)
    obtain ⟨y', hy'⟩ := exists_frOver_below d (fun _ => rfl) y₂' (hO p.R (fun _ => rfl) y₂')
    rw [ruleUp_eq d f p y₂ y hy, ruleUp_eq d f p y₂' y' hy']
    exact wtRed Xo c a m f hf p.R t y y' (frBor_down d GlobalTheory.abelianSchemeLaws_all.1.globalFns hy hy' hb)

/- English proof (translation)
Introduce `k _ _ _ _ hk y₂ y ho`. Take `⟨p, φ, w₂, hw₂⟩` from `GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂ k y₂`. Rewrite using `[GlobalTheory.FlatLine.evR_of_frMap_test (ruleUp_mem d hO hf).1 hw₂]`. Use `letI := algBelow d p.R`. Use `haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad`.

Set `φ' : p.R →ₐ[c.F] k` to `{ φ.toRingHom with commutes' := fun t => (φ.commutes _).trans (hk t) }`. Take `⟨w, hw⟩` from `exists_frOver_below d (fun _ => rfl) w₂ (hO p.R (fun _ => rfl) w₂)`. Take `⟨z, hz⟩` from `GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ' w`. Establish `hoz : FrOver d y₂ z` using `GlobalTheory.FrameLift.frOver_map d (ψ := φ') (ψ₂ := φ) rfl hw hz hw₂`. Take `rfl : z = y` from `frOver_unique d GlobalTheory.abelianSchemeLaws_all.1.globalFns hoz ho`.

Rewrite using `[ruleUp_eq d f p w₂ w hw]`. Conclude with `(ReciprocityTheory.ChartRestriction.G.PullbackSections.evNat_of Xo c (GlobalTheory.TransferCompare.evalWD_framed Xo c) (GlobalTheory.TransferCompare.allTest_framed Xo c) f hf.1 p.R k φ' w z hz).symm`.
-/
theorem ruleUp_pull (d : DeltaDat Xo c 0) (hO : AllOver d) {a : (E →+* ℂ) × ℕ → ℕ} {m : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a m) : GlobalTheory.LevPull.Pull d f (ruleUp d f) := by
  intro k _ _ _ _ hk y₂ y ho
  obtain ⟨p, φ, w₂, hw₂⟩ := GlobalTheory.TransferCompare.allTest_framed d.Xo₂ d.c₂ k y₂
  rw [GlobalTheory.FlatLine.evR_of_frMap_test (ruleUp_mem d hO hf).1 hw₂]
  letI := algBelow d p.R
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  let φ' : p.R →ₐ[c.F] k := { φ.toRingHom with commutes' := fun t => (φ.commutes _).trans (hk t) }
  obtain ⟨w, hw⟩ := exists_frOver_below d (fun _ => rfl) w₂ (hO p.R (fun _ => rfl) w₂)
  obtain ⟨z, hz⟩ := GlobalTheory.TransferCompare.frBC_framed Xo c _ _ φ' w
  have hoz : FrOver d y₂ z := GlobalTheory.FrameLift.frOver_map d (ψ := φ') (ψ₂ := φ) rfl hw hz hw₂
  obtain rfl : z = y := frOver_unique d GlobalTheory.abelianSchemeLaws_all.1.globalFns hoz ho
  rw [ruleUp_eq d f p w₂ w hw]
  exact (ReciprocityTheory.ChartRestriction.G.PullbackSections.evNat_of Xo c (GlobalTheory.TransferCompare.evalWD_framed Xo c)
      (GlobalTheory.TransferCompare.allTest_framed Xo c) f hf.1 p.R k φ' w z hz).symm

end Rules

section Main

open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo GlobalTheory.LevPull GlobalTheory.FieldBC
open scoped ENNReal

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c d _ hl hB a n`. Take `⟨h1, -, -, -, -, -, hlift, -, -⟩` from `hl`. Establish `hO : AllOver d` using `allOver_of_overBase d h1.2.2 (by`. Break down `hB with ⟨hpq, hA⟩ | h` into its components or cases. Conclude with `GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq hA d`.

Conclude with `h)`. Use `⟨fun f hf => ⟨ruleUp d f, ⟨ruleUp_mem d hO hf, ruleUp_pull d hO hf⟩, fun g hg => ?_⟩, fun f hf h0 => ?_⟩` and prove the remaining obligations. Use `eq_of_geometric hg.1.1 (ruleUp_mem d hO hf).1 fun k _ _ _ y₂ => ?_` and prove the remaining obligations. Use `letI := algBelow d k`. Take `⟨y, hy⟩` from `exists_frOver_below d (fun _ => rfl) y₂ (hO k (fun _ => rfl) y₂)`.

Rewrite using `[hg.2 k (fun _ => rfl) y₂ y hy, ruleUp_pull d hO hf k (fun _ => rfl) y₂ y hy]`. Use `eq_of_geometric hf.1 (sec Xo c a n).zero_mem.1 fun k _ _ _ y => ?_` and prove the remaining obligations. Use `letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra`. Establish `hk : ∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t` using `fun t => congrArg (algebraMap c.F k) (d.eF.symm_apply_apply t)`. Take `⟨y₂, hy⟩` from `hlift k hk y`.

Establish `e` using `h0 k hk y₂ y hy`. Conclude with `e.symm.trans ((evalAt_zero _ _ y₂).trans (evalAt_zero _ _ y).symm)`.
-/
theorem section_pullback_existsUnique :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev → ((Dw.p ≠ Dw.q ∧ l.A = 1) ∨ GlobalTheory.ClsVal.Cmp.OverBase d) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), (∀ f ∈ sec Xo c a n, ∃! g, g ∈ sec d.Xo₂ d.c₂ a n ∧ Pull d f g) ∧ ∀ f ∈ sec Xo c a n, Pull d f 0 → f = 0 := by
  intro E _ _ _ H Dw l Xo c d _ hl hB a n
  obtain ⟨h1, -, -, -, -, -, hlift, -, -⟩ := hl
  have hO : AllOver d := allOver_of_overBase d h1.2.2 (by
    rcases hB with ⟨hpq, hA⟩ | h
    · exact GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq hA d
    · exact h)
  refine ⟨fun f hf => ⟨ruleUp d f, ⟨ruleUp_mem d hO hf, ruleUp_pull d hO hf⟩, fun g hg => ?_⟩, fun f hf h0 => ?_⟩
  · refine eq_of_geometric hg.1.1 (ruleUp_mem d hO hf).1 fun k _ _ _ y₂ => ?_
    letI := algBelow d k
    obtain ⟨y, hy⟩ := exists_frOver_below d (fun _ => rfl) y₂ (hO k (fun _ => rfl) y₂)
    rw [hg.2 k (fun _ => rfl) y₂ y hy, ruleUp_pull d hO hf k (fun _ => rfl) y₂ y hy]
  · refine eq_of_geometric hf.1 (sec Xo c a n).zero_mem.1 fun k _ _ _ y => ?_
    letI : Algebra d.c₂.F k := ((algebraMap c.F k).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ t : c.F, algebraMap d.c₂.F k (d.eF t) = algebraMap c.F k t := fun t =>
      congrArg (algebraMap c.F k) (d.eF.symm_apply_apply t)
    obtain ⟨y₂, hy⟩ := hlift k hk y
    have e := h0 k hk y₂ y hy
    exact e.symm.trans ((evalAt_zero _ _ y₂).trans (evalAt_zero _ _ y).symm)

end Main

end GlobalTheory.CoverSec
