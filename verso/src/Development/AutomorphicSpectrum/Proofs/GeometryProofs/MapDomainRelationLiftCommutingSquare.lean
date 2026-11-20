import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
The claim follows from `RingOfIntegers.ext (g.σ.apply_symm_apply (a : E))`.
-/
theorem HostAut.s_symm_s (g : HostAut H) (a : 𝓞 E) : g.s (g.symm.s a) = a :=
  RingOfIntegers.ext (g.σ.apply_symm_apply (a : E))

/- English proof (translation)
The claim follows from `RingOfIntegers.ext (g.σ.symm_apply_apply (a : E))`.
-/
theorem HostAut.hostAut_symm_s_s (g : HostAut H) (a : 𝓞 E) : g.symm.s (g.s a) = a :=
  RingOfIntegers.ext (g.σ.symm_apply_apply (a : E))

/- English proof (translation)
The claim follows from `RingOfIntegers.ext rfl`.
-/
theorem HostAut.hostAut_refl_s (a : 𝓞 E) : (HostAut.refl H).s a = a :=
  RingOfIntegers.ext rfl

/- English proof (translation)
Consider the cases of `u`. Consider the cases of `v`. Establish `: ∀ a, _ = _` using `h`. Take `rfl : _ = _` from `funext this`. Both sides reduce to the same expression.
-/
theorem oAct_eq {O : Type} [CommRing O] {S : Scheme.{0}} {G : Over S} [GrpObj G] {u v : OAct O G}
    (h : ∀ a, u.act a = v.act a) : u = v := by
  cases u
  cases v
  have : ∀ a, _ = _ := h
  obtain rfl : _ = _ := funext this
  rfl

/- English proof (translation)
Consider the cases of `t with`. Consider the case `mk G semi act PP cub sym adj prim`. Establish `hact : twistAct act g.s = act` using `oAct_eq h`. Establish `key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'), (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim`. Introduce `act' e adj' prim'`.

Substitute `e` using the available equality. Both sides reduce to the same expression. Conclude with `key _ hact _ _`.
-/
theorem twistSAB_eq_of_act {S : Scheme.{0}} (t : SAB H S) (g : HostAut H)
    (h : ∀ a, t.act.act (g.s a) = t.act.act a) : twistSAB t g = t := by
  cases t with
  | mk G semi act PP cub sym adj prim =>
    have hact : twistAct act g.s = act := oAct_eq h
    have key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'),
        (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim := by
      intro act' e adj' prim'
      subst e
      rfl
    exact key _ hact _ _

/- English proof (translation)
Consider the cases of `t with`. Consider the case `mk G semi act PP cub sym adj prim`. Establish `hact : twistAct (twistAct act g.s) g'.s = act` using `oAct_eq fun a => congrArg act.act (h a)`. Establish `key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'), (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim`. Introduce `act' e adj' prim'`.

Substitute `e` using the available equality. Both sides reduce to the same expression. Conclude with `key _ hact _ _`.
-/
theorem twistSAB_twistSAB {S : Scheme.{0}} (t : SAB H S) (g g' : HostAut H)
    (h : ∀ a, g.s (g'.s a) = a) : twistSAB (twistSAB t g) g' = t := by
  cases t with
  | mk G semi act PP cub sym adj prim =>
    have hact : twistAct (twistAct act g.s) g'.s = act := oAct_eq fun a => congrArg act.act (h a)
    have key : ∀ (act' : OAct (𝓞 E) G) (_ : act' = act) (adj' prim'),
        (SAB.mk G semi act' PP cub sym adj' prim' : SAB H S) = SAB.mk G semi act PP cub sym adj prim := by
      intro act' e adj' prim'
      subst e
      rfl
    exact key _ hact _ _

/- English proof (translation)
Assemble the required witnesses or components as `⟨twistSAB_twistSAB t g g.symm g.s_symm_s, twistSAB_twistSAB t g.symm g g.hostAut_symm_s_s, twistSAB_eq_of_act t _ fun a => congrArg t.act.act (HostAut.hostAut_refl_s a)⟩`.
-/
theorem twistSAB_symm_refl (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0})
    (t : SAB H S) (g : HostAut H) :
    twistSAB (twistSAB t g) g.symm = t ∧ twistSAB (twistSAB t g.symm) g = t ∧
      twistSAB t (HostAut.refl H) = t :=
  ⟨twistSAB_twistSAB t g g.symm g.s_symm_s, twistSAB_twistSAB t g.symm g g.hostAut_symm_s_s,
    twistSAB_eq_of_act t _ fun a => congrArg t.act.act (HostAut.hostAut_refl_s a)⟩

end GlobalTheory.CompanionTheory.Ar
