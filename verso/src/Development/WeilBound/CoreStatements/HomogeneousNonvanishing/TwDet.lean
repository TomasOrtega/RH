import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwLiemult
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tw_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (S : Scheme.{0}) (G : Over S) [GrpObj G] (act : OAct (𝓞 E) G) (k : Type) [Field k] (t : Sp k ⟶ S) (ρ : k), DetCond D act t ρ → DetCond D (twistAct act g.s) t ρ := by
  intro E _ _ _ H D g S G _ act k _ t ρ h τ
  have e : τ = (τ.comp g.s.symm.toRingHom).comp g.s.toRingHom := by
    ext a
    simp
  have e2 : (τ.comp g.s.symm.toRingHom) H.rt = τ H.rt := by
    show τ (g.s.symm H.rt) = τ H.rt
    rw [(RingEquiv.symm_apply_eq _).2 g.s_rt.symm]
  have := h (τ.comp g.s.symm.toRingHom)
  rw [e2] at this
  refine ⟨fun h1 => ?_, fun h1 => ?_⟩
  · rw [e, tw_liemult]
    exact this.1 h1
  · rw [e, tw_liemult]
    exact this.2 h1

end PositivityTheory.UnitarySelfGeneration
