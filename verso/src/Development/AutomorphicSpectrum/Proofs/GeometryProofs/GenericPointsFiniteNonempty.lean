import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPointsOpenIntegralCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Comps

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem finite_maximal_points (X : Type) [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X]
    [QuasiSober X] [T0Space X] : {x : X | ∀ x' : X, x' ⤳ x → x' = x}.Finite := by
  refine Set.Finite.of_injOn (f := fun x : X => closure {x}) (t := irreducibleComponents X) ?_ ?_
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents)
  · intro x hx
    have hZ : irreducibleComponent x ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
    have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
    have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
    have hg := hirr.isGenericPoint_genericPoint_closure
    rw [hcl.closure_eq] at hg
    have hs : hirr.genericPoint ⤳ x := by
      rw [specializes_iff_mem_closure, hg.def]
      exact mem_irreducibleComponent
    have he := hx _ hs
    show closure {x} ∈ irreducibleComponents X
    rw [← he, hg.def]
    exact hZ
  · intro x _ y _ h
    exact (inseparable_iff_closure_eq.2 h).eq

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem nonempty_maximal_points (X : Type) [TopologicalSpace X] [QuasiSober X] [T0Space X] [Nonempty X] :
    {x : X | ∀ x' : X, x' ⤳ x → x' = x}.Nonempty := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have hZ : irreducibleComponent x ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hirr : IsIrreducible (irreducibleComponent x) := isIrreducible_irreducibleComponent
  have hcl : IsClosed (irreducibleComponent x) := isClosed_irreducibleComponent
  have hg := hirr.isGenericPoint_genericPoint_closure
  rw [hcl.closure_eq] at hg
  refine ⟨hirr.genericPoint, fun x' hx' => ?_⟩
  have hm : Maximal IsIrreducible (irreducibleComponent x) := hZ
  have hsub : irreducibleComponent x ⊆ closure {x'} := by
    rw [← hg.def]
    exact hx'.closure_subset
  have hirr' : IsIrreducible (closure {x'}) := isIrreducible_singleton.closure
  have heq : closure {x'} = irreducibleComponent x := (hm.eq_of_subset hirr' hsub).symm
  exact (inseparable_iff_closure_eq.2 (heq.trans hg.def.symm)).eq

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem exists_typeFn {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))
  refine ⟨_, fun i => (e.symm i).1, ?_⟩
  have key : ∀ τ : E →+* ℂ, Nat.card {i // (e.symm i).1 = τ} = m τ := by
    intro τ
    have e1 : {i // (e.symm i).1 = τ} ≃ Fin (m τ) :=
      (e.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype τ)
    rw [Nat.card_congr e1, Nat.card_fin]
  intro τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [key]; simp [m, h]
  · rw [key]; simp [m, h]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem moduli_nonempty (hc : N1c) (Xo : Moduli D l) : Nonempty Xo.X := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
  · obtain ⟨f, -, -⟩ := Xo.rep (Sp (KA l)) (𝟙 _) inferInstance (GlobalTheory.Models.RankZero.zeroObj h l _)
    exact ⟨f (IsLocalRing.closedPoint (KA l))⟩
  · obtain ⟨g, ty, hty⟩ := exists_typeFn H D.p D.q
    obtain ⟨F⟩ := hc E H D l Xo (KA l).val.toRingHom g ty h rfl hty
    exact ⟨F.u ⟨0, F.n_pos⟩ 0 (IsLocalRing.closedPoint ℂ)⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem model_nonempty {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    (h : Nonempty Xo.X) : Nonempty Y.X := by
  obtain ⟨x⟩ := h
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Xo.s) (g := spMap (IntermediateField.inclusion c.le).toRingHom) x (IsLocalRing.closedPoint c.F)
    (Subsingleton.elim _ _)
  exact ⟨Y.j z⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem finite_nonempty_maximal : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧ {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  intro hG E _ _ _ H D l Xo c Y
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have : TopologicalSpace.NoetherianSpace Y.X := GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj
  have : Nonempty Y.X := model_nonempty Y (moduli_nonempty hG.1.2.2.1 Xo)
  exact ⟨finite_maximal_points Y.X, nonempty_maximal_points Y.X⟩

end GlobalTheory.CompanionTheory.Ar.Comps
