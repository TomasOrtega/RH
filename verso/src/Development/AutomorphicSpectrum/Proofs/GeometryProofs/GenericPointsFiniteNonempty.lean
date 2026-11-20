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
Use `Set.Finite.of_injOn (f := fun x : X => closure {x}) (t := irreducibleComponents X) ?_ ?_ (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents)` and prove the remaining obligations. Introduce `x hx`. Establish `hZ : irreducibleComponent x ∈ irreducibleComponents X` using `irreducibleComponent_mem_irreducibleComponents x`. Establish `hirr : IsIrreducible (irreducibleComponent x)` using `isIrreducible_irreducibleComponent`. Establish `hcl : IsClosed (irreducibleComponent x)` using `isClosed_irreducibleComponent`.

Establish `hg` using `hirr.isGenericPoint_genericPoint_closure`. Rewrite `hg` using `[hcl.closure_eq]`. Establish `hs : hirr.genericPoint ⤳ x`. Rewrite using `[specializes_iff_mem_closure, hg.def]`. Conclude with `mem_irreducibleComponent`.

Establish `he` using `hx _ hs`. Use `show closure {x} ∈ irreducibleComponents X`. Rewrite using `[← he, hg.def]`. Conclude with `hZ`. Introduce `x _ y _ h`.

Conclude with `(inseparable_iff_closure_eq.2 h).eq`.
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
Take `⟨x⟩` from `‹Nonempty X›`. Establish `hZ : irreducibleComponent x ∈ irreducibleComponents X` using `irreducibleComponent_mem_irreducibleComponents x`. Establish `hirr : IsIrreducible (irreducibleComponent x)` using `isIrreducible_irreducibleComponent`. Establish `hcl : IsClosed (irreducibleComponent x)` using `isClosed_irreducibleComponent`. Establish `hg` using `hirr.isGenericPoint_genericPoint_closure`.

Rewrite `hg` using `[hcl.closure_eq]`. Use `⟨hirr.genericPoint, fun x' hx' => ?_⟩` and prove the remaining obligations. Establish `hm : Maximal IsIrreducible (irreducibleComponent x)` using `hZ`. Establish `hsub : irreducibleComponent x ⊆ closure {x'}`. Rewrite using `[← hg.def]`.

Conclude with `hx'.closure_subset`. Establish `hirr' : IsIrreducible (closure {x'})` using `isIrreducible_singleton.closure`. Establish `heq : closure {x'} = irreducibleComponent x` using `(hm.eq_of_subset hirr' hsub).symm`. Conclude with `(inseparable_iff_closure_eq.2 (heq.trans hg.def.symm)).eq`.
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
Set `m : (E →+* ℂ) → ℕ` to `fun τ => if τ (H.rt : E) = H.rt0 then p else q`. Set `e` to `Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))`. Use `⟨_, fun i => (e.symm i).1, ?_⟩` and prove the remaining obligations. Establish `key : ∀ τ : E →+* ℂ, Nat.card {i // (e.symm i).1 = τ} = m τ`. Introduce `τ`.

Establish `e1 : {i // (e.symm i).1 = τ} ≃ Fin (m τ)` using `(e.symm.subtypeEquiv (fun _ => Iff.rfl)).trans (Equiv.sigmaSubtype τ)`. Rewrite using `[Nat.card_congr e1, Nat.card_fin]`. Introduce `τ`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Rewrite using `[key]`.

Simplify using `[m, h]`. Rewrite using `[key]`. Simplify using `[m, h]`.
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
Break down `Nat.eq_zero_or_pos (D.p + D.q) with h | h` into its components or cases. Take `⟨f, -, -⟩` from `Xo.rep (Sp (KA l)) (𝟙 _) inferInstance (GlobalTheory.Models.RankZero.zeroObj h l _)`. Conclude with `⟨f (IsLocalRing.closedPoint (KA l))⟩`. Take `⟨g, ty, hty⟩` from `exists_typeFn H D.p D.q`. Take `⟨F⟩` from `hc E H D l Xo (KA l).val.toRingHom g ty h rfl hty`.

Conclude with `⟨F.u ⟨0, F.n_pos⟩ 0 (IsLocalRing.closedPoint ℂ)⟩`.
-/
theorem moduli_nonempty (hc : N1c) (Xo : Moduli D l) : Nonempty Xo.X := by
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h | h
  · obtain ⟨f, -, -⟩ := Xo.rep (Sp (KA l)) (𝟙 _) inferInstance (GlobalTheory.Models.RankZero.zeroObj h l _)
    exact ⟨f (IsLocalRing.closedPoint (KA l))⟩
  · obtain ⟨g, ty, hty⟩ := exists_typeFn H D.p D.q
    obtain ⟨F⟩ := hc E H D l Xo (KA l).val.toRingHom g ty h rfl hty
    exact ⟨F.u ⟨0, F.n_pos⟩ 0 (IsLocalRing.closedPoint ℂ)⟩

/- English proof (translation)
Take `⟨x⟩` from `h`. Take `⟨z, -, -⟩` from `Scheme.Pullback.exists_preimage_pullback (f := Xo.s) (g := spMap (IntermediateField.inclusion c.le).toRingHom) x (IsLocalRing.closedPoint c.F) (Subsingleton.elim _ _)`. Conclude with `⟨Y.j z⟩`.
-/
theorem model_nonempty {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    (h : Nonempty Xo.X) : Nonempty Y.X := by
  obtain ⟨x⟩ := h
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := Xo.s) (g := spMap (IntermediateField.inclusion c.le).toRingHom) x (IsLocalRing.closedPoint c.F)
    (Subsingleton.elim _ _)
  exact ⟨Y.j z⟩

/- English proof (translation)
Introduce `hG E _ _ _ H D l Xo c Y`. Establish `: NumberField c.F` using `{ to_charZero := inferInstance, to_finiteDimensional := c.fin }`. Establish `: TopologicalSpace.NoetherianSpace Y.X` using `GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj`. Establish `: Nonempty Y.X` using `model_nonempty Y (moduli_nonempty hG.1.2.2.1 Xo)`. Conclude with `⟨finite_maximal_points Y.X, nonempty_maximal_points Y.X⟩`.
-/
theorem finite_nonempty_maximal : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)), {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Finite ∧ {x : Y.X | ∀ x' : Y.X, x' ⤳ x → x' = x}.Nonempty := by
  intro hG E _ _ _ H D l Xo c Y
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have : TopologicalSpace.NoetherianSpace Y.X := GlobalTheory.ModelSum.noetherianSpace_of_isProjOver Y.proj
  have : Nonempty Y.X := model_nonempty Y (moduli_nonempty hG.1.2.2.1 Xo)
  exact ⟨finite_maximal_points Y.X, nonempty_maximal_points Y.X⟩

end GlobalTheory.CompanionTheory.Ar.Comps
