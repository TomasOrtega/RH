import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefficientFieldAlgClosedInFunctionFieldsOfPerio
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RegularFunctionConstOfFiniteValuesAnyLevelStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat.FixedConstLevel

open Polynomial GlobalTheory.CompRat.FixedConst

/- English proof (translation)
Introduce `E _ _ _ H D l Xo σ g ty F h1 hσ hty hA c hperm Z a ha`. Take `⟨r, rfl⟩` from `GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))`. Establish `hr : IsIntegral c.F r` using `(isIntegral_algebraMap_iff (algebraMap (kap Z) (Om Z)).injective).1 ha.isIntegral`. It suffices to establish `h : r ∈ (algebraMap c.F (kap Z)).range by`. Take `⟨k, hk⟩` from `h`.

Conclude with `⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩`. Establish `hfin : FiniteDimensional ℚ c.F` using `c.fin`. Establish `hcF : Countable c.F` using `Cardinal.mk_le_aleph0_iff.1 (by`. Simplify `Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)` using `[Cardinal.mkRat]`. Establish `hk : Countable (kap Z)` using `GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H D l Xo c).1 Z)`.

Take `⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ)` from `GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)`. Use `mem_range_of_fixed φ hr fun τ hτ => ?_` and prove the remaining obligations. Use `Xo.smooth` as an intermediate fact. Establish `: Smooth Xo.s` using `SmoothOfRelativeDimension.smooth D.dim Xo.s`. Use `CompFin.isNoetherian_XF Xo c` as an intermediate fact.

Establish `: GlobalTheory.IsNormalScheme (Xo.XF c)` using `(GlobalTheory.isNormalScheme_iff _).2 (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c)) ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))`. Set `κ : c.F →+* Γ(Xo.XF c, ⊤)` to `((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom`. Set `j : c.F →+* ℂ` to `algebraMap c.F ℂ`. Establish `hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i`. Introduce `x i hx`.

Use extensionality with `k`. Express the relevant statement in the definitionally equal form `ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _`. Rewrite using `[← ev_comp, hx, ev_spec]`. Conclude with `congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)`. Set `x : Sp ℂ ⟶ Xo.XF c` to `Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z`.

Establish `hx : x ≫ strK = spMap j`. Rewrite using `[Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `k`. Conclude with `φ.commutes k`.

Establish `hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (genPt Z) trivial).hom f)` using `ev_residue _ φ.toRingHom`. Establish `hm` using `minpoly.monic hr`. Take `⟨f, hf, hf0⟩` from `exists_section Z (genPt Z) ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r).map κ) (hm.map _) r (by`. Apply `φ.toRingHom.injective` to reduce the goal to its premises. Rewrite using `[hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), eval₂_map, hκ x j hx, map_zero]`.

Conclude with `(aeval_algHom_apply φ r _).trans (by rw [minpoly.aeval, map_zero]))`. Establish `hS : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap j → valAt' y ⊤ f ∈ insert 0 ((minpoly c.F r).rootSet ℂ)`. Introduce `y hy`. Establish `h` using `congrArg (ev y) hf0`. Rewrite `h` using `[map_mul, ← eval₂_at_apply, eval₂_map, hκ y j hy, map_zero, mul_eq_zero]`.

Rewrite using `[valAt'_top]`. Conclude with `h.imp id fun h => mem_rootSet.2 ⟨hm.ne_zero, h⟩`. Take `⟨i, P, hP, hu⟩` from `F.onto (x ≫ pullback.fst _ _) (by`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, hx, (RingHom.ext hA : σ = algebraMap (KA l) ℂ), ← Spec.map_comp]`. Use the proof step `rfl)`.

Take `⟨P', hP', hu'⟩` from `hperm τ (fun z hz => hτ ⟨z, hz⟩) i P hP`. Establish `key` using `GlobalTheory.T.regularFunction_const_of_finite_values_any_level E H D l Xo σ g ty F h1 hσ hty c j f _ ((rootSet_finite _ _).insert 0) hS i P' P hP' hP (spMap (τ : ℂ →+* ℂ) ≫ x) x (by rw [Category.assoc, ← hu]; exact hu') (by`. Rewrite using `[Category.assoc, hx, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `k`.

Conclude with `hτ k) hu.symm hx`. Rewrite `key` using `[valAt'_top, valAt'_top, ev_conj, hev, hf]`. Then use the resulting hypothesis.
-/
theorem fnAlgClosed_of_permutes_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → (∀ x : KA l, σ x = (x : ℂ)) → ∀ c : Coeff l, (∀ τ : ℂ ≃+* ℂ, (∀ x ∈ c.F, τ x = x) → ConjugationPermutesPeriods F τ id) → FnAlgClosed Xo c := by
  intro E _ _ _ H D l Xo σ g ty F h1 hσ hty hA c hperm Z a ha
  obtain ⟨r, rfl⟩ := GlobalTheory.GeomIrr.mem_range_of_isAlgebraic_ratFun a (ha.tower_top (kap Z))
  have hr : IsIntegral c.F r := (isIntegral_algebraMap_iff (algebraMap (kap Z) (Om Z)).injective).1 ha.isIntegral
  suffices h : r ∈ (algebraMap c.F (kap Z)).range by
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rw [← hk, ← IsScalarTower.algebraMap_apply]⟩
  have hfin : FiniteDimensional ℚ c.F := c.fin
  have hcF : Countable c.F := Cardinal.mk_le_aleph0_iff.1 (by
    simpa [Cardinal.mkRat] using Algebra.IsAlgebraic.cardinalMk_le_max ℚ c.F)
  have hk : Countable (kap Z) :=
    GlobalTheory.GenericReading.countable_of_fg_top ((GlobalTheory.Reg.kap_fg_trdeg E H D l Xo c).1 Z)
  obtain ⟨φ⟩ : Nonempty (kap Z →ₐ[c.F] ℂ) := GlobalTheory.nonempty_algHom_complex_of_countable c.F (kap Z)
  refine mem_range_of_fixed φ hr fun τ hτ => ?_
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have := CompFin.isNoetherian_XF Xo c
  have : GlobalTheory.IsNormalScheme (Xo.XF c) := (GlobalTheory.isNormalScheme_iff _).2
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (strK (Xo := Xo) (c := c))
      ((GlobalTheory.isNormalScheme_iff _).1 inferInstance))
  let κ : c.F →+* Γ(Xo.XF c, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv ≫ (strK (Xo := Xo) (c := c)).appTop).hom
  let j : c.F →+* ℂ := algebraMap c.F ℂ
  have hκ : ∀ (x : Sp ℂ ⟶ Xo.XF c) (i : c.F →+* ℂ), x ≫ strK = spMap i → (ev x).comp κ = i := by
    intro x i hx
    ext k
    change ev x ((strK (Xo := Xo) (c := c)).appTop.hom _) = _
    rw [← ev_comp, hx, ev_spec]
    exact congrArg i ((Scheme.ΓSpecIso (CommRingCat.of c.F)).inv_hom_id_apply k)
  let x : Sp ℂ ⟶ Xo.XF c := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ genSp Z
  have hx : x ≫ strK = spMap j := by
    rw [Category.assoc, ← Spec.map_preimage (genSp Z ≫ strK), ← Spec.map_comp]
    congr 1
    ext k
    exact φ.commutes k
  have hev : ∀ f, ev x f = φ (((Xo.XF c).evaluation ⊤ (genPt Z) trivial).hom f) := ev_residue _ φ.toRingHom
  have hm := minpoly.monic hr
  obtain ⟨f, hf, hf0⟩ := exists_section Z (genPt Z)
    ((Z.2.1 : IsIrreducible (Z : Set (Xo.XF c))).isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)) ((minpoly c.F r).map κ) (hm.map _) r (by
    apply φ.toRingHom.injective
    rw [hom_eval₂, ← (RingHom.ext hev : ev x = φ.toRingHom.comp _), eval₂_map, hκ x j hx, map_zero]
    exact (aeval_algHom_apply φ r _).trans (by rw [minpoly.aeval, map_zero]))
  have hS : ∀ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap j →
      valAt' y ⊤ f ∈ insert 0 ((minpoly c.F r).rootSet ℂ) := by
    intro y hy
    have h := congrArg (ev y) hf0
    rw [map_mul, ← eval₂_at_apply, eval₂_map, hκ y j hy, map_zero, mul_eq_zero] at h
    rw [valAt'_top]
    exact h.imp id fun h => mem_rootSet.2 ⟨hm.ne_zero, h⟩
  obtain ⟨i, P, hP, hu⟩ := F.onto (x ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx, (RingHom.ext hA : σ = algebraMap (KA l) ℂ), ← Spec.map_comp]
    rfl)
  obtain ⟨P', hP', hu'⟩ := hperm τ (fun z hz => hτ ⟨z, hz⟩) i P hP
  have key := GlobalTheory.T.regularFunction_const_of_finite_values_any_level E H D l Xo σ g ty F h1 hσ hty c j f _ ((rootSet_finite _ _).insert 0) hS i P' P hP' hP
    (spMap (τ : ℂ →+* ℂ) ≫ x) x (by rw [Category.assoc, ← hu]; exact hu') (by
      rw [Category.assoc, hx, ← Spec.map_comp]
      congr 1
      ext k
      exact hτ k) hu.symm hx
  rwa [valAt'_top, valAt'_top, ev_conj, hev, hf] at key

end GlobalTheory.CompRat.FixedConstLevel
