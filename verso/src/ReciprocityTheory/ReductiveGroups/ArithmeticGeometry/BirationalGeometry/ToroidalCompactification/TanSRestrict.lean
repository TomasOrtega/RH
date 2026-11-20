import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ChartAway

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] {G : Over (Spec (CommRingCat.of S))} [GrpObj G]

def TanS {A : Type} [CommRing A] [Algebra S A] (y : sp (R₀ := S) (DualNumber A) ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom S A A) ≫ y = 1

/- English proof (translation)
Unfold `TanS at hy ⊢`. Rewrite using `[← Category.assoc, spMap_comp]`. Establish `e : (TrivSqZeroExt.fstHom S A' A').comp (dualMapS j) = j.comp (TrivSqZeroExt.fstHom S A A)`. Use `AlgHom.ext fun x => ?_` and prove the remaining obligations. Simplify using `[dualMapS_fst]`.

Rewrite using `[e, ← spMap_comp, Category.assoc, hy, comp_one'']`.
-/
theorem tanS_restrict {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (j : A →ₐ[S] A')
    {y : sp (R₀ := S) (DualNumber A) ⟶ G} (hy : TanS y) : TanS (spMap (dualMapS j) ≫ y) := by
  unfold TanS at hy ⊢
  rw [← Category.assoc, spMap_comp]
  have e : (TrivSqZeroExt.fstHom S A' A').comp (dualMapS j) = j.comp (TrivSqZeroExt.fstHom S A A) := by
    refine AlgHom.ext fun x => ?_
    simp [dualMapS_fst]
  rw [e, ← spMap_comp, Category.assoc, hy, comp_one'']

/- English proof (translation)
Unfold `TanS at hy ⊢`. Rewrite using `[← Category.assoc, spMap_comp]`. Establish `e : (TrivSqZeroExt.fstHom S A A).comp (scaleS c) = TrivSqZeroExt.fstHom S A A`. Use `AlgHom.ext fun x => ?_` and prove the remaining obligations. Simplify using `[scaleS_fst]`.

Rewrite using `[e, hy]`.
-/
theorem tanS_scale {A : Type} [CommRing A] [Algebra S A] (c : A) {y : sp (R₀ := S) (DualNumber A) ⟶ G}
    (hy : TanS y) : TanS (spMap (scaleS c) ≫ y) := by
  unfold TanS at hy ⊢
  rw [← Category.assoc, spMap_comp]
  have e : (TrivSqZeroExt.fstHom S A A).comp (scaleS c) = TrivSqZeroExt.fstHom S A A := by
    refine AlgHom.ext fun x => ?_
    simp [scaleS_fst]
  rw [e, hy]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fst_restrict (s : S) (A : Type) [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
    [IsScalarTower S (Localization.Away s) A] :
    (TrivSqZeroExt.fstHom (Localization.Away s) A A).restrictScalars S = TrivSqZeroExt.fstHom S A A := rfl

section Chart

variable {s : S} (C : Chart (Gs G s)) {A : Type} [CommRing A] [Algebra S A] [Algebra (Localization.Away s) A]
  [IsScalarTower S (Localization.Away s) A]

abbrev epsA (A : Type) [CommRing A] [Algebra (Localization.Away s) A] :
    Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] A :=
  (Algebra.ofId (Localization.Away s) A).comp (eps C)

/- English proof (translation)
Establish `hy' : pushR G (pullR (G` using `G) (R' := Localization.Away s) y) = y := pushR_pullR (G := G) (R' := Localization.Away s) y`. Establish `h0 : spMap (TrivSqZeroExt.fstHom (Localization.Away s) A A) ≫ pullR (G` using `G) (R' := Localization.Away s) y = pt C (epsA C A) := by`. Apply `pushR_inj (G := G)` to reduce the goal to its premises. Rewrite using `[pushR_spMap, fst_restrict, hy', hy]`. Simplify using `only [epsA]`.

Rewrite using `[pt_eps, pushR_one]`. Establish `hnil : ∀ a ∈ RingHom.ker (TrivSqZeroExt.fstHom (Localization.Away s) A A), IsNilpotent a`. Introduce `a ha`. Establish `h1 : a.fst = 0` using `ha`. Use `⟨2, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `refine TrivSqZeroExt.ext ?_ ?_ <;> simp [pow_two, h1]`. Establish `hcov` using `le_preimage_of_nil C (TrivSqZeroExt.fstHom (Localization.Away s) A A) (fun a => ⟨TrivSqZeroExt.inl a, by simp⟩) hnil _ (epsA C A) h0`. Take `⟨h, hh⟩` from `exists_pt C _ hcov`. Use `⟨h, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : pt C ((TrivSqZeroExt.fstHom (Localization.Away s) A A).comp h) = pt C (epsA C A)`.

Rewrite using `[← spMap_pt, ← hh, h0]`. Establish `h2` using `pt_injective C h1`. Introduce `b`. Simplify using `using AlgHom.congr_fun h2 b`. Rewrite using `[← hy', hh]`.
-/
theorem tanS_chart {y : sp (R₀ := S) (DualNumber A) ⟶ G} (hy : TanS y) :
    ∃ h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A, IsTanAt (epsA C A) h ∧ y = pushR G (pt C h) := by
  have hy' : pushR G (pullR (G := G) (R' := Localization.Away s) y) = y :=
    pushR_pullR (G := G) (R' := Localization.Away s) y
  have h0 : spMap (TrivSqZeroExt.fstHom (Localization.Away s) A A) ≫
      pullR (G := G) (R' := Localization.Away s) y = pt C (epsA C A) := by
    apply pushR_inj (G := G)
    rw [pushR_spMap, fst_restrict, hy', hy]
    simp only [epsA]
    rw [pt_eps, pushR_one]
  have hnil : ∀ a ∈ RingHom.ker (TrivSqZeroExt.fstHom (Localization.Away s) A A), IsNilpotent a := by
    intro a ha
    have h1 : a.fst = 0 := ha
    refine ⟨2, ?_⟩
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [pow_two, h1]
  have hcov := le_preimage_of_nil C (TrivSqZeroExt.fstHom (Localization.Away s) A A)
    (fun a => ⟨TrivSqZeroExt.inl a, by simp⟩) hnil _ (epsA C A) h0
  obtain ⟨h, hh⟩ := exists_pt C _ hcov
  refine ⟨h, ?_, ?_⟩
  · have h1 : pt C ((TrivSqZeroExt.fstHom (Localization.Away s) A A).comp h) = pt C (epsA C A) := by
      rw [← spMap_pt, ← hh, h0]
    have h2 := pt_injective C h1
    intro b
    simpa using AlgHom.congr_fun h2 b
  · rw [← hy', hh]

/- English proof (translation)
Unfold `TanS`. Rewrite using `[← fst_restrict s A, ← pushR_spMap, spMap_pt]`. Establish `e : (TrivSqZeroExt.fstHom (Localization.Away s) A A).comp h = epsA C A`. Use `AlgHom.ext fun b => ?_` and prove the remaining obligations. Simplify using `using hh b`.

Rewrite using `[e]`. Simplify using `only [epsA]`. Rewrite using `[pt_eps, pushR_one]`.
-/
theorem chart_tanS (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) (hh : IsTanAt (epsA C A) h) :
    TanS (pushR G (pt C h)) := by
  unfold TanS
  rw [← fst_restrict s A, ← pushR_spMap, spMap_pt]
  have e : (TrivSqZeroExt.fstHom (Localization.Away s) A A).comp h = epsA C A := by
    refine AlgHom.ext fun b => ?_
    simpa using hh b
  rw [e]
  simp only [epsA]
  rw [pt_eps, pushR_one]

/- English proof (translation)
The claim follows from `pt_injective C (pushR_inj (G := G) e)`.
-/
theorem chart_inj {h₁ h₂ : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A}
    (e : pushR G (pt C h₁) = pushR G (pt C h₂)) : h₁ = h₂ :=
  pt_injective C (pushR_inj (G := G) e)

/- English proof (translation)
Rewrite using `[← spMap_pt, pushR_spMap]`. Use `congr 2`.
-/
theorem chart_map {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A']
    [IsScalarTower S (Localization.Away s) A'] (j : A →ₐ[Localization.Away s] A')
    (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (dualMapS (j.restrictScalars S)) ≫ pushR G (pt C h) = pushR G (pt C ((dualMapS j).comp h)) := by
  rw [← spMap_pt, pushR_spMap]
  congr 2

/- English proof (translation)
Rewrite using `[← spMap_pt, pushR_spMap]`. Use `congr 2`.
-/
theorem chart_scale (c : A) (h : Γ((Gs G s).left, C.U) →ₐ[Localization.Away s] DualNumber A) :
    spMap (scaleS (S := S) c) ≫ pushR G (pt C h) = pushR G (pt C ((scaleS c).comp h)) := by
  rw [← spMap_pt, pushR_spMap]
  congr 2

def upS {A' : Type} [CommRing A'] [Algebra S A'] [Algebra (Localization.Away s) A']
    [IsScalarTower S (Localization.Away s) A'] (j : A →ₐ[S] A') : A →ₐ[Localization.Away s] A' :=
  { j with
    commutes' := fun r => by
      have : (j : A →+* A').comp (algebraMap (Localization.Away s) A) = algebraMap (Localization.Away s) A' :=
        IsLocalization.ringHom_ext (Submonoid.powers s) (by
          ext a
          simp [← IsScalarTower.algebraMap_apply])
      exact RingHom.congr_fun this r }

end Chart

end ReciprocityTheory.ChartRestriction.G.Chart
