import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ D C W _ _ _ T Z p p' hpp hR b hb z`. Establish `hw : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ jK R`. Rewrite using `[← T.ξ_π, ← C.gp_π, ← Category.assoc T.G.hom, ← T.cart.1.w, ← Category.assoc C.A.A.hom, ← C.α_cart.1.w]`. Simplify using `only [← Category.assoc]`. Rewrite using `[hpp]`.

Establish `hpt` using `congrArg (fun g => (g z).asIdeal) hw`. Simplify using `only [Scheme.Hom.comp_apply] at hpt`. Use `set P := ((p ≫ T.G.hom) z) with hP`. Establish `hc : P.asIdeal.comap T.φ = ⊥`. Establish `e1 : (spMap T.φ ((T.G.hom) (p z))).asIdeal = P.asIdeal.comap T.φ`.

Rewrite using `[hP, Scheme.Hom.comp_apply]`. Both sides reduce to the same expression. Rewrite using `[← e1, hpt]`. Establish `e2 : ((jK R) ((C.A.A.hom) (p' z))).asIdeal = ((C.A.A.hom) (p' z)).asIdeal.comap (algebraMap R (FractionRing R))` using `rfl`. Rewrite using `[e2]`.

Establish `hbot : ((C.A.A.hom) (p' z)).asIdeal = ⊥`. Use `((C.A.A.hom) (p' z)).isPrime` as an intermediate fact. Conclude with `Ideal.eq_bot_of_prime _`. Rewrite using `[hbot]`. Conclude with `(Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)))`.

Establish `hdvr : IsDiscreteValuationRing W` using `T.cdvr.1`. Establish `hPbot : P.asIdeal = ⊥`. Assume the negation of the conclusion as `hne`. Establish `hmax : P.asIdeal.IsMaximal` using `Ideal.IsPrime.isMaximal P.isPrime hne`. Establish `hm : P.asIdeal = maximalIdeal W` using `IsLocalRing.eq_maximalIdeal hmax`.

Establish `hRm : maximalIdeal R ≠ ⊥` using `fun h => hR ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)`. Take `⟨r, hr, hr0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hRm`. Establish `hl` using `T.loc`. Establish `hφr : T.φ r ∈ P.asIdeal`. Rewrite using `[hm]`.

Conclude with `(IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal _).1 hr (isUnit_of_map_unit T.φ r hu)`. Establish `: r ∈ P.asIdeal.comap T.φ` using `hφr`. Rewrite `this` using `[hc]`. Conclude with `hr0 ((Submodule.mem_bot R).1 this)`. Establish `hmem : (p ≫ T.G.hom) z ∈ (Sp W).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b)`.

Rewrite using `[basicOpen_eq_of_affine]`. Use `show b ∉ ((p ≫ T.G.hom) z).asIdeal`. Rewrite using `[← hP, hPbot]`. Conclude with `fun h => hb ((Submodule.mem_bot W).1 h)`. Establish `hpull : gs p z ⊤ (scal T.G.hom b) = gs (p ≫ T.G.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b)` using `gs_pull p T.G.hom z ⊤ trivial _`.

Rewrite using `[hpull, gs_eq _ z ⊤ trivial]`. Establish `hz : z ∈ Z.basicOpen (((p ≫ T.G.hom).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b))`. Rewrite using `[← Scheme.preimage_basicOpen]`. Conclude with `hmem`. Conclude with `(Scheme.mem_basicOpen Z _ z (by trivial)).1 hz`.
-/
theorem unit_nonfield : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ¬ IsField R → ∀ b : W, b ≠ 0 → ∀ z : Z, IsUnit (gs p z ⊤ (scal T.G.hom b)) := by
  intro R _ _ _ D C W _ _ _ T Z p p' hpp hR b hb z

  have hw : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ jK R := by
    rw [← T.ξ_π, ← C.gp_π, ← Category.assoc T.G.hom, ← T.cart.1.w, ← Category.assoc C.A.A.hom, ← C.α_cart.1.w]
    simp only [← Category.assoc]; rw [hpp]
  have hpt := congrArg (fun g => (g z).asIdeal) hw
  simp only [Scheme.Hom.comp_apply] at hpt
  set P := ((p ≫ T.G.hom) z) with hP
  have hc : P.asIdeal.comap T.φ = ⊥ := by
    have e1 : (spMap T.φ ((T.G.hom) (p z))).asIdeal = P.asIdeal.comap T.φ := by
      rw [hP, Scheme.Hom.comp_apply]; rfl
    rw [← e1, hpt]
    have e2 : ((jK R) ((C.A.A.hom) (p' z))).asIdeal = ((C.A.A.hom) (p' z)).asIdeal.comap (algebraMap R (FractionRing R)) := rfl
    rw [e2]
    have hbot : ((C.A.A.hom) (p' z)).asIdeal = ⊥ := by
      have := ((C.A.A.hom) (p' z)).isPrime
      exact Ideal.eq_bot_of_prime _
    rw [hbot]
    exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R)))
  have hdvr : IsDiscreteValuationRing W := T.cdvr.1
  have hPbot : P.asIdeal = ⊥ := by
    by_contra hne
    have hmax : P.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal P.isPrime hne
    have hm : P.asIdeal = maximalIdeal W := IsLocalRing.eq_maximalIdeal hmax
    have hRm : maximalIdeal R ≠ ⊥ := fun h => hR ((IsLocalRing.isField_iff_maximalIdeal_eq).2 h)
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hRm
    have hl := T.loc
    have hφr : T.φ r ∈ P.asIdeal := by
      rw [hm]
      exact (IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal _).1 hr (isUnit_of_map_unit T.φ r hu)
    have : r ∈ P.asIdeal.comap T.φ := hφr
    rw [hc] at this
    exact hr0 ((Submodule.mem_bot R).1 this)
  have hmem : (p ≫ T.G.hom) z ∈ (Sp W).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b) := by
    rw [basicOpen_eq_of_affine]
    show b ∉ ((p ≫ T.G.hom) z).asIdeal
    rw [← hP, hPbot]; exact fun h => hb ((Submodule.mem_bot W).1 h)
  have hpull : gs p z ⊤ (scal T.G.hom b) = gs (p ≫ T.G.hom) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b) :=
    gs_pull p T.G.hom z ⊤ trivial _
  rw [hpull, gs_eq _ z ⊤ trivial]
  have hz : z ∈ Z.basicOpen (((p ≫ T.G.hom).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom b)) := by
    rw [← Scheme.preimage_basicOpen]; exact hmem
  exact (Scheme.mem_basicOpen Z _ z (by trivial)).1 hz

end GlobalTheory.Mum
