import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR IsTangent IsLieComb IsLieBasis)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.JetPoint

open GlobalTheory.SqZero

variable {R : Type} [CommRing R]

/- English proof (translation)
Introduce `y`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Conclude with `⟨Ideal.Quotient.mk _ p, rfl⟩`.
-/
theorem jetTruncR_surjective (κ : Type) (m : ℕ) : Function.Surjective (jetTruncR R κ m) := by
  intro y
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ p, rfl⟩

/- English proof (translation)
The claim follows from `jet_ext fun j => by rw [jetAug_zR] exact jetAug_zR (R := R) m j`.
-/
theorem jetAug_comp_jetTruncR (κ : Type) (m : ℕ) :
    (jetAug R κ m).comp (jetTruncR R κ m) = jetAug R κ (m + 1) :=
  jet_ext fun j => by
    rw [jetAug_zR]
    exact jetAug_zR (R := R) m j

/- English proof (translation)
Establish `hle : RingHom.ker (jetTruncR R κ m) ≤ RingHom.ker (jetAug R κ (m + 1))`. Introduce `a ha`. Establish `ha' : jetTruncR R κ m a = 0` using `ha`. Express the relevant statement in the definitionally equal form `jetAug R κ (m + 1) a = 0`. Rewrite using `[← jetAug_comp_jetTruncR, AlgHom.comp_apply, ha', map_zero]`.

Use `⟨m + 1 + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.zero_eq_bot, ← le_bot_iff, ← ker_jetAug_pow (R := R) κ (m + 1)]`. Conclude with `Ideal.pow_right_mono hle _`.
-/
theorem ker_jetTruncR_isNilpotent (κ : Type) (m : ℕ) :
    IsNilpotent (RingHom.ker (jetTruncR R κ m)) := by
  have hle : RingHom.ker (jetTruncR R κ m) ≤ RingHom.ker (jetAug R κ (m + 1)) := by
    intro a ha
    have ha' : jetTruncR R κ m a = 0 := ha
    change jetAug R κ (m + 1) a = 0
    rw [← jetAug_comp_jetTruncR, AlgHom.comp_apply, ha', map_zero]
  refine ⟨m + 1 + 1, ?_⟩
  rw [Ideal.zero_eq_bot, ← le_bot_iff, ← ker_jetAug_pow (R := R) κ (m + 1)]
  exact Ideal.pow_right_mono hle _

/- English proof (translation)
The claim follows from `jet_ext fun _ => rfl`.
-/
theorem jetZeroR_comp_jetTruncR (κ : Type) (m : ℕ) :
    (jetZeroR R κ m).comp (jetTruncR R κ m) = jetZeroR R κ (m + 1) :=
  jet_ext fun _ => rfl

/- English proof (translation)
The claim follows from `Ideal.Quotient.eq_zero_iff_mem.2 (by rw [zero_add, pow_one] exact Ideal.subset_span ⟨j, rfl⟩)`.
-/
theorem zR_zero_eq_zero {κ : Type} (j : κ) : zR (R := R) 0 j = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.2 (by
    rw [zero_add, pow_one]
    exact Ideal.subset_span ⟨j, rfl⟩)

/- English proof (translation)
The claim follows from `mul_eq_zero_of_sq (ker_jetAug_pow (R := R) κ 1) (zR_mem_ker 1 j) (zR_mem_ker 1 j)`.
-/
theorem zR_one_mul_self {κ : Type} (j : κ) : zR (R := R) 1 j * zR (R := R) 1 j = 0 :=
  mul_eq_zero_of_sq (ker_jetAug_pow (R := R) κ 1) (zR_mem_ker 1 j) (zR_mem_ker 1 j)

end GlobalTheory.JetPoint

namespace GlobalTheory

open SqZero JetPoint

/- English proof (translation)
Introduce `R _ G _ _ hG d v hv`. Establish `htan : ∀ i, IsTan (v i)` using `fun i => (isTan_iff _).2 (hv.1 i)`. Use `choose L hL using fun m => ptsMap_surjective_of_isNilpotent (G := G) hv (jetTruncR R (Fin d) m) (jetTruncR_surjective _ m) (ker_jetTruncR_isNilpotent _ m)`. Set `x₁ : sp (R₀` to `R) (JetR R (Fin d) 1) ⟶ G := lieExp v (fun j => zR (R := R) 1 j) zR_one_mul_self`. Set `y : ∀ m : ℕ, sp (R₀` to `R) (JetR R (Fin d) (m + 1)) ⟶ G := fun m => Nat.rec (motive := fun m => sp (R₀ := R) (JetR R (Fin d) (m + 1)) ⟶ G) x₁ (fun k z => L (k + 1) z) m`.

Set `x : ∀ m : ℕ, sp (R₀` to `R) (JetR R (Fin d) m) ⟶ G := fun m => Nat.casesOn (motive := fun m => sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) m 1 y`. Establish `h₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m`. Introduce and unpack `(_ | m)`. Express the relevant statement in the definitionally equal form `spMap _ ≫ lieExp v _ _ = 1`. Rewrite using `[comp_lieExp, lieExp]`.

Conclude with `Finset.prod_eq_one fun i _ => epsTo_zero_comp (htan i) _ (zR_zero_eq_zero i) _`. Conclude with `hL (m + 1) (y m)`. Use `⟨x, h₁, fun m => ?_, fun j => ?_⟩` and prove the remaining obligations. Proceed by induction on `m with`. Consider the case `zero => exact comp_one' _`.

Consider the case `succ m ih => rw [← jetZeroR_comp_jetTruncR, ← spMap_comp, Category.assoc, h₁, ih]`. Express the relevant statement in the definitionally equal form `spMap _ ≫ lieExp v _ _ = _`. Rewrite using `[comp_lieExp, lieExp, Finset.prod_eq_single j]`. Establish `: ∀ (t : DualNumber R) (ht : t * t = 0), t = DualNumber.eps → epsTo R t ht = AlgHom.id R _` using `fun t ht e => DualNumber.algHom_ext (by rw [epsTo_eps, e]; rfl)`. Rewrite using `[this _ _ (by rw [dualLift_zR, Pi.single_eq_same]; rfl), spMap_id]`.

Conclude with `Category.id_comp _`. Introduce `i _ hi`. Conclude with `epsTo_zero_comp (htan i) _ (by rw [dualLift_zR, Pi.single_eq_of_ne hi, TrivSqZeroExt.inr_zero]) _`. Simplify using the standard rewrite rules.
-/
theorem exists_jetPoints_of_isLieBasis :
    ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v → ∃ (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), (∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧ (∀ m, spMap (jetZeroR R (Fin d) m) ≫ x m = 1) ∧ (∀ j, spMap (dualLift (Pi.single j (1 : R))) ≫ x 1 = v j) := by
  intro R _ G _ _ hG d v hv
  have htan : ∀ i, IsTan (v i) := fun i => (isTan_iff _).2 (hv.1 i)
  choose L hL using fun m => ptsMap_surjective_of_isNilpotent (G := G) hv (jetTruncR R (Fin d) m)
    (jetTruncR_surjective _ m) (ker_jetTruncR_isNilpotent _ m)
  let x₁ : sp (R₀ := R) (JetR R (Fin d) 1) ⟶ G :=
    lieExp v (fun j => zR (R := R) 1 j) zR_one_mul_self
  let y : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) (m + 1)) ⟶ G :=
    fun m => Nat.rec (motive := fun m => sp (R₀ := R) (JetR R (Fin d) (m + 1)) ⟶ G) x₁
      (fun k z => L (k + 1) z) m
  let x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G :=
    fun m => Nat.casesOn (motive := fun m => sp (R₀ := R) (JetR R (Fin d) m) ⟶ G) m 1 y
  have h₁ : ∀ m, spMap (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m := by
    rintro (_ | m)
    · change spMap _ ≫ lieExp v _ _ = 1
      rw [comp_lieExp, lieExp]
      exact Finset.prod_eq_one fun i _ => epsTo_zero_comp (htan i) _ (zR_zero_eq_zero i) _
    · exact hL (m + 1) (y m)
  refine ⟨x, h₁, fun m => ?_, fun j => ?_⟩
  · induction m with
    | zero => exact comp_one' _
    | succ m ih => rw [← jetZeroR_comp_jetTruncR, ← spMap_comp, Category.assoc, h₁, ih]
  · change spMap _ ≫ lieExp v _ _ = _
    rw [comp_lieExp, lieExp, Finset.prod_eq_single j]
    · have : ∀ (t : DualNumber R) (ht : t * t = 0), t = DualNumber.eps →
          epsTo R t ht = AlgHom.id R _ := fun t ht e =>
        DualNumber.algHom_ext (by rw [epsTo_eps, e]; rfl)
      rw [this _ _ (by rw [dualLift_zR, Pi.single_eq_same]; rfl), spMap_id]
      exact Category.id_comp _
    · intro i _ hi
      exact epsTo_zero_comp (htan i) _
        (by rw [dualLift_zR, Pi.single_eq_of_ne hi, TrivSqZeroExt.inr_zero]) _
    · simp

end GlobalTheory
