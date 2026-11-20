import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiScalarsRelationsUpToBaseUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Establish `h0 : κ 0 = 1`. Establish `h` using `hcube 0 0 0`. Simplify using `only [add_zero] at h`. Conclude with `mul_eq_left.1 h`. Establish `hpow : ∀ n : ℕ, κ (n • x) = κ x ^ (n ^ 2) ∧ κ ((n + 1) • x) = κ x ^ ((n + 1) ^ 2)`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [h0]`. Consider the case `succ n ih`. Use `⟨ih.2, ?_⟩` and prove the remaining obligations.

Establish `h` using `hcube ((n + 1) • x) x (-x)`. Establish `e1 : (n + 1) • x + x + -x = (n + 1) • x` using `by abel`. Establish `e2 : (n + 1) • x + x = (n + 1 + 1) • x` using `by rw [succ_nsmul _ (n + 1)]`. Establish `e3 : (n + 1) • x + -x = n • x` using `by rw [succ_nsmul]; abel`. Establish `e4 : x + -x = 0` using `by abel`.

Rewrite `h` using `[e1, e2, e3, e4, hneg, h0, ih.1, ih.2, _root_.mul_one]`. Establish `hx : κ x ^ ((n + 1) ^ 2) * κ x ^ ((n + 1) ^ 2) * κ x * κ x = κ x ^ ((n + 1 + 1) ^ 2) * κ x ^ (n ^ 2)`. Rewrite using `[← pow_add, ← pow_succ, ← pow_succ, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `mul_right_cancel (h.symm.trans hx)`. Conclude with `(hpow n).1`.
-/
theorem evenCube_nsmul_pow {X U : Type*} [AddCommGroup X] [CommGroup U] (κ : X → U)
    (hneg : ∀ x, κ (-x) = κ x)
    (hcube : ∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z))
    (x : X) (n : ℕ) : κ (n • x) = κ x ^ (n ^ 2) := by
  have h0 : κ 0 = 1 := by
    have h := hcube 0 0 0
    simp only [add_zero] at h
    exact mul_eq_left.1 h
  have hpow : ∀ n : ℕ, κ (n • x) = κ x ^ (n ^ 2) ∧ κ ((n + 1) • x) = κ x ^ ((n + 1) ^ 2) := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h := hcube ((n + 1) • x) x (-x)
      have e1 : (n + 1) • x + x + -x = (n + 1) • x := by abel
      have e2 : (n + 1) • x + x = (n + 1 + 1) • x := by rw [succ_nsmul _ (n + 1)]
      have e3 : (n + 1) • x + -x = n • x := by rw [succ_nsmul]; abel
      have e4 : x + -x = 0 := by abel
      rw [e1, e2, e3, e4, hneg, h0, ih.1, ih.2, _root_.mul_one] at h
      have hx : κ x ^ ((n + 1) ^ 2) * κ x ^ ((n + 1) ^ 2) * κ x * κ x
          = κ x ^ ((n + 1 + 1) ^ 2) * κ x ^ (n ^ 2) := by
        rw [← pow_add, ← pow_succ, ← pow_succ, ← pow_add]; congr 1; ring
      exact mul_right_cancel (h.symm.trans hx)
  exact (hpow n).1

/- English proof (translation)
Rewrite using `[eq_comm, QuotientGroup.mk'_eq_mk']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨u, rfl⟩, h⟩`. Conclude with `⟨u, by rw [← h, mul_comm q]; rfl⟩`. Introduce and unpack `⟨u, h⟩`.

Conclude with `⟨_, ⟨u, rfl⟩, Units.ext (by rw [h, mul_comm q]; rfl)⟩`.
-/
theorem unitsQuot_eq_iff {R K : Type*} [CommRing R] [CommRing K] [Algebra R K] (p q : Kˣ) :
    QuotientGroup.mk' (Units.map (algebraMap R K).toMonoidHom).range p =
      QuotientGroup.mk' (Units.map (algebraMap R K).toMonoidHom).range q ↔
    ∃ u : Rˣ, (p : K) = algebraMap R K (u : R) * (q : K) := by
  rw [eq_comm, QuotientGroup.mk'_eq_mk']
  constructor
  · rintro ⟨_, ⟨u, rfl⟩, h⟩
    exact ⟨u, by rw [← h, mul_comm q]; rfl⟩
  · rintro ⟨u, h⟩
    exact ⟨_, ⟨u, rfl⟩, Units.ext (by rw [h, mul_comm q]; rfl)⟩

/- English proof (translation)
Introduce `R _ _ _ D ga a h hE hB χ n`. Take `⟨hc, he⟩` from `GlobalTheory.PsiScalUnit.main R D ga a h`. Establish `key` using `evenCube_nsmul_pow (fun x => QuotientGroup.mk' (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range (a x)) (fun x => (unitsQuot_eq_iff _ _).2 (he hE x)) (fun x y z => by`. Use `(unitsQuot_eq_iff _ _).2 (hc hB x y z)` as an intermediate fact. Simplify `this) χ n` using `only [map_mul]`.

Take `⟨u, hu⟩` from `(unitsQuot_eq_iff (R := R) _ _).1 (key.trans (map_pow _ _ _).symm)`. Conclude with `⟨u, hu.trans (by rw [Units.val_pow_eq_pow_val])⟩`.
-/
theorem psiScal_nsmul_eq_unit_mul_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (ga : ∀ χ : D.X, LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (a : D.X → (FractionRing R)ˣ), GlobalTheory.UU.PsiScal D ga a → D.PsiEven → D.TauBimult → ∀ (χ : D.X) (n : ℕ), ∃ u : Rˣ, ((a (n • χ) : (FractionRing R)ˣ) : FractionRing R) = algebraMap R (FractionRing R) (u : R) * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2) := by
  intro R _ _ _ D ga a h hE hB χ n
  obtain ⟨hc, he⟩ := GlobalTheory.PsiScalUnit.main R D ga a h
  have key := evenCube_nsmul_pow
    (fun x => QuotientGroup.mk' (Units.map (algebraMap R (FractionRing R)).toMonoidHom).range (a x))
    (fun x => (unitsQuot_eq_iff _ _).2 (he hE x))
    (fun x y z => by
      have := (unitsQuot_eq_iff _ _).2 (hc hB x y z)
      simpa only [map_mul] using this) χ n
  obtain ⟨u, hu⟩ := (unitsQuot_eq_iff (R := R) _ _).1 (key.trans (map_pow _ _ _).symm)
  exact ⟨u, hu.trans (by rw [Units.val_pow_eq_pow_val])⟩

end GlobalTheory.Mum
