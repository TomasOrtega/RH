import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LatJet

variable {R : Type} [CommRing R] (σ : R →+* ℂ) {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (J' : JetRing ℂ I n)

def coeffMap (x : J.B) : J'.B := J'.b.repr.symm (Finsupp.mapRange σ σ.map_zero (J.b.repr x))

variable {σ J J'}

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem coeffMap_repr (x : J.B) (ν : Idx I n) : J'.b.repr (coeffMap σ J J' x) ν = σ (J.b.repr x ν) := by
  simp [coeffMap]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem coeffMap_add (x y : J.B) : coeffMap σ J J' (x + y) = coeffMap σ J J' x + coeffMap σ J J' y := by
  refine J'.b.ext_elem fun ν => ?_
  simp [coeffMap_repr]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem coeffMap_zero : coeffMap σ J J' 0 = 0 := by
  refine J'.b.ext_elem fun ν => ?_
  simp [coeffMap_repr]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem coeffMap_smul (r : R) (x : J.B) : coeffMap σ J J' (r • x) = σ r • coeffMap σ J J' x := by
  refine J'.b.ext_elem fun ν => ?_
  simp [coeffMap_repr]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem coeffMap_nsmul (k : ℕ) (x : J.B) : coeffMap σ J J' (k • x) = k • coeffMap σ J J' x := by
  rw [← Nat.cast_smul_eq_nsmul R k x, coeffMap_smul, map_natCast, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem coeffMap_basis (ν : Idx I n) : coeffMap σ J J' (J.b ν) = J'.b ν := by
  refine J'.b.ext_elem fun ρ => ?_
  rw [coeffMap_repr, J.b.repr_self, J'.b.repr_self, Finsupp.single_apply, Finsupp.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeffMap_basis_mul (ν ν' : Idx I n) :
    coeffMap σ J J' (J.b ν * J.b ν') = J'.b ν * J'.b ν' := by
  rw [JetRing.mul J, JetRing.mul J']
  split_ifs
  · rw [coeffMap_nsmul, coeffMap_basis]
  · exact coeffMap_zero

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem coeffMap_one : coeffMap σ J J' 1 = 1 := by
  rw [← J.one, coeffMap_basis, J'.one]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Treat this case separately.

Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem coeffMap_mul (x y : J.B) : coeffMap σ J J' (x * y) = coeffMap σ J J' x * coeffMap σ J J' y := by
  have hx : x ∈ Submodule.span R (Set.range J.b) := J.b.mem_span x
  have hy : y ∈ Submodule.span R (Set.range J.b) := J.b.mem_span y
  induction hx using Submodule.span_induction generalizing y with
  | mem a ha =>
    obtain ⟨ν, rfl⟩ := ha
    induction hy using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨ν', rfl⟩ := hc
      rw [coeffMap_basis_mul, coeffMap_basis, coeffMap_basis]
    | zero => rw [mul_zero, coeffMap_zero, mul_zero]
    | add u v _ _ hu hv => rw [mul_add, coeffMap_add, coeffMap_add, hu, hv, mul_add]
    | smul r u _ hu => rw [mul_smul_comm, coeffMap_smul, coeffMap_smul, hu, mul_smul_comm]
  | zero => rw [zero_mul, coeffMap_zero, zero_mul]
  | add u v _ _ hu hv => rw [add_mul, coeffMap_add, coeffMap_add, hu y hy, hv y hy, add_mul]
  | smul r u _ hu => rw [smul_mul_assoc, coeffMap_smul, coeffMap_smul, hu y hy, smul_mul_assoc]

variable (σ J J')

def coeffHom : J.B →+* J'.B where
  toFun := coeffMap σ J J'
  map_one' := coeffMap_one
  map_mul' := coeffMap_mul
  map_zero' := coeffMap_zero
  map_add' := coeffMap_add

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coeffHom_isDPMorphism : IsDPMorphism J.κ J'.κ (coeffHom σ J J') := by
  have hker : ∀ a ∈ RingHom.ker J.π, coeffHom σ J J' a ∈ RingHom.ker J'.π := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [J'.π_eq, coeffHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, coeffMap_repr, ← J.π_eq, ha, map_zero]
  refine ⟨?_, fun {k} a ha => ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    exact fun a ha => hker a ha
  · have hu : IsUnit ((k.factorial : ℕ) : J'.B) := by
      have : ((k.factorial : ℕ) : J'.B) = algebraMap ℂ J'.B (k.factorial : ℂ) := by simp
      rw [this]
      exact (IsUnit.mk0 _ (by exact_mod_cast k.factorial_ne_zero)).map _
    refine hu.mul_left_cancel ?_
    rw [J'.κ.factorial_mul_dpow_eq_pow (hker a ha), ← map_natCast (coeffHom σ J J'), ← map_mul,
      J.κ.factorial_mul_dpow_eq_pow ha, map_pow]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem exists_coeffHom : ∃ τ : J.B →+* J'.B, (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) ∧ IsDPMorphism J.κ J'.κ τ :=
  ⟨coeffHom σ J J', fun x ν => coeffMap_repr x ν, coeffHom_isDPMorphism σ J J'⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem jet_coeffMap : ∀ {R : Type} [CommRing R] (σ : R →+* ℂ) {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (J' : JetRing ℂ I n),
    ∃ τ : J.B →+* J'.B, (∀ x ν, J'.b.repr (τ x) ν = σ (J.b.repr x ν)) ∧ IsDPMorphism J.κ J'.κ τ :=
  by
  intro R _ σ I _ n J J'
  exact exists_coeffHom σ J J'

end GlobalTheory.LatJet
