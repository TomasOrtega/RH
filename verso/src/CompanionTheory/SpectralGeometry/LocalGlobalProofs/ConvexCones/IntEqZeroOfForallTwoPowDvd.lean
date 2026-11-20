import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean

set_option autoImplicit false

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem int_eq_zero_of_forall_two_pow_dvd (n : ℤ) (h : ∀ k : ℕ, (2 : ℤ) ^ k ∣ n) : n = 0 := by
  refine Int.eq_zero_of_abs_lt_dvd (h n.natAbs) ?_
  have h1 : n.natAbs < 2 ^ n.natAbs := Nat.lt_two_pow_self
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h1

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem exists_two_pow_smul_of_covers2 {X : Type} [AddCommGroup X] {ι : Type} {a : ι → X}
    (ha : Covers2 a) (d : X →+ X) (hd : ∀ i, d (a i) = 0) (k : ℕ) :
    ∀ y : X, ∃ z : X, d y = ((2 : ℤ) ^ k) • z := by
  induction k with
  | zero => exact fun y => ⟨d y, by simp⟩
  | succ k ih =>
    intro y
    obtain ⟨i, x, rfl⟩ := ha y
    obtain ⟨z, hz⟩ := ih x
    refine ⟨z, ?_⟩
    rw [map_add, map_add, hd, hz, zero_add, pow_succ, mul_smul, two_smul]
    simp only [two_smul, smul_add]

/- English proof (translation)
By extensionality, compare the relevant components. Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Simplify to obtain the desired conclusion from the available facts.
-/
theorem addHom_eq_zero_of_covers2 {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {ι : Type} {a : ι → X} (ha : Covers2 a) (d : X →+ X) (hd : ∀ i, d (a i) = 0) : d = 0 := by
  ext y
  let b := Module.Free.chooseBasis ℤ X
  refine b.repr.injective (Finsupp.ext fun j => ?_)
  have : b.repr (d y) j = 0 := by
    refine int_eq_zero_of_forall_two_pow_dvd _ fun k => ?_
    obtain ⟨z, hz⟩ := exists_two_pow_smul_of_covers2 ha d hd k y
    exact ⟨b.repr z j, by rw [hz]; simp⟩
  simpa using this

/- English proof (translation)
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem addHom_ext_of_covers2 {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X]
    {ι : Type} {a : ι → X} (ha : Covers2 a) {f g : X →+ X} (h : ∀ i, f (a i) = g (a i)) : f = g := by
  have := addHom_eq_zero_of_covers2 ha (f - g) (fun i => by simp [h i])
  exact sub_eq_zero.mp this

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem finite_addHom_of_covers2 : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (ι : Type)
    [Finite ι] (a : ι → X), Covers2 a → ∀ F : Set X, F.Finite → {f : X →+ X | ∀ i, f (a i) ∈ F}.Finite := by
  intro X _ _ _ ι _ a ha F hF
  have hT : (Set.pi Set.univ fun _ : ι => F).Finite := Set.Finite.pi fun _ => hF
  refine Set.Finite.of_injOn (f := fun (f : X →+ X) (i : ι) => f (a i)) ?_ ?_ hT
  · exact fun f hf i _ => hf i
  · exact fun f _ g _ h => addHom_ext_of_covers2 ha fun i => congrFun h i

end GlobalTheory.CompanionTheory.Ar.Fan
