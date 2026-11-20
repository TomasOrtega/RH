import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularGenus.StdLatEqSpan
import Formalism.HermitianLattices.StatementMass
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual

open NumberField

noncomputable section

namespace PI.UG.W

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
example (E : Type) [Field E] [NumberField E] [StarRing E] : PI.UG.IsCMUnram E ↔ Formalism.HermitianLatticesTheory.IsCMUnram E := Iff.rfl

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
example (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (p : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) :
    IsUnimodularAt (hStd E n) p N ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt (hStd E n) p N := Iff.rfl

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
example (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (p : Ideal (𝓞 E)) (N : Submodule (𝓞 E) (Sp E n)) :
    (∃ g ∈ isom (hStd E n), gmap g (loc (K := E) p (stdLat E n)) = loc (K := E) p N) ↔
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom (hStd E n), Formalism.HermitianLatticesTheory.gmap g (Formalism.HermitianLatticesTheory.loc (K := E) p (stdLat E n)) = Formalism.HermitianLatticesTheory.loc (K := E) p N) :=
  Iff.rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Supply the required witnesses or components. Supply the required witnesses or components.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem stdLat_isOrtho (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice (hStd E n) (stdLat E n) n := by
  refine ⟨fun i => Pi.single i 1, ?_, ?_, ?_, ?_⟩
  · convert (Pi.basisFun E (Fin n)).linearIndependent using 1 <;> first | rfl | (funext i; simp)
  · convert (Pi.basisFun E (Fin n)).span_eq using 3 <;> first | rfl | (funext i; simp)
  · apply le_antisymm
    · intro x hx
      rw [stdLat, Submodule.mem_pi] at hx
      have hx' : ∀ i, ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = x i := fun i =>
        Submodule.mem_one.mp (hx i (Set.mem_univ i))
      choose r hr using hx'
      have hxe : x = ∑ i, r i • (Pi.single i (1 : E) : Fin n → E) := by
        funext k
        simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hr]
      rw [hxe]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, stdLat, Submodule.mem_pi]
      intro j _
      rw [Submodule.mem_one]
      by_cases hij : j = i
      · subst hij
        exact ⟨1, by simp⟩
      · exact ⟨0, by simp [Pi.single_apply, hij]⟩
  · intro i j
    simp only [hStd, LinearMap.mk₂'ₛₗ_apply]
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_apply, hk]) (by simp)]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Pi.single_apply, hij, Ne.symm hij]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem unimodLocal_of_locDual (hLD : Formalism.HermitianLatticesTheory.LocDual) : UnimodLocal := by
  intro E _ _ _ n N hN hU p hp
  have hsymm : (hStd E n).IsSymm := by
    first
      | (refine ⟨fun x y => ?_⟩
         simp [hStd, map_sum, starRingEnd_apply, star_mul', mul_comm])
      | (intro x y
         simp [hStd, map_sum, starRingEnd_apply, star_mul', mul_comm])
  have hstar : ∀ r : 𝓞 E, star (algebraMap (𝓞 E) E r) ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro r
    exact ⟨RingOfIntegers.mapRingHom (starRingEnd E) r, rfl⟩
  have hfg : N.FG := hN.fg
  have key := (hLD (𝓞 E) E (Sp E n) (hStd E n) hsymm hstar N hfg).2
  exact key.mp hU p hp

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unimodLocal : UnimodLocal := unimodLocal_of_locDual Formalism.HermitianLatticesTheory.locDual

end PI.UG.W
