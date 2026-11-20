import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalDefs
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

variable {E : Type*} [Field E]

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem gr_enough [CharZero E] (i : ℕ) :
    HasEnoughRootsOfUnity (AlgebraicClosure E) (l ^ i) := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  infer_instance

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eps_mem_princ_iff [CharZero E] (g : Gal(AlgebraicClosure E/E)) (n : ℕ) :
    eps l E g ∈ princ l n ↔ ∀ ζ : AlgebraicClosure E, ζ ^ l ^ n = 1 → g ζ = ζ := by
  haveI := fun i => gr_enough (l := l) (E := E) i
  set L := AlgebraicClosure E
  set σ : L ≃+* L := MulSemiringAction.toRingAut Gal(L/E) L g with hσ
  have hσg : ∀ x : L, σ x = g x := fun x => rfl
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hn := HasEnoughRootsOfUnity.natCard_rootsOfUnity L (l ^ n)
  have key : eps l E g ∈ princ l n ↔
      (modularCyclotomicCharacter L hn σ : ZMod (l ^ n)) = 1 := by
    rw [← cyclotomicCharacter.toZModPow]
    simp only [princ, redPow, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
      map_one]
    rfl
  have hpow : ∀ {M : Type _} [Monoid M] (a : M), a ^ l ^ n = 1 →
      a ^ (1 : ZMod (l ^ n)).val = a := by
    intro M _ a ha
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ ha, pow_one]
  rw [key]
  constructor
  · intro h ζ hζ
    have := cyclotomicCharacter.spec l σ ζ hζ
    rw [cyclotomicCharacter.toZModPow, h] at this
    rw [← hσg, this, hpow ζ hζ]
  · intro h
    symm
    apply modularCyclotomicCharacter.unique
    intro t ht
    rw [mem_rootsOfUnity] at ht
    have ht' : (t : L) ^ l ^ n = 1 := by
      rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
    rw [hpow (t : L) ht', hσg, h _ ht']

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isClosed_galImage [CharZero E] : IsClosed (galImage l E : Set ℤ_[l]ˣ) := by
  have hc : Continuous (eps l E) :=
    cyclotomicCharacter.continuous l E (AlgebraicClosure E)
  have : (galImage l E : Set ℤ_[l]ˣ) = Set.range (eps l E) := by
    ext x
    simp [galImage]
  rw [this]
  exact (isCompact_range hc).isClosed

end KStar.TotallyRealRoots
