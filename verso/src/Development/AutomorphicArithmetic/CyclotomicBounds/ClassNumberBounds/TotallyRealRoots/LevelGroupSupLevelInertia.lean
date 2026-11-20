import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuBasic

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem lv_princ_le (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H := by
  intro u hu
  refine mem_levelGroup.mpr ⟨1, H.one_mem, ?_⟩
  rw [map_one]
  exact (MonoidHom.mem_ker.mp hu).symm

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
private theorem lv_red_surjective : Function.Surjective (red l) := by
  intro v
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective (v : ZMod l)
  have hx : PadicInt.toZMod (k : ℤ_[l]) = (v : ZMod l) := by
    rw [map_natCast, hk]
  have hu : IsUnit (k : ℤ_[l]) := by
    by_contra hne
    have hm : (k : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := hne
    rw [← PadicInt.ker_toZMod, RingHom.mem_ker, hx] at hm
    exact v.ne_zero hm
  refine ⟨hu.unit, Units.ext ?_⟩
  simp [red, hx]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem princ_le_levelGroup (N : ℕ) (H : Subgroup (ZMod N)ˣ) :
    princ l (N.factorization l) ≤ levelGroup l N H ∧ IsOpen (levelGroup l N H : Set ℤ_[l]ˣ) :=
  ⟨lv_princ_le N H, Subgroup.isOpen_mono (lv_princ_le N H) (isOpen_princ _)⟩

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem levelGroup_eq_top {N : ℕ} (hN : ¬ l ∣ N) (H : Subgroup (ZMod N)ˣ) :
    levelGroup l N H = ⊤ ∧ resOrder l (levelGroup l N H) = l - 1 := by
  have h : levelGroup l N H = ⊤ := by
    rw [eq_top_iff]
    intro u _
    apply lv_princ_le N H
    rw [mem_princ, Nat.factorization_eq_zero_of_not_dvd hN, pow_zero]
    exact one_dvd _
  refine ⟨h, ?_⟩
  rw [h, resOrder, Subgroup.map_top_of_surjective _ lv_red_surjective, Subgroup.card_top,
    Nat.card_eq_fintype_card, ZMod.card_units]

end KStar.TotallyRealRoots
