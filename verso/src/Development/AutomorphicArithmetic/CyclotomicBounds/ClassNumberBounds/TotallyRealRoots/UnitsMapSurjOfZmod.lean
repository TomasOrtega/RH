import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.LeNuIffPowMemPrinc

namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Substitute using the available equality. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Establish an intermediate fact.

A detailed English derivation is pending.
-/
private theorem units_map_surj_of_zmod (n : ℕ) (f : ℤ_[l] →+* ZMod n) :
    Function.Surjective (Units.map f.toMonoidHom) := by
  by_cases hn : n = 1
  · subst hn
    intro y
    exact ⟨1, Subsingleton.elim _ _⟩
  · haveI : Nontrivial (ZMod n) := ZMod.nontrivial_iff.mpr hn
    have hf : Function.Surjective f := fun y =>
      ⟨((ZMod.cast y : ℤ) : ℤ_[l]), by rw [map_intCast, ZMod.intCast_zmod_cast]⟩
    exact IsLocalRing.surjective_units_map_of_local_ringHom f hf (IsLocalHom.of_surjective f hf)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem princ_anti {a b : ℕ} (h : a ≤ b) : princ l b ≤ princ l a := by
  intro u hu
  rw [mem_princ] at hu ⊢
  exact (pow_dvd_pow _ h).trans hu

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem princ_one_eq_ker : princ l 1 = (red l).ker := by
  ext u
  rw [mem_princ, MonoidHom.mem_ker, pow_one]
  have key : PadicInt.toZMod ((u : ℤ_[l]) - 1) = 0 ↔ (l : ℤ_[l]) ∣ (u : ℤ_[l]) - 1 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton]
  rw [← key, map_sub, map_one, sub_eq_zero]
  simp [red, Units.ext_iff]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem redPow_surjective (a : ℕ) : Function.Surjective (redPow l a) :=
  units_map_surj_of_zmod _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem red_surjective : Function.Surjective (red l) :=
  units_map_surj_of_zmod _ _

end KStar.TotallyRealRoots
