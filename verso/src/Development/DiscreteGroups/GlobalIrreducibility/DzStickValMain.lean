import Development.DiscreteGroups.GlobalIrreducibility.DzStickValSub

noncomputable section

namespace DiscreteGroups.sglob.Stick

open IsDedekindDomain

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
  (D : GSDatum p f k A Q)

/- English proof (translation)
Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem val_g {a : ℕ} (ha : a < p ^ f - 1) :
    Q.intValuation (D.g a) = Q.intValuation (D.ζ - 1) ^ dsum p a := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  rcases Nat.eq_zero_or_pos a with rfl | h0
  · rw [D.g_zero, dsum_of_lt hp2 (by omega)]; simp
  have hb : p ^ f - 1 - a < p ^ f - 1 := by omega
  have h1 := D.pow_dsum_le_val_g ha
  have h2 := D.pow_dsum_le_val_g hb
  have h3 := D.val_g_mul_val_g_compl h0 ha
  have h4 := dsum_compl hp2 f a ha.le
  have hπ := D.val_ζ_sub_one_ne_zero
  rw [← h4, pow_add] at h3
  refine le_antisymm ?_ h1
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < Q.intValuation (D.ζ - 1) ^ dsum p (p ^ f - 1 - a) :=
    zero_lt_iff.2 (pow_ne_zero _ hπ)
  have : Q.intValuation (D.ζ - 1) ^ dsum p a * Q.intValuation (D.ζ - 1) ^ dsum p (p ^ f - 1 - a) <
      Q.intValuation (D.g a) * Q.intValuation (D.g (p ^ f - 1 - a)) :=
    mul_lt_mul hlt h2 hpos zero_le
  exact absurd h3 this.ne'

end GSDatum

end DiscreteGroups.sglob.Stick
