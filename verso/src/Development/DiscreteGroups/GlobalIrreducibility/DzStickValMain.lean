import Development.DiscreteGroups.GlobalIrreducibility.DzStickValSub

noncomputable section

namespace DiscreteGroups.sglob.Stick

open IsDedekindDomain

namespace GSDatum

variable {p f : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Fintype k] [Algebra (ZMod p) k]
  {A : Type*} [CommRing A] [IsDedekindDomain A] {Q : HeightOneSpectrum A}
  (D : GSDatum p f k A Q)

/- English proof (translation)
Establish `hp2 : 2 ≤ p` using `(Fact.out : p.Prime).two_le`. Break down `Nat.eq_zero_or_pos a with rfl | h0` into its components or cases. Rewrite using `[D.g_zero, dsum_of_lt hp2 (by omega)]; simp`. Establish `hb : p ^ f - 1 - a < p ^ f - 1` using `by omega`. Establish `h1` using `D.pow_dsum_le_val_g ha`.

Establish `h2` using `D.pow_dsum_le_val_g hb`. Establish `h3` using `D.val_g_mul_val_g_compl h0 ha`. Establish `h4` using `dsum_compl hp2 f a ha.le`. Establish `hπ` using `D.val_ζ_sub_one_ne_zero`. Rewrite `h3` using `[← h4, pow_add]`.

Use `le_antisymm ?_ h1` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Rewrite `hlt` using `[not_le]`. Establish `hpos : 0 < Q.intValuation (D.ζ - 1) ^ dsum p (p ^ f - 1 - a)` using `zero_lt_iff.2 (pow_ne_zero _ hπ)`. Establish `: Q.intValuation (D.ζ - 1) ^ dsum p a * Q.intValuation (D.ζ - 1) ^ dsum p (p ^ f - 1 - a) < Q.intValuation (D.g a) * Q.intValuation (D.g (p ^ f - 1 - a))` using `mul_lt_mul hlt h2 hpos zero_le`.

Conclude with `absurd h3 this.ne'`.
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
