import Mathlib
import Formalism.PeriodIntegrals.KerLat

noncomputable section

namespace PI.TwoDivisibility

/- English proof (translation)
Establish an intermediate fact. Supply the required witnesses or components.
-/
theorem int_coords_zero (L : PeriodPair) (x y : ℤ)
    (h : (x : ℂ) * L.ω₁ + (y : ℂ) * L.ω₂ = 0) : x = 0 ∧ y = 0 := by
  have := LinearIndependent.pair_iff.mp L.indep (x : ℝ) (y : ℝ)
    (by rw [Complex.real_smul, Complex.real_smul]; push_cast; exact h)
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact.
-/
theorem half_not_mem (L : PeriodPair) (p q : ℤ) (h : ¬ ((2 : ℤ) ∣ p ∧ (2 : ℤ) ∣ q)) :
    (p : ℂ) / 2 * L.ω₁ + (q : ℂ) / 2 * L.ω₂ ∉ L.lattice := by
  intro hm
  obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.mp hm
  have := LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - (p : ℝ) / 2) ((n : ℝ) - (q : ℝ) / 2)
    (by rw [Complex.real_smul, Complex.real_smul]; push_cast; linear_combination e)
  apply h
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · have h1 : (p : ℝ) = 2 * m := by linarith [this.1]
    exact_mod_cast h1
  · have h2 : (q : ℝ) = 2 * n := by linarith [this.2]
    exact_mod_cast h2

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem zmod_pick : ∀ a b c e : ZMod 2, a + e = 1 → b * c = 0 →
    ∃ m n : ZMod 2, (m * a + n * c ≠ 0 ∨ m * b + n * e ≠ 0) ∧
      (m - (m * a + n * c) ≠ 0 ∨ n - (m * b + n * e) ≠ 0) := by
  decide

/- English proof (translation)
Evaluate the decidable proposition.
-/
theorem zmod_sq_self : ∀ a : ZMod 2, a * a = a := by decide

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem two_dvd_iff (p : ℤ) : (2 : ℤ) ∣ p ↔ ((p : ZMod 2) = 0) := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; norm_num

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Substitute using the available equality. Establish an intermediate fact.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Rewrite the indicated hypotheses using the stated equalities. Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact.

Move the embeddings inside the algebraic operations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.

Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

The claim follows by propositional logic. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. The claim follows by propositional logic.

A detailed English derivation is pending.
-/
theorem key (L : PeriodPair) (T : ℂ) (N : ℤ) (hN : 0 < N) (hN2 : Even N)
    (hq : T * T = T - N) (hT : ∀ w ∈ L.lattice, T * w ∈ L.lattice) :
    ∃ t : ℂ, 2 * t ∈ L.lattice ∧ T * t ∉ L.lattice ∧ (1 - T) * t ∉ L.lattice := by
  obtain ⟨a, b, ha⟩ := PeriodPair.mem_lattice.mp (hT _ L.ω₁_mem_lattice)
  obtain ⟨c, e, hc⟩ := PeriodPair.mem_lattice.mp (hT _ L.ω₂_mem_lattice)
  have h1 := int_coords_zero L (a * a + b * c - a + N) (a * b + b * e - b)
    (by push_cast; linear_combination ((a : ℂ) - 1 + T) * ha + (b : ℂ) * hc + L.ω₁ * hq)
  have h2 := int_coords_zero L (c * a + e * c - c) (c * b + e * e - e + N)
    (by push_cast; linear_combination (c : ℂ) * ha + ((e : ℂ) - 1 + T) * hc + L.ω₂ * hq)

  have htr : a + e = 1 := by
    rcases eq_or_ne b 0 with hb | hb
    · rcases eq_or_ne c 0 with hc0 | hc0
      · exfalso
        subst hb
        have h3 : a * a - a + N = 0 := by linarith [h1.1]
        have h4 : 0 ≤ a * a - a := by
          rcases le_or_gt a 0 with h | h
          · nlinarith
          · nlinarith
        linarith
      · have h5 : c * (a + e - 1) = 0 := by linear_combination h2.1
        have := (mul_eq_zero.mp h5).resolve_left hc0
        linarith
    · have h5 : b * (a + e - 1) = 0 := by linear_combination h1.2
      have := (mul_eq_zero.mp h5).resolve_left hb
      linarith

  obtain ⟨r, hr⟩ := hN2
  have hbc : ((b : ZMod 2) * (c : ZMod 2)) = 0 := by
    have h6 : ((a * a + b * c - a + N : ℤ) : ZMod 2) = 0 := by rw [h1.1]; simp
    have h7 : ((N : ℤ) : ZMod 2) = 0 := by
      rw [hr]; push_cast; rw [← two_mul]
      have : (2 : ZMod 2) = 0 := rfl
      rw [this, zero_mul]
    push_cast at h6
    rw [h7, zmod_sq_self] at h6
    linear_combination h6
  have htr2 : ((a : ZMod 2) + (e : ZMod 2)) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod 2)) htr
    push_cast at this
    exact this
  obtain ⟨m, n, hmn1, hmn2⟩ := zmod_pick _ _ _ _ htr2 hbc
  set m' : ℤ := (m.val : ℤ) with hm'
  set n' : ℤ := (n.val : ℤ) with hn'
  have hmc : ((m' : ℤ) : ZMod 2) = m := by
    rw [hm', Int.cast_natCast, ZMod.natCast_zmod_val]
  have hnc : ((n' : ℤ) : ZMod 2) = n := by
    rw [hn', Int.cast_natCast, ZMod.natCast_zmod_val]
  refine ⟨(m' : ℂ) / 2 * L.ω₁ + (n' : ℂ) / 2 * L.ω₂, ?_, ?_, ?_⟩
  · exact PeriodPair.mem_lattice.mpr ⟨m', n', by ring⟩
  · have hE : T * ((m' : ℂ) / 2 * L.ω₁ + (n' : ℂ) / 2 * L.ω₂) =
        ((m' * a + n' * c : ℤ) : ℂ) / 2 * L.ω₁ + ((m' * b + n' * e : ℤ) : ℂ) / 2 * L.ω₂ := by
      push_cast
      linear_combination (-(m' : ℂ) / 2) * ha + (-(n' : ℂ) / 2) * hc
    rw [hE]
    apply half_not_mem
    rw [two_dvd_iff, two_dvd_iff]
    push_cast
    rw [hmc, hnc]
    tauto
  · have hE : (1 - T) * ((m' : ℂ) / 2 * L.ω₁ + (n' : ℂ) / 2 * L.ω₂) =
        ((m' - (m' * a + n' * c) : ℤ) : ℂ) / 2 * L.ω₁ +
          ((n' - (m' * b + n' * e) : ℤ) : ℂ) / 2 * L.ω₂ := by
      push_cast
      linear_combination ((m' : ℂ) / 2) * ha + ((n' : ℂ) / 2) * hc
    rw [hE]
    apply half_not_mem
    rw [two_dvd_iff, two_dvd_iff]
    push_cast
    rw [hmc, hnc]
    tauto

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Take a linear combination of the given relations to obtain the conclusion.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main : PI.KerLat.ExistsTwoTorsionOffKernels := by
  intro L d hd hθ
  set s : ℂ := ((Real.sqrt d : ℝ) : ℂ) with hsdef
  have hs : s * s = (d : ℂ) := by
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg d)]
    simp
  have hd8 : (d : ℤ) = 8 * ((d / 8 : ℕ) : ℤ) + 7 := by omega
  set k : ℤ := ((d / 8 : ℕ) : ℤ) with hk
  have hk0 : 0 ≤ k := by positivity
  have hdC : (d : ℂ) = 8 * (k : ℂ) + 7 := by exact_mod_cast hd8
  have hq : ((1 + Complex.I * s) / 2) * ((1 + Complex.I * s) / 2) =
      ((1 + Complex.I * s) / 2) - ((2 * k + 2 : ℤ) : ℂ) := by
    push_cast
    linear_combination (-1 / 4 : ℂ) * hs + (-1 / 4 : ℂ) * hdC + (s * s / 4) * Complex.I_sq
  obtain ⟨t, h1, h2, h3⟩ := key L ((1 + Complex.I * s) / 2) (2 * k + 2) (by omega)
    ⟨k + 1, by ring⟩ hq hθ
  refine ⟨t, h1, h2, ?_⟩
  have : (1 - Complex.I * s) / 2 = 1 - (1 + Complex.I * s) / 2 := by ring
  rw [this]
  exact h3

end PI.TwoDivisibility
