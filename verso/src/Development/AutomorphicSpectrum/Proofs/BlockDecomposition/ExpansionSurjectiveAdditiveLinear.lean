import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationSpanDividedPowers

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil.Expand

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

/- English proof (translation)
Simplify to obtain the desired conclusion from the available facts.
-/
theorem natCast_l_acr : (l : A.Acr 1) = 0 := by
  simpa using A.pow_l_acr 1

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem dxi_zero : A.dxi 1 0 = 1 := by
  rw [PAlg.dxi, divided_power_xi_zero, map_one]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem dxi_mul (i j : ℕ) :
    A.dxi 1 i * A.dxi 1 j = (((i + j).choose i : ℕ) : A.Acr 1) * A.dxi 1 (i + j) := by
  simp only [PAlg.dxi]
  rw [← map_mul, divided_power_xi_mul, map_mul, map_natCast]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem dxi_succ (m : ℕ) :
    A.dxi 1 m * A.dxi 1 1 = ((m + 1 : ℕ) : A.Acr 1) * A.dxi 1 (m + 1) := by
  rw [dxi_mul, Nat.choose_succ_self_right]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dxi_one_pow (n : ℕ) : A.dxi 1 1 ^ n = (n.factorial : A.Acr 1) * A.dxi 1 n := by
  induction n with
  | zero => simp [dxi_zero]
  | succ n ih =>
    rw [pow_succ, ih, mul_assoc, dxi_succ, Nat.factorial_succ]
    push_cast
    ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem aTo1_pi : A.aTo1 A.pi = -A.dxi 1 1 := by
  have h := A.aTo1_coeff A.xi
  rw [xi_coeff_zero, toAcr_xi, map_neg] at h
  rw [← h, neg_neg]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem aTo1_pi_pow : A.aTo1 A.pi ^ l = 0 := by
  have hp : l.Prime := Fact.out
  obtain ⟨t, ht⟩ := Nat.dvd_factorial hp.pos (le_refl l)
  rw [aTo1_pi, neg_pow, dxi_one_pow, ht]
  push_cast
  rw [natCast_l_acr]
  simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_inv {a : ℕ} (h : ¬ l ∣ a) : ∃ m : ℕ, (m : A.Acr 1) * (a : A.Acr 1) = 1 := by
  have hp : l.Prime := Fact.out
  have hc : Nat.Coprime a l := ((Nat.Prime.coprime_iff_not_dvd hp).2 h).symm
  obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hc hp.one_lt
  refine ⟨m, ?_⟩
  have e := Nat.div_add_mod (a * m) l
  rw [hm.2] at e
  have e' := congrArg (Nat.cast : ℕ → A.Acr 1) e
  push_cast at e'
  rw [natCast_l_acr, zero_mul, zero_add] at e'
  rw [mul_comm]
  exact e'.symm

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem dxi_lq_add (q j : ℕ) (hj : j < l) :
    ∃ n : ℕ, A.dxi 1 (l * q + j) = (n : A.Acr 1) * A.dxi 1 1 ^ j * A.dxi 1 (l * q) := by
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨n, hn⟩ := ih (by omega)
    have hnd : ¬ l ∣ l * q + j + 1 := by
      intro h
      rw [add_assoc] at h
      have h' := (Nat.dvd_add_right (Dvd.intro q rfl)).1 h
      have := Nat.le_of_dvd (by omega) h'
      omega
    obtain ⟨m, hm⟩ := exists_inv A hnd
    refine ⟨m * n, ?_⟩
    have e := dxi_succ A (l * q + j)
    calc A.dxi 1 (l * q + (j + 1))
        = (m : A.Acr 1) * ((l * q + j + 1 : ℕ) : A.Acr 1) * A.dxi 1 (l * q + j + 1) := by
          rw [hm, one_mul]; rfl
      _ = (m : A.Acr 1) * (A.dxi 1 (l * q + j) * A.dxi 1 1) := by rw [e]; ring
      _ = _ := by rw [hn]; push_cast; ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem expand_single (q : ℕ) (b : A.A) :
    A.expand (Finsupp.single q b) = A.aTo1 b * A.dxi 1 (l * q) := by
  simp [PAlg.expand]

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem exists_dxi_eq (k : ℕ) : ∃ (b : A.A) (q : ℕ), A.dxi 1 k = A.aTo1 b * A.dxi 1 (l * q) := by
  have hp : l.Prime := Fact.out
  obtain ⟨n, hn⟩ := dxi_lq_add A (k / l) (k % l) (Nat.mod_lt _ hp.pos)
  rw [Nat.div_add_mod] at hn
  refine ⟨(n : A.A) * (-A.pi) ^ (k % l), k / l, ?_⟩
  rw [hn, map_mul, map_natCast, map_pow, map_neg, aTo1_pi, neg_neg]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem expand_add (c c' : ℕ →₀ A.A) : A.expand (c + c') = A.expand c + A.expand c' := by
  simp only [PAlg.expand]
  exact Finsupp.sum_add_index' (by simp) (by intro k a b; simp [add_mul])

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem expand_smul (a : A.A) (c : ℕ →₀ A.A) : A.expand (a • c) = A.aTo1 a * A.expand c := by
  simp only [PAlg.expand]
  rw [Finsupp.sum_smul_index' (by simp), Finsupp.mul_sum]
  refine Finsupp.sum_congr fun k _ => ?_
  rw [smul_eq_mul, map_mul, mul_assoc]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Express the relevant assertion in an equivalent form by its definition.

Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem expand_surjective : Function.Surjective A.expand := by
  intro y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hz := mem_spanFrom_zero A z
  unfold spanFrom at hz
  change ∃ c, A.expand c = A.mkAcr 1 z
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, -, rfl⟩ := hx
    obtain ⟨b, q, h⟩ := exists_dxi_eq A k
    exact ⟨Finsupp.single q b, by rw [expand_single, ← h]; rfl⟩
  | zero => exact ⟨0, by simp [PAlg.expand]⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, h⟩ := hx
    obtain ⟨c', h'⟩ := hy
    exact ⟨c + c', by rw [expand_add, h, h', map_add]⟩
  | smul w x _ hx =>
    obtain ⟨c, h⟩ := hx
    refine ⟨w.coeff 0 • c, ?_⟩
    rw [expand_smul, h, aTo1_coeff, Algebra.smul_def, map_mul]
    rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.expand ∧
    (∀ c c' : ℕ →₀ A.A, A.expand (c + c') = A.expand c + A.expand c') ∧
    (∀ (a : A.A) (c : ℕ →₀ A.A), A.expand (a • c) = A.aTo1 a * A.expand c) ∧
    ∀ k, A.aTo1 (A.pi ^ l) * A.dxi 1 k = 0 := fun A =>
  ⟨expand_surjective A, expand_add A, expand_smul A, fun k => by
    rw [map_pow, aTo1_pi_pow, zero_mul]⟩

end GlobalTheory.CompanionTheory.PerfFil.Expand
