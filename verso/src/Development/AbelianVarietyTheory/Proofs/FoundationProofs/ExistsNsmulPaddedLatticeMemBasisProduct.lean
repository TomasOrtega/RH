import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.PadCommensurable

def sat {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] (f : V →+ V') (B : AddSubgroup V') : AddSubgroup V where
  carrier := {y | ∃ n : ℕ, 0 < n ∧ n • f y ∈ B}
  zero_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨k, hk, hy⟩
    refine ⟨n * k, Nat.mul_pos hn hk, ?_⟩
    rw [map_add, smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.nsmul_mem hx _
    · rw [mul_smul]; exact B.nsmul_mem hy _
  neg_mem' := by
    rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [map_neg, smul_neg]; exact B.neg_mem hx⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Proceed by induction. Treat this case separately.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Treat this case separately. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem uniform_of_fg {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] (f : V →+ V') (A : AddSubgroup V)
    (B : AddSubgroup V') (hA : A.FG) (h : A ≤ sat f B) : ∃ R : ℕ, 0 < R ∧ ∀ y ∈ A, R • f y ∈ B := by
  obtain ⟨S, rfl⟩ := hA
  have h' : ∀ y : S, ∃ n : ℕ, 0 < n ∧ n • f y ∈ B := fun y => h (AddSubgroup.subset_closure y.2)
  choose n hn hy using h'
  refine ⟨∏ y, n y, Finset.prod_pos fun y _ => hn y, fun y hy' => ?_⟩
  induction hy' using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc⟩ : n ⟨x, hx⟩ ∣ ∏ y, n y := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    rw [hc, mul_comm, mul_smul]
    exact B.nsmul_mem (hy ⟨x, hx⟩) _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, smul_add]; exact B.add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact B.neg_mem hx

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_nat_mul_int {K : Type*} [Field K] [NumberField K] (κ : K) :
    ∃ (n : ℕ) (a : 𝓞 K), 0 < n ∧ (a : K) = n * κ := by
  have halg : IsAlgebraic ℤ κ := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic κ)
  obtain ⟨d, hd, hi⟩ := halg.exists_integral_multiple
  rcases Int.natAbs_eq d with h | h
  · refine ⟨d.natAbs, ⟨d • κ, hi⟩, Int.natAbs_pos.2 hd, ?_⟩
    change d • κ = _
    rw [zsmul_eq_mul]
    conv_lhs => rw [h]
    rw [Int.cast_natCast]
  · refine ⟨d.natAbs, -⟨d • κ, hi⟩, Int.natAbs_pos.2 hd, ?_⟩
    change -(d • κ) = _
    rw [zsmul_eq_mul]
    conv_lhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast]
    ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations.

Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem exists_nsmul_mem (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (w : ℂ) (hw : w ∈ lamOf D cc δ)
    (A : Matrix (Fin N') (Fin N) D.host.E) :
    w • embV D (tor0 D cc δ) A ∈ sat (AddMonoidHom.id _) (LaB D (tor0 D cc δ) b) := by
  obtain ⟨-, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ hc
  have hA : A ∈ Submodule.span D.host.K (Set.range b) := by rw [hb.2]; trivial
  obtain ⟨κ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hA
  have e : w • embV D (tor0 D cc δ) (∑ i, κ i • b i) =
      ∑ i, (D.host.φ₀ (κ i : D.host.E) * w) • embV D (tor0 D cc δ) (b i) := by
    funext τ s t
    have h1 : ∀ i, (κ i • b i) s t = (κ i : D.host.E) * b i s t := fun i => rfl
    have h2 := hD.1 τ
    simp only [embV, tor0, Pi.smul_apply, Finset.sum_apply, Matrix.sum_apply, h1, map_sum, map_mul, h2,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  obtain ⟨n, a, hn, ha⟩ := exists_nat_mul_int (κ i)
  refine ⟨n, hn, AddSubgroup.subset_closure ⟨_, hst a w hw, i, ?_⟩⟩
  rw [AddMonoidHom.id_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ha]
  congr 1
  push_cast
  rw [map_mul, map_natCast]
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem nsmul_pad_mem : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b → (La D (tor0 D cc δ) L L').FG → ∃ R : ℕ, 0 < R ∧ ∀ y ∈ La D (tor0 D cc δ) L L', R • pad D m y ∈ LaB D (tor0 D cc δ) b := by
  intro D hD cc δ hc N N' m r L L' b hb hfg
  refine uniform_of_fg (padL D m).toAddMonoidHom _ _ hfg ?_
  rw [La, AddSubgroup.closure_le]
  rintro _ ⟨w, hw, A, -, rfl⟩
  obtain ⟨n, hn, h⟩ := exists_nsmul_mem D hD cc δ hc b hb w hw (padM D m A)
  refine ⟨n, hn, ?_⟩
  change n • pad D m _ ∈ _
  rw [pad_smul, pad_embV D _ (fun τ => map_zero (embT D τ))]
  exact h

end GlobalTheory.PadCommensurable
