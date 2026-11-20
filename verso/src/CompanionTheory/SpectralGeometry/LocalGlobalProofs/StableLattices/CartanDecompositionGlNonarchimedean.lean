import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanExists
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BallSubgroup

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.UnitBall

variable (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]

noncomputable def ball : ValuationSubring L :=
  by apply _root_.UpperTheory.Reformulated.B.BallSubgroup.ball <;> assumption

variable {L}

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_ball {x : L} : x ∈ ball L ↔ ‖x‖ ≤ 1 := Iff.rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isUnit_of_norm_eq_one {x : ball L} (h : ‖(x : L)‖ = 1) : IsUnit x := by
  have hx : (x : L) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h
    exact zero_ne_one h
  have hi : (x : L)⁻¹ ∈ ball L := by
    rw [mem_ball, norm_inv, h, inv_one]
  refine IsUnit.of_mul_eq_one ⟨(x : L)⁻¹, hi⟩ ?_
  apply Subtype.ext
  simp [hx]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_eq_one_of_isUnit {x : ball L} (h : IsUnit x) : ‖(x : L)‖ = 1 := by
  obtain ⟨y, hy⟩ := h.exists_right_inv
  have h1 : (x : L) * (y : L) = 1 := by
    have := congrArg (Subtype.val) hy
    simpa using this
  have h2 : ‖(x : L)‖ * ‖(y : L)‖ = 1 := by
    rw [← norm_mul, h1, norm_one]
  have hx : ‖(x : L)‖ ≤ 1 := x.2
  have hy' : ‖(y : L)‖ ≤ 1 := y.2
  nlinarith [norm_nonneg (x : L), norm_nonneg (y : L)]

variable {p : Lˣ}

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem norm_unif_pos (p : Lˣ) : 0 < ‖(p : L)‖ := norm_pos_iff.2 p.ne_zero

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem exists_nat_norm (hp : IsUnif p) {x : L} (hx : x ≠ 0) (h1 : ‖x‖ ≤ 1) :
    ∃ m : ℕ, ‖x‖ = ‖(p : L)‖ ^ m := by
  obtain ⟨a, ha⟩ := hp.2 x hx
  have h0 := norm_unif_pos p
  have hnn : 0 ≤ a := by
    by_contra hneg
    have hlt : a < 0 := not_le.1 hneg
    have : 1 < ‖(p : L)‖ ^ a := one_lt_zpow_of_neg₀ h0 hp.1 hlt
    linarith
  refine ⟨a.toNat, ?_⟩
  rw [ha, ← zpow_natCast, Int.toNat_of_nonneg hnn]

def unif (hp : IsUnif p) : ball L := ⟨p, hp.1.le⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem unif_coe (hp : IsUnif p) : ((unif hp : ball L) : L) = p := rfl

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem irreducible_unif (hp : IsUnif p) : Irreducible (unif hp) := by
  have h0 := norm_unif_pos p
  refine ⟨fun h => ?_, ?_⟩
  · have := norm_eq_one_of_isUnit h
    rw [unif_coe] at this
    exact absurd this hp.1.ne
  · intro a b hab
    have hab' : (p : L) = (a : L) * (b : L) := by
      have := congrArg (Subtype.val) hab
      simpa [unif_coe] using this
    have ha0 : (a : L) ≠ 0 := fun h => p.ne_zero (by rw [hab', h, zero_mul])
    have hb0 : (b : L) ≠ 0 := fun h => p.ne_zero (by rw [hab', h, mul_zero])
    obtain ⟨i, hi⟩ := exists_nat_norm hp ha0 a.2
    obtain ⟨j, hj⟩ := exists_nat_norm hp hb0 b.2
    have hn : ‖(p : L)‖ ^ 1 = ‖(p : L)‖ ^ (i + j) := by
      rw [pow_one, pow_add, ← hi, ← hj, ← norm_mul, ← hab']
    have hij : 1 = i + j := pow_right_injective₀ h0 hp.1.ne hn
    rcases Nat.eq_zero_or_pos i with h | h
    · left
      apply isUnit_of_norm_eq_one
      rw [hi, h, pow_zero]
    · right
      have : j = 0 := by omega
      apply isUnit_of_norm_eq_one
      rw [hj, this, pow_zero]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
-/
theorem isDVR (hp : IsUnif p) : IsDiscreteValuationRing (ball L) := by
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨unif hp, irreducible_unif hp, ?_⟩
  intro x hx
  have hx0 : (x : L) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨m, hm⟩ := exists_nat_norm hp hx0 x.2
  have h0 := norm_unif_pos p
  have hpm : (p : L) ^ m ≠ 0 := pow_ne_zero _ p.ne_zero
  have hq : ‖(x : L) / (p : L) ^ m‖ = 1 := by
    rw [norm_div, norm_pow, hm]
    exact div_self (pow_ne_zero _ h0.ne')
  let q : ball L := ⟨(x : L) / (p : L) ^ m, hq.le⟩
  obtain ⟨u, hu⟩ := isUnit_of_norm_eq_one (x := q) hq
  refine ⟨m, u, ?_⟩
  apply Subtype.ext
  have hu' : ((u : ball L) : L) = (x : L) / (p : L) ^ m := by rw [hu]
  change ((unif hp : ball L) : L) ^ m * ((u : ball L) : L) = (x : L)
  rw [hu', unif_coe]
  field_simp

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_mem_congK (n : ℕ) (U : GL (Fin n) (ball L)) :
    Matrix.GeneralLinearGroup.map (algebraMap (ball L) L) U ∈ congK L n 1 zero_le_one le_rfl := by
  have key : ∀ (A : Matrix (Fin n) (Fin n) (ball L)) (i j : Fin n),
      ‖(A.map (algebraMap (ball L) L) - 1) i j‖ ≤ 1 := by
    intro A i j
    rw [Matrix.sub_apply, Matrix.map_apply, sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (A i j).2 ?_)
    rw [norm_neg, Matrix.one_apply]
    split_ifs <;> simp
  intro i j
  refine ⟨key _ i j, ?_⟩
  rw [← map_inv]
  exact key _ i j

end GlobalTheory.CompanionTheory.CartGL.UnitBall

namespace GlobalTheory.CompanionTheory.CartGL

open UnitBall in

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem cartan_unitBall (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L]
    (n : ℕ) (p : Lˣ) (hp : IsUnif p) (g : GL (Fin n) L) :
    ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ congK L n 1 zero_le_one le_rfl,
      ∃ k₂ ∈ congK L n 1 zero_le_one le_rfl, g = k₁ * dPow p a * k₂ := by
  haveI := isDVR hp
  have hdet : IsUnit (g : Matrix (Fin n) (Fin n) L).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  obtain ⟨u, v, a, hu, hv, ha, hg⟩ := GlobalTheory.CompanionTheory.Dblock.CartanDVR.cartan_exists (ball L) L n (unif hp)
    (irreducible_unif hp) (g : Matrix (Fin n) (Fin n) L) hdet
  obtain ⟨U, rfl⟩ := (Matrix.isUnit_iff_isUnit_det u).2 hu
  obtain ⟨V, rfl⟩ := (Matrix.isUnit_iff_isUnit_det v).2 hv
  refine ⟨a, ha, _, map_mem_congK n U, _, map_mem_congK n V, ?_⟩
  apply Units.ext
  rw [hg, Units.val_mul, Units.val_mul, dPow_val]
  have hd : (Matrix.diagonal fun i => (algebraMap (ball L) L (unif hp)) ^ (a i)) =
      Matrix.diagonal fun i => ((p ^ a i : Lˣ) : L) := by
    congr 1
    funext i
    rw [Units.val_zpow_eq_zpow_val]
    rfl
  rw [hd]
  rfl

end GlobalTheory.CompanionTheory.CartGL
