import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudePairRegularImageAtP
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.StabFin
open scoped TensorProduct Classical

namespace GlobalTheory.StabFin.IntBound

variable (p : ℕ) [Fact p.Prime] (Kw : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ)

noncomputable def mu : KQ p Kw r →+* PadicAlgCl p :=
  (Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _) :
    Kw ⊗[ℚ_[p]] Qr p r →ₐ[ℚ_[p]] PadicAlgCl p).toRingHom

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _)) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) = _`. Rewrite using `[Algebra.TensorProduct.lift_tmul]`. Simplify using the standard rewrite rules.
-/
theorem mu_inclK (a : Kw) : mu p Kw r (inclK p Kw r a) = (a : PadicAlgCl p) := by
  change (Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _)) (a ⊗ₜ[ℚ_[p]] (1 : Qr p r)) = _
  rw [Algebra.TensorProduct.lift_tmul]
  simp

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _)) ((1 : Kw) ⊗ₜ[ℚ_[p]] b) = _`. Rewrite using `[Algebra.TensorProduct.lift_tmul]`. Simplify using the standard rewrite rules.
-/
theorem mu_inclQ (b : Qr p r) : mu p Kw r (inclQ p Kw r b) = (b : PadicAlgCl p) := by
  change (Algebra.TensorProduct.lift Kw.val (Qr p r).val (fun _ _ => Commute.all _ _)) ((1 : Kw) ⊗ₜ[ℚ_[p]] b) = _
  rw [Algebra.TensorProduct.lift_tmul]
  simp

/- English proof (translation)
Rewrite using `[intKQ, Subring.closure_le]`. Introduce and unpack `x (⟨a, rfl⟩ | ⟨b, rfl⟩)`. Express the relevant statement in the definitionally equal form `mu p Kw r (inclK p Kw r a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p`. Rewrite using `[mu_inclK]`. Conclude with `a.2`.

Express the relevant statement in the definitionally equal form `mu p Kw r (inclQ p Kw r b) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p`. Rewrite using `[mu_inclQ]`. Conclude with `b.2`.
-/
theorem intKQ_le : intKQ p Kw r ≤ (ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p).toSubring.comap (mu p Kw r) := by
  rw [intKQ, Subring.closure_le]
  rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
  · change mu p Kw r (inclK p Kw r a) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p
    rw [mu_inclK]
    exact a.2
  · change mu p Kw r (inclQ p Kw r b) ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.Obar p
    rw [mu_inclQ]
    exact b.2

/- English proof (translation)
The claim follows from `ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.1 (intKQ_le p Kw r hx)`.
-/
theorem norm_mu_le_one (x : KQ p Kw r) (hx : x ∈ intKQ p Kw r) : ‖mu p Kw r x‖ ≤ 1 :=
  ReciprocityTheory.DiscreteGroups.LocalClassField.mem_Obar_iff.1 (intKQ_le p Kw r hx)

end GlobalTheory.StabFin.IntBound

namespace GlobalTheory.StabFin

/- English proof (translation)
Introduce `p _ Kw n r N H k hk hN v c hv hev`. Use `set μ := IntBound.mu p Kw r`. Use `set A := μ.mapMatrix (H : Matrix (Fin n) (Fin n) (KQ p Kw r))`. Use `set Ai := μ.mapMatrix ((H⁻¹ : GL (Fin n) (KQ p Kw r)) : Matrix (Fin n) (Fin n) (KQ p Kw r))`. Use `set B := μ.mapMatrix (k : Matrix (Fin n) (Fin n) (KQ p Kw r))`.

Establish `hAAi : A * Ai = 1`. Rewrite using `[← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]`. Establish `hAiA : Ai * A = 1`. Rewrite using `[← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]`. Establish `hM : N.map (fun x => (x : PadicAlgCl p)) = A * B * Ai`.

Establish `h1 : N.map (fun x => (x : PadicAlgCl p)) = μ.mapMatrix (N.map (inclK p Kw r))`. Use extensionality with `i j`. Simplify using `[μ, IntBound.mu_inclK]`. Rewrite using `[h1, hN, Units.val_mul, Units.val_mul, map_mul, map_mul]`. Use `set v' := Ai *ᵥ v`.

Establish `hv' : v' ≠ 0`. Introduce `h0`. Apply `hv` to reduce the goal to its premises. Establish `: A *ᵥ v' = v` using `by rw [mulVec_mulVec, hAAi, one_mulVec]`. Rewrite using `[← this, h0, mulVec_zero]`.

Establish `hBv : B *ᵥ v' = c • v'`. Establish `e1 : Ai *ᵥ (N.map (fun x => (x : PadicAlgCl p)) *ᵥ v) = c • v'`. Rewrite using `[hev, mulVec_smul]`. Rewrite `e1` using `[hM, mulVec_mulVec, ← mul_assoc, ← mul_assoc, hAiA, one_mul, ← mulVec_mulVec]`. Conclude with `e1`.

Establish `hB : ∀ i j, ‖B i j‖ ≤ 1`. Take `⟨k0, rfl⟩` from `hk`. Introduce `i j`. Simplify using `only [B, RingHom.mapMatrix_apply, Matrix.map_apply, GeneralLinearGroup.map_apply]`. Conclude with `IntBound.norm_mu_le_one p Kw r _ (k0 i j).2`.

Use `haveI : Nonempty (Fin n) := by`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nonempty_iff]`. Conclude with `hv' (Subsingleton.elim _ _)`. Take `⟨j, hj⟩` from `Finite.exists_max (fun l => ‖v' l‖)`.

Establish `hpos : 0 < ‖v' j‖`. Break down `(norm_nonneg (v' j)).lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Apply `hv'` to reduce the goal to its premises.

Use function extensionality and compare the values at `l`. Use `hj l` as an intermediate fact. Rewrite `this` using `[← h]`. Conclude with `norm_le_zero_iff.1 this`. Establish `key : ‖c‖ * ‖v' j‖ ≤ 1 * ‖v' j‖`.

Establish `e : c * v' j = ∑ l, B j l * v' l`. Use `congrFun hBv j` as an intermediate fact. Rewrite `this` using `[Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← this]`. Both sides reduce to the same expression.

Rewrite using `[← norm_mul, e, one_mul]`. Use `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun l _ => ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right key hpos`.
-/
theorem norm_eigen_le_one_of_conj_Kres : ∀ (p : ℕ) [Fact p.Prime] (Kw : IntermediateField ℚ_[p] (PadicAlgCl p))
    (n r : ℕ) (N : Matrix (Fin n) (Fin n) Kw) (H k : GL (Fin n) (KQ p Kw r)), k ∈ Kres p Kw n r →
    N.map (inclK p Kw r) = ((H * k * H⁻¹ : GL (Fin n) (KQ p Kw r)) : Matrix (Fin n) (Fin n) (KQ p Kw r)) →
    ∀ (v : Fin n → PadicAlgCl p) (c : PadicAlgCl p), v ≠ 0 →
      N.map (fun x => (x : PadicAlgCl p)) *ᵥ v = c • v → ‖c‖ ≤ 1 := by
  intro p _ Kw n r N H k hk hN v c hv hev
  set μ := IntBound.mu p Kw r
  set A := μ.mapMatrix (H : Matrix (Fin n) (Fin n) (KQ p Kw r))
  set Ai := μ.mapMatrix ((H⁻¹ : GL (Fin n) (KQ p Kw r)) : Matrix (Fin n) (Fin n) (KQ p Kw r))
  set B := μ.mapMatrix (k : Matrix (Fin n) (Fin n) (KQ p Kw r))
  have hAAi : A * Ai = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have hAiA : Ai * A = 1 := by
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have hM : N.map (fun x => (x : PadicAlgCl p)) = A * B * Ai := by
    have h1 : N.map (fun x => (x : PadicAlgCl p)) = μ.mapMatrix (N.map (inclK p Kw r)) := by
      ext i j
      simp [μ, IntBound.mu_inclK]
    rw [h1, hN, Units.val_mul, Units.val_mul, map_mul, map_mul]
  set v' := Ai *ᵥ v
  have hv' : v' ≠ 0 := by
    intro h0
    apply hv
    have : A *ᵥ v' = v := by rw [mulVec_mulVec, hAAi, one_mulVec]
    rw [← this, h0, mulVec_zero]
  have hBv : B *ᵥ v' = c • v' := by
    have e1 : Ai *ᵥ (N.map (fun x => (x : PadicAlgCl p)) *ᵥ v) = c • v' := by
      rw [hev, mulVec_smul]
    rw [hM, mulVec_mulVec, ← mul_assoc, ← mul_assoc, hAiA, one_mul, ← mulVec_mulVec] at e1
    exact e1
  have hB : ∀ i j, ‖B i j‖ ≤ 1 := by
    obtain ⟨k0, rfl⟩ := hk
    intro i j
    simp only [B, RingHom.mapMatrix_apply, Matrix.map_apply, GeneralLinearGroup.map_apply]
    exact IntBound.norm_mu_le_one p Kw r _ (k0 i j).2
  haveI : Nonempty (Fin n) := by
    by_contra h
    rw [not_nonempty_iff] at h
    exact hv' (Subsingleton.elim _ _)
  obtain ⟨j, hj⟩ := Finite.exists_max (fun l => ‖v' l‖)
  have hpos : 0 < ‖v' j‖ := by
    rcases (norm_nonneg (v' j)).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hv'
      funext l
      have := hj l
      rw [← h] at this
      exact norm_le_zero_iff.1 this
  have key : ‖c‖ * ‖v' j‖ ≤ 1 * ‖v' j‖ := by
    have e : c * v' j = ∑ l, B j l * v' l := by
      have := congrFun hBv j
      rw [Pi.smul_apply, smul_eq_mul] at this
      rw [← this]
      rfl
    rw [← norm_mul, e, one_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun l _ => ?_
    rw [norm_mul]
    calc ‖B j l‖ * ‖v' l‖ ≤ 1 * ‖v' j‖ :=
          mul_le_mul (hB j l) (hj l) (norm_nonneg _) zero_le_one
      _ = ‖v' j‖ := one_mul _
  exact le_of_mul_le_mul_right key hpos

end GlobalTheory.StabFin
