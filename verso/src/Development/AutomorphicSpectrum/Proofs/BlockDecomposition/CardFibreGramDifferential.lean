import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMatricesCardStatement

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.GramDiff

variable {E : Type} [CommRing E] (τ : E →+* E)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cT_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E) :
    cT τ (A * B) = cT τ B * cT τ A := by
  simp only [cT, Matrix.map_mul, Matrix.transpose_mul]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem cT_add {a b : ℕ} (A B : Matrix (Fin a) (Fin b) E) :
    cT τ (A + B) = cT τ A + cT τ B := by
  ext i j
  simp [cT]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem cT_zero {a b : ℕ} : cT τ (0 : Matrix (Fin a) (Fin b) E) = 0 := by
  ext i j
  simp [cT]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem cT_neg {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) : cT τ (-A) = -cT τ A := by
  ext i j
  simp [cT]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem cT_smul {a b : ℕ} (c : E) (A : Matrix (Fin a) (Fin b) E) :
    cT τ (c • A) = τ c • cT τ A := by
  ext i j
  simp [cT]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem cT_cT (hτ : ∀ a, τ (τ a) = a) {a b : ℕ} (A : Matrix (Fin a) (Fin b) E) :
    cT τ (cT τ A) = A := by
  ext i j
  simp [cT, hτ]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem cT_cross (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} {S : Matrix (Fin m) (Fin m) E} (hS : cT τ S = S)
    (x y : Matrix (Fin m) (Fin n) E) : cT τ (cT τ x * S * y) = cT τ y * S * x := by
  rw [cT_mul, cT_mul, cT_cT τ hτ, hS, Matrix.mul_assoc]

def hermSub (n : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) E) where
  carrier := {H | cT τ H = H}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [cT_add, ha, hb]
  zero_mem' := cT_zero τ
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rw [cT_neg, ha]

def diffMap (hτ : ∀ a, τ (τ a) = a) {m n : ℕ} (S : Matrix (Fin m) (Fin m) E) (hS : cT τ S = S)
    (x : Matrix (Fin m) (Fin n) E) : Matrix (Fin m) (Fin n) E →+ hermSub τ n :=
  AddMonoidHom.mk'
    (fun y => ⟨cT τ y * S * x + cT τ x * S * y, by
      change cT τ (cT τ y * S * x + cT τ x * S * y) = cT τ y * S * x + cT τ x * S * y
      rw [cT_add, cT_cross τ hτ hS, cT_cross τ hτ hS, add_comm]⟩)
    (by
      intro a b
      apply Subtype.ext
      change cT τ (a + b) * S * x + cT τ x * S * (a + b) =
        (cT τ a * S * x + cT τ x * S * a) + (cT τ b * S * x + cT τ x * S * b)
      rw [cT_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add]
      abel)

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion. Establish an intermediate fact. Take a linear combination of the given relations to obtain the conclusion. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Take a linear combination of the given relations to obtain the conclusion.
-/
theorem exists_trace_one {q : ℕ} {ε : ℤ} (h : ResAlg E τ q ε) : ∃ θ : E, θ + τ θ = 1 := by
  obtain ⟨u, hu, -⟩ := h.basis
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h1 : (u - τ u) * τ v = -1 := by
    have := congrArg τ hv
    rw [map_mul, map_sub, h.inv, map_one] at this
    linear_combination -this
  have h2 : τ v = -v := by
    linear_combination (-(τ v)) * hv + v * h1
  refine ⟨u * v, ?_⟩
  rw [map_mul, h2]
  linear_combination hv

/- English proof (translation)
Assume the hypotheses and unpack their components. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the hypotheses and the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem diffMap_surjective {q : ℕ} {ε : ℤ} (h : ResAlg E τ q ε) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) E) (hS : cT τ S = S) (T : Matrix (Fin n) (Fin n) E)
    (x : Matrix (Fin m) (Fin n) E) (hT : IsUnit T.det) (hx : cT τ x * S * x = T) :
    Function.Surjective (diffMap τ h.inv S hS x) := by
  rintro ⟨H, hH⟩
  have hH' : cT τ H = H := hH
  obtain ⟨θ, hθ⟩ := exists_trace_one τ h
  have hW : cT τ x * S * (x * T⁻¹ * (θ • H)) = θ • H := by
    calc cT τ x * S * (x * T⁻¹ * (θ • H)) = (cT τ x * S * x) * T⁻¹ * (θ • H) := by
          simp only [Matrix.mul_assoc]
      _ = θ • H := by rw [hx, Matrix.mul_nonsing_inv T hT, Matrix.one_mul]
  refine ⟨x * T⁻¹ * (θ • H), ?_⟩
  apply Subtype.ext
  change cT τ (x * T⁻¹ * (θ • H)) * S * x + cT τ x * S * (x * T⁻¹ * (θ • H)) = H
  rw [← cT_cross τ h.inv hS x (x * T⁻¹ * (θ • H)), hW, cT_smul, hH', ← add_smul, add_comm, hθ, one_smul]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_fibre_mul {A B : Type} [AddCommGroup A] [AddCommGroup B] [Finite A] (f : A →+ B)
    (hf : Function.Surjective f) (b : B) : Nat.card {a // f a = b} * Nat.card B = Nat.card A := by
  obtain ⟨y, rfl⟩ := hf b
  have e : {a // f a = f y} ≃ f.ker :=
    { toFun := fun a => ⟨a.1 - y, by simp [AddMonoidHom.mem_ker, a.2]⟩
      invFun := fun k => ⟨k.1 + y, by
        have : f k.1 = 0 := k.2
        simp [this]⟩
      left_inv := fun a => by simp
      right_inv := fun k => by simp }
  have hi : f.ker.index = Nat.card B := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hf]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  rw [Nat.card_congr e, ← hi]
  exact AddSubgroup.card_mul_index f.ker

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem card_fibre_gram_differential : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) E) (T : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin m) (Fin n) E) (H : Matrix (Fin n) (Fin n) E), cT τ S = S → cT τ T = T → IsUnit T.det → cT τ x * S * x = T → cT τ H = H → Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} = q ^ (2 * m * n - n ^ 2) := by
  intro E _ τ q ε h m n hnm S T x H hS _ hT hx hH
  have hq : 0 < q := lt_trans Nat.zero_lt_one h.one_lt
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by rw [h.card]; positivity)
  have hM : Nat.card (Matrix (Fin m) (Fin n) E) = ((q ^ 2) ^ n) ^ m := by
    change Nat.card (Fin m → Fin n → E) = _
    rw [Nat.card_fun, Nat.card_fun, h.card]
    simp
  have hHerm : Nat.card (hermSub τ n) = q ^ (n ^ 2) := GlobalTheory.T.hermitian_matrices_card E τ q ε h n
  have hfib := card_fibre_mul (diffMap τ h.inv S hS x)
    (diffMap_surjective τ h S hS T x hT hx) ⟨H, hH⟩
  have hc : Nat.card {y : Matrix (Fin m) (Fin n) E // cT τ y * S * x + cT τ x * S * y = H} =
      Nat.card {y // diffMap τ h.inv S hS x y = ⟨H, hH⟩} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      rw [Subtype.ext_iff]
      rfl)
  have hle : n ^ 2 ≤ 2 * m * n := by nlinarith
  have hpow : ((q ^ 2) ^ n) ^ m = q ^ (n ^ 2) * q ^ (2 * m * n - n ^ 2) := by
    rw [← pow_add, Nat.add_sub_cancel' hle, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [hc]
  rw [hHerm, hM, hpow, mul_comm] at hfib
  exact Nat.eq_of_mul_eq_mul_left (pow_pos hq _) hfib

end GlobalTheory.CompanionTheory.UnrDens.GramDiff
