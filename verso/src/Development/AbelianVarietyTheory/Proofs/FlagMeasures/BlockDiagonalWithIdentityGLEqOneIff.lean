import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMulStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BernsteinZelevinskyDerivativeGLnEqTwistedSumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicClassFunBlockDiagonalEqSumDerivativesStatement

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

noncomputable section

namespace GlobalTheory.GLm.GGSum

variable {g : ℕ} [Fact g.Prime]

def dirac (g n : ℕ) [Fact g.Prime] : Gn g n → ℂ := fun x => if x = 1 then 1 else 0

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tri_add (a b : ℕ) : (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + (a * b + b * (b - 1) / 2) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc a b 1, Nat.triangle_succ, Nat.triangle_succ, ih]; ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem conj_eq_one {G : Type} [Group G] (p x : G) : p * x * p⁻¹ = 1 ↔ x = 1 := by
  constructor
  · intro h
    have : x = p⁻¹ * (p * x * p⁻¹) * p := by group
    rw [this, h]; group
  · rintro rfl; group

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem dirac_class (n : ℕ) : IsClass (dirac g n) := by
  intro x y
  simp only [dirac, conj_eq_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem gg_class (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : IsClass (gg ψ n) := by
  intro x z
  unfold gg
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft z) _ _ ?_).symm
  intro y
  have : (z * y)⁻¹ * (z * x * z⁻¹) * (z * y) = y⁻¹ * x * y := by group
  simp only [Equiv.coe_mulLeft, this]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem wh_dirac (ψ : AddChar (ZMod g) ℂ) (n : ℕ) :
    wh ψ (dirac g n) = ((g : ℂ) ^ (n * (n - 1) / 2))⁻¹ := by
  rw [← (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g n 0 0 ψ).2.1]
  simp [wh, tr, dirac]

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem wh_mul_left (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  simp only [wh, tr, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (s : Finset ℕ) (f : ℕ → Gn g n → ℂ) :
    wh ψ (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, wh ψ (f i) := by
  simp only [wh, tr, Finset.mul_sum]
  exact Finset.sum_comm

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem wh_hc (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (a b n : ℕ) (hn : n = a + b) (α : Gn g a → ℂ)
    (β : Gn g b → ℂ) (hα : IsClass α) (hβ : IsClass β) : wh ψ (hc a b α β n) = wh ψ α * wh ψ β := by
  unfold hc
  rw [GlobalTheory.T.whittakerDimension_harishChandraInduction_mul g ψ hψ a b n hn _ (fun y x z => by simp only [hα x z]) (fun x y z => by simp only [hβ y z])]
  simp only [wh_mul_left]
  rw [mul_comm, ← wh_mul_left]
  simp only [mul_comm]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem entN_one (n a b : ℕ) (ha : a < n) (hb : b < n) : entN (1 : Mt g n) a b = if a = b then 1 else 0 := by
  simp [entN, ha, hb, Matrix.one_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem tl_one (i n : ℕ) (hi : i ≤ n) : tl i (1 : Mt g n) = 1 := by
  ext a b
  rw [tl, entN_one n a b (by omega) (by omega), Matrix.one_apply]
  simp [Fin.ext_iff]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem inR_one (i n : ℕ) (hi : i ≤ n) : InR i (1 : Mt g n) := by
  refine ⟨fun a b h1 h2 => Matrix.one_apply_ne (fun h => by subst h; omega), fun a b => ?_⟩
  have ha := a.2
  have hb := b.2
  rw [br, entN_one n _ _ (by omega) (by omega)]
  refine ⟨fun h => if_neg ?_, fun h => if_pos (by rw [h])⟩
  have : (b : ℕ) < a := h
  omega

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem supFrom_one (i n : ℕ) : supFrom i (1 : Mt g n) = 0 := by
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Finset.mem_Ico] at hj
  rw [entN_one n _ _ (by omega) (by omega), if_neg (by omega)]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem der_dirac (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (hi : i ≤ n) :
    der ψ i (dirac g n) =
      fun h => ((g : ℂ) ^ (i * (n - i) + (n - i) * (n - i - 1) / 2))⁻¹ * dirac g i h := by
  funext h
  rw [GlobalTheory.T.bernsteinZelevinskyDerivativeGLn_eq_twisted_sum g ψ i n _ h hi]
  congr 1
  rw [Finset.sum_eq_single (1 : Gn g n)]
  · have e : ((1 : Mt g i) = (h : Mt g i)) ↔ h = 1 :=
      ⟨fun e => Units.ext e.symm, fun e => by rw [e]; rfl⟩
    simp only [Units.val_one, inR_one i n hi, tl_one i n hi, supFrom_one, dirac, true_and, e]
    simp
  · intro x _ hx
    simp [dirac, hx]
  · simp

def dM {k : ℕ} (h : Mt g k) : Mt g (k + 1) :=
  fun i j => if (i : ℕ) < k ∧ (j : ℕ) < k then entN h i j else (1 : Mt g (k + 1)) i j

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem dM_cc {k : ℕ} (h : Mt g k) (i j : Fin k) : dM h i.castSucc j.castSucc = h i j := by
  simp [dM, entN]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem dM_lc {k : ℕ} (h : Mt g k) (j : Fin k) : dM h (Fin.last k) j.castSucc = 0 := by
  simp [dM, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem dM_cl {k : ℕ} (h : Mt g k) (j : Fin k) : dM h j.castSucc (Fin.last k) = 0 := by
  simp [dM, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem dM_ll {k : ℕ} (h : Mt g k) : dM h (Fin.last k) (Fin.last k) = 1 := by
  simp [dM]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem dM_mul {k : ℕ} (h h' : Mt g k) : dM h * dM h' = dM (h * h') := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, dM_cc, dM_lc, dM_cl, dM_ll]

/- English proof (translation)
By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem dM_one (k : ℕ) : dM (1 : Mt g k) = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [dM_cc, dM_lc, dM_cl, dM_ll, Matrix.one_apply, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne']

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem blockDiagonalWithIdentityGL_eq_one_iff {k : ℕ} (h : Gn g k) : diag1 h (k + 1) = 1 ↔ h = 1 := by
  have hu : IsUnit (dM (h : Mt g k)) :=
    ⟨⟨dM (h : Mt g k), dM ((h⁻¹ : Gn g k) : Mt g k), by rw [dM_mul, Units.mul_inv, dM_one],
      by rw [dM_mul, Units.inv_mul, dM_one]⟩, rfl⟩
  have hc : ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1)) = dM (h : Mt g k) := by
    change ((toG (dM (h : Mt g k)) : Gn g (k + 1)) : Mt g (k + 1)) = _
    rw [toG, dif_pos hu]; rfl
  constructor
  · intro e
    rw [e] at hc
    apply Units.ext
    ext i j
    rw [← dM_cc (h : Mt g k) i j, ← hc]
    simp [Matrix.one_apply]
  · intro e
    apply Units.ext
    rw [hc, e]
    exact dM_one k

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the hypotheses and the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the indicated hypotheses using the stated equalities. Clear the denominators using the available nonvanishing facts.

A detailed English derivation is pending.
-/
theorem sum_wh_gg : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ k : ℕ,
    ∑ j ∈ Finset.range (k + 1), wh ψ (gg ψ j) = (g : ℂ) ^ k := by
  intro g hg ψ hψ k
  have hg0 : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hg.out.ne_zero
  have h1 : dirac g k = fun h => ∑ i ∈ Finset.range (k + 1),
      hc i (k - i) (der ψ i (dirac g (k + 1))) (gg ψ (k - i)) k h := by
    funext h
    rw [← GlobalTheory.T.mirabolicClassFun_blockDiagonal_eq_sum_derivatives g ψ hψ k _ (fun p x _ _ => dirac_class _ x p) h]
    simp only [dirac, blockDiagonalWithIdentityGL_eq_one_iff]
  have h2 := wh_dirac ψ k
  rw [h1, wh_sum] at h2
  have h3 : ∀ i ∈ Finset.range (k + 1),
      wh ψ (hc i (k - i) (der ψ i (dirac g (k + 1))) (gg ψ (k - i)) k) =
        ((g : ℂ) ^ (k * (k - 1) / 2 + k))⁻¹ * wh ψ (gg ψ (k + 1 - 1 - i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [der_dirac ψ i (k + 1) hi.le, wh_hc ψ hψ i (k - i) k (by omega) _ _
      (fun x y => by simp only [dirac_class i x y]) (gg_class ψ _), wh_mul_left, wh_dirac, ← mul_inv, ← pow_add,
      add_comm _ (i * (i - 1) / 2), ← tri_add, Nat.add_sub_cancel' hi.le, Nat.triangle_succ]
    rfl
  rw [Finset.sum_congr rfl h3, ← Finset.mul_sum, Finset.sum_range_reflect (fun j => wh ψ (gg ψ j)), pow_add] at h2
  field_simp at h2
  exact h2

end GlobalTheory.GLm.GGSum
