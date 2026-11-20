import Mathlib
import Formalism.PeriodIntegrals.NMeasInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.ConjSubMulVec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureInverseContraction.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.HJMulVecGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MeasureDecomposition.ContinuousUMatApply

noncomputable section

open Matrix MeasureTheory NumberField

namespace PI.NMeasInv.UnitaryGroupMassFormula

section Inst

variable {n r : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ}

def wt (r : ℕ) (lam : ℝ) : Fin r → ℝ := fun b => lam ^ (r - b.val)

/- English proof (translation)
Unfold `wt`. Use `b.isLt` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation.
-/
theorem wt_ge (lam : ℝ) (hlam : 1 ≤ lam) (b : Fin r) : lam ≤ wt r lam b := by
  unfold wt
  have := b.isLt
  calc lam = lam ^ 1 := (pow_one _).symm
    _ ≤ lam ^ (r - b.val) := pow_le_pow_right₀ hlam (by omega)

/- English proof (translation)
Unfold `wt`. Use `b.isLt` as an intermediate fact. Use `c.isLt` as an intermediate fact. Establish `h : b.val < c.val` using `hbc`. Rewrite using `[← pow_succ']`.

Conclude with `pow_le_pow_right₀ hlam (by omega)`.
-/
theorem wt_step (lam : ℝ) (hlam : 1 ≤ lam) (b c : Fin r) (hbc : b < c) : lam * wt r lam c ≤ wt r lam b := by
  unfold wt
  have := b.isLt
  have := c.isLt
  have h : b.val < c.val := hbc
  rw [← pow_succ']
  exact pow_le_pow_right₀ hlam (by omega)

def Cmat (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℂ) := {M | ∀ i j, ‖(M - 1) i j‖ ≤ 1}

/- English proof (translation)
Establish `: Cmat n = Set.pi Set.univ (fun i : Fin n => Set.pi Set.univ (fun j : Fin n => Metric.closedBall ((1 : Matrix (Fin n) (Fin n) ℂ) i j) 1))`. Use extensionality with `M`. Use `show (∀ i j, ‖(M - 1) i j‖ ≤ 1) ↔ _`. Conclude with `⟨fun h i _ j _ => by simpa [Metric.mem_closedBall, dist_eq_norm, Matrix.sub_apply] using h i j, fun h i j => by`. Use `h i (Set.mem_univ _) j (Set.mem_univ _)` as an intermediate fact.

Simplify `this⟩` using `[Metric.mem_closedBall, dist_eq_norm, Matrix.sub_apply]`. Rewrite using `[this]`. Conclude with `isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _`.
-/
theorem isCompact_Cmat (n : ℕ) : IsCompact (Cmat n) := by
  have : Cmat n = Set.pi Set.univ (fun i : Fin n =>
      Set.pi Set.univ (fun j : Fin n => Metric.closedBall ((1 : Matrix (Fin n) (Fin n) ℂ) i j) 1)) := by
    ext M
    show (∀ i j, ‖(M - 1) i j‖ ≤ 1) ↔ _
    exact ⟨fun h i _ j _ => by simpa [Metric.mem_closedBall, dist_eq_norm, Matrix.sub_apply] using h i j,
      fun h i j => by
        have := h i (Set.mem_univ _) j (Set.mem_univ _)
        simpa [Metric.mem_closedBall, dist_eq_norm, Matrix.sub_apply] using this⟩
  rw [this]
  exact isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall _ _

def aUJ (hG : Gram ε e f) (s : Fin r → ℝ) (hs : ∀ b, s b ≠ 0) : Formalism.REAL.UJ ε :=
  ⟨⟨Amat ε e f s, Amat ε e f s⁻¹, Amat_mul_inv hG s hs, Amat_inv_mul hG s hs⟩, inUJ_A hG s hs⟩

/- English proof (translation)
Establish `hSb0 : ∀ y i, 0 ≤ Sb ε e f (Formalism.MainNotions.S.uMat g) y i` using `fun y i => by unfold Sb; positivity`. Use `set S : ℝ := ∑ i, ∑ j, Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j 1) i with hS`. Establish `hS0 : 0 ≤ S` using `Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hSb0 _ _`. Use `set lam : ℝ := 1 + S with hlamdef`. Establish `hlam : 1 ≤ lam` using `by linarith`.

Use `set t := wt r lam with htdef`. Establish `ht0 : ∀ b, 0 < t b` using `fun b => lt_of_lt_of_le one_pos (hlam.trans (wt_ge lam hlam b))`. Establish `hs : ∀ b, t⁻¹ b ≠ 0` using `fun b => by simp [(ht0 b).ne']`. Use `⟨t⁻¹, hs, fun i j => ?_⟩` and prove the remaining obligations. Establish `hmat : Formalism.MainNotions.S.uMat (aUJ hG t⁻¹ hs * g * (aUJ hG t⁻¹ hs)⁻¹) = Amat ε e f t⁻¹ * Formalism.MainNotions.S.uMat g * Amat ε e f t⁻¹⁻¹` using `rfl`.

Apply the tactic sequence `have hentry : ∀ K : Matrix (Fin n) (Fin n) ℂ, K i j = (K *ᵥ Pi.single j 1) i := fun K => by`. Simplify using `[mulVec, dotProduct, Pi.single_apply]`. Apply the tactic sequence `rw [hmat, hentry (Amat ε e f t⁻¹ * Formalism.MainNotions.S.uMat g * Amat ε e f t⁻¹⁻¹ - 1), conj_sub_mulVec hG t⁻¹ hs, inv_inv]`. Establish `hgg : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1` using `PI.ScMuExists.UnitaryGroupMassFormula.uMat_mul_inv g`. Use `(entry_bound hG t lam hlam (wt_ge lam hlam) (wt_step lam hlam) (PI.ScMuExists.UnitaryGroupMassFormula.uMat_inUJ g) hgg hgN hg'N _ i).trans ?_` and prove the remaining obligations.

Establish `h1 : Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j 1) i ≤ ∑ j', Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i` using `Finset.single_le_sum (f := fun j' => Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i) (fun j' _ => hSb0 _ _) (Finset.mem_univ j)`. Establish `h2 : ∑ j', Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i ≤ S` using `Finset.single_le_sum (f := fun i => ∑ j', Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i) (fun i _ => Finset.sum_nonneg fun _ _ => hSb0 _ _) (Finset.mem_univ i)`. Rewrite using `[inv_mul_le_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem local_contract (hG : Gram ε e f) {z : Fin n → ℂ} (g : Formalism.REAL.UJ ε)
    (hgN : InN ε e z (Formalism.MainNotions.S.uMat g)) (hg'N : InN ε e z (Formalism.MainNotions.S.uMat g⁻¹)) :
    ∃ s : Fin r → ℝ, ∃ hs : ∀ b, s b ≠ 0, Formalism.MainNotions.S.uMat (aUJ hG s hs * g * (aUJ hG s hs)⁻¹) ∈ Cmat n := by
  have hSb0 : ∀ y i, 0 ≤ Sb ε e f (Formalism.MainNotions.S.uMat g) y i := fun y i => by unfold Sb; positivity
  set S : ℝ := ∑ i, ∑ j, Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j 1) i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hSb0 _ _
  set lam : ℝ := 1 + S with hlamdef
  have hlam : 1 ≤ lam := by linarith
  set t := wt r lam with htdef
  have ht0 : ∀ b, 0 < t b := fun b => lt_of_lt_of_le one_pos (hlam.trans (wt_ge lam hlam b))
  have hs : ∀ b, t⁻¹ b ≠ 0 := fun b => by simp [(ht0 b).ne']
  refine ⟨t⁻¹, hs, fun i j => ?_⟩
  have hmat : Formalism.MainNotions.S.uMat (aUJ hG t⁻¹ hs * g * (aUJ hG t⁻¹ hs)⁻¹) =
      Amat ε e f t⁻¹ * Formalism.MainNotions.S.uMat g * Amat ε e f t⁻¹⁻¹ := rfl
  have hentry : ∀ K : Matrix (Fin n) (Fin n) ℂ, K i j = (K *ᵥ Pi.single j 1) i := fun K => by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [hmat, hentry (Amat ε e f t⁻¹ * Formalism.MainNotions.S.uMat g * Amat ε e f t⁻¹⁻¹ - 1), conj_sub_mulVec hG t⁻¹ hs,
    inv_inv]
  have hgg : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := PI.ScMuExists.UnitaryGroupMassFormula.uMat_mul_inv g
  refine (entry_bound hG t lam hlam (wt_ge lam hlam) (wt_step lam hlam) (PI.ScMuExists.UnitaryGroupMassFormula.uMat_inUJ g) hgg
    hgN hg'N _ i).trans ?_
  have h1 : Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j 1) i ≤
      ∑ j', Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i :=
    Finset.single_le_sum (f := fun j' => Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i)
      (fun j' _ => hSb0 _ _) (Finset.mem_univ j)
  have h2 : ∑ j', Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i ≤ S :=
    Finset.single_le_sum (f := fun i => ∑ j', Sb ε e f (Formalism.MainNotions.S.uMat g) (Pi.single j' 1) i)
      (fun i _ => Finset.sum_nonneg fun _ _ => hSb0 _ _) (Finset.mem_univ i)
  rw [inv_mul_le_iff₀ (by linarith)]
  linarith

/- English proof (translation)
Introduce `I r e f z hF`. Use `⟨Set.pi Set.univ (fun v => {g : Formalism.REAL.UJ (I.ε v) | Formalism.MainNotions.S.uMat g ∈ Cmat I.n}), isCompact_univ_pi fun v => (Formalism.REAL.isClosedEmbeddingMatrix I.n (I.ε v)).1.isCompact_preimage (isCompact_Cmat I.n), ?_⟩` and prove the remaining obligations. Introduce `m hm`. Establish `hfr` using `fun v => PI.ScMuExists.UnitaryGroupMassFormula.rv_frame (I := I) hF v`. Establish `hG : ∀ v, Gram (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a))` using `fun v => ⟨(hfr v).1, (hfr v).2.1, (hfr v).2.2.1⟩`.

Establish `hez : ∀ v a, hJ (I.ε v) (rv I v (e a)) (rv I v z) = 0` using `fun v a => ((hfr v).2.2.2.1 a).1`. Establish `hfz : ∀ v a, hJ (I.ε v) (rv I v (f a)) (rv I v z) = 0` using `fun v a => ((hfr v).2.2.2.1 a).2`. Establish `hm' : m⁻¹ ∈ Ninf I e z` using `(PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z).inv_mem hm`. Use `choose s hs hC using fun v => local_contract (hG v) (m v) (hm v) (hm' v)`. Use `⟨fun v => aUJ (hG v) (s v) (hs v), fun x hx v => ?_, fun x hx v => ?_, fun v _ => hC v⟩` and prove the remaining obligations.

Use `show InN _ _ _ (Amat _ _ _ (s v) * Formalism.MainNotions.S.uMat (x v) * Amat _ _ _ (s v)⁻¹)`. Conclude with `inN_A_conj (hG v) (s v) (hs v) (hez v) (hfz v) (hx v)`. Establish `hs' : ∀ b, (s v)⁻¹ b ≠ 0` using `fun b => by simp [hs v b]`. Use `inN_A_conj (hG v) (s v)⁻¹ hs' (hez v) (hfz v) (hx v)` as an intermediate fact. Rewrite `this` using `[inv_inv]`.

Use `show InN _ _ _ (Amat _ _ _ (s v)⁻¹ * Formalism.MainNotions.S.uMat (x v) * Amat _ _ _ (s v))`. Conclude with `this`.
-/
theorem measure_contraction_formula : Contract := by
  intro I r e f z hF
  refine ⟨Set.pi Set.univ (fun v => {g : Formalism.REAL.UJ (I.ε v) | Formalism.MainNotions.S.uMat g ∈ Cmat I.n}),
    isCompact_univ_pi fun v => (Formalism.REAL.isClosedEmbeddingMatrix I.n (I.ε v)).1.isCompact_preimage (isCompact_Cmat I.n), ?_⟩
  intro m hm
  have hfr := fun v => PI.ScMuExists.UnitaryGroupMassFormula.rv_frame (I := I) hF v
  have hG : ∀ v, Gram (I.ε v) (fun a => rv I v (e a)) (fun a => rv I v (f a)) := fun v =>
    ⟨(hfr v).1, (hfr v).2.1, (hfr v).2.2.1⟩
  have hez : ∀ v a, hJ (I.ε v) (rv I v (e a)) (rv I v z) = 0 := fun v a => ((hfr v).2.2.2.1 a).1
  have hfz : ∀ v a, hJ (I.ε v) (rv I v (f a)) (rv I v z) = 0 := fun v a => ((hfr v).2.2.2.1 a).2
  have hm' : m⁻¹ ∈ Ninf I e z := (PI.ScMuExists.UnitaryGroupMassFormula.NSub I e z).inv_mem hm
  choose s hs hC using fun v => local_contract (hG v) (m v) (hm v) (hm' v)
  refine ⟨fun v => aUJ (hG v) (s v) (hs v), fun x hx v => ?_, fun x hx v => ?_, fun v _ => hC v⟩
  · show InN _ _ _ (Amat _ _ _ (s v) * Formalism.MainNotions.S.uMat (x v) * Amat _ _ _ (s v)⁻¹)
    exact inN_A_conj (hG v) (s v) (hs v) (hez v) (hfz v) (hx v)
  · have hs' : ∀ b, (s v)⁻¹ b ≠ 0 := fun b => by simp [hs v b]
    have := inN_A_conj (hG v) (s v)⁻¹ hs' (hez v) (hfz v) (hx v)
    rw [inv_inv] at this
    show InN _ _ _ (Amat _ _ _ (s v)⁻¹ * Formalism.MainNotions.S.uMat (x v) * Amat _ _ _ (s v))
    exact this

end Inst

end PI.NMeasInv.UnitaryGroupMassFormula
