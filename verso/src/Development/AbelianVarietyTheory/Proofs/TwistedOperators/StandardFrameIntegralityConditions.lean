import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairTable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section
namespace GlobalTheory.SeeConjRead.DetUnit

open Classical

section Val
variable {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)

/- English proof (translation)
Break down `Int.units_eq_one_or (Equiv.Perm.sign s) with h | h` into its components or cases. Rewrite using `[h, one_smul]`. Rewrite using `[h, Units.neg_smul, one_smul, Valuation.map_neg]`.
-/
theorem v_sign_smul {n : ℕ} (s : Equiv.Perm (Fin n)) (x : K) : v (Equiv.Perm.sign s • x) = v x := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]
  · rw [h, Units.neg_smul, one_smul, Valuation.map_neg]

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `Valuation.map_sum_le v fun s _ => ?_` and prove the remaining obligations. Rewrite using `[v_sign_smul, map_prod]`. Conclude with `Finset.prod_le_one' fun i _ => h _ _`.
-/
theorem v_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : ∀ i j, v (M i j) ≤ 1) : v M.det ≤ 1 := by
  rw [Matrix.det_apply]
  refine Valuation.map_sum_le v fun s _ => ?_
  rw [v_sign_smul, map_prod]
  exact Finset.prod_le_one' fun i _ => h _ _

/- English proof (translation)
Establish `hle : ∀ i j, v (M i j) ≤ 1`. Introduce `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Establish `h1` using `h i i`.

Rewrite `h1` using `[if_pos rfl]`. Establish `: M i i = (M i i - d i) + d i` using `by ring`. Rewrite using `[this]`. Conclude with `(Valuation.map_add v _ _).trans (max_le h1.le (hd i).le)`. Establish `h1` using `h i j`.

Rewrite `h1` using `[if_neg hij, sub_zero]`. Conclude with `h1.le`. Establish `hdiag : ∀ i, v (M i i) = 1`. Introduce `i`. Establish `h1` using `h i i`.

Rewrite `h1` using `[if_pos rfl]`. Establish `: M i i = (M i i - d i) + d i` using `by ring`. Rewrite using `[this, Valuation.map_add_eq_of_lt_right v (by rw [hd i]; exact h1), hd i]`. Rewrite using `[Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]`. Establish `hmain : v (Equiv.Perm.sign (1 : Equiv.Perm (Fin n)) • ∏ i, M ((1 : Equiv.Perm (Fin n)) i) i) = 1`.

Rewrite using `[v_sign_smul, map_prod]`. Conclude with `Finset.prod_eq_one fun i _ => hdiag i`. Establish `hrest : v (∑ s ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)), Equiv.Perm.sign s • ∏ i, M (s i) i) < 1`. Use `Valuation.map_sum_lt v one_ne_zero fun s hs => ?_` and prove the remaining obligations. Establish `hs1 : s ≠ 1` using `Finset.ne_of_mem_erase hs`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, s i ≠ i := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `hs1 (Equiv.ext hc)`. Rewrite using `[v_sign_smul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`.

Establish `h1` using `h (s i) i`. Rewrite `h1` using `[if_neg hi, sub_zero]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun j _ => hle _ _)) h1`. Rewrite using `[Valuation.map_add_eq_of_lt_left v (by rw [hmain]; exact hrest), hmain]`.
-/
theorem v_det_eq_one {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (d : Fin n → K) (hd : ∀ a, v (d a) = 1)
    (h : ∀ a b, v (M a b - if a = b then d a else 0) < 1) : v M.det = 1 := by
  have hle : ∀ i j, v (M i j) ≤ 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have h1 := h i i
      rw [if_pos rfl] at h1
      have : M i i = (M i i - d i) + d i := by ring
      rw [this]
      exact (Valuation.map_add v _ _).trans (max_le h1.le (hd i).le)
    · have h1 := h i j
      rw [if_neg hij, sub_zero] at h1
      exact h1.le
  have hdiag : ∀ i, v (M i i) = 1 := by
    intro i
    have h1 := h i i
    rw [if_pos rfl] at h1
    have : M i i = (M i i - d i) + d i := by ring
    rw [this, Valuation.map_add_eq_of_lt_right v (by rw [hd i]; exact h1), hd i]
  rw [Matrix.det_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : Equiv.Perm (Fin n)))]
  have hmain : v (Equiv.Perm.sign (1 : Equiv.Perm (Fin n)) • ∏ i, M ((1 : Equiv.Perm (Fin n)) i) i) = 1 := by
    rw [v_sign_smul, map_prod]
    exact Finset.prod_eq_one fun i _ => hdiag i
  have hrest : v (∑ s ∈ Finset.univ.erase (1 : Equiv.Perm (Fin n)), Equiv.Perm.sign s • ∏ i, M (s i) i) < 1 := by
    refine Valuation.map_sum_lt v one_ne_zero fun s hs => ?_
    have hs1 : s ≠ 1 := Finset.ne_of_mem_erase hs
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ i := by
      by_contra hc
      push_neg at hc
      exact hs1 (Equiv.ext hc)
    rw [v_sign_smul, map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have h1 := h (s i) i
    rw [if_neg hi, sub_zero] at h1
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (Finset.prod_le_one' fun j _ => hle _ _)) h1
  rw [Valuation.map_add_eq_of_lt_left v (by rw [hmain]; exact hrest), hmain]

end Val

end GlobalTheory.SeeConjRead.DetUnit

namespace GlobalTheory.SeeConjRead.DetUnit

/- English proof (translation)
Use `(GlobalTheory.StdFrames.mem_OA_iff x).1 hx Q` as an intermediate fact. Rewrite `this` using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Then use the resulting hypothesis.
-/
theorem val_le_of_int {D : D7} (Q : Pl D.host.E) (x : EAf D) (hx : x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    Valued.v (GlobalTheory.StdFrames.cpt Q x) ≤ 1 := by
  have := (GlobalTheory.StdFrames.mem_OA_iff x).1 hx Q
  rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at this

/- English proof (translation)
Rewrite using `[RingHom.map_det]`. Conclude with `v_det_le _ _ fun i j => val_le_of_int Q _ (hM i j)`.
-/
theorem val_det_le {D : D7} {n : ℕ} (Q : Pl D.host.E) (M : Matrix (Fin n) (Fin n) (EAf D))
    (hM : ∀ i j, M i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) : Valued.v (GlobalTheory.StdFrames.cpt Q M.det) ≤ 1 := by
  rw [RingHom.map_det]
  exact v_det_le _ _ fun i j => val_le_of_int Q _ (hM i j)

/- English proof (translation)
Introduce `D n β₀ J U W Q d hG hA hB hd hX`. Use `set A := (β₀⁻¹).val * U with hAdef`. Use `set B := (β₀⁻¹).val * W with hBdef`. Use `set G := Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val with hGdef`. Establish `hU : U = β₀.val * A` using `by rw [hAdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`.

Establish `hW : W = β₀.val * B` using `by rw [hBdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Establish `hX' : Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W = Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A * G * B`. Rewrite using `[hGdef, hU, hW, GlobalTheory.StdFrames.cT_mul']`. Simplify using `only [Matrix.mul_assoc]`. Establish `h1 : Valued.v (GlobalTheory.StdFrames.cpt Q (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W).det) = 1`.

Rewrite using `[RingHom.map_det]`. Use `v_det_eq_one _ _ (fun a => GlobalTheory.StdFrames.cpt Q (d a)) hd fun a b => ?_` and prove the remaining obligations. Use `hX a b` as an intermediate fact. Unfold `SmallAt at this`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply]`.

Use `split_ifs at this ⊢ with hab`. Rewrite `this` using `[map_sub]`. Then use the resulting hypothesis. Rewrite `this`, the goal using `[sub_zero]`. Then use the resulting hypothesis. Rewrite `h1` using `[hX', Matrix.det_mul, Matrix.det_mul]`. Simplify using `only [map_mul] at h1`.

Establish `ha : Valued.v (GlobalTheory.StdFrames.cpt Q (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A).det) ≤ 1` using `val_det_le Q _ fun i j => Formalism.UG.P.csDual_sig_mem _ (hA j i)`. Establish `hg : Valued.v (GlobalTheory.StdFrames.cpt Q G.det) ≤ 1` using `val_det_le Q _ hG`. Establish `hb : Valued.v (GlobalTheory.StdFrames.cpt Q B.det) ≤ 1` using `val_det_le Q _ hB`. Use `le_antisymm hb ?_` and prove the remaining obligations. Rewrite using `[← h1]`.

Conclude with `mul_le_of_le_one_left' (mul_le_one' ha hg)`.
-/
theorem det_unit : ∀ {D : D7} {n : ℕ} (β₀ : GL (Fin n) (EAf D)) (J U W : Matrix (Fin n) (Fin n) (EAf D)) (Q : Pl D.host.E) (d : Fin n → EAf D), (∀ i j, (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * U) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ i j, ((β₀⁻¹).val * W) i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → (∀ a, Valued.v (GlobalTheory.StdFrames.cpt Q (d a)) = 1) → (∀ a b, SmallAt Q ((Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W) a b - if a = b then d a else 0)) → Valued.v (GlobalTheory.StdFrames.cpt Q ((β₀⁻¹).val * W).det) = 1 := by
  intro D n β₀ J U W Q d hG hA hB hd hX
  set A := (β₀⁻¹).val * U with hAdef
  set B := (β₀⁻¹).val * W with hBdef
  set G := Formalism.UG.cT (GlobalTheory.StdFrames.sg D) β₀.val * J * β₀.val with hGdef
  have hU : U = β₀.val * A := by rw [hAdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hW : W = β₀.val * B := by rw [hBdef, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hX' : Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W = Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A * G * B := by
    rw [hGdef, hU, hW, GlobalTheory.StdFrames.cT_mul']
    simp only [Matrix.mul_assoc]
  have h1 : Valued.v (GlobalTheory.StdFrames.cpt Q (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) U * J * W).det) = 1 := by
    rw [RingHom.map_det]
    refine v_det_eq_one _ _ (fun a => GlobalTheory.StdFrames.cpt Q (d a)) hd fun a b => ?_
    have := hX a b
    unfold SmallAt at this
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    split_ifs at this ⊢ with hab
    · rwa [map_sub] at this
    · rwa [sub_zero] at this ⊢
  rw [hX', Matrix.det_mul, Matrix.det_mul] at h1
  simp only [map_mul] at h1
  have ha : Valued.v (GlobalTheory.StdFrames.cpt Q (Formalism.UG.cT (GlobalTheory.StdFrames.sg D) A).det) ≤ 1 :=
    val_det_le Q _ fun i j => Formalism.UG.P.csDual_sig_mem _ (hA j i)
  have hg : Valued.v (GlobalTheory.StdFrames.cpt Q G.det) ≤ 1 := val_det_le Q _ hG
  have hb : Valued.v (GlobalTheory.StdFrames.cpt Q B.det) ≤ 1 := val_det_le Q _ hB
  refine le_antisymm hb ?_
  rw [← h1]
  exact mul_le_of_le_one_left' (mul_le_one' ha hg)

end GlobalTheory.SeeConjRead.DetUnit
