import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialOperatorFderivFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialOperatorSchwartzSeminormBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeBoundByPartialsStatement

open GlobalTheory.SliceSchwartz
open scoped ContDiff

noncomputable section

namespace GlobalTheory.SliceOp
open GlobalTheory.SliceSchwartz

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] [Fintype κ₁']

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro P f`. Conclude with `contDiff_zero.2 (GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f).1.continuous`. Consider the case `succ n ih`. Introduce `P f`.

Take `⟨hd, hf⟩` from `GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f`. Establish `e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1` using `by push_cast; rfl`. Rewrite using `[e, contDiff_succ_iff_fderiv_apply]`. Use `⟨hd, by simp, fun v => ?_⟩` and prove the remaining obligations. Establish `: (fun s => fderiv ℝ (qOp P f) s v) = fun s => qOp P (pd (padL (κ'` using `κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s :=`.

Use function extensionality and compare the values at `fun s => hf s v`. Rewrite using `[this]`. Conclude with `(ih _ _).add (ih _ _)`.
-/
theorem contDiff_qOp_nat (n : ℕ) : ∀ (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ), ContDiff ℝ n (qOp P f) := by
  induction n with
  | zero => intro P f; exact contDiff_zero.2 (GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f).1.continuous
  | succ n ih =>
    intro P f
    obtain ⟨hd, hf⟩ := GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f
    have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [e, contDiff_succ_iff_fderiv_apply]
    refine ⟨hd, by simp, fun v => ?_⟩
    have : (fun s => fderiv ℝ (qOp P f) s v) = fun s =>
        qOp P (pd (padL (κ' := κ') (v ∘ Sum.inl)) f) s + qOp ((pd (v ∘ Sum.inr)).comp P) f s :=
      funext fun s => hf s v
    rw [this]
    exact (ih _ _).add (ih _ _)

/- English proof (translation)
The claim follows from `contDiff_infty.2 fun n => contDiff_qOp_nat n P f`.
-/
theorem contDiff_qOp (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ)
    (f : SchwartzMap (κ ⊕ κ' → V) ℂ) : ContDiff ℝ ∞ (qOp P f) :=
  contDiff_infty.2 fun n => contDiff_qOp_nat n P f

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `P k`. Take `⟨s, C, hC, h⟩` from `GlobalTheory.T.partial_operator_schwartz_seminorm_bound V κ κ' κ₁' P k`. Conclude with `⟨s, C, hC, fun f z => by rw [norm_iteratedFDeriv_zero]; exact h f z⟩`.

Consider the case `succ n ih`. Introduce `P k`. Take `⟨CE, hCE, hE⟩` from `GlobalTheory.T.iterated_derivative_bound_by_partials (κ ⊕ κ₁' → V)`. Use `set b := Module.finBasis ℝ (κ ⊕ κ₁' → V)`. Take `⟨s1, C1, hC1, h1⟩` from `ih P k`.

Use `choose s1' C1' hC1' h1' using fun i => clm_sup_bound (pd (padL (κ' := κ') (b i ∘ Sum.inl))) s1`. Use `choose s2 C2 hC2 h2 using fun i => ih ((pd (b i ∘ Sum.inr)).comp P) k`. Use `⟨Finset.univ.sup (fun i => s1' i ∪ s2 i), CE * ∑ i, (C1 * C1' i + C2 i), mul_nonneg hCE (Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg hC1 (hC1' i)) (hC2 i)), fun f z => ?_⟩` and prove the remaining obligations. Use `set p := schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ`. Use `set S := (Finset.univ.sup (fun i => s1' i ∪ s2 i)).sup p f`.

Establish `hmono : ∀ i (t : Finset (ℕ × ℕ)), t ⊆ s1' i ∪ s2 i → t.sup p f ≤ S`. Introduce `i t ht`. Conclude with `Seminorm.le_def.1 (Finset.sup_mono (ht.trans (Finset.le_sup (f := fun i => s1' i ∪ s2 i) (Finset.mem_univ i)))) f`. Establish `key : ∀ i, ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖ ≤ (C1 * C1' i + C2 i) * S`. Introduce `i`.

Establish `hfun : (fun w => fderiv ℝ (qOp P f) w (b i)) = qOp P (pd (padL (κ'` using `κ') (b i ∘ Sum.inl)) f) + qOp ((pd (b i ∘ Sum.inr)).comp P) f :=`. Use function extensionality and compare the values at `fun w => (GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f).2 w (b i)`. Rewrite using `[hfun, iteratedFDeriv_add_apply (contDiff_qOp_nat n _ _).contDiffAt (contDiff_qOp_nat n _ _).contDiffAt]`. Establish `e1` using `h1 (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f) z`. Establish `e1'` using `h1' i f`.

Establish `e2` using `h2 i f z`. Establish `m1` using `hmono i (s1' i) Finset.subset_union_left`. Establish `m2` using `hmono i (s2 i) Finset.subset_union_right`. Establish `hz : 0 ≤ ‖z‖ ^ k` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← mul_add]`. Conclude with `mul_le_mul_of_nonneg_left (norm_add_le _ _) hz`. Use `_ ≤ C1 * (C1' i * S) + C2 i * S := by`. Use `add_le_add (e1.trans (mul_le_mul_of_nonneg_left (e1'.trans (mul_le_mul_of_nonneg_left m1 (hC1' i))) hC1)) (e2.trans (mul_le_mul_of_nonneg_left m2 (hC2 i)))` and prove the remaining obligations. Use `_ = (C1 * C1' i + C2 i) * S := by ring`.

Establish `hz : 0 ≤ ‖z‖ ^ k` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ CE * ∑ i, (C1 * C1' i + C2 i) * S := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => key i) hCE`. Use `_ = (CE * ∑ i, (C1 * C1' i + C2 i)) * S := by rw [mul_assoc, Finset.sum_mul]`.
-/
theorem decay_qOp (n : ℕ) : ∀ (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ) (k : ℕ),
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (z : κ ⊕ κ₁' → V),
      ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P f) z‖ ≤ C * s.sup (schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ) f := by
  induction n with
  | zero =>
    intro P k
    obtain ⟨s, C, hC, h⟩ := GlobalTheory.T.partial_operator_schwartz_seminorm_bound V κ κ' κ₁' P k
    exact ⟨s, C, hC, fun f z => by rw [norm_iteratedFDeriv_zero]; exact h f z⟩
  | succ n ih =>
    intro P k
    obtain ⟨CE, hCE, hE⟩ := GlobalTheory.T.iterated_derivative_bound_by_partials (κ ⊕ κ₁' → V)
    set b := Module.finBasis ℝ (κ ⊕ κ₁' → V)
    obtain ⟨s1, C1, hC1, h1⟩ := ih P k
    choose s1' C1' hC1' h1' using fun i => clm_sup_bound (pd (padL (κ' := κ') (b i ∘ Sum.inl))) s1
    choose s2 C2 hC2 h2 using fun i => ih ((pd (b i ∘ Sum.inr)).comp P) k
    refine ⟨Finset.univ.sup (fun i => s1' i ∪ s2 i), CE * ∑ i, (C1 * C1' i + C2 i),
      mul_nonneg hCE (Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg hC1 (hC1' i)) (hC2 i)), fun f z => ?_⟩
    set p := schwartzSeminormFamily ℂ (κ ⊕ κ' → V) ℂ
    set S := (Finset.univ.sup (fun i => s1' i ∪ s2 i)).sup p f
    have hmono : ∀ i (t : Finset (ℕ × ℕ)), t ⊆ s1' i ∪ s2 i → t.sup p f ≤ S := by
      intro i t ht
      exact Seminorm.le_def.1 (Finset.sup_mono (ht.trans
        (Finset.le_sup (f := fun i => s1' i ∪ s2 i) (Finset.mem_univ i)))) f
    have key : ∀ i, ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖
        ≤ (C1 * C1' i + C2 i) * S := by
      intro i
      have hfun : (fun w => fderiv ℝ (qOp P f) w (b i)) =
          qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f) + qOp ((pd (b i ∘ Sum.inr)).comp P) f :=
        funext fun w => (GlobalTheory.T.partial_operator_fderiv_formula V κ κ' κ₁' P f).2 w (b i)
      rw [hfun, iteratedFDeriv_add_apply (contDiff_qOp_nat n _ _).contDiffAt (contDiff_qOp_nat n _ _).contDiffAt]
      have e1 := h1 (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f) z
      have e1' := h1' i f
      have e2 := h2 i f z
      have m1 := hmono i (s1' i) Finset.subset_union_left
      have m2 := hmono i (s2 i) Finset.subset_union_right
      have hz : 0 ≤ ‖z‖ ^ k := by positivity
      calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f)) z +
              iteratedFDeriv ℝ n (qOp ((pd (b i ∘ Sum.inr)).comp P) f) z‖
          ≤ ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp P (pd (padL (κ' := κ') (b i ∘ Sum.inl)) f)) z‖ +
              ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (qOp ((pd (b i ∘ Sum.inr)).comp P) f) z‖ := by
            rw [← mul_add]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) hz
        _ ≤ C1 * (C1' i * S) + C2 i * S := by
            refine add_le_add (e1.trans (mul_le_mul_of_nonneg_left (e1'.trans
              (mul_le_mul_of_nonneg_left m1 (hC1' i))) hC1)) (e2.trans (mul_le_mul_of_nonneg_left m2 (hC2 i)))
        _ = (C1 * C1' i + C2 i) * S := by ring
    have hz : 0 ≤ ‖z‖ ^ k := by positivity
    calc ‖z‖ ^ k * ‖iteratedFDeriv ℝ (n + 1) (qOp P f) z‖
        ≤ ‖z‖ ^ k * (CE * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖) :=
          mul_le_mul_of_nonneg_left (hE _ (contDiff_qOp P f) n z) hz
      _ = CE * ∑ i, ‖z‖ ^ k * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ (qOp P f) w (b i)) z‖ := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; congr 1; funext i; ring
      _ ≤ CE * ∑ i, (C1 * C1' i + C2 i) * S :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => key i) hCE
      _ = (CE * ∑ i, (C1 * C1' i + C2 i)) * S := by rw [mul_assoc, Finset.sum_mul]

end GlobalTheory.SliceOp

open GlobalTheory.SliceOp in
/- English proof (translation)
Introduce `V _ _ _ κ κ' κ₁' _ _ _ P`. Use `⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f => qOp P f) ?_ ?_ ?_ ?_, fun f s => rfl⟩` and prove the remaining obligations. Introduce `f g s`. Simplify using `only [qOp, ← sliceRL_apply, map_add, SchwartzMap.add_apply]`. Introduce `a f s`.

Simplify using `only [qOp, ← sliceRL_apply, map_smul, SchwartzMap.smul_apply, RingHom.id_apply]`. Introduce `f`. Conclude with `contDiff_qOp P f`. Introduce and unpack `⟨k, n⟩`. Conclude with `decay_qOp n P k`.
-/
theorem GlobalTheory.SliceOp.exists_tensor_clm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (κ κ' κ₁' : Type)
    [Fintype κ] [Fintype κ'] [Fintype κ₁'] (P : SchwartzMap (κ' → V) ℂ →L[ℂ] SchwartzMap (κ₁' → V) ℂ),
    ∃ Q : SchwartzMap (κ ⊕ κ' → V) ℂ →L[ℂ] SchwartzMap (κ ⊕ κ₁' → V) ℂ,
      ∀ (f : SchwartzMap (κ ⊕ κ' → V) ℂ) (s : κ ⊕ κ₁' → V), Q f s = P (sliceR f (s ∘ Sum.inl)) (s ∘ Sum.inr) := by
  intro V _ _ _ κ κ' κ₁' _ _ _ P
  refine ⟨SchwartzMap.mkCLM (σ := RingHom.id ℂ) (fun f => qOp P f) ?_ ?_ ?_ ?_, fun f s => rfl⟩
  · intro f g s
    simp only [qOp, ← sliceRL_apply, map_add, SchwartzMap.add_apply]
  · intro a f s
    simp only [qOp, ← sliceRL_apply, map_smul, SchwartzMap.smul_apply, RingHom.id_apply]
  · intro f; exact contDiff_qOp P f
  · rintro ⟨k, n⟩; exact decay_qOp n P k
