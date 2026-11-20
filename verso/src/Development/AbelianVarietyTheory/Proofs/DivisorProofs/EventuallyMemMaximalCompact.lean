import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicInt

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.IntegralAE

open GlobalTheory.InertSph (latAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem`. Consider the case `exact _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem`. Consider the case `(apply _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem ..)`.
-/
theorem exists_zsmul_mem {L : Submodule (𝓞 E) (Fin d → E)} (hL : L.IsLattice E) (w : Fin d → E) :
    ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  first
  | exact @_root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem
  | exact _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem
  | (apply _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraicIntegerMultiple.exists_int_smul_mem ..)

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨b, hb, hb', y, hy, rfl⟩` from `hz`. Use `AddSubgroup.subset_closure ⟨a * b, fun u hu => ?_, ?_, y, hy, smul_smul _ _ _⟩` and prove the remaining obligations. Rewrite using `[smul_eq_mul, mul_left_comm, ← smul_eq_mul u, hb u hu, mul_zero]`.

Rewrite using `[map_mul]`. Conclude with `mul_mem ha hb'`. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add _ _ _ _ h1 h2 => rw [smul_add]`.

Conclude with `add_mem h1 h2`. Consider the case `neg _ _ h1 => rw [smul_neg]`. Conclude with `neg_mem h1`.
-/
theorem smul_mem_latAt (W : Spc F E d) (v : Pl F) {a : AF F} (ha : evFin F v a ∈ v.adicCompletionIntegers F)
    {z : Fin d → AE F E} (hz : z ∈ latAt W v) : a • z ∈ latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, hb', y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, fun u hu => ?_, ?_, y, hy, smul_smul _ _ _⟩
    · rw [smul_eq_mul, mul_left_comm, ← smul_eq_mul u, hb u hu, mul_zero]
    · rw [map_mul]; exact mul_mem ha hb'
  | zero => rw [smul_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg _ _ h1 => rw [smul_neg]; exact neg_mem h1

/- English proof (translation)
Establish `hadd : ∀ x y : Fin d → AE F E, (∀ᶠ v in cofinite, partFin v x ∈ latAt W v) → (∀ᶠ v in cofinite, partFin v y ∈ latAt W v) → ∀ᶠ v in cofinite, partFin v (x + y) ∈ latAt W v` using `fun x y hx hy => (hx.and hy).mono fun v h => by`. Rewrite using `[partFin, smul_add]`. Conclude with `add_mem h.1 h.2`. Establish `hzero : ∀ᶠ v in cofinite, partFin v (0 : Fin d → AE F E) ∈ latAt W v` using `Eventually.of_forall fun v => by rw [partFin, smul_zero]; exact zero_mem _`. Establish `hs : ∀ (i : Fin d) (t : AE F E), ∀ᶠ v in cofinite, partFin v (Pi.single i t : Fin d → AE F E) ∈ latAt W v`.

Introduce `i t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simpa using hzero`. Consider the case `add s t h1 h2 => rw [Pi.single_add]`. Conclude with `hadd _ _ h1 h2`.

Consider the case `tmul a c`. Take `⟨N, hN, hy⟩` from `exists_zsmul_mem hL (Pi.single i c : Fin d → E)`. Establish `hNF : (N : F) ≠ 0` using `Int.cast_ne_zero.2 hN`. Use `set b : AF F := (N : F)⁻¹ • a with hb`. Establish `hint : ∀ᶠ v in cofinite, evFin F v b ∈ v.adicCompletionIntegers F` using `b.2.2`.

Establish `e : (Pi.single i (a ⊗ₜ[F] c) : Fin d → AE F E) = b • fun j => inclR (F` using `F) (AF F) ((N • (Pi.single i c : Fin d → E)) j) := by`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `only [Pi.single_eq_same, Pi.smul_apply]`.

Express the relevant statement in the definitionally equal form `_ = b • ((1 : AF F) ⊗ₜ[F] (N • c))`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one, hb, TensorProduct.smul_tmul, ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hNF, one_smul]`. Simplify using `[Pi.single_eq_of_ne hj]`. Use `hint.mono fun v hv => ?_` and prove the remaining obligations. Rewrite using `[e, partFin, smul_comm]`.

Use `smul_mem_latAt W v hv (AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v 1, ?_, _, hy, rfl⟩)` and prove the remaining obligations. Rewrite using `[GlobalTheory.LatVac.evFin_liftV]`. Conclude with `one_mem _`. Rewrite using `[← Finset.univ_sum_single x]`. Conclude with `Finset.sum_induction _ (fun y : Fin d → AE F E => ∀ᶠ v in cofinite, partFin v y ∈ latAt W v) hadd hzero fun i _ => hs i _`.
-/
theorem eventually_partFin_mem (W : Spc F E d) (hL : W.L.IsLattice E) (x : Fin d → AE F E) :
    ∀ᶠ v in cofinite, partFin v x ∈ latAt W v := by
  classical
  have hadd : ∀ x y : Fin d → AE F E, (∀ᶠ v in cofinite, partFin v x ∈ latAt W v) →
      (∀ᶠ v in cofinite, partFin v y ∈ latAt W v) → ∀ᶠ v in cofinite, partFin v (x + y) ∈ latAt W v :=
    fun x y hx hy => (hx.and hy).mono fun v h => by
      rw [partFin, smul_add]; exact add_mem h.1 h.2
  have hzero : ∀ᶠ v in cofinite, partFin v (0 : Fin d → AE F E) ∈ latAt W v :=
    Eventually.of_forall fun v => by rw [partFin, smul_zero]; exact zero_mem _
  have hs : ∀ (i : Fin d) (t : AE F E), ∀ᶠ v in cofinite, partFin v (Pi.single i t : Fin d → AE F E) ∈ latAt W v := by
    intro i t
    induction t using TensorProduct.induction_on with
    | zero => simpa using hzero
    | add s t h1 h2 => rw [Pi.single_add]; exact hadd _ _ h1 h2
    | tmul a c =>
      obtain ⟨N, hN, hy⟩ := exists_zsmul_mem hL (Pi.single i c : Fin d → E)
      have hNF : (N : F) ≠ 0 := Int.cast_ne_zero.2 hN
      set b : AF F := (N : F)⁻¹ • a with hb
      have hint : ∀ᶠ v in cofinite, evFin F v b ∈ v.adicCompletionIntegers F := b.2.2
      have e : (Pi.single i (a ⊗ₜ[F] c) : Fin d → AE F E) =
          b • fun j => inclR (F := F) (AF F) ((N • (Pi.single i c : Fin d → E)) j) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp only [Pi.single_eq_same, Pi.smul_apply]
          change _ = b • ((1 : AF F) ⊗ₜ[F] (N • c))
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, hb, TensorProduct.smul_tmul,
            ← Int.cast_smul_eq_zsmul F, smul_smul, inv_mul_cancel₀ hNF, one_smul]
        · simp [Pi.single_eq_of_ne hj]
      refine hint.mono fun v hv => ?_
      rw [e, partFin, smul_comm]
      refine smul_mem_latAt W v hv (AddSubgroup.subset_closure ⟨_, GlobalTheory.LatVac.at_liftV v 1, ?_, _, hy, rfl⟩)
      rw [GlobalTheory.LatVac.evFin_liftV]; exact one_mem _
  rw [← Finset.univ_sum_single x]
  exact Finset.sum_induction _ (fun y : Fin d → AE F E => ∀ᶠ v in cofinite, partFin v y ∈ latAt W v) hadd hzero
    fun i _ => hs i _

/- English proof (translation)
Establish `hfg : (W.L.restrictScalars ℤ).FG`. Establish `: Module.Finite (𝓞 E) W.L` using `Module.Finite.iff_fg.2 hL.fg`. Establish `: Module.Finite ℤ W.L` using `Module.Finite.trans (𝓞 E) W.L`. Conclude with `Module.Finite.iff_fg.1 (show Module.Finite ℤ (W.L.restrictScalars ℤ) from this)`. Take `⟨s, hs⟩` from `hfg`.

Establish `h1 : ∀ᶠ v in cofinite, ∀ y ∈ s, partFin v (A *ᵥ fun i => inclR (F` using `F) (AF F) (y i)) ∈ latAt W v := (eventually_all_finset s).2 fun y _ => eventually_partFin_mem W hL _`. Use `h1.mono fun v hv z hz => ?_` and prove the remaining obligations. Establish `h2 : ∀ y ∈ W.L, partFin v (A *ᵥ fun i => inclR (F` using `F) (AF F) (y i)) ∈ latAt W v := by`. Introduce `y hy`. Establish `hy' : y ∈ Submodule.span ℤ (s : Set (Fin d → E))` using `by rw [hs]; exact hy`.

Use `clear hy`. Proceed by induction on `hy' using Submodule.span_induction with`. Consider the case `mem y hy => exact hv y hy`. Consider the case `zero`. Establish `: (fun i => inclR (F` using `F) (AF F) ((0 : Fin d → E) i)) = 0 := funext fun i => map_zero _`.

Rewrite using `[this, Matrix.mulVec_zero, partFin, smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy`. Establish `: (fun i => inclR (F` using `F) (AF F) ((x + y) i)) = (fun i => inclR (F := F) (AF F) (x i)) + fun i => inclR (F := F) (AF F) (y i) := funext fun i => map_add _ _ _`. Rewrite using `[this, Matrix.mulVec_add, partFin, smul_add]`.

Conclude with `add_mem hx hy`. Consider the case `smul n x _ hx`. Establish `: (fun i => inclR (F` using `F) (AF F) ((n • x) i)) = n • (fun i => inclR (F := F) (AF F) (x i)) := funext fun i => map_zsmul _ _ _`. Rewrite using `[this, Matrix.mulVec_smul, partFin, smul_comm]`. Conclude with `zsmul_mem hx _`.

Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨b, hb, hb', y, hy, rfl⟩` from `hz`. Rewrite using `[Matrix.mulVec_smul, ← partFin_of_at hb, partFin, smul_eq_mul, mul_comm, mul_smul]`. Conclude with `smul_mem_latAt W v hb' (h2 y hy)`.

Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `zero_mem _`. Consider the case `add _ _ _ _ h1 h2 => rw [Matrix.mulVec_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg _ _ h1 => rw [Matrix.mulVec_neg]`.

Conclude with `neg_mem h1`.
-/
theorem eventually_mulVec_mem (W : Spc F E d) (hL : W.L.IsLattice E) (A : Matrix (Fin d) (Fin d) (AE F E)) :
    ∀ᶠ v in cofinite, ∀ z ∈ latAt W v, A *ᵥ z ∈ latAt W v := by
  have hfg : (W.L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) W.L := Module.Finite.iff_fg.2 hL.fg
    have : Module.Finite ℤ W.L := Module.Finite.trans (𝓞 E) W.L
    exact Module.Finite.iff_fg.1 (show Module.Finite ℤ (W.L.restrictScalars ℤ) from this)
  obtain ⟨s, hs⟩ := hfg
  have h1 : ∀ᶠ v in cofinite, ∀ y ∈ s, partFin v (A *ᵥ fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v :=
    (eventually_all_finset s).2 fun y _ => eventually_partFin_mem W hL _
  refine h1.mono fun v hv z hz => ?_
  have h2 : ∀ y ∈ W.L, partFin v (A *ᵥ fun i => inclR (F := F) (AF F) (y i)) ∈ latAt W v := by
    intro y hy
    have hy' : y ∈ Submodule.span ℤ (s : Set (Fin d → E)) := by rw [hs]; exact hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem y hy => exact hv y hy
    | zero =>
      have : (fun i => inclR (F := F) (AF F) ((0 : Fin d → E) i)) = 0 := funext fun i => map_zero _
      rw [this, Matrix.mulVec_zero, partFin, smul_zero]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : (fun i => inclR (F := F) (AF F) ((x + y) i)) =
          (fun i => inclR (F := F) (AF F) (x i)) + fun i => inclR (F := F) (AF F) (y i) := funext fun i => map_add _ _ _
      rw [this, Matrix.mulVec_add, partFin, smul_add]; exact add_mem hx hy
    | smul n x _ hx =>
      have : (fun i => inclR (F := F) (AF F) ((n • x) i)) =
          n • (fun i => inclR (F := F) (AF F) (x i)) := funext fun i => map_zsmul _ _ _
      rw [this, Matrix.mulVec_smul, partFin, smul_comm]; exact zsmul_mem hx _
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, hb', y, hy, rfl⟩ := hz
    rw [Matrix.mulVec_smul, ← partFin_of_at hb, partFin, smul_eq_mul, mul_comm, mul_smul]
    exact smul_mem_latAt W v hb' (h2 y hy)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add _ _ _ _ h1 h2 => rw [Matrix.mulVec_add]; exact add_mem h1 h2
  | neg _ _ h1 => rw [Matrix.mulVec_neg]; exact neg_mem h1

/- English proof (translation)
Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨b, hb, -, y, -, rfl⟩` from `hz`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, h b hb]`. Consider the case `zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]`.

Consider the case `add _ _ _ _ h1 h2 => rw [Matrix.mulVec_add, Matrix.mulVec_add, h1, h2]`. Consider the case `neg _ _ h1 => rw [Matrix.mulVec_neg, Matrix.mulVec_neg, h1]`.
-/
theorem mulVec_eq_of_loc (W : Spc F E d) (v : Pl F) {A B : Matrix (Fin d) (Fin d) (AE F E)}
    (h : ∀ u : AF F, At (evFin F v) u → u • A = u • B) {z : Fin d → AE F E} (hz : z ∈ latAt W v) :
    A *ᵥ z = B *ᵥ z := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, -, y, -, rfl⟩ := hz
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, h b hb]
  | zero => rw [Matrix.mulVec_zero, Matrix.mulVec_zero]
  | add _ _ _ _ h1 h2 => rw [Matrix.mulVec_add, Matrix.mulVec_add, h1, h2]
  | neg _ _ h1 => rw [Matrix.mulVec_neg, Matrix.mulVec_neg, h1]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d W hL hf`. Use `((eventually_mulVec_mem W hL (mat hf)).and (eventually_mulVec_mem W hL (mat hf⁻¹))).mono fun v hv g hg h => ⟨hg, fun z hz => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[mulVec_eq_of_loc W v h hz]`. Conclude with `hv.1 z hz`. Establish `h' : ∀ u : AF F, At (evFin F v) u → u • mat g⁻¹ = u • mat hf⁻¹` using `fun u hu => by`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, GlobalTheory.StabHaar.mat_mul_inv, Matrix.mul_one]`. Use `_ = u • mat hf⁻¹ := by`. Rewrite using `[← h u hu, Matrix.mul_smul, GlobalTheory.StabHaar.mat_inv_mul, Matrix.smul_mul, Matrix.one_mul]`. Rewrite using `[mulVec_eq_of_loc W v h' hz]`.

Conclude with `hv.2 z hz`.
-/
theorem eventually_mem_KAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d), W.L.IsLattice E → ∀ hf : UA σ W.J,
    ∀ᶠ v in Filter.cofinite, ∀ g ∈ UAt σ W (evFin F v), (∀ u : AF F, At (evFin F v) u → u • mat g = u • mat hf) →
      g ∈ GlobalTheory.InertSph.KAt σ W v := by
  intro F E _ _ _ _ _ σ d W hL hf
  refine ((eventually_mulVec_mem W hL (mat hf)).and (eventually_mulVec_mem W hL (mat hf⁻¹))).mono
    fun v hv g hg h => ⟨hg, fun z hz => ⟨?_, ?_⟩⟩
  · rw [mulVec_eq_of_loc W v h hz]; exact hv.1 z hz
  · have h' : ∀ u : AF F, At (evFin F v) u → u • mat g⁻¹ = u • mat hf⁻¹ := fun u hu => by
      calc u • mat g⁻¹ = mat g⁻¹ * (u • mat hf) * mat hf⁻¹ := by
            rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, GlobalTheory.StabHaar.mat_mul_inv, Matrix.mul_one]
        _ = u • mat hf⁻¹ := by
            rw [← h u hu, Matrix.mul_smul, GlobalTheory.StabHaar.mat_inv_mul, Matrix.smul_mul, Matrix.one_mul]
    rw [mulVec_eq_of_loc W v h' hz]; exact hv.2 z hz

end GlobalTheory.IntegralAE
