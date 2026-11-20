import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqAdeleSupportedAtFinitePlaceOfSupportedAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisSide
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LatPtDecomp

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem`. Consider the case `exact _root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem`. Consider the case `(apply _root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem ..)`.
-/
theorem exists_zsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) (w : Fin n → E) : ∃ N : ℤ, N ≠ 0 ∧ N • w ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntSmulMemSubmodule.exists_int_smul_mem ..)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `hk' : algebraMap F (Fv F v) k ≠ 0` using `(map_ne_zero _).2 hk`. Establish `hkv : Valued.v (algebraMap F (Fv F v) k) ≠ 0` using `(Valuation.ne_zero_iff _).2 hk'`. Establish `hd : DenseRange (algebraMap F (v.adicCompletion F))` using `HeightOneSpectrum.denseRange_algebraMap (K := F) v`. Establish `hN : {y : v.adicCompletion F | Valued.v (t - y) < Valued.v (algebraMap F (Fv F v) k)} ∈ nhds t`. Establish `ho` using `(Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict (algebraMap F (Fv F v) k))).preimage (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => t - y)`.

Simplify using `only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] at ho`. Use `ho.mem_nhds ?_` and prove the remaining obligations. Use `show Valued.v (t - t) < _`. Rewrite using `[sub_self, map_zero]`. Conclude with `zero_lt_iff.2 hkv`.

Take `⟨s, hs⟩` from `hd.mem_nhds hN`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]`. Establish `hs' : Valued.v (t - algebraMap F (Fv F v) s) < Valued.v (algebraMap F (Fv F v) k)` using `hs`. Rewrite using `[inv_mul_le_iff₀ (zero_lt_iff.2 hkv), mul_one]`.

Conclude with `hs'.le`.
-/
theorem exists_sub_mem (v : Pl F) (t : Fv F v) {k : F} (hk : k ≠ 0) :
    ∃ s : F, (algebraMap F (Fv F v) k)⁻¹ * (t - algebraMap F (Fv F v) s) ∈ v.adicCompletionIntegers F := by
  have hk' : algebraMap F (Fv F v) k ≠ 0 := (map_ne_zero _).2 hk
  have hkv : Valued.v (algebraMap F (Fv F v) k) ≠ 0 := (Valuation.ne_zero_iff _).2 hk'
  have hd : DenseRange (algebraMap F (v.adicCompletion F)) := HeightOneSpectrum.denseRange_algebraMap (K := F) v
  have hN : {y : v.adicCompletion F | Valued.v (t - y) < Valued.v (algebraMap F (Fv F v) k)} ∈ nhds t := by
    have ho := (Valued.isOpen_ball (v.adicCompletion F) (Valued.v.restrict (algebraMap F (Fv F v) k))).preimage
      (continuous_const.sub continuous_id : Continuous fun y : v.adicCompletion F => t - y)
    simp only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (t - t) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hkv
  obtain ⟨s, hs⟩ := hd.mem_nhds hN
  refine ⟨s, ?_⟩
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀]
  have hs' : Valued.v (t - algebraMap F (Fv F v) s) < Valued.v (algebraMap F (Fv F v) k) := hs
  rw [inv_mul_le_iff₀ (zero_lt_iff.2 hkv), mul_one]
  exact hs'.le

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [incM, Matrix.map_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp [inclR]`.
-/
theorem incM_single {n d : ℕ} (i : Fin n) (j : Fin d) (y : E) :
    incM F (Matrix.single i j y) = Matrix.single i j ((1 : AF F) ⊗ₜ[F] y) := by
  ext a b
  simp only [incM, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [inclR]

/- English proof (translation)
Apply the tactic sequence `ext k l; simp only [Matrix.sub_apply, Matrix.single_apply]; split_ifs <;> simp`.
-/
theorem single_sub {A : Type} [AddGroup A] {n d : ℕ} (i : Fin n) (j : Fin d) (a b : A) :
    Matrix.single i j a - Matrix.single i j b = Matrix.single i j (a - b) := by
  ext k l; simp only [Matrix.sub_apply, Matrix.single_apply]; split_ifs <;> simp

/- English proof (translation)
Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul]`.
-/
theorem atPlace_one_smul_tmul (v : Pl F) (a : AF F) (x : E) :
    GlobalTheory.EmbChart.atPlace v 1 • (a ⊗ₜ[F] x) = GlobalTheory.EmbChart.atPlace v (evFin F v a) ⊗ₜ[F] x := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, one_mul]

/- English proof (translation)
Take `⟨N, hN, hNx⟩` from `exists_zsmul_mem X.L hX (Pi.single i x)`. Take `⟨N', hN', hNy⟩` from `exists_zsmul_mem Y.L hY (Pi.single j 1)`. Establish `hK : ((N * N' : ℤ) : F) ≠ 0` using `Int.cast_ne_zero.2 (mul_ne_zero hN hN')`. Take `⟨s, hs⟩` from `exists_sub_mem v t hK`. Use `set r := (algebraMap F (Fv F v) ((N * N' : ℤ) : F))⁻¹ * (t - algebraMap F (Fv F v) s) with hr`.

Use `⟨Matrix.single i j (algebraMap F E s * x), ?_⟩` and prove the remaining obligations. Use `AddSubgroup.subset_closure ⟨GlobalTheory.EmbChart.atPlace v r, GlobalTheory.VacAny.at_atPlace r, ?_, _, hNx, _, hNy, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.EmbChart.evFin_atPlace]`. Conclude with `hs`. Establish `hv : Matrix.vecMulVec (N • Pi.single i x) (N' • Pi.single j (1 : E)) = Matrix.single i j (((N * N' : ℤ) : F) • x)`.

Use extensionality with `a b`. Simplify using `only [Matrix.vecMulVec_apply, Pi.smul_apply, Pi.single_apply, Matrix.single_apply]`. Apply the tactic sequence `by_cases h1 : a = i <;> by_cases h2 : b = j`. Substitute `h1 h2` using the available equality. Simplify using `only [if_true, and_self, smul_eq_mul, mul_one]`.

Rewrite using `[Algebra.smul_def (A := E) ((N * N' : ℤ) : F), map_intCast]`. Simplify using `only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul, mul_one]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Apply the tactic sequence `all_goals simp [h1, h2, eq_comm (a := i), eq_comm (a := j)]`.

Establish `hev : ∀ c : F, evFin F v (c • (1 : AF F)) = algebraMap F (Fv F v) c` using `fun c => by`. Rewrite using `[map_smul, map_one, Algebra.algebraMap_eq_smul_one]`. Establish `hK' : algebraMap F (Fv F v) ((N * N' : ℤ) : F) ≠ 0` using `(map_ne_zero _).2 hK`. Rewrite using `[hv, incM_single, incM_single, Matrix.smul_single, Matrix.smul_single, single_sub]`. Use `congr 1`.

Rewrite using `[← Algebra.smul_def, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, atPlace_one_smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, ← TensorProduct.sub_tmul, ← map_sub, hev, hev, hr]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.
-/
theorem core {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (hX : X.L.IsLattice E) (hY : Y.L.IsLattice E) (v : Pl F)
    (i : Fin n) (j : Fin d) (t : Fv F v) (x : E) :
    ∃ X₀ : Matrix (Fin n) (Fin d) E,
      Matrix.single i j (GlobalTheory.EmbChart.atPlace v t ⊗ₜ[F] x) - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  obtain ⟨N, hN, hNx⟩ := exists_zsmul_mem X.L hX (Pi.single i x)
  obtain ⟨N', hN', hNy⟩ := exists_zsmul_mem Y.L hY (Pi.single j 1)
  have hK : ((N * N' : ℤ) : F) ≠ 0 := Int.cast_ne_zero.2 (mul_ne_zero hN hN')
  obtain ⟨s, hs⟩ := exists_sub_mem v t hK
  set r := (algebraMap F (Fv F v) ((N * N' : ℤ) : F))⁻¹ * (t - algebraMap F (Fv F v) s) with hr
  refine ⟨Matrix.single i j (algebraMap F E s * x), ?_⟩
  refine AddSubgroup.subset_closure ⟨GlobalTheory.EmbChart.atPlace v r, GlobalTheory.VacAny.at_atPlace r, ?_, _, hNx, _, hNy, ?_⟩
  · rw [GlobalTheory.EmbChart.evFin_atPlace]; exact hs
  · have hv : Matrix.vecMulVec (N • Pi.single i x) (N' • Pi.single j (1 : E)) =
        Matrix.single i j (((N * N' : ℤ) : F) • x) := by
      ext a b
      simp only [Matrix.vecMulVec_apply, Pi.smul_apply, Pi.single_apply, Matrix.single_apply]
      by_cases h1 : a = i <;> by_cases h2 : b = j
      · subst h1 h2
        simp only [if_true, and_self, smul_eq_mul, mul_one]
        rw [Algebra.smul_def (A := E) ((N * N' : ℤ) : F), map_intCast]
        simp only [algebraMap_int_eq, eq_intCast, zsmul_eq_mul, mul_one]; push_cast; ring
      all_goals simp [h1, h2, eq_comm (a := i), eq_comm (a := j)]
    have hev : ∀ c : F, evFin F v (c • (1 : AF F)) = algebraMap F (Fv F v) c := fun c => by
      rw [map_smul, map_one, Algebra.algebraMap_eq_smul_one]
    have hK' : algebraMap F (Fv F v) ((N * N' : ℤ) : F) ≠ 0 := (map_ne_zero _).2 hK
    rw [hv, incM_single, incM_single, Matrix.smul_single, Matrix.smul_single, single_sub]
    congr 1
    rw [← Algebra.smul_def, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, atPlace_one_smul_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, GlobalTheory.EmbChart.atPlace_mul_right, ← TensorProduct.sub_tmul, ← map_sub,
      hev, hev, hr]
    congr 2
    field_simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ n d X Y hX hY v z hz`. Establish `hz' : z = GlobalTheory.EmbChart.atPlace v 1 • z`. Establish `h` using `hz (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])`. Rewrite `h` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `h`.

Set `P : Matrix (Fin n) (Fin d) (AE F E) → Prop` to `fun w => ∃ X₀ : Matrix (Fin n) (Fin d) E, GlobalTheory.EmbChart.atPlace v 1 • w - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v`. Establish `P0 : P 0` using `⟨0, by simp [incM]⟩`. Establish `Padd : ∀ w w', P w → P w' → P (w + w')`. Introduce and unpack `w w' ⟨A, hA⟩ ⟨B, hB⟩`. Use `⟨A + B, ?_⟩` and prove the remaining obligations.

Establish `: GlobalTheory.EmbChart.atPlace v 1 • (w + w') - GlobalTheory.EmbChart.atPlace v 1 • incM F (A + B) = (GlobalTheory.EmbChart.atPlace v 1 • w - GlobalTheory.EmbChart.atPlace v 1 • incM F A) + (GlobalTheory.EmbChart.atPlace v 1 • w' - GlobalTheory.EmbChart.atPlace v 1 • incM F B)`. Establish `hI : incM F (A + B) = incM F A + incM F B` using `by ext; simp [incM]`. Rewrite using `[hI, smul_add, smul_add]`. Normalize the expressions using the abelian group laws. Rewrite using `[this]`.

Conclude with `add_mem hA hB`. Establish `Psum : ∀ {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin d) (AE F E)), (∀ k ∈ s, P (f k)) → P (∑ k ∈ s, f k)`. Introduce `ι s f h`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using P0`.

Consider the case `insert k s hk ih`. Rewrite using `[Finset.sum_insert hk]`. Conclude with `Padd _ _ (h k (Finset.mem_insert_self _ _)) (ih fun m hm => h m (Finset.mem_insert_of_mem hm))`. Establish `Psingle : ∀ (i : Fin n) (j : Fin d) (w : AE F E), P (Matrix.single i j w)`. Introduce `i j w`.

Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simpa using P0`. Consider the case `add a b ha hb => rw [Matrix.single_add]`. Conclude with `Padd _ _ ha hb`. Consider the case `tmul a x`.

Rewrite using `[show P (Matrix.single i j (a ⊗ₜ[F] x)) ↔ ∃ X₀ : Matrix (Fin n) (Fin d) E, Matrix.single i j (GlobalTheory.EmbChart.atPlace v (evFin F v a) ⊗ₜ[F] x) - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v by`. Simplify using `only [P, Matrix.smul_single, atPlace_one_smul_tmul]]`. Conclude with `core X Y hX hY v i j _ x`. Choose the witnesses or unpack the hypotheses as in `⟨X₀, h⟩ : P z := by`. Rewrite using `[Matrix.matrix_eq_sum_single z]`.

Conclude with `Psum _ _ fun i _ => Psum _ _ fun j _ => Psingle i j _`. Conclude with `⟨X₀, by rw [hz']; exact h⟩`.
-/
theorem decomp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d), X.L.IsLattice E → Y.L.IsLattice E → ∀ (v : Pl F) (z : Matrix (Fin n) (Fin d) (AE F E)),
    At (evFin F v) z → ∃ X₀ : Matrix (Fin n) (Fin d) E, z - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v := by
  intro F E _ _ _ _ _ n d X Y hX hY v z hz
  have hz' : z = GlobalTheory.EmbChart.atPlace v 1 • z := by
    have h := hz (1 - GlobalTheory.EmbChart.atPlace v 1) (by rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h
    exact h
  let P : Matrix (Fin n) (Fin d) (AE F E) → Prop := fun w =>
    ∃ X₀ : Matrix (Fin n) (Fin d) E, GlobalTheory.EmbChart.atPlace v 1 • w - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈ latAtV X Y v
  have P0 : P 0 := ⟨0, by simp [incM]⟩
  have Padd : ∀ w w', P w → P w' → P (w + w') := by
    rintro w w' ⟨A, hA⟩ ⟨B, hB⟩
    refine ⟨A + B, ?_⟩
    have : GlobalTheory.EmbChart.atPlace v 1 • (w + w') - GlobalTheory.EmbChart.atPlace v 1 • incM F (A + B) =
        (GlobalTheory.EmbChart.atPlace v 1 • w - GlobalTheory.EmbChart.atPlace v 1 • incM F A) +
        (GlobalTheory.EmbChart.atPlace v 1 • w' - GlobalTheory.EmbChart.atPlace v 1 • incM F B) := by
      have hI : incM F (A + B) = incM F A + incM F B := by ext; simp [incM]
      rw [hI, smul_add, smul_add]; abel
    rw [this]; exact add_mem hA hB
  have Psum : ∀ {ι : Type} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin d) (AE F E)), (∀ k ∈ s, P (f k)) → P (∑ k ∈ s, f k) := by
    intro ι s f h
    classical
    induction s using Finset.induction_on with
    | empty => simpa using P0
    | insert k s hk ih =>
      rw [Finset.sum_insert hk]
      exact Padd _ _ (h k (Finset.mem_insert_self _ _)) (ih fun m hm => h m (Finset.mem_insert_of_mem hm))
  have Psingle : ∀ (i : Fin n) (j : Fin d) (w : AE F E), P (Matrix.single i j w) := by
    intro i j w
    induction w using TensorProduct.induction_on with
    | zero => simpa using P0
    | add a b ha hb => rw [Matrix.single_add]; exact Padd _ _ ha hb
    | tmul a x =>
      rw [show P (Matrix.single i j (a ⊗ₜ[F] x)) ↔ ∃ X₀ : Matrix (Fin n) (Fin d) E,
          Matrix.single i j (GlobalTheory.EmbChart.atPlace v (evFin F v a) ⊗ₜ[F] x) - GlobalTheory.EmbChart.atPlace v 1 • incM F X₀ ∈
            latAtV X Y v by
        simp only [P, Matrix.smul_single, atPlace_one_smul_tmul]]
      exact core X Y hX hY v i j _ x
  obtain ⟨X₀, h⟩ : P z := by
    rw [Matrix.matrix_eq_sum_single z]
    exact Psum _ _ fun i _ => Psum _ _ fun j _ => Psingle i j _
  exact ⟨X₀, by rw [hz']; exact h⟩

end GlobalTheory.LatPtDecomp
