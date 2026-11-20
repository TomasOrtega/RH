import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisZero
import GroundTheory.GlobalFields.Adele.Discrete
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.QhtUnip

noncomputable section

namespace GlobalTheory.QhtUnip.ApproxBdd

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `b0` to `Module.finBasis F E`. Establish `h : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • b0 i)` using `fun i => by`. Take `⟨m, hm, hi⟩` from `((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (b0 i))).exists_integral_multiple`. Conclude with `⟨m, hm, hi⟩`. Use `choose m hm hi using h`.

Use `⟨b0.isUnitSMul (w := fun i => (m i : F)) fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Conclude with `isUnit_iff_ne_zero.2 (by exact_mod_cast hm i)`. Rewrite using `[Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]`. Conclude with `hi i`.
-/
theorem exists_basis_integral :
    ∃ b : Module.Basis (Fin (Module.finrank F E)) F E, ∀ i, IsIntegral ℤ (b i) := by
  let b0 := Module.finBasis F E
  have h : ∀ i, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • b0 i) := fun i => by
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic (b0 i))).exists_integral_multiple
    exact ⟨m, hm, hi⟩
  choose m hm hi using h
  refine ⟨b0.isUnitSMul (w := fun i => (m i : F)) fun i => ?_, fun i => ?_⟩
  · exact isUnit_iff_ne_zero.2 (by exact_mod_cast hm i)
  · rw [Module.Basis.isUnitSMul_apply, Int.cast_smul_eq_zsmul]
    exact hi i

/- English proof (translation)
Use `⟨fun v => ?_, fun w τ => ?_⟩` and prove the remaining obligations. Establish `hv : v ∉ (∅ : Finset (Pl F))` using `by simp`. Rewrite using `[if_neg hv, map_sum]`. Use `absFin_sum_le F v _ _ fun i _ => ?_` and prove the remaining obligations. Establish `e : compFin F E v (d i ⊗ₜ[F] b i) = evFin F v (d i) ⊗ₜ[F] b i` using `Algebra.TensorProduct.map_tmul _ _ _ _`.

Rewrite using `[e]`. Use `(absFin_tmul_le F v _ ⟨b i, hb i⟩).trans ?_` and prove the remaining obligations. Use `show ‖(d i).2 v‖₊ ≤ 1`. Establish `h2 : (d i).2 v ∈ v.adicCompletionIntegers F` using `(hd i).2 v`. Conclude with `Valued.toNormedField.norm_le_one_iff.2 h2` after adjusting the coercions.

Rewrite using `[map_sum, map_sum]`. Use `(nnnorm_sum_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Establish `e : compInf F E w (d i ⊗ₜ[F] b i) = evInf F w (d i) ⊗ₜ[F] b i` using `Algebra.TensorProduct.map_tmul _ _ _ _`.

Rewrite using `[e, infEmb_tmul, nnnorm_mul]`. Use `show ‖InfinitePlace.Completion.extensionEmbedding w ((d i).1 w)‖₊ * _ ≤ _`. Establish `h1 : ‖InfinitePlace.Completion.extensionEmbedding w ((d i).1 w)‖₊ = ‖(d i).1 w‖₊` using `NNReal.eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _)`. Rewrite using `[h1]`. Conclude with `mul_le_mul' (hR _ (hd i).1 w) (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (b i)‖₊) (fun _ _ => by positivity) (Finset.mem_univ τ.1))`.
-/
theorem sum_tmul_mem_bddA {n : ℕ} (b : Fin n → E) (hb : ∀ i, IsIntegral ℤ (b i)) (C : Set (Ainf F)) (R : ℝ≥0)
    (hR : ∀ x ∈ C, ∀ w : InfinitePlace F, ‖x w‖₊ ≤ R) (d : Fin n → AF F)
    (hd : ∀ i, (d i).1 ∈ C ∧ (d i).2 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F) :
    (∑ i, d i ⊗ₜ[F] b i : AE F E) ∈ bddA E (∅ : Finset (Pl F)) (R * ∑ i, ∑ τ : E →+* ℂ, ‖τ (b i)‖₊) := by
  refine ⟨fun v => ?_, fun w τ => ?_⟩
  · have hv : v ∉ (∅ : Finset (Pl F)) := by simp
    rw [if_neg hv, map_sum]
    refine absFin_sum_le F v _ _ fun i _ => ?_
    have e : compFin F E v (d i ⊗ₜ[F] b i) = evFin F v (d i) ⊗ₜ[F] b i :=
      Algebra.TensorProduct.map_tmul _ _ _ _
    rw [e]
    refine (absFin_tmul_le F v _ ⟨b i, hb i⟩).trans ?_
    show ‖(d i).2 v‖₊ ≤ 1
    have h2 : (d i).2 v ∈ v.adicCompletionIntegers F := (hd i).2 v
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 h2
  · rw [map_sum, map_sum]
    refine (nnnorm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have e : compInf F E w (d i ⊗ₜ[F] b i) = evInf F w (d i) ⊗ₜ[F] b i :=
      Algebra.TensorProduct.map_tmul _ _ _ _
    rw [e, infEmb_tmul, nnnorm_mul]
    show ‖InfinitePlace.Completion.extensionEmbedding w ((d i).1 w)‖₊ * _ ≤ _
    have h1 : ‖InfinitePlace.Completion.extensionEmbedding w ((d i).1 w)‖₊ = ‖(d i).1 w‖₊ :=
      NNReal.eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _)
    rw [h1]
    exact mul_le_mul' (hR _ (hd i).1 w) (Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ (b i)‖₊)
      (fun _ _ => by positivity) (Finset.mem_univ τ.1))

end GlobalTheory.QhtUnip.ApproxBdd

namespace GlobalTheory.QhtUnip

open GlobalTheory.AdelicU GlobalTheory.QhtUnip.ApproxBdd

/- English proof (translation)
Introduce `F E _ _ _ _ _ ι z`. Take `⟨b, hb⟩` from `exists_basis_integral (F := F) (E := E)`. Take `⟨C, hC, hCx⟩` from `GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F`. Choose the witnesses or unpack the hypotheses as in `⟨R, hR⟩ : ∃ R : ℝ≥0, ∀ x ∈ C, ∀ w : InfinitePlace F, ‖x w‖₊ ≤ R := by`. Take `⟨M, hM⟩` from `hC.bddAbove_image (f := fun x : Ainf F => ∑ w, ‖x w‖₊) (Continuous.continuousOn (continuous_finset_sum _ fun w _ => (continuous_apply w).nnnorm))`.

Use `⟨M, fun x hx w => ?_⟩` and prove the remaining obligations. Conclude with `(Finset.single_le_sum (f := fun w => ‖x w‖₊) (fun _ _ => by positivity) (Finset.mem_univ w)).trans (hM ⟨x, hx, rfl⟩)`. Set `B` to `Algebra.TensorProduct.basis (AF F) b`. Use `choose k hk using hCx`. Use `⟨fun t => ∑ i, k (B.repr (z t) i) • b i, ∅, R * ∑ i, ∑ τ : E →+* ℂ, ‖τ (b i)‖₊, fun t => ?_⟩` and prove the remaining obligations.

Use `show z t - inclR (F := F) (AF F) (∑ i, k (B.repr (z t) i) • b i) ∈ _`. Establish `hz : z t = ∑ i, B.repr (z t) i ⊗ₜ[F] b i` using `by conv_lhs => rw [← B.sum_repr (z t)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Use `set a := B.repr (z t) with ha`.

Establish `hinc : inclR (F` using `F) (AF F) (∑ i, k (a i) • b i) = ∑ i, algebraMap F (AF F) (k (a i)) ⊗ₜ[F] b i := by`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `show (1 : AF F) ⊗ₜ[F] (k (a i) • b i) = _`. Rewrite using `[← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]`.

Establish `key : z t - inclR (F` using `F) (AF F) (∑ i, k (a i) • b i) = ∑ i, (a i - algebraMap F (AF F) (k (a i))) ⊗ₜ[F] b i := by`. Rewrite using `[hinc, hz, ← Finset.sum_sub_distrib]`. Simplify using `only [TensorProduct.sub_tmul]`. Rewrite using `[key]`. Conclude with `sum_tmul_mem_bddA b hb C R hR _ fun i => hk _`.
-/
theorem exists_rat_sub_mem_bdd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : Type) (z : ι → AE F E), ∃ e : ι → E, (fun t => z t - inclR (F := F) (AF F) (e t)) ∈ Bdd F E ι := by
  intro F E _ _ _ _ _ ι z
  obtain ⟨b, hb⟩ := exists_basis_integral (F := F) (E := E)
  obtain ⟨C, hC, hCx⟩ := GroundTheory.Global.exists_isCompact_forall_exists_sub_mem F
  obtain ⟨R, hR⟩ : ∃ R : ℝ≥0, ∀ x ∈ C, ∀ w : InfinitePlace F, ‖x w‖₊ ≤ R := by
    obtain ⟨M, hM⟩ := hC.bddAbove_image (f := fun x : Ainf F => ∑ w, ‖x w‖₊)
      (Continuous.continuousOn (continuous_finset_sum _ fun w _ => (continuous_apply w).nnnorm))
    refine ⟨M, fun x hx w => ?_⟩
    exact (Finset.single_le_sum (f := fun w => ‖x w‖₊) (fun _ _ => by positivity) (Finset.mem_univ w)).trans
      (hM ⟨x, hx, rfl⟩)
  let B := Algebra.TensorProduct.basis (AF F) b
  choose k hk using hCx
  refine ⟨fun t => ∑ i, k (B.repr (z t) i) • b i, ∅, R * ∑ i, ∑ τ : E →+* ℂ, ‖τ (b i)‖₊, fun t => ?_⟩
  show z t - inclR (F := F) (AF F) (∑ i, k (B.repr (z t) i) • b i) ∈ _
  have hz : z t = ∑ i, B.repr (z t) i ⊗ₜ[F] b i := by
    conv_lhs => rw [← B.sum_repr (z t)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  set a := B.repr (z t) with ha
  have hinc : inclR (F := F) (AF F) (∑ i, k (a i) • b i) = ∑ i, algebraMap F (AF F) (k (a i)) ⊗ₜ[F] b i := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    show (1 : AF F) ⊗ₜ[F] (k (a i) • b i) = _
    rw [← TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]
  have key : z t - inclR (F := F) (AF F) (∑ i, k (a i) • b i) =
      ∑ i, (a i - algebraMap F (AF F) (k (a i))) ⊗ₜ[F] b i := by
    rw [hinc, hz, ← Finset.sum_sub_distrib]
    simp only [TensorProduct.sub_tmul]
  rw [key]
  exact sum_tmul_mem_bddA b hb C R hR _ fun i => hk _

end GlobalTheory.QhtUnip
