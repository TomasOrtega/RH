import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.LinFormBound

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Rewrite using `[← absFin_tmul_one (E := F) F v, TensorProduct.sum_tmul]`. Conclude with `absFin_sum_le F v _ _ fun i hi => (absFin_tmul_one (E := F) F v (x i)).trans_le (h i hi)`.
-/
theorem nnnorm_sum_le (v : HeightOneSpectrum (𝓞 F)) {ι : Type} (s : Finset ι) (x : ι → Fv F v) {c : ℝ≥0}
    (h : ∀ i ∈ s, ‖x i‖₊ ≤ c) : ‖∑ i ∈ s, x i‖₊ ≤ c := by
  rw [← absFin_tmul_one (E := F) F v, TensorProduct.sum_tmul]
  exact absFin_sum_le F v _ _ fun i hi => (absFin_tmul_one (E := F) F v (x i)).trans_le (h i hi)

/- English proof (translation)
Use `(eventually_absFin_le_one (E := F) F (a ⊗ₜ[F] (1 : F))).mono fun v hv => ?_` and prove the remaining obligations. Rewrite `hv` using `[compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, absFin_tmul_one]`. Then use the resulting hypothesis.
-/
theorem eventually_nnnorm_evFin_le_one (a : AF F) : ∀ᶠ v in Filter.cofinite, ‖evFin F v a‖₊ ≤ 1 := by
  refine (eventually_absFin_le_one (E := F) F (a ⊗ₜ[F] (1 : F))).mono fun v hv => ?_
  rwa [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    absFin_tmul_one] at hv

/- English proof (translation)
Take `⟨s, b, hb⟩` from `FiniteDimensional.exists_is_basis_integral (𝓞 F) F E`. Establish `hb' : ∀ i, IsIntegral ℤ (b i)` using `fun i => isIntegral_trans _ (hb i)`. Set `B` to `Algebra.TensorProduct.basis (AF F) b.traceDual`. Set `y : Fin n × Fin m × s → AF F` to `fun q => f (Matrix.single q.1 q.2.1 (B q.2.2))`. Set `K : HeightOneSpectrum (𝓞 F) → ℝ≥0` to `fun v => max 1 (Finset.univ.sup fun q => ‖evFin F v (y q)‖₊)`.

Establish `hdec : ∀ X : Matrix (Fin n) (Fin m) (AF F ⊗[F] E), f X = ∑ q : Fin n × Fin m × s, B.repr (X q.1 q.2.1) q.2.2 * y q`. Introduce `X`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single X]`. Simplify using `only [map_sum, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `conv_lhs => rw [← B.sum_repr (X i j)]`. Establish `: Matrix.single i j (∑ k, B.repr (X i j) k • B k) = ∑ k, B.repr (X i j) k • Matrix.single i j (B k)`. Simplify using `only [← Matrix.singleLinearMap_apply (R := AF F), map_sum, map_smul]`. Rewrite using `[this, map_sum]`. Simplify using `only [map_smul, smul_eq_mul, y]`.

Use `⟨K, ?_, fun v => le_max_left _ _, fun X v => ?_⟩` and prove the remaining obligations. Establish `h` using `eventually_all.2 fun q => eventually_nnnorm_evFin_le_one (y q)`. Use `(eventually_cofinite.1 h).subset fun v hv hv' => hv (max_eq_left (Finset.sup_le fun q _ => ?_))` and prove the remaining obligations. Conclude with `hv' q`. Establish `hsup : ∀ p : Fin n × Fin m, absFin F v (compFin F E v (X p.1 p.2)) ≤ Finset.univ.sup fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2))` using `fun p => Finset.le_sup (f := fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2))) (Finset.mem_univ p)`.

Rewrite using `[hdec X, map_sum]`. Use `nnnorm_sum_le v _ _ fun q _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, nnnorm_mul, mul_comm]`. Use `mul_le_mul' ?_ ?_` and prove the remaining obligations. Conclude with `(Finset.le_sup (f := fun q => ‖evFin F v (y q)‖₊) (Finset.mem_univ q)).trans (le_max_right _ _)`.

Rewrite using `[← HeightProper.repr_map b.traceDual (evFin F v) (X q.1 q.2.1) q.2.2]`. Use `(HeightProper.nnnorm_repr_le_absFin b hb' v _ q.2.2).trans ?_` and prove the remaining obligations. Establish `hc : Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (X q.1 q.2.1) = compFin F E v (X q.1 q.2.1)`. Both sides reduce to the same expression. Rewrite using `[hc]`.

Conclude with `hsup (q.1, q.2.1)`.
-/
theorem exists_bound {n m : ℕ} (f : Matrix (Fin n) (Fin m) (AF F ⊗[F] E) →ₗ[AF F] AF F) :
    ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧
      ∀ X v, ‖evFin F v (f X)‖₊ ≤
        K v * Finset.univ.sup fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2)) := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  let B := Algebra.TensorProduct.basis (AF F) b.traceDual

  let y : Fin n × Fin m × s → AF F := fun q => f (Matrix.single q.1 q.2.1 (B q.2.2))
  let K : HeightOneSpectrum (𝓞 F) → ℝ≥0 := fun v => max 1 (Finset.univ.sup fun q => ‖evFin F v (y q)‖₊)
  have hdec : ∀ X : Matrix (Fin n) (Fin m) (AF F ⊗[F] E),
      f X = ∑ q : Fin n × Fin m × s, B.repr (X q.1 q.2.1) q.2.2 * y q := by
    intro X
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← B.sum_repr (X i j)]
    have : Matrix.single i j (∑ k, B.repr (X i j) k • B k) = ∑ k, B.repr (X i j) k • Matrix.single i j (B k) := by
      simp only [← Matrix.singleLinearMap_apply (R := AF F), map_sum, map_smul]
    rw [this, map_sum]
    simp only [map_smul, smul_eq_mul, y]
  refine ⟨K, ?_, fun v => le_max_left _ _, fun X v => ?_⟩
  · have h := eventually_all.2 fun q => eventually_nnnorm_evFin_le_one (y q)
    refine (eventually_cofinite.1 h).subset fun v hv hv' => hv (max_eq_left (Finset.sup_le fun q _ => ?_))
    exact hv' q
  · have hsup : ∀ p : Fin n × Fin m, absFin F v (compFin F E v (X p.1 p.2)) ≤
        Finset.univ.sup fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2)) :=
      fun p => Finset.le_sup (f := fun p : Fin n × Fin m => absFin F v (compFin F E v (X p.1 p.2)))
        (Finset.mem_univ p)
    rw [hdec X, map_sum]
    refine nnnorm_sum_le v _ _ fun q _ => ?_
    rw [map_mul, nnnorm_mul, mul_comm]
    refine mul_le_mul' ?_ ?_
    · exact (Finset.le_sup (f := fun q => ‖evFin F v (y q)‖₊) (Finset.mem_univ q)).trans (le_max_right _ _)
    · rw [← HeightProper.repr_map b.traceDual (evFin F v) (X q.1 q.2.1) q.2.2]
      refine (HeightProper.nnnorm_repr_le_absFin b hb' v _ q.2.2).trans ?_
      have hc : Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) (X q.1 q.2.1) = compFin F E v (X q.1 q.2.1) :=
        rfl
      rw [hc]
      exact hsup (q.1, q.2.1)

end GlobalTheory.LinFormBound

/- English proof (translation)
Introduce `f` and use `GlobalTheory.LinFormBound.exists_bound f`.
-/
theorem GlobalTheory.LinFormBound.main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (f : Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] AF F), ∃ K : HeightOneSpectrum (𝓞 F) → ℝ≥0, (Function.mulSupport K).Finite ∧ (∀ v, 1 ≤ K v) ∧ ∀ X v, ‖evFin F v (f X)‖₊ ≤ K v * Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) :=
  fun f => GlobalTheory.LinFormBound.exists_bound f
