import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.ThK.Vac
open scoped Matrix TensorProduct nonZeroDivisors
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LatVac
open GlobalTheory.StdDual (codiff codiff_ne_zero)
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
/- English proof (translation)
Establish `hσ` using `sigma_sigma hB.cm`. Establish `: Module.Finite (𝓞 F) (𝓞 E)` using `Module.Finite.of_restrictScalars_finite ℤ _ _`. Take `⟨m, g, f, hg, hf, hid⟩` from `dual_family (𝓞 F) F (W.L.restrictScalars (𝓞 F)) (hW.lat.fg.restrictScalars) (by`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Take `⟨t, ht⟩` from `multiple_mem_span_of_mem_localization_span (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E (W.L : Set (Fin d → E)) x (hW.lat.span_eq_top ▸ Submodule.mem_top)`. Take `⟨_, k, hk, rfl⟩` from `t`. Rewrite `ht` using `[Submodule.span_eq]`. Establish `hk0 : (k : F) ≠ 0` using `Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hk)`. Establish `ht' : (k : F) • x ∈ W.L`.

Rewrite using `[Int.cast_smul_eq_zsmul, ← algebraMap_smul (𝓞 E) k x]`. Conclude with `ht`. Rewrite using `[← inv_smul_smul₀ hk0 x]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ht'))`. Use `choose u hu using fun i => exists_tr_rep hσ (skew_det hW) (f i)`.

Establish `hdec : ∀ z : Fin d → AE F E, z = ∑ i, trF σ W.J (u i) z • incV (g i)` using `fun z => by`. Establish `hz` using `span_incV z`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨x, rfl⟩` from `hz`.

Simplify using `only [trF_incV, ← hu]`. Use extensionality with `j`. Use `conv_lhs => rw [hid x]`. Simplify using `only [incV, Finset.sum_apply, Pi.smul_apply, map_sum, algebraMap_smul]`. Conclude with `Finset.sum_congr rfl fun i _ => map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) _ _`.

Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp only [map_add, add_smul, Finset.sum_add_distrib, ← hx, ← hy]`. Consider the case `smul a x _ hx => simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← hx]`. Rewrite using `[hdec w]`. Use `sum_mem fun i _ => AddSubgroup.subset_closure ⟨_, fun a ha => ?_, ?_, g i, hg i, rfl⟩` and prove the remaining obligations.

Rewrite using `[← map_smul, hw a ha, map_zero]`. Use `mem_int_of_psi hB.std v _ fun t ht a ha => ?_` and prove the remaining obligations. Establish `hm : algebraMap F E t • u i ∈ W.L` using `(hW.dual _).2 fun x hx o => by`. Set `o' : 𝓞 E` to `⟨σ o, (RingOfIntegers.isIntegral_coe o).map (σ.restrictScalars ℤ)⟩`. Take `⟨c, hc⟩` from `hf i _ (W.L.smul_mem o' hx)`.

Establish `e : (o : E) * form σ W.J (algebraMap F E t • u i) x = t • form σ W.J (u i) (o' • x)`. Rewrite using `[form_eq, form_eq, Algebra.smul_def t, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Establish `: (o' • x) l = σ o * x l` using `rfl`. Rewrite using `[this, map_mul, hσ, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← Algebra.trace_trace (S := F), map_smul, ← hu, ← hc, smul_eq_mul]`. Take `⟨k, hk⟩` from `(FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))).1 ht _ ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)`. Rewrite `hk` using `[Algebra.traceForm_apply]`. Rewrite using `[← hk]`.

Conclude with `isIntegral_algebraMap`. Use `h _ hm a ha` as an intermediate fact. Rewrite `this` using `[trF_smul, liftV_mul, map_mul (evFin F v), AlgHom.commutes]`. Then use the resulting hypothesis.
-/
theorem mem_latW_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {W : Spc F E d} {r s : ℕ} (hW : W.IsSkew σ B r s) (v : Pl F)
    {w : Fin d → AE F E} (hw : At (evFin F v) w)
    (h : ∀ y ∈ W.L, ∀ a ∈ v.adicCompletionIntegers F, B.ψ (liftV v a * trF σ W.J y w) = 1) : w ∈ latW W v := by
  have hσ := sigma_sigma hB.cm
  have : Module.Finite (𝓞 F) (𝓞 E) := Module.Finite.of_restrictScalars_finite ℤ _ _
  obtain ⟨m, g, f, hg, hf, hid⟩ := dual_family (𝓞 F) F (W.L.restrictScalars (𝓞 F)) (hW.lat.fg.restrictScalars) (by
    rw [eq_top_iff]
    intro x _
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (Algebra.algebraMapSubmonoid (𝓞 E) ℤ⁰) E
      (W.L : Set (Fin d → E)) x (hW.lat.span_eq_top ▸ Submodule.mem_top)
    obtain ⟨_, k, hk, rfl⟩ := t
    rw [Submodule.span_eq] at ht
    have hk0 : (k : F) ≠ 0 := Int.cast_ne_zero.2 (nonZeroDivisors.ne_zero hk)
    have ht' : (k : F) • x ∈ W.L := by
      rw [Int.cast_smul_eq_zsmul, ← algebraMap_smul (𝓞 E) k x]; exact ht
    rw [← inv_smul_smul₀ hk0 x]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ht'))
  choose u hu using fun i => exists_tr_rep hσ (skew_det hW) (f i)
  have hdec : ∀ z : Fin d → AE F E, z = ∑ i, trF σ W.J (u i) z • incV (g i) := fun z => by
    have hz := span_incV z
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨x, rfl⟩ := hz
      simp only [trF_incV, ← hu]
      ext j
      conv_lhs => rw [hid x]
      simp only [incV, Finset.sum_apply, Pi.smul_apply, map_sum, algebraMap_smul]
      exact Finset.sum_congr rfl fun i _ =>
        map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) _ _
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, add_smul, Finset.sum_add_distrib, ← hx, ← hy]
    | smul a x _ hx => simp only [map_smul, smul_eq_mul, mul_smul, ← Finset.smul_sum, ← hx]
  rw [hdec w]
  refine sum_mem fun i _ => AddSubgroup.subset_closure ⟨_, fun a ha => ?_, ?_, g i, hg i, rfl⟩
  · rw [← map_smul, hw a ha, map_zero]
  · refine mem_int_of_psi hB.std v _ fun t ht a ha => ?_
    have hm : algebraMap F E t • u i ∈ W.L := (hW.dual _).2 fun x hx o => by
      let o' : 𝓞 E := ⟨σ o, (RingOfIntegers.isIntegral_coe o).map (σ.restrictScalars ℤ)⟩
      obtain ⟨c, hc⟩ := hf i _ (W.L.smul_mem o' hx)
      have e : (o : E) * form σ W.J (algebraMap F E t • u i) x = t • form σ W.J (u i) (o' • x) := by
        rw [form_eq, form_eq, Algebra.smul_def t, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        have : (o' • x) l = σ o * x l := rfl
        rw [this, map_mul, hσ, Matrix.smul_vecMul, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, ← Algebra.trace_trace (S := F), map_smul, ← hu, ← hc, smul_eq_mul]
      obtain ⟨k, hk⟩ := (FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))).1 ht _
        ((FractionalIdeal.mem_one_iff _).2 ⟨c, rfl⟩)
      rw [Algebra.traceForm_apply] at hk
      rw [← hk]
      exact isIntegral_algebraMap
    have := h _ hm a ha
    rwa [trF_smul, liftV_mul, map_mul (evFin F v), AlgHom.commutes] at this
/- English proof (translation)
Establish `hσ` using `sigma_sigma hB.cm`. Take `⟨m, g, f, hg, hf, hid⟩` from `dual_family (𝓞 E) E X.L hX.lat.fg hX.lat.span_eq_top`. Set `a : Fin m → Fin n → E` to `fun i k => f i (Pi.single k 1)`. Set `u : Fin m → Fin n → E` to `fun i => (fun k => σ (a i k)) ᵥ* X.J⁻¹`. Establish `hu : ∀ i, u i ᵥ* X.J = fun k => σ (a i k)` using `fun i => by`.

Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (herm_det hX), Matrix.vecMul_one]`. Establish `huL : ∀ i, u i ∈ X.L` using `fun i => (hX.dual _).2 fun x hx => by`. Take `⟨c, hc⟩` from `hf i x hx`. Establish `e : form σ X.J (u i) x = σ (f i x)`. Rewrite using `[form_eq, hu, LinearMap.pi_apply_eq_sum_univ (f i) x, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, map_mul, mul_comm]`. Establish `: (fun j => if k = j then (1 : E) else 0) = Pi.single k 1` using `funext fun j => by`. Rewrite using `[Pi.single_apply]`. Conclude with `if_congr eq_comm rfl rfl`.

Rewrite using `[this]`. Rewrite using `[e, ← hc]`. Conclude with `(RingOfIntegers.isIntegral_coe c).map (σ.restrictScalars ℤ)`. Establish `hdec : z = ∑ i, Matrix.vecMulVec (incV (g i)) (incV (a i) ᵥ* z)`. Use extensionality with `p l`.

Establish `e : ∀ k, ∑ i, incV (F` using `F) (g i) p * incV (a i) k = (1 : Matrix (Fin n) (Fin n) (AE F E)) p k := fun k => by`. Use `congrFun (hid (Pi.single k 1)) p` as an intermediate fact. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this`. Simplify using `only [incV, ← map_mul, ← map_sum, mul_comm (g _ p), a, ← this, Pi.single_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, ← mul_assoc]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_mul, e]`. Conclude with `(congrFun (congrFun (Matrix.one_mul z) p) l).symm`. Rewrite using `[hdec]`.

Use `sum_mem fun i _ => vecMulVec_mem (hg i) (_root_.PositivityTheory.ThK.Vac.mem_latW_k hB hW v (fun c hc => ?_) fun y hy c hc => ?_)` and prove the remaining obligations. Rewrite using `[← Matrix.vecMul_smul, hz c hc, Matrix.vecMul_zero]`. Use `h _ (neg_mem (AddSubgroup.subset_closure ⟨liftV v c, at_liftV v c, by rwa [evFin_liftV], u i, huL i, y, hy, rfl⟩))` as an intermediate fact. Rewrite `this` using `[GlobalTheory.LatVacArith.symp_neg_left, ← one_smul (AF F) z, symp_smul_smul, symp_vecMulVec hσ, hu]`. Simplify `this` using `only [hσ, mul_one, mul_neg, neg_neg]`.
-/
theorem mem_latAtV_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {X : Spc F E n} {W : Spc F E d} {r s r' s' : ℕ} (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (v : Pl F) {z : Matrix (Fin n) (Fin d) (AE F E)} (hz : At (evFin F v) z)
    (h : ∀ γ ∈ latAtV X W v, B.ψ (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) γ z) = 1) : z ∈ latAtV X W v := by
  have hσ := sigma_sigma hB.cm
  obtain ⟨m, g, f, hg, hf, hid⟩ := dual_family (𝓞 E) E X.L hX.lat.fg hX.lat.span_eq_top
  let a : Fin m → Fin n → E := fun i k => f i (Pi.single k 1)
  let u : Fin m → Fin n → E := fun i => (fun k => σ (a i k)) ᵥ* X.J⁻¹
  have hu : ∀ i, u i ᵥ* X.J = fun k => σ (a i k) := fun i => by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (herm_det hX), Matrix.vecMul_one]
  have huL : ∀ i, u i ∈ X.L := fun i => (hX.dual _).2 fun x hx => by
    obtain ⟨c, hc⟩ := hf i x hx
    have e : form σ X.J (u i) x = σ (f i x) := by
      rw [form_eq, hu, LinearMap.pi_apply_eq_sum_univ (f i) x, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_eq_mul, map_mul, mul_comm]
      have : (fun j => if k = j then (1 : E) else 0) = Pi.single k 1 := funext fun j => by
        rw [Pi.single_apply]; exact if_congr eq_comm rfl rfl
      rw [this]
    rw [e, ← hc]
    exact (RingOfIntegers.isIntegral_coe c).map (σ.restrictScalars ℤ)
  have hdec : z = ∑ i, Matrix.vecMulVec (incV (g i)) (incV (a i) ᵥ* z) := by
    ext p l
    have e : ∀ k, ∑ i, incV (F := F) (g i) p * incV (a i) k = (1 : Matrix (Fin n) (Fin n) (AE F E)) p k := fun k => by
      have := congrFun (hid (Pi.single k 1)) p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp only [incV, ← map_mul, ← map_sum, mul_comm (g _ p), a, ← this, Pi.single_apply, Matrix.one_apply]
      split_ifs <;> simp
    simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, e]
    exact (congrFun (congrFun (Matrix.one_mul z) p) l).symm
  rw [hdec]
  refine sum_mem fun i _ => vecMulVec_mem (hg i) (_root_.PositivityTheory.ThK.Vac.mem_latW_k hB hW v (fun c hc => ?_) fun y hy c hc => ?_)
  · rw [← Matrix.vecMul_smul, hz c hc, Matrix.vecMul_zero]
  · have := h _ (neg_mem (AddSubgroup.subset_closure ⟨liftV v c, at_liftV v c, by rwa [evFin_liftV], u i, huL i, y, hy, rfl⟩))
    rw [GlobalTheory.LatVacArith.symp_neg_left, ← one_smul (AF F) z, symp_smul_smul, symp_vecMulVec hσ, hu] at this
    simpa only [hσ, mul_one, mul_neg, neg_neg] using this
end PositivityTheory.ThK.Vac
end
end
