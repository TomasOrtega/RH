import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.BMat

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.C5.Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def linearFormAdelic (δ : E) : AE F E →ₗ[AF F] AF F :=
  (Algebra.TensorProduct.rid F (AF F) (AF F)).toLinearMap ∘ₗ
    LinearMap.baseChange (AF F) (Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inclR_eq' (x : E) : inclR (F := F) (AF F) x = (1 : AF F) ⊗ₜ[F] x := rfl

/- English proof (translation)
Take `⟨τ⟩` from `(inferInstance : Nonempty (E →+* ℂ))`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]`.
-/
theorem sigma_invol' {B : Base F E} (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Take `⟨τ⟩` from `(inferInstance : Nonempty (E →+* ℂ))`. Establish `hc : (NumberField.InfinitePlace.mk τ).IsComplex` using `hB.cm.2.1.isComplex _`. Rewrite `hc` using `[NumberField.InfinitePlace.isComplex_mk_iff]`.

Apply `hc` to reduce the goal to its premises. Use `show NumberField.ComplexEmbedding.conjugate τ = τ`. Use extensionality with `x`. Rewrite using `[NumberField.ComplexEmbedding.conjugate_coe_eq]`. Use `show star (τ x) = τ x`.

Rewrite using `[← hB.cm.2.2.2 τ x, hne x]`.
-/
theorem exists_ne_sigma {B : Base F E} (hB : B.IsGood σ) : ∃ x : E, σ x ≠ x := by
  by_contra hne
  push Not at hne
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have hc : (NumberField.InfinitePlace.mk τ).IsComplex := hB.cm.2.1.isComplex _
  rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  show NumberField.ComplexEmbedding.conjugate τ = τ
  ext x
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  show star (τ x) = τ x
  rw [← hB.cm.2.2.2 τ x, hne x]

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `hli : LinearIndependent F ![(1 : E), q]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s t hst`.

Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality. Use `⟨?_, rfl⟩` and prove the remaining obligations. Simplify using `using hst`. It suffices to derive a contradiction.

Apply `hne (-(s / t))` to reduce the goal to its premises. Establish `h1 : t • q = -(s • (1 : E))` using `eq_neg_of_add_eq_zero_right hst`. Establish `h2 : q = t⁻¹ • -(s • (1 : E))` using `by rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]`. Rewrite using `[h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]`. Establish `hcard : Fintype.card (Fin 2) = Module.finrank F E` using `by rw [hB.cm.2.2.1]; rfl`.

Establish `hspan` using `hli.span_eq_top_of_card_eq_finrank hcard`. Establish `hσid : σ.toLinearMap = LinearMap.id`. Use `LinearMap.ext_on_range hspan fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Simplify using the standard rewrite rules.

Simplify using `using hq`. Take `⟨x, hx⟩` from `exists_ne_sigma hB`. Conclude with `hx (by simpa using LinearMap.congr_fun hσid x)`.
-/
theorem fixed_mem {B : Base F E} (hB : B.IsGood σ) {q : E} (hq : σ q = q) : ∃ f : F, algebraMap F E f = q := by
  by_contra hne
  push Not at hne
  have hli : LinearIndependent F ![(1 : E), q] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      refine ⟨?_, rfl⟩
      simpa using hst
    · exfalso
      apply hne (-(s / t))
      have h1 : t • q = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : q = t⁻¹ • -(s • (1 : E)) := by rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [hB.cm.2.2.1]; rfl
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hσid : σ.toLinearMap = LinearMap.id := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    fin_cases i
    · simp
    · simpa using hq
  obtain ⟨x, hx⟩ := exists_ne_sigma hB
  exact hx (by simpa using LinearMap.congr_fun hσid x)

/- English proof (translation)
Establish `hk0 : (k : E) ≠ 0`. Introduce `h`. Establish `h1 : ((k * k : ℤ) : E) = 1` using `by rw [hk]; simp`. Rewrite `h1` using `[Int.cast_mul, h, zero_mul]`. Conclude with `zero_ne_one h1`.

Establish `hfix : σ (y / δ) = y / δ`. Rewrite using `[map_div₀, hy, hδ, mul_div_mul_left _ _ hk0]`. Take `⟨f, hf⟩` from `fixed_mem hB hfix`. Use `⟨f, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, hf, div_mul_cancel₀ _ hδ0]`.
-/
theorem eig_line {B : Base F E} (hB : B.IsGood σ) {k : ℤ} (hk : k * k = 1) {δ y : E} (hδ0 : δ ≠ 0)
    (hδ : σ δ = (k : E) * δ) (hy : σ y = (k : E) * y) : ∃ f : F, y = f • δ := by
  have hk0 : (k : E) ≠ 0 := by
    intro h
    have h1 : ((k * k : ℤ) : E) = 1 := by rw [hk]; simp
    rw [Int.cast_mul, h, zero_mul] at h1
    exact zero_ne_one h1
  have hfix : σ (y / δ) = y / δ := by
    rw [map_div₀, hy, hδ, mul_div_mul_left _ _ hk0]
  obtain ⟨f, hf⟩ := fixed_mem hB hfix
  refine ⟨f, ?_⟩
  rw [Algebra.smul_def, hf, div_mul_cancel₀ _ hδ0]

/- English proof (translation)
Establish `hex : ∃ ℓ : E →ₗ[F] F, δ ≠ 0 → ℓ δ = 1`. Establish `: ¬ ∀ φ : Module.Dual F E, φ δ = 0` using `fun h => hδ0 ((Module.forall_dual_apply_eq_zero_iff F δ).1 h)`. Use `push Not at this`. Take `⟨φ, hφ⟩` from `this`. Conclude with `⟨(φ δ)⁻¹ • φ, fun _ => by simp [hφ]⟩`.

Conclude with `Classical.epsilon_spec hex hδ0`.
-/
theorem ell_spec {δ : E} (hδ0 : δ ≠ 0) : (Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1) δ = 1 := by
  have hex : ∃ ℓ : E →ₗ[F] F, δ ≠ 0 → ℓ δ = 1 := by
    have : ¬ ∀ φ : Module.Dual F E, φ δ = 0 := fun h => hδ0 ((Module.forall_dual_apply_eq_zero_iff F δ).1 h)
    push Not at this
    obtain ⟨φ, hφ⟩ := this
    exact ⟨(φ δ)⁻¹ • φ, fun _ => by simp [hφ]⟩
  exact Classical.epsilon_spec hex hδ0

/- English proof (translation)
Rewrite using `[inclR_eq', TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Simplify using `[linearFormAdelic, LinearMap.baseChange_tmul, ell_spec hδ0]`.
-/
theorem ellA_smul_inclR {δ : E} (hδ0 : δ ≠ 0) (a : AF F) : linearFormAdelic (F := F) δ (a • inclR (F := F) (AF F) δ) = a := by
  rw [inclR_eq', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp [linearFormAdelic, LinearMap.baseChange_tmul, ell_spec hδ0]

/- English proof (translation)
Use `⟨(Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1) e, ?_⟩` and prove the remaining obligations. Rewrite using `[inclR_eq']`. Simplify using `[linearFormAdelic, LinearMap.baseChange_tmul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem ellA_inclR (δ : E) (e : E) : ∃ f : F, linearFormAdelic (F := F) δ (inclR (F := F) (AF F) e) = algebraMap F (AF F) f := by
  refine ⟨(Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1) e, ?_⟩
  rw [inclR_eq']
  simp [linearFormAdelic, LinearMap.baseChange_tmul, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Establish `hinv` using `sigma_invol' hB`. Use `set ℓ : E →ₗ[F] F := Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1 with hℓdef`. Establish `hℓ : ℓ δ = 1` using `ell_spec hδ0`. Establish `hsm : ∀ x : E, (k : F) • x = (k : E) * x` using `fun x => by rw [Algebra.smul_def, map_intCast]`. Establish `hkk : (k : F) * k = 1` using `by exact_mod_cast hk`.

Set `g : E →ₗ[F] E` to `ℓ.smulRight δ`. Set `p : E →ₗ[F] E` to `LinearMap.id + (k : F) • σ.toLinearMap`. Establish `hzero : (LinearMap.id - g) ∘ₗ p = 0`. Use extensionality with `e`. Establish `hw : σ (e + (k : F) • σ e) = (k : E) * (e + (k : F) • σ e)`.

Rewrite using `[hsm (σ e), map_add, map_mul, map_intCast, hinv, mul_add, ← mul_assoc, ← Int.cast_mul, hk, Int.cast_one, one_mul, add_comm]`. Take `⟨f, hf⟩` from `eig_line hB hk hδ0 hδ hw`. Use `show (e + (k : F) • σ e) - ℓ (e + (k : F) • σ e) • δ = 0`. Rewrite using `[hf, map_smul, hℓ, smul_eq_mul, mul_one, sub_self]`. Establish `hbc : ∀ w : AE F E, (LinearMap.id - g).baseChange (AF F) w = w - linearFormAdelic (F` using `F) δ w • inclR (F := F) (AF F) δ := by`.

Introduce `w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Rewrite using `[LinearMap.baseChange_tmul, inclR_eq', TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Simplify using `[linearFormAdelic, g, LinearMap.baseChange_tmul, TensorProduct.tmul_sub, TensorProduct.smul_tmul]`. Both sides reduce to the same expression. Consider the case `add x y hx hy`. Rewrite using `[map_add, hx, hy, map_add, add_smul]`. Normalize the expressions using the abelian group laws.

Establish `hpc : ∀ w : AE F E, p.baseChange (AF F) w = w + (k : F) • cA σ w`. Introduce `w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`.

Simplify using `[p, cA, LinearMap.baseChange_tmul]`. Consider the case `add x y hx hy`. Rewrite using `[map_add, hx, hy, map_add, smul_add]`. Normalize the expressions using the abelian group laws. Establish `hkz : (k : F) • cA σ z = z`.

Rewrite using `[hz, show ((k : ℤ) : AE F E) = algebraMap F (AE F E) (k : F) by rw [map_intCast], ← Algebra.smul_def, smul_smul, hkk, one_smul]`. Establish `h2 : p.baseChange (AF F) z = (2 : F) • z`. Rewrite using `[hpc, hkz, two_smul]`. Establish `h0 : (LinearMap.id - g).baseChange (AF F) (p.baseChange (AF F) z) = 0`. Rewrite using `[← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hzero, LinearMap.baseChange_zero, LinearMap.zero_apply]`.

Rewrite `h0` using `[h2, LinearMap.map_smul_of_tower, hbc]`. Conclude with `(sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left two_ne_zero))`.
-/
theorem eig_AE {B : Base F E} (hB : B.IsGood σ) {k : ℤ} (hk : k * k = 1) {δ : E} (hδ0 : δ ≠ 0)
    (hδ : σ δ = (k : E) * δ) {z : AE F E} (hz : cA σ z = (k : AE F E) * z) :
    z = linearFormAdelic (F := F) δ z • inclR (F := F) (AF F) δ := by
  have hinv := sigma_invol' hB
  set ℓ : E →ₗ[F] F := Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1 with hℓdef
  have hℓ : ℓ δ = 1 := ell_spec hδ0
  have hsm : ∀ x : E, (k : F) • x = (k : E) * x := fun x => by rw [Algebra.smul_def, map_intCast]
  have hkk : (k : F) * k = 1 := by exact_mod_cast hk
  let g : E →ₗ[F] E := ℓ.smulRight δ
  let p : E →ₗ[F] E := LinearMap.id + (k : F) • σ.toLinearMap
  have hzero : (LinearMap.id - g) ∘ₗ p = 0 := by
    ext e
    have hw : σ (e + (k : F) • σ e) = (k : E) * (e + (k : F) • σ e) := by
      rw [hsm (σ e), map_add, map_mul, map_intCast, hinv, mul_add, ← mul_assoc, ← Int.cast_mul, hk, Int.cast_one, one_mul,
        add_comm]
    obtain ⟨f, hf⟩ := eig_line hB hk hδ0 hδ hw
    show (e + (k : F) • σ e) - ℓ (e + (k : F) • σ e) • δ = 0
    rw [hf, map_smul, hℓ, smul_eq_mul, mul_one, sub_self]
  have hbc : ∀ w : AE F E, (LinearMap.id - g).baseChange (AF F) w = w - linearFormAdelic (F := F) δ w • inclR (F := F) (AF F) δ := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [LinearMap.baseChange_tmul, inclR_eq', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [linearFormAdelic, g, LinearMap.baseChange_tmul, TensorProduct.tmul_sub, TensorProduct.smul_tmul]
      rfl
    | add x y hx hy =>
      rw [map_add, hx, hy, map_add, add_smul]
      abel
  have hpc : ∀ w : AE F E, p.baseChange (AF F) w = w + (k : F) • cA σ w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      simp [p, cA, LinearMap.baseChange_tmul]
    | add x y hx hy =>
      rw [map_add, hx, hy, map_add, smul_add]
      abel
  have hkz : (k : F) • cA σ z = z := by
    rw [hz, show ((k : ℤ) : AE F E) = algebraMap F (AE F E) (k : F) by rw [map_intCast], ← Algebra.smul_def, smul_smul, hkk,
      one_smul]
  have h2 : p.baseChange (AF F) z = (2 : F) • z := by
    rw [hpc, hkz, two_smul]
  have h0 : (LinearMap.id - g).baseChange (AF F) (p.baseChange (AF F) z) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hzero, LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [h2, LinearMap.map_smul_of_tower, hbc] at h0
  exact (sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left two_ne_zero))

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap (R := AF F) (linearFormAdelic (F := F) (E := E) δ)`.
-/
theorem continuous_ellA (δ : E) : Continuous (linearFormAdelic (F := F) (E := E) δ) :=
  IsModuleTopology.continuous_of_linearMap (R := AF F) (linearFormAdelic (F := F) (E := E) δ)

end PositivityTheory.SiegelWeilFormula.Act.C5.Meas

end
