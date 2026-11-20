import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf

noncomputable section

namespace GlobalTheory.CompanionTheory.DiscriminantUnit

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gen PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

/- English proof (translation)
Establish `hσw : σS w = -w`. Establish `h1 : σS w * σS u = 1` using `by rw [← map_mul, hw, map_one]`. Rewrite `h1` using `[hu]`. Take the linear combination `(-w) * h1 - (σS w) * hw`. Use `⟨isUnit_iff_exists_inv.2 ⟨t * w, ?_⟩, fun a => ⟨(a + σS a) * t, (a - σS a) * t * w, ?_, ?_, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[hu]`. Take the linear combination `(w * u) * h2 + hw`. Rewrite using `[map_mul, map_add, hinv, ht]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_mul, map_sub, hinv, ht, hσw]`.

Expand and normalize the polynomial expressions, which then agree. Take the linear combination `(-a) * h2 - (a - σS a) * t * hw`.
-/
theorem decomp {S : Type*} [CommRing S] (σS : S →+* S) (hinv : ∀ a, σS (σS a) = a) {u t w : S}
    (hu : σS u = -u) (ht : σS t = t) (h2 : t * 2 = 1) (hw : w * u = 1) :
    IsUnit (u - σS u) ∧ ∀ a, ∃ x y, σS x = x ∧ σS y = y ∧ a = x + y * u := by
  have hσw : σS w = -w := by
    have h1 : σS w * σS u = 1 := by rw [← map_mul, hw, map_one]
    rw [hu] at h1
    linear_combination (-w) * h1 - (σS w) * hw
  refine ⟨isUnit_iff_exists_inv.2 ⟨t * w, ?_⟩, fun a => ⟨(a + σS a) * t, (a - σS a) * t * w, ?_, ?_, ?_⟩⟩
  · rw [hu]
    linear_combination (w * u) * h2 + hw
  · rw [map_mul, map_add, hinv, ht]
    ring
  · rw [map_mul, map_mul, map_sub, hinv, ht, hσw]
    ring
  · linear_combination (-a) * h2 - (a - σS a) * t * hw

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem conj_conj (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Use `haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1`. Break down `eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h0` into its components or cases. Establish `: e ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `he`. Rewrite `this` using `[h0, Algebra.mem_bot]`. Conclude with `this`.

It suffices to derive a contradiction. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Use `haveI := h.2.1`. Use `IsTotallyComplex.complexEmbedding_not_isReal τ ?_` and prove the remaining obligations. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Establish `hx : x ∈ AlgHom.equalizer σ (AlgHom.id F E)` using `h0 ▸ Algebra.mem_top`. Establish `hx' : σ x = x` using `hx`. Use `h.2.2.2 τ x` as an intermediate fact. Rewrite `this` using `[hx']`.

Conclude with `this.symm`.
-/
theorem exists_of_conj_eq (h : IsCMExt F E σ) (e : E) (he : σ e = e) :
    ∃ f, algebraMap F E f = e := by
  haveI := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h0
  · have : e ∈ AlgHom.equalizer σ (AlgHom.id F E) := he
    rw [h0, Algebra.mem_bot] at this
    exact this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    haveI := h.2.1
    refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := h0 ▸ Algebra.mem_top
    have hx' : σ x = x := hx
    have := h.2.2.2 τ x
    rw [hx'] at this
    exact this.symm

/- English proof (translation)
Establish `hσ` using `conj_conj h`. Take `⟨a, ha⟩` from `exists_of_conj_eq h (e + σ e) (by rw [map_add, hσ, add_comm])`. Establish `h1 : Algebra.trace F E (σ e) = Algebra.trace F E e` using `Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e`. Establish `h3` using `congrArg (Algebra.trace F E) ha`. Rewrite `h3` using `[Algebra.trace_algebraMap, h.2.2.1, map_add, h1, two_smul, ← two_mul, ← two_mul]`.

Rewrite using `[← ha, mul_left_cancel₀ two_ne_zero h3]`.
-/
theorem trace_field (h : IsCMExt F E σ) (e : E) :
    algebraMap F E (Algebra.trace F E e) = e + σ e := by
  have hσ := conj_conj h
  obtain ⟨a, ha⟩ := exists_of_conj_eq h (e + σ e) (by rw [map_add, hσ, add_comm])
  have h1 : Algebra.trace F E (σ e) = Algebra.trace F E e :=
    Algebra.trace_eq_of_algEquiv (AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)) e
  have h3 := congrArg (Algebra.trace F E) ha
  rw [Algebra.trace_algebraMap, h.2.2.1, map_add, h1, two_smul, ← two_mul, ← two_mul] at h3
  rw [← ha, mul_left_cancel₀ two_ne_zero h3]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `tmul a e`.

Establish `h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Establish `h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e)`. Rewrite using `[h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, smul_eq_mul]`. Establish `h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e` using `rfl`.

Rewrite using `[h3, h4, ← TensorProduct.tmul_add, ← trace_field h, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]`.
-/
theorem trace_tensor (R : Type) [CommRing R] [Algebra F R] (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.trace R (R ⊗[F] E) z) = z + sigR R σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]; ring
  | tmul a e =>
    have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h3 : Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) =
        a * algebraMap F R (Algebra.trace F E e) := by
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    have h4 : sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl
    rw [h3, h4, ← TensorProduct.tmul_add, ← trace_field h, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, mul_comm, ← Algebra.smul_def,
      TensorProduct.smul_tmul, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul a e => show a ⊗ₜ[F] σ (σ e) = _`. Rewrite using `[conj_conj h]`.
-/
theorem sigR_sigR (R : Type) [CommRing R] [Algebra F R] (h : IsCMExt F E σ) (z : R ⊗[F] E) :
    sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [conj_conj h]

/- English proof (translation)
Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem sigR_scalar (R : Type) [CommRing R] [Algebra F R] (c : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) c) = algebraMap R (R ⊗[F] E) c := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

/- English proof (translation)
Rewrite using `[Algebra.discr_def, Matrix.det_fin_two]`. Simplify using `only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, trace_field h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem discr_eq (h : IsCMExt F E σ) (bs : Module.Basis (Fin 2) F E) :
    algebraMap F E (Algebra.discr F ⇑bs) = (bs 0 * σ (bs 1) - bs 1 * σ (bs 0)) ^ 2 := by
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, map_sub, map_mul, trace_field h]
  ring

section Ring

variable {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)} {S : Subring (Fv F v ⊗[F] E)}

/- English proof (translation)
Establish `h1 : x ∈ Rv bs v`. Rewrite using `[← hcar]`. Conclude with `hx`. Establish `h2 : β • x ∈ Rv bs v` using `fun k => by`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Conclude with `mul_mem hβ (h1 k)`. Rewrite `h2` using `[← hcar]`. Conclude with `h2`.
-/
theorem smul_mem (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) {β : Fv F v}
    (hβ : β ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E} (hx : x ∈ S) : β • x ∈ S := by
  have h1 : x ∈ Rv bs v := by
    rw [← hcar]
    exact hx
  have h2 : β • x ∈ Rv bs v := fun k => by
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hβ (h1 k)
  rw [← hcar] at h2
  exact h2

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `smul_mem hcar hβ (one_mem S)`.
-/
theorem scalar_mem (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) {β : Fv F v}
    (hβ : β ∈ v.adicCompletionIntegers F) : algebraMap (Fv F v) (Fv F v ⊗[F] E) β ∈ S := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact smul_mem hcar hβ (one_mem S)

/- English proof (translation)
Establish `h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v` using `fun k => by`. Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`.

Rewrite `h` using `[← hcar]`. Conclude with `h`.
-/
theorem basis_mem (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) (i : Fin d) :
    Algebra.TensorProduct.basis (Fv F v) bs i ∈ S := by
  have h : Algebra.TensorProduct.basis (Fv F v) bs i ∈ Rv bs v := fun k => by
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  rw [← hcar] at h
  exact h

/- English proof (translation)
Rewrite using `[Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis (Fv F v) bs), Matrix.trace]`. Use `sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]`. Establish `h1 : a * Algebra.TensorProduct.basis (Fv F v) bs k ∈ Rv bs v`. Rewrite using `[← hcar]`.

Conclude with `mul_mem ha (basis_mem hcar k)`. Conclude with `h1 k`.
-/
theorem trace_mem (hcar : (S : Set (Fv F v ⊗[F] E)) = Rv bs v) {a : Fv F v ⊗[F] E} (ha : a ∈ S) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) a ∈ v.adicCompletionIntegers F := by
  rw [Algebra.trace_eq_matrix_trace (Algebra.TensorProduct.basis (Fv F v) bs), Matrix.trace]
  refine sum_mem fun k _ => ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul]
  have h1 : a * Algebra.TensorProduct.basis (Fv F v) bs k ∈ Rv bs v := by
    rw [← hcar]
    exact mul_mem ha (basis_mem hcar k)
  exact h1 k

/- English proof (translation)
Establish `h` using `hI (2 : F)⁻¹ (by classical exact Finset.mem_union_right _ (by simp))`. Rewrite `h` using `[map_inv₀, map_ofNat]`. Then use the resulting hypothesis.
-/
theorem half_mem (hI : IntAt v (basisSet σ bs)) : (2 : Fv F v)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h := hI (2 : F)⁻¹ (by classical exact Finset.mem_union_right _ (by simp))
  rwa [map_inv₀, map_ofNat] at h

/- English proof (translation)
The claim follows from `hI _ (by classical exact Finset.mem_union_right _ (by simp))`.
-/
theorem discr_mem (hI : IntAt v (basisSet σ bs)) :
    algebraMap F (Fv F v) (Algebra.discr F (⇑bs))⁻¹ ∈ v.adicCompletionIntegers F :=
  hI _ (by classical exact Finset.mem_union_right _ (by simp))

end Ring

/- English proof (translation)
Take `⟨hcm, hI, hcar, hsig, hϖ0, hϖ1, hϖd, hϖc⟩` from `hH`. Establish `h20 : (2 : Fv F v) ≠ 0`. Establish `h` using `(algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))`. Rewrite `h` using `[map_ofNat, map_zero]`. Then use the resulting hypothesis. Establish `e2 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 : Fv F v)⁻¹ * 2 = 1`.

Rewrite using `[← map_ofNat (algebraMap (Fv F v) (Fv F v ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ h20, map_one]`. Establish `hfix : sigR (Fv F v) σ (a : Fv F v ⊗[F] E) = a` using `by rw [← hsig, ha]`. Establish `hc1` using `trace_tensor (Fv F v) hcm (a : Fv F v ⊗[F] E)`. Rewrite `hc1` using `[hfix]`. Use `set c : Fv F v := (2 : Fv F v)⁻¹ * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v ⊗[F] E) with hc`.

Establish `hcO : c ∈ v.adicCompletionIntegers F` using `mul_mem (half_mem hI) (trace_mem hcar a.2)`. Establish `hac : (a : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c`. Rewrite using `[hc, map_mul, hc1, ← two_mul, ← mul_assoc, e2, one_mul]`. Distinguish the cases in `hlt : ‖c‖ < 1`. It suffices to derive a contradiction.

Apply `hn` to reduce the goal to its premises. Take `⟨c', hc'⟩` from `hϖd ⟨c, hcO⟩ hlt`. Establish `hc'' : c = (ϖ : Fv F v) * (c' : Fv F v)` using `congrArg Subtype.val hc'`. Use `Ideal.mem_span_singleton'.2 ⟨⟨_, scalar_mem hcar c'.2⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, Subring.coe_mul, hac, hc'', map_mul, mul_comm]`.

Establish `hle : ‖c‖ ≤ 1`. Establish `h` using `hcO`. Rewrite `h` using `[HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff]`. Then use the resulting hypothesis. Establish `h1 : ‖c‖ = 1` using `le_antisymm hle (not_lt.1 hlt)`. Establish `hc0 : c ≠ 0`.

Introduce `h`. Rewrite `h1` using `[h, norm_zero]`. Conclude with `zero_ne_one h1`. Establish `hinvO : c⁻¹ ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, norm_inv, h1, inv_one]`.

Use `isUnit_iff_exists_inv.2 ⟨⟨_, scalar_mem hcar hinvO⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Subring.coe_mul, hac]`. Use `show algebraMap (Fv F v) (Fv F v ⊗[F] E) c * algebraMap (Fv F v) (Fv F v ⊗[F] E) c⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel₀ hc0, map_one]`.
-/
theorem fixed_isUnit {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {S : Subring (Fv F v ⊗[F] E)} {σS : S →+* S} {ϖ : v.adicCompletionIntegers F}
    (hH : QuadHyp σ bs v S σS ϖ) (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S) (a : S) (ha : σS a = a)
    (hn : a ∉ lev (⟨_, hϖ⟩ : S) 1) : IsUnit a := by
  obtain ⟨hcm, hI, hcar, hsig, hϖ0, hϖ1, hϖd, hϖc⟩ := hH
  have h20 : (2 : Fv F v) ≠ 0 := by
    have h := (algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at h
  have e2 : algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 : Fv F v)⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap (Fv F v) (Fv F v ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ h20, map_one]
  have hfix : sigR (Fv F v) σ (a : Fv F v ⊗[F] E) = a := by rw [← hsig, ha]
  have hc1 := trace_tensor (Fv F v) hcm (a : Fv F v ⊗[F] E)
  rw [hfix] at hc1
  set c : Fv F v := (2 : Fv F v)⁻¹ * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (a : Fv F v ⊗[F] E) with hc
  have hcO : c ∈ v.adicCompletionIntegers F := mul_mem (half_mem hI) (trace_mem hcar a.2)
  have hac : (a : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) c := by
    rw [hc, map_mul, hc1, ← two_mul, ← mul_assoc, e2, one_mul]
  by_cases hlt : ‖c‖ < 1
  · exfalso
    apply hn
    obtain ⟨c', hc'⟩ := hϖd ⟨c, hcO⟩ hlt
    have hc'' : c = (ϖ : Fv F v) * (c' : Fv F v) := congrArg Subtype.val hc'
    refine Ideal.mem_span_singleton'.2 ⟨⟨_, scalar_mem hcar c'.2⟩, Subtype.ext ?_⟩
    rw [pow_one, Subring.coe_mul, hac, hc'', map_mul, mul_comm]
  · have hle : ‖c‖ ≤ 1 := by
      have h := hcO
      rwa [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff] at h
    have h1 : ‖c‖ = 1 := le_antisymm hle (not_lt.1 hlt)
    have hc0 : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at h1
      exact zero_ne_one h1
    have hinvO : c⁻¹ ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← Valued.toNormedField.norm_le_one_iff, norm_inv, h1,
        inv_one]
    refine isUnit_iff_exists_inv.2 ⟨⟨_, scalar_mem hcar hinvO⟩, Subtype.ext ?_⟩
    rw [Subring.coe_mul, hac]
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) c * algebraMap (Fv F v) (Fv F v ⊗[F] E) c⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ hc0, map_one]

/- English proof (translation)
Take `⟨hcm, hI, hcar, hsig, -⟩` from `hH`. Establish `hd : d = 2`. Establish `h` using `Module.finrank_eq_card_basis bs`. Rewrite `h` using `[hcm.2.2.1]`. Simplify using `using h.symm`.

Substitute `hd` using the available equality. Establish `h20 : (2 : Fv F v) ≠ 0`. Establish `h` using `(algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))`. Rewrite `h` using `[map_ofNat, map_zero]`. Then use the resulting hypothesis. Establish `hinv : ∀ a, σS (σS a) = a` using `fun a => Subtype.ext (by rw [hsig, hsig, sigR_sigR _ hcm])`.

Set `ι : E →ₐ[F] Fv F v ⊗[F] E` to `Algebra.TensorProduct.includeRight`. Set `B : Fin 2 → S` to `fun i => ⟨_, basis_mem hcar i⟩`. Establish `hB : ∀ i, ((B i : S) : Fv F v ⊗[F] E) = ι (bs i)` using `fun i => Algebra.TensorProduct.basis_apply _ _`. Establish `hσB : ∀ i, ((σS (B i) : S) : Fv F v ⊗[F] E) = ι (σ (bs i))` using `fun i => by`. Rewrite using `[hsig, hB]`.

Both sides reduce to the same expression. Take `⟨u, hudef⟩ : ∃ u : S, u = B 0 * σS (B 1) - B 1 * σS (B 0)` from `⟨_, rfl⟩`. Establish `hu : σS u = -u`. Rewrite using `[hudef, map_sub, map_mul, map_mul, hinv, hinv]`. Expand and normalize the polynomial expressions, which then agree.

Establish `huc : (u : Fv F v ⊗[F] E) = ι (bs 0 * σ (bs 1) - bs 1 * σ (bs 0))`. Rewrite using `[hudef, AddSubgroupClass.coe_sub, Subring.coe_mul, Subring.coe_mul, hB, hB, hσB, hσB, map_sub, map_mul, map_mul]`. Establish `hsq : (u : Fv F v ⊗[F] E) * u = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (Algebra.discr F ⇑bs))`. Rewrite using `[huc, ← map_mul, ← pow_two, ← discr_eq hcm, ι.commutes, IsScalarTower.algebraMap_apply F (Fv F v)]`. Establish `hD : Algebra.discr F ⇑bs ≠ 0` using `Algebra.discr_not_zero_of_basis F bs`.

Establish `hw : (⟨_, scalar_mem hcar (discr_mem hI)⟩ * u : S) * u = 1`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[Subring.coe_mul, Subring.coe_mul, mul_assoc, hsq]`. Use `show algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (Algebra.discr F ⇑bs)⁻¹) * _ = 1`. Rewrite using `[← map_mul, ← map_mul, inv_mul_cancel₀ hD, map_one, map_one]`.

Establish `ht : σS ⟨_, scalar_mem hcar (half_mem hI)⟩ = ⟨_, scalar_mem hcar (half_mem hI)⟩` using `Subtype.ext (by rw [hsig]; exact sigR_scalar _ _)`. Establish `h2 : (⟨_, scalar_mem hcar (half_mem hI)⟩ : S) * 2 = 1`. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[Subring.coe_mul]`. Use `show algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 : Fv F v)⁻¹ * 2 = 1`.

Rewrite using `[← map_ofNat (algebraMap (Fv F v) (Fv F v ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ h20, map_one]`. Conclude with `⟨u, decomp σS hinv hu ht h2 hw⟩`.
-/
theorem exists_split {d : ℕ} {bs : Module.Basis (Fin d) F E} {v : HeightOneSpectrum (𝓞 F)}
    {S : Subring (Fv F v ⊗[F] E)} {σS : S →+* S} {ϖ : v.adicCompletionIntegers F}
    (hH : QuadHyp σ bs v S σS ϖ) :
    ∃ u : S, IsUnit (u - σS u) ∧ ∀ a, ∃ x y, σS x = x ∧ σS y = y ∧ a = x + y * u := by
  obtain ⟨hcm, hI, hcar, hsig, -⟩ := hH
  have hd : d = 2 := by
    have h := Module.finrank_eq_card_basis bs
    rw [hcm.2.2.1] at h
    simpa using h.symm
  subst hd
  have h20 : (2 : Fv F v) ≠ 0 := by
    have h := (algebraMap F (Fv F v)).injective.ne (two_ne_zero (α := F))
    rwa [map_ofNat, map_zero] at h
  have hinv : ∀ a, σS (σS a) = a := fun a => Subtype.ext (by rw [hsig, hsig, sigR_sigR _ hcm])
  let ι : E →ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.includeRight
  let B : Fin 2 → S := fun i => ⟨_, basis_mem hcar i⟩
  have hB : ∀ i, ((B i : S) : Fv F v ⊗[F] E) = ι (bs i) := fun i =>
    Algebra.TensorProduct.basis_apply _ _
  have hσB : ∀ i, ((σS (B i) : S) : Fv F v ⊗[F] E) = ι (σ (bs i)) := fun i => by
    rw [hsig, hB]
    rfl
  obtain ⟨u, hudef⟩ : ∃ u : S, u = B 0 * σS (B 1) - B 1 * σS (B 0) := ⟨_, rfl⟩
  have hu : σS u = -u := by
    rw [hudef, map_sub, map_mul, map_mul, hinv, hinv]
    ring
  have huc : (u : Fv F v ⊗[F] E) = ι (bs 0 * σ (bs 1) - bs 1 * σ (bs 0)) := by
    rw [hudef, AddSubgroupClass.coe_sub, Subring.coe_mul, Subring.coe_mul, hB, hB, hσB, hσB, map_sub, map_mul, map_mul]
  have hsq : (u : Fv F v ⊗[F] E) * u =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (Algebra.discr F ⇑bs)) := by
    rw [huc, ← map_mul, ← pow_two, ← discr_eq hcm, ι.commutes, IsScalarTower.algebraMap_apply F (Fv F v)]
  have hD : Algebra.discr F ⇑bs ≠ 0 := Algebra.discr_not_zero_of_basis F bs
  have hw : (⟨_, scalar_mem hcar (discr_mem hI)⟩ * u : S) * u = 1 := by
    refine Subtype.ext ?_
    rw [Subring.coe_mul, Subring.coe_mul, mul_assoc, hsq]
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (Algebra.discr F ⇑bs)⁻¹) * _ = 1
    rw [← map_mul, ← map_mul, inv_mul_cancel₀ hD, map_one, map_one]
  have ht : σS ⟨_, scalar_mem hcar (half_mem hI)⟩ = ⟨_, scalar_mem hcar (half_mem hI)⟩ :=
    Subtype.ext (by rw [hsig]; exact sigR_scalar _ _)
  have h2 : (⟨_, scalar_mem hcar (half_mem hI)⟩ : S) * 2 = 1 := by
    refine Subtype.ext ?_
    rw [Subring.coe_mul]
    show algebraMap (Fv F v) (Fv F v ⊗[F] E) (2 : Fv F v)⁻¹ * 2 = 1
    rw [← map_ofNat (algebraMap (Fv F v) (Fv F v ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ h20, map_one]
  exact ⟨u, decomp σS hinv hu ht h2 hw⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d bs v S σS ϖ hH hϖ`. Conclude with `⟨fun a ha hn => fixed_isUnit hH hϖ a ha hn, exists_split hH⟩`.
-/
theorem q4 : PositivityTheory.SiegelWeilFormula.Gunr.Q4 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hH hϖ
  exact ⟨fun a ha hn => fixed_isUnit hH hϖ a ha hn, exists_split hH⟩

end GlobalTheory.CompanionTheory.DiscriminantUnit

end
