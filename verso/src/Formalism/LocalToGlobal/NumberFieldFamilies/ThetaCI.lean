import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCW
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Set `_ : Algebra F ℂ` to `f.toAlgebra`. Set `φ : E →ₐ[F] ℂ` to `IsAlgClosed.lift`. Conclude with `⟨φ.toRingHom, RingHom.ext fun x => φ.commutes x⟩`.
-/
theorem emb_ext (f : F →+* ℂ) : ∃ φ : E →+* ℂ, φ.comp (algebraMap F E) = f := by
  let _ : Algebra F ℂ := f.toAlgebra
  let φ : E →ₐ[F] ℂ := IsAlgClosed.lift
  exact ⟨φ.toRingHom, RingHom.ext fun x => φ.commutes x⟩

/- English proof (translation)
Rewrite using `[TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, mul_one]`.
-/
theorem tmul_dec (c : Ainf F) (a b : F) (δ : E) :
    c ⊗ₜ[F] (algebraMap F E a + algebraMap F E b * δ) = (a • c) ⊗ₜ[F] (1 : E) + (b • c) ⊗ₜ[F] δ := by
  rw [TensorProduct.tmul_add, TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, mul_one]

end Gen

variable {D : D7}

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Establish `h : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`. Rewrite using `[emb_star, map_neg, h, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]`.
-/
theorem star_delta (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [emb_star, map_neg, h, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

/- English proof (translation)
The claim follows from `Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))`.
-/
theorem sqrt_d_pos (D : D7) : 0 < Real.sqrt D.host.d :=
  Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))

/- English proof (translation)
Introduce `h0`. Establish `h : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`. Rewrite `h` using `[h0, map_zero]`. Conclude with `mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 (sqrt_d_pos D).ne') h.symm`.
-/
theorem delta_ne (D : D7) : D.host.sqrtMinusD ≠ 0 := by
  intro h0
  have h : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [h0, map_zero] at h
  exact mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.2 (sqrt_d_pos D).ne') h.symm

/- English proof (translation)
Establish `hd` using `delta_ne D`. Take `⟨a, ha⟩` from `(D.sp.cm.fixed ((x + star x) / 2)).1 (by`. Rewrite using `[star_div₀, star_add, star_star, add_comm]`. Use the proof step `simp)`. Take `⟨b, hb⟩` from `(D.sp.cm.fixed ((x - star x) / (2 * D.host.sqrtMinusD))).1 (by`.

Rewrite using `[star_div₀, star_sub, star_star, star_mul', star_delta]`. Establish `: star (2 : D.host.E) = 2` using `by simp`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring)`.

Use `⟨a, b, ?_⟩` and prove the remaining obligations. Rewrite using `[ha, hb]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem decompE (x : D.host.E) : ∃ a b : D.host.F,
    x = algebraMap D.host.F D.host.E a + algebraMap D.host.F D.host.E b * D.host.sqrtMinusD := by
  have hd := delta_ne D
  obtain ⟨a, ha⟩ := (D.sp.cm.fixed ((x + star x) / 2)).1 (by
    rw [star_div₀, star_add, star_star, add_comm]; simp)
  obtain ⟨b, hb⟩ := (D.sp.cm.fixed ((x - star x) / (2 * D.host.sqrtMinusD))).1 (by
    rw [star_div₀, star_sub, star_star, star_mul', star_delta]
    have : star (2 : D.host.E) = 2 := by simp
    rw [this]
    field_simp
    ring)
  refine ⟨a, b, ?_⟩
  rw [ha, hb]
  field_simp
  ring

/- English proof (translation)
The claim follows from `D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))`.
-/
theorem tauE_inj {τ τ' : D.what₂.Tau} (h : tauE D τ = tauE D τ') : τ = τ' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

/- English proof (translation)
Take `⟨g, rfl⟩` from `(factEmb D.R D.host).1.2 φ`. Conclude with `⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 h⟩, by unfold tauE; rw [Equiv.apply_symm_apply]⟩`.
-/
theorem tauE_surj (φ : D.host.E →+* ℂ) (h : φ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)) :
    ∃ τ, tauE D τ = φ := by
  obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 φ
  exact ⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 h⟩, by unfold tauE; rw [Equiv.apply_symm_apply]⟩

/- English proof (translation)
Establish `h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`. Establish `hs : D.host.sqrtMinusD * D.host.sqrtMinusD = -(D.host.d : D.host.E)`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[map_mul, h0, map_neg, map_natCast, mul_mul_mul_comm, Complex.I_mul_I, ← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules.

Establish `h1 : φ D.host.sqrtMinusD * φ D.host.sqrtMinusD = (Complex.I * (Real.sqrt D.host.d : ℂ)) * (Complex.I * (Real.sqrt D.host.d : ℂ))`. Rewrite using `[← map_mul, hs, ← h0, ← map_mul, hs, map_neg, map_neg, map_natCast, map_natCast]`. Break down `mul_self_eq_mul_self_iff.1 h1 with h | h` into its components or cases. Take `⟨τ, e⟩` from `tauE_surj φ h`. Conclude with `⟨τ, Or.inl e⟩`.

Take `⟨τ, e⟩` from `tauE_surj (ComplexEmbedding.conjugate φ) (by`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, h, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]`. Use the proof step `ring)`. Conclude with `⟨τ, Or.inr e⟩`.
-/
theorem tauE_or (φ : D.host.E →+* ℂ) : ∃ τ, tauE D τ = φ ∨ tauE D τ = ComplexEmbedding.conjugate φ := by
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hs : D.host.sqrtMinusD * D.host.sqrtMinusD = -(D.host.d : D.host.E) := by
    apply D.host.φ₀.injective
    rw [map_mul, h0, map_neg, map_natCast, mul_mul_mul_comm, Complex.I_mul_I, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have h1 : φ D.host.sqrtMinusD * φ D.host.sqrtMinusD =
      (Complex.I * (Real.sqrt D.host.d : ℂ)) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [← map_mul, hs, ← h0, ← map_mul, hs, map_neg, map_neg, map_natCast, map_natCast]
  rcases mul_self_eq_mul_self_iff.1 h1 with h | h
  · obtain ⟨τ, e⟩ := tauE_surj φ h
    exact ⟨τ, Or.inl e⟩
  · obtain ⟨τ, e⟩ := tauE_surj (ComplexEmbedding.conjugate φ) (by
      rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring)
    exact ⟨τ, Or.inr e⟩

/- English proof (translation)
Use `D.sp.cm.totReal` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce `τ τ' h`. Establish `e : (tauE D τ).comp (algebraMap D.host.F D.host.E) = (tauE D τ').comp (algebraMap D.host.F D.host.E)`. Establish `h1` using `congrArg InfinitePlace.embedding h`.

Simplify using `only [plF] at h1`. Rewrite `h1` using `[InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal _), InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal _)]`. Then use the resulting hypothesis. Apply `tauE_inj` to reduce the goal to its premises. Use `ext1 x`. Take `⟨a, b, rfl⟩` from `decompE x`.

Establish `ea` using `DFunLike.congr_fun e a`. Establish `eb` using `DFunLike.congr_fun e b`. Simplify using `only [RingHom.comp_apply] at ea eb`. Rewrite using `[map_add, map_add, map_mul, map_mul, ea, eb, tauE_sqrtMinusD, tauE_sqrtMinusD]`. Introduce `w`.

Take `⟨φ, hφ⟩` from `emb_ext (E := D.host.E) w.embedding`. Take `⟨τ, h | h⟩` from `tauE_or φ`. Conclude with `⟨τ, by show plF _ = w; unfold plF; rw [h, hφ, InfinitePlace.mk_embedding]⟩`. Use `⟨τ, ?_⟩ show plF _ = w` and prove the remaining obligations. Unfold `plF`.

Establish `: (ComplexEmbedding.conjugate φ).comp (algebraMap D.host.F D.host.E) = ComplexEmbedding.conjugate w.embedding` using `by rw [← hφ]; rfl`. Rewrite using `[h, this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]`.
-/
theorem plF_bij (D : D7) : Function.Bijective fun τ : D.what₂.Tau => plF (F := D.host.F) (tauE D τ) := by
  have := D.sp.cm.totReal
  constructor
  · intro τ τ' h
    have e : (tauE D τ).comp (algebraMap D.host.F D.host.E) = (tauE D τ').comp (algebraMap D.host.F D.host.E) := by
      have h1 := congrArg InfinitePlace.embedding h
      simp only [plF] at h1
      rwa [InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal _),
        InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal _)] at h1
    apply tauE_inj
    ext1 x
    obtain ⟨a, b, rfl⟩ := decompE x
    have ea := DFunLike.congr_fun e a
    have eb := DFunLike.congr_fun e b
    simp only [RingHom.comp_apply] at ea eb
    rw [map_add, map_add, map_mul, map_mul, ea, eb, tauE_sqrtMinusD, tauE_sqrtMinusD]
  · intro w
    obtain ⟨φ, hφ⟩ := emb_ext (E := D.host.E) w.embedding
    obtain ⟨τ, h | h⟩ := tauE_or φ
    · exact ⟨τ, by show plF _ = w; unfold plF; rw [h, hφ, InfinitePlace.mk_embedding]⟩
    · refine ⟨τ, ?_⟩
      show plF _ = w
      unfold plF
      have : (ComplexEmbedding.conjugate φ).comp (algebraMap D.host.F D.host.E) =
          ComplexEmbedding.conjugate w.embedding := by rw [← hφ]; rfl
      rw [h, this, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem theta_tensor_apply (τ : D.what₂.Tau) (a : Ainf D.host.F) (x : D.host.E) :
    th0 D τ (a ⊗ₜ[D.host.F] x) = compF (F := D.host.F) (tauE D τ) a * tauE D τ x := rfl

/- English proof (translation)
The claim follows from `(InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply _ _).symm`.
-/
theorem compF_real (τ : D.what₂.Tau) (a : Ainf D.host.F) :
    compF (F := D.host.F) (tauE D τ) a = ((InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (haveI := D.sp.cm.totReal; IsTotallyReal.isReal (plF (F := D.host.F) (tauE D τ))) (a _) : ℝ) : ℂ) :=
  (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply _ _).symm

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul c x`. Take `⟨a, b, rfl⟩` from `decompE x`. Conclude with `⟨a • c, b • c, tmul_dec c a b _⟩`.

Consider the case `add x y hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨a', b', rfl⟩` from `hy`. Conclude with `⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul, add_add_add_comm]⟩`.
-/
theorem decompInf (y : Ainf D.host.F ⊗[D.host.F] D.host.E) :
    ∃ a b : Ainf D.host.F, y = a ⊗ₜ[D.host.F] 1 + b ⊗ₜ[D.host.F] D.host.sqrtMinusD := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c x =>
    obtain ⟨a, b, rfl⟩ := decompE x
    exact ⟨a • c, b • c, tmul_dec c a b _⟩
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [TensorProduct.add_tmul, TensorProduct.add_tmul, add_add_add_comm]⟩

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `decompInf y`. Establish `key : ∀ w, a w = 0 ∧ b w = 0`. Introduce `w`. Take `⟨τ, rfl⟩` from `(plF_bij D).2 w`. Establish `e` using `h τ`.

Rewrite `e` using `[map_add, theta_tensor_apply, theta_tensor_apply, map_one, mul_one, tauE_sqrtMinusD, compF_real, compF_real]`. Establish `e1` using `congrArg Complex.re e`. Establish `e2` using `congrArg Complex.im e`. Simplify using `only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, sub_zero, add_zero, zero_add, Complex.zero_re, Complex.zero_im, sub_self] at e1 e2`. Conclude with `⟨(map_eq_zero _).1 e1, (map_eq_zero _).1 ((mul_eq_zero.1 e2).resolve_right (sqrt_d_pos D).ne')⟩`.

Establish `ha : a = 0` using `funext fun w => (key w).1`. Establish `hb : b = 0` using `funext fun w => (key w).2`. Rewrite using `[ha, hb]`. Simplify using the standard rewrite rules.
-/
theorem inf_inj {y : Ainf D.host.F ⊗[D.host.F] D.host.E} (h : ∀ τ, th0 D τ y = 0) : y = 0 := by
  obtain ⟨a, b, rfl⟩ := decompInf y
  have key : ∀ w, a w = 0 ∧ b w = 0 := by
    intro w
    obtain ⟨τ, rfl⟩ := (plF_bij D).2 w
    have e := h τ
    rw [map_add, theta_tensor_apply, theta_tensor_apply, map_one, mul_one, tauE_sqrtMinusD, compF_real, compF_real] at e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, sub_zero, add_zero, zero_add, Complex.zero_re,
      Complex.zero_im, sub_self] at e1 e2
    exact ⟨(map_eq_zero _).1 e1, (map_eq_zero _).1 ((mul_eq_zero.1 e2).resolve_right (sqrt_d_pos D).ne')⟩
  have ha : a = 0 := funext fun w => (key w).1
  have hb : b = 0 := funext fun w => (key w).2
  rw [ha, hb]
  simp

/- English proof (translation)
Use `D.sp.cm.totReal` as an intermediate fact. Set `e` to `Equiv.ofBijective _ (plF_bij D)`. Use `choose s hs using fun w : InfinitePlace D.host.F => InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (r (e.symm w))`. Use `⟨s, fun τ => ?_⟩` and prove the remaining obligations. Use `(compF_real τ s).trans ?_` and prove the remaining obligations.

Rewrite using `[hs]`. Conclude with `congrArg (fun t => ((r t : ℝ) : ℂ)) (e.symm_apply_apply τ)`.
-/
theorem real_surj (r : D.what₂.Tau → ℝ) : ∃ a : Ainf D.host.F, ∀ τ, compF (F := D.host.F) (tauE D τ) a = r τ := by
  have := D.sp.cm.totReal
  let e := Equiv.ofBijective _ (plF_bij D)
  choose s hs using fun w : InfinitePlace D.host.F =>
    InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal (IsTotallyReal.isReal w) (r (e.symm w))
  refine ⟨s, fun τ => ?_⟩
  refine (compF_real τ s).trans ?_
  rw [hs]
  exact congrArg (fun t => ((r t : ℝ) : ℂ)) (e.symm_apply_apply τ)

/- English proof (translation)
Take `⟨a, ha⟩` from `real_surj fun τ => (z τ).re`. Take `⟨b, hb⟩` from `real_surj fun τ => (z τ).im / Real.sqrt D.host.d`. Use `⟨a ⊗ₜ[D.host.F] 1 + b ⊗ₜ[D.host.F] D.host.sqrtMinusD, fun τ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, theta_tensor_apply, theta_tensor_apply, map_one, mul_one, tauE_sqrtMinusD, ha, hb]`. Establish `h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 (sqrt_d_pos D).ne'`.

Use `conv_rhs => rw [← Complex.re_add_im (z τ)]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem inf_surj (z : D.what₂.Tau → ℂ) : ∃ y : Ainf D.host.F ⊗[D.host.F] D.host.E, ∀ τ, th0 D τ y = z τ := by
  obtain ⟨a, ha⟩ := real_surj fun τ => (z τ).re
  obtain ⟨b, hb⟩ := real_surj fun τ => (z τ).im / Real.sqrt D.host.d
  refine ⟨a ⊗ₜ[D.host.F] 1 + b ⊗ₜ[D.host.F] D.host.sqrtMinusD, fun τ => ?_⟩
  rw [map_add, theta_tensor_apply, theta_tensor_apply, map_one, mul_one, tauE_sqrtMinusD, ha, hb]
  have h2 : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (sqrt_d_pos D).ne'
  conv_rhs => rw [← Complex.re_add_im (z τ)]
  push_cast
  field_simp

variable (D) in

def cmpAt (τ : D.what₂.Tau) : AE D →+* ℂ := (th0 D τ).comp (infPart D)

/- English proof (translation)
Use `ae_ext (sub_eq_zero.1 (inf_inj fun τ => ?_)) h2` and prove the remaining obligations. Rewrite using `[RingHom.map_sub, sub_eq_zero]`. Conclude with `h1 τ`.
-/
theorem ae_ext' {x y : AE D} (h1 : ∀ τ, cmpAt D τ x = cmpAt D τ y) (h2 : finPart D x = finPart D y) : x = y := by
  refine ae_ext (sub_eq_zero.1 (inf_inj fun τ => ?_)) h2
  rw [RingHom.map_sub, sub_eq_zero]
  exact h1 τ

def mkAE (z : D.what₂.Tau → ℂ) (b : Af D.host.F ⊗[D.host.F] D.host.E) : AE D := pairE (inf_surj z).choose b

/- English proof (translation)
Establish `e : infPart D (mkAE z b) = (inf_surj z).choose` using `fst_pairE _ _`. Use `show th0 D τ (infPart D (mkAE z b)) = _`. Rewrite using `[e]`. Conclude with `(inf_surj z).choose_spec τ`.
-/
theorem cmpAt_mkAE (z : D.what₂.Tau → ℂ) (b : Af D.host.F ⊗[D.host.F] D.host.E) (τ : D.what₂.Tau) :
    cmpAt D τ (mkAE z b) = z τ := by
  have e : infPart D (mkAE z b) = (inf_surj z).choose := fst_pairE _ _
  show th0 D τ (infPart D (mkAE z b)) = _
  rw [e]
  exact (inf_surj z).choose_spec τ

/- English proof (translation)
The claim follows from `snd_pairE _ _`.
-/
theorem finPart_mkAE (z : D.what₂.Tau → ℂ) (b : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (mkAE z b) = b :=
  snd_pairE _ _

def mkU (z : D.what₂.Tau → ℂ) (hz : ∀ τ, z τ ≠ 0) : (AE D)ˣ :=
  Units.mkOfMulEqOne (mkAE z 1) (mkAE (fun τ => (z τ)⁻¹) 1) (ae_ext' (fun τ => by
    rw [RingHom.map_mul, cmpAt_mkAE, cmpAt_mkAE, RingHom.map_one, mul_inv_cancel₀ (hz τ)]) (by
    rw [RingHom.map_mul, finPart_mkAE, finPart_mkAE, RingHom.map_one, mul_one]))

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => show th0 D τ (fstA D.host.F a ⊗ₜ[D.host.F] star e) = starRingEnd ℂ (th0 D τ (fstA D.host.F a ⊗ₜ[D.host.F] e))`. Rewrite using `[theta_tensor_apply, theta_tensor_apply, emb_star, map_mul, compF_real, Complex.conj_ofReal]`. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add, RingHom.map_add]`.
-/
theorem cmpAt_cA (τ : D.what₂.Tau) (x : AE D) : cmpAt D τ (cA D x) = starRingEnd ℂ (cmpAt D τ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    show th0 D τ (fstA D.host.F a ⊗ₜ[D.host.F] star e) = starRingEnd ℂ (th0 D τ (fstA D.host.F a ⊗ₜ[D.host.F] e))
    rw [theta_tensor_apply, theta_tensor_apply, emb_star, map_mul, compF_real, Complex.conj_ofReal]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add, RingHom.map_add]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => rfl`. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add, RingHom.map_add]`.
-/
theorem finPart_cA (x : AE D) : finPart D (cA D x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy, RingHom.map_add, RingHom.map_add]

/- English proof (translation)
The claim follows from `(theta_infinite_family D τ).1 x`.
-/
theorem cmpAt_incA (τ : D.what₂.Tau) (x : D.host.E) : cmpAt D τ (incA D x) = tauE D τ x := (theta_infinite_family D τ).1 x

/- English proof (translation)
Introduce and unpack `χ τ a b ⟨n, hn, e⟩ ⟨m, hm, e'⟩`. Assume the negation of the conclusion as `hab`. Establish `hk : n - m ≠ 0`. Introduce `h`. Apply `hab` to reduce the goal to its premises.

Establish `: (n : ℚ) = m` using `by exact_mod_cast sub_eq_zero.1 h`. Combine the linear equalities and inequalities to obtain the conclusion. Set `u : ℂ` to `Complex.exp (((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)`. Establish `hu : u ≠ 0` using `Complex.exp_ne_zero _`. Establish `hn1 : ‖u‖ = 1` using `Complex.norm_exp_ofReal_mul_I _`.

Set `x` to `mkU (D := D) (fun τ' => if τ' = τ then u else 1) (fun τ' => by split_ifs; exacts [hu, one_ne_zero])`. Establish `h1 : finPart D (x : AE D) = 1` using `finPart_mkAE _ _`. Establish `h2 : ∀ τ', τ' ≠ τ → th0 D τ' (infPart D (x : AE D)) = 1` using `fun τ' h => (cmpAt_mkAE _ _ τ').trans (if_neg h)`. Establish `h3 : th0 D τ (infPart D (x : AE D)) = u` using `(cmpAt_mkAE _ _ τ).trans (if_pos rfl)`. Establish `a1` using `allSome_fam.1 e x h1 h2`.

Establish `a2` using `allSome_fam.1 e' x h1 h2`. Rewrite `a2` using `[a1, h3, hn1, Complex.ofReal_one, div_one]`. Establish `a3 : u ^ (n - m) = 1` using `by rw [zpow_sub₀ hu, a2, div_self (zpow_ne_zero _ hu)]`. Establish `a4 : u ^ (n - m) = -1`. Rewrite using `[← Complex.exp_int_mul, ← Complex.exp_pi_mul_I]`.

Use `congr 1`. Establish `: ((n - m : ℤ) : ℂ) ≠ 0` using `Int.cast_ne_zero.2 hk`. Rewrite using `[Complex.ofReal_div, Complex.ofReal_intCast]`. Clear the denominators using the available nonvanishing facts. Rewrite `a4` using `[a3]`.

Evaluate the numerical expressions using `at a4`.
-/
theorem expU (D : D7) : ExpU D := by
  classical
  rintro χ τ a b ⟨n, hn, e⟩ ⟨m, hm, e'⟩
  by_contra hab
  have hk : n - m ≠ 0 := by
    intro h
    apply hab
    have : (n : ℚ) = m := by exact_mod_cast sub_eq_zero.1 h
    linarith
  let u : ℂ := Complex.exp (((Real.pi / ((n - m : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I)
  have hu : u ≠ 0 := Complex.exp_ne_zero _
  have hn1 : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  let x := mkU (D := D) (fun τ' => if τ' = τ then u else 1) (fun τ' => by split_ifs; exacts [hu, one_ne_zero])
  have h1 : finPart D (x : AE D) = 1 := finPart_mkAE _ _
  have h2 : ∀ τ', τ' ≠ τ → th0 D τ' (infPart D (x : AE D)) = 1 := fun τ' h => (cmpAt_mkAE _ _ τ').trans (if_neg h)
  have h3 : th0 D τ (infPart D (x : AE D)) = u := (cmpAt_mkAE _ _ τ).trans (if_pos rfl)
  have a1 := allSome_fam.1 e x h1 h2
  have a2 := allSome_fam.1 e' x h1 h2
  rw [a1, h3, hn1, Complex.ofReal_one, div_one] at a2
  have a3 : u ^ (n - m) = 1 := by rw [zpow_sub₀ hu, a2, div_self (zpow_ne_zero _ hu)]
  have a4 : u ^ (n - m) = -1 := by
    rw [← Complex.exp_int_mul, ← Complex.exp_pi_mul_I]
    congr 1
    have : ((n - m : ℤ) : ℂ) ≠ 0 := Int.cast_ne_zero.2 hk
    rw [Complex.ofReal_div, Complex.ofReal_intCast]
    field_simp
  rw [a3] at a4
  norm_num at a4

/- English proof (translation)
Use extensionality with `i j`. Conclude with `ae_ext' (fun τ => congrFun (congrFun (h1 τ) i) j) (congrFun (congrFun h2 i) j)`.
-/
theorem mat_ext {m n : ℕ} {M N : Matrix (Fin m) (Fin n) (AE D)} (h1 : ∀ τ, M.map (cmpAt D τ) = N.map (cmpAt D τ))
    (h2 : M.map (finPart D) = N.map (finPart D)) : M = N := by
  ext i j
  exact ae_ext' (fun τ => congrFun (congrFun (h1 τ) i) j) (congrFun (congrFun h2 i) j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infMat_eq (V : HSp D) (τ : D.what₂.Tau) (h : GA D V) :
    infMat D.sp.cm.sig V.gram (th0 D τ) h = (mt V h).map (cmpAt D τ) := rfl

/- English proof (translation)
Introduce `V τ g hg`. Establish `hg' : gᴴ * gramAt D V τ * g = gramAt D V τ` using `hg`. Set `z : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ` to `fun τ' => if τ' = τ then g else 1`. Establish `hz : ∀ τ', (z τ')ᴴ * gramAt D V τ' * z τ' = gramAt D V τ'` using `fun τ' => by`. Distinguish the cases in `h : τ' = τ`.

Substitute `h` using the available equality. Simplify `hg'` using `[z]`. Simplify using `[z, h]`. Set `M : Matrix (Fin V.rank) (Fin V.rank) (AE D)` to `fun i j => mkAE (fun τ' => z τ' i j) ((1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j)`. Establish `m1 : ∀ τ', M.map (cmpAt D τ') = z τ'` using `fun τ' => by ext i j; exact cmpAt_mkAE _ _ τ'`.

Establish `m2 : M.map (finPart D) = 1` using `by ext i j; exact finPart_mkAE _ _`. Establish `rel : (M.map (cA D))ᵀ * V.gram.map (incA D) * M = V.gram.map (incA D)`. Use `mat_ext (fun τ' => ?_) ?_` and prove the remaining obligations. Establish `a : ((M.map (cA D))ᵀ).map (cmpAt D τ') = (z τ')ᴴ`. Rewrite using `[← m1]`.

Use extensionality with `i j`. Conclude with `cmpAt_cA τ' _`. Establish `b : (V.gram.map (incA D)).map (cmpAt D τ') = gramAt D V τ'` using `by ext i j; exact cmpAt_incA τ' _`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, a, b, m1, hz]`. Establish `a : ((M.map (cA D))ᵀ).map (finPart D) = 1`.

Establish `: ((M.map (cA D))ᵀ).map (finPart D) = ((M.map (finPart D)).map (sigR (Af D.host.F) D.sp.cm.sig))ᵀ`. Use extensionality with `i j`. Conclude with `finPart_cA _`. Rewrite using `[this, m2, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.transpose_one]`. Rewrite using `[Matrix.map_mul, Matrix.map_mul, a, m2, Matrix.one_mul, Matrix.mul_one]`.

Establish `hM : IsUnit M`. Rewrite using `[Matrix.isUnit_iff_isUnit_det]`. Establish `e` using `congrArg Matrix.det rel`. Rewrite `e` using `[Matrix.det_mul]`. Establish `hJ : IsUnit (V.gram.map (incA D)).det`.

Establish `e2 : (V.gram.map (incA D)).det = incA D V.gram.det` using `((incA D).map_det V.gram).symm`. Rewrite using `[e2]`. Conclude with `(gram_det_ne V).isUnit.map _`. Conclude with `isUnit_of_mul_isUnit_right (e ▸ hJ)`. Set `h : GA D V` to `(⟨hM.unit, rel⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)`.

Establish `hh : IsAtTau (th0 D) V τ g h` using `⟨Units.ext m2, (m1 τ).trans (if_pos rfl), fun τ' e => (m1 τ').trans (if_neg e)⟩`. Use `⟨h, hh, fun h' hh' => ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `mat_ext (M := mt V h') (N := mt V h) (fun τ' => ?_) ?_` and prove the remaining obligations.

Rewrite using `[← infMat_eq, ← infMat_eq]`. Distinguish the cases in `e : τ' = τ`. Rewrite using `[e, hh.2.1, hh'.2.1]`. Rewrite using `[hh.2.2 τ' e, hh'.2.2 τ' e]`. Establish `a : finHom V h' = 1` using `hh'.1`.

Conclude with `(congrArg Units.val a).trans m2.symm`.
-/
theorem atTauU (D : D7) : AtTauU D := by
  classical
  intro V τ g hg
  have hg' : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
  let z : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ' => if τ' = τ then g else 1
  have hz : ∀ τ', (z τ')ᴴ * gramAt D V τ' * z τ' = gramAt D V τ' := fun τ' => by
    by_cases h : τ' = τ
    · subst h; simpa [z] using hg'
    · simp [z, h]
  let M : Matrix (Fin V.rank) (Fin V.rank) (AE D) := fun i j =>
    mkAE (fun τ' => z τ' i j) ((1 : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j)
  have m1 : ∀ τ', M.map (cmpAt D τ') = z τ' := fun τ' => by ext i j; exact cmpAt_mkAE _ _ τ'
  have m2 : M.map (finPart D) = 1 := by ext i j; exact finPart_mkAE _ _
  have rel : (M.map (cA D))ᵀ * V.gram.map (incA D) * M = V.gram.map (incA D) := by
    refine mat_ext (fun τ' => ?_) ?_
    · have a : ((M.map (cA D))ᵀ).map (cmpAt D τ') = (z τ')ᴴ := by
        rw [← m1]; ext i j; exact cmpAt_cA τ' _
      have b : (V.gram.map (incA D)).map (cmpAt D τ') = gramAt D V τ' := by ext i j; exact cmpAt_incA τ' _
      rw [Matrix.map_mul, Matrix.map_mul, a, b, m1, hz]
    · have a : ((M.map (cA D))ᵀ).map (finPart D) = 1 := by
        have : ((M.map (cA D))ᵀ).map (finPart D) = ((M.map (finPart D)).map (sigR (Af D.host.F) D.sp.cm.sig))ᵀ := by
          ext i j; exact finPart_cA _
        rw [this, m2, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _), Matrix.transpose_one]
      rw [Matrix.map_mul, Matrix.map_mul, a, m2, Matrix.one_mul, Matrix.mul_one]
  have hM : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have e := congrArg Matrix.det rel
    rw [Matrix.det_mul] at e
    have hJ : IsUnit (V.gram.map (incA D)).det := by
      have e2 : (V.gram.map (incA D)).det = incA D V.gram.det := ((incA D).map_det V.gram).symm
      rw [e2]
      exact (gram_det_ne V).isUnit.map _
    exact isUnit_of_mul_isUnit_right (e ▸ hJ)
  let h : GA D V := (⟨hM.unit, rel⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram)
  have hh : IsAtTau (th0 D) V τ g h :=
    ⟨Units.ext m2, (m1 τ).trans (if_pos rfl), fun τ' e => (m1 τ').trans (if_neg e)⟩
  refine ⟨h, hh, fun h' hh' => ?_⟩
  apply Subtype.ext
  apply Units.ext
  refine mat_ext (M := mt V h') (N := mt V h) (fun τ' => ?_) ?_
  · rw [← infMat_eq, ← infMat_eq]
    by_cases e : τ' = τ
    · rw [e, hh.2.1, hh'.2.1]
    · rw [hh.2.2 τ' e, hh'.2.2 τ' e]
  · have a : finHom V h' = 1 := hh'.1
    exact (congrArg Units.val a).trans m2.symm

end Formalism.L2.Fam.ThC

end
