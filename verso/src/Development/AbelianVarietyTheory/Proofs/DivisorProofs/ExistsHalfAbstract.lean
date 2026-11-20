import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartFPlaceIdem
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory

noncomputable section

namespace GlobalTheory.SplitDetCharF

section Local

variable (F : Type) [Field F] [NumberField F]

/- English proof (translation)
Establish `h : y * y ∈ v.adicCompletionIntegers F`. Rewrite using `[hy]`. Conclude with `HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v d`. Break down `ValuationSubring.mem_or_inv_mem (v.adicCompletionIntegers F) y with h1 | h1` into its components or cases. Conclude with `h1`.

Distinguish the cases in `h0 : y = 0`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Use `mul_mem h h1` as an intermediate fact. Rewrite `this` using `[mul_assoc, mul_inv_cancel₀ h0, mul_one]`. Then use the resulting hypothesis.
-/
theorem sqrt_mem_of_int (d : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v)
    (hy : y * y = algebraMap F (Fv F v) (d : F)) : y ∈ v.adicCompletionIntegers F := by
  have h : y * y ∈ v.adicCompletionIntegers F := by
    rw [hy]; exact HeightOneSpectrum.coe_algebraMap_mem (𝓞 F) F v d
  rcases ValuationSubring.mem_or_inv_mem (v.adicCompletionIntegers F) y with h1 | h1
  · exact h1
  · by_cases h0 : y = 0
    · rw [h0]; exact zero_mem _
    · have := mul_mem h h1
      rwa [mul_assoc, mul_inv_cancel₀ h0, mul_one] at this

/- English proof (translation)
Use `⟨⟨fun v => if h : ∃ y : Fv F v, y * y = algebraMap F (Fv F v) (d : F) then h.choose else 0, Filter.Eventually.of_forall fun v => ?_⟩, ⟨fun v => if ∃ y : Fv F v, y * y = algebraMap F (Fv F v) (d : F) then 1 else 0, Filter.Eventually.of_forall fun v => ?_⟩, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : ∃ y : Fv F v, y * y = algebraMap F (Fv F v) (d : F)`. Simplify using `only [h, dif_pos]`. Conclude with `sqrt_mem_of_int F d v _ h.choose_spec`. Simplify using `only [h, dif_neg, not_false_iff]`.

Conclude with `zero_mem _`. Distinguish the cases in `h : ∃ y : Fv F v, y * y = algebraMap F (Fv F v) (d : F)`. Simplify using `only [h, if_true]`. Conclude with `one_mem _`. Simplify using `only [h, if_false]`.

Conclude with `zero_mem _`. Distinguish the cases in `h : ∃ y : Fv F v, y * y = algebraMap F (Fv F v) (d : F)`. Use `left`. Use `⟨if_pos h, ?_⟩` and prove the remaining obligations. Establish `e : ∀ x : Fv F v, x = h.choose → x * x = algebraMap F (Fv F v) (d : F)` using `fun x hx => hx ▸ h.choose_spec`.

Conclude with `e _ (dif_pos h)`. Use `right`. Conclude with `⟨if_neg h, dif_neg h, fun y hy => h ⟨y, hy⟩⟩`.
-/
theorem exists_sqrt_adele (d : 𝓞 F) : ∃ s ι : Af F, ∀ v,
    (evalV F v ι = 1 ∧ evalV F v s * evalV F v s = algebraMap F (Fv F v) (d : F)) ∨
    (evalV F v ι = 0 ∧ evalV F v s = 0 ∧ ∀ y : Fv F v, y * y ≠ algebraMap F (Fv F v) (d : F)) := by
  classical
  refine ⟨⟨fun v => if h : ∃ y : Fv F v, y * y = algebraMap F (Fv F v) (d : F) then h.choose else 0,
      Filter.Eventually.of_forall fun v => ?_⟩,
    ⟨fun v => if ∃ y : Fv F v, y * y = algebraMap F (Fv F v) (d : F) then 1 else 0,
      Filter.Eventually.of_forall fun v => ?_⟩, fun v => ?_⟩
  · by_cases h : ∃ y : Fv F v, y * y = algebraMap F (Fv F v) (d : F)
    · simp only [h, dif_pos]; exact sqrt_mem_of_int F d v _ h.choose_spec
    · simp only [h, dif_neg, not_false_iff]; exact zero_mem _
  · by_cases h : ∃ y : Fv F v, y * y = algebraMap F (Fv F v) (d : F)
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _
  · by_cases h : ∃ y : Fv F v, y * y = algebraMap F (Fv F v) (d : F)
    · left
      refine ⟨if_pos h, ?_⟩
      have e : ∀ x : Fv F v, x = h.choose → x * x = algebraMap F (Fv F v) (d : F) := fun x hx => hx ▸ h.choose_spec
      exact e _ (dif_pos h)
    · right
      exact ⟨if_neg h, dif_neg h, fun y hy => h ⟨y, hy⟩⟩

/- English proof (translation)
The claim follows from `Subtype.ext (funext fun v => h v)`.
-/
theorem af_ext' {x y : Af F} (h : ∀ v, evalV F v x = evalV F v y) : x = y :=
  Subtype.ext (funext fun v => h v)

/- English proof (translation)
The claim follows from `Prod.ext (mul_zero _) rfl`.
-/
theorem pair_mul (α β : Af F) : pairA F 0 α * pairA F 0 β = pairA F 0 (α * β) :=
  Prod.ext (mul_zero _) rfl

/- English proof (translation)
The claim follows from `Prod.ext (zero_mul _) rfl`.
-/
theorem pair_mul' (α : Af F) (b : AF F) : pairA F 0 α * b = pairA F 0 (α * sndA F b) :=
  Prod.ext (zero_mul _) rfl

/- English proof (translation)
The claim follows from `Prod.ext neg_zero rfl`.
-/
theorem pair_neg (α : Af F) : -pairA F 0 α = pairA F 0 (-α) :=
  Prod.ext neg_zero rfl

/- English proof (translation)
Use `af_ext' F fun w => ?_` and prove the remaining obligations. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[map_mul, map_mul, h]`. Rewrite using `[map_mul, map_mul, h0 w hw, zero_mul, zero_mul]`.
-/
theorem place_ext {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (h0 : ∀ v', v' ≠ v → evalV F v' α = 0)
    {x y : Af F} (h : evalV F v x = evalV F v y) : α * x = α * y := by
  refine af_ext' F fun w => ?_
  by_cases hw : w = v
  · subst hw; rw [map_mul, map_mul, h]
  · rw [map_mul, map_mul, h0 w hw, zero_mul, zero_mul]

/- English proof (translation)
Rewrite using `[AlgHom.commutes, AlgHom.commutes]`.
-/
theorem evalV_snd_algebraMap (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    evalV F v (sndA F (algebraMap F (AF F) x)) = algebraMap F (Fv F v) x := by
  rw [AlgHom.commutes, AlgHom.commutes]

end Local

section Field

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Apply `w.embedding.injective` to reduce the goal to its premises. Rewrite using `[h.2.2.2, h.2.2.2, star_star]`.
-/
theorem sig_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  apply w.embedding.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Take `⟨w⟩ : Nonempty (InfinitePlace E)` from `inferInstance`. Establish `hw : w.IsComplex` using `h.2.1.isComplex w`. Rewrite `hw` using `[InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff]`.

Apply `hw` to reduce the goal to its premises. Use extensionality with `x`. Use `h.2.2.2 w.embedding x` as an intermediate fact. Rewrite `this` using `[hc]`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`.

Conclude with `this.symm`.
-/
theorem sig_ne {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : ∃ x, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hw : w.IsComplex := h.2.1.isComplex w
  rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hw
  apply hw
  ext x
  have := h.2.2.2 w.embedding x
  rw [hc] at this
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact this.symm

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul a x`. Take `⟨u, w, rfl⟩` from `h x`. Use `⟨u • a, w • a, ?_⟩` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_add, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]`. Simplify using the standard rewrite rules. Consider the case `add x y hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨a', b', rfl⟩` from `hy`.

Conclude with `⟨a + a', b + b', by rw [map_add, map_add]; ring⟩`.
-/
theorem tensor_decomp {A : Type} [CommRing A] [Algebra F A] (δ : E)
    (h : ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • δ) (z : A ⊗[F] E) :
    ∃ a b : A, z = algebraMap A (A ⊗[F] E) a + algebraMap A (A ⊗[F] E) b * ((1 : A) ⊗ₜ[F] δ) := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    obtain ⟨u, w, rfl⟩ := h x
    refine ⟨u • a, w • a, ?_⟩
    rw [TensorProduct.tmul_add, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.tmul_mul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul]
    simp
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨a', b', rfl⟩ := hy
    exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := A) (B := E) (algebraMap F E).injective`.
-/
theorem tensor_inj {A : Type} [CommRing A] [Algebra F A] : Function.Injective (algebraMap A (A ⊗[F] E)) :=
  Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := A) (B := E) (algebraMap F E).injective

/- English proof (translation)
Take `⟨δ0, b, hsq, hb0, hb1, hbb⟩` from `GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 (sig_invol h) (sig_ne h)`. Take `⟨x, y, hy, hxy⟩` from `IsFractionRing.div_surjective (A := 𝓞 F) δ0`. Establish `hy0 : (y : F) ≠ 0`. Introduce `h0`. Conclude with `nonZeroDivisors.coe_ne_zero ⟨y, hy⟩ (by exact_mod_cast h0)`.

Establish `hδ0 : δ0 ≠ 0`. Introduce and unpack `rfl`. Conclude with `hsq ⟨0, by simp⟩`. Establish `hx : ((x : 𝓞 F) : F) = δ0 * ((y : 𝓞 F) : F)`. Rewrite using `[← hxy]`.

Conclude with `(div_mul_cancel₀ _ hy0).symm`. Establish `hd : ((x * y : 𝓞 F) : F) = δ0 * (y : F) * (y : F)` using `by show (x : F) * (y : F) = _`. Rewrite using `[hx]`. Establish `hyE : algebraMap F E (y : F) ≠ 0` using `(map_ne_zero _).2 hy0`. Use `⟨algebraMap F E (y : F) * b 1, x * y, ?_, ?_, ?_, fun z => ?_⟩` and prove the remaining obligations.

Rewrite using `[hd]`. Conclude with `mul_ne_zero (mul_ne_zero hδ0 hy0) hy0`. Rewrite using `[map_mul, AlgHom.commutes, hb1, mul_neg]`. Rewrite using `[hd]`. Establish `: b 1 * b 1 = algebraMap F E δ0` using `hbb`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨b.repr z 0, b.repr z 1 / y, ?_⟩` and prove the remaining obligations. Establish `hz` using `b.sum_repr z`. Rewrite `hz` using `[Fin.sum_univ_two, hb0]`. Rewrite `*` using `[Algebra.smul_def (b.repr z 1 / y), Algebra.smul_def (b.repr z 1), map_div₀]`.

Use `conv_lhs => rw [← hz]`. Rewrite using `[Algebra.smul_def]`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_int_basis {σ : E →ₐ[F] E} (h : IsCMExt F E σ) :
    ∃ (θ : E) (d : 𝓞 F), (d : F) ≠ 0 ∧ σ θ = -θ ∧ θ * θ = algebraMap F E (d : F) ∧
      ∀ x : E, ∃ u w : F, x = u • (1 : E) + w • θ := by
  obtain ⟨δ0, b, hsq, hb0, hb1, hbb⟩ :=
    GlobalTheory.QuadNormBase.exists_basis F E σ h.2.2.1 (sig_invol h) (sig_ne h)
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 F) δ0
  have hy0 : (y : F) ≠ 0 := by
    intro h0
    exact nonZeroDivisors.coe_ne_zero ⟨y, hy⟩ (by exact_mod_cast h0)
  have hδ0 : δ0 ≠ 0 := by
    rintro rfl
    exact hsq ⟨0, by simp⟩
  have hx : ((x : 𝓞 F) : F) = δ0 * ((y : 𝓞 F) : F) := by
    rw [← hxy]; exact (div_mul_cancel₀ _ hy0).symm
  have hd : ((x * y : 𝓞 F) : F) = δ0 * (y : F) * (y : F) := by
    show (x : F) * (y : F) = _
    rw [hx]
  have hyE : algebraMap F E (y : F) ≠ 0 := (map_ne_zero _).2 hy0
  refine ⟨algebraMap F E (y : F) * b 1, x * y, ?_, ?_, ?_, fun z => ?_⟩
  · rw [hd]
    exact mul_ne_zero (mul_ne_zero hδ0 hy0) hy0
  · rw [map_mul, AlgHom.commutes, hb1, mul_neg]
  · rw [hd]
    have : b 1 * b 1 = algebraMap F E δ0 := hbb
    calc algebraMap F E (y : F) * b 1 * (algebraMap F E (y : F) * b 1)
        = algebraMap F E (y : F) * algebraMap F E (y : F) * (b 1 * b 1) := by ring
      _ = _ := by rw [this, ← map_mul, ← map_mul]; congr 1; ring
  · refine ⟨b.repr z 0, b.repr z 1 / y, ?_⟩
    have hz := b.sum_repr z
    rw [Fin.sum_univ_two, hb0] at hz
    rw [Algebra.smul_def (b.repr z 1 / y), Algebra.smul_def (b.repr z 1), map_div₀] at *
    conv_lhs => rw [← hz]
    rw [Algebra.smul_def]
    field_simp

end Field

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨δ, -, hn⟩` from `GlobalTheory.QuadNormBase.norm_form F E σ h.2.2.1 (sig_invol h) (sig_ne h)`. Take `⟨x, y, e1, e2⟩` from `(hn (AF F)).1 z`. Rewrite using `[e1, e2]`.
-/
theorem algebraMap_norm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (z : AEF F E) :
    algebraMap (AF F) (AEF F E) (Algebra.norm (AF F) z) = z * cAF σ z := by
  obtain ⟨δ, -, hn⟩ := GlobalTheory.QuadNormBase.norm_form F E σ h.2.2.1 (sig_invol h) (sig_ne h)
  obtain ⟨x, y, e1, e2⟩ := (hn (AF F)).1 z
  rw [e1, e2]

end Adelic

section Character

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def cut {R : Type} [CommRing R] (ε : R) (h : ε * ε = ε) : R →* R where
  toFun u := (1 - ε) + ε * u
  map_one' := by ring
  map_mul' u v := by linear_combination (-(1 - u - v + u * v)) * h

/- English proof (translation)
Set `I : Ideal R` to `LinearMap.ker (LinearMap.mul R R a)`. Establish `h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1`. Use extensionality with `i j`. Conclude with `Ideal.Quotient.eq.2 (h i j)`. Establish `h2` using `congrArg Matrix.det h1`.

Rewrite `h2` using `[← RingHom.map_det, ← RingHom.map_det, Matrix.det_one]`. Conclude with `Ideal.Quotient.eq.1 h2`.
-/
theorem mul_det_sub_one {R : Type} [CommRing R] {n : ℕ} (a : R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, a * (M - 1) i j = 0) : a * (M.det - 1) = 0 := by
  let I : Ideal R := LinearMap.ker (LinearMap.mul R R a)
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 := by
    ext i j
    exact Ideal.Quotient.eq.2 (h i j)
  have h2 := congrArg Matrix.det h1
  rw [← RingHom.map_det, ← RingHom.map_det, Matrix.det_one] at h2
  exact Ideal.Quotient.eq.1 h2

/- English proof (translation)
Take the linear combination `ε * hd + (d - 1) * (a1 + a2)`.
-/
theorem cut_eq {R : Type} [CommRing R] {ε e f d : R} (a1 : ε * e = e)
    (a2 : ε * f = 0) (hd : (1 - (e + f)) * (d - 1) = 0) : (1 - ε) + ε * d = e * d + (1 - e) := by
  linear_combination ε * hd + (d - 1) * (a1 + a2)

/- English proof (translation)
Establish `e4 : ε * (d - 1) = f * (d - 1)`. Take the linear combination `ε * hd + (d - 1) * (a1 + a2)`. Take the linear combination `(1 + f * (d' - 1)) * e4 + (d - 1) * (d' - 1) * e2 + f * e3`.
-/
theorem cut_mul {R : Type} [CommRing R] {ε e f d d' : R} (e2 : f * f = f) (a1 : ε * e = 0)
    (a2 : ε * f = f) (hd : (1 - (e + f)) * (d - 1) = 0) (e3 : d * d' = 1) :
    ((1 - ε) + ε * d) * (f * d' + (1 - f)) = 1 := by
  have e4 : ε * (d - 1) = f * (d - 1) := by
    linear_combination ε * hd + (d - 1) * (a1 + a2)
  linear_combination (1 + f * (d' - 1)) * e4 + (d - 1) * (d' - 1) * e2 + f * e3

/- English proof (translation)
Establish `key : ∀ a : R ⊗[F] E, a = i.rTensor E (Algebra.TensorProduct.map p (AlgHom.id F E) a) + j.rTensor E (Algebra.TensorProduct.map q (AlgHom.id F E) a)`. Introduce `a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul m x => simp [← TensorProduct.add_tmul, h]`.

Consider the case `add a b ha hb`. Simplify using `only [map_add]`. Rewrite using `[add_add_add_comm, ← ha, ← hb]`. Rewrite using `[key a, h1, h2]`. Simplify using the standard rewrite rules.
-/
theorem tensor_prod_ext {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra F R] [Algebra F A] [Algebra F B] (p : R →ₐ[F] A) (q : R →ₐ[F] B) (i : A →ₗ[F] R) (j : B →ₗ[F] R)
    (h : ∀ x, i (p x) + j (q x) = x) (a : R ⊗[F] E)
    (h1 : Algebra.TensorProduct.map p (AlgHom.id F E) a = 0)
    (h2 : Algebra.TensorProduct.map q (AlgHom.id F E) a = 0) : a = 0 := by
  have key : ∀ a : R ⊗[F] E,
      a = i.rTensor E (Algebra.TensorProduct.map p (AlgHom.id F E) a) +
        j.rTensor E (Algebra.TensorProduct.map q (AlgHom.id F E) a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul m x => simp [← TensorProduct.add_tmul, h]
    | add a b ha hb =>
      simp only [map_add]
      rw [add_add_add_comm, ← ha, ← hb]
  rw [key a, h1, h2]; simp

/- English proof (translation)
The claim follows from `tensor_prod_ext (fstA F) (sndA F) (LinearMap.inl F (Ainf F) (Af F)) (LinearMap.inr F (Ainf F) (Af F)) (fun x => Prod.ext (add_zero x.1) (zero_add x.2)) a h1 h2`.
-/
theorem adele_tensor_ext (a : AEF F E) (h1 : infPartF F E a = 0) (h2 : finPartF F E a = 0) : a = 0 :=
  tensor_prod_ext (fstA F) (sndA F) (LinearMap.inl F (Ainf F) (Af F)) (LinearMap.inr F (Ainf F) (Af F))
    (fun x => Prod.ext (add_zero x.1) (zero_add x.2)) a h1 h2

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Establish `h : Formalism.UG.cT (sigR (AF F) σ) (mtF σ J g) * JR (F` using `F) (AF F) J * mtF σ J g = JR (F := F) (AF F) J := g.2`. Establish `hu : IsUnit (JR (F` using `F) (AF F) J).det := by`. Use `((Ne.isUnit hJ.2).map (inclR (F := F) (AF F)))` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Then use the resulting hypothesis. Establish `h2` using `congrArg Matrix.det h`.

Rewrite `h2` using `[Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Use `hu.mul_left_cancel ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(JR (F := F) (AF F) J).det * ((mtF σ J g).det * sigR (AF F) σ (mtF σ J g).det) = _`. Take the linear combination `h2`.
-/
theorem det_mul_conj (hJ : IsHermND σ J) (g : GAF σ J) :
    (mtF σ J g).det * cAF σ (mtF σ J g).det = 1 := by
  have h : Formalism.UG.cT (sigR (AF F) σ) (mtF σ J g) * JR (F := F) (AF F) J * mtF σ J g = JR (F := F) (AF F) J := g.2
  have hu : IsUnit (JR (F := F) (AF F) J).det := by
    have := ((Ne.isUnit hJ.2).map (inclR (F := F) (AF F)))
    rwa [RingHom.map_det] at this
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Formalism.UG.cT, Matrix.det_transpose, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det] at h2
  refine hu.mul_left_cancel ?_
  change (JR (F := F) (AF F) J).det * ((mtF σ J g).det * sigR (AF F) σ (mtF σ J g).det) = _
  linear_combination h2

/- English proof (translation)
Take `⟨⟨η, hη⟩, h1⟩` from `h`. Establish `e : x * x' = idFF F E (Units.map (Algebra.norm (AF F) : AEF F E →* AF F) x)`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, hx]`. Conclude with `(algebraMap_norm hc (x : AEF F E)).symm`.

Rewrite using `[← map_mul, e, h1 η hη, hη.2.2.1 x, one_pow]`.
-/
theorem char_norm (hc : IsCMExt F E σ) {χ : (AEF F E)ˣ →* Circle} {m : ℕ} (h : ResEtaF χ m) (x x' : (AEF F E)ˣ)
    (hx : (x' : AEF F E) = cAF σ x) : χ x * χ x' = 1 := by
  obtain ⟨⟨η, hη⟩, h1⟩ := h
  have e : x * x' = idFF F E (Units.map (Algebra.norm (AF F) : AEF F E →* AF F) x) := by
    refine Units.ext ?_
    rw [Units.val_mul, hx]
    exact (algebraMap_norm hc (x : AEF F E)).symm
  rw [← map_mul, e, h1 η hη, hη.2.2.1 x, one_pow]

/- English proof (translation)
Take `⟨x', hx'⟩ : IsUnit (cAF σ (x : AEF F E))` from `x.isUnit.map (cAF σ)`. Establish `hcx` using `char_norm hc h x x' hx'`. Establish `h1 : y * x' = 1` using `Units.ext (by rw [Units.val_mul, hx', hy, Units.val_one])`. Establish `h2` using `congrArg χ h1`. Rewrite `h2` using `[map_mul, map_one, ← hcx]`.

Conclude with `mul_right_cancel h2`.
-/
theorem char_eq_of_mul_conj (hc : IsCMExt F E σ) {χ : (AEF F E)ˣ →* Circle} {m : ℕ} (h : ResEtaF χ m)
    (y x : (AEF F E)ˣ) (hy : (y : AEF F E) * cAF σ x = 1) : χ y = χ x := by
  obtain ⟨x', hx'⟩ : IsUnit (cAF σ (x : AEF F E)) := x.isUnit.map (cAF σ)
  have hcx := char_norm hc h x x' hx'
  have h1 : y * x' = 1 := Units.ext (by rw [Units.val_mul, hx', hy, Units.val_one])
  have h2 := congrArg χ h1
  rw [map_mul, map_one, ← hcx] at h2
  exact mul_right_cancel h2

variable (σ J) in

def cutDet (ε : AEF F E) (h : ε * ε = ε) : GAF σ J →* (AEF F E)ˣ :=
  (Units.map (cut ε h)).comp ((Matrix.GeneralLinearGroup.det (n := Fin n) (R := AEF F E)).comp (matHomF σ J))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cutDet_val (ε : AEF F E) (h : ε * ε = ε) (g : GAF σ J) :
    (cutDet σ J ε h g : AEF F E) = (1 - ε) + ε * (mtF σ J g).det := rfl

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[cutDet_val, Units.val_one]`. Take the linear combination `mul_det_sub_one ε _ hg`.
-/
theorem cutDet_eq_one (ε : AEF F E) (h : ε * ε = ε) (g : GAF σ J)
    (hg : ∀ i j, ε * (mtF σ J g - 1) i j = 0) : cutDet σ J ε h g = 1 := by
  refine Units.ext ?_
  rw [cutDet_val, Units.val_one]
  linear_combination mul_det_sub_one ε _ hg

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) (AEF F E)`. Establish `h0 : Continuous fun g : GAF σ J => matHomF σ J g` using `continuous_subtype_val`. Establish `h1 : Continuous (mtF σ J)` using `Units.continuous_val.comp h0`. Establish `h2 : Continuous fun g : GAF σ J => mtF σ J g⁻¹`.

Establish `e : (fun g : GAF σ J => mtF σ J g⁻¹) = fun g => ((matHomF σ J g)⁻¹).1`. Use function extensionality and compare the values at `g`. Unfold `mtF`. Rewrite using `[map_inv]`. Rewrite using `[e]`.

Conclude with `Units.continuous_coe_inv.comp h0`. Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_const.add (continuous_const.mul h1.matrix_det)`. Simplify using `only [← map_inv, cutDet_val]`. Conclude with `continuous_const.add (continuous_const.mul h2.matrix_det)`.
-/
theorem continuous_cutDet (ε : AEF F E) (h : ε * ε = ε) : Continuous (cutDet σ J ε h) := by
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AEF F E) := IsModuleTopology.isTopologicalRing (AF F) (AEF F E)
  have h0 : Continuous fun g : GAF σ J => matHomF σ J g := continuous_subtype_val
  have h1 : Continuous (mtF σ J) := Units.continuous_val.comp h0
  have h2 : Continuous fun g : GAF σ J => mtF σ J g⁻¹ := by
    have e : (fun g : GAF σ J => mtF σ J g⁻¹) = fun g => ((matHomF σ J g)⁻¹).1 := by
      funext g
      unfold mtF
      rw [map_inv]
    rw [e]
    exact Units.continuous_coe_inv.comp h0
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact continuous_const.add (continuous_const.mul h1.matrix_det)
  · simp only [← map_inv, cutDet_val]
    exact continuous_const.add (continuous_const.mul h2.matrix_det)

/- English proof (translation)
Use `cutDet_eq_one ε h1 g fun i j => ?_` and prove the remaining obligations. Establish `hm : ((mtF σ J g).map (finPartF F E)) = 1` using `congrArg Units.val (show Formalism.UG.bc (finPartF F E) (matHomF σ J g) = 1 from hg)`. Establish `hf : finPartF F E ((mtF σ J g - 1) i j) = 0`. Establish `e1 : finPartF F E (mtF σ J g i j) = (1 : Matrix (Fin n) (Fin n) _) i j` using `congrFun (congrFun hm i) j`. Rewrite using `[Matrix.sub_apply, RingHom.map_sub, e1, sub_eq_zero]`.

Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]`. Rewrite using `[Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]`. Conclude with `adele_tensor_ext _ (by rw [RingHom.map_mul, h3, zero_mul]) (by rw [RingHom.map_mul, hf, mul_zero])`.
-/
theorem cutDet_real (ε : AEF F E) (h1 : ε * ε = ε) (h3 : infPartF F E ε = 0) (g : GAF σ J)
    (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ J) : cutDet σ J ε h1 g = 1 := by
  refine cutDet_eq_one ε h1 g fun i j => ?_
  have hm : ((mtF σ J g).map (finPartF F E)) = 1 :=
    congrArg Units.val (show Formalism.UG.bc (finPartF F E) (matHomF σ J g) = 1 from hg)
  have hf : finPartF F E ((mtF σ J g - 1) i j) = 0 := by
    have e1 : finPartF F E (mtF σ J g i j) = (1 : Matrix (Fin n) (Fin n) _) i j :=
      congrFun (congrFun hm i) j
    rw [Matrix.sub_apply, RingHom.map_sub, e1, sub_eq_zero]
    by_cases e : i = j
    · subst e; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne e, Matrix.one_apply_ne e, RingHom.map_zero]
  exact adele_tensor_ext _ (by rw [RingHom.map_mul, h3, zero_mul]) (by rw [RingHom.map_mul, hf, mul_zero])

/- English proof (translation)
The claim follows from `mul_det_sub_one _ _ fun i j => by rw [sub_mul, one_mul, hg i j, sub_self]`.
-/
theorem det_supp {e : AEF F E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) * ((mtF σ J g).det - 1) = 0 :=
  mul_det_sub_one _ _ fun i j => by rw [sub_mul, one_mul, hg i j, sub_self]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[cutDet_val, hx]`. Conclude with `cut_eq a1 a2 (det_supp hg)`.
-/
theorem cutDet_same (ε : AEF F E) (h1 : ε * ε = ε) {e : AEF F E} (a1 : ε * e = e) (a2 : ε * cAF σ e = 0)
    {g : GAF σ J} {x : (AEF F E)ˣ} (hg : SuppAtF σ e J g) (hx : IsDetAtF σ e J g x) : cutDet σ J ε h1 g = x := by
  refine Units.ext ?_
  rw [cutDet_val, hx]
  exact cut_eq a1 a2 (det_supp hg)

/- English proof (translation)
Establish `hx' : (x : AEF F E) = e * (mtF σ J g).det + (1 - e)` using `hx`. Establish `e2 : cAF σ e * cAF σ e = cAF σ e` using `by rw [← RingHom.map_mul, he]`. Establish `e5 : cAF σ x = cAF σ e * cAF σ (mtF σ J g).det + (1 - cAF σ e)`. Rewrite using `[hx', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]`. Rewrite using `[cutDet_val, e5]`.

Conclude with `cut_mul e2 a1 a2 (det_supp hg) (det_mul_conj hJ g)`.
-/
theorem cutDet_conj (hJ : IsHermND σ J) (ε : AEF F E) (h1 : ε * ε = ε) {e : AEF F E} (he : e * e = e)
    (a1 : ε * e = 0) (a2 : ε * cAF σ e = cAF σ e) {g : GAF σ J} {x : (AEF F E)ˣ} (hg : SuppAtF σ e J g)
    (hx : IsDetAtF σ e J g x) : (cutDet σ J ε h1 g : AEF F E) * cAF σ x = 1 := by
  have hx' : (x : AEF F E) = e * (mtF σ J g).det + (1 - e) := hx
  have e2 : cAF σ e * cAF σ e = cAF σ e := by rw [← RingHom.map_mul, he]
  have e5 : cAF σ x = cAF σ e * cAF σ (mtF σ J g).det + (1 - cAF σ e) := by
    rw [hx', RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
  rw [cutDet_val, e5]
  exact cut_mul e2 a1 a2 (det_supp hg) (det_mul_conj hJ g)

end Character

end GlobalTheory.SplitDetCharF
