import Mathlib
import Lemmata.FirstBlockLemmaH.Imports
import Lemmata.GeneralBFactThirdVariant.Imports

noncomputable section

namespace Formalism.L2.Pj.DatLin

open NumberField TensorProduct
open scoped nonZeroDivisors ComplexConjugate

variable {E : Type} [Field E] [NumberField E]

section Scalar

variable (Ψ : Finset (E →+* ℂ))

def embO : 𝓞 E →+ (Ψ → ℂ) where
  toFun e τ := (τ : E →+* ℂ) (e : E)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def phi1 : ℝ ⊗[ℤ] 𝓞 E →ₗ[ℝ] (Ψ → ℂ) := LinearMap.liftBaseChange ℝ (embO Ψ).toIntLinearMap

/- English proof (translation)
Use extensionality with `τ`. Simplify using `[phi1, LinearMap.liftBaseChange_tmul, embO, Complex.real_smul]`.
-/
theorem phi1_tmul (x : ℝ) (e : 𝓞 E) :
    phi1 Ψ (x ⊗ₜ e) = fun τ : Ψ => (x : ℂ) * (τ : E →+* ℂ) (e : E) := by
  ext τ
  simp [phi1, LinearMap.liftBaseChange_tmul, embO, Complex.real_smul]

variable {Ψ}

/- English proof (translation)
Rewrite using `[hΨ]`. Simplify using `[ComplexEmbedding.conjugate]`.
-/
theorem conj_mem_iff (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ)
    (σ : E →+* ℂ) : ComplexEmbedding.conjugate σ ∈ Ψ ↔ σ ∉ Ψ := by
  rw [hΨ]
  simp [ComplexEmbedding.conjugate]

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_third_variant.goal1 .. | (apply Bl.general_b_fact_third_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_variant.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_variant.goal1 <;> assumption) | (intros; apply @Bl.genera …`.
-/
theorem li1 (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ)
    (x : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → ℝ)
    (hx : ∀ τ ∈ Ψ, ∑ k, (x k : ℂ) * τ ((RingOfIntegers.basis E k : 𝓞 E) : E) = 0) : x = 0 := by
  first | exact Bl.general_b_fact_third_variant.goal1 .. | (apply Bl.general_b_fact_third_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_variant.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_variant.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_third_variant.goal1 <;> assumption) | (apply @Bl.general_b_fact_third_variant.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_third_variant.goal1 E ‹_› ‹_› Ψ hΨ x hx | exact @Bl.general_b_fact_third_variant.goal1 E ‹_› ‹_› Ψ hΨ x | exact @Bl.general_b_fact_third_variant.goal1 E ‹_› ‹_› Ψ hΨ | exact @Bl.general_b_fact_third_variant.goal1 E ‹_› ‹_› Ψ | exact @Bl.general_b_fact_third_variant.goal1 E ‹_› ‹_› | exact @Bl.general_b_fact_third_variant.goal1 E ‹_› | exact @Bl.general_b_fact_third_variant.goal1 E

/- English proof (translation)
Establish `h1 : Ψᶜ = Ψ.image ComplexEmbedding.conjugate`. Use extensionality with `σ`. Simplify using `only [Finset.mem_compl, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `⟨ComplexEmbedding.conjugate σ, (conj_mem_iff hΨ σ).2 h, by simp [ComplexEmbedding.conjugate]⟩`. Introduce and unpack `⟨τ, hτ, rfl⟩`. Conclude with `(hΨ τ).1 hτ`. Establish `hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ))`. Introduce `a c h`.

Simplify `congrArg star h` using `[ComplexEmbedding.conjugate]`. Establish `h2 : (Ψ.image ComplexEmbedding.conjugate).card = Ψ.card` using `Finset.card_image_of_injective _ hinj`. Establish `h3` using `Finset.card_compl Ψ`. Establish `h4` using `Embeddings.card E ℂ`. Establish `h5` using `Finset.card_le_univ Ψ`.

Rewrite `h3` using `[h1, h2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_card (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) :
    2 * Ψ.card = Module.finrank ℚ E := by
  classical
  have h1 : Ψᶜ = Ψ.image ComplexEmbedding.conjugate := by
    ext σ
    simp only [Finset.mem_compl, Finset.mem_image]
    constructor
    · intro h
      exact ⟨ComplexEmbedding.conjugate σ, (conj_mem_iff hΨ σ).2 h, by simp [ComplexEmbedding.conjugate]⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact (hΨ τ).1 hτ
  have hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) := by
    intro a c h
    simpa [ComplexEmbedding.conjugate] using congrArg star h
  have h2 : (Ψ.image ComplexEmbedding.conjugate).card = Ψ.card := Finset.card_image_of_injective _ hinj
  have h3 := Finset.card_compl Ψ
  have h4 := Embeddings.card E ℂ
  have h5 := Finset.card_le_univ Ψ
  rw [h1, h2] at h3
  omega

/- English proof (translation)
Establish `hinj : Function.Injective (phi1 Ψ)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `t ht`. Set `B` to `Algebra.TensorProduct.basis ℝ (RingOfIntegers.basis E)`. Establish `hx` using `li1 hΨ (fun k => B.repr t k) (fun τ hτ => by`.

Establish `h1` using `congrFun ht ⟨τ, hτ⟩`. Rewrite `h1` using `[← B.sum_repr t, map_sum]`. Simplify `h1)` using `[B, Algebra.TensorProduct.basis_apply, phi1_tmul, Finset.sum_apply, Complex.real_smul]`. Establish `: B.repr t = 0`. Use extensionality with `k`.

Conclude with `congrFun hx k`. Simplify using `using B.repr.injective (this.trans (map_zero _).symm)`. Use `⟨hinj, ?_⟩` and prove the remaining obligations. Rewrite using `[← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]` and apply the resulting hypothesis. Rewrite using `[Module.finrank_baseChange, RingOfIntegers.rank, Module.finrank_pi_fintype]`.

Simplify using `only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_coe]`. Rewrite using `[← two_card hΨ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phi1_bijective (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) :
    Function.Bijective (phi1 Ψ) := by
  classical
  have hinj : Function.Injective (phi1 Ψ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    let B := Algebra.TensorProduct.basis ℝ (RingOfIntegers.basis E)
    have hx := li1 hΨ (fun k => B.repr t k) (fun τ hτ => by
      have h1 := congrFun ht ⟨τ, hτ⟩
      rw [← B.sum_repr t, map_sum] at h1
      simpa [B, Algebra.TensorProduct.basis_apply, phi1_tmul, Finset.sum_apply, Complex.real_smul]
        using h1)
    have : B.repr t = 0 := by
      ext k
      exact congrFun hx k
    simpa using B.repr.injective (this.trans (map_zero _).symm)
  refine ⟨hinj, ?_⟩
  rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
  rw [Module.finrank_baseChange, RingOfIntegers.rank, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Fintype.card_coe]
  rw [← two_card hΨ]
  ring

end Scalar

section General

variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (b : Module.Basis ι E V) (Ψ : Finset (E →+* ℂ)) (M : Submodule (𝓞 E) V)

def coordO : M →+ (Ψ → ι → ℂ) where
  toFun v τ i := (τ : E →+* ℂ) (b.repr v i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def theta : ℝ ⊗[ℤ] M →ₗ[ℝ] (Ψ → ι → ℂ) :=
  LinearMap.liftBaseChange ℝ (coordO b Ψ M).toIntLinearMap

/- English proof (translation)
Use extensionality with `τ i`. Simplify using `[theta, LinearMap.liftBaseChange_tmul, coordO, Complex.real_smul]`.
-/
theorem theta_tmul (x : ℝ) (v : M) :
    theta b Ψ M (x ⊗ₜ v) = fun (τ : Ψ) i => (x : ℂ) * (τ : E →+* ℂ) (b.repr v i) := by
  ext τ i
  simp [theta, LinearMap.liftBaseChange_tmul, coordO, Complex.real_smul]

def embI : (ι → 𝓞 E) →+ (Ψ → ι → ℂ) where
  toFun n τ i := (τ : E →+* ℂ) (n i : E)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def phiI : ℝ ⊗[ℤ] (ι → 𝓞 E) →ₗ[ℝ] (Ψ → ι → ℂ) :=
  LinearMap.liftBaseChange ℝ (embI (ι := ι) Ψ).toIntLinearMap

/- English proof (translation)
Use extensionality with `τ i`. Simplify using `[phiI, LinearMap.liftBaseChange_tmul, embI, Complex.real_smul]`.
-/
theorem phiI_tmul (x : ℝ) (n : ι → 𝓞 E) :
    phiI Ψ (x ⊗ₜ n) = fun (τ : Ψ) i => (x : ℂ) * (τ : E →+* ℂ) (n i : E) := by
  ext τ i
  simp [phiI, LinearMap.liftBaseChange_tmul, embI, Complex.real_smul]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x n => simp [phiI_tmul, phi1_tmul, TensorProduct.piRightHom_tmul]`. Consider the case `add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]`.
-/
theorem phiI_eq (t : ℝ ⊗[ℤ] (ι → 𝓞 E)) (τ : Ψ) (i : ι) :
    phiI Ψ t τ i = phi1 Ψ (TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E) t i) τ := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x n => simp [phiI_tmul, phi1_tmul, TensorProduct.piRightHom_tmul]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

variable {Ψ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `t t' h`. Apply `(TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E)).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Apply `(phi1_bijective hΨ).1` to reduce the goal to its premises.

Use function extensionality and compare the values at `τ`. Rewrite using `[← phiI_eq, ← phiI_eq, h]`. Introduce `u choose y hy using fun i => (phi1_bijective hΨ).2 (fun τ => u τ i)`. Use `⟨(TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E)).symm y, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ i`.

Rewrite using `[phiI_eq, LinearEquiv.apply_symm_apply, hy]`.
-/
theorem phiI_bijective (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ) :
    Function.Bijective (phiI (ι := ι) Ψ) := by
  constructor
  · intro t t' h
    apply (TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E)).injective
    funext i
    apply (phi1_bijective hΨ).1
    funext τ
    rw [← phiI_eq, ← phiI_eq, h]
  · intro u
    choose y hy using fun i => (phi1_bijective hΨ).2 (fun τ => u τ i)
    refine ⟨(TensorProduct.piRight ℤ ℝ ℝ (fun _ : ι => 𝓞 E)).symm y, ?_⟩
    funext τ i
    rw [phiI_eq, LinearEquiv.apply_symm_apply, hy]

/- English proof (translation)
Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot]`. Conclude with `Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance`.
-/
theorem flat_real : Module.Flat ℤ ℝ := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot]
  exact Submodule.isTorsionFree_iff_torsion_eq_bot.1 inferInstance

variable {b M}

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.FirstBlockLemmaH.goal1 .. | (apply Bl.FirstBlockLemmaH.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaH.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaH.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaH.goal1 <;> assumption) | (apply @Bl.Fi …`.
-/
theorem exists_den (hfg : Module.Finite (𝓞 E) M) :
    ∃ s ∈ (𝓞 E)⁰, ∀ v ∈ M, ∀ i,
      algebraMap (𝓞 E) E s * b.repr v i ∈ (algebraMap (𝓞 E) E).range := by
  first | exact Bl.FirstBlockLemmaH.goal1 .. | (apply Bl.FirstBlockLemmaH.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaH.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaH.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaH.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaH.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι ‹_› ‹_› b M hfg | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι ‹_› ‹_› b M | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι ‹_› ‹_› b | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι ‹_› ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› ι | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› V | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E ‹_› | exact @Bl.FirstBlockLemmaH.goal1 E

variable (b M)

def kapF (s : 𝓞 E) (hs : ∀ v ∈ M, ∀ i,
      algebraMap (𝓞 E) E s * b.repr v i ∈ (algebraMap (𝓞 E) E).range) (v : M) (i : ι) : 𝓞 E :=
  (hs v v.2 i).choose

/- English proof (translation)
The claim follows from `(hs v v.2 i).choose_spec`.
-/
theorem kapF_spec (s : 𝓞 E) (hs) (v : M) (i : ι) :
    algebraMap (𝓞 E) E (kapF b M s hs v i) = algebraMap (𝓞 E) E s * b.repr v i :=
  (hs v v.2 i).choose_spec

def kap (s : 𝓞 E) (hs : ∀ v ∈ M, ∀ i,
      algebraMap (𝓞 E) E s * b.repr v i ∈ (algebraMap (𝓞 E) E).range) : M →+ (ι → 𝓞 E) where
  toFun v i := kapF b M s hs v i
  map_zero' := by
    funext i
    apply IsFractionRing.injective (𝓞 E) E
    rw [kapF_spec]
    simp
  map_add' x y := by
    funext i
    apply IsFractionRing.injective (𝓞 E) E
    simp only [Pi.add_apply, map_add]
    rw [kapF_spec, kapF_spec, kapF_spec]
    simp [mul_add]

/- English proof (translation)
The claim follows from `kapF_spec b M s hs v i`.
-/
theorem kap_spec (s : 𝓞 E) (hs) (v : M) (i : ι) :
    algebraMap (𝓞 E) E (kap b M s hs v i) = algebraMap (𝓞 E) E s * b.repr v i :=
  kapF_spec b M s hs v i

def iota1 (s' : 𝓞 E) (hs' : ∀ i, s' • b i ∈ M) : (ι → 𝓞 E) →+ M where
  toFun n := ⟨∑ i, n i • s' • b i, Submodule.sum_mem _ fun i _ => M.smul_mem _ (hs' i)⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Establish `e : ((iota1 b M s' hs' n : M) : V) = ∑ k, (algebraMap (𝓞 E) E (n k) * algebraMap (𝓞 E) E s') • b k`. Simplify using `only [iota1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, ← map_mul, algebraMap_smul]`. Rewrite using `[e, b.repr_sum_self]`.
-/
theorem iota1_repr (s' : 𝓞 E) (hs') (n : ι → 𝓞 E) (i : ι) :
    b.repr (iota1 b M s' hs' n) i = algebraMap (𝓞 E) E (n i) * algebraMap (𝓞 E) E s' := by
  have e : ((iota1 b M s' hs' n : M) : V) =
      ∑ k, (algebraMap (𝓞 E) E (n k) * algebraMap (𝓞 E) E s') • b k := by
    simp only [iota1, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, ← map_mul, algebraMap_smul]
  rw [e, b.repr_sum_self]

/- English proof (translation)
Establish `hne : ∀ s ∈ (𝓞 E)⁰, ∀ τ : Ψ, (τ : E →+* ℂ) (algebraMap (𝓞 E) E s) ≠ 0`. Introduce `s hs τ`. Rewrite using `[map_ne_zero]`. Conclude with `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs`. Prove the components needed by the constructor for the conclusion.

Take `⟨s, hs, hsI⟩` from `exists_den (b := b) hfg`. Set `κ` to `(kap b M s hsI).toIntLinearMap`. Establish `hκ : Function.Injective κ`. Introduce `v w h`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Establish `h1` using `congrArg (fun n => algebraMap (𝓞 E) E (n i)) h`. Simplify using `only [κ, AddMonoidHom.coe_toIntLinearMap, kap_spec] at h1`. Conclude with `mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs) h1`.

Establish `hκR : Function.Injective (LinearMap.baseChange ℝ κ)`. Use `flat_real` as an intermediate fact. Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap κ hκ`. Establish `E2 : ∀ t τ i, phiI Ψ (LinearMap.baseChange ℝ κ t) τ i = (τ : E →+* ℂ) (algebraMap (𝓞 E) E s) * theta b Ψ M t τ i`.

Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => intro τ i`. Simplify using the standard rewrite rules. Consider the case `tmul x v`.

Introduce `τ i`. Simplify using `only [LinearMap.baseChange_tmul, phiI_tmul, theta_tmul, κ, AddMonoidHom.coe_toIntLinearMap]`. Rewrite using `[show ((kap b M s hsI v i : 𝓞 E) : E) = algebraMap (𝓞 E) E (kap b M s hsI v i) from rfl, kap_spec, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy => intro τ i`.

Simplify using `only [map_add, Pi.add_apply, hx, hy, mul_add]`. Introduce `t t' h`. Apply `hκR` to reduce the goal to its premises. Apply `(phiI_bijective hΨ).1` to reduce the goal to its premises. Use function extensionality and compare the values at `τ i`.

Rewrite using `[E2, E2, h]`. Use `choose sf hsf hsfM using hsm`. Set `s' : 𝓞 E` to `∏ i, sf (b i)`. Establish `hs' : s' ∈ (𝓞 E)⁰` using `prod_mem fun i _ => hsf (b i)`. Establish `hs'M : ∀ i, s' • b i ∈ M`.

Introduce `i`. Establish `: s' = sf (b i) * ∏ k ∈ Finset.univ.erase i, sf (b k)` using `(Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm`. Rewrite using `[this, mul_comm, mul_smul]`. Conclude with `M.smul_mem _ (hsfM (b i))`. Set `ι₁` to `(iota1 b M s' hs'M).toIntLinearMap`.

Establish `E1 : ∀ t τ i, theta b Ψ M (LinearMap.baseChange ℝ ι₁ t) τ i = (τ : E →+* ℂ) (algebraMap (𝓞 E) E s') * phiI Ψ t τ i`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => intro τ i`. Simplify using the standard rewrite rules.

Consider the case `tmul x n`. Introduce `τ i`. Simplify using `only [LinearMap.baseChange_tmul, phiI_tmul, theta_tmul, ι₁, AddMonoidHom.coe_toIntLinearMap]`. Rewrite using `[iota1_repr, map_mul]`. Rewrite using `[show ((n i : 𝓞 E) : E) = algebraMap (𝓞 E) E (n i) from rfl]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy => intro τ i`. Simplify using `only [map_add, Pi.add_apply, hx, hy, mul_add]`. Introduce `u`. Take `⟨t, ht⟩` from `(phiI_bijective (ι := ι) hΨ).2 (fun τ i => ((τ : E →+* ℂ) (algebraMap (𝓞 E) E s'))⁻¹ * u τ i)`.

Use `⟨LinearMap.baseChange ℝ ι₁ t, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `τ i`. Rewrite using `[E1, ht]`. Simplify using `only`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ (hne s' hs' τ), one_mul]`.
-/
theorem theta_bijective (hΨ : ∀ σ : E →+* ℂ, σ ∈ Ψ ↔ ComplexEmbedding.conjugate σ ∉ Ψ)
    (hfg : Module.Finite (𝓞 E) M) (hsm : ∀ v : V, ∃ s ∈ (𝓞 E)⁰, s • v ∈ M) :
    Function.Bijective (theta b Ψ M) := by
  classical
  have hne : ∀ s ∈ (𝓞 E)⁰, ∀ τ : Ψ, (τ : E →+* ℂ) (algebraMap (𝓞 E) E s) ≠ 0 := by
    intro s hs τ
    rw [map_ne_zero]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  constructor
  ·
    obtain ⟨s, hs, hsI⟩ := exists_den (b := b) hfg
    let κ := (kap b M s hsI).toIntLinearMap
    have hκ : Function.Injective κ := by
      intro v w h
      apply Subtype.ext
      apply b.repr.injective
      ext i
      have h1 := congrArg (fun n => algebraMap (𝓞 E) E (n i)) h
      simp only [κ, AddMonoidHom.coe_toIntLinearMap, kap_spec] at h1
      exact mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs) h1
    have hκR : Function.Injective (LinearMap.baseChange ℝ κ) := by
      have := flat_real
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap κ hκ
    have E2 : ∀ t τ i, phiI Ψ (LinearMap.baseChange ℝ κ t) τ i =
        (τ : E →+* ℂ) (algebraMap (𝓞 E) E s) * theta b Ψ M t τ i := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => intro τ i; simp
      | tmul x v =>
        intro τ i
        simp only [LinearMap.baseChange_tmul, phiI_tmul, theta_tmul, κ,
          AddMonoidHom.coe_toIntLinearMap]
        rw [show ((kap b M s hsI v i : 𝓞 E) : E) = algebraMap (𝓞 E) E (kap b M s hsI v i) from rfl,
          kap_spec, map_mul]
        ring
      | add x y hx hy => intro τ i; simp only [map_add, Pi.add_apply, hx, hy, mul_add]
    intro t t' h
    apply hκR
    apply (phiI_bijective hΨ).1
    funext τ i
    rw [E2, E2, h]
  ·
    choose sf hsf hsfM using hsm
    let s' : 𝓞 E := ∏ i, sf (b i)
    have hs' : s' ∈ (𝓞 E)⁰ := prod_mem fun i _ => hsf (b i)
    have hs'M : ∀ i, s' • b i ∈ M := by
      intro i
      have : s' = sf (b i) * ∏ k ∈ Finset.univ.erase i, sf (b k) :=
        (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
      rw [this, mul_comm, mul_smul]
      exact M.smul_mem _ (hsfM (b i))
    let ι₁ := (iota1 b M s' hs'M).toIntLinearMap
    have E1 : ∀ t τ i, theta b Ψ M (LinearMap.baseChange ℝ ι₁ t) τ i =
        (τ : E →+* ℂ) (algebraMap (𝓞 E) E s') * phiI Ψ t τ i := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => intro τ i; simp
      | tmul x n =>
        intro τ i
        simp only [LinearMap.baseChange_tmul, phiI_tmul, theta_tmul, ι₁,
          AddMonoidHom.coe_toIntLinearMap]
        rw [iota1_repr, map_mul]
        rw [show ((n i : 𝓞 E) : E) = algebraMap (𝓞 E) E (n i) from rfl]
        ring
      | add x y hx hy => intro τ i; simp only [map_add, Pi.add_apply, hx, hy, mul_add]
    intro u
    obtain ⟨t, ht⟩ := (phiI_bijective (ι := ι) hΨ).2
      (fun τ i => ((τ : E →+* ℂ) (algebraMap (𝓞 E) E s'))⁻¹ * u τ i)
    refine ⟨LinearMap.baseChange ℝ ι₁ t, ?_⟩
    funext τ i
    rw [E1, ht]
    simp only
    rw [← mul_assoc, mul_inv_cancel₀ (hne s' hs' τ), one_mul]

end General

end Formalism.L2.Pj.DatLin
