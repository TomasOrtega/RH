import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermDiagCM

open ComplexConjugate

/- English proof (translation)
Set `B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ` to `LinearMap.mk₂ ℝ (fun v v' => (v ⬝ᵥ M.mulVec (star v')).im) (fun a b c => by simp [add_dotProduct]) (fun r a b => by simp [smul_dotProduct]) (fun a b c => by simp [star_add, Matrix.mulVec_add, dotProduct_add]) (fun r a b => by simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])`. Establish `h1 : ∀ v ∈ Λ, B v = 0` using `fun v hv => LinearMap.ext_on hs (fun v' hv' => by simpa [B] using h0 v hv v' hv')`. Establish `hB : B = 0` using `LinearMap.ext_on hs (fun v hv => by simpa using h1 v hv)`. Establish `him : ∀ z w : Fin n → ℂ, (z ⬝ᵥ M.mulVec (star w)).im = 0` using `fun z w => by`. Use `congrArg (fun f => f z w) hB` as an intermediate fact.

Simplify `this` using `[B]`. Establish `hall : ∀ z w : Fin n → ℂ, z ⬝ᵥ M.mulVec (star w) = 0` using `fun z w => by`. Apply `Complex.ext` to reduce the goal to its premises. Use `him (Complex.I • z) w` as an intermediate fact. Simplify `this` using `[smul_dotProduct]`.

Simplify using `using him z w`. Use extensionality with `i j`. Use `hall (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single, single_dotProduct]`.
-/
theorem matrix_eq_zero_of_im_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (Λ : Submodule ℤ (Fin n → ℂ)) (hs : Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤)
    (h0 : ∀ v ∈ Λ, ∀ v' ∈ Λ, (v ⬝ᵥ M.mulVec (star v')).im = 0) : M = 0 := by
  let B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun v v' => (v ⬝ᵥ M.mulVec (star v')).im)
      (fun a b c => by simp [add_dotProduct])
      (fun r a b => by simp [smul_dotProduct])
      (fun a b c => by simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (fun r a b => by simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  have h1 : ∀ v ∈ Λ, B v = 0 := fun v hv =>
    LinearMap.ext_on hs (fun v' hv' => by simpa [B] using h0 v hv v' hv')
  have hB : B = 0 := LinearMap.ext_on hs (fun v hv => by simpa using h1 v hv)
  have him : ∀ z w : Fin n → ℂ, (z ⬝ᵥ M.mulVec (star w)).im = 0 := fun z w => by
    have := congrArg (fun f => f z w) hB
    simpa [B] using this
  have hall : ∀ z w : Fin n → ℂ, z ⬝ᵥ M.mulVec (star w) = 0 := fun z w => by
    apply Complex.ext
    · have := him (Complex.I • z) w
      simpa [smul_dotProduct] using this
    · simpa using him z w
  ext i j
  have := hall (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single, single_dotProduct] using this

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Set `f : I × Bool → (E →+* ℂ)` to `fun p => cond p.2 (ComplexEmbedding.conjugate (φ p.1)) (φ p.1)`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, a⟩ ⟨j, b⟩ hij`. Establish `uniq : ∀ k l, φ k = φ l ∨ φ k = ComplexEmbedding.conjugate (φ l) → k = l`.

Introduce `k l hkl`. Take `⟨m, -, hm⟩` from `hφ (φ k)`. Conclude with `(hm k (Or.inl rfl)).trans (hm l hkl).symm`. Apply the tactic sequence `cases a <;> cases b <;> simp only [f, cond_true, cond_false] at hij`. Simplify using `[uniq i j (Or.inl hij)]`.

Establish `hij'` using `uniq i j (Or.inr hij)`. Substitute `hij'` using the available equality. Conclude with `absurd (ComplexEmbedding.isReal_iff.mpr hij.symm) (IsTotallyComplex.complexEmbedding_not_isReal (φ i))`. Establish `hij'` using `uniq j i (Or.inr hij.symm)`. Substitute `hij'` using the available equality.

Conclude with `absurd (ComplexEmbedding.isReal_iff.mpr hij) (IsTotallyComplex.complexEmbedding_not_isReal (φ j))`. Establish `: φ i = φ j`. Use `congrArg ComplexEmbedding.conjugate hij` as an intermediate fact. Simplify using `using this`. Simplify using `[uniq i j (Or.inl this)]`.

Introduce `σ`. Take `⟨i, hi, -⟩` from `hφ σ`. Break down `hi with h | h` into its components or cases. Conclude with `⟨(i, false), h.symm⟩`. Conclude with `⟨(i, true), h.symm⟩`.

Rewrite using `[← Fintype.sum_bijective f hf (fun p => f p w) (fun σ => σ w) (fun _ => rfl), Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool]`. Simplify using `[f, ComplexEmbedding.conjugate_coe_eq, add_comm]`.
-/
theorem sum_embeddings_eq {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : GlobalTheory.CMVal.IsCMType φ)
    (w : E) : ∑ σ : E →+* ℂ, σ w = ∑ i, (φ i w + conj (φ i w)) := by
  let f : I × Bool → (E →+* ℂ) := fun p => cond p.2 (ComplexEmbedding.conjugate (φ p.1)) (φ p.1)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ hij
      have uniq : ∀ k l, φ k = φ l ∨ φ k = ComplexEmbedding.conjugate (φ l) → k = l := by
        intro k l hkl
        obtain ⟨m, -, hm⟩ := hφ (φ k)
        exact (hm k (Or.inl rfl)).trans (hm l hkl).symm
      cases a <;> cases b <;> simp only [f, cond_true, cond_false] at hij
      · simp [uniq i j (Or.inl hij)]
      · have hij' := uniq i j (Or.inr hij)
        subst hij'
        exact absurd (ComplexEmbedding.isReal_iff.mpr hij.symm)
          (IsTotallyComplex.complexEmbedding_not_isReal (φ i))
      · have hij' := uniq j i (Or.inr hij.symm)
        subst hij'
        exact absurd (ComplexEmbedding.isReal_iff.mpr hij)
          (IsTotallyComplex.complexEmbedding_not_isReal (φ j))
      · have : φ i = φ j := by
          have := congrArg ComplexEmbedding.conjugate hij
          simpa using this
        simp [uniq i j (Or.inl this)]
    · intro σ
      obtain ⟨i, hi, -⟩ := hφ σ
      rcases hi with h | h
      · exact ⟨(i, false), h.symm⟩
      · exact ⟨(i, true), h.symm⟩
  rw [← Fintype.sum_bijective f hf (fun p => f p w) (fun σ => σ w) (fun _ => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  simp [f, ComplexEmbedding.conjugate_coe_eq, add_comm]

/- English proof (translation)
Set `eq : (E →+* ℂ) ≃ (E →+* ℂ)` to `{ toFun := fun σ => (g : ℂ →+* ℂ).comp σ invFun := fun σ => (g.symm : ℂ →+* ℂ).comp σ left_inv := fun σ => by ext x; simp right_inv := fun σ => by ext x; simp }`. Conclude with `Fintype.sum_equiv eq _ _ (fun σ => by simp [eq])`.
-/
theorem sum_embeddings_map (g : ℂ ≃+* ℂ) (w : E) :
    ∑ σ : E →+* ℂ, g (σ w) = ∑ σ : E →+* ℂ, σ w := by
  let eq : (E →+* ℂ) ≃ (E →+* ℂ) :=
    { toFun := fun σ => (g : ℂ →+* ℂ).comp σ
      invFun := fun σ => (g.symm : ℂ →+* ℂ).comp σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  exact Fintype.sum_equiv eq _ _ (fun σ => by simp [eq])

/- English proof (translation)
Establish `e1 : σ (β * x * IsCMField.complexConj E x') = σ β * (σ x * conj (σ x'))`. Rewrite using `[map_mul, map_mul, IsCMField.complexEmbedding_complexConj]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, map_mul, hβ]`. Establish `hs` using `Complex.sub_conj (σ x * conj (σ x'))`.

Move the coercions through the operations in `at hs`. Take the linear combination `(-σ β) * hs`.
-/
theorem term_eq (σ : E →+* ℂ) (β x x' : E) (hβ : conj (σ β) = -σ β) :
    (2 * Complex.I * σ β) * (((σ x * conj (σ x')).im : ℝ) : ℂ) =
      σ (β * x * IsCMField.complexConj E x') + conj (σ (β * x * IsCMField.complexConj E x')) := by
  have e1 : σ (β * x * IsCMField.complexConj E x') = σ β * (σ x * conj (σ x')) := by
    rw [map_mul, map_mul, IsCMField.complexEmbedding_complexConj]; ring
  rw [e1, map_mul, hβ]
  have hs := Complex.sub_conj (σ x * conj (σ x'))
  push_cast at hs
  linear_combination (-σ β) * hs

end CM

end GlobalTheory.HermDiagCM

open ComplexConjugate in

/- English proof (translation)
Introduce `K _ _ d δ io hd hδ g hg E _ _ _ _ I _ φ hφ hio n e Λ L hs hΛ h β hh N hN Hm hHm hform`. Establish `hconj : ∀ (σ : E →+* ℂ) (y : E), conj (σ y) = σ (IsCMField.complexConj E y)` using `fun σ y => (IsCMField.complexEmbedding_complexConj E σ y).symm`. Establish `hgcomp : ∀ i y, ((g : ℂ →+* ℂ).comp (φ i)) y = g (φ i y)` using `fun i y => rfl`. Establish `hβi : ∀ i, conj (φ i β) = -(φ i β)`. Introduce `i`.

Establish `h2 : conj ((h i : ℂ)) = (h i : ℂ)` using `Complex.conj_ofReal _`. Rewrite `h2` using `[hh i, map_mul, map_mul, Complex.conj_I, map_ofNat]`. Establish `h3 : (2 * Complex.I : ℂ) ≠ 0` using `by simp`. Establish `h4 : (2 * Complex.I) * conj (φ i β) = (2 * Complex.I) * (-(φ i β))`. Take the linear combination `-h2`.

Conclude with `mul_left_cancel₀ h3 h4`. Establish `hcβ : ∀ i, IsCMField.complexConj E β = -β` using `fun i => (φ i).injective (by rw [← hconj, hβi, map_neg])`. Establish `hgc : ∀ i y, conj (g (φ i y)) = g (conj (φ i y))`. Introduce `i y`. Rewrite using `[← hgcomp, hconj, hconj, hgcomp]`.

Establish `hgβ : ∀ i, conj (g (φ i β)) = -(g (φ i β))`. Introduce `i`. Rewrite using `[hgc, hβi, map_neg]`. Use `set h' : I → ℝ := fun i => ((2 * Complex.I * g (φ i β)) / N).re with hh'def`. Establish `hh' : ∀ i, (h' i : ℂ) = 2 * Complex.I * g (φ i β) / N`.

Introduce `i`. Conclude with `Complex.conj_eq_iff_re.mp (by`. Rewrite using `[map_div₀, map_mul, map_mul, Complex.conj_I, hgβ i, map_ofNat, Complex.conj_ofReal]`. Use the proof step `ring)`. Establish `hN' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`.

Use `⟨h', ?_, ?_⟩` and prove the remaining obligations. Use `set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) with hD`. It suffices to establish `Hm - D = 0 from sub_eq_zero.mp this`. Apply `matrix_eq_zero_of_im_form (Hm - D) Λ hs` to reduce the goal to its premises. Introduce `v hv v' hv'`.

Take `⟨x, hx, rfl⟩` from `(hΛ v).mp hv`. Take `⟨x', hx', rfl⟩` from `(hΛ v').mp hv'`. Rewrite using `[Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, hform x hx x' hx', sub_eq_zero]`. Establish `hDv : ((fun j ↦ g (φ (e j) x)) ⬝ᵥ D.mulVec (star fun j ↦ g (φ (e j) x'))).im = ∑ i, h' i * (g (φ i x) * conj (g (φ i x'))).im`. Rewrite using `[dotProduct, Complex.im_sum]`.

Rewrite using `[← Equiv.sum_comp e (fun i => h' i * (g (φ i x) * conj (g (φ i x'))).im)]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Simplify using `only [hD, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]`. Rewrite using `[mul_left_comm, Complex.im_ofReal_mul]`. Rewrite using `[hDv]`.

Apply `Complex.ofReal_injective` to reduce the goal to its premises. Use `push_cast`. Simplify using `only [hh, hh']`. Use `set w := β * x * IsCMField.complexConj E x' with hw`. Establish `A : ∀ i, 2 * Complex.I * g (φ i β) / N * (((g (φ i x) * conj (g (φ i x'))).im : ℝ) : ℂ) = (N : ℂ)⁻¹ * (g (φ i w) + conj (g (φ i w)))`.

Introduce `i`. Use `term_eq ((g : ℂ →+* ℂ).comp (φ i)) β x x' (by rw [hgcomp]; exact hgβ i)` as an intermediate fact. Simplify using `only [hgcomp] at this`. Rewrite using `[div_eq_mul_inv, mul_comm _ (N : ℂ)⁻¹, _root_.mul_assoc, this]`. Establish `B : ∀ i, 2 * Complex.I * φ i β * (((φ i x * conj (φ i x')).im : ℝ) : ℂ) = φ i w + conj (φ i w)` using `fun i => term_eq (φ i) β x x' (hβi i)`.

Rewrite using `[Finset.sum_congr rfl (fun i _ => A i), Finset.sum_congr rfl (fun i _ => B i), ← Finset.mul_sum]`. Use `congr 1`. Rewrite using `[← sum_embeddings_eq φ hφ w, ← sum_embeddings_map g w, ← map_sum, sum_embeddings_eq φ hφ w, map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_add, hgc]`.

Introduce `i`. Establish `key : g (Complex.I * (Real.sqrt d : ℂ)) = Complex.I * (Real.sqrt d : ℂ)`. Establish `hsq : (Complex.I * (Real.sqrt d : ℂ)) ^ 2 = -(d : ℂ)`. Rewrite using `[mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hio2 : (io δ) ^ 2 = -(d : ℂ)` using `by rw [← map_pow, hδ, map_neg, map_natCast]`. Establish `hprod : (io δ - Complex.I * (Real.sqrt d : ℂ)) * (io δ + Complex.I * (Real.sqrt d : ℂ)) = 0`. Take the linear combination `hio2 - hsq`. Break down `mul_eq_zero.mp hprod with h1 | h1` into its components or cases.

Establish `h5 : Complex.I * (Real.sqrt d : ℂ) = io δ` using `by linear_combination -h1`. Rewrite using `[h5, hg]`. Establish `h5 : Complex.I * (Real.sqrt d : ℂ) = -io δ` using `by linear_combination h1`. Rewrite using `[h5, map_neg, hg]`. Rewrite using `[hh i, hh' i]`.

Establish `e2 : 2 * Complex.I * φ i β * (Real.sqrt d : ℂ) = 2 * φ i β * (Complex.I * (Real.sqrt d : ℂ))`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2, map_mul, map_mul, key, map_ofNat]`. Clear the denominators using the available nonvanishing facts.
-/
theorem GlobalTheory.HermDiagCM.diagonal_of_conj_form : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) →
      ∀ (n : ℕ) (e : Fin n ≃ I) (Λ : Submodule ℤ (Fin n → ℂ)) (L : Set E),
        Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ g (φ (e j) x)) →
      ∀ (h : I → ℝ) (β : E), (∀ i, (h i : ℂ) = 2 * Complex.I * φ i β) → ∀ N : ℝ, 0 < N →
      ∀ Hm : Matrix (Fin n) (Fin n) ℂ, Hm.IsHermitian →
        (∀ x ∈ L, ∀ x' ∈ L, ((fun j ↦ g (φ (e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) x'))).im =
          N⁻¹ * ∑ i, h i * (φ i x * starRingEnd ℂ (φ i x')).im) →
        ∃ h' : I → ℝ, Hm = Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) ∧
          ∀ i, g ((h i : ℂ) * (Real.sqrt d : ℝ)) = (N : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  intro K _ _ d δ io hd hδ g hg E _ _ _ _ I _ φ hφ hio n e Λ L hs hΛ h β hh N hN Hm hHm hform
  have hconj : ∀ (σ : E →+* ℂ) (y : E), conj (σ y) = σ (IsCMField.complexConj E y) :=
    fun σ y => (IsCMField.complexEmbedding_complexConj E σ y).symm
  have hgcomp : ∀ i y, ((g : ℂ →+* ℂ).comp (φ i)) y = g (φ i y) := fun i y => rfl
  have hβi : ∀ i, conj (φ i β) = -(φ i β) := by
    intro i
    have h2 : conj ((h i : ℂ)) = (h i : ℂ) := Complex.conj_ofReal _
    rw [hh i, map_mul, map_mul, Complex.conj_I, map_ofNat] at h2
    have h3 : (2 * Complex.I : ℂ) ≠ 0 := by simp
    have h4 : (2 * Complex.I) * conj (φ i β) = (2 * Complex.I) * (-(φ i β)) := by
      linear_combination -h2
    exact mul_left_cancel₀ h3 h4
  have hcβ : ∀ i, IsCMField.complexConj E β = -β := fun i =>
    (φ i).injective (by rw [← hconj, hβi, map_neg])
  have hgc : ∀ i y, conj (g (φ i y)) = g (conj (φ i y)) := by
    intro i y
    rw [← hgcomp, hconj, hconj, hgcomp]
  have hgβ : ∀ i, conj (g (φ i β)) = -(g (φ i β)) := by
    intro i
    rw [hgc, hβi, map_neg]
  set h' : I → ℝ := fun i => ((2 * Complex.I * g (φ i β)) / N).re with hh'def
  have hh' : ∀ i, (h' i : ℂ) = 2 * Complex.I * g (φ i β) / N := by
    intro i
    exact Complex.conj_eq_iff_re.mp (by
      rw [map_div₀, map_mul, map_mul, Complex.conj_I, hgβ i, map_ofNat, Complex.conj_ofReal]; ring)
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨h', ?_, ?_⟩
  · set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) with hD
    suffices Hm - D = 0 from sub_eq_zero.mp this
    apply matrix_eq_zero_of_im_form (Hm - D) Λ hs
    intro v hv v' hv'
    obtain ⟨x, hx, rfl⟩ := (hΛ v).mp hv
    obtain ⟨x', hx', rfl⟩ := (hΛ v').mp hv'
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, hform x hx x' hx', sub_eq_zero]
    have hDv : ((fun j ↦ g (φ (e j) x)) ⬝ᵥ D.mulVec (star fun j ↦ g (φ (e j) x'))).im =
        ∑ i, h' i * (g (φ i x) * conj (g (φ i x'))).im := by
      rw [dotProduct, Complex.im_sum]
      rw [← Equiv.sum_comp e (fun i => h' i * (g (φ i x) * conj (g (φ i x'))).im)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hD, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]
      rw [mul_left_comm, Complex.im_ofReal_mul]
    rw [hDv]
    apply Complex.ofReal_injective
    push_cast
    simp only [hh, hh']
    set w := β * x * IsCMField.complexConj E x' with hw
    have A : ∀ i, 2 * Complex.I * g (φ i β) / N * (((g (φ i x) * conj (g (φ i x'))).im : ℝ) : ℂ) =
        (N : ℂ)⁻¹ * (g (φ i w) + conj (g (φ i w))) := by
      intro i
      have := term_eq ((g : ℂ →+* ℂ).comp (φ i)) β x x' (by rw [hgcomp]; exact hgβ i)
      simp only [hgcomp] at this
      rw [div_eq_mul_inv, mul_comm _ (N : ℂ)⁻¹, _root_.mul_assoc, this]
    have B : ∀ i, 2 * Complex.I * φ i β * (((φ i x * conj (φ i x')).im : ℝ) : ℂ) =
        φ i w + conj (φ i w) := fun i => term_eq (φ i) β x x' (hβi i)
    rw [Finset.sum_congr rfl (fun i _ => A i), Finset.sum_congr rfl (fun i _ => B i),
      ← Finset.mul_sum]
    congr 1
    rw [← sum_embeddings_eq φ hφ w, ← sum_embeddings_map g w, ← map_sum, sum_embeddings_eq φ hφ w,
      map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_add, hgc]
  · intro i
    have key : g (Complex.I * (Real.sqrt d : ℂ)) = Complex.I * (Real.sqrt d : ℂ) := by
      have hsq : (Complex.I * (Real.sqrt d : ℂ)) ^ 2 = -(d : ℂ) := by
        rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        push_cast; ring
      have hio2 : (io δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ, map_neg, map_natCast]
      have hprod : (io δ - Complex.I * (Real.sqrt d : ℂ)) * (io δ + Complex.I * (Real.sqrt d : ℂ)) = 0 := by
        linear_combination hio2 - hsq
      rcases mul_eq_zero.mp hprod with h1 | h1
      · have h5 : Complex.I * (Real.sqrt d : ℂ) = io δ := by linear_combination -h1
        rw [h5, hg]
      · have h5 : Complex.I * (Real.sqrt d : ℂ) = -io δ := by linear_combination h1
        rw [h5, map_neg, hg]
    rw [hh i, hh' i]
    have e2 : 2 * Complex.I * φ i β * (Real.sqrt d : ℂ) = 2 * φ i β * (Complex.I * (Real.sqrt d : ℂ)) := by
      ring
    rw [e2, map_mul, map_mul, key, map_ofNat]
    field_simp
