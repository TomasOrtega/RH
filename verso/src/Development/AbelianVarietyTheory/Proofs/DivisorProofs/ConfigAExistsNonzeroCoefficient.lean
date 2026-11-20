import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneEvaluationConstantStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.CTZero

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨hs, A, hA⟩` from `h`. Set `e : (Fin 0 ⊕ Fin s) ≃ Fin n` to `(Equiv.emptySum (Fin 0) (Fin s)).trans (finCongr (by omega))`. Use `set D : Matrix (Fin 0 ⊕ Fin s) (Fin 0 ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD`. Establish `hDD : D * D = 1`. Rewrite using `[hD, Matrix.fromBlocks_multiply]`.

Simplify using `[Matrix.fromBlocks_one]`. Establish `h1 : Aᵀ * (M * A.map star * D) = 1`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hDD]`. Establish `h2 : (M * A.map star * D) * Aᵀ = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).mp h1`. Establish `h3 : A * (M * A.map star * D)ᵀ = 1`.

Use `congrArg Matrix.transpose h2` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one]`. Then use the resulting hypothesis. Use `set w := (M * A.map star * D)ᵀ *ᵥ y`. Establish `hyw : y = A *ᵥ w` using `by rw [Matrix.mulVec_mulVec, h3, Matrix.one_mulVec]`. Establish `hst : star (A *ᵥ w) = A.map star *ᵥ star w`.

Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, star_sum]`. Establish `key : y ⬝ᵥ M *ᵥ star y = w ⬝ᵥ D *ᵥ star w`. Rewrite using `[← hA, hyw, hst, Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul]`. Simplify using `only [Matrix.vecMul_vecMul, Matrix.mul_assoc]`.

Establish `h0 : w ⬝ᵥ D *ᵥ star w = 0` using `key.symm.trans hy`. Establish `hsum : ∑ i : Fin s, w (Sum.inr i) * star (w (Sum.inr i)) = 0`. Simplify using `[hD, dotProduct, Matrix.mulVec, Matrix.fromBlocks, Fintype.sum_sum_type] at h0`. Simplify `h0` using `[Matrix.one_apply]`. Establish `hz : ∀ i, w (Sum.inr i) = 0`.

Establish `hr : ∑ i : Fin s, Complex.normSq (w (Sum.inr i)) = 0`. Establish `: ((∑ i : Fin s, Complex.normSq (w (Sum.inr i)) : ℝ) : ℂ) = 0`. Rewrite using `[← hsum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.star_def, Complex.mul_conj]`. Conclude with `this` after adjusting the coercions. Introduce `i`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (w (Sum.inr j)))).mp hr i (Finset.mem_univ _)` as an intermediate fact. Conclude with `Complex.normSq_eq_zero.mp this`.

Establish `hw : w = 0`. Use function extensionality and compare the values at `i`. Break down `i with i | i` into its components or cases. Conclude with `i.elim0`. Conclude with `hz i`.

Rewrite using `[hyw, hw, Matrix.mulVec_zero]`.
-/
theorem hasSig_zero_aniso {n s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M 0 s) (y : Fin n → ℂ)
    (hy : y ⬝ᵥ M *ᵥ star y = 0) : y = 0 := by
  obtain ⟨hs, A, hA⟩ := h
  let e : (Fin 0 ⊕ Fin s) ≃ Fin n := (Equiv.emptySum (Fin 0) (Fin s)).trans (finCongr (by omega))
  set D : Matrix (Fin 0 ⊕ Fin s) (Fin 0 ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have hDD : D * D = 1 := by
    rw [hD, Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  have h1 : Aᵀ * (M * A.map star * D) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hDD]
  have h2 : (M * A.map star * D) * Aᵀ = 1 := (Matrix.mul_eq_one_comm_of_equiv e).mp h1
  have h3 : A * (M * A.map star * D)ᵀ = 1 := by
    have := congrArg Matrix.transpose h2
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  set w := (M * A.map star * D)ᵀ *ᵥ y
  have hyw : y = A *ᵥ w := by rw [Matrix.mulVec_mulVec, h3, Matrix.one_mulVec]
  have hst : star (A *ᵥ w) = A.map star *ᵥ star w := by
    ext i; simp [Matrix.mulVec, dotProduct, star_sum]
  have key : y ⬝ᵥ M *ᵥ star y = w ⬝ᵥ D *ᵥ star w := by
    rw [← hA, hyw, hst, Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, ← Matrix.vecMul_transpose,
      Matrix.vecMul_vecMul]
    simp only [Matrix.vecMul_vecMul, Matrix.mul_assoc]
  have h0 : w ⬝ᵥ D *ᵥ star w = 0 := key.symm.trans hy
  have hsum : ∑ i : Fin s, w (Sum.inr i) * star (w (Sum.inr i)) = 0 := by
    simp [hD, dotProduct, Matrix.mulVec, Matrix.fromBlocks, Fintype.sum_sum_type] at h0
    simpa [Matrix.one_apply] using h0
  have hz : ∀ i, w (Sum.inr i) = 0 := by
    have hr : ∑ i : Fin s, Complex.normSq (w (Sum.inr i)) = 0 := by
      have : ((∑ i : Fin s, Complex.normSq (w (Sum.inr i)) : ℝ) : ℂ) = 0 := by
        rw [← hsum]; push_cast; refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.star_def, Complex.mul_conj]
      exact_mod_cast this
    intro i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (w (Sum.inr j)))).mp hr i (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.mp this
  have hw : w = 0 := by
    funext i; rcases i with i | i
    · exact i.elim0
    · exact hz i
  rw [hyw, hw, Matrix.mulVec_zero]

/- English proof (translation)
Introduce `x hx`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Set `τ : E →+* ℂ` to `(B.emb w).1`. Establish `hcm : ∀ z : E, τ (σ z) = star (τ z)` using `fun z => hB.cm.2.2.2 τ z`. Establish `hy : (fun i => τ (x i)) ⬝ᵥ (X.J.map τ) *ᵥ star (fun i => τ (x i)) = 0`.

Use `congrArg τ hx` as an intermediate fact. Rewrite `this` using `[map_zero]`. Establish `hs : (star fun i => τ (x i)) = τ ∘ fun i => σ (x i)`. Use extensionality with `i`. Simplify using `[hcm]`.

Rewrite using `[← this, hs, form, RingHom.map_dotProduct]`. Use `show (τ ∘ x) ⬝ᵥ _ = (τ ∘ x) ⬝ᵥ _`. Use `congr 1`. Use extensionality with `i`. Conclude with `(RingHom.map_mulVec τ X.J _ i).symm`.

Use `hasSig_zero_aniso (h.sig w) _ hy` as an intermediate fact. Use function extensionality and compare the values at `i`. Conclude with `τ.injective (by simpa using congrFun this i)`.
-/
theorem aniso_of_herm {n s : ℕ} (B : Base F E) (hB : B.IsGood σ) (X : Spc F E n) (h : X.IsHerm σ B 0 s) :
    ∀ x, form σ X.J x x = 0 → x = 0 := by
  intro x hx
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  let τ : E →+* ℂ := (B.emb w).1
  have hcm : ∀ z : E, τ (σ z) = star (τ z) := fun z => hB.cm.2.2.2 τ z
  have hy : (fun i => τ (x i)) ⬝ᵥ (X.J.map τ) *ᵥ star (fun i => τ (x i)) = 0 := by
    have := congrArg τ hx
    rw [map_zero] at this
    have hs : (star fun i => τ (x i)) = τ ∘ fun i => σ (x i) := by
      ext i; simp [hcm]
    rw [← this, hs, form, RingHom.map_dotProduct]
    show (τ ∘ x) ⬝ᵥ _ = (τ ∘ x) ⬝ᵥ _
    congr 1
    ext i
    exact (RingHom.map_mulVec τ X.J _ i).symm
  have := hasSig_zero_aniso (h.sig w) _ hy
  funext i
  exact τ.injective (by simpa using congrFun this i)

/- English proof (translation)
Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `Φ ⟨f, -, φ, hSB, hev, rfl⟩`. Conclude with `GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v h => h.1.trans h.2)`.
-/
theorem polData_le_schA {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ X W)
    (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.mpr ?_
  rintro Φ ⟨f, -, φ, hSB, hev, rfl⟩
  exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB ((hev.and hM.std).mono fun v h => h.1.trans h.2)

end GlobalTheory.ThK.CTZero

open GlobalTheory.ThK.CTZero in

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e' he'`. Take `⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩` from `G₁`. Establish `hv : V₁' = G.V'` using `hC.eV`. Substitute `hv` using the available equality. Distinguish the cases in `hg : M₁'.IsGood B.ψ`.

Take `⟨C₀, hC₀, h1, -⟩` from `GlobalTheory.T.adapted_plane_evaluation_constant hKP F E σ B a' (b + 2 + a') (b + a') G.V' G.W W₁ G.M' M₁' H' 0 (b + 1) hC.hH' hg e' he'`. Use `⟨C₀, hC₀, ?_⟩` and prove the remaining obligations. Introduce `X om om' om₁ om₁' hT _ Φ' hΦ' g`. Establish `hV'` using `hT.geo.hV'`. Rewrite `hV'` using `[hC.q0]`.

Establish `han` using `aniso_of_herm B hT.base G.V' hV'`. Conclude with `h1 han _ _ _ _ _ _ _ (Check.isPair_of_isTriple hT).2 Φ' (polData_le_schA B G.M' hT.geo.hM' hΦ') g`. Use `⟨1, one_ne_zero, ?_⟩` and prove the remaining obligations. Introduce `X om om' om₁ om₁' _ hT₁`. Conclude with `absurd hT₁.geo.hM' hg`.
-/
theorem GlobalTheory.ThK.ctSmallZeroTheta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e', IsEv B G.M' G₁.M' 1 H'.ι (iso0 a' H') e' → ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ PolData B G.M', ∀ g, IsCT H' (theta om' Φ' g) (fun h => C₀ * thetaSum F (e' (om' (g, h) Φ'))) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e' he'
  obtain ⟨p₁, q₁, V₁, V₁', W₁, M₁, M₁'⟩ := G₁
  have hv : V₁' = G.V' := hC.eV
  subst hv
  by_cases hg : M₁'.IsGood B.ψ
  · obtain ⟨C₀, hC₀, h1, -⟩ := GlobalTheory.T.adapted_plane_evaluation_constant hKP F E σ B a' (b + 2 + a') (b + a') G.V' G.W W₁ G.M' M₁' H' 0 (b + 1)
      hC.hH' hg e' he'
    refine ⟨C₀, hC₀, ?_⟩
    intro X om om' om₁ om₁' hT _ Φ' hΦ' g
    have hV' := hT.geo.hV'
    rw [hC.q0] at hV'
    have han := aniso_of_herm B hT.base G.V' hV'
    exact h1 han _ _ _ _ _ _ _ (Check.isPair_of_isTriple hT).2 Φ' (polData_le_schA B G.M' hT.geo.hM' hΦ') g
  · refine ⟨1, one_ne_zero, ?_⟩
    intro X om om' om₁ om₁' _ hT₁
    exact absurd hT₁.geo.hM' hg
