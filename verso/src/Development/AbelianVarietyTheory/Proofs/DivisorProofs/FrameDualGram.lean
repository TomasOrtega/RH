import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PlaneFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hσ.2.2.2, hσ.2.2.2, star_star]`.
-/
theorem conj_conj {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) (a : E) : σ (σ a) = a := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

/- English proof (translation)
Take `⟨hrs, A, hA⟩` from `h`. Set `e : Fin r ⊕ Fin s ≃ Fin n` to `finSumFinEquiv.trans (finCongr hrs)`. Establish `h2 : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star = (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm`. Rewrite using `[← hA]`. Use extensionality with `i j`.

Simplify using `[Matrix.mul_apply]`. Establish `h3` using `congrArg Matrix.det h2`. Rewrite `h3` using `[Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul]`. Introduce `h0`. Rewrite `h3` using `[h0, Matrix.det_neg]`.

Simplify using `at h3`. Conclude with `pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) h3.symm`.
-/
theorem det_ne_zero_of_hasSig {n r s : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  have h2 : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [Matrix.mul_apply]
  have h3 := congrArg Matrix.det h2
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul] at h3
  intro h0
  rw [h0, Matrix.det_neg] at h3
  simp at h3
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) h3.symm

/- English proof (translation)
Establish `hs : ∀ i j, σ (J i j) = -J j i` using `fun i j => hJ j i`. Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hs, conj_conj hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring` and prove the remaining obligations.
-/
theorem form_skew {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  have hs : ∀ i j, σ (J i j) = -J j i := fun i j => hJ j i
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hs, conj_conj hσ, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PlaneFrame

namespace GlobalTheory.PlaneFrame

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH`. Establish `hinv` using `conj_conj hσ`. Take `⟨hrank, hxx, hyy, hxy, horth, hgram, -, hsplit, -, -, -⟩` from `hH`. Substitute `hrank` using the available equality. Establish `hsk` using `form_skew hσ hW.skew`.

Establish `hyx : form σ W.J H'.y H'.x = -1` using `by rw [hsk, hxy, map_one]`. Establish `hxι : ∀ u, form σ W.J H'.x (H'.ι *ᵥ u) = 0` using `fun u => by rw [hsk, (horth u).1, map_zero, neg_zero]`. Establish `hyι : ∀ u, form σ W.J H'.y (H'.ι *ᵥ u) = 0` using `fun u => by rw [hsk, (horth u).2, map_zero, neg_zero]`. Establish `hlin : ∀ (u : Fin d₁ → E) (a b : E) (w : Fin (d₁ + 2) → E), form σ W.J (H'.ι *ᵥ u + (a • H'.x + b • H'.y)) w = form σ W.J (H'.ι *ᵥ u) w + a * form σ W.J H'.x w + b * form σ W.J H'.y w`. Introduce `u a b w`.

Simplify using `only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `Φ : ((Fin d₁ → E) × E × E) →ₗ[E] (Fin (d₁ + 2) → E)` to `H'.ι.mulVecLin.coprod ((LinearMap.toSpanSingleton E _ H'.x).coprod (LinearMap.toSpanSingleton E _ H'.y))`. Establish `hΦ : ∀ p, Φ p = H'.ι *ᵥ p.1 + (p.2.1 • H'.x + p.2.2 • H'.y)` using `fun p => rfl`. Establish `hsurj : Function.Surjective Φ`.

Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hW.lat.span_eq_top, Submodule.span_le]`. Introduce `z hz`. Take `⟨a, b, u, -, -, -, rfl⟩` from `hsplit z hz`. Conclude with `⟨(u, a, b), by rw [hΦ]; abel⟩`. Establish `hinj : Function.Injective Φ`.

Rewrite using `[LinearMap.injective_iff_surjective_of_finrank_eq_finrank]`. Conclude with `hsurj`. Simplify using `[Module.finrank_prod]`. Set `eΦ` to `LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩`. Set `πl : (Fin (d₁ + 2) → E) →ₗ[E] (Fin d₁ → E)` to `LinearMap.fst E _ _ ∘ₗ eΦ.symm.toLinearMap`.

Establish `hπ : ∀ p, πl (Φ p) = p.1`. Introduce `p`. Simplify using `only [πl, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.fst_apply]`. Rewrite using `[show Φ p = eΦ p from rfl, LinearEquiv.symm_apply_apply]`. Use `⟨LinearMap.toMatrix' πl, ?_, ?_, ?_⟩` and prove the remaining obligations.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun u => ?_` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, LinearMap.comp_apply, Matrix.toLin'_apply]`. Use `hπ (u, 0, 0)` as an intermediate fact. Rewrite `this` using `[hΦ]`.

Simplify using `using this`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun z => ?_` and prove the remaining obligations. Take `⟨⟨u, a, b⟩, rfl⟩` from `hsurj z`. Rewrite using `[Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]`.

Rewrite using `[Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, ← Matrix.mulVec_mulVec, show LinearMap.toMatrix' πl *ᵥ Φ (u, a, b) = πl (Φ (u, a, b)) from (Matrix.toLin'_apply _ _).symm.trans (by rw [Matrix.toLin'_toMatrix']), hπ]`. Establish `e1 : (W.J *ᵥ fun i => σ (H'.y i)) ⬝ᵥ Φ (u, a, b) = a`. Rewrite using `[dotProduct_comm, ← form, hΦ, hlin, (horth u).2, hxy, hyy]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (W.J *ᵥ fun i => σ (H'.x i)) ⬝ᵥ Φ (u, a, b) = -b`.

Rewrite using `[dotProduct_comm, ← form, hΦ, hlin, (horth u).1, hxx, hyx]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2, hΦ]`. Use extensionality with `i`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hgram, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]`. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hJdet : W.J.det ≠ 0`. Introduce `h0`.

Apply `det_ne_zero_of_hasSig _ (hW.sig w)` to reduce the goal to its premises. Rewrite using `[Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]`. Establish `hJinj : Function.Injective W.J.mulVec` using `Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hJdet))`. Establish `hσinj : Function.Injective σ` using `fun a b h => by rw [← hinv a, ← hinv b, h]`. Establish `hιinj : Function.Injective H'.ι.mulVec`.

Introduce `u v h`. Use `hinj (a₁ := (u, 0, 0)) (a₂ := (v, 0, 0)) (by rw [hΦ, hΦ]; simpa using h)` as an intermediate fact. Simplify using `using congrArg Prod.fst this`. Introduce `v v' hvv`. Rewrite using `[← sub_eq_zero]`.

Establish `h0 : (H'.ιᵀ * W.J * H'.ι.map σ) *ᵥ (v - v') = 0` using `by rw [Matrix.mulVec_sub, hvv, sub_self]`. Use `set c : Fin d₁ → E := fun j => σ ((v - v') j) with hcdef`. Establish `hc : H'.ι.map σ *ᵥ (v - v') = fun i => σ ((H'.ι *ᵥ c) i)`. Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, c, hinv]`.

Establish `h1 : ∀ u, form σ W.J (H'.ι *ᵥ u) (H'.ι *ᵥ c) = 0`. Introduce `u`. Establish `: form σ W.J (H'.ι *ᵥ u) (H'.ι *ᵥ c) = u ⬝ᵥ ((H'.ιᵀ * W.J * H'.ι.map σ) *ᵥ (v - v'))`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, form]`. Rewrite using `[this, h0, dotProduct_zero]`.

Establish `h2 : ∀ z, form σ W.J z (H'.ι *ᵥ c) = 0`. Introduce `z`. Take `⟨⟨u, a, b⟩, rfl⟩` from `hsurj z`. Rewrite using `[hΦ, hlin, h1, hxι, hyι]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h3 : W.J *ᵥ (fun i => σ ((H'.ι *ᵥ c) i)) = 0`. Use extensionality with `i`. Use `h2 (Pi.single i 1)` as an intermediate fact. Rewrite `this` using `[form, single_dotProduct, one_mul]`. Simplify using `using this`.

Establish `h4 : H'.ι *ᵥ c = 0`. Use `hJinj (h3.trans (Matrix.mulVec_zero _).symm)` as an intermediate fact. Use extensionality with `i`. Conclude with `hσinj ((congrFun this i).trans (map_zero σ).symm)`. Establish `h5 : c = 0` using `hιinj (h4.trans (Matrix.mulVec_zero _).symm)`.

Use extensionality with `j`. Use `congrFun h5 j` as an intermediate fact. Simplify using `only [c, Pi.zero_apply] at this`. Simplify using `using hσinj (this.trans (map_zero σ).symm)`.
-/
theorem frame_dual_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧
      Matrix.vecMulVec H'.x (W.J *ᵥ fun i => σ (H'.y i)) + H'.ι * π - Matrix.vecMulVec H'.y (W.J *ᵥ fun i => σ (H'.x i)) = 1 ∧
      IsUnit W₁.J.det := by
  intro F E _ _ _ _ _ σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH
  have hinv := conj_conj hσ
  obtain ⟨hrank, hxx, hyy, hxy, horth, hgram, -, hsplit, -, -, -⟩ := hH
  subst hrank
  have hsk := form_skew hσ hW.skew
  have hyx : form σ W.J H'.y H'.x = -1 := by rw [hsk, hxy, map_one]
  have hxι : ∀ u, form σ W.J H'.x (H'.ι *ᵥ u) = 0 := fun u => by rw [hsk, (horth u).1, map_zero, neg_zero]
  have hyι : ∀ u, form σ W.J H'.y (H'.ι *ᵥ u) = 0 := fun u => by rw [hsk, (horth u).2, map_zero, neg_zero]
  have hlin : ∀ (u : Fin d₁ → E) (a b : E) (w : Fin (d₁ + 2) → E),
      form σ W.J (H'.ι *ᵥ u + (a • H'.x + b • H'.y)) w =
        form σ W.J (H'.ι *ᵥ u) w + a * form σ W.J H'.x w + b * form σ W.J H'.y w := by
    intro u a b w
    simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]; ring
  let Φ : ((Fin d₁ → E) × E × E) →ₗ[E] (Fin (d₁ + 2) → E) :=
    H'.ι.mulVecLin.coprod ((LinearMap.toSpanSingleton E _ H'.x).coprod (LinearMap.toSpanSingleton E _ H'.y))
  have hΦ : ∀ p, Φ p = H'.ι *ᵥ p.1 + (p.2.1 • H'.x + p.2.2 • H'.y) := fun p => rfl
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hW.lat.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨a, b, u, -, -, -, rfl⟩ := hsplit z hz
    exact ⟨(u, a, b), by rw [hΦ]; abel⟩
  have hinj : Function.Injective Φ := by
    rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hsurj
    · simp [Module.finrank_prod]
  let eΦ := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  let πl : (Fin (d₁ + 2) → E) →ₗ[E] (Fin d₁ → E) := LinearMap.fst E _ _ ∘ₗ eΦ.symm.toLinearMap
  have hπ : ∀ p, πl (Φ p) = p.1 := by
    intro p
    simp only [πl, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearMap.fst_apply]
    rw [show Φ p = eΦ p from rfl, LinearEquiv.symm_apply_apply]
  refine ⟨LinearMap.toMatrix' πl, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one, LinearMap.comp_apply, Matrix.toLin'_apply]
    have := hπ (u, 0, 0)
    rw [hΦ] at this
    simpa using this
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun z => ?_
    obtain ⟨⟨u, a, b⟩, rfl⟩ := hsurj z
    rw [Matrix.toLin'_one, LinearMap.id_apply, Matrix.toLin'_apply]
    rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec,
      ← Matrix.mulVec_mulVec, show LinearMap.toMatrix' πl *ᵥ Φ (u, a, b) = πl (Φ (u, a, b)) from
        (Matrix.toLin'_apply _ _).symm.trans (by rw [Matrix.toLin'_toMatrix']), hπ]
    have e1 : (W.J *ᵥ fun i => σ (H'.y i)) ⬝ᵥ Φ (u, a, b) = a := by
      rw [dotProduct_comm, ← form, hΦ, hlin, (horth u).2, hxy, hyy]; ring
    have e2 : (W.J *ᵥ fun i => σ (H'.x i)) ⬝ᵥ Φ (u, a, b) = -b := by
      rw [dotProduct_comm, ← form, hΦ, hlin, (horth u).1, hxx, hyx]; ring
    rw [e1, e2, hΦ]
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
    ring
  · rw [← hgram, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]

    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hJdet : W.J.det ≠ 0 := by
      intro h0
      apply det_ne_zero_of_hasSig _ (hW.sig w)
      rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]
    have hJinj : Function.Injective W.J.mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hJdet))
    have hσinj : Function.Injective σ := fun a b h => by rw [← hinv a, ← hinv b, h]
    have hιinj : Function.Injective H'.ι.mulVec := by
      intro u v h
      have := hinj (a₁ := (u, 0, 0)) (a₂ := (v, 0, 0)) (by rw [hΦ, hΦ]; simpa using h)
      simpa using congrArg Prod.fst this
    intro v v' hvv
    rw [← sub_eq_zero]
    have h0 : (H'.ιᵀ * W.J * H'.ι.map σ) *ᵥ (v - v') = 0 := by rw [Matrix.mulVec_sub, hvv, sub_self]
    set c : Fin d₁ → E := fun j => σ ((v - v') j) with hcdef
    have hc : H'.ι.map σ *ᵥ (v - v') = fun i => σ ((H'.ι *ᵥ c) i) := by
      ext i; simp [Matrix.mulVec, dotProduct, map_sum, c, hinv]
    have h1 : ∀ u, form σ W.J (H'.ι *ᵥ u) (H'.ι *ᵥ c) = 0 := by
      intro u
      have : form σ W.J (H'.ι *ᵥ u) (H'.ι *ᵥ c) = u ⬝ᵥ ((H'.ιᵀ * W.J * H'.ι.map σ) *ᵥ (v - v')) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hc, Matrix.dotProduct_mulVec,
          Matrix.vecMul_transpose, form]
      rw [this, h0, dotProduct_zero]
    have h2 : ∀ z, form σ W.J z (H'.ι *ᵥ c) = 0 := by
      intro z
      obtain ⟨⟨u, a, b⟩, rfl⟩ := hsurj z
      rw [hΦ, hlin, h1, hxι, hyι]; ring
    have h3 : W.J *ᵥ (fun i => σ ((H'.ι *ᵥ c) i)) = 0 := by
      ext i
      have := h2 (Pi.single i 1)
      rw [form, single_dotProduct, one_mul] at this
      simpa using this
    have h4 : H'.ι *ᵥ c = 0 := by
      have := hJinj (h3.trans (Matrix.mulVec_zero _).symm)
      ext i
      exact hσinj ((congrFun this i).trans (map_zero σ).symm)
    have h5 : c = 0 := hιinj (h4.trans (Matrix.mulVec_zero _).symm)
    ext j
    have := congrFun h5 j
    simp only [c, Pi.zero_apply] at this
    simpa using hσinj (this.trans (map_zero σ).symm)

end GlobalTheory.PlaneFrame
