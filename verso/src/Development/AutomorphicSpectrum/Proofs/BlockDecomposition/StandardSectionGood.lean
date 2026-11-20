import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.IsEpCont
import GroundTheory.AutomorphicForms.ReductionIwasawa

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped NumberField.AdeleRing

open PositivityTheory.RgEis GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CompanionTheory.StdGoodAd

section Unitary

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/- English proof (translation)
Set `f : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n)` to `Matrix.toEuclideanLin Uᵀ`. Establish `hf : ∀ x : EuclideanSpace 𝕜 (Fin n), (f x).ofLp = x.ofLp ᵥ* U` using `fun x => by`. Simplify using `[f, Matrix.toEuclideanLin_apply, Matrix.mulVec_transpose]`. Establish `hn : ∀ x, ‖f x‖ = ‖x‖` using `fun x => by`. Use `h x.ofLp` as an intermediate fact.

Rewrite using `[EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, hf]`. Simplify `this` using `[euclidNorm]`. Establish `hi` using `(LinearMap.norm_map_iff_inner_map_map f).1 hn`. Rewrite using `[mem_unitaryGroup_iff]`. Use extensionality with `j i`.

Use `hi (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)` as an intermediate fact. Rewrite `this` using `[EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct, hf, hf]`. Simplify `this` using `[Matrix.mul_apply, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm]`.
-/
theorem mem_unitary_of_euclid (U : Matrix (Fin n) (Fin n) 𝕜)
    (h : ∀ z : Fin n → 𝕜, euclidNorm (z ᵥ* U) = euclidNorm z) : U ∈ unitaryGroup (Fin n) 𝕜 := by
  classical
  let f : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n) := Matrix.toEuclideanLin Uᵀ
  have hf : ∀ x : EuclideanSpace 𝕜 (Fin n), (f x).ofLp = x.ofLp ᵥ* U := fun x => by
    simp [f, Matrix.toEuclideanLin_apply, Matrix.mulVec_transpose]
  have hn : ∀ x, ‖f x‖ = ‖x‖ := fun x => by
    have := h x.ofLp
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, hf]
    simpa [euclidNorm] using this
  have hi := (LinearMap.norm_map_iff_inner_map_map f).1 hn
  rw [mem_unitaryGroup_iff]
  ext j i
  have := hi (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct, hf, hf] at this
  simpa [Matrix.mul_apply, dotProduct, Matrix.one_apply, Pi.single_apply, eq_comm] using this

end Unitary

section Transport

variable {E 𝕜 : Type*} [NormedField E] [RCLike 𝕜] {n : ℕ}

/- English proof (translation)
Use `mem_unitary_of_euclid _ fun z => ?_` and prove the remaining obligations. Establish `hφ' : ∀ x, ‖φ.symm x‖ = ‖x‖` using `fun x => by rw [← hφ, RingEquiv.apply_symm_apply]`. Establish `e1 : z ᵥ* k.map φ = fun j => φ.toRingHom (((fun i => φ.symm (z i)) ᵥ* k) j)`. Use extensionality with `j`. Simplify using `[vecMul, dotProduct, map_sum, map_mul]`.

Rewrite using `[e1, euclidNorm_map φ.toRingHom hφ, hk]`. Conclude with `euclidNorm_map φ.symm.toRingHom hφ' z`.
-/
theorem map_mem_unitary_of_ringEquiv (φ : E ≃+* 𝕜) (hφ : ∀ x, ‖φ x‖ = ‖x‖)
    (k : Matrix (Fin n) (Fin n) E) (hk : ∀ y : Fin n → E, euclidNorm (y ᵥ* k) = euclidNorm y) :
    k.map φ ∈ unitaryGroup (Fin n) 𝕜 := by
  refine mem_unitary_of_euclid _ fun z => ?_
  have hφ' : ∀ x, ‖φ.symm x‖ = ‖x‖ := fun x => by rw [← hφ, RingEquiv.apply_symm_apply]
  have e1 : z ᵥ* k.map φ = fun j => φ.toRingHom (((fun i => φ.symm (z i)) ᵥ* k) j) := by
    ext j
    simp [vecMul, dotProduct, map_sum, map_mul]
  rw [e1, euclidNorm_map φ.toRingHom hφ, hk]
  exact euclidNorm_map φ.symm.toRingHom hφ' z

/- English proof (translation)
Rewrite `hU`, the goal using `[mem_unitaryGroup_iff]`. Establish `hs : star (U.map (algebraMap ℝ ℂ)) = (star U).map (algebraMap ℝ ℂ)`. Use extensionality with `i j`. Simplify using `[Matrix.star_apply]`. Rewrite using `[hs, ← Matrix.map_mul, hU, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem map_ofReal_mem_unitary {U : Matrix (Fin n) (Fin n) ℝ} (hU : U ∈ unitaryGroup (Fin n) ℝ) :
    U.map (algebraMap ℝ ℂ) ∈ unitaryGroup (Fin n) ℂ := by
  rw [mem_unitaryGroup_iff] at hU ⊢
  have hs : star (U.map (algebraMap ℝ ℂ)) = (star U).map (algebraMap ℝ ℂ) := by
    ext i j
    simp [Matrix.star_apply]
  rw [hs, ← Matrix.map_mul, hU, Matrix.map_one _ (map_zero _) (map_one _)]

end Transport

section Place

variable {K : Type*} [Field K] {n : ℕ}

/- English proof (translation)
Distinguish the cases in `hw : w.IsReal`. Establish `h` using `map_mem_unitary_of_ringEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x) _ hk`. Establish `h2` using `map_ofReal_mem_unitary h`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Simplify using `[InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]`. Establish `hc` using `InfinitePlace.not_isReal_iff_isComplex.1 hw`. Establish `h` using `map_mem_unitary_of_ringEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc) (fun x => (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x) _ hk`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `i j`.

Simplify using `[InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]`.
-/
theorem map_mem_unitary_of_mem_archCompact (w : InfinitePlace K) {k : GL (Fin n) w.Completion}
    (hk : k ∈ archCompact w) :
    (k : Matrix (Fin n) (Fin n) w.Completion).map (InfinitePlace.Completion.extensionEmbedding w) ∈
      unitaryGroup (Fin n) ℂ := by
  by_cases hw : w.IsReal
  · have h := map_mem_unitary_of_ringEquiv (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
      (fun x => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) x) _ hk
    have h2 := map_ofReal_mem_unitary h
    convert h2 using 1
    ext i j
    simp [InfinitePlace.Completion.ringEquivRealOfIsReal_apply,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.1 hw
    have h := map_mem_unitary_of_ringEquiv (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc)
      (fun x => (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) x) _ hk
    convert h using 1
    ext i j
    simp [InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply]

/- English proof (translation)
Introduce `y`. Establish `hφ : ∀ x, ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖` using `fun x => (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x`. Rewrite using `[← euclidNorm_map (InfinitePlace.Completion.extensionEmbedding w) hφ, ← euclidNorm_map (InfinitePlace.Completion.extensionEmbedding w) hφ y]`. Establish `e1 : (fun j => InfinitePlace.Completion.extensionEmbedding w ((y ᵥ* (k : Matrix (Fin n) (Fin n) w.Completion)) j)) = (fun i => InfinitePlace.Completion.extensionEmbedding w (y i)) ᵥ* (k : Matrix (Fin n) (Fin n) w.Completion).map (InfinitePlace.Completion.extensionEmbedding w)`. Use extensionality with `j`.

Simplify using `[vecMul, dotProduct, map_sum, map_mul]`. Rewrite using `[e1, euclidNorm_vecMul_unitary hk]`.
-/
theorem mem_archCompact_of_map_mem_unitary (w : InfinitePlace K) {k : GL (Fin n) w.Completion}
    (hk : (k : Matrix (Fin n) (Fin n) w.Completion).map
      (InfinitePlace.Completion.extensionEmbedding w) ∈ unitaryGroup (Fin n) ℂ) :
    k ∈ archCompact w := by
  intro y
  have hφ : ∀ x, ‖InfinitePlace.Completion.extensionEmbedding w x‖ = ‖x‖ := fun x =>
    (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
  rw [← euclidNorm_map (InfinitePlace.Completion.extensionEmbedding w) hφ,
    ← euclidNorm_map (InfinitePlace.Completion.extensionEmbedding w) hφ y]
  have e1 : (fun j => InfinitePlace.Completion.extensionEmbedding w
      ((y ᵥ* (k : Matrix (Fin n) (Fin n) w.Completion)) j)) =
      (fun i => InfinitePlace.Completion.extensionEmbedding w (y i)) ᵥ*
        (k : Matrix (Fin n) (Fin n) w.Completion).map
          (InfinitePlace.Completion.extensionEmbedding w) := by
    ext j
    simp [vecMul, dotProduct, map_sum, map_mul]
  rw [e1, euclidNorm_vecMul_unitary hk]

end Place

section Global

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
Simplify using `only [intAd, Subring.mem_iInf, Subring.mem_comap]`. Both sides reduce to the same expression.
-/
theorem mem_intAd_iff {a : 𝔸[K]} :
    a ∈ intAd K ↔ ∀ v : HeightOneSpectrum (𝓞 K), a.2 v ∈ v.adicCompletionIntegers K := by
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_kGL_iff {E R : Type} [Field E] [CommRing R] (A : Ad E R) {ι : Type} [Fintype ι]
    [DecidableEq ι] {k : GL ι R} :
    k ∈ A.kGL ι ↔ (∀ r c, (k : Matrix ι ι R) r c ∈ A.O ∧ ((k⁻¹ : GL ι R) : Matrix ι ι R) r c ∈ A.O) ∧
      ∀ w, (k : Matrix ι ι R).map (A.φ w) ∈ Matrix.unitaryGroup ι ℂ :=
  Iff.rfl

/- English proof (translation)
Rewrite using `[mem_kGL_iff, mem_maxCompact]`. Establish `hw : ∀ w : InfinitePlace K, (k : Matrix (Fin n) (Fin n) 𝔸[K]).map ((adStd K).φ w) = ((infAt w k : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion).map (InfinitePlace.Completion.extensionEmbedding w)` using `fun w => by`. Use extensionality with `i j`. Both sides reduce to the same expression. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun w => mem_archCompact_of_map_mem_unitary w (by rw [← hw]; exact h2 w), fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[GLnLocal.mem_integralGL_iff]`. Use `⟨fun i j => (GroundTheory.Global.mem_valuationInteger_iff _ _).2 (mem_intAd_iff.1 (h1 i j).1 v), fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[← finAt_inv]`.

Conclude with `(GroundTheory.Global.mem_valuationInteger_iff _ _).2 (mem_intAd_iff.1 (h1 i j).2 v)`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun r c => ⟨mem_intAd_iff.2 fun v => ?_, mem_intAd_iff.2 fun v => ?_⟩, fun w : InfinitePlace K => ?_⟩` and prove the remaining obligations. Conclude with `(GroundTheory.Global.mem_valuationInteger_iff _ _).1 (((GLnLocal.mem_integralGL_iff _ _).1 (h2 v)).1 r c)`. Use `((GLnLocal.mem_integralGL_iff _ _).1 (h2 v)).2 r c` as an intermediate fact.

Rewrite `this` using `[← finAt_inv]`. Conclude with `(GroundTheory.Global.mem_valuationInteger_iff _ _).1 this`. Rewrite using `[hw w]`. Conclude with `map_mem_unitary_of_mem_archCompact w (h1 w)`.
-/
theorem mem_kGL_fin_iff {k : GL (Fin n) 𝔸[K]} : k ∈ (adStd K).kGL (Fin n) ↔ k ∈ maxCompact := by
  rw [mem_kGL_iff, mem_maxCompact]
  have hw : ∀ w : InfinitePlace K, (k : Matrix (Fin n) (Fin n) 𝔸[K]).map ((adStd K).φ w) =
      ((infAt w k : GL (Fin n) w.Completion) : Matrix (Fin n) (Fin n) w.Completion).map
        (InfinitePlace.Completion.extensionEmbedding w) := fun w => by
    ext i j
    rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun w => mem_archCompact_of_map_mem_unitary w (by rw [← hw]; exact h2 w), fun v => ?_⟩
    rw [GLnLocal.mem_integralGL_iff]
    refine ⟨fun i j => (GroundTheory.Global.mem_valuationInteger_iff _ _).2 (mem_intAd_iff.1 (h1 i j).1 v), fun i j => ?_⟩
    rw [← finAt_inv]
    exact (GroundTheory.Global.mem_valuationInteger_iff _ _).2 (mem_intAd_iff.1 (h1 i j).2 v)
  · rintro ⟨h1, h2⟩
    refine ⟨fun r c => ⟨mem_intAd_iff.2 fun v => ?_, mem_intAd_iff.2 fun v => ?_⟩,
      fun w : InfinitePlace K => ?_⟩
    · exact (GroundTheory.Global.mem_valuationInteger_iff _ _).1 (((GLnLocal.mem_integralGL_iff _ _).1 (h2 v)).1 r c)
    · have := ((GLnLocal.mem_integralGL_iff _ _).1 (h2 v)).2 r c
      rw [← finAt_inv] at this
      exact (GroundTheory.Global.mem_valuationInteger_iff _ _).1 this
    · rw [hw w]
      exact map_mem_unitary_of_mem_archCompact w (h1 w)

end Global

section Reindex

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def re (R : Type) [CommRing R] (e : ι ≃ κ) : GL ι R ≃* GL κ R :=
  Units.mapEquiv (Matrix.reindexAlgEquiv R R e).toMulEquiv

variable {R : Type} [CommRing R]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem re_val (e : ι ≃ κ) (g : GL ι R) :
    ((re R e g : GL κ R) : Matrix κ κ R) = (g : Matrix ι ι R).submatrix e.symm e.symm := rfl

/- English proof (translation)
Rewrite using `[← map_inv, re_val]`.
-/
theorem re_inv_val (e : ι ≃ κ) (g : GL ι R) :
    (((re R e g)⁻¹ : GL κ R) : Matrix κ κ R) =
      ((g⁻¹ : GL ι R) : Matrix ι ι R).submatrix e.symm e.symm := by
  rw [← map_inv, re_val]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[re_val]`.
-/
theorem re_symm_re (e : ι ≃ κ) (g : GL ι R) : re R e.symm (re R e g) = g := by
  ext i j
  simp [re_val]

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Establish `: (Units.val ∘ (re R e)) = fun g : GL ι R => (g : Matrix ι ι R).submatrix e.symm e.symm` using `rfl`. Rewrite using `[this]`. Conclude with `Units.continuous_val.matrix_submatrix _ _`. Establish `: (fun g : GL ι R => (((re R e g)⁻¹ : GL κ R) : Matrix κ κ R)) = fun g : GL ι R => ((g⁻¹ : GL ι R) : Matrix ι ι R).submatrix e.symm e.symm`.

Use function extensionality and compare the values at `fun g => re_inv_val e g`. Rewrite using `[this]`. Conclude with `(Units.continuous_iff.1 (continuous_id (X := GL ι R))).2.matrix_submatrix _ _`.
-/
theorem continuous_re [TopologicalSpace R] [IsTopologicalRing R] (e : ι ≃ κ) :
    Continuous (re R e) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have : (Units.val ∘ (re R e)) = fun g : GL ι R => (g : Matrix ι ι R).submatrix e.symm e.symm := rfl
    rw [this]
    exact Units.continuous_val.matrix_submatrix _ _
  · have : (fun g : GL ι R => (((re R e g)⁻¹ : GL κ R) : Matrix κ κ R)) =
        fun g : GL ι R => ((g⁻¹ : GL ι R) : Matrix ι ι R).submatrix e.symm e.symm :=
      funext fun g => re_inv_val e g
    rw [this]
    exact (Units.continuous_iff.1 (continuous_id (X := GL ι R))).2.matrix_submatrix _ _

/- English proof (translation)
Rewrite `hg`, the goal using `[mem_kGL_iff]`. Use `⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[re_val]`. Conclude with `(hg.1 _ _).1`. Rewrite using `[re_inv_val]`.

Conclude with `(hg.1 _ _).2`. Establish `h` using `hg.2 w`. Rewrite `h`, the goal using `[mem_unitaryGroup_iff]`. Establish `e1 : ((re R e g : GL κ R) : Matrix κ κ R).map (A.φ w) = ((g : Matrix ι ι R).map (A.φ w)).submatrix e.symm e.symm` using `rfl`. Rewrite using `[e1, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, h, Matrix.submatrix_one_equiv]`.
-/
theorem re_mem_kGL {E : Type} [Field E] (A : Ad E R) (e : ι ≃ κ) {g : GL ι R}
    (hg : g ∈ A.kGL ι) : re R e g ∈ A.kGL κ := by
  rw [mem_kGL_iff] at hg ⊢
  refine ⟨fun r c => ⟨?_, ?_⟩, fun w => ?_⟩
  · rw [re_val]; exact (hg.1 _ _).1
  · rw [re_inv_val]; exact (hg.1 _ _).2
  · have h := hg.2 w
    rw [mem_unitaryGroup_iff] at h ⊢
    have e1 : ((re R e g : GL κ R) : Matrix κ κ R).map (A.φ w) =
        ((g : Matrix ι ι R).map (A.φ w)).submatrix e.symm e.symm := rfl
    rw [e1, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose, h, Matrix.submatrix_one_equiv]

/- English proof (translation)
Set `e : ι ≃ Fin (Fintype.card {x // x ∈ s} + Fintype.card {x // x ∉ s})` to `(Equiv.sumCompl (· ∈ s)).symm.trans ((Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finSumFinEquiv)`. Use `⟨_, e, fun r c hr hc => ?_⟩` and prove the remaining obligations. Simplify using `only [e, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hc, Equiv.sumCompl_symm_apply_of_neg hr, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_equiv_first (s : Set ι) :
    ∃ (n : ℕ) (e : ι ≃ Fin n), ∀ r c, r ∉ s → c ∈ s → e c < e r := by
  classical
  let e : ι ≃ Fin (Fintype.card {x // x ∈ s} + Fintype.card {x // x ∉ s}) :=
    (Equiv.sumCompl (· ∈ s)).symm.trans
      ((Equiv.sumCongr (Fintype.equivFin _) (Fintype.equivFin _)).trans finSumFinEquiv)
  refine ⟨_, e, fun r c hr hc => ?_⟩
  simp only [e, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hc,
    Equiv.sumCompl_symm_apply_of_neg hr, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_castAdd,
    Fin.val_natAdd]
  omega

end Reindex

section Main

variable (K : Type) [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Set `e` to `Fintype.equivFin ι`. Establish `h : ((adStd K).kGL ι : Set (GL ι 𝔸[K])) = re 𝔸[K] e.symm '' (maxCompact (K` using `K) (n := Fintype.card ι) : Set (AdelicGLn.AdelicGL K (Fintype.card ι))) := by`. Use extensionality with `g`. Prove the components needed by the constructor for the conclusion. Introduce `hg`.

Conclude with `⟨re 𝔸[K] e g, mem_kGL_fin_iff.1 (re_mem_kGL _ e hg), re_symm_re e g⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `re_mem_kGL _ e.symm (mem_kGL_fin_iff.2 hx)`. Rewrite using `[h]`. Conclude with `isCompact_maxCompact.image (continuous_re e.symm)`.
-/
theorem isCompact_kGL : IsCompact ((adStd K).kGL ι : Set (GL ι 𝔸[K])) := by
  let e := Fintype.equivFin ι
  have h : ((adStd K).kGL ι : Set (GL ι 𝔸[K])) =
      re 𝔸[K] e.symm '' (maxCompact (K := K) (n := Fintype.card ι) :
        Set (AdelicGLn.AdelicGL K (Fintype.card ι))) := by
    ext g
    constructor
    · intro hg
      exact ⟨re 𝔸[K] e g, mem_kGL_fin_iff.1 (re_mem_kGL _ e hg), re_symm_re e g⟩
    · rintro ⟨x, hx, rfl⟩
      exact re_mem_kGL _ e.symm (mem_kGL_fin_iff.2 hx)
  rw [h]
  exact isCompact_maxCompact.image (continuous_re e.symm)

/- English proof (translation)
Introduce `g`. Take `⟨n, e, he⟩` from `exists_equiv_first s`. Take `⟨b, hb, κ, hκ, hg⟩` from `exists_adelicBorel_mul_maxCompact (K := K) (re 𝔸[K] e g)`. Use `⟨re 𝔸[K] e.symm b, fun r hr c hc => ⟨?_, ?_⟩, re 𝔸[K] e.symm κ, re_mem_kGL _ e.symm (mem_kGL_fin_iff.2 hκ), ?_⟩` and prove the remaining obligations. Rewrite using `[re_val]`.

Conclude with `hb (he r c hr hc)`. Rewrite using `[re_inv_val]`. Conclude with `(adelicBorel.inv_mem hb) (he r c hr hc)`. Rewrite using `[← map_mul, ← hg, re_symm_re]`.
-/
theorem iwa_stab (s : Set ι) : Iwa (stab 𝔸[K] s) ((adStd K).kGL ι) := by
  intro g
  obtain ⟨n, e, he⟩ := exists_equiv_first s
  obtain ⟨b, hb, κ, hκ, hg⟩ := exists_adelicBorel_mul_maxCompact (K := K) (re 𝔸[K] e g)
  refine ⟨re 𝔸[K] e.symm b, fun r hr c hc => ⟨?_, ?_⟩, re 𝔸[K] e.symm κ,
    re_mem_kGL _ e.symm (mem_kGL_fin_iff.2 hκ), ?_⟩
  · rw [re_val]
    exact hb (he r c hr hc)
  · rw [re_inv_val]
    exact (adelicBorel.inv_mem hb) (he r c hr hc)
  · rw [← map_mul, ← hg, re_symm_re]

end Main

/- English proof (translation)
Introduce `K _ _`. Use `{ iinj := AdeleRing.algebraMap_injective (𝓞 K) K lgmul := fun x y => ?_ lgcont := ?_ lgi := fun x => ?_ χcont := continuous_const χi := fun _ => rfl kcpt := fun ι _ _ => isCompact_kGL K iwa := fun ι _ _ s => iwa_stab K s }` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Real.log ((IdeleGroup.ideleModule K (x * y) : _) : ℝ) = _`. Rewrite using `[map_mul]`. Conclude with `Real.log_mul (IdeleGroup.ideleModule K x).2.ne' (IdeleGroup.ideleModule K y).2.ne'`.

Conclude with `(continuous_subtype_val.comp IdeleGroup.continuous_ideleModule).log fun x => (IdeleGroup.ideleModule K x).2.ne'`. Express the relevant statement in the definitionally equal form `Real.log ((IdeleGroup.ideleModule K (IdeleGroup.diagonal K x) : _) : ℝ) = 0`. Rewrite using `[IdeleGroup.ideleModule_diagonal]`. Simplify using the standard rewrite rules.
-/
theorem stdGood : PositivityTheory.RgEis.StdGood := by
  intro K _ _
  refine
    { iinj := AdeleRing.algebraMap_injective (𝓞 K) K
      lgmul := fun x y => ?_
      lgcont := ?_
      lgi := fun x => ?_
      χcont := continuous_const
      χi := fun _ => rfl
      kcpt := fun ι _ _ => isCompact_kGL K
      iwa := fun ι _ _ s => iwa_stab K s }
  · change Real.log ((IdeleGroup.ideleModule K (x * y) : _) : ℝ) = _
    rw [map_mul]
    exact Real.log_mul (IdeleGroup.ideleModule K x).2.ne' (IdeleGroup.ideleModule K y).2.ne'
  · exact (continuous_subtype_val.comp IdeleGroup.continuous_ideleModule).log
      fun x => (IdeleGroup.ideleModule K x).2.ne'
  · change Real.log ((IdeleGroup.ideleModule K (IdeleGroup.diagonal K x) : _) : ℝ) = 0
    rw [IdeleGroup.ideleModule_diagonal]
    simp

end GlobalTheory.CompanionTheory.StdGoodAd
