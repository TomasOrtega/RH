import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StIsotropicRank
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ShortIsotropic
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField
open scoped Matrix

namespace IsotropicRank

/- English proof (translation)
Establish `h1 : ∀ v ∈ S, ∀ y ∈ Submodule.span Em S, hermForm Em H v y = 0`. Introduce `v hv y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem w hw => exact hS v hv w hw`. Consider the case `zero => exact ShortIsotropic.hermForm_zero_right H v`.

Consider the case `add y y' _ _ h h' => rw [ShortIsotropic.hermForm_add_right, h, h', add_zero]`. Consider the case `smul c y _ h => rw [ShortIsotropic.hermForm_smul_right, h, mul_zero]`. Introduce `x hx y hy`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem v hv => exact h1 v hv y hy`.

Consider the case `zero => exact ShortIsotropic.hermForm_zero_left H y`. Consider the case `add x x' _ _ h h' => rw [ShortIsotropic.hermForm_add_left, h, h', add_zero]`. Consider the case `smul c x _ h => rw [ShortIsotropic.hermForm_smul_left, h, mul_zero]`.
-/
theorem hermForm_span_eq_zero {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {N : ℕ}
    (H : Matrix (Fin N) (Fin N) Em) (S : Set (Fin N → Em)) (hS : ∀ v ∈ S, ∀ w ∈ S, hermForm Em H v w = 0) :
    ∀ x ∈ Submodule.span Em S, ∀ y ∈ Submodule.span Em S, hermForm Em H x y = 0 := by
  have h1 : ∀ v ∈ S, ∀ y ∈ Submodule.span Em S, hermForm Em H v y = 0 := by
    intro v hv y hy
    induction hy using Submodule.span_induction with
    | mem w hw => exact hS v hv w hw
    | zero => exact ShortIsotropic.hermForm_zero_right H v
    | add y y' _ _ h h' => rw [ShortIsotropic.hermForm_add_right, h, h', add_zero]
    | smul c y _ h => rw [ShortIsotropic.hermForm_smul_right, h, mul_zero]
  intro x hx y hy
  induction hx using Submodule.span_induction with
  | mem v hv => exact h1 v hv y hy
  | zero => exact ShortIsotropic.hermForm_zero_left H y
  | add x x' _ _ h h' => rw [ShortIsotropic.hermForm_add_left, h, h', add_zero]
  | smul c x _ h => rw [ShortIsotropic.hermForm_smul_left, h, mul_zero]

/- English proof (translation)
Take `⟨σ⟩ : Nonempty (Em →+* ℂ)` from `inferInstance`. Distinguish the cases in `h : ∃ τ, A.emb τ = σ`. Conclude with `⟨h.choose⟩`. Take `⟨τ, _⟩` from `not_not.mp (mt (A.cmType σ).mpr h)`. Conclude with `⟨τ⟩`.
-/
theorem nonempty_cmType {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}
    (A : HermDatum Em Ψ N j) : Nonempty Ψ := by
  obtain ⟨σ⟩ : Nonempty (Em →+* ℂ) := inferInstance
  by_cases h : ∃ τ, A.emb τ = σ
  · exact ⟨h.choose⟩
  · obtain ⟨τ, _⟩ := not_not.mp (mt (A.cmType σ).mpr h)
    exact ⟨τ⟩

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin M) (LinearMap.ker_eq_bot.mpr hM)`. Establish `hL : LinearMap.toMatrix' g * M = 1`. Establish `hM' : LinearMap.toMatrix' (Matrix.mulVecLin M) = M`. Rewrite using `[← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']`. Rewrite using `[← hM', ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]`.

Establish `hLσ : (LinearMap.toMatrix' g).map σ * M.map σ = 1`. Rewrite using `[← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]`. Introduce `c d hcd`. Establish `h` using `congrArg ((LinearMap.toMatrix' g).map σ).mulVec hcd`. Simplify `h` using `only [Matrix.mulVec_mulVec, hLσ, Matrix.one_mulVec]`.
-/
theorem mulVec_map_injective {K L : Type*} [Field K] [Field L] {n r : ℕ} (σ : K →+* L)
    (M : Matrix (Fin n) (Fin r) K) (hM : Function.Injective M.mulVec) : Function.Injective (M.map σ).mulVec := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin M)
    (LinearMap.ker_eq_bot.mpr hM)
  have hL : LinearMap.toMatrix' g * M = 1 := by
    have hM' : LinearMap.toMatrix' (Matrix.mulVecLin M) = M := by
      rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
    rw [← hM', ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hLσ : (LinearMap.toMatrix' g).map σ * M.map σ = 1 := by
    rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero σ) (map_one σ)]
  intro c d hcd
  have h := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hcd
  simpa only [Matrix.mulVec_mulVec, hLσ, Matrix.one_mulVec] using h

/- English proof (translation)
Introduce `Em _ _ _ Ψ _ N j A S hS`. Take `⟨τ⟩` from `nonempty_cmType A`. Take `⟨P, hPu, hP⟩` from `A.signature τ`. Use `set U := Submodule.span Em S`. Use `set r := Module.finrank Em U`.

Set `b` to `Module.finBasis Em U`. Set `M : Matrix (Fin N) (Fin r) Em` to `Matrix.of fun i a => (b a : Fin N → Em) i`. Establish `hMv : ∀ c, M *ᵥ c = ∑ a, c a • (b a : Fin N → Em)`. Introduce `c`. Use extensionality with `i`.

Simplify using `[M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Establish `hli : LinearIndependent Em fun a => (b a : Fin N → Em)` using `b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)`. Establish `hM : Function.Injective M.mulVec`. Introduce `c d hcd`. Establish `h0 : ∑ a, (c - d) a • (b a : Fin N → Em) = 0`.

Rewrite using `[← hMv, Matrix.mulVec_sub]`. Conclude with `sub_eq_zero.mpr hcd`. Use function extensionality and compare the values at `a`. Conclude with `sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 a)`. Establish `hz : ∀ a a', hermForm Em A.H (b a) (b a') = 0` using `fun a a' => hermForm_span_eq_zero A.H S hS _ (b a).2 _ (b a').2`.

Use `set Mτ := M.map (A.emb τ)`. Use `set Hτ := A.H.map (A.emb τ)`. Establish `hG : Mτᴴ * Hτ * Mτ = 0`. Use extensionality with `a a'`. Establish `h` using `ShortIsotropic.emb_hermForm (A.emb τ) A.H (b a) (b a')`.

Rewrite `h` using `[hz a a', map_zero]`. Rewrite using `[Matrix.zero_apply, h]`. Simplify using `only [Mτ, Hτ, M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Establish `hq : ∀ c, star (Mτ *ᵥ c) ⬝ᵥ (Hτ *ᵥ (Mτ *ᵥ c)) = 0`. Introduce `c`. Rewrite using `[Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG, Matrix.zero_mulVec, dotProduct_zero]`. Set `g : Fin (N - j) → Fin N` to `fun k => ⟨j + k, by omega⟩`. Set `f : (Fin r → ℂ) →ₗ[ℂ] (Fin (N - j) → ℂ)` to `LinearMap.funLeft ℂ ℂ g ∘ₗ Matrix.mulVecLin (P⁻¹ * Mτ)`.

Establish `hinj : Function.Injective f`. Use `(injective_iff_map_eq_zero f).mpr fun c hc => ?_` and prove the remaining obligations. Use `set y := P⁻¹ *ᵥ (Mτ *ᵥ c)`. Establish `hy0 : ∀ a : Fin N, j ≤ (a : ℕ) → y a = 0`. Introduce `a ha`.

Establish `h` using `congrFun hc ⟨a - j, by omega⟩`. Simplify using `only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, Pi.zero_apply] at h`. Establish `hg : g ⟨a - j, by omega⟩ = a` using `Fin.ext (by simp only [g]; omega)`. Rewrite `h` using `[hg]`. Then use the resulting hypothesis. Establish `hw` using `ShortIsotropic.form_witt hP (Mτ *ᵥ c) (Mτ *ᵥ c)`.

Rewrite `hw` using `[hq c]`. Establish `hsum : ∑ a, Complex.normSq (y a) = 0`. Establish `h` using `congrArg Complex.re hw.symm`. Simplify using `only [signMat, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum, Complex.zero_re] at h`. Rewrite using `[← h]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : (a : ℕ) < j`. Simplify using `only [ha, if_true, one_mul, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `h0 : ((P⁻¹ * Mτ) *ᵥ c) a = 0`.

Rewrite using `[← Matrix.mulVec_mulVec]`. Conclude with `hy0 a (by omega)`. Establish `h1 : y a = 0` using `hy0 a (by omega)`. Simplify using `[ha, h0, h1]`. Establish `hy : y = 0`.

Use function extensionality and compare the values at `a`. Establish `h` using `(Finset.sum_eq_zero_iff_of_nonneg fun a _ => Complex.normSq_nonneg (y a)).mp hsum a (Finset.mem_univ a)`. Conclude with `Complex.normSq_eq_zero.mp h`. Establish `hMc : Mτ *ᵥ c = 0`. Establish `: Mτ *ᵥ c = P *ᵥ y`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]`. Rewrite using `[this, hy, Matrix.mulVec_zero]`. Conclude with `mulVec_map_injective (A.emb τ) M hM (hMc.trans (Matrix.mulVec_zero Mτ).symm)`. Use `LinearMap.finrank_le_finrank_of_injective hinj` as an intermediate fact. Simplify `this` using `only [Module.finrank_fin_fun]`.
-/
theorem proof : IsotropicRank.Statement := by
  intro Em _ _ _ Ψ _ N j A S hS
  obtain ⟨τ⟩ := nonempty_cmType A
  obtain ⟨P, hPu, hP⟩ := A.signature τ
  set U := Submodule.span Em S
  set r := Module.finrank Em U
  let b := Module.finBasis Em U
  let M : Matrix (Fin N) (Fin r) Em := Matrix.of fun i a => (b a : Fin N → Em) i
  have hMv : ∀ c, M *ᵥ c = ∑ a, c a • (b a : Fin N → Em) := by
    intro c
    ext i
    simp [M, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hli : LinearIndependent Em fun a => (b a : Fin N → Em) :=
    b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hM : Function.Injective M.mulVec := by
    intro c d hcd
    have h0 : ∑ a, (c - d) a • (b a : Fin N → Em) = 0 := by
      rw [← hMv, Matrix.mulVec_sub]
      exact sub_eq_zero.mpr hcd
    funext a
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ h0 a)
  have hz : ∀ a a', hermForm Em A.H (b a) (b a') = 0 := fun a a' =>
    hermForm_span_eq_zero A.H S hS _ (b a).2 _ (b a').2
  set Mτ := M.map (A.emb τ)
  set Hτ := A.H.map (A.emb τ)
  have hG : Mτᴴ * Hτ * Mτ = 0 := by
    ext a a'
    have h := ShortIsotropic.emb_hermForm (A.emb τ) A.H (b a) (b a')
    rw [hz a a', map_zero] at h
    rw [Matrix.zero_apply, h]
    simp only [Mτ, Hτ, M, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.of_apply,
      dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hq : ∀ c, star (Mτ *ᵥ c) ⬝ᵥ (Hτ *ᵥ (Mτ *ᵥ c)) = 0 := by
    intro c
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      hG, Matrix.zero_mulVec, dotProduct_zero]
  let g : Fin (N - j) → Fin N := fun k => ⟨j + k, by omega⟩
  let f : (Fin r → ℂ) →ₗ[ℂ] (Fin (N - j) → ℂ) := LinearMap.funLeft ℂ ℂ g ∘ₗ Matrix.mulVecLin (P⁻¹ * Mτ)
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr fun c hc => ?_
    set y := P⁻¹ *ᵥ (Mτ *ᵥ c)
    have hy0 : ∀ a : Fin N, j ≤ (a : ℕ) → y a = 0 := by
      intro a ha
      have h := congrFun hc ⟨a - j, by omega⟩
      simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.funLeft_apply, Matrix.mulVecLin_apply,
        ← Matrix.mulVec_mulVec, Pi.zero_apply] at h
      have hg : g ⟨a - j, by omega⟩ = a := Fin.ext (by simp only [g]; omega)
      rwa [hg] at h
    have hw := ShortIsotropic.form_witt hP (Mτ *ᵥ c) (Mτ *ᵥ c)
    rw [hq c] at hw
    have hsum : ∑ a, Complex.normSq (y a) = 0 := by
      have h := congrArg Complex.re hw.symm
      simp only [signMat, Matrix.mulVec_diagonal, dotProduct, Pi.star_apply, Complex.re_sum,
        Complex.zero_re] at h
      rw [← h]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases ha : (a : ℕ) < j
      · simp only [ha, if_true, one_mul, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im,
          Complex.normSq_apply]
        ring
      · have h0 : ((P⁻¹ * Mτ) *ᵥ c) a = 0 := by
          rw [← Matrix.mulVec_mulVec]
          exact hy0 a (by omega)
        have h1 : y a = 0 := hy0 a (by omega)
        simp [ha, h0, h1]
    have hy : y = 0 := by
      funext a
      have h := (Finset.sum_eq_zero_iff_of_nonneg fun a _ => Complex.normSq_nonneg (y a)).mp hsum a
        (Finset.mem_univ a)
      exact Complex.normSq_eq_zero.mp h
    have hMc : Mτ *ᵥ c = 0 := by
      have : Mτ *ᵥ c = P *ᵥ y := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hPu, Matrix.one_mulVec]
      rw [this, hy, Matrix.mulVec_zero]
    exact mulVec_map_injective (A.emb τ) M hM (hMc.trans (Matrix.mulVec_zero Mτ).symm)
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fin_fun] using this

end IsotropicRank

end GroundTheory.Heights₂.Heights.NineStatements
