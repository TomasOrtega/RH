import Mathlib
import Formalism.LocalToGlobal.Divisibility.Frames
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder MatrixOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.DivisionValues

section SlopeTestRemainingChoices

/- English proof (translation)
Establish `hk : LinearMap.ker (Matrix.toLin' E) = ⊥`. Apply `LinearMap.ker_eq_bot.mpr` to reduce the goal to its premises. Introduce `x y hxy`. Apply `h` to reduce the goal to its premises. Simplify `hxy` using `[Matrix.toLin'_apply]`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' E) hk`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Establish `h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' E) = 1`. Rewrite using `[hg]`. Conclude with `LinearMap.toMatrix'_id`.

Rewrite `h1` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']`. Then use the resulting hypothesis.
-/
theorem exists_left_inv {F : Type} [Field F] {n d : ℕ} (E : Matrix (Fin n) (Fin d) F)
    (h : Function.Injective E.mulVec) : ∃ L : Matrix (Fin d) (Fin n) F, L * E = 1 := by
  have hk : LinearMap.ker (Matrix.toLin' E) = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply h
    simpa [Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' E) hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' E) = 1 := by
    rw [hg]; exact LinearMap.toMatrix'_id
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1

/- English proof (translation)
Introduce `x y hxy`. Use `congrArg L.mulVec hxy` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, h]`.
-/
theorem inj_of_left_inv {F : Type} [Field F] {n d : ℕ} {C : Matrix (Fin n) (Fin d) F}
    {L : Matrix (Fin d) (Fin n) F} (h : L * C = 1) : Function.Injective C.mulVec := by
  intro x y hxy
  have := congrArg L.mulVec hxy
  simpa [Matrix.mulVec_mulVec, h] using this

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem map_one' {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} :
    (1 : Matrix (Fin n) (Fin n) K).map σ = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/- English proof (translation)
Take `⟨L, hL⟩` from `exists_left_inv E h`. Apply `inj_of_left_inv (L := L.map σ)` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul, hL, map_one']`.
-/
theorem map_inj {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (h : Function.Injective E.mulVec) : Function.Injective (E.map σ).mulVec := by
  obtain ⟨L, hL⟩ := exists_left_inv E h
  apply inj_of_left_inv (L := L.map σ)
  rw [← Matrix.map_mul, hL, map_one']

/- English proof (translation)
Take `⟨R, hR⟩` from `Matrix.mulVec_surjective_iff_exists_right_inverse.mp h`. Apply `Matrix.mulVec_surjective_iff_exists_right_inverse.mpr` to reduce the goal to its premises. Conclude with `⟨R.map σ, by rw [← Matrix.map_mul, hR, map_one']⟩`.
-/
theorem map_surj {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (P : Matrix (Fin d) (Fin n) K)
    (h : Function.Surjective P.mulVec) : Function.Surjective (P.map σ).mulVec := by
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  apply Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
  exact ⟨R.map σ, by rw [← Matrix.map_mul, hR, map_one']⟩

/- English proof (translation)
Use extensionality with `a i`. Simplify using `only [Matrix.map_apply, Matrix.conjTranspose_apply]`. Rewrite using `[hE i a]`. Both sides reduce to the same expression.
-/
theorem map_conjTranspose' {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {n d : ℕ}
    (E : Matrix (Fin n) (Fin d) K) (hE : ∀ i a, σ (star (E i a)) = starRingEnd ℂ (σ (E i a))) :
    (Eᴴ).map σ = (E.map σ)ᴴ := by
  ext a i
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply]
  rw [hE i a]
  rfl

/- English proof (translation)
Establish `h1 : ∀ u : Fin n → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v u = fun i => v.embedding (u i)`. Introduce `u`. Use function extensionality and compare the values at `i`. Simplify using `[Formalism.HermitianLatticesTheory.vecAt]`. Simplify using `only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h1, metOf]`.

Rewrite using `[← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]`. Both sides reduce to the same expression.
-/
theorem majAt_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y =
      star (fun i => v.embedding (x i)) ⬝ᵥ (metOf (X v)).mulVec (fun i => v.embedding (y i)) := by
  have h1 : ∀ u : Fin n → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v u =
      fun i => v.embedding (u i) := by
    intro u; funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h1, metOf]
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct]`.
-/
theorem emb_mulVec {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} (E : Matrix (Fin n) (Fin d) K)
    (x : Fin d → K) : (fun i => σ (E.mulVec x i)) = (E.map σ).mulVec (fun a => σ (x a)) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `n A hA`. Establish `h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A` using `hA.posSemidef.nonneg`. Establish `hs : CFC.sqrt A * CFC.sqrt A = A` using `CFC.sqrt_mul_sqrt_self A h0`. Establish `hdet : IsUnit (CFC.sqrt A).det`. Establish `h1 : A.det ≠ 0` using `hA.det_pos.ne'`.

Rewrite `h1` using `[← hs, Matrix.det_mul]`. Conclude with `isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)`. Establish `hH : (CFC.sqrt A)ᴴ = CFC.sqrt A`. Use `(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq` as an intermediate fact. Rewrite `this` using `[Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis.

Use `⟨Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩` and prove the remaining obligations. Rewrite using `[metOf, frameOf, Matrix.nonsing_inv_nonsing_inv _ hdet, hH, hs]`.
-/
theorem frameOfSpec : FrameOfSpec := by
  intro n A hA
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ≤ A := hA.posSemidef.nonneg
  have hs : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h0
  have hdet : IsUnit (CFC.sqrt A).det := by
    have h1 : A.det ≠ 0 := hA.det_pos.ne'
    rw [← hs, Matrix.det_mul] at h1
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul h1)
  have hH : (CFC.sqrt A)ᴴ = CFC.sqrt A := by
    have := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)).star_eq
    rwa [Matrix.star_eq_conjTranspose] at this
  refine ⟨Matrix.isUnit_nonsing_inv_det _ hdet, ?_⟩
  rw [metOf, frameOf, Matrix.nonsing_inv_nonsing_inv _ hdet, hH, hs]

/- English proof (translation)
Introduce `n Y hY`. Establish `hpos : (metOf Y).PosDef`. Apply `Matrix.PosDef.conjTranspose_mul_self` to reduce the goal to its premises. Conclude with `Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ hY))`. Use `⟨hpos, ?_, (frameOfSpec n _ hpos).2⟩` and prove the remaining obligations.

Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[metOf, Matrix.mul_assoc, ← Matrix.mul_assoc Y⁻¹, Matrix.nonsing_inv_mul _ hY, Matrix.one_mul, ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hY, Matrix.conjTranspose_one]`.
-/
theorem metOfSpec : MetOfSpec := by
  intro n Y hY
  have hpos : (metOf Y).PosDef := by
    apply Matrix.PosDef.conjTranspose_mul_self
    exact Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det _ hY))
  refine ⟨hpos, ?_, (frameOfSpec n _ hpos).2⟩
  apply Matrix.inv_eq_right_inv
  rw [metOf, Matrix.mul_assoc, ← Matrix.mul_assoc Y⁻¹, Matrix.nonsing_inv_mul _ hY, Matrix.one_mul,
    ← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hY, Matrix.conjTranspose_one]

/- English proof (translation)
Introduce `n d A hA`. Use `⟨fun P hP => ?_, fun C hC => hA.conjTranspose_mul_mul_same hC⟩` and prove the remaining obligations. Take `⟨R, hR⟩` from `Matrix.mulVec_surjective_iff_exists_right_inverse.mp hP`. Establish `hinj : Function.Injective (Pᴴ).mulVec`. Apply `inj_of_left_inv (L := Rᴴ)` to reduce the goal to its premises.

Rewrite using `[← Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_one]`. Establish `h1` using `hA.inv.conjTranspose_mul_mul_same hinj`. Rewrite `h1` using `[Matrix.conjTranspose_conjTranspose]`. Conclude with `h1.inv`.
-/
theorem quotRestrPosDef : QuotRestrPosDef := by
  intro n d A hA
  refine ⟨fun P hP => ?_, fun C hC => hA.conjTranspose_mul_mul_same hC⟩
  obtain ⟨R, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hP
  have hinj : Function.Injective (Pᴴ).mulVec := by
    apply inj_of_left_inv (L := Rᴴ)
    rw [← Matrix.conjTranspose_mul, hR, Matrix.conjTranspose_one]
  have h1 := hA.inv.conjTranspose_mul_mul_same hinj
  rw [Matrix.conjTranspose_conjTranspose] at h1
  exact h1.inv

/- English proof (translation)
Introduce `n d A hA C P h1 h2`. Establish `hGP : Cᴴ * A * C * P = Cᴴ * A`. Rewrite `h2` using `[Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]`. Rewrite using `[Matrix.mul_assoc (Cᴴ * A), ← h2]`. Establish `hPG : Pᴴ * (Cᴴ * A * C) = A * C`.

Use `congrArg Matrix.conjTranspose hGP` as an intermediate fact. Simplify `this` using `[Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc]`. Rewrite using `[quotMetC, restrMetC]`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[Matrix.mul_assoc, hPG, Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit), Matrix.one_mul, h1]`.
-/
theorem quotEqRestrC : QuotEqRestrC := by
  intro n d A hA C P h1 h2
  have hGP : Cᴴ * A * C * P = Cᴴ * A := by
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2
    rw [Matrix.mul_assoc (Cᴴ * A), ← h2]
  have hPG : Pᴴ * (Cᴴ * A * C) = A * C := by
    have := congrArg Matrix.conjTranspose hGP
    simpa [Matrix.conjTranspose_mul, hA.isHermitian.eq, Matrix.mul_assoc] using this
  rw [quotMetC, restrMetC]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_assoc, hPG, Matrix.mul_assoc, ← Matrix.mul_assoc A⁻¹,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA.isUnit), Matrix.one_mul, h1]

/- English proof (translation)
Introduce `K _ _ _ K0 n H h1 h2`. Conclude with `⟨h1, fun v => frameOfSpec n _ (h2 v)⟩`.
-/
theorem stdFrameRatHerm : StdFrameRatHerm := by
  intro K _ _ _ K0 n H h1 h2
  exact ⟨h1, fun v => frameOfSpec n _ (h2 v)⟩

/- English proof (translation)
Introduce `K _ _ v0 n H h2`. Conclude with `⟨fun v => (frameOfSpec n _ (h2 v)).1, (frameOfSpec n _ (h2 v0)).2⟩`.
-/
theorem stdFrameHermAt : StdFrameHermAt := by
  intro K _ _ v0 n H h2
  exact ⟨fun v => (frameOfSpec n _ (h2 v)).1, (frameOfSpec n _ (h2 v0)).2⟩

/- English proof (translation)
Introduce `K _ _ _ n D H h2 P hP v`. Conclude with `frameOfSpec D _ ((quotRestrPosDef n D _ (h2 v)).1 _ (map_surj _ P hP))`.
-/
theorem quotFrameIsQuot : QuotFrameIsQuot := by
  intro K _ _ _ n D H h2 P hP v
  exact frameOfSpec D _ ((quotRestrPosDef n D _ (h2 v)).1 _ (map_surj _ P hP))

/- English proof (translation)
Introduce `K _ _ _ n d H h2 E hE v`. Establish `hs` using `frameOfSpec d _ ((quotRestrPosDef n d _ (h2 v)).2 _ (map_inj v.embedding E hE))`. Use `⟨hs.1, hs.2, fun x y => ?_⟩` and prove the remaining obligations. Establish `hm1 : metOf (restrFrame E H v) = restrMetC (E.map v.embedding) (H.map v.embedding)` using `hs.2`. Establish `hm2 : metOf (stdFrame H v) = H.map v.embedding` using `(frameOfSpec n _ (h2 v)).2`.

Rewrite using `[majAt_eq, majAt_eq, hm1, hm2, emb_mulVec, emb_mulVec, restrMetC, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem restrFrameSpec : RestrFrameSpec := by
  intro K _ _ _ n d H h2 E hE v
  have hs := frameOfSpec d _ ((quotRestrPosDef n d _ (h2 v)).2 _ (map_inj v.embedding E hE))
  refine ⟨hs.1, hs.2, fun x y => ?_⟩
  have hm1 : metOf (restrFrame E H v) = restrMetC (E.map v.embedding) (H.map v.embedding) := hs.2
  have hm2 : metOf (stdFrame H v) = H.map v.embedding := (frameOfSpec n _ (h2 v)).2
  rw [majAt_eq, majAt_eq, hm1, hm2, emb_mulVec, emb_mulVec, restrMetC, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul, map_conjTranspose' σ E hE, restrMetC]`.
-/
theorem map_restr {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {n d : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K)
    (hE : ∀ i a, σ (star (E i a)) = starRingEnd ℂ (σ (E i a))) :
    (Eᴴ * H * E).map σ = restrMetC (E.map σ) (H.map σ) := by
  rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose' σ E hE, restrMetC]

/- English proof (translation)
Introduce `K _ _ _ v0 hv0 n d H h2 E hE`. Use `⟨fun v => (restrFrameSpec K n d H h2 E hE v).1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_restr v0.embedding H E fun i a => hv0 _]`. Conclude with `(restrFrameSpec K n d H h2 E hE v0).2.1`.
-/
theorem restrFrameHermAt : RestrFrameHermAt := by
  intro K _ _ _ v0 hv0 n d H h2 E hE
  refine ⟨fun v => (restrFrameSpec K n d H h2 E hE v).1, ?_⟩
  rw [map_restr v0.embedding H E fun i a => hv0 _]
  exact (restrFrameSpec K n d H h2 E hE v0).2.1

/- English proof (translation)
Introduce `K _ _ _ K0 hcm hstar n d H h1 h2 E hE hE0`. Establish `hmap : ∀ v : InfinitePlace K, (Eᴴ * H * E).map v.embedding = restrMetC (E.map v.embedding) (H.map v.embedding)` using `fun v => map_restr v.embedding H E fun i a => hcm _ _ (hE0 i a)`. Use `⟨⟨?_, fun v => ⟨(restrFrameSpec K n d H h2 E hE v).1, ?_⟩⟩, ?_⟩` and prove the remaining obligations. Introduce `a b`. Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply]`.

Conclude with `Subfield.sum_mem _ fun j _ => Subfield.mul_mem _ (Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hstar _ (hE0 i a)) (h1 i j)) (hE0 j b)`. Rewrite using `[hmap v]`. Conclude with `(restrFrameSpec K n d H h2 E hE v).2.1`. Use function extensionality and compare the values at `v`. Rewrite using `[stdFrame, hmap v, restrFrame]`.
-/
theorem restrFrameRatHerm : RestrFrameRatHerm := by
  intro K _ _ _ K0 hcm hstar n d H h1 h2 E hE hE0
  have hmap : ∀ v : InfinitePlace K, (Eᴴ * H * E).map v.embedding =
      restrMetC (E.map v.embedding) (H.map v.embedding) :=
    fun v => map_restr v.embedding H E fun i a => hcm _ _ (hE0 i a)
  refine ⟨⟨?_, fun v => ⟨(restrFrameSpec K n d H h2 E hE v).1, ?_⟩⟩, ?_⟩
  · intro a b
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Subfield.sum_mem _ fun j _ => Subfield.mul_mem _
      (Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hstar _ (hE0 i a)) (h1 i j)) (hE0 j b)
  · rw [hmap v]
    exact (restrFrameSpec K n d H h2 E hE v).2.1
  · funext v
    rw [stdFrame, hmap v, restrFrame]

/- English proof (translation)
Establish `h1 : Pr.map v.embedding * E.map v.embedding = 1`. Rewrite using `[← Matrix.map_mul, hP.1, map_one']`. Establish `h2 : (E.map v.embedding)ᴴ * H.map v.embedding * (1 - E.map v.embedding * Pr.map v.embedding) = 0`. Use `congrArg (fun M => M.map v.embedding) hP.2` as an intermediate fact. Simplify using `only [Matrix.map_mul, Matrix.map_sub _ (map_sub v.embedding), map_one', map_conjTranspose' v.embedding E hE] at this`.

Rewrite using `[this]`. Conclude with `Matrix.map_zero _ (map_zero _)`. Rewrite using `[quotFrame, restrFrame, quotEqRestrC n d _ hH _ _ h1 h2]`.
-/
theorem quot_eq_restr_of {K : Type} [Field K] [NumberField K] [StarRing K] (v : InfinitePlace K)
    {n d : ℕ} (H : Matrix (Fin n) (Fin n) K) (hH : (H.map v.embedding).PosDef)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (hE : ∀ i a, v.embedding (star (E i a)) = starRingEnd ℂ (v.embedding (E i a)))
    (hP : IsOrthProj H E Pr) : quotFrame Pr H v = restrFrame E H v := by
  have h1 : Pr.map v.embedding * E.map v.embedding = 1 := by
    rw [← Matrix.map_mul, hP.1, map_one']
  have h2 : (E.map v.embedding)ᴴ * H.map v.embedding *
      (1 - E.map v.embedding * Pr.map v.embedding) = 0 := by
    have := congrArg (fun M => M.map v.embedding) hP.2
    simp only [Matrix.map_mul, Matrix.map_sub _ (map_sub v.embedding), map_one',
      map_conjTranspose' v.embedding E hE] at this
    rw [this]
    exact Matrix.map_zero _ (map_zero _)
  rw [quotFrame, restrFrame, quotEqRestrC n d _ hH _ _ h1 h2]

/- English proof (translation)
Introduce `K _ _ _ v0 hv0 n d H hH E Pr hP`. Conclude with `quot_eq_restr_of v0 H hH E Pr (fun i a => hv0 _) hP`.
-/
theorem quotEqRestrAt : QuotEqRestrAt := by
  intro K _ _ _ v0 hv0 n d H hH E Pr hP
  exact quot_eq_restr_of v0 H hH E Pr (fun i a => hv0 _) hP

/- English proof (translation)
Introduce `K _ _ _ K0 hcm n d H hH E Pr hE hP`. Use function extensionality and compare the values at `v`. Conclude with `quot_eq_restr_of v H (hH v) E Pr (fun i a => hcm _ _ (hE i a)) hP`.
-/
theorem quotEqRestrRat : QuotEqRestrRat := by
  intro K _ _ _ K0 hcm n d H hH E Pr hE hP
  funext v
  exact quot_eq_restr_of v H (hH v) E Pr (fun i a => hcm _ _ (hE i a)) hP

/- English proof (translation)
Introduce `K _ _ _ v0 hv0 n d H hH E Pr hP`. Establish `hsurj : Function.Surjective Pr.mulVec` using `Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨E, hP.1⟩`. Establish `hinj : Function.Injective E.mulVec` using `inj_of_left_inv hP.1`. Use `⟨fun v => (quotFrameIsQuot K n d H hH Pr hsurj v).1, ?_⟩` and prove the remaining obligations. Rewrite using `[quotEqRestrAt K v0 hv0 n d H (hH v0) E Pr hP]`.

Conclude with `(restrFrameHermAt K v0 hv0 n d H hH E hinj).2`.
-/
theorem quotFrameHermAt : QuotFrameHermAt := by
  intro K _ _ _ v0 hv0 n d H hH E Pr hP
  have hsurj : Function.Surjective Pr.mulVec :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨E, hP.1⟩
  have hinj : Function.Injective E.mulVec := inj_of_left_inv hP.1
  refine ⟨fun v => (quotFrameIsQuot K n d H hH Pr hsurj v).1, ?_⟩
  rw [quotEqRestrAt K v0 hv0 n d H (hH v0) E Pr hP]
  exact (restrFrameHermAt K v0 hv0 n d H hH E hinj).2

/- English proof (translation)
Introduce `K _ _ n v0 Y X`. Conclude with `⟨by simp [spliceFrame], fun v hv => by simp [spliceFrame, hv]⟩`.
-/
theorem spliceFrameSpec : SpliceFrameSpec := by
  intro K _ _ n v0 Y X
  classical
  exact ⟨by simp [spliceFrame], fun v hv => by simp [spliceFrame, hv]⟩

section Weight

variable {K : Type} [Field K] [NumberField K] {n : ℕ} {Ix : Type} [Fintype Ix]

/- English proof (translation)
Rewrite using `[weightMet, Matrix.sum_mulVec, dotProduct_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, restrMetC, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`.
-/
theorem weightMet_form (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (weightMet pr t X v).mulVec y =
      ∑ p, ((t p v : ℝ) : ℂ) * (star (((pr p).map v.embedding).mulVec x) ⬝ᵥ
        (metOf (X v)).mulVec (((pr p).map v.embedding).mulVec y)) := by
  rw [weightMet, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, restrMetC, Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/- English proof (translation)
Use `congrArg σ.mapMatrix hsum` as an intermediate fact. Simplify `this` using `[map_sum, RingHom.mapMatrix_apply]`.
-/
theorem sum_map_eq_one (pr : Ix → Matrix (Fin n) (Fin n) K) (hsum : ∑ p, pr p = 1) (σ : K →+* ℂ) :
    ∑ p, (pr p).map σ = 1 := by
  have := congrArg σ.mapMatrix hsum
  simpa [map_sum, RingHom.mapMatrix_apply] using this

/- English proof (translation)
Establish `hM` using `(metOfSpec n _ (hX v)).1`. Establish `hpsd : (weightMet pr t X v).PosSemidef`. Apply `Matrix.posSemidef_sum` to reduce the goal to its premises. Introduce `p _`. Apply `Matrix.PosSemidef.smul (hM.posSemidef.conjTranspose_mul_mul_same _)` to reduce the goal to its premises.

Conclude with `(ht p v).le` after adjusting the coercions. Use `Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1 fun x hx => ?_` and prove the remaining obligations. Rewrite using `[weightMet_form]`. Establish `ht' : ∀ p, (0 : ℂ) < ((t p v : ℝ) : ℂ)` using `fun p => by exact_mod_cast ht p v`. Apply `Finset.sum_pos'` to reduce the goal to its premises.

Introduce `p _`. Conclude with `mul_nonneg (ht' p).le (hM.posSemidef.dotProduct_mulVec_nonneg _)`. Assume the negation of the conclusion as `hcon`. Apply `hx` to reduce the goal to its premises. Establish `h0 : ∀ p, ((pr p).map v.embedding).mulVec x = 0`.

Introduce `p`. Assume the negation of the conclusion as `hp`. Conclude with `hcon ⟨p, Finset.mem_univ p, mul_pos (ht' p) (hM.dotProduct_mulVec_pos hp)⟩`. Establish `h1 : x = (∑ p, (pr p).map v.embedding).mulVec x`. Rewrite using `[sum_map_eq_one pr hsum, Matrix.one_mulVec]`.

Rewrite using `[h1, Matrix.sum_mulVec]`. Conclude with `Finset.sum_eq_zero fun p _ => h0 p`.
-/
theorem weightMet_posDef (pr : Ix → Matrix (Fin n) (Fin n) K) (t : Ix → InfinitePlace K → ℝ)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (ht : ∀ p v, 0 < t p v) (hsum : ∑ p, pr p = 1) (v : InfinitePlace K) :
    (weightMet pr t X v).PosDef := by
  have hM := (metOfSpec n _ (hX v)).1
  have hpsd : (weightMet pr t X v).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro p _
    apply Matrix.PosSemidef.smul (hM.posSemidef.conjTranspose_mul_mul_same _)
    exact_mod_cast (ht p v).le
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1 fun x hx => ?_
  rw [weightMet_form]
  have ht' : ∀ p, (0 : ℂ) < ((t p v : ℝ) : ℂ) := fun p => by exact_mod_cast ht p v
  apply Finset.sum_pos'
  · intro p _
    exact mul_nonneg (ht' p).le (hM.posSemidef.dotProduct_mulVec_nonneg _)
  · by_contra hcon
    apply hx
    have h0 : ∀ p, ((pr p).map v.embedding).mulVec x = 0 := by
      intro p
      by_contra hp
      exact hcon ⟨p, Finset.mem_univ p, mul_pos (ht' p) (hM.dotProduct_mulVec_pos hp)⟩
    have h1 : x = (∑ p, (pr p).map v.embedding).mulVec x := by
      rw [sum_map_eq_one pr hsum, Matrix.one_mulVec]
    rw [h1, Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun p _ => h0 p

end Weight

/- English proof (translation)
Introduce `K _ _ _ n Ix _ pr t X hX ht hsum v`. Establish `hs` using `frameOfSpec n _ (weightMet_posDef pr t X hX ht hsum v)`. Use `⟨hs.1, hs.2, fun x y => ?_⟩` and prove the remaining obligations. Establish `hm : metOf (weightFrame pr t X v) = weightMet pr t X v` using `hs.2`. Rewrite using `[majAt_eq, hm, weightMet_form]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[majAt_eq, emb_mulVec, emb_mulVec]`.
-/
theorem weightFrameSpec : WeightFrameSpec := by
  intro K _ _ _ n Ix _ pr t X hX ht hsum v
  have hs := frameOfSpec n _ (weightMet_posDef pr t X hX ht hsum v)
  refine ⟨hs.1, hs.2, fun x y => ?_⟩
  have hm : metOf (weightFrame pr t X v) = weightMet pr t X v := hs.2
  rw [majAt_eq, hm, weightMet_form]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [majAt_eq, emb_mulVec, emb_mulVec]

/- English proof (translation)
Introduce `K _ _ _ n Ix _ pr t X hX ht hsum horth v hperp p x y hx`. Rewrite using `[(weightFrameSpec K n Ix pr t X hX ht hsum v).2.2 x y]`. Establish `hq0 : ∀ q, q ≠ p → (pr q).mulVec x = 0`. Introduce `q hq`. Rewrite using `[← hx, Matrix.mulVec_mulVec, horth q p hq, Matrix.zero_mulVec]`.

Establish `hz : ∀ u : Fin n → K, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v 0 u = 0`. Introduce `u`. Rewrite using `[majAt_eq]`. Establish `: (fun i => v.embedding ((0 : Fin n → K) i)) = 0` using `by funext i; simp`. Rewrite using `[this, star_zero, zero_dotProduct]`.

Rewrite using `[Finset.sum_eq_single p (fun q _ hq => by rw [hq0 q hq, hz, mul_zero]) (fun h => absurd (Finset.mem_univ p) h), hx]`. Use `congr 1`. Establish `hy : (fun i => v.embedding (y i)) = ∑ q, ((pr q).map v.embedding).mulVec (fun i => v.embedding (y i))`. Rewrite using `[← Matrix.sum_mulVec, sum_map_eq_one pr hsum, Matrix.one_mulVec]`. Establish `hterm : ∀ q, q ≠ p → star (fun i => v.embedding (x i)) ⬝ᵥ (metOf (X v)).mulVec (((pr q).map v.embedding).mulVec (fun i => v.embedding (y i))) = 0`.

Introduce `q hq`. Use `hperp p q (Ne.symm hq) x y` as an intermediate fact. Rewrite `this` using `[hx, majAt_eq, emb_mulVec]`. Then use the resulting hypothesis. Rewrite using `[majAt_eq, majAt_eq, emb_mulVec]`. Use `conv_rhs => rw [hy, Matrix.mulVec_sum, dotProduct_sum]`.

Rewrite using `[Finset.sum_eq_single p (fun q _ hq => hterm q hq) (fun h => absurd (Finset.mem_univ p) h)]`.
-/
theorem weightFramePart : WeightFramePart := by
  intro K _ _ _ n Ix _ pr t X hX ht hsum horth v hperp p x y hx
  classical
  rw [(weightFrameSpec K n Ix pr t X hX ht hsum v).2.2 x y]
  have hq0 : ∀ q, q ≠ p → (pr q).mulVec x = 0 := by
    intro q hq
    rw [← hx, Matrix.mulVec_mulVec, horth q p hq, Matrix.zero_mulVec]
  have hz : ∀ u : Fin n → K, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v 0 u = 0 := by
    intro u
    rw [majAt_eq]
    have : (fun i => v.embedding ((0 : Fin n → K) i)) = 0 := by funext i; simp
    rw [this, star_zero, zero_dotProduct]
  rw [Finset.sum_eq_single p (fun q _ hq => by rw [hq0 q hq, hz, mul_zero])
    (fun h => absurd (Finset.mem_univ p) h), hx]
  congr 1
  have hy : (fun i => v.embedding (y i)) =
      ∑ q, ((pr q).map v.embedding).mulVec (fun i => v.embedding (y i)) := by
    rw [← Matrix.sum_mulVec, sum_map_eq_one pr hsum, Matrix.one_mulVec]
  have hterm : ∀ q, q ≠ p → star (fun i => v.embedding (x i)) ⬝ᵥ (metOf (X v)).mulVec
      (((pr q).map v.embedding).mulVec (fun i => v.embedding (y i))) = 0 := by
    intro q hq
    have := hperp p q (Ne.symm hq) x y
    rwa [hx, majAt_eq, emb_mulVec] at this
  rw [majAt_eq, majAt_eq, emb_mulVec]
  conv_rhs => rw [hy, Matrix.mulVec_sum, dotProduct_sum]
  rw [Finset.sum_eq_single p (fun q _ hq => hterm q hq) (fun h => absurd (Finset.mem_univ p) h)]

/- English proof (translation)
Rewrite using `[majAt_eq, majAt_eq, h]`.
-/
theorem majAt_congr_frame {K : Type} [Field K] [NumberField K] {n : ℕ}
    (X X2 : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (h : X v = X2 v)
    (x y : Fin n → K) : Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X2 v x y := by
  rw [majAt_eq, majAt_eq, h]

/- English proof (translation)
Simplify using `only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.majAt]`. Use `congr 1`. Rewrite using `[Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]`.
-/
theorem normAt_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (v : InfinitePlace K) (x : Fin n → K) :
    Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v x =
      Real.sqrt (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v x x).re := by
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm, Formalism.HermitianLatticesTheory.majAt]
  congr 1
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

section Instances

variable (K : Type) [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Introduce `σ _ ha` and use `ha σ`.
-/
theorem isCMSub_cmMax' : IsCMSub (cmMax K) := fun σ _ ha => ha σ

def sumP : Matrix (Fin 1) (Fin 2) K := Matrix.of fun _ _ => 1

def diagE : Matrix (Fin 2) (Fin 1) K := Matrix.of fun _ _ => 1

end Instances

end Formalism.L2.DIV
