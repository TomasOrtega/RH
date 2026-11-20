import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section
namespace GlobalTheory.UnitLemma.Desc

/- English proof (translation)
Rewrite using `[Algebra.norm_apply, Algebra.norm_apply]`. Establish `h : Algebra.lmul F (R₁ × R₂) (x, 1) = (Algebra.lmul F R₁ x).prodMap (Algebra.lmul F R₂ 1)`. Apply the tactic sequence `refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp`. Rewrite using `[h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₂), map_one LinearMap.det, mul_one]`.
-/
theorem norm_prod_one {F R₁ R₂ : Type} [Field F] [CommRing R₁] [CommRing R₂] [Algebra F R₁] [Algebra F R₂]
    [Module.Finite F R₁] [Module.Finite F R₂] (x : R₁) :
    Algebra.norm F ((x, 1) : R₁ × R₂) = Algebra.norm F x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (R₁ × R₂) (x, 1) = (Algebra.lmul F R₁ x).prodMap (Algebra.lmul F R₂ 1) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₂), map_one LinearMap.det, mul_one]

/- English proof (translation)
Rewrite using `[Algebra.norm_apply, Algebra.norm_apply]`. Establish `h : Algebra.lmul F (R₁ × R₂) (1, x) = (Algebra.lmul F R₁ 1).prodMap (Algebra.lmul F R₂ x)`. Apply the tactic sequence `refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp`. Rewrite using `[h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₁), map_one LinearMap.det, one_mul]`.
-/
theorem norm_one_prod {F R₁ R₂ : Type} [Field F] [CommRing R₁] [CommRing R₂] [Algebra F R₁] [Algebra F R₂]
    [Module.Finite F R₁] [Module.Finite F R₂] (x : R₂) :
    Algebra.norm F ((1, x) : R₁ × R₂) = Algebra.norm F x := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul F (R₁ × R₂) (1, x) = (Algebra.lmul F R₁ 1).prodMap (Algebra.lmul F R₂ x) := by
    refine LinearMap.ext fun p => Prod.ext ?_ ?_ <;> simp
  rw [h, LinearMap.det_prodMap, map_one (Algebra.lmul F R₁), map_one LinearMap.det, one_mul]

/- English proof (translation)
Use `⟨⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | j)`. Conclude with `Prod.ext (h₁.idem i).eq (mul_zero 0)`. Conclude with `Prod.ext (mul_zero 0) (h₂.idem j).eq`. Introduce and unpack `(i | j) (i' | j') hne`.

Establish `hii : i ≠ i'` using `fun h => hne (congrArg Sum.inl h)`. Conclude with `Prod.ext (h₁.ortho hii) (mul_zero 0)`. Conclude with `Prod.ext (mul_zero _) (zero_mul _)`. Conclude with `Prod.ext (zero_mul _) (mul_zero _)`. Establish `hjj : j ≠ j'` using `fun h => hne (congrArg Sum.inr h)`.

Conclude with `Prod.ext (mul_zero 0) (h₂.ortho hjj)`. Rewrite using `[Fintype.sum_sum_type]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[Prod.fst_sum, h₁.complete]`. Simplify using `[Prod.snd_sum, h₂.complete]`.
-/
theorem coi_prod {R₁ R₂ : Type} [Ring R₁] [Ring R₂] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {e₁ : ι₁ → R₁} {e₂ : ι₂ → R₂} (h₁ : CompleteOrthogonalIdempotents e₁)
    (h₂ : CompleteOrthogonalIdempotents e₂) :
    CompleteOrthogonalIdempotents (Sum.elim (fun i => ((e₁ i, 0) : R₁ × R₂)) (fun j => ((0, e₂ j) : R₁ × R₂))) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro (i | j)
    · exact Prod.ext (h₁.idem i).eq (mul_zero 0)
    · exact Prod.ext (mul_zero 0) (h₂.idem j).eq
  · rintro (i | j) (i' | j') hne
    · have hii : i ≠ i' := fun h => hne (congrArg Sum.inl h)
      exact Prod.ext (h₁.ortho hii) (mul_zero 0)
    · exact Prod.ext (mul_zero _) (zero_mul _)
    · exact Prod.ext (zero_mul _) (mul_zero _)
    · have hjj : j ≠ j' := fun h => hne (congrArg Sum.inr h)
      exact Prod.ext (mul_zero 0) (h₂.ortho hjj)
  · rw [Fintype.sum_sum_type]
    refine Prod.ext ?_ ?_
    · simp [Prod.fst_sum, h₁.complete]
    · simp [Prod.snd_sum, h₂.complete]

/- English proof (translation)
Take `⟨f, hf, hf0, hfy, hQ, hnQ⟩` from `h`. Use `⟨(f, 0), Prod.ext hf.eq (mul_zero 0), fun h0 => hf0 (congrArg Prod.fst h0), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y₁, y₂⟩ hy`. Establish `hy₁ : f * y₁ ≠ 0` using `fun h0 => hy (Prod.ext h0 (zero_mul y₂))`. Take `⟨z, hz⟩` from `hfy y₁ hy₁`.

Conclude with `⟨(z, 0), Prod.ext hz (mul_zero _)⟩`. Introduce `hP`. Take `⟨h1, h2⟩` from `hQ (hPQ.1 hP)`. Use `⟨by rw [h1], ?_⟩` and prove the remaining obligations. Use `show (σ₁ f, σ₂ 0) = (f, 0)`.

Rewrite using `[h2, map_zero]`. Introduce `hP`. Take `⟨h1, h2⟩` from `hnQ (fun hq => hP (hPQ.2 hq))`. Use `show ((f, 0) * (σ₁ f, σ₂ 0) : R₁ × R₂) = 0 ∧ (e, 0) = (f, 0) + (σ₁ f, σ₂ 0)`. Rewrite using `[map_zero]`.

Conclude with `⟨Prod.ext h1 (mul_zero 0), Prod.ext h2 (add_zero 0).symm⟩`.
-/
theorem factor_inl {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (e : R₁) (P Q : Prop) (hPQ : P ↔ Q)
    (h : ∃ f : R₁, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (Q → e = f ∧ σ₁ f = f) ∧ (¬Q → f * σ₁ f = 0 ∧ e = f + σ₁ f)) :
    ∃ f : R₁ × R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (P → (e, 0) = f ∧ RingEquiv.prodCongr σ₁ σ₂ f = f) ∧
      (¬P → f * RingEquiv.prodCongr σ₁ σ₂ f = 0 ∧ (e, 0) = f + RingEquiv.prodCongr σ₁ σ₂ f) := by
  obtain ⟨f, hf, hf0, hfy, hQ, hnQ⟩ := h
  refine ⟨(f, 0), Prod.ext hf.eq (mul_zero 0), fun h0 => hf0 (congrArg Prod.fst h0), ?_, ?_, ?_⟩
  · rintro ⟨y₁, y₂⟩ hy
    have hy₁ : f * y₁ ≠ 0 := fun h0 => hy (Prod.ext h0 (zero_mul y₂))
    obtain ⟨z, hz⟩ := hfy y₁ hy₁
    exact ⟨(z, 0), Prod.ext hz (mul_zero _)⟩
  · intro hP
    obtain ⟨h1, h2⟩ := hQ (hPQ.1 hP)
    refine ⟨by rw [h1], ?_⟩
    show (σ₁ f, σ₂ 0) = (f, 0)
    rw [h2, map_zero]
  · intro hP
    obtain ⟨h1, h2⟩ := hnQ (fun hq => hP (hPQ.2 hq))
    show ((f, 0) * (σ₁ f, σ₂ 0) : R₁ × R₂) = 0 ∧ (e, 0) = (f, 0) + (σ₁ f, σ₂ 0)
    rw [map_zero]
    exact ⟨Prod.ext h1 (mul_zero 0), Prod.ext h2 (add_zero 0).symm⟩

/- English proof (translation)
Take `⟨f, hf, hf0, hfy, hQ, hnQ⟩` from `h`. Use `⟨(0, f), Prod.ext (mul_zero 0) hf.eq, fun h0 => hf0 (congrArg Prod.snd h0), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y₁, y₂⟩ hy`. Establish `hy₂ : f * y₂ ≠ 0` using `fun h0 => hy (Prod.ext (zero_mul y₁) h0)`. Take `⟨z, hz⟩` from `hfy y₂ hy₂`.

Conclude with `⟨(0, z), Prod.ext (mul_zero _) hz⟩`. Introduce `hP`. Take `⟨h1, h2⟩` from `hQ (hPQ.1 hP)`. Use `⟨by rw [h1], ?_⟩` and prove the remaining obligations. Use `show (σ₁ 0, σ₂ f) = (0, f)`.

Rewrite using `[h2, map_zero]`. Introduce `hP`. Take `⟨h1, h2⟩` from `hnQ (fun hq => hP (hPQ.2 hq))`. Use `show ((0, f) * (σ₁ 0, σ₂ f) : R₁ × R₂) = 0 ∧ (0, e) = (0, f) + (σ₁ 0, σ₂ f)`. Rewrite using `[map_zero]`.

Conclude with `⟨Prod.ext (mul_zero 0) h1, Prod.ext (add_zero 0).symm h2⟩`.
-/
theorem factor_inr {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (e : R₂) (P Q : Prop) (hPQ : P ↔ Q)
    (h : ∃ f : R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (Q → e = f ∧ σ₂ f = f) ∧ (¬Q → f * σ₂ f = 0 ∧ e = f + σ₂ f)) :
    ∃ f : R₁ × R₂, IsIdempotentElem f ∧ f ≠ 0 ∧ (∀ y, f * y ≠ 0 → ∃ z, f * y * z = f) ∧
      (P → (0, e) = f ∧ RingEquiv.prodCongr σ₁ σ₂ f = f) ∧
      (¬P → f * RingEquiv.prodCongr σ₁ σ₂ f = 0 ∧ (0, e) = f + RingEquiv.prodCongr σ₁ σ₂ f) := by
  obtain ⟨f, hf, hf0, hfy, hQ, hnQ⟩ := h
  refine ⟨(0, f), Prod.ext (mul_zero 0) hf.eq, fun h0 => hf0 (congrArg Prod.snd h0), ?_, ?_, ?_⟩
  · rintro ⟨y₁, y₂⟩ hy
    have hy₂ : f * y₂ ≠ 0 := fun h0 => hy (Prod.ext (zero_mul y₁) h0)
    obtain ⟨z, hz⟩ := hfy y₂ hy₂
    exact ⟨(0, z), Prod.ext (mul_zero _) hz⟩
  · intro hP
    obtain ⟨h1, h2⟩ := hQ (hPQ.1 hP)
    refine ⟨by rw [h1], ?_⟩
    show (σ₁ 0, σ₂ f) = (0, f)
    rw [h2, map_zero]
  · intro hP
    obtain ⟨h1, h2⟩ := hnQ (fun hq => hP (hPQ.2 hq))
    show ((0, f) * (σ₁ 0, σ₂ f) : R₁ × R₂) = 0 ∧ (0, e) = (0, f) + (σ₁ 0, σ₂ f)
    rw [map_zero]
    exact ⟨Prod.ext (mul_zero 0) h1, Prod.ext (add_zero 0).symm h2⟩

/- English proof (translation)
Use `⟨⟨Prod.isUnit_iff.2 ⟨hu, isUnit_one⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show (σ₁ x, σ₂ 1) = (x, 1)`. Rewrite using `[hσ, map_one]`. Conclude with `Prod.ext (by simpa using h1) (by simp)`.
-/
theorem unit_inl {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (x e : R₁) (hu : IsUnit x) (hσ : σ₁ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((x, 1) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (x, 1) = (x, 1)) ∧
      ((x, 1) : R₁ × R₂) * (1 - (e, 0)) = 1 - (e, 0) := by
  refine ⟨⟨Prod.isUnit_iff.2 ⟨hu, isUnit_one⟩, ?_⟩, ?_⟩
  · show (σ₁ x, σ₂ 1) = (x, 1)
    rw [hσ, map_one]
  · exact Prod.ext (by simpa using h1) (by simp)

/- English proof (translation)
Use `⟨⟨Prod.isUnit_iff.2 ⟨isUnit_one, hu⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show (σ₁ 1, σ₂ x) = (1, x)`. Rewrite using `[hσ, map_one]`. Conclude with `Prod.ext (by simp) (by simpa using h1)`.
-/
theorem unit_inr {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (σ₁ : R₁ ≃+* R₁) (σ₂ : R₂ ≃+* R₂)
    (x e : R₂) (hu : IsUnit x) (hσ : σ₂ x = x) (h1 : x * (1 - e) = 1 - e) :
    (IsUnit ((1, x) : R₁ × R₂) ∧ RingEquiv.prodCongr σ₁ σ₂ (1, x) = (1, x)) ∧
      ((1, x) : R₁ × R₂) * (1 - (0, e)) = 1 - (0, e) := by
  refine ⟨⟨Prod.isUnit_iff.2 ⟨isUnit_one, hu⟩, ?_⟩, ?_⟩
  · show (σ₁ 1, σ₂ x) = (1, x)
    rw [hσ, map_one]
  · exact Prod.ext (by simp) (by simpa using h1)

/- English proof (translation)
Introduce `K B₁ B₂ ι₁ ι₂ _ _ e₁ π₁ e₂ π₂ S₁ S₂ h₁ h₂`. Take `⟨⟨hc₁, hf₁⟩, hπ₁⟩` from `h₁`. Take `⟨⟨hc₂, hf₂⟩, hπ₂⟩` from `h₂`. Use `⟨⟨coi_prod hc₁ hc₂, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | j)`.

Conclude with `factor_inl B₁.σ B₂.σ (e₁ i) _ _ Finset.inl_mem_disjSum (hf₁ i)`. Conclude with `factor_inr B₁.σ B₂.σ (e₂ j) _ _ Finset.inr_mem_disjSum (hf₂ j)`. Introduce and unpack `(i | j) hi`. Rewrite `hi` using `[Finset.inl_mem_disjSum]`. Take `⟨⟨hu, hσ⟩, h1, hη⟩` from `hπ₁ i hi`.

Take `⟨hA, hB⟩` from `unit_inl B₁.σ B₂.σ (π₁ i) (e₁ i) hu hσ h1`. Use `⟨hA, hB, ?_⟩` and prove the remaining obligations. Use `show K.eta (Algebra.norm K.E ((π₁ i, 1) : B₁.A × B₂.A)) = -1`. Rewrite using `[norm_prod_one]`. Conclude with `hη`.

Rewrite `hi` using `[Finset.inr_mem_disjSum]`. Take `⟨⟨hu, hσ⟩, h1, hη⟩` from `hπ₂ j hi`. Take `⟨hA, hB⟩` from `unit_inr B₁.σ B₂.σ (π₂ j) (e₂ j) hu hσ h1`. Use `⟨hA, hB, ?_⟩` and prove the remaining obligations. Use `show K.eta (Algebra.norm K.E ((1, π₂ j) : B₁.A × B₂.A)) = -1`.

Rewrite using `[norm_one_prod]`. Conclude with `hη`.
-/
theorem isFrame_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] (e₁ π₁ : ι₁ → B₁.A) (e₂ π₂ : ι₂ → B₂.A) (S₁ : Finset ι₁) (S₂ : Finset ι₂), IsFrame B₁ e₁ π₁ S₁ → IsFrame B₂ e₂ π₂ S₂ → IsFrame (B₁.prod B₂) (Sum.elim (fun i => ((e₁ i, 0) : B₁.A × B₂.A)) (fun j => ((0, e₂ j) : B₁.A × B₂.A))) (Sum.elim (fun i => ((π₁ i, 1) : B₁.A × B₂.A)) (fun j => ((1, π₂ j) : B₁.A × B₂.A))) (S₁.disjSum S₂) := by
  intro K B₁ B₂ ι₁ ι₂ _ _ e₁ π₁ e₂ π₂ S₁ S₂ h₁ h₂
  obtain ⟨⟨hc₁, hf₁⟩, hπ₁⟩ := h₁
  obtain ⟨⟨hc₂, hf₂⟩, hπ₂⟩ := h₂
  refine ⟨⟨coi_prod hc₁ hc₂, ?_⟩, ?_⟩
  · rintro (i | j)
    · exact factor_inl B₁.σ B₂.σ (e₁ i) _ _ Finset.inl_mem_disjSum (hf₁ i)
    · exact factor_inr B₁.σ B₂.σ (e₂ j) _ _ Finset.inr_mem_disjSum (hf₂ j)
  · rintro (i | j) hi
    · rw [Finset.inl_mem_disjSum] at hi
      obtain ⟨⟨hu, hσ⟩, h1, hη⟩ := hπ₁ i hi
      obtain ⟨hA, hB⟩ := unit_inl B₁.σ B₂.σ (π₁ i) (e₁ i) hu hσ h1
      refine ⟨hA, hB, ?_⟩
      show K.eta (Algebra.norm K.E ((π₁ i, 1) : B₁.A × B₂.A)) = -1
      rw [norm_prod_one]
      exact hη
    · rw [Finset.inr_mem_disjSum] at hi
      obtain ⟨⟨hu, hσ⟩, h1, hη⟩ := hπ₂ j hi
      obtain ⟨hA, hB⟩ := unit_inr B₁.σ B₂.σ (π₂ j) (e₂ j) hu hσ h1
      refine ⟨hA, hB, ?_⟩
      show K.eta (Algebra.norm K.E ((1, π₂ j) : B₁.A × B₂.A)) = -1
      rw [norm_one_prod]
      exact hη

end GlobalTheory.UnitLemma.Desc
