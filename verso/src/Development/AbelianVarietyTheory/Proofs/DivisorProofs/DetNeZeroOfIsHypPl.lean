import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAutSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.HypPl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[hcm.2.2.2, hcm.2.2.2, star_star]`.
-/
theorem conj_conj {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2, star_star]

section Form

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Simplify using `[form, add_dotProduct]`.
-/
theorem form_add_left (a b c : Fin n → E) : form σ J (a + b) c = form σ J a c + form σ J b c := by
  simp [form, add_dotProduct]

/- English proof (translation)
Simplify using `[form, smul_dotProduct]`.
-/
theorem form_smul_left (s : E) (a c : Fin n → E) : form σ J (s • a) c = s * form σ J a c := by
  simp [form, smul_dotProduct]

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem form_skew (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) :
    σ (form σ J b a) = -form σ J a b := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Establish `h : (fun i => σ ((ι *ᵥ v) i)) = ι.map σ *ᵥ fun k => σ (v k)`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`. Simplify using `only [form]`. Rewrite using `[h, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]`.
-/
theorem form_mulVec {n₁ : ℕ} (ι : Matrix (Fin n) (Fin n₁) E) (u v : Fin n₁ → E) :
    form σ J (ι *ᵥ u) (ι *ᵥ v) = form σ (ιᵀ * J * ι.map σ) u v := by
  have h : (fun i => σ ((ι *ᵥ v) i)) = ι.map σ *ᵥ fun k => σ (v k) := by
    funext i; simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [form]
  rw [h, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul,
    ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]

end Form

section Hyp

variable {σ : E →ₐ[F] E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁}

/- English proof (translation)
Simplify using `[form]`.
-/
theorem form_zero_left (J : Matrix (Fin n) (Fin n) E) (c : Fin n → E) : form σ J 0 c = 0 := by
  simp [form]

/- English proof (translation)
Establish `h` using `form_skew σ Y.J hσ hH.2.2.2.2.2.2.1 H.y H.x`. Rewrite `h` using `[hH.2.2.2.1, map_one]`. Take the linear combination `h`.
-/
theorem form_y_x (hσ : ∀ e, σ (σ e) = e) (hH : IntV.IsHypPl σ Y Y₁ H) : form σ Y.J H.y H.x = -1 := by
  have h := form_skew σ Y.J hσ hH.2.2.2.2.2.2.1 H.y H.x
  rw [hH.2.2.2.1, map_one] at h
  linear_combination h

/- English proof (translation)
Establish `hyx` using `form_y_x hσ hH`. Take `⟨-, hxx, hyy, hxy, horth, hgram, hJ, hdet⟩` from `hH`. Establish `hx` using `h H.x`. Establish `hy` using `h H.y`. Simplify using `only [form_add_left, form_smul_left, hxx, hyy, hxy, hyx, (horth u).1, (horth u).2] at hx hy`.

Establish `ht : t = 0` using `by linear_combination -hx`. Establish `hs : s = 0` using `by linear_combination hy`. Substitute `ht hs` using the available equality. Use `⟨rfl, ?_, rfl⟩` and prove the remaining obligations. Establish `hu : u ᵥ* Y₁.J = 0`.

Use function extensionality and compare the values at `i`. Establish `hi` using `h (H.ι *ᵥ Pi.single i 1)`. Rewrite `hi` using `[zero_smul, zero_smul, zero_add, add_zero, form_mulVec, hgram]`. Establish `hs1 : (fun k => σ ((Pi.single i (1 : E) : Fin n₁ → E) k)) = (Pi.single i (1 : E) : Fin n₁ → E)`. Apply the tactic sequence `funext k; by_cases hk : k = i <;> simp [hk]`.

Rewrite `hi` using `[form, hs1, Matrix.dotProduct_mulVec, dotProduct_single, mul_one]`. Conclude with `hi`. Conclude with `Matrix.eq_zero_of_vecMul_eq_zero hdet hu`.
-/
theorem coeffs_eq_zero (hσ : ∀ e, σ (σ e) = e) (hH : IntV.IsHypPl σ Y Y₁ H) (s t : E) (u : Fin n₁ → E)
    (h : ∀ c, form σ Y.J (s • H.x + H.ι *ᵥ u + t • H.y) c = 0) : s = 0 ∧ u = 0 ∧ t = 0 := by
  have hyx := form_y_x hσ hH
  obtain ⟨-, hxx, hyy, hxy, horth, hgram, hJ, hdet⟩ := hH
  have hx := h H.x
  have hy := h H.y
  simp only [form_add_left, form_smul_left, hxx, hyy, hxy, hyx, (horth u).1, (horth u).2] at hx hy
  have ht : t = 0 := by linear_combination -hx
  have hs : s = 0 := by linear_combination hy
  subst ht hs
  refine ⟨rfl, ?_, rfl⟩
  have hu : u ᵥ* Y₁.J = 0 := by
    funext i
    have hi := h (H.ι *ᵥ Pi.single i 1)
    rw [zero_smul, zero_smul, zero_add, add_zero, form_mulVec, hgram] at hi
    have hs1 : (fun k => σ ((Pi.single i (1 : E) : Fin n₁ → E) k)) = (Pi.single i (1 : E) : Fin n₁ → E) := by
      funext k; by_cases hk : k = i <;> simp [hk]
    rw [form, hs1, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at hi
    exact hi
  exact Matrix.eq_zero_of_vecMul_eq_zero hdet hu

def hypMap (H : Plane E n n₁) : (E × (Fin n₁ → E) × E) →ₗ[E] (Fin n → E) :=
  (LinearMap.fst E E ((Fin n₁ → E) × E)).smulRight H.x +
    (Matrix.mulVecLin H.ι).comp ((LinearMap.fst E (Fin n₁ → E) E).comp (LinearMap.snd E E _)) +
    ((LinearMap.snd E (Fin n₁ → E) E).comp (LinearMap.snd E E _)).smulRight H.y

/- English proof (translation)
Simplify using `[hypMap]`.
-/
theorem hypMap_apply (H : Plane E n n₁) (p : E × (Fin n₁ → E) × E) :
    hypMap H p = p.1 • H.x + H.ι *ᵥ p.2.1 + p.2.2 • H.y := by
  simp [hypMap]

/- English proof (translation)
Establish `hinj : Function.Injective (hypMap H)`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce and unpack `⟨s, u, t⟩ hp`. Rewrite `hp` using `[hypMap_apply]`. Take `⟨rfl, rfl, rfl⟩` from `coeffs_eq_zero hσ hH s t u (fun c => by rw [hp, form_zero_left])`.

Both sides reduce to the same expression. Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_prod, hH.1]; omega)).1 hinj`. Take `⟨⟨s, u, t⟩, hp⟩` from `hsurj z`. Conclude with `⟨s, t, u, by rw [← hp, hypMap_apply]⟩`.
-/
theorem span_of_isHypPl (hσ : ∀ e, σ (σ e) = e) (hH : IntV.IsHypPl σ Y Y₁ H) (z : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y := by
  have hinj : Function.Injective (hypMap H) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, u, t⟩ hp
    rw [hypMap_apply] at hp
    obtain ⟨rfl, rfl, rfl⟩ := coeffs_eq_zero hσ hH s t u (fun c => by rw [hp, form_zero_left])
    rfl
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Module.finrank_prod, hH.1]; omega)).1 hinj
  obtain ⟨⟨s, u, t⟩, hp⟩ := hsurj z
  exact ⟨s, t, u, by rw [← hp, hypMap_apply]⟩

/- English proof (translation)
Introduce `hd`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hd`. Take `⟨s, t, u, rfl⟩` from `span_of_isHypPl hσ hH w`. Take `⟨rfl, rfl, rfl⟩` from `coeffs_eq_zero hσ hH s t u (fun c => by`. Rewrite using `[form, Matrix.dotProduct_mulVec, hw, zero_dotProduct])`.

Conclude with `hw0 (by simp)`.
-/
theorem det_ne_zero_of_isHypPl (hσ : ∀ e, σ (σ e) = e) (hH : IntV.IsHypPl σ Y Y₁ H) : Y.J.det ≠ 0 := by
  intro hd
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
  obtain ⟨s, t, u, rfl⟩ := span_of_isHypPl hσ hH w
  obtain ⟨rfl, rfl, rfl⟩ := coeffs_eq_zero hσ hH s t u (fun c => by
    rw [form, Matrix.dotProduct_mulVec, hw, zero_dotProduct])
  exact hw0 (by simp)

end Hyp

end GlobalTheory.ThK.HypPl

end
