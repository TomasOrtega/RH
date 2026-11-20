import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

namespace GlobalTheory.CartanPlane

open Matrix

/- English proof (translation)
Use extensionality with `i`. Simplify using `[mulVec, dotProduct, star_sum]`.
-/
theorem star_mulVec_map {m k : Type} [Fintype k] (B : Matrix m k ℂ) (v : k → ℂ) :
    star (B *ᵥ v) = B.map star *ᵥ star v := by
  ext i
  simp [mulVec, dotProduct, star_sum]

/- English proof (translation)
Rewrite using `[star_mulVec_map, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm (A *ᵥ u), dotProduct_mulVec, dotProduct_comm]`.
-/
theorem form_mulVec {m k l : Type} [Fintype m] [Fintype k] [Fintype l] (A : Matrix m k ℂ) (B : Matrix m l ℂ)
    (M : Matrix m m ℂ) (u : k → ℂ) (v : l → ℂ) :
    (A *ᵥ u) ⬝ᵥ M *ᵥ star (B *ᵥ v) = u ⬝ᵥ (Aᵀ * M * B.map star) *ᵥ star v := by
  rw [star_mulVec_map, ← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose, dotProduct_comm (A *ᵥ u),
    dotProduct_mulVec, dotProduct_comm]

/- English proof (translation)
Establish `h : ∀ i j, star (M i j) = M j i` using `fun i j => by rw [← conjTranspose_apply, hM]`. Simplify using `only [dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum, h]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_swap {m : Type} [Fintype m] (M : Matrix m m ℂ) (hM : Mᴴ = M) (x y : m → ℂ) :
    y ⬝ᵥ M *ᵥ star x = star (x ⬝ᵥ M *ᵥ star y) := by
  have h : ∀ i j, star (M i j) = M j i := fun i j => by rw [← conjTranspose_apply, hM]
  simp only [dotProduct, mulVec, star_sum, star_mul', star_star, Pi.star_apply, Finset.mul_sum, h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Use extensionality with `i j`. Use `h (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Simplify `this` using `[single_dotProduct, mulVec_single]`.
-/
theorem ext_form {m : Type} [Fintype m] [DecidableEq m] (A B : Matrix m m ℂ)
    (h : ∀ x y : m → ℂ, x ⬝ᵥ A *ᵥ star y = x ⬝ᵥ B *ᵥ star y) : A = B := by
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  simpa [single_dotProduct, mulVec_single] using this

end GlobalTheory.CartanPlane

namespace GlobalTheory.CartanPlane
open Matrix

/- English proof (translation)
Introduce `n n₁ M X Yv ι P θ₁ hn hM hXX hYY hXY hιX hιY hPι hθ₁`. Substitute `hn` using the available equality. Use `set M₁ := ιᵀ * M * ι.map star with hM₁`. Establish `hYX : Yv ⬝ᵥ M *ᵥ star X = 1` using `by rw [herm_swap M hM, hXY]; simp`. Establish `hιuX : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0`.

Introduce `u`. Rewrite using `[dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιX, zero_dotProduct]`. Establish `hιuY : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star Yv = 0`. Introduce `u`. Rewrite using `[dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιY, zero_dotProduct]`.

Establish `hXιu : ∀ u, X ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0` using `by intro u; rw [herm_swap M hM, hιuX, star_zero]`. Establish `hYιu : ∀ u, Yv ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0` using `by intro u; rw [herm_swap M hM, hιuY, star_zero]`. Establish `hιι : ∀ u u', (ι *ᵥ u) ⬝ᵥ M *ᵥ star (ι *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u'` using `fun u u' => form_mulVec ι ι M u u'`. Establish `hexp : ∀ u (a b : ℂ) u' (a' b' : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star (ι *ᵥ u' + a' • X + b' • Yv) = u ⬝ᵥ M₁ *ᵥ star u' + a * star b' + b * star a'`. Introduce `u a b u' a' b'`.

Simplify using `only [add_dotProduct, star_add, mulVec_add, dotProduct_add, smul_dotProduct, star_smul, mulVec_smul, dotProduct_smul, hιι, hιuX, hιuY, hXιu, hYιu, hXX, hYY, hXY, hYX, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcY : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star Yv = a`. Introduce `u a b`. Use `hexp u a b 0 0 1` as an intermediate fact.

Simplify using `using this`. Establish `hcX : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star X = b`. Introduce `u a b`. Use `hexp u a b 0 1 0` as an intermediate fact. Simplify using `using this`.

Establish `hdec : ∀ z : Fin (n₁ + 2) → ℂ, ∃ (u : Fin n₁ → ℂ) (a b : ℂ), z = ι *ᵥ u + a • X + b • Yv`. Set `Φ : ((Fin n₁ → ℂ) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin (n₁ + 2) → ℂ)` to `(Matrix.toLin' ι).comp (LinearMap.fst ℂ _ _) + ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).smulRight X).comp (LinearMap.snd ℂ _ _) + ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).smulRight Yv).comp (LinearMap.snd ℂ _ _)`. Establish `hΦ : ∀ p, Φ p = ι *ᵥ p.1 + p.2 0 • X + p.2 1 • Yv` using `fun p => by simp [Φ]`. Establish `hinj : Function.Injective Φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce and unpack `⟨u, w⟩ h0`. Rewrite `h0` using `[hΦ]`. Establish `ha` using `hcY u (w 0) (w 1)`. Establish `hb` using `hcX u (w 0) (w 1)`. Simplify using `only at h0 ha hb`.

Rewrite `ha`, `hb` using `[h0, zero_dotProduct]`. Establish `hu : ι *ᵥ u = 0` using `by rw [← ha, ← hb] at h0; simpa using h0`. Establish `: u = 0` using `by rw [← one_mulVec u, ← hPι, ← mulVec_mulVec, hu, mulVec_zero]`. Use `Prod.ext this ?_` and prove the remaining obligations. Apply the tactic sequence `ext i; fin_cases i <;> simp [← ha, ← hb]`.

Establish `hsurj : Function.Surjective Φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_prod])).mp hinj`. Introduce `z`. Take `⟨p, hp⟩` from `hsurj z`. Conclude with `⟨p.1, p.2 0, p.2 1, by rw [← hp, hΦ]⟩`. Use `set vX := M *ᵥ star X with hvX`.

Use `set vY := M *ᵥ star Yv with hvY`. Use `set C₁ : Matrix (Fin n₁) (Fin (n₁ + 2)) ℂ := P - vecMulVec (P *ᵥ X) vY - vecMulVec (P *ᵥ Yv) vX with hC₁`. Use `set θ : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ := ι * θ₁ * C₁ + vecMulVec Yv vY + vecMulVec X vX with hθdef`. Establish `hθ : ∀ u (a b : ℂ), θ *ᵥ (ι *ᵥ u + a • X + b • Yv) = ι *ᵥ (θ₁ *ᵥ u) + b • X + a • Yv`. Introduce `u a b`.

Establish `ha : vY ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = a` using `by rw [dotProduct_comm]; exact hcY u a b`. Establish `hb : vX ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = b` using `by rw [dotProduct_comm]; exact hcX u a b`. Establish `hC : C₁ *ᵥ (ι *ᵥ u + a • X + b • Yv) = u`. Rewrite using `[hC₁, sub_mulVec, sub_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec, hPι, one_mulVec]`. Simplify using `only [op_smul_eq_smul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hθdef, add_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, ← mulVec_mulVec, ← mulVec_mulVec, hC]`. Simplify using `only [op_smul_eq_smul]`. Normalize the expressions using the abelian group laws. Establish `hext : ∀ A B : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ, (∀ u (a b : ℂ), A *ᵥ (ι *ᵥ u + a • X + b • Yv) = B *ᵥ (ι *ᵥ u + a • X + b • Yv)) → A = B`.

Introduce `A B h`. Apply `ext_of_mulVec_single` to reduce the goal to its premises. Introduce `i`. Take `⟨u, a, b, hz⟩` from `hdec (Pi.single i 1)`. Rewrite using `[hz, h]`.

Establish `hθ₁θ₁ : ∀ u, θ₁ *ᵥ (θ₁ *ᵥ u) = u` using `fun u => by rw [mulVec_mulVec, hθ₁.1, one_mulVec]`. Establish `hiso₁ : ∀ u u', (θ₁ *ᵥ u) ⬝ᵥ M₁ *ᵥ star (θ₁ *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u'` using `fun u u' => by`. Rewrite using `[form_mulVec, hθ₁.2.1]`. Establish `hre : ∀ c : ℂ, (c * star c).re = Complex.normSq c` using `fun c => by`. Simplify using `[Complex.mul_re, Complex.normSq_apply]`.

Use `⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Apply `hext` to reduce the goal to its premises. Introduce `u a b`. Rewrite using `[← mulVec_mulVec, hθ, hθ, hθ₁θ₁, one_mulVec]`. Apply `ext_form` to reduce the goal to its premises.

Introduce `x y`. Rewrite using `[← form_mulVec]`. Take `⟨u, a, b, rfl⟩` from `hdec x`. Take `⟨u', a', b', rfl⟩` from `hdec y`. Rewrite using `[hθ, hθ, hexp, hexp, hiso₁]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `x hx`. Take `⟨u, a, b, rfl⟩` from `hdec x`. Rewrite using `[hθ, hexp, Complex.add_re, Complex.add_re, hre, hre]`. Distinguish the cases in `hu : u = 0`.

Substitute `hu` using the available equality. Establish `hab : a ≠ 0 ∨ b ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hx` to reduce the goal to its premises.

Simplify using `[h.1, h.2]`. Simplify using `only [mulVec_zero, zero_dotProduct, Complex.zero_re, zero_add]`. Break down `hab with h | h` into its components or cases. Use `Complex.normSq_pos.mpr h` as an intermediate fact. Use `Complex.normSq_nonneg b` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Use `Complex.normSq_pos.mpr h` as an intermediate fact. Use `Complex.normSq_nonneg a` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `hθ₁.2.2 u hu` as an intermediate fact.

Use `Complex.normSq_nonneg b` as an intermediate fact. Use `Complex.normSq_nonneg a` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Apply `ext_of_mulVec_single` to reduce the goal to its premises. Introduce `j`.

Use `hθ (Pi.single j 1) 0 0` as an intermediate fact. Simplify using `only [zero_smul, add_zero] at this`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, this]`. Use `hθ 0 1 0` as an intermediate fact. Simplify using `using this`.
-/
theorem extend_swap : ∀ (n n₁ : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (X Yv : Fin n → ℂ) (ι : Matrix (Fin n) (Fin n₁) ℂ)
    (P : Matrix (Fin n₁) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ), n = n₁ + 2 → Mᴴ = M →
    X ⬝ᵥ M *ᵥ star X = 0 → Yv ⬝ᵥ M *ᵥ star Yv = 0 → X ⬝ᵥ M *ᵥ star Yv = 1 →
    ιᵀ *ᵥ (M *ᵥ star X) = 0 → ιᵀ *ᵥ (M *ᵥ star Yv) = 0 → P * ι = 1 →
    IsCartan (ιᵀ * M * ι.map star) θ₁ → ∃ θ, IsCartan M θ ∧ θ * ι = ι * θ₁ ∧ θ *ᵥ X = Yv := by
  intro n n₁ M X Yv ι P θ₁ hn hM hXX hYY hXY hιX hιY hPι hθ₁
  subst hn
  set M₁ := ιᵀ * M * ι.map star with hM₁
  have hYX : Yv ⬝ᵥ M *ᵥ star X = 1 := by rw [herm_swap M hM, hXY]; simp
  have hιuX : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star X = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιX, zero_dotProduct]
  have hιuY : ∀ u, (ι *ᵥ u) ⬝ᵥ M *ᵥ star Yv = 0 := by
    intro u; rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hιY, zero_dotProduct]
  have hXιu : ∀ u, X ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuX, star_zero]
  have hYιu : ∀ u, Yv ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 := by intro u; rw [herm_swap M hM, hιuY, star_zero]
  have hιι : ∀ u u', (ι *ᵥ u) ⬝ᵥ M *ᵥ star (ι *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => form_mulVec ι ι M u u'
  have hexp : ∀ u (a b : ℂ) u' (a' b' : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star (ι *ᵥ u' + a' • X + b' • Yv) =
      u ⬝ᵥ M₁ *ᵥ star u' + a * star b' + b * star a' := by
    intro u a b u' a' b'
    simp only [add_dotProduct, star_add, mulVec_add, dotProduct_add, smul_dotProduct, star_smul, mulVec_smul,
      dotProduct_smul, hιι, hιuX, hιuY, hXιu, hYιu, hXX, hYY, hXY, hYX, smul_eq_mul]
    ring
  have hcY : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star Yv = a := by
    intro u a b; have := hexp u a b 0 0 1; simpa using this
  have hcX : ∀ u (a b : ℂ), (ι *ᵥ u + a • X + b • Yv) ⬝ᵥ M *ᵥ star X = b := by
    intro u a b; have := hexp u a b 0 1 0; simpa using this

  have hdec : ∀ z : Fin (n₁ + 2) → ℂ, ∃ (u : Fin n₁ → ℂ) (a b : ℂ), z = ι *ᵥ u + a • X + b • Yv := by
    let Φ : ((Fin n₁ → ℂ) × (Fin 2 → ℂ)) →ₗ[ℂ] (Fin (n₁ + 2) → ℂ) :=
      (Matrix.toLin' ι).comp (LinearMap.fst ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).smulRight X).comp (LinearMap.snd ℂ _ _) +
        ((LinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 1).smulRight Yv).comp (LinearMap.snd ℂ _ _)
    have hΦ : ∀ p, Φ p = ι *ᵥ p.1 + p.2 0 • X + p.2 1 • Yv := fun p => by simp [Φ]
    have hinj : Function.Injective Φ := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨u, w⟩ h0
      rw [hΦ] at h0
      have ha := hcY u (w 0) (w 1)
      have hb := hcX u (w 0) (w 1)
      simp only at h0 ha hb
      rw [h0, zero_dotProduct] at ha hb
      have hu : ι *ᵥ u = 0 := by rw [← ha, ← hb] at h0; simpa using h0
      have : u = 0 := by rw [← one_mulVec u, ← hPι, ← mulVec_mulVec, hu, mulVec_zero]
      refine Prod.ext this ?_
      ext i; fin_cases i <;> simp [← ha, ← hb]
    have hsurj : Function.Surjective Φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_prod])).mp hinj
    intro z
    obtain ⟨p, hp⟩ := hsurj z
    exact ⟨p.1, p.2 0, p.2 1, by rw [← hp, hΦ]⟩

  set vX := M *ᵥ star X with hvX
  set vY := M *ᵥ star Yv with hvY
  set C₁ : Matrix (Fin n₁) (Fin (n₁ + 2)) ℂ := P - vecMulVec (P *ᵥ X) vY - vecMulVec (P *ᵥ Yv) vX with hC₁
  set θ : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ := ι * θ₁ * C₁ + vecMulVec Yv vY + vecMulVec X vX with hθdef
  have hθ : ∀ u (a b : ℂ), θ *ᵥ (ι *ᵥ u + a • X + b • Yv) = ι *ᵥ (θ₁ *ᵥ u) + b • X + a • Yv := by
    intro u a b
    have ha : vY ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = a := by rw [dotProduct_comm]; exact hcY u a b
    have hb : vX ⬝ᵥ (ι *ᵥ u + a • X + b • Yv) = b := by rw [dotProduct_comm]; exact hcX u a b
    have hC : C₁ *ᵥ (ι *ᵥ u + a • X + b • Yv) = u := by
      rw [hC₁, sub_mulVec, sub_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, mulVec_add, mulVec_add,
        mulVec_smul, mulVec_smul, mulVec_mulVec, hPι, one_mulVec]
      simp only [op_smul_eq_smul]
      abel
    rw [hθdef, add_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ha, hb, ← mulVec_mulVec, ← mulVec_mulVec, hC]
    simp only [op_smul_eq_smul]
    abel
  have hext : ∀ A B : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) ℂ,
      (∀ u (a b : ℂ), A *ᵥ (ι *ᵥ u + a • X + b • Yv) = B *ᵥ (ι *ᵥ u + a • X + b • Yv)) → A = B := by
    intro A B h
    apply ext_of_mulVec_single
    intro i
    obtain ⟨u, a, b, hz⟩ := hdec (Pi.single i 1)
    rw [hz, h]
  have hθ₁θ₁ : ∀ u, θ₁ *ᵥ (θ₁ *ᵥ u) = u := fun u => by rw [mulVec_mulVec, hθ₁.1, one_mulVec]
  have hiso₁ : ∀ u u', (θ₁ *ᵥ u) ⬝ᵥ M₁ *ᵥ star (θ₁ *ᵥ u') = u ⬝ᵥ M₁ *ᵥ star u' := fun u u' => by
    rw [form_mulVec, hθ₁.2.1]
  have hre : ∀ c : ℂ, (c * star c).re = Complex.normSq c := fun c => by
    simp [Complex.mul_re, Complex.normSq_apply]
  refine ⟨θ, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · apply hext
    intro u a b
    rw [← mulVec_mulVec, hθ, hθ, hθ₁θ₁, one_mulVec]
  · apply ext_form
    intro x y
    rw [← form_mulVec]
    obtain ⟨u, a, b, rfl⟩ := hdec x
    obtain ⟨u', a', b', rfl⟩ := hdec y
    rw [hθ, hθ, hexp, hexp, hiso₁]
    ring
  · intro x hx
    obtain ⟨u, a, b, rfl⟩ := hdec x
    rw [hθ, hexp, Complex.add_re, Complex.add_re, hre, hre]
    by_cases hu : u = 0
    · subst hu
      have hab : a ≠ 0 ∨ b ≠ 0 := by
        by_contra h
        push_neg at h
        apply hx
        simp [h.1, h.2]
      simp only [mulVec_zero, zero_dotProduct, Complex.zero_re, zero_add]
      rcases hab with h | h
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg b; linarith
      · have := Complex.normSq_pos.mpr h; have := Complex.normSq_nonneg a; linarith
    · have := hθ₁.2.2 u hu
      have := Complex.normSq_nonneg b; have := Complex.normSq_nonneg a; linarith
  · apply ext_of_mulVec_single
    intro j
    have := hθ (Pi.single j 1) 0 0
    simp only [zero_smul, add_zero] at this
    rw [← mulVec_mulVec, ← mulVec_mulVec, this]
  · have := hθ 0 1 0
    simpa using this

end GlobalTheory.CartanPlane
