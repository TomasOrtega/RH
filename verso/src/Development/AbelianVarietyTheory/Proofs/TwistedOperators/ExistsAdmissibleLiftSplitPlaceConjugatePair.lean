import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockOfMatrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.AdmLift

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d W v hskew π₁ π₂ b₁ b₂ h12 h21 inj surj S hS X₁ X₂ hX`. Set `c : v.adicCompletionIntegers F →+* Fv F v` to `(v.adicCompletionIntegers F).toSubring.subtype`. Establish `hc : ∀ A : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), A.map (fun x => (x : Fv F v)) = A.map c` using `fun _ => rfl`. Use `set B₁ : Matrix (Fin d) (Fin d) (Fv F v) := (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) with hB₁`. Use `set B₂ : Matrix (Fin d) (Fin d) (Fv F v) := (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) with hB₂`.

Use `set C₁ : Matrix (Fin d) (Fin d) (Fv F v) := ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hC₁`. Use `set C₂ : Matrix (Fin d) (Fin d) (Fv F v) := ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hC₂`. Establish `hBC₂ : B₂ * C₂ = 1` using `b₂.mul_inv`. Establish `hCB₁ : C₁ᵀ * B₁ᵀ = 1` using `by rw [← Matrix.transpose_mul, show B₁ * C₁ = 1 from b₁.mul_inv, Matrix.transpose_one]`. Use `set J₁ : Matrix (Fin d) (Fin d) (Fv F v) := (incM F W.J).map π₁ with hJ₁`.

Use `set M₁ : Matrix (Fin d) (Fin d) (Fv F v) := B₁ * X₁.map (fun x => (x : Fv F v)) * C₁ with hM₁`. Use `set M₂ : Matrix (Fin d) (Fin d) (Fv F v) := B₂ * X₂.map (fun x => (x : Fv F v)) * C₂ with hM₂`. Establish `hX' : (X₁.map c)ᵀ * S.map c + S.map c * X₂.map c = 0`. Use `congrArg (fun A => A.map c) hX` as an intermediate fact. Simplify `this` using `[Matrix.map_add, Matrix.map_mul, Matrix.transpose_map]`.

Rewrite `hS` using `[hc]`. Establish `key₁ : M₁ᵀ * J₁ + J₁ * M₂ = 0`. Establish `e : M₁ᵀ * J₁ + J₁ * M₂ = C₁ᵀ * ((X₁.map c)ᵀ * S.map c + S.map c * X₂.map c) * C₂`. Rewrite using `[hS, hM₁, hM₂, hc, hc]`. Simplify using `only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`.

Use `congr 1`. Rewrite using `[hBC₂, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc C₁ᵀ, hCB₁, Matrix.one_mul]`. Rewrite using `[e, hX', Matrix.mul_zero, Matrix.zero_mul]`. Establish `hJ₂ : (incM F W.J).map π₂ = -J₁ᵀ`.

Use extensionality with `i j`. Establish `h1 : cA σ (inclR (F` using `F) (AF F) (W.J i j)) = inclR (F := F) (AF F) (σ (W.J i j)) := by simp [cA, inclR]`. Simplify using `only [incM, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, hJ₁]`. Rewrite using `[← h12, h1, hskew j i, map_neg, map_neg]`. Establish `key₂ : M₂ᵀ * (-J₁ᵀ) + (-J₁ᵀ) * M₁ = 0`.

Establish `gen : ∀ A B K : Matrix (Fin d) (Fin d) (Fv F v), Bᵀ * (-Kᵀ) + (-Kᵀ) * A = -(Aᵀ * K + K * B)ᵀ`. Introduce `A B K`. Rewrite using `[Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, neg_add, Matrix.mul_neg, Matrix.neg_mul, add_comm]`. Rewrite using `[gen, key₁, Matrix.transpose_zero, neg_zero]`. Use `choose z hzA hz1 hz2 using surj`.

Set `Y : Matrix (Fin d) (Fin d) (AE F E)` to `Matrix.of fun i j => z (M₁ i j) (M₂ i j)`. Establish `hY1 : Y.map π₁ = M₁` using `by ext i j; simp [Y, hz1]`. Establish `hY2 : Y.map π₂ = M₂` using `by ext i j; simp [Y, hz2]`. Establish `hAtE : ∀ i j, At (evFin F v) (Y i j)` using `fun i j => hzA _ _`. Establish `atMulR : ∀ a b : AE F E, At (evFin F v) a → At (evFin F v) (a * b)` using `fun a b ha u hu => by`.

Rewrite using `[← smul_mul_assoc, ha u hu, zero_mul]`. Establish `atMulL : ∀ a b : AE F E, At (evFin F v) b → At (evFin F v) (a * b)` using `fun a b hb u hu => by`. Rewrite using `[← mul_smul_comm, hb u hu, mul_zero]`. Establish `atCA : ∀ a : AE F E, At (evFin F v) a → At (evFin F v) (cA σ a)` using `fun a ha u hu => by`. Rewrite using `[← map_smul, ha u hu, map_zero]`.

Establish `atSum : ∀ f : Fin d → AE F E, (∀ k, At (evFin F v) (f k)) → At (evFin F v) (∑ k, f k)` using `fun f hf u hu => by`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_eq_zero fun k _ => hf k u hu`. Establish `atAdd : ∀ a b : AE F E, At (evFin F v) a → At (evFin F v) b → At (evFin F v) (a + b)` using `fun a b ha hb u hu => by`. Rewrite using `[smul_add, ha u hu, hb u hu, add_zero]`.

Use `⟨Y, ?_, hY1, hY2, ?_⟩` and prove the remaining obligations. Introduce `u hu`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, Matrix.zero_apply]`. Conclude with `hAtE i j u hu`.

Use `set Q := Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) with hQ`. Establish `hcomp₁ : (Y.map (cA σ)).map π₁ = M₂`. Rewrite using `[← hY2]`. Use extensionality with `i j`. Simplify using `[h12]`.

Establish `hcomp₂ : (Y.map (cA σ)).map π₂ = M₁`. Rewrite using `[← hY1]`. Use extensionality with `i j`. Simplify using `[h21]`. Establish `hQ1 : Q.map π₁ = 0`.

Rewrite using `[hQ, Matrix.map_add, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hY1, hcomp₁, ← hJ₁, key₁]`. Conclude with `fun a b => map_add π₁ a b`. Establish `hQ2 : Q.map π₂ = 0`. Rewrite using `[hQ, Matrix.map_add, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hY2, hcomp₂, hJ₂, key₂]`. Conclude with `fun a b => map_add π₂ a b`.

Use extensionality with `i j`. Apply `inj` to reduce the goal to its premises. Simplify using `only [hQ, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Conclude with `atAdd _ _ (atSum _ fun k => atMulR _ _ (hAtE k i)) (atSum _ fun k => atMulL _ _ (atCA _ (hAtE k j)))`. Use `congrFun (congrFun hQ1 i) j` as an intermediate fact.

Simplify using `using this`. Use `congrFun (congrFun hQ2 i) j` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_admissible_lift : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F), (∀ i j, σ (W.J j i) = -W.J i j) →
  ∀ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
  (∀ z, π₁ (cA σ z) = π₂ z) → (∀ z, π₂ (cA σ z) = π₁ z) → (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) → (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) →
  ∀ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F),
  S.map (fun x => (x : Fv F v)) = (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) →
  ∀ X₁ X₂ : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), X₁ᵀ * S + S * X₂ = 0 →
  ∃ Y : Matrix (Fin d) (Fin d) (AE F E), At (evFin F v) Y ∧
    Y.map π₁ = (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) * X₁.map (fun x => (x : Fv F v)) * ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Y.map π₂ = (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) * X₂.map (fun x => (x : Fv F v)) * ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) ∧
    Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) = 0 := by
  intro F E _ _ _ _ _ σ d W v hskew π₁ π₂ b₁ b₂ h12 h21 inj surj S hS X₁ X₂ hX

  let c : v.adicCompletionIntegers F →+* Fv F v := (v.adicCompletionIntegers F).toSubring.subtype
  have hc : ∀ A : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), A.map (fun x => (x : Fv F v)) = A.map c := fun _ => rfl
  set B₁ : Matrix (Fin d) (Fin d) (Fv F v) := (b₁ : Matrix (Fin d) (Fin d) (Fv F v)) with hB₁
  set B₂ : Matrix (Fin d) (Fin d) (Fv F v) := (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) with hB₂
  set C₁ : Matrix (Fin d) (Fin d) (Fv F v) := ((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hC₁
  set C₂ : Matrix (Fin d) (Fin d) (Fv F v) := ((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) with hC₂
  have hBC₂ : B₂ * C₂ = 1 := b₂.mul_inv
  have hCB₁ : C₁ᵀ * B₁ᵀ = 1 := by rw [← Matrix.transpose_mul, show B₁ * C₁ = 1 from b₁.mul_inv, Matrix.transpose_one]
  set J₁ : Matrix (Fin d) (Fin d) (Fv F v) := (incM F W.J).map π₁ with hJ₁
  set M₁ : Matrix (Fin d) (Fin d) (Fv F v) := B₁ * X₁.map (fun x => (x : Fv F v)) * C₁ with hM₁
  set M₂ : Matrix (Fin d) (Fin d) (Fv F v) := B₂ * X₂.map (fun x => (x : Fv F v)) * C₂ with hM₂

  have hX' : (X₁.map c)ᵀ * S.map c + S.map c * X₂.map c = 0 := by
    have := congrArg (fun A => A.map c) hX
    simpa [Matrix.map_add, Matrix.map_mul, Matrix.transpose_map] using this
  rw [hc] at hS
  have key₁ : M₁ᵀ * J₁ + J₁ * M₂ = 0 := by
    have e : M₁ᵀ * J₁ + J₁ * M₂ = C₁ᵀ * ((X₁.map c)ᵀ * S.map c + S.map c * X₂.map c) * C₂ := by
      rw [hS, hM₁, hM₂, hc, hc]
      simp only [Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      congr 1
      · rw [hBC₂, Matrix.mul_one]
      · rw [← Matrix.mul_assoc C₁ᵀ, hCB₁, Matrix.one_mul]
    rw [e, hX', Matrix.mul_zero, Matrix.zero_mul]

  have hJ₂ : (incM F W.J).map π₂ = -J₁ᵀ := by
    ext i j
    have h1 : cA σ (inclR (F := F) (AF F) (W.J i j)) = inclR (F := F) (AF F) (σ (W.J i j)) := by simp [cA, inclR]
    simp only [incM, Matrix.map_apply, Matrix.neg_apply, Matrix.transpose_apply, hJ₁]
    rw [← h12, h1, hskew j i, map_neg, map_neg]
  have key₂ : M₂ᵀ * (-J₁ᵀ) + (-J₁ᵀ) * M₁ = 0 := by
    have gen : ∀ A B K : Matrix (Fin d) (Fin d) (Fv F v), Bᵀ * (-Kᵀ) + (-Kᵀ) * A = -(Aᵀ * K + K * B)ᵀ := by
      intro A B K
      rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, neg_add,
        Matrix.mul_neg, Matrix.neg_mul, add_comm]
    rw [gen, key₁, Matrix.transpose_zero, neg_zero]

  choose z hzA hz1 hz2 using surj
  let Y : Matrix (Fin d) (Fin d) (AE F E) := Matrix.of fun i j => z (M₁ i j) (M₂ i j)
  have hY1 : Y.map π₁ = M₁ := by ext i j; simp [Y, hz1]
  have hY2 : Y.map π₂ = M₂ := by ext i j; simp [Y, hz2]
  have hAtE : ∀ i j, At (evFin F v) (Y i j) := fun i j => hzA _ _
  have atMulR : ∀ a b : AE F E, At (evFin F v) a → At (evFin F v) (a * b) := fun a b ha u hu => by
    rw [← smul_mul_assoc, ha u hu, zero_mul]
  have atMulL : ∀ a b : AE F E, At (evFin F v) b → At (evFin F v) (a * b) := fun a b hb u hu => by
    rw [← mul_smul_comm, hb u hu, mul_zero]
  have atCA : ∀ a : AE F E, At (evFin F v) a → At (evFin F v) (cA σ a) := fun a ha u hu => by
    rw [← map_smul, ha u hu, map_zero]
  have atSum : ∀ f : Fin d → AE F E, (∀ k, At (evFin F v) (f k)) → At (evFin F v) (∑ k, f k) := fun f hf u hu => by
    rw [Finset.smul_sum]; exact Finset.sum_eq_zero fun k _ => hf k u hu
  have atAdd : ∀ a b : AE F E, At (evFin F v) a → At (evFin F v) b → At (evFin F v) (a + b) := fun a b ha hb u hu => by
    rw [smul_add, ha u hu, hb u hu, add_zero]
  refine ⟨Y, ?_, hY1, hY2, ?_⟩
  · intro u hu
    ext i j
    rw [Matrix.smul_apply, Matrix.zero_apply]
    exact hAtE i j u hu
  · set Q := Yᵀ * incM F W.J + incM F W.J * Y.map (cA σ) with hQ
    have hcomp₁ : (Y.map (cA σ)).map π₁ = M₂ := by
      rw [← hY2]; ext i j; simp [h12]
    have hcomp₂ : (Y.map (cA σ)).map π₂ = M₁ := by
      rw [← hY1]; ext i j; simp [h21]
    have hQ1 : Q.map π₁ = 0 := by
      rw [hQ, Matrix.map_add, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hY1, hcomp₁, ← hJ₁, key₁]
      exact fun a b => map_add π₁ a b
    have hQ2 : Q.map π₂ = 0 := by
      rw [hQ, Matrix.map_add, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hY2, hcomp₂, hJ₂, key₂]
      exact fun a b => map_add π₂ a b
    ext i j
    apply inj
    · simp only [hQ, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
      exact atAdd _ _ (atSum _ fun k => atMulR _ _ (hAtE k i)) (atSum _ fun k => atMulL _ _ (atCA _ (hAtE k j)))
    · have := congrFun (congrFun hQ1 i) j
      simpa using this
    · have := congrFun (congrFun hQ2 i) j
      simpa using this

end GlobalTheory.AdmLift

end
