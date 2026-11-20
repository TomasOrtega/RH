import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import ReciprocityTheory.DualLattices.FischerSelfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TotalDegreeSubstFLe

open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ConjugateType

def ConjSp (E : Type) : Type := E

namespace ConjSp

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

instance : NormedAddCommGroup (ConjSp E) := inferInstanceAs (NormedAddCommGroup E)

def out (x : ConjSp E) : E := x

def mk (x : E) : ConjSp E := x

instance : Module ℂ (ConjSp E) := Module.compHom E (starRingEnd ℂ)

instance : NormedSpace ℂ (ConjSp E) where
  norm_smul_le z x := by
    show ‖starRingEnd ℂ z • out x‖ ≤ ‖z‖ * ‖out x‖
    rw [norm_smul, RCLike.norm_conj]

instance : InnerProductSpace ℂ (ConjSp E) where
  inner x y := inner ℂ (out y) (out x)
  norm_sq_eq_re_inner x := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (out x)
  conj_inner_symm x y := inner_conj_symm (𝕜 := ℂ) (out y) (out x)
  add_left x y z := inner_add_right (𝕜 := ℂ) (out z) (out x) (out y)
  smul_left x y r := inner_smul_right (𝕜 := ℂ) (out y) (out x) (starRingEnd ℂ r)

def mkL (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] : E →ₛₗ[starRingEnd ℂ] ConjSp E where
  toFun := mk
  map_add' _ _ := rfl
  map_smul' z x := by
    show z • x = starRingEnd ℂ (starRingEnd ℂ z) • x
    rw [Complex.conj_conj]

instance [FiniteDimensional ℂ E] : FiniteDimensional ℂ (ConjSp E) :=
  Module.Finite.of_surjective (mkL E) fun x => ⟨out x, rfl⟩

def map (f : E →L[ℂ] E) : ConjSp E →L[ℂ] ConjSp E where
  toFun x := mk (f (out x))
  map_add' x y := f.map_add (out x) (out y)
  map_smul' z x := f.map_smul (starRingEnd ℂ z) (out x)
  cont := f.cont

def unsub (V : Submodule ℂ (ConjSp E)) : Submodule ℂ E where
  carrier := {x | mk x ∈ V}
  add_mem' hx hy := V.add_mem hx hy
  zero_mem' := V.zero_mem
  smul_mem' z x hx := by
    have h := V.smul_mem (starRingEnd ℂ z) hx
    have e : mk (z • x) = starRingEnd ℂ z • mk x := (mkL E).map_smul' z x
    show mk (z • x) ∈ V
    rw [e]; exact h

end ConjSp

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := starRingEnd ℂ)`.
-/
theorem map_star_mul {k : ℕ} (a b : Matrix (Fin k) (Fin k) ℂ) :
    (a * b).map star = a.map star * b.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

/- English proof (translation)
The claim follows from `Matrix.map_one _ (star_zero _) (star_one _)`.
-/
theorem map_star_one {k : ℕ} : (1 : Matrix (Fin k) (Fin k) ℂ).map star = 1 :=
  Matrix.map_one _ (star_zero _) (star_one _)

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_star_star {k : ℕ} (a : Matrix (Fin k) (Fin k) ℂ) : (a.map star).map star = a := by
  ext i j; simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_star_conjTranspose {k : ℕ} (a : Matrix (Fin k) (Fin k) ℂ) : (a.map star)ᴴ = aᴴ.map star := by
  ext i j; simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_star_Jm {k : ℕ} (ε : Fin k → Bool) : (Formalism.REAL.Jm ε).map star = Formalism.REAL.Jm ε := by
  ext i j
  simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `h` using `congrArg (fun a : Matrix (Fin k) (Fin k) ℂ => a.map star) (show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε from hg)`. Simplify using `only [map_star_mul, map_star_Jm, ← map_star_conjTranspose] at h`. Conclude with `h`.
-/
theorem map_star_mem_UJ {k : ℕ} {ε : Fin k → Bool} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset ε) :
    g.map star ∈ UJset ε := by
  have h := congrArg (fun a : Matrix (Fin k) (Fin k) ℂ => a.map star) (show gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε from hg)
  simp only [map_star_mul, map_star_Jm, ← map_star_conjTranspose] at h
  exact h

/- English proof (translation)
Take `⟨h1, h2⟩` from `hg`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `h1`, the goal using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]`. Rewrite using `[map_star_conjTranspose, ← map_star_mul, h1, map_star_one]`. Establish `h` using `congrArg (fun a : Matrix (Fin k) (Fin k) ℂ => a.map star) h2`.

Simplify `h` using `only [map_star_mul, map_star_Jm]`.
-/
theorem map_star_mem_K {k : ℕ} {ε : Fin k → Bool} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) :
    g.map star ∈ Formalism.REAL.Kset ε := by
  obtain ⟨h1, h2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] at h1 ⊢
    rw [map_star_conjTranspose, ← map_star_mul, h1, map_star_one]
  · have h := congrArg (fun a : Matrix (Fin k) (Fin k) ℂ => a.map star) h2
    simpa only [map_star_mul, map_star_Jm] using h

/- English proof (translation)
Rewrite using `[← Complex.exp_conj]`. Simplify using the standard rewrite rules.
-/
theorem star_exp_mul_I (x : ℝ) :
    starRingEnd ℂ (Complex.exp ((x : ℂ) * Complex.I)) = Complex.exp (((-x : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_conj]
  simp

/- English proof (translation)
Rewrite using `[Matrix.diagonal_map (star_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `star_exp_mul_I (θ a)`.
-/
theorem map_star_diag {k : ℕ} (θ : Fin k → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).map star =
      Matrix.diagonal fun a => Complex.exp ((((-θ) a : ℝ) : ℂ) * Complex.I) := by
  rw [Matrix.diagonal_map (star_zero _)]
  congr 1
  funext a
  exact star_exp_mul_I (θ a)

variable {k : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def conjRep (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) :
    Matrix (Fin k) (Fin k) ℂ → (ConjSp H →L[ℂ] ConjSp H) :=
  fun g => ConjSp.map (σ (g.map star))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem sum_neg (μ θ : Fin k → ℝ) : ∑ a, μ a * (-θ) a = -∑ a, μ a * θ a := by
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h θ hθ`. Establish `h1` using `map_star_mem_K hθ`. Rewrite `h1` using `[map_star_diag]`. Establish `h2 : σ ((Matrix.diagonal fun a => Complex.exp ((((-θ) a : ℝ) : ℂ) * Complex.I)).map star) (ConjSp.out v) = starRingEnd ℂ (Complex.exp (((∑ a, μ a * (-θ) a : ℝ) : ℂ) * Complex.I)) • ConjSp.out v` using `h (-θ) h1`.

Rewrite `h2` using `[map_star_diag, star_exp_mul_I, sum_neg, neg_neg, neg_neg]`. Conclude with `h2`. Introduce `h θ hθ`. Establish `h1` using `map_star_mem_K hθ`. Rewrite `h1` using `[map_star_diag]`.

Establish `h2` using `h (-θ) h1`. Use `show σ ((Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).map star) (ConjSp.out v) = starRingEnd ℂ (Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I)) • ConjSp.out v`. Rewrite using `[map_star_diag, star_exp_mul_I, ← sum_neg]`. Conclude with `h2`.
-/
theorem isWtOn_conjRep_iff (ε : Fin k → Bool) (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (μ : Fin k → ℝ)
    (v : ConjSp H) :
    IsWtOn (Formalism.REAL.Kset ε) (conjRep σ) μ v ↔ IsWtOn (Formalism.REAL.Kset ε) σ μ (ConjSp.out v) := by
  constructor
  · intro h θ hθ
    have h1 := map_star_mem_K hθ
    rw [map_star_diag] at h1
    have h2 : σ ((Matrix.diagonal fun a => Complex.exp ((((-θ) a : ℝ) : ℂ) * Complex.I)).map star) (ConjSp.out v) =
        starRingEnd ℂ (Complex.exp (((∑ a, μ a * (-θ) a : ℝ) : ℂ) * Complex.I)) • ConjSp.out v := h (-θ) h1
    rw [map_star_diag, star_exp_mul_I, sum_neg, neg_neg, neg_neg] at h2
    exact h2
  · intro h θ hθ
    have h1 := map_star_mem_K hθ
    rw [map_star_diag] at h1
    have h2 := h (-θ) h1
    show σ ((Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).map star) (ConjSp.out v) =
        starRingEnd ℂ (Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I)) • ConjSp.out v
    rw [map_star_diag, star_exp_mul_I, ← sum_neg]
    exact h2

/- English proof (translation)
Take `⟨⟨h1, h2⟩, h3, h4⟩` from `h`. Use `⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => h3 _ (map_star_mem_UJ hg) (ConjSp.out v), fun v => ?_⟩` and prove the remaining obligations. Use extensionality with `v show σ ((1 : Matrix (Fin k) (Fin k) ℂ).map star) (ConjSp.out v) = ConjSp.out v`. Rewrite using `[map_star_one, h1]`. Both sides reduce to the same expression.

Use extensionality with `v show σ ((a * b).map star) (ConjSp.out v) = σ (a.map star) (σ (b.map star) (ConjSp.out v))`. Rewrite using `[map_star_mul, h2 _ (map_star_mem_UJ ha) _ (map_star_mem_UJ hb)]`. Both sides reduce to the same expression. Establish `hc : Continuous fun g : Matrix (Fin k) (Fin k) ℂ => g.map star` using `continuous_id.matrix_map continuous_star`. Conclude with `(h4 (ConjSp.out v)).comp hc.continuousOn fun g hg => map_star_mem_UJ hg`.
-/
theorem isURepOn_conjRep {ε : Fin k → Bool} {σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}
    (h : IsURepOn (UJset ε) σ) : IsURepOn (UJset ε) (conjRep σ) := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := h
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => h3 _ (map_star_mem_UJ hg) (ConjSp.out v), fun v => ?_⟩
  · ext v
    show σ ((1 : Matrix (Fin k) (Fin k) ℂ).map star) (ConjSp.out v) = ConjSp.out v
    rw [map_star_one, h1]; rfl
  · ext v
    show σ ((a * b).map star) (ConjSp.out v) = σ (a.map star) (σ (b.map star) (ConjSp.out v))
    rw [map_star_mul, h2 _ (map_star_mem_UJ ha) _ (map_star_mem_UJ hb)]; rfl
  · have hc : Continuous fun g : Matrix (Fin k) (Fin k) ℂ => g.map star :=
      continuous_id.matrix_map continuous_star
    exact (h4 (ConjSp.out v)).comp hc.continuousOn fun g hg => map_star_mem_UJ hg

/- English proof (translation)
Take `⟨-, -, h3, ⟨v, -, hv0, hv⟩, h5⟩` from `h`. Use `⟨inferInstance, fun _ _ _ _ => trivial, fun S _ hS => ?_, ⟨ConjSp.mk v, trivial, hv0, (isWtOn_conjRep_iff ε σ Λ _).2 hv⟩, fun μ w _ hw0 hw => h5 μ (ConjSp.out w) trivial hw0 ((isWtOn_conjRep_iff ε σ μ w).1 hw)⟩` and prove the remaining obligations. Establish `hst : IsKStableOn ε σ (ConjSp.unsub S)`. Introduce `g hg w hw`. Establish `h1 : ConjSp.mk (σ ((g.map star).map star) w) ∈ S` using `hS _ (map_star_mem_K hg) (ConjSp.mk w) hw`.

Rewrite `h1` using `[map_star_star]`. Conclude with `h1`. Break down `h3 _ le_top hst with h0 | h0` into its components or cases. Use `left`. Rewrite using `[eq_bot_iff]`.

Introduce `w hw`. Establish `: ConjSp.out w ∈ ConjSp.unsub S` using `hw`. Rewrite `this` using `[h0]`. Conclude with `this`. Use `right`.

Rewrite using `[eq_top_iff]`. Introduce `w _`. Establish `: ConjSp.out w ∈ ConjSp.unsub S` using `by rw [h0]; trivial`. Conclude with `this`.
-/
theorem isKTypeOf_conjRep [FiniteDimensional ℂ H] {ε : Fin k → Bool} {σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}
    {Λ : Fin k → ℝ} (h : IsKTypeOf ε σ Λ ⊤) : IsKTypeOf ε (conjRep σ) Λ ⊤ := by
  obtain ⟨-, -, h3, ⟨v, -, hv0, hv⟩, h5⟩ := h
  refine ⟨inferInstance, fun _ _ _ _ => trivial, fun S _ hS => ?_,
    ⟨ConjSp.mk v, trivial, hv0, (isWtOn_conjRep_iff ε σ Λ _).2 hv⟩,
    fun μ w _ hw0 hw => h5 μ (ConjSp.out w) trivial hw0 ((isWtOn_conjRep_iff ε σ μ w).1 hw)⟩
  have hst : IsKStableOn ε σ (ConjSp.unsub S) := by
    intro g hg w hw
    have h1 : ConjSp.mk (σ ((g.map star).map star) w) ∈ S := hS _ (map_star_mem_K hg) (ConjSp.mk w) hw
    rw [map_star_star] at h1
    exact h1
  rcases h3 _ le_top hst with h0 | h0
  · left
    rw [eq_bot_iff]
    intro w hw
    have : ConjSp.out w ∈ ConjSp.unsub S := hw
    rw [h0] at this
    exact this
  · right
    rw [eq_top_iff]
    intro w _
    have : ConjSp.out w ∈ ConjSp.unsub S := by rw [h0]; trivial
    exact this

/- English proof (translation)
Introduce `k Λ H _ _ _ σ h1 h2`. Conclude with `⟨ConjSp H, inferInstance, inferInstance, inferInstance, conjRep σ, ConjSp.mkL H, Function.bijective_id, isURepOn_conjRep h1, isKTypeOf_conjRep h2, fun _ _ => rfl⟩`.
-/
theorem exists_conjugate_type : ∀ (k : ℕ) (Λ : Fin k → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), IsURepOn (UJset (allPos k)) σ → IsKTypeOf (allPos k) σ Λ ⊤ → ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : InnerProductSpace ℂ E) (_ : FiniteDimensional ℂ E) (π : Matrix (Fin k) (Fin k) ℂ → (E →L[ℂ] E)) (J : H →ₛₗ[starRingEnd ℂ] E), Function.Bijective J ∧ IsURepOn (UJset (allPos k)) π ∧ IsKTypeOf (allPos k) π Λ ⊤ ∧ ∀ g u, π g (J u) = J (σ (g.map star) u) := by
  intro k Λ H _ _ _ σ h1 h2
  exact ⟨ConjSp H, inferInstance, inferInstance, inferInstance, conjRep σ, ConjSp.mkL H,
    Function.bijective_id, isURepOn_conjRep h1, isKTypeOf_conjRep h2, fun _ _ => rfl⟩

end GlobalTheory.ConjugateType
