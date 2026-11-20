import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open Complex
open scoped ComplexConjugate

namespace GlobalTheory.Ker.CreOp

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

noncomputable def holD (v : W) (Φ : W → ℂ) (z : W) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))

/- English proof (translation)
The claim follows from `(contDiff_infty_iff_fderiv.1 h).2.clm_apply contDiff_const`.
-/
theorem contDiff_fderiv_apply {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : W) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => fderiv ℝ Φ z v := (contDiff_infty_iff_fderiv.1 h).2.clm_apply contDiff_const

/- English proof (translation)
Use `show ContDiff ℝ _ fun z => (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))`. Conclude with `contDiff_const.mul ((contDiff_fderiv_apply h v).sub (contDiff_const.mul (contDiff_fderiv_apply h (I • v))))`.
-/
theorem contDiff_holD {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (v : W) :
    ContDiff ℝ (⊤ : ℕ∞) (holD v Φ) := by
  show ContDiff ℝ _ fun z => (1 / 2 : ℂ) * (fderiv ℝ Φ z v - I * fderiv ℝ Φ z (I • v))
  exact contDiff_const.mul
    ((contDiff_fderiv_apply h v).sub (contDiff_const.mul (contDiff_fderiv_apply h (I • v))))

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `hs : HasFDerivAt (fun y => Φ y + Ψ y) (fderiv ℝ Φ z + fderiv ℝ Ψ z) z` using `(h z).hasFDerivAt.add (h' z).hasFDerivAt`. Simplify using `only [holD, hs.fderiv, ContinuousLinearMap.add_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem holD_add {Φ Ψ : W → ℂ} (h : Differentiable ℝ Φ) (h' : Differentiable ℝ Ψ) (v : W) :
    holD v (fun z => Φ z + Ψ z) = fun z => holD v Φ z + holD v Ψ z := by
  funext z
  have hs : HasFDerivAt (fun y => Φ y + Ψ y) (fderiv ℝ Φ z + fderiv ℝ Ψ z) z :=
    (h z).hasFDerivAt.add (h' z).hasFDerivAt
  simp only [holD, hs.fderiv, ContinuousLinearMap.add_apply]
  ring

/- English proof (translation)
Establish `hr : ∀ (r : ℝ) (a : W), lam (r • a) = r • lam a`. Introduce `r a`. Rewrite using `[RCLike.real_smul_eq_coe_smul (K := ℂ) r a, h2]`. Simplify using `[Complex.real_smul]`. Establish `: FiniteDimensional ℝ W` using `Module.Finite.trans ℂ W`.

Conclude with `⟨LinearMap.toContinuousLinearMap ({ toFun := lam, map_add' := h1, map_smul' := fun r a => by rw [RingHom.id_apply]; exact hr r a } : W →ₗ[ℝ] ℂ), rfl⟩`.
-/
theorem exists_clm_of_antilinear [FiniteDimensional ℂ W] {lam : W → ℂ}
    (h1 : ∀ a b, lam (a + b) = lam a + lam b) (h2 : ∀ (t : ℂ) a, lam (t • a) = conj t * lam a) :
    ∃ T : W →L[ℝ] ℂ, lam = T := by
  have hr : ∀ (r : ℝ) (a : W), lam (r • a) = r • lam a := by
    intro r a
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) r a, h2]
    simp [Complex.real_smul]
  have : FiniteDimensional ℝ W := Module.Finite.trans ℂ W
  exact ⟨LinearMap.toContinuousLinearMap
    ({ toFun := lam, map_add' := h1, map_smul' := fun r a => by rw [RingHom.id_apply]; exact hr r a }
      : W →ₗ[ℝ] ℂ), rfl⟩

/- English proof (translation)
Use function extensionality and compare the values at `z`. Establish `hT : HasFDerivAt (fun y => T y * Φ y) (T z • fderiv ℝ Φ z + Φ z • T) z` using `T.hasFDerivAt.mul (h z).hasFDerivAt`. Simplify using `only [holD, hT.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, h2]`. Take the linear combination `(1 / 2 : ℂ) * Φ z * T v * I_sq`.
-/
theorem holD_mul (T : W →L[ℝ] ℂ) (h2 : ∀ a, T (I • a) = -I * T a) {Φ : W → ℂ}
    (h : Differentiable ℝ Φ) (v : W) :
    holD v (fun z => T z * Φ z) = fun z => T z * holD v Φ z := by
  funext z
  have hT : HasFDerivAt (fun y => T y * Φ y) (T z • fderiv ℝ Φ z + Φ z • T) z :=
    T.hasFDerivAt.mul (h z).hasFDerivAt
  simp only [holD, hT.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, h2]
  linear_combination (1 / 2 : ℂ) * Φ z * T v * I_sq

/- English proof (translation)
Establish `e : fderiv ℝ Φ z = (fderiv ℂ Φ z).restrictScalars ℝ` using `h.fderiv_restrictScalars ℝ`. Simplify using `only [holD, e, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul, smul_eq_mul]`. Take the linear combination `(-(1 / 2) : ℂ) * fderiv ℂ Φ z v * I_sq`.
-/
theorem holD_of_differentiableAt {Φ : W → ℂ} {z : W} (h : DifferentiableAt ℂ Φ z) (v : W) :
    holD v Φ z = fderiv ℂ Φ z v := by
  have e : fderiv ℝ Φ z = (fderiv ℂ Φ z).restrictScalars ℝ := h.fderiv_restrictScalars ℝ
  simp only [holD, e, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.map_smul,
    smul_eq_mul]
  linear_combination (-(1 / 2) : ℂ) * fderiv ℂ Φ z v * I_sq

variable {σ : Type} (u : σ → W)

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `nil => exact h`. Consider the case `cons l M ih => exact contDiff_holD ih (u l)`.
-/
theorem contDiff_foldr_holD {Φ : W → ℂ} (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (M : List σ) :
    ContDiff ℝ (⊤ : ℕ∞) (M.foldr (fun l => holD (u l)) Φ) := by
  induction M with
  | nil => exact h
  | cons l M ih => exact contDiff_holD ih (u l)

/- English proof (translation)
Establish `hθ' : ContDiff ℂ ⊤ θ` using `GlobalTheory.SCV.contDiff_of_differentiable hθ ⊤`. Proceed by induction on `M with`. Consider the case `nil => funext z`. Simplify using the standard rewrite rules. Consider the case `cons l M ih`.

Establish `hA : Differentiable ℂ (iteratedFDeriv ℂ M.length θ)` using `hθ'.differentiable_iteratedFDeriv (WithTop.coe_lt_top _)`. Use function extensionality and compare the values at `z`. Simplify using `only [List.foldr_cons]`. Rewrite using `[ih, holD_of_differentiableAt ((hA z).continuousMultilinear_apply_const _), fderiv_continuousMultilinear_apply_const_apply (hA z)]`. Both sides reduce to the same expression.
-/
theorem foldr_holD_eq_iteratedFDeriv [FiniteDimensional ℂ W] {θ : W → ℂ}
    (hθ : Differentiable ℂ θ) (M : List σ) :
    M.foldr (fun l => holD (u l)) θ =
      fun z => iteratedFDeriv ℂ M.length θ z fun k => u (M.get k) := by
  have hθ' : ContDiff ℂ ⊤ θ := GlobalTheory.SCV.contDiff_of_differentiable hθ ⊤
  induction M with
  | nil => funext z; simp
  | cons l M ih =>
    have hA : Differentiable ℂ (iteratedFDeriv ℂ M.length θ) :=
      hθ'.differentiable_iteratedFDeriv (WithTop.coe_lt_top _)
    funext z
    simp only [List.foldr_cons]
    rw [ih, holD_of_differentiableAt ((hA z).continuousMultilinear_apply_const _),
      fderiv_continuousMultilinear_apply_const_apply (hA z)]
    rfl

/- English proof (translation)
Proceed by induction on `R with`. Consider the case `nil`. Simplify using `only [List.map_nil, List.sum_nil]`. Conclude with `contDiff_const`. Consider the case `cons p R ih`.

Simplify using `only [List.map_cons, List.sum_cons]`. Conclude with `(p.1.contDiff.mul (hR p (by simp))).add (ih fun q hq => hR q (by simp [hq]))`.
-/
private theorem contDiff_list_sum_mul (R : List ((W →L[ℝ] ℂ) × (W → ℂ)))
    (hR : ∀ p ∈ R, ContDiff ℝ (⊤ : ℕ∞) p.2) :
    ContDiff ℝ (⊤ : ℕ∞) fun z => (R.map fun p => p.1 z * p.2 z).sum := by
  induction R with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    exact contDiff_const
  | cons p R ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (p.1.contDiff.mul (hR p (by simp))).add (ih fun q hq => hR q (by simp [hq]))

/- English proof (translation)
Proceed by induction on `R with`. Consider the case `nil => funext z`. Simplify using `[holD]`. Consider the case `cons p R ih`. Establish `hp` using `hR p (by simp)`.

Establish `hR' : ∀ q ∈ R, (∀ a, q.1 (I • a) = -I * q.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) q.2` using `fun q hq => hR q (by simp [hq])`. Establish `hS` using `contDiff_list_sum_mul R fun q hq => (hR' q hq).2`. Establish `hd : Differentiable ℝ p.2` using `(contDiff_infty_iff_fderiv.1 hp.2).1`. Simplify using `only [List.map_cons, List.sum_cons]`. Rewrite using `[holD_add (show Differentiable ℝ fun z => p.1 z * p.2 z from p.1.differentiable.mul hd) (contDiff_infty_iff_fderiv.1 hS).1, holD_mul p.1 hp.1 hd, ih hR']`.
-/
private theorem holD_list_sum_mul (R : List ((W →L[ℝ] ℂ) × (W → ℂ)))
    (hR : ∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) (v : W) :
    holD v (fun z => (R.map fun p => p.1 z * p.2 z).sum) =
      fun z => (R.map fun p => p.1 z * holD v p.2 z).sum := by
  induction R with
  | nil => funext z; simp [holD]
  | cons p R ih =>
    have hp := hR p (by simp)
    have hR' : ∀ q ∈ R, (∀ a, q.1 (I • a) = -I * q.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) q.2 :=
      fun q hq => hR q (by simp [hq])
    have hS := contDiff_list_sum_mul R fun q hq => (hR' q hq).2
    have hd : Differentiable ℝ p.2 := (contDiff_infty_iff_fderiv.1 hp.2).1
    simp only [List.map_cons, List.sum_cons]
    rw [holD_add (show Differentiable ℝ fun z => p.1 z * p.2 z from p.1.differentiable.mul hd)
      (contDiff_infty_iff_fderiv.1 hS).1,
      holD_mul p.1 hp.1 hd, ih hR']

/- English proof (translation)
Introduce `σ W _ _ _ u lam θ hlam hθ Dl hDl L`. Use `choose T hT using fun l => exists_clm_of_antilinear (hlam l).1 (hlam l).2`. Establish `hTI : ∀ l a, T l (I • a) = -I * T l a`. Introduce `l a`. Rewrite using `[← hT l, (hlam l).2, Complex.conj_I]`.

Establish `hθs : ContDiff ℝ (⊤ : ℕ∞) θ` using `(GlobalTheory.SCV.contDiff_of_differentiable hθ _).restrict_scalars ℝ`. Establish `step : ∀ l Φ, Dl l Φ = fun z => T l z * Φ z + holD (u l) Φ z`. Introduce `l Φ`. Use function extensionality and compare the values at `z`. Rewrite using `[hDl, ← hT l]`.

Both sides reduce to the same expression. Establish `hsm : ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ)`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => exact hθs`.

Consider the case `cons l L ih`. Simplify using `only [List.foldr_cons]`. Rewrite using `[step]`. Conclude with `((T l).contDiff.mul ih).add (contDiff_holD ih (u l))`. Establish `key : ∀ L : List σ, ∃ R : List ((W →L[ℝ] ℂ) × (W → ℂ)), (∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) ∧ L.foldr Dl θ = fun z => L.foldr (fun l => holD (u l)) θ z + (R.map fun p => p.1 z * p.2 z).sum`.

Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => exact ⟨[], by simp, by funext z; simp⟩`. Consider the case `cons l L ih`. Take `⟨R, hR, hE⟩` from `ih`.

Use `⟨(T l, L.foldr Dl θ) :: R.map (fun p => (p.1, holD (u l) p.2)), ?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [List.mem_cons, List.mem_map] at hp`. Break down `hp with rfl | ⟨q, hq, rfl⟩` into its components or cases. Conclude with `⟨hTI l, hsm L⟩`.

Conclude with `⟨(hR q hq).1, contDiff_holD (hR q hq).2 (u l)⟩`. Establish `hD` using `contDiff_foldr_holD u hθs L`. Establish `hS` using `contDiff_list_sum_mul R fun p hp => (hR p hp).2`. Establish `e : holD (u l) (L.foldr Dl θ) = fun z => holD (u l) (L.foldr (fun l => holD (u l)) θ) z + (R.map fun p => p.1 z * holD (u l) p.2 z).sum`. Rewrite using `[hE, holD_add (contDiff_infty_iff_fderiv.1 hD).1 (contDiff_infty_iff_fderiv.1 hS).1, holD_list_sum_mul R hR (u l)]`.

Use function extensionality and compare the values at `z`. Simplify using `only [List.foldr_cons, step, e, List.map_cons, List.map_map, List.sum_cons, Function.comp_def]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨hsm L, ?_⟩` and prove the remaining obligations. Take `⟨R, -, hE⟩` from `key L`.

Establish `h0 : (R.map fun p => p.1 0 * p.2 0).sum = 0` using `List.sum_eq_zero fun x hx => by`. Take `⟨p, -, rfl⟩` from `List.mem_map.1 hx`. Simplify using the standard rewrite rules. Rewrite using `[hE]`. Simplify using `only [h0, add_zero]`.

Rewrite using `[foldr_holD_eq_iteratedFDeriv u hθ L]`.
-/
theorem foldr_creation_zero : ∀ (σ W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (u : σ → W) (lam : σ → W → ℂ) (θ : W → ℂ),
    (∀ l, (∀ a b, lam l (a + b) = lam l a + lam l b) ∧
      ∀ (t : ℂ) a, lam l (t • a) = conj t * lam l a) → Differentiable ℂ θ →
    ∀ Dl : σ → (W → ℂ) → W → ℂ,
      (∀ l Φ z, Dl l Φ z = lam l z * Φ z +
        (1 / 2 : ℂ) * (fderiv ℝ Φ z (u l) - I * fderiv ℝ Φ z (I • u l))) →
      ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) ∧
        L.foldr Dl θ 0 = iteratedFDeriv ℂ L.length θ 0 fun k => u (L.get k) := by
  intro σ W _ _ _ u lam θ hlam hθ Dl hDl L
  choose T hT using fun l => exists_clm_of_antilinear (hlam l).1 (hlam l).2
  have hTI : ∀ l a, T l (I • a) = -I * T l a := by
    intro l a
    rw [← hT l, (hlam l).2, Complex.conj_I]
  have hθs : ContDiff ℝ (⊤ : ℕ∞) θ :=
    (GlobalTheory.SCV.contDiff_of_differentiable hθ _).restrict_scalars ℝ
  have step : ∀ l Φ, Dl l Φ = fun z => T l z * Φ z + holD (u l) Φ z := by
    intro l Φ
    funext z
    rw [hDl, ← hT l]
    rfl
  have hsm : ∀ L : List σ, ContDiff ℝ (⊤ : ℕ∞) (L.foldr Dl θ) := by
    intro L
    induction L with
    | nil => exact hθs
    | cons l L ih =>
      simp only [List.foldr_cons]
      rw [step]
      exact ((T l).contDiff.mul ih).add (contDiff_holD ih (u l))
  have key : ∀ L : List σ, ∃ R : List ((W →L[ℝ] ℂ) × (W → ℂ)),
      (∀ p ∈ R, (∀ a, p.1 (I • a) = -I * p.1 a) ∧ ContDiff ℝ (⊤ : ℕ∞) p.2) ∧
      L.foldr Dl θ = fun z =>
        L.foldr (fun l => holD (u l)) θ z + (R.map fun p => p.1 z * p.2 z).sum := by
    intro L
    induction L with
    | nil => exact ⟨[], by simp, by funext z; simp⟩
    | cons l L ih =>
      obtain ⟨R, hR, hE⟩ := ih
      refine ⟨(T l, L.foldr Dl θ) :: R.map (fun p => (p.1, holD (u l) p.2)), ?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons, List.mem_map] at hp
        rcases hp with rfl | ⟨q, hq, rfl⟩
        · exact ⟨hTI l, hsm L⟩
        · exact ⟨(hR q hq).1, contDiff_holD (hR q hq).2 (u l)⟩
      · have hD := contDiff_foldr_holD u hθs L
        have hS := contDiff_list_sum_mul R fun p hp => (hR p hp).2
        have e : holD (u l) (L.foldr Dl θ) = fun z =>
            holD (u l) (L.foldr (fun l => holD (u l)) θ) z +
              (R.map fun p => p.1 z * holD (u l) p.2 z).sum := by
          rw [hE, holD_add (contDiff_infty_iff_fderiv.1 hD).1 (contDiff_infty_iff_fderiv.1 hS).1,
            holD_list_sum_mul R hR (u l)]
        funext z
        simp only [List.foldr_cons, step, e, List.map_cons, List.map_map, List.sum_cons,
          Function.comp_def]
        ring
  refine ⟨hsm L, ?_⟩
  obtain ⟨R, -, hE⟩ := key L
  have h0 : (R.map fun p => p.1 0 * p.2 0).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
      simp
  rw [hE]
  simp only [h0, add_zero]
  rw [foldr_holD_eq_iteratedFDeriv u hθ L]

end GlobalTheory.Ker.CreOp
