import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom

section Conj

variable {k r : ℕ}

def cjm (M : Formalism.QuantumDeterminants.Mt k r) : Formalism.QuantumDeterminants.Mt k r := fun i j => star (M i j)

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `[cjm]`.
-/
theorem cjm_cjm (M : Formalism.QuantumDeterminants.Mt k r) : cjm (cjm M) = M := by
  funext i j; simp [cjm]

/- English proof (translation)
Unfold `cjm`. Use `fun_prop`.
-/
theorem measurable_cjm : Measurable (cjm : Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r) := by
  unfold cjm; fun_prop

def cjmE : Formalism.QuantumDeterminants.Mt k r ≃ᵐ Formalism.QuantumDeterminants.Mt k r where
  toFun := cjm
  invFun := cjm
  left_inv := cjm_cjm
  right_inv := cjm_cjm
  measurable_toFun := measurable_cjm
  measurable_invFun := measurable_cjm

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_star_eq (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : X.map star = Xᴴᵀ := by
  ext i j; simp

/- English proof (translation)
Rewrite using `[map_star_eq, map_star_eq, Matrix.exp_transpose, Matrix.exp_conjTranspose]`.
-/
theorem exp_map_star (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (X.map star) = (NormedSpace.exp X).map star := by
  rw [map_star_eq, map_star_eq, Matrix.exp_transpose, Matrix.exp_conjTranspose]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`. Unfold `Formalism.QuantumDeterminants.Hpk`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem Hpk_map_star : (Formalism.QuantumDeterminants.Hpk k r).map star = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.map_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hg`. Use `⟨?_, fun a i hi => ?_, fun i j a b c => ?_⟩` and prove the remaining obligations. Establish `h1' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r` using `h1 show (g.map star)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g.map star = Formalism.QuantumDeterminants.Hpk k r`. Establish `e : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, M.map star = M.map (starRingEnd ℂ)`. Introduce `M`.

Both sides reduce to the same expression. Establish `hc : (g.map star)ᴴ = gᴴ.map star` using `by ext i j; simp`. Rewrite using `[hc, ← Hpk_map_star, e, e, e, ← Matrix.map_mul, ← Matrix.map_mul, h1']`. Apply the tactic sequence `simp only [Matrix.map_apply, h2 a i hi]; split_ifs <;> simp`. Apply the tactic sequence `simp only [Matrix.map_apply, h3 i j a b c]; split_ifs <;> simp`.
-/
theorem map_star_mem_N {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.Nset k r) : g.map star ∈ Formalism.QuantumDeterminants.Nset k r := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨?_, fun a i hi => ?_, fun i j a b c => ?_⟩
  · have h1' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := h1
    show (g.map star)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g.map star = Formalism.QuantumDeterminants.Hpk k r
    have e : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, M.map star = M.map (starRingEnd ℂ) := by
      intro M; rfl
    have hc : (g.map star)ᴴ = gᴴ.map star := by ext i j; simp
    rw [hc, ← Hpk_map_star, e, e, e, ← Matrix.map_mul, ← Matrix.map_mul, h1']
  · simp only [Matrix.map_apply, h2 a i hi]; split_ifs <;> simp
  · simp only [Matrix.map_apply, h3 i j a b c]; split_ifs <;> simp

end Conj

section Conj2
variable {k r : ℕ}

def cjR (m : ℕ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := (WithLp.equiv 2 _).symm (realifyFun ((unrealify x).map star))
  map_add' x y := by
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, unrealify] <;> ring
  map_smul' c x := by
    ext ⟨i, j, b⟩
    cases b <;> simp [realifyFun, unrealify]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[unrealify, realifyFun]`.
-/
theorem unrealify_realify' {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) :
    unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
  ext i j
  simp [unrealify, realifyFun]

/- English proof (translation)
The claim follows from `unrealify_realify' _`.
-/
theorem unrealify_cjR {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (cjR m x) = (unrealify x).map star := unrealify_realify' _

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]`.

Simplify using `only [unrealify, Real.norm_eq_abs, sq_abs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sq_unrealify' {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    ‖x‖ ^ 2 = ∑ i, ∑ j, ‖unrealify x i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [unrealify, Real.norm_eq_abs, sq_abs]
  ring

/- English proof (translation)
Establish `: ‖cjR m x‖ ^ 2 = ‖x‖ ^ 2`. Rewrite using `[norm_sq_unrealify', norm_sq_unrealify', unrealify_cjR]`. Simplify using `only [Matrix.map_apply, norm_star]`. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this`.
-/
theorem norm_cjR {m : ℕ} (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : ‖cjR m x‖ = ‖x‖ := by
  have : ‖cjR m x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [norm_sq_unrealify', norm_sq_unrealify', unrealify_cjR]
    simp only [Matrix.map_apply, norm_star]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/- English proof (translation)
Introduce `x hx`. Establish `: lieE S ≤ (lieE S).comap (cjR (2 * r + k + 1))`. Unfold `lieE`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨X, hX, rfl⟩`.

Use `Submodule.subset_span ⟨X.map star, fun t => ?_, ?_⟩` and prove the remaining obligations. Establish `e : ((t : ℂ) • X.map star) = ((t : ℂ) • X).map star`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[e, exp_map_star]`.

Conclude with `hS _ (hX t)`. Use `show _ = (WithLp.equiv 2 _).symm (realifyFun ((unrealify _).map star))`. Rewrite using `[unrealify_realify']`. Conclude with `this hx`.
-/
theorem cjR_mem {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) : ∀ x ∈ lieE S, cjR (2 * r + k + 1) x ∈ lieE S := by
  intro x hx
  have : lieE S ≤ (lieE S).comap (cjR (2 * r + k + 1)) := by
    unfold lieE
    rw [Submodule.span_le]
    rintro _ ⟨X, hX, rfl⟩
    refine Submodule.subset_span ⟨X.map star, fun t => ?_, ?_⟩
    · have e : ((t : ℂ) • X.map star) = ((t : ℂ) • X).map star := by
        ext i j; simp
      rw [e, exp_map_star]; exact hS _ (hX t)
    · show _ = (WithLp.equiv 2 _).symm (realifyFun ((unrealify _).map star))
      rw [unrealify_realify']
  exact this hx

/- English proof (translation)
Use `show ‖cjR (2 * r + k + 1) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ = ‖(x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖`. Conclude with `norm_cjR _`.
-/
theorem norm_cjR_restrict {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) (x : lieE S) :
    ‖(cjR (2 * r + k + 1)).restrict (cjR_mem hS) x‖ = ‖x‖ := by
  show ‖cjR (2 * r + k + 1) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ =
    ‖(x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖
  exact norm_cjR _

/- English proof (translation)
Unfold `haarLie`. Rewrite using `[Measure.map_smul]`. Use `congr 1`. Use `set E : lieE S → Formalism.QuantumDeterminants.Mt k r := fun x => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j with hE`. Distinguish the cases in `hm : AEMeasurable E volume`.

Set `Φ₀ : lieE S →ₗᵢ[ℝ] lieE S` to `⟨(cjR (2 * r + k + 1)).restrict (cjR_mem hS), norm_cjR_restrict hS⟩`. Set `Φ : lieE S ≃ₗᵢ[ℝ] lieE S` to `Φ₀.toLinearIsometryEquiv rfl`. Establish `hΦ` using `Φ.measurePreserving`. Establish `e : (cjmE (k` using `k) (r := r)) ∘ E = E ∘ Φ := by`. Use function extensionality and compare the values at `x`.

Use `show cjm (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) = fun i j => NormedSpace.exp (unrealify (cjR (2 * r + k + 1) x)) i j`. Rewrite using `[unrealify_cjR, exp_map_star]`. Both sides reduce to the same expression. Rewrite using `[AEMeasurable.map_map_of_aemeasurable (cjmE (k := k) (r := r)).measurable.aemeasurable hm, e, ← AEMeasurable.map_map_of_aemeasurable (by rwa [hΦ.map_eq]) hΦ.measurable.aemeasurable, hΦ.map_eq]`. Rewrite using `[Measure.map_of_not_aemeasurable hm, Measure.map_zero]`.
-/
theorem haarLie_map_cjm {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hS : ∀ g ∈ S, g.map star ∈ S) (κ : ENNReal) : (haarLie S κ).map (cjmE (k := k) (r := r)) = haarLie S κ := by
  unfold haarLie
  rw [Measure.map_smul]
  congr 1
  set E : lieE S → Formalism.QuantumDeterminants.Mt k r := fun x => fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j with hE
  by_cases hm : AEMeasurable E volume
  · let Φ₀ : lieE S →ₗᵢ[ℝ] lieE S := ⟨(cjR (2 * r + k + 1)).restrict (cjR_mem hS), norm_cjR_restrict hS⟩
    let Φ : lieE S ≃ₗᵢ[ℝ] lieE S := Φ₀.toLinearIsometryEquiv rfl
    have hΦ := Φ.measurePreserving
    have e : (cjmE (k := k) (r := r)) ∘ E = E ∘ Φ := by
      funext x
      show cjm (fun i j => NormedSpace.exp (unrealify (x : EuclideanSpace ℝ _)) i j) =
        fun i j => NormedSpace.exp (unrealify (cjR (2 * r + k + 1) x)) i j
      rw [unrealify_cjR, exp_map_star]
      rfl
    rw [AEMeasurable.map_map_of_aemeasurable (cjmE (k := k) (r := r)).measurable.aemeasurable hm, e,
      ← AEMeasurable.map_map_of_aemeasurable (by rwa [hΦ.map_eq]) hΦ.measurable.aemeasurable, hΦ.map_eq]
  · rw [Measure.map_of_not_aemeasurable hm, Measure.map_zero]

end Conj2

section Places

variable (D : D7)

def plE : D.what₂.Tau ≃ InfinitePlace D.host.E :=
  Equiv.ofBijective (fun τ => InfinitePlace.mk (embS D τ))
    ((Function.bijective_iff_existsUnique _).2 (GlobalTheory.RealPlaces.existsUnique_place D))

/- English proof (translation)
The claim follows from `(GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec`.
-/
theorem plE_tauOf (w : InfinitePlace D.host.E) : plE D (tauOf D w) = w :=
  (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec

/- English proof (translation)
Rewrite using `[Equiv.eq_symm_apply, plE_tauOf]`.
-/
theorem tauOf_eq (w : InfinitePlace D.host.E) : tauOf D w = (plE D).symm w := by
  rw [Equiv.eq_symm_apply, plE_tauOf]

def cjwE (w : InfinitePlace D.host.E) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS ≃ᵐ Formalism.QuantumDeterminants.Mt D.R.k D.R.rS :=
  if Direct D w then MeasurableEquiv.refl _ else cjmE

/- English proof (translation)
Unfold `cjwE cjw`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem cjwE_apply (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) : cjwE D w M = cjw D w M := by
  unfold cjwE cjw
  split_ifs <;> rfl

def GmE : (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) ≃ᵐ (InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :=
  (MeasurableEquiv.piCongrLeft (fun _ => Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) (plE D)).trans
    (MeasurableEquiv.piCongrRight (fun w => cjwE D w))

/- English proof (translation)
Use function extensionality and compare the values at `y w`. Use `show cjwE D w ((MeasurableEquiv.piCongrLeft (fun _ => Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) (plE D)) y w) = _`. Simplify using `only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, cjwE_apply, Gm, tauOf_eq, eq_rec_constant]`.
-/
theorem coe_GmE : ⇑(GmE D) = Gm D := by
  funext y w
  show cjwE D w ((MeasurableEquiv.piCongrLeft (fun _ => Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) (plE D)) y w) = _
  simp only [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, cjwE_apply, Gm, tauOf_eq, eq_rec_constant]

/- English proof (translation)
Unfold `cjwE`. Use `split_ifs`. Conclude with `MeasurePreserving.id _`. Conclude with `⟨(cjmE).measurable, haarLie_map_cjm (fun g hg => map_star_mem_N hg) 1⟩`.
-/
theorem cjwE_mp (w : InfinitePlace D.host.E) :
    MeasurePreserving (cjwE D w) (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) := by
  unfold cjwE
  split_ifs
  · exact MeasurePreserving.id _
  · exact ⟨(cjmE).measurable, haarLie_map_cjm (fun g hg => map_star_mem_N hg) 1⟩

/- English proof (translation)
Use `haveI : SigmaFinite (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) := (GlobalTheory.haarLie_isHaarOn_Nset D.R.k D.R.rS 1 one_pos ENNReal.one_lt_top).1`. Establish `h1` using `measurePreserving_piCongrLeft (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (plE D)`. Establish `h2` using `measurePreserving_pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (cjwE_mp D)`. Conclude with `h2.comp h1`.
-/
theorem GmE_mp : MeasurePreserving (GmE D)
    (Measure.pi fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1)
    (Measure.pi fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) := by
  haveI : SigmaFinite (haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) :=
    (GlobalTheory.haarLie_isHaarOn_Nset D.R.k D.R.rS 1 one_pos ENNReal.one_lt_top).1
  have h1 := measurePreserving_piCongrLeft (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (plE D)
  have h2 := measurePreserving_pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1)
    (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (cjwE_mp D)
  exact h2.comp h1

end Places

/- English proof (translation)
Introduce `D S`. Rewrite using `[← coe_GmE, MeasurableEquiv.image_eq_preimage_symm, ← MeasurableEquiv.map_apply, (GmE_mp D).symm.map_eq]`.
-/
theorem measure_Gm_image : ∀ (D : D7) (S : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
    Measure.pi (fun _ : InfinitePlace D.host.E => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) (Gm D '' S) =
      Measure.pi (fun _ : D.what₂.Tau => haarLie (Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) 1) S := by
  intro D S
  rw [← coe_GmE, MeasurableEquiv.image_eq_preimage_symm, ← MeasurableEquiv.map_apply, (GmE_mp D).symm.map_eq]

end GlobalTheory.CovDom
