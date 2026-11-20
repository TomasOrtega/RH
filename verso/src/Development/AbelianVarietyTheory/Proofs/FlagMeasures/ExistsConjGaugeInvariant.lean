import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MuGPreimageConj

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

def innerAutTop {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (s : G) : G ≃ₜ* G :=
  { MulAut.conj s with
    continuous_toFun := by
      change Continuous fun g : G => s * g * s⁻¹
      fun_prop
    continuous_invFun := by
      change Continuous fun g : G => s⁻¹ * g * s
      fun_prop }

/- English proof (translation)
Unfold `Formalism.REAL.inUJ at hg ⊢`. Establish `hJ : (Formalism.REAL.Jm ε).map (starRingEnd ℂ) = Formalism.REAL.Jm ε`. Use extensionality with `i j`. Simplify using `only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hH : (g.map (starRingEnd ℂ))ᴴ = gᴴ.map (starRingEnd ℂ)`. Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply]`. Establish `h2` using `congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)) hg`. Simplify using `only [Matrix.map_mul, hJ] at h2`.

Rewrite using `[hH]`. Conclude with `h2`.
-/
theorem inUJ_map_conj {n : ℕ} (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.inUJ ε (g.map (starRingEnd ℂ)) := by
  unfold Formalism.REAL.inUJ at hg ⊢
  have hJ : (Formalism.REAL.Jm ε).map (starRingEnd ℂ) = Formalism.REAL.Jm ε := by
    ext i j
    simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
    split_ifs <;> simp
  have hH : (g.map (starRingEnd ℂ))ᴴ = gᴴ.map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)) hg
  simp only [Matrix.map_mul, hJ] at h2
  rw [hH]
  exact h2

noncomputable def conjUJHom {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε →* Formalism.REAL.UJ ε :=
  ((Units.map ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom).comp (Formalism.REAL.UJ ε).subtype).codRestrict
    (Formalism.REAL.UJ ε) fun g => inUJ_map_conj ε g.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem uMat_conjUJHom {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) :
    uMat (conjUJHom ε g) = (uMat g).map (starRingEnd ℂ) := rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show uMat (conjUJHom ε (conjUJHom ε g)) = uMat g`. Rewrite using `[uMat_conjUJHom, uMat_conjUJHom]`. Use extensionality with `i j`.

Simplify using the standard rewrite rules.
-/
theorem conjUJHom_invol {n : ℕ} (ε : Fin n → Bool) (g : Formalism.REAL.UJ ε) : conjUJHom ε (conjUJHom ε g) = g := by
  apply Subtype.ext
  apply Units.ext
  show uMat (conjUJHom ε (conjUJHom ε g)) = uMat g
  rw [uMat_conjUJHom, uMat_conjUJHom]
  ext i j
  simp

/- English proof (translation)
Establish `hc : Continuous ((starRingEnd ℂ).mapMatrix (m` using `Fin n)).toMonoidHom := by show Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)`. Conclude with `Continuous.matrix_map continuous_id Complex.continuous_conj`. Establish `hu` using `Continuous.units_map _ hc`. Conclude with `Continuous.subtype_mk (hu.comp continuous_subtype_val) _`.
-/
theorem continuous_conjUJHom {n : ℕ} (ε : Fin n → Bool) : Continuous (conjUJHom ε) := by
  have hc : Continuous ((starRingEnd ℂ).mapMatrix (m := Fin n)).toMonoidHom := by
    show Continuous fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)
    exact Continuous.matrix_map continuous_id Complex.continuous_conj
  have hu := Continuous.units_map _ hc
  exact Continuous.subtype_mk (hu.comp continuous_subtype_val) _

noncomputable def conjUJ {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε where
  toFun := conjUJHom ε
  invFun := conjUJHom ε
  left_inv := conjUJHom_invol ε
  right_inv := conjUJHom_invol ε
  map_mul' := map_mul _
  continuous_toFun := continuous_conjUJHom ε
  continuous_invFun := continuous_conjUJHom ε

/- English proof (translation)
Establish `hT : ∀ g, (C.trans (innerAutTop s)) (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) = C g`. Introduce `g`. Use `show s * C (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) * s⁻¹ = C g`. Simplify using `only [map_mul, map_inv, C.apply_symm_apply]`. Use `group`.

Establish `key` using `gauge_map_of_iso n n ε ε rfl (C.trans (innerAutTop s)) (C.symm s⁻¹) (fun g => by rw [hT]; exact hC g) c c hc hc`. Establish `hf : (fun g => s * C g * s⁻¹) = ⇑(C.trans (innerAutTop s))`. Use function extensionality and compare the values at `g`. Both sides reduce to the same expression. Rewrite using `[hf]`.

Conclude with `key`.
-/
theorem gauge_map_inner_comp {n : ℕ} (ε : Fin n → Bool) (C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε)
    (hC : ∀ g, Formalism.REAL.hs (uMat (C g) - 1) = Formalism.REAL.hs (uMat g - 1)) (s : Formalism.REAL.UJ ε) (c : ℝ)
    (hc : IsGauge ε c) :
    (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  have hT : ∀ g, (C.trans (innerAutTop s)) (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) = C g := by
    intro g
    show s * C (C.symm s⁻¹ * g * (C.symm s⁻¹)⁻¹) * s⁻¹ = C g
    simp only [map_mul, map_inv, C.apply_symm_apply]
    group
  have key := gauge_map_of_iso n n ε ε rfl (C.trans (innerAutTop s)) (C.symm s⁻¹)
    (fun g => by rw [hT]; exact hC g) c c hc hc
  have hf : (fun g => s * C g * s⁻¹) = ⇑(C.trans (innerAutTop s)) := by
    funext g
    rfl
  rw [hf]
  exact key

/- English proof (translation)
Introduce `n ε τ hτ`. Break down `hτ with rfl | rfl` into its components or cases. Use `⟨ContinuousMulEquiv.refl _, fun g => ?_, fun s c hc => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Conclude with `gauge_map_inner_comp ε (ContinuousMulEquiv.refl _) (fun g => rfl) s c hc`. Use `⟨conjUJ ε, fun g => uMat_conjUJHom ε g, fun s c hc => ?_⟩` and prove the remaining obligations. Use `gauge_map_inner_comp ε (conjUJ ε) (fun g => ?_) s c hc` and prove the remaining obligations. Establish `h1 : uMat (conjUJ ε g) = (uMat g).map (starRingEnd ℂ)` using `uMat_conjUJHom ε g`. Rewrite using `[h1]`.

Unfold `Formalism.REAL.hs`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e : ((uMat g).map (starRingEnd ℂ) - 1) i j = starRingEnd ℂ ((uMat g - 1) i j)`. Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]`. Use `congr 1`.

Simplify using `only [Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[e, Complex.norm_conj]`.
-/
theorem exists_conj_gauge_invariant : ∀ (n : ℕ) (ε : Fin n → Bool) (τ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → ∃ C : Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε, (∀ g, uMat (C g) = (uMat g).map τ) ∧ ∀ (s : Formalism.REAL.UJ ε) (c : ℝ), IsGauge ε c → (ENNReal.ofReal c • Formalism.REAL.muG ε).map (fun g => s * C g * s⁻¹) = ENNReal.ofReal c • Formalism.REAL.muG ε := by
  intro n ε τ hτ
  rcases hτ with rfl | rfl
  · refine ⟨ContinuousMulEquiv.refl _, fun g => ?_, fun s c hc => ?_⟩
    · ext i j
      simp
    · exact gauge_map_inner_comp ε (ContinuousMulEquiv.refl _) (fun g => rfl) s c hc
  · refine ⟨conjUJ ε, fun g => uMat_conjUJHom ε g, fun s c hc => ?_⟩
    refine gauge_map_inner_comp ε (conjUJ ε) (fun g => ?_) s c hc
    have h1 : uMat (conjUJ ε g) = (uMat g).map (starRingEnd ℂ) := uMat_conjUJHom ε g
    rw [h1]
    unfold Formalism.REAL.hs
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e : ((uMat g).map (starRingEnd ℂ) - 1) i j = starRingEnd ℂ ((uMat g - 1) i j) := by
      rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub]
      congr 1
      simp only [Matrix.one_apply]
      split_ifs <;> simp
    rw [e, Complex.norm_conj]

end GlobalTheory.LeviIso
