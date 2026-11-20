import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticOrthonormalFramesStatement
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD GlobalTheory.FockVacuum

noncomputable section

namespace GlobalTheory.HoweD

section Sign

variable {ι : Type} {P Q R S : ι → ℕ}

def cplxD (ι : Type) (P Q R S : ι → ℕ) : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) where
  toFun c w := Matrix.of fun a b => lineSign a b * Complex.I * c w a b
  map_add' c c' := by ext w a b; simp [mul_add]
  map_smul' r c := by ext w a b; simp; ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cplxD_apply (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cplxD ι P Q R S c w a b = lineSign a b * Complex.I * c w a b := rfl

/- English proof (translation)
Use extensionality with `w a b`. Apply the tactic sequence `rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, ← mul_assoc]`.
-/
theorem cplxD_cplxD (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) : cplxD ι P Q R S (cplxD ι P Q R S c) = -c := by
  ext w a b
  rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, ← mul_assoc]

/- English proof (translation)
Use `Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h]`. Take the linear combination `(-(c w a b * (starRingEnd ℂ) (c' w a b))) * Complex.I_mul_I`. Take the linear combination `(c w a b * (starRingEnd ℂ) (c' w a b)) * Complex.I_mul_I`.
-/
theorem herm_cplxD [Fintype ι] (c c' : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    ∑ w, ∑ a, ∑ b, lineSign a b * cplxD ι P Q R S c w a b * star (cplxD ι P Q R S c' w a b) =
      ∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b) := by
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h]
  · linear_combination (-(c w a b * (starRingEnd ℂ) (c' w a b))) * Complex.I_mul_I
  · linear_combination (c w a b * (starRingEnd ℂ) (c' w a b)) * Complex.I_mul_I

/- English proof (translation)
Establish `h : ∀ w a b, (lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im = -Complex.normSq (c w a b)`. Introduce `w a b`. Apply the tactic sequence `rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, Complex.normSq_apply] <;> ring`. Simplify using `only [Complex.im_sum, h, Finset.sum_neg_distrib]`. Choose the witnesses or unpack the hypotheses as in `⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by`.

Assume the negation of the conclusion as `h0`. Use `push_neg at h0`. Conclude with `hc (by ext w a b; exact h0 w a b)`. Establish `: 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b)` using `Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normS …`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem herm_cplxD_pos [Fintype ι] (c : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) (hc : c ≠ 0) :
    0 < -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im := by
  have h : ∀ w a b, (lineSign a b * c w a b * star (cplxD ι P Q R S c w a b)).im = -Complex.normSq (c w a b) := by
    intro w a b
    rcases lineSign_cases a b with h | h <;> simp [cplxD_apply, h, Complex.normSq_apply] <;> ring
  simp only [Complex.im_sum, h, Finset.sum_neg_distrib]
  obtain ⟨w, a, b, hw⟩ : ∃ w a b, c w a b ≠ 0 := by
    by_contra h0
    push_neg at h0
    exact hc (by ext w a b; exact h0 w a b)
  have : 0 < ∑ w, ∑ a, ∑ b, Complex.normSq (c w a b) :=
    Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
      ⟨w, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
        ⟨a, Finset.mem_univ _, Finset.sum_pos' (fun _ _ => Complex.normSq_nonneg _)
          ⟨b, Finset.mem_univ _, Complex.normSq_pos.2 hw⟩⟩⟩
  linarith

/- English proof (translation)
Use extensionality with `w' a' b'`. Rewrite using `[cplxD_apply]`. Distinguish the cases in `hw : w' = w`. Substitute `hw` using the available equality. Distinguish the cases in `hab : a = a' ∧ b = b'`.

Take `⟨rfl, rfl⟩` from `hab`. Apply the tactic sequence `rcases lineSign_cases a b with h | h <;> simp [h]`. Simplify using `[Matrix.single_apply, hab]`. Simplify using `[hw]`.
-/
theorem cplxD_single [DecidableEq ι] (w : ι) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) :
    cplxD ι P Q R S (Pi.single w (Matrix.single a b 1)) =
      (lineSign a b).re • (Pi.single w (Matrix.single a b Complex.I) : ∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) := by
  ext w' a' b'
  rw [cplxD_apply]
  by_cases hw : w' = w
  · subst hw
    by_cases hab : a = a' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := hab
      rcases lineSign_cases a b with h | h <;> simp [h]
    · simp [Matrix.single_apply, hab]
  · simp [hw]

end Sign

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C D hCM hFr hD`. Establish `hU` using `fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ => GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)`. Use `choose U hU hU' using hU`. Establish `hadd : ∀ c c', U (c + c') = U c + U c'` using `fun c c' => by`. Use `(hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm` and prove the remaining obligations.

Rewrite using `[smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]`. Rewrite using `[Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]`. Establish `hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c` using `fun r c => by`. Use `(hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm` and prove the remaining obligations. Rewrite using `[smul_comm, (hU c).1 u hu, smul_zero]`.

Rewrite using `[GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Set `p : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)` to `{ toFun := fun c i => evI F ((d.e (U c)).1 i) map_add' := fun c c' => by`. Use function extensionality and compare the values at `i`.

Rewrite using `[hadd, map_add]`. Conclude with `map_add (evR F) _ _`. Use the proof step `map_smul' := fun r c => by`. Use function extensionality and compare the values at `i`. Rewrite using `[hsmul, map_smul]`.

Conclude with `evI_realAd_mul r _ }`. Set `q : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)` to `{ toFun := fun c i => evI F ((d.e (U c)).2 i) map_add' := fun c c' => by`. Use function extensionality and compare the values at `i`. Rewrite using `[hadd, map_add]`. Conclude with `map_add (evR F) _ _`.

Use the proof step `map_smul' := fun r c => by`. Use function extensionality and compare the values at `i`. Rewrite using `[hsmul, map_smul]`. Conclude with `evI_realAd_mul r _ }`. Establish `hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) = -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im` using `fun c c' => by`.

Rewrite using `[← GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form, trPair_apply, trPair_apply, ← map_sub, ← evR_apply]`. Simplify using `only [dotProduct, map_sub, map_sum, map_mul]`. Both sides reduce to the same expression. Establish `hs : Function.Surjective (p.prod q)`. Introduce and unpack `⟨v, v'⟩`.

Set `u` to `d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))`. Establish `hu : At (evI F) u` using `fun t ht => by`. Rewrite using `[← map_smul, LinearEquiv.map_eq_zero_iff]`. Use extensionality with `i`. Conclude with `mul_infAd t ht _`.

Conclude with `mul_infAd t ht _`. Use `choose A' hA' using fun w => (hFr.2.1 w).2`. Use `choose C' hC' using fun w => (hFr.2.2 w).2`. Establish `huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ` using `hU' _ _ ⟨hu, fun w => by`. Establish `: (C' w)ᵀ * (C w)ᵀ = 1` using `by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩`. Use `⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evI F ((d.e (U _)).1 i) = v i`. Rewrite using `[← huc, LinearEquiv.apply_symm_apply, evI_infAd]`.

Express the relevant statement in the definitionally equal form `evI F ((d.e (U _)).2 i) = v' i`. Rewrite using `[← huc, LinearEquiv.apply_symm_apply, evI_infAd]`. Take `⟨X, Y, hX, hY, hYp, hXY⟩` from `exists_siegel (trPair F κ) p q (cplxD _ P Q R S) cplxD_cplxD (fun c c' => by rw [hω, hω, herm_cplxD]) (fun c hc => by rw [hω]; exact herm_cplxD_pos c hc) hs`. Take `⟨f, hf0, hf⟩` from `exists_gaussian X Y hX hY hYp`. Use `⟨f, hf0, fun w a b u u' hu hu' hc hc' => ?_⟩` and prove the remaining obligations.

Establish `e1` using `hU' _ u ⟨hu, hc⟩`. Establish `e2` using `hU' _ u' ⟨hu', hc'⟩`. Use `set c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b 1) with hcdef`. Use `set c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b Complex.I) with hcdef'`. Establish `hJ : cplxD _ P Q R S c = (lineSign a b).re • c'` using `cplxD_single w a b`.

Use extensionality with `x`. Establish `h1` using `hXY c x`. Establish `h2` using `hXY (cplxD _ P Q R S c) x`. Rewrite `h2` using `[cplxD_cplxD]`. Rewrite `h1`, `h2` using `[hJ]`.

Simplify using `only [map_smul, map_neg, smul_eq_mul] at h1 h2`. Establish `k1 : D u f x = 2 * Real.pi * Complex.I * ((X x (p c) : ℝ) + Complex.I * (Y x (p c) : ℝ)) * f x - 2 * Real.pi * Complex.I * (trPair F κ x (q c) : ℝ) * f x`. Rewrite using `[hD u hu, hf, e1]`. Both sides reduce to the same expression. Establish `k2 : D u' f x = 2 * Real.pi * Complex.I * ((X x (p c') : ℝ) + Complex.I * (Y x (p c') : ℝ)) * f x - 2 * Real.pi * Complex.I * (trPair F κ x (q c') : ℝ) * f x`.

Rewrite using `[hD u' hu', hf, e2]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `D u f x + (lineSign a b * Complex.I) * D u' f x = 0`. Rewrite using `[k1, k2]`. Establish `h1'` using `congrArg (fun t : ℝ => (t : ℂ)) h1`.

Establish `h2'` using `congrArg (fun t : ℝ => (t : ℂ)) h2`. Establish `hl : (((lineSign a b).re : ℝ) : ℂ) = lineSign a b`. Apply the tactic sequence `rcases lineSign_cases a b with h | h <;> simp [h]`. Move the coercions through the operations in `at h1' h2'`. Rewrite `h1'`, `h2'` using `[hl]`.

Take the linear combination `(2 * Real.pi * Complex.I * f x) * h1' + (2 * Real.pi * Complex.I * Complex.I * f x) * h2' + (2 * Real.pi * Complex.I * f x * lineSign a b * (Y x (p c') : ℝ)) * Complex.I_mul_I`.
-/
theorem exists_vacuumD : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → FramedD τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (u u' : Matrix α β (AE F E)),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a₀ b₀ A C D hCM hFr hD
  have hU := fun c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ =>
    GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.T.realScalarArchimedeanAdele_smul_matrix_realPlace σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  let p : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2, d.form,
      trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  obtain ⟨X, Y, hX, hY, hYp, hXY⟩ := exists_siegel (trPair F κ) p q (cplxD _ P Q R S) cplxD_cplxD
    (fun c c' => by rw [hω, hω, herm_cplxD]) (fun c hc => by rw [hω]; exact herm_cplxD_pos c hc) hs
  obtain ⟨f, hf0, hf⟩ := exists_gaussian X Y hX hY hYp
  refine ⟨f, hf0, fun w a b u u' hu hu' hc hc' => ?_⟩
  have e1 := hU' _ u ⟨hu, hc⟩
  have e2 := hU' _ u' ⟨hu', hc'⟩
  set c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b 1) with hcdef
  set c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ := Pi.single w (Matrix.single a b Complex.I) with hcdef'
  have hJ : cplxD _ P Q R S c = (lineSign a b).re • c' := cplxD_single w a b
  ext x
  have h1 := hXY c x
  have h2 := hXY (cplxD _ P Q R S c) x
  rw [cplxD_cplxD] at h2
  rw [hJ] at h1 h2
  simp only [map_smul, map_neg, smul_eq_mul] at h1 h2
  have k1 : D u f x = 2 * Real.pi * Complex.I * ((X x (p c) : ℝ) + Complex.I * (Y x (p c) : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c) : ℝ) * f x := by
    rw [hD u hu, hf, e1]; rfl
  have k2 : D u' f x = 2 * Real.pi * Complex.I * ((X x (p c') : ℝ) + Complex.I * (Y x (p c') : ℝ)) * f x -
      2 * Real.pi * Complex.I * (trPair F κ x (q c') : ℝ) * f x := by
    rw [hD u' hu', hf, e2]; rfl
  change D u f x + (lineSign a b * Complex.I) * D u' f x = 0
  rw [k1, k2]
  have h1' := congrArg (fun t : ℝ => (t : ℂ)) h1
  have h2' := congrArg (fun t : ℝ => (t : ℂ)) h2
  have hl : (((lineSign a b).re : ℝ) : ℂ) = lineSign a b := by
    rcases lineSign_cases a b with h | h <;> simp [h]
  push_cast at h1' h2'
  rw [hl] at h1' h2'
  linear_combination (2 * Real.pi * Complex.I * f x) * h1' + (2 * Real.pi * Complex.I * Complex.I * f x) * h2' +
    (2 * Real.pi * Complex.I * f x * lineSign a b * (Y x (p c') : ℝ)) * Complex.I_mul_I

end GlobalTheory.HoweD
