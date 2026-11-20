import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2Statement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
namespace GlobalTheory.CptCoeff
open MeasureTheory Matrix ComplexConjugate

/- English proof (translation)
Establish `e : ∀ y : ℂ, (((‖y‖ ^ 2 : ℝ)) : ℂ) = y * conj y` using `fun y => by`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Rewrite using `[e, e, e, e]`. Simplify using `only [map_add, map_sub, map_mul, Complex.conj_I]`. Take the linear combination `(1 / 2 : ℂ) * (z * conj w - w * conj z) * Complex.I_sq`.
-/
theorem mul_conj_polar (z w : ℂ) : z * conj w = (1 / 4 : ℂ) * ((((‖z + w‖ ^ 2 : ℝ) : ℂ) - ((‖z - w‖ ^ 2 : ℝ) : ℂ)) +
    Complex.I * (((‖z + Complex.I * w‖ ^ 2 : ℝ) : ℂ) - ((‖z - Complex.I * w‖ ^ 2 : ℝ) : ℂ))) := by
  have e : ∀ y : ℂ, (((‖y‖ ^ 2 : ℝ)) : ℂ) = y * conj y := fun y => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [e, e, e, e]
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  linear_combination (1 / 2 : ℂ) * (z * conj w - w * conj z) * Complex.I_sq

/- English proof (translation)
Establish `hi : Integrable (fun x => ‖h x‖ ^ 2) μ` using `hh.integrable_norm_pow two_ne_zero`. Rewrite using `[integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity) hi.aestronglyMeasurable]`. Use `congr 3`. Use function extensionality and compare the values at `x`. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]`.
-/
theorem integral_sq_norm {X : Type} [MeasurableSpace X] {μ : Measure X} {h : X → ℂ} (hh : MemLp h 2 μ) :
    ∫ x, (((‖h x‖ ^ 2 : ℝ)) : ℂ) ∂μ = (((∫⁻ x, ‖h x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) := by
  have hi : Integrable (fun x => ‖h x‖ ^ 2) μ := hh.integrable_norm_pow two_ne_zero
  rw [integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by positivity)
    hi.aestronglyMeasurable]
  congr 3
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

/- English proof (translation)
The claim follows from `(hh.integrable_norm_pow two_ne_zero).ofReal`.
-/
theorem integrable_sq_norm {X : Type} [MeasurableSpace X] {μ : Measure X} {h : X → ℂ} (hh : MemLp h 2 μ) :
    Integrable (fun x => (((‖h x‖ ^ 2 : ℝ)) : ℂ)) μ :=
  (hh.integrable_norm_pow two_ne_zero).ofReal

/- English proof (translation)
Establish `h1` using `hf.add hg`. Establish `h2` using `hf.sub hg`. Establish `h3` using `hf.add (hg.const_smul Complex.I)`. Establish `h4` using `hf.sub (hg.const_smul Complex.I)`. Rewrite using `[← integral_sq_norm h1, ← integral_sq_norm h2, ← integral_sq_norm h3, ← integral_sq_norm h4, ← integral_sub (integrable_sq_norm h1) (integrable_sq_norm h2), ← integral_sub (integrable_sq_norm h3) (integrable_sq_norm h4), ← integral_const_mul, ← integral_add, ← integral_const_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_conj_polar (f x) (g x)`. Conclude with `(integrable_sq_norm h1).sub (integrable_sq_norm h2)`.

Conclude with `((integrable_sq_norm h3).sub (integrable_sq_norm h4)).const_mul _`.
-/
theorem integral_mul_conj {X : Type} [MeasurableSpace X] {μ : Measure X} {f g : X → ℂ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : ∫ x, f x * conj (g x) ∂μ = (1 / 4 : ℂ) *
      (((((∫⁻ x, ‖(f + g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) - (((∫⁻ x, ‖(f - g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ)) +
      Complex.I * ((((∫⁻ x, ‖(f + Complex.I • g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ) -
        (((∫⁻ x, ‖(f - Complex.I • g) x‖ₑ ^ 2 ∂μ).toReal : ℝ) : ℂ))) := by
  have h1 := hf.add hg
  have h2 := hf.sub hg
  have h3 := hf.add (hg.const_smul Complex.I)
  have h4 := hf.sub (hg.const_smul Complex.I)
  rw [← integral_sq_norm h1, ← integral_sq_norm h2, ← integral_sq_norm h3, ← integral_sq_norm h4,
    ← integral_sub (integrable_sq_norm h1) (integrable_sq_norm h2),
    ← integral_sub (integrable_sq_norm h3) (integrable_sq_norm h4), ← integral_const_mul,
    ← integral_add, ← integral_const_mul]
  · congr 1
    funext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact mul_conj_polar (f x) (g x)
  · exact (integrable_sq_norm h1).sub (integrable_sq_norm h2)
  · exact ((integrable_sq_norm h3).sub (integrable_sq_norm h4)).const_mul _

/- English proof (translation)
Rewrite using `[integral_mul_conj (hP _ (hT f hf)) (hP _ (hT g hg)), integral_mul_conj (hP f hf) (hP g hg), ← map_add, ← map_sub, ← map_smul, ← map_add, ← map_sub, hU _ (P.add_mem hf hg), hU _ (P.sub_mem hf hg), hU _ (P.add_mem hf (P.smul_mem _ hg)), hU _ (P.sub_mem hf (P.smul_mem _ hg))]`.
-/
theorem integral_mul_conj_map {X : Type} [MeasurableSpace X] {μ : Measure X} (P : Submodule ℂ (X → ℂ))
    (hP : ∀ f ∈ P, MemLp f 2 μ) (T : Module.End ℂ (X → ℂ)) (hT : ∀ f ∈ P, T f ∈ P)
    (hU : ∀ f ∈ P, ∫⁻ x, ‖T f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) {f g : X → ℂ} (hf : f ∈ P) (hg : g ∈ P) :
    ∫ x, T f x * conj (T g x) ∂μ = ∫ x, f x * conj (g x) ∂μ := by
  rw [integral_mul_conj (hP _ (hT f hf)) (hP _ (hT g hg)), integral_mul_conj (hP f hf) (hP g hg),
    ← map_add, ← map_sub, ← map_smul, ← map_add, ← map_sub, hU _ (P.add_mem hf hg), hU _ (P.sub_mem hf hg),
    hU _ (P.add_mem hf (P.smul_mem _ hg)), hU _ (P.sub_mem hf (P.smul_mem _ hg))]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def infOne : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

/- English proof (translation)
Introduce `t ht`. Establish `h1 : t.1 = 0` using `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact ht)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `t.1 * 1 = 0`. Rewrite using `[h1, zero_mul]`.

Express the relevant statement in the definitionally equal form `t.2 * 0 = 0`. Conclude with `mul_zero _`.
-/
theorem at_infOne : At (evI F) (infOne (F := F)) := by
  intro t ht
  have h1 : t.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact ht)
  refine Prod.ext ?_ ?_
  · change t.1 * 1 = 0
    rw [h1, zero_mul]
  · change t.2 * 0 = 0
    exact mul_zero _

/- English proof (translation)
The claim follows from `evalV_singleFin_ne h a`.
-/
theorem evFin_liftV_ne {v w : Pl F} (h : w ≠ v) (a : Fv F v) : evFin F w (GlobalTheory.LatVac.liftV v a) = 0 :=
  evalV_singleFin_ne h a

/- English proof (translation)
Use `set e : AF F := infOne + ∑ w ∈ S, GlobalTheory.LatVac.liftV w 1 with he`. Establish `h1 : evI F (1 - e) = 0`. Express the relevant statement in the definitionally equal form `InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (1 - e)) = 0`. Establish `h0 : fstA F (infOne (F` using `F)) = 1 := rfl`. Establish `hl : ∀ w : Pl F, fstA F (GlobalTheory.LatVac.liftV w 1) = 0` using `fun w => rfl`.

Establish `: fstA F (1 - e) = 0`. Rewrite using `[he, map_sub, map_one, map_add, map_sum, h0, Finset.sum_eq_zero fun w _ => hl w, add_zero, sub_self]`. Rewrite using `[this, map_zero]`. Establish `h2 : ∀ w ∈ S, evFin F w (1 - e) = 0`. Introduce `w hw`.

Rewrite using `[he, map_sub, map_one, map_add, map_sum]`. Establish `h0 : evFin F w (infOne (F` using `F)) = 0 := by`. Express the relevant statement in the definitionally equal form `evalV F w (sndA F infOne) = 0`. Establish `: sndA F (infOne (F` using `F)) = 0 := rfl`. Rewrite using `[this, map_zero]`.

Establish `hs : ∑ x ∈ S, evFin F w (GlobalTheory.LatVac.liftV x 1) = ∑ x ∈ S, if w = x then (1 : Fv F w) else 0`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Distinguish the cases in `hx : w = x`. Substitute `hx` using the available equality. Rewrite using `[if_pos rfl, GlobalTheory.LatVac.evFin_liftV]`.

Rewrite using `[if_neg hx, evFin_liftV_ne hx]`. Rewrite using `[h0, hs, Finset.sum_ite_eq S w (fun _ => (1 : Fv F w)), if_pos hw, zero_add, sub_self]`. Establish `hue : u = e • u`. Use `hu (1 - e) h1 h2` as an intermediate fact. Rewrite `this` using `[sub_smul, one_smul, sub_eq_zero]`. Then use the resulting hypothesis.

Establish `hA : e • A = 0`. Rewrite using `[he, add_smul, Finset.sum_smul, hI _ at_infOne, zero_add]`. Conclude with `Finset.sum_eq_zero fun w hw => hS w hw _ (GlobalTheory.LatVac.at_liftV w 1)`. Rewrite using `[hue, Matrix.mul_smul, ← Matrix.smul_mul, hA, Matrix.zero_mul]`.
-/
theorem mul_eq_zero_of_supp (S : Finset (Pl F)) {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE F E))
    (hI : ∀ t : AF F, At (evI F) t → t • A = 0) (hS : ∀ w ∈ S, ∀ t : AF F, At (evFin F w) t → t • A = 0)
    (u : Matrix (Fin n) (Fin k) (AE F E))
    (hu : ∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) : A * u = 0 := by
  classical
  set e : AF F := infOne + ∑ w ∈ S, GlobalTheory.LatVac.liftV w 1 with he
  have h1 : evI F (1 - e) = 0 := by
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (1 - e)) = 0
    have h0 : fstA F (infOne (F := F)) = 1 := rfl
    have hl : ∀ w : Pl F, fstA F (GlobalTheory.LatVac.liftV w 1) = 0 := fun w => rfl
    have : fstA F (1 - e) = 0 := by
      rw [he, map_sub, map_one, map_add, map_sum, h0, Finset.sum_eq_zero fun w _ => hl w, add_zero, sub_self]
    rw [this, map_zero]
  have h2 : ∀ w ∈ S, evFin F w (1 - e) = 0 := by
    intro w hw
    rw [he, map_sub, map_one, map_add, map_sum]
    have h0 : evFin F w (infOne (F := F)) = 0 := by
      change evalV F w (sndA F infOne) = 0
      have : sndA F (infOne (F := F)) = 0 := rfl
      rw [this, map_zero]
    have hs : ∑ x ∈ S, evFin F w (GlobalTheory.LatVac.liftV x 1) = ∑ x ∈ S, if w = x then (1 : Fv F w) else 0 := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : w = x
      · subst hx; rw [if_pos rfl, GlobalTheory.LatVac.evFin_liftV]
      · rw [if_neg hx, evFin_liftV_ne hx]
    rw [h0, hs, Finset.sum_ite_eq S w (fun _ => (1 : Fv F w)), if_pos hw, zero_add, sub_self]
  have hue : u = e • u := by
    have := hu (1 - e) h1 h2
    rwa [sub_smul, one_smul, sub_eq_zero] at this
  have hA : e • A = 0 := by
    rw [he, add_smul, Finset.sum_smul, hI _ at_infOne, zero_add]
    exact Finset.sum_eq_zero fun w hw => hS w hw _ (GlobalTheory.LatVac.at_liftV w 1)
  rw [hue, Matrix.mul_smul, ← Matrix.smul_mul, hA, Matrix.zero_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' hT S g h hgI hhI hgS hhS Φ hΦ u hu μ hμ`. Use `letI : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _`. Establish `hW` using `IsUWeilPair.isUSplitting hT.weil'`. Establish `hg : mat g * u = u`. Use `mul_eq_zero_of_supp S (mat g - 1) hgI hgS u hu` as an intermediate fact.

Rewrite `this` using `[Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]`. Then use the resulting hypothesis. Establish `hh : u * (mat h)ᵀ = u`. Use `mul_eq_zero_of_supp S (mat h - 1) hhI hhS uᵀ (fun t h1 h2 => by rw [← Matrix.transpose_smul, hu t h1 h2, Matrix.transpose_zero])` as an intermediate fact. Rewrite `this` using `[Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]`. Use `congrArg Matrix.transpose this` as an intermediate fact.

Rewrite `this` using `[Matrix.transpose_mul, Matrix.transpose_transpose]`. Then use the resulting hypothesis. Establish `hact : actAB (cA σ) (g, h) u = u`. Express the relevant statement in the definitionally equal form `mat g * u * (mat h)ᵀ = u`. Rewrite using `[hg, hh]`. Establish `hcomm : om' (g, h) (G.M'.co.rho B.ψ u Φ) = G.M'.co.rho B.ψ u (om' (g, h) Φ)`.

Rewrite using `[hW.impl (g, h) u Φ hΦ, hact]`. Rewrite using `[← hcomm]`. Conclude with `integral_mul_conj_map (μ := μ) (schA F _) (fun f hf => GlobalTheory.T.adelic_schwartz_mem_L2 F _ μ hμ f hf) (om' (g, h)) (fun f hf => hW.pres (g, h) f hf) (fun f hf => hW.unit μ hμ (g, h) f hf) hΦ (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std u Φ hΦ)`.
-/
theorem matrix_coeff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (S : Finset (Pl F)) (g : UA σ G.V'.J) (h : UA σ G.W.J),
    (∀ u : AF F, At (evI F) u → u • (mat g - 1) = 0) → (∀ u : AF F, At (evI F) u → u • (mat h - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat g - 1) = 0) →
    (∀ w ∈ S, ∀ u : AF F, At (evFin F w) u → u • (mat h - 1) = 0) →
    ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ∀ u : Matrix (Fin a') (Fin (a + a')) (AE F E),
    (∀ t : AF F, evI F t = 0 → (∀ w ∈ S, evFin F w t = 0) → t • u = 0) →
    ∀ μ : @MeasureTheory.Measure (Fin a' × Fin (a + a') → AF F) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      (@MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x =>
          om' (g, h) Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u (om' (g, h) Φ) x)) =
        @MeasureTheory.integral _ ℂ _ _ (borel _) μ fun x => Φ x * starRingEnd ℂ (G.M'.co.rho B.ψ u Φ x) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT S g h hgI hhI hgS hhS Φ hΦ u hu μ hμ
  letI : MeasurableSpace (Fin a' × Fin (a + a') → AF F) := borel _
  have hW := IsUWeilPair.isUSplitting hT.weil'
  have hg : mat g * u = u := by
    have := mul_eq_zero_of_supp S (mat g - 1) hgI hgS u hu
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have hh : u * (mat h)ᵀ = u := by
    have := mul_eq_zero_of_supp S (mat h - 1) hhI hhS uᵀ
      (fun t h1 h2 => by rw [← Matrix.transpose_smul, hu t h1 h2, Matrix.transpose_zero])
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
    have := congrArg Matrix.transpose this
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose] at this
  have hact : actAB (cA σ) (g, h) u = u := by
    change mat g * u * (mat h)ᵀ = u
    rw [hg, hh]
  have hcomm : om' (g, h) (G.M'.co.rho B.ψ u Φ) = G.M'.co.rho B.ψ u (om' (g, h) Φ) := by
    rw [hW.impl (g, h) u Φ hΦ, hact]
  rw [← hcomm]
  exact integral_mul_conj_map (μ := μ) (schA F _) (fun f hf => GlobalTheory.T.adelic_schwartz_mem_L2 F _ μ hμ f hf) (om' (g, h))
    (fun f hf => hW.pres (g, h) f hf) (fun f hf => hW.unit μ hμ (g, h) f hf) hΦ
    (GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std u Φ hΦ)

end GlobalTheory.CptCoeff

end
