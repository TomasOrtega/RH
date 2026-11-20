import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape

noncomputable section

open MeasureTheory Filter Topology GlobalTheory.Orb GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open Formalism.REAL (UJ KG toM toMK muK)
open Formalism.MainNotions.S (IsDS)
open GlobalTheory.HCChar (dsChar torusPt)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.Pc1

def LocalPC4 : Prop :=
  ∀ (r : ℕ), Odd r → ∀ (ε : Fin r → Bool) (lam : Fin r → ℤ), Gap4 r lam →
    ∀ (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] (D : Matrix (Fin r) (Fin r) ℂ → (X →L[ℂ] X))
      (hD : IsDS ε (fun a => (lam a : ℝ)) D) (μ : Measure (UJ ε)) [μ.IsHaarMeasure],
      ∃ f, GlobalTheory.PsCo.Pc.IsPC' ε lam μ D hD f

/- English proof (translation)
The claim follows from `tendsto_nhds_unique (tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun t ht => (h t ht).symm)) hL`.
-/
theorem eq_of_const_of_tendsto {a L : ℂ} {u : ℝ → ℂ} (h : ∀ t, 1 ≤ t → u t = a) (hL : Tendsto u atTop (𝓝 L)) : a = L :=
  tendsto_nhds_unique (tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun t ht => (h t ht).symm)) hL

/- English proof (translation)
Rewrite `h` using `[IsRegSS, Matrix.charpoly_diagonal]`. Conclude with `Polynomial.separable_prod_X_sub_C_iff.1 h`.
-/
theorem injective_of_regSS {n : ℕ} {z : Fin n → ℂ} (h : IsRegSS (Matrix.diagonal z)) : Function.Injective z := by
  rw [IsRegSS, Matrix.charpoly_diagonal] at h
  exact Polynomial.separable_prod_X_sub_C_iff.1 h

/- English proof (translation)
Use `Complex.ofReal_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun x _ => pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 fun e => ?_)))` and prove the remaining obligations. Establish `h1` using `x.2.1`. Rewrite `h1` using `[h e, x.2.2]`. Conclude with `Bool.noConfusion h1`.
-/
theorem dMode_ne_zero {n : ℕ} (ε : Fin n → Bool) {θ : Fin n → ℝ}
    (h : Function.Injective fun a => Complex.exp (θ a * Complex.I)) : (dMode ε θ : ℂ) ≠ 0 := by
  refine Complex.ofReal_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun x _ => pow_ne_zero _ (norm_ne_zero_iff.2 (sub_ne_zero.2 fun e => ?_)))
  have h1 := x.2.1
  rw [h e, x.2.2] at h1
  exact Bool.noConfusion h1

/- English proof (translation)
Express the relevant statement in the definitionally equal form `toM (torusPt ε θ) ∈ Formalism.REAL.Kset ε`. Establish `e : toM (torusPt ε θ) = Matrix.diagonal fun a => Complex.exp (θ a * Complex.I)` using `rfl`. Rewrite using `[e]`. Use `⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Rewrite using `[Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]`. Simplify using the standard rewrite rules.
-/
theorem torusPt_mem_KG {n : ℕ} (ε : Fin n → Bool) (θ : Fin n → ℝ) : torusPt ε θ ∈ KG ε := by
  change toM (torusPt ε θ) ∈ Formalism.REAL.Kset ε
  have e : toM (torusPt ε θ) = Matrix.diagonal fun a => Complex.exp (θ a * Complex.I) := rfl
  rw [e]
  refine ⟨?_, by simp [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, mul_comm]⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  rw [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  simp

/- English proof (translation)
Introduce `r hr ε lam hgap X _ _ D hD μ _`. Use `haveI := hD.1`. Use `haveI := hD.2.1`. Take `⟨M, P, hP, hcl, htor, hone, hzero⟩` from `hK r hr ε lam hgap X D hD`. Take `⟨p, q, hpq, htop⟩` from `hAlg r ε M P hP`.

Take `⟨G, hG⟩` from `hProf (nMode ε)`. Take `⟨d, hd, hfam⟩` from `hFam r ε G p hG`. Take `⟨c, hc, hlim⟩` from `hLim r ε μ G hG`. Take `⟨hl1, hl2⟩` from `hlim p`. Set `φ : ℝ → Mat r → ℂ` to `fun t => c⁻¹ • famF ε G p t`.

Establish `hφ : ∀ t, 1 ≤ t → φ t ∈ ShapeM ε d` using `fun t ht => Submodule.smul_mem _ _ (hfam t (by linarith)).1`. Establish `hdiff : ∀ t, 1 ≤ t → φ 1 - φ t ∈ AdSpanM ε` using `fun t ht => by`. Rewrite using `[← smul_sub]`. Conclude with `Submodule.smul_mem _ _ (hHom r ε G p q hG hpq t ht)`. Establish `hsum : ∀ t, (fun g : UJ ε => φ 1 (toM g)) = (fun g => φ t (toM g)) + fun g => (φ 1 - φ t) (toM g)` using `fun t => funext fun g => by simp`.

Establish `key : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∃ (B : U →L[ℂ] U) (a : ℂ), (∀ v, B v = ∫ k : KG ε, ev (toMK k) (topP ε M P) • π k v ∂(muK ε)) ∧ HasTrace B a ∧ HasTrace (repOp π μ …`. Introduce `U _ _ _ π hu hi`. Take `⟨w, hw, hw1, hw2⟩` from `hTr r ε μ U π hu hi d`. Take `⟨B, hB, hBt⟩` from `hw2 _ (hd _ le_rfl)`. Rewrite `hB`, `hBt` using `[htop]`.

Use `⟨B, _, hB, hBt, ?_⟩` and prove the remaining obligations. Establish `hint : ∀ t, 1 ≤ t → Integrable (fun g : UJ ε => φ t (toM g) * w g) μ` using `fun t ht => ((hSh r ε d _ (hφ t ht)).2.2.1.mul hw).integrable_of_hasCompactSupport (hSh r ε d _ (hφ t ht)).2.2.2.mul_right`. Establish `hconst : ∀ t, 1 ≤ t → ∫ g, φ t (toM g) * w g ∂μ = ∫ g, φ 1 (toM g) * w g ∂μ` using `fun t ht => by`. Establish `h1` using `(hw1 _ (Submodule.sub_mem _ (hφ 1 le_rfl) (hφ t ht))).2`. Rewrite `h1` using `[(hTA r ε μ U π hu hi _ (hdiff t ht)).2]`.

Simplify using `only [Pi.sub_apply, sub_mul] at h1`. Rewrite `h1` using `[integral_sub (hint 1 le_rfl) (hint t ht)]`. Conclude with `(sub_eq_zero.1 h1.symm).symm`. Establish `hT` using `(hl1 w hw).const_mul c⁻¹`. Rewrite `hT` using `[inv_mul_cancel_left₀ hc, htop]`.

Rewrite using `[← eq_of_const_of_tendsto hconst (hT.congr fun t => by`. Rewrite using `[← integral_const_mul]`. Simplify using `[φ, mul_assoc])]`. Conclude with `hw1 _ (hφ 1 le_rfl)`. Use `⟨fun g => φ 1 (toM g), (hSh r ε d _ (hφ 1 le_rfl)).1, (hSh r ε d _ (hφ 1 le_rfl)).2.1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨B, a, hB, hBa, h⟩` from `key X (ujRep hD.2.2.1) (isUnitaryRep_repVia _ _ GlobalTheory.HCChar.continuous_ujMat) (isTopIrreducible_repVia _ _ (fun x hx => by`. Establish `hJ : IsUnit x`. Establish `h : x.conjTranspose * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε` using `hx`. Establish `hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1`. Rewrite using `[Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Apply the tactic sequence `congr 1; funext a; split_ifs <;> simp`. Establish `h2 : (Formalism.REAL.Jm ε * x.conjTranspose * Formalism.REAL.Jm ε) * x = 1`. Rewrite using `[mul_assoc, mul_assoc, ← mul_assoc x.conjTranspose, h, hJ]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse h2)`. Conclude with `⟨⟨hJ.unit, hx⟩, rfl⟩) hD.2.2.2.1)`.

Rewrite `h` using `[hone B a hB hBa]`. Then use the resulting hypothesis. Introduce `U _ _ _ π hu hi hne`. Take `⟨B, a, hB, hBa, h⟩` from `key U π hu hi`. Rewrite `h` using `[hzero U π hu hi hne B a hB hBa]`. Then use the resulting hypothesis. Introduce `s hs hnc dt _ _`.

Take `⟨R, hR, hx⟩` from `hNE r ε s hs hnc`. Establish `ht : (1 : ℝ) ≤ 1 + 2 / R` using `by have := div_pos two_pos hR; linarith`. Establish `h0 : HasOrbInt μ s dt (fun g => φ (1 + 2 / R) (toM g)) 0`. Establish `e : conjFn s (fun g : UJ ε => φ (1 + 2 / R) (toM g)) = 0` using `funext fun x => by`. Establish `h1 : 1 < (1 + 2 / R) * rM ε (toM (x⁻¹ * s * x))`.

Establish `h2 : (1 + 2 / R) * R ≤ (1 + 2 / R) * rM ε (toM (x⁻¹ * s * x))` using `mul_le_mul_of_nonneg_left (hx x) (by linarith)`. Establish `h3 : (1 + 2 / R) * R = R + 2` using `by field_simp`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[conjFn, φ, (hfam _ (by linarith)).2 _ h1]`. Rewrite using `[HasOrbInt, e]`.

Conclude with `⟨integrable_zero _ _ _, integral_zero _ _⟩`. Rewrite using `[hsum (1 + 2 / R)]`. Simplify using `using h0.add (hOA r ε μ s hs dt _ (hdiff _ ht))`. Introduce `s hs hcp y θ hy dt _ _`. Establish `hreg : IsRegSS (ujMat ε (torusPt ε θ))`.

Rewrite using `[← hy, IsRegSS, map_mul, Matrix.charpoly_mul_comm, ← map_mul, mul_inv_cancel_left]`. Conclude with `hs`. Establish `hinj : Function.Injective fun a => Complex.exp (θ a * Complex.I)` using `injective_of_regSS hreg`. Establish `hO` using `fun t (ht : 1 ≤ t) => hOC r ε μ s hs hcp dt y _ (hSh r ε d _ (hφ t ht)).2.2.1 (hSh r ε d _ (hφ t ht)).2.2.2`. Rewrite `hO` using `[hy]`.

Establish `hconst : ∀ t, 1 ≤ t → (∫ x, φ t (toM (x⁻¹ * torusPt ε θ * x)) ∂μ) / (dt.real Set.univ : ℂ) = (∫ x, φ 1 (toM (x⁻¹ * torusPt ε θ * x)) ∂μ) / (dt.real Set.univ : ℂ)` using `fun t ht => by`. Establish `h1` using `(hO t ht).add (hOA r ε μ s hs dt _ (hdiff t ht))`. Rewrite `h1` using `[← hsum t, add_zero]`. Conclude with `h1.2.symm.trans (hO 1 le_rfl).2`. Establish `hT` using `((hl2 θ (torusPt ε θ) rfl hinj fun k => by`.

Rewrite using `[htop]`. Conclude with `hcl ⟨_, torusPt_mem_KG ε θ⟩ k).const_mul c⁻¹).div_const (dt.real Set.univ : ℂ)`. Rewrite `hT` using `[htop, htor θ hinj, mul_div_assoc c, inv_mul_cancel_left₀ hc, mul_div_cancel_right₀ _ (dMode_ne_zero ε hinj)]`. Rewrite using `[← eq_of_const_of_tendsto hconst (hT.congr fun t => by`. Rewrite using `[← integral_const_mul]`.

Simplify using `[φ])]`. Conclude with `hO 1 le_rfl`.
-/
theorem localPC4_of (hAlg : StAlg) (hProf : StProfile) (hFam : StFam) (hHom : StHomot) (hLim : StLim)
    (hSh : StShape) (hOA : StOrbAd) (hOC : StOrbCpt) (hNE : StNonEll) (hTr : StTr) (hTA : StTrAd)
    (hK : StKData) : LocalPC4 := by
  intro r hr ε lam hgap X _ _ D hD μ _
  haveI := hD.1
  haveI := hD.2.1
  obtain ⟨M, P, hP, hcl, htor, hone, hzero⟩ := hK r hr ε lam hgap X D hD
  obtain ⟨p, q, hpq, htop⟩ := hAlg r ε M P hP
  obtain ⟨G, hG⟩ := hProf (nMode ε)
  obtain ⟨d, hd, hfam⟩ := hFam r ε G p hG
  obtain ⟨c, hc, hlim⟩ := hLim r ε μ G hG
  obtain ⟨hl1, hl2⟩ := hlim p
  let φ : ℝ → Mat r → ℂ := fun t => c⁻¹ • famF ε G p t
  have hφ : ∀ t, 1 ≤ t → φ t ∈ ShapeM ε d := fun t ht => Submodule.smul_mem _ _ (hfam t (by linarith)).1
  have hdiff : ∀ t, 1 ≤ t → φ 1 - φ t ∈ AdSpanM ε := fun t ht => by
    rw [← smul_sub]; exact Submodule.smul_mem _ _ (hHom r ε G p q hG hpq t ht)
  have hsum : ∀ t, (fun g : UJ ε => φ 1 (toM g)) = (fun g => φ t (toM g)) + fun g => (φ 1 - φ t) (toM g) :=
    fun t => funext fun g => by simp
  have key : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U]
      (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∃ (B : U →L[ℂ] U) (a : ℂ),
        (∀ v, B v = ∫ k : KG ε, ev (toMK k) (topP ε M P) • π k v ∂(muK ε)) ∧ HasTrace B a ∧
          HasTrace (repOp π μ fun g => φ 1 (toM g)) a := by
    intro U _ _ _ π hu hi
    obtain ⟨w, hw, hw1, hw2⟩ := hTr r ε μ U π hu hi d
    obtain ⟨B, hB, hBt⟩ := hw2 _ (hd _ le_rfl)
    rw [htop] at hB hBt
    refine ⟨B, _, hB, hBt, ?_⟩
    have hint : ∀ t, 1 ≤ t → Integrable (fun g : UJ ε => φ t (toM g) * w g) μ := fun t ht =>
      ((hSh r ε d _ (hφ t ht)).2.2.1.mul hw).integrable_of_hasCompactSupport (hSh r ε d _ (hφ t ht)).2.2.2.mul_right
    have hconst : ∀ t, 1 ≤ t → ∫ g, φ t (toM g) * w g ∂μ = ∫ g, φ 1 (toM g) * w g ∂μ := fun t ht => by
      have h1 := (hw1 _ (Submodule.sub_mem _ (hφ 1 le_rfl) (hφ t ht))).2
      rw [(hTA r ε μ U π hu hi _ (hdiff t ht)).2] at h1
      simp only [Pi.sub_apply, sub_mul] at h1
      rw [integral_sub (hint 1 le_rfl) (hint t ht)] at h1
      exact (sub_eq_zero.1 h1.symm).symm
    have hT := (hl1 w hw).const_mul c⁻¹
    rw [inv_mul_cancel_left₀ hc, htop] at hT
    rw [← eq_of_const_of_tendsto hconst (hT.congr fun t => by
      rw [← integral_const_mul]; simp [φ, mul_assoc])]
    exact hw1 _ (hφ 1 le_rfl)
  refine ⟨fun g => φ 1 (toM g), (hSh r ε d _ (hφ 1 le_rfl)).1, (hSh r ε d _ (hφ 1 le_rfl)).2.1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨B, a, hB, hBa, h⟩ := key X (ujRep hD.2.2.1)
      (isUnitaryRep_repVia _ _ GlobalTheory.HCChar.continuous_ujMat)
      (isTopIrreducible_repVia _ _ (fun x hx => by
        have hJ : IsUnit x := by
          have h : x.conjTranspose * Formalism.REAL.Jm ε * x = Formalism.REAL.Jm ε := hx
          have hJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
            rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
            congr 1; funext a; split_ifs <;> simp
          have h2 : (Formalism.REAL.Jm ε * x.conjTranspose * Formalism.REAL.Jm ε) * x = 1 := by
            rw [mul_assoc, mul_assoc, ← mul_assoc x.conjTranspose, h, hJ]
          exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse h2)
        exact ⟨⟨hJ.unit, hx⟩, rfl⟩) hD.2.2.2.1)
    rwa [hone B a hB hBa] at h
  · intro U _ _ _ π hu hi hne
    obtain ⟨B, a, hB, hBa, h⟩ := key U π hu hi
    rwa [hzero U π hu hi hne B a hB hBa] at h
  · intro s hs hnc dt _ _
    obtain ⟨R, hR, hx⟩ := hNE r ε s hs hnc
    have ht : (1 : ℝ) ≤ 1 + 2 / R := by have := div_pos two_pos hR; linarith
    have h0 : HasOrbInt μ s dt (fun g => φ (1 + 2 / R) (toM g)) 0 := by
      have e : conjFn s (fun g : UJ ε => φ (1 + 2 / R) (toM g)) = 0 := funext fun x => by
        have h1 : 1 < (1 + 2 / R) * rM ε (toM (x⁻¹ * s * x)) := by
          have h2 : (1 + 2 / R) * R ≤ (1 + 2 / R) * rM ε (toM (x⁻¹ * s * x)) :=
            mul_le_mul_of_nonneg_left (hx x) (by linarith)
          have h3 : (1 + 2 / R) * R = R + 2 := by field_simp
          linarith
        simp [conjFn, φ, (hfam _ (by linarith)).2 _ h1]
      rw [HasOrbInt, e]
      exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
    rw [hsum (1 + 2 / R)]
    simpa using h0.add (hOA r ε μ s hs dt _ (hdiff _ ht))
  · intro s hs hcp y θ hy dt _ _
    have hreg : IsRegSS (ujMat ε (torusPt ε θ)) := by
      rw [← hy, IsRegSS, map_mul, Matrix.charpoly_mul_comm, ← map_mul, mul_inv_cancel_left]
      exact hs
    have hinj : Function.Injective fun a => Complex.exp (θ a * Complex.I) := injective_of_regSS hreg
    have hO := fun t (ht : 1 ≤ t) => hOC r ε μ s hs hcp dt y _ (hSh r ε d _ (hφ t ht)).2.2.1 (hSh r ε d _ (hφ t ht)).2.2.2
    rw [hy] at hO
    have hconst : ∀ t, 1 ≤ t → (∫ x, φ t (toM (x⁻¹ * torusPt ε θ * x)) ∂μ) / (dt.real Set.univ : ℂ) =
        (∫ x, φ 1 (toM (x⁻¹ * torusPt ε θ * x)) ∂μ) / (dt.real Set.univ : ℂ) := fun t ht => by
      have h1 := (hO t ht).add (hOA r ε μ s hs dt _ (hdiff t ht))
      rw [← hsum t, add_zero] at h1
      exact h1.2.symm.trans (hO 1 le_rfl).2
    have hT := ((hl2 θ (torusPt ε θ) rfl hinj fun k => by
      rw [htop]; exact hcl ⟨_, torusPt_mem_KG ε θ⟩ k).const_mul c⁻¹).div_const (dt.real Set.univ : ℂ)
    rw [htop, htor θ hinj, mul_div_assoc c, inv_mul_cancel_left₀ hc, mul_div_cancel_right₀ _ (dMode_ne_zero ε hinj)] at hT
    rw [← eq_of_const_of_tendsto hconst (hT.congr fun t => by
      rw [← integral_const_mul]; simp [φ])]
    exact hO 1 le_rfl

/- English proof (translation)
Introduce `h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12` and use `localPC4_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12`.
-/
theorem localPC_of_steps : StAlg → StProfile → StFam → StHomot → StLim → StShape → StOrbAd → StOrbCpt → StNonEll → StTr →
    StTrAd → StKData → GlobalTheory.PsCo.Pc.LocalPC :=
  fun h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => localPC4_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12

end GlobalTheory.PsCo.Pc1
