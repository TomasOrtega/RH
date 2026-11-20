import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace PositivityTheory.RgBcC.VC

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Use `show y.val.det ≠ 0`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero`.
-/
theorem mem_GLs (y : G n) : y.val ∈ GLs n := by
  show y.val.det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

/- English proof (translation)
Use `show k.1.det ≠ 0`. Introduce `h0`. Establish `h` using `congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 k.2)`. Rewrite `h` using `[Matrix.det_mul, h0, mul_zero, Matrix.det_one]`. Conclude with `zero_ne_one h`.
-/
theorem unitary_mem_GLs (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  show k.1.det ≠ 0
  intro h0
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.1 k.2)
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at h
  exact zero_ne_one h

def trT {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (T : V →L[ℂ] V) :
    (V →L[ℂ] V) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.trace ℂ V).comp ((ContinuousLinearMap.coeLM ℂ).comp ((ContinuousLinearMap.mul ℂ (V →L[ℂ] V)).flip T).toLinearMap))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trT_apply {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (T B : V →L[ℂ] V) :
    trT T B = LinearMap.trace ℂ V ((B * T : V →L[ℂ] V) : V →ₗ[ℂ] V) := rfl

/- English proof (translation)
Use `show (1 : Mat n).det ≠ 0`. Simplify using the standard rewrite rules.
-/
theorem one_mem_GLs : (1 : Mat n) ∈ GLs n := by
  show (1 : Mat n).det ≠ 0
  simp

/- English proof (translation)
Introduce `hWE hWS hGC hGF hFF hNU hKZ hIS n lam E Fr ε ι S Γ T h _ _ μ _ w g τ k hg hk d W₁ W₂ hW hW1 hd1 hd2 N hN ν _`. Take `⟨H, hHs, hHh, hHtr, hHk, hHq, hHd⟩` from `hFF n W₁ W₂ hW hW1`. Set `A : Mat n → (E.V →L[ℂ] E.V)` to `fun x => ε (H x)`. Establish `hA : IsField E A`. Use `⟨(LinearMap.toContinuousLinearMap ε).contDiff.comp_contDiffOn hHs, fun x hx k₀ => ?_⟩` and prove the remaining obligations.

Establish `e1` using `h.frε k₀.1 (unitary_mem_GLs k₀) (H x) (hHh x hx)`. Rewrite `e1` using `[h.onK k₀]`. Establish `e2 : E.ρ k₀⁻¹ * E.ρ k₀ = 1` using `by rw [← map_mul, inv_mul_cancel, map_one]`. Use `show ε (H (x * k₀.1)) = E.ρ k₀⁻¹ * ε (H x) * E.ρ k₀`. Rewrite using `[hHk x hx k₀]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hAq : QInv W₁ W₂ A` using `fun q hq h1 h2 x hx => by show ε (H (q * x)) = ε (H x)`. Rewrite using `[hHq q hq h1 h2 x hx]`. Establish `hcomm` using `hKC hWE hWS hGC hGF hIS n μ E w g τ k hg hk W₁ W₂ hW A hA hAq`. Take `⟨hks, ⟨R, hR⟩, hbi, -⟩` from `hk`.

Establish `hid` using `hKN hNU hKZ hNA n μ E k hks ⟨R, hR⟩ hbi W₁ W₂ hW N hN ν A hA hAq hcomm d.val (mem_GLs d)`. Establish `hd : A d.val = -A 1` using `by show ε (H d.val) = -ε (H 1)`. Rewrite using `[hHd d.val (mem_GLs d) hd1 hd2, map_neg]`. Rewrite `hid` using `[hd]`. Use `set B := ∫ u : N, k ((u : G n).val * d.val) ∂ν with hBdef`.

Establish `hanti : A 1 * B = -(B * A 1)` using `by rw [← hid, mul_neg]`. Establish `htr : trT T B = 0`. Rewrite using `[trT_apply]`. Conclude with `hTZ E.V B T (ε (H 1)) (ι (H 1)) ((H 1 * H 1).trace) hHtr (h.car _ _ (hHh 1 one_mem_GLs) (hHh 1 one_mem_GLs)) hanti (h.Tε _)`. Establish `hcont : Continuous fun u : N => k ((u : G n).val * d.val)`.

Use `hks.continuousOn.comp_continuous ?_ fun u => ?_` and prove the remaining obligations. Conclude with `(Units.continuous_val.comp continuous_subtype_val).matrix_mul continuous_const`. Conclude with `mem_GLs ((u : G n) * d)`. Establish `hNc : IsClosed (N : Set (G n))` using `(hNU n W₁ W₂ hW N hN).1`. Establish `hK : IsCompact ((fun u : N => (u : G n)) ⁻¹' ((fun y : G n => y * d) ⁻¹' {y : G n | lg y.val ≤ R}))`.

Use `hNc.isClosedEmbedding_subtypeVal.isCompact_preimage ?_` and prove the remaining obligations. Establish `: (fun y : G n => y * d) ⁻¹' {y : G n | lg y.val ≤ R} = (fun y : G n => y * d⁻¹) '' {y : G n | lg y.val ≤ R}`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce `hy`. Conclude with `⟨y * d, hy, by rw [mul_assoc, mul_inv_cancel, mul_one]⟩`. Introduce and unpack `⟨z, hz, rfl⟩`. Rewrite using `[Set.mem_ofPred_eq, mul_assoc, inv_mul_cancel, mul_one]` and apply the resulting hypothesis. Rewrite using `[this]`.

Conclude with `(hLg n R).image (continuous_id.mul continuous_const)`. Establish `hcpt : HasCompactSupport fun u : N => k ((u : G n).val * d.val)`. Use `HasCompactSupport.intro hK fun u hu => ?_` and prove the remaining obligations. Use `hR _ (mem_GLs ((u : G n) * d)) ?_` and prove the remaining obligations. Simplify using `only [Set.mem_preimage, Set.mem_ofPred_eq, not_le] at hu`.

Conclude with `hu`. Establish `hint : Integrable (fun u : N => k ((u : G n).val * d.val)) ν` using `hcont.integrable_of_hasCompactSupport hcpt`. Establish `hphi : (fun u : N => phiOf E T k (u * d)) = fun u : N => trT T (k ((u : G n).val * d.val))` using `rfl`. Use `⟨by rw [hphi]; exact (trT T).integrable_comp hint, ?_⟩` and prove the remaining obligations. Rewrite using `[hphi, (trT T).integral_comp_comm hint]`.

Conclude with `htr`.
-/
theorem vcKer_of (hKC : KerComm) (hKN : KerNId) (hNA : NAvg) (hTZ : TrZero) (hLg : LgCpt) : VCKer := by
  intro hWE hWS hGC hGF hFF hNU hKZ hIS n lam E Fr ε ι S Γ T h _ _ μ _ w g τ k hg hk d W₁ W₂ hW hW1 hd1 hd2 N hN ν _
  obtain ⟨H, hHs, hHh, hHtr, hHk, hHq, hHd⟩ := hFF n W₁ W₂ hW hW1
  let A : Mat n → (E.V →L[ℂ] E.V) := fun x => ε (H x)
  have hA : IsField E A := by
    refine ⟨(LinearMap.toContinuousLinearMap ε).contDiff.comp_contDiffOn hHs, fun x hx k₀ => ?_⟩
    have e1 := h.frε k₀.1 (unitary_mem_GLs k₀) (H x) (hHh x hx)
    rw [h.onK k₀] at e1
    have e2 : E.ρ k₀⁻¹ * E.ρ k₀ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
    show ε (H (x * k₀.1)) = E.ρ k₀⁻¹ * ε (H x) * E.ρ k₀
    rw [hHk x hx k₀]
    calc ε (k₀.1ᴴ * H x * k₀.1) = (E.ρ k₀⁻¹ * E.ρ k₀) * ε (k₀.1ᴴ * H x * k₀.1) := by rw [e2, one_mul]
      _ = E.ρ k₀⁻¹ * (E.ρ k₀ * ε (k₀.1ᴴ * H x * k₀.1)) := mul_assoc _ _ _
      _ = E.ρ k₀⁻¹ * (ε (H x) * E.ρ k₀) := by rw [← e1]
      _ = E.ρ k₀⁻¹ * ε (H x) * E.ρ k₀ := (mul_assoc _ _ _).symm
  have hAq : QInv W₁ W₂ A := fun q hq h1 h2 x hx => by
    show ε (H (q * x)) = ε (H x)
    rw [hHq q hq h1 h2 x hx]
  have hcomm := hKC hWE hWS hGC hGF hIS n μ E w g τ k hg hk W₁ W₂ hW A hA hAq
  obtain ⟨hks, ⟨R, hR⟩, hbi, -⟩ := hk
  have hid := hKN hNU hKZ hNA n μ E k hks ⟨R, hR⟩ hbi W₁ W₂ hW N hN ν A hA hAq hcomm d.val (mem_GLs d)
  have hd : A d.val = -A 1 := by
    show ε (H d.val) = -ε (H 1)
    rw [hHd d.val (mem_GLs d) hd1 hd2, map_neg]
  rw [hd] at hid
  set B := ∫ u : N, k ((u : G n).val * d.val) ∂ν with hBdef
  have hanti : A 1 * B = -(B * A 1) := by rw [← hid, mul_neg]
  have htr : trT T B = 0 := by
    rw [trT_apply]
    exact hTZ E.V B T (ε (H 1)) (ι (H 1)) ((H 1 * H 1).trace) hHtr
      (h.car _ _ (hHh 1 one_mem_GLs) (hHh 1 one_mem_GLs)) hanti (h.Tε _)
  have hcont : Continuous fun u : N => k ((u : G n).val * d.val) := by
    refine hks.continuousOn.comp_continuous ?_ fun u => ?_
    · exact (Units.continuous_val.comp continuous_subtype_val).matrix_mul continuous_const
    · exact mem_GLs ((u : G n) * d)
  have hNc : IsClosed (N : Set (G n)) := (hNU n W₁ W₂ hW N hN).1
  have hK : IsCompact ((fun u : N => (u : G n)) ⁻¹' ((fun y : G n => y * d) ⁻¹' {y : G n | lg y.val ≤ R})) := by
    refine hNc.isClosedEmbedding_subtypeVal.isCompact_preimage ?_
    have : (fun y : G n => y * d) ⁻¹' {y : G n | lg y.val ≤ R} = (fun y : G n => y * d⁻¹) '' {y : G n | lg y.val ≤ R} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro hy
        exact ⟨y * d, hy, by rw [mul_assoc, mul_inv_cancel, mul_one]⟩
      · rintro ⟨z, hz, rfl⟩
        rwa [Set.mem_ofPred_eq, mul_assoc, inv_mul_cancel, mul_one]
    rw [this]
    exact (hLg n R).image (continuous_id.mul continuous_const)
  have hcpt : HasCompactSupport fun u : N => k ((u : G n).val * d.val) := by
    refine HasCompactSupport.intro hK fun u hu => ?_
    refine hR _ (mem_GLs ((u : G n) * d)) ?_
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, not_le] at hu
    exact hu
  have hint : Integrable (fun u : N => k ((u : G n).val * d.val)) ν := hcont.integrable_of_hasCompactSupport hcpt
  have hphi : (fun u : N => phiOf E T k (u * d)) = fun u : N => trT T (k ((u : G n).val * d.val)) := rfl
  refine ⟨by rw [hphi]; exact (trT T).integrable_comp hint, ?_⟩
  rw [hphi, (trT T).integral_comp_comm hint]
  exact htr

/- English proof (translation)
Introduce `hWE hWS _ hGC hGF hFF hNU hKZ n lam E Fr ε ι S Γ T h _ _ μ _ k val τ hk d W₁ W₂ hW hW1 hd1 hd2 N hN ν _`. Take `⟨m, c, w, g, ks, hks, hsum, -⟩` from `hk`. Establish `key : ∀ i, Integrable (fun u : N => phiOf E T (ks i) (u * d)) ν ∧ ∫ u : N, phiOf E T (ks i) (u * d) ∂ν = 0` using `fun i => hVK hWE hWS hGC hGF hFF hNU hKZ hIS n lam E Fr ε ι S Γ T h μ (w i) (g i) τ (ks i) (hks i).1 (hks i).2 d W₁ W₂ hW hW1 hd1 hd2 N hN ν`. Establish `hpt : (fun u : N => phiOf E T k (u * d)) = fun u : N => ∑ i, c i * phiOf E T (ks i) (u * d)`. Use function extensionality and compare the values at `u`.

Use `show trT T (k ((u : G n) * d).val) = ∑ i, c i * trT T (ks i ((u : G n) * d).val)`. Rewrite using `[hsum _ (mem_GLs _), map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Rewrite using `[hpt, integral_finsetSum _ fun i _ => (key i).1.const_mul (c i)]`. Simplify using `only [integral_const_mul, (key _).2, mul_zero, Finset.sum_const_zero]`.
-/
theorem vcOf_of (hIS : IntSmooth) (hVK : VCKer) : VCOf := by
  intro hWE hWS _ hGC hGF hFF hNU hKZ n lam E Fr ε ι S Γ T h _ _ μ _ k val τ hk d W₁ W₂ hW hW1 hd1 hd2 N hN ν _
  obtain ⟨m, c, w, g, ks, hks, hsum, -⟩ := hk
  have key : ∀ i, Integrable (fun u : N => phiOf E T (ks i) (u * d)) ν ∧ ∫ u : N, phiOf E T (ks i) (u * d) ∂ν = 0 :=
    fun i => hVK hWE hWS hGC hGF hFF hNU hKZ hIS n lam E Fr ε ι S Γ T h μ (w i) (g i) τ (ks i) (hks i).1 (hks i).2
      d W₁ W₂ hW hW1 hd1 hd2 N hN ν
  have hpt : (fun u : N => phiOf E T k (u * d)) = fun u : N => ∑ i, c i * phiOf E T (ks i) (u * d) := by
    funext u
    show trT T (k ((u : G n) * d).val) = ∑ i, c i * trT T (ks i ((u : G n) * d).val)
    rw [hsum _ (mem_GLs _), map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hpt, integral_finsetSum _ fun i _ => (key i).1.const_mul (c i)]
  simp only [integral_const_mul, (key _).2, mul_zero, Finset.sum_const_zero]

end PositivityTheory.RgBcC.VC
