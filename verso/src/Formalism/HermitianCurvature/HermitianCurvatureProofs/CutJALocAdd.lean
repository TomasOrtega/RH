import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocCC

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open NumberField Formalism.FourierDecayAlt.P.CutMP

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Unfold `JF.TransportedAlt`. Establish `hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)`. Establish `hr : (0 : ℝ) < (r : ℝ) + 1` using `by positivity`. Establish `hA' : 10 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ A` using `by simpa [nDim] using hA`. Establish `hn2 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `by nlinarith`.

Rewrite using `[lt_div_iff₀ (by positivity)]`. Simplify using `only [Nat.cast_zero, mul_zero, sub_zero]`. Use polynomial arithmetic with `[mul_pos hr (lt_of_lt_of_le one_pos hn2)]`.
-/
theorem locAdd_thr (k r : ℕ) {A : ℝ} (hA : 10 * ((r : ℝ) + 1) * nDim k r ^ 2 ≤ A) : JF.TransportedAlt k r A 0 := by
  unfold JF.TransportedAlt
  have hn : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * r + k + 1)
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hA' : 10 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 ≤ A := by simpa [nDim] using hA
  have hn2 : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  rw [lt_div_iff₀ (by positivity)]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  nlinarith [mul_pos hr (lt_of_lt_of_le one_pos hn2)]

/- English proof (translation)
Use `⟨10, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A J J' hBg hA hJ hJ'`. Establish `hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'` using `(hB.1.2.2.2.1.2 v).2.2.2.1`. Establish `hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z'`. Rewrite using `[hPl.2.2.2.1, hPl.2.2.2.2.1]`.

Both sides reduce to the same expression. Establish `hThr` using `locAdd_thr S.G.k S.G.r hA`. Use `⟨Formalism.FourierDecayAlt.P.Qx8.FFl_add hJ.1 hJ'.1, fun δ hδ => ?_⟩` and prove the remaining obligations. Take `⟨F, hF1, hF2, hF3⟩` from `hJ.2 δ hδ`. Take `⟨F', hF1', hF2', hF3'⟩` from `hJ'.2 δ hδ`.

Use `⟨F + F', Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hF1 hF1', fun m => ?_, fun x hx hG => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hF2 m`. Take `⟨c', hc'⟩` from `hF2' m`. Conclude with `⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩`. Establish `hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z'` using `⟨hx.1, hTT ▸ hx.2⟩`.

Establish `hg` using `Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq`. Establish `h0 : B.InCC A 0 F` using `by simpa using hF2 0`. Establish `h0' : B.InCC A 0 F'` using `by simpa using hF2' 0`. Establish `i1` using `(Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F hThr h0).1 _ hg`. Establish `i2` using `(Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F' hThr h0').1 _ hg`.

Establish `e : ∀ G : GFn S v, B.JF (T v).base G (B.gq (T v).base x) = ∫ p, JF.integrand (T v).base G (B.gq (T v).base x) p ∂(T v).base.μSS` using `fun G => rfl`. Rewrite using `[Pi.add_apply, hF3 x hx hG, hF3' x hx hG, e, e, e, ← integral_add i1 i2]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `only [JF.integrand, B.rho, Pi.add_apply, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, smul_add]`.
-/
theorem local_additivity_transfer : JALocAdd := by
  refine ⟨10, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top Cb A₀ hB v Bg A J J' hBg hA hJ hJ'
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  have hThr := locAdd_thr S.G.k S.G.r hA
  refine ⟨Formalism.FourierDecayAlt.P.Qx8.FFl_add hJ.1 hJ'.1, fun δ hδ => ?_⟩
  obtain ⟨F, hF1, hF2, hF3⟩ := hJ.2 δ hδ
  obtain ⟨F', hF1', hF2', hF3'⟩ := hJ'.2 δ hδ
  refine ⟨F + F', Formalism.FourierDecayAlt.P.JCx2.ckOn_add' hF1 hF1', fun m => ?_, fun x hx hG => ?_⟩
  · obtain ⟨c, hc⟩ := hF2 m
    obtain ⟨c', hc'⟩ := hF2' m
    exact ⟨c + c', Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hc hc'⟩
  · have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, hTT ▸ hx.2⟩
    have hg := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
    have h0 : B.InCC A 0 F := by simpa using hF2 0
    have h0' : B.InCC A 0 F' := by simpa using hF2' 0
    have i1 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F hThr h0).1 _ hg
    have i2 := (Formalism.FourierDecayAlt.P.bessel_integral_converges S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base A F' hThr h0').1 _ hg
    have e : ∀ G : GFn S v, B.JF (T v).base G (B.gq (T v).base x) =
        ∫ p, JF.integrand (T v).base G (B.gq (T v).base x) p ∂(T v).base.μSS := fun G => rfl
    rw [Pi.add_apply, hF3 x hx hG, hF3' x hx hG, e, e, e, ← integral_add i1 i2]
    congr 1
    funext p
    simp only [JF.integrand, B.rho, Pi.add_apply, ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add, smul_add]

end Formalism.FourierDecayAlt.P.CutMP.JA

end
