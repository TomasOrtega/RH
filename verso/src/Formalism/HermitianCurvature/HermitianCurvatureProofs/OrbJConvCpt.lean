import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsHaarStabilizer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Dx3
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

/- English proof (translation)
Use `set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn`. Use `set bN : ℝ := 4 * ((r : ℝ) * nn + 1) with hbN`. Use `set c : ℕ := (c₁ + 1) * (r + 1) ^ 2 with hc`. Use `set M : ℝ := A / c - 2 * bN with hM`. Establish `hmono : C2.IsMonomial (Zhat k r D.z D.z' γ)` using `⟨w, d, hd, hZ⟩`.

Take `⟨CP, hCP, -⟩` from `hPP k r D.z D.z' γ (P.Dx2.Rad.std D) ⟨hγ, hpos⟩ hmono`. Establish `hc1 : 1 ≤ c` using `Nat.one_le_iff_ne_zero.mpr (by positivity)`. Establish `hcpos : (0 : ℝ) < c` using `by exact_mod_cast hc1`. Establish `hnn0 : 0 ≤ nn` using `by positivity`. Establish `hrn : 0 ≤ (r : ℝ) * nn` using `by positivity`.

Establish `hbN0 : 0 ≤ bN` using `by positivity`. Establish `hccast : (c : ℝ) = ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2` using `by rw [hc]; push_cast; ring`. Establish `hAc : 16 * ((r : ℝ) * nn + 1) ≤ A / c`. Rewrite using `[le_div_iff₀ hcpos, hccast]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hA4 : 4 * bN ≤ A / c` using `by rw [hbN]; linarith`. Establish `hk1 : (1 : ℝ) ≤ k` using `by exact_mod_cast D.k_pos`. Establish `hr2 : ((r : ℝ) + 1) ^ 2 ≤ (r : ℝ) * nn + 1`. Rewrite using `[hnn]`. Use `push_cast`.

Use polynomial arithmetic with `[mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) (show (0 : ℝ) ≤ r + k - 1 by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])]`. Establish `hMR : 2 * ((r : ℝ) + 1) ^ 2 < M`. Rewrite using `[hM, hbN]`. Use polynomial arithmetic with `[sq_nonneg ((r : ℝ) + 1)]`. Establish `hM0 : 0 ≤ M` using `by nlinarith [sq_nonneg ((r : ℝ) + 1)]`.

Establish `hA0 : 0 ≤ A`. Use `div_nonneg_iff.mp (show 0 ≤ A / c by linarith)` as an intermediate fact. Break down `this with h | h` into its components or cases. Conclude with `h.1`. Combine the linear relations using `[h.2]`.

Establish `hG : P.Dx2.Rad.Good D γ w d` using `⟨P.Dx2.Rad.exists_rho D hγ hpos hd hZ, P.Dx2.Rad.u_inj D hγ hpos hd hZ, fun ρ hρ => P.Dx2.Rad.u_lstg D hγ hpos hd hZ hρ⟩`. Establish `hR` using `P.Dx2.Rad.haar_good D hγ hd hG`. Use `P.Dx2.OrbJ.sigmaF hR` as an intermediate fact. Establish `hI` using `intR D hγ hd hG hMR`. Use `set μR := Formalism.FourierDecayAlt.D.muR D γ w with hμR`.

Use `set cR : ℝ := ∫ x, B.gN (Matrix.of x) ^ (-M) ∂μR with hcRdef`. Establish `hone : Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ B.GV k r`. Simplify using `using (P.unitary_group_closed k r).one_mem`. Establish `hcR : 0 < cR`. Use `om_pos hR hM0 hI hone` as an intermediate fact.

Simplify `this` using `[Om]`. Use `set cF := max sharpFunctionalExponent 0 with hcF`. Establish `hFb : ∀ g ∈ B.GV k r, ‖F g‖ ≤ cF * B.gN g ^ (-A)`. Introduce `g hg`. Establish `h0` using `hb g hg`.

Establish `hg1 : 1 ≤ B.gN g` using `P.BetaSesquilinearity.gN_ge_one hg`. Establish `hpw : 0 < B.gN g ^ A` using `Real.rpow_pos_of_pos (by linarith) _`. Rewrite using `[Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpw]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨KW, hKW1, hKW⟩` from `UW_bound D.z D.z_mem D.T_pos`.

Take `⟨KW', hKW1', hKW'⟩` from `UW_bound D.z' D.z'_mem D.T'_pos`. Use `set K1 := KW * KW' with hK1`. Use `set Kγ := B.gN γ⁻¹ * B.gN γ with hKγ`. Establish `hγ1 : 1 ≤ B.gN γ` using `P.BetaSesquilinearity.gN_ge_one hγ`. Establish `hγi : B.gN γ⁻¹ = B.gN γ` using `(P.norm_of_inverse k r γ hγ).1`.

Establish `hKγ0 : 0 < Kγ` using `by rw [hKγ, hγi]; nlinarith`. Use `set Kf := cF * K1 ^ A * CP ^ (A / c) * Kγ ^ bN / cR with hKf`. Use `⟨cut μR M, ⟨cut_meas M, cut_nonneg μR M, fun p hp => cut_norm hR hM0 hI p hp.2.1⟩, ?_⟩` and prove the remaining obligations. Establish `hmaj` using `(maj_int D (A / c - 3 * bN) bN (by linarith) le_rfl).const_mul Kf`. Use `Integrable.mono' hmaj ((cut_meas M).aestronglyMeasurable.smul (integrand_aesm D hγ hFc)) ?_` and prove the remaining obligations.

Use `filter_upwards [P.Dx2.OrbJ.ae_inSS D] with p hp`. Take `⟨h1, h2, h3, h4⟩` from `hp`. Take `⟨ρ, σ, X, hρ, hσ, hnρσ, hσX, hXY, hn'le⟩` from `geom D hγ hpos hCP hmono h2 h4`. Establish `hN1 : 1 ≤ B.gN (Matrix.of p.1.2 : B.Mat k r)` using `P.BetaSesquilinearity.gN_ge_one h2.1`. Establish `hN1' : 1 ≤ B.gN (Matrix.of p.2.2 : B.Mat k r)` using `P.BetaSesquilinearity.gN_ge_one h4.1`.

Establish `hS1 : 1 ≤ B.gN σ` using `P.BetaSesquilinearity.gN_ge_one hσ`. Establish `hg0 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 ∈ B.GV k r` using `Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hγ) h4.1`. Establish `hY1 : 1 ≤ B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2)` using `P.BetaSesquilinearity.gN_ge_one hg0`. Establish `hsgs` using `P.B7.sgs_mem D ⟨h1, h2, h3, h4⟩ hγ`. Establish `hGg : 0 < B.gN (B.sgs p γ)` using `by linarith [P.BetaSesquilinearity.gN_ge_one hsgs]`.

Establish `hYG : B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ≤ K1 * B.gN (B.sgs p γ)`. Establish `hhu : IsUnit (Matrix.of p.1.1 : B.Mat k r).det` using `(P.unitary_group_closed k r).unit _ h1.1`. Establish `hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det` using `(P.unitary_group_closed k r).unit _ h3.1`. Establish `e : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 = (Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹`. Simplify using `only [B.sgs, Matrix.mul_assoc]`.

Rewrite using `[Matrix.mul_nonsing_inv_cancel_left _ _ hhu, Matrix.mul_nonsing_inv _ hh'u, Matrix.mul_one]`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Establish `a1` using `hKW _ h1`. Establish `a2` using `hKW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)`.

Establish `s0` using `P.B6.gN_nonneg (B.sgs p γ)`. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_right a1 s0) a2 (P.B6.gN_nonneg _) (mul_nonneg (by linarith) s0)`. Use `_ = K1 * B.gN (B.sgs p γ) := by rw [hK1]; ring`. Establish `hθ : cut μR M p ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR`. Establish `hlow` using `om_lower hR hM0 hI hρ hσ`.

Establish `e : Matrix.of.symm (ρ * σ) = p.1.2` using `by rw [← hnρσ]; exact Equiv.symm_apply_apply _ _`. Rewrite `hlow` using `[e]`. Establish `hσp : 0 < B.gN σ ^ (-M)` using `Real.rpow_pos_of_pos (by linarith) _`. Establish `hpos' : 0 < cR * B.gN σ ^ (-M)` using `mul_pos hcR hσp`. Unfold `cut`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.rpow_neg (P.B6.gN_nonneg σ)]`. Establish `: 0 < B.gN σ ^ M` using `Real.rpow_pos_of_pos (by linarith) _`. Clear the denominators using the available nonvanishing facts. Establish `hθ0` using `cut_nonneg μR M p`.

Establish `hFv : ‖B.rho D p F γ‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)` using `(P.B7.norm_rho_le D ⟨h1, h2, h3, h4⟩ F γ).trans (hFb _ hsgs)`. Establish `hCP0 : 0 < CP`. Assume the negation of the conclusion as `hle'`. Establish `hle` using `not_lt.mp hle'`. Use `mul_nonpos_of_nonpos_of_nonneg hle (pow_nonneg (P.B6.gN_nonneg ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2)) (c₁ * (r + 1) ^ 2))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hec : c₁ * (r + 1) ^ 2 ≤ c` using `Nat.mul_le_mul_right _ (Nat.le_succ _)`. Establish `hXY' : X ≤ CP * B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ^ c` using `hXY.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hec) hCP0.le)`. Establish `hK10 : 0 < K1` using `by rw [hK1]; positivity`. Establish `hkey` using `key_real hN1 hS1 hσX hY1 hGg hc1 hXY' hn'le hN1' hYG hθ hθ0 hFv (norm_nonneg _) hcR (le_max_right _ _) hCP0 hK10 hKγ0 hM hbN0 hA4`.

Rewrite using `[norm_smul, Real.norm_of_nonneg hθ0]`. Unfold `Formalism.FourierDecayAlt.D.orbIntegrand`. Rewrite using `[norm_smul, P.B7.norm_xi, one_mul]`. Conclude with `hkey`.
-/
theorem conv0 (D : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ)
    (A : ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (c₁ : ℕ)
    (hPP : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r), C2.Std k r z z' → C2.PosPt k r z z' γ →
      C2.IsMonomial (Zhat k r z z' γ) → ∃ C : ℝ,
        (∀ σ ∈ C2.Sg k r z z' γ, ∀ s' ∈ Sset k r z',
          B.gN σ + B.gN s' ≤ C * B.gN (σ⁻¹ * γ * s') ^ (c₁ * (r + 1) ^ 2)) ∧
        (∀ s ∈ Sset k r z, ∀ σ' ∈ C2.Sg' k r z z' γ,
          B.gN s + B.gN σ' ≤ C * B.gN (s⁻¹ * γ * σ') ^ (c₁ * (r + 1) ^ 2)))
    (hγ : γ ∈ B.GV k r) (hd : ∀ a, d a ≠ 0) (hZ : Zhat k r D.z D.z' γ = C2.monoP w d)
    (hpos : 0 < Gf k r D.z D.z' γ)
    (hA : 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A)
    (hFc : ContinuousOn F (B.GV k r)) (sharpFunctionalExponent : ℝ) (hb : ∀ g ∈ B.GV k r, B.gN g ^ A * ‖F g‖ ≤ sharpFunctionalExponent) :
    ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ (Formalism.FourierDecayAlt.D.muR D γ w) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS := by
  set nn : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hnn
  set bN : ℝ := 4 * ((r : ℝ) * nn + 1) with hbN
  set c : ℕ := (c₁ + 1) * (r + 1) ^ 2 with hc
  set M : ℝ := A / c - 2 * bN with hM
  have hmono : C2.IsMonomial (Zhat k r D.z D.z' γ) := ⟨w, d, hd, hZ⟩
  obtain ⟨CP, hCP, -⟩ := hPP k r D.z D.z' γ (P.Dx2.Rad.std D) ⟨hγ, hpos⟩ hmono

  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc1
  have hnn0 : 0 ≤ nn := by positivity
  have hrn : 0 ≤ (r : ℝ) * nn := by positivity
  have hbN0 : 0 ≤ bN := by positivity
  have hccast : (c : ℝ) = ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 := by rw [hc]; push_cast; ring
  have hAc : 16 * ((r : ℝ) * nn + 1) ≤ A / c := by
    rw [le_div_iff₀ hcpos, hccast]
    calc 16 * ((r : ℝ) * nn + 1) * (((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2)
        = 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * nn + 1) := by ring
      _ ≤ A := hA
  have hA4 : 4 * bN ≤ A / c := by rw [hbN]; linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hr2 : ((r : ℝ) + 1) ^ 2 ≤ (r : ℝ) * nn + 1 := by
    rw [hnn]; push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
      (show (0 : ℝ) ≤ r + k - 1 by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)])]
  have hMR : 2 * ((r : ℝ) + 1) ^ 2 < M := by
    rw [hM, hbN]; nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hM0 : 0 ≤ M := by nlinarith [sq_nonneg ((r : ℝ) + 1)]
  have hA0 : 0 ≤ A := by
    have := div_nonneg_iff.mp (show 0 ≤ A / c by linarith)
    rcases this with h | h
    · exact h.1
    · linarith [h.2]

  have hG : P.Dx2.Rad.Good D γ w d := ⟨P.Dx2.Rad.exists_rho D hγ hpos hd hZ, P.Dx2.Rad.u_inj D hγ hpos hd hZ,
    fun ρ hρ => P.Dx2.Rad.u_lstg D hγ hpos hd hZ hρ⟩
  have hR := P.Dx2.Rad.haar_good D hγ hd hG
  have := P.Dx2.OrbJ.sigmaF hR
  have hI := intR D hγ hd hG hMR
  set μR := Formalism.FourierDecayAlt.D.muR D γ w with hμR
  set cR : ℝ := ∫ x, B.gN (Matrix.of x) ^ (-M) ∂μR with hcRdef
  have hone : Matrix.of (Matrix.of.symm (1 : B.Mat k r)) ∈ B.GV k r := by
    simpa using (P.unitary_group_closed k r).one_mem
  have hcR : 0 < cR := by
    have := om_pos hR hM0 hI hone
    simpa [Om] using this

  set cF := max sharpFunctionalExponent 0 with hcF
  have hFb : ∀ g ∈ B.GV k r, ‖F g‖ ≤ cF * B.gN g ^ (-A) := by
    intro g hg
    have h0 := hb g hg
    have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
    have hpw : 0 < B.gN g ^ A := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hpw]
    calc ‖F g‖ * B.gN g ^ A = B.gN g ^ A * ‖F g‖ := by ring
      _ ≤ sharpFunctionalExponent := h0
      _ ≤ cF := le_max_left _ _

  obtain ⟨KW, hKW1, hKW⟩ := UW_bound D.z D.z_mem D.T_pos
  obtain ⟨KW', hKW1', hKW'⟩ := UW_bound D.z' D.z'_mem D.T'_pos
  set K1 := KW * KW' with hK1
  set Kγ := B.gN γ⁻¹ * B.gN γ with hKγ
  have hγ1 : 1 ≤ B.gN γ := P.BetaSesquilinearity.gN_ge_one hγ
  have hγi : B.gN γ⁻¹ = B.gN γ := (P.norm_of_inverse k r γ hγ).1
  have hKγ0 : 0 < Kγ := by rw [hKγ, hγi]; nlinarith
  set Kf := cF * K1 ^ A * CP ^ (A / c) * Kγ ^ bN / cR with hKf
  refine ⟨cut μR M, ⟨cut_meas M, cut_nonneg μR M, fun p hp => cut_norm hR hM0 hI p hp.2.1⟩, ?_⟩
  have hmaj := (maj_int D (A / c - 3 * bN) bN (by linarith) le_rfl).const_mul Kf
  refine Integrable.mono' hmaj ((cut_meas M).aestronglyMeasurable.smul (integrand_aesm D hγ hFc)) ?_
  filter_upwards [P.Dx2.OrbJ.ae_inSS D] with p hp
  obtain ⟨h1, h2, h3, h4⟩ := hp
  obtain ⟨ρ, σ, X, hρ, hσ, hnρσ, hσX, hXY, hn'le⟩ := geom D hγ hpos hCP hmono h2 h4
  have hN1 : 1 ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h2.1
  have hN1' : 1 ≤ B.gN (Matrix.of p.2.2 : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one h4.1
  have hS1 : 1 ≤ B.gN σ := P.BetaSesquilinearity.gN_ge_one hσ
  have hg0 : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 ∈ B.GV k r :=
    Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv h2.1) hγ) h4.1
  have hY1 : 1 ≤ B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) := P.BetaSesquilinearity.gN_ge_one hg0
  have hsgs := P.B7.sgs_mem D ⟨h1, h2, h3, h4⟩ hγ
  have hGg : 0 < B.gN (B.sgs p γ) := by linarith [P.BetaSesquilinearity.gN_ge_one hsgs]
  have hYG : B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ≤ K1 * B.gN (B.sgs p γ) := by
    have hhu : IsUnit (Matrix.of p.1.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h1.1
    have hh'u : IsUnit (Matrix.of p.2.1 : B.Mat k r).det := (P.unitary_group_closed k r).unit _ h3.1
    have e : (Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2 =
        (Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹ := by
      simp only [B.sgs, Matrix.mul_assoc]
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ hhu, Matrix.mul_nonsing_inv _ hh'u, Matrix.mul_one]
    rw [e]
    calc B.gN ((Matrix.of p.1.1 : B.Mat k r) * B.sgs p γ * (Matrix.of p.2.1 : B.Mat k r)⁻¹)
        ≤ B.gN (Matrix.of p.1.1 : B.Mat k r) * B.gN (B.sgs p γ) * B.gN (Matrix.of p.2.1 : B.Mat k r)⁻¹ :=
          (P.B6.gN_mul_le _ _).trans (mul_le_mul_of_nonneg_right (P.B6.gN_mul_le _ _) (P.B6.gN_nonneg _))
      _ ≤ KW * B.gN (B.sgs p γ) * KW' := by
          have a1 := hKW _ h1
          have a2 := hKW' _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv h3)
          have s0 := P.B6.gN_nonneg (B.sgs p γ)
          exact mul_le_mul (mul_le_mul_of_nonneg_right a1 s0) a2 (P.B6.gN_nonneg _)
            (mul_nonneg (by linarith) s0)
      _ = K1 * B.gN (B.sgs p γ) := by rw [hK1]; ring
  have hθ : cut μR M p ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
    have hlow := om_lower hR hM0 hI hρ hσ
    have e : Matrix.of.symm (ρ * σ) = p.1.2 := by rw [← hnρσ]; exact Equiv.symm_apply_apply _ _
    rw [e] at hlow
    have hσp : 0 < B.gN σ ^ (-M) := Real.rpow_pos_of_pos (by linarith) _
    have hpos' : 0 < cR * B.gN σ ^ (-M) := mul_pos hcR hσp
    unfold cut
    calc B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / Om μR M p.1.2
        ≤ B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) / (cR * B.gN σ ^ (-M)) :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg (P.B6.gN_nonneg _) _) hpos' hlow
      _ = B.gN (Matrix.of p.1.2 : B.Mat k r) ^ (-M) * B.gN σ ^ M / cR := by
          rw [Real.rpow_neg (P.B6.gN_nonneg σ)]
          have : 0 < B.gN σ ^ M := Real.rpow_pos_of_pos (by linarith) _
          field_simp
  have hθ0 := cut_nonneg μR M p
  have hFv : ‖B.rho D p F γ‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A) :=
    (P.B7.norm_rho_le D ⟨h1, h2, h3, h4⟩ F γ).trans (hFb _ hsgs)
  have hCP0 : 0 < CP := by
    by_contra hle'
    have hle := not_lt.mp hle'
    have := mul_nonpos_of_nonpos_of_nonneg hle
      (pow_nonneg (P.B6.gN_nonneg ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2)) (c₁ * (r + 1) ^ 2))
    linarith
  have hec : c₁ * (r + 1) ^ 2 ≤ c := Nat.mul_le_mul_right _ (Nat.le_succ _)
  have hXY' : X ≤ CP * B.gN ((Matrix.of p.1.2 : B.Mat k r)⁻¹ * γ * Matrix.of p.2.2) ^ c :=
    hXY.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hY1 hec) hCP0.le)
  have hK10 : 0 < K1 := by rw [hK1]; positivity
  have hkey := key_real hN1 hS1 hσX hY1 hGg hc1 hXY' hn'le hN1' hYG hθ hθ0 hFv (norm_nonneg _) hcR
    (le_max_right _ _) hCP0 hK10 hKγ0 hM hbN0 hA4
  rw [norm_smul, Real.norm_of_nonneg hθ0]
  unfold Formalism.FourierDecayAlt.D.orbIntegrand
  rw [norm_smul, P.B7.norm_xi, one_mul]
  exact hkey

/- English proof (translation)
Take `⟨hCk, ⟨R, hR⟩, -⟩` from `hF`. Establish `hFc : ContinuousOn F (B.GV k r)` using `P.B5.ckOn_continuousOn hCk`. Use `set K : Set (B.Mat k r) := B.GV k r ∩ {g | B.gN g ≤ R} with hK`. Establish `hgNc : Continuous (fun g : B.Mat k r => B.gN g)`. Unfold `B.gN`.

Use `Real.continuous_sqrt.comp ?_` and prove the remaining obligations. Use `continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))`. Establish `hKc : IsCompact K`. Establish `hbox : IsCompact (Set.univ.pi fun _ : Fin (2 * r + k + 1) => Set.univ.pi fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) (max R 0))` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`.

Use `hbox.of_isClosed_subset ((P.unitary_group_closed k r).closed.inter (isClosed_le hgNc continuous_const)) ?_` and prove the remaining obligations. Introduce `g hg`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]`. Introduce `i j`. Conclude with `(entry_le_gN g i j).trans (hg.2.trans (le_max_left _ _))`.

Take `⟨C, hC⟩` from `hKc.exists_bound_of_continuousOn (hFc.mono Set.inter_subset_left)`. Use `⟨(max R 1) ^ A * max C 0, fun g hg => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hF0 : F g = 0`. Rewrite using `[hF0, norm_zero, mul_zero]`. Conclude with `mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_max_right _ _)`.

Establish `hgR` using `hR g hg hF0`. Establish `hg1 : 1 ≤ B.gN g` using `P.BetaSesquilinearity.gN_ge_one hg`. Establish `h1 : B.gN g ^ A ≤ (max R 1) ^ A` using `Real.rpow_le_rpow (by linarith) (hgR.trans (le_max_left _ _)) hA`. Establish `h2 : ‖F g‖ ≤ max C 0` using `(hC g ⟨hg, hgR⟩).trans (le_max_left _ _)`. Conclude with `mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)`.
-/
theorem cpt_bound (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hF : KB.CptCoef D F) (A : ℝ)
    (hA : 0 ≤ A) : ∃ c : ℝ, ∀ g ∈ B.GV k r, B.gN g ^ A * ‖F g‖ ≤ c := by
  obtain ⟨hCk, ⟨R, hR⟩, -⟩ := hF
  have hFc : ContinuousOn F (B.GV k r) := P.B5.ckOn_continuousOn hCk
  set K : Set (B.Mat k r) := B.GV k r ∩ {g | B.gN g ≤ R} with hK
  have hgNc : Continuous (fun g : B.Mat k r => B.gN g) := by
    unfold B.gN
    refine Real.continuous_sqrt.comp ?_
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  have hKc : IsCompact K := by
    have hbox : IsCompact (Set.univ.pi fun _ : Fin (2 * r + k + 1) =>
        Set.univ.pi fun _ : Fin (2 * r + k + 1) => Metric.closedBall (0 : ℂ) (max R 0)) :=
      isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    refine hbox.of_isClosed_subset ((P.unitary_group_closed k r).closed.inter
      (isClosed_le hgNc continuous_const)) ?_
    intro g hg
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Metric.mem_closedBall, dist_zero_right]
    intro i j
    exact (entry_le_gN g i j).trans (hg.2.trans (le_max_left _ _))
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hFc.mono Set.inter_subset_left)
  refine ⟨(max R 1) ^ A * max C 0, fun g hg => ?_⟩
  by_cases hF0 : F g = 0
  · rw [hF0, norm_zero, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (le_max_right _ _)
  · have hgR := hR g hg hF0
    have hg1 : 1 ≤ B.gN g := P.BetaSesquilinearity.gN_ge_one hg
    have h1 : B.gN g ^ A ≤ (max R 1) ^ A :=
      Real.rpow_le_rpow (by linarith) (hgR.trans (le_max_left _ _)) hA
    have h2 : ‖F g‖ ≤ max C 0 := (hC g ⟨hg, hgR⟩).trans (le_max_left _ _)
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)

/- English proof (translation)
Take `⟨c₁, hPP⟩` from `Formalism.FourierDecayAlt.P.polynomial_map_proper`. Use `set A : ℝ := 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) with hAdef`. Establish `hA0 : 0 ≤ A` using `by positivity`. Take `⟨c, hc⟩` from `cpt_bound S F hF A hA0`. Conclude with `conv0 S γ w d A F c₁ hPP hγ hd hZ hpos le_rfl (P.B5.ckOn_continuousOn hF.1) c hc`.
-/
theorem orbJConv_cpt (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (d : Fin (r + 1) → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hγ : γ ∈ B.GV k r) (hrel : C6.IsRelevant S γ)
    (hd : ∀ a, d a ≠ 0) (hZ : Zhat k r S.z S.z' γ = C2.monoP w d) (hpos : 0 < Gf k r S.z S.z' γ)
    (hF : KB.CptCoef S F) :
    ∃ θ, D.IsNormCut S γ (D.muR S γ w) θ ∧ Integrable (fun p => θ p • D.orbIntegrand S γ F p) S.μSS := by
  obtain ⟨c₁, hPP⟩ := Formalism.FourierDecayAlt.P.polynomial_map_proper
  set A : ℝ := 16 * ((c₁ : ℝ) + 1) * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) with hAdef
  have hA0 : 0 ≤ A := by positivity
  obtain ⟨c, hc⟩ := cpt_bound S F hF A hA0
  exact conv0 S γ w d A F c₁ hPP hγ hd hZ hpos le_rfl (P.B5.ckOn_continuousOn hF.1) c hc

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.CV
