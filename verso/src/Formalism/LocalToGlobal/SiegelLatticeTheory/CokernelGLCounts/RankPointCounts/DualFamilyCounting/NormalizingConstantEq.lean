import Mathlib
import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff

noncomputable section

namespace Formalism.L2.SG.Pf.NcCut

open Formalism.FourierDecayAlt.S3

variable {P : Type} [Fintype P] (B : MassData P)

/- English proof (translation)
Take `⟨hp, -, -, -, -, hU0, -⟩` from `hP`. Establish `h0 : B.Mo = B.localVolumeArchimedean * (B.μKo * B.μKo) / (B.μSo * B.μSo')`. Establish `h` using `hO`. Unfold `MassData.InOrdinary at h`. Rewrite `h` using `[div_eq_iff hU0.ne']`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ∀ p, B.Mp p = B.localVolumeAtPlace p * (B.μKp p * B.μKnatp p) / (B.μSp p * B.μSp' p)`. Introduce `p`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hU⟩` from `hp p`.

Establish `h` using `(hT p).1`. Rewrite `h` using `[div_eq_iff hU.ne']`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Unfold `MassData.MM MassData.unitLevelVolume MassData.μK MassData.μKnat MassData.μS MassData.μS'`.

Simplify using `only [h0, h1, Finset.prod_div_distrib, Finset.prod_mul_distrib]`. Rewrite using `[div_mul_div_comm]`. Apply the tactic sequence `congr 1 <;> ring`.
-/
theorem MM_eq (hP : B.Pos) (hO : B.InOrdinary) (hT : B.InTyped) :
    B.MM = B.unitLevelVolume * B.μK * B.μKnat / (B.μS * B.μS') := by
  obtain ⟨hp, -, -, -, -, hU0, -⟩ := hP
  have h0 : B.Mo = B.localVolumeArchimedean * (B.μKo * B.μKo) / (B.μSo * B.μSo') := by
    have h := hO
    unfold MassData.InOrdinary at h
    rw [div_eq_iff hU0.ne'] at h
    rw [h]
    ring
  have h1 : ∀ p, B.Mp p = B.localVolumeAtPlace p * (B.μKp p * B.μKnatp p) / (B.μSp p * B.μSp' p) := by
    intro p
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hU⟩ := hp p
    have h := (hT p).1
    rw [div_eq_iff hU.ne'] at h
    rw [h]
    ring
  unfold MassData.MM MassData.unitLevelVolume MassData.μK MassData.μKnat MassData.μS MassData.μS'
  simp only [h0, h1, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  rw [div_mul_div_comm]
  congr 1 <;> ring

/- English proof (translation)
Establish `hMM` using `MM_eq B hP hO hT`. Take `⟨hp, hKo, -, -, -, -, hH, hH', -, -, hN, hN', hZZ, -, -, -, hHa, -, -, -, hB, hVH, -, -, -, hCoo, -, -, -, hr0, -⟩` from `hP`. Take `⟨hρ, hNa, -, hNa'⟩` from `hMs`. Take `⟨hS, -, hS', -⟩` from `hL`. Establish `hK : 0 < B.μK`.

Unfold `MassData.μK`. Conclude with `mul_pos hKo (Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.1)`. Establish `hvN : B.volN = 1 / B.μN`. Rewrite using `[eq_div_iff hN.ne', ← hNa, hV.1]`. Establish `hvN' : B.volN' = 1 / B.μN'`.

Rewrite using `[eq_div_iff hN'.ne', ← hNa', hV.2]`. Establish `hM' : B.n0c * B.ρ0 = B.AA` using `hM`. Unfold `MassData.AA at hM'`. Rewrite `hM'` using `[hMM, hS, hS']`. Establish `hn` using `eq_div_of_mul_eq hr0.ne' hM'`.

Rewrite using `[hn, hρ, hvN, hvN']`. Establish `h1` using `hK.ne'`. Establish `h2` using `hH.ne'`. Establish `h3` using `hH'.ne'`. Establish `h4` using `hN.ne'`.

Establish `h5` using `hN'.ne'`. Establish `h6` using `hZZ.ne'`. Establish `h7` using `hHa.ne'`. Establish `h8` using `hVH.ne'`. Clear the denominators using the available nonvanishing facts.
-/
theorem normalizing_constant_eq (hP : B.Pos) (hM : B.InMass) (hMs : B.InMasses) (hL : B.InLevelS) (hO : B.InOrdinary)
    (hT : B.InTyped) (hV : B.volNa = 1 ∧ B.volNa' = 1) :
    B.n0c = B.volB / B.volHa * B.Coo * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) * B.μKnat / B.μH' := by
  have hMM := MM_eq B hP hO hT
  obtain ⟨hp, hKo, -, -, -, -, hH, hH', -, -, hN, hN', hZZ, -, -, -, hHa, -, -, -, hB, hVH, -, -, -,
    hCoo, -, -, -, hr0, -⟩ := hP
  obtain ⟨hρ, hNa, -, hNa'⟩ := hMs
  obtain ⟨hS, -, hS', -⟩ := hL
  have hK : 0 < B.μK := by
    unfold MassData.μK
    exact mul_pos hKo (Finset.prod_pos fun p _ => (hp p).2.2.2.2.2.1)
  have hvN : B.volN = 1 / B.μN := by
    rw [eq_div_iff hN.ne', ← hNa, hV.1]
  have hvN' : B.volN' = 1 / B.μN' := by
    rw [eq_div_iff hN'.ne', ← hNa', hV.2]
  have hM' : B.n0c * B.ρ0 = B.AA := hM
  unfold MassData.AA at hM'
  rw [hMM, hS, hS'] at hM'
  have hn := eq_div_of_mul_eq hr0.ne' hM'
  rw [hn, hρ, hvN, hvN']
  have h1 := hK.ne'
  have h2 := hH.ne'
  have h3 := hH'.ne'
  have h4 := hN.ne'
  have h5 := hN'.ne'
  have h6 := hZZ.ne'
  have h7 := hHa.ne'
  have h8 := hVH.ne'
  field_simp

/- English proof (translation)
Rewrite using `[normalizing_constant_eq B hP hM hMs hL hO hT hV]`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hal, -⟩` from `hP`. Rewrite using `[eq_div_iff (mul_ne_zero hal.ne' hkap)]`. Apply the tactic sequence `constructor <;> intro h <;> linear_combination h`.
-/
theorem nc_iff (hP : B.Pos) (hM : B.InMass) (hMs : B.InMasses) (hL : B.InLevelS) (hO : B.InOrdinary)
    (hT : B.InTyped) (hV : B.volNa = 1 ∧ B.volNa' = 1) (c ng kap : ℝ) (hkap : kap ≠ 0) :
    c = B.n0c * ng / (B.al * kap) ↔
      c * B.al * kap = B.volB / B.volHa * B.Coo * B.volH * B.volN * B.volN' * (B.unitLevelVolume / B.volZZ) *
        B.μKnat / B.μH' * ng := by
  rw [normalizing_constant_eq B hP hM hMs hL hO hT hV]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hal, -⟩ := hP
  rw [eq_div_iff (mul_ne_zero hal.ne' hkap)]
  constructor <;> intro h <;> linear_combination h

end Formalism.L2.SG.Pf.NcCut
