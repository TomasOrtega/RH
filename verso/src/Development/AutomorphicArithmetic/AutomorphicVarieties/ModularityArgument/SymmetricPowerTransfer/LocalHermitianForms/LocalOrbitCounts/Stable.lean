import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.ExistsUnitOneAddGenerator
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SumShift
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.Vanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GVals
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.GOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.SqrtO
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.RootEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.OfEMulStar
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.ClsSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FixPSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatLam
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.DatFormM
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FixPMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.PStable
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.KapRam
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.KapMove
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.UnitAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NonsqMul

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Unfold `Stable`. Introduce `O K _ _ _ _ _ Δ τ hL c d m hD hev j hj χ hχ a ha`. Establish `hreg` using `hD.reg`. Establish `hc` using `hD.c_ne`. Establish `h2K : (2 : K) ≠ 0`.

Establish `h` using `hL.two.map (algebraMap O K)`. Rewrite `h` using `[map_ofNat]`. Conclude with `h.ne_zero`. Establish `hshift : ∀ (f : Kˣ → ℂ), (∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x) → ∀ g : Kˣ, (∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * g)) → stabSum O c d m = ∑ᶠ t : Kˣ ⧸ NE τ, f (Quotient.out t)`. Introduce `f hf g hk`.

Unfold `stabSum`. Rewrite using `[finsum_congr (fun t => hk _)]`. Conclude with `(sumShift O K Δ τ hL hreg f hf g).1`. Distinguish the cases in `hτ : τ ∈ (algebraMap O K).range`. Use `swap`.

Establish `h0 : ∀ t : Kˣ, lcount O c d ((t : K) • m) = 0`. Introduce `t`. Assume the negation of the conclusion as `hne`. Conclude with `hτ (vanish O K Δ τ hL c d _ (datSmul K Δ τ c d m hD t) hne).1`. Establish `hg : gOrb O j χ a = 0`.

Assume the negation of the conclusion as `hne`. Conclude with `hτ (gVanish O K Δ τ hL j hj χ a (Or.inl ha) hne)`. Rewrite using `[hg]`. Unfold `stabSum`. Simplify using `only [h0, finsum_zero]`.

Take `⟨τ₀, hτ₀⟩` from `hτ`. Take `⟨z, hz⟩` from `exists_unit_one_add_generator hreg`. Break down `tri hL τ₀ with ⟨hm, hu⟩ | ⟨hm, hu⟩ | ⟨hu1, hu2⟩` into its components or cases. Establish `hx : (2 + τ₀) - 2 ^ 2 ∈ IsLocalRing.maximalIdeal O`. Establish `e : (2 + τ₀) - 2 ^ 2 = τ₀ - 2` using `by ring`.

Rewrite using `[e]`. Conclude with `hm`. Take `⟨r, hr2, hrm⟩` from `sqrtO O K Δ hL (2 + τ₀) 2 hL.two hx`. Establish `hrK : (algebraMap O K) r ^ 2 = 2 + τ`. Rewrite using `[← map_pow, hr2, map_add, map_ofNat, hτ₀]`.

Establish `hlam : QuadraticAlgebra.norm ((algebraMap K (Lsq K Δ)) ((algebraMap O K) r)) = 2 + τ`. Rewrite using `[QuadraticAlgebra.norm_algebraMap, hrK]`. Establish `hD0` using `datLam K Δ τ c hreg hc _ hlam z hz`. Take `⟨m', hm', hmove⟩` from `dat_move hL hD hD0.d_norm`. Take `⟨t₁, rfl⟩` from `datForm O K Δ τ hL c _ hlam z hz m' hm'`.

Establish `hP` using `caseP O K Δ τ hL hreg r hrm hrK c hev j χ hj hχ a ha z hz`. Set `f : Kˣ → ℂ` to `fun y => lcount O c (dLam ((algebraMap K (Lsq K Δ)) ((algebraMap O K) r)) z) ((y : K) • 1)`. Establish `hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x` using `fun t ht x => lcount_inv hL hD0 t ht x`. Establish `hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * t₁)`. Introduce `k`.

Rewrite using `[hmove, smul_smul]`. Both sides reduce to the same expression. Rewrite using `[hshift f hf t₁ hk]`. Establish `hc2 : -2 * c ≠ 0` using `mul_ne_zero (neg_ne_zero.mpr h2K) hc`. Conclude with `((sumShift O K Δ τ hL hreg f hf 1).2.2 _ _ hP ⟨Units.mk0 _ hc2, by rw [Units.val_mk0]⟩).1`.

Establish `hevc : EvenVal O c`. Apply `EvenVal.of_mul_unit hu` to reduce the goal to its premises. Rewrite using `[map_sub, map_ofNat, hτ₀]`. Conclude with `hev`. Establish `hm2 : τ₀ - 2 * (((-1 : ℤˣ) : ℤ) : O) ∈ IsLocalRing.maximalIdeal O`.

Establish `e : τ₀ - 2 * (((-1 : ℤˣ) : ℤ) : O) = τ₀ + 2` using `by push_cast; ring`. Rewrite using `[e]`. Conclude with `hm`. Take `⟨x, y, _, hsq, hn⟩` from `rootEx O K Δ τ hL τ₀ (-1) hτ₀ hm2`. Use `set u : Etau K τ := { re := (algebraMap O K) x, im := (algebraMap O K) y } with hu_def`.

Establish `hu2' : u ^ 2 = -ω`. Rewrite using `[hsq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨ν, hνI, hνN⟩` from `normEx O K Δ hL (-1)`.

Establish `hνN' : QuadraticAlgebra.norm ν = -1`. Rewrite using `[hνN]`. Simplify using the standard rewrite rules. Take `⟨ε, s, hs0, hΔ⟩` from `hL.even`. Establish `hΔ' : Δ * (s⁻¹) ^ 2 = (algebraMap O K) ↑ε`.

Rewrite using `[hΔ]`. Clear the denominators using the available nonvanishing facts. Take `⟨hdn, hform⟩` from `datFormM O K Δ τ hL c u hu2' hn ν hνN' s⁻¹ (inv_ne_zero hs0)`. Take `⟨m', hm'', hmove⟩` from `dat_move hL hD hdn`. Take `⟨t₁, rfl⟩` from `hform m' hm''`.

Establish `hM` using `caseM O K Δ τ hL hreg τ₀ hτ₀ hm c hevc u hu2' hn ν hνI hνN' s⁻¹ ε hΔ'`. Set `g : Kˣ` to `t₁ * Units.mk0 _ hreg`. Set `f : Kˣ → ℂ` to `fun y => pcount O τ (y : K)`. Establish `hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x`. Introduce `t ht x`.

Simplify using `only [f, Units.val_mul]`. Conclude with `pNorm O K Δ τ hL t ht x`. Establish `hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * g)`. Introduce `k`. Rewrite using `[hmove, ← smul_assoc, smul_smul, ← Units.val_mul, hM]`.

Simplify using `only [f, g, Units.val_mul, Units.val_mk0, mul_assoc]`. Rewrite using `[hshift f hf g hk]`. Conclude with `pStable O K Δ τ hL hreg j χ hj hχ a ha`. Establish `hevc : EvenVal O c`. Apply `EvenVal.of_mul_unit hu2` to reduce the goal to its premises.

Rewrite using `[map_sub, map_ofNat, hτ₀]`. Conclude with `hev`. Establish `hU : (algebraMap O K) ↑(-(hu1.unit * hu2.unit)) = τ ^ 2 - 4`. Rewrite using `[Units.val_neg, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, map_neg, map_mul, map_add, map_sub, map_ofNat, hτ₀]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨lam, hlamI, hlamN⟩` from `normEx O K Δ hL hu1.unit`. Establish `hlam : QuadraticAlgebra.norm lam = 2 + τ`. Rewrite using `[hlamN, IsUnit.unit_spec, map_add, map_ofNat, hτ₀]`. Establish `hD0` using `datLam K Δ τ c hreg hc lam hlam z hz`. Take `⟨m', hm', hmove⟩` from `dat_move hL hD hD0.d_norm`.

Take `⟨t₁, rfl⟩` from `datForm O K Δ τ hL c lam hlam z hz m' hm'`. Establish `hG` using `caseG O K Δ τ hL ⟨_, hU⟩ c hevc lam hlamI hlam z hz`. Establish `hga` using `(gVals O K Δ τ hL hreg ⟨τ₀, hτ₀⟩ j χ hj hχ a ha z hz).2.1 ⟨_, hU⟩`. Set `f : Kˣ → ℂ` to `fun y => lcount O c (dLam lam z) ((y : K) • 1)`. Establish `hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x` using `fun t ht x => lcount_inv hL hD0 t ht x`.

Establish `hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * t₁)`. Introduce `k`. Rewrite using `[hmove, smul_smul]`. Both sides reduce to the same expression. Rewrite using `[hshift f hf t₁ hk, hga]`.

Establish `h1 : hs (τ ^ 2 - 4) ((1 : Kˣ) : K) = 1`. Rewrite using `[Units.val_one]`. Unfold `hs`. Rewrite using `[if_pos ⟨1, 0, by ring⟩]`. Conclude with `((sumShift O K Δ τ hL hreg f hf 1).2.2 _ _ hG ⟨1, h1⟩).1`.
-/
theorem UpperTheory.V.Z.Sym.Loc.stable : UpperTheory.V.Z.Sym.Loc.Stable := by
  unfold Stable
  intro O K _ _ _ _ _ Δ τ hL c d m hD hev j hj χ hχ a ha
  have hreg := hD.reg
  have hc := hD.c_ne
  have h2K : (2 : K) ≠ 0 := by
    have h := hL.two.map (algebraMap O K)
    rw [map_ofNat] at h
    exact h.ne_zero
  have hshift : ∀ (f : Kˣ → ℂ), (∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x) → ∀ g : Kˣ,
      (∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * g)) → stabSum O c d m = ∑ᶠ t : Kˣ ⧸ NE τ, f (Quotient.out t) := by
    intro f hf g hk
    unfold stabSum
    rw [finsum_congr (fun t => hk _)]
    exact (sumShift O K Δ τ hL hreg f hf g).1
  by_cases hτ : τ ∈ (algebraMap O K).range
  swap
  · have h0 : ∀ t : Kˣ, lcount O c d ((t : K) • m) = 0 := by
      intro t
      by_contra hne
      exact hτ (vanish O K Δ τ hL c d _ (datSmul K Δ τ c d m hD t) hne).1
    have hg : gOrb O j χ a = 0 := by
      by_contra hne
      exact hτ (gVanish O K Δ τ hL j hj χ a (Or.inl ha) hne)
    rw [hg]
    unfold stabSum
    simp only [h0, finsum_zero]
  obtain ⟨τ₀, hτ₀⟩ := hτ
  obtain ⟨z, hz⟩ := exists_unit_one_add_generator hreg
  rcases tri hL τ₀ with ⟨hm, hu⟩ | ⟨hm, hu⟩ | ⟨hu1, hu2⟩
  · have hx : (2 + τ₀) - 2 ^ 2 ∈ IsLocalRing.maximalIdeal O := by
      have e : (2 + τ₀) - 2 ^ 2 = τ₀ - 2 := by ring
      rw [e]
      exact hm
    obtain ⟨r, hr2, hrm⟩ := sqrtO O K Δ hL (2 + τ₀) 2 hL.two hx
    have hrK : (algebraMap O K) r ^ 2 = 2 + τ := by
      rw [← map_pow, hr2, map_add, map_ofNat, hτ₀]
    have hlam : QuadraticAlgebra.norm ((algebraMap K (Lsq K Δ)) ((algebraMap O K) r)) = 2 + τ := by
      rw [QuadraticAlgebra.norm_algebraMap, hrK]
    have hD0 := datLam K Δ τ c hreg hc _ hlam z hz
    obtain ⟨m', hm', hmove⟩ := dat_move hL hD hD0.d_norm
    obtain ⟨t₁, rfl⟩ := datForm O K Δ τ hL c _ hlam z hz m' hm'
    have hP := caseP O K Δ τ hL hreg r hrm hrK c hev j χ hj hχ a ha z hz
    let f : Kˣ → ℂ := fun y => lcount O c (dLam ((algebraMap K (Lsq K Δ)) ((algebraMap O K) r)) z) ((y : K) • 1)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := fun t ht x => lcount_inv hL hD0 t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * t₁) := by
      intro k
      rw [hmove, smul_smul]
      rfl
    rw [hshift f hf t₁ hk]
    have hc2 : -2 * c ≠ 0 := mul_ne_zero (neg_ne_zero.mpr h2K) hc
    exact ((sumShift O K Δ τ hL hreg f hf 1).2.2 _ _ hP ⟨Units.mk0 _ hc2, by rw [Units.val_mk0]⟩).1
  · have hevc : EvenVal O c := by
      apply EvenVal.of_mul_unit hu
      rw [map_sub, map_ofNat, hτ₀]
      exact hev
    have hm2 : τ₀ - 2 * (((-1 : ℤˣ) : ℤ) : O) ∈ IsLocalRing.maximalIdeal O := by
      have e : τ₀ - 2 * (((-1 : ℤˣ) : ℤ) : O) = τ₀ + 2 := by push_cast; ring
      rw [e]
      exact hm
    obtain ⟨x, y, _, hsq, hn⟩ := rootEx O K Δ τ hL τ₀ (-1) hτ₀ hm2
    set u : Etau K τ := { re := (algebraMap O K) x, im := (algebraMap O K) y } with hu_def
    have hu2' : u ^ 2 = -ω := by
      rw [hsq]
      push_cast
      ring
    obtain ⟨ν, hνI, hνN⟩ := normEx O K Δ hL (-1)
    have hνN' : QuadraticAlgebra.norm ν = -1 := by
      rw [hνN]
      simp
    obtain ⟨ε, s, hs0, hΔ⟩ := hL.even
    have hΔ' : Δ * (s⁻¹) ^ 2 = (algebraMap O K) ↑ε := by
      rw [hΔ]
      field_simp
    obtain ⟨hdn, hform⟩ := datFormM O K Δ τ hL c u hu2' hn ν hνN' s⁻¹ (inv_ne_zero hs0)
    obtain ⟨m', hm'', hmove⟩ := dat_move hL hD hdn
    obtain ⟨t₁, rfl⟩ := hform m' hm''
    have hM := caseM O K Δ τ hL hreg τ₀ hτ₀ hm c hevc u hu2' hn ν hνI hνN' s⁻¹ ε hΔ'
    let g : Kˣ := t₁ * Units.mk0 _ hreg
    let f : Kˣ → ℂ := fun y => pcount O τ (y : K)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := by
      intro t ht x
      simp only [f, Units.val_mul]
      exact pNorm O K Δ τ hL t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * g) := by
      intro k
      rw [hmove, ← smul_assoc, smul_smul, ← Units.val_mul, hM]
      simp only [f, g, Units.val_mul, Units.val_mk0, mul_assoc]
    rw [hshift f hf g hk]
    exact pStable O K Δ τ hL hreg j χ hj hχ a ha
  · have hevc : EvenVal O c := by
      apply EvenVal.of_mul_unit hu2
      rw [map_sub, map_ofNat, hτ₀]
      exact hev
    have hU : (algebraMap O K) ↑(-(hu1.unit * hu2.unit)) = τ ^ 2 - 4 := by
      rw [Units.val_neg, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, map_neg, map_mul, map_add, map_sub,
        map_ofNat, hτ₀]
      ring
    obtain ⟨lam, hlamI, hlamN⟩ := normEx O K Δ hL hu1.unit
    have hlam : QuadraticAlgebra.norm lam = 2 + τ := by
      rw [hlamN, IsUnit.unit_spec, map_add, map_ofNat, hτ₀]
    have hD0 := datLam K Δ τ c hreg hc lam hlam z hz
    obtain ⟨m', hm', hmove⟩ := dat_move hL hD hD0.d_norm
    obtain ⟨t₁, rfl⟩ := datForm O K Δ τ hL c lam hlam z hz m' hm'
    have hG := caseG O K Δ τ hL ⟨_, hU⟩ c hevc lam hlamI hlam z hz
    have hga := (gVals O K Δ τ hL hreg ⟨τ₀, hτ₀⟩ j χ hj hχ a ha z hz).2.1 ⟨_, hU⟩
    let f : Kˣ → ℂ := fun y => lcount O c (dLam lam z) ((y : K) • 1)
    have hf : ∀ t ∈ NE τ, ∀ x : Kˣ, f (t * x) = f x := fun t ht x => lcount_inv hL hD0 t ht x
    have hk : ∀ k : Kˣ, lcount O c d ((k : K) • m) = f (k * t₁) := by
      intro k
      rw [hmove, smul_smul]
      rfl
    rw [hshift f hf t₁ hk, hga]
    have h1 : hs (τ ^ 2 - 4) ((1 : Kˣ) : K) = 1 := by
      rw [Units.val_one]
      unfold hs
      rw [if_pos ⟨1, 0, by ring⟩]
    exact ((sumShift O K Δ τ hL hreg f hf 1).2.2 _ _ hG ⟨1, h1⟩).1
