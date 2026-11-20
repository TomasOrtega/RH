import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CmDatumCharTwoAdicOrderBounds
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.OrdProjNDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Introduce `h l _ c e hl2 he ψ hψ hR`. Establish `hl : l.Prime` using `Fact.out`. Take `⟨hchar, hpar⟩` from `(Host.mem_X h).mp hψ`. Take `⟨-, -, h16, ho, -⟩` from `hostIndex h`. Establish `hq : 0 < h.q` using `Nat.pos_of_neZero h.q`.

Take `⟨-, -, -, -, -, hcond, -, -, -, -, hord⟩` from `hostTh1 h _ ψ hchar l hl hl2`. Take `⟨-, -, -, -, hc⟩` from `cmDatum_char_two_adic_order_bounds h _ ψ hchar l hl hl2`. Take `⟨h12, hTb⟩` from `hc hR`. Use `⟨⟨hl2, he, ?_, hpar, ho, ?_, hTb, by omega⟩, hq, hcond, ?_⟩` and prove the remaining obligations. Conclude with `even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 16).trans h16)`.

Introduce `r hr hr2`. Conclude with `orderOf_dvd_iff_pow_eq_one.mp (hord r hr hr2)`. Establish `hl3 : 3 ≤ l`. Use `hl.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hlq : 0 < l * h.q` using `Nat.mul_pos (by omega) hq`. Establish `hR1 : h.R1 l ψ = 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ` using `rfl`. Establish `hX : l * h.q ≤ (l * h.q) ^ 2` using `Nat.le_self_pow two_ne_zero _`. Establish `hoX : 1 * (l * h.q) ^ 2 ≤ h.o * (l * h.q) ^ 2` using `Nat.mul_le_mul_right _ ho`. Establish `hmain : 2 * (l * h.q) ≤ 16 * h.o * (l * h.q) ^ 2` using `by nlinarith`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.V.UnitaryThreeInertia.hostData_of_host :
    ∀ (h : Host) {l : ℕ} [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 1 ≤ e → ∀ ψ ∈ h.X c e, h.R1 l ψ ≤ 2 ^ c2 ψ → HostData l e ψ h.o ∧ XData l ψ h.q := by
  intro h l _ c e hl2 he ψ hψ hR
  have hl : l.Prime := Fact.out
  obtain ⟨hchar, hpar⟩ := (Host.mem_X h).mp hψ
  obtain ⟨-, -, h16, ho, -⟩ := hostIndex h
  have hq : 0 < h.q := Nat.pos_of_neZero h.q
  obtain ⟨-, -, -, -, -, hcond, -, -, -, -, hord⟩ := hostTh1 h _ ψ hchar l hl hl2
  obtain ⟨-, -, -, -, hc⟩ := cmDatum_char_two_adic_order_bounds h _ ψ hchar l hl hl2
  obtain ⟨h12, hTb⟩ := hc hR
  refine ⟨⟨hl2, he, ?_, hpar, ho, ?_, hTb, by omega⟩, hq, hcond, ?_⟩
  · exact even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 16).trans h16)
  · intro r hr hr2
    exact orderOf_dvd_iff_pow_eq_one.mp (hord r hr hr2)
  · have hl3 : 3 ≤ l := by
      have := hl.two_le
      omega
    have hlq : 0 < l * h.q := Nat.mul_pos (by omega) hq
    have hR1 : h.R1 l ψ = 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ := rfl
    have hX : l * h.q ≤ (l * h.q) ^ 2 := Nat.le_self_pow two_ne_zero _
    have hoX : 1 * (l * h.q) ^ 2 ≤ h.o * (l * h.q) ^ 2 := Nat.mul_le_mul_right _ ho
    have hmain : 2 * (l * h.q) ≤ 16 * h.o * (l * h.q) ^ 2 := by nlinarith
    calc 2 * (l * h.q) * 4 ^ n0 l ψ ≤ 16 * h.o * (l * h.q) ^ 2 * 4 ^ n0 l ψ := Nat.mul_le_mul_right _ hmain
      _ = h.R1 l ψ := hR1.symm
      _ ≤ 2 ^ c2 ψ := hR
