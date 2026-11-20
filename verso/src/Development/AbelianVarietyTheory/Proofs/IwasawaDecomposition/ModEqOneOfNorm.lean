import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem.LevelChoice

/- English proof (translation)
Take `⟨a, ha⟩` from `Ideal.mem_span_singleton'.1 hc`. Establish `hπ : (π : E) = 1 + (a : E) * (m : E)`. Establish `h` using `congrArg (fun x : 𝓞 E => (x : E)) ha`. Simplify using `only [map_mul, map_natCast, map_sub, map_one] at h`. Express the relevant statement in the definitionally equal form `(a : E) * (m : E) = (π : E) - 1 at h`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hai : IsIntegral ℤ (a : E)` using `a.2`. Establish `hci : IsIntegral ℤ (c (a : E))` using `hai.map c.toIntAlgHom`. Establish `hmi : IsIntegral ℤ ((m : ℕ) : E)`.

Simplify using `using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))`. Establish `hm0 : (m : E) ≠ 0` using `by exact_mod_cast (by omega : m ≠ 0)`. Establish `hm0' : (m : ℚ) ≠ 0` using `by exact_mod_cast (by omega : m ≠ 0)`. Establish `hx : algebraMap ℚ E (((p : ℚ) - 1) / m) = (a : E) + c a + (m : E) * ((a : E) * c a)`. Rewrite using `[map_div₀, map_sub, map_natCast, map_natCast, map_one, ← hn, hπ, map_add, map_one, map_mul, map_natCast]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hxi : IsIntegral ℤ (algebraMap ℚ E (((p : ℚ) - 1) / m))`. Rewrite using `[hx]`. Conclude with `(hai.add hci).add (hmi.mul (hai.mul hci))`.

Establish `hqi : IsIntegral ℤ (((p : ℚ) - 1) / m)` using `(isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 hxi`. Take `⟨k, hk⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hqi`. Establish `hk' : ((p : ℚ) - 1) = (k : ℚ) * m`. Establish `: (k : ℚ) = ((p : ℚ) - 1) / m` using `by simpa using hk`. Rewrite using `[this]`.

Clear the denominators using the available nonvanishing facts. Establish `hz : (p : ℤ) = 1 + (m : ℤ) * k`. Establish `: ((p : ℤ) : ℚ) = ((1 + (m : ℤ) * k : ℤ) : ℚ)` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions. Establish `h1 : ((p % m : ℕ) : ℤ) = 1`.

Rewrite using `[Int.natCast_mod, hz, Int.add_mul_emod_self_left]`. Conclude with `Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hm)`. Conclude with `h1` after adjusting the coercions.
-/
theorem mod_eq_one_of_norm {E : Type} [Field E] [NumberField E] (c : E →+* E) (π : 𝓞 E) (p m : ℕ) (hm : 1 < m)
    (hn : (π : E) * c (π : E) = (p : E)) (hc : π - 1 ∈ Ideal.span {((m : ℕ) : 𝓞 E)}) : p % m = 1 := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 hc
  have hπ : (π : E) = 1 + (a : E) * (m : E) := by
    have h := congrArg (fun x : 𝓞 E => (x : E)) ha
    simp only [map_mul, map_natCast, map_sub, map_one] at h
    change (a : E) * (m : E) = (π : E) - 1 at h
    rw [h]; ring
  have hai : IsIntegral ℤ (a : E) := a.2
  have hci : IsIntegral ℤ (c (a : E)) := hai.map c.toIntAlgHom
  have hmi : IsIntegral ℤ ((m : ℕ) : E) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  have hm0 : (m : E) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hx : algebraMap ℚ E (((p : ℚ) - 1) / m) = (a : E) + c a + (m : E) * ((a : E) * c a) := by
    rw [map_div₀, map_sub, map_natCast, map_natCast, map_one, ← hn, hπ, map_add, map_one, map_mul, map_natCast]
    field_simp
    ring
  have hxi : IsIntegral ℤ (algebraMap ℚ E (((p : ℚ) - 1) / m)) := by
    rw [hx]
    exact (hai.add hci).add (hmi.mul (hai.mul hci))
  have hqi : IsIntegral ℤ (((p : ℚ) - 1) / m) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ E).injective).1 hxi
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hqi
  have hk' : ((p : ℚ) - 1) = (k : ℚ) * m := by
    have : (k : ℚ) = ((p : ℚ) - 1) / m := by simpa using hk
    rw [this]; field_simp
  have hz : (p : ℤ) = 1 + (m : ℤ) * k := by
    have : ((p : ℤ) : ℚ) = ((1 + (m : ℤ) * k : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  have h1 : ((p % m : ℕ) : ℤ) = 1 := by
    rw [Int.natCast_mod, hz, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by norm_num) (by exact_mod_cast hm)
  exact_mod_cast h1

/- English proof (translation)
Introduce `P du Ds Ga hdu hDs hGa h`. Use `choose π p hp h1 h2 hK hN hc hlo hhi using h`. Establish `hq8 : P.H.q % 8 = 3` using `P.H.hyp.2.2.1`. Establish `hd16 : P.H.d % 16 = 7` using `P.H.hyp.2.2.2.1`. Establish `hn : 0 < P.H.QS` using `P.H.QS_pos`.

Establish `hm : 1 < P.H.QS * P.H.q * P.H.d`. Establish `hq : 0 < P.H.q` using `by omega`. Establish `hd : 0 < P.H.d` using `by omega`. Establish `h1 : P.H.q ≤ P.H.QS * P.H.q` using `Nat.le_mul_of_pos_left _ hn`. Establish `h2 : P.H.QS * P.H.q ≤ P.H.QS * P.H.q * P.H.d` using `Nat.le_mul_of_pos_right _ hd`.

Use linear arithmetic over natural numbers and integers. Establish `hcond : ∀ u, p u % (P.H.QS * P.H.q * P.H.d) = 1` using `fun u => by`. Use `mod_eq_one_of_norm (P.H.conj : P.H.E →+* P.H.E) (π u) (p u) _ hm (hN u) ?_` and prove the remaining obligations. Use `Ideal.span_singleton_le_span_singleton.2 ?_ (hc u)` and prove the remaining obligations. Conclude with `Nat.cast_dvd_cast (Dvd.intro _ rfl)`.

Conclude with `⟨{ T := p, T_prime := hp, T_cond := hcond, piT := π, piT_K := hK, piT_norm := hN, piT_cong := hc, T_ne_pde := fun u => ⟨h1 u, h2 u⟩, duStar := du, duStar_pos := hdu, Dstar := Ds, Dstar_pos := hDs, GamP := Ga, one_lt_gammaP := hGa, T_win := fun u => ⟨hlo u, hhi u⟩ }, rfl, rfl, rfl …`.
-/
theorem exists_levCh : ∀ (P : PreCh) (du : P.Word → ℕ) (Ds Ga : ℝ), (∀ u, 0 < du u) → 0 < Ds → 1 < Ga → (∀ u, ∃ (π : 𝓞 P.H.E) (p : ℕ), p.Prime ∧ p ≠ P.H.pde ∧ p ≠ P.H.pde' ∧ (π : P.H.E) ∈ P.H.K ∧ (π : P.H.E) * P.H.conj (π : P.H.E) = (p : P.H.E) ∧ π - 1 ∈ Ideal.span {((P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 : ℕ) : 𝓞 P.H.E)} ∧ (Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * Ga ^ (-(2 : ℝ) / (P.R.f * P.R.k)) ≤ (p : ℝ) ∧ (p : ℝ) ≤ (1 + 1 / ((P.R.f : ℝ) * P.R.k)) * ((Ds / du u) ^ ((1 : ℝ) / (P.R.f * P.R.k)) * Ga ^ (-(2 : ℝ) / (P.R.f * P.R.k)))) → ∃ L : LevCh P, L.duStar = du ∧ L.Dstar = Ds ∧ L.GamP = Ga := by
  intro P du Ds Ga hdu hDs hGa h
  choose π p hp h1 h2 hK hN hc hlo hhi using h
  have hq8 : P.H.q % 8 = 3 := P.H.hyp.2.2.1
  have hd16 : P.H.d % 16 = 7 := P.H.hyp.2.2.2.1
  have hn : 0 < P.H.QS := P.H.QS_pos
  have hm : 1 < P.H.QS * P.H.q * P.H.d := by
    have hq : 0 < P.H.q := by omega
    have hd : 0 < P.H.d := by omega
    have h1 : P.H.q ≤ P.H.QS * P.H.q := Nat.le_mul_of_pos_left _ hn
    have h2 : P.H.QS * P.H.q ≤ P.H.QS * P.H.q * P.H.d := Nat.le_mul_of_pos_right _ hd
    omega
  have hcond : ∀ u, p u % (P.H.QS * P.H.q * P.H.d) = 1 := fun u => by
    refine mod_eq_one_of_norm (P.H.conj : P.H.E →+* P.H.E) (π u) (p u) _ hm (hN u) ?_
    refine Ideal.span_singleton_le_span_singleton.2 ?_ (hc u)
    exact Nat.cast_dvd_cast (Dvd.intro _ rfl)
  exact ⟨{ T := p, T_prime := hp, T_cond := hcond, piT := π, piT_K := hK, piT_norm := hN, piT_cong := hc,
           T_ne_pde := fun u => ⟨h1 u, h2 u⟩, duStar := du, duStar_pos := hdu, Dstar := Ds, Dstar_pos := hDs,
           GamP := Ga, one_lt_gammaP := hGa, T_win := fun u => ⟨hlo u, hhi u⟩ }, rfl, rfl, rfl⟩

end GlobalTheory.Mem.LevelChoice
