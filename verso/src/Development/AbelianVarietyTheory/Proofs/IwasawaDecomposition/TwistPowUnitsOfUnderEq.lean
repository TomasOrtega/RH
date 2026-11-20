import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatCongrOfAbsNormPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmEmbeddingProperties

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

namespace GlobalTheory.Mem.Chr

/- English proof (translation)
Introduce `R H S ξ hξ Q Q' hu n hn x hx`. Distinguish the cases in `hQ : Q = Q'`. Substitute `hQ` using the available equality. Conclude with `hn x hx`. Distinguish the cases in `hur : ξ.UnrAt Q`.

Rewrite using `[hur x hx, one_pow]`. Take `⟨-, htriv, htame, hram⟩` from `hξ`. Take `⟨-, hq, -, -⟩` from `hram Q hur`. Take `⟨a, k, hcop, hk, hcong⟩` from `(GlobalTheory.localUnit_congr_global H.E Q x hx).2 _ hq rfl`. Take `⟨c, -, hcm, -⟩` from `GlobalTheory.Mem.HostCM.host_cm R H`.

Establish `hqQ : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q.asIdeal` using `Ideal.absNorm_mem Q.asIdeal`. Establish `hqQ' : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q'.asIdeal`. Establish `h1 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ (Q.under (𝓞 H.F)).asIdeal` using `by show algebraMap (𝓞 H.F) (𝓞 H.E) _ ∈ Q.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hqQ`.

Rewrite `h1` using `[hu]`. Establish `h2 : algebraMap (𝓞 H.F) (𝓞 H.E) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ Q'.asIdeal` using `h1`. Rewrite `h2` using `[map_natCast]`. Then use the resulting hypothesis. Establish `hkQ : IsUnitAt Q (atFin Q k)` using `isUnitAt_nat (H := H) hqQ hcop hk`. Establish `hkQ' : IsUnitAt Q' (atFin Q' k)` using `isUnitAt_nat (H := H) hqQ' hcop hk`.

Establish `hxk : IsUnitAt Q (x * (atFin Q k)⁻¹)`. Unfold `IsUnitAt at hx hkQ ⊢`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]`. Establish `h1 : ξ.loc Q (x * (atFin Q k)⁻¹) = 1` using `htame Q _ hxk (by simpa using hcong)`. Rewrite `h1` using `[map_mul, map_inv, mul_inv_eq_one]`.

Establish `ha0 : (a : H.F) ≠ 0`. Introduce `h`. Establish `h0 : a = 0` using `by exact_mod_cast h`. Apply `k.ne_zero` to reduce the goal to its premises. Rewrite using `[hk, h0, Nat.cast_zero]`.

Establish `hup : upF H.F (Units.mk0 (a : H.F) ha0) = k`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hk]`. Conclude with `map_natCast (algebraMap H.F H.E) a`. Establish `hab : aboveF (L` using `H.E) H.F (Q.under (𝓞 H.F)) = {Q, Q'} := by`.

Establish `hc' : ConjPl c.toRingEquiv Q Q'` using `((under_eq_iff_conjPl c hcm.rank hcm.ne Q Q').1 hu.symm).resolve_left (Ne.symm hQ)`. Use extensionality with `P`. Establish `hm : P ∈ aboveF (L` using `H.E) H.F (Q.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = Q.under (𝓞 H.F) := by`. Unfold `aboveF`. Rewrite using `[Set.Finite.mem_toFinset]`.

Both sides reduce to the same expression. Rewrite using `[hm, under_eq_iff_conjPl c hcm.rank hcm.ne Q P, Finset.mem_insert, Finset.mem_singleton]`. Use `or_congr Iff.rfl ⟨fun h => (existsUnique_conjPl _ Q).unique h hc', ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `hc'`.

Establish `h2` using `htriv.1 (Q.under (𝓞 H.F)) (Units.mk0 (a : H.F) ha0)`. Rewrite `h2` using `[HChar.resFin_apply, hab, Finset.prod_pair hQ, hup]`. Establish `h3 : ξ.loc Q (atFin Q k) * ξ.loc Q' (atFin Q' k) = 1` using `h2`. Establish `h4` using `congrArg (· ^ n) h3`. Simplify using `only [mul_pow, hn _ hkQ', mul_one, one_pow] at h4`.

Rewrite using `[h1, h4]`.
-/
theorem twist_pow_units_of_under_eq : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (S : Set ℕ) (ξ : HChar H.E), IsTwist H S ξ → ∀ (Q Q' : HeightOneSpectrum (𝓞 H.E)), Q.under (𝓞 H.F) = Q'.under (𝓞 H.F) → ∀ n : ℕ, (∀ x, IsUnitAt Q' x → ξ.loc Q' x ^ n = 1) → ∀ x, IsUnitAt Q x → ξ.loc Q x ^ n = 1 := by
  intro R H S ξ hξ Q Q' hu n hn x hx
  by_cases hQ : Q = Q'
  · subst hQ
    exact hn x hx
  by_cases hur : ξ.UnrAt Q
  · rw [hur x hx, one_pow]
  obtain ⟨-, htriv, htame, hram⟩ := hξ
  obtain ⟨-, hq, -, -⟩ := hram Q hur
  obtain ⟨a, k, hcop, hk, hcong⟩ := (GlobalTheory.localUnit_congr_global H.E Q x hx).2 _ hq rfl
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hqQ : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q.asIdeal := Ideal.absNorm_mem Q.asIdeal
  have hqQ' : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.E) ∈ Q'.asIdeal := by
    have h1 : ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ (Q.under (𝓞 H.F)).asIdeal := by
      show algebraMap (𝓞 H.F) (𝓞 H.E) _ ∈ Q.asIdeal
      rw [map_natCast]
      exact hqQ
    rw [hu] at h1
    have h2 : algebraMap (𝓞 H.F) (𝓞 H.E) ((Ideal.absNorm Q.asIdeal : ℕ) : 𝓞 H.F) ∈ Q'.asIdeal := h1
    rwa [map_natCast] at h2
  have hkQ : IsUnitAt Q (atFin Q k) := isUnitAt_nat (H := H) hqQ hcop hk
  have hkQ' : IsUnitAt Q' (atFin Q' k) := isUnitAt_nat (H := H) hqQ' hcop hk
  have hxk : IsUnitAt Q (x * (atFin Q k)⁻¹) := by
    unfold IsUnitAt at hx hkQ ⊢
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]
  have h1 : ξ.loc Q (x * (atFin Q k)⁻¹) = 1 := htame Q _ hxk (by simpa using hcong)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have ha0 : (a : H.F) ≠ 0 := by
    intro h
    have h0 : a = 0 := by exact_mod_cast h
    apply k.ne_zero
    rw [hk, h0, Nat.cast_zero]
  have hup : upF H.F (Units.mk0 (a : H.F) ha0) = k := by
    apply Units.ext
    rw [hk]
    exact map_natCast (algebraMap H.F H.E) a
  have hab : aboveF (L := H.E) H.F (Q.under (𝓞 H.F)) = {Q, Q'} := by
    have hc' : ConjPl c.toRingEquiv Q Q' :=
      ((under_eq_iff_conjPl c hcm.rank hcm.ne Q Q').1 hu.symm).resolve_left (Ne.symm hQ)
    ext P
    have hm : P ∈ aboveF (L := H.E) H.F (Q.under (𝓞 H.F)) ↔ P.under (𝓞 H.F) = Q.under (𝓞 H.F) := by
      unfold aboveF
      rw [Set.Finite.mem_toFinset]
      rfl
    rw [hm, under_eq_iff_conjPl c hcm.rank hcm.ne Q P, Finset.mem_insert, Finset.mem_singleton]
    refine or_congr Iff.rfl ⟨fun h => (existsUnique_conjPl _ Q).unique h hc', ?_⟩
    rintro rfl
    exact hc'
  have h2 := htriv.1 (Q.under (𝓞 H.F)) (Units.mk0 (a : H.F) ha0)
  rw [HChar.resFin_apply, hab, Finset.prod_pair hQ, hup] at h2
  have h3 : ξ.loc Q (atFin Q k) * ξ.loc Q' (atFin Q' k) = 1 := h2
  have h4 := congrArg (· ^ n) h3
  simp only [mul_pow, hn _ hkQ', mul_one, one_pow] at h4
  rw [h1, h4]

end GlobalTheory.Mem.Chr
