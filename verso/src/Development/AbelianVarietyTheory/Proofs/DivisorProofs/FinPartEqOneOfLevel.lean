import Mathlib
import Formalism.PairingDivisors.StatementA
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartEqOneOfFibres

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology

namespace GlobalTheory.CMVal.OrderUnits

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Use `set t : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) ^ n with ht`. Establish `hv : Valued.v (t : P.adicCompletion E) = WithZero.exp (-(n : ℤ))`. Establish `h2 : Valued.v ((Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) : (P.adicCompletion E)ˣ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ)` using `Formalism.L2.Host.unif_spec P`. Rewrite using `[ht, Units.val_pow_eq_pow_val, map_pow, h2, ← WithZero.exp_nsmul]`. Simplify using the standard rewrite rules.

Establish `hc : Continuous fun x : P.adicCompletion E => (x - z) / (t : P.adicCompletion E)` using `by fun_prop`. Establish `ho` using `(Valued.isOpen_valuationSubring (P.adicCompletion E)).preimage hc`. Use `mem_of_superset (ho.mem_nhds ?_) ?_` and prove the remaining obligations. Use `show (z - z) / (t : P.adicCompletion E) ∈ Valued.v.valuationSubring`. Rewrite using `[sub_self, zero_div]`.

Conclude with `zero_mem _`. Introduce `x hx`. Establish `hx' : Valued.v ((x - z) / (t : P.adicCompletion E)) ≤ 1` using `hx`. Rewrite `hx'` using `[map_div₀, hv, div_le_one₀ (WithZero.exp_pos)]`. Conclude with `hx'`.
-/
theorem ball_mem_nhds (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (z : P.adicCompletion E) :
    {x : P.adicCompletion E | Valued.v (x - z) ≤ WithZero.exp (-(n : ℤ))} ∈ 𝓝 z := by
  set t : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) ^ n with ht
  have hv : Valued.v (t : P.adicCompletion E) = WithZero.exp (-(n : ℤ)) := by
    have h2 : Valued.v ((Formalism.L2.Host.atFin P (Formalism.L2.Host.unif P) : (P.adicCompletion E)ˣ) : P.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec P
    rw [ht, Units.val_pow_eq_pow_val, map_pow, h2, ← WithZero.exp_nsmul]
    simp
  have hc : Continuous fun x : P.adicCompletion E => (x - z) / (t : P.adicCompletion E) := by fun_prop
  have ho := (Valued.isOpen_valuationSubring (P.adicCompletion E)).preimage hc
  refine mem_of_superset (ho.mem_nhds ?_) ?_
  · show (z - z) / (t : P.adicCompletion E) ∈ Valued.v.valuationSubring
    rw [sub_self, zero_div]; exact zero_mem _
  · intro x hx
    have hx' : Valued.v ((x - z) / (t : P.adicCompletion E)) ≤ 1 := hx
    rw [map_div₀, hv, div_le_one₀ (WithZero.exp_pos)] at hx'
    exact hx'

/- English proof (translation)
Rewrite using `[FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(P.intValuation_le_pow_iff_mem b n).2 hb`.
-/
theorem val_int_le (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (b : 𝓞 E) (hb : b ∈ P.asIdeal ^ n) :
    Valued.v (algebraMap E (Af E) (algebraMap (𝓞 E) E b) P) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]
  exact (P.intValuation_le_pow_iff_mem b n).2 hb

/- English proof (translation)
Establish `hev : ∀ P : HeightOneSpectrum (𝓞 E), Continuous fun z : Af E => z P` using `fun P => RestrictedProduct.continuous_eval P`. Establish `hU : ∀ᶠ x : Af E in 𝓝 z, ∀ P ∈ S, Valued.v (x P - z P) ≤ WithZero.exp (-(n : ℤ))`. Rewrite using `[Filter.eventually_all_finset]`. Introduce `P _`. Conclude with `(hev P).tendsto z (ball_mem_nhds P n (z P))`.

Establish `hz1 : z ∈ closure (((orderC c).map (algebraMap E (Af E)) : Subring (Af E)) : Set (Af E))` using `hz`. Take `⟨x, ⟨k, hk, rfl⟩, hx⟩` from `((mem_closure_iff_frequently.1 hz1).and_eventually hU).exists`. Take `⟨a, b, hb, rfl⟩` from `mem_orderC.1 hk`. Use `⟨a, fun P hP => ?_⟩` and prove the remaining obligations. Establish `hb' : b ∈ P.asIdeal ^ n`.

Establish `h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal ^ n`. Use `(Ideal.map_mono (Ideal.le_of_dvd hn)).trans ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_pow]`. Use `Ideal.pow_right_mono ?_ n` and prove the remaining obligations. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Conclude with `(hS P hP).ge`. Conclude with `h1 hb`. Establish `h2` using `val_int_le P n b hb'`. Establish `h3` using `hx P hP`. Rewrite `h3` using `[map_add]`.

Establish `h4 : algebraMap E (Af E) (algebraMap (OF E) E a) P - z P = ((algebraMap E (Af E) (algebraMap (OF E) E a) + algebraMap E (Af E) (algebraMap (𝓞 E) E b)) P - z P) - algebraMap E (Af E) (algebraMap (𝓞 E) E b) P`. Express the relevant statement in the definitionally equal form `_ = (algebraMap E (Af E) (algebraMap (OF E) E a) P + algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z P) - _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h4]`. Conclude with `Valuation.map_sub_le _ h3 h2`.
-/
theorem exists_cong {c : Ideal (OF E)} (v : HeightOneSpectrum (OF E)) (n : ℕ) (hn : v.asIdeal ^ n ∣ c)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hS : ∀ P ∈ S, Over P v) {z : Af E} (hz : z ∈ hatO c) :
    ∃ a : OF E, ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P) ≤ WithZero.exp (-(n : ℤ)) := by
  have hev : ∀ P : HeightOneSpectrum (𝓞 E), Continuous fun z : Af E => z P := fun P =>
    RestrictedProduct.continuous_eval P
  have hU : ∀ᶠ x : Af E in 𝓝 z, ∀ P ∈ S, Valued.v (x P - z P) ≤ WithZero.exp (-(n : ℤ)) := by
    rw [Filter.eventually_all_finset]
    intro P _
    exact (hev P).tendsto z (ball_mem_nhds P n (z P))
  have hz1 : z ∈ closure (((orderC c).map (algebraMap E (Af E)) : Subring (Af E)) : Set (Af E)) := hz
  obtain ⟨x, ⟨k, hk, rfl⟩, hx⟩ := ((mem_closure_iff_frequently.1 hz1).and_eventually hU).exists
  obtain ⟨a, b, hb, rfl⟩ := mem_orderC.1 hk
  refine ⟨a, fun P hP => ?_⟩
  have hb' : b ∈ P.asIdeal ^ n := by
    have h1 : Ideal.map (algebraMap (OF E) (𝓞 E)) c ≤ P.asIdeal ^ n := by
      refine (Ideal.map_mono (Ideal.le_of_dvd hn)).trans ?_
      rw [Ideal.map_pow]
      refine Ideal.pow_right_mono ?_ n
      rw [Ideal.map_le_iff_le_comap]
      exact (hS P hP).ge
    exact h1 hb
  have h2 := val_int_le P n b hb'
  have h3 := hx P hP
  rw [map_add] at h3
  have h4 : algebraMap E (Af E) (algebraMap (OF E) E a) P - z P =
      ((algebraMap E (Af E) (algebraMap (OF E) E a) + algebraMap E (Af E) (algebraMap (𝓞 E) E b)) P - z P) -
        algebraMap E (Af E) (algebraMap (𝓞 E) E b) P := by
    change _ = (algebraMap E (Af E) (algebraMap (OF E) E a) P + algebraMap E (Af E) (algebraMap (𝓞 E) E b) P - z P) - _
    ring
  rw [h4]
  exact Valuation.map_sub_le _ h3 h2

/- English proof (translation)
Take `⟨a, ha⟩` from `exists_cong (P.under (OF E)) 0 (by simp) {P} (fun P' hP' => by`. Rewrite using `[Finset.mem_singleton.1 hP']`. Use the proof step `rfl) hz`. Establish `h1` using `ha P (Finset.mem_singleton_self P)`. Establish `h2` using `val_int_le P 0 (algebraMap (OF E) (𝓞 E) a) (by simp)`.

Establish `h3 : z P = algebraMap E (Af E) (algebraMap (OF E) E a) P - (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Conclude with `(Valuation.map_sub_le _ h2 h1).trans_eq (by simp)`.
-/
theorem val_le_one {c : Ideal (OF E)} {z : Af E} (hz : z ∈ hatO c) (P : HeightOneSpectrum (𝓞 E)) : Valued.v (z P) ≤ 1 := by
  obtain ⟨a, ha⟩ := exists_cong (P.under (OF E)) 0 (by simp) {P} (fun P' hP' => by
    rw [Finset.mem_singleton.1 hP']; rfl) hz
  have h1 := ha P (Finset.mem_singleton_self P)
  have h2 := val_int_le P 0 (algebraMap (OF E) (𝓞 E) a) (by simp)
  have h3 : z P = algebraMap E (Af E) (algebraMap (OF E) E a) P - (algebraMap E (Af E) (algebraMap (OF E) E a) P - z P) := by
    ring
  rw [h3]
  exact (Valuation.map_sub_le _ h2 h1).trans_eq (by simp)

/- English proof (translation)
Establish `h1` using `val_le_one (mem_hatOUnits.1 hy).1 P`. Establish `h2` using `val_le_one (mem_hatOUnits.1 hy).2 P`. Establish `h3 : Valued.v ((y : Af E) P) * Valued.v ((↑y⁻¹ : Af E) P) = 1`. Rewrite using `[← map_mul]`. Conclude with `(congrArg Valued.v (coord P y).val_inv).trans (map_one _)`.

Conclude with `le_antisymm h1 (by`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem val_eq_one {c : Ideal (OF E)} {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v ((y : Af E) P) = 1 := by
  have h1 := val_le_one (mem_hatOUnits.1 hy).1 P
  have h2 := val_le_one (mem_hatOUnits.1 hy).2 P
  have h3 : Valued.v ((y : Af E) P) * Valued.v ((↑y⁻¹ : Af E) P) = 1 := by
    rw [← map_mul]
    exact (congrArg Valued.v (coord P y).val_inv).trans (map_one _)
  exact le_antisymm h1 (by
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ Valued.v ((y : Af E) P) * 1 := by gcongr
      _ = _ := mul_one _)

/- English proof (translation)
Use `Fibre.finPart_eq_one_of_fibres E χ y fun v => ?_` and prove the remaining obligations. Use `set S := Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v with hS`. Establish `hO : ∀ P ∈ S, Over P v` using `fun P hP => by`. Rewrite `hP` using `[hS]`. Unfold `Formalism.L2.Host.aboveF at hP`.

Rewrite `hP` using `[Set.Finite.mem_toFinset]`. Establish `: P.under (OF E) = v` using `hP`. Rewrite using `[← this]`. Both sides reduce to the same expression. Take `⟨n, hn, hlev⟩` from `hl v`.

Break down `Nat.eq_zero_or_pos n with rfl | hpos` into its components or cases. Conclude with `Finset.prod_eq_one fun P hP => (χ.unrAt_iff P).2 (hlev P (hO P hP)) _ (val_eq_one hy P)`. Take `⟨a, ha⟩` from `exists_cong v n hn S hO (mem_hatOUnits.1 hy).1`. Establish `hva : ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P) = 1` using `fun P hP => by`. Establish `hlt : Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - (y : Af E) P) < Valued.v ((y : Af E) P)`.

Rewrite using `[val_eq_one hy P]`. Use `(ha P hP).trans_lt ?_` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Valuation.map_eq_of_sub_lt _ hlt, val_eq_one hy P]`.

Distinguish the cases in `h0 : algebraMap (OF E) E a = 0`. Use `Finset.prod_eq_one fun P hP => ?_` and prove the remaining obligations. Establish `h1` using `hva P hP`. Rewrite `h1` using `[h0, map_zero]`. Conclude with `absurd (h1.symm.trans (map_zero _)) one_ne_zero`.

Set `k' : (maximalRealSubfield E)ˣ` to `Units.mk0 (a : maximalRealSubfield E) (fun h1 => h0 (congrArg Subtype.val h1))`. Establish `h2` using `hF.1 v k'`. Unfold `Formalism.L2.Host.HChar.resFin at h2`. Rewrite `h2` using `[MonoidHom.finsetProd_apply]`. Rewrite using `[← h2]`.

Use `Finset.prod_congr rfl fun P hP => ?_` and prove the remaining obligations. Use `set u : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) k') with hu`. Establish `hu' : (u : P.adicCompletion E) = algebraMap E (Af E) (algebraMap (OF E) E a) P` using `rfl`. Establish `hvu : Valued.v (u : P.adicCompletion E) = 1` using `hva P hP`. Use `show χ.loc P (coord P y) = χ.loc P u`.

Establish `h3 : χ.loc P (u / coord P y) = 1`. Use `hlev P (hO P hP) _ ?_ ?_` and prove the remaining obligations. Use `show Valued.v ((u / coord P y : (P.adicCompletion E)ˣ) : P.adicCompletion E) = 1`. Rewrite using `[Units.val_div_eq_div_val, map_div₀, hvu, coe_coord, val_eq_one hy P, div_one]`. Rewrite using `[Units.val_div_eq_div_val, div_sub_one (coord P y).ne_zero, map_div₀, coe_coord, val_eq_one hy P, div_one, hu']`.

Conclude with `ha P hP`. Rewrite `h3` using `[map_div, div_eq_one]`. Conclude with `h3.symm`.
-/
theorem finPart_eq_one_of_level {c : Ideal (OF E)} {χ : HChar E} (hF : TrivOnF χ)
    (hl : ∀ v : HeightOneSpectrum (OF E), ∃ n : ℕ, v.asIdeal ^ n ∣ c ∧ ∀ P, Over P v → LevelLe χ P n)
    {y : (Af E)ˣ} (hy : y ∈ hatOUnits c) : finPart χ y = 1 := by
  refine Fibre.finPart_eq_one_of_fibres E χ y fun v => ?_
  set S := Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v with hS
  have hO : ∀ P ∈ S, Over P v := fun P hP => by
    rw [hS] at hP
    unfold Formalism.L2.Host.aboveF at hP
    rw [Set.Finite.mem_toFinset] at hP
    have : P.under (OF E) = v := hP
    rw [← this]; rfl
  obtain ⟨n, hn, hlev⟩ := hl v
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Finset.prod_eq_one fun P hP => (χ.unrAt_iff P).2 (hlev P (hO P hP)) _ (val_eq_one hy P)
  obtain ⟨a, ha⟩ := exists_cong v n hn S hO (mem_hatOUnits.1 hy).1
  have hva : ∀ P ∈ S, Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P) = 1 := fun P hP => by
    have hlt : Valued.v (algebraMap E (Af E) (algebraMap (OF E) E a) P - (y : Af E) P) < Valued.v ((y : Af E) P) := by
      rw [val_eq_one hy P]
      refine (ha P hP).trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    rw [Valuation.map_eq_of_sub_lt _ hlt, val_eq_one hy P]
  by_cases h0 : algebraMap (OF E) E a = 0
  · refine Finset.prod_eq_one fun P hP => ?_
    have h1 := hva P hP
    rw [h0, map_zero] at h1
    exact absurd (h1.symm.trans (map_zero _)) one_ne_zero
  let k' : (maximalRealSubfield E)ˣ := Units.mk0 (a : maximalRealSubfield E)
    (fun h1 => h0 (congrArg Subtype.val h1))
  have h2 := hF.1 v k'
  unfold Formalism.L2.Host.HChar.resFin at h2
  rw [MonoidHom.finsetProd_apply] at h2
  rw [← h2]
  refine Finset.prod_congr rfl fun P hP => ?_
  set u : (P.adicCompletion E)ˣ := Formalism.L2.Host.atFin P (Formalism.L2.Host.upF (maximalRealSubfield E) k') with hu
  have hu' : (u : P.adicCompletion E) = algebraMap E (Af E) (algebraMap (OF E) E a) P := rfl
  have hvu : Valued.v (u : P.adicCompletion E) = 1 := hva P hP
  show χ.loc P (coord P y) = χ.loc P u
  have h3 : χ.loc P (u / coord P y) = 1 := by
    refine hlev P (hO P hP) _ ?_ ?_
    · show Valued.v ((u / coord P y : (P.adicCompletion E)ˣ) : P.adicCompletion E) = 1
      rw [Units.val_div_eq_div_val, map_div₀, hvu, coe_coord, val_eq_one hy P, div_one]
    · rw [Units.val_div_eq_div_val, div_sub_one (coord P y).ne_zero, map_div₀, coe_coord, val_eq_one hy P, div_one, hu']
      exact ha P hP
  rw [map_div, div_eq_one] at h3
  exact h3.symm

/- English proof (translation)
Introduce `E _ _ _ I _ φ _ s κ 𝔣 Q χ _ _ _ hχ y hy`. Use `finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hy` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ Q`. Use `⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩` and prove the remaining obligations. Rewrite using `[pow_one]`.

Conclude with `Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _`. Conclude with `⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _, fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩`.
-/
theorem finPart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E),
    UnramFin E → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 Q χ →
      ∀ y ∈ hatOUnits (condQ 𝔣 Q), finPart χ y = 1 := by
  intro E _ _ _ I _ φ _ s κ 𝔣 Q χ _ _ _ hχ y hy
  refine finPart_eq_one_of_level hχ.2.1 (fun v => ?_) hy
  by_cases hv : v ∈ Q
  · refine ⟨1, ?_, fun P hP => (hχ.2.2.2 v P hP).1 hv⟩
    rw [pow_one]
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem (fun q : HeightOneSpectrum (OF E) => q.asIdeal) hv) _
  · exact ⟨expIn 𝔣 v, Dvd.dvd.mul_right (pow_multiplicity_dvd _ _) _,
      fun P hP => ((hχ.2.2.2 v P hP).2 hv _).2 le_rfl⟩

end GlobalTheory.CMVal.OrderUnits
