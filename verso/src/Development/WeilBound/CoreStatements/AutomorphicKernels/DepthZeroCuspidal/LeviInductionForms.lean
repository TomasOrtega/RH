import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Formalism.SharpRestriction.LevelLetterCocycles.WildPro

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

/- English proof (translation)
Establish `hN : p ^ k ≠ 0` using `pow_ne_zero _ hp.ne_zero`. Establish `h1 : v (x ^ p ^ k) = 1`. Use `Valuation.map_one_add_of_lt v hx` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`. Then use the resulting hypothesis. Establish `hx1 : v x ≤ 1`.

Use `le_of_not_gt fun hc => ?_` and prove the remaining obligations. Establish `: 1 < v x ^ p ^ k` using `one_lt_pow₀ hc hN`. Rewrite `this` using `[← map_pow, h1]`. Conclude with `lt_irrefl _ this`. Establish `hy : v (x - 1) ≤ 1` using `(Valuation.map_sub v x 1).trans (max_le hx1 (by rw [map_one]))`.

Take `⟨r, hr⟩` from `exists_add_pow_prime_pow_eq hp (⟨x - 1, hy⟩ : v.integer) (1 : v.integer) k`. Establish `hr' : x ^ p ^ k = (x - 1) ^ p ^ k + 1 + (p : K) * (x - 1) * (r : K)`. Use `congrArg (fun z : v.integer => (z : K)) hr` as an intermediate fact. Simplify using `only [Subring.coe_add, Subring.coe_pow, Subring.coe_mul, Subring.coe_natCast, OneMemClass.coe_one, one_pow, mul_one, sub_add_cancel] at this`. Conclude with `this`.

Establish `hr1 : v (r : K) ≤ 1` using `r.2`. Establish `e : (x - 1) ^ p ^ k = (x ^ p ^ k - 1) + -((p : K) * (x - 1) * (r : K))`. Rewrite using `[hr']`. Expand and normalize the polynomial expressions, which then agree. Establish `hlt : v ((x - 1) ^ p ^ k) < 1`.

Rewrite using `[e]`. Use `Valuation.map_add_lt v hx ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_neg, map_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `lt_of_not_ge fun hc => ?_` and prove the remaining obligations.

Establish `: 1 ≤ v (x - 1) ^ p ^ k` using `one_le_pow₀ hc`. Rewrite `this` using `[← map_pow]`. Conclude with `absurd hlt (not_lt.2 this)`.
-/
theorem val_sub_one_lt_of_pow {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {p : ℕ} (hp : p.Prime) (hpv : v (p : K) < 1) {x : K} {k : ℕ} (hx : v (x ^ p ^ k - 1) < 1) :
    v (x - 1) < 1 := by
  have hN : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 : v (x ^ p ^ k) = 1 := by
    have := Valuation.map_one_add_of_lt v hx
    rwa [add_sub_cancel] at this
  have hx1 : v x ≤ 1 := by
    refine le_of_not_gt fun hc => ?_
    have : 1 < v x ^ p ^ k := one_lt_pow₀ hc hN
    rw [← map_pow, h1] at this
    exact lt_irrefl _ this
  have hy : v (x - 1) ≤ 1 :=
    (Valuation.map_sub v x 1).trans (max_le hx1 (by rw [map_one]))
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨x - 1, hy⟩ : v.integer) (1 : v.integer) k
  have hr' : x ^ p ^ k = (x - 1) ^ p ^ k + 1 + (p : K) * (x - 1) * (r : K) := by
    have := congrArg (fun z : v.integer => (z : K)) hr
    simp only [Subring.coe_add, Subring.coe_pow, Subring.coe_mul, Subring.coe_natCast, OneMemClass.coe_one,
      one_pow, mul_one, sub_add_cancel] at this
    exact this
  have hr1 : v (r : K) ≤ 1 := r.2
  have e : (x - 1) ^ p ^ k = (x ^ p ^ k - 1) + -((p : K) * (x - 1) * (r : K)) := by
    rw [hr']; ring
  have hlt : v ((x - 1) ^ p ^ k) < 1 := by
    rw [e]
    refine Valuation.map_add_lt v hx ?_
    rw [Valuation.map_neg, map_mul, map_mul]
    calc v (p : K) * v (x - 1) * v (r : K) ≤ v (p : K) * 1 * 1 := by gcongr
      _ < 1 := by rw [mul_one, mul_one]; exact hpv
  refine lt_of_not_ge fun hc => ?_
  have : 1 ≤ v (x - 1) ^ p ^ k := one_le_pow₀ hc
  rw [← map_pow] at this
  exact absurd hlt (not_lt.2 this)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

omit [IsAlgClosure E Ω] in

/- English proof (translation)
Introduce `y hy`. Establish `hv : A.valuation y ≠ 0` using `by simpa using hy`. Establish `e : σ y / y - 1 = (σ y - y) / y` using `by field_simp`. Rewrite using `[e, map_div₀]`. Conclude with `(div_lt_one₀ (zero_lt_iff.2 hv)).2 (hσ.2 y hy)`.
-/
theorem wildPf_of_isWild {σ : G E Ω} (hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A σ) : Formalism.MainNotions.N.KillingConditions.WildPf.IsWild A σ := by
  intro y hy
  have hv : A.valuation y ≠ 0 := by simpa using hy
  have e : σ y / y - 1 = (σ y - y) / y := by field_simp
  rw [e, map_div₀]
  exact (div_lt_one₀ (zero_lt_iff.2 hv)).2 (hσ.2 y hy)

/- English proof (translation)
Take `⟨p, hp, hpw⟩ : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 E) ∈ w.asIdeal` from `⟨_, GlobalTheory.LocalData.resChar_prime w, GlobalTheory.LocalData.resChar_mem w⟩`. Establish `hpA : A.valuation ((p : ℕ) : Ω) < 1`. Use `(h ((p : ℕ) : 𝓞 E)).2 hpw` as an intermediate fact. Simplify using `using this`. Establish `hpv : Valued.v ((p : ℕ) : w.adicCompletion E) < 1`.

Establish `h1` using `(w.valuation_lt_one_iff_mem (K := E) ((p : ℕ) : 𝓞 E)).2 hpw`. Establish `h2` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w ((p : ℕ) : E)`. Simplify using `only [map_natCast] at h1`. Establish `h3 : ((p : ℕ) : w.adicCompletion E) = (((p : ℕ) : E) : w.adicCompletion E)` using `(map_natCast (algebraMap E (w.adicCompletion E)) p).symm`. Rewrite using `[h3, h2]`.

Conclude with `h1`. Use `set U : Set (w.adicCompletion E)ˣ := {u | Valued.v ((u : w.adicCompletion E) - 1) < 1} with hUdef`. Establish `hU : U ∈ nhds (1 : (w.adicCompletion E)ˣ)`. Establish `h0 : {x : w.adicCompletion E | Valued.v (x - 1) < 1} ∈ nhds ((1 : (w.adicCompletion E)ˣ) : w.adicCompletion E)`. Rewrite using `[Valued.mem_nhds]`.

Conclude with `⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩`. Conclude with `Units.continuous_val.continuousAt.preimage_mem_nhds h0`. Establish `hV : (fun τ : Ine (F` using `E) A => a (ineIncl h τ)) ⁻¹' U ∈ nhds (1 : Ine (F := E) A) := by`. Use `ha.cont.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Simplify using `using hU`.

Take `⟨O, hO, hOs⟩` from `(mem_nhds_induced Subtype.val (1 : Ine (F := E) A) _).1 hV`. Rewrite `hO` using `[OneMemClass.coe_one]`. Take `⟨L, hL, hLO⟩` from `(krullTopology_mem_nhds_one_iff E Ω O).1 hO`. Take `⟨k, hk⟩` from `Formalism.MainNotions.N.KillingConditions.WildPf.wildProP E Ω A p hp hpA (σ : G E Ω) (wildPf_of_isWild hσ) L.fixingSubgroup (IntermediateField.fixingSubgroup_isOpen L)`. Establish `hτ : (σ : G E Ω) ^ (p ^ k) ∈ Ine (F` using `E) A := (Ine (F := E) A).pow_mem hσ.1 _`.

Establish `hmem` using `hOs (show ((⟨_, hτ⟩ : Ine (F := E) A) : G E Ω) ∈ O from hLO hk)`. Establish `e : ineIncl h (⟨_, hτ⟩ : Ine (F` using `E) A) = σ ^ (p ^ k) := Subtype.ext (by simp)`. Simplify using `only [Set.mem_preimage, e, map_pow, hUdef, Set.mem_ofPred_eq, Units.val_pow_eq_pow_val] at hmem`. Conclude with `val_sub_one_lt_of_pow Valued.v hp hpv hmem`.
-/
theorem wild_to_unitsOne (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (σ : Weil h)
    (hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω)) : Valued.v ((a σ : w.adicCompletion E) - 1) < 1 := by
  obtain ⟨p, hp, hpw⟩ : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 E) ∈ w.asIdeal :=
    ⟨_, GlobalTheory.LocalData.resChar_prime w, GlobalTheory.LocalData.resChar_mem w⟩
  have hpA : A.valuation ((p : ℕ) : Ω) < 1 := by
    have := (h ((p : ℕ) : 𝓞 E)).2 hpw
    simpa using this
  have hpv : Valued.v ((p : ℕ) : w.adicCompletion E) < 1 := by
    have h1 := (w.valuation_lt_one_iff_mem (K := E) ((p : ℕ) : 𝓞 E)).2 hpw
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w ((p : ℕ) : E)
    simp only [map_natCast] at h1
    have h3 : ((p : ℕ) : w.adicCompletion E) = (((p : ℕ) : E) : w.adicCompletion E) :=
      (map_natCast (algebraMap E (w.adicCompletion E)) p).symm
    rw [h3, h2]; exact h1
  set U : Set (w.adicCompletion E)ˣ := {u | Valued.v ((u : w.adicCompletion E) - 1) < 1} with hUdef
  have hU : U ∈ nhds (1 : (w.adicCompletion E)ˣ) := by
    have h0 : {x : w.adicCompletion E | Valued.v (x - 1) < 1} ∈
        nhds ((1 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
      rw [Valued.mem_nhds]
      exact ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
    exact Units.continuous_val.continuousAt.preimage_mem_nhds h0
  have hV : (fun τ : Ine (F := E) A => a (ineIncl h τ)) ⁻¹' U ∈ nhds (1 : Ine (F := E) A) := by
    refine ha.cont.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨O, hO, hOs⟩ := (mem_nhds_induced Subtype.val (1 : Ine (F := E) A) _).1 hV
  rw [OneMemClass.coe_one] at hO
  obtain ⟨L, hL, hLO⟩ := (krullTopology_mem_nhds_one_iff E Ω O).1 hO
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.KillingConditions.WildPf.wildProP E Ω A p hp hpA (σ : G E Ω) (wildPf_of_isWild hσ)
    L.fixingSubgroup (IntermediateField.fixingSubgroup_isOpen L)
  have hτ : (σ : G E Ω) ^ (p ^ k) ∈ Ine (F := E) A := (Ine (F := E) A).pow_mem hσ.1 _
  have hmem := hOs (show ((⟨_, hτ⟩ : Ine (F := E) A) : G E Ω) ∈ O from hLO hk)
  have e : ineIncl h (⟨_, hτ⟩ : Ine (F := E) A) = σ ^ (p ^ k) := Subtype.ext (by simp)
  simp only [Set.mem_preimage, e, map_pow, hUdef, Set.mem_ofPred_eq, Units.val_pow_eq_pow_val] at hmem
  exact val_sub_one_lt_of_pow Valued.v hp hpv hmem

end PositivityTheory.LocalParametersCuspidal.DZC

end
