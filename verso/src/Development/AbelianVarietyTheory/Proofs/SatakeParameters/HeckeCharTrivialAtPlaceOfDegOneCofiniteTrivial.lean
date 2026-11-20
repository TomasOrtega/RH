import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticRingOfIntegersMulMemSpanOneGenStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeakApproxUnitFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongrModPowResidueDegreeOneFactorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowValuationDivSubOneLeOfCongrStatement
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

namespace GlobalTheory.HeckeFin

section ValLemmas
variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/- English proof (translation)
Establish `e : a = 1 + (a - 1)` using `by ring`. Rewrite using `[e, Valuation.map_one_add_of_lt v (lt_of_le_of_lt ha hε)]`.
-/
theorem val_eq_one_of_sub_one (v : Valuation K Γ) {a : K} {ε : Γ} (hε : ε < 1)
    (ha : v (a - 1) ≤ ε) : v a = 1 := by
  have e : a = 1 + (a - 1) := by ring
  rw [e, Valuation.map_one_add_of_lt v (lt_of_le_of_lt ha hε)]

/- English proof (translation)
Establish `e : a * b - 1 = a * (b - 1) + (a - 1)` using `by ring`. Rewrite using `[e]`. Use `le_trans (Valuation.map_add v _ _) (max_le ?_ ha)` and prove the remaining obligations. Rewrite using `[map_mul, val_eq_one_of_sub_one v hε ha, one_mul]`. Conclude with `hb`.
-/
theorem mul_sub_one_le (v : Valuation K Γ) {a b : K} {ε : Γ} (hε : ε < 1)
    (ha : v (a - 1) ≤ ε) (hb : v (b - 1) ≤ ε) : v (a * b - 1) ≤ ε := by
  have e : a * b - 1 = a * (b - 1) + (a - 1) := by ring
  rw [e]
  refine le_trans (Valuation.map_add v _ _) (max_le ?_ ha)
  rw [map_mul, val_eq_one_of_sub_one v hε ha, one_mul]; exact hb

/- English proof (translation)
Establish `h1` using `val_eq_one_of_sub_one v hε ha`. Establish `ha0 : a ≠ 0` using `by rintro rfl; simp at h1`. Establish `e : a⁻¹ - 1 = -(a - 1) * a⁻¹` using `by field_simp; ring`. Rewrite using `[e, map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, mul_one]`. Conclude with `ha`.
-/
theorem inv_sub_one_le (v : Valuation K Γ) {a : K} {ε : Γ} (hε : ε < 1)
    (ha : v (a - 1) ≤ ε) : v (a⁻¹ - 1) ≤ ε := by
  have h1 := val_eq_one_of_sub_one v hε ha
  have ha0 : a ≠ 0 := by rintro rfl; simp at h1
  have e : a⁻¹ - 1 = -(a - 1) * a⁻¹ := by field_simp; ring
  rw [e, map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, mul_one]; exact ha

end ValLemmas
end GlobalTheory.HeckeFin

namespace GlobalTheory.HeckeFin

/- English proof (translation)
Rewrite using `[← map_one (algebraMap E (v.adicCompletion E)), ← map_sub]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a - 1)`.
-/
theorem val_coe_sub_one (E : Type) [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (a : E) :
    Valued.v (algebraMap E (v.adicCompletion E) a - 1) = v.valuation E (a - 1) := by
  rw [← map_one (algebraMap E (v.adicCompletion E)), ← map_sub]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a - 1)

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ _ _ χ hχ hdeg hinf w x`. Take `⟨hunr, hloc, hfac⟩` from `GlobalTheory.T.continuous_ideleChar_local_factorization E χ hχ.1`. Use `choose nf hnf using hloc`. Establish `hU` using `Filter.eventually_cofinite.mp hunr`. Establish `hX` using `Filter.eventually_cofinite.mp hdeg`.

Use `set S : Finset (HeightOneSpectrum (𝓞 E)) := hU.toFinset ∪ hX.toFinset ∪ {w} with hS`. Establish `hSu : ∀ v ∉ S, UnrAt χ v`. Introduce `v hv`. Assume the negation of the conclusion as `h`. Conclude with `hv (by simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inl h))`.

Establish `hSd : ∀ v ∉ S, DegOne F v → TrivAt χ v`. Introduce `v hv`. Assume the negation of the conclusion as `h`. Conclude with `hv (by simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inr h))`. Establish `hwS : w ∈ S` using `by simp [hS]`.

Take `⟨θ, D, hD0, hθ⟩` from `GlobalTheory.T.exists_denom_mul_mem_span_one_gen_of_finrank_two F E (Algebra.IsQuadraticExtension.finrank_eq_two F E)`. Use `set ι := algebraMap (𝓞 F) (𝓞 E) with hι`. Establish `hιinj : Function.Injective ι` using `by first`. Consider the case `exact FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)`. Consider the case `exact NoZeroSMulDivisors.algebraMap_injective (𝓞 F) (𝓞 E)`.

Use `set m : Ideal (𝓞 F) := Ideal.span {D} * Ideal.comap ι (∏ Q ∈ S, Q.asIdeal) with hm`. Establish `hm0 : m ≠ ⊥`. Establish `hP : (∏ Q ∈ S, Q.asIdeal) ≠ ⊥`. Rewrite using `[← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]`. Introduce `Q _`.

Rewrite using `[Ideal.zero_eq_bot]`. Conclude with `Q.ne_bot`. Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP`. Establish `hC : Ideal.comap ι (∏ Q ∈ S, Q.asIdeal) ≠ ⊥` using `Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral a)`. Establish `hD : Ideal.span {D} ≠ ⊥` using `by rwa [Ne, Ideal.span_singleton_eq_bot]`.

Rewrite using `[hm, ← Ideal.zero_eq_bot]`. Conclude with `mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot])`. Establish `hmD : m ≤ Ideal.span {D}` using `Ideal.mul_le_left`. Establish `hmS : ∀ Q ∈ S, m ≤ Q.asIdeal.comap ι` using `fun Q hQ => le_trans Ideal.mul_le_right (Ideal.comap_mono (by rw [← Finset.mul_prod_erase S (fun Q => Q.asIdeal) hQ]; exact Ideal.mul_le_left))`. Establish `hfin : {P : HeightOneSpectrum (𝓞 E) | m ≤ P.asIdeal.comap ι}.Finite`.

Establish `h0 : m.map ι ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hιinj]`. Conclude with `hm0`. Use `(Ideal.finite_factors h0).subset ?_` and prove the remaining obligations. Introduce `P hP`.

Simplify using `only [Set.mem_setOf_eq] at hP ⊢`. Rewrite using `[Ideal.dvd_iff_le]`. Conclude with `Ideal.map_le_iff_le_comap.mpr hP`. Use `set S' := hfin.toFinset with hS'`. Establish `memS' : ∀ P, P ∈ S' ↔ m ≤ P.asIdeal.comap ι` using `by intro P; simp [hS']`.

Establish `hwS' : w ∈ S'` using `(memS' w).2 (hmS w hwS)`. Establish `hSS' : ∀ v ∉ S', v ∉ S` using `fun v hv h => hv ((memS' v).2 (hmS v h))`. Use `set n : ℕ := S'.sup nf + 1 with hn`. Use `set ε : WithZero (Multiplicative ℤ) := WithZero.exp (-(n:ℤ)) with hεdef`. Establish `hε : ε < 1` using `by rw [hεdef, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega`.

Establish `hεv : ∀ v ∈ S', ε ≤ WithZero.exp (-(nf v : ℤ))`. Introduce `v hv`. Rewrite using `[hεdef, WithZero.exp_le_exp]`. Use `Finset.le_sup (f := nf) hv` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨y, hy0, hyw, hyv⟩` from `GlobalTheory.T.exists_weak_approx_unit_finite_place E S' w x n`. Take `⟨y1, y2, hy2, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) y`. Establish `hy2' : y2 ≠ 0` using `nonZeroDivisors.ne_zero hy2`. Establish `hy1' : y1 ≠ 0` using `by rintro rfl; simp at hy0`. Establish `hDι : ι D ≠ 0`.

Introduce `h`. Apply `hD0` to reduce the goal to its premises. Apply `hιinj` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Establish `hc1 : ι D * y1 ≠ 0` using `mul_ne_zero hDι hy1'`.

Establish `hc2 : ι D * y2 ≠ 0` using `mul_ne_zero hDι hy2'`. Use `choose Nf hNf using fun (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) (hc : c ≠ 0) => GlobalTheory.T.exists_pow_valuation_div_sub_one_le_of_congr E v c hc n`. Use `set N : ℕ := S'.sup (fun v => Nf v _ hc1 ⊔ Nf v _ hc2) with hN`. Take `⟨k1, hk1, hk1P⟩` from `GlobalTheory.T.exists_congr_mod_pow_residueDegreeOne_factors F E θ D hθ m hm0 hmD y1 N`. Take `⟨k2, hk2, hk2P⟩` from `GlobalTheory.T.exists_congr_mod_pow_residueDegreeOne_factors F E θ D hθ m hm0 hmD y2 N`.

Establish `hmem : ∀ v ∈ S', ∀ (k c : 𝓞 E), k - c ∈ Ideal.map ι (m ^ N) → ∀ M ≤ N, k - c ∈ v.asIdeal ^ M`. Introduce `v hv k c h M hM`. Establish `h1 : Ideal.map ι (m ^ N) ≤ v.asIdeal ^ N`. Rewrite using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr ((memS' v).1 hv)) N`.

Conclude with `Ideal.pow_le_pow_right hM (h1 h)`. Establish `hcl1 : ∀ v ∈ S', v.valuation E ((k1 : E) / ((ι D * y1 : 𝓞 E) : E) - 1) ≤ ε` using `fun v hv => hNf v _ hc1 k1 (hmem v hv _ _ hk1 _ (le_trans le_sup_left (Finset.le_sup (f := fun v => Nf v _ hc1 ⊔ Nf v _ hc2) hv)))`. Establish `hcl2 : ∀ v ∈ S', v.valuation E ((k2 : E) / ((ι D * y2 : 𝓞 E) : E) - 1) ≤ ε` using `fun v hv => hNf v _ hc2 k2 (hmem v hv _ _ hk2 _ (le_trans le_sup_right (Finset.le_sup (f := fun v => Nf v _ hc1 ⊔ Nf v _ hc2) hv)))`. Establish `hk1' : (k1 : E) ≠ 0`. Introduce `h`.

Use `hcl1 w hwS'` as an intermediate fact. Rewrite `this` using `[h, zero_div, zero_sub, Valuation.map_neg, map_one]`. Conclude with `absurd hε (not_lt.mpr this)`. Establish `hk2' : (k2 : E) ≠ 0`. Introduce `h`.

Use `hcl2 w hwS'` as an intermediate fact. Rewrite `this` using `[h, zero_div, zero_sub, Valuation.map_neg, map_one]`. Conclude with `absurd hε (not_lt.mpr this)`. Establish `ha : ∀ z : 𝓞 E, algebraMap (𝓞 E) E z = (z : E)` using `fun z => rfl`. Establish `hDE : ((ι D : 𝓞 E) : E) ≠ 0` using `by exact_mod_cast hDι`.

Establish `hy1E : (y1 : E) ≠ 0` using `by exact_mod_cast hy1'`. Establish `hy2E : (y2 : E) ≠ 0` using `by exact_mod_cast hy2'`. Use `set kk : E := (k1 : E) / (k2 : E) with hkk`. Establish `hkk0 : kk ≠ 0` using `div_ne_zero hk1' hk2'`. Establish `hkey : kk = ((k1 : E) / ((ι D * y1 : 𝓞 E) : E)) * ((k2 : E) / ((ι D * y2 : 𝓞 E) : E))⁻¹ * (algebraMap (𝓞 E) E y1 / algebraMap (𝓞 E) E y2)`.

Rewrite using `[ha, ha, hkk]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hv1 : ∀ v ∈ S', v ≠ w → v.valuation E (kk - 1) ≤ ε`. Introduce `v hv hvw`.

Rewrite using `[hkey]`. Conclude with `GlobalTheory.HeckeFin.mul_sub_one_le _ hε (GlobalTheory.HeckeFin.mul_sub_one_le _ hε (hcl1 v hv) (GlobalTheory.HeckeFin.inv_sub_one_le _ hε (hcl2 v hv))) (hyv v hv hvw)`. Establish `hvw : Valued.v (algebraMap E (w.adicCompletion E) kk * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ ε`. Establish `e : algebraMap E (w.adicCompletion E) kk * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (((k1 : E) / ((ι D * y1 : 𝓞 E) : E)) * ((k2 : E) / ((ι D * y2 : 𝓞 E) : E))⁻¹) * (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E y1 / algebraM …`. Rewrite using `[hkey, map_mul, mul_assoc]`.

Rewrite using `[e]`. Use `GlobalTheory.HeckeFin.mul_sub_one_le _ hε ?_ hyw` and prove the remaining obligations. Rewrite using `[val_coe_sub_one]`. Conclude with `GlobalTheory.HeckeFin.mul_sub_one_le _ hε (hcl1 w hwS') (GlobalTheory.HeckeFin.inv_sub_one_le _ hε (hcl2 w hwS'))`. Use `set kU : Eˣ := Units.mk0 kk hkk0 with hkU`.

Establish `hcoe : ∀ v : HeightOneSpectrum (𝓞 E), ((finPart E v (diagUnits E kU) : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) kk` using `fun v => rfl`. Establish `hout : ∀ v ∉ S', χ (localIdele E v (finPart E v (diagUnits E kU))) = 1`. Introduce `v hv`. Establish `hvS` using `hSS' v hv`. Establish `hmv : ¬ m ≤ v.asIdeal.comap ι` using `fun h => hv ((memS' v).2 h)`.

Distinguish the cases in `h1 : k1 ∈ v.asIdeal`. Conclude with `hSd v hvS (hk1P v hmv h1) _`. Distinguish the cases in `h2 : k2 ∈ v.asIdeal`. Conclude with `hSd v hvS (hk2P v hmv h2) _`. Apply `hSu v hvS` to reduce the goal to its premises.

Rewrite using `[hcoe, show Valued.v (algebraMap E (v.adicCompletion E) kk) = v.valuation E kk from HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v kk, hkk, map_div₀]`. Establish `e1 : ∀ k : 𝓞 E, k ∉ v.asIdeal → v.valuation E (k : E) = 1`. Introduce `k hk`. Use `le_antisymm (v.valuation_le_one k) ?_` and prove the remaining obligations. Rewrite using `[← not_lt]`.

Introduce `hlt`. Conclude with `hk ((v.valuation_lt_one_iff_mem k).mp hlt)`. Rewrite using `[e1 k1 h1, e1 k2 h2, div_one]`. Establish `hprod` using `hfac (diagUnits E kU) S' hout`. Rewrite `hprod` using `[hχ.2 kU, hinf, one_mul, Finset.prod_eq_single w]`.

Use `set z : (w.adicCompletion E)ˣ := (finPart E w (diagUnits E kU))⁻¹ * x with hz`. Establish `hzv : χ (localIdele E w z) = 1`. Apply `hnf w z` to reduce the goal to its premises. Use `le_trans ?_ (hεv w hwS')` and prove the remaining obligations. Establish `e : (z : w.adicCompletion E) = (algebraMap E (w.adicCompletion E) kk * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E))⁻¹`.

Rewrite using `[hz, Units.val_mul, Units.val_inv_eq_inv_val, hcoe, Units.val_inv_eq_inv_val, mul_inv, inv_inv]`. Rewrite using `[e]`. Conclude with `GlobalTheory.HeckeFin.inv_sub_one_le _ hε hvw`. Establish `hx : x = finPart E w (diagUnits E kU) * z` using `by rw [hz, mul_inv_cancel_left]`. Use `show χ (localIdele E w x) = 1`.

Rewrite using `[hx, map_mul, map_mul, ← hprod, hzv, one_mul]`. Introduce `v hv hvw`. Apply `hnf v` to reduce the goal to its premises. Rewrite using `[hcoe]`. Use `le_trans ?_ (hεv v hv)` and prove the remaining obligations.

Rewrite using `[val_coe_sub_one]`. Conclude with `hv1 v hv hvw`. Introduce `h`. Conclude with `absurd hwS' h`.
-/
theorem trivAt_of_degOne_cofinite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (χ : Ideles E →* ℂˣ), IsHeckeChar E χ → (∀ᶠ w in Filter.cofinite, DegOne F w → TrivAt χ w) → (∀ x : (InfiniteAdeleRing E)ˣ, χ (infIdele E x) = 1) → ∀ w, TrivAt χ w := by
  intro F E _ _ _ _ _ _ _ _ χ hχ hdeg hinf w x
  classical
  obtain ⟨hunr, hloc, hfac⟩ := GlobalTheory.T.continuous_ideleChar_local_factorization E χ hχ.1
  choose nf hnf using hloc
  have hU := Filter.eventually_cofinite.mp hunr
  have hX := Filter.eventually_cofinite.mp hdeg
  set S : Finset (HeightOneSpectrum (𝓞 E)) := hU.toFinset ∪ hX.toFinset ∪ {w} with hS
  have hSu : ∀ v ∉ S, UnrAt χ v := by
    intro v hv; by_contra h
    exact hv (by simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inl h))
  have hSd : ∀ v ∉ S, DegOne F v → TrivAt χ v := by
    intro v hv; by_contra h
    exact hv (by simp only [hS, Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq]; exact Or.inl (Or.inr h))
  have hwS : w ∈ S := by simp [hS]
  obtain ⟨θ, D, hD0, hθ⟩ := GlobalTheory.T.exists_denom_mul_mem_span_one_gen_of_finrank_two F E (Algebra.IsQuadraticExtension.finrank_eq_two F E)
  set ι := algebraMap (𝓞 F) (𝓞 E) with hι
  have hιinj : Function.Injective ι := by
    first
    | exact FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E)
    | exact NoZeroSMulDivisors.algebraMap_injective (𝓞 F) (𝓞 E)
  set m : Ideal (𝓞 F) := Ideal.span {D} * Ideal.comap ι (∏ Q ∈ S, Q.asIdeal) with hm
  have hm0 : m ≠ ⊥ := by
    have hP : (∏ Q ∈ S, Q.asIdeal) ≠ ⊥ := by
      rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
      intro Q _; rw [Ideal.zero_eq_bot]; exact Q.ne_bot
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    have hC : Ideal.comap ι (∏ Q ∈ S, Q.asIdeal) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_integral_mem ha0 ha (Algebra.IsIntegral.isIntegral a)
    have hD : Ideal.span {D} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
    rw [hm, ← Ideal.zero_eq_bot]
    exact mul_ne_zero (by rwa [Ideal.zero_eq_bot]) (by rwa [Ideal.zero_eq_bot])
  have hmD : m ≤ Ideal.span {D} := Ideal.mul_le_left
  have hmS : ∀ Q ∈ S, m ≤ Q.asIdeal.comap ι := fun Q hQ =>
    le_trans Ideal.mul_le_right (Ideal.comap_mono (by rw [← Finset.mul_prod_erase S (fun Q => Q.asIdeal) hQ]; exact Ideal.mul_le_left))
  have hfin : {P : HeightOneSpectrum (𝓞 E) | m ≤ P.asIdeal.comap ι}.Finite := by
    have h0 : m.map ι ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hιinj]; exact hm0
    refine (Ideal.finite_factors h0).subset ?_
    intro P hP
    simp only [Set.mem_setOf_eq] at hP ⊢
    rw [Ideal.dvd_iff_le]; exact Ideal.map_le_iff_le_comap.mpr hP
  set S' := hfin.toFinset with hS'
  have memS' : ∀ P, P ∈ S' ↔ m ≤ P.asIdeal.comap ι := by intro P; simp [hS']
  have hwS' : w ∈ S' := (memS' w).2 (hmS w hwS)
  have hSS' : ∀ v ∉ S', v ∉ S := fun v hv h => hv ((memS' v).2 (hmS v h))
  set n : ℕ := S'.sup nf + 1 with hn
  set ε : WithZero (Multiplicative ℤ) := WithZero.exp (-(n:ℤ)) with hεdef
  have hε : ε < 1 := by rw [hεdef, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hεv : ∀ v ∈ S', ε ≤ WithZero.exp (-(nf v : ℤ)) := by
    intro v hv; rw [hεdef, WithZero.exp_le_exp]; have := Finset.le_sup (f := nf) hv; omega
  obtain ⟨y, hy0, hyw, hyv⟩ := GlobalTheory.T.exists_weak_approx_unit_finite_place E S' w x n
  obtain ⟨y1, y2, hy2, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have hy2' : y2 ≠ 0 := nonZeroDivisors.ne_zero hy2
  have hy1' : y1 ≠ 0 := by rintro rfl; simp at hy0
  have hDι : ι D ≠ 0 := by
    intro h; apply hD0; apply hιinj; rw [h, map_zero]
  have hc1 : ι D * y1 ≠ 0 := mul_ne_zero hDι hy1'
  have hc2 : ι D * y2 ≠ 0 := mul_ne_zero hDι hy2'
  choose Nf hNf using fun (v : HeightOneSpectrum (𝓞 E)) (c : 𝓞 E) (hc : c ≠ 0) => GlobalTheory.T.exists_pow_valuation_div_sub_one_le_of_congr E v c hc n
  set N : ℕ := S'.sup (fun v => Nf v _ hc1 ⊔ Nf v _ hc2) with hN
  obtain ⟨k1, hk1, hk1P⟩ := GlobalTheory.T.exists_congr_mod_pow_residueDegreeOne_factors F E θ D hθ m hm0 hmD y1 N
  obtain ⟨k2, hk2, hk2P⟩ := GlobalTheory.T.exists_congr_mod_pow_residueDegreeOne_factors F E θ D hθ m hm0 hmD y2 N
  have hmem : ∀ v ∈ S', ∀ (k c : 𝓞 E), k - c ∈ Ideal.map ι (m ^ N) → ∀ M ≤ N, k - c ∈ v.asIdeal ^ M := by
    intro v hv k c h M hM
    have h1 : Ideal.map ι (m ^ N) ≤ v.asIdeal ^ N := by
      rw [Ideal.map_pow]; exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr ((memS' v).1 hv)) N
    exact Ideal.pow_le_pow_right hM (h1 h)
  have hcl1 : ∀ v ∈ S', v.valuation E ((k1 : E) / ((ι D * y1 : 𝓞 E) : E) - 1) ≤ ε := fun v hv =>
    hNf v _ hc1 k1 (hmem v hv _ _ hk1 _ (le_trans le_sup_left (Finset.le_sup (f := fun v => Nf v _ hc1 ⊔ Nf v _ hc2) hv)))
  have hcl2 : ∀ v ∈ S', v.valuation E ((k2 : E) / ((ι D * y2 : 𝓞 E) : E) - 1) ≤ ε := fun v hv =>
    hNf v _ hc2 k2 (hmem v hv _ _ hk2 _ (le_trans le_sup_right (Finset.le_sup (f := fun v => Nf v _ hc1 ⊔ Nf v _ hc2) hv)))
  have hk1' : (k1 : E) ≠ 0 := by
    intro h; have := hcl1 w hwS'; rw [h, zero_div, zero_sub, Valuation.map_neg, map_one] at this
    exact absurd hε (not_lt.mpr this)
  have hk2' : (k2 : E) ≠ 0 := by
    intro h; have := hcl2 w hwS'; rw [h, zero_div, zero_sub, Valuation.map_neg, map_one] at this
    exact absurd hε (not_lt.mpr this)
  have ha : ∀ z : 𝓞 E, algebraMap (𝓞 E) E z = (z : E) := fun z => rfl
  have hDE : ((ι D : 𝓞 E) : E) ≠ 0 := by exact_mod_cast hDι
  have hy1E : (y1 : E) ≠ 0 := by exact_mod_cast hy1'
  have hy2E : (y2 : E) ≠ 0 := by exact_mod_cast hy2'
  set kk : E := (k1 : E) / (k2 : E) with hkk
  have hkk0 : kk ≠ 0 := div_ne_zero hk1' hk2'
  have hkey : kk = ((k1 : E) / ((ι D * y1 : 𝓞 E) : E)) * ((k2 : E) / ((ι D * y2 : 𝓞 E) : E))⁻¹ *
      (algebraMap (𝓞 E) E y1 / algebraMap (𝓞 E) E y2) := by
    rw [ha, ha, hkk]; push_cast; field_simp
  have hv1 : ∀ v ∈ S', v ≠ w → v.valuation E (kk - 1) ≤ ε := by
    intro v hv hvw
    rw [hkey]
    exact GlobalTheory.HeckeFin.mul_sub_one_le _ hε (GlobalTheory.HeckeFin.mul_sub_one_le _ hε (hcl1 v hv)
      (GlobalTheory.HeckeFin.inv_sub_one_le _ hε (hcl2 v hv))) (hyv v hv hvw)
  have hvw : Valued.v (algebraMap E (w.adicCompletion E) kk *
      ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) - 1) ≤ ε := by
    have e : algebraMap E (w.adicCompletion E) kk * ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        algebraMap E (w.adicCompletion E) (((k1 : E) / ((ι D * y1 : 𝓞 E) : E)) * ((k2 : E) / ((ι D * y2 : 𝓞 E) : E))⁻¹) *
        (algebraMap E (w.adicCompletion E) (algebraMap (𝓞 E) E y1 / algebraMap (𝓞 E) E y2) *
          ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E)) := by
      rw [hkey, map_mul, mul_assoc]
    rw [e]
    refine GlobalTheory.HeckeFin.mul_sub_one_le _ hε ?_ hyw
    rw [val_coe_sub_one]
    exact GlobalTheory.HeckeFin.mul_sub_one_le _ hε (hcl1 w hwS') (GlobalTheory.HeckeFin.inv_sub_one_le _ hε (hcl2 w hwS'))
  set kU : Eˣ := Units.mk0 kk hkk0 with hkU
  have hcoe : ∀ v : HeightOneSpectrum (𝓞 E), ((finPart E v (diagUnits E kU) : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
      algebraMap E (v.adicCompletion E) kk := fun v => rfl
  have hout : ∀ v ∉ S', χ (localIdele E v (finPart E v (diagUnits E kU))) = 1 := by
    intro v hv
    have hvS := hSS' v hv
    have hmv : ¬ m ≤ v.asIdeal.comap ι := fun h => hv ((memS' v).2 h)
    by_cases h1 : k1 ∈ v.asIdeal
    · exact hSd v hvS (hk1P v hmv h1) _
    by_cases h2 : k2 ∈ v.asIdeal
    · exact hSd v hvS (hk2P v hmv h2) _
    apply hSu v hvS
    rw [hcoe, show Valued.v (algebraMap E (v.adicCompletion E) kk) = v.valuation E kk from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v kk, hkk, map_div₀]
    have e1 : ∀ k : 𝓞 E, k ∉ v.asIdeal → v.valuation E (k : E) = 1 := by
      intro k hk
      refine le_antisymm (v.valuation_le_one k) ?_
      rw [← not_lt]; intro hlt; exact hk ((v.valuation_lt_one_iff_mem k).mp hlt)
    rw [e1 k1 h1, e1 k2 h2, div_one]
  have hprod := hfac (diagUnits E kU) S' hout
  rw [hχ.2 kU, hinf, one_mul, Finset.prod_eq_single w] at hprod
  · set z : (w.adicCompletion E)ˣ := (finPart E w (diagUnits E kU))⁻¹ * x with hz
    have hzv : χ (localIdele E w z) = 1 := by
      apply hnf w z
      refine le_trans ?_ (hεv w hwS')
      have e : (z : w.adicCompletion E) = (algebraMap E (w.adicCompletion E) kk *
          ((x⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E))⁻¹ := by
        rw [hz, Units.val_mul, Units.val_inv_eq_inv_val, hcoe, Units.val_inv_eq_inv_val, mul_inv, inv_inv]
      rw [e]; exact GlobalTheory.HeckeFin.inv_sub_one_le _ hε hvw
    have hx : x = finPart E w (diagUnits E kU) * z := by rw [hz, mul_inv_cancel_left]
    show χ (localIdele E w x) = 1
    rw [hx, map_mul, map_mul, ← hprod, hzv, one_mul]
  · intro v hv hvw
    apply hnf v
    rw [hcoe]; refine le_trans ?_ (hεv v hv)
    rw [val_coe_sub_one]; exact hv1 v hv hvw
  · intro h; exact absurd hwS' h

end GlobalTheory.HeckeFin
