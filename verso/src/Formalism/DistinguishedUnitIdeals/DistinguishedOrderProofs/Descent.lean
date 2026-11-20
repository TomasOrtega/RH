import Mathlib
import Formalism.DistinguishedUnitIdeals.UnivPart

noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

section Helpers

variable {O : Type} [CommRing O]

/- English proof (translation)
Simplify `φ.commutes a` using `[PowerSeries.algebraMap_apply]`.
-/
theorem algHom_C (φ : PowerSeries O →ₐ[O] PowerSeries O) (a : O) : φ (C a) = C a := by
  simpa [PowerSeries.algebraMap_apply] using φ.commutes a

/- English proof (translation)
Use `conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const h]`. Rewrite using `[map_add, map_mul, algHom_C]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem algHom_eq_const_add (φ : PowerSeries O →ₐ[O] PowerSeries O) (h : PowerSeries O) :
    φ h = C (constantCoeff h) + φ X * φ (mk fun p => coeff (p + 1) h) := by
  conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const h]
  rw [map_add, map_mul, algHom_C]
  ring

/- English proof (translation)
Establish `h` using `hE.coe_natDegree_eq_order_map (E : PowerSeries O) 1 (by rw [map_one]; exact (Ideal.ne_top_iff_one I).mp hI) (by rw [mul_one])`. Rewrite using `[← h, ENat.toNat_coe]`.
-/
theorem order_map_toNat_of_isDistinguishedAt {I : Ideal O} (hI : I ≠ ⊤) {E : Polynomial O}
    (hE : E.IsDistinguishedAt I) :
    ((E : PowerSeries O).map (Ideal.Quotient.mk I)).order.toNat = E.natDegree := by
  have h := hE.coe_natDegree_eq_order_map (E : PowerSeries O) 1
    (by rw [map_one]; exact (Ideal.ne_top_iff_one I).mp hI) (by rw [mul_one])
  rw [← h, ENat.toNat_coe]

/- English proof (translation)
Establish `H` using `hE.isWeierstrassDivisorAt hI`. Establish `hd` using `H.isWeierstrassDivisionAt_div_mod F`. Use `⟨H.div F, H.mod F, ?_, hd.eq_mul_add⟩` and prove the remaining obligations. Establish `h1` using `hd.degree_lt`. Rewrite `h1` using `[order_map_toNat_of_isDistinguishedAt hI hE]`. Then use the resulting hypothesis.
-/
theorem exists_div_of_isDistinguishedAt {I : Ideal O} [IsAdicComplete I O] (hI : I ≠ ⊤)
    {E : Polynomial O} (hE : E.IsDistinguishedAt I) (F : PowerSeries O) :
    ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < E.natDegree ∧
      F = (E : PowerSeries O) * q + r := by
  have H := hE.isWeierstrassDivisorAt hI
  have hd := H.isWeierstrassDivisionAt_div_mod F
  refine ⟨H.div F, H.mod F, ?_, hd.eq_mul_add⟩
  have h1 := hd.degree_lt
  rwa [order_map_toNat_of_isDistinguishedAt hI hE] at h1

/- English proof (translation)
Establish `H` using `hE.isWeierstrassDivisorAt hI`. Use `(H.eq_zero_of_mul_eq ?_ h).2` and prove the remaining obligations. Rewrite using `[order_map_toNat_of_isDistinguishedAt hI hE]` and apply the resulting hypothesis.
-/
theorem eq_zero_of_isDistinguishedAt_mul {I : Ideal O} [IsAdicComplete I O] (hI : I ≠ ⊤)
    {E : Polynomial O} (hE : E.IsDistinguishedAt I) {q : PowerSeries O} {r : Polynomial O}
    (hr : r.degree < E.natDegree) (h : (E : PowerSeries O) * q = r) : r = 0 := by
  have H := hE.isWeierstrassDivisorAt hI
  refine (H.eq_zero_of_mul_eq ?_ h).2
  rwa [order_map_toNat_of_isDistinguishedAt hI hE]

/- English proof (translation)
Establish `h` using `map_sum (Polynomial.coeToPowerSeries.ringHom (R := O)) (fun i : Fin d => Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) Finset.univ`. Simplify using `only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X] at h`. Conclude with `h`.
-/
theorem coe_sum_fin {d : ℕ} (a : Fin d → O) :
    ((∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O) :
      PowerSeries O) = ∑ i : Fin d, C (a i) * X ^ (i : ℕ) := by
  have h := map_sum (Polynomial.coeToPowerSeries.ringHom (R := O))
    (fun i : Fin d => Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)) Finset.univ
  simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_mul, Polynomial.coe_C,
    Polynomial.coe_pow, Polynomial.coe_X] at h
  exact h

/- English proof (translation)
Simplify using `[Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj]`.
-/
theorem coeff_sum_fin {d : ℕ} (a : Fin d → O) (j : Fin d) :
    (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O).coeff j = a j := by
  simp [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj]

/- English proof (translation)
Establish `h : r = ∑ i : Fin d, Polynomial.C (r.coeff i) * Polynomial.X ^ (i : ℕ)`. Use extensionality with `j`. Rewrite using `[Polynomial.finset_sum_coeff]`. Simplify using `only [Polynomial.coeff_C_mul_X_pow]`. Distinguish the cases in `hj : j < d`.

Rewrite using `[Finset.sum_eq_single ⟨j, hj⟩]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `h`.

Conclude with `hb (Fin.ext h.symm)`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hr (by exact_mod_cast not_lt.mp hj))]`. Use `symm`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hj (h ▸ i.2)`. Rewrite using `[← coe_sum_fin]`.

Conclude with `congrArg _ h`.
-/
theorem coe_eq_sum_fin {d : ℕ} {r : Polynomial O} (hr : r.degree < d) :
    (r : PowerSeries O) = ∑ i : Fin d, C (r.coeff i) * X ^ (i : ℕ) := by
  have h : r = ∑ i : Fin d, Polynomial.C (r.coeff i) * Polynomial.X ^ (i : ℕ) := by
    ext j
    rw [Polynomial.finset_sum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    by_cases hj : j < d
    · rw [Finset.sum_eq_single ⟨j, hj⟩]
      · simp
      · intro b _ hb
        rw [if_neg]
        intro h
        exact hb (Fin.ext h.symm)
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hr (by exact_mod_cast not_lt.mp hj))]
      symm
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg]
      intro h
      exact hj (h ▸ i.2)
  rw [← coe_sum_fin]
  exact congrArg _ h

/- English proof (translation)
Establish `hI : Ideal.span {P} ≠ ⊤` using `by rwa [Ne, Ideal.span_singleton_eq_top]`. Establish `h0` using `Ideal.iInf_pow_eq_bot_of_isDomain _ hI`. Establish `hx : x ∈ ⨅ i, Ideal.span {P} ^ i` using `Ideal.mem_iInf.mpr fun N => by`. Rewrite using `[Ideal.span_singleton_pow, Ideal.mem_span_singleton]`. Conclude with `h N`.

Rewrite `hx` using `[h0, Ideal.mem_bot]`. Conclude with `hx`.
-/
theorem eq_zero_of_forall_pow_dvd {R : Type} [CommRing R] [IsNoetherianRing R] [IsDomain R]
    {P : R} (hP : ¬ IsUnit P) {x : R} (h : ∀ N : ℕ, P ^ N ∣ x) : x = 0 := by
  have hI : Ideal.span {P} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  have h0 := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  have hx : x ∈ ⨅ i, Ideal.span {P} ^ i := Ideal.mem_iInf.mpr fun N => by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact h N
  rw [h0, Ideal.mem_bot] at hx
  exact hx

/- English proof (translation)
Use `choose qf rf hrf hF using hdiv`. Set `H : PowerSeries O → Fin d → PowerSeries O` to `fun F i => mk fun k => (rf (qf^[k] F)).coeff i`. Establish `hT : ∀ G i, (mk fun p => coeff (p + 1) (H G i)) = H (qf G) i`. Introduce `G i`. Use extensionality with `p`.

Simplify using `[H, PowerSeries.coeff_mk, Function.iterate_succ_apply]`. Establish `hc : ∀ G i, constantCoeff (H G i) = (rf G).coeff i`. Introduce `G i`. Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]`. Both sides reduce to the same expression.

Establish `hS : ∀ G, ∑ i, φ (H G i) * X ^ (i : ℕ) = rf G + φ X * ∑ i, φ (H (qf G) i) * X ^ (i : ℕ)`. Introduce `G`. Rewrite using `[coe_eq_sum_fin (hrf G), Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[algHom_eq_const_add φ (H G i), hc, hT]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hdvd : ∀ N G, φ X ^ N ∣ G - ∑ i, φ (H G i) * X ^ (i : ℕ)`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => intro G`.

Simplify using the standard rewrite rules. Consider the case `succ N ih`. Introduce `G`. Take `⟨c, hc'⟩` from `ih (qf G)`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Rewrite using `[hS G]`. Take the linear combination `(hF G) + φ X * hc'`. Use `⟨H F, ?_⟩` and prove the remaining obligations. Conclude with `(sub_eq_zero.mp (hkrull _ fun N => hdvd N F))`.
-/
theorem exists_sum_algHom_mul_X_pow (φ : PowerSeries O →ₐ[O] PowerSeries O) (d : ℕ)
    (hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < d ∧ F = φ X * q + r)
    (hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0)
    (F : PowerSeries O) : ∃ h : Fin d → PowerSeries O, F = ∑ i, φ (h i) * X ^ (i : ℕ) := by
  choose qf rf hrf hF using hdiv
  let H : PowerSeries O → Fin d → PowerSeries O := fun F i => mk fun k => (rf (qf^[k] F)).coeff i
  have hT : ∀ G i, (mk fun p => coeff (p + 1) (H G i)) = H (qf G) i := by
    intro G i
    ext p
    simp [H, PowerSeries.coeff_mk, Function.iterate_succ_apply]
  have hc : ∀ G i, constantCoeff (H G i) = (rf G).coeff i := by
    intro G i
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    rfl
  have hS : ∀ G, ∑ i, φ (H G i) * X ^ (i : ℕ) = rf G + φ X * ∑ i, φ (H (qf G) i) * X ^ (i : ℕ) := by
    intro G
    rw [coe_eq_sum_fin (hrf G), Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [algHom_eq_const_add φ (H G i), hc, hT]
    ring
  have hdvd : ∀ N G, φ X ^ N ∣ G - ∑ i, φ (H G i) * X ^ (i : ℕ) := by
    intro N
    induction N with
    | zero => intro G; simp
    | succ N ih =>
      intro G
      obtain ⟨c, hc'⟩ := ih (qf G)
      refine ⟨c, ?_⟩
      rw [hS G]
      linear_combination (hF G) + φ X * hc'
  refine ⟨H F, ?_⟩
  exact (sub_eq_zero.mp (hkrull _ fun N => hdvd N F))

/- English proof (translation)
Establish `step : ∀ h : Fin d → PowerSeries O, ∑ i, φ (h i) * X ^ (i : ℕ) = 0 → (∀ i, constantCoeff (h i) = 0) ∧ ∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ) = 0`. Introduce `h hs`. Establish `e : ∑ i, φ (h i) * X ^ (i : ℕ) = ∑ i, C (constantCoeff (h i)) * X ^ (i : ℕ) + φ X * ∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ)`. Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[algHom_eq_const_add φ (h i)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e` using `[hs]`. Establish `h0` using `huniq (fun i => constantCoeff (h i)) (-(∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ))) (by linear_combination -e)`. Use `⟨h0, ?_⟩` and prove the remaining obligations.

Establish `hsum0 : ∑ i, C (constantCoeff (h i)) * X ^ (i : ℕ) = 0` using `Finset.sum_eq_zero fun i _ => by`. Rewrite using `[show constantCoeff (h i) = 0 from h0 i, map_zero, zero_mul]`. Rewrite `e` using `[hsum0, zero_add]`. Conclude with `(mul_eq_zero.mp e.symm).resolve_left hP0`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `h hs i`. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Conclude with `(step h hs).1 i`.

Consider the case `succ n ih`. Introduce `h hs i`. Establish `h1` using `ih _ (step h hs).2 i`. Simplify `h1` using `[PowerSeries.coeff_mk]`.
-/
theorem eq_zero_of_sum_algHom_mul_X_pow [IsDomain O] (φ : PowerSeries O →ₐ[O] PowerSeries O)
    (d : ℕ)
    (huniq : ∀ (a : Fin d → O) (q : PowerSeries O),
      ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0)
    (hP0 : φ X ≠ 0) :
    ∀ (n : ℕ) (h : Fin d → PowerSeries O), ∑ i, φ (h i) * X ^ (i : ℕ) = 0 →
      ∀ i, coeff n (h i) = 0 := by
  have step : ∀ h : Fin d → PowerSeries O, ∑ i, φ (h i) * X ^ (i : ℕ) = 0 →
      (∀ i, constantCoeff (h i) = 0) ∧
        ∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ) = 0 := by
    intro h hs
    have e : ∑ i, φ (h i) * X ^ (i : ℕ) = ∑ i, C (constantCoeff (h i)) * X ^ (i : ℕ) +
        φ X * ∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [algHom_eq_const_add φ (h i)]
      ring
    rw [hs] at e
    have h0 := huniq (fun i => constantCoeff (h i))
      (-(∑ i, φ (mk fun p => coeff (p + 1) (h i)) * X ^ (i : ℕ))) (by linear_combination -e)
    refine ⟨h0, ?_⟩
    have hsum0 : ∑ i, C (constantCoeff (h i)) * X ^ (i : ℕ) = 0 :=
      Finset.sum_eq_zero fun i _ => by
        rw [show constantCoeff (h i) = 0 from h0 i, map_zero, zero_mul]
    rw [hsum0, zero_add] at e
    exact (mul_eq_zero.mp e.symm).resolve_left hP0
  intro n
  induction n with
  | zero =>
    intro h hs i
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (step h hs).1 i
  | succ n ih =>
    intro h hs i
    have h1 := ih _ (step h hs).2 i
    simpa [PowerSeries.coeff_mk] using h1

end Helpers

/- English proof (translation)
Introduce `O _ _ _ _ ϖ hϖ φ d hd hU c f g hf`. Take `⟨u, E, hu, hE, hEd, hP⟩` from `hU`. Establish `hmax` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`. Use `haveI : IsAdicComplete (Ideal.span {ϖ}) O := by rw [← hmax]; infer_instance`. Establish `hI : Ideal.span {ϖ} ≠ ⊤`.

Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Conclude with `hϖ.not_isUnit`. Take `⟨uu, rfl⟩` from `hu`. Establish `hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O), r.degree < d ∧ F = φ X * q + r`. Introduce `F`.

Take `⟨q, r, hr, hFq⟩` from `exists_div_of_isDistinguishedAt hI hE F`. Use `⟨(↑uu⁻¹ : PowerSeries O) * q, r, hEd ▸ hr, ?_⟩` and prove the remaining obligations. Rewrite using `[hP, hFq]`. Establish `: (↑uu : PowerSeries O) * ↑uu⁻¹ = 1` using `Units.mul_inv uu`. Take the linear combination `(-(E : PowerSeries O) * q) * this`.

Establish `hPnu : ¬ IsUnit (φ X)`. Introduce `hunit`. Rewrite `hunit` using `[PowerSeries.isUnit_iff_constantCoeff, hP, map_mul]`. Establish `h2` using `(IsUnit.mul_iff.mp hunit).2`. Establish `hmem : PowerSeries.constantCoeff (E : PowerSeries O) ∈ Ideal.span {ϖ}`.

Rewrite using `[← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]`. Conclude with `hE.toIsWeaklyEisensteinAt.mem (by omega)`. Conclude with `hI (Ideal.eq_top_of_isUnit_mem _ hmem h2)`. Establish `hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0` using `fun x hx => eq_zero_of_forall_pow_dvd hPnu hx`. Establish `hP0 : φ X ≠ 0`.

Rewrite using `[hP]`. Use `mul_ne_zero uu.ne_zero ?_` and prove the remaining obligations. Rewrite using `[Ne, Polynomial.coe_eq_zero_iff]`. Conclude with `hE.monic.ne_zero`. Establish `huniq : ∀ (a : Fin d → O) (q : PowerSeries O), ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0`.

Introduce `a q hq i`. Establish `hr0 : (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O) = 0`. Use `eq_zero_of_isDistinguishedAt_mul hI hE (q := (↑uu : PowerSeries O) * q) (hEd ▸ Polynomial.degree_sum_fin_lt a) ?_` and prove the remaining obligations. Rewrite using `[coe_sum_fin, hq, hP]`. Expand and normalize the polynomial expressions, which then agree.

Use `coeff_sum_fin a i` as an intermediate fact. Rewrite `this` using `[hr0, Polynomial.coeff_zero]`. Conclude with `this.symm`. Take `⟨α, β, hαβ⟩` from `Ideal.mem_span_pair.mp hf`. Take `⟨a, ha⟩` from `exists_sum_algHom_mul_X_pow φ d hdiv hkrull α`.

Take `⟨b, hb⟩` from `exists_sum_algHom_mul_X_pow φ d hdiv hkrull β`. Set `i0 : Fin d` to `⟨0, hd⟩`. Set `h : Fin d → PowerSeries O` to `fun i => C c * a i + g * b i - if i = i0 then f else 0`. Establish `e1 : ∑ i, C c * φ (a i) * X ^ (i : ℕ) = C c * α`. Rewrite using `[ha, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `e2 : ∑ i, φ g * φ (b i) * X ^ (i : ℕ) = φ g * β`. Rewrite using `[hb, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Establish `e3 : ∑ i, φ (if i = i0 then f else 0) * X ^ (i : ℕ) = φ f`.

Rewrite using `[Finset.sum_eq_single i0]`. Simplify using `[i0]`. Introduce `j _ hj`. Simplify using `[hj]`. Introduce `hn`.

Conclude with `absurd (Finset.mem_univ _) hn`. Establish `hs : ∑ i, φ (h i) * X ^ (i : ℕ) = 0`. Simplify using `only [h, map_sub, map_add, map_mul, algHom_C, sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Rewrite using `[e1, e2, e3]`. Take the linear combination `hαβ`.

Establish `hz` using `eq_zero_of_sum_algHom_mul_X_pow φ d huniq hP0`. Establish `h0 : h i0 = 0`. Use extensionality with `n`. Rewrite using `[map_zero]`. Conclude with `hz n h hs i0`.

Simplify using `only [h, if_pos rfl, if_true] at h0`. Conclude with `Ideal.mem_span_pair.mpr ⟨a i0, b i0, by linear_combination h0⟩`.
-/
theorem mem_span_of_frobenius_mem_span : Descent := by
  intro O _ _ _ _ ϖ hϖ φ d hd hU c f g hf
  obtain ⟨u, E, hu, hE, hEd, hP⟩ := hU
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  haveI : IsAdicComplete (Ideal.span {ϖ}) O := by rw [← hmax]; infer_instance
  have hI : Ideal.span {ϖ} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    exact hϖ.not_isUnit
  obtain ⟨uu, rfl⟩ := hu
  have hdiv : ∀ F : PowerSeries O, ∃ (q : PowerSeries O) (r : Polynomial O),
      r.degree < d ∧ F = φ X * q + r := by
    intro F
    obtain ⟨q, r, hr, hFq⟩ := exists_div_of_isDistinguishedAt hI hE F
    refine ⟨(↑uu⁻¹ : PowerSeries O) * q, r, hEd ▸ hr, ?_⟩
    rw [hP, hFq]
    have : (↑uu : PowerSeries O) * ↑uu⁻¹ = 1 := Units.mul_inv uu
    linear_combination (-(E : PowerSeries O) * q) * this
  have hPnu : ¬ IsUnit (φ X) := by
    intro hunit
    rw [PowerSeries.isUnit_iff_constantCoeff, hP, map_mul] at hunit
    have h2 := (IsUnit.mul_iff.mp hunit).2
    have hmem : PowerSeries.constantCoeff (E : PowerSeries O) ∈ Ideal.span {ϖ} := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe]
      exact hE.toIsWeaklyEisensteinAt.mem (by omega)
    exact hI (Ideal.eq_top_of_isUnit_mem _ hmem h2)
  have hkrull : ∀ x : PowerSeries O, (∀ N : ℕ, φ X ^ N ∣ x) → x = 0 :=
    fun x hx => eq_zero_of_forall_pow_dvd hPnu hx
  have hP0 : φ X ≠ 0 := by
    rw [hP]
    refine mul_ne_zero uu.ne_zero ?_
    rw [Ne, Polynomial.coe_eq_zero_iff]
    exact hE.monic.ne_zero
  have huniq : ∀ (a : Fin d → O) (q : PowerSeries O),
      ∑ i, C (a i) * X ^ (i : ℕ) = φ X * q → ∀ i, a i = 0 := by
    intro a q hq i
    have hr0 : (∑ i : Fin d, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ) : Polynomial O) = 0 := by
      refine eq_zero_of_isDistinguishedAt_mul hI hE (q := (↑uu : PowerSeries O) * q)
        (hEd ▸ Polynomial.degree_sum_fin_lt a) ?_
      rw [coe_sum_fin, hq, hP]
      ring
    have := coeff_sum_fin a i
    rw [hr0, Polynomial.coeff_zero] at this
    exact this.symm
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hf
  obtain ⟨a, ha⟩ := exists_sum_algHom_mul_X_pow φ d hdiv hkrull α
  obtain ⟨b, hb⟩ := exists_sum_algHom_mul_X_pow φ d hdiv hkrull β
  let i0 : Fin d := ⟨0, hd⟩
  let h : Fin d → PowerSeries O := fun i => C c * a i + g * b i - if i = i0 then f else 0
  have e1 : ∑ i, C c * φ (a i) * X ^ (i : ℕ) = C c * α := by
    rw [ha, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, φ g * φ (b i) * X ^ (i : ℕ) = φ g * β := by
    rw [hb, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, φ (if i = i0 then f else 0) * X ^ (i : ℕ) = φ f := by
    rw [Finset.sum_eq_single i0]
    · simp [i0]
    · intro j _ hj
      simp [hj]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  have hs : ∑ i, φ (h i) * X ^ (i : ℕ) = 0 := by
    simp only [h, map_sub, map_add, map_mul, algHom_C, sub_mul, add_mul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
    rw [e1, e2, e3]
    linear_combination hαβ
  have hz := eq_zero_of_sum_algHom_mul_X_pow φ d huniq hP0
  have h0 : h i0 = 0 := by
    ext n
    rw [map_zero]
    exact hz n h hs i0
  simp only [h, if_pos rfl, if_true] at h0
  exact Ideal.mem_span_pair.mpr ⟨a i0, b i0, by linear_combination h0⟩

end Formalism.ExponentWindows
