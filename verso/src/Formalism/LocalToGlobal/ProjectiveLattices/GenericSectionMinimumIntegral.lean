import Formalism.LocalToGlobal.ProjectiveLattices.SumT0MulRatioEqOne
import Formalism.LocalToGlobal.ProjectiveLattices.TotalDegreePderivLt
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.GenericSectionMinimum

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain IsLocalRing

/- English proof (translation)
Set `S` to `(IsArtinianRing.setOfPred_isMaximal_finite A).toFinset`. Set `q : Ideal A → Polynomial R` to `fun m => if hm : m.IsMaximal then Classical.choose (h m hm) else 1`. Establish `hq : ∀ m, (q m).Monic` using `fun m => by`. Distinguish the cases in `hm : m.IsMaximal`. Simplify using `only [q, dif_pos hm]`.

Conclude with `(Classical.choose_spec (h m hm)).1`. Simplify using `only [q, dif_neg hm]`. Conclude with `Polynomial.monic_one`. Establish `hqm : ∀ m, m.IsMaximal → Polynomial.aeval x (q m) ∈ m` using `fun m hm => by`. Establish `hqe : q m = Classical.choose (h m hm)` using `dif_pos hm`.

Use `set p := Classical.choose (h m hm) with hp`. Establish `e : Polynomial.eval₂ (algebraMap R (A ⧸ m)) (Ideal.Quotient.mk m x) p = 0` using `(Classical.choose_spec (h m hm)).2`. Rewrite using `[hqe, ← Ideal.Quotient.eq_zero_iff_mem]`. Establish `e2` using `Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ R m) x p`. Rewrite `e2` using `[Ideal.Quotient.mkₐ_eq_mk, Polynomial.aeval_def]`.

Rewrite using `[← e2]`. Conclude with `e`. Set `Pp` to `∏ m ∈ S, q m`. Establish `hP : Pp.Monic` using `Polynomial.monic_prod_of_monic _ _ fun m _ => hq m`. Establish `hmem : ∀ J : Ideal A, J.IsPrime → Polynomial.aeval x Pp ∈ J`.

Introduce `J hJ`. Use `haveI := hJ`. Establish `hJm : J.IsMaximal` using `IsArtinianRing.isMaximal_of_isPrime J`. Establish `hJS : J ∈ S` using `(Set.Finite.mem_toFinset _).2 hJm`. Conclude with `Ideal.mem_of_dvd _ (map_dvd _ (Finset.dvd_prod_of_mem q hJS)) (hqm J hJm)`.

Take `⟨n, hn⟩` from `(nilpotent_iff_mem_prime).2 hmem`. Use `⟨Pp ^ n, hP.pow n, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_def, map_pow, hn]`.
-/
theorem isIntegral_of_quot {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [IsArtinianRing A] (x : A)
    (h : ∀ m : Ideal A, m.IsMaximal → IsIntegral R (Ideal.Quotient.mk m x)) : IsIntegral R x := by
  classical
  let S := (IsArtinianRing.setOfPred_isMaximal_finite A).toFinset
  let q : Ideal A → Polynomial R := fun m => if hm : m.IsMaximal then Classical.choose (h m hm) else 1
  have hq : ∀ m, (q m).Monic := fun m => by
    by_cases hm : m.IsMaximal
    · simp only [q, dif_pos hm]; exact (Classical.choose_spec (h m hm)).1
    · simp only [q, dif_neg hm]; exact Polynomial.monic_one
  have hqm : ∀ m, m.IsMaximal → Polynomial.aeval x (q m) ∈ m := fun m hm => by
    have hqe : q m = Classical.choose (h m hm) := dif_pos hm
    set p := Classical.choose (h m hm) with hp
    have e : Polynomial.eval₂ (algebraMap R (A ⧸ m)) (Ideal.Quotient.mk m x) p = 0 :=
      (Classical.choose_spec (h m hm)).2
    rw [hqe, ← Ideal.Quotient.eq_zero_iff_mem]
    have e2 := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ R m) x p
    rw [Ideal.Quotient.mkₐ_eq_mk, Polynomial.aeval_def] at e2
    rw [← e2]
    exact e
  let Pp := ∏ m ∈ S, q m
  have hP : Pp.Monic := Polynomial.monic_prod_of_monic _ _ fun m _ => hq m
  have hmem : ∀ J : Ideal A, J.IsPrime → Polynomial.aeval x Pp ∈ J := by
    intro J hJ
    haveI := hJ
    have hJm : J.IsMaximal := IsArtinianRing.isMaximal_of_isPrime J
    have hJS : J ∈ S := (Set.Finite.mem_toFinset _).2 hJm
    exact Ideal.mem_of_dvd _ (map_dvd _ (Finset.dvd_prod_of_mem q hJS)) (hqm J hJm)
  obtain ⟨n, hn⟩ := (nilpotent_iff_mem_prime).2 hmem
  refine ⟨Pp ^ n, hP.pow n, ?_⟩
  rw [← Polynomial.aeval_def, map_pow, hn]

section Inst

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO))
  {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

/- English proof (translation)
Use `haveI := hfd`. Use `haveI : CharZero (X.Kl la) := charZero_of_injective_algebraMap (algebraMap B.KO (X.Kl la)).injective`. Use `haveI : CharZero (Kp X la N) := charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective`. Use `haveI : IsArtinianRing (OsK X la w) := IsArtinianRing.of_finite (Kp X la N) (OsK X la w)`. Establish `hirr : Irreducible (unif X la)` using `Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))`.

Establish `hirrO : Irreducible (unifO X la N)` using `Op.irreducible_map X la N hirr`. Use `haveI : Algebra.IsIntegral (Kp X la N) (OsK X la w) := Algebra.IsIntegral.of_finite _ _`. Establish `hunif : IsUnif (OsK X la w) (unifO X la N)` using `isUnif_of_field (Kp X la N) hirrO`. Establish `hu : ∀ n : ℕ, 0 < n → IsUnit (n : OsK X la w)` using `fun n hn => by`. Rewrite using `[← map_natCast (algebraMap (Kp X la N) (OsK X la w)) n]`.

Conclude with `(IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')).map _`. Establish `hδO : ∀ l : Fin N, ∃ δ : OsK X la w → OsK X la w, IsDer δ ∧ ∀ x, δ (toOsK X la w x) = toOsK X la w (dF X la w l x)` using `fun l => exists_derOsK X la w l`. Use `choose δO hδOd hδOv using hδO`. Use `isIntegral_of_quot _ fun m hm => ?_` and prove the remaining obligations. Use `haveI : m.IsMaximal := hm`.

Use `letI : Field (OsK X la w ⧸ m) := Ideal.Quotient.field m`. Set `π : OsK X la w →+* OsK X la w ⧸ m` to `Ideal.Quotient.mk m`. Establish `hδm : ∀ l : Fin N, ∃ δ : OsK X la w ⧸ m → OsK X la w ⧸ m, IsDer δ ∧ ∀ x, δ (π x) = π (δO l x)` using `fun l => (hδOd l).quot m (fun x hx => (hδOd l).mem_max hu m hx)`. Use `choose δ hδ hδv using hδm`. Assume the negation of the conclusion as `hni`.

Take `⟨V, hRV, hxV⟩` from `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn (R := (integralClosure (Op X la N) (OsK X la w ⧸ m)).toSubring) (x := π (toOsK X la w (xr X la w k))) (fun h => hni h)`. Establish `hIV : ∀ z : OsK X la w ⧸ m, IsIntegral (Op X la N) z → z ∈ V` using `fun z hz => hRV hz`. Establish `hOV : ∀ o : Op X la N, algebraMap (Op X la N) (OsK X la w ⧸ m) o ∈ V` using `fun o => hIV _ isIntegral_algebraMap`. Establish `hOle : ∀ o : Op X la N, V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) o) ≤ 1` using `fun o => (V.valuation_le_one_iff _).2 (hOV o)`. Establish `hϖ : V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) (unifO X la N)) < 1`.

Use `lt_of_le_of_ne (hOle _) fun h1 => hxV ?_` and prove the remaining obligations. Take `⟨n, hn⟩` from `hunif.denom (toOsK X la w (xr X la w k))`. Establish `hint : IsIntegral (Op X la N) (π (unifO X la N ^ n • toOsK X la w (xr X la w k)))` using `(show IsIntegral (Op X la N) (unifO X la N ^ n • toOsK X la w (xr X la w k)) from hn).map (Ideal.Quotient.mkₐ (Op X la N) m)`. Establish `hmem` using `hIV _ hint`. Rewrite `hmem` using `[Algebra.smul_def, map_mul]`.

Rewrite `hmem`, the goal using `[← V.valuation_le_one_iff]`. Establish `e : π (algebraMap (Op X la N) (OsK X la w) (unifO X la N ^ n)) = algebraMap (Op X la N) (OsK X la w ⧸ m) (unifO X la N) ^ n`. Rewrite using `[map_pow, map_pow]`. Both sides reduce to the same expression. Rewrite `hmem` using `[e, Valuation.map_mul, Valuation.map_pow, h1, one_pow, one_mul]`. Then use the resulting hypothesis.

Establish `hmax : ∀ a ∈ maximalIdeal (Op X la N), V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) a) < 1`. Introduce `a ha`. Rewrite `ha` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirrO, Ideal.mem_span_singleton']`. Take `⟨b, rfl⟩` from `ha`. Rewrite using `[map_mul, Valuation.map_mul]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hunitV : ∀ u : Op X la N, IsUnit u → V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) u) = 1`. Introduce `u hu'`. Take `⟨u', hu''⟩` from `hu'.exists_right_inv`. Establish `e` using `congrArg (fun z => V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) z)) hu''`.

Simplify using `only [map_mul, Valuation.map_mul, map_one, Valuation.map_one] at e`. Use `le_antisymm (hOle u) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `letI : Algebra (X.Kl la) (OsK X la w ⧸ m) := ((algebraMap (Kp X la N) (OsK X la w ⧸ m)).comp (algebraMap (X.Kl la) (Kp X la N))).toAlgebra`. Set `T : Fin (WeightFamilies.dimY D j + 1) × Fin N → OsK X la w ⧸ m` to `fun q => algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (Tv X la N q))`.

Set `y : Fin N → OsK X la w ⧸ m` to `fun k => π (toOsK X la w (xr X la w k))`. Establish `hKF : ∀ z : Kp X la N, algebraMap (Kp X la N) (OsK X la w ⧸ m) z = π (toOsK X la w (algebraMap (Kp X la N) (Frac0 X la w) z))` using `fun z => rfl`. Establish `hδK : ∀ l (z : Kp X la N), δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) z) = algebraMap (Kp X la N) (OsK X la w ⧸ m) (dK X la N (0, l) z)`. Introduce `l z`. Rewrite using `[hKF, hδv, hδOv, dF_algebraMap, ← hKF]`.

Establish `hev : ∀ Pp : MvPolynomial (Fin (WeightFamilies.dimY D j + 1) × Fin N) (X.Ol la), MvPolynomial.aeval T (MvPolynomial.map (algebraMap (X.Ol la) (X.Kl la)) Pp) = algebraMap (Op X la N) (OsK X la w ⧸ m) (algebraMap (Pol X la N) (Op X la N) Pp)`. Introduce `Pp`. Proceed by induction on `Pp using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[MvPolynomial.map_C, MvPolynomial.aeval_C]`.

Use `show algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) a)) = algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.C a)))`. Rewrite using `[← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N), ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Op X la N), ← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N)]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p q hp`. Simplify using `only [map_mul, hp, MvPolynomial.map_X, MvPolynomial.aeval_X]`.

Both sides reduce to the same expression. Establish `htow : ∀ a : X.Ol la, algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) a) = algebraMap (Op X la N) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (Op X la N) a)`. Introduce `a`. Use `show algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) a)) = algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (algebraMap (X.Ol la) (Op X la N) a))`. Rewrite using `[← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N), ← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N)]`.

Establish `hmaxOl : ∀ a : X.Ol la, a ∈ maximalIdeal (X.Ol la) → V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) a)) < 1`. Introduce `a ha`. Rewrite using `[htow]`. Use `hmax _ ((mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu))` and prove the remaining obligations. Establish `hKlO : ∀ c : X.Kl la, V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) ≤ 1 → c ∈ Set.range (algebraMap (X.Ol la) (X.Kl la))`.

Introduce `c hc`. Distinguish the cases in `hc0 : c = 0`. Conclude with `⟨0, by rw [hc0, map_zero]⟩`. Break down `(X.Ol la).mem_or_inv_mem c with hcO | hcO` into its components or cases. Conclude with `⟨⟨c, hcO⟩, rfl⟩`.

Distinguish the cases in `hu : IsUnit (⟨c⁻¹, hcO⟩ : X.Ol la)`. Take `⟨v', hv'⟩` from `hu.exists_right_inv`. Establish `e : (c⁻¹ : X.Kl la) * (v' : X.Kl la) = 1`. Use `congrArg (fun z : X.Ol la => (z : X.Kl la)) hv'` as an intermediate fact. Simplify using `using this`.

Use `⟨v', ?_⟩` and prove the remaining obligations. Use `show (v' : X.Kl la) = c`. Combine the equalities or inequalities in the displayed calculation. It suffices to derive a contradiction. Establish `hlt` using `hmaxOl ⟨c⁻¹, hcO⟩ ((mem_maximalIdeal _).2 hu)`.

Establish `e : V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) * V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) ⟨c⁻¹, hcO⟩)) = 1`. Rewrite using `[← Valuation.map_mul, ← map_mul]`. Use `show V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (c * c⁻¹)) = 1`. Rewrite using `[mul_inv_cancel₀ hc0, map_one, Valuation.map_one]`. Establish `hlt2 : V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) * V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) ⟨c⁻¹, hcO⟩)) < 1`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `absurd e (ne_of_lt hlt2)`. Establish `hG : ∀ Q : MvPolynomial (Fin (WeightFamilies.dimY D j + 1) × Fin N) (X.Kl la), (∀ α, V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (Q.coeff α)) ≤ 1) → (∃ α, V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (Q.coeff α)) = 1) → V.valuation (MvPolynomial.aeval T Q) = 1`. Introduce and unpack `Q hle ⟨α, hα⟩`. Choose the witnesses or unpack the hypotheses as in `⟨Pp, rfl⟩ : Q ∈ Set.range (MvPolynomial.map (algebraMap (X.Ol la) (X.Kl la))) := by`.

Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`. Introduce `c hc`. Take `⟨β, -, rfl⟩` from `MvPolynomial.mem_coeffs_iff.mp hc`. Conclude with `hKlO _ (hle β)`. Rewrite using `[hev]`.

Apply `hunitV` to reduce the goal to its premises. Rewrite using `[IsLocalization.AtPrime.isUnit_to_map_iff (Op X la N) (gI X la N)]`. Use `show Pp ∉ gI X la N`. Introduce `hg`. Rewrite `hg` using `[gI, Formalism.DV.gaussIdeal, MvPolynomial.mem_map_C_iff]`.

Rewrite `hα` using `[MvPolynomial.coeff_map]`. Conclude with `(hmaxOl _ (hg α)).ne hα`. Establish `hδ0 : ∀ l k, δ l (T (0, k)) = if k = l then 1 else 0`. Introduce `l k`. Use `show δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k)))) = _`.

Rewrite using `[hδK, dK_Tv]`. Distinguish the cases in `hk : k = l`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h => hk (Prod.mk.inj h).2), if_neg hk, map_zero]`.

Establish `hδs : ∀ l (i : Fin (WeightFamilies.dimY D j)) k, δ l (T (i.succ, k)) = 0`. Introduce `l i k`. Use `show δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i.succ, k)))) = 0`. Rewrite using `[hδK, dK_Tv, if_neg (fun h => Fin.succ_ne_zero i (Prod.mk.inj h).1), map_zero]`. Establish `hδKl : ∀ l (c : X.Kl la), δ l (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) = 0`.

Introduce `l c`. Use `show δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (X.Kl la) (Kp X la N) c)) = 0`. Rewrite using `[hδK, dK_Kl, map_zero]`. Establish `hδy : ∀ l k, δ l (y k) = -(y k * y l)`. Introduce `l k`.

Use `show δ l (π (toOsK X la w (xr X la w k))) = _`. Rewrite using `[hδv, hδOv, dF_xr, map_neg, map_mul, map_neg, map_mul]`. Establish `h1 : ∑ k, T (0, k) * y k = 1`. Use `congrArg (fun z => π (toOsK X la w z)) (sum_T0_mul_ratio_eq_one X la w)` as an intermediate fact. Simplify using `only [map_sum, map_mul, map_one] at this`.

Conclude with `this`. Establish `halg : Algebra.IsAlgebraic (Algebra.adjoin (X.Kl la) (Set.range T)) (OsK X la w ⧸ m)` using `by set Sa := Algebra.adjoin (X.Kl la) (Set.range T) with hSa`. Establish `hmemS : ∀ Q : MvPolynomial (Fin (WeightFamilies.dimY D j + 1) × Fin N) (X.Kl la), MvPolynomial.aeval T Q ∈ Sa`. Introduce `Q`. Proceed by induction on `Q using MvPolynomial.induction_on with`.

Consider the case `C c => rw [MvPolynomial.aeval_C]`. Conclude with `Sa.algebraMap_mem c`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `Sa.add_mem hp hq`. Consider the case `mul_X p q hp => rw [map_mul, MvPolynomial.aeval_X]`.

Conclude with `Sa.mul_mem hp (Algebra.subset_adjoin ⟨q, rfl⟩)`. Use `letI : Algebra (Pol X la N) (OsK X la w ⧸ m) := ((algebraMap (Op X la N) (OsK X la w ⧸ m)).comp (algebraMap (Pol X la N) (Op X la N))).toAlgebra`. Use `haveI : IsScalarTower (Pol X la N) (Op X la N) (OsK X la w ⧸ m) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hPS : ∀ Pp : Pol X la N, algebraMap (Pol X la N) (OsK X la w ⧸ m) Pp ∈ Sa` using `fun Pp => by show algebraMap (Op X la N) (OsK X la w ⧸ m) (algebraMap (Pol X la N) (Op X la N) Pp) ∈ Sa`. Rewrite using `[← hev]`.

Conclude with `hmemS _`. Establish `hinj : Function.Injective (algebraMap (Pol X la N) (OsK X la w ⧸ m))` using `by show Function.Injective ((algebraMap (Kp X la N) (OsK X la w ⧸ m)).comp ((algebraMap (Op X la N) (Kp X la N)).comp (algebraMap (Pol X la N) (Op X la N))))`. Conclude with `(algebraMap (Kp X la N) _).injective.comp ((IsFractionRing.injective _ _).comp (IsLocalization.injective (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors))`. Set `ψ : Pol X la N →+* Sa` to `(algebraMap (Pol X la N) (OsK X la w ⧸ m)).codRestrict Sa hPS`. Use `haveI : Algebra.IsIntegral (Kp X la N) (OsK X la w ⧸ m) := Algebra.IsIntegral.of_finite _ _`.

Use `⟨fun f => ?_⟩` and prove the remaining obligations. Establish `hfK : IsAlgebraic (Kp X la N) f` using `(Algebra.IsIntegral.isIntegral f).isAlgebraic`. Establish `hfO : IsAlgebraic (Op X la N) f` using `(IsFractionRing.isAlgebraic_iff (A := Op X la N) (K := Kp X la N) (C := OsK X la w ⧸ m)).2 hfK`. Take `⟨p, hp0, hp⟩` from `hfO`. Take `⟨⟨b, hb⟩, hbp⟩` from `IsLocalization.integerNormalization_map_to_map (gI X la N).primeCompl p`.

Establish `hp'0 : IsLocalization.integerNormalization (gI X la N).primeCompl p ≠ 0`. Introduce `h0`. Rewrite `hbp` using `[h0, Polynomial.map_zero]`. Establish `hb' : algebraMap (Pol X la N) (Op X la N) b ≠ 0` using `(IsLocalization.map_units (Op X la N) (⟨b, hb⟩ : (gI X la N).primeCompl)).ne_zero`. Rewrite `hbp` using `[← algebraMap_smul (Op X la N) b p]`.

Conclude with `hp0 ((smul_eq_zero.mp hbp.symm).resolve_left hb')`. Use `⟨(IsLocalization.integerNormalization (gI X la N).primeCompl p).map ψ, (Polynomial.map_ne_zero_iff (fun a b' hab => hinj (congrArg Subtype.val hab))).2 hp'0, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map]`. Establish `e : (algebraMap Sa (OsK X la w ⧸ m)).comp ψ = algebraMap (Pol X la N) (OsK X la w ⧸ m)` using `RingHom.ext fun _ => rfl`. Rewrite using `[e, ← Polynomial.aeval_def]`.

Conclude with `IsLocalization.integerNormalization_aeval_eq_zero (M := (gI X la N).primeCompl) p hp`. Conclude with `hxV (gauss_direct (WeightFamilies.dimY D j) N T y δ hδ hδKl hδ0 hδs hδy h1 halg V hG k)`.
-/
theorem isIntegral_xr (hfd : FiniteDimensional (Kp X la N) (OsK X la w)) (k : Fin N) :
    IsIntegral (Op X la N) (toOsK X la w (xr X la w k)) := by
  classical
  haveI := hfd
  haveI : CharZero (X.Kl la) := charZero_of_injective_algebraMap (algebraMap B.KO (X.Kl la)).injective
  haveI : CharZero (Kp X la N) := charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective
  haveI : IsArtinianRing (OsK X la w) := IsArtinianRing.of_finite (Kp X la N) (OsK X la w)
  have hirr : Irreducible (unif X la) := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))
  have hirrO : Irreducible (unifO X la N) := Op.irreducible_map X la N hirr
  haveI : Algebra.IsIntegral (Kp X la N) (OsK X la w) := Algebra.IsIntegral.of_finite _ _
  have hunif : IsUnif (OsK X la w) (unifO X la N) := isUnif_of_field (Kp X la N) hirrO
  have hu : ∀ n : ℕ, 0 < n → IsUnit (n : OsK X la w) := fun n hn => by
    rw [← map_natCast (algebraMap (Kp X la N) (OsK X la w)) n]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 hn.ne')).map _

  have hδO : ∀ l : Fin N, ∃ δ : OsK X la w → OsK X la w, IsDer δ ∧
      ∀ x, δ (toOsK X la w x) = toOsK X la w (dF X la w l x) := fun l => exists_derOsK X la w l
  choose δO hδOd hδOv using hδO
  refine isIntegral_of_quot _ fun m hm => ?_
  haveI : m.IsMaximal := hm
  letI : Field (OsK X la w ⧸ m) := Ideal.Quotient.field m
  let π : OsK X la w →+* OsK X la w ⧸ m := Ideal.Quotient.mk m

  have hδm : ∀ l : Fin N, ∃ δ : OsK X la w ⧸ m → OsK X la w ⧸ m, IsDer δ ∧ ∀ x, δ (π x) = π (δO l x) :=
    fun l => (hδOd l).quot m (fun x hx => (hδOd l).mem_max hu m hx)
  choose δ hδ hδv using hδm
  by_contra hni

  obtain ⟨V, hRV, hxV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure (Op X la N) (OsK X la w ⧸ m)).toSubring) (x := π (toOsK X la w (xr X la w k))) (fun h => hni h)
  have hIV : ∀ z : OsK X la w ⧸ m, IsIntegral (Op X la N) z → z ∈ V := fun z hz => hRV hz
  have hOV : ∀ o : Op X la N, algebraMap (Op X la N) (OsK X la w ⧸ m) o ∈ V := fun o => hIV _ isIntegral_algebraMap
  have hOle : ∀ o : Op X la N, V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) o) ≤ 1 := fun o =>
    (V.valuation_le_one_iff _).2 (hOV o)

  have hϖ : V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) (unifO X la N)) < 1 := by
    refine lt_of_le_of_ne (hOle _) fun h1 => hxV ?_
    obtain ⟨n, hn⟩ := hunif.denom (toOsK X la w (xr X la w k))
    have hint : IsIntegral (Op X la N) (π (unifO X la N ^ n • toOsK X la w (xr X la w k))) :=
      (show IsIntegral (Op X la N) (unifO X la N ^ n • toOsK X la w (xr X la w k)) from hn).map
        (Ideal.Quotient.mkₐ (Op X la N) m)
    have hmem := hIV _ hint
    rw [Algebra.smul_def, map_mul] at hmem
    rw [← V.valuation_le_one_iff] at hmem ⊢
    have e : π (algebraMap (Op X la N) (OsK X la w) (unifO X la N ^ n)) =
        algebraMap (Op X la N) (OsK X la w ⧸ m) (unifO X la N) ^ n := by
      rw [map_pow, map_pow]; rfl
    rwa [e, Valuation.map_mul, Valuation.map_pow, h1, one_pow, one_mul] at hmem
  have hmax : ∀ a ∈ maximalIdeal (Op X la N), V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) a) < 1 := by
    intro a ha
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hirrO, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, Valuation.map_mul]
    calc V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) b) *
          V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) (unifO X la N))
        ≤ 1 * V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) (unifO X la N)) := by gcongr; exact hOle b
      _ < 1 := by rw [one_mul]; exact hϖ
  have hunitV : ∀ u : Op X la N, IsUnit u → V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) u) = 1 := by
    intro u hu'
    obtain ⟨u', hu''⟩ := hu'.exists_right_inv
    have e := congrArg (fun z => V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) z)) hu''
    simp only [map_mul, Valuation.map_mul, map_one, Valuation.map_one] at e
    refine le_antisymm (hOle u) ?_
    calc (1 : _) = V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) u) *
          V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) u') := e.symm
      _ ≤ V.valuation (algebraMap (Op X la N) (OsK X la w ⧸ m) u) * 1 := by gcongr; exact hOle u'
      _ = _ := mul_one _

  letI : Algebra (X.Kl la) (OsK X la w ⧸ m) :=
    ((algebraMap (Kp X la N) (OsK X la w ⧸ m)).comp (algebraMap (X.Kl la) (Kp X la N))).toAlgebra
  let T : Fin (WeightFamilies.dimY D j + 1) × Fin N → OsK X la w ⧸ m := fun q =>
    algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (Tv X la N q))
  let y : Fin N → OsK X la w ⧸ m := fun k => π (toOsK X la w (xr X la w k))
  have hKF : ∀ z : Kp X la N, algebraMap (Kp X la N) (OsK X la w ⧸ m) z =
      π (toOsK X la w (algebraMap (Kp X la N) (Frac0 X la w) z)) := fun z => rfl
  have hδK : ∀ l (z : Kp X la N), δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) z) =
      algebraMap (Kp X la N) (OsK X la w ⧸ m) (dK X la N (0, l) z) := by
    intro l z
    rw [hKF, hδv, hδOv, dF_algebraMap, ← hKF]
  have hev : ∀ Pp : MvPolynomial (Fin (WeightFamilies.dimY D j + 1) × Fin N) (X.Ol la),
      MvPolynomial.aeval T (MvPolynomial.map (algebraMap (X.Ol la) (X.Kl la)) Pp) =
        algebraMap (Op X la N) (OsK X la w ⧸ m) (algebraMap (Pol X la N) (Op X la N) Pp) := by
    intro Pp
    induction Pp using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.map_C, MvPolynomial.aeval_C]
      show algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) a)) =
        algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N)
          (algebraMap (Pol X la N) (Op X la N) (MvPolynomial.C a)))
      rw [← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N), ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply (X.Ol la) (Pol X la N) (Op X la N),
        ← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N)]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p q hp =>
      simp only [map_mul, hp, MvPolynomial.map_X, MvPolynomial.aeval_X]
      rfl
  have htow : ∀ a : X.Ol la, algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) a) =
      algebraMap (Op X la N) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (Op X la N) a) := by
    intro a
    show algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (X.Kl la) (Kp X la N) (algebraMap (X.Ol la) (X.Kl la) a)) =
      algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (algebraMap (X.Ol la) (Op X la N) a))
    rw [← IsScalarTower.algebraMap_apply (X.Ol la) (X.Kl la) (Kp X la N),
      ← IsScalarTower.algebraMap_apply (X.Ol la) (Op X la N) (Kp X la N)]
  have hmaxOl : ∀ a : X.Ol la, a ∈ maximalIdeal (X.Ol la) →
      V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) a)) < 1 := by
    intro a ha
    rw [htow]
    refine hmax _ ((mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit _ _ hu))
  have hKlO : ∀ c : X.Kl la, V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) ≤ 1 →
      c ∈ Set.range (algebraMap (X.Ol la) (X.Kl la)) := by
    intro c hc
    by_cases hc0 : c = 0
    · exact ⟨0, by rw [hc0, map_zero]⟩
    rcases (X.Ol la).mem_or_inv_mem c with hcO | hcO
    · exact ⟨⟨c, hcO⟩, rfl⟩
    · by_cases hu : IsUnit (⟨c⁻¹, hcO⟩ : X.Ol la)
      · obtain ⟨v', hv'⟩ := hu.exists_right_inv
        have e : (c⁻¹ : X.Kl la) * (v' : X.Kl la) = 1 := by
          have := congrArg (fun z : X.Ol la => (z : X.Kl la)) hv'
          simpa using this
        refine ⟨v', ?_⟩
        show (v' : X.Kl la) = c
        calc (v' : X.Kl la) = c * (c⁻¹ * v') := by rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
          _ = c := by rw [e, mul_one]
      · exfalso
        have hlt := hmaxOl ⟨c⁻¹, hcO⟩ ((mem_maximalIdeal _).2 hu)
        have e : V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) *
            V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) ⟨c⁻¹, hcO⟩)) = 1 := by
          rw [← Valuation.map_mul, ← map_mul]
          show V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (c * c⁻¹)) = 1
          rw [mul_inv_cancel₀ hc0, map_one, Valuation.map_one]
        have hlt2 : V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) *
            V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) ⟨c⁻¹, hcO⟩)) < 1 := by
          calc V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) *
              V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) ⟨c⁻¹, hcO⟩))
              ≤ 1 * V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (algebraMap (X.Ol la) (X.Kl la) ⟨c⁻¹, hcO⟩)) := by
                gcongr
            _ < 1 := by rw [one_mul]; exact hlt
        exact absurd e (ne_of_lt hlt2)
  have hG : ∀ Q : MvPolynomial (Fin (WeightFamilies.dimY D j + 1) × Fin N) (X.Kl la),
      (∀ α, V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (Q.coeff α)) ≤ 1) →
      (∃ α, V.valuation (algebraMap (X.Kl la) (OsK X la w ⧸ m) (Q.coeff α)) = 1) →
      V.valuation (MvPolynomial.aeval T Q) = 1 := by
    rintro Q hle ⟨α, hα⟩
    obtain ⟨Pp, rfl⟩ : Q ∈ Set.range (MvPolynomial.map (algebraMap (X.Ol la) (X.Kl la))) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨β, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
      exact hKlO _ (hle β)
    rw [hev]
    apply hunitV
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Op X la N) (gI X la N)]
    show Pp ∉ gI X la N
    intro hg
    rw [gI, Formalism.DV.gaussIdeal, MvPolynomial.mem_map_C_iff] at hg
    rw [MvPolynomial.coeff_map] at hα
    exact (hmaxOl _ (hg α)).ne hα
  have hδ0 : ∀ l k, δ l (T (0, k)) = if k = l then 1 else 0 := by
    intro l k
    show δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (0, k)))) = _
    rw [hδK, dK_Tv]
    by_cases hk : k = l
    · subst hk; simp
    · rw [if_neg (fun h => hk (Prod.mk.inj h).2), if_neg hk, map_zero]
  have hδs : ∀ l (i : Fin (WeightFamilies.dimY D j)) k, δ l (T (i.succ, k)) = 0 := by
    intro l i k
    show δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (Op X la N) (Kp X la N) (Tv X la N (i.succ, k)))) = 0
    rw [hδK, dK_Tv, if_neg (fun h => Fin.succ_ne_zero i (Prod.mk.inj h).1), map_zero]
  have hδKl : ∀ l (c : X.Kl la), δ l (algebraMap (X.Kl la) (OsK X la w ⧸ m) c) = 0 := by
    intro l c
    show δ l (algebraMap (Kp X la N) (OsK X la w ⧸ m) (algebraMap (X.Kl la) (Kp X la N) c)) = 0
    rw [hδK, dK_Kl, map_zero]
  have hδy : ∀ l k, δ l (y k) = -(y k * y l) := by
    intro l k
    show δ l (π (toOsK X la w (xr X la w k))) = _
    rw [hδv, hδOv, dF_xr, map_neg, map_mul, map_neg, map_mul]
  have h1 : ∑ k, T (0, k) * y k = 1 := by
    have := congrArg (fun z => π (toOsK X la w z)) (sum_T0_mul_ratio_eq_one X la w)
    simp only [map_sum, map_mul, map_one] at this
    exact this
  have halg : Algebra.IsAlgebraic (Algebra.adjoin (X.Kl la) (Set.range T)) (OsK X la w ⧸ m) := by
    set Sa := Algebra.adjoin (X.Kl la) (Set.range T) with hSa
    have hmemS : ∀ Q : MvPolynomial (Fin (WeightFamilies.dimY D j + 1) × Fin N) (X.Kl la), MvPolynomial.aeval T Q ∈ Sa := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C c => rw [MvPolynomial.aeval_C]; exact Sa.algebraMap_mem c
      | add p q hp hq => rw [map_add]; exact Sa.add_mem hp hq
      | mul_X p q hp => rw [map_mul, MvPolynomial.aeval_X]; exact Sa.mul_mem hp (Algebra.subset_adjoin ⟨q, rfl⟩)
    letI : Algebra (Pol X la N) (OsK X la w ⧸ m) :=
      ((algebraMap (Op X la N) (OsK X la w ⧸ m)).comp (algebraMap (Pol X la N) (Op X la N))).toAlgebra
    haveI : IsScalarTower (Pol X la N) (Op X la N) (OsK X la w ⧸ m) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hPS : ∀ Pp : Pol X la N, algebraMap (Pol X la N) (OsK X la w ⧸ m) Pp ∈ Sa := fun Pp => by
      show algebraMap (Op X la N) (OsK X la w ⧸ m) (algebraMap (Pol X la N) (Op X la N) Pp) ∈ Sa
      rw [← hev]
      exact hmemS _
    have hinj : Function.Injective (algebraMap (Pol X la N) (OsK X la w ⧸ m)) := by
      show Function.Injective ((algebraMap (Kp X la N) (OsK X la w ⧸ m)).comp
        ((algebraMap (Op X la N) (Kp X la N)).comp (algebraMap (Pol X la N) (Op X la N))))
      exact (algebraMap (Kp X la N) _).injective.comp ((IsFractionRing.injective _ _).comp
        (IsLocalization.injective (Op X la N) (gI X la N).primeCompl_le_nonZeroDivisors))
    let ψ : Pol X la N →+* Sa := (algebraMap (Pol X la N) (OsK X la w ⧸ m)).codRestrict Sa hPS
    haveI : Algebra.IsIntegral (Kp X la N) (OsK X la w ⧸ m) := Algebra.IsIntegral.of_finite _ _
    refine ⟨fun f => ?_⟩
    have hfK : IsAlgebraic (Kp X la N) f := (Algebra.IsIntegral.isIntegral f).isAlgebraic
    have hfO : IsAlgebraic (Op X la N) f :=
      (IsFractionRing.isAlgebraic_iff (A := Op X la N) (K := Kp X la N) (C := OsK X la w ⧸ m)).2 hfK
    obtain ⟨p, hp0, hp⟩ := hfO
    obtain ⟨⟨b, hb⟩, hbp⟩ := IsLocalization.integerNormalization_map_to_map (gI X la N).primeCompl p
    have hp'0 : IsLocalization.integerNormalization (gI X la N).primeCompl p ≠ 0 := by
      intro h0
      rw [h0, Polynomial.map_zero] at hbp
      have hb' : algebraMap (Pol X la N) (Op X la N) b ≠ 0 :=
        (IsLocalization.map_units (Op X la N) (⟨b, hb⟩ : (gI X la N).primeCompl)).ne_zero
      rw [← algebraMap_smul (Op X la N) b p] at hbp
      exact hp0 ((smul_eq_zero.mp hbp.symm).resolve_left hb')
    refine ⟨(IsLocalization.integerNormalization (gI X la N).primeCompl p).map ψ,
      (Polynomial.map_ne_zero_iff (fun a b' hab => hinj (congrArg Subtype.val hab))).2 hp'0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have e : (algebraMap Sa (OsK X la w ⧸ m)).comp ψ = algebraMap (Pol X la N) (OsK X la w ⧸ m) :=
      RingHom.ext fun _ => rfl
    rw [e, ← Polynomial.aeval_def]
    exact IsLocalization.integerNormalization_aeval_eq_zero (M := (gI X la N).primeCompl) p hp
  exact hxV (gauss_direct (WeightFamilies.dimY D j) N T y δ hδ hδKl hδ0 hδs hδy h1 halg V hG k)

end Inst

/- English proof (translation)
Introduce `hfd hred ζ`. Use `haveI := hfd`. Use `haveI := hred`. Use `haveI : CharZero ((xplus X E hM).Kl la) := charZero_of_injective_algebraMap (algebraMap B.KO ((xplus X E hM).Kl la)).injective`. Use `haveI : CharZero (Kp (xplus X E hM) la G.N) := charZero_of_injective_algebraMap (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N)).injective`.

Use `haveI : IsDVRAt ζ := (integralClosure_dvr' (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)).2 ζ`. Establish `hirr : Irreducible (unif (xplus X E hM) la)` using `Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la))`. Use `haveI : Algebra.IsIntegral (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := Algebra.IsIntegral.of_finite _ _`. Establish `hunif : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N)` using `isUnif_of_field (Kp (xplus X E hM) la G.N) (Op.irreducible_map _ la G.N hirr)`. Establish `hint : ∀ k, toOsK (xplus X E hM) la G.w (wRat G la k) ∈ As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)` using `fun k => isIntegral_xr (xplus X E hM) la G.w hfd k`.

Use `⟨fun k => ord_nonneg ζ hunif (hint k), ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hall`. Use `push Not at hall`. Establish `hmemζ : ∀ k, (⟨_, hint k⟩ : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))) ∈ ζ.asIdeal`. Introduce `k`.

Assume the negation of the conclusion as `hk`. Apply `hall k` to reduce the goal to its premises. Rewrite using `[ord_of_mem ζ hunif (hint k)]`. Establish `hu : IsUnit (algebraMap _ (Loc ζ) (⟨_, hint k⟩ : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))))` using `(IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal _).2 hk`. Establish `h0 : vL ζ ⟨_, hint k⟩ = 0` using `by show Ring.ord (Loc ζ) _ = 0`.

Use `Ring.ord_mul_of_isUnit_left hu (1 : Loc ζ)` as an intermediate fact. Rewrite `this` using `[mul_one, Ring.ord_one]`. Conclude with `this`. Rewrite using `[h0]`. Both sides reduce to the same expression.

Establish `hT : ∀ k, algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (Tv (xplus X E hM) la G.N (0, k))) ∈ As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)` using `fun k => isIntegral_algebraMap (x := Tv (xplus X E hM) la G.N (0, k))`. Set `s : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))` to `∑ k, ⟨_, hT k⟩ * ⟨_, hint k⟩`. Establish `hs1 : s = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (toOsK (xplus X E hM) la G.w) (sum_T0_mul_ratio_eq_one (xplus X E hM) la G.w)` as an intermediate fact.

Simplify using `only [map_sum, map_mul, map_one] at this`. Use `show (As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)).val s = (As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)).val 1`. Rewrite using `[map_sum, map_one]`. Simplify using `only [map_mul]`. Conclude with `this`.

Establish `hsζ : s ∈ ζ.asIdeal` using `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hmemζ k)`. Rewrite `hsζ` using `[hs1]`. Conclude with `ζ.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 hsζ)`.
-/
theorem generic_section_minimum_integral {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X}
    {hM : IntAtExt X E} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (xplus X E hM) ka wL wF)
    (la : HeightOneSpectrum (𝓞 B.KO)) : GenericSectionMinimumIntegral G la := by
  classical
  intro hfd hred ζ
  haveI := hfd
  haveI := hred
  haveI : CharZero ((xplus X E hM).Kl la) :=
    charZero_of_injective_algebraMap (algebraMap B.KO ((xplus X E hM).Kl la)).injective
  haveI : CharZero (Kp (xplus X E hM) la G.N) :=
    charZero_of_injective_algebraMap (algebraMap ((xplus X E hM).Kl la) (Kp (xplus X E hM) la G.N)).injective
  haveI : IsDVRAt ζ := (integralClosure_dvr' (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N)
    (OsK (xplus X E hM) la G.w)).2 ζ
  have hirr : Irreducible (unif (xplus X E hM) la) :=
    Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible ((xplus X E hM).Ol la))
  haveI : Algebra.IsIntegral (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := Algebra.IsIntegral.of_finite _ _
  have hunif : IsUnif (OsK (xplus X E hM) la G.w) (unifO (xplus X E hM) la G.N) :=
    isUnif_of_field (Kp (xplus X E hM) la G.N) (Op.irreducible_map _ la G.N hirr)
  have hint : ∀ k, toOsK (xplus X E hM) la G.w (wRat G la k) ∈
      As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) :=
    fun k => isIntegral_xr (xplus X E hM) la G.w hfd k
  refine ⟨fun k => ord_nonneg ζ hunif (hint k), ?_⟩
  by_contra hall
  push Not at hall
  have hmemζ : ∀ k, (⟨_, hint k⟩ : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))) ∈ ζ.asIdeal := by
    intro k
    by_contra hk
    apply hall k
    rw [ord_of_mem ζ hunif (hint k)]
    have hu : IsUnit (algebraMap _ (Loc ζ) (⟨_, hint k⟩ : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)))) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal _).2 hk
    have h0 : vL ζ ⟨_, hint k⟩ = 0 := by
      show Ring.ord (Loc ζ) _ = 0
      have := Ring.ord_mul_of_isUnit_left hu (1 : Loc ζ)
      rw [mul_one, Ring.ord_one] at this
      exact this
    rw [h0]
    rfl
  have hT : ∀ k, algebraMap (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)
      (algebraMap (Op (xplus X E hM) la G.N) (Kp (xplus X E hM) la G.N) (Tv (xplus X E hM) la G.N (0, k))) ∈
        As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := fun k =>
    isIntegral_algebraMap (x := Tv (xplus X E hM) la G.N (0, k))
  let s : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) := ∑ k, ⟨_, hT k⟩ * ⟨_, hint k⟩
  have hs1 : s = 1 := by
    apply Subtype.ext
    have := congrArg (toOsK (xplus X E hM) la G.w) (sum_T0_mul_ratio_eq_one (xplus X E hM) la G.w)
    simp only [map_sum, map_mul, map_one] at this
    show (As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)).val s =
      (As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)).val 1
    rw [map_sum, map_one]
    simp only [map_mul]
    exact this
  have hsζ : s ∈ ζ.asIdeal := Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hmemζ k)
  rw [hs1] at hsζ
  exact ζ.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 hsζ)

end Formalism.L2.Pj.GenericSectionMinimum
