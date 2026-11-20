import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsSectionOrder
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PFGNullstellensatz
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartFinite

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Establish `hj'` using `h j (Finset.mem_insert_self j s)`. Take `⟨h1, h2⟩` from `ih fun i hi => h i (Finset.mem_insert_of_mem hi)`.

Establish `hp : (p j ^ k j).natDegree ≤ k j * a j` using `Polynomial.natDegree_pow_le_of_le _ hj'`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, Finset.prod_insert hj]`. Use `⟨Polynomial.natDegree_mul_le_of_le hp h1, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_mul_add_eq_of_natDegree_le hp h1, h2, Polynomial.coeff_pow_of_natDegree_le hj']`.
-/
theorem natDegree_coeff_prod_pow {S ι : Type*} [CommRing S] (s : Finset ι) (p : ι → Polynomial S)
    (a k : ι → ℕ) (h : ∀ i ∈ s, (p i).natDegree ≤ a i) :
    (∏ i ∈ s, p i ^ k i).natDegree ≤ ∑ i ∈ s, k i * a i ∧
      (∏ i ∈ s, p i ^ k i).coeff (∑ i ∈ s, k i * a i) = ∏ i ∈ s, (p i).coeff (a i) ^ k i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    have hj' := h j (Finset.mem_insert_self j s)
    obtain ⟨h1, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hp : (p j ^ k j).natDegree ≤ k j * a j := Polynomial.natDegree_pow_le_of_le _ hj'
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Finset.prod_insert hj]
    refine ⟨Polynomial.natDegree_mul_le_of_le hp h1, ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hp h1, h2, Polynomial.coeff_pow_of_natDegree_le hj']

variable {F : Type} [Field F] {n e : ℕ}

def lineVar (t : Fin n → F) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    Polynomial (MvPolynomial (Fin e × Fin n) F) :=
  Fin.cases (motive := fun _ => Polynomial (MvPolynomial (Fin e × Fin n) F))
    (Polynomial.C (C (t ij.2)) * Polynomial.X - Polynomial.C (C (if ij.2 = m then 1 else 0)))
    (fun i => Polynomial.C (X (i, ij.2))) ij.1

def linePoly (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F) (m : Fin n) :
    Polynomial (MvPolynomial (Fin e × Fin n) F) :=
  aeval (lineVar t m) f

/- English proof (translation)
Take `⟨i, j⟩` from `ij`. Consider the cases of `i using Fin.cases with`. Consider the case `zero`. Simplify using `only [lineVar, specFirstVar, groupWeight, Fin.cases_zero, Pi.single_eq_same]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Use `compute_degree`. Apply the tactic sequence `by_cases h : j = m <;> simp [h, Polynomial.coeff_one]`. Consider the case `succ i`. Simplify using `[lineVar, specFirstVar, groupWeight, (Fin.succ_ne_zero i).symm]`.
-/
theorem lineVar_natDegree_coeff (t : Fin n → F) (m : Fin n) (ij : Fin (e + 1) × Fin n) :
    (lineVar t m ij).natDegree ≤ groupWeight (e + 1) n ij 0 ∧
      (lineVar t m ij).coeff (groupWeight (e + 1) n ij 0) = specFirstVar t ij := by
  obtain ⟨i, j⟩ := ij
  cases i using Fin.cases with
  | zero =>
    simp only [lineVar, specFirstVar, groupWeight, Fin.cases_zero, Pi.single_eq_same]
    refine ⟨?_, ?_⟩
    · compute_degree
    · by_cases h : j = m <;> simp [h, Polynomial.coeff_one]
  | succ i =>
    simp [lineVar, specFirstVar, groupWeight, (Fin.succ_ne_zero i).symm]

/- English proof (translation)
Establish `hw : ∀ d ∈ f.support, ∑ ij ∈ d.support, d ij * groupWeight (e + 1) n ij 0 = δ`. Introduce `d hd`. Establish `h` using `congrFun (hf (mem_support_iff.mp hd)) 0`. Simplify `h` using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`. Establish `key : ∀ d ∈ f.support, (∏ ij ∈ d.support, lineVar t m ij ^ d ij).natDegree ≤ δ ∧ (∏ ij ∈ d.support, lineVar t m ij ^ d ij).coeff δ = ∏ ij ∈ d.support, specFirstVar t ij ^ d ij`.

Introduce `d hd`. Take `⟨h1, h2⟩` from `natDegree_coeff_prod_pow d.support (lineVar t m) (fun ij => groupWeight (e + 1) n ij 0) d (fun ij _ => (lineVar_natDegree_coeff t m ij).1)`. Rewrite `h1`, `h2` using `[hw d hd]`. Conclude with `⟨h1, h2.trans (Finset.prod_congr rfl fun ij _ => by rw [(lineVar_natDegree_coeff t m ij).2])⟩`. Establish `hs : linePoly f t m = ∑ d ∈ f.support, Polynomial.C (C (coeff d f)) * ∏ ij ∈ d.support, lineVar t m ij ^ d ij` using `by conv_lhs => rw [linePoly, f.as_sum, map_sum]`.

Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `[aeval_monomial, Polynomial.algebraMap_apply, Finsupp.prod]`. Establish `hs' : specFirst f t = ∑ d ∈ f.support, C (coeff d f) * ∏ ij ∈ d.support, specFirstVar t ij ^ d ij` using `by conv_lhs => rw [specFirst, f.as_sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun d _ => bind₁_monomial _ _ _`. Rewrite using `[hs, hs']`.

Use `⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => (Polynomial.natDegree_C_mul_le _ _).trans (key d hd).1, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.finsetSum_coeff]`. Conclude with `Finset.sum_congr rfl fun d hd => by rw [Polynomial.coeff_C_mul, (key d hd).2]`.
-/
theorem linePoly_natDegree_coeff {δ : ℕ} {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) (t : Fin n → F) (m : Fin n) :
    (linePoly f t m).natDegree ≤ δ ∧ (linePoly f t m).coeff δ = specFirst f t := by
  classical
  have hw : ∀ d ∈ f.support, ∑ ij ∈ d.support, d ij * groupWeight (e + 1) n ij 0 = δ := by
    intro d hd
    have h := congrFun (hf (mem_support_iff.mp hd)) 0
    simpa [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] using h
  have key : ∀ d ∈ f.support, (∏ ij ∈ d.support, lineVar t m ij ^ d ij).natDegree ≤ δ ∧
      (∏ ij ∈ d.support, lineVar t m ij ^ d ij).coeff δ =
        ∏ ij ∈ d.support, specFirstVar t ij ^ d ij := by
    intro d hd
    obtain ⟨h1, h2⟩ := natDegree_coeff_prod_pow d.support (lineVar t m)
      (fun ij => groupWeight (e + 1) n ij 0) d (fun ij _ => (lineVar_natDegree_coeff t m ij).1)
    rw [hw d hd] at h1 h2
    exact ⟨h1, h2.trans (Finset.prod_congr rfl fun ij _ => by rw [(lineVar_natDegree_coeff t m ij).2])⟩
  have hs : linePoly f t m = ∑ d ∈ f.support,
      Polynomial.C (C (coeff d f)) * ∏ ij ∈ d.support, lineVar t m ij ^ d ij := by
    conv_lhs => rw [linePoly, f.as_sum, map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [aeval_monomial, Polynomial.algebraMap_apply, Finsupp.prod]
  have hs' : specFirst f t = ∑ d ∈ f.support, C (coeff d f) * ∏ ij ∈ d.support, specFirstVar t ij ^ d ij := by
    conv_lhs => rw [specFirst, f.as_sum, map_sum]
    exact Finset.sum_congr rfl fun d _ => bind₁_monomial _ _ _
  rw [hs, hs']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd =>
    (Polynomial.natDegree_C_mul_le _ _).trans (key d hd).1, ?_⟩
  rw [Polynomial.finsetSum_coeff]
  exact Finset.sum_congr rfl fun d hd => by rw [Polynomial.coeff_C_mul, (key d hd).2]

/- English proof (translation)
Use `set J := chartIncIdeal I t e`. Use `set ψ := Polynomial.eval₂RingHom (rename (R := F) (Sum.inr : Fin e × Fin n → Fin n ⊕ Fin e × Fin n)).toRingHom (X (Sum.inl m))`. Establish `: IsReduced (MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ J.radical)` using `(Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical J)`. It suffices to establish `h0 : Ideal.Quotient.mk J.radical (ψ (linePoly f t m)) = 0 from Ideal.Quotient.eq_zero_iff_mem.mp h0`. Use `FGNullstellensatz.proof F _ _ fun φ => ?_` and prove the remaining obligations.

Use `set Φ := φ.comp (Ideal.Quotient.mkₐ F J.radical)`. Use `set pt : Fin n ⊕ Fin e × Fin n → AlgebraicClosure F := fun v => Φ (X v) with hpt`. Establish `hΦ : Φ = aeval pt` using `aeval_unique Φ`. Establish `hJ : ∀ g ∈ J, aeval pt g = 0`. Introduce `g hg`.

Rewrite using `[← hΦ]`. Express the relevant statement in the definitionally equal form `φ (Ideal.Quotient.mk _ g) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.le_radical hg), map_zero]`. Use `set x : Fin n → AlgebraicClosure F := fun j => pt (Sum.inl j) with hx`. Establish `hI : ∀ g ∈ I, aeval x g = 0`.

Introduce `g hg`. Use `hJ (rename Sum.inl g) (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hg)))` as an intermediate fact. Rewrite `this` using `[aeval_rename]`. Then use the resulting hypothesis. Establish `hlin : ∑ j, algebraMap F _ (t j) * x j = 1`. Use `hJ (rename Sum.inl (linForm t - 1)) (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))` as an intermediate fact.

Rewrite `this` using `[aeval_rename]`. Simplify `this` using `[linForm, sub_eq_zero]`. Establish `hU : ∀ i : Fin e, ∑ j, pt (Sum.inr (i, j)) * x j = 0`. Introduce `i`. Use `hJ _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))` as an intermediate fact.

Simplify using `using this`. Use `set V : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij => Fin.cases (motive := fun _ => AlgebraicClosure F) (algebraMap F _ (t ij.2) * x m - algebraMap F _ (if ij.2 = m then 1 else 0)) (fun i => pt (Sum.inr (i, ij.2))) ij.1 with hV`. Establish `hVmem : V ∈ incidence I (e + 1)`. Use `⟨x, ?_, hI, ?_⟩` and prove the remaining obligations. Introduce `h0`.

Rewrite `hlin` using `[h0]`. Simplify using `at hlin`. Introduce `i`. Consider the cases of `i using Fin.cases with`. Consider the case `zero`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hV, Fin.cases_zero, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Use `_ = 0 := by simp [hlin]`.

Consider the case `succ i => simpa [hV] using hU i`. Establish `hfV : aeval V f = 0` using `(hf.2 f).mpr dvd_rfl V hVmem`. Establish `hk1 : ((aeval pt).toRingHom.comp ψ).comp (algebraMap F (Polynomial (MvPolynomial (Fin e × Fin n) F))) = algebraMap F (AlgebraicClosure F)`. Use extensionality with `a`. Simplify using `[ψ, Polynomial.algebraMap_apply]`.

Establish `hk2 : ((aeval pt).toRingHom.comp ψ) ∘ lineVar t m = V`. Use function extensionality and compare the values at `⟨i, j⟩`. Consider the cases of `i using Fin.cases with`. Consider the case `zero => by_cases h : j = m <;> simp [lineVar, hV, ψ, hx, h]`. Consider the case `succ i => simp [lineVar, hV, ψ]`.

Express the relevant statement in the definitionally equal form `Φ (ψ (linePoly f t m)) = 0`. Rewrite using `[hΦ]`. Express the relevant statement in the definitionally equal form `((aeval pt).toRingHom.comp ψ) (linePoly f t m) = 0`. Rewrite using `[linePoly, aeval_def, MvPolynomial.eval₂_comp_left, hk1, hk2, ← aeval_def, hfV]`.
-/
theorem exists_pow_mem (I : Ideal (MvPolynomial (Fin n) F)) (f : MvPolynomial (Fin (e + 1) × Fin n) F)
    (t : Fin n → F) (hf : IsChowForm I (e + 1) f) (m : Fin n) :
    ∃ N : ℕ, (Polynomial.eval₂RingHom (rename (R := F) (Sum.inr : Fin e × Fin n → Fin n ⊕ Fin e × Fin n)).toRingHom
      (X (Sum.inl m)) (linePoly f t m)) ^ N ∈ chartIncIdeal I t e := by
  classical
  set J := chartIncIdeal I t e
  set ψ := Polynomial.eval₂RingHom (rename (R := F) (Sum.inr : Fin e × Fin n → Fin n ⊕ Fin e × Fin n)).toRingHom
      (X (Sum.inl m))
  have : IsReduced (MvPolynomial (Fin n ⊕ Fin e × Fin n) F ⧸ J.radical) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical J)
  suffices h0 : Ideal.Quotient.mk J.radical (ψ (linePoly f t m)) = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mp h0
  refine FGNullstellensatz.proof F _ _ fun φ => ?_
  set Φ := φ.comp (Ideal.Quotient.mkₐ F J.radical)
  set pt : Fin n ⊕ Fin e × Fin n → AlgebraicClosure F := fun v => Φ (X v) with hpt
  have hΦ : Φ = aeval pt := aeval_unique Φ
  have hJ : ∀ g ∈ J, aeval pt g = 0 := by
    intro g hg
    rw [← hΦ]
    change φ (Ideal.Quotient.mk _ g) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.le_radical hg), map_zero]
  set x : Fin n → AlgebraicClosure F := fun j => pt (Sum.inl j) with hx
  have hI : ∀ g ∈ I, aeval x g = 0 := by
    intro g hg
    have := hJ (rename Sum.inl g)
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_left hg)))
    rwa [aeval_rename] at this
  have hlin : ∑ j, algebraMap F _ (t j) * x j = 1 := by
    have := hJ (rename Sum.inl (linForm t - 1))
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
    rw [aeval_rename] at this
    simpa [linForm, sub_eq_zero] using this
  have hU : ∀ i : Fin e, ∑ j, pt (Sum.inr (i, j)) * x j = 0 := by
    intro i
    have := hJ _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    simpa using this
  set V : Fin (e + 1) × Fin n → AlgebraicClosure F := fun ij =>
    Fin.cases (motive := fun _ => AlgebraicClosure F)
      (algebraMap F _ (t ij.2) * x m - algebraMap F _ (if ij.2 = m then 1 else 0))
      (fun i => pt (Sum.inr (i, ij.2))) ij.1 with hV
  have hVmem : V ∈ incidence I (e + 1) := by
    refine ⟨x, ?_, hI, ?_⟩
    · intro h0
      rw [h0] at hlin
      simp at hlin
    · intro i
      cases i using Fin.cases with
      | zero =>
        calc ∑ j, V (0, j) * x j
            = x m * ∑ j, algebraMap F _ (t j) * x j - ∑ j, algebraMap F _ (if j = m then 1 else 0) * x j := by
              simp only [hV, Fin.cases_zero, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
              congr 1
              exact Finset.sum_congr rfl fun j _ => by ring
          _ = 0 := by simp [hlin]
      | succ i => simpa [hV] using hU i
  have hfV : aeval V f = 0 := (hf.2 f).mpr dvd_rfl V hVmem
  have hk1 : ((aeval pt).toRingHom.comp ψ).comp
      (algebraMap F (Polynomial (MvPolynomial (Fin e × Fin n) F))) = algebraMap F (AlgebraicClosure F) := by
    ext a
    simp [ψ, Polynomial.algebraMap_apply]
  have hk2 : ((aeval pt).toRingHom.comp ψ) ∘ lineVar t m = V := by
    funext ⟨i, j⟩
    cases i using Fin.cases with
    | zero => by_cases h : j = m <;> simp [lineVar, hV, ψ, hx, h]
    | succ i => simp [lineVar, hV, ψ]
  change Φ (ψ (linePoly f t m)) = 0
  rw [hΦ]
  change ((aeval pt).toRingHom.comp ψ) (linePoly f t m) = 0
  rw [linePoly, aeval_def, MvPolynomial.eval₂_comp_left, hk1, hk2, ← aeval_def, hfV]

end ChartFinite

open ChartFinite in

/- English proof (translation)
Introduce `F _ n e I f t p _ hI hf hp`. Take `⟨δ, -, hδ⟩` from `chowFormMultiHomog F n (e + 1) I f hI hf`. Establish `hu : IsUnit (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (specFirst f t))` using `IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, hp⟩ : p.primeCompl)`. Establish `hint : ∀ m : Fin n, IsIntegral (Localization.AtPrime p) (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)))`. Introduce `m`.

Take `⟨N, hN⟩` from `exists_pow_mem I f t hf m`. Take `⟨h1, h2⟩` from `linePoly_natDegree_coeff hδ t m`. Establish `hSig : (Polynomial.eval₂ (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) (chartX I t e (X m)) (linePoly f t m)) ^ N = 0`. Establish `h0` using `(Ideal.Quotient.eq_zero_iff_mem (I := chartIncIdeal I t e)).mpr hN`. Rewrite `h0` using `[map_pow, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂]`.

Establish `hx : chartX I t e (X m) = Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inl m))`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inl (X m)) = _`. Rewrite using `[rename_X]`. Rewrite using `[hx]`. Conclude with `h0`.

Establish `hQdeg : ((linePoly f t m).map (algebraMap _ (Localization.AtPrime p)) ^ N).natDegree ≤ N * δ` using `Polynomial.natDegree_pow_le_of_le N (Polynomial.natDegree_map_le.trans h1)`. Establish `hQcoeff : ((linePoly f t m).map (algebraMap _ (Localization.AtPrime p)) ^ N).coeff (N * δ) = (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (specFirst f t)) ^ N`. Rewrite using `[Polynomial.coeff_pow_of_natDegree_le (Polynomial.natDegree_map_le.trans h1), Polynomial.coeff_map, h2]`. Establish `hQeval : ((linePoly f t m).map (algebraMap _ (Localization.AtPrime p)) ^ N).eval₂ (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)) (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = 0`. Rewrite using `[Polynomial.eval₂_pow, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (ChartLoc I t e p), ← Polynomial.hom_eval₂, ← map_pow, hSig, map_zero]`.

Use `⟨Polynomial.C (↑(hu.unit ^ N)⁻¹) * (linePoly f t m).map (algebraMap _ (Localization.AtPrime p)) ^ N, Polynomial.monic_of_natDegree_le_of_coeff_eq_one (N * δ) ((Polynomial.natDegree_C_mul_le _ _).trans hQdeg) ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_C_mul, hQcoeff]`. Establish `h3` using `(hu.unit ^ N).inv_mul`. Rewrite `h3` using `[Units.val_pow_eq_pow_val, hu.unit_spec]`. Then use the resulting hypothesis. Rewrite using `[Polynomial.eval₂_mul, hQeval, mul_zero]`.

Establish `hS : ∀ y : MvPolynomial (Fin e × Fin n) F, algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) y) ∈ Algebra.adjoin (Localization.AtPrime p) (Set.range fun m : Fin n => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)))`. Introduce `y`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Set `κ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartLoc I t e p` to `(algebraMap (ChartInc I t e) (ChartLoc I t e p)).comp (Ideal.Quotient.mk (chartIncIdeal I t e))`.

Establish `hκ : ∀ g, κ g ∈ Algebra.adjoin (Localization.AtPrime p) (Set.range fun m : Fin n => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)))`. Introduce `g`. Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `h3 : κ (C a) = algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a))`.

Express the relevant statement in the definitionally equal form `algebraMap (ChartInc I t e) (ChartLoc I t e p) (Ideal.Quotient.mk (chartIncIdeal I t e) (C a)) = algebraMap (ChartInc I t e) (ChartLoc I t e p) (Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inr (C a)))`. Rewrite using `[rename_C]`. Rewrite using `[h3]`. Conclude with `hS (C a)`. Consider the case `add g h hg hh`.

Rewrite using `[map_add]`. Conclude with `add_mem hg hh`. Consider the case `mul_X g v hg`. Rewrite using `[map_mul]`. Use `mul_mem hg ?_` and prove the remaining obligations.

Consider the cases of `v with`. Consider the case `inl j`. Use `Algebra.subset_adjoin ⟨j, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap (ChartInc I t e) (ChartLoc I t e p) (Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inl (X j))) = algebraMap (ChartInc I t e) (ChartLoc I t e p) (Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inl j)))`. Rewrite using `[rename_X]`.

Consider the case `inr ij`. Establish `h3 : κ (X (Sum.inr ij)) = algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X ij))`. Express the relevant statement in the definitionally equal form `algebraMap (ChartInc I t e) (ChartLoc I t e p) (Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inr ij))) = algebraMap (ChartInc I t e) (ChartLoc I t e p) (Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inr (X ij)))`. Rewrite using `[rename_X]`. Rewrite using `[h3]`.

Conclude with `hS (X ij)`. Establish `hSig : ∀ z : ChartInc I t e, algebraMap (ChartInc I t e) (ChartLoc I t e p) z ∈ Algebra.adjoin (Localization.AtPrime p) (Set.range fun m : Fin n => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)))`. Introduce `z`. Take `⟨g, rfl⟩` from `Ideal.Quotient.mk_surjective (I := chartIncIdeal I t e) z`. Conclude with `hκ g`.

Establish `htop : Algebra.adjoin (Localization.AtPrime p) (Set.range fun m : Fin n => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `z -`. Take `⟨⟨y, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl) z`. Take `⟨s, s₀, hs₀, rfl⟩` from `s`.

Simplify using `only`. Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one]`. Use `mul_mem (hSig y) ?_` and prove the remaining obligations. Establish `h` using `IsLocalization.algebraMap_mk' (Rₘ := Localization.AtPrime p) (Sₘ := ChartLoc I t e p) (M := p.primeCompl) (S := ChartInc I t e) 1 ⟨s₀, hs₀⟩`. Rewrite `h` using `[map_one]`.

Rewrite using `[← h]`. Conclude with `Subalgebra.algebraMap_mem _ _`. Establish `hfg` using `fg_adjoin_of_finite (Set.finite_range _) (by rintro _ ⟨m, rfl⟩; exact hint m)`. Rewrite `hfg` using `[htop, Algebra.top_toSubmodule]`. Conclude with `⟨hfg⟩`.
-/
theorem ChartFinite.proof : ChartFinite.Statement := by
  intro F _ n e I f t p _ hI hf hp
  classical
  obtain ⟨δ, -, hδ⟩ := chowFormMultiHomog F n (e + 1) I f hI hf
  have hu : IsUnit (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (specFirst f t)) :=
    IsLocalization.map_units (Localization.AtPrime p) (⟨specFirst f t, hp⟩ : p.primeCompl)
  have hint : ∀ m : Fin n, IsIntegral (Localization.AtPrime p)
      (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) := by
    intro m
    obtain ⟨N, hN⟩ := exists_pow_mem I f t hf m
    obtain ⟨h1, h2⟩ := linePoly_natDegree_coeff hδ t m
    have hSig : (Polynomial.eval₂ (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e))
        (chartX I t e (X m)) (linePoly f t m)) ^ N = 0 := by
      have h0 := (Ideal.Quotient.eq_zero_iff_mem (I := chartIncIdeal I t e)).mpr hN
      rw [map_pow, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂] at h0
      have hx : chartX I t e (X m) = Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inl m)) := by
        change Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inl (X m)) = _
        rw [rename_X]
      rw [hx]
      exact h0
    have hQdeg : ((linePoly f t m).map (algebraMap _ (Localization.AtPrime p)) ^ N).natDegree ≤ N * δ :=
      Polynomial.natDegree_pow_le_of_le N (Polynomial.natDegree_map_le.trans h1)
    have hQcoeff : ((linePoly f t m).map (algebraMap _ (Localization.AtPrime p)) ^ N).coeff (N * δ) =
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (specFirst f t)) ^ N := by
      rw [Polynomial.coeff_pow_of_natDegree_le (Polynomial.natDegree_map_le.trans h1), Polynomial.coeff_map, h2]
    have hQeval : ((linePoly f t m).map (algebraMap _ (Localization.AtPrime p)) ^ N).eval₂
        (algebraMap (Localization.AtPrime p) (ChartLoc I t e p))
        (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = 0 := by
      rw [Polynomial.eval₂_pow, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (ChartLoc I t e p),
        ← Polynomial.hom_eval₂, ← map_pow, hSig, map_zero]
    refine ⟨Polynomial.C (↑(hu.unit ^ N)⁻¹) * (linePoly f t m).map (algebraMap _ (Localization.AtPrime p)) ^ N,
      Polynomial.monic_of_natDegree_le_of_coeff_eq_one (N * δ)
        ((Polynomial.natDegree_C_mul_le _ _).trans hQdeg) ?_, ?_⟩
    · rw [Polynomial.coeff_C_mul, hQcoeff]
      have h3 := (hu.unit ^ N).inv_mul
      rwa [Units.val_pow_eq_pow_val, hu.unit_spec] at h3
    · rw [Polynomial.eval₂_mul, hQeval, mul_zero]
  have hS : ∀ y : MvPolynomial (Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) y) ∈
        Algebra.adjoin (Localization.AtPrime p)
          (Set.range fun m : Fin n => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) := by
    intro y
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)]
    exact Subalgebra.algebraMap_mem _ _
  let κ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartLoc I t e p :=
    (algebraMap (ChartInc I t e) (ChartLoc I t e p)).comp (Ideal.Quotient.mk (chartIncIdeal I t e))
  have hκ : ∀ g, κ g ∈ Algebra.adjoin (Localization.AtPrime p)
      (Set.range fun m : Fin n => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) := by
    intro g
    induction g using MvPolynomial.induction_on with
    | C a =>
      have h3 : κ (C a) = algebraMap (ChartInc I t e) (ChartLoc I t e p)
          (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a)) := by
        change algebraMap (ChartInc I t e) (ChartLoc I t e p) (Ideal.Quotient.mk (chartIncIdeal I t e) (C a)) =
          algebraMap (ChartInc I t e) (ChartLoc I t e p)
            (Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inr (C a)))
        rw [rename_C]
      rw [h3]
      exact hS (C a)
    | add g h hg hh =>
      rw [map_add]
      exact add_mem hg hh
    | mul_X g v hg =>
      rw [map_mul]
      refine mul_mem hg ?_
      cases v with
      | inl j =>
        refine Algebra.subset_adjoin ⟨j, ?_⟩
        change algebraMap (ChartInc I t e) (ChartLoc I t e p)
            (Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inl (X j))) =
          algebraMap (ChartInc I t e) (ChartLoc I t e p) (Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inl j)))
        rw [rename_X]
      | inr ij =>
        have h3 : κ (X (Sum.inr ij)) = algebraMap (ChartInc I t e) (ChartLoc I t e p)
            (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X ij)) := by
          change algebraMap (ChartInc I t e) (ChartLoc I t e p)
              (Ideal.Quotient.mk (chartIncIdeal I t e) (X (Sum.inr ij))) =
            algebraMap (ChartInc I t e) (ChartLoc I t e p)
              (Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inr (X ij)))
          rw [rename_X]
        rw [h3]
        exact hS (X ij)
  have hSig : ∀ z : ChartInc I t e, algebraMap (ChartInc I t e) (ChartLoc I t e p) z ∈
      Algebra.adjoin (Localization.AtPrime p)
        (Set.range fun m : Fin n => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) := by
    intro z
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective (I := chartIncIdeal I t e) z
    exact hκ g
  have htop : Algebra.adjoin (Localization.AtPrime p)
      (Set.range fun m : Fin n => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨⟨y, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl) z
    obtain ⟨s, s₀, hs₀, rfl⟩ := s
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine mul_mem (hSig y) ?_
    have h := IsLocalization.algebraMap_mk' (Rₘ := Localization.AtPrime p) (Sₘ := ChartLoc I t e p)
      (M := p.primeCompl) (S := ChartInc I t e) 1 ⟨s₀, hs₀⟩
    rw [map_one] at h
    rw [← h]
    exact Subalgebra.algebraMap_mem _ _
  have hfg := fg_adjoin_of_finite (Set.finite_range _) (by rintro _ ⟨m, rfl⟩; exact hint m)
  rw [htop, Algebra.top_toSubmodule] at hfg
  exact ⟨hfg⟩

end

end GroundTheory.Heights₂.Heights
