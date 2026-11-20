import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace SectionCycle

section Local

variable {S : Type*} [CommRing S]

/- English proof (translation)
Set `q : (S ⧸ J) →ₗ[S] (S ⧸ J₁)` to `Submodule.mapQ J J₁ LinearMap.id hJ`. Set `φ` to `IsLocalizedModule.map W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J)) (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J₁)) q`. Establish `hφ : ∀ (x : S) (s : W.primeCompl), φ (LocalizedModule.mk (Submodule.Quotient.mk x) s) = LocalizedModule.mk (Submodule.Quotient.mk x) s`. Introduce `x s`. Rewrite using `[IsLocalizedModule.map_LocalizedModules]`.

Both sides reduce to the same expression. Establish `htW : t ∈ W.primeCompl` using `ht`. Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y`.

Use `LocalizedModule.induction_on (fun m s hy ↦ ?_) y` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective J m`. Rewrite `hy` using `[hφ, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]`. Take `⟨u, hu⟩` from `hy`. Simplify using `only [smul_zero, one_smul] at hu`.

Rewrite `hu` using `[Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]`. Rewrite using `[← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]`. Use `⟨⟨t, htW⟩ * u, ?_⟩` and prove the remaining obligations. Simplify using `only [smul_zero, one_smul]`. Rewrite using `[Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul, Submonoid.coe_mul, mul_assoc]`.

Conclude with `hmul _ hu`. Establish `hsurj : Function.Surjective φ`. Introduce `y`. Use `LocalizedModule.induction_on (fun m s ↦ ?_) y` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective J₁ m`.

Conclude with `⟨LocalizedModule.mk (Submodule.Quotient.mk x) s, hφ x s⟩`. Conclude with `((LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization W.primeCompl (Localization.AtPrime W)).length_eq`.
-/
theorem length_localized_eq {J J₁ W : Ideal S} [W.IsPrime] (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (S ⧸ J₁)) := by
  let q : (S ⧸ J) →ₗ[S] (S ⧸ J₁) := Submodule.mapQ J J₁ LinearMap.id hJ
  let φ := IsLocalizedModule.map W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J))
    (LocalizedModule.mkLinearMap W.primeCompl (S ⧸ J₁)) q
  have hφ : ∀ (x : S) (s : W.primeCompl), φ (LocalizedModule.mk (Submodule.Quotient.mk x) s) =
      LocalizedModule.mk (Submodule.Quotient.mk x) s := by
    intro x s
    rw [IsLocalizedModule.map_LocalizedModules]
    rfl
  have htW : t ∈ W.primeCompl := ht
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y
    refine LocalizedModule.induction_on (fun m s hy ↦ ?_) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J m
    rw [hφ, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at hy
    obtain ⟨u, hu⟩ := hy
    simp only [smul_zero, one_smul] at hu
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul] at hu
    rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
    refine ⟨⟨t, htW⟩ * u, ?_⟩
    simp only [smul_zero, one_smul]
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      smul_eq_mul, Submonoid.coe_mul, mul_assoc]
    exact hmul _ hu
  have hsurj : Function.Surjective φ := by
    intro y
    refine LocalizedModule.induction_on (fun m s ↦ ?_) y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective J₁ m
    exact ⟨LocalizedModule.mk (Submodule.Quotient.mk x) s, hφ x s⟩
  exact ((LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)).length_eq

/- English proof (translation)
Establish `key : ∀ Q : Ideal S, Q.IsPrime → Q ≤ W → (J ≤ Q ↔ J₁ ≤ Q)` using `fun Q hQ hQW ↦ ⟨fun h x hx ↦ (hQ.mem_or_mem (h (hmul x hx))).resolve_left fun htQ ↦ ht (hQW htQ), hJ.trans⟩`. Simplify using `only [Ideal.minimalPrimes, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hWp, hJW⟩, hmin⟩`. Conclude with `⟨⟨hWp, (key W hWp le_rfl).mp hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mpr hQ.2⟩ hQW⟩`.

Introduce and unpack `⟨⟨hWp, hJW⟩, hmin⟩`. Conclude with `⟨⟨hWp, (key W hWp le_rfl).mpr hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mp hQ.2⟩ hQW⟩`.
-/
theorem mem_minimalPrimes_iff {J J₁ W : Ideal S} (hJ : J ≤ J₁) {t : S} (ht : t ∉ W)
    (hmul : ∀ x ∈ J₁, t * x ∈ J) : W ∈ J.minimalPrimes ↔ W ∈ J₁.minimalPrimes := by
  have key : ∀ Q : Ideal S, Q.IsPrime → Q ≤ W → (J ≤ Q ↔ J₁ ≤ Q) := fun Q hQ hQW ↦
    ⟨fun h x hx ↦ (hQ.mem_or_mem (h (hmul x hx))).resolve_left fun htQ ↦ ht (hQW htQ), hJ.trans⟩
  simp only [Ideal.minimalPrimes, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨hWp, hJW⟩, hmin⟩
    exact ⟨⟨hWp, (key W hWp le_rfl).mp hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mpr hQ.2⟩ hQW⟩
  · rintro ⟨⟨hWp, hJW⟩, hmin⟩
    exact ⟨⟨hWp, (key W hWp le_rfl).mpr hJW⟩, fun Q hQ hQW ↦ hmin ⟨hQ.1, (key Q hQ.1 hQW).mp hQ.2⟩ hQW⟩

end Local

section Cycle

variable {K : Type*} {κ : K → Type*} {R : Type*} [CommRing R]

/- English proof (translation)
Unfold `NumbersDVR.divCycle`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨hmin, hrel⟩`. Conclude with `h ⟨hmin.1.1, hrel, le_sup_left.trans hmin.1.2⟩`.
-/
theorem divCycle_eq_zero {I W : Ideal (NumbersDVR.MRing κ R)} (f : NumbersDVR.MRing κ R)
    (h : ¬ (W.IsPrime ∧ NumbersDVR.IsRelevant W ∧ I ≤ W)) : NumbersDVR.divCycle I f W = 0 := by
  unfold NumbersDVR.divCycle
  rw [dif_neg]
  rintro ⟨hmin, hrel⟩
  exact h ⟨hmin.1.1, hrel, le_sup_left.trans hmin.1.2⟩

/- English proof (translation)
Use `set J := I ⊔ Ideal.span {f * g'} with hJdef`. Establish `hfg : f * g' ∈ J` using `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Establish `hIJ : I ≤ J` using `le_sup_left`. Establish `hf'g : f' * g ∈ J`. Establish `h` using `J.sub_mem hfg (hIJ hrel)`.

Rewrite `h` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h1 : J ≤ I ⊔ Ideal.span {f}` using `sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_sup_right (Ideal.mul_mem_right g' _ (Ideal.mem_span_singleton_self f))))`. Establish `h2 : J ≤ I ⊔ Ideal.span {g}`. Use `sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)` and prove the remaining obligations. Establish `h` using `Ideal.add_mem _ (Ideal.mem_sup_left hrel : _ ∈ I ⊔ Ideal.span {g}) (Ideal.mem_sup_right (Ideal.mul_mem_left _ f' (Ideal.mem_span_singleton_self g)) : _ ∈ I ⊔ Ideal.span {g})`.

Rewrite `h` using `[sub_add_cancel]`. Then use the resulting hypothesis. Establish `hm1 : ∀ x ∈ I ⊔ Ideal.span {f}, g' * x ∈ J`. Introduce `x hx`. Take `⟨i, hi, y, hy, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`.

Rewrite using `[mul_add, show g' * (r * f) = r * (f * g') by ring]`. Conclude with `J.add_mem (hIJ (I.mul_mem_left _ hi)) (J.mul_mem_left _ hfg)`. Establish `hm2 : ∀ x ∈ I ⊔ Ideal.span {g}, f' * x ∈ J`. Introduce `x hx`. Take `⟨i, hi, y, hy, rfl⟩` from `Submodule.mem_sup.mp hx`.

Take `⟨r, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Rewrite using `[mul_add, show f' * (r * g) = r * (f' * g) by ring]`. Conclude with `J.add_mem (hIJ (I.mul_mem_left _ hi)) (J.mul_mem_left _ hf'g)`. Establish `e1` using `mem_minimalPrimes_iff h1 hg' hm1`. Establish `e2` using `mem_minimalPrimes_iff h2 hf' hm2`.

Establish `l1` using `length_localized_eq h1 hg' hm1`. Establish `l2` using `length_localized_eq h2 hf' hm2`. Unfold `NumbersDVR.divCycle`. Distinguish the cases in `hc : W ∈ (I ⊔ Ideal.span {f}).minimalPrimes ∧ NumbersDVR.IsRelevant W`. Establish `hc' : W ∈ (I ⊔ Ideal.span {g}).minimalPrimes ∧ NumbersDVR.IsRelevant W` using `⟨e2.mp (e1.mpr hc.1), hc.2⟩`.

Rewrite using `[dif_pos hc, dif_pos hc']`. Conclude with `congrArg (fun m : ℕ∞ ↦ (m.toNat : ℤ)) (l1.symm.trans l2)`. Establish `hc' : ¬ (W ∈ (I ⊔ Ideal.span {g}).minimalPrimes ∧ NumbersDVR.IsRelevant W)` using `fun h ↦ hc ⟨e1.mp (e2.mpr h.1), h.2⟩`. Rewrite using `[dif_neg hc, dif_neg hc']`.
-/
theorem divCycle_eq_of_cross (I : Ideal (NumbersDVR.MRing κ R)) {f g f' g' : NumbersDVR.MRing κ R}
    {W : Ideal (NumbersDVR.MRing κ R)} [W.IsPrime] (hf' : f' ∉ W) (hg' : g' ∉ W)
    (hrel : f * g' - f' * g ∈ I) : NumbersDVR.divCycle I f W = NumbersDVR.divCycle I g W := by
  set J := I ⊔ Ideal.span {f * g'} with hJdef
  have hfg : f * g' ∈ J := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hIJ : I ≤ J := le_sup_left
  have hf'g : f' * g ∈ J := by
    have h := J.sub_mem hfg (hIJ hrel)
    rwa [sub_sub_cancel] at h
  have h1 : J ≤ I ⊔ Ideal.span {f} := sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr
    (Ideal.mem_sup_right (Ideal.mul_mem_right g' _ (Ideal.mem_span_singleton_self f))))
  have h2 : J ≤ I ⊔ Ideal.span {g} := by
    refine sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    have h := Ideal.add_mem _ (Ideal.mem_sup_left hrel : _ ∈ I ⊔ Ideal.span {g})
      (Ideal.mem_sup_right (Ideal.mul_mem_left _ f' (Ideal.mem_span_singleton_self g)) :
        _ ∈ I ⊔ Ideal.span {g})
    rwa [sub_add_cancel] at h
  have hm1 : ∀ x ∈ I ⊔ Ideal.span {f}, g' * x ∈ J := by
    intro x hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mul_add, show g' * (r * f) = r * (f * g') by ring]
    exact J.add_mem (hIJ (I.mul_mem_left _ hi)) (J.mul_mem_left _ hfg)
  have hm2 : ∀ x ∈ I ⊔ Ideal.span {g}, f' * x ∈ J := by
    intro x hx
    obtain ⟨i, hi, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    rw [mul_add, show f' * (r * g) = r * (f' * g) by ring]
    exact J.add_mem (hIJ (I.mul_mem_left _ hi)) (J.mul_mem_left _ hf'g)
  have e1 := mem_minimalPrimes_iff h1 hg' hm1
  have e2 := mem_minimalPrimes_iff h2 hf' hm2
  have l1 := length_localized_eq h1 hg' hm1
  have l2 := length_localized_eq h2 hf' hm2
  unfold NumbersDVR.divCycle
  by_cases hc : W ∈ (I ⊔ Ideal.span {f}).minimalPrimes ∧ NumbersDVR.IsRelevant W
  · have hc' : W ∈ (I ⊔ Ideal.span {g}).minimalPrimes ∧ NumbersDVR.IsRelevant W :=
      ⟨e2.mp (e1.mpr hc.1), hc.2⟩
    rw [dif_pos hc, dif_pos hc']
    exact congrArg (fun m : ℕ∞ ↦ (m.toNat : ℤ)) (l1.symm.trans l2)
  · have hc' : ¬ (W ∈ (I ⊔ Ideal.span {g}).minimalPrimes ∧ NumbersDVR.IsRelevant W) :=
      fun h ↦ hc ⟨e1.mp (e2.mpr h.1), h.2⟩
    rw [dif_neg hc, dif_neg hc']

end Cycle

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply]`. Simplify using `only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, coordDeg, smul_eq_mul, Finsupp.prod]`. Repeatedly rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun v _ ↦ ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_eq_single v.1 (fun k _ hk ↦ by simp [hk]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem prod_pow_weight {M : Type*} [CommMonoid M] (t : ι → M) (s : Coord n →₀ ℕ) :
    ∏ k, t k ^ (Finsupp.weight (coordDeg n) s k) = s.prod fun v e ↦ t v.1 ^ e := by
  classical
  rw [Finsupp.weight_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, coordDeg, smul_eq_mul, Finsupp.prod]
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  rw [Finset.prod_eq_single v.1 (fun k _ hk ↦ by simp [hk]) (by simp)]
  simp

section AddBlock

variable {P : ArithVariety n} (D : AddBlockData P)

/- English proof (translation)
Introduce `v w h`. Establish `h1 : v.1 = w.1` using `Option.some_injective _ (congrArg Sigma.fst h)`. Conclude with `Sigma.ext h1 (Sigma.mk.inj_iff.mp h).2`.
-/
theorem oldCoord_injective : Function.Injective D.oldCoord := by
  intro v w h
  have h1 : v.1 = w.1 := Option.some_injective _ (congrArg Sigma.fst h)
  exact Sigma.ext h1 (Sigma.mk.inj_iff.mp h).2

/- English proof (translation)
Rewrite using `[prod_pow_weight (fun k ↦ (X (some k) : MvPolynomial (Option ι) P.FunField))]`. Rewrite using `[AddBlockData.liftOld, rename_monomial, AddBlockData.extMap, coe_eval₂Hom, eval₂_monomial, Finsupp.prod_mapDomain_index_inj (oldCoord_injective D)]`. Rewrite using `[monomial_eq, map_mul, map_finsuppProd, map_mul, map_finsuppProd]`. Simplify using `only [map_pow, mul_pow, Finsupp.prod_mul]`. Establish `ha : C (P.mkF (C a)) = (Int.castRingHom (MvPolynomial (Option ι) P.FunField)) a`.

Rewrite using `[← RingHom.comp_apply P.mkF C, eq_intCast, map_intCast, eq_intCast]`. Rewrite using `[ha, mul_assoc]`. Both sides reduce to the same expression.
-/
theorem extMap_liftOld_monomial (s : Coord n →₀ ℕ) (a : ℤ) :
    D.extMap (D.liftOld (monomial s a)) =
      C (P.mkF (monomial s a)) * ∏ k, X (some k) ^ (Finsupp.weight (coordDeg n) s k) := by
  rw [prod_pow_weight (fun k ↦ (X (some k) : MvPolynomial (Option ι) P.FunField))]
  rw [AddBlockData.liftOld, rename_monomial, AddBlockData.extMap, coe_eval₂Hom, eval₂_monomial,
    Finsupp.prod_mapDomain_index_inj (oldCoord_injective D)]
  rw [monomial_eq, map_mul, map_finsuppProd, map_mul, map_finsuppProd]
  simp only [map_pow, mul_pow, Finsupp.prod_mul]
  have ha : C (P.mkF (C a)) = (Int.castRingHom (MvPolynomial (Option ι) P.FunField)) a := by
    rw [← RingHom.comp_apply P.mkF C, eq_intCast, map_intCast, eq_intCast]
  rw [ha, mul_assoc]
  rfl

/- English proof (translation)
Rewrite using `[h.as_sum, map_sum, map_sum, map_sum, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun s hs ↦ ?_` and prove the remaining obligations. Rewrite using `[extMap_liftOld_monomial, hh (mem_support_iff.mp hs)]`.
-/
theorem extMap_liftOld {h : MvPolynomial (Coord n) ℤ} {δ : ι → ℕ}
    (hh : IsWeightedHomogeneous (coordDeg n) h δ) :
    D.extMap (D.liftOld h) = C (P.mkF h) * ∏ k, X (some k) ^ δ k := by
  rw [h.as_sum, map_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [extMap_liftOld_monomial, hh (mem_support_iff.mp hs)]

/- English proof (translation)
Rewrite using `[AddBlockData.extMap, eval₂Hom_X']`. Both sides reduce to the same expression.
-/
theorem extMap_newCoord (j : Fin (D.size + 1)) :
    D.extMap (X (D.newCoord j)) = C (D.elt j) * X none := by
  rw [AddBlockData.extMap, eval₂Hom_X']
  rfl

/- English proof (translation)
Rewrite using `[AddBlockData.extIdeal, RingHom.mem_ker, ← finsum_weightedHomogeneousComponent (w := coordDeg n) (φ := p), finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p), map_sum, map_sum]`. Use `Finset.sum_eq_zero fun m _ ↦ ?_` and prove the remaining obligations. Rewrite using `[extMap_liftOld D (weightedHomogeneousComponent_isWeightedHomogeneous m p), (P.mkF_eq_zero_iff _).mpr (P.homogeneous p hp m), map_zero, zero_mul]`.
-/
theorem liftOld_mem {p : MvPolynomial (Coord n) ℤ} (hp : p ∈ P.ideal) : D.liftOld p ∈ D.extIdeal := by
  rw [AddBlockData.extIdeal, RingHom.mem_ker,
    ← finsum_weightedHomogeneousComponent (w := coordDeg n) (φ := p),
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p), map_sum, map_sum]
  refine Finset.sum_eq_zero fun m _ ↦ ?_
  rw [extMap_liftOld D (weightedHomogeneousComponent_isWeightedHomogeneous m p),
    (P.mkF_eq_zero_iff _).mpr (P.homogeneous p hp m), map_zero, zero_mul]

variable {d : ι → ℕ} {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}

/- English proof (translation)
Take `⟨δ, hδ, hδk⟩` from `hg.homog c j`. Use `hδ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Rewrite using `[← hδk k]`. Simplify using the standard rewrite rules.
-/
theorem isWeightedHomogeneous_form (hg : D.IsFormSystem d g) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (D.size + 1)) :
    IsWeightedHomogeneous (coordDeg n) (g c j) (fun k ↦ ((d k : ℤ) + D.deg k).toNat) := by
  obtain ⟨δ, hδ, hδk⟩ := hg.homog c j
  convert hδ using 1
  funext k
  rw [← hδk k]
  simp

/- English proof (translation)
Rewrite using `[AddBlockData.extIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, map_mul, map_mul, extMap_newCoord, extMap_newCoord, extMap_liftOld D (isWeightedHomogeneous_chartMonomial c d), extMap_liftOld D (isWeightedHomogeneous_chartMonomial c' d), extMap_liftOld D (isWeightedHomogeneous …`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cross_mem (hg : D.IsFormSystem d g) {c c' : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    (hc' : P.IsLive c') (j j' : Fin (D.size + 1)) :
    X (D.newCoord j) * D.liftOld (chartMonomial c d) * D.liftOld (g c' j') -
      X (D.newCoord j') * D.liftOld (chartMonomial c' d) * D.liftOld (g c j) ∈ D.extIdeal := by
  rw [AddBlockData.extIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, map_mul, map_mul,
    extMap_newCoord, extMap_newCoord, extMap_liftOld D (isWeightedHomogeneous_chartMonomial c d),
    extMap_liftOld D (isWeightedHomogeneous_chartMonomial c' d),
    extMap_liftOld D (isWeightedHomogeneous_form D hg c' j'),
    extMap_liftOld D (isWeightedHomogeneous_form D hg c j), hg.value c hc, hg.value c' hc']
  simp only [map_mul]
  ring

/- English proof (translation)
Rewrite using `[AddBlockData.extIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, extMap_newCoord, extMap_newCoord, extMap_liftOld D (isWeightedHomogeneous_form D hg c i), extMap_liftOld D (isWeightedHomogeneous_form D hg c j), hg.value c hc, hg.value c hc]`. Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem swap_mem (hg : D.IsFormSystem d g) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    (i j : Fin (D.size + 1)) :
    D.liftOld (g c i) * X (D.newCoord j) - D.liftOld (g c j) * X (D.newCoord i) ∈ D.extIdeal := by
  rw [AddBlockData.extIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, extMap_newCoord,
    extMap_newCoord, extMap_liftOld D (isWeightedHomogeneous_form D hg c i),
    extMap_liftOld D (isWeightedHomogeneous_form D hg c j), hg.value c hc, hg.value c hc]
  simp only [map_mul]
  ring

omit [Fintype ι] in

/- English proof (translation)
The claim follows from `fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)`.
-/
theorem mkF_X_ne_zero {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) (k : ι) :
    P.mkF (X ⟨k, c k⟩) ≠ 0 :=
  fun h ↦ hc k ((P.mkF_eq_zero_iff _).mp h)

/- English proof (translation)
Proceed by induction on `hu using Subring.closure_induction with`. Consider the case `mem x hx`. Take `⟨v, rfl⟩` from `hx`. Use `⟨1, X v * ∏ k ∈ Finset.univ.erase v.1, X ⟨k, c k⟩, ?_⟩` and prove the remaining obligations. Establish `hne` using `mkF_X_ne_zero hc v.1`.

Simplify using `only [ArithVariety.chartCoord, chartMonomial, Pi.one_apply, pow_one, map_prod, map_mul]`. Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ v.1)]`. Clear the denominators using the available nonvanishing facts. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `one => exact ⟨0, 1, by simp⟩`.

Consider the case `add x y _ _ hx hy`. Take `⟨e, f, hf⟩` from `hx`. Take `⟨e', f', hf'⟩` from `hy`. Use `⟨e + e', f * chartMonomial c 1 ^ e' + f' * chartMonomial c 1 ^ e, ?_⟩` and prove the remaining obligations. Simplify using `only [map_add, map_mul, map_pow, ← hf, ← hf']`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `neg x _ hx`. Take `⟨e, f, hf⟩` from `hx`. Use `⟨e, -f, ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, ← hf]`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `mul x y _ _ hx hy`. Take `⟨e, f, hf⟩` from `hx`. Take `⟨e', f', hf'⟩` from `hy`. Use `⟨e + e', f * f', ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ← hf, ← hf']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_clear_denom {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {u : P.FunField} (hu : u ∈ P.chartRing c) :
    ∃ (e : ℕ) (f : MvPolynomial (Coord n) ℤ), u * P.mkF (chartMonomial c 1) ^ e = P.mkF f := by
  induction hu using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    refine ⟨1, X v * ∏ k ∈ Finset.univ.erase v.1, X ⟨k, c k⟩, ?_⟩
    have hne := mkF_X_ne_zero hc v.1
    simp only [ArithVariety.chartCoord, chartMonomial, Pi.one_apply, pow_one, map_prod, map_mul]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v.1)]
    field_simp
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨e, f, hf⟩ := hx
    obtain ⟨e', f', hf'⟩ := hy
    refine ⟨e + e', f * chartMonomial c 1 ^ e' + f' * chartMonomial c 1 ^ e, ?_⟩
    simp only [map_add, map_mul, map_pow, ← hf, ← hf']
    ring
  | neg x _ hx =>
    obtain ⟨e, f, hf⟩ := hx
    refine ⟨e, -f, ?_⟩
    rw [map_neg, ← hf]
    ring
  | mul x y _ _ hx hy =>
    obtain ⟨e, f, hf⟩ := hx
    obtain ⟨e', f', hf'⟩ := hy
    refine ⟨e + e', f * f', ?_⟩
    rw [map_mul, ← hf, ← hf']
    ring

/- English proof (translation)
Use `choose e f hf using fun j ↦ exists_clear_denom hc (hu j)`. Use `⟨∑ j, e j, fun j ↦ f j * chartMonomial c 1 ^ (∑ i, e i - e j), fun j ↦ ?_⟩` and prove the remaining obligations. Establish `hle : e j ≤ ∑ i, e i` using `Finset.single_le_sum (fun i _ ↦ Nat.zero_le (e i)) (Finset.mem_univ j)`. Rewrite using `[map_mul, map_pow, ← hf j, ← Nat.add_sub_cancel' hle, pow_add, Nat.add_sub_cancel_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_common_denom {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {m : ℕ} {u : Fin m → P.FunField} (hu : ∀ j, u j ∈ P.chartRing c) :
    ∃ (E : ℕ) (f : Fin m → MvPolynomial (Coord n) ℤ),
      ∀ j, u j * P.mkF (chartMonomial c 1) ^ E = P.mkF (f j) := by
  choose e f hf using fun j ↦ exists_clear_denom hc (hu j)
  refine ⟨∑ j, e j, fun j ↦ f j * chartMonomial c 1 ^ (∑ i, e i - e j), fun j ↦ ?_⟩
  have hle : e j ≤ ∑ i, e i := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (e i)) (Finset.mem_univ j)
  rw [map_mul, map_pow, ← hf j, ← Nat.add_sub_cancel' hle, pow_add, Nat.add_sub_cancel_left]
  ring

/- English proof (translation)
Simplify using `only [chartMonomial, ArithVariety.chartPow, map_prod, map_pow]`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (mkF_X_ne_zero hc k), Int.toNat_of_nonneg (hd k)]`.
-/
theorem mkF_chartMonomial_mul_chartPow (hd : ∀ k, 0 ≤ (d k : ℤ) + D.deg k)
    {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c) :
    P.mkF (chartMonomial c d) * P.chartPow c D.deg =
      P.mkF (chartMonomial c fun k ↦ ((d k : ℤ) + D.deg k).toNat) := by
  simp only [chartMonomial, ArithVariety.chartPow, map_prod, map_pow]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (mkF_X_ne_zero hc k), Int.toNat_of_nonneg (hd k)]

/- English proof (translation)
Rewrite using `[chartMonomial, map_prod]`. Use `Submonoid.prod_mem _ fun k _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_pow, AddBlockData.liftOld, rename_X]`. Conclude with `Submonoid.pow_mem _ ((Ideal.mem_primeCompl_iff).mpr (hW k)) _`.
-/
theorem liftOld_chartMonomial_mem_primeCompl {W : Ideal (MvPolynomial (Coord D.extSizes) ℤ)} [W.IsPrime]
    {c : (k : ι) → Fin (n k + 1)} (hW : ∀ k, (X (D.oldCoord ⟨k, c k⟩) : MvPolynomial _ ℤ) ∉ W)
    (e : ι → ℕ) : D.liftOld (chartMonomial c e) ∈ W.primeCompl := by
  rw [chartMonomial, map_prod]
  refine Submonoid.prod_mem _ fun k _ ↦ ?_
  rw [map_pow, AddBlockData.liftOld, rename_X]
  exact Submonoid.pow_mem _ ((Ideal.mem_primeCompl_iff).mpr (hW k)) _

/- English proof (translation)
Take `⟨u, hu, hsum⟩` from `D.generating c hc`. Take `⟨E, f, hf⟩` from `exists_common_denom hc hu`. Establish `hsum' : ∑ j, u j * D.elt j = P.chartPow c D.deg`. Establish `hcp : P.chartPow c D.deg ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (mkF_X_ne_zero hc k)`. Rewrite using `[← one_mul (P.chartPow c D.deg), ← hsum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Use `set Q := chartMonomial c fun k ↦ ((d k : ℤ) + D.deg k).toNat`. Establish `hmem : ∑ j, f j * g c j - chartMonomial c 1 ^ E * Q ∈ P.ideal`. Rewrite using `[← P.mkF_eq_zero_iff, map_sub, map_sum, map_mul, map_pow, ← mkF_chartMonomial_mul_chartPow D hg.nonneg hc, ← hsum', sub_eq_zero, Finset.mul_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← hf j, hg.value c hc j]`. Expand and normalize the polynomial expressions, which then agree. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_not] at h`.

Establish `h1` using `hPW (liftOld_mem D hmem)`. Establish `h2 : D.liftOld (∑ j, f j * g c j) ∈ W`. Rewrite using `[map_sum]`. Conclude with `W.sum_mem fun j _ ↦ by rw [map_mul]; exact W.mul_mem_left _ (h j)`. Establish `h3 : D.liftOld (chartMonomial c 1 ^ E * Q) ∈ W`.

Use `W.sub_mem h2 h1` as an intermediate fact. Rewrite `this` using `[map_sub, sub_sub_cancel]`. Then use the resulting hypothesis. Rewrite `h3` using `[map_mul, map_pow]`. Conclude with `(Ideal.mem_primeCompl_iff.mp (W.primeCompl.mul_mem (W.primeCompl.pow_mem (liftOld_chartMonomial_mem_primeCompl D hW 1) E) (liftOld_chartMonomial_mem_primeCompl D hW _))) h3`.
-/
theorem exists_form_not_mem (hg : D.IsFormSystem d g) {c : (k : ι) → Fin (n k + 1)} (hc : P.IsLive c)
    {W : Ideal (MvPolynomial (Coord D.extSizes) ℤ)} [W.IsPrime] (hPW : D.extIdeal ≤ W)
    (hW : ∀ k, (X (D.oldCoord ⟨k, c k⟩) : MvPolynomial _ ℤ) ∉ W) :
    ∃ i, D.liftOld (g c i) ∉ W := by
  obtain ⟨u, hu, hsum⟩ := D.generating c hc
  obtain ⟨E, f, hf⟩ := exists_common_denom hc hu
  have hsum' : ∑ j, u j * D.elt j = P.chartPow c D.deg := by
    have hcp : P.chartPow c D.deg ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ ↦ zpow_ne_zero _ (mkF_X_ne_zero hc k)
    rw [← one_mul (P.chartPow c D.deg), ← hsum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    field_simp
  set Q := chartMonomial c fun k ↦ ((d k : ℤ) + D.deg k).toNat
  have hmem : ∑ j, f j * g c j - chartMonomial c 1 ^ E * Q ∈ P.ideal := by
    rw [← P.mkF_eq_zero_iff, map_sub, map_sum, map_mul, map_pow,
      ← mkF_chartMonomial_mul_chartPow D hg.nonneg hc, ← hsum', sub_eq_zero, Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_mul, ← hf j, hg.value c hc j]
    ring
  by_contra h
  simp only [not_exists, not_not] at h
  have h1 := hPW (liftOld_mem D hmem)
  have h2 : D.liftOld (∑ j, f j * g c j) ∈ W := by
    rw [map_sum]
    exact W.sum_mem fun j _ ↦ by rw [map_mul]; exact W.mul_mem_left _ (h j)
  have h3 : D.liftOld (chartMonomial c 1 ^ E * Q) ∈ W := by
    have := W.sub_mem h2 h1
    rwa [map_sub, sub_sub_cancel] at this
  rw [map_mul, map_pow] at h3
  exact (Ideal.mem_primeCompl_iff.mp (W.primeCompl.mul_mem
    (W.primeCompl.pow_mem (liftOld_chartMonomial_mem_primeCompl D hW 1) E)
    (liftOld_chartMonomial_mem_primeCompl D hW _))) h3

end AddBlock

/- English proof (translation)
Introduce `ι _ _ n P D d g hg c j hgc W`. Unfold `NumbersDVR.ratDiv`. Rewrite using `[sub_eq_zero]`. Establish `hc : P.IsLive c`. Assume the negation of the conclusion as `hc`.

Conclude with `hgc (by rw [hg.dead c hc j, map_zero]; exact Submodule.zero_mem _)`. Distinguish the cases in `hW : W.IsPrime ∧ NumbersDVR.IsRelevant W ∧ D.extIdeal ≤ W`. Use `swap`. Rewrite using `[divCycle_eq_zero _ hW, divCycle_eq_zero _ hW]`. Take `⟨hWp, hrel, hPW⟩` from `hW`.

Use `hWp` as an intermediate fact. Use `choose c' hc'W using fun k : ι ↦ hrel (some k)`. Take `⟨j', hj'W⟩` from `hrel none`. Set `c'' : (k : ι) → Fin (n k + 1)` to `c'`. Establish `hWc : ∀ k, (X (D.oldCoord ⟨k, c'' k⟩) : MvPolynomial _ ℤ) ∉ W` using `hc'W`.

Establish `hlive : P.IsLive c''` using `fun k hk ↦ by`. Establish `h` using `hPW (liftOld_mem D hk)`. Rewrite `h` using `[AddBlockData.liftOld, rename_X]`. Conclude with `hWc k h`. Take `⟨i, hi⟩` from `exists_form_not_mem D hg hlive hPW hWc`.

Establish `hj'' : (X (D.newCoord j') : MvPolynomial (Coord D.extSizes) ℤ) ∉ W` using `hj'W`. Establish `hg' : D.liftOld (g c'' j') ∉ W`. Introduce `hmem`. Establish `hs` using `hPW (swap_mem D hg hlive i j')`. Establish `: D.liftOld (g c'' i) * X (D.newCoord j') ∈ W`.

Use `W.add_mem hs (W.mul_mem_right (X (D.newCoord i)) hmem)` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Break down `Ideal.IsPrime.mem_or_mem hWp this with h | h` into its components or cases. Conclude with `hi h`. Conclude with `hj'' h`.

Establish `hf' : X (D.newCoord j') * D.liftOld (chartMonomial c'' d) ∉ W`. Introduce `hmem`. Break down `Ideal.IsPrime.mem_or_mem hWp hmem with h | h` into its components or cases. Conclude with `hj'' h`. Conclude with `Ideal.mem_primeCompl_iff.mp (liftOld_chartMonomial_mem_primeCompl D hWc d) h`.

Conclude with `divCycle_eq_of_cross _ hf' hg' (cross_mem D hg hc hlive j j')`.
-/
theorem proof : SectionCycle.Statement := by
  intro ι _ _ n P D d g hg c j hgc W
  unfold NumbersDVR.ratDiv
  rw [sub_eq_zero]
  have hc : P.IsLive c := by
    by_contra hc
    exact hgc (by rw [hg.dead c hc j, map_zero]; exact Submodule.zero_mem _)
  by_cases hW : W.IsPrime ∧ NumbersDVR.IsRelevant W ∧ D.extIdeal ≤ W
  swap
  · rw [divCycle_eq_zero _ hW, divCycle_eq_zero _ hW]
  obtain ⟨hWp, hrel, hPW⟩ := hW
  have := hWp
  choose c' hc'W using fun k : ι ↦ hrel (some k)
  obtain ⟨j', hj'W⟩ := hrel none
  let c'' : (k : ι) → Fin (n k + 1) := c'
  have hWc : ∀ k, (X (D.oldCoord ⟨k, c'' k⟩) : MvPolynomial _ ℤ) ∉ W := hc'W
  have hlive : P.IsLive c'' := fun k hk ↦ by
    have h := hPW (liftOld_mem D hk)
    rw [AddBlockData.liftOld, rename_X] at h
    exact hWc k h
  obtain ⟨i, hi⟩ := exists_form_not_mem D hg hlive hPW hWc
  have hj'' : (X (D.newCoord j') : MvPolynomial (Coord D.extSizes) ℤ) ∉ W := hj'W
  have hg' : D.liftOld (g c'' j') ∉ W := by
    intro hmem
    have hs := hPW (swap_mem D hg hlive i j')
    have : D.liftOld (g c'' i) * X (D.newCoord j') ∈ W := by
      have := W.add_mem hs (W.mul_mem_right (X (D.newCoord i)) hmem)
      rwa [sub_add_cancel] at this
    rcases Ideal.IsPrime.mem_or_mem hWp this with h | h
    · exact hi h
    · exact hj'' h
  have hf' : X (D.newCoord j') * D.liftOld (chartMonomial c'' d) ∉ W := by
    intro hmem
    rcases Ideal.IsPrime.mem_or_mem hWp hmem with h | h
    · exact hj'' h
    · exact Ideal.mem_primeCompl_iff.mp (liftOld_chartMonomial_mem_primeCompl D hWc d) h
  exact divCycle_eq_of_cross _ hf' hg' (cross_mem D hg hc hlive j j')

end SectionCycle

end

end GroundTheory.Heights₂.Heights
