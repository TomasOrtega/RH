import Development.EtaleCohomology.EtaleSheaves.FibreEqvPf

noncomputable section
open Polynomial GlobalTheory.EtC

namespace LateralTheory.E.SpecAICPf

/- English proof (translation)
Introduce `p hp hd`. Take `⟨a, ha⟩` from `h (p.map e.symm.toRingHom) (hp.map _) (by rwa [natDegree_map_eq_of_injective e.symm.injective])`. Use `⟨e a, ?_⟩` and prove the remaining obligations. Use `congrArg e ha` as an intermediate fact. Rewrite `this` using `[eval_map, ← coe_eval₂RingHom, map_zero]`.

Rewrite using `[← this]`. Simplify using `[eval₂_eq_sum_range, eval_eq_sum_range, map_sum]`.
-/
theorem aic_equiv {A A' : Type} [CommRing A] [CommRing A'] (e : A ≃+* A') (h : AIC A) : AIC A' := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map e.symm.toRingHom) (hp.map _) (by rwa [natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  have := congrArg e ha
  rw [eval_map, ← coe_eval₂RingHom, map_zero] at this
  rw [← this]
  simp [eval₂_eq_sum_range, eval_eq_sum_range, map_sum]

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hp hn`. Rewrite using `[eq_one_of_monic_natDegree_zero hp hn]`.

Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `p hp hn`. Take `⟨a, ha⟩` from `h p hp (by omega)`. Establish `hdeg : (p /ₘ (X - C a)).natDegree = n`.

Rewrite using `[natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Establish `e` using `mul_divByMonic_eq_iff_isRoot.2 ha`. Establish `hq : (p /ₘ (X - C a)).Monic` using `Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [e]; exact hp)`. Rewrite using `[← e, roots_mul (by rw [e]; exact hp.ne_zero), roots_X_sub_C, Multiset.card_add, ih _ hq hdeg]`.

Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.
-/
theorem card_roots_of_aic {A : Type} [CommRing A] [IsDomain A] (h : AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.Monic → p.natDegree = n → Multiset.card p.roots = n := by
  intro n
  induction n with
  | zero =>
    intro p hp hn
    rw [eq_one_of_monic_natDegree_zero hp hn]; simp
  | succ n ih =>
    intro p hp hn
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdeg : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    have e := mul_divByMonic_eq_iff_isRoot.2 ha
    have hq : (p /ₘ (X - C a)).Monic := Monic.of_mul_monic_left (monic_X_sub_C a) (by rw [e]; exact hp)
    rw [← e, roots_mul (by rw [e]; exact hp.ne_zero), roots_X_sub_C, Multiset.card_add, ih _ hq hdeg]
    simp; omega

/- English proof (translation)
Introduce `p hp hd`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset M (Finset.image p.coeff (Finset.range (p.natDegree + 1)))`. Use `set r : S := algebraMap B S b`. Establish `hl : p.scaleRoots r ∈ lifts (algebraMap B S)`. Rewrite using `[lifts_iff_coeff_lifts]`.

Introduce `i`. Rewrite using `[coeff_scaleRoots]`. Break down `lt_trichotomy i p.natDegree with hi | hi | hi` into its components or cases. Take `⟨t, ht⟩` from `hb (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)`. Use `⟨t * b ^ (p.natDegree - (i + 1)), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, ht, map_pow, Algebra.smul_def]`. Simplify using `only [r]`. Establish `: p.natDegree - i = (p.natDegree - (i + 1)) + 1` using `by omega`. Rewrite using `[this, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Substitute `hi; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩` using the available equality. Rewrite using `[coeff_eq_zero_of_natDegree_lt hi]; exact ⟨0, by simp⟩`. Take `⟨q, hq, hqd, hqm⟩` from `lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff r).2 hp)`. Take `⟨β, hβ⟩` from `h q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)`. Establish `hru : IsUnit r` using `IsLocalization.map_units S b`.

Use `⟨algebraMap B S β * hru.unit⁻¹, ?_⟩` and prove the remaining obligations. Establish `h1` using `scaleRoots_eval₂_mul (p := p) (RingHom.id S) (algebraMap B S β * hru.unit⁻¹) r`. Simplify using `only [eval₂_id, RingHom.id_apply] at h1`. Establish `h2 : r * (algebraMap B S β * hru.unit⁻¹) = algebraMap B S β`. Rewrite using `[mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]`.

Rewrite `h1` using `[h2, ← hq, eval_map, eval₂_hom, hβ, map_zero]`. Conclude with `(hru.pow _).mul_right_eq_zero.1 h1.symm`.
-/
theorem aic_localization {B S : Type} [CommRing B] [CommRing S] [Algebra B S] (M : Submonoid B)
    [IsLocalization M S] (h : AIC B) : AIC S := by
  classical
  intro p hp hd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset M (Finset.image p.coeff (Finset.range (p.natDegree + 1)))
  set r : S := algebraMap B S b
  have hl : p.scaleRoots r ∈ lifts (algebraMap B S) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · obtain ⟨t, ht⟩ := hb (p.coeff i) (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), rfl⟩)
      refine ⟨t * b ^ (p.natDegree - (i + 1)), ?_⟩
      rw [map_mul, ht, map_pow, Algebra.smul_def]
      simp only [r]
      have : p.natDegree - i = (p.natDegree - (i + 1)) + 1 := by omega
      rw [this, pow_succ]; ring
    · subst hi; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt hi]; exact ⟨0, by simp⟩
  obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hl ((monic_scaleRoots_iff r).2 hp)
  obtain ⟨β, hβ⟩ := h q hqm (by rw [hqd, natDegree_scaleRoots]; exact hd)
  have hru : IsUnit r := IsLocalization.map_units S b
  refine ⟨algebraMap B S β * hru.unit⁻¹, ?_⟩
  have h1 := scaleRoots_eval₂_mul (p := p) (RingHom.id S) (algebraMap B S β * hru.unit⁻¹) r
  simp only [eval₂_id, RingHom.id_apply] at h1
  have h2 : r * (algebraMap B S β * hru.unit⁻¹) = algebraMap B S β := by
    rw [mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]
  rw [h2, ← hq, eval_map, eval₂_hom, hβ, map_zero] at h1
  exact (hru.pow _).mul_right_eq_zero.1 h1.symm

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap R L)`. Introduce `a b hab`. Conclude with `hK (congrArg Subtype.val hab)`. Establish `hc : Multiset.card (p.map (algebraMap R L)).roots = p.natDegree`. Rewrite using `[card_roots_of_aic hL _ _ (hp.map _) rfl, natDegree_map_eq_of_injective hinj]`.

Use `⟨?_, hc⟩` and prove the remaining obligations. Rewrite using `[roots_map_of_injective_of_card_eq_natDegree (f := L.val.toRingHom) Subtype.val_injective (by rw [hc, natDegree_map_eq_of_injective hinj]), map_map]`. Both sides reduce to the same expression.
-/
theorem roots_eq {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] (hK : Function.Injective (algebraMap R K)) (L : Subalgebra R K) (hL : AIC L)
    (p : R[X]) (hp : p.Monic) : (p.map (algebraMap R L)).roots.map L.val.toRingHom = (p.map (algebraMap R K)).roots ∧
      Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
  have hinj : Function.Injective (algebraMap R L) := by
    intro a b hab
    exact hK (congrArg Subtype.val hab)
  have hc : Multiset.card (p.map (algebraMap R L)).roots = p.natDegree := by
    rw [card_roots_of_aic hL _ _ (hp.map _) rfl, natDegree_map_eq_of_injective hinj]
  refine ⟨?_, hc⟩
  rw [roots_map_of_injective_of_card_eq_natDegree (f := L.val.toRingHom) Subtype.val_injective
    (by rw [hc, natDegree_map_eq_of_injective hinj]), map_map]
  rfl

/- English proof (translation)
Introduce `p hp hd`. Set `K` to `FractionRing R`. Set `L : MaximalSpectrum R → Subalgebra R K` to `fun v => Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors`. Establish `hL : ∀ v, AIC (L v)` using `fun v => aic_equiv (IsLocalization.algEquiv v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal) (L v)).toRingEquiv (h v)`. Take `⟨m, hm⟩` from `Ideal.exists_maximal R`.

Take `⟨e0, c0⟩` from `roots_eq (IsFractionRing.injective R K) (L ⟨m, hm⟩) (hL _) p hp`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, x ∈ (p.map (algebraMap R K)).roots := by`. Rewrite using `[← e0]`. Apply `Multiset.exists_mem_of_ne_zero` to reduce the goal to its premises. Introduce `h0`.

Rewrite `h0` using `[Multiset.map_eq_zero]`. Rewrite `c0` using `[h0]`. Simplify using `at c0`. Use linear arithmetic over natural numbers and integers. Establish `hmem : x ∈ (⊥ : Subalgebra R K)`.

Rewrite using `[← MaximalSpectrum.iInf_localization_eq_bot R K, Algebra.mem_iInf]`. Introduce `v`. Rewrite `hx` using `[← (roots_eq (IsFractionRing.injective R K) (L v) (hL v) p hp).1]`. Take `⟨y, -, rfl⟩` from `Multiset.mem_map.1 hx`. Conclude with `y.2`.

Take `⟨a, rfl⟩` from `Algebra.mem_bot.1 hmem`. Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `hr` using `(mem_roots (hp.map _).ne_zero).1 hx`. Rewrite `hr` using `[IsRoot, eval_map, eval₂_hom]`. Conclude with `(IsFractionRing.injective R K) (by rw [hr, map_zero])`.
-/
theorem aic_of_local {R : Type} [CommRing R] [IsDomain R]
    (h : ∀ v : MaximalSpectrum R, AIC (Localization.AtPrime v.asIdeal)) : AIC R := by
  classical
  intro p hp hd
  let K := FractionRing R
  let L : MaximalSpectrum R → Subalgebra R K := fun v =>
    Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors
  have hL : ∀ v, AIC (L v) := fun v =>
    aic_equiv (IsLocalization.algEquiv v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal) (L v)).toRingEquiv (h v)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  obtain ⟨e0, c0⟩ := roots_eq (IsFractionRing.injective R K) (L ⟨m, hm⟩) (hL _) p hp
  obtain ⟨x, hx⟩ : ∃ x, x ∈ (p.map (algebraMap R K)).roots := by
    rw [← e0]
    apply Multiset.exists_mem_of_ne_zero
    intro h0
    rw [Multiset.map_eq_zero] at h0
    rw [h0] at c0; simp at c0; omega
  have hmem : x ∈ (⊥ : Subalgebra R K) := by
    rw [← MaximalSpectrum.iInf_localization_eq_bot R K, Algebra.mem_iInf]
    intro v
    rw [← (roots_eq (IsFractionRing.injective R K) (L v) (hL v) p hp).1] at hx
    obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hx
    exact y.2
  obtain ⟨a, rfl⟩ := Algebra.mem_bot.1 hmem
  refine ⟨a, ?_⟩
  have hr := (mem_roots (hp.map _).ne_zero).1 hx
  rw [IsRoot, eval_map, eval₂_hom] at hr
  exact (IsFractionRing.injective R K) (by rw [hr, map_zero])

end LateralTheory.E.SpecAICPf

namespace LateralTheory.E.SpecAICPf

open CategoryTheory AlgebraicGeometry

/- English proof (translation)
Establish `: x.asIdeal.IsPrime` using `x.isPrime`. Set `_ : Algebra B ((Spec B).presheaf.stalk x)` to `StructureSheaf.stalkAlgebra B x`. Establish `: IsLocalization.AtPrime ((Spec B).presheaf.stalk x) x.asIdeal` using `StructureSheaf.IsLocalization.to_stalk B x`. Conclude with `aic_localization x.asIdeal.primeCompl hA`.
-/
theorem stalk_aic (B : CommRingCat.{0}) (hA : AIC B) (x : Spec B) : AIC ((Spec B).presheaf.stalk x) := by
  have : x.asIdeal.IsPrime := x.isPrime
  let _ : Algebra B ((Spec B).presheaf.stalk x) := StructureSheaf.stalkAlgebra B x
  have : IsLocalization.AtPrime ((Spec B).presheaf.stalk x) x.asIdeal := StructureSheaf.IsLocalization.to_stalk B x
  exact aic_localization x.asIdeal.primeCompl hA

/- English proof (translation)
Introduce `B hB hA`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations. Introduce `U hU hne`. Use `haveI : Nonempty U := hne.to_subtype`. Apply `aic_of_local` to reduce the goal to its premises.

Introduce `v`. Set `y : PrimeSpectrum Γ(Spec B, U)` to `⟨v.asIdeal, v.isMaximal.isPrime⟩`. Establish `hy : hU.fromSpec y ∈ U` using `by show hU.fromSpec y ∈ (U : Set (Spec B))`. Rewrite using `[← hU.range_fromSpec]`. Conclude with `⟨y, rfl⟩`.

Use `letI := TopCat.Presheaf.algebra_section_stalk (Spec B).presheaf ⟨hU.fromSpec y, hy⟩`. Establish `hloc : IsLocalization.AtPrime ((Spec B).presheaf.stalk (hU.fromSpec y)) y.asIdeal` using `hU.isLocalization_stalk' y hy`. Establish `hst` using `stalk_aic B hA (hU.fromSpec y)`. Conclude with `aic_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl ((Spec B).presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime v.asIdeal)).toRingEquiv hst`.
-/
theorem SpecAIC_of : LateralTheory.E.FibreEqvPf.SpecAIC := by
  intro B hB hA
  refine ⟨inferInstance, ?_⟩
  intro U hU hne
  haveI : Nonempty U := hne.to_subtype
  apply aic_of_local
  intro v
  let y : PrimeSpectrum Γ(Spec B, U) := ⟨v.asIdeal, v.isMaximal.isPrime⟩
  have hy : hU.fromSpec y ∈ U := by
    show hU.fromSpec y ∈ (U : Set (Spec B))
    rw [← hU.range_fromSpec]; exact ⟨y, rfl⟩
  letI := TopCat.Presheaf.algebra_section_stalk (Spec B).presheaf ⟨hU.fromSpec y, hy⟩
  have hloc : IsLocalization.AtPrime ((Spec B).presheaf.stalk (hU.fromSpec y)) y.asIdeal := hU.isLocalization_stalk' y hy
  have hst := stalk_aic B hA (hU.fromSpec y)
  exact aic_equiv (IsLocalization.algEquiv y.asIdeal.primeCompl ((Spec B).presheaf.stalk (hU.fromSpec y))
    (Localization.AtPrime v.asIdeal)).toRingEquiv hst

end LateralTheory.E.SpecAICPf
