import Mathlib

open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `h1' : d.natAbs ∣ m ^ k`. Use `Int.natAbs_dvd_natAbs.mpr h1` as an intermediate fact. Simplify `this` using `[Int.natAbs_pow]`. Establish `hc : Nat.Coprime m d.natAbs`. Rewrite using `[hm.coprime_iff_not_dvd]`.

Introduce `h`. Conclude with `h2 (Int.natCast_dvd.mpr h)`. Conclude with `Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hc).symm h1'`.
-/
private lemma natAbs_eq_one_of_dvd_prime_pow_not_dvd {d : ℤ} {m k : ℕ} (hm : m.Prime) (h1 : d ∣ (m : ℤ) ^ k)
    (h2 : ¬ (m : ℤ) ∣ d) : d.natAbs = 1 := by
  have h1' : d.natAbs ∣ m ^ k := by
    have := Int.natAbs_dvd_natAbs.mpr h1
    simpa [Int.natAbs_pow] using this
  have hc : Nat.Coprime m d.natAbs := by
    rw [hm.coprime_iff_not_dvd]
    intro h
    exact h2 (Int.natCast_dvd.mpr h)
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_left k hc).symm h1'

/- English proof (translation)
Establish `: NeZero m` using `⟨hm.ne_zero⟩`. Establish `: Fact m.Prime` using `⟨hm⟩`. Set `E` to `CyclotomicField m K`. Establish `: FiniteDimensional ℚ E` using `Module.Finite.trans K E`. Establish `hζ` using `IsCyclotomicExtension.zeta_spec m K E`.

Use `set ζ := IsCyclotomicExtension.zeta m K E`. Set `A : IntermediateField ℚ E` to `IntermediateField.adjoin ℚ {ζ}`. Set `B : IntermediateField ℚ E` to `(IsScalarTower.toAlgHom ℚ K E).fieldRange`. Establish `hAc : IsCyclotomicExtension {m} ℚ A` using `hζ.intermediateField_adjoin_isCyclotomicExtension ℚ`. Establish `hGal : IsGalois ℚ A` using `IsCyclotomicExtension.isGalois {m} ℚ A`.

Establish `hinf : A ⊓ B = ⊥`. Set `F : IntermediateField ℚ E` to `A ⊓ B`. Set `_ : Algebra F A` to `(IntermediateField.inclusion (inf_le_left : F ≤ A)).toRingHom.toAlgebra`. Set `_ : Algebra F K` to `(((IsScalarTower.toAlgHom ℚ K E).equivFieldRange.symm.toAlgHom).comp (IntermediateField.inclusion (inf_le_right : F ≤ B))).toRingHom.toAlgebra`. Establish `hFA : NumberField.discr F ∣ NumberField.discr A` using `NumberField.discr_dvd_discr F A`.

Establish `hFK : NumberField.discr F ∣ NumberField.discr K` using `NumberField.discr_dvd_discr F K`. Establish `hA : NumberField.discr A = (-1) ^ ((m - 1) / 2) * (m : ℤ) ^ (m - 2)` using `IsCyclotomicExtension.Rat.discr_prime m A`. Establish `hpow : NumberField.discr F ∣ (m : ℤ) ^ (m - 2)`. Establish `: NumberField.discr F ∣ (-1) ^ ((m - 1) / 2) * (m : ℤ) ^ (m - 2)` using `hA ▸ hFA`. Conclude with `(IsUnit.dvd_mul_left ((isUnit_neg_one).pow _)).mp this`.

Establish `hnd : ¬ (m : ℤ) ∣ NumberField.discr F` using `fun h => hd (h.trans hFK)`. Establish `h1 : (NumberField.discr F).natAbs = 1` using `natAbs_eq_one_of_dvd_prime_pow_not_dvd hm hpow hnd`. Establish `hrank : Module.finrank ℚ F = 1`. Assume the negation of the conclusion as `hne`. Establish `hgt : 1 < Module.finrank ℚ F` using `lt_of_le_of_ne Module.finrank_pos (Ne.symm hne)`.

Establish `h2` using `NumberField.abs_discr_gt_two hgt`. Rewrite `h2` using `[Int.abs_eq_natAbs, h1]`. Evaluate the numerical expressions using `at h2`. Conclude with `IntermediateField.finrank_eq_one_iff.mp hrank`. Establish `hdis : A.LinearDisjoint B` using `@IntermediateField.LinearDisjoint.of_inf_eq_bot _ _ _ _ _ A B (by exact hGal) _ _ hinf`.

Establish `e1 : (IsScalarTower.toAlgHom ℚ K E).range = B.toSubalgebra` using `(AlgHom.fieldRange_toSubalgebra _).symm`. Establish `hdisK : A.LinearDisjoint K`. Rewrite using `[IntermediateField.linearDisjoint_iff, e1]`. Conclude with `IntermediateField.linearDisjoint_iff'.mp hdis`. Establish `hrk : Module.rank K (IntermediateField.adjoin K (A : Set E)) = Module.rank ℚ A` using `hdisK.adjoin_rank_eq_rank_left_of_isAlgebraic_left`.

Establish `htop : IntermediateField.adjoin K {ζ} = ⊤`. Rewrite using `[← IntermediateField.toSubalgebra_inj, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic ζ), IntermediateField.top_toSubalgebra]`. Conclude with `IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ`. Establish `htop' : IntermediateField.adjoin K (A : Set E) = ⊤`. Use `top_le_iff.mp (htop ▸ ?_)` and prove the remaining obligations.

Conclude with `IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (IntermediateField.subset_adjoin K (A : Set E) (IntermediateField.mem_adjoin_simple_self ℚ ζ)))`. Establish `hfinA : Module.finrank ℚ A = m.totient` using `IsCyclotomicExtension.finrank A (cyclotomic.irreducible_rat hm.pos)`. Establish `hfinE : Module.finrank K E = m.totient`. Establish `h' : Module.finrank K (IntermediateField.adjoin K (A : Set E)) = m.totient`. Rewrite using `[Module.finrank, hrk]`.

Conclude with `hfinA`. Rewrite `h'` using `[htop', IntermediateField.finrank_top']`. Then use the resulting hypothesis. Establish `hint : IsIntegral K ζ` using `Algebra.IsIntegral.isIntegral ζ`. Establish `hdeg : (minpoly K ζ).natDegree = m.totient`. Rewrite using `[← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top', hfinE]`.

Establish `hdvd : minpoly K ζ ∣ cyclotomic m K`. Apply `minpoly.dvd` to reduce the goal to its premises. Rewrite using `[aeval_def, eval₂_eq_eval_map, map_cyclotomic]`. Conclude with `hζ.isRoot_cyclotomic hm.pos`. Establish `heq : cyclotomic m K = minpoly K ζ` using `eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m K) hdvd (by rw [natDegree_cyclotomic, hdeg])`.

Rewrite using `[heq]`. Conclude with `minpoly.irreducible hint`.
-/
theorem irreducible_cyclotomic_of_not_dvd_discr (K : Type) [Field K] [NumberField K] (m : ℕ)
    (hm : m.Prime) (hd : ¬ (m : ℤ) ∣ discr K) : Irreducible (cyclotomic m K) := by
  have : NeZero m := ⟨hm.ne_zero⟩
  have : Fact m.Prime := ⟨hm⟩
  let E := CyclotomicField m K
  have : FiniteDimensional ℚ E := Module.Finite.trans K E
  have hζ := IsCyclotomicExtension.zeta_spec m K E
  set ζ := IsCyclotomicExtension.zeta m K E
  let A : IntermediateField ℚ E := IntermediateField.adjoin ℚ {ζ}
  let B : IntermediateField ℚ E := (IsScalarTower.toAlgHom ℚ K E).fieldRange
  have hAc : IsCyclotomicExtension {m} ℚ A := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have hGal : IsGalois ℚ A := IsCyclotomicExtension.isGalois {m} ℚ A
  have hinf : A ⊓ B = ⊥ := by
    let F : IntermediateField ℚ E := A ⊓ B
    let _ : Algebra F A := (IntermediateField.inclusion (inf_le_left : F ≤ A)).toRingHom.toAlgebra
    let _ : Algebra F K := (((IsScalarTower.toAlgHom ℚ K E).equivFieldRange.symm.toAlgHom).comp
      (IntermediateField.inclusion (inf_le_right : F ≤ B))).toRingHom.toAlgebra
    have hFA : NumberField.discr F ∣ NumberField.discr A := NumberField.discr_dvd_discr F A
    have hFK : NumberField.discr F ∣ NumberField.discr K := NumberField.discr_dvd_discr F K
    have hA : NumberField.discr A = (-1) ^ ((m - 1) / 2) * (m : ℤ) ^ (m - 2) :=
      IsCyclotomicExtension.Rat.discr_prime m A
    have hpow : NumberField.discr F ∣ (m : ℤ) ^ (m - 2) := by
      have : NumberField.discr F ∣ (-1) ^ ((m - 1) / 2) * (m : ℤ) ^ (m - 2) := hA ▸ hFA
      exact (IsUnit.dvd_mul_left ((isUnit_neg_one).pow _)).mp this
    have hnd : ¬ (m : ℤ) ∣ NumberField.discr F := fun h => hd (h.trans hFK)
    have h1 : (NumberField.discr F).natAbs = 1 := natAbs_eq_one_of_dvd_prime_pow_not_dvd hm hpow hnd
    have hrank : Module.finrank ℚ F = 1 := by
      by_contra hne
      have hgt : 1 < Module.finrank ℚ F := lt_of_le_of_ne Module.finrank_pos (Ne.symm hne)
      have h2 := NumberField.abs_discr_gt_two hgt
      rw [Int.abs_eq_natAbs, h1] at h2
      norm_num at h2
    exact IntermediateField.finrank_eq_one_iff.mp hrank
  have hdis : A.LinearDisjoint B :=
    @IntermediateField.LinearDisjoint.of_inf_eq_bot _ _ _ _ _ A B (by exact hGal) _ _ hinf
  have e1 : (IsScalarTower.toAlgHom ℚ K E).range = B.toSubalgebra :=
    (AlgHom.fieldRange_toSubalgebra _).symm
  have hdisK : A.LinearDisjoint K := by
    rw [IntermediateField.linearDisjoint_iff, e1]
    exact IntermediateField.linearDisjoint_iff'.mp hdis
  have hrk : Module.rank K (IntermediateField.adjoin K (A : Set E)) = Module.rank ℚ A :=
    hdisK.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  have htop : IntermediateField.adjoin K {ζ} = ⊤ := by
    rw [← IntermediateField.toSubalgebra_inj,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic ζ),
      IntermediateField.top_toSubalgebra]
    exact IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have htop' : IntermediateField.adjoin K (A : Set E) = ⊤ := by
    refine top_le_iff.mp (htop ▸ ?_)
    exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr
      (IntermediateField.subset_adjoin K (A : Set E) (IntermediateField.mem_adjoin_simple_self ℚ ζ)))
  have hfinA : Module.finrank ℚ A = m.totient := IsCyclotomicExtension.finrank A (cyclotomic.irreducible_rat hm.pos)
  have hfinE : Module.finrank K E = m.totient := by
    have h' : Module.finrank K (IntermediateField.adjoin K (A : Set E)) = m.totient := by
      rw [Module.finrank, hrk]
      exact hfinA
    rwa [htop', IntermediateField.finrank_top'] at h'
  have hint : IsIntegral K ζ := Algebra.IsIntegral.isIntegral ζ
  have hdeg : (minpoly K ζ).natDegree = m.totient := by
    rw [← IntermediateField.adjoin.finrank hint, htop, IntermediateField.finrank_top', hfinE]
  have hdvd : minpoly K ζ ∣ cyclotomic m K := by
    apply minpoly.dvd
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hζ.isRoot_cyclotomic hm.pos
  have heq : cyclotomic m K = minpoly K ζ :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic m K) hdvd
      (by rw [natDegree_cyclotomic, hdeg])
  rw [heq]
  exact minpoly.irreducible hint

/- English proof (translation)
Introduce `K _ _ n hn`. Take `⟨m, hmp, hgt, hmod⟩` from `Nat.exists_prime_gt_modEq_one (NumberField.discr K).natAbs hn`. Use `⟨m, hmp, (Nat.modEq_iff_dvd' hmp.one_le).mp hmod.symm, ?_⟩` and prove the remaining obligations. Apply `irreducible_cyclotomic_of_not_dvd_discr K m hmp` to reduce the goal to its premises. Introduce `h`.

Establish `hne : NumberField.discr K ≠ 0` using `NumberField.discr_ne_zero K`. Use `Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natCast_dvd.mp h)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_prime_dvd_sub_one_irreducible_cyclotomic :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), n ≠ 0 →
      ∃ m : ℕ, m.Prime ∧ n ∣ m - 1 ∧ Irreducible (cyclotomic m K) := by
  intro K _ _ n hn
  obtain ⟨m, hmp, hgt, hmod⟩ := Nat.exists_prime_gt_modEq_one (NumberField.discr K).natAbs hn
  refine ⟨m, hmp, (Nat.modEq_iff_dvd' hmp.one_le).mp hmod.symm, ?_⟩
  apply irreducible_cyclotomic_of_not_dvd_discr K m hmp
  intro h
  have hne : NumberField.discr K ≠ 0 := NumberField.discr_ne_zero K
  have := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) (Int.natCast_dvd.mp h)
  omega

end GlobalTheory
