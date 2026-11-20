import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.WitBase

open Polynomial

noncomputable section

namespace PI.SqfRootsInj.W

open PI.SqfLab

section
variable {g : ℕ} [Fact g.Prime]

/- English proof (translation)
Take `⟨hmon, hdeg, hc0⟩` from `hf`. Establish `hf0 : f ≠ 0` using `hmon.ne_zero`. Establish `hroot : aeval x f = 0`. Unfold `rootsBar at hx`. Rewrite `hx` using `[mem_roots']`.

Rewrite using `[← eval_map_algebraMap]`. Conclude with `hx.2`. Establish `hint : IsIntegral (ZMod g) x` using `Algebra.IsIntegral.isIntegral x`. Establish `hdvd` using `minpoly.dvd (ZMod g) x hroot`. Use `⟨?_, hdvd, ?_, minpoly.natDegree_pos hint⟩` and prove the remaining obligations.

Introduce and unpack `rfl`. Apply `hc0` to reduce the goal to its premises. Establish `h0` using `coeff_zero_eq_aeval_zero' (A := Fbar g) f`. Rewrite `h0` using `[hroot]`. Conclude with `(algebraMap (ZMod g) (Fbar g)).injective (by rw [h0, map_zero])`.

Rewrite using `[← hdeg]`. Conclude with `natDegree_le_of_dvd hdvd hf0`.
-/
theorem root_facts {r : ℕ} {f : (ZMod g)[X]} (hf : IsLab g r f) {x : Fbar g}
    (hx : x ∈ rootsBar f) :
    x ≠ 0 ∧ minpoly (ZMod g) x ∣ f ∧ (minpoly (ZMod g) x).natDegree ≤ r ∧
      1 ≤ (minpoly (ZMod g) x).natDegree := by
  obtain ⟨hmon, hdeg, hc0⟩ := hf
  have hf0 : f ≠ 0 := hmon.ne_zero
  have hroot : aeval x f = 0 := by
    unfold rootsBar at hx
    rw [mem_roots'] at hx
    rw [← eval_map_algebraMap]
    exact hx.2
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hdvd := minpoly.dvd (ZMod g) x hroot
  refine ⟨?_, hdvd, ?_, minpoly.natDegree_pos hint⟩
  · rintro rfl
    apply hc0
    have h0 := coeff_zero_eq_aeval_zero' (A := Fbar g) f
    rw [hroot] at h0
    exact (algebraMap (ZMod g) (Fbar g)).injective (by rw [h0, map_zero])
  · rw [← hdeg]
    exact natDegree_le_of_dvd hdvd hf0

/- English proof (translation)
Establish `h2 : x ^ (q - 1) * x = 1 * x` using `by rw [← pow_succ, Nat.sub_add_cancel hq, h, one_mul]`. Conclude with `mul_right_cancel₀ hx h2`.
-/
theorem pow_pred_eq_one' {K : Type*} [Field K] {x : K} (hx : x ≠ 0) {q : ℕ} (hq : 1 ≤ q)
    (h : x ^ q = x) : x ^ (q - 1) = 1 := by
  have h2 : x ^ (q - 1) * x = 1 * x := by rw [← pow_succ, Nat.sub_add_cancel hq, h, one_mul]
  exact mul_right_cancel₀ hx h2

/- English proof (translation)
Take `⟨c, hc⟩` from `hd`. Substitute `hc` using the available equality. Break down `Nat.lt_or_ge c 2 with h | h` into its components or cases. Use `interval_cases c`. Use linear arithmetic over natural numbers and integers.

Conclude with `absurd (mul_one J).symm hne`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_mul_le_of_dvd_ne {J E : ℕ} (hd : J ∣ E) (hne : J ≠ E) (hE : 1 ≤ E) : 2 * J ≤ E := by
  obtain ⟨c, hc⟩ := hd
  subst hc
  rcases Nat.lt_or_ge c 2 with h | h
  · interval_cases c
    · omega
    · exact absurd (mul_one J).symm hne
  · nlinarith

/- English proof (translation)
Establish `hg : 1 < g` using `(Fact.out : g.Prime).one_lt`. Establish `hxe : x ^ (g ^ e) = x` using `he ▸ pow_card_minpoly x`. Use `⟨Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hg), ?_⟩` and prove the remaining obligations. Conclude with `orderOf_dvd_of_pow_eq_one (pow_pred_eq_one' hx0 (Nat.one_le_pow _ _ (by omega)) hxe)`.
-/
theorem orderOf_dvd_pow_sub_one {x : Fbar g} (hx0 : x ≠ 0) {e : ℕ}
    (he : (minpoly (ZMod g) x).natDegree = e) (he1 : 1 ≤ e) :
    g ^ e - 1 ≠ 0 ∧ orderOf x ∣ g ^ e - 1 := by
  have hg : 1 < g := (Fact.out : g.Prime).one_lt
  have hxe : x ^ (g ^ e) = x := he ▸ pow_card_minpoly x
  refine ⟨Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by omega) hg), ?_⟩
  exact orderOf_dvd_of_pow_eq_one (pow_pred_eq_one' hx0 (Nat.one_le_pow _ _ (by omega)) hxe)

/- English proof (translation)
Take `⟨hx0, hxd, -, hx1⟩` from `root_facts hf hx`. Take `⟨hy0, hyd, -, hy1⟩` from `root_facts hf hy`. Establish `hxint : IsIntegral (ZMod g) x` using `Algebra.IsIntegral.isIntegral x`. Establish `hyint : IsIntegral (ZMod g) y` using `Algebra.IsIntegral.isIntegral y`. Establish `hcop : IsCoprime (minpoly (ZMod g) x) (minpoly (ZMod g) y)`.

Use `(Irreducible.coprime_iff_not_dvd (minpoly.irreducible hxint)).2 fun h => hne ?_` and prove the remaining obligations. Conclude with `eq_of_monic_of_associated (minpoly.monic hxint) (minpoly.monic hyint) ((minpoly.irreducible hxint).associated_of_dvd (minpoly.irreducible hyint) h)`. Establish `hprod : minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f` using `hcop.mul_dvd hxd hyd`. Establish `hdeg : (minpoly (ZMod g) x).natDegree + (minpoly (ZMod g) y).natDegree ≤ r`. Rewrite using `[← hf.2.1, ← natDegree_mul (minpoly.ne_zero hxint) (minpoly.ne_zero hyint)]`.

Conclude with `natDegree_le_of_dvd hprod hf.1.ne_zero`. Take `⟨hNe, hox⟩` from `orderOf_dvd_pow_sub_one hx0 rfl hx1`. Take `⟨hNe', hoy⟩` from `orderOf_dvd_pow_sub_one hy0 rfl hy1`. Use `⟨_, _, x, y, hy1, hle, hdeg, ?_, rfl, rfl, hprod, pow_card_minpoly y, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnd`.

Establish `hv` using `padicValNat.eq_zero_of_not_dvd hnd`. Establish `h1` using `pow_eq_part_pow_of_dvd ℓ hℓ x _ (mul_ne_zero hNe hNe') (dvd_mul_of_dvd_left hox _)`. Establish `h2` using `pow_eq_part_pow_of_dvd ℓ hℓ y _ (mul_ne_zero hNe hNe') (dvd_mul_of_dvd_right hoy _)`. Rewrite `h1`, `h2` using `[hv, pow_zero, pow_one, pow_one]`. Conclude with `hxy (by rw [h1, h2, hp])`.

Unfold `Lp`. Rewrite using `[← hp]`. Conclude with `pow_eq_part_pow_of_dvd ℓ hℓ x _ hNe hox`.
-/
theorem caseB_of {r ℓ : ℕ} (hℓ : ℓ.Prime) {f : (ZMod g)[X]} (hf : IsLab g r f)
    {x y : Fbar g} (hx : x ∈ rootsBar f) (hy : y ∈ rootsBar f) (hxy : x ≠ y)
    (hp : primeToPart ℓ x = primeToPart ℓ y)
    (hne : minpoly (ZMod g) x ≠ minpoly (ZMod g) y)
    (hle : (minpoly (ZMod g) y).natDegree ≤ (minpoly (ZMod g) x).natDegree) :
    CaseB g r ℓ f := by
  obtain ⟨hx0, hxd, -, hx1⟩ := root_facts hf hx
  obtain ⟨hy0, hyd, -, hy1⟩ := root_facts hf hy
  have hxint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hyint : IsIntegral (ZMod g) y := Algebra.IsIntegral.isIntegral y
  have hcop : IsCoprime (minpoly (ZMod g) x) (minpoly (ZMod g) y) := by
    refine (Irreducible.coprime_iff_not_dvd (minpoly.irreducible hxint)).2 fun h => hne ?_
    exact eq_of_monic_of_associated (minpoly.monic hxint) (minpoly.monic hyint)
      ((minpoly.irreducible hxint).associated_of_dvd (minpoly.irreducible hyint) h)
  have hprod : minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f := hcop.mul_dvd hxd hyd
  have hdeg : (minpoly (ZMod g) x).natDegree + (minpoly (ZMod g) y).natDegree ≤ r := by
    rw [← hf.2.1, ← natDegree_mul (minpoly.ne_zero hxint) (minpoly.ne_zero hyint)]
    exact natDegree_le_of_dvd hprod hf.1.ne_zero
  obtain ⟨hNe, hox⟩ := orderOf_dvd_pow_sub_one hx0 rfl hx1
  obtain ⟨hNe', hoy⟩ := orderOf_dvd_pow_sub_one hy0 rfl hy1
  refine ⟨_, _, x, y, hy1, hle, hdeg, ?_, rfl, rfl, hprod, pow_card_minpoly y, ?_⟩
  · by_contra hnd
    have hv := padicValNat.eq_zero_of_not_dvd hnd
    have h1 := pow_eq_part_pow_of_dvd ℓ hℓ x _ (mul_ne_zero hNe hNe')
      (dvd_mul_of_dvd_left hox _)
    have h2 := pow_eq_part_pow_of_dvd ℓ hℓ y _ (mul_ne_zero hNe hNe')
      (dvd_mul_of_dvd_right hoy _)
    rw [hv, pow_zero, pow_one, pow_one] at h1 h2
    exact hxy (by rw [h1, h2, hp])
  · unfold Lp
    rw [← hp]
    exact pow_eq_part_pow_of_dvd ℓ hℓ x _ hNe hox

/- English proof (translation)
Take `⟨hx0, hxd, hxr, hx1⟩` from `root_facts hf hx`. Take `⟨hy0, -, -, -⟩` from `root_facts hf hy`. Establish `hxint : IsIntegral (ZMod g) x` using `Algebra.IsIntegral.isIntegral x`. Take `⟨hNe, hox⟩` from `orderOf_dvd_pow_sub_one hx0 rfl hx1`. Take `⟨-, hoy⟩` from `orderOf_dvd_pow_sub_one hy0 (congrArg natDegree heq.symm) hx1`.

Establish `hxL` using `pow_eq_part_pow_of_dvd ℓ hℓ x _ hNe hox`. Establish `hyL` using `pow_eq_part_pow_of_dvd ℓ hℓ y _ hNe hoy`. Establish `htt : x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ = y ^ Lp g (minpoly (ZMod g) x).natDegree ℓ`. Unfold `Lp`. Rewrite using `[hxL, hyL, hp]`.

Take `⟨σ, hσ⟩` from `(Normal.minpoly_eq_iff_mem_orbit (F := ZMod g) (E := Fbar g)).1 heq.symm`. Use `replace hσ : σ x = y := hσ`. Establish `hσt : σ (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ) = x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ`. Rewrite using `[map_pow, hσ, htt]`. Establish `hxnot : x ∉ IntermediateField.adjoin (ZMod g) {x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ}`.

Introduce `hmem`. Take `⟨p, q, hpq⟩` from `(IntermediateField.mem_adjoin_simple_iff (ZMod g) x).1 hmem`. Establish `hfix : σ x = x`. Rewrite using `[hpq, map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, hσt]`. Conclude with `hxy (hfix.symm.trans hσ)`.

Establish `htint : IsIntegral (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)` using `Algebra.IsIntegral.isIntegral _`. Establish `hle : IntermediateField.adjoin (ZMod g) {x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ} ≤ IntermediateField.adjoin (ZMod g) {x}`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `pow_mem (IntermediateField.mem_adjoin_simple_self (ZMod g) x) _`. Use `haveI := IntermediateField.adjoin.finiteDimensional hxint`.

Establish `hdiv : (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ∣ (minpoly (ZMod g) x).natDegree`. Establish `h` using `IntermediateField.finrank_dvd_of_le_right hle`. Rewrite `h` using `[IntermediateField.adjoin.finrank htint, IntermediateField.adjoin.finrank hxint]`. Then use the resulting hypothesis. Establish `hjne : (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ≠ (minpoly (ZMod g) x).natDegree`. Introduce `hEq`.

Apply `hxnot` to reduce the goal to its premises. Establish `hEq2` using `IntermediateField.eq_of_le_of_finrank_eq hle (by rw [IntermediateField.adjoin.finrank htint, IntermediateField.adjoin.finrank hxint, hEq])`. Rewrite using `[hEq2]`. Conclude with `IntermediateField.mem_adjoin_simple_self _ x`. Establish `hj1` using `minpoly.natDegree_pos htint`.

Establish `h2j : 2 * (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ≤ (minpoly (ZMod g) x).natDegree`. Conclude with `two_mul_le_of_dvd_ne hdiv hjne hx1`. Establish `ht0 : x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ ≠ 0` using `pow_ne_zero _ hx0`. Establish `htj` using `pow_pred_eq_one' ht0 (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos) (pow_card_minpoly (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ))`. Use `⟨_, _, x, by omega, hxr, hj1, h2j, ?_, rfl, hxd, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hnd`. Establish `hv` using `padicValNat.eq_zero_of_not_dvd hnd`. Rewrite `hxL`, `hyL` using `[hv, pow_zero, pow_one, pow_one]`. Conclude with `hxy (by rw [hxL, hyL, hp])`. Rewrite using `[mul_comm, pow_mul]`.

Conclude with `htj`.
-/
theorem caseA_of {r ℓ : ℕ} (hℓ : ℓ.Prime) {f : (ZMod g)[X]} (hf : IsLab g r f)
    {x y : Fbar g} (hx : x ∈ rootsBar f) (hy : y ∈ rootsBar f) (hxy : x ≠ y)
    (hp : primeToPart ℓ x = primeToPart ℓ y)
    (heq : minpoly (ZMod g) x = minpoly (ZMod g) y) :
    CaseA g r ℓ f := by
  obtain ⟨hx0, hxd, hxr, hx1⟩ := root_facts hf hx
  obtain ⟨hy0, -, -, -⟩ := root_facts hf hy
  have hxint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  obtain ⟨hNe, hox⟩ := orderOf_dvd_pow_sub_one hx0 rfl hx1
  obtain ⟨-, hoy⟩ := orderOf_dvd_pow_sub_one hy0 (congrArg natDegree heq.symm) hx1
  have hxL := pow_eq_part_pow_of_dvd ℓ hℓ x _ hNe hox
  have hyL := pow_eq_part_pow_of_dvd ℓ hℓ y _ hNe hoy
  have htt : x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ =
      y ^ Lp g (minpoly (ZMod g) x).natDegree ℓ := by
    unfold Lp; rw [hxL, hyL, hp]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ZMod g) (E := Fbar g)).1 heq.symm
  replace hσ : σ x = y := hσ
  have hσt : σ (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ) =
      x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ := by
    rw [map_pow, hσ, htt]
  have hxnot : x ∉ IntermediateField.adjoin (ZMod g)
      {x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ} := by
    intro hmem
    obtain ⟨p, q, hpq⟩ := (IntermediateField.mem_adjoin_simple_iff (ZMod g) x).1 hmem
    have hfix : σ x = x := by
      rw [hpq, map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, hσt]
    exact hxy (hfix.symm.trans hσ)
  have htint : IsIntegral (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ) :=
    Algebra.IsIntegral.isIntegral _
  have hle : IntermediateField.adjoin (ZMod g) {x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ} ≤
      IntermediateField.adjoin (ZMod g) {x} := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self (ZMod g) x) _
  haveI := IntermediateField.adjoin.finiteDimensional hxint
  have hdiv : (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ∣
      (minpoly (ZMod g) x).natDegree := by
    have h := IntermediateField.finrank_dvd_of_le_right hle
    rwa [IntermediateField.adjoin.finrank htint, IntermediateField.adjoin.finrank hxint] at h
  have hjne : (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ≠
      (minpoly (ZMod g) x).natDegree := by
    intro hEq
    apply hxnot
    have hEq2 := IntermediateField.eq_of_le_of_finrank_eq hle
      (by rw [IntermediateField.adjoin.finrank htint, IntermediateField.adjoin.finrank hxint, hEq])
    rw [hEq2]
    exact IntermediateField.mem_adjoin_simple_self _ x
  have hj1 := minpoly.natDegree_pos htint
  have h2j : 2 * (minpoly (ZMod g) (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ)).natDegree ≤
      (minpoly (ZMod g) x).natDegree := by
    exact two_mul_le_of_dvd_ne hdiv hjne hx1
  have ht0 : x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ ≠ 0 := pow_ne_zero _ hx0
  have htj := pow_pred_eq_one' ht0 (Nat.one_le_pow _ _ (Fact.out : g.Prime).pos)
    (pow_card_minpoly (x ^ Lp g (minpoly (ZMod g) x).natDegree ℓ))
  refine ⟨_, _, x, by omega, hxr, hj1, h2j, ?_, rfl, hxd, ?_⟩
  · by_contra hnd
    have hv := padicValNat.eq_zero_of_not_dvd hnd
    rw [hv, pow_zero, pow_one, pow_one] at hxL hyL
    exact hxy (by rw [hxL, hyL, hp])
  · rw [mul_comm, pow_mul]
    exact htj

end

/- English proof (translation)
Introduce `g r _ f hf`. Take `⟨hlab, -, hnot⟩` from `hf`. Use `push Not at hnot`. Take `⟨ℓ, hℓ, hBB, x, hx, y, hy, hp, hxy⟩` from `hnot`. Use `⟨ℓ, hℓ, hBB, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `heq : minpoly (ZMod g) x = minpoly (ZMod g) y`. Conclude with `Or.inl (caseA_of hℓ hlab hx hy hxy hp heq)`. Use `right`. Break down `le_total (minpoly (ZMod g) y).natDegree (minpoly (ZMod g) x).natDegree with h | h` into its components or cases. Conclude with `caseB_of hℓ hlab hx hy hxy hp heq h`.

Conclude with `caseB_of hℓ hlab hy hx (Ne.symm hxy) hp.symm (Ne.symm heq) h`.
-/
theorem counted_labels_have_witness : Witness := by
  intro g r _ f hf
  obtain ⟨hlab, -, hnot⟩ := hf
  push Not at hnot
  obtain ⟨ℓ, hℓ, hBB, x, hx, y, hy, hp, hxy⟩ := hnot
  refine ⟨ℓ, hℓ, hBB, ?_⟩
  by_cases heq : minpoly (ZMod g) x = minpoly (ZMod g) y
  · exact Or.inl (caseA_of hℓ hlab hx hy hxy hp heq)
  · right
    rcases le_total (minpoly (ZMod g) y).natDegree (minpoly (ZMod g) x).natDegree with h | h
    · exact caseB_of hℓ hlab hx hy hxy hp heq h
    · exact caseB_of hℓ hlab hy hx (Ne.symm hxy) hp.symm (Ne.symm heq) h

end PI.SqfRootsInj.W
