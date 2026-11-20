import Mathlib

open PrimeSpectrum

namespace GlobalTheory

variable {R : Type} [CommRing R]

/- English proof (translation)
Use `by_contra! H`. Establish `hdis : Disjoint ((⊥ : Ideal R) : Set R) ((p.primeCompl ⊔ Submonoid.powers a : Submonoid R) : Set R)`. Rewrite using `[Set.disjoint_left]`. Introduce and unpack `x hx hxS`. Rewrite `hx` using `[SetLike.mem_coe, Ideal.mem_bot]`.

Substitute `hx` using the available equality. Take `⟨y, hy, z, hz, hyz⟩` from `Submonoid.mem_sup.mp hxS`. Take `⟨n, rfl⟩` from `hz`. Conclude with `H y hy n hyz`. Take `⟨q, hq, -, hqd⟩` from `Ideal.exists_le_prime_disjoint ⊥ _ hdis`.

Establish `hqp : q ≤ p`. Introduce `x hx`. Assume the negation of the conclusion as `hxp`. Conclude with `Set.disjoint_left.mp hqd hx (Submonoid.mem_sup_left (show x ∈ p.primeCompl from hxp))`. Establish `hqp'` using `(hR q hq).eq_of_le hp.ne_top hqp`.

Establish `haq : a ∉ q` using `fun h => Set.disjoint_left.mp hqd h (Submonoid.mem_sup_right (Submonoid.mem_powers a))`. Conclude with `haq (hqp' ▸ ha)`.
-/
theorem exists_mul_pow_eq_zero_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) {p : Ideal R} [hp : p.IsPrime] {a : R}
    (ha : a ∈ p) : ∃ t ∉ p, ∃ n : ℕ, t * a ^ n = 0 := by
  by_contra! H
  have hdis : Disjoint ((⊥ : Ideal R) : Set R)
      ((p.primeCompl ⊔ Submonoid.powers a : Submonoid R) : Set R) := by
    rw [Set.disjoint_left]
    rintro x hx hxS
    rw [SetLike.mem_coe, Ideal.mem_bot] at hx
    subst hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submonoid.mem_sup.mp hxS
    obtain ⟨n, rfl⟩ := hz
    exact H y hy n hyz
  obtain ⟨q, hq, -, hqd⟩ := Ideal.exists_le_prime_disjoint ⊥ _ hdis
  have hqp : q ≤ p := by
    intro x hx
    by_contra hxp
    exact Set.disjoint_left.mp hqd hx
      (Submonoid.mem_sup_left (show x ∈ p.primeCompl from hxp))
  have hqp' := (hR q hq).eq_of_le hp.ne_top hqp
  have haq : a ∉ q := fun h => Set.disjoint_left.mp hqd h
    (Submonoid.mem_sup_right (Submonoid.mem_powers a))
  exact haq (hqp' ▸ ha)

/- English proof (translation)
Use `⟨?_, (basicOpen a).isOpen⟩` and prove the remaining obligations. Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `x hx`. Establish `hax : a ∈ x.asIdeal`. Simplify `hx` using `[Set.mem_compl_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]`.

Take `⟨t, ht, n, htn⟩` from `exists_mul_pow_eq_zero_of_forall_isMaximal hR hax`. Use `⟨(basicOpen t : Set (PrimeSpectrum R)), ?_, (basicOpen t).isOpen, ht⟩` and prove the remaining obligations. Introduce `y hy hya`. Rewrite `hy`, `hya` using `[SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]`. Establish `: t * a ^ n ∈ y.asIdeal` using `htn ▸ y.asIdeal.zero_mem`.

Break down `y.isPrime.mem_or_mem this with h | h` into its components or cases. Conclude with `hy h`. Conclude with `hya (y.isPrime.mem_of_pow_mem n h)`.
-/
theorem isClopen_basicOpen_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (a : R) :
    IsClopen ((basicOpen a : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
  refine ⟨?_, (basicOpen a).isOpen⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  have hax : a ∈ x.asIdeal := by
    simpa [Set.mem_compl_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] using hx
  obtain ⟨t, ht, n, htn⟩ := exists_mul_pow_eq_zero_of_forall_isMaximal hR hax
  refine ⟨(basicOpen t : Set (PrimeSpectrum R)), ?_, (basicOpen t).isOpen, ht⟩
  intro y hy hya
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hy hya
  have : t * a ^ n ∈ y.asIdeal := htn ▸ y.asIdeal.zero_mem
  rcases y.isPrime.mem_or_mem this with h | h
  · exact hy h
  · exact hya (y.isPrime.mem_of_pow_mem n h)

/- English proof (translation)
Set `c : TopologicalSpace.Clopens (PrimeSpectrum R)` to `⟨(basicOpen a : Set (PrimeSpectrum R)), isClopen_basicOpen_of_forall_isMaximal hR a⟩`. Set `e` to `(isIdempotentElemEquivClopens (R := R)).symm c`. Establish `he : basicOpen e.1 = basicOpen a`. Rewrite using `[basicOpen_isIdempotentElemEquivClopens_symm]`. Both sides reduce to the same expression.

Take `⟨k, hk⟩` from `(basicOpen_le_basicOpen_iff _ _).mp he.le`. Establish `hmem : e.1 ∈ Ideal.span {a}`. Rewrite using `[← e.2.pow_succ_eq k, pow_succ']`. Conclude with `Ideal.mul_mem_left _ _ hk`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.mp hmem`.

Use `⟨e.1, b, e.2, by rw [mul_comm, hb], fun p hp hap => ?_⟩` and prove the remaining obligations. Establish `h1 : (⟨p, hp⟩ : PrimeSpectrum R) ∈ basicOpen a` using `hap`. Rewrite `h1` using `[← he]`. Conclude with `h1`.
-/
theorem exists_isIdempotentElem_mul_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (a : R) :
    ∃ e b : R, IsIdempotentElem e ∧ a * b = e ∧ ∀ p : Ideal R, p.IsPrime → a ∉ p → e ∉ p := by
  let c : TopologicalSpace.Clopens (PrimeSpectrum R) :=
    ⟨(basicOpen a : Set (PrimeSpectrum R)), isClopen_basicOpen_of_forall_isMaximal hR a⟩
  let e := (isIdempotentElemEquivClopens (R := R)).symm c
  have he : basicOpen e.1 = basicOpen a := by
    rw [basicOpen_isIdempotentElemEquivClopens_symm]; rfl
  obtain ⟨k, hk⟩ := (basicOpen_le_basicOpen_iff _ _).mp he.le
  have hmem : e.1 ∈ Ideal.span {a} := by
    rw [← e.2.pow_succ_eq k, pow_succ']
    exact Ideal.mul_mem_left _ _ hk
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨e.1, b, e.2, by rw [mul_comm, hb], fun p hp hap => ?_⟩
  have h1 : (⟨p, hp⟩ : PrimeSpectrum R) ∈ basicOpen a := hap
  rw [← he] at h1
  exact h1

/- English proof (translation)
Take `⟨S, hS⟩` from `((Module.Invertible.linearEquiv R M).symm 1).exists_finset`. Use `replace hS : 1 = ∑ i ∈ S, i.1 i.2 := by`. Simplify `hS` using `[LinearEquiv.symm_apply_eq, Module.Invertible.linearEquiv]`. Use `letI : LinearOrder (Module.Dual R M × M) := IsWellOrder.linearOrder WellOrderingRel`. Use `choose e b he hab hep using fun i : Module.Dual R M × M => exists_isIdempotentElem_mul_of_forall_isMaximal hR (i.1 i.2)`.

Set `Q : Module.Dual R M × M → R` to `fun l => ∏ j ∈ S with j < l, (1 - e j)`. Set `e' : Module.Dual R M × M → R` to `fun l => e l * Q l`. Establish `hQi : ∀ l, IsIdempotentElem (Q l)` using `fun l => Finset.prod_induction _ IsIdempotentElem (fun _ _ h1 h2 => h1.mul h2) IsIdempotentElem.one (fun j _ => (he j).one_sub)`. Establish `he'i : ∀ l, IsIdempotentElem (e' l)` using `fun l => (he l).mul (hQi l)`. Establish `hlt : ∀ k ∈ S, ∀ l ∈ S, k < l → e k * e' l = 0`.

Introduce `k hk l _ hkl`. Establish `hmem : k ∈ S.filter (· < l)` using `Finset.mem_filter.mpr ⟨hk, hkl⟩`. Simplify using `only [e', Q]`. Rewrite using `[← Finset.mul_prod_erase _ _ hmem]`. Take the linear combination `(-(e l * ∏ x ∈ (S.filter (· < l)).erase k, (1 - e x))) * (he k).eq`.

Establish `horth : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → e' k * e' l = 0`. Introduce `k hk l hl hkl`. Break down `lt_or_gt_of_ne hkl with h | h` into its components or cases. Use `hlt k hk l hl h` as an intermediate fact. Simplify using `only [e'] at this ⊢`.

Take the linear combination `Q k * this`. Use `hlt l hl k hk h` as an intermediate fact. Simplify using `only [e'] at this ⊢`. Take the linear combination `Q l * this`. Set `x : M` to `∑ k ∈ S, e' k • k.2`.

Set `φ : Module.Dual R M` to `∑ l ∈ S, (b l * e' l) • l.1`. Establish `hφx : φ x = ∑ l ∈ S, e' l`. Simplify using `only [φ, x, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single l]`.

Establish `h1` using `(he'i l).eq`. Establish `h2` using `hab l`. Establish `h3 : e' l * e l = e' l`. Simplify using `only [e']`. Take the linear combination `Q l * (he l).eq`.

Take the linear combination `(b l * l.1 l.2) * h1 + e' l * h2 + h3`. Introduce `k hk hkl`. Use `horth l hl k hk (Ne.symm hkl)` as an intermediate fact. Take the linear combination `(b k * k.1 l.2) * this`. Introduce `h`.

Conclude with `absurd hl h`. Establish `hsum : ∑ l ∈ S, e' l = 1 - ∏ i ∈ S, (1 - e i)`. Rewrite using `[Finset.prod_one_sub_ordered S e]`. Expand and normalize the polynomial expressions, which then agree. Establish `hunit : IsUnit (1 - ∏ i ∈ S, (1 - e i))`.

Assume the negation of the conclusion as `hnu`. Take `⟨m, hm, hxm⟩` from `exists_max_ideal_of_mem_nonunits hnu`. Take `⟨i, hi, him⟩ : ∃ i ∈ S, i.1 i.2 ∉ m` from `by by_contra! hall`. Conclude with `hm.ne_top ((Ideal.eq_top_iff_one _).mpr (hS ▸ Ideal.sum_mem _ hall))`. Establish `hei` using `hep i m hm.isPrime him`.

Establish `h1 : 1 - e i ∈ m`. Establish `: e i * (1 - e i) ∈ m`. Rewrite using `[mul_sub, mul_one, (he i).eq, sub_self]`. Conclude with `m.zero_mem`. Conclude with `(hm.isPrime.mem_or_mem this).resolve_left hei`.

Establish `hP : ∏ i ∈ S, (1 - e i) ∈ m`. Rewrite using `[← Finset.mul_prod_erase _ _ hi]`. Conclude with `m.mul_mem_right _ h1`. Conclude with `hm.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using m.add_mem hxm hP))`. Rewrite `hunit` using `[← hsum, ← hφx]`.

Conclude with `.of_equiv <| .symm <| .ofBijective φ (Module.Invertible.bijective_of_surjective <| LinearMap.range_eq_top.mp <| Ideal.eq_top_of_isUnit_mem _ ⟨x, rfl⟩ hunit)`.
-/
theorem free_of_invertible_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (M : Type) [AddCommGroup M] [Module R M]
    (hM : Module.Invertible R M) : Module.Free R M := by
  classical
  obtain ⟨S, hS⟩ := ((Module.Invertible.linearEquiv R M).symm 1).exists_finset
  replace hS : 1 = ∑ i ∈ S, i.1 i.2 := by
    simpa [LinearEquiv.symm_apply_eq, Module.Invertible.linearEquiv] using hS
  letI : LinearOrder (Module.Dual R M × M) := IsWellOrder.linearOrder WellOrderingRel
  choose e b he hab hep using
    fun i : Module.Dual R M × M => exists_isIdempotentElem_mul_of_forall_isMaximal hR (i.1 i.2)

  let Q : Module.Dual R M × M → R := fun l => ∏ j ∈ S with j < l, (1 - e j)
  let e' : Module.Dual R M × M → R := fun l => e l * Q l
  have hQi : ∀ l, IsIdempotentElem (Q l) := fun l =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ h1 h2 => h1.mul h2)
      IsIdempotentElem.one (fun j _ => (he j).one_sub)
  have he'i : ∀ l, IsIdempotentElem (e' l) := fun l => (he l).mul (hQi l)
  have hlt : ∀ k ∈ S, ∀ l ∈ S, k < l → e k * e' l = 0 := by
    intro k hk l _ hkl
    have hmem : k ∈ S.filter (· < l) := Finset.mem_filter.mpr ⟨hk, hkl⟩
    simp only [e', Q]
    rw [← Finset.mul_prod_erase _ _ hmem]
    linear_combination (-(e l * ∏ x ∈ (S.filter (· < l)).erase k, (1 - e x))) * (he k).eq
  have horth : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → e' k * e' l = 0 := by
    intro k hk l hl hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · have := hlt k hk l hl h
      simp only [e'] at this ⊢
      linear_combination Q k * this
    · have := hlt l hl k hk h
      simp only [e'] at this ⊢
      linear_combination Q l * this

  let x : M := ∑ k ∈ S, e' k • k.2
  let φ : Module.Dual R M := ∑ l ∈ S, (b l * e' l) • l.1
  have hφx : φ x = ∑ l ∈ S, e' l := by
    simp only [φ, x, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.sum_eq_single l]
    · have h1 := (he'i l).eq
      have h2 := hab l
      have h3 : e' l * e l = e' l := by
        simp only [e']; linear_combination Q l * (he l).eq
      linear_combination (b l * l.1 l.2) * h1 + e' l * h2 + h3
    · intro k hk hkl
      have := horth l hl k hk (Ne.symm hkl)
      linear_combination (b k * k.1 l.2) * this
    · intro h; exact absurd hl h
  have hsum : ∑ l ∈ S, e' l = 1 - ∏ i ∈ S, (1 - e i) := by
    rw [Finset.prod_one_sub_ordered S e]; ring
  have hunit : IsUnit (1 - ∏ i ∈ S, (1 - e i)) := by
    by_contra hnu
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hnu
    obtain ⟨i, hi, him⟩ : ∃ i ∈ S, i.1 i.2 ∉ m := by
      by_contra! hall
      exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (hS ▸ Ideal.sum_mem _ hall))
    have hei := hep i m hm.isPrime him
    have h1 : 1 - e i ∈ m := by
      have : e i * (1 - e i) ∈ m := by
        rw [mul_sub, mul_one, (he i).eq, sub_self]; exact m.zero_mem
      exact (hm.isPrime.mem_or_mem this).resolve_left hei
    have hP : ∏ i ∈ S, (1 - e i) ∈ m := by
      rw [← Finset.mul_prod_erase _ _ hi]; exact m.mul_mem_right _ h1
    exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using m.add_mem hxm hP))
  rw [← hsum, ← hφx] at hunit
  exact .of_equiv <| .symm <| .ofBijective φ (Module.Invertible.bijective_of_surjective <|
    LinearMap.range_eq_top.mp <| Ideal.eq_top_of_isUnit_mem _ ⟨x, rfl⟩ hunit)

/- English proof (translation)
Introduce `R _ hR c`. Establish `: Subsingleton (CommRing.Pic R)` using `CommRing.Pic.subsingleton_iff.mpr fun M _ _ hM => free_of_invertible_of_forall_isMaximal hR M hM`. Conclude with `Subsingleton.elim _ _`.
-/
theorem pic_eq_one_of_forall_isMaximal :
    ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) →
      ∀ c : CommRing.Pic R, c = 1 := by
  intro R _ hR c
  have : Subsingleton (CommRing.Pic R) := CommRing.Pic.subsingleton_iff.mpr
    fun M _ _ hM => free_of_invertible_of_forall_isMaximal hR M hM
  exact Subsingleton.elim _ _

end GlobalTheory
