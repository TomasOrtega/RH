import Formalism.HermitianCurvature.PrimeToDifferent

namespace Formalism.FourierDecayAlt.P.S6x6
open NumberField NumberField.IsCMField Module Formalism.FourierDecayAlt.S6
open scoped nonZeroDivisors

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `[complexConj_apply_apply]`.
-/
theorem conj_conj (x : 𝓞 E) :
    ringOfIntegersComplexConj E (ringOfIntegersComplexConj E x) = x := by
  apply RingOfIntegers.ext
  simp [complexConj_apply_apply]

/- English proof (translation)
Take `⟨x, hx, y, hy, hxy⟩` from `Ideal.isCoprime_iff_exists.mp hc`. Take `⟨w, rfl⟩` from `Ideal.mem_span_singleton'.mp hy`. Establish `hfix : ringOfIntegersComplexConj E (x * ringOfIntegersComplexConj E x) = x * ringOfIntegersComplexConj E x`. Rewrite using `[map_mul, conj_conj, mul_comm]`. Take `⟨a, ha⟩` from `(ringOfIntegersComplexConj_eq_self_iff E _).mp hfix`.

Establish `hfix2 : ringOfIntegersComplexConj E (w + ringOfIntegersComplexConj E w - (g : 𝓞 E) * (w * ringOfIntegersComplexConj E w)) = w + ringOfIntegersComplexConj E w - (g : 𝓞 E) * (w * ringOfIntegersComplexConj E w)`. Simplify using `only [map_sub, map_add, map_mul, conj_conj, map_natCast]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨b, hb⟩` from `(ringOfIntegersComplexConj_eq_self_iff E _).mp hfix2`. Establish `hx' : x = 1 - w * (g : 𝓞 E)` using `by rw [← hxy]; ring`.

Establish `hab : a + (g : 𝓞 (maximalRealSubfield E)) * b = 1`. Apply `FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E)` to reduce the goal to its premises. Rewrite using `[map_add, map_mul, ha, hb, map_natCast, map_one, hx']`. Simplify using `only [map_sub, map_mul, map_one, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨a, fun haP => hP.ne_top ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.eq_top_iff_one, ← hab]`. Conclude with `P.add_mem haP (P.mul_mem_right _ hgP)`. Rewrite using `[ha]`. Conclude with `Ideal.mul_mem_right _ _ hx`.
-/
theorem exists_real_mem_different (g : ℕ) (hc : PrimeToDifferent E g)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsPrime)
    (hgP : (g : 𝓞 (maximalRealSubfield E)) ∈ P) :
    ∃ a : 𝓞 (maximalRealSubfield E), a ∉ P ∧
      algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a ∈ differentIdeal ℤ (𝓞 E) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.mp hc
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have hfix : ringOfIntegersComplexConj E (x * ringOfIntegersComplexConj E x) =
      x * ringOfIntegersComplexConj E x := by
    rw [map_mul, conj_conj, mul_comm]
  obtain ⟨a, ha⟩ := (ringOfIntegersComplexConj_eq_self_iff E _).mp hfix
  have hfix2 : ringOfIntegersComplexConj E (w + ringOfIntegersComplexConj E w -
      (g : 𝓞 E) * (w * ringOfIntegersComplexConj E w)) =
      w + ringOfIntegersComplexConj E w - (g : 𝓞 E) * (w * ringOfIntegersComplexConj E w) := by
    simp only [map_sub, map_add, map_mul, conj_conj, map_natCast]
    ring
  obtain ⟨b, hb⟩ := (ringOfIntegersComplexConj_eq_self_iff E _).mp hfix2
  have hx' : x = 1 - w * (g : 𝓞 E) := by rw [← hxy]; ring
  have hab : a + (g : 𝓞 (maximalRealSubfield E)) * b = 1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E)
    rw [map_add, map_mul, ha, hb, map_natCast, map_one, hx']
    simp only [map_sub, map_mul, map_one, map_natCast]
    ring
  refine ⟨a, fun haP => hP.ne_top ?_, ?_⟩
  · rw [Ideal.eq_top_iff_one, ← hab]
    exact P.add_mem haP (P.mul_mem_right _ hgP)
  · rw [ha]; exact Ideal.mul_mem_right _ _ hx

/- English proof (translation)
Unfold `dd`. Rewrite using `[FractionalIdeal.coeIdeal_ne_zero]`. Conclude with `differentIdeal_ne_bot`.
-/
theorem dd_ne_zero : dd E ≠ 0 := by
  unfold dd
  rw [FractionalIdeal.coeIdeal_ne_zero]
  exact differentIdeal_ne_bot

/- English proof (translation)
The claim follows from `FractionalIdeal.coeIdeal_le_one`.
-/
theorem dd_le_one : dd E ≤ 1 := FractionalIdeal.coeIdeal_le_one

/- English proof (translation)
Take `⟨a, haP, ha⟩` from `exists_real_mem_different E g hc P hP hgP`. Take `⟨b, hb, h⟩` from `ht`. Take `⟨n, hn⟩ : ∃ n : ℕ, ν' ≤ ν + n` from `⟨(ν' - ν).toNat, by omega⟩`. Take `⟨m, hm⟩ : ∃ m : ℕ, (n : ℤ) + ν = m + ν'` from `⟨(ν + n - ν').toNat, by omega⟩`. Use `⟨a ^ n * b, fun hh => (hP.mem_or_mem hh).elim (fun h' => haP (hP.mem_of_pow_mem _ h')) hb, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ ∈ idl E g k ν at h`. Use `show _ ∈ idl E g k ν'`. Establish `ha' : algebraMap (𝓞 (maximalRealSubfield E)) E a ∈ dd E`. Unfold `dd`. Rewrite using `[FractionalIdeal.mem_coeIdeal]`.

Conclude with `⟨_, ha, rfl⟩`. Establish `hpow : ∀ j : ℕ, algebraMap (𝓞 (maximalRealSubfield E)) E a ^ j ∈ dd E ^ j`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`.

Consider the case `succ j ih => rw [pow_succ, pow_succ]`. Conclude with `FractionalIdeal.mul_mem_mul ih ha'`. Establish `h1 : algebraMap (𝓞 (maximalRealSubfield E)) E a ^ n ∈ dd E ^ n` using `hpow n`. Establish `h2` using `FractionalIdeal.mul_mem_mul h1 h`. Establish `h3 : dd E ^ n * idl E g k ν = dd E ^ m * idl E g k ν'`.

Unfold `idl`. Rewrite using `[← mul_assoc, ← mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (dd_ne_zero E), ← zpow_add₀ (dd_ne_zero E), hm]`. Establish `h4 : dd E ^ m * idl E g k ν' ≤ idl E g k ν'`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, map_pow, mul_assoc]`.

Conclude with `h4 (h3 ▸ h2)`.
-/
theorem localisation_typed_independent_exponent (g : ℕ) (k ν ν' : ℤ) (hc : PrimeToDifferent E g)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsPrime)
    (hgP : (g : 𝓞 (maximalRealSubfield E)) ∈ P) (t : E)
    (ht : t ∈ locAt E P (zsub E (idl E g k ν))) : t ∈ locAt E P (zsub E (idl E g k ν')) := by
  obtain ⟨a, haP, ha⟩ := exists_real_mem_different E g hc P hP hgP
  obtain ⟨b, hb, h⟩ := ht
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ν' ≤ ν + n := ⟨(ν' - ν).toNat, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℤ) + ν = m + ν' := ⟨(ν + n - ν').toNat, by omega⟩
  refine ⟨a ^ n * b, fun hh => (hP.mem_or_mem hh).elim (fun h' => haP (hP.mem_of_pow_mem _ h')) hb, ?_⟩
  change _ ∈ idl E g k ν at h
  show _ ∈ idl E g k ν'
  have ha' : algebraMap (𝓞 (maximalRealSubfield E)) E a ∈ dd E := by
    unfold dd
    rw [FractionalIdeal.mem_coeIdeal]
    exact ⟨_, ha, rfl⟩
  have hpow : ∀ j : ℕ, algebraMap (𝓞 (maximalRealSubfield E)) E a ^ j ∈ dd E ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih ha'
  have h1 : algebraMap (𝓞 (maximalRealSubfield E)) E a ^ n ∈ dd E ^ n :=
    hpow n
  have h2 := FractionalIdeal.mul_mem_mul h1 h
  have h3 : dd E ^ n * idl E g k ν = dd E ^ m * idl E g k ν' := by
    unfold idl
    rw [← mul_assoc, ← mul_assoc, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (dd_ne_zero E),
      ← zpow_add₀ (dd_ne_zero E), hm]
  have h4 : dd E ^ m * idl E g k ν' ≤ idl E g k ν' := by
    calc dd E ^ m * idl E g k ν' ≤ 1 * idl E g k ν' :=
          mul_le_mul_left (pow_le_one' (dd_le_one E) m) _
      _ = _ := one_mul _
  rw [map_mul, map_pow, mul_assoc]
  exact h4 (h3 ▸ h2)

section LG

variable {E}

/- English proof (translation)
Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, fun h => (hP.mem_or_mem h).elim ha hb, ?_⟩` and prove the remaining obligations. Establish `h1` using `hL.1 b _ hax`. Establish `h2` using `hL.1 a _ hby`.

Establish `h3 : algebraMap (𝓞 (maximalRealSubfield E)) E (a * b) * (x + y) = algebraMap (𝓞 (maximalRealSubfield E)) E b * (algebraMap (𝓞 (maximalRealSubfield E)) E a * x) + algebraMap (𝓞 (maximalRealSubfield E)) E a * (algebraMap (𝓞 (maximalRealSubfield E)) E b * y)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h3]`. Conclude with `L.add_mem h1 h2`.
-/
theorem locAt_add {L : Submodule ℤ E} (hL : IsFLattice E L)
    {P : Ideal (𝓞 (maximalRealSubfield E))} (hP : P.IsPrime) {x y : E}
    (hx : x ∈ locAt E P L) (hy : y ∈ locAt E P L) : x + y ∈ locAt E P L := by
  obtain ⟨a, ha, hax⟩ := hx
  obtain ⟨b, hb, hby⟩ := hy
  refine ⟨a * b, fun h => (hP.mem_or_mem h).elim ha hb, ?_⟩
  have h1 := hL.1 b _ hax
  have h2 := hL.1 a _ hby
  have h3 : algebraMap (𝓞 (maximalRealSubfield E)) E (a * b) * (x + y) =
      algebraMap (𝓞 (maximalRealSubfield E)) E b * (algebraMap (𝓞 (maximalRealSubfield E)) E a * x) +
      algebraMap (𝓞 (maximalRealSubfield E)) E a * (algebraMap (𝓞 (maximalRealSubfield E)) E b * y) := by
    rw [map_mul]; ring
  rw [h3]; exact L.add_mem h1 h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h), by simp⟩`.
-/
theorem locAt_zero (L : Submodule ℤ E) {P : Ideal (𝓞 (maximalRealSubfield E))} (hP : P.IsPrime) :
    (0 : E) ∈ locAt E P L :=
  ⟨1, fun h => hP.ne_top ((Ideal.eq_top_iff_one P).mpr h), by simp⟩

/- English proof (translation)
The claim follows from `Finset.sum_induction f (fun x => x ∈ locAt E P L) (fun _ _ hx hy => locAt_add hL hP hx hy) (locAt_zero L hP) h`.
-/
theorem locAt_sum {L : Submodule ℤ E} (hL : IsFLattice E L)
    {P : Ideal (𝓞 (maximalRealSubfield E))} (hP : P.IsPrime) {ι : Type*} (s : Finset ι) (f : ι → E)
    (h : ∀ i ∈ s, f i ∈ locAt E P L) : ∑ i ∈ s, f i ∈ locAt E P L :=
  Finset.sum_induction f (fun x => x ∈ locAt E P L) (fun _ _ hx hy => locAt_add hL hP hx hy)
    (locAt_zero L hP) h

def ann {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) : Ideal (𝓞 (maximalRealSubfield E)) where
  carrier := {a | algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show algebraMap _ E (a + b) * t ∈ L
    rw [map_add, add_mul]; exact L.add_mem ha hb
  smul_mem' := fun c a ha => by
    show algebraMap _ E (c • a) * t ∈ L
    rw [smul_eq_mul, map_mul, mul_assoc]; exact hL.1 c _ ha

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ann {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E)
    (a : 𝓞 (maximalRealSubfield E)) :
    a ∈ ann hL t ↔ algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ L := Iff.rfl

/- English proof (translation)
Take `⟨n, hn, hnt⟩` from `hL.2 t`. Introduce `h`. Establish `h1 : (n : 𝓞 (maximalRealSubfield E)) ∈ ann hL t`. Rewrite using `[mem_ann, map_natCast]`. Conclude with `hnt`.

Rewrite `h1` using `[h, Ideal.mem_bot]`. Establish `: n = 0` using `by exact_mod_cast h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem ann_ne_bot {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) : ann hL t ≠ ⊥ := by
  obtain ⟨n, hn, hnt⟩ := hL.2 t
  intro h
  have h1 : (n : 𝓞 (maximalRealSubfield E)) ∈ ann hL t := by
    rw [mem_ann, map_natCast]; exact hnt
  rw [h, Ideal.mem_bot] at h1
  have : n = 0 := by exact_mod_cast h1
  omega

/- English proof (translation)
Establish `hfin : FiniteMultiplicity P (ann hL τ)` using `FiniteMultiplicity.of_not_isUnit (fun h => hP.ne_top (Ideal.isUnit_iff.mp h)) (ann_ne_bot hL τ)`. Take `⟨J, hJ, hPJ⟩` from `hfin.exists_eq_pow_mul_and_not_dvd`. Generalize the expression as in `multiplicity P (ann hL τ) = k at hJ`. Rewrite `hPJ` using `[Ideal.dvd_iff_le]`. Take `⟨b, hbJ, hbP⟩` from `SetLike.not_le_iff_exists.mp hPJ`.

Establish `hcop : IsCoprime P J`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Assume the negation of the conclusion as `h`. Establish `h1 : P = P ⊔ J` using `hP.eq_of_le h le_sup_left`. Conclude with `hPJ (h1 ▸ le_sup_right)`.

Take `⟨u, hu, e, he, hue⟩` from `Ideal.isCoprime_iff_exists.mp (hcop.pow_left (m := k))`. Use `⟨e, ⟨b, hbP, ?_⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : u * b ∈ ann hL τ` using `hJ ▸ Ideal.mul_mem_mul hu hbJ`. Rewrite `h1` using `[mem_ann]`. Establish `h2 : algebraMap (𝓞 (maximalRealSubfield E)) E b * (algebraMap (𝓞 (maximalRealSubfield E)) E e * τ - τ) = -(algebraMap (𝓞 (maximalRealSubfield E)) E (u * b) * τ)`.

Establish `h3 : algebraMap (𝓞 (maximalRealSubfield E)) E u + algebraMap (𝓞 (maximalRealSubfield E)) E e = 1`. Rewrite using `[← map_add, hue, map_one]`. Rewrite using `[map_mul]`. Take the linear combination `(algebraMap (𝓞 (maximalRealSubfield E)) E b * τ) * h3`. Rewrite using `[h2]`.

Conclude with `L.neg_mem h1`. Introduce `Q hQ hQP`. Establish `hnle : ¬ P ≤ Q` using `fun h => hQP (hP.eq_of_le hQ.ne_top h).symm`. Take `⟨c, hcP, hcQ⟩` from `SetLike.not_le_iff_exists.mp hnle`. Use `⟨c ^ k, fun h => hcQ (hQ.isPrime.mem_of_pow_mem _ h), ?_⟩` and prove the remaining obligations.

Establish `h1 : c ^ k * e ∈ ann hL τ` using `hJ ▸ Ideal.mul_mem_mul (Ideal.pow_mem_pow hcP k) he`. Rewrite `h1` using `[mem_ann, map_mul, mul_assoc]`. Conclude with `h1`.
-/
theorem exists_multiplier {L : Submodule ℤ E} (hL : IsFLattice E L)
    (P : Ideal (𝓞 (maximalRealSubfield E))) (hP : P.IsMaximal) (τ : E) :
    ∃ e : 𝓞 (maximalRealSubfield E),
      algebraMap (𝓞 (maximalRealSubfield E)) E e * τ - τ ∈ locAt E P L ∧
      ∀ Q : Ideal (𝓞 (maximalRealSubfield E)), Q.IsMaximal → Q ≠ P →
        algebraMap (𝓞 (maximalRealSubfield E)) E e * τ ∈ locAt E Q L := by
  have hfin : FiniteMultiplicity P (ann hL τ) :=
    FiniteMultiplicity.of_not_isUnit (fun h => hP.ne_top (Ideal.isUnit_iff.mp h)) (ann_ne_bot hL τ)
  obtain ⟨J, hJ, hPJ⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  generalize multiplicity P (ann hL τ) = k at hJ
  rw [Ideal.dvd_iff_le] at hPJ
  obtain ⟨b, hbJ, hbP⟩ := SetLike.not_le_iff_exists.mp hPJ
  have hcop : IsCoprime P J := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have h1 : P = P ⊔ J := hP.eq_of_le h le_sup_left
    exact hPJ (h1 ▸ le_sup_right)
  obtain ⟨u, hu, e, he, hue⟩ := Ideal.isCoprime_iff_exists.mp (hcop.pow_left (m := k))
  refine ⟨e, ⟨b, hbP, ?_⟩, ?_⟩
  · have h1 : u * b ∈ ann hL τ := hJ ▸ Ideal.mul_mem_mul hu hbJ
    rw [mem_ann] at h1
    have h2 : algebraMap (𝓞 (maximalRealSubfield E)) E b *
        (algebraMap (𝓞 (maximalRealSubfield E)) E e * τ - τ) =
        -(algebraMap (𝓞 (maximalRealSubfield E)) E (u * b) * τ) := by
      have h3 : algebraMap (𝓞 (maximalRealSubfield E)) E u +
          algebraMap (𝓞 (maximalRealSubfield E)) E e = 1 := by
        rw [← map_add, hue, map_one]
      rw [map_mul]
      linear_combination (algebraMap (𝓞 (maximalRealSubfield E)) E b * τ) * h3
    rw [h2]; exact L.neg_mem h1
  · intro Q hQ hQP
    have hnle : ¬ P ≤ Q := fun h => hQP (hP.eq_of_le hQ.ne_top h).symm
    obtain ⟨c, hcP, hcQ⟩ := SetLike.not_le_iff_exists.mp hnle
    refine ⟨c ^ k, fun h => hcQ (hQ.isPrime.mem_of_pow_mem _ h), ?_⟩
    have h1 : c ^ k * e ∈ ann hL τ := hJ ▸ Ideal.mul_mem_mul (Ideal.pow_mem_pow hcP k) he
    rw [mem_ann, map_mul, mul_assoc] at h1
    exact h1

/- English proof (translation)
Take `⟨n, hn, hnt⟩` from `hL.2 t`. Establish `hn0 : (n : 𝓞 (maximalRealSubfield E)) ≠ 0`. Introduce `h`. Establish `: n = 0` using `by exact_mod_cast h`. Use linear arithmetic over natural numbers and integers.

Establish `hI : Ideal.span {(n : 𝓞 (maximalRealSubfield E))} ≠ 0`. Simplify `hn0` using `[Ideal.span_singleton_eq_bot]`. Use `((Ideal.finite_factors hI).image (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)) => v.asIdeal)).subset ?_` and prove the remaining obligations. Introduce and unpack `P ⟨hP, htP⟩`. Establish `hnP : (n : 𝓞 (maximalRealSubfield E)) ∈ P`.

Assume the negation of the conclusion as `h`. Conclude with `htP ⟨n, h, by rw [map_natCast]; exact hnt⟩`. Establish `hPbot : P ≠ ⊥`. Introduce `h`. Rewrite `hnP` using `[h, Ideal.mem_bot]`.

Conclude with `hn0 hnP`. Conclude with `⟨⟨P, hP.isPrime, hPbot⟩, by show P ∣ _`. Rewrite using `[Ideal.dvd_span_singleton]`. Conclude with `hnP, rfl⟩`.
-/
theorem finite_bad {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E) :
    {P : Ideal (𝓞 (maximalRealSubfield E)) | P.IsMaximal ∧ t ∉ locAt E P L}.Finite := by
  obtain ⟨n, hn, hnt⟩ := hL.2 t
  have hn0 : (n : 𝓞 (maximalRealSubfield E)) ≠ 0 := by
    intro h
    have : n = 0 := by exact_mod_cast h
    omega
  have hI : Ideal.span {(n : 𝓞 (maximalRealSubfield E))} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hn0
  refine ((Ideal.finite_factors hI).image
    (fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E)) => v.asIdeal)).subset ?_
  rintro P ⟨hP, htP⟩
  have hnP : (n : 𝓞 (maximalRealSubfield E)) ∈ P := by
    by_contra h
    exact htP ⟨n, h, by rw [map_natCast]; exact hnt⟩
  have hPbot : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hnP
    exact hn0 hnP
  exact ⟨⟨P, hP.isPrime, hPbot⟩, by
    show P ∣ _
    rw [Ideal.dvd_span_singleton]; exact hnP, rfl⟩

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `hI : ann hL t ≠ ⊤`. Introduce `h`. Establish `h1 : (1 : 𝓞 (maximalRealSubfield E)) ∈ ann hL t` using `h ▸ Submodule.mem_top`. Rewrite `h1` using `[mem_ann]`.

Apply `hcon` to reduce the goal to its premises. Simplify using `using h1`. Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal _ hI`. Take `⟨a, ha, hat⟩` from `ht M hM`. Conclude with `ha (hIM hat)`.
-/
theorem mem_of_forall_locAt {L : Submodule ℤ E} (hL : IsFLattice E L) (t : E)
    (ht : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → t ∈ locAt E P L) : t ∈ L := by
  by_contra hcon
  have hI : ann hL t ≠ ⊤ := by
    intro h
    have h1 : (1 : 𝓞 (maximalRealSubfield E)) ∈ ann hL t := h ▸ Submodule.mem_top
    rw [mem_ann] at h1
    apply hcon
    simpa using h1
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨a, ha, hat⟩ := ht M hM
  exact ha (hIM hat)

/- English proof (translation)
Establish `hex : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), ∃ e : 𝓞 (maximalRealSubfield E), P.IsMaximal → (algebraMap (𝓞 (maximalRealSubfield E)) E e * τ P - τ P ∈ locAt E P L ∧ ∀ Q : Ideal (𝓞 (maximalRealSubfield E)), Q.IsMaximal → Q ≠ P → algebraMap (𝓞 (maximalRealSubfield E)) E e * τ P ∈ …`. Introduce `P`. Distinguish the cases in `hP : P.IsMaximal`. Take `⟨e, he⟩` from `exists_multiplier hL P hP (τ P)`. Conclude with `⟨e, fun _ => he⟩`.

Conclude with `⟨0, fun h => absurd h hP⟩`. Use `choose e he using hex`. Use `⟨∑ P ∈ S, algebraMap (𝓞 (maximalRealSubfield E)) E (e P) * τ P, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hPS`. Rewrite using `[← Finset.add_sum_erase S _ hPS, add_sub_right_comm]`.

Use `locAt_add hL (hS P hPS).isPrime (he P (hS P hPS)).1 ?_` and prove the remaining obligations. Use `locAt_sum hL (hS P hPS).isPrime _ _ fun Q hQ => ?_` and prove the remaining obligations. Rewrite `hQ` using `[Finset.mem_erase]`. Conclude with `(he Q (hS Q hQ.2)).2 P (hS P hPS) (Ne.symm hQ.1)`. Introduce `P hP hPS`.

Use `locAt_sum hL hP.isPrime _ _ fun Q hQ => ?_` and prove the remaining obligations. Conclude with `(he Q (hS Q hQ)).2 P hP (fun h => hPS (h ▸ hQ))`.
-/
theorem approx {L : Submodule ℤ E} (hL : IsFLattice E L)
    (S : Finset (Ideal (𝓞 (maximalRealSubfield E)))) (τ : Ideal (𝓞 (maximalRealSubfield E)) → E)
    (hS : ∀ P ∈ S, P.IsMaximal) :
    ∃ t : E, (∀ P ∈ S, t - τ P ∈ locAt E P L) ∧
      ∀ P : Ideal (𝓞 (maximalRealSubfield E)), P.IsMaximal → P ∉ S → t ∈ locAt E P L := by
  classical
  have hex : ∀ P : Ideal (𝓞 (maximalRealSubfield E)), ∃ e : 𝓞 (maximalRealSubfield E),
      P.IsMaximal → (algebraMap (𝓞 (maximalRealSubfield E)) E e * τ P - τ P ∈ locAt E P L ∧
      ∀ Q : Ideal (𝓞 (maximalRealSubfield E)), Q.IsMaximal → Q ≠ P →
        algebraMap (𝓞 (maximalRealSubfield E)) E e * τ P ∈ locAt E Q L) := by
    intro P
    by_cases hP : P.IsMaximal
    · obtain ⟨e, he⟩ := exists_multiplier hL P hP (τ P)
      exact ⟨e, fun _ => he⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose e he using hex
  refine ⟨∑ P ∈ S, algebraMap (𝓞 (maximalRealSubfield E)) E (e P) * τ P, ?_, ?_⟩
  · intro P hPS
    rw [← Finset.add_sum_erase S _ hPS, add_sub_right_comm]
    refine locAt_add hL (hS P hPS).isPrime (he P (hS P hPS)).1 ?_
    refine locAt_sum hL (hS P hPS).isPrime _ _ fun Q hQ => ?_
    rw [Finset.mem_erase] at hQ
    exact (he Q (hS Q hQ.2)).2 P (hS P hPS) (Ne.symm hQ.1)
  · intro P hP hPS
    refine locAt_sum hL hP.isPrime _ _ fun Q hQ => ?_
    exact (he Q (hS Q hQ)).2 P hP (fun h => hPS (h ▸ hQ))

end LG

end Formalism.FourierDecayAlt.P.S6x6

namespace Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.S6

/- English proof (translation)
Introduce `E _ _ _ g k ν _ hc P hP hgP`. Use extensionality with `t`. Conclude with `⟨S6x6.localisation_typed_independent_exponent E g k ν 0 hc P hP hgP t, S6x6.localisation_typed_independent_exponent E g k 0 ν hc P hP hgP t⟩`.
-/
theorem localisation_typed_condition : Formalism.FourierDecayAlt.S6.LocTyped := by
  intro E _ _ _ g k ν _ hc P hP hgP
  ext t
  exact ⟨S6x6.localisation_typed_independent_exponent E g k ν 0 hc P hP hgP t, S6x6.localisation_typed_independent_exponent E g k 0 ν hc P hP hgP t⟩

/- English proof (translation)
Introduce `E _ _ _ L hL`. Conclude with `⟨S6x6.finite_bad hL, S6x6.mem_of_forall_locAt hL, S6x6.approx hL⟩`.
-/
theorem local_global_principle : Formalism.FourierDecayAlt.S6.LocalGlobal := by
  intro E _ _ _ L hL
  exact ⟨S6x6.finite_bad hL, S6x6.mem_of_forall_locAt hL, S6x6.approx hL⟩

end Formalism.FourierDecayAlt.P
