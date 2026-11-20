import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartUnitBasicOpenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalizationStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChCoh

def IsU {Ω : Type} [Field Ω] (S : Subring Ω) (a : Ω) : Prop := a ≠ 0 ∧ a ∈ S ∧ a⁻¹ ∈ S

section Units

variable {Ω : Type} [Field Ω] {S : Subring Ω}

/- English proof (translation)
Assemble the required witnesses or components as `⟨one_ne_zero, S.one_mem, by simpa using S.one_mem⟩`.
-/
theorem IsU.one : IsU S 1 := ⟨one_ne_zero, S.one_mem, by simpa using S.one_mem⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩`.
-/
theorem IsU.mul {a b : Ω} (ha : IsU S a) (hb : IsU S b) : IsU S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

/- English proof (translation)
Establish `ha0` using `left_ne_zero_of_mul h.1`. Establish `hb0` using `right_ne_zero_of_mul h.1`. Use `⟨ha0, ha, ?_⟩` and prove the remaining obligations. Establish `: a⁻¹ = b * (a * b)⁻¹` using `by field_simp`. Rewrite using `[this]`.

Conclude with `S.mul_mem hb h.2.2`.
-/
theorem IsU.of_mul {a b : Ω} (ha : a ∈ S) (hb : b ∈ S) (h : IsU S (a * b)) : IsU S a := by
  have ha0 := left_ne_zero_of_mul h.1
  have hb0 := right_ne_zero_of_mul h.1
  refine ⟨ha0, ha, ?_⟩
  have : a⁻¹ = b * (a * b)⁻¹ := by field_simp
  rw [this]
  exact S.mul_mem hb h.2.2

/- English proof (translation)
Take `⟨b, hb⟩` from `h.exists_right_inv`. Establish `hb' : (a : Ω) * (b : Ω) = 1` using `by exact_mod_cast congrArg (Subtype.val) hb`. Establish `h0 : (a : Ω) ≠ 0` using `left_ne_zero_of_mul_eq_one hb'`. Use `⟨h0, a.2, ?_⟩` and prove the remaining obligations. Rewrite using `[inv_eq_of_mul_eq_one_right hb']`.

Conclude with `b.2`.
-/
theorem IsU.of_isUnit {a : S} (h : IsUnit a) : IsU S (a : Ω) := by
  obtain ⟨b, hb⟩ := h.exists_right_inv
  have hb' : (a : Ω) * (b : Ω) = 1 := by exact_mod_cast congrArg (Subtype.val) hb
  have h0 : (a : Ω) ≠ 0 := left_ne_zero_of_mul_eq_one hb'
  refine ⟨h0, a.2, ?_⟩
  rw [inv_eq_of_mul_eq_one_right hb']
  exact b.2

end Units

def satIdeal {A E : Type} [CommRing A] [AddCommGroup E] [Module A E] (S : Submodule A E) (f : A) (e : E) : Ideal A where
  carrier := {a | ∃ k : ℕ, (f ^ k * a) • e ∈ S}
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    refine ⟨k + l, ?_⟩
    have : (f ^ (k + l) * (a + b)) • e = f ^ l • ((f ^ k * a) • e) + f ^ k • ((f ^ l * b) • e) := by
      simp only [smul_smul, ← add_smul]
      congr 1
      ring
    rw [this]
    exact S.add_mem (S.smul_mem _ hk) (S.smul_mem _ hl)
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c a ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have : (f ^ k * (c • a)) • e = c • ((f ^ k * a) • e) := by
      simp only [smul_smul, smul_eq_mul]
      congr 1
      ring
    rw [this]
    exact S.smul_mem _ hk

section Abstract

variable {A : Type} [CommRing A] {Ω : Type} [Field Ω] (ι : A →+* Ω) {E : Type} [AddCommGroup E] [Module Ω E]
  [Module A E]

/- English proof (translation)
Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, by simpa using IsU.one, by simpa using Submodule.subset_span hx⟩`. Consider the case `zero => exact ⟨1, by simpa using IsU.one, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨v, hv, h⟩` from `hx`.

Take `⟨w, hw, h'⟩` from `hy`. Use `⟨v * w, by rw [map_mul]; exact hv.mul hw, ?_⟩` and prove the remaining obligations. Establish `: (v * w) • (x + y) = w • (v • x) + v • (w • y)`. Simplify using `only [smul_add, smul_smul, mul_comm]`. Rewrite using `[this]`.

Conclude with `add_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem _ _ h')`. Consider the case `smul r x _ hx`. Take `⟨v, hv, h⟩` from `hx`. Take `⟨u, w, hw, hr⟩` from `hfrac r r.2`. Use `⟨w * v, by rw [map_mul]; exact hw.mul hv, ?_⟩` and prove the remaining obligations.

Establish `: (w * v) • (r • x) = u • (v • x)`. Establish `h1 : r • x = (r : Ω) • x` using `rfl`. Rewrite using `[h1, hsm, hsm, hsm, smul_smul, smul_smul, map_mul, hr]`. Use `congr 1`. Use `hw.1` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem clear_denoms (hsm : ∀ (a : A) (e : E), a • e = ι a • e) {S : Subring Ω}
    (hfrac : ∀ a ∈ S, ∃ u v : A, IsU S (ι v) ∧ a = ι u / ι v) (s : Set E) {e : E}
    (he : e ∈ Submodule.span S s) : ∃ v : A, IsU S (ι v) ∧ v • e ∈ Submodule.span A s := by
  induction he using Submodule.span_induction with
  | mem x hx => exact ⟨1, by simpa using IsU.one, by simpa using Submodule.subset_span hx⟩
  | zero => exact ⟨1, by simpa using IsU.one, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨v, hv, h⟩ := hx
    obtain ⟨w, hw, h'⟩ := hy
    refine ⟨v * w, by rw [map_mul]; exact hv.mul hw, ?_⟩
    have : (v * w) • (x + y) = w • (v • x) + v • (w • y) := by
      simp only [smul_add, smul_smul, mul_comm]
    rw [this]
    exact add_mem (Submodule.smul_mem _ _ h) (Submodule.smul_mem _ _ h')
  | smul r x _ hx =>
    obtain ⟨v, hv, h⟩ := hx
    obtain ⟨u, w, hw, hr⟩ := hfrac r r.2
    refine ⟨w * v, by rw [map_mul]; exact hw.mul hv, ?_⟩
    have : (w * v) • (r • x) = u • (v • x) := by
      have h1 : r • x = (r : Ω) • x := rfl
      rw [h1, hsm, hsm, hsm, smul_smul, smul_smul, map_mul, hr]
      congr 1
      have := hw.1
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ h

/- English proof (translation)
Proceed by induction on `he using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span hx`. Consider the case `zero => exact zero_mem _`. Consider the case `add _ _ _ _ hx hy => exact add_mem hx hy`. Consider the case `smul a x _ hx`.

Rewrite using `[hsm]`. Conclude with `Submodule.smul_mem _ (⟨ι a, hAS a⟩ : S) hx`.
-/
theorem mem_of_mem_spanA (hsm : ∀ (a : A) (e : E), a • e = ι a • e) {S : Subring Ω} (hAS : ∀ a, ι a ∈ S)
    {s : Set E} {e : E} (he : e ∈ Submodule.span A s) : e ∈ Submodule.span S s := by
  induction he using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact zero_mem _
  | add _ _ _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx =>
    rw [hsm]
    exact Submodule.smul_mem _ (⟨ι a, hAS a⟩ : S) hx

variable {Pt : Type} (R : Pt → Subring Ω)

/- English proof (translation)
Establish `hrad : g * f ∈ (satIdeal (Submodule.span A t) g e).radical`. Rewrite using `[Ideal.radical_eq_sInf, Ideal.mem_sInf]`. Introduce and unpack `P ⟨hJP, hP⟩`. Assume the negation of the conclusion as `hn`. Take `⟨q, hq⟩` from `hprime P hP`.

Establish `hgf : IsU (R q) (ι g * ι f)`. Rewrite using `[← map_mul]`. Conclude with `not_not.1 fun h => hn ((hq _).2 h)`. Establish `hg' : IsU (R q) (ι g)` using `IsU.of_mul (hAR q g) (hAR q f) hgf`. Establish `hf' : IsU (R q) (ι f)` using `IsU.of_mul (hAR q f) (hAR q g) (by rwa [mul_comm])`.

Establish `hmem : e ∈ Submodule.span (R q) t`. Rewrite using `[← hg q hg', hf q hf']`. Conclude with `Submodule.subset_span he`. Take `⟨v, hv, hve⟩` from `clear_denoms ι hsm (hfrac q) t hmem`. Establish `hvJ : v ∈ satIdeal (Submodule.span A t) g e` using `⟨0, by simpa using hve⟩`.

Conclude with `(hq v).1 (hJP hvJ) hv`. Take `⟨m, k, hk⟩` from `hrad`. Use `⟨m, fun q hgq => ?_⟩` and prove the remaining obligations. Rewrite using `[hg q hgq]`. Establish `h1` using `mem_of_mem_spanA ι hsm (hAR q) hk`.

Rewrite `h1` using `[hsm]`. Establish `h2 : (ι f) ^ m • e = ((ι g ^ (k + m))⁻¹) • (ι (g ^ k * (g * f) ^ m) • e)`. Rewrite using `[smul_smul]`. Use `congr 1`. Use `hgq.1` as an intermediate fact.

Simplify using `only [map_mul, map_pow, mul_pow, pow_add]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ (⟨(ι g ^ (k + m))⁻¹, by rw [← inv_pow]; exact pow_mem hgq.2.2 _⟩ : R q) h1`.
-/
theorem pow_smul_mem (hsm : ∀ (a : A) (e : E), a • e = ι a • e) (hAR : ∀ q a, ι a ∈ R q)
    (hfrac : ∀ q, ∀ a ∈ R q, ∃ u v : A, IsU (R q) (ι v) ∧ a = ι u / ι v)
    (hprime : ∀ P : Ideal A, P.IsPrime → ∃ q : Pt, ∀ u : A, u ∈ P ↔ ¬ IsU (R q) (ι u))
    (L : ∀ q, Submodule (R q) E) {f g : A} {s t : Set E}
    (hf : ∀ q, IsU (R q) (ι f) → L q = Submodule.span (R q) s)
    (hg : ∀ q, IsU (R q) (ι g) → L q = Submodule.span (R q) t) {e : E} (he : e ∈ s) :
    ∃ m : ℕ, ∀ q, IsU (R q) (ι g) → (ι f) ^ m • e ∈ L q := by
  have hrad : g * f ∈ (satIdeal (Submodule.span A t) g e).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra hn
    obtain ⟨q, hq⟩ := hprime P hP
    have hgf : IsU (R q) (ι g * ι f) := by
      rw [← map_mul]
      exact not_not.1 fun h => hn ((hq _).2 h)
    have hg' : IsU (R q) (ι g) := IsU.of_mul (hAR q g) (hAR q f) hgf
    have hf' : IsU (R q) (ι f) := IsU.of_mul (hAR q f) (hAR q g) (by rwa [mul_comm])
    have hmem : e ∈ Submodule.span (R q) t := by
      rw [← hg q hg', hf q hf']
      exact Submodule.subset_span he
    obtain ⟨v, hv, hve⟩ := clear_denoms ι hsm (hfrac q) t hmem
    have hvJ : v ∈ satIdeal (Submodule.span A t) g e := ⟨0, by simpa using hve⟩
    exact (hq v).1 (hJP hvJ) hv
  obtain ⟨m, k, hk⟩ := hrad
  refine ⟨m, fun q hgq => ?_⟩
  rw [hg q hgq]
  have h1 := mem_of_mem_spanA ι hsm (hAR q) hk
  rw [hsm] at h1
  have h2 : (ι f) ^ m • e = ((ι g ^ (k + m))⁻¹) • (ι (g ^ k * (g * f) ^ m) • e) := by
    rw [smul_smul]
    congr 1
    have := hgq.1
    simp only [map_mul, map_pow, mul_pow, pow_add]
    field_simp
  rw [h2]
  exact Submodule.smul_mem _ (⟨(ι g ^ (k + m))⁻¹, by rw [← inv_pow]; exact pow_mem hgq.2.2 _⟩ : R q) h1

/- English proof (translation)
Use `choose F n b hF hL using hcover`. Establish `htop : Ideal.span (Set.range F) = ⊤`. Assume the negation of the conclusion as `h`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ h`. Take `⟨q, hq⟩` from `hprime P hP.isPrime`.

Conclude with `(hq (F q)).1 (hle (Ideal.subset_span ⟨q, rfl⟩)) (hF q)`. Establish `h1 : (1 : A) ∈ Ideal.span (Set.range F)` using `by rw [htop]; trivial`. Take `⟨c, hc⟩` from `Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 h1`. Establish `hsome : ∀ q, ∃ l ∈ c.support, IsU (R q) (ι (F l))`. Introduce `q`.

Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Use `letI := hloc q`. Set `φ : A →+* R q` to `ι.codRestrict (R q) (hAR q)`. Establish `hmem : (1 : A) ∈ (IsLocalRing.maximalIdeal (R q)).comap φ`.

Rewrite using `[← hc]`. Use `Ideal.sum_mem _ fun l hl => Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Use `show φ (F l) ∈ IsLocalRing.maximalIdeal (R q)`. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun hu => hn l hl (IsU.of_isUnit hu)`.

Establish `h1' : (1 : R q) ∈ IsLocalRing.maximalIdeal (R q)` using `by simpa using hmem`. Conclude with `(Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1'`. Establish `hm : ∀ (l : Pt) (i : Fin (n l)), ∃ m : ℕ, ∀ q, (ι (F l)) ^ m • b l i ∈ L q`. Introduce `l i`. Establish `h` using `fun j => pow_smul_mem ι R hsm hAR hfrac hprime L (f := F l) (g := F j) (hL l) (hL j) (e := b l i) ⟨i, rfl⟩`.

Use `choose m hm using h`. Use `⟨c.support.sup m, fun q => ?_⟩` and prove the remaining obligations. Take `⟨j, hj, hu⟩` from `hsome q`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le (Finset.le_sup (f := m) hj)`. Rewrite using `[hd, add_comm, pow_add, mul_smul]`.

Conclude with `(L q).smul_mem (⟨(ι (F l)) ^ d, pow_mem (hAR q _) _⟩ : R q) (hm j q hu)`. Use `choose m hm using hm`. Set `g : (Σ l : c.support, Fin (n l)) → E` to `fun t => (ι (F t.1)) ^ (m t.1 t.2) • b t.1 t.2`. Set `eq` to `Fintype.equivFin (Σ l : c.support, Fin (n l))`. Use `⟨_, g ∘ eq.symm, fun q => ?_⟩` and prove the remaining obligations.

Rewrite using `[EquivLike.range_comp]`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨l, hl, hu⟩` from `hsome q`. Rewrite using `[hL l q hu, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Establish `h2 : b l i = ((ι (F l))⁻¹) ^ (m l i) • g ⟨⟨l, hl⟩, i⟩` using `by show _ = _ • (ι (F l)) ^ (m l i) • b l i`. Rewrite using `[smul_smul, ← mul_pow, inv_mul_cancel₀ hu.1, one_pow, one_smul]`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ (⟨_, pow_mem hu.2.2 _⟩ : R q) (Submodule.subset_span ⟨_, rfl⟩)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `hm _ _ q`.
-/
theorem finite_gen (hsm : ∀ (a : A) (e : E), a • e = ι a • e) (hAR : ∀ q a, ι a ∈ R q)
    (hfrac : ∀ q, ∀ a ∈ R q, ∃ u v : A, IsU (R q) (ι v) ∧ a = ι u / ι v)
    (hprime : ∀ P : Ideal A, P.IsPrime → ∃ q : Pt, ∀ u : A, u ∈ P ↔ ¬ IsU (R q) (ι u))
    (hloc : ∀ q, IsLocalRing (R q)) (L : ∀ q, Submodule (R q) E)
    (hcover : ∀ p : Pt, ∃ (f : A) (n : ℕ) (b : Fin n → E), IsU (R p) (ι f) ∧
      ∀ q, IsU (R q) (ι f) → L q = Submodule.span (R q) (Set.range b)) :
    ∃ (n : ℕ) (b : Fin n → E), ∀ q, L q = Submodule.span (R q) (Set.range b) := by
  choose F n b hF hL using hcover
  have htop : Ideal.span (Set.range F) = ⊤ := by
    by_contra h
    obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨q, hq⟩ := hprime P hP.isPrime
    exact (hq (F q)).1 (hle (Ideal.subset_span ⟨q, rfl⟩)) (hF q)
  have h1 : (1 : A) ∈ Ideal.span (Set.range F) := by rw [htop]; trivial
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 h1
  have hsome : ∀ q, ∃ l ∈ c.support, IsU (R q) (ι (F l)) := by
    intro q
    by_contra hn
    push_neg at hn
    letI := hloc q
    let φ : A →+* R q := ι.codRestrict (R q) (hAR q)
    have hmem : (1 : A) ∈ (IsLocalRing.maximalIdeal (R q)).comap φ := by
      rw [← hc]
      refine Ideal.sum_mem _ fun l hl => Ideal.mul_mem_left _ _ ?_
      show φ (F l) ∈ IsLocalRing.maximalIdeal (R q)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hn l hl (IsU.of_isUnit hu)
    have h1' : (1 : R q) ∈ IsLocalRing.maximalIdeal (R q) := by simpa using hmem
    exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal _).ne_top h1'
  have hm : ∀ (l : Pt) (i : Fin (n l)), ∃ m : ℕ, ∀ q, (ι (F l)) ^ m • b l i ∈ L q := by
    intro l i
    have h := fun j => pow_smul_mem ι R hsm hAR hfrac hprime L (f := F l) (g := F j) (hL l) (hL j)
      (e := b l i) ⟨i, rfl⟩
    choose m hm using h
    refine ⟨c.support.sup m, fun q => ?_⟩
    obtain ⟨j, hj, hu⟩ := hsome q
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := m) hj)
    rw [hd, add_comm, pow_add, mul_smul]
    exact (L q).smul_mem (⟨(ι (F l)) ^ d, pow_mem (hAR q _) _⟩ : R q) (hm j q hu)
  choose m hm using hm
  let g : (Σ l : c.support, Fin (n l)) → E := fun t => (ι (F t.1)) ^ (m t.1 t.2) • b t.1 t.2
  let eq := Fintype.equivFin (Σ l : c.support, Fin (n l))
  refine ⟨_, g ∘ eq.symm, fun q => ?_⟩
  rw [EquivLike.range_comp]
  apply le_antisymm
  · obtain ⟨l, hl, hu⟩ := hsome q
    rw [hL l q hu, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h2 : b l i = ((ι (F l))⁻¹) ^ (m l i) • g ⟨⟨l, hl⟩, i⟩ := by
      show _ = _ • (ι (F l)) ^ (m l i) • b l i
      rw [smul_smul, ← mul_pow, inv_mul_cancel₀ hu.1, one_pow, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ (⟨_, pow_mem hu.2.2 _⟩ : R q) (Submodule.subset_span ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact hm _ _ q

end Abstract

/- English proof (translation)
Unfold `regAt`. Conclude with `IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (RingHom.rangeRestrict_surjective _)`.
-/
theorem isLocalRing_regAt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) :
    IsLocalRing (regAt ξ p) := by
  unfold regAt
  exact IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (RingHom.rangeRestrict_surjective _)

end GlobalTheory.CompanionTheory.Ar.ChCoh
