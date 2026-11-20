import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

namespace GlobalTheory.FlatFibreRegular

/- English proof (translation)
Set `P : Finset A → Prop` to `fun S => (↑S ⊆ (I : Set A)) ∧ ∀ x ∈ I, ∃ s ∉ 𝔭, s * x ∈ Ideal.span (S : Set A)`. Establish `hex : ∃ n, ∃ S : Finset A, S.card = n ∧ P S`. Take `⟨S, hS⟩` from `hI`. Use `⟨S.card, S, rfl, fun a ha => ?_, fun x hx => ⟨1, ?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hS]`.

Conclude with `Ideal.subset_span ha`. Conclude with `fun h => (Ideal.IsPrime.ne_top' (I := 𝔭)) ((Ideal.eq_top_iff_one _).2 h)`. Rewrite using `[one_mul, hS]`. Conclude with `hx`. Take `⟨S, hcard, hSI, hSgen⟩` from `Nat.find_spec hex`.

Use `⟨S, hSI, hSgen, fun c hc k => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hk`. Establish `hlt : (S.erase k).card < Nat.find hex`. Rewrite using `[← hcard]`. Conclude with `Finset.card_erase_lt_of_mem k.2`.

Apply `Nat.find_min hex hlt` to reduce the goal to its premises. Use `⟨S.erase k, rfl, fun x hx => hSI (Finset.mem_of_mem_erase hx), fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hsx⟩` from `hSgen x hx`. Use `⟨c k * s, fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hk hs), ?_⟩` and prove the remaining obligations. Establish `key : Ideal.span (S : Set A) ≤ Submodule.comap (LinearMap.mulLeft A (c k)) (Ideal.span ((S.erase k : Finset A) : Set A))`.

Rewrite using `[Ideal.span_le]`. Introduce `a ha`. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]`. Distinguish the cases in `hak : a = k`. Rewrite using `[hak]`.

Establish `h1` using `Finset.add_sum_erase Finset.univ (fun i : S => c i * (i : A)) (Finset.mem_univ k)`. Rewrite `h1` using `[hc]`. Rewrite using `[eq_neg_of_add_eq_zero_left h1]`. Use `neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))` and prove the remaining obligations. Establish `hik : i ≠ k` using `Finset.ne_of_mem_erase hi`.

Conclude with `Finset.mem_erase.2 ⟨fun h => hik (Subtype.ext h), i.2⟩`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_erase.2 ⟨hak, ha⟩))`. Use `key hsx` as an intermediate fact. Simplify `this` using `[mul_assoc]`.
-/
theorem exists_minimal_generators {A : Type} [CommRing A] (𝔭 : Ideal A) [𝔭.IsPrime] (I : Ideal A)
    (hI : I.FG) :
    ∃ S : Finset A, (↑S ⊆ (I : Set A)) ∧ (∀ x ∈ I, ∃ s ∉ 𝔭, s * x ∈ Ideal.span (S : Set A)) ∧
      ∀ c : S → A, ∑ i, c i * (i : A) = 0 → ∀ i, c i ∈ 𝔭 := by
  classical
  let P : Finset A → Prop := fun S =>
    (↑S ⊆ (I : Set A)) ∧ ∀ x ∈ I, ∃ s ∉ 𝔭, s * x ∈ Ideal.span (S : Set A)
  have hex : ∃ n, ∃ S : Finset A, S.card = n ∧ P S := by
    obtain ⟨S, hS⟩ := hI
    refine ⟨S.card, S, rfl, fun a ha => ?_, fun x hx => ⟨1, ?_, ?_⟩⟩
    · rw [← hS]; exact Ideal.subset_span ha
    · exact fun h => (Ideal.IsPrime.ne_top' (I := 𝔭)) ((Ideal.eq_top_iff_one _).2 h)
    · rw [one_mul, hS]; exact hx
  obtain ⟨S, hcard, hSI, hSgen⟩ := Nat.find_spec hex
  refine ⟨S, hSI, hSgen, fun c hc k => ?_⟩
  by_contra hk
  have hlt : (S.erase k).card < Nat.find hex := by
    rw [← hcard]; exact Finset.card_erase_lt_of_mem k.2
  apply Nat.find_min hex hlt
  refine ⟨S.erase k, rfl, fun x hx => hSI (Finset.mem_of_mem_erase hx), fun x hx => ?_⟩
  obtain ⟨s, hs, hsx⟩ := hSgen x hx
  refine ⟨c k * s, fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hk hs), ?_⟩
  have key : Ideal.span (S : Set A) ≤
      Submodule.comap (LinearMap.mulLeft A (c k)) (Ideal.span ((S.erase k : Finset A) : Set A)) := by
    rw [Ideal.span_le]
    intro a ha
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    by_cases hak : a = k
    · rw [hak]
      have h1 := Finset.add_sum_erase Finset.univ (fun i : S => c i * (i : A)) (Finset.mem_univ k)
      rw [hc] at h1
      rw [eq_neg_of_add_eq_zero_left h1]
      refine neg_mem (Ideal.sum_mem _ fun i hi => Ideal.mul_mem_left _ _ (Ideal.subset_span ?_))
      have hik : i ≠ k := Finset.ne_of_mem_erase hi
      exact Finset.mem_erase.2 ⟨fun h => hik (Subtype.ext h), i.2⟩
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Finset.mem_erase.2 ⟨hak, ha⟩))
  have := key hsx
  simpa [mul_assoc] using this

/- English proof (translation)
Take `⟨S, hSI, hSgen, hrel⟩` from `exists_minimal_generators 𝔭 I hI`. Use `set J := 𝔭.map (algebraMap A L) with hJdef`. Set `v : S → L` to `fun i => algebraMap A L i`. Establish `hspan : I.map (algebraMap A L) ≤ Ideal.span (Set.range v)`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `x hx`. Take `⟨s, hs, hsx⟩` from `hSgen x hx`. Establish `h1 : algebraMap A L (s * x) ∈ Ideal.span (Set.range v)`. Establish `: Ideal.map (algebraMap A L) (Ideal.span (S : Set A)) ≤ Ideal.span (Set.range v)`. Rewrite using `[Ideal.map_span]`.

Apply `Ideal.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Conclude with `⟨⟨a, ha⟩, rfl⟩`. Conclude with `this (Ideal.mem_map_of_mem _ hsx)`. Rewrite `h1` using `[map_mul]`.

Take `⟨t, ht⟩` from `(hu s hs).exists_left_inv`. Use `Ideal.mul_mem_left _ t h1` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ht, one_mul]`. Then use the resulting hypothesis. Establish `hvI : ∀ i, v i ∈ I.map (algebraMap A L)` using `fun i => Ideal.mem_map_of_mem _ (hSI i.2)`. Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun L).1 (hspan hy)`.

Establish `hgy' : g * y ∈ J • Ideal.span (Set.range v)`. Establish `h1 : (I * 𝔭).map (algebraMap A L) ≤ J • Ideal.span (Set.range v)`. Rewrite using `[Ideal.smul_eq_mul, Ideal.map_mul, mul_comm]`. Conclude with `Ideal.mul_mono_right hspan`. Conclude with `h1 hgy`.

Take `⟨w, hwJ, hw⟩` from `(Submodule.mem_ideal_smul_span_iff_exists_sum J v _).1 hgy'`. Rewrite `hw` using `[Finsupp.sum_fintype _ _ (by simp)]`. Establish `hrel0 : ∑ i : S, (i : A) • (g * c i - w i) = 0`. Establish `e1 : ∑ i : S, (i : A) • (g * c i) = g * y`. Rewrite using `[← hc, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [smul_eq_mul, v]`. Simplify using `only [Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : ∑ i : S, (i : A) • w i = g * y`.

Rewrite using `[← hw]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [smul_eq_mul, v]`. Simplify using `only [Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [smul_sub, Finset.sum_sub_distrib, e1, e2, sub_self]`. Take `⟨k, a, z, hx, hf⟩` from `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := L) (f := fun i : S => (i : A)) (x := fun i => g * c i - w i) hrel0`. Establish `ha : ∀ i j, a i j ∈ 𝔭` using `fun i j => hrel (fun i => a i j) (by rw [← hf j]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _) i`. Establish `hcJ : ∀ i, c i ∈ J`. Introduce `i`.

Apply `hg` to reduce the goal to its premises. Establish `h1 : g * c i - w i ∈ J`. Establish `hxi` using `hx i`. Simplify using `only at hxi`. Rewrite using `[hxi]`.

Conclude with `Ideal.sum_mem _ fun j _ => by`. Rewrite using `[Algebra.smul_def]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha i j))`. Simplify using `using Ideal.add_mem _ h1 (hwJ i)`. Rewrite using `[← hc, Ideal.map_mul]`.

Conclude with `Ideal.sum_mem _ fun i _ => by`. Rewrite using `[smul_eq_mul, mul_comm (c i)]`. Conclude with `Ideal.mul_mem_mul (hvI i) (hcJ i)`.
-/
theorem mem_map_mul_of_mul_mem {A L : Type} [CommRing A] [CommRing L] [Algebra A L] [Module.Flat A L]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s))
    (g : L) (hg : ∀ y, g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L))
    (I : Ideal A) (hI : I.FG) (y : L) (hy : y ∈ I.map (algebraMap A L))
    (hgy : g * y ∈ (I * 𝔭).map (algebraMap A L)) : y ∈ (I * 𝔭).map (algebraMap A L) := by
  classical
  obtain ⟨S, hSI, hSgen, hrel⟩ := exists_minimal_generators 𝔭 I hI
  set J := 𝔭.map (algebraMap A L) with hJdef
  let v : S → L := fun i => algebraMap A L i
  have hspan : I.map (algebraMap A L) ≤ Ideal.span (Set.range v) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨s, hs, hsx⟩ := hSgen x hx
    have h1 : algebraMap A L (s * x) ∈ Ideal.span (Set.range v) := by
      have : Ideal.map (algebraMap A L) (Ideal.span (S : Set A)) ≤ Ideal.span (Set.range v) := by
        rw [Ideal.map_span]
        apply Ideal.span_mono
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
      exact this (Ideal.mem_map_of_mem _ hsx)
    rw [map_mul] at h1
    obtain ⟨t, ht⟩ := (hu s hs).exists_left_inv
    have := Ideal.mul_mem_left _ t h1
    rwa [← mul_assoc, ht, one_mul] at this
  have hvI : ∀ i, v i ∈ I.map (algebraMap A L) := fun i => Ideal.mem_map_of_mem _ (hSI i.2)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 (hspan hy)
  have hgy' : g * y ∈ J • Ideal.span (Set.range v) := by
    have h1 : (I * 𝔭).map (algebraMap A L) ≤ J • Ideal.span (Set.range v) := by
      rw [Ideal.smul_eq_mul, Ideal.map_mul, mul_comm]
      exact Ideal.mul_mono_right hspan
    exact h1 hgy
  obtain ⟨w, hwJ, hw⟩ := (Submodule.mem_ideal_smul_span_iff_exists_sum J v _).1 hgy'
  rw [Finsupp.sum_fintype _ _ (by simp)] at hw
  have hrel0 : ∑ i : S, (i : A) • (g * c i - w i) = 0 := by
    have e1 : ∑ i : S, (i : A) • (g * c i) = g * y := by
      rw [← hc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_eq_mul, v]; simp only [Algebra.smul_def]; ring
    have e2 : ∑ i : S, (i : A) • w i = g * y := by
      rw [← hw]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [smul_eq_mul, v]; simp only [Algebra.smul_def]; ring
    simp only [smul_sub, Finset.sum_sub_distrib, e1, e2, sub_self]
  obtain ⟨k, a, z, hx, hf⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := A) (M := L)
    (f := fun i : S => (i : A)) (x := fun i => g * c i - w i) hrel0
  have ha : ∀ i j, a i j ∈ 𝔭 := fun i j =>
    hrel (fun i => a i j) (by rw [← hf j]; exact Finset.sum_congr rfl fun i _ => mul_comm _ _) i
  have hcJ : ∀ i, c i ∈ J := by
    intro i
    apply hg
    have h1 : g * c i - w i ∈ J := by
      have hxi := hx i
      dsimp only at hxi
      rw [hxi]
      exact Ideal.sum_mem _ fun j _ => by
        rw [Algebra.smul_def]; exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (ha i j))
    simpa using Ideal.add_mem _ h1 (hwJ i)
  rw [← hc, Ideal.map_mul]
  exact Ideal.sum_mem _ fun i _ => by
    rw [smul_eq_mul, mul_comm (c i)]; exact Ideal.mul_mem_mul (hvI i) (hcJ i)

/- English proof (translation)
Establish `hn : ∀ n : ℕ, y ∈ (𝔭 ^ n).map (algebraMap A L)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]`. Conclude with `Submodule.mem_top`.

Consider the case `succ n ih`. Rewrite using `[pow_succ]`. Conclude with `mem_map_mul_of_mul_mem 𝔭 hu g hg (𝔭 ^ n) (IsNoetherian.noetherian _) y ih (by rw [hgy]; exact zero_mem _)`. Rewrite using `[← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ, Ideal.mem_iInf]`. Introduce `n`.

Rewrite using `[← Ideal.map_pow]`. Conclude with `hn n`.
-/
theorem eq_zero_of_mul_eq_zero {A L : Type} [CommRing A] [IsNoetherianRing A] [CommRing L]
    [IsLocalRing L] [IsNoetherianRing L] [Algebra A L] [Module.Flat A L]
    (𝔭 : Ideal A) [𝔭.IsPrime] (hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s))
    (hJ : 𝔭.map (algebraMap A L) ≠ ⊤)
    (g : L) (hg : ∀ y, g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L))
    (y : L) (hgy : g * y = 0) : y = 0 := by
  have hn : ∀ n : ℕ, y ∈ (𝔭 ^ n).map (algebraMap A L) := by
    intro n
    induction n with
    | zero => rw [pow_zero, Ideal.one_eq_top, Ideal.map_top]; exact Submodule.mem_top
    | succ n ih =>
      rw [pow_succ]
      exact mem_map_mul_of_mul_mem 𝔭 hu g hg (𝔭 ^ n) (IsNoetherian.noetherian _) y ih
        (by rw [hgy]; exact zero_mem _)
  rw [← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ, Ideal.mem_iInf]
  intro n
  rw [← Ideal.map_pow]
  exact hn n

/- English proof (translation)
Use `haveI : _root_.IsReduced ((A ⧸ 𝔭) ⊗[A] B) := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (A ⧸ 𝔭) _`. Set `e` to `(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B 𝔭).toRingEquiv.trans (Algebra.TensorProduct.comm A B (A ⧸ 𝔭)).toRingEquiv`. Use `haveI : _root_.IsReduced (B ⧸ 𝔭.map (algebraMap A B)) := isReduced_of_injective e.toRingHom e.injective`. Conclude with `(Ideal.isRadical_iff_quotient_reduced _).2 this`.
-/
theorem isRadical_map_of_smooth {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.Smooth A B] (𝔭 : Ideal A) [𝔭.IsPrime] : (𝔭.map (algebraMap A B)).IsRadical := by
  haveI : _root_.IsReduced ((A ⧸ 𝔭) ⊗[A] B) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (A ⧸ 𝔭) _
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B 𝔭).toRingEquiv.trans
    (Algebra.TensorProduct.comm A B (A ⧸ 𝔭)).toRingEquiv
  haveI : _root_.IsReduced (B ⧸ 𝔭.map (algebraMap A B)) :=
    isReduced_of_injective e.toRingHom e.injective
  exact (Ideal.isRadical_iff_quotient_reduced _).2 this

/- English proof (translation)
Use `set L := Localization.AtPrime u`. Use `set J := I₀.map (algebraMap B L) with hJdef`. Establish `hJrad : J.IsRadical`. Introduce and unpack `x ⟨n, hn⟩`. Take `⟨⟨b, s⟩, hx⟩` from `IsLocalization.mk'_surjective u.primeCompl x`.

Simplify using `only at hx`. Substitute `hx` using the available equality. Establish `h1 : algebraMap B L (b ^ n) ∈ J`. Use `Ideal.mul_mem_right (algebraMap B L ((s ^ n : u.primeCompl) : B)) J hn` as an intermediate fact. Rewrite `this` using `[← IsLocalization.mk'_pow, IsLocalization.mk'_spec]`. Then use the resulting hypothesis.

Take `⟨t, ht, htb⟩` from `(IsLocalization.algebraMap_mem_map_algebraMap_iff u.primeCompl L _ _).1 h1`. Establish `h2 : t * b ∈ I₀` using `hrad ⟨n + 1, by`. Rewrite using `[show (t * b) ^ (n + 1) = (t ^ n * b) * (t * b ^ n) by ring]`. Conclude with `Ideal.mul_mem_left _ _ htb⟩`. Establish `h3 : algebraMap B L b ∈ J`.

Establish `h4` using `Ideal.mem_map_of_mem (algebraMap B L) h2`. Rewrite `h4` using `[map_mul]`. Take `⟨t', ht'⟩` from `(IsLocalization.map_units L (⟨t, ht⟩ : u.primeCompl)).exists_left_inv`. Use `Ideal.mul_mem_left _ t' h4` as an intermediate fact. Rewrite `this` using `[← mul_assoc, ht', one_mul]`. Then use the resulting hypothesis.

Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one]`. Conclude with `Ideal.mul_mem_right _ _ h3`. Assume the negation of the conclusion as `hyJ`. Rewrite `hyJ` using `[← hJrad.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]`. Use `push_neg at hyJ`.

Take `⟨P, hP, hyP⟩` from `hyJ`. Use `haveI : P.IsPrime := hP.1.1`. Establish `hgP : algebraMap B L g ∈ P` using `((Ideal.IsPrime.mem_or_mem inferInstance (hP.1.2 hy)).resolve_right hyP)`. Use `set Q := P.comap (algebraMap B L)`. Establish `hQu : Q ≤ u`.

Introduce `x hx`. Assume the negation of the conclusion as `hxu`. Conclude with `(Ideal.IsPrime.ne_top inferInstance : P ≠ ⊤) (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units L (⟨x, hxu⟩ : u.primeCompl)))`. Establish `hQmin : Q ∈ I₀.minimalPrimes`. Use `⟨⟨inferInstance, Ideal.map_le_iff_le_comap.1 hP.1.2⟩, fun Q' hQ' hle => ?_⟩` and prove the remaining obligations.

Use `haveI : Q'.IsPrime := hQ'.1`. Establish `hd : Disjoint (u.primeCompl : Set B) (Q' : Set B)` using `Set.disjoint_left.2 fun x hxM hxI => hxM (hQu (hle hxI))`. Use `haveI := IsLocalization.isPrime_of_isPrime_disjoint u.primeCompl L Q' hQ'.1 hd`. Establish `hc` using `IsLocalization.comap_map_of_isPrime_disjoint u.primeCompl L hQ'.1 hd`. Establish `hPP : P ≤ Q'.map (algebraMap B L)` using `hP.2 ⟨inferInstance, Ideal.map_mono hQ'.2⟩ (Ideal.map_le_iff_le_comap.2 hle)`.

Introduce `x hx`. Rewrite using `[← hc]`. Conclude with `hPP hx`. Conclude with `hg Q hQmin hQu hgP`.
-/
theorem mem_of_mul_mem {B : Type} [CommRing B] (u : Ideal B) [u.IsPrime] (I₀ : Ideal B)
    (hrad : I₀.IsRadical) (g : B) (hg : ∀ Q ∈ I₀.minimalPrimes, Q ≤ u → g ∉ Q)
    (y : Localization.AtPrime u)
    (hy : algebraMap B _ g * y ∈ I₀.map (algebraMap B (Localization.AtPrime u))) :
    y ∈ I₀.map (algebraMap B (Localization.AtPrime u)) := by
  set L := Localization.AtPrime u
  set J := I₀.map (algebraMap B L) with hJdef
  have hJrad : J.IsRadical := by
    rintro x ⟨n, hn⟩
    obtain ⟨⟨b, s⟩, hx⟩ := IsLocalization.mk'_surjective u.primeCompl x
    dsimp only at hx
    subst hx
    have h1 : algebraMap B L (b ^ n) ∈ J := by
      have := Ideal.mul_mem_right (algebraMap B L ((s ^ n : u.primeCompl) : B)) J hn
      rwa [← IsLocalization.mk'_pow, IsLocalization.mk'_spec] at this
    obtain ⟨t, ht, htb⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff u.primeCompl L _ _).1 h1
    have h2 : t * b ∈ I₀ := hrad ⟨n + 1, by
      rw [show (t * b) ^ (n + 1) = (t ^ n * b) * (t * b ^ n) by ring]
      exact Ideal.mul_mem_left _ _ htb⟩
    have h3 : algebraMap B L b ∈ J := by
      have h4 := Ideal.mem_map_of_mem (algebraMap B L) h2
      rw [map_mul] at h4
      obtain ⟨t', ht'⟩ := (IsLocalization.map_units L (⟨t, ht⟩ : u.primeCompl)).exists_left_inv
      have := Ideal.mul_mem_left _ t' h4
      rwa [← mul_assoc, ht', one_mul] at this
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ h3
  by_contra hyJ
  rw [← hJrad.radical, ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf] at hyJ
  push_neg at hyJ
  obtain ⟨P, hP, hyP⟩ := hyJ
  haveI : P.IsPrime := hP.1.1
  have hgP : algebraMap B L g ∈ P := ((Ideal.IsPrime.mem_or_mem inferInstance (hP.1.2 hy)).resolve_right hyP)
  set Q := P.comap (algebraMap B L)
  have hQu : Q ≤ u := by
    intro x hx
    by_contra hxu
    exact (Ideal.IsPrime.ne_top inferInstance : P ≠ ⊤)
      (Ideal.eq_top_of_isUnit_mem _ hx (IsLocalization.map_units L (⟨x, hxu⟩ : u.primeCompl)))
  have hQmin : Q ∈ I₀.minimalPrimes := by
    refine ⟨⟨inferInstance, Ideal.map_le_iff_le_comap.1 hP.1.2⟩, fun Q' hQ' hle => ?_⟩
    haveI : Q'.IsPrime := hQ'.1
    have hd : Disjoint (u.primeCompl : Set B) (Q' : Set B) :=
      Set.disjoint_left.2 fun x hxM hxI => hxM (hQu (hle hxI))
    haveI := IsLocalization.isPrime_of_isPrime_disjoint u.primeCompl L Q' hQ'.1 hd
    have hc := IsLocalization.comap_map_of_isPrime_disjoint u.primeCompl L hQ'.1 hd
    have hPP : P ≤ Q'.map (algebraMap B L) :=
      hP.2 ⟨inferInstance, Ideal.map_mono hQ'.2⟩ (Ideal.map_le_iff_le_comap.2 hle)
    intro x hx
    rw [← hc]
    exact hPP hx
  exact hg Q hQmin hQu hgP

/- English proof (translation)
Introduce `A B _ _ _ _ _ b g u hgb hg`. Use `set 𝔭 := u.asIdeal.comap (algebraMap A B)`. Use `set L := Localization.AtPrime u.asIdeal`. Use `haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B`. Use `haveI : Module.Flat A L := Module.Flat.trans A B L`.

Establish `hmapeq : 𝔭.map (algebraMap A L) = (𝔭.map (algebraMap A B)).map (algebraMap B L)`. Rewrite using `[Ideal.map_map, ← IsScalarTower.algebraMap_eq]`. Establish `hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s)`. Introduce `s hs`. Rewrite using `[IsScalarTower.algebraMap_apply A B L]`.

Conclude with `IsLocalization.map_units L (⟨algebraMap A B s, hs⟩ : u.asIdeal.primeCompl)`. Establish `hJ : 𝔭.map (algebraMap A L) ≠ ⊤`. Rewrite using `[hmapeq]`. Use `ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal L).ne_top ?_` and prove the remaining obligations. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`.

Conclude with `Ideal.map_mono (Ideal.map_le_iff_le_comap.2 le_rfl)`. Establish `hg' : ∀ y : L, algebraMap B L g * y ∈ 𝔭.map (algebraMap A L) → y ∈ 𝔭.map (algebraMap A L)`. Introduce `y hy`. Rewrite `hy`, the goal using `[hmapeq]`. Conclude with `mem_of_mul_mem u.asIdeal _ (isRadical_map_of_smooth 𝔭) g hg y hy`.

Apply `eq_zero_of_mul_eq_zero 𝔭 hu hJ (algebraMap B L g) hg'` to reduce the goal to its premises. Rewrite using `[← map_mul, hgb, map_zero]`.
-/
theorem localization_eq_zero_of_mul_eq_zero : ∀ (A B : Type) [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B] [Algebra.Smooth A B]
    (b g : B) (u : PrimeSpectrum B), g * b = 0 →
    (∀ Q ∈ ((u.asIdeal.comap (algebraMap A B)).map (algebraMap A B)).minimalPrimes, Q ≤ u.asIdeal → g ∉ Q) →
    algebraMap B (Localization.AtPrime u.asIdeal) b = 0 := by
  intro A B _ _ _ _ _ b g u hgb hg
  set 𝔭 := u.asIdeal.comap (algebraMap A B)
  set L := Localization.AtPrime u.asIdeal
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : Module.Flat A L := Module.Flat.trans A B L
  have hmapeq : 𝔭.map (algebraMap A L) = (𝔭.map (algebraMap A B)).map (algebraMap B L) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hu : ∀ s ∉ 𝔭, IsUnit (algebraMap A L s) := by
    intro s hs
    rw [IsScalarTower.algebraMap_apply A B L]
    exact IsLocalization.map_units L (⟨algebraMap A B s, hs⟩ : u.asIdeal.primeCompl)
  have hJ : 𝔭.map (algebraMap A L) ≠ ⊤ := by
    rw [hmapeq]
    refine ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal L).ne_top ?_
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.2 le_rfl)
  have hg' : ∀ y : L, algebraMap B L g * y ∈ 𝔭.map (algebraMap A L) →
      y ∈ 𝔭.map (algebraMap A L) := by
    intro y hy
    rw [hmapeq] at hy ⊢
    exact mem_of_mul_mem u.asIdeal _ (isRadical_map_of_smooth 𝔭) g hg y hy
  apply eq_zero_of_mul_eq_zero 𝔭 hu hJ (algebraMap B L g) hg'
  rw [← map_mul, hgb, map_zero]

end GlobalTheory.FlatFibreRegular
