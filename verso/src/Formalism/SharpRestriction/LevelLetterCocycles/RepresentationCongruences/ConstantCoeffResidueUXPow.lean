import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantLeRpowOfThreeLe

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

section ContDHelpers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Establish `hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩`. Establish `h0 : IsLocalRing.residue O ϖ = 0` using `(IsLocalRing.residue_eq_zero_iff ϖ).2 (hmax ▸ Ideal.mem_span_singleton_self ϖ)`. Rewrite using `[map_mul, PowerSeries.map_C, h0, map_zero, zero_mul]`.

Introduce `h`. Establish `hc : ∀ n, ∃ c : O, coeff n f = ϖ * c`. Introduce `n`. Establish `h1 : IsLocalRing.residue O (coeff n f) = 0`. Use `congrArg (coeff n) h` as an intermediate fact.

Simplify `this` using `[PowerSeries.coeff_map]`. Rewrite `h1` using `[IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `h1`. Conclude with `⟨c, hc⟩`. Use `choose c hc using hc`.

Use `⟨PowerSeries.mk c, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc n]`.
-/
theorem ContD.dvd_iff_map_eq_zero {ϖ : O} (hϖ : Irreducible ϖ) (f : O⟦X⟧) :
    C ϖ ∣ f ↔ f.map (IsLocalRing.residue O) = 0 := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  constructor
  · rintro ⟨g, rfl⟩
    have h0 : IsLocalRing.residue O ϖ = 0 :=
      (IsLocalRing.residue_eq_zero_iff ϖ).2 (hmax ▸ Ideal.mem_span_singleton_self ϖ)
    rw [map_mul, PowerSeries.map_C, h0, map_zero, zero_mul]
  · intro h
    have hc : ∀ n, ∃ c : O, coeff n f = ϖ * c := by
      intro n
      have h1 : IsLocalRing.residue O (coeff n f) = 0 := by
        have := congrArg (coeff n) h
        simpa [PowerSeries.coeff_map] using this
      rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton] at h1
      obtain ⟨c, hc⟩ := h1
      exact ⟨c, hc⟩
    choose c hc using hc
    refine ⟨PowerSeries.mk c, ?_⟩
    ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc n]

/- English proof (translation)
Introduce `h`. Apply `hϖ.ne_zero` to reduce the goal to its premises. Use `congrArg constantCoeff h` as an intermediate fact. Simplify using `using this`.
-/
theorem ContD.C_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : (C ϖ : O⟦X⟧) ≠ 0 := by
  intro h
  apply hϖ.ne_zero
  have := congrArg constantCoeff h
  simpa using this

/- English proof (translation)
Use `⟨ContD.C_ne_zero hϖ, fun hu => hϖ.not_isUnit ?_, fun a b hab => ?_⟩` and prove the remaining obligations. Simplify using `using hu.map (constantCoeff (R := O))`. Rewrite `hab` using `[ContD.dvd_iff_map_eq_zero hϖ, map_mul, mul_eq_zero]`. Break down `hab with h | h` into its components or cases. Conclude with `Or.inl ((ContD.dvd_iff_map_eq_zero hϖ a).2 h)`.

Conclude with `Or.inr ((ContD.dvd_iff_map_eq_zero hϖ b).2 h)`.
-/
theorem ContD.prime_C {ϖ : O} (hϖ : Irreducible ϖ) : Prime (C ϖ : O⟦X⟧) := by
  refine ⟨ContD.C_ne_zero hϖ, fun hu => hϖ.not_isUnit ?_, fun a b hab => ?_⟩
  · simpa using hu.map (constantCoeff (R := O))
  · rw [ContD.dvd_iff_map_eq_zero hϖ, map_mul, mul_eq_zero] at hab
    rcases hab with h | h
    · exact Or.inl ((ContD.dvd_iff_map_eq_zero hϖ a).2 h)
    · exact Or.inr ((ContD.dvd_iff_map_eq_zero hϖ b).2 h)

/- English proof (translation)
Introduce `h` and use `hg ((ContD.dvd_iff_map_eq_zero hϖ g).1 h)`.
-/
theorem ContD.not_dvd_of_isDist {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : IsDist g) :
    ¬ C ϖ ∣ g := fun h => hg ((ContD.dvd_iff_map_eq_zero hϖ g).1 h)

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[map_zero]`. Assume the negation of the conclusion as `hne`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ`. Take `⟨G, hG⟩` from `h (n + 1)`.

Establish `h1 : coeff m F = ϖ ^ (n + 1) * coeff m G`. Rewrite using `[hG, ← map_pow, PowerSeries.coeff_C_mul]`. Rewrite `h1` using `[hu, pow_succ]`. Establish `hϖn : ϖ ^ n ≠ 0` using `pow_ne_zero _ hϖ.ne_zero`. Establish `h2 : (u : O) = ϖ * coeff m G`.

Apply `mul_right_cancel₀ hϖn` to reduce the goal to its premises. Take the linear combination `h1`. Apply `hϖ.not_isUnit` to reduce the goal to its premises. Apply `isUnit_of_mul_isUnit_left (y := coeff m G)` to reduce the goal to its premises. Rewrite using `[← h2]`.

Conclude with `u.isUnit`.
-/
theorem ContD.eq_zero_of_forall_pow_dvd {ϖ : O} (hϖ : Irreducible ϖ) (F : O⟦X⟧)
    (h : ∀ n : ℕ, C ϖ ^ n ∣ F) : F = 0 := by
  ext m
  rw [map_zero]
  by_contra hne
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  obtain ⟨G, hG⟩ := h (n + 1)
  have h1 : coeff m F = ϖ ^ (n + 1) * coeff m G := by
    rw [hG, ← map_pow, PowerSeries.coeff_C_mul]
  rw [hu, pow_succ] at h1
  have hϖn : ϖ ^ n ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have h2 : (u : O) = ϖ * coeff m G := by
    apply mul_right_cancel₀ hϖn
    linear_combination h1
  apply hϖ.not_isUnit
  apply isUnit_of_mul_isUnit_left (y := coeff m G)
  rw [← h2]
  exact u.isUnit

/- English proof (translation)
It suffices to establish `key : ∀ n : ℕ, ∀ G, S G → C ϖ ^ n ∣ G from ContD.eq_zero_of_forall_pow_dvd hϖ F (fun n => key n F hF)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro G _`. Simplify using the standard rewrite rules.

Consider the case `succ n ih`. Introduce `G hG`. Take `⟨G', rfl⟩` from `(ContD.dvd_iff_map_eq_zero hϖ G).2 (h0 G hG)`. Take `⟨Q, hQ⟩` from `ih G' (h1 G' hG)`. Conclude with `⟨Q, by rw [hQ, pow_succ]; ring⟩`.
-/
theorem ContD.descent {ϖ : O} (hϖ : Irreducible ϖ) (S : O⟦X⟧ → Prop)
    (h0 : ∀ F, S F → F.map (IsLocalRing.residue O) = 0)
    (h1 : ∀ F, S (C ϖ * F) → S F) (F : O⟦X⟧) (hF : S F) : F = 0 := by
  suffices key : ∀ n : ℕ, ∀ G, S G → C ϖ ^ n ∣ G from
    ContD.eq_zero_of_forall_pow_dvd hϖ F (fun n => key n F hF)
  intro n
  induction n with
  | zero => intro G _; simp
  | succ n ih =>
    intro G hG
    obtain ⟨G', rfl⟩ := (ContD.dvd_iff_map_eq_zero hϖ G).2 (h0 G hG)
    obtain ⟨Q, hQ⟩ := ih G' (h1 G' hG)
    exact ⟨Q, by rw [hQ, pow_succ]; ring⟩

/- English proof (translation)
Take `⟨H, hH⟩` from `h`. Establish `hp` using `ContD.prime_C hϖ`. Establish `hgN : ¬ C ϖ ∣ g ^ N` using `fun hd => hg (hp.dvd_of_dvd_pow hd)`. Take `⟨K, rfl⟩` from `(hp.dvd_or_dvd ⟨F, hH.symm⟩).resolve_left hgN`. Use `⟨K, mul_left_cancel₀ (ContD.C_ne_zero hϖ) ?_⟩` and prove the remaining obligations.

Rewrite using `[hH]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ContD.dvd_of_dvd_C_mul {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : ¬ C ϖ ∣ g) (N : ℕ)
    (F : O⟦X⟧) (h : g ^ N ∣ C ϖ * F) : g ^ N ∣ F := by
  obtain ⟨H, hH⟩ := h
  have hp := ContD.prime_C hϖ
  have hgN : ¬ C ϖ ∣ g ^ N := fun hd => hg (hp.dvd_of_dvd_pow hd)
  obtain ⟨K, rfl⟩ := (hp.dvd_or_dvd ⟨F, hH.symm⟩).resolve_left hgN
  refine ⟨K, mul_left_cancel₀ (ContD.C_ne_zero hϖ) ?_⟩
  rw [hH]
  ring

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero => intro G _`. Simplify using the standard rewrite rules. Consider the case `succ s ih`. Introduce `G hG`.

Establish `hp` using `ContD.prime_C hϖ`. Establish `h1 : C ϖ ∣ G` using `(hp.dvd_or_dvd (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero s)) hG)).resolve_left hg`. Take `⟨G', rfl⟩` from `h1`. Establish `h2 : C ϖ ^ s ∣ g * G'`. Take `⟨Q, hQ⟩` from `hG`.

Use `⟨Q, mul_left_cancel₀ (ContD.C_ne_zero hϖ) ?_⟩` and prove the remaining obligations. Rewrite `hQ` using `[pow_succ]`. Take the linear combination `hQ`. Take `⟨R, hR⟩` from `ih G' h2`. Conclude with `⟨R, by rw [hR, pow_succ]; ring⟩`.
-/
theorem ContD.pow_dvd_of_dvd_mul {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : ¬ C ϖ ∣ g) (s : ℕ) :
    ∀ G : O⟦X⟧, C ϖ ^ s ∣ g * G → C ϖ ^ s ∣ G := by
  induction s with
  | zero => intro G _; simp
  | succ s ih =>
    intro G hG
    have hp := ContD.prime_C hϖ
    have h1 : C ϖ ∣ G :=
      (hp.dvd_or_dvd (dvd_trans (dvd_pow_self _ (Nat.succ_ne_zero s)) hG)).resolve_left hg
    obtain ⟨G', rfl⟩ := h1
    have h2 : C ϖ ^ s ∣ g * G' := by
      obtain ⟨Q, hQ⟩ := hG
      refine ⟨Q, mul_left_cancel₀ (ContD.C_ne_zero hϖ) ?_⟩
      rw [pow_succ] at hQ
      linear_combination hQ
    obtain ⟨R, hR⟩ := ih G' h2
    exact ⟨R, by rw [hR, pow_succ]; ring⟩

/- English proof (translation)
Use `ContD.descent hϖ (fun F => ∀ N : ℕ, g ^ N ∣ F) ?_ ?_ F hF` and prove the remaining obligations. Introduce `F hF'`. Establish `hX : (X : (IsLocalRing.ResidueField O)⟦X⟧) ∣ g.map (IsLocalRing.residue O)` using `PowerSeries.X_dvd_iff.2 hg0`. Use extensionality with `n`. Establish `h1 : (X : (IsLocalRing.ResidueField O)⟦X⟧) ^ (n + 1) ∣ F.map (IsLocalRing.residue O)`.

Take `⟨Q, hQ⟩` from `hF' (n + 1)`. Use `dvd_trans (pow_dvd_pow_of_dvd hX _) ⟨Q.map (IsLocalRing.residue O), ?_⟩` and prove the remaining obligations. Rewrite using `[hQ, map_mul, map_pow]`. Rewrite using `[map_zero]`. Conclude with `PowerSeries.X_pow_dvd_iff.1 h1 n (Nat.lt_succ_self n)`.

Introduce `F hF' N`. Conclude with `ContD.dvd_of_dvd_C_mul hϖ hg N F (hF' N)`.
-/
theorem ContD.eq_zero_of_forall_dvd_pow {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : ¬ C ϖ ∣ g)
    (hg0 : constantCoeff (g.map (IsLocalRing.residue O)) = 0) (F : O⟦X⟧)
    (hF : ∀ N : ℕ, g ^ N ∣ F) : F = 0 := by
  refine ContD.descent hϖ (fun F => ∀ N : ℕ, g ^ N ∣ F) ?_ ?_ F hF
  · intro F hF'
    have hX : (X : (IsLocalRing.ResidueField O)⟦X⟧) ∣ g.map (IsLocalRing.residue O) :=
      PowerSeries.X_dvd_iff.2 hg0
    ext n
    have h1 : (X : (IsLocalRing.ResidueField O)⟦X⟧) ^ (n + 1) ∣ F.map (IsLocalRing.residue O) := by
      obtain ⟨Q, hQ⟩ := hF' (n + 1)
      refine dvd_trans (pow_dvd_pow_of_dvd hX _) ⟨Q.map (IsLocalRing.residue O), ?_⟩
      rw [hQ, map_mul, map_pow]
    rw [map_zero]
    exact PowerSeries.X_pow_dvd_iff.1 h1 n (Nat.lt_succ_self n)
  · intro F hF' N
    exact ContD.dvd_of_dvd_C_mul hϖ hg N F (hF' N)

/- English proof (translation)
Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 h`. Establish `hx : x = x' + (x - x')` using `by ring`. Rewrite using `[hx]`. Apply `Ideal.add_pow_mem_of_pow_mem_of_le (m := a) (n := s)` to reduce the goal to its premises. Conclude with `Ideal.subset_span (by simp)`.

Rewrite using `[← hy, mul_pow]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`. Use linear arithmetic over natural numbers and integers.
-/
theorem ContD.m5 {R : Type*} [CommRing R] (x x' t : R) (a s : ℕ) (hs : 1 ≤ s)
    (h : x - x' ∈ Ideal.span {t}) : x ^ (a + s - 1) ∈ Ideal.span {x' ^ a, t ^ s} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  have hx : x = x' + (x - x') := by ring
  rw [hx]
  apply Ideal.add_pow_mem_of_pow_mem_of_le (m := a) (n := s)
  · exact Ideal.subset_span (by simp)
  · rw [← hy, mul_pow]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · omega

/- English proof (translation)
Use `show f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ ⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `le_iSup₂ (f := fun (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}) => (j : ℕ∞)) k h`. Introduce `h`.

Assume the negation of the conclusion as `hf`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Apply `hf` to reduce the goal to its premises. Establish `h1 : C ϖ ^ 0 ∈ Ideal.span {C ϖ ^ 0, g}` using `Ideal.subset_span (by simp)`.

Establish `h2` using `Ideal.mul_mem_left _ f h1`. Rewrite `h2` using `[pow_zero, mul_one]`. Then use the resulting hypothesis. Establish `hle : (⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)) ≤ ((k - 1 : ℕ) : ℕ∞)`. Apply `iSup₂_le` to reduce the goal to its premises. Introduce `j hj`.

Establish `hjk : j < k`. Assume the negation of the conclusion as `hjk`. Use `push_neg at hjk`. Apply `hf` to reduce the goal to its premises. Establish `hsub : Ideal.span {C ϖ ^ j, g} ≤ Ideal.span {C ϖ ^ k, g}`.

Rewrite using `[Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]`. Use `⟨?_, Ideal.subset_span (by simp)⟩` and prove the remaining obligations. Rewrite using `[show C ϖ ^ j = C ϖ ^ (j - k) * C ϖ ^ k by rw [← pow_add, Nat.sub_add_cancel hjk]]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`. Conclude with `hsub hj`.

Conclude with `(by omega : j ≤ k - 1)` after adjusting the coercions. Establish `hlt : ((k - 1 : ℕ) : ℕ∞) < (k : ℕ∞)` using `by exact_mod_cast (by omega : k - 1 < k)`. Conclude with `absurd (lt_of_le_of_lt hle hlt) (not_lt.2 h)`.
-/
theorem ContD.mem_iff_le (ϖ : O) (g f : O⟦X⟧) (k : ℕ) :
    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
  show f ∈ Ideal.span {C ϖ ^ k, g} ↔
    (k : ℕ∞) ≤ ⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)
  constructor
  · intro h
    exact le_iSup₂ (f := fun (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}) => (j : ℕ∞)) k h
  · intro h
    by_contra hf
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hf
      have h1 : C ϖ ^ 0 ∈ Ideal.span {C ϖ ^ 0, g} := Ideal.subset_span (by simp)
      have h2 := Ideal.mul_mem_left _ f h1
      rwa [pow_zero, mul_one] at h2
    have hle : (⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)) ≤ ((k - 1 : ℕ) : ℕ∞) := by
      apply iSup₂_le
      intro j hj
      have hjk : j < k := by
        by_contra hjk
        push_neg at hjk
        apply hf
        have hsub : Ideal.span {C ϖ ^ j, g} ≤ Ideal.span {C ϖ ^ k, g} := by
          rw [Ideal.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
          refine ⟨?_, Ideal.subset_span (by simp)⟩
          rw [show C ϖ ^ j = C ϖ ^ (j - k) * C ϖ ^ k by rw [← pow_add, Nat.sub_add_cancel hjk]]
          exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
        exact hsub hj
      exact_mod_cast (by omega : j ≤ k - 1)
    have hlt : ((k - 1 : ℕ) : ℕ∞) < (k : ℕ∞) := by exact_mod_cast (by omega : k - 1 < k)
    exact absurd (lt_of_le_of_lt hle hlt) (not_lt.2 h)

/- English proof (translation)
Assume the negation of the conclusion as `hab`. Use `push_neg at hab`. Establish `hb : b ≠ ⊤` using `ne_top_of_lt hab`. Take `⟨m, rfl⟩` from `ENat.ne_top_iff_exists.1 hb`. Establish `h1 : ((m + 1 : ℕ) : ℕ∞) ≤ a` using `by first`.

Consider the case `exact_mod_cast Order.add_one_le_of_lt hab`. Consider the case `exact_mod_cast (ENat.add_one_le_iff (ENat.coe_ne_top m)).2 hab`. Establish `h2` using `h (m + 1) h1`. Normalize the coercions in `at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem ContD.enat_le_of_forall {a b : ℕ∞} (h : ∀ k : ℕ, (k : ℕ∞) ≤ a → (k : ℕ∞) ≤ b) : a ≤ b := by
  by_contra hab
  push_neg at hab
  have hb : b ≠ ⊤ := ne_top_of_lt hab
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.1 hb
  have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ a := by
    first
    | exact_mod_cast Order.add_one_le_of_lt hab
    | exact_mod_cast (ENat.add_one_le_iff (ENat.coe_ne_top m)).2 hab
  have h2 := h (m + 1) h1
  norm_cast at h2
  omega

/- English proof (translation)
Use `first`. Consider the case `exact ψ.commutes c`. Consider the case `simpa using ψ.commutes c`.
-/
theorem ContD.alg_C (ψ : O⟦X⟧ →ₐ[O] O⟦X⟧) (c : O) : ψ (C c) = C c := by
  first
  | exact ψ.commutes c
  | simpa using ψ.commutes c

end ContDHelpers

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
variable {l : ℕ} [Fact l.Prime] (P : PhiData O l)
variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

omit hϖ in
/- English proof (translation)
Establish `hl : l ≠ 0` using `Nat.Prime.ne_zero Fact.out`. Simplify using `[map_mul, map_pow, PowerSeries.map_X, hl, zero_pow]`.
-/
theorem PhiData.constantCoeff_residue_u_X_pow :
    constantCoeff ((P.u * X ^ l).map (IsLocalRing.residue O)) = 0 := by
  have hl : l ≠ 0 := Nat.Prime.ne_zero Fact.out
  simp [map_mul, map_pow, PowerSeries.map_X, hl, zero_pow]

omit hϖ in
/- English proof (translation)
Rewrite using `[map_mul, map_pow, PowerSeries.map_X]`. Conclude with `mul_ne_zero (P.hu.map (PowerSeries.map (IsLocalRing.residue O))).ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)`.
-/
theorem PhiData.ContD_a_ne : (P.u * X ^ l).map (IsLocalRing.residue O) ≠ 0 := by
  rw [map_mul, map_pow, PowerSeries.map_X]
  exact mul_ne_zero (P.hu.map (PowerSeries.map (IsLocalRing.residue O))).ne_zero
    (pow_ne_zero _ PowerSeries.X_ne_zero)

omit hϖ in
/- English proof (translation)
Rewrite using `[P.hred, PowerSeries.map_X, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero P.constantCoeff_residue_u_X_pow)]`.
-/
theorem PhiData.ContD_map_phiX :
    (P.φ X).map (IsLocalRing.residue O) = (P.u * X ^ l).map (IsLocalRing.residue O) := by
  rw [P.hred, PowerSeries.map_X, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero P.constantCoeff_residue_u_X_pow)]

/- English proof (translation)
Use `show (P.φ X).map (IsLocalRing.residue O) ≠ 0`. Rewrite using `[P.ContD_map_phiX]`. Conclude with `P.ContD_a_ne`.
-/
theorem PhiData.ContD_isDist_phiX : IsDist (P.φ X) := by
  show (P.φ X).map (IsLocalRing.residue O) ≠ 0
  rw [P.ContD_map_phiX]
  exact P.ContD_a_ne

omit hϖ in
/- English proof (translation)
Establish `hu0 : constantCoeff ((P.u).map (IsLocalRing.residue O)) ≠ 0` using `((P.hu.map (PowerSeries.map (IsLocalRing.residue O))).map (constantCoeff (R := IsLocalRing.ResidueField O))).ne_zero`. Establish `h1 : ((P.φ X).map (IsLocalRing.residue O)).order = (l : ℕ∞)`. Rewrite using `[P.ContD_map_phiX, map_mul, map_pow, PowerSeries.map_X, PowerSeries.order_mul, PowerSeries.order_X_pow]`. Establish `h2 : ((P.u).map (IsLocalRing.residue O)).order = 0`. Rewrite using `[show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]`.

Use `⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply]` and apply the resulting hypothesis. Rewrite using `[h2, zero_add]`. Use `show 1 ≤ ((P.φ X).map (IsLocalRing.residue O)).order.toNat`. Rewrite using `[h1, ENat.toNat_coe]`.

Conclude with `(Nat.Prime.one_lt Fact.out).le`.
-/
theorem PhiData.ContD_wdeg_phiX : 1 ≤ wdeg (P.φ X) := by
  have hu0 : constantCoeff ((P.u).map (IsLocalRing.residue O)) ≠ 0 :=
    ((P.hu.map (PowerSeries.map (IsLocalRing.residue O))).map (constantCoeff (R := IsLocalRing.ResidueField O))).ne_zero
  have h1 : ((P.φ X).map (IsLocalRing.residue O)).order = (l : ℕ∞) := by
    rw [P.ContD_map_phiX, map_mul, map_pow, PowerSeries.map_X, PowerSeries.order_mul,
      PowerSeries.order_X_pow]
    have h2 : ((P.u).map (IsLocalRing.residue O)).order = 0 := by
      rw [show (0 : ℕ∞) = ((0 : ℕ) : ℕ∞) from rfl, PowerSeries.order_eq_nat]
      refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
      rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    rw [h2, zero_add]
  show 1 ≤ ((P.φ X).map (IsLocalRing.residue O)).order.toNat
  rw [h1, ENat.toNat_coe]
  exact (Nat.Prime.one_lt Fact.out).le

/- English proof (translation)
Establish `hpoly : ∀ p : Polynomial O, h (p : O⟦X⟧) = P.φ (p : O⟦X⟧)`. Introduce `p`. Establish `hc : h.comp (Polynomial.coeToPowerSeries.algHom O) = P.φ.comp (Polynomial.coeToPowerSeries.algHom O)`. Apply `Polynomial.algHom_ext` to reduce the goal to its premises. Simplify using `[hX]`.

Use `congrArg (fun ψ : Polynomial O →ₐ[O] O⟦X⟧ => ψ p) hc` as an intermediate fact. Simplify using `using this`. Rewrite using `[← sub_eq_zero]`. Use `ContD.eq_zero_of_forall_dvd_pow hϖ (ContD.not_dvd_of_isDist hϖ (P.ContD_isDist_phiX hϖ)) ?_ _ ?_` and prove the remaining obligations. Rewrite using `[P.ContD_map_phiX]`.

Conclude with `P.constantCoeff_residue_u_X_pow`. Introduce `N`. Establish `hdvd : (X : O⟦X⟧) ^ N ∣ f - (PowerSeries.trunc N f : O⟦X⟧)`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`.

Simplify using `[PowerSeries.coeff_trunc, hm]`. Take `⟨r, hr⟩` from `hdvd`. Establish `hf : f = (PowerSeries.trunc N f : O⟦X⟧) + X ^ N * r` using `by rw [← hr]; ring`. Rewrite using `[hf, map_add, map_add, map_mul, map_mul, map_pow, map_pow, hX, hpoly]`. Conclude with `⟨h r - P.φ r, by ring⟩`.
-/
theorem PhiData.ContD_eq_of_X (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = P.φ X) (f : O⟦X⟧) :
    h f = P.φ f := by
  have hpoly : ∀ p : Polynomial O, h (p : O⟦X⟧) = P.φ (p : O⟦X⟧) := by
    intro p
    have hc : h.comp (Polynomial.coeToPowerSeries.algHom O) =
        P.φ.comp (Polynomial.coeToPowerSeries.algHom O) := by
      apply Polynomial.algHom_ext
      simp [hX]
    have := congrArg (fun ψ : Polynomial O →ₐ[O] O⟦X⟧ => ψ p) hc
    simpa using this
  rw [← sub_eq_zero]
  refine ContD.eq_zero_of_forall_dvd_pow hϖ
    (ContD.not_dvd_of_isDist hϖ (P.ContD_isDist_phiX hϖ)) ?_ _ ?_
  · rw [P.ContD_map_phiX]
    exact P.constantCoeff_residue_u_X_pow
  · intro N
    have hdvd : (X : O⟦X⟧) ^ N ∣ f - (PowerSeries.trunc N f : O⟦X⟧) := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      simp [PowerSeries.coeff_trunc, hm]
    obtain ⟨r, hr⟩ := hdvd
    have hf : f = (PowerSeries.trunc N f : O⟦X⟧) + X ^ N * r := by rw [← hr]; ring
    rw [hf, map_add, map_add, map_mul, map_mul, map_pow, map_pow, hX, hpoly]
    exact ⟨h r - P.φ r, by ring⟩

/- English proof (translation)
Establish `hD` using `P.ContD_wdeg_phiX`. Take `⟨h, hX, -, hu⟩` from `exists_weierstrass_substitution (P.φ X) (P.ContD_isDist_phiX hϖ) hD`. Establish `hh : ∀ f, h f = P.φ f` using `P.ContD_eq_of_X hϖ h hX`. Use `choose c hc using fun f => (hu f).exists`. Establish `huniq : ∀ f d, f = ∑ i : Fin (wdeg (P.φ X)), X ^ (i : ℕ) * h (d i) → c f = d` using `fun f d hd => (hu f).unique (hc f) hd`.

Set `lam : O⟦X⟧ →ₗ[O] O⟦X⟧` to `{ toFun := fun f => c f ⟨0, hD⟩ map_add' := fun f g => by`. Use `huniq (f + g) (fun i => c f i + c g i) (by` as an intermediate fact. Simplify using `only [map_add, mul_add, Finset.sum_add_distrib]`. Rewrite using `[← hc f, ← hc g])`. Conclude with `congrFun this _`.

Use the proof step `map_smul' := fun r f => by`. Use `huniq (r • f) (fun i => r • c f i) (by` as an intermediate fact. Simplify using `only [map_smul, mul_smul_comm]`. Rewrite using `[← Finset.smul_sum, ← hc f])`. Conclude with `congrFun this _ }`.

Use `⟨lam, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b`. Rewrite using `[← hh a]`. Use `huniq (h a * b) (fun i => a * c b i) (by` as an intermediate fact. Simplify using `only [map_mul]`.

Use `conv_lhs => rw [hc b]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use the proof step `ring)`. Conclude with `congrFun this _`.

Introduce `a`. Rewrite using `[← hh a]`. Use `huniq (h a) (fun i => if (i : ℕ) = 0 then a else 0) (by` as an intermediate fact. Rewrite using `[Finset.sum_eq_single ⟨0, hD⟩]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Establish `: (b : ℕ) ≠ 0` using `fun h0 => hb (Fin.ext h0)`. Simplify using `[this]`. Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn)`.

Establish `h2` using `congrFun this ⟨0, hD⟩`. Establish `h3 : c (h a) ⟨0, hD⟩ = a` using `by simpa using h2`. Conclude with `h3`.
-/
theorem PhiData.exists_retraction :
    ∃ lam : O⟦X⟧ →ₗ[O] O⟦X⟧, (∀ a b : O⟦X⟧, lam (P.φ a * b) = a * lam b) ∧ (∀ a, lam (P.φ a) = a) := by
  have hD := P.ContD_wdeg_phiX
  obtain ⟨h, hX, -, hu⟩ := exists_weierstrass_substitution (P.φ X) (P.ContD_isDist_phiX hϖ) hD
  have hh : ∀ f, h f = P.φ f := P.ContD_eq_of_X hϖ h hX
  choose c hc using fun f => (hu f).exists
  have huniq : ∀ f d, f = ∑ i : Fin (wdeg (P.φ X)), X ^ (i : ℕ) * h (d i) → c f = d :=
    fun f d hd => (hu f).unique (hc f) hd
  let lam : O⟦X⟧ →ₗ[O] O⟦X⟧ :=
    { toFun := fun f => c f ⟨0, hD⟩
      map_add' := fun f g => by
        have := huniq (f + g) (fun i => c f i + c g i) (by
          simp only [map_add, mul_add, Finset.sum_add_distrib]
          rw [← hc f, ← hc g])
        exact congrFun this _
      map_smul' := fun r f => by
        have := huniq (r • f) (fun i => r • c f i) (by
          simp only [map_smul, mul_smul_comm]
          rw [← Finset.smul_sum, ← hc f])
        exact congrFun this _ }
  refine ⟨lam, ?_, ?_⟩
  · intro a b
    rw [← hh a]
    have := huniq (h a * b) (fun i => a * c b i) (by
      simp only [map_mul]
      conv_lhs => rw [hc b]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring)
    exact congrFun this _
  · intro a
    rw [← hh a]
    have := huniq (h a) (fun i => if (i : ℕ) = 0 then a else 0) (by
      rw [Finset.sum_eq_single ⟨0, hD⟩]
      · simp
      · intro b _ hb
        have : (b : ℕ) ≠ 0 := fun h0 => hb (Fin.ext h0)
        simp [this]
      · intro hn; exact absurd (Finset.mem_univ _) hn)
    have h2 := congrFun this ⟨0, hD⟩
    have h3 : c (h a) ⟨0, hD⟩ = a := by simpa using h2
    exact h3

/- English proof (translation)
Take `⟨lam, hlam1, hlam2⟩` from `P.exists_retraction hϖ`. Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.1 h`. Rewrite using `[Ideal.mem_span_pair]`. Use `⟨lam a, lam b, ?_⟩` and prove the remaining obligations. Establish `e1 : a * C ϖ ^ k = P.φ (C ϖ ^ k) * a` using `by rw [map_pow, ContD.alg_C, mul_comm]`.

Establish `e2 : b * P.φ g = P.φ g * b` using `mul_comm _ _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hlam1, hlam1]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = lam (a * C ϖ ^ k + b * P.φ g) := by rw [map_add, e1, e2]`.

Use `_ = lam (P.φ f) := by rw [hab]`. Use `_ = f := hlam2 f`.
-/
theorem PhiData.DESC (f g : O⟦X⟧) (k : ℕ)
    (h : P.φ f ∈ Ideal.span {C ϖ ^ k, P.φ g}) : f ∈ Ideal.span {C ϖ ^ k, g} := by
  obtain ⟨lam, hlam1, hlam2⟩ := P.exists_retraction hϖ
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 h
  rw [Ideal.mem_span_pair]
  refine ⟨lam a, lam b, ?_⟩
  have e1 : a * C ϖ ^ k = P.φ (C ϖ ^ k) * a := by rw [map_pow, ContD.alg_C, mul_comm]
  have e2 : b * P.φ g = P.φ g * b := mul_comm _ _
  calc lam a * C ϖ ^ k + lam b * g = lam (P.φ (C ϖ ^ k) * a) + lam (P.φ g * b) := by
        rw [hlam1, hlam1]; ring
    _ = lam (a * C ϖ ^ k + b * P.φ g) := by rw [map_add, e1, e2]
    _ = lam (P.φ f) := by rw [hab]
    _ = f := hlam2 f

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Apply `ContD.enat_le_of_forall` to reduce the goal to its premises. Introduce `k hk`. Rewrite `hk`, the goal using `[← ContD.mem_iff_le]`. Conclude with `P.DESC hϖ f g k hk`.

Apply `ContD.enat_le_of_forall` to reduce the goal to its premises. Introduce `k hk`. Rewrite `hk`, the goal using `[← ContD.mem_iff_le]`. Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.1 hk`. Rewrite using `[Ideal.mem_span_pair]`.

Use `⟨P.φ a, P.φ b, ?_⟩` and prove the remaining obligations. Rewrite using `[← hab, map_add, map_mul, map_mul, map_pow, ContD.alg_C]`.
-/
theorem PhiData.cont_phi_phi_eq {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) :
    cont ϖ (P.φ g) (P.φ f) = cont ϖ g f := by
  apply le_antisymm
  · apply ContD.enat_le_of_forall
    intro k hk
    rw [← ContD.mem_iff_le] at hk ⊢
    exact P.DESC hϖ f g k hk
  · apply ContD.enat_le_of_forall
    intro k hk
    rw [← ContD.mem_iff_le] at hk ⊢
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hk
    rw [Ideal.mem_span_pair]
    refine ⟨P.φ a, P.φ b, ?_⟩
    rw [← hab, map_add, map_mul, map_mul, map_pow, ContD.alg_C]

/- English proof (translation)
The claim follows from `ContD.m5 X (X - C (l : O)) (C (l : O)) A' s hs (by rw [sub_sub_cancel]; exact Ideal.mem_span_singleton_self _)`.
-/
theorem PhiData.X_pow_mem_span_q_pow_l_pow (A' s : ℕ) (hs : 1 ≤ s) :
    (X : O⟦X⟧) ^ (A' + s - 1) ∈ Ideal.span {(X - C (l : O)) ^ A', C (l : O) ^ s} := ContD.m5 X (X - C (l : O)) (C (l : O)) A' s hs
    (by rw [sub_sub_cancel]; exact Ideal.mem_span_singleton_self _)

/- English proof (translation)
Establish `hl` using `(Fact.out : Nat.Prime l).one_lt`. Establish `hp1 : P.p 1 = P.φ X` using `rfl`. Establish `hφX : P.φ X = C (l : O) + P.u * (X - C (l : O)) * X ^ (l - 1)`. Establish `h` using `P.hφ0`. Rewrite `h` using `[map_sub, P.φ_C_l]`.

Take the linear combination `h`. Establish `hl1 : (X : O⟦X⟧) ^ l = X * X ^ (l - 1)`. Rewrite using `[← pow_succ', Nat.sub_add_cancel hl.le]`. Establish `hmem : P.p 1 - P.u * X ^ l ∈ Ideal.span {C (l : O)}`. Rewrite using `[hp1, hφX, Ideal.mem_span_singleton']`.

Conclude with `⟨1 - P.u * X ^ (l - 1), by rw [hl1]; ring⟩`. Establish `hm` using `ContD.m5 (P.p 1) (P.u * X ^ l) (C (l : O)) A' s hs hmem`. Use `Ideal.span_le.2 ?_ hm` and prove the remaining obligations. Rewrite using `[Set.insert_subset_iff, Set.singleton_subset_iff]`. Use `⟨?_, Ideal.subset_span (by simp)⟩` and prove the remaining obligations.

Rewrite using `[mul_pow, ← pow_mul]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`.
-/
theorem PhiData.p_one_pow_mem_span_X_pow_mul_l_pow (A' s : ℕ) (hs : 1 ≤ s) :
    P.p 1 ^ (A' + s - 1) ∈ Ideal.span {(X : O⟦X⟧) ^ (l * A'), C (l : O) ^ s} := by
  have hl := (Fact.out : Nat.Prime l).one_lt
  have hp1 : P.p 1 = P.φ X := rfl
  have hφX : P.φ X = C (l : O) + P.u * (X - C (l : O)) * X ^ (l - 1) := by
    have h := P.hφ0
    rw [map_sub, P.φ_C_l] at h
    linear_combination h
  have hl1 : (X : O⟦X⟧) ^ l = X * X ^ (l - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hl.le]
  have hmem : P.p 1 - P.u * X ^ l ∈ Ideal.span {C (l : O)} := by
    rw [hp1, hφX, Ideal.mem_span_singleton']
    exact ⟨1 - P.u * X ^ (l - 1), by rw [hl1]; ring⟩
  have hm := ContD.m5 (P.p 1) (P.u * X ^ l) (C (l : O)) A' s hs hmem
  refine Ideal.span_le.2 ?_ hm
  rw [Set.insert_subset_iff, Set.singleton_subset_iff]
  refine ⟨?_, Ideal.subset_span (by simp)⟩
  rw [mul_pow, ← pow_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/- English proof (translation)
Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.1 h`. Establish `hgk : ¬ C ϖ ∣ g ^ k` using `fun hd => ContD.not_dvd_of_isDist hϖ hg ((ContD.prime_C hϖ).dvd_of_dvd_pow hd)`. Establish `hsplit : g ^ B' = g ^ k * g ^ (B' - k)` using `by rw [← pow_add, Nat.add_sub_cancel' hk]`. Rewrite `hab` using `[hsplit]`. Establish `hd : C ϖ ^ s ∣ g ^ k * (F - b * g ^ (B' - k))` using `⟨a, by linear_combination -hab⟩`.

Take `⟨c, hc⟩` from `ContD.pow_dvd_of_dvd_mul hϖ hgk s _ hd`. Rewrite using `[Ideal.mem_span_pair]`. Conclude with `⟨c, b, by linear_combination -hc⟩`.
-/
theorem V2 {g : O⟦X⟧} (hg : IsDist g) (k B' s : ℕ) (hk : k ≤ B') (F : O⟦X⟧)
    (h : g ^ k * F ∈ Ideal.span {C ϖ ^ s, g ^ B'}) : F ∈ Ideal.span {C ϖ ^ s, g ^ (B' - k)} := by
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 h
  have hgk : ¬ C ϖ ∣ g ^ k := fun hd =>
    ContD.not_dvd_of_isDist hϖ hg ((ContD.prime_C hϖ).dvd_of_dvd_pow hd)
  have hsplit : g ^ B' = g ^ k * g ^ (B' - k) := by rw [← pow_add, Nat.add_sub_cancel' hk]
  rw [hsplit] at hab
  have hd : C ϖ ^ s ∣ g ^ k * (F - b * g ^ (B' - k)) := ⟨a, by linear_combination -hab⟩
  obtain ⟨c, hc⟩ := ContD.pow_dvd_of_dvd_mul hϖ hgk s _ hd
  rw [Ideal.mem_span_pair]
  exact ⟨c, b, by linear_combination -hc⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
