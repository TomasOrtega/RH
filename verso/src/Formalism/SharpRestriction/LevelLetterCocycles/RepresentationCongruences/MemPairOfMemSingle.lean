import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.QuotientDistinguishedTorsionFree
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Filtration

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

noncomputable def cont (ϖ : O) (g f : O⟦X⟧) : ℕ∞ :=
  ⨆ (k : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ k, g}), (k : ℕ∞)

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hb : b ≠ ⊤` using `ne_top_of_lt hlt`. Take `⟨n, rfl⟩` from `ENat.ne_top_iff_exists.1 hb`. Establish `h1 : ((n + 1 : ℕ) : ℕ∞) ≤ a`.

Establish `h2` using `(ENat.add_one_le_iff hb).2 hlt`. Conclude with `h2` after adjusting the coercions. Establish `h2` using `h (n + 1) h1`. Normalize the coercions in `at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem Cont.enat_le_of_forall {a b : ℕ∞} (h : ∀ k : ℕ, (k : ℕ∞) ≤ a → (k : ℕ∞) ≤ b) : a ≤ b := by
  by_contra hlt
  push_neg at hlt
  have hb : b ≠ ⊤ := ne_top_of_lt hlt
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.1 hb
  have h1 : ((n + 1 : ℕ) : ℕ∞) ≤ a := by
    have h2 := (ENat.add_one_le_iff hb).2 hlt
    exact_mod_cast h2
  have h2 := h (n + 1) h1
  norm_cast at h2
  omega

/- English proof (translation)
Use `(Ideal.span_le.2 ?_) h` and prove the remaining obligations. Introduce `x hx`. Break down `hx with rfl | rfl` into its components or cases. Establish `e : C ϖ ^ k = C ϖ ^ j * C ϖ ^ (k - j)` using `by rw [← pow_add, Nat.add_sub_cancel' hjk]`. Rewrite using `[e]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))`. Conclude with `Ideal.subset_span (by simp)`.
-/
theorem Cont.mem_pair_mono (ϖ : O) (g f : O⟦X⟧) {j k : ℕ} (hjk : j ≤ k)
    (h : f ∈ Ideal.span {C ϖ ^ k, g}) : f ∈ Ideal.span {C ϖ ^ j, g} := by
  refine (Ideal.span_le.2 ?_) h
  intro x hx
  rcases hx with rfl | rfl
  · have e : C ϖ ^ k = C ϖ ^ j * C ϖ ^ (k - j) := by rw [← pow_add, Nat.add_sub_cancel' hjk]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · exact Ideal.subset_span (by simp)

/- English proof (translation)
Establish `h1 : (1 : O⟦X⟧) ∈ Ideal.span {C ϖ ^ 0, g}` using `Ideal.subset_span (by simp)`. Simplify using `using Ideal.mul_mem_left _ f h1`.
-/
theorem Cont.mem_zero (ϖ : O) (g f : O⟦X⟧) : f ∈ Ideal.span {C ϖ ^ 0, g} := by
  have h1 : (1 : O⟦X⟧) ∈ Ideal.span {C ϖ ^ 0, g} := Ideal.subset_span (by simp)
  simpa using Ideal.mul_mem_left _ f h1

/- English proof (translation)
Unfold `cont`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `le_iSup₂ (f := fun (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}) => (j : ℕ∞)) k h`. Introduce `hk`.

Assume the negation of the conclusion as `hnot`. Establish `hk0 : k ≠ 0`. Introduce and unpack `rfl`. Conclude with `hnot (Cont.mem_zero ϖ g f)`. Establish `hbound : (⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)) ≤ ((k - 1 : ℕ) : ℕ∞)`.

Apply `iSup₂_le` to reduce the goal to its premises. Introduce `j hj`. Establish `hj' : j ≤ k - 1`. Assume the negation of the conclusion as `hjk`. Use `push_neg at hjk`.

Conclude with `hnot (Cont.mem_pair_mono ϖ g f (by omega) hj)`. Conclude with `hj'` after adjusting the coercions. Establish `h3` using `le_trans hk hbound`. Normalize the coercions in `at h3`. Use linear arithmetic over natural numbers and integers.
-/
theorem Cont.mem_iff_le (ϖ : O) (g f : O⟦X⟧) (k : ℕ) :
    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
  unfold cont
  constructor
  · intro h
    exact le_iSup₂ (f := fun (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}) => (j : ℕ∞)) k h
  · intro hk
    by_contra hnot
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hnot (Cont.mem_zero ϖ g f)
    have hbound : (⨆ (j : ℕ) (_ : f ∈ Ideal.span {C ϖ ^ j, g}), (j : ℕ∞)) ≤ ((k - 1 : ℕ) : ℕ∞) := by
      apply iSup₂_le
      intro j hj
      have hj' : j ≤ k - 1 := by
        by_contra hjk
        push_neg at hjk
        exact hnot (Cont.mem_pair_mono ϖ g f (by omega) hj)
      exact_mod_cast hj'
    have h3 := le_trans hk hbound
    norm_cast at h3
    omega

/- English proof (translation)
Conclude with `(IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit`.
-/
theorem Cont.residue_unif {ϖ : O} (hϖ : Irreducible ϖ) : IsLocalRing.residue O ϖ = 0 := by
  exact (IsLocalRing.residue_eq_zero_iff ϖ).2 hϖ.not_isUnit

/- English proof (translation)
Introduce `h`. Apply `hϖ.ne_zero` to reduce the goal to its premises. Establish `h1` using `congrArg PowerSeries.constantCoeff h`. Simplify using `using h1`.
-/
theorem Cont.C_unif_ne_zero {ϖ : O} (hϖ : Irreducible ϖ) : (C ϖ : O⟦X⟧) ≠ 0 := by
  intro h
  apply hϖ.ne_zero
  have h1 := congrArg PowerSeries.constantCoeff h
  simpa using h1

/- English proof (translation)
Establish `hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ`. Establish `hc : ∀ n, ∃ c, PowerSeries.coeff n f = ϖ * c`. Introduce `n`. Establish `h1 : IsLocalRing.residue O (PowerSeries.coeff n f) = 0`. Establish `h2` using `congrArg (PowerSeries.coeff n) hf`.

Simplify `h2` using `[PowerSeries.coeff_map]`. Rewrite `h1` using `[IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `h1`. Conclude with `⟨c, by rw [← hc, mul_comm]⟩`. Use `choose c hc using hc`.

Use `⟨PowerSeries.mk c, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc n]`.
-/
theorem Cont.C_dvd_of_map_eq_zero {ϖ : O} (hϖ : Irreducible ϖ) (f : O⟦X⟧)
    (hf : f.map (IsLocalRing.residue O) = 0) : C ϖ ∣ f := by
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hc : ∀ n, ∃ c, PowerSeries.coeff n f = ϖ * c := by
    intro n
    have h1 : IsLocalRing.residue O (PowerSeries.coeff n f) = 0 := by
      have h2 := congrArg (PowerSeries.coeff n) hf
      simpa [PowerSeries.coeff_map] using h2
    rw [IsLocalRing.residue_eq_zero_iff, hmax, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hc n]

/- English proof (translation)
Use `⟨Cont.C_unif_ne_zero hϖ, ?_, ?_⟩` and prove the remaining obligations. Introduce `hu`. Establish `h1` using `hu.map (PowerSeries.constantCoeff (R := O))`. Rewrite `h1` using `[PowerSeries.constantCoeff_C]`. Conclude with `hϖ.not_isUnit h1`.

Introduce `f g hfg`. Establish `hmap : (f * g).map (IsLocalRing.residue O) = 0`. Take `⟨h, hh⟩` from `hfg`. Rewrite using `[hh, map_mul, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, zero_mul]`. Rewrite `hmap` using `[map_mul]`.

Break down `mul_eq_zero.1 hmap with h | h` into its components or cases. Conclude with `Or.inl (Cont.C_dvd_of_map_eq_zero hϖ f h)`. Conclude with `Or.inr (Cont.C_dvd_of_map_eq_zero hϖ g h)`.
-/
theorem Cont.prime_C_unif {ϖ : O} (hϖ : Irreducible ϖ) : Prime (C ϖ : O⟦X⟧) := by
  refine ⟨Cont.C_unif_ne_zero hϖ, ?_, ?_⟩
  · intro hu
    have h1 := hu.map (PowerSeries.constantCoeff (R := O))
    rw [PowerSeries.constantCoeff_C] at h1
    exact hϖ.not_isUnit h1
  · intro f g hfg
    have hmap : (f * g).map (IsLocalRing.residue O) = 0 := by
      obtain ⟨h, hh⟩ := hfg
      rw [hh, map_mul, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, zero_mul]
    rw [map_mul] at hmap
    rcases mul_eq_zero.1 hmap with h | h
    · exact Or.inl (Cont.C_dvd_of_map_eq_zero hϖ f h)
    · exact Or.inr (Cont.C_dvd_of_map_eq_zero hϖ g h)

/- English proof (translation)
Introduce and unpack `⟨h, hh⟩`. Apply `hg` to reduce the goal to its premises. Rewrite using `[hh, map_mul, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, zero_mul]`.
-/
theorem Cont.not_C_dvd {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : IsDist g) : ¬ (C ϖ ∣ g) := by
  rintro ⟨h, hh⟩
  apply hg
  rw [hh, map_mul, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, zero_mul]

/- English proof (translation)
Proceed by induction on `n generalizing h with`. Consider the case `zero => simpa using hm`. Consider the case `succ n ih`. Apply `ih` to reduce the goal to its premises. Take `⟨q, hq⟩` from `Ideal.mem_span_singleton'.1 hm`.

Establish `hdvd : C ϖ ∣ q * g` using `⟨C ϖ ^ n * h, by rw [hq, pow_succ]; ring⟩`. Break down `(Cont.prime_C_unif hϖ).2.2 q g hdvd with ⟨q', rfl⟩ | hg'` into its components or cases. Rewrite using `[Ideal.mem_span_singleton']`. Use `⟨q', ?_⟩` and prove the remaining obligations. Establish `h1 : C ϖ * (q' * g) = C ϖ * (C ϖ ^ n * h)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `mul_left_cancel₀ (Cont.C_unif_ne_zero hϖ) h1`. Conclude with `absurd hg' (Cont.not_C_dvd hϖ hg)`.
-/
theorem Cont.mem_of_pow_mul_mem {ϖ : O} (hϖ : Irreducible ϖ) {g : O⟦X⟧} (hg : IsDist g) (n : ℕ)
    (h : O⟦X⟧) (hm : C ϖ ^ n * h ∈ Ideal.span {g}) : h ∈ Ideal.span {g} := by
  induction n generalizing h with
  | zero => simpa using hm
  | succ n ih =>
    apply ih
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 hm
    have hdvd : C ϖ ∣ q * g := ⟨C ϖ ^ n * h, by rw [hq, pow_succ]; ring⟩
    rcases (Cont.prime_C_unif hϖ).2.2 q g hdvd with ⟨q', rfl⟩ | hg'
    · rw [Ideal.mem_span_singleton']
      refine ⟨q', ?_⟩
      have h1 : C ϖ * (q' * g) = C ϖ * (C ϖ ^ n * h) := by
        calc C ϖ * (q' * g) = C ϖ * q' * g := by ring
          _ = C ϖ ^ (n + 1) * h := hq
          _ = C ϖ * (C ϖ ^ n * h) := by ring
      exact mul_left_cancel₀ (Cont.C_unif_ne_zero hϖ) h1
    · exact absurd hg' (Cont.not_C_dvd hϖ hg)

/- English proof (translation)
Rewrite using `[Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul]`. Both sides reduce to the same expression.
-/
theorem Cont.smul_mk (g : O⟦X⟧) (r : O) (a : O⟦X⟧) :
    r • Ideal.Quotient.mk (Ideal.span {g}) a = Ideal.Quotient.mk (Ideal.span {g}) (C r * a) := by
  rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul]
  rfl

variable {ϖ : O} (hϖ : Irreducible ϖ)
include hϖ

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, n, h⟩`. Establish `h1` using `Cont.mem_of_pow_mul_mem hϖ hg n _ h`. Establish `h2 : f = C ϖ ^ k * a + (f - C ϖ ^ k * a)` using `by ring`. Rewrite using `[h2]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))) (Ideal.span_mono (Set.subset_insert _ _) h1)`. Introduce `hf`. Take `⟨u, v, huv⟩` from `Ideal.mem_span_pair.1 hf`. Use `⟨u, 0, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero, one_mul, ← huv, Ideal.mem_span_singleton']`.

Conclude with `⟨v, by ring⟩`.
-/
theorem C2' {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) (k : ℕ) :
    (∃ (a : O⟦X⟧) (n : ℕ), C ϖ ^ n * (f - C ϖ ^ k * a) ∈ Ideal.span {g}) ↔
      f ∈ Ideal.span {C ϖ ^ k, g} := by
  constructor
  · rintro ⟨a, n, h⟩
    have h1 := Cont.mem_of_pow_mul_mem hϖ hg n _ h
    have h2 : f = C ϖ ^ k * a + (f - C ϖ ^ k * a) := by ring
    rw [h2]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.span_mono (Set.subset_insert _ _) h1)
  · intro hf
    obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hf
    refine ⟨u, 0, ?_⟩
    rw [pow_zero, one_mul, ← huv, Ideal.mem_span_singleton']
    exact ⟨v, by ring⟩

/- English proof (translation)
Conclude with `Cont.mem_iff_le ϖ g f k`.
-/
theorem mem_iff_le_cont {g : O⟦X⟧} (hg : IsDist g) (f : O⟦X⟧) (k : ℕ) :
    f ∈ Ideal.span {C ϖ ^ k, g} ↔ (k : ℕ∞) ≤ cont ϖ g f := by
  exact Cont.mem_iff_le ϖ g f k

/- English proof (translation)
Establish `key : ∀ k : ℕ, f ∈ Ideal.span {C ϖ ^ k, g} ↔ ∀ i, ϖ ^ k ∣ b.repr (Ideal.Quotient.mk (Ideal.span {g}) f) i`. Introduce `k`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a, d, had⟩` from `Ideal.mem_span_pair.mp h`.

Establish `hq : Ideal.Quotient.mk (Ideal.span {g}) f = ϖ ^ k • Ideal.Quotient.mk (Ideal.span {g}) a`. Rewrite using `[Cont.smul_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Conclude with `⟨d, by rw [map_pow]; linear_combination had⟩`. Introduce `i`. Rewrite using `[hq, map_smul, Finsupp.smul_apply, smul_eq_mul]`.

Conclude with `dvd_mul_right _ _`. Introduce `h choose c hc using h`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (b.equivFun.symm c)`. Establish `hx : Ideal.Quotient.mk (Ideal.span {g}) f = ϖ ^ k • Ideal.Quotient.mk (Ideal.span {g}) a`. Apply `b.repr.injective` to reduce the goal to its premises.

Use extensionality with `i`. Establish `e1` using `congrFun (b.equivFun.apply_symm_apply c) i`. Rewrite `e1` using `[Module.Basis.equivFun_apply]`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul, hc i, ha, e1]`. Rewrite `hx` using `[Cont.smul_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton']`.

Take `⟨d, hd⟩` from `hx`. Rewrite `hd` using `[map_pow]`. Conclude with `Ideal.mem_span_pair.mpr ⟨a, d, by linear_combination hd⟩`. Establish `key2 : ∀ k : ℕ, (k : ℕ∞) ≤ cont ϖ g f ↔ (k : ℕ∞) ≤ ⨅ i, IsDiscreteValuationRing.addVal O (b.repr (Ideal.Quotient.mk _ f) i)`. Introduce `k`.

Rewrite using `[← Cont.mem_iff_le ϖ g f k, key k, le_iInf_iff]`. Apply `forall_congr'` to reduce the goal to its premises. Introduce `i`. Rewrite using `[← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]`. Conclude with `le_antisymm (Cont.enat_le_of_forall fun k hk => (key2 k).mp hk) (Cont.enat_le_of_forall fun k hk => (key2 k).mpr hk)`.
-/
theorem C0 {g : O⟦X⟧} (hg : IsDist g) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι O (O⟦X⟧ ⧸ Ideal.span {g})) (f : O⟦X⟧) :
    cont ϖ g f = ⨅ i, IsDiscreteValuationRing.addVal O (b.repr (Ideal.Quotient.mk _ f) i) := by
  have key : ∀ k : ℕ, f ∈ Ideal.span {C ϖ ^ k, g} ↔
      ∀ i, ϖ ^ k ∣ b.repr (Ideal.Quotient.mk (Ideal.span {g}) f) i := by
    intro k
    constructor
    · intro h
      obtain ⟨a, d, had⟩ := Ideal.mem_span_pair.mp h
      have hq : Ideal.Quotient.mk (Ideal.span {g}) f = ϖ ^ k • Ideal.Quotient.mk (Ideal.span {g}) a := by
        rw [Cont.smul_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton']
        exact ⟨d, by rw [map_pow]; linear_combination had⟩
      intro i
      rw [hq, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    · intro h
      choose c hc using h
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (b.equivFun.symm c)
      have hx : Ideal.Quotient.mk (Ideal.span {g}) f = ϖ ^ k • Ideal.Quotient.mk (Ideal.span {g}) a := by
        apply b.repr.injective
        ext i
        have e1 := congrFun (b.equivFun.apply_symm_apply c) i
        rw [Module.Basis.equivFun_apply] at e1
        rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hc i, ha, e1]
      rw [Cont.smul_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton'] at hx
      obtain ⟨d, hd⟩ := hx
      rw [map_pow] at hd
      exact Ideal.mem_span_pair.mpr ⟨a, d, by linear_combination hd⟩
  have key2 : ∀ k : ℕ, (k : ℕ∞) ≤ cont ϖ g f ↔
      (k : ℕ∞) ≤ ⨅ i, IsDiscreteValuationRing.addVal O (b.repr (Ideal.Quotient.mk _ f) i) := by
    intro k
    rw [← Cont.mem_iff_le ϖ g f k, key k, le_iInf_iff]
    apply forall_congr'
    intro i
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]
  exact le_antisymm (Cont.enat_le_of_forall fun k hk => (key2 k).mp hk)
    (Cont.enat_le_of_forall fun k hk => (key2 k).mpr hk)

/- English proof (translation)
Apply `Cont.enat_le_of_forall` to reduce the goal to its premises. Introduce `k hk`. Establish `h1` using `(Cont.mem_iff_le ϖ g' f k).2 hk`. Apply `(Cont.mem_iff_le ϖ g f k).1` to reduce the goal to its premises. Use `(Ideal.span_le.2 ?_) h1` and prove the remaining obligations.

Introduce `x hx`. Break down `hx with rfl | rfl` into its components or cases. Conclude with `Ideal.subset_span (by simp)`. Take `⟨c, rfl⟩` from `hdvd`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))`.
-/
theorem m1 {g g' : O⟦X⟧} (hg : IsDist g) (hg' : IsDist g') (hdvd : g ∣ g') (f : O⟦X⟧) :
    cont ϖ g' f ≤ cont ϖ g f := by
  apply Cont.enat_le_of_forall
  intro k hk
  have h1 := (Cont.mem_iff_le ϖ g' f k).2 hk
  apply (Cont.mem_iff_le ϖ g f k).1
  refine (Ideal.span_le.2 ?_) h1
  intro x hx
  rcases hx with rfl | rfl
  · exact Ideal.subset_span (by simp)
  · obtain ⟨c, rfl⟩ := hdvd
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

/- English proof (translation)
Apply `Cont.enat_le_of_forall` to reduce the goal to its premises. Introduce `j hj`. Conclude with `(Cont.mem_iff_le ϖ g _ j).1 (Ideal.mul_mem_left _ k ((Cont.mem_iff_le ϖ g f j).2 hj))`.
-/
theorem m2 {g : O⟦X⟧} (hg : IsDist g) (k f : O⟦X⟧) : cont ϖ g f ≤ cont ϖ g (k * f) := by
  apply Cont.enat_le_of_forall
  intro j hj
  exact (Cont.mem_iff_le ϖ g _ j).1 (Ideal.mul_mem_left _ k ((Cont.mem_iff_le ϖ g f j).2 hj))

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `h1 : ((1 : ℕ) : ℕ∞) ≤ cont ϖ g f`. Rewrite using `[Nat.cast_one]`. Conclude with `ENat.one_le_iff_ne_zero.2 hne`. Establish `h2` using `(Cont.mem_iff_le ϖ g f 1).2 h1`.

Take `⟨u, v, huv⟩` from `Ideal.mem_span_pair.1 h2`. Establish `hmap : f.map (IsLocalRing.residue O) = v.map (IsLocalRing.residue O) * g.map (IsLocalRing.residue O)`. Rewrite using `[← huv, map_add, map_mul, map_mul, pow_one, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero, mul_zero, zero_add]`. Establish `hord : (g.map (IsLocalRing.residue O)).order ≤ (f.map (IsLocalRing.residue O)).order`. Rewrite using `[hmap, PowerSeries.order_mul]`.

Conclude with `le_add_self`. Establish `hf0 : (f.map (IsLocalRing.residue O)).order ≠ ⊤` using `fun h => hf (PowerSeries.order_eq_top.1 h)`. Establish `h3` using `ENat.toNat_le_toNat hord hf0`. Unfold `wdeg at hlt`. Use linear arithmetic over natural numbers and integers.
-/
theorem m3 {g f : O⟦X⟧} (hg : IsDist g) (hf : IsDist f) (hlt : wdeg f < wdeg g) :
    cont ϖ g f = 0 := by
  by_contra hne
  have h1 : ((1 : ℕ) : ℕ∞) ≤ cont ϖ g f := by
    rw [Nat.cast_one]
    exact ENat.one_le_iff_ne_zero.2 hne
  have h2 := (Cont.mem_iff_le ϖ g f 1).2 h1
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 h2
  have hmap : f.map (IsLocalRing.residue O) =
      v.map (IsLocalRing.residue O) * g.map (IsLocalRing.residue O) := by
    rw [← huv, map_add, map_mul, map_mul, pow_one, PowerSeries.map_C, Cont.residue_unif hϖ, map_zero,
      mul_zero, zero_add]
  have hord : (g.map (IsLocalRing.residue O)).order ≤ (f.map (IsLocalRing.residue O)).order := by
    rw [hmap, PowerSeries.order_mul]
    exact le_add_self
  have hf0 : (f.map (IsLocalRing.residue O)).order ≠ ⊤ := fun h => hf (PowerSeries.order_eq_top.1 h)
  have h3 := ENat.toNat_le_toNat hord hf0
  unfold wdeg at hlt
  omega

omit hϖ in

/- English proof (translation)
Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 h`. Establish `hx : x = x' + t * y` using `by linear_combination (-1 : R) * hy`. Rewrite using `[hx, add_pow]`. Apply `Ideal.sum_mem` to reduce the goal to its premises. Introduce `m hm`.

Rewrite `hm` using `[Finset.mem_range]`. Distinguish the cases in `ham : a ≤ m`. Establish `e : x' ^ m = x' ^ a * x' ^ (m - a)` using `by rw [← pow_add, Nat.add_sub_cancel' ham]`. Rewrite using `[e]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises.

Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Conclude with `Ideal.subset_span (by simp)`. Use `push_neg at ham`. Establish `hs' : s ≤ a + s - 1 - m` using `by omega`.

Establish `e : (t * y) ^ (a + s - 1 - m) = t ^ s * (t ^ (a + s - 1 - m - s) * y ^ (a + s - 1 - m))`. Rewrite using `[mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hs']`. Rewrite using `[e]`. Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Apply `Ideal.mul_mem_left` to reduce the goal to its premises.

Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Conclude with `Ideal.subset_span (by simp)`.
-/
theorem m5 {R : Type*} [CommRing R] (x x' t : R) (a s : ℕ) (hs : 1 ≤ s)
    (h : x - x' ∈ Ideal.span {t}) : x ^ (a + s - 1) ∈ Ideal.span {x' ^ a, t ^ s} := by
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h
  have hx : x = x' + t * y := by linear_combination (-1 : R) * hy
  rw [hx, add_pow]
  apply Ideal.sum_mem
  intro m hm
  rw [Finset.mem_range] at hm
  by_cases ham : a ≤ m
  · have e : x' ^ m = x' ^ a * x' ^ (m - a) := by rw [← pow_add, Nat.add_sub_cancel' ham]
    rw [e]
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_right
    exact Ideal.subset_span (by simp)
  · push_neg at ham
    have hs' : s ≤ a + s - 1 - m := by omega
    have e : (t * y) ^ (a + s - 1 - m) = t ^ s * (t ^ (a + s - 1 - m - s) * y ^ (a + s - 1 - m)) := by
      rw [mul_pow, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hs']
    rw [e]
    apply Ideal.mul_mem_right
    apply Ideal.mul_mem_left
    apply Ideal.mul_mem_right
    exact Ideal.subset_span (by simp)

end Formalism.MainNotions.N.FrobeniusPowerSeries
