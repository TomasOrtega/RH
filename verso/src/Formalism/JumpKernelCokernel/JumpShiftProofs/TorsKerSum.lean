import Formalism.JumpKernelCokernel.Statement

noncomputable section

namespace Formalism.KernelCokernelLengths.TorsionKernelSumLemmas

open PowerSeries

variable {O : Type} [CommRing O]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Establish `hs : Subsingleton (O ⧸ Ideal.span {ℓ ^ 0})` using `Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one])`. Rewrite using `[Module.length_eq_zero, Nat.cast_zero, zero_mul]`. Consider the case `succ k ih`.

Establish `hle : Ideal.span {ℓ} ≤ Submodule.comap (LinearMap.mulLeft O (ℓ ^ k)) (Ideal.span {ℓ ^ (k + 1)})`. Introduce `x hx`. Rewrite using `[Submodule.mem_comap, LinearMap.mulLeft_apply]`. Take `⟨y, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Conclude with `Ideal.mem_span_singleton.mpr ⟨y, by ring⟩`.

Establish `hge : Ideal.span {ℓ ^ (k + 1)} ≤ Ideal.span {ℓ ^ k}` using `Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ℓ k.le_succ)`. Establish `hk : ℓ ^ k ≠ 0` using `pow_ne_zero k hℓ`. Establish `hf : Function.Injective (Submodule.mapQ _ _ (LinearMap.mulLeft O (ℓ ^ k)) hle)`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `x hx`.

Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[LinearMap.mem_ker, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]`. Rewrite using `[Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `hx`. Use `⟨c, mul_left_cancel₀ hk ?_⟩` and prove the remaining obligations.

Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hg : Function.Surjective (Submodule.factor hge)`. Introduce `y`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`.

Conclude with `⟨Submodule.Quotient.mk a, rfl⟩`. Establish `hex : Function.Exact (Submodule.mapQ _ _ (LinearMap.mulLeft O (ℓ ^ k)) hle) (Submodule.factor hge)`. Introduce `y`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h' : a ∈ Ideal.span {ℓ ^ k}`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Conclude with `h`. Take `⟨c, hc⟩` from `Ideal.mem_span_singleton.mp h'`.

Conclude with `⟨Submodule.Quotient.mk c, by rw [Submodule.mapQ_apply, LinearMap.mulLeft_apply, hc]⟩`. Introduce and unpack `⟨x, hx⟩`. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[← hx, Submodule.mapQ_apply, LinearMap.mulLeft_apply]`. Use `show (Submodule.Quotient.mk (ℓ ^ k * c) : O ⧸ Ideal.span {ℓ ^ k}) = 0`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)`. Rewrite using `[Module.length_eq_add_of_exact _ _ hf hg hex, ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem len_pow [IsDomain O] (ℓ : O) (hℓ : ℓ ≠ 0) (k : ℕ) :
    Module.length O (O ⧸ Ideal.span {ℓ ^ k}) = (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  induction k with
  | zero =>
    have hs : Subsingleton (O ⧸ Ideal.span {ℓ ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one])
    rw [Module.length_eq_zero, Nat.cast_zero, zero_mul]
  | succ k ih =>

    have hle : Ideal.span {ℓ} ≤ Submodule.comap (LinearMap.mulLeft O (ℓ ^ k)) (Ideal.span {ℓ ^ (k + 1)}) := by
      intro x hx
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      exact Ideal.mem_span_singleton.mpr ⟨y, by ring⟩
    have hge : Ideal.span {ℓ ^ (k + 1)} ≤ Ideal.span {ℓ ^ k} :=
      Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ℓ k.le_succ)
    have hk : ℓ ^ k ≠ 0 := pow_ne_zero k hℓ
    have hf : Function.Injective (Submodule.mapQ _ _ (LinearMap.mulLeft O (ℓ ^ k)) hle) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, LinearMap.mulLeft_apply,
        Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at hx
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, mul_left_cancel₀ hk ?_⟩
      rw [hc]
      ring
    have hg : Function.Surjective (Submodule.factor hge) := by
      intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk a, rfl⟩
    have hex : Function.Exact (Submodule.mapQ _ _ (LinearMap.mulLeft O (ℓ ^ k)) hle) (Submodule.factor hge) := by
      intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      constructor
      · intro h
        have h' : a ∈ Ideal.span {ℓ ^ k} := by
          rw [← Submodule.Quotient.mk_eq_zero]
          exact h
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h'
        exact ⟨Submodule.Quotient.mk c, by rw [Submodule.mapQ_apply, LinearMap.mulLeft_apply, hc]⟩
      · rintro ⟨x, hx⟩
        obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [← hx, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
        show (Submodule.Quotient.mk (ℓ ^ k * c) : O ⧸ Ideal.span {ℓ ^ k}) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    rw [Module.length_eq_add_of_exact _ _ hf hg hex, ih]
    push_cast
    ring

abbrev J (ℓ : O) (n k : ℕ) : Ideal (PowerSeries O) :=
  Ideal.span {(X : PowerSeries O) ^ n, C (ℓ ^ k)}

/- English proof (translation)
Introduce `i hi`. Take `⟨a, c, rfl⟩` from `Ideal.mem_span_pair.mp hr`. Rewrite using `[map_add, coeff_mul_X_pow', if_neg (by omega), zero_add, coeff_mul_C]`. Conclude with `dvd_mul_left _ _`.
-/
theorem coeff_dvd_of_mem (ℓ : O) (n k : ℕ) {r : PowerSeries O} (hr : r ∈ J ℓ n k) :
    ∀ i < n, ℓ ^ k ∣ coeff i r := by
  intro i hi
  obtain ⟨a, c, rfl⟩ := Ideal.mem_span_pair.mp hr
  rw [map_add, coeff_mul_X_pow', if_neg (by omega), zero_add, coeff_mul_C]
  exact dvd_mul_left _ _

/- English proof (translation)
Establish `hp' : ∀ i < n, ∃ c, coeff i p = ℓ ^ k * c` using `fun i hi => hp i hi`. Use `choose! c hc using hp'`. Use `Ideal.mem_span_pair.mpr ⟨PowerSeries.mk fun j => coeff (j + n) p, PowerSeries.mk fun i => if i < n then c i else 0, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Rewrite using `[map_add, coeff_mul_X_pow', coeff_mul_C, coeff_mk, coeff_mk]`.

Use `split_ifs with h1 h2 h2`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Nat.sub_add_cancel h1]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc i h2]`.

Expand and normalize the polynomial expressions, which then agree. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_of_coeff_dvd (ℓ : O) (n k : ℕ) (p : PowerSeries O)
    (hp : ∀ i < n, ℓ ^ k ∣ coeff i p) : p ∈ J ℓ n k := by
  have hp' : ∀ i < n, ∃ c, coeff i p = ℓ ^ k * c := fun i hi => hp i hi
  choose! c hc using hp'
  refine Ideal.mem_span_pair.mpr
    ⟨PowerSeries.mk fun j => coeff (j + n) p, PowerSeries.mk fun i => if i < n then c i else 0, ?_⟩
  ext i
  rw [map_add, coeff_mul_X_pow', coeff_mul_C, coeff_mk, coeff_mk]
  split_ifs with h1 h2 h2
  · omega
  · rw [Nat.sub_add_cancel h1]
    ring
  · rw [hc i h2]
    ring
  · omega

/- English proof (translation)
Rewrite using `[sub_mul, map_sub, coeff_succ_X_mul, coeff_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeff_step (ℓ : O) (p : PowerSeries O) (i : ℕ) :
    coeff i p = coeff (i + 1) ((X - C ℓ) * p) + ℓ * coeff (i + 1) p := by
  rw [sub_mul, map_sub, coeff_succ_X_mul, coeff_C_mul]
  ring

/- English proof (translation)
Establish `key : ∀ j i, i + j = n - 1 → i < n → ℓ ^ k ∣ coeff i p`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `i hij _`.

Rewrite using `[show i = n - 1 by omega]`. Conclude with `htop`. Consider the case `succ j ih`. Introduce `i hij hi`. Rewrite using `[Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_step ℓ p i]`.

Conclude with `dvd_add (Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_dvd_of_mem ℓ n k hp (i + 1) (by omega)) (dvd_mul_of_dvd_right (ih (i + 1) (by omega) (by omega)) _)`. Introduce `i hi`. Conclude with `key (n - 1 - i) i (by omega) hi`.
-/
theorem all_coeff_dvd (ℓ : O) (n k : ℕ) (p : PowerSeries O) (hp : (X - C ℓ) * p ∈ J ℓ n k)
    (htop : ℓ ^ k ∣ coeff (n - 1) p) : ∀ i < n, ℓ ^ k ∣ coeff i p := by

  have key : ∀ j i, i + j = n - 1 → i < n → ℓ ^ k ∣ coeff i p := by
    intro j
    induction j with
    | zero =>
      intro i hij _
      rw [show i = n - 1 by omega]
      exact htop
    | succ j ih =>
      intro i hij hi
      rw [Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_step ℓ p i]
      exact dvd_add (Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_dvd_of_mem ℓ n k hp (i + 1) (by omega))
        (dvd_mul_of_dvd_right (ih (i + 1) (by omega) (by omega)) _)
  intro i hi
  exact key (n - 1 - i) i (by omega) hi

def lift (ℓ : O) (n k : ℕ) : (PowerSeries O ⧸ J ℓ n k) → PowerSeries O :=
  Function.surjInv Ideal.Quotient.mk_surjective

/- English proof (translation)
The claim follows from `Function.surjInv_eq Ideal.Quotient.mk_surjective b`.
-/
theorem mk_lift (ℓ : O) (n k : ℕ) (b : PowerSeries O ⧸ J ℓ n k) :
    Ideal.Quotient.mk (J ℓ n k) (lift ℓ n k b) = b := Function.surjInv_eq Ideal.Quotient.mk_surjective b

def topFun (ℓ : O) (n k : ℕ) (b : PowerSeries O ⧸ J ℓ n k) : O ⧸ Ideal.span {ℓ ^ k} :=
  Ideal.Quotient.mk _ (coeff (n - 1) (lift ℓ n k b))

/- English proof (translation)
Unfold `Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.topFun`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Establish `h` using `Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.mk_lift ℓ n k (Ideal.Quotient.mk _ p)`. Rewrite `h` using `[Ideal.Quotient.eq]`. Establish `h2` using `Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_dvd_of_mem ℓ n k h (n - 1) (by omega)`.

Rewrite `h2` using `[map_sub]`. Then use the resulting hypothesis.
-/
theorem topFun_mk (ℓ : O) (n k : ℕ) (hn : 0 < n) (p : PowerSeries O) :
    topFun ℓ n k (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (coeff (n - 1) p) := by
  unfold Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.topFun
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have h := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.mk_lift ℓ n k (Ideal.Quotient.mk _ p)
  rw [Ideal.Quotient.eq] at h
  have h2 := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_dvd_of_mem ℓ n k h (n - 1) (by omega)
  rwa [map_sub] at h2

def topMap (ℓ : O) (n k : ℕ) (hn : 0 < n) :
    (PowerSeries O ⧸ J ℓ n k) →ₗ[O] O ⧸ Ideal.span {ℓ ^ k} where
  toFun := topFun ℓ n k
  map_add' a b := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_add, topFun_mk ℓ n k hn, topFun_mk ℓ n k hn, topFun_mk ℓ n k hn, map_add, map_add]
  map_smul' c a := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
      topFun_mk ℓ n k hn, topFun_mk ℓ n k hn, PowerSeries.algebraMap_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, coeff_C_mul]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos n with hn | hn` into its components or cases. Substitute `hn` using the available equality. Establish `h1 : (X : PowerSeries O) ^ 0 ∈ J ℓ 0 k` using `Ideal.subset_span (Set.mem_insert _ _)`. Rewrite `h1` using `[pow_zero]`. Establish `hs : Subsingleton (PowerSeries O ⧸ J ℓ 0 k)` using `Ideal.Quotient.subsingleton_iff.mpr ((Ideal.eq_top_iff_one _).mpr h1)`.

Rewrite using `[Module.length_eq_zero]`. Conclude with `zero_le`. Establish `hinj : Function.Injective ((topMap ℓ n k hn).comp (LinearMap.ker (LinearMap.mulLeft O (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))).subtype)`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce and unpack `⟨b, hb⟩ hT`.

Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective b`. Establish `hb'` using `hb`. Rewrite `hb'` using `[LinearMap.mem_ker, LinearMap.mulLeft_apply, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Rewrite `hT` using `[LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply]`. Establish `hT' : topFun ℓ n k (Ideal.Quotient.mk _ p) = 0` using `hT`.

Rewrite `hT'` using `[Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.topFun_mk ℓ n k hn, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Establish `hpJ` using `Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.mem_of_coeff_dvd ℓ n k p (Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.all_coeff_dvd ℓ n k p hb' hT')`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr hpJ`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem single (ℓ : O) (n k : ℕ) [IsDomain O] (hℓ : ℓ ≠ 0) :
    Module.length O (LinearMap.ker (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : (X : PowerSeries O) ^ 0 ∈ J ℓ 0 k := Ideal.subset_span (Set.mem_insert _ _)
    rw [pow_zero] at h1
    have hs : Subsingleton (PowerSeries O ⧸ J ℓ 0 k) :=
      Ideal.Quotient.subsingleton_iff.mpr ((Ideal.eq_top_iff_one _).mpr h1)
    rw [Module.length_eq_zero]
    exact zero_le
  ·
    have hinj : Function.Injective ((topMap ℓ n k hn).comp (LinearMap.ker (LinearMap.mulLeft O
        (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))).subtype) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨b, hb⟩ hT
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hb' := hb
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hb'
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply] at hT
      have hT' : topFun ℓ n k (Ideal.Quotient.mk _ p) = 0 := hT
      rw [Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.topFun_mk ℓ n k hn, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton] at hT'
      have hpJ := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.mem_of_coeff_dvd ℓ n k p
        (Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.all_coeff_dvd ℓ n k p hb' hT')
      apply Subtype.ext
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hpJ
    calc _ ≤ Module.length O (O ⧸ Ideal.span {ℓ ^ k}) := Module.length_le_of_injective _ hinj
      _ = _ := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow ℓ hℓ k

/- English proof (translation)
Set `Φ : LinearMap.ker (LinearMap.pi fun i => (f i).comp (LinearMap.proj (R` to `R) (φ := M) i)) →ₗ[R] (∀ i, LinearMap.ker (f i)) := LinearMap.pi fun i => LinearMap.codRestrict (LinearMap.ker (f i)) ((LinearMap.proj (R := R) (φ := M) i).comp (Submodule.subtype _)) (fun x => by`. Establish `hx` using `x.2`. Rewrite `hx`, the goal using `[LinearMap.mem_ker]`. Establish `h2` using `congrFun hx i`. Simplify using `using h2)`.

Establish `hΦ : Function.Injective Φ`. Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Establish `h2` using `congrArg (fun z => (z i : M i)) hxy`.

Simplify `h2` using `[Φ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ker_pi_le {ι : Type} [Fintype ι] {R : Type} [CommRing R] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (f : ∀ i, M i →ₗ[R] M i) :
    Module.length R (LinearMap.ker (LinearMap.pi fun i => (f i).comp (LinearMap.proj (R := R)
      (φ := M) i))) ≤ ∑ i, Module.length R (LinearMap.ker (f i)) := by
  let Φ : LinearMap.ker (LinearMap.pi fun i => (f i).comp (LinearMap.proj (R := R) (φ := M) i)) →ₗ[R]
      (∀ i, LinearMap.ker (f i)) :=
    LinearMap.pi fun i => LinearMap.codRestrict (LinearMap.ker (f i))
      ((LinearMap.proj (R := R) (φ := M) i).comp (Submodule.subtype _)) (fun x => by
        have hx := x.2
        rw [LinearMap.mem_ker] at hx ⊢
        have h2 := congrFun hx i
        simpa using h2)
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have h2 := congrArg (fun z => (z i : M i)) hxy
    simpa [Φ] using h2
  calc _ ≤ Module.length R (∀ i, LinearMap.ker (f i)) := Module.length_le_of_injective Φ hΦ
    _ = _ := Module.length_pi_of_fintype R _

end Formalism.KernelCokernelLengths.TorsionKernelSumLemmas

open Formalism.KernelCokernelLengths.TorsionKernelSumLemmas in
/- English proof (translation)
Unfold `Formalism.KernelCokernelLengths.TorsKerSum`. Introduce `O _ _ _ ℓ hℓ m k n`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem Formalism.KernelCokernelLengths.torsion_kernel_sum_length : Formalism.KernelCokernelLengths.TorsKerSum := by
  unfold Formalism.KernelCokernelLengths.TorsKerSum
  intro O _ _ _ ℓ hℓ m k n
  calc _ ≤ ∑ j : Fin m, Module.length O (LinearMap.ker (LinearMap.mulLeft O
        (Ideal.Quotient.mk (J ℓ (n j) k) ((PowerSeries.X : PowerSeries O) - PowerSeries.C ℓ)))) :=
        Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.ker_pi_le _ _
    _ ≤ ∑ _j : Fin m, (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) :=
        Finset.sum_le_sum fun j _ => Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.single ℓ (n j) k hℓ
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
