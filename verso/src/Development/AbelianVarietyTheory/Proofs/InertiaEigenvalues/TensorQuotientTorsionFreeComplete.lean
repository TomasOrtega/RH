import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

noncomputable section

namespace GlobalTheory.XiQuotient

section Algebra

variable {R : Type} [CommRing R] (π : R)

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Simplify using the standard rewrite rules.
-/
theorem smodEq_iff {M : Type} [AddCommGroup M] [Module R M] (n : ℕ) (x y : M) :
    x ≡ y [SMOD (Ideal.span {π} ^ n • ⊤ : Submodule R M)] ↔ ∃ z : M, π ^ n • z = x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨fun x hx => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Use `h.toIsHausdorff.haus x fun n => ?_` and prove the remaining obligations. Rewrite using `[smodEq_iff, sub_zero]`.

Conclude with `hx n`. Establish `hc : ∀ {m n : ℕ}, m ≤ n → u m ≡ u n [SMOD (Ideal.span {π} ^ m • ⊤ : Submodule R M)]`. Introduce `m n hmn`. Rewrite using `[smodEq_iff]`. Proceed by induction on `n, hmn using Nat.le_induction with`.

Consider the case `base => exact ⟨0, by simp⟩`. Consider the case `succ k hk ih`. Take `⟨z, hz⟩` from `ih`. Take `⟨w, hw⟩` from `hu k`. Use `⟨z + π ^ (k - m) • w, ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hk, hz, hw]`. Normalize the expressions using the abelian group laws. Take `⟨L, hL⟩` from `h.toIsPrecomplete.prec hc`. Conclude with `⟨L, fun n => (smodEq_iff π n _ _).1 (hL n)⟩`. Introduce and unpack `⟨h1, h2⟩ haveI : IsHausdorff (Ideal.span {π}) M := ⟨fun x hx => h1 x fun n => by`.

Simplify using `using (smodEq_iff π n _ _).1 (hx n)⟩`. Use `haveI : IsPrecomplete (Ideal.span {π}) M := ⟨fun u hu => by`. Take `⟨L, hL⟩` from `h2 u fun n => (smodEq_iff π n _ _).1 (hu (Nat.le_succ n))`. Conclude with `⟨L, fun n => (smodEq_iff π n _ _).2 (hL n)⟩⟩`. Conclude with `⟨⟩`.
-/
theorem isAdicComplete_iff {M : Type} [AddCommGroup M] [Module R M] :
    IsAdicComplete (Ideal.span {π}) M ↔
      (∀ x : M, (∀ n : ℕ, ∃ z : M, π ^ n • z = x) → x = 0) ∧
      ∀ u : ℕ → M, (∀ n : ℕ, ∃ z : M, π ^ n • z = u n - u (n + 1)) →
        ∃ L : M, ∀ n : ℕ, ∃ z : M, π ^ n • z = u n - L := by
  constructor
  · intro h
    refine ⟨fun x hx => ?_, fun u hu => ?_⟩
    · refine h.toIsHausdorff.haus x fun n => ?_
      rw [smodEq_iff, sub_zero]
      exact hx n
    · have hc : ∀ {m n : ℕ}, m ≤ n →
          u m ≡ u n [SMOD (Ideal.span {π} ^ m • ⊤ : Submodule R M)] := by
        intro m n hmn
        rw [smodEq_iff]
        induction n, hmn using Nat.le_induction with
        | base => exact ⟨0, by simp⟩
        | succ k hk ih =>
          obtain ⟨z, hz⟩ := ih
          obtain ⟨w, hw⟩ := hu k
          refine ⟨z + π ^ (k - m) • w, ?_⟩
          rw [smul_add, smul_smul, ← pow_add, Nat.add_sub_cancel' hk, hz, hw]
          abel
      obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec hc
      exact ⟨L, fun n => (smodEq_iff π n _ _).1 (hL n)⟩
  · rintro ⟨h1, h2⟩
    haveI : IsHausdorff (Ideal.span {π}) M := ⟨fun x hx => h1 x fun n => by
      simpa using (smodEq_iff π n _ _).1 (hx n)⟩
    haveI : IsPrecomplete (Ideal.span {π}) M := ⟨fun u hu => by
      obtain ⟨L, hL⟩ := h2 u fun n => (smodEq_iff π n _ _).1 (hu (Nat.le_succ n))
      exact ⟨L, fun n => (smodEq_iff π n _ _).2 (hL n)⟩⟩
    exact ⟨⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `(isAdicComplete_iff π).1 hA`. Establish `hstep : ∀ x y : A, π • x = f y → ∃ y', y = π • y' ∧ x = f y'`. Introduce `x y h`. Take `⟨y', rfl⟩` from `hreg x y h`. Use `⟨y', rfl, sub_eq_zero.1 (hπ _ ?_)⟩` and prove the remaining obligations.

Rewrite using `[smul_sub, h, map_smul, sub_self]`. Establish `hpow : ∀ (n : ℕ) (x y : A), π ^ n • x = f y → ∃ y', π ^ n • y' = y`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x y _; exact ⟨y, by simp⟩`.

Consider the case `succ n ih`. Introduce `x y h`. Rewrite `h` using `[pow_succ', mul_smul]`. Take `⟨y', rfl, h'⟩` from `hstep _ _ h`. Take `⟨y'', rfl⟩` from `ih _ _ h'`.

Conclude with `⟨y'', by rw [pow_succ', mul_smul]⟩`. Use `⟨fun q hq => ?_, (isAdicComplete_iff π).2 ⟨fun q hq => ?_, fun u hu => ?_⟩⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `hg q`. Rewrite `hq` using `[← map_smul, hfg]`. Take `⟨y, hy⟩` from `hq`.

Take `⟨y', -, h⟩` from `hstep _ _ hy.symm`. Conclude with `(hfg x).2 ⟨y', h.symm⟩`. Take `⟨x, rfl⟩` from `hg q`. Establish `: ∀ n : ℕ, ∃ y z : A, f y = x - π ^ n • z`. Introduce `n`.

Take `⟨w, hw⟩` from `hq n`. Take `⟨z, rfl⟩` from `hg w`. Take `⟨y, hy⟩` from `(hfg (x - π ^ n • z)).1 (by rw [map_sub, map_smul, hw, sub_self])`. Conclude with `⟨y, z, hy⟩`. Use `choose y z hyz using this`.

Take `⟨L, hL⟩` from `h2 y fun n => hpow n (π • z (n + 1) - z n) _ (by`. Rewrite using `[map_sub, hyz, hyz, smul_sub, smul_smul, ← pow_succ]`. Use the proof step `abel)`. Use `(hfg x).2 ⟨L, (sub_eq_zero.1 (h1 _ fun n => ?_)).symm⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hL n`.

Use `⟨z n + f w, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, ← map_smul, hw, map_sub, hyz]`. Normalize the expressions using the abelian group laws. Use `choose z hz using hu choose z' hz' using fun n => hg (z n)`. Take `⟨x₀, hx₀⟩` from `hg (u 0)`.

Set `x : ℕ → A` to `fun n => x₀ - ∑ i ∈ Finset.range n, π ^ i • z' i`. Establish `hx : ∀ n, g (x n) = u n`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [x, hx₀]`.

Consider the case `succ n ih`. Establish `: x (n + 1) = x n - π ^ n • z' n`. Simplify using `only [x, Finset.sum_range_succ]`. Normalize the expressions using the abelian group laws. Rewrite using `[this, map_sub, ih, map_smul, hz', hz]`.

Normalize the expressions using the abelian group laws. Take `⟨L, hL⟩` from `h2 x fun n => ⟨z' n, by simp only [x, Finset.sum_range_succ]; abel⟩`. Use `⟨g L, fun n => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `hL n`. Conclude with `⟨g w, by rw [← map_smul, hw, map_sub, hx]⟩`.
-/
theorem isAdicComplete_coker {A Q : Type} [AddCommGroup A] [Module R A] [AddCommGroup Q]
    [Module R Q] (hA : IsAdicComplete (Ideal.span {π}) A) (hπ : ∀ x : A, π • x = 0 → x = 0)
    (f : A →ₗ[R] A) (g : A →ₗ[R] Q) (hg : Function.Surjective g)
    (hfg : ∀ x, g x = 0 ↔ ∃ y, f y = x)
    (hreg : ∀ x y : A, π • x = f y → ∃ y', y = π • y') :
    (∀ q : Q, π • q = 0 → q = 0) ∧ IsAdicComplete (Ideal.span {π}) Q := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_iff π).1 hA
  have hstep : ∀ x y : A, π • x = f y → ∃ y', y = π • y' ∧ x = f y' := by
    intro x y h
    obtain ⟨y', rfl⟩ := hreg x y h
    refine ⟨y', rfl, sub_eq_zero.1 (hπ _ ?_)⟩
    rw [smul_sub, h, map_smul, sub_self]
  have hpow : ∀ (n : ℕ) (x y : A), π ^ n • x = f y → ∃ y', π ^ n • y' = y := by
    intro n
    induction n with
    | zero => intro x y _; exact ⟨y, by simp⟩
    | succ n ih =>
      intro x y h
      rw [pow_succ', mul_smul] at h
      obtain ⟨y', rfl, h'⟩ := hstep _ _ h
      obtain ⟨y'', rfl⟩ := ih _ _ h'
      exact ⟨y'', by rw [pow_succ', mul_smul]⟩
  refine ⟨fun q hq => ?_, (isAdicComplete_iff π).2 ⟨fun q hq => ?_, fun u hu => ?_⟩⟩
  · obtain ⟨x, rfl⟩ := hg q
    rw [← map_smul, hfg] at hq
    obtain ⟨y, hy⟩ := hq
    obtain ⟨y', -, h⟩ := hstep _ _ hy.symm
    exact (hfg x).2 ⟨y', h.symm⟩
  · obtain ⟨x, rfl⟩ := hg q
    have : ∀ n : ℕ, ∃ y z : A, f y = x - π ^ n • z := by
      intro n
      obtain ⟨w, hw⟩ := hq n
      obtain ⟨z, rfl⟩ := hg w
      obtain ⟨y, hy⟩ := (hfg (x - π ^ n • z)).1 (by rw [map_sub, map_smul, hw, sub_self])
      exact ⟨y, z, hy⟩
    choose y z hyz using this
    obtain ⟨L, hL⟩ := h2 y fun n => hpow n (π • z (n + 1) - z n) _ (by
      rw [map_sub, hyz, hyz, smul_sub, smul_smul, ← pow_succ]; abel)
    refine (hfg x).2 ⟨L, (sub_eq_zero.1 (h1 _ fun n => ?_)).symm⟩
    obtain ⟨w, hw⟩ := hL n
    refine ⟨z n + f w, ?_⟩
    rw [smul_add, ← map_smul, hw, map_sub, hyz]
    abel
  · choose z hz using hu
    choose z' hz' using fun n => hg (z n)
    obtain ⟨x₀, hx₀⟩ := hg (u 0)
    let x : ℕ → A := fun n => x₀ - ∑ i ∈ Finset.range n, π ^ i • z' i
    have hx : ∀ n, g (x n) = u n := by
      intro n
      induction n with
      | zero => simp [x, hx₀]
      | succ n ih =>
        have : x (n + 1) = x n - π ^ n • z' n := by
          simp only [x, Finset.sum_range_succ]; abel
        rw [this, map_sub, ih, map_smul, hz', hz]
        abel
    obtain ⟨L, hL⟩ := h2 x fun n => ⟨z' n, by simp only [x, Finset.sum_range_succ]; abel⟩
    refine ⟨g L, fun n => ?_⟩
    obtain ⟨w, hw⟩ := hL n
    exact ⟨g w, by rw [← map_smul, hw, map_sub, hx]⟩

/- English proof (translation)
Take `⟨h1, h2⟩` from `(isAdicComplete_iff π).1 hQ`. Use `(isAdicComplete_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use function extensionality and compare the values at `i`.

Use `h1 _ fun n => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `hx n`. Conclude with `⟨e z i, by rw [← hz, map_smul]; rfl⟩`. Establish `: ∀ i, ∃ L : Q, ∀ n : ℕ, ∃ z : Q, π ^ n • z = e (u n) i - L`. Introduce `i`.

Use `h2 (fun n => e (u n) i) fun n => ?_` and prove the remaining obligations. Take `⟨z, hz⟩` from `hu n`. Use `⟨e z i, ?_⟩` and prove the remaining obligations. Use `congrFun (congrArg e hz) i` as an intermediate fact. Rewrite `this` using `[map_smul, map_sub]`.

Conclude with `this`. Use `choose L z hz using this`. Use `⟨e.symm L, fun n => ⟨e.symm (fun i => z i n), ?_⟩⟩` and prove the remaining obligations. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_smul, map_sub, e.apply_symm_apply, e.apply_symm_apply]`.

Use function extensionality and compare the values at `i`. Conclude with `hz i n`.
-/
theorem isAdicComplete_of_equiv_pi {ι Q M : Type} [AddCommGroup Q] [Module R Q] [AddCommGroup M]
    [Module R M] (hQ : IsAdicComplete (Ideal.span {π}) Q) (e : M ≃ₗ[R] (ι → Q)) :
    IsAdicComplete (Ideal.span {π}) M := by
  obtain ⟨h1, h2⟩ := (isAdicComplete_iff π).1 hQ
  refine (isAdicComplete_iff π).2 ⟨fun x hx => ?_, fun u hu => ?_⟩
  · apply e.injective
    rw [map_zero]
    funext i
    refine h1 _ fun n => ?_
    obtain ⟨z, hz⟩ := hx n
    exact ⟨e z i, by rw [← hz, map_smul]; rfl⟩
  · have : ∀ i, ∃ L : Q, ∀ n : ℕ, ∃ z : Q, π ^ n • z = e (u n) i - L := by
      intro i
      refine h2 (fun n => e (u n) i) fun n => ?_
      obtain ⟨z, hz⟩ := hu n
      refine ⟨e z i, ?_⟩
      have := congrFun (congrArg e hz) i
      rw [map_smul, map_sub] at this
      exact this
    choose L z hz using this
    refine ⟨e.symm L, fun n => ⟨e.symm (fun i => z i n), ?_⟩⟩
    apply e.injective
    rw [map_smul, map_sub, e.apply_symm_apply, e.apply_symm_apply]
    funext i
    exact hz i n

end Algebra

/- English proof (translation)
Establish `hpow : ∀ (n : ℕ) (x : M), (l : ℤ_[l]) ^ n • x = 0 → x = 0`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro x hx`. Simplify using `using hx`.

Consider the case `succ n ih`. Introduce `x hx`. Rewrite `hx` using `[pow_succ, mul_smul]`. Conclude with `h x (ih _ hx)`. Use `⟨fun {c x} hcx => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hc : c = 0`. Conclude with `Or.inl hc`. Use `right`. Rewrite `hcx` using `[PadicInt.unitCoeff_spec hc, mul_comm, mul_smul]`. Use `hpow _ _ hcx` as an intermediate fact.

Rewrite `this` using `[← Units.smul_def, smul_eq_zero_iff_eq]`. Then use the resulting hypothesis.
-/
theorem noZeroSMulDivisors_of_prime {l : ℕ} [Fact l.Prime] {M : Type} [AddCommGroup M]
    [Module ℤ_[l] M] (h : ∀ x : M, (l : ℤ_[l]) • x = 0 → x = 0) : NoZeroSMulDivisors ℤ_[l] M := by
  have hpow : ∀ (n : ℕ) (x : M), (l : ℤ_[l]) ^ n • x = 0 → x = 0 := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      rw [pow_succ, mul_smul] at hx
      exact h x (ih _ hx)
  refine ⟨fun {c x} hcx => ?_⟩
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    rw [PadicInt.unitCoeff_spec hc, mul_comm, mul_smul] at hcx
    have := hpow _ _ hcx
    rwa [← Units.smul_def, smul_eq_zero_iff_eq] at this

section Ainf

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_natCast]`.
-/
theorem smul_l (x : Ainf l) : (l : ℤ_[l]) • x = (l : Ainf l) * x := by
  rw [Algebra.smul_def, map_natCast]

/- English proof (translation)
Establish `h : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l)` using `inferInstance`. Rewrite using `[← IsAdicComplete.map_algebraMap_iff (S := Ainf l), Ideal.map_span, Set.image_singleton, map_natCast]`. Conclude with `h`.
-/
theorem ainf_complete : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) (Ainf l) := by
  have h : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l) := inferInstance
  rw [← IsAdicComplete.map_algebraMap_iff (S := Ainf l), Ideal.map_span, Set.image_singleton,
    map_natCast]
  exact h

/- English proof (translation)
The claim follows from `WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))`.
-/
theorem inclW_injective : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

variable {P : LocPrime l} (AI : LocAinf l P)

/- English proof (translation)
Introduce `h`. Establish `hu` using `AI.isUnit_inclW_ξ.map (WittVector.constantCoeff : WCb l →+* Cb l)`. Apply `hu.ne_zero` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(inclW l AI.ξ).coeff 0 = 0`. Rewrite using `[inclW, WittVector.map_coeff]`.

Express the relevant statement in the definitionally equal form `algebraMap (OCb l) (Cb l) (WittVector.constantCoeff AI.ξ) = 0`. Rewrite using `[h, map_zero]`.
-/
theorem xi_coeff_ne_zero : WittVector.constantCoeff AI.ξ ≠ 0 := by
  intro h
  have hu := AI.isUnit_inclW_ξ.map (WittVector.constantCoeff : WCb l →+* Cb l)
  apply hu.ne_zero
  change (inclW l AI.ξ).coeff 0 = 0
  rw [inclW, WittVector.map_coeff]
  change algebraMap (OCb l) (Cb l) (WittVector.constantCoeff AI.ξ) = 0
  rw [h, map_zero]

/- English proof (translation)
Rewrite `h` using `[smul_l]`. Establish `h0` using `congrArg (WittVector.constantCoeff : Ainf l →+* OCb l) h`. Rewrite `h0` using `[map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_pow]`. Establish `hy : y.coeff 0 = 0` using `(mul_eq_zero.1 h0.symm).resolve_left (pow_ne_zero k (xi_coeff_ne_zero AI))`. Rewrite `hy` using `[← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton']`.

Take `⟨y', rfl⟩` from `hy`. Conclude with `⟨y', by rw [smul_l, mul_comm]⟩`.
-/
theorem xi_pow_regular (k : ℕ) (x y : Ainf l) (h : (l : ℤ_[l]) • x = AI.ξ ^ k * y) :
    ∃ y', y = (l : ℤ_[l]) • y' := by
  rw [smul_l] at h
  have h0 := congrArg (WittVector.constantCoeff : Ainf l →+* OCb l) h
  rw [map_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul, map_pow] at h0
  have hy : y.coeff 0 = 0 :=
    (mul_eq_zero.1 h0.symm).resolve_left (pow_ne_zero k (xi_coeff_ne_zero AI))
  rw [← WittVector.mem_span_p_iff_coeff_zero_eq_zero, Ideal.mem_span_singleton'] at hy
  obtain ⟨y', rfl⟩ := hy
  exact ⟨y', by rw [smul_l, mul_comm]⟩

def toMxi (a : ℤ) : Ainf l →ₗ[ℤ_[l]] Mxi (AinfSub l) (xiU AI) a :=
  LinearMap.codRestrict _
    ((LinearMap.mulLeft ℤ_[l] ((xiU AI ^ a : (WCb l)ˣ) : WCb l)) ∘ₗ (inclWA l).toLinearMap)
    fun x => ⟨inclWA l x, ⟨x, rfl⟩, rfl⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toMxi_val (a : ℤ) (x : Ainf l) :
    (toMxi AI a x : WCb l) = ((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l x := rfl

/- English proof (translation)
Introduce and unpack `⟨_, _, ⟨x, rfl⟩, rfl⟩`. Conclude with `⟨x, rfl⟩`.
-/
theorem toMxi_surjective (a : ℤ) : Function.Surjective (toMxi AI a) := by
  rintro ⟨_, _, ⟨x, rfl⟩, rfl⟩
  exact ⟨x, rfl⟩

/- English proof (translation)
Take `⟨k, rfl⟩` from `Int.exists_add_of_le hab`. Establish `hk : ∀ y : Ainf l, ((xiU AI ^ (a + k) : (WCb l)ˣ) : WCb l) * inclW l y = ((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l (AI.ξ ^ k * y)`. Introduce `y`. Rewrite using `[zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_assoc]`. Both sides reduce to the same expression.

Use `isAdicComplete_coker (l : ℤ_[l]) ainf_complete ?_ (LinearMap.mulLeft ℤ_[l] (AI.ξ ^ k)) ((Submodule.mkQ _) ∘ₗ toMxi AI a) ((Submodule.mkQ_surjective _).comp (toMxi_surjective AI a)) ?_ (xi_pow_regular AI k)` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[smul_l, mul_comm]`. Conclude with `WittVector.eq_zero_of_p_mul_eq_zero x hx`. Introduce `x`.

Rewrite using `[LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply, toMxi_val]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, rfl⟩, hy⟩`. Use `⟨y, inclW_injective ?_⟩` and prove the remaining obligations. Establish `hy' : ((xiU AI ^ (a + k) : (WCb l)ˣ) : WCb l) * inclW l y = ((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l x` using `hy`.

Rewrite `hy'` using `[hk]`. Conclude with `(Units.mul_right_inj _).1 hy'`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨inclW l y, ⟨y, rfl⟩, hk y⟩`.
-/
theorem quotient_complete (a b : ℤ) (hab : a ≤ b) :
    (∀ q : Qab (AinfSub l) (xiU AI) a b, (l : ℤ_[l]) • q = 0 → q = 0) ∧
      IsAdicComplete (Ideal.span {(l : ℤ_[l])}) (Qab (AinfSub l) (xiU AI) a b) := by
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hab
  have hk : ∀ y : Ainf l, ((xiU AI ^ (a + k) : (WCb l)ˣ) : WCb l) * inclW l y =
      ((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l (AI.ξ ^ k * y) := by
    intro y
    rw [zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow, mul_assoc]
    rfl
  refine isAdicComplete_coker (l : ℤ_[l]) ainf_complete ?_ (LinearMap.mulLeft ℤ_[l] (AI.ξ ^ k))
    ((Submodule.mkQ _) ∘ₗ toMxi AI a)
    ((Submodule.mkQ_surjective _).comp (toMxi_surjective AI a)) ?_ (xi_pow_regular AI k)
  · intro x hx
    rw [smul_l, mul_comm] at hx
    exact WittVector.eq_zero_of_p_mul_eq_zero x hx
  · intro x
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply, toMxi_val]
    constructor
    · rintro ⟨_, ⟨y, rfl⟩, hy⟩
      refine ⟨y, inclW_injective ?_⟩
      have hy' : ((xiU AI ^ (a + k) : (WCb l)ˣ) : WCb l) * inclW l y =
          ((xiU AI ^ a : (WCb l)ˣ) : WCb l) * inclW l x := hy
      rw [hk] at hy'
      exact (Units.mul_right_inj _).1 hy'
    · rintro ⟨y, rfl⟩
      exact ⟨inclW l y, ⟨y, rfl⟩, hk y⟩

end Ainf

/- English proof (translation)
Introduce `l _ P AI a b hab T _ _ _ _`. Take `⟨h1, h2⟩` from `quotient_complete AI a b hab`. Set `β` to `Module.Free.chooseBasis ℤ_[l] T`. Set `e : TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b) ≃ₗ[ℤ_[l]] (Module.Free.ChooseBasisIndex ℤ_[l] T → Qab (AinfSub l) (xiU AI) a b)` to `(TensorProduct.comm ℤ_[l] _ _).trans ((TensorProduct.congr (LinearEquiv.refl ℤ_[l] _) β.equivFun).trans (TensorProduct.piScalarRight ℤ_[l] ℤ_[l] _ _))`. Use `⟨noZeroSMulDivisors_of_prime fun x hx => ?_, isAdicComplete_of_equiv_pi _ h2 e⟩` and prove the remaining obligations.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use function extensionality and compare the values at `i`. Apply `h1` to reduce the goal to its premises. Use `congrFun (congrArg e hx) i` as an intermediate fact.

Rewrite `this` using `[map_smul, map_zero]`. Conclude with `this`.
-/
theorem tensor_quotient_torsionFree_complete : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (AI : LocAinf l P) (a b : ℤ), a ≤ b → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T]
    [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T],
    NoZeroSMulDivisors ℤ_[l] (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) ∧
      IsAdicComplete (Ideal.span {(l : ℤ_[l])})
        (TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b)) := by
  intro l _ P AI a b hab T _ _ _ _
  classical
  obtain ⟨h1, h2⟩ := quotient_complete AI a b hab
  let β := Module.Free.chooseBasis ℤ_[l] T
  let e : TensorProduct ℤ_[l] T (Qab (AinfSub l) (xiU AI) a b) ≃ₗ[ℤ_[l]]
      (Module.Free.ChooseBasisIndex ℤ_[l] T → Qab (AinfSub l) (xiU AI) a b) :=
    (TensorProduct.comm ℤ_[l] _ _).trans
      ((TensorProduct.congr (LinearEquiv.refl ℤ_[l] _) β.equivFun).trans
        (TensorProduct.piScalarRight ℤ_[l] ℤ_[l] _ _))
  refine ⟨noZeroSMulDivisors_of_prime fun x hx => ?_, isAdicComplete_of_equiv_pi _ h2 e⟩
  apply e.injective
  rw [map_zero]
  funext i
  apply h1
  have := congrFun (congrArg e hx) i
  rw [map_smul, map_zero] at this
  exact this

end GlobalTheory.XiQuotient
