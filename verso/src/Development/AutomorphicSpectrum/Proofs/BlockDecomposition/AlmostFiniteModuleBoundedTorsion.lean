import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.AlmostFinite

universe w

variable {R : Type} [CommRing R]

def BS (c : R) (M : Type w) [AddCommGroup M] [Module R M] : Prop :=
  ∃ k : ℕ, (∀ (x : M) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) ∧
    ∀ x : M, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0

/- English proof (translation)
Assemble the required witnesses or components as `⟨k, fun x _ _ => h x, fun x _ => h x⟩`.
-/
theorem BS.of_pow {c : R} {M : Type w} [AddCommGroup M] [Module R M] (k : ℕ)
    (h : ∀ x : M, c ^ k • x = 0) : BS c M :=
  ⟨k, fun x _ _ => h x, fun x _ => h x⟩

/- English proof (translation)
Take `⟨k₁, t₁, s₁⟩` from `h₁`. Take `⟨k₂, t₂, s₂⟩` from `h₂`. Establish `key : ∀ (y : M) (n : ℕ), c ^ n • y ∈ N → c ^ k₂ • y ∈ N`. Introduce `y n hy`. Establish `h0 : c ^ n • (N.mkQ y) = 0`.

Rewrite using `[← map_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero N).2 hy`. Establish `h1` using `t₂ _ _ h0`. Rewrite `h1` using `[← map_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero N).1 h1`.

Use `⟨k₁ + k₂, ?_, ?_⟩` and prove the remaining obligations. Introduce `x n hx`. Establish `hm : c ^ k₂ • x ∈ N` using `key x n (by rw [hx]; exact N.zero_mem)`. Establish `h0 : c ^ n • (⟨_, hm⟩ : N) = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Submodule.coe_smul, Submodule.coe_zero]`. Rewrite using `[smul_comm, hx, smul_zero]`. Establish `h1` using `congrArg Subtype.val (t₁ _ _ h0)`. Simplify using `only [Submodule.coe_smul, Submodule.coe_zero] at h1`. Rewrite using `[pow_add, mul_smul, h1]`.

Introduce `x hx`. Establish `hx2 : c ^ k₂ • x ∈ N`. Establish `h0 : c ^ k₂ • N.mkQ x = 0` using `s₂ _ (fun m => by`. Take `⟨y, hy⟩` from `hx m`. Conclude with `⟨N.mkQ y, by rw [hy, map_smul]⟩)`.

Rewrite `h0` using `[← map_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero N).1 h0`. Establish `hw : ∀ n : ℕ, ∃ w : N, x = c ^ n • (w : M)`. Introduce `n`. Take `⟨y, hy⟩` from `hx (n + k₂)`.

Establish `hy2 : c ^ k₂ • y ∈ N`. Use `key y (k₂ + (n + k₂)) ?_` and prove the remaining obligations. Rewrite using `[pow_add, mul_smul, ← hy]`. Conclude with `hx2`. Conclude with `⟨⟨_, hy2⟩, by rw [hy, pow_add, mul_smul]⟩`.

Take `⟨w₀, hw₀⟩` from `hw 0`. Establish `hxN : x ∈ N`. Rewrite using `[hw₀]`. Simplify using the standard rewrite rules. Establish `h1` using `congrArg Subtype.val (s₁ ⟨x, hxN⟩ (fun n => by`.

Take `⟨w, hw'⟩` from `hw n`. Conclude with `⟨w, Subtype.ext (by simpa using hw')⟩))`. Simplify using `only [Submodule.coe_smul, Submodule.coe_zero] at h1`. Rewrite using `[add_comm, pow_add, mul_smul, h1, smul_zero]`.
-/
theorem BS.ext {c : R} {M : Type w} [AddCommGroup M] [Module R M] (N : Submodule R M)
    (h₁ : BS c N) (h₂ : BS c (M ⧸ N)) : BS c M := by
  obtain ⟨k₁, t₁, s₁⟩ := h₁
  obtain ⟨k₂, t₂, s₂⟩ := h₂
  have key : ∀ (y : M) (n : ℕ), c ^ n • y ∈ N → c ^ k₂ • y ∈ N := by
    intro y n hy
    have h0 : c ^ n • (N.mkQ y) = 0 := by
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero N).2 hy
    have h1 := t₂ _ _ h0
    rw [← map_smul] at h1
    exact (Submodule.Quotient.mk_eq_zero N).1 h1
  refine ⟨k₁ + k₂, ?_, ?_⟩
  · intro x n hx
    have hm : c ^ k₂ • x ∈ N := key x n (by rw [hx]; exact N.zero_mem)
    have h0 : c ^ n • (⟨_, hm⟩ : N) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      rw [smul_comm, hx, smul_zero]
    have h1 := congrArg Subtype.val (t₁ _ _ h0)
    simp only [Submodule.coe_smul, Submodule.coe_zero] at h1
    rw [pow_add, mul_smul, h1]
  · intro x hx
    have hx2 : c ^ k₂ • x ∈ N := by
      have h0 : c ^ k₂ • N.mkQ x = 0 := s₂ _ (fun m => by
        obtain ⟨y, hy⟩ := hx m
        exact ⟨N.mkQ y, by rw [hy, map_smul]⟩)
      rw [← map_smul] at h0
      exact (Submodule.Quotient.mk_eq_zero N).1 h0
    have hw : ∀ n : ℕ, ∃ w : N, x = c ^ n • (w : M) := by
      intro n
      obtain ⟨y, hy⟩ := hx (n + k₂)
      have hy2 : c ^ k₂ • y ∈ N := by
        refine key y (k₂ + (n + k₂)) ?_
        rw [pow_add, mul_smul, ← hy]
        exact hx2
      exact ⟨⟨_, hy2⟩, by rw [hy, pow_add, mul_smul]⟩
    obtain ⟨w₀, hw₀⟩ := hw 0
    have hxN : x ∈ N := by
      rw [hw₀]; simp
    have h1 := congrArg Subtype.val (s₁ ⟨x, hxN⟩ (fun n => by
      obtain ⟨w, hw'⟩ := hw n
      exact ⟨w, Subtype.ext (by simpa using hw')⟩))
    simp only [Submodule.coe_smul, Submodule.coe_zero] at h1
    rw [add_comm, pow_add, mul_smul, h1, smul_zero]

/- English proof (translation)
Take `⟨k, t, s⟩` from `h`. Use `⟨k + a, ?_, ?_⟩` and prove the remaining obligations. Introduce `x n hx`. Establish `h0 : c ^ n • (⟨_, hN x⟩ : N) = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Simplify using `only [Submodule.coe_smul, Submodule.coe_zero]`. Rewrite using `[smul_comm, hx, smul_zero]`. Establish `h1` using `congrArg Subtype.val (t _ _ h0)`. Simplify using `only [Submodule.coe_smul, Submodule.coe_zero] at h1`. Rewrite using `[pow_add, mul_smul, h1]`.

Introduce `x hx`. Establish `h1` using `congrArg Subtype.val (s ⟨_, hN x⟩ (fun n => by`. Take `⟨y, hy⟩` from `hx n`. Use `⟨⟨_, hN y⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.coe_smul]`.

Rewrite using `[hy, smul_comm]))`. Simplify using `only [Submodule.coe_smul, Submodule.coe_zero] at h1`. Rewrite using `[pow_add, mul_smul, h1]`.
-/
theorem BS.of_submodule {c : R} {M : Type w} [AddCommGroup M] [Module R M] (N : Submodule R M)
    (a : ℕ) (hN : ∀ x : M, c ^ a • x ∈ N) (h : BS c N) : BS c M := by
  obtain ⟨k, t, s⟩ := h
  refine ⟨k + a, ?_, ?_⟩
  · intro x n hx
    have h0 : c ^ n • (⟨_, hN x⟩ : N) = 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      rw [smul_comm, hx, smul_zero]
    have h1 := congrArg Subtype.val (t _ _ h0)
    simp only [Submodule.coe_smul, Submodule.coe_zero] at h1
    rw [pow_add, mul_smul, h1]
  · intro x hx
    have h1 := congrArg Subtype.val (s ⟨_, hN x⟩ (fun n => by
      obtain ⟨y, hy⟩ := hx n
      refine ⟨⟨_, hN y⟩, Subtype.ext ?_⟩
      simp only [Submodule.coe_smul]
      rw [hy, smul_comm]))
    simp only [Submodule.coe_smul, Submodule.coe_zero] at h1
    rw [pow_add, mul_smul, h1]

section Base

variable {I : Ideal R} {c : R}

/- English proof (translation)
Distinguish the cases in `hJ : ∀ t : R, t • m = 0 → t ∈ I`. Use `⟨0, ?_, ?_⟩` and prove the remaining obligations. Introduce `x n hx`. Take `⟨r, rfl⟩` from `hm x`. Rewrite `hx` using `[smul_smul]`.

Break down `hI.mem_or_mem (hJ _ hx) with h | h` into its components or cases. Conclude with `absurd (hI.mem_of_pow_mem _ h) hc`. Simplify using `[hM r h m]`. Introduce `x hx`. Take `⟨r, rfl⟩` from `hm x`.

Establish `hr : r ∈ I`. Use `hs r (fun n => ?_)` and prove the remaining obligations. Take `⟨y, hy⟩` from `hx n`. Take `⟨s, rfl⟩` from `hm y`. Rewrite `hy` using `[smul_smul]`.

Establish `h0 : (r - c ^ n * s) ∈ I` using `hJ _ (by rw [sub_smul, hy, sub_self])`. Establish `h1 : r = c ^ n * s + (r - c ^ n * s)` using `by ring`. Rewrite using `[h1]`. Conclude with `Submodule.add_mem_sup (Ideal.mem_span_singleton'.2 ⟨s, mul_comm _ _⟩) h0`. Simplify using `[hM r hr m]`.

Use `push Not at hJ`. Take `⟨t, ht, htI⟩` from `hJ`. Take `⟨n, hn⟩` from `hv t htI`. Take `⟨a, ha, i, hi, hai⟩` from `Submodule.mem_sup.1 hn`. Take `⟨u, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`.

Use `BS.of_pow n (fun x => ?_)` and prove the remaining obligations. Take `⟨r, rfl⟩` from `hm x`. Rewrite using `[smul_comm, ← hai, add_smul, mul_smul, ht, smul_zero, hM i hi m, add_zero, smul_zero]`.
-/
theorem BS.cyclic (hI : I.IsPrime) (hc : c ∉ I)
    (hv : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    (hs : ∀ x : R, (∀ n : ℕ, x ∈ Ideal.span {c ^ n} ⊔ I) → x ∈ I)
    {M : Type w} [AddCommGroup M] [Module R M] (hM : ∀ i ∈ I, ∀ x : M, i • x = 0)
    (m : M) (hm : ∀ x : M, ∃ r : R, x = r • m) : BS c M := by
  by_cases hJ : ∀ t : R, t • m = 0 → t ∈ I
  · refine ⟨0, ?_, ?_⟩
    · intro x n hx
      obtain ⟨r, rfl⟩ := hm x
      rw [smul_smul] at hx
      rcases hI.mem_or_mem (hJ _ hx) with h | h
      · exact absurd (hI.mem_of_pow_mem _ h) hc
      · simp [hM r h m]
    · intro x hx
      obtain ⟨r, rfl⟩ := hm x
      have hr : r ∈ I := by
        refine hs r (fun n => ?_)
        obtain ⟨y, hy⟩ := hx n
        obtain ⟨s, rfl⟩ := hm y
        rw [smul_smul] at hy
        have h0 : (r - c ^ n * s) ∈ I := hJ _ (by rw [sub_smul, hy, sub_self])
        have h1 : r = c ^ n * s + (r - c ^ n * s) := by ring
        rw [h1]
        exact Submodule.add_mem_sup (Ideal.mem_span_singleton'.2 ⟨s, mul_comm _ _⟩) h0
      simp [hM r hr m]
  · push Not at hJ
    obtain ⟨t, ht, htI⟩ := hJ
    obtain ⟨n, hn⟩ := hv t htI
    obtain ⟨a, ha, i, hi, hai⟩ := Submodule.mem_sup.1 hn
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    refine BS.of_pow n (fun x => ?_)
    obtain ⟨r, rfl⟩ := hm x
    rw [smul_comm, ← hai, add_smul, mul_smul, ht, smul_zero, hM i hi m, add_zero, smul_zero]

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero`. Introduce `M _ _ _ g hg`. Use `BS.of_pow 0 (fun x => ?_)` and prove the remaining obligations. Establish `hx : x ∈ Submodule.span R (Set.range g)` using `by rw [hg]; trivial`.

Establish `: Set.range g = ∅` using `Set.range_eq_empty g`. Rewrite `hx` using `[this, Submodule.span_empty, Submodule.mem_bot]`. Simplify using `[hx]`. Consider the case `succ a ih`. Introduce `M _ _ hM g hg`.

Use `BS.ext (Submodule.span R {g 0}) ?_ ?_` and prove the remaining obligations. Use `BS.cyclic hI hc hv hs (fun i hi x => Subtype.ext (by simpa using hM i hi x)) ⟨g 0, Submodule.mem_span_singleton_self _⟩ (fun x => ?_)` and prove the remaining obligations. Take `⟨r, hr⟩` from `Submodule.mem_span_singleton.1 x.2`. Conclude with `⟨r, Subtype.ext (by simpa using hr.symm)⟩`. Use `ih _ (fun i hi x => ?_) (fun j => Submodule.mkQ _ (g j.succ)) ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective _ x`. Rewrite using `[← map_smul, hM i hi y, map_zero]`. Rewrite using `[eq_top_iff, ← Submodule.range_mkQ (Submodule.span R {g 0}), LinearMap.range_eq_map, ← hg, Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations.

Establish `: Submodule.mkQ (Submodule.span R {g 0}) (g 0) = 0`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self (g 0))`. Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`.
-/
theorem BS.of_gens (hI : I.IsPrime) (hc : c ∉ I)
    (hv : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    (hs : ∀ x : R, (∀ n : ℕ, x ∈ Ideal.span {c ^ n} ⊔ I) → x ∈ I) (a : ℕ) :
    ∀ (M : Type w) [AddCommGroup M] [Module R M], (∀ i ∈ I, ∀ x : M, i • x = 0) →
      ∀ g : Fin a → M, Submodule.span R (Set.range g) = ⊤ → BS c M := by
  induction a with
  | zero =>
    intro M _ _ _ g hg
    refine BS.of_pow 0 (fun x => ?_)
    have hx : x ∈ Submodule.span R (Set.range g) := by rw [hg]; trivial
    have : Set.range g = ∅ := Set.range_eq_empty g
    rw [this, Submodule.span_empty, Submodule.mem_bot] at hx
    simp [hx]
  | succ a ih =>
    intro M _ _ hM g hg
    refine BS.ext (Submodule.span R {g 0}) ?_ ?_
    · refine BS.cyclic hI hc hv hs (fun i hi x => Subtype.ext (by simpa using hM i hi x))
        ⟨g 0, Submodule.mem_span_singleton_self _⟩ (fun x => ?_)
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 x.2
      exact ⟨r, Subtype.ext (by simpa using hr.symm)⟩
    · refine ih _ (fun i hi x => ?_) (fun j => Submodule.mkQ _ (g j.succ)) ?_
      · obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
        rw [← map_smul, hM i hi y, map_zero]
      · rw [eq_top_iff, ← Submodule.range_mkQ (Submodule.span R {g 0}), LinearMap.range_eq_map,
          ← hg, Submodule.map_span, Submodule.span_le]
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · have : Submodule.mkQ (Submodule.span R {g 0}) (g 0) = 0 := by
            exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self (g 0))
          rw [this]
          exact Submodule.zero_mem _
        · exact Submodule.subset_span ⟨j, rfl⟩

/- English proof (translation)
Proceed by induction on `s with`. Consider the case `zero`. Introduce `M _ _ _ hM`. Use `BS.of_pow 0 (fun x => ?_)` and prove the remaining obligations. Simplify using `using hM 1 (by simp) x`.

Consider the case `succ s ih`. Introduce `M _ _ hfin hM`. Establish `hN : (I • (⊤ : Submodule R M)).FG` using `Submodule.FG.smul hfg Module.Finite.fg_top`. Use `BS.ext (I • (⊤ : Submodule R M)) ?_ ?_` and prove the remaining obligations. Use `ih _ (Module.Finite.iff_fg.2 hN) (fun r hr x => Subtype.ext ?_)` and prove the remaining obligations.

Take `⟨x, hx⟩` from `x`. Simplify using `only [Submodule.coe_smul, Submodule.coe_zero]`. Proceed by induction on `hx using Submodule.smul_induction_on' with`. Consider the case `smul i hi y _`. Rewrite using `[smul_smul]`.

Conclude with `hM _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hr hi) y`. Consider the case `add x _ y _ hx hy => rw [smul_add, hx, hy, add_zero]`. Take `⟨a, g, hg⟩` from `Module.Finite.exists_fin (R := R) (M := M ⧸ (I • (⊤ : Submodule R M)))`. Use `BS.of_gens hI hc hv hs a _ (fun i hi x => ?_) g hg` and prove the remaining obligations. Take `⟨y, rfl⟩` from `Submodule.mkQ_surjective _ x`.

Rewrite using `[← map_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul hi (Submodule.mem_top (x := y)))`.
-/
theorem BS.of_finite (hfg : I.FG) (hI : I.IsPrime) (hc : c ∉ I)
    (hv : ∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I)
    (hs : ∀ x : R, (∀ n : ℕ, x ∈ Ideal.span {c ^ n} ⊔ I) → x ∈ I) (s : ℕ) :
    ∀ (M : Type w) [AddCommGroup M] [Module R M], Module.Finite R M →
      (∀ r ∈ I ^ s, ∀ x : M, r • x = 0) → BS c M := by
  induction s with
  | zero =>
    intro M _ _ _ hM
    refine BS.of_pow 0 (fun x => ?_)
    simpa using hM 1 (by simp) x
  | succ s ih =>
    intro M _ _ hfin hM
    have hN : (I • (⊤ : Submodule R M)).FG := Submodule.FG.smul hfg Module.Finite.fg_top
    refine BS.ext (I • (⊤ : Submodule R M)) ?_ ?_
    · refine ih _ (Module.Finite.iff_fg.2 hN) (fun r hr x => Subtype.ext ?_)
      obtain ⟨x, hx⟩ := x
      simp only [Submodule.coe_smul, Submodule.coe_zero]
      induction hx using Submodule.smul_induction_on' with
      | smul i hi y _ =>
        rw [smul_smul]
        exact hM _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hr hi) y
      | add x _ y _ hx hy => rw [smul_add, hx, hy, add_zero]
    · obtain ⟨a, g, hg⟩ := Module.Finite.exists_fin (R := R) (M := M ⧸ (I • (⊤ : Submodule R M)))
      refine BS.of_gens hI hc hv hs a _ (fun i hi x => ?_) g hg
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero _).2
        (Submodule.smul_mem_smul hi (Submodule.mem_top (x := y)))

end Base

/- English proof (translation)
Take `⟨m, g, hg⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hfg`. Use `choose y hy using hx`. Establish `hr : ∀ n, ∃ r : Fin m → R, ∑ i, r i • g i = c ^ a • y n`. Introduce `n`. Use `hN (y n)` as an intermediate fact.

Rewrite `this` using `[← hg]`. Conclude with `(Submodule.mem_span_range_iff_exists_fun R).1 this`. Use `choose r hr using hr`. Set `S : Fin m → ℕ → R` to `fun i n => ∑ j ∈ Finset.range n, c ^ j * r j i`. Establish `hmod : ∀ (u v : R) (n : ℕ), u ≡ v [SMOD ((Ideal.span {c}) ^ n • ⊤ : Submodule R R)] ↔ ∃ t, u - v = c ^ n * t`.

Introduce `u v n`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht⟩; exact ⟨t, by rw [← ht, mul_comm]⟩`. Introduce and unpack `⟨t, ht⟩; exact ⟨t, by rw [ht, mul_comm]⟩`.

Establish `hlim : ∀ i, ∃ s : R, ∀ n, ∃ t, S i n - s = c ^ n * t`. Introduce `i`. Take `⟨L, hL⟩` from `hc.prec' (S i) (fun {p q} hpq => by`. Rewrite using `[hmod]`. Take `⟨d, rfl⟩` from `Nat.exists_eq_add_of_le hpq`.

Use `⟨- ∑ j ∈ Finset.range d, c ^ j * r (p + j) i, ?_⟩` and prove the remaining obligations. Simplify using `only [S]`. Rewrite using `[Finset.sum_range_add, mul_neg, Finset.mul_sum]`. Simplify using `only [pow_add, mul_assoc]`. Use the proof step `ring)`.

Conclude with `⟨L, fun n => (hmod _ _ _).1 (hL n)⟩`. Use `choose s t ht using hlim`. Establish `hpart : ∀ n, c ^ a • x n = c ^ a • x 0 + ∑ i, S i n • g i`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => simp [S]`. Consider the case `succ n ih`. Establish `h1 : c ^ a • x (n + 1) = c ^ a • x n + c ^ n • (c ^ a • y n)`. Rewrite using `[smul_comm (c ^ n), ← smul_add, ← hy n]`. Use `congr 1`.

Normalize the expressions using the abelian group laws. Rewrite using `[h1, ih, ← hr n, add_assoc, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Simplify using `only [S]`.

Rewrite using `[Finset.sum_range_succ, add_smul, mul_smul]`. Use `⟨c ^ a • x 0 + ∑ i, s i • g i, fun n => ⟨∑ i, (- t i n) • g i, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hpart n, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[← sub_smul, smul_smul, show s i - S i n = c ^ n * - t i n by`.

Rewrite using `[mul_neg, ← ht i n]`. Use the proof step `ring]`.
-/
theorem limit_of_cauchy {c : R} (hc : IsPrecomplete (Ideal.span {c}) R)
    {M : Type w} [AddCommGroup M] [Module R M] (N : Submodule R M) (hfg : N.FG) (a : ℕ)
    (hN : ∀ x : M, c ^ a • x ∈ N) (x : ℕ → M)
    (hx : ∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) :
    ∃ z : M, ∀ n, ∃ y, z - c ^ a • x n = c ^ n • y := by
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg
  choose y hy using hx
  have hr : ∀ n, ∃ r : Fin m → R, ∑ i, r i • g i = c ^ a • y n := by
    intro n
    have := hN (y n)
    rw [← hg] at this
    exact (Submodule.mem_span_range_iff_exists_fun R).1 this
  choose r hr using hr
  let S : Fin m → ℕ → R := fun i n => ∑ j ∈ Finset.range n, c ^ j * r j i
  have hmod : ∀ (u v : R) (n : ℕ),
      u ≡ v [SMOD ((Ideal.span {c}) ^ n • ⊤ : Submodule R R)] ↔ ∃ t, u - v = c ^ n * t := by
    intro u v n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨t, ht⟩; exact ⟨t, by rw [← ht, mul_comm]⟩
    · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht, mul_comm]⟩
  have hlim : ∀ i, ∃ s : R, ∀ n, ∃ t, S i n - s = c ^ n * t := by
    intro i
    obtain ⟨L, hL⟩ := hc.prec' (S i) (fun {p q} hpq => by
      rw [hmod]
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
      refine ⟨- ∑ j ∈ Finset.range d, c ^ j * r (p + j) i, ?_⟩
      simp only [S]
      rw [Finset.sum_range_add, mul_neg, Finset.mul_sum]
      simp only [pow_add, mul_assoc]
      ring)
    exact ⟨L, fun n => (hmod _ _ _).1 (hL n)⟩
  choose s t ht using hlim
  have hpart : ∀ n, c ^ a • x n = c ^ a • x 0 + ∑ i, S i n • g i := by
    intro n
    induction n with
    | zero => simp [S]
    | succ n ih =>
      have h1 : c ^ a • x (n + 1) = c ^ a • x n + c ^ n • (c ^ a • y n) := by
        rw [smul_comm (c ^ n), ← smul_add, ← hy n]
        congr 1
        abel
      rw [h1, ih, ← hr n, add_assoc, Finset.smul_sum, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [S]
      rw [Finset.sum_range_succ, add_smul, mul_smul]
  refine ⟨c ^ a • x 0 + ∑ i, s i • g i, fun n => ⟨∑ i, (- t i n) • g i, ?_⟩⟩
  rw [hpart n, add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← sub_smul, smul_smul, show s i - S i n = c ^ n * - t i n by
    rw [mul_neg, ← ht i n]; ring]

/- English proof (translation)
Introduce `R _ I c hfg hnil hprime _ hv hpre hsep M _ _ hM`. Take `⟨a, N, hN, hx⟩` from `hM`. Take `⟨s, hs⟩` from `hnil`. Establish `hBS : BS c M`. Distinguish the cases in `hc : c ∈ I`.

Use `BS.of_pow s (fun x => ?_)` and prove the remaining obligations. Establish `h0 : c ^ s ∈ I ^ s` using `Ideal.pow_mem_pow hc s`. Rewrite `h0` using `[hs]`. Establish `h1 : c ^ s = 0` using `h0`. Simplify using `[h1]`.

Use `BS.of_submodule N a hx ?_` and prove the remaining obligations. Use `BS.of_finite hfg hprime hc hv hsep s _ (Module.Finite.iff_fg.2 hN) (fun r hr y => ?_)` and prove the remaining obligations. Rewrite `hr` using `[hs]`. Establish `h1 : r = 0` using `hr`. Simplify using `[h1]`.

Take `⟨k, ht, hd⟩` from `hBS`. Use `⟨k + a, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x n h`. Rewrite using `[add_comm, pow_add, mul_smul, ht x n h, smul_zero]`. Introduce `x h`.

Rewrite using `[add_comm, pow_add, mul_smul, hd x h, smul_zero]`. Introduce `x h`. Take `⟨z, hz⟩` from `limit_of_cauchy hpre N hN a hx x h`. Use `⟨c ^ k • z, fun n => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `hz n`.

Use `⟨c ^ k • y, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_add, mul_smul, ← smul_sub, hy, smul_comm]`.
-/
theorem afg_separated_complete :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (c : R), I.FG → IsNilpotent I → I.IsPrime →
    (∀ x y : R, x ∈ Ideal.span {y} ⊔ I ∨ y ∈ Ideal.span {x} ⊔ I) → (∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I) →
    IsPrecomplete (Ideal.span {c}) R → (∀ x : R, (∀ n : ℕ, x ∈ Ideal.span {c ^ n} ⊔ I) → x ∈ I) →
    ∀ (M : Type 1) [AddCommGroup M] [Module R M], AFG c M → ∃ k : ℕ,
      (∀ (x : M) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0) ∧ (∀ x : M, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0) ∧
      ∀ x : ℕ → M, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : M, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y := by
  intro R _ I c hfg hnil hprime _ hv hpre hsep M _ _ hM
  obtain ⟨a, N, hN, hx⟩ := hM
  obtain ⟨s, hs⟩ := hnil
  have hBS : BS c M := by
    by_cases hc : c ∈ I
    · refine BS.of_pow s (fun x => ?_)
      have h0 : c ^ s ∈ I ^ s := Ideal.pow_mem_pow hc s
      rw [hs] at h0
      have h1 : c ^ s = 0 := h0
      simp [h1]
    · refine BS.of_submodule N a hx ?_
      refine BS.of_finite hfg hprime hc hv hsep s _ (Module.Finite.iff_fg.2 hN) (fun r hr y => ?_)
      rw [hs] at hr
      have h1 : r = 0 := hr
      simp [h1]
  obtain ⟨k, ht, hd⟩ := hBS
  refine ⟨k + a, ?_, ?_, ?_⟩
  · intro x n h
    rw [add_comm, pow_add, mul_smul, ht x n h, smul_zero]
  · intro x h
    rw [add_comm, pow_add, mul_smul, hd x h, smul_zero]
  · intro x h
    obtain ⟨z, hz⟩ := limit_of_cauchy hpre N hN a hx x h
    refine ⟨c ^ k • z, fun n => ?_⟩
    obtain ⟨y, hy⟩ := hz n
    refine ⟨c ^ k • y, ?_⟩
    rw [pow_add, mul_smul, ← smul_sub, hy, smul_comm]

end GlobalTheory.CompanionTheory.AlmostFinite
