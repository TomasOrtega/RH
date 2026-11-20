import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

namespace GlobalTheory.GamFilt

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro a _`. Simplify using `using h0 a`. Consider the case `succ k ih`.

Introduce `a ha`. Rewrite `ha` using `[pow_succ]`. Use `Submodule.mul_induction_on ha ?_ ?_` and prove the remaining obligations. Introduce `x hx y hy`. Establish `hfy : f y ∈ I`.

Use `I.add_mem (h0 y) hy` as an intermediate fact. Simplify using `using this`. Establish `e : f (x * y) - x * y = (f x - x) * f y + x * (f y - y)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul (ih x hx) hfy`. Rewrite using `[show k + 1 + 1 = k + 2 from rfl, pow_add]`.

Conclude with `Ideal.mul_mem_mul hx (h1 y hy)`. Introduce `x y hx hy`. Establish `e : f (x + y) - (x + y) = (f x - x) + (f y - y)`. Rewrite using `[map_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Ideal.add_mem _ hx hy`.
-/
theorem sub_mem_pow_succ {A : Type*} [CommRing A] (f : A →+* A) (I : Ideal A)
    (h0 : ∀ a, f a - a ∈ I) (h1 : ∀ a ∈ I, f a - a ∈ I ^ 2) :
    ∀ k : ℕ, ∀ a ∈ I ^ k, f a - a ∈ I ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro a _; simpa using h0 a
  | succ k ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      have hfy : f y ∈ I := by
        have := I.add_mem (h0 y) hy
        simpa using this
      have e : f (x * y) - x * y = (f x - x) * f y + x * (f y - y) := by
        rw [map_mul]; ring
      rw [e]
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (ih x hx) hfy
      · rw [show k + 1 + 1 = k + 2 from rfl, pow_add]
        exact Ideal.mul_mem_mul hx (h1 y hy)
    · intro x y hx hy
      have e : f (x + y) - (x + y) = (f x - x) + (f y - y) := by
        rw [map_add]; ring
      rw [e]
      exact Ideal.add_mem _ hx hy

/- English proof (translation)
Use `sub_mem_pow_succ f _ h0 ?_` and prove the remaining obligations. Introduce `y hy`. Take `⟨a, b, rfl⟩` from `Ideal.mem_span_pair.1 hy`. Establish `e : f (a * p + b * t) - (a * p + b * t) = (f a - a) * p + (f b - b) * t + f b * (f t - t)`. Rewrite using `[map_add, map_mul, map_mul, hp]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `hpm : p ∈ Ideal.span {p, t}` using `Ideal.subset_span (by simp)`. Establish `htm : t ∈ Ideal.span {p, t}` using `Ideal.subset_span (by simp)`. Use `Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) (Ideal.mul_mem_left _ _ ht)` and prove the remaining obligations.

Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul (h0 a) hpm`. Rewrite using `[pow_two]`. Conclude with `Ideal.mul_mem_mul (h0 b) htm`.
-/
theorem sub_mem_pow_succ_pair {A : Type*} [CommRing A] (f : A →+* A) (p t : A)
    (h0 : ∀ a, f a - a ∈ Ideal.span {p, t}) (hp : f p = p)
    (ht : f t - t ∈ Ideal.span {p, t} ^ 2) :
    ∀ k : ℕ, ∀ a ∈ Ideal.span {p, t} ^ k, f a - a ∈ Ideal.span {p, t} ^ (k + 1) := by
  refine sub_mem_pow_succ f _ h0 ?_
  intro y hy
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hy
  have e : f (a * p + b * t) - (a * p + b * t) =
      (f a - a) * p + (f b - b) * t + f b * (f t - t) := by
    rw [map_add, map_mul, map_mul, hp]; ring
  rw [e]
  have hpm : p ∈ Ideal.span {p, t} := Ideal.subset_span (by simp)
  have htm : t ∈ Ideal.span {p, t} := Ideal.subset_span (by simp)
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) (Ideal.mul_mem_left _ _ ht)
  · rw [pow_two]; exact Ideal.mul_mem_mul (h0 a) hpm
  · rw [pow_two]; exact Ideal.mul_mem_mul (h0 b) htm

/- English proof (translation)
Establish `h1 : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a)`. Rewrite using `[PowerSeries.X_dvd_iff]`. Simplify using the standard rewrite rules. Take `⟨b, hb⟩` from `h1`. Establish `ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b`.

Rewrite using `[← hb, PowerSeries.algebraMap_apply]`. Simplify using the standard rewrite rules. Rewrite using `[PowerSeries.X_dvd_iff, ha, map_add, AlgHom.commutes, map_mul]`. Simplify using `[hg]`.
-/
theorem X_dvd_sub {O : Type*} [CommRing O] (g : PowerSeries O →ₐ[O] PowerSeries O)
    (hg : PowerSeries.constantCoeff (g PowerSeries.X) = 0) (a : PowerSeries O) :
    PowerSeries.X ∣ g a - a := by
  have h1 : PowerSeries.X ∣ a - PowerSeries.C (PowerSeries.constantCoeff a) := by
    rw [PowerSeries.X_dvd_iff]; simp
  obtain ⟨b, hb⟩ := h1
  have ha : a = algebraMap O (PowerSeries O) (PowerSeries.constantCoeff a) + PowerSeries.X * b := by
    rw [← hb, PowerSeries.algebraMap_apply]; simp
  rw [PowerSeries.X_dvd_iff, ha, map_add, AlgHom.commutes, map_mul]
  simp [hg]

/- English proof (translation)
Establish `: PowerSeries.X ^ 2 ∣ F - PowerSeries.X - PowerSeries.X * (PowerSeries.C ((p : O) * c))`. Rewrite using `[PowerSeries.X_pow_dvd_iff]`. Introduce `m hm`. Use `interval_cases m`. Simplify using `[h0]`.

Rewrite using `[map_sub, map_sub, h1, PowerSeries.coeff_succ_X_mul]`. Simplify using the standard rewrite rules. Take `⟨h, hh⟩` from `this`. Use `⟨h, ?_⟩` and prove the remaining obligations. Rewrite `hh` using `[map_mul, map_natCast]`.

Take the linear combination `hh`.
-/
theorem exists_X_sub {O : Type*} [CommRing O] (F : PowerSeries O) (p : ℕ) (c : O)
    (h0 : PowerSeries.constantCoeff F = 0) (h1 : PowerSeries.coeff 1 F = 1 + p * c) :
    ∃ h : PowerSeries O, F - PowerSeries.X =
      PowerSeries.X * ((p : PowerSeries O) * PowerSeries.C c + PowerSeries.X * h) := by
  have : PowerSeries.X ^ 2 ∣ F - PowerSeries.X - PowerSeries.X * (PowerSeries.C ((p : O) * c)) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simp [h0]
    · rw [map_sub, map_sub, h1, PowerSeries.coeff_succ_X_mul]
      simp
  obtain ⟨h, hh⟩ := this
  refine ⟨h, ?_⟩
  rw [map_mul, map_natCast] at hh
  linear_combination hh

/- English proof (translation)
Establish `hpm : ((p : ℕ) : LetA O n) ∈ Ideal.span {((p : ℕ) : LetA O n), letπ}` using `Ideal.subset_span (by simp)`. Establish `htm : (letπ : LetA O n) ∈ Ideal.span {((p : ℕ) : LetA O n), letπ}` using `Ideal.subset_span (by simp)`. Use `sub_mem_pow_succ_pair (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom _ _ ?_ (map_natCast _ _) ?_` and prove the remaining obligations. Introduce `a choose b hb using fun i => X_dvd_sub g h0 (a i)`. Establish `e : (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom a - a = letπ * b` using `funext hb`.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ htm`. Take `⟨h, hh⟩` from `exists_X_sub _ p c h0 h1`. Establish `e : (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom letπ - letπ = letπ * (((p : ℕ) : LetA O n) * (fun _ => PowerSeries.C c) + letπ * (fun _ => h))`. Use function extensionality and compare the values at `fun _ => hh`.

Rewrite using `[e, pow_two]`. Conclude with `Ideal.mul_mem_mul htm (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpm) (Ideal.mul_mem_right _ _ htm))`.
-/
theorem letγ_sub_mem {O : Type} [CommRing O] {n : ℕ} (g : PowerSeries O →ₐ[O] PowerSeries O) (p : ℕ)
    (c : O) (h0 : PowerSeries.constantCoeff (g PowerSeries.X) = 0)
    (h1 : PowerSeries.coeff 1 (g PowerSeries.X) = 1 + p * c) :
    ∀ k : ℕ, ∀ a ∈ (Ideal.span {((p : ℕ) : LetA O n), letπ}) ^ k,
      letγ g a - a ∈ (Ideal.span {((p : ℕ) : LetA O n), letπ}) ^ (k + 1) := by
  have hpm : ((p : ℕ) : LetA O n) ∈ Ideal.span {((p : ℕ) : LetA O n), letπ} :=
    Ideal.subset_span (by simp)
  have htm : (letπ : LetA O n) ∈ Ideal.span {((p : ℕ) : LetA O n), letπ} :=
    Ideal.subset_span (by simp)
  refine sub_mem_pow_succ_pair (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom _ _ ?_ (map_natCast _ _) ?_
  · intro a
    choose b hb using fun i => X_dvd_sub g h0 (a i)
    have e : (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom a - a = letπ * b := funext hb
    rw [e]
    exact Ideal.mul_mem_right _ _ htm
  · obtain ⟨h, hh⟩ := exists_X_sub _ p c h0 h1
    have e : (letγ g : LetA O n →ₐ[O] LetA O n).toRingHom letπ - letπ =
        letπ * (((p : ℕ) : LetA O n) * (fun _ => PowerSeries.C c) + letπ * (fun _ => h)) :=
      funext fun _ => hh
    rw [e, pow_two]
    exact Ideal.mul_mem_mul htm (Ideal.add_mem _ (Ideal.mul_mem_right _ _ hpm)
      (Ideal.mul_mem_right _ _ htm))

/- English proof (translation)
Establish `hl : (l : ↥LL.1) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Use `set y : ↥LL.1 := (algebraMap ↥(OL LL) ↥LL.1 u - 1) / (l : ↥LL.1) with hy`. Establish `e : algebraMap ↥(OL LL) ↥LL.1 u - 1 = (l : ↥LL.1) * y`. Rewrite using `[hy]`. Clear the denominators using the available nonvanishing facts.

Rewrite `hu` using `[e, AddValuation.map_mul, P.v_l]`. Establish `h0 : 0 ≤ P.v LL y`. Establish `: (1 : WithTop ℚ) + 0 ≤ 1 + P.v LL y` using `by simpa using hu`. Conclude with `(WithTop.add_le_add_iff_left WithTop.one_ne_top).1 this`. Use `⟨⟨y, (P.v_O LL y).1 h0⟩, Subtype.ext ?_⟩` and prove the remaining obligations.

Establish `: (u : ↥LL.1) - 1 = (l : ↥LL.1) * y` using `e`. Use `push_cast`. Take the linear combination `this`.
-/
theorem exists_eq_one_add {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l) (u : ↥(OL LL))
    (hu : (1 : WithTop ℚ) ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 u - 1)) :
    ∃ c : ↥(OL LL), u = 1 + (l : ↥(OL LL)) * c := by
  have hl : (l : ↥LL.1) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  set y : ↥LL.1 := (algebraMap ↥(OL LL) ↥LL.1 u - 1) / (l : ↥LL.1) with hy
  have e : algebraMap ↥(OL LL) ↥LL.1 u - 1 = (l : ↥LL.1) * y := by
    rw [hy]; field_simp
  rw [e, AddValuation.map_mul, P.v_l] at hu
  have h0 : 0 ≤ P.v LL y := by
    have : (1 : WithTop ℚ) + 0 ≤ 1 + P.v LL y := by simpa using hu
    exact (WithTop.add_le_add_iff_left WithTop.one_ne_top).1 this
  refine ⟨⟨y, (P.v_O LL y).1 h0⟩, Subtype.ext ?_⟩
  have : (u : ↥LL.1) - 1 = (l : ↥LL.1) * y := e
  push_cast
  linear_combination this

/- English proof (translation)
Introduce `D HW l _ K s LL h W g hg`. Establish `h1` using `(W.GKs_def g).1 hg`. Rewrite `h1` using `[← W.χΓ_res g]`. Establish `hs : (1 : WithTop ℚ) ≤ (W.s : WithTop ℚ)` using `by exact_mod_cast W.s_pos`. Take `⟨c, hc⟩` from `exists_eq_one_add (D.loc l) LL _ (hs.trans h1)`.

Conclude with `letγ_sub_mem (W.γ₀ (W.resΓ g)) l c (W.γ₀_X _).1 ((W.γ₀_X _).2.trans hc)`.
-/
theorem gamma_sub_mem_pow_succ : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ g ∈ W.GKs, ∀ (k : ℕ), ∀ a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ k, W.γA (W.resΓ g) a - a ∈ (Ideal.span {((l : ℕ) : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))), letπ}) ^ (k + 1) := by
  intro D HW l _ K s LL h W g hg
  have h1 := (W.GKs_def g).1 hg
  rw [← W.χΓ_res g] at h1
  have hs : (1 : WithTop ℚ) ≤ (W.s : WithTop ℚ) := by exact_mod_cast W.s_pos
  obtain ⟨c, hc⟩ := exists_eq_one_add (D.loc l) LL _ (hs.trans h1)
  exact letγ_sub_mem (W.γ₀ (W.resΓ g)) l c (W.γ₀_X _).1 ((W.γ₀_X _).2.trans hc)

end GlobalTheory.GamFilt
