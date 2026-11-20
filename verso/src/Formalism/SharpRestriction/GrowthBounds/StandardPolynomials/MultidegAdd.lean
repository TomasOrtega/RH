import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestRawTail1Of
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

abbrev MonH (X : Loc) := ((X.TT × Bool) × Fin (X.m + 1)) →₀ ℕ

def ndM (X : Loc) (m : MonH X) : ℕ := degUS (hhLetters X.TT) 1 m

/- English proof (translation)
Simplify using `only [ndM, degUS]`. Apply the tactic sequence `exact Finsupp.sum_add_index' (h := fun (v : (X.TT × Bool) × Fin (X.m + 1)) (n : ℕ) => if ((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨ ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1) then n else 0) (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)`.
-/
theorem ndM_add (X : Loc) (a b : MonH X) : ndM X (a + b) = ndM X a + ndM X b := by
  simp only [ndM, degUS]
  exact Finsupp.sum_add_index'
    (h := fun (v : (X.TT × Bool) × Fin (X.m + 1)) (n : ℕ) => if ((hhLetters X.TT).vec v.1 = true ∧ 1 ≤ v.2.val) ∨
      ((hhLetters X.TT).vec v.1 = false ∧ v.2.val < 1) then n else 0)
    (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)

/- English proof (translation)
Simplify using `[multideg, Finset.sum_add_distrib]`.
-/
theorem multideg_add {ι : Type} {n : ℕ} (a b : ι × Fin n →₀ ℕ) (i : ι) :
    multideg (a + b) i = multideg a i + multideg b i := by
  simp [multideg, Finset.sum_add_distrib]

section Tail

variable (C0 Cde CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] (O : Type) [CommRing O] [IsDomain O] (w : O) (mm : ℝ) (n o : ℕ)

abbrev SSe (ε : ℕ) : Submodule O (RHH O X) :=
  SSg O C0 Cde CE1 CE2 X (mm + ((n - ε : ℕ) : ℝ) * ka1 X) (((X.c - (n - ε) : ℕ) : ℝ) * ka1 X) (o + ε)

def tailSub : Submodule O (RHH O X) where
  carrier := {P | ∃ τ : ℕ → RHH O X, (∀ ε ∈ Finset.Ico 1 n, τ ε ∈ SSe C0 Cde CE1 CE2 X O mm n o ε) ∧
    InWj w (P - ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • τ ε) n}
  add_mem' := by
    rintro P Q ⟨τ, h1, h2⟩ ⟨τ', k1, k2⟩
    refine ⟨fun ε => τ ε + τ' ε, fun ε hε => Submodule.add_mem _ (h1 ε hε) (k1 ε hε), ?_⟩
    have e : P + Q - ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • (τ ε + τ' ε) =
        (P - ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • τ ε) + (Q - ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • τ' ε) := by
      simp only [smul_add, Finset.sum_add_distrib]
      abel
    rw [e]
    exact (wjSub w n).add_mem h2 k2
  zero_mem' := ⟨fun _ => 0, fun _ _ => Submodule.zero_mem _, by
    simp only [smul_zero, Finset.sum_const_zero, sub_zero]; exact (wjSub w n).zero_mem⟩
  smul_mem' := by
    rintro a P ⟨τ, h1, h2⟩
    refine ⟨fun ε => a • τ ε, fun ε hε => Submodule.smul_mem _ _ (h1 ε hε), ?_⟩
    have e : a • P - ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • a • τ ε = a • (P - ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • τ ε) := by
      rw [smul_sub, Finset.smul_sum]
      congr 1
      exact Finset.sum_congr rfl fun ε _ => smul_comm _ _ _
    rw [e]
    exact (wjSub w n).smul_mem a h2

variable {C0 Cde CE1 CE2 X O w mm n o}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => 0, fun _ _ => Submodule.zero_mem _, by simp only [smul_zero, Finset.sum_const_zero, sub_zero] exact h⟩`.
-/
theorem tail_of_wj {P : RHH O X} (h : InWj w P n) : P ∈ tailSub C0 Cde CE1 CE2 X O w mm n o := ⟨fun _ => 0, fun _ _ => Submodule.zero_mem _, by
  simp only [smul_zero, Finset.sum_const_zero, sub_zero]
  exact h⟩

/- English proof (translation)
Use `⟨fun ε => if ε = e then τ else 0, fun ε hε => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h' : ε = e`. Substitute `h'` using the available equality. Simplify using `using h`. Simplify using `[h']`.

Establish `hs : ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • (if ε = e then τ else 0) = (w ^ e) • τ`. Rewrite using `[Finset.sum_eq_single e]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[hb]`.

Introduce `h'`. Conclude with `absurd he h'`. Use `show InWj w ((w ^ e) • τ - ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • (if ε = e then τ else 0)) n`. Rewrite using `[hs, sub_self]`. Conclude with `(wjSub w n).zero_mem`.
-/
theorem tail_of_ssg {e : ℕ} (he : e ∈ Finset.Ico 1 n) {τ : RHH O X} (h : τ ∈ SSe C0 Cde CE1 CE2 X O mm n o e) :
    (w ^ e) • τ ∈ tailSub C0 Cde CE1 CE2 X O w mm n o := by
  refine ⟨fun ε => if ε = e then τ else 0, fun ε hε => ?_, ?_⟩
  · by_cases h' : ε = e
    · subst h'
      simpa using h
    · simp [h']
  · have hs : ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • (if ε = e then τ else 0) = (w ^ e) • τ := by
      rw [Finset.sum_eq_single e]
      · simp
      · intro b _ hb
        simp [hb]
      · intro h'
        exact absurd he h'
    show InWj w ((w ^ e) • τ - ∑ ε ∈ Finset.Ico 1 n, (w ^ ε) • (if ε = e then τ else 0)) n
    rw [hs, sub_self]
    exact (wjSub w n).zero_mem

end Tail

section Liftable

variable (C0 Cde CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O]
  [Algebra (WF X.p X.n') O] (w : O) (mm : ℝ) (n o : ℕ)

abbrev lift1 : RHH O X →ₐ[KK O] RHH O X := liftSubst X.p X.n' O w 1 (hhLetters X.TT) 1

def liftSub : Submodule O (RHH O X) where
  carrier := {σ | ∃ raw : RHH O X, IsCleanAwayFromPlane X O w 1 o raw ∧ lift1 X O w raw - σ ∈ tailSub C0 Cde CE1 CE2 X O w mm n o}
  add_mem' := by
    rintro P Q ⟨r, h1, h2⟩ ⟨r', k1, k2⟩
    refine ⟨r + r', (cleanSub X O w 1 o).add_mem h1 k1, ?_⟩
    have e : lift1 X O w (r + r') - (P + Q) = (lift1 X O w r - P) + (lift1 X O w r' - Q) := by
      rw [map_add]; abel
    rw [e]
    exact Submodule.add_mem _ h2 k2
  zero_mem' := ⟨0, (cleanSub X O w 1 o).zero_mem, by simp⟩
  smul_mem' := by
    rintro a P ⟨r, h1, h2⟩
    refine ⟨a • r, (cleanSub X O w 1 o).smul_mem a h1, ?_⟩
    have e : lift1 X O w (a • r) - a • P = a • (lift1 X O w r - P) := by
      rw [AlgHom.map_smul_of_tower, smul_sub]
    rw [e]
    exact Submodule.smul_mem _ _ h2

end Liftable

section Cls

variable {X : Loc} {O : Type} [CommRing O] [IsDomain O]

def TCls (w : O) (dgT : X.TT × Bool → ℕ) (oT cnt : ℕ) (P : RHH O X) : Prop :=
  ∀ M : MonH X, (P.coeff M ≠ 0 → ∀ l, multideg M l = dgT l) ∧
    ∃ c : O, P.coeff M = algebraMap O (KK O) (w ^ (max cnt (ndM X M - oT)) * c)

/- English proof (translation)
Introduce `M`. Distinguish the cases in `hM : M = 0`. Substitute `hM` using the available equality. Use `⟨fun _ l => by simp [multideg], 1, ?_⟩` and prove the remaining obligations. Simplify using `[ndM, degUS]`.

Use `⟨fun h => by simp [MvPolynomial.coeff_one, Ne.symm hM] at h, 0, ?_⟩` and prove the remaining obligations. Simplify using `[MvPolynomial.coeff_one, Ne.symm hM]`.
-/
theorem TCls.one (w : O) : TCls (X := X) w (fun _ => 0) 0 0 (1 : RHH O X) := by
  intro M
  by_cases hM : M = 0
  · subst hM
    refine ⟨fun _ l => by simp [multideg], 1, ?_⟩
    simp [ndM, degUS]
  · refine ⟨fun h => by simp [MvPolynomial.coeff_one, Ne.symm hM] at h, 0, ?_⟩
    simp [MvPolynomial.coeff_one, Ne.symm hM]

/- English proof (translation)
Introduce `M`. Prove the components needed by the constructor for the conclusion. Introduce `h l`. Rewrite `h` using `[MvPolynomial.coeff_mul]`. Take `⟨x, hx, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`.

Establish `h1 : P.coeff x.1 ≠ 0` using `left_ne_zero_of_mul hne`. Establish `h2 : Q.coeff x.2 ≠ 0` using `right_ne_zero_of_mul hne`. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Rewrite using `[← hx, multideg_add, (hP x.1).1 h1 l, (hQ x.2).1 h2 l]`. Rewrite using `[MvPolynomial.coeff_mul]`.

Establish `key : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal M, ∃ c0 : O, P.coeff x.1 * Q.coeff x.2 = algebraMap O (KK O) (w ^ (max (c + c') (ndM X M - (o + o'))) * c0)`. Introduce `x hx`. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Take `⟨a, ha⟩` from `(hP x.1).2`. Take `⟨b, hb⟩` from `(hQ x.2).2`.

Establish `hle : max (c + c') (ndM X M - (o + o')) ≤ max c (ndM X x.1 - o) + max c' (ndM X x.2 - o')`. Rewrite using `[← hx, ndM_add]`. Apply `max_le` to reduce the goal to its premises. Conclude with `Nat.add_le_add (le_max_left _ _) (le_max_left _ _)`. Use `le_max_right c (ndM X x.1 - o)` as an intermediate fact.

Use `le_max_right c' (ndM X x.2 - o')` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hle`. Use `⟨w ^ k * (a * b), ?_⟩` and prove the remaining obligations. Rewrite using `[ha, hb, ← map_mul]`.

Use `congr 1`. Rewrite using `[show w ^ max c (ndM X x.1 - o) * a * (w ^ max c' (ndM X x.2 - o') * b) = w ^ (max c (ndM X x.1 - o) + max c' (ndM X x.2 - o')) * (a * b) by ring, hk, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Use `choose! f hf using key`. Rewrite using `[Finset.sum_congr rfl hf, ← map_sum, ← Finset.mul_sum]`.

Conclude with `⟨_, rfl⟩`.
-/
theorem TCls.mul {w : O} {d d' : X.TT × Bool → ℕ} {o o' c c' : ℕ} {P Q : RHH O X} (hP : TCls w d o c P)
    (hQ : TCls w d' o' c' Q) : TCls w (fun l => d l + d' l) (o + o') (c + c') (P * Q) := by
  intro M
  constructor
  · intro h l
    rw [MvPolynomial.coeff_mul] at h
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : P.coeff x.1 ≠ 0 := left_ne_zero_of_mul hne
    have h2 : Q.coeff x.2 ≠ 0 := right_ne_zero_of_mul hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [← hx, multideg_add, (hP x.1).1 h1 l, (hQ x.2).1 h2 l]
  · rw [MvPolynomial.coeff_mul]
    have key : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal M, ∃ c0 : O, P.coeff x.1 * Q.coeff x.2 =
        algebraMap O (KK O) (w ^ (max (c + c') (ndM X M - (o + o'))) * c0) := by
      intro x hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      obtain ⟨a, ha⟩ := (hP x.1).2
      obtain ⟨b, hb⟩ := (hQ x.2).2
      have hle : max (c + c') (ndM X M - (o + o')) ≤
          max c (ndM X x.1 - o) + max c' (ndM X x.2 - o') := by
        rw [← hx, ndM_add]
        apply max_le
        · exact Nat.add_le_add (le_max_left _ _) (le_max_left _ _)
        · have := le_max_right c (ndM X x.1 - o)
          have := le_max_right c' (ndM X x.2 - o')
          omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      refine ⟨w ^ k * (a * b), ?_⟩
      rw [ha, hb, ← map_mul]
      congr 1
      rw [show w ^ max c (ndM X x.1 - o) * a * (w ^ max c' (ndM X x.2 - o') * b) =
        w ^ (max c (ndM X x.1 - o) + max c' (ndM X x.2 - o')) * (a * b) by ring, hk, pow_add]
      ring
    choose! f hf using key
    rw [Finset.sum_congr rfl hf, ← map_sum, ← Finset.mul_sum]
    exact ⟨_, rfl⟩

/- English proof (translation)
Proceed by induction on `u with`. Consider the case `zero => simpa using TCls.one (X := X) w`. Consider the case `succ u ih`. Rewrite using `[pow_succ]`. Establish `h` using `ih.mul hP`.

Establish `e1 : (fun l => (u + 1) * d l) = (fun l => u * d l + d l)`. Use function extensionality and compare the values at `l`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, show (u + 1) * o = u * o + o by ring, show (u + 1) * c = u * c + c by ring]`. Conclude with `h`.
-/
theorem TCls.pow {w : O} {d : X.TT × Bool → ℕ} {o c : ℕ} {P : RHH O X} (hP : TCls w d o c P) (u : ℕ) :
    TCls w (fun l => u * d l) (u * o) (u * c) (P ^ u) := by
  induction u with
  | zero => simpa using TCls.one (X := X) w
  | succ u ih =>
    rw [pow_succ]
    have h := ih.mul hP
    have e1 : (fun l => (u + 1) * d l) = (fun l => u * d l + d l) := by
      funext l
      ring
    rw [e1, show (u + 1) * o = u * o + o by ring, show (u + 1) * c = u * c + c by ring]
    exact h

/- English proof (translation)
Use `revert hP`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `using TCls.one (X := X) w`. Introduce `a s ha ih hP`.

Rewrite using `[Finset.prod_insert ha]`. Establish `h1` using `hP a (Finset.mem_insert_self a s)`. Establish `h2` using `ih (fun b hb => hP b (Finset.mem_insert_of_mem hb))`. Establish `h` using `h1.mul h2`. Simplify using `only [Finset.sum_insert ha]`.

Conclude with `h`.
-/
theorem TCls.prod {w : O} {κ : Type} (s : Finset κ) (d : κ → X.TT × Bool → ℕ) (o c : κ → ℕ) (P : κ → RHH O X)
    (hP : ∀ a ∈ s, TCls w (d a) (o a) (c a) (P a)) :
    TCls w (fun l => ∑ a ∈ s, d a l) (∑ a ∈ s, o a) (∑ a ∈ s, c a) (∏ a ∈ s, P a) := by
  classical
  revert hP
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using TCls.one (X := X) w
  · intro a s ha ih hP
    rw [Finset.prod_insert ha]
    have h1 := hP a (Finset.mem_insert_self a s)
    have h2 := ih (fun b hb => hP b (Finset.mem_insert_of_mem hb))
    have h := h1.mul h2
    simp only [Finset.sum_insert ha]
    exact h

end Cls

structure FacSys (C0 Cde CE1 CE2 : ℝ) (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] (w : O) (mm : ℝ) (n o : ℕ) (σ : RHH O X) where
  κ : Type
  fin : Fintype κ
  mult : κ → ℕ
  f : κ → RHH O X
  sg : κ → RHH O X
  od : κ → ℕ
  dg : κ → X.TT × Bool → ℕ
  fR : RHH O X
  sgR : RHH O X
  oR : ℕ
  fac : ∀ a, IsFac w (f a) (od a) (sg a)
  sgHom : ∀ a, ∀ m ∈ (sg a).support, ndM X m = od a
  liftPol : ∀ a, lift1 X O w (f a) ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dg a)
  sgPol : ∀ a, sg a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (dg a)
  rigA : InA fR
  rigLift : lift1 X O w fR = (w ^ oR) • sgR
  rigInt : InA sgR
  clean : ∀ g' : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), IsGLW g' →
    ratPlane X.p X.n' 1 g' ≠ ratPlane X.p X.n' 1 1 →
    InWjRg X.p X.n' O w 1 (hhLetters X.TT) g' (fR * ∏ a, f a ^ mult a) (o + X.c)
  total : fR * ∏ a, f a ^ mult a ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) (hhDegs X.TT X.aT X.bT)
  ordEq : oR + ∑ a, mult a * od a = o
  symEq : sgR * ∏ a, sg a ^ mult a = σ
  core : ∀ u : κ → ℕ, (∀ a, u a ≤ mult a) → ∀ (M : MonH X) (e : ℕ), 1 ≤ e → ∑ a, u a ≤ e → e < n →
    (∀ l, multideg M l = ∑ a, u a * dg a l) → ndM X M ≤ ∑ a, u a * od a + e →
    sgR * (∏ a, sg a ^ (mult a - u a)) * monomial M 1 ∈ SSe C0 Cde CE1 CE2 X O mm n o e

section Asm

variable {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [Algebra (WF X.p X.n') O] {w : O} {mm : ℝ} {n o : ℕ} {σ : RHH O X}

/- English proof (translation)
Introduce `m`. Take `⟨c, hc⟩` from `h m`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `hw' : algebraMap O (KK O) w ≠ 0` using `fun h0 => hw (IsFractionRing.injective O (KK O) (h0.trans (map_zero _).symm))`. Rewrite using `[MvPolynomial.coeff_C_mul, hc, map_mul, map_mul, map_pow, map_pow, pow_add, mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hw')]`.
-/
theorem inWj_div (hw : w ≠ 0) {τ : Type} {P : MvPolynomial τ (KK O)} {a b : ℕ} (h : InWj w P (a + b)) :
    InWj w (C ((algebraMap O (KK O) w ^ a)⁻¹) * P) b := by
  intro m
  obtain ⟨c, hc⟩ := h m
  refine ⟨c, ?_⟩
  have hw' : algebraMap O (KK O) w ≠ 0 := fun h0 =>
    hw (IsFractionRing.injective O (KK O) (h0.trans (map_zero _).symm))
  rw [MvPolynomial.coeff_C_mul, hc, map_mul, map_mul, map_pow, map_pow, pow_add, mul_assoc,
    inv_mul_cancel_left₀ (pow_ne_zero _ hw')]

/- English proof (translation)
Establish `hK : algebraMap O (KK O) w ≠ 0` using `fun h0 => hw (IsFractionRing.injective O (KK O) (by rw [h0, map_zero]))`. Introduce `M`. Prove the components needed by the constructor for the conclusion. Introduce `h l`. Establish `hmem : C ((algebraMap O (KK O) w ^ od)⁻¹) * lift1 X O w f - sg ∈ Pol (KK O) (ι` using `X.TT × Bool) (X.m + 1) dg := by`.

Use `Submodule.sub_mem _ ?_ hS` and prove the remaining obligations. Rewrite using `[← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hL`. Use `((MvPolynomial.mem_restrictSupport_iff _).1 hmem) (Finset.mem_coe.2 (MvPolynomial.mem_support_iff.2 h))` as an intermediate fact. Conclude with `this l`.

Establish `e : C ((algebraMap O (KK O) w ^ od)⁻¹) * lift1 X O w f - sg = C ((algebraMap O (KK O) w ^ od)⁻¹) * (lift1 X O w f - (w ^ od) • sg)`. Rewrite using `[mul_sub, ← C_mul_eq_smul, ← mul_assoc, ← C_mul, map_pow, inv_mul_cancel₀ (pow_ne_zero _ hK), C_1, one_mul]`. Distinguish the cases in `hnd : ndM X M - od ≤ 1`. Rewrite using `[max_eq_left hnd, e]`. Conclude with `inWj_div hw hf.sym M`.

Establish `hgt : od < ndM X M` using `by omega`. Establish `h0 : sg.coeff M = 0`. Assume the negation of the conclusion as `h`. Use `hH M (MvPolynomial.mem_support_iff.2 h)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Take `⟨a, ha⟩` from `lift_substitution_coeff_divisible X.p X.n' O w (hhLetters X.TT) 1 1 (isGLW_one' _) f hf.inA M`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[max_eq_right (by omega), coeff_sub, h0, sub_zero, coeff_C_mul]`. Establish `ha' : (lift1 X O w f).coeff M = algebraMap O (KK O) (w ^ ndM X M * a)` using `ha`. Rewrite using `[ha']`.

Establish `: ndM X M = od + (ndM X M - od)` using `by omega`. Use `conv_lhs => rw [this]`. Rewrite using `[pow_add, mul_assoc, map_mul, map_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hK), one_mul]`.
-/
theorem tail_cls (hw : w ≠ 0) {f sg : RHH O X} {od : ℕ} {dg : X.TT × Bool → ℕ} (hf : IsFac w f od sg)
    (hH : ∀ m ∈ sg.support, ndM X m = od) (hL : lift1 X O w f ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dg)
    (hS : sg ∈ Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dg) :
    TCls w dg od 1 (C ((algebraMap O (KK O) w ^ od)⁻¹) * lift1 X O w f - sg) := by
  classical
  have hK : algebraMap O (KK O) w ≠ 0 := fun h0 => hw (IsFractionRing.injective O (KK O) (by rw [h0, map_zero]))
  intro M
  constructor
  · intro h l
    have hmem : C ((algebraMap O (KK O) w ^ od)⁻¹) * lift1 X O w f - sg ∈
        Pol (KK O) (ι := X.TT × Bool) (X.m + 1) dg := by
      refine Submodule.sub_mem _ ?_ hS
      rw [← smul_eq_C_mul]
      exact Submodule.smul_mem _ _ hL
    have := ((MvPolynomial.mem_restrictSupport_iff _).1 hmem) (Finset.mem_coe.2 (MvPolynomial.mem_support_iff.2 h))
    exact this l
  · have e : C ((algebraMap O (KK O) w ^ od)⁻¹) * lift1 X O w f - sg =
        C ((algebraMap O (KK O) w ^ od)⁻¹) * (lift1 X O w f - (w ^ od) • sg) := by
      rw [mul_sub, ← C_mul_eq_smul, ← mul_assoc, ← C_mul, map_pow, inv_mul_cancel₀ (pow_ne_zero _ hK), C_1, one_mul]
    by_cases hnd : ndM X M - od ≤ 1
    · rw [max_eq_left hnd, e]
      exact inWj_div hw hf.sym M
    · have hgt : od < ndM X M := by omega
      have h0 : sg.coeff M = 0 := by
        by_contra h
        have := hH M (MvPolynomial.mem_support_iff.2 h)
        omega
      obtain ⟨a, ha⟩ := lift_substitution_coeff_divisible X.p X.n' O w (hhLetters X.TT) 1 1 (isGLW_one' _) f hf.inA M
      refine ⟨a, ?_⟩
      rw [max_eq_right (by omega), coeff_sub, h0, sub_zero, coeff_C_mul]
      have ha' : (lift1 X O w f).coeff M = algebraMap O (KK O) (w ^ ndM X M * a) := ha
      rw [ha']
      have : ndM X M = od + (ndM X M - od) := by omega
      conv_lhs => rw [this]
      rw [pow_add, mul_assoc, map_mul, map_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hK), one_mul]

/- English proof (translation)
Set `_` to `F.fin`. Establish `hK : algebraMap O (KK O) w ≠ 0` using `fun h0 => hw (IsFractionRing.injective O (KK O) (by rw [h0, map_zero]))`. Use `set wK := algebraMap O (KK O) w with hwK`. Use `set Ftot := F.fR * ∏ a, F.f a ^ F.mult a with hFtot`. Establish `hsgA : ∀ u : F.κ → ℕ, InWj w (F.sgR * ∏ a, F.sg a ^ u a) 0`.

Introduce `u`. Establish `h1` using `inWj_prod (w := w) Finset.univ (fun a => F.sg a ^ u a) (fun a => u a * 0) (fun a _ => inWj_pow ((inA_iff_wj w).1 (F.fac a).sgInt) (u a))`. Establish `h2` using `inWj_mul ((inA_iff_wj w).1 F.rigInt) h1`. Simplify using `using h2`. Use `⟨C ((wK ^ o)⁻¹) * Ftot, ⟨?_, ?_, fun g' hg' hne => ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ F.total`. Rewrite using `[← mul_assoc, ← C_mul, map_pow, mul_inv_cancel₀ (pow_ne_zero _ hK), C_1, one_mul, inA_iff_wj w]`. Establish `h1` using `inWj_prod (w := w) Finset.univ (fun a => F.f a ^ F.mult a) (fun a => F.mult a * 0) (fun a _ => inWj_pow ((inA_iff_wj w).1 (F.fac a).inA) (F.mult a))`. Establish `h2` using `inWj_mul ((inA_iff_wj w).1 F.rigA) h1`.

Simplify using `using h2`. Unfold `InWjRg`. Rewrite using `[map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]`. Conclude with `inWj_div hw (F.clean g' hg' hne)`. Use `set t : F.κ → RHH O X := fun a => C ((wK ^ F.od a)⁻¹) * lift1 X O w (F.f a) - F.sg a with ht`.

Establish `h1 : ∀ a, lift1 X O w (F.f a) = C (wK ^ F.od a) * (t a + F.sg a)`. Introduce `a`. Simplify using `only [ht, sub_add_cancel]`. Rewrite using `[← mul_assoc, ← C_mul, mul_inv_cancel₀ (pow_ne_zero _ hK), C_1, one_mul]`. Establish `h2 : lift1 X O w Ftot = C (wK ^ o) * (F.sgR * ∏ a, (t a + F.sg a) ^ F.mult a)`.

Rewrite using `[hFtot, map_mul, map_prod, F.rigLift, ← C_mul_eq_smul]`. Simplify using `only [map_pow, h1, mul_pow]`. Rewrite using `[Finset.prod_mul_distrib]`. Establish `this' : ∏ a, ((C wK : RHH O X) ^ F.od a) ^ F.mult a = C wK ^ (∑ a, F.mult a * F.od a)`. Rewrite using `[← Finset.prod_pow_eq_pow_sum]`.

Conclude with `Finset.prod_congr rfl fun a _ => by rw [← pow_mul, mul_comm]`. Establish `ho : (C wK : RHH O X) ^ o = C wK ^ F.oR * C wK ^ (∑ a, F.mult a * F.od a)` using `by rw [← pow_add, F.ordEq]`. Rewrite using `[this', ho]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : lift1 X O w (C ((wK ^ o)⁻¹) * Ftot) = F.sgR * ∏ a, (t a + F.sg a) ^ F.mult a`.

Rewrite using `[map_mul, MvPolynomial.algHom_C, h2, MvPolynomial.algebraMap_eq, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hK), C_1, one_mul]`. Establish `hcls : ∀ a, TCls w (F.dg a) (F.od a) 1 (t a)` using `fun a => tail_cls hw (F.fac a) (F.sgHom a) (F.liftPol a) (F.sgPol a)`. Establish `h4 : ∏ a, (t a + F.sg a) ^ F.mult a = ∑ u ∈ Fintype.piFinset (fun a => Finset.range (F.mult a + 1)), ∏ a, (t a ^ u a * F.sg a ^ (F.mult a - u a) * ((F.mult a).choose (u a) : RHH O X))`. Simplify using `only [add_pow]`. Conclude with `Finset.prod_univ_sum _ _`.

Establish `h0mem : (fun _ => 0 : F.κ → ℕ) ∈ Fintype.piFinset (fun a => Finset.range (F.mult a + 1))`. Simplify using `[Fintype.mem_piFinset]`. Establish `h5 : lift1 X O w (C ((wK ^ o)⁻¹) * Ftot) - σ = ∑ u ∈ (Fintype.piFinset (fun a => Finset.range (F.mult a + 1))).erase (fun _ => 0), F.sgR * ∏ a, (t a ^ u a * F.sg a ^ (F.mult a - u a) * ((F.mult a).choose (u a) : RHH O X))`. Establish `h0t : F.sgR * ∏ a, (t a ^ (0 : ℕ) * F.sg a ^ (F.mult a - 0) * ((F.mult a).choose 0 : RHH O X)) = σ`. Simplify using `using F.symEq`.

Rewrite using `[h3, h4, ← Finset.add_sum_erase _ _ h0mem, mul_add, ← Finset.mul_sum]`. Use `beta_reduce`. Rewrite using `[h0t, add_sub_cancel_left]`. Rewrite using `[h5]`. Use `Submodule.sum_mem _ fun u hu => ?_` and prove the remaining obligations.

Establish `hu0 : u ≠ fun _ => 0` using `(Finset.mem_erase.1 hu).1`. Establish `hule : ∀ a, u a ≤ F.mult a` using `fun a => by`. Use `Fintype.mem_piFinset.1 (Finset.mem_erase.1 hu).2 a` as an intermediate fact. Conclude with `Nat.lt_succ_iff.1 (Finset.mem_range.1 this)`. Establish `hpos : 1 ≤ ∑ a, u a`.

Assume the negation of the conclusion as `h`. Establish `h' : ∑ a, u a = 0` using `by omega`. Conclude with `hu0 (funext fun a => (Finset.sum_eq_zero_iff.1 h') a (Finset.mem_univ a))`. Use `set U := F.sgR * ∏ a, F.sg a ^ (F.mult a - u a) with hU`. Use `set Pu := ∏ a, t a ^ u a with hPu`.

Establish `hPcls : TCls w (fun l => ∑ a, u a * F.dg a l) (∑ a, u a * F.od a) (∑ a, u a * 1) Pu` using `TCls.prod Finset.univ _ _ _ _ fun a _ => (hcls a).pow (u a)`. Establish `e6 : F.sgR * ∏ a, (t a ^ u a * F.sg a ^ (F.mult a - u a) * ((F.mult a).choose (u a) : RHH O X)) = (∏ a, (F.mult a).choose (u a)) • (U * Pu)`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib, nsmul_eq_mul, Nat.cast_prod, hU, hPu]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e6]`.

Use `Submodule.smul_of_tower_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[← MvPolynomial.support_sum_monomial_coeff Pu, Finset.mul_sum]`. Use `Submodule.sum_mem _ fun M hM => ?_` and prove the remaining obligations. Take `⟨hdeg, c, hc⟩` from `hPcls M`. Establish `hdeg'` using `hdeg (MvPolynomial.mem_support_iff.1 hM)`.

Use `set e := max (∑ a, u a * 1) (ndM X M - ∑ a, u a * F.od a) with he`. Establish `e7 : U * monomial M (Pu.coeff M) = c • ((w ^ e) • (U * monomial M 1))`. Rewrite using `[hc, smul_smul, mul_comm c, ← mul_smul_comm]`. Use `congr 1`. Rewrite using `[← algebraMap_smul (KK O) (w ^ e * c), MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`.

Rewrite using `[e7]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hsum1 : ∑ a, u a * 1 = ∑ a, u a` using `by simp`. Distinguish the cases in `hen : e < n`. Use `tail_of_ssg (Finset.mem_Ico.2 ⟨?_, hen⟩) ?_` and prove the remaining obligations.

Rewrite using `[he, hsum1]`. Conclude with `le_trans hpos (le_max_left _ _)`. Use `F.core u hule M e ?_ ?_ hen hdeg' ?_` and prove the remaining obligations. Rewrite using `[he, hsum1]`. Conclude with `le_trans hpos (le_max_left _ _)`.

Rewrite using `[he, hsum1]`. Conclude with `le_max_left _ _`. Use `le_max_right (∑ a, u a * 1) (ndM X M - ∑ a, u a * F.od a)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `tail_of_wj ?_` and prove the remaining obligations.

Establish `hUM : InWj w (U * monomial M 1) 0`. Establish `hm : InWj w (monomial M (1 : KK O) : RHH O X) 0`. Introduce `m'`. Rewrite using `[MvPolynomial.coeff_monomial]`. Distinguish the cases in `h : M = m'`.

Conclude with `⟨1, by simp [h]⟩`. Conclude with `⟨0, by simp [h]⟩`. Simplify using `using inWj_mul (hsgA _) hm`. Use `wj_smul_pow hUM e` as an intermediate fact. Rewrite `this` using `[zero_add]`.

Conclude with `wj_mono (by omega) this`.
-/
theorem FacSys.liftable (hw : w ≠ 0) (F : FacSys C0 Cde CE1 CE2 X O w mm n o σ) :
    σ ∈ liftSub C0 Cde CE1 CE2 X O w mm n o := by
  classical
  let _ := F.fin
  have hK : algebraMap O (KK O) w ≠ 0 := fun h0 => hw (IsFractionRing.injective O (KK O) (by rw [h0, map_zero]))
  set wK := algebraMap O (KK O) w with hwK
  set Ftot := F.fR * ∏ a, F.f a ^ F.mult a with hFtot
  have hsgA : ∀ u : F.κ → ℕ, InWj w (F.sgR * ∏ a, F.sg a ^ u a) 0 := by
    intro u
    have h1 := inWj_prod (w := w) Finset.univ (fun a => F.sg a ^ u a) (fun a => u a * 0)
      (fun a _ => inWj_pow ((inA_iff_wj w).1 (F.fac a).sgInt) (u a))
    have h2 := inWj_mul ((inA_iff_wj w).1 F.rigInt) h1
    simpa using h2
  refine ⟨C ((wK ^ o)⁻¹) * Ftot, ⟨?_, ?_, fun g' hg' hne => ?_⟩, ?_⟩
  · rw [← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ F.total
  · rw [← mul_assoc, ← C_mul, map_pow, mul_inv_cancel₀ (pow_ne_zero _ hK), C_1, one_mul, inA_iff_wj w]
    have h1 := inWj_prod (w := w) Finset.univ (fun a => F.f a ^ F.mult a) (fun a => F.mult a * 0)
      (fun a _ => inWj_pow ((inA_iff_wj w).1 (F.fac a).inA) (F.mult a))
    have h2 := inWj_mul ((inA_iff_wj w).1 F.rigA) h1
    simpa using h2
  · unfold InWjRg
    rw [map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]
    exact inWj_div hw (F.clean g' hg' hne)
  · set t : F.κ → RHH O X := fun a => C ((wK ^ F.od a)⁻¹) * lift1 X O w (F.f a) - F.sg a with ht
    have h1 : ∀ a, lift1 X O w (F.f a) = C (wK ^ F.od a) * (t a + F.sg a) := by
      intro a
      simp only [ht, sub_add_cancel]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (pow_ne_zero _ hK), C_1, one_mul]
    have h2 : lift1 X O w Ftot = C (wK ^ o) * (F.sgR * ∏ a, (t a + F.sg a) ^ F.mult a) := by
      rw [hFtot, map_mul, map_prod, F.rigLift, ← C_mul_eq_smul]
      simp only [map_pow, h1, mul_pow]
      rw [Finset.prod_mul_distrib]
      have this' : ∏ a, ((C wK : RHH O X) ^ F.od a) ^ F.mult a = C wK ^ (∑ a, F.mult a * F.od a) := by
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_congr rfl fun a _ => by rw [← pow_mul, mul_comm]
      have ho : (C wK : RHH O X) ^ o = C wK ^ F.oR * C wK ^ (∑ a, F.mult a * F.od a) := by rw [← pow_add, F.ordEq]
      rw [this', ho]
      ring
    have h3 : lift1 X O w (C ((wK ^ o)⁻¹) * Ftot) = F.sgR * ∏ a, (t a + F.sg a) ^ F.mult a := by
      rw [map_mul, MvPolynomial.algHom_C, h2, MvPolynomial.algebraMap_eq, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (pow_ne_zero _ hK), C_1, one_mul]
    have hcls : ∀ a, TCls w (F.dg a) (F.od a) 1 (t a) := fun a =>
      tail_cls hw (F.fac a) (F.sgHom a) (F.liftPol a) (F.sgPol a)

    have h4 : ∏ a, (t a + F.sg a) ^ F.mult a =
        ∑ u ∈ Fintype.piFinset (fun a => Finset.range (F.mult a + 1)),
          ∏ a, (t a ^ u a * F.sg a ^ (F.mult a - u a) * ((F.mult a).choose (u a) : RHH O X)) := by
      simp only [add_pow]
      exact Finset.prod_univ_sum _ _
    have h0mem : (fun _ => 0 : F.κ → ℕ) ∈ Fintype.piFinset (fun a => Finset.range (F.mult a + 1)) := by
      simp [Fintype.mem_piFinset]
    have h5 : lift1 X O w (C ((wK ^ o)⁻¹) * Ftot) - σ =
        ∑ u ∈ (Fintype.piFinset (fun a => Finset.range (F.mult a + 1))).erase (fun _ => 0),
          F.sgR * ∏ a, (t a ^ u a * F.sg a ^ (F.mult a - u a) * ((F.mult a).choose (u a) : RHH O X)) := by
      have h0t : F.sgR * ∏ a, (t a ^ (0 : ℕ) * F.sg a ^ (F.mult a - 0) * ((F.mult a).choose 0 : RHH O X)) = σ := by
        simpa using F.symEq
      rw [h3, h4, ← Finset.add_sum_erase _ _ h0mem, mul_add, ← Finset.mul_sum]
      beta_reduce
      rw [h0t, add_sub_cancel_left]
    rw [h5]
    refine Submodule.sum_mem _ fun u hu => ?_
    have hu0 : u ≠ fun _ => 0 := (Finset.mem_erase.1 hu).1
    have hule : ∀ a, u a ≤ F.mult a := fun a => by
      have := Fintype.mem_piFinset.1 (Finset.mem_erase.1 hu).2 a
      exact Nat.lt_succ_iff.1 (Finset.mem_range.1 this)
    have hpos : 1 ≤ ∑ a, u a := by
      by_contra h
      have h' : ∑ a, u a = 0 := by omega
      exact hu0 (funext fun a => (Finset.sum_eq_zero_iff.1 h') a (Finset.mem_univ a))
    set U := F.sgR * ∏ a, F.sg a ^ (F.mult a - u a) with hU
    set Pu := ∏ a, t a ^ u a with hPu
    have hPcls : TCls w (fun l => ∑ a, u a * F.dg a l) (∑ a, u a * F.od a) (∑ a, u a * 1) Pu :=
      TCls.prod Finset.univ _ _ _ _ fun a _ => (hcls a).pow (u a)
    have e6 : F.sgR * ∏ a, (t a ^ u a * F.sg a ^ (F.mult a - u a) * ((F.mult a).choose (u a) : RHH O X)) =
        (∏ a, (F.mult a).choose (u a)) • (U * Pu) := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, nsmul_eq_mul, Nat.cast_prod, hU, hPu]
      ring
    rw [e6]
    refine Submodule.smul_of_tower_mem _ _ ?_
    rw [← MvPolynomial.support_sum_monomial_coeff Pu, Finset.mul_sum]
    refine Submodule.sum_mem _ fun M hM => ?_
    obtain ⟨hdeg, c, hc⟩ := hPcls M
    have hdeg' := hdeg (MvPolynomial.mem_support_iff.1 hM)
    set e := max (∑ a, u a * 1) (ndM X M - ∑ a, u a * F.od a) with he
    have e7 : U * monomial M (Pu.coeff M) = c • ((w ^ e) • (U * monomial M 1)) := by
      rw [hc, smul_smul, mul_comm c, ← mul_smul_comm]
      congr 1
      rw [← algebraMap_smul (KK O) (w ^ e * c), MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e7]
    refine Submodule.smul_mem _ _ ?_
    have hsum1 : ∑ a, u a * 1 = ∑ a, u a := by simp
    by_cases hen : e < n
    · refine tail_of_ssg (Finset.mem_Ico.2 ⟨?_, hen⟩) ?_
      · rw [he, hsum1]; exact le_trans hpos (le_max_left _ _)
      · refine F.core u hule M e ?_ ?_ hen hdeg' ?_
        · rw [he, hsum1]; exact le_trans hpos (le_max_left _ _)
        · rw [he, hsum1]; exact le_max_left _ _
        · have := le_max_right (∑ a, u a * 1) (ndM X M - ∑ a, u a * F.od a)
          omega
    · refine tail_of_wj ?_
      have hUM : InWj w (U * monomial M 1) 0 := by
        have hm : InWj w (monomial M (1 : KK O) : RHH O X) 0 := by
          intro m'
          rw [MvPolynomial.coeff_monomial]
          by_cases h : M = m'
          · exact ⟨1, by simp [h]⟩
          · exact ⟨0, by simp [h]⟩
        simpa using inWj_mul (hsgA _) hm
      have := wj_smul_pow hUM e
      rw [zero_add] at this
      exact wj_mono (by omega) this

end Asm

end Formalism.MainNotions.ColumnSystems.Pf
