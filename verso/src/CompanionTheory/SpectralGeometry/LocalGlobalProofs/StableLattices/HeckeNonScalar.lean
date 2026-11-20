import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEquality

noncomputable section

open Finset Polynomial

namespace GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof

open CompanionTheory.RgExh CompanionTheory.RgExh.Hk ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

section Poly

variable {A : Type*} [Ring A] [Algebra ℂ A]

def IsP (g : ℂ → A) : Prop := ∃ p : A[X], ∀ t, g t = p.eval (algebraMap ℂ A t)

/- English proof (translation)
Assemble the required witnesses or components as `⟨C a, fun t => by simp⟩`.
-/
theorem IsP.const (a : A) : IsP (fun _ : ℂ => a) := ⟨C a, fun t => by simp⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨C a + C b * X, fun t => by simp [eval_mul_X]⟩`.
-/
theorem IsP.lin (a b : A) : IsP (fun t : ℂ => a + b * algebraMap ℂ A t) :=
  ⟨C a + C b * X, fun t => by simp [eval_mul_X]⟩

/- English proof (translation)
Take `⟨p, hp⟩` from `hf`. Take `⟨q, hq⟩` from `hg`. Use `⟨p * q, fun t => ?_⟩` and prove the remaining obligations. Use `show f t * g t = _`. Rewrite using `[hp, hq]`.

Conclude with `(eval₂_mul_noncomm (RingHom.id A) (algebraMap ℂ A t) (fun k => (Algebra.commutes t _).symm)).symm`.
-/
theorem IsP.mul {f g : ℂ → A} (hf : IsP f) (hg : IsP g) : IsP (fun t => f t * g t) := by
  obtain ⟨p, hp⟩ := hf
  obtain ⟨q, hq⟩ := hg
  refine ⟨p * q, fun t => ?_⟩
  show f t * g t = _
  rw [hp, hq]
  exact (eval₂_mul_noncomm (RingHom.id A) (algebraMap ℂ A t)
    (fun k => (Algebra.commutes t _).symm)).symm

/- English proof (translation)
Use `choose p hp using hf`. Conclude with `⟨∑ i ∈ s, p i, fun t => by simp [eval_finset_sum, hp]⟩`.
-/
theorem IsP.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → A} (hf : ∀ i, IsP (f i)) :
    IsP (fun t => ∑ i ∈ s, f i t) := by
  choose p hp using hf
  exact ⟨∑ i ∈ s, p i, fun t => by simp [eval_finset_sum, hp]⟩

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using IsP.const (1 : A)`. Consider the case `cons f l ih`. Simplify using `only [List.map_cons, List.prod_cons]`. Conclude with `(h f (by simp)).mul (ih fun g hg => h g (by simp [hg]))`.
-/
theorem IsP.listProd (l : List (ℂ → A)) (h : ∀ f ∈ l, IsP f) :
    IsP (fun t => (l.map fun f => f t).prod) := by
  induction l with
  | nil => simpa using IsP.const (1 : A)
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (h f (by simp)).mul (ih fun g hg => h g (by simp [hg]))

/- English proof (translation)
Distinguish the cases in `h : a = b`. Use `IsP.lin (E a b + algebraMap ℂ A x₀) (1 : A)` as an intermediate fact. Use `this using 2 with t` and compare the differences between its conclusion and the goal. Simplify using `[capEntry, h, map_add, add_assoc]`. Use `IsP.const (E a b)` as an intermediate fact.

Use `this using 2 with t` and compare the differences between its conclusion and the goal. Simplify using `[capEntry, h]`.
-/
theorem isPolynomial_capelliEntry {n : ℕ} (E : Fin n → Fin n → A) (x₀ : ℂ) (a b : Fin n) :
    IsP (fun t : ℂ => capEntry E (x₀ + t) a b) := by
  by_cases h : a = b
  · have := IsP.lin (E a b + algebraMap ℂ A x₀) (1 : A)
    convert this using 2 with t
    simp [capEntry, h, map_add, add_assoc]
  · have := IsP.const (E a b)
    convert this using 2 with t
    simp [capEntry, h]

/- English proof (translation)
Unfold `cminor`. Use `IsP.sum _ fun σ => ?_` and prove the remaining obligations. Apply the tactic sequence `have h := (IsP.const ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A))).mul (IsP.listProd (List.ofFn fun j : Fin p => fun t : ℂ => capEntry E (x₀ - ((j : ℕ) : ℂ) + t) (R (σ j)) (S j)) (fun f hf => by`. Take `⟨j, rfl⟩` from `(List.mem_ofFn' _ _).1 hf`. Apply the tactic sequence `exact isPolynomial_capelliEntry E _ _ _))`.

Use `h using 2 with t` and compare the differences between its conclusion and the goal. Rewrite using `[zsmul_eq_mul, List.map_ofFn]`. Use `congr 2`. Use `congrArg List.ofFn (funext fun j => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isPolynomial_capelliMinor {n p : ℕ} (E : Fin n → Fin n → A) (R S : Fin p → Fin n) (x₀ : ℂ) :
    IsP (fun t : ℂ => cminor E R S (x₀ + t)) := by
  unfold cminor
  refine IsP.sum _ fun σ => ?_
  have h := (IsP.const ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A))).mul
    (IsP.listProd (List.ofFn fun j : Fin p => fun t : ℂ =>
      capEntry E (x₀ - ((j : ℕ) : ℂ) + t) (R (σ j)) (S j)) (fun f hf => by
        obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hf
        exact isPolynomial_capelliEntry E _ _ _))
  convert h using 2 with t
  rw [zsmul_eq_mul, List.map_ofFn]
  congr 2
  refine congrArg List.ofFn (funext fun j => ?_)
  simp only [Function.comp]
  congr 1
  ring

end Poly

/- English proof (translation)
Establish `hP'` using `(X_pow_dvd_iff (f := P) (n := 2)).1 hP`. Establish `hP0` using `hP' 0 (by norm_num)`. Establish `hP1` using `hP' 1 (by norm_num)`. Establish `key : ∀ φ : Module.Dual ℂ W, φ (T (w 0)) = 0 ∧ φ (T (w 1) + w 0) = 0`. Introduce `φ`.

Establish `hQ : (∑ i ∈ range k, C (φ (T (w i))) * X ^ i) + X * (∑ i ∈ range k, C (φ (w i)) * X ^ i) - C (φ u) * P = 0`. Use `Polynomial.funext fun t => ?_` and prove the remaining obligations. Use `congrArg φ (h t)` as an intermediate fact. Simplify using `only [map_add, map_sum, map_smul, smul_eq_mul] at this`. Simplify using `only [eval_sub, eval_add, eval_mul, eval_finset_sum, eval_C, eval_X, eval_pow, eval_zero]`.

Rewrite using `[sub_eq_zero, mul_comm (φ u)]`. Simplify using `only [mul_comm (φ _) (t ^ _)]`. Conclude with `this`. Establish `c0` using `congrArg (fun q : ℂ[X] => q.coeff 0) hQ`. Establish `c1` using `congrArg (fun q : ℂ[X] => q.coeff 1) hQ`.

Establish `k0 : 0 ∈ range k` using `mem_range.2 (by omega)`. Establish `k1 : 1 ∈ range k` using `mem_range.2 (by omega)`. Simplify using `only [coeff_sub, coeff_add, finset_sum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero, mul_ite, mul_one, mul_zero, coeff_X_mul, coeff_X_mul_zero, hP0, hP1] at c0 c1`. Simplify using `[k0, k1] at c0 c1`. Conclude with `⟨c0, by rw [map_add]; exact c1⟩`.

Conclude with `⟨(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => (key φ).1, (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => (key φ).2⟩`.
-/
theorem coeff_extract {W : Type*} [AddCommGroup W] [Module ℂ W] (T : Module.End ℂ W) (k : ℕ) (hk : 2 ≤ k)
    (w : ℕ → W) (P : ℂ[X]) (u : W) (hP : (X : ℂ[X]) ^ 2 ∣ P)
    (h : ∀ t : ℂ, T (∑ i ∈ range k, t ^ i • w i) + t • ∑ i ∈ range k, t ^ i • w i = P.eval t • u) :
    T (w 0) = 0 ∧ T (w 1) + w 0 = 0 := by
  have hP' := (X_pow_dvd_iff (f := P) (n := 2)).1 hP
  have hP0 := hP' 0 (by norm_num)
  have hP1 := hP' 1 (by norm_num)
  have key : ∀ φ : Module.Dual ℂ W, φ (T (w 0)) = 0 ∧ φ (T (w 1) + w 0) = 0 := by
    intro φ
    have hQ : (∑ i ∈ range k, C (φ (T (w i))) * X ^ i) + X * (∑ i ∈ range k, C (φ (w i)) * X ^ i)
        - C (φ u) * P = 0 := by
      refine Polynomial.funext fun t => ?_
      have := congrArg φ (h t)
      simp only [map_add, map_sum, map_smul, smul_eq_mul] at this
      simp only [eval_sub, eval_add, eval_mul, eval_finset_sum, eval_C, eval_X, eval_pow, eval_zero]
      rw [sub_eq_zero, mul_comm (φ u)]
      simp only [mul_comm (φ _) (t ^ _)]
      exact this
    have c0 := congrArg (fun q : ℂ[X] => q.coeff 0) hQ
    have c1 := congrArg (fun q : ℂ[X] => q.coeff 1) hQ
    have k0 : 0 ∈ range k := mem_range.2 (by omega)
    have k1 : 1 ∈ range k := mem_range.2 (by omega)
    simp only [coeff_sub, coeff_add, finset_sum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero,
      mul_ite, mul_one, mul_zero, coeff_X_mul, coeff_X_mul_zero, hP0, hP1] at c0 c1
    simp [k0, k1] at c0 c1
    exact ⟨c0, by rw [map_add]; exact c1⟩
  exact ⟨(Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => (key φ).1,
    (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun φ => (key φ).2⟩

/- English proof (translation)
Establish `hE' : GlRelR X.E` using `X.gl`. Use function extensionality and compare the values at `b`. Establish `key : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) • X.E d b (cminor X.E d.succAbove c.succAbove (x - 1) v) + (x * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ))) • cminor X.E b.succAbove c.succAbove (x - 1) v = (if b = c then capelliC X.E x else 0) v`. Introduce `c`. Establish `h` using `LinearMap.congr_fun (capelli_expand_plus X.E hE' x b c) v`.

Rewrite `h` using `[LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply, Module.End.mul_apply, capEntry, LinearMap.add_apply, smul_add, Finset.sum_add_distrib] at h`. Establish `h2 : ∑ z : Fin (m + 1), ((-1 : ℂ) ^ ((z : ℕ) + (c : ℕ))) • (if z = b then algebraMap ℂ (Module.End ℂ X.V) x else 0) (cminor X.E z.succAbove c.succAbove (x - 1) v) = (x * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ))) • cminor X.E b.succAbove c.succAbove (x - 1) v`. Rewrite using `[Finset.sum_eq_single b]`. Simplify using `[Module.algebraMap_end_apply, smul_smul, mul_comm]`.

Introduce `d _ hd`. Simplify using `[hd]`. Simplify using the standard rewrite rules. Rewrite `h` using `[h2]`. Conclude with `h`.

Establish `hR : y b • capelliC X.E x v = ∑ c, y c • (if b = c then capelliC X.E x else 0) v`. Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[Ne.symm hc]`.

Simplify using the standard rewrite rules. Use `show om X (nnPlus X.E y x v) b + x • nnPlus X.E y x v b = y b • capelliC X.E x v`. Rewrite using `[hR, om_apply]`. Simplify using `only [nnPlus, map_sum, map_smul, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← key c, smul_add, Finset.smul_sum]`. Simplify using `only [smul_smul]`. Rewrite using `[mul_left_comm]`.
-/
theorem om_nnPlus {m : ℕ} (X : GMod (m + 1)) (y : Fin (m + 1) → ℂ) (x : ℂ) (v : X.V) :
    om X (nnPlus X.E y x v) + x • nnPlus X.E y x v = fun b => y b • capelliC X.E x v := by
  have hE' : GlRelR X.E := X.gl
  funext b
  have key : ∀ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
      X.E d b (cminor X.E d.succAbove c.succAbove (x - 1) v) +
      (x * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ))) • cminor X.E b.succAbove c.succAbove (x - 1) v =
      (if b = c then capelliC X.E x else 0) v := by
    intro c
    have h := LinearMap.congr_fun (capelli_expand_plus X.E hE' x b c) v
    rw [LinearMap.sum_apply] at h
    simp only [LinearMap.smul_apply, Module.End.mul_apply, capEntry, LinearMap.add_apply, smul_add,
      Finset.sum_add_distrib] at h
    have h2 : ∑ z : Fin (m + 1), ((-1 : ℂ) ^ ((z : ℕ) + (c : ℕ))) •
        (if z = b then algebraMap ℂ (Module.End ℂ X.V) x else 0) (cminor X.E z.succAbove c.succAbove (x - 1) v) =
        (x * (-1 : ℂ) ^ ((b : ℕ) + (c : ℕ))) • cminor X.E b.succAbove c.succAbove (x - 1) v := by
      rw [Finset.sum_eq_single b]
      · simp [Module.algebraMap_end_apply, smul_smul, mul_comm]
      · intro d _ hd; simp [hd]
      · simp
    rw [h2] at h
    exact h
  have hR : y b • capelliC X.E x v = ∑ c, y c • (if b = c then capelliC X.E x else 0) v := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  show om X (nnPlus X.E y x v) b + x • nnPlus X.E y x v b = y b • capelliC X.E x v
  rw [hR, om_apply]
  simp only [nnPlus, map_sum, map_smul, Finset.smul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← key c, smul_add, Finset.smul_sum]
  simp only [smul_smul]
  rw [mul_left_comm]

/- English proof (translation)
Introduce `n X χ s hS hN hfree ⟨r, hrs, hr⟩`. Consider the cases of `n with`. Consider the case `zero => exact s.elim0`. Consider the case `succ m`. Establish `hE' : GlRelR X.E` using `X.gl`.

Use `set ω : ℂ := cn (m + 1) - χ s with hω`. Establish `hC : ∀ x : ℂ, capelliC X.E x = Formalism.QuantumDeterminants.capP χ (x - cn (m + 1)) • (1 : Module.End ℂ X.V)`. Introduce `x`. Establish `h` using `hS (x - cn (m + 1))`. Establish `e : x - cn (m + 1) + (((m + 1 : ℕ) : ℂ) - 1) / 2 = x` using `by simp [cn]`.

Rewrite `h` using `[e, GlobalTheory.CompanionTheory.RgExhHecke.qdetEq]`. Conclude with `h`. Use `set P : ℂ[X] := ∏ q : Fin (m + 1), (Polynomial.X + C (χ q - χ s)) with hPdef`. Establish `hPe : ∀ t : ℂ, P.eval t = Formalism.QuantumDeterminants.capP χ (ω + t - cn (m + 1))`. Introduce `t`.

Simplify using `only [hPdef, eval_prod, eval_add, eval_X, eval_C, Formalism.QuantumDeterminants.capP]`. Use `Finset.prod_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hω]`. Expand and normalize the polynomial expressions, which then agree. Establish `hPd : (Polynomial.X : ℂ[X]) ^ 2 ∣ P`.

Establish `hs : s ∈ (univ : Finset (Fin (m + 1)))` using `mem_univ s`. Establish `hr' : r ∈ (univ.erase s)` using `mem_erase.2 ⟨hrs, mem_univ r⟩`. Rewrite using `[hPdef, ← Finset.mul_prod_erase univ _ hs, ← Finset.mul_prod_erase _ _ hr', hr, sub_self, C_0, add_zero, ← mul_assoc, pow_two]`. Conclude with `Dvd.intro _ rfl`. Take `⟨v, hv⟩` from `exists_ne (0 : X.V)`.

Establish `hc1 : Formalism.QuantumDeterminants.capP χ (ω - 1 - cn (m + 1)) ≠ 0`. Simplify using `only [Formalism.QuantumDeterminants.capP]`. Use `Finset.prod_ne_zero_iff.2 fun q _ hq => hfree q ?_` and prove the remaining obligations. Rewrite `hq` using `[hω]`. Take the linear combination `hq`.

Choose the witnesses or unpack the hypotheses as in `⟨d, hd⟩ : ∃ d : Fin (m + 1), cminor X.E s.succAbove d.succAbove (ω - 1) v ≠ 0 := by`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Establish `h` using `LinearMap.congr_fun (capelli_expand_minus X.E hE' (ω - 1) s s) v`. Rewrite `h` using `[LinearMap.sum_apply, if_pos rfl, hC]`.

Apply the tactic sequence `have h0 : ∑ d : Fin (m + 1), (((-1 : ℂ) ^ ((d : ℕ) + (s : ℕ))) • (capEntry X.E (ω - 1 - (m : ℂ)) s d * cminor X.E s.succAbove d.succAbove (ω - 1))) v = 0 := Finset.sum_eq_zero fun d _ => by simp [Module.End.mul_apply, hall d]`. Rewrite `h` using `[h0]`. Establish `h1 : Formalism.QuantumDeterminants.capP χ (ω - 1 - cn (m + 1)) • v = 0` using `by simpa using h.symm`. Conclude with `(smul_ne_zero hc1 hv) h1`. Use `set y : Fin (m + 1) → ℂ := Pi.single d 1 with hy`.

Use `choose p hp using fun a b : Fin (m + 1) => isPolynomial_capelliMinor X.E a.succAbove b.succAbove (ω - 1)`. Use `set k : ℕ := (univ.sup fun ab : Fin (m + 1) × Fin (m + 1) => (p ab.1 ab.2).natDegree) + 2 with hk`. Establish `hdeg : ∀ a b, (p a b).natDegree < k` using `fun a b => by`. Use `Finset.le_sup (f := fun ab : Fin (m + 1) × Fin (m + 1) => (p ab.1 ab.2).natDegree) (mem_univ (a, b))` as an intermediate fact. Simplify using `only at this`.

Use linear arithmetic over natural numbers and integers. Use `set w : ℕ → Fin (m + 1) → X.V := fun i a => ∑ c, (y c * (-1) ^ ((a : ℕ) + (c : ℕ))) • ((p a c).coeff i) v with hw`. Establish `hexp : ∀ (a c : Fin (m + 1)) (t : ℂ), cminor X.E a.succAbove c.succAbove (ω + t - 1) v = ∑ i ∈ range k, t ^ i • ((p a c).coeff i) v`. Introduce `a c t`. Establish `e : ω + t - 1 = ω - 1 + t` using `by ring`.

Establish `hp' : cminor X.E a.succAbove c.succAbove (ω - 1 + t) = _` using `hp a c t`. Rewrite using `[e, hp', eval_eq_sum_range' (hdeg a c), LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← map_pow, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]`. Establish `hNt : ∀ t : ℂ, nnPlus X.E y (ω + t) v = ∑ i ∈ range k, t ^ i • w i`.

Introduce `t`. Use function extensionality and compare the values at `a`. Simplify using `only [nnPlus, hexp, Finset.sum_apply, Pi.smul_apply, hw, Finset.smul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => smul_comm _ _ _`.

Use `set T : Module.End ℂ (Fin (m + 1) → X.V) := om X + ω • 1 with hT`. Establish `hid : ∀ t : ℂ, T (∑ i ∈ range k, t ^ i • w i) + t • ∑ i ∈ range k, t ^ i • w i = P.eval t • (fun b => y b • v)`. Introduce `t`. Rewrite using `[← hNt]`. Establish `h` using `om_nnPlus X y (ω + t) v`.

Establish `e : T (nnPlus X.E y (ω + t) v) + t • nnPlus X.E y (ω + t) v = om X (nnPlus X.E y (ω + t) v) + (ω + t) • nnPlus X.E y (ω + t) v`. Simplify using `[hT, add_smul, add_assoc]`. Rewrite using `[e, h, hC, ← hPe]`. Use function extensionality and compare the values at `b`. Simplify using `only [LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply]`.

Conclude with `smul_comm _ _ _`. Take `⟨h0, h1⟩` from `coeff_extract T k (by omega) w P _ hPd hid`. Establish `hw0 : w 0 = nnPlus X.E y ω v`. Use `hNt 0` as an intermediate fact. Rewrite `this` using `[add_zero]`.

Rewrite using `[this, Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Simplify using `[hi]`. Introduce `h; exact absurd (mem_range.2 (by omega)) h`.

Establish `hw0ne : w 0 ≠ 0`. Introduce `h`. Rewrite `h` using `[hw0]`. Establish `h2` using `congrFun h s`. Simplify using `only [nnPlus, Pi.zero_apply] at h2`.

Rewrite `h2` using `[Finset.sum_eq_single d]`. Simplify using `[hy] at h2`. Conclude with `hd h2`. Introduce `c _ hc`. Simplify using `[hy, hc]`.

Simplify using the standard rewrite rules. Establish `hTa : ∀ f, T f = 0 ↔ om X f = (χ s - cn (m + 1)) • f`. Introduce `f`. Establish `: χ s - cn (m + 1) = -ω` using `by rw [hω]; ring`. Rewrite using `[this, hT, neg_smul, eq_neg_iff_add_eq_zero]`.

Simplify using the standard rewrite rules. Use `⟨w 1, ?_, fun h => hw0ne ?_⟩` and prove the remaining obligations. Establish `ha : χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2 = -ω` using `by rw [hω]; simp [cn] show w 1 ∈ (om X).maxGenEigenspace (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2)`. Rewrite using `[ha, Module.End.mem_maxGenEigenspace]`. Use `⟨2, ?_⟩` and prove the remaining obligations.

Establish `e : om X - (-ω) • (1 : Module.End ℂ (Fin (m + 1) → X.V)) = T` using `by simp [hT]`. Establish `e2 : T (w 1) = - w 0` using `eq_neg_of_add_eq_zero_left h1`. Rewrite using `[e, pow_two, Module.End.mul_apply, e2, map_neg, h0, neg_zero]`. Use `(hTa _).2 h` as an intermediate fact. Rewrite `h1` using `[this, zero_add]`.

Conclude with `h1`.
-/
theorem nonScal : NonScal := by
  intro n X χ s hS hN hfree ⟨r, hrs, hr⟩
  cases n with
  | zero => exact s.elim0
  | succ m =>
  have hE' : GlRelR X.E := X.gl
  set ω : ℂ := cn (m + 1) - χ s with hω

  have hC : ∀ x : ℂ, capelliC X.E x = Formalism.QuantumDeterminants.capP χ (x - cn (m + 1)) • (1 : Module.End ℂ X.V) := by
    intro x
    have h := hS (x - cn (m + 1))
    have e : x - cn (m + 1) + (((m + 1 : ℕ) : ℂ) - 1) / 2 = x := by simp [cn]
    rw [e, GlobalTheory.CompanionTheory.RgExhHecke.qdetEq] at h
    exact h

  set P : ℂ[X] := ∏ q : Fin (m + 1), (Polynomial.X + C (χ q - χ s)) with hPdef
  have hPe : ∀ t : ℂ, P.eval t = Formalism.QuantumDeterminants.capP χ (ω + t - cn (m + 1)) := by
    intro t
    simp only [hPdef, eval_prod, eval_add, eval_X, eval_C, Formalism.QuantumDeterminants.capP]
    refine Finset.prod_congr rfl fun q _ => ?_
    rw [hω]; ring
  have hPd : (Polynomial.X : ℂ[X]) ^ 2 ∣ P := by
    have hs : s ∈ (univ : Finset (Fin (m + 1))) := mem_univ s
    have hr' : r ∈ (univ.erase s) := mem_erase.2 ⟨hrs, mem_univ r⟩
    rw [hPdef, ← Finset.mul_prod_erase univ _ hs, ← Finset.mul_prod_erase _ _ hr', hr, sub_self, C_0, add_zero,
      ← mul_assoc, pow_two]
    exact Dvd.intro _ rfl

  obtain ⟨v, hv⟩ := exists_ne (0 : X.V)
  have hc1 : Formalism.QuantumDeterminants.capP χ (ω - 1 - cn (m + 1)) ≠ 0 := by
    simp only [Formalism.QuantumDeterminants.capP]
    refine Finset.prod_ne_zero_iff.2 fun q _ hq => hfree q ?_
    rw [hω] at hq
    linear_combination hq
  obtain ⟨d, hd⟩ : ∃ d : Fin (m + 1), cminor X.E s.succAbove d.succAbove (ω - 1) v ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h := LinearMap.congr_fun (capelli_expand_minus X.E hE' (ω - 1) s s) v
    rw [LinearMap.sum_apply, if_pos rfl, hC] at h
    have h0 : ∑ d : Fin (m + 1), (((-1 : ℂ) ^ ((d : ℕ) + (s : ℕ))) •
        (capEntry X.E (ω - 1 - (m : ℂ)) s d * cminor X.E s.succAbove d.succAbove (ω - 1))) v = 0 :=
      Finset.sum_eq_zero fun d _ => by simp [Module.End.mul_apply, hall d]
    rw [h0] at h
    have h1 : Formalism.QuantumDeterminants.capP χ (ω - 1 - cn (m + 1)) • v = 0 := by simpa using h.symm
    exact (smul_ne_zero hc1 hv) h1
  set y : Fin (m + 1) → ℂ := Pi.single d 1 with hy
  choose p hp using fun a b : Fin (m + 1) => isPolynomial_capelliMinor X.E a.succAbove b.succAbove (ω - 1)
  set k : ℕ := (univ.sup fun ab : Fin (m + 1) × Fin (m + 1) => (p ab.1 ab.2).natDegree) + 2 with hk
  have hdeg : ∀ a b, (p a b).natDegree < k := fun a b => by
    have := Finset.le_sup (f := fun ab : Fin (m + 1) × Fin (m + 1) => (p ab.1 ab.2).natDegree)
      (mem_univ (a, b))
    simp only at this
    omega
  set w : ℕ → Fin (m + 1) → X.V :=
    fun i a => ∑ c, (y c * (-1) ^ ((a : ℕ) + (c : ℕ))) • ((p a c).coeff i) v with hw
  have hexp : ∀ (a c : Fin (m + 1)) (t : ℂ), cminor X.E a.succAbove c.succAbove (ω + t - 1) v =
      ∑ i ∈ range k, t ^ i • ((p a c).coeff i) v := by
    intro a c t
    have e : ω + t - 1 = ω - 1 + t := by ring
    have hp' : cminor X.E a.succAbove c.succAbove (ω - 1 + t) = _ := hp a c t
    rw [e, hp', eval_eq_sum_range' (hdeg a c), LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← map_pow, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
  have hNt : ∀ t : ℂ, nnPlus X.E y (ω + t) v = ∑ i ∈ range k, t ^ i • w i := by
    intro t
    funext a
    simp only [nnPlus, hexp, Finset.sum_apply, Pi.smul_apply, hw, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => smul_comm _ _ _
  set T : Module.End ℂ (Fin (m + 1) → X.V) := om X + ω • 1 with hT
  have hid : ∀ t : ℂ, T (∑ i ∈ range k, t ^ i • w i) + t • ∑ i ∈ range k, t ^ i • w i =
      P.eval t • (fun b => y b • v) := by
    intro t
    rw [← hNt]
    have h := om_nnPlus X y (ω + t) v
    have e : T (nnPlus X.E y (ω + t) v) + t • nnPlus X.E y (ω + t) v =
        om X (nnPlus X.E y (ω + t) v) + (ω + t) • nnPlus X.E y (ω + t) v := by
      simp [hT, add_smul, add_assoc]
    rw [e, h, hC, ← hPe]
    funext b
    simp only [LinearMap.smul_apply, Module.End.one_apply, Pi.smul_apply]
    exact smul_comm _ _ _
  obtain ⟨h0, h1⟩ := coeff_extract T k (by omega) w P _ hPd hid
  have hw0 : w 0 = nnPlus X.E y ω v := by
    have := hNt 0
    rw [add_zero] at this
    rw [this, Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (mem_range.2 (by omega)) h
  have hw0ne : w 0 ≠ 0 := by
    intro h
    rw [hw0] at h
    have h2 := congrFun h s
    simp only [nnPlus, Pi.zero_apply] at h2
    rw [Finset.sum_eq_single d] at h2
    · simp [hy] at h2
      exact hd h2
    · intro c _ hc; simp [hy, hc]
    · simp
  have hTa : ∀ f, T f = 0 ↔ om X f = (χ s - cn (m + 1)) • f := by
    intro f
    have : χ s - cn (m + 1) = -ω := by rw [hω]; ring
    rw [this, hT, neg_smul, eq_neg_iff_add_eq_zero]
    simp
  refine ⟨w 1, ?_, fun h => hw0ne ?_⟩
  · have ha : χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2 = -ω := by rw [hω]; simp [cn]
    show w 1 ∈ (om X).maxGenEigenspace (χ s - (((m + 1 : ℕ) : ℂ) - 1) / 2)
    rw [ha, Module.End.mem_maxGenEigenspace]
    refine ⟨2, ?_⟩
    have e : om X - (-ω) • (1 : Module.End ℂ (Fin (m + 1) → X.V)) = T := by simp [hT]
    have e2 : T (w 1) = - w 0 := eq_neg_of_add_eq_zero_left h1
    rw [e, pow_two, Module.End.mul_apply, e2, map_neg, h0, neg_zero]
  · have := (hTa _).2 h
    rw [this, zero_add] at h1
    exact h1

end GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
