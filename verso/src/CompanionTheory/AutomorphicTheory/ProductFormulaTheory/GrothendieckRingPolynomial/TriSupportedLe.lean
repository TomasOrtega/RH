import Mathlib
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList

open MvPolynomial

namespace CompanionTheory.Groth.ChartWirtingerDerivatives

def toZAlg {σ : Type*} (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  AlgHom.mk ψ (by
    intro r
    show ψ (algebraMap ℤ (MvPolynomial σ ℤ) r) = algebraMap ℤ (MvPolynomial σ ℤ) r
    rw [algebraMap_eq, eq_intCast C r]
    exact map_intCast ψ r)

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Rewrite using `[supported_eq_adjoin_X, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Conclude with `absurd ht (by simp)`.

Consider the case `succ N ih`. Rewrite using `[supported_eq_adjoin_X, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Simplify using `only [Set.mem_ofPred_eq] at ht`. Establish `hmono : (supported ℤ {t | w t < N}).map (toZAlg ψ) ≤ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ)` using `Subalgebra.map_mono (supported_mono fun t (ht : w t < N) => (Nat.lt_succ_of_lt ht : w t < N + 1))`.

Take `⟨ε, p, hp, hψ⟩` from `h t`. Establish `hpmem : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ)`. Apply `hmono` to reduce the goal to its premises. Apply `ih` to reduce the goal to its premises. Rewrite using `[mem_supported]`.

Introduce `u hu`. Use `hp u hu` as an intermediate fact. Simplify using `only [Set.mem_ofPred_eq]`. Use linear arithmetic over natural numbers and integers. Establish `hXmem : ψ (X t) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ)` using `Subalgebra.mem_map.2 ⟨X t, (X_mem_supported).2 (by simpa using ht), rfl⟩`.

Establish `heq : (X t : MvPolynomial σ ℤ) = (ε : ℤ) • ψ (X t) - (ε : ℤ) • p`. Rewrite using `[hψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, add_sub_cancel_right]`. Rewrite using `[SetLike.mem_coe, heq]`. Conclude with `Subalgebra.sub_mem _ (Subalgebra.smul_mem _ hXmem _) (Subalgebra.smul_mem _ hpmem _)`.
-/
theorem tri_supported_le {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) (N : ℕ) :
    supported ℤ {t | w t < N} ≤ (supported ℤ {t | w t < N}).map (toZAlg ψ) := by
  induction N with
  | zero =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    exact absurd ht (by simp)
  | succ N ih =>
    rw [supported_eq_adjoin_X, Algebra.adjoin_le_iff]
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_ofPred_eq] at ht
    have hmono : (supported ℤ {t | w t < N}).map (toZAlg ψ) ≤
        (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.map_mono (supported_mono fun t (ht : w t < N) => (Nat.lt_succ_of_lt ht : w t < N + 1))
    obtain ⟨ε, p, hp, hψ⟩ := h t
    have hpmem : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) := by
      apply hmono; apply ih
      rw [mem_supported]
      intro u hu
      have := hp u hu
      simp only [Set.mem_ofPred_eq]; omega
    have hXmem : ψ (X t) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.mem_map.2 ⟨X t, (X_mem_supported).2 (by simpa using ht), rfl⟩
    have heq : (X t : MvPolynomial σ ℤ) = (ε : ℤ) • ψ (X t) - (ε : ℤ) • p := by
      rw [hψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, add_sub_cancel_right]
    rw [SetLike.mem_coe, heq]
    exact Subalgebra.sub_mem _ (Subalgebra.smul_mem _ hXmem _) (Subalgebra.smul_mem _ hpmem _)

/- English proof (translation)
Introduce `y`. Establish `hy : y ∈ supported ℤ {t | w t < y.vars.sup (fun t => w t + 1)}`. Rewrite using `[mem_supported]`. Introduce `t ht`. Use `Finset.le_sup (f := fun t => w t + 1) (Finset.mem_coe.1 ht)` as an intermediate fact.

Simplify using `only [Set.mem_ofPred_eq]`. Use linear arithmetic over natural numbers and integers. Take `⟨x, -, hx⟩` from `Subalgebra.mem_map.1 (tri_supported_le w ψ h _ hy)`. Conclude with `⟨x, hx⟩`.
-/
theorem tri_surj {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Surjective ψ := by
  intro y
  have hy : y ∈ supported ℤ {t | w t < y.vars.sup (fun t => w t + 1)} := by
    rw [mem_supported]
    intro t ht
    have := Finset.le_sup (f := fun t => w t + 1) (Finset.mem_coe.1 ht)
    simp only [Set.mem_ofPred_eq]; omega
  obtain ⟨x, -, hx⟩ := Subalgebra.mem_map.1 (tri_supported_le w ψ h _ hy)
  exact ⟨x, hx⟩

/- English proof (translation)
Use `⟨?_, tri_surj w ψ h⟩` and prove the remaining obligations. Use `choose ε p hp hψ using h`. Establish `hq : ∀ s, ∃ q : MvPolynomial σ ℤ, (∀ t ∈ q.vars, w t < w s) ∧ ψ q = -((ε s : ℤ) • p s)`. Introduce `s`. Establish `hmem : -((ε s : ℤ) • p s) ∈ supported ℤ {t | w t < w s}` using `neg_mem (Subalgebra.smul_mem _ (mem_supported.2 fun t ht => hp s t ht) _)`.

Take `⟨q, hq, hq'⟩` from `Subalgebra.mem_map.1 (tri_supported_le w ψ (fun s => ⟨ε s, p s, hp s, hψ s⟩) (w s) hmem)`. Conclude with `⟨q, fun t ht => mem_supported.1 hq ht, hq'⟩`. Use `choose q hqv hqψ using hq`. Set `g : σ → MvPolynomial σ ℤ` to `fun s => (ε s : ℤ) • X s + q s`. Set `φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ` to `(aeval g : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ).toRingHom`.

Establish `hφX : ∀ s, φ (X s) = (ε s : ℤ) • X s + q s` using `fun s => aeval_X g s`. Establish `hcomp : ∀ x, ψ (φ x) = x`. Establish `hAlg : (toZAlg ψ).comp (aeval g) = AlgHom.id ℤ (MvPolynomial σ ℤ)`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `s`.

Use `show ψ (φ (X s)) = X s`. Rewrite using `[hφX, map_add, map_zsmul, hψ, hqψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul, add_neg_cancel_right]`. Introduce `x`. Conclude with `AlgHom.congr_fun hAlg x`. Establish `hφs : Function.Surjective φ` using `tri_surj w φ fun s => ⟨ε s, q s, hqv s, hφX s⟩`.

Introduce `x y hxy`. Take `⟨a, rfl⟩` from `hφs x`. Take `⟨b, rfl⟩` from `hφs y`. Establish `hab : a = b` using `(hcomp a).symm.trans (hxy.trans (hcomp b))`. Rewrite using `[hab]`.
-/
theorem tri_bij {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Bijective ψ := by
  refine ⟨?_, tri_surj w ψ h⟩
  choose ε p hp hψ using h
  have hq : ∀ s, ∃ q : MvPolynomial σ ℤ, (∀ t ∈ q.vars, w t < w s) ∧ ψ q = -((ε s : ℤ) • p s) := by
    intro s
    have hmem : -((ε s : ℤ) • p s) ∈ supported ℤ {t | w t < w s} :=
      neg_mem (Subalgebra.smul_mem _ (mem_supported.2 fun t ht => hp s t ht) _)
    obtain ⟨q, hq, hq'⟩ := Subalgebra.mem_map.1
      (tri_supported_le w ψ (fun s => ⟨ε s, p s, hp s, hψ s⟩) (w s) hmem)
    exact ⟨q, fun t ht => mem_supported.1 hq ht, hq'⟩
  choose q hqv hqψ using hq
  let g : σ → MvPolynomial σ ℤ := fun s => (ε s : ℤ) • X s + q s
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ := (aeval g : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ).toRingHom
  have hφX : ∀ s, φ (X s) = (ε s : ℤ) • X s + q s := fun s => aeval_X g s
  have hcomp : ∀ x, ψ (φ x) = x := by
    have hAlg : (toZAlg ψ).comp (aeval g) = AlgHom.id ℤ (MvPolynomial σ ℤ) := by
      apply MvPolynomial.algHom_ext
      intro s
      show ψ (φ (X s)) = X s
      rw [hφX, map_add, map_zsmul, hψ, hqψ, smul_add, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul,
        add_neg_cancel_right]
    intro x
    exact AlgHom.congr_fun hAlg x
  have hφs : Function.Surjective φ := tri_surj w φ fun s => ⟨ε s, q s, hqv s, hφX s⟩
  intro x y hxy
  obtain ⟨a, rfl⟩ := hφs x
  obtain ⟨b, rfl⟩ := hφs y
  have hab : a = b := (hcomp a).symm.trans (hxy.trans (hcomp b))
  rw [hab]

/- English proof (translation)
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `a ha`. Assume the negation of the conclusion as `hne`. Take `⟨m0, hm0, hmin⟩` from `a.support.exists_min_image w (Finsupp.support_nonempty_iff.2 hne)`. Establish `hval` using `congrArg (fun y : I →₀ ℤ => y (L m0)) ha`.

Simplify using `only [Finsupp.linearCombination_apply, Finsupp.coe_zero, Pi.zero_apply] at hval`. Rewrite `hval` using `[Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single m0]`. Simplify using `only [Finsupp.smul_apply, h1, smul_eq_mul, mul_one] at hval`. Conclude with `(Finsupp.mem_support_iff.1 hm0) hval`. Introduce `m hm hne'`.

Simplify using `only [Finsupp.smul_apply, smul_eq_mul]`. Distinguish the cases in `hf : f m (L m0) = 0`. Simplify using `[hf]`. Break down `hlt m m0 hf with h | h` into its components or cases. Conclude with `absurd h hne'`.

Conclude with `absurd (hmin m hm) (not_le.2 h)`. Introduce `h`. Conclude with `absurd hm0 h`.
-/
theorem uni_inj {M I : Type*} (L : M ≃ I) (w : M → ℕ) (f : M → I →₀ ℤ)
    (h1 : ∀ m, f m (L m) = 1) (hlt : ∀ m n, f m (L n) ≠ 0 → m = n ∨ w m < w n) :
    Function.Injective (Finsupp.linearCombination ℤ f) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro a ha
  by_contra hne
  obtain ⟨m0, hm0, hmin⟩ := a.support.exists_min_image w (Finsupp.support_nonempty_iff.2 hne)
  have hval := congrArg (fun y : I →₀ ℤ => y (L m0)) ha
  simp only [Finsupp.linearCombination_apply, Finsupp.coe_zero, Pi.zero_apply] at hval
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single m0] at hval
  · simp only [Finsupp.smul_apply, h1, smul_eq_mul, mul_one] at hval
    exact (Finsupp.mem_support_iff.1 hm0) hval
  · intro m hm hne'
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases hf : f m (L m0) = 0
    · simp [hf]
    · rcases hlt m m0 hf with h | h
      · exact absurd h hne'
      · exact absurd (hmin m hm) (not_le.2 h)
  · intro h; exact absurd hm0 h

/- English proof (translation)
It suffices to establish `H : ∀ d n, b (c n) - w n ≤ d → ∃ a : M →₀ ℤ, a ∈ Finsupp.supported ℤ ℤ {m | c m = c n} ∧ Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 by`. Introduce `n`. Take `⟨a, ha, ha'⟩` from `H _ n le_rfl`. Conclude with `⟨a, fun m hm => (Finsupp.mem_supported _ _).1 ha hm, ha'⟩`. Introduce `d`.

Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`. Introduce `n hn`. Establish `H : ∀ i ∈ (f n).support.erase (L n), ∃ a : M →₀ ℤ, a ∈ Finsupp.supported ℤ ℤ {m | c m = c n} ∧ Finsupp.linearCombination ℤ f a = Finsupp.single i 1`. Introduce `i hi`.

Take `⟨hne, hi⟩` from `Finset.mem_erase.1 hi`. Establish `hf : f n (L (L.symm i)) ≠ 0`. Rewrite using `[L.apply_symm_apply]`. Conclude with `Finsupp.mem_support_iff.1 hi`. Take `⟨hc, hw⟩` from `hlt n (L.symm i) hf`.

Establish `hw' : w n < w (L.symm i)` using `hw.resolve_left fun h => hne (by rw [h, L.apply_symm_apply])`. Establish `hb'` using `hb (L.symm i)`. Establish `hlt' : b (c (L.symm i)) - w (L.symm i) < d`. Rewrite `hn` using `[hc]`. Use linear arithmetic over natural numbers and integers.

Take `⟨a, ha, ha'⟩` from `ih _ hlt' (L.symm i) le_rfl`. Use `⟨a, ?_, by rw [ha', L.apply_symm_apply]⟩` and prove the remaining obligations. Rewrite using `[hc]` and apply the resulting hypothesis. Use `choose! g hg hg' using H`. Use `⟨Finsupp.single n 1 - ∑ i ∈ (f n).support.erase (L n), f n i • g i, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Submodule.sub_mem _ (Finsupp.single_mem_supported ℤ _ rfl) (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hg i hi))`. Establish `hs : ∑ i ∈ (f n).support.erase (L n), Finsupp.linearCombination ℤ f (f n i • g i) = ∑ i ∈ (f n).support.erase (L n), f n i • Finsupp.single i (1 : ℤ)` using `Finset.sum_congr rfl fun i hi => by rw [map_smul, hg' i hi]`. Establish `hsplit : f n = Finsupp.single (L n) 1 + ∑ i ∈ (f n).support.erase (L n), f n i • Finsupp.single i (1 : ℤ)` using `by conv_lhs => rw [← Finsupp.sum_single (f n)]`. Rewrite using `[Finsupp.sum, ← Finset.add_sum_erase _ _ (Finsupp.mem_support_iff.2 (by rw [h1]; exact one_ne_zero)), h1]`. Repeatedly rewrite using `[Finsupp.smul_single_one]`.

Rewrite using `[map_sub, map_sum, Finsupp.linearCombination_single, one_smul, hs]`. Conclude with `(eq_sub_of_add_eq hsplit.symm).symm`.
-/
theorem uni_exists {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    ∀ n, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 := by
  classical
  suffices H : ∀ d n, b (c n) - w n ≤ d → ∃ a : M →₀ ℤ, a ∈ Finsupp.supported ℤ ℤ {m | c m = c n} ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 by
    intro n
    obtain ⟨a, ha, ha'⟩ := H _ n le_rfl
    exact ⟨a, fun m hm => (Finsupp.mem_supported _ _).1 ha hm, ha'⟩
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro n hn
  have H : ∀ i ∈ (f n).support.erase (L n), ∃ a : M →₀ ℤ,
      a ∈ Finsupp.supported ℤ ℤ {m | c m = c n} ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single i 1 := by
    intro i hi
    obtain ⟨hne, hi⟩ := Finset.mem_erase.1 hi
    have hf : f n (L (L.symm i)) ≠ 0 := by
      rw [L.apply_symm_apply]; exact Finsupp.mem_support_iff.1 hi
    obtain ⟨hc, hw⟩ := hlt n (L.symm i) hf
    have hw' : w n < w (L.symm i) :=
      hw.resolve_left fun h => hne (by rw [h, L.apply_symm_apply])
    have hb' := hb (L.symm i)
    have hlt' : b (c (L.symm i)) - w (L.symm i) < d := by
      rw [hc] at hn; omega
    obtain ⟨a, ha, ha'⟩ := ih _ hlt' (L.symm i) le_rfl
    refine ⟨a, ?_, by rw [ha', L.apply_symm_apply]⟩
    rwa [hc]
  choose! g hg hg' using H
  refine ⟨Finsupp.single n 1 - ∑ i ∈ (f n).support.erase (L n), f n i • g i, ?_, ?_⟩
  · exact Submodule.sub_mem _ (Finsupp.single_mem_supported ℤ _ rfl)
      (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ (hg i hi))
  · have hs : ∑ i ∈ (f n).support.erase (L n), Finsupp.linearCombination ℤ f (f n i • g i) =
        ∑ i ∈ (f n).support.erase (L n), f n i • Finsupp.single i (1 : ℤ) :=
      Finset.sum_congr rfl fun i hi => by rw [map_smul, hg' i hi]
    have hsplit : f n = Finsupp.single (L n) 1 +
        ∑ i ∈ (f n).support.erase (L n), f n i • Finsupp.single i (1 : ℤ) := by
      conv_lhs => rw [← Finsupp.sum_single (f n)]
      rw [Finsupp.sum, ← Finset.add_sum_erase _ _
        (Finsupp.mem_support_iff.2 (by rw [h1]; exact one_ne_zero)), h1]
      simp_rw [Finsupp.smul_single_one]
    rw [map_sub, map_sum, Finsupp.linearCombination_single, one_smul, hs]
    exact (eq_sub_of_add_eq hsplit.symm).symm

/- English proof (translation)
Use `⟨uni_inj L w f h1 fun m n h => (hlt m n h).2, ?_⟩` and prove the remaining obligations. Introduce `y`. Use `Finsupp.induction_linear y ?_ ?_ ?_` and prove the remaining obligations. Conclude with `⟨0, map_zero _⟩`. Introduce and unpack `y z ⟨a, ha⟩ ⟨a', ha'⟩`.

Conclude with `⟨a + a', by rw [map_add, ha, ha']⟩`. Introduce `i r`. Take `⟨a, -, ha⟩` from `uni_exists L c w b f hb h1 hlt (L.symm i)`. Conclude with `⟨r • a, by rw [map_smul, ha, L.apply_symm_apply, Finsupp.smul_single_one]⟩`.
-/
theorem uni_bij {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    Function.Bijective (Finsupp.linearCombination ℤ f) := by
  refine ⟨uni_inj L w f h1 fun m n h => (hlt m n h).2, ?_⟩
  intro y
  refine Finsupp.induction_linear y ?_ ?_ ?_
  · exact ⟨0, map_zero _⟩
  · rintro y z ⟨a, ha⟩ ⟨a', ha'⟩
    exact ⟨a + a', by rw [map_add, ha, ha']⟩
  · intro i r
    obtain ⟨a, -, ha⟩ := uni_exists L c w b f hb h1 hlt (L.symm i)
    exact ⟨r • a, by rw [map_smul, ha, L.apply_symm_apply, Finsupp.smul_single_one]⟩

end CompanionTheory.Groth.ChartWirtingerDerivatives

namespace CompanionTheory.Groth

/- English proof (translation)
Introduce `_ w ψ h` and use `ChartWirtingerDerivatives.tri_bij w ψ h`.
-/
theorem triAut : TriAut := fun _ w ψ h => ChartWirtingerDerivatives.tri_bij w ψ h

/- English proof (translation)
Introduce `_ _ _ L c w b f hb h1 hlt` and use `⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩`.
-/
theorem uniTri : UniTri := fun _ _ _ L c w b f hb h1 hlt =>
  ⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩

end CompanionTheory.Groth
