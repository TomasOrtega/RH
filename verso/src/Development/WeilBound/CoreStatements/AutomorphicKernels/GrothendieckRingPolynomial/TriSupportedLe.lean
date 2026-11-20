import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList

open MvPolynomial

namespace PositivityTheory.Groth.ChartWirtingerDerivatives

def toZAlg {σ : Type*} (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ) :
    MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  AlgHom.mk ψ (by
    intro r
    show ψ (algebraMap ℤ (MvPolynomial σ ℤ) r) = algebraMap ℤ (MvPolynomial σ ℤ) r
    rw [algebraMap_eq, eq_intCast C r]
    exact map_intCast ψ r)

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Introduce `x hx`. Establish `he : {t | w t < 0} = (∅ : Set σ)`. Use extensionality with `t`.

Simplify using the standard rewrite rules. Rewrite `hx` using `[he, supported_empty]`. Take `⟨r, rfl⟩` from `Algebra.mem_bot.1 hx`. Conclude with `Subalgebra.algebraMap_mem _ r`. Consider the case `succ N ih`.

Introduce `x hx`. Rewrite `hx` using `[supported_eq_adjoin_X]`. Use `Algebra.adjoin_le ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Take `⟨ε, p, hp, hψ⟩` from `h s`.

Establish `hs' : w s < N + 1` using `hs`. Establish `hXs : X s ∈ supported ℤ {t | w t < N + 1}` using `X_mem_supported.2 hs`. Establish `h1 : ψ (X s) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ)` using `Subalgebra.mem_map.2 ⟨X s, hXs, rfl⟩`. Establish `h2 : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ)`. Establish `hp' : p ∈ supported ℤ {t | w t < N}`.

Rewrite using `[mem_supported]`. Introduce `t ht`. Use `hp t ht` as an intermediate fact. Use `show w t < N`. Use linear arithmetic over natural numbers and integers.

Use `Subalgebra.map_mono (supported_mono ?_) (ih hp')` and prove the remaining obligations. Introduce `t ht`. Establish `ht' : w t < N` using `ht`. Use `show w t < N + 1`. Use linear arithmetic over natural numbers and integers.

Establish `key : X s = ((ε⁻¹ : ℤˣ) : ℤ) • (ψ (X s) - p)`. Rewrite using `[hψ, add_sub_cancel_right, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]`. Rewrite using `[key]`. Conclude with `Subalgebra.smul_mem _ (Subalgebra.sub_mem _ h1 h2) _`.
-/
theorem tri_supported_le {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) (N : ℕ) :
    supported ℤ {t | w t < N} ≤ (supported ℤ {t | w t < N}).map (toZAlg ψ) := by
  induction N with
  | zero =>
    intro x hx
    have he : {t | w t < 0} = (∅ : Set σ) := by
      ext t
      simp
    rw [he, supported_empty] at hx
    obtain ⟨r, rfl⟩ := Algebra.mem_bot.1 hx
    exact Subalgebra.algebraMap_mem _ r
  | succ N ih =>
    intro x hx
    rw [supported_eq_adjoin_X] at hx
    refine Algebra.adjoin_le ?_ hx
    rintro _ ⟨s, hs, rfl⟩
    obtain ⟨ε, p, hp, hψ⟩ := h s
    have hs' : w s < N + 1 := hs
    have hXs : X s ∈ supported ℤ {t | w t < N + 1} := X_mem_supported.2 hs
    have h1 : ψ (X s) ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) :=
      Subalgebra.mem_map.2 ⟨X s, hXs, rfl⟩
    have h2 : p ∈ (supported ℤ {t | w t < N + 1}).map (toZAlg ψ) := by
      have hp' : p ∈ supported ℤ {t | w t < N} := by
        rw [mem_supported]
        intro t ht
        have := hp t ht
        show w t < N
        omega
      refine Subalgebra.map_mono (supported_mono ?_) (ih hp')
      intro t ht
      have ht' : w t < N := ht
      show w t < N + 1
      omega
    have key : X s = ((ε⁻¹ : ℤˣ) : ℤ) • (ψ (X s) - p) := by
      rw [hψ, add_sub_cancel_right, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    rw [key]
    exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ h1 h2) _

/- English proof (translation)
Establish `hrange : ∀ s, X s ∈ (toZAlg ψ).range`. Introduce `s`. Establish `hmem` using `tri_supported_le w ψ h (w s + 1) (X_mem_supported.2 (show w s < w s + 1 by omega))`. Take `⟨y, -, hy⟩` from `Subalgebra.mem_map.1 hmem`. Conclude with `(AlgHom.mem_range _).2 ⟨y, hy⟩`.

Establish `htop : (toZAlg ψ).range = ⊤`. Rewrite using `[eq_top_iff, ← adjoin_range_X, Algebra.adjoin_le_iff]`. Introduce and unpack `_ ⟨s, rfl⟩`. Conclude with `hrange s`. Introduce `y`.

Establish `hy : y ∈ (toZAlg ψ).range`. Rewrite using `[htop]`. Conclude with `Algebra.mem_top`. Take `⟨x, hx⟩` from `(AlgHom.mem_range _).1 hy`. Conclude with `⟨x, hx⟩`.
-/
theorem tri_surj {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Surjective ψ := by
  have hrange : ∀ s, X s ∈ (toZAlg ψ).range := by
    intro s
    have hmem := tri_supported_le w ψ h (w s + 1)
      (X_mem_supported.2 (show w s < w s + 1 by omega))
    obtain ⟨y, -, hy⟩ := Subalgebra.mem_map.1 hmem
    exact (AlgHom.mem_range _).2 ⟨y, hy⟩
  have htop : (toZAlg ψ).range = ⊤ := by
    rw [eq_top_iff, ← adjoin_range_X, Algebra.adjoin_le_iff]
    rintro _ ⟨s, rfl⟩
    exact hrange s
  intro y
  have hy : y ∈ (toZAlg ψ).range := by
    rw [htop]
    exact Algebra.mem_top
  obtain ⟨x, hx⟩ := (AlgHom.mem_range _).1 hy
  exact ⟨x, hx⟩

/- English proof (translation)
Use `⟨?_, tri_surj w ψ h⟩` and prove the remaining obligations. Establish `hpre : ∀ s, ∃ (ε : ℤˣ) (q : MvPolynomial σ ℤ), (∀ t ∈ q.vars, w t < w s) ∧ ψ ((ε : ℤ) • X s + q) = X s`. Introduce `s`. Take `⟨ε, p, hp, hψ⟩` from `h s`. Establish `hp' : ((ε⁻¹ : ℤˣ) : ℤ) • p ∈ supported ℤ {t | w t < w s}`.

Apply `Subalgebra.smul_mem` to reduce the goal to its premises. Rewrite using `[mem_supported]`. Introduce `t ht`. Conclude with `hp t ht`. Take `⟨q, hq, hqe⟩` from `Subalgebra.mem_map.1 (tri_supported_le w ψ h (w s) hp')`.

Use `⟨ε⁻¹, -q, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Rewrite `ht` using `[vars_neg]`. Conclude with `(mem_supported.1 hq) (Finset.mem_coe.2 ht)`. Establish `hqe' : ψ q = ((ε⁻¹ : ℤˣ) : ℤ) • p` using `hqe`.

Rewrite using `[map_add, map_neg, map_zsmul, hψ, hqe', smul_add, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul, add_neg_cancel_right]`. Use `choose ε' q hq hψq using hpre`. Set `φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ` to `(aeval fun s => ((ε' s : ℤˣ) : ℤ) • X s + q s).toRingHom`. Establish `hφX : ∀ s, φ (X s) = ((ε' s : ℤˣ) : ℤ) • X s + q s` using `fun s => aeval_X _ _`. Establish `hφs : Function.Surjective φ` using `tri_surj w φ (fun s => ⟨ε' s, q s, hq s, hφX s⟩)`.

Establish `hcomp : ∀ a, ψ (φ a) = a`. Establish `hc : ψ.comp φ = RingHom.id _`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r show ψ (φ (C r)) = C r`. Simplify using `only [eq_intCast C r, map_intCast]`.

Introduce `s show ψ (φ (X s)) = X s`. Rewrite using `[hφX]`. Conclude with `hψq s`. Introduce `a`. Rewrite using `[← RingHom.comp_apply, hc, RingHom.id_apply]`.

Introduce `a b hab`. Take `⟨a', rfl⟩` from `hφs a`. Take `⟨b', rfl⟩` from `hφs b`. Rewrite `hab` using `[hcomp, hcomp]`. Rewrite using `[hab]`.
-/
theorem tri_bij {σ : Type*} (w : σ → ℕ) (ψ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ)
    (h : ∀ s, ∃ (ε : ℤˣ) (p : MvPolynomial σ ℤ), (∀ t ∈ p.vars, w t < w s) ∧
      ψ (X s) = (ε : ℤ) • X s + p) : Function.Bijective ψ := by
  refine ⟨?_, tri_surj w ψ h⟩
  have hpre : ∀ s, ∃ (ε : ℤˣ) (q : MvPolynomial σ ℤ), (∀ t ∈ q.vars, w t < w s) ∧
      ψ ((ε : ℤ) • X s + q) = X s := by
    intro s
    obtain ⟨ε, p, hp, hψ⟩ := h s
    have hp' : ((ε⁻¹ : ℤˣ) : ℤ) • p ∈ supported ℤ {t | w t < w s} := by
      apply Subalgebra.smul_mem
      rw [mem_supported]
      intro t ht
      exact hp t ht
    obtain ⟨q, hq, hqe⟩ := Subalgebra.mem_map.1 (tri_supported_le w ψ h (w s) hp')
    refine ⟨ε⁻¹, -q, ?_, ?_⟩
    · intro t ht
      rw [vars_neg] at ht
      exact (mem_supported.1 hq) (Finset.mem_coe.2 ht)
    · have hqe' : ψ q = ((ε⁻¹ : ℤˣ) : ℤ) • p := hqe
      rw [map_add, map_neg, map_zsmul, hψ, hqe', smul_add, smul_smul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_smul, add_neg_cancel_right]
  choose ε' q hq hψq using hpre
  let φ : MvPolynomial σ ℤ →+* MvPolynomial σ ℤ :=
    (aeval fun s => ((ε' s : ℤˣ) : ℤ) • X s + q s).toRingHom
  have hφX : ∀ s, φ (X s) = ((ε' s : ℤˣ) : ℤ) • X s + q s := fun s => aeval_X _ _
  have hφs : Function.Surjective φ := tri_surj w φ (fun s => ⟨ε' s, q s, hq s, hφX s⟩)
  have hcomp : ∀ a, ψ (φ a) = a := by
    have hc : ψ.comp φ = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show ψ (φ (C r)) = C r
        simp only [eq_intCast C r, map_intCast]
      · intro s
        show ψ (φ (X s)) = X s
        rw [hφX]
        exact hψq s
    intro a
    rw [← RingHom.comp_apply, hc, RingHom.id_apply]
  intro a b hab
  obtain ⟨a', rfl⟩ := hφs a
  obtain ⟨b', rfl⟩ := hφs b
  rw [hcomp, hcomp] at hab
  rw [hab]

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `a ha`. Assume the negation of the conclusion as `hne`. Establish `hsupp : a.support.Nonempty` using `Finsupp.support_nonempty_iff.2 hne`. Take `⟨n, hn, hmin⟩` from `a.support.exists_min_image w hsupp`.

Establish `hcoef` using `congrArg (fun g => g (L n)) ha`. Simplify using `only [Finsupp.linearCombination_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoef`. Rewrite `hcoef` using `[Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single n]`. Simplify using `only [Finsupp.smul_apply, h1, smul_eq_mul, mul_one] at hcoef`. Conclude with `(Finsupp.mem_support_iff.1 hn) hcoef`.

Introduce `m hm hmn`. Simplify using `only [Finsupp.smul_apply, smul_eq_mul]`. Distinguish the cases in `hf : f m (L n) = 0`. Simplify using `[hf]`. Break down `hlt m n hf with h | h` into its components or cases.

Conclude with `absurd h hmn`. Conclude with `absurd (hmin m hm) (not_le.2 h)`. Introduce `hn'`. Conclude with `absurd hn hn'`.
-/
theorem uni_inj {M I : Type*} (L : M ≃ I) (w : M → ℕ) (f : M → I →₀ ℤ)
    (h1 : ∀ m, f m (L m) = 1) (hlt : ∀ m n, f m (L n) ≠ 0 → m = n ∨ w m < w n) :
    Function.Injective (Finsupp.linearCombination ℤ f) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  have hsupp : a.support.Nonempty := Finsupp.support_nonempty_iff.2 hne
  obtain ⟨n, hn, hmin⟩ := a.support.exists_min_image w hsupp
  have hcoef := congrArg (fun g => g (L n)) ha
  simp only [Finsupp.linearCombination_apply, Finsupp.coe_zero, Pi.zero_apply] at hcoef
  rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single n] at hcoef
  · simp only [Finsupp.smul_apply, h1, smul_eq_mul, mul_one] at hcoef
    exact (Finsupp.mem_support_iff.1 hn) hcoef
  · intro m hm hmn
    simp only [Finsupp.smul_apply, smul_eq_mul]
    by_cases hf : f m (L n) = 0
    · simp [hf]
    · rcases hlt m n hf with h | h
      · exact absurd h hmn
      · exact absurd (hmin m hm) (not_le.2 h)
  · intro hn'
    exact absurd hn hn'

/- English proof (translation)
Introduce `n`. It suffices to establish `key : ∀ d n, b (c n) - w n = d → ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧ Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 from key _ n rfl`. Introduce `d`. Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d ih`.

Introduce `n hd`. Use `set v : I →₀ ℤ := Finsupp.single (L n) 1 - f n with hv`. Establish `hvsupp : ∀ i ∈ v.support, c (L.symm i) = c n ∧ b (c (L.symm i)) - w (L.symm i) < d`. Introduce `i hi`. Establish `hvi : v i ≠ 0` using `Finsupp.mem_support_iff.1 hi`.

Use `set m := L.symm i with hm`. Establish `hi' : i = L m` using `by rw [hm, Equiv.apply_symm_apply]`. Establish `hne : m ≠ n`. Introduce `hmn`. Apply `hvi` to reduce the goal to its premises.

Rewrite using `[hi', hmn, hv, Finsupp.sub_apply, Finsupp.single_eq_same, h1, sub_self]`. Establish `hf : f n (L m) ≠ 0`. Introduce `hf0`. Apply `hvi` to reduce the goal to its premises. Rewrite using `[hi', hv, Finsupp.sub_apply, hf0, sub_zero, Finsupp.single_apply, if_neg]`.

Introduce `heq`. Conclude with `hne (L.injective heq).symm`. Take `⟨hc, hw⟩` from `hlt n m hf`. Break down `hw with hw | hw` into its components or cases. Conclude with `absurd hw.symm hne`.

Use `⟨hc.symm, ?_⟩` and prove the remaining obligations. Establish `hbm` using `hb m`. Rewrite `hbm`, the goal using `[← hc]`. Use linear arithmetic over natural numbers and integers. Establish `hex : ∀ i ∈ v.support, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧ Finsupp.linearCombination ℤ f a = Finsupp.single i 1`.

Introduce `i hi`. Take `⟨hc, hlt'⟩` from `hvsupp i hi`. Take `⟨a, ha1, ha2⟩` from `ih _ hlt' (L.symm i) rfl`. Use `⟨a, fun m hm => (ha1 m hm).trans hc, ?_⟩` and prove the remaining obligations. Rewrite using `[ha2, Equiv.apply_symm_apply]`.

Use `choose! g hg1 hg2 using hex`. Use `⟨Finsupp.single n 1 + ∑ i ∈ v.support, v i • g i, ?_, ?_⟩` and prove the remaining obligations. Introduce `m hm`. Break down `Finset.mem_union.1 (Finsupp.support_add hm) with hm1 | hm1` into its components or cases. Rewrite `hm1` using `[Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]`.

Rewrite using `[hm1]`. Take `⟨i, hi, hmi⟩` from `Finset.mem_biUnion.1 (Finsupp.support_finset_sum hm1)`. Conclude with `hg1 i hi m (Finsupp.support_smul hmi)`. Rewrite using `[map_add, map_sum, Finsupp.linearCombination_single, one_smul]`. Rewrite using `[Finset.sum_congr rfl (fun i hi => by rw [map_smul, hg2 i hi])]`.

Establish `hsum : ∑ i ∈ v.support, v i • Finsupp.single i (1 : ℤ) = v` using `by conv_rhs => rw [← Finsupp.sum_single v]`. Rewrite using `[Finsupp.sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Finsupp.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[hsum, hv]`.

Normalize the expressions using the abelian group laws.
-/
theorem uni_exists {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    ∀ n, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 := by
  classical
  intro n
  suffices key : ∀ d n, b (c n) - w n = d → ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
      Finsupp.linearCombination ℤ f a = Finsupp.single (L n) 1 from key _ n rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro n hd
    set v : I →₀ ℤ := Finsupp.single (L n) 1 - f n with hv
    have hvsupp : ∀ i ∈ v.support, c (L.symm i) = c n ∧
        b (c (L.symm i)) - w (L.symm i) < d := by
      intro i hi
      have hvi : v i ≠ 0 := Finsupp.mem_support_iff.1 hi
      set m := L.symm i with hm
      have hi' : i = L m := by rw [hm, Equiv.apply_symm_apply]
      have hne : m ≠ n := by
        intro hmn
        apply hvi
        rw [hi', hmn, hv, Finsupp.sub_apply, Finsupp.single_eq_same, h1, sub_self]
      have hf : f n (L m) ≠ 0 := by
        intro hf0
        apply hvi
        rw [hi', hv, Finsupp.sub_apply, hf0, sub_zero, Finsupp.single_apply, if_neg]
        intro heq
        exact hne (L.injective heq).symm
      obtain ⟨hc, hw⟩ := hlt n m hf
      rcases hw with hw | hw
      · exact absurd hw.symm hne
      · refine ⟨hc.symm, ?_⟩
        have hbm := hb m
        rw [← hc] at hbm ⊢
        omega
    have hex : ∀ i ∈ v.support, ∃ a : M →₀ ℤ, (∀ m ∈ a.support, c m = c n) ∧
        Finsupp.linearCombination ℤ f a = Finsupp.single i 1 := by
      intro i hi
      obtain ⟨hc, hlt'⟩ := hvsupp i hi
      obtain ⟨a, ha1, ha2⟩ := ih _ hlt' (L.symm i) rfl
      refine ⟨a, fun m hm => (ha1 m hm).trans hc, ?_⟩
      rw [ha2, Equiv.apply_symm_apply]
    choose! g hg1 hg2 using hex
    refine ⟨Finsupp.single n 1 + ∑ i ∈ v.support, v i • g i, ?_, ?_⟩
    · intro m hm
      rcases Finset.mem_union.1 (Finsupp.support_add hm) with hm1 | hm1
      · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hm1
        rw [hm1]
      · obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hm1)
        exact hg1 i hi m (Finsupp.support_smul hmi)
    · rw [map_add, map_sum, Finsupp.linearCombination_single, one_smul]
      rw [Finset.sum_congr rfl (fun i hi => by rw [map_smul, hg2 i hi])]
      have hsum : ∑ i ∈ v.support, v i • Finsupp.single i (1 : ℤ) = v := by
        conv_rhs => rw [← Finsupp.sum_single v]
        rw [Finsupp.sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsum, hv]
      abel

/- English proof (translation)
Use `⟨uni_inj L w f h1 (fun m n hf => (hlt m n hf).2), ?_⟩` and prove the remaining obligations. Establish `hrange : ∀ i, Finsupp.single i (1 : ℤ) ∈ LinearMap.range (Finsupp.linearCombination ℤ f)`. Introduce `i`. Take `⟨a, -, ha⟩` from `uni_exists L c w b f hb h1 hlt (L.symm i)`. Rewrite `ha` using `[Equiv.apply_symm_apply]`.

Conclude with `LinearMap.mem_range.2 ⟨a, ha⟩`. Introduce `g`. Establish `hg : g ∈ LinearMap.range (Finsupp.linearCombination ℤ f)`. Use `Finsupp.induction_linear g ?_ ?_ ?_` and prove the remaining obligations. Conclude with `Submodule.zero_mem _`.

Introduce `x y hx hy`. Conclude with `Submodule.add_mem _ hx hy`. Introduce `i r`. Establish `hmem` using `Submodule.smul_mem _ r (hrange i)`. Rewrite `hmem` using `[Finsupp.smul_single, smul_eq_mul, mul_one]`. Then use the resulting hypothesis.

Conclude with `LinearMap.mem_range.1 hg`.
-/
theorem uni_bij {M I C : Type*} (L : M ≃ I) (c : M → C) (w : M → ℕ) (b : C → ℕ) (f : M → I →₀ ℤ)
    (hb : ∀ m, w m ≤ b (c m)) (h1 : ∀ m, f m (L m) = 1)
    (hlt : ∀ m n, f m (L n) ≠ 0 → c m = c n ∧ (m = n ∨ w m < w n)) :
    Function.Bijective (Finsupp.linearCombination ℤ f) := by
  refine ⟨uni_inj L w f h1 (fun m n hf => (hlt m n hf).2), ?_⟩
  have hrange : ∀ i, Finsupp.single i (1 : ℤ) ∈ LinearMap.range (Finsupp.linearCombination ℤ f) := by
    intro i
    obtain ⟨a, -, ha⟩ := uni_exists L c w b f hb h1 hlt (L.symm i)
    rw [Equiv.apply_symm_apply] at ha
    exact LinearMap.mem_range.2 ⟨a, ha⟩
  intro g
  have hg : g ∈ LinearMap.range (Finsupp.linearCombination ℤ f) := by
    refine Finsupp.induction_linear g ?_ ?_ ?_
    · exact Submodule.zero_mem _
    · intro x y hx hy
      exact Submodule.add_mem _ hx hy
    · intro i r
      have hmem := Submodule.smul_mem _ r (hrange i)
      rwa [Finsupp.smul_single, smul_eq_mul, mul_one] at hmem
  exact LinearMap.mem_range.1 hg

end PositivityTheory.Groth.ChartWirtingerDerivatives

namespace PositivityTheory.Groth

/- English proof (translation)
Introduce `_ w ψ h` and use `ChartWirtingerDerivatives.tri_bij w ψ h`.
-/
theorem triAut : TriAut := fun _ w ψ h => ChartWirtingerDerivatives.tri_bij w ψ h

/- English proof (translation)
Introduce `_ _ _ L c w b f hb h1 hlt` and use `⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩`.
-/
theorem uniTri : UniTri := fun _ _ _ L c w b f hb h1 hlt =>
  ⟨ChartWirtingerDerivatives.uni_bij L c w b f hb h1 hlt, ChartWirtingerDerivatives.uni_exists L c w b f hb h1 hlt⟩

end PositivityTheory.Groth
