import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogResolutionReindexed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogRelationRatioReindex
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UnitRatioDivisorSupportEq
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.MemMCoordIdealOfAevalEqZero

noncomputable section

namespace RootFieldNumerics.Ref.Zeros

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open GlobalTheory.CompanionTheory.Ar.Chg GlobalTheory.CompanionTheory.Ar.Chg.DegBlock
open GroundTheory.Heights₂.Heights.LowerBoundFree (mem_mCoordIdeal_of_aeval_eq_zero)
open GlobalTheory.CompanionTheory.Ar.Giv (aeval_eq_zero_of_mem_mCoordIdeal)

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type} [∀ k, Fintype (J₀ k)]
  [∀ k, Fintype (J k)]

/- English proof (translation)
Introduce `m hm k`. Break down `Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hf m h k`. Conclude with `hg m h k`.
-/
theorem homog_add {f g : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

/- English proof (translation)
Introduce `m hm k`. Rewrite `hm` using `[MvPolynomial.support_neg]`. Conclude with `hf m hm k`.
-/
theorem homog_neg {f : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing J) a := by
  intro m hm
  simp at hm

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using homog_zero a`. Consider the case `insert x s hx ih`. Rewrite using `[Finset.sum_insert hx]`. Conclude with `homog_add (h x (Finset.mem_insert_self x s)) (ih fun u hu => h u (Finset.mem_insert_of_mem hu))`.
-/
theorem homog_sum {X : Type} (s : Finset X) {f : X → MRing J} {a : K → ℕ} (h : ∀ x ∈ s, IsMultiHomog (f x) a) :
    IsMultiHomog (∑ x ∈ s, f x) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_zero a
  | insert x s hx ih =>
    rw [Finset.sum_insert hx]
    exact homog_add (h x (Finset.mem_insert_self x s)) (ih fun u hu => h u (Finset.mem_insert_of_mem hu))

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using (isMultiHomog_one' (J₀ := J))`. Consider the case `succ n ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `isMultiHomog_mul' ih hf`.
-/
theorem homog_pow {f : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) : IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (isMultiHomog_one' (J₀ := J))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul' ih hf

/- English proof (translation)
Introduce `m hm k'`. Rewrite `hm` using `[MvPolynomial.support_X, Finset.mem_singleton]`. Substitute `hm` using the available equality. Distinguish the cases in `h : k' = k`. Substitute `h` using the available equality.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `e`.

Conclude with `hb (eq_of_heq (Sigma.mk.inj e).2).symm`. Simplify using the standard rewrite rules. Rewrite using `[Pi.single_eq_of_ne h]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply, if_neg]`.

Introduce `e`. Conclude with `h (Sigma.mk.inj e).1.symm`.
-/
theorem homog_X [DecidableEq K] (k : K) (i : J k) : IsMultiHomog (X ⟨k, i⟩ : MRing J) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact hb (eq_of_heq (Sigma.mk.inj e).2).symm
    · simp
  · rw [Pi.single_eq_of_ne h]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro e
    exact h (Sigma.mk.inj e).1.symm

/- English proof (translation)
Establish `h` using `isMultiHomog_prod' (J₀ := J) Finset.univ (f := fun k => (X ⟨k, c k⟩ : MRing J) ^ a k) (a := fun k => a k • Pi.single k 1) fun k _ => homog_pow (homog_X k (c k)) (a k)`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.
-/
theorem homog_mono (c : ∀ k, J k) (a : K → ℕ) : IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing J) ^ a k) a := by
  classical
  have h := isMultiHomog_prod' (J₀ := J) Finset.univ (f := fun k => (X ⟨k, c k⟩ : MRing J) ^ a k)
    (a := fun k => a k • Pi.single k 1) fun k _ => homog_pow (homog_X k (c k)) (a k)
  convert h using 1
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

/- English proof (translation)
Establish `hq : ∀ k (i : J₀ k), ∃ i' : J (κ k), v ⟨k, i⟩ = ⟨κ k, i'⟩`. Introduce `k i`. Establish `h1` using `hv.2.2.1 ⟨k, i⟩`. Generalize the expression as in `v ⟨k, i⟩ = q at h1`. Take `⟨q1, q2⟩` from `q`.

Simplify using `only at h1`. Substitute `h1` using the available equality. Conclude with `⟨q2, rfl⟩`. Use `choose g hg using hq`. Establish `hb : ∀ k, Function.Bijective (g k)`.

Introduce `k`. Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Establish `: v ⟨k, a⟩ = v ⟨k, b⟩` using `by rw [hg, hg, hab]`. Conclude with `eq_of_heq (Sigma.mk.inj (hv.2.1 this)).2`.

Introduce `i'`. Take `⟨p, hp⟩` from `hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩`. Establish `h1 : κ p.1 = κ k` using `by rw [← hv.2.2.1 p, hp]`. Take `⟨k₁, i⟩` from `p`. Take `rfl : k₁ = k` from `hv.1 h1`.

Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite `hp` using `[hg]`. Conclude with `eq_of_heq (Sigma.mk.inj hp).2`. Use `⟨fun k => Equiv.ofBijective (g k) (hb k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Take `⟨k, i⟩` from `p`. Conclude with `hg k i`.
-/
theorem exists_blkV {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) :
    ∃ bx : ∀ k, J₀ k ≃ J (κ k), v = blkV κ bx := by
  have hq : ∀ k (i : J₀ k), ∃ i' : J (κ k), v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
    intro k i
    have h1 := hv.2.2.1 ⟨k, i⟩
    generalize v ⟨k, i⟩ = q at h1
    obtain ⟨q1, q2⟩ := q
    simp only at h1
    subst h1
    exact ⟨q2, rfl⟩
  choose g hg using hq
  have hb : ∀ k, Function.Bijective (g k) := by
    intro k
    constructor
    · intro a b hab
      have : v ⟨k, a⟩ = v ⟨k, b⟩ := by rw [hg, hg, hab]
      exact eq_of_heq (Sigma.mk.inj (hv.2.1 this)).2
    · intro i'
      obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
      have h1 : κ p.1 = κ k := by rw [← hv.2.2.1 p, hp]
      obtain ⟨k₁, i⟩ := p
      obtain rfl : k₁ = k := hv.1 h1
      refine ⟨i, ?_⟩
      rw [hg] at hp
      exact eq_of_heq (Sigma.mk.inj hp).2
  refine ⟨fun k => Equiv.ofBijective (g k) (hb k), ?_⟩
  funext p
  obtain ⟨k, i⟩ := p
  exact hg k i

/- English proof (translation)
Use `choose d g h hg hh h0 he using fun j => hB (b j)`. Use `⟨fun j => g j * ∏ k ∈ (Finset.range n).erase j, h k, ∑ k ∈ Finset.range n, d k, ∏ k ∈ Finset.range n, aeval y₀ (h k), Finset.prod_ne_zero_iff.2 fun k _ => h0 k, fun j hj => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← Finset.add_sum_erase _ _ hj]`. Conclude with `isMultiHomog_mul' (hg j) (isMultiHomog_prod' _ fun k _ => hh k)`. Rewrite using `[← Finset.mul_prod_erase _ _ hj, map_mul, map_prod, he, mul_assoc]`.
-/
theorem common_den {Ω₀ : Type} [Field Ω₀] (y₀ : (Σ k, J₀ k) → Ω₀) (hB : Birational y₀) (b : ℕ → Ω₀) (n : ℕ) :
    ∃ (c : ℕ → MRing J₀) (a : K₀ → ℕ) (H : Ω₀), H ≠ 0 ∧ ∀ j ∈ Finset.range n,
      IsMultiHomog (c j) a ∧ aeval y₀ (c j) = b j * H := by
  classical
  choose d g h hg hh h0 he using fun j => hB (b j)
  refine ⟨fun j => g j * ∏ k ∈ (Finset.range n).erase j, h k, ∑ k ∈ Finset.range n, d k,
    ∏ k ∈ Finset.range n, aeval y₀ (h k), Finset.prod_ne_zero_iff.2 fun k _ => h0 k, fun j hj => ⟨?_, ?_⟩⟩
  · rw [← Finset.add_sum_erase _ _ hj]
    exact isMultiHomog_mul' (hg j) (isMultiHomog_prod' _ fun k _ => hh k)
  · rw [← Finset.mul_prod_erase _ _ hj, map_mul, map_prod, he, mul_assoc]

/- English proof (translation)
Use `letI := i.toAlgebra`. Establish `hFy : aeval y F ≠ 0` using `fun h => hFP (mem_mCoordIdeal_of_aeval_eq_zero y hF h)`. Establish `hren : ∀ g : MRing J₀, aeval y (rename v g) = i (aeval y₀ g)`. Introduce `g`. Rewrite using `[aeval_rename, ← GlobalTheory.CompanionTheory.Ar.Rel.aeval_comp_ringHom i y₀ g]`.

Use `congr 2`. Use function extensionality and compare the values at `p`. Conclude with `hy p`. Establish `key : ∀ c : ∀ k, J k, ∃ (G : MRing J₀) (b : K₀ → ℕ), IsMultiHomog G b ∧ aeval y₀ G ≠ 0 ∧ ∀ z ∈ mcPts (mCoordIdeal y), (∀ k, z ⟨k, c k⟩ ≠ 0) → eval z (map (Int.castRingHom ℂ) F) = 0 → eval (fun p => z (v p)) (map (Int.castRingHom ℂ) G) = 0`. Introduce `c`.

Distinguish the cases in `hc : ∀ k, y ⟨k, c k⟩ ≠ 0`. Set `M : MRing J` to `∏ k, (X ⟨k, c k⟩ : MRing J) ^ aF k`. Establish `hM : IsMultiHomog M aF` using `homog_mono c aF`. Establish `hMy : aeval y M ≠ 0`. Simplify using `only [M, map_prod, map_pow, aeval_X]`.

Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)`. Use `set α : Ω := aeval y F / aeval y M with hα`. Establish `hα0 : α ≠ 0` using `div_ne_zero hFy hMy`. Establish `hint : IsIntegral Ω₀ α` using `(halg α).isIntegral`. Use `set p := minpoly Ω₀ α with hp`.

Establish `hp0 : p.coeff 0 ≠ 0` using `minpoly.coeff_zero_ne_zero hint hα0`. Establish `hpa : Polynomial.aeval α p = 0` using `minpoly.aeval Ω₀ α`. Rewrite `hpa` using `[Polynomial.aeval_eq_sum_range]`. Use `set n := p.natDegree`. Take `⟨cc, a, H, hH, hcc⟩` from `common_den y₀ hB (fun j => p.coeff j) (n + 1)`.

Establish `h0n : 0 ∈ Finset.range (n + 1)` using `by simp`. Use `⟨cc 0, a, (hcc 0 h0n).1, by rw [(hcc 0 h0n).2]; exact mul_ne_zero hp0 hH, ?_⟩` and prove the remaining obligations. Introduce `z hz hzc hFz`. Set `Φ : MRing J` to `∑ j ∈ Finset.range (n + 1), rename v (cc j) * F ^ j * M ^ (n - j)`. Establish `hΦh : IsMultiHomog Φ (Function.extend κ a 0 + n • aF)`.

Use `homog_sum _ fun j hj => ?_` and prove the remaining obligations. Establish `hjn : j ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`. Establish `h1` using `isMultiHomog_mul' (isMultiHomog_mul' (isMultiHomog_rename' hv (hcc j hj).1) (homog_pow hF j)) (homog_pow hM (n - j))`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[add_assoc, ← add_nsmul, Nat.add_sub_cancel' hjn]`.

Establish `hΦy : aeval y Φ = 0`. Establish `hterm : ∀ j ∈ Finset.range (n + 1), aeval y (rename v (cc j) * F ^ j * M ^ (n - j)) = (i H * aeval y M ^ n) * (p.coeff j • α ^ j)`. Introduce `j hj`. Establish `hjn : j ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`. Rewrite using `[map_mul, map_mul, map_pow, map_pow, hren, (hcc j hj).2, mul_assoc, GlobalTheory.CompanionTheory.Ar.Rel.pow_mul_pow_sub_eq _ _ hMy hjn, Algebra.smul_def, map_mul]`.

Use `show _ = _ * (i (p.coeff j) * α ^ j)`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Φ, map_sum]`. Rewrite using `[Finset.sum_congr rfl hterm, ← Finset.mul_sum, hpa, mul_zero]`. Establish `hev` using `hz.2 Φ (mem_mCoordIdeal_of_aeval_eq_zero y hΦh hΦy)`.

Simplify using `only [Φ, map_sum, map_mul, map_pow, hFz] at hev`. Rewrite `hev` using `[Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp), eval_map_rename']`. Establish `hMz : eval z (map (Int.castRingHom ℂ) M) ≠ 0`. Simplify using `only [M, map_prod, map_pow, map_X, eval_X]`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)`.

Rewrite `hev` using `[pow_zero, mul_one]`. Conclude with `(mul_eq_zero.1 hev).resolve_right (pow_ne_zero _ hMz)`. Use `⟨1, 0, isMultiHomog_one', by simp, fun z hz hzc _ => ?_⟩` and prove the remaining obligations. It suffices to derive a contradiction. Apply `hc` to reduce the goal to its premises.

Introduce `k h`. Apply `hzc k` to reduce the goal to its premises. Establish `hm : (X ⟨k, c k⟩ : MRing J) ∈ mCoordIdeal y` using `by show mConeMap y (X _) = 0`. Simplify using `[mConeMap, h]`. Simplify using `using hz.2 _ hm`.

Use `choose G b hG hGy hz using key`. Use `⟨∏ c, G c, ∑ c, b c, isMultiHomog_prod' _ fun c _ => hG c, ?_, fun z hzP hFz => ?_⟩` and prove the remaining obligations. Rewrite using `[map_prod]`. Conclude with `Finset.prod_ne_zero_iff.2 fun c _ => hGy c`. Use `choose c hc using hzP.1`.

Rewrite using `[map_prod, map_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ c) (hz c z hzP hc hFz)`.
-/
theorem zeros_proj {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω) (i : Ω₀ →+* Ω)
    {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) (hy : ∀ p, y (v p) = i (y₀ p))
    (hB : Birational y₀) (halg : ∀ α : Ω, (letI := i.toAlgebra; IsAlgebraic Ω₀ α))
    {F : MRing J} {aF : K → ℕ} (hF : IsMultiHomog F aF) (hFP : F ∉ mCoordIdeal y) :
    ∃ (G : MRing J₀) (b : K₀ → ℕ), IsMultiHomog G b ∧ aeval y₀ G ≠ 0 ∧
      ∀ z ∈ mcPts (mCoordIdeal y), eval z (map (Int.castRingHom ℂ) F) = 0 →
        eval (fun p => z (v p)) (map (Int.castRingHom ℂ) G) = 0 := by
  classical
  letI := i.toAlgebra
  have hFy : aeval y F ≠ 0 := fun h => hFP (mem_mCoordIdeal_of_aeval_eq_zero y hF h)
  have hren : ∀ g : MRing J₀, aeval y (rename v g) = i (aeval y₀ g) := by
    intro g
    rw [aeval_rename, ← GlobalTheory.CompanionTheory.Ar.Rel.aeval_comp_ringHom i y₀ g]
    congr 2
    funext p
    exact hy p
  have key : ∀ c : ∀ k, J k, ∃ (G : MRing J₀) (b : K₀ → ℕ), IsMultiHomog G b ∧ aeval y₀ G ≠ 0 ∧
      ∀ z ∈ mcPts (mCoordIdeal y), (∀ k, z ⟨k, c k⟩ ≠ 0) → eval z (map (Int.castRingHom ℂ) F) = 0 →
        eval (fun p => z (v p)) (map (Int.castRingHom ℂ) G) = 0 := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · let M : MRing J := ∏ k, (X ⟨k, c k⟩ : MRing J) ^ aF k
      have hM : IsMultiHomog M aF := homog_mono c aF
      have hMy : aeval y M ≠ 0 := by
        simp only [M, map_prod, map_pow, aeval_X]
        exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
      set α : Ω := aeval y F / aeval y M with hα
      have hα0 : α ≠ 0 := div_ne_zero hFy hMy
      have hint : IsIntegral Ω₀ α := (halg α).isIntegral
      set p := minpoly Ω₀ α with hp
      have hp0 : p.coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hα0
      have hpa : Polynomial.aeval α p = 0 := minpoly.aeval Ω₀ α
      rw [Polynomial.aeval_eq_sum_range] at hpa
      set n := p.natDegree
      obtain ⟨cc, a, H, hH, hcc⟩ := common_den y₀ hB (fun j => p.coeff j) (n + 1)
      have h0n : 0 ∈ Finset.range (n + 1) := by simp
      refine ⟨cc 0, a, (hcc 0 h0n).1, by rw [(hcc 0 h0n).2]; exact mul_ne_zero hp0 hH, ?_⟩
      intro z hz hzc hFz
      let Φ : MRing J := ∑ j ∈ Finset.range (n + 1), rename v (cc j) * F ^ j * M ^ (n - j)
      have hΦh : IsMultiHomog Φ (Function.extend κ a 0 + n • aF) := by
        refine homog_sum _ fun j hj => ?_
        have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        have h1 := isMultiHomog_mul' (isMultiHomog_mul' (isMultiHomog_rename' hv (hcc j hj).1) (homog_pow hF j))
          (homog_pow hM (n - j))
        convert h1 using 1
        rw [add_assoc, ← add_nsmul, Nat.add_sub_cancel' hjn]
      have hΦy : aeval y Φ = 0 := by
        have hterm : ∀ j ∈ Finset.range (n + 1), aeval y (rename v (cc j) * F ^ j * M ^ (n - j)) =
            (i H * aeval y M ^ n) * (p.coeff j • α ^ j) := by
          intro j hj
          have hjn : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          rw [map_mul, map_mul, map_pow, map_pow, hren, (hcc j hj).2, mul_assoc,
            GlobalTheory.CompanionTheory.Ar.Rel.pow_mul_pow_sub_eq _ _ hMy hjn, Algebra.smul_def, map_mul]
          show _ = _ * (i (p.coeff j) * α ^ j)
          ring
        simp only [Φ, map_sum]
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hpa, mul_zero]
      have hev := hz.2 Φ (mem_mCoordIdeal_of_aeval_eq_zero y hΦh hΦy)
      simp only [Φ, map_sum, map_mul, map_pow, hFz] at hev
      rw [Finset.sum_eq_single 0 (fun j _ hj => by simp [hj]) (by simp), eval_map_rename'] at hev
      have hMz : eval z (map (Int.castRingHom ℂ) M) ≠ 0 := by
        simp only [M, map_prod, map_pow, map_X, eval_X]
        exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hzc k)
      rw [pow_zero, mul_one] at hev
      exact (mul_eq_zero.1 hev).resolve_right (pow_ne_zero _ hMz)
    · refine ⟨1, 0, isMultiHomog_one', by simp, fun z hz hzc _ => ?_⟩
      exfalso
      apply hc
      intro k h
      apply hzc k
      have hm : (X ⟨k, c k⟩ : MRing J) ∈ mCoordIdeal y := by
        show mConeMap y (X _) = 0
        simp [mConeMap, h]
      simpa using hz.2 _ hm
  choose G b hG hGy hz using key
  refine ⟨∏ c, G c, ∑ c, b c, isMultiHomog_prod' _ fun c _ => hG c, ?_, fun z hzP hFz => ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun c _ => hGy c
  · choose c hc using hzP.1
    rw [map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (hz c z hzP hc hFz)

/- English proof (translation)
Introduce `s`. Establish `hs : s ∈ Subfield.closure (Set.range fun ij : Fin n × Fin n => yf ij.1 / yf ij.2)`. Rewrite using `[hgen]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hs using Subfield.closure_induction with`.

Consider the case `mem x hx`. Take `⟨⟨a, b⟩, rfl⟩` from `hx`. Distinguish the cases in `hb : yf b = 0`. Conclude with `⟨0, 0, 1, homog_zero _, isMultiHomog_one', by simp, by simp [hb]⟩`. Conclude with `⟨Pi.single () 1, X ⟨(), a⟩, X ⟨(), b⟩, homog_X _ _, homog_X _ _, by simpa using hb, by simp [hb]⟩`.

Consider the case `one => exact ⟨0, 1, 1, isMultiHomog_one', isMultiHomog_one', by simp, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨d, g, h, hg, hh, h0, he⟩` from `hx`. Take `⟨d', g', h', hg', hh', h0', he'⟩` from `hy`. Use `⟨d + d', g * h' + h * g', h * h', homog_add (isMultiHomog_mul' hg hh') (isMultiHomog_mul' hh hg'), isMultiHomog_mul' hh hh', by rw [map_mul]; exact mul_ne_zero h0 h0', ?_⟩` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, he, he']`. Expand and normalize the polynomial expressions, which then agree. Consider the case `neg x _ hx`. Take `⟨d, g, h, hg, hh, h0, he⟩` from `hx`. Conclude with `⟨d, -g, h, homog_neg hg, hh, h0, by rw [map_neg, he]; ring⟩`.

Consider the case `inv x _ hx`. Take `⟨d, g, h, hg, hh, h0, he⟩` from `hx`. Distinguish the cases in `hx0 : x = 0`. Conclude with `⟨0, 0, 1, homog_zero _, isMultiHomog_one', by simp, by simp [hx0]⟩`. Use `⟨d, h, g, hh, hg, by rw [he]; exact mul_ne_zero hx0 h0, ?_⟩` and prove the remaining obligations.

Rewrite using `[he]`. Clear the denominators using the available nonvanishing facts. Consider the case `mul x y _ _ hx hy`. Take `⟨d, g, h, hg, hh, h0, he⟩` from `hx`. Take `⟨d', g', h', hg', hh', h0', he'⟩` from `hy`.

Use `⟨d + d', g * g', h * h', isMultiHomog_mul' hg hg', isMultiHomog_mul' hh hh', by rw [map_mul]; exact mul_ne_zero h0 h0', ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, he, he']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem birational_of_closure {Ω : Type} [Field Ω] {n : ℕ} (yf : Fin n → Ω)
    (hgen : Subfield.closure (Set.range fun ij : Fin n × Fin n => yf ij.1 / yf ij.2) = ⊤) :
    Birational (ι := fun _ : Unit => Fin n) fun p => yf p.2 := by
  classical
  intro s
  have hs : s ∈ Subfield.closure (Set.range fun ij : Fin n × Fin n => yf ij.1 / yf ij.2) := by
    rw [hgen]; trivial
  induction hs using Subfield.closure_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    by_cases hb : yf b = 0
    · exact ⟨0, 0, 1, homog_zero _, isMultiHomog_one', by simp, by simp [hb]⟩
    · exact ⟨Pi.single () 1, X ⟨(), a⟩, X ⟨(), b⟩, homog_X _ _, homog_X _ _, by simpa using hb, by simp [hb]⟩
  | one => exact ⟨0, 1, 1, isMultiHomog_one', isMultiHomog_one', by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, g, h, hg, hh, h0, he⟩ := hx
    obtain ⟨d', g', h', hg', hh', h0', he'⟩ := hy
    refine ⟨d + d', g * h' + h * g', h * h', homog_add (isMultiHomog_mul' hg hh') (isMultiHomog_mul' hh hg'),
      isMultiHomog_mul' hh hh', by rw [map_mul]; exact mul_ne_zero h0 h0', ?_⟩
    simp only [map_add, map_mul, he, he']
    ring
  | neg x _ hx =>
    obtain ⟨d, g, h, hg, hh, h0, he⟩ := hx
    exact ⟨d, -g, h, homog_neg hg, hh, h0, by rw [map_neg, he]; ring⟩
  | inv x _ hx =>
    obtain ⟨d, g, h, hg, hh, h0, he⟩ := hx
    by_cases hx0 : x = 0
    · exact ⟨0, 0, 1, homog_zero _, isMultiHomog_one', by simp, by simp [hx0]⟩
    · refine ⟨d, h, g, hh, hg, by rw [he]; exact mul_ne_zero hx0 h0, ?_⟩
      rw [he]
      field_simp
  | mul x y _ _ hx hy =>
    obtain ⟨d, g, h, hg, hh, h0, he⟩ := hx
    obtain ⟨d', g', h', hg', hh', h0', he'⟩ := hy
    refine ⟨d + d', g * g', h * h', isMultiHomog_mul' hg hg',
      isMultiHomog_mul' hh hh', by rw [map_mul]; exact mul_ne_zero h0 h0', ?_⟩
    simp only [map_mul, he, he']
    ring

end RootFieldNumerics.Ref.Zeros
