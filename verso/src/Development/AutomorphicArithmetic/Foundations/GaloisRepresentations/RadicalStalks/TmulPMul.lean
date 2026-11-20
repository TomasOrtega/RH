import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

/- English proof (translation)
Establish `h1 : (p : C) * t = p • t` using `(nsmul_eq_mul p t).symm`. Establish `h2 : (p • l : k) = 0` using `by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]`. Rewrite using `[h1, ← TensorProduct.smul_tmul, h2, TensorProduct.zero_tmul]`.
-/
private lemma tmul_p_mul (p : ℕ) (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] (l : k) (t : C) :
    l ⊗ₜ[ℤ] ((p : C) * t) = 0 := by
  have h1 : (p : C) * t = p • t := (nsmul_eq_mul p t).symm
  have h2 : (p • l : k) = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [h1, ← TensorProduct.smul_tmul, h2, TensorProduct.zero_tmul]

/- English proof (translation)
Use `haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩`. Use `letI : Algebra (ZMod p) k := ZMod.algebra k p`. Set `B` to `Module.Basis.ofVectorSpace (ZMod p) k`. Set `J : Ideal C` to `Ideal.span {(p : C)}`. Establish `hpJ : (Int.castAddHom (C ⧸ J)) (p : ℤ) = 0` using `by show ((p : ℤ) : C ⧸ J) = 0`.

Rewrite using `[Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.subset_span rfl`. Set `φ : ZMod p →+ C ⧸ J` to `ZMod.lift p ⟨Int.castAddHom (C ⧸ J), hpJ⟩`. Establish `hφ1 : φ 1 = 1`. Establish `h1` using `ZMod.lift_coe p ⟨Int.castAddHom (C ⧸ J), hpJ⟩ (1 : ℤ)`.

Simplify using `using h1`. Use `⟨_, B, ?_, ?_⟩` and prove the remaining obligations. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `tmul l t`. Use `⟨(B.repr l).mapRange (fun r => ((r.val : ℕ) : C) * t) (by simp), ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _)]`. Establish `hl` using `B.linearCombination_repr l`. Rewrite `hl` using `[Finsupp.linearCombination_apply]`.

Use `conv_lhs => rw [← hl]`. Rewrite using `[Finsupp.sum, Finsupp.sum, TensorProduct.sum_tmul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hs : (B.repr l j) • B j = (B.repr l j).val • B j` using `by conv_lhs => rw [← ZMod.natCast_zmod_val (B.repr l j)]`. Rewrite using `[Nat.cast_smul_eq_nsmul]`.

Rewrite using `[hs, TensorProduct.smul_tmul, nsmul_eq_mul]`. Consider the case `add x y hx hy`. Take `⟨c1, rfl⟩` from `hx`. Take `⟨c2, rfl⟩` from `hy`. Conclude with `⟨c1 + c2, by rw [Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) (fun _ _ _ => TensorProduct.tmul_add _ _ _)]⟩`.

Introduce `s c hs j hj`. Set `L : k →ₗ[ℤ] C →ₗ[ℤ] C ⧸ J` to `LinearMap.mk₂ ℤ (fun l t => φ (B.repr l j) * Ideal.Quotient.mk J t) (by intros; simp [add_mul]) (by intro n m t; rw [map_zsmul, Finsupp.smul_apply, map_zsmul, smul_mul_assoc]) (by intros; simp [mul_add]) (by intro n m t; rw [map_zsmul, mul_smul_comm])`. Establish `h0` using `congrArg (TensorProduct.lift L) hs`. Rewrite `h0` using `[map_sum, map_zero]`. Establish `step : ∀ i ∈ s, TensorProduct.lift L (B i ⊗ₜ[ℤ] c i) = if i = j then Ideal.Quotient.mk J (c i) else 0`.

Introduce `i _`. Rewrite using `[TensorProduct.lift.tmul]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[L, hφ1]`.

Simplify using `[L, h, Finsupp.single_apply]`. Rewrite `h0` using `[Finset.sum_congr rfl step, Finset.sum_ite_eq' s j, if_pos hj, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mem_span_singleton.mp h0`.
-/
private lemma core (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] :
    ∃ (I : Type) (β : I → k),
      (∀ x : k ⊗[ℤ] C, ∃ c : I →₀ C, x = c.sum fun j d => β j ⊗ₜ[ℤ] d) ∧
      (∀ (s : Finset I) (c : I → C), ∑ j ∈ s, β j ⊗ₜ[ℤ] c j = 0 → ∀ j ∈ s, (p : C) ∣ c j) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let B := Module.Basis.ofVectorSpace (ZMod p) k
  let J : Ideal C := Ideal.span {(p : C)}
  have hpJ : (Int.castAddHom (C ⧸ J)) (p : ℤ) = 0 := by
    show ((p : ℤ) : C ⧸ J) = 0
    rw [Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  let φ : ZMod p →+ C ⧸ J := ZMod.lift p ⟨Int.castAddHom (C ⧸ J), hpJ⟩
  have hφ1 : φ 1 = 1 := by
    have h1 := ZMod.lift_coe p ⟨Int.castAddHom (C ⧸ J), hpJ⟩ (1 : ℤ)
    simpa using h1
  refine ⟨_, B, ?_, ?_⟩
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l t =>
      refine ⟨(B.repr l).mapRange (fun r => ((r.val : ℕ) : C) * t) (by simp), ?_⟩
      rw [Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _)]
      have hl := B.linearCombination_repr l
      rw [Finsupp.linearCombination_apply] at hl
      conv_lhs => rw [← hl]
      rw [Finsupp.sum, Finsupp.sum, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hs : (B.repr l j) • B j = (B.repr l j).val • B j := by
        conv_lhs => rw [← ZMod.natCast_zmod_val (B.repr l j)]
        rw [Nat.cast_smul_eq_nsmul]
      rw [hs, TensorProduct.smul_tmul, nsmul_eq_mul]
    | add x y hx hy =>
      obtain ⟨c1, rfl⟩ := hx
      obtain ⟨c2, rfl⟩ := hy
      exact ⟨c1 + c2, by rw [Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) (fun _ _ _ => TensorProduct.tmul_add _ _ _)]⟩
  · intro s c hs j hj
    let L : k →ₗ[ℤ] C →ₗ[ℤ] C ⧸ J := LinearMap.mk₂ ℤ (fun l t => φ (B.repr l j) * Ideal.Quotient.mk J t)
      (by intros; simp [add_mul])
      (by intro n m t; rw [map_zsmul, Finsupp.smul_apply, map_zsmul, smul_mul_assoc])
      (by intros; simp [mul_add])
      (by intro n m t; rw [map_zsmul, mul_smul_comm])
    have h0 := congrArg (TensorProduct.lift L) hs
    rw [map_sum, map_zero] at h0
    have step : ∀ i ∈ s, TensorProduct.lift L (B i ⊗ₜ[ℤ] c i) = if i = j then Ideal.Quotient.mk J (c i) else 0 := by
      intro i _
      rw [TensorProduct.lift.tmul]
      by_cases h : i = j
      · subst h; simp [L, hφ1]
      · simp [L, h, Finsupp.single_apply]
    rw [Finset.sum_congr rfl step, Finset.sum_ite_eq' s j, if_pos hj, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact Ideal.mem_span_singleton.mp h0

/- English proof (translation)
Take `⟨s, hs⟩` from `(inferInstance : Module.Projective R M).out`. Establish `hy : ∀ m, g * s x m = 0`. Introduce `m`. Establish `h0 : s (g • x) = 0` using `by rw [hx, map_zero]`. Rewrite `h0` using `[map_smul]`.

Establish `h1` using `congrArg (fun y => y m) h0`. Simplify using `using h1`. Use `choose u v huv using fun m => h _ (hy m)`. Use `⟨∑ m ∈ (s x).support, u m • m, ∑ m ∈ (s x).support, v m • m, ?_⟩` and prove the remaining obligations. Establish `hx'` using `hs x`.

Rewrite `hx'` using `[Finsupp.linearCombination_apply]`. Use `conv_lhs => rw [← hx']`. Rewrite using `[Finsupp.sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[huv m, add_smul, mul_smul, mul_smul]`.

Both sides reduce to the same expression.
-/
private lemma exact1 {R : Type} [CommRing R] (g a b : R) (h : ∀ x : R, g * x = 0 → ∃ u v, x = a * u + b * v)
    {M : Type 1} [AddCommGroup M] [Module R M] [Module.Projective R M] (x : M) (hx : g • x = 0) :
    ∃ u v : M, x = a • u + b • v := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  have hy : ∀ m, g * s x m = 0 := by
    intro m
    have h0 : s (g • x) = 0 := by rw [hx, map_zero]
    rw [map_smul] at h0
    have h1 := congrArg (fun y => y m) h0
    simpa using h1
  choose u v huv using fun m => h _ (hy m)
  refine ⟨∑ m ∈ (s x).support, u m • m, ∑ m ∈ (s x).support, v m • m, ?_⟩
  have hx' := hs x
  rw [Finsupp.linearCombination_apply] at hx'
  conv_lhs => rw [← hx']
  rw [Finsupp.sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [huv m, add_smul, mul_smul, mul_smul]
  rfl

/- English proof (translation)
Take `⟨s, hs⟩` from `(inferInstance : Module.Projective R M).out`. Establish `hy : ∀ m, a * s x m = 0`. Introduce `m`. Establish `h0 : s (a • x) = 0` using `by rw [hx, map_zero]`. Rewrite `h0` using `[map_smul]`.

Establish `h1` using `congrArg (fun y => y m) h0`. Simplify using `using h1`. Use `choose u hu using fun m => h _ (hy m)`. Use `⟨∑ m ∈ (s x).support, u m • m, ?_⟩` and prove the remaining obligations. Establish `hx'` using `hs x`.

Rewrite `hx'` using `[Finsupp.linearCombination_apply]`. Use `conv_lhs => rw [← hx']`. Rewrite using `[Finsupp.sum, Finset.smul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_smul, hu m, mul_smul]`.

Both sides reduce to the same expression.
-/
private lemma exact2 {R : Type} [CommRing R] (e g a : R) (h : ∀ x : R, a * x = 0 → ∃ u, e * x = g * u)
    {M : Type 1} [AddCommGroup M] [Module R M] [Module.Projective R M] (x : M) (hx : a • x = 0) :
    ∃ u : M, e • x = g • u := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  have hy : ∀ m, a * s x m = 0 := by
    intro m
    have h0 : s (a • x) = 0 := by rw [hx, map_zero]
    rw [map_smul] at h0
    have h1 := congrArg (fun y => y m) h0
    simpa using h1
  choose u hu using fun m => h _ (hy m)
  refine ⟨∑ m ∈ (s x).support, u m • m, ?_⟩
  have hx' := hs x
  rw [Finsupp.linearCombination_apply] at hx'
  conv_lhs => rw [← hx']
  rw [Finsupp.sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_smul, hu m, mul_smul]
  rfl

/- English proof (translation)
Introduce `p _ k _ _ C _ w f π M _ _ _`. Take `⟨I, β, hspan, hind⟩` from `core p k C`. Prove the components needed by the constructor for the conclusion. Introduce `x hx`. Use `exact1 _ _ _ ?_ x hx` and prove the remaining obligations.

Introduce `y hy`. Take `⟨c, rfl⟩` from `hspan y`. Rewrite `hy` using `[Finsupp.sum, Finset.mul_sum]`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul] at hy`. Establish `key : ∀ j ∈ c.support, (p : C) ∣ π.g * c j` using `hind c.support (fun j => π.g * c j) hy`.

Use `choose! u v hd using fun j (hj : j ∈ c.support) => π.annG (c j) (key j hj)`. Use `⟨∑ j ∈ c.support, β j ⊗ₜ[ℤ] u j, ∑ j ∈ c.support, β j ⊗ₜ[ℤ] v j, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Take `⟨t, ht⟩` from `hd j hj`.

Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← TensorProduct.tmul_add]`. Establish `hc : c j = π.a * u j + (1 - π.ε) * v j + p * t` using `by rw [← ht]; ring`. Rewrite using `[hc, TensorProduct.tmul_add, tmul_p_mul p k C, add_zero]`. Introduce `x hx`. Use `exact2 _ _ _ ?_ x hx` and prove the remaining obligations.

Introduce `y hy`. Take `⟨c, rfl⟩` from `hspan y`. Rewrite `hy` using `[Finsupp.sum, Finset.mul_sum]`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul] at hy`. Establish `key : ∀ j ∈ c.support, (p : C) ∣ π.a * c j` using `hind c.support (fun j => π.a * c j) hy`.

Use `choose! u hd using fun j (hj : j ∈ c.support) => π.annA (c j) (key j hj)`. Use `⟨∑ j ∈ c.support, β j ⊗ₜ[ℤ] u j, ?_⟩` and prove the remaining obligations. Rewrite using `[Finsupp.sum, Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Take `⟨t, ht⟩` from `hd j hj`.

Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]`. Establish `hc : π.ε * c j = π.g * u j + p * t` using `by rw [← ht]; ring`. Rewrite using `[hc, TensorProduct.tmul_add, tmul_p_mul p k C, add_zero]`.
-/
theorem UpperTheory.Gal.Ord.proj :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] (w : Ideal C) (f : ℕ) (π : Par p w f)
      (M : Type 1) [AddCommGroup M] [Module (k ⊗[ℤ] C) M] [Module.Projective (k ⊗[ℤ] C) M],
      (∀ x : M, ((1 : k) ⊗ₜ[ℤ] π.g) • x = 0 → ∃ u v : M, x = ((1 : k) ⊗ₜ[ℤ] π.a) • u + ((1 : k) ⊗ₜ[ℤ] (1 - π.ε)) • v) ∧
      ∀ x : M, ((1 : k) ⊗ₜ[ℤ] π.a) • x = 0 → ∃ u : M, ((1 : k) ⊗ₜ[ℤ] π.ε) • x = ((1 : k) ⊗ₜ[ℤ] π.g) • u := by
  intro p _ k _ _ C _ w f π M _ _ _
  obtain ⟨I, β, hspan, hind⟩ := core p k C
  constructor
  · intro x hx
    refine exact1 _ _ _ ?_ x hx
    intro y hy
    obtain ⟨c, rfl⟩ := hspan y
    rw [Finsupp.sum, Finset.mul_sum] at hy
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul] at hy
    have key : ∀ j ∈ c.support, (p : C) ∣ π.g * c j := hind c.support (fun j => π.g * c j) hy
    choose! u v hd using fun j (hj : j ∈ c.support) => π.annG (c j) (key j hj)
    refine ⟨∑ j ∈ c.support, β j ⊗ₜ[ℤ] u j, ∑ j ∈ c.support, β j ⊗ₜ[ℤ] v j, ?_⟩
    rw [Finsupp.sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨t, ht⟩ := hd j hj
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← TensorProduct.tmul_add]
    have hc : c j = π.a * u j + (1 - π.ε) * v j + p * t := by rw [← ht]; ring
    rw [hc, TensorProduct.tmul_add, tmul_p_mul p k C, add_zero]
  · intro x hx
    refine exact2 _ _ _ ?_ x hx
    intro y hy
    obtain ⟨c, rfl⟩ := hspan y
    rw [Finsupp.sum, Finset.mul_sum] at hy
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul] at hy
    have key : ∀ j ∈ c.support, (p : C) ∣ π.a * c j := hind c.support (fun j => π.a * c j) hy
    choose! u hd using fun j (hj : j ∈ c.support) => π.annA (c j) (key j hj)
    refine ⟨∑ j ∈ c.support, β j ⊗ₜ[ℤ] u j, ?_⟩
    rw [Finsupp.sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨t, ht⟩ := hd j hj
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
    have hc : π.ε * c j = π.g * u j + p * t := by rw [← ht]; ring
    rw [hc, TensorProduct.tmul_add, tmul_p_mul p k C, add_zero]
