import Mathlib
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `k A _ _ _ _ ε Δ ⟨hL, hR⟩`. Use `haveI : IsArtinianRing A := IsArtinianRing.of_finite k A`. Use `set I : Ideal A := RingHom.ker ε with hI`. Take `⟨n, hn⟩` from `IsArtinian.monotone_stabilizes (⟨fun m => OrderDual.toDual (I ^ m), fun a b h => Ideal.pow_le_pow_right h⟩ : ℕ →o (Ideal A)ᵒᵈ)`. Establish `hst : ∀ m, n ≤ m → I ^ n = I ^ m` using `fun m hm => hn m hm`.

Use `set N := n + 1 with hN`. Use `set J : Ideal A := I ^ N with hJ`. Establish `hJJ : IsIdempotentElem J` using `by show J * J = J`. Rewrite using `[hJ, ← pow_add, ← hst (N + N) (by omega), hst N (by omega)]`. Establish `hfg : J.FG` using `IsNoetherian.noetherian J`.

Take `⟨e', he', hJe⟩` from `(Ideal.isIdempotentElem_iff_of_fg J hfg).mp hJJ`. Establish `he'J : e' ∈ J` using `by rw [hJe]; exact Submodule.mem_span_singleton_self e'`. Establish `hJI : J ≤ I` using `Ideal.pow_le_self (by omega)`. Establish `he'0 : ε e' = 0` using `hJI he'J`. Use `⟨1 - e', by simp [he'0], he'.one_sub, ?_⟩` and prove the remaining obligations.

Establish `hspan : Ideal.span {1 - (1 - e')} = J`. Rewrite using `[sub_sub_cancel, hJe]`. Rewrite using `[hspan]`. Use `set mk : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J with hmk`. Set `ε' : A ⧸ J →ₐ[k] k` to `Ideal.Quotient.liftₐ J ε (fun a ha => hJI ha)`.

Establish `hε' : ∀ a, ε' (mk a) = ε a` using `fun a => rfl`. Establish `hnil : ∀ y ∈ RingHom.ker ε', IsNilpotent y`. Introduce `y hy`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mkₐ_surjective k J y`. Establish `ha : a ∈ I` using `by rw [RingHom.mem_ker] at hy ⊢; rw [← hε']; exact hy`.

Use `⟨N, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`. Conclude with `(Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.pow_mem_pow ha N)`. Set `φ : (A ⧸ J) ⊗[k] (A ⧸ J) →ₐ[k] k` to `Algebra.TensorProduct.productMap ε' ε'`. Set `Δ'' : A →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J)` to `(Algebra.TensorProduct.map mk mk).comp Δ`.

Establish `hφ : ∀ t : A ⊗[k] A, φ (Algebra.TensorProduct.map mk mk t) = ε (TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap t))`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [φ, hε', mul_comm]`.

Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Establish `hφΔ : ∀ a, φ (Δ'' a) = ε a`. Introduce `a`. Use `show φ (Algebra.TensorProduct.map mk mk (Δ a)) = ε a`. Rewrite using `[hφ, hR]`.

Set `iL : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J)` to `Algebra.TensorProduct.includeLeft`. Set `iR : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J)` to `Algebra.TensorProduct.includeRight`. Establish `key : ∀ t : (A ⧸ J) ⊗[k] (A ⧸ J), t - algebraMap k _ (φ t) ∈ nilradical _`. Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x y => set u := x - algebraMap k (A ⧸ J) (ε' x) with hu set v := y - algebraMap k (A ⧸ J) (ε' y) with hv`. Establish `hu0 : IsNilpotent u` using `hnil _ (by simp [RingHom.mem_ker, u])`. Establish `hv0 : IsNilpotent v` using `hnil _ (by simp [RingHom.mem_ker, v])`. Establish `hL : iL u ∈ nilradical _` using `mem_nilradical.2 (hu0.map _)`.

Establish `hR' : iR v ∈ nilradical _` using `mem_nilradical.2 (hv0.map _)`. Establish `heq : x ⊗ₜ[k] y - algebraMap k _ (φ (x ⊗ₜ[k] y)) = iL u * iR v + algebraMap k _ (ε' y) * iL u + algebraMap k _ (ε' x) * iR v`. Establish `h1 : x ⊗ₜ[k] y = iL x * iR y`. Simplify using `[iL, iR, Algebra.TensorProduct.tmul_mul_tmul]`. Establish `h2 : iL x = iL u + algebraMap k _ (ε' x)`.

Rewrite using `[← AlgHom.commutes iL, ← map_add]`. Simplify using `[u]`. Establish `h3 : iR y = iR v + algebraMap k _ (ε' y)`. Rewrite using `[← AlgHom.commutes iR, ← map_add]`. Simplify using `[v]`.

Establish `h4 : φ (x ⊗ₜ[k] y) = ε' x * ε' y` using `by simp [φ]`. Rewrite using `[h4, map_mul, h1, h2, h3]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[heq]`. Conclude with `add_mem (add_mem (Ideal.mul_mem_right _ _ hL) (Ideal.mul_mem_left _ _ hL)) (Ideal.mul_mem_left _ _ hR')`.

Consider the case `add s t hs ht`. Use `add_mem hs ht` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add]`. Normalize the expressions using the abelian group laws.

Establish `hkill : ∀ a ∈ J, Δ'' a = 0`. Establish `h0 : Δ'' e' = 0`. Apply `(he'.map Δ'').eq_zero_of_isNilpotent` to reduce the goal to its premises. Use `mem_nilradical.1 (key (Δ'' e'))` as an intermediate fact. Rewrite `this` using `[hφΔ, he'0, map_zero, sub_zero]`. Then use the resulting hypothesis.

Introduce `a ha`. Rewrite `ha` using `[hJe]`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 ha`. Rewrite using `[map_mul, h0, mul_zero]`. Set `Δ' : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J)` to `Ideal.Quotient.liftₐ J Δ'' hkill`.

Establish `hΔ' : ∀ a, Δ' (mk a) = Algebra.TensorProduct.map mk mk (Δ a)` using `fun a => rfl`. Use `⟨ε', Δ', ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `a'`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mkₐ_surjective k J a'`. Establish `gen : ∀ t : A ⊗[k] A, TensorProduct.lid k (A ⧸ J) (LinearMap.rTensor (A ⧸ J) ε'.toLinearMap (Algebra.TensorProduct.map mk mk t)) = mk (TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap t))`.

Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [hε']`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`.

Rewrite using `[← hmk, hΔ', gen, hL]`. Introduce `a'`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mkₐ_surjective k J a'`. Establish `gen : ∀ t : A ⊗[k] A, TensorProduct.rid k (A ⧸ J) (LinearMap.lTensor (A ⧸ J) ε'.toLinearMap (Algebra.TensorProduct.map mk mk t)) = mk (TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap t))`. Introduce `t`.

Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [hε']`. Consider the case `add s t hs ht => simp only [map_add, hs, ht]`. Rewrite using `[← hmk, hΔ', gen, hR]`.

Rewrite using `[Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]`. Introduce `y hy`. Conclude with `mem_nilradical.2 (hnil y hy)`.
-/
theorem localFactor_counital_descends :
    ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∃ e : A, ε e = 1 ∧ IsIdempotentElem e ∧ ∃ (ε' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] k) (Δ' : (A ⧸ Ideal.span {1 - e}) →ₐ[k] (A ⧸ Ideal.span {1 - e}) ⊗[k] (A ⧸ Ideal.span {1 - e})), ((∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.lid k (A ⧸ Ideal.span {1 - e}) (LinearMap.rTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a) ∧ (∀ a : (A ⧸ Ideal.span {1 - e}), TensorProduct.rid k (A ⧸ Ideal.span {1 - e}) (LinearMap.lTensor (A ⧸ Ideal.span {1 - e}) ε'.toLinearMap (Δ' a)) = a)) ∧ IsNilpotent (RingHom.ker ε') := by
  intro k A _ _ _ _ ε Δ ⟨hL, hR⟩
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  set I : Ideal A := RingHom.ker ε with hI
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes
    (⟨fun m => OrderDual.toDual (I ^ m), fun a b h => Ideal.pow_le_pow_right h⟩ : ℕ →o (Ideal A)ᵒᵈ)
  have hst : ∀ m, n ≤ m → I ^ n = I ^ m := fun m hm => hn m hm
  set N := n + 1 with hN
  set J : Ideal A := I ^ N with hJ
  have hJJ : IsIdempotentElem J := by
    show J * J = J
    rw [hJ, ← pow_add, ← hst (N + N) (by omega), hst N (by omega)]
  have hfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨e', he', hJe⟩ := (Ideal.isIdempotentElem_iff_of_fg J hfg).mp hJJ
  have he'J : e' ∈ J := by rw [hJe]; exact Submodule.mem_span_singleton_self e'
  have hJI : J ≤ I := Ideal.pow_le_self (by omega)
  have he'0 : ε e' = 0 := hJI he'J
  refine ⟨1 - e', by simp [he'0], he'.one_sub, ?_⟩
  have hspan : Ideal.span {1 - (1 - e')} = J := by
    rw [sub_sub_cancel, hJe]
  rw [hspan]
  set mk : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J with hmk
  let ε' : A ⧸ J →ₐ[k] k := Ideal.Quotient.liftₐ J ε (fun a ha => hJI ha)
  have hε' : ∀ a, ε' (mk a) = ε a := fun a => rfl
  have hnil : ∀ y ∈ RingHom.ker ε', IsNilpotent y := by
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J y
    have ha : a ∈ I := by rw [RingHom.mem_ker] at hy ⊢; rw [← hε']; exact hy
    refine ⟨N, ?_⟩
    rw [← map_pow]
    exact (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.pow_mem_pow ha N)
  let φ : (A ⧸ J) ⊗[k] (A ⧸ J) →ₐ[k] k := Algebra.TensorProduct.productMap ε' ε'
  let Δ'' : A →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := (Algebra.TensorProduct.map mk mk).comp Δ
  have hφ : ∀ t : A ⊗[k] A, φ (Algebra.TensorProduct.map mk mk t)
      = ε (TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap t)) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [φ, hε', mul_comm]
    | add s t hs ht => simp only [map_add, hs, ht]
  have hφΔ : ∀ a, φ (Δ'' a) = ε a := by
    intro a
    show φ (Algebra.TensorProduct.map mk mk (Δ a)) = ε a
    rw [hφ, hR]
  let iL : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Algebra.TensorProduct.includeLeft
  let iR : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Algebra.TensorProduct.includeRight
  have key : ∀ t : (A ⧸ J) ⊗[k] (A ⧸ J), t - algebraMap k _ (φ t) ∈ nilradical _ := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      set u := x - algebraMap k (A ⧸ J) (ε' x) with hu
      set v := y - algebraMap k (A ⧸ J) (ε' y) with hv
      have hu0 : IsNilpotent u := hnil _ (by simp [RingHom.mem_ker, u])
      have hv0 : IsNilpotent v := hnil _ (by simp [RingHom.mem_ker, v])
      have hL : iL u ∈ nilradical _ :=
        mem_nilradical.2 (hu0.map _)
      have hR' : iR v ∈ nilradical _ :=
        mem_nilradical.2 (hv0.map _)
      have heq : x ⊗ₜ[k] y - algebraMap k _ (φ (x ⊗ₜ[k] y)) =
          iL u * iR v
          + algebraMap k _ (ε' y) * iL u
          + algebraMap k _ (ε' x) * iR v := by
        have h1 : x ⊗ₜ[k] y = iL x * iR y := by
          simp [iL, iR, Algebra.TensorProduct.tmul_mul_tmul]
        have h2 : iL x = iL u + algebraMap k _ (ε' x) := by
          rw [← AlgHom.commutes iL, ← map_add]; simp [u]
        have h3 : iR y = iR v + algebraMap k _ (ε' y) := by
          rw [← AlgHom.commutes iR, ← map_add]; simp [v]
        have h4 : φ (x ⊗ₜ[k] y) = ε' x * ε' y := by simp [φ]
        rw [h4, map_mul, h1, h2, h3]; ring
      rw [heq]
      exact add_mem (add_mem (Ideal.mul_mem_right _ _ hL) (Ideal.mul_mem_left _ _ hL)) (Ideal.mul_mem_left _ _ hR')
    | add s t hs ht =>
      have := add_mem hs ht
      convert this using 1
      simp only [map_add]; abel
  have hkill : ∀ a ∈ J, Δ'' a = 0 := by
    have h0 : Δ'' e' = 0 := by
      apply (he'.map Δ'').eq_zero_of_isNilpotent
      have := mem_nilradical.1 (key (Δ'' e'))
      rwa [hφΔ, he'0, map_zero, sub_zero] at this
    intro a ha
    rw [hJe] at ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, h0, mul_zero]
  let Δ' : A ⧸ J →ₐ[k] (A ⧸ J) ⊗[k] (A ⧸ J) := Ideal.Quotient.liftₐ J Δ'' hkill
  have hΔ' : ∀ a, Δ' (mk a) = Algebra.TensorProduct.map mk mk (Δ a) := fun a => rfl
  refine ⟨ε', Δ', ⟨?_, ?_⟩, ?_⟩
  · intro a'
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J a'
    have gen : ∀ t : A ⊗[k] A, TensorProduct.lid k (A ⧸ J) (LinearMap.rTensor (A ⧸ J) ε'.toLinearMap
        (Algebra.TensorProduct.map mk mk t)) = mk (TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [hε']
      | add s t hs ht => simp only [map_add, hs, ht]
    rw [← hmk, hΔ', gen, hL]
  · intro a'
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective k J a'
    have gen : ∀ t : A ⊗[k] A, TensorProduct.rid k (A ⧸ J) (LinearMap.lTensor (A ⧸ J) ε'.toLinearMap
        (Algebra.TensorProduct.map mk mk t)) = mk (TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap t)) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => simp [hε']
      | add s t hs ht => simp only [map_add, hs, ht]
    rw [← hmk, hΔ', gen, hR]
  · rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro y hy
    exact mem_nilradical.2 (hnil y hy)

end GlobalTheory
