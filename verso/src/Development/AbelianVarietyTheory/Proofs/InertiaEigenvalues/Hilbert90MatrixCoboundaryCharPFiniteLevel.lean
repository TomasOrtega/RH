import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

namespace GlobalTheory.UnramifiedHilbertNinety

open GlobalTheory.UnramifiedCrys

/- English proof (translation)
Establish `key : ∀ T : Finset ι, ∃ v : ι → V, (∀ i ∈ T, v i ∈ S) ∧ f v ≠ 0`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => exact ⟨v₀, by simp, h₀⟩`. Consider the case `insert a T ha ih`.

Take `⟨v, hv, hf⟩` from `ih`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, hne⟩ : ∃ s ∈ S, f (Function.update v a s) ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `h1` using `hS (f.toLinearMap v a) hc`.

Establish `h2` using `LinearMap.congr_fun h1 (v a)`. Rewrite `h2` using `[MultilinearMap.toLinearMap_apply, Function.update_eq_self]`. Conclude with `hf h2`. Use `⟨Function.update v a s, fun i hi => ?_, hne⟩` and prove the remaining obligations. Distinguish the cases in `hia : i = a`.

Substitute `hia` using the available equality. Rewrite using `[Function.update_self]` and apply the resulting hypothesis. Rewrite using `[Function.update_of_ne hia]`. Conclude with `hv i ((Finset.mem_insert.1 hi).resolve_left hia)`. Take `⟨v, hv, hf⟩` from `key Finset.univ`.

Conclude with `⟨v, fun i => hv i (Finset.mem_univ i), hf⟩`.
-/
theorem exists_mem_multilinear_ne_zero {R V ι : Type} [CommRing R] [AddCommGroup V] [Module R V]
    [Fintype ι] [DecidableEq ι] (f : MultilinearMap R (fun _ : ι => V) R) (S : Set V)
    (hS : ∀ l : V →ₗ[R] R, (∀ s ∈ S, l s = 0) → l = 0) (v₀ : ι → V) (h₀ : f v₀ ≠ 0) :
    ∃ v : ι → V, (∀ i, v i ∈ S) ∧ f v ≠ 0 := by
  have key : ∀ T : Finset ι, ∃ v : ι → V, (∀ i ∈ T, v i ∈ S) ∧ f v ≠ 0 := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨v₀, by simp, h₀⟩
    | insert a T ha ih =>
      obtain ⟨v, hv, hf⟩ := ih
      obtain ⟨s, hs, hne⟩ : ∃ s ∈ S, f (Function.update v a s) ≠ 0 := by
        by_contra hc
        push Not at hc
        have h1 := hS (f.toLinearMap v a) hc
        have h2 := LinearMap.congr_fun h1 (v a)
        rw [MultilinearMap.toLinearMap_apply, Function.update_eq_self] at h2
        exact hf h2
      refine ⟨Function.update v a s, fun i hi => ?_, hne⟩
      by_cases hia : i = a
      · subst hia
        rwa [Function.update_self]
      · rw [Function.update_of_ne hia]
        exact hv i ((Finset.mem_insert.1 hi).resolve_left hia)
  obtain ⟨v, hv, hf⟩ := key Finset.univ
  exact ⟨v, fun i => hv i (Finset.mem_univ i), hf⟩

/- English proof (translation)
Use `set N := fixer ρ p m with hN`. Use `letI : Fintype (G ⧸ N) := Fintype.ofFinite _`. Set `χ : G ⧸ N → (fixedPow p R m →* R)` to `fun x => (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype`. Establish `hχ : Function.Injective χ`. Introduce `x x' h`.

Rewrite using `[← x.out_eq, ← x'.out_eq]`. Apply `Quotient.sound` to reduce the goal to its premises. Apply `QuotientGroup.leftRel_apply.2` to reduce the goal to its premises. Introduce `y hy`. Establish `h1 : ρ x.out y = ρ x'.out y` using `DFunLike.congr_fun h ⟨y, hy⟩`.

Rewrite using `[map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, RingAut.one_apply]`. Establish `hli` using `(linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ`. Establish `hsum : ∀ (f : G → R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g, ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out`. Introduce `f hf g`. Use `Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_` and prove the remaining obligations.

Take `⟨n, hn⟩` from `QuotientGroup.mk_out_eq_mul N (g * x.out)`. Establish `: MulAction.toPerm g x = QuotientGroup.mk (g * x.out)`. Rewrite using `[MulAction.toPerm_apply]`. Use `conv_lhs => rw [← x.out_eq]`. Both sides reduce to the same expression.

Rewrite using `[this, hn, hf _ _ n.2]`. Set `S : Set (Fin r → R)` to `{v | (∀ i, v i ^ p ^ m = v i) ∧ ∀ g i, ∑ k, M g i k * ρ g (v k) = v i}`. Establish `hb : ∀ (θ : fixedPow p R m) (j : Fin r), (fun i => ∑ x : G ⧸ N, ρ x.out θ * M x.out i j) ∈ S`. Introduce `θ j`. Establish `hθm : (θ : R) ^ p ^ m = θ` using `θ.2`.

Use `⟨fun i => ?_, fun g i => ?_⟩` and prove the remaining obligations. Rewrite using `[sum_pow_char_pow]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[mul_pow, ← map_pow, hθm, hM]`. Establish `h2` using `hsum (fun g => ρ g θ * M g i j) (fun g n hn => by`.

Simplify using `only [map_mul, RingAut.mul_apply, hn θ hθm, hMN n hn, mul_one]) g`. Simplify using `only [map_sum, Finset.mul_sum]`. Rewrite using `[← h2, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul, RingAut.mul_apply, Matrix.mul_apply, hρ, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hS : ∀ l : (Fin r → R) →ₗ[R] R, (∀ s ∈ S, l s = 0) → l = 0`. Introduce `l hl`. Use `LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_` and prove the remaining obligations.

Establish `h1` using `Fintype.linearIndependent_iff.1 hli (fun x => l (fun i => M x.out i j)) (by`. Use function extensionality and compare the values at `θ`. Simplify using `only [Finset.sum_apply, Function.comp, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]`. Establish `h3 : (fun i => ∑ x : G ⧸ N, ρ x.out θ * M x.out i j) = ∑ x : G ⧸ N, ρ x.out θ • (fun i => M x.out i j)`. Use function extensionality and compare the values at `i`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Establish `h4` using `hl _ (hb θ j)`. Rewrite `h4` using `[h3, map_sum]`. Rewrite using `[← h4]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, smul_eq_mul, mul_comm]`. Use the proof step `rfl) (QuotientGroup.mk 1)`. Take `⟨n, hn⟩` from `QuotientGroup.mk_out_eq_mul N (1 : G)`. Simplify using `only [hn, one_mul, hMN n n.2] at h1`. Establish `h5 : (fun i => (1 : Matrix (Fin r) (Fin r) R) i j) = Pi.single j 1`.

Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.one_apply, Pi.single_apply]`. Rewrite `h1` using `[h5]`. Simplify using `using h1`. Take `⟨v, hv, hf⟩` from `exists_mem_multilinear_ne_zero (Matrix.detRowAlternating (n := Fin r) (R := R)).toMultilinearMap S hS (1 : Matrix (Fin r) (Fin r) R) (by`.

Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin r) (Fin r) R).det ≠ 0`. Rewrite using `[Matrix.det_one]`. Conclude with `one_ne_zero)`. Establish `hf' : ((Matrix.of v).transpose).det ≠ 0`. Rewrite using `[Matrix.det_transpose]`.

Conclude with `hf`. Establish `hW : ∀ i j, (Matrix.of v).transpose i j ^ p ^ m = (Matrix.of v).transpose i j` using `fun i j => (hv j).1 i`. Use `⟨(Matrix.of v).transpose, ?_, hW, fun g => ?_⟩` and prove the remaining obligations. Use `set t := ((Matrix.of v).transpose).det with ht`. Establish `htq : t ^ p ^ m = t`.

Rewrite using `[← iterateFrobenius_def, ht, RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Conclude with `hW i j`. Establish `h1 : 1 < p ^ m` using `Nat.one_lt_pow hm.ne' hp.out.one_lt`.

Establish `hu : t ^ (p ^ m - 2) * t = 1`. Apply `mul_right_cancel₀ hf'` to reduce the goal to its premises. Rewrite using `[← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]`. Conclude with `IsUnit.of_mul_eq_one_right _ hu`. Use extensionality with `i j`.

Conclude with `(hv j).2 g i`.
-/
theorem exists_matrix_coboundary (p : ℕ) [hp : Fact p.Prime] (G : Type) [Group G] (R : Type)
    [CommRing R] [IsDomain R] [CharP R p] (ρ : G →* (R ≃+* R)) (m : ℕ) (hm : 0 < m)
    (hfin : Finite (G ⧸ fixer ρ p m)) (r : ℕ) (M : G →* Matrix (Fin r) (Fin r) R)
    (hρ : ∀ g h i j, ρ g (M h i j) = M h i j) (hM : ∀ h i j, M h i j ^ p ^ m = M h i j)
    (hMN : ∀ g ∈ fixer ρ p m, M g = 1) :
    ∃ W : Matrix (Fin r) (Fin r) R, IsUnit W.det ∧ (∀ i j, W i j ^ p ^ m = W i j) ∧
      ∀ g, M g * W.map (ρ g) = W := by
  classical
  set N := fixer ρ p m with hN
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  let χ : G ⧸ N → (fixedPow p R m →* R) := fun x =>
    (ρ x.out).toMonoidHom.comp (fixedPow p R m).subtype
  have hχ : Function.Injective χ := by
    intro x x' h
    rw [← x.out_eq, ← x'.out_eq]
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.2
    intro y hy
    have h1 : ρ x.out y = ρ x'.out y := DFunLike.congr_fun h ⟨y, hy⟩
    rw [map_mul, RingAut.mul_apply, ← h1, ← RingAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      RingAut.one_apply]
  have hli := (linearIndependent_monoidHom (fixedPow p R m) R).comp χ hχ
  have hsum : ∀ (f : G → R), (∀ g, ∀ n ∈ N, f (g * n) = f g) → ∀ g,
      ∑ x : G ⧸ N, f (g * x.out) = ∑ x : G ⧸ N, f x.out := by
    intro f hf g
    refine Fintype.sum_equiv (MulAction.toPerm g) _ _ fun x => ?_
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (g * x.out)
    have : MulAction.toPerm g x = QuotientGroup.mk (g * x.out) := by
      rw [MulAction.toPerm_apply]
      conv_lhs => rw [← x.out_eq]
      rfl
    rw [this, hn, hf _ _ n.2]
  let S : Set (Fin r → R) := {v | (∀ i, v i ^ p ^ m = v i) ∧
    ∀ g i, ∑ k, M g i k * ρ g (v k) = v i}
  have hb : ∀ (θ : fixedPow p R m) (j : Fin r),
      (fun i => ∑ x : G ⧸ N, ρ x.out θ * M x.out i j) ∈ S := by
    intro θ j
    have hθm : (θ : R) ^ p ^ m = θ := θ.2
    refine ⟨fun i => ?_, fun g i => ?_⟩
    · rw [sum_pow_char_pow]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_pow, ← map_pow, hθm, hM]
    · have h2 := hsum (fun g => ρ g θ * M g i j) (fun g n hn => by
        simp only [map_mul, RingAut.mul_apply, hn θ hθm, hMN n hn, mul_one]) g
      simp only [map_sum, Finset.mul_sum]
      rw [← h2, Finset.sum_comm]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [map_mul, RingAut.mul_apply, Matrix.mul_apply, hρ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
  have hS : ∀ l : (Fin r → R) →ₗ[R] R, (∀ s ∈ S, l s = 0) → l = 0 := by
    intro l hl
    refine LinearMap.pi_ext' fun j => LinearMap.ext_ring ?_
    have h1 := Fintype.linearIndependent_iff.1 hli (fun x => l (fun i => M x.out i j)) (by
      funext θ
      simp only [Finset.sum_apply, Function.comp, Pi.zero_apply, Pi.smul_apply, smul_eq_mul]
      have h3 : (fun i => ∑ x : G ⧸ N, ρ x.out θ * M x.out i j) =
          ∑ x : G ⧸ N, ρ x.out θ • (fun i => M x.out i j) := by
        funext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h4 := hl _ (hb θ j)
      rw [h3, map_sum] at h4
      rw [← h4]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
      rfl) (QuotientGroup.mk 1)
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N (1 : G)
    simp only [hn, one_mul, hMN n n.2] at h1
    have h5 : (fun i => (1 : Matrix (Fin r) (Fin r) R) i j) = Pi.single j 1 := by
      funext i
      rw [Matrix.one_apply, Pi.single_apply]
    rw [h5] at h1
    simpa using h1
  obtain ⟨v, hv, hf⟩ := exists_mem_multilinear_ne_zero
    (Matrix.detRowAlternating (n := Fin r) (R := R)).toMultilinearMap S hS
    (1 : Matrix (Fin r) (Fin r) R) (by
      change (1 : Matrix (Fin r) (Fin r) R).det ≠ 0
      rw [Matrix.det_one]
      exact one_ne_zero)
  have hf' : ((Matrix.of v).transpose).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact hf
  have hW : ∀ i j, (Matrix.of v).transpose i j ^ p ^ m = (Matrix.of v).transpose i j :=
    fun i j => (hv j).1 i
  refine ⟨(Matrix.of v).transpose, ?_, hW, fun g => ?_⟩
  · set t := ((Matrix.of v).transpose).det with ht
    have htq : t ^ p ^ m = t := by
      rw [← iterateFrobenius_def, ht, RingHom.map_det]
      congr 1
      ext i j
      exact hW i j
    have h1 : 1 < p ^ m := Nat.one_lt_pow hm.ne' hp.out.one_lt
    have hu : t ^ (p ^ m - 2) * t = 1 := by
      apply mul_right_cancel₀ hf'
      rw [← pow_succ, ← pow_succ, one_mul, show p ^ m - 2 + 1 + 1 = p ^ m by omega, htq]
    exact IsUnit.of_mul_eq_one_right _ hu
  · ext i j
    exact (hv j).2 g i

end GlobalTheory.UnramifiedHilbertNinety
