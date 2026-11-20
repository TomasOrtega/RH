import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRingHomPowPrimePow
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PfFacts

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

/- English proof (translation)
Apply `FC.injective` to reduce the goal to its premises. Rewrite using `[RingEquiv.apply_symm_apply, Algebra.smul_def, Algebra.smul_def, map_mul, RingEquiv.apply_symm_apply, hFC, ← map_pow (algebraMap A C), ← hFA (FA.symm a), RingEquiv.apply_symm_apply]`.
-/
theorem frobenius_symm_smul {p : ℕ} {A C : Type} [CommRing A] [CommRing C] [Algebra A C]
    (FA : A ≃+* A) (hFA : ∀ x, FA x = x ^ p) (FC : C ≃+* C) (hFC : ∀ x, FC x = x ^ p)
    (a : A) (c : C) : FC.symm (a • c) = FA.symm a • FC.symm c := by
  apply FC.injective
  rw [RingEquiv.apply_symm_apply, Algebra.smul_def, Algebra.smul_def, map_mul,
    RingEquiv.apply_symm_apply, hFC, ← map_pow (algebraMap A C), ← hFA (FA.symm a),
    RingEquiv.apply_symm_apply]

/- English proof (translation)
Take `⟨g, hg⟩` from `GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p A h.char 1`. Establish `hg' : ∀ x, g x = x ^ p` using `fun x => by rw [hg, pow_one]`. Establish `hb : Function.Bijective g`. Establish `e : (g : A → A) = fun x => x ^ p` using `funext hg'`. Rewrite using `[e]`.

Conclude with `h.bij`. Conclude with `⟨RingEquiv.ofBijective g hb, fun x => by rw [RingEquiv.ofBijective_apply, hg']⟩`.
-/
private theorem exists_ringEquiv_frobenius_of_pf (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (h : Pf p A) :
    ∃ F : A ≃+* A, ∀ x, F x = x ^ p := by
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p A h.char 1
  have hg' : ∀ x, g x = x ^ p := fun x => by rw [hg, pow_one]
  have hb : Function.Bijective g := by
    have e : (g : A → A) = fun x => x ^ p := funext hg'
    rw [e]
    exact h.bij
  exact ⟨RingEquiv.ofBijective g hb, fun x => by rw [RingEquiv.ofBijective_apply, hg']⟩

/- English proof (translation)
Introduce `p _ A _ B _ _ K _ _ hA hB hK`. Take `⟨FA, hFA⟩` from `exists_ringEquiv_frobenius_of_pf p A hA`. Take `⟨FB, hFB⟩` from `exists_ringEquiv_frobenius_of_pf p B hB`. Take `⟨FK, hFK⟩` from `exists_ringEquiv_frobenius_of_pf p K hK`. Establish `hchar : (p : B ⊗[A] K) = 0`.

Establish `h` using `map_natCast (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] K) p`. Rewrite using `[← h, hB.char, map_zero]`. Take `⟨g, hg⟩` from `GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (B ⊗[A] K) hchar 1`. Establish `hg' : ∀ x, g x = x ^ p` using `fun x => by rw [hg, pow_one]`. Set `f : B →+ K →+ B ⊗[A] K` to `AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun k => FB.symm b ⊗ₜ[A] FK.symm k) (fun k k' => by rw [map_add, TensorProduct.tmul_add])) (fun b b' => by`.

Use extensionality with `k`. Simplify using `only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, TensorProduct.add_tmul])`. Establish `hf : ∀ (a : A) (b : B) (k : K), f (a • b) k = f b (a • k)`. Introduce `a b k`. Simplify using `only [f, AddMonoidHom.mk'_apply]`.

Rewrite using `[frobenius_symm_smul FA hFA FB hFB, frobenius_symm_smul FA hFA FK hFK, TensorProduct.smul_tmul]`. Establish `hψ : ∀ x, TensorProduct.liftAddHom f hf (g x) = x`. Introduce `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `tmul b k`. Rewrite using `[hg', Algebra.TensorProduct.tmul_pow, TensorProduct.liftAddHom_tmul]`. Simplify using `only [f, AddMonoidHom.mk'_apply]`. Rewrite using `[← hFB b, ← hFK k, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.

Establish `hgfun : (fun x : B ⊗[A] K => x ^ p) = g` using `funext fun x => (hg' x).symm`. Use `⟨hchar, ?_⟩` and prove the remaining obligations. Rewrite using `[hgfun]`. Use `⟨Function.LeftInverse.injective hψ, ?_⟩` and prove the remaining obligations. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, map_zero g⟩`. Consider the case `tmul b k`. Take `⟨b', hb'⟩` from `hB.bij.2 b`. Take `⟨k', hk'⟩` from `hK.bij.2 k`.

Establish `hb'' : b' ^ p = b` using `hb'`. Establish `hk'' : k' ^ p = k` using `hk'`. Use `⟨b' ⊗ₜ[A] k', ?_⟩` and prove the remaining obligations. Rewrite using `[hg', Algebra.TensorProduct.tmul_pow, hb'', hk'']`. Consider the case `add x y hx hy`.

Take `⟨x', hx'⟩` from `hx`. Take `⟨y', hy'⟩` from `hy`. Conclude with `⟨x' + y', by rw [map_add, hx', hy']⟩`.
-/
theorem pf_tensor : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (B : Type) [CommRing B]
    [Algebra A B] (K : Type) [CommRing K] [Algebra A K], Pf p A → Pf p B → Pf p K →
    Pf p (B ⊗[A] K) := by
  intro p _ A _ B _ _ K _ _ hA hB hK
  obtain ⟨FA, hFA⟩ := exists_ringEquiv_frobenius_of_pf p A hA
  obtain ⟨FB, hFB⟩ := exists_ringEquiv_frobenius_of_pf p B hB
  obtain ⟨FK, hFK⟩ := exists_ringEquiv_frobenius_of_pf p K hK
  have hchar : (p : B ⊗[A] K) = 0 := by
    have h := map_natCast (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] K) p
    rw [← h, hB.char, map_zero]
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Frobenius.exists_ringHom_pow_prime_pow p (B ⊗[A] K) hchar 1
  have hg' : ∀ x, g x = x ^ p := fun x => by rw [hg, pow_one]
  let f : B →+ K →+ B ⊗[A] K :=
    AddMonoidHom.mk' (fun b => AddMonoidHom.mk' (fun k => FB.symm b ⊗ₜ[A] FK.symm k)
      (fun k k' => by rw [map_add, TensorProduct.tmul_add]))
      (fun b b' => by
        ext k
        simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply, map_add, TensorProduct.add_tmul])
  have hf : ∀ (a : A) (b : B) (k : K), f (a • b) k = f b (a • k) := by
    intro a b k
    simp only [f, AddMonoidHom.mk'_apply]
    rw [frobenius_symm_smul FA hFA FB hFB, frobenius_symm_smul FA hFA FK hFK, TensorProduct.smul_tmul]
  have hψ : ∀ x, TensorProduct.liftAddHom f hf (g x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b k =>
      rw [hg', Algebra.TensorProduct.tmul_pow, TensorProduct.liftAddHom_tmul]
      simp only [f, AddMonoidHom.mk'_apply]
      rw [← hFB b, ← hFK k, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hgfun : (fun x : B ⊗[A] K => x ^ p) = g := funext fun x => (hg' x).symm
  refine ⟨hchar, ?_⟩
  rw [hgfun]
  refine ⟨Function.LeftInverse.injective hψ, ?_⟩
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero g⟩
  | tmul b k =>
    obtain ⟨b', hb'⟩ := hB.bij.2 b
    obtain ⟨k', hk'⟩ := hK.bij.2 k
    have hb'' : b' ^ p = b := hb'
    have hk'' : k' ^ p = k := hk'
    refine ⟨b' ⊗ₜ[A] k', ?_⟩
    rw [hg', Algebra.TensorProduct.tmul_pow, hb'', hk'']
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy']⟩

end GlobalTheory.CompanionTheory.PerfectRing
