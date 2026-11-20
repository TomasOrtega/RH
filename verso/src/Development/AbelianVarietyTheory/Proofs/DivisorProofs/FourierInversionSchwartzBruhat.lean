import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSecAlgTop
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped TensorProduct

/- English proof (translation)
Establish `hsum : ∀ c : Fin r → R, ∑ k, c k • Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k) = Ideal.Quotient.mk (RingHom.ker κ) (∑ k, c k ⊗ₜ[A] v k)`. Introduce `c`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `h1 : c k • ((1 : R) ⊗ₜ[A] v k) = c k ⊗ₜ[A] v k`.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[← h1]`. Conclude with `(map_smul (Ideal.Quotient.mkₐ R (RingHom.ker κ)) (c k) ((1 : R) ⊗ₜ[A] v k)).symm`. Establish `hker : ∀ x y : R ⊗[A] B, Ideal.Quotient.mk (RingHom.ker κ) x = Ideal.Quotient.mk (RingHom.ker κ) y ↔ κ x = κ y`. Introduce `x y`.

Rewrite using `[Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]`. Establish `hsub : ∀ c c' : Fin r → R, ∑ k, (c - c') k ⊗ₜ[A] v k = ∑ k, c k ⊗ₜ[A] v k - ∑ k, c' k ⊗ₜ[A] v k`. Introduce `c c'`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[Pi.sub_apply, TensorProduct.sub_tmul]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hinj, hsurj⟩`. Use `⟨fun s => ?_, ?_, ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `hsurj s`.

Conclude with `⟨_, hc⟩`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Rewrite `hg` using `[hsum, show (0 : (R ⊗[A] B) ⧸ RingHom.ker κ) = Ideal.Quotient.mk (RingHom.ker κ) 0 from (map_zero _).symm, hker]`. Establish `h0 : (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) g = (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) 0`.

Simplify using `only [Pi.zero_apply, TensorProduct.zero_tmul, Finset.sum_const_zero, map_zero]`. Simplify using `using hg`. Introduce `i`. Rewrite using `[hinj h0]`. Both sides reduce to the same expression.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨c, hc⟩` from `hsurj (κ t)`. Rewrite using `[Submodule.mem_span_range_iff_exists_fun]`.

Conclude with `⟨c, by rw [hsum, hker]; exact hc⟩`. Introduce and unpack `⟨hsurj, hli, hspan⟩`. Use `⟨fun c c' h => ?_, fun s => ?_⟩` and prove the remaining obligations. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Establish `h2` using `hli (c - c') (by`.

Rewrite using `[hsum, show (0 : (R ⊗[A] B) ⧸ RingHom.ker κ) = Ideal.Quotient.mk (RingHom.ker κ) 0 from (map_zero _).symm, hker, hsub, map_sub, map_zero, sub_eq_zero]`. Conclude with `h)`. Use function extensionality and compare the values at `i`. Conclude with `sub_eq_zero.mp (h2 i)`. Take `⟨t, rfl⟩` from `hsurj s`.

Establish `hm : Ideal.Quotient.mk (RingHom.ker κ) t ∈ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)))`. Rewrite using `[hspan]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `hm` using `[Submodule.mem_span_range_iff_exists_fun]`. Take `⟨c, hc⟩` from `hm`.

Rewrite `hc` using `[hsum, hker]`. Conclude with `⟨c, hc⟩`.
-/
theorem GlobalTheory.tensorSum_bijective_iff (A B R S : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] [CommRing S] (κ : R ⊗[A] B →+* S) {r : ℕ} (v : Fin r → B) :
    Function.Bijective (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) ↔ (Function.Surjective κ ∧ LinearIndependent R (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) = ⊤) := by
  have hsum : ∀ c : Fin r → R, ∑ k, c k • Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)
      = Ideal.Quotient.mk (RingHom.ker κ) (∑ k, c k ⊗ₜ[A] v k) := by
    intro c
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : c k • ((1 : R) ⊗ₜ[A] v k) = c k ⊗ₜ[A] v k := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [← h1]
    exact (map_smul (Ideal.Quotient.mkₐ R (RingHom.ker κ)) (c k) ((1 : R) ⊗ₜ[A] v k)).symm
  have hker : ∀ x y : R ⊗[A] B, Ideal.Quotient.mk (RingHom.ker κ) x = Ideal.Quotient.mk (RingHom.ker κ) y ↔ κ x = κ y := by
    intro x y
    rw [Ideal.Quotient.eq, RingHom.mem_ker, map_sub, sub_eq_zero]
  have hsub : ∀ c c' : Fin r → R, ∑ k, (c - c') k ⊗ₜ[A] v k = ∑ k, c k ⊗ₜ[A] v k - ∑ k, c' k ⊗ₜ[A] v k := by
    intro c c'
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.sub_apply, TensorProduct.sub_tmul]
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun s => ?_, ?_, ?_⟩
    · obtain ⟨c, hc⟩ := hsurj s
      exact ⟨_, hc⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [hsum, show (0 : (R ⊗[A] B) ⧸ RingHom.ker κ) = Ideal.Quotient.mk (RingHom.ker κ) 0 from (map_zero _).symm,
        hker] at hg
      have h0 : (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) g = (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) 0 := by
        simp only [Pi.zero_apply, TensorProduct.zero_tmul, Finset.sum_const_zero, map_zero]
        simpa using hg
      intro i
      rw [hinj h0]
      rfl
    · rw [eq_top_iff]
      intro x _
      obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨c, hc⟩ := hsurj (κ t)
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨c, by rw [hsum, hker]; exact hc⟩
  · rintro ⟨hsurj, hli, hspan⟩
    refine ⟨fun c c' h => ?_, fun s => ?_⟩
    · rw [Fintype.linearIndependent_iff] at hli
      have h2 := hli (c - c') (by
        rw [hsum, show (0 : (R ⊗[A] B) ⧸ RingHom.ker κ) = Ideal.Quotient.mk (RingHom.ker κ) 0 from (map_zero _).symm,
          hker, hsub, map_sub, map_zero, sub_eq_zero]
        exact h)
      funext i
      exact sub_eq_zero.mp (h2 i)
    · obtain ⟨t, rfl⟩ := hsurj s
      have hm : Ideal.Quotient.mk (RingHom.ker κ) t ∈ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) := by
        rw [hspan]; trivial
      rw [Submodule.mem_span_range_iff_exists_fun] at hm
      obtain ⟨c, hc⟩ := hm
      rw [hsum, hker] at hc
      exact ⟨c, hc⟩

/- English proof (translation)
The claim follows from `GlobalTheory.tensorSum_bijective_iff`.
-/
example : ∀ (A B R S : Type) [CommRing A] [CommRing B] [Algebra A B] [CommRing R] [Algebra A R] [CommRing S] (κ : R ⊗[A] B →+* S) {r : ℕ} (v : Fin r → B), Function.Bijective (fun c : Fin r → R => κ (∑ k, c k ⊗ₜ[A] v k)) ↔ (Function.Surjective κ ∧ LinearIndependent R (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k)) ∧ Submodule.span R (Set.range (fun k => Ideal.Quotient.mk (RingHom.ker κ) ((1 : R) ⊗ₜ[A] v k))) = ⊤) := GlobalTheory.tensorSum_bijective_iff
