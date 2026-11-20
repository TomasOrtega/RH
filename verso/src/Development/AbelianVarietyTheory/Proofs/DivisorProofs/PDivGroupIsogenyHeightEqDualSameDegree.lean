import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

section Height

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k]

/- English proof (translation)
Establish `h` using `G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩`. Rewrite `h` using `[Module.rankAtStalk_eq_finrank_of_free]`. Then use the resulting hypothesis.
-/
theorem finrank_level (G : PDivGroup p k) (n : ℕ) : Module.finrank k (G.A n) = p ^ (n * G.height) := by
  have h := G.rank_eq n ⟨⊥, Ideal.isPrime_bot⟩
  rwa [Module.rankAtStalk_eq_finrank_of_free] at h

/- English proof (translation)
Establish `h : (CartierDual.map f : CartierDual k A →ₐ[k] CartierDual k B).toLinearMap = (CartierDual.toDual k B).symm.toLinearMap ∘ₗ ((f : B →ₐ[k] A).toLinearMap.dualMap ∘ₗ (CartierDual.toDual k A).toLinearMap)` using `rfl`. Rewrite using `[h, LinearMap.range_comp, LinearEquiv.finrank_map_eq, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _), LinearMap.finrank_range_dualMap_eq_finrank_range]`.
-/
theorem finrank_range_cartierDual_map {A B : Type} [CommRing A] [CommRing B] [HopfAlgebra k A]
    [HopfAlgebra k B] [Module.Finite k A] [Module.Finite k B] (f : B →ₐc[k] A) :
    Module.finrank k (LinearMap.range (CartierDual.map f : CartierDual k A →ₐ[k] CartierDual k B).toLinearMap) =
      Module.finrank k (LinearMap.range (f : B →ₐ[k] A).toLinearMap) := by
  have h : (CartierDual.map f : CartierDual k A →ₐ[k] CartierDual k B).toLinearMap =
      (CartierDual.toDual k B).symm.toLinearMap ∘ₗ
        ((f : B →ₐ[k] A).toLinearMap.dualMap ∘ₗ (CartierDual.toDual k A).toLinearMap) := rfl
  rw [h, LinearMap.range_comp, LinearEquiv.finrank_map_eq,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _),
    LinearMap.finrank_range_dualMap_eq_finrank_range]

/- English proof (translation)
Take `⟨f, hf, hk⟩` from `G.exists_res_le h`. Establish `hk' : kerIdeal (mulBy k (G.A n) (p ^ m)) = RingHom.ker (f : G.A n →ₐ[k] G.A m)` using `hk.symm`. Rewrite using `[hk', (Ideal.quotientKerAlgEquivOfSurjective (f := (f : G.A n →ₐ[k] G.A m)) hf).toLinearEquiv.finrank_eq, finrank_level]`.
-/
theorem finrank_quot_mulBy (G : PDivGroup p k) {m n : ℕ} (h : m ≤ n) :
    Module.finrank k (G.A n ⧸ kerIdeal (mulBy k (G.A n) (p ^ m))) = p ^ (m * G.height) := by
  obtain ⟨f, hf, hk⟩ := G.exists_res_le h
  have hk' : kerIdeal (mulBy k (G.A n) (p ^ m)) = RingHom.ker (f : G.A n →ₐ[k] G.A m) := hk.symm
  rw [hk', (Ideal.quotientKerAlgEquivOfSurjective (f := (f : G.A n →ₐ[k] G.A m)) hf).toLinearEquiv.finrank_eq,
    finrank_level]

/- English proof (translation)
Establish `key : ∀ n, m ≤ n → p ^ (n * G.height) ≤ p ^ (m * G.height) * p ^ (n * H.height)`. Introduce `n hn`. Establish `hL` using `finrank_eq_ker_mul_range k (G.A n) (G.A n) (mulBy k (G.A n) (p ^ m))`. Rewrite `hL` using `[finrank_quot_mulBy G hn, finrank_level]`. Establish `happ : (q ≫ g).app n = mulBy k (G.A n) (p ^ m)`.

Rewrite using `[hqg, ← natCast_smul_id_app]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hr : LinearMap.range ((mulBy k (G.A n) (p ^ m) : G.A n →ₐ[k] G.A n).toLinearMap) ≤ LinearMap.range ((q.app n : H.A n →ₐ[k] G.A n).toLinearMap)`. Rewrite using `[← happ]`.

Conclude with `LinearMap.range_comp_le_range (g.app n : G.A n →ₐ[k] H.A n).toLinearMap (q.app n : H.A n →ₐ[k] G.A n).toLinearMap`. Establish `h1` using `Submodule.finrank_mono hr`. Establish `h2` using `LinearMap.finrank_range_le ((q.app n : H.A n →ₐ[k] G.A n).toLinearMap)`. Rewrite `h2` using `[finrank_level]`. Rewrite using `[hL]`.

Conclude with `Nat.mul_le_mul_left _ (h1.trans h2)`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h3` using `key (m * G.height + m + 1) (by nlinarith)`. Rewrite `h3` using `[← pow_add]`.

Establish `h4` using `(Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 h3`. Use polynomial arithmetic with `[Nat.mul_le_mul_left (m * G.height + m + 1) hlt]`.
-/
theorem height_le_of_comp_eq {G H : PDivGroup p k} (q : G ⟶ H) (g : H ⟶ G) (m : ℕ)
    (hqg : q ≫ g = (p : ℤ_[p]) ^ m • 𝟙 G) : G.height ≤ H.height := by
  have key : ∀ n, m ≤ n → p ^ (n * G.height) ≤ p ^ (m * G.height) * p ^ (n * H.height) := by
    intro n hn
    have hL := finrank_eq_ker_mul_range k (G.A n) (G.A n) (mulBy k (G.A n) (p ^ m))
    rw [finrank_quot_mulBy G hn, finrank_level] at hL
    have happ : (q ≫ g).app n = mulBy k (G.A n) (p ^ m) := by
      rw [hqg, ← natCast_smul_id_app]
      push_cast
      rfl
    have hr : LinearMap.range ((mulBy k (G.A n) (p ^ m) : G.A n →ₐ[k] G.A n).toLinearMap) ≤
        LinearMap.range ((q.app n : H.A n →ₐ[k] G.A n).toLinearMap) := by
      rw [← happ]
      exact LinearMap.range_comp_le_range (g.app n : G.A n →ₐ[k] H.A n).toLinearMap
        (q.app n : H.A n →ₐ[k] G.A n).toLinearMap
    have h1 := Submodule.finrank_mono hr
    have h2 := LinearMap.finrank_range_le ((q.app n : H.A n →ₐ[k] G.A n).toLinearMap)
    rw [finrank_level] at h2
    rw [hL]
    exact Nat.mul_le_mul_left _ (h1.trans h2)
  by_contra hlt
  push_neg at hlt
  have h3 := key (m * G.height + m + 1) (by nlinarith)
  rw [← pow_add] at h3
  have h4 := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 h3
  nlinarith [Nat.mul_le_mul_left (m * G.height + m + 1) hlt]

/- English proof (translation)
Take `⟨m, g, h1, h2⟩` from `hq`. Establish `hGH : G.height = H.height` using `le_antisymm (height_le_of_comp_eq q g m h1) (height_le_of_comp_eq g q m h2)`. Use `⟨hGH, ⟨m, dualHom H G g, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← dualHom_comp, h2, map_smul, dualHom_id]`. Rewrite using `[← dualHom_comp, h1, map_smul, dualHom_id]`.

Introduce and unpack `e ⟨N, hN⟩`. Use `⟨N, fun n hn => ?_⟩` and prove the remaining obligations. Establish `he` using `hN n hn`. Establish `L1` using `finrank_eq_ker_mul_range k (G.A n) (H.A n) (q.app n)`. Establish `L2` using `finrank_eq_ker_mul_range k (H.dual.A n) (G.dual.A n) ((dualHom G H q).app n)`.

Rewrite `L1` using `[he, finrank_level]`. Rewrite `L2` using `[finrank_level, dualHom_app, finrank_range_cartierDual_map]`. Establish `hr : 0 < Module.finrank k (LinearMap.range (q.app n : H.A n →ₐ[k] G.A n).toLinearMap)`. Break down `Nat.eq_zero_or_pos (Module.finrank k (LinearMap.range (q.app n : H.A n →ₐ[k] G.A n).toLinearMap)) with h0 | h0` into its components or cases. Rewrite `L1` using `[h0, mul_zero]`.

Conclude with `absurd L1 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)`. Conclude with `h0`. Establish `L3 : p ^ (n * H.dual.height) = p ^ (n * G.height)` using `by rw [hGH]`. Rewrite `L3` using `[L1, L2]`. Conclude with `Nat.eq_of_mul_eq_mul_right hr L3`.
-/
theorem height_eq_and_dual_isog (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (q : G ⟶ H) (hq : IsIsog q) :
    G.height = H.height ∧ IsIsog (dualHom G H q) ∧ ∀ e, HasLogDeg q e → HasLogDeg (dualHom G H q) e := by
  obtain ⟨m, g, h1, h2⟩ := hq
  have hGH : G.height = H.height :=
    le_antisymm (height_le_of_comp_eq q g m h1) (height_le_of_comp_eq g q m h2)
  refine ⟨hGH, ⟨m, dualHom H G g, ?_, ?_⟩, ?_⟩
  · rw [← dualHom_comp, h2, map_smul, dualHom_id]
  · rw [← dualHom_comp, h1, map_smul, dualHom_id]
  · rintro e ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have he := hN n hn
    have L1 := finrank_eq_ker_mul_range k (G.A n) (H.A n) (q.app n)
    have L2 := finrank_eq_ker_mul_range k (H.dual.A n) (G.dual.A n) ((dualHom G H q).app n)
    rw [he, finrank_level] at L1
    rw [finrank_level, dualHom_app, finrank_range_cartierDual_map] at L2
    have hr : 0 < Module.finrank k (LinearMap.range (q.app n : H.A n →ₐ[k] G.A n).toLinearMap) := by
      rcases Nat.eq_zero_or_pos (Module.finrank k (LinearMap.range (q.app n : H.A n →ₐ[k] G.A n).toLinearMap))
        with h0 | h0
      · rw [h0, mul_zero] at L1
        exact absurd L1 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
      · exact h0
    have L3 : p ^ (n * H.dual.height) = p ^ (n * G.height) := by rw [hGH]
    rw [L1, L2] at L3
    exact Nat.eq_of_mul_eq_mul_right hr L3

end Height

end GlobalTheory.Dieu
