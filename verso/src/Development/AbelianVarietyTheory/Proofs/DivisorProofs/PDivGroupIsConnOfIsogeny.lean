import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerEqRangeOfRangeEqKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu

/- English proof (translation)
Establish `ha' : counit (R` using `k) a = 0 := ha`. Express the relevant statement in the definitionally equal form `counit (R := k) (f a) = 0`. Rewrite using `[CoalgHomClass.counit_comp_apply, ha']`.
-/
theorem mem_augIdeal_map {k A B : Type} [CommRing k] [CommRing A] [CommRing B] [Bialgebra k A]
    [Bialgebra k B] (f : A →ₐc[k] B) {a : A} (ha : a ∈ augIdeal k A) : f a ∈ augIdeal k B := by
  have ha' : counit (R := k) a = 0 := ha
  change counit (R := k) (f a) = 0
  rw [CoalgHomClass.counit_comp_apply, ha']

/- English proof (translation)
Take `⟨N, hN⟩` from `h`. Conclude with `⟨N, hf (by rw [map_pow, hN, map_zero])⟩`.
-/
theorem isNilpotent_of_map_injective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) {a : A} (h : IsNilpotent (f a)) : IsNilpotent a := by
  obtain ⟨N, hN⟩ := h
  exact ⟨N, hf (by rw [map_pow, hN, map_zero])⟩

/- English proof (translation)
Introduce `n b hb`. Take `⟨c, rfl⟩` from `H.res_surjective n b`. Establish `hc : c ∈ augIdeal k (H.A (n + 1))`. Establish `hb' : counit (R` using `k) (H.res n c) = 0 := hb`. Express the relevant statement in the definitionally equal form `counit (R := k) c = 0`.

Rewrite `hb'` using `[CoalgHomClass.counit_comp_apply]`. Then use the resulting hypothesis. Establish `h1` using `h (n + 1) c hc`. Rewrite `h1` using `[pow_succ', ← mulBy_mulBy, ← H.mulP_res, map_mulBy]`. Take `⟨ρ, hρ⟩` from `HTPair.exists_retraction_mulP H n`. Establish `hinj : Function.Injective (H.mulP n : H.A n →ₐ[k] H.A (n + 1))` using `Function.LeftInverse.injective hρ`.

Conclude with `isNilpotent_of_map_injective (H.mulP n : H.A n →ₐ[k] H.A (n + 1)).toRingHom hinj h1`.
-/
theorem nil_mulBy_pow_of_succ {p : ℕ} {k : Type} [Field k] (H : PDivGroup p k) (j : ℕ)
    (h : ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ (j + 1)) b)) :
    ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ j) b) := by
  intro n b hb
  obtain ⟨c, rfl⟩ := H.res_surjective n b
  have hc : c ∈ augIdeal k (H.A (n + 1)) := by
    have hb' : counit (R := k) (H.res n c) = 0 := hb
    change counit (R := k) c = 0
    rwa [CoalgHomClass.counit_comp_apply] at hb'
  have h1 := h (n + 1) c hc
  rw [pow_succ', ← mulBy_mulBy, ← H.mulP_res, map_mulBy] at h1
  obtain ⟨ρ, hρ⟩ := HTPair.exists_retraction_mulP H n
  have hinj : Function.Injective (H.mulP n : H.A n →ₐ[k] H.A (n + 1)) :=
    Function.LeftInverse.injective hρ
  exact isNilpotent_of_map_injective (H.mulP n : H.A n →ₐ[k] H.A (n + 1)).toRingHom hinj h1

/- English proof (translation)
Introduce `p _ k _ _ G H q hq hG`. Take `⟨m, q', -, h2⟩` from `hq`. Establish `hm : ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ m) b)`. Introduce `n b hb`. Establish `e : mulBy k (H.A n) (p ^ m) = (q'.app n).comp (q.app n)`.

Rewrite using `[← natCast_smul_id_app H (p ^ m) n, Nat.cast_pow, ← h2]`. Both sides reduce to the same expression. Rewrite using `[e, BialgHom.comp_apply]`. Conclude with `(hG n _ (mem_augIdeal_map _ hb)).map (q'.app n : G.A n →ₐ[k] H.A n)`. Establish `key : ∀ j, (∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ j) b)) → ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ 0) b)`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact id`. Consider the case `succ j ih => exact fun h => ih (nil_mulBy_pow_of_succ H j h)`. Introduce `n b hb`.

Establish `h0` using `key m hm n b hb`. Establish `e1 : mulBy k (H.A n) (p ^ 0) b = b`. Rewrite using `[pow_zero, mulBy, pow_one]`. Both sides reduce to the same expression. Rewrite `h0` using `[e1]`. Then use the resulting hypothesis.
-/
theorem isConn_of_isIsog : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (G H : PDivGroup p k) (q : G ⟶ H), IsIsog q → G.IsConn → H.IsConn := by
  intro p _ k _ _ G H q hq hG
  obtain ⟨m, q', -, h2⟩ := hq
  have hm : ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ m) b) := by
    intro n b hb
    have e : mulBy k (H.A n) (p ^ m) = (q'.app n).comp (q.app n) := by
      rw [← natCast_smul_id_app H (p ^ m) n, Nat.cast_pow, ← h2]
      rfl
    rw [e, BialgHom.comp_apply]
    exact (hG n _ (mem_augIdeal_map _ hb)).map (q'.app n : G.A n →ₐ[k] H.A n)
  have key : ∀ j, (∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ j) b)) →
      ∀ n, ∀ b ∈ augIdeal k (H.A n), IsNilpotent (mulBy k (H.A n) (p ^ 0) b) := by
    intro j
    induction j with
    | zero => exact id
    | succ j ih => exact fun h => ih (nil_mulBy_pow_of_succ H j h)
  intro n b hb
  have h0 := key m hm n b hb
  have e1 : mulBy k (H.A n) (p ^ 0) b = b := by
    rw [pow_zero, mulBy, pow_one]
    rfl
  rwa [e1] at h0

end GlobalTheory.Dieu
