import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleAnnihilatorEqSelfStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorIntersectionCardStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardComapEqCardKerMulCardRangeInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardEqCardKerMulCardRange

namespace GlobalTheory.CompanionTheory.Counting

/- English proof (translation)
Introduce `n _ H H' P P' _ _ _ _ _ _ _ _ _ _ _ _ B hB hB' loc loc' hR L`. Establish `e1` using `card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H P loc L`. Establish `e2` using `card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H' P' loc' (⨅ x ∈ L, LinearMap.ker (B.flip x))`. Establish `e3` using `card_eq_card_ker_mul_card_range (ZMod n) H P loc`. Establish `hflip : B.flip.flip = B` using `LinearMap.flip_flip B`.

Establish `hdd` using `GlobalTheory.T.double_annihilator_eq_self n P' P B.flip hB' (by rw [hflip]; exact hB) (LinearMap.range loc')`. Rewrite `hdd` using `[hflip, ← hR]`. Establish `e4` using `GlobalTheory.T.annihilator_intersection_card n P P' B hB hB' (LinearMap.range loc) L`. Rewrite `e4` using `[hdd]`. Rewrite using `[e1, e2, e3]`.

Establish `key : Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') * (Nat.card P * Nat.card ↥(LinearMap.range loc ⊓ L)) = Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') * (Nat.card ↥(LinearMap.range loc' ⊓ ⨅ x ∈ L, LinearMap.ker (B.flip x)) * Nat.card ↥(LinearMa …`. Rewrite using `[e4]`. Combine the linear relations using `[key]`.
-/
theorem card_comap_mul_card_ker_mul_card_eq :
    ∀ (n : ℕ) [NeZero n] (H H' P P' : Type) [AddCommGroup H] [Module (ZMod n) H] [Finite H] [AddCommGroup H'] [Module (ZMod n) H'] [Finite H'] [AddCommGroup P] [Module (ZMod n) P] [Finite P] [AddCommGroup P'] [Module (ZMod n) P'] [Finite P'] (B : P' →ₗ[ZMod n] P →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ (loc : H →ₗ[ZMod n] P) (loc' : H' →ₗ[ZMod n] P'), LinearMap.range loc = (⨅ y ∈ LinearMap.range loc', LinearMap.ker (B y)) → ∀ L : Submodule (ZMod n) P, Nat.card ↥(L.comap loc) * Nat.card ↥(LinearMap.ker loc') * Nat.card P = Nat.card ↥((⨅ x ∈ L, LinearMap.ker (B.flip x)).comap loc') * Nat.card H * Nat.card ↥L := by
  intro n _ H H' P P' _ _ _ _ _ _ _ _ _ _ _ _ B hB hB' loc loc' hR L
  have e1 := card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H P loc L
  have e2 := card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H' P' loc'
    (⨅ x ∈ L, LinearMap.ker (B.flip x))
  have e3 := card_eq_card_ker_mul_card_range (ZMod n) H P loc
  have hflip : B.flip.flip = B := LinearMap.flip_flip B
  have hdd := GlobalTheory.T.double_annihilator_eq_self n P' P B.flip hB' (by rw [hflip]; exact hB) (LinearMap.range loc')
  rw [hflip, ← hR] at hdd
  have e4 := GlobalTheory.T.annihilator_intersection_card n P P' B hB hB' (LinearMap.range loc) L
  rw [hdd] at e4
  rw [e1, e2, e3]
  have key : Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') *
      (Nat.card P * Nat.card ↥(LinearMap.range loc ⊓ L)) =
      Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') *
      (Nat.card ↥(LinearMap.range loc' ⊓ ⨅ x ∈ L, LinearMap.ker (B.flip x)) *
        Nat.card ↥(LinearMap.range loc) * Nat.card ↥L) := by
    rw [e4]
  linarith [key]

end GlobalTheory.CompanionTheory.Counting
