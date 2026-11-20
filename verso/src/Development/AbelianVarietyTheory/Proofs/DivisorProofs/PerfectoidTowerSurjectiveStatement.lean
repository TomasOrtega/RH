import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectoidTowerSurjective
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
open Ideal WittVector
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPerfectoidTowerSurjective.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.perfectoid_tower_surjective : ∀ (p : ℕ) [Fact p.Prime] (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (Ideal.span {(p : R)}) R] (φ : A →+* R), (p : A) ≠ 0 → Function.Surjective ((Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ) → RingHom.ker ((Ideal.Quotient.mk (Ideal.span {(p : R)})).comp φ) = Ideal.span {(p : A)} → ∀ π : ℕ → A, π 0 = p → (∀ n, π (n + 1) ^ p = π n) → (∀ (n : ℕ) (x : A), (p : A) ∣ x ^ (p ^ n) → π n ∣ x) → ∃ pflat : PreTilt R p, PreTilt.untilt pflat = (p : R) ∧ ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → pflat ∣ c := by
  first | exact @GlobalTheory.pflat_dvd_of_roots | exact GlobalTheory.pflat_dvd_of_roots | (intros; apply GlobalTheory.pflat_dvd_of_roots <;> assumption)
