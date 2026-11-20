import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MuDvdFrobXiSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WinLift

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h V G0 hP hθ i m`. Establish `ent : ∀ (c : Ainf p O) (i : Fin d ⊕ Fin k) (m : Fin h), (V * blk d k c 1 * G0.map WittVector.frobenius) i m = ∑ l, V i l * (Sum.elim (fun _ => c) (fun _ => (1 : Ainf p O)) l * WittVector.frobenius (G0 l m))`. Introduce `c i m`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [blk, Matrix.mul_diagonal, Matrix.map_apply]`.

Conclude with `Finset.sum_congr rfl fun l _ => by ring`. Establish `h1 : ∀ l, ∃ w : Ainf p O, Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l * WittVector.frobenius (G0 l m) = WittVector.frobenius (xi ε) * w`. Introduce and unpack `(l | l)`. Conclude with `⟨_, rfl⟩`. Establish `hmem : G0 (Sum.inr l) m ∈ RingHom.ker (WittVector.fontaineTheta O p)` using `hθ l m`.

Rewrite `hmem` using `[AinfXi.ker_theta hv ε (root_prim hε), Ideal.mem_span_singleton']`. Take `⟨w, hw⟩` from `hmem`. Conclude with `⟨WittVector.frobenius w, by rw [← hw, map_mul]; simp; ring⟩`. Use `choose w hw using h1`. Establish `hE : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m = WittVector.frobenius (xi ε) * ((∑ l, V i l * w l) - G0 i m)`.

Rewrite using `[ent]`. Repeatedly rewrite using `[hw]`. Rewrite using `[mul_sub, Finset.mul_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun l _ => by ring`.

Establish `hdiff : ∀ l : Fin d ⊕ Fin k, Sandwich.mu ε ∣ Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l - Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l`. Introduce and unpack `(l | l)`. Conclude with `mu_dvd_frob_xi_sub ε`. Simplify using the standard rewrite rules. Establish `hmu : Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m`.

Establish `hPim` using `hP i m`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hPim`. Establish `key : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m - ((V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius) i m - (p : Ainf p O) * G0 i m) = (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (x …`. Rewrite using `[ent, ent]`. Simplify using `only [sub_mul, mul_sub, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hR : Sandwich.mu ε ∣ (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l - Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) * WittVector.frobenius (G0 l m))) - (WittVector.frobenius (xi ε) - p) * G0 i m` using `dvd_sub (Finset.dvd_sum fun l _ => Dvd.dvd.mul_left ((hdiff l).mul_right _) _) ((mu_dvd_frob_xi_sub ε).mul_right _)`. Rewrite `hR` using `[← key]`. Use `dvd_add hR hPim` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Rewrite `hmu`, the goal using `[hE]`. Conclude with `mul_dvd_mul_left _ (mu_dvd_of_xi_mul F _ hmu)`.
-/
theorem lift_solves_div_frob_xi_mu : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (V : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) (G0 : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)), (∀ i m, Sandwich.mu ε ∣ (V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius - (p : Ainf p O) • G0) i m) → (∀ j m, WittVector.fontaineTheta O p (G0 (Sum.inr j) m) = 0) → ∀ i m, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m - WittVector.frobenius (xi ε) * G0 i m := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h V G0 hP hθ i m
  have ent : ∀ (c : Ainf p O) (i : Fin d ⊕ Fin k) (m : Fin h),
      (V * blk d k c 1 * G0.map WittVector.frobenius) i m =
        ∑ l, V i l * (Sum.elim (fun _ => c) (fun _ => (1 : Ainf p O)) l *
          WittVector.frobenius (G0 l m)) := by
    intro c i m
    rw [Matrix.mul_apply]
    simp only [blk, Matrix.mul_diagonal, Matrix.map_apply]
    exact Finset.sum_congr rfl fun l _ => by ring
  have h1 : ∀ l, ∃ w : Ainf p O,
      Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l *
        WittVector.frobenius (G0 l m) = WittVector.frobenius (xi ε) * w := by
    rintro (l | l)
    · exact ⟨_, rfl⟩
    · have hmem : G0 (Sum.inr l) m ∈ RingHom.ker (WittVector.fontaineTheta O p) := hθ l m
      rw [AinfXi.ker_theta hv ε (root_prim hε), Ideal.mem_span_singleton'] at hmem
      obtain ⟨w, hw⟩ := hmem
      exact ⟨WittVector.frobenius w, by rw [← hw, map_mul]; simp; ring⟩
  choose w hw using h1
  have hE : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
      WittVector.frobenius (xi ε) * G0 i m =
        WittVector.frobenius (xi ε) * ((∑ l, V i l * w l) - G0 i m) := by
    rw [ent]
    simp_rw [hw]
    rw [mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  have hdiff : ∀ l : Fin d ⊕ Fin k, Sandwich.mu ε ∣
      Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l -
        Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l := by
    rintro (l | l)
    · exact mu_dvd_frob_xi_sub ε
    · simp
  have hmu : Sandwich.mu ε ∣
      (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
        WittVector.frobenius (xi ε) * G0 i m := by
    have hPim := hP i m
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hPim
    have key : (V * blk d k (WittVector.frobenius (xi ε)) 1 * G0.map WittVector.frobenius) i m -
        WittVector.frobenius (xi ε) * G0 i m -
        ((V * blk d k (p : Ainf p O) 1 * G0.map WittVector.frobenius) i m - (p : Ainf p O) * G0 i m) =
        (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε)) (fun _ => (1 : Ainf p O)) l -
          Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) *
            WittVector.frobenius (G0 l m))) -
        (WittVector.frobenius (xi ε) - p) * G0 i m := by
      rw [ent, ent]
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
      ring
    have hR : Sandwich.mu ε ∣ (∑ l, V i l * ((Sum.elim (fun _ => WittVector.frobenius (xi ε))
        (fun _ => (1 : Ainf p O)) l - Sum.elim (fun _ => (p : Ainf p O)) (fun _ => (1 : Ainf p O)) l) *
          WittVector.frobenius (G0 l m))) - (WittVector.frobenius (xi ε) - p) * G0 i m :=
      dvd_sub (Finset.dvd_sum fun l _ => Dvd.dvd.mul_left ((hdiff l).mul_right _) _)
        ((mu_dvd_frob_xi_sub ε).mul_right _)
    rw [← key] at hR
    have := dvd_add hR hPim
    rwa [sub_add_cancel] at this
  rw [hE] at hmu ⊢
  exact mul_dvd_mul_left _ (mu_dvd_of_xi_mul F _ hmu)

end GlobalTheory.WinLift
