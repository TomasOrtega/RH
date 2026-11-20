import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHopfQuotientTorsionIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFibreDimQuotientPDivGroupLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveRankAtStalkOfConstFibreDimStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory.HTPair

/- English proof (translation)
Introduce `p _ O _ _ _ G τ`. Establish `hex` using `fun m => GlobalTheory.T.exists_hopf_quotient_ker_eq_torsionIdeal O (τ.B m) (p ^ m)`. Use `choose D iR iH iC q hq hk using hex`. Use `letI := iR`. Use `letI := iH`.

Use `letI := iC`. Establish `hB1 : ∀ m (x : PrimeSpectrum O), fibreDim (τ.B m ⧸ torsionIdeal O (τ.B m) (p ^ m)) x = p ^ (m * G.height)`. Introduce `m x`. Establish `h` using `GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel p O G 1 m le_rfl (τ.B m)`. Rewrite `h` using `[show 1 + m = m + 1 from Nat.add_comm 1 m]`.

Conclude with `h (τ.j m) (τ.ρ m) (τ.ρ_j m) (τ.tors_le m) x`. Establish `hB2 : ∀ m (x : PrimeSpectrum O), fibreDim (τ.B (m + 1) ⧸ torsionIdeal O (τ.B (m + 1)) (p ^ m)) x = p ^ (m * G.height)`. Introduce `m x`. Establish `h` using `GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel p O G 2 m (by norm_num) (τ.B (m + 1))`. Rewrite `h` using `[show 2 + m = m + 1 + 1 by omega]`.

Conclude with `h (τ.j (m + 1)) (τ.ρ (m + 1)) (τ.ρ_j (m + 1)) (τ.tors_le (m + 1)) x`. Use `haveI hfin : ∀ m, Module.Finite O (D m) := fun m => Module.Finite.of_surjective (q m : τ.B m →ₗ[O] D m) (hq m)`. Establish `hD : ∀ m (x : PrimeSpectrum O), fibreDim (D m) x = p ^ (m * G.height)`. Introduce `m x`. Establish `hk' : RingHom.ker (q m : τ.B m →ₐ[O] D m) = torsionIdeal O (τ.B m) (p ^ m)` using `hk m`.

Establish `e` using `((Ideal.quotientEquivAlgOfEq O hk').symm.trans (Ideal.quotientKerAlgEquivOfSurjective (f := (q m : τ.B m →ₐ[O] D m)) (hq m))).toLinearEquiv`. Rewrite using `[← hB1 m x]`. Conclude with `(fibreDim_congr e x).symm`. Establish `hPR` using `fun m => GlobalTheory.T.projective_rankAtStalk_of_const_fibreDim O (D m) (p ^ (m * G.height)) (hD m)`. Use `haveI hproj : ∀ m, Module.Projective O (D m) := fun m => (hPR m).1`.

Establish `hle : ∀ m, RingHom.ker (q (m + 1)) ≤ RingHom.ker ((q m).comp (τ.r m))`. Introduce `m b hb`. Rewrite `hb` using `[hk]`. Establish `h1 : τ.r m b ∈ torsionIdeal O (τ.B m) (p ^ (m + 1))`. Rewrite using `[← map_torsionIdeal (τ.r_surjective m)]`.

Conclude with `Ideal.mem_map_of_mem (τ.r m : τ.B (m + 1) →ₐ[O] τ.B m) hb`. Establish `h2 : τ.r m b ∈ RingHom.ker (q m)`. Rewrite using `[hk]`. Conclude with `torsionIdeal_le_of_dvd (pow_dvd_pow p (Nat.le_succ m)) h1`. Rewrite `h2`, the goal using `[RingHom.mem_ker]`.

Conclude with `h2`. Set `res` to `fun m => liftSurj (q (m + 1)) (hq (m + 1)) ((q m).comp (τ.r m)) (hle m)`. Establish `hres : ∀ m b, res m (q (m + 1) b) = q m (τ.r m b)` using `fun m b => liftSurj_apply ..`. Establish `hres_surj : ∀ m, Function.Surjective (res m)`. Introduce `m d`.

Take `⟨c, rfl⟩` from `hq m d`. Take `⟨b, rfl⟩` from `τ.r_surjective m c`. Conclude with `⟨_, hres m b⟩`. Establish `hker : ∀ m, RingHom.ker (res m) = torsionIdeal O (D (m + 1)) (p ^ m)`. Introduce `m`.

Use `ker_eq_of_fibreDim_eq (res m : D (m + 1) →ₐ[O] D m) (hres_surj m) _ ?_ fun x => ?_` and prove the remaining obligations. Rewrite using `[← map_torsionIdeal (hq (m + 1))]`. Use `Ideal.map_le_iff_le_comap.2 fun b hb => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `res m (q (m + 1) b) = 0`.

Rewrite using `[hres, ← RingHom.mem_ker, hk, ← map_torsionIdeal (τ.r_surjective m)]`. Conclude with `Ideal.mem_map_of_mem (τ.r m : τ.B (m + 1) →ₐ[O] τ.B m) hb`. Set `φ : τ.B (m + 1) →ₐ[O] D (m + 1) ⧸ torsionIdeal O (D (m + 1)) (p ^ m)` to `(Ideal.Quotient.mkₐ O _).comp (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1))`. Establish `hφ : Function.Surjective φ` using `(Ideal.Quotient.mkₐ_surjective O _).comp (hq (m + 1))`. Establish `hkφ : RingHom.ker φ = torsionIdeal O (τ.B (m + 1)) (p ^ m)`.

Use extensionality with `b`. Rewrite using `[RingHom.mem_ker]`. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (q (m + 1) b) = 0 ↔ _`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, ← map_torsionIdeal (hq (m + 1))]`. Prove the components needed by the constructor for the conclusion.

Introduce `hb`. Take `⟨c, hc, e⟩` from `(Ideal.mem_map_iff_of_surjective (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1)) (hq (m + 1))).1 hb`. Establish `h3 : b - c ∈ RingHom.ker (q (m + 1))`. Rewrite using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Conclude with `e.symm`.

Rewrite `h3` using `[hk]`. Establish `h4` using `torsionIdeal_le_of_dvd (R := O) (A := τ.B (m + 1)) (pow_dvd_pow p (Nat.le_succ m)) h3`. Simplify using `using Ideal.add_mem _ h4 hc`. Introduce `hb`. Conclude with `Ideal.mem_map_of_mem (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1)) hb`.

Establish `e` using `((Ideal.quotientEquivAlgOfEq O hkφ).symm.trans (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv`. Rewrite using `[hD, ← hB2 m x]`. Conclude with `(fibreDim_congr e x).symm`. Set `H : PDivGroup p O` to `{ height := G.height A := D commRing := iR hopf := iH cocomm := iC finite := hfin projective := hproj rank_eq := fun m x => (hPR m).2 x res := res res_surjective := hres_surj ker_res := hker }`. Conclude with `⟨H, q, hq, hk, hres⟩`.
-/
theorem exists_quotPDivGroup : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O]
    [IsLocalRing O] (G : PDivGroup p O) (τ : QuotTower G), ∃ (H : PDivGroup p O)
    (q : ∀ m, τ.B m →ₐc[O] H.A m), (∀ m, Function.Surjective (q m)) ∧
    (∀ m, RingHom.ker (q m) = torsionIdeal O (τ.B m) (p ^ m)) ∧
    ∀ m b, H.res m (q (m + 1) b) = q m (τ.r m b) := by
  intro p _ O _ _ _ G τ
  have hex := fun m => GlobalTheory.T.exists_hopf_quotient_ker_eq_torsionIdeal O (τ.B m) (p ^ m)
  choose D iR iH iC q hq hk using hex
  letI := iR
  letI := iH
  letI := iC
  have hB1 : ∀ m (x : PrimeSpectrum O),
      fibreDim (τ.B m ⧸ torsionIdeal O (τ.B m) (p ^ m)) x = p ^ (m * G.height) := by
    intro m x
    have h := GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel p O G 1 m le_rfl (τ.B m)
    rw [show 1 + m = m + 1 from Nat.add_comm 1 m] at h
    exact h (τ.j m) (τ.ρ m) (τ.ρ_j m) (τ.tors_le m) x
  have hB2 : ∀ m (x : PrimeSpectrum O),
      fibreDim (τ.B (m + 1) ⧸ torsionIdeal O (τ.B (m + 1)) (p ^ m)) x = p ^ (m * G.height) := by
    intro m x
    have h := GlobalTheory.T.torsion_fibreDim_quotient_pDivGroupLevel p O G 2 m (by norm_num) (τ.B (m + 1))
    rw [show 2 + m = m + 1 + 1 by omega] at h
    exact h (τ.j (m + 1)) (τ.ρ (m + 1)) (τ.ρ_j (m + 1)) (τ.tors_le (m + 1)) x
  haveI hfin : ∀ m, Module.Finite O (D m) := fun m =>
    Module.Finite.of_surjective (q m : τ.B m →ₗ[O] D m) (hq m)
  have hD : ∀ m (x : PrimeSpectrum O), fibreDim (D m) x = p ^ (m * G.height) := by
    intro m x
    have hk' : RingHom.ker (q m : τ.B m →ₐ[O] D m) = torsionIdeal O (τ.B m) (p ^ m) := hk m
    have e := ((Ideal.quotientEquivAlgOfEq O hk').symm.trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := (q m : τ.B m →ₐ[O] D m)) (hq m))).toLinearEquiv
    rw [← hB1 m x]
    exact (fibreDim_congr e x).symm
  have hPR := fun m => GlobalTheory.T.projective_rankAtStalk_of_const_fibreDim O (D m) (p ^ (m * G.height)) (hD m)
  haveI hproj : ∀ m, Module.Projective O (D m) := fun m => (hPR m).1
  have hle : ∀ m, RingHom.ker (q (m + 1)) ≤ RingHom.ker ((q m).comp (τ.r m)) := by
    intro m b hb
    rw [hk] at hb
    have h1 : τ.r m b ∈ torsionIdeal O (τ.B m) (p ^ (m + 1)) := by
      rw [← map_torsionIdeal (τ.r_surjective m)]
      exact Ideal.mem_map_of_mem (τ.r m : τ.B (m + 1) →ₐ[O] τ.B m) hb
    have h2 : τ.r m b ∈ RingHom.ker (q m) := by
      rw [hk]
      exact torsionIdeal_le_of_dvd (pow_dvd_pow p (Nat.le_succ m)) h1
    rw [RingHom.mem_ker] at h2 ⊢
    exact h2
  let res := fun m => liftSurj (q (m + 1)) (hq (m + 1)) ((q m).comp (τ.r m)) (hle m)
  have hres : ∀ m b, res m (q (m + 1) b) = q m (τ.r m b) := fun m b => liftSurj_apply ..
  have hres_surj : ∀ m, Function.Surjective (res m) := by
    intro m d
    obtain ⟨c, rfl⟩ := hq m d
    obtain ⟨b, rfl⟩ := τ.r_surjective m c
    exact ⟨_, hres m b⟩
  have hker : ∀ m, RingHom.ker (res m) = torsionIdeal O (D (m + 1)) (p ^ m) := by
    intro m
    refine ker_eq_of_fibreDim_eq (res m : D (m + 1) →ₐ[O] D m) (hres_surj m) _ ?_ fun x => ?_
    · rw [← map_torsionIdeal (hq (m + 1))]
      refine Ideal.map_le_iff_le_comap.2 fun b hb => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change res m (q (m + 1) b) = 0
      rw [hres, ← RingHom.mem_ker, hk, ← map_torsionIdeal (τ.r_surjective m)]
      exact Ideal.mem_map_of_mem (τ.r m : τ.B (m + 1) →ₐ[O] τ.B m) hb
    · let φ : τ.B (m + 1) →ₐ[O] D (m + 1) ⧸ torsionIdeal O (D (m + 1)) (p ^ m) :=
        (Ideal.Quotient.mkₐ O _).comp (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1))
      have hφ : Function.Surjective φ :=
        (Ideal.Quotient.mkₐ_surjective O _).comp (hq (m + 1))
      have hkφ : RingHom.ker φ = torsionIdeal O (τ.B (m + 1)) (p ^ m) := by
        ext b
        rw [RingHom.mem_ker]
        change Ideal.Quotient.mk _ (q (m + 1) b) = 0 ↔ _
        rw [Ideal.Quotient.eq_zero_iff_mem, ← map_torsionIdeal (hq (m + 1))]
        constructor
        · intro hb
          obtain ⟨c, hc, e⟩ := (Ideal.mem_map_iff_of_surjective
            (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1)) (hq (m + 1))).1 hb
          have h3 : b - c ∈ RingHom.ker (q (m + 1)) := by
            rw [RingHom.mem_ker, map_sub, sub_eq_zero]
            exact e.symm
          rw [hk] at h3
          have h4 := torsionIdeal_le_of_dvd (R := O) (A := τ.B (m + 1))
            (pow_dvd_pow p (Nat.le_succ m)) h3
          simpa using Ideal.add_mem _ h4 hc
        · intro hb
          exact Ideal.mem_map_of_mem (q (m + 1) : τ.B (m + 1) →ₐ[O] D (m + 1)) hb
      have e := ((Ideal.quotientEquivAlgOfEq O hkφ).symm.trans
        (Ideal.quotientKerAlgEquivOfSurjective hφ)).toLinearEquiv
      rw [hD, ← hB2 m x]
      exact (fibreDim_congr e x).symm
  let H : PDivGroup p O :=
    { height := G.height
      A := D
      commRing := iR
      hopf := iH
      cocomm := iC
      finite := hfin
      projective := hproj
      rank_eq := fun m x => (hPR m).2 x
      res := res
      res_surjective := hres_surj
      ker_res := hker }
  exact ⟨H, q, hq, hk, hres⟩

end GlobalTheory.HTPair
