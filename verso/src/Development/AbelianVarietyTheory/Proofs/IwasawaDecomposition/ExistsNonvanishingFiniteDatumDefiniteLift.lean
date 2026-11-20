import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.AdjDatumNe

open GlobalTheory.AdelicLatMove GlobalTheory.PlaceVec

def rectOne (R : Type) [Zero R] [One R] (b a : ℕ) : Matrix (Fin b) (Fin a) R :=
  fun i j => if i.val = j.val then 1 else 0

/- English proof (translation)
Introduce `i j hi hj` and use `if_neg (by omega)`.
-/
theorem lowZero_rectOne (R : Type) [Zero R] [One R] (b a k : ℕ) : LowZero k (rectOne R b a) :=
  fun i j hi hj => if_neg (by omega)

/- English proof (translation)
Use extensionality with `i j`. Establish `h1 : i.val < b ∧ j.val < a` using `⟨by omega, j.2⟩`. Unfold `topL rectOne`. Rewrite using `[dif_pos h1, Matrix.one_apply]`. Simplify using `only [Fin.ext_iff]`.
-/
theorem topL_rectOne (R : Type) [Zero R] [One R] {b a : ℕ} (h : a ≤ b) : topL a (rectOne R b a) = 1 := by
  ext i j
  have h1 : i.val < b ∧ j.val < a := ⟨by omega, j.2⟩
  unfold topL rectOne
  rw [dif_pos h1, Matrix.one_apply]
  simp only [Fin.ext_iff]

/- English proof (translation)
Establish `hG' : G' * G = 1` using `mul_eq_one_comm.1 hG`. Establish `hH' : H' * H = 1` using `mul_eq_one_comm.1 hH`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sandwich_cancel' {R : Type} [CommRing R] {m n : ℕ} (A A' G G' : Matrix (Fin m) (Fin m) R)
    (B B' H H' : Matrix (Fin n) (Fin n) R) (N : Matrix (Fin m) (Fin n) R) (c : R) (hA : A' * A = 1) (hG : G * G' = 1)
    (hB : B' * B = 1) (hH : H * H' = 1) : (A' * G') * (c • ((G * A) * N * (B' * H'))) * (H * B) = c • N := by
  have hG' : G' * G = 1 := mul_eq_one_comm.1 hG
  have hH' : H' * H = 1 := mul_eq_one_comm.1 hH
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc _ = (A' * (G' * G) * A) * N * (B' * (H' * H) * B) := by simp only [Matrix.mul_assoc]
    _ = N := by rw [hG', hH', Matrix.mul_one, Matrix.mul_one, hA, hB, Matrix.one_mul, Matrix.mul_one]

variable {D : D7}

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, RingHom.map_zero _⟩`. Consider the case `tmul x α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] x, rfl⟩`. Consider the case `add x y hx hy`. Take `⟨s, hs⟩` from `hx`.

Take `⟨t, ht⟩` from `hy`. Conclude with `⟨s + t, by rw [RingHom.map_add, hs, ht]⟩`.
-/
theorem toEAf_surjective (z : EAf D) : ∃ w : AE D, toEAf D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul x α => exact ⟨pairA D.host.F 0 α ⊗ₜ[D.host.F] x, rfl⟩
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨t, ht⟩ := hy
    exact ⟨s + t, by rw [RingHom.map_add, hs, ht]⟩

/- English proof (translation)
Use `choose N hN using fun (i : Fin S.rank) (j : Fin T.rank) => toEAf_surjective (((S.gram.map (eToEAf D) * βS.val) * I * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) i j)`. Use `⟨Matrix.of fun j i => cA D (e * N i j), fun j i => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cA D e * cA D (e * N i j) = cA D (e * N i j)`. Rewrite using `[← RingHom.map_mul, ← mul_assoc, he]`. Rewrite using `[frMapAdj_eq, ← sandwich_cancel' _ _ _ _ _ _ _ _ I (toEAf D e) βS.inv_mul (gram_map_mul_inv S) βT.inv_mul (gram_map_mul_inv T)]`.

Use `congr 2`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cF D (toEAf D (cA D (e * N i j))) = toEAf D e * _`. Rewrite using `[toEAf_cA, cF_cF_toEAf, RingHom.map_mul, hN]`.
-/
theorem exists_half_frMapAdj (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    {e : AE D} (he : e * e = e) (I : Matrix (Fin S.rank) (Fin T.rank) (EAf D)) :
    ∃ x : WO S T, IsHalf (cA D e) x ∧ frMapAdj S T βS βT x = toEAf D e • I := by
  choose N hN using fun (i : Fin S.rank) (j : Fin T.rank) => toEAf_surjective
    (((S.gram.map (eToEAf D) * βS.val) * I * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) i j)
  refine ⟨Matrix.of fun j i => cA D (e * N i j), fun j i => ?_, ?_⟩
  · change cA D e * cA D (e * N i j) = cA D (e * N i j)
    rw [← RingHom.map_mul, ← mul_assoc, he]
  · rw [frMapAdj_eq, ← sandwich_cancel' _ _ _ _ _ _ _ _ I (toEAf D e) βS.inv_mul (gram_map_mul_inv S) βT.inv_mul
      (gram_map_mul_inv T)]
    congr 2
    refine Matrix.ext fun i j => ?_
    change cF D (toEAf D (cA D (e * N i j))) = toEAf D e * _
    rw [toEAf_cA, cF_cF_toEAf, RingHom.map_mul, hN]

/- English proof (translation)
Establish `he` using `idemSum_mul_self h`. Establish `hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))`. Use `⟨hi, fun PP hPP => ?_⟩` and prove the remaining obligations. Take `⟨⟨es, h1, h2⟩, -⟩` from `h`. Establish `h3 : es PP * ∑ j ∈ P, es j = es PP` using `GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij => (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h => hij (isIdemAt_inj (h1 j hj) (h ▸ h1 i hi))) hPP`.

Rewrite `h3` using `[← h2]`. Take `⟨k, hk⟩` from `GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)`. Establish `h4 : (⟨toEAf D (es PP), k⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D e, hi⟩ = ⟨toEAf D (es PP), k⟩` using `Subtype.ext (by change toEAf D (es PP) * toEAf D e = toEAf D (es PP); rw [← RingHom.map_mul, h3])`. Establish `h5` using `congrArg (Formalism.L2.DIV.resS D.host.F PP) h4`. Rewrite `h5` using `[RingHom.map_mul, hk, one_mul]`. Then use the resulting hypothesis.
-/
theorem idemSum_res {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    ∃ hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      ∀ PP ∈ P, Formalism.L2.DIV.resS D.host.F PP ⟨toEAf D e, hi⟩ = 1 := by
  have he := idemSum_mul_self h
  have hi : toEAf D e ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he]))
  refine ⟨hi, fun PP hPP => ?_⟩
  obtain ⟨⟨es, h1, h2⟩, -⟩ := h
  have h3 : es PP * ∑ j ∈ P, es j = es PP :=
    GlobalTheory.PlaceModelSum.mul_sum_orth (fun i hi => (h1 i hi).1) (fun i hi j hj hij =>
      (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (h1 i hi).1 (h1 j hj).1).resolve_left fun h =>
        hij (isIdemAt_inj (h1 j hj) (h ▸ h1 i hi))) hPP
  rw [← h2] at h3
  obtain ⟨k, hk⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D _ _ (h1 PP hPP)
  have h4 : (⟨toEAf D (es PP), k⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨toEAf D e, hi⟩ = ⟨toEAf D (es PP), k⟩ :=
    Subtype.ext (by change toEAf D (es PP) * toEAf D e = toEAf D (es PP); rw [← RingHom.map_mul, h3])
  have h5 := congrArg (Formalism.L2.DIV.resS D.host.F PP) h4
  rwa [RingHom.map_mul, hk, one_mul] at h5

/- English proof (translation)
Introduce `i j`. Express the relevant statement in the definitionally equal form `ε * (if i.val = j.val then 1 else 0) ∈ _`. Use `split_ifs`. Rewrite using `[mul_one]` and apply the resulting hypothesis. Rewrite using `[mul_zero]`.

Conclude with `zero_mem _`.
-/
theorem isIntM_smul_rectOne {ε : EAf D} (hi : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (b a : ℕ) :
    IsIntM (ε • rectOne (EAf D) b a) := by
  intro i j
  change ε * (if i.val = j.val then 1 else 0) ∈ _
  split_ifs
  · rwa [mul_one]
  · rw [mul_zero]; exact zero_mem _

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Use `(dif_pos (isIntM_smul_rectOne hi b a i j)).trans ?_` and prove the remaining obligations. Distinguish the cases in `hij : i.val = j.val`. Use `Eq.trans (congrArg _ (Subtype.ext ?_)) (h.trans (if_pos hij).symm)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ε * (if i.val = j.val then 1 else 0) = ε`.

Rewrite using `[if_pos hij, mul_one]`. Use `Eq.trans (congrArg _ (Subtype.ext ?_)) ((RingHom.map_zero _).trans (if_neg hij).symm)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ε * (if i.val = j.val then 1 else 0) = 0`. Rewrite using `[if_neg hij, mul_zero]`.
-/
theorem redM_smul_rectOne {ε : EAf D} (hi : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E)
    (h : Formalism.L2.DIV.resS D.host.F PP ⟨ε, hi⟩ = 1) (b a : ℕ) :
    redM PP (ε • rectOne (EAf D) b a) = rectOne _ b a := by
  funext i j
  refine (dif_pos (isIntM_smul_rectOne hi b a i j)).trans ?_
  by_cases hij : i.val = j.val
  · refine Eq.trans (congrArg _ (Subtype.ext ?_)) (h.trans (if_pos hij).symm)
    change ε * (if i.val = j.val then 1 else 0) = ε
    rw [if_pos hij, mul_one]
  · refine Eq.trans (congrArg _ (Subtype.ext ?_)) ((RingHom.map_zero _).trans (if_neg hij).symm)
    change ε * (if i.val = j.val then 1 else 0) = 0
    rw [if_neg hij, mul_zero]

/- English proof (translation)
Introduce `D S T βS βT Pg Q P ξ e hr he hg hQ`. Take `⟨x, hx, hx'⟩` from `exists_half_frMapAdj S T βS βT (idemSum_mul_self he) (rectOne _ _ _)`. Take `⟨hi, hres⟩` from `idemSum_res he`. Use `⟨x, hx, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hx']`.

Conclude with `isIntM_smul_rectOne hi _ _`. Establish `key : ∀ PP ∈ P, LowZero T.rank (redM PP (frMapAdj S T βS βT x)) ∧ topL T.rank (redM PP (frMapAdj S T βS βT x)) = 1` using `fun PP hPP => by`. Rewrite using `[hx', redM_smul_rectOne hi PP (hres PP hPP)]`. Conclude with `⟨lowZero_rectOne _ _ _ _, topL_rectOne _ hr⟩`. Use `mul_ne_zero ?_ ?_` and prove the remaining obligations.

Unfold `omegaK`. Rewrite using `[if_pos fun PP hPP => key PP (hg PP hPP)]`. Conclude with `one_ne_zero`. Unfold `omegaQ`. Rewrite using `[dif_pos fun PP hPP => ⟨(key PP (hQ PP hPP)).1, by`.

Rewrite using `[(key PP (hQ PP hPP)).2, Matrix.det_one]`. Conclude with `isUnit_one⟩]`. Conclude with `Finset.prod_ne_zero_iff.2 fun PP _ => zpow_ne_zero _ (Units.ne_zero _)`.
-/
theorem exists_datum_ne_zero : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (Pg Q P : Finset (Formalism.L2.DIV.Pl D.host.E)) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (e : AE D), T.rank ≤ S.rank → IsIdemSum e P → (∀ PP ∈ Pg, PP ∈ P) → (∀ PP ∈ Q, PP ∈ P) → ∃ x : WO S T, IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧ omegaK Pg (fun PP => redM PP (frMapAdj S T βS βT x)) * omegaQ Q T.rank ξ (-1) (fun PP => redM PP (frMapAdj S T βS βT x)) ≠ 0 := by
  intro D S T βS βT Pg Q P ξ e hr he hg hQ
  obtain ⟨x, hx, hx'⟩ := exists_half_frMapAdj S T βS βT (idemSum_mul_self he) (rectOne _ _ _)
  obtain ⟨hi, hres⟩ := idemSum_res he
  refine ⟨x, hx, ?_, ?_⟩
  · rw [hx']; exact isIntM_smul_rectOne hi _ _
  · have key : ∀ PP ∈ P, LowZero T.rank (redM PP (frMapAdj S T βS βT x)) ∧
        topL T.rank (redM PP (frMapAdj S T βS βT x)) = 1 := fun PP hPP => by
      rw [hx', redM_smul_rectOne hi PP (hres PP hPP)]
      exact ⟨lowZero_rectOne _ _ _ _, topL_rectOne _ hr⟩
    refine mul_ne_zero ?_ ?_
    · unfold omegaK
      rw [if_pos fun PP hPP => key PP (hg PP hPP)]
      exact one_ne_zero
    · unfold omegaQ
      rw [dif_pos fun PP hPP => ⟨(key PP (hQ PP hPP)).1, by
        rw [(key PP (hQ PP hPP)).2, Matrix.det_one]; exact isUnit_one⟩]
      exact Finset.prod_ne_zero_iff.2 fun PP _ => zpow_ne_zero _ (Units.ne_zero _)

end GlobalTheory.AdjDatumNe

end
