import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdLatEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIdempotentPlaceChartFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdeleCMMemIntegralOfIdempotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLiftIdempotentFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFinitePartIdempotentBlendMemLatticeStabilStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotUnitMove

variable {D : D7}

/- English proof (translation)
Take `⟨ι, P, es, h1, -, rfl⟩` from `he`. Rewrite using `[← sub_eq_zero, ← mul_sub, Finset.sum_mul]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Use `(GlobalTheory.DownLift.SplitCoef.toEAf_idem_mul_eq_zero (h1 i hi) _).1 ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_sub, h, sub_self, mul_zero]`.
-/
theorem mul_eq_of_toEAf_eq {e : AE D} (he : GlobalTheory.PlaceModelSum.IsOrthSum e) {a b : AE D}
    (h : toEAf D a = toEAf D b) : e * a = e * b := by
  obtain ⟨ι, P, es, h1, -, rfl⟩ := he
  rw [← sub_eq_zero, ← mul_sub, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i hi => ?_
  refine (GlobalTheory.DownLift.SplitCoef.toEAf_idem_mul_eq_zero (h1 i hi) _).1 ?_
  rw [map_mul, map_sub, h, sub_self, mul_zero]

/- English proof (translation)
Establish `hΛ : r.Λ = Formalism.L2.Col.stdLat D.host.E V.rank`. Use extensionality with `y`. Rewrite using `[hs.2.1]`. Simplify using `[Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]`. Establish `hf` using `hr.2.1`.

Rewrite `hf` using `[hΛ]`. Prove the components needed by the constructor for the conclusion. Establish `h` using `(hf (fun k => r.β.val k j)).2 fun k => by`. Establish `e : (r.β⁻¹).val.mulVec (fun k => r.β.val k j) k = ((r.β⁻¹).val * r.β.val) k j`. Simplify using `[Matrix.mulVec, Matrix.mul_apply, dotProduct]`.

Rewrite using `[e, Units.inv_mul, Matrix.one_apply]`. Use `split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Conclude with `(GlobalTheory.CongStdLoc.mem_hatL_std_iff _).1 h i`.

Establish `h` using `(hf (Pi.single j 1)).1 ((GlobalTheory.CongStdLoc.mem_hatL_std_iff _).2 fun k => by`. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Simplify using `only [Pi.single_eq_same]`. Conclude with `one_mem _`.

Rewrite using `[Pi.single_eq_of_ne hk]`. Conclude with `zero_mem _)`. Establish `e : (r.β⁻¹).val.mulVec (Pi.single j 1) i = (r.β⁻¹).val i j`. Simplify using `[Matrix.mulVec_single]`. Rewrite using `[← e]`.

Conclude with `h i`.
-/
theorem frame_int {V : HSp D} {r : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.Rig V} (hs : r.IsStd) (hr : r.Is) (i j : Fin V.rank) :
    r.β.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (r.β⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have hΛ : r.Λ = Formalism.L2.Col.stdLat D.host.E V.rank := by
    ext y
    rw [hs.2.1]
    simp [Formalism.L2.Col.stdLat, Submodule.mem_pi, Submodule.mem_one]
  have hf := hr.2.1
  rw [hΛ] at hf
  constructor
  · have h := (hf (fun k => r.β.val k j)).2 fun k => by
      have e : (r.β⁻¹).val.mulVec
          (fun k => r.β.val k j) k = ((r.β⁻¹).val * r.β.val) k j := by
        simp [Matrix.mulVec, Matrix.mul_apply, dotProduct]
      rw [e, Units.inv_mul, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    exact (GlobalTheory.CongStdLoc.mem_hatL_std_iff _).1 h i
  · have h := (hf (Pi.single j 1)).1 ((GlobalTheory.CongStdLoc.mem_hatL_std_iff _).2 fun k => by
      by_cases hk : k = j
      · subst hk; simp only [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hk]; exact zero_mem _)
    have e : (r.β⁻¹).val.mulVec
        (Pi.single j 1) i = (r.β⁻¹).val i j := by
      simp [Matrix.mulVec_single]
    rw [← e]
    exact h i

/- English proof (translation)
The claim follows from `GlobalTheory.T.exists_theta_lift_idempotent_form`.
-/
theorem exists_unitary : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (e : AE D), e * e = e → e * cA D e = 0 →
    ∀ (P Q : Matrix (Fin V.rank) (Fin V.rank) (AE D)), e • (P * Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
      e • (Q * P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
    ∃ g : GA D V,
      Formalism.L2.Theta.mt V g = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • (Q.map (cA D)).transpose ∧
      Formalism.L2.Theta.mt V g⁻¹ = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • Q + cA D e • (P.map (cA D)).transpose := GlobalTheory.T.exists_theta_lift_idempotent_form

/- English proof (translation)
The claim follows from `GlobalTheory.T.unitaryFinitePart_idempotentBlend_mem_latticeStabilizer`.
-/
theorem mem_St : ∀ {D : D7} (V : HSp D) (g : GA D V) (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∀ ε φ : Lev.EAf D, ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → φ ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
    (Formalism.L2.Theta.mt V g).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₁ * β₀⁻¹).val + φ • ((β₀ * β₁⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    (Formalism.L2.Theta.mt V g⁻¹).map (toEAf D) = (1 - ε - φ) • (1 : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) +
      ε • (β₀ * β₁⁻¹).val + φ • ((β₁ * β₀⁻¹).val.map (GlobalTheory.AdelicLatMove.cF D)).transpose →
    Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ := GlobalTheory.T.unitaryFinitePart_idempotentBlend_mem_latticeStabilizer

/- English proof (translation)
Simplify using `only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`. Take the linear combination `(P i k - (1 : Matrix (Fin n) (Fin n) (AE D)) i k) * he + ((Q.map (cA D)).transpose i k - (1 : Matrix (Fin n) (Fin n) (AE D)) i k) * hef`.
-/
theorem smul_entry {e : AE D} {n : ℕ} (P Q : Matrix (Fin n) (Fin n) (AE D)) (he : e * e = e) (hef : e * cA D e = 0)
    (i k : Fin n) :
    e * ((1 - e - cA D e) • (1 : Matrix (Fin n) (Fin n) (AE D)) + e • P + cA D e • (Q.map (cA D)).transpose) i k =
      e * P i k := by
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (P i k - (1 : Matrix (Fin n) (Fin n) (AE D)) i k) * he +
    ((Q.map (cA D)).transpose i k - (1 : Matrix (Fin n) (Fin n) (AE D)) i k) * hef

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← hu c b, ← mul_assoc, ← mul_assoc, mul_comm (H a c), mul_comm (P a c), hH]`.
-/
theorem mul_half_eq {e : AE D} {n k : ℕ} (H P : Matrix (Fin n) (Fin n) (AE D)) (hH : ∀ i j, e * H i j = e * P i j)
    (u : Matrix (Fin n) (Fin k) (AE D)) (hu : ∀ a b, e * u a b = u a b) : HMul.hMul H u = HMul.hMul P u := by
  ext a b
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← hu c b, ← mul_assoc, ← mul_assoc, mul_comm (H a c), mul_comm (P a c), hH]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← hu a c, mul_assoc, mul_assoc, mul_left_comm e, mul_left_comm e, hH]`.
-/
theorem half_mul_eq {e : AE D} {n k : ℕ} (H P : Matrix (Fin n) (Fin n) (AE D)) (hH : ∀ i j, e * H i j = e * P i j)
    (u : Matrix (Fin k) (Fin n) (AE D)) (hu : ∀ a b, e * u a b = u a b) : HMul.hMul u H = HMul.hMul u P := by
  ext a b
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← hu a c, mul_assoc, mul_assoc, mul_left_comm e, mul_left_comm e, hH]

/- English proof (translation)
Take the linear combination `(p - o) * he + (q - o) * hf + (p + q - o - o) * hef`.
-/
theorem supp_alg {R : Type} [CommRing R] (e f o p q : R) (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) :
    (e + f) * ((1 - e - f) * o + e * p + f * q - o) = (1 - e - f) * o + e * p + f * q - o := by
  linear_combination (p - o) * he + (q - o) * hf + (p + q - o - o) * hef

/- English proof (translation)
Rewrite using `[← Matrix.map_apply (f := toEAf D), Matrix.map_mul, hA, hB, ← Units.val_mul, hab, Units.val_one, ← Matrix.map_apply (f := toEAf D), Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem toEAf_prod {n : ℕ} (A B : Matrix (Fin n) (Fin n) (AE D)) (a b : GL (Fin n) (Lev.EAf D))
    (hA : A.map (toEAf D) = a.val) (hB : B.map (toEAf D) = b.val) (hab : a * b = 1) (i j : Fin n) :
    toEAf D ((A * B) i j) = toEAf D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j) := by
  rw [← Matrix.map_apply (f := toEAf D), Matrix.map_mul, hA, hB, ← Units.val_mul, hab, Units.val_one,
    ← Matrix.map_apply (f := toEAf D), Matrix.map_one _ (map_zero _) (map_one _)]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Introduce `D V hV e hO hef β₀ β₁ h₀ h₁`. Establish `he : e * e = e` using `hO.idem`. Establish `hc : cA D e * cA D e = cA D e` using `by rw [← map_mul, he]`. Establish `hce : cA D e * e = 0` using `by rw [mul_comm, hef]`. Use `choose P hP using fun i j => GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) ((β₁ * β₀⁻¹).val i j)`.

Use `choose Q hQ using fun i j => GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) ((β₀ * β₁⁻¹).val i j)`. Establish `hPm : (Matrix.of P).map (toEAf D) = (β₁ * β₀⁻¹).val` using `by ext i j; exact hP i j`. Establish `hQm : (Matrix.of Q).map (toEAf D) = (β₀ * β₁⁻¹).val` using `by ext i j; exact hQ i j`. Establish `hPQ : e • (Matrix.of P * Matrix.of Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))`. Use extensionality with `i j`.

Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Conclude with `mul_eq_of_toEAf_eq hO (toEAf_prod _ _ _ _ hPm hQm (by group) i j)`. Establish `hQP : e • (Matrix.of Q * Matrix.of P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))`. Use extensionality with `i j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`.

Conclude with `mul_eq_of_toEAf_eq hO (toEAf_prod _ _ _ _ hQm hPm (by group) i j)`. Take `⟨g, hg, hgi⟩` from `exists_unitary V hV e he hef _ _ hPQ hQP`. Establish `hdd : (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det = 1`. Rewrite using `[← Matrix.det_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]`. Establish `hdd' : (Formalism.L2.Theta.mt V g⁻¹).det * (Formalism.L2.Theta.mt V g).det = 1` using `by rw [mul_comm, hdd]`.

Use `⟨g, ⟨e * (Formalism.L2.Theta.mt V g).det + (1 - e), e * (Formalism.L2.Theta.mt V g⁻¹).det + (1 - e), ?_, ?_⟩, fun i j => ?_, ?_, rfl, fun k u hu => ?_, fun k u hu => ?_⟩` and prove the remaining obligations. Take the linear combination `((Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det - (Formalism.L2.Theta.mt V g).det - (Formalism.L2.Theta.mt V g⁻¹).det + 1) * he + e * hdd`. Take the linear combination `((Formalism.L2.Theta.mt V g⁻¹).det * (Formalism.L2.Theta.mt V g).det - (Formalism.L2.Theta.mt V g⁻¹).det - (Formalism.L2.Theta.mt V g).det + 1) * he + e * hdd'`. Use `clear hPQ hQP hdd hdd' hPm hQm hP hQ h₀ h₁`. Simplify using `only [hg, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Conclude with `supp_alg _ _ _ _ _ he hc hef`. Use `mem_St V g β₀ β₁ h₀ h₁ (toEAf D e) (toEAf D (cA D e)) (GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem he) (GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem hc) ?_ ?_` and prove the remaining obligations. Use extensionality with `i j`. Simplify using `only [hg, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, map_add, map_mul, map_sub, map_one, GlobalTheory.AdelicLatMove.toEAf_cA, Matrix.of_apply, hP, hQ]`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Use extensionality with `i j`. Simplify using `only [hgi, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, map_add, map_mul, map_sub, map_one, GlobalTheory.AdelicLatMove.toEAf_cA, Matrix.of_apply, hP, hQ]`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Apply the tactic sequence `rw [mul_half_eq (Formalism.L2.Theta.mt V g) (Matrix.of P) (fun i j => by rw [hg]; exact smul_entry _ _ he hef i j) u hu, Matrix.map_mul, hPm]`. Apply the tactic sequence `rw [half_mul_eq (Formalism.L2.Theta.mt V g⁻¹) (Matrix.of Q) (fun i j => by rw [hgi]; exact smul_entry _ _ he hef i j) u hu, Matrix.map_mul, hQm]`.
-/
theorem exists_move : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (e : AE D), GlobalTheory.PlaceModelSum.IsOrthSum e → e * cA D e = 0 →
    ∀ (β₀ β₁ : GL (Fin V.rank) (Lev.EAf D)),
    (∀ i j, β₀.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₀⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    (∀ i j, β₁.val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ (β₁⁻¹).val i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) →
    ∃ (g : GA D V) (x : (AE D)ˣ), Formalism.L2.Theta.SuppAt e V g ∧ Formalism.IndefR.Lev.finE V g ∈ Formalism.L2.DIV.St β₁ ∧
      Formalism.L2.Theta.IsDetAt e V g x ∧
      (∀ (k : ℕ) (u : Matrix (Fin V.rank) (Fin k) (AE D)), (∀ a b, e * u a b = u a b) →
        (HMul.hMul (Formalism.L2.Theta.mt V g) u).map (toEAf D) = HMul.hMul (β₁ * β₀⁻¹).val (u.map (toEAf D))) ∧
      ∀ (k : ℕ) (u : Matrix (Fin k) (Fin V.rank) (AE D)), (∀ a b, e * u a b = u a b) →
        (HMul.hMul u (Formalism.L2.Theta.mt V g⁻¹)).map (toEAf D) = HMul.hMul (u.map (toEAf D)) (β₀ * β₁⁻¹).val := by
  intro D V hV e hO hef β₀ β₁ h₀ h₁
  have he : e * e = e := hO.idem
  have hc : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hce : cA D e * e = 0 := by rw [mul_comm, hef]
  choose P hP using fun i j => GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) ((β₁ * β₀⁻¹).val i j)
  choose Q hQ using fun i j => GlobalTheory.AdjDatumNe.toEAf_surjective (D := D) ((β₀ * β₁⁻¹).val i j)
  have hPm : (Matrix.of P).map (toEAf D) = (β₁ * β₀⁻¹).val := by ext i j; exact hP i j
  have hQm : (Matrix.of Q).map (toEAf D) = (β₀ * β₁⁻¹).val := by ext i j; exact hQ i j
  have hPQ : e • (Matrix.of P * Matrix.of Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_eq_of_toEAf_eq hO (toEAf_prod _ _ _ _ hPm hQm (by group) i j)
  have hQP : e • (Matrix.of Q * Matrix.of P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact mul_eq_of_toEAf_eq hO (toEAf_prod _ _ _ _ hQm hPm (by group) i j)
  obtain ⟨g, hg, hgi⟩ := exists_unitary V hV e he hef _ _ hPQ hQP
  have hdd : (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det = 1 := by
    rw [← Matrix.det_mul, ← GlobalTheory.AdelicLatMove.mt_mul, mul_inv_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.det_one]
  have hdd' : (Formalism.L2.Theta.mt V g⁻¹).det * (Formalism.L2.Theta.mt V g).det = 1 := by rw [mul_comm, hdd]
  refine ⟨g, ⟨e * (Formalism.L2.Theta.mt V g).det + (1 - e), e * (Formalism.L2.Theta.mt V g⁻¹).det + (1 - e), ?_, ?_⟩,
    fun i j => ?_, ?_, rfl, fun k u hu => ?_, fun k u hu => ?_⟩
  · linear_combination ((Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det - (Formalism.L2.Theta.mt V g).det -
      (Formalism.L2.Theta.mt V g⁻¹).det + 1) * he + e * hdd
  · linear_combination ((Formalism.L2.Theta.mt V g⁻¹).det * (Formalism.L2.Theta.mt V g).det - (Formalism.L2.Theta.mt V g⁻¹).det -
      (Formalism.L2.Theta.mt V g).det + 1) * he + e * hdd'
  · clear hPQ hQP hdd hdd' hPm hQm hP hQ h₀ h₁
    simp only [hg, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact supp_alg _ _ _ _ _ he hc hef
  · refine mem_St V g β₀ β₁ h₀ h₁ (toEAf D e) (toEAf D (cA D e)) (GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem he)
      (GlobalTheory.IdemFin.toEAf_mem_intAf_of_idem hc) ?_ ?_
    · ext i j
      simp only [hg, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, map_add,
        map_mul, map_sub, map_one, GlobalTheory.AdelicLatMove.toEAf_cA, Matrix.of_apply, hP, hQ]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    · ext i j
      simp only [hgi, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.transpose_apply, map_add,
        map_mul, map_sub, map_one, GlobalTheory.AdelicLatMove.toEAf_cA, Matrix.of_apply, hP, hQ]
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
  · rw [mul_half_eq (Formalism.L2.Theta.mt V g) (Matrix.of P) (fun i j => by rw [hg]; exact smul_entry _ _ he hef i j) u hu,
      Matrix.map_mul, hPm]
  · rw [half_mul_eq (Formalism.L2.Theta.mt V g⁻¹) (Matrix.of Q) (fun i j => by rw [hgi]; exact smul_entry _ _ he hef i j) u hu,
      Matrix.map_mul, hQm]

/- English proof (translation)
Establish `h` using `GlobalTheory.AdelicLatMove.gram_mul_inv V g`. Establish `e1 : V.gram.map (incA D) = 1` using `by rw [hV]; exact Matrix.map_one _ (map_zero _) (map_one _)`. Rewrite `h` using `[e1, Matrix.one_mul, Matrix.mul_one]`. Conclude with `h.symm`.
-/
theorem adj_eq_inv {V : HSp D} (hV : V.gram = 1) (g : GA D V) :
    ((Formalism.L2.Theta.mt V g).map (cA D)).transpose = Formalism.L2.Theta.mt V g⁻¹ := by
  have h := GlobalTheory.AdelicLatMove.gram_mul_inv V g
  have e1 : V.gram.map (incA D) = 1 := by rw [hV]; exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [e1, Matrix.one_mul, Matrix.mul_one] at h
  exact h.symm

/- English proof (translation)
Rewrite using `[adj_eq_inv hV, inv_inv]`.
-/
theorem adj_inv_eq {V : HSp D} (hV : V.gram = 1) (g : GA D V) :
    ((Formalism.L2.Theta.mt V g⁻¹).map (cA D)).transpose = Formalism.L2.Theta.mt V g := by
  rw [adj_eq_inv hV, inv_inv]

/- English proof (translation)
Simplify using `only [Units.val_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc (b₁⁻¹).val, Units.inv_mul, Matrix.one_mul, Units.inv_mul, Matrix.mul_one]`.
-/
theorem frame_cancel {R : Type} [CommRing R] {m n : ℕ} (a₀ a₁ : GL (Fin m) R) (b₀ b₁ : GL (Fin n) R)
    (x : Matrix (Fin n) (Fin m) R) :
    HMul.hMul (HMul.hMul (b₁⁻¹).val (HMul.hMul (HMul.hMul (b₁ * b₀⁻¹).val x) (a₀ * a₁⁻¹).val)) a₁.val =
      HMul.hMul (HMul.hMul (b₀⁻¹).val x) a₀.val := by
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (b₁⁻¹).val, Units.inv_mul, Matrix.one_mul, Units.inv_mul, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc (b₁ * b₀⁻¹).val]`. Conclude with `frame_cancel a₀ a₁ b₀ b₁ x`.
-/
theorem frame_cancel' {R : Type} [CommRing R] {m n : ℕ} (a₀ a₁ : GL (Fin m) R) (b₀ b₁ : GL (Fin n) R)
    (x : Matrix (Fin n) (Fin m) R) :
    HMul.hMul (HMul.hMul (b₁⁻¹).val (HMul.hMul (b₁ * b₀⁻¹).val (HMul.hMul x (a₀ * a₁⁻¹).val))) a₁.val =
      HMul.hMul (HMul.hMul (b₀⁻¹).val x) a₀.val := by
  rw [← Matrix.mul_assoc (b₁ * b₀⁻¹).val]
  exact frame_cancel a₀ a₁ b₀ b₁ x

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hG, hH, ← Matrix.mul_assoc, h5, h4]`. Conclude with `frame_cancel βw₀ βw₁ βa₀ βa₁ _`.
-/
theorem adj_key {R S : Type} [CommRing R] [CommRing S] (c : R →+* R) (f : R →+* S) {a w : ℕ}
    (G' Gi' : Matrix (Fin a) (Fin a) R) (H Hi : Matrix (Fin w) (Fin w) R) (u : Matrix (Fin w) (Fin a) R)
    (βa₀ βa₁ : GL (Fin a) S) (βw₀ βw₁ : GL (Fin w) S)
    (hG : (Gi'.map c).transpose = G') (hH : (H.map c).transpose = Hi)
    (h4 : (HMul.hMul G' (u.map c).transpose).map f = HMul.hMul (βa₁ * βa₀⁻¹).val ((u.map c).transpose.map f))
    (h5 : (HMul.hMul (HMul.hMul G' (u.map c).transpose) Hi).map f =
      HMul.hMul ((HMul.hMul G' (u.map c).transpose).map f) (βw₀ * βw₁⁻¹).val) :
    HMul.hMul (HMul.hMul (βa₁⁻¹).val (((HMul.hMul (HMul.hMul H u) Gi').map c).transpose.map f)) βw₁.val =
      HMul.hMul (HMul.hMul (βa₀⁻¹).val ((u.map c).transpose.map f)) βw₀.val := by
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul, hG, hH, ← Matrix.mul_assoc, h5, h4]
  exact frame_cancel βw₀ βw₁ βa₀ βa₁ _

/- English proof (translation)
Introduce `a b`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, hu]`.
-/
theorem half_mul_right {e : AE D} {m n k : ℕ} {u : Matrix (Fin m) (Fin n) (AE D)} (hu : ∀ a b, e * u a b = u a b)
    (M : Matrix (Fin n) (Fin k) (AE D)) : ∀ a b, e * (HMul.hMul u M) a b = (HMul.hMul u M) a b := by
  intro a b
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← mul_assoc, hu]

/- English proof (translation)
Introduce `a b`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, hu]`.
-/
theorem half_mul_left {e : AE D} {m n k : ℕ} {u : Matrix (Fin m) (Fin n) (AE D)} (hu : ∀ a b, e * u a b = u a b)
    (M : Matrix (Fin k) (Fin m) (AE D)) : ∀ a b, e * (HMul.hMul M u) a b = (HMul.hMul M u) a b := by
  intro a b
  simp only [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_left_comm, hu]

/- English proof (translation)
Introduce `D T L sc G W i j A A' WW X Y hX hY t`. Establish `hI` using `hY.is.idem t`. Establish `hO` using `GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hI`. Take `⟨g, x, g1, g2, g3, g4, g5⟩` from `exists_move A hY.std.1 _ hO hI.2 X.rA.β Y.rA.β (frame_int hX.std hX.is.rigA) (frame_int hY.std hY.is.rigA)`. Take `⟨g', x', g'1, g'2, g'3, g'4, g'5⟩` from `exists_move A' hY.std'.1 _ hO hI.2 X.rA'.β Y.rA'.β (frame_int hX.std' hX.is.rigA') (frame_int hY.std' hY.is.rigA')`.

Take `⟨h, y, h1, h2, h3, h4, h5⟩` from `exists_move WW hY.stdW.1 _ hO hI.2 X.rW.β Y.rW.β (frame_int hX.stdW hX.is.rigW) (frame_int hY.stdW hY.is.rigW)`. Use `⟨g, g', h, x, x', y, ⟨g1, g2, g3⟩, ⟨g'1, g'2, g'3⟩, ⟨h1, h2, h3⟩, fun u hu => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Simplify using `only [frMapO, actO]`. Rewrite using `[Matrix.mul_assoc (Formalism.L2.Theta.mt WW h), h4 _ _ (half_mul_right hu _), g5 _ _ hu]`. Conclude with `frame_cancel' X.rA.β Y.rA.β X.rW.β Y.rW.β _`.

Establish `hA' : A'.gram = 1` using `hY.std'.1`. Establish `hW : WW.gram = 1` using `hY.stdW.1`. Establish `hd : ∀ a b, Y.e t * ((u.map (cA D)).transpose) a b = ((u.map (cA D)).transpose) a b`. Introduce `a b`. Simplify using `only [Matrix.transpose_apply, Matrix.map_apply]`.

Use `conv_rhs => rw [← hu b a]`. Rewrite using `[map_mul, cA_cA]`. Simplify using `only [frMapAdj, actO, hA', hW, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]`. Conclude with `adj_key (cA D) (toEAf D) _ _ _ _ u X.rA'.β Y.rA'.β X.rW.β Y.rW.β (adj_inv_eq hA' g') (adj_eq_inv hW h) (g'4 _ _ hd) (h5 _ _ (half_mul_left hd _))`.
-/
theorem move_elts : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (i j : Fin D.R.m)
    (A A' WW : HSp D) (X Y : Tri T A A' WW), IsBottomTri W i j X → IsBottomTri W i j Y → ∀ t : T,
    ∃ (g : GA D A) (g' : GA D A') (h : GA D WW) (x x' y : (AE D)ˣ),
      (Formalism.L2.Theta.SuppAt (Y.e t) A g ∧ Formalism.IndefR.Lev.finE A g ∈ Formalism.L2.DIV.St Y.rA.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) A g x) ∧
      (Formalism.L2.Theta.SuppAt (Y.e t) A' g' ∧ Formalism.IndefR.Lev.finE A' g' ∈ Formalism.L2.DIV.St Y.rA'.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) A' g' x') ∧
      (Formalism.L2.Theta.SuppAt (Y.e t) WW h ∧ Formalism.IndefR.Lev.finE WW h ∈ Formalism.L2.DIV.St Y.rW.β ∧
        Formalism.L2.Theta.IsDetAt (Y.e t) WW h y) ∧
      (∀ u : WO A WW, IsHalf (Y.e t) u → frMapO A WW Y.rA.β Y.rW.β (actO A WW g h u) = frMapO A WW X.rA.β X.rW.β u) ∧
      ∀ u : WO A' WW, IsHalf (cA D (Y.e t)) u →
        frMapAdj A' WW Y.rA'.β Y.rW.β (actO A' WW g' h u) = frMapAdj A' WW X.rA'.β X.rW.β u := by
  intro D T L sc G W i j A A' WW X Y hX hY t
  have hI := hY.is.idem t
  have hO := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hI
  obtain ⟨g, x, g1, g2, g3, g4, g5⟩ := exists_move A hY.std.1 _ hO hI.2 X.rA.β Y.rA.β
    (frame_int hX.std hX.is.rigA) (frame_int hY.std hY.is.rigA)
  obtain ⟨g', x', g'1, g'2, g'3, g'4, g'5⟩ := exists_move A' hY.std'.1 _ hO hI.2 X.rA'.β Y.rA'.β
    (frame_int hX.std' hX.is.rigA') (frame_int hY.std' hY.is.rigA')
  obtain ⟨h, y, h1, h2, h3, h4, h5⟩ := exists_move WW hY.stdW.1 _ hO hI.2 X.rW.β Y.rW.β
    (frame_int hX.stdW hX.is.rigW) (frame_int hY.stdW hY.is.rigW)
  refine ⟨g, g', h, x, x', y, ⟨g1, g2, g3⟩, ⟨g'1, g'2, g'3⟩, ⟨h1, h2, h3⟩, fun u hu => ?_, fun u hu => ?_⟩
  · simp only [frMapO, actO]
    rw [Matrix.mul_assoc (Formalism.L2.Theta.mt WW h), h4 _ _ (half_mul_right hu _), g5 _ _ hu]
    exact frame_cancel' X.rA.β Y.rA.β X.rW.β Y.rW.β _
  · have hA' : A'.gram = 1 := hY.std'.1
    have hW : WW.gram = 1 := hY.stdW.1
    have hd : ∀ a b, Y.e t * ((u.map (cA D)).transpose) a b = ((u.map (cA D)).transpose) a b := by
      intro a b
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      conv_rhs => rw [← hu b a]
      rw [map_mul, cA_cA]
    simp only [frMapAdj, actO, hA', hW, inv_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, Matrix.mul_one]
    exact adj_key (cA D) (toEAf D) _ _ _ _ u X.rA'.β Y.rA'.β X.rW.β Y.rW.β (adj_inv_eq hA' g') (adj_eq_inv hW h)
      (g'4 _ _ hd) (h5 _ _ (half_mul_left hd _))

end GlobalTheory.BotUnitMove

end
