import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemLevelOfThetaDatumNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `: ε * ε ^ n = ε`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih => rw [pow_succ, ← mul_assoc, ih, h]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem units_mul_relation_rearrange_commRing {R : Type} [CommRing R] {ε : R} (h : ε * ε = ε) (n : ℕ) : (1 : R) = 1 - ε + ε * ε ^ n := by
  have : ε * ε ^ n = ε := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, h]
  rw [this]; ring

/- English proof (translation)
Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Use `congr 1`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]`.
-/
private theorem matrix_map_ringHom_add_smul_sandwich {R : Type} [CommRing R] {a b : ℕ} (βS : GL (Fin a) R) (βT : GL (Fin b) R) (ε : R)
    (J : Matrix (Fin b) (Fin a) R) :
    (βT⁻¹).val * (ε • (βT.val * J * (βS⁻¹).val)) * βS.val = ε • J := by
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
    Matrix.mul_one]

/- English proof (translation)
Use extensionality with `i j`. Unfold `topL`. Rewrite using `[dif_pos ⟨lt_of_lt_of_le i.2 hab, j.2⟩]`. Simplify using `[Matrix.one_apply, Fin.ext_iff]`.
-/
private theorem topL_smul_identity {R : Type} [CommRing R] {a b : ℕ} (hab : a ≤ b) (ε : R) :
    topL a (ε • (Matrix.of fun (i : Fin b) (j : Fin a) => if i.1 = j.1 then (1 : R) else 0)) =
      ε • (1 : Matrix (Fin a) (Fin a) R) := by
  ext i j
  unfold topL
  rw [dif_pos ⟨lt_of_lt_of_le i.2 hab, j.2⟩]
  simp [Matrix.one_apply, Fin.ext_iff]

/- English proof (translation)
Introduce `D S T βS βT ν e Z I hr he`. Establish `hee : e * e = e` using `GlobalTheory.PlaceDatum.idemSum_mul_self he`. Establish `hE` using `StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he`. Establish `hεε : toEAf D e * toEAf D e = toEAf D e` using `by rw [← RingHom.map_mul, hee]`. Set `J : Matrix (Fin T.rank) (Fin S.rank) (EAf D)` to `Matrix.of fun i j => if i.1 = j.1 then 1 else 0`.

Set `M : Matrix (Fin T.rank) (Fin S.rank) (EAf D)` to `βT.val * J * (βS⁻¹).val`. Use `choose w _ hw using fun i j => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj (D := D) (M i j)`. Set `x : WO S T` to `fun i j => e * w i j`. Establish `hx : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • M`. Use extensionality with `i j`.

Express the relevant statement in the definitionally equal form `toEAf D (e * w i j) = toEAf D e * M i j`. Rewrite using `[RingHom.map_mul, hw]`. Establish `hf : frMapO S T βS βT x = toEAf D e • J`. Unfold `frMapO`. Rewrite using `[hx]`.

Conclude with `matrix_map_ringHom_add_smul_sandwich βS βT (toEAf D e) J`. Establish `hJ : ∀ i j, (toEAf D e • J) i j = if i.1 = j.1 then toEAf D e else 0` using `fun i j => by`. Express the relevant statement in the definitionally equal form `toEAf D e * (if i.1 = j.1 then 1 else 0) = _`. Use `split_ifs`. Conclude with `mul_one _`.

Conclude with `mul_zero _`. Establish `h1 : IsHalf e x` using `fun i j => by`. Express the relevant statement in the definitionally equal form `e * (e * w i j) = e * w i j`. Rewrite using `[← mul_assoc, hee]`. Establish `h2 : IsIntM (toEAf D e • J)` using `fun i j => by`.

Rewrite using `[hJ]`. Use `split_ifs`. Conclude with `hE`. Conclude with `zero_mem _`. Establish `h3 : ∀ i j, S.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((toEAf D e • J) i j)` using `fun i j hi => by`.

Establish `hj` using `j.2`. Rewrite using `[hJ, if_neg (by omega)]`. Conclude with `⟨zero_mem _, zero_mem _⟩`. Establish `h4 : ∃ y, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (topL S.rank (toEAf D e • J)) y`. Use `⟨1, RingHom.map_one _, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[topL_smul_identity hr, Matrix.det_smul, Matrix.det_one, mul_one, Units.val_one, RingHom.map_one]`. Conclude with `units_mul_relation_rearrange_commRing hεε _`. Rewrite using `[inv_one, Units.val_one, RingHom.map_one]`. Conclude with `one_mem _`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst`. Rewrite using `[hf, if_pos ⟨h1, h2, h3⟩]`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar`. Rewrite using `[dif_pos h4]`. Conclude with `Circle.coe_ne_zero _`.
-/
theorem UpperTheory.exists_stdFst_ne_zero_of_rank_le :
    ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (ν : (AE D)ˣ →* Circle) (e : AE D) (Z : Finset (Formalism.L2.DIV.Pl D.host.E)) (I : Ideal (𝓞 D.host.E)),
      S.rank ≤ T.rank → IsIdemSum e Z → ∃ x : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst ν e I S T βS βT x ≠ 0 := by
  intro D S T βS βT ν e Z I hr he
  have hee : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hεε : toEAf D e * toEAf D e = toEAf D e := by rw [← RingHom.map_mul, hee]
  let J : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.of fun i j => if i.1 = j.1 then 1 else 0
  let M : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := βT.val * J * (βS⁻¹).val
  choose w _ hw using fun i j => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_surj (D := D) (M i j)
  let x : WO S T := fun i j => e * w i j
  have hx : (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map (toEAf D) = toEAf D e • M := by
    ext i j
    change toEAf D (e * w i j) = toEAf D e * M i j
    rw [RingHom.map_mul, hw]
  have hf : frMapO S T βS βT x = toEAf D e • J := by
    unfold frMapO
    rw [hx]
    exact matrix_map_ringHom_add_smul_sandwich βS βT (toEAf D e) J
  have hJ : ∀ i j, (toEAf D e • J) i j = if i.1 = j.1 then toEAf D e else 0 := fun i j => by
    change toEAf D e * (if i.1 = j.1 then 1 else 0) = _
    split_ifs
    · exact mul_one _
    · exact mul_zero _
  have h1 : IsHalf e x := fun i j => by
    change e * (e * w i j) = e * w i j
    rw [← mul_assoc, hee]
  have h2 : IsIntM (toEAf D e • J) := fun i j => by
    rw [hJ]
    split_ifs
    · exact hE
    · exact zero_mem _
  have h3 : ∀ i j, S.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I ((toEAf D e • J) i j) := fun i j hi => by
    have hj := j.2
    rw [hJ, if_neg (by omega)]
    exact ⟨zero_mem _, zero_mem _⟩
  have h4 : ∃ y, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet e (topL S.rank (toEAf D e • J)) y := by
    refine ⟨1, RingHom.map_one _, ?_, ?_⟩
    · rw [topL_smul_identity hr, Matrix.det_smul, Matrix.det_one, mul_one, Units.val_one, RingHom.map_one]
      exact units_mul_relation_rearrange_commRing hεε _
    · rw [inv_one, Units.val_one, RingHom.map_one]
      exact one_mem _
  refine ⟨x, ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
  rw [hf, if_pos ⟨h1, h2, h3⟩]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar
  rw [dif_pos h4]
  exact Circle.coe_ne_zero _
