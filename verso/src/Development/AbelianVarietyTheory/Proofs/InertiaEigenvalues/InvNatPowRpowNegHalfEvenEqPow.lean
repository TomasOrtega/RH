import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumVectorDropAuxiliaryPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaVacuumHeckeIdentitySplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumHeckeIndicatorIntegralEqPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceChartFiniteAdeleTensorLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumUniversalDeterminantDatumCoeffEqPrimitiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArtinMapSplitPlaceUniformiserEqFrobeniusInvStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModulusUnramifiedCharDetHeckeDoubleCosetSplitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
noncomputable section

namespace GlobalTheory.DistRel
variable {D : D7} {S T : HSp D}

open GlobalTheory.SplitHecke

/- English proof (translation)
Rewrite using `[← Fintype.prod_ite_eq' i₀ (fun _ => A), ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem prod_ite_split {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ : ι) (A : ℂ) (f : ι → ℂ) :
    ∏ i, (if i = i₀ then A else f i) = (∏ i, (if i = i₀ then 1 else f i)) * A := by
  rw [← Fintype.prod_ite_eq' i₀ (fun _ => A), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

open Classical in

/- English proof (translation)
Establish `key : ∀ y : Reds D T.rank S.rank, B.locFn Q (fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y) y = B.locFn Q (fun PP y => if PP.1 = P then 1 else φ PP.1 y) y * ((prim (y P) : ℚ) : ℂ)` using `fun y => by`. Unfold `Base.locFn`. Establish `h1 : ∀ PP : ↥Q, (if PP.1 = P then ((prim (y PP.1) : ℚ) : ℂ) else φ PP.1 (y PP.1)) = if PP = ⟨P, hP⟩ then ((prim (y P) : ℚ) : ℂ) else φ PP.1 (y PP.1)` using `fun PP => by`. Distinguish the cases in `h : PP.1 = P`. Rewrite using `[if_pos h, if_pos (Subtype.ext h), h]`.

Rewrite using `[if_neg h, if_neg fun e => h (congrArg Subtype.val e)]`. Establish `h2 : ∀ PP : ↥Q, (if PP.1 = P then (1 : ℂ) else φ PP.1 (y PP.1)) = if PP = ⟨P, hP⟩ then 1 else φ PP.1 (y PP.1)` using `fun PP => by`. Distinguish the cases in `h : PP.1 = P`. Rewrite using `[if_pos h, if_pos (Subtype.ext h)]`. Rewrite using `[if_neg h, if_neg fun e => h (congrArg Subtype.val e)]`.

Simplify using `only [h1, h2]`. Rewrite using `[mul_assoc]`. Use `congr 1`. Use `prod_ite_split (⟨P, hP⟩ : ↥Q) (((prim (y P) : ℚ) : ℂ)) (fun PP => φ PP.1 (y PP.1)) using 2` and compare the differences between its conclusion and the goal. Unfold `Frame.datumFn`.

Apply the tactic sequence `split_ifs with c1 c2 <;> simp [key, mul_assoc]`.
-/
theorem datumFn_prim (B : Base S T) (Q : Finset (Pl D.host.E)) {P : Pl D.host.E} (hP : P ∈ Q)
    (φ : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ) (x : WO S T) :
    B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y) x =
      B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q fun PP y => if PP.1 = P then 1 else φ PP.1 y) x *
        ((prim (redM P (frMapO S T B.F.βS B.F.βT x)) : ℚ) : ℂ) := by
  have key : ∀ y : Reds D T.rank S.rank, B.locFn Q (fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y) y =
      B.locFn Q (fun PP y => if PP.1 = P then 1 else φ PP.1 y) y * ((prim (y P) : ℚ) : ℂ) := fun y => by
    unfold Base.locFn
    have h1 : ∀ PP : ↥Q, (if PP.1 = P then ((prim (y PP.1) : ℚ) : ℂ) else φ PP.1 (y PP.1)) =
        if PP = ⟨P, hP⟩ then ((prim (y P) : ℚ) : ℂ) else φ PP.1 (y PP.1) := fun PP => by
      by_cases h : PP.1 = P
      · rw [if_pos h, if_pos (Subtype.ext h), h]
      · rw [if_neg h, if_neg fun e => h (congrArg Subtype.val e)]
    have h2 : ∀ PP : ↥Q, (if PP.1 = P then (1 : ℂ) else φ PP.1 (y PP.1)) =
        if PP = ⟨P, hP⟩ then 1 else φ PP.1 (y PP.1) := fun PP => by
      by_cases h : PP.1 = P
      · rw [if_pos h, if_pos (Subtype.ext h)]
      · rw [if_neg h, if_neg fun e => h (congrArg Subtype.val e)]
    simp only [h1, h2]
    rw [mul_assoc]
    congr 1
    convert prod_ite_split (⟨P, hP⟩ : ↥Q) (((prim (y P) : ℚ) : ℂ)) (fun PP => φ PP.1 (y PP.1)) using 2
  unfold Frame.datumFn
  split_ifs with c1 c2 <;> simp [key, mul_assoc]

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
variable {D : D7} {S T : HSp D}
open GlobalTheory.SplitHecke
open Classical

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Assume the negation of the conclusion as `hx`.

Break down `h1 with h1 | h1` into its components or cases. Conclude with `h2 (Or.inl h1)`. Conclude with `h2 (Or.inr ⟨hx, h1⟩)`. Introduce and unpack `rfl`. Conclude with `⟨Or.inr hP, fun h => h.elim (fun h' => hR h') fun h' => h'.1 rfl⟩`.
-/
theorem sdiff_erase {Q R : Finset (Pl D.host.E)} {P : Pl D.host.E} (hP : P ∈ Q) (hR : P ∉ R) :
    (R ∪ Q) \ (R ∪ Q.erase P) = {P} := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hx
    rcases h1 with h1 | h1
    · exact h2 (Or.inl h1)
    · exact h2 (Or.inr ⟨hx, h1⟩)
  · rintro rfl
    exact ⟨Or.inr hP, fun h => h.elim (fun h' => hR h') fun h' => h'.1 rfl⟩

/- English proof (translation)
Establish `hPd : P ∉ B.de.Q` using `fun h => Finset.disjoint_left.1 hQ.2 h hP`. Establish `hsub : B.de.Q ∪ Q.erase P ⊆ B.de.Q ∪ Q` using `Finset.union_subset_union (subset_refl _) (Finset.erase_subset _ _)`. Establish `hsd` using `sdiff_erase hP hPd`. Establish `e1` using `halfIdem_eq_add (Pg := B.G.Pg) hsub`. Establish `hid : idem ((B.de.Q ∪ Q) \ (B.de.Q ∪ Q.erase P)) = idemAt P` using `by rw [hsd, idem, Finset.sum_singleton]`.

Rewrite `e1` using `[hid]`. Establish `h2` using `halfIdem_mul_idem hQ.1 hsub`. Rewrite `h2` using `[hid]`. Establish `h3` using `idem_mul_self_of (hQ.1.empty_sdiff (Qb := B.de.Q ∪ Q.erase P))`. Rewrite `h3` using `[hid]`.

Establish `h1` using `(hQ.1.mono hsub).isOrthSum.1.idem`. Establish `h4` using `hQ.1.isOrthSum.2`. Rewrite `h4` using `[e1, map_add]`. Establish `h6 : cA D (halfIdem B.G.Pg (B.de.Q ∪ Q.erase P)) * cA D (idemAt P) = 0` using `by rw [← map_mul, h2, map_zero]`. Establish `h7 : cA D (idemAt P) * cA D (idemAt P) = cA D (idemAt P)` using `by rw [← map_mul, h3]`.

Establish `hPs : PlacesOK ∅ ({P} : Finset (Pl D.host.E))`. Use `hQ.1.empty_sdiff (Qb := B.de.Q ∪ Q.erase P)` as an intermediate fact. Rewrite `this` using `[hsd]`. Then use the resulting hypothesis. Use `set a' := halfIdem B.G.Pg (B.de.Q ∪ Q.erase P)`. Use `set e := idemAt P`.

Use `⟨e1, h2, ?_, h3, h1, hPs⟩` and prove the remaining obligations. Take the linear combination `(-cA D e) * h1 + (-(cA D e * cA D e)) * h2 + (a' * cA D e) * h4 + (-(a' * a') - a' * e) * h6 + (-(a' * a')) * h7`.
-/
theorem idem_facts (B : Base S T) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    halfIdem B.G.Pg (B.de.Q ∪ Q) = halfIdem B.G.Pg (B.de.Q ∪ Q.erase P) + idemAt P ∧
    halfIdem B.G.Pg (B.de.Q ∪ Q.erase P) * idemAt P = 0 ∧
    halfIdem B.G.Pg (B.de.Q ∪ Q.erase P) * cA D (idemAt P) = 0 ∧ idemAt P * idemAt P = idemAt P ∧
    halfIdem B.G.Pg (B.de.Q ∪ Q.erase P) * halfIdem B.G.Pg (B.de.Q ∪ Q.erase P) =
      halfIdem B.G.Pg (B.de.Q ∪ Q.erase P) ∧ PlacesOK ∅ ({P} : Finset (Pl D.host.E)) := by
  have hPd : P ∉ B.de.Q := fun h => Finset.disjoint_left.1 hQ.2 h hP
  have hsub : B.de.Q ∪ Q.erase P ⊆ B.de.Q ∪ Q := Finset.union_subset_union (subset_refl _) (Finset.erase_subset _ _)
  have hsd := sdiff_erase hP hPd
  have e1 := halfIdem_eq_add (Pg := B.G.Pg) hsub
  have hid : idem ((B.de.Q ∪ Q) \ (B.de.Q ∪ Q.erase P)) = idemAt P := by rw [hsd, idem, Finset.sum_singleton]
  rw [hid] at e1
  have h2 := halfIdem_mul_idem hQ.1 hsub
  rw [hid] at h2
  have h3 := idem_mul_self_of (hQ.1.empty_sdiff (Qb := B.de.Q ∪ Q.erase P))
  rw [hid] at h3
  have h1 := (hQ.1.mono hsub).isOrthSum.1.idem
  have h4 := hQ.1.isOrthSum.2
  rw [e1, map_add] at h4
  have h6 : cA D (halfIdem B.G.Pg (B.de.Q ∪ Q.erase P)) * cA D (idemAt P) = 0 := by rw [← map_mul, h2, map_zero]
  have h7 : cA D (idemAt P) * cA D (idemAt P) = cA D (idemAt P) := by rw [← map_mul, h3]
  have hPs : PlacesOK ∅ ({P} : Finset (Pl D.host.E)) := by
    have := hQ.1.empty_sdiff (Qb := B.de.Q ∪ Q.erase P)
    rwa [hsd] at this
  set a' := halfIdem B.G.Pg (B.de.Q ∪ Q.erase P)
  set e := idemAt P
  refine ⟨e1, h2, ?_, h3, h1, hPs⟩
  linear_combination (-cA D e) * h1 + (-(cA D e * cA D e)) * h2 + (a' * cA D e) * h4 + (-(a' * a') - a' * e) * h6 +
    (-(a' * a')) * h7

/- English proof (translation)
Establish `hs` using `GlobalTheory.SplitHecke.suppAt_inv hγ`. Establish `hM : a' • Formalism.L2.Theta.mt T γ⁻¹ = a' • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))`. Use extensionality with `i j`. Use `hs i j` as an intermediate fact. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`.

Establish `h3 : a' * (Formalism.L2.Theta.mt T γ⁻¹ - 1) i j = 0`. Rewrite using `[← this, ← mul_assoc, mul_add, h1, h2, add_zero, zero_mul]`. Rewrite `h3` using `[Matrix.sub_apply, mul_sub, sub_eq_zero]`. Conclude with `h3`. Unfold `actO`.

Rewrite using `[inv_inv, GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one, ← Matrix.smul_mul, hM, Matrix.smul_mul, Matrix.one_mul]`.
-/
theorem smul_actO {a' e : AE D} (h1 : a' * e = 0) (h2 : a' * cA D e = 0) {γ : GA D T} (hγ : SuppAt e T γ) (x : WO S T) :
    a' • actO S T (1 : GA D S)⁻¹ γ⁻¹ x = a' • x := by
  have hs := GlobalTheory.SplitHecke.suppAt_inv hγ
  have hM : a' • Formalism.L2.Theta.mt T γ⁻¹ = a' • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    ext i j
    have := hs i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    have h3 : a' * (Formalism.L2.Theta.mt T γ⁻¹ - 1) i j = 0 := by
      rw [← this, ← mul_assoc, mul_add, h1, h2, add_zero, zero_mul]
    rw [Matrix.sub_apply, mul_sub, sub_eq_zero] at h3
    exact h3
  unfold actO
  rw [inv_inv, GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one, ← Matrix.smul_mul, hM, Matrix.smul_mul, Matrix.one_mul]

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
variable {D : D7} {S T : HSp D}
open GlobalTheory.SplitHecke
open Classical

/- English proof (translation)
Establish `hm : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)), (M.map (toEAf D)).map φv = M.map π` using `fun M => by`. Rewrite using `[Matrix.map_map]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `hφ1 a`.

Establish `hb : ∀ {n : ℕ} (β : GL (Fin n) (Datum.EAf D)), (β.1).map φv = (Matrix.GeneralLinearGroup.map φv β).1` using `fun β => rfl`. Rewrite using `[rho_val]`. Unfold `frMapO actO`. Simplify using `only [inv_inv, GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one, Matrix.map_mul, hm, hb, map_inv, Matrix.mul_assoc]`. Use `congr 2`.

Rewrite using `[← Matrix.mul_assoc (Matrix.GeneralLinearGroup.map φv F.βT).1, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`.
-/
theorem Y_act (F : Frame S T) {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}
    (φv : Datum.EAf D →+* Fv D.host.F v) (hφ1 : ∀ a, φv (toEAf D a) = π a) (γ : GA D T) (x : WO S T) :
    (frMapO S T F.βS F.βT (actO S T (1 : GA D S)⁻¹ γ⁻¹ x)).map φv =
      (rho T π (Matrix.GeneralLinearGroup.map φv F.βT) γ⁻¹).1 * (frMapO S T F.βS F.βT x).map φv := by
  have hm : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) (AE D)), (M.map (toEAf D)).map φv = M.map π := fun M => by
    rw [Matrix.map_map]
    congr 1
    funext a
    exact hφ1 a
  have hb : ∀ {n : ℕ} (β : GL (Fin n) (Datum.EAf D)), (β.1).map φv = (Matrix.GeneralLinearGroup.map φv β).1 := fun β => rfl
  rw [rho_val]
  unfold frMapO actO
  simp only [inv_inv, GlobalTheory.AdelicLatMove.mt_one, Matrix.mul_one, Matrix.map_mul, hm, hb, map_inv, Matrix.mul_assoc]
  congr 2
  rw [← Matrix.mul_assoc (Matrix.GeneralLinearGroup.map φv F.βT).1, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mul]

/- English proof (translation)
Establish `hid : idem ({P} : Finset (Pl D.host.E)) = idemAt P` using `by rw [idem, Finset.sum_singleton]`. Establish `hh : IsHalf (idem ({P} : Finset (Pl D.host.E))) (idemAt P • y)` using `by rw [hid]; exact isHalf_smul hee y`. Establish `hint : IsIntM (frMapO S T F.βS F.βT (idemAt P • y)) ↔ IntM (Ov D v) ((frMapO S T F.βS F.βT y).map φv)`. Rewrite using `[frMapO_smul]`. Conclude with `forall₂_congr fun i j => hφ2 _`.

Rewrite using `[← hint]`. Conclude with `⟨fun h => (GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hPs hh h).1, fun h => GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral hF hPs hh h⟩`.
-/
theorem lat_iff {F : Frame S T} (hF : F.Good) {P : Pl D.host.E} (hPs : PlacesOK ∅ ({P} : Finset (Pl D.host.E)))
    (hee : idemAt P * idemAt P = idemAt P) {v : HeightOneSpectrum (𝓞 D.host.F)} (φv : Datum.EAf D →+* Fv D.host.F v)
    (hφ2 : ∀ N : Datum.EAf D, toEAf D (idemAt P) * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ IsInt (Ov D v) (φv N))
    (y : WO S T) : idemAt P • y ∈ F.lat ↔ IntM (Ov D v) ((frMapO S T F.βS F.βT y).map φv) := by
  have hid : idem ({P} : Finset (Pl D.host.E)) = idemAt P := by rw [idem, Finset.sum_singleton]
  have hh : IsHalf (idem ({P} : Finset (Pl D.host.E))) (idemAt P • y) := by rw [hid]; exact isHalf_smul hee y
  have hint : IsIntM (frMapO S T F.βS F.βT (idemAt P • y)) ↔ IntM (Ov D v) ((frMapO S T F.βS F.βT y).map φv) := by
    rw [frMapO_smul]
    exact forall₂_congr fun i j => hφ2 _
  rw [← hint]
  exact ⟨fun h => (GlobalTheory.T.frameMatrices_integral_of_mem_completedLattice hF hPs hh h).1, fun h => GlobalTheory.T.mem_completedLattice_of_frameMatrix_integral hF hPs hh h⟩

/- English proof (translation)
Unfold `halfInd`. Distinguish the cases in `h : e • y ∈ Λ`. Rewrite using `[if_pos ⟨h, isHalf_smul he y⟩, if_pos h]`. Rewrite using `[if_neg fun h' => h h'.1, if_neg h]`.
-/
theorem halfInd_smul {m n : ℕ} {e : AE D} (he : e * e = e) (Λ : AddSubgroup (Mx D m n)) (y : Mx D m n) :
    halfInd e Λ (e • y) = if e • y ∈ Λ then 1 else 0 := by
  unfold halfInd
  by_cases h : e • y ∈ Λ
  · rw [if_pos ⟨h, isHalf_smul he y⟩, if_pos h]
  · rw [if_neg fun h' => h h'.1, if_neg h]

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
variable {D : D7} {S T : HSp D}
open GlobalTheory.SplitHecke
open Classical

/- English proof (translation)
Rewrite using `[← Finset.mul_sum, Finset.sum_boole, ← Nat.card_eq_finsetCard]`. Use `congr 2`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun i => Finset.mem_filter)`.
-/
theorem card_filter_eq {ι : Type} (R : Finset ι) (p : ι → Prop) (C : ℂ) :
    ∑ γ ∈ R, C * (if p γ then 1 else 0) = C * (Nat.card {γ : ι // γ ∈ R ∧ p γ} : ℂ) := by
  rw [← Finset.mul_sum, Finset.sum_boole, ← Nat.card_eq_finsetCard]
  congr 2
  exact Nat.card_congr (Equiv.subtypeEquivRight fun i => Finset.mem_filter)

/- English proof (translation)
Take `⟨e1, h2, h3, hee, -, hPs⟩` from `idem_facts B hQ hP`. Establish `hPd : P ∉ B.de.Q` using `fun h => Finset.disjoint_left.1 hQ.2 h hP`. Establish `hsub : B.de.Q ∪ Q.erase P ⊆ B.de.Q ∪ Q` using `Finset.union_subset_union (subset_refl _) (Finset.erase_subset _ _)`. Establish `hid : idem ((B.de.Q ∪ Q) \ (B.de.Q ∪ Q.erase P)) = idemAt P` using `by rw [sdiff_erase hP hPd, idem, Finset.sum_singleton]`. Use `set ω1 := B.locFn Q fun PP y => if PP.1 = P then 1 else φ PP.1 y with hω1`.

Establish `hdep : ∀ y y' : Reds D T.rank S.rank, (∀ PP ∈ B.de.Q ∪ Q.erase P, y PP = y' PP) → ω1 y = ω1 y'` using `fun y y' hy => by`. Rewrite using `[hω1]`. Unfold `Base.locFn`. Use `congr 1`. Conclude with `Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)]`.

Use `Finset.prod_congr rfl fun PP _ => ?_ dsimp only` and prove the remaining obligations. Distinguish the cases in `h : PP.1 = P`. Rewrite using `[if_pos h, if_pos h]`. Rewrite using `[if_neg h, if_neg h, hy PP.1 (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨h, PP.2⟩))]`. Establish `hR` using `datumFn_eq_restrict hB.frame hQ.1 hsub hdep`.

Rewrite `hR` using `[hid]`. Use `set a' := halfIdem B.G.Pg (B.de.Q ∪ Q.erase P)`. Use `set e := idemAt P`. Use `set β' := Matrix.GeneralLinearGroup.map φv B.F.βT`. Use `set Y := (frMapO S T B.F.βS B.F.βT x).map φv with hY`.

Use `set C := B.F.datumFn B.G (B.de.Q ∪ Q.erase P) ω1 (a' • x) * (if IsHalf (a' + e) x then 1 else 0) with hC`. Establish `key : ∀ γ : GA D T, SuppAt e T γ → B.F.datumFn B.G (B.de.Q ∪ Q) ω1 (actO S T (1 : GA D S)⁻¹ γ⁻¹ x) = C * (if IntM (Ov D v) ((rho T π β' γ⁻¹).1 * Y) then 1 else 0)` using `fun γ hγ => by`. Rewrite using `[hR, restrictHalf_apply, smul_actO h2 h3 hγ, halfInd_smul hee]`. Establish `hh : IsHalf (a' + e) (actO S T (1 : GA D S)⁻¹ γ⁻¹ x) ↔ IsHalf (a' + e) x`. Use `⟨fun h => ?_, fun h => GlobalTheory.SplitHecke.isHalf_actO _ _ h⟩` and prove the remaining obligations.

Use `GlobalTheory.SplitHecke.isHalf_actO (1 : GA D S) γ h` as an intermediate fact. Rewrite using `[show actO S T (1 : GA D S) γ (actO S T (1 : GA D S)⁻¹ γ⁻¹ x) = x by` and apply the resulting hypothesis. Use `GlobalTheory.SplitHecke.actO_inv_actO (1 : GA D S)⁻¹ γ⁻¹ x` as an intermediate fact. Rewrite `this` using `[inv_inv, inv_inv] at this]`. Then use the resulting hypothesis. Establish `hl : e • actO S T (1 : GA D S)⁻¹ γ⁻¹ x ∈ B.F.lat ↔ IntM (Ov D v) ((rho T π β' γ⁻¹).1 * Y)`.

Rewrite using `[lat_iff hB.frame hPs hee φv hφ2, Y_act B.F φv hφ1]`. Simplify using `only [hC, hh, hl]`. Apply the tactic sequence `split_ifs <;> ring`. Establish `key0 : B.F.datumFn B.G (B.de.Q ∪ Q) ω1 x = C * (if IntM (Ov D v) Y then 1 else 0)`. Use `key 1 (GlobalTheory.SplitHecke.suppAt_one T)` as an intermediate fact.

Rewrite using `[inv_one, inv_one, show actO S T (1 : GA D S) (1 : GA D T) x = x by` and apply the resulting hypothesis. Unfold `actO`. Simplify using `[GlobalTheory.AdelicLatMove.mt_one], map_one, Units.val_one, Matrix.one_mul] at this`. Establish `hHk : ∀ k ∈ Finset.Icc 1 T.rank, Hk (Ov D v) p k (rho T π β' (α k)) ∧ Reps (Ov D v) (rho T π β' (α k)) (R k) (rho T π β')` using `fun k hk => ⟨GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset e v π hsp hπ T β' hfr ϖ p k (α k) hpϖ (hα k hk).1, reps_of hsp hπ hfr (hα k hk).1.2.1 (hα k hk).2.1 (hα k hk).2.2⟩`. Establish `hint : ∀ k ∈ Finset.Icc 1 T.rank, ∀ γ ∈ R k, IntM (Ov D v) (rho T π β' γ).1` using `fun k hk γ hγ => by`.

Take `⟨k₁, k₂, g₁, g₂, hg⟩` from `(hHk k hk).2.1 γ hγ`. Rewrite using `[hg]`. Conclude with `(GlobalTheory.SplitHecke.Cosets.hk_mul (hHk k hk).1 g₁ g₂).1`. Rewrite using `[datumFn_prim B Q hP φ x, key0]`. Establish `hsum : ∀ k ∈ Finset.Icc 1 T.rank, ∑ γ ∈ R k, B.F.datumFn B.G (B.de.Q ∪ Q) ω1 (actO S T (1 : GA D S)⁻¹ γ⁻¹ x) = C * (Nat.card {γ : GA D T // γ ∈ R k ∧ IntM (Ov D v) (((rho T π β' γ)⁻¹).1 * Y)} : ℂ)` using `fun k hk => by`.

Rewrite using `[Finset.sum_congr rfl fun γ hγ => key γ ((hα k hk).2.1 γ hγ)]`. Simplify using `only [map_inv]`. Conclude with `card_filter_eq (R k) _ C`. Rewrite using `[Finset.sum_congr rfl fun k hk => by rw [hsum k hk]]`. Distinguish the cases in `hY0 : IntM (Ov D v) Y`.

Take `⟨z, hz⟩` from `intM_iff.1 hY0`. Establish `hm` using `GlobalTheory.T.sum_hecke_indicator_integral_eq_primitive (Ov D v) (Fv D.host.F v) p hp T.rank S.rank (GA D T) (fun k => rho T π β' (α k)) R (rho T π β') hHk z`. Rewrite `hm` using `[hz]`. Rewrite using `[if_pos hY0, mul_one]`. Establish `e2 : C + ∑ k ∈ Finset.Icc 1 T.rank, (-1 : ℂ) ^ k * (Nat.card (IsLocalRing.ResidueField (Ov D v)) : ℂ) ^ (k * (k - 1) / 2) * (C * (Nat.card {γ : GA D T // γ ∈ R k ∧ IntM (Ov D v) (((rho T π β' γ)⁻¹).1 * Y)} : ℂ)) = C * ((prim (z.map (IsLocalRing.residue (Ov D v))) : ℚ) : ℂ)`.

Rewrite using `[← hm, mul_add, mul_one, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.

Distinguish the cases in `hC0 : C = 0`. Rewrite using `[hC0, zero_mul, zero_mul]`. Use `congr 1`. Establish `hd : B.F.datumFn B.G (B.de.Q ∪ Q) ω1 x ≠ 0` using `by rw [key0, if_pos hY0, mul_one]; exact hC0`. Establish `hI : IsIntM (frMapO S T B.F.βS B.F.βT x)`.

Assume the negation of the conclusion as `hn`. Apply `hd` to reduce the goal to its premises. Simplify using `only [Frame.datumFn, hn, and_false, if_false, mul_zero]`. Conclude with `hφ3 _ _ _ hI z hz` after adjusting the coercions. Rewrite using `[if_neg hY0, mul_zero, zero_mul, zero_add]`.

Use `(Finset.sum_eq_zero fun k hk => ?_).symm` and prove the remaining obligations. Establish `h0 : Nat.card {γ : GA D T // γ ∈ R k ∧ IntM (Ov D v) (((rho T π β' γ)⁻¹).1 * Y)} = 0`. Use `Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨γ, hγ, h⟩ => hY0 ?_⟩)` and prove the remaining obligations. Use `(hint k hk γ hγ).mul h` as an intermediate fact. Rewrite `this` using `[← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`. Then use the resulting hypothesis.

Rewrite using `[h0, Nat.cast_zero, mul_zero, mul_zero]`.
-/
theorem datum_rel (B : Base S T) (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) {P : Pl D.host.E} (hP : P ∈ Q)
    (φ : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v} (hsp : IsSplitIdem D (idemAt P))
    (hπ : Chart (idemAt P) v π) (φv : Datum.EAf D →+* Fv D.host.F v) (hφ1 : ∀ a, φv (toEAf D a) = π a)
    (hφ2 : ∀ N : Datum.EAf D, toEAf D (idemAt P) * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ IsInt (Ov D v) (φv N))
    (hφ3 : ∀ (m n : ℕ) (N : Matrix (Fin m) (Fin n) (Datum.EAf D)), IsIntM N → ∀ z : Matrix (Fin m) (Fin n) (Ov D v),
      z.map (algebraMap (Ov D v) (Fv D.host.F v)) = N.map φv → prim (redM P N) = prim (z.map (IsLocalRing.residue (Ov D v))))
    (hfr : Frame T (idemAt P) π (Matrix.GeneralLinearGroup.map φv B.F.βT)) [Finite (IsLocalRing.ResidueField (Ov D v))]
    {ϖ : D.host.E} {p : Ov D v} (hp : Irreducible p) (hpϖ : algebraMap (Ov D v) (Fv D.host.F v) p = π (incA D ϖ))
    (α : ℕ → GA D T) (R : ℕ → Finset (GA D T))
    (hα : ∀ k ∈ Finset.Icc 1 T.rank, IsHeckeElt T (idemAt P) ϖ k (α k) ∧ (∀ γ ∈ R k, SuppAt (idemAt P) T γ) ∧
      Mult.IsCosetRep T (Mult.locPart T (KsphC T ∅) (idemAt P)) (α k) (R k)) (x : WO S T) :
    B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y) x =
      B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q fun PP y => if PP.1 = P then 1 else φ PP.1 y) x +
        ∑ k ∈ Finset.Icc 1 T.rank, ((-1 : ℂ) ^ k * (Nat.card (IsLocalRing.ResidueField (Ov D v)) : ℂ) ^ (k * (k - 1) / 2)) *
          ∑ γ ∈ R k, B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q fun PP y => if PP.1 = P then 1 else φ PP.1 y)
            (actO S T (1 : GA D S)⁻¹ γ⁻¹ x) := by
  obtain ⟨e1, h2, h3, hee, -, hPs⟩ := idem_facts B hQ hP
  have hPd : P ∉ B.de.Q := fun h => Finset.disjoint_left.1 hQ.2 h hP
  have hsub : B.de.Q ∪ Q.erase P ⊆ B.de.Q ∪ Q := Finset.union_subset_union (subset_refl _) (Finset.erase_subset _ _)
  have hid : idem ((B.de.Q ∪ Q) \ (B.de.Q ∪ Q.erase P)) = idemAt P := by rw [sdiff_erase hP hPd, idem, Finset.sum_singleton]
  set ω1 := B.locFn Q fun PP y => if PP.1 = P then 1 else φ PP.1 y with hω1
  have hdep : ∀ y y' : Reds D T.rank S.rank, (∀ PP ∈ B.de.Q ∪ Q.erase P, y PP = y' PP) → ω1 y = ω1 y' := fun y y' hy => by
    rw [hω1]
    unfold Base.locFn
    congr 1
    · exact Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)]
    · refine Finset.prod_congr rfl fun PP _ => ?_
      dsimp only
      by_cases h : PP.1 = P
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h, hy PP.1 (Finset.mem_union_right _ (Finset.mem_erase.2 ⟨h, PP.2⟩))]
  have hR := datumFn_eq_restrict hB.frame hQ.1 hsub hdep
  rw [hid] at hR
  set a' := halfIdem B.G.Pg (B.de.Q ∪ Q.erase P)
  set e := idemAt P
  set β' := Matrix.GeneralLinearGroup.map φv B.F.βT
  set Y := (frMapO S T B.F.βS B.F.βT x).map φv with hY
  set C := B.F.datumFn B.G (B.de.Q ∪ Q.erase P) ω1 (a' • x) * (if IsHalf (a' + e) x then 1 else 0) with hC
  have key : ∀ γ : GA D T, SuppAt e T γ → B.F.datumFn B.G (B.de.Q ∪ Q) ω1 (actO S T (1 : GA D S)⁻¹ γ⁻¹ x) =
      C * (if IntM (Ov D v) ((rho T π β' γ⁻¹).1 * Y) then 1 else 0) := fun γ hγ => by
    rw [hR, restrictHalf_apply, smul_actO h2 h3 hγ, halfInd_smul hee]
    have hh : IsHalf (a' + e) (actO S T (1 : GA D S)⁻¹ γ⁻¹ x) ↔ IsHalf (a' + e) x := by
      refine ⟨fun h => ?_, fun h => GlobalTheory.SplitHecke.isHalf_actO _ _ h⟩
      have := GlobalTheory.SplitHecke.isHalf_actO (1 : GA D S) γ h
      rwa [show actO S T (1 : GA D S) γ (actO S T (1 : GA D S)⁻¹ γ⁻¹ x) = x by
        have := GlobalTheory.SplitHecke.actO_inv_actO (1 : GA D S)⁻¹ γ⁻¹ x
        rwa [inv_inv, inv_inv] at this] at this
    have hl : e • actO S T (1 : GA D S)⁻¹ γ⁻¹ x ∈ B.F.lat ↔ IntM (Ov D v) ((rho T π β' γ⁻¹).1 * Y) := by
      rw [lat_iff hB.frame hPs hee φv hφ2, Y_act B.F φv hφ1]
    simp only [hC, hh, hl]
    split_ifs <;> ring
  have key0 : B.F.datumFn B.G (B.de.Q ∪ Q) ω1 x = C * (if IntM (Ov D v) Y then 1 else 0) := by
    have := key 1 (GlobalTheory.SplitHecke.suppAt_one T)
    rwa [inv_one, inv_one, show actO S T (1 : GA D S) (1 : GA D T) x = x by
      unfold actO; simp [GlobalTheory.AdelicLatMove.mt_one], map_one, Units.val_one, Matrix.one_mul] at this

  have hHk : ∀ k ∈ Finset.Icc 1 T.rank, Hk (Ov D v) p k (rho T π β' (α k)) ∧ Reps (Ov D v) (rho T π β' (α k)) (R k) (rho T π β') :=
    fun k hk => ⟨GlobalTheory.T.heckeElement_component_mem_standardDoubleCoset e v π hsp hπ T β' hfr ϖ p k (α k) hpϖ (hα k hk).1,
      reps_of hsp hπ hfr (hα k hk).1.2.1 (hα k hk).2.1 (hα k hk).2.2⟩
  have hint : ∀ k ∈ Finset.Icc 1 T.rank, ∀ γ ∈ R k, IntM (Ov D v) (rho T π β' γ).1 := fun k hk γ hγ => by
    obtain ⟨k₁, k₂, g₁, g₂, hg⟩ := (hHk k hk).2.1 γ hγ
    rw [hg]
    exact (GlobalTheory.SplitHecke.Cosets.hk_mul (hHk k hk).1 g₁ g₂).1
  rw [datumFn_prim B Q hP φ x, key0]
  have hsum : ∀ k ∈ Finset.Icc 1 T.rank, ∑ γ ∈ R k, B.F.datumFn B.G (B.de.Q ∪ Q) ω1 (actO S T (1 : GA D S)⁻¹ γ⁻¹ x) =
      C * (Nat.card {γ : GA D T // γ ∈ R k ∧ IntM (Ov D v) (((rho T π β' γ)⁻¹).1 * Y)} : ℂ) := fun k hk => by
    rw [Finset.sum_congr rfl fun γ hγ => key γ ((hα k hk).2.1 γ hγ)]
    simp only [map_inv]
    exact card_filter_eq (R k) _ C
  rw [Finset.sum_congr rfl fun k hk => by rw [hsum k hk]]
  by_cases hY0 : IntM (Ov D v) Y
  · obtain ⟨z, hz⟩ := intM_iff.1 hY0
    have hm := GlobalTheory.T.sum_hecke_indicator_integral_eq_primitive (Ov D v) (Fv D.host.F v) p hp T.rank S.rank (GA D T) (fun k => rho T π β' (α k)) R (rho T π β')
      hHk z
    rw [hz] at hm
    rw [if_pos hY0, mul_one]
    have e2 : C + ∑ k ∈ Finset.Icc 1 T.rank, (-1 : ℂ) ^ k * (Nat.card (IsLocalRing.ResidueField (Ov D v)) : ℂ) ^ (k * (k - 1) / 2) *
        (C * (Nat.card {γ : GA D T // γ ∈ R k ∧ IntM (Ov D v) (((rho T π β' γ)⁻¹).1 * Y)} : ℂ)) =
        C * ((prim (z.map (IsLocalRing.residue (Ov D v))) : ℚ) : ℂ) := by
      rw [← hm, mul_add, mul_one, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e2]
    by_cases hC0 : C = 0
    · rw [hC0, zero_mul, zero_mul]
    · congr 1
      have hd : B.F.datumFn B.G (B.de.Q ∪ Q) ω1 x ≠ 0 := by rw [key0, if_pos hY0, mul_one]; exact hC0
      have hI : IsIntM (frMapO S T B.F.βS B.F.βT x) := by
        by_contra hn
        apply hd
        simp only [Frame.datumFn, hn, and_false, if_false, mul_zero]
      exact_mod_cast hφ3 _ _ _ hI z hz
  · rw [if_neg hY0, mul_zero, zero_mul, zero_add]
    refine (Finset.sum_eq_zero fun k hk => ?_).symm
    have h0 : Nat.card {γ : GA D T // γ ∈ R k ∧ IntM (Ov D v) (((rho T π β' γ)⁻¹).1 * Y)} = 0 := by
      refine Nat.card_eq_zero.2 (Or.inl ⟨fun ⟨γ, hγ, h⟩ => hY0 ?_⟩)
      have := (hint k hk γ hγ).mul h
      rwa [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at this
    rw [h0, Nat.cast_zero, mul_zero, mul_zero]

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
variable {D : D7} {S T : HSp D}
open GlobalTheory.SplitHecke
open Classical

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `(he.2 1 one_ne_zero).2 (by` as an intermediate fact. Rewrite using `[show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])` and apply the resulting hypothesis. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)`.
-/
theorem finPart_idem_mem {e : AE D} {P : Pl D.host.E} (he : IsIdemAt e P) : finPart D e ∈ intAE D := by
  by_contra hc
  have := (he.2 1 one_ne_zero).2 (by
    rwa [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one, mul_one])
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

/- English proof (translation)
Establish `he` using `hS.isIdemAt hP`. Establish `h1' : (1 - idemAt P) * ((y⁻¹ : (AE D)ˣ) : AE D) = 1 - idemAt P` using `by conv_lhs => rw [← h1, mul_assoc, Units.mul_inv, mul_one]`. Establish `key : ∀ z : AE D, (1 - idemAt P) * z = 1 - idemAt P → finPart D (idemAt P * z) ∈ intAE D → finPart D z ∈ intAE D` using `fun z a b => by`. Establish `: z = idemAt P * z + 1 - idemAt P` using `by linear_combination a`. Rewrite using `[this, RingHom.map_sub, RingHom.map_add, RingHom.map_one]`.

Conclude with `sub_mem (add_mem b (GlobalTheory.SplitDivisors.one_mem_int D)) (finPart_idem_mem he)`. Establish `hinf : infPart D (y : AE D) = 1`. Establish `h0 : infPart D (idemAt P) = 0` using `GlobalTheory.StepVec.infPart_idemAt he`. Establish `: (y : AE D) = idemAt P * (y : AE D) + (1 - idemAt P)` using `by linear_combination h1`. Rewrite using `[this, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h0]`.

Expand and normalize the polynomial expressions, which then agree. Use `hχ y hinf (key _ h1 h2) (key _ h1' h3) ?_` and prove the remaining obligations. Establish `h0 : idemAt P * (idem Q + cA D (idem Q)) = 0`. Rewrite using `[mul_add, idem, map_sum, Finset.mul_sum, Finset.mul_sum, Finset.sum_eq_zero fun j hj => hS.mul_eq_zero hP (hQ hj) fun e => hn (e ▸ hj), Finset.sum_eq_zero fun j hj => hS.mul_conj hP (hQ hj), add_zero]`. Take the linear combination `(idem Q + cA D (idem Q)) * h1 + ((y : AE D) - 1) * h0`.
-/
theorem unram_at {χ : (AE D)ˣ →* Circle} {Q S' : Finset (Pl D.host.E)} (hχ : UnramOutside χ Q) (hS : SplitSet S')
    (hQ : Q ⊆ S') {P : Pl D.host.E} (hP : P ∈ S') (hn : P ∉ Q) (y : (AE D)ˣ)
    (h1 : (1 - idemAt P) * (y : AE D) = 1 - idemAt P) (h2 : finPart D (idemAt P * (y : AE D)) ∈ intAE D)
    (h3 : finPart D (idemAt P * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D) : χ y = 1 := by
  have he := hS.isIdemAt hP
  have h1' : (1 - idemAt P) * ((y⁻¹ : (AE D)ˣ) : AE D) = 1 - idemAt P := by
    conv_lhs => rw [← h1, mul_assoc, Units.mul_inv, mul_one]
  have key : ∀ z : AE D, (1 - idemAt P) * z = 1 - idemAt P → finPart D (idemAt P * z) ∈ intAE D → finPart D z ∈ intAE D :=
    fun z a b => by
      have : z = idemAt P * z + 1 - idemAt P := by linear_combination a
      rw [this, RingHom.map_sub, RingHom.map_add, RingHom.map_one]
      exact sub_mem (add_mem b (GlobalTheory.SplitDivisors.one_mem_int D)) (finPart_idem_mem he)
  have hinf : infPart D (y : AE D) = 1 := by
    have h0 : infPart D (idemAt P) = 0 := GlobalTheory.StepVec.infPart_idemAt he
    have : (y : AE D) = idemAt P * (y : AE D) + (1 - idemAt P) := by linear_combination h1
    rw [this, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, h0]
    ring
  refine hχ y hinf (key _ h1 h2) (key _ h1' h3) ?_
  have h0 : idemAt P * (idem Q + cA D (idem Q)) = 0 := by
    rw [mul_add, idem, map_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.sum_eq_zero fun j hj => hS.mul_eq_zero hP (hQ hj) fun e => hn (e ▸ hj),
      Finset.sum_eq_zero fun j hj => hS.mul_conj hP (hQ hj), add_zero]
  linear_combination (idem Q + cA D (idem Q)) * h1 + ((y : AE D) - 1) * h0

/- English proof (translation)
Take `⟨S', hg, hq, hS⟩` from `hQ.1.split`. Establish `hPS : P ∈ S'` using `hq (Finset.mem_union_right _ hP)`. Establish `hPg : P ∉ B.G.Pg` using `fun h => Finset.disjoint_left.1 hQ.1.disj h (Finset.mem_union_right _ hP)`. Establish `hPd : P ∉ B.de.Q` using `fun h => Finset.disjoint_left.1 hQ.2 h hP`. Rewrite using `[Base.mu, MonoidHom.mul_apply, unram_at hB.unram hS hg hPS hPg y h1 h2 h3, unram_at hB.de.unram hS (Finset.subset_union_left.trans hq) hPS hPd y h1 h2 h3, mul_one]`.
-/
theorem mu_unram (B : Base S T) (hB : B.Good) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) {P : Pl D.host.E} (hP : P ∈ Q)
    (y : (AE D)ˣ) (h1 : (1 - idemAt P) * (y : AE D) = 1 - idemAt P) (h2 : finPart D (idemAt P * (y : AE D)) ∈ intAE D)
    (h3 : finPart D (idemAt P * ((y⁻¹ : (AE D)ˣ) : AE D)) ∈ intAE D) : B.mu y = 1 := by
  obtain ⟨S', hg, hq, hS⟩ := hQ.1.split
  have hPS : P ∈ S' := hq (Finset.mem_union_right _ hP)
  have hPg : P ∉ B.G.Pg := fun h => Finset.disjoint_left.1 hQ.1.disj h (Finset.mem_union_right _ hP)
  have hPd : P ∉ B.de.Q := fun h => Finset.disjoint_left.1 hQ.2 h hP
  rw [Base.mu, MonoidHom.mul_apply, unram_at hB.unram hS hg hPS hPg y h1 h2 h3,
    unram_at hB.de.unram hS (Finset.subset_union_left.trans hq) hPS hPd y h1 h2 h3, mul_one]

end GlobalTheory.DistRel

namespace GlobalTheory.DistRel
variable {D : D7} {S T : HSp D}
open GlobalTheory.SplitHecke
open Classical

/- English proof (translation)
Establish `h1 : (-((2 * m : ℕ) : ℝ) / 2) = -(m : ℝ)` using `by push_cast; ring`. Rewrite using `[h1, Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv, Real.rpow_natCast, ← pow_mul]`.
-/
theorem inv_natPow_rpow_neg_half_even_eq_pow (q : ℕ) (hq : 0 < q) (k m : ℕ) :
    ((((q : ℝ) ^ k)⁻¹) ^ (-((2 * m : ℕ) : ℝ) / 2) : ℝ) = (q : ℝ) ^ (k * m) := by
  have h1 : (-((2 * m : ℕ) : ℝ) / 2) = -(m : ℝ) := by push_cast; ring
  rw [h1, Real.rpow_neg (by positivity), Real.inv_rpow (by positivity), inv_inv, Real.rpow_natCast, ← pow_mul]

/- English proof (translation)
Take `⟨S', -, hq', hS'⟩` from `hQ.1.split`. Establish `he : IsIdemAt (idemAt P) P` using `hS'.isIdemAt (hq' (Finset.mem_union_right _ hP))`. Take `⟨v, π, hπ⟩` from `GlobalTheory.T.exists_place_chart_of_splitIdempotent (idemAt P) he.1`. Take `⟨⟨p, hpϖ, hp⟩, hq⟩` from `GlobalTheory.T.splitChart_uniformiser_and_residueCard (idemAt P) P v π he hπ ϖ hϖ1 hϖ2`. Take `⟨φv, hφ1, hφ2, hφ3, hfr⟩` from `GlobalTheory.T.splitPlaceChart_finiteAdeleTensor_levels D (idemAt P) P v π he hπ`.

Establish `hq0 : Ideal.absNorm P.asIdeal ≠ 0` using `fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `: Finite (IsLocalRing.ResidueField (Ov D v))` using `Nat.finite_of_card_ne_zero (hq ▸ hq0)`. Establish `hdr` using `datum_rel B hB hQ hP φ he.1 hπ φv hφ1 hφ2 hφ3 (hfr T B.F.βT B.F.ΛT hbT) hp hpϖ α R hα`. Rewrite `hdr` using `[hq]`. Establish `hae : halfIdem B.G.Pg (B.de.Q ∪ Q) * idemAt P = idemAt P`.

Take `⟨e1, h2, -, hee, -, -⟩` from `idem_facts B hQ hP`. Rewrite using `[e1, add_mul, h2, zero_add, hee]`. Use `set a := halfIdem B.G.Pg (B.de.Q ∪ Q)`. Use `set Tm := B.F.placeMap a`. Establish `hTm` using `Frame.isPlaceModel_placeMap (G := B.G) hB.frame hQ.1`.

Establish `ho` using `hQ.1.isOrthSum`. Use `set ω1 := B.locFn Q fun PP y => if PP.1 = P then 1 else φ PP.1 y`. Establish `hdep : ∀ y y' : Reds D T.rank S.rank, (∀ PP ∈ B.de.Q ∪ Q, y PP = y' PP) → ω1 y = ω1 y'` using `fun y y' hy => by`. Unfold `ω1 Base.locFn`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)]`. Conclude with `Finset.prod_congr rfl fun PP _ => by rw [hy PP.1 (Finset.mem_union_right _ PP.2)]`. Establish `hSB` using `Frame.isSBHalf_datumFn (G := B.G) hB.frame hQ.1 hdep`. Use `set Φ1 := B.F.datumFn B.G (B.de.Q ∪ Q) ω1`. Establish `hv1 : B.vecAt Q (fun PP y => if PP.1 = P then 1 else φ PP.1 y) = Tm Φ1` using `rfl`.

Establish `hlaw : ∀ k ∈ Finset.Icc 1 T.rank, ∀ γ ∈ R k, ω (1, γ) (Tm Φ1) = (((B.mu x : Circle) : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (S.rank / 2))) • Tm (fun t => Φ1 (actO S T (1 : GA D S)⁻¹ γ⁻¹ t))`. Introduce `k hk γ hγ`. Establish `hγs` using `(hα k hk).2.1 γ hγ`. Establish `hL` using `GlobalTheory.SplitLinear.law_place hω hB.frame.sdS hB.frame.sdT ho.1.idem ho.1.infPart_eq ho.2 hB.frame.vac.2.theta hB.frame.vac.2.lat hTm he.1 hae (GlobalTheory.SplitHecke.suppAt_one S) hγs Φ1 hSB`. Rewrite using `[hL]`.

Use `congr 1`. Take `⟨-, k₁, hk₁, k₂, hk₂, hγe⟩` from `((hα k hk).2.2.1 γ hγ)`. Establish `hH` using `GlobalTheory.T.modulus_unramifiedChar_det_heckeDoubleCoset_split D T P (idemAt P) he ϖ hϖ1 hϖ2 x hx k (α k) (hα k hk).1 k₁ hk₁ k₂ hk₂ (GlobalTheory.VecInv.detAt (idemAt P) he.1.1 T γ) (by rw [← hγe]; exact GlobalTheory.VecInv.isDetAt_detAt _ he.1.1 T γ)`. Take `⟨hH1, hH2⟩` from `hH`. Establish `hmu` using `hH2 Circle (B.mu * 1) (fun y h1 h2 h3 => by`.

Rewrite using `[mul_one]`. Conclude with `mu_unram B hB hQ hP y h1 h2 h3)`. Rewrite `hmu` using `[mul_one]`. Unfold `GlobalTheory.SplitLinear.fac GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac`. Rewrite using `[map_one, splitFacO, map_one, inv_one, one_mul, mul_one, hmu, hH1]`.

Establish `habs : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1` using `by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]`. Rewrite using `[habs, Real.one_rpow, one_mul]`. Take `⟨m, hm⟩` from `hB.even`. Establish `hn : S.rank = 2 * m` using `by omega`. Rewrite using `[hn, inv_natPow_rpow_neg_half_even_eq_pow _ (Nat.pos_of_ne_zero hq0) k m, show 2 * m / 2 = m by omega]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hfun : B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y) = Φ1 + ∑ k ∈ Finset.Icc 1 T.rank, ((-1 : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (k - 1) / 2)) • ∑ γ ∈ R k, fun t => Φ1 (actO S T (1 : GA D S)⁻¹ γ⁻¹ t)`. Use function extensionality and compare the values at `t`. Rewrite using `[hdr t]`.

Simplify using `[Finset.sum_apply, Pi.smul_apply, Φ1, ω1]`. Establish `hv : B.vecAt Q (fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y) = Tm (B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y))` using `rfl`. Rewrite using `[hv, hfun, map_add, map_sum, hv1]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, map_sum, Finset.smul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun γ hγ => ?_` and prove the remaining obligations. Rewrite using `[hlaw k hk γ hγ, smul_smul]`. Use `congr 1`. Establish `hne : ((B.mu x : Circle) : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (S.rank / 2)) ≠ 0` using `mul_ne_zero (pow_ne_zero _ (Circle.coe_ne_zero _)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq0))`.

Clear the denominators using the available nonvanishing facts.
-/
theorem vec_rel (B : Base S T) (hB : B.Good) (hbT : Lev.IsBaseFrame T B.F.βT B.F.ΛT 1) {ω : PairRep S T}
    (hω : B.IsWeil 1 ω) {Q : Finset (Pl D.host.E)} (hQ : B.admitted Q) {P : Pl D.host.E} (hP : P ∈ Q)
    (φ : ∀ PP : Pl D.host.E, Matrix (Fin T.rank) (Fin S.rank) (kP PP) → ℂ)
    {ϖ : 𝓞 D.host.E} (hϖ1 : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (x : (AE D)ˣ)
    (hx : (x : AE D) = idemAt P * incA D (ϖ : D.host.E) + (1 - idemAt P))
    (α : ℕ → GA D T) (R : ℕ → Finset (GA D T))
    (hα : ∀ k ∈ Finset.Icc 1 T.rank, IsHeckeElt T (idemAt P) (ϖ : D.host.E) k (α k) ∧ (∀ γ ∈ R k, SuppAt (idemAt P) T γ) ∧
      Mult.IsCosetRep T (Mult.locPart T (KsphC T ∅) (idemAt P)) (α k) (R k)) :
    B.vecAt Q (fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y) =
      B.vecAt Q (fun PP y => if PP.1 = P then 1 else φ PP.1 y) +
        ∑ k ∈ Finset.Icc 1 T.rank, ((-1 : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (k - 1) / 2) *
          (((B.mu x : Circle) : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (S.rank / 2)))⁻¹) •
          ∑ γ ∈ R k, ω (1, γ) (B.vecAt Q fun PP y => if PP.1 = P then 1 else φ PP.1 y) := by
  obtain ⟨S', -, hq', hS'⟩ := hQ.1.split
  have he : IsIdemAt (idemAt P) P := hS'.isIdemAt (hq' (Finset.mem_union_right _ hP))
  obtain ⟨v, π, hπ⟩ := GlobalTheory.T.exists_place_chart_of_splitIdempotent (idemAt P) he.1
  obtain ⟨⟨p, hpϖ, hp⟩, hq⟩ := GlobalTheory.T.splitChart_uniformiser_and_residueCard (idemAt P) P v π he hπ ϖ hϖ1 hϖ2
  obtain ⟨φv, hφ1, hφ2, hφ3, hfr⟩ := GlobalTheory.T.splitPlaceChart_finiteAdeleTensor_levels D (idemAt P) P v π he hπ
  have hq0 : Ideal.absNorm P.asIdeal ≠ 0 := fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have : Finite (IsLocalRing.ResidueField (Ov D v)) := Nat.finite_of_card_ne_zero (hq ▸ hq0)
  have hdr := datum_rel B hB hQ hP φ he.1 hπ φv hφ1 hφ2 hφ3 (hfr T B.F.βT B.F.ΛT hbT) hp hpϖ α R hα
  rw [hq] at hdr

  have hae : halfIdem B.G.Pg (B.de.Q ∪ Q) * idemAt P = idemAt P := by
    obtain ⟨e1, h2, -, hee, -, -⟩ := idem_facts B hQ hP
    rw [e1, add_mul, h2, zero_add, hee]
  set a := halfIdem B.G.Pg (B.de.Q ∪ Q)
  set Tm := B.F.placeMap a
  have hTm := Frame.isPlaceModel_placeMap (G := B.G) hB.frame hQ.1
  have ho := hQ.1.isOrthSum
  set ω1 := B.locFn Q fun PP y => if PP.1 = P then 1 else φ PP.1 y
  have hdep : ∀ y y' : Reds D T.rank S.rank, (∀ PP ∈ B.de.Q ∪ Q, y PP = y' PP) → ω1 y = ω1 y' := fun y y' hy => by
    unfold ω1 Base.locFn
    congr 1
    · exact Finset.prod_congr rfl fun PP hPP => by rw [hy PP (Finset.mem_union_left _ hPP)]
    · exact Finset.prod_congr rfl fun PP _ => by rw [hy PP.1 (Finset.mem_union_right _ PP.2)]
  have hSB := Frame.isSBHalf_datumFn (G := B.G) hB.frame hQ.1 hdep
  set Φ1 := B.F.datumFn B.G (B.de.Q ∪ Q) ω1
  have hv1 : B.vecAt Q (fun PP y => if PP.1 = P then 1 else φ PP.1 y) = Tm Φ1 := rfl

  have hlaw : ∀ k ∈ Finset.Icc 1 T.rank, ∀ γ ∈ R k, ω (1, γ) (Tm Φ1) =
      (((B.mu x : Circle) : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (S.rank / 2))) •
        Tm (fun t => Φ1 (actO S T (1 : GA D S)⁻¹ γ⁻¹ t)) := by
    intro k hk γ hγ
    have hγs := (hα k hk).2.1 γ hγ
    have hL := GlobalTheory.SplitLinear.law_place hω hB.frame.sdS hB.frame.sdT ho.1.idem ho.1.infPart_eq ho.2
      hB.frame.vac.2.theta hB.frame.vac.2.lat hTm he.1 hae (GlobalTheory.SplitHecke.suppAt_one S) hγs Φ1 hSB
    rw [hL]
    congr 1
    obtain ⟨-, k₁, hk₁, k₂, hk₂, hγe⟩ := ((hα k hk).2.2.1 γ hγ)
    have hH := GlobalTheory.T.modulus_unramifiedChar_det_heckeDoubleCoset_split D T P (idemAt P) he ϖ hϖ1 hϖ2 x hx k (α k) (hα k hk).1 k₁ hk₁ k₂ hk₂
      (GlobalTheory.VecInv.detAt (idemAt P) he.1.1 T γ) (by rw [← hγe]; exact GlobalTheory.VecInv.isDetAt_detAt _ he.1.1 T γ)
    obtain ⟨hH1, hH2⟩ := hH
    have hmu := hH2 Circle (B.mu * 1) (fun y h1 h2 h3 => by
      rw [mul_one]; exact mu_unram B hB hQ hP y h1 h2 h3)
    rw [mul_one] at hmu
    unfold GlobalTheory.SplitLinear.fac GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.modFac
    rw [map_one, splitFacO, map_one, inv_one, one_mul, mul_one, hmu, hH1]
    have habs : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin D 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absFin, GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
    rw [habs, Real.one_rpow, one_mul]
    obtain ⟨m, hm⟩ := hB.even
    have hn : S.rank = 2 * m := by omega
    rw [hn, inv_natPow_rpow_neg_half_even_eq_pow _ (Nat.pos_of_ne_zero hq0) k m, show 2 * m / 2 = m by omega]
    push_cast
    rfl

  have hfun : B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y) =
      Φ1 + ∑ k ∈ Finset.Icc 1 T.rank, ((-1 : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (k - 1) / 2)) •
        ∑ γ ∈ R k, fun t => Φ1 (actO S T (1 : GA D S)⁻¹ γ⁻¹ t) := by
    funext t
    rw [hdr t]
    simp [Finset.sum_apply, Pi.smul_apply, Φ1, ω1]
  have hv : B.vecAt Q (fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y) =
      Tm (B.F.datumFn B.G (B.de.Q ∪ Q) (B.locFn Q fun PP y => if PP.1 = P then ((prim y : ℚ) : ℂ) else φ PP.1 y)) := rfl
  rw [hv, hfun, map_add, map_sum, hv1]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [map_smul, map_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [hlaw k hk γ hγ, smul_smul]
  congr 1
  have hne : ((B.mu x : Circle) : ℂ) ^ k * ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (k * (S.rank / 2)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Circle.coe_ne_zero _)) (pow_ne_zero _ (Nat.cast_ne_zero.2 hq0))
  field_simp

end GlobalTheory.DistRel
