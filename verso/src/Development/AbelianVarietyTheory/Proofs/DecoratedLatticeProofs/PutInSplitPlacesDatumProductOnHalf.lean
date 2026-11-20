import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrOfMulEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorOrthogonalIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelCompIdempotentSplitTensorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceModelRestrictedTensorFixedHalfStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatumListConsEqIdempotentTensorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointIdempotentsOrthogonalSumPlacesStatement

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.PutIn

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem overAll_cons_iff (ψ : AddChar (AF D.host.F) ℂ) {p : ι → SplitPt D k} {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n n' k → ℂ) (i : ι) (J : List ι) (f f' : WO S T → ℂ) :
    OverAll ψ α β LS LT Ψ (i :: J) f f' ↔ ∃ g, OverAll ψ α β LS LT Ψ J f g ∧ Over ψ (α i) (β i) LS LT g (Ψ i) f' := Iff.rfl

/- English proof (translation)
Introduce `J`. Proceed by induction on `J with`. Consider the case `nil => intro _ _ i hi`. Simplify using `at hi`. Consider the case `cons j J ih`.

Introduce `f' h i hi`. Take `⟨g, hg, hO⟩` from `(overAll_cons_iff ψ α β LS LT Ψ j J f f').1 h`. Break down `List.mem_cons.1 hi with rfl | hi` into its components or cases. Conclude with `hO.2.2.2.1`. Conclude with `ih g hg i hi`.
-/
theorem sb_of_overAll (ψ : AddChar (AF D.host.F) ℂ) {p : ι → SplitPt D k} {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T) (Ψ : ι → Matrix n n' k → ℂ) (f : WO S T → ℂ) :
    ∀ (J : List ι) (f' : WO S T → ℂ), OverAll ψ α β LS LT Ψ J f f' → ∀ i ∈ J, Ψ i ∈ SB (Matrix n n' k) := by
  intro J
  induction J with
  | nil => intro _ _ i hi; simp at hi
  | cons j J ih =>
    intro f' h i hi
    obtain ⟨g, hg, hO⟩ := (overAll_cons_iff ψ α β LS LT Ψ j J f f').1 h
    rcases List.mem_cons.1 hi with rfl | hi
    · exact hO.2.2.2.1
    · exact ih g hg i hi

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `GlobalTheory.PlaceModel.latO_le_top _ h`. Introduce `h`. Take `⟨ε, hε, hsum⟩` from `p.above`.

Establish `he : p.e * p.e = p.e` using `p.split.1`. Establish `hεe : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e`. Rewrite using `[← hsum, add_mul, he, mul_comm (cA D p.e), p.split.2.1, add_zero]`. Establish `h1` using `(GlobalTheory.PlaceModel.idem_smul_mem hε he hεe h).1`. Establish `ht' : p.e • t = t` using `Matrix.ext fun i j => ht i j`.

Rewrite `h1` using `[ht']`. Then use the resulting hypothesis.
-/
theorem mem_latO_at_iff (p : SplitPt D k) {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (t : WO S T) (ht : IsHalf p.e t) : t ∈ latO S T LS LT (· = p.v) ↔ t ∈ latO S T LS LT fun _ => True := by
  constructor
  · intro h; exact GlobalTheory.PlaceModel.latO_le_top _ h
  · intro h
    obtain ⟨ε, hε, hsum⟩ := p.above
    have he : p.e * p.e = p.e := p.split.1
    have hεe : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, he, mul_comm (cA D p.e), p.split.2.1, add_zero]
    have h1 := (GlobalTheory.PlaceModel.idem_smul_mem hε he hεe h).1
    have ht' : p.e • t = t := Matrix.ext fun i j => ht i j
    rwa [ht'] at h1

/- English proof (translation)
Take `⟨hs, K, hK, hinv, hsup⟩` from `h`. Use `⟨hs, K, hK, fun u hu hh t => hinv u ((hcmp u hh).2 hu) hh t, fun t ht => (hcmp _ ?_).1 (hsup t ht)⟩` and prove the remaining obligations. Introduce `i j`. Rewrite using `[Matrix.smul_apply, nsmul_eq_mul, ← mul_assoc, mul_comm e, mul_assoc, hs t ht i j]`.
-/
theorem isSBHalf_of_half_iff {S T : HSp D} (e : AE D) (Λ Λ' : AddSubgroup (WO S T)) (Φ : WO S T → ℂ)
    (hcmp : ∀ t, IsHalf e t → (t ∈ Λ' ↔ t ∈ Λ)) (h : IsSBHalf e Λ' Φ) : IsSBHalf e Λ Φ := by
  obtain ⟨hs, K, hK, hinv, hsup⟩ := h
  refine ⟨hs, K, hK, fun u hu hh t => hinv u ((hcmp u hh).2 hu) hh t, fun t ht => (hcmp _ ?_).1 (hsup t ht)⟩
  intro i j
  rw [Matrix.smul_apply, nsmul_eq_mul, ← mul_assoc, mul_comm e, mul_assoc, hs t ht i j]

open Classical in
/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `h0 : IsHalf (0 : AE D) t → t ∈ Λ` using `fun ht => by`. Establish `: t = 0` using `Matrix.ext fun i j => by simpa [eq_comm] using ht i j`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Unfold `datJ halfInd`. Distinguish the cases in `ht : IsHalf (0 : AE D) t`. Rewrite using `[if_pos (by simpa [eSum] using ht), if_pos ⟨h0 ht, ht⟩]; rfl`. Rewrite using `[if_neg (by simpa [eSum] using ht), if_neg fun h => ht h.2]`.
-/
theorem datJ_nil (p : ι → SplitPt D k) {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n)
    (Ψ : ι → Matrix n n' k → ℂ) (Λ : AddSubgroup (WO S T)) : datJ p α β Ψ [] = halfInd 0 Λ := by
  funext t
  have h0 : IsHalf (0 : AE D) t → t ∈ Λ := fun ht => by
    have : t = 0 := Matrix.ext fun i j => by simpa [eq_comm] using ht i j
    rw [this]; exact zero_mem _
  unfold datJ halfInd
  by_cases ht : IsHalf (0 : AE D) t
  · rw [if_pos (by simpa [eSum] using ht), if_pos ⟨h0 ht, ht⟩]; rfl
  · rw [if_neg (by simpa [eSum] using ht), if_neg fun h => ht h.2]

/- English proof (translation)
Introduce `J`. Proceed by induction on `J with`. Consider the case `nil => intro _ _`. Rewrite using `[datJ_nil p α β Ψ (latO S T (LS : Set _) (LT : Set _) fun _ => True)]`. Conclude with `GlobalTheory.isSBHalf_halfInd _ _`.

Consider the case `cons i J ih`. Introduce `hJ hSB`. Rewrite `hJ` using `[List.nodup_cons]`. Establish `hort : ∀ j ∈ J, (p i).e * (p j).e = 0` using `fun j hj => horth i j fun h => hJ.1 (h ▸ hj)`. Rewrite using `[GlobalTheory.T.datum_list_cons_eq_idempotent_tensor D k ι p n n' S T α β Ψ i J hJ.1 hort, eSum_cons, add_comm]`.

Use `GlobalTheory.T.schwartzBruhat_half_tensor_orthogonal_idempotents D S T _ _ _ _ _ (eSum_mul p _ J fun j hj => by rw [mul_comm]; exact hort j hj) (p i).split.1 (fun u hu => GlobalTheory.PlaceModelSum.idem_smul_latO (p i).split.1 hu) (ih hJ.2 fun j hj => hSB j (List.mem_cons_of_mem …` and prove the remaining obligations. Conclude with `isSBHalf_of_half_iff _ _ _ _ (fun t ht => mem_latO_at_iff (p i) _ _ t ht) (SBHalfAt.isSBHalf_extFun_latO D k (p i) S T n n' (α i) (β i) LS LT hSD hTD (Ψ i) (hSB i List.mem_cons_self))`.
-/
theorem datJ_SB (p : ι → SplitPt D k) {S T : HSp D} (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n)
    (Ψ : ι → Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (hSD : IsSelfDualC S LS) (hTD : IsSelfDualC T LT)
    (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) :
    ∀ J : List ι, J.Nodup → (∀ i ∈ J, Ψ i ∈ SB (Matrix n n' k)) →
      IsSBHalf (eSum p J) (latO S T (LS : Set _) (LT : Set _) fun _ => True) (datJ p α β Ψ J) := by
  intro J
  induction J with
  | nil => intro _ _; rw [datJ_nil p α β Ψ (latO S T (LS : Set _) (LT : Set _) fun _ => True)]; exact GlobalTheory.isSBHalf_halfInd _ _
  | cons i J ih =>
    intro hJ hSB
    rw [List.nodup_cons] at hJ
    have hort : ∀ j ∈ J, (p i).e * (p j).e = 0 := fun j hj => horth i j fun h => hJ.1 (h ▸ hj)
    rw [GlobalTheory.T.datum_list_cons_eq_idempotent_tensor D k ι p n n' S T α β Ψ i J hJ.1 hort, eSum_cons, add_comm]
    refine GlobalTheory.T.schwartzBruhat_half_tensor_orthogonal_idempotents D S T _ _ _ _ _ (eSum_mul p _ J fun j hj => by rw [mul_comm]; exact hort j hj) (p i).split.1
      (fun u hu => GlobalTheory.PlaceModelSum.idem_smul_latO (p i).split.1 hu) (ih hJ.2 fun j hj => hSB j (List.mem_cons_of_mem _ hj)) ?_
    exact isSBHalf_of_half_iff _ _ _ _ (fun t ht => mem_latO_at_iff (p i) _ _ t ht)
      (SBHalfAt.isSBHalf_extFun_latO D k (p i) S T n n' (α i) (β i) LS LT hSD hTD (Ψ i) (hSB i List.mem_cons_self))

/- English proof (translation)
Introduce `J`. Proceed by induction on `J with`. Consider the case `nil`. Introduce `_ f' Tm hTm h`. Establish `h1 : f' = f` using `h`.

Rewrite using `[h1, datJ_nil p α β Ψ (latO S T (LS : Set _) (LT : Set _) fun _ => True), ← hTm.vac, one_smul]`. Both sides reduce to the same expression. Consider the case `cons i J ih`. Introduce `hJ f' Tm hTm h`. Take `⟨g, hg, hO⟩` from `(overAll_cons_iff ψ α β LS LT Ψ i J f f').1 h`.

Establish `hJ'` using `List.nodup_cons.1 hJ`. Establish `hort : ∀ j ∈ J, (p i).e * (p j).e = 0` using `fun j hj => horth i j fun h => hJ'.1 (h ▸ hj)`. Establish `hmul : eSum p J * (p i).e = 0` using `eSum_mul p _ J fun j hj => by rw [mul_comm]; exact hort j hj`. Establish `hstab : ∀ u ∈ (latO S T (LS : Set _) (LT : Set _) fun _ => True), (p i).e • u ∈ (latO S T (LS : Set _) (LT : Set _) fun _ => True)` using `fun u hu => GlobalTheory.PlaceModelSum.idem_smul_latO (p i).split.1 hu`. Rewrite `hTm` using `[eSum_cons, add_comm]`.

Establish `hA` using `GlobalTheory.T.isPlaceModel_comp_idempotentSplitTensor D ψ S T (eSum p J) (p i).e _ f Tm hmul (p i).split.1 hstab hTm`. Establish `hg' : g = Tm (tens (p i).e (datJ p α β Ψ J) (halfInd (p i).e (latO S T (LS : Set _) (LT : Set _) fun _ => True)))` using `ih hJ'.2 g _ hA hg`. Establish `hSBJ` using `datJ_SB p α β Ψ LS LT hSD hTD horth J hJ'.2 (sb_of_overAll ψ α β LS LT Ψ f J g hg)`. Establish `hcmp : ∀ t, IsHalf (p i).e t → (t ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v) ↔ t ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True)` using `fun t ht => mem_latO_at_iff (p i) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) t ht`. Establish `hB` using `GlobalTheory.T.place_model_restricted_tensor_fixed_half D ψ S T (eSum p J) (p i).e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v)) (datJ p …`.

Rewrite `hB` using `[← hg']`. Rewrite using `[hO.2.2.2.2.2 _ hB, LinearMap.comp_apply, tensR_apply, GlobalTheory.T.datum_list_cons_eq_idempotent_tensor D k ι p n n' S T α β Ψ i J hJ'.1 hort]`.
-/
theorem overAll_eq (ψ : AddChar (AF D.host.F) ℂ) (p : ι → SplitPt D k) {S T : HSp D} (α : ∀ i, Frame (p i) S n')
    (β : ∀ i, Frame (p i) T n) (Ψ : ι → Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (hSD : IsSelfDualC S LS)
    (hTD : IsSelfDualC T LT) (horth : ∀ i j, i ≠ j → (p i).e * (p j).e = 0) (f : WO S T → ℂ) :
    ∀ J : List ι, J.Nodup → ∀ (f' : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)),
      IsPlaceModel ψ (symplO S T) (heisO ψ S T) (eSum p J) (latO S T (LS : Set _) (LT : Set _) fun _ => True) 1 f Tm →
      OverAll ψ α β LS LT Ψ J f f' → f' = Tm (datJ p α β Ψ J) := by
  intro J
  induction J with
  | nil =>
    intro _ f' Tm hTm h
    have h1 : f' = f := h
    rw [h1, datJ_nil p α β Ψ (latO S T (LS : Set _) (LT : Set _) fun _ => True), ← hTm.vac, one_smul]
    rfl
  | cons i J ih =>
    intro hJ f' Tm hTm h
    obtain ⟨g, hg, hO⟩ := (overAll_cons_iff ψ α β LS LT Ψ i J f f').1 h
    have hJ' := List.nodup_cons.1 hJ
    have hort : ∀ j ∈ J, (p i).e * (p j).e = 0 := fun j hj => horth i j fun h => hJ'.1 (h ▸ hj)
    have hmul : eSum p J * (p i).e = 0 := eSum_mul p _ J fun j hj => by rw [mul_comm]; exact hort j hj
    have hstab : ∀ u ∈ (latO S T (LS : Set _) (LT : Set _) fun _ => True), (p i).e • u ∈ (latO S T (LS : Set _) (LT : Set _) fun _ => True) :=
      fun u hu => GlobalTheory.PlaceModelSum.idem_smul_latO (p i).split.1 hu
    rw [eSum_cons, add_comm] at hTm
    have hA := GlobalTheory.T.isPlaceModel_comp_idempotentSplitTensor D ψ S T (eSum p J) (p i).e _ f Tm hmul (p i).split.1 hstab hTm
    have hg' : g = Tm (tens (p i).e (datJ p α β Ψ J) (halfInd (p i).e (latO S T (LS : Set _) (LT : Set _) fun _ => True))) :=
      ih hJ'.2 g _ hA hg
    have hSBJ := datJ_SB p α β Ψ LS LT hSD hTD horth J hJ'.2
      (sb_of_overAll ψ α β LS LT Ψ f J g hg)
    have hcmp : ∀ t, IsHalf (p i).e t → (t ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v) ↔
        t ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True) :=
      fun t ht => mem_latO_at_iff (p i) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) t ht
    have hB := GlobalTheory.T.place_model_restricted_tensor_fixed_half D ψ S T (eSum p J) (p i).e (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) fun _ => True)
      (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = (p i).v)) (datJ p α β Ψ J) f Tm
      hmul (p i).split.1 hstab hcmp hSBJ hTm
    rw [← hg'] at hB
    rw [hO.2.2.2.2.2 _ hB, LinearMap.comp_apply, tensR_apply, GlobalTheory.T.datum_list_cons_eq_idempotent_tensor D k ι p n n' S T α β Ψ i J hJ'.1 hort]

/- English proof (translation)
Introduce `D k _ _ _ _ ι p J hPl n n' _ _ _ _ ψ hψ S T α β LS LT hSD hTD hLS hLT Pset e hIdem hEq Ψ f f' hθf hvac hOver`. Take `⟨horth, rfl⟩` from `GlobalTheory.T.split_point_idempotents_orthogonal_sum_places D k ι p J _ hPl Pset e hIdem hEq`. Establish `hΛ : stdHom S T = latO S T (LS : Set _) (LT : Set _) (fun _ => True)`. Establish `h1 : (LS : Set (Fin S.rank → D.host.E)) = intVec D S.rank` using `Set.ext hLS`. Establish `h2 : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank` using `Set.ext hLT`.

Rewrite using `[h1, h2]`. Establish `hid` using `eSum_idem p horth J hPl.nodup`. Unfold `IsRatDatum`. Rewrite `hvac`, the goal using `[hΛ]`. Use `⟨datJ p α β Ψ J, datJ_SB p α β Ψ LS LT hSD hTD horth J hPl.nodup (sb_of_overAll ψ α β LS LT Ψ f J f' hOver), ?_, ?_⟩` and prove the remaining obligations.

Introduce `γ`. Establish `hh : IsHalf (eSum p J) (γ.map fun a => eSum p J * incA D a)` using `fun i j => by`. Rewrite using `[Matrix.map_apply, ← mul_assoc, hid]`. Unfold `datJ`. Rewrite using `[if_pos hh]`.

Use `congr 1`. Use `List.map_congr_left fun i hi => ?_` and prove the remaining obligations. Use `congr 1`. Unfold `rd`. Use `congr 2`.

Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, map_mul, pr_eSum p horth J hPl.nodup i hi, one_mul]`. Conclude with `⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ S T LS LT hSD hTD Pset _ hIdem f hθf hvac).1, fun Tm hTm => overAll_eq ψ p α β Ψ LS LT hSD hTD horth f J hPl.nodup f' Tm hTm hOver⟩`.
-/
theorem ratDatum_of_overAll : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt D k) (J : List ι), Places p J (fun v => ∃ i, v = (p i).v) →
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (α : ∀ i, Frame (p i) S n') (β : ∀ i, Frame (p i) T n) (LS : Lat S) (LT : Lat T),
    IsSelfDualC S LS → IsSelfDualC T LT → (∀ z, z ∈ LS ↔ z ∈ intVec D S.rank) → (∀ z, z ∈ LT ↔ z ∈ intVec D T.rank) →
    ∀ (Pset : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e Pset →
    (∃ eq : ι ≃ Pset, ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e (eq i).1) →
    ∀ (Ψ : ι → Matrix n n' k → ℂ) (f f' : WO S T → ℂ), IsThetaFunO ψ S T f → IsLatVac (heisO ψ S T) (stdHom S T) f →
    OverAll ψ α β LS LT Ψ J f f' →
    IsRatDatum ψ S T e (fun γ => (J.map fun i => Ψ i (rd (α i) (β i) (γ.map (incA D)))).prod) f f' := by
  intro D k _ _ _ _ ι p J hPl n n' _ _ _ _ ψ hψ S T α β LS LT hSD hTD hLS hLT Pset e hIdem hEq Ψ f f' hθf hvac hOver
  obtain ⟨horth, rfl⟩ := GlobalTheory.T.split_point_idempotents_orthogonal_sum_places D k ι p J _ hPl Pset e hIdem hEq
  have hΛ : stdHom S T = latO S T (LS : Set _) (LT : Set _) (fun _ => True) := by
    have h1 : (LS : Set (Fin S.rank → D.host.E)) = intVec D S.rank := Set.ext hLS
    have h2 : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank := Set.ext hLT
    rw [h1, h2]
  have hid := eSum_idem p horth J hPl.nodup
  unfold IsRatDatum
  rw [hΛ] at hvac ⊢
  refine ⟨datJ p α β Ψ J, datJ_SB p α β Ψ LS LT hSD hTD horth J hPl.nodup (sb_of_overAll ψ α β LS LT Ψ f J f' hOver), ?_, ?_⟩
  · intro γ
    have hh : IsHalf (eSum p J) (γ.map fun a => eSum p J * incA D a) := fun i j => by
      rw [Matrix.map_apply, ← mul_assoc, hid]
    unfold datJ
    rw [if_pos hh]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    congr 1
    unfold rd
    congr 2
    ext a b
    simp only [Matrix.map_apply, map_mul, pr_eSum p horth J hPl.nodup i hi, one_mul]
  · exact ⟨(GlobalTheory.PlaceModelSum.placeModelExistsSum D ψ hψ S T LS LT hSD hTD Pset _ hIdem f hθf hvac).1,
      fun Tm hTm => overAll_eq ψ p α β Ψ LS LT hSD hTD horth f J hPl.nodup f' Tm hTm hOver⟩

end GlobalTheory.FinPl.PutIn

end
