import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

set_option synthInstance.maxHeartbeats 160000

namespace GlobalTheory.SelfDualAt

variable {D : D7}

open Classical in

def indP (P : Pl D → Prop) : Af D.host.F :=
  ⟨fun v => if P v then 1 else 0, Filter.Eventually.of_forall fun v => by
    by_cases h : P v
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

open Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_indP (P : Pl D → Prop) (v : Pl D) : evalV D.host.F v (indP P) = if P v then 1 else 0 := rfl

def cP (P : Pl D → Prop) : AF D.host.F := pairA D.host.F 0 (indP P)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _`. Rewrite using `[map_one]`. Both sides reduce to the same expression.
-/
theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]
  rfl

/- English proof (translation)
Unfold `hO`. Simplify using `only [Matrix.smul_apply, Algebra.smul_def, map_mul, cA_alg]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring` and prove the remaining obligations.
-/
theorem hO_smul_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) : hO S T x (c • y) = hO S T (c • x) y := by
  unfold hO
  simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, cA_alg]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring

/- English proof (translation)
Unfold `symplO`. Rewrite using `[hO_smul_swap]`.
-/
theorem symplO_smul_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = symplO S T (c • x) y := by
  unfold symplO
  rw [hO_smul_swap]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Establish `h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (a ⊗ₜ[D.host.F] e) = evalV D.host.F w a ⊗ₜ[D.host.F] e` using `rfl`. Rewrite using `[h, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]`.

Simplify using `[Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]`. Consider the case `add x y hx hy`. Simplify using `only [RingHom.map_add, LinearEquiv.map_add, Finsupp.add_apply, hx, hy]`. Conclude with `(RingHom.map_add (evalV D.host.F w).toRingHom _ _).symm`.
-/
theorem compFin_repr (w : Pl D) (y : Af D.host.F ⊗[D.host.F] D.host.E) (k : Fin (Module.finrank D.host.F D.host.E)) :
    (Algebra.TensorProduct.basis (Fv D.host.F w) (Module.finBasis D.host.F D.host.E)).repr
        (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w y) k =
      evalV D.host.F w ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (a ⊗ₜ[D.host.F] e) = evalV D.host.F w a ⊗ₜ[D.host.F] e := rfl
    rw [h, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul]
    simp [Finsupp.smul_apply, Finsupp.mapRange_apply, map_mul, AlgHom.commutes]
  | add x y hx hy =>
    simp only [RingHom.map_add, LinearEquiv.map_add, Finsupp.add_apply, hx, hy]
    exact (RingHom.map_add (evalV D.host.F w).toRingHom _ _).symm

/- English proof (translation)
Establish `hr : (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y = 0`. Use `Finsupp.ext fun k => ?_` and prove the remaining obligations. Establish `hk : ∀ w : Pl D, evalV D.host.F w ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0` using `fun w => by`. Rewrite using `[← compFin_repr, h w, map_zero]`. Both sides reduce to the same expression.

Rewrite using `[Finsupp.zero_apply]`. Use `FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_` and prove the remaining obligations. Conclude with `hk w`. Simplify using `using hr`.
-/
theorem eq_zero_of_compFin (y : Af D.host.F ⊗[D.host.F] D.host.E) (h : ∀ w, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w y = 0) :
    y = 0 := by
  have hr : (Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y = 0 := by
    refine Finsupp.ext fun k => ?_
    have hk : ∀ w : Pl D, evalV D.host.F w
        ((Algebra.TensorProduct.basis (Af D.host.F) (Module.finBasis D.host.F D.host.E)).repr y k) = 0 := fun w => by
      rw [← compFin_repr, h w, map_zero]; rfl
    rw [Finsupp.zero_apply]
    refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
    exact hk w
  simpa using hr

set_option maxHeartbeats 800000 in
/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]`. Establish `h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (sndA D.host.F (cP P) ⊗ₜ[D.host.F] (1 : D.host.E)) = evalV D.host.F w (indP P) ⊗ₜ[D.host.F] (1 : D.host.E)`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Both sides reduce to the same expression. Rewrite using `[h, evalV_indP, if_pos hw]`.

Conclude with `Algebra.TensorProduct.one_def.symm`.
-/
theorem compFin_alg_cP (P : Pl D → Prop) (w : Pl D) (hw : P w) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (algebraMap (AF D.host.F) (AE D) (cP P))) = 1 := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, GlobalTheory.LatVac.finPart_tmul]
  have h : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (sndA D.host.F (cP P) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      evalV D.host.F w (indP P) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    rfl
  rw [h, evalV_indP, if_pos hw]
  exact Algebra.TensorProduct.one_def.symm

set_option maxHeartbeats 800000 in

/- English proof (translation)
Rewrite `hz` using `[idAt, Ideal.mem_inf, Ideal.mem_iInf]`. Take `⟨hinf, hfin⟩` from `hz`. Rewrite `hinf` using `[RingHom.mem_ker]`. Establish `h0 : (1 - algebraMap (AF D.host.F) (AE D) (cP P)) * z = 0`. Apply `GlobalTheory.LatVac.eq_zero_of_parts` to reduce the goal to its premises.

Rewrite using `[RingHom.map_mul, hinf, mul_zero]`. Apply `eq_zero_of_compFin` to reduce the goal to its premises. Introduce `w`. Rewrite using `[RingHom.map_mul, RingHom.map_mul]`. Distinguish the cases in `hw : P w`.

Rewrite using `[RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, compFin_alg_cP P w hw, sub_self, zero_mul]`. Establish `h1` using `hfin ⟨w, hw⟩`. Rewrite `h1` using `[RingHom.mem_ker]`. Rewrite using `[show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D z) = compAt D w z from rfl, h1, mul_zero]`. Rewrite `h0` using `[sub_mul, one_mul, sub_eq_zero]`.

Conclude with `h0.symm`.
-/
theorem algebraMap_placeIdempotent_mul (P : Pl D → Prop) (z : AE D) (hz : z ∈ idAt D P) :
    algebraMap (AF D.host.F) (AE D) (cP P) * z = z := by
  rw [idAt, Ideal.mem_inf, Ideal.mem_iInf] at hz
  obtain ⟨hinf, hfin⟩ := hz
  rw [RingHom.mem_ker] at hinf
  have h0 : (1 - algebraMap (AF D.host.F) (AE D) (cP P)) * z = 0 := by
    apply GlobalTheory.LatVac.eq_zero_of_parts
    · rw [RingHom.map_mul, hinf, mul_zero]
    · apply eq_zero_of_compFin
      intro w
      rw [RingHom.map_mul, RingHom.map_mul]
      by_cases hw : P w
      · rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_one, compFin_alg_cP P w hw, sub_self, zero_mul]
      · have h1 := hfin ⟨w, hw⟩
        rw [RingHom.mem_ker] at h1
        rw [show GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D z) = compAt D w z from rfl, h1, mul_zero]
  rw [sub_mul, one_mul, sub_eq_zero] at h0
  exact h0.symm

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩` from `hy`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Use `⟨indP P * α, ?_, ?_, a, ha, s, hs, t, ht, ?_⟩` and prove the remaining obligations.

Introduce `v`. Rewrite using `[map_mul]`. Use `mul_mem ?_ (hα v)` and prove the remaining obligations. Rewrite using `[evalV_indP]`. Use `split_ifs`.

Conclude with `one_mem _`. Conclude with `zero_mem _`. Introduce `v hv`. Rewrite using `[map_mul, evalV_indP, if_neg hv, zero_mul]`. Use extensionality with `i j`.

Rewrite using `[Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, TensorProduct.smul_tmul', smul_eq_mul]`. Use `congr 1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use `show (0 : Ainf D.host.F) * 0 = 0`. Rewrite using `[zero_mul]`.

Both sides reduce to the same expression. Consider the case `zero => rw [smul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ h1 h2 => rw [smul_add]`. Conclude with `add_mem h1 h2`.

Consider the case `neg x _ h => rw [smul_neg]`. Conclude with `neg_mem h`.
-/
theorem smul_mem_latO (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : Pl D → Prop) (y : WO S T) (hy : y ∈ latO S T LS LT fun _ => True) : cP P • y ∈ latO S T LS LT P := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨indP P * α, ?_, ?_, a, ha, s, hs, t, ht, ?_⟩
    · intro v
      rw [map_mul]
      refine mul_mem ?_ (hα v)
      rw [evalV_indP]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro v hv
      rw [map_mul, evalV_indP, if_neg hv, zero_mul]
    · ext i j
      rw [Matrix.smul_apply, Matrix.of_apply, Matrix.of_apply, TensorProduct.smul_tmul', smul_eq_mul]
      congr 1
      refine Prod.ext ?_ ?_
      · show (0 : Ainf D.host.F) * 0 = 0
        rw [zero_mul]
      · rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h => rw [smul_neg]; exact neg_mem h

/- English proof (translation)
Introduce `D ψ hψ S T LS LT hS hT P u hu`. Establish `key` using `(GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1`. Establish `hinf : u.map (infPart D) = 0`. Use extensionality with `i j`. Establish `h` using `(Ideal.mem_inf.1 (hu i j)).1`.

Rewrite `h` using `[RingHom.mem_ker]`. Simplify using `using h`. Establish `hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True`. Apply `AddSubgroup.closure_mono` to reduce the goal to its premises. Introduce and unpack `w ⟨α, hα, -, rest⟩`.

Conclude with `⟨α, hα, fun v h => (h trivial).elim, rest⟩`. Establish `hfix : cP P • u = u`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply, Algebra.smul_def]`. Conclude with `algebraMap_placeIdempotent_mul P _ (hu i j)`.

Prove the components needed by the constructor for the conclusion. Introduce `hm u' hu'`. Conclude with `(key u hinf).1 (hle hm) u' (hle hu')`. Introduce `hann`. Establish `h2 : ∀ y ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ψ (symplO S T u y) = 1`.

Introduce `y hy`. Establish `h` using `hann _ (smul_mem_latO S T _ _ P y hy)`. Rewrite `h` using `[symplO_smul_swap, hfix]`. Then use the resulting hypothesis. Rewrite using `[← hfix]`. Conclude with `smul_mem_latO S T _ _ P u ((key u hinf).2 h2)`.
-/
theorem latO_ann_at : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (LS : Lat S) (LT : Lat T), IsSelfDualC S LS → IsSelfDualC T LT → ∀ (P : Pl D → Prop) (u : WO S T), MxAt P u → (u ∈ latO S T (LS : Set _) (LT : Set _) P ↔ ∀ u' ∈ latO S T (LS : Set _) (LT : Set _) P, ψ (symplO S T u u') = 1) := by
  intro D ψ hψ S T LS LT hS hT P u hu
  have key := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T LS LT hψ hS hT).1
  have hinf : u.map (infPart D) = 0 := by
    ext i j
    have h := (Ideal.mem_inf.1 (hu i j)).1
    rw [RingHom.mem_ker] at h
    simpa using h
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun v h => (h trivial).elim, rest⟩
  have hfix : cP P • u = u := by
    ext i j
    rw [Matrix.smul_apply, Algebra.smul_def]
    exact algebraMap_placeIdempotent_mul P _ (hu i j)
  constructor
  · intro hm u' hu'
    exact (key u hinf).1 (hle hm) u' (hle hu')
  · intro hann
    have h2 : ∀ y ∈ latO S T (LS : Set _) (LT : Set _) (fun _ => True), ψ (symplO S T u y) = 1 := by
      intro y hy
      have h := hann _ (smul_mem_latO S T _ _ P y hy)
      rwa [symplO_smul_swap, hfix] at h
    rw [← hfix]
    exact smul_mem_latO S T _ _ P u ((key u hinf).2 h2)

end GlobalTheory.SelfDualAt

end
