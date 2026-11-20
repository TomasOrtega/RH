import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalFrobeniusPullbackBasisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `tmul a t`. Rewrite using `[TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul, ← congrFun (LinearMap.toMatrix_mulVec_repr b b r t) i, Matrix.mulVec, dotProduct, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations.

Rewrite using `[Module.Basis.baseChange_repr_tmul, map_smul, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]`. Consider the case `add y z hy hz`. Rewrite using `[map_add, map_add, Finsupp.add_apply, hy, hz, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Simplify using `only [map_add, Finsupp.add_apply, mul_add]`.
-/
theorem repr_map_baseChange {l : ℕ} [Fact l.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[l] T] {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) (s : WCb l →ₗ[ℤ_[l]] WCb l) (r : T →ₗ[ℤ_[l]] T)
    (y : WCb l ⊗[ℤ_[l]] T) (i : Fin d) :
    (b.baseChange (WCb l)).repr (TensorProduct.map s r y) i =
      ∑ n, algebraMap ℤ_[l] (WCb l) (LinearMap.toMatrix b b r i n) * s ((b.baseChange (WCb l)).repr y n) := by
  induction y with
  | zero => simp
  | tmul a t =>
    rw [TensorProduct.map_tmul, Module.Basis.baseChange_repr_tmul,
      ← congrFun (LinearMap.toMatrix_mulVec_repr b b r t) i, Matrix.mulVec, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Module.Basis.baseChange_repr_tmul, map_smul, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
  | add y z hy hz =>
    rw [map_add, map_add, Finsupp.add_apply, hy, hz, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [map_add, Finsupp.add_apply, mul_add]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `l _ K bk d S M e hF T _ _ ρ j H`. Establish `hfin` using `H.finite`. Establish `hfree` using `H.free`. Take `⟨e', he'⟩` from `GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) (Fin d) e`. Take `⟨c, hc⟩` from `GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ j H.bc (Fin d) e'`.

Establish `hrank : Module.finrank ℤ_[l] T = d`. Rewrite using `[← Module.finrank_baseChange (R := WCb l), Module.finrank_eq_card_basis c, Fintype.card_fin]`. Set `b` to `Module.finBasisOfFinrankEq ℤ_[l] T hrank`. Set `U : Matrix (Fin d) (Fin d) (WCb l)` to `(b.baseChange (WCb l)).toMatrix c`. Establish `hck : ∀ k, c k = ∑ i, U i k • (b.baseChange (WCb l)) i` using `fun k => ((b.baseChange (WCb l)).sum_repr (c k)).symm`.

Establish `hcj : ∀ k, c k = j (M.tr bk.ι (e k))` using `fun k => by rw [hc, he']`. Use `⟨b, U, ⟨?_, ?_, ?_⟩, fun k => ?_⟩` and prove the remaining obligations. Use `letI := (b.baseChange (WCb l)).invertibleToMatrix c`. Conclude with `isUnit_of_invertible _`. Establish `hu : IsUnit (inclW l (bk.ev bk.E))` using `isUnit_inclW_of_span bk.span_ev`.

Set `t : ↥(ainfObj K).I` to `⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩`. Establish `hu' : IsUnit (((inclW l).comp (ainfId K).toRingHom) (t : (ainfObj K).A))` using `hu`. Establish `ht0 : (t : (ainfObj K).A) ≠ 0` using `fun h => hu'.ne_zero (by rw [h, map_zero])`. Establish `key : ∀ k, inclW l (bk.ev bk.E) ^ S.a • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k) = ∑ i, bk.evW (S.A i k) • c i`. Introduce `k`.

Establish `hsum : ∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j') = M.tr bk.ι (e k)`. Simplify using `[Pi.single_apply]`. Take `⟨m, s, hm⟩` from `exists_isFrac (t : (ainfObj K).A) (M.Φ (ainfObj K) t (∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j')))`. Take `⟨r, hr⟩` from `GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι t _ m s hm`. Use `replace hm : IsFrac (t : (ainfObj K).A) (M.Φ (ainfObj K) t (M.tr bk.ι (e k))) m s := by`.

Simplify `hm` using `only [hsum]`. Establish `hj : inclW l (bk.ev bk.E) ^ s • TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (M.tr bk.ι (e k))) = j m` using `H.j_φ t ht0 _ m s hm`. Establish `hφ1 : (fun j' => (ainfObj K).D.φ ((Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j')) = (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A)`. Use function extensionality and compare the values at `fun j' => by`. Distinguish the cases in `h : j' = k`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`. Rewrite `hr` using `[hφ1]`. Establish `hr3` using `(j.map_smulₛₗ ((t : (ainfObj K).A) ^ r) _).symm.trans ((congrArg j hr).trans j.map_zero)`.

Establish `hur : IsUnit (((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ r))`. Rewrite using `[map_pow]`. Conclude with `hu'.pow r`. Establish `hr5` using `sub_eq_zero.1 ((j.map_sub _ _).symm.trans (hur.smul_eq_zero.1 hr3))`. Establish `hr7` using `(j.map_smulₛₗ _ _).symm.trans (hr5.trans (j.map_smulₛₗ _ _))`.

Establish `e1 : ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) = inclW l (bk.ev bk.E) ^ S.a` using `map_pow _ _ _`. Establish `e2 : ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) = inclW l (bk.ev bk.E) ^ s` using `map_pow _ _ _`. Establish `hsum2 : j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) = ∑ i, bk.evW (S.A i k) • c i`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.map_smulₛₗ, ← hcj, Matrix.mulVec_single_one]`. Both sides reduce to the same expression. Apply `(hu.pow s).smul_left_cancel.1` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcj, smul_smul, smul_smul, mul_comm]`.

Use `_ = inclW l (bk.ev bk.E) ^ S.a • j m := congrArg _ hj`. Use `_ = ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) • j m := congrArg (· • j m) e1.symm`. Use `_ = ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) • j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) := hr7`. Use `_ = inclW l (bk.ev bk.E) ^ s • ∑ i, bk.evW (S.A i k) • c i := by rw [e2, hsum2]`. Establish `hev : ∀ x, bk.evW x = inclW l (bk.ev x)` using `fun _ => rfl`.

Use `Matrix.ext fun i k => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun y => (b.baseChange (WCb l)).repr y i) (key k)`. Simplify using `only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, repr_map_baseChange, LinearMap.toMatrix_id, Matrix.one_apply, smul_eq_mul, apply_ite (algebraMap ℤ_[l] (WCb l)), map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ …`. Simplify using `only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul, hev, U, Module.Basis.toMatrix_apply]`. Rewrite using `[h]`.

Conclude with `Finset.sum_congr rfl fun x _ => by rw [hev, mul_comm]`. Introduce `g`. Establish `keyg : ∀ k, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (c k) = ∑ i, inclW l (S.ε bk.ι ((ainfHom K g).comp bk.ι) i k) • c i`. Introduce `k`. Rewrite using `[hcj, ← H.j_act_of g (ainfHom K g) (fun _ => rfl), ← M.tr_comp, hF.tr bk.ι ((ainfHom K g).comp bk.ι) k, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, ← hcj]`. Both sides reduce to the same expression. Use `Matrix.ext fun i k => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun y => (b.baseChange (WCb l)).repr y i) (keyg k)`.

Simplify using `only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply, repr_map_baseChange, smul_eq_mul, AlgEquiv.toLinearMap_apply] at h`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, U, Module.Basis.toMatrix_apply, zW]`. Rewrite using `[h]`. Conclude with `Finset.sum_congr rfl fun x _ => mul_comm _ _`. Rewrite using `[← hcj, hck]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem exists_mReal_of_realises : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] (ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)), Realises K M (ainfObj K) (ainfId K) T ρ j → ∃ (b : Module.Basis (Fin d) ℤ_[l] T) (U : Matrix (Fin d) (Fin d) (WCb l)), MReal S (fun g => LinearMap.toMatrix b b (ρ g)) U ∧ ∀ k, j (M.tr bk.ι (e k)) = ∑ i, U i k ⊗ₜ[ℤ_[l]] b i := by
  intro l _ K bk d S M e hF T _ _ ρ j H
  have hfin := H.finite
  have hfree := H.free
  obtain ⟨e', he'⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ (M.tr bk.ι) (M.tr_bc bk.ι) (Fin d) e
  obtain ⟨c, hc⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ _ _ _ j H.bc (Fin d) e'
  have hrank : Module.finrank ℤ_[l] T = d := by
    rw [← Module.finrank_baseChange (R := WCb l), Module.finrank_eq_card_basis c, Fintype.card_fin]
  let b := Module.finBasisOfFinrankEq ℤ_[l] T hrank
  let U : Matrix (Fin d) (Fin d) (WCb l) := (b.baseChange (WCb l)).toMatrix c
  have hck : ∀ k, c k = ∑ i, U i k • (b.baseChange (WCb l)) i := fun k => ((b.baseChange (WCb l)).sum_repr (c k)).symm
  have hcj : ∀ k, c k = j (M.tr bk.ι (e k)) := fun k => by rw [hc, he']
  refine ⟨b, U, ⟨?_, ?_, ?_⟩, fun k => ?_⟩
  · letI := (b.baseChange (WCb l)).invertibleToMatrix c
    exact isUnit_of_invertible _
  · have hu : IsUnit (inclW l (bk.ev bk.E)) := isUnit_inclW_of_span bk.span_ev
    let t : ↥(ainfObj K).I := ⟨bk.ι.f bk.E, bk.ι.f_I _ (Ideal.mem_span_singleton_self _)⟩
    have hu' : IsUnit (((inclW l).comp (ainfId K).toRingHom) (t : (ainfObj K).A)) := hu
    have ht0 : (t : (ainfObj K).A) ≠ 0 := fun h => hu'.ne_zero (by rw [h, map_zero])
    have key : ∀ k, inclW l (bk.ev bk.E) ^ S.a • TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k) =
        ∑ i, bk.evW (S.A i k) • c i := by
      intro k
      have hsum : ∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j') = M.tr bk.ι (e k) := by
        simp [Pi.single_apply]
      obtain ⟨m, s, hm⟩ := exists_isFrac (t : (ainfObj K).A)
        (M.Φ (ainfObj K) t (∑ j', (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j' • M.tr bk.ι (e j')))
      obtain ⟨r, hr⟩ := GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ (ainfObj K) bk.ι t _ m s hm
      replace hm : IsFrac (t : (ainfObj K).A) (M.Φ (ainfObj K) t (M.tr bk.ι (e k))) m s := by
        simpa only [hsum] using hm
      have hj : inclW l (bk.ev bk.E) ^ s • TensorProduct.map (frobW l).toLinearMap LinearMap.id
          (j (M.tr bk.ι (e k))) = j m := H.j_φ t ht0 _ m s hm
      have hφ1 : (fun j' => (ainfObj K).D.φ ((Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) j')) =
          (Pi.single k (1 : (ainfObj K).A) : Fin d → (ainfObj K).A) :=
        funext fun j' => by
          by_cases h : j' = k
          · subst h; simp
          · simp [Pi.single_apply, h]
      rw [hφ1] at hr
      have hr3 := (j.map_smulₛₗ ((t : (ainfObj K).A) ^ r) _).symm.trans ((congrArg j hr).trans j.map_zero)
      have hur : IsUnit (((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ r)) := by
        rw [map_pow]; exact hu'.pow r
      have hr5 := sub_eq_zero.1 ((j.map_sub _ _).symm.trans (hur.smul_eq_zero.1 hr3))
      have hr7 := (j.map_smulₛₗ _ _).symm.trans (hr5.trans (j.map_smulₛₗ _ _))
      have e1 : ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) = inclW l (bk.ev bk.E) ^ S.a :=
        map_pow _ _ _
      have e2 : ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) = inclW l (bk.ev bk.E) ^ s :=
        map_pow _ _ _
      have hsum2 : j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) =
          ∑ i, bk.evW (S.A i k) • c i := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [LinearMap.map_smulₛₗ, ← hcj, Matrix.mulVec_single_one]
        rfl
      apply (hu.pow s).smul_left_cancel.1
      calc inclW l (bk.ev bk.E) ^ s • (inclW l (bk.ev bk.E) ^ S.a •
              TensorProduct.map (frobW l).toLinearMap LinearMap.id (c k))
          = inclW l (bk.ev bk.E) ^ S.a • (inclW l (bk.ev bk.E) ^ s •
              TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (M.tr bk.ι (e k)))) := by
            rw [hcj, smul_smul, smul_smul, mul_comm]
        _ = inclW l (bk.ev bk.E) ^ S.a • j m := congrArg _ hj
        _ = ((inclW l).comp (ainfId K).toRingHom) ((BK.hf bk.ι bk.E) ^ S.a) • j m := congrArg (· • j m) e1.symm
        _ = ((inclW l).comp (ainfId K).toRingHom) ((t : (ainfObj K).A) ^ s) •
              j (∑ i, (S.A.map (BK.hf bk.ι)).mulVec (Pi.single k 1) i • M.tr bk.ι (e i)) := hr7
        _ = inclW l (bk.ev bk.E) ^ s • ∑ i, bk.evW (S.A i k) • c i := by rw [e2, hsum2]
    have hev : ∀ x, bk.evW x = inclW l (bk.ev x) := fun _ => rfl
    refine Matrix.ext fun i k => ?_
    have h := congrArg (fun y => (b.baseChange (WCb l)).repr y i) (key k)
    simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      repr_map_baseChange, LinearMap.toMatrix_id, Matrix.one_apply, smul_eq_mul, apply_ite (algebraMap ℤ_[l] (WCb l)),
      map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      AlgHom.toLinearMap_apply] at h
    simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.mul_apply, smul_eq_mul, hev, U,
      Module.Basis.toMatrix_apply]
    rw [h]
    exact Finset.sum_congr rfl fun x _ => by rw [hev, mul_comm]
  · intro g
    have keyg : ∀ k, TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ g) (c k) =
        ∑ i, inclW l (S.ε bk.ι ((ainfHom K g).comp bk.ι) i k) • c i := by
      intro k
      rw [hcj, ← H.j_act_of g (ainfHom K g) (fun _ => rfl), ← M.tr_comp, hF.tr bk.ι ((ainfHom K g).comp bk.ι) k,
        map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, ← hcj]
      rfl
    refine Matrix.ext fun i k => ?_
    have h := congrArg (fun y => (b.baseChange (WCb l)).repr y i) (keyg k)
    simp only [map_smul, map_sum, Finsupp.smul_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      repr_map_baseChange, smul_eq_mul, AlgEquiv.toLinearMap_apply] at h
    simp only [Matrix.mul_apply, Matrix.map_apply, U, Module.Basis.toMatrix_apply, zW]
    rw [h]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  · rw [← hcj, hck]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Module.Basis.baseChange_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end GlobalTheory.BSP
