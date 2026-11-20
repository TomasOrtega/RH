import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UAtMemIsoB
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB
open scoped TensorProduct GlobalTheory.VacAny
open Matrix

noncomputable section

namespace GlobalTheory.LocPair

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Establish `h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e)`. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, smul_eq_mul]`.
-/
theorem trace_tmul [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Rewrite using `[trace_tmul, map_mul, AlgHom.commutes]`. Express the relevant statement in the definitionally equal form `_ = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (evFin F v a ⊗ₜ[F] e)`.

Rewrite using `[trace_tmul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`.
-/
theorem evFin_trace [FiniteDimensional F E] (v : Pl F) (z : AE F E) :
    evFin F v (Algebra.trace (AF F) (AE F E) z) = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [trace_tmul, map_mul, AlgHom.commutes]
    change _ = Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (evFin F v a ⊗ₜ[F] e)
    rw [trace_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Express the relevant statement in the definitionally equal form `Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((GlobalTheory.LatVac.liftV v a) ⊗ₜ[F] e) = a ⊗ₜ[F] e`. Rewrite using `[Algebra.TensorProduct.map_tmul, GlobalTheory.LatVac.evFin_liftV, AlgHom.id_apply]`.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem compFin_liftT (v : Pl F) (t : Fv F v ⊗[F] E) : compFin F E v (GlobalTheory.VanishLoc.liftT v t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    change Algebra.TensorProduct.map (evFin F v) (AlgHom.id F E) ((GlobalTheory.LatVac.liftV v a) ⊗ₜ[F] e) = a ⊗ₜ[F] e
    rw [Algebra.TensorProduct.map_tmul, GlobalTheory.LatVac.evFin_liftV, AlgHom.id_apply]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

open GlobalTheory.LatVac in

/- English proof (translation)
Rewrite using `[co.form]`. Simplify using `[locCo, dotProduct, map_sum, map_mul, map_sub]`.
-/
theorem locCo_pair {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} {κ : Type} [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux B κ) (v : Pl F) (w w' : W) :
    (locCo co v w).1 ⬝ᵥ (locCo co v w').2 - (locCo co v w').1 ⬝ᵥ (locCo co v w).2 = evFin F v (B w w') := by
  rw [co.form]
  simp [locCo, dotProduct, map_sum, map_mul, map_sub]

/- English proof (translation)
Simplify using `[cA, inclR]`.
-/
theorem cA_inclR (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e => simp [cA, hσ]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem cA_cA {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) (z : AE F E) : cA σ (cA σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Simplify using `only [GlobalTheory.WeilM.hTens, GlobalTheory.VanishLoc.uAt, shiftB, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, incV, incM, Matrix.map_apply, smul_eq_mul, map_mul, cA_inclR, cA_cA hσ, form, dotProduct, Matrix.mulVec, map_sum, Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Use `(Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_` and prove the remaining obligations. Use `Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hTens_eq {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n n₁ d d₁ : ℕ} (JA : Matrix (Fin n) (Fin n) E)
    (JB : Matrix (Fin d) (Fin d) E) (H : Plane E n n₁) (H' : Plane E d d₁) (v : Pl F) (t : Fv F v ⊗[F] E)
    (l : (AE F E)ˣ) :
    GlobalTheory.WeilM.hTens (cA σ) (incM F JA) (incM F JB) (GlobalTheory.VanishLoc.uAt H H' v t) (shiftB σ H H' l) =
      GlobalTheory.VanishLoc.liftT v t * l.1 * inclR (F := F) (AF F) (form σ JA H.x H.y) *
        inclR (F := F) (AF F) (form σ JB H'.y H'.x) := by
  simp only [GlobalTheory.WeilM.hTens, GlobalTheory.VanishLoc.uAt, shiftB, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply,
    incV, incM, Matrix.map_apply, smul_eq_mul, map_mul, cA_inclR, cA_cA hσ, form, dotProduct, Matrix.mulVec,
    map_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun j _ => ?_)
  refine (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans ?_
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun k _ => ?_)
  ring

/- English proof (translation)
Simplify using `only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[hJ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem form_swap_skew {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' hT v t l`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hT.base.cm.2.2.1]; norm_num)`. Establish `hσ` using `cm_conj_conj hT.base.cm`. Establish `hxy : form σ G.V'.J H.x H.y = 1` using `hC.hH.xy`. Establish `hyx : form σ G.W.J H'.y H'.x = -1`.

Rewrite using `[form_swap_skew hσ _ hT.geo.hW.skew, hC.hH'.xy, map_one]`. Rewrite using `[locCo_pair, GlobalTheory.WeilM.symp, hTens_eq hσ, evFin_trace, hxy, hyx, map_one, map_neg, map_one]`. Establish `e : (-1 : AE F E) * (GlobalTheory.VanishLoc.liftT v t * l.1 * 1 * -1) = GlobalTheory.VanishLoc.liftT v t * l.1` using `by ring`. Rewrite using `[e, map_mul, compFin_liftT]`.
-/
theorem pair_trace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (t : Fv F v ⊗[F] E) (l : (AE F E)ˣ),
      (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.VanishLoc.uAt H H' v t)).1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v (shiftB σ H H' l)).2 -
        (GlobalTheory.LatVac.locCo G.M'.co v (shiftB σ H H' l)).1 ⬝ᵥ (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.VanishLoc.uAt H H' v t)).2 =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (t * compFin F E v l.1) := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' hT v t l
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hT.base.cm.2.2.1]; norm_num)
  have hσ := cm_conj_conj hT.base.cm
  have hxy : form σ G.V'.J H.x H.y = 1 := hC.hH.xy
  have hyx : form σ G.W.J H'.y H'.x = -1 := by
    rw [form_swap_skew hσ _ hT.geo.hW.skew, hC.hH'.xy, map_one]
  rw [locCo_pair, GlobalTheory.WeilM.symp, hTens_eq hσ, evFin_trace, hxy, hyx, map_one, map_neg, map_one]
  have e : (-1 : AE F E) * (GlobalTheory.VanishLoc.liftT v t * l.1 * 1 * -1) = GlobalTheory.VanishLoc.liftT v t * l.1 := by ring
  rw [e, map_mul, compFin_liftT]

end GlobalTheory.LocPair
