import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramAtPosDef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeCharMulInv
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.CondStd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.VacNonzeroReal

variable {D : D7}

/- English proof (translation)
Use `haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩`. Use `haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _`. Establish `h1 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x` using `continuous_const.prodMk continuous_id`. Establish `h2 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D)` using `h1.smul (continuous_const : Continuous fun _ : Af D.host.F => ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D))`. Use `h2.congr fun x => ?_` and prove the remaining obligations.

Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.
-/
theorem continuous_finTmul (e : D.host.E) :
    Continuous fun x : Af D.host.F => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D) := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x :=
    continuous_const.prodMk continuous_id
  have h2 : Continuous fun x : Af D.host.F => pairA D.host.F 0 x • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) :=
    h1.smul (continuous_const : Continuous fun _ : Af D.host.F => ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D))
  refine h2.congr fun x => ?_
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/- English proof (translation)
Use `show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Use `show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0`. Rewrite using `[TensorProduct.zero_tmul]`.
-/
theorem infPart_finTmul (x : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0 := by
  show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F 0 x ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
  rw [TensorProduct.zero_tmul]

/- English proof (translation)
Use `show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0`. Rewrite using `[Algebra.TensorProduct.map_tmul]`. Use `show (0 : Af D.host.F) ⊗ₜ[D.host.F] _ = 0`. Rewrite using `[TensorProduct.zero_tmul]`.
-/
theorem finPart_infTmul (x : Ainf D.host.F) (e : D.host.E) :
    finPart D (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0 := by
  show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) (pairA D.host.F x 0 ⊗ₜ[D.host.F] e) = 0
  rw [Algebra.TensorProduct.map_tmul]
  show (0 : Af D.host.F) ⊗ₜ[D.host.F] _ = 0
  rw [TensorProduct.zero_tmul]

set_option synthInstance.maxHeartbeats 160000 in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, V.zero_mem, map_zero _, 0, map_zero _, by rw [map_zero, add_zero, add_zero]⟩`. Consider the case `tmul a e => set W : Set (Af D.host.F) := (fun x => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D)) ⁻¹' V with hW`. Establish `hWo : IsOpen W` using `hV.preimage (continuous_finTmul e)`. Establish `hO : IsOpen {x : Af D.host.F | a.2 - x ∈ W}` using `hWo.preimage (continuous_const.sub continuous_id)`.

Take `⟨c, hc⟩` from `Formalism.L2.SG.Pf.CondStd.dense_F.exists_mem_open hO ⟨a.2, by show (pairA D.host.F 0 (a.2 - a.2) ⊗ₜ[D.host.F] e : AE D) ∈ V`. Rewrite using `[sub_self]`. Establish `: pairA D.host.F 0 (0 : Af D.host.F) = 0` using `rfl`. Rewrite using `[this, TensorProduct.zero_tmul]`. Conclude with `V.zero_mem⟩`.

Use `⟨algebraMap D.host.F D.host.E c * e, _, hc, infPart_finTmul _ _, _, finPart_infTmul (a.1 - algebraMap D.host.F (Ainf D.host.F) c) e, ?_⟩` and prove the remaining obligations. Establish `hinc : incA D (algebraMap D.host.F D.host.E c * e) = algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e` using `by show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) = _`. Establish `h1 : (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] algebraMap D.host.F D.host.E c) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Establish `h2 : algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e = (algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e)`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`. Rewrite using `[h1, h2, ← Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply']`. Rewrite using `[hinc, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]`. Use `congr 1`. Use `Prod.ext ?_ ?_` and prove the remaining obligations.

Use `show a.1 = algebraMap D.host.F (Ainf D.host.F) c + 0 + (a.1 - algebraMap D.host.F (Ainf D.host.F) c)`. Normalize the expressions using the abelian group laws. Use `show a.2 = algebraMap D.host.F (Af D.host.F) c + (a.2 - algebraMap D.host.F (Af D.host.F) c) + 0`. Normalize the expressions using the abelian group laws. Consider the case `add x y hx hy`.

Take `⟨e, u, hu, hu0, r, hr0, hx⟩` from `hx`. Take `⟨e', u', hu', hu0', r', hr0', hy⟩` from `hy`. Use `⟨e + e', u + u', V.add_mem hu hu', by rw [map_add, hu0, hu0', add_zero], r + r', by rw [map_add, hr0, hr0', add_zero], ?_⟩` and prove the remaining obligations. Rewrite using `[hx, hy, map_add, add_add_add_comm _ r, add_add_add_comm (incA D e) u]`.
-/
theorem decomp_AE (V : AddSubgroup (AE D)) (hV : IsOpen (V : Set (AE D))) (z : AE D) :
    ∃ e : D.host.E, ∃ u ∈ V, infPart D u = 0 ∧ ∃ r : AE D, finPart D r = 0 ∧ z = incA D e + u + r := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, V.zero_mem, map_zero _, 0, map_zero _, by rw [map_zero, add_zero, add_zero]⟩
  | tmul a e =>
    set W : Set (Af D.host.F) := (fun x => (pairA D.host.F 0 x ⊗ₜ[D.host.F] e : AE D)) ⁻¹' V with hW
    have hWo : IsOpen W := hV.preimage (continuous_finTmul e)
    have hO : IsOpen {x : Af D.host.F | a.2 - x ∈ W} := hWo.preimage (continuous_const.sub continuous_id)
    obtain ⟨c, hc⟩ := Formalism.L2.SG.Pf.CondStd.dense_F.exists_mem_open hO
      ⟨a.2, by
        show (pairA D.host.F 0 (a.2 - a.2) ⊗ₜ[D.host.F] e : AE D) ∈ V
        rw [sub_self]
        have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
        rw [this, TensorProduct.zero_tmul]
        exact V.zero_mem⟩
    refine ⟨algebraMap D.host.F D.host.E c * e, _, hc, infPart_finTmul _ _, _, finPart_infTmul (a.1 - algebraMap D.host.F (Ainf D.host.F) c) e, ?_⟩
    have hinc : incA D (algebraMap D.host.F D.host.E c * e) =
        algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e := by
      show (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) = _
      have h1 : (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E c * e) =
          ((1 : AF D.host.F) ⊗ₜ[D.host.F] algebraMap D.host.F D.host.E c) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have h2 : algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] e =
          (algebraMap D.host.F (AF D.host.F) c ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      rw [h1, h2, ← Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply']
    rw [hinc, ← TensorProduct.add_tmul, ← TensorProduct.add_tmul]
    congr 1
    refine Prod.ext ?_ ?_
    · show a.1 = algebraMap D.host.F (Ainf D.host.F) c + 0 + (a.1 - algebraMap D.host.F (Ainf D.host.F) c)
      abel
    · show a.2 = algebraMap D.host.F (Af D.host.F) c + (a.2 - algebraMap D.host.F (Af D.host.F) c) + 0
      abel
  | add x y hx hy =>
    obtain ⟨e, u, hu, hu0, r, hr0, hx⟩ := hx
    obtain ⟨e', u', hu', hu0', r', hr0', hy⟩ := hy
    refine ⟨e + e', u + u', V.add_mem hu hu', by rw [map_add, hu0, hu0', add_zero], r + r',
      by rw [map_add, hr0, hr0', add_zero], ?_⟩
    rw [hx, hy, map_add, add_add_add_comm _ r, add_add_add_comm (incA D e) u]

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Distinguish the cases in `h : i = a ∧ j = b`. Take `⟨rfl, rfl⟩` from `h`. Simplify using `only [Matrix.single_apply, and_self, if_true]`. Conclude with `continuous_id`.

Establish `: ∀ v : AE D, (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) a b = 0` using `fun v => by`. Rewrite using `[Matrix.single_apply, if_neg h]`. Simplify `continuous_const` using `only [this]`.
-/
theorem continuous_single {m n : ℕ} (i : Fin m) (j : Fin n) :
    Continuous fun v : AE D => (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Matrix.single_apply, and_self, if_true]
    exact continuous_id
  · have : ∀ v : AE D, (Matrix.single i j v : Matrix (Fin m) (Fin n) (AE D)) a b = 0 := fun v => by
      rw [Matrix.single_apply, if_neg h]
    simpa only [this] using continuous_const

def singleHom {m n : ℕ} (i : Fin m) (j : Fin n) : AE D →+ Matrix (Fin m) (Fin n) (AE D) where
  toFun v := Matrix.single i j v
  map_zero' := Matrix.single_zero i j
  map_add' x y := Matrix.single_add i j x y

/- English proof (translation)
Establish `hV : ∀ i j, IsOpen ((U.comap (singleHom i j) : AddSubgroup (AE D)) : Set (AE D))` using `fun i j => hU.preimage (continuous_single i j)`. Use `choose e u hu hu0 r hr0 hw using fun i j => decomp_AE _ (hV i j) (w i j)`. Use `⟨Matrix.of e, Matrix.of u, ?_, ?_, Matrix.of r, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.matrix_eq_sum_single (Matrix.of u)]`. Conclude with `U.sum_mem fun i _ => U.sum_mem fun j _ => hu i j`.

Use extensionality with `i j`. Simplify using `[hu0 i j]`. Use extensionality with `i j`. Simplify using `[hr0 i j]`. Use extensionality with `i j`.

Rewrite using `[hw i j]`. Both sides reduce to the same expression.
-/
theorem decomp_WO {S T : HSp D} (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) (w : WO S T) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ u ∈ U, u.map (infPart D) = 0 ∧
      ∃ r : WO S T, r.map (finPart D) = 0 ∧ w = ratW T S γ + u + r := by
  classical
  have hV : ∀ i j, IsOpen ((U.comap (singleHom i j) : AddSubgroup (AE D)) : Set (AE D)) := fun i j =>
    hU.preimage (continuous_single i j)
  choose e u hu hu0 r hr0 hw using fun i j => decomp_AE _ (hV i j) (w i j)
  refine ⟨Matrix.of e, Matrix.of u, ?_, ?_, Matrix.of r, ?_, ?_⟩
  · rw [Matrix.matrix_eq_sum_single (Matrix.of u)]
    exact U.sum_mem fun i _ => U.sum_mem fun j _ => hu i j
  · ext i j
    simp [hu0 i j]
  · ext i j
    simp [hr0 i j]
  · ext i j
    rw [hw i j]
    rfl

/- English proof (translation)
Introduce `D ψ θ S T sS sT LS LT f hv`. Establish `hne` using `GlobalTheory.TwistFactorProof.vac_ne_zero hv`. Establish `hth : IsThetaFunO ψ S T f` using `hv.2.theta`. Choose the witnesses or unpack the hypotheses as in `⟨w0, hw0⟩ : ∃ w, f w ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hne (funext h)`. Take `⟨U, hUo, hU⟩` from `hth.level`. Take `⟨γ, u, huU, hu0, r, hr0, rfl⟩` from `decomp_WO U hUo w0`. Use `⟨r, hr0, fun hfr => ?_⟩` and prove the remaining obligations.

Establish `hψ : ∀ a, ψ a ≠ 0` using `fun a => by`. Establish `: ψ a * ψ (-a) = 1` using `by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`. Conclude with `left_ne_zero_of_mul_eq_one this`. Rewrite `hw0` using `[add_assoc, hth.quasi γ (u + r)]`. Establish `hfur : f (u + r) ≠ 0` using `right_ne_zero_of_mul hw0`.

Establish `h2` using `congrFun (hU u huU hu0) r`. Unfold `heisO at h2`. Rewrite `h2` using `[hfr, add_comm r u]`. Conclude with `(mul_ne_zero (hψ _) hfur) h2`.
-/
theorem exists_finPart_zero_ne : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (f : WO S T → ℂ), IsVacO ψ θ S T sS sT LS LT f → ∃ w : WO S T, w.map (finPart D) = 0 ∧ f w ≠ 0 := by
  intro D ψ θ S T sS sT LS LT f hv
  have hne := GlobalTheory.TwistFactorProof.vac_ne_zero hv
  have hth : IsThetaFunO ψ S T f := hv.2.theta
  obtain ⟨w0, hw0⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨U, hUo, hU⟩ := hth.level
  obtain ⟨γ, u, huU, hu0, r, hr0, rfl⟩ := decomp_WO U hUo w0
  refine ⟨r, hr0, fun hfr => ?_⟩
  have hψ : ∀ a, ψ a ≠ 0 := fun a => by
    have : ψ a * ψ (-a) = 1 := by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one this
  rw [add_assoc, hth.quasi γ (u + r)] at hw0
  have hfur : f (u + r) ≠ 0 := right_ne_zero_of_mul hw0
  have h2 := congrFun (hU u huU hu0) r
  unfold heisO at h2
  rw [hfr, add_comm r u] at h2
  exact (mul_ne_zero (hψ _) hfur) h2

end GlobalTheory.VacNonzeroReal
