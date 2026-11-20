import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LeviFixesAnisotropic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LeviInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uGrpHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocIdxLift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds

noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct
open Matrix

section Lift

variable (I : Formalism.MainNotions.S.AutInst)

def liftS (p : HeightOneSpectrum (𝓞 I.F)) (c : Fv I.F p ⊗[I.F] I.E) : I.E ⊗[I.F] Af I.F :=
  (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (PI.MassDataKppVolLemmas.thetaP I p c)

/- English proof (translation)
Unfold `liftS PI.FinKW.psiV`. Rewrite using `[AlgHom.comp_apply]`. Use `erw [AlgEquiv.apply_symm_apply]`. Both sides reduce to the same expression.
-/
theorem psiV_liftS (p v : HeightOneSpectrum (𝓞 I.F)) (c : Fv I.F p ⊗[I.F] I.E) :
    PI.FinKW.psiV I v (liftS I p c) = PI.MassDataKppVolLemmas.tV I v (PI.MassDataKppVolLemmas.thetaP I p c) := by
  unfold liftS PI.FinKW.psiV
  rw [AlgHom.comp_apply]
  erw [AlgEquiv.apply_symm_apply]
  rfl

/- English proof (translation)
Rewrite using `[psiV_liftS]`. Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Simplify using `only [PI.MassDataKppVolLemmas.thetaP, TensorProduct.map_tmul, LinearMap.id_apply, PI.MassDataKppVolLemmas.tV]`.

Simplify using `[PI.MassDataKppVolLemmas.sL, tensMap]`. Rewrite using `[show evalV I.F p (singleV I.F p a) = a from PI.MassDataKppVolLemmas.Comp_single_same I p a]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`.
-/
theorem psiV_liftS_same (p : HeightOneSpectrum (𝓞 I.F)) (c : Fv I.F p ⊗[I.F] I.E) :
    PI.FinKW.psiV I p (liftS I p c) = c := by
  rw [psiV_liftS]
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [PI.MassDataKppVolLemmas.thetaP, TensorProduct.map_tmul, LinearMap.id_apply, PI.MassDataKppVolLemmas.tV]
    simp [PI.MassDataKppVolLemmas.sL, tensMap]
    rw [show evalV I.F p (singleV I.F p a) = a from PI.MassDataKppVolLemmas.Comp_single_same I p a]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/- English proof (translation)
Rewrite using `[psiV_liftS]`. Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a e`. Simplify using `[PI.MassDataKppVolLemmas.thetaP, PI.MassDataKppVolLemmas.tV, PI.MassDataKppVolLemmas.sL, tensMap]`.

Rewrite using `[show evalV I.F v (singleV I.F p a) = 0 from PI.MassDataKppVolLemmas.Comp_single_ne I p v h a, TensorProduct.zero_tmul]`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]`.
-/
theorem psiV_liftS_ne (p v : HeightOneSpectrum (𝓞 I.F)) (h : v ≠ p) (c : Fv I.F p ⊗[I.F] I.E) :
    PI.FinKW.psiV I v (liftS I p c) = 0 := by
  rw [psiV_liftS]
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [PI.MassDataKppVolLemmas.thetaP, PI.MassDataKppVolLemmas.tV, PI.MassDataKppVolLemmas.sL, tensMap]
    rw [show evalV I.F v (singleV I.F p a) = 0 from PI.MassDataKppVolLemmas.Comp_single_ne I p v h a,
      TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[PI.FinKW.vecV, incl, ratV, PI.FinKW.psiV, Formalism.UG.inclE, inclR]`.
-/
theorem vecV_incl (v : HeightOneSpectrum (𝓞 I.F)) (x : Fin I.n → I.E) :
    PI.FinKW.vecV I v (incl I x) = ratV (F := I.F) (Fv I.F v) x := by
  funext i
  simp [PI.FinKW.vecV, incl, ratV, PI.FinKW.psiV, Formalism.UG.inclE, inclR]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `map_add (PI.FinKW.psiV I v) (x i) (y i)`.
-/
theorem vecV_add (v : HeightOneSpectrum (𝓞 I.F)) (x y : VA I) :
    PI.FinKW.vecV I v (x + y) = PI.FinKW.vecV I v x + PI.FinKW.vecV I v y := by
  funext i
  exact map_add (PI.FinKW.psiV I v) (x i) (y i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `map_mul (PI.FinKW.psiV I v) c (x i)`.
-/
theorem vecV_smul (v : HeightOneSpectrum (𝓞 I.F)) (c : I.E ⊗[I.F] Af I.F) (x : VA I) :
    PI.FinKW.vecV I v (c • x) = PI.FinKW.psiV I v c • PI.FinKW.vecV I v x := by
  funext i
  exact map_mul (PI.FinKW.psiV I v) c (x i)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `map_zero (PI.FinKW.psiV I v)`.
-/
theorem vecV_zero (v : HeightOneSpectrum (𝓞 I.F)) : PI.FinKW.vecV I v (0 : VA I) = 0 := by
  funext i
  exact map_zero (PI.FinKW.psiV I v)

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, rfl⟩` from `hx`. Use `⟨liftS I p 1 • incl I (Y a), Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[vecV_smul, psiV_liftS_same, one_smul, vecV_incl]`.

Introduce `v hv`. Rewrite using `[vecV_smul, psiV_liftS_ne I p v hv, zero_smul]`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, vecV_zero I p, fun v _ => vecV_zero I v⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨U, hU, h1, h2⟩` from `hx`.

Take `⟨U', hU', h1', h2'⟩` from `hy`. Use `⟨U + U', Submodule.add_mem _ hU hU', ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[vecV_add, h1, h1']`. Rewrite using `[vecV_add, h2 v hv, h2' v hv, add_zero]`. Consider the case `smul c x _ hx`.

Take `⟨U, hU, h1, h2⟩` from `hx`. Use `⟨liftS I p c • U, Submodule.smul_mem _ _ hU, ?_, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[vecV_smul, psiV_liftS_same, h1]`. Rewrite using `[vecV_smul, h2 v hv, smul_zero]`.
-/
theorem span_lift (p : HeightOneSpectrum (𝓞 I.F)) {m : ℕ} (Y : Fin m → Fin I.n → I.E) (s : Set (Fin m))
    (u : Fin I.n → Fv I.F p ⊗[I.F] I.E) (hu : u ∈ spanR (F := I.F) (Fv I.F p) Y s) :
    ∃ U : VA I, U ∈ Submodule.span (I.E ⊗[I.F] Af I.F) ((fun a => incl I (Y a)) '' s) ∧
      PI.FinKW.vecV I p U = u ∧ ∀ v, v ≠ p → PI.FinKW.vecV I v U = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨liftS I p 1 • incl I (Y a), Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩), ?_, ?_⟩
    · rw [vecV_smul, psiV_liftS_same, one_smul, vecV_incl]
    · intro v hv
      rw [vecV_smul, psiV_liftS_ne I p v hv, zero_smul]
  | zero => exact ⟨0, Submodule.zero_mem _, vecV_zero I p, fun v _ => vecV_zero I v⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h1, h2⟩ := hx
    obtain ⟨U', hU', h1', h2'⟩ := hy
    refine ⟨U + U', Submodule.add_mem _ hU hU', ?_, fun v hv => ?_⟩
    · rw [vecV_add, h1, h1']
    · rw [vecV_add, h2 v hv, h2' v hv, add_zero]
  | smul c x _ hx =>
    obtain ⟨U, hU, h1, h2⟩ := hx
    refine ⟨liftS I p c • U, Submodule.smul_mem _ _ hU, ?_, fun v hv => ?_⟩
    · rw [vecV_smul, psiV_liftS_same, h1]
    · rw [vecV_smul, h2 v hv, smul_zero]

/- English proof (translation)
Take `⟨U, hU, h1, h2⟩` from `span_lift I p Y s _ h`. Establish `e : M *ᵥ w = U`. Use function extensionality and compare the values at `i`. Rewrite using `[← sub_eq_zero]`. Apply `PI.FinKW.local_vector_injective I` to reduce the goal to its premises.

Introduce `v`. Rewrite using `[map_sub]`. Establish `e1 : PI.FinKW.psiV I v ((M *ᵥ w) i) = ((M.map (PI.FinKW.psiV I v)) *ᵥ PI.FinKW.vecV I v w) i` using `congrFun (PI.MassDataKppVolLemmas.LocIdxLift_vecV_mulVec I v M w) i`. Establish `e2 : PI.FinKW.psiV I v (U i) = PI.FinKW.vecV I v U i` using `rfl`. Rewrite using `[e1, e2]`.

Distinguish the cases in `hv : v = p`. Substitute `hv` using the available equality. Rewrite using `[h1, sub_self]`. Rewrite using `[hM v hv, h2 v hv, Matrix.zero_mulVec]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `hU`.
-/
theorem mulVec_mem_span (p : HeightOneSpectrum (𝓞 I.F)) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hM : ∀ v, v ≠ p → M.map (PI.FinKW.psiV I v) = 0) {m : ℕ} (Y : Fin m → Fin I.n → I.E) (s : Set (Fin m))
    (w : VA I)
    (h : (M.map (PI.FinKW.psiV I p)) *ᵥ PI.FinKW.vecV I p w ∈ spanR (F := I.F) (Fv I.F p) Y s) :
    M *ᵥ w ∈ Submodule.span (I.E ⊗[I.F] Af I.F) ((fun a => incl I (Y a)) '' s) := by
  obtain ⟨U, hU, h1, h2⟩ := span_lift I p Y s _ h
  have e : M *ᵥ w = U := by
    funext i
    rw [← sub_eq_zero]
    apply PI.FinKW.local_vector_injective I
    intro v
    rw [map_sub]
    have e1 : PI.FinKW.psiV I v ((M *ᵥ w) i) = ((M.map (PI.FinKW.psiV I v)) *ᵥ PI.FinKW.vecV I v w) i :=
      congrFun (PI.MassDataKppVolLemmas.LocIdxLift_vecV_mulVec I v M w) i
    have e2 : PI.FinKW.psiV I v (U i) = PI.FinKW.vecV I v U i := rfl
    rw [e1, e2]
    by_cases hv : v = p
    · subst hv
      rw [h1, sub_self]
    · rw [hM v hv, h2 v hv, Matrix.zero_mulVec]
      simp
  rw [e]
  exact hU

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => simp [PI.FinKW.psiV, Formalism.UG.sigR, sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem psiV_sigR (v : HeightOneSpectrum (𝓞 I.F)) (t : I.E ⊗[I.F] Af I.F) :
    PI.FinKW.psiV I v (Formalism.UG.sigR I.cm.sig (Af I.F) t) = sigR (Fv I.F v) I.cm.sig (PI.FinKW.psiV I v t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [PI.FinKW.psiV, Formalism.UG.sigR, sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Simplify using `[PI.FinKW.psiV, Formalism.UG.inclE, inclR]`.
-/
theorem psiV_inclE (v : HeightOneSpectrum (𝓞 I.F)) (a : I.E) :
    PI.FinKW.psiV I v (Formalism.UG.inclE (F := I.F) (Af I.F) a) = inclR (Fv I.F v) a := by
  simp [PI.FinKW.psiV, Formalism.UG.inclE, inclR]

/- English proof (translation)
Simplify using `[hA, hR, Formalism.UG.hform, JR, PI.FinKW.vecV, map_sum, map_mul, psiV_sigR, psiV_inclE, dotProduct, mulVec, Matrix.map_apply]`.
-/
theorem psiV_hA (v : HeightOneSpectrum (𝓞 I.F)) (x y : VA I) :
    PI.FinKW.psiV I v (hA I x y) =
      hR (Fv I.F v) I.cm.sig I.J (PI.FinKW.vecV I v x) (PI.FinKW.vecV I v y) := by
  simp [hA, hR, Formalism.UG.hform, JR, PI.FinKW.vecV, map_sum, map_mul, psiV_sigR, psiV_inclE, dotProduct,
    mulVec, Matrix.map_apply]

end Lift

/- English proof (translation)
Introduce `D X hb hK hT hL w p n hn hnK`. Take `⟨hn1, hn2⟩` from `hn`. Take `⟨y, hy⟩` from `PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb (PI.MassDataKppVolLemmas.liftHA X.B.I p.1 n)`. Establish `hcomp : ∀ v, v ≠ p.1 → PI.MassDataKppVolLemmas.piV X.B.I v (PI.MassDataKppVolLemmas.tf X.B.I hb y) = 1` using `fun v h => by rw [hy, PI.MassDataKppVolLemmas.LocIdxLift_piV_ne X.B.I p.1 v h]`. Establish `hsame : PI.MassDataKppVolLemmas.piV X.B.I p.1 (PI.MassDataKppVolLemmas.tf X.B.I hb y) = n`.

Rewrite using `[hy, PI.MassDataKppVolLemmas.LocIdxLift_piV_same]`. Establish `hyK : y ∈ X.B.I.Kset`. Rewrite using `[← PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb, Kf, Subgroup.mem_iInf]`. Introduce `v`. Use `show HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.piV X.B.I v (PI.MassDataKppVolLemmas.tf X.B.I hb y)) ∈ Kloc v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))`.

Distinguish the cases in `h : v = p.1`. Substitute `h` using the available equality. Rewrite using `[hsame]`. Conclude with `hnK`. Rewrite using `[hcomp v h]`.

Conclude with `(Kloc v _).one_mem`. Establish `hmat : ∀ v, (X.B.I.fmat y - 1).map (PI.FinKW.psiV X.B.I v) = ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (PI.MassDataKppVolLemmas.piV X.B.I v (PI.MassDataKppVolLemmas.tf X.B.I hb y)) : GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) - 1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ( …`. Introduce `v`. Rewrite using `[Matrix.map_sub _ (map_sub _), PI.MassDataKppVolLemmas.LocIdxLift_psiV_fmat X.B.I hb, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hM0 : ∀ v, v ≠ p.1 → (X.B.I.fmat y - 1).map (PI.FinKW.psiV X.B.I v) = 0`.

Introduce `v hv`. Rewrite using `[hmat v, hcomp v hv]`. Conclude with `sub_self _`. Establish `hMp : ∀ x : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E, ((X.B.I.fmat y - 1).map (PI.FinKW.psiV X.B.I p.1)) *ᵥ x = lin (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J n x - x`. Introduce `x`.

Rewrite using `[hmat p.1, hsame, Matrix.sub_mulVec, Matrix.one_mulVec]`. Both sides reduce to the same expression. Establish `hstd` using `FrameW.frameOf_isStd X w`. Establish `hyN : y ∈ X.NfinU w`. Use `⟨fun a => ?_, ?_, fun y' hy' => ?_⟩` and prove the remaining obligations.

Use `mulVec_mem_span X.B.I p.1 _ hM0 X.eR _ _ ?_` and prove the remaining obligations. Rewrite using `[hMp, vecV_incl]`. Conclude with `hn1 a`. Rewrite using `[← Set.image_univ]`. Use `mulVec_mem_span X.B.I p.1 _ hM0 X.eR _ _ ?_` and prove the remaining obligations.

Rewrite using `[hMp, vecV_incl]`. Use `hn2 _ (fun a => ?_)` and prove the remaining obligations. Rewrite using `[hermForm_rational_vectors]`. Establish `h0 : hE X.B.I.cm.sig X.B.I.J ((frameOf X w).e a) (X.zR w) = 0` using `hstd.2.2.2.1 a`. Rewrite using `[h0, map_zero]`.

Rewrite using `[← Set.image_univ]`. Use `mulVec_mem_span X.B.I p.1 _ hM0 X.eR _ _ ?_` and prove the remaining obligations. Rewrite using `[hMp]`. Use `hn2 _ (fun a => ?_)` and prove the remaining obligations. Use `show hR (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (X.eR a)) (PI.FinKW.vecV X.B.I p.1 y') = 0`.

Rewrite using `[← vecV_incl, ← psiV_hA, hy' a, map_zero]`. Establish `hN` using `MassDataMassesW.NLev.nLevel_holds X w y hyN hyK`. Use `⟨finHA X hb y, ⟨finHA X hb ((X.xu w)⁻¹ * y * X.xu w), ⟨_, hN, rfl⟩, ?_⟩, hsame⟩` and prove the remaining obligations. Use `show finHA X hb (X.xu w) * finHA X hb ((X.xu w)⁻¹ * y * X.xu w) * (finHA X hb (X.xu w))⁻¹ = finHA X hb y`. Rewrite using `[finHA_mul, finHA_mul, finHA_inv]`.

Use `group`.
-/
theorem unipotent_integral_in_level : UnipotentIntegralInLevel := by
  intro D X hb hK hT hL w p n hn hnK
  obtain ⟨hn1, hn2⟩ := hn
  obtain ⟨y, hy⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb
    (PI.MassDataKppVolLemmas.liftHA X.B.I p.1 n)
  have hcomp : ∀ v, v ≠ p.1 → PI.MassDataKppVolLemmas.piV X.B.I v (PI.MassDataKppVolLemmas.tf X.B.I hb y) = 1 :=
    fun v h => by rw [hy, PI.MassDataKppVolLemmas.LocIdxLift_piV_ne X.B.I p.1 v h]
  have hsame : PI.MassDataKppVolLemmas.piV X.B.I p.1 (PI.MassDataKppVolLemmas.tf X.B.I hb y) = n := by
    rw [hy, PI.MassDataKppVolLemmas.LocIdxLift_piV_same]

  have hyK : y ∈ X.B.I.Kset := by
    rw [← PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb, Kf, Subgroup.mem_iInf]
    intro v
    show HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
      (PI.MassDataKppVolLemmas.piV X.B.I v (PI.MassDataKppVolLemmas.tf X.B.I hb y)) ∈
        Kloc v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    by_cases h : v = p.1
    · subst h; rw [hsame]; exact hnK
    · rw [hcomp v h]; exact (Kloc v _).one_mem

  have hmat : ∀ v, (X.B.I.fmat y - 1).map (PI.FinKW.psiV X.B.I v) =
      ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
        (PI.MassDataKppVolLemmas.piV X.B.I v (PI.MassDataKppVolLemmas.tf X.B.I hb y)) :
          GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) -
        1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) := by
    intro v
    rw [Matrix.map_sub _ (map_sub _), PI.MassDataKppVolLemmas.LocIdxLift_psiV_fmat X.B.I hb,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hM0 : ∀ v, v ≠ p.1 → (X.B.I.fmat y - 1).map (PI.FinKW.psiV X.B.I v) = 0 := by
    intro v hv
    rw [hmat v, hcomp v hv]
    exact sub_self _
  have hMp : ∀ x : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E,
      ((X.B.I.fmat y - 1).map (PI.FinKW.psiV X.B.I p.1)) *ᵥ x = lin (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J n x - x := by
    intro x
    rw [hmat p.1, hsame, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  have hstd := FrameW.frameOf_isStd X w

  have hyN : y ∈ X.NfinU w := by
    refine ⟨fun a => ?_, ?_, fun y' hy' => ?_⟩
    · refine mulVec_mem_span X.B.I p.1 _ hM0 X.eR _ _ ?_
      rw [hMp, vecV_incl]
      exact hn1 a
    · rw [← Set.image_univ]
      refine mulVec_mem_span X.B.I p.1 _ hM0 X.eR _ _ ?_
      rw [hMp, vecV_incl]
      refine hn2 _ (fun a => ?_)
      rw [hermForm_rational_vectors]
      have h0 : hE X.B.I.cm.sig X.B.I.J ((frameOf X w).e a) (X.zR w) = 0 := hstd.2.2.2.1 a
      rw [h0, map_zero]
    · rw [← Set.image_univ]
      refine mulVec_mem_span X.B.I p.1 _ hM0 X.eR _ _ ?_
      rw [hMp]
      refine hn2 _ (fun a => ?_)
      show hR (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (X.eR a))
        (PI.FinKW.vecV X.B.I p.1 y') = 0
      rw [← vecV_incl, ← psiV_hA, hy' a, map_zero]
  have hN := MassDataMassesW.NLev.nLevel_holds X w y hyN hyK
  refine ⟨finHA X hb y, ⟨finHA X hb ((X.xu w)⁻¹ * y * X.xu w), ⟨_, hN, rfl⟩, ?_⟩, hsame⟩
  show finHA X hb (X.xu w) * finHA X hb ((X.xu w)⁻¹ * y * X.xu w) * (finHA X hb (X.xu w))⁻¹ = finHA X hb y
  rw [finHA_mul, finHA_mul, finHA_inv]
  group

/- English proof (translation)
The claim follows from `locLevi_of_NO unipotent_integral_in_level`.
-/
theorem locLevi_holds : LocLevi := locLevi_of_NO unipotent_integral_in_level

end MassDataLevelSSteps
