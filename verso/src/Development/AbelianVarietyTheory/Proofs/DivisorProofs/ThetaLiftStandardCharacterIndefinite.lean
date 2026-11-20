import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.WeilContF

open Formalism.IndefR.DatumF

/- English proof (translation)
Establish `: (InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K → mixedEmbedding.mixedSpace K) = fun x => ((fun v : {w : InfinitePlace K // InfinitePlace.IsReal w} => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)), (fun v : {w : InfinitePlace K // InfinitePlace. …`. Use function extensionality and compare the values at `x`. Conclude with `InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x`. Rewrite using `[this]`. Use `Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)` and prove the remaining obligations.

Conclude with `(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _)`. Conclude with `(InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)`.
-/
theorem continuous_mixed (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K) := by
  have : (InfiniteAdeleRing.ringEquiv_mixedSpace K : InfiniteAdeleRing K → mixedEmbedding.mixedSpace K) =
      fun x => ((fun v : {w : InfinitePlace K // InfinitePlace.IsReal w} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace K // InfinitePlace.IsComplex w} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
  rw [this]
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

/- English proof (translation)
Use `continuous_pi fun v => ?_` and prove the remaining obligations. Break down `v.isReal_or_isComplex with hv | hv` into its components or cases. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]`. Conclude with `((continuous_apply _).comp continuous_fst).congr fun y => (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩).symm`. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]`.

Conclude with `((continuous_apply _).comp continuous_snd).congr fun y => (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩).symm`.
-/
theorem continuous_mixed_symm (K : Type) [Field K] [NumberField K] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace K).apply_symm_apply y)) ⟨v, hv⟩).symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem modTop : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩

/- English proof (translation)
The claim follows from `Module.Finite.of_restrictScalars_finite ℚ F E`.
-/
theorem finiteFE : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E

/- English proof (translation)
Use `haveI := finiteFE (F := F) (E := E)`. Use `haveI := modTop (F := F) (E := E)`. Conclude with `IsModuleTopology.isTopologicalRing (AF F) (AEF F E)`.
-/
theorem topRing : IsTopologicalRing (AEF F E) := by
  haveI := finiteFE (F := F) (E := E)
  haveI := modTop (F := F) (E := E)
  exact IsModuleTopology.isTopologicalRing (AF F) (AEF F E)

def sigLin (σ : E →ₐ[F] E) : AEF F E →ₗ[AF F] AEF F E :=
  TensorProduct.AlgebraTensorModule.map (LinearMap.id : AF F →ₗ[AF F] AF F) σ.toLinearMap

/- English proof (translation)
Use `haveI := finiteFE (F := F) (E := E)`. Use `haveI := modTop (F := F) (E := E)`. Use `haveI := topRing (F := F) (E := E)`. Establish `h` using `IsModuleTopology.continuous_of_linearMap (sigLin σ)`. Establish `e : (sigLin σ : AEF F E → AEF F E) = cAF σ`.

Use function extensionality and compare the values at `x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b => show (TensorProduct.AlgebraTensorModule.map (LinearMap.id : AF F →ₗ[AF F] AF F) σ.toLinearMap) (a ⊗ₜ[F] b) = Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ (a ⊗ₜ[F] b)`. Rewrite using `[TensorProduct.AlgebraTensorModule.map_tmul, Algebra.TensorProduct.map_tmul]`.

Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem continuous_cAF (σ : E →ₐ[F] E) : Continuous (cAF σ) := by
  haveI := finiteFE (F := F) (E := E)
  haveI := modTop (F := F) (E := E)
  haveI := topRing (F := F) (E := E)
  have h := IsModuleTopology.continuous_of_linearMap (sigLin σ)
  have e : (sigLin σ : AEF F E → AEF F E) = cAF σ := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      show (TensorProduct.AlgebraTensorModule.map (LinearMap.id : AF F →ₗ[AF F] AF F) σ.toLinearMap)
        (a ⊗ₜ[F] b) = Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ (a ⊗ₜ[F] b)
      rw [TensorProduct.AlgebraTensorModule.map_tmul, Algebra.TensorProduct.map_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [e] at h
  exact h

/- English proof (translation)
Use `haveI := finiteFE (F := F) (E := E)`. Use `haveI := modTop (F := F) (E := E)`. Use `haveI := topRing (F := F) (E := E)`. Establish `hy' : ∀ i j, Continuous fun t => cAF σ (y t i j)` using `fun i j => (continuous_cAF σ).comp ((continuous_apply j).comp ((continuous_apply i).comp hy))`. Establish `hx' : ∀ i j, Continuous fun t => x t i j` using `fun i j => (continuous_apply j).comp ((continuous_apply i).comp hx)`.

Establish `hh : Continuous fun t => hOF σ JS JT (x t) (y t)` using `continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)`. Establish `ht : Continuous (Algebra.trace (AF F) (AEF F E))` using `IsModuleTopology.continuous_of_linearMap _`. Conclude with `continuous_const.mul (ht.comp (continuous_const.mul hh))`.
-/
theorem continuous_symplOHF (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ : E) {X : Type} [TopologicalSpace X] {x y : X → WOF F E nS nT}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun t => symplOHF σ JS JT ξ (x t) (y t) := by
  haveI := finiteFE (F := F) (E := E)
  haveI := modTop (F := F) (E := E)
  haveI := topRing (F := F) (E := E)
  have hy' : ∀ i j, Continuous fun t => cAF σ (y t i j) := fun i j =>
    (continuous_cAF σ).comp ((continuous_apply j).comp ((continuous_apply i).comp hy))
  have hx' : ∀ i j, Continuous fun t => x t i j := fun i j =>
    (continuous_apply j).comp ((continuous_apply i).comp hx)
  have hh : Continuous fun t => hOF σ JS JT (x t) (y t) :=
    continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ => continuous_finset_sum _ fun _ _ =>
      continuous_finset_sum _ fun _ _ => ((continuous_const.mul (hy' _ _)).mul continuous_const).mul (hx' _ _)
  have ht : Continuous (Algebra.trace (AF F) (AEF F E)) := IsModuleTopology.continuous_of_linearMap _
  exact continuous_const.mul (ht.comp (continuous_const.mul hh))

def eInf (F : Type) [Field F] [NumberField F] : AF F := pairA F 1 0

/- English proof (translation)
Rewrite using `[Algebra.smul_def, map_mul]`. Establish `: finPartF F E (algebraMap (AF F) (AEF F E) (eInf F)) = 0` using `by show (sndA F (eInf F)) ⊗ₜ[F] (1 : E) = 0`. Establish `: sndA F (eInf F) = 0` using `rfl`. Rewrite using `[this, TensorProduct.zero_tmul]`. Rewrite using `[this, zero_mul]`.
-/
theorem finPartF_eInf_smul (z : AEF F E) : finPartF F E (eInf F • z) = 0 := by
  rw [Algebra.smul_def, map_mul]
  have : finPartF F E (algebraMap (AF F) (AEF F E) (eInf F)) = 0 := by
    show (sndA F (eInf F)) ⊗ₜ[F] (1 : E) = 0
    have : sndA F (eInf F) = 0 := rfl
    rw [this, TensorProduct.zero_tmul]
  rw [this, zero_mul]

/- English proof (translation)
Establish `e : z - eInf F • z = (1 - eInf F) • z` using `by rw [sub_smul, one_smul]`. Rewrite using `[e, Algebra.smul_def, map_mul]`. Establish `: infPartF F E (algebraMap (AF F) (AEF F E) (1 - eInf F)) = 0` using `by show (fstA F (1 - eInf F)) ⊗ₜ[F] (1 : E) = 0`. Establish `: fstA F (1 - eInf F) = 0`. Rewrite using `[map_sub, map_one]`.

Use `show (1 : Ainf F) - 1 = 0`. Conclude with `sub_self _`. Rewrite using `[this, TensorProduct.zero_tmul]`. Rewrite using `[this, zero_mul]`.
-/
theorem infPartF_sub_eInf_smul (z : AEF F E) : infPartF F E (z - eInf F • z) = 0 := by
  have e : z - eInf F • z = (1 - eInf F) • z := by rw [sub_smul, one_smul]
  rw [e, Algebra.smul_def, map_mul]
  have : infPartF F E (algebraMap (AF F) (AEF F E) (1 - eInf F)) = 0 := by
    show (fstA F (1 - eInf F)) ⊗ₜ[F] (1 : E) = 0
    have : fstA F (1 - eInf F) = 0 := by
      rw [map_sub, map_one]
      show (1 : Ainf F) - 1 = 0
      exact sub_self _
    rw [this, TensorProduct.zero_tmul]
  rw [this, zero_mul]

end GlobalTheory.WeilContF

end

noncomputable section

namespace GlobalTheory.WeilContF

open Formalism.IndefR.DatumF
open scoped Topology

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

attribute [local instance] finiteFE modTop topRing

variable (F E) in

def crd : AEF F E ≃ₗ[AF F] (Fin (Module.finrank F E) → AF F) :=
  (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).equivFun

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap (crd F E).toLinearMap`.
-/
theorem continuous_crd : Continuous (crd F E) :=
  IsModuleTopology.continuous_of_linearMap (crd F E).toLinearMap

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap (crd F E).symm.toLinearMap`.
-/
theorem continuous_crd_symm : Continuous (crd F E).symm :=
  IsModuleTopology.continuous_of_linearMap (crd F E).symm.toLinearMap

/- English proof (translation)
The claim follows from `Prod.ext (one_mul x) (zero_mul (0 : Af F))`.
-/
theorem eInf_mul_pair (x : Ainf F) : eInf F * pairA F x 0 = pairA F x 0 :=
  Prod.ext (one_mul x) (zero_mul (0 : Af F))

/- English proof (translation)
The claim follows from `Prod.ext rfl (zero_mul a.2).symm`.
-/
theorem pair_fst_eInf_mul (a : AF F) : pairA F (eInf F * a).1 0 = eInf F * a :=
  Prod.ext rfl (zero_mul a.2).symm

variable (F E) in

def realCh (nS nT : ℕ) : (Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F) →+ WOF F E nS nT where
  toFun t := fun i j => (crd F E).symm fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0
  map_zero' := by
    funext i j
    show (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0) 0) = 0
    rw [map_zero]
    exact (crd F E).symm.map_zero
  map_add' x y := by
    funext i j
    show (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x (i, j, l) + y (i, j, l))) 0) =
      (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x (i, j, l))) 0) +
      (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y (i, j, l))) 0)
    rw [← map_add]
    congr 1
    funext l
    rw [map_add]
    exact Prod.ext rfl (add_zero (0 : Af F)).symm

variable (F E) in

def realCo (nS nT : ℕ) (y : WOF F E nS nT) : Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F :=
  fun p => InfiniteAdeleRing.ringEquiv_mixedSpace F ((crd F E (y p.1 p.2.1)) p.2.2).1

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => continuous_crd_symm.comp (continuous_pi fun l => ?_)` and prove the remaining obligations. Use `show Continuous fun t : Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l)), (0 : Af F)) : Ainf F × Af F)`. Conclude with `((continuous_mixed_symm F).comp (continuous_apply (i, j, l))).prodMk continuous_const`.
-/
theorem continuous_realCh (nS nT : ℕ) : Continuous (realCh F E nS nT) := by
  refine continuous_pi fun i => continuous_pi fun j => continuous_crd_symm.comp (continuous_pi fun l => ?_)
  show Continuous fun t : Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F =>
    (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l)), (0 : Af F)) : Ainf F × Af F)
  exact ((continuous_mixed_symm F).comp (continuous_apply (i, j, l))).prodMk continuous_const

/- English proof (translation)
Use `continuous_pi fun p => ?_` and prove the remaining obligations. Conclude with `(continuous_mixed F).comp (continuous_fst.comp ((continuous_apply p.2.2).comp (continuous_crd.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))))`.
-/
theorem continuous_realCo (nS nT : ℕ) : Continuous (realCo F E nS nT) := by
  refine continuous_pi fun p => ?_
  exact (continuous_mixed F).comp (continuous_fst.comp ((continuous_apply p.2.2).comp
    (continuous_crd.comp ((continuous_apply p.2.1).comp (continuous_apply p.1)))))

/- English proof (translation)
Use `show finPartF F E ((crd F E).symm fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0) = 0`. Establish `e : (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0) = eInf F • fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0`. Use function extensionality and compare the values at `l`. Conclude with `(eInf_mul_pair _).symm`. Rewrite using `[e, LinearEquiv.map_smul]`.

Conclude with `finPartF_eInf_smul _`.
-/
theorem realCh_fin (nS nT : ℕ) (t) (i j) : finPartF F E (realCh F E nS nT t i j) = 0 := by
  show finPartF F E ((crd F E).symm fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0) = 0
  have e : (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0) =
      eInf F • fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t (i, j, l))) 0 := by
    funext l
    exact (eInf_mul_pair _).symm
  rw [e, LinearEquiv.map_smul]
  exact finPartF_eInf_smul _

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Use `show (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F ((crd F E ((eInf F • y) i j)) l).1)) 0) = (eInf F • y) i j`. Establish `e : (eInf F • y) i j = eInf F • y i j` using `rfl`. Rewrite using `[e, LinearEquiv.map_smul]`. Use `conv_rhs => rw [← (crd F E).symm_apply_apply (eInf F • y i j), LinearEquiv.map_smul]`.

Use `congr 1`. Use function extensionality and compare the values at `l`. Rewrite using `[RingEquiv.symm_apply_apply]`. Conclude with `pair_fst_eInf_mul _`.
-/
theorem realCh_realCo (nS nT : ℕ) (y : WOF F E nS nT) :
    realCh F E nS nT (realCo F E nS nT (eInf F • y)) = eInf F • y := by
  funext i j
  show (crd F E).symm (fun l => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
    (InfiniteAdeleRing.ringEquiv_mixedSpace F ((crd F E ((eInf F • y) i j)) l).1)) 0) = (eInf F • y) i j
  have e : (eInf F • y) i j = eInf F • y i j := rfl
  rw [e, LinearEquiv.map_smul]
  conv_rhs => rw [← (crd F E).symm_apply_apply (eInf F • y i j), LinearEquiv.map_smul]
  congr 1
  funext l
  rw [RingEquiv.symm_apply_apply]
  exact pair_fst_eInf_mul _

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hstd g hU hsm`. Use `haveI := finiteFE (F := F) (E := E)`. Use `haveI := modTop (F := F) (E := E)`. Use `haveI := topRing (F := F) (E := E)`. Use `haveI : IsTopologicalAddGroup (AEF F E) := IsTopologicalRing.to_topologicalAddGroup`.

Take `⟨U, hUo, hUf⟩` from `hU`. Set `φ` to `(Module.finBasis ℝ (Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F)).equivFunL`. Set `L : (Fin _ → ℝ) →+ WOF F E nS nT` to `(realCh F E nS nT).comp φ.symm.toLinearEquiv.toAddMonoidHom`. Establish `hLc : Continuous L` using `(continuous_realCh nS nT).comp φ.symm.continuous`. Establish `hL0 : ∀ t, (L t).map (finPartF F E) = 0` using `fun t => by`.

Use function extensionality and compare the values at `i j`. Conclude with `realCh_fin nS nT _ i j`. Establish `hLφ : ∀ v, L (φ v) = realCh F E nS nT v` using `fun v => by show realCh F E nS nT (φ.symm (φ v)) = _`. Rewrite using `[φ.symm_apply_apply]`. Use `continuous_iff_continuousAt.2 fun w => ?_` and prove the remaining obligations.

Set `a : WOF F E nS nT → WOF F E nS nT` to `fun w' => w + eInf F • (w' - w)`. Set `u : WOF F E nS nT → WOF F E nS nT` to `fun w' => w' - a w'`. Establish `hsmc : Continuous fun y : WOF F E nS nT => eInf F • y` using `continuous_const_smul _`. Establish `ha : Continuous a` using `continuous_const.add (hsmc.comp (continuous_sub_right w))`. Establish `hu : Continuous u` using `continuous_id.sub ha`.

Establish `huw : u w = 0` using `by show w - (w + eInf F • (w - w)) = 0`. Rewrite using `[sub_self, smul_zero, add_zero, sub_self]`. Establish `hinf : ∀ w', (u w').map (infPartF F E) = 0`. Introduce `w'`. Establish `e : u w' = (w' - w) - eInf F • (w' - w)` using `sub_add_eq_sub_sub _ _ _`.

Use function extensionality and compare the values at `i j`. Use `show infPartF F E (u w' i j) = 0`. Rewrite using `[e]`. Conclude with `infPartF_sub_eInf_smul _`. Establish `hga : Continuous fun w' => g (a w')`.

Establish `h1` using `(hsm _ L hLc hL0 w).continuous.comp (φ.continuous.comp ((continuous_realCo nS nT).comp (hsmc.comp (continuous_sub_right w))))`. Use `h1.congr fun w' => ?_` and prove the remaining obligations. Use `show g (w + L (φ (realCo F E nS nT (eInf F • (w' - w))))) = g (w + eInf F • (w' - w))`. Rewrite using `[hLφ, realCh_realCo]`. Establish `hg : Continuous fun w' => B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w')` using `(hstd.1.1.comp (continuous_symplOHF σ JS JT ξ₀ ha hu).neg).mul hga`.

Establish `hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U` using `hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))`. Use `hg.continuousAt.congr (hev.mono fun w' hw' => ?_)` and prove the remaining obligations. Establish `e` using `congrFun (hUf _ hw' (hinf w')) (a w')`. Establish `e2 : a w' + u w' = w'` using `add_sub_cancel _ _`. Use `show B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w') = g w'`.

Rewrite using `[← e]`. Use `show _ * (B.ψ (symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w' + u w')) = _`. Rewrite using `[e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]`.
-/
theorem continuous_of_level_real : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ g : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
      (∃ U : AddSubgroup (Formalism.IndefR.DatumF.WOF F E nS nT), IsOpen (U : Set (Formalism.IndefR.DatumF.WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (Formalism.IndefR.DatumF.infPartF F E) = 0 → Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (u) g = g) →
      (∀ (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.DatumF.WOF F E nS nT), Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
        ∀ w : Formalism.IndefR.DatumF.WOF F E nS nT, ContDiff ℝ ∞ fun x => g (w + L x)) →
      Continuous g := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ hstd g hU hsm
  haveI := finiteFE (F := F) (E := E)
  haveI := modTop (F := F) (E := E)
  haveI := topRing (F := F) (E := E)
  haveI : IsTopologicalAddGroup (AEF F E) := IsTopologicalRing.to_topologicalAddGroup
  obtain ⟨U, hUo, hUf⟩ := hU
  let φ := (Module.finBasis ℝ (Fin nT × Fin nS × Fin (Module.finrank F E) → mixedEmbedding.mixedSpace F)).equivFunL
  let L : (Fin _ → ℝ) →+ WOF F E nS nT := (realCh F E nS nT).comp φ.symm.toLinearEquiv.toAddMonoidHom
  have hLc : Continuous L := (continuous_realCh nS nT).comp φ.symm.continuous
  have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => by
    funext i j
    exact realCh_fin nS nT _ i j
  have hLφ : ∀ v, L (φ v) = realCh F E nS nT v := fun v => by
    show realCh F E nS nT (φ.symm (φ v)) = _
    rw [φ.symm_apply_apply]
  refine continuous_iff_continuousAt.2 fun w => ?_
  let a : WOF F E nS nT → WOF F E nS nT := fun w' => w + eInf F • (w' - w)
  let u : WOF F E nS nT → WOF F E nS nT := fun w' => w' - a w'
  have hsmc : Continuous fun y : WOF F E nS nT => eInf F • y := continuous_const_smul _
  have ha : Continuous a := continuous_const.add (hsmc.comp (continuous_sub_right w))
  have hu : Continuous u := continuous_id.sub ha
  have huw : u w = 0 := by
    show w - (w + eInf F • (w - w)) = 0
    rw [sub_self, smul_zero, add_zero, sub_self]
  have hinf : ∀ w', (u w').map (infPartF F E) = 0 := by
    intro w'
    have e : u w' = (w' - w) - eInf F • (w' - w) := sub_add_eq_sub_sub _ _ _
    funext i j
    show infPartF F E (u w' i j) = 0
    rw [e]
    exact infPartF_sub_eInf_smul _
  have hga : Continuous fun w' => g (a w') := by
    have h1 := (hsm _ L hLc hL0 w).continuous.comp
      (φ.continuous.comp ((continuous_realCo nS nT).comp (hsmc.comp (continuous_sub_right w))))
    refine h1.congr fun w' => ?_
    show g (w + L (φ (realCo F E nS nT (eInf F • (w' - w))))) = g (w + eInf F • (w' - w))
    rw [hLφ, realCh_realCo]
  have hg : Continuous fun w' => B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w') :=
    (hstd.1.1.comp (continuous_symplOHF σ JS JT ξ₀ ha hu).neg).mul hga
  have hev : ∀ᶠ w' in 𝓝 w, u w' ∈ U :=
    hu.continuousAt.preimage_mem_nhds (hUo.mem_nhds (by rw [huw]; exact U.zero_mem))
  refine hg.continuousAt.congr (hev.mono fun w' hw' => ?_)
  have e := congrFun (hUf _ hw' (hinf w')) (a w')
  have e2 : a w' + u w' = w' := add_sub_cancel _ _
  show B.ψ (-symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w') = g w'
  rw [← e]
  show _ * (B.ψ (symplOHF σ JS JT ξ₀ (a w') (u w')) * g (a w' + u w')) = _
  rw [e2, ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.WeilContF
