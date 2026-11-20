import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotypicFactorOfIsIrreduciblePiFiniteGroups
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorRepOfEmbeddingsIsIrreducibleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.AlgWtBC

section DualBC

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {G : Type} [Group G]
  {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

def dualBC : K' ⊗[K] Module.Dual K V ≃ₗ[K'] Module.Dual K' (K' ⊗[K] V) :=
  (TensorProduct.isBaseChange K V K').toDualBaseChange

/- English proof (translation)
The claim follows from `(TensorProduct.isBaseChange K V K').toDualBaseChange_tmul a f v`.
-/
theorem dualBC_tmul (a : K') (f : Module.Dual K V) (v : V) :
    dualBC (a ⊗ₜ[K] f) ((1 : K') ⊗ₜ[K] v) = a * algebraMap K K' (f v) :=
  (TensorProduct.isBaseChange K V K').toDualBaseChange_tmul a f v

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a g`. Apply `(TensorProduct.isBaseChange K V K').algHom_ext` to reduce the goal to its premises.

Introduce `v`. Simplify using `only [TensorProduct.mk_apply, LinearMap.baseChange_tmul, LinearMap.dualMap_apply, dualBC_tmul]`.
-/
theorem dualBC_natural (f : V →ₗ[K] V) (x : K' ⊗[K] Module.Dual K V) :
    dualBC (f.dualMap.baseChange K' x) = (f.baseChange K').dualMap (dualBC x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a g =>
    apply (TensorProduct.isBaseChange K V K').algHom_ext
    intro v
    simp only [TensorProduct.mk_apply, LinearMap.baseChange_tmul, LinearMap.dualMap_apply, dualBC_tmul]

/- English proof (translation)
Use `GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv _ _ (dualBC (K' := K') (V := V)).symm ?_ h` and prove the remaining obligations. Introduce `g x`. Apply `dualBC.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply]`. Use `show dualBC ((ρ g⁻¹).dualMap.baseChange K' _) = ((ρ g⁻¹).baseChange K').dualMap x`.

Rewrite using `[dualBC_natural, LinearEquiv.apply_symm_apply]`.
-/
theorem isIrreducible_bcRep_dual (ρ : Representation K G V)
    (h : (bcRep (K' := K') ρ).dual.IsIrreducible) : (bcRep (K' := K') ρ.dual).IsIrreducible := by
  refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv _ _ (dualBC (K' := K') (V := V)).symm ?_ h
  intro g x
  apply dualBC.injective
  rw [LinearEquiv.apply_symm_apply]
  show dualBC ((ρ g⁻¹).dualMap.baseChange K' _) = ((ρ g⁻¹).baseChange K').dualMap x
  rw [dualBC_natural, LinearEquiv.apply_symm_apply]

end DualBC

end GlobalTheory.AlgWtBC

noncomputable section

namespace GlobalTheory.AlgWtBC

open Formalism.L2.DIV

section CoefBC

variable {K K' : Type} [Field K] [Field K'] [Algebra K K'] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, MvPolynomial.map_X]`.

Use `congr 1`. Simplify using `only [Formalism.GradedWeylDivisibility.colAddGen, MvPolynomial.aeval_X]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_colAddGen {r m : ℕ} (l j : Fin m) (f : MvPolynomial (Fin r × Fin m) K) :
    MvPolynomial.map (algebraMap K K') (Formalism.GradedWeylDivisibility.colAddGen K l j f) =
      Formalism.GradedWeylDivisibility.colAddGen K' l j (MvPolynomial.map (algebraMap K K') f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    congr 1
    simp only [Formalism.GradedWeylDivisibility.colAddGen, MvPolynomial.aeval_X]
    split_ifs <;> simp

/- English proof (translation)
Simplify using `only [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero, MvPolynomial.mem_weightedHomogeneousSubmodule] at hf ⊢`. Use `⟨fun d hd => hf.1 (by` and prove the remaining obligations. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[MvPolynomial.coeff_map, h0, map_zero]), fun l j hlj => ?_⟩`.

Rewrite using `[← map_colAddGen, hf.2 l j hlj, MvPolynomial.map_rename]`.
-/
theorem map_mem_dualWeyl {r m : ℕ} (ν : Fin m → ℕ) {f : MvPolynomial (Fin r × Fin m) K}
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r m ν) :
    MvPolynomial.map (algebraMap K K') f ∈ Formalism.GradedWeylDivisibility.dualWeyl K' r m ν := by
  simp only [Formalism.GradedWeylDivisibility.dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, MvPolynomial.mem_weightedHomogeneousSubmodule] at hf ⊢
  refine ⟨fun d hd => hf.1 (by
    intro h0
    apply hd
    rw [MvPolynomial.coeff_map, h0, map_zero]), fun l j hlj => ?_⟩
  rw [← map_colAddGen, hf.2 l j hlj, MvPolynomial.map_rename]

/- English proof (translation)
Unfold `VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢`. Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem P hP`. Take `⟨G, hG, rfl⟩` from `hP`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨fun s => MvPolynomial.map (algebraMap K K') (G s), fun s => map_mem_dualWeyl _ (hG s), ?_⟩` and prove the remaining obligations. Simplify using `only [map_prod, Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.map_rename]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul c x _ hx`. Rewrite using `[MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem map_mem_VV (lam : ι → DomWeight n) {F : Pol K ι n} (hF : F ∈ VV K lam) :
    MvPolynomial.map (algebraMap K K') F ∈ VV K' lam := by
  unfold VV Formalism.GradedWeylDivisibility.tensorLat at hF ⊢
  induction hF using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨G, hG, rfl⟩ := hP
    apply Submodule.subset_span
    refine ⟨fun s => MvPolynomial.map (algebraMap K K') (G s), fun s => map_mem_dualWeyl _ (hG s), ?_⟩
    simp only [map_prod, Formalism.GradedWeylDivisibility.blockEmb, MvPolynomial.map_rename]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx =>
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Unfold `detPow`. Establish `: Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap K K') g) = Units.map (algebraMap K K' : K →* K') (Matrix.GeneralLinearGroup.det g)` using `by ext; simp [RingHom.map_det]`. Rewrite using `[this, ← map_zpow (Units.map (algebraMap K K' : K →* K')) (Matrix.GeneralLinearGroup.det g) c, Units.coe_map]`. Both sides reduce to the same expression.
-/
theorem detPow_map (g : GL (Fin n) K) (c : ℤ) :
    algebraMap K K' (detPow K n g c) = detPow K' n (Matrix.GeneralLinearGroup.map (algebraMap K K') g) c := by
  unfold detPow
  have : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap K K') g) =
      Units.map (algebraMap K K' : K →* K') (Matrix.GeneralLinearGroup.det g) := by
    ext; simp [RingHom.map_det]
  rw [this, ← map_zpow (Units.map (algebraMap K K' : K →* K')) (Matrix.GeneralLinearGroup.det g) c, Units.coe_map]
  rfl

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, MvPolynomial.map_X]`.

Use `congr 1`. Simplify using `[trAct, Formalism.GradedWeylDivisibility.blockAct, map_sum]`.
-/
theorem map_trAct (g : ι → GL (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map (algebraMap K K') (trAct g F) =
      trAct (fun τ => Matrix.GeneralLinearGroup.map (algebraMap K K') (g τ)) (MvPolynomial.map (algebraMap K K') F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    congr 1
    simp [trAct, Formalism.GradedWeylDivisibility.blockAct, map_sum]

/- English proof (translation)
Simplify using `only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_trAct]`. Use `congr 2`. Simplify using `only [detTwK, map_prod, detPow_map]`.
-/
theorem map_actP (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (F : Pol K ι n) :
    MvPolynomial.map (algebraMap K K') (actP lam g F) =
      actP lam (fun τ => Matrix.GeneralLinearGroup.map (algebraMap K K') (g τ))
        (MvPolynomial.map (algebraMap K K') F) := by
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, MvPolynomial.smul_eq_C_mul, map_mul,
    MvPolynomial.map_C, map_trAct]
  congr 2
  simp only [detTwK, map_prod, detPow_map]

def bcPol (lam : ι → DomWeight n) : K' ⊗[K] VV K lam →ₗ[K'] Pol K' ι n :=
  (MvPolynomial.algebraTensorAlgEquiv K K').toLinearEquiv.toLinearMap ∘ₗ (VV K lam).subtype.baseChange K'

/- English proof (translation)
Simplify using `[bcPol]`.
-/
theorem bcPol_tmul (lam : ι → DomWeight n) (a : K') (F : VV K lam) :
    bcPol lam (a ⊗ₜ[K] F) = a • MvPolynomial.map (algebraMap K K') (F : Pol K ι n) := by
  simp [bcPol]

/- English proof (translation)
Use `(MvPolynomial.algebraTensorAlgEquiv K K').toLinearEquiv.injective.comp ?_` and prove the remaining obligations. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap _ (VV K lam).injective_subtype`.
-/
theorem bcPol_injective (lam : ι → DomWeight n) : Function.Injective (bcPol (K := K) (K' := K') lam) := by
  refine (MvPolynomial.algebraTensorAlgEquiv K K').toLinearEquiv.injective.comp ?_
  exact Module.Flat.lTensor_preserves_injective_linearMap _ (VV K lam).injective_subtype

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `tmul a F => rw [bcPol_tmul]`.

Conclude with `(VV K' lam).smul_mem a (map_mem_VV lam F.2)`.
-/
theorem bcPol_mem (lam : ι → DomWeight n) (x : K' ⊗[K] VV K lam) : bcPol lam x ∈ VV K' lam := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul a F => rw [bcPol_tmul]; exact (VV K' lam).smul_mem a (map_mem_VV lam F.2)

/- English proof (translation)
Rewrite using `[Module.finrank_baseChange, Module.finrank_eq_card_basis (bVV K lam), Module.finrank_eq_card_basis (bVV K' lam)]`.
-/
theorem finrank_bc_VV (lam : ι → DomWeight n) :
    Module.finrank K' (K' ⊗[K] VV K lam) = Module.finrank K' (VV K' lam) := by
  rw [Module.finrank_baseChange, Module.finrank_eq_card_basis (bVV K lam),
    Module.finrank_eq_card_basis (bVV K' lam)]

def bcVV (lam : ι → DomWeight n) : K' ⊗[K] VV K lam ≃ₗ[K'] VV K' lam :=
  LinearMap.linearEquivOfInjective (LinearMap.codRestrict (VV K' lam) (bcPol lam) (bcPol_mem lam))
    (by intro x y h; exact bcPol_injective lam (congrArg Subtype.val h)) (finrank_bc_VV lam)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem bcVV_val (lam : ι → DomWeight n) (x : K' ⊗[K] VV K lam) : (bcVV lam x : Pol K' ι n) = bcPol lam x := rfl

end CoefBC

section Weight

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {ι : Type} [Fintype ι]
  {K K' : Type} [Field K] [Field K'] [Algebra K K']

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use extensionality with `i j`. Simplify using `[GlobalTheory.AlgWtF.embGLF]`.
-/
theorem embGLF_comp (emb : ι → L →+* K) (γ : GL (Fin n) L) :
    GlobalTheory.AlgWtF.embGLF (fun τ => (algebraMap K K').comp (emb τ)) γ =
      fun τ => Matrix.GeneralLinearGroup.map (algebraMap K K') (GlobalTheory.AlgWtF.embGLF emb γ τ) := by
  funext τ
  ext i j
  simp [GlobalTheory.AlgWtF.embGLF]

/- English proof (translation)
Use `GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv _ _ (bcVV (K := K) (K' := K') lam).symm ?_ h` and prove the remaining obligations. Introduce `γ x`. Apply `(bcVV (K := K) (K' := K') lam).injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply]`. Take `⟨y, rfl⟩` from `(bcVV (K := K) (K' := K') lam).surjective x`.

Rewrite using `[LinearEquiv.symm_apply_apply]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[bcVV_val]`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]`. Consider the case `tmul a F => show bcPol lam (a ⊗ₜ[K] (GlobalTheory.AlgWtF.tenRepF emb lam γ F)) = actP lam (GlobalTheory.AlgWtF.embGLF _ (GlobalTheory.AlgWtF.ratHom γ)) (bcVV lam (a ⊗ₜ[K] F) : Pol K' ι n)`. Rewrite using `[bcVV_val, bcPol_tmul, bcPol_tmul, map_smul, embGLF_comp]`. Use `congr 1`. Conclude with `map_actP lam _ _`.
-/
theorem isIrreducible_bcRep_tenRepF (emb : ι → L →+* K) (lam : ι → DomWeight n)
    (h : (GlobalTheory.AlgWtF.tenRepF (fun τ => (algebraMap K K').comp (emb τ)) lam).IsIrreducible) :
    (bcRep (K' := K') (GlobalTheory.AlgWtF.tenRepF emb lam)).IsIrreducible := by
  refine GlobalTheory.PiIsotypic.isIrreducible_of_linearEquiv _ _ (bcVV (K := K) (K' := K') lam).symm ?_ h
  intro γ x
  apply (bcVV (K := K) (K' := K') lam).injective
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨y, rfl⟩ := (bcVV (K := K) (K' := K') lam).surjective x
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [bcVV_val]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
  | tmul a F =>
    show bcPol lam (a ⊗ₜ[K] (GlobalTheory.AlgWtF.tenRepF emb lam γ F)) =
      actP lam (GlobalTheory.AlgWtF.embGLF _ (GlobalTheory.AlgWtF.ratHom γ)) (bcVV lam (a ⊗ₜ[K] F) : Pol K' ι n)
    rw [bcVV_val, bcPol_tmul, bcPol_tmul, map_smul, embGLF_comp]
    congr 1
    exact map_actP lam _ _

end Weight

end GlobalTheory.AlgWtBC

noncomputable section

namespace GlobalTheory.AlgWtBC

/- English proof (translation)
Use `⟨fun τ τ' he => h.1 ?_, fun τ τ' he => h.2 τ τ' ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `(algebraMap K K').injective (RingHom.congr_fun he x)`. Use extensionality with `x`. Conclude with `(algebraMap K K').injective (RingHom.congr_fun he x)`.
-/
theorem cmDist_comp {L : Type} [Field L] [NumberField L] [IsCMField L] {ι : Type} {K K' : Type} [Field K] [Field K']
    [Algebra K K'] (emb : ι → L →+* K) (h : GlobalTheory.AlgWtF.CMDist emb) :
    GlobalTheory.AlgWtF.CMDist (fun τ => (algebraMap K K').comp (emb τ)) := by
  refine ⟨fun τ τ' he => h.1 ?_, fun τ τ' he => h.2 τ τ' ?_⟩
  · ext x
    exact (algebraMap K K').injective (RingHom.congr_fun he x)
  · ext x
    exact (algebraMap K K').injective (RingHom.congr_fun he x)

/- English proof (translation)
Introduce `L _ _ _ n ι _ K _ _ emb lam hCM K' _ _`. Use `haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective`. Establish `h1` using `GlobalTheory.T.weightTensorRepOfEmbeddings_isIrreducible L n ι K' (fun τ => (algebraMap K K').comp (emb τ)) lam (cmDist_comp emb hCM)`. Establish `h2` using `isIrreducible_bcRep_tenRepF (K' := K') emb lam h1`. Establish `h3` using `GlobalTheory.T.contragredient_isIrreducible_finiteDimensional K' _ _ _ h2`.

Conclude with `isIrreducible_bcRep_dual _ h3`.
-/
theorem isIrreducible_bcRep_wtRepF : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (ι : Type) [Fintype ι] (K : Type) [Field K] [CharZero K]
    (emb : ι → L →+* K) (lam : ι → DomWeight n), GlobalTheory.AlgWtF.CMDist emb → ∀ (K' : Type) [Field K'] [Algebra K K'],
      (Formalism.IndefR.NX.bcRep (K' := K') (GlobalTheory.AlgWtF.wtRepF emb lam)).IsIrreducible := by
  intro L _ _ _ n ι _ K _ _ emb lam hCM K' _ _
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  have h1 := GlobalTheory.T.weightTensorRepOfEmbeddings_isIrreducible L n ι K' (fun τ => (algebraMap K K').comp (emb τ)) lam (cmDist_comp emb hCM)
  have h2 := isIrreducible_bcRep_tenRepF (K' := K') emb lam h1
  have h3 := GlobalTheory.T.contragredient_isIrreducible_finiteDimensional K' _ _ _ h2
  exact isIrreducible_bcRep_dual _ h3

end GlobalTheory.AlgWtBC
