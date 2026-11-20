import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHNeat
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ReHermitianCombinationNonpos

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf
open Matrix NumberField
open scoped TensorProduct

namespace Formalism.L2.SG.PoincareInHH.Cut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

section R6a

variable {D : D7} (X : HidaSetting D)

def matLC (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E) : (VS D).V →ₗ[D.host.E] (VS D).V :=
  X.bas.equivFun.symm.toLinearMap ∘ₗ Matrix.toLin' A ∘ₗ X.bas.equivFun.toLinearMap

/- English proof (translation)
Simplify using `only [matLC, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.apply_symm_apply, Matrix.toLin'_apply]`.
-/
theorem matL_reprC (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E) (y : (VS D).V) :
    X.bas.equivFun (matLC X A y) = A *ᵥ X.bas.equivFun y := by
  simp only [matLC, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply, Matrix.toLin'_apply]

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Apply `X.bas.equivFun.injective` to reduce the goal to its premises. Rewrite using `[LinearMap.comp_apply, matL_reprC, matL_reprC, matL_reprC, Matrix.mulVec_mulVec]`.
-/
theorem matL_mulC (A B : Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E) :
    matLC X (A * B) = matLC X A ∘ₗ matLC X B := by
  apply LinearMap.ext
  intro y
  apply X.bas.equivFun.injective
  rw [LinearMap.comp_apply, matL_reprC, matL_reprC, matL_reprC, Matrix.mulVec_mulVec]

/- English proof (translation)
Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Apply `X.bas.equivFun.injective` to reduce the goal to its premises. Rewrite using `[matL_reprC, Matrix.one_mulVec, LinearMap.id_apply]`.
-/
theorem matL_oneC : matLC X 1 = LinearMap.id := by
  apply LinearMap.ext
  intro y
  apply X.bas.equivFun.injective
  rw [matL_reprC, Matrix.one_mulVec, LinearMap.id_apply]

abbrev mapMC : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E →+* Matrix (Fin X.B.I.n) (Fin X.B.I.n) D.host.E :=
  (X.ιE : X.B.I.E →+* D.host.E).mapMatrix

def matEC (M : GL (Fin X.B.I.n) X.B.I.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (matLC X (mapMC X (M : Matrix _ _ _))) (matLC X (mapMC X ((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix _ _ _)))
    (by rw [← matL_mulC, ← map_mul, M.mul_inv, map_one, matL_oneC])
    (by rw [← matL_mulC, ← map_mul, M.inv_mul, map_one, matL_oneC])

/- English proof (translation)
The claim follows from `matL_reprC X _ y`.
-/
theorem matE_reprC (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.bas.equivFun (matEC X M y) = mapMC X (M : Matrix _ _ _) *ᵥ X.bas.equivFun y :=
  matL_reprC X _ y

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h` using `congrFun (matE_reprC X M y) i`. Simplify using `only [Module.Basis.equivFun_apply] at h`. Simplify using `only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, h, Matrix.mulVec, dotProduct, mapMC, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply, Module.Basis.equivFun_apply]`.
-/
theorem matE_crdC (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    X.crd (matEC X M y) = (M : Matrix _ _ _) *ᵥ X.crd y := by
  funext i
  have h := congrFun (matE_reprC X M y) i
  simp only [Module.Basis.equivFun_apply] at h
  simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, h, Matrix.mulVec, dotProduct, mapMC,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply, Module.Basis.equivFun_apply]

/- English proof (translation)
Rewrite using `[matE_crdC]`. Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.L2.SG.HidaSetting.incl]`. Conclude with `RingHom.map_mulVec _ _ _ i`.
-/
theorem matE_inclC (M : GL (Fin X.B.I.n) X.B.I.E) (y : (VS D).V) :
    incl X.B.I (X.crd (matEC X M y)) =
      (M : Matrix _ _ _).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ incl X.B.I (X.crd y) := by
  rw [matE_crdC]
  funext i
  simp only [Formalism.L2.SG.HidaSetting.incl]
  exact RingHom.map_mulVec _ _ _ i

end R6a

section NormLeOneOfIntegral

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Use `conv_lhs => rw [← X.bas.sum_equivFun x, ← X.bas.sum_equivFun y]`. Simplify using `only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, starRingEnd_apply, Finset.mul_sum]`. Use `Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hT_expandC (x y : (VS D).V) :
    (VS D).hT x y =
      ∑ i, ∑ j, star (X.bas.equivFun x i) * (X.bas.equivFun y j * (VS D).hT (X.bas i) (X.bas j)) := by
  conv_lhs => rw [← X.bas.sum_equivFun x, ← X.bas.sum_equivFun y]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    map_smul, smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_comm.trans (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_)
  ring

/- English proof (translation)
Simplify using `only [dotProduct, Matrix.mulVec, mapMC, RingHom.mapMatrix_apply, Matrix.map_apply, Pi.star_apply, Finset.mul_sum, RingEquiv.coe_toRingHom]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qformC (a c : Fin X.B.I.n → D.host.E) :
    ∑ i, ∑ j, star (a i) * (c j * X.ιE (X.B.I.J i j)) = star a ⬝ᵥ (mapMC X X.B.I.J *ᵥ c) := by
  simp only [dotProduct, Matrix.mulVec, mapMC, RingHom.mapMatrix_apply, Matrix.map_apply, Pi.star_apply,
    Finset.mul_sum, RingEquiv.coe_toRingHom]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `hstar : ∀ y : D.host.E, D.host.conj y = star y` using `fun y => by haveI := D.host.isCMField_hostE`. Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[← D.embE_φ₀, RingHom.comp_apply, RingHom.comp_apply, D.embE_conj, D.starLL_cx]`. Use `first`. Consider the case `exact (NumberField.IsCMField.complexEmbedding_complexConj (D.what₂.embLL.comp D.embE) y).symm`.

Consider the case `exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (D.what₂.embLL.comp D.embE) y).symm`. Establish `hc : ∀ x : X.B.I.E, X.ιE (star x) = star (X.ιE x)` using `fun x => by`. Rewrite using `[X.ιE_conj, hstar]`. Establish `h0 : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _) * X.B.I.J * (M : Matrix _ _ _) = X.B.I.J` using `hM`. Establish `h1` using `congrArg (mapMC X) h0`.

Rewrite `h1` using `[map_mul, map_mul]`. Establish `h2 : mapMC X (Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _)) = (mapMC X (M : Matrix _ _ _))ᴴ`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, Matrix.conjTranspose_apply, hc]`. Apply the tactic sequence `all_goals first`.

Consider the case `(rw [starRingEnd_apply]; exact hc _)`. Consider the case `exact hc _`. Rewrite `h1` using `[h2]`. Conclude with `h1`.
-/
theorem mapM_unitaryC (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    (mapMC X (M : Matrix _ _ _))ᴴ * mapMC X X.B.I.J * mapMC X (M : Matrix _ _ _) = mapMC X X.B.I.J := by

  have hstar : ∀ y : D.host.E, D.host.conj y = star y := fun y => by
    haveI := D.host.isCMField_hostE
    apply D.host.φ₀.injective
    rw [← D.embE_φ₀, RingHom.comp_apply, RingHom.comp_apply, D.embE_conj, D.starLL_cx]
    first
    | exact (NumberField.IsCMField.complexEmbedding_complexConj (D.what₂.embLL.comp D.embE) y).symm
    | exact (NumberField.IsCMField.complexEmbedding_complexConj (K := D.host.E) (D.what₂.embLL.comp D.embE) y).symm
  have hc : ∀ x : X.B.I.E, X.ιE (star x) = star (X.ιE x) := fun x => by
    rw [X.ιE_conj, hstar]
  have h0 : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _) * X.B.I.J * (M : Matrix _ _ _) = X.B.I.J := hM
  have h1 := congrArg (mapMC X) h0
  rw [map_mul, map_mul] at h1
  have h2 : mapMC X (Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix _ _ _)) = (mapMC X (M : Matrix _ _ _))ᴴ := by
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, hc]
    all_goals first
      | (rw [starRingEnd_apply]; exact hc _)
      | exact hc _
  rw [h2] at h1
  exact h1

/- English proof (translation)
Use `show ∀ x y, (VS D).hT (matEC X M x) (matEC X M y) = (VS D).hT x y`. Introduce `x y`. Establish `hu` using `mapM_unitaryC X M hM`. Rewrite using `[hT_expandC X (matEC X M x) (matEC X M y), hT_expandC X x y]`. Simplify using `only [← X.J_eq, qformC, matE_reprC, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hu]`.
-/
theorem matE_isomC (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    matEC X M ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := by
  show ∀ x y, (VS D).hT (matEC X M x) (matEC X M y) = (VS D).hT x y
  intro x y
  have hu := mapM_unitaryC X M hM
  rw [hT_expandC X (matEC X M x) (matEC X M y), hT_expandC X x y]
  simp only [← X.J_eq, qformC, matE_reprC, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hu]

end NormLeOneOfIntegral

/- English proof (translation)
Use `first`. Consider the case `infer_instance`. Consider the case `(unfold Af; infer_instance)`. Consider the case `(obtain ⟨p, hp0, hp⟩ := (Ring.not_isField_iff_exists_prime).1 (NumberField.RingOfIntegers.not_isField F)`. Set `v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)` to `⟨p, hp, hp0⟩`.

Use `⟨⟨0, 1, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h'` using `congrArg (fun z : Af F => (z : ∀ w, IsDedekindDomain.HeightOneSpectrum.adicCompletion F w) v) h`. Use `first`. Consider the case `exact (zero_ne_one (α := IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)) h'`. Consider the case `exact zero_ne_one h')`.
-/
theorem af_nontrivC (F : Type) [Field F] [NumberField F] : Nontrivial (Af F) := by
  first
  | infer_instance
  | (unfold Af; infer_instance)
  | (obtain ⟨p, hp0, hp⟩ := (Ring.not_isField_iff_exists_prime).1 (NumberField.RingOfIntegers.not_isField F)
     let v : IsDedekindDomain.HeightOneSpectrum (𝓞 F) := ⟨p, hp, hp0⟩
     refine ⟨⟨0, 1, fun h => ?_⟩⟩
     have h' := congrArg (fun z : Af F => (z : ∀ w, IsDedekindDomain.HeightOneSpectrum.adicCompletion F w) v) h
     first
     | exact (zero_ne_one (α := IsDedekindDomain.HeightOneSpectrum.adicCompletion F v)) h'
     | exact zero_ne_one h')

/- English proof (translation)
Use `haveI := af_nontrivC X.B.I.F`. Conclude with `Algebra.TensorProduct.includeLeft_injective (R := X.B.I.F) (S := X.B.I.F) (RingHom.injective _)`.
-/
theorem inclInjC {D : D7} (X : HidaSetting D) : Function.Injective (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) : X.B.I.E → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
  haveI := af_nontrivC X.B.I.F
  exact Algebra.TensorProduct.includeLeft_injective (R := X.B.I.F) (S := X.B.I.F) (RingHom.injective _)

def latOfC (h : Hfin X u) : Set (VS D).V :=
  {y | X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y) ∈ X.B.I.Lf}

def LatOfLattice : Prop :=
  ∀ h : Hfin X u, ∃ Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V,
    (Λ : Set (VS D).V) = latOfC X u h ∧ Submodule.IsLattice D.host.E Λ

/- English proof (translation)
Take `⟨γ, -, hinf, hfin⟩` from `hy`. Rewrite `hfin` using `[h2, show X.B.I.fmat 1 = 1 from rfl]`. Establish `hγ : (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = 1`. Use extensionality with `i j`. Apply `inclInjC X` to reduce the goal to its premises.

Establish `hij` using `congrFun (congrFun hfin i) j`. Rewrite `hij` using `[Matrix.map_apply]`. Rewrite using `[← hij, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h1 : y.1 = 1`.

Use function extensionality and compare the values at `v`. Establish `hv` using `hinf v`. Rewrite `hv` using `[hγ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v))]`. Use `first`. Consider the case `exact Subtype.ext (Units.ext hv)`.

Consider the case `(apply Subtype.ext; apply Units.ext; simpa using hv)`. Conclude with `Prod.ext h1 h2`.
-/
theorem gf_eq_one_of_snd (y : X.B.I.GA) (hy : y ∈ X.B.I.GFset) (h2 : y.2 = 1) : y = 1 := by
  obtain ⟨γ, -, hinf, hfin⟩ := hy
  rw [h2, show X.B.I.fmat 1 = 1 from rfl] at hfin
  have hγ : (γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = 1 := by
    ext i j
    apply inclInjC X
    have hij := congrFun (congrFun hfin i) j
    rw [Matrix.map_apply] at hij
    rw [← hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h1 : y.1 = 1 := by
    funext v
    have hv := hinf v
    rw [hγ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (X.B.I.P_unit v))] at hv
    first
    | exact Subtype.ext (Units.ext hv)
    | (apply Subtype.ext; apply Units.ext; simpa using hv)
  exact Prod.ext h1 h2

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf]`. Simplify using `[Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, h, Ne.symm h, Finsupp.single_apply]`.
-/
theorem crd_bas (i : Fin X.B.I.n) : X.crd (X.bas i) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h
    simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf]
  · simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf, h, Ne.symm h, Finsupp.single_apply]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[Formalism.L2.SG.HidaSetting.incl]`. Simplify using `[Formalism.L2.SG.HidaSetting.incl, h]`.
-/
theorem incl_single (i : Fin X.B.I.n) : incl X.B.I (Pi.single i 1) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h
    simp [Formalism.L2.SG.HidaSetting.incl]
  · simp [Formalism.L2.SG.HidaSetting.incl, h]

/- English proof (translation)
Establish `hm : X.B.I.fmat g = 1`. Use extensionality with `i j`. Establish `h` using `congrFun (hg (X.bas j)) i`. Rewrite `h` using `[crd_bas, incl_single, Matrix.mulVec_single_one]`. Establish `h2 : X.B.I.fmat g i j = (Pi.single j 1 : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) i` using `by first`.

Consider the case `exact h`. Consider the case `simpa using h`. Rewrite `h2` using `[Pi.single_apply]`. Rewrite using `[Matrix.one_apply]`. Conclude with `h2`.

Conclude with `Subtype.ext (Units.ext hm)`.
-/
theorem fmat_eq_one_of_fix (g : X.B.I.Gf) (hg : ∀ y, X.B.I.fmat g *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd y)) :
    g = 1 := by
  have hm : X.B.I.fmat g = 1 := by
    ext i j
    have h := congrFun (hg (X.bas j)) i
    rw [crd_bas, incl_single, Matrix.mulVec_single_one] at h
    have h2 : X.B.I.fmat g i j = (Pi.single j 1 : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) i := by
      first
      | exact h
      | simpa using h
    rw [Pi.single_apply] at h2
    rw [Matrix.one_apply]
    exact h2
  exact Subtype.ext (Units.ext hm)

/- English proof (translation)
Establish `hs : ∀ x y, (VS D).hT y x = star ((VS D).hT x y)` using `fun x y => by first`. Consider the case `exact ((VS D).herm.eq x y).symm`. Consider the case `exact ((VS D).herm x y).symm`. Establish `hzz : (VS D).hT (X.zu u) (X.zu u) ≠ 0`. Rewrite using `[X.zu_norm u, neg_ne_zero, Nat.cast_ne_zero]`.

Introduce `hT0`. Establish `hc` using `D.host.level_coprimeS _ (D.T_level u)`. Rewrite `hc` using `[hT0, Nat.coprime_zero_left]`. Establish `hdvd` using `D.host.tower_dvd`. Rewrite `hdvd` using `[hc, Nat.dvd_one]`.

Use `first`. Consider the case `exact absurd hdvd (by simp)`. Consider the case `simp at hdvd`. Consider the case `omega`. Establish `hfe : ∀ a b, (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0` using `fun a b => by`.

Rewrite using `[hs, X.ef]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hze : ∀ a, (VS D).hT (X.zu u) (X.eX a) = 0` using `fun a => by`. Rewrite using `[hs, (X.zu_orth u a).1, star_zero]`. Establish `hzf : ∀ a, (VS D).hT (X.zu u) (X.fY a) = 0` using `fun a => by`.

Rewrite using `[hs, (X.zu_orth u a).2, star_zero]`. Use `⟨∑ a, (VS D).hT (X.fY a) v • X.eX a + ∑ a, (VS D).hT (X.eX a) v • X.fY a + ((VS D).hT (X.zu u) v / (VS D).hT (X.zu u) (X.zu u)) • X.zu u, ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl ⟨a, rfl⟩)))`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ⟨a, rfl⟩)))`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))`. Establish `key : ∀ x ∈ Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}, (VS D).hT x (v - (∑ a, (VS D).hT (X.fY a) v • X.eX a + ∑ a, (VS D).hT (X.eX a) v • X.fY a + ((VS D).hT (X.zu u) v / (VS D).hT (X.zu u) (X.zu u)) • X.zu u)) = 0`. Introduce `x hx`. Break down `hx with (⟨b, rfl⟩ | ⟨b, rfl⟩) | hz` into its components or cases. Simplify using `[map_sub, map_add, map_sum, map_smul, smul_eq_mul, X.ee, X.ef, (X.zu_orth u b).1, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']`.

Simplify using `[map_sub, map_add, map_sum, map_smul, smul_eq_mul, X.ff, hfe, (X.zu_orth u b).2, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality. Simplify using `[map_sub, map_add, map_sum, map_smul, smul_eq_mul, hze, hzf, hzz]`. Simplify using `only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]`.

Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact key y hy`. Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add, LinearMap.add_apply, hy, hz, add_zero]`.

Consider the case `smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]`.
-/
theorem decomp (v : (VS D).V) : ∃ s ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}),
    v - s ∈ orth (VS D) (Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u})) := by
  have hs : ∀ x y, (VS D).hT y x = star ((VS D).hT x y) := fun x y => by
    first
    | exact ((VS D).herm.eq x y).symm
    | exact ((VS D).herm x y).symm
  have hzz : (VS D).hT (X.zu u) (X.zu u) ≠ 0 := by
    rw [X.zu_norm u, neg_ne_zero, Nat.cast_ne_zero]

    intro hT0
    have hc := D.host.level_coprimeS _ (D.T_level u)
    rw [hT0, Nat.coprime_zero_left] at hc
    have hdvd := D.host.tower_dvd
    rw [hc, Nat.dvd_one] at hdvd
    first
    | exact absurd hdvd (by simp)
    | simp at hdvd
    | omega
  have hfe : ∀ a b, (VS D).hT (X.fY b) (X.eX a) = if a = b then 1 else 0 := fun a b => by
    rw [hs, X.ef]
    split_ifs <;> simp
  have hze : ∀ a, (VS D).hT (X.zu u) (X.eX a) = 0 := fun a => by
    rw [hs, (X.zu_orth u a).1, star_zero]
  have hzf : ∀ a, (VS D).hT (X.zu u) (X.fY a) = 0 := fun a => by
    rw [hs, (X.zu_orth u a).2, star_zero]

  refine ⟨∑ a, (VS D).hT (X.fY a) v • X.eX a + ∑ a, (VS D).hT (X.eX a) v • X.fY a +
      ((VS D).hT (X.zu u) v / (VS D).hT (X.zu u) (X.zu u)) • X.zu u, ?_, ?_⟩
  · refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl ⟨a, rfl⟩)))
    · exact Submodule.sum_mem _ fun a _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inr ⟨a, rfl⟩)))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr rfl))
  · have key : ∀ x ∈ Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u},
        (VS D).hT x (v - (∑ a, (VS D).hT (X.fY a) v • X.eX a + ∑ a, (VS D).hT (X.eX a) v • X.fY a +
          ((VS D).hT (X.zu u) v / (VS D).hT (X.zu u) (X.zu u)) • X.zu u)) = 0 := by
      intro x hx
      rcases hx with (⟨b, rfl⟩ | ⟨b, rfl⟩) | hz
      · simp [map_sub, map_add, map_sum, map_smul, smul_eq_mul, X.ee, X.ef, (X.zu_orth u b).1,
          mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
      · simp [map_sub, map_add, map_sum, map_smul, smul_eq_mul, X.ff, hfe, (X.zu_orth u b).2,
          mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        simp [map_sub, map_add, map_sum, map_smul, smul_eq_mul, hze, hzf, hzz]
    simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact key y hy
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, LinearMap.add_apply, hy, hz, add_zero]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fmat_one' : X.B.I.fmat 1 = 1 := by
  rfl

/- English proof (translation)
Establish `hdec` using `fun v => decomp X u v`. Use `set U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u})`. Use `set W := orth (VS D) U`. Establish `hUmap : U.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = U` using `map_eq_of_iff fun w => by`. Prove the components needed by the constructor for the conclusion.

Introduce `hw`. Establish `e : δ w = w` using `δ.injective (hUfix _ hw)`. Rewrite using `[← e]`. Conclude with `hw`. Introduce `hw`.

Rewrite using `[hUfix w hw]`. Conclude with `hw`. Establish `hWmap : W.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = W`. Rewrite using `[orth_map_bl hδiso U, hUmap]`. Establish `hX : (⊥ : Submodule D.host.E (VS D).V).map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = ⊥` using `Submodule.map_bot _`.

Establish `hR : ∀ x ∈ W, ∀ y ∈ (⊥ : Submodule D.host.E (VS D).V), (VS D).hT x y = 0`. Introduce `x _ y hy`. Rewrite using `[(Submodule.mem_bot _).1 hy, map_zero]`. Establish `hLb : ∀ x ∈ (⊥ : Submodule D.host.E (VS D).V), ∀ y ∈ W, (VS D).hT x y = 0`. Introduce `x hx y _`.

Rewrite using `[(Submodule.mem_bot _).1 hx, map_zero, LinearMap.zero_apply]`. Establish `hpos : ∀ w ∈ W, w ∉ (⊥ : Submodule D.host.E (VS D).V) → 0 < Algebra.trace ℚ D.host.E ((VS D).hT w w)`. Introduce `w hw hw0`. Establish `hw0' : w ≠ 0` using `fun h0 => hw0 (by rw [h0]; exact Submodule.zero_mem _)`. Establish `hXp : (X.Fu u).Xplus ≤ U`.

Unfold `FlagG.Xplus FlagG.X`. Rewrite using `[X.Fu_e u, X.flagZVector u]`. Use `sup_le (Submodule.span_mono ?_) (Submodule.span_mono ?_)` and prove the remaining obligations. Conclude with `fun x hx => Or.inl (Or.inl hx)`. Conclude with `fun x hx => Or.inr hx`.

Use `posW_holds D (D.mem u).A.T (D.mem u).A.T_prime.pos (X.Fu u) w (orth_anti hXp hw) ?_` and prove the remaining obligations. Introduce `hwX`. Apply `hw0'` to reduce the goal to its premises. Unfold `FlagG.X at hwX`. Rewrite `hwX` using `[X.Fu_e u]`.

Take `⟨cf, hcf⟩` from `(Submodule.mem_span_range_iff_exists_fun D.host.E).1 hwX`. Establish `hc0 : ∀ b, cf b = 0`. Introduce `b`. Establish `h1` using `(mem_orth_iff_bl.1 hw) (X.fY b) (Submodule.subset_span (Or.inl (Or.inr ⟨b, rfl⟩)))`. Rewrite `h1` using `[← hcf, map_sum]`.

Simplify using `only [map_smul, smul_eq_mul, hT_f_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1`. Conclude with `h1`. Rewrite using `[← hcf]`. Simplify using `[hc0]`. Use `haveI := hΛlat`.

Use `set Q := qEquiv δ W ⊥ hWmap hX with hQ`. Establish `hlat` using `qLat_isLattice Λ W ⊥`. Establish `hiso : Q ∈ Formalism.HermitianLatticesTheory.isom (qForm (VS D).hT W ⊥ hR hLb)`. Establish `: ∀ a b, qForm (VS D).hT W ⊥ hR hLb (Q a) (Q b) = qForm (VS D).hT W ⊥ hR hLb a b`. Introduce `a b`.

Proceed by induction on `a using Submodule.Quotient.induction_on with | H a => ?_`. Proceed by induction on `b using Submodule.Quotient.induction_on with | H b => ?_`. Rewrite using `[hQ, qEquiv_mk, qEquiv_mk, qForm_mk, qForm_mk]`. Conclude with `hδiso a b`. Conclude with `this`.

Establish `hpq : ∀ q : QW W ⊥, q ≠ 0 → 0 < Algebra.trace ℚ D.host.E (qForm (VS D).hT W ⊥ hR hLb q q)`. Introduce `q hq`. Proceed by induction on `q using Submodule.Quotient.induction_on with | H w => ?_`. Rewrite using `[qForm_mk]`. Use `hpos w w.2 ?_` and prove the remaining obligations.

Introduce `hwX`. Apply `hq` to reduce the goal to its premises. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `hwX`. Establish `haut : Q ∈ Formalism.L2.Col.autLat (qLat Λ W ⊥)`.

Establish `: Formalism.HermitianLatticesTheory.gmap Q (qLat Λ W ⊥) = qLat Λ W ⊥`. Use extensionality with `n`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩`. Take `⟨w, hwΛ, rfl⟩` from `mem_qLat.1 hm`.

Use `mem_qLat.2 ⟨⟨δ w, (mem_of_map_eq hWmap _).2 w.2⟩, (hδΛ w).2 hwΛ, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression. Introduce `hn`. Take `⟨w, hwΛ, rfl⟩` from `mem_qLat.1 hn`. Establish `h1 : δ (δ.symm w) ∈ W` using `by simpa using w.2`.

Establish `h2 : δ (δ.symm w) ∈ Λ` using `by simpa using hwΛ`. Use `⟨Submodule.Quotient.mk ⟨δ.symm w, (mem_of_map_eq hWmap _).1 h1⟩, mem_qLat.2 ⟨_, (hδΛ _).1 h2, rfl⟩, ?_⟩` and prove the remaining obligations. Use `show Q _ = _`. Rewrite using `[hQ, qEquiv_mk]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules. Conclude with `this`. Establish `hQfin : IsOfFinOrder Q` using `Formalism.L2.Col.isOfFinOrder_of_isom (qForm (VS D).hT W ⊥ hR hLb) (qForm_isSymm (VS D).hT (VS D).herm W ⊥ hR hLb) hpq hlat hiso haut`. Take `⟨m, hm, hQm⟩` from `(isOfFinOrder_iff_pow_eq_one).1 hQfin`.

Establish `hpowQ : ∀ j : ℕ, ∀ w : W, ∃ hw' : (δ ^ j) (w : (VS D).V) ∈ W, (Q ^ j) (Submodule.Quotient.mk w) = Submodule.Quotient.mk ⟨(δ ^ j) (w : (VS D).V), hw'⟩`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro w; exact ⟨by simpa using w.2, by rw [pow_zero]; rfl⟩`. Consider the case `succ j ih`.

Introduce `w`. Establish `hδw : δ (w : (VS D).V) ∈ W` using `(mem_of_map_eq hWmap _).2 w.2`. Take `⟨hw', e⟩` from `ih ⟨δ w, hδw⟩`. Use `⟨by rw [pow_succ, LinearEquiv.mul_apply]; exact hw', ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ, LinearEquiv.mul_apply, hQ, qEquiv_mk, ← hQ, e]`.

Use `congr 2`. Establish `hWm : ∀ w ∈ W, (δ ^ m) w = w`. Introduce `w hw`. Take `⟨hw', e⟩` from `hpowQ m ⟨w, hw⟩`. Rewrite `e` using `[hQm, LinearEquiv.coe_one, id, Submodule.Quotient.eq]`.

Establish `: (w - (δ ^ m) w : (VS D).V) ∈ (⊥ : Submodule D.host.E (VS D).V)` using `e`. Rewrite `this` using `[Submodule.mem_bot, sub_eq_zero]`. Conclude with `this.symm`. Establish `hUm : ∀ j : ℕ, ∀ s ∈ U, (δ ^ j) s = s`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => intro s _`. Rewrite using `[pow_zero]`. Both sides reduce to the same expression. Consider the case `succ j ih => intro s hs`.

Rewrite using `[pow_succ, LinearEquiv.mul_apply, hUfix s hs, ih s hs]`. Use `⟨m, hm, LinearEquiv.ext fun v => ?_⟩` and prove the remaining obligations. Take `⟨s, hs, hws⟩` from `hdec v`. Establish `e : v = (v - s) + s` using `by abel`. Rewrite using `[LinearEquiv.coe_one, id, e, map_add, hWm _ hws, hUm m s hs]`.
-/
theorem delta_finOrd (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hδiso : δ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (hUfix : ∀ w ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}), δ w = w)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛlat : Submodule.IsLattice D.host.E Λ)
    (hδΛ : ∀ v, δ v ∈ Λ ↔ v ∈ Λ) : ∃ m : ℕ, 0 < m ∧ δ ^ m = 1 := by
  have hdec := fun v => decomp X u v
  set U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u})
  set W := orth (VS D) U
  have hUmap : U.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = U := map_eq_of_iff fun w => by
    constructor
    · intro hw
      have e : δ w = w := δ.injective (hUfix _ hw)
      rw [← e]; exact hw
    · intro hw; rw [hUfix w hw]; exact hw
  have hWmap : W.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = W := by
    rw [orth_map_bl hδiso U, hUmap]
  have hX : (⊥ : Submodule D.host.E (VS D).V).map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = ⊥ := Submodule.map_bot _
  have hR : ∀ x ∈ W, ∀ y ∈ (⊥ : Submodule D.host.E (VS D).V), (VS D).hT x y = 0 := by
    intro x _ y hy; rw [(Submodule.mem_bot _).1 hy, map_zero]
  have hLb : ∀ x ∈ (⊥ : Submodule D.host.E (VS D).V), ∀ y ∈ W, (VS D).hT x y = 0 := by
    intro x hx y _; rw [(Submodule.mem_bot _).1 hx, map_zero, LinearMap.zero_apply]
  have hpos : ∀ w ∈ W, w ∉ (⊥ : Submodule D.host.E (VS D).V) →
      0 < Algebra.trace ℚ D.host.E ((VS D).hT w w) := by
    intro w hw hw0
    have hw0' : w ≠ 0 := fun h0 => hw0 (by rw [h0]; exact Submodule.zero_mem _)
    have hXp : (X.Fu u).Xplus ≤ U := by
      unfold FlagG.Xplus FlagG.X
      rw [X.Fu_e u, X.flagZVector u]
      refine sup_le (Submodule.span_mono ?_) (Submodule.span_mono ?_)
      · exact fun x hx => Or.inl (Or.inl hx)
      · exact fun x hx => Or.inr hx
    refine posW_holds D (D.mem u).A.T (D.mem u).A.T_prime.pos (X.Fu u) w (orth_anti hXp hw) ?_
    intro hwX
    apply hw0'
    unfold FlagG.X at hwX
    rw [X.Fu_e u] at hwX
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hwX
    have hc0 : ∀ b, cf b = 0 := by
      intro b
      have h1 := (mem_orth_iff_bl.1 hw) (X.fY b) (Submodule.subset_span (Or.inl (Or.inr ⟨b, rfl⟩)))
      rw [← hcf, map_sum] at h1
      simp only [map_smul, smul_eq_mul, hT_f_e, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h1
      exact h1
    rw [← hcf]
    simp [hc0]
  haveI := hΛlat
  set Q := qEquiv δ W ⊥ hWmap hX with hQ
  have hlat := qLat_isLattice Λ W ⊥
  have hiso : Q ∈ Formalism.HermitianLatticesTheory.isom (qForm (VS D).hT W ⊥ hR hLb) := by
    have : ∀ a b, qForm (VS D).hT W ⊥ hR hLb (Q a) (Q b) = qForm (VS D).hT W ⊥ hR hLb a b := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | H a => ?_
      induction b using Submodule.Quotient.induction_on with | H b => ?_
      rw [hQ, qEquiv_mk, qEquiv_mk, qForm_mk, qForm_mk]
      exact hδiso a b
    exact this
  have hpq : ∀ q : QW W ⊥, q ≠ 0 → 0 < Algebra.trace ℚ D.host.E (qForm (VS D).hT W ⊥ hR hLb q q) := by
    intro q hq
    induction q using Submodule.Quotient.induction_on with | H w => ?_
    rw [qForm_mk]
    refine hpos w w.2 ?_
    intro hwX
    apply hq
    rw [Submodule.Quotient.mk_eq_zero]
    exact hwX
  have haut : Q ∈ Formalism.L2.Col.autLat (qLat Λ W ⊥) := by
    have : Formalism.HermitianLatticesTheory.gmap Q (qLat Λ W ⊥) = qLat Λ W ⊥ := by
      ext n
      constructor
      · rintro ⟨m, hm, rfl⟩
        obtain ⟨w, hwΛ, rfl⟩ := mem_qLat.1 hm
        refine mem_qLat.2 ⟨⟨δ w, (mem_of_map_eq hWmap _).2 w.2⟩, (hδΛ w).2 hwΛ, ?_⟩
        rfl
      · intro hn
        obtain ⟨w, hwΛ, rfl⟩ := mem_qLat.1 hn
        have h1 : δ (δ.symm w) ∈ W := by simpa using w.2
        have h2 : δ (δ.symm w) ∈ Λ := by simpa using hwΛ
        refine ⟨Submodule.Quotient.mk ⟨δ.symm w, (mem_of_map_eq hWmap _).1 h1⟩,
          mem_qLat.2 ⟨_, (hδΛ _).1 h2, rfl⟩, ?_⟩
        show Q _ = _
        rw [hQ, qEquiv_mk]
        congr 1
        apply Subtype.ext
        simp
    exact this
  have hQfin : IsOfFinOrder Q :=
    Formalism.L2.Col.isOfFinOrder_of_isom (qForm (VS D).hT W ⊥ hR hLb) (qForm_isSymm (VS D).hT (VS D).herm W ⊥ hR hLb)
      hpq hlat hiso haut
  obtain ⟨m, hm, hQm⟩ := (isOfFinOrder_iff_pow_eq_one).1 hQfin
  have hpowQ : ∀ j : ℕ, ∀ w : W, ∃ hw' : (δ ^ j) (w : (VS D).V) ∈ W,
      (Q ^ j) (Submodule.Quotient.mk w) = Submodule.Quotient.mk ⟨(δ ^ j) (w : (VS D).V), hw'⟩ := by
    intro j
    induction j with
    | zero => intro w; exact ⟨by simpa using w.2, by rw [pow_zero]; rfl⟩
    | succ j ih =>
      intro w
      have hδw : δ (w : (VS D).V) ∈ W := (mem_of_map_eq hWmap _).2 w.2
      obtain ⟨hw', e⟩ := ih ⟨δ w, hδw⟩
      refine ⟨by rw [pow_succ, LinearEquiv.mul_apply]; exact hw', ?_⟩
      rw [pow_succ, LinearEquiv.mul_apply, hQ, qEquiv_mk, ← hQ, e]
      congr 2
  have hWm : ∀ w ∈ W, (δ ^ m) w = w := by
    intro w hw
    obtain ⟨hw', e⟩ := hpowQ m ⟨w, hw⟩
    rw [hQm, LinearEquiv.coe_one, id, Submodule.Quotient.eq] at e
    have : (w - (δ ^ m) w : (VS D).V) ∈ (⊥ : Submodule D.host.E (VS D).V) := e
    rw [Submodule.mem_bot, sub_eq_zero] at this
    exact this.symm
  have hUm : ∀ j : ℕ, ∀ s ∈ U, (δ ^ j) s = s := by
    intro j
    induction j with
    | zero => intro s _; rw [pow_zero]; rfl
    | succ j ih => intro s hs; rw [pow_succ, LinearEquiv.mul_apply, hUfix s hs, ih s hs]
  refine ⟨m, hm, LinearEquiv.ext fun v => ?_⟩
  obtain ⟨s, hs, hws⟩ := hdec v
  have e : v = (v - s) + s := by abel
  rw [LinearEquiv.coe_one, id, e, map_add, hWm _ hws, hUm m s hs]

/- English proof (translation)
Establish `hk : ∀ k : ℕ, ∀ y, incl X.B.I (X.crd ((δ ^ k) y)) = X.B.I.fmat (γ ^ k).2 *ᵥ incl X.B.I (X.crd y)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `y`.

Rewrite using `[pow_zero, pow_zero, Prod.snd_one, fmat_one', Matrix.one_mulVec]`. Apply the tactic sequence `all_goals first | rfl | simp`. Consider the case `succ k ih`. Introduce `y`. Establish `e1 : (δ ^ (k + 1)) y = (δ ^ k) (δ y)`.

Rewrite using `[pow_succ]`. Both sides reduce to the same expression. Establish `e2 : X.B.I.fmat (γ ^ (k + 1)).2 = X.B.I.fmat (γ ^ k).2 * X.B.I.fmat γ.2`. Rewrite using `[pow_succ, Prod.snd_mul]`. Apply the tactic sequence `first | rfl | simp`.

Rewrite using `[e1, ih, hincl, e2, Matrix.mulVec_mulVec]`. Establish `hfix : ∀ y, X.B.I.fmat (γ ^ m).2 *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd y)`. Introduce `y`. Rewrite using `[← hk m y, hδm]`. Apply the tactic sequence `all_goals rfl`.

Establish `h2 : (γ ^ m).2 = 1` using `fmat_eq_one_of_fix X (γ ^ m).2 hfix`. Conclude with `gf_eq_one_of_snd X (γ ^ m) (pow_mem hGF m) h2`.
-/
theorem gam_pow_eq_one (γ : X.B.I.GA) (hGF : γ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)
    (δ : (VS D).V ≃ₗ[D.host.E] (VS D).V)
    (hincl : ∀ y, incl X.B.I (X.crd (δ y)) = X.B.I.fmat γ.2 *ᵥ incl X.B.I (X.crd y))
    (m : ℕ) (hδm : δ ^ m = 1) : γ ^ m = 1 := by
  have hk : ∀ k : ℕ, ∀ y, incl X.B.I (X.crd ((δ ^ k) y)) =
      X.B.I.fmat (γ ^ k).2 *ᵥ incl X.B.I (X.crd y) := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [pow_zero, pow_zero, Prod.snd_one, fmat_one', Matrix.one_mulVec]
      all_goals first | rfl | simp
    | succ k ih =>
      intro y
      have e1 : (δ ^ (k + 1)) y = (δ ^ k) (δ y) := by
        rw [pow_succ]
        rfl
      have e2 : X.B.I.fmat (γ ^ (k + 1)).2 = X.B.I.fmat (γ ^ k).2 * X.B.I.fmat γ.2 := by
        rw [pow_succ, Prod.snd_mul]
        first | rfl | simp
      rw [e1, ih, hincl, e2, Matrix.mulVec_mulVec]
  have hfix : ∀ y, X.B.I.fmat (γ ^ m).2 *ᵥ incl X.B.I (X.crd y) = incl X.B.I (X.crd y) := by
    intro y
    rw [← hk m y, hδm]
    all_goals rfl
  have h2 : (γ ^ m).2 = 1 := fmat_eq_one_of_fix X (γ ^ m).2 hfix
  exact gf_eq_one_of_snd X (γ ^ m) (pow_mem hGF m) h2

/- English proof (translation)
Introduce `h γ hγ`. Establish `hGF : (γ : X.B.I.GA) ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I` using `(Subgroup.mem_inf.1 γ.2).1`. Establish `hH : (γ : X.B.I.GA).2 ∈ Hfin X u` using `(Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).2`. Establish `hGF'` using `hGF`. Take `⟨γ0, hγ0U, -, hγ0f⟩` from `hGF'`.

Establish `hincl : ∀ y, incl X.B.I (X.crd (matEC X γ0 y)) = X.B.I.fmat (γ : X.B.I.GA).2 *ᵥ incl X.B.I (X.crd y)`. Introduce `y`. Rewrite using `[hγ0f]`. Conclude with `matE_inclC X γ0 y`. Establish `hinj : ∀ a b : (VS D).V, incl X.B.I (X.crd a) = incl X.B.I (X.crd b) → a = b`.

Introduce `a b hab`. Apply `X.bas.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Establish `hi` using `congrFun hab i`. Simplify using `only [Formalism.L2.SG.HidaSetting.incl] at hi`.

Establish `h2` using `inclInjC X hi`. Simplify using `only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf] at h2`. Conclude with `X.ιE.symm.injective h2`. Establish `hfixS : ∀ w ∈ Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}, matEC X γ0 w = w`. Introduce `w hw`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[hincl]`. Establish `hw' : X.crd w ∈ fixSet X u`. Break down `hw with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz` into its components or cases. Conclude with `Or.inl (Or.inl ⟨a, rfl⟩)`.

Conclude with `Or.inl (Or.inr ⟨a, rfl⟩)`. Rewrite `hz` using `[Set.mem_singleton_iff]`. Substitute `hz` using the available equality. Conclude with `Or.inr rfl`. Conclude with `(show ∀ y ∈ fixSet X u, X.B.I.fmat (γ : X.B.I.GA).2 *ᵥ incl X.B.I y = incl X.B.I y from hH) _ hw'`.

Establish `hUfix : ∀ w ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}), matEC X γ0 w = w`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact hfixS x hx`. Consider the case `zero => exact map_zero _`.

Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`. Consider the case `smul c x _ hx => rw [map_smul, hx]`. Take `⟨Λ, hΛ, hΛlat⟩` from `hL h`. Establish `hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * (γ : X.B.I.GA).2 * ((h : X.B.I.Gf) * X.xu u) ∈ X.K2`. Establish `e : ((h : X.B.I.Gf) * X.xu u)⁻¹ * (γ : X.B.I.GA).2 * ((h : X.B.I.Gf) * X.xu u) = (X.xu u)⁻¹ * ((h⁻¹ * iotaF X u γ * h : Hfin X u) : X.B.I.Gf) * X.xu u`.

Establish `hi : ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2` using `rfl`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, hi]`. Use `group`. Rewrite using `[e]`. Conclude with `hγ`.

Establish `hkK : ∀ x, x ∈ X.B.I.Lf ↔ X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * (γ : X.B.I.GA).2 * ((h : X.B.I.Gf) * X.xu u)) *ᵥ x ∈ X.B.I.Lf` using `(show _ ∈ X.B.I.Kset ∧ _ from hk).1`. Establish `hmemΛ : ∀ v, v ∈ Λ ↔ X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd v) ∈ X.B.I.Lf`. Introduce `v`. Rewrite using `[← SetLike.mem_coe, hΛ]`. Apply the tactic sequence `all_goals exact Iff.rfl`.

Establish `hfm : X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ * X.B.I.fmat (γ : X.B.I.GA).2 = X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * (γ : X.B.I.GA).2 * ((h : X.B.I.Gf) * X.xu u)) * X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹`. Apply the tactic sequence `have hmul : ∀ a b : X.B.I.Gf, X.B.I.fmat (a * b) = X.B.I.fmat a * X.B.I.fmat b := fun a b => by first | rfl | simp`. Rewrite using `[← hmul, ← hmul]`. Use `congr 1`. Use `group`.

Establish `hδΛ : ∀ v, matEC X γ0 v ∈ Λ ↔ v ∈ Λ`. Introduce `v`. Rewrite using `[hmemΛ, hmemΛ, hincl, Matrix.mulVec_mulVec, hfm, ← Matrix.mulVec_mulVec]`. Conclude with `(hkK _).symm`. Take `⟨m, hm, hδm⟩` from `delta_finOrd X u (matEC X γ0) (matE_isomC X γ0 hγ0U) hUfix Λ hΛlat hδΛ`.

Establish `hγm : (γ : X.B.I.GA) ^ m = 1` using `gam_pow_eq_one X γ hGF (matEC X γ0) hincl m hδm`. Conclude with `isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, Subtype.ext (by simpa using hγm)⟩`.
-/
theorem gamFinKu_of (hK : X.LevelSubgroupCharacter) (hL : LatOfLattice X u) : GamFinKu X u hK := by
  intro h γ hγ
  have hGF : (γ : X.B.I.GA) ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I := (Subgroup.mem_inf.1 γ.2).1
  have hH : (γ : X.B.I.GA).2 ∈ Hfin X u := (Subgroup.mem_prod.1 (Subgroup.mem_inf.1 γ.2).2).2
  have hGF' := hGF
  obtain ⟨γ0, hγ0U, -, hγ0f⟩ := hGF'

  have hincl : ∀ y, incl X.B.I (X.crd (matEC X γ0 y)) =
      X.B.I.fmat (γ : X.B.I.GA).2 *ᵥ incl X.B.I (X.crd y) := by
    intro y
    rw [hγ0f]
    exact matE_inclC X γ0 y
  have hinj : ∀ a b : (VS D).V, incl X.B.I (X.crd a) = incl X.B.I (X.crd b) → a = b := by
    intro a b hab
    apply X.bas.repr.injective
    ext i
    have hi := congrFun hab i
    simp only [Formalism.L2.SG.HidaSetting.incl] at hi
    have h2 := inclInjC X hi
    simp only [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf] at h2
    exact X.ιE.symm.injective h2

  have hfixS : ∀ w ∈ Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}, matEC X γ0 w = w := by
    intro w hw
    apply hinj
    rw [hincl]
    have hw' : X.crd w ∈ fixSet X u := by
      rcases hw with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hz
      · exact Or.inl (Or.inl ⟨a, rfl⟩)
      · exact Or.inl (Or.inr ⟨a, rfl⟩)
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        exact Or.inr rfl
    exact (show ∀ y ∈ fixSet X u, X.B.I.fmat (γ : X.B.I.GA).2 *ᵥ incl X.B.I y = incl X.B.I y from hH) _ hw'
  have hUfix : ∀ w ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}),
      matEC X γ0 w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx => exact hfixS x hx
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]

  obtain ⟨Λ, hΛ, hΛlat⟩ := hL h
  have hk : ((h : X.B.I.Gf) * X.xu u)⁻¹ * (γ : X.B.I.GA).2 * ((h : X.B.I.Gf) * X.xu u) ∈ X.K2 := by
    have e : ((h : X.B.I.Gf) * X.xu u)⁻¹ * (γ : X.B.I.GA).2 * ((h : X.B.I.Gf) * X.xu u)
        = (X.xu u)⁻¹ * ((h⁻¹ * iotaF X u γ * h : Hfin X u) : X.B.I.Gf) * X.xu u := by
      have hi : ((iotaF X u γ : Hfin X u) : X.B.I.Gf) = (γ : X.B.I.GA).2 := rfl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hi]
      group
    rw [e]
    exact hγ
  have hkK : ∀ x, x ∈ X.B.I.Lf ↔
      X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * (γ : X.B.I.GA).2 * ((h : X.B.I.Gf) * X.xu u)) *ᵥ x
        ∈ X.B.I.Lf :=
    (show _ ∈ X.B.I.Kset ∧ _ from hk).1
  have hmemΛ : ∀ v, v ∈ Λ ↔
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd v) ∈ X.B.I.Lf := by
    intro v
    rw [← SetLike.mem_coe, hΛ]
    all_goals exact Iff.rfl
  have hfm : X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ * X.B.I.fmat (γ : X.B.I.GA).2 =
      X.B.I.fmat (((h : X.B.I.Gf) * X.xu u)⁻¹ * (γ : X.B.I.GA).2 * ((h : X.B.I.Gf) * X.xu u)) *
        X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ := by
    have hmul : ∀ a b : X.B.I.Gf, X.B.I.fmat (a * b) = X.B.I.fmat a * X.B.I.fmat b :=
      fun a b => by first | rfl | simp
    rw [← hmul, ← hmul]
    congr 1
    group
  have hδΛ : ∀ v, matEC X γ0 v ∈ Λ ↔ v ∈ Λ := by
    intro v
    rw [hmemΛ, hmemΛ, hincl, Matrix.mulVec_mulVec, hfm, ← Matrix.mulVec_mulVec]
    exact (hkK _).symm

  obtain ⟨m, hm, hδm⟩ := delta_finOrd X u (matEC X γ0) (matE_isomC X γ0 hγ0U) hUfix Λ hΛlat hδΛ
  have hγm : (γ : X.B.I.GA) ^ m = 1 := gam_pow_eq_one X γ hGF (matEC X γ0) hincl m hδm
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, Subtype.ext (by simpa using hγm)⟩

/- English proof (translation)
Introduce `x γ hx`. Conclude with `hU x γ hx (gamFinKu_of X u hK hL x γ hx)`.
-/
theorem neatKu_of_gamUnipKu (hK : X.LevelSubgroupCharacter) (hL : LatOfLattice X u) (hU : GamUnipKu X u hK) : NeatKu X u hK := by
  intro x γ hx
  exact hU x γ hx (gamFinKu_of X u hK hL x γ hx)

end Formalism.L2.SG.PoincareInHH.Cut
