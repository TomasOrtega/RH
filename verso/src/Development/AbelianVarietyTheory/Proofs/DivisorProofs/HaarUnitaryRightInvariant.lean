import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLineStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLocallyCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.IwasawaKAvgInt

noncomputable section

namespace GlobalTheory.ArchPartUnimod

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare GlobalTheory.LocUnitaryUnimod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def projArch : AF F →ₐ[F] Ainf F := AlgHom.fst F (Ainf F) (Af F)

variable (F) in

def inclArch : Ainf F →ₗ[F] AF F := LinearMap.inl F (Ainf F) (Af F)

/- English proof (translation)
The claim follows from `Prod.ext rfl (mul_zero (0 : Af F)).symm`.
-/
theorem inclArch_mul (a b : Ainf F) : inclArch F (a * b) = inclArch F a * inclArch F b :=
  Prod.ext rfl (mul_zero (0 : Af F)).symm

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem projArch_inclArch (a : Ainf F) : projArch F (inclArch F a) = a := rfl

/- English proof (translation)
The claim follows from `Prod.ext (one_mul a.1).symm (zero_mul a.2).symm`.
-/
theorem inclArch_projArch (a : AF F) : inclArch F (projArch F a) = inclArch F 1 * a :=
  Prod.ext (one_mul a.1).symm (zero_mul a.2).symm

/- English proof (translation)
The claim follows from `continuous_fst`.
-/
theorem continuous_projArch : Continuous (projArch F) := continuous_fst

/- English proof (translation)
The claim follows from `continuous_id.prodMk continuous_const`.
-/
theorem continuous_inclArch : Continuous (inclArch F) := continuous_id.prodMk continuous_const

/- English proof (translation)
The claim follows from `(InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)`.
-/
theorem fst_eq_zero {u : AF F} (hu : evI F u = 0) : u.1 = 0 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)

omit [NumberField E] in
/- English proof (translation)
Introduce `u hu`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, smul_zero]`. Consider the case `tmul a x`. Establish `h : u * inclArch F a = 0` using `Prod.ext (show u.1 * a = 0 by rw [fst_eq_zero hu, zero_mul]) (show u.2 * 0 = 0 from mul_zero _)`.

Express the relevant statement in the definitionally equal form `(u * inclArch F a) ⊗ₜ[F] x = 0`. Rewrite using `[h, TensorProduct.zero_tmul]`. Consider the case `add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]`.
-/
theorem at_tens (y : Ainf F ⊗[F] E) : At (evI F) (tensNU (E := E) (inclArch F) inclArch_mul y : AE F E) := by
  intro u hu
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, smul_zero]
  | tmul a x =>
    have h : u * inclArch F a = 0 :=
      Prod.ext (show u.1 * a = 0 by rw [fst_eq_zero hu, zero_mul]) (show u.2 * 0 = 0 from mul_zero _)
    change (u * inclArch F a) ⊗ₜ[F] x = 0
    rw [h, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, smul_add, hx, hy, add_zero]

omit [NumberField E] in
/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero, map_zero, smul_zero]`. Consider the case `tmul a x => exact congrArg (· ⊗ₜ[F] x) (inclArch_projArch a)`. Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]`.
-/
theorem tens_proj (z : AE F E) :
    tensNU (E := E) (inclArch F) inclArch_mul (Algebra.TensorProduct.map (projArch F) (AlgHom.id F E) z) =
      inclArch F 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, smul_zero]
  | tmul a x => exact congrArg (· ⊗ₜ[F] x) (inclArch_projArch a)
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

omit [NumberField E] in
/- English proof (translation)
Establish `h` using `hz (1 - inclArch F 1) (by`. Establish `: (1 - inclArch F 1 : AF F).1 = 0` using `sub_self (1 : Ainf F)`. Conclude with `(congrArg (InfiniteAdeleRing.ringEquiv_mixedSpace F) this).trans (map_zero _))`. Rewrite `h` using `[sub_smul, one_smul, sub_eq_zero]`. Conclude with `h.symm`.
-/
theorem smul_of_at {z : AE F E} (hz : At (evI F) z) : inclArch F 1 • z = z := by
  have h := hz (1 - inclArch F 1) (by
    have : (1 - inclArch F 1 : AF F).1 = 0 := sub_self (1 : Ainf F)
    exact (congrArg (InfiniteAdeleRing.ringEquiv_mixedSpace F) this).trans (map_zero _))
  rw [sub_smul, one_smul, sub_eq_zero] at h
  exact h.symm

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

omit [NumberField E] in

/- English proof (translation)
Use `HA_ext σ J fun r s => ?_` and prove the remaining obligations. Rewrite using `[mat_extH, mat_mapH, tens_proj]`. Use `set x := (HA.mat (AF F) σ J g : Matrix (Fin n) (Fin n) (AE F E)) r s with hxdef`. Establish `hx : At (evI F) (x - (1 : Matrix (Fin n) (Fin n) (AE F E)) r s)` using `fun u hu => by`. Use `congrFun (congrFun (hg u hu) r) s` as an intermediate fact.

Simplify `this` using `[smul_sub]`. Establish `key` using `smul_of_at hx`. Establish `h1 : (tensNU (E` using `E) (inclArch F) inclArch_mul 1 : AE F E) = inclArch F 1 • (1 : AE F E) := by`. Rewrite using `[← tens_proj, map_one (Algebra.TensorProduct.map (projArch F) (AlgHom.id F E))]`. Rewrite using `[h1, sub_mul, one_mul, smul_mul_assoc, one_mul]`.

Rewrite `key` using `[smul_sub]`. Take the linear combination `key`.
-/
theorem extH_mapH {g : HA (AF F) σ J}
    (hg : At (evI F) ((HA.mat (AF F) σ J g : Matrix (Fin n) (Fin n) (AE F E)) - 1)) :
    extH σ J (inclArch F) inclArch_mul (mapH σ J (projArch F) g) = g := by
  refine HA_ext σ J fun r s => ?_
  rw [mat_extH, mat_mapH, tens_proj]
  set x := (HA.mat (AF F) σ J g : Matrix (Fin n) (Fin n) (AE F E)) r s with hxdef
  have hx : At (evI F) (x - (1 : Matrix (Fin n) (Fin n) (AE F E)) r s) := fun u hu => by
    have := congrFun (congrFun (hg u hu) r) s
    simpa [smul_sub] using this
  have key := smul_of_at hx
  have h1 : (tensNU (E := E) (inclArch F) inclArch_mul 1 : AE F E) = inclArch F 1 • (1 : AE F E) := by
    rw [← tens_proj, map_one (Algebra.TensorProduct.map (projArch F) (AlgHom.id F E))]
  rw [h1, sub_mul, one_mul, smul_mul_assoc, one_mul]
  rw [smul_sub] at key
  linear_combination key

omit [NumberField E] in

/- English proof (translation)
Introduce `u hu`. Use extensionality with `r s`. Rewrite using `[Matrix.smul_apply, Matrix.sub_apply, mat_extH, Matrix.zero_apply]`. Establish `h1` using `at_tens (E := E) 1 u hu`. Establish `h2` using `at_tens (E := E) ((HA.mat (Ainf F) σ J h).1 r s) u hu`.

Rewrite using `[sub_mul, one_mul, smul_sub, smul_add, smul_sub, ← smul_mul_assoc, h1, h2, zero_mul, sub_zero, add_zero, sub_self]`.
-/
theorem at_extH (h : HA (Ainf F) σ J) :
    At (evI F) ((HA.mat (AF F) σ J (extH σ J (inclArch F) inclArch_mul h) : Matrix (Fin n) (Fin n) (AE F E)) - 1) := by
  intro u hu
  ext r s
  rw [Matrix.smul_apply, Matrix.sub_apply, mat_extH, Matrix.zero_apply]
  have h1 := at_tens (E := E) 1 u hu
  have h2 := at_tens (E := E) ((HA.mat (Ainf F) σ J h).1 r s) u hu
  rw [sub_mul, one_mul, smul_sub, smul_add, smul_sub, ← smul_mul_assoc, h1, h2, zero_mul, sub_zero, add_zero, sub_self]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Conclude with `(continuous_mapH σ X.Jᵀ (projArch F) continuous_projArch).comp ((continuous_toHAe σ X.J).comp continuous_subtype_val)`.
-/
theorem continuous_archTo (X : Spc F E n) :
    Continuous fun g : UAtSub σ X (evI F) => mapH σ X.Jᵀ (projArch F) (toHAe σ X.J g.1) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact (continuous_mapH σ X.Jᵀ (projArch F) continuous_projArch).comp
    ((continuous_toHAe σ X.J).comp continuous_subtype_val)

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Conclude with `(continuous_toHAe_symm σ X.J).comp (continuous_extH σ X.Jᵀ (inclArch F) inclArch_mul continuous_inclArch)`.
-/
theorem continuous_archFrom (X : Spc F E n) :
    Continuous fun h : HA (Ainf F) σ X.Jᵀ => (toHAe σ X.J).symm (extH σ X.Jᵀ (inclArch F) inclArch_mul h) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact (continuous_toHAe_symm σ X.J).comp (continuous_extH σ X.Jᵀ (inclArch F) inclArch_mul continuous_inclArch)

/- English proof (translation)
Rewrite using `[mem_UAtSub]`. Express the relevant statement in the definitionally equal form `At (evI F) (mat ((toHAe σ X.J).symm (extH σ X.Jᵀ (inclArch F) inclArch_mul h)) - 1)`. Rewrite using `[mat_toHAe_symm]`. Conclude with `at_extH σ X.Jᵀ h`.
-/
theorem mem_archFrom (X : Spc F E n) (h : HA (Ainf F) σ X.Jᵀ) :
    (toHAe σ X.J).symm (extH σ X.Jᵀ (inclArch F) inclArch_mul h) ∈ UAtSub σ X (evI F) := by
  rw [mem_UAtSub]
  change At (evI F) (mat ((toHAe σ X.J).symm (extH σ X.Jᵀ (inclArch F) inclArch_mul h)) - 1)
  rw [mat_toHAe_symm]
  exact at_extH σ X.Jᵀ h

/- English proof (translation)
Establish `hg : At (evI F) ((HA.mat (AF F) σ X.Jᵀ (toHAe σ X.J g.1) : Matrix (Fin n) (Fin n) (AE F E)) - 1)`. Rewrite using `[mat_toHAe]`. Conclude with `g.2`. Rewrite using `[extH_mapH σ X.Jᵀ hg, MulEquiv.symm_apply_apply]`.
-/
theorem archFrom_archTo (X : Spc F E n) (g : UAtSub σ X (evI F)) :
    (toHAe σ X.J).symm (extH σ X.Jᵀ (inclArch F) inclArch_mul (mapH σ X.Jᵀ (projArch F) (toHAe σ X.J g.1))) = g.1 := by
  have hg : At (evI F) ((HA.mat (AF F) σ X.Jᵀ (toHAe σ X.J g.1) : Matrix (Fin n) (Fin n) (AE F E)) - 1) := by
    rw [mat_toHAe]
    exact g.2
  rw [extH_mapH σ X.Jᵀ hg, MulEquiv.symm_apply_apply]

def archEquiv (X : Spc F E n) : UAtSub σ X (evI F) ≃ₜ* HA (Ainf F) σ X.Jᵀ where
  toFun g := mapH σ X.Jᵀ (projArch F) (toHAe σ X.J g.1)
  invFun h := ⟨(toHAe σ X.J).symm (extH σ X.Jᵀ (inclArch F) inclArch_mul h), mem_archFrom σ X h⟩
  left_inv g := Subtype.ext (archFrom_archTo σ X g)
  right_inv h := by
    change mapH σ X.Jᵀ (projArch F) ((toHAe σ X.J) ((toHAe σ X.J).symm _)) = h
    rw [MulEquiv.apply_symm_apply]
    exact mapH_extH_self σ X.Jᵀ (projArch F) (inclArch F) inclArch_mul projArch_inclArch h
  map_mul' g g' := by
    change mapH σ X.Jᵀ (projArch F) (toHAe σ X.J (g.1 * g'.1)) = _
    rw [map_mul, map_mul]
  continuous_toFun := continuous_archTo σ X
  continuous_invFun := (continuous_archFrom σ X).subtype_mk _

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Use `haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _`. Use `haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩`. Use `haveI : IsTopologicalGroup (UA σ X.J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F X.J)))`. Establish `hJ : IsHermND σ X.Jᵀ` using `⟨fun i j => by simp [Matrix.transpose_apply, herm], by rwa [Matrix.det_transpose]⟩`.

Establish `hU` using `(GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite F E σ hcm n X.Jᵀ hJ).1`. Conclude with `GlobalTheory.ArchUnitaryUnimod.isUnimodularLC_of_equiv hU (archEquiv σ X).symm`.
-/
theorem isUnimodularLC_UAtSub_inf (hcm : IsCMExt F E σ) (X : Spc F E n) (herm : ∀ i j, σ (X.J j i) = X.J i j)
    (hdet : X.J.det ≠ 0) : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.IsUnimodularLC (UAtSub σ X (evI F)) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI : IsTopologicalGroup (UA σ X.J) := inferInstanceAs (IsTopologicalGroup (UG (cA σ) (incM F X.J)))
  have hJ : IsHermND σ X.Jᵀ := ⟨fun i j => by simp [Matrix.transpose_apply, herm], by rwa [Matrix.det_transpose]⟩
  have hU := (GlobalTheory.ArchUnitaryUnimod.unimodularOver_infinite F E σ hcm n X.Jᵀ hJ).1
  exact GlobalTheory.ArchUnitaryUnimod.isUnimodularLC_of_equiv hU (archEquiv σ X).symm

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n X r s hB hX μ hμ g`. Take `⟨-, -, -, -, -, -, hR⟩` from `isUnimodularLC_UAtSub_inf σ hB.cm X hX.herm (GlobalTheory.ThetaKInv.det_ne_zero_of_isHerm hX)`. Conclude with `(hR μ hμ).map_mul_right_eq_self g`.
-/
theorem haar_map_mul_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    ∀ μ : Measure (UAtSub σ X (evI F)), μ.IsHaarMeasure → ∀ g : UAtSub σ X (evI F), μ.map (· * g) = μ := by
  intro F E _ _ _ _ _ σ B n X r s hB hX μ hμ g
  obtain ⟨-, -, -, -, -, -, hR⟩ := isUnimodularLC_UAtSub_inf σ hB.cm X hX.herm
    (GlobalTheory.ThetaKInv.det_ne_zero_of_isHerm hX)
  exact (hR μ hμ).map_mul_right_eq_self g

end GlobalTheory.ArchPartUnimod

end
