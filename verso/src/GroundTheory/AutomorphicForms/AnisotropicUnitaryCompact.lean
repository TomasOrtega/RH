import Mathlib
import GroundTheory.AutomorphicForms.AnisotropicUnitaryHeight
set_option maxSynthPendingDepth 1

open Module Matrix TensorProduct Topology NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

noncomputable section

namespace Anisotropic

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Topology

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]

local notation "𝒩" => Fintype.card (ι × κ)

/- English proof (translation)
The claim follows from `(tensorCoordsHomeomorph R b).continuous`.
-/
theorem continuous_coords : Continuous (coords b R) :=
  (tensorCoordsHomeomorph R b).continuous

/- English proof (translation)
The claim follows from `(tensorCoordsHomeomorph R b).symm.continuous`.
-/
theorem continuous_coords_symm : Continuous (coords b R).symm :=
  (tensorCoordsHomeomorph R b).symm.continuous

/- English proof (translation)
Use `continuous_pi fun p => continuous_pi fun q => ?_` and prove the remaining obligations. Use `show Continuous fun M : Matrix ι ι (R ⊗[K] E) => coords b R (baseBasis b R ((Fintype.equivFin (ι × κ)).symm p).2 * M ((Fintype.equivFin (ι × κ)).symm p).1 ((Fintype.equivFin (ι × κ)).symm q).1) ((Fintype.equivFin (ι × κ)).symm q).2`. Conclude with `(continuous_apply _).comp ((continuous_coords b R).comp (continuous_const.mul (continuous_id.matrix_elem _ _)))`.
-/
theorem continuous_resHom :
    Continuous (resHom (ι := ι) b R : Matrix ι ι (R ⊗[K] E) → Matrix (Fin 𝒩) (Fin 𝒩) R) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  show Continuous fun M : Matrix ι ι (R ⊗[K] E) => coords b R
    (baseBasis b R ((Fintype.equivFin (ι × κ)).symm p).2 *
      M ((Fintype.equivFin (ι × κ)).symm p).1 ((Fintype.equivFin (ι × κ)).symm q).1)
        ((Fintype.equivFin (ι × κ)).symm q).2
  exact (continuous_apply _).comp ((continuous_coords b R).comp
    (continuous_const.mul (continuous_id.matrix_elem _ _)))

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(continuous_resHom b R).comp Units.continuous_coe_inv.matrix_transpose`. Conclude with `(continuous_resHom b R).comp Units.continuous_val.matrix_transpose`.
-/
theorem continuous_trHom : Continuous (trHom (ι := ι) b R) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_resHom b R).comp Units.continuous_coe_inv.matrix_transpose
  · exact (continuous_resHom b R).comp Units.continuous_val.matrix_transpose

def readoff (A : Matrix (Fin 𝒩) (Fin 𝒩) R) : Matrix ι ι (R ⊗[K] E) := fun i j =>
  (coords b R).symm fun l => ∑ k, coords b R 1 k *
    A (Fintype.equivFin (ι × κ) (i, k)) (Fintype.equivFin (ι × κ) (j, l))

/- English proof (translation)
Use extensionality with `i j`. Apply `(coords b R).injective` to reduce the goal to its premises. Rewrite using `[readoff, LinearEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `l`. Establish `h` using `congrFun (coords_mul b R 1 (M i j)) l`.

Rewrite `h` using `[one_mul]`. Rewrite using `[h]`. Simplify using `only [vecMul, dotProduct, resHom_apply, Equiv.symm_apply_apply, blockHom_apply]`.
-/
theorem readoff_resHom (M : Matrix ι ι (R ⊗[K] E)) : readoff b R (resHom b R M) = M := by
  ext i j
  apply (coords b R).injective
  rw [readoff, LinearEquiv.apply_symm_apply]
  funext l
  have h := congrFun (coords_mul b R 1 (M i j)) l
  rw [one_mul] at h
  rw [h]
  simp only [vecMul, dotProduct, resHom_apply, Equiv.symm_apply_apply, blockHom_apply]

/- English proof (translation)
Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Use `(continuous_coords_symm b R).comp (continuous_pi fun l => ?_)` and prove the remaining obligations. Conclude with `continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_id.matrix_elem _ _)`.
-/
theorem continuous_readoff : Continuous (readoff (ι := ι) b R) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  refine (continuous_coords_symm b R).comp (continuous_pi fun l => ?_)
  exact continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_id.matrix_elem _ _)

end Topology

section Star

variable {R : Type*} [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']

def cstar (X : Matrix ι ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E) := (X.map (conjBase K E R))ᵀ

/- English proof (translation)
Simplify using `only [cstar, Matrix.map_mul, transpose_mul]`.
-/
theorem cstar_mul (X Y : Matrix ι ι (R ⊗[K] E)) : cstar (X * Y) = cstar Y * cstar X := by
  simp only [cstar, Matrix.map_mul, transpose_mul]

/- English proof (translation)
Simplify using `[cstar]`.
-/
theorem cstar_one : cstar (1 : Matrix ι ι (R ⊗[K] E)) = 1 := by
  simp [cstar]

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := (baseMap f : R ⊗[K] E →ₐ[K] R' ⊗[K] E).toRingHom)`.
-/
theorem map_baseMap_mul (f : R →ₐ[K] R') (X Y : Matrix ι ι (R ⊗[K] E)) :
    (X * Y).map (baseMap f) = X.map (baseMap f) * Y.map (baseMap f) :=
  Matrix.map_mul (f := (baseMap f : R ⊗[K] E →ₐ[K] R' ⊗[K] E).toRingHom)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [cstar, transpose_apply, Matrix.map_apply, baseMap_eq_tensorMap, tensorMap_conjBase]`.
-/
theorem cstar_baseMap (f : R →ₐ[K] R') (X : Matrix ι ι (R ⊗[K] E)) :
    cstar (X.map (baseMap f)) = (cstar X).map (baseMap f) := by
  ext i j
  simp only [cstar, transpose_apply, Matrix.map_apply, baseMap_eq_tensorMap, tensorMap_conjBase]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [baseMatrix, Matrix.map_apply, baseMap_eq_tensorMap, tensorMap_includeRight]`.
-/
theorem baseMatrix_baseMap (f : R →ₐ[K] R') :
    (baseMatrix K H R).map (baseMap f) = baseMatrix K H R' := by
  ext i j
  simp only [baseMatrix, Matrix.map_apply, baseMap_eq_tensorMap, tensorMap_includeRight]

/- English proof (translation)
Rewrite using `[map_baseMap_mul, map_baseMap_mul, cstar_baseMap, baseMatrix_baseMap]`.
-/
theorem cstar_mul_baseMatrix_map (f : R →ₐ[K] R') (X : Matrix ι ι (R ⊗[K] E)) :
    (cstar X * baseMatrix K H R * X).map (baseMap f) =
      cstar (X.map (baseMap f)) * baseMatrix K H R' * X.map (baseMap f) := by
  rw [map_baseMap_mul, map_baseMap_mul, cstar_baseMap, baseMatrix_baseMap]

end Star

section Main

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

variable [NumberField K]

local notation "𝒩'" => Fintype.card (ι × Fin (Module.finrank K E))

/- English proof (translation)
Set `b` to `Module.finBasis K E`. Introduce `z z' h`. Apply `(coords b K).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Establish `h1` using `congrFun (congrArg (coords b 𝔸[K]) h) k`.

Rewrite `h1` using `[coords_baseMap, coords_baseMap]`. Conclude with `AdeleRing.algebraMap_injective (𝓞 K) K h1`.
-/
theorem baseMap_ofId_injective :
    Function.Injective (baseMap (Algebra.ofId K 𝔸[K]) : K ⊗[K] E → 𝔸[K] ⊗[K] E) := by
  let b := Module.finBasis K E
  intro z z' h
  apply (coords b K).injective
  funext k
  have h1 := congrFun (congrArg (coords b 𝔸[K]) h) k
  rw [coords_baseMap, coords_baseMap] at h1
  exact AdeleRing.algebraMap_injective (𝓞 K) K h1

/- English proof (translation)
Establish `hm' : cstar ((diagGL (Algebra.ofId K 𝔸[K]) m : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι _) * baseMatrix K H 𝔸[K] * (diagGL (Algebra.ofId K 𝔸[K]) m : Matrix ι ι _) = baseMatrix K H 𝔸[K]` using `hm`. Use `show cstar (m : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K * m = baseMatrix K H K`. Rewrite `hm'` using `[diagGL_val, ← cstar_mul_baseMatrix_map, ← baseMatrix_baseMap H (Algebra.ofId K 𝔸[K])]`. Conclude with `Matrix.map_injective baseMap_ofId_injective hm'`.
-/
theorem mem_unitaryPoints_of_diagGL {m : GL ι (K ⊗[K] E)}
    (hm : diagGL (Algebra.ofId K 𝔸[K]) m ∈ unitaryPoints K E H 𝔸[K]) : m ∈ unitaryPoints K E H K := by
  have hm' : cstar ((diagGL (Algebra.ofId K 𝔸[K]) m : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι _) *
      baseMatrix K H 𝔸[K] * (diagGL (Algebra.ofId K 𝔸[K]) m : Matrix ι ι _) =
      baseMatrix K H 𝔸[K] := hm
  show cstar (m : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K * m = baseMatrix K H K
  rw [diagGL_val, ← cstar_mul_baseMatrix_map, ← baseMatrix_baseMap H (Algebra.ofId K 𝔸[K])] at hm'
  exact Matrix.map_injective baseMap_ofId_injective hm'

/- English proof (translation)
Set `b` to `Module.finBasis K E`. Take `⟨C, hC, hred⟩` from `exists_isCompact_trHom H b hH haniso`. Use `set α := Algebra.ofId K 𝔸[K] with hα`. Use `set Hb := baseMatrix K H 𝔸[K] with hHb`. Set `Ψ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun x => cstar (x : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * x`.

Set `Φ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun g => Ψ g⁻¹`. Establish `hΨmul : ∀ x y, Ψ (x * y) = cstar (y : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ x * y`. Introduce `x y`. Simplify using `only [Ψ, Units.val_mul, cstar_mul, Matrix.mul_assoc]`. Establish `hΨone : Ψ 1 = Hb`.

Simplify using `[Ψ, cstar_one]`. Establish `hcancel : ∀ (z : GL ι (𝔸[K] ⊗[K] E)) (X : Matrix ι ι (𝔸[K] ⊗[K] E)), cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) * (cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * X * ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) * (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = X`. Introduce `z X`. Establish `h1 : cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) * cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1`. Rewrite using `[← cstar_mul, z.inv_mul, cstar_one]`.

Establish `h2 : ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1` using `z.inv_mul`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]`. Establish `hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ unitaryPoints K E H 𝔸[K]`.

Introduce `g g'`. Establish `e1 : Φ g = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ (g⁻¹ * g') * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))` using `by show Ψ g⁻¹ = _`. Rewrite using `[← hΨmul, mul_inv_cancel_right]`. Establish `e2 : Φ g' = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))` using `by show Ψ g'⁻¹ = _`. Rewrite using `[← hΨone, ← hΨmul, one_mul]`.

Rewrite using `[e1, e2]`. Prove the components needed by the constructor for the conclusion. Introduce `he`. Establish `h` using `congrArg (fun X => cstar (g' : Matrix ι ι (𝔸[K] ⊗[K] E)) * X * (g' : Matrix ι ι (𝔸[K] ⊗[K] E))) he`. Simplify using `only [hcancel] at h`.

Conclude with `h`. Introduce `hu`. Establish `h : Ψ (g⁻¹ * g') = Hb` using `hu`. Rewrite using `[h]`. Set `Γ : Subgroup (GL ι (𝔸[K] ⊗[K] E))` to `(diagGL (ι := ι) α).range`.

Set `C₂ : Set (GL ι (𝔸[K] ⊗[K] E))` to `{w | trHom b 𝔸[K] w ∈ C}`. Set `Ψ' : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun A => cstar (readoff b 𝔸[K] A)ᵀ * Hb * (readoff b 𝔸[K] A)ᵀ`. Establish `hΨ'c : Continuous Ψ'`. Establish `h1 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (readoff (ι` using `ι) b 𝔸[K] A)ᵀ := (continuous_readoff b 𝔸[K]).matrix_transpose`. Establish `h2 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => cstar (readoff (ι` using `ι) b 𝔸[K] A)ᵀ := by show Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (((readoff (ι := ι) b 𝔸[K] A)ᵀ).map (conjBase K E 𝔸[K]))ᵀ`.

Conclude with `(h1.matrix_map (continuous_conjBase 𝔸[K])).matrix_transpose`. Conclude with `(h2.matrix_mul continuous_const).matrix_mul h1`. Establish `hC₂ : ∀ w ∈ C₂, Φ w = Ψ' (trHom b 𝔸[K] w : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K])`. Introduce `w _`. Use `show Ψ w⁻¹ = _`.

Simplify using `only [Ψ, Ψ', trHom_val, readoff_resHom, transpose_transpose]`. Establish `hX : IsCompact (Ψ' '' (Units.val '' C))` using `(hC.image Units.continuous_val).image hΨ'c`. Set `ψ : Matrix ι ι (K ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun V => V.map (baseMap α)`. Establish `hΓ : ∀ M : GL ι (K ⊗[K] E), Φ (diagGL α M) = ψ (cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K * ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)))`. Introduce `M`.

Use `show Ψ (diagGL α M)⁻¹ = _`. Rewrite using `[← map_inv]`. Simplify using `only [Ψ, ψ, diagGL_val]`. Rewrite using `[cstar_mul_baseMatrix_map]`. Establish `hfinV : {V | ψ V ∈ Ψ' '' (Units.val '' C)}.Finite`.

Use `finite_of_isCompact_coords hX ψ (fun p : ι × ι × Fin (Module.finrank K E) => fun X => coords b 𝔸[K] (X p.1 p.2.1) p.2.2) (fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp (continuous_id.matrix_elem _ _))) (fun V p => coords b K (V p.1 p.2.1) p.2.2) ?_ ?_` and prove the remaining obligations. Introduce `V V' h`. Use extensionality with `i j`. Apply `(coords b K).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `k`.

Conclude with `congrFun h (i, j, k)`. Introduce `V p`. Simplify using `only [ψ, Matrix.map_apply, coords_baseMap]`. Both sides reduce to the same expression. Establish `hfin : (Φ '' C₂ ∩ Φ '' (Γ : Set (GL ι (𝔸[K] ⊗[K] E)))).Finite`.

Use `(hfinV.image ψ).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨w, hw, rfl⟩, _, ⟨M, rfl⟩, he⟩`. Use `⟨cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K * ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)), ?_, ?_⟩` and prove the remaining obligations. Use `show ψ _ ∈ Ψ' '' (Units.val '' C)`. Rewrite using `[← hΓ M, he, hC₂ w hw]`.

Conclude with `⟨_, ⟨_, hw, rfl⟩, rfl⟩`. Rewrite using `[← hΓ M, he]`. Take `⟨T, hTΓ, hT⟩` from `exists_finset_of_orbit Φ (unitaryPoints K E H 𝔸[K]) Γ hΦ C₂ hfin`. Set `C₃ : Set (GL (Fin 𝒩') 𝔸[K])` to `⋃ δ ∈ T, (fun c => (trHom b 𝔸[K] δ)⁻¹ * c) '' C`. Establish `hC₃ : IsCompact C₃` using `T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id)`.

Set `Ω : Set (unitaryPoints K E H 𝔸[K])` to `{v | trHom b 𝔸[K] (v : GL ι (𝔸[K] ⊗[K] E)) ∈ C₃}`. Use `⟨Ω, ?_, ?_⟩` and prove the remaining obligations. Establish `hΩcl : IsClosed Ω` using `hC₃.isClosed.preimage ((continuous_trHom b 𝔸[K]).comp continuous_subtype_val)`. Set `F : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → ι × ι × Fin (Module.finrank K E) → 𝔸[K]` to `fun A p => coords b 𝔸[K] ((readoff (ι := ι) b 𝔸[K] A)ᵀ p.1 p.2.1) p.2.2`. Establish `hFc : Continuous F` using `continuous_pi fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp (((continuous_readoff b 𝔸[K]).matrix_transpose).matrix_elem _ _))`.

Use `set D := (unitaryCoords H 𝔸[K] b) ⁻¹' (F '' (Units.val '' C₃)) with hD`. Establish `hDc : IsCompact D` using `(isClosedEmbedding_unitaryCoords H 𝔸[K] b hH).isCompact_preimage ((hC₃.image Units.continuous_val).image hFc)`. Establish `hsub : Ω ⊆ D⁻¹`. Introduce `v hv`. Use `show v⁻¹ ∈ D`.

Use `⟨_, ⟨_, hv, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Simplify using `only [F, trHom_val, readoff_resHom, transpose_transpose]`. Both sides reduce to the same expression. Conclude with `hDc.inv.of_isClosed_subset hΩcl hsub`.

Introduce `u`. Take `⟨M, hM⟩` from `hred u`. Take `⟨δ, hδT, hηδ, -⟩` from `hT u u.2 (diagGL α M) ⟨M, rfl⟩ ((diagGL α M)⁻¹ * (u : GL ι (𝔸[K] ⊗[K] E))) hM (by rw [mul_inv_cancel_left])`. Take `⟨m, rfl⟩` from `hTΓ δ hδT`. Rewrite `hηδ` using `[← map_mul]`.

Establish `hU` using `mem_unitaryPoints_of_diagGL H hηδ`. Use `⟨unitaryDiagonal K H ⟨M * m, hU⟩, ⟨_, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `e : ((unitaryDiagonal K H ⟨M * m, hU⟩ : unitaryPoints K E H 𝔸[K]) : GL ι (𝔸[K] ⊗[K] E)) = diagGL α (M * m)` using `Units.ext rfl`. Use `show trHom b 𝔸[K] (((unitaryDiagonal K H ⟨M * m, hU⟩)⁻¹ * u : unitaryPoints K E H 𝔸[K]) : GL ι (𝔸[K] ⊗[K] E)) ∈ C₃`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_inv, e]`.

Use `Set.mem_biUnion hδT ⟨_, hM, ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]`.
-/
theorem exists_isCompact_unitary (hH : IsUnit H.det)
    (haniso : ∀ ξ : ι → K ⊗[K] E, hermValue K H K ξ = 0 → ξ = 0) :
    ∃ Ω : Set (unitaryPoints K E H 𝔸[K]), IsCompact Ω ∧ ∀ u : unitaryPoints K E H 𝔸[K],
      ∃ θ ∈ (unitaryDiagonal K H).range, θ⁻¹ * u ∈ Ω := by
  classical
  let b := Module.finBasis K E
  obtain ⟨C, hC, hred⟩ := exists_isCompact_trHom H b hH haniso
  set α := Algebra.ofId K 𝔸[K] with hα
  set Hb := baseMatrix K H 𝔸[K] with hHb
  let Ψ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun x =>
    cstar (x : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * x
  let Φ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun g => Ψ g⁻¹
  have hΨmul : ∀ x y, Ψ (x * y) = cstar (y : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ x * y := by
    intro x y
    simp only [Ψ, Units.val_mul, cstar_mul, Matrix.mul_assoc]
  have hΨone : Ψ 1 = Hb := by
    simp [Ψ, cstar_one]
  have hcancel : ∀ (z : GL ι (𝔸[K] ⊗[K] E)) (X : Matrix ι ι (𝔸[K] ⊗[K] E)),
      cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        (cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * X *
          ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) *
        (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = X := by
    intro z X
    have h1 : cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1 := by
      rw [← cstar_mul, z.inv_mul, cstar_one]
    have h2 : ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1 := z.inv_mul
    calc _ = (cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
          cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) * X *
          (((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
            (z : Matrix ι ι (𝔸[K] ⊗[K] E))) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  have hΦ : ∀ g g', Φ g = Φ g' ↔ g⁻¹ * g' ∈ unitaryPoints K E H 𝔸[K] := by
    intro g g'
    have e1 : Φ g = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        Ψ (g⁻¹ * g') * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) := by
      show Ψ g⁻¹ = _
      rw [← hΨmul, mul_inv_cancel_right]
    have e2 : Φ g' = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        Hb * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) := by
      show Ψ g'⁻¹ = _
      rw [← hΨone, ← hΨmul, one_mul]
    rw [e1, e2]
    constructor
    · intro he
      have h := congrArg (fun X => cstar (g' : Matrix ι ι (𝔸[K] ⊗[K] E)) * X *
        (g' : Matrix ι ι (𝔸[K] ⊗[K] E))) he
      simp only [hcancel] at h
      exact h
    · intro hu
      have h : Ψ (g⁻¹ * g') = Hb := hu
      rw [h]
  let Γ : Subgroup (GL ι (𝔸[K] ⊗[K] E)) := (diagGL (ι := ι) α).range
  let C₂ : Set (GL ι (𝔸[K] ⊗[K] E)) := {w | trHom b 𝔸[K] w ∈ C}
  let Ψ' : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → Matrix ι ι (𝔸[K] ⊗[K] E) := fun A =>
    cstar (readoff b 𝔸[K] A)ᵀ * Hb * (readoff b 𝔸[K] A)ᵀ
  have hΨ'c : Continuous Ψ' := by
    have h1 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (readoff (ι := ι) b 𝔸[K] A)ᵀ :=
      (continuous_readoff b 𝔸[K]).matrix_transpose
    have h2 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] =>
        cstar (readoff (ι := ι) b 𝔸[K] A)ᵀ := by
      show Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] =>
        (((readoff (ι := ι) b 𝔸[K] A)ᵀ).map (conjBase K E 𝔸[K]))ᵀ
      exact (h1.matrix_map (continuous_conjBase 𝔸[K])).matrix_transpose
    exact (h2.matrix_mul continuous_const).matrix_mul h1
  have hC₂ : ∀ w ∈ C₂, Φ w = Ψ' (trHom b 𝔸[K] w : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K]) := by
    intro w _
    show Ψ w⁻¹ = _
    simp only [Ψ, Ψ', trHom_val, readoff_resHom, transpose_transpose]
  have hX : IsCompact (Ψ' '' (Units.val '' C)) := (hC.image Units.continuous_val).image hΨ'c
  let ψ : Matrix ι ι (K ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun V => V.map (baseMap α)
  have hΓ : ∀ M : GL ι (K ⊗[K] E), Φ (diagGL α M) =
      ψ (cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K *
        ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E))) := by
    intro M
    show Ψ (diagGL α M)⁻¹ = _
    rw [← map_inv]
    simp only [Ψ, ψ, diagGL_val]
    rw [cstar_mul_baseMatrix_map]
  have hfinV : {V | ψ V ∈ Ψ' '' (Units.val '' C)}.Finite := by
    refine finite_of_isCompact_coords hX ψ
      (fun p : ι × ι × Fin (Module.finrank K E) => fun X => coords b 𝔸[K] (X p.1 p.2.1) p.2.2)
      (fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp
        (continuous_id.matrix_elem _ _)))
      (fun V p => coords b K (V p.1 p.2.1) p.2.2) ?_ ?_
    · intro V V' h
      ext i j
      apply (coords b K).injective
      funext k
      exact congrFun h (i, j, k)
    · intro V p
      simp only [ψ, Matrix.map_apply, coords_baseMap]
      rfl
  have hfin : (Φ '' C₂ ∩ Φ '' (Γ : Set (GL ι (𝔸[K] ⊗[K] E)))).Finite := by
    refine (hfinV.image ψ).subset ?_
    rintro _ ⟨⟨w, hw, rfl⟩, _, ⟨M, rfl⟩, he⟩
    refine ⟨cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K *
        ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)), ?_, ?_⟩
    · show ψ _ ∈ Ψ' '' (Units.val '' C)
      rw [← hΓ M, he, hC₂ w hw]
      exact ⟨_, ⟨_, hw, rfl⟩, rfl⟩
    · rw [← hΓ M, he]
  obtain ⟨T, hTΓ, hT⟩ := exists_finset_of_orbit Φ (unitaryPoints K E H 𝔸[K]) Γ hΦ C₂ hfin
  let C₃ : Set (GL (Fin 𝒩') 𝔸[K]) := ⋃ δ ∈ T, (fun c => (trHom b 𝔸[K] δ)⁻¹ * c) '' C
  have hC₃ : IsCompact C₃ :=
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id)
  let Ω : Set (unitaryPoints K E H 𝔸[K]) := {v | trHom b 𝔸[K] (v : GL ι (𝔸[K] ⊗[K] E)) ∈ C₃}
  refine ⟨Ω, ?_, ?_⟩
  · have hΩcl : IsClosed Ω :=
      hC₃.isClosed.preimage ((continuous_trHom b 𝔸[K]).comp continuous_subtype_val)
    let F : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → ι × ι × Fin (Module.finrank K E) → 𝔸[K] :=
      fun A p =>
      coords b 𝔸[K] ((readoff (ι := ι) b 𝔸[K] A)ᵀ p.1 p.2.1) p.2.2
    have hFc : Continuous F := continuous_pi fun p => (continuous_apply _).comp
      ((continuous_coords b 𝔸[K]).comp
        (((continuous_readoff b 𝔸[K]).matrix_transpose).matrix_elem _ _))
    set D := (unitaryCoords H 𝔸[K] b) ⁻¹' (F '' (Units.val '' C₃)) with hD
    have hDc : IsCompact D := (isClosedEmbedding_unitaryCoords H 𝔸[K] b hH).isCompact_preimage
      ((hC₃.image Units.continuous_val).image hFc)
    have hsub : Ω ⊆ D⁻¹ := by
      intro v hv
      show v⁻¹ ∈ D
      refine ⟨_, ⟨_, hv, rfl⟩, ?_⟩
      funext p
      simp only [F, trHom_val, readoff_resHom, transpose_transpose]
      rfl
    exact hDc.inv.of_isClosed_subset hΩcl hsub
  · intro u
    obtain ⟨M, hM⟩ := hred u
    obtain ⟨δ, hδT, hηδ, -⟩ := hT u u.2 (diagGL α M) ⟨M, rfl⟩
      ((diagGL α M)⁻¹ * (u : GL ι (𝔸[K] ⊗[K] E))) hM (by rw [mul_inv_cancel_left])
    obtain ⟨m, rfl⟩ := hTΓ δ hδT
    rw [← map_mul] at hηδ
    have hU := mem_unitaryPoints_of_diagGL H hηδ
    refine ⟨unitaryDiagonal K H ⟨M * m, hU⟩, ⟨_, rfl⟩, ?_⟩
    have e : ((unitaryDiagonal K H ⟨M * m, hU⟩ : unitaryPoints K E H 𝔸[K]) :
        GL ι (𝔸[K] ⊗[K] E)) = diagGL α (M * m) := Units.ext rfl
    show trHom b 𝔸[K] (((unitaryDiagonal K H ⟨M * m, hU⟩)⁻¹ * u : unitaryPoints K E H 𝔸[K]) :
      GL ι (𝔸[K] ⊗[K] E)) ∈ C₃
    rw [Subgroup.coe_mul, Subgroup.coe_inv, e]
    refine Set.mem_biUnion hδT ⟨_, hM, ?_⟩
    simp only [map_mul, map_inv, _root_.mul_inv_rev, mul_assoc]

/- English proof (translation)
Take `⟨Ω, hΩ, hdec⟩` from `exists_isCompact_unitary H hH haniso`. Establish `himage : RightCosetSpace.mk (unitaryDiagonal K H).range '' Ω = Set.univ`. Use `Set.eq_univ_of_forall fun q => ?_` and prove the remaining obligations. Take `⟨u, rfl⟩` from `RightCosetSpace.mk_surjective _ q`. Take `⟨θ, hθ, hθu⟩` from `hdec u`.

Conclude with `⟨θ⁻¹ * u, hθu, RightCosetSpace.mk_eq_mk_iff.2 ⟨⟨θ⁻¹, inv_mem hθ⟩, rfl⟩⟩`. Conclude with `⟨by rw [← himage]; exact hΩ.image (RightCosetSpace.continuous_mk _)⟩`.
-/
theorem compactSpace_unitaryQuotient_of_anisotropic' (hH : IsUnit H.det)
    (haniso : ∀ ξ : ι → K ⊗[K] E, hermValue K H K ξ = 0 → ξ = 0) :
    CompactSpace (RightCosetSpace (unitaryDiagonal K H).range) := by
  obtain ⟨Ω, hΩ, hdec⟩ := exists_isCompact_unitary H hH haniso
  have himage : RightCosetSpace.mk (unitaryDiagonal K H).range '' Ω = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    obtain ⟨u, rfl⟩ := RightCosetSpace.mk_surjective _ q
    obtain ⟨θ, hθ, hθu⟩ := hdec u
    exact ⟨θ⁻¹ * u, hθu, RightCosetSpace.mk_eq_mk_iff.2 ⟨⟨θ⁻¹, inv_mem hθ⟩, rfl⟩⟩
  exact ⟨by rw [← himage]; exact hΩ.image (RightCosetSpace.continuous_mk _)⟩

end Main

end Anisotropic

end

end GroundTheory.Automorphic
