import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegMatAct
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace GenDegMatAct

section Subst

variable {J : Type} [Fintype J]

def linSubst (B : Matrix J J ℚ) : MvPolynomial J ℚ →ₐ[ℚ] MvPolynomial J ℚ :=
  aeval fun i => ∑ j, C (B i j) * X j

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `only [linSubst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Conclude with `Finset.sum_comm`.
-/
theorem linSubst_comp (B B' : Matrix J J ℚ) :
    (linSubst B).comp (linSubst B') = linSubst (B' * B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [linSubst, AlgHom.comp_apply, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[linSubst, Matrix.one_apply, apply_ite C, ite_mul]`.
-/
theorem linSubst_one [DecidableEq J] : linSubst (1 : Matrix J J ℚ) = AlgHom.id ℚ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [linSubst, Matrix.one_apply, apply_ite C, ite_mul]

/- English proof (translation)
Take `⟨B', h⟩` from `hB`. Apply the tactic sequence `refine ⟨B', ?_, ?_⟩ <;> rw [Matrix.ext_iff_mulVec] <;> intro v <;>`. Simplify using `[← Matrix.mulVec_mulVec, (h v).1, (h v).2]`.
-/
theorem exists_inv [DecidableEq J] {B : Matrix J J ℚ} (hB : IsInvMat B) : ∃ B' : Matrix J J ℚ, B * B' = 1 ∧ B' * B = 1 := by
  classical
  obtain ⟨B', h⟩ := hB
  refine ⟨B', ?_, ?_⟩ <;> rw [Matrix.ext_iff_mulVec] <;> intro v <;>
    simp [← Matrix.mulVec_mulVec, (h v).1, (h v).2]

def linEquiv [DecidableEq J] (B B' : Matrix J J ℚ) (h₁ : B * B' = 1) (h₂ : B' * B = 1) :
    MvPolynomial J ℚ ≃ₐ[ℚ] MvPolynomial J ℚ :=
  AlgEquiv.ofAlgHom (linSubst B) (linSubst B') (by rw [linSubst_comp, h₂, linSubst_one])
    (by rw [linSubst_comp, h₁, linSubst_one])

/- English proof (translation)
Establish `h` using `hf.aeval (fun i => ∑ j, C (B i j) * X j) (n := 1) fun i => IsHomogeneous.sum _ _ _ fun j _ => by`. Simplify using `using (isHomogeneous_C J (B i j)).mul (isHomogeneous_X ℚ j)`. Simplify `h` using `[linSubst]`.
-/
theorem isHomogeneous_linSubst (B : Matrix J J ℚ) {f : MvPolynomial J ℚ} {n : ℕ} (hf : f.IsHomogeneous n) :
    (linSubst B f).IsHomogeneous n := by
  have h := hf.aeval (fun i => ∑ j, C (B i j) * X j) (n := 1) fun i =>
    IsHomogeneous.sum _ _ _ fun j _ => by
      simpa using (isHomogeneous_C J (B i j)).mul (isHomogeneous_X ℚ j)
  simpa [linSubst] using h

end Subst

section Ideals

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

/- English proof (translation)
Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `i`. Simplify using `[coneMap, matAct, linSubst, Finset.sum_mul, mul_assoc, Polynomial.algebraMap_apply]`.
-/
theorem coneMap_matAct (B : Matrix J J ℚ) (x : J → Ω) :
    coneMap ℚ (matAct B x) = (coneMap ℚ x).comp (linSubst B) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [coneMap, matAct, linSubst, Finset.sum_mul, mul_assoc, Polynomial.algebraMap_apply]

/- English proof (translation)
Use extensionality with `f`. Simplify using `[coordIdeal, RingHom.mem_ker, coneMap_matAct]`.
-/
theorem coordIdeal_matAct (B : Matrix J J ℚ) (x : J → Ω) :
    coordIdeal ℚ (matAct B x) = (coordIdeal ℚ x).comap (linSubst B) := by
  ext f
  simp [coordIdeal, RingHom.mem_ker, coneMap_matAct]

omit [Fintype J] in

/- English proof (translation)
Establish `hring : ((coneMap ℚ x : MvPolynomial J ℚ →+* Polynomial Ω).comp (MvPolynomial.map (Int.castRingHom ℚ))) = (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[coneMap]`. Introduce `i`.

Simplify using `[coneMap]`. Establish `hker : coordIdeal ℤ x = (coordIdeal ℚ x).comap (MvPolynomial.map (Int.castRingHom ℚ))`. Use extensionality with `f`. Rewrite using `[Ideal.mem_comap]`. Simplify using `only [coordIdeal, RingHom.mem_ker]`.

Establish `h` using `RingHom.congr_fun hring f`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h`. Rewrite using `[h]`. Set `_` to `MvPolynomial.algebraMvPolynomial (σ := J) (R := ℤ) (S := ℚ)`. Establish `e : algebraMap (MvPolynomial J ℤ) (MvPolynomial J ℚ) = MvPolynomial.map (Int.castRingHom ℚ)`.

Rewrite using `[MvPolynomial.algebraMap_def, algebraMap_int_eq]`. Establish `h` using `IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := J))) (MvPolynomial J ℚ) (coordIdeal ℚ x)`. Rewrite `h` using `[e]`. Rewrite using `[hker]`. Conclude with `h`.
-/
theorem map_coordIdeal_int (x : J → Ω) :
    (coordIdeal ℤ x).map (MvPolynomial.map (Int.castRingHom ℚ)) = coordIdeal ℚ x := by
  have hring : ((coneMap ℚ x : MvPolynomial J ℚ →+* Polynomial Ω).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) = (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [coneMap]
    · intro i
      simp [coneMap]
  have hker : coordIdeal ℤ x = (coordIdeal ℚ x).comap (MvPolynomial.map (Int.castRingHom ℚ)) := by
    ext f
    rw [Ideal.mem_comap]
    simp only [coordIdeal, RingHom.mem_ker]
    have h := RingHom.congr_fun hring f
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe] at h
    rw [h]
  let _ := MvPolynomial.algebraMvPolynomial (σ := J) (R := ℤ) (S := ℚ)
  have e : algebraMap (MvPolynomial J ℤ) (MvPolynomial J ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  have h := IsLocalization.map_under ((nonZeroDivisors ℤ).map (C (σ := J))) (MvPolynomial J ℚ)
    (coordIdeal ℚ x)
  rw [e] at h
  rw [hker]
  exact h

end Ideals

section Hilbert

variable {κ : Type} [Fintype κ]

open GroundTheory.Heights₂.Heights.NumbersDVR

/- English proof (translation)
Establish `hdeg : ∀ d : Ix κ →₀ ℕ, ∑ i : κ, d ⟨(), i⟩ = Finsupp.weight 1 d`. Introduce `d`. Establish `h1 : d.degree = Finsupp.weight 1 d`. Rewrite using `[Finsupp.degree_eq_weight_one]`. Both sides reduce to the same expression.

Rewrite using `[← h1, Finsupp.degree_eq_sum, Fintype.sum_sigma]`. Conclude with `(Fintype.sum_unique (fun u : Unit => ∑ y : GlobalTheory κ u, d ⟨u, y⟩)).symm`. Establish `hw : ∀ d : Ix κ →₀ ℕ, Finsupp.weight (blockWeight (GlobalTheory κ)) d = fun _ => Finsupp.weight 1 d`. Introduce `d`. Use function extensionality and compare the values at `u`.

Consider the cases of `u`. Rewrite using `[← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]`. Simplify using `[blockWeight]`. Simplify using `only [IsHomogeneous, IsWeightedHomogeneous, hw]`. Prove the components needed by the constructor for the conclusion.

Introduce `h d hd`. Conclude with `congrFun (h hd) ()`. Introduce `h d hd`. Use function extensionality and compare the values at `u`. Conclude with `h hd`.
-/
theorem isWeightedHomogeneous_iff (f : MvPolynomial (Ix κ) ℚ) (m : Unit → ℕ) :
    IsWeightedHomogeneous (blockWeight (GlobalTheory κ)) f m ↔ f.IsHomogeneous (m ()) := by
  have hdeg : ∀ d : Ix κ →₀ ℕ, ∑ i : κ, d ⟨(), i⟩ = Finsupp.weight 1 d := by
    intro d
    have h1 : d.degree = Finsupp.weight 1 d := by
      rw [Finsupp.degree_eq_weight_one]
      rfl
    rw [← h1, Finsupp.degree_eq_sum, Fintype.sum_sigma]
    exact (Fintype.sum_unique (fun u : Unit => ∑ y : GlobalTheory κ u, d ⟨u, y⟩)).symm
  have hw : ∀ d : Ix κ →₀ ℕ, Finsupp.weight (blockWeight (GlobalTheory κ)) d = fun _ => Finsupp.weight 1 d := by
    intro d
    funext u
    cases u
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
    simp [blockWeight]
  simp only [IsHomogeneous, IsWeightedHomogeneous, hw]
  constructor
  · intro h d hd
    exact congrFun (h hd) ()
  · intro h d hd
    funext u
    exact h hd

/- English proof (translation)
Rewrite `hf`, the goal using `[mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_iff]`. Conclude with `isHomogeneous_linSubst B hf`.
-/
theorem mem_weighted_linSubst (B : Matrix (Ix κ) (Ix κ) ℚ) {m : Unit → ℕ} {f : MvPolynomial (Ix κ) ℚ}
    (hf : f ∈ weightedHomogeneousSubmodule ℚ (blockWeight (GlobalTheory κ)) m) :
    linSubst B f ∈ weightedHomogeneousSubmodule ℚ (blockWeight (GlobalTheory κ)) m := by
  rw [mem_weightedHomogeneousSubmodule, isWeightedHomogeneous_iff] at hf ⊢
  exact isHomogeneous_linSubst B hf

/- English proof (translation)
Use `set e := linEquiv B B' h₁ h₂`. Establish `hc : P.comap (linSubst B) = P.comap e`. Use extensionality with `f`. Both sides reduce to the same expression. Establish `hIJ : P = (P.comap e).map (e : MRing (GlobalTheory κ) ℚ →+* MRing (GlobalTheory κ) ℚ)` using `(Ideal.map_comap_of_surjective _ e.surjective P).symm`.

Use `set E := Ideal.quotientEquivAlg (R₁ := ℚ) (P.comap e) P e hIJ`. Establish `hpiece : ∀ m : Unit → ℕ, (NumbersDVR.gradedPiece (P.comap e) m).map E.toLinearEquiv.toLinearMap = NumbersDVR.gradedPiece P m`. Introduce `m`. Use extensionality with `y`. Simplify using `only [NumbersDVR.gradedPiece, Submodule.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨f, hf, rfl⟩, rfl⟩`. Use `⟨e f, mem_weighted_linSubst B hf, ?_⟩` and prove the remaining obligations. Simplify using `[E, Ideal.quotientEquivAlg_mk]`. Introduce and unpack `⟨g, hg, rfl⟩`.

Use `⟨_, ⟨e.symm g, mem_weighted_linSubst B' hg, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[E, Ideal.quotientEquivAlg_mk]`. Use function extensionality and compare the values at `m`. Unfold `NumbersDVR.hilbFn`. Rewrite using `[hc]`.

Use `split_ifs`. Rewrite using `[← hpiece, LinearEquiv.finrank_map_eq]`. Both sides reduce to the same expression.
-/
theorem hilbFn_comap [DecidableEq κ] (B B' : Matrix (Ix κ) (Ix κ) ℚ) (h₁ : B * B' = 1) (h₂ : B' * B = 1)
    (P : Ideal (MRing (GlobalTheory κ) ℚ)) : NumbersDVR.hilbFn (P.comap (linSubst B)) = NumbersDVR.hilbFn P := by
  set e := linEquiv B B' h₁ h₂
  have hc : P.comap (linSubst B) = P.comap e := by
    ext f
    rfl
  have hIJ : P = (P.comap e).map (e : MRing (GlobalTheory κ) ℚ →+* MRing (GlobalTheory κ) ℚ) :=
    (Ideal.map_comap_of_surjective _ e.surjective P).symm
  set E := Ideal.quotientEquivAlg (R₁ := ℚ) (P.comap e) P e hIJ
  have hpiece : ∀ m : Unit → ℕ, (NumbersDVR.gradedPiece (P.comap e) m).map E.toLinearEquiv.toLinearMap = NumbersDVR.gradedPiece P m := by
    intro m
    ext y
    simp only [NumbersDVR.gradedPiece, Submodule.mem_map]
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      refine ⟨e f, mem_weighted_linSubst B hf, ?_⟩
      simp [E, Ideal.quotientEquivAlg_mk]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨_, ⟨e.symm g, mem_weighted_linSubst B' hg, rfl⟩, ?_⟩
      simp [E, Ideal.quotientEquivAlg_mk]
  funext m
  unfold NumbersDVR.hilbFn
  rw [hc]
  split_ifs
  · rw [← hpiece, LinearEquiv.finrank_map_eq]
  · rfl

end Hilbert

end GenDegMatAct

/- English proof (translation)
Introduce `D Ω _ _ κ _ x B hB`. Take `⟨B', h₁, h₂⟩` from `GenDegMatAct.exists_inv hB`. Unfold `genDeg`. Rewrite using `[GenDegMatAct.map_coordIdeal_int, GenDegMatAct.map_coordIdeal_int, GenDegMatAct.coordIdeal_matAct]`. Unfold `NumbersDVR.intNum`.

Use `congr 2`. Use `GenDegMatAct.hilbFn_comap B B' h₁ h₂ (coordIdeal ℚ x)` and compare the differences between its conclusion and the goal.
-/
theorem GenDegMatAct.proof : GenDegMatAct.Statement := by
  intro D Ω _ _ κ _ x B hB
  classical
  obtain ⟨B', h₁, h₂⟩ := GenDegMatAct.exists_inv hB
  unfold genDeg
  rw [GenDegMatAct.map_coordIdeal_int, GenDegMatAct.map_coordIdeal_int, GenDegMatAct.coordIdeal_matAct]
  unfold NumbersDVR.intNum
  congr 2
  convert GenDegMatAct.hilbFn_comap B B' h₁ h₂ (coordIdeal ℚ x)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
