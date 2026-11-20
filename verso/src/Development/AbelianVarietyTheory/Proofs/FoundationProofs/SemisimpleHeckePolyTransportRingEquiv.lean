import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.Transport

variable {R S : Type} [CommRing R] [CommRing S]

def mapF (φ : R →+* S) (F : ℂ → MvPolynomial (Fin 2) R) : ℂ → MvPolynomial (Fin 2) S :=
  fun z => MvPolynomial.map φ (F z)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem map_smul' (φ : R →+* S) (c : R) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (c • p) = φ c • MvPolynomial.map φ p := by
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.
-/
theorem map_slP (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (slP m p) = slP m (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slP]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, Betti.slP_X, MvPolynomial.map_X, map_add, map_smul', map_intCast]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem mapF_add (φ : R →+* S) (F G : ℂ → MvPolynomial (Fin 2) R) : mapF φ (F + G) = mapF φ F + mapF φ G := by
  funext z; simp [mapF]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem mapF_sub (φ : R →+* S) (F G : ℂ → MvPolynomial (Fin 2) R) : mapF φ (F - G) = mapF φ F - mapF φ G := by
  funext z; simp [mapF]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem mapF_smul (φ : R →+* S) (c : R) (F : ℂ → MvPolynomial (Fin 2) R) : mapF φ (c • F) = φ c • mapF φ F := by
  funext z; simp [mapF, map_smul']

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem mapF_sum {ι : Type} (φ : R →+* S) (s : Finset ι) (F : ι → ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (∑ j ∈ s, F j) = ∑ j ∈ s, mapF φ (F j) := by
  funext z; simp [mapF, Finset.sum_apply, map_sum]

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem mapF_opP (φ : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (opP R m F) = opP S m (mapF φ F) := by
  funext z; simp [mapF, opP, map_slP]

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem mapF_opL (φ : R →+* S) (N l : ℕ) (T : Letter) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF φ (opL R N l T F) = opL S N l T (mapF φ F) := by
  cases T with
  | T q => simp only [opL, LinearMap.add_apply, LinearMap.sum_apply, mapF_add, mapF_sum, mapF_opP]
  | U => simp only [opL, LinearMap.sum_apply, mapF_sum, mapF_opP]
  | D d => simp only [opL, mapF_opP]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression.
-/
theorem mapF_mem_pot (φ : R →+* S) {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) R}
    (hF : F ∈ Pot R w Γ) : mapF φ F ∈ Pot S w Γ := by
  obtain ⟨h1, h2⟩ := hF
  refine ⟨fun z => (h1 z).map φ, fun γ hγ => ?_⟩
  obtain ⟨p, hp⟩ := h2 γ hγ
  refine ⟨MvPolynomial.map φ p, fun z hz => ?_⟩
  rw [← hp z hz, map_sub, map_slP]; rfl

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem mapF_mem_triv (φ : R →+* S) {w : ℕ} {Γ : Subgroup SL(2, ℤ)} {F : ℂ → MvPolynomial (Fin 2) R}
    (hF : F ∈ Triv R w Γ) : mapF φ F ∈ Triv S w Γ := by
  obtain ⟨ψ, p, h1, h2⟩ := hF
  refine ⟨mapF φ ψ, MvPolynomial.map φ p, fun γ hγ z hz => ?_, fun z hz => ?_⟩
  · simp only [mapF]; rw [← map_slP, h1 γ hγ z hz]
  · simp only [mapF]; rw [h2 z hz, map_add]

/- English proof (translation)
Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Treat this case separately. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Treat this case separately. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Supply the required witnesses or components.
-/
theorem exists_preimage (ι : R ≃+* S) (N l : ℕ) (lam : Letter → R) {P : FreeAlgebra S Letter} (hP : P ∈ admissibleLettersSubalgebra S N l) :
    ∃ Q ∈ admissibleLettersSubalgebra R N l, ι (FreeAlgebra.lift R lam Q) = FreeAlgebra.lift S (fun T => ι (lam T)) P ∧
      ∀ F, mapF (ι : R →+* S) (FreeAlgebra.lift R (opL R N l) Q F) =
        FreeAlgebra.lift S (opL S N l) P (mapF (ι : R →+* S) F) := by
  unfold admissibleLettersSubalgebra at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨T, hT, rfl⟩ := hx
    exact ⟨FreeAlgebra.ι R T, Algebra.subset_adjoin ⟨T, hT, rfl⟩, by simp, fun F => by simp [mapF_opL]⟩
  | algebraMap r =>
    refine ⟨algebraMap R _ (ι.symm r), Subalgebra.algebraMap_mem _ _, by simp, fun F => ?_⟩
    simp [Module.algebraMap_end_apply, mapF_smul]
  | add x y _ _ hx hy =>
    obtain ⟨Q, hQ, h1, h2⟩ := hx
    obtain ⟨Q', hQ', h1', h2'⟩ := hy
    exact ⟨Q + Q', add_mem hQ hQ', by simp [h1, h1'], fun F => by simp [mapF_add, h2, h2']⟩
  | mul x y _ _ hx hy =>
    obtain ⟨Q, hQ, h1, h2⟩ := hx
    obtain ⟨Q', hQ', h1', h2'⟩ := hy
    exact ⟨Q * Q', mul_mem hQ hQ', by simp [h1, h1'], fun F => by simp [h2, h2']⟩

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem mapF_symm_mapF (ι : R ≃+* S) (F : ℂ → MvPolynomial (Fin 2) R) :
    mapF (ι.symm : S →+* R) (mapF (ι : R →+* S) F) = F := by
  funext z
  simp only [mapF, MvPolynomial.map_map]
  rw [RingEquiv.symm_comp, MvPolynomial.map_id]

end GlobalTheory.KZ.Transport

open GlobalTheory.KZ.Transport in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem GlobalTheory.KZ.ssPot_transport : ∀ (N l w : ℕ) {E : Type} [Field E] (ι : E ≃+* ℂ) (lam : Letter → E),
    SSPotB N l w (fun T => ι (lam T)) → ∃ P ∈ admissibleLettersSubalgebra E N l, FreeAlgebra.lift E lam P = 1 ∧
      ∀ F ∈ Pot E w (Gam N l), ∀ T : Letter, admitted N l T →
        (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
          (FreeAlgebra.lift E (opL E N l) P F) ∈ Triv E w (Gam N l) := by
  intro N l w E _ ι lam ⟨P, hP, h1, h2⟩
  obtain ⟨Q, hQ, e1, e2⟩ := exists_preimage ι N l lam hP
  refine ⟨Q, hQ, ι.injective (by rw [e1, h1, map_one]), fun F hF T hT => ?_⟩
  have h := mapF_mem_triv (ι.symm : ℂ →+* E) (h2 _ (mapF_mem_pot (ι : E →+* ℂ) hF) T hT)
  rw [← e2] at h
  rw [← mapF_symm_mapF ι ((opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
          (FreeAlgebra.lift E (opL E N l) Q F))]
  convert h using 2
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, mapF_sub, mapF_smul, mapF_opL]
  rfl
