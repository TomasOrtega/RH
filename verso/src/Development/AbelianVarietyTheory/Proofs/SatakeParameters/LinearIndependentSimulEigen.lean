import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryRationalHeckeCommuteComplexAutomoStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugatesAutomorphicFormSpanFiniteDimensionalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAutomorphismOrbitMemFiniteExtensionPadicStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConjIsAutFormU
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LinearIndependentJointEigenvectors
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong
open scoped Pointwise

noncomputable section

namespace GlobalTheory.Cong

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors`. Consider the case `exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors`. Consider the case `(apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors ..)`.
-/
theorem linearIndependent_simulEigen {J V : Type} [AddCommGroup V] [Module ℂ V] (T : J → V →ₗ[ℂ] V)
    (S : Set (J → ℂ)) (v : S → V) (hv : ∀ χ, v χ ≠ 0)
    (hT : ∀ (χ : S) j, T j (v χ) = (χ : J → ℂ) j • v χ) : LinearIndependent ℂ v := by
  first
  | exact @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors
  | (apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenvectorsIndependentSatakeParameters.linearIndependent_jointEigenvectors ..)

def opLin {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ) :
    V →ₗ[ℂ] V :=
  f.sum fun g c => c • ρ g

/- English proof (translation)
Simplify using `[opLin, opOf, Finsupp.sum, LinearMap.sum_apply]`.
-/
theorem opLin_apply {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ Γ V) (f : Γ →₀ ℂ)
    (v : V) : opLin ρ f v = opOf ρ f v := by
  simp [opLin, opOf, Finsupp.sum, LinearMap.sum_apply]

/- English proof (translation)
Use `Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hφ.cont continuous_const ?_` and prove the remaining obligations. Introduce and unpack `x ⟨γ, hγ, g, hg, rfl⟩`. Simplify using `only [Pi.zero_apply]`. Rewrite using `[hφ.left γ hγ g]`. Conclude with `h0 g hg`.
-/
theorem eq_zero_of_finU {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {φ : UA E n → ℂ}
    (hφ : IsAutFormU φ) (h0 : ∀ g ∈ finU E n, φ g = 0) : φ = 0 := by
  refine Continuous.ext_on (GlobalTheory.UnitarySplit.dense_and_split E n).1 hφ.cont continuous_const ?_
  rintro x ⟨γ, hγ, g, hg, rfl⟩
  simp only [Pi.zero_apply]
  rw [hφ.left γ hγ g]
  exact h0 g hg

/- English proof (translation)
Introduce `E _ _ _ l _ ι a _ w₀ K _ lam J t η ht hact U hU`. Take `⟨φ, hφU, hφ0, hφK⟩` from `hU.fix`. Establish `hφ : IsAutFormU φ` using `hU.aut.aut φ hφU`. Establish `heig : ∀ j, opOf (RU E a) (t j) φ = η U j • φ` using `fun j => hact U hU.aut φ hφU hφK j`. Choose the witnesses or unpack the hypotheses as in `⟨g₀, hg₀, hφg₀⟩ : ∃ g ∈ finU E a, φ g ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hφ0 (eq_zero_of_finU hφ h)`. Use `choose φ' hφ' hφ'eq using fun σ : ℂ ≃+* ℂ => exists_conj_isAutFormU E a σ φ hφ`. Take `⟨M, hMfin, hM⟩` from `GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional E a φ hφ`.

Establish `heig' : ∀ σ j, opOf (RU E a) (t j) (φ' σ) = σ (η U j) • φ' σ` using `fun σ j => GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism E a σ (t j) (ht j) φ (φ' σ) (η U j) hφ (hφ' σ) (hφ'eq σ) (heig j)`. Establish `hne : ∀ σ, φ' σ ≠ 0`. Introduce `σ h`. Establish `e` using `hφ'eq σ g₀ hg₀`. Rewrite `e` using `[h, Pi.zero_apply, eq_comm, map_eq_zero_iff σ σ.injective]`.

Conclude with `hφg₀ e`. Establish `hfin : (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j)).Finite` using `by set S := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j) with hS`. Establish `hch : ∀ χ : S, ∃ σ : ℂ ≃+* ℂ, (fun j => σ (η U j)) = (χ : J → ℂ)` using `fun χ => χ.2`. Use `choose sel hsel using hch`. Set `v : S → (UA E a → ℂ)` to `fun χ => φ' (sel χ)`.

Establish `hli : LinearIndependent ℂ v`. Use `linearIndependent_simulEigen (fun j => opLin (RU E a) (t j)) S v (fun χ => hne _) ?_` and prove the remaining obligations. Introduce `χ j`. Rewrite using `[opLin_apply, heig', ← hsel χ]`. Set `v' : S → M` to `fun χ => ⟨v χ, hM (sel χ) (φ' (sel χ)) (hφ' _) (hφ'eq _)⟩`.

Establish `hli' : LinearIndependent ℂ v'` using `LinearIndependent.of_comp M.subtype hli`. Establish `: Finite S` using `hli'.finite`. Conclude with `Set.toFinite S`. Take `⟨L, hL, hLmem⟩` from `GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic l ι J (η U) hfin`. Conclude with `⟨⟨L, hL⟩, hLmem⟩`.
-/
theorem finU_holds : FinU := by
  intro E _ _ _ l _ ι a _ w₀ K _ lam J t η ht hact U hU
  obtain ⟨φ, hφU, hφ0, hφK⟩ := hU.fix
  have hφ : IsAutFormU φ := hU.aut.aut φ hφU
  have heig : ∀ j, opOf (RU E a) (t j) φ = η U j • φ := fun j => hact U hU.aut φ hφU hφK j
  obtain ⟨g₀, hg₀, hφg₀⟩ : ∃ g ∈ finU E a, φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (eq_zero_of_finU hφ h)
  choose φ' hφ' hφ'eq using fun σ : ℂ ≃+* ℂ => exists_conj_isAutFormU E a σ φ hφ
  obtain ⟨M, hMfin, hM⟩ := GlobalTheory.T.conjugates_automorphicForm_span_finiteDimensional E a φ hφ
  have heig' : ∀ σ j, opOf (RU E a) (t j) (φ' σ) = σ (η U j) • φ' σ := fun σ j =>
    GlobalTheory.T.definiteUnitaryRationalHecke_commute_complexAutomorphism E a σ (t j) (ht j) φ (φ' σ) (η U j) hφ (hφ' σ) (hφ'eq σ) (heig j)
  have hne : ∀ σ, φ' σ ≠ 0 := by
    intro σ h
    have e := hφ'eq σ g₀ hg₀
    rw [h, Pi.zero_apply, eq_comm, map_eq_zero_iff σ σ.injective] at e
    exact hφg₀ e
  have hfin : (Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j)).Finite := by
    set S := Set.range fun σ : ℂ ≃+* ℂ => fun j => σ (η U j) with hS
    have hch : ∀ χ : S, ∃ σ : ℂ ≃+* ℂ, (fun j => σ (η U j)) = (χ : J → ℂ) := fun χ => χ.2
    choose sel hsel using hch
    let v : S → (UA E a → ℂ) := fun χ => φ' (sel χ)
    have hli : LinearIndependent ℂ v := by
      refine linearIndependent_simulEigen (fun j => opLin (RU E a) (t j)) S v (fun χ => hne _) ?_
      intro χ j
      rw [opLin_apply, heig', ← hsel χ]
    let v' : S → M := fun χ => ⟨v χ, hM (sel χ) (φ' (sel χ)) (hφ' _) (hφ'eq _)⟩
    have hli' : LinearIndependent ℂ v' := LinearIndependent.of_comp M.subtype hli
    have : Finite S := hli'.finite
    exact Set.toFinite S
  obtain ⟨L, hL, hLmem⟩ := GlobalTheory.T.finite_automorphism_orbit_mem_finite_extension_padic l ι J (η U) hfin
  exact ⟨⟨L, hL⟩, hLmem⟩

end GlobalTheory.Cong
