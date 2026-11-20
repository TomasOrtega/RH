import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasisStatement
import Lemmata.GeneralBFactExtra.Imports

namespace ReciprocityTheory.ChartRestriction.G.H1

open Module TensorProduct

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact'''.goal1 .. | (apply Bl.general_b_fact'''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact'''.goal1 <;> assumption)`.
-/
theorem linearIndependent_of_eigen {K V ι Γ : Type} [Field K] [AddCommGroup V] [Module K V]
    (T : Γ → V →ₗ[K] V) (c : ι → Γ → K) (w : ι → V) (hw : ∀ i, w i ≠ 0)
    (he : ∀ i γ, T γ (w i) = c i γ • w i) (hd : ∀ i j, i ≠ j → ∃ γ, c i γ ≠ c j γ) :
    LinearIndependent K w := by
  first | exact Bl.general_b_fact'''.goal1 .. | (apply Bl.general_b_fact'''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact'''.goal1 <;> assumption)

/- English proof (translation)
Introduce `R _ _ M _ _ _ _ ι _ Γ T χ s hcard hs hT hχ`. Establish `hiff : ∀ x : M, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = 0 ↔ x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M)`. Introduce `x`. Establish `h1 : TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal R) ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x) = Submodule.Quotient.mk x`. Establish `h` using `TensorProduct.quotTensorEquivQuotSMul_mk_tmul (IsLocalRing.maximalIdeal R) (1 : R) x`.

Rewrite `h` using `[one_smul]`. Conclude with `h`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, ← h1, LinearEquiv.map_eq_zero_iff]`. Conclude with `Iff.rfl`. Set `w : ι → IsLocalRing.ResidueField R ⊗[R] M` to `fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] s i`.

Establish `hw0 : ∀ i, w i ≠ 0` using `fun i h => hs i ((hiff (s i)).mp h)`. Establish `he : ∀ i γ, ((T γ).baseChange (IsLocalRing.ResidueField R)) (w i) = IsLocalRing.residue R (χ i γ) • w i`. Introduce `i γ`. Establish `hd` using `(hiff _).mpr (hT i γ)`. Rewrite `hd` using `[TensorProduct.tmul_sub, sub_eq_zero]`.

Simplify using `only [w, LinearMap.baseChange_tmul, hd, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Use `congr 1`. Rewrite using `[Algebra.smul_def, mul_one]`. Both sides reduce to the same expression. Establish `hd : ∀ i j, i ≠ j → ∃ γ, IsLocalRing.residue R (χ i γ) ≠ IsLocalRing.residue R (χ j γ)`.

Introduce `i j hij`. Take `⟨γ, hγ⟩` from `hχ i j hij`. Use `⟨γ, fun h => hγ ?_⟩` and prove the remaining obligations. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]`. Establish `hli : LinearIndependent (IsLocalRing.ResidueField R) w` using `linearIndependent_of_eigen (fun γ => (T γ).baseChange (IsLocalRing.ResidueField R)) (fun i γ => IsLocalRing.residue R (χ i γ)) w hw0 he hd`.

Establish `hcard' : Fintype.card ι = finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)`. Rewrite using `[Module.finrank_baseChange, hcard]`. Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Establish `h0 : finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) = 0`. Rewrite using `[← hcard']`.

Conclude with `Fintype.card_eq_zero`. Use `haveI : Subsingleton (IsLocalRing.ResidueField R ⊗[R] M) := Module.finrank_zero_iff.mp h0`. Conclude with `IsLocalRing.span_eq_top_of_tmul_eq_basis s (Basis.empty _) (fun i => isEmptyElim i)`. Conclude with `IsLocalRing.span_eq_top_of_tmul_eq_basis s (basisOfLinearIndependentOfCardEqFinrank hli hcard') (fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank])`.
-/
theorem nakayamaChar_holds : NakayamaCharStatement := by
  intro R _ _ M _ _ _ _ ι _ Γ T χ s hcard hs hT hχ
  classical
  have hiff : ∀ x : M, (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x = 0 ↔
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
    intro x
    have h1 : TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal R)
        ((1 : IsLocalRing.ResidueField R) ⊗ₜ[R] x) = Submodule.Quotient.mk x := by
      have h := TensorProduct.quotTensorEquivQuotSMul_mk_tmul (IsLocalRing.maximalIdeal R) (1 : R) x
      rw [one_smul] at h
      exact h
    rw [← Submodule.Quotient.mk_eq_zero, ← h1, LinearEquiv.map_eq_zero_iff]
    exact Iff.rfl
  let w : ι → IsLocalRing.ResidueField R ⊗[R] M := fun i => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] s i
  have hw0 : ∀ i, w i ≠ 0 := fun i h => hs i ((hiff (s i)).mp h)
  have he : ∀ i γ, ((T γ).baseChange (IsLocalRing.ResidueField R)) (w i) =
      IsLocalRing.residue R (χ i γ) • w i := by
    intro i γ
    have hd := (hiff _).mpr (hT i γ)
    rw [TensorProduct.tmul_sub, sub_eq_zero] at hd
    simp only [w, LinearMap.baseChange_tmul, hd, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    congr 1
    rw [Algebra.smul_def, mul_one]
    rfl
  have hd : ∀ i j, i ≠ j → ∃ γ, IsLocalRing.residue R (χ i γ) ≠ IsLocalRing.residue R (χ j γ) := by
    intro i j hij
    obtain ⟨γ, hγ⟩ := hχ i j hij
    refine ⟨γ, fun h => hγ ?_⟩
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  have hli : LinearIndependent (IsLocalRing.ResidueField R) w :=
    linearIndependent_of_eigen (fun γ => (T γ).baseChange (IsLocalRing.ResidueField R))
      (fun i γ => IsLocalRing.residue R (χ i γ)) w hw0 he hd
  have hcard' : Fintype.card ι = finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) := by
    rw [Module.finrank_baseChange, hcard]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h0 : finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M) = 0 := by
      rw [← hcard']
      exact Fintype.card_eq_zero
    haveI : Subsingleton (IsLocalRing.ResidueField R ⊗[R] M) := Module.finrank_zero_iff.mp h0
    exact IsLocalRing.span_eq_top_of_tmul_eq_basis s (Basis.empty _) (fun i => isEmptyElim i)
  · exact IsLocalRing.span_eq_top_of_tmul_eq_basis s
      (basisOfLinearIndependentOfCardEqFinrank hli hcard')
      (fun i => by rw [coe_basisOfLinearIndependentOfCardEqFinrank])

end ReciprocityTheory.ChartRestriction.G.H1
