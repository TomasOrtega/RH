import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantFrameComparisonStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionIntertwiningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

section Frame

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

/- English proof (translation)
Establish `key : ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (algebraMap ℤ_[p] Λ c)) = (algebraMap ℤ_[p] (Ainf p O) c) ⊗ₜ[ℤ_[p]] (1 : Λ)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Establish `h1` using `hf 1 (algebraMap ℤ_[p] Λ c)`. Rewrite `h1` using `[key, hf, map_one, map_one, one_mul, mul_one]`. Conclude with `h1.symm`.
-/
theorem sigma_algebraMap_of_isTheta {σ : Λ →+* O} {f : RL p O Λ →+* O} (hf : IsTheta σ f)
    (c : ℤ_[p]) : σ (algebraMap ℤ_[p] Λ c) = padicToO p O c := by
  have key : ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (algebraMap ℤ_[p] Λ c)) =
      (algebraMap ℤ_[p] (Ainf p O) c) ⊗ₜ[ℤ_[p]] (1 : Λ) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have h1 := hf 1 (algebraMap ℤ_[p] Λ c)
  rw [key, hf, map_one, map_one, one_mul, mul_one] at h1
  exact h1.symm

/- English proof (translation)
Establish `hl : l ∈ Algebra.adjoin ℤ_[p] {α}` using `hα ▸ Algebra.mem_top`. Rewrite `hl` using `[Algebra.adjoin_singleton_eq_range_aeval]`. Take `⟨g, rfl⟩` from `(AlgHom.mem_range _).mp hl`. Use `⟨g.map (padicToO p O), fun σ f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval_map, Polynomial.aeval_def, Polynomial.hom_eval₂]`.

Use `congr 1`. Use extensionality with `c`. Conclude with `sigma_algebraMap_of_isTheta hf c`.
-/
theorem exists_poly_of_adjoin (α : Λ) (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (l : Λ) :
    ∃ g : Polynomial O, ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → σ l = g.eval (σ α) := by
  have hl : l ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hl
  obtain ⟨g, rfl⟩ := (AlgHom.mem_range _).mp hl
  refine ⟨g.map (padicToO p O), fun σ f hf => ?_⟩
  rw [Polynomial.eval_map, Polynomial.aeval_def, Polynomial.hom_eval₂]
  congr 1
  ext c
  exact sigma_algebraMap_of_isTheta hf c

/- English proof (translation)
Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, fun σ f _ => by simp⟩`. Consider the case `tmul a l`. Take `⟨g, hg⟩` from `exists_poly_of_adjoin (O := O) α hα l`. Conclude with `⟨Polynomial.C (WittVector.fontaineTheta O p a) * g, fun σ f hf => by`.

Rewrite using `[hf, hg σ f hf]`. Use the proof step `simp⟩`. Consider the case `add x y hx hy`. Take `⟨P, hP⟩` from `hx`. Take `⟨Q, hQ⟩` from `hy`.

Conclude with `⟨P + Q, fun σ f hf => by rw [map_add, hP σ f hf, hQ σ f hf, Polynomial.eval_add]⟩`.
-/
theorem exists_poly_of_elt (α : Λ) (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (r : RL p O Λ) :
    ∃ P : Polynomial O, ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → f r = P.eval (σ α) := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, fun σ f _ => by simp⟩
  | tmul a l =>
    obtain ⟨g, hg⟩ := exists_poly_of_adjoin (O := O) α hα l
    exact ⟨Polynomial.C (WittVector.fontaineTheta O p a) * g, fun σ f hf => by
      rw [hf, hg σ f hf]; simp⟩
  | add x y hx hy =>
    obtain ⟨P, hP⟩ := hx
    obtain ⟨Q, hQ⟩ := hy
    exact ⟨P + Q, fun σ f hf => by rw [map_add, hP σ f hf, hQ σ f hf, Polynomial.eval_add]⟩

/- English proof (translation)
Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add P Q hP hQ`. Take `⟨r, hr⟩` from `hP`. Take `⟨s, hs⟩` from `hQ`. Conclude with `⟨r + s, fun σ f hf => by rw [map_add, hr σ f hf, hs σ f hf, Polynomial.eval_add]⟩`.

Consider the case `monomial n c`. Take `⟨a, ha⟩` from `hθ c`. Conclude with `⟨a ⊗ₜ[ℤ_[p]] (α ^ n), fun σ f hf => by rw [hf, ha, map_pow, Polynomial.eval_monomial]⟩`.
-/
theorem exists_elt_of_poly (hθ : Function.Surjective (WittVector.fontaineTheta O p)) (α : Λ)
    (P : Polynomial O) : ∃ r : RL p O Λ, ∀ (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → f r = P.eval (σ α) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    obtain ⟨r, hr⟩ := hP
    obtain ⟨s, hs⟩ := hQ
    exact ⟨r + s, fun σ f hf => by rw [map_add, hr σ f hf, hs σ f hf, Polynomial.eval_add]⟩
  | monomial n c =>
    obtain ⟨a, ha⟩ := hθ c
    exact ⟨a ⊗ₜ[ℤ_[p]] (α ^ n), fun σ f hf => by rw [hf, ha, map_pow, Polynomial.eval_monomial]⟩

end Frame

end GlobalTheory.DetInv

namespace GlobalTheory.DetInv

/- English proof (translation)
Use `haveI := Fintype.ofFinite ι`. Establish `h1 : ∀ (i : Fin N) (c : ι → C), (fun σ => (Pi.single i (c σ) : Fin N → C)) ∈ LinearMap.range Φ`. Introduce `i c`. Use `set Q := Lagrange.interpolate Finset.univ x c with hQ`. Establish `e : (fun σ => (Pi.single i (c σ) : Fin N → C)) = ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k • fun σ => (Pi.single i (x σ ^ k) : Fin N → C)`.

Use function extensionality and compare the values at `σ j`. Establish `hc : c σ = ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * x σ ^ k`. Rewrite using `[← Polynomial.eval_eq_sum_range, hQ, Lagrange.eval_interpolate_at_node c hx.injOn (Finset.mem_univ σ)]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]`. Use `split_ifs`.

Conclude with `hc`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h i k)`. Introduce `y`.

Establish `e : y = ∑ i : Fin N, fun σ => (Pi.single i (y σ i) : Fin N → C)`. Use function extensionality and compare the values at `σ j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Establish `: y ∈ LinearMap.range Φ`. Rewrite using `[e]`.

Conclude with `Submodule.sum_mem _ fun i _ => h1 i _`. Conclude with `this`.
-/
theorem surjective_of_pow_mem_range {C V ι : Type} [Field C] [AddCommGroup V] [Module C V]
    [Finite ι] {N : ℕ} (Φ : V →ₗ[C] (ι → Fin N → C)) (x : ι → C) (hx : Function.Injective x)
    (h : ∀ (i : Fin N) (k : ℕ),
      (fun σ => (Pi.single i (x σ ^ k) : Fin N → C)) ∈ LinearMap.range Φ) :
    Function.Surjective Φ := by
  classical
  haveI := Fintype.ofFinite ι
  have h1 : ∀ (i : Fin N) (c : ι → C),
      (fun σ => (Pi.single i (c σ) : Fin N → C)) ∈ LinearMap.range Φ := by
    intro i c
    set Q := Lagrange.interpolate Finset.univ x c with hQ
    have e : (fun σ => (Pi.single i (c σ) : Fin N → C)) =
        ∑ k ∈ Finset.range (Q.natDegree + 1),
          Q.coeff k • fun σ => (Pi.single i (x σ ^ k) : Fin N → C) := by
      funext σ j
      have hc : c σ = ∑ k ∈ Finset.range (Q.natDegree + 1), Q.coeff k * x σ ^ k := by
        rw [← Polynomial.eval_eq_sum_range, hQ,
          Lagrange.eval_interpolate_at_node c hx.injOn (Finset.mem_univ σ)]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      split_ifs
      · exact hc
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (h i k)
  intro y
  have e : y = ∑ i : Fin N, fun σ => (Pi.single i (y σ i) : Fin N → C) := by
    funext σ j
    simp [Finset.sum_apply, Pi.single_apply]
  have : y ∈ LinearMap.range Φ := by
    rw [e]
    exact Submodule.sum_mem _ fun i _ => h1 i _
  exact this

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ α hα N h hh D`. Take `⟨-, -, -, hθ, -⟩` from `GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε`. Take `⟨-, eM, -, hM, -⟩` from `GlobalTheory.T.determinant_frame_comparison p C v O hv ε hε Λ N h hh D`. Establish `hf : ∀ σ : Λ →+* O, ∃ f : RL p O Λ →+* O, IsTheta σ f` using `fun σ => (theta_tensor_exists p C v O hv ε hε Λ σ).imp fun f hf => hf.1`. Use `choose f hf using hf`.

Establish `hπ : ∀ σ : Λ →+* O, ∃ π, IsProj C eM (f σ) π` using `fun σ => GlobalTheory.T.exists_theta_projection p O C Λ N h σ (f σ) eM (hf σ)`. Use `choose π hπ using hπ`. Take `⟨hfin, hcard⟩` from `GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ`. Establish `hinj : Function.Injective fun σ : Λ →+* O => algebraMap O C (σ α)`. Introduce `σ τ hστ`.

Establish `h1 : σ α = τ α` using `hv.hom_inj hστ`. Use extensionality with `l`. Take `⟨g, hg⟩` from `exists_poly_of_adjoin (O := O) α hα l`. Rewrite using `[hg σ _ (hf σ), hg τ _ (hf τ), h1]`. Establish `hsurj : Function.Surjective (LinearMap.pi π)`.

Use `surjective_of_pow_mem_range _ _ hinj fun i k => ?_` and prove the remaining obligations. Use `⟨fun j => algebraMap O C (WittVector.fontaineTheta O p (eM (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (α ^ k))) j)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `σ`. Rewrite using `[LinearMap.pi_apply, hπ σ]`. Use function extensionality and compare the values at `j`.

Simplify using `only [Pi.single_apply]`. Use `split_ifs`. Rewrite using `[hf σ]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish `hrk : Module.finrank C (Fin h → C) = Module.finrank C ((Λ →+* O) → Fin N → C)` using `by haveI := Fintype.ofFinite (Λ →+* O)`. Rewrite using `[Module.finrank_pi_fintype C (M := fun _ : Λ →+* O => Fin N → C)]`. Rewrite `hcard` using `[Nat.card_eq_fintype_card]`. Simplify using `[hcard, hh]`. Establish `hi : Function.Injective (LinearMap.pi π)` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).mpr hsurj`.

Establish `hb : Function.Bijective (LinearMap.pi π)` using `⟨hi, hsurj⟩`. Use `⟨LinearEquiv.ofBijective (LinearMap.pi π) hb, ?_, ?_⟩` and prove the remaining obligations. Introduce `l z σ`. Establish `hmat : IsMat eM eM (D.ρM l) (Matrix.diagonal fun _ : Fin N => ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l : RL p O Λ))`. Introduce `w`.

Rewrite using `[← hM l w]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using `[Matrix.mulVec_diagonal]`. Establish `key` using `GlobalTheory.T.theta_projection_intertwining p O C Λ N h (f σ) eM eM (π σ) (π σ) _ _ (hπ σ) (hπ σ) hmat z`.

Simplify using `only [LinearEquiv.ofBijective_apply, LinearMap.pi_apply]`. Establish `e1 : (actH D l).map (algebraMap O C) *ᵥ z = redC C (D.ρM l) z`. Simplify using `only [actH, redC, Matrix.map_map, Matrix.toLin'_apply, RingHom.coe_comp]`. Rewrite using `[e1, key, Matrix.diagonal_map (map_zero _)]`. Use function extensionality and compare the values at `j`.

Rewrite using `[Matrix.mulVec_diagonal, RingHom.comp_apply, hf σ]`. Simplify using the standard rewrite rules. Introduce `z`. Simplify using `only [LinearEquiv.ofBijective_apply, LinearMap.pi_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `hz i choose t ht using hz choose a ha using fun j => hθ (t j)`. Establish `e : z = fun j => algebraMap O C (WittVector.fontaineTheta O p (eM (eM.symm a) j))`. Use function extensionality and compare the values at `j`. Rewrite using `[eM.apply_symm_apply, ha, ht]`. Take `⟨P, hP⟩` from `exists_poly_of_elt α hα (eM.symm a i)`.

Use `⟨P, fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[e, hπ σ, ← hP σ _ (hf σ)]`. Introduce `hz choose P hP using hz choose r hr using fun i => exists_elt_of_poly hθ α (P i)`. Establish `e : z = fun j => algebraMap O C (WittVector.fontaineTheta O p (eM r j))`. Apply `hi` to reduce the goal to its premises.

Use function extensionality and compare the values at `σ`. Rewrite using `[LinearMap.pi_apply, LinearMap.pi_apply, hπ σ]`. Use function extensionality and compare the values at `i`. Rewrite using `[hP, hr i σ _ (hf σ)]`. Introduce `j`.

Rewrite using `[e]`. Conclude with `⟨_, rfl⟩`.
-/
theorem exists_frame_model : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (α : Λ), Algebra.adjoin ℤ_[p] {α} = ⊤ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ D : Datum ε h Λ, ∃ Φ : (Fin h → C) ≃ₗ[C] ((Λ →+* O) → Fin N → C), (∀ l z σ, Φ ((actH D l).map (algebraMap O C) *ᵥ z) σ = algebraMap O C (σ l) • Φ z σ) ∧ ∀ z, (∀ i, z i ∈ (algebraMap O C).range) ↔ ∀ i, ∃ f : Polynomial O, ∀ σ, Φ z σ i = algebraMap O C (f.eval (σ α)) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ α hα N h hh D
  obtain ⟨-, -, -, hθ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  obtain ⟨-, eM, -, hM, -⟩ := GlobalTheory.T.determinant_frame_comparison p C v O hv ε hε Λ N h hh D
  have hf : ∀ σ : Λ →+* O, ∃ f : RL p O Λ →+* O, IsTheta σ f := fun σ =>
    (theta_tensor_exists p C v O hv ε hε Λ σ).imp fun f hf => hf.1
  choose f hf using hf
  have hπ : ∀ σ : Λ →+* O, ∃ π, IsProj C eM (f σ) π := fun σ =>
    GlobalTheory.T.exists_theta_projection p O C Λ N h σ (f σ) eM (hf σ)
  choose π hπ using hπ
  obtain ⟨hfin, hcard⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  have hinj : Function.Injective fun σ : Λ →+* O => algebraMap O C (σ α) := by
    intro σ τ hστ
    have h1 : σ α = τ α := hv.hom_inj hστ
    ext l
    obtain ⟨g, hg⟩ := exists_poly_of_adjoin (O := O) α hα l
    rw [hg σ _ (hf σ), hg τ _ (hf τ), h1]
  have hsurj : Function.Surjective (LinearMap.pi π) := by
    refine surjective_of_pow_mem_range _ _ hinj fun i k => ?_
    refine ⟨fun j => algebraMap O C (WittVector.fontaineTheta O p
      (eM (Pi.single i ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] (α ^ k))) j)), ?_⟩
    funext σ
    rw [LinearMap.pi_apply, hπ σ]
    funext j
    simp only [Pi.single_apply]
    split_ifs
    · rw [hf σ]; simp
    · simp
  have hrk : Module.finrank C (Fin h → C) = Module.finrank C ((Λ →+* O) → Fin N → C) := by
    haveI := Fintype.ofFinite (Λ →+* O)
    rw [Module.finrank_pi_fintype C (M := fun _ : Λ →+* O => Fin N → C)]
    rw [Nat.card_eq_fintype_card] at hcard
    simp [hcard, hh]
  have hi : Function.Injective (LinearMap.pi π) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrk).mpr hsurj
  have hb : Function.Bijective (LinearMap.pi π) := ⟨hi, hsurj⟩
  refine ⟨LinearEquiv.ofBijective (LinearMap.pi π) hb, ?_, ?_⟩
  · intro l z σ
    have hmat : IsMat eM eM (D.ρM l)
        (Matrix.diagonal fun _ : Fin N => ((1 : Ainf p O) ⊗ₜ[ℤ_[p]] l : RL p O Λ)) := by
      intro w
      rw [← hM l w]
      congr 1
      funext j
      simp [Matrix.mulVec_diagonal]
    have key := GlobalTheory.T.theta_projection_intertwining p O C Λ N h (f σ) eM eM (π σ) (π σ) _ _ (hπ σ) (hπ σ) hmat z
    simp only [LinearEquiv.ofBijective_apply, LinearMap.pi_apply]
    have e1 : (actH D l).map (algebraMap O C) *ᵥ z = redC C (D.ρM l) z := by
      simp only [actH, redC, Matrix.map_map, Matrix.toLin'_apply, RingHom.coe_comp]
    rw [e1, key, Matrix.diagonal_map (map_zero _)]
    funext j
    rw [Matrix.mulVec_diagonal, RingHom.comp_apply, hf σ]
    simp
  · intro z
    simp only [LinearEquiv.ofBijective_apply, LinearMap.pi_apply]
    constructor
    · intro hz i
      choose t ht using hz
      choose a ha using fun j => hθ (t j)
      have e : z = fun j => algebraMap O C (WittVector.fontaineTheta O p (eM (eM.symm a) j)) := by
        funext j
        rw [eM.apply_symm_apply, ha, ht]
      obtain ⟨P, hP⟩ := exists_poly_of_elt α hα (eM.symm a i)
      refine ⟨P, fun σ => ?_⟩
      rw [e, hπ σ, ← hP σ _ (hf σ)]
    · intro hz
      choose P hP using hz
      choose r hr using fun i => exists_elt_of_poly hθ α (P i)
      have e : z = fun j => algebraMap O C (WittVector.fontaineTheta O p (eM r j)) := by
        apply hi
        funext σ
        rw [LinearMap.pi_apply, LinearMap.pi_apply, hπ σ]
        funext i
        rw [hP, hr i σ _ (hf σ)]
      intro j
      rw [e]
      exact ⟨_, rfl⟩

end GlobalTheory.DetInv
