import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.WeightCharacters.DeltaNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.Branching
open UpperTheory.Gal.Gen (IsLevel fixedBy)
open UpperTheory.Gal.Wt

/- English proof (translation)
Introduce `hB hS hT E _ _ _ a τ W`. Take `⟨-, -, hmono, -, -, hinv⟩` from `hB`. Use `set v₀ := InfinitePlace.mk τ with hv₀`. Set `d : ℕ` to `∑ i, ((W v₀).w i).natAbs + a * (W v₀).detShift.natAbs`. Establish `hps : ∀ k, psum (W v₀) k ≤ d` using `fun k => by`.

Establish `h1 : psum (W v₀) k ≤ ∑ i, (((W v₀).w i).natAbs : ℤ)` using `(Finset.sum_le_sum fun i _ => Int.le_natAbs).trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Int.natCast_nonneg _)`. Establish `h2 : (0 : ℤ) ≤ ((a * (W v₀).detShift.natAbs : ℕ) : ℤ)` using `Int.natCast_nonneg _`. Simplify using `only [d, Nat.cast_add, Nat.cast_sum]`. Use linear arithmetic over natural numbers and integers. Establish `h1 : ∀ k w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ), (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpLe d ∧ (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpGe (-d)` using `fun k w L => ⟨(hmono _ _ (hps k)).1 (hS a k _ w L).1, (hmono _ _ (neg_le_neg (by exact_mod_cast Nat.le_add_left _ _))).2 (hS a k _ w L).2⟩`.

Use `⟨d, fun k x hx v L => ?_⟩` and prove the remaining obligations. Establish `h2 : (∀ z, (x z).1 ∈ embU a v₀.embedding) ∧ ∀ w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ), (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpLe d ∧ (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpGe (-d)`. Break down `InfinitePlace.embedding_mk_eq τ with e | e` into its components or cases. Rewrite using `[hv₀, e]`. Use `⟨fun z => (hx z).1, fun w L => ?_⟩` and prove the remaining obligations.

Simplify using `only [(hx _).2]`. Conclude with `h1 k w L`. Rewrite using `[hv₀, e]`. Use `⟨fun z => by rw [GlobalTheory.DefiniteBC.embU_conjugate]; exact (hx z).1, fun w L => ?_⟩` and prove the remaining obligations. Establish `e2 : ∀ z, cEmb (ComplexEmbedding.conjugate τ) (x z).1 = tor a k z⁻¹` using `fun z => by`.

Rewrite using `[← (hT a k z).2.2.2, ← (hx z).2]`. Use extensionality with `i j`. Simplify using `[cEmb, GlobalTheory.DefiniteBC.coord_conjugate]`. Simplify using `only [e2]`. Establish `h3` using `(hinv _ _).2 (h1 k w L).2`.

Rewrite `h3` using `[neg_neg]`. Conclude with `⟨h3, (hinv _ _).1 (h1 k w L).1⟩`. Set `Φ : W.Sp →ₗ[ℂ] (Circle → ℂ)` to `LinearMap.pi fun z => L ∘ₗ W.rep (x z)`. Set `N : Submodule ℂ W.Sp` to `(ExpLe d ⊓ ExpGe (-d)).comap Φ`. Establish `hN : ∀ e, GlobalTheory.CoefIrred.tenMul W e ∈ N` using `fun e => by`.

Establish `h` using `h2.2 (e v₀) (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)`. Establish `e3 : Φ (GlobalTheory.CoefIrred.tenMul W e) = fun z => (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀) (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) (e v₀))`. Use function extensionality and compare the values at `z`. Use `rep_tenMul_update W v₀ (x z) (h2.1 z) e (e v₀)` as an intermediate fact. Rewrite `this` using `[Function.update_eq_self]`.

Conclude with `congrArg L this`. Express the relevant statement in the definitionally equal form `Φ _ ∈ ExpLe d ⊓ ExpGe (-d)`. Rewrite using `[e3]`. Conclude with `h`. Establish `h0` using `(GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) a W (W.Sp ⧸ N) 0).unique (y₁ := N.mkQ) (y₂ := 0) (fun u => (Submodule.Quotient.mk_eq_zero N).2 (hN u)) (fun u => rfl)`.

Conclude with `(Submodule.Quotient.mk_eq_zero N).1 (LinearMap.congr_fun h0 v)`.
-/
theorem UpperTheory.Gal.Wt.wExp_h : ExpBasic → SqExp → TorFacts → WExp := by
  intro hB hS hT E _ _ _ a τ W
  classical
  obtain ⟨-, -, hmono, -, -, hinv⟩ := hB
  set v₀ := InfinitePlace.mk τ with hv₀
  let d : ℕ := ∑ i, ((W v₀).w i).natAbs + a * (W v₀).detShift.natAbs
  have hps : ∀ k, psum (W v₀) k ≤ d := fun k => by
    have h1 : psum (W v₀) k ≤ ∑ i, (((W v₀).w i).natAbs : ℤ) :=
      (Finset.sum_le_sum fun i _ => Int.le_natAbs).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => Int.natCast_nonneg _)
    have h2 : (0 : ℤ) ≤ ((a * (W v₀).detShift.natAbs : ℕ) : ℤ) := Int.natCast_nonneg _
    simp only [d, Nat.cast_add, Nat.cast_sum]
    omega
  have h1 : ∀ k w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ), (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpLe d ∧
      (fun z => L (sqRep ℂ a (W v₀) (tor a k z) w)) ∈ ExpGe (-d) := fun k w L =>
    ⟨(hmono _ _ (hps k)).1 (hS a k _ w L).1, (hmono _ _ (neg_le_neg (by exact_mod_cast Nat.le_add_left _ _))).2 (hS a k _ w L).2⟩
  refine ⟨d, fun k x hx v L => ?_⟩
  have h2 : (∀ z, (x z).1 ∈ embU a v₀.embedding) ∧ ∀ w (L : nablaSq ℂ a (W v₀) →ₗ[ℂ] ℂ),
      (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpLe d ∧
      (fun z => L (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) w)) ∈ ExpGe (-d) := by
    rcases InfinitePlace.embedding_mk_eq τ with e | e
    · rw [hv₀, e]
      refine ⟨fun z => (hx z).1, fun w L => ?_⟩
      simp only [(hx _).2]
      exact h1 k w L
    · rw [hv₀, e]
      refine ⟨fun z => by rw [GlobalTheory.DefiniteBC.embU_conjugate]; exact (hx z).1, fun w L => ?_⟩
      have e2 : ∀ z, cEmb (ComplexEmbedding.conjugate τ) (x z).1 = tor a k z⁻¹ := fun z => by
        rw [← (hT a k z).2.2.2, ← (hx z).2]
        ext i j
        simp [cEmb, GlobalTheory.DefiniteBC.coord_conjugate]
      simp only [e2]
      have h3 := (hinv _ _).2 (h1 k w L).2
      rw [neg_neg] at h3
      exact ⟨h3, (hinv _ _).1 (h1 k w L).1⟩
  let Φ : W.Sp →ₗ[ℂ] (Circle → ℂ) := LinearMap.pi fun z => L ∘ₗ W.rep (x z)
  let N : Submodule ℂ W.Sp := (ExpLe d ⊓ ExpGe (-d)).comap Φ
  have hN : ∀ e, GlobalTheory.CoefIrred.tenMul W e ∈ N := fun e => by
    have h := h2.2 (e v₀) (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)
    have e3 : Φ (GlobalTheory.CoefIrred.tenMul W e) = fun z => (L ∘ₗ (GlobalTheory.CoefIrred.tenMul W).toLinearMap e v₀)
        (sqRep ℂ a (W v₀) (cEmb v₀.embedding (x z).1) (e v₀)) := by
      funext z
      have := rep_tenMul_update W v₀ (x z) (h2.1 z) e (e v₀)
      rw [Function.update_eq_self] at this
      exact congrArg L this
    change Φ _ ∈ ExpLe d ⊓ ExpGe (-d)
    rw [e3]
    exact h
  have h0 := (GlobalTheory.T.dualWeylModule_tensor_coefficient_universal (InfinitePlace E) a W (W.Sp ⧸ N) 0).unique (y₁ := N.mkQ) (y₂ := 0)
    (fun u => (Submodule.Quotient.mk_eq_zero N).2 (hN u)) (fun u => rfl)
  exact (Submodule.Quotient.mk_eq_zero N).1 (LinearMap.congr_fun h0 v)
