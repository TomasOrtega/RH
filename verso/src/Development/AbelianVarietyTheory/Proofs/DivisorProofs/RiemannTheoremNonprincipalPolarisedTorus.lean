import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQuotientAbelianByFinitePoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenyOfNcard
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionDescendsEtaleCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSuperlatticeOfRiemannFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeHomFiniteImageOfTrivialOnMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolUnifPullAlongGroupHomStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `g Λ Hm hd hf hH hpos hint`. Take `⟨Λ₁, N, Ef, hle, hN, hNΛ, hd₁, hf₁, hE, hbij⟩` from `GlobalTheory.T.exists_polarized_superlattice_of_riemann_form g Λ Hm hd hf hH hpos hint`. Take `⟨P, u, χ, hPg, hu, hAH, -, -⟩` from `GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd₁ hf₁ hH hpos hE hbij`. Establish `hNc : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Use `set e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) := fun z => u.ex ((N : ℂ)⁻¹ • z) with he`.

Establish `e_add : ∀ z w, e (z + w) = e z * e w` using `fun z w => by simp only [he, smul_add, u.ex_add]`. Establish `e_zero : e 0 = 1`. Establish `h` using `e_add 0 0`. Rewrite `h` using `[add_zero]`. Conclude with `(mul_eq_left.1 h.symm)`.

Establish `e_nsmul : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n`. Introduce `n z`. Proceed by induction on `n with`. Consider the case `zero => simp [e_zero]`. Consider the case `succ n ih => rw [Nat.cast_succ, add_smul, one_smul, e_add, ih, pow_succ]`.

Establish `e_N : ∀ z, e ((N : ℂ) • z) = u.ex z` using `fun z => by`. Simplify using `only [he, smul_smul, inv_mul_cancel₀ hNc, one_smul]`. Establish `e_sub : ∀ z w, e (z - w) * e w = e z` using `fun z w => by rw [← e_add, sub_add_cancel]`. Set `C : Subgroup (𝟙_ (Over (Sp ℂ)) ⟶ P.A)` to `{ carrier := e '' (Λ : Set (Fin g → ℂ)) mul_mem' := by`. Introduce and unpack `_ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩`.

Conclude with `⟨a + b, Λ.add_mem ha hb, e_add a b⟩`. Use the proof step `one_mem' := ⟨0, Λ.zero_mem, e_zero⟩`. Use the proof step `inv_mem' := by`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Use `⟨-a, Λ.neg_mem ha, ?_⟩` and prove the remaining obligations.

Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← e_add, neg_add_cancel, e_zero] }`. Establish `hCfin : Finite C`. Use `(GlobalTheory.T.finite_image_lattice_of_hom_trivial_on_multiples g Λ _ e N hd hf e_add hN fun l hl => by` as an intermediate fact. Rewrite using `[e_N, u.ker, hu]`.

Conclude with `hle hl).to_subtype`. Conclude with `this`. Establish `hA` using `P.isAb`. Use `hA.proper` as an intermediate fact. Use `hA.comm` as an intermediate fact.

Take `⟨A, _, ψ, hA', hψ, hψf, hψe, hψs, hker⟩` from `GlobalTheory.exists_quotient_abelian_by_finite_points ℂ P.A hA C hCfin`. Use `hA'.smooth` as an intermediate fact. Establish `hmon : IsMonHom (𝟙 P.A ^ N)` using `GlobalTheory.GrpTangent.mulN_eq_pow P.A _ ▸ GlobalTheory.GrpTangent.isMonHom_mulN P.A _`. Take `⟨⟨φ, hφ, hc⟩, -⟩` from `GlobalTheory.exists_monHom_factor_of_flat_surjective _ P.A A P.A ψ (𝟙 P.A ^ N) hψ hmon inferInstance hψs inferInstance fun T z hz => by`. Rewrite using `[MonObj.comp_pow, Category.comp_id]`.

Use `GlobalTheory.SS.PrincIsog.pow_eq_one_of_etale ψ N (fun y hy => ?_) T z hz` and prove the remaining obligations. Take `⟨c, ⟨l, hl, rfl⟩, rfl⟩` from `(hker ℂ (𝟙 _) y).1 hy`. Rewrite using `[← MonObj.comp_pow, ← e_nsmul, e_N, (u.ker l).2 (hu ▸ hle hl), MonObj.comp_one]`. Establish `htu : toUnit (Over.mk (𝟙 (Sp ℂ))) = 𝟙 (𝟙_ (Over (Sp ℂ)))` using `toUnit_unique _ _`. Set `exA : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A)` to `fun z => e z ≫ ψ`.

Establish `exA_add : ∀ z w, exA (z + w) = exA z * exA w` using `fun z w => by`. Simplify using `only [exA, e_add, MonObj.mul_comp]`. Establish `exA_onto : Function.Surjective exA`. Introduce `x`. Take `⟨b, hb⟩` from `GlobalTheory.SS.PrincIsog.exists_lift_point (F := ℂ) ψ.left x.left`.

Set `b' : 𝟙_ (Over (Sp ℂ)) ⟶ P.A` to `Over.homMk b (by`. Rewrite using `[← Over.w ψ, ← Category.assoc, hb]`. Conclude with `Over.w _)`. Establish `hb' : b' ≫ ψ = x` using `Over.OverMorphism.ext hb`. Take `⟨w, hw⟩` from `u.ex_onto b'`.

Conclude with `⟨(N : ℂ) • w, by simp only [exA, e_N, hw, hb']⟩`. Establish `exA_ker : ∀ z, exA z = 1 ↔ z ∈ Λ`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨c, ⟨l, hl, rfl⟩, hc'⟩` from `(hker ℂ (𝟙 _) (e z)).1 h`. Rewrite `hc'` using `[htu]`. Use `replace hc' : e z = e l := hc'.trans (Category.id_comp _)`. Establish `h1 : e (z - l) = 1`. Use `e_sub z l` as an intermediate fact.

Rewrite `this` using `[hc']`. Conclude with `mul_eq_right.1 this`. Establish `h2` using `(u.ker _).1 h1`. Rewrite `h2` using `[hu]`. Establish `h3` using `hNΛ _ h2`.

Rewrite `h3` using `[smul_smul, mul_inv_cancel₀ hNc, one_smul]`. Use `Λ.add_mem h3 hl` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis. Introduce `hz`. Conclude with `(hker ℂ (𝟙 _) (e z)).2 ⟨e z, ⟨z, hz, rfl⟩, by rw [htu]; exact (Category.id_comp _).symm⟩`.

Establish `hcl : Continuous (fun z : Fin g → ℂ => (N : ℂ)⁻¹ • z)` using `continuous_const_smul _`. Establish `exA_hol : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} ∧ DifferentiableOn ℂ (fun z => valAt' (exA z).left U f) {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U}`. Introduce `U f`. Establish `hs : {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} = (fun z => (N : ℂ)⁻¹ • z) ⁻¹' {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (ψ.left ⁻¹ᵁ U)}`. Use extensionality with `z`.

Simplify using `only [exA, he, Over.comp_left, Scheme.Hom.comp_preimage, Set.mem_setOf_eq, Set.mem_preimage]`. Establish `hv : (fun z => valAt' (exA z).left U f) = (fun w => valAt' (u.ex w).left (ψ.left ⁻¹ᵁ U) ((ψ.left.app U).hom f)) ∘ (fun z => (N : ℂ)⁻¹ • z)`. Use function extensionality and compare the values at `z`. Simplify using `only [Function.comp, exA, he, Over.comp_left, GlobalTheory.valAt'_comp]`. Use `⟨hs ▸ (u.hol _ ((ψ.left.app U).hom f)).1.preimage hcl, ?_⟩` and prove the remaining obligations.

Rewrite using `[hs, hv]`. Conclude with `(u.hol _ _).2.comp ((differentiable_id (𝕜 := ℂ) (E := Fin g → ℂ)).const_smul ((N : ℂ)⁻¹)).differentiableOn (fun z hz => hz)`. Establish `hcomp : ∀ z, exA z ≫ φ = u.ex z` using `fun z => by`. Simplify using `only [exA, Category.assoc, hc, MonObj.comp_pow, Category.comp_id]`. Rewrite using `[← e_nsmul, e_N]`.

Take `⟨uA, χA, hΛA, hAHA⟩` from `GlobalTheory.T.exists_holUnif_pull_along_groupHom A P.A φ P.L g u exA Λ Hm χ exA_add exA_onto exA_ker hd hf exA_hol hcomp (hu ▸ hle) hAH`. Establish `hsm : SmoothOfRelativeDimension g A.hom` using `GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover ℂ _ _ ψ.left A.hom g hψe hψs inferInstance (by rw [Over.w]; exact hPg ▸ P.smoothDim)`. Conclude with `⟨A, inferInstance, hA', hsm, P.L.pull φ.left, uA, χA, pull_isLB P.isLB _, hΛA, hAHA⟩`.
-/
theorem GlobalTheory.riemann_polarised_torus : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (A : Over (Sp ℂ)) (_ : GrpObj A), IsAbelianScheme A ∧ SmoothOfRelativeDimension g A.hom ∧
      ∃ (L : LB A.left) (u : HolUnif A L g) (χ : u.Λ → ℂ), L.IsLB ∧ (∀ w, w ∈ u.Λ ↔ w ∈ Λ) ∧ u.IsAH Hm χ := by
  intro g Λ Hm hd hf hH hpos hint
  obtain ⟨Λ₁, N, Ef, hle, hN, hNΛ, hd₁, hf₁, hE, hbij⟩ := GlobalTheory.T.exists_polarized_superlattice_of_riemann_form g Λ Hm hd hf hH hpos hint
  obtain ⟨P, u, χ, hPg, hu, hAH, -, -⟩ := GlobalTheory.principalTorus_algebraic g Λ₁ Hm Ef hd₁ hf₁ hH hpos hE hbij
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  set e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A) := fun z => u.ex ((N : ℂ)⁻¹ • z) with he
  have e_add : ∀ z w, e (z + w) = e z * e w := fun z w => by simp only [he, smul_add, u.ex_add]
  have e_zero : e 0 = 1 := by
    have h := e_add 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have e_nsmul : ∀ (n : ℕ) z, e ((n : ℂ) • z) = e z ^ n := by
    intro n z
    induction n with
    | zero => simp [e_zero]
    | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, e_add, ih, pow_succ]
  have e_N : ∀ z, e ((N : ℂ) • z) = u.ex z := fun z => by
    simp only [he, smul_smul, inv_mul_cancel₀ hNc, one_smul]
  have e_sub : ∀ z w, e (z - w) * e w = e z := fun z w => by rw [← e_add, sub_add_cancel]
  let C : Subgroup (𝟙_ (Over (Sp ℂ)) ⟶ P.A) :=
    { carrier := e '' (Λ : Set (Fin g → ℂ))
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, Λ.add_mem ha hb, e_add a b⟩
      one_mem' := ⟨0, Λ.zero_mem, e_zero⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        refine ⟨-a, Λ.neg_mem ha, ?_⟩
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← e_add, neg_add_cancel, e_zero] }
  have hCfin : Finite C := by
    have := (GlobalTheory.T.finite_image_lattice_of_hom_trivial_on_multiples g Λ _ e N hd hf e_add hN fun l hl => by
      rw [e_N, u.ker, hu]; exact hle hl).to_subtype
    exact this
  have hA := P.isAb
  have := hA.proper
  have := hA.comm
  obtain ⟨A, _, ψ, hA', hψ, hψf, hψe, hψs, hker⟩ := GlobalTheory.exists_quotient_abelian_by_finite_points ℂ P.A hA C hCfin
  have := hA'.smooth
  have hmon : IsMonHom (𝟙 P.A ^ N) := GlobalTheory.GrpTangent.mulN_eq_pow P.A _ ▸ GlobalTheory.GrpTangent.isMonHom_mulN P.A _
  obtain ⟨⟨φ, hφ, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ P.A A P.A ψ (𝟙 P.A ^ N) hψ hmon
    inferInstance hψs inferInstance fun T z hz => by
      rw [MonObj.comp_pow, Category.comp_id]
      refine GlobalTheory.SS.PrincIsog.pow_eq_one_of_etale ψ N (fun y hy => ?_) T z hz
      obtain ⟨c, ⟨l, hl, rfl⟩, rfl⟩ := (hker ℂ (𝟙 _) y).1 hy
      rw [← MonObj.comp_pow, ← e_nsmul, e_N, (u.ker l).2 (hu ▸ hle hl), MonObj.comp_one]
  have htu : toUnit (Over.mk (𝟙 (Sp ℂ))) = 𝟙 (𝟙_ (Over (Sp ℂ))) := toUnit_unique _ _
  let exA : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ A) := fun z => e z ≫ ψ
  have exA_add : ∀ z w, exA (z + w) = exA z * exA w := fun z w => by
    simp only [exA, e_add, MonObj.mul_comp]
  have exA_onto : Function.Surjective exA := by
    intro x
    obtain ⟨b, hb⟩ := GlobalTheory.SS.PrincIsog.exists_lift_point (F := ℂ) ψ.left x.left
    let b' : 𝟙_ (Over (Sp ℂ)) ⟶ P.A := Over.homMk b (by
      rw [← Over.w ψ, ← Category.assoc, hb]; exact Over.w _)
    have hb' : b' ≫ ψ = x := Over.OverMorphism.ext hb
    obtain ⟨w, hw⟩ := u.ex_onto b'
    exact ⟨(N : ℂ) • w, by simp only [exA, e_N, hw, hb']⟩
  have exA_ker : ∀ z, exA z = 1 ↔ z ∈ Λ := by
    intro z
    constructor
    · intro h
      obtain ⟨c, ⟨l, hl, rfl⟩, hc'⟩ := (hker ℂ (𝟙 _) (e z)).1 h
      rw [htu] at hc'
      replace hc' : e z = e l := hc'.trans (Category.id_comp _)
      have h1 : e (z - l) = 1 := by
        have := e_sub z l
        rw [hc'] at this
        exact mul_eq_right.1 this
      have h2 := (u.ker _).1 h1
      rw [hu] at h2
      have h3 := hNΛ _ h2
      rw [smul_smul, mul_inv_cancel₀ hNc, one_smul] at h3
      have := Λ.add_mem h3 hl
      rwa [sub_add_cancel] at this
    · intro hz
      exact (hker ℂ (𝟙 _) (e z)).2 ⟨e z, ⟨z, hz, rfl⟩, by rw [htu]; exact (Category.id_comp _).symm⟩
  have hcl : Continuous (fun z : Fin g → ℂ => (N : ℂ)⁻¹ • z) := continuous_const_smul _
  have exA_hol : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), IsOpen {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valAt' (exA z).left U f) {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} := by
    intro U f
    have hs : {z | ⊤ ≤ (exA z).left ⁻¹ᵁ U} =
        (fun z => (N : ℂ)⁻¹ • z) ⁻¹' {w | ⊤ ≤ (u.ex w).left ⁻¹ᵁ (ψ.left ⁻¹ᵁ U)} := by
      ext z
      simp only [exA, he, Over.comp_left, Scheme.Hom.comp_preimage, Set.mem_setOf_eq, Set.mem_preimage]
    have hv : (fun z => valAt' (exA z).left U f) =
        (fun w => valAt' (u.ex w).left (ψ.left ⁻¹ᵁ U) ((ψ.left.app U).hom f)) ∘ (fun z => (N : ℂ)⁻¹ • z) := by
      funext z
      simp only [Function.comp, exA, he, Over.comp_left, GlobalTheory.valAt'_comp]
    refine ⟨hs ▸ (u.hol _ ((ψ.left.app U).hom f)).1.preimage hcl, ?_⟩
    rw [hs, hv]
    exact (u.hol _ _).2.comp ((differentiable_id (𝕜 := ℂ) (E := Fin g → ℂ)).const_smul ((N : ℂ)⁻¹)).differentiableOn (fun z hz => hz)
  have hcomp : ∀ z, exA z ≫ φ = u.ex z := fun z => by
    simp only [exA, Category.assoc, hc, MonObj.comp_pow, Category.comp_id]
    rw [← e_nsmul, e_N]
  obtain ⟨uA, χA, hΛA, hAHA⟩ := GlobalTheory.T.exists_holUnif_pull_along_groupHom A P.A φ P.L g u exA Λ Hm χ exA_add exA_onto exA_ker hd hf
    exA_hol hcomp (hu ▸ hle) hAH
  have hsm : SmoothOfRelativeDimension g A.hom :=
    GlobalTheory.SmoothDescent.smoothOfRelativeDimension_of_etale_cover ℂ _ _ ψ.left A.hom g hψe hψs inferInstance
      (by rw [Over.w]; exact hPg ▸ P.smoothDim)
  exact ⟨A, inferInstance, hA', hsm, P.L.pull φ.left, uA, χA, pull_isLB P.isLB _, hΛA, hAHA⟩
