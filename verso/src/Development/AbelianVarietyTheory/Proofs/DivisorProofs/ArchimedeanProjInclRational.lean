import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyUniformizationExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatTorusAct

open scoped IntermediateField

/- English proof (translation)
Establish `hint : IsIntegral ℚ w`. Use `⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.monic_X_pow_add_C _ (by norm_num)`. Simplify using `[hw]`. Rewrite using `[IntermediateField.adjoin.finrank hint]`.

Establish `hdvd : minpoly ℚ w ∣ Polynomial.X ^ 2 + Polynomial.C (d : ℚ)` using `minpoly.dvd _ _ (by simp [hw])`. Establish `hle : (minpoly ℚ w).natDegree ≤ 2`. Use `Polynomial.natDegree_le_of_dvd hdvd (Polynomial.monic_X_pow_add_C (d : ℚ) (by norm_num)).ne_zero` as an intermediate fact. Rewrite `this` using `[Polynomial.natDegree_X_pow_add_C]`. Then use the resulting hypothesis. Establish `hpos` using `minpoly.natDegree_pos hint`.

Establish `hne : (minpoly ℚ w).natDegree ≠ 1`. Introduce `h1`. Take `⟨q, hq⟩` from `(minpoly.natDegree_eq_one_iff).1 h1`. Establish `h2 : ((q ^ 2 : ℚ) : E) = ((-(d : ℚ) : ℚ) : E)`. Rewrite using `[Rat.cast_pow]`.

Use `push_cast`. Establish `: (algebraMap ℚ E q) = (q : E)` using `rfl`. Rewrite using `[← this, hq, hw]`. Establish `h3 : q ^ 2 = -(d : ℚ)` using `Rat.cast_injective h2`. Establish `h4 : (0 : ℚ) < d` using `by exact_mod_cast hd`.

Use polynomial arithmetic with `[sq_nonneg q]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_adjoin_sqrt_neg {E : Type} [Field E] [CharZero E] (d : ℕ) (hd : 0 < d) (w : E) (hw : w ^ 2 = -(d : E)) :
    Module.finrank ℚ ℚ⟮w⟯ = 2 := by
  have hint : IsIntegral ℚ w := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hw]
  rw [IntermediateField.adjoin.finrank hint]
  have hdvd : minpoly ℚ w ∣ Polynomial.X ^ 2 + Polynomial.C (d : ℚ) := minpoly.dvd _ _ (by simp [hw])
  have hle : (minpoly ℚ w).natDegree ≤ 2 := by
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.monic_X_pow_add_C (d : ℚ) (by norm_num)).ne_zero
    rwa [Polynomial.natDegree_X_pow_add_C] at this
  have hpos := minpoly.natDegree_pos hint
  have hne : (minpoly ℚ w).natDegree ≠ 1 := by
    intro h1
    obtain ⟨q, hq⟩ := (minpoly.natDegree_eq_one_iff).1 h1
    have h2 : ((q ^ 2 : ℚ) : E) = ((-(d : ℚ) : ℚ) : E) := by
      rw [Rat.cast_pow]; push_cast
      have : (algebraMap ℚ E q) = (q : E) := rfl
      rw [← this, hq, hw]
    have h3 : q ^ 2 = -(d : ℚ) := Rat.cast_injective h2
    have h4 : (0 : ℚ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg q]
  omega

/- English proof (translation)
Establish `: f.toRatAlgHom = g.toRatAlgHom`. Use `IntermediateField.adjoin_algHom_ext ℚ ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality.

Conclude with `h`. Use extensionality with `x`. Conclude with `DFunLike.congr_fun this x`.
-/
theorem ringHom_ext_adjoin {E R : Type} [Field E] [CharZero E] [Field R] [CharZero R] (w : E)
    (f g : ℚ⟮w⟯ →+* R) (h : f (IntermediateField.AdjoinSimple.gen ℚ w) = g (IntermediateField.AdjoinSimple.gen ℚ w)) : f = g := by
  have : f.toRatAlgHom = g.toRatAlgHom := by
    refine IntermediateField.adjoin_algHom_ext ℚ ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h
  ext x
  exact DFunLike.congr_fun this x

/- English proof (translation)
Introduce `E _ _ _ I _ d φ hF c y hc`. Take `⟨hdp, -, -, -, -, hcard, hcm, w, hw, hφw⟩` from `hF`. Establish `hd : 0 < d` using `hdp.pos`. Establish `hI : Nonempty I` using `Fintype.card_pos_iff.1 (by omega)`. Take `⟨i₀⟩` from `hI`.

Set `δ : ℚ⟮w⟯` to `IntermediateField.AdjoinSimple.gen ℚ w`. Establish `hδ : δ ^ 2 = -(d : ℚ⟮w⟯)` using `Subtype.ext (by simpa [δ] using hw)`. Establish `hagree : ∀ i, (φ i).comp (algebraMap ℚ⟮w⟯ E) = (φ i₀).comp (algebraMap ℚ⟮w⟯ E)` using `fun i ↦ ringHom_ext_adjoin w _ _ (by show φ i w = φ i₀ w`. Rewrite using `[hφw, hφw])`. Take `⟨𝔠, X, U, -⟩` from `GlobalTheory.T.cm_abelian_variety_uniformization_exists ℚ⟮w⟯ d δ ((φ i₀).comp (algebraMap ℚ⟮w⟯ E)) (finrank_adjoin_sqrt_neg d hd w hw) hd hδ E I φ hcm hagree c y hc`.

Use `⟨𝔠, X, U, fun a ↦ ?_⟩` and prove the remaining obligations. Set `T : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ)` to `{ toFun := fun v j ↦ φ (U.e j) (a : E) * v j map_add' := fun v v' ↦ by ext j; simp [mul_add] map_smul' := fun s v ↦ by ext j; simp; ring }`. Establish `hT : ∀ v ∈ U.u.Λ, T v ∈ U.u.Λ`. Introduce `v hv`. Take `⟨x, hx, rfl⟩` from `(U.lat v).1 hv`.

Use `(U.lat _).2 ⟨(a : E) * x, mul_mem_lattice a.2 hx, ?_⟩` and prove the remaining obligations. Use extensionality with `j`. Simplify using `[T, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]`. Take `⟨α, hα, hαe⟩` from `GlobalTheory.RealMult.Obj.exists_isMonHom_of_map_lattice (FR E) 𝔠 X _ _ U.u T hT`. Conclude with `⟨α, hα, hαe⟩`.
-/
theorem exists_unif_act_orderC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (d : ℕ) (φ : I → E →+* ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∃ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
      ∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α := by
  intro E _ _ _ I _ d φ hF c y hc
  obtain ⟨hdp, -, -, -, -, hcard, hcm, w, hw, hφw⟩ := hF
  have hd : 0 < d := hdp.pos
  have hI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hI
  let δ : ℚ⟮w⟯ := IntermediateField.AdjoinSimple.gen ℚ w
  have hδ : δ ^ 2 = -(d : ℚ⟮w⟯) := Subtype.ext (by simpa [δ] using hw)
  have hagree : ∀ i, (φ i).comp (algebraMap ℚ⟮w⟯ E) = (φ i₀).comp (algebraMap ℚ⟮w⟯ E) := fun i ↦
    ringHom_ext_adjoin w _ _ (by
      show φ i w = φ i₀ w
      rw [hφw, hφw])
  obtain ⟨𝔠, X, U, -⟩ := GlobalTheory.T.cm_abelian_variety_uniformization_exists ℚ⟮w⟯ d δ ((φ i₀).comp (algebraMap ℚ⟮w⟯ E))
    (finrank_adjoin_sqrt_neg d hd w hw) hd hδ E I φ hcm hagree c y hc
  refine ⟨𝔠, X, U, fun a ↦ ?_⟩
  let T : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    { toFun := fun v j ↦ φ (U.e j) (a : E) * v j
      map_add' := fun v v' ↦ by ext j; simp [mul_add]
      map_smul' := fun s v ↦ by ext j; simp; ring }
  have hT : ∀ v ∈ U.u.Λ, T v ∈ U.u.Λ := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (U.lat v).1 hv
    refine (U.lat _).2 ⟨(a : E) * x, mul_mem_lattice a.2 hx, ?_⟩
    ext j
    simp [T, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  obtain ⟨α, hα, hαe⟩ := GlobalTheory.RealMult.Obj.exists_isMonHom_of_map_lattice (FR E) 𝔠 X _ _ U.u T hT
  exact ⟨α, hα, hαe⟩

end GlobalTheory.LatTorusAct
