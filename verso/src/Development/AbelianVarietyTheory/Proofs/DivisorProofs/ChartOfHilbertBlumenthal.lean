import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLevelStructureComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelStructureLiftNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLocalFactorizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothDetGeneratedCoverStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An

/- English proof (translation)
Introduce `I _ n J`. Establish `hπ : ∀ a : ℂ, J.π (algebraMap ℂ J.B a) = a`. Introduce `a`. Rewrite using `[J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul]`. Simplify using the standard rewrite rules.

Establish `hnil : ∀ x ∈ RingHom.ker J.π, IsNilpotent x`. Introduce `x hx`. Take `⟨N, hN⟩` from `J.nil`. Use `⟨N, ?_⟩` and prove the remaining obligations. Use `hN (List.replicate N (1, x)) (by` as an intermediate fact.

Introduce `p hp; rw [List.eq_of_mem_replicate hp]; exact hx) (by simp)`. Simplify `this` using `[J.κ.dpow_one hx]`. Use `⟨?_, hπ, hnil⟩` and prove the remaining obligations. Use `haveI : Nontrivial J.B := RingHom.domain_nontrivial J.π`. Establish `key : ∀ a : J.B, a ∈ nonunits J.B → J.π a = 0`.

Introduce `a ha`. Assume the negation of the conclusion as `h0`. Apply `ha` to reduce the goal to its premises. Establish `hu : IsUnit (algebraMap ℂ J.B (J.π a))` using `(IsUnit.mk0 _ h0).map _`. Establish `hn : IsNilpotent (a - algebraMap ℂ J.B (J.π a))` using `hnil _ (by simp [RingHom.mem_ker, hπ])`.

Use `hn.isUnit_add_left_of_commute hu (Commute.all _ _)` as an intermediate fact. Simplify using `using this`. Use `IsLocalRing.of_nonunits_add fun a b ha hb ↦ ?_` and prove the remaining obligations. Introduce `hab`. Establish `h1` using `hab.map J.π`.

Rewrite `h1` using `[map_add, key a ha, key b hb, add_zero]`. Conclude with `not_isUnit_zero h1`.
-/
theorem jetRing_local_nil : ∀ (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n),
    IsLocalRing J.B ∧ (∀ a : ℂ, J.π (algebraMap ℂ J.B a) = a) ∧ ∀ x ∈ RingHom.ker J.π, IsNilpotent x := by
  intro I _ n J
  have hπ : ∀ a : ℂ, J.π (algebraMap ℂ J.B a) = a := by
    intro a
    rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul]
    simp
  have hnil : ∀ x ∈ RingHom.ker J.π, IsNilpotent x := by
    intro x hx
    obtain ⟨N, hN⟩ := J.nil
    refine ⟨N, ?_⟩
    have := hN (List.replicate N (1, x)) (by
      intro p hp; rw [List.eq_of_mem_replicate hp]; exact hx) (by simp)
    simpa [J.κ.dpow_one hx] using this
  refine ⟨?_, hπ, hnil⟩
  haveI : Nontrivial J.B := RingHom.domain_nontrivial J.π
  have key : ∀ a : J.B, a ∈ nonunits J.B → J.π a = 0 := by
    intro a ha
    by_contra h0
    apply ha
    have hu : IsUnit (algebraMap ℂ J.B (J.π a)) := (IsUnit.mk0 _ h0).map _
    have hn : IsNilpotent (a - algebraMap ℂ J.B (J.π a)) :=
      hnil _ (by simp [RingHom.mem_ker, hπ])
    have := hn.isUnit_add_left_of_commute hu (Commute.all _ _)
    simpa using this
  refine IsLocalRing.of_nonunits_add fun a b ha hb ↦ ?_
  intro hab
  have h1 := hab.map J.π
  rw [map_add, key a ha, key b hb, add_zero] at h1
  exact not_isUnit_zero h1

/- English proof (translation)
Introduce `H F _ _ _ 𝔠 R _ _ X' β`. Take `⟨M, s, U, α, hfine, -, -, -, -, -, ⟨V, -, hV, hdisc, -⟩, -⟩` from `H F 𝔠 3 le_rfl`. Establish `h3 : IsUnit ((Int.castRingHom ℂ) 3)`. Rewrite using `[isUnit_iff_ne_zero]`. Evaluate the numerical expressions.

Set `ι₀ : Localization.Away (3 : ℤ) →+* ℂ` to `IsLocalization.Away.lift (3 : ℤ) h3`. Take `⟨b, ⟨hbs, φ, hφ, -⟩, -⟩` from `hfine (Sp R) (spMap ((algebraMap ℂ R).comp ι₀)) X' β`. Use `⟨M, s, U, V, b, φ, ι₀, hφ, hV, ?_, hbs⟩` and prove the remaining obligations. Introduce `x`. Apply `hdisc` to reduce the goal to its premises.

Establish `hd : IsUnit ((NumberField.discr F : ℤ) : R)`. Rewrite using `[← map_intCast (algebraMap ℂ R)]`. Conclude with `(IsUnit.mk0 _ (by exact_mod_cast NumberField.discr_ne_zero F)).map _`. Set `e` to `(Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv`. Establish `hu : IsUnit ((NumberField.discr F : ℤ) : Γ(Sp R, ⊤))`.

Use `hd.map e.symm.toRingHom` as an intermediate fact. Simplify `this` using `[map_intCast]`. Establish `hx : x ∈ b ⁻¹ᵁ M.basicOpen ((NumberField.discr F : ℤ) : Γ(M, ⊤))`. Rewrite using `[Scheme.preimage_basicOpen, map_intCast]`. Establish `hu' : IsUnit ((NumberField.discr F : ℤ) : Γ(Sp R, b ⁻¹ᵁ ⊤))`.

Use `hu.map ((Sp R).presheaf.map (homOfLE (le_top : b ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom` as an intermediate fact. Rewrite `this` using `[map_intCast]`. Then use the resulting hypothesis. Rewrite using `[Scheme.basicOpen_of_isUnit _ hu']`. Discharge the goal by the elementary cases of `trivial`. Conclude with `hx`.
-/
theorem exists_smooth_modulus_point : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (R : Type) [CommRing R] [Algebra ℂ R] (X' : Obj F 𝔠 (Sp R)), X'.Level 3 →
    ∃ (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (3 : ℤ))) (U : Obj F 𝔠 M) (V : M.Opens) (b : Sp R ⟶ M)
      (φ : X'.A.left ⟶ U.A.left) (ι₀ : Localization.Away (3 : ℤ) →+* ℂ),
      X'.IsPullBy U b φ ∧ SmoothOfRelativeDimension (Module.finrank ℚ F) (V.ι ≫ s) ∧ (∀ x, b.base x ∈ V) ∧
      b ≫ s = spMap ((algebraMap ℂ R).comp ι₀) := by
  intro H F _ _ _ 𝔠 R _ _ X' β
  obtain ⟨M, s, U, α, hfine, -, -, -, -, -, ⟨V, -, hV, hdisc, -⟩, -⟩ := H F 𝔠 3 le_rfl
  have h3 : IsUnit ((Int.castRingHom ℂ) 3) := by
    rw [isUnit_iff_ne_zero]; norm_num
  let ι₀ : Localization.Away (3 : ℤ) →+* ℂ := IsLocalization.Away.lift (3 : ℤ) h3
  obtain ⟨b, ⟨hbs, φ, hφ, -⟩, -⟩ := hfine (Sp R) (spMap ((algebraMap ℂ R).comp ι₀)) X' β
  refine ⟨M, s, U, V, b, φ, ι₀, hφ, hV, ?_, hbs⟩
  intro x
  apply hdisc
  have hd : IsUnit ((NumberField.discr F : ℤ) : R) := by
    rw [← map_intCast (algebraMap ℂ R)]
    exact (IsUnit.mk0 _ (by exact_mod_cast NumberField.discr_ne_zero F)).map _
  let e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  have hu : IsUnit ((NumberField.discr F : ℤ) : Γ(Sp R, ⊤)) := by
    have := hd.map e.symm.toRingHom
    simpa [map_intCast] using this
  have hx : x ∈ b ⁻¹ᵁ M.basicOpen ((NumberField.discr F : ℤ) : Γ(M, ⊤)) := by
    rw [Scheme.preimage_basicOpen, map_intCast]
    have hu' : IsUnit ((NumberField.discr F : ℤ) : Γ(Sp R, b ⁻¹ᵁ ⊤)) := by
      have := hu.map ((Sp R).presheaf.map (homOfLE (le_top : b ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom
      rwa [map_intCast] at this
    rw [Scheme.basicOpen_of_isUnit _ hu']
    trivial
  exact hx

/- English proof (translation)
Introduce `H F _ _ _ 𝔠 I _ n J X'`. Take `⟨hloc, hπ, hnil⟩` from `jetRing_local_nil I n J`. Set `π : J.B →ₐ[ℂ] ℂ` to `{ J.π with commutes' := hπ }`. Take `⟨X₀, i₀, h₀⟩` from `Obj.exists_isPullBy X' (spMap (π : J.B →+* ℂ))`. Take `⟨α₀⟩` from `GlobalTheory.T.nonempty_level_structure_complex F 𝔠 3 (by norm_num) X₀`.

Take `⟨β⟩` from `GlobalTheory.T.level_structure_lift_nilpotent F 𝔠 3 (by norm_num) J.B π hnil X' X₀ i₀ h₀ α₀`. Take `⟨M, s, U, V, b, φ, ι₀, hφ, hV, hb, hbs⟩` from `exists_smooth_modulus_point H.1 F 𝔠 J.B X' β`. Take `⟨B, _, _, _, g, j, hg⟩` from `GlobalTheory.T.exists_smooth_local_factorization _ ι₀ M s V _ hV J.B b hb hbs`. Take `⟨X₁, φ₁, h₁⟩` from `Obj.exists_isPullBy U g`. Rewrite `hφ` using `[← hg]`.

Take `⟨ψ, hψ, -⟩` from `hφ.cancel h₁`. Take `⟨B', _, _, _, X₂, δ, k, j', q, hq, hk⟩` from `GlobalTheory.T.exists_smooth_det_generated_cover F 𝔠 B J.B j X₁`. Establish `e : spMap (j : B →+* J.B) = spMap (j' : B' →+* J.B) ≫ spMap (k : B →+* B')`. Rewrite using `[← hk]`. Use `show Spec.map _ = Spec.map _ ≫ Spec.map _`.

Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite `hψ` using `[e]`. Take `⟨ψ', hψ', -⟩` from `hψ.cancel hq`. Conclude with `⟨B', _, _, inferInstance, X₂, δ, j', ψ', hψ'⟩`.
-/
theorem chart_of_hilbertBlumenthal : GlobalTheory.Published.HilbertBlumenthal → Chart := by
  intro H F _ _ _ 𝔠 I _ n J X'
  obtain ⟨hloc, hπ, hnil⟩ := jetRing_local_nil I n J
  let π : J.B →ₐ[ℂ] ℂ := { J.π with commutes' := hπ }
  obtain ⟨X₀, i₀, h₀⟩ := Obj.exists_isPullBy X' (spMap (π : J.B →+* ℂ))
  obtain ⟨α₀⟩ := GlobalTheory.T.nonempty_level_structure_complex F 𝔠 3 (by norm_num) X₀
  obtain ⟨β⟩ := GlobalTheory.T.level_structure_lift_nilpotent F 𝔠 3 (by norm_num) J.B π hnil X' X₀ i₀ h₀ α₀
  obtain ⟨M, s, U, V, b, φ, ι₀, hφ, hV, hb, hbs⟩ := exists_smooth_modulus_point H.1 F 𝔠 J.B X' β
  obtain ⟨B, _, _, _, g, j, hg⟩ := GlobalTheory.T.exists_smooth_local_factorization _ ι₀ M s V _ hV J.B b hb hbs
  obtain ⟨X₁, φ₁, h₁⟩ := Obj.exists_isPullBy U g
  rw [← hg] at hφ
  obtain ⟨ψ, hψ, -⟩ := hφ.cancel h₁
  obtain ⟨B', _, _, _, X₂, δ, k, j', q, hq, hk⟩ := GlobalTheory.T.exists_smooth_det_generated_cover F 𝔠 B J.B j X₁
  have e : spMap (j : B →+* J.B) = spMap (j' : B' →+* J.B) ≫ spMap (k : B →+* B') := by
    rw [← hk]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  rw [e] at hψ
  obtain ⟨ψ', hψ', -⟩ := hψ.cancel hq
  exact ⟨B', _, _, inferInstance, X₂, δ, j', ψ', hψ'⟩

end GlobalTheory.LatJet.An
