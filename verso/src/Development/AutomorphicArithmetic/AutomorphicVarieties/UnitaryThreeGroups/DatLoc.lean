import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.KatoUse
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.GalOfCusp Matrix IsLocalRing
open UpperTheory.V UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.Alg UpperTheory.V.U3

/- English proof (translation)
Introduce `Ω _ _ _ K _ _ _ l _ c N _ e ψ D`. Establish `hι : D.ι = Loc.iota D.j`. Use extensionality with `σ x`. Apply `D.j.injective` to reduce the goal to its premises. Rewrite using `[Loc.iota_spec, ← D.ι_spec]`.

Take `⟨hemb, hrange, -, hmap, hcyc, -, -⟩` from `Loc.iotaFacts D.j`. Establish `hmem : ∀ x : Ω, x ∈ Loc.placeJ D.j ↔ Valued.v (D.j x) ≤ 1` using `fun x => Iff.rfl`. Establish `hA : (Loc.placeJ D.j).valuation (l : Ω) < 1`. Establish `hnot : (l : Ω)⁻¹ ∉ Loc.placeJ D.j`. Rewrite using `[hmem, map_inv₀, map_natCast, map_inv₀, PadicAlgCl.valuation_p, not_le]`.

Establish `hl : (1 : NNReal) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`. Simplify using `using hl`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hnot` to reduce the goal to its premises.

Establish `hle : (Loc.placeJ D.j).valuation (l : Ω) ≤ 1` using `((Loc.placeJ D.j).valuation_le_one_iff _).2 (natCast_mem _ l)`. Rewrite using `[← ValuationSubring.valuation_le_one_iff, map_inv₀, le_antisymm hle h, inv_one]`. Use `⟨Loc.placeJ D.j, hA, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hι]`. Conclude with `hrange`.

Rewrite using `[hι]`. Conclude with `hmap`. Rewrite using `[hι]`. Conclude with `hemb.injective`. Introduce `x`.

Rewrite using `[hmem, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]`. Introduce `σ`. Rewrite using `[hι]`. Conclude with `DFunLike.congr_fun (hcyc l) σ`. Introduce `A' hA'`.

Take `⟨-, -, -, -, -, -, -, hconj, -, hact⟩` from `ML.placeBasic Ω`. Take `⟨g, rfl⟩` from `hconj (Loc.placeJ D.j) A' l Fact.out hA hA'`. Conclude with `⟨g, (hact _ g).1, (hact _ g).2.1⟩`.
-/
theorem UpperTheory.V.U3.dat_loc :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
      {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ),
      ∃ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 ∧ D.ι.range = Dec (F := ℚ) A ∧ (Loc.Iq l).map D.ι = Ine (F := ℚ) A ∧
        Function.Injective D.ι ∧ (∀ x : Ω, x ∈ A ↔ ‖D.j x‖ ≤ 1) ∧ (∀ σ, cycZ ℚ Ω l (D.ι σ) = Loc.cyc l l σ) ∧
        ∀ A' : ValuationSubring Ω, A'.valuation (l : Ω) < 1 → ∃ g : G ℚ Ω,
          (∀ s, s ∈ Dec (F := ℚ) A' ↔ g⁻¹ * s * g ∈ Dec (F := ℚ) A) ∧ ∀ s, s ∈ Ine (F := ℚ) A' ↔ g⁻¹ * s * g ∈ Ine (F := ℚ) A := by
  intro Ω _ _ _ K _ _ _ l _ c N _ e ψ D
  have hι : D.ι = Loc.iota D.j := by
    ext σ x
    apply D.j.injective
    rw [Loc.iota_spec, ← D.ι_spec]
  obtain ⟨hemb, hrange, -, hmap, hcyc, -, -⟩ := Loc.iotaFacts D.j
  have hmem : ∀ x : Ω, x ∈ Loc.placeJ D.j ↔ Valued.v (D.j x) ≤ 1 := fun x => Iff.rfl
  have hA : (Loc.placeJ D.j).valuation (l : Ω) < 1 := by
    have hnot : (l : Ω)⁻¹ ∉ Loc.placeJ D.j := by
      rw [hmem, map_inv₀, map_natCast, map_inv₀, PadicAlgCl.valuation_p, not_le]
      have hl : (1 : NNReal) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      simpa using hl
    by_contra h
    push_neg at h
    apply hnot
    have hle : (Loc.placeJ D.j).valuation (l : Ω) ≤ 1 :=
      ((Loc.placeJ D.j).valuation_le_one_iff _).2 (natCast_mem _ l)
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, le_antisymm hle h, inv_one]
  refine ⟨Loc.placeJ D.j, hA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hι]; exact hrange
  · rw [hι]; exact hmap
  · rw [hι]; exact hemb.injective
  · intro x
    rw [hmem, ← NNReal.coe_le_coe, PadicAlgCl.valuation_coe, NNReal.coe_one]
  · intro σ
    rw [hι]
    exact DFunLike.congr_fun (hcyc l) σ
  · intro A' hA'
    obtain ⟨-, -, -, -, -, -, -, hconj, -, hact⟩ := ML.placeBasic Ω
    obtain ⟨g, rfl⟩ := hconj (Loc.placeJ D.j) A' l Fact.out hA hA'
    exact ⟨g, (hact _ g).1, (hact _ g).2.1⟩
