import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AAcrossOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalArtinCompNormCompatStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvable

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

section Res

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K L] [Algebra K Ω] [Algebra L Ω]
  [IsScalarTower K L Ω] {A : ValuationSubring Ω}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ine_res_iff (t : G L Ω) :
    (AlgEquiv.restrictScalarsHom K t : G K Ω) ∈ Ine (F := K) A ↔ t ∈ Ine (F := L) A := Iff.rfl

def ineRes : Ine (F := L) A →* Ine (F := K) A :=
  ((AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω).comp (Ine (F := L) A).subtype).codRestrict _ fun t =>
    (mem_ine_res_iff (K := K) (t : G L Ω)).2 t.2

variable [IsAlgClosure K Ω] [IsAlgClosure L Ω] {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 L)}
  {hK : IsPlaceOver A v} {hL : IsPlaceOver A w}

/- English proof (translation)
Establish `hV : IsOpen {t : Ine (F` using `L) A | ζ (aL (ineIncl hL t)) = 1} := haL.smooth hζ`. Take `⟨W, hW, hWV⟩` from `isOpen_induced_iff.1 hV`. Establish `h1W : (1 : G L Ω) ∈ W`. Establish `h1 : (1 : Ine (F` using `L) A) ∈ Subtype.val ⁻¹' W := by`. Rewrite using `[hWV]`.

Simplify using the standard rewrite rules. Conclude with `h1`. Take `⟨E, hE, hEW⟩` from `(krullTopology_mem_nhds_one_iff L Ω W).1 (hW.mem_nhds h1W)`. Use `haveI := hE`. Establish `hN : IsOpen ((Subgroup.map (AlgEquiv.restrictScalarsHom K) E.fixingSubgroup : Subgroup (G K Ω)) : Set (G K Ω))` using `GlobalTheory.KLift.isOpen_map_restrictScalars _ E.fixingSubgroup_isOpen`.

Use `IsSmooth.of_open (hN.preimage continuous_subtype_val) ?_ ?_` and prove the remaining obligations. Use `show ((1 : Ine (F := K) A) : G K Ω) ∈ Subgroup.map (AlgEquiv.restrictScalarsHom K) E.fixingSubgroup`. Conclude with `Subgroup.one_mem _`. Introduce `σ hσ`. Establish `hσ' : (σ : G K Ω) ∈ Subgroup.map (AlgEquiv.restrictScalarsHom K) E.fixingSubgroup` using `hσ`.

Take `⟨n, hn, hnσ⟩` from `Subgroup.mem_map.1 hσ'`. Establish `hnI : n ∈ Ine (F` using `L) A := (mem_ine_res_iff (K := K) n).1 (by rw [hnσ]; exact σ.2)`. Establish `hres : ineRes (K` using `K) (⟨n, hnI⟩ : Ine (F := L) A) = σ := Subtype.ext hnσ`. Establish `ht : (⟨n, hnI⟩ : Ine (F` using `L) A) ∈ {t : Ine (F := L) A | ζ (aL (ineIncl hL t)) = 1} := by`. Rewrite using `[← hWV]`.

Conclude with `hEW hn`. Rewrite using `[← hres, hθ]`. Conclude with `ht`.
-/
theorem isSmooth_of_ine [FiniteDimensional K L] {aL : Weil hL →* (w.adicCompletion L)ˣ} (haL : IsLocalArtin hL aL)
    {ζ : (w.adicCompletion L)ˣ →* ℂˣ} (hζ : IsSmoothChar ζ) (θ : Weil hK →* ℂˣ)
    (hθ : ∀ t : Ine (F := L) A, θ (ineIncl hK (ineRes (K := K) t)) = ζ (aL (ineIncl hL t))) : IsSmooth θ := by
  have hV : IsOpen {t : Ine (F := L) A | ζ (aL (ineIncl hL t)) = 1} := haL.smooth hζ
  obtain ⟨W, hW, hWV⟩ := isOpen_induced_iff.1 hV
  have h1W : (1 : G L Ω) ∈ W := by
    have h1 : (1 : Ine (F := L) A) ∈ Subtype.val ⁻¹' W := by
      rw [hWV]
      simp
    exact h1
  obtain ⟨E, hE, hEW⟩ := (krullTopology_mem_nhds_one_iff L Ω W).1 (hW.mem_nhds h1W)
  haveI := hE
  have hN : IsOpen ((Subgroup.map (AlgEquiv.restrictScalarsHom K) E.fixingSubgroup : Subgroup (G K Ω)) :
      Set (G K Ω)) := GlobalTheory.KLift.isOpen_map_restrictScalars _ E.fixingSubgroup_isOpen
  refine IsSmooth.of_open (hN.preimage continuous_subtype_val) ?_ ?_
  · show ((1 : Ine (F := K) A) : G K Ω) ∈ Subgroup.map (AlgEquiv.restrictScalarsHom K) E.fixingSubgroup
    exact Subgroup.one_mem _
  · intro σ hσ
    have hσ' : (σ : G K Ω) ∈ Subgroup.map (AlgEquiv.restrictScalarsHom K) E.fixingSubgroup := hσ
    obtain ⟨n, hn, hnσ⟩ := Subgroup.mem_map.1 hσ'
    have hnI : n ∈ Ine (F := L) A := (mem_ine_res_iff (K := K) n).1 (by rw [hnσ]; exact σ.2)
    have hres : ineRes (K := K) (⟨n, hnI⟩ : Ine (F := L) A) = σ := Subtype.ext hnσ
    have ht : (⟨n, hnI⟩ : Ine (F := L) A) ∈ {t : Ine (F := L) A | ζ (aL (ineIncl hL t)) = 1} := by
      rw [← hWV]
      exact hEW hn
    rw [← hres, hθ]
    exact ht

/- English proof (translation)
Take `⟨χ, hχ, hθχ⟩` from `haK.factor θ (isSmooth_of_ine haL hζ θ hθ)`. Use `⟨χ, hχ, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `haL.surj x`. Establish `hdeg : deg g = 0`. Establish `h` using `haL.ord_eq g`.

Rewrite `h` using `[hx]`. Use linear arithmetic over natural numbers and integers. Establish `hI : (g : G L Ω) ∈ Ine (F` using `L) A := deg_eq_zero_iff.1 hdeg`. Establish `hg : ineIncl hL (⟨g, hI⟩ : Ine (F` using `L) A) = g := Subtype.ext rfl`. Establish `key` using `GlobalTheory.T.localArtin_comp_norm_compat K L Ω A v w hK hL aK aL haK haL (ineIncl hK (ineRes (K := K) (⟨g, hI⟩ : Ine (F := L) A))) (ineIncl hL ⟨g, hI⟩) (fun _ => rfl)`.

Rewrite using `[← hg, ← hθ, hθχ, MonoidHom.comp_apply, key]`.
-/
theorem exists_char_of_ine [FiniteDimensional K L] [w.asIdeal.LiesOver v.asIdeal]
    {aK : Weil hK →* (v.adicCompletion K)ˣ} (haK : IsLocalArtin hK aK)
    {aL : Weil hL →* (w.adicCompletion L)ˣ} (haL : IsLocalArtin hL aL)
    {ζ : (w.adicCompletion L)ˣ →* ℂˣ} (hζ : IsSmoothChar ζ) (θ : Weil hK →* ℂˣ)
    (hθ : ∀ t : Ine (F := L) A, θ (ineIncl hK (ineRes (K := K) t)) = ζ (aL (ineIncl hL t))) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ, IsSmoothChar χ ∧ ∀ x : (w.adicCompletion L)ˣ,
      ord (w.adicCompletion L) x = 0 → ζ x = χ (GlobalTheory.BCChar.normU v w x) := by
  obtain ⟨χ, hχ, hθχ⟩ := haK.factor θ (isSmooth_of_ine haL hζ θ hθ)
  refine ⟨χ, hχ, fun x hx => ?_⟩
  obtain ⟨g, rfl⟩ := haL.surj x
  have hdeg : deg g = 0 := by
    have h := haL.ord_eq g
    rw [hx] at h
    omega
  have hI : (g : G L Ω) ∈ Ine (F := L) A := deg_eq_zero_iff.1 hdeg
  have hg : ineIncl hL (⟨g, hI⟩ : Ine (F := L) A) = g := Subtype.ext rfl
  have key := GlobalTheory.T.localArtin_comp_norm_compat K L Ω A v w hK hL aK aL haK haL
    (ineIncl hK (ineRes (K := K) (⟨g, hI⟩ : Ine (F := L) A))) (ineIncl hL ⟨g, hI⟩) (fun _ => rfl)
  rw [← hg, ← hθ, hθχ, MonoidHom.comp_apply, key]

end Res

end UpperTheory.V.Z.Win
