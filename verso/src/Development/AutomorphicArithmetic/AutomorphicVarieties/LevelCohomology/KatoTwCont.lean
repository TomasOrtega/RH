import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.QuotRepMk

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato

/- English proof (translation)
Rewrite using `[Units.continuous_iff]`. Use `⟨h, ?_⟩` and prove the remaining obligations. Establish `: (fun x => ((f x)⁻¹ : Rˣ).val) = (fun s => (f s : R)) ∘ (fun x => x⁻¹)`. Use function extensionality and compare the values at `x`. Simplify using `[map_inv]`.

Rewrite using `[this]`. Conclude with `h.comp continuous_inv`.
-/
private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  have : (fun x => ((f x)⁻¹ : Rˣ).val) = (fun s => (f s : R)) ∘ (fun x => x⁻¹) := by
    funext x
    simp [map_inv]
  rw [this]
  exact h.comp continuous_inv

/- English proof (translation)
Apply `continuous_of_continuousAt_one` to reduce the goal to its premises. Establish `hev : (fun _ : Γ => (1 : H)) =ᶠ[nhds 1] f` using `Filter.eventually_of_mem (hU.mem_nhds h1) fun s hs => (h s hs).symm`. Conclude with `(continuousAt_const (y := (1 : H))).congr hev`.
-/
private theorem cont_of_ker {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (f : Γ →* H) (U : Set Γ) (hU : IsOpen U) (h1 : 1 ∈ U)
    (h : ∀ s ∈ U, f s = 1) : Continuous f := by
  apply continuous_of_continuousAt_one
  have hev : (fun _ : Γ => (1 : H)) =ᶠ[nhds 1] f :=
    Filter.eventually_of_mem (hU.mem_nhds h1) fun s hs => (h s hs).symm
  exact (continuousAt_const (y := (1 : H))).congr hev

/- English proof (translation)
Establish `hS : {ζ : Ω | ζ ^ M = 1} = ((Polynomial.nthRoots M (1 : Ω)).toFinset : Set Ω)`. Use extensionality with `ζ`. Simplify using `[Polynomial.mem_nthRoots (by omega : 0 < M)]`. Use `haveI : Finite ↥{ζ : Ω | ζ ^ M = 1} := by`. Rewrite using `[hS]`.

Use `infer_instance`. Set `E` to `IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ M = 1}`. Use `haveI : FiniteDimensional ℚ E := IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Use `cont_of_ker φ (E.fixingSubgroup : Set (G ℚ Ω)) E.fixingSubgroup_isOpen E.fixingSubgroup.one_mem ?_` and prove the remaining obligations. Introduce `s hs`.

Apply `hφ` to reduce the goal to its premises. Introduce `ζ hζ`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff E s).mp hs ζ (IntermediateField.subset_adjoin ℚ _ hζ)`.
-/
private theorem cont_kills {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (M : ℕ) (hM : 1 ≤ M) (φ : G ℚ Ω →* (Qbar l)ˣ) (hφ : KillsMu M φ) : Continuous φ := by
  classical
  have hS : {ζ : Ω | ζ ^ M = 1} = ((Polynomial.nthRoots M (1 : Ω)).toFinset : Set Ω) := by
    ext ζ
    simp [Polynomial.mem_nthRoots (by omega : 0 < M)]
  haveI : Finite ↥{ζ : Ω | ζ ^ M = 1} := by
    rw [hS]
    infer_instance
  let E := IntermediateField.adjoin ℚ {ζ : Ω | ζ ^ M = 1}
  haveI : FiniteDimensional ℚ E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine cont_of_ker φ (E.fixingSubgroup : Set (G ℚ Ω)) E.fixingSubgroup_isOpen E.fixingSubgroup.one_mem ?_
  intro s hs
  apply hφ
  intro ζ hζ
  exact (IntermediateField.mem_fixingSubgroup_iff E s).mp hs ζ (IntermediateField.subset_adjoin ℚ _ hζ)

/- English proof (translation)
Introduce `l _ Ω _ _ _ n W hW M hM φ hφ j`. Establish `hc1 : Continuous fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])` using `(Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)`. Establish `hc2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l])` using `continuous_subtype_val`. Establish `hcyc : Continuous (cycBar ℚ Ω l)`. Apply `cont_units` to reduce the goal to its premises.

Conclude with `(continuous_algebraMap ℚ_[l] (Qbar l)).comp (hc2.comp hc1)`. Establish `hχ : Continuous (cycBar ℚ Ω l ^ j * φ)`. Establish `e : ⇑(cycBar ℚ Ω l ^ j * φ) = fun s => (cycBar ℚ Ω l s) ^ j * φ s`. Use function extensionality and compare the values at `s`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `(hcyc.zpow j).mul (cont_kills M hM φ hφ)`. Apply `cont_units` to reduce the goal to its premises. Establish `e2 : (fun s => (((tw W (cycBar ℚ Ω l ^ j * φ)) s : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) = fun s => ((cycBar ℚ Ω l ^ j * φ) s : Qbar l) • (W s : Matrix (Fin n) (Fin n) (Qbar l))`. Use function extensionality and compare the values at `(tw_val W _)`.

Rewrite using `[e2]`. Conclude with `(Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hW)`.
-/
theorem UpperTheory.V.X.Kato.twCont :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (W : G ℚ Ω →* GL (Fin n) (Qbar l)), Continuous W → ∀ (M : ℕ), 1 ≤ M → ∀ φ : G ℚ Ω →* (Qbar l)ˣ, KillsMu M φ → ∀ j : ℤ, Continuous (tw W (cycBar ℚ Ω l ^ j * φ)) := by
  intro l _ Ω _ _ _ n W hW M hM φ hφ j
  have hc1 : Continuous fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    (Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l)
  have hc2 : Continuous fun x : ℤ_[l] => (x : ℚ_[l]) := continuous_subtype_val
  have hcyc : Continuous (cycBar ℚ Ω l) := by
    apply cont_units
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (hc2.comp hc1)
  have hχ : Continuous (cycBar ℚ Ω l ^ j * φ) := by
    have e : ⇑(cycBar ℚ Ω l ^ j * φ) = fun s => (cycBar ℚ Ω l s) ^ j * φ s := by
      funext s
      simp
    rw [e]
    exact (hcyc.zpow j).mul (cont_kills M hM φ hφ)
  apply cont_units
  have e2 : (fun s => (((tw W (cycBar ℚ Ω l ^ j * φ)) s : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) =
      fun s => ((cycBar ℚ Ω l ^ j * φ) s : Qbar l) • (W s : Matrix (Fin n) (Fin n) (Qbar l)) :=
    funext (tw_val W _)
  rw [e2]
  exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp hW)
