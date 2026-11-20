import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Classifies
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToZModPowKummerEqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsCrysAtCyclotomicZpowRestrictDecompositionGroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial GlobalTheory.GalOfCusp UpperTheory.V.Af

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨h, ?_⟩` and prove the remaining obligations. Simplify using `only [← map_inv]`. Conclude with `h.comp continuous_inv`.
-/
private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

/- English proof (translation)
Simplify using `only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]`.
-/
private theorem conj_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (g : GL (Fin n) k) (s : Γ) :
    ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Introduce `K Ω _ _ _ _ _ _ l _ n M m r j H`. Establish `hz : Continuous fun s : G K Ω => ((cycZ K Ω l s : ℤ_[l]ˣ) : ℤ_[l])` using `Units.continuous_val.comp (continuous_cycZ K Ω l)`. Establish `hcyc : Continuous fun s : G K Ω => (cycBar K Ω l s : Qbar l)` using `(continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)`. Establish `hχ : Continuous fun s : G K Ω => cycBar K Ω l s ^ j` using `(cont_units _ hcyc).zpow j`. Use `⟨?_, fun w hw => ?_, fun w hw => ?_⟩` and prove the remaining obligations.

Use `cont_units _ ?_` and prove the remaining obligations. Simplify using `only [tw_val]`. Conclude with `(Units.continuous_val.comp hχ).smul (Units.continuous_val.comp H.cont)`. Take `⟨A, hA, χ, hk, g, hg⟩` from `H.away w hw`. Use `⟨A, hA, χ, hk, g, fun s hs => ?_⟩` and prove the remaining obligations.

Establish `h1 : cycBar K Ω l s = 1`. Simplify using `only [cycBar, MonoidHom.comp_apply, GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hA hw hs, map_one]`. Establish `h2 : (cycBar K Ω l ^ j) s = 1` using `by show cycBar K Ω l s ^ j = 1`. Rewrite using `[h1, one_zpow]`. Rewrite using `[conj_tw, h2, Units.val_one, one_smul, hg s hs]`.

Take `⟨A, hA, χ, κ, hk, ⟨g, hg⟩, hκ, hor⟩` from `H.above w hw`. Use `⟨A, hA, χ, fun i => κ i * (cycBar K Ω l ^ j).comp (Dec (F := K) A).subtype, hk, ⟨g, fun s => ⟨fun a b hab => ?_, fun a => ?_⟩⟩, fun i s hs => ?_, ?_⟩` and prove the remaining obligations. Use `(hg s).1 a b hab show ((g * tw r _ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) a b = 0` as an intermediate fact. Rewrite using `[conj_tw, Matrix.smul_apply]`. Conclude with `smul_eq_zero_of_right _ this`.

Use `(hg s).2 a show ((g * tw r _ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) a a = _` as an intermediate fact. Rewrite using `[conj_tw, Matrix.smul_apply, smul_eq_mul, this]`. Conclude with `mul_comm _ _`. Use `show κ i s * cycBar K Ω l s ^ j = _`. Rewrite using `[hκ i s hs, zpow_add, mul_right_comm]`.

Break down `hor with h | ⟨O, _, _, _, Bw, hI, hP⟩` into its components or cases. Use `left`. Introduce `a b e`. Apply `h a b` to reduce the goal to its premises. Rewrite `e` using `[mul_right_comm]`.

Conclude with `mul_right_cancel e`. Use `right`. Take `⟨T⟩` from `UpperTheory.V.Loc.tiedP l`. Conclude with `⟨O, _, _, _, Bw, hI, GlobalTheory.HodgeOfTrue.potCrys_twistBy T Bw ((cycBar K Ω l ^ j).comp (Dec (F := K) A).subtype) _ hP (UpperTheory.isCrysAt_cyclotomic_zpow_restrict_decompositionGroup K Ω l A O Bw j)⟩`.
-/
theorem UpperTheory.level_twist_cyclotomic_pow :
    ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n M : ℕ) (m : Fin n → ℤ) (r : G K Ω →* GL (Fin n) (Qbar l)) (j : ℤ), Level l M m r → Level l M (fun i => m i + j) (tw r (cycBar K Ω l ^ j)) := by
  intro K Ω _ _ _ _ _ _ l _ n M m r j H
  have hz : Continuous fun s : G K Ω => ((cycZ K Ω l s : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.continuous_val.comp (continuous_cycZ K Ω l)
  have hcyc : Continuous fun s : G K Ω => (cycBar K Ω l s : Qbar l) :=
    (continuous_algebraMap ℚ_[l] (PadicAlgCl l)).comp (continuous_subtype_val.comp hz)
  have hχ : Continuous fun s : G K Ω => cycBar K Ω l s ^ j := (cont_units _ hcyc).zpow j
  refine ⟨?_, fun w hw => ?_, fun w hw => ?_⟩
  · refine cont_units _ ?_
    simp only [tw_val]
    exact (Units.continuous_val.comp hχ).smul (Units.continuous_val.comp H.cont)
  · obtain ⟨A, hA, χ, hk, g, hg⟩ := H.away w hw
    refine ⟨A, hA, χ, hk, g, fun s hs => ?_⟩
    have h1 : cycBar K Ω l s = 1 := by
      simp only [cycBar, MonoidHom.comp_apply, GlobalTheory.WeilDeligne.cycZ_of_mem_Ine hA hw hs, map_one]
    have h2 : (cycBar K Ω l ^ j) s = 1 := by
      show cycBar K Ω l s ^ j = 1
      rw [h1, one_zpow]
    rw [conj_tw, h2, Units.val_one, one_smul, hg s hs]
  · obtain ⟨A, hA, χ, κ, hk, ⟨g, hg⟩, hκ, hor⟩ := H.above w hw
    refine ⟨A, hA, χ, fun i => κ i * (cycBar K Ω l ^ j).comp (Dec (F := K) A).subtype, hk, ⟨g, fun s => ⟨fun a b hab => ?_, fun a => ?_⟩⟩,
      fun i s hs => ?_, ?_⟩
    · have := (hg s).1 a b hab
      show ((g * tw r _ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) a b = 0
      rw [conj_tw, Matrix.smul_apply]
      exact smul_eq_zero_of_right _ this
    · have := (hg s).2 a
      show ((g * tw r _ s * g⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) a a = _
      rw [conj_tw, Matrix.smul_apply, smul_eq_mul, this]
      exact mul_comm _ _
    · show κ i s * cycBar K Ω l s ^ j = _
      rw [hκ i s hs, zpow_add, mul_right_comm]
    · rcases hor with h | ⟨O, _, _, _, Bw, hI, hP⟩
      · left
        intro a b e
        apply h a b
        rw [mul_right_comm] at e
        exact mul_right_cancel e
      · right
        obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
        exact ⟨O, _, _, _, Bw, hI, GlobalTheory.HodgeOfTrue.potCrys_twistBy T Bw
          ((cycBar K Ω l ^ j).comp (Dec (F := K) A).subtype) _ hP (UpperTheory.isCrysAt_cyclotomic_zpow_restrict_decompositionGroup K Ω l A O Bw j)⟩
