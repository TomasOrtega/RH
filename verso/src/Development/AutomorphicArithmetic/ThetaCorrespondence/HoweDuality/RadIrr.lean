import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
import Development.WeilBound.ThetaLifts.SphericalLattices.ThetaSubSup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInfAlt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianTransform
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsOrbitKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianIdentity

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.Lit.HoweDuality GlobalTheory.HoweGlobalPair

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL hI K hrel hst hne`. Establish `one_mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v)` using `by show At _ (mat 1 - 1)`. Establish `h1 : mat (1 : UA σ X.J) = 1` using `Matrix.ext fun i => congrFun rfl`. Rewrite using `[h1, sub_self]`. Introduce `_ _`.

Simplify using the standard rewrite rules. Establish `aug_le : augAt om v ≤ SB (Fin n × Fin d → Fv F v)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩`. Conclude with `Submodule.sub_mem _ hφ₁ hφ`.

Establish `key : ∀ P : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ P → Stable (opFin om v) P → P = relFin om v ∨ P = ⊤`. Introduce `P hP hPs`. Establish `hT : GlobalTheory.Published.ThetaSub om v (P.map (SB (Fin n × Fin d → Fv F v)).subtype)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz`.

Establish `hzS` using `aug_le hz`. Use `⟨⟨z, hzS⟩, hP ?_, rfl⟩` and prove the remaining obligations. Simplify `hz` using `[relFin]`. Introduce and unpack `_ ⟨k, -, rfl⟩`. Conclude with `k.2`.

Introduce and unpack `h hh _ ⟨k, hk, rfl⟩ φ₁ hφ₁ hA`. Establish `hφ₁eq : φ₁ = ω (1, h) k` using `(hL.acts 1 one_mem h hh k k.2 φ₁).mp hA`. Set `g : Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v))` to `{ toFun := fun x => ⟨ω (1, h) x, hL.pres 1 one_mem h hh x x.2⟩ map_add' := fun x y => by ext1; simp map_smul' := fun c x => by ext1; simp }`. Establish `hg : g ∈ opFin om v`. Use `⟨h, hh, fun φ => ?_⟩` and prove the remaining obligations.

Conclude with `(hL.acts 1 one_mem h hh φ φ.2 _).mpr rfl`. Use `⟨g k, hPs g hg k hk, ?_⟩` and prove the remaining obligations. Simplify using `[g, hφ₁eq]`. Break down `hI _ hT with h1 | h1` into its components or cases. Use `left`.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v`. Rewrite using `[← h1]`.

Conclude with `⟨x, hx, rfl⟩`. Simplify `hx'` using `[relFin]`. Introduce `hx`. Conclude with `hP hx`. Use `right`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ P.map (SB (Fin n × Fin d → Fv F v)).subtype`. Rewrite using `[h1]`. Conclude with `x.2`.

Take `⟨y, hy, hyx⟩` from `hx'`. Establish `hyx' : y = x` using `Subtype.ext hyx`. Rewrite using `[← hyx']`. Conclude with `hy`. Establish `hK : K = relFin om v`.

Break down `key K hrel hst with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hne`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s, s ∉ relFin om v := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hK, eq_top_iff]`. Introduce `x _`. Conclude with `hc x`.

Use `⟨s, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hP hPs hsP`. Break down `key P hP hPs with h | h` into its components or cases. Rewrite `hsP` using `[h]`. Conclude with `absurd hsP hs`.

Conclude with `h`. Introduce `k hk`. Use `⟨1, Subalgebra.one_mem _, rfl, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[hK]`. Simplify using `using hk`.
-/
theorem UpperTheory.Lit.HoweDuality.radIrr :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (PositivityTheory.ThK.Fn F n d v)}, PositivityTheory.ThK.IsLocRep M ψ om v ω ρ → PositivityTheory.Sph.IrrAt om v → ∀ K : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ K → Stable (opFin om v) K → K ≠ ⊤ → Rad (opFin om v) (relFin om v) K := by
  intro F E _ _ _ _ _ σ n d X W M ψ om v ω ρ hL hI K hrel hst hne
  have one_mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    show At _ (mat 1 - 1)
    have h1 : mat (1 : UA σ X.J) = 1 := Matrix.ext fun i => congrFun rfl
    rw [h1, sub_self]
    intro _ _
    simp
  have aug_le : augAt om v ≤ SB (Fin n × Fin d → Fv F v) := by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact Submodule.sub_mem _ hφ₁ hφ
  have key : ∀ P : Submodule ℂ ↥(SB (Fin n × Fin d → Fv F v)), relFin om v ≤ P →
      Stable (opFin om v) P → P = relFin om v ∨ P = ⊤ := by
    intro P hP hPs
    have hT : GlobalTheory.Published.ThetaSub om v (P.map (SB (Fin n × Fin d → Fv F v)).subtype) := by
      refine ⟨?_, ?_, ?_⟩
      · intro z hz
        have hzS := aug_le hz
        refine ⟨⟨z, hzS⟩, hP ?_, rfl⟩
        simpa [relFin] using hz
      · rintro _ ⟨k, -, rfl⟩
        exact k.2
      · rintro h hh _ ⟨k, hk, rfl⟩ φ₁ hφ₁ hA
        have hφ₁eq : φ₁ = ω (1, h) k := (hL.acts 1 one_mem h hh k k.2 φ₁).mp hA
        let g : Module.End ℂ ↥(SB (Fin n × Fin d → Fv F v)) :=
          { toFun := fun x => ⟨ω (1, h) x, hL.pres 1 one_mem h hh x x.2⟩
            map_add' := fun x y => by ext1; simp
            map_smul' := fun c x => by ext1; simp }
        have hg : g ∈ opFin om v := by
          refine ⟨h, hh, fun φ => ?_⟩
          exact (hL.acts 1 one_mem h hh φ φ.2 _).mpr rfl
        refine ⟨g k, hPs g hg k hk, ?_⟩
        simp [g, hφ₁eq]
    rcases hI _ hT with h1 | h1
    · left
      ext x
      constructor
      · intro hx
        have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ augAt om v := by
          rw [← h1]
          exact ⟨x, hx, rfl⟩
        simpa [relFin] using hx'
      · intro hx
        exact hP hx
    · right
      rw [eq_top_iff]
      intro x _
      have hx' : (x : (Fin n × Fin d → Fv F v) → ℂ) ∈ P.map (SB (Fin n × Fin d → Fv F v)).subtype := by
        rw [h1]
        exact x.2
      obtain ⟨y, hy, hyx⟩ := hx'
      have hyx' : y = x := Subtype.ext hyx
      rw [← hyx']
      exact hy
  have hK : K = relFin om v := by
    rcases key K hrel hst with h | h
    · exact h
    · exact absurd h hne
  obtain ⟨s, hs⟩ : ∃ s, s ∉ relFin om v := by
    by_contra hc
    push_neg at hc
    apply hne
    rw [hK, eq_top_iff]
    intro x _
    exact hc x
  refine ⟨s, ?_, ?_⟩
  · intro P hP hPs hsP
    rcases key P hP hPs with h | h
    · rw [h] at hsP
      exact absurd hsP hs
    · exact h
  · intro k hk
    refine ⟨1, Subalgebra.one_mem _, rfl, ?_⟩
    rw [hK] at hk
    simpa using hk
