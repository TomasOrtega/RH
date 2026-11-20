import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Const

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `Rder`. Simplify using the standard rewrite rules.
-/
theorem Rder_const (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) :
    Rder θ V τ Z (fun _ => c) = fun _ => 0 := by
  funext g
  unfold Rder
  simp

/- English proof (translation)
Use function extensionality and compare the values at `g`. Unfold `RderC`. Simplify using `[Rder_const]`.
-/
theorem RderC_const (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) (c : ℂ) :
    RderC θ V τ Z (fun _ => c) = fun _ => 0 := by
  funext g
  unfold RderC
  simp [Rder_const]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨c, rfl⟩`. Consider the case `cons f l ih`. Take `⟨c1, h1⟩` from `ih (fun g hg => hl g (by simp [hg]))`. Take `⟨c2, h2⟩` from `hl f (by simp) c1`.

Conclude with `⟨c2, by simp only [List.foldr_cons, h1, h2]⟩`.
-/
theorem foldr_const (l : List ((GA D V → ℂ) → (GA D V → ℂ)))
    (hl : ∀ f ∈ l, ∀ c : ℂ, ∃ c' : ℂ, f (fun _ => c) = fun _ => c') (c : ℂ) :
    ∃ c' : ℂ, l.foldr (fun f acc => f acc) (fun _ => c) = fun _ => c' := by
  induction l with
  | nil => exact ⟨c, rfl⟩
  | cons f l ih =>
    obtain ⟨c1, h1⟩ := ih (fun g hg => hl g (by simp [hg]))
    obtain ⟨c2, h2⟩ := hl f (by simp) c1
    exact ⟨c2, by simp only [List.foldr_cons, h1, h2]⟩

/- English proof (translation)
Unfold `gelf`. Apply `Finset.sum_induction _ (fun F => ∃ c', F = fun _ => c')` to reduce the goal to its premises. Introduce and unpack `_ _ ⟨a, rfl⟩ ⟨b, rfl⟩`. Conclude with `⟨a + b, rfl⟩`. Conclude with `⟨0, rfl⟩`.

Introduce `idx _`. Apply `foldr_const` to reduce the goal to its premises. Introduce `f hf c0`. Rewrite `hf` using `[List.mem_ofFn]`. Take `⟨a, rfl⟩` from `hf`.

Conclude with `⟨0, RderC_const θ V τ _ c0⟩`.
-/
theorem gelf_const (τ : D.what₂.Tau) (k : ℕ) (c : ℂ) : ∃ c' : ℂ, gelf θ V τ k (fun _ => c) = fun _ => c' := by
  unfold gelf
  apply Finset.sum_induction _ (fun F => ∃ c', F = fun _ => c')
  · rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, rfl⟩
  · exact ⟨0, rfl⟩
  · intro idx _
    apply foldr_const
    intro f hf c0
    rw [List.mem_ofFn] at hf
    obtain ⟨a, rfl⟩ := hf
    exact ⟨0, RderC_const θ V τ _ c0⟩

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨c, rfl⟩`. Consider the case `cons p l ih`. Take `⟨c1, h1⟩` from `ih`. Conclude with `⟨0, by simp only [List.foldr_cons, h1, Rder_const]⟩`.
-/
theorem foldrRder_const (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (c : ℂ) :
    ∃ c' : ℂ, l.foldr (fun p f => Rder θ V p.1 p.2 f) (fun _ => c) = fun _ => c' := by
  induction l with
  | nil => exact ⟨c, rfl⟩
  | cons p l ih =>
    obtain ⟨c1, h1⟩ := ih
    exact ⟨0, by simp only [List.foldr_cons, h1, Rder_const]⟩

/- English proof (translation)
Introduce `_ _ _` and use `rfl level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩ cont := continuous_const smooth := fun _ _ _ _ _ => contDiff_const zfin := by refine ⟨Submodule.span ℂ {fun _ => (1 : ℂ)}, FiniteDimensional.span_singleton ℂ _, ?_, ?_⟩ · exact Submodule.mem_span_singleton.2 ⟨c, by funext g; simp⟩ …`.
-/
theorem isAutFunSm_const (c : ℂ) : IsAutFunSm θ V (fun _ => c) where
  left := fun _ _ _ => rfl
  level := ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩
  cont := continuous_const
  smooth := fun _ _ _ _ _ => contDiff_const
  zfin := by
    refine ⟨Submodule.span ℂ {fun _ => (1 : ℂ)}, FiniteDimensional.span_singleton ℂ _, ?_, ?_⟩
    · exact Submodule.mem_span_singleton.2 ⟨c, by funext g; simp⟩
    · intro τ k f hf
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hf
      have e : (a • fun _ : GA D V => (1 : ℂ)) = fun _ => a := by funext g; simp
      obtain ⟨c', hc'⟩ := gelf_const θ V τ k a
      rw [e, hc']
      exact Submodule.mem_span_singleton.2 ⟨c', by funext g; simp⟩
  growth := by
    refine ⟨0, fun l _ x => ?_⟩
    obtain ⟨c', hc'⟩ := foldrRder_const θ V l c
    exact ⟨‖c'‖, fun g _ => by rw [hc', pow_zero, mul_one]⟩

end Const

/- English proof (translation)
Take `⟨⟨θ, hθ⟩, h⟩` from `sm`. Establish `hr` using `h θ hθ V h1`. Establish `hc : (fun _ => c) ∈ Set.range ⇑(T.ev V)`. Rewrite using `[hr]`. Conclude with `isAutFunSm_const θ V c`.

Take `⟨F, hF⟩` from `hc`. Conclude with `⟨F, hF⟩`.
-/
theorem ThetaTied.exists_const {X : ThetaX D} (T : ThetaTied D X) (sm : ThetaSmoothnessCondition T) (V : HSp D) (h1 : V.SigOK)
    (c : ℂ) : ∃ F : X.AF V, T.ev V F = fun _ => c := by
  obtain ⟨⟨θ, hθ⟩, h⟩ := sm
  have hr := h θ hθ V h1
  have hc : (fun _ => c) ∈ Set.range ⇑(T.ev V) := by
    rw [hr]
    exact isAutFunSm_const θ V c
  obtain ⟨F, hF⟩ := hc
  exact ⟨F, hF⟩

/- English proof (translation)
Take `⟨F1, hF1⟩` from `T.exists_const sm V h1 1`. Take `⟨F0, hF0⟩` from `T.exists_const sm V h1 0`. Use `⟨F1, F0, fun h => ?_⟩` and prove the remaining obligations. Establish `h'` using `congrArg (fun F => T.ev V F 1) h`. Simplify using `[hF1, hF0] at h'`.
-/
theorem ThetaTied.nontrivial {X : ThetaX D} (T : ThetaTied D X) (sm : ThetaSmoothnessCondition T) (V : HSp D) (h1 : V.SigOK) :
    Nontrivial (X.AF V) := by
  obtain ⟨F1, hF1⟩ := T.exists_const sm V h1 1
  obtain ⟨F0, hF0⟩ := T.exists_const sm V h1 0
  refine ⟨F1, F0, fun h => ?_⟩
  have h' := congrArg (fun F => T.ev V F 1) h
  simp [hF1, hF0] at h'

/- English proof (translation)
Unfold `VolTieG at h`. Unfold `Formalism.MainNotions.StandardLattice.VolTie`. Introduce `W P Q hW hsig`. Establish `e1 : (fun ρ => (W.sig (tauE D ρ)).1) = fun _ => P`. Use function extensionality and compare the values at `ρ`.

Rewrite using `[hsig]`. Establish `e2 : (fun ρ => (W.sig (tauE D ρ)).2) = fun _ => Q`. Use function extensionality and compare the values at `ρ`. Rewrite using `[hsig]`. Establish `h'` using `h W hW`.

Rewrite `h'` using `[e1, e2]`. Conclude with `h'`.
-/
theorem VolTieG.volTie (h : VolTieG D) : Formalism.MainNotions.StandardLattice.VolTie D := by
  unfold VolTieG at h
  unfold Formalism.MainNotions.StandardLattice.VolTie
  intro W P Q hW hsig
  have e1 : (fun ρ => (W.sig (tauE D ρ)).1) = fun _ => P := by
    funext ρ
    rw [hsig]
  have e2 : (fun ρ => (W.sig (tauE D ρ)).2) = fun _ => Q := by
    funext ρ
    rw [hsig]
  have h' := h W hW
  rw [e1, e2] at h'
  exact h'

end Formalism.L2.Theta

end
