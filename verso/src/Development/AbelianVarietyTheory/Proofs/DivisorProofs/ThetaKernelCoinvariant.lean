import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleFirstFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleSecondFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatLocalApproximationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSpaceStatement

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.KCoinvGood

/- English proof (translation)
The claim follows from `Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ`.
-/
theorem augAt_le_SB {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (v : Pl F) : augAt om v ≤ SB _ :=
  Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ

/- English proof (translation)
Introduce `r _` and use `by have e : tens ev (0 : (κ → R) → ℂ) r = 0 := funext fun x => by simp [tens] rw [e, map_zero]`.
-/
theorem acts_zero {F : Type} [Field F] [NumberField F] {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts ev T 0 0 := fun r _ => by
  have e : tens ev (0 : (κ → R) → ℂ) r = 0 := funext fun x => by simp [tens]
  rw [e, map_zero]

/- English proof (translation)
Break down `h with h | h` into its components or cases. Introduce `φ hφ`. Use `⟨fun h0 => h ▸ ⟨hφ, h0⟩, fun hm => hA hm⟩` and prove the remaining obligations. It suffices to derive a contradiction. Take `⟨x, hx⟩` from `exists_ne (0 : P)`.

Establish `: x ∈ S.map p` using `honto ▸ Submodule.mem_top`. Take `⟨y, hy, rfl⟩` from `this`. Establish `hy' : y ∈ S ⊓ LinearMap.ker p` using `by rw [h]; exact hy`. Conclude with `hx hy'.2`.
-/
theorem ker_eq_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    (S A : Submodule ℂ V) (p : V →ₗ[ℂ] P) (hA : A ≤ LinearMap.ker p) (honto : S.map p = ⊤)
    (h : S ⊓ LinearMap.ker p = A ∨ S ⊓ LinearMap.ker p = S) : ∀ φ ∈ S, p φ = 0 ↔ φ ∈ A := by
  rcases h with h | h
  · intro φ hφ
    refine ⟨fun h0 => h ▸ ⟨hφ, h0⟩, fun hm => hA hm⟩
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : P)
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    have hy' : y ∈ S ⊓ LinearMap.ker p := by rw [h]; exact hy
    exact hx hy'.2

/- English proof (translation)
Use `set q := p.domRestrict S`. Establish `hs : Function.Surjective q`. Introduce `x`. Establish `: x ∈ S.map p` using `honto ▸ Submodule.mem_top`. Take `⟨y, hy, rfl⟩` from `this`.

Conclude with `⟨⟨y, hy⟩, rfl⟩`. Establish `hker : LinearMap.ker q ≤ LinearMap.ker (l.domRestrict S)` using `fun x hx => hk x.1 x.2 hx`. Use `⟨((LinearMap.ker q).liftQ (l.domRestrict S) hker).comp (q.quotKerEquivOfSurjective hs).symm.toLinearMap, fun φ hφ => ?_⟩` and prove the remaining obligations. Establish `: (q.quotKerEquivOfSurjective hs).symm (p φ) = Submodule.Quotient.mk ⟨φ, hφ⟩`. Rewrite using `[LinearEquiv.symm_apply_eq]`.

Both sides reduce to the same expression. Simplify using `[this]`.
-/
theorem factor_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P]
    (S : Submodule ℂ V) (p : V →ₗ[ℂ] P) (l : V →ₗ[ℂ] ℂ) (honto : S.map p = ⊤) (hk : ∀ φ ∈ S, p φ = 0 → l φ = 0) :
    ∃ l₀ : P →ₗ[ℂ] ℂ, ∀ φ ∈ S, l φ = l₀ (p φ) := by
  set q := p.domRestrict S
  have hs : Function.Surjective q := by
    intro x
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : LinearMap.ker q ≤ LinearMap.ker (l.domRestrict S) := fun x hx => hk x.1 x.2 hx
  refine ⟨((LinearMap.ker q).liftQ (l.domRestrict S) hker).comp (q.quotKerEquivOfSurjective hs).symm.toLinearMap,
    fun φ hφ => ?_⟩
  have : (q.quotKerEquivOfSurjective hs).symm (p φ) = Submodule.Quotient.mk ⟨φ, hφ⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [this]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B a a' G X om om' R Rf hm`. Establish `ht` using `hm.triple`. Establish `hf` using `hm.fin`. Use `⟨fun v hv => ?_, GlobalTheory.T.weil_representation_preserves_space hP F E σ B a a' G X om om' ht⟩` and prove the remaining obligations. Use `haveI := hf.nontriv v`.

Establish `hnr` using `GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' ht v hv`. Establish `k1 : ∀ φ ∈ SB _, Rf.p v φ = 0 ↔ φ ∈ augAt om v` using `ker_eq_of _ _ _ (hf.inv v) (hf.onto v) <| GlobalTheory.T.augmentation_submodule_first_factor hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om v) (hf.inv v)) inf_le_left fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by`. Use `hf.equiv v h hh φ hφ.1 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero _ _) (by rw [map_zero]; exact hφ.2)` as an intermediate fact. Rewrite `this` using `[map_zero]`. Conclude with `this⟩`.

Establish `k2 : ∀ φ ∈ SB _, Rf.p' v φ = 0 ↔ φ ∈ augAt om' v` using `ker_eq_of _ _ _ (hf.inv' v) (hf.onto' v) <| GlobalTheory.T.augmentation_submodule_second_factor hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om' v) (hf.inv' v)) inf_le_left fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by`. Use `hf.equiv v h hh 0 (zero_mem _) φ hφ.1 0 (zero_mem _) φ₁ hφ₁ (acts_zero _ _) hact (by rw [map_zero]; exact hφ.2.symm)` as an intermediate fact. Rewrite `this` using `[map_zero]`. Conclude with `this.symm⟩`. Use `⟨k1, k2, fun t ξ => ?_, fun l hl => ?_⟩` and prove the remaining obligations.

Establish `: ξ ∈ (SB _).map (Rf.p' v)` using `hf.onto' v ▸ Submodule.mem_top`. Take `⟨φ, hφ, rfl⟩` from `this`. Take `⟨φ₀, h₀, hd⟩` from `GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' ht v hv hnr t φ hφ`. Use `⟨φ₀, h₀, ?_⟩` and prove the remaining obligations. Use `hf.inv' v hd` as an intermediate fact.

Rewrite `this` using `[LinearMap.mem_ker, map_sub, sub_eq_zero]`. Conclude with `this.symm`. Conclude with `factor_of _ _ _ (hf.onto' v) fun φ hφ h0 => hl ((k2 φ hφ).1 h0)`.
-/
theorem kCoinv (hP : GlobalTheory.FunPr.Hypotheses₂) : GlobalTheory.ThK.KCoinv := by
  intro F E _ _ _ _ _ σ B a a' G X om om' R Rf hm
  have ht := hm.triple
  have hf := hm.fin
  refine ⟨fun v hv => ?_, GlobalTheory.T.weil_representation_preserves_space hP F E σ B a a' G X om om' ht⟩
  haveI := hf.nontriv v
  have hnr := GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a a' G X om om' ht v hv
  have k1 : ∀ φ ∈ SB _, Rf.p v φ = 0 ↔ φ ∈ augAt om v :=
    ker_eq_of _ _ _ (hf.inv v) (hf.onto v) <|
      GlobalTheory.T.augmentation_submodule_first_factor hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om v) (hf.inv v)) inf_le_left
        fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by
          have := hf.equiv v h hh φ hφ.1 0 (zero_mem _) φ₁ hφ₁ 0 (zero_mem _) hact (acts_zero _ _)
            (by rw [map_zero]; exact hφ.2)
          rw [map_zero] at this; exact this⟩
  have k2 : ∀ φ ∈ SB _, Rf.p' v φ = 0 ↔ φ ∈ augAt om' v :=
    ker_eq_of _ _ _ (hf.inv' v) (hf.onto' v) <|
      GlobalTheory.T.augmentation_submodule_second_factor hP F E σ B a a' G X om om' ht v hv hnr _ (le_inf (augAt_le_SB om' v) (hf.inv' v)) inf_le_left
        fun h hh φ hφ φ₁ hφ₁ hact => ⟨hφ₁, by
          have := hf.equiv v h hh 0 (zero_mem _) φ hφ.1 0 (zero_mem _) φ₁ hφ₁ (acts_zero _ _) hact
            (by rw [map_zero]; exact hφ.2.symm)
          rw [map_zero] at this; exact this.symm⟩
  refine ⟨k1, k2, fun t ξ => ?_, fun l hl => ?_⟩
  · have : ξ ∈ (SB _).map (Rf.p' v) := hf.onto' v ▸ Submodule.mem_top
    obtain ⟨φ, hφ, rfl⟩ := this
    obtain ⟨φ₀, h₀, hd⟩ := GlobalTheory.T.schwartz_bruhat_local_approximation hP F E σ B a a' G X om om' ht v hv hnr t φ hφ
    refine ⟨φ₀, h₀, ?_⟩
    have := hf.inv' v hd
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
    exact this.symm
  · exact factor_of _ _ _ (hf.onto' v) fun φ hφ h0 => hl ((k2 φ hφ).1 h0)

end GlobalTheory.KCoinvGood
