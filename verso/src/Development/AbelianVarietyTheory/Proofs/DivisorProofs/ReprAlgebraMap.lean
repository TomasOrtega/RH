import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal

namespace GlobalTheory.LatJet

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_single_one]`.
-/
theorem JetRing.repr_algebraMap {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ} (J : JetRing R I n) (a : R) :
    J.b.repr (algebraMap R J.B a) = Finsupp.single ⟨0, by simp⟩ a := by
  rw [Algebra.algebraMap_eq_smul_one, ← J.one, map_smul, Module.Basis.repr_self, Finsupp.smul_single_one]

/- English proof (translation)
Take `⟨ε, hε⟩` from `h4`. Use `⟨ε, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ I _ 𝔠 hf R₀ s r hs R _ _ _ _ _ X₀ δ₀ N hN κ`. Take `⟨J⟩` from `h1 R I (∑ i, κ i)`. Take `⟨Y⟩` from `h2 (FR E) 𝔠 R I (∑ i, κ i) J X₀ δ₀ N hN`.

Use `letI : Algebra R₀ J.B := ((algebraMap R J.B).comp (algebraMap R₀ R)).toAlgebra`. Set `ν : Idx I (∑ i, κ i)` to `⟨κ, Nat.le_succ _⟩`. Use `⟨J.b.repr (r.val J.B Y.X' trivial Y.δ') ν, ?_⟩` and prove the remaining obligations. Introduce `σ hσ φ c y m hφ hc hr T hT g u hg hu`. Take `⟨J'⟩` from `h1 ℂ I (∑ i, κ i)`.

Take `⟨Y', τ, q, hτ, hq, hd⟩` from `h3 E I 𝔠 φ (lattice c y) R σ _ J J' X₀ δ₀ N Y T hT`. Use `letI : Algebra R₀ J'.B := ((algebraMap ℂ J'.B).comp R₀.subtype).toAlgebra`. Establish `hcomm : ∀ a : R₀, τ (algebraMap R₀ J.B a) = algebraMap R₀ J'.B a`. Introduce `a`. Apply `J'.b.repr.injective` to reduce the goal to its premises.

Use extensionality with `μ`. Rewrite using `[hτ]`. Express the relevant statement in the definitionally equal form `σ (J.b.repr (algebraMap R J.B (algebraMap R₀ R a)) μ) = J'.b.repr (algebraMap ℂ J'.B (a : ℂ)) μ`. Rewrite using `[J.repr_algebraMap, J'.repr_algebraMap, Finsupp.single_apply, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> simp [hσ]`.

Establish `hbc` using `r.baseChange J.B J'.B ⟨τ, hcomm⟩ Y.X' trivial Y'.X' trivial q Y.δ' Y'.δ' hq hd`. Establish `key` using `hε E I 𝔠 φ c y hf hφ hc R₀ s r m hs hr T _ J' Y' (fun _ => rfl) g ν u hg hu`. Rewrite `key` using `[hbc]`. Rewrite using `[← key]`. Conclude with `congrArg (T.C ^ (2 * s) * ·) (hτ _ ν).symm`.
-/
theorem jetCore_of (h1 : JetRingEx) (h2 : JetLift) (h3 : JetBC) (h4 : JetAnalytic) : JetCore := by
  obtain ⟨ε, hε⟩ := h4
  refine ⟨ε, ?_⟩
  intro E _ _ _ I _ 𝔠 hf R₀ s r hs R _ _ _ _ _ X₀ δ₀ N hN κ
  obtain ⟨J⟩ := h1 R I (∑ i, κ i)
  obtain ⟨Y⟩ := h2 (FR E) 𝔠 R I (∑ i, κ i) J X₀ δ₀ N hN
  letI : Algebra R₀ J.B := ((algebraMap R J.B).comp (algebraMap R₀ R)).toAlgebra
  let ν : Idx I (∑ i, κ i) := ⟨κ, Nat.le_succ _⟩
  refine ⟨J.b.repr (r.val J.B Y.X' trivial Y.δ') ν, ?_⟩
  intro σ hσ φ c y m hφ hc hr T hT g u hg hu
  obtain ⟨J'⟩ := h1 ℂ I (∑ i, κ i)
  obtain ⟨Y', τ, q, hτ, hq, hd⟩ := h3 E I 𝔠 φ (lattice c y) R σ _ J J' X₀ δ₀ N Y T hT
  letI : Algebra R₀ J'.B := ((algebraMap ℂ J'.B).comp R₀.subtype).toAlgebra
  have hcomm : ∀ a : R₀, τ (algebraMap R₀ J.B a) = algebraMap R₀ J'.B a := by
    intro a
    apply J'.b.repr.injective
    ext μ
    rw [hτ]
    change σ (J.b.repr (algebraMap R J.B (algebraMap R₀ R a)) μ) = J'.b.repr (algebraMap ℂ J'.B (a : ℂ)) μ
    rw [J.repr_algebraMap, J'.repr_algebraMap, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs <;> simp [hσ]
  have hbc := r.baseChange J.B J'.B ⟨τ, hcomm⟩ Y.X' trivial Y'.X' trivial q Y.δ' Y'.δ' hq hd
  have key := hε E I 𝔠 φ c y hf hφ hc R₀ s r m hs hr T _ J' Y' (fun _ => rfl) g ν u hg hu
  rw [hbc] at key
  rw [← key]
  exact congrArg (T.C ^ (2 * s) * ·) (hτ _ ν).symm

end GlobalTheory.LatJet
