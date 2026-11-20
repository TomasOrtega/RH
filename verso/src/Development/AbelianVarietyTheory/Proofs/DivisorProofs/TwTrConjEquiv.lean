import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

/- English proof (translation)
Introduce `G _ V V' _ _ _ _ ρ ρ' e K K' f A`. Use `set φ := e.toLinearEquiv with hφ`. Establish `hint : ∀ g v, φ (ρ g v) = ρ' g (φ v)` using `fun g v => by`. Establish `h` using `LinearMap.congr_fun (e.isIntertwining' g) v`. Simplify `h` using `[hφ]`.

Establish `hint' : ∀ g v', ρ' g v' = φ (ρ g (φ.symm v'))` using `fun g v' => by`. Rewrite using `[hint, φ.apply_symm_apply]`. Establish `hmem : ∀ v', v' ∈ fixed ρ' K' ↔ φ.symm v' ∈ fixed ρ K'`. Introduce `v'`. Use `show (∀ h : K', ρ' h v' = ((1 : K' →* ℂˣ) h : ℂ) • v') ↔ (∀ h : K', ρ h (φ.symm v') = ((1 : K' →* ℂˣ) h : ℂ) • φ.symm v')`.

Simplify using `only [MonoidHom.one_apply, Units.val_one, one_smul]`. Use `forall_congr' fun h => ?_` and prove the remaining obligations. Rewrite using `[hint']`. Prove the components needed by the constructor for the conclusion. Introduce `H`.

Conclude with `(φ.symm_apply_eq.2 H.symm).symm`. Introduce `H`. Rewrite using `[H, φ.apply_symm_apply]`. Establish `hlev : levOp ρ' K K' f (φ.conj A) = φ.conj (levOp ρ K K' f A)`. Establish `hs` using `(φ.conj.toAddEquiv).map_finsum (fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ A))`.

Unfold `levOp`. Rewrite using `[map_smul]`. Use `congr 1`. Use `Eq.trans ?_ hs.symm` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `q`. Use extensionality with `v'`. Simplify using `[LinearEquiv.conj_apply, hint']`. Establish `hA : φ.toLinearMap ∘ₗ A ∘ₗ φ.symm.toLinearMap = φ.conj A`. Rewrite using `[LinearEquiv.conj_apply, LinearMap.comp_assoc]`.

Rewrite using `[hA]`. Establish `hmap : (fixed ρ K').map (φ : V →ₗ[ℂ] V') = fixed ρ' K'`. Use extensionality with `v'`. Rewrite using `[Submodule.mem_map_equiv, hmem]`. Use `set L := levOp ρ K K' f A with hL`.

Establish `hc : (∀ v ∈ fixed ρ' K', φ.conj L v ∈ fixed ρ' K') ↔ (∀ v ∈ fixed ρ K', L v ∈ fixed ρ K')`. Prove the components needed by the constructor for the conclusion. Introduce `H v hv`. Establish `h1 : φ v ∈ fixed ρ' K'` using `(hmem _).2 (by simpa using hv)`. Establish `h2` using `(hmem _).1 (H _ h1)`.

Simplify `h2` using `[LinearEquiv.conj_apply]`. Introduce `H v' hv'`. Rewrite using `[hmem]`. Simplify `H _ ((hmem _).1 hv')` using `[LinearEquiv.conj_apply]`. Unfold `twTr`.

Simplify using `only [hlev]`. Distinguish the cases in `h : ∀ v ∈ fixed ρ K', L v ∈ fixed ρ K'`. Rewrite using `[dif_pos (hc.2 h), dif_pos h]`. Set `ψ` to `φ.ofSubmodules _ _ hmap`. Establish `hr : (φ.conj L).restrict (hc.2 h) = ψ.conj (L.restrict h)`.

Use extensionality with `⟨v', hv'⟩`. Simplify using `[ψ, LinearEquiv.conj_apply, LinearMap.restrict_apply]`. Rewrite using `[hr, LinearMap.trace_conj']`. Rewrite using `[dif_neg (mt hc.1 h), dif_neg h]`.
-/
theorem twTr_conj_equiv : ∀ (G : Type) [Group G] (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (e : ρ.Equiv ρ') (K K' : Subgroup G) (f : G → ℂ) (A : V →ₗ[ℂ] V), twTr ρ' K K' f (e.toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ e.toLinearEquiv.symm.toLinearMap) = twTr ρ K K' f A := by
  intro G _ V V' _ _ _ _ ρ ρ' e K K' f A
  set φ := e.toLinearEquiv with hφ
  have hint : ∀ g v, φ (ρ g v) = ρ' g (φ v) := fun g v => by
    have h := LinearMap.congr_fun (e.isIntertwining' g) v
    simpa [hφ] using h
  have hint' : ∀ g v', ρ' g v' = φ (ρ g (φ.symm v')) := fun g v' => by
    rw [hint, φ.apply_symm_apply]
  have hmem : ∀ v', v' ∈ fixed ρ' K' ↔ φ.symm v' ∈ fixed ρ K' := by
    intro v'
    show (∀ h : K', ρ' h v' = ((1 : K' →* ℂˣ) h : ℂ) • v') ↔
      (∀ h : K', ρ h (φ.symm v') = ((1 : K' →* ℂˣ) h : ℂ) • φ.symm v')
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    refine forall_congr' fun h => ?_
    rw [hint']
    constructor
    · intro H
      exact (φ.symm_apply_eq.2 H.symm).symm
    · intro H
      rw [H, φ.apply_symm_apply]
  have hlev : levOp ρ' K K' f (φ.conj A) = φ.conj (levOp ρ K K' f A) := by
    have hs := (φ.conj.toAddEquiv).map_finsum (fun q : G ⧸ K' => f q.out • (ρ q.out ∘ₗ A))
    unfold levOp
    rw [map_smul]
    congr 1
    refine Eq.trans ?_ hs.symm
    congr 1
    funext q
    ext v'
    simp [LinearEquiv.conj_apply, hint']
  have hA : φ.toLinearMap ∘ₗ A ∘ₗ φ.symm.toLinearMap = φ.conj A := by
    rw [LinearEquiv.conj_apply, LinearMap.comp_assoc]
  rw [hA]
  have hmap : (fixed ρ K').map (φ : V →ₗ[ℂ] V') = fixed ρ' K' := by
    ext v'
    rw [Submodule.mem_map_equiv, hmem]
  set L := levOp ρ K K' f A with hL
  have hc : (∀ v ∈ fixed ρ' K', φ.conj L v ∈ fixed ρ' K') ↔ (∀ v ∈ fixed ρ K', L v ∈ fixed ρ K') := by
    constructor
    · intro H v hv
      have h1 : φ v ∈ fixed ρ' K' := (hmem _).2 (by simpa using hv)
      have h2 := (hmem _).1 (H _ h1)
      simpa [LinearEquiv.conj_apply] using h2
    · intro H v' hv'
      rw [hmem]
      simpa [LinearEquiv.conj_apply] using H _ ((hmem _).1 hv')
  unfold twTr
  simp only [hlev]
  by_cases h : ∀ v ∈ fixed ρ K', L v ∈ fixed ρ K'
  · rw [dif_pos (hc.2 h), dif_pos h]
    let ψ := φ.ofSubmodules _ _ hmap
    have hr : (φ.conj L).restrict (hc.2 h) = ψ.conj (L.restrict h) := by
      ext ⟨v', hv'⟩
      simp [ψ, LinearEquiv.conj_apply, LinearMap.restrict_apply]
    rw [hr, LinearMap.trace_conj']
  · rw [dif_neg (mt hc.1 h), dif_neg h]

end GlobalTheory.BCT
