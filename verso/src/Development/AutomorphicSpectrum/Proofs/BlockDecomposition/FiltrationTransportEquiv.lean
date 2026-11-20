import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.FiltTransfer

/- English proof (translation)
Introduce `G H _ _ ψ V V' _ _ _ _ ρ ρ' e K X _ _ τ Vf h0 hK hm hV hΨ`. Establish `he : ∀ (h : H) (v : V), e (ρ h v) = ρ' (ψ h) (e v)` using `fun h v => e.toIntertwiningMap.isIntertwining _ _ h v`. Set `S : ℕ → Subrepresentation ρ` to `fun i => ⟨(Vf i).comap e.toLinearMap, fun h v hv => by`. Establish `hv' : e v ∈ Vf i` using `hv`. Use `show e (ρ h v) ∈ Vf i`.

Rewrite using `[he]`. Conclude with `hV i (ψ h) hv'⟩`. Establish `memS : ∀ (i : ℕ) (v : V), v ∈ (S i).toSubmodule ↔ e v ∈ Vf i` using `fun _ _ => Iff.rfl`. Use `⟨fun t => S t, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hab v hv`.

Conclude with `hm (Fin.le_def.1 hab) hv`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use extensionality with `v`. Use `show e v ∈ Vf 0 ↔ v = 0`. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use extensionality with `v`. Use `show e v ∈ Vf K ↔ True`. Rewrite using `[hK]`.

Simplify using the standard rewrite rules. Introduce `t`. Take `⟨Ψ, hs, hk⟩` from `hΨ t`. Set `f : (S (t + 1)).toSubmodule →ₗ[ℂ] X t` to `Ψ.toLinearMap ∘ₗ (e.toLinearMap.restrict (p := (S (t + 1)).toSubmodule) (q := Vf (t + 1)) fun _ hv => hv)`. Establish `hf : ∀ x, f x = Ψ ⟨e x, x.2⟩` using `fun _ => rfl`.

Establish `hsurj : Function.Surjective f`. Introduce `y`. Take `⟨w, rfl⟩` from `hs y`. Use `⟨⟨e.symm w, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show e (e.symm w) ∈ Vf (t + 1)`.

Simplify using the standard rewrite rules. Rewrite using `[hf]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using the standard rewrite rules.

Establish `hker : (S t).toSubmodule.comap (S (t + 1)).toSubmodule.subtype = LinearMap.ker f`. Use extensionality with `x`. Rewrite using `[LinearMap.mem_ker, hf, hk]`. Both sides reduce to the same expression. Set `E` to `(Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hsurj)`.

Use `⟨Representation.Equiv.mk E ?_⟩` and prove the remaining obligations. Introduce `g`. Establish `hE : ∀ x, E (Submodule.Quotient.mk x) = f x` using `fun x => rfl`. Use `LinearMap.ext fun q => ?_` and prove the remaining obligations. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Establish `hstep : f ⟨ρ g x, (S (t + 1)).apply_mem_toSubmodule g x.2⟩ = τ t (ψ g) (f x)`. Rewrite using `[hf, hf, ← Ψ.isIntertwining _ _ (ψ g)]`. Use `congr 1`. Conclude with `Subtype.ext (he g x)`. Conclude with `hstep`.
-/
theorem subQuot_of_filtration : ∀ {G H : Type} [Group G] [Group H] (ψ : H →* G) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (ρ : Representation ℂ H V) (ρ' : Representation ℂ G V'), ρ.Equiv (ρ'.comp ψ) → ∀ (K : ℕ) (X : Fin K → Type) [∀ j, AddCommGroup (X j)] [∀ j, Module ℂ (X j)] (τ : ∀ j, Representation ℂ G (X j)) (Vf : ℕ → Submodule ℂ V'), Vf 0 = ⊥ → Vf K = ⊤ → Monotone Vf → ∀ (hV : ∀ i (g : G), Vf i ≤ (Vf i).comap (ρ' g)), (∀ j : Fin K, ∃ Ψ : Representation.IntertwiningMap (ρ'.subrepresentation (Vf (j + 1)) (hV (j + 1))) (τ j), Function.Surjective Ψ ∧ ∀ x, Ψ x = 0 ↔ (x : V') ∈ Vf j) → ∃ S : Fin (K + 1) → Subrepresentation ρ, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last K) = ⊤ ∧ ∀ t : Fin K, Nonempty ((GlobalTheory.SmGL.subQuot (S t.succ) (S t.castSucc)).Equiv ((τ t).comp ψ)) := by
  intro G H _ _ ψ V V' _ _ _ _ ρ ρ' e K X _ _ τ Vf h0 hK hm hV hΨ
  have he : ∀ (h : H) (v : V), e (ρ h v) = ρ' (ψ h) (e v) := fun h v =>
    e.toIntertwiningMap.isIntertwining _ _ h v
  let S : ℕ → Subrepresentation ρ := fun i =>
    ⟨(Vf i).comap e.toLinearMap, fun h v hv => by
      have hv' : e v ∈ Vf i := hv
      show e (ρ h v) ∈ Vf i
      rw [he]
      exact hV i (ψ h) hv'⟩
  have memS : ∀ (i : ℕ) (v : V), v ∈ (S i).toSubmodule ↔ e v ∈ Vf i := fun _ _ => Iff.rfl
  refine ⟨fun t => S t, ?_, ?_, ?_, ?_⟩
  · intro a b hab v hv
    exact hm (Fin.le_def.1 hab) hv
  · apply Subrepresentation.toSubmodule_injective
    ext v
    show e v ∈ Vf 0 ↔ v = 0
    rw [h0]
    simp
  · apply Subrepresentation.toSubmodule_injective
    ext v
    show e v ∈ Vf K ↔ True
    rw [hK]
    simp
  · intro t
    obtain ⟨Ψ, hs, hk⟩ := hΨ t
    let f : (S (t + 1)).toSubmodule →ₗ[ℂ] X t :=
      Ψ.toLinearMap ∘ₗ
        (e.toLinearMap.restrict (p := (S (t + 1)).toSubmodule) (q := Vf (t + 1)) fun _ hv => hv)
    have hf : ∀ x, f x = Ψ ⟨e x, x.2⟩ := fun _ => rfl
    have hsurj : Function.Surjective f := by
      intro y
      obtain ⟨w, rfl⟩ := hs y
      refine ⟨⟨e.symm w, ?_⟩, ?_⟩
      · show e (e.symm w) ∈ Vf (t + 1)
        simp
      · rw [hf]
        congr 1
        apply Subtype.ext
        simp
    have hker : (S t).toSubmodule.comap (S (t + 1)).toSubmodule.subtype = LinearMap.ker f := by
      ext x
      rw [LinearMap.mem_ker, hf, hk]
      rfl
    let E := (Submodule.quotEquivOfEq _ _ hker).trans (f.quotKerEquivOfSurjective hsurj)
    refine ⟨Representation.Equiv.mk E ?_⟩
    intro g
    have hE : ∀ x, E (Submodule.Quotient.mk x) = f x := fun x => rfl
    refine LinearMap.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have hstep : f ⟨ρ g x, (S (t + 1)).apply_mem_toSubmodule g x.2⟩ =
        τ t (ψ g) (f x) := by
      rw [hf, hf, ← Ψ.isIntertwining _ _ (ψ g)]
      congr 1
      exact Subtype.ext (he g x)
    exact hstep

end GlobalTheory.CompanionTheory.FiltTransfer
