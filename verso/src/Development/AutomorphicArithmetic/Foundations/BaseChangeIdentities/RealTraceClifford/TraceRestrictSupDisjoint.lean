import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

/- English proof (translation)
Set `φ : (S × S') →ₗ[ℂ] ↥(S ⊔ S')` to `((S.subtype.coprod S'.subtype).codRestrict (S ⊔ S') (fun p => by`. Simplify using `using Submodule.add_mem_sup p.1.2 p.2.2))`. Establish `hφ : ∀ p, (φ p : V) = (p.1 : V) + (p.2 : V)` using `fun p => by simp [φ]`. Establish `hinj : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`.

Introduce and unpack `⟨a, b⟩ h`. Establish `h0 : (a : V) + (b : V) = 0` using `by simpa [hφ] using congrArg Subtype.val h`. Establish `ha : (a : V) ∈ S'`. Establish `: (a : V) = -(b : V)` using `eq_neg_of_add_eq_zero_left h0`. Rewrite using `[this]`.

Conclude with `S'.neg_mem b.2`. Establish `ha0 : (a : V) = 0` using `(Submodule.disjoint_def.1 hd) _ a.2 ha`. Establish `hb0 : (b : V) = 0` using `by simpa [ha0] using h0`. Apply the tactic sequence `ext <;> simp [ha0, hb0]`. Establish `hsurj : Function.Surjective φ`.

Introduce and unpack `⟨x, hx⟩`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hx`. Conclude with `⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (hφ _)⟩`. Set `e : (S × S') ≃ₗ[ℂ] ↥(S ⊔ S')` to `LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩`. Establish `he : ∀ p, (e p : V) = (p.1 : V) + (p.2 : V)` using `fun p => hφ p`.

Establish `hconj : f.restrict hT = e.conj ((f.restrict hS).prodMap (f.restrict hS'))`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Take `⟨p, rfl⟩` from `e.surjective x`. Establish `hc : e.conj ((f.restrict hS).prodMap (f.restrict hS')) (e p) = e ((f.restrict hS).prodMap (f.restrict hS') p)`. Simplify using `[LinearEquiv.conj_apply]`.

Rewrite using `[hc]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[LinearMap.restrict_coe_apply, he, he, map_add]`. Both sides reduce to the same expression. Rewrite using `[hconj, LinearMap.trace_conj', LinearMap.trace_prodMap']`.
-/
private theorem trace_restrict_sup_disjoint {V : Type} [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V)
    (S S' : Submodule ℂ V) (hF : FiniteDimensional ℂ S) (hF' : FiniteDimensional ℂ S')
    (hd : Disjoint S S') (hS : ∀ x ∈ S, f x ∈ S) (hS' : ∀ x ∈ S', f x ∈ S')
    (hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S') :
    LinearMap.trace ℂ ↥(S ⊔ S') (f.restrict hT) =
      LinearMap.trace ℂ S (f.restrict hS) + LinearMap.trace ℂ S' (f.restrict hS') := by
  let φ : (S × S') →ₗ[ℂ] ↥(S ⊔ S') :=
    ((S.subtype.coprod S'.subtype).codRestrict (S ⊔ S') (fun p => by
      simpa using Submodule.add_mem_sup p.1.2 p.2.2))
  have hφ : ∀ p, (φ p : V) = (p.1 : V) + (p.2 : V) := fun p => by simp [φ]
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ h
    have h0 : (a : V) + (b : V) = 0 := by simpa [hφ] using congrArg Subtype.val h
    have ha : (a : V) ∈ S' := by
      have : (a : V) = -(b : V) := eq_neg_of_add_eq_zero_left h0
      rw [this]; exact S'.neg_mem b.2
    have ha0 : (a : V) = 0 := (Submodule.disjoint_def.1 hd) _ a.2 ha
    have hb0 : (b : V) = 0 := by simpa [ha0] using h0
    ext <;> simp [ha0, hb0]
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext (hφ _)⟩
  let e : (S × S') ≃ₗ[ℂ] ↥(S ⊔ S') := LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ p, (e p : V) = (p.1 : V) + (p.2 : V) := fun p => hφ p
  have hconj : f.restrict hT = e.conj ((f.restrict hS).prodMap (f.restrict hS')) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨p, rfl⟩ := e.surjective x
    have hc : e.conj ((f.restrict hS).prodMap (f.restrict hS')) (e p) =
        e ((f.restrict hS).prodMap (f.restrict hS') p) := by
      simp [LinearEquiv.conj_apply]
    rw [hc]
    apply Subtype.ext
    rw [LinearMap.restrict_coe_apply, he, he, map_add]
    rfl
  rw [hconj, LinearMap.trace_conj', LinearMap.trace_prodMap']

/- English proof (translation)
Introduce `V _ _ f`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `S S' hF hF' hd hS hS'`. Establish `hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S'`. Introduce `x hx`.

Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem_sup (hS a ha) (hS' b hb)`. Unfold `PositivityTheory.RgBcC.RealD.trOn`. Rewrite using `[dif_pos hT, dif_pos hS, dif_pos hS']`.

Conclude with `trace_restrict_sup_disjoint f S S' hF hF' hd hS hS' hT`. Introduce `S g c hf hg`. Establish `hfg : ∀ x ∈ S, (f + g) x ∈ S` using `fun x hx => S.add_mem (hf x hx) (hg x hx)`. Establish `hcf : ∀ x ∈ S, (c • f) x ∈ S` using `fun x hx => S.smul_mem c (hf x hx)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `PositivityTheory.RgBcC.RealD.trOn`. Rewrite using `[dif_pos hfg, dif_pos hf, dif_pos hg, ← map_add]`. Use `congr 1`. Unfold `PositivityTheory.RgBcC.RealD.trOn`. Rewrite using `[dif_pos hcf, dif_pos hf]`.

Establish `: (c • f).restrict hcf = c • f.restrict hf` using `by ext x; simp`. Rewrite using `[this, map_smul, smul_eq_mul]`. Introduce `he`. Unfold `PositivityTheory.RgBcC.RealD.trOn`. Rewrite using `[dif_pos hf, dif_pos hg]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `[he x x.2]`. Introduce `S S' g hF hF' hf hg`. Establish `h1 : ∀ x ∈ S, (g * f) x ∈ S` using `fun x hx => hg _ (hf x hx)`.

Establish `h2 : ∀ x ∈ S', (f * g) x ∈ S'` using `fun x hx => hf _ (hg x hx)`. Unfold `PositivityTheory.RgBcC.RealD.trOn`. Rewrite using `[dif_pos h1, dif_pos h2]`. Set `a : S →ₗ[ℂ] S'` to `f.restrict hf`. Set `b : S' →ₗ[ℂ] S` to `g.restrict hg`.

Establish `e1 : (g * f).restrict h1 = b ∘ₗ a` using `by ext x; rfl`. Establish `e2 : (f * g).restrict h2 = a ∘ₗ b` using `by ext x; rfl`. Rewrite using `[e1, e2]`. Conclude with `LinearMap.trace_comp_comm' a b`. Introduce `S hF`.

Establish `h1 : ∀ x ∈ S, (1 : Module.End ℂ V) x ∈ S` using `fun x hx => hx`. Unfold `PositivityTheory.RgBcC.RealD.trOn`. Rewrite using `[dif_pos h1]`. Establish `: (1 : Module.End ℂ V).restrict h1 = LinearMap.id` using `by ext x; rfl`. Rewrite using `[this, LinearMap.trace_id]`.
-/
theorem UpperTheory.RealTr.trAdd :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (f : Module.End ℂ V),
      (∀ S S' : Submodule ℂ V, FiniteDimensional ℂ S → FiniteDimensional ℂ S' → Disjoint S S' → (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S', f x ∈ S') →
        trOn (S ⊔ S') f = trOn S f + trOn S' f) ∧
      (∀ (S : Submodule ℂ V) (g : Module.End ℂ V) (c : ℂ), (∀ x ∈ S, f x ∈ S) → (∀ x ∈ S, g x ∈ S) →
        trOn S (f + g) = trOn S f + trOn S g ∧ trOn S (c • f) = c * trOn S f ∧ ((∀ x ∈ S, f x = g x) → trOn S f = trOn S g)) ∧
      (∀ (S S' : Submodule ℂ V) (g : Module.End ℂ V), FiniteDimensional ℂ S → FiniteDimensional ℂ S' → (∀ x ∈ S, f x ∈ S') → (∀ x ∈ S', g x ∈ S) →
        trOn S (g * f) = trOn S' (f * g)) ∧
      ∀ S : Submodule ℂ V, FiniteDimensional ℂ S → trOn S (1 : Module.End ℂ V) = Module.finrank ℂ S := by
  intro V _ _ f
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S S' hF hF' hd hS hS'
    have hT : ∀ x ∈ S ⊔ S', f x ∈ S ⊔ S' := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact Submodule.add_mem_sup (hS a ha) (hS' b hb)
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dif_pos hT, dif_pos hS, dif_pos hS']
    exact trace_restrict_sup_disjoint f S S' hF hF' hd hS hS' hT
  · intro S g c hf hg
    have hfg : ∀ x ∈ S, (f + g) x ∈ S := fun x hx => S.add_mem (hf x hx) (hg x hx)
    have hcf : ∀ x ∈ S, (c • f) x ∈ S := fun x hx => S.smul_mem c (hf x hx)
    refine ⟨?_, ?_, ?_⟩
    · unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dif_pos hfg, dif_pos hf, dif_pos hg, ← map_add]
      congr 1
    · unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dif_pos hcf, dif_pos hf]
      have : (c • f).restrict hcf = c • f.restrict hf := by ext x; simp
      rw [this, map_smul, smul_eq_mul]
    · intro he
      unfold PositivityTheory.RgBcC.RealD.trOn
      rw [dif_pos hf, dif_pos hg]
      congr 1
      ext x
      simp [he x x.2]
  · intro S S' g hF hF' hf hg
    have h1 : ∀ x ∈ S, (g * f) x ∈ S := fun x hx => hg _ (hf x hx)
    have h2 : ∀ x ∈ S', (f * g) x ∈ S' := fun x hx => hf _ (hg x hx)
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dif_pos h1, dif_pos h2]
    let a : S →ₗ[ℂ] S' := f.restrict hf
    let b : S' →ₗ[ℂ] S := g.restrict hg
    have e1 : (g * f).restrict h1 = b ∘ₗ a := by ext x; rfl
    have e2 : (f * g).restrict h2 = a ∘ₗ b := by ext x; rfl
    rw [e1, e2]
    exact LinearMap.trace_comp_comm' a b
  · intro S hF
    have h1 : ∀ x ∈ S, (1 : Module.End ℂ V) x ∈ S := fun x hx => hx
    unfold PositivityTheory.RgBcC.RealD.trOn
    rw [dif_pos h1]
    have : (1 : Module.End ℂ V).restrict h1 = LinearMap.id := by ext x; rfl
    rw [this, LinearMap.trace_id]
