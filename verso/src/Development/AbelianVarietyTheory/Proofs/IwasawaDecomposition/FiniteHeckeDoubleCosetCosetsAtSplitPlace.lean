import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TSetFinLoc

open GlobalTheory.TSetFin

/- English proof (translation)
Introduce `L _ _ _ n s ϖ hϖ J hJ k`. Take `⟨c, hc⟩` from `approx_class s.v`. Use `haveI : Finite (𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot`. Set `κ : GAf L n → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal)` to `fun x => if h : x ∈ tSet L n s ϖ k then fun i j => c (((h.2.choose : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) else 0`. Establish `key : ∀ x ∈ tSet L n s ϖ k, ∀ x' ∈ tSet L n s ϖ k, κ x = κ x' → (x : GAf L n ⧸ J) = x'`.

Introduce `x hx x' hx' hκ`. Simplify using `only [κ, dif_pos hx, dif_pos hx'] at hκ`. Take `⟨ha, b, hb, hg⟩` from `hx.2.choose_spec`. Take `⟨ha', b', hb', hg'⟩` from `hx'.2.choose_spec`. Use `set a := hx.2.choose`.

Use `set a' := hx'.2.choose`. Establish `ia` using `glint_int ha`. Establish `ia'` using `glint_int ha'`. Establish `ib` using `glint_int hb`. Establish `ib'` using `glint_int hb'`.

Establish `hcl : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j - (a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1` using `fun i j => hc _ _ (ia.1 i j) (ia'.1 i j) (congrFun (congrFun hκ i) j)`. Establish `hcl' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j - (a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1` using `fun i j => by`. Rewrite using `[← Valuation.map_neg, neg_sub]`. Conclude with `hcl i j`. Establish `hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hϖ`.

Establish `h1` using `local_int s.v ϖ k hunif a a' b b' _ _ ia'.1 ia.2 ib.2 ib'.1 hcl hg hg'`. Establish `h2` using `local_int s.v ϖ k hunif a' a b' b _ _ ia.1 ia'.2 ib'.2 ib.1 hcl' hg' hg`. Rewrite using `[QuotientGroup.eq]`. Establish `htriv : TrivOutside {s.v} (x⁻¹ * x')` using `triv_mul (triv_inv hx.1) hx'.1`. Use `(hJ _ htriv).2 ?_` and prove the remaining obligations.

Use `mem_Umax_of_loc s _ htriv (fun i j => ?_) (fun i j => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_inv]`. Conclude with `h1 i j`. Rewrite using `[mul_inv_rev, inv_inv, map_mul, map_inv]`. Conclude with `h2 i j`.

Set `g : GAf L n ⧸ J → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal)` to `fun q => if h : ∃ x ∈ tSet L n s ϖ k, (x : GAf L n ⧸ J) = q then κ h.choose else 0`. Use `Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg`. Establish `h : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x` using `⟨x, hx, rfl⟩`. Establish `h' : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x'` using `⟨x', hx', rfl⟩`.

Simplify using `only [g, dif_pos h, dif_pos h'] at hgg`. Use `show (x : GAf L n ⧸ J) = x'`. Rewrite using `[← h.choose_spec.2, ← h'.choose_spec.2]`. Conclude with `key _ h.choose_spec.1 _ h'.choose_spec.1 hgg`.
-/
theorem finite_image_tSet_loc : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ J : Subgroup (GAf L n),
    (∀ κ, TrivOutside {s.v} κ → (κ ∈ J ↔ κ ∈ Umax L n)) → ∀ k : ℕ,
    ((fun x : GAf L n => (x : GAf L n ⧸ J)) '' tSet L n s ϖ k).Finite := by
  intro L _ _ _ n s ϖ hϖ J hJ k
  classical
  obtain ⟨c, hc⟩ := approx_class s.v
  haveI : Finite (𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ s.v.ne_bot
  let κ : GAf L n → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun x =>
    if h : x ∈ tSet L n s ϖ k then
      fun i j => c (((h.2.choose : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) :
        Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j)
    else 0
  have key : ∀ x ∈ tSet L n s ϖ k, ∀ x' ∈ tSet L n s ϖ k, κ x = κ x' →
      (x : GAf L n ⧸ J) = x' := by
    intro x hx x' hx' hκ
    simp only [κ, dif_pos hx, dif_pos hx'] at hκ
    obtain ⟨ha, b, hb, hg⟩ := hx.2.choose_spec
    obtain ⟨ha', b', hb', hg'⟩ := hx'.2.choose_spec
    set a := hx.2.choose
    set a' := hx'.2.choose
    have ia := glint_int ha
    have ia' := glint_int ha'
    have ib := glint_int hb
    have ib' := glint_int hb'
    have hcl : ∀ i j, Valued.v ((a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j =>
      hc _ _ (ia.1 i j) (ia'.1 i j) (congrFun (congrFun hκ i) j)
    have hcl' : ∀ i j, Valued.v ((a' : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j -
        (a : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) i j) < 1 := fun i j => by
      rw [← Valuation.map_neg, neg_sub]; exact hcl i j
    have hunif : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
    have h1 := local_int s.v ϖ k hunif a a' b b' _ _ ia'.1 ia.2 ib.2 ib'.1 hcl hg hg'
    have h2 := local_int s.v ϖ k hunif a' a b' b _ _ ia.1 ia'.2 ib'.2 ib.1 hcl' hg' hg
    rw [QuotientGroup.eq]
    have htriv : TrivOutside {s.v} (x⁻¹ * x') := triv_mul (triv_inv hx.1) hx'.1
    refine (hJ _ htriv).2 ?_
    refine mem_Umax_of_loc s _ htriv (fun i j => ?_) (fun i j => ?_)
    · rw [map_mul, map_inv]; exact h1 i j
    · rw [mul_inv_rev, inv_inv, map_mul, map_inv]; exact h2 i j
  let g : GAf L n ⧸ J → (Fin n → Fin n → 𝓞 (maximalRealSubfield L) ⧸ s.v.asIdeal) := fun q =>
    if h : ∃ x ∈ tSet L n s ϖ k, (x : GAf L n ⧸ J) = q then κ h.choose else 0
  refine Set.Finite.of_finite_image (f := g) (Set.toFinite _) ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨x', hx', rfl⟩ hgg
  have h : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x := ⟨x, hx, rfl⟩
  have h' : ∃ y ∈ tSet L n s ϖ k, (y : GAf L n ⧸ J) = x' := ⟨x', hx', rfl⟩
  simp only [g, dif_pos h, dif_pos h'] at hgg
  show (x : GAf L n ⧸ J) = x'
  rw [← h.choose_spec.2, ← h'.choose_spec.2]
  exact key _ h.choose_spec.1 _ h'.choose_spec.1 hgg

end GlobalTheory.TSetFinLoc

end
