import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhitImgMono

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.SubquotExt

/- English proof (translation)
Introduce `G V W _ _ _ _ _ ρ σ A B hAB hσ hB`. Use `haveI : IsSimpleOrder (Subrepresentation σ) := hσ`. Unfold `GlobalTheory.SmGL.IsSubquotient at hB ⊢`. Take `⟨S, f, hf⟩` from `hB`. Set `P : Submodule ℂ S.toSubmodule` to `(A.toSubmodule.comap B.toSubmodule.subtype).comap S.toSubmodule.subtype`.

Establish `hNinv : ∀ (g : G) ⦃w : W⦄, w ∈ P.map f.toLinearMap → σ g w ∈ P.map f.toLinearMap`. Introduce `g w hw`. Rewrite `hw`, the goal using `[Submodule.mem_map]`. Take `⟨s, hs, rfl⟩` from `hw`. Establish `hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule` using `hs`.

Use `⟨S.toRepresentation g s, A.apply_mem_toSubmodule g hs', ?_⟩` and prove the remaining obligations. Conclude with `f.isIntertwining _ _ g s`. Set `N : Subrepresentation σ` to `⟨P.map f.toLinearMap, hNinv⟩`. Set `Z : Subrepresentation σ` to `⟨⊥, by`. Introduce `g w hw`.

Rewrite `hw`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hw, map_zero]⟩`. Set `Fu : Subrepresentation σ` to `⟨⊤, by`. Introduce `g w _`. Conclude with `Submodule.mem_top⟩`.

Break down `IsSimpleOrder.eq_bot_or_eq_top N with hN | hN` into its components or cases. Use `right`. Establish `hle : N ≤ Z`. Rewrite using `[hN]`. Conclude with `bot_le`.

Establish `hfP : P ≤ LinearMap.ker f.toLinearMap`. Introduce `s hs`. Establish `h0 : f.toLinearMap s ∈ (⊥ : Submodule ℂ W)` using `hle (Submodule.mem_map_of_mem hs)`. Conclude with `LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 h0)`. Set `A' : Submodule ℂ B.toSubmodule` to `A.toSubmodule.comap B.toSubmodule.subtype`.

Establish `hQ : ∀ (g : G) (b : B.toSubmodule), GlobalTheory.SmGL.subQuot B A g (A'.mkQ b) = A'.mkQ (B.toRepresentation g b)`. Introduce `g b`. Use `first`. Consider the case `rfl`. Consider the case `(unfold GlobalTheory.SmGL.subQuot`.

Rewrite using `[Representation.quotient_apply]`. Use the proof step `rfl)`. Establish `hSinv : ∀ (g : G) ⦃x : B.toSubmodule ⧸ A'⦄, x ∈ S.toSubmodule.map A'.mkQ → GlobalTheory.SmGL.subQuot B A g x ∈ S.toSubmodule.map A'.mkQ`. Introduce `g x hx`. Rewrite `hx`, the goal using `[Submodule.mem_map]`.

Take `⟨b, hb, rfl⟩` from `hx`. Conclude with `⟨B.toRepresentation g b, S.apply_mem_toSubmodule g hb, (hQ g b).symm⟩`. Set `S'' : Subrepresentation (GlobalTheory.SmGL.subQuot B A)` to `⟨S.toSubmodule.map A'.mkQ, hSinv⟩`. Set `ψ0 : S.toSubmodule →ₗ[ℂ] (S.toSubmodule.map A'.mkQ)` to `LinearMap.codRestrict _ (A'.mkQ ∘ₗ S.toSubmodule.subtype) (fun s => Submodule.mem_map_of_mem s.2)`. Establish `hPker : P ≤ LinearMap.ker ψ0`.

Introduce `s hs`. Establish `hs' : (s : B.toSubmodule) ∈ A'` using `hs`. Rewrite using `[LinearMap.mem_ker]`. Conclude with `Subtype.ext ((Submodule.Quotient.mk_eq_zero A').2 hs')`. Establish `hkerP : LinearMap.ker ψ0 ≤ P`.

Introduce `s hs`. Rewrite `hs` using `[LinearMap.mem_ker]`. Establish `h2 : (Submodule.Quotient.mk (s : B.toSubmodule) : B.toSubmodule ⧸ A') = 0` using `congrArg Subtype.val hs`. Conclude with `(Submodule.Quotient.mk_eq_zero A').1 h2`. Establish `hinj : Function.Injective (P.liftQ ψ0 hPker)` using `LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot P ψ0 hPker hkerP)`.

Establish `hsurj : Function.Surjective (P.liftQ ψ0 hPker)`. Introduce `x`. Take `⟨y, hy⟩` from `x`. Rewrite `hy` using `[Submodule.mem_map]`. Take `⟨b, hb, rfl⟩` from `hy`.

Conclude with `⟨Submodule.Quotient.mk ⟨b, hb⟩, rfl⟩`. Set `e` to `LinearEquiv.ofBijective (P.liftQ ψ0 hPker) ⟨hinj, hsurj⟩`. Set `F'' : (S.toSubmodule.map A'.mkQ) →ₗ[ℂ] W` to `P.liftQ f.toLinearMap hfP ∘ₗ e.symm.toLinearMap`. Establish `key : ∀ s, F'' (ψ0 s) = f s`. Introduce `s`.

Establish `he : ψ0 s = e (Submodule.Quotient.mk s)` using `rfl`. Use `show P.liftQ f.toLinearMap hfP (e.symm (ψ0 s)) = f s`. Rewrite using `[he, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Establish `hrep : ∀ (g : G) (s : S.toSubmodule), S''.toRepresentation g (ψ0 s) = ψ0 (S.toRepresentation g s)` using `fun g s => Subtype.ext (hQ g s)`.

Establish `hψ0 : ∀ x : S.toSubmodule.map A'.mkQ, ∃ s, ψ0 s = x`. Introduce `x`. Take `⟨y, rfl⟩` from `hsurj x`. Take `⟨s, rfl⟩` from `Submodule.mkQ_surjective P y`. Conclude with `⟨s, rfl⟩`.

Set `f'' : S''.toRepresentation.IntertwiningMap σ` to `⟨F'', fun g => LinearMap.ext fun x => by`. Take `⟨s, rfl⟩` from `hψ0 x`. Use `show F'' (S''.toRepresentation g (ψ0 s)) = σ g (F'' (ψ0 s))`. Rewrite using `[hrep, key, key]`. Conclude with `f.isIntertwining _ _ g s⟩`.

Use `⟨S'', f'', fun w => ?_⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `hf w`. Conclude with `⟨ψ0 s, key s⟩`. Use `left`. Establish `hge : Fu ≤ N`.

Rewrite using `[hN]`. Conclude with `le_top`. Establish `hAB' : A.toSubmodule ≤ B.toSubmodule` using `fun x hx => hAB hx`. Establish `hS'inv : ∀ (g : G) ⦃a : A.toSubmodule⦄, a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') → A.toRepresentation g a ∈ S.toSubmodule.comap (Submodule.inclusion hAB')`. Introduce `g a ha`.

Conclude with `S.apply_mem_toSubmodule g ha`. Set `S' : Subrepresentation A.toRepresentation` to `⟨S.toSubmodule.comap (Submodule.inclusion hAB'), hS'inv⟩`. Set `r : (S.toSubmodule.comap (Submodule.inclusion hAB')) →ₗ[ℂ] S.toSubmodule` to `(Submodule.inclusion hAB').restrict (fun a ha => ha)`. Set `f' : S'.toRepresentation.IntertwiningMap σ` to `⟨f.toLinearMap ∘ₗ r, fun g => LinearMap.ext fun x => by show f.toLinearMap (r (S'.toRepresentation g x)) = σ g (f.toLinearMap (r x))`. Conclude with `f.isIntertwining _ _ g (r x)⟩`.

Use `⟨S', f', fun w => ?_⟩` and prove the remaining obligations. Establish `hw : w ∈ P.map f.toLinearMap` using `hge (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ W))`. Rewrite `hw` using `[Submodule.mem_map]`. Take `⟨s, hs, rfl⟩` from `hw`. Establish `hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule` using `hs`.

Establish `ha : (⟨((s : B.toSubmodule) : V), hs'⟩ : A.toSubmodule) ∈ S.toSubmodule.comap (Submodule.inclusion hAB')` using `by first`. Consider the case `exact s.2`. Consider the case `simpa using s.2`. Conclude with `⟨⟨⟨((s : B.toSubmodule) : V), hs'⟩, ha⟩, rfl⟩`.
-/
theorem isSubquotient_sub_or_quot :
    ∀ (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (A B : Subrepresentation ρ), A ≤ B → σ.IsIrreducible → IsSubquotient σ B.toRepresentation →
    IsSubquotient σ A.toRepresentation ∨ IsSubquotient σ (subQuot B A) := by
  intro G V W _ _ _ _ _ ρ σ A B hAB hσ hB
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  unfold GlobalTheory.SmGL.IsSubquotient at hB ⊢
  obtain ⟨S, f, hf⟩ := hB
  let P : Submodule ℂ S.toSubmodule :=
    (A.toSubmodule.comap B.toSubmodule.subtype).comap S.toSubmodule.subtype
  have hNinv : ∀ (g : G) ⦃w : W⦄, w ∈ P.map f.toLinearMap → σ g w ∈ P.map f.toLinearMap := by
    intro g w hw
    rw [Submodule.mem_map] at hw ⊢
    obtain ⟨s, hs, rfl⟩ := hw
    have hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule := hs
    refine ⟨S.toRepresentation g s, A.apply_mem_toSubmodule g hs', ?_⟩
    exact f.isIntertwining _ _ g s
  let N : Subrepresentation σ := ⟨P.map f.toLinearMap, hNinv⟩
  let Z : Subrepresentation σ := ⟨⊥, by
    intro g w hw
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]⟩
  let Fu : Subrepresentation σ := ⟨⊤, by
    intro g w _
    exact Submodule.mem_top⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top N with hN | hN
  · right
    have hle : N ≤ Z := by
      rw [hN]
      exact bot_le
    have hfP : P ≤ LinearMap.ker f.toLinearMap := by
      intro s hs
      have h0 : f.toLinearMap s ∈ (⊥ : Submodule ℂ W) := hle (Submodule.mem_map_of_mem hs)
      exact LinearMap.mem_ker.2 ((Submodule.mem_bot ℂ).1 h0)
    let A' : Submodule ℂ B.toSubmodule := A.toSubmodule.comap B.toSubmodule.subtype
    have hQ : ∀ (g : G) (b : B.toSubmodule), GlobalTheory.SmGL.subQuot B A g (A'.mkQ b) =
        A'.mkQ (B.toRepresentation g b) := by
      intro g b
      first
      | rfl
      | (unfold GlobalTheory.SmGL.subQuot
         rw [Representation.quotient_apply]
         rfl)
    have hSinv : ∀ (g : G) ⦃x : B.toSubmodule ⧸ A'⦄, x ∈ S.toSubmodule.map A'.mkQ →
        GlobalTheory.SmGL.subQuot B A g x ∈ S.toSubmodule.map A'.mkQ := by
      intro g x hx
      rw [Submodule.mem_map] at hx ⊢
      obtain ⟨b, hb, rfl⟩ := hx
      exact ⟨B.toRepresentation g b, S.apply_mem_toSubmodule g hb, (hQ g b).symm⟩
    let S'' : Subrepresentation (GlobalTheory.SmGL.subQuot B A) := ⟨S.toSubmodule.map A'.mkQ, hSinv⟩
    let ψ0 : S.toSubmodule →ₗ[ℂ] (S.toSubmodule.map A'.mkQ) :=
      LinearMap.codRestrict _ (A'.mkQ ∘ₗ S.toSubmodule.subtype) (fun s => Submodule.mem_map_of_mem s.2)
    have hPker : P ≤ LinearMap.ker ψ0 := by
      intro s hs
      have hs' : (s : B.toSubmodule) ∈ A' := hs
      rw [LinearMap.mem_ker]
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero A').2 hs')
    have hkerP : LinearMap.ker ψ0 ≤ P := by
      intro s hs
      rw [LinearMap.mem_ker] at hs
      have h2 : (Submodule.Quotient.mk (s : B.toSubmodule) : B.toSubmodule ⧸ A') = 0 := congrArg Subtype.val hs
      exact (Submodule.Quotient.mk_eq_zero A').1 h2
    have hinj : Function.Injective (P.liftQ ψ0 hPker) :=
      LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot P ψ0 hPker hkerP)
    have hsurj : Function.Surjective (P.liftQ ψ0 hPker) := by
      intro x
      obtain ⟨y, hy⟩ := x
      rw [Submodule.mem_map] at hy
      obtain ⟨b, hb, rfl⟩ := hy
      exact ⟨Submodule.Quotient.mk ⟨b, hb⟩, rfl⟩
    let e := LinearEquiv.ofBijective (P.liftQ ψ0 hPker) ⟨hinj, hsurj⟩
    let F'' : (S.toSubmodule.map A'.mkQ) →ₗ[ℂ] W := P.liftQ f.toLinearMap hfP ∘ₗ e.symm.toLinearMap
    have key : ∀ s, F'' (ψ0 s) = f s := by
      intro s
      have he : ψ0 s = e (Submodule.Quotient.mk s) := rfl
      show P.liftQ f.toLinearMap hfP (e.symm (ψ0 s)) = f s
      rw [he, LinearEquiv.symm_apply_apply]
      rfl
    have hrep : ∀ (g : G) (s : S.toSubmodule), S''.toRepresentation g (ψ0 s) = ψ0 (S.toRepresentation g s) :=
      fun g s => Subtype.ext (hQ g s)
    have hψ0 : ∀ x : S.toSubmodule.map A'.mkQ, ∃ s, ψ0 s = x := by
      intro x
      obtain ⟨y, rfl⟩ := hsurj x
      obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective P y
      exact ⟨s, rfl⟩
    let f'' : S''.toRepresentation.IntertwiningMap σ := ⟨F'', fun g => LinearMap.ext fun x => by
      obtain ⟨s, rfl⟩ := hψ0 x
      show F'' (S''.toRepresentation g (ψ0 s)) = σ g (F'' (ψ0 s))
      rw [hrep, key, key]
      exact f.isIntertwining _ _ g s⟩
    refine ⟨S'', f'', fun w => ?_⟩
    obtain ⟨s, rfl⟩ := hf w
    exact ⟨ψ0 s, key s⟩
  · left
    have hge : Fu ≤ N := by
      rw [hN]
      exact le_top
    have hAB' : A.toSubmodule ≤ B.toSubmodule := fun x hx => hAB hx
    have hS'inv : ∀ (g : G) ⦃a : A.toSubmodule⦄, a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') →
        A.toRepresentation g a ∈ S.toSubmodule.comap (Submodule.inclusion hAB') := by
      intro g a ha
      exact S.apply_mem_toSubmodule g ha
    let S' : Subrepresentation A.toRepresentation := ⟨S.toSubmodule.comap (Submodule.inclusion hAB'), hS'inv⟩
    let r : (S.toSubmodule.comap (Submodule.inclusion hAB')) →ₗ[ℂ] S.toSubmodule :=
      (Submodule.inclusion hAB').restrict (fun a ha => ha)
    let f' : S'.toRepresentation.IntertwiningMap σ := ⟨f.toLinearMap ∘ₗ r, fun g => LinearMap.ext fun x => by
      show f.toLinearMap (r (S'.toRepresentation g x)) = σ g (f.toLinearMap (r x))
      exact f.isIntertwining _ _ g (r x)⟩
    refine ⟨S', f', fun w => ?_⟩
    have hw : w ∈ P.map f.toLinearMap := hge (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ W))
    rw [Submodule.mem_map] at hw
    obtain ⟨s, hs, rfl⟩ := hw
    have hs' : ((s : B.toSubmodule) : V) ∈ A.toSubmodule := hs
    have ha : (⟨((s : B.toSubmodule) : V), hs'⟩ : A.toSubmodule) ∈ S.toSubmodule.comap (Submodule.inclusion hAB') := by
      first
      | exact s.2
      | simpa using s.2
    exact ⟨⟨⟨((s : B.toSubmodule) : V), hs'⟩, ha⟩, rfl⟩

end GlobalTheory.CompanionTheory.SubquotExt

end
