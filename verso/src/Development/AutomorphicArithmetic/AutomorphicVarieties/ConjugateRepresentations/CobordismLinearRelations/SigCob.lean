import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

/- English proof (translation)
Consider the cases of `q with`. Consider the case `zero`. Introduce `x hx`. Express the relevant statement in the definitionally equal form `T (c x) = 0`. Rewrite using `[hc x hx, map_zero]`.

Consider the case `succ k`. Take `⟨b, b1, b2⟩` from `hc`. Use `⟨fun x => T (b x), fun γ x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `T (b _) = _`. Rewrite using `[b1 γ x hx, hT]`.

Express the relevant statement in the definitionally equal form `T (c x) = _`. Rewrite using `[b2 x hx]`. Simplify using `only [hd, map_sum, map_zsmul]`.
-/
private theorem hcob_map {Γ M M' : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (ρ : Representation ℂ Γ M) (ρ' : Representation ℂ Γ M') (T : M →+ M') (hT : ∀ γ m, T (ρ γ m) = ρ' γ (T m))
    (q : ℕ) (c : List Γ → M) (hc : HCob ρ q c) : HCob ρ' q (fun x => T (c x)) := by
  cases q with
  | zero =>
    intro x hx
    change T (c x) = 0
    rw [hc x hx, map_zero]
  | succ k =>
    obtain ⟨b, b1, b2⟩ := hc
    refine ⟨fun x => T (b x), fun γ x hx => ?_, fun x hx => ?_⟩
    · change T (b _) = _
      rw [b1 γ x hx, hT]
    · change T (c x) = _
      rw [b2 x hx]
      simp only [hd, map_sum, map_zsmul]

/- English proof (translation)
Set `T : ((GL (Fin a) (Af E) ⧸ U) → Fin Ξ.d → ℂ) →+ ((GL (Fin a) (Af E) ⧸ U) → Fin Ξ'.d → ℂ)` to `{ toFun := fun f y i => σ (f y (Fin.cast h.symm i)) map_zero' := by ext y i; simp map_add' := fun f g => by ext y i; simp }`. Use `hcob_map _ _ T (fun γ f => ?_) q c hc` and prove the remaining obligations. Use function extensionality and compare the values at `y i`. Express the relevant statement in the definitionally equal form `σ ((ratC Ξ γ *ᵥ f _) (Fin.cast h.symm i)) = (ratC Ξ' γ *ᵥ fun j => σ (f _ (Fin.cast h.symm j))) i`. Simplify using `only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← hσ _ _ _]`.

Conclude with `Fintype.sum_equiv (finCongr h) _ _ fun j => rfl`.
-/
private theorem sigCob_one {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (σ : ℂ ≃+* ℂ) {Ξ Ξ' : AlgRep E a} (h : Ξ.d = Ξ'.d) (hσ : ConjMat σ h) (q : ℕ)
    (c : List ↥(⊤ : Subgroup (GL (Fin a) E)) → (GL (Fin a) (Af E) ⧸ U) → Fin Ξ.d → ℂ)
    (hc : HCob (levelRep ⊤ U (ratC Ξ)) q c) : HCob (levelRep ⊤ U (ratC Ξ')) q (sigC σ h c) := by
  let T : ((GL (Fin a) (Af E) ⧸ U) → Fin Ξ.d → ℂ) →+ ((GL (Fin a) (Af E) ⧸ U) → Fin Ξ'.d → ℂ) :=
    { toFun := fun f y i => σ (f y (Fin.cast h.symm i))
      map_zero' := by ext y i; simp
      map_add' := fun f g => by ext y i; simp }
  refine hcob_map _ _ T (fun γ f => ?_) q c hc
  funext y i
  change σ ((ratC Ξ γ *ᵥ f _) (Fin.cast h.symm i)) = (ratC Ξ' γ *ᵥ fun j => σ (f _ (Fin.cast h.symm j))) i
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, ← hσ _ _ _]
  exact Fintype.sum_equiv (finCongr h) _ _ fun j => rfl

/- English proof (translation)
Introduce `E _ _ _ a U σ Ξ Ξ' h hσ q c`. Use `⟨fun hc => ?_, sigCob_one U σ h hσ q c⟩` and prove the remaining obligations. Establish `hσ' : ConjMat σ.symm h.symm` using `fun γ i j => by`. Rewrite using `[RingEquiv.eq_symm_apply, ← hσ]`. Both sides reduce to the same expression.

Establish `e : sigC σ.symm h.symm (sigC σ h c) = c`. Use function extensionality and compare the values at `z y i`. Conclude with `σ.symm_apply_apply _`. Use `sigCob_one U σ.symm h.symm hσ' q _ hc` as an intermediate fact. Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Cj.sigCob :
    UpperTheory.V.Cj.SigCob := by
  intro E _ _ _ a U σ Ξ Ξ' h hσ q c
  refine ⟨fun hc => ?_, sigCob_one U σ h hσ q c⟩
  have hσ' : ConjMat σ.symm h.symm := fun γ i j => by
    rw [RingEquiv.eq_symm_apply, ← hσ]; rfl
  have e : sigC σ.symm h.symm (sigC σ h c) = c := by
    funext z y i
    exact σ.symm_apply_apply _
  have := sigCob_one U σ.symm h.symm hσ' q _ hc
  rwa [e] at this
