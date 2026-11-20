import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin

noncomputable section

namespace PositivityTheory.Rg.BcB.F.FX.Bo.IsoInverse

open GlobalTheory.PRep

variable {G V V' : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

/- English proof (translation)
Use `show (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _`. Simplify using the standard rewrite rules.
-/
theorem mem_fixed_iff (ρ : Representation ℂ G V) (K : Subgroup G) (v : V) :
    v ∈ fixed ρ K ↔ ∀ h : K, ρ (h : G) v = v := by
  show (∀ h : K, ρ (h : G) v = ((1 : K →* ℂˣ) h : ℂ) • v) ↔ _
  simp

variable {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}

/- English proof (translation)
Introduce `g w`. Apply `L.injective` to reduce the goal to its premises. Rewrite using `[hL, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`.
-/
theorem symm_intertwines (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) :
    ∀ g w, L.symm (ρ' g w) = ρ g (L.symm w) := by
  intro g w
  apply L.injective
  rw [hL, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/- English proof (translation)
Introduce and unpack `_ ⟨v, hv, rfl⟩`. Rewrite `hv` using `[SetLike.mem_coe, mem_fixed_iff]`. Rewrite using `[mem_fixed_iff]`. Introduce `h`. Simplify using `only [LinearEquiv.coe_coe]`.

Rewrite using `[← hL, hv h]`.
-/
theorem map_fixed_le (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) (K : Subgroup G) :
    (fixed ρ K).map (L : V →ₗ[ℂ] V') ≤ fixed ρ' K := by
  rintro _ ⟨v, hv, rfl⟩
  rw [SetLike.mem_coe, mem_fixed_iff] at hv
  rw [mem_fixed_iff]
  intro h
  simp only [LinearEquiv.coe_coe]
  rw [← hL, hv h]

/- English proof (translation)
Use `le_antisymm (map_fixed_le L hL K) ?_` and prove the remaining obligations. Introduce `w hw`. Establish `hm : (L.symm : V' →ₗ[ℂ] V) w ∈ (fixed ρ' K).map (L.symm : V' →ₗ[ℂ] V)` using `⟨w, hw, rfl⟩`. Use `⟨L.symm w, map_fixed_le L.symm (symm_intertwines L hL) K hm, ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem map_fixed_eq (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) (K : Subgroup G) :
    (fixed ρ K).map (L : V →ₗ[ℂ] V') = fixed ρ' K := by
  refine le_antisymm (map_fixed_le L hL K) ?_
  intro w hw
  have hm : (L.symm : V' →ₗ[ℂ] V) w ∈ (fixed ρ' K).map (L.symm : V' →ₗ[ℂ] V) := ⟨w, hw, rfl⟩
  refine ⟨L.symm w, map_fixed_le L.symm (symm_intertwines L hL) K hm, ?_⟩
  simp

def imap (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) : ρ.IntertwiningMap ρ' :=
  ⟨(L : V →ₗ[ℂ] V'), fun g => by ext v; exact hL g v⟩

/- English proof (translation)
The claim follows from `GlobalTheory.SmGL.IsSubquotient.of_surjective (imap L hL) (fun w => ⟨L.symm w, L.apply_symm_apply w⟩)`.
-/
theorem isSubquotient_of (L : V ≃ₗ[ℂ] V') (hL : ∀ g v, L (ρ g v) = ρ' g (L v)) :
    GlobalTheory.SmGL.IsSubquotient ρ' ρ :=
  GlobalTheory.SmGL.IsSubquotient.of_surjective (imap L hL) (fun w => ⟨L.symm w, L.apply_symm_apply w⟩)

end PositivityTheory.Rg.BcB.F.FX.Bo.IsoInverse

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open GlobalTheory.PRep IsoInverse

/- English proof (translation)
Introduce `G V V' _ _ _ _ _ ρ ρ' ⟨e⟩ K`. Establish `hL : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v)` using `fun g v => Representation.IntertwiningMap.isIntertwining (f := e.toIntertwiningMap) (g := g) (v := v)`. Establish `hL'` using `symm_intertwines e.toLinearEquiv hL`. Set `F` to `e.toLinearEquiv.ofSubmodules _ _ (map_fixed_eq e.toLinearEquiv hL K)`. Use `⟨fun W _ _ τ => ⟨fun h => h.trans (isSubquotient_of e.toLinearEquiv.symm hL'), fun h => h.trans (isSubquotient_of e.toLinearEquiv hL)⟩, F.finrank_eq, ⟨fun _ => F.finiteDimensional, fun _ => F.symm.finiteDimensional⟩⟩` and prove the remaining obligations.
-/
theorem IsoInv_holds : IsoInv := by
  intro G V V' _ _ _ _ _ ρ ρ' ⟨e⟩ K
  have hL : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) := fun g v =>
    Representation.IntertwiningMap.isIntertwining (f := e.toIntertwiningMap) (g := g) (v := v)
  have hL' := symm_intertwines e.toLinearEquiv hL
  let F := e.toLinearEquiv.ofSubmodules _ _ (map_fixed_eq e.toLinearEquiv hL K)
  refine ⟨fun W _ _ τ => ⟨fun h => h.trans (isSubquotient_of e.toLinearEquiv.symm hL'),
    fun h => h.trans (isSubquotient_of e.toLinearEquiv hL)⟩, F.finrank_eq,
    ⟨fun _ => F.finiteDimensional, fun _ => F.symm.finiteDimensional⟩⟩

end PositivityTheory.Rg.BcB.F.FX.Bo
