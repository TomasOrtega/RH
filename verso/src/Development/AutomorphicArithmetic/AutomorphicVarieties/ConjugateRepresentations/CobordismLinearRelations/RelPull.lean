import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerNat
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

/- English proof (translation)
Consider the cases of `q with`. Consider the case `zero`. Introduce `z hz`. Use `beta_reduce`. Rewrite using `[h z hz, map_zero]`.

Consider the case `succ q`. Take `⟨b, b1, b2⟩` from `h`. Use `⟨fun z => P (b z), fun γ z hz => ?_, fun z hz => ?_⟩` and prove the remaining obligations. Use `beta_reduce`. Rewrite using `[b1 γ z hz, hP]`.

Use `beta_reduce`. Rewrite using `[b2 z hz]`. Simplify using `only [hd, map_sum, map_zsmul]`.
-/
private theorem cob_map {Γ M N : Type} [Group Γ] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (ρ : Representation ℂ Γ M) (ρ' : Representation ℂ Γ N) (P : M →ₗ[ℂ] N) (hP : ∀ γ m, P (ρ γ m) = ρ' γ (P m))
    (q : ℕ) (c : List Γ → M) (h : HCob ρ q c) : HCob ρ' q (fun z => P (c z)) := by
  cases q with
  | zero =>
    intro z hz
    beta_reduce
    rw [h z hz, map_zero]
  | succ q =>
    obtain ⟨b, b1, b2⟩ := h
    refine ⟨fun z => P (b z), fun γ z hz => ?_, fun z hz => ?_⟩
    · beta_reduce
      rw [b1 γ z hz, hP]
    · beta_reduce
      rw [b2 z hz]
      simp only [hd, map_sum, map_zsmul]

/- English proof (translation)
Establish `wd : ∀ y y' : G, (QuotientGroup.leftRel U') y y' → ((y * x : G) : G ⧸ U) = ((y' * x : G) : G ⧸ U)`. Introduce `y y' hy`. Establish `h1` using `hx _ (QuotientGroup.leftRel_apply.1 hy)`. Use `QuotientGroup.eq.2 ?_` and prove the remaining obligations. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use `group`. Use `⟨Quotient.lift _ wd, fun _ => rfl, fun g s => ?_⟩` and prove the remaining obligations. Proceed by induction on `s using QuotientGroup.induction_on with | H y => ?_`. Express the relevant statement in the definitionally equal form `((g * y * x : G) : G ⧸ U) = ((g * (y * x) : G) : G ⧸ U)`. Rewrite using `[mul_assoc]`.
-/
private theorem coset_map {G : Type} [Group G] {U U' : Subgroup G} {x : G} (hx : ∀ u ∈ U', x⁻¹ * u * x ∈ U) :
    ∃ f : G ⧸ U' → G ⧸ U, (∀ y : G, f y = ((y * x : G) : G ⧸ U)) ∧ ∀ (g : G) s, f (g • s) = g • f s := by
  have wd : ∀ y y' : G, (QuotientGroup.leftRel U') y y' → ((y * x : G) : G ⧸ U) = ((y' * x : G) : G ⧸ U) := by
    intro y y' hy
    have h1 := hx _ (QuotientGroup.leftRel_apply.1 hy)
    refine QuotientGroup.eq.2 ?_
    convert h1 using 1
    group
  refine ⟨Quotient.lift _ wd, fun _ => rfl, fun g s => ?_⟩
  induction s using QuotientGroup.induction_on with | H y => ?_
  change ((g * y * x : G) : G ⧸ U) = ((g * (y * x) : G) : G ⧸ U)
  rw [mul_assoc]

/- English proof (translation)
Introduce `E _ _ _ a U U' x hx σ Ξ Ξ' h q α β ⟨hα, hβ, c, c', p, p', hc⟩`. Take `⟨f, f1, f2⟩` from `coset_map hx`. Take `⟨a1, -, a2⟩` from `perNat E a U U' x hx Ξ q α hα`. Take `⟨b1, -, b2⟩` from `perNat E a U U' x hx Ξ' q β hβ`. Use `⟨a1, b1, fun z s => c z (f s), fun z s => c' z (f s), a2 c _ (fun z y => by rw [f1]) p, b2 c' _ (fun z y => by rw [f1]) p', ?_⟩` and prove the remaining obligations.

Use `cob_map (levelRep ⊤ U (ratC Ξ')) (levelRep ⊤ U' (ratC Ξ')) (LinearMap.funLeft ℂ _ f) (fun γ m => ?_) q _ hc` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Express the relevant statement in the definitionally equal form `_ *ᵥ m (_ • f s) = _ *ᵥ m (f (_ • s))`. Rewrite using `[f2]`.
-/
theorem UpperTheory.V.Cj.relPull :
    UpperTheory.V.Cj.RelPull := by
  intro E _ _ _ a U U' x hx σ Ξ Ξ' h q α β ⟨hα, hβ, c, c', p, p', hc⟩
  obtain ⟨f, f1, f2⟩ := coset_map hx
  obtain ⟨a1, -, a2⟩ := perNat E a U U' x hx Ξ q α hα
  obtain ⟨b1, -, b2⟩ := perNat E a U U' x hx Ξ' q β hβ
  refine ⟨a1, b1, fun z s => c z (f s), fun z s => c' z (f s), a2 c _ (fun z y => by rw [f1]) p,
    b2 c' _ (fun z y => by rw [f1]) p', ?_⟩
  refine cob_map (levelRep ⊤ U (ratC Ξ')) (levelRep ⊤ U' (ratC Ξ')) (LinearMap.funLeft ℂ _ f) (fun γ m => ?_) q _ hc
  funext s
  change _ *ᵥ m (_ • f s) = _ *ᵥ m (f (_ • s))
  rw [f2]
