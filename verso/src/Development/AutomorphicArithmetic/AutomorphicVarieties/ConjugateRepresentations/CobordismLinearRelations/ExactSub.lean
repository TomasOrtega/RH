import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerNat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.LevSub
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

/- English proof (translation)
Establish `e : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) = ((Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)) ⁻¹' (U : Set G)`. Use extensionality with `u`. Simplify using the standard rewrite rules. Use `⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, fun u hu => by simpa using hu⟩` and prove the remaining obligations. Rewrite using `[e]`.

Conclude with `h1.preimage (Homeomorph.continuous _)`. Rewrite using `[e]`. Conclude with `(Homeomorph.isCompact_preimage _).2 h2`.
-/
private theorem conj_level {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (U : Subgroup G)
    (h1 : IsOpen (U : Set G)) (h2 : IsCompact (U : Set G)) (x : G) :
    ∃ U' : Subgroup G, IsOpen (U' : Set G) ∧ IsCompact (U' : Set G) ∧ ∀ u ∈ U', x⁻¹ * u * x ∈ U := by
  have e : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) : Set G) =
      ((Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)) ⁻¹' (U : Set G) := by
    ext u
    simp
  refine ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, fun u hu => by simpa using hu⟩
  · rw [e]; exact h1.preimage (Homeomorph.continuous _)
  · rw [e]; exact (Homeomorph.isCompact_preimage _).2 h2

/- English proof (translation)
Introduce `E _ _ _ a Ξ q`. Establish `comb : ∀ (s : ℂ) (α β : Co Ξ q), Exact Ξ α → Exact Ξ β → Exact Ξ (s • α + β)`. Introduce and unpack `s α β ⟨U, u1, u2, hα⟩ ⟨V, v1, v2, hβ⟩`. Establish `hα'` using `((levSub E a Ξ q).2.1 U (U ⊓ V) inf_le_left α).2 hα`. Establish `hβ'` using `((levSub E a Ξ q).2.1 V (U ⊓ V) inf_le_right β).2 hβ`.

Use `⟨U ⊓ V, u1.inter v1, u2.inter_right (V.isClosed_of_isOpen v1), ?_⟩` and prove the remaining obligations. Consider the cases of `q with`. Consider the case `zero`. Express the relevant statement in the definitionally equal form `α = 0 at hα'`. Express the relevant statement in the definitionally equal form `β = 0 at hβ'`.

Express the relevant statement in the definitionally equal form `s • α + β = 0`. Rewrite using `[hα', hβ', smul_zero, add_zero]`. Consider the case `succ q`. Take `⟨η, e1, rfl⟩` from `hα'`. Take `⟨ζ, z1, rfl⟩` from `hβ'`.

Conclude with `⟨s • η + ζ, (levSub E a Ξ q).1 _ s η ζ e1 z1, dCo_comb s η ζ⟩`. Establish `hz : Exact Ξ (0 : Co Ξ q)`. Take `⟨L, hL, -⟩` from `(levSub E a Ξ q).2.2`. Take `⟨U, u1, u2, -⟩` from `(hL 0).1 L.zero_mem`. Use `⟨U, u1, u2, ?_⟩` and prove the remaining obligations.

Consider the cases of `q with`. Consider the case `zero => rfl`. Consider the case `succ q`. Conclude with `⟨0, ⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩, AlternatingMap.ext fun X => by simp [dCo_apply]⟩`. Use `⟨{ carrier := {ω | Exact Ξ ω} add_mem' := fun {α β} hα hβ => by simpa only [one_smul, Set.mem_ofPred_eq] using comb 1 α β hα hβ zero_mem' := hz smul_mem' := fun s α hα => by simpa only [add_zero, Set.mem_ofPred_eq] using comb s α 0 hα hz }, fun _ => Iff.rfl, ?_⟩` and prove the remaining obligations.

Introduce and unpack `x ω ⟨U, u1, u2, hω⟩`. Take `⟨U', v1, v2, hx⟩` from `conj_level U u1 u2 x`. Use `⟨U', v1, v2, ?_⟩` and prove the remaining obligations. Consider the cases of `q with`. Consider the case `zero`.

Express the relevant statement in the definitionally equal form `ω = 0 at hω`. Express the relevant statement in the definitionally equal form `trans x ω = 0`. Rewrite using `[hω, ← transRep_apply, map_zero]`. Consider the case `succ q`. Take `⟨η, e1, rfl⟩` from `hω`.

Take `⟨p1, p2, -⟩` from `perNat E a U U' x hx Ξ q η e1`. Conclude with `⟨trans x η, p1, p2⟩`.
-/
theorem UpperTheory.V.Cj.exactSub :
    UpperTheory.V.Cj.ExactSub := by
  intro E _ _ _ a Ξ q
  have comb : ∀ (s : ℂ) (α β : Co Ξ q), Exact Ξ α → Exact Ξ β → Exact Ξ (s • α + β) := by
    rintro s α β ⟨U, u1, u2, hα⟩ ⟨V, v1, v2, hβ⟩
    have hα' := ((levSub E a Ξ q).2.1 U (U ⊓ V) inf_le_left α).2 hα
    have hβ' := ((levSub E a Ξ q).2.1 V (U ⊓ V) inf_le_right β).2 hβ
    refine ⟨U ⊓ V, u1.inter v1, u2.inter_right (V.isClosed_of_isOpen v1), ?_⟩
    cases q with
    | zero =>
      change α = 0 at hα'
      change β = 0 at hβ'
      change s • α + β = 0
      rw [hα', hβ', smul_zero, add_zero]
    | succ q =>
      obtain ⟨η, e1, rfl⟩ := hα'
      obtain ⟨ζ, z1, rfl⟩ := hβ'
      exact ⟨s • η + ζ, (levSub E a Ξ q).1 _ s η ζ e1 z1, dCo_comb s η ζ⟩
  have hz : Exact Ξ (0 : Co Ξ q) := by
    obtain ⟨L, hL, -⟩ := (levSub E a Ξ q).2.2
    obtain ⟨U, u1, u2, -⟩ := (hL 0).1 L.zero_mem
    refine ⟨U, u1, u2, ?_⟩
    cases q with
    | zero => rfl
    | succ q =>
      exact ⟨0, ⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩,
        AlternatingMap.ext fun X => by simp [dCo_apply]⟩
  refine ⟨{ carrier := {ω | Exact Ξ ω}
            add_mem' := fun {α β} hα hβ => by simpa only [one_smul, Set.mem_ofPred_eq] using comb 1 α β hα hβ
            zero_mem' := hz
            smul_mem' := fun s α hα => by simpa only [add_zero, Set.mem_ofPred_eq] using comb s α 0 hα hz }, fun _ => Iff.rfl, ?_⟩
  rintro x ω ⟨U, u1, u2, hω⟩
  obtain ⟨U', v1, v2, hx⟩ := conj_level U u1 u2 x
  refine ⟨U', v1, v2, ?_⟩
  cases q with
  | zero =>
    change ω = 0 at hω
    change trans x ω = 0
    rw [hω, ← transRep_apply, map_zero]
  | succ q =>
    obtain ⟨η, e1, rfl⟩ := hω
    obtain ⟨p1, p2, -⟩ := perNat E a U U' x hx Ξ q η e1
    exact ⟨trans x η, p1, p2⟩
