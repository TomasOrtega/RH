import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PerNat
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HarmLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.FinExC
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

/- English proof (translation)
Assemble the required witnesses or components as `⟨hα.equiv, hα.basic, fun X => Submodule.span_mono (by rintro _ ⟨φ, v, hφ, rfl⟩ exact ⟨φ, v, ⟨hφ.1, fun u hu => hφ.2.1 u (h hu), hφ.2.2⟩, rfl⟩) (hα.val X)⟩`.
-/
private theorem lev_mono {U U' : Subgroup (GL (Fin a) (Af E))} (h : U' ≤ U) {q : ℕ} {α : Geo.Co Ξ q}
    (hα : Geo.IsLev U Ξ α) : Geo.IsLev U' Ξ α :=
  ⟨hα.equiv, hα.basic, fun X => Submodule.span_mono (by
    rintro _ ⟨φ, v, hφ, rfl⟩
    exact ⟨φ, v, ⟨hφ.1, fun u hu => hφ.2.1 u (h hu), hφ.2.2⟩, rfl⟩) (hα.val X)⟩

/- English proof (translation)
Establish `ap : ∀ X, (s • α + β) X = s • α X + β X` using `fun X => rfl`. Use `⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩` and prove the remaining obligations. Rewrite using `[ap, ap, hα.equiv k X, hβ.equiv k X, map_add, map_smul]`. Rewrite using `[ap, hα.basic X i hi, hβ.basic X i hi, smul_zero, add_zero]`. Rewrite using `[ap]`.

Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (hα.val X)) (hβ.val X)`.
-/
private theorem lev_comb {U : Subgroup (GL (Fin a) (Af E))} {q : ℕ} (s : ℂ) {α β : Geo.Co Ξ q}
    (hα : Geo.IsLev U Ξ α) (hβ : Geo.IsLev U Ξ β) : Geo.IsLev U Ξ (s • α + β) := by
  have ap : ∀ X, (s • α + β) X = s • α X + β X := fun X => rfl
  refine ⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩
  · rw [ap, ap, hα.equiv k X, hβ.equiv k X, map_add, map_smul]
  · rw [ap, hα.basic X i hi, hβ.basic X i hi, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hα.val X)) (hβ.val X)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩`.
-/
private theorem lev_zero {U : Subgroup (GL (Fin a) (Af E))} {q : ℕ} : Geo.IsLev U Ξ (0 : Geo.Co Ξ q) :=
  ⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ _ a Ξ q`. Use `⟨fun U s α β hα hβ => lev_comb s hα hβ, fun U U' h α => ⟨lev_mono h, fun hα => ?_⟩, ?_⟩` and prove the remaining obligations. Consider the cases of `q with`. Consider the case `zero => exact hα`. Consider the case `succ q`.

Take `⟨η, h1, h2⟩` from `hα`. Conclude with `⟨η, lev_mono h h1, h2⟩`. Use `⟨{ carrier := {ω | Lev Ξ ω}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun ω => Iff.rfl, ?_⟩` and prove the remaining obligations. Introduce and unpack `α β ⟨U, u1, u2, u3⟩ ⟨U', v1, v2, v3⟩`. Establish `ho : IsOpen ((U ⊓ U' : Subgroup _) : Set (GL (Fin a) (Af E)))` using `u1.inter v1`.

Use `⟨U ⊓ U', ho, u2.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1, ?_⟩` and prove the remaining obligations. Use `lev_comb 1 (lev_mono inf_le_left u3) (lev_mono (U' := U ⊓ U') inf_le_right v3)` as an intermediate fact. Rewrite `this` using `[one_smul]`. Then use the resulting hypothesis. Take `⟨U, u1, u2⟩` from `GlobalTheory.GLIntegral.exists_isOpen_isCompact E a`. Conclude with `⟨U, u1, u2, lev_zero⟩`.

Introduce and unpack `s α ⟨U, u1, u2, u3⟩`. Use `lev_comb s u3 lev_zero` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `⟨U, u1, u2, this⟩`. Introduce and unpack `x ω ⟨U, u1, u2, u3⟩`.

Set `e : GL (Fin a) (Af E) ≃ₜ GL (Fin a) (Af E)` to `(Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)`. Establish `he : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup _) : Set (GL (Fin a) (Af E))) = e ⁻¹' U`. Use extensionality with `u`. Simplify using `[e]`. Use `⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, (perNat E a U _ x (fun u hu => ?_) Ξ q ω u3).1⟩` and prove the remaining obligations.

Rewrite using `[he]`. Conclude with `u1.preimage e.continuous`. Rewrite using `[he]`. Conclude with `e.isCompact_preimage.2 u2`. Simplify using `using hu`.
-/
theorem UpperTheory.V.Cj.levSub :
    UpperTheory.V.Cj.LevSub := by
  intro E _ _ _ a Ξ q
  refine ⟨fun U s α β hα hβ => lev_comb s hα hβ, fun U U' h α => ⟨lev_mono h, fun hα => ?_⟩, ?_⟩
  · cases q with
    | zero => exact hα
    | succ q =>
      obtain ⟨η, h1, h2⟩ := hα
      exact ⟨η, lev_mono h h1, h2⟩
  · refine ⟨{ carrier := {ω | Lev Ξ ω}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun ω => Iff.rfl, ?_⟩
    · rintro α β ⟨U, u1, u2, u3⟩ ⟨U', v1, v2, v3⟩
      have ho : IsOpen ((U ⊓ U' : Subgroup _) : Set (GL (Fin a) (Af E))) := u1.inter v1
      refine ⟨U ⊓ U', ho, u2.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun k hk => hk.1, ?_⟩
      have := lev_comb 1 (lev_mono inf_le_left u3) (lev_mono (U' := U ⊓ U') inf_le_right v3)
      rwa [one_smul] at this
    · obtain ⟨U, u1, u2⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E a
      exact ⟨U, u1, u2, lev_zero⟩
    · rintro s α ⟨U, u1, u2, u3⟩
      have := lev_comb s u3 lev_zero
      rw [add_zero] at this
      exact ⟨U, u1, u2, this⟩
    · rintro x ω ⟨U, u1, u2, u3⟩
      let e : GL (Fin a) (Af E) ≃ₜ GL (Fin a) (Af E) := (Homeomorph.mulLeft x⁻¹).trans (Homeomorph.mulRight x)
      have he : ((U.comap (MulAut.conj x⁻¹).toMonoidHom : Subgroup _) : Set (GL (Fin a) (Af E))) = e ⁻¹' U := by
        ext u
        simp [e]
      refine ⟨U.comap (MulAut.conj x⁻¹).toMonoidHom, ?_, ?_, (perNat E a U _ x (fun u hu => ?_) Ξ q ω u3).1⟩
      · rw [he]; exact u1.preimage e.continuous
      · rw [he]; exact e.isCompact_preimage.2 u2
      · simpa using hu
