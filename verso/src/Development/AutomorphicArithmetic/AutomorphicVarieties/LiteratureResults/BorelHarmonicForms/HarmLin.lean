import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {Ξ : AlgRep E a}

/- English proof (translation)
Assemble the required witnesses or components as `⟨hω.equiv, hω.basic, fun X => Submodule.span_mono (by rintro _ ⟨φ, v, hφ, rfl⟩ exact ⟨φ, v, h φ hφ, rfl⟩) (hω.val X)⟩`.
-/
private theorem rel_mono {P Q : Sm E a → Prop} (h : ∀ φ, P φ → Q φ) {q : ℕ}
    {ω : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))} (hω : IsRelCochain Ξ P ω) :
    IsRelCochain Ξ Q ω :=
  ⟨hω.equiv, hω.basic, fun X => Submodule.span_mono (by
    rintro _ ⟨φ, v, hφ, rfl⟩
    exact ⟨φ, v, h φ hφ, rfl⟩) (hω.val X)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨hφ.1, fun u hu => hφ.2.1 u (h hu), hφ.2.2⟩`.
-/
private theorem level_mono {U U' : Subgroup (GL (Fin a) (Af E))} (h : U' ≤ U) (φ : Sm E a) (hφ : IsLevelFn U Ξ φ) :
    IsLevelFn U' Ξ φ := ⟨hφ.1, fun u hu => hφ.2.1 u (h hu), hφ.2.2⟩

variable {U : Subgroup (GL (Fin a) (Af E))} {r : ℝ} {n : ℕ} {e : Fin n → GlobalTheory.GKCoh.Herm E a}

/- English proof (translation)
Use `⟨⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `AlternatingMap.ext fun X => by simp [dCo_apply]`. Consider the cases of `q with`. Consider the case `zero => trivial`. Consider the case `succ q => exact AlternatingMap.ext fun X => by simp [del_apply]`.
-/
private theorem harm_zero {q : ℕ} :
    IsHarm U Ξ r e (0 : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))) := by
  refine ⟨⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩, ?_, ?_⟩
  · exact AlternatingMap.ext fun X => by simp [dCo_apply]
  · cases q with
    | zero => trivial
    | succ q => exact AlternatingMap.ext fun X => by simp [del_apply]

/- English proof (translation)
Establish `ap : ∀ X, (c • ω + η) X = c • ω X + η X` using `fun X => rfl`. Use `⟨⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ap, ap, hω.rel.equiv k X, hη.rel.equiv k X, map_add, map_smul]`. Rewrite using `[ap, hω.rel.basic X i hi, hη.rel.basic X i hi, smul_zero, add_zero]`. Rewrite using `[ap]`.

Conclude with `Submodule.add_mem _ (Submodule.smul_mem _ _ (hω.rel.val X)) (hη.rel.val X)`. Use `AlternatingMap.ext fun X => ?_` and prove the remaining obligations. Establish `h1` using `DFunLike.congr_fun hω.closed X`. Establish `h2` using `DFunLike.congr_fun hη.closed X`. Rewrite `h1`, `h2`, the goal using `[dCo_apply, AlternatingMap.zero_apply]`.

Simplify using `only [ap, map_add, map_smul, smul_add, Finset.sum_add_distrib, h2, add_zero]`. Rewrite using `[← smul_zero c, ← h1, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => smul_comm _ _ _`. Consider the cases of `q with`. Consider the case `zero => trivial`.

Consider the case `succ q`. Use `AlternatingMap.ext fun X => ?_` and prove the remaining obligations. Establish `h1` using `DFunLike.congr_fun (show del _ e ω = 0 from hω.coclosed) X`. Establish `h2` using `DFunLike.congr_fun (show del _ e η = 0 from hη.coclosed) X`. Rewrite `h1`, `h2`, the goal using `[del_apply, AlternatingMap.zero_apply]`.

Simplify using `only [ap, map_add, map_smul, Finset.sum_add_distrib, h2, add_zero, ← Finset.smul_sum, h1, smul_zero]`.
-/
private theorem harm_comb {q : ℕ} (c : ℂ)
    {ω η : GlobalTheory.GKCoh.Herm E a [⋀^Fin q]→ₗ[ℝ] (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ))} (hω : IsHarm U Ξ r e ω)
    (hη : IsHarm U Ξ r e η) : IsHarm U Ξ r e (c • ω + η) := by
  have ap : ∀ X, (c • ω + η) X = c • ω X + η X := fun X => rfl
  refine ⟨⟨fun k X => ?_, fun X i hi => ?_, fun X => ?_⟩, ?_, ?_⟩
  · rw [ap, ap, hω.rel.equiv k X, hη.rel.equiv k X, map_add, map_smul]
  · rw [ap, hω.rel.basic X i hi, hη.rel.basic X i hi, smul_zero, add_zero]
  · rw [ap]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (hω.rel.val X)) (hη.rel.val X)
  · refine AlternatingMap.ext fun X => ?_
    have h1 := DFunLike.congr_fun hω.closed X
    have h2 := DFunLike.congr_fun hη.closed X
    rw [dCo_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
    simp only [ap, map_add, map_smul, smul_add, Finset.sum_add_distrib, h2, add_zero]
    rw [← smul_zero c, ← h1, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · cases q with
    | zero => trivial
    | succ q =>
      refine AlternatingMap.ext fun X => ?_
      have h1 := DFunLike.congr_fun (show del _ e ω = 0 from hω.coclosed) X
      have h2 := DFunLike.congr_fun (show del _ e η = 0 from hη.coclosed) X
      rw [del_apply, AlternatingMap.zero_apply] at h1 h2 ⊢
      simp only [ap, map_add, map_smul, Finset.sum_add_distrib, h2, add_zero, ← Finset.smul_sum, h1, smul_zero]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ _ a n e U Ξ r q`. Use `⟨fun s ω c h => ?_, fun ω => ⟨fun h => rel_mono (fun _ hφ => hφ.1) h.rel, fun U' hU => ⟨fun h => ⟨rel_mono (fun φ hφ => ⟨level_mono hU φ hφ.1, hφ.2⟩) h.rel, h.closed, h.coclosed⟩, rel_mono (level_mono hU)⟩⟩⟩` and prove the remaining obligations. Proceed by induction on `(Finset.univ : Finset (Fin s)) using Finset.cons_induction with`. Consider the case `empty => exact harm_zero`. Consider the case `cons j t hj ih`.

Rewrite using `[Finset.sum_cons]`. Conclude with `harm_comb _ (h j) ih`.
-/
theorem UpperTheory.V.Lit.Bor.harmLin :
    UpperTheory.V.Lit.Bor.HarmLin := by
  intro E _ _ _ a n e U Ξ r q
  refine ⟨fun s ω c h => ?_, fun ω => ⟨fun h => rel_mono (fun _ hφ => hφ.1) h.rel, fun U' hU =>
    ⟨fun h => ⟨rel_mono (fun φ hφ => ⟨level_mono hU φ hφ.1, hφ.2⟩) h.rel, h.closed, h.coclosed⟩,
      rel_mono (level_mono hU)⟩⟩⟩
  induction (Finset.univ : Finset (Fin s)) using Finset.cons_induction with
  | empty => exact harm_zero
  | cons j t hj ih =>
    rw [Finset.sum_cons]
    exact harm_comb _ (h j) ih
