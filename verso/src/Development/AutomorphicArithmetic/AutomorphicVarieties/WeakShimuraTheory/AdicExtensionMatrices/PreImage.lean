import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Establish `h1 : Algebra.adjoin B s ≤ (Algebra.adjoin B' s).restrictScalars B` using `Algebra.adjoin_le fun x hx => (Subalgebra.mem_restrictScalars B).2 (Algebra.subset_adjoin hx)`. Rewrite `h1` using `[h]`. Conclude with `eq_top_iff.2 fun x _ => (Subalgebra.mem_restrictScalars B).1 (h1 Algebra.mem_top)`.
-/
private theorem adjoin_top_of_tower {B B' A : Type} [CommRing B] [CommRing B'] [CommRing A] [Algebra B A] [Algebra B B']
    [Algebra B' A] [IsScalarTower B B' A] {s : Set A} (h : Algebra.adjoin B s = ⊤) : Algebra.adjoin B' s = ⊤ := by
  have h1 : Algebra.adjoin B s ≤ (Algebra.adjoin B' s).restrictScalars B :=
    Algebra.adjoin_le fun x hx => (Subalgebra.mem_restrictScalars B).2 (Algebra.subset_adjoin hx)
  rw [h] at h1
  exact eq_top_iff.2 fun x _ => (Subalgebra.mem_restrictScalars B).1 (h1 Algebra.mem_top)

/- English proof (translation)
Establish `hp' : Function.Surjective (p : Y.B →+* B')` using `hp`. Use `haveI : Nontrivial B' := j.domain_nontrivial`. Use `haveI : IsCO Λ B' := co_quot Λ Y.B B' p hp`. Use `letI : Algebra B' Y.A := j.toAlgebra`. Use `letI : Algebra Y.B B' := (p : Y.B →+* B').toAlgebra`.

Use `haveI t1 : IsScalarTower Y.B B' Y.A := IsScalarTower.of_algebraMap_eq fun b => (hj b).symm`. Use `haveI t2 : IsScalarTower Λ B' Y.A := IsScalarTower.of_algebraMap_eq fun b => by`. Rewrite using `[← p.commutes, IsScalarTower.algebraMap_apply Λ Y.B Y.A]`. Conclude with `(hj _).symm`. Establish `hm : (maximalIdeal Y.B).map (p : Y.B →+* B') = maximalIdeal B'` using `IsLocalRing.map_maximalIdeal_of_surjective _ hp'`.

Establish `hle : maximalIdeal Y.B ≤ (maximalIdeal B').comap (p : Y.B →+* B')`. Rewrite using `[← hm]`. Conclude with `Ideal.le_comap_map`. Establish `hc : (algebraMap B' Y.A).comp (p : Y.B →+* B') = algebraMap Y.B Y.A` using `RingHom.ext hj`. Establish `hr : (res Λ B' : B' →+* ResidueField Λ).comp (p : Y.B →+* B') = (res Λ Y.B : Y.B →+* ResidueField Λ)` using `RingHom.ext fun b => res_map p b`.

Use `haveI := Y.ft`. Use `⟨{ A := Y.A, B := B', ft := Algebra.FiniteType.of_restrictScalars_finiteType Y.B _ _ P := Y.P, pair := Y.pair, cont := ?_, gen := adjoin_top_of_tower Y.gen cp := fun g => (Y.cp g).map (p : Y.B →+* B') cp_map := fun g => ?_, cp_cont := fun n => ?_, cp_red := fun g => ?_ ψ := fun v …` and prove the remaining obligations. Rewrite using `[← hm, Ideal.map_map, hc]`. Conclude with `Y.cont`. Rewrite using `[Polynomial.map_map, hc, Y.cp_map]`.

Simplify using `only [coeff_map]`. Conclude with `adicCont_map (p : Y.B →+* B') hle (Y.cp_cont n)`. Rewrite using `[Polynomial.map_map, hr, Y.cp_red]`. Establish `h : f.comp p = f'.comp p` using `Y.genB R _ _ (fun g n => by`. Establish `h3` using `h1 g n`.

Rewrite `h3` using `[coeff_map]`. Conclude with `h3) h2`. Use `AlgHom.ext fun x => ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `hp x`. Conclude with `AlgHom.congr_fun h b`.
-/
private theorem pre_of_surj {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a) [Nontrivial Y.A] (B' : Type) [CommRing B'] [Algebra Λ B']
    (p : Y.B →ₐ[Λ] B') (hp : Function.Surjective p) (j : B' →+* Y.A) (hj : ∀ b, j (p b) = algebraMap Y.B Y.A b)
    (hi : Function.Injective j) : ∃ Y' : Pre Φ a, Function.Injective (algebraMap Y'.B Y'.A) := by
  have hp' : Function.Surjective (p : Y.B →+* B') := hp
  haveI : Nontrivial B' := j.domain_nontrivial
  haveI : IsCO Λ B' := co_quot Λ Y.B B' p hp
  letI : Algebra B' Y.A := j.toAlgebra
  letI : Algebra Y.B B' := (p : Y.B →+* B').toAlgebra
  haveI t1 : IsScalarTower Y.B B' Y.A := IsScalarTower.of_algebraMap_eq fun b => (hj b).symm
  haveI t2 : IsScalarTower Λ B' Y.A := IsScalarTower.of_algebraMap_eq fun b => by
    rw [← p.commutes, IsScalarTower.algebraMap_apply Λ Y.B Y.A]
    exact (hj _).symm
  have hm : (maximalIdeal Y.B).map (p : Y.B →+* B') = maximalIdeal B' :=
    IsLocalRing.map_maximalIdeal_of_surjective _ hp'
  have hle : maximalIdeal Y.B ≤ (maximalIdeal B').comap (p : Y.B →+* B') := by
    rw [← hm]; exact Ideal.le_comap_map
  have hc : (algebraMap B' Y.A).comp (p : Y.B →+* B') = algebraMap Y.B Y.A := RingHom.ext hj
  have hr : (res Λ B' : B' →+* ResidueField Λ).comp (p : Y.B →+* B') =
      (res Λ Y.B : Y.B →+* ResidueField Λ) := RingHom.ext fun b => res_map p b
  haveI := Y.ft
  refine ⟨{ A := Y.A, B := B', ft := Algebra.FiniteType.of_restrictScalars_finiteType Y.B _ _
            P := Y.P, pair := Y.pair, cont := ?_, gen := adjoin_top_of_tower Y.gen
            cp := fun g => (Y.cp g).map (p : Y.B →+* B')
            cp_map := fun g => ?_, cp_cont := fun n => ?_, cp_red := fun g => ?_
            ψ := fun v i s => p (Y.ψ v i s)
            ψ_map := fun v i s hs => (hj _).trans (Y.ψ_map v i s hs)
            ψ_cont := fun v i => adicCont_map (p : Y.B →+* B') hle (Y.ψ_cont v i)
            ψ_red := fun v i s hs => (res_map p _).trans (Y.ψ_red v i s hs)
            genB := fun R _ _ _ f f' h1 h2 => ?_
            univ := Y.univ }, hi⟩
  · rw [← hm, Ideal.map_map, hc]
    exact Y.cont
  · rw [Polynomial.map_map, hc, Y.cp_map]
  · simp only [coeff_map]
    exact adicCont_map (p : Y.B →+* B') hle (Y.cp_cont n)
  · rw [Polynomial.map_map, hr, Y.cp_red]
  · have h : f.comp p = f'.comp p := Y.genB R _ _ (fun g n => by
      have h3 := h1 g n
      rw [coeff_map] at h3
      exact h3) h2
    refine AlgHom.ext fun x => ?_
    obtain ⟨b, rfl⟩ := hp x
    exact AlgHom.congr_fun h b

/- English proof (translation)
Introduce `O Γ _ _ _ Φ Λ _ _ a Y hA`. Conclude with `pre_of_surj Y (Y.B ⧸ RingHom.ker (algebraMap Y.B Y.A)) (Ideal.Quotient.mkₐ Λ _) Ideal.Quotient.mk_surjective (RingHom.kerLift (algebraMap Y.B Y.A)) (fun b => RingHom.kerLift_mk _ b) (RingHom.kerLift_injective _)`.
-/
theorem UpperTheory.V.Ws.sxPreImage :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} (Y : Pre Φ a), Nontrivial Y.A → ∃ Y' : Pre Φ a, Function.Injective (algebraMap Y'.B Y'.A) := by
  intro O Γ _ _ _ Φ Λ _ _ a Y hA
  exact pre_of_surj Y (Y.B ⧸ RingHom.ker (algebraMap Y.B Y.A)) (Ideal.Quotient.mkₐ Λ _) Ideal.Quotient.mk_surjective
    (RingHom.kerLift (algebraMap Y.B Y.A)) (fun b => RingHom.kerLift_mk _ b) (RingHom.kerLift_injective _)
