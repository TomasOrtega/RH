import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrNoeth
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxUnivD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SubMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SxSubRD
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.CoreCp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.ContGr
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.CoreGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.GenZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.QuotPowNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PreOfCore
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.SplitRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PreImage
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PreLine

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS`. Use `haveI : IsCO Λ (ResidueField Λ) := (co_res Λ).1`. Take `⟨R, _, _, _, D, hU⟩` from `sxUnivD l hS`. Take `⟨W, hW⟩` from `sxGradD hU`. Use `haveI : IsCO Λ (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal Λ (ℤ × ℤ) R W hW.max`.

Use `haveI : IsScalarTower Λ (W.gr 0) W.A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Take `⟨D', hD', hrep⟩` from `sxSubRD a W.A D (fun g i j => W.part_le_A (hW.ent g i j)) (fun v i s => W.part_le_A (hW.chr v i s)) hU.1.rep`. Establish `hψ : ∀ v i s, (W.A.val (D'.ψ v i s) : R) = D.ψ v i s`. Introduce `v i s`. Rewrite using `[← hD']`.

Both sides reduce to the same expression. Establish `hr : ∀ g i j, (W.A.val (D'.r g i j) : R) = D.r g i j`. Introduce `g i j`. Rewrite using `[← hD']`. Both sides reduce to the same expression.

Take `⟨cp, hcp1, hcp2, hcp3⟩` from `sxCoreCp hU.1 hW D' hD'`. Set `ψ : (v : Φ.ι) → Fin 4 → Φ.Gv v → W.gr 0` to `fun v i s => ⟨D'.ψ v i s, by show W.A.val (D'.ψ v i s) ∈ W.part 0`. Rewrite using `[hψ]`. Conclude with `hW.chr v i s⟩`. Establish `hcont` using `sxContGr W hW.max (Γ := Γ)`.

Set `C : Core Φ a` to `{ A := W.A B := W.gr 0 ft := (gr_noeth Λ (ℤ × ℤ) R W hW.max).2.1 D := D' rep := hrep cont := fun i j => hcont.1 (wt i j) (fun g => D'.r g i j) (fun g => by show W.A.val (D'.r g i j) ∈ W.part (wt i j)`. Rewrite using `[hr]`. Conclude with `hW.ent g i j)`. Use the proof step `(by`. Simplify using `only [Subalgebra.coe_val] at hr`.

Simplify using `only [hr]`. Conclude with `hU.1.cont i j)`. Use `gen := sxCoreGen hW D' hD'`. Use `cp := cp`. Use `cp_map := hcp1`.

Use `cp_cont := hcp2`. Use `cp_red := hcp3`. Use `ψ := ψ`. Use `ψ_map := fun _ _ _ => rfl`. Use `ψ_cont := fun v i => (sxContGr W hW.max (Γ := Φ.Gv v)).2 (ψ v i) (by`.

Simplify using `only [Subalgebra.coe_val] at hψ`. Simplify using `only [ψ, hψ]`. Conclude with `hU.1.contψ v i)`. Use `ψ_red := fun v i s => by`. Establish `h` using `res_map (O := Λ) ((W.A.val).comp (IsScalarTower.toAlgHom Λ (W.gr 0) W.A)) (ψ v i s)`.

Rewrite using `[← h]`. Establish `h2 : ((W.A.val).comp (IsScalarTower.toAlgHom Λ (W.gr 0) W.A)) (ψ v i s) = D.ψ v i s` using `hψ v i s`. Rewrite using `[h2]`. Conclude with `hU.1.redψ v i s`. Use `genB := sxGenZero hS.ok hU.1 hW D' hD' cp hcp1 ψ (fun _ _ _ => rfl)`.

Use `univ := sxNearA hU hW D' hD' }`. Take `⟨Y⟩` from `sxPreOfCore (fun v s hs => (hS.mu v s hs).1) C`. Take `⟨hres, hlift⟩` from `sxSplitRes hS`. Take `⟨f, -⟩` from `Y.univ (ResidueField Λ) _ _ hres hlift`. Use `haveI : Nontrivial Y.A := f.toRingHom.domain_nontrivial`.

Take `⟨Y', hinj⟩` from `sxPreImage Y this`. Conclude with `⟨Y'.toSpace hinj (sxPreLine Y')⟩`.
-/
theorem UpperTheory.V.Ws.spaceEx :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → Nonempty (Space Φ a) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hS
  haveI : IsCO Λ (ResidueField Λ) := (co_res Λ).1
  obtain ⟨R, _, _, _, D, hU⟩ := sxUnivD l hS
  obtain ⟨W, hW⟩ := sxGradD hU
  haveI : IsCO Λ (W.gr 0) := wPres_gr_zero_isCO_of_mem_maximalIdeal Λ (ℤ × ℤ) R W hW.max
  haveI : IsScalarTower Λ (W.gr 0) W.A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨D', hD', hrep⟩ := sxSubRD a W.A D (fun g i j => W.part_le_A (hW.ent g i j))
    (fun v i s => W.part_le_A (hW.chr v i s)) hU.1.rep
  have hψ : ∀ v i s, (W.A.val (D'.ψ v i s) : R) = D.ψ v i s := by
    intro v i s
    rw [← hD']
    rfl
  have hr : ∀ g i j, (W.A.val (D'.r g i j) : R) = D.r g i j := by
    intro g i j
    rw [← hD']
    rfl
  obtain ⟨cp, hcp1, hcp2, hcp3⟩ := sxCoreCp hU.1 hW D' hD'
  let ψ : (v : Φ.ι) → Fin 4 → Φ.Gv v → W.gr 0 := fun v i s =>
    ⟨D'.ψ v i s, by
      show W.A.val (D'.ψ v i s) ∈ W.part 0
      rw [hψ]
      exact hW.chr v i s⟩
  have hcont := sxContGr W hW.max (Γ := Γ)
  let C : Core Φ a :=
    { A := W.A
      B := W.gr 0
      ft := (gr_noeth Λ (ℤ × ℤ) R W hW.max).2.1
      D := D'
      rep := hrep
      cont := fun i j => hcont.1 (wt i j) (fun g => D'.r g i j)
        (fun g => by
          show W.A.val (D'.r g i j) ∈ W.part (wt i j)
          rw [hr]
          exact hW.ent g i j)
        (by
          simp only [Subalgebra.coe_val] at hr
          simp only [hr]
          exact hU.1.cont i j)
      gen := sxCoreGen hW D' hD'
      cp := cp
      cp_map := hcp1
      cp_cont := hcp2
      cp_red := hcp3
      ψ := ψ
      ψ_map := fun _ _ _ => rfl
      ψ_cont := fun v i => (sxContGr W hW.max (Γ := Φ.Gv v)).2 (ψ v i) (by
        simp only [Subalgebra.coe_val] at hψ
        simp only [ψ, hψ]
        exact hU.1.contψ v i)
      ψ_red := fun v i s => by
        have h := res_map (O := Λ) ((W.A.val).comp (IsScalarTower.toAlgHom Λ (W.gr 0) W.A)) (ψ v i s)
        rw [← h]
        have h2 : ((W.A.val).comp (IsScalarTower.toAlgHom Λ (W.gr 0) W.A)) (ψ v i s) = D.ψ v i s := hψ v i s
        rw [h2]
        exact hU.1.redψ v i s
      genB := sxGenZero hS.ok hU.1 hW D' hD' cp hcp1 ψ (fun _ _ _ => rfl)
      univ := sxNearA hU hW D' hD' }
  obtain ⟨Y⟩ := sxPreOfCore (fun v s hs => (hS.mu v s hs).1) C
  obtain ⟨hres, hlift⟩ := sxSplitRes hS
  obtain ⟨f, -⟩ := Y.univ (ResidueField Λ) _ _ hres hlift
  haveI : Nontrivial Y.A := f.toRingHom.domain_nontrivial
  obtain ⟨Y', hinj⟩ := sxPreImage Y this
  exact ⟨Y'.toSpace hinj (sxPreLine Y')⟩
