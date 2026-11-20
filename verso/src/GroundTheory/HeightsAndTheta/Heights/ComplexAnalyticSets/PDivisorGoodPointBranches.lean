import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDivisorGoodPointBranches
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GoodPointBranchExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets Metric Set

noncomputable section

/- English proof (translation)
Introduce `n d J u M q _hJ _hdim _hu hqJ hqu hreg hchart hdouble`. Take `⟨A, O, V, g, -, hV, hqV, hg, hAg, hS⟩` from `hreg`. Take `⟨N₀, hN₀, hdbl⟩` from `hdouble`. Set `F : Set (Fin n ⊕ Fin M.m → ℂ)` to `{w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q}`. Establish `hmemF : ∀ w, w ∈ F ↔ (w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q)` using `fun w => Iff.rfl`.

Establish `hFfin : F.Finite` using `NormalModelFibre.fibre_finite M q`. Take `⟨G, hGo, hGd⟩` from `hFfin.t2_separation`. Set `_ : Fintype F` to `hFfin.fintype`. Set `e : Fin (Fintype.card F) ≃ F` to `(Fintype.equivFin F).symm`. Establish `hbr : ∀ b : Fin (Fintype.card F), ∃ γ : VarBranch J (d + 1) q, ∃ ord : ℕ, (∃ U ∈ 𝓝 (e b : Fin n ⊕ Fin M.m → ℂ), ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U, IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' ∈ γ.image) ∧ (∀ x ∈ γ.image, x ∈ N₀ ∧ ∃ w' ∈ …`.

Introduce `b`. Establish `hb` using `(hmemF _).1 (e b).2`. Take `⟨r, φ, k, hr, hφd, hφi, hφ0, hφZ, hφU, hvan, hinjD⟩` from `hchart (e b) hb.1 hb.2`. Take `⟨γ, h⟩` from `GoodPointBranch.exists_branch M hqu hV hqV hg hAg hS hN₀ hdbl hb.2 hr hφd hφi hφ0 hφZ hφU hvan hinjD ((hGo _).2.mem_nhds (hGo _).1)`. Conclude with `⟨γ, k, h⟩`.

Use `choose γ ord hcovw himg hslice hvan hbij using hbr`. Use `⟨Fintype.card F, γ, ord, LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)), ?_, ?_, ?_, hvan, hbij⟩` and prove the remaining obligations. Use `choose U hU hUc using hcovw`. Take `⟨N, hN, hNU⟩` from `NormalModelFibre.eventually_mem_of_fibre_subset M (q := q) (isOpen_iUnion fun b => isOpen_interior (s := U b)) (fun w hw hwq => by`. Take `⟨b, hb⟩` from `e.surjective ⟨w, (hmemF w).2 ⟨hw, hwq⟩⟩`.

Use `mem_iUnion.2 ⟨b, mem_interior_iff_mem_nhds.2 ?_⟩` and prove the remaining obligations. Establish `hbw : (e b : Fin n ⊕ Fin M.m → ℂ) = w` using `congrArg Subtype.val hb`. Rewrite using `[← hbw]`. Conclude with `hU b)`. Use `⟨N, hN, fun x hx => ?_⟩` and prove the remaining obligations.

Take `⟨w, hw, rfl⟩` from `NormalModelFibre.exists_mem_fibre M hx.1`. Take `⟨b, hb⟩` from `mem_iUnion.1 (hNU w hw hx.2)`. Conclude with `mem_iUnion.2 ⟨b, hUc b w ⟨hw, interior_subset hb⟩⟩`. Use `choose N' hN' hN'c using hslice`. Conclude with `⟨⋂ b, N' b, Filter.iInter_mem.2 hN', fun x hx hxu b => hN'c b x ⟨hx.1, mem_iInter.1 hx.2 b⟩ hxu⟩`.

Introduce `b b' hbb' x hx`. Take `⟨hxN, w, ⟨hw, hwG⟩, rfl⟩` from `himg b x hx.1`. Take `⟨-, w', ⟨hw', hw'G⟩, hww'⟩` from `himg b' _ hx.2`. Establish `hne : w ≠ w'`. Introduce and unpack `rfl`.

Establish `hdisj : Disjoint (G (e b)) (G (e b'))` using `hGd (e b).2 (e b').2 (fun h => hbb' (e.injective (Subtype.ext h)))`. Conclude with `Set.disjoint_left.1 hdisj hwG hw'G`. Conclude with `hdbl w hw w' hw' hww'.symm hxN hne`.
-/
theorem DivisorGoodPointBranches.proof : DivisorGoodPointBranches.Statement := by
  intro n d J u M q _hJ _hdim _hu hqJ hqu hreg hchart hdouble
  obtain ⟨A, O, V, g, -, hV, hqV, hg, hAg, hS⟩ := hreg
  obtain ⟨N₀, hN₀, hdbl⟩ := hdouble
  let F : Set (Fin n ⊕ Fin M.m → ℂ) :=
    {w | w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q}
  have hmemF : ∀ w, w ∈ F ↔ (w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∧ IndefiniteRowSideFullHecke.ComplexSets.firstCoords w = q) :=
    fun w => Iff.rfl
  have hFfin : F.Finite := NormalModelFibre.fibre_finite M q
  obtain ⟨G, hGo, hGd⟩ := hFfin.t2_separation
  let _ : Fintype F := hFfin.fintype
  let e : Fin (Fintype.card F) ≃ F := (Fintype.equivFin F).symm
  have hbr : ∀ b : Fin (Fintype.card F), ∃ γ : VarBranch J (d + 1) q, ∃ ord : ℕ,
      (∃ U ∈ 𝓝 (e b : Fin n ⊕ Fin M.m → ℂ), ∀ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ U,
        IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' ∈ γ.image) ∧
      (∀ x ∈ γ.image, x ∈ N₀ ∧
        ∃ w' ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal ∩ G (e b), IndefiniteRowSideFullHecke.ComplexSets.firstCoords w' = x) ∧
      (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ γ.slice) ∧
      VanishesToOrder (fun t => linEval u (γ.toFun t)) γ.radius ord ∧
      Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0)
        (LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)) *ᵥ γ.toFun τ)) (0 : Fin (d + 1) → ℂ)) := by
    intro b
    have hb := (hmemF _).1 (e b).2
    obtain ⟨r, φ, k, hr, hφd, hφi, hφ0, hφZ, hφU, hvan, hinjD⟩ := hchart (e b) hb.1 hb.2
    obtain ⟨γ, h⟩ := GoodPointBranch.exists_branch M hqu hV hqV hg hAg hS hN₀ hdbl hb.2 hr hφd hφi hφ0
      hφZ hφU hvan hinjD ((hGo _).2.mem_nhds (hGo _).1)
    exact ⟨γ, k, h⟩
  choose γ ord hcovw himg hslice hvan hbij using hbr
  refine ⟨Fintype.card F, γ, ord, LinearMap.toMatrix' (A : (Fin n → ℂ) →ₗ[ℂ] (Fin d → ℂ)),
    ?_, ?_, ?_, hvan, hbij⟩
  · choose U hU hUc using hcovw
    obtain ⟨N, hN, hNU⟩ := NormalModelFibre.eventually_mem_of_fibre_subset M (q := q)
      (isOpen_iUnion fun b => isOpen_interior (s := U b)) (fun w hw hwq => by
        obtain ⟨b, hb⟩ := e.surjective ⟨w, (hmemF w).2 ⟨hw, hwq⟩⟩
        refine mem_iUnion.2 ⟨b, mem_interior_iff_mem_nhds.2 ?_⟩
        have hbw : (e b : Fin n ⊕ Fin M.m → ℂ) = w := congrArg Subtype.val hb
        rw [← hbw]
        exact hU b)
    refine ⟨N, hN, fun x hx => ?_⟩
    obtain ⟨w, hw, rfl⟩ := NormalModelFibre.exists_mem_fibre M hx.1
    obtain ⟨b, hb⟩ := mem_iUnion.1 (hNU w hw hx.2)
    exact mem_iUnion.2 ⟨b, hUc b w ⟨hw, interior_subset hb⟩⟩
  · choose N' hN' hN'c using hslice
    exact ⟨⋂ b, N' b, Filter.iInter_mem.2 hN',
      fun x hx hxu b => hN'c b x ⟨hx.1, mem_iInter.1 hx.2 b⟩ hxu⟩
  · intro b b' hbb' x hx
    obtain ⟨hxN, w, ⟨hw, hwG⟩, rfl⟩ := himg b x hx.1
    obtain ⟨-, w', ⟨hw', hw'G⟩, hww'⟩ := himg b' _ hx.2
    have hne : w ≠ w' := by
      rintro rfl
      have hdisj : Disjoint (G (e b)) (G (e b')) :=
        hGd (e b).2 (e b').2 (fun h => hbb' (e.injective (Subtype.ext h)))
      exact Set.disjoint_left.1 hdisj hwG hw'G
    exact hdbl w hw w' hw' hww'.symm hxN hne

end

end GroundTheory.Heights₂.Heights
