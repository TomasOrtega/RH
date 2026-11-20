import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AutomorphicArithmetic.CyclotomicBounds.SmallFacts
import Formalism.SharpRestriction.GlobalTheoremInputs
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

/- English proof (translation)
Introduce `D L HW X R hD hS h09 h78 hG2 hK hSha`. Introduce `i hTw hg hR π hπ`. Establish `hl : (D.nd.l i).Prime` using `(D.nd.lPrime i).out`. Establish `hR'` using `hR`. Take `⟨h23, hqd, -⟩` from `hR'`.

Establish `hsm : D.nd.l i ∉ D.host.small` using `fun h => h23 (Or.inl h)`. Establish `hl2 : D.nd.l i ≠ 2` using `UpperTheory.Small.ne_two D.host hsm`. Establish `hl3 : D.nd.l i ≠ 3` using `fun h => h23 (Or.inr h)`. Establish `hlq : D.nd.l i ≠ D.host.q` using `fun h => hqd (Or.inl h)`. Establish `hld : D.nd.l i ≠ D.host.d` using `fun h => hqd (Or.inr h)`.

Establish `hg0 : D.nd.l i ≠ D.host.g 0` using `fun h => hg (by simp [TwistedPlaces.gset, h])`. Establish `hg1 : D.nd.l i ≠ D.host.g 1` using `fun h => hg (by simp [TwistedPlaces.gset, h])`. Establish `hZ : π ∈ D.nd.Z i` using `(D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1`. Take `⟨hK1, hK2⟩` from `hK i hTw`. Take `⟨hFin, -⟩` from `hK1 π hπ`.

Establish `hodd : Odd (D.nd.l i)` using `hl.odd_of_ne_two hl2`. Establish `hShaT : ∀ e ∈ Finset.Ioo 0 D.R.t, GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤`. Introduce `e he`. Rewrite `he` using `[Finset.mem_Ioo]`. Conclude with `lt_top_iff_ne_top.2 (@hSha (D.nd.l i) (D.nd.lPrime i) e he.1 he.2)`.

Establish `hIco : Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t`. Use extensionality with `e`. Simplify using `only [Finset.mem_Ico, Finset.mem_Ioo]`. Use linear arithmetic over natural numbers and integers. Establish `hVV : TwistedPlaces.VVr D (D.nd.l i) = ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ)`.

Unfold `TwistedPlaces.VVr`. Simplify using `only [Rows.Data.VV, hIco]`. Establish `hcls : TwistedPlaces.SplitK D (D.nd.l i) ∨ TwistedPlaces.InertK D (D.nd.l i)`. Unfold `TwistedPlaces.SplitK TwistedPlaces.InertK Host.cls primeClass`. Simplify using `only [hsm, hlq, hld, if_false]`.

Apply the tactic sequence `split_ifs <;> simp`. Break down `hcls with hsp | hin` into its components or cases. Take `⟨ep, hdecl, hram, hAdm⟩` from `hS.a78 i hTw hg hR hsp`. Establish `hA` using `hAdm π hπ`. Establish `hL : EmbeddingTypes.hypL i` using `⟨hl.two_le, Or.inl hsp, fun _ => hram, hg0, hg1⟩`.

Establish `hzeta : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1` using `fun v hv => (hA.2.2.2.2.2.1 v (Or.inr hv)).2.2.1 hv`. Take `⟨-, -, hB⟩` from `h78 i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) hA (fun _ _ _ => hG2 i hg π hπ) hL hdecl hZ`. Establish `hT` using `hB hFin hShaT hzeta`. Establish `hpl : (↑((X.dc i).row ∪ (X.dc i).col) : Set _) = placesOver D.host.E (D.nd.l i)`. Use extensionality with `v`.

Rewrite using `[Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe]`. Conclude with `(X.dc i).cover v`. Establish `hsum : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) = ((∑ u ∈ (X.dc i).col, (2 * (N.locDeg D.host.E u : ℚ) * D.R.m + 1) * (X.eS i : ℚ) : ℚ) : ℝ)`. Unfold `TwistedPlaces.sumOver`. Rewrite using `[← hpl, finsum_mem_coe_finset]`.

Rewrite using `[Finset.sum_congr rfl fun w _ => hD.len0S i hsp π w]`. Rewrite using `[← Rat.cast_sum]`. Use `congr 1`. Simplify using `only [lenA]`. Rewrite using `[Finset.sum_ite_mem, Finset.union_inter_cancel_right]`.

Establish `hBB` using `hD.error_bound_split_eq i hsp π`. Establish `hcol : (∑ u ∈ (X.dc i).col, ((X.eS i : ℚ) + (N.locDeg D.host.E u : ℚ) * D.R.m * ((X.eS i : ℚ) + D.nd.vdel i) + 2 * D.nd.vdel i + Br.h0W i u (X.ρ i) π + (N.locDeg D.host.E u : ℚ) * D.R.m * (X.eS i : ℚ) + D.R.r * (X.c0 i u : ℚ))) = (∑ u ∈ (X.dc i).col, (2 * (N.locDeg D.host.E u : ℚ …`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun u _ => by ring`. Unfold `EmbeddingTypes.boundSplit at hT`.

Rewrite `hT` using `[hcol]`. Establish `hT'` using `(Rat.cast_le (K := ℝ)).2 hT`. Rewrite using `[hsum, hBB, hVV]`. Unfold `localErrorBoundPlaces TwistedPlaces.vhE`. Move the coercions through the operations in `at hT' hK2 ⊢`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA` using `hS.a09 i hTw hg hR hin π hπ`. Establish `hT` using `h09 i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) (hS.goodR i) hA hg0 hg1 hZ hFin hShaT`. Establish `hcol` using `hD.col i hin`. Establish `hrow : (↑(X.dc i).row : Set _) = placesOver D.host.E (D.nd.l i)`.

Use extensionality with `v`. Use `(X.dc i).cover v` as an intermediate fact. Rewrite `this` using `[hcol]`. Simplify using `using this`. Establish `hsum : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) = ((∑ w ∈ (X.dc i).row, X.lenRow i w : ℚ) : ℝ)`.

Unfold `TwistedPlaces.sumOver`. Rewrite using `[← hrow, finsum_mem_coe_finset, Rat.cast_sum]`. Conclude with `Finset.sum_congr rfl fun w _ => hD.len0I i hin π w`. Establish `hW : ∑ w ∈ (X.dc i).row ∪ (X.dc i).col, TruncatedSeriesCountingIdentities.lenW i (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) w = ∑ w ∈ (X.dc i).row, X.lenRow i w`. Rewrite using `[hcol, Finset.union_empty]`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `[TruncatedSeriesCountingIdentities.lenW, hcol]`. Rewrite `hT` using `[hW]`. Establish `hT'` using `(Rat.cast_le (K := ℝ)).2 hT`. Rewrite using `[hsum, hD.error_bound_inert_eq i hin π, hVV]`.

Unfold `KillingConditions.localErrorBoundDecomposition TwistedPlaces.vhE`. Move the coercions through the operations in `at hT' hK2 ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem starAD_of_global : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (X : KillingConditions.HubData D) (R : KillingConditions.RowK),
    KillingConditions.DataAD L HW X R → KillingConditions.StepAD L X → TruncatedSeriesCountingIdentities.IntegralityFromMetric D →
    (∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
      (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ep : Bool) (e' : ℕ)
      (c0 : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ), EmbeddingTypes.admitted i r ρ π dc ep e' c0 cB →
      (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.admG2 i r ρ π) →
      EmbeddingTypes.aux₃ i r ρ π dc ep e' c0 cB) →
    (∀ i, D.nd.l i ∉ TwistedPlaces.gset D → ∀ π ∈ D.nd.Zgood i, TruncatedSeriesCountingIdentities.admG2 i (X.r i) (X.ρ i) π) →
    KillingConditions.KillAt X.ρ → TwistedPlaces.ShaFinOdd D →
    KillingConditions.StarAD L X := by
  classical
  intro D L HW X R hD hS h09 h78 hG2 hK hSha
  intro i hTw hg hR π hπ
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hR' := hR
  obtain ⟨h23, hqd, -⟩ := hR'
  have hsm : D.nd.l i ∉ D.host.small := fun h => h23 (Or.inl h)
  have hl2 : D.nd.l i ≠ 2 := UpperTheory.Small.ne_two D.host hsm
  have hl3 : D.nd.l i ≠ 3 := fun h => h23 (Or.inr h)
  have hlq : D.nd.l i ≠ D.host.q := fun h => hqd (Or.inl h)
  have hld : D.nd.l i ≠ D.host.d := fun h => hqd (Or.inr h)
  have hg0 : D.nd.l i ≠ D.host.g 0 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hg1 : D.nd.l i ≠ D.host.g 1 := fun h => hg (by simp [TwistedPlaces.gset, h])
  have hZ : π ∈ D.nd.Z i := (D.Z_tie i π).2 ((D.Zgood_tie i π).1 hπ).1
  obtain ⟨hK1, hK2⟩ := hK i hTw
  obtain ⟨hFin, -⟩ := hK1 π hπ
  have hodd : Odd (D.nd.l i) := hl.odd_of_ne_two hl2
  have hShaT : ∀ e ∈ Finset.Ioo 0 D.R.t, GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤ := by
    intro e he
    rw [Finset.mem_Ioo] at he
    exact lt_top_iff_ne_top.2 (@hSha (D.nd.l i) (D.nd.lPrime i) e he.1 he.2)
  have hIco : Finset.Ico 1 D.R.t = Finset.Ioo 0 D.R.t := by
    ext e; simp only [Finset.mem_Ico, Finset.mem_Ioo]; omega
  have hVV : TwistedPlaces.VVr D (D.nd.l i) = ((∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e : ℚ) : ℝ) := by
    unfold TwistedPlaces.VVr
    simp only [Rows.Data.VV, hIco]
  have hcls : TwistedPlaces.SplitK D (D.nd.l i) ∨ TwistedPlaces.InertK D (D.nd.l i) := by
    unfold TwistedPlaces.SplitK TwistedPlaces.InertK Host.cls primeClass
    simp only [hsm, hlq, hld, if_false]
    split_ifs <;> simp
  rcases hcls with hsp | hin
  ·
    obtain ⟨ep, hdecl, hram, hAdm⟩ := hS.a78 i hTw hg hR hsp
    have hA := hAdm π hπ
    have hL : EmbeddingTypes.hypL i := ⟨hl.two_le, Or.inl hsp, fun _ => hram, hg0, hg1⟩
    have hzeta : ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1 := fun v hv => (hA.2.2.2.2.2.1 v (Or.inr hv)).2.2.1 hv
    obtain ⟨-, -, hB⟩ := h78 i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) hA
      (fun _ _ _ => hG2 i hg π hπ) hL hdecl hZ
    have hT := hB hFin hShaT hzeta
    have hpl : (↑((X.dc i).row ∪ (X.dc i).col) : Set _) = placesOver D.host.E (D.nd.l i) := by
      ext v
      rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe]
      exact (X.dc i).cover v
    have hsum : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) =
        ((∑ u ∈ (X.dc i).col, (2 * (N.locDeg D.host.E u : ℚ) * D.R.m + 1) * (X.eS i : ℚ) : ℚ) : ℝ) := by
      unfold TwistedPlaces.sumOver
      rw [← hpl, finsum_mem_coe_finset]
      rw [Finset.sum_congr rfl fun w _ => hD.len0S i hsp π w]
      rw [← Rat.cast_sum]
      congr 1
      simp only [lenA]
      rw [Finset.sum_ite_mem, Finset.union_inter_cancel_right]
    have hBB := hD.error_bound_split_eq i hsp π
    have hcol : (∑ u ∈ (X.dc i).col,
        ((X.eS i : ℚ) + (N.locDeg D.host.E u : ℚ) * D.R.m * ((X.eS i : ℚ) + D.nd.vdel i) + 2 * D.nd.vdel i +
          Br.h0W i u (X.ρ i) π + (N.locDeg D.host.E u : ℚ) * D.R.m * (X.eS i : ℚ) + D.R.r * (X.c0 i u : ℚ))) =
        (∑ u ∈ (X.dc i).col, (2 * (N.locDeg D.host.E u : ℚ) * D.R.m + 1) * (X.eS i : ℚ)) +
        ∑ u ∈ (X.dc i).col, ((N.locDeg D.host.E u : ℚ) * D.R.m * D.nd.vdel i + 2 * D.nd.vdel i +
          Br.h0W i u (X.ρ i) π + D.R.r * (X.c0 i u : ℚ)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun u _ => by ring
    unfold EmbeddingTypes.boundSplit at hT
    rw [hcol] at hT
    have hT' := (Rat.cast_le (K := ℝ)).2 hT
    rw [hsum, hBB, hVV]
    unfold localErrorBoundPlaces TwistedPlaces.vhE
    push_cast at hT' hK2 ⊢
    linarith
  ·
    have hA := hS.a09 i hTw hg hR hin π hπ
    have hT := h09 i (X.r i) (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) (X.cB i) (hS.goodR i) hA hg0 hg1 hZ hFin hShaT
    have hcol := hD.col i hin
    have hrow : (↑(X.dc i).row : Set _) = placesOver D.host.E (D.nd.l i) := by
      ext v
      have := (X.dc i).cover v
      rw [hcol] at this
      simpa using this
    have hsum : TwistedPlaces.sumOver D (D.nd.l i) (X.len0 i π) = ((∑ w ∈ (X.dc i).row, X.lenRow i w : ℚ) : ℝ) := by
      unfold TwistedPlaces.sumOver
      rw [← hrow, finsum_mem_coe_finset, Rat.cast_sum]
      exact Finset.sum_congr rfl fun w _ => hD.len0I i hin π w
    have hW : ∑ w ∈ (X.dc i).row ∪ (X.dc i).col, TruncatedSeriesCountingIdentities.lenW i (X.ρ i) π (X.dc i) (X.lenRow i) (X.e' i) w =
        ∑ w ∈ (X.dc i).row, X.lenRow i w := by
      rw [hcol, Finset.union_empty]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [TruncatedSeriesCountingIdentities.lenW, hcol]
    rw [hW] at hT
    have hT' := (Rat.cast_le (K := ℝ)).2 hT
    rw [hsum, hD.error_bound_inert_eq i hin π, hVV]
    unfold KillingConditions.localErrorBoundDecomposition TwistedPlaces.vhE
    push_cast at hT' hK2 ⊢
    linarith

end GlobalTheory.NLink
