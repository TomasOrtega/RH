import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PtOver
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.PtPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.CobOfCoord
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.BlockPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.NotOver
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.DiagConst
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.IsDvrCoef
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.NePure
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.AmbZero

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
private theorem span_of_equiv {K K' H n : Type} [CommRing K] [CommRing K'] [Fintype n] [DecidableEq n] (e : K ≃+* K')
    (f : H → Matrix n n K) (f' : H → Matrix n n K') (hf : ∀ g i j, f' g i j = e (f g i j))
    (h : Submodule.span K' (Set.range f') = ⊤) : Submodule.span K (Set.range f) = ⊤ := by
  have key : ∀ x ∈ Submodule.span K' (Set.range f'), x.map e.symm ∈ Submodule.span K (Set.range f) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨g, rfl⟩ := ha
      refine Submodule.subset_span ⟨g, ?_⟩
      ext i j
      simp [hf]
    | zero =>
      have : (0 : Matrix n n K').map e.symm = 0 := by ext i j; simp
      rw [this]; exact zero_mem _
    | add a b _ _ ha hb =>
      have : (a + b).map e.symm = a.map e.symm + b.map e.symm := by ext i j; simp
      rw [this]; exact add_mem ha hb
    | smul s a _ ha =>
      have : (s • a).map e.symm = e.symm s • a.map e.symm := by ext i j; simp
      rw [this]; exact Submodule.smul_mem _ _ ha
  rw [eq_top_iff]
  intro y _
  have h1 := key (y.map e) (by rw [h]; trivial)
  have h2 : (y.map e).map e.symm = y := by ext i j; simp
  rwa [h2] at h1

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
private theorem charpoly_mapRep {R R' H : Type} [CommRing R] [CommRing R'] [Group H] (f : R →+* R') (r r' : H →* M4 R)
    (h : ∀ g, (r g).charpoly = (r' g).charpoly) (g : H) : (mapRep f r g).charpoly = (mapRep f r' g).charpoly := by
  change ((r g).map f).charpoly = ((r' g).map f).charpoly
  rw [Matrix.charpoly_map, Matrix.charpoly_map, h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Ws.sp4Of :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ ι : PadicAlgCl l ≃+* ℂ, Con D → Pur D ι → Autm D ι → D.Fin0 ∧ D.NoEnd ∧ D.AllIrr (UpperTheory.V.Aut.IsAut4 ι) := by
  intro hP Ω _ _ _ l _ c D hD ι hC hPu hA
  obtain ⟨⟨𝔟, e, he⟩, -⟩ := ambZero l
  refine ⟨?_, ?_, ?_⟩
  · by_contra hF
    obtain ⟨𝔞, r, hch, hr, x, hx, hne⟩ := ptOver hP D hD hF
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔞 r hr
    rcases triV hP D hD 𝔞 r hr with h | h | ⟨h02, h20, h⟩
    · exact hC 𝔞 hch r u hu (Or.inl h)
    · obtain ⟨n, hn, hxn⟩ := diagConst D hD 𝔞 hch r hr u hu h x hx
      exact hne n hn hxn
    · obtain ⟨r₁, u₁, hu₁, hb, hs⟩ := blockPart D hD 𝔞 r hr u hu h02 h20 h
      obtain ⟨r₂, u₂, hu₂, hE, -⟩ := bl hP D hD 𝔞 r₁ u₁ hu₁ hb hs
      exact hC 𝔞 hch r₂ u₂ hu₂ (Or.inr hE)
  · intro r hr hb hs
    obtain ⟨r', hr', rfl⟩ := eptV D hD 𝔟 e he r hr
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔟 r' hr'
    have hb' : ∀ g, IsBlock (r' g) := fun g i j hij =>
      Subtype.ext (e.injective ((hb g i j hij).trans (map_zero e).symm))
    have hs' := span_of_equiv e (fun g => (mapRep 𝔟.toK r' g).submatrix ixA ixA) _ (fun _ _ _ => rfl) hs
    obtain ⟨r₂, u₂, hu₂, hE, hcp⟩ := bl hP D hD 𝔟 r' u hu hb' hs'
    refine nePure D hD ι 𝔟 e he r' u hu hb' ?_
    obtain ⟨H, M, hH, hM, h⟩ := hPu 𝔟 e he r₂ u₂ hu₂ (Or.inr hE)
    have hc := charpoly_mapRep ((e : 𝔟.K →+* PadicAlgCl l).comp 𝔟.toK) r₂ r' hcp
    refine ⟨H, M, hH, hM, fun p hp hpM A hA f σ hf hσ hF => ?_⟩
    rw [← hc]
    exact h p hp hpM A hA f σ hf hσ hF
  · intro r hr hI
    obtain ⟨r', hr', rfl⟩ := eptV D hD 𝔟 e he r hr
    obtain ⟨u, hu⟩ := ptPair hP D hD 𝔟 r' hr'
    exact hA 𝔟 e he r' u hu (span_of_equiv e (mapRep 𝔟.toK r') _ (fun _ _ _ => rfl) hI)
