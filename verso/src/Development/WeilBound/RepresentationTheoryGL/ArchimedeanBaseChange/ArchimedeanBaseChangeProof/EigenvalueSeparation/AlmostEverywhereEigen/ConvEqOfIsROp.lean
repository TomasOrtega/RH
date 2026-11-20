import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OrthogonalKeepingHolds

noncomputable section

open NumberField Matrix MeasureTheory
open GlobalTheory.CuspRep PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.E2

/- English proof (translation)
Take `⟨N, hN, hN1⟩` from `exists_compact_mem_nhds (1 : X.G)`. Establish `hK : IsCompact (N⁻¹ * (tsupport φ * N))` using `hN.inv.mul (IsCompact.mul hφ.2 hN)`. Take `⟨C, hC0, hC⟩` from `kerClose X _ x y hK`. Take `⟨W, hW, h⟩` from `approxU X φ (ε / (C + 1)) hφ (by positivity)`. Use `⟨W ∩ N, Filter.inter_mem hW hN1, fun ψ hψ hs => (hC _ φ _ ?_ ?_ fun z => (h ψ hψ (hs.trans Set.inter_subset_left) z).2).trans ?_⟩` and prove the remaining obligations.

Establish `a1` using `cvTest X φ ψ hφ hψ.1`. Establish `hsN` using `hs.trans Set.inter_subset_right`. Use `(cvTest X _ _ (kerBasic X ψ hψ.1).2.2.2.1 a1.1).2.1.trans (Set.mul_subset_mul ?_ ?_)` and prove the remaining obligations. Use `closure_minimal (fun z hz => Set.mem_inv.2 (hsN (subset_tsupport _ fun e => hz ?_))) hN.inv.isClosed` and prove the remaining obligations. Simplify using `[adj, e]`.

Conclude with `closure_minimal (a1.2.1.trans (Set.mul_subset_mul_left hsN)) (IsCompact.mul hφ.2 hN).isClosed`. Introduce `z hz`. Establish `h1` using `mem_of_mem_nhds hN1`. Conclude with `⟨1, by simpa using h1, z, ⟨z, subset_tsupport _ hz, 1, h1, mul_one z⟩, one_mul z⟩`. Rewrite using `[mul_div_assoc', div_le_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem ker_approx (X : Ctx) (φ : X.G → ℂ) (hφ : Tst φ) (x y : X.G) (ε : ℝ) (hε : 0 < ε) : ∃ W ∈ nhds (1 : X.G), ∀ ψ,
    IsBump X ψ → tsupport ψ ⊆ W → ‖ker X.Γ (cv X.μ (adj ψ) (cv X.μ φ ψ)) x y - ker X.Γ φ x y‖ ≤ ε := by
  obtain ⟨N, hN, hN1⟩ := exists_compact_mem_nhds (1 : X.G)
  have hK : IsCompact (N⁻¹ * (tsupport φ * N)) := hN.inv.mul (IsCompact.mul hφ.2 hN)
  obtain ⟨C, hC0, hC⟩ := kerClose X _ x y hK
  obtain ⟨W, hW, h⟩ := approxU X φ (ε / (C + 1)) hφ (by positivity)
  refine ⟨W ∩ N, Filter.inter_mem hW hN1, fun ψ hψ hs => (hC _ φ _ ?_ ?_ fun z =>
    (h ψ hψ (hs.trans Set.inter_subset_left) z).2).trans ?_⟩
  · have a1 := cvTest X φ ψ hφ hψ.1
    have hsN := hs.trans Set.inter_subset_right
    refine (cvTest X _ _ (kerBasic X ψ hψ.1).2.2.2.1 a1.1).2.1.trans (Set.mul_subset_mul ?_ ?_)
    · refine closure_minimal (fun z hz => Set.mem_inv.2 (hsN (subset_tsupport _ fun e => hz ?_))) hN.inv.isClosed
      simp [adj, e]
    · exact closure_minimal (a1.2.1.trans (Set.mul_subset_mul_left hsN)) (IsCompact.mul hφ.2 hN).isClosed
  · intro z hz
    have h1 := mem_of_mem_nhds hN1
    exact ⟨1, by simpa using h1, z, ⟨z, subset_tsupport _ hz, 1, h1, mul_one z⟩, one_mul z⟩
  · rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith

/- English proof (translation)
Use `eq_of_forall_dist_le fun ε hε => ?_` and prove the remaining obligations. Take `⟨W, hW, a⟩` from `ker_approx X _ (h i j) x y _ (half_pos hε)`. Take `⟨W', hW', a'⟩` from `ker_approx X _ (h' i j) x y _ (half_pos hε)`. Take `⟨ψ, hψ, hs⟩` from `bumpEx X _ (Filter.inter_mem hW hW')`. Take `⟨c1, c2⟩` from `colOp X ι ψ hψ.1`.

Take `⟨u, hu⟩` from `c1 y j`. Take `⟨v, hv⟩` from `c1 x i`. Establish `e` using `((c2 Φ T h hT y j u hu).2 x i v hv).symm.trans ((c2 Φ' T h' hT' y j u hu).2 x i v hv)`. Establish `b` using `a ψ hψ (hs.trans Set.inter_subset_left)`. Establish `b'` using `a' ψ hψ (hs.trans Set.inter_subset_right)`.

Rewrite `b` using `[e, ← dist_eq_norm]`. Rewrite `b'` using `[← dist_eq_norm]`. Combine the linear relations using `[dist_triangle_left (ker X.Γ (Φ i j) x y) (ker X.Γ (Φ' i j) x y) (ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ' i j) ψ)) x y)]`.
-/
theorem ker_eq_of_isOp (X : Ctx) {ι : Type} [Fintype ι] {Φ Φ' : Matrix ι ι (X.G → ℂ)} {T : X.Hs ι →L[ℂ] X.Hs ι}
    (h : ∀ i j, Tst (Φ i j)) (h' : ∀ i j, Tst (Φ' i j)) (hT : X.IsOp Φ T) (hT' : X.IsOp Φ' T) (i j : ι) (x y : X.G) :
    ker X.Γ (Φ i j) x y = ker X.Γ (Φ' i j) x y := by
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨W, hW, a⟩ := ker_approx X _ (h i j) x y _ (half_pos hε)
  obtain ⟨W', hW', a'⟩ := ker_approx X _ (h' i j) x y _ (half_pos hε)
  obtain ⟨ψ, hψ, hs⟩ := bumpEx X _ (Filter.inter_mem hW hW')
  obtain ⟨c1, c2⟩ := colOp X ι ψ hψ.1
  obtain ⟨u, hu⟩ := c1 y j
  obtain ⟨v, hv⟩ := c1 x i
  have e := ((c2 Φ T h hT y j u hu).2 x i v hv).symm.trans ((c2 Φ' T h' hT' y j u hu).2 x i v hv)
  have b := a ψ hψ (hs.trans Set.inter_subset_left)
  have b' := a' ψ hψ (hs.trans Set.inter_subset_right)
  rw [e, ← dist_eq_norm] at b
  rw [← dist_eq_norm] at b'
  linarith [dist_triangle_left (ker X.Γ (Φ i j) x y) (ker X.Γ (Φ' i j) x y) (ker X.Γ (cv X.μ (adj ψ) (cv X.μ (Φ' i j) ψ)) x y)]

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} [Fintype ι]

/- English proof (translation)
The claim follows from `ker_eq_of_isOp (ctx ratProper_holds D) h h' hT hT' i j x y`.
-/
theorem kerH_eq_of_isROp (D : Dom E a b) {Φ Φ' : Matrix ι ι (H E a b → ℂ)} {T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D}
    (h : IsTestM Φ) (h' : IsTestM Φ') (hT : IsROp D Φ T) (hT' : IsROp D Φ' T) (i j : ι) (x y : H E a b) :
    kerH (Φ i j) x y = kerH (Φ' i j) x y := ker_eq_of_isOp (ctx ratProper_holds D) h h' hT hT' i j x y

/- English proof (translation)
The claim follows from `Finset.sum_congr rfl fun j _ => ((P.unfold kerBasic P.convcont (ctx ratProper_holds D) (Φ i j) (f j) (h i j) (hc j) fun γ hγ z => hl j ⟨γ, hγ⟩ z).1 x).symm`.
-/
theorem conv_eq_ker (D : Dom E a b) {Φ : Matrix ι ι (H E a b → ℂ)} (h : IsTestM Φ) {f : ι → H E a b → ℂ}
    (hc : ∀ i, Continuous (f i)) (hl : LeftInv f) (i : ι) (x : H E a b) :
    conv D.μ Φ f i x = ∑ j, ∫ y, kerH (Φ i j) x y * f j y ∂D.ν :=
  Finset.sum_congr rfl fun j _ => ((P.unfold kerBasic P.convcont (ctx ratProper_holds D) (Φ i j) (f j) (h i j) (hc j)
    fun γ hγ z => hl j ⟨γ, hγ⟩ z).1 x).symm

/- English proof (translation)
Use function extensionality and compare the values at `i x`. Rewrite using `[conv_eq_ker D h hc hl, conv_eq_ker D h' hc hl]`. Simplify using `only [kerH_eq_of_isROp D h h' hT hT']`.
-/
theorem conv_eq_of_isROp (D : Dom E a b) {Φ Φ' : Matrix ι ι (H E a b → ℂ)} {T : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D}
    (h : IsTestM Φ) (h' : IsTestM Φ') (hT : IsROp D Φ T) (hT' : IsROp D Φ' T) {f : ι → H E a b → ℂ}
    (hc : ∀ i, Continuous (f i)) (hl : LeftInv f) : conv D.μ Φ f = conv D.μ Φ' f := by
  funext i x
  rw [conv_eq_ker D h hc hl, conv_eq_ker D h' hc hl]
  simp only [kerH_eq_of_isROp D h h' hT hT']

end PositivityTheory.Rg.BcB.E2

end
