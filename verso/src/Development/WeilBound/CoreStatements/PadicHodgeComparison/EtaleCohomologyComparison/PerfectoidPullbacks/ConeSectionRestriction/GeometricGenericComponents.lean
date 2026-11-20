import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NoetherNormalizationHomogeneousStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PreimageBasicOpenNonempty
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsHomRelation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsAffineOpenPreimage
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsAlgebraicOfIntegralTorusS
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ExistsCoordBasicOpen

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Use `haveI : IsClosedImmersion i := hci`. Use `haveI hXi : IsIntegral X := isIntegral_of_smooth q (n + 1)`. Use `haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective`. Take `⟨e, m, y, he, hy, halg, hfin⟩` from `GlobalTheory.T.noether_normalization_homogeneous K N (homIdeal i) (homIdeal_ne_top i) (homIdeal_homog i)`. Establish `hcov` using `iSup_preimage_eq_top i he y hy hfin`.

Choose the witnesses or unpack the hypotheses as in `⟨d, rfl⟩ : ∃ d, m = d + 1 := by`. Break down `m with _ | d` into its components or cases. It suffices to derive a contradiction. Take `⟨x⟩` from `(inferInstance : Nonempty X)`. Establish `hx : x ∈ (⊤ : X.Opens)` using `trivial`.

Rewrite `hx` using `[← hcov, iSup_of_empty]`. Simplify using `at hx`. Conclude with `⟨d, rfl⟩`. Establish `hpos : ∀ S : Finset (Fin (d + 1)), S.Nonempty → 0 < S.card * e` using `fun S hS => Nat.mul_pos hS.card_pos he`. Establish `haff : ∀ S : Finset (Fin (d + 1)), S.Nonempty → IsAffineOpen (⨅ k ∈ S, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k))`.

Introduce `S hS`. Rewrite using `[biInf_preimage i y S]`. Conclude with `isAffineOpen_preimage i hci (yS_mem y hy S) (hpos S hS)`. Set `W : X.Opens` to `⨅ k ∈ (Finset.univ : Finset (Fin (d + 1))), i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)`. Establish `hWaff : IsAffineOpen W` using `haff _ Finset.univ_nonempty`.

Establish `hWV : W ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)` using `le_iInf fun k => biInf_le _ (Finset.mem_univ k)`. Establish `hWS : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y Finset.univ)` using `(biInf_preimage i y _).le`. Establish `hWne : (W : Set X).Nonempty`. Establish `hne0 : Ideal.Quotient.mk (homIdeal i) (yS y Finset.univ) ≠ 0`. Introduce `h0`.

Establish `h1 : MvPolynomial.aeval (fun k => Ideal.Quotient.mk (homIdeal i) (y k)) (∏ k : Fin (d + 1), (MvPolynomial.X k : MvPolynomial (Fin (d + 1)) K)) = 0`. Rewrite using `[map_prod]`. Simplify `h0` using `[yS, map_prod]`. Establish `h2` using `halg (h1.trans (map_zero _).symm)`. Conclude with `Finset.prod_ne_zero_iff.2 (fun k _ => MvPolynomial.X_ne_zero k) h2`.

Use `preimage_basicOpen_nonempty i (hpos _ Finset.univ_nonempty) (yS_mem y hy Finset.univ) hne0` as an intermediate fact. Rewrite `this` using `[← biInf_preimage i y Finset.univ]`. Then use the resulting hypothesis. Use `letI algW : Algebra K Γ(X, W) := (strV q W).toAlgebra`. Establish `htW : ∀ k, IsUnit (tV i y hy W hWV k)` using `tV_isUnit i y hy hWV`. Establish `hindW : AlgebraicIndependent K (tV i y hy W hWV)` using `algebraicIndependent_tV i y hy hWV he q hiq halg hWne`.

Use `haveI : Nonempty W := hWne.to_subtype`. Establish `hintW : ∀ r : Γ(X, W), IsIntegral (torusS K (fun k => (htW k).unit) Finset.univ) r`. Introduce `r`. Establish `hr : r ∈ Set.range (resO (le_refl W))` using `⟨r, by simp [resO]⟩`. Rewrite `hr` using `[range_resO_eq i hci (yS_mem y hy _) (hpos _ Finset.univ_nonempty) (biInf_preimage i y _) le_rfl hWS]`.

Take `⟨a, rfl⟩` from `hr`. Conclude with `isIntegral_torusS i y hy hWV he q hiq hfin Finset.univ hWS htW a`. Establish `halgW : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (tV i y hy W hWV))) Γ(X, W)` using `isAlgebraic_of_integral_torusS (fun k => (htW k).unit) hintW`. Use `haveI hlft : LocallyOfFiniteType q := by first`. Consider the case `infer_instance`.

Consider the case `(haveI : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q; infer_instance)`. Consider the case `(haveI : Smooth q := inferInstance; haveI : LocallyOfFinitePresentation q := inferInstance; infer_instance)`. Use `haveI : Algebra.FiniteType K Γ(X, W) := finiteType_affine q hWaff`. Take `⟨g, hg0, het⟩` from `exists_etale_away (tV i y hy W hWV) hindW halgW`. Take `⟨c, hc⟩` from `exists_coord_basicOpen q hWaff g (tV i y hy W hWV) het`.

Establish `hVne : ((X.basicOpen g : X.Opens) : Set X).Nonempty`. Rewrite using `[← TopologicalSpace.Opens.ne_bot_iff_nonempty]`. Introduce `h`. Conclude with `hg0 ((basicOpen_eq_bot_iff g).1 h)`. Establish `hdn : d = n + 1` using `coord_card_eq q (n + 1) hVne c`.

Substitute `hdn` using the available equality. Use `⟨e, he, y, hy, ?_⟩` and prove the remaining obligations. Introduce `U`. Establish `hV : X.basicOpen g ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)` using `(X.basicOpen_le g).trans hWV`. Establish `hct : ∀ k, c.t k = tV i y hy (X.basicOpen g) hV k`.

Introduce `k`. Rewrite using `[hc k]`. Simplify using `only [tV, resO]`. Rewrite using `[← CommRingCat.comp_apply, Scheme.Hom.appLE_map]`. Set `c' : Coord q (X.basicOpen g) (n + 1)` to `⟨c.affine, tV i y hy (X.basicOpen g) hV, by`.

Establish `h` using `c.etale`. Rewrite using `[show c.t = tV i y hy (X.basicOpen g) hV from funext hct] at h⟩` and apply the resulting hypothesis. Use `⟨hcov, fun S hS => haff S hS, X.basicOpen g, hV, c', ?_⟩` and prove the remaining obligations. Use `letI algV : Algebra K Γ(X, X.basicOpen g) := (strV q _).toAlgebra`. Use `haveI : Nonempty (X.basicOpen g) := hVne.to_subtype`.

Use `⟨inferInstance, fun k => rfl, tV_isUnit i y hy hV, algebraicIndependent_tV i y hy hV he q hiq halg hVne, ?_⟩` and prove the remaining obligations. Set `B : Finset (Fin (n + 2)) → Subalgebra K Γ(X, X.basicOpen g)` to `fun S => { (resO (le_biInf_of_le hV S)).range with algebraMap_mem' := fun a => RingHom.mem_range.2 ⟨strV q _ a, (RingHom.congr_fun (strV_res q (le_biInf_of_le hV S)) a).symm⟩ }`. Establish `memB : ∀ S x, x ∈ B S ↔ x ∈ Set.range (resO (le_biInf_of_le hV S))` using `fun S x => RingHom.mem_range`. Use `⟨B, fun S _ => Set.ext fun x => memB S x, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `S _`.

Conclude with `map_injective_of_isIntegral X (homOfLE (le_biInf_of_le hV S))`. Introduce `S hS`. Establish `hS' : X.basicOpen g ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)` using `(le_biInf_of_le hV S).trans (biInf_preimage i y S).le`. Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨m, hm, rfl⟩`.

Establish `h1` using `tpow_mem_range i y hy hV he S hS' (tV_isUnit i y hy hV) m hm`. Rewrite `h1` using `[← range_resO_eq i hci (yS_mem y hy S) (hpos S hS) (biInf_preimage i y S) (le_biInf_of_le hV S) hS']`. Conclude with `(memB S _).2 h1`. Introduce `S hS`. Use `letI : Algebra K Γ(X, ⨅ k ∈ S, U k) := (strV q _).toAlgebra`.

Use `haveI : Algebra.FiniteType K Γ(X, ⨅ k ∈ S, U k) := finiteType_affine q (haff S hS)`. Set `φ : Γ(X, ⨅ k ∈ S, U k) →ₐ[K] Γ(X, X.basicOpen g)` to `{ resO (le_biInf_of_le hV S) with commutes' := fun a => (RingHom.congr_fun (strV_res q (le_biInf_of_le hV S)) a).symm }`. Establish `hB : B S = φ.range`. Use extensionality with `x`. Rewrite using `[memB, AlgHom.mem_range]`.

Both sides reduce to the same expression. Rewrite using `[hB, ← Algebra.map_top]`. Conclude with `Algebra.FiniteType.out.map φ`. Introduce `S hS b hb`. Establish `hS' : X.basicOpen g ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S)` using `(le_biInf_of_le hV S).trans (biInf_preimage i y S).le`.

Rewrite `hb` using `[memB, range_resO_eq i hci (yS_mem y hy S) (hpos S hS) (biInf_preimage i y S) (le_biInf_of_le hV S) hS']`. Take `⟨a, rfl⟩` from `hb`. Conclude with `isIntegral_torusS i y hy hV he q hiq hfin S hS' (tV_isUnit i y hy hV) a`. Introduce `j x hx`. Rewrite `hx`, the goal using `[memB]`.

Take `⟨a, rfl⟩` from `hx`. Establish `hle : (⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), U k) ≤ ⨅ k ∈ Finset.univ.erase j, U k` using `biInf_mono fun k _ => Finset.mem_univ k`. Use `⟨resO hle a, ?_⟩` and prove the remaining obligations. Simplify using `only [resO]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`.

Both sides reduce to the same expression. Introduce `r`. Take `⟨b, hb, b', hb', hne, h⟩` from `exists_frac_basicOpen hWaff g hVne r`. Conclude with `⟨b, (memB _ _).2 hb, b', (memB _ _).2 hb', hne, h⟩`.
-/
theorem geo_setup {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (n : ℕ) [SmoothOfRelativeDimension (n + 1) q] (N : ℕ) (i : X ⟶ PSpace K N)
    (hci : IsClosedImmersion i) (hiq : i ≫ PSpace.str K N = q) :
    ∃ (e : ℕ) (_ : 0 < e) (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e),
      let U : Fin (n + 2) → X.Opens := fun k => i ⁻¹ᵁ Proj.basicOpen _ (y k)
      (⨆ k, U k) = ⊤ ∧
      (∀ S : Finset (Fin (n + 2)), S.Nonempty → IsAffineOpen (⨅ k ∈ S, U k)) ∧
      ∃ (V : X.Opens) (hV : V ≤ ⨅ k, U k) (c : Coord q V (n + 1)),
        letI := (strV q V).toAlgebra
        IsDomain Γ(X, V) ∧
        (∀ k, c.t k = (i.appLE _ V (hV.trans (iInf_le U 0))).hom (yRatio y hy k)) ∧
        ∃ ht : ∀ k, IsUnit (c.t k),
          AlgebraicIndependent K c.t ∧
          ∃ B : Finset (Fin (n + 2)) → Subalgebra K Γ(X, V),
            (∀ S, S.Nonempty → (B S : Set Γ(X, V)) = Set.range (resO (le_biInf_of_le hV S))) ∧
            (∀ S, S.Nonempty → Function.Injective (resO (le_biInf_of_le hV S))) ∧
            (∀ S, S.Nonempty → torusS K (fun k => (ht k).unit) S ≤ B S) ∧
            (∀ S, S.Nonempty → (B S).FG) ∧
            (∀ S, S.Nonempty → ∀ b ∈ B S, IsIntegral (torusS K (fun k => (ht k).unit) S) b) ∧
            (∀ j, B (Finset.univ.erase j) ≤ B Finset.univ) ∧
            (∀ r : Γ(X, V), ∃ b ∈ B Finset.univ, ∃ b' ∈ B Finset.univ, b' ≠ 0 ∧ r * b' = b) := by
  classical
  haveI : IsClosedImmersion i := hci
  haveI hXi : IsIntegral X := isIntegral_of_smooth q (n + 1)
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  obtain ⟨e, m, y, he, hy, halg, hfin⟩ :=
    GlobalTheory.T.noether_normalization_homogeneous K N (homIdeal i) (homIdeal_ne_top i) (homIdeal_homog i)
  have hcov := iSup_preimage_eq_top i he y hy hfin
  obtain ⟨d, rfl⟩ : ∃ d, m = d + 1 := by
    rcases m with _ | d
    · exfalso
      obtain ⟨x⟩ := (inferInstance : Nonempty X)
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← hcov, iSup_of_empty] at hx
      simp at hx
    · exact ⟨d, rfl⟩
  have hpos : ∀ S : Finset (Fin (d + 1)), S.Nonempty → 0 < S.card * e := fun S hS => Nat.mul_pos hS.card_pos he
  have haff : ∀ S : Finset (Fin (d + 1)), S.Nonempty →
      IsAffineOpen (⨅ k ∈ S, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)) := by
    intro S hS
    rw [biInf_preimage i y S]
    exact isAffineOpen_preimage i hci (yS_mem y hy S) (hpos S hS)
  let W : X.Opens := ⨅ k ∈ (Finset.univ : Finset (Fin (d + 1))), i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k)
  have hWaff : IsAffineOpen W := haff _ Finset.univ_nonempty
  have hWV : W ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) := le_iInf fun k => biInf_le _ (Finset.mem_univ k)
  have hWS : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y Finset.univ) := (biInf_preimage i y _).le
  have hWne : (W : Set X).Nonempty := by
    have hne0 : Ideal.Quotient.mk (homIdeal i) (yS y Finset.univ) ≠ 0 := by
      intro h0
      have h1 : MvPolynomial.aeval (fun k => Ideal.Quotient.mk (homIdeal i) (y k))
          (∏ k : Fin (d + 1), (MvPolynomial.X k : MvPolynomial (Fin (d + 1)) K)) = 0 := by
        rw [map_prod]
        simpa [yS, map_prod] using h0
      have h2 := halg (h1.trans (map_zero _).symm)
      exact Finset.prod_ne_zero_iff.2 (fun k _ => MvPolynomial.X_ne_zero k) h2
    have := preimage_basicOpen_nonempty i (hpos _ Finset.univ_nonempty) (yS_mem y hy Finset.univ) hne0
    rwa [← biInf_preimage i y Finset.univ] at this
  letI algW : Algebra K Γ(X, W) := (strV q W).toAlgebra
  have htW : ∀ k, IsUnit (tV i y hy W hWV k) := tV_isUnit i y hy hWV
  have hindW : AlgebraicIndependent K (tV i y hy W hWV) :=
    algebraicIndependent_tV i y hy hWV he q hiq halg hWne
  haveI : Nonempty W := hWne.to_subtype
  have hintW : ∀ r : Γ(X, W), IsIntegral (torusS K (fun k => (htW k).unit) Finset.univ) r := by
    intro r
    have hr : r ∈ Set.range (resO (le_refl W)) := ⟨r, by simp [resO]⟩
    rw [range_resO_eq i hci (yS_mem y hy _) (hpos _ Finset.univ_nonempty) (biInf_preimage i y _) le_rfl hWS] at hr
    obtain ⟨a, rfl⟩ := hr
    exact isIntegral_torusS i y hy hWV he q hiq hfin Finset.univ hWS htW a
  have halgW : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (tV i y hy W hWV))) Γ(X, W) :=
    isAlgebraic_of_integral_torusS (fun k => (htW k).unit) hintW
  haveI hlft : LocallyOfFiniteType q := by
    first
      | infer_instance
      | (haveI : Smooth q := SmoothOfRelativeDimension.smooth (n + 1) q; infer_instance)
      | (haveI : Smooth q := inferInstance; haveI : LocallyOfFinitePresentation q := inferInstance; infer_instance)
  haveI : Algebra.FiniteType K Γ(X, W) := finiteType_affine q hWaff
  obtain ⟨g, hg0, het⟩ := exists_etale_away (tV i y hy W hWV) hindW halgW
  obtain ⟨c, hc⟩ := exists_coord_basicOpen q hWaff g (tV i y hy W hWV) het
  have hVne : ((X.basicOpen g : X.Opens) : Set X).Nonempty := by
    rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty]
    intro h
    exact hg0 ((basicOpen_eq_bot_iff g).1 h)
  have hdn : d = n + 1 := coord_card_eq q (n + 1) hVne c
  subst hdn
  refine ⟨e, he, y, hy, ?_⟩
  intro U
  have hV : X.basicOpen g ≤ ⨅ k, i ⁻¹ᵁ Proj.basicOpen (grK K N) (y k) := (X.basicOpen_le g).trans hWV
  have hct : ∀ k, c.t k = tV i y hy (X.basicOpen g) hV k := by
    intro k
    rw [hc k]
    simp only [tV, resO]
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  let c' : Coord q (X.basicOpen g) (n + 1) :=
    ⟨c.affine, tV i y hy (X.basicOpen g) hV, by
      have h := c.etale
      rwa [show c.t = tV i y hy (X.basicOpen g) hV from funext hct] at h⟩
  refine ⟨hcov, fun S hS => haff S hS, X.basicOpen g, hV, c', ?_⟩
  letI algV : Algebra K Γ(X, X.basicOpen g) := (strV q _).toAlgebra
  haveI : Nonempty (X.basicOpen g) := hVne.to_subtype
  refine ⟨inferInstance, fun k => rfl, tV_isUnit i y hy hV, algebraicIndependent_tV i y hy hV he q hiq halg hVne, ?_⟩
  let B : Finset (Fin (n + 2)) → Subalgebra K Γ(X, X.basicOpen g) := fun S =>
    { (resO (le_biInf_of_le hV S)).range with
      algebraMap_mem' := fun a => RingHom.mem_range.2 ⟨strV q _ a,
        (RingHom.congr_fun (strV_res q (le_biInf_of_le hV S)) a).symm⟩ }
  have memB : ∀ S x, x ∈ B S ↔ x ∈ Set.range (resO (le_biInf_of_le hV S)) := fun S x => RingHom.mem_range
  refine ⟨B, fun S _ => Set.ext fun x => memB S x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S _
    exact map_injective_of_isIntegral X (homOfLE (le_biInf_of_le hV S))
  · intro S hS
    have hS' : X.basicOpen g ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S) :=
      (le_biInf_of_le hV S).trans (biInf_preimage i y S).le
    refine Algebra.adjoin_le ?_
    rintro _ ⟨m, hm, rfl⟩
    have h1 := tpow_mem_range i y hy hV he S hS' (tV_isUnit i y hy hV) m hm
    rw [← range_resO_eq i hci (yS_mem y hy S) (hpos S hS) (biInf_preimage i y S) (le_biInf_of_le hV S) hS'] at h1
    exact (memB S _).2 h1
  · intro S hS
    letI : Algebra K Γ(X, ⨅ k ∈ S, U k) := (strV q _).toAlgebra
    haveI : Algebra.FiniteType K Γ(X, ⨅ k ∈ S, U k) := finiteType_affine q (haff S hS)
    let φ : Γ(X, ⨅ k ∈ S, U k) →ₐ[K] Γ(X, X.basicOpen g) :=
      { resO (le_biInf_of_le hV S) with
        commutes' := fun a => (RingHom.congr_fun (strV_res q (le_biInf_of_le hV S)) a).symm }
    have hB : B S = φ.range := by
      ext x
      rw [memB, AlgHom.mem_range]
      rfl
    rw [hB, ← Algebra.map_top]
    exact Algebra.FiniteType.out.map φ
  · intro S hS b hb
    have hS' : X.basicOpen g ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (yS y S) :=
      (le_biInf_of_le hV S).trans (biInf_preimage i y S).le
    rw [memB, range_resO_eq i hci (yS_mem y hy S) (hpos S hS) (biInf_preimage i y S) (le_biInf_of_le hV S) hS'] at hb
    obtain ⟨a, rfl⟩ := hb
    exact isIntegral_torusS i y hy hV he q hiq hfin S hS' (tV_isUnit i y hy hV) a
  · intro j x hx
    rw [memB] at hx ⊢
    obtain ⟨a, rfl⟩ := hx
    have hle : (⨅ k ∈ (Finset.univ : Finset (Fin (n + 2))), U k) ≤ ⨅ k ∈ Finset.univ.erase j, U k :=
      biInf_mono fun k _ => Finset.mem_univ k
    refine ⟨resO hle a, ?_⟩
    simp only [resO]
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  · intro r
    obtain ⟨b, hb, b', hb', hne, h⟩ := exists_frac_basicOpen hWaff g hVne r
    exact ⟨b, (memB _ _).2 hb, b', (memB _ _).2 hb', hne, h⟩

end CrystallineSemistableComparison.Pb
