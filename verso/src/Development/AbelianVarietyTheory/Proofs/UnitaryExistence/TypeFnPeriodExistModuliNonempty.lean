import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureHermitianModelOfDatumStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag

open NumberField Matrix
open scoped nonZeroDivisors ComplexConjugate
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodExists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [IsCMField E] in

/- English proof (translation)
Establish `h1 : Ψ.card = Ψᶜ.card`. Use `Finset.card_nbij' (fun σ => ComplexEmbedding.conjugate σ) (fun σ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `σ hσ`. Simplify using `using (h σ).mp hσ`. Introduce `σ hσ`.

Use `h (ComplexEmbedding.conjugate σ)` as an intermediate fact. Rewrite `this` using `[ComplexEmbedding.involutive_conjugate E σ]`. Conclude with `this.mpr (by simpa using hσ)`. Introduce `σ _`. Conclude with `ComplexEmbedding.involutive_conjugate E σ`.

Introduce `σ _`. Conclude with `ComplexEmbedding.involutive_conjugate E σ`. Establish `h2` using `Finset.card_add_card_compl Ψ`. Rewrite `h2` using `[NumberField.Embeddings.card E ℂ]`. Use linear arithmetic over natural numbers and integers.
-/
lemma card_cmType (Ψ : Finset (E →+* ℂ))
    (h : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) :
    Ψ.card = Module.finrank ℚ E / 2 := by
  classical
  have h1 : Ψ.card = Ψᶜ.card := by
    refine Finset.card_nbij' (fun σ => ComplexEmbedding.conjugate σ)
      (fun σ => ComplexEmbedding.conjugate σ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simpa using (h σ).mp hσ
    · intro σ hσ
      have := h (ComplexEmbedding.conjugate σ)
      rw [ComplexEmbedding.involutive_conjugate E σ] at this
      exact this.mpr (by simpa using hσ)
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
    · intro σ _; exact ComplexEmbedding.involutive_conjugate E σ
  have h2 := Finset.card_add_card_compl Ψ
  rw [NumberField.Embeddings.card E ℂ] at h2
  omega

/- English proof (translation)
Establish `hc : ∀ τ, Nonempty ({i // ty i = τ} ≃ {i // ty' i = τ})`. Introduce `τ`. Rewrite using `[← Finite.card_eq]`. Distinguish the cases in `hτ : τ (H.rt : E) = H.rt0`. Rewrite using `[(h τ).1 hτ, (h' τ).1 hτ]`.

Rewrite using `[(h τ).2 hτ, (h' τ).2 hτ]`. Conclude with `⟨Equiv.ofFiberEquiv fun τ => (hc τ).some, Equiv.ofFiberEquiv_map _⟩`.
-/
lemma exists_equiv_of_isTypeFn {H : Host E} {p q g g' : ℕ} {ty : Fin g → (E →+* ℂ)}
    {ty' : Fin g' → (E →+* ℂ)} (h : IsTypeFn H p q ty) (h' : IsTypeFn H p q ty') :
    ∃ e : Fin g ≃ Fin g', ∀ k, ty' (e k) = ty k := by
  have hc : ∀ τ, Nonempty ({i // ty i = τ} ≃ {i // ty' i = τ}) := by
    intro τ
    rw [← Finite.card_eq]
    by_cases hτ : τ (H.rt : E) = H.rt0
    · rw [(h τ).1 hτ, (h' τ).1 hτ]
    · rw [(h τ).2 hτ, (h' τ).2 hτ]
  exact ⟨Equiv.ofFiberEquiv fun τ => (hc τ).some, Equiv.ofFiberEquiv_map _⟩

/- English proof (translation)
Take `⟨h1, h2, h3, h4, Hm, hH, hpos, hE⟩` from `hP`. Set `L : (Fin g' → ℂ) ≃L[ℝ] (Fin g → ℂ)` to `(LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv`. Establish `hL : ∀ z k, L z k = z (e k)` using `fun _ _ => rfl`. Establish `hF : ∀ z w, hermForm (Hm.submatrix e e) (L z) (L w) = hermForm Hm z w`. Introduce `z w`.

Simplify using `only [hermForm, dotProduct, mulVec, submatrix_apply, Pi.star_apply, hL]`. Rewrite using `[← e.sum_comp]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← e.sum_comp]`. Set `P' : D.La →+ (Fin g → ℂ)` to `L.toLinearEquiv.toLinearMap.toAddMonoidHom.comp P`.

Establish `hP' : ∀ x, P' x = L (P x)` using `fun _ => rfl`. Use `⟨P', ?_, ?_, ?_, ?_, Hm.submatrix e e, hH.submatrix e, ?_, ?_⟩` and prove the remaining obligations. Introduce `a x k`. Rewrite using `[hP', hP', hL, hL, h1, he]`. Introduce `x y hxy`.

Conclude with `h2 (L.injective hxy)`. Set `f : P'.range → P.range` to `fun z => ⟨L.symm z.1, by`. Take `⟨_, x, rfl⟩` from `z`. Conclude with `⟨x, by simp [hP']⟩⟩`. Establish `hf : Continuous f` using `(L.symm.continuous.comp continuous_subtype_val).subtype_mk _`.

Conclude with `DiscreteTopology.of_continuous_injective hf fun z w hzw => Subtype.ext (L.symm.injective (congrArg Subtype.val hzw))`. Establish `: Set.range P' = L.toLinearEquiv.toLinearMap '' Set.range P`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression. Rewrite using `[this, ← Submodule.map_span, h4, Submodule.map_top, LinearEquiv.range]`.

Introduce `z hz`. Take `⟨w, rfl⟩` from `L.surjective z`. Rewrite using `[hF]`. Conclude with `hpos w fun h => hz (by rw [h, map_zero])`. Introduce `x y`.

Rewrite using `[hP', hP', hF, hE]`.
-/
lemma exists_isPeriod_of_equiv {H : Host E} {D : Datum H} {g g' : ℕ} {ty : Fin g → (E →+* ℂ)}
    {ty' : Fin g' → (E →+* ℂ)} (e : Fin g ≃ Fin g') (he : ∀ k, ty' (e k) = ty k)
    {P : D.La →+ (Fin g' → ℂ)} (hP : IsPeriod D ty' P) : ∃ P', IsPeriod D ty P' := by
  obtain ⟨h1, h2, h3, h4, Hm, hH, hpos, hE⟩ := hP
  let L : (Fin g' → ℂ) ≃L[ℝ] (Fin g → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL : ∀ z k, L z k = z (e k) := fun _ _ => rfl
  have hF : ∀ z w, hermForm (Hm.submatrix e e) (L z) (L w) = hermForm Hm z w := by
    intro z w
    simp only [hermForm, dotProduct, mulVec, submatrix_apply, Pi.star_apply, hL]
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← e.sum_comp]
  let P' : D.La →+ (Fin g → ℂ) := L.toLinearEquiv.toLinearMap.toAddMonoidHom.comp P
  have hP' : ∀ x, P' x = L (P x) := fun _ => rfl
  refine ⟨P', ?_, ?_, ?_, ?_, Hm.submatrix e e, hH.submatrix e, ?_, ?_⟩
  · intro a x k
    rw [hP', hP', hL, hL, h1, he]
  · intro x y hxy
    exact h2 (L.injective hxy)
  · let f : P'.range → P.range := fun z => ⟨L.symm z.1, by
      obtain ⟨_, x, rfl⟩ := z
      exact ⟨x, by simp [hP']⟩⟩
    have hf : Continuous f := (L.symm.continuous.comp continuous_subtype_val).subtype_mk _
    exact DiscreteTopology.of_continuous_injective hf fun z w hzw =>
      Subtype.ext (L.symm.injective (congrArg Subtype.val hzw))
  · have : Set.range P' = L.toLinearEquiv.toLinearMap '' Set.range P := by
      rw [← Set.range_comp]; rfl
    rw [this, ← Submodule.map_span, h4, Submodule.map_top, LinearEquiv.range]
  · intro z hz
    obtain ⟨w, rfl⟩ := L.surjective z
    rw [hF]
    exact hpos w fun h => hz (by rw [h, map_zero])
  · intro x y
    rw [hP', hP', hF, hE]

/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `hsq : (H.rt : E) ^ 2 = -(H.d : E)`. Use `congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `him : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.im ≠ 0`.

Introduce `z hz h0`. Use `congrArg Complex.re hz` as an intermediate fact. Simplify using `[sq, h0] at this`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Take `⟨σ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Establish `hσ : (σ (H.rt : E)).im ≠ 0` using `him _ (by rw [← map_pow, hsq]; simp)`. Establish `hne : (H.rt : E) ≠ 0` using `fun h => hσ (by rw [h]; simp)`. Establish `hcc : FD.cc (H.rt : E) = -(H.rt : E)`. Establish `h2 : (FD.cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2`. Unfold `FD.cc`.

Rewrite using `[← map_pow, hsq]`. Simplify using the standard rewrite rules. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h` into its components or cases. It suffices to derive a contradiction. Establish `h3` using `congrArg Complex.im (FD.emb_cc σ (H.rt : E))`.

Rewrite `h3` using `[h, Complex.conj_im]`. Conclude with `hσ (by linarith)`. Conclude with `h`. Break down `lt_or_gt_of_ne (him _ H.sqrt_neg_disc_sq) with h | h` into its components or cases. Use `⟨-(H.rt : E), ?_, neg_ne_zero.2 hne, fun τ hτ => ?_⟩` and prove the remaining obligations.

Unfold `FD.cc at hcc ⊢`. Rewrite using `[map_neg, hcc]`. Rewrite using `[map_neg, hτ, Complex.neg_im]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `⟨_, hcc, hne, fun τ hτ => by rw [hτ]; exact h⟩`.
-/
lemma exists_imaginary (H : Host E) : ∃ ξ : E, FD.cc ξ = -ξ ∧ ξ ≠ 0 ∧
    ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ ξ).im := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simpa using this
  have him : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.im ≠ 0 := by
    intro z hz h0
    have := congrArg Complex.re hz
    simp [sq, h0] at this
    nlinarith [mul_self_nonneg z.re]
  obtain ⟨σ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσ : (σ (H.rt : E)).im ≠ 0 := him _ (by rw [← map_pow, hsq]; simp)
  have hne : (H.rt : E) ≠ 0 := fun h => hσ (by rw [h]; simp)
  have hcc : FD.cc (H.rt : E) = -(H.rt : E) := by
    have h2 : (FD.cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      unfold FD.cc
      rw [← map_pow, hsq]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
    · exfalso
      have h3 := congrArg Complex.im (FD.emb_cc σ (H.rt : E))
      rw [h, Complex.conj_im] at h3
      exact hσ (by linarith)
    · exact h
  rcases lt_or_gt_of_ne (him _ H.sqrt_neg_disc_sq) with h | h
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 hne, fun τ hτ => ?_⟩
    · unfold FD.cc at hcc ⊢
      rw [map_neg, hcc]
    · rw [map_neg, hτ, Complex.neg_im]; linarith
  · exact ⟨_, hcc, hne, fun τ hτ => by rw [hτ]; exact h⟩

/- English proof (translation)
Take `⟨ξ, hξ, hξ0, hpos⟩` from `exists_imaginary H`. Take `⟨Gm, φ, hm⟩` from `exists_herm_coord_of_datum E H D ξ hξ hξ0 _ rfl`. Set `Ψ : Finset (E →+* ℂ)` to `Finset.univ.filter fun τ => τ (H.rt : E) = H.rt0`. Establish `hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0` using `fun τ => by simp [Ψ]`. Set `idx` to `(Fintype.equivFin (Ψ × Fin (D.p + D.q))).symm`.

Take `⟨h1, h2⟩` from `FramePeriod.isPeriod_frame E H D _ ξ Gm φ Ψ hΨ _ idx _ (fun _ => rfl) hξ (fun τ hτ => hpos τ ((hΨ τ).1 hτ)) hm rfl`. Use `choose Q hQ hG using fun τ : Ψ => (GlobalTheory.T.signature_hermitian_model_of_datum E H D _ ξ Gm φ hξ hm τ.1 ((hΨ _).1 τ.2)).1 (hpos _ ((hΨ _).1 τ.2))`. Establish `hx : (fun τ => Q τ : FD.Frame Ψ (D.p + D.q)) ∈ FD.GG Ψ Gm D.q`. Introduce `τ`. Use `⟨hQ τ, fun i => ?_⟩` and prove the remaining obligations.

Establish `h3 : FD.dmin Gm (fun τ => Q τ : FD.Frame Ψ (D.p + D.q)) τ i = ((FD.psgn D.q i : ℝ) : ℂ)`. Express the relevant statement in the definitionally equal form `FD.lminor (FD.gram τ.1 Gm (Q τ)) i = _`. Rewrite using `[hG, FD.FrameDegreeData.lminor_diagonal, FD.psgn, ← Fin.prod_univ_eq_prod_range]`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[h3, Complex.ofReal_re]`. Use `mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)` and prove the remaining obligations. Unfold `FD.sgn`. Apply the tactic sequence `split_ifs <;> norm_num`. Take `⟨⟨P, hP⟩, h4⟩` from `h2 _ hx`.

Use `⟨_, _, h1, ?_, P, h4 P hP⟩` and prove the remaining obligations. Rewrite using `[Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, card_cmType Ψ (FramePeriod.cmType H Ψ hΨ)]`.
-/
lemma exists_typeFn_period (H : Host E) (D : Datum H) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty ∧
      g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P := by
  classical
  obtain ⟨ξ, hξ, hξ0, hpos⟩ := exists_imaginary H
  obtain ⟨Gm, φ, hm⟩ := exists_herm_coord_of_datum E H D ξ hξ hξ0 _ rfl
  let Ψ : Finset (E →+* ℂ) := Finset.univ.filter fun τ => τ (H.rt : E) = H.rt0
  have hΨ : ∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0 := fun τ => by simp [Ψ]
  let idx := (Fintype.equivFin (Ψ × Fin (D.p + D.q))).symm
  obtain ⟨h1, h2⟩ := FramePeriod.isPeriod_frame E H D _ ξ Gm φ Ψ hΨ _ idx _ (fun _ => rfl) hξ
    (fun τ hτ => hpos τ ((hΨ τ).1 hτ)) hm rfl
  choose Q hQ hG using fun τ : Ψ =>
    (GlobalTheory.T.signature_hermitian_model_of_datum E H D _ ξ Gm φ hξ hm τ.1 ((hΨ _).1 τ.2)).1 (hpos _ ((hΨ _).1 τ.2))
  have hx : (fun τ => Q τ : FD.Frame Ψ (D.p + D.q)) ∈ FD.GG Ψ Gm D.q := by
    intro τ
    refine ⟨hQ τ, fun i => ?_⟩
    have h3 : FD.dmin Gm (fun τ => Q τ : FD.Frame Ψ (D.p + D.q)) τ i = ((FD.psgn D.q i : ℝ) : ℂ) := by
      change FD.lminor (FD.gram τ.1 Gm (Q τ)) i = _
      rw [hG, FD.FrameDegreeData.lminor_diagonal, FD.psgn, ← Fin.prod_univ_eq_prod_range]
      push_cast
      rfl
    rw [h3, Complex.ofReal_re]
    refine mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
    unfold FD.sgn
    split_ifs <;> norm_num
  obtain ⟨⟨P, hP⟩, h4⟩ := h2 _ hx
  refine ⟨_, _, h1, ?_, P, h4 P hP⟩
  rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin,
    card_cmType Ψ (FramePeriod.cmType H Ψ hΨ)]

/- English proof (translation)
Take `⟨g', ty', h', hg, P, hP⟩` from `exists_typeFn_period H D`. Take `⟨e, he⟩` from `exists_equiv_of_isTypeFn h h'`. Conclude with `⟨(Fin.equiv_iff_eq.1 ⟨e⟩).trans hg, exists_isPeriod_of_equiv e he hP⟩`.
-/
lemma period_of_isTypeFn (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ))
    (h : IsTypeFn H D.p D.q ty) :
    g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P := by
  obtain ⟨g', ty', h', hg, P, hP⟩ := exists_typeFn_period H D
  obtain ⟨e, he⟩ := exists_equiv_of_isTypeFn h h'
  exact ⟨(Fin.equiv_iff_eq.1 ⟨e⟩).trans hg, exists_isPeriod_of_equiv e he hP⟩

/- English proof (translation)
Introduce `E _ _ _ H D`. Take `⟨g, ty, h, -⟩` from `exists_typeFn_period H D`. Use `⟨⟨g, ty, h⟩, period_of_isTypeFn H D, fun hN hr l Xo c => ?_⟩` and prove the remaining obligations. Take `⟨U⟩` from `hN E H D l Xo (KA l).val.toRingHom g ty hr rfl h`. Set `i : Fin U.n` to `⟨0, U.n_pos⟩`.

Take `⟨-, P, hP⟩` from `period_of_isTypeFn H (U.Di i) g ty (by rw [(U.sig i).1, (U.sig i).2]; exact h)`. Establish `hw : CategoryTheory.CategoryStruct.comp (U.u i P) Xo.s = CategoryTheory.CategoryStruct.comp (spMap c.F.val.toRingHom) (spMap (IntermediateField.inclusion c.le).toRingHom)`. Rewrite using `[U.over_σ i P hP]`. Conclude with `AlgebraicGeometry.Spec.map_comp (CommRingCat.ofHom (IntermediateField.inclusion c.le).toRingHom) (CommRingCat.ofHom c.F.val.toRingHom)`. Conclude with `⟨(CategoryTheory.Limits.pullback.lift _ _ hw).base (IsLocalRing.closedPoint ℂ)⟩`.
-/
theorem typeFn_period_exist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty) ∧ (∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ P, IsPeriod D ty P) ∧ (N1c → 1 ≤ D.p + D.q → ∀ (l : Level H) (Xo : Moduli D l) (c : Coeff l), Nonempty (Xo.XF c)) := by
  intro E _ _ _ H D
  obtain ⟨g, ty, h, -⟩ := exists_typeFn_period H D
  refine ⟨⟨g, ty, h⟩, period_of_isTypeFn H D, fun hN hr l Xo c => ?_⟩
  obtain ⟨U⟩ := hN E H D l Xo (KA l).val.toRingHom g ty hr rfl h
  let i : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨-, P, hP⟩ := period_of_isTypeFn H (U.Di i) g ty (by rw [(U.sig i).1, (U.sig i).2]; exact h)
  have hw : CategoryTheory.CategoryStruct.comp (U.u i P) Xo.s =
      CategoryTheory.CategoryStruct.comp (spMap c.F.val.toRingHom)
        (spMap (IntermediateField.inclusion c.le).toRingHom) := by
    rw [U.over_σ i P hP]
    exact AlgebraicGeometry.Spec.map_comp (CommRingCat.ofHom (IntermediateField.inclusion c.le).toRingHom)
      (CommRingCat.ofHom c.F.val.toRingHom)
  exact ⟨(CategoryTheory.Limits.pullback.lift _ _ hw).base (IsLocalRing.closedPoint ℂ)⟩

end GlobalTheory.PeriodExists
