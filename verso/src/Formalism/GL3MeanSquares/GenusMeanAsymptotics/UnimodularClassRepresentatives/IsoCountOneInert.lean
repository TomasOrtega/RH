import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MapMkConjTranspose

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.IsotropicCounts

open Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [hFF : Fact (IsFixF K F)] {m : ℕ}

/- English proof (translation)
Establish `hF` using `hFF.out`. Use `set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def`. Take `⟨θ, hθ⟩` from `exists_sub_conjO_notMem hK hP`. Establish `e1 : extP K 𝔭 ^ 1 = P`. Rewrite using `[pow_one]`.

Conclude with `SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP (by rw [← conjIdeal_eq_comap]; exact hc) hθ`. Set `_` to `Ideal.Quotient.field P`. Use `NormResidues.finite_quot hP` as an intermediate fact. Set `_` to `Fintype.ofFinite (𝓞 K ⧸ P)`. Establish `hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 ^ 2`.

Rewrite using `[← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_inert hK hF hP hc]`. Establish `hσ : ∀ x, NormResidues.sigEquiv P hc (NormResidues.sigEquiv P hc x) = x` using `NormResidues.sigHom_sigHom P hc`. Establish `hne : ∃ x, NormResidues.sigEquiv P hc x ≠ x`. Use `⟨Ideal.Quotient.mk P θ, fun h => hθ ?_⟩` and prove the remaining obligations. Rewrite `h` using `[NormResidues.sigEquiv_mk]`.

Conclude with `Ideal.Quotient.eq.1 h.symm`. Establish `h1` using `UnitaryNormCounts.card_inert (m := Fin m) (Ideal.quotEquivOfEq e1) (NormResidues.sigEquiv P hc) (by`. Introduce `a`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite using `[star_mk, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk, NormResidues.sigEquiv_mk]`.

Use the proof step `rfl) hσ hne _ hq (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (u i))`. Use the proof step `(by`. Introduce `i`. Rewrite using `[star_mk, star_def, hu])`. Use the proof step `(fun i => isUnit_mk (hunit i) 1)`.

Unfold `isoCount`. Rewrite using `[diagonal_map (map_zero _), h1]`. Conclude with `card_unitary_fin _ hσ hne _ hq m`.
-/
theorem isoCount_one_inert (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P) (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤) :
    (isoCount (P.comap (algebraMap (𝓞 F) (𝓞 K))) 1 (diagonal u) : ℝ) =
      (Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ) ^ (m ^ 2) *
        ∏ j ∈ Finset.Icc 1 m,
          (1 - (-(Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ))⁻¹ ^ j) := by
  have hF := hFF.out
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  obtain ⟨θ, hθ⟩ := exists_sub_conjO_notMem hK hP
  have e1 : extP K 𝔭 ^ 1 = P := by
    rw [pow_one]
    exact SplitPrimeIdeals.map_comap_of_inert conjO_conjO (conjO_eq_iff_mem_range hF) hP
      (by rw [← conjIdeal_eq_comap]; exact hc) hθ
  let _ := Ideal.Quotient.field P
  have := NormResidues.finite_quot hP
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_inert hK hF hP hc]
  have hσ : ∀ x, NormResidues.sigEquiv P hc (NormResidues.sigEquiv P hc x) = x := NormResidues.sigHom_sigHom P hc
  have hne : ∃ x, NormResidues.sigEquiv P hc x ≠ x := by
    refine ⟨Ideal.Quotient.mk P θ, fun h => hθ ?_⟩
    rw [NormResidues.sigEquiv_mk] at h
    exact Ideal.Quotient.eq.1 h.symm
  have h1 := UnitaryNormCounts.card_inert (m := Fin m) (Ideal.quotEquivOfEq e1) (NormResidues.sigEquiv P hc)
    (by
      intro a
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [star_mk, Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk, NormResidues.sigEquiv_mk]
      rfl) hσ hne _ hq (fun i => Ideal.Quotient.mk (extP K 𝔭 ^ 1) (u i))
    (by
      intro i
      rw [star_mk, star_def, hu])
    (fun i => isUnit_mk (hunit i) 1)
  unfold isoCount
  rw [diagonal_map (map_zero _), h1]
  exact card_unitary_fin _ hσ hne _ hq m

/- English proof (translation)
Establish `hF` using `hFF.out`. Establish `h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P`. Use `set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def`. Establish `e1 : extP K 𝔭 ^ 1 ≤ P`. Rewrite using `[pow_one]`.

Conclude with `Ideal.map_comap_le`. Set `_` to `Ideal.Quotient.field P`. Use `NormResidues.finite_quot hP` as an intermediate fact. Set `_` to `Fintype.ofFinite (𝓞 K ⧸ P)`. Use `finite_quot (K := K) h𝔭 1` as an intermediate fact.

Establish `hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭`. Rewrite using `[← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_split hK hF hP hc]`. Establish `hb : Function.Bijective fun a : 𝓞 K ⧸ extP K 𝔭 ^ 1 => (Ideal.Quotient.factor e1 (star a), Ideal.Quotient.factor e1 a)`. Apply `Function.Surjective.bijective_of_nat_card_le` to reduce the goal to its premises. Introduce `y`.

Take `⟨z, hz⟩` from `NormResidues.pairHom_surjective hP hc y`. Use `⟨Ideal.Quotient.mk _ z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hz, NormResidues.pairHom_apply]`. Use `show (Ideal.Quotient.factor e1 (star (Ideal.Quotient.mk _ z)), _) = _`. Rewrite using `[star_mk]`.

Both sides reduce to the same expression. Rewrite using `[absNorm_extP_pow hK hF h𝔭, Nat.card_prod, Nat.card_eq_fintype_card, hq]`. Apply `le_of_eq` to reduce the goal to its premises. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `UnitaryNormCounts.card_split (m := Fin m) (Ideal.Quotient.factor e1) hb ((diagonal u).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1))) (by`.

Rewrite using `[map_mk_conjTranspose, diagonal_conjTranspose]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Conclude with `hu i)`. Use the proof step `(by`.

Rewrite using `[diagonal_map (map_zero _), det_diagonal]`. Conclude with `Finset.univ.prod_induction _ IsUnit (fun _ _ h1 h2 => h1.mul h2) isUnit_one (fun i _ => isUnit_mk (hunit i) 1))`. Unfold `isoCount`. Rewrite using `[h1]`. Conclude with `card_GL_fin _ hq m`.
-/
theorem isoCount_one_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {P : Ideal (𝓞 K)} (hP : P.IsMaximal)
    (hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P ≠ P) (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤) :
    (isoCount (P.comap (algebraMap (𝓞 F) (𝓞 K))) 1 (diagonal u) : ℝ) =
      (Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ) ^ (m ^ 2) *
        ∏ j ∈ Finset.Icc 1 m,
          (1 - ((Ideal.absNorm (P.comap (algebraMap (𝓞 F) (𝓞 K))) : ℝ))⁻¹ ^ j) := by
  have hF := hFF.out
  have h𝔭 : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
  set 𝔭 := P.comap (algebraMap (𝓞 F) (𝓞 K)) with h𝔭def
  have e1 : extP K 𝔭 ^ 1 ≤ P := by
    rw [pow_one]
    exact Ideal.map_comap_le
  let _ := Ideal.Quotient.field P
  have := NormResidues.finite_quot hP
  let _ := Fintype.ofFinite (𝓞 K ⧸ P)
  have := finite_quot (K := K) h𝔭 1
  have hq : Fintype.card (𝓞 K ⧸ P) = Ideal.absNorm 𝔭 := by
    rw [← Nat.card_eq_fintype_card, NormResidues.natCard_quot, absNorm_comap_split hK hF hP hc]
  have hb : Function.Bijective fun a : 𝓞 K ⧸ extP K 𝔭 ^ 1 =>
      (Ideal.Quotient.factor e1 (star a), Ideal.Quotient.factor e1 a) := by
    apply Function.Surjective.bijective_of_nat_card_le
    · intro y
      obtain ⟨z, hz⟩ := NormResidues.pairHom_surjective hP hc y
      refine ⟨Ideal.Quotient.mk _ z, ?_⟩
      rw [← hz, NormResidues.pairHom_apply]
      show (Ideal.Quotient.factor e1 (star (Ideal.Quotient.mk _ z)), _) = _
      rw [star_mk]
      rfl
    · rw [absNorm_extP_pow hK hF h𝔭, Nat.card_prod, Nat.card_eq_fintype_card, hq]
      apply le_of_eq
      ring
  have h1 := UnitaryNormCounts.card_split (m := Fin m) (Ideal.Quotient.factor e1) hb
    ((diagonal u).map (Ideal.Quotient.mk (extP K 𝔭 ^ 1)))
    (by
      rw [map_mk_conjTranspose, diagonal_conjTranspose]
      congr 2
      funext i
      exact hu i)
    (by
      rw [diagonal_map (map_zero _), det_diagonal]
      exact Finset.univ.prod_induction _ IsUnit (fun _ _ h1 h2 => h1.mul h2) isUnit_one
        (fun i _ => isUnit_mk (hunit i) 1))
  unfold isoCount
  rw [h1]
  exact card_GL_fin _ hq m

/- English proof (translation)
Establish `hF` using `hFF.out`. Take `⟨P, hP, rfl⟩` from `exists_maximal_over hK hF h𝔭`. Unfold `alphaStd`. Rewrite using `[etaF_comap hK hF hP]`. Distinguish the cases in `hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P`.

Rewrite using `[isoCount_one_inert hK hP hc u hu hunit, if_pos hc]`. Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, ← mul_pow, inv_neg]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[isoCount_one_split hK hP hc u hu hunit, if_neg hc]`. Use `congr 1`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Rewrite using `[_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, one_pow, one_mul]`.
-/
theorem isoCount_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) :
    (isoCount 𝔭 1 (diagonal u) : ℝ) = (Ideal.absNorm 𝔭 : ℝ) ^ (m ^ 2) * alphaStd K 𝔭 m := by
  have hF := hFF.out
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  unfold alphaStd
  rw [etaF_comap hK hF hP]
  by_cases hc : Formalism.HermitianLatticesTheory.conjIdeal (K := K) P = P
  · rw [isoCount_one_inert hK hP hc u hu hunit, if_pos hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, ← mul_pow, inv_neg]
    congr 2
    ring
  · rw [isoCount_one_split hK hP hc u hu hunit, if_neg hc]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [_root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, one_pow, one_mul]

/- English proof (translation)
Establish `hg : (diagonal u)ᴴ = diagonal u`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hu i`.

Establish `hdet : Ideal.span {(diagonal u).det} ⊔ extP K 𝔭 = ⊤`. Rewrite using `[Matrix.det_diagonal, ← Ideal.prod_span_singleton]`. Conclude with `Ideal.prod_sup_eq_top fun i _ => hunit i`. Rewrite using `[isoCount_eq_pow hK h𝔭 (diagonal u) hg hdet k]`. Use `push_cast`.

Rewrite using `[isoCount_one hK h𝔭 u hu hunit]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isoCount_diag (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (u : Fin m → 𝓞 K) (hu : ∀ i, conjO K (u i) = u i)
    (hunit : ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤) (k : ℕ) :
    (isoCount 𝔭 (k + 1) (diagonal u) : ℝ) =
      (Ideal.absNorm 𝔭 : ℝ) ^ ((k + 1) * m ^ 2) * alphaStd K 𝔭 m := by
  have hg : (diagonal u)ᴴ = diagonal u := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact hu i
  have hdet : Ideal.span {(diagonal u).det} ⊔ extP K 𝔭 = ⊤ := by
    rw [Matrix.det_diagonal, ← Ideal.prod_span_singleton]
    exact Ideal.prod_sup_eq_top fun i _ => hunit i
  rw [isoCount_eq_pow hK h𝔭 (diagonal u) hg hdet k]
  push_cast
  rw [isoCount_one hK h𝔭 u hu hunit]
  ring

end Formalism.HermitianLattices.Ext.L3.IsotropicCounts
