import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Loc4ResOfLine

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

/- English proof (translation)
Introduce `h0`. Unfold `psiRes0 at h0`. Rewrite `h0` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Establish `hu : IsUnit (g⁻¹ 0 a)` using `WittVector.isUnit_of_coeff_zero_ne_zero _ h`. Establish `hu' : IsUnit (psiO X.p X.n' O 0 (g⁻¹ 0 a))` using `hu.map _`.

Conclude with `S.w_irr.not_isUnit (isUnit_of_dvd_unit h0 hu')`.
-/
theorem psiRes0_ne {X : Loc} [Fact X.p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
    (a : Fin (X.m + 1)) (h : WittVector.constantCoeff (g⁻¹ 0 a) ≠ 0) : psiRes0 X O S.w g a ≠ 0 := by
  intro h0
  unfold psiRes0 at h0
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
  have hu : IsUnit (g⁻¹ 0 a) := WittVector.isUnit_of_coeff_zero_ne_zero _ h
  have hu' : IsUnit (psiO X.p X.n' O 0 (g⁻¹ 0 a)) := hu.map _
  exact S.w_irr.not_isUnit (isUnit_of_dvd_unit h0 hu')

/- English proof (translation)
Introduce `X _ O _ _ _ _ S _ _ g _ hne h0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`. Apply `hne` to reduce the goal to its premises. Establish `hcc : ∀ c : Fin X.m, WittVector.constantCoeff (g⁻¹ 0 c.succ) = 0`.

Introduce `c`. Assume the negation of the conclusion as `hc`. Conclude with `psiRes0_ne S g c.succ hc (hall c)`. Establish `hv0 : WittVector.constantCoeff (g⁻¹ 0 0) ≠ 0`. Introduce `hz`.

Apply `h0` to reduce the goal to its premises. Unfold `psiRes0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Distinguish the cases in `hx : g⁻¹ 0 0 = 0`. Rewrite using `[hx, map_zero]`.

Conclude with `dvd_zero _`. Take `⟨m, b, hb, hab⟩` from `WittVector.exists_eq_pow_p_mul (g⁻¹ 0 0) hx`. Establish `hm : m ≠ 0`. Introduce and unpack `rfl`. Rewrite `hab` using `[pow_zero, one_mul]`.

Conclude with `hb (hab ▸ hz)`. Rewrite using `[hab, map_mul, map_pow, map_natCast]`. Establish `hwp : S.w ∣ (X.p : O)`. Establish `h1` using `S.p_mem`. Rewrite `h1` using `[(IsDiscreteValuationRing.irreducible_iff_uniformizer S.w).mp S.w_irr, Ideal.mem_span_singleton]`.

Conclude with `h1`. Conclude with `Dvd.dvd.mul_right (dvd_pow hwp hm) _`. Establish `hset : ∀ h : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'), ratPlane X.p X.n' 1 h = Submodule.span (GaloisField X.p X.n') {fun c => WittVector.constantCoeff (h⁻¹ 0 c)}`. Introduce `h`. Unfold `ratPlane`.

Use `congr 1`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, hi, rfl⟩`.

Establish `hi0 : i = 0` using `Fin.ext (by rw [Fin.val_zero]; omega)`. Rewrite using `[hi0]`. Introduce and unpack `rfl`. Conclude with `⟨0, by simp, rfl⟩`. Rewrite using `[hset g, hset 1, inv_one]`.

Establish `hv : (fun c => WittVector.constantCoeff (g⁻¹ 0 c)) = WittVector.constantCoeff (g⁻¹ 0 0) • (fun c => WittVector.constantCoeff ((1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) 0 c))`. Use function extensionality and compare the values at `c`. Use `Fin.cases ?_ (fun c' => ?_) c` and prove the remaining obligations. Simplify using the standard rewrite rules. Simplify using `[hcc c', Matrix.one_apply_ne (Fin.succ_ne_zero c').symm]`.

Rewrite using `[hv, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hv0)]`.
-/
theorem resLineAt : ResLineAt := by
  intro X _ O _ _ _ _ S _ _ g _ hne h0
  by_contra hall
  push_neg at hall
  apply hne
  have hcc : ∀ c : Fin X.m, WittVector.constantCoeff (g⁻¹ 0 c.succ) = 0 := by
    intro c
    by_contra hc
    exact psiRes0_ne S g c.succ hc (hall c)
  have hv0 : WittVector.constantCoeff (g⁻¹ 0 0) ≠ 0 := by
    intro hz
    apply h0
    unfold psiRes0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    by_cases hx : g⁻¹ 0 0 = 0
    · rw [hx, map_zero]
      exact dvd_zero _
    · obtain ⟨m, b, hb, hab⟩ := WittVector.exists_eq_pow_p_mul (g⁻¹ 0 0) hx
      have hm : m ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hab
        exact hb (hab ▸ hz)
      rw [hab, map_mul, map_pow, map_natCast]
      have hwp : S.w ∣ (X.p : O) := by
        have h1 := S.p_mem
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer S.w).mp S.w_irr,
          Ideal.mem_span_singleton] at h1
        exact h1
      exact Dvd.dvd.mul_right (dvd_pow hwp hm) _
  have hset : ∀ h : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'),
      ratPlane X.p X.n' 1 h =
        Submodule.span (GaloisField X.p X.n') {fun c => WittVector.constantCoeff (h⁻¹ 0 c)} := by
    intro h
    unfold ratPlane
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi0 : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
      rw [hi0]
    · rintro rfl
      exact ⟨0, by simp, rfl⟩
  rw [hset g, hset 1, inv_one]
  have hv : (fun c => WittVector.constantCoeff (g⁻¹ 0 c)) = WittVector.constantCoeff (g⁻¹ 0 0) •
      (fun c => WittVector.constantCoeff ((1 : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) 0 c)) := by
    funext c
    refine Fin.cases ?_ (fun c' => ?_) c
    · simp
    · simp [hcc c', Matrix.one_apply_ne (Fin.succ_ne_zero c').symm]
  rw [hv, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ hv0)]

/- English proof (translation)
The claim follows from `loc4Res_of_line resLineAt`.
-/
theorem loc4Res : LocalResidueBound := loc4Res_of_line resLineAt

end Formalism.MainNotions.ColumnSystems.Pf
