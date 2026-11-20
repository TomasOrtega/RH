import Formalism.LocalToGlobal.ProjectiveLattices.CurveSec

noncomputable section

namespace Formalism.L2.Pj

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Gaps.EtaleWeightGaps NumberField IsDedekindDomain

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {E : PtExt X} {hM : IntAtExt X E}
  {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData (xplus X E hM) ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} {g0 : B.Cusp j wF}

/- English proof (translation)
Establish `: FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)`. Establish `: FiniteDimensional (Kp (xplus X E hM) la G.N) (↥C.A' ⧸ C.JA)` using `C.fin`. Conclude with `LinearEquiv.finiteDimensional C.quotEquiv.toLinearEquiv`. Establish `: IsReduced (OsK (xplus X E hM) la G.w)`. Establish `: IsReduced (↥C.A' ⧸ C.JA)` using `C.red`.

Conclude with `isReduced_of_injective C.quotEquiv.symm.toRingHom C.quotEquiv.symm.injective`. Establish `: IsArtinianRing (OsK (xplus X E hM) la G.w)` using `IsArtinianRing.of_finite (Kp (xplus X E hM) la G.N) _`. Assume the negation of the conclusion as `hnu`. Use `set a := toOsK (xplus X E hM) la G.w x with ha`. Choose the witnesses or unpack the hypotheses as in `⟨I, hI⟩ : ∃ I : MaximalSpectrum (OsK (xplus X E hM) la G.w), a ∈ I.asIdeal := by`.

Take `⟨M, hM, haM⟩` from `Ideal.exists_le_maximal (Ideal.span {a}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Conclude with `⟨⟨M, hM⟩, haM (Ideal.subset_span rfl)⟩`. Set `e` to `IsArtinianRing.equivPi (OsK (xplus X E hM) la G.w)`. Use `set ε := e.symm (Pi.single I 1) with hε`. Establish `hεa : ε * a = 0`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, map_zero, hε, e.apply_symm_apply]`. Use function extensionality and compare the values at `m`. Distinguish the cases in `hm : m = I`. Substitute `hm` using the available equality.

Rewrite using `[Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.zero_apply]`. Use `show Ideal.Quotient.mk m.asIdeal a = 0`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hI`. Rewrite using `[Pi.mul_apply, Pi.single_eq_of_ne hm, zero_mul, Pi.zero_apply]`. Establish `hεε : ε * ε = ε`.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_mul, hε, e.apply_symm_apply]`. Use function extensionality and compare the values at `m`. Distinguish the cases in `hm : m = I`. Substitute `hm` using the available equality.

Rewrite using `[Pi.mul_apply, Pi.single_eq_same, one_mul]`. Rewrite using `[Pi.mul_apply, Pi.single_eq_of_ne hm, zero_mul]`. Establish `hε0 : ε ≠ 0`. Introduce `h`. Establish `h1` using `congrArg e h`.

Rewrite `h1` using `[hε, e.apply_symm_apply, map_zero]`. Establish `h2` using `congrFun h1 I`. Rewrite `h2` using `[Pi.single_eq_same, Pi.zero_apply]`. Establish `h3 : (1 : OsK (xplus X E hM) la G.w) ∈ I.asIdeal` using `Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact h2)`. Conclude with `I.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 h3)`.

Establish `hint : IsIntegral (Op (xplus X E hM) la G.N) ε`. Use `⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩` and prove the remaining obligations. Simplify using `[pow_two, hεε]`. Set `ε' : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w))` to `⟨ε, hint⟩`. Establish `hnot : ¬ IsUnit (1 - ε')`.

Introduce `hu`. Apply `hε0` to reduce the goal to its premises. Establish `h1 : ε' * (1 - ε') = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ε * (1 - ε) = 0`.

Rewrite using `[mul_sub, mul_one, hεε, sub_self]`. Establish `h2` using `(hu.mul_left_eq_zero).1 h1`. Conclude with `congrArg Subtype.val h2`. Take `⟨Z, hZ, hZ1⟩` from `Ideal.exists_le_maximal (Ideal.span {1 - ε'}) (by rwa [Ne, Ideal.span_singleton_eq_top])`. Set `ζ : PtsG G la` to `⟨Z, hZ⟩`.

Establish `hεZ : ε' ∉ ζ.asIdeal`. Introduce `h`. Establish `h1 : (1 - ε') + ε' ∈ Z` using `Z.add_mem (hZ1 (Ideal.subset_span rfl)) h`. Rewrite `h1` using `[sub_add_cancel]`. Conclude with `hZ.ne_top ((Ideal.eq_top_iff_one _).2 h1)`.

Take `⟨e0, he0⟩` from `toOsK_surjective (xplus X E hM) la G.w ε`. Establish `hev` using `(hw ζ).evW e0 ε' he0`. Establish `hu : IsUnit (algebraMap ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) (Loc ζ) ε')` using `(IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal ε').2 hεZ`. Establish `hne : (hw ζ).toSecPt.lift (e0 : Lw (xplus X E hM) la G.w) ≠ 0`. Rewrite using `[hev]`.

Conclude with `((hu.map (hw ζ).ι).map (algebraMap (hw ζ).T.V (hw ζ).T.Fr)).ne_zero`. Establish `hJ : e0 * x ∈ Jid (xplus X E hM) la G.w`. Rewrite using `[← toOsK_eq_zero_iff, map_mul, he0]`. Conclude with `hεa`. Establish `h0` using `(hw ζ).toSecPt.lift_Jid hJ`.

Rewrite `h0` using `[Subalgebra.coe_mul, map_mul]`. Conclude with `mul_ne_zero hne (hx ζ) h0`.
-/
theorem isUnit_toOsK_of_lift {y : PtsG G la → E.Pt' la} (hw : ∀ ζ, FromW ζ (y ζ)) (C : CurveModel G la g0)
    (x : ↥(Frac0 (xplus X E hM) la G.w))
    (hx : ∀ ζ, (hw ζ).toSecPt.lift (x : Lw (xplus X E hM) la G.w) ≠ 0) :
    IsUnit (toOsK (xplus X E hM) la G.w x) := by
  classical
  have : FiniteDimensional (Kp (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w) := by
    have : FiniteDimensional (Kp (xplus X E hM) la G.N) (↥C.A' ⧸ C.JA) := C.fin
    exact LinearEquiv.finiteDimensional C.quotEquiv.toLinearEquiv
  have : IsReduced (OsK (xplus X E hM) la G.w) := by
    have : IsReduced (↥C.A' ⧸ C.JA) := C.red
    exact isReduced_of_injective C.quotEquiv.symm.toRingHom C.quotEquiv.symm.injective
  have : IsArtinianRing (OsK (xplus X E hM) la G.w) := IsArtinianRing.of_finite (Kp (xplus X E hM) la G.N) _
  by_contra hnu
  set a := toOsK (xplus X E hM) la G.w x with ha
  obtain ⟨I, hI⟩ : ∃ I : MaximalSpectrum (OsK (xplus X E hM) la G.w), a ∈ I.asIdeal := by
    obtain ⟨M, hM, haM⟩ := Ideal.exists_le_maximal (Ideal.span {a}) (by rwa [Ne, Ideal.span_singleton_eq_top])
    exact ⟨⟨M, hM⟩, haM (Ideal.subset_span rfl)⟩
  let e := IsArtinianRing.equivPi (OsK (xplus X E hM) la G.w)
  set ε := e.symm (Pi.single I 1) with hε
  have hεa : ε * a = 0 := by
    apply e.injective
    rw [map_mul, map_zero, hε, e.apply_symm_apply]
    funext m
    by_cases hm : m = I
    · subst hm
      rw [Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.zero_apply]
      show Ideal.Quotient.mk m.asIdeal a = 0
      exact Ideal.Quotient.eq_zero_iff_mem.2 hI
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hm, zero_mul, Pi.zero_apply]
  have hεε : ε * ε = ε := by
    apply e.injective
    rw [map_mul, hε, e.apply_symm_apply]
    funext m
    by_cases hm : m = I
    · subst hm; rw [Pi.mul_apply, Pi.single_eq_same, one_mul]
    · rw [Pi.mul_apply, Pi.single_eq_of_ne hm, zero_mul]
  have hε0 : ε ≠ 0 := by
    intro h
    have h1 := congrArg e h
    rw [hε, e.apply_symm_apply, map_zero] at h1
    have h2 := congrFun h1 I
    rw [Pi.single_eq_same, Pi.zero_apply] at h2
    have h3 : (1 : OsK (xplus X E hM) la G.w) ∈ I.asIdeal :=
      Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_one]; exact h2)
    exact I.isMaximal.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hint : IsIntegral (Op (xplus X E hM) la G.N) ε := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩
    simp [pow_two, hεε]
  let ε' : ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) := ⟨ε, hint⟩
  have hnot : ¬ IsUnit (1 - ε') := by
    intro hu
    apply hε0
    have h1 : ε' * (1 - ε') = 0 := by
      apply Subtype.ext
      show ε * (1 - ε) = 0
      rw [mul_sub, mul_one, hεε, sub_self]
    have h2 := (hu.mul_left_eq_zero).1 h1
    exact congrArg Subtype.val h2
  obtain ⟨Z, hZ, hZ1⟩ := Ideal.exists_le_maximal (Ideal.span {1 - ε'}) (by rwa [Ne, Ideal.span_singleton_eq_top])
  let ζ : PtsG G la := ⟨Z, hZ⟩
  have hεZ : ε' ∉ ζ.asIdeal := by
    intro h
    have h1 : (1 - ε') + ε' ∈ Z := Z.add_mem (hZ1 (Ideal.subset_span rfl)) h
    rw [sub_add_cancel] at h1
    exact hZ.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  obtain ⟨e0, he0⟩ := toOsK_surjective (xplus X E hM) la G.w ε
  have hev := (hw ζ).evW e0 ε' he0
  have hu : IsUnit (algebraMap ↥(As (Op (xplus X E hM) la G.N) (OsK (xplus X E hM) la G.w)) (Loc ζ) ε') :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (Loc ζ) ζ.asIdeal ε').2 hεZ
  have hne : (hw ζ).toSecPt.lift (e0 : Lw (xplus X E hM) la G.w) ≠ 0 := by
    rw [hev]
    exact ((hu.map (hw ζ).ι).map (algebraMap (hw ζ).T.V (hw ζ).T.Fr)).ne_zero
  have hJ : e0 * x ∈ Jid (xplus X E hM) la G.w := by
    rw [← toOsK_eq_zero_iff, map_mul, he0]
    exact hεa
  have h0 := (hw ζ).toSecPt.lift_Jid hJ
  rw [Subalgebra.coe_mul, map_mul] at h0
  exact mul_ne_zero hne (hx ζ) h0

end Formalism.L2.Pj
