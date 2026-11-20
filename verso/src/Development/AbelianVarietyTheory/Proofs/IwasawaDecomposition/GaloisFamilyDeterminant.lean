import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ResidueLocPlace

/- English proof (translation)
Establish `hy : IsIntegral ℤ_[p] y` using `Algebra.IsIntegral.isIntegral y`. Set `v` to `NormedField.valuation (K := Qbar p)`. Establish `hmem : ∀ z : ℤ_[p], ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom) z ∈ v.integer`. Introduce `z`. Rewrite using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`.

Establish `: ‖algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])‖ ≤ 1`. Rewrite using `[PadicAlgCl.norm_extends p]`. Conclude with `PadicInt.norm_le_one z`. Conclude with `this` after adjusting the coercions. Set `φ : ℤ_[p] →+* v.integer` to `((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom).codRestrict v.integer hmem`.

Establish `hI : IsIntegral v.integer (f y)`. Use `IsIntegral.map_of_comp_eq φ f ?_ hy` and prove the remaining obligations. Use extensionality with `z`. Simplify using `only [RingHom.comp_apply, hf]`. Both sides reduce to the same expression.

Establish `h` using `(Valuation.integer.integers v).mem_of_integral hI`. Rewrite `h` using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`. Conclude with `h` after adjusting the coercions.
-/
theorem norm_le_one_of_finite {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (f : O →+* Qbar p)
    (hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])) (y : O) :
    ‖f y‖ ≤ 1 := by
  have hy : IsIntegral ℤ_[p] y := Algebra.IsIntegral.isIntegral y
  let v := NormedField.valuation (K := Qbar p)
  have hmem : ∀ z : ℤ_[p], ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom) z ∈ v.integer := by
    intro z
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    have : ‖algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])‖ ≤ 1 := by
      rw [PadicAlgCl.norm_extends p]; exact PadicInt.norm_le_one z
    exact_mod_cast this
  let φ : ℤ_[p] →+* v.integer := ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom).codRestrict v.integer hmem
  have hI : IsIntegral v.integer (f y) := by
    refine IsIntegral.map_of_comp_eq φ f ?_ hy
    ext z
    simp only [RingHom.comp_apply, hf]
    rfl
  have h := (Valuation.integer.integers v).mem_of_integral hI
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

/- English proof (translation)
Establish `hle : ∀ z : O, ‖f z‖ ≤ 1` using `norm_le_one_of_finite f hf`. Establish `hfp : ‖f (p : O)‖ = (p : ℝ)⁻¹`. Establish `h1` using `hf (p : ℤ_[p])`. Rewrite `h1` using `[map_natCast]`. Rewrite using `[h1, PadicAlgCl.norm_extends p]`.

Simplify using `[Padic.norm_p]`. Establish `hp1 : (p : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)`. Establish `hp0 : (p : O) ≠ 0`. Introduce `h`. Rewrite `hfp` using `[h, map_zero, norm_zero]`.

Establish `: (0 : ℝ) < (p : ℝ)⁻¹`. Use `(Fact.out : p.Prime).pos` as an intermediate fact. Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpu : ¬ IsUnit (p : O)`.

Introduce and unpack `⟨u, hu⟩`. Establish `h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`. Establish `h3` using `congrArg norm h2`. Rewrite `h3` using `[norm_mul, norm_one, hu, hfp]`. Establish `h4` using `hle ((u⁻¹ : Oˣ) : O)`.

Establish `h5 : (0 : ℝ) ≤ (p : ℝ)⁻¹` using `by positivity`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h4 h5]`. Distinguish the cases in `hy0 : y = 0`. Rewrite using `[hy0, map_zero, norm_zero]`. Conclude with `zero_lt_one`.

Take `⟨π, hπ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨e, u, hpe⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hπ`. Take `⟨k, w, hyk⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ`. Establish `he : e ≠ 0`. Introduce and unpack `rfl`.

Apply `hpu` to reduce the goal to its premises. Rewrite using `[hpe, pow_zero, mul_one]`. Conclude with `u.isUnit`. Establish `hk : k ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hy` using `[hyk, pow_zero, mul_one]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hy w.isUnit`. Establish `hu1 : ‖f (u : O)‖ = 1`. Establish `h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1` using `by rw [← map_mul, Units.mul_inv, map_one]`. Establish `h3` using `congrArg norm h2`.

Rewrite `h3` using `[norm_mul, norm_one]`. Establish `h4` using `hle ((u⁻¹ : Oˣ) : O)`. Establish `h6` using `hle (u : O)`. Establish `h5 : 0 ≤ ‖f (u : O)‖` using `norm_nonneg _`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h4 h5]`.

Establish `key : y ^ e * (u : O) ^ k = (p : O) ^ k * (w : O) ^ e`. Rewrite using `[hpe, hyk]`. Expand and normalize the polynomial expressions, which then agree. Establish `hn` using `congrArg (fun z => ‖f z‖) key`. Simplify using `only [map_mul, map_pow, norm_mul, norm_pow, hu1, one_pow, mul_one, hfp] at hn`.

Establish `hw` using `hle (w : O)`. Establish `hA : ‖f y‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k`. Rewrite using `[hn]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_one₀ (norm_nonneg _) hw`.

Use `_ = _ := mul_one _`. Establish `hB : ((p : ℝ)⁻¹) ^ k < 1` using `pow_lt_one₀ (by positivity) hp1 hk`. Conclude with `(pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 (lt_of_le_of_lt hA hB)`.
-/
theorem norm_lt_one_of_mem_maximalIdeal {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (f : O →+* Qbar p)
    (hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])) {y : O}
    (hy : y ∈ IsLocalRing.maximalIdeal O) : ‖f y‖ < 1 := by
  have hle : ∀ z : O, ‖f z‖ ≤ 1 := norm_le_one_of_finite f hf
  have hfp : ‖f (p : O)‖ = (p : ℝ)⁻¹ := by
    have h1 := hf (p : ℤ_[p])
    rw [map_natCast] at h1
    rw [h1, PadicAlgCl.norm_extends p]
    simp [Padic.norm_p]
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hp0 : (p : O) ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hfp
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have := (Fact.out : p.Prime).pos; positivity
    linarith
  have hpu : ¬ IsUnit (p : O) := by
    rintro ⟨u, hu⟩
    have h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one, hu, hfp] at h3
    have h4 := hle ((u⁻¹ : Oˣ) : O)
    have h5 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  by_cases hy0 : y = 0
  · rw [hy0, map_zero, norm_zero]; exact zero_lt_one
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hπ
  obtain ⟨k, w, hyk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  have he : e ≠ 0 := by
    rintro rfl; apply hpu; rw [hpe, pow_zero, mul_one]; exact u.isUnit
  have hk : k ≠ 0 := by
    rintro rfl
    rw [hyk, pow_zero, mul_one] at hy
    exact (IsLocalRing.mem_maximalIdeal _).1 hy w.isUnit
  have hu1 : ‖f (u : O)‖ = 1 := by
    have h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one] at h3
    have h4 := hle ((u⁻¹ : Oˣ) : O)
    have h6 := hle (u : O)
    have h5 : 0 ≤ ‖f (u : O)‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  have key : y ^ e * (u : O) ^ k = (p : O) ^ k * (w : O) ^ e := by
    rw [hpe, hyk]; ring
  have hn := congrArg (fun z => ‖f z‖) key
  simp only [map_mul, map_pow, norm_mul, norm_pow, hu1, one_pow, mul_one, hfp] at hn
  have hw := hle (w : O)
  have hA : ‖f y‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k := by
    rw [hn]
    calc ((p : ℝ)⁻¹) ^ k * ‖f (w : O)‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hw
      _ = _ := mul_one _
  have hB : ((p : ℝ)⁻¹) ^ k < 1 := pow_lt_one₀ (by positivity) hp1 hk
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 (lt_of_le_of_lt hA hB)

end GlobalTheory.ResidueLocPlace

namespace GlobalTheory.ResidueLocPlace

/- English proof (translation)
Substitute `h` using the available equality. Set `f : O →+* Qbar p` to `iq.comp (algebraMap O (FractionRing O))`. Establish `hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])` using `iq_alg`. Establish `hmem : ∀ y, ι (f y) ∈ B` using `fun y => (hB _).2 (by rw [RingEquiv.symm_apply_apply]; exact norm_le_one_of_finite f hf y)`. Set `g : O →+* B` to `(ι.toRingHom.comp f).codRestrict B.toSubring hmem`.

Set `F : O →+* Formalism.CyclotomicNorms.Fbar p` to `κB.toRingHom.comp ((IsLocalRing.residue B).comp g)`. Establish `hF : ∀ a ∈ IsLocalRing.maximalIdeal O, F a = 0`. Introduce `a ha`. Establish `hlt` using `norm_lt_one_of_mem_maximalIdeal f hf ha`. Establish `hg : g a ∈ IsLocalRing.maximalIdeal B`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce and unpack `⟨u, hu⟩`. Establish `h1 : ((u : B) : ℂ) * (((u⁻¹ : Bˣ) : B) : ℂ) = 1`. Rewrite using `[← Subring.coe_mul, Units.mul_inv]`. Both sides reduce to the same expression.

Rewrite `h1` using `[hu]`. Establish `h2 : ι (f a) = ((g a : B) : ℂ)` using `rfl`. Rewrite `h1` using `[← h2]`. Establish `h3` using `congrArg (fun z => ‖ι.symm z‖) h1`. Simplify using `only [map_mul, RingEquiv.symm_apply_apply, norm_mul, map_one, norm_one] at h3`.

Establish `h4 : ‖ι.symm (((u⁻¹ : Bˣ) : B) : ℂ)‖ ≤ 1` using `(hB _).1 (((u⁻¹ : Bˣ) : B)).2`. Establish `h5 : 0 ≤ ‖f a‖` using `norm_nonneg _`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left h4 h5]`. Use `show κB (IsLocalRing.residue B (g a)) = 0`. Rewrite using `[(IsLocalRing.residue_eq_zero_iff _).2 hg, map_zero]`.

Conclude with `⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) F hF, fun y => ⟨hmem y, rfl⟩⟩`.
-/
theorem exists_residue_lift {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (hp : p.Prime)
    (hq : q.Prime) (ι : Qbar p ≃+* ℂ) (B : ValuationSubring ℂ) (hB : ∀ z, z ∈ B ↔ ‖ι.symm z‖ ≤ 1)
    (κB : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar p)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[q] O]
    [Module.Finite ℤ_[q] O] (iq : FractionRing O →+* Qbar q)
    (iq_alg : ∀ z : ℤ_[q], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[q] O z)) =
      algebraMap ℚ_[q] (Qbar q) (z : ℚ_[q])) :
    ∃ κ : IsLocalRing.ResidueField O →+* Formalism.CyclotomicNorms.Fbar q, ∀ y : O,
      ∃ hy : (((qCast h ι).toRingHom.comp iq).comp (algebraMap O (FractionRing O))) y ∈ B,
        fbCast h hp hq (κB (IsLocalRing.residue B ⟨_, hy⟩)) = κ (IsLocalRing.residue O y) := by
  subst h
  let f : O →+* Qbar p := iq.comp (algebraMap O (FractionRing O))
  have hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := iq_alg
  have hmem : ∀ y, ι (f y) ∈ B := fun y =>
    (hB _).2 (by rw [RingEquiv.symm_apply_apply]; exact norm_le_one_of_finite f hf y)
  let g : O →+* B := (ι.toRingHom.comp f).codRestrict B.toSubring hmem
  let F : O →+* Formalism.CyclotomicNorms.Fbar p := κB.toRingHom.comp ((IsLocalRing.residue B).comp g)
  have hF : ∀ a ∈ IsLocalRing.maximalIdeal O, F a = 0 := by
    intro a ha
    have hlt := norm_lt_one_of_mem_maximalIdeal f hf ha
    have hg : g a ∈ IsLocalRing.maximalIdeal B := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have h1 : ((u : B) : ℂ) * (((u⁻¹ : Bˣ) : B) : ℂ) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]; rfl
      rw [hu] at h1
      have h2 : ι (f a) = ((g a : B) : ℂ) := rfl
      rw [← h2] at h1
      have h3 := congrArg (fun z => ‖ι.symm z‖) h1
      simp only [map_mul, RingEquiv.symm_apply_apply, norm_mul, map_one, norm_one] at h3
      have h4 : ‖ι.symm (((u⁻¹ : Bˣ) : B) : ℂ)‖ ≤ 1 := (hB _).1 (((u⁻¹ : Bˣ) : B)).2
      have h5 : 0 ≤ ‖f a‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h4 h5]
    show κB (IsLocalRing.residue B (g a)) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).2 hg, map_zero]
  exact ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) F hF, fun y => ⟨hmem y, rfl⟩⟩

end GlobalTheory.ResidueLocPlace

/- English proof (translation)
Introduce `D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i`. Conclude with `GlobalTheory.ResidueLocPlace.exists_residue_lift (X.nd.w_l i) _ _ (A.pl.ι (X.nd.w i)) (A.pl.plB (X.nd.w i)) (A.pl.plB_eq (X.nd.w i)) (A.pl.plκ (X.nd.w i)) (Sp.iq i) (Sp.iq_alg i)`.
-/
theorem GlobalTheory.ResidueLocPlace.exists_residueField_map : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ κ : IsLocalRing.ResidueField (X.nd.O i) →+* Formalism.CyclotomicNorms.Fbar (X.nd.l i), ∀ y : X.nd.O i, ∃ h : (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) y ∈ A.pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) = κ (IsLocalRing.residue (X.nd.O i) y) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i
  exact GlobalTheory.ResidueLocPlace.exists_residue_lift (X.nd.w_l i) _ _ (A.pl.ι (X.nd.w i)) (A.pl.plB (X.nd.w i))
    (A.pl.plB_eq (X.nd.w i)) (A.pl.plκ (X.nd.w i)) (Sp.iq i) (Sp.iq_alg i)
