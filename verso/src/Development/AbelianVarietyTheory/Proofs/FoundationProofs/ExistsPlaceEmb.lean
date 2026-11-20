import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerRankVanishing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

namespace GlobalTheory.EmbThroughCompletion

section Norm

/- English proof (translation)
Set `f : R →+* (NormedField.valuation (K` to `C)).integer := (algebraMap R C).codRestrict _ (fun r => by`. Rewrite using `[Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]`. Conclude with `hR r)`. Establish `h1 : IsIntegral (NormedField.valuation (K` using `C)).integer x := hx.map_of_comp_eq f (RingHom.id C) (by ext r; rfl)`. Establish `h2` using `(Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h1`.

Rewrite `h2` using `[Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]`. Conclude with `h2`.
-/
theorem norm_le_one_of_isIntegral {R C : Type} [CommRing R] [NormedField C] [IsUltrametricDist C]
    [Algebra R C] (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {x : C} (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  let f : R →+* (NormedField.valuation (K := C)).integer :=
    (algebraMap R C).codRestrict _ (fun r => by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
      exact hR r)
  have h1 : IsIntegral (NormedField.valuation (K := C)).integer x :=
    hx.map_of_comp_eq f (RingHom.id C) (by ext r; rfl)
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h1
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe] at h2
  exact h2

variable {E C : Type} [Field E] [NumberField E] [NormedField C] [IsUltrametricDist C]

/- English proof (translation)
The claim follows from `norm_le_one_of_isIntegral (R := ℤ) (fun r => by simpa using IsUltrametricDist.norm_intCast_le_one C r) (map_isIntegral_int a x.isIntegral_coe)`.
-/
theorem norm_int_le_one (a : E →+* C) (x : 𝓞 E) : ‖a (x : E)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (R := ℤ) (fun r => by simpa using IsUltrametricDist.norm_intCast_le_one C r)
    (map_isIntegral_int a x.isIntegral_coe)

/- English proof (translation)
Take `⟨n, d, h⟩` from `v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x`. Establish `hd : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ‖c ((d : 𝓞 E) : E)‖ = 1` using `fun c hc => le_antisymm (norm_int_le_one c _) (not_lt.1 fun h' => d.2 ((hc _).1 h'))`. Break down `h with h | h` into its components or cases. Establish `key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → (‖c x‖ < 1 ↔ n ∈ v.asIdeal)`. Introduce `c hc`.

Establish `h1` using `congrArg (fun y => ‖c y‖) h`. Simplify using `only [map_mul, norm_mul] at h1`. Rewrite using `[← hc n]`. Express the relevant statement in the definitionally equal form `‖c x‖ * ‖c ((d : 𝓞 E) : E)‖ = ‖c (n : E)‖ at h1`. Rewrite `h1` using `[hd c hc, mul_one]`.

Rewrite using `[h1]`. Rewrite using `[key a ha, key b hb]`. Establish `key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ¬ ‖c x‖ < 1`. Introduce `c hc hlt`. Establish `h1` using `congrArg (fun y => ‖c y‖) h`.

Simplify using `only [map_mul, norm_mul] at h1`. Express the relevant statement in the definitionally equal form `‖c x‖ * ‖c (n : E)‖ = ‖c ((d : 𝓞 E) : E)‖ at h1`. Rewrite `h1` using `[hd c hc]`. Establish `h2` using `norm_int_le_one c n`. Establish `h3` using `norm_nonneg (c x)`.

Establish `h4` using `norm_nonneg (c (n : E))`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `iff_of_false (key a ha) (key b hb)`.
-/
theorem norm_lt_one_iff (v : HeightOneSpectrum (𝓞 E)) (a b : E →+* C)
    (ha : ∀ x : 𝓞 E, ‖a (x : E)‖ < 1 ↔ x ∈ v.asIdeal) (hb : ∀ x : 𝓞 E, ‖b (x : E)‖ < 1 ↔ x ∈ v.asIdeal)
    (x : E) : ‖a x‖ < 1 ↔ ‖b x‖ < 1 := by
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) x
  have hd : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ‖c ((d : 𝓞 E) : E)‖ = 1 :=
    fun c hc => le_antisymm (norm_int_le_one c _) (not_lt.1 fun h' => d.2 ((hc _).1 h'))
  rcases h with h | h
  · have key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) →
        (‖c x‖ < 1 ↔ n ∈ v.asIdeal) := by
      intro c hc
      have h1 := congrArg (fun y => ‖c y‖) h
      simp only [map_mul, norm_mul] at h1
      rw [← hc n]
      change ‖c x‖ * ‖c ((d : 𝓞 E) : E)‖ = ‖c (n : E)‖ at h1
      rw [hd c hc, mul_one] at h1
      rw [h1]
    rw [key a ha, key b hb]
  · have key : ∀ c : E →+* C, (∀ x : 𝓞 E, ‖c (x : E)‖ < 1 ↔ x ∈ v.asIdeal) → ¬ ‖c x‖ < 1 := by
      intro c hc hlt
      have h1 := congrArg (fun y => ‖c y‖) h
      simp only [map_mul, norm_mul] at h1
      change ‖c x‖ * ‖c (n : E)‖ = ‖c ((d : 𝓞 E) : E)‖ at h1
      rw [hd c hc] at h1
      have h2 := norm_int_le_one c n
      have h3 := norm_nonneg (c x)
      have h4 := norm_nonneg (c (n : E))
      nlinarith
    exact iff_of_false (key a ha) (key b hb)

end Norm

section Padic

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `hx : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Rewrite `h` using `[← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)]`. Establish `hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Conclude with `fun n => ⟨⟨_, h n⟩, rfl⟩`.

Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]`.
-/
theorem isIntegral_of_norm_le_one (x : PadicAlgCl l) (h : ‖x‖ ≤ 1) : IsIntegral ℤ_[l] x := by
  have hx : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic hx)] at h
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n => ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl (minpoly.monic hx)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

/- English proof (translation)
Use `(isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).symm.trans ⟨fun h => norm_le_one_of_isIntegral (fun r => ?_) h, fun h => isIntegral_of_norm_le_one _ h⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]`. Conclude with `r.2`.
-/
theorem mem_OL_iff (K : Loc.FinExt l) (x : K.1) : x ∈ Loc.OL K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  refine (isIntegral_algHom_iff (K.1.val.restrictScalars ℤ_[l]) K.1.val.toRingHom.injective).symm.trans
    ⟨fun h => norm_le_one_of_isIntegral (fun r => ?_) h, fun h => isIntegral_of_norm_le_one _ h⟩
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
  exact r.2

/- English proof (translation)
Establish `hx` using `(mem_OL_iff K _).1 x.2`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `lt_of_le_of_ne hx fun h1 => h ?_` and prove the remaining obligations. Establish `h0 : (x : K.1) ≠ 0`.

Introduce `h0`. Rewrite `h1` using `[h0]`. Simplify using `at h1`. Use `isUnit_iff_exists_inv.2 ⟨⟨(x : K.1)⁻¹, (mem_OL_iff K _).2 ?_⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.coe_inv, norm_inv, h1, inv_one]`.

Introduce `h hu`. Take `⟨y, hy⟩` from `isUnit_iff_exists_inv.1 hu`. Establish `hy'` using `(mem_OL_iff K _).1 y.2`. Establish `h1` using `congrArg (fun z : Loc.OL K => ‖((z : K.1) : PadicAlgCl l)‖) hy`. Simplify using `only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h1`.

Establish `h3` using `norm_nonneg ((x : K.1) : PadicAlgCl l)`. Establish `h4` using `norm_nonneg ((y : K.1) : PadicAlgCl l)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem not_isUnit_iff (K : Loc.FinExt l) (x : Loc.OL K) :
    ¬ IsUnit x ↔ ‖((x : K.1) : PadicAlgCl l)‖ < 1 := by
  have hx := (mem_OL_iff K _).1 x.2
  constructor
  · intro h
    refine lt_of_le_of_ne hx fun h1 => h ?_
    have h0 : (x : K.1) ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
    refine isUnit_iff_exists_inv.2 ⟨⟨(x : K.1)⁻¹, (mem_OL_iff K _).2 ?_⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩
    rw [IntermediateField.coe_inv, norm_inv, h1, inv_one]
  · intro h hu
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hu
    have hy' := (mem_OL_iff K _).1 y.2
    have h1 := congrArg (fun z : Loc.OL K => ‖((z : K.1) : PadicAlgCl l)‖) hy
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at h1
    have h3 := norm_nonneg ((x : K.1) : PadicAlgCl l)
    have h4 := norm_nonneg ((y : K.1) : PadicAlgCl l)
    nlinarith

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hd : DenseRange (Pi.map fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l]))` using `DenseRange.piMap fun _ => Padic.denseRange_ratCast l`. Establish `hcl : ∀ f : E →+* PadicAlgCl l, IsClopen {c : Fin n → ℚ_[l] | ‖∑ k, c k • f (y k)‖ < 1}`. Introduce `f`. Use `(IsUltrametricDist.isClopen_ball (0 : PadicAlgCl l) 1).preimage (f := fun c : Fin n → ℚ_[l] => ∑ k, c k • f (y k)) (by fun_prop)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `c`. Simplify using the standard rewrite rules. Establish `key : ∀ c : Fin n → ℚ_[l], ‖∑ k, c k • a (y k)‖ < 1 → ‖∑ k, c k • b (y k)‖ < 1`. Introduce `c`. Use `hd.induction_on c ?_ fun q => ?_` and prove the remaining obligations.

Use `(hcl a).compl.isClosed.union (hcl b).isClosed` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `c`. Simplify using `only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]`. Conclude with `imp_iff_not_or`.

Establish `e : ∀ f : E →+* PadicAlgCl l, ∑ k, (Pi.map (fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) q) k • f (y k) = f (∑ k, (q k : E) * y k)`. Introduce `f`. Simplify using `[Algebra.smul_def]`. Rewrite using `[e a, e b]`. Conclude with `(h _).1`.

Assume the negation of the conclusion as `hne`. Establish `hpos : 0 < ‖∑ k, c k • b (y k)‖` using `norm_pos_iff.2 hne`. Take `⟨r, hr⟩` from `NormedField.exists_lt_norm ℚ_[l] ‖∑ k, c k • b (y k)‖⁻¹`. Establish `h1` using `key (r • c) (by`. Simplify using `only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, hc, smul_zero, norm_zero, zero_lt_one])`.

Simplify using `only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, norm_smul] at h1`. Rewrite `hr` using `[inv_lt_iff_one_lt_mul₀ hpos]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_eq_zero (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) {n : ℕ}
    (y : Fin n → E) (c : Fin n → ℚ_[l]) (hc : ∑ k, c k • a (y k) = 0) : ∑ k, c k • b (y k) = 0 := by
  have hd : DenseRange (Pi.map fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ f : E →+* PadicAlgCl l, IsClopen {c : Fin n → ℚ_[l] | ‖∑ k, c k • f (y k)‖ < 1} := by
    intro f
    have := (IsUltrametricDist.isClopen_ball (0 : PadicAlgCl l) 1).preimage
      (f := fun c : Fin n → ℚ_[l] => ∑ k, c k • f (y k)) (by fun_prop)
    convert this using 1
    ext c
    simp
  have key : ∀ c : Fin n → ℚ_[l], ‖∑ k, c k • a (y k)‖ < 1 → ‖∑ k, c k • b (y k)‖ < 1 := by
    intro c
    refine hd.induction_on c ?_ fun q => ?_
    · have := (hcl a).compl.isClosed.union (hcl b).isClosed
      convert this using 1
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      exact imp_iff_not_or
    · have e : ∀ f : E →+* PadicAlgCl l,
          ∑ k, (Pi.map (fun _ : Fin n => (Rat.cast : ℚ → ℚ_[l])) q) k • f (y k) =
            f (∑ k, (q k : E) * y k) := by
        intro f
        simp [Algebra.smul_def]
      rw [e a, e b]
      exact (h _).1
  by_contra hne
  have hpos : 0 < ‖∑ k, c k • b (y k)‖ := norm_pos_iff.2 hne
  obtain ⟨r, hr⟩ := NormedField.exists_lt_norm ℚ_[l] ‖∑ k, c k • b (y k)‖⁻¹
  have h1 := key (r • c) (by
    simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, hc, smul_zero, norm_zero, zero_lt_one])
  simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, norm_smul] at h1
  rw [inv_lt_iff_one_lt_mul₀ hpos] at hr
  linarith

/- English proof (translation)
Set `pb` to `Field.powerBasisOfFiniteOfSeparable ℚ E`. Establish `hroot : Polynomial.aeval (b pb.gen) (minpoly ℚ_[l] (a pb.gen)) = 0`. Establish `h0` using `minpoly.aeval ℚ_[l] (a pb.gen)`. Rewrite `h0`, the goal using `[Polynomial.aeval_eq_sum_range, Finset.sum_range]`. Simplify using `only [← map_pow] at h0 ⊢`.

Conclude with `sum_eq_zero a b h _ _ h0`. Take `⟨g, hg⟩` from `minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) hroot`. Use `⟨g, fun x => ?_⟩` and prove the remaining obligations. Establish `: ((g : PadicAlgCl l →+* PadicAlgCl l).comp a).toRatAlgHom = b.toRatAlgHom` using `pb.algHom_ext hg`. Conclude with `DFunLike.congr_fun this x`.
-/
theorem exists_conj (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) :
    ∃ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, g (a x) = b x := by
  let pb := Field.powerBasisOfFiniteOfSeparable ℚ E
  have hroot : Polynomial.aeval (b pb.gen) (minpoly ℚ_[l] (a pb.gen)) = 0 := by
    have h0 := minpoly.aeval ℚ_[l] (a pb.gen)
    rw [Polynomial.aeval_eq_sum_range, Finset.sum_range] at h0 ⊢
    simp only [← map_pow] at h0 ⊢
    exact sum_eq_zero a b h _ _ h0
  obtain ⟨g, hg⟩ := minpoly.exists_algEquiv_of_root' (Algebra.IsAlgebraic.isAlgebraic _) hroot
  refine ⟨g, fun x => ?_⟩
  have : ((g : PadicAlgCl l →+* PadicAlgCl l).comp a).toRatAlgHom = b.toRatAlgHom :=
    pb.algHom_ext hg
  exact DFunLike.congr_fun this x

variable {Ω : Type} [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_conj (Bw.j.comp (algebraMap E Ω)) (Bw.LL.1.val.toRingHom.comp b) (norm_lt_one_iff v _ _ (fun x => by`. Rewrite using `[← hA x, ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, hj, RingHom.comp_apply, map_inv₀, norm_inv]`. Generalize the expression as in `algebraMap E Ω (x : E) = y`. Distinguish the cases in `hy : y = 0`. Simplify using `[hy]`.

Establish `: 0 < ‖Bw.j y‖` using `norm_pos_iff.2 ((map_ne_zero _).2 hy)`. Simplify using `only [hy, false_or, not_le]`. Rewrite using `[one_lt_inv₀ this]) hb)`. Set `σ : Bw.Kw.1 →ₐ[ℚ_[l]] PadicAlgCl l` to `(g : PadicAlgCl l →ₐ[ℚ_[l]] PadicAlgCl l).comp Bw.Kw.1.val`. Conclude with `⟨σ.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split σ), fun x => Subtype.ext (hg x)⟩`.
-/
theorem exists_factor (v : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (hA : IsPlaceOver A v)
    (hj : ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) (b : E →+* Bw.LL.1)
    (hb : ∀ x : 𝓞 E, ‖((b (x : E) : Bw.LL.1) : PadicAlgCl l)‖ < 1 ↔ x ∈ v.asIdeal) :
    ∃ τ : Bw.Kw.1 →ₐ[ℚ_[l]] Bw.LL.1, ∀ x : E, τ ⟨Bw.j (algebraMap E Ω x), Bw.j_E x⟩ = b x := by
  obtain ⟨g, hg⟩ := exists_conj (Bw.j.comp (algebraMap E Ω)) (Bw.LL.1.val.toRingHom.comp b)
    (norm_lt_one_iff v _ _ (fun x => by
      rw [← hA x, ← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or, hj,
        RingHom.comp_apply, map_inv₀, norm_inv]
      generalize algebraMap E Ω (x : E) = y
      by_cases hy : y = 0
      · simp [hy]
      · have : 0 < ‖Bw.j y‖ := norm_pos_iff.2 ((map_ne_zero _).2 hy)
        simp only [hy, false_or, not_le]
        rw [one_lt_inv₀ this]) hb)
  let σ : Bw.Kw.1 →ₐ[ℚ_[l]] PadicAlgCl l := (g : PadicAlgCl l →ₐ[ℚ_[l]] PadicAlgCl l).comp Bw.Kw.1.val
  exact ⟨σ.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split σ), fun x => Subtype.ext (hg x)⟩

end Padic

end GlobalTheory.EmbThroughCompletion
