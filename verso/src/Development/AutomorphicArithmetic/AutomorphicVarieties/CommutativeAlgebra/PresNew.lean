import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PreservedCoefficient

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

/- English proof (translation)
Establish `hI : MvPolynomial.idealOfVars σ R ≤ m.comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom)`. Rewrite using `[MvPolynomial.idealOfVars, Ideal.span_le]`. Introduce and unpack `_ ⟨s, rfl⟩`. Simplify using `using hF s`. Establish `hIn : MvPolynomial.idealOfVars σ R ^ n ≤ (m ^ n).comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom)` using `(Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)`.

Set `e` to `toAdicCompletionAlgEquiv σ R`. Establish `key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R) (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), F (e.symm y) ∈ m ^ n`. Introduce `y hy`. Use `Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def, map_mul]`.

Conclude with `Ideal.mul_mem_right _ _ (hIn hp)`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem ha hb`. Establish `h` using `key (e (g - (truncTotal n g : MvPolynomial σ R))) (by`. Rewrite using `[AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R), LinearMap.mem_ker, AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]`.

Establish `: truncTotal n (g - ((truncTotal n g : MvPolynomial σ R) : MvPowerSeries σ R)) = 0`. Use extensionality with `x`. Rewrite using `[coeff_truncTotal_eq_ite]`. Use `split_ifs with hx`. Rewrite using `[map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx]`.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[this]`. Use the proof step `rfl)`. Rewrite `h` using `[AlgEquiv.symm_apply_apply, map_sub]`. Then use the resulting hypothesis.
-/
private theorem pres_new_low {R S σ : Type} [CommRing R] [CommRing S] [Finite σ] (m : Ideal S)
    (F : MvPowerSeries σ R →+* S) (hF : ∀ s, F (X s) ∈ m) (n : ℕ) (g : MvPowerSeries σ R) :
    F g - F (truncTotal n g : MvPolynomial σ R) ∈ m ^ n := by
  have hI : MvPolynomial.idealOfVars σ R ≤ m.comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    simpa using hF s
  have hIn : MvPolynomial.idealOfVars σ R ^ n ≤
      (m ^ n).comap (F.comp MvPolynomial.coeToMvPowerSeries.ringHom) :=
    (Ideal.pow_right_mono hI n).trans (Ideal.le_comap_pow _ n)
  let e := toAdicCompletionAlgEquiv σ R
  have key : ∀ y ∈ (MvPolynomial.idealOfVars σ R ^ n • ⊤ : Submodule (MvPolynomial σ R)
      (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R))), F (e.symm y) ∈ m ^ n := by
    intro y hy
    refine Submodule.smul_induction_on hy (fun p hp z _ => ?_) (fun a b ha hb => ?_)
    · rw [map_smul, Algebra.smul_def, map_mul]
      exact Ideal.mul_mem_right _ _ (hIn hp)
    · rw [map_add, map_add]; exact add_mem ha hb
  have h := key (e (g - (truncTotal n g : MvPolynomial σ R))) (by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (MvPolynomial.idealOfVars_fg σ R), LinearMap.mem_ker,
      AdicCompletion.eval_apply, toAdicCompletionAlgEquiv_apply, toAdicCompletion_apply_eq_mk_truncTotal]
    have : truncTotal n (g - ((truncTotal n g : MvPolynomial σ R) : MvPowerSeries σ R)) = 0 := by
      ext x
      rw [coeff_truncTotal_eq_ite]
      split_ifs with hx
      · rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ hx]; simp
      · simp
    rw [this]
    rfl)
  rwa [AlgEquiv.symm_apply_apply, map_sub] at h

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.PreservedCoefficient.pres_new_coeff N`.
-/
private theorem pres_new_coeff {O σ : Type} [CommRing O] [IsLocalRing O] (N : ℕ) :
    ∀ h ∈ maximalIdeal (MvPowerSeries σ O) ^ N, ∀ a : σ →₀ ℕ,
      coeff a h ∈ maximalIdeal O ^ (N - a.degree) :=
  _root_.UpperTheory.Reformulated.B.PreservedCoefficient.pres_new_coeff N

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[coeff_wcomp]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[if_pos rfl]`.

Use `split_ifs with h1`. Both sides reduce to the same expression. Conclude with `(hh a h1).symm`. Rewrite using `[if_neg hij] split_ifs with h1`. Rewrite using `[map_zero]`.

Conclude with `hh a (h1 ▸ Ne.symm hij)`. Simplify using the standard rewrite rules.
-/
private theorem pres_new_wcomp {O σ X : Type} [CommRing O] [AddCommGroup X] [DecidableEq X] (wt : σ → X)
    {i : X} (j : X) {h : MvPowerSeries σ O} (hh : h ∈ wtPart O wt i) :
    wcomp O wt j h = if i = j then h else 0 := by
  ext a
  rw [coeff_wcomp]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    split_ifs with h1
    · rfl
    · exact (hh a h1).symm
  · rw [if_neg hij]
    split_ifs with h1
    · rw [map_zero]
      exact hh a (h1 ▸ Ne.symm hij)
    · simp

/- English proof (translation)
Proceed by induction on `u using Finsupp.induction_linear with`. Consider the case `zero => simpa using one_mem_wtPart O w`. Consider the case `add u v hu hv`. Establish `: (monomial (u + v) 1 : MvPowerSeries τ O) = monomial u 1 * monomial v 1`. Rewrite using `[monomial_mul_monomial, one_mul]`.

Rewrite using `[this, map_mul, map_add]`. Conclude with `mul_mem_wtPart O w hu hv`. Consider the case `single s n`. Rewrite using `[← X_pow_eq, map_pow, Finsupp.weight_single]`. Conclude with `SetLike.pow_mem_graded n (hΦ s)`.
-/
private theorem pres_new_mono {O σ τ Y : Type} [CommRing O] [AddCommGroup Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s))
    (u : τ →₀ ℕ) : Φ (monomial u 1) ∈ wtPart O w (Finsupp.weight wt u) := by
  induction u using Finsupp.induction_linear with
  | zero => simpa using one_mem_wtPart O w
  | add u v hu hv =>
    have : (monomial (u + v) 1 : MvPowerSeries τ O) = monomial u 1 * monomial v 1 := by
      rw [monomial_mul_monomial, one_mul]
    rw [this, map_mul, map_add]
    exact mul_mem_wtPart O w hu hv
  | single s n =>
    rw [← X_pow_eq, map_pow, Finsupp.weight_single]
    exact SetLike.pow_mem_graded n (hΦ s)

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial u c`. Establish `: ((MvPolynomial.monomial u c : MvPolynomial τ O) : MvPowerSeries τ O) = c • monomial u 1`. Rewrite using `[MvPolynomial.coe_monomial, ← map_smul, smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul, map_smul, map_smul, map_smul, pres_new_wcomp w j (pres_new_mono wt w Φ hΦ u), pres_new_wcomp wt j (h := monomial u 1) (pres_new_mono wt wt (AlgHom.id O _) (X_mem_wtPart O wt) u)]`.

Apply the tactic sequence `split_ifs <;> simp`. Consider the case `add p q hp hq => simp only [MvPolynomial.coe_add, map_add, hp, hq]`.
-/
private theorem pres_new_poly {O σ τ Y : Type} [CommRing O] [AddCommGroup Y] [DecidableEq Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s)) (j : Y)
    (p : MvPolynomial τ O) : Φ (wcomp O wt j p) = wcomp O w j (Φ p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u c =>
    have : ((MvPolynomial.monomial u c : MvPolynomial τ O) : MvPowerSeries τ O) = c • monomial u 1 := by
      rw [MvPolynomial.coe_monomial, ← map_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, map_smul, map_smul, map_smul, pres_new_wcomp w j (pres_new_mono wt w Φ hΦ u),
      pres_new_wcomp wt j (h := monomial u 1) (pres_new_mono wt wt (AlgHom.id O _) (X_mem_wtPart O wt) u)]
    split_ifs <;> simp
  | add p q hp hq => simp only [MvPolynomial.coe_add, map_add, hp, hq]

/- English proof (translation)
Establish `hl` using `pres_new_low (maximalIdeal (MvPowerSeries σ O)) (Φ : MvPowerSeries τ O →+* MvPowerSeries σ O) hm`. Use extensionality with `a`. Rewrite using `[← sub_eq_zero]`. Use `IsHausdorff.haus (I := maximalIdeal O) inferInstance _ fun k => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`.

Establish `h1` using `pres_new_coeff _ _ (hl (k + a.degree) g) a`. Establish `h2` using `pres_new_coeff _ _ (hl (k + a.degree) (wcomp O wt j g)) a`. Establish `h3 : ((truncTotal (k + a.degree) (wcomp O wt j g) : MvPolynomial τ O) : MvPowerSeries τ O) = wcomp O wt j (truncTotal (k + a.degree) g : MvPolynomial τ O)`. Use extensionality with `b`. Simplify using `only [coeff_wcomp, MvPolynomial.coeff_coe, coeff_truncTotal_eq_ite]`.

Apply the tactic sequence `split_ifs <;> rfl`. Rewrite `h2` using `[h3]`. Simplify using `only [RingHom.coe_coe, Nat.add_sub_cancel, map_sub] at h1 h2`. Rewrite `h2` using `[pres_new_poly wt w Φ hΦ]`. Rewrite `h2`, the goal using `[coeff_wcomp]`.

Use `split_ifs at h2 ⊢`. Simplify using `using sub_mem h2 h1`. Conclude with `h2`.
-/
private theorem pres_new_comm {O σ τ Y : Type} [CommRing O] [IsLocalRing O] [IsHausdorff (maximalIdeal O) O]
    [Finite τ] [AddCommGroup Y] [DecidableEq Y] (wt : τ → Y) (w : σ → Y)
    (Φ : MvPowerSeries τ O →ₐ[O] MvPowerSeries σ O) (hΦ : ∀ s, Φ (X s) ∈ wtPart O w (wt s))
    (hm : ∀ s, Φ (X s) ∈ maximalIdeal (MvPowerSeries σ O)) (j : Y)
    (g : MvPowerSeries τ O) : Φ (wcomp O wt j g) = wcomp O w j (Φ g) := by
  have hl := pres_new_low (maximalIdeal (MvPowerSeries σ O)) (Φ : MvPowerSeries τ O →+* MvPowerSeries σ O) hm
  ext a
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := maximalIdeal O) inferInstance _ fun k => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  have h1 := pres_new_coeff _ _ (hl (k + a.degree) g) a
  have h2 := pres_new_coeff _ _ (hl (k + a.degree) (wcomp O wt j g)) a
  have h3 : ((truncTotal (k + a.degree) (wcomp O wt j g) : MvPolynomial τ O) : MvPowerSeries τ O) =
      wcomp O wt j (truncTotal (k + a.degree) g : MvPolynomial τ O) := by
    ext b
    simp only [coeff_wcomp, MvPolynomial.coeff_coe, coeff_truncTotal_eq_ite]
    split_ifs <;> rfl
  rw [h3] at h2
  simp only [RingHom.coe_coe, Nat.add_sub_cancel, map_sub] at h1 h2
  rw [pres_new_poly wt w Φ hΦ] at h2
  rw [coeff_wcomp] at h2 ⊢
  split_ifs at h2 ⊢
  · simpa using sub_mem h2 h1
  · exact h2

/- English proof (translation)
Introduce `O _ _ _ _ Y _ _ _ _ R _ _ _ W _ τ _ wt z hz hgen`. Use `haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O W.σ`. Use `haveI : IsCO O (MvPowerSeries τ O) := co_mvps O O τ`. Use `choose f hf hfz using fun s => (hz s).2`. Establish `hfz' : ∀ s, W.π (f s) = z s` using `hfz`.

Establish `hfm : ∀ s, f s ∈ maximalIdeal (MvPowerSeries W.σ O)` using `fun s hu => (hz s).1 (hfz' s ▸ hu.map W.π)`. Take `⟨Φ, ⟨-, hΦ⟩, -⟩` from `co_ev O O (MvPowerSeries W.σ O) τ (Algebra.ofId _ _) f hfm`. Establish `hF : ∀ s, (W.π.comp Φ) (X s) = z s` using `fun s => by rw [AlgHom.comp_apply, hΦ, hfz']`. Use `⟨⟨τ, wt, W.π.comp Φ, ?_, ?_⟩, Equiv.refl _, fun s => ⟨hF s, rfl⟩⟩` and prove the remaining obligations. Use `co_surj O _ R _ (hgen.trans (sup_le_sup_right (sup_le ?_ ?_) _))` and prove the remaining obligations.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨s, rfl⟩`. Rewrite using `[← hF s]`. Use `Ideal.mem_map_of_mem _ fun hu => ?_` and prove the remaining obligations. Simplify using `using isUnit_constantCoeff _ hu`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `c hc`. Rewrite using `[Ideal.mem_comap, ← (W.π.comp Φ).commutes]`. Use `Ideal.mem_map_of_mem _ fun hu => hc ?_` and prove the remaining obligations. Simplify `isUnit_constantCoeff _ hu` using `[MvPowerSeries.algebraMap_apply]`.

Introduce `g hg j show W.π (Φ _) = 0`. Rewrite using `[pres_new_comm wt W.wt Φ (fun s => hΦ s ▸ hf s) (fun s => hΦ s ▸ hfm s)]`. Conclude with `W.homog _ hg j`.
-/
theorem UpperTheory.V.Alg.pres_new :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R), (∀ s, W.z s ∈ maximalIdeal R) → ∀ (τ : Type) [Fintype τ] (wt : τ → X) (z : τ → R), (∀ s, z s ∈ maximalIdeal R ∧ z s ∈ W.part (wt s)) →
      maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ (maximalIdeal O).map (algebraMap O R) ⊔ maximalIdeal R ^ 2 →
      ∃ (W' : WPres O X R) (e : τ ≃ W'.σ), ∀ s, W'.z (e s) = z s ∧ W'.wt (e s) = wt s := by
  intro O _ _ _ _ Y _ _ _ _ R _ _ _ W _ τ _ wt z hz hgen
  haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O W.σ
  haveI : IsCO O (MvPowerSeries τ O) := co_mvps O O τ
  choose f hf hfz using fun s => (hz s).2
  have hfz' : ∀ s, W.π (f s) = z s := hfz
  have hfm : ∀ s, f s ∈ maximalIdeal (MvPowerSeries W.σ O) := fun s hu =>
    (hz s).1 (hfz' s ▸ hu.map W.π)
  obtain ⟨Φ, ⟨-, hΦ⟩, -⟩ := co_ev O O (MvPowerSeries W.σ O) τ (Algebra.ofId _ _) f hfm
  have hF : ∀ s, (W.π.comp Φ) (X s) = z s := fun s => by rw [AlgHom.comp_apply, hΦ, hfz']
  refine ⟨⟨τ, wt, W.π.comp Φ, ?_, ?_⟩, Equiv.refl _, fun s => ⟨hF s, rfl⟩⟩
  · refine co_surj O _ R _ (hgen.trans (sup_le_sup_right (sup_le ?_ ?_) _))
    · rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      rw [← hF s]
      refine Ideal.mem_map_of_mem _ fun hu => ?_
      simpa using isUnit_constantCoeff _ hu
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      rw [Ideal.mem_comap, ← (W.π.comp Φ).commutes]
      refine Ideal.mem_map_of_mem _ fun hu => hc ?_
      simpa [MvPowerSeries.algebraMap_apply] using isUnit_constantCoeff _ hu
  · intro g hg j
    show W.π (Φ _) = 0
    rw [pres_new_comm wt W.wt Φ (fun s => hΦ s ▸ hf s) (fun s => hΦ s ▸ hfm s)]
    exact W.homog _ hg j
