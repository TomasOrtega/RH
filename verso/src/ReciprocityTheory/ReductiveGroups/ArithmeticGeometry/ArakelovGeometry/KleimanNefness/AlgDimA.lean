import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AlgDimSt
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import ReciprocityTheory.CommutativeAlgebra.WeakRegularity.RingKrullDimQuotientAddOneLeOfLt
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.LocDim
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bridge
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.DimFormulaOfSurjective

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal

open ReciprocityTheory.CA

/- English proof (translation)
Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => exact absurd rfl hx`. Consider the case `coe a`. Proceed by induction on `y using WithBot.recBotCoe with`. Consider the case `bot => exact absurd h (by simp)`.

Consider the case `coe b`. Normalize the coercions in `at h hxn ⊢`. Proceed by induction on `a using ENat.recTopCoe with`. Consider the case `top => exact absurd hxn (by simp)`. Consider the case `coe a`.

Proceed by induction on `b using ENat.recTopCoe with`. Consider the case `top => exact WithTop.coe_lt_top a`. Consider the case `coe b`. Normalize the coercions in `at h ⊢`.
-/
theorem lt_of_add_one_le_fin (x y : WithBot ℕ∞) (n : ℕ) (hx : x ≠ ⊥) (hxn : x ≤ n)
    (h : x + 1 ≤ y) : x < y := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl hx
  | coe a =>
  induction y using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe b =>
  norm_cast at h hxn ⊢
  induction a using ENat.recTopCoe with
  | top => exact absurd hxn (by simp)
  | coe a =>
  induction b using ENat.recTopCoe with
  | top => exact WithTop.coe_lt_top a
  | coe b =>
  norm_cast at h ⊢

/- English proof (translation)
Establish `: Nontrivial (R ⧸ I)` using `Ideal.Quotient.nontrivial_iff.mpr hI`. Conclude with `ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial`.
-/
theorem ringKrullDim_quotient_ne_bot {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    ringKrullDim (R ⧸ I) ≠ ⊥ := by
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  exact ne_bot_of_le_ne_bot (by simp) ringKrullDim_nonneg_of_nontrivial

/- English proof (translation)
Introduce `F _ σ _ V W hV hW hVW`. Establish `h1` using `ReciprocityTheory.CA.Link.ringKrullDim_quotient_add_one_le_of_lt hVW`. Establish `h2 : ringKrullDim (MvPolynomial σ F ⧸ W) ≤ (Fintype.card σ : ℕ)`. Use `(ringKrullDim_quotient_le W).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card, zero_add]`.

Conclude with `lt_of_add_one_le_fin _ _ _ (ringKrullDim_quotient_ne_bot W hW.ne_top) h2 h1`.
-/
theorem dimLt' : DimLtStatement := by
  intro F _ σ _ V W hV hW hVW
  have h1 := ReciprocityTheory.CA.Link.ringKrullDim_quotient_add_one_le_of_lt hVW
  have h2 : ringKrullDim (MvPolynomial σ F ⧸ W) ≤ (Fintype.card σ : ℕ) := by
    refine (ringKrullDim_quotient_le W).trans (le_of_eq ?_)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, zero_add]
  exact lt_of_add_one_le_fin _ _ _ (ringKrullDim_quotient_ne_bot W hW.ne_top) h2 h1

/- English proof (translation)
Establish `hdisj : Disjoint (𝔐.primeCompl : Set S) (W : Set S)` using `Set.disjoint_left.mpr fun x hx hxp => hx (hle hxp)`. Set `p` to `W.map (algebraMap S (Localization.AtPrime 𝔐))`. Establish `: p.IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint 𝔐.primeCompl _ W inferInstance hdisj`. Establish `hc : p.comap (algebraMap S (Localization.AtPrime 𝔐)) = W` using `IsLocalization.under_map_of_isPrime_disjoint 𝔐.primeCompl _ (I := W) inferInstance hdisj`. Establish `h2` using `h.localization_atPrime p`.

Establish `: IsLocalization W.primeCompl (Localization.AtPrime p)`. Establish `h0 : IsLocalization (p.comap (algebraMap S (Localization.AtPrime 𝔐))).primeCompl (Localization.AtPrime p)` using `inferInstance`. Use `h0 using 2` and compare the differences between its conclusion and the goal. Rewrite using `[hc]`. Set `e` to `IsLocalization.algEquiv W.primeCompl (Localization.AtPrime W) (Localization.AtPrime p)`.

Conclude with `h2.of_ringEquiv e.symm.toRingEquiv`.
-/
theorem isCM_atPrime_of_le {S : Type*} [CommRing S] (𝔐 W : Ideal S) [𝔐.IsPrime] [W.IsPrime]
    (h : IsCM (Localization.AtPrime 𝔐)) (hle : W ≤ 𝔐) : IsCM (Localization.AtPrime W) := by
  have hdisj : Disjoint (𝔐.primeCompl : Set S) (W : Set S) :=
    Set.disjoint_left.mpr fun x hx hxp => hx (hle hxp)
  let p := W.map (algebraMap S (Localization.AtPrime 𝔐))
  have : p.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔐.primeCompl _ W inferInstance hdisj
  have hc : p.comap (algebraMap S (Localization.AtPrime 𝔐)) = W :=
    IsLocalization.under_map_of_isPrime_disjoint 𝔐.primeCompl _ (I := W) inferInstance hdisj
  have h2 := h.localization_atPrime p
  have : IsLocalization W.primeCompl (Localization.AtPrime p) := by
    have h0 : IsLocalization (p.comap (algebraMap S (Localization.AtPrime 𝔐))).primeCompl
        (Localization.AtPrime p) := inferInstance
    convert h0 using 2
    rw [hc]
  let e := IsLocalization.algEquiv W.primeCompl (Localization.AtPrime W) (Localization.AtPrime p)
  exact h2.of_ringEquiv e.symm.toRingEquiv

/- English proof (translation)
Establish `hWp : W.IsPrime` using `hW.1.1`. Establish `hVW : V ≤ W` using `le_sup_left.trans hW.1.2`. Establish `hsW : s ∈ W` using `hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))`. Take `⟨𝔐, h𝔐, hW𝔐⟩` from `Ideal.exists_le_maximal W hWp.ne_top`. Establish `hCM` using `(height_maximal_mvPolynomial_field F N 𝔐).1`.

Establish `hCMW` using `isCM_atPrime_of_le 𝔐 W hCM hW𝔐`. Establish `hrel` using `height_eq_add_of_isCM_localization W V hCMW hVW`. Set `f` to `Ideal.Quotient.mk V`. Establish `hf : Function.Surjective f` using `Ideal.Quotient.mk_surjective`. Establish `hker : RingHom.ker f ≤ W` using `by rw [Ideal.mk_ker]; exact hVW`.

Establish `hP : (W.map f).IsPrime` using `Ideal.map_isPrime_of_surjective hf hker`. Establish `hcomapJ : (Ideal.span {f s}).comap f = V ⊔ Ideal.span {s}`. Rewrite using `[← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective _ hf, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]`. Establish `hmin : W.map f ∈ (Ideal.span {f s}).minimalPrimes`. Establish `h0` using `hW`.

Rewrite `h0` using `[← hcomapJ, Ideal.comap_minimalPrimes_eq_of_surjective hf]`. Take `⟨Q, hQ, hQW⟩` from `h0`. Rewrite using `[← hQW, Ideal.map_comap_of_surjective _ hf]`. Conclude with `hQ`. Establish `: (Ideal.span {f s}).IsPrincipal` using `⟨⟨f s, rfl⟩⟩`.

Establish `hle1 : (W.map f).height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin`. Establish `hne : W.map f ≠ ⊥`. Introduce `h0`. Establish `h3 : f s ∈ W.map f` using `Ideal.mem_map_of_mem f hsW`. Rewrite `h3` using `[h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hs h3`. Establish `hge1 : 1 ≤ (W.map f).height`. Rewrite using `[Order.one_le_iff_ne_zero]`. Conclude with `fun h0 => hne (Ideal.height_eq_zero_iff_eq_bot.mp h0)`. Establish `h1 : (W.map f).height = 1` using `le_antisymm hle1 hge1`.

Establish `eV` using `height_add_ringKrullDim_quotient_mvPolynomial_field F N V`. Establish `eW` using `height_add_ringKrullDim_quotient_mvPolynomial_field F N W`. Rewrite `eW` using `[hrel, h1]`. Use `dimFormula_arith V.height 1 _ _ N (ringKrullDim_quotient_ne_bot W hWp.ne_top) (ringKrullDim_quotient_ne_bot V hV.ne_top) eW eV` as an intermediate fact. Rewrite using `[add_comm]`.

Conclude with `this` after adjusting the coercions.
-/
theorem dimPIT_fin (F : Type) [Field F] (N : ℕ) (V W : Ideal (MvPolynomial (Fin N) F))
    (s : MvPolynomial (Fin N) F) (hV : V.IsPrime) (hs : s ∉ V)
    (hW : W ∈ (V ⊔ Ideal.span {s}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin N) F ⧸ W) + 1 =
      ringKrullDim (MvPolynomial (Fin N) F ⧸ V) := by
  have hWp : W.IsPrime := hW.1.1
  have hVW : V ≤ W := le_sup_left.trans hW.1.2
  have hsW : s ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  obtain ⟨𝔐, h𝔐, hW𝔐⟩ := Ideal.exists_le_maximal W hWp.ne_top
  have hCM := (height_maximal_mvPolynomial_field F N 𝔐).1
  have hCMW := isCM_atPrime_of_le 𝔐 W hCM hW𝔐
  have hrel := height_eq_add_of_isCM_localization W V hCMW hVW
  let f := Ideal.Quotient.mk V
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ W := by rw [Ideal.mk_ker]; exact hVW
  have hP : (W.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have hcomapJ : (Ideal.span {f s}).comap f = V ⊔ Ideal.span {s} := by
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective _ hf,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_comm]
  have hmin : W.map f ∈ (Ideal.span {f s}).minimalPrimes := by
    have h0 := hW
    rw [← hcomapJ, Ideal.comap_minimalPrimes_eq_of_surjective hf] at h0
    obtain ⟨Q, hQ, hQW⟩ := h0
    rw [← hQW, Ideal.map_comap_of_surjective _ hf]
    exact hQ
  have : (Ideal.span {f s}).IsPrincipal := ⟨⟨f s, rfl⟩⟩
  have hle1 : (W.map f).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have hne : W.map f ≠ ⊥ := by
    intro h0
    have h3 : f s ∈ W.map f := Ideal.mem_map_of_mem f hsW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h3
    exact hs h3
  have hge1 : 1 ≤ (W.map f).height := by
    rw [Order.one_le_iff_ne_zero]
    exact fun h0 => hne (Ideal.height_eq_zero_iff_eq_bot.mp h0)
  have h1 : (W.map f).height = 1 := le_antisymm hle1 hge1
  have eV := height_add_ringKrullDim_quotient_mvPolynomial_field F N V
  have eW := height_add_ringKrullDim_quotient_mvPolynomial_field F N W
  rw [hrel, h1] at eW
  have := dimFormula_arith V.height 1 _ _ N (ringKrullDim_quotient_ne_bot W hWp.ne_top)
    (ringKrullDim_quotient_ne_bot V hV.ne_top) eW eV
  rw [add_comm]
  exact_mod_cast this

/- English proof (translation)
Introduce `F _ σ _ V W s hV hs hW`. Set `e : MvPolynomial σ F ≃+* MvPolynomial (Fin (Fintype.card σ)) F` to `(MvPolynomial.renameEquiv F (Fintype.equivFin σ)).toRingEquiv`. Set `g : MvPolynomial (Fin (Fintype.card σ)) F →+* MvPolynomial σ F` to `e.symm`. Set `eh : MvPolynomial σ F →+* MvPolynomial (Fin (Fintype.card σ)) F` to `e`. Establish `hcm : ∀ I : Ideal (MvPolynomial σ F), I.comap g = I.map eh` using `fun I => Ideal.comap_symm e`.

Establish `hV' : (V.map eh).IsPrime`. Establish `h0 : (V.comap g).IsPrime` using `Ideal.comap_isPrime g V`. Rewrite `h0` using `[hcm]`. Then use the resulting hypothesis. Establish `hs' : eh s ∉ V.map eh`. Rewrite using `[← hcm, Ideal.mem_comap]`.

Simplify `hs` using `[g, eh]`. Establish `key` using `Ideal.comap_minimalPrimes_eq_of_surjective (f := g) e.symm.surjective (V ⊔ Ideal.span {s})`. Establish `hmem : W.comap g ∈ ((V ⊔ Ideal.span {s}).comap g).minimalPrimes` using `key ▸ ⟨W, hW, rfl⟩`. Rewrite `hmem` using `[hcm, hcm, Ideal.map_sup, Ideal.map_span, Set.image_singleton]`. Use `dimPIT_fin F _ _ _ _ hV' hs' hmem` as an intermediate fact.

Rewrite using `[ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv W _ e rfl), ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V _ e rfl)]`. Conclude with `this`.
-/
theorem dimPIT' : DimPITStatement := by
  intro F _ σ _ V W s hV hs hW
  let e : MvPolynomial σ F ≃+* MvPolynomial (Fin (Fintype.card σ)) F :=
    (MvPolynomial.renameEquiv F (Fintype.equivFin σ)).toRingEquiv
  let g : MvPolynomial (Fin (Fintype.card σ)) F →+* MvPolynomial σ F := e.symm
  let eh : MvPolynomial σ F →+* MvPolynomial (Fin (Fintype.card σ)) F := e
  have hcm : ∀ I : Ideal (MvPolynomial σ F), I.comap g = I.map eh := fun I => Ideal.comap_symm e
  have hV' : (V.map eh).IsPrime := by
    have h0 : (V.comap g).IsPrime := Ideal.comap_isPrime g V
    rwa [hcm] at h0
  have hs' : eh s ∉ V.map eh := by
    rw [← hcm, Ideal.mem_comap]
    simpa [g, eh] using hs
  have key := Ideal.comap_minimalPrimes_eq_of_surjective (f := g) e.symm.surjective
    (V ⊔ Ideal.span {s})
  have hmem : W.comap g ∈ ((V ⊔ Ideal.span {s}).comap g).minimalPrimes := key ▸ ⟨W, hW, rfl⟩
  rw [hcm, hcm, Ideal.map_sup, Ideal.map_span, Set.image_singleton] at hmem
  have := dimPIT_fin F _ _ _ _ hV' hs' hmem
  rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv W _ e rfl),
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V _ e rfl)]
  exact this

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KrullDimensionPrincipalIdeal
