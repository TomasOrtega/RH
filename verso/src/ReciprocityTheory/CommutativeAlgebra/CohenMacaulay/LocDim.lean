import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularOfLeHeight

namespace ReciprocityTheory.CA

open IsLocalRing RingTheory.Sequence

/- English proof (translation)
Establish `hmem : ∀ r ∈ rs.map (algebraMap R (Localization.AtPrime P)), r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P)`. Introduce `r hr`. Take `⟨x, hx, rfl⟩` from `List.mem_map.1 hr`. Conclude with `(IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P x).2 (hrs x hx)`. Use `⟨rs.map (algebraMap R (Localization.AtPrime P)), List.length_map _, hmem, reg.of_flat, ?_⟩` and prove the remaining obligations.

Introduce `h`. Establish `hle : Ideal.ofList (rs.map (algebraMap R (Localization.AtPrime P))) ≤ IsLocalRing.maximalIdeal (Localization.AtPrime P)` using `Ideal.span_le.2 fun r hr => hmem r hr`. Rewrite `h` using `[Ideal.smul_eq_mul, Ideal.mul_top]`. Rewrite `hle` using `[← h]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime P)).ne_top (top_le_iff.1 hle)`.
-/
theorem depthGE_localization_of_isWeaklyRegular {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]
    {rs : List R} (hrs : ∀ x ∈ rs, x ∈ P) (reg : IsWeaklyRegular R rs) :
    DepthGE (Localization.AtPrime P) rs.length := by
  have hmem : ∀ r ∈ rs.map (algebraMap R (Localization.AtPrime P)),
      r ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P x).2 (hrs x hx)
  refine ⟨rs.map (algebraMap R (Localization.AtPrime P)), List.length_map _, hmem, reg.of_flat, ?_⟩
  intro h
  have hle : Ideal.ofList (rs.map (algebraMap R (Localization.AtPrime P))) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
    Ideal.span_le.2 fun r hr => hmem r hr
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at h
  rw [← h] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime P)).ne_top (top_le_iff.1 hle)

/- English proof (translation)
Take `⟨ss, hlen, hmem, hreg⟩` from `depthGE_localization_of_isWeaklyRegular Q hrs reg`. Establish `: IsNoetherianRing (Localization.AtPrime Q)` using `IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance`. Establish `e` using `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ss hreg`. Rewrite `e` using `[IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)]`. Establish `hne : Ideal.ofList ss ≠ ⊤`.

Introduce `htop`. Establish `: Ideal.ofList ss ≤ maximalIdeal (Localization.AtPrime Q)`. Rewrite using `[Ideal.ofList, Ideal.span_le]`. Conclude with `fun x hx => hmem x hx`. Conclude with `(maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (htop ▸ this))`.

Establish `: Nontrivial (Localization.AtPrime Q ⧸ Ideal.ofList ss)` using `Ideal.Quotient.nontrivial_iff.mpr hne`. Establish `h0` using `ringKrullDim_nonneg_of_nontrivial (R := Localization.AtPrime Q ⧸ Ideal.ofList ss)`. Establish `: ((ss.length : ℕ) : WithBot ℕ∞) ≤ (Q.height : WithBot ℕ∞)`. Rewrite using `[← e]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← hlen]`. Conclude with `this` after adjusting the coercions.
-/
theorem length_le_height_of_isWeaklyRegular {R : Type*} [CommRing R] [IsNoetherianRing R]
    (Q : Ideal R) [Q.IsPrime] {rs : List R} (hrs : ∀ x ∈ rs, x ∈ Q) (reg : IsWeaklyRegular R rs) :
    (rs.length : ℕ∞) ≤ Q.height := by
  obtain ⟨ss, hlen, hmem, hreg⟩ := depthGE_localization_of_isWeaklyRegular Q hrs reg
  have : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have e := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ss hreg
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q)] at e
  have hne : Ideal.ofList ss ≠ ⊤ := by
    intro htop
    have : Ideal.ofList ss ≤ maximalIdeal (Localization.AtPrime Q) := by
      rw [Ideal.ofList, Ideal.span_le]; exact fun x hx => hmem x hx
    exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (htop ▸ this))
  have : Nontrivial (Localization.AtPrime Q ⧸ Ideal.ofList ss) :=
    Ideal.Quotient.nontrivial_iff.mpr hne
  have h0 := ringKrullDim_nonneg_of_nontrivial (R := Localization.AtPrime Q ⧸ Ideal.ofList ss)
  have : ((ss.length : ℕ) : WithBot ℕ∞) ≤ (Q.height : WithBot ℕ∞) := by
    rw [← e]
    calc ((ss.length : ℕ) : WithBot ℕ∞) = 0 + ss.length := (zero_add _).symm
      _ ≤ _ := add_le_add_left h0 _
  rw [← hlen]
  exact_mod_cast this

variable {R : Type*} [CommRing R] [IsLocalRing R]

/- English proof (translation)
Take `⟨rs, hlen, hmem, hreg⟩` from `h.exists_isRegular_of_le_height (Ideal.IsPrime.ne_top ‹_›) hr`. Substitute `hlen` using the available equality. Conclude with `depthGE_localization_of_isWeaklyRegular P hmem hreg.1`.
-/
theorem IsCM.depthGE_localization_of_le_height (h : IsCM R) (P : Ideal R) [P.IsPrime] {r : ℕ}
    (hr : (r : ℕ∞) ≤ P.height) : DepthGE (Localization.AtPrime P) r := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := h.exists_isRegular_of_le_height (Ideal.IsPrime.ne_top ‹_›) hr
  subst hlen
  exact depthGE_localization_of_isWeaklyRegular P hmem hreg.1

/- English proof (translation)
Use `haveI : IsNoetherianRing R := h.1`. Establish `hfin : P.height ≠ ⊤` using `by first`. Consider the case `exact Ideal.height_ne_top (Ideal.IsPrime.ne_top ‹_›)`. Consider the case `exact (Ideal.height_lt_top (Ideal.IsPrime.ne_top ‹_›)).ne`. Consider the case `exact Ideal.height_ne_top ‹_›`.

Consider the case `(rw [Ideal.IsPrime.height_eq_primeHeight]; exact (Ideal.primeHeight_lt_top P).ne)`. Consider the case `(rw [Ideal.height_eq_primeHeight P]; exact (Ideal.primeHeight_lt_top P).ne)`. Consider the case `exact (Ideal.primeHeight_lt_top P).ne`. Use `⟨inferInstance, P.height.toNat, ?_, h.depthGE_localization_of_le_height P (by rw [ENat.coe_toNat hfin])⟩` and prove the remaining obligations. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]`.

Use `conv_lhs => rw [← ENat.coe_toNat hfin]`. Both sides reduce to the same expression.
-/
theorem IsCM.localization_atPrime (h : IsCM R) (P : Ideal R) [P.IsPrime] :
    IsCM (Localization.AtPrime P) := by
  haveI : IsNoetherianRing R := h.1
  have hfin : P.height ≠ ⊤ := by
    first
    | exact Ideal.height_ne_top (Ideal.IsPrime.ne_top ‹_›)
    | exact (Ideal.height_lt_top (Ideal.IsPrime.ne_top ‹_›)).ne
    | exact Ideal.height_ne_top ‹_›
    | (rw [Ideal.IsPrime.height_eq_primeHeight]; exact (Ideal.primeHeight_lt_top P).ne)
    | (rw [Ideal.height_eq_primeHeight P]; exact (Ideal.primeHeight_lt_top P).ne)
    | exact (Ideal.primeHeight_lt_top P).ne
  refine ⟨inferInstance, P.height.toNat, ?_,
    h.depthGE_localization_of_le_height P (by rw [ENat.coe_toNat hfin])⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)]
  conv_lhs => rw [← ENat.coe_toNat hfin]
  rfl

/- English proof (translation)
Establish `hN : IsNoetherianRing R` using `h.1`. Establish `hPt : P ≠ ⊤` using `Ideal.IsPrime.ne_top ‹_›`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp (P.height_ne_top hPt)`. Take `⟨rs, hlen, hmem, hreg⟩` from `h.exists_isRegular_of_le_height hPt hn.le`. Establish `hmax : ∀ x ∈ rs, x ∈ maximalIdeal R` using `fun x hx => le_maximalIdeal hPt (hmem x hx)`.

Establish `hJP : Ideal.ofList rs ≤ P`. Rewrite using `[Ideal.ofList, Ideal.span_le]`. Conclude with `fun x hx => hmem x hx`. Establish `hht : P.height ≤ (Ideal.ofList rs).height`. Rewrite using `[(Ideal.ofList rs).height_eq_inf_minimalPrimes]`.

Use `le_iInf₂ fun Q hQ => ?_` and prove the remaining obligations. Use `hQ.isPrime` as an intermediate fact. Rewrite using `[← hn, ← hlen]`. Conclude with `length_le_height_of_isWeaklyRegular Q (fun x hx => hQ.1.2 (Ideal.subset_span hx)) hreg.1`. Establish `hPmin : P ∈ (Ideal.ofList rs).minimalPrimes` using `Ideal.mem_minimalPrimes_of_height_le hJP hht`.

Establish `hCM : IsCMMod R (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R))` using `(isCM_iff_isCMMod.mp h).quotient_ofList hmax hreg`. Establish `hJ : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs` using `by simp`. Establish `hann : Module.annihilator R (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs`. Rewrite using `[hJ, Ideal.annihilator_quotient]`. Establish `hass : P ∈ associatedPrimes R (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R))`.

Rewrite using `[hCM.associatedPrimes_eq_minimalPrimes, hann]`. Conclude with `hPmin`. Establish `e1` using `hCM.ringKrullDim_quotient_eq_supportDim hass`. Establish `e2` using `Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg`. Rewrite `e2` using `[Module.supportDim_self_eq_ringKrullDim]`.

Rewrite using `[e1, ← e2, ← hn, ← hlen, add_comm]`. Both sides reduce to the same expression.
-/
theorem IsCM.height_add_ringKrullDim_quotient (h : IsCM R) (P : Ideal R) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (R ⧸ P) = ringKrullDim R := by
  have hN : IsNoetherianRing R := h.1
  have hPt : P ≠ ⊤ := Ideal.IsPrime.ne_top ‹_›
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (P.height_ne_top hPt)
  obtain ⟨rs, hlen, hmem, hreg⟩ := h.exists_isRegular_of_le_height hPt hn.le
  have hmax : ∀ x ∈ rs, x ∈ maximalIdeal R := fun x hx => le_maximalIdeal hPt (hmem x hx)
  have hJP : Ideal.ofList rs ≤ P := by
    rw [Ideal.ofList, Ideal.span_le]; exact fun x hx => hmem x hx
  have hht : P.height ≤ (Ideal.ofList rs).height := by
    rw [(Ideal.ofList rs).height_eq_inf_minimalPrimes]
    refine le_iInf₂ fun Q hQ => ?_
    have := hQ.isPrime
    rw [← hn, ← hlen]
    exact length_le_height_of_isWeaklyRegular Q
      (fun x hx => hQ.1.2 (Ideal.subset_span hx)) hreg.1
  have hPmin : P ∈ (Ideal.ofList rs).minimalPrimes := Ideal.mem_minimalPrimes_of_height_le hJP hht
  have hCM : IsCMMod R (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R)) :=
    (isCM_iff_isCMMod.mp h).quotient_ofList hmax hreg
  have hJ : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs := by simp
  have hann : Module.annihilator R (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R)) =
      Ideal.ofList rs := by
    rw [hJ, Ideal.annihilator_quotient]
  have hass : P ∈ associatedPrimes R (R ⧸ Ideal.ofList rs • (⊤ : Submodule R R)) := by
    rw [hCM.associatedPrimes_eq_minimalPrimes, hann]; exact hPmin
  have e1 := hCM.ringKrullDim_quotient_eq_supportDim hass
  have e2 := Module.supportDim_add_length_eq_supportDim_of_isRegular rs hreg
  rw [Module.supportDim_self_eq_ringKrullDim] at e2
  rw [e1, ← e2, ← hn, ← hlen, add_comm]
  rfl

end ReciprocityTheory.CA
