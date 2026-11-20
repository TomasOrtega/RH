import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BlowUpPushHypothesesExample
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PComponentDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSupSpanMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

universe u

/- English proof (translation)
Introduce `htop`. Establish `h1 : (1 : MRing ι O) ∈ W ⊔ Ideal.span {(C ϖ : MRing ι O)}` using `htop ▸ Submodule.mem_top`. Take `⟨w, hw, t, ht, hwt⟩` from `Submodule.mem_sup.mp h1`. Take `⟨s, rfl⟩` from `Ideal.mem_span_singleton'.mp ht`. Establish `hw0 : (C (coeff 0 w) : MRing ι O) ∈ W`.

Establish `h` using `hW w hw 0`. Rewrite `h` using `[weightedHomogeneousComponent_zero]`. Then use the resulting hypothesis. Introduce `v hv`. Use `congrFun hv v.1` as an intermediate fact. Simplify using `[blockWeight] at this`.

Establish `hc : coeff 0 w = 0`. Establish `h : coeff 0 w ∈ W.comap (C : O →+* MRing ι O)` using `hw0`. Rewrite `h` using `[h0]`. Conclude with `h`. Establish `h2` using `congrArg (coeff 0) hwt`.

Rewrite `h2` using `[coeff_add, mul_comm s, coeff_C_mul, hc, zero_add, coeff_zero_one]`. Conclude with `hϖ (isUnit_iff_exists_inv.mpr ⟨_, h2⟩)`.
-/
theorem sup_span_C_ne_top_of_multiHomog {O : Type*} [CommRing O] {K : Type} [DecidableEq K]
    (ι : K → Type) {W : Ideal (MRing ι O)} (hW : IsMultiHomogIdeal W)
    (h0 : W.comap (C : O →+* MRing ι O) = ⊥) {ϖ : O} (hϖ : ¬ IsUnit ϖ) :
    W ⊔ Ideal.span {(C ϖ : MRing ι O)} ≠ ⊤ := by
  intro htop
  have h1 : (1 : MRing ι O) ∈ W ⊔ Ideal.span {(C ϖ : MRing ι O)} := htop ▸ Submodule.mem_top
  obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp ht
  have hw0 : (C (coeff 0 w) : MRing ι O) ∈ W := by
    have h := hW w hw 0
    rwa [weightedHomogeneousComponent_zero] at h
    intro v hv
    have := congrFun hv v.1
    simp [blockWeight] at this
  have hc : coeff 0 w = 0 := by
    have h : coeff 0 w ∈ W.comap (C : O →+* MRing ι O) := hw0
    rw [h0] at h
    exact h
  have h2 := congrArg (coeff 0) hwt
  rw [coeff_add, mul_comm s, coeff_C_mul, hc, zero_add, coeff_zero_one] at h2
  exact hϖ (isUnit_iff_exists_inv.mpr ⟨_, h2⟩)

/- English proof (translation)
Establish `hWp : W.IsPrime` using `hWmin.1.1`. Establish `hPW : P ≤ W` using `le_sup_left.trans hWmin.1.2`. Establish `hfW : f ∈ W` using `hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))`. Establish `hup` using `ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_add_one_le hPW hfW hfP`. Establish `hq : W.map (Ideal.Quotient.mk P) ∈ (Ideal.span {Ideal.Quotient.mk P f}).minimalPrimes`.

Establish `e : Ideal.span {Ideal.Quotient.mk P f} = (Ideal.span {f}).map (Ideal.Quotient.mk P)`. Rewrite using `[Ideal.map_span, Set.image_singleton]`. Rewrite using `[e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]`. Conclude with `⟨W, hWmin, rfl⟩`. Establish `: (W.map (Ideal.Quotient.mk P)).IsPrime` using `hq.1.1`.

Establish `: (Ideal.span {Ideal.Quotient.mk P f}).IsPrincipal` using `⟨⟨_, rfl⟩⟩`. Establish `hk : (W.map (Ideal.Quotient.mk P)).height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq`. Take `⟨m, hm, hWm'⟩` from `Ideal.exists_le_maximal _ hWϖ`. Establish `hWm : W ≤ m` using `le_sup_left.trans hWm'`. Establish `: m.IsPrime` using `hm.isPrime`.

Establish `hmge` using `le_height_of_isMaximal_of_uniformiser_mem hϖ m hm (hWm' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))`. Establish `hdimS` using `ringKrullDim_mvPolynomial_dvr (σ := Σ k, ι k) O`. Establish `hfin : FiniteRingKrullDim (MRing ι O)`. Rewrite using `[finiteRingKrullDim_iff_ne_bot_and_top, hdimS]`. Conclude with `⟨by rw [← WithBot.coe_natCast]; exact WithBot.coe_ne_bot, by`.

Rewrite using `[← WithBot.coe_natCast]`. Conclude with `ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩`. Establish `hmax : ∀ m' : Ideal (MRing ι O), m'.IsMaximal → m'.height ≤ ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞)`. Introduce `m' hm'`. Use `Ideal.height_le_ringKrullDim_of_ne_top hm'.ne_top` as an intermediate fact.

Rewrite `this` using `[hdimS]`. Conclude with `this` after adjusting the coercions. Establish `hmeq : m.height = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞)` using `le_antisymm (hmax m hm) hmge`. Establish `hcat1` using `DimF.height_eq_height_add_of_isRegularRing P W hPW`. Establish `hcat2` using `DimF.height_eq_height_add_of_isRegularRing W m hWm`.

Establish `hsum : P.height + (W.map (Ideal.Quotient.mk P)).height + (m.map (Ideal.Quotient.mk W)).height = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞)`. Rewrite using `[← hcat1, ← hcat2, hmeq]`. Establish `hPfin : P.height ≠ ⊤` using `fun h => by`. Simplify using `only [h, top_add] at hsum`. Conclude with `ENat.top_ne_natCast _ hsum`.

Establish `hafin : (W.map (Ideal.Quotient.mk P)).height ≠ ⊤` using `fun h => by`. Simplify using `only [h, top_add, add_top] at hsum`. Conclude with `ENat.top_ne_natCast _ hsum`. Establish `hbfin : (m.map (Ideal.Quotient.mk W)).height ≠ ⊤` using `fun h => by`. Simplify using `only [h, add_top] at hsum`.

Conclude with `ENat.top_ne_natCast _ hsum`. Take `⟨h0, hh0⟩ : ∃ h0 : ℕ, P.height = h0` from `⟨_, (ENat.natCast_toNat hPfin).symm⟩`. Take `⟨a0, ha0⟩ : ∃ a0 : ℕ, (W.map (Ideal.Quotient.mk P)).height = a0` from `⟨_, (ENat.natCast_toNat hafin).symm⟩`. Take `⟨b0, hb0⟩ : ∃ b0 : ℕ, (m.map (Ideal.Quotient.mk W)).height = b0` from `⟨_, (ENat.natCast_toNat hbfin).symm⟩`. Rewrite `hsum` using `[hh0, ha0, hb0]`.

Rewrite `hk` using `[ha0]`. Establish `hsum' : h0 + a0 + b0 = Nat.card (Σ k, ι k) + 1` using `by exact_mod_cast hsum`. Establish `hk' : a0 ≤ 1` using `by exact_mod_cast hk`. Establish `hPdim` using `ringKrullDim_quotient_le_sub_height P (Nat.card (Σ k, ι k) + 1) h0 hmax hh0`. Rewrite `hPdim` using `[hdim]`.

Establish `hPdim' : N + 1 ≤ Nat.card (Σ k, ι k) + 1 - h0` using `by exact_mod_cast hPdim`. Establish `hlow` using `Ideal.height_le_ringKrullDim_of_ne_top (DimF.isPrime_map_mk (A := MRing ι O) (q := W) (M := m) hWm).ne_top`. Rewrite `hlow` using `[hb0]`. Establish `hb' : N ≤ b0` using `by omega`. Establish `hlow' : ((N : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ W)` using `le_trans (by exact_mod_cast hb') hlow`.

Rewrite `hup` using `[hdim]`. Conclude with `withBot_eq_of_le_of_add_one_le hlow' hup`.
-/
theorem ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {K : Type} [Fintype K] {ι : K → Type}
    [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι O)} [P.IsPrime] {f : MRing ι O} (hfP : f ∉ P)
    (hWmin : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes)
    (hWϖ : W ⊔ Ideal.span {(C ϖ : MRing ι O)} ≠ ⊤) (N : ℕ)
    (hdim : ringKrullDim (MRing ι O ⧸ P) = ((N + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (MRing ι O ⧸ W) = (N : WithBot ℕ∞) := by
  have hWp : W.IsPrime := hWmin.1.1
  have hPW : P ≤ W := le_sup_left.trans hWmin.1.2
  have hfW : f ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hup := ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_add_one_le hPW hfW hfP

  have hq : W.map (Ideal.Quotient.mk P) ∈ (Ideal.span {Ideal.Quotient.mk P f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk P f} = (Ideal.span {f}).map (Ideal.Quotient.mk P) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨W, hWmin, rfl⟩
  have : (W.map (Ideal.Quotient.mk P)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk P f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hk : (W.map (Ideal.Quotient.mk P)).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq

  obtain ⟨m, hm, hWm'⟩ := Ideal.exists_le_maximal _ hWϖ
  have hWm : W ≤ m := le_sup_left.trans hWm'
  have : m.IsPrime := hm.isPrime
  have hmge := le_height_of_isMaximal_of_uniformiser_mem hϖ m hm
    (hWm' (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  have hdimS := ringKrullDim_mvPolynomial_dvr (σ := Σ k, ι k) O
  have hfin : FiniteRingKrullDim (MRing ι O) := by
    rw [finiteRingKrullDim_iff_ne_bot_and_top, hdimS]
    exact ⟨by rw [← WithBot.coe_natCast]; exact WithBot.coe_ne_bot, by
      rw [← WithBot.coe_natCast]
      exact ne_of_lt (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top _))⟩
  have hmax : ∀ m' : Ideal (MRing ι O), m'.IsMaximal →
      m'.height ≤ ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    intro m' hm'
    have := Ideal.height_le_ringKrullDim_of_ne_top hm'.ne_top
    rw [hdimS] at this
    exact_mod_cast this
  have hmeq : m.height = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := le_antisymm (hmax m hm) hmge

  have hcat1 := DimF.height_eq_height_add_of_isRegularRing P W hPW
  have hcat2 := DimF.height_eq_height_add_of_isRegularRing W m hWm
  have hsum : P.height + (W.map (Ideal.Quotient.mk P)).height + (m.map (Ideal.Quotient.mk W)).height
      = ((Nat.card (Σ k, ι k) + 1 : ℕ) : ℕ∞) := by
    rw [← hcat1, ← hcat2, hmeq]
  have hPfin : P.height ≠ ⊤ := fun h => by
    simp only [h, top_add] at hsum; exact ENat.top_ne_natCast _ hsum
  have hafin : (W.map (Ideal.Quotient.mk P)).height ≠ ⊤ := fun h => by
    simp only [h, top_add, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  have hbfin : (m.map (Ideal.Quotient.mk W)).height ≠ ⊤ := fun h => by
    simp only [h, add_top] at hsum; exact ENat.top_ne_natCast _ hsum
  obtain ⟨h0, hh0⟩ : ∃ h0 : ℕ, P.height = h0 := ⟨_, (ENat.natCast_toNat hPfin).symm⟩
  obtain ⟨a0, ha0⟩ : ∃ a0 : ℕ, (W.map (Ideal.Quotient.mk P)).height = a0 :=
    ⟨_, (ENat.natCast_toNat hafin).symm⟩
  obtain ⟨b0, hb0⟩ : ∃ b0 : ℕ, (m.map (Ideal.Quotient.mk W)).height = b0 :=
    ⟨_, (ENat.natCast_toNat hbfin).symm⟩
  rw [hh0, ha0, hb0] at hsum
  rw [ha0] at hk
  have hsum' : h0 + a0 + b0 = Nat.card (Σ k, ι k) + 1 := by exact_mod_cast hsum
  have hk' : a0 ≤ 1 := by exact_mod_cast hk

  have hPdim := ringKrullDim_quotient_le_sub_height P (Nat.card (Σ k, ι k) + 1) h0 hmax hh0
  rw [hdim] at hPdim
  have hPdim' : N + 1 ≤ Nat.card (Σ k, ι k) + 1 - h0 := by exact_mod_cast hPdim

  have hlow := Ideal.height_le_ringKrullDim_of_ne_top
    (DimF.isPrime_map_mk (A := MRing ι O) (q := W) (M := m) hWm).ne_top
  rw [hb0] at hlow
  have hb' : N ≤ b0 := by omega
  have hlow' : ((N : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ W) :=
    le_trans (by exact_mod_cast hb') hlow
  rw [hdim] at hup
  exact withBot_eq_of_le_of_add_one_le hlow' hup

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP c x hxc hxP W hW hϖW`. Establish `hWd : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W`. Unfold `divCycle at hW`. Use `split_ifs at hW with h`. Conclude with `h`.

Conclude with `absurd rfl hW`. Take `⟨hWmin, hrel⟩` from `hWd`. Establish `hWp : W.IsPrime` using `hWmin.1.1`. Establish `hPp : P.IsPrime` using `hP.multiProj.isPrime`. Establish `hWh : IsMultiHomogIdeal W` using `MinimalPrimeMultiHomog.proof O K ι _ W (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hxc) hWmin`.

Establish `h0 : W.comap (C : O →+* MRing ι O) = ⊥`. Assume the negation of the conclusion as `hne`. Establish `hmx : (W.comap (C : O →+* MRing ι O)).IsMaximal` using `haveI : (W.comap (C : O →+* MRing ι O)).IsPrime := Ideal.IsPrime.comap _ IsPrime.to_maximal_ideal hne`. Establish `hϖm : ϖ ∈ W.comap (C : O →+* MRing ι O)`. Rewrite using `[IsLocalRing.eq_maximalIdeal hmx]`.

Conclude with `(IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit`. Conclude with `hϖW hϖm`. Establish `hdim` using `ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top hϖ hxP hWmin (sup_span_C_ne_top_of_multiHomog ι hWh h0 hϖ.not_isUnit) (d + 1 + Fintype.card K) (by rw [hP.dim, show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by ring])`. Conclude with `⟨⟨hWp, hWh, hrel⟩, h0, hdim⟩`.
-/
theorem HorizontalComponentModel.proof : HorizontalComponentModel.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP c x hxc hxP W hW hϖW
  have hWd : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes ∧ IsRelevant W := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h
    · exact absurd rfl hW
  obtain ⟨hWmin, hrel⟩ := hWd
  have hWp : W.IsPrime := hWmin.1.1
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hWh : IsMultiHomogIdeal W :=
    MinimalPrimeMultiHomog.proof O K ι _ W
      (SupSpanMultiHomog.proof O K ι P x c hP.multiProj.multiHomog hxc) hWmin

  have h0 : W.comap (C : O →+* MRing ι O) = ⊥ := by
    by_contra hne
    have hmx : (W.comap (C : O →+* MRing ι O)).IsMaximal :=
      haveI : (W.comap (C : O →+* MRing ι O)).IsPrime := Ideal.IsPrime.comap _
      IsPrime.to_maximal_ideal hne
    have hϖm : ϖ ∈ W.comap (C : O →+* MRing ι O) := by
      rw [IsLocalRing.eq_maximalIdeal hmx]
      exact (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
    exact hϖW hϖm
  have hdim := ringKrullDim_quotient_eq_of_minimalPrime_of_sup_ne_top hϖ hxP hWmin
    (sup_span_C_ne_top_of_multiHomog ι hWh h0 hϖ.not_isUnit) (d + 1 + Fintype.card K)
    (by rw [hP.dim, show d + 1 + 1 + Fintype.card K = d + 1 + Fintype.card K + 1 by ring])
  exact ⟨⟨hWp, hWh, hrel⟩, h0, hdim⟩

end

end GroundTheory.Heights₂.Heights.NumbersDVR
