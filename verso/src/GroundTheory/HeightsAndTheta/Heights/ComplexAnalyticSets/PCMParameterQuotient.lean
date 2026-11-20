import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMParameterQuotient
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMRegularElement
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.CMDepthAssoc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

/- English proof (translation)
Establish `: Nontrivial C` using `e.injective.nontrivial`. Establish `: IsLocalRing C` using `IsLocalRing.of_surjective' e.toRingHom e.surjective`. Establish `: IsNoetherianRing C` using `isNoetherianRing_of_ringEquiv A e`. Take `⟨rs, hm, hreg, hdim⟩` from `IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)`. Use `{ exists_isWeaklyRegular := ⟨rs.map e, ?_, ?_, ?_⟩ }` and prove the remaining obligations.

Introduce `r hr`. Take `⟨s, hs, rfl⟩` from `List.mem_map.1 hr`. Establish `hs'` using `hm s hs`. Rewrite `hs'`, the goal using `[mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun h => hs' (by simpa using h.map e.symm)`.

Use `RingHomInvPair.of_ringEquiv e` as an intermediate fact. Use `RingHomInvPair.symm (↑e : A →+* C) (e.symm : C →+* A)` as an intermediate fact. Conclude with `(e.toSemilinearEquiv.isWeaklyRegular_congr' rs).1 hreg`. Rewrite using `[← ringKrullDim_eq_of_ringEquiv e, hdim, List.length_map]`.
-/
theorem IsCohenMacaulayLocalRing.of_ringEquiv {A C : Type*} [CommRing A] [CommRing C]
    [IsCohenMacaulayLocalRing A] (e : A ≃+* C) : IsCohenMacaulayLocalRing C := by
  have : Nontrivial C := e.injective.nontrivial
  have : IsLocalRing C := IsLocalRing.of_surjective' e.toRingHom e.surjective
  have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv A e
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  refine { exists_isWeaklyRegular := ⟨rs.map e, ?_, ?_, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    have hs' := hm s hs
    rw [mem_maximalIdeal, mem_nonunits_iff] at hs' ⊢
    exact fun h => hs' (by simpa using h.map e.symm)
  · have := RingHomInvPair.of_ringEquiv e
    have := RingHomInvPair.symm (↑e : A →+* C) (e.symm : C →+* A)
    exact (e.toSemilinearEquiv.isWeaklyRegular_congr' rs).1 hreg
  · rw [← ringKrullDim_eq_of_ringEquiv e, hdim, List.length_map]

/- English proof (translation)
Proceed by induction on `a using WithBot.recBotCoe with`. Consider the case `bot => simp at h`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`.

Rewrite `h` using `[← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj, top_add]`. Conclude with `absurd h (ENat.top_ne_natCast n)`. Consider the case `coe k`. Use `⟨k, rfl, ?_⟩` and prove the remaining obligations. Conclude with `h` after adjusting the coercions.
-/
theorem exists_nat_of_add_natCast_eq {a : WithBot ℕ∞} {m n : ℕ}
    (h : a + (m : WithBot ℕ∞) = (n : WithBot ℕ∞)) : ∃ k : ℕ, a = k ∧ k + m = n := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj, top_add] at h
      exact absurd h (ENat.top_ne_natCast n)
    | coe k =>
      refine ⟨k, rfl, ?_⟩
      exact_mod_cast h

/- English proof (translation)
Introduce `B _ _ d`. Proceed by induction on `d generalizing B with`. Consider the case `zero`. Introduce `x _ _`. Establish `h0 : Ideal.span (Set.range x) = ⊥`.

Rewrite using `[Set.range_eq_empty, Ideal.span_empty]`. Conclude with `IsCohenMacaulayLocalRing.of_ringEquiv ((RingEquiv.quotientBot B).symm.trans (Ideal.quotEquivOfEq h0.symm))`. Consider the case `succ d ih => classical`. Introduce `x hx hdim`. Set `x' : Fin d → B ⧸ Ideal.span {x 0}` to `fun i => Ideal.Quotient.mk _ (x i.succ)`.

Establish `hIJ : Ideal.span (Set.range x) = Ideal.span {x 0} ⊔ Ideal.span (Set.range (Fin.tail x))`. Rewrite using `[Fin.range_fin_succ, Ideal.span_insert]`. Establish `hmap : (Ideal.span (Set.range (Fin.tail x))).map (Ideal.Quotient.mk (Ideal.span {x 0})) = Ideal.span (Set.range x')`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Both sides reduce to the same expression.

Set `e : (B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x') ≃+* B ⧸ Ideal.span (Set.range x)` to `(Ideal.quotEquivOfEq hmap.symm).trans ((DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq hIJ.symm))`. Establish `hIne : Ideal.span {x 0} ≠ ⊤` using `fun h => (maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ (Ideal.span_singleton_le_iff_mem _).2 (hx 0)))`. Establish `: Nontrivial (B ⧸ Ideal.span {x 0})` using `Ideal.Quotient.nontrivial_iff.2 hIne`. Establish `: IsLocalRing (B ⧸ Ideal.span {x 0})` using `IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective`. Establish `: IsLocalHom (Ideal.Quotient.mk (Ideal.span {x 0}))` using `IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective`.

Establish `hx' : ∀ i, x' i ∈ maximalIdeal (B ⧸ Ideal.span {x 0})` using `fun i => (mem_maximalIdeal _).2 fun hu => (mem_maximalIdeal _).1 (hx i.succ) (isUnit_of_map_unit (Ideal.Quotient.mk _) _ hu)`. Take `⟨rs, -, -, hD⟩` from `IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)`. Establish `he` using `ringKrullDim_eq_of_ringEquiv e`. Take `⟨k, hk, hkn⟩` from `exists_nat_of_add_natCast_eq (hdim.trans hD)`. Establish `hKrull : ringKrullDim (B ⧸ Ideal.span {x 0}) ≤ (k : WithBot ℕ∞) + (d : WithBot ℕ∞)`.

Establish `hs : ((Finset.univ.image x' : Finset _) : Set _) ⊆ SetLike.coe (Ring.jacobson (B ⧸ Ideal.span {x 0}))`. Rewrite using `[IsLocalRing.ringJacobson_eq_maximalIdeal]`. Introduce `z hz`. Rewrite `hz` using `[Finset.coe_image, Finset.coe_univ, Set.image_univ]`. Take `⟨i, rfl⟩` from `hz`.

Conclude with `hx' i`. Establish `h1` using `ringKrullDim_le_ringKrullDim_quotient_add_card _ hs`. Rewrite `h1` using `[Finset.coe_image, Finset.coe_univ, Set.image_univ, he, hk]`. Use `h1.trans ?_` and prove the remaining obligations. Use `gcongr`.

Conclude with `Finset.card_image_le.trans (Finset.card_univ.trans (Fintype.card_fin d)).le` after adjusting the coercions. Establish `hmin : ∀ p ∈ minimalPrimes B, x 0 ∉ p`. Introduce `p hp hyp`. Establish `hle : Ideal.span {x 0} ≤ p` using `(Ideal.span_singleton_le_iff_mem _).2 hyp`. Establish `h1` using `ringKrullDim_quotient_eq_of_mem_minimalPrimes hp`.

Establish `h2 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ Ideal.span {x 0})` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)`. Establish `h3` using `(h1.symm.trans_le h2).trans hKrull`. Rewrite `h3` using `[hD]`. Establish `h4 : rs.length ≤ k + d` using `by exact_mod_cast h3`. Use linear arithmetic over natural numbers and integers.

Take `⟨hnzd, hCM⟩` from `hreg B (x 0) (hx 0) hmin`. Establish `hdimI : ringKrullDim (B ⧸ Ideal.span {x 0}) + ((1 : ℕ) : WithBot ℕ∞) = (rs.length : WithBot ℕ∞)`. Rewrite using `[Nat.cast_one, ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd (hx 0), hD]`. Take `⟨k', hk', hk'n⟩` from `exists_nat_of_add_natCast_eq hdimI`. Establish `hdim' : ringKrullDim ((B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x')) + (d : WithBot ℕ∞) = ringKrullDim (B ⧸ Ideal.span {x 0})`.

Rewrite using `[he, hk, hk']`. Conclude with `(by omega : k + d = k')` after adjusting the coercions. Establish `: IsCohenMacaulayLocalRing (B ⧸ Ideal.span {x 0})` using `hCM`. Use `ih (B ⧸ Ideal.span {x 0}) x' hx' hdim'` as an intermediate fact. Conclude with `IsCohenMacaulayLocalRing.of_ringEquiv e`.
-/
theorem CMParameterQuotient.proof (hreg : CMRegularElement.Statement.{0}) :
    CMParameterQuotient.Statement := by
  intro B _ _ d
  induction d generalizing B with
  | zero =>
    intro x _ _
    have h0 : Ideal.span (Set.range x) = ⊥ := by
      rw [Set.range_eq_empty, Ideal.span_empty]
    exact IsCohenMacaulayLocalRing.of_ringEquiv
      ((RingEquiv.quotientBot B).symm.trans (Ideal.quotEquivOfEq h0.symm))
  | succ d ih =>
    classical
    intro x hx hdim
    let x' : Fin d → B ⧸ Ideal.span {x 0} := fun i => Ideal.Quotient.mk _ (x i.succ)
    have hIJ : Ideal.span (Set.range x) =
        Ideal.span {x 0} ⊔ Ideal.span (Set.range (Fin.tail x)) := by
      rw [Fin.range_fin_succ, Ideal.span_insert]
    have hmap : (Ideal.span (Set.range (Fin.tail x))).map (Ideal.Quotient.mk (Ideal.span {x 0})) =
        Ideal.span (Set.range x') := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    let e : (B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x') ≃+* B ⧸ Ideal.span (Set.range x) :=
      (Ideal.quotEquivOfEq hmap.symm).trans
        ((DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq hIJ.symm))
    have hIne : Ideal.span {x 0} ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ (Ideal.span_singleton_le_iff_mem _).2 (hx 0)))
    have : Nontrivial (B ⧸ Ideal.span {x 0}) := Ideal.Quotient.nontrivial_iff.2 hIne
    have : IsLocalRing (B ⧸ Ideal.span {x 0}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x 0})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hx' : ∀ i, x' i ∈ maximalIdeal (B ⧸ Ideal.span {x 0}) := fun i =>
      (mem_maximalIdeal _).2 fun hu =>
        (mem_maximalIdeal _).1 (hx i.succ) (isUnit_of_map_unit (Ideal.Quotient.mk _) _ hu)
    obtain ⟨rs, -, -, hD⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
    have he := ringKrullDim_eq_of_ringEquiv e
    obtain ⟨k, hk, hkn⟩ := exists_nat_of_add_natCast_eq (hdim.trans hD)

    have hKrull : ringKrullDim (B ⧸ Ideal.span {x 0}) ≤ (k : WithBot ℕ∞) + (d : WithBot ℕ∞) := by
      have hs : ((Finset.univ.image x' : Finset _) : Set _) ⊆ SetLike.coe (Ring.jacobson (B ⧸ Ideal.span {x 0})) := by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        intro z hz
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hz
        obtain ⟨i, rfl⟩ := hz
        exact hx' i
      have h1 := ringKrullDim_le_ringKrullDim_quotient_add_card _ hs
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, he, hk] at h1
      refine h1.trans ?_
      gcongr
      exact_mod_cast Finset.card_image_le.trans (Finset.card_univ.trans (Fintype.card_fin d)).le
    have hmin : ∀ p ∈ minimalPrimes B, x 0 ∉ p := by
      intro p hp hyp
      have hle : Ideal.span {x 0} ≤ p := (Ideal.span_singleton_le_iff_mem _).2 hyp
      have h1 := ringKrullDim_quotient_eq_of_mem_minimalPrimes hp
      have h2 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ Ideal.span {x 0}) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
      have h3 := (h1.symm.trans_le h2).trans hKrull
      rw [hD] at h3
      have h4 : rs.length ≤ k + d := by exact_mod_cast h3
      omega
    obtain ⟨hnzd, hCM⟩ := hreg B (x 0) (hx 0) hmin
    have hdimI : ringKrullDim (B ⧸ Ideal.span {x 0}) + ((1 : ℕ) : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) := by
      rw [Nat.cast_one, ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd (hx 0),
        hD]
    obtain ⟨k', hk', hk'n⟩ := exists_nat_of_add_natCast_eq hdimI
    have hdim' : ringKrullDim ((B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x')) + (d : WithBot ℕ∞) =
        ringKrullDim (B ⧸ Ideal.span {x 0}) := by
      rw [he, hk, hk']
      exact_mod_cast (by omega : k + d = k')
    have : IsCohenMacaulayLocalRing (B ⧸ Ideal.span {x 0}) := hCM
    have := ih (B ⧸ Ideal.span {x 0}) x' hx' hdim'
    exact IsCohenMacaulayLocalRing.of_ringEquiv e

end GroundTheory.Heights₂.Heights
