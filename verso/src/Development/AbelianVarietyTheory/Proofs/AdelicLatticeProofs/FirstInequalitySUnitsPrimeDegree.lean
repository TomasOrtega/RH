import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HerbrandPrimeOrderStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90Statement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsKum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PrimeMulCardPlacesLeCardOverKummerStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPlaceValuationAut
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsKummerStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowsSubgroupOfSelfSPow
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Unfold `pIdx`. Rewrite using `[← Subgroup.index_comap]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [pows, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_comap, powMonoidHom_apply, MonoidHom.mem_range]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨y, rfl⟩, h⟩`. Conclude with `⟨y, hj (by simpa using h)⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨j y, ⟨y, rfl⟩, by simp⟩`.
-/
private theorem pIdx_range_eq (p : ℕ) {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    pIdx p j.range = (pows p (⊤ : Subgroup U)).index := by
  unfold pIdx
  rw [← Subgroup.index_comap]
  congr 1
  ext x
  simp only [pows, Subgroup.mem_map, Subgroup.mem_top, true_and, Subgroup.mem_comap,
    powMonoidHom_apply, MonoidHom.mem_range]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨y, hj (by simpa using h)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨j y, ⟨y, rfl⟩, by simp⟩

/- English proof (translation)
Rewrite using `[← pIdx_range_eq p U.subtype U.subtype_injective, Subgroup.range_subtype]`.
-/
private theorem index_pows_top_eq (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    (pows p (⊤ : Subgroup U)).index = pIdx p U := by
  rw [← pIdx_range_eq p U.subtype U.subtype_injective, Subgroup.range_subtype]

/- English proof (translation)
Rewrite using `[← index_pows_top_eq p U, pIdx, Subgroup.relIndex_top_right]`.
-/
private theorem pIdx_top_eq (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pIdx p (⊤ : Subgroup U) = pIdx p U := by
  rw [← index_pows_top_eq p U, pIdx, Subgroup.relIndex_top_right]

/- English proof (translation)
Unfold `pTor`. Use `symm`. Use `Nat.card_eq_of_bijective (fun x => ⟨j x.1, ⟨x.1, rfl⟩, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`. Conclude with `Subtype.ext (hj (congrArg Subtype.val h))`.

Introduce and unpack `⟨_, ⟨y, rfl⟩, h⟩`. Conclude with `⟨⟨y, Subgroup.mem_top _, hj (by rw [map_pow, h, map_one])⟩, rfl⟩`.
-/
private theorem pTor_range_eq (p : ℕ) {U A : Type} [CommGroup U] [CommGroup A] (j : U →* A)
    (hj : Function.Injective j) :
    pTor p j.range = pTor p (⊤ : Subgroup U) := by
  unfold pTor
  symm
  refine Nat.card_eq_of_bijective
    (fun x => ⟨j x.1, ⟨x.1, rfl⟩, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩
  · intro a b h
    exact Subtype.ext (hj (congrArg Subtype.val h))
  · rintro ⟨_, ⟨y, rfl⟩, h⟩
    exact ⟨⟨y, Subgroup.mem_top _, hj (by rw [map_pow, h, map_one])⟩, rfl⟩

/- English proof (translation)
Rewrite using `[← pTor_range_eq p U.subtype U.subtype_injective, Subgroup.range_subtype]`.
-/
private theorem pTor_top_eq (p : ℕ) {G : Type} [CommGroup G] (U : Subgroup G) :
    pTor p (⊤ : Subgroup U) = pTor p U := by
  rw [← pTor_range_eq p U.subtype U.subtype_injective, Subgroup.range_subtype]

/- English proof (translation)
Use `⟨fun h0 => hn (by subst h0; simpa using hd), ?_⟩` and prove the remaining obligations. Establish `hmn : m ≤ n` using `Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd`. Take `⟨q, rfl⟩ : ∃ q, p = q + 1` from `⟨p - 1, by have := hp.two_le; omega⟩`. Establish `hq : q ≠ 0` using `by have := hp.two_le; omega`. Simplify using `only [Nat.add_sub_cancel, one_pow, one_mul] at h hs`.

Use `set p := q + 1 with hpq`. Establish `hpos : 0 < p` using `hp.pos`. Establish `h1 : (p * p ^ (e + p * r)) * (p * n) ^ q ≤ (p * p ^ (e + p * r)) * (p ^ t) ^ q`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← pow_mul, mul_assoc, ← pow_add]`.

Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (p * n) ^ q ≤ (p ^ t) ^ q` using `Nat.le_of_mul_le_mul_left h1 (by positivity)`. Establish `h3 : p * n ≤ p ^ t` using `(Nat.pow_le_pow_iff_left hq).1 h2`. Conclude with `le_trans (Nat.mul_le_mul_left _ hmn) h3`.
-/
private theorem arith_first_ineq (p m n c e r t : ℕ) (hp : p.Prime) (hd : m ∣ n) (hn : n ≠ 0)
    (h : n ^ (p - 1) * p ^ (e + p * r) * p ^ p = 1 ^ (p - 1) * p * (p ^ (c + r)) ^ p)
    (hs : p * c ≤ e + (p - 1) * t) : m ≠ 0 ∧ p * m ≤ p ^ t := by
  refine ⟨fun h0 => hn (by subst h0; simpa using hd), ?_⟩
  have hmn : m ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  have hq : q ≠ 0 := by have := hp.two_le; omega
  simp only [Nat.add_sub_cancel, one_pow, one_mul] at h hs
  set p := q + 1 with hpq
  have hpos : 0 < p := hp.pos
  have h1 : (p * p ^ (e + p * r)) * (p * n) ^ q ≤ (p * p ^ (e + p * r)) * (p ^ t) ^ q := by
    calc (p * p ^ (e + p * r)) * (p * n) ^ q
        = n ^ q * p ^ (e + p * r) * p ^ (q + 1) := by rw [mul_pow, pow_succ]; ring
      _ = p * (p ^ (c + r)) ^ p := h
      _ = p * p ^ (p * c + p * r) := by rw [← pow_mul]; congr 2; ring
      _ ≤ p * p ^ (e + q * t + p * r) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos (by omega))
      _ = (p * p ^ (e + p * r)) * (p ^ t) ^ q := by
        rw [← pow_mul, mul_assoc, ← pow_add]; congr 2; ring
  have h2 : (p * n) ^ q ≤ (p ^ t) ^ q := Nat.le_of_mul_le_mul_left h1 (by positivity)
  have h3 : p * n ≤ p ^ t := (Nat.pow_le_pow_iff_left hq).1 h2
  exact le_trans (Nat.mul_le_mul_left _ hmn) h3

/- English proof (translation)
Introduce `p F _ _ _ ζ δ S hp hζ hS hδ hns`. Take `⟨E, _, _, θ, σ, hq⟩` from `exists_isKum p F ζ δ hp hζ hns`. Take `⟨hfd, hrk, hper, hfix, -, -, hnorm⟩` from `GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p F E ζ δ θ σ hq`. Take `⟨-, -, hgal, -⟩` from `kummer_galois p F E ζ δ θ σ hq`. Use `haveI : NumberField E := NumberField.of_module_finite F E`.

Use `haveI : IsTotallyComplex E := isTotallyComplex_of_algebra F E`. Take `⟨SE, hSE⟩` from `(places_over F E).1 S`. Take `⟨hup, hσ⟩` from `sUnits_over_and_aut F E S SE hSE`. Establish `h90` using `GlobalTheory.T.hilbert90_sUnits_kummer' p F E ζ δ θ σ hq S SE hSE hS ((mem_sUnits F S δ).1 hδ)`. Establish `hcf` using `GlobalTheory.T.prime_mul_card_places_le_card_over_kummer p F E ζ δ θ σ hq S SE hSE`.

Establish `hζE : IsPrimitiveRoot (algebraMap F E ζ) p` using `hζ.map_of_injective (algebraMap F E).injective`. Take `⟨htF, hiF⟩` from `pTor_pIdx_sUnits p F ζ S hp hζ`. Take `⟨htE, hiE⟩` from `pTor_pIdx_sUnits p E _ SE hp hζE`. Establish `hinf : Fintype.card (InfinitePlace E) = p * Fintype.card (InfinitePlace F)`. Establish `h1` using `IsTotallyComplex.finrank F`.

Establish `h2` using `IsTotallyComplex.finrank E`. Establish `h3` using `Module.finrank_mul_finrank ℚ F E`. Establish `h4` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F`. Establish `h5` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E`. Rewrite `h4`, `h5` using `[IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]`.

Rewrite using `[h4, h5]`. Rewrite `h3` using `[h1, h2, hrk]`. Apply `Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)` to reduce the goal to its premises. Rewrite using `[← h3]`. Expand and normalize the polynomial expressions, which then agree.

Set `τ : sUnits E SE →* sUnits E SE` to `((Units.map (σ : E →* E)).comp (sUnits E SE).subtype).codRestrict _ (fun y => hσ σ y y.2)`. Establish `hτ : ∀ y : sUnits E SE, (((τ y : sUnits E SE) : Eˣ) : E) = σ ((y : Eˣ) : E)` using `fun _ => rfl`. Establish `hτi : ∀ (i : ℕ) (y : sUnits E SE), (((τ^[i] y : sUnits E SE) : Eˣ) : E) = σ^[i] ((y : Eˣ) : E)`. Introduce `i`. Proceed by induction on `i with`.

Consider the case `zero => intro y`. Both sides reduce to the same expression. Consider the case `succ i ih => intro y`. Rewrite using `[Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, ih]`. Establish `hN : ∀ y : sUnits E SE, (((nrm τ p y : sUnits E SE) : Eˣ) : E) = ∏ i ∈ Finset.range p, σ^[i] ((y : Eˣ) : E)`.

Introduce `y`. Rewrite using `[nrm_apply, Subgroup.val_finset_prod, Units.coe_prod]`. Conclude with `Finset.prod_congr rfl (fun i _ => hτi i y)`. Set `j : sUnits F S →* sUnits E SE` to `((Units.map (algebraMap F E : F →* E)).comp (sUnits F S).subtype).codRestrict _ (fun y => (hup y).2 y.2)`. Establish `hj : ∀ y : sUnits F S, (((j y : sUnits E SE) : Eˣ) : E) = algebraMap F E ((y : Fˣ) : F)` using `fun _ => rfl`.

Establish `hext : ∀ a b : sUnits E SE, ((a : Eˣ) : E) = ((b : Eˣ) : E) → a = b` using `fun a b h => Subtype.ext (Units.ext h)`. Establish `hjinj : Function.Injective j`. Introduce `a b h`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Apply `(algebraMap F E).injective` to reduce the goal to its premises. Rewrite using `[← hj, ← hj, h]`. Establish `hrange : fix τ = j.range`. Use extensionality with `y`. Rewrite using `[MonoidHom.mem_range, mem_fix]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Take `⟨a, ha⟩` from `hfix ((y : Eˣ) : E) (by rw [← hτ, h])`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`.

Conclude with `(y : Eˣ).ne_zero (by simpa using ha)`. Establish `hy : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = y` using `Units.ext (by simpa using ha.symm)`. Use `⟨⟨Units.mk0 a ha0, (hup _).1 (hy ▸ y.2)⟩, hext _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[hj, ha]`. Both sides reduce to the same expression.

Introduce and unpack `⟨x, rfl⟩`. Apply `hext` to reduce the goal to its premises. Rewrite using `[hτ, hj, AlgEquiv.commutes]`. Establish `hone : (dif τ).range.relIndex (nrm τ p).ker = 1`. Rewrite using `[Subgroup.relIndex_eq_one]`.

Introduce `a ha`. Establish `h1 : ∏ i ∈ Finset.range p, σ^[i] ((a : Eˣ) : E) = 1`. Rewrite using `[← hN, MonoidHom.mem_ker.1 ha]`. Both sides reduce to the same expression. Take `⟨y, hy, h⟩` from `h90 a a.2 h1`.

Use `⟨⟨y, hy⟩, hext _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[h, dif_apply, Subgroup.coe_div, Units.val_div_eq_div_val, hτ]`. Take `⟨h0, -, -, -, key⟩` from `GlobalTheory.T.herbrand_prime_order' p (sUnits E SE) τ hp (fun a => hext _ _ (by rw [hτi, hper])) (by rw [pIdx_top_eq, hiE]; exact pow_ne_zero _ hp.ne_zero) (by rw [pTor_top_eq, htE]; exact hp.ne_zero)`. Rewrite `key` using `[hone, hrange, pIdx_range_eq p j hjinj, pTor_range_eq p j hjinj, index_pows_top_eq, pIdx_top_eq, pTor_top_eq, pTor_top_eq, htF, htE, hiF, hiE, hinf, ← Subgroup.index_comap]`. Rewrite `h0` using `[hrange, ← Subgroup.index_comap]`.

Use `arith_first_ineq p _ _ _ _ _ _ hp ?_ h0 key hcf` and prove the remaining obligations. Apply `Subgroup.index_dvd_of_le` to reduce the goal to its premises. Introduce and unpack `x ⟨y, hy⟩`. Rewrite using `[Subgroup.mem_subgroupOf, hnorm]`. Conclude with `⟨((y : Eˣ) : E), by rw [← hN, hy, hj]⟩`.
-/
theorem first_inequality_sUnits_prime :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ : F) (δ : Fˣ)
      (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → AdmP p F S →
      δ ∈ sUnits F S → (∀ r : F, r ^ p ≠ (δ : F)) →
      (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≠ 0 ∧
        p * (kNorm p (RingHom.id F) (δ : F)).relIndex (sUnits F S) ≤ p ^ tNon p F δ S := by
  intro p F _ _ _ ζ δ S hp hζ hS hδ hns
  obtain ⟨E, _, _, θ, σ, hq⟩ := exists_isKum p F ζ δ hp hζ hns
  obtain ⟨hfd, hrk, hper, hfix, -, -, hnorm⟩ := GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p F E ζ δ θ σ hq
  obtain ⟨-, -, hgal, -⟩ := kummer_galois p F E ζ δ θ σ hq
  haveI : NumberField E := NumberField.of_module_finite F E
  haveI : IsTotallyComplex E := isTotallyComplex_of_algebra F E
  obtain ⟨SE, hSE⟩ := (places_over F E).1 S
  obtain ⟨hup, hσ⟩ := sUnits_over_and_aut F E S SE hSE
  have h90 := GlobalTheory.T.hilbert90_sUnits_kummer' p F E ζ δ θ σ hq S SE hSE hS ((mem_sUnits F S δ).1 hδ)
  have hcf := GlobalTheory.T.prime_mul_card_places_le_card_over_kummer p F E ζ δ θ σ hq S SE hSE
  have hζE : IsPrimitiveRoot (algebraMap F E ζ) p := hζ.map_of_injective (algebraMap F E).injective
  obtain ⟨htF, hiF⟩ := pTor_pIdx_sUnits p F ζ S hp hζ
  obtain ⟨htE, hiE⟩ := pTor_pIdx_sUnits p E _ SE hp hζE
  have hinf : Fintype.card (InfinitePlace E) = p * Fintype.card (InfinitePlace F) := by
    have h1 := IsTotallyComplex.finrank F
    have h2 := IsTotallyComplex.finrank E
    have h3 := Module.finrank_mul_finrank ℚ F E
    have h4 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    have h5 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    rw [IsTotallyComplex.nrRealPlaces_eq_zero, zero_add] at h4 h5
    rw [h4, h5]
    rw [h1, h2, hrk] at h3
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2)
    rw [← h3]; ring
  let τ : sUnits E SE →* sUnits E SE :=
    ((Units.map (σ : E →* E)).comp (sUnits E SE).subtype).codRestrict _ (fun y => hσ σ y y.2)
  have hτ : ∀ y : sUnits E SE, (((τ y : sUnits E SE) : Eˣ) : E) = σ ((y : Eˣ) : E) :=
    fun _ => rfl
  have hτi : ∀ (i : ℕ) (y : sUnits E SE),
      (((τ^[i] y : sUnits E SE) : Eˣ) : E) = σ^[i] ((y : Eˣ) : E) := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih => intro y; rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hτ, ih]
  have hN : ∀ y : sUnits E SE, (((nrm τ p y : sUnits E SE) : Eˣ) : E) =
      ∏ i ∈ Finset.range p, σ^[i] ((y : Eˣ) : E) := by
    intro y
    rw [nrm_apply, Subgroup.val_finset_prod, Units.coe_prod]
    exact Finset.prod_congr rfl (fun i _ => hτi i y)
  let j : sUnits F S →* sUnits E SE :=
    ((Units.map (algebraMap F E : F →* E)).comp (sUnits F S).subtype).codRestrict _
      (fun y => (hup y).2 y.2)
  have hj : ∀ y : sUnits F S, (((j y : sUnits E SE) : Eˣ) : E) = algebraMap F E ((y : Fˣ) : F) :=
    fun _ => rfl
  have hext : ∀ a b : sUnits E SE, ((a : Eˣ) : E) = ((b : Eˣ) : E) → a = b :=
    fun a b h => Subtype.ext (Units.ext h)
  have hjinj : Function.Injective j := by
    intro a b h
    apply Subtype.ext
    apply Units.ext
    apply (algebraMap F E).injective
    rw [← hj, ← hj, h]
  have hrange : fix τ = j.range := by
    ext y
    rw [MonoidHom.mem_range, mem_fix]
    constructor
    · intro h
      obtain ⟨a, ha⟩ := hfix ((y : Eˣ) : E) (by rw [← hτ, h])
      have ha0 : a ≠ 0 := by
        rintro rfl
        exact (y : Eˣ).ne_zero (by simpa using ha)
      have hy : Units.map (algebraMap F E : F →* E) (Units.mk0 a ha0) = y :=
        Units.ext (by simpa using ha.symm)
      refine ⟨⟨Units.mk0 a ha0, (hup _).1 (hy ▸ y.2)⟩, hext _ _ ?_⟩
      rw [hj, ha]; rfl
    · rintro ⟨x, rfl⟩
      apply hext
      rw [hτ, hj, AlgEquiv.commutes]
  have hone : (dif τ).range.relIndex (nrm τ p).ker = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro a ha
    have h1 : ∏ i ∈ Finset.range p, σ^[i] ((a : Eˣ) : E) = 1 := by
      rw [← hN, MonoidHom.mem_ker.1 ha]; rfl
    obtain ⟨y, hy, h⟩ := h90 a a.2 h1
    refine ⟨⟨y, hy⟩, hext _ _ ?_⟩
    rw [h, dif_apply, Subgroup.coe_div, Units.val_div_eq_div_val, hτ]
  obtain ⟨h0, -, -, -, key⟩ := GlobalTheory.T.herbrand_prime_order' p (sUnits E SE) τ hp
    (fun a => hext _ _ (by rw [hτi, hper]))
    (by rw [pIdx_top_eq, hiE]; exact pow_ne_zero _ hp.ne_zero)
    (by rw [pTor_top_eq, htE]; exact hp.ne_zero)
  rw [hone, hrange, pIdx_range_eq p j hjinj, pTor_range_eq p j hjinj, index_pows_top_eq,
    pIdx_top_eq, pTor_top_eq, pTor_top_eq, htF, htE, hiF, hiE, hinf,
    ← Subgroup.index_comap] at key
  rw [hrange, ← Subgroup.index_comap] at h0
  refine arith_first_ineq p _ _ _ _ _ _ hp ?_ h0 key hcf
  apply Subgroup.index_dvd_of_le
  rintro x ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf, hnorm]
  exact ⟨((y : Eˣ) : E), by rw [← hN, hy, hj]⟩

end GlobalTheory.CNorm
