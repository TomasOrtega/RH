import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIsScalar
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ExportSeries GlobalTheory.SeriesTie

noncomputable section

namespace GlobalTheory.ChoiceAdm

open Formalism.L2.NTheta (IsIdemAt)

variable {D : D7}

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Use `D.host.isCMField_hostE` as an intermediate fact. Conclude with `(IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans (D.host.conjE_apply D.host.φ₀ x).symm`.
-/
theorem star_eq_conj (x : D.host.E) : star x = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

abbrev cnj (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cnj_coe (x : 𝓞 D.host.E) : ((cnj D x : 𝓞 D.host.E) : D.host.E) = D.host.conj x := rfl

/- English proof (translation)
Establish `hle : P.asIdeal ≤ P'.asIdeal.comap (cnj D)` using `fun c hc => by`. Take `⟨c', h1, h2⟩` from `h c hc`. Establish `e : cnj D c = c'` using `RingOfIntegers.ext (by rw [cnj_coe, h2, star_eq_conj])`. Rewrite using `[Ideal.mem_comap, e]`. Conclude with `h1`.

Establish `heq` using `P.isMaximal.eq_of_le (Ideal.comap_ne_top _ P'.isPrime.ne_top) hle`. Introduce `x y hxy`. Establish `e : y = cnj D x` using `RingOfIntegers.ext hxy`. Rewrite using `[e, ← Ideal.mem_comap, ← heq]`.
-/
theorem isConjPl_of_lev {P P' : Pl D.host.E} (h : Lev.IsConjPl P P') : IsConjPl D.host P P' := by
  have hle : P.asIdeal ≤ P'.asIdeal.comap (cnj D) := fun c hc => by
    obtain ⟨c', h1, h2⟩ := h c hc
    have e : cnj D c = c' := RingOfIntegers.ext (by rw [cnj_coe, h2, star_eq_conj])
    rw [Ideal.mem_comap, e]
    exact h1
  have heq := P.isMaximal.eq_of_le (Ideal.comap_ne_top _ P'.isPrime.ne_top) hle
  intro x y hxy
  have e : y = cnj D x := RingOfIntegers.ext hxy
  rw [e, ← Ideal.mem_comap, ← heq]

/- English proof (translation)
Introduce `hc` and use `GlobalTheory.SeriesTie.ne_of_split h (isConjPl_of_lev hc) rfl`.
-/
theorem not_lev_self {P : Pl D.host.E} (h : IsSplitPl D.host P) : ¬ Lev.IsConjPl P P := fun hc =>
  GlobalTheory.SeriesTie.ne_of_split h (isConjPl_of_lev hc) rfl

/- English proof (translation)
Use `GlobalTheory.MovedIdem.exists_isIdemAt P fun hP => ?_` and prove the remaining obligations. Take `⟨x, hx, hy⟩` from `h`. Use `hy (cnj D x) rfl ?_` and prove the remaining obligations. Rewrite using `[← hP]`. Conclude with `Ideal.subset_span ⟨x, hx, by`.

Express the relevant statement in the definitionally equal form `((cnj D x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E)`. Rewrite using `[cnj_coe, star_eq_conj]⟩`.
-/
theorem exists_idem {P : Pl D.host.E} (h : IsSplitPl D.host P) : ∃ e, IsIdemAt e P := by
  refine GlobalTheory.MovedIdem.exists_isIdemAt P fun hP => ?_
  obtain ⟨x, hx, hy⟩ := h
  refine hy (cnj D x) rfl ?_
  rw [← hP]
  exact Ideal.subset_span ⟨x, hx, by
    change ((cnj D x : 𝓞 D.host.E) : D.host.E) = star (x : D.host.E)
    rw [cnj_coe, star_eq_conj]⟩

/- English proof (translation)
Establish `hc : Lev.IsConjPl j (GlobalTheory.IdemSupport.cP j)` using `fun c hc => ⟨GlobalTheory.IdemSupport.cO D c, by show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D c) ∈ j.asIdeal`. Rewrite using `[show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D c) = c from RingOfIntegers.ext (star_star (c : D.host.E))], rfl⟩` and apply the resulting hypothesis. Establish `h2 : IsIdemAt (cA D b) (GlobalTheory.IdemSupport.cP j)` using `(GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 j _ b hb hc`. Rewrite `h2` using `[← e]`. Establish `hij : i = GlobalTheory.IdemSupport.cP j`.

Use `HeightOneSpectrum.ext (Ideal.ext fun x => ?_)` and prove the remaining obligations. Distinguish the cases in `hx : x = 0`. Rewrite using `[hx]`. Conclude with `iff_of_true (zero_mem _) (zero_mem _)`. Rewrite using `[ha.2 x hx, h2.2 x hx]`.

Rewrite using `[hij]`. Conclude with `hc`.
-/
theorem lev_of_eq_cA {i j : Pl D.host.E} {a b : Formalism.L2.Theta.AE D} (ha : IsIdemAt a i) (hb : IsIdemAt b j)
    (e : a = cA D b) : Lev.IsConjPl j i := by
  have hc : Lev.IsConjPl j (GlobalTheory.IdemSupport.cP j) := fun c hc =>
    ⟨GlobalTheory.IdemSupport.cO D c, by
      show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D c) ∈ j.asIdeal
      rwa [show GlobalTheory.IdemSupport.cO D (GlobalTheory.IdemSupport.cO D c) = c from RingOfIntegers.ext (star_star (c : D.host.E))], rfl⟩
  have h2 : IsIdemAt (cA D b) (GlobalTheory.IdemSupport.cP j) :=
    (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents D.sp.X').2.2.2 j _ b hb hc
  rw [← e] at h2
  have hij : i = GlobalTheory.IdemSupport.cP j := by
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
    · rw [ha.2 x hx, h2.2 x hx]
  rw [hij]
  exact hc

open Classical in
/- English proof (translation)
Establish `hid : ∀ p ∈ P ∪ H, IsIdemAt (idemAt p) p`. Introduce `p hp`. Break down `Finset.mem_union.1 hp with h | h` into its components or cases. Conclude with `hP.isIdemAt h`. Take `⟨e, he⟩` from `hH p h`.

Rewrite using `[idemAt_eq he]`. Conclude with `he`. Use `⟨idem (P ∪ H), ⟨idemAt, hid, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[idem, map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_` and prove the remaining obligations.

Distinguish the cases in `hh : i ∈ H ∨ j ∈ H`. Break down `GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hid i hi).1 (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hid j hj).1) with e | e` into its components or cases. Conclude with `absurd (lev_of_eq_cA (hid i hi) (hid j hj) e) (hc j hj i hi hh.symm)`. Conclude with `e`. Use `push_neg at hh`.

Establish `hi' : i ∈ P` using `(Finset.mem_union.1 hi).resolve_right hh.1`. Establish `hj' : j ∈ P` using `(Finset.mem_union.1 hj).resolve_right hh.2`. Conclude with `hP.mul_conj hi' hj'`.
-/
theorem splitSet_union {P H : Finset (Pl D.host.E)} (hP : SplitSet P) (hH : ∀ p ∈ H, ∃ e, IsIdemAt e p)
    (hc : ∀ p ∈ P ∪ H, ∀ p' ∈ P ∪ H, p ∈ H ∨ p' ∈ H → ¬ Lev.IsConjPl p p') : SplitSet (P ∪ H) := by
  classical
  have hid : ∀ p ∈ P ∪ H, IsIdemAt (idemAt p) p := by
    intro p hp
    rcases Finset.mem_union.1 hp with h | h
    · exact hP.isIdemAt h
    · obtain ⟨e, he⟩ := hH p h
      rw [idemAt_eq he]
      exact he
  refine ⟨idem (P ∪ H), ⟨idemAt, hid, rfl⟩, ?_⟩
  rw [idem, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => ?_
  by_cases hh : i ∈ H ∨ j ∈ H
  · rcases GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hid i hi).1 (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hid j hj).1) with e | e
    · exact absurd (lev_of_eq_cA (hid i hi) (hid j hj) e) (hc j hj i hi hh.symm)
    · exact e
  · push_neg at hh
    have hi' : i ∈ P := (Finset.mem_union.1 hi).resolve_right hh.1
    have hj' : j ∈ P := (Finset.mem_union.1 hj).resolve_right hh.2
    exact hP.mul_conj hi' hj'

end GlobalTheory.ChoiceAdm

end

namespace GlobalTheory.ChoiceAdm

open Classical in

/- English proof (translation)
Introduce `D N X ρ hρ i j b Q hsplit hdisj`. Establish `hG` using `hρ.base i j b`. Establish `hdeQ : (ρ.B i j b).de.Q = half (ρ.ch i) (X.pD i)` using `by rw [hρ.delta i j b]; rfl`. Establish `deS0 : ∀ P ∈ (ρ.B i j b).de.Q, P ∈ X.S0 i` using `fun P hP => by`. Rewrite `hP` using `[hdeQ]`.

Conclude with `X.primes_subset_exceptional i (mem_half.1 hP).1`. Establish `PgS0 : ∀ P ∈ (ρ.B i j b).G.Pg, P ∈ X.S0 i` using `fun P hP => by`. Take `⟨k, hk⟩` from `hρ.Pg i j b P hP`. Conclude with `Finset.mem_coe.1 (X.placesOver_subset_exceptional i k hk)`. Establish `hH : ∀ P ∈ half (ρ.ch i) Q, P ∉ X.S0 i` using `fun P hP h => Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 h`.

Establish `hcS0 : ∀ P ∈ half (ρ.ch i) Q, ∀ P' ∈ X.S0 i, ¬ Lev.IsConjPl P P' ∧ ¬ Lev.IsConjPl P' P`. Introduce `P hP P' hP'`. Use `⟨fun hc => hH P hP ?_, fun hc => hH P hP ?_⟩` and prove the remaining obligations. Conclude with `hρ.goodSetup_badPlaces_conj i P' hP' P (GlobalTheory.GalChar.isConjPl_symm (isConjPl_of_lev hc))`. Conclude with `hρ.goodSetup_badPlaces_conj i P' hP' P (isConjPl_of_lev hc)`.

Establish `hA : ∀ P ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q, P ∈ X.S0 i` using `fun P hP => (Finset.mem_union.1 hP).elim (PgS0 P) (deS0 P)`. Use `⟨⟨⟨(ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q ∪ half (ρ.ch i) Q, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `Finset.subset_union_left.trans Finset.subset_union_left`. Conclude with `Finset.union_subset (Finset.subset_union_right.trans Finset.subset_union_left) Finset.subset_union_right`. Use `splitSet_union ?_ (fun p hp => exists_idem (hsplit p (mem_half.1 hp).1)) ?_` and prove the remaining obligations.

Take `⟨P0, h1, h2, h3⟩` from `hG.places.split`. Conclude with `h3.mono (Finset.union_subset h1 h2)`. Introduce `p hp p' hp' hh hc`. Distinguish the cases in `h1 : p ∈ half (ρ.ch i) Q`. Distinguish the cases in `h2 : p' ∈ half (ρ.ch i) Q`.

Distinguish the cases in `e : p = p'`. Substitute `e` using the available equality. Conclude with `not_lev_self (hsplit p (mem_half.1 h1).1) hc`. Conclude with `((hρ.ch i).pair p p' (isConjPl_of_lev hc) e).1 (mem_half.1 h1).2 (mem_half.1 h2).2`. Establish `: p' ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q` using `(Finset.mem_union.1 hp').resolve_right h2`.

Conclude with `(hcS0 p h1 p' (hA p' this)).1 hc`. Establish `hpA : p ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q` using `(Finset.mem_union.1 hp).resolve_right h1`. Establish `h2 : p' ∈ half (ρ.ch i) Q` using `hh.resolve_left h1`. Conclude with `(hcS0 p' h2 p (hA p hpA)).2 hc`. Use `Finset.disjoint_union_right.2 ⟨hG.places.disj, Finset.disjoint_left.2 fun p hp hq => hH p hq (PgS0 p hp)⟩` and prove the remaining obligations.

Introduce `PP hPP PP' hPP'`. Break down `hPP with h | h` into its components or cases. Conclude with `hG.places.prime PP (Or.inl h) PP' hPP'`. Break down `Finset.mem_union.1 h with h | h` into its components or cases. Conclude with `hG.places.prime PP (Or.inr h) PP' hPP'`.

Use `hρ.goodSetup_count_eq_zero_off_badPlaces i PP' fun hS => ?_` and prove the remaining obligations. Break down `hPP' with e | hc` into its components or cases. Conclude with `hH PP h (e ▸ hS)`. Conclude with `(hcS0 PP h PP' hS).1 hc`. Conclude with `Finset.disjoint_left.2 fun p hp hq => hH p hq (deS0 p hp)`.
-/
theorem adm_half_of_good_of_split_disjoint : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (ρ : Setup X), ρ.Good →
    ∀ (i : X.Tw) (j : Fin D.R.m) (b : Bool) (Q : Finset (Pl D.host.E)), (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl D.host P) →
      Disjoint Q (X.S0 i) → (ρ.B i j b).admitted (half (ρ.ch i) Q) := by
  intro D N X ρ hρ i j b Q hsplit hdisj
  classical
  have hG := hρ.base i j b
  have hdeQ : (ρ.B i j b).de.Q = half (ρ.ch i) (X.pD i) := by rw [hρ.delta i j b]; rfl
  have deS0 : ∀ P ∈ (ρ.B i j b).de.Q, P ∈ X.S0 i := fun P hP => by
    rw [hdeQ] at hP
    exact X.primes_subset_exceptional i (mem_half.1 hP).1
  have PgS0 : ∀ P ∈ (ρ.B i j b).G.Pg, P ∈ X.S0 i := fun P hP => by
    obtain ⟨k, hk⟩ := hρ.Pg i j b P hP
    exact Finset.mem_coe.1 (X.placesOver_subset_exceptional i k hk)
  have hH : ∀ P ∈ half (ρ.ch i) Q, P ∉ X.S0 i := fun P hP h =>
    Finset.disjoint_left.1 hdisj (mem_half.1 hP).1 h

  have hcS0 : ∀ P ∈ half (ρ.ch i) Q, ∀ P' ∈ X.S0 i, ¬ Lev.IsConjPl P P' ∧ ¬ Lev.IsConjPl P' P := by
    intro P hP P' hP'
    refine ⟨fun hc => hH P hP ?_, fun hc => hH P hP ?_⟩
    · exact hρ.goodSetup_badPlaces_conj i P' hP' P (GlobalTheory.GalChar.isConjPl_symm (isConjPl_of_lev hc))
    · exact hρ.goodSetup_badPlaces_conj i P' hP' P (isConjPl_of_lev hc)
  have hA : ∀ P ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q, P ∈ X.S0 i := fun P hP =>
    (Finset.mem_union.1 hP).elim (PgS0 P) (deS0 P)
  refine ⟨⟨⟨(ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q ∪ half (ρ.ch i) Q, ?_, ?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · exact Finset.subset_union_left.trans Finset.subset_union_left
  · exact Finset.union_subset (Finset.subset_union_right.trans Finset.subset_union_left) Finset.subset_union_right
  · refine splitSet_union ?_ (fun p hp => exists_idem (hsplit p (mem_half.1 hp).1)) ?_
    · obtain ⟨P0, h1, h2, h3⟩ := hG.places.split
      exact h3.mono (Finset.union_subset h1 h2)
    · intro p hp p' hp' hh hc
      by_cases h1 : p ∈ half (ρ.ch i) Q
      · by_cases h2 : p' ∈ half (ρ.ch i) Q
        · by_cases e : p = p'
          · subst e
            exact not_lev_self (hsplit p (mem_half.1 h1).1) hc
          · exact ((hρ.ch i).pair p p' (isConjPl_of_lev hc) e).1 (mem_half.1 h1).2 (mem_half.1 h2).2
        · have : p' ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q := (Finset.mem_union.1 hp').resolve_right h2
          exact (hcS0 p h1 p' (hA p' this)).1 hc
      · have hpA : p ∈ (ρ.B i j b).G.Pg ∪ (ρ.B i j b).de.Q := (Finset.mem_union.1 hp).resolve_right h1
        have h2 : p' ∈ half (ρ.ch i) Q := hh.resolve_left h1
        exact (hcS0 p' h2 p (hA p hpA)).2 hc
  · refine Finset.disjoint_union_right.2 ⟨hG.places.disj, Finset.disjoint_left.2 fun p hp hq => hH p hq (PgS0 p hp)⟩
  · intro PP hPP PP' hPP'
    rcases hPP with h | h
    · exact hG.places.prime PP (Or.inl h) PP' hPP'
    · rcases Finset.mem_union.1 h with h | h
      · exact hG.places.prime PP (Or.inr h) PP' hPP'
      · refine hρ.goodSetup_count_eq_zero_off_badPlaces i PP' fun hS => ?_
        rcases hPP' with e | hc
        · exact hH PP h (e ▸ hS)
        · exact (hcS0 PP h PP' hS).1 hc
  · exact Finset.disjoint_left.2 fun p hp hq => hH p hq (deS0 p hp)

end GlobalTheory.ChoiceAdm
