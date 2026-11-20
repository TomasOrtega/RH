import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ActsLinOfSplitLin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRamifiedPlacesHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterConjHalfIdeleEqProdLocalStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DilChi
open GlobalTheory.ChiUnit

/- English proof (translation)
Use `show Formalism.L2.DIV.starOHom (m : 𝓞 E) ∈ P.asIdeal ↔ _`. Rewrite using `[map_natCast]`.
-/
theorem natCast_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (P : Pl E) (m : ℕ) :
    (m : 𝓞 E) ∈ (conjPl P).asIdeal ↔ (m : 𝓞 E) ∈ P.asIdeal := by
  show Formalism.L2.DIV.starOHom (m : 𝓞 E) ∈ P.asIdeal ↔ _
  rw [map_natCast]

/- English proof (translation)
Use `show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO a) ∈ P.asIdeal ↔ _`. Rewrite using `[Formalism.L2.DIV.starO_starO]`.
-/
theorem conjO_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (P : Pl E) (a : 𝓞 E) :
    Formalism.L2.DIV.starO a ∈ (conjPl P).asIdeal ↔ a ∈ P.asIdeal := by
  show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO a) ∈ P.asIdeal ↔ _
  rw [Formalism.L2.DIV.starO_starO]

/- English proof (translation)
Introduce `ha`. Apply `h` to reduce the goal to its premises. Establish `h1 : Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO a) ∈ Ideal.map Formalism.L2.DIV.starOHom ((conjPl P).asIdeal ^ 2)` using `Ideal.mem_map_of_mem _ ha`. Rewrite `h1` using `[Ideal.map_pow]`. Establish `h2 : Ideal.map Formalism.L2.DIV.starOHom (conjPl P).asIdeal ≤ P.asIdeal` using `Ideal.map_comap_le`.

Establish `h3` using `Ideal.pow_right_mono h2 2 h1`. Rewrite `h3` using `[show Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO a) = a from Formalism.L2.DIV.starO_starO a]`. Then use the resulting hypothesis.
-/
theorem conjO_not_mem_sq {E : Type} [Field E] [NumberField E] [StarRing E] {P : Pl E} {a : 𝓞 E}
    (h : a ∉ P.asIdeal ^ 2) : Formalism.L2.DIV.starO a ∉ (conjPl P).asIdeal ^ 2 := by
  intro ha
  apply h
  have h1 : Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO a) ∈ Ideal.map Formalism.L2.DIV.starOHom ((conjPl P).asIdeal ^ 2) := Ideal.mem_map_of_mem _ ha
  rw [Ideal.map_pow] at h1
  have h2 : Ideal.map Formalism.L2.DIV.starOHom (conjPl P).asIdeal ≤ P.asIdeal := Ideal.map_comap_le
  have h3 := Ideal.pow_right_mono h2 2 h1
  rwa [show Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO a) = a from Formalism.L2.DIV.starO_starO a] at h3

/- English proof (translation)
Use `haveI : Finite (kP P) := Nat.finite_of_card_ne_zero h`. Use `letI := Fintype.ofFinite (kP P)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]`. Conclude with `Nat.cast_card_eq_zero (kP P)`.
-/
theorem natCard_mem {E : Type} [Field E] [NumberField E] (P : Pl E) (h : Nat.card (kP P) ≠ 0) :
    ((Nat.card (kP P) : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  haveI : Finite (kP P) := Nat.finite_of_card_ne_zero h
  letI := Fintype.ofFinite (kP P)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero (kP P)

/- English proof (translation)
Establish `hca : c * (e * i + c * s + (1 - e - c)) = c * s`. Take the linear combination `(i - 1) * hce + (s - 1) * hc2`. Establish `hpow : ∀ m : ℕ, c * (e * i + c * s + (1 - e - c)) ^ m = c * s ^ m`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => simp`. Consider the case `succ m ih`. Combine the equalities or inequalities in the displayed calculation. Take the linear combination `hpow n`.
-/
theorem units_mul_relation_rearrange_commRing {Rg : Type*} [CommRing Rg] (c e i s : Rg) (n : ℕ) (hc2 : c * c = c) (hce : c * e = 0) :
    c * (e * i + c * s + (1 - e - c)) ^ n + (1 - c) = 1 + c * (s ^ n - 1) := by
  have hca : c * (e * i + c * s + (1 - e - c)) = c * s := by
    linear_combination (i - 1) * hce + (s - 1) * hc2
  have hpow : ∀ m : ℕ, c * (e * i + c * s + (1 - e - c)) ^ m = c * s ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc c * (e * i + c * s + (1 - e - c)) ^ (m + 1) = (c * (e * i + c * s + (1 - e - c)) ^ m) * (e * i + c * s + (1 - e - c)) := by ring
        _ = s ^ m * (c * (e * i + c * s + (1 - e - c))) := by rw [ih]; ring
        _ = c * s ^ (m + 1) := by rw [hca]; ring
  linear_combination hpow n

/- English proof (translation)
Establish `he : eQ * eQ = eQ` using `by classical`. Take `⟨es, hes, hsum, horth⟩` from `Formalism.IndefR.Fin.idemSum_orth Q eQ heQ`. Rewrite using `[hsum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single i (fun j hj hji => (horth i hi j hj (Ne.symm hji)).1) (fun h => absurd hi h)]`.

Conclude with `(hes i hi).1`. Establish `hc2 : cA D eQ * cA D eQ = cA D eQ` using `by rw [← map_mul, he]`. Establish `hce : cA D eQ * eQ = 0` using `by rw [mul_comm]; exact heQ.2`. Establish `hs : incA D (star ϖ) = cA D (incA D ϖ)` using `rfl`. Rewrite using `[hx, hz, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.

Unfold `Formalism.L2.JoinChr.locE`. Rewrite using `[map_pow, hs]`. Conclude with `units_mul_relation_rearrange_commRing _ _ _ _ V.rank hc2 hce`.
-/
theorem detIdele_eq_locE (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (eQ : AE D) (heQ : IsIdemSum eQ Q)
    (ϖ : D.host.E) (z : GA D V)
    (hz : mt V z = Matrix.diagonal (fun _ => eQ * incA D ϖ⁻¹ + cA D eQ * cA D (incA D ϖ) + (1 - eQ - cA D eQ)))
    (x : (AE D)ˣ) (hx : IsDetAt (cA D eQ) V z x) :
    (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (star ϖ ^ V.rank) := by
  have he : eQ * eQ = eQ := by
    classical
    obtain ⟨es, hes, hsum, horth⟩ := Formalism.IndefR.Fin.idemSum_orth Q eQ heQ
    rw [hsum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i (fun j hj hji => (horth i hi j hj (Ne.symm hji)).1) (fun h => absurd hi h)]
    exact (hes i hi).1
  have hc2 : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, he]
  have hce : cA D eQ * eQ = 0 := by rw [mul_comm]; exact heQ.2
  have hs : incA D (star ϖ) = cA D (incA D ϖ) := rfl
  rw [hx, hz, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold Formalism.L2.JoinChr.locE
  rw [map_pow, hs]
  exact units_mul_relation_rearrange_commRing _ _ _ _ V.rank hc2 hce

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV ξ χ ξR Q ω φ hK hQt N hN hNQ eQ heQ ϖ hϖ0 hϖ z hz x hx`. Use `show GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N _`. Establish `hlev` using `hC.lev`. Establish `hs0 : star ((ϖ : 𝓞 D.host.E) : D.host.E) ≠ 0` using `by simpa using hϖ0`. Use `set u : D.host.Eˣ := Units.mk0 _ hs0 with hu`.

Establish `hxl : (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (((u ^ (Vc D i).rank : D.host.Eˣ)) : D.host.E)`. Rewrite using `[detIdele_eq_locE D (Vc D i) Q eQ heQ _ z hz x hx, Units.val_pow_eq_pow_val]`. Both sides reduce to the same expression. Establish `hval : ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ → ((c x : Circle) : ℂ) = ∏ P ∈ Q, (((ψ.locK (conjPl P) u : ℂˣ) : ℂ)) ^ (Vc D i).rank`. Introduce `c ψ hc`.

Rewrite using `[GlobalTheory.T.heckeCharacter_conjHalfIdele_eq_prod_local D Q eQ heQ (u ^ (Vc D i).rank) x hxl c ψ hc]`. Use `Finset.prod_congr rfl fun P _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow, Units.val_pow_eq_pow_val]`. Establish `e : ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)) = (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ)) * (((χ x : Circle) : ℂ)) * (((R.eta x : Circle) : ℂ))⁻¹`. Simplify using `only [Lift.chrTh, Lift.tup, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]`.

Rewrite using `[e, hval _ _ (hlev.mu0 i), hval _ _ hK.chr, hval _ _ hlev.eta]`. Establish `hb : ∀ P ∈ Q, Formalism.L2.DIV.starO ϖ ∈ (conjPl P).asIdeal ∧ Formalism.L2.DIV.starO ϖ ∉ (conjPl P).asIdeal ^ 2` using `fun P hP => ⟨(conjO_mem_conjPl P ϖ).2 (hϖ P hP).1, conjO_not_mem_sq (hϖ P hP).2⟩`. Establish `hNc : ∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ (conjPl P).asIdeal` using `fun P hP => (natCast_mem_conjPl P N).2 (hNQ P hP)`. Establish `hunr : ∀ P ∈ Q, (R.C.mu0 i).UnrAt (conjPl P)` using `fun P hP => by`. Take `⟨⟨q, hq, hqc, -, hqg⟩, -⟩` from `hK.pl P hP`.

Establish `hqm : (q : 𝓞 D.host.E) ∈ (conjPl P).asIdeal`. Rewrite using `[natCast_mem_conjPl, ← hqc]; exact natCard_mem P (by rw [hqc]; exact hq.ne_zero)`. Conclude with `(R.C.isMu0 i).unr (conjPl P) fun k hk => not_mem_of_prime_ne (conjPl P) (D.host.g_prime k) hq (hqg k) hqm hk`. Establish `hcoe : (u : D.host.E) = ((Formalism.L2.DIV.starO ϖ : 𝓞 D.host.E) : D.host.E)` using `by rw [Formalism.L2.DIV.starO_coe]; rfl`. Take `⟨nμ, -, hnμ⟩` from `(R.C.isMu0 i).inf`.

Take `⟨n, hn, hnx⟩` from `hK.fin`. Use `unitOff_inv (unitOff_mul (unitOff_mul (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _) (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)) (unitOff_inv (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)))` and prove the remaining obligations. Rewrite using `[locK_eq_val _ (hunr P hP) u _ hcoe (hb P hP).1 (hb P hP).2]`. Conclude with `GlobalTheory.ValUnit.unitOff_val _ _ _ _ nμ (conjPl P) _ hnμ (finite_ramified_places_hecke_character _ (R.C.isMu0 i).unr) (R.C.isMu0 i).tame (hunr P hP) (hNc P hP)`. Use `unitOff_of_pow_eq_one _ hn ?_` and prove the remaining obligations.

Establish `h` using `LR ξ n hnx (conjPl P) u`. Rewrite using `[← Units.val_pow_eq_pow_val, h, Units.val_one]`. Rewrite using `[locK_eq_val _ (R.C.isEta.unr (conjPl P)) u _ hcoe (hb P hP).1 (hb P hP).2]`. Conclude with `GlobalTheory.ValUnit.unitOff_val _ _ _ _ _ (conjPl P) _ R.C.isEta.inf (Set.Finite.subset Set.finite_empty fun w hw => hw (R.C.isEta.unr w)) (fun w y hy _ => R.C.isEta.unr w y hy) (R.C.isEta.unr (conjPl P)) (hNc P hP)`.
-/
theorem chi_unitOff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∀ x : (AE D)ˣ, IsDetAt (cA D eQ) (Vc D i) z x → UnitOff N ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV ξ χ ξR Q ω φ hK hQt N hN hNQ eQ heQ ϖ hϖ0 hϖ z hz x hx
  show GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N _
  have hlev := hC.lev
  have hs0 : star ((ϖ : 𝓞 D.host.E) : D.host.E) ≠ 0 := by simpa using hϖ0
  set u : D.host.Eˣ := Units.mk0 _ hs0 with hu
  have hxl : (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (((u ^ (Vc D i).rank : D.host.Eˣ)) : D.host.E) := by
    rw [detIdele_eq_locE D (Vc D i) Q eQ heQ _ z hz x hx, Units.val_pow_eq_pow_val]; rfl
  have hval : ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ →
      ((c x : Circle) : ℂ) = ∏ P ∈ Q, (((ψ.locK (conjPl P) u : ℂˣ) : ℂ)) ^ (Vc D i).rank := by
    intro c ψ hc
    rw [GlobalTheory.T.heckeCharacter_conjHalfIdele_eq_prod_local D Q eQ heQ (u ^ (Vc D i).rank) x hxl c ψ hc]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_pow, Units.val_pow_eq_pow_val]
  have e : ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)) =
      (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ)) * (((χ x : Circle) : ℂ)) * (((R.eta x : Circle) : ℂ))⁻¹ := by
    simp only [Lift.chrTh, Lift.tup, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [e, hval _ _ (hlev.mu0 i), hval _ _ hK.chr, hval _ _ hlev.eta]
  have hb : ∀ P ∈ Q, Formalism.L2.DIV.starO ϖ ∈ (conjPl P).asIdeal ∧ Formalism.L2.DIV.starO ϖ ∉ (conjPl P).asIdeal ^ 2 := fun P hP =>
    ⟨(conjO_mem_conjPl P ϖ).2 (hϖ P hP).1, conjO_not_mem_sq (hϖ P hP).2⟩
  have hNc : ∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := fun P hP => (natCast_mem_conjPl P N).2 (hNQ P hP)
  have hunr : ∀ P ∈ Q, (R.C.mu0 i).UnrAt (conjPl P) := fun P hP => by
    obtain ⟨⟨q, hq, hqc, -, hqg⟩, -⟩ := hK.pl P hP
    have hqm : (q : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := by
      rw [natCast_mem_conjPl, ← hqc]; exact natCard_mem P (by rw [hqc]; exact hq.ne_zero)
    exact (R.C.isMu0 i).unr (conjPl P) fun k hk =>
      not_mem_of_prime_ne (conjPl P) (D.host.g_prime k) hq (hqg k) hqm hk
  have hcoe : (u : D.host.E) = ((Formalism.L2.DIV.starO ϖ : 𝓞 D.host.E) : D.host.E) := by rw [Formalism.L2.DIV.starO_coe]; rfl
  obtain ⟨nμ, -, hnμ⟩ := (R.C.isMu0 i).inf
  obtain ⟨n, hn, hnx⟩ := hK.fin
  refine unitOff_inv (unitOff_mul (unitOff_mul (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)
    (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)) (unitOff_inv (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)))
  · rw [locK_eq_val _ (hunr P hP) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ nμ (conjPl P) _ hnμ (finite_ramified_places_hecke_character _ (R.C.isMu0 i).unr)
      (R.C.isMu0 i).tame (hunr P hP) (hNc P hP)
  · refine unitOff_of_pow_eq_one _ hn ?_
    have h := LR ξ n hnx (conjPl P) u
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  · rw [locK_eq_val _ (R.C.isEta.unr (conjPl P)) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ _ (conjPl P) _ R.C.isEta.inf
      (Set.Finite.subset Set.finite_empty fun w hw => hw (R.C.isEta.unr w)) (fun w y hy _ => R.C.isEta.unr w y hy)
      (R.C.isEta.unr (conjPl P)) (hNc P hP)

end GlobalTheory.DilChi
