import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTuplesOfLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPowPrimeOrderEmbeddingsDifferByCoprimePower
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open GlobalTheory.BigOn.Exp.TwConj GlobalTheory.IdemSupport
open Formalism.L2.Host (HChar IsDelta IsPsi)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj.LevAt

section Places

variable {D : D7}

/- English proof (translation)
The claim follows from `HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])`.
-/
theorem cP_cP (P : Pl D.host.E) : cP (cP P) = P :=
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_cP, mem_cP, cO_cO])

/- English proof (translation)
Establish `: {r : 𝓞 D.host.E | ∃ s ∈ P.asIdeal, algebraMap _ D.host.E r = star (algebraMap _ D.host.E s)} = ((cP P).asIdeal : Set (𝓞 D.host.E))`. Use extensionality with `r`. Use `⟨fun ⟨s, hs, e⟩ => ?_, fun h => ⟨cO D r, h, (star_star _).symm⟩⟩` and prove the remaining obligations. Establish `: r = cO D s` using `RingOfIntegers.ext e`. Express the relevant statement in the definitionally equal form `cO D r ∈ P.asIdeal`.

Rewrite using `[this, cO_cO]` and apply the resulting hypothesis. Rewrite using `[Formalism.HermitianLatticesTheory.conjIdeal, this, Ideal.span_eq]`.
-/
theorem conjIdeal_eq_cP (P : Pl D.host.E) : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (cP P).asIdeal := by
  have : {r : 𝓞 D.host.E | ∃ s ∈ P.asIdeal, algebraMap _ D.host.E r = star (algebraMap _ D.host.E s)} =
      ((cP P).asIdeal : Set (𝓞 D.host.E)) := by
    ext r
    refine ⟨fun ⟨s, hs, e⟩ => ?_, fun h => ⟨cO D r, h, (star_star _).symm⟩⟩
    have : r = cO D s := RingOfIntegers.ext e
    change cO D r ∈ P.asIdeal
    rwa [this, cO_cO]
  rw [Formalism.HermitianLatticesTheory.conjIdeal, this, Ideal.span_eq]

/- English proof (translation)
Rewrite using `[mem_cP, map_natCast]`.
-/
theorem nat_mem_cP (P : Pl D.host.E) (n : ℕ) : (n : 𝓞 D.host.E) ∈ (cP P).asIdeal ↔ (n : 𝓞 D.host.E) ∈ P.asIdeal := by
  rw [mem_cP, map_natCast]

/- English proof (translation)
The claim follows from `(Ideal.map_symm (cO D)).symm`.
-/
theorem asIdeal_cP (P : Pl D.host.E) : (cP P).asIdeal = P.asIdeal.map (cO D).symm :=
  (Ideal.map_symm (cO D)).symm

/- English proof (translation)
Rewrite using `[asIdeal_cP, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap, map_natCast]`.
-/
theorem nat_mem_sq_cP (P : Pl D.host.E) (n : ℕ) :
    (n : 𝓞 D.host.E) ∈ (cP P).asIdeal ^ 2 ↔ (n : 𝓞 D.host.E) ∈ P.asIdeal ^ 2 := by
  rw [asIdeal_cP, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap, map_natCast]

/- English proof (translation)
The claim follows from `(Nat.card_congr (Ideal.quotientEquiv P.asIdeal (cP P).asIdeal (cO D).symm (asIdeal_cP P)).toEquiv).symm`.
-/
theorem card_cP (P : Pl D.host.E) : Nat.card (kP (cP P)) = Nat.card (kP P) :=
  (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (cP P).asIdeal (cO D).symm (asIdeal_cP P)).toEquiv).symm

/- English proof (translation)
Use `or_congr_right ⟨fun ⟨P', h, e⟩ => ?_, fun h => ⟨_, h, (isConjPl_iff _ _).2 (cP_cP P).symm⟩⟩` and prove the remaining obligations. Rewrite using `[(isConjPl_iff _ _).1 e, cP_cP]`. Conclude with `h`.
-/
theorem mem_or_conj {Q : Finset (Pl D.host.E)} {P : Pl D.host.E} :
    (P ∈ Q ∨ ∃ P' ∈ Q, Lev.IsConjPl P' P) ↔ P ∈ Q ∨ cP P ∈ Q := by
  refine or_congr_right ⟨fun ⟨P', h, e⟩ => ?_, fun h => ⟨_, h, (isConjPl_iff _ _).2 (cP_cP P).symm⟩⟩
  rw [(isConjPl_iff _ _).1 e, cP_cP]
  exact h

/- English proof (translation)
Rewrite using `[Bridge.SplitOff, conjIdeal_eq_cP]`. Use `and_congr (not_congr ⟨fun h => HeightOneSpectrum.ext h, fun h => by rw [h]⟩) (and_congr_right fun _ => ?_)` and prove the remaining obligations. Conclude with `⟨fun h hm => h _ hm rfl, fun h Q hQ e => h ((HeightOneSpectrum.ext e : Q = cP P) ▸ hQ)⟩`.
-/
theorem splitOff_iff {P : Pl D.host.E} {S : Set (Pl D.host.E)} : Bridge.SplitOff P S ↔ cP P ≠ P ∧ P ∉ S ∧ cP P ∉ S := by
  rw [Bridge.SplitOff, conjIdeal_eq_cP]
  refine and_congr (not_congr ⟨fun h => HeightOneSpectrum.ext h, fun h => by rw [h]⟩) (and_congr_right fun _ => ?_)
  exact ⟨fun h hm => h _ hm rfl, fun h Q hQ e => h ((HeightOneSpectrum.ext e : Q = cP P) ▸ hQ)⟩

/- English proof (translation)
Use `choose r hr using fun a : (kP P)ˣ => Ideal.Quotient.mk_surjective (a : kP P)`. Use `haveI : P.asIdeal.IsPrime := P.isPrime`. Establish `hn : ∀ {b : 𝓞 D.host.E} {a : (kP P)ˣ}, Ideal.Quotient.mk P.asIdeal b = a → b ∉ P.asIdeal` using `fun {b a} e hb => a.ne_zero (e ▸ Ideal.Quotient.eq_zero_iff_mem.2 hb)`. Establish `h0 : ∀ {b : 𝓞 D.host.E}, b ∉ P.asIdeal → (b : D.host.E) ≠ 0` using `fun {b} hb e => hb ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)`. Establish `h1 : ∀ {b : 𝓞 D.host.E}, b ∉ P.asIdeal → P.valuation D.host.E (b : D.host.E) = 1` using `fun {b} hb => le_antisymm (HeightOneSpectrum.valuation_le_one _ _) (not_lt.1 fun h => hb ((HeightOneSpectrum.valuation_lt_one_iff_mem _ _).1 h))`.

Set `f : (kP P)ˣ → ℂˣ` to `fun a => χ.locK P (Units.mk0 _ (h0 (hn (hr a))))`. Establish `hf : ∀ (a : (kP P)ˣ) (b : 𝓞 D.host.E) (x : D.host.Eˣ), (x : D.host.E) = b → Ideal.Quotient.mk P.asIdeal b = a → f a = χ.locK P x` using `fun a b x hx hb => by`. Rewrite using `[GlobalTheory.NormOneUnit.locK_tame ht (y := Units.mk0 _ (h0 (hn (hr a)))) (h1 (hn (hr a)))]`. Rewrite using `[hx]`. Conclude with `(HeightOneSpectrum.valuation_lt_one_iff_mem P (b - r a)).2 (Ideal.Quotient.eq.1 (hb.trans (hr a).symm))`.

Use `⟨MonoidHom.mk' f fun a a' => ?_, fun b k u hk hu => hf u b k hk hu.symm⟩` and prove the remaining obligations. Rewrite using `[hf _ (r a * r a') (Units.mk0 _ (h0 (hn (hr a))) * Units.mk0 _ (h0 (hn (hr a')))) rfl (by rw [map_mul, hr, hr, Units.val_mul]), map_mul]`.
-/
theorem exists_isRes {χ : HChar D.host.E} {P : Pl D.host.E} (ht : χ.TameAt P) : ∃ c, IsRes χ P c := by
  choose r hr using fun a : (kP P)ˣ => Ideal.Quotient.mk_surjective (a : kP P)
  haveI : P.asIdeal.IsPrime := P.isPrime
  have hn : ∀ {b : 𝓞 D.host.E} {a : (kP P)ˣ}, Ideal.Quotient.mk P.asIdeal b = a → b ∉ P.asIdeal := fun {b a} e hb =>
    a.ne_zero (e ▸ Ideal.Quotient.eq_zero_iff_mem.2 hb)
  have h0 : ∀ {b : 𝓞 D.host.E}, b ∉ P.asIdeal → (b : D.host.E) ≠ 0 := fun {b} hb e =>
    hb ((RingOfIntegers.coe_eq_zero_iff.1 e) ▸ zero_mem _)
  have h1 : ∀ {b : 𝓞 D.host.E}, b ∉ P.asIdeal → P.valuation D.host.E (b : D.host.E) = 1 := fun {b} hb =>
    le_antisymm (HeightOneSpectrum.valuation_le_one _ _)
      (not_lt.1 fun h => hb ((HeightOneSpectrum.valuation_lt_one_iff_mem _ _).1 h))
  let f : (kP P)ˣ → ℂˣ := fun a => χ.locK P (Units.mk0 _ (h0 (hn (hr a))))
  have hf : ∀ (a : (kP P)ˣ) (b : 𝓞 D.host.E) (x : D.host.Eˣ), (x : D.host.E) = b → Ideal.Quotient.mk P.asIdeal b = a →
      f a = χ.locK P x := fun a b x hx hb => by
    rw [GlobalTheory.NormOneUnit.locK_tame ht (y := Units.mk0 _ (h0 (hn (hr a)))) (h1 (hn (hr a)))]
    rw [hx]
    exact (HeightOneSpectrum.valuation_lt_one_iff_mem P (b - r a)).2 (Ideal.Quotient.eq.1 (hb.trans (hr a).symm))
  refine ⟨MonoidHom.mk' f fun a a' => ?_, fun b k u hk hu => hf u b k hk hu.symm⟩
  rw [hf _ (r a * r a') (Units.mk0 _ (h0 (hn (hr a))) * Units.mk0 _ (h0 (hn (hr a')))) rfl
    (by rw [map_mul, hr, hr, Units.val_mul]), map_mul]

end Places

section Transfer

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

/- English proof (translation)
Use `choose xiR hxiR using fun v => exists_isRes (h4 v)`. Establish `k : ∀ P ∈ Q, ∃ P' ∈ R.Q t, P = P' ∨ P = cP P'` using `fun P hP => ((hc P).1 (Or.inl hP)).elim (fun h => ⟨P, h, Or.inl rfl⟩) fun h => ⟨_, h, Or.inr (cP_cP P).symm⟩`. Establish `kn : ∀ P ∈ Q, ∃ P' ∈ R.Q t, (∀ n : ℕ, (n : 𝓞 D.host.E) ∈ P.asIdeal ↔ (n : 𝓞 D.host.E) ∈ P'.asIdeal) ∧ (∀ n : ℕ, (n : 𝓞 D.host.E) ∈ P.asIdeal ^ 2 ↔ (n : 𝓞 D.host.E) ∈ P'.asIdeal ^ 2) ∧ Nat.card (kP P) = Nat.card (kP P') ∧ cP P ≠ P` using `fun P hP => by`. Take `⟨P', h, e⟩` from `k P hP`. Establish `hne : cP P' ≠ P'` using `fun e => (hL.Q_pl t P' h).2 P' h ((isConjPl_iff _ _).2 e.symm)`.

Break down `e with rfl | rfl` into its components or cases. Conclude with `⟨P, h, fun _ => Iff.rfl, fun _ => Iff.rfl, rfl, hne⟩`. Conclude with `⟨P', h, nat_mem_cP P', nat_mem_sq_cP P', card_cP P', by rw [cP_cP]; exact hne.symm⟩`. Use `⟨xiR, h1, h2, h3, h4, fun P hP => ⟨?_, fun P' hP' hc' => ?_⟩, fun P hP => ?_, fun p hp => ?_, fun P => ?_, fun P _ => hxiR P, fun P hP => ?_, fun i P hP => ?_, fun P hP P' hP' => hch.one P (hQ P hP) P' (hQ P' hP'), fun P hP => ?_⟩` and prove the remaining obligations. Take `⟨P', h, -, e2, e3, -⟩` from `kn P hP`.

Take `⟨q, a1, a2, a3, a4⟩` from `(hL.Q_pl t P' h).1`. Conclude with `⟨q, a1, e3.trans a2, fun hm => a3 ((e2 q).1 hm), a4⟩`. Take `⟨-, -, -, -, -, hne⟩` from `kn P hP`. Establish `e` using `(isConjPl_iff _ _).1 hc'`. Conclude with `(hch.pair P P' (isConjPl_of_lev hc') (e ▸ hne.symm)).1 (hQ P hP) (hQ P' hP')`.

Take `⟨P', h, e1, -⟩` from `kn P hP`. Conclude with `⟨fun hm => (hL.Q_off t P' h).1 ((e1 _).1 hm), fun u hm => (hL.Q_off t P' h).2 u ((e1 _).1 hm)⟩`. Take `⟨𝔭, h𝔭⟩` from `hL.Q_de p hp`. Conclude with `⟨𝔭, h𝔭, fun P hP hm => h𝔭 t P (hde p hp P hP hm) hm⟩`. Rewrite using `[h5, hL.Q_ram, mem_or_conj, mem_or_conj, hc]`.

Take `⟨P', h, -, -, e3, -⟩` from `kn P hP`. Rewrite using `[e3]`. Conclude with `hF.roots t P' (Or.inr h)`. Take `⟨g, c0R, c0L, ht⟩` from `hF.tie`. Rewrite `hP` using `[splitOff_iff]`.

Establish `hno : ¬ (R.pl P ∈ R.Q t ∨ cP (R.pl P) ∈ R.Q t)` using `fun h => ((hc _).2 h).elim (fun h => hP.2.1 (Or.inr h)) fun h => hP.2.2 (Or.inr h)`. Establish `hok : P ∈ A.ok t` using `(ht.ok t P).2 (splitOff_iff.2 ⟨hP.1, fun h => h.elim (fun h => hP.2.1 (Or.inl h)) fun h => hno (Or.inl h), fun h => h.elim (fun h => hP.2.2 (Or.inl h)) fun h => hno (Or.inr h)⟩)`. Establish `hu : (R.xiH t).UnrAt (R.pl P)`. Assume the negation of the conclusion as `h`. Conclude with `hno (mem_or_conj.1 ((hL.Q_ram t _).1 h))`.

Take `⟨y, hy⟩` from `h6 _ hu`. Establish `hy0 : y ≠ 0`. Introduce and unpack `rfl`. Rewrite `hy` using `[map_zero, zero_mul]`. Conclude with `Units.ne_zero _ hy.symm`.

Use `⟨A.muVal i t P * Units.mk0 y hy0, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, map_mul, hF.muVal i t P hok, HChar.val_mul, HChar.val_mul, Units.val_mul, Units.val_mul, ← hy, Units.val_mk0]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨P', h, e1, -⟩` from `kn P hP`. Conclude with `fun hm => hG.2 t P' h ((e1 _).1 hm)`.
-/
theorem twLev_of_conj {R : RealDat D A Ks} (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (hG : QGuard R) (t : T0)
    {χ : HChar D.host.E} {xi : (AE D)ˣ →* Circle} {Q : Finset (Pl D.host.E)} {ch : Set (Pl D.host.E)} (hch : IsChoice ch)
    (hQ : ∀ P ∈ Q, P ∈ ch) (hc : ∀ P, (P ∈ Q ∨ cP P ∈ Q) ↔ (P ∈ R.Q t ∨ cP P ∈ R.Q t))
    (hde : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∀ P ∈ Q, ((p : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → P ∈ R.Q t)
    (h1 : ChrEq xi χ) (h2 : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) (h3 : χ.TrivOn D.host.F) (h4 : ∀ v, χ.TameAt v)
    (h5 : ∀ v, χ.UnrAt v ↔ (R.xiH t).UnrAt v)
    (h6 : ∀ v, (R.xiH t).UnrAt v → ∃ y : D.what₂.LL, D.what₂.embLL y * ((R.xiH t).val v : ℂˣ) = (χ.val v : ℂˣ)) :
    ∃ xiR, TwLev R χ xi Q xiR := by
  choose xiR hxiR using fun v => exists_isRes (h4 v)
  have k : ∀ P ∈ Q, ∃ P' ∈ R.Q t, P = P' ∨ P = cP P' := fun P hP =>
    ((hc P).1 (Or.inl hP)).elim (fun h => ⟨P, h, Or.inl rfl⟩) fun h => ⟨_, h, Or.inr (cP_cP P).symm⟩
  have kn : ∀ P ∈ Q, ∃ P' ∈ R.Q t, (∀ n : ℕ, (n : 𝓞 D.host.E) ∈ P.asIdeal ↔ (n : 𝓞 D.host.E) ∈ P'.asIdeal) ∧
      (∀ n : ℕ, (n : 𝓞 D.host.E) ∈ P.asIdeal ^ 2 ↔ (n : 𝓞 D.host.E) ∈ P'.asIdeal ^ 2) ∧ Nat.card (kP P) = Nat.card (kP P') ∧
      cP P ≠ P := fun P hP => by
    obtain ⟨P', h, e⟩ := k P hP
    have hne : cP P' ≠ P' := fun e => (hL.Q_pl t P' h).2 P' h ((isConjPl_iff _ _).2 e.symm)
    rcases e with rfl | rfl
    · exact ⟨P, h, fun _ => Iff.rfl, fun _ => Iff.rfl, rfl, hne⟩
    · exact ⟨P', h, nat_mem_cP P', nat_mem_sq_cP P', card_cP P', by rw [cP_cP]; exact hne.symm⟩
  refine ⟨xiR, h1, h2, h3, h4, fun P hP => ⟨?_, fun P' hP' hc' => ?_⟩, fun P hP => ?_, fun p hp => ?_, fun P => ?_,
    fun P _ => hxiR P, fun P hP => ?_, fun i P hP => ?_, fun P hP P' hP' => hch.one P (hQ P hP) P' (hQ P' hP'), fun P hP => ?_⟩
  · obtain ⟨P', h, -, e2, e3, -⟩ := kn P hP
    obtain ⟨q, a1, a2, a3, a4⟩ := (hL.Q_pl t P' h).1
    exact ⟨q, a1, e3.trans a2, fun hm => a3 ((e2 q).1 hm), a4⟩
  · obtain ⟨-, -, -, -, -, hne⟩ := kn P hP
    have e := (isConjPl_iff _ _).1 hc'
    exact (hch.pair P P' (isConjPl_of_lev hc') (e ▸ hne.symm)).1 (hQ P hP) (hQ P' hP')
  · obtain ⟨P', h, e1, -⟩ := kn P hP
    exact ⟨fun hm => (hL.Q_off t P' h).1 ((e1 _).1 hm), fun u hm => (hL.Q_off t P' h).2 u ((e1 _).1 hm)⟩
  · obtain ⟨𝔭, h𝔭⟩ := hL.Q_de p hp
    exact ⟨𝔭, h𝔭, fun P hP hm => h𝔭 t P (hde p hp P hP hm) hm⟩
  · rw [h5, hL.Q_ram, mem_or_conj, mem_or_conj, hc]
  · obtain ⟨P', h, -, -, e3, -⟩ := kn P hP
    rw [e3]
    exact hF.roots t P' (Or.inr h)
  · obtain ⟨g, c0R, c0L, ht⟩ := hF.tie
    rw [splitOff_iff] at hP
    have hno : ¬ (R.pl P ∈ R.Q t ∨ cP (R.pl P) ∈ R.Q t) := fun h =>
      ((hc _).2 h).elim (fun h => hP.2.1 (Or.inr h)) fun h => hP.2.2 (Or.inr h)
    have hok : P ∈ A.ok t := (ht.ok t P).2 (splitOff_iff.2 ⟨hP.1, fun h => h.elim (fun h => hP.2.1 (Or.inl h)) fun h => hno (Or.inl h),
      fun h => h.elim (fun h => hP.2.2 (Or.inl h)) fun h => hno (Or.inr h)⟩)
    have hu : (R.xiH t).UnrAt (R.pl P) := by
      by_contra h
      exact hno (mem_or_conj.1 ((hL.Q_ram t _).1 h))
    obtain ⟨y, hy⟩ := h6 _ hu
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hy
      exact Units.ne_zero _ hy.symm
    refine ⟨A.muVal i t P * Units.mk0 y hy0, ?_⟩
    rw [Units.val_mul, map_mul, hF.muVal i t P hok, HChar.val_mul, HChar.val_mul, Units.val_mul, Units.val_mul, ← hy, Units.val_mk0]
    ring
  · obtain ⟨P', h, e1, -⟩ := kn P hP
    exact fun hm => hG.2 t P' h ((e1 _).1 hm)

end Transfer

section Chars

variable {D : D7}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero]`. Both sides reduce to the same expression. Consider the case `succ n ih => rw [pow_succ, pow_succ, Formalism.L2.Host.HChar.loc_mul, ih]`.
-/
theorem loc_pow (χ : HChar D.host.E) (n : ℕ) (v : Pl D.host.E) (x : (v.adicCompletion D.host.E)ˣ) :
    (χ ^ n).loc v x = χ.loc v x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; rfl
  | succ n ih => rw [pow_succ, pow_succ, Formalism.L2.Host.HChar.loc_mul, ih]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rwa [zero_add, pow_one, pow_one]`. Consider the case `succ n ih => rw [pow_succ, pow_succ χ]`. Conclude with `GlobalTheory.TwistChr.chrEq_mul ih h`.
-/
theorem chrEq_pow {c : (AE D)ˣ →* Circle} {χ : HChar D.host.E} (h : ChrEq c χ) (n : ℕ) :
    ChrEq (c ^ (n + 1)) (χ ^ (n + 1)) := by
  induction n with
  | zero => rwa [zero_add, pow_one, pow_one]
  | succ n ih => rw [pow_succ, pow_succ χ]; exact GlobalTheory.TwistChr.chrEq_mul ih h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rwa [zero_add, pow_one]`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul h`.
-/
theorem trivOn_pow {χ : HChar D.host.E} (h : χ.TrivOn D.host.F) (n : ℕ) : (χ ^ (n + 1)).TrivOn D.host.F := by
  induction n with
  | zero => rwa [zero_add, pow_one]
  | succ n ih => rw [pow_succ]; exact ih.mul h

variable {q l : ℕ} {δ ψ : HChar D.host.E} {Q : Finset (Pl D.host.E)}

/- English proof (translation)
Introduce `hu` and use `by obtain ⟨n, hn⟩ := hψ.ord have h15 := (hδ.ine v hv (l ^ n)).1 fun x hx => by have h3 : ψ.loc v x ^ (l ^ n) = 1 := by rw [← loc_pow, show ψ ^ (l ^ n) = 1 from hn] rfl have h4 := hu x hx rw [Formalism.L2.Host.HChar.loc_mul, loc_pow] at h4 rw [eq_inv_of_mul_eq_one_left h4, inv_pow …`.
-/
theorem not_unr (hδ : IsDelta q δ) (hψ : IsPsi l Q ψ) (hl : l.Prime) (a : ℕ) {v : Pl D.host.E}
    (hv : (q : 𝓞 D.host.E) ∈ v.asIdeal) : ¬ (δ * ψ ^ a).UnrAt v := fun hu => by
  obtain ⟨n, hn⟩ := hψ.ord
  have h15 := (hδ.ine v hv (l ^ n)).1 fun x hx => by
    have h3 : ψ.loc v x ^ (l ^ n) = 1 := by
      rw [← loc_pow, show ψ ^ (l ^ n) = 1 from hn]
      rfl
    have h4 := hu x hx
    rw [Formalism.L2.Host.HChar.loc_mul, loc_pow] at h4
    rw [eq_inv_of_mul_eq_one_left h4, inv_pow, ← pow_mul, mul_comm, pow_mul, h3, one_pow, inv_one]
  have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hl).1 (Nat.prime_three.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
  have h5 := (Nat.prime_dvd_prime_iff_eq Nat.prime_five hl).1 (Nat.prime_five.dvd_of_dvd_pow (dvd_trans (by norm_num) h15))
  omega

/- English proof (translation)
Distinguish the cases in `hv : (q : 𝓞 D.host.E) ∈ v.asIdeal`. Establish `h` using `not_unr hδ hψ hl 1 hv`. Rewrite `h` using `[pow_one]`. Conclude with `iff_of_false (not_unr hδ hψ hl a hv) h`. Take `⟨n, hn⟩` from `hψ.ord`.

Use `forall₂_congr fun x hx => ?_` and prove the remaining obligations. Establish `h3 : ψ.loc v x ^ (l ^ n) = 1`. Rewrite using `[← loc_pow, show ψ ^ (l ^ n) = 1 from hn]`. Both sides reduce to the same expression. Rewrite using `[Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, hδ.unr v hv x hx, one_mul, one_mul, loc_pow]`.

Use `⟨fun h => ?_, fun h => by rw [h, one_pow]⟩` and prove the remaining obligations. Use `pow_gcd_eq_one.2 ⟨h, h3⟩` as an intermediate fact. Rewrite `this` using `[Nat.Coprime.gcd_eq_one (ha.pow_right n), pow_one]`. Then use the resulting hypothesis.
-/
theorem unr_iff (hδ : IsDelta q δ) (hψ : IsPsi l Q ψ) (hl : l.Prime) {a : ℕ} (ha : a.Coprime l) (v : Pl D.host.E) :
    (δ * ψ ^ a).UnrAt v ↔ (δ * ψ).UnrAt v := by
  by_cases hv : (q : 𝓞 D.host.E) ∈ v.asIdeal
  · have h := not_unr hδ hψ hl 1 hv
    rw [pow_one] at h
    exact iff_of_false (not_unr hδ hψ hl a hv) h
  · obtain ⟨n, hn⟩ := hψ.ord
    refine forall₂_congr fun x hx => ?_
    have h3 : ψ.loc v x ^ (l ^ n) = 1 := by
      rw [← loc_pow, show ψ ^ (l ^ n) = 1 from hn]
      rfl
    rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, hδ.unr v hv x hx, one_mul, one_mul, loc_pow]
    refine ⟨fun h => ?_, fun h => by rw [h, one_pow]⟩
    have := pow_gcd_eq_one.2 ⟨h, h3⟩
    rwa [Nat.Coprime.gcd_eq_one (ha.pow_right n), pow_one] at this

/- English proof (translation)
Take `⟨n, hn⟩` from `hψ.ord`. Take `⟨m, hm0, hm⟩` from `hδ.fin`. Use `⟨m * l ^ n, Nat.mul_pos hm0 (pow_pos hl.pos n), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(δ * ψ ^ a) ^ (m * l ^ n) = 1`. Rewrite using `[mul_pow, pow_mul δ, show δ ^ m = 1 from hm, one_pow, one_mul, ← pow_mul, mul_comm m, ← mul_assoc, mul_comm a, mul_assoc, pow_mul, show ψ ^ (l ^ n) = 1 from hn, one_pow]`.
-/
theorem fin_mul (hδ : IsDelta q δ) (hψ : IsPsi l Q ψ) (hl : l.Prime) (a : ℕ) : ∃ n : ℕ, 0 < n ∧ (δ * ψ ^ a).OrderDvd n := by
  obtain ⟨n, hn⟩ := hψ.ord
  obtain ⟨m, hm0, hm⟩ := hδ.fin
  refine ⟨m * l ^ n, Nat.mul_pos hm0 (pow_pos hl.pos n), ?_⟩
  change (δ * ψ ^ a) ^ (m * l ^ n) = 1
  rw [mul_pow, pow_mul δ, show δ ^ m = 1 from hm, one_pow, one_mul, ← pow_mul, mul_comm m, ← mul_assoc, mul_comm a, mul_assoc, pow_mul,
    show ψ ^ (l ^ n) = 1 from hn, one_pow]

/- English proof (translation)
Introduce `x hx h1` and use `by rw [Formalism.L2.Host.HChar.loc_mul, loc_pow, hδ.tame v x hx h1, hψ.tame v x hx h1, one_pow, one_mul]`.
-/
theorem tame_mul (hδ : IsDelta q δ) (hψ : IsPsi l Q ψ) (a : ℕ) (v : Pl D.host.E) : (δ * ψ ^ a).TameAt v := fun x hx h1 => by
  rw [Formalism.L2.Host.HChar.loc_mul, loc_pow, hδ.tame v x hx h1, hψ.tame v x hx h1, one_pow, one_mul]

/- English proof (translation)
Establish `hu : ¬ IsUnit (q : 𝓞 D.host.E)` using `fun h => by`. Establish `h1` using `h.map (Algebra.norm ℤ)`. Rewrite `h1` using `[show (q : 𝓞 D.host.E) = algebraMap ℤ _ (q : ℤ) by simp, Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast]`. Conclude with `hq.one_lt.ne' h1`. Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hu)`.

Establish `hqM : (q : 𝓞 D.host.E) ∈ M` using `hle (Ideal.mem_span_singleton_self _)`. Use `⟨⟨M, hM.isPrime, fun e => ?_⟩, hqM⟩` and prove the remaining obligations. Rewrite `hqM` using `[e, Ideal.mem_bot]`. Conclude with `hq.ne_zero (by exact_mod_cast hqM)`.
-/
theorem exists_over {q : ℕ} (hq : q.Prime) : ∃ v : Pl D.host.E, (q : 𝓞 D.host.E) ∈ v.asIdeal := by
  have hu : ¬ IsUnit (q : 𝓞 D.host.E) := fun h => by
    have h1 := h.map (Algebra.norm ℤ)
    rw [show (q : 𝓞 D.host.E) = algebraMap ℤ _ (q : ℤ) by simp, Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne',
      Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at h1
    exact hq.one_lt.ne' h1
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_ne_top hu)
  have hqM : (q : 𝓞 D.host.E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, fun e => ?_⟩, hqM⟩
  rw [e, Ideal.mem_bot] at hqM
  exact hq.ne_zero (by exact_mod_cast hqM)

/- English proof (translation)
Use `haveI : CharZero (FractionRing (D.ntw.Ok i k)) := (ρ.ek i b k).charZero`. Establish `hn : D.ntw.l i ^ k ≠ 0` using `pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero`. Establish `h1 : ∀ σ, ψ σ ^ (D.ntw.l i ^ k) = 1` using `fun σ => by`. Take `⟨n, hn⟩` from `hψ.2.2.2.2.1 σ`. Establish `hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1` using `Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)`.

Rewrite using `[← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]`. Take `⟨a, ha, h⟩` from `GlobalTheory.charPowPrimeOrder_embeddings_differ_by_coprime_power _ (FractionRing (D.ntw.Ok i k)) _ k (D.ntw.lPrime i).out ((Units.map (algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k))).toMonoidHom).comp ψ) (fun g => by rw [MonoidHom.comp_apply, ← map_pow, h1, map_one]) (ρ …`. Use `⟨a, ha, MonoidHom.ext fun x => Circle.ext ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `ρ.rc.exists_sym x`. Establish `e1` using `charOf_eq ρ.rc (ρ.eOk i b k) hψ.2.2.1 hσ hn (h1 σ)`.

Establish `e2` using `charOf_eq ρ.rc (ρ'.eOk i b k) hψ.2.2.1 hσ hn (h1 σ)`. Rewrite using `[MonoidHom.pow_apply, Circle.coe_pow]`. Express the relevant statement in the definitionally equal form `((GlobalTheory.SeriesTie.charOf ρ'.rc (ρ'.eOk i b k) ψ x : Circle) : ℂ) = ((GlobalTheory.SeriesTie.charOf ρ.rc (ρ.eOk i b k) ψ x : Circle) : ℂ) ^ a`. Rewrite using `[hs, e1, e2]`. Use `h σ` as an intermediate fact.

Rewrite `this` using `[Units.val_pow_eq_pow_val, map_pow]`. Conclude with `this`.
-/
theorem exists_pow {ρ ρ' : Setup D.ntw} (hs : ρ'.rc = ρ.rc) {i : D.ntw.Tw} (b : Bool) {k : ℕ} {Q : Finset (Pl D.host.E)}
    {ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} (hψ : IntegralHeckeForms.TwOK i k Q ψ) :
    ∃ a : ℕ, a.Coprime (D.ntw.l i) ∧ (ρ'.tw i b k Q ψ).chi = (ρ.tw i b k Q ψ).chi ^ a := by
  haveI : CharZero (FractionRing (D.ntw.Ok i k)) := (ρ.ek i b k).charZero
  have hn : D.ntw.l i ^ k ≠ 0 := pow_ne_zero _ (D.ntw.lPrime i).out.ne_zero
  have h1 : ∀ σ, ψ σ ^ (D.ntw.l i ^ k) = 1 := fun σ => by
    obtain ⟨n, hn⟩ := hψ.2.2.2.2.1 σ
    have hz : D.ntw.zk i k ^ (D.ntw.l i ^ k) = 1 := Units.ext (by simpa using (D.ntw.zk_prim i k).pow_eq_one)
    rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  obtain ⟨a, ha, h⟩ := GlobalTheory.charPowPrimeOrder_embeddings_differ_by_coprime_power _ (FractionRing (D.ntw.Ok i k)) _ k
    (D.ntw.lPrime i).out ((Units.map (algebraMap (D.ntw.Ok i k) (FractionRing (D.ntw.Ok i k))).toMonoidHom).comp ψ)
    (fun g => by rw [MonoidHom.comp_apply, ← map_pow, h1, map_one]) (ρ.ek i b k) (ρ'.ek i b k)
  refine ⟨a, ha, MonoidHom.ext fun x => Circle.ext ?_⟩
  obtain ⟨σ, hσ⟩ := ρ.rc.exists_sym x
  have e1 := charOf_eq ρ.rc (ρ.eOk i b k) hψ.2.2.1 hσ hn (h1 σ)
  have e2 := charOf_eq ρ.rc (ρ'.eOk i b k) hψ.2.2.1 hσ hn (h1 σ)
  rw [MonoidHom.pow_apply, Circle.coe_pow]
  change ((GlobalTheory.SeriesTie.charOf ρ'.rc (ρ'.eOk i b k) ψ x : Circle) : ℂ) =
    ((GlobalTheory.SeriesTie.charOf ρ.rc (ρ.eOk i b k) ψ x : Circle) : ℂ) ^ a
  rw [hs, e1, e2]
  have := h σ
  rw [Units.val_pow_eq_pow_val, map_pow] at this
  exact this

end Chars

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}

/- English proof (translation)
Use `⟨if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, ?_, fun P => ?_⟩` and prove the remaining obligations. Use `split_ifs exacts [D.host.pde'_prime, D.host.pde_prime]`. Unfold `Formalism.L2.Host.CharFrame.delAt split_ifs exacts [C.isDel', C.isDel]`. Rewrite using `[← Finset.mem_coe, D.ntw.pD_eq]`. Both sides reduce to the same expression.
-/
theorem exists_delta (C : Formalism.L2.Host.CharFrame D) (i : D.ntw.Tw) : ∃ q : ℕ, q.Prime ∧ IsDelta q (C.delAt (D.ntw.l i)) ∧
    ∀ P : Pl D.host.E, P ∈ D.ntw.pD i ↔ (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  refine ⟨if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde, ?_, ?_, fun P => ?_⟩
  · split_ifs
    exacts [D.host.pde'_prime, D.host.pde_prime]
  · unfold Formalism.L2.Host.CharFrame.delAt
    split_ifs
    exacts [C.isDel', C.isDel]
  · rw [← Finset.mem_coe, D.ntw.pD_eq]
    rfl

open Classical in

/- English proof (translation)
Establish `hw'` using `(p.tw_iff w).1 hw`. Establish `hL` using `p.charW.base.lev`. Establish `hψ` using `p.Tp.psi_is w hw'`. Rewrite `hψ` using `[← ex.nch.twI_l]`. Establish `hl` using `(D.ntw.lPrime (ex.nch.twI w)).out`.

Establish `h2 : p.R.toRealDat.toLevCh.xiH (p.R.mu (D.plEq w)) = p.R.C.delAt (D.ntw.l (ex.nch.twI w)) * p.Tp.psi w`. Rewrite using `[← p.tupAt w, p.tupXi _ (Or.inr ⟨w, rfl⟩), (D.what₂.muAt_or w).resolve_left hw', p.Tp.xi_tw, ex.nch.twI_l]`. Take `⟨q, -, hδ, hq⟩` from `exists_delta p.R.C (ex.nch.twI w)`. Take `⟨k1, k2⟩` from `placesAt (j := j) hw hρ hp`. Simplify using `only [mem_or_conj] at k2`.

Establish `hch` using `hρ.ch (ex.nch.twI w)`. Establish `hQ : ∀ P, P ∈ (baseW ex w j ρ).de.Q ∪ half (ρ.ch (ex.nch.twI w)) (ex.nch.Q w) ↔ (P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w) ∧ P ∈ ρ.ch (ex.nch.twI w)` using `fun P => by`. Rewrite using `[Finset.mem_union, baseW, hρ.delta, or_and_right]`. Conclude with `or_congr mem_half mem_half`. Use `twLev_of_conj hL hF hG (p.R.mu (D.plEq w)) hch (fun P hP => ((hQ P).1 hP).2) (fun P => ?_) (fun r hr P hP hm => ?_) (GlobalTheory.TwistChr.chrEq_mul (hp.delta _ j _) hc) (fin_mul hδ hψ hl _) (hδ.triv.mul (trivOn_pow hψ.triv a)) (tame_mul hδ hψ _) (fun v => by rw [h2]; exact unr_i …` and prove the remaining obligations.

Rewrite using `[hQ, hQ, ← k2, ← k2, cP_cP, or_comm (a := cP P ∈ _) (b := P ∈ _), ← and_or_left, and_iff_left_iff_imp]`. Introduce `h`. Establish `hne : P ≠ cP P` using `fun e => by`. Establish `h' : P ∈ p.R.Q (p.R.mu (D.plEq w))` using `h.elim id fun h => e ▸ h`. Conclude with `(hL.Q_pl _ P h').2 P h' ((isConjPl_iff _ _).2 e)`.

Distinguish the cases in `hP : cP P ∈ ρ.ch (ex.nch.twI w)`. Conclude with `Or.inr hP`. Conclude with `Or.inl ((hch.pair P _ (isConjPl_of_lev ((isConjPl_iff _ _).2 rfl)) hne).2 hP)`. Break down `Finset.mem_union.1 hP with h | h` into its components or cases. Conclude with `((k1 P).1 h).1`.

Use `absurd ?_ (hlow P (mem_half.1 h).1)` and prove the remaining obligations. Rewrite using `[Nat.cast_mul]`. Break down `hr with rfl | rfl` into its components or cases. Use `exacts [Ideal.mul_mem_right _ _ hm, Ideal.mul_mem_left _ _ hm]`. Establish `hv' : v ∉ ex.nch.Q w` using `fun h => (hL.Q_ram _ v).2 (mem_or_conj.2 ((k2 v).2 (Or.inr h))) hv`.

Take `⟨y, hy⟩` from `hm.psiVal w hw' v ((hψ.ram v).2 hv')`. Establish `hy' : D.what₂.embLL y = (((p.Tp.psi w).val v : ℂˣ) : ℂ)` using `by simpa [Formalism.L2.Host.HChar.valTw] using hy`. Establish `hv2 : (p.Tp.psi w ^ (a + 1)).val v = (p.Tp.psi w).val v ^ (a + 1)` using `loc_pow _ _ _ _`. Use `⟨y ^ a, ?_⟩` and prove the remaining obligations. Rewrite using `[h2, map_pow, hy', Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_mul, hv2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem twLev_pow (hm : RecTies p) (hF : p.R.toRealDat.IsFam) (hG : QGuard p.R.toRealDat) (hw : D.plEq w ∈ p.R.twPl) (j : Fin D.R.m)
    (hlow : ∀ P ∈ ex.nch.Q w, ((D.host.pde * D.host.pde' : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hp : RealPin p.R p.cG ρ) {c : (AE D)ˣ →* Circle} {a : ℕ}
    (ha : (a + 1).Coprime (D.ntw.l (ex.nch.twI w))) (hc : ChrEq c (p.Tp.psi w ^ (a + 1))) :
    ∃ xiR, TwLev p.R.toRealDat (p.R.C.delAt (D.ntw.l (ex.nch.twI w)) * p.Tp.psi w ^ (a + 1)) ((baseW ex w j ρ).de.chi * c)
      ((baseW ex w j ρ).de.Q ∪ half (ρ.ch (ex.nch.twI w)) (ex.nch.Q w)) xiR := by
  have hw' := (p.tw_iff w).1 hw
  have hL := p.charW.base.lev
  have hψ := p.Tp.psi_is w hw'
  rw [← ex.nch.twI_l] at hψ
  have hl := (D.ntw.lPrime (ex.nch.twI w)).out
  have h2 : p.R.toRealDat.toLevCh.xiH (p.R.mu (D.plEq w)) = p.R.C.delAt (D.ntw.l (ex.nch.twI w)) * p.Tp.psi w := by
    rw [← p.tupAt w, p.tupXi _ (Or.inr ⟨w, rfl⟩), (D.what₂.muAt_or w).resolve_left hw', p.Tp.xi_tw, ex.nch.twI_l]
  obtain ⟨q, -, hδ, hq⟩ := exists_delta p.R.C (ex.nch.twI w)
  obtain ⟨k1, k2⟩ := placesAt (j := j) hw hρ hp
  simp only [mem_or_conj] at k2
  have hch := hρ.ch (ex.nch.twI w)
  have hQ : ∀ P, P ∈ (baseW ex w j ρ).de.Q ∪ half (ρ.ch (ex.nch.twI w)) (ex.nch.Q w) ↔
      (P ∈ D.ntw.pD (ex.nch.twI w) ∨ P ∈ ex.nch.Q w) ∧ P ∈ ρ.ch (ex.nch.twI w) := fun P => by
    rw [Finset.mem_union, baseW, hρ.delta, or_and_right]
    exact or_congr mem_half mem_half
  refine twLev_of_conj hL hF hG (p.R.mu (D.plEq w)) hch (fun P hP => ((hQ P).1 hP).2) (fun P => ?_) (fun r hr P hP hm => ?_)
    (GlobalTheory.TwistChr.chrEq_mul (hp.delta _ j _) hc) (fin_mul hδ hψ hl _) (hδ.triv.mul (trivOn_pow hψ.triv a)) (tame_mul hδ hψ _)
    (fun v => by rw [h2]; exact unr_iff hδ hψ hl ha v) fun v hv => ?_
  · rw [hQ, hQ, ← k2, ← k2, cP_cP, or_comm (a := cP P ∈ _) (b := P ∈ _), ← and_or_left, and_iff_left_iff_imp]
    intro h
    have hne : P ≠ cP P := fun e => by
      have h' : P ∈ p.R.Q (p.R.mu (D.plEq w)) := h.elim id fun h => e ▸ h
      exact (hL.Q_pl _ P h').2 P h' ((isConjPl_iff _ _).2 e)
    by_cases hP : cP P ∈ ρ.ch (ex.nch.twI w)
    · exact Or.inr hP
    · exact Or.inl ((hch.pair P _ (isConjPl_of_lev ((isConjPl_iff _ _).2 rfl)) hne).2 hP)
  · rcases Finset.mem_union.1 hP with h | h
    · exact ((k1 P).1 h).1
    · refine absurd ?_ (hlow P (mem_half.1 h).1)
      rw [Nat.cast_mul]
      rcases hr with rfl | rfl
      exacts [Ideal.mul_mem_right _ _ hm, Ideal.mul_mem_left _ _ hm]
  · have hv' : v ∉ ex.nch.Q w := fun h => (hL.Q_ram _ v).2 (mem_or_conj.2 ((k2 v).2 (Or.inr h))) hv
    obtain ⟨y, hy⟩ := hm.psiVal w hw' v ((hψ.ram v).2 hv')
    have hy' : D.what₂.embLL y = (((p.Tp.psi w).val v : ℂˣ) : ℂ) := by simpa [Formalism.L2.Host.HChar.valTw] using hy
    have hv2 : (p.Tp.psi w ^ (a + 1)).val v = (p.Tp.psi w).val v ^ (a + 1) := loc_pow _ _ _ _
    refine ⟨y ^ a, ?_⟩
    rw [h2, map_pow, hy', Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_mul, hv2]
    push_cast
    ring

end Point

end GlobalTheory.BigOn.Exp.TwConj.LevAt

namespace GlobalTheory.BigOn.Exp.TwConj

open LevAt in

/- English proof (translation)
Introduce `_ _ _ hA hC` and use `by refine AtTw.imp (AtTw.and hA (AtTw.and hC lowAt_holds)) fun Fm x hx i p hr hm w hw j H => ?_ obtain ⟨⟨a1, -, -⟩, a2, a3⟩ := H intro ρ ρ' hρ hρ' hp hs hA have hl := ((Fm.D x i).ntw.lPrime ((Fm.ex x hx i).nch.twI w)).out have hlow : ∀ P ∈ (Fm.ex x hx i).nch.Q w, (((Fm.D x i).hos …`.
-/
theorem twLevAt_holds : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → TwAdm → TwChr →
    GlobalTheory.BigOn.Exp.TwConj.TwLevAt := fun _ _ _ hA hC => by
  refine AtTw.imp (AtTw.and hA (AtTw.and hC lowAt_holds)) fun Fm x hx i p hr hm w hw j H => ?_
  obtain ⟨⟨a1, -, -⟩, a2, a3⟩ := H
  intro ρ ρ' hρ hρ' hp hs hA
  have hl := ((Fm.D x i).ntw.lPrime ((Fm.ex x hx i).nch.twI w)).out
  have hlow : ∀ P ∈ (Fm.ex x hx i).nch.Q w,
      (((Fm.D x i).host.pde * (Fm.D x i).host.pde' : ℕ) : 𝓞 (Fm.D x i).host.E) ∉ P.asIdeal := fun P hP h => by
    refine Finset.disjoint_left.1 a1.2.1 hP (a3 P ?_)
    rw [mul_assoc _ (Fm.D x i).host.pde, ← mul_assoc, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ h
  have pw : ∀ σ σ' : Setup (Fm.D x i).ntw, σ.Good → Adapted p w σ → σ'.rc = σ.rc →
      ∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w σ').chi (p.Tp.psi w ^ (a + 1)) := fun σ σ' hσ hσA e => by
    obtain ⟨a, ha, h⟩ := exists_pow e ((Fm.ex x hx i).nch.sd w) a1
    rcases a with _ | a
    · exact absurd (Nat.coprime_zero_left _ |>.1 ha) hl.one_lt.ne'
    · exact ⟨a, ha, by rw [twW, h]; exact chrEq_pow (a2 σ hσ hσA).1 a⟩
  obtain ⟨⟨a, ha, hc⟩, a', ha', hc'⟩ : (∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w ρ).chi (p.Tp.psi w ^ (a + 1))) ∧
      ∃ a : ℕ, (a + 1).Coprime ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) ∧
        ChrEq (twW (Fm.ex x hx i) w ρ').chi (p.Tp.psi w ^ (a + 1)) :=
    hA.elim (fun h => ⟨pw ρ ρ hρ h rfl, pw ρ ρ' hρ h hs.1⟩) fun h => ⟨pw ρ' ρ hρ' h hs.1.symm, pw ρ' ρ' hρ' h rfl⟩
  obtain ⟨xiR, h1⟩ := twLev_pow hm.2.2 p.charW.base.fam p.qGuard hw j hlow hρ hp ha hc
  obtain ⟨xiR', h2⟩ := twLev_pow hm.2.2 p.charW.base.fam p.qGuard hw j hlow hρ hp ha' hc'
  have hQ : (twW (Fm.ex x hx i) w ρ').Q = half (ρ.ch ((Fm.ex x hx i).nch.twI w)) ((Fm.ex x hx i).nch.Q w) := by
    simp only [Setup.tw, twistOf, hs.2.1]
  obtain ⟨q, hq, hδ, -⟩ := exists_delta p.R.C ((Fm.ex x hx i).nch.twI w)
  obtain ⟨v, hv⟩ := exists_over (D := Fm.D x i) hq
  have hψ := p.Tp.psi_is w ((p.tw_iff w).1 hw)
  rw [← (Fm.ex x hx i).nch.twI_l] at hψ
  have hne : ∀ n : ℕ, p.R.C.delAt ((Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w)) * p.Tp.psi w ^ n ≠ 1 := fun n e =>
    not_unr hδ hψ hl n hv (by rw [e]; exact fun _ _ => rfl)
  refine ⟨_, _, xiR, xiR', h1, hQ ▸ h2, hne _, hne _, or_iff_not_imp_left.2 fun e => ?_⟩
  rw [Ne, not_not] at e
  exact GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ h1.xi (e ▸ h2.xi)

end GlobalTheory.BigOn.Exp.TwConj
