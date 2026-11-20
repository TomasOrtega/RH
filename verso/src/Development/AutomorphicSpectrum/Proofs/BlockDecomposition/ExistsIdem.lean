import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.TiltIdem

variable {B R : Type} [CommRing B] [CommRing R]

/- English proof (translation)
Establish `hix : IsIdempotentElem (i x)`. Express the relevant statement in the definitionally equal form `i x * i x = i x`. Rewrite using `[← map_mul, hx.eq]`. Establish `hiy : IsIdempotentElem (i y)`. Express the relevant statement in the definitionally equal form `i y * i y = i y`.

Rewrite using `[← map_mul, hy.eq]`. Establish `hb : PrimeSpectrum.basicOpen (i x) = PrimeSpectrum.basicOpen (i y)`. Use extensionality with `p`. Conclude with `h p`. Establish `e : i x = i y` using `PrimeSpectrum.basicOpen_injOn_isIdempotentElem hix hiy hb`.

Conclude with `(hidem (i y) hiy).unique ⟨hx, e⟩ ⟨hy, rfl⟩`.
-/
theorem idem_eq (i : B →* R)
    (hidem : ∀ e : R, IsIdempotentElem e → ∃! e₀ : B, IsIdempotentElem e₀ ∧ i e₀ = e)
    {x y : B} (hx : IsIdempotentElem x) (hy : IsIdempotentElem y)
    (h : ∀ p : PrimeSpectrum R, i x ∉ p.asIdeal ↔ i y ∉ p.asIdeal) : x = y := by
  have hix : IsIdempotentElem (i x) := by
    change i x * i x = i x
    rw [← map_mul, hx.eq]
  have hiy : IsIdempotentElem (i y) := by
    change i y * i y = i y
    rw [← map_mul, hy.eq]
  have hb : PrimeSpectrum.basicOpen (i x) = PrimeSpectrum.basicOpen (i y) := by
    ext p
    exact h p
  have e : i x = i y := PrimeSpectrum.basicOpen_injOn_isIdempotentElem hix hiy hb
  exact (hidem (i y) hiy).unique ⟨hx, e⟩ ⟨hy, rfl⟩

/- English proof (translation)
Establish `hfib : ∀ a : ι, ∃ e : B, IsIdempotentElem e ∧ ∀ p : PrimeSpectrum R, i e ∉ p.asIdeal ↔ f p = a`. Introduce `a`. Establish `hc : IsClopen (f ⁻¹' {a})` using `f.isLocallyConstant.isClopen_fiber a`. Take `⟨ε, hε, hs⟩` from `PrimeSpectrum.isClopen_iff.1 hc`. Take `⟨e₀, ⟨he₀, rfl⟩, -⟩` from `hidem ε hε`.

Use `⟨e₀, he₀, fun p => ?_⟩` and prove the remaining obligations. Establish `: p ∈ f ⁻¹' {a} ↔ p ∈ PrimeSpectrum.basicOpen (i e₀)` using `by rw [hs]; rfl`. Conclude with `this.symm`. Use `choose e he hp using hfib`. Establish `hnot0 : ∀ p : PrimeSpectrum R, ¬ (i 0 ∉ p.asIdeal)` using `fun p h => h (by rw [h0]; exact p.asIdeal.zero_mem)`.

Establish `hmul : ∀ (x y : B) (p : PrimeSpectrum R), i (x * y) ∉ p.asIdeal ↔ i x ∉ p.asIdeal ∧ i y ∉ p.asIdeal`. Introduce `x y p`. Rewrite using `[map_mul, p.isPrime.mul_mem_iff_mem_or_mem]`. The claim follows by propositional logic. Establish `hort : OrthogonalIdempotents e`.

Use `⟨he, fun a b hab => ?_⟩` and prove the remaining obligations. Use `idem_eq i hidem ((he a).mul (he b)) IsIdempotentElem.zero fun p => ?_` and prove the remaining obligations. Use `iff_of_false ?_ (hnot0 p)` and prove the remaining obligations. Introduce `h`. Take `⟨h1, h2⟩` from `(hmul _ _ p).1 h`.

Conclude with `hab (((hp a p).1 h1).symm.trans ((hp b p).1 h2))`. Establish `hsum : IsIdempotentElem (∑ a, e a)` using `hort.isIdempotentElem_sum`. Establish `hc : IsIdempotentElem (1 - ∑ a, e a)` using `hsum.one_sub`. Establish `hce : ∀ a, (1 - ∑ b, e b) * e a = 0`. Introduce `a`.

Rewrite using `[sub_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single a, (he a).eq, sub_self]`. Conclude with `fun b _ hb => hort.ortho hb`. Conclude with `fun h => absurd (Finset.mem_univ a) h`. Establish `hone : 1 - ∑ a, e a = 0`. Use `idem_eq i hidem hc IsIdempotentElem.zero fun p => ?_` and prove the remaining obligations.

Use `iff_of_false ?_ (hnot0 p)` and prove the remaining obligations. Introduce `h`. Establish `h1 : i (e (f p)) ∉ p.asIdeal` using `(hp (f p) p).2 rfl`. Establish `h2` using `(hmul _ _ p).2 ⟨h, h1⟩`. Rewrite `h2` using `[hce]`.

Conclude with `hnot0 p h2`. Use `⟨e, ⟨hort, (sub_eq_zero.1 hone).symm⟩, hp, fun e' a he' h => ?_⟩` and prove the remaining obligations. Use `idem_eq i hidem (he'.mul (he a)) he' fun p => ?_` and prove the remaining obligations. Rewrite using `[hmul]`. Conclude with `⟨fun h' => h'.1, fun h' => ⟨h', (hp a p).2 (h p h')⟩⟩`.
-/
theorem exists_idem (i : B →* R) (h0 : i 0 = 0)
    (hidem : ∀ e : R, IsIdempotentElem e → ∃! e₀ : B, IsIdempotentElem e₀ ∧ i e₀ = e)
    {ι : Type} [Fintype ι] (f : LocallyConstant (PrimeSpectrum R) ι) :
    ∃ e : ι → B, CompleteOrthogonalIdempotents e ∧
      (∀ (a : ι) (p : PrimeSpectrum R), i (e a) ∉ p.asIdeal ↔ f p = a) ∧
      ∀ (e' : B) (a : ι), IsIdempotentElem e' →
        (∀ p : PrimeSpectrum R, i e' ∉ p.asIdeal → f p = a) → e' * e a = e' := by
  classical
  have hfib : ∀ a : ι, ∃ e : B, IsIdempotentElem e ∧
      ∀ p : PrimeSpectrum R, i e ∉ p.asIdeal ↔ f p = a := by
    intro a
    have hc : IsClopen (f ⁻¹' {a}) := f.isLocallyConstant.isClopen_fiber a
    obtain ⟨ε, hε, hs⟩ := PrimeSpectrum.isClopen_iff.1 hc
    obtain ⟨e₀, ⟨he₀, rfl⟩, -⟩ := hidem ε hε
    refine ⟨e₀, he₀, fun p => ?_⟩
    have : p ∈ f ⁻¹' {a} ↔ p ∈ PrimeSpectrum.basicOpen (i e₀) := by rw [hs]; rfl
    exact this.symm
  choose e he hp using hfib
  have hnot0 : ∀ p : PrimeSpectrum R, ¬ (i 0 ∉ p.asIdeal) := fun p h => h (by rw [h0]; exact p.asIdeal.zero_mem)
  have hmul : ∀ (x y : B) (p : PrimeSpectrum R), i (x * y) ∉ p.asIdeal ↔ i x ∉ p.asIdeal ∧ i y ∉ p.asIdeal := by
    intro x y p
    rw [map_mul, p.isPrime.mul_mem_iff_mem_or_mem]
    tauto
  have hort : OrthogonalIdempotents e := by
    refine ⟨he, fun a b hab => ?_⟩
    refine idem_eq i hidem ((he a).mul (he b)) IsIdempotentElem.zero fun p => ?_
    refine iff_of_false ?_ (hnot0 p)
    intro h
    obtain ⟨h1, h2⟩ := (hmul _ _ p).1 h
    exact hab (((hp a p).1 h1).symm.trans ((hp b p).1 h2))
  have hsum : IsIdempotentElem (∑ a, e a) := hort.isIdempotentElem_sum
  have hc : IsIdempotentElem (1 - ∑ a, e a) := hsum.one_sub
  have hce : ∀ a, (1 - ∑ b, e b) * e a = 0 := by
    intro a
    rw [sub_mul, one_mul, Finset.sum_mul, Finset.sum_eq_single a, (he a).eq, sub_self]
    · exact fun b _ hb => hort.ortho hb
    · exact fun h => absurd (Finset.mem_univ a) h
  have hone : 1 - ∑ a, e a = 0 := by
    refine idem_eq i hidem hc IsIdempotentElem.zero fun p => ?_
    refine iff_of_false ?_ (hnot0 p)
    intro h
    have h1 : i (e (f p)) ∉ p.asIdeal := (hp (f p) p).2 rfl
    have h2 := (hmul _ _ p).2 ⟨h, h1⟩
    rw [hce] at h2
    exact hnot0 p h2
  refine ⟨e, ⟨hort, (sub_eq_zero.1 hone).symm⟩, hp, fun e' a he' h => ?_⟩
  refine idem_eq i hidem (he'.mul (he a)) he' fun p => ?_
  rw [hmul]
  exact ⟨fun h' => h'.1, fun h' => ⟨h', (hp a p).2 (h p h')⟩⟩

/- English proof (translation)
Express the relevant statement in the definitionally equal form `A.th (WittVector.teichmuller l 0) = 0`. Rewrite using `[WittVector.teichmuller_zero, map_zero]`.
-/
theorem sharp_zero' {l : ℕ} [Fact l.Prime] (A : PAlg l) : A.sharp 0 = 0 := by
  change A.th (WittVector.teichmuller l 0) = 0
  rw [WittVector.teichmuller_zero, map_zero]

/- English proof (translation)
Introduce `l _ H A hA ι _ f`. Set `i : A.A →* A.Ug` to `(algebraMap A.U A.Ug : A.U →* A.Ug).comp A.sharp`. Establish `h0 : i 0 = 0`. Express the relevant statement in the definitionally equal form `algebraMap A.U A.Ug (A.sharp 0) = 0`. Rewrite using `[sharp_zero', map_zero]`.

Set `f' : LocallyConstant (PrimeSpectrum A.Ug) ι` to `⟨f, f.isLocallyConstant⟩`. Conclude with `exists_idem i h0 (H.idem A hA) f'`.
-/
theorem lcIdem : CrystallineSemistableComparison.E.LcIdem := by
  intro l _ H A hA ι _ f
  let i : A.A →* A.Ug := (algebraMap A.U A.Ug : A.U →* A.Ug).comp A.sharp
  have h0 : i 0 = 0 := by
    change algebraMap A.U A.Ug (A.sharp 0) = 0
    rw [sharp_zero', map_zero]
  let f' : LocallyConstant (PrimeSpectrum A.Ug) ι := ⟨f, f.isLocallyConstant⟩
  exact exists_idem i h0 (H.idem A hA) f'

end GlobalTheory.CompanionTheory.TiltIdem
