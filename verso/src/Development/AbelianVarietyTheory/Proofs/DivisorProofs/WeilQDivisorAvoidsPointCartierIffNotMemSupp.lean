import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.PairStep

open CategoryTheory AlgebraicGeometry TopologicalSpace in
set_option autoImplicit false in
/- English proof (translation)
Take `⟨U, hzU, a, rfl⟩` from `hreg.exists_fnOf`. Take `⟨V, hV, hzV, hVU⟩` from `(Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hzU`. Establish `hV' : IsAffineOpen V` using `hV`. Establish `hgV : genericPoint X ∈ V` using `((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨z, trivial, hzV⟩`. Rewrite `hf`, `hnu`, the goal using `[← _root_.GlobalTheory.Cartier.fnOf_resG hVU hgV a]`.

Generalize the expression as in `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hVU a = b at hf hnu ⊢`. Use `haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩`. Use `haveI : Nonempty V := ⟨⟨z, hzV⟩⟩`. Establish `hmem : ∀ q : PrimeSpectrum Γ(X, V), hV'.fromSpec q ∈ V` using `fun q => by`. Establish `: hV'.fromSpec q ∈ Set.range hV'.fromSpec` using `Set.mem_range_self q`.

Rewrite `this` using `[hV'.range_fromSpec]`. Then use the resulting hypothesis. Establish `key : ∀ q : PrimeSpectrum Γ(X, V), _root_.GlobalTheory.Cartier.UnitAt (hV'.fromSpec q) (_root_.GlobalTheory.Cartier.fnOf V hgV b) ↔ b ∉ q.asIdeal`. Introduce `q`. Rewrite using `[_root_.GlobalTheory.Cartier.unitAt_fnOf_iff (hmem q) hgV b]`. Establish `: hV'.fromSpec q ∈ X.basicOpen b ↔ q ∈ PrimeSpectrum.basicOpen b`.

Rewrite using `[← hV'.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression. Rewrite using `[this, PrimeSpectrum.mem_basicOpen]`. Use `set p := hV'.primeIdealOf ⟨z, hzV⟩`. Establish `hpz : hV'.fromSpec p = z` using `hV'.fromSpec_primeIdealOf ⟨z, hzV⟩`.

Establish `hbp : b ∈ p.asIdeal`. Assume the negation of the conclusion as `h`. Conclude with `hnu (hpz ▸ (key p).mpr h)`. Take `⟨P, hPmin, hPp⟩` from `Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem _).mpr hbp)`. Use `haveI hPprime : P.IsPrime := hPmin.1.1`.

Use `set q : PrimeSpectrum Γ(X, V) := ⟨P, hPprime⟩`. Establish `hbP : b ∈ P` using `(Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2`. Use `⟨hV'.fromSpec q, ?_, ?_, fun h => (key q).mp h hbP⟩` and prove the remaining obligations. Rewrite using `[← hpz]`. Conclude with `((PrimeSpectrum.le_iff_specializes q p).mp hPp).map hV'.fromSpec.continuous`.

Use `letI := X.presheaf.algebra_section_stalk ⟨hV'.fromSpec q, hmem q⟩ haveI hloc := hV'.isLocalization_stalk' q (hmem q)`. Establish `hdim : ringKrullDim (X.presheaf.stalk (hV'.fromSpec q)) = (P.height : WithBot ℕ∞)` using `@IsLocalization.AtPrime.ringKrullDim_eq_height _ _ q.asIdeal q.2 _ _ _ hloc`. Rewrite `hdim` using `[ringKrullDim_stalk_eq_coheight]`. Use `haveI : (Ideal.span {b}).IsPrincipal := ⟨⟨b, rfl⟩⟩`. Establish `hle : P.height ≤ 1` using `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin`.

Establish `hne : P.height ≠ 0`. Rewrite using `[Ne, Ideal.height_eq_zero_iff]`. Introduce `hmin`. Establish `hbot : P ≤ ⊥` using `hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le`. Establish `hb0 : b = 0` using `(Submodule.eq_bot_iff _).mp (le_bot_iff.mp hbot) b hbP`.

Conclude with `hf (by rw [hb0, map_zero])`. Establish `h1 : P.height = 1` using `le_antisymm hle (ENat.one_le_iff_ne_zero.mpr hne)`. Rewrite `hdim` using `[h1]`. Conclude with `hdim` after adjusting the coercions.
-/
private lemma exists_coheight_one_generalization_not_unitAt {X : Scheme.{0}} [IsIntegral X]
    [IsLocallyNoetherian X] {z : X} {f : X.functionField} (hf : f ≠ 0)
    (hreg : _root_.GlobalTheory.Cartier.RegAt z f) (hnu : ¬ _root_.GlobalTheory.Cartier.UnitAt z f) :
    ∃ w : X, w ⤳ z ∧ Order.coheight w = 1 ∧ ¬ _root_.GlobalTheory.Cartier.UnitAt w f := by
  obtain ⟨U, hzU, a, rfl⟩ := hreg.exists_fnOf
  obtain ⟨V, hV, hzV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hzU
  have hV' : IsAffineOpen V := hV
  have hgV : genericPoint X ∈ V :=
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr ⟨z, trivial, hzV⟩
  rw [← _root_.GlobalTheory.Cartier.fnOf_resG hVU hgV a] at hf hnu ⊢
  generalize _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.resG X hVU a = b at hf hnu ⊢
  haveI : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  haveI : Nonempty V := ⟨⟨z, hzV⟩⟩
  have hmem : ∀ q : PrimeSpectrum Γ(X, V), hV'.fromSpec q ∈ V := fun q => by
    have : hV'.fromSpec q ∈ Set.range hV'.fromSpec := Set.mem_range_self q
    rwa [hV'.range_fromSpec] at this
  have key : ∀ q : PrimeSpectrum Γ(X, V),
      _root_.GlobalTheory.Cartier.UnitAt (hV'.fromSpec q) (_root_.GlobalTheory.Cartier.fnOf V hgV b) ↔
        b ∉ q.asIdeal := by
    intro q
    rw [_root_.GlobalTheory.Cartier.unitAt_fnOf_iff (hmem q) hgV b]
    have : hV'.fromSpec q ∈ X.basicOpen b ↔ q ∈ PrimeSpectrum.basicOpen b := by
      rw [← hV'.fromSpec_preimage_basicOpen]; rfl
    rw [this, PrimeSpectrum.mem_basicOpen]
  set p := hV'.primeIdealOf ⟨z, hzV⟩
  have hpz : hV'.fromSpec p = z := hV'.fromSpec_primeIdealOf ⟨z, hzV⟩
  have hbp : b ∈ p.asIdeal := by
    by_contra h
    exact hnu (hpz ▸ (key p).mpr h)
  obtain ⟨P, hPmin, hPp⟩ := Ideal.exists_minimalPrimes_le
    ((Ideal.span_singleton_le_iff_mem _).mpr hbp)
  haveI hPprime : P.IsPrime := hPmin.1.1
  set q : PrimeSpectrum Γ(X, V) := ⟨P, hPprime⟩
  have hbP : b ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hPmin.1.2
  refine ⟨hV'.fromSpec q, ?_, ?_, fun h => (key q).mp h hbP⟩
  · rw [← hpz]
    exact ((PrimeSpectrum.le_iff_specializes q p).mp hPp).map hV'.fromSpec.continuous
  · letI := X.presheaf.algebra_section_stalk ⟨hV'.fromSpec q, hmem q⟩
    haveI hloc := hV'.isLocalization_stalk' q (hmem q)
    have hdim : ringKrullDim (X.presheaf.stalk (hV'.fromSpec q)) = (P.height : WithBot ℕ∞) :=
      @IsLocalization.AtPrime.ringKrullDim_eq_height _ _ q.asIdeal q.2 _ _ _ hloc
    rw [ringKrullDim_stalk_eq_coheight] at hdim
    haveI : (Ideal.span {b}).IsPrincipal := ⟨⟨b, rfl⟩⟩
    have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hPmin
    have hne : P.height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff]
      intro hmin
      have hbot : P ≤ ⊥ := hmin.2 ⟨Ideal.isPrime_bot, bot_le⟩ bot_le
      have hb0 : b = 0 := (Submodule.eq_bot_iff _).mp (le_bot_iff.mp hbot) b hbP
      exact hf (by rw [hb0, map_zero])
    have h1 : P.height = 1 := le_antisymm hle (ENat.one_le_iff_ne_zero.mpr hne)
    rw [h1] at hdim
    exact_mod_cast hdim

open CategoryTheory AlgebraicGeometry TopologicalSpace in
set_option autoImplicit false in

/- English proof (translation)
Introduce `X _ _ D m z hD hm`. Establish `hm' : (m : ℚ) ≠ 0` using `by exact_mod_cast hm.ne'`. Take `⟨g, hg⟩` from `D.exists_isEqn z`. Take `⟨U, hzU, hU⟩` from `hg.exists_nhds`. Establish `hgen : ∀ w : X, w ⤳ z → D.IsEqn w g` using `fun w hwz => hU w (hwz.mem_open U.isOpen hzU)`.

Unfold `_root_.GlobalTheory.PairStep.Off _root_.GlobalTheory.Discrepancy.qWeil`. Simplify using `only [div_eq_zero_iff, hm', or_false, Int.cast_eq_zero]`. Rewrite using `[hg.mem_supp_iff, not_not]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Assume the negation of the conclusion as `hnu`. Establish `hreg` using `(_root_.GlobalTheory.Cartier.CartierDiv.eff_iff.mp hD) z g hg`. Take `⟨w, hwz, hw1, hwnu⟩` from `exists_coheight_one_generalization_not_unitAt (Units.ne_zero g) hreg hnu`. Establish `hmult` using `h w hwz`. Rewrite `hmult` using `[(hgen w hwz).mult_eq]`.

Take `⟨a, ha⟩` from `_root_.GlobalTheory.Discrepancy.regAt_of_specializes hwz hreg`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `Units.ne_zero g (by rw [← ha, map_zero])`. Rewrite `hmult` using `[← ha, _root_.GlobalTheory.Cartier.ord_algebraMap hw1 ha0]`.

Establish `hdim : ringKrullDim (X.presheaf.stalk w) = 1`. Rewrite using `[ringKrullDim_stalk_eq_coheight, hw1]`. Both sides reduce to the same expression. Use `haveI : Ring.KrullDimLE 1 (X.presheaf.stalk w) := by`. Rewrite using `[Ring.krullDimLE_iff, hdim]`.

Conclude with `le_rfl` after adjusting the coercions. Establish `hfin` using `isFiniteLength_quotient_span_singleton (X.presheaf.stalk w) (mem_nonZeroDivisors_of_ne_zero ha0)`. Establish `htop` using `Module.length_ne_top_iff.mpr hfin`. Establish `hzero : Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a}) ≠ 0`. Rewrite using `[Ne, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top]`.

Conclude with `fun hunit => hwnu ⟨a, hunit, ha⟩`. Establish `: (Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a})).toNat ≠ 0`. Rewrite using `[Ne, ENat.toNat_eq_zero]`. The claim follows by propositional logic. Conclude with `this (by exact_mod_cast hmult)`.

Introduce `hunit w hwz`. Rewrite using `[(hgen w hwz).mult_eq]`. Take `⟨V, hzV, hV⟩` from `hunit.exists_nhds`. Conclude with `(hV w (hwz.mem_open V.isOpen hzV)).ord_eq_zero`.
-/
theorem _root_.GlobalTheory.PairStep.off_qWeil_iff_notMem_supp : ∀ (X : Scheme.{0}) [IsIntegral X]
    [IsLocallyNoetherian X] (D₀ : _root_.GlobalTheory.Cartier.CartierDiv X) (m : ℕ) (z : X),
    D₀.Eff → 0 < m →
      (_root_.GlobalTheory.PairStep.Off (_root_.GlobalTheory.Discrepancy.qWeil D₀ m) z ↔
        z ∉ D₀.supp) := by
  intro X _ _ D m z hD hm
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  obtain ⟨g, hg⟩ := D.exists_isEqn z
  obtain ⟨U, hzU, hU⟩ := hg.exists_nhds
  have hgen : ∀ w : X, w ⤳ z → D.IsEqn w g := fun w hwz =>
    hU w (hwz.mem_open U.isOpen hzU)
  unfold _root_.GlobalTheory.PairStep.Off _root_.GlobalTheory.Discrepancy.qWeil
  simp only [div_eq_zero_iff, hm', or_false, Int.cast_eq_zero]
  rw [hg.mem_supp_iff, not_not]
  constructor
  · intro h
    by_contra hnu
    have hreg := (_root_.GlobalTheory.Cartier.CartierDiv.eff_iff.mp hD) z g hg
    obtain ⟨w, hwz, hw1, hwnu⟩ := exists_coheight_one_generalization_not_unitAt (Units.ne_zero g) hreg hnu
    have hmult := h w hwz
    rw [(hgen w hwz).mult_eq] at hmult
    obtain ⟨a, ha⟩ := _root_.GlobalTheory.Discrepancy.regAt_of_specializes hwz hreg
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact Units.ne_zero g (by rw [← ha, map_zero])
    rw [← ha, _root_.GlobalTheory.Cartier.ord_algebraMap hw1 ha0] at hmult
    have hdim : ringKrullDim (X.presheaf.stalk w) = 1 := by
      rw [ringKrullDim_stalk_eq_coheight, hw1]; rfl
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk w) := by
      rw [Ring.krullDimLE_iff, hdim]
      exact_mod_cast le_rfl
    have hfin := isFiniteLength_quotient_span_singleton (X.presheaf.stalk w)
      (mem_nonZeroDivisors_of_ne_zero ha0)
    have htop := Module.length_ne_top_iff.mpr hfin
    have hzero : Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a}) ≠ 0 := by
      rw [Ne, Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff,
        Ideal.span_singleton_eq_top]
      exact fun hunit => hwnu ⟨a, hunit, ha⟩
    have : (Module.length (X.presheaf.stalk w) (X.presheaf.stalk w ⧸ Ideal.span {a})).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero]
      tauto
    exact this (by exact_mod_cast hmult)
  · intro hunit w hwz
    rw [(hgen w hwz).mult_eq]
    obtain ⟨V, hzV, hV⟩ := hunit.exists_nhds
    exact (hV w (hwz.mem_open V.isOpen hzV)).ord_eq_zero

end GlobalTheory.PairStep
