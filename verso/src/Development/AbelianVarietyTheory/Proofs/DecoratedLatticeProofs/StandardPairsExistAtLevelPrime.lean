import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPointFrameCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IncAMulMemIntAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryDatumLevelPrimeSplitDegreeGramFacts
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PadicResidueFieldCardAndPrimeIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotSqDvdOfRationalPrimeSplitsCompletelyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacesDvdNormIffUnderPrimesDvdStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace StdExProof

/- English proof (translation)
The claim follows from `GlobalTheory.T.padic_residueField_card_and_prime_irreducible T`.
-/
theorem qt_facts (T : ℕ) [Fact T.Prime] : Nat.card 𝓀[ℚ_[T]] = T ∧ Irreducible ((T : 𝒪[ℚ_[T]])) := GlobalTheory.T.padic_residueField_card_and_prime_irreducible T

/- English proof (translation)
The claim follows from `GlobalTheory.T.not_sq_dvd_of_rationalPrimeSplitsCompletely E T hT hs w hw`.
-/
theorem not_sq_dvd (E : Type) [Field E] [NumberField E] (T : ℕ) (hT : T.Prime) (hs : GlobalTheory.St.G.SplitsIn E T)
    (w : HeightOneSpectrum (𝓞 E)) (hw : (T : 𝓞 E) ∈ w.asIdeal) : ¬ w.asIdeal ^ 2 ∣ Ideal.span {(T : 𝓞 E)} :=
  GlobalTheory.T.not_sq_dvd_of_rationalPrimeSplitsCompletely E T hT hs w hw

/- English proof (translation)
The claim follows from `GlobalTheory.T.places_dvd_norm_iff_under_primes_dvd D π π' T hπ' hT hne x`.
-/
theorem places_over (D : D7) (π π' : 𝓞 D.host.E) (T : ℕ) (hπ' : (π' : D.host.E) = star (π : D.host.E))
    (hT : π * π' = (T : 𝓞 D.host.E)) (hne : π ≠ 0) (x : HeightOneSpectrum (𝓞 D.host.F)) :
    (T : 𝓞 D.host.F) ∈ x.asIdeal ↔ ∃ w ∈ Formalism.L2.Col.divs π, w.under (𝓞 D.host.F) = x :=
  GlobalTheory.T.places_dvd_norm_iff_under_primes_dvd D π π' T hπ' hT hne x

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `h1 : IsIntegral ℤ (p.pr (incA D (x : D.host.E)))` using `(x.2).map ((p.pr.comp (incA D)).toIntAlgHom)`. Establish `h2 : IsIntegral 𝒪[k] (p.pr (incA D (x : D.host.E)))` using `h1.tower_top`. Conclude with `(Valuation.integer.integers (valuation k)).mem_of_integral h2`.
-/
theorem pr_int (p : SplitPt D k) (x : 𝓞 D.host.E) : p.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
  have h1 : IsIntegral ℤ (p.pr (incA D (x : D.host.E))) := (x.2).map ((p.pr.comp (incA D)).toIntAlgHom)
  have h2 : IsIntegral 𝒪[k] (p.pr (incA D (x : D.host.E))) := h1.tower_top
  exact (Valuation.integer.integers (valuation k)).mem_of_integral h2

/- English proof (translation)
Establish `hy0 : y ≠ 0` using `fun h => hy (h ▸ w.asIdeal.zero_mem)`. Establish `hyE : (y : D.host.E) ≠ 0` using `by exact_mod_cast hy0`. Establish `hI : finPart D (p.e * incA D ((y : D.host.E))⁻¹) ∈ intAE D` using `not_not.1 (mt (hw.2 y hy0).2 hy)`. Establish `h1 : p.pr (incA D ((y : D.host.E))⁻¹) ∈ 𝒪[k]`. Rewrite using `[p.int_iff, p.sec_pr]`.

Conclude with `hI`. Establish `h2` using `pr_int p y`. Establish `hmul : p.pr (incA D (y : D.host.E)) * p.pr (incA D ((y : D.host.E))⁻¹) = 1`. Rewrite using `[← map_mul, ← map_mul, mul_inv_cancel₀ hyE, map_one, map_one]`. Establish `e1 : valuation k (p.pr (incA D (y : D.host.E))) ≤ 1` using `h2`.

Establish `e2 : valuation k (p.pr (incA D ((y : D.host.E))⁻¹)) ≤ 1` using `h1`. Establish `e3` using `congrArg (valuation k) hmul`. Rewrite `e3` using `[map_mul, map_one]`. Use `le_antisymm e1 ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Establish `: valuation k (p.pr (incA D (y : D.host.E))) * valuation k (p.pr (incA D ((y : D.host.E))⁻¹)) < 1` using `mul_lt_one_of_lt_of_le hlt e2`. Rewrite `this` using `[e3]`. Conclude with `lt_irrefl _ this`.
-/
theorem val_pr_eq_one (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : Formalism.L2.NTheta.IsIdemAt p.e w)
    (y : 𝓞 D.host.E) (hy : y ∉ w.asIdeal) : valuation k (p.pr (incA D (y : D.host.E))) = 1 := by
  have hy0 : y ≠ 0 := fun h => hy (h ▸ w.asIdeal.zero_mem)
  have hyE : (y : D.host.E) ≠ 0 := by exact_mod_cast hy0
  have hI : finPart D (p.e * incA D ((y : D.host.E))⁻¹) ∈ intAE D := not_not.1 (mt (hw.2 y hy0).2 hy)
  have h1 : p.pr (incA D ((y : D.host.E))⁻¹) ∈ 𝒪[k] := by
    rw [p.int_iff, p.sec_pr]; exact hI
  have h2 := pr_int p y
  have hmul : p.pr (incA D (y : D.host.E)) * p.pr (incA D ((y : D.host.E))⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hyE, map_one, map_one]
  have e1 : valuation k (p.pr (incA D (y : D.host.E))) ≤ 1 := h2
  have e2 : valuation k (p.pr (incA D ((y : D.host.E))⁻¹)) ≤ 1 := h1
  have e3 := congrArg (valuation k) hmul
  rw [map_mul, map_one] at e3
  refine le_antisymm e1 ?_
  by_contra hlt
  push_neg at hlt
  have : valuation k (p.pr (incA D (y : D.host.E))) * valuation k (p.pr (incA D ((y : D.host.E))⁻¹)) < 1 :=
    mul_lt_one_of_lt_of_le hlt e2
  rw [e3] at this
  exact lt_irrefl _ this

/- English proof (translation)
Introduce `x`. Establish `hL' : ∀ z : Fin S.rank → D.host.E, z ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = z i` using `fun z => by`. Rewrite using `[hL z]`. Conclude with `⟨fun h i => ⟨⟨z i, h i⟩, rfl⟩, fun h i => by obtain ⟨b, hb⟩ := h i; exact hb ▸ b.2⟩`. Rewrite using `[hb, Matrix.one_mulVec, GlobalTheory.FinPl.Model.mem_latV_std S L hL' p.v, mem_stdLat]`.

Use `forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[p.int_iff]`. Conclude with `⟨fun h => ⟨GlobalTheory.FinPl.FrameLat.sec_mem_idAt p _, h⟩, fun h => h.2⟩`.
-/
theorem isLat_std (p : SplitPt D k) (S : HSp D) (β : Frame p S (Fin S.rank)) (hb : β.b = 1) (L : Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D _) : β.IsLat L (stdLat k (Fin S.rank)) := by
  intro x
  have hL' : ∀ z : Fin S.rank → D.host.E, z ∈ L ↔ ∀ i, ∃ b : 𝓞 D.host.E, (b : D.host.E) = z i := fun z => by
    rw [hL z]
    exact ⟨fun h i => ⟨⟨z i, h i⟩, rfl⟩, fun h i => by obtain ⟨b, hb⟩ := h i; exact hb ▸ b.2⟩
  rw [hb, Matrix.one_mulVec, GlobalTheory.FinPl.Model.mem_latV_std S L hL' p.v, mem_stdLat]
  refine forall_congr' fun i => ?_
  rw [p.int_iff]
  exact ⟨fun h => ⟨GlobalTheory.FinPl.FrameLat.sec_mem_idAt p _, h⟩, fun h => h.2⟩

def scPair (c : 𝒪[k]) (hc : IsUnit c) {n : Type} [Fintype n] (i : n) : Pair k n where
  lat := stdLat k n
  isLat := inferInstance
  fn := c • (stdPair k i).fn
  fn_ne h := (stdPair k i).fn_ne (LinearMap.ext fun x => (hc.smul_eq_zero).1 (LinearMap.congr_fun h x))

/- English proof (translation)
Assemble the required witnesses or components as `⟨mem_stdLat.2 hx, by show c • residue 𝒪[k] ⟨x i, _⟩ = _ rw [map_mul, Algebra.smul_def]; rfl⟩`.
-/
theorem scPair_hasVal (c : 𝒪[k]) (hc : IsUnit c) {n : Type} [Fintype n] (i : n) (x : n → k) (hx : ∀ j, x j ∈ 𝒪[k]) :
    (scPair c hc i).HasVal x (residue 𝒪[k] (c * ⟨x i, hx i⟩)) :=
  ⟨mem_stdLat.2 hx, by
    show c • residue 𝒪[k] ⟨x i, _⟩ = _
    rw [map_mul, Algebra.smul_def]; rfl⟩

end StdExProof
end GlobalTheory.AdForm

namespace GlobalTheory.AdForm.StdExProof
open GlobalTheory.AdForm

/- English proof (translation)
Introduce `B X I hI _hP l Z u ψ hψ L hL`. Use `haveI hTf : Fact (B.T u).Prime := ⟨l.pr.T_prime u⟩`. Take `⟨hcard, hirr⟩` from `qt_facts (B.T u)`. Establish `hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u))` using `l.pr.piT_cop u`. Establish `hne : X.piT u ≠ 0`.

Introduce `h0`. Rewrite `hcop` using `[h0, map_zero, isCoprime_zero_left]`. Conclude with `not_isUnit_zero hcop`. Establish `hmem : ∀ i : (B.primes X).vT u, X.piT u ∈ i.1.asIdeal` using `fun i => (Formalism.L2.Col.mem_divs hne _).1 i.2`. Establish `hconj : ∀ i : (B.primes X).vT u, B.fields.conjO (X.piT u) ∉ i.1.asIdeal`.

Introduce `i hc`. Take `⟨a, b, hab⟩` from `hcop`. Conclude with `i.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ i.1.asIdeal.add_mem (Ideal.mul_mem_left _ a (hmem i)) (Ideal.mul_mem_left _ b hc)))`. Establish `hcP : ∀ i : (B.primes X).vT u, GlobalTheory.IdemSupport.cP (D` using `I.rec7 l Z) i.1 ≠ i.1 := by`. Introduce `i h`.

Apply `hconj i` to reduce the goal to its premises. Establish `h1 : X.piT u ∈ (GlobalTheory.IdemSupport.cP (D` using `I.rec7 l Z) i.1).asIdeal := by rw [h]; exact hmem i`. Establish `h2` using `(GlobalTheory.IdemSupport.mem_cP (D := I.rec7 l Z) i.1 (X.piT u)).1 h1`. Establish `h3 : B.fields.conjO (X.piT u) = GlobalTheory.IdemSupport.cO (I.rec7 l Z) (X.piT u)` using `RingOfIntegers.ext rfl`. Rewrite using `[h3]`.

Conclude with `h2`. Use `choose e he using fun i : (B.primes X).vT u => GlobalTheory.StdFrames.exists_isIdemAt (hcP i)`. Establish `hsplitT` using `(GlobalTheory.St.G.record_facts (I.rec7 l Z) u).1`. Establish `hsp : ∀ i : (B.primes X).vT u, ∃ p : SplitPt (I.rec7 l Z) ℚ_[B.T u], p.e = e i` using `fun i => (GlobalTheory.InhPt.exists_splitPt_frame_char (I.rec7 l Z)).1 ℚ_[B.T u] (B.T u) hTf.out hcard hirr i.1 (e i) (he i) (he i).1 (l.pr.vT_norm u _ i.2) (not_sq_dvd _ (B.T u) hTf.out hsplitT i.1 (by`. Establish `h` using `Ideal.mul_mem_right (B.fields.conjO (X.piT u)) _ (hmem i)`.

Rewrite `h` using `[l.pr.piT_norm u]`. Conclude with `h))`. Use `choose p hpe using hsp`. Establish `hidem : ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e i.1` using `fun i => (hpe i).symm ▸ he i`. Set `wE : (B.primes X).vT u → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E)` to `fun i => i.1`.

Establish `hv : ∀ i : (B.primes X).vT u, HeightOneSpectrum.under (𝓞 (I.rec7 l Z).host.F) (wE i) = (p i).v`. Introduce `i`. Take `⟨ε, h1, h2⟩` from `(p i).above`. Conclude with `GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (hidem i) h1 h2`. Establish `hover` using `fun x => places_over (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl (l.pr.piT_norm u) hne x`.

Establish `hTv : ∀ i, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal` using `fun i => (hover (p i).v).2 ⟨wE i, i.2, hv i⟩`. Establish `hunit : ∀ i, (p i).UnitAA` using `fun i => GlobalTheory.FinPl.UnitAt.unitAA_level I l Z u (p i) (hTv i)`. Establish `hpart2` using `fun i => (GlobalTheory.InhPt.exists_splitPt_frame_char (I.rec7 l Z)).2 ℚ_[B.T u] (p i)`. Use `choose χ hχ using fun i => (hpart2 i).2 ψ hψ`. Use `choose β hβ using fun j i => (hpart2 i).1 ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank) 1 1 (mul_one 1) (mul_one 1)`.

Establish `hβ' : ∀ j i, (β j i).b' = 1` using `fun j i => by`. Use `(β j i).bb'` as an intermediate fact. Rewrite `this` using `[hβ j i, one_mul]`. Then use the resulting hypothesis. Establish `hrank : ∀ j, 0 < ((I.rec7 l Z).sp.X j).rank`. Introduce `j`.

Take `⟨hs, h1, -⟩` from `hI.spaces`. Rewrite using `[show (I.rec7 l Z).sp.X j = B.sp.X j from rfl, h1 j]`. Use `show 0 < B.R.k + j * (B.R.t + 1)`. Use `B.R.m_add_three_le_k` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Set `c : (B.primes X).vT u → 𝒪[ℚ_[B.T u]]` to `fun i => ⟨(p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)), pr_int (p i) (B.fields.conjO (X.piT u))⟩`. Establish `hcv : ∀ i, valuation ℚ_[B.T u] ((p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E))) = 1` using `fun i => val_pr_eq_one (p i) (hidem i) (B.fields.conjO (X.piT u)) (hconj i)`. Establish `hc : ∀ i, IsUnit (c i)` using `fun i => (Valuation.integer.integers (valuation ℚ_[B.T u])).isUnit_iff_valuation_eq_one.2 (hcv i)`. Set `last : ∀ j, Fin ((I.rec7 l Z).sp.X j).rank` to `fun j => ⟨((I.rec7 l Z).sp.X j).rank - 1, by have := hrank j; omega⟩`. Set `Q : ∀ j, (B.primes X).vT u → Pair ℚ_[B.T u] (Fin ((I.rec7 l Z).sp.X j).rank)` to `fun j i => scPair (c i) (hc i) (last j)`.

Establish `hStd : StdT I l Z u p β Q L`. Use `⟨⟨Equiv.refl _, fun i => hidem i⟩, fun j hj => ⟨hL j hj, fun i => ⟨isLat_std (p i) _ (β j i) (hβ j i) (L j) (hL j hj), ?_⟩⟩⟩` and prove the remaining obligations. Introduce `z hz r hr`. Establish `hz' : ∀ r', IsIntegral ℤ (z r')` using `(hL j hj z).1 hz`. Establish `hx : ∀ r', (p i).pr (incA (I.rec7 l Z) (z r')) ∈ 𝒪[ℚ_[B.T u]]` using `fun r' => pr_int (p i) ⟨z r', hz' r'⟩`.

Establish `hrl : r = last j` using `Fin.ext (by show r.1 = _ - 1; omega)`. Substitute `hrl` using the available equality. Use `⟨c i * ⟨_, hx (last j)⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) * (p i).pr (incA (I.rec7 l Z) (z (last j))) = _`. Rewrite using `[← map_mul]`.

Conclude with `congrArg _ (map_mul _ _ _).symm`. Rewrite using `[hβ' j i, Matrix.one_mulVec]`. Conclude with `scPair_hasVal (c i) (hc i) (last j) _ hx`. Use `⟨ℚ_[B.T u], inferInstance, inferInstance, inferInstance, inferInstance, (B.primes X).vT u, p, Finset.univ.toList, ⟨(B.T u : 𝒪[ℚ_[B.T u]]), hirr⟩, χ, β, Q, ⟨Finset.nodup_toList _, fun i => Finset.mem_toList.2 (Finset.mem_univ _), GlobalTheory.AdForm.StdT.places_injective I hI _hP …` and prove the remaining obligations. Establish `hm : (p i).pr (incA (I.rec7 l Z) (X.piT u : B.fields.E)) * (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) = (B.T u : ℚ_[B.T u])`.

Establish `: ((X.piT u : B.fields.E) * (B.fields.conjO (X.piT u) : B.fields.E)) = ((B.T u : ℕ) : B.fields.E)`. Conclude with `congrArg (fun x : 𝓞 B.fields.E => (x : B.fields.E)) (l.pr.piT_norm u)` after adjusting the coercions. Establish `h2 : (p i).pr (incA (I.rec7 l Z) (X.piT u : B.fields.E)) * (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) = (p i).pr (incA (I.rec7 l Z) (((B.T u : ℕ) : B.fields.E)))`. Rewrite using `[← map_mul, ← this]`. Conclude with `congrArg _ (map_mul _ _ _).symm`.

Rewrite using `[h2]`. Conclude with `map_natCast ((p i).pr.comp (incA (I.rec7 l Z))) (B.T u)`. Establish `hv2` using `congrArg (valuation ℚ_[B.T u]) hm`. Rewrite `hv2` using `[map_mul, hcv i, mul_one]`. Rewrite using `[hv2]`.

Both sides reduce to the same expression. Rewrite using `[hover x]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`. Conclude with `⟨wE i, i.2, hv i⟩`.

Introduce and unpack `⟨w, hw, rfl⟩`. Conclude with `⟨⟨w, hw⟩, hv ⟨w, hw⟩⟩`.
-/
theorem stdEx' : StdEx' := by
  intro B X I hI _hP l Z u ψ hψ L hL
  haveI hTf : Fact (B.T u).Prime := ⟨l.pr.T_prime u⟩
  obtain ⟨hcard, hirr⟩ := qt_facts (B.T u)
  have hcop : IsCoprime (X.piT u) (B.fields.conjO (X.piT u)) := l.pr.piT_cop u
  have hne : X.piT u ≠ 0 := by
    intro h0
    rw [h0, map_zero, isCoprime_zero_left] at hcop
    exact not_isUnit_zero hcop
  have hmem : ∀ i : (B.primes X).vT u, X.piT u ∈ i.1.asIdeal := fun i => (Formalism.L2.Col.mem_divs hne _).1 i.2
  have hconj : ∀ i : (B.primes X).vT u, B.fields.conjO (X.piT u) ∉ i.1.asIdeal := by
    intro i hc
    obtain ⟨a, b, hab⟩ := hcop
    exact i.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ i.1.asIdeal.add_mem (Ideal.mul_mem_left _ a (hmem i)) (Ideal.mul_mem_left _ b hc)))
  have hcP : ∀ i : (B.primes X).vT u, GlobalTheory.IdemSupport.cP (D := I.rec7 l Z) i.1 ≠ i.1 := by
    intro i h
    apply hconj i
    have h1 : X.piT u ∈ (GlobalTheory.IdemSupport.cP (D := I.rec7 l Z) i.1).asIdeal := by rw [h]; exact hmem i
    have h2 := (GlobalTheory.IdemSupport.mem_cP (D := I.rec7 l Z) i.1 (X.piT u)).1 h1
    have h3 : B.fields.conjO (X.piT u) = GlobalTheory.IdemSupport.cO (I.rec7 l Z) (X.piT u) := RingOfIntegers.ext rfl
    rw [h3]; exact h2
  choose e he using fun i : (B.primes X).vT u => GlobalTheory.StdFrames.exists_isIdemAt (hcP i)
  have hsplitT := (GlobalTheory.St.G.record_facts (I.rec7 l Z) u).1
  have hsp : ∀ i : (B.primes X).vT u, ∃ p : SplitPt (I.rec7 l Z) ℚ_[B.T u], p.e = e i := fun i =>
    (GlobalTheory.InhPt.exists_splitPt_frame_char (I.rec7 l Z)).1 ℚ_[B.T u] (B.T u) hTf.out hcard hirr i.1 (e i) (he i) (he i).1
      (l.pr.vT_norm u _ i.2) (not_sq_dvd _ (B.T u) hTf.out hsplitT i.1 (by
        have h := Ideal.mul_mem_right (B.fields.conjO (X.piT u)) _ (hmem i)
        rw [l.pr.piT_norm u] at h
        exact h))
  choose p hpe using hsp
  have hidem : ∀ i, Formalism.L2.NTheta.IsIdemAt (p i).e i.1 := fun i => (hpe i).symm ▸ he i
  let wE : (B.primes X).vT u → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.E) := fun i => i.1
  have hv : ∀ i : (B.primes X).vT u, HeightOneSpectrum.under (𝓞 (I.rec7 l Z).host.F) (wE i) = (p i).v := by
    intro i
    obtain ⟨ε, h1, h2⟩ := (p i).above
    exact GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (hidem i) h1 h2
  have hover := fun x => places_over (I.rec7 l Z) (X.piT u) (B.fields.conjO (X.piT u)) (B.T u) rfl (l.pr.piT_norm u) hne x
  have hTv : ∀ i, ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ (p i).v.asIdeal := fun i =>
    (hover (p i).v).2 ⟨wE i, i.2, hv i⟩
  have hunit : ∀ i, (p i).UnitAA := fun i => GlobalTheory.FinPl.UnitAt.unitAA_level I l Z u (p i) (hTv i)
  have hpart2 := fun i => (GlobalTheory.InhPt.exists_splitPt_frame_char (I.rec7 l Z)).2 ℚ_[B.T u] (p i)
  choose χ hχ using fun i => (hpart2 i).2 ψ hψ
  choose β hβ using fun j i => (hpart2 i).1 ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank) 1 1 (mul_one 1) (mul_one 1)
  have hβ' : ∀ j i, (β j i).b' = 1 := fun j i => by
    have := (β j i).bb'
    rwa [hβ j i, one_mul] at this
  have hrank : ∀ j, 0 < ((I.rec7 l Z).sp.X j).rank := by
    intro j
    obtain ⟨hs, h1, -⟩ := hI.spaces
    rw [show (I.rec7 l Z).sp.X j = B.sp.X j from rfl, h1 j]
    show 0 < B.R.k + j * (B.R.t + 1)
    have := B.R.m_add_three_le_k
    omega
  let c : (B.primes X).vT u → 𝒪[ℚ_[B.T u]] := fun i =>
    ⟨(p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)), pr_int (p i) (B.fields.conjO (X.piT u))⟩
  have hcv : ∀ i, valuation ℚ_[B.T u] ((p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E))) = 1 :=
    fun i => val_pr_eq_one (p i) (hidem i) (B.fields.conjO (X.piT u)) (hconj i)
  have hc : ∀ i, IsUnit (c i) := fun i =>
    (Valuation.integer.integers (valuation ℚ_[B.T u])).isUnit_iff_valuation_eq_one.2 (hcv i)
  let last : ∀ j, Fin ((I.rec7 l Z).sp.X j).rank := fun j => ⟨((I.rec7 l Z).sp.X j).rank - 1, by have := hrank j; omega⟩
  let Q : ∀ j, (B.primes X).vT u → Pair ℚ_[B.T u] (Fin ((I.rec7 l Z).sp.X j).rank) := fun j i => scPair (c i) (hc i) (last j)
  have hStd : StdT I l Z u p β Q L := by
    refine ⟨⟨Equiv.refl _, fun i => hidem i⟩, fun j hj => ⟨hL j hj, fun i => ⟨isLat_std (p i) _ (β j i) (hβ j i) (L j) (hL j hj), ?_⟩⟩⟩
    intro z hz r hr
    have hz' : ∀ r', IsIntegral ℤ (z r') := (hL j hj z).1 hz
    have hx : ∀ r', (p i).pr (incA (I.rec7 l Z) (z r')) ∈ 𝒪[ℚ_[B.T u]] := fun r' => pr_int (p i) ⟨z r', hz' r'⟩
    have hrl : r = last j := Fin.ext (by show r.1 = _ - 1; omega)
    subst hrl
    refine ⟨c i * ⟨_, hx (last j)⟩, ?_, ?_⟩
    · show (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) * (p i).pr (incA (I.rec7 l Z) (z (last j))) = _
      rw [← map_mul]
      exact congrArg _ (map_mul _ _ _).symm
    · rw [hβ' j i, Matrix.one_mulVec]
      exact scPair_hasVal (c i) (hc i) (last j) _ hx
  refine ⟨ℚ_[B.T u], inferInstance, inferInstance, inferInstance, inferInstance, (B.primes X).vT u, p, Finset.univ.toList,
    ⟨(B.T u : 𝒪[ℚ_[B.T u]]), hirr⟩, χ, β, Q, ⟨Finset.nodup_toList _, fun i => Finset.mem_toList.2 (Finset.mem_univ _),
    GlobalTheory.AdForm.StdT.places_injective I hI _hP l Z u p β Q L hStd, fun x => Iff.rfl, hunit⟩,
    fun i => ⟨(hχ i).2.2.2 (hunit i), (hχ i).1⟩, hcard, fun i => ⟨?_, hcv i⟩, fun x => ?_, hβ, hStd⟩
  · have hm : (p i).pr (incA (I.rec7 l Z) (X.piT u : B.fields.E)) *
        (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) = (B.T u : ℚ_[B.T u]) := by
      have : ((X.piT u : B.fields.E) * (B.fields.conjO (X.piT u) : B.fields.E)) = ((B.T u : ℕ) : B.fields.E) := by
        exact_mod_cast congrArg (fun x : 𝓞 B.fields.E => (x : B.fields.E)) (l.pr.piT_norm u)
      have h2 : (p i).pr (incA (I.rec7 l Z) (X.piT u : B.fields.E)) *
          (p i).pr (incA (I.rec7 l Z) (B.fields.conjO (X.piT u) : B.fields.E)) =
          (p i).pr (incA (I.rec7 l Z) (((B.T u : ℕ) : B.fields.E))) := by
        rw [← map_mul, ← this]
        exact congrArg _ (map_mul _ _ _).symm
      rw [h2]
      exact map_natCast ((p i).pr.comp (incA (I.rec7 l Z))) (B.T u)
    have hv2 := congrArg (valuation ℚ_[B.T u]) hm
    rw [map_mul, hcv i, mul_one] at hv2
    rw [hv2]
    rfl
  · rw [hover x]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨wE i, i.2, hv i⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, hv ⟨w, hw⟩⟩

end GlobalTheory.AdForm.StdExProof
