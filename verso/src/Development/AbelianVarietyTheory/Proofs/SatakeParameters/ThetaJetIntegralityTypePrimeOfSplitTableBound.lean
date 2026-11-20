import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetSplitAmb
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRatIdxOfJetsRatDeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetLossOfFamilyFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumJetsTranslate
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypothesesProofStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceExtendsToIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoeffInLetters
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterTrivialNearOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNonzeroThetaVectorsNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFinite
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.EntryG

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.AtG
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable (jetSum RatIdx)
open GlobalTheory.DatumJets (SplitSet map_jetSum)
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.JetsFromTables

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ} {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}

omit [NumberField E] [StarRing E] in
/- English proof (translation)
Introduce `_ hx P hP` and use `hx P (h hP)`.
-/
theorem homAt_mono {S T : Finset (HeightOneSpectrum (𝓞 E))} (h : T ⊆ S) : homAt S N N' ≤ homAt T N N' :=
  fun _ hx P hP => hx P (h hP)

/- English proof (translation)
Introduce `P hP y hy`. Take `⟨s, hs, hsy⟩` from `(mem_locP P N' _).1 (hx P hP y hy)`. Use `(mem_locP P N' _).2 ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs (hr P hP), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul]` and apply the resulting hypothesis.
-/
theorem homAt_of_smul {T : Finset (HeightOneSpectrum (𝓞 E))} {r : 𝓞 E} (hr : ∀ P ∈ T, r ∉ P.asIdeal) {x : HomE E a b}
    (hx : r • x ∈ homAt T N N') : x ∈ homAt T N N' := by
  intro P hP y hy
  obtain ⟨s, hs, hsy⟩ := (mem_locP P N' _).1 (hx P hP y hy)
  refine (mem_locP P N' _).2 ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs (hr P hP), ?_⟩
  rwa [mul_smul]

end Loc

section Level

variable {X : Fields} (A : Amb X) {a b : ℕ} {S : Finset (HeightOneSpectrum (𝓞 X.E))}
  {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)}

/- English proof (translation)
Establish `hadd` using `indAdd_of A a b S M hM (lattice_classes_finite_refinement X a b S) (indTieD_of_la A a b S M hM hLa)`. Establish `hsm : A.IndSmooth a b S M` using `indSmooth_of A _ _ _ _ hE`. Use `fin_mul S N N' hR.1 hR.2.1 c k hc hk` as an intermediate fact. Set `_` to `Fintype.ofFinite (↥(mulLat c (homAt S N N')) ⧸ (mulLat (c * k) (homAt S N N')).comap (mulLat c (homAt S N N')).subtype)`. Establish `h1 : A.thInd S N N' c x = fun w => ∑ z, A.thInd S N N' (c * k) (x + (lrep (mulLat c (homAt S N N')) (mulLat (c * k) (homAt S N N')) z : HomE X.E a b)) w`.

Use function extensionality and compare the values at `w`. Rewrite using `[hadd N N' c k x hc hk hR w, latSum_eq, finsum_eq_sum_of_fintype]`. Rewrite using `[latSum_eq, finsum_eq_sum_of_fintype]`. Unfold `jetC derivAt0`. Rewrite using `[h1, iteratedFDeriv_sum (fun z _ => hsm N N' (c * k) _ (hR.add (Subtype.coe_prop _)) _), Finset.sum_apply, _root_.sum_apply, Finset.mul_sum]`.
-/
theorem jetC_refine (hLa : A.LaHyp a b S) (hE : A.ESmooth a b) {M c k : ℕ} (hM : 0 < M) (hc : 0 < c) (hk : 0 < k) {x : HomE X.E a b}
    (hR : InRange S M (c * k) N N' x) (m : DVar X.Tau a b →₀ ℕ) :
    jetC A.cD (A.thInd S N N' c x) m =
      latSum (mulLat c (homAt S N N')) (mulLat (c * k) (homAt S N N')) fun y => jetC A.cD (A.thInd S N N' (c * k) (x + y)) m := by
  have hadd := indAdd_of A a b S M hM (lattice_classes_finite_refinement X a b S) (indTieD_of_la A a b S M hM hLa)
  have hsm : A.IndSmooth a b S M := indSmooth_of A _ _ _ _ hE
  have := fin_mul S N N' hR.1 hR.2.1 c k hc hk
  let _ := Fintype.ofFinite (↥(mulLat c (homAt S N N')) ⧸ (mulLat (c * k) (homAt S N N')).comap (mulLat c (homAt S N N')).subtype)
  have h1 : A.thInd S N N' c x = fun w => ∑ z, A.thInd S N N' (c * k)
      (x + (lrep (mulLat c (homAt S N N')) (mulLat (c * k) (homAt S N N')) z : HomE X.E a b)) w := by
    funext w
    rw [hadd N N' c k x hc hk hR w, latSum_eq, finsum_eq_sum_of_fintype]
  rw [latSum_eq, finsum_eq_sum_of_fintype]
  unfold jetC derivAt0
  rw [h1, iteratedFDeriv_sum (fun z _ => hsm N N' (c * k) _ (hR.add (Subtype.coe_prop _)) _), Finset.sum_apply, _root_.sum_apply,
    Finset.mul_sum]

/- English proof (translation)
Establish `hck` using `Nat.mul_pos hc hk`. Use `fin_div S N N' hN hN' cA (c * k) hA hck` as an intermediate fact. Use `fin_mul S N N' hN hN' c k hc hk` as an intermediate fact. Rewrite using `[latSum_tower _ (mulLat c (homAt S N N')) _ (mulLat_mul_le c k _) (mulLat_le_divLat c cA _) _ ?_]`. Use `latSum_congr _ _ fun x hx => ?_` and prove the remaining obligations.

Rewrite using `[jetC_refine A hLa hE (Nat.mul_pos hA hck) hc hk ⟨hN, hN', hck, Dvd.intro_left cA rfl, divLat_mul_of cA (c * k) _ hx⟩ m, ← latSum_mul_left]`. Conclude with `latSum_congr _ _ fun y hy => by rw [hinv x y hy]`. Introduce `x y hy`. Establish `h1 : A.thInd S N N' (c * k) (x + y) = A.thInd S N N' (c * k) x`. Unfold `Amb.thInd Amb.liftW`.

Rewrite using `[isLift_congr A S N N' (c * k) (x + y) x (by simpa using hy)]`. Rewrite using `[hinv x y (mulLat_mul_le c k _ hy), h1]`.
-/
theorem latSum_coarsen (hLa : A.LaHyp a b S) (hE : A.ESmooth a b) (hN : IsSdLat N) (hN' : IsSdLat N') {cA c k : ℕ} (hA : 0 < cA)
    (hc : 0 < c) (hk : 0 < k) (Ξ : HomE X.E a b → ℂ) (hinv : ∀ x y, y ∈ mulLat c (homAt S N N') → Ξ (x + y) = Ξ x)
    (m : DVar X.Tau a b →₀ ℕ) :
    (latSum (divLat cA (homAt S N N')) (mulLat (c * k) (homAt S N N')) fun x => Ξ x * jetC A.cD (A.thInd S N N' (c * k) x) m) =
      latSum (divLat cA (homAt S N N')) (mulLat c (homAt S N N')) fun x => Ξ x * jetC A.cD (A.thInd S N N' c x) m := by
  have hck := Nat.mul_pos hc hk
  have := fin_div S N N' hN hN' cA (c * k) hA hck
  have := fin_mul S N N' hN hN' c k hc hk
  rw [latSum_tower _ (mulLat c (homAt S N N')) _ (mulLat_mul_le c k _) (mulLat_le_divLat c cA _) _ ?_]
  · refine latSum_congr _ _ fun x hx => ?_
    rw [jetC_refine A hLa hE (Nat.mul_pos hA hck) hc hk ⟨hN, hN', hck, Dvd.intro_left cA rfl, divLat_mul_of cA (c * k) _ hx⟩ m,
      ← latSum_mul_left]
    exact latSum_congr _ _ fun y hy => by rw [hinv x y hy]
  · intro x y hy
    have h1 : A.thInd S N N' (c * k) (x + y) = A.thInd S N N' (c * k) x := by
      unfold Amb.thInd Amb.liftW
      rw [isLift_congr A S N N' (c * k) (x + y) x (by simpa using hy)]
    rw [hinv x y (mulLat_mul_le c k _ hy), h1]

/- English proof (translation)
Establish `p₁` using `Nat.pos_of_dvd_of_pos h₁ hM`. Establish `p₂` using `Nat.pos_of_dvd_of_pos h₂ hM`. Take `⟨k₁, e₁⟩` from `h₁`. Take `⟨k₂, e₂⟩` from `h₂`. Apply `A.σ₀.injective` to reduce the goal to its premises.

Rewrite using `[map_jetSum A S hN hN' hA p₁ Ξ r₁, map_jetSum A S hN hN' hA p₂ Ξ r₂, ← latSum_coarsen A hLa hE hN hN' hA p₁ (Nat.pos_of_mul_pos_left (e₁ ▸ hM)) _ (fun x y hy => congrArg A.σ₀ (i₁ x y hy)), ← latSum_coarsen A hLa hE hN hN' hA p₂ (Nat.pos_of_mul_pos_left (e₂ ▸ hM)) _ (fun x y hy => …`.
-/
theorem jetSum_level (hLa : A.LaHyp a b S) (hE : A.ESmooth a b) (hN : IsSdLat N) (hN' : IsSdLat N') {cA c₁ c₂ M : ℕ} (hA : 0 < cA)
    (hM : 0 < M) (h₁ : c₁ ∣ M) (h₂ : c₂ ∣ M) (Ξ : HomE X.E a b → X.K)
    (i₁ : ∀ x y, y ∈ mulLat c₁ (homAt S N N') → Ξ (x + y) = Ξ x) (i₂ : ∀ x y, y ∈ mulLat c₂ (homAt S N N') → Ξ (x + y) = Ξ x)
    {m : DVar X.Tau a b →₀ ℕ} (r₁ : m ∈ RatIdx A S cA c₁ N N' Ξ) (r₂ : m ∈ RatIdx A S cA c₂ N N' Ξ) :
    jetSum A S cA c₁ N N' Ξ m = jetSum A S cA c₂ N N' Ξ m := by
  have p₁ := Nat.pos_of_dvd_of_pos h₁ hM
  have p₂ := Nat.pos_of_dvd_of_pos h₂ hM
  obtain ⟨k₁, e₁⟩ := h₁
  obtain ⟨k₂, e₂⟩ := h₂
  apply A.σ₀.injective
  rw [map_jetSum A S hN hN' hA p₁ Ξ r₁, map_jetSum A S hN hN' hA p₂ Ξ r₂,
    ← latSum_coarsen A hLa hE hN hN' hA p₁ (Nat.pos_of_mul_pos_left (e₁ ▸ hM)) _ (fun x y hy => congrArg A.σ₀ (i₁ x y hy)),
    ← latSum_coarsen A hLa hE hN hN' hA p₂ (Nat.pos_of_mul_pos_left (e₂ ▸ hM)) _ (fun x y hy => congrArg A.σ₀ (i₂ x y hy)),
    ← e₁, ← e₂]

/- English proof (translation)
Take `⟨-, hLa, -, -, -, hn, -, hS⟩` from `hctx`. Establish `h1 : X.conjO ϖ ∉ P.asIdeal` using `fun h => hLa.2.2.1 P hP (hS _ h)`. Conclude with `⟨h1, fun h => (P.isPrime.mem_or_mem (hn ▸ h)).elim hϖ h1⟩`.
-/
theorem notMem_of_split {ϖ : 𝓞 X.E} {p : ℕ} (hctx : SplitSet A a b S ϖ p) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ S)
    (hϖ : ϖ ∉ P.asIdeal) : X.conjO ϖ ∉ P.asIdeal ∧ (p : 𝓞 X.E) ∉ P.asIdeal := by
  obtain ⟨-, hLa, -, -, -, hn, -, hS⟩ := hctx
  have h1 : X.conjO ϖ ∉ P.asIdeal := fun h => hLa.2.2.1 P hP (hS _ h)
  exact ⟨h1, fun h => (P.isPrime.mem_or_mem (hn ▸ h)).elim hϖ h1⟩

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hΞ`. Establish `hp : p.Prime` using `hctx.2.2.2.2.1`. Establish `hϖ0 : ϖ ≠ 0` using `left_ne_zero_of_mul (by rw [hctx.2.2.2.2.2.1]; exact_mod_cast hp.ne_zero)`. Establish `hsub : divs ϖ ⊆ S` using `fun P hP => hctx.2.2.2.2.2.2.2 P ((mem_divs hϖ0 P).1 hP)`. Establish `hM` using `Nat.mul_pos hA hB`.

Take `⟨n, c', hc', hn⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hM.ne' p hp.ne_one`. Establish `hc0 : 0 < c'` using `Nat.pos_of_ne_zero fun h => hc' (h ▸ dvd_zero p)`. Establish `hpn : ∀ P ∈ S \ divs ϖ, ((p ^ n : ℕ) : 𝓞 X.E) ∉ P.asIdeal` using `fun P hP h => by`. Rewrite `hP` using `[Finset.mem_sdiff, mem_divs hϖ0]`. Rewrite `h` using `[Nat.cast_pow]`.

Conclude with `(notMem_of_split A hctx hP.1 hP.2).2 (P.isPrime.mem_of_pow_mem n h)`. Establish `hL : p * c' ∣ cA * cB` using `Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.Prime.coprime_iff_not_dvd hp).2 hc') (hpB.mul_left _) ⟨p ^ n, by rw [hn, mul_comm]⟩`. Establish `h3' : ∀ x z, z ∈ mulLat p (homAt S N N') → z ∈ mulLat cB (homAt (S \ divs ϖ) N N') → Ξ (x + z) = Ξ x` using `fun x z hz hz' => h3 x z (Submodule.map_mono (homAt_mono hsub) hz) (by convert hz')`. Establish `hB' : (cB : X.E) ≠ 0` using `by exact_mod_cast hB.ne'`. Rewrite using `[jetSum_level A hctx.2.1 hctx.2.2.2.1 hN hN' hA hM (Dvd.intro_left _ rfl) hL Ξ (fun x y hy => ?_) (fun x y hy => ?_) (hrat _ hB (Dvd.intro_left _ rfl)) (hrat _ (Nat.mul_pos hp.pos hc0) hL)]`.

Use `fin_div S N N' hN hN' cA (p * c') hA (Nat.mul_pos hp.pos hc0)` as an intermediate fact. Set `_` to `Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat (p * c') (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)`. Rewrite using `[jetSum, latSum_eq, finsum_eq_sum_of_fintype, Finset.mul_sum]`. Use `Valuation.map_sum_le _ fun z _ => ?_` and prove the remaining obligations. Generalize the expression as in `lrep _ _ z = x`.

Take `⟨x, hx⟩` from `x`. Simplify using `only`. Distinguish the cases in `h0 : Ξ x = 0`. Simplify using `[h0]`. Rewrite using `[mul_left_comm, map_mul]`.

Use `mul_le_one' (h1 x) (hb c' x hc0 hc' ((mem_divLat _ _ _).2 fun P hP => ?_))` and prove the remaining obligations. Distinguish the cases in `hP' : P ∈ divs ϖ`. Conclude with `Submodule.smul_mem _ (c' : 𝓞 X.E) (h2 x h0) P hP'`. Use `homAt_of_smul hpn (x := (c' : 𝓞 X.E) • x) ?_ P (Finset.mem_sdiff.2 ⟨hP, hP'⟩)` and prove the remaining obligations. Rewrite using `[smul_smul, ← Nat.cast_mul, ← hn, mul_comm, Nat.cast_mul, mul_smul]`.

Conclude with `homAt_mono Finset.sdiff_subset (Submodule.smul_mem _ _ ((mem_divLat _ _ _).1 hx))`. Take `⟨k, rfl⟩` from `hpB`. Conclude with `h3' x y (mulLat_mul_le p k _ hy) (Submodule.map_mono (homAt_mono Finset.sdiff_subset) hy)`. Use `h3' x y (mulLat_mul_le p c' _ hy) ?_` and prove the remaining obligations. Take `⟨t, ht, rfl⟩` from `(mem_mulLat _ _ _).1 hy`.

Use `(mem_mulLat _ _ _).2 ⟨(cB : X.E)⁻¹ • ((p * c' : ℕ) : 𝓞 X.E) • t, homAt_of_smul hpn ?_, ?_⟩` and prove the remaining obligations. Establish `e : ((p ^ n : ℕ) : 𝓞 X.E) • (cB : X.E)⁻¹ • ((p * c' : ℕ) : 𝓞 X.E) • t = ((p * cA : ℕ) : 𝓞 X.E) • t`. Establish `e1 : (cA : X.E) * cB = p ^ n * c'` using `by exact_mod_cast hn`. Simplify using `only [Nat.cast_smul_eq_nsmul]`. Simplify using `only [← Nat.cast_smul_eq_nsmul X.E, smul_smul]`.

Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Take the linear combination `(-(p : X.E)) * e1`. Rewrite using `[e]`.

Conclude with `homAt_mono Finset.sdiff_subset (Submodule.smul_mem _ _ ht)`. Rewrite using `[Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul X.E, smul_smul, mul_inv_cancel₀ hB', one_smul]`.
-/
theorem datum_bound {ϖ : 𝓞 X.E} {p cA cB : ℕ} (hctx : SplitSet A a b S ϖ p) (hN : IsSdLat N) (hN' : IsSdLat N') (hA : 0 < cA)
    (hB : 0 < cB) (hpB : p ∣ cB) (w : HeightOneSpectrum (𝓞 X.K)) (κ : X.K) (Ξ : HomE X.E a b → X.K)
    (hΞ : GlobalTheory.ColPeriod.DatumAt (divs ϖ) S p cB w N N' Ξ) {m : DVar X.Tau a b →₀ ℕ}
    (hrat : ∀ c : ℕ, 0 < c → c ∣ cA * cB → m ∈ RatIdx A S cA c N N' Ξ)
    (hb : ∀ (c' : ℕ) (x : HomE X.E a b), 0 < c' → ¬ p ∣ c' → x ∈ divLat c' (homAt S N N') →
      w.valuation X.K (κ * A.jetK S N N' (p * c') x m) ≤ 1) :
    w.valuation X.K (κ * jetSum A S cA cB N N' Ξ m) ≤ 1 := by
  classical
  obtain ⟨h1, h2, h3⟩ := hΞ
  have hp : p.Prime := hctx.2.2.2.2.1
  have hϖ0 : ϖ ≠ 0 := left_ne_zero_of_mul (by rw [hctx.2.2.2.2.2.1]; exact_mod_cast hp.ne_zero)
  have hsub : divs ϖ ⊆ S := fun P hP => hctx.2.2.2.2.2.2.2 P ((mem_divs hϖ0 P).1 hP)
  have hM := Nat.mul_pos hA hB
  obtain ⟨n, c', hc', hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' p hp.ne_one
  have hc0 : 0 < c' := Nat.pos_of_ne_zero fun h => hc' (h ▸ dvd_zero p)
  have hpn : ∀ P ∈ S \ divs ϖ, ((p ^ n : ℕ) : 𝓞 X.E) ∉ P.asIdeal := fun P hP h => by
    rw [Finset.mem_sdiff, mem_divs hϖ0] at hP
    rw [Nat.cast_pow] at h
    exact (notMem_of_split A hctx hP.1 hP.2).2 (P.isPrime.mem_of_pow_mem n h)
  have hL : p * c' ∣ cA * cB :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.Prime.coprime_iff_not_dvd hp).2 hc') (hpB.mul_left _) ⟨p ^ n, by rw [hn, mul_comm]⟩
  have h3' : ∀ x z, z ∈ mulLat p (homAt S N N') → z ∈ mulLat cB (homAt (S \ divs ϖ) N N') → Ξ (x + z) = Ξ x := fun x z hz hz' =>
    h3 x z (Submodule.map_mono (homAt_mono hsub) hz) (by convert hz')
  have hB' : (cB : X.E) ≠ 0 := by exact_mod_cast hB.ne'
  rw [jetSum_level A hctx.2.1 hctx.2.2.2.1 hN hN' hA hM (Dvd.intro_left _ rfl) hL Ξ (fun x y hy => ?_) (fun x y hy => ?_)
    (hrat _ hB (Dvd.intro_left _ rfl)) (hrat _ (Nat.mul_pos hp.pos hc0) hL)]
  · have := fin_div S N N' hN hN' cA (p * c') hA (Nat.mul_pos hp.pos hc0)
    let _ := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat (p * c') (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
    rw [jetSum, latSum_eq, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Valuation.map_sum_le _ fun z _ => ?_
    generalize lrep _ _ z = x
    obtain ⟨x, hx⟩ := x
    dsimp only
    by_cases h0 : Ξ x = 0
    · simp [h0]
    rw [mul_left_comm, map_mul]
    refine mul_le_one' (h1 x) (hb c' x hc0 hc' ((mem_divLat _ _ _).2 fun P hP => ?_))
    by_cases hP' : P ∈ divs ϖ
    · exact Submodule.smul_mem _ (c' : 𝓞 X.E) (h2 x h0) P hP'
    · refine homAt_of_smul hpn (x := (c' : 𝓞 X.E) • x) ?_ P (Finset.mem_sdiff.2 ⟨hP, hP'⟩)
      rw [smul_smul, ← Nat.cast_mul, ← hn, mul_comm, Nat.cast_mul, mul_smul]
      exact homAt_mono Finset.sdiff_subset (Submodule.smul_mem _ _ ((mem_divLat _ _ _).1 hx))
  · obtain ⟨k, rfl⟩ := hpB
    exact h3' x y (mulLat_mul_le p k _ hy) (Submodule.map_mono (homAt_mono Finset.sdiff_subset) hy)
  · refine h3' x y (mulLat_mul_le p c' _ hy) ?_
    obtain ⟨t, ht, rfl⟩ := (mem_mulLat _ _ _).1 hy
    refine (mem_mulLat _ _ _).2 ⟨(cB : X.E)⁻¹ • ((p * c' : ℕ) : 𝓞 X.E) • t, homAt_of_smul hpn ?_, ?_⟩
    · have e : ((p ^ n : ℕ) : 𝓞 X.E) • (cB : X.E)⁻¹ • ((p * c' : ℕ) : 𝓞 X.E) • t = ((p * cA : ℕ) : 𝓞 X.E) • t := by
        have e1 : (cA : X.E) * cB = p ^ n * c' := by exact_mod_cast hn
        simp only [Nat.cast_smul_eq_nsmul]
        simp only [← Nat.cast_smul_eq_nsmul X.E, smul_smul]
        congr 1
        push_cast
        field_simp
        linear_combination (-(p : X.E)) * e1
      rw [e]
      exact homAt_mono Finset.sdiff_subset (Submodule.smul_mem _ _ ht)
    · rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul X.E, smul_smul, mul_inv_cancel₀ hB', one_smul]

end Level

section Host

/- English proof (translation)
Establish `hd0 : (d : ℚ) ≠ 0` using `by exact_mod_cast hd.ne_zero`. Establish `h1 : (d * (2 * b)) ^ 2 = ((d * (4 * g - t ^ 2) : ℤ) : ℚ)`. Use `push_cast`. Rewrite using `[← ht, ← hn]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : IsIntegral ℤ ((d : ℚ) * (2 * b))` using `IsIntegral.of_pow (n := 2) two_pos (h1 ▸ isIntegral_algebraMap (x := (d * (4 * g - t ^ 2) : ℤ)))`. Take `⟨r, hr⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h2`. Establish `hr' : (r : ℚ) = d * (2 * b)` using `hr`. Establish `h3 : r ^ 2 = d * (4 * g - t ^ 2)`. Rewrite `h1` using `[← hr']`.

Conclude with `h1` after adjusting the coercions. Take `⟨s, hs⟩ : (d : ℤ) ∣ r` from `(Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨_, h3⟩`. Establish `hb : 2 * b = s` using `mul_left_cancel₀ hd0 (by rw [← hr', hs]; push_cast; ring)`. Establish `h4 : t ^ 2 + d * s ^ 2 = 4 * g`. Establish `: (t : ℚ) ^ 2 + d * s ^ 2 = 4 * g` using `by rw [← ht, ← hb, ← hn]; ring`.

Conclude with `this` after adjusting the coercions. Establish `h5 : Even (t - s)`. Establish `hdo : Odd (d : ℤ)` using `by exact_mod_cast Nat.odd_iff.2 hodd`. Establish `h6 : Even (t ^ 2 + d * s ^ 2)` using `h4 ▸ ⟨2 * g, by ring⟩`. Simplify `h6` using `[parity_simps, Int.not_even_iff_odd.2 hdo]`.

Take `⟨m, hm⟩` from `h5`. Establish `hm' : (t : ℚ) - s = m + m` using `by exact_mod_cast hm`. Conclude with `⟨m, s, by linarith, by linarith⟩`.
-/
theorem half_coords {d g : ℕ} (hd : d.Prime) (hodd : d % 2 = 1) {a b : ℚ} {t : ℤ} (ht : 2 * a = t) (hn : a ^ 2 + d * b ^ 2 = g) :
    ∃ m n : ℤ, a = m + n / 2 ∧ b = n / 2 := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne_zero
  have h1 : (d * (2 * b)) ^ 2 = ((d * (4 * g - t ^ 2) : ℤ) : ℚ) := by
    push_cast
    rw [← ht, ← hn]; ring
  have h2 : IsIntegral ℤ ((d : ℚ) * (2 * b)) := IsIntegral.of_pow (n := 2) two_pos (h1 ▸ isIntegral_algebraMap (x := (d * (4 * g - t ^ 2) : ℤ)))
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  have hr' : (r : ℚ) = d * (2 * b) := hr
  have h3 : r ^ 2 = d * (4 * g - t ^ 2) := by
    rw [← hr'] at h1; exact_mod_cast h1
  obtain ⟨s, hs⟩ : (d : ℤ) ∣ r := (Nat.prime_iff_prime_int.1 hd).dvd_of_dvd_pow (n := 2) ⟨_, h3⟩
  have hb : 2 * b = s := mul_left_cancel₀ hd0 (by rw [← hr', hs]; push_cast; ring)
  have h4 : t ^ 2 + d * s ^ 2 = 4 * g := by
    have : (t : ℚ) ^ 2 + d * s ^ 2 = 4 * g := by rw [← ht, ← hb, ← hn]; ring
    exact_mod_cast this
  have h5 : Even (t - s) := by
    have hdo : Odd (d : ℤ) := by exact_mod_cast Nat.odd_iff.2 hodd
    have h6 : Even (t ^ 2 + d * s ^ 2) := h4 ▸ ⟨2 * g, by ring⟩
    simpa [parity_simps, Int.not_even_iff_odd.2 hdo] using h6
  obtain ⟨m, hm⟩ := h5
  have hm' : (t : ℚ) - s = m + m := by exact_mod_cast hm
  exact ⟨m, s, by linarith, by linarith⟩

/- English proof (translation)
Take `⟨a, b, hab⟩` from `GlobalTheory.QuadSubfield.exists_coords D (EX.piG_K i)`. Establish `hc` using `GlobalTheory.QuadSubfield.conj_coords D a b`. Establish `hn` using `EX.piG_norm i`. Establish `hint : IsIntegral ℤ (((EX.piG i : 𝓞 D.host.E) : D.host.E) + D.host.conj ((EX.piG i : 𝓞 D.host.E) : D.host.E))` using `(EX.piG i).isIntegral_coe.add (map_isIntegral_int D.host.conj (EX.piG i).isIntegral_coe)`. Rewrite `hint`, `hn` using `[hab, hc]`.

Establish `e : (a : D.host.E) + b * D.host.sqrtMinusD + (a - b * D.host.sqrtMinusD) = algebraMap ℚ D.host.E (2 * a)` using `by simp; ring`. Rewrite `hint` using `[e, isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective]`. Take `⟨t, ht⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hint`. Establish `hn' : a ^ 2 + D.host.d * b ^ 2 = D.host.g i`. Establish `: (a : D.host.E) ^ 2 + D.host.d * b ^ 2 = D.host.g i`.

Take the linear combination `hn + (b : D.host.E) ^ 2 * D.host.sqrtMinusD_sq`. Conclude with `this` after adjusting the coercions. Establish `hh` using `D.host.hyp`. Take `⟨m, n, hm, hn⟩` from `half_coords hh.2.1 (by have := hh.2.2.2.1; omega) (t := t) (by simpa using ht.symm) hn'`. Establish `hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`.

Use `⟨m, n, ?_⟩` and prove the remaining obligations. Rewrite using `[hab, map_add, map_mul, map_ratCast, map_ratCast, hφ, hm, hn, Formalism.L2.Th1.CM.omegaK]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isQInt_piG {D : D7} (EX : ErrX D) (i : Fin 2) :
    Formalism.L2.AlgTh.IsQInt D.host.d (D.host.φ₀ ((EX.piG i : 𝓞 D.host.E) : D.host.E)) := by
  obtain ⟨a, b, hab⟩ := GlobalTheory.QuadSubfield.exists_coords D (EX.piG_K i)
  have hc := GlobalTheory.QuadSubfield.conj_coords D a b
  have hn := EX.piG_norm i
  have hint : IsIntegral ℤ (((EX.piG i : 𝓞 D.host.E) : D.host.E) + D.host.conj ((EX.piG i : 𝓞 D.host.E) : D.host.E)) :=
    (EX.piG i).isIntegral_coe.add (map_isIntegral_int D.host.conj (EX.piG i).isIntegral_coe)
  rw [hab, hc] at hint hn
  have e : (a : D.host.E) + b * D.host.sqrtMinusD + (a - b * D.host.sqrtMinusD) = algebraMap ℚ D.host.E (2 * a) := by
    simp; ring
  rw [e, isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective] at hint
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hn' : a ^ 2 + D.host.d * b ^ 2 = D.host.g i := by
    have : (a : D.host.E) ^ 2 + D.host.d * b ^ 2 = D.host.g i := by
      linear_combination hn + (b : D.host.E) ^ 2 * D.host.sqrtMinusD_sq
    exact_mod_cast this
  have hh := D.host.hyp
  obtain ⟨m, n, hm, hn⟩ := half_coords hh.2.1 (by have := hh.2.2.2.1; omega) (t := t) (by simpa using ht.symm) hn'
  have hφ : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  refine ⟨m, n, ?_⟩
  rw [hab, map_add, map_mul, map_ratCast, map_ratCast, hφ, hm, hn, Formalism.L2.Th1.CM.omegaK]
  push_cast
  ring

end Host

/- English proof (translation)
Introduce `hJ D EX sel δ B χ cD hH hsel hA i w hw u mu cst hcst j b _ hb N N' hN hN' hsN hsN' Ξ hΞ e _ hrat`. Establish `hPr` using `hH.2.2.2.2`. Establish `hX` using `hH.2.2.2.1.ok`. Establish `hp : (D.host.g i).Prime` using `hPr.g_prime i`. Establish `: Fact (D.host.g i).Prime` using `⟨hp⟩`.

Establish `hs : (recSeam D).Ok` using `⟨GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recSeam_emb D, bridge_star_holds D.R D.host⟩`. Establish `hcc : TaylorLogMetric.IsCurveIdeal D D.host.ccK` using `by rw [hH.1]; exact ⟨by simp, by simp⟩`. Establish `hev : ∀ j, Even (D.R.N j)` using `fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)`. Establish `hb' : Even b` using `hb ▸ hev _`. Establish `hV : B.VecP χ` using `GlobalTheory.ColNorms.familyVectors D _ δ B χ hH.2.2.1 hH.2.1 hcc hA.1 hA.2.1 (GlobalTheory.ExponentsFinite.yFinite _ _ _)`.

Take `⟨hL, hE⟩` from `GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth D _ (recSeam D) _ δ B χ cD _ b hX hs hcc hA.1 hV (hev j) hb'`. Take `⟨hctx, hA0, hB0, hg⟩` from `GlobalTheory.T.datumJets_typePrimeBadPrimesLevelsHypotheses D EX sel δ B χ cD hH hsel i u mu cst hcst _ b hL hE`. Establish `hcong : D.host.g i ≡ 1 [MOD D.host.QS * D.host.q * D.host.d]` using `hPr.g_cong i`. Establish `hnd : ∀ t, t ∣ D.host.QS * D.host.q * D.host.d → ¬ D.host.g i ∣ t` using `fun t ht h => hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd.1 ((hcong.of_dvd (h.trans ht)).symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)))))`. Establish `h5 : 5 ≤ D.host.g i`.

Establish `h4 : D.host.g i ≡ 1 [MOD 4]` using `hcong.of_dvd ((by norm_num : 4 ∣ 16).trans D.host.toHostRaw.sixteen_dvd_condN)`. Use `hp.one_lt` as an intermediate fact. Unfold `Nat.ModEq at h4`. Use linear arithmetic over natural numbers and integers. Establish `hpd : ¬ D.host.g i ∣ D.host.d` using `hnd _ (Dvd.intro_left _ rfl)`.

Establish `hpq : D.host.g i ≠ D.host.q` using `fun h => hnd D.host.q D.host.toHostRaw.q_dvd_condN h.dvd`. Establish `hdisc` using `GlobalTheory.GoodDepth.not_dvd_discr_host D.R D.host _ hp (UpperTheory.Ram.g_notMem_small D i) hpq fun h => hpd h.dvd`. Take `⟨lam, hlam⟩` from `GlobalTheory.T.place_over_p_induced_by_algebraic_padic_embedding _ (recSeam D).σ₀ (D.host.g i) w hw`. Take `⟨ι, hι⟩` from `GlobalTheory.ThLoc.place_extends_to_iso _ lam`. Establish `hιC : ∀ x ∈ TaylorLogMetric.Qbar, TaylorLogMetric.lamC lam x = ι x` using `fun x hx => by rw [TaylorLogMetric.lamC, dif_pos hx]; exact (hι ⟨x, hx⟩).symm`.

Establish `hval : ∀ k : D.what₂.LL, ‖ι ((recSeam D).σ₀ k)‖ ≤ 1 → w.valuation _ k ≤ 1` using `fun k hk => by`. Establish `hq : (recSeam D).σ₀ k ∈ TaylorLogMetric.Qbar`. Rewrite using `[mem_algebraicClosure_iff]`. Conclude with `(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) k).algHom (recSeam D).σ₀.toRatAlgHom`. Conclude with `(hlam k).1 ⟨hq, by rwa [hιC _ hq]⟩`.

Establish `hcD : ∀ τ, ‖ι (cD τ)‖ ≤ 1` using `fun τ => by`. Take `⟨M, _, hM, hs⟩` from `hA.2.2`. Take `⟨s, hsc, hsp⟩` from `hs τ`. Rewrite using `[← hsc, ← hιC _ (GlobalTheory.EigenGenerator.mem_Qbar M s)]`. Conclude with `(GlobalTheory.EigenGenerator.norm_generator_eq_one D _ lam (UpperTheory.Ram.g_notMem_small D i) hpq M hM τ s hsp).le`.

Establish `hstd : ∀ {n : ℕ} {L : Submodule (𝓞 D.host.E) (Sp D.host.E n)}, L.FG → GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (D.host.g i) L → (recSeam D).StdAtP (D.host.g i) L` using `fun hL h => by`. Take `⟨s, hs, h1, h2⟩` from `GlobalTheory.LiftTypePrime.ProdComb.eqAt_std (GlobalTheory.DatumJets.Transl.stdAt_of_stdOver D hp hL h)`. Conclude with `⟨s, hs, h2, h1⟩`. Use `set πE : D.host.E := ((EX.piG i : 𝓞 D.host.E) : D.host.E) with hπE`. Establish `hτ : ∀ τ, (recFields D).embC (recSeam D).σ₀ τ πE = D.host.φ₀ πE` using `fun τ => (hs.1 τ πE).trans (hH.2.1 τ ⟨πE, EX.piG_K i⟩)`.

Establish `hτ' : ∀ τ, (recFields D).embC (recSeam D).σ₀ τ (star πE) = conj (D.host.φ₀ πE)` using `fun τ => by`. Rewrite using `[hX.conjE, hτ]`. Establish `hπ0 : (recFields D).conjO (EX.piG i) ≠ 0` using `right_ne_zero_of_mul (by rw [hPr.piG_norm i]; exact_mod_cast hp.ne_zero)`. Establish `hcc' : (recFields D).conjO ((recFields D).conjO (EX.piG i)) = EX.piG i` using `Subtype.ext (star_star _)`. Establish `hsplit : Formalism.L2.AlgTh.SplitS (ambOf (recSeam D) B χ cD) (Sall sel mu u) (D.host.g i) (D.host.φ₀ πE) (EX.piG i)`.

Use `⟨hτ, hτ', fun P hP => ⟨fun hS h => ?_, fun h => hctx.2.2.2.2.2.2.2 P ?_⟩⟩` and prove the remaining obligations. Distinguish the cases in `h' : (recFields D).conjO (EX.piG i) ∈ P.asIdeal`. Take `⟨x, y, hxy⟩` from `hPr.piG_cop i`. Conclude with `P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ h')))`. Conclude with `(notMem_of_split _ hctx hS h').2 hP`.

Conclude with `(P.isPrime.mem_or_mem ((hPr.piG_norm i).symm ▸ hP)).resolve_left h`. Establish `hππ : D.host.φ₀ πE * conj (D.host.φ₀ πE) = (D.host.g i : ℂ)`. Rewrite using `[← GlobalTheory.QuadSubfield.emb_conj, ← map_mul, EX.piG_norm i, map_natCast]`. Use `datum_bound _ hctx hN hN' hA0 hB0 hg w _ Ξ hΞ hrat fun c' x hc0 hc' hx => hval _ ?_` and prove the remaining obligations. Establish `key` using `hJ (recSeam D) B χ cD hs hcc hA.1 hA.2.1 _ b _ N N' (D.host.g i) ι (hev j) hb' hN hN' (hstd hN.1.fg hsN) (hstd hN'.1.fg hsN') hdisc hcD h5 hpd hctx.2.1 _ _ (isQInt_piG EX i) hππ hsplit c' x hc0 hc' hx e`.

Establish `hκ : (recSeam D).σ₀ (e.prod fun k n => (recFields D).emb k.1 (star πE) ^ n) = conj (D.host.φ₀ πE) ^ e.degree`. Rewrite using `[map_finsuppProd, Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [map_pow]; exact congrArg (· ^ e k) (hτ' k.1)`. Rewrite using `[map_mul (recSeam D).σ₀, map_mul (recSeam D).σ₀, hκ]`. Simplify using `only [map_mul, map_pow, map_natCast, norm_mul, norm_pow]`.

Use `le_of_eq_of_le ?_ key` and prove the remaining obligations. Rewrite using `[Fields.f, mul_right_comm (Fintype.card _)]`. Conclude with `(mul_comm _ _).trans ((congrArg _ (mul_comm _ _)).trans (mul_assoc _ _ _).symm)`.
-/
theorem jetLossAll_of_jetSplitAmb : JetSplitAmb → ∀ (D : D7) (EX : ErrX D)
    (sel : HeightOneSpectrum (𝓞 D.host.F) → HeightOneSpectrum (𝓞 D.host.E)) (δ : ℂ) (B : Base D D.host.ccK δ) (χ : TaylorLogMetric.IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), GlobalTheory.ColPeriod.JetLossAll D EX sel B χ cD := by
  intro hJ D EX sel δ B χ cD hH hsel hA i w hw u mu cst hcst j b _ hb N N' hN hN' hsN hsN' Ξ hΞ e _ hrat
  have hPr := hH.2.2.2.2
  have hX := hH.2.2.2.1.ok
  have hp : (D.host.g i).Prime := hPr.g_prime i
  have : Fact (D.host.g i).Prime := ⟨hp⟩
  have hs : (recSeam D).Ok := ⟨GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound.recSeam_emb D, bridge_star_holds D.R D.host⟩
  have hcc : TaylorLogMetric.IsCurveIdeal D D.host.ccK := by rw [hH.1]; exact ⟨by simp, by simp⟩
  have hev : ∀ j, Even (D.R.N j) := fun j => D.R.k_even.add (D.R.t_odd.add_one.mul_left j)
  have hb' : Even b := hb ▸ hev _
  have hV : B.VecP χ := GlobalTheory.ColNorms.familyVectors D _ δ B χ hH.2.2.1 hH.2.1 hcc hA.1 hA.2.1 (GlobalTheory.ExponentsFinite.yFinite _ _ _)
  obtain ⟨hL, hE⟩ := GlobalTheory.ThetaMove.LatticeFacts.laHyp_and_eSmooth D _ (recSeam D) _ δ B χ cD _ b hX hs hcc hA.1 hV (hev j) hb'
  obtain ⟨hctx, hA0, hB0, hg⟩ := GlobalTheory.T.datumJets_typePrimeBadPrimesLevelsHypotheses D EX sel δ B χ cD hH hsel i u mu cst hcst _ b hL hE
  have hcong : D.host.g i ≡ 1 [MOD D.host.QS * D.host.q * D.host.d] := hPr.g_cong i
  have hnd : ∀ t, t ∣ D.host.QS * D.host.q * D.host.d → ¬ D.host.g i ∣ t := fun t ht h =>
    hp.one_lt.ne' (Nat.dvd_one.1 ((Nat.modEq_zero_iff_dvd.1
      ((hcong.of_dvd (h.trans ht)).symm.trans (Nat.modEq_zero_iff_dvd.2 dvd_rfl)))))
  have h5 : 5 ≤ D.host.g i := by
    have h4 : D.host.g i ≡ 1 [MOD 4] := hcong.of_dvd ((by norm_num : 4 ∣ 16).trans D.host.toHostRaw.sixteen_dvd_condN)
    have := hp.one_lt
    unfold Nat.ModEq at h4
    omega
  have hpd : ¬ D.host.g i ∣ D.host.d := hnd _ (Dvd.intro_left _ rfl)
  have hpq : D.host.g i ≠ D.host.q := fun h => hnd D.host.q D.host.toHostRaw.q_dvd_condN h.dvd
  have hdisc := GlobalTheory.GoodDepth.not_dvd_discr_host D.R D.host _ hp (UpperTheory.Ram.g_notMem_small D i) hpq fun h => hpd h.dvd
  obtain ⟨lam, hlam⟩ := GlobalTheory.T.place_over_p_induced_by_algebraic_padic_embedding _ (recSeam D).σ₀ (D.host.g i) w hw
  obtain ⟨ι, hι⟩ := GlobalTheory.ThLoc.place_extends_to_iso _ lam
  have hιC : ∀ x ∈ TaylorLogMetric.Qbar, TaylorLogMetric.lamC lam x = ι x := fun x hx => by rw [TaylorLogMetric.lamC, dif_pos hx]; exact (hι ⟨x, hx⟩).symm
  have hval : ∀ k : D.what₂.LL, ‖ι ((recSeam D).σ₀ k)‖ ≤ 1 → w.valuation _ k ≤ 1 := fun k hk => by
    have hq : (recSeam D).σ₀ k ∈ TaylorLogMetric.Qbar := by
      rw [mem_algebraicClosure_iff]
      exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) k).algHom (recSeam D).σ₀.toRatAlgHom
    exact (hlam k).1 ⟨hq, by rwa [hιC _ hq]⟩
  have hcD : ∀ τ, ‖ι (cD τ)‖ ≤ 1 := fun τ => by
    obtain ⟨M, _, hM, hs⟩ := hA.2.2
    obtain ⟨s, hsc, hsp⟩ := hs τ
    rw [← hsc, ← hιC _ (GlobalTheory.EigenGenerator.mem_Qbar M s)]
    exact (GlobalTheory.EigenGenerator.norm_generator_eq_one D _ lam (UpperTheory.Ram.g_notMem_small D i) hpq M hM τ s hsp).le
  have hstd : ∀ {n : ℕ} {L : Submodule (𝓞 D.host.E) (Sp D.host.E n)}, L.FG → GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.StdOver (D.host.g i) L →
      (recSeam D).StdAtP (D.host.g i) L := fun hL h => by
    obtain ⟨s, hs, h1, h2⟩ := GlobalTheory.LiftTypePrime.ProdComb.eqAt_std (GlobalTheory.DatumJets.Transl.stdAt_of_stdOver D hp hL h)
    exact ⟨s, hs, h2, h1⟩
  set πE : D.host.E := ((EX.piG i : 𝓞 D.host.E) : D.host.E) with hπE
  have hτ : ∀ τ, (recFields D).embC (recSeam D).σ₀ τ πE = D.host.φ₀ πE := fun τ =>
    (hs.1 τ πE).trans (hH.2.1 τ ⟨πE, EX.piG_K i⟩)
  have hτ' : ∀ τ, (recFields D).embC (recSeam D).σ₀ τ (star πE) = conj (D.host.φ₀ πE) := fun τ => by
    rw [hX.conjE, hτ]
  have hπ0 : (recFields D).conjO (EX.piG i) ≠ 0 :=
    right_ne_zero_of_mul (by rw [hPr.piG_norm i]; exact_mod_cast hp.ne_zero)
  have hcc' : (recFields D).conjO ((recFields D).conjO (EX.piG i)) = EX.piG i := Subtype.ext (star_star _)
  have hsplit : Formalism.L2.AlgTh.SplitS (ambOf (recSeam D) B χ cD) (Sall sel mu u) (D.host.g i) (D.host.φ₀ πE) (EX.piG i) := by
    refine ⟨hτ, hτ', fun P hP => ⟨fun hS h => ?_, fun h => hctx.2.2.2.2.2.2.2 P ?_⟩⟩
    · by_cases h' : (recFields D).conjO (EX.piG i) ∈ P.asIdeal
      · obtain ⟨x, y, hxy⟩ := hPr.piG_cop i
        exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hxy ▸ add_mem (P.asIdeal.mul_mem_left _ h) (P.asIdeal.mul_mem_left _ h')))
      · exact (notMem_of_split _ hctx hS h').2 hP
    · exact (P.isPrime.mem_or_mem ((hPr.piG_norm i).symm ▸ hP)).resolve_left h
  have hππ : D.host.φ₀ πE * conj (D.host.φ₀ πE) = (D.host.g i : ℂ) := by
    rw [← GlobalTheory.QuadSubfield.emb_conj, ← map_mul, EX.piG_norm i, map_natCast]
  refine datum_bound _ hctx hN hN' hA0 hB0 hg w _ Ξ hΞ hrat fun c' x hc0 hc' hx => hval _ ?_
  have key := hJ (recSeam D) B χ cD hs hcc hA.1 hA.2.1 _ b _ N N' (D.host.g i) ι (hev j) hb' hN hN' (hstd hN.1.fg hsN)
    (hstd hN'.1.fg hsN') hdisc hcD h5 hpd hctx.2.1 _ _ (isQInt_piG EX i) hππ hsplit c' x hc0 hc' hx e
  have hκ : (recSeam D).σ₀ (e.prod fun k n => (recFields D).emb k.1 (star πE) ^ n) = conj (D.host.φ₀ πE) ^ e.degree := by
    rw [map_finsuppProd, Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun k _ => by rw [map_pow]; exact congrArg (· ^ e k) (hτ' k.1)
  rw [map_mul (recSeam D).σ₀, map_mul (recSeam D).σ₀, hκ]
  simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  refine le_of_eq_of_le ?_ key
  rw [Fields.f, mul_right_comm (Fintype.card _)]
  exact (mul_comm _ _).trans ((congrArg _ (mul_comm _ _)).trans (mul_assoc _ _ _).symm)

end GlobalTheory.JetsFromTables
