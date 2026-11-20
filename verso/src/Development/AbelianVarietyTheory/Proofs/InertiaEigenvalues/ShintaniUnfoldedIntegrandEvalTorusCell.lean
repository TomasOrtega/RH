import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDiagonalUniformizerEqZeroOfNotAntitoneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCellDecompositionLastRowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceIndicatorDiagonalUniformizerMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdelicAbsDetPowDiagonalUniformizerMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergLocalTermEqSphericalWhittakerProducStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOffStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.ZEul

/- English proof (translation)
Introduce `E _ _ _ n g`. Simplify using `[GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, GlobalTheory.Mem.Chr.CharModel.absHom_val]`.
-/
theorem detPow_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (g : GA E n),
    GlobalTheory.RSJ.detPow E n 0 g = 1 := by
  intro E _ _ _ n g
  simp [GlobalTheory.RSJ.detPow, chiDet, GlobalTheory.HeckeGal.Model.absPow, GlobalTheory.Mem.Chr.CharModel.absHom_val]

/- English proof (translation)
Introduce `E _ _ _ m ϖ l g`. Use function extensionality and compare the values at `i`. Establish `h` using `congrArg (fun M : GL (Fin (m + 1)) (Cinf E) => (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) i) (show Matrix.GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl (m + 1) ϖ l * g) = Matrix.GeneralLinearGroup.map (pInf E) g by rw [map_mul, GlobalTheory.CellDec. …`. Conclude with `h`.
-/
theorem pInf_lastRow_tl_mul : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℤ))
    (g : GA E (m + 1)),
    (fun i => pInf E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l * g) i)) = fun i => pInf E (GlobalTheory.ZEul.lastRow g i) := by
  intro E _ _ _ m ϖ l g
  funext i
  have h := congrArg (fun M : GL (Fin (m + 1)) (Cinf E) => (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) i)
    (show Matrix.GeneralLinearGroup.map (pInf E) (GlobalTheory.CellDec.tl (m + 1) ϖ l * g) =
      Matrix.GeneralLinearGroup.map (pInf E) g by rw [map_mul, GlobalTheory.CellDec.tl, pInf_finGL, one_mul])
  exact h

/- English proof (translation)
Introduce `E _ _ _ m S hψ ϖ hϖ b α α' φ φ' N J Φ hJ hint hS hloc hΦ hNφ hNφ' hKφ hKφ' hWφ hWφ' x g hg`. Establish `hWp : ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit φ p = b p ∧ GlobalTheory.JSW.whit φ' p = b p`. Introduce `p hp`. Establish `h0 : GlobalTheory.JSW.tl ϖ (0 : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)) = 1` using `by simp [GlobalTheory.JSW.tl]`. Establish `e1` using `hWφ 0 (by simp) p hp`.

Establish `e2` using `hWφ' 0 (by simp) p hp`. Rewrite `e1`, `e2` using `[h0, mul_one]`. Simplify using `only [Finsupp.support_zero, Finset.prod_empty, mul_one] at e1 e2`. Conclude with `⟨e1, e2⟩`. Establish `hnorm : ∀ u : GA E (m + 1), ‖GlobalTheory.JSW.psiN u‖ = 1` using `fun u => Circle.norm_coe _`.

Establish `hcc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z z' : ℂ, c * z * conj (c * z') = z * conj z'`. Introduce `c hc z z'`. Rewrite using `[map_mul]`. Establish `: c * conj c = 1`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Establish `hzero : ∀ F F' : GA E (m + 1) → ℂ, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨ GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0 → GlobalTheory.ZEul.uInt F F' Φ N 0 g = 0`. Introduce `F F' h`. Apply the tactic sequence `rcases h with h | h <;> simp only [GlobalTheory.ZEul.uInt, h, mul_zero, zero_mul]`.

Establish `hdec : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 → GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), ∃ p ∈ GlobalTheory.JSW.mirS E S m, ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) …`. Introduce `h1 h2`. Take `⟨u, hu, p, hp, κ, hκ, he⟩` from `GlobalTheory.T.mirabolicCell_decomposition_lastRow E m S J hJ N hS Φ hΦ g hg h1 h2`. Establish `k1 : GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) = GlobalTheory.JSW.psiN u * b p` using `by rw [he, hKφ κ hκ, hNφ u hu, (hWp p hp).1]`. Establish `k2 : GlobalTheory.JSW.whit φ' (g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) = GlobalTheory.JSW.psiN u * b p` using `by rw [he, hKφ' κ hκ, hNφ' u hu, (hWp p hp).2]`.

Apply the tactic sequence `refine ⟨u, hu, p, hp, κ, hκ, he, ?_, ?_, ?_⟩ <;>`. Simplify using `only [GlobalTheory.ZEul.uInt, k1, k2, hcc _ (hnorm u), GlobalTheory.ZEul.detPow_zero, Complex.ofReal_one, mul_one]`. Establish `h12 : GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧ GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g`. Distinguish the cases in `h0 : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨ GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0`. Rewrite using `[hzero _ _ h0, hzero _ _ h0, hzero _ _ h0]`.

Conclude with `⟨rfl, rfl⟩`. Use `push_neg at h0`. Take `⟨-, -, p, -, -, -, -, e1, e2, e3⟩` from `hdec h0.1 h0.2`. Rewrite using `[e1, e2, e3]`. Conclude with `⟨rfl, rfl⟩`.

Use `⟨h12.1, h12.2, fun l => ?_⟩` and prove the remaining obligations. Establish `hyt` using `GlobalTheory.ZEul.pInf_lastRow_tl_mul E m ϖ l.1 g`. Take `⟨hind1, hind2⟩` from `GlobalTheory.T.lastRowCongruenceIndicator_diagonalUniformizer_mul E m S ϖ hϖ N hint hloc l g hg`. Establish `hdt` using `GlobalTheory.T.idelicAbsDetPow_diagonalUniformizer_mul E (m + 1) ϖ hϖ l.1 x g`. Establish `hL : GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) = GlobalTheory.JSW.whit φ (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) * conj (GlobalTheory.JSW.whit φ' (G …`.

Simplify using `only [GlobalTheory.ZEul.uInt]`. Rewrite using `[hyt]`. Rewrite using `[hL]`. Establish `hprod0 : ∀ w ∈ l.1.support, GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x (l.1 w) = 0 → (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x v) = 0` using `fun w hw h => Finset.prod_eq_zero hw h`. Distinguish the cases in `hz : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨ GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0`.

Establish `hIt : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨ GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0`. Break down `hz with h | h` into its components or cases. Conclude with `Or.inl h`. Use `right`. Distinguish the cases in `hl : ∀ w, 0 ≤ l.1 w (Fin.last m)`.

Rewrite using `[hind1 hl, h]`. Use `push_neg at hl`. Conclude with `hind2 hl`. Rewrite using `[hzero φ φ hz]`. Apply the tactic sequence `rcases hIt with h | h <;> simp [h]`.

Use `push_neg at hz`. Distinguish the cases in `hlast : ∀ w, 0 ≤ l.1 w (Fin.last m)`. Use `swap`. Use `push_neg at hlast`. Take `⟨w, hw⟩` from `hlast`.

Establish `hws : w ∈ l.1.support`. Rewrite using `[Finsupp.mem_support_iff]`. Introduce `h0`. Rewrite `hw` using `[h0]`. Simplify using `at hw`.

Rewrite using `[hind2 ⟨w, hw⟩, hprod0 w hws ?_]`. Simplify using the standard rewrite rules. Rewrite using `[GlobalTheory.ZEul.rsTerm, if_neg]`. Introduce and unpack `⟨h1, -⟩`. Conclude with `absurd (h1 (Fin.last m)) (not_le.2 hw)`.

Rewrite using `[hind1 hlast]`. Take `⟨u, hu, p, hp, κ, hκ, he, -, e0, -⟩` from `hdec hz.1 hz.2`. Rewrite using `[e0]`. Use `set t := GlobalTheory.CellDec.tl (m + 1) ϖ l.1 with ht`. Establish `hcomm : p * t = t * p` using `GlobalTheory.T.adelicDiagonalUniformizer_commute_of_one_off E (m + 1) S ϖ l p hp.1`.

Establish `hu' : t * u * t⁻¹ ∈ GlobalTheory.JSW.NA E (m + 1)` using `(GlobalTheory.SmGL.mem_unipB (Ad E)).1 (GlobalTheory.CellDec.tl_conj_mem ϖ l.1 ((GlobalTheory.SmGL.mem_unipB (Ad E)).2 hu))`. Establish `hσ : t * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = (t * u * t⁻¹) * (p * t) * finGL E (m + 1) κ`. Rewrite using `[mul_assoc t g, he, hcomm]`. Use `group`. Establish `hW : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, F (u * g) = GlobalTheory.JSW.psiN u * F g) → (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, F (g * finGL E (m + 1) κ) = F g) → F (t * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (G …`.

Introduce `F hN hK`. Rewrite using `[hσ, hK κ hκ, hN _ hu']`. Rewrite using `[hW _ hNφ hKφ, hW _ hNφ' hKφ', hcc _ (hnorm _)]`. Distinguish the cases in `hanti : ∀ w, Antitone (l.1 w)`. Use `swap`.

Use `push_neg at hanti`. Take `⟨w, hw⟩` from `hanti`. Establish `hw0 : l.1 w ≠ 0` using `by rintro h0; rw [h0] at hw; exact hw antitone_const`. Establish `hwS : w ∉ S` using `fun h => hw0 (l.2 w h)`. Establish `hws : w ∈ l.1.support` using `Finsupp.mem_support_iff.2 hw0`.

Rewrite using `[GlobalTheory.T.whittaker_diagonalUniformizer_eq_zero_of_not_antitone E m S J w hwS (hψ w hwS) ϖ (hϖ w) (GlobalTheory.JSW.whit φ) hNφ hKφ l.1 hw p (hp.1 w hwS), hprod0 w hws ?_]`. Simplify using the standard rewrite rules. Rewrite using `[GlobalTheory.ZEul.rsTerm, if_neg]`. Introduce and unpack `⟨-, h2⟩`. Conclude with `hw h2`.

Establish `hnn : ∀ w i, 0 ≤ l.1 w i` using `fun w i => le_trans (hlast w) (hanti w (Fin.le_last i))`. Take `⟨l', hl'app⟩ : ∃ l' : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), ∀ w, l' w = fun i => (l.1 w i).toNat` from `⟨Finsupp.mapRange (fun v i => (v i).toNat) (funext fun _ => rfl) l.1, fun w => Finsupp.mapRange_apply⟩`. Establish `hl' : ∀ w i, ((l' w i : ℕ) : ℤ) = l.1 w i` using `fun w i => by`. Rewrite using `[hl'app]`. Conclude with `Int.toNat_of_nonneg (hnn w i)`.

Establish `hsupp : l'.support = l.1.support`. Use extensionality with `w`. Simplify using `only [Finsupp.mem_support_iff, ne_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h h0`.

Apply `h` to reduce the goal to its premises. Rewrite using `[hl'app, h0]`. Both sides reduce to the same expression. Introduce `h h0`. Apply `h` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Use `hl' w i` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `using this.symm`. Establish `htl : t = GlobalTheory.JSW.tl ϖ l'` using `GlobalTheory.T.adelicDiagonalUniformizer_eq_prod_localDiagonal E (m + 1) ϖ l.1 l' hl'`.

Establish `hsS : ∀ w ∈ l'.support, w ∉ S` using `fun w hw hS' => by`. Rewrite `hw` using `[hsupp, Finsupp.mem_support_iff]`. Conclude with `hw (l.2 w hS')`. Rewrite using `[hdt, htl, hWφ l' hsS p hp, hWφ' l' hsS p hp, hsupp]`. Establish `key : ((GlobalTheory.CellDec.dinv (m + 1) l.1 : ℝ) : ℂ) * ((∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l' w)) * conj (∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l' w))) * (((∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-x * ∑ i …`.

Rewrite using `[map_prod, ← Finset.prod_mul_distrib, GlobalTheory.CellDec.dinv, Complex.ofReal_prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finsupp.prod]`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `hq : 0 < qV E w` using `Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Rewrite using `[hl'app]`. Conclude with `GlobalTheory.T.rankinSelbergLocalTerm_eq_sphericalWhittaker_product (qV E w) hq (m + 1) _ _ x (l.1 w) (hnn w) (hanti w)`.

Rewrite using `[← key]`. Simplify using `only [map_mul, Complex.ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem uInt_cell_eval : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) →
    ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ (b : GA E (m + 1) → ℂ) (α α' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ) (φ φ' : GA E (m + 1) → ℂ)
      (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v : HeightOneSpectrum (𝓞 E), z v ∈ v.adicCompletionIntegers E) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    (∀ z z' : Af E, (∀ v ∈ S, z v = z' v) → (∀ v ∉ S, z v ∈ v.adicCompletionIntegers E) →
        (∀ v ∉ S, z' v ∈ v.adicCompletionIntegers E) → (z ∈ GlobalTheory.RSJ.natLat E N ↔ z' ∈ GlobalTheory.RSJ.natLat E N)) →
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ' g) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ GlobalTheory.JSW.mirS E S m,
      GlobalTheory.JSW.whit φ (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) →
    (∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ GlobalTheory.JSW.mirS E S m,
      GlobalTheory.JSW.whit φ' (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l w)) →
    ∀ x : ℝ, ∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S,
      GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧ GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧
      ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x v) *
            GlobalTheory.ZEul.uInt φ φ Φ N 0 g * (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) := by
  intro E _ _ _ m S hψ ϖ hϖ b α α' φ φ' N J Φ hJ hint hS hloc hΦ hNφ hNφ' hKφ hKφ' hWφ hWφ' x g hg
  have hWp : ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit φ p = b p ∧ GlobalTheory.JSW.whit φ' p = b p := by
    intro p hp
    have h0 : GlobalTheory.JSW.tl ϖ (0 : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ)) = 1 := by simp [GlobalTheory.JSW.tl]
    have e1 := hWφ 0 (by simp) p hp
    have e2 := hWφ' 0 (by simp) p hp
    rw [h0, mul_one] at e1 e2
    simp only [Finsupp.support_zero, Finset.prod_empty, mul_one] at e1 e2
    exact ⟨e1, e2⟩
  have hnorm : ∀ u : GA E (m + 1), ‖GlobalTheory.JSW.psiN u‖ = 1 := fun u => Circle.norm_coe _
  have hcc : ∀ c : ℂ, ‖c‖ = 1 → ∀ z z' : ℂ, c * z * conj (c * z') = z * conj z' := by
    intro c hc z z'
    rw [map_mul]
    have : c * conj c = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
    calc c * z * (conj c * conj z') = (c * conj c) * (z * conj z') := by ring
      _ = _ := by rw [this, one_mul]
  have hzero : ∀ F F' : GA E (m + 1) → ℂ, Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0 → GlobalTheory.ZEul.uInt F F' Φ N 0 g = 0 := by
    intro F F' h
    rcases h with h | h <;> simp only [GlobalTheory.ZEul.uInt, h, mul_zero, zero_mul]
  have hdec : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), ∃ p ∈ GlobalTheory.JSW.mirS E S m, ∃ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J,
        g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = u * p * finGL E (m + 1) κ ∧
        GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ∧
        GlobalTheory.ZEul.uInt φ φ Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) ∧
        GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = b p * conj (b p) * Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
          GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) := by
    intro h1 h2
    obtain ⟨u, hu, p, hp, κ, hκ, he⟩ := GlobalTheory.T.mirabolicCell_decomposition_lastRow E m S J hJ N hS Φ hΦ g hg h1 h2
    have k1 : GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN u * b p := by rw [he, hKφ κ hκ, hNφ u hu, (hWp p hp).1]
    have k2 : GlobalTheory.JSW.whit φ' (g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN u * b p := by rw [he, hKφ' κ hκ, hNφ' u hu, (hWp p hp).2]
    refine ⟨u, hu, p, hp, κ, hκ, he, ?_, ?_, ?_⟩ <;>
      simp only [GlobalTheory.ZEul.uInt, k1, k2, hcc _ (hnorm u), GlobalTheory.ZEul.detPow_zero, Complex.ofReal_one, mul_one]
  have h12 : GlobalTheory.ZEul.uInt φ φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g ∧
      GlobalTheory.ZEul.uInt φ' φ' Φ N 0 g = GlobalTheory.ZEul.uInt φ φ Φ N 0 g := by
    by_cases h0 : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0
    · rw [hzero _ _ h0, hzero _ _ h0, hzero _ _ h0]; exact ⟨rfl, rfl⟩
    push_neg at h0
    obtain ⟨-, -, p, -, -, -, -, e1, e2, e3⟩ := hdec h0.1 h0.2
    rw [e1, e2, e3]; exact ⟨rfl, rfl⟩
  refine ⟨h12.1, h12.2, fun l => ?_⟩

  have hyt := GlobalTheory.ZEul.pInf_lastRow_tl_mul E m ϖ l.1 g
  obtain ⟨hind1, hind2⟩ := GlobalTheory.T.lastRowCongruenceIndicator_diagonalUniformizer_mul E m S ϖ hϖ N hint hloc l g hg
  have hdt := GlobalTheory.T.idelicAbsDetPow_diagonalUniformizer_mul E (m + 1) ϖ hϖ l.1 x g
  have hL : GlobalTheory.ZEul.uInt φ φ' Φ N x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
      GlobalTheory.JSW.whit φ (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
        infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) *
      conj (GlobalTheory.JSW.whit φ' (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g *
        infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))) *
      Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) *
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) *
      (GlobalTheory.RSJ.detPow E (m + 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) : ℂ) := by
    simp only [GlobalTheory.ZEul.uInt]; rw [hyt]
  rw [hL]
  have hprod0 : ∀ w ∈ l.1.support, GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
      (fun i => (α' w i : ℂ)) x (l.1 w) = 0 →
      (l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (α' w i : ℂ)) x v) = 0 :=
    fun w hw h => Finset.prod_eq_zero hw h
  by_cases hz : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
      GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0
  · have hIt : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) = 0 ∨
        GlobalTheory.RSJ.indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) i)) = 0 := by
      rcases hz with h | h
      · exact Or.inl h
      · right
        by_cases hl : ∀ w, 0 ≤ l.1 w (Fin.last m)
        · rw [hind1 hl, h]
        · push_neg at hl; exact hind2 hl
    rw [hzero φ φ hz]
    rcases hIt with h | h <;> simp [h]
  push_neg at hz
  by_cases hlast : ∀ w, 0 ≤ l.1 w (Fin.last m)
  swap
  · push_neg at hlast
    obtain ⟨w, hw⟩ := hlast
    have hws : w ∈ l.1.support := by
      rw [Finsupp.mem_support_iff]; intro h0; rw [h0] at hw; simp at hw
    rw [hind2 ⟨w, hw⟩, hprod0 w hws ?_]
    · simp
    · rw [GlobalTheory.ZEul.rsTerm, if_neg]; rintro ⟨h1, -⟩; exact absurd (h1 (Fin.last m)) (not_le.2 hw)
  rw [hind1 hlast]
  obtain ⟨u, hu, p, hp, κ, hκ, he, -, e0, -⟩ := hdec hz.1 hz.2
  rw [e0]
  set t := GlobalTheory.CellDec.tl (m + 1) ϖ l.1 with ht
  have hcomm : p * t = t * p := GlobalTheory.T.adelicDiagonalUniformizer_commute_of_one_off E (m + 1) S ϖ l p hp.1
  have hu' : t * u * t⁻¹ ∈ GlobalTheory.JSW.NA E (m + 1) :=
    (GlobalTheory.SmGL.mem_unipB (Ad E)).1 (GlobalTheory.CellDec.tl_conj_mem ϖ l.1 ((GlobalTheory.SmGL.mem_unipB (Ad E)).2 hu))
  have hσ : t * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) =
      (t * u * t⁻¹) * (p * t) * finGL E (m + 1) κ := by
    rw [mul_assoc t g, he, hcomm]; group
  have hW : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, F (u * g) = GlobalTheory.JSW.psiN u * F g) →
      (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, F (g * finGL E (m + 1) κ) = F g) →
      F (t * g * infGL E (m + 1) (GlobalTheory.RSJ.secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) =
        GlobalTheory.JSW.psiN (t * u * t⁻¹) * F (p * t) := by
    intro F hN hK; rw [hσ, hK κ hκ, hN _ hu']
  rw [hW _ hNφ hKφ, hW _ hNφ' hKφ', hcc _ (hnorm _)]
  by_cases hanti : ∀ w, Antitone (l.1 w)
  swap
  · push_neg at hanti
    obtain ⟨w, hw⟩ := hanti
    have hw0 : l.1 w ≠ 0 := by rintro h0; rw [h0] at hw; exact hw antitone_const
    have hwS : w ∉ S := fun h => hw0 (l.2 w h)
    have hws : w ∈ l.1.support := Finsupp.mem_support_iff.2 hw0
    rw [GlobalTheory.T.whittaker_diagonalUniformizer_eq_zero_of_not_antitone E m S J w hwS (hψ w hwS) ϖ (hϖ w) (GlobalTheory.JSW.whit φ) hNφ hKφ l.1 hw p (hp.1 w hwS), hprod0 w hws ?_]
    · simp
    · rw [GlobalTheory.ZEul.rsTerm, if_neg]; rintro ⟨-, h2⟩; exact hw h2
  have hnn : ∀ w i, 0 ≤ l.1 w i := fun w i => le_trans (hlast w) (hanti w (Fin.le_last i))
  obtain ⟨l', hl'app⟩ : ∃ l' : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), ∀ w, l' w = fun i => (l.1 w i).toNat :=
    ⟨Finsupp.mapRange (fun v i => (v i).toNat) (funext fun _ => rfl) l.1, fun w => Finsupp.mapRange_apply⟩
  have hl' : ∀ w i, ((l' w i : ℕ) : ℤ) = l.1 w i := fun w i => by
    rw [hl'app]; exact Int.toNat_of_nonneg (hnn w i)
  have hsupp : l'.support = l.1.support := by
    ext w
    simp only [Finsupp.mem_support_iff, ne_eq]
    constructor
    · intro h h0; apply h; rw [hl'app, h0]; rfl
    · intro h h0; apply h; funext i; have := hl' w i; rw [h0] at this; simpa using this.symm
  have htl : t = GlobalTheory.JSW.tl ϖ l' := GlobalTheory.T.adelicDiagonalUniformizer_eq_prod_localDiagonal E (m + 1) ϖ l.1 l' hl'
  have hsS : ∀ w ∈ l'.support, w ∉ S := fun w hw hS' => by
    rw [hsupp, Finsupp.mem_support_iff] at hw; exact hw (l.2 w hS')
  rw [hdt, htl, hWφ l' hsS p hp, hWφ' l' hsS p hp, hsupp]
  have key : ((GlobalTheory.CellDec.dinv (m + 1) l.1 : ℝ) : ℂ) *
      ((∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l' w)) *
        conj (∏ w ∈ l.1.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l' w))) *
      (((∏ w ∈ l.1.support, (qV E w : ℝ) ^ (-x * ∑ i, (l.1 w i : ℝ))) : ℝ) : ℂ) =
      l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (α w i : ℂ))
        (fun i => (α' w i : ℂ)) x v := by
    rw [map_prod, ← Finset.prod_mul_distrib, GlobalTheory.CellDec.dinv, Complex.ofReal_prod, Complex.ofReal_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, Finsupp.prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    have hq : 0 < qV E w := Nat.pos_of_ne_zero fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    rw [hl'app]
    exact GlobalTheory.T.rankinSelbergLocalTerm_eq_sphericalWhittaker_product (qV E w) hq (m + 1) _ _ x (l.1 w) (hnn w) (hanti w)
  rw [← key]
  simp only [map_mul, Complex.ofReal_mul]
  ring

end GlobalTheory.ZEul
