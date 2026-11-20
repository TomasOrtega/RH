import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartFromAdelicDictionary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFramedLevelIffTwoAdelicPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedPointClassesBijectiveDoubleCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StabIffMemConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsK1PointCongruent
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology MeasureTheory
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC
open Formalism.MainNotions Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Col2.TopCh
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopStepPrimes

open IsDedekindDomain.HeightOneSpectrum GlobalTheory.TopStep

/- English proof (translation)
Establish `hlt : P.valuation E x < 1` using `h.trans_lt (by decide)`. Take `⟨n, d, hnd⟩` from `P.exists_primeCompl_mul_eq_of_integer x hlt.le`. Establish `hd : (d : 𝓞 E) ∉ P.asIdeal` using `d.2`. Establish `hdv : P.valuation E (algebraMap (𝓞 E) E d) = 1`. Rewrite using `[valuation_of_algebraMap]`.

Conclude with `le_antisymm (P.intValuation_le_one _) (not_lt.1 fun hc => hd ((P.intValuation_lt_one_iff_mem _).1 hc))`. Establish `hn : n ∈ P.asIdeal`. Rewrite using `[← P.valuation_lt_one_iff_mem (K := E)]`. Express the relevant statement in the definitionally equal form `P.valuation E (algebraMap (𝓞 E) E n) < 1`. Rewrite using `[← hnd, map_mul, hdv, mul_one]`.

Conclude with `hlt`. Establish `hs` using `reduction_spec P hd (a := x) (r := n) (by rw [mul_comm]; exact hnd)`. Rewrite `hs` using `[Ideal.Quotient.eq_zero_iff_mem.2 hn]`. Conclude with `(mul_eq_zero.1 hs).resolve_left (mk_ne_zero hd)`.
-/
theorem reduction_eq_zero_of_valuation_le {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {x : E}
    (h : P.valuation E x ≤ WithZero.coe (Multiplicative.ofAdd (-((1 : ℕ) : ℤ)))) : redP P x = 0 := by
  have hlt : P.valuation E x < 1 := h.trans_lt (by decide)
  obtain ⟨n, d, hnd⟩ := P.exists_primeCompl_mul_eq_of_integer x hlt.le
  have hd : (d : 𝓞 E) ∉ P.asIdeal := d.2
  have hdv : P.valuation E (algebraMap (𝓞 E) E d) = 1 := by
    rw [valuation_of_algebraMap]
    exact le_antisymm (P.intValuation_le_one _) (not_lt.1 fun hc => hd ((P.intValuation_lt_one_iff_mem _).1 hc))
  have hn : n ∈ P.asIdeal := by
    rw [← P.valuation_lt_one_iff_mem (K := E)]
    change P.valuation E (algebraMap (𝓞 E) E n) < 1
    rw [← hnd, map_mul, hdv, mul_one]
    exact hlt
  have hs := reduction_spec P hd (a := x) (r := n) (by rw [mul_comm]; exact hnd)
  rw [Ideal.Quotient.eq_zero_iff_mem.2 hn] at hs
  exact (mul_eq_zero.1 hs).resolve_left (mk_ne_zero hd)

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[redGL_val]`. Use extensionality with `i j`. Establish `h2 : LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) i j = g.1 (Pi.single j 1) i`. Rewrite using `[LinearMap.toMatrix'_apply]`.

Both sides reduce to the same expression. Establish `hv` using `hg i j`. Rewrite `hv` using `[Matrix.sub_apply, h2]`. Apply the tactic sequence `have hx := glint_entry g i j`. Establish `hδ : IntAt P ((1 : Matrix (Fin n) (Fin n) E) i j)`.

Distinguish the cases in `hij : i = j`. Simplify `intAt_one` using `[Matrix.one_apply, hij]`. Simplify `intAt_zero` using `[Matrix.one_apply, hij]`. Establish `hr : redP P ((1 : Matrix (Fin n) (Fin n) E) i j) = (1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j`. Distinguish the cases in `hij : i = j`.

Simplify `reduction_one₂` using `[Matrix.one_apply, hij]`. Simplify `reduction_zero` using `[Matrix.one_apply, hij]`. Establish `e : g.1 (Pi.single j 1) i = (g.1 (Pi.single j 1) i - (1 : Matrix (Fin n) (Fin n) E) i j) + (1 : Matrix (Fin n) (Fin n) E) i j` using `by ring`. Use `show redP P (g.1 (Pi.single j 1) i) = _`. Rewrite using `[e, reduction_add (intAt_sub hx hδ) hδ, reduction_eq_zero_of_valuation_le hv, zero_add, hr]`.

Both sides reduce to the same expression.
-/
theorem redGL_eq_one_of_lqPrinc {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    (g : GLint E n P) (hg : lqPrinc P 1 (g : Sp E n ≃ₗ[E] Sp E n)) : redGL n P g = 1 := by
  apply Units.ext
  rw [redGL_val]
  ext i j
  have h2 : LinearMap.toMatrix' ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) i j = g.1 (Pi.single j 1) i := by
    rw [LinearMap.toMatrix'_apply]
    rfl
  have hv := hg i j
  rw [Matrix.sub_apply, h2] at hv
  have hx := glint_entry g i j
  have hδ : IntAt P ((1 : Matrix (Fin n) (Fin n) E) i j) := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using intAt_one
    · simpa [Matrix.one_apply, hij] using intAt_zero
  have hr : redP P ((1 : Matrix (Fin n) (Fin n) E) i j) = (1 : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) i j := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using reduction_one₂
    · simpa [Matrix.one_apply, hij] using reduction_zero
  have e : g.1 (Pi.single j 1) i = (g.1 (Pi.single j 1) i - (1 : Matrix (Fin n) (Fin n) E) i j) +
      (1 : Matrix (Fin n) (Fin n) E) i j := by ring
  show redP P (g.1 (Pi.single j 1) i) = _
  rw [e, reduction_add (intAt_sub hx hδ) hδ, reduction_eq_zero_of_valuation_le hv, zero_add, hr]
  rfl

end GlobalTheory.TopStepPrimes

open GlobalTheory.TopStepPrimes in

/- English proof (translation)
Introduce `B X I h u a`. Take `⟨hX, hPr, -⟩` from `base_fields_primes_ok B X`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(GlobalTheory.Mem.LevTwist.levOk_twists B X I h).2.1.mono_right (I.Q_subset_SQ a)`. Introduce `P hP`.

Establish `h1` using `GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem`. Unfold `Sall at h1`. Simplify using `only [Finset.mem_union] at h1 hP ⊢`. Break down `hP with h0 | hP` into its components or cases. Conclude with `absurd h0 (Finset.notMem_empty _)`.

Introduce and unpack `(hc | hc)`. Conclude with `Finset.notMem_empty _ hc`. Conclude with `(h1 P (Or.inr hP)).1 (Or.inr hc)`. Introduce `P g hg`. Establish `e` using `redGL_eq_one_of_lqPrinc g hg`.

Use `⟨(mem_levQX _ _ _ _).2 (e ▸ Subgroup.one_mem _), ?_⟩` and prove the remaining obligations. Rewrite using `[levQX_lam]`. Establish `key : ∀ {G M : Type} [Group G] [Monoid M] (H : Subgroup G) (f : H →* M) (y : G) (hy : y ∈ H), y = 1 → f ⟨y, hy⟩ = 1`. Introduce and unpack `G M _ _ H f y hy rfl`. Conclude with `map_one f`.

Conclude with `key _ _ _ _ e`.
-/
theorem GlobalTheory.TopStepPrimes.primes_top_ok : ∀ {B : Base} {X : PreX B.toPre} {I : TC B X}, I.Ok → ∀ (u : B.Word) (a : I.ι), Disjoint (B.primes X).vGs (I.Q a) ∧ (∀ P ∈ uSG ∅ (uSG (B.primes X).vGs (I.Q a)), conjPrime₂ P ∉ uSG ∅ (uSG (B.primes X).vGs (I.Q a))) ∧ ∀ (P : I.Q a) (g : ↥(GLint B.fields.E (B.R.N B.R.m - 1) P.1)), lqPrinc P.1 1 (g : Sp B.fields.E (B.R.N B.R.m - 1) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N B.R.m - 1)) → ∃ h : g ∈ (levQX B.R I.sel (I.tup a) P).H, (levQX B.R I.sel (I.tup a) P).lam ⟨g, h⟩ = 1 := by
  intro B X I h u a
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  refine ⟨?_, ?_, ?_⟩
  · exact (GlobalTheory.Mem.LevTwist.levOk_twists B X I h).2.1.mono_right (I.Q_subset_SQ a)
  · intro P hP
    have h1 := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem
    unfold Sall at h1
    simp only [Finset.mem_union] at h1 hP ⊢
    rcases hP with h0 | hP
    · exact absurd h0 (Finset.notMem_empty _)
    · rintro (hc | hc)
      · exact Finset.notMem_empty _ hc
      · exact (h1 P (Or.inr hP)).1 (Or.inr hc)
  · intro P g hg
    have e := redGL_eq_one_of_lqPrinc g hg
    refine ⟨(mem_levQX _ _ _ _).2 (e ▸ Subgroup.one_mem _), ?_⟩
    rw [levQX_lam]
    have key : ∀ {G M : Type} [Group G] [Monoid M] (H : Subgroup G) (f : H →* M) (y : G) (hy : y ∈ H), y = 1 → f ⟨y, hy⟩ = 1 := by
      rintro G M _ _ H f y hy rfl
      exact map_one f
    exact key _ _ _ _ e
