import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.Statement
import Formalism.CoboundaryTransfers.Statement

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def IsWachBasis {r : ℕ} (b : Fin r → W.DD T) : Prop :=
  LinearIndependent (LetA O n) b ∧ Submodule.span (LetA O n) (Set.range b) = W.N T ∧
    LinearIndependent W.EE b ∧ Submodule.span W.EE (Set.range b) = ⊤

def IsLetterBasis (i : ZMod n) {r : ℕ} (b : Fin r → W.DD T) : Prop :=
  (∀ k, b k ∈ W.Nl T i) ∧
    ∀ x ∈ W.Nl T i, ∃! c : Fin r → PowerSeries O,
      x = ∑ k, (Pi.single i (c k) : LetA O n) • b k

def FrobBounds (M₀ h₀ : ℕ) : Prop :=
  (∀ x ∈ W.N T, W.Q ^ M₀ • W.φD T x ∈ W.N T) ∧ ∀ y ∈ W.N T, W.Q ^ h₀ • y ∈ W.φpull T

def FreeLetters : Prop :=
  (∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, IsWachBasis W T b) ∧
    (∀ i : ZMod n, ∃ b : Fin (Module.finrank O ↥T.L.T) → W.DD T, IsLetterBasis W T i b) ∧
    ∃ M₀ h₀ : ℕ, FrobBounds W T M₀ h₀

/- English proof (translation)
Take `⟨hli, hsp, -, -⟩` from `hb`. Establish `hmul : ∀ a : PowerSeries O, (Pi.single i a : LetA O n) * letE i = Pi.single i a`. Introduce `a`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using `[letE]`. Simplify using `[letE, h]`. Establish `hmul' : ∀ a : LetA O n, (letE i : LetA O n) * a = Pi.single i (a i)`. Introduce `a`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using `[letE]`. Simplify using `[letE, h]`.

Use `⟨fun k => ⟨b k, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hsp]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Introduce and unpack `x ⟨y, hy, rfl⟩`. Establish `hy' : y ∈ Submodule.span (LetA O n) (Set.range b)` using `by rw [hsp]; exact hy`.

Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hy'`. Establish `key : (letE i : LetA O n) • (∑ k, a k • b k) = ∑ k, (Pi.single i (a k i) : LetA O n) • b k`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [smul_smul, hmul']`. Use `⟨fun k => a k i, ?_, fun c hc => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(letE i : LetA O n) • (∑ k, a k • b k) = _`. Rewrite using `[key]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [smul_smul, hmul]`. Express the relevant statement in the definitionally equal form `(letE i : LetA O n) • (∑ k, a k • b k) = _ at hc`. Rewrite `hc` using `[key]`.

Simplify using `only [smul_smul, hmul] at hc`. Use function extensionality and compare the values at `k`. Establish `h0` using `Fintype.linearIndependent_iff.1 hli (fun k => (Pi.single i (c k) : LetA O n) - Pi.single i (a k i)) (by simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]) k`. Establish `h1` using `congrFun h0 i`. Simplify `h1` using `[sub_eq_zero]`.
-/
theorem IsWachBasis.letter {r : ℕ} {b : Fin r → W.DD T} (hb : IsWachBasis W T b) (i : ZMod n) :
    IsLetterBasis W T i (fun k => (letE i : LetA O n) • b k) := by
  obtain ⟨hli, hsp, -, -⟩ := hb
  have hmul : ∀ a : PowerSeries O,
      (Pi.single i a : LetA O n) * letE i = Pi.single i a := by
    intro a
    funext j
    by_cases h : j = i
    · subst h; simp [letE]
    · simp [letE, h]
  have hmul' : ∀ a : LetA O n, (letE i : LetA O n) * a = Pi.single i (a i) := by
    intro a
    funext j
    by_cases h : j = i
    · subst h; simp [letE]
    · simp [letE, h]
  refine ⟨fun k => ⟨b k, ?_, rfl⟩, ?_⟩
  · rw [← hsp]; exact Submodule.subset_span ⟨k, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ Submodule.span (LetA O n) (Set.range b) := by rw [hsp]; exact hy
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy'
    have key : (letE i : LetA O n) • (∑ k, a k • b k) =
        ∑ k, (Pi.single i (a k i) : LetA O n) • b k := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, hmul']
    refine ⟨fun k => a k i, ?_, fun c hc => ?_⟩
    · change (letE i : LetA O n) • (∑ k, a k • b k) = _
      rw [key]
      exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, hmul]
    · change (letE i : LetA O n) • (∑ k, a k • b k) = _ at hc
      rw [key] at hc
      simp only [smul_smul, hmul] at hc
      funext k
      have h0 := Fintype.linearIndependent_iff.1 hli
        (fun k => (Pi.single i (c k) : LetA O n) - Pi.single i (a k i))
        (by simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]) k
      have h1 := congrFun h0 i
      simpa [sub_eq_zero] using h1

/- English proof (translation)
Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨z, hz, rfl⟩ := hx`. Conclude with `hF.1 z hz`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `(W.N T).add_mem hx hy`. Consider the case `smul a x _ hx => rw [smul_comm]`. Conclude with `(W.N T).smul_mem a hx`.
-/
theorem FrobBounds.pull {M₀ h₀ : ℕ} (hF : FrobBounds W T M₀ h₀) :
    ∀ y ∈ W.φpull T, W.Q ^ M₀ • y ∈ W.N T := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx => obtain ⟨z, hz, rfl⟩ := hx; exact hF.1 z hz
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact (W.N T).add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact (W.N T).smul_mem a hx

end Generic

def WachLettersFree (l : ℕ) [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) : Prop :=
  ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys (P.PD K) T.ρ →
    FreeLetters (H.W K s LL h) T

end GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness
