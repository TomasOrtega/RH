import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicValuationThetaKernelJetBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridNumericalDataRealPlaceGapSizeBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParameterSizeConditionsNumericBounds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section
open GlobalTheory.SignedHC

/- English proof (translation)
The claim follows from `|(x : ℝ) - (c : ℝ)| ≤ (len : ℝ) / 2 := by obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 h have : (a' : ℝ) + 1 ≤ len := by exact_mod_cast (Finset.mem_range.1 ha') have h0 : (0 : ℝ) ≤ a' := Nat.cast_nonneg a' push_cast rw [abs_le]; constructor <;> linarith`.
-/
private theorem parBd_block {c x : ℚ} {len : ℕ} (h : x ∈ TPar.block c len) :
    |(x : ℝ) - (c : ℝ)| ≤ (len : ℝ) / 2 := by
  obtain ⟨a', ha', rfl⟩ := Finset.mem_image.1 h
  have : (a' : ℝ) + 1 ≤ len := by exact_mod_cast (Finset.mem_range.1 ha')
  have h0 : (0 : ℝ) ≤ a' := Nat.cast_nonneg a'
  push_cast
  rw [abs_le]; constructor <;> linarith

/- English proof (translation)
Establish `hal : ∀ l, l ≤ G.m → (0 : ℝ) ≤ ((G.a l : ℚ) : ℝ) ∧ ((G.a l : ℚ) : ℝ) ≤ B`. Introduce `l hl`. Establish `h2` using `(hv 2 le_rfl G.two_le_k).1`. Establish `hl' : (l : ℝ) ≤ G.m` using `by exact_mod_cast hl`. Establish `hl0 : (0 : ℝ) ≤ l` using `by positivity`.

Establish `hg : (0 : ℝ) ≤ G.ga` using `by positivity`. Establish `h1 : (0 : ℝ) ≤ (l : ℝ) * G.ga` using `mul_nonneg hl0 hg`. Establish `h3 : (0 : ℝ) ≤ ((G.m : ℝ) + 1 - l) * G.ga` using `mul_nonneg (by linarith) hg`. Unfold `GlobalTheory.SignedHC.GridData.a at ha ⊢`. Move the coercions through the operations in `at ha ⊢`.

Apply the tactic sequence `constructor <;> nlinarith`. Establish `hcen : ∀ l, 1 ≤ l → l ≤ G.m → |(((G.cen l : ℤ) : ℚ) : ℝ)| ≤ B + 1`. Introduce `l h1 h2`. Establish `e` using `hN l (Finset.mem_Icc.2 ⟨h1, h2⟩)`. Establish `e' : |(((G.cen l : ℤ) : ℚ) : ℝ) - (((G.a (l - 1) : ℚ) : ℝ) + ((G.a l : ℚ) : ℝ)) / 2| ≤ 1`.

Unfold `GlobalTheory.SignedHC.GridData.mid at e`. Conclude with `e` after adjusting the coercions. Establish `a1` using `hal l h2`. Establish `a2` using `hal (l - 1) (by omega)`. Rewrite `e'`, the goal using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith [e'.1, e'.2, a1.1, a1.2, a2.1, a2.2]`. Establish `hC : ∀ l len, 1 ≤ l → l ≤ G.m → len ≤ G.s → ∀ x ∈ TPar.block (G.cen l : ℚ) len, |(x : ℝ)| ≤ 5 * B`. Introduce `l len h1 h2 h3 x hx`. Establish `e` using `abs_le.1 (parBd_block hx)`. Establish `e'` using `abs_le.1 (hcen l h1 h2)`.

Establish `: (len : ℝ) ≤ G.s` using `by exact_mod_cast h3`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith [e.1, e.2, e'.1, e'.2]`. Establish `hM : ∀ l len, 1 ≤ l → l ≤ G.m → len ≤ G.t + 1 → ∀ x ∈ TPar.block (-(G.e l : ℚ)) len, |(x : ℝ)| ≤ 5 * B`. Introduce `l len h1 h2 h3 x hx`. Establish `e` using `abs_le.1 (parBd_block hx)`.

Take `⟨b1, b2, b3⟩` from `hb l h1 h2`. Establish `: (len : ℝ) ≤ G.t + 1` using `by exact_mod_cast h3`. Move the coercions through the operations in `at e`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith [e.1, e.2]`. Prove the components needed by the constructor for the conclusion.

Introduce `i x hx`. Take `⟨sg, hx⟩` from `mem_entries.1 hx`. Break down `GlobalTheory.SignedHC.GridData.mem_parD.1 hx with ⟨hc, -⟩ | ⟨l, h1, h2, he⟩ | ⟨l, h1, h2, hc, -⟩ | ⟨l, h1, h2, hc, -⟩` into its components or cases. Take `⟨i', h2, hk, e⟩` from `GlobalTheory.SignedHC.GridData.mem_cloud.1 hc`. Simplify using `only at e`.

Take `⟨v1, v2⟩` from `hv i' h2 hk`. Rewrite using `[e]`. Use `push_cast`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Establish `e : x = -(G.b l : ℚ)` using `congrArg Prod.fst he`.

Take `⟨b1, b2, b3⟩` from `hb l h1 h2`. Rewrite using `[e]`. Use `push_cast`. Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Conclude with `hM l G.t h1 (by omega) (by omega) x hc`.

Conclude with `hC l G.s (by omega) h2 le_rfl x hc`. Introduce `x hx`. Break down `GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨l, h1, h2, hc⟩ | ⟨l, h1, h2, hc⟩` into its components or cases. Take `⟨i, hi, rfl⟩` from `GlobalTheory.SignedHC.GridData.mem_tops.1 h`. Take `⟨a1, a2⟩` from `hal i hi`.

Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Take `⟨i, h2, hk, rfl⟩` from `GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h`. Take `⟨v1, v2⟩` from `hv i h2 hk`. Unfold `GlobalTheory.SignedHC.GridData.vHalf`. Use `push_cast`.

Apply the tactic sequence `rw [abs_le]; constructor <;> linarith`. Conclude with `hC l (G.s - 1) h1 h2 (by omega) x hc`. Conclude with `hM l (G.t + 1) h1 (by omega) le_rfl x hc`.
-/
private theorem parBd_generic (G : GlobalTheory.SignedHC.GridData) (B : ℝ) (hB : 12 ≤ B) (hN : G.NearMid)
    (hv : ∀ i, 2 ≤ i → i ≤ G.k → (0 : ℝ) ≤ G.v i ∧ (G.v i : ℝ) ≤ B) (ha : ((G.a 0 : ℚ) : ℝ) ≤ B)
    (hb : ∀ l, 1 ≤ l → l ≤ G.m → (0 : ℝ) ≤ G.b l ∧ (G.b l : ℝ) ≤ G.e l ∧ (G.e l : ℝ) ≤ 4 * B)
    (ht : (G.t : ℝ) ≤ B) (hs : (G.s : ℝ) ≤ B) {j : ℕ} (hj : j ≤ G.m) :
    (∀ i, ∀ x ∈ entries (G.parD i j), |(x : ℝ)| ≤ 5 * B) ∧ ∀ x ∈ G.weightX j, |(x : ℝ)| ≤ 5 * B := by
  have hal : ∀ l, l ≤ G.m → (0 : ℝ) ≤ ((G.a l : ℚ) : ℝ) ∧ ((G.a l : ℚ) : ℝ) ≤ B := by
    intro l hl
    have h2 := (hv 2 le_rfl G.two_le_k).1
    have hl' : (l : ℝ) ≤ G.m := by exact_mod_cast hl
    have hl0 : (0 : ℝ) ≤ l := by positivity
    have hg : (0 : ℝ) ≤ G.ga := by positivity
    have h1 : (0 : ℝ) ≤ (l : ℝ) * G.ga := mul_nonneg hl0 hg
    have h3 : (0 : ℝ) ≤ ((G.m : ℝ) + 1 - l) * G.ga := mul_nonneg (by linarith) hg
    unfold GlobalTheory.SignedHC.GridData.a at ha ⊢
    push_cast at ha ⊢
    constructor <;> nlinarith
  have hcen : ∀ l, 1 ≤ l → l ≤ G.m → |(((G.cen l : ℤ) : ℚ) : ℝ)| ≤ B + 1 := by
    intro l h1 h2
    have e := hN l (Finset.mem_Icc.2 ⟨h1, h2⟩)
    have e' : |(((G.cen l : ℤ) : ℚ) : ℝ) - (((G.a (l - 1) : ℚ) : ℝ) + ((G.a l : ℚ) : ℝ)) / 2| ≤ 1 := by
      unfold GlobalTheory.SignedHC.GridData.mid at e
      exact_mod_cast e
    have a1 := hal l h2
    have a2 := hal (l - 1) (by omega)
    rw [abs_le] at e' ⊢
    constructor <;> linarith [e'.1, e'.2, a1.1, a1.2, a2.1, a2.2]
  have hC : ∀ l len, 1 ≤ l → l ≤ G.m → len ≤ G.s → ∀ x ∈ TPar.block (G.cen l : ℚ) len, |(x : ℝ)| ≤ 5 * B := by
    intro l len h1 h2 h3 x hx
    have e := abs_le.1 (parBd_block hx)
    have e' := abs_le.1 (hcen l h1 h2)
    have : (len : ℝ) ≤ G.s := by exact_mod_cast h3
    rw [abs_le]; constructor <;> linarith [e.1, e.2, e'.1, e'.2]
  have hM : ∀ l len, 1 ≤ l → l ≤ G.m → len ≤ G.t + 1 → ∀ x ∈ TPar.block (-(G.e l : ℚ)) len, |(x : ℝ)| ≤ 5 * B := by
    intro l len h1 h2 h3 x hx
    have e := abs_le.1 (parBd_block hx)
    obtain ⟨b1, b2, b3⟩ := hb l h1 h2
    have : (len : ℝ) ≤ G.t + 1 := by exact_mod_cast h3
    push_cast at e
    rw [abs_le]; constructor <;> linarith [e.1, e.2]
  constructor
  · intro i x hx
    obtain ⟨sg, hx⟩ := mem_entries.1 hx
    rcases GlobalTheory.SignedHC.GridData.mem_parD.1 hx with ⟨hc, -⟩ | ⟨l, h1, h2, he⟩ | ⟨l, h1, h2, hc, -⟩ | ⟨l, h1, h2, hc, -⟩
    · obtain ⟨i', h2, hk, e⟩ := GlobalTheory.SignedHC.GridData.mem_cloud.1 hc
      simp only at e
      obtain ⟨v1, v2⟩ := hv i' h2 hk
      rw [e]; push_cast
      rw [abs_le]; constructor <;> linarith
    · have e : x = -(G.b l : ℚ) := congrArg Prod.fst he
      obtain ⟨b1, b2, b3⟩ := hb l h1 h2
      rw [e]; push_cast
      rw [abs_le]; constructor <;> linarith
    · exact hM l G.t h1 (by omega) (by omega) x hc
    · exact hC l G.s (by omega) h2 le_rfl x hc
  · intro x hx
    rcases GlobalTheory.SignedHC.GridData.mem_weightX.1 hx with h | h | ⟨l, h1, h2, hc⟩ | ⟨l, h1, h2, hc⟩
    · obtain ⟨i, hi, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_tops.1 h
      obtain ⟨a1, a2⟩ := hal i hi
      rw [abs_le]; constructor <;> linarith
    · obtain ⟨i, h2, hk, rfl⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 h
      obtain ⟨v1, v2⟩ := hv i h2 hk
      unfold GlobalTheory.SignedHC.GridData.vHalf
      push_cast
      rw [abs_le]; constructor <;> linarith
    · exact hC l (G.s - 1) h1 h2 (by omega) x hc
    · exact hM l (G.t + 1) h1 (by omega) le_rfl x hc

end

/- English proof (translation)
Introduce `D large₂ hS hH X hX τ`. Take `⟨hN, -, -, -, hm2, -, -, h12⟩` from `GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, hSb, hpos, -⟩` from `hS`. Use `set G := GlobalTheory.ChiGrid.num D 1 τ with hG`. Establish `hk : G.k = D.R.k` using `rfl`.

Establish `hm : G.m = D.R.m` using `rfl`. Establish `hga : G.ga = GlobalTheory.ChiGrid.gap D 1` using `rfl`. Take `⟨hv0, hb0, he0⟩` from `GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (GlobalTheory.ChiGrid.sLen D) (GlobalTheory.ChiGrid.gap D 1) (GlobalTheory.ChiGrid.cen D 1 τ)`. Establish `hv : ∀ i : Fin (D.R.k - 1), (((D.hc τ).v i : ℚ) : ℝ) = ((G.v (i.1 + 2) : ℤ) : ℝ)`. Introduce `i`.

Establish `e : (D.hc τ).v i = ((G.v (i.1 + 2) : ℤ) : ℚ)` using `hv0 i`. Rewrite using `[e, Rat.cast_intCast]`. Establish `hb : ∀ l : Fin D.R.m, (((D.hc τ).b l : ℚ) : ℝ) = ((G.b (l.1 + 1) : ℤ) : ℝ)`. Introduce `l`. Establish `e : (D.hc τ).b l = ((G.b (l.1 + 1) : ℤ) : ℚ)` using `hb0 l`.

Rewrite using `[e, Rat.cast_intCast]`. Establish `he : ∀ l : Fin D.R.m, (((D.hc τ).e l : ℚ) : ℝ) = ((G.e (l.1 + 1) : ℤ) : ℝ)`. Introduce `l`. Establish `e : (D.hc τ).e l = ((G.e (l.1 + 1) : ℤ) : ℚ)` using `he0 l`. Rewrite using `[e, Rat.cast_intCast]`.

Establish `hprod : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ)` using `by positivity`. Establish `hvv : ∀ i, 2 ≤ i → i ≤ G.k → (0 : ℝ) ≤ G.v i ∧ (G.v i : ℝ) ≤ large₂.Sc`. Introduce `i h2 hi`. Take `⟨a, rfl⟩` from `Nat.exists_eq_add_of_le' h2`. Establish `h` using `large₂.cloud_v τ ⟨a, by omega⟩`.

Rewrite `h` using `[hv]`. Conclude with `h`. Establish `hts : D.R.t + sLen D + 1 ≤ bigN D`. Unfold `bigN`. Establish `: 1 * (D.R.t + sLen D + 1) ≤ D.R.m * (D.R.t + sLen D + 1)` using `Nat.mul_le_mul_right _ (by omega)`.

Use linear arithmetic over natural numbers and integers. Establish `hgen : ∀ j, j ≤ G.m → (∀ i, ∀ x ∈ GlobalTheory.SignedHC.entries (G.parD i j), |(x : ℝ)| ≤ 5 * large₂.sc.b) ∧ ∀ x ∈ G.weightX j, |(x : ℝ)| ≤ 5 * large₂.sc.b`. Introduce `j hj`. Use `parBd_generic G large₂.sc.b h12 (GlobalTheory.ChiGrid.num_nearMid D 1 τ) ?_ ?_ ?_ ?_ ?_ hj` and prove the remaining obligations. Introduce `i h2 hi`.

Take `⟨a, b⟩` from `hvv i h2 hi`. Conclude with `⟨a, by linarith⟩`. Establish `h` using `(hvv 2 le_rfl G.two_le_k).2`. Establish `e : (((G.a 0 : ℚ)) : ℝ) = ((G.v 2 : ℤ) : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ)`. Unfold `GlobalTheory.SignedHC.GridData.a`.

Rewrite using `[hm, hga]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `l h1 hl`. Take `⟨a, rfl⟩` from `Nat.exists_eq_add_of_le' h1`. Take `⟨p1, p2⟩` from `hpos τ ⟨a, by omega⟩`. Establish `g` using `(hH.gap τ ⟨a, by omega⟩).1`. Establish `ht0 : (0 : ℚ) ≤ D.R.t` using `by positivity`.

Establish `g' : (D.hc τ).b ⟨a, by omega⟩ ≤ (D.hc τ).e ⟨a, by omega⟩` using `by linarith`. Establish `g'' : (((D.hc τ).b ⟨a, by omega⟩ : ℚ) : ℝ) ≤ (((D.hc τ).e ⟨a, by omega⟩ : ℚ) : ℝ)` using `by exact_mod_cast g'`. Establish `p1' : (0 : ℝ) ≤ (((D.hc τ).b ⟨a, by omega⟩ : ℚ) : ℝ)` using `by exact_mod_cast p1.le`. Rewrite `p1'`, `g''` using `[hb]`. Rewrite `p2`, `g''` using `[he]`.

Conclude with `⟨p1', g'', p2⟩`. Establish `: (D.R.t : ℝ) ≤ bigN D` using `by exact_mod_cast (by omega : D.R.t ≤ bigN D)`. Conclude with `this.trans hN`. Establish `: (sLen D : ℝ) ≤ bigN D` using `by exact_mod_cast (by omega : sLen D ≤ bigN D)`. Conclude with `this.trans hN`.

Introduce `x hx`. Consider the cases of `X with`. Consider the case `core i => exact hX.elim`. Consider the case `top j`. Take `⟨sg, hx⟩` from `GlobalTheory.SignedHC.mem_entries.1 hx`.

Establish `h` using `(hgen j hX).2 x (GlobalTheory.SignedHC.mem_plus.1 hx).1`. Combine the linear equalities and inequalities to obtain the conclusion. Consider the case `grid i j`. Take `⟨sg, hx⟩` from `GlobalTheory.SignedHC.mem_entries.1 hx`. Establish `hj : j ≤ G.m` using `le_of_eq hX.2`.

Establish `hx'` using `GlobalTheory.SignedHC.mem_shift.1 hx`. Establish `h` using `(hgen j hj).1 i _ (GlobalTheory.SignedHC.fst_mem_entries hx')`. Simplify using `only at h`. Rewrite `h`, the goal using `[abs_le]`. Apply the tactic sequence `split_ifs at h <;> push_cast at h <;> constructor <;> linarith [h.1, h.2]`.
-/
theorem UpperTheory.WildA.parBd :
    ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → ∀ X : Node, DefNode D.R.m X → ∀ (τ : D.what₂.Tau),
      ∀ x ∈ GlobalTheory.SignedHC.entries (Node.par D 1 X τ), |(x : ℝ)| ≤ 6 * large₂.sc.b := by
  intro D large₂ hS hH X hX τ
  obtain ⟨hN, -, -, -, hm2, -, -, h12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hS
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hSb, hpos, -⟩ := hS
  set G := GlobalTheory.ChiGrid.num D 1 τ with hG
  have hk : G.k = D.R.k := rfl
  have hm : G.m = D.R.m := rfl
  have hga : G.ga = GlobalTheory.ChiGrid.gap D 1 := rfl
  obtain ⟨hv0, hb0, he0⟩ := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (GlobalTheory.ChiGrid.sLen D) (GlobalTheory.ChiGrid.gap D 1)
    (GlobalTheory.ChiGrid.cen D 1 τ)
  have hv : ∀ i : Fin (D.R.k - 1), (((D.hc τ).v i : ℚ) : ℝ) = ((G.v (i.1 + 2) : ℤ) : ℝ) := by
    intro i
    have e : (D.hc τ).v i = ((G.v (i.1 + 2) : ℤ) : ℚ) := hv0 i
    rw [e, Rat.cast_intCast]
  have hb : ∀ l : Fin D.R.m, (((D.hc τ).b l : ℚ) : ℝ) = ((G.b (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).b l = ((G.b (l.1 + 1) : ℤ) : ℚ) := hb0 l
    rw [e, Rat.cast_intCast]
  have he : ∀ l : Fin D.R.m, (((D.hc τ).e l : ℚ) : ℝ) = ((G.e (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).e l = ((G.e (l.1 + 1) : ℤ) : ℚ) := he0 l
    rw [e, Rat.cast_intCast]
  have hprod : (0 : ℝ) ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by positivity
  have hvv : ∀ i, 2 ≤ i → i ≤ G.k → (0 : ℝ) ≤ G.v i ∧ (G.v i : ℝ) ≤ large₂.Sc := by
    intro i h2 hi
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' h2
    have h := large₂.cloud_v τ ⟨a, by omega⟩
    rw [hv] at h
    exact h
  have hts : D.R.t + sLen D + 1 ≤ bigN D := by
    unfold bigN
    have : 1 * (D.R.t + sLen D + 1) ≤ D.R.m * (D.R.t + sLen D + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hgen : ∀ j, j ≤ G.m → (∀ i, ∀ x ∈ GlobalTheory.SignedHC.entries (G.parD i j), |(x : ℝ)| ≤ 5 * large₂.sc.b) ∧
      ∀ x ∈ G.weightX j, |(x : ℝ)| ≤ 5 * large₂.sc.b := by
    intro j hj
    refine parBd_generic G large₂.sc.b h12 (GlobalTheory.ChiGrid.num_nearMid D 1 τ) ?_ ?_ ?_ ?_ ?_ hj
    · intro i h2 hi
      obtain ⟨a, b⟩ := hvv i h2 hi
      exact ⟨a, by linarith⟩
    · have h := (hvv 2 le_rfl G.two_le_k).2
      have e : (((G.a 0 : ℚ)) : ℝ) = ((G.v 2 : ℤ) : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by
        unfold GlobalTheory.SignedHC.GridData.a; rw [hm, hga]; push_cast; ring
      rw [e]; linarith
    · intro l h1 hl
      obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' h1
      obtain ⟨p1, p2⟩ := hpos τ ⟨a, by omega⟩
      have g := (hH.gap τ ⟨a, by omega⟩).1
      have ht0 : (0 : ℚ) ≤ D.R.t := by positivity
      have g' : (D.hc τ).b ⟨a, by omega⟩ ≤ (D.hc τ).e ⟨a, by omega⟩ := by linarith
      have g'' : (((D.hc τ).b ⟨a, by omega⟩ : ℚ) : ℝ) ≤ (((D.hc τ).e ⟨a, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast g'
      have p1' : (0 : ℝ) ≤ (((D.hc τ).b ⟨a, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast p1.le
      rw [hb] at p1' g''
      rw [he] at p2 g''
      exact ⟨p1', g'', p2⟩
    · have : (D.R.t : ℝ) ≤ bigN D := by exact_mod_cast (by omega : D.R.t ≤ bigN D)
      exact this.trans hN
    · have : (sLen D : ℝ) ≤ bigN D := by exact_mod_cast (by omega : sLen D ≤ bigN D)
      exact this.trans hN
  intro x hx
  cases X with
  | core i => exact hX.elim
  | top j =>
    obtain ⟨sg, hx⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have h := (hgen j hX).2 x (GlobalTheory.SignedHC.mem_plus.1 hx).1
    linarith
  | grid i j =>
    obtain ⟨sg, hx⟩ := GlobalTheory.SignedHC.mem_entries.1 hx
    have hj : j ≤ G.m := le_of_eq hX.2
    have hx' := GlobalTheory.SignedHC.mem_shift.1 hx
    have h := (hgen j hj).1 i _ (GlobalTheory.SignedHC.fst_mem_entries hx')
    simp only at h
    rw [abs_le] at h ⊢
    split_ifs at h <;> push_cast at h <;> constructor <;> linarith [h.1, h.2]
