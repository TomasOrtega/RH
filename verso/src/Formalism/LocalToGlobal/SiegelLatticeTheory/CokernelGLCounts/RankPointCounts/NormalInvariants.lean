import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepHeightOfNormOne
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBound

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.FourierDecayAlt
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut

namespace Formalism.L2.SG.NGCut.NormalInvariants

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PG {D : D7} (TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) : ℝ := ∏ w : InfinitePlace D.host.E, w (GPt TT γ)

def NmlInv : Prop :=
  ∀ Cg cb Cw cT CT C0 : ℝ, ∃ C'₀ Cl₀ : ℝ, ∀ C' Cl : ℝ, C'₀ ≤ C' → Cl₀ ≤ Cl →
    ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
      Ctx Cg cb Cw cT CT C0 C' Cl D large₂ X Y u u' →
      ∀ (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ)
        (c : Set (TauC Y u u')) (γ : PN.Pts D.host.E D.R.rS),
        (∃ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν) →
        1 ≤ NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ →
        ∃ (J J' : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (m m' : D.host.E)
          (κ : NuC D → D.host.E × D.host.E),
          J ≠ 0 ∧ J' ≠ 0 ∧ m ≠ 0 ∧ m' ≠ 0 ∧
          (∀ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν →
            (κ ν).1 ∈ J ∧ (κ ν).1 * star (κ ν).1 = m ∧ (κ ν).2 ∈ J' ∧ (κ ν).2 * star (κ ν).2 = m') ∧
          (∀ ν₁ ν₂, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν₁ →
            PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) c γ ν₂ → κ ν₁ = κ ν₂ → ν₁ = ν₂) ∧
          |((Algebra.norm ℚ m : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 *
            ((Tu D u : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2 ∧
          |((Algebra.norm ℚ m' : ℚ) : ℝ)| ≤ ((FractionalIdeal.absNorm J' : ℚ) : ℝ) ^ 2 *
            ((Tu D u' : ℕ) : ℝ) ^ (2 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 2

def NormCount : Prop :=
  ∀ (D : D7) (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) (m : D.host.E), J ≠ 0 → m ≠ 0 →
    ∀ S : Finset D.host.E, (∀ x ∈ S, x ∈ J ∧ x * star x = m) →
      (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 ≤ 8 * (D.R.f : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)|

/- English proof (translation)
Proceed by induction on `f with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases. Substitute `h` using the available equality.

Evaluate the numerical expressions. Establish `h1 : 1 ≤ n` using `h`. Rewrite using `[pow_succ 81 n]`. Use polynomial arithmetic with `[ih, h1]`.
-/
private theorem eight_mul_sq_le_eightyOne_pow (f : ℕ) : 8 * f ^ 2 ≤ 81 ^ f := by
  induction f with
  | zero => simp
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      norm_num
    · have h1 : 1 ≤ n := h
      rw [pow_succ 81 n]
      nlinarith [ih, h1]

/- English proof (translation)
Establish `h' : ((8 * f ^ 2 : ℕ) : ℝ) ≤ ((81 ^ f : ℕ) : ℝ)` using `by exact_mod_cast eight_mul_sq_le_eightyOne_pow f`. Move the coercions through the operations in `at h'`. Establish `e : (6561 : ℝ) ^ f = (81 : ℝ) ^ f * (81 : ℝ) ^ f`. Rewrite using `[← mul_pow]`. Evaluate the numerical expressions.

Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem nat_bound (f : ℕ) : (64 : ℝ) * (f : ℝ) ^ 4 ≤ 6561 ^ f := by
  have h' : ((8 * f ^ 2 : ℕ) : ℝ) ≤ ((81 ^ f : ℕ) : ℝ) := by exact_mod_cast eight_mul_sq_le_eightyOne_pow f
  push_cast at h'
  have e : (6561 : ℝ) ^ f = (81 : ℝ) ^ f * (81 : ℝ) ^ f := by
    rw [← mul_pow]
    norm_num
  rw [e]
  calc (64 : ℝ) * (f : ℝ) ^ 4 = (8 * (f : ℝ) ^ 2) * (8 * (f : ℝ) ^ 2) := by ring
    _ ≤ (81 : ℝ) ^ f * (81 : ℝ) ^ f := mul_le_mul h' h' (by positivity) (by positivity)

/- English proof (translation)
Unfold `Formalism.BasicNotions.Host.rdE`. Apply `Real.one_le_rpow` to reduce the goal to its premises. Establish `h` using `NumberField.discr_ne_zero D.host.E`. Establish `h' : (1 : ℤ) ≤ |discr D.host.E|` using `Int.one_le_abs h`. Conclude with `h'` after adjusting the coercions.

Check the signs of the components of the expression.
-/
theorem rd_one_le (D : D7) : 1 ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow
  · have h := NumberField.discr_ne_zero D.host.E
    have h' : (1 : ℤ) ≤ |discr D.host.E| := Int.one_le_abs h
    exact_mod_cast h'
  · positivity

/- English proof (translation)
Use `haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE`. Establish `hfin : Module.finrank ℚ D.host.E = 2 * D.R.f`. Rewrite using `[D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]`. Use `first`. Consider the case `ring`.

Consider the case `rfl`. Consider the case `omega`. Consider the case `(simp only [Formalism.BasicNotions.Ranks.ord]; ring)`. Establish `hcard : Fintype.card (InfinitePlace D.host.E) = D.R.f`. Establish `h1` using `NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E`.

Establish `h2` using `NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E`. Establish `h3` using `NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E`. Use linear arithmetic over natural numbers and integers. Unfold `NGPt PG`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, inv_pow]`.
-/
theorem ngPt_eq {D : D7} (TT : ℕ) (γ : PN.Pts D.host.E D.R.rS) :
    NGPt D.host.rdE TT γ = ((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹ * PG TT γ := by
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
    first
    | ring
    | rfl
    | omega
    | (simp only [Formalism.BasicNotions.Ranks.ord]; ring)
  have hcard : Fintype.card (InfinitePlace D.host.E) = D.R.f := by
    have h1 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces D.host.E
    have h2 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank D.host.E
    have h3 := NumberField.IsTotallyComplex.nrRealPlaces_eq_zero D.host.E
    omega
  unfold NGPt PG
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, inv_pow]

/- English proof (translation)
Establish `h0 : D.host.rdE ≠ 0` using `ne_of_gt (lt_of_lt_of_le one_pos (rd_one_le D))`. Rewrite using `[inv_pow, ← pow_mul, ← pow_mul]`. Rewrite using `[show 12 * D.R.rS * (D.R.rS + 1) * D.R.f = 2 * D.R.rS * (D.R.rS + 1) * (D.R.f * 6) by ring]`. Conclude with `mul_inv_cancel₀ (pow_ne_zero _ h0)`.
-/
theorem rd_cancel (D : D7) :
    D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
      (((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) ^ 6 = 1 := by
  have h0 : D.host.rdE ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos (rd_one_le D))
  rw [inv_pow, ← pow_mul, ← pow_mul]
  rw [show 12 * D.R.rS * (D.R.rS + 1) * D.R.f = 2 * D.R.rS * (D.R.rS + 1) * (D.R.f * 6) by ring]
  exact mul_inv_cancel₀ (pow_ne_zero _ h0)

/- English proof (translation)
Establish `hf` using `nat_bound f`. Establish `hT0 : (0 : ℝ) ≤ T` using `by linarith`. Establish `hT0' : (0 : ℝ) ≤ T'` using `by linarith`. Establish `hTT0 : (0 : ℝ) ≤ T * T'` using `mul_nonneg hT0 hT0'`. Establish `hTT : (9 : ℝ) ≤ T * T'` using `by nlinarith`.

Establish `h4 : (6561 : ℝ) ≤ (T * T') ^ 4`. Use `pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9) hTT 4` as an intermediate fact. Evaluate the numerical expressions using `at this`. Conclude with `this`. Establish `h9 : (6561 : ℝ) ^ f ≤ (T * T') ^ (4 * f)`.

Rewrite using `[pow_mul]`. Conclude with `pow_le_pow_left₀ (by norm_num) h4 f`. Establish `hP : P ^ 4 ≤ P ^ 6` using `pow_le_pow_right₀ hP1 (by norm_num)`. Establish `hB : (0 : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2)` using `mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hT0 _) (sq_nonneg _))`. Establish `hA : c1 * c2 ≤ (8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2)) * (8 * (f : ℝ) ^ 2 * (T' ^ (2 * f) * P ^ 2))` using `mul_le_mul hc1 hc2 h2 hB`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (T * T') ^ (4 * f) * ((T * T') ^ (2 * f) * P ^ 6) := mul_le_mul (hf.trans h9) (mul_le_mul_of_nonneg_left hP (pow_nonneg hTT0 _)) (mul_nonneg (pow_nonneg hTT0 _) (by positivity)) (pow_nonneg hTT0 _)`. Use `_ = (T * T') ^ (6 * f) * P ^ 6 := by ring`.
-/
theorem count_bound (f : ℕ) (T T' P c1 c2 : ℝ) (hT1 : 3 ≤ T) (hT2 : 3 ≤ T') (hP1 : 1 ≤ P)
    (hc1 : c1 ≤ 8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2)) (hc2 : c2 ≤ 8 * (f : ℝ) ^ 2 * (T' ^ (2 * f) * P ^ 2))
    (_h1 : 0 ≤ c1) (h2 : 0 ≤ c2) :
    c1 * c2 ≤ (T * T') ^ (6 * f) * P ^ 6 := by
  have hf := nat_bound f
  have hT0 : (0 : ℝ) ≤ T := by linarith
  have hT0' : (0 : ℝ) ≤ T' := by linarith
  have hTT0 : (0 : ℝ) ≤ T * T' := mul_nonneg hT0 hT0'
  have hTT : (9 : ℝ) ≤ T * T' := by nlinarith
  have h4 : (6561 : ℝ) ≤ (T * T') ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 9) hTT 4
    norm_num at this
    exact this
  have h9 : (6561 : ℝ) ^ f ≤ (T * T') ^ (4 * f) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (by norm_num) h4 f
  have hP : P ^ 4 ≤ P ^ 6 := pow_le_pow_right₀ hP1 (by norm_num)
  have hB : (0 : ℝ) ≤ 8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2) :=
    mul_nonneg (by positivity) (mul_nonneg (pow_nonneg hT0 _) (sq_nonneg _))
  have hA : c1 * c2 ≤ (8 * (f : ℝ) ^ 2 * (T ^ (2 * f) * P ^ 2)) * (8 * (f : ℝ) ^ 2 * (T' ^ (2 * f) * P ^ 2)) :=
    mul_le_mul hc1 hc2 h2 hB
  calc c1 * c2 ≤ _ := hA
    _ = (64 * (f : ℝ) ^ 4) * ((T * T') ^ (2 * f) * P ^ 4) := by
        rw [mul_pow]
        ring
    _ ≤ (T * T') ^ (4 * f) * ((T * T') ^ (2 * f) * P ^ 6) :=
        mul_le_mul (hf.trans h9) (mul_le_mul_of_nonneg_left hP (pow_nonneg hTT0 _))
          (mul_nonneg (pow_nonneg hTT0 _) (by positivity)) (pow_nonneg hTT0 _)
    _ = (T * T') ^ (6 * f) * P ^ 6 := by ring

/- English proof (translation)
Introduce `Cg cb Cw cT CT C0`. Take `⟨a₀, b₀, hA2⟩` from `hA Cg cb Cw cT CT C0`. Take `⟨o₀, p₀, hO2⟩` from `hO Cg cb Cw cT CT C0`. Use `⟨max a₀ o₀, max b₀ p₀, fun C' Cl h1 h2 D large₂ X Y u u' hc νL νB ng => ?_⟩` and prove the remaining obligations. Introduce `cl γ S hS`.

Establish `hrd` using `rd_one_le D`. Establish `hv : 2 * D.host.v = D.host.rdE` using `by unfold Host.v; ring`. Establish `hstand` using `hc.2.1`. Use `show (S.card : ℝ) ≤ ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) * (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f)) * NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6`. Establish `eR : (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) * (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f)) * ((((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ) ^ 6 = (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f) * …`.

Establish `hR` using `rd_cancel D`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = _ := by rw [hR, one_mul]`. Rewrite using `[hv, ngPt_eq, eR]`.

Establish `hT1 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ)` using `by exact_mod_cast hstand.2.2.2.1`. Establish `hT2 : (3 : ℝ) ≤ ((Tu D u' : ℕ) : ℝ)` using `by exact_mod_cast hstand.2.2.2.2.1`. Break down `S.eq_empty_or_nonempty with hSe | ⟨ν0, hν0⟩` into its components or cases. Rewrite using `[hSe]`. Simplify using `only [Finset.card_empty, Nat.cast_zero]`.

Use `mul_nonneg (pow_nonneg (by nlinarith) _) ?_` and prove the remaining obligations. Rewrite using `[show PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6 = (PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 3) ^ 2 by ring]`. Conclude with `sq_nonneg _`. Establish `hocc : ∃ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) cl γ ν` using `⟨ν0, hS ν0 hν0⟩`. Establish `hIsPt : PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ` using `⟨cl, ν0, hS ν0 hν0⟩`.

Establish `hNG0` using `(hO2 C' Cl (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2) D large₂ X Y u u' hc νL νB ng γ hIsPt).1`. Take `⟨J, J', m, m', κ, hJ, hJ', hm, hm', hmem, hinj, hN, hN'⟩` from `hA2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u u' hc νL νB ng cl γ hocc hNG0`. Establish `hNG` using `hNG0`. Rewrite `hNG` using `[ngPt_eq]`. Establish `hP1 : 1 ≤ PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ`.

Establish `hX : 1 ≤ (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f` using `one_le_pow₀ (one_le_pow₀ hrd)`. Establish `hpos : 0 < (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f` using `lt_of_lt_of_le one_pos hX`. Rewrite `hNG` using `[inv_mul_eq_div, le_div_iff₀ hpos, one_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Set `T1` to `S.image (fun ν => (κ ν).1)`.

Set `T2` to `S.image (fun ν => (κ ν).2)`. Establish `hcard : S.card ≤ T1.card * T2.card`. Combine the equalities or inequalities in the displayed calculation. Introduce `p hp`. Take `⟨ν, hν, rfl⟩` from `Finset.mem_image.1 hp`.

Conclude with `Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hν, Finset.mem_image_of_mem _ hν⟩)`. Use `_ = T1.card * T2.card := Finset.card_product _ _`. Establish `hB1` using `hB D J m hJ hm T1 (by`. Introduce `x hx`. Take `⟨ν, hν, rfl⟩` from `Finset.mem_image.1 hx`.

Conclude with `⟨(hmem ν (hS ν hν)).1, (hmem ν (hS ν hν)).2.1⟩)`. Establish `hB2` using `hB D J' m' hJ' hm' T2 (by`. Introduce `x hx`. Take `⟨ν, hν, rfl⟩` from `Finset.mem_image.1 hx`. Conclude with `⟨(hmem ν (hS ν hν)).2.2.1, (hmem ν (hS ν hν)).2.2.2⟩)`.

Establish `hJp : 0 < ((FractionalIdeal.absNorm J : ℚ) : ℝ)`. Establish `h0 : FractionalIdeal.absNorm J ≠ 0` using `by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]`. Use `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J) (Ne.symm h0)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hJp' : 0 < ((FractionalIdeal.absNorm J' : ℚ) : ℝ)`.

Establish `h0 : FractionalIdeal.absNorm J' ≠ 0` using `by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]`. Use `lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J') (Ne.symm h0)` as an intermediate fact. Conclude with `this` after adjusting the coercions. Generalize the expression as in `PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ = P at hN hN' hP1 ⊢`. Generalize the expression as in `((Tu D u : ℕ) : ℝ) = T at hN hT1 ⊢`.

Generalize the expression as in `((Tu D u' : ℕ) : ℝ) = T' at hN' hT2 ⊢`. Generalize the expression as in `((FractionalIdeal.absNorm J : ℚ) : ℝ) = nJ at hB1 hN hJp`. Generalize the expression as in `((FractionalIdeal.absNorm J' : ℚ) : ℝ) = nJ' at hB2 hN' hJp'`. Generalize the expression as in `|((Algebra.norm ℚ m : ℚ) : ℝ)| = nm at hB1 hN`. Generalize the expression as in `|((Algebra.norm ℚ m' : ℚ) : ℝ)| = nm' at hB2 hN'`.

Establish `hc1 : (T1.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)`. Establish `h` using `hB1.trans (mul_le_mul_of_nonneg_left hN (by positivity))`. Establish `h' : (T1.card : ℝ) * nJ ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ ^ 2`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right h' (by positivity)`.

Establish `hc2 : (T2.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T' ^ (2 * D.R.f) * P ^ 2)`. Establish `h` using `hB2.trans (mul_le_mul_of_nonneg_left hN' (by positivity))`. Establish `h' : (T2.card : ℝ) * nJ' ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T' ^ (2 * D.R.f) * P ^ 2)) * nJ' ^ 2`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right h' (by positivity)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem stepNormals_of (hA : NmlInv) (hB : NormCount) (hO : StepNormOne) : StepNormals := by
  intro Cg cb Cw cT CT C0
  obtain ⟨a₀, b₀, hA2⟩ := hA Cg cb Cw cT CT C0
  obtain ⟨o₀, p₀, hO2⟩ := hO Cg cb Cw cT CT C0
  refine ⟨max a₀ o₀, max b₀ p₀, fun C' Cl h1 h2 D large₂ X Y u u' hc νL νB ng => ?_⟩
  intro cl γ S hS
  have hrd := rd_one_le D
  have hv : 2 * D.host.v = D.host.rdE := by unfold Host.v; ring
  have hstand := hc.2.1
  show (S.card : ℝ) ≤ ((2 * D.host.v) ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
    (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f)) *
    NGPt D.host.rdE ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6
  have eR : (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
      (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f)) *
      ((((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ) ^ 6 =
      (((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6 := by
    have hR := rd_cancel D
    calc _ = (D.host.rdE ^ (12 * D.R.rS * (D.R.rS + 1) * D.R.f) *
          (((D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f)⁻¹) ^ 6) *
          ((((Tu D u : ℕ) : ℝ) * ((Tu D u' : ℕ) : ℝ)) ^ (6 * D.R.f) * PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6) := by
          ring
      _ = _ := by rw [hR, one_mul]
  rw [hv, ngPt_eq, eR]
  have hT1 : (3 : ℝ) ≤ ((Tu D u : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.1
  have hT2 : (3 : ℝ) ≤ ((Tu D u' : ℕ) : ℝ) := by exact_mod_cast hstand.2.2.2.2.1
  rcases S.eq_empty_or_nonempty with hSe | ⟨ν0, hν0⟩
  · rw [hSe]
    simp only [Finset.card_empty, Nat.cast_zero]
    refine mul_nonneg (pow_nonneg (by nlinarith) _) ?_
    rw [show PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 6 = (PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ ^ 3) ^ 2 by ring]
    exact sq_nonneg _
  have hocc : ∃ ν, PN.Occ (Y.tO u u') (NOf2 Y u u' νL νB ng) cl γ ν := ⟨ν0, hS ν0 hν0⟩
  have hIsPt : PN.IsPt (Y.tO u u') (NOf2 Y u u' νL νB ng) γ := ⟨cl, ν0, hS ν0 hν0⟩
  have hNG0 := (hO2 C' Cl (le_trans (le_max_right _ _) h1) (le_trans (le_max_right _ _) h2) D large₂ X Y u u' hc
    νL νB ng γ hIsPt).1
  obtain ⟨J, J', m, m', κ, hJ, hJ', hm, hm', hmem, hinj, hN, hN'⟩ :=
    hA2 C' Cl (le_trans (le_max_left _ _) h1) (le_trans (le_max_left _ _) h2) D large₂ X Y u u' hc νL νB ng cl γ hocc hNG0
  have hNG := hNG0
  rw [ngPt_eq] at hNG
  have hP1 : 1 ≤ PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ := by
    have hX : 1 ≤ (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := one_le_pow₀ (one_le_pow₀ hrd)
    have hpos : 0 < (D.host.rdE ^ (2 * D.R.rS * (D.R.rS + 1))) ^ D.R.f := lt_of_lt_of_le one_pos hX
    rw [inv_mul_eq_div, le_div_iff₀ hpos, one_mul] at hNG
    linarith

  let T1 := S.image (fun ν => (κ ν).1)
  let T2 := S.image (fun ν => (κ ν).2)
  have hcard : S.card ≤ T1.card * T2.card := by
    calc S.card = (S.image κ).card :=
          (Finset.card_image_of_injOn fun a ha b hb h => hinj a b (hS a ha) (hS b hb) h).symm
      _ ≤ (T1 ×ˢ T2).card := Finset.card_le_card (by
          intro p hp
          obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hp
          exact Finset.mem_product.2 ⟨Finset.mem_image_of_mem _ hν, Finset.mem_image_of_mem _ hν⟩)
      _ = T1.card * T2.card := Finset.card_product _ _
  have hB1 := hB D J m hJ hm T1 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).1, (hmem ν (hS ν hν)).2.1⟩)
  have hB2 := hB D J' m' hJ' hm' T2 (by
    intro x hx
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨(hmem ν (hS ν hν)).2.2.1, (hmem ν (hS ν hν)).2.2.2⟩)
  have hJp : 0 < ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J) (Ne.symm h0)
    exact_mod_cast this
  have hJp' : 0 < ((FractionalIdeal.absNorm J' : ℚ) : ℝ) := by
    have h0 : FractionalIdeal.absNorm J' ≠ 0 := by rwa [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    have := lt_of_le_of_ne (FractionalIdeal.absNorm_nonneg J') (Ne.symm h0)
    exact_mod_cast this
  generalize PG ((Tu D u : ℕ) * (Tu D u' : ℕ)) γ = P at hN hN' hP1 ⊢
  generalize ((Tu D u : ℕ) : ℝ) = T at hN hT1 ⊢
  generalize ((Tu D u' : ℕ) : ℝ) = T' at hN' hT2 ⊢
  generalize ((FractionalIdeal.absNorm J : ℚ) : ℝ) = nJ at hB1 hN hJp
  generalize ((FractionalIdeal.absNorm J' : ℚ) : ℝ) = nJ' at hB2 hN' hJp'
  generalize |((Algebra.norm ℚ m : ℚ) : ℝ)| = nm at hB1 hN
  generalize |((Algebra.norm ℚ m' : ℚ) : ℝ)| = nm' at hB2 hN'
  have hc1 : (T1.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB1.trans (mul_le_mul_of_nonneg_left hN (by positivity))
    have h' : (T1.card : ℝ) * nJ ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T ^ (2 * D.R.f) * P ^ 2)) * nJ ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  have hc2 : (T2.card : ℝ) ≤ 8 * (D.R.f : ℝ) ^ 2 * (T' ^ (2 * D.R.f) * P ^ 2) := by
    have h := hB2.trans (mul_le_mul_of_nonneg_left hN' (by positivity))
    have h' : (T2.card : ℝ) * nJ' ^ 2 ≤ (8 * (D.R.f : ℝ) ^ 2 * (T' ^ (2 * D.R.f) * P ^ 2)) * nJ' ^ 2 := by
      calc _ ≤ _ := h
        _ = _ := by ring
    exact le_of_mul_le_mul_right h' (by positivity)
  calc (S.card : ℝ) ≤ (T1.card : ℝ) * T2.card := by exact_mod_cast hcard
    _ ≤ _ := count_bound D.R.f T T' P _ _ hT1 hT2 hP1 hc1 hc2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)

def NormCountG : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (m : E), J ≠ 0 → m ≠ 0 →
    ∀ S : Finset E, (∀ x ∈ S, x ∈ J ∧ x * NumberField.IsCMField.complexConj E x = m) →
      (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2 ≤
        2 * (Module.finrank ℚ E : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)|

/- English proof (translation)
Introduce `D J m hJ hm S hS`. Use `haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE`. Establish `hfin : Module.finrank ℚ D.host.E = 2 * D.R.f`. Rewrite using `[D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]`. Use `first`.

Consider the case `ring`. Consider the case `rfl`. Consider the case `omega`. Consider the case `(simp only [Formalism.BasicNotions.Ranks.ord]; ring)`. Establish `h1` using `h D.host.E J m hJ hm S (fun x hx => ⟨(hS x hx).1, (hS x hx).2⟩)`.

Establish `hf : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ)` using `by rw [hfin]; push_cast; ring`. Rewrite `h1` using `[hf]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem normCount_of (h : NormCountG) : NormCount := by
  intro D J m hJ hm S hS
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  have hfin : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
    first
    | ring
    | rfl
    | omega
    | (simp only [Formalism.BasicNotions.Ranks.ord]; ring)
  have h1 := h D.host.E J m hJ hm S (fun x hx => ⟨(hS x hx).1, (hS x hx).2⟩)
  have hf : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by rw [hfin]; push_cast; ring
  rw [hf] at h1
  calc (S.card : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ 2
      ≤ 2 * (2 * (D.R.f : ℝ)) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| := h1
    _ = 8 * (D.R.f : ℝ) ^ 2 * |((Algebra.norm ℚ m : ℚ) : ℝ)| := by ring

end Formalism.L2.SG.NGCut.NormalInvariants
