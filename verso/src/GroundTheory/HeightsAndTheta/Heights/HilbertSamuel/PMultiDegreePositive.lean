import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMultiDegreePositive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegrePrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreHilb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSegreDimGe
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDegreePositive
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace MultiDegreePositive

/- English proof (translation)
Rewrite using `[Filter.tendsto_atTop_atTop]`. Introduce `b`. Use `⟨∑ k, |b k|, fun a ha k => ?_⟩` and prove the remaining obligations. Conclude with `(le_abs_self _).trans ((Finset.single_le_sum (fun k _ => abs_nonneg (b k)) (Finset.mem_univ k)).trans ha)`.
-/
theorem tendsto_diag (K : Type) [Fintype K] :
    Filter.Tendsto (fun n : ℤ => fun _ : K => n) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨∑ k, |b k|, fun a ha k => ?_⟩
  exact (le_abs_self _).trans
    ((Finset.single_le_sum (fun k _ => abs_nonneg (b k)) (Finset.mem_univ k)).trans ha)

/- English proof (translation)
Simplify using `only [mixedDiff, List.ofFn_succ, List.foldr_cons]`.
-/
theorem mixedDiff_succ {L : Type} [DecidableEq L] (b : L → ℤ) (H : (L → ℤ) → ℤ) (r : ℕ) :
    mixedDiff (fun _ : Fin (r + 1) => b) H = diffStep b (mixedDiff (fun _ : Fin r => b) H) := by
  simp only [mixedDiff, List.ofFn_succ, List.foldr_cons]

/- English proof (translation)
Proceed by induction on `r generalizing n with`. Consider the case `zero => simpa [mixedDiff] using hg n`. Consider the case `succ r ih`. Rewrite using `[mixedDiff_succ, mixedDiff_succ]`. Establish `e1 : ∀ (L : Type), ((fun _ : L => n) - fun _ : L => (1 : ℤ)) = fun _ => n - 1` using `fun L => funext fun _ => rfl`.

Simplify using `only [diffStep, e1, ih]`.
-/
theorem mixedDiff_diag {K : Type} [DecidableEq K] (h : (K → ℤ) → ℤ) (g : (Unit → ℤ) → ℤ)
    (hg : ∀ n : ℤ, g (fun _ => n) = h (fun _ => n)) (r : ℕ) (n : ℤ) :
    mixedDiff (fun _ : Fin r => fun _ : Unit => (1 : ℤ)) g (fun _ => n) =
      mixedDiff (fun _ : Fin r => fun _ : K => (1 : ℤ)) h (fun _ => n) := by
  induction r generalizing n with
  | zero => simpa [mixedDiff] using hg n
  | succ r ih =>
    rw [mixedDiff_succ, mixedDiff_succ]
    have e1 : ∀ (L : Type), ((fun _ : L => n) - fun _ : L => (1 : ℤ)) = fun _ => n - 1 :=
      fun L => funext fun _ => rfl
    simp only [diffStep, e1, ih]

/- English proof (translation)
Establish `hle` using `(ringKrullDim_quotient_le q).trans_eq (MvPolynomial.ringKrullDim_of_isNoetherianRing (R := F) (ι := Σ k, ι k))`. Rewrite `hle` using `[hd, ringKrullDim_eq_zero_of_field, zero_add, Nat.card_of_isEmpty, Fintype.card_eq_zero, add_zero]`. Establish `he : e = 0` using `by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hle) : (e : ℕ∞) = 0)`. Substitute `he` using the available equality. Establish `hrel : FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ))`.

Rewrite using `[FieldNumbers.relDim_of_ringKrullDim_eq q (0 + Fintype.card K) hd]`. Simplify using `only [Nat.cast_add, add_sub_cancel_right]`. Both sides reduce to the same expression. Take `⟨hA, -⟩` from `FieldNumbers.MixedDiffConst.full F K ι q hq.multiHomog hq.relevant 0 hrel`. Take `⟨m, hm⟩` from `(hA (fun _ : Fin 0 => fun _ : K => (1 : ℤ))).exists`.

Rewrite using `[← hm]`. Establish `hm0 : mixedDiff (fun _ : Fin 0 => fun _ : K => (1 : ℤ)) (hilbFn q) m = hilbFn q m` using `rfl`. Rewrite using `[hm0]`. Take `⟨hfin, hval⟩` from `FieldNumbers.GradedFinite.full F K ι q (fun _ => 0)`. Establish `hmm : m = fun k => ((fun _ : K => (0 : ℕ)) k : ℤ)` using `funext fun k => isEmptyElim k`.

Rewrite using `[hmm, hval]`. Establish `hne : (⟨Ideal.Quotient.mkₐ F q 1, Submodule.mem_map_of_mem (mem_weightedHomogeneousSubmodule F _ _ _ |>.mpr (isWeightedHomogeneous_one F _))⟩ : gradedPiece q (fun _ : K => 0)) ≠ 0`. Introduce `h0`. Establish `h1` using `congrArg Subtype.val h0`. Simplify using `only [Submodule.coe_zero, map_one] at h1`.

Conclude with `hq.isPrime.ne_top (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h1) |> (Ideal.eq_top_iff_one q).mpr)`. Conclude with `Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩` after adjusting the coercions.
-/
theorem pos_of_isEmpty {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] [IsEmpty K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ) (hq : IsMultiProjPrime q)
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    0 < intNum F q (fun _ : Fin e => fun _ : K => (1 : ℤ)) := by
  have hle := (ringKrullDim_quotient_le q).trans_eq
    (MvPolynomial.ringKrullDim_of_isNoetherianRing (R := F) (ι := Σ k, ι k))
  rw [hd, ringKrullDim_eq_zero_of_field, zero_add, Nat.card_of_isEmpty, Fintype.card_eq_zero,
    add_zero] at hle
  have he : e = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hle) : (e : ℕ∞) = 0)
  subst he
  have hrel : FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq q (0 + Fintype.card K) hd]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  obtain ⟨hA, -⟩ := FieldNumbers.MixedDiffConst.full F K ι q hq.multiHomog hq.relevant 0 hrel
  obtain ⟨m, hm⟩ := (hA (fun _ : Fin 0 => fun _ : K => (1 : ℤ))).exists
  rw [← hm]
  have hm0 : mixedDiff (fun _ : Fin 0 => fun _ : K => (1 : ℤ)) (hilbFn q) m = hilbFn q m := rfl
  rw [hm0]
  obtain ⟨hfin, hval⟩ := FieldNumbers.GradedFinite.full F K ι q (fun _ => 0)
  have hmm : m = fun k => ((fun _ : K => (0 : ℕ)) k : ℤ) := funext fun k => isEmptyElim k
  rw [hmm, hval]
  have hne : (⟨Ideal.Quotient.mkₐ F q 1, Submodule.mem_map_of_mem
      (mem_weightedHomogeneousSubmodule F _ _ _ |>.mpr (isWeightedHomogeneous_one F _))⟩ :
        gradedPiece q (fun _ : K => 0)) ≠ 0 := by
    intro h0
    have h1 := congrArg Subtype.val h0
    simp only [Submodule.coe_zero, map_one] at h1
    exact hq.isPrime.ne_top (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h1) |>
      (Ideal.eq_top_iff_one q).mpr)
  exact_mod_cast Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩

end MultiDegreePositive

/- English proof (translation)
Introduce `F _ K _ _ ι _ q e hq hd`. Break down `isEmpty_or_nonempty K with hK | hK` into its components or cases. Conclude with `MultiDegreePositive.pos_of_isEmpty q e hq hd`. Establish `hq'` using `hPrime F K ι q hq`. Establish `hge` using `hDim F K ι q e hq hd`.

Establish `hle` using `(ringKrullDim_quotient_le (segrePrime F q)).trans_eq (MvPolynomial.ringKrullDim_of_isNoetherianRing (R := F) (ι := Σ _ : Unit, ∀ k, ι k))`. Rewrite `hle` using `[ringKrullDim_eq_zero_of_field, zero_add]`. Choose the witnesses or unpack the hypotheses as in `⟨D, hD, heD⟩ : ∃ D : ℕ, ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q) = ((D + 1 : ℕ) : WithBot ℕ∞) ∧ e ≤ D := by`. Generalize the expression as in `ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q) = x at hge hle ⊢`. Proceed by induction on `x using WithBot.recBotCoe with`.

Consider the case `bot => exact absurd hge (by simp)`. Consider the case `coe x`. Proceed by induction on `x using ENat.recTopCoe with`. Consider the case `top`. Establish `h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((Nat.card (Σ _ : Unit, ∀ k, ι k) : ℕ∞) : WithBot ℕ∞)` using `hle`.

Conclude with `absurd (WithBot.coe_le_coe.mp h') (not_le.mpr (ENat.natCast_lt_top _))`. Consider the case `coe m`. Establish `hm : e + 1 ≤ m` using `by exact_mod_cast hge`. Conclude with `⟨m - 1, by rw [Nat.sub_add_cancel (by omega)]; rfl, by omega⟩`. Establish `hrel : FieldNumbers.relDim q = ((e : ℕ) : WithBot (WithTop ℤ))`.

Rewrite using `[FieldNumbers.relDim_of_ringKrullDim_eq q (e + Fintype.card K) hd]`. Simplify using `only [Nat.cast_add, add_sub_cancel_right]`. Both sides reduce to the same expression. Establish `hrel' : FieldNumbers.relDim (segrePrime F q) = ((D : ℕ) : WithBot (WithTop ℤ))`. Rewrite using `[FieldNumbers.relDim_of_ringKrullDim_eq (segrePrime F q) (D + 1) hD]`.

Simplify using `only [Fintype.card_unit, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]`. Both sides reduce to the same expression. Take `⟨hA, hB⟩` from `FieldNumbers.MixedDiffConst.full F K ι q hq.multiHomog hq.relevant e hrel`. Take `⟨hA', -⟩` from `FieldNumbers.MixedDiffConst.full F Unit (fun _ => ∀ k, ι k) (segrePrime F q) hq'.multiHomog hq'.relevant D hrel'`. Establish `hpos` using `DegreePositive.proof F (∀ k, ι k) (segrePrime F q) D hq' hD`.

Establish `hdiag` using `MultiDegreePositive.mixedDiff_diag (hilbFn q) (hilbFn (segrePrime F q)) (fun n => hHilb F K ι q n)`. Establish `hA'd` using `(MultiDegreePositive.tendsto_diag Unit).eventually (hA' (fun _ : Fin D => fun _ : Unit => (1 : ℤ)))`. Establish `hDe : D = e`. Assume the negation of the conclusion as `hne`. Establish `hBd` using `(MultiDegreePositive.tendsto_diag K).eventually (hB D (by omega) (fun _ : Fin D => fun _ : K => (1 : ℤ)))`.

Take `⟨n, h1, h2⟩` from `(hA'd.and hBd).exists`. Rewrite `h1` using `[hdiag]`. Use linear arithmetic over natural numbers and integers. Substitute `hDe` using the available equality. Establish `hAd` using `(MultiDegreePositive.tendsto_diag K).eventually (hA (fun _ : Fin D => fun _ : K => (1 : ℤ)))`.

Take `⟨n, h1, h2⟩` from `(hA'd.and hAd).exists`. Rewrite `h1` using `[hdiag]`. Use linear arithmetic over natural numbers and integers.
-/
theorem MultiDegreePositive.proof (hPrime : SegrePrime.Statement) (hHilb : SegreHilb.Statement)
    (hDim : SegreDimGe.Statement) : MultiDegreePositive.Statement := by
  intro F _ K _ _ ι _ q e hq hd
  rcases isEmpty_or_nonempty K with hK | hK
  · exact MultiDegreePositive.pos_of_isEmpty q e hq hd

  have hq' := hPrime F K ι q hq
  have hge := hDim F K ι q e hq hd
  have hle := (ringKrullDim_quotient_le (segrePrime F q)).trans_eq
    (MvPolynomial.ringKrullDim_of_isNoetherianRing (R := F)
      (ι := Σ _ : Unit, ∀ k, ι k))
  rw [ringKrullDim_eq_zero_of_field, zero_add] at hle

  obtain ⟨D, hD, heD⟩ : ∃ D : ℕ, ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸
      segrePrime F q) = ((D + 1 : ℕ) : WithBot ℕ∞) ∧ e ≤ D := by
    generalize ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q) = x at hge hle ⊢
    induction x using WithBot.recBotCoe with
    | bot => exact absurd hge (by simp)
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((Nat.card (Σ _ : Unit, ∀ k, ι k) : ℕ∞) : WithBot ℕ∞) := hle
        exact absurd (WithBot.coe_le_coe.mp h') (not_le.mpr (ENat.natCast_lt_top _))
      | coe m =>
        have hm : e + 1 ≤ m := by exact_mod_cast hge
        exact ⟨m - 1, by rw [Nat.sub_add_cancel (by omega)]; rfl, by omega⟩
  have hrel : FieldNumbers.relDim q = ((e : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq q (e + Fintype.card K) hd]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  have hrel' : FieldNumbers.relDim (segrePrime F q) = ((D : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq (segrePrime F q) (D + 1) hD]
    simp only [Fintype.card_unit, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rfl
  obtain ⟨hA, hB⟩ := FieldNumbers.MixedDiffConst.full F K ι q hq.multiHomog hq.relevant e hrel
  obtain ⟨hA', -⟩ := FieldNumbers.MixedDiffConst.full F Unit (fun _ => ∀ k, ι k) (segrePrime F q)
    hq'.multiHomog hq'.relevant D hrel'
  have hpos := DegreePositive.proof F (∀ k, ι k) (segrePrime F q) D hq' hD
  have hdiag := MultiDegreePositive.mixedDiff_diag (hilbFn q) (hilbFn (segrePrime F q))
    (fun n => hHilb F K ι q n)
  have hA'd := (MultiDegreePositive.tendsto_diag Unit).eventually
    (hA' (fun _ : Fin D => fun _ : Unit => (1 : ℤ)))

  have hDe : D = e := by
    by_contra hne
    have hBd := (MultiDegreePositive.tendsto_diag K).eventually
      (hB D (by omega) (fun _ : Fin D => fun _ : K => (1 : ℤ)))
    obtain ⟨n, h1, h2⟩ := (hA'd.and hBd).exists
    rw [hdiag] at h1
    omega
  subst hDe
  have hAd := (MultiDegreePositive.tendsto_diag K).eventually
    (hA (fun _ : Fin D => fun _ : K => (1 : ℤ)))
  obtain ⟨n, h1, h2⟩ := (hA'd.and hAd).exists
  rw [hdiag] at h1
  omega

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
