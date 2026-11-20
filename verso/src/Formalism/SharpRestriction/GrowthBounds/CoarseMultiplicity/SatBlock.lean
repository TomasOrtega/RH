import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BFDefs
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.BlockInj
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.SymInt

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r : ℕ} [NeZero r] (D : BlockData N)

def beF (v : BVar N r D.T.t) : MvPolynomial (BVar N r D.T.t) (KK O) :=
  match v with
  | Sum.inl a => X (Sum.inl a)
  | Sum.inr (_, false) => 1
  | Sum.inr (i, true) => X (Sum.inr (i, true))

def giF (v : BVar N r D.T.t) : MvPolynomial (BVar N r D.T.t) (KK O) :=
  match v with
  | Sum.inl a => X (Sum.inl a)
  | Sum.inr (i, false) => X (Sum.inr (i, false))
  | Sum.inr (i, true) => X (Sum.inr (i, true)) - qq (O := O) (r := r) D i

/- English proof (translation)
Use `Fin.lastCases ?_ (fun i' => ?_) i` and prove the remaining obligations. Simplify using `[qq, xiVar, hf]`. Simplify using `[qq, hf]`.
-/
theorem qq_fix (f : BVar N r D.T.t → MvPolynomial (BVar N r D.T.t) (KK O)) (hf : ∀ a, f (Sum.inl a) = X (Sum.inl a))
    (i : Fin (D.T.t + 1)) : aeval f (qq (O := O) (r := r) D i) = qq (O := O) (r := r) D i := by
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp [qq, xiVar, hf]
  · simp [qq, hf]

/- English proof (translation)
Use `Fin.lastCases ?_ (fun i' => ?_) i` and prove the remaining obligations. Simplify using `only [qq, Fin.lastCases_last]`. Conclude with `Subalgebra.sum_mem _ fun c _ => (IntAlg O _).mul_mem (X_mem_intAlg O _) (X_mem_intAlg O _)`. Simplify using `only [qq, Fin.lastCases_castSucc]`. Conclude with `Subalgebra.sum_mem _ fun c _ => (IntAlg O _).mul_mem (X_mem_intAlg O _) (X_mem_intAlg O _)`.
-/
theorem qq_int (i : Fin (D.T.t + 1)) : qq (O := O) (r := r) D i ∈ IntAlg O (BVar N r D.T.t) := by
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · simp only [qq, Fin.lastCases_last]
    exact Subalgebra.sum_mem _ fun c _ => (IntAlg O _).mul_mem (X_mem_intAlg O _) (X_mem_intAlg O _)
  · simp only [qq, Fin.lastCases_castSucc]
    exact Subalgebra.sum_mem _ fun c _ => (IntAlg O _).mul_mem (X_mem_intAlg O _) (X_mem_intAlg O _)

/- English proof (translation)
Establish `h : ((aeval (giF (O` using `O) (r := r) D)).comp ((aeval (beF (O := O) (r := r) D)).comp (tau D))) = aeval (beF (O := O) (r := r) D) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `(a | ⟨i, _ | _⟩)`. Simplify using `[tau, tauF, beF, giF]`. Simplify using `[tau, tauF, beF, giF]`.

Simplify using `only [AlgHom.comp_apply, tau, aeval_X, tauF, map_add, map_mul, beF, one_mul, giF, map_one]`. Rewrite using `[qq_fix D (beF D) (fun _ => rfl), qq_fix D (giF D) (fun _ => rfl)]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `DFunLike.congr_fun h P`.
-/
theorem gi_be_tau (P : MvPolynomial (BVar N r D.T.t) (KK O)) :
    aeval (giF (O := O) (r := r) D) (aeval (beF (O := O) (r := r) D) (tau D P)) = aeval (beF (O := O) (r := r) D) P := by
  have h : ((aeval (giF (O := O) (r := r) D)).comp ((aeval (beF (O := O) (r := r) D)).comp (tau D))) =
      aeval (beF (O := O) (r := r) D) := by
    apply MvPolynomial.algHom_ext
    rintro (a | ⟨i, _ | _⟩)
    · simp [tau, tauF, beF, giF]
    · simp [tau, tauF, beF, giF]
    · simp only [AlgHom.comp_apply, tau, aeval_X, tauF, map_add, map_mul, beF, one_mul, giF, map_one]
      rw [qq_fix D (beF D) (fun _ => rfl), qq_fix D (giF D) (fun _ => rfl)]
      ring
  exact DFunLike.congr_fun h P

/- English proof (translation)
Establish `h : (ppi (O` using `O) (r := r) D).comp (aeval (beF (O := O) (r := r) D)) = ppi D := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `(a | ⟨i, _ | _⟩)`. Simplify using `[beF]`. Simplify using `[beF, ppi, piF]`.

Simplify using `[beF]`. Conclude with `DFunLike.congr_fun h P`.
-/
theorem ppi_be (P : MvPolynomial (BVar N r D.T.t) (KK O)) :
    ppi D (aeval (beF (O := O) (r := r) D) P) = ppi D P := by
  have h : (ppi (O := O) (r := r) D).comp (aeval (beF (O := O) (r := r) D)) = ppi D := by
    apply MvPolynomial.algHom_ext
    rintro (a | ⟨i, _ | _⟩)
    · simp [beF]
    · simp [beF, ppi, piF]
    · simp [beF]
  exact DFunLike.congr_fun h P

/- English proof (translation)
Proceed by induction on `q using MvPolynomial.induction_on generalizing e with`. Consider the case `C a`. Rewrite using `[map_C]`. Establish `: ppi (O` using `O) (r := r) D (C (algebraMap O (KK O) a)) = C (C (algebraMap O (KK O) a)) := by`. Simplify using `[ppi, MvPolynomial.algebraMap_eq]`.

Rewrite using `[this, coeff_C]`. Use `split_ifs`. Conclude with `⟨C a, by simp⟩`. Conclude with `(IntAlg O _).zero_mem`. Consider the case `add p q hp hq`.

Rewrite using `[map_add, map_add, coeff_add]`. Conclude with `(IntAlg O _).add_mem (hp e) (hq e)`. Consider the case `mul_X p v hp`. Rewrite using `[map_mul, map_mul, map_X]`. Establish `hv : ppi (O` using `O) (r := r) D (X v) = piF D v := by simp [ppi]`.

Rewrite using `[hv]`. Break down `v with ⟨a, c⟩ | ⟨i, _ | _⟩` into its components or cases. Use `Fin.lastCases ?_ (fun a' => ?_) a` and prove the remaining obligations. Simplify using `only [piF, Fin.lastCases_last]`. Rewrite using `[coeff_mul_X']`.

Use `split_ifs`. Conclude with `hp _`. Conclude with `(IntAlg O _).zero_mem`. Simplify using `only [piF, Fin.lastCases_castSucc]`. Rewrite using `[mul_comm, coeff_C_mul]`.

Conclude with `(IntAlg O _).mul_mem (X_mem_intAlg O _) (hp e)`. Simplify using `only [piF, mul_one]`. Conclude with `hp e`. Simplify using `only [piF]`. Rewrite using `[coeff_mul_X']`.

Use `split_ifs`. Conclude with `hp _`. Conclude with `(IntAlg O _).zero_mem`.
-/
theorem ppi_int (q : MvPolynomial (BVar N r D.T.t) O) (e : (Fin (D.T.t + 1) ⊕ Fin r) →₀ ℕ) :
    coeff e (ppi (O := O) (r := r) D (map (algebraMap O (KK O)) q)) ∈ IntAlg O (Fin N × Fin r) := by
  classical
  induction q using MvPolynomial.induction_on generalizing e with
  | C a =>
    rw [map_C]
    have : ppi (O := O) (r := r) D (C (algebraMap O (KK O) a)) = C (C (algebraMap O (KK O) a)) := by
      simp [ppi, MvPolynomial.algebraMap_eq]
    rw [this, coeff_C]
    split_ifs
    · exact ⟨C a, by simp⟩
    · exact (IntAlg O _).zero_mem
  | add p q hp hq =>
    rw [map_add, map_add, coeff_add]
    exact (IntAlg O _).add_mem (hp e) (hq e)
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_X]
    have hv : ppi (O := O) (r := r) D (X v) = piF D v := by simp [ppi]
    rw [hv]
    rcases v with ⟨a, c⟩ | ⟨i, _ | _⟩
    · refine Fin.lastCases ?_ (fun a' => ?_) a
      · simp only [piF, Fin.lastCases_last]
        rw [coeff_mul_X']
        split_ifs
        · exact hp _
        · exact (IntAlg O _).zero_mem
      · simp only [piF, Fin.lastCases_castSucc]
        rw [mul_comm, coeff_C_mul]
        exact (IntAlg O _).mul_mem (X_mem_intAlg O _) (hp e)
    · simp only [piF, mul_one]
      exact hp e
    · simp only [piF]
      rw [coeff_mul_X']
      split_ifs
      · exact hp _
      · exact (IntAlg O _).zero_mem

/- English proof (translation)
Rewrite `hx` using `[span_eq_range]`. Take `⟨v, rfl⟩` from `hx`. Establish `hv` using `Ltot_apply D v`. Use `set B := ∑ i : ↥(IF (r := r) D), base D i.1.1 i.1.2 (v i : MvPolynomial (Fin N × Fin r) (KK O)) with hB`. Establish `hT : Ltot D v = tau D B`.

Rewrite using `[hv, hB, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => ell_eq_tau D _ _ _`. Establish `h1 : aeval (beF (O` using `O) (r := r) D) B ∈ IntAlg O (BVar N r D.T.t) := by`. Rewrite using `[← gi_be_tau D B, ← hT]`. Use `aeval_mem_intAlg O _ ?_ (aeval_mem_intAlg O _ ?_ (intPol_le O hi))` and prove the remaining obligations.

Introduce and unpack `(a | ⟨i, _ | _⟩)`. Conclude with `X_mem_intAlg O _`. Conclude with `X_mem_intAlg O _`. Conclude with `(IntAlg O _).sub_mem (X_mem_intAlg O _) (qq_int D i)`. Introduce and unpack `(a | ⟨i, _ | _⟩)`.

Conclude with `X_mem_intAlg O _`. Conclude with `(IntAlg O _).one_mem`. Conclude with `X_mem_intAlg O _`. Take `⟨q, hq⟩` from `h1`. Establish `hq' : map (algebraMap O (KK O)) q = aeval (beF (O` using `O) (r := r) D) B := hq`.

Establish `hint : ∀ i0 : ↥(IF (r` using `r) D), (v i0 : MvPolynomial (Fin N × Fin r) (KK O)) ∈ IntAlg O (Fin N × Fin r) := by`. Introduce `i0`. Establish `h2` using `ppi_int D q (eExp D i0.1.1 i0.1.2)`. Rewrite `h2` using `[hq', ppi_be, hB, map_sum]`. Simplify using `only [ppi_base] at h2`.

Rewrite `h2` using `[coeff_sum, Finset.sum_eq_single i0]`. Rewrite `h2` using `[coeff_monomial, if_pos rfl]`. Then use the resulting hypothesis. Introduce `b _ hb`. Rewrite using `[coeff_monomial, if_neg]`. Introduce `he`.

Take `⟨e1, e2⟩` from `eExp_inj D he`. Conclude with `hb (Subtype.ext (Sigma.ext e1 (heq_of_eq e2)))`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Rewrite using `[hv]`.

Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `hi'` using `i.2`. Unfold `IF at hi'`. Rewrite `hi'` using `[Finset.mem_sigma]`. Establish `hlv` using `(mem_Lv D _).1 hi'.1`.

Establish `hβ` using `Finset.Nat.mem_antidiagonalTuple.1 hi'.2`. Take `⟨q0, hq0⟩` from `hint i`. Unfold `BlockData.SSZ`. Use `Submodule.subset_span ?_` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion]`.

Use `⟨i.1.1.1, i.1.1.2, hlv, (v i : MvPolynomial (Fin N × Fin r) (KK O)), ⟨(v i).2, ⟨q0, hq0⟩⟩, xiMon (KK O) N r D.T.t i.1.2, xiMon_mem D _ _ hβ, ?_⟩` and prove the remaining obligations. Rewrite using `[ell_apply]`. Simplify using `only [pre, mul_assoc]`.
-/
theorem sat_block (x : MvPolynomial (BVar N r D.T.t) (KK O))
    (hx : x ∈ Submodule.span (KK O) ((D.SSZ O (r := r) : Submodule O (MvPolynomial (BVar N r D.T.t) (KK O))) :
      Set (MvPolynomial (BVar N r D.T.t) (KK O)))) (hi : x ∈ IntPol O (BVar N r D.T.t)) : x ∈ D.SSZ O (r := r) := by
  classical
  rw [span_eq_range] at hx
  obtain ⟨v, rfl⟩ := hx
  have hv := Ltot_apply D v
  set B := ∑ i : ↥(IF (r := r) D), base D i.1.1 i.1.2 (v i : MvPolynomial (Fin N × Fin r) (KK O)) with hB
  have hT : Ltot D v = tau D B := by
    rw [hv, hB, map_sum]
    exact Finset.sum_congr rfl fun i _ => ell_eq_tau D _ _ _
  have h1 : aeval (beF (O := O) (r := r) D) B ∈ IntAlg O (BVar N r D.T.t) := by
    rw [← gi_be_tau D B, ← hT]
    refine aeval_mem_intAlg O _ ?_ (aeval_mem_intAlg O _ ?_ (intPol_le O hi))
    · rintro (a | ⟨i, _ | _⟩)
      · exact X_mem_intAlg O _
      · exact X_mem_intAlg O _
      · exact (IntAlg O _).sub_mem (X_mem_intAlg O _) (qq_int D i)
    · rintro (a | ⟨i, _ | _⟩)
      · exact X_mem_intAlg O _
      · exact (IntAlg O _).one_mem
      · exact X_mem_intAlg O _
  obtain ⟨q, hq⟩ := h1
  have hq' : map (algebraMap O (KK O)) q = aeval (beF (O := O) (r := r) D) B := hq
  have hint : ∀ i0 : ↥(IF (r := r) D), (v i0 : MvPolynomial (Fin N × Fin r) (KK O)) ∈ IntAlg O (Fin N × Fin r) := by
    intro i0
    have h2 := ppi_int D q (eExp D i0.1.1 i0.1.2)
    rw [hq', ppi_be, hB, map_sum] at h2
    simp only [ppi_base] at h2
    rw [coeff_sum, Finset.sum_eq_single i0] at h2
    · rwa [coeff_monomial, if_pos rfl] at h2
    · intro b _ hb
      rw [coeff_monomial, if_neg]
      intro he
      obtain ⟨e1, e2⟩ := eExp_inj D he
      exact hb (Subtype.ext (Sigma.ext e1 (heq_of_eq e2)))
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi' := i.2
  unfold IF at hi'
  rw [Finset.mem_sigma] at hi'
  have hlv := (mem_Lv D _).1 hi'.1
  have hβ := Finset.Nat.mem_antidiagonalTuple.1 hi'.2
  obtain ⟨q0, hq0⟩ := hint i
  unfold BlockData.SSZ
  refine Submodule.subset_span ?_
  simp only [Set.mem_iUnion]
  refine ⟨i.1.1.1, i.1.1.2, hlv, (v i : MvPolynomial (Fin N × Fin r) (KK O)), ⟨(v i).2, ⟨q0, hq0⟩⟩,
    xiMon (KK O) N r D.T.t i.1.2, xiMon_mem D _ _ hβ, ?_⟩
  rw [ell_apply]
  simp only [pre, mul_assoc]

end

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ D x hx hi` and use `sat_block D x hx hi`.
-/
theorem satAt : SatAt := fun _ _ _ _ _ _ _ D x hx hi => sat_block D x hx hi

end Formalism.MainNotions.ColumnSystems.Pf
