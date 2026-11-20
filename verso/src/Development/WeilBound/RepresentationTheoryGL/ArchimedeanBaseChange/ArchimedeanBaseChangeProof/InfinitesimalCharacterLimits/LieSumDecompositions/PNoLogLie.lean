import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PNoLogSt
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.CasimirOnParabolicInduction
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceMemOfQdetMem

noncomputable section

open NumberField Polynomial GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def Zr (N r : ℕ) : Lie E N := fun i j => if i = j ∧ (i : ℕ) < r then 1 else 0

def Tr1 (r s : ℕ) (τ : E →+* ℂ) : Module.End ℂ (Sm E (r + s)) :=
  ∑ i : Fin r, Eop τ (Fin.castAdd s i) (Fin.castAdd s i)

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _`. Rewrite using `[Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i w`.

Simplify using `only [Pi.mul_apply]`. Apply the tactic sequence `split_ifs <;> simp [← Complex.exp_add]`.
-/
theorem aInf_add' (N r : ℕ) (s t : ℝ) : aInf E N r (s + t) = aInf E N r s * aInf E N r t := by
  apply Units.ext
  change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i w
  simp only [Pi.mul_apply]
  split_ifs <;> simp [← Complex.exp_add]

omit [NumberField E] [IsTotallyComplex E] in
/- English proof (translation)
The claim follows from `Units.ext (by change Matrix.diagonal _ = 1 rw [← Matrix.diagonal_one] congr 1 funext i w simp)`.
-/
theorem aInf_zero' (N r : ℕ) : aInf E N r 0 = 1 :=
  Units.ext (by
    change Matrix.diagonal _ = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i w
    simp)

/- English proof (translation)
Rewrite using `[aT, aT, aT, aInf_add', map_mul]`.
-/
theorem aT_add' (N r : ℕ) (s t : ℝ) : aT E N r (s + t) = aT E N r s * aT E N r t := by
  rw [aT, aT, aT, aInf_add', map_mul]

/- English proof (translation)
Rewrite using `[lieS_apply, lieS_apply]`. Establish `h` using `lie_comm (E := E) (toL (Matrix.single i i x)) (toL (Matrix.single j j y))`. Establish `e : Matrix.of (toL (Matrix.single i i x)) * Matrix.of (toL (Matrix.single j j y)) = Matrix.of (toL (Matrix.single j j y)) * Matrix.of (toL (Matrix.single i i x))`. Simplify using `only [toL, Equiv.apply_symm_apply]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Rewrite using `[Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_comm]`. Establish `z : ∀ (p q : Fin N) (u v : Cinf E), p ≠ q → Matrix.single p p u * Matrix.single q q v = 0`. Introduce `p q u v hpq`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.single_apply]`. Distinguish the cases in `h1 : p = a ∧ p = c`. Rewrite using `[if_pos h1, if_neg (fun h2 => hpq (h1.2.trans h2.1.symm)), mul_zero]`.

Rewrite using `[if_neg h1, zero_mul]`. Rewrite using `[z i j x y hij, z j i y x (Ne.symm hij)]`. Rewrite `h` using `[e, sub_self]`. Conclude with `sub_eq_zero.1 h`.
-/
theorem lieS_diag_comm {N : ℕ} (i j : Fin N) (x y : Cinf E) : Commute (lieS E N i i x) (lieS E N j j y) := by
  classical
  rw [lieS_apply, lieS_apply]
  have h := lie_comm (E := E) (toL (Matrix.single i i x)) (toL (Matrix.single j j y))
  have e : Matrix.of (toL (Matrix.single i i x)) * Matrix.of (toL (Matrix.single j j y)) =
      Matrix.of (toL (Matrix.single j j y)) * Matrix.of (toL (Matrix.single i i x)) := by
    simp only [toL, Equiv.apply_symm_apply]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.single_mul_single_same, Matrix.single_mul_single_same, mul_comm]
    · have z : ∀ (p q : Fin N) (u v : Cinf E), p ≠ q → Matrix.single p p u * Matrix.single q q v = 0 := by
        intro p q u v hpq
        refine Matrix.ext fun a b => ?_
        rw [Matrix.mul_apply, Matrix.zero_apply]
        refine Finset.sum_eq_zero fun c _ => ?_
        simp only [Matrix.single_apply]
        by_cases h1 : p = a ∧ p = c
        · rw [if_pos h1, if_neg (fun h2 => hpq (h1.2.trans h2.1.symm)), mul_zero]
        · rw [if_neg h1, zero_mul]
      rw [z i j x y hij, z j i y x (Ne.symm hij)]
  rw [e, sub_self] at h
  exact sub_eq_zero.1 h

/- English proof (translation)
Establish `hc` using `fun x y => lieS_diag_comm (E := E) i j x y`. Simplify using `only [Eop]`. Use `Commute.smul_right (Commute.smul_left ?_ _) _` and prove the remaining obligations. Conclude with `Commute.sub_left (Commute.sub_right (hc _ _) ((hc _ _).smul_right _)) ((Commute.sub_right (hc _ _) ((hc _ _).smul_right _)).smul_left _)`.
-/
theorem Eop_diag_comm {N : ℕ} (τ τ' : E →+* ℂ) (i j : Fin N) : Commute (Eop τ i i) (Eop τ' j j) := by
  have hc := fun x y => lieS_diag_comm (E := E) i j x y
  simp only [Eop]
  refine Commute.smul_right (Commute.smul_left ?_ _) _
  exact Commute.sub_left (Commute.sub_right (hc _ _) ((hc _ _).smul_right _))
    ((Commute.sub_right (hc _ _) ((hc _ _).smul_right _)).smul_left _)

/- English proof (translation)
Simplify using `only [Tr1, ← Finset.sum_add_distrib, Eop_add_Eop_conj]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← map_sum]`. Establish `h1 : ∑ w : InfinitePlace E, atEmb w.embedding (1 : ℂ) = (1 : Cinf E)`. Establish `e : ∀ w : InfinitePlace E, atEmb w.embedding (1 : ℂ) = Pi.single w ((fun _ => (1 : ℂ)) w)`.

Introduce `w`. Simplify using `[atEmb, InfinitePlace.mk_embedding]`. Simplify using `only [e]`. Conclude with `Finset.univ_sum_single _`. Rewrite using `[h1]`.

Simplify using `only [lieS_apply, ← map_sum]`. Use `congr 1`. Use function extensionality and compare the values at `a b`. Simplify using `only [Zr, toL, Finset.sum_apply, Matrix.of_symm_apply, Matrix.single_apply]`. Distinguish the cases in `hab : a = b ∧ (a : ℕ) < r`.

Rewrite using `[if_pos hab]`. Take `⟨rfl, ha⟩` from `hab`. Rewrite using `[Finset.sum_eq_single (⟨a, ha⟩ : Fin r)]`. Rewrite using `[if_pos]`. Conclude with `⟨Fin.ext rfl, Fin.ext rfl⟩`.

Introduce `c _ hc`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, -⟩`. Conclude with `hc (Fin.ext (by have := congrArg Fin.val h1; simpa using this))`. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hab]`. Use `(Finset.sum_eq_zero fun c _ => ?_).symm` and prove the remaining obligations. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hab ⟨h1.symm.trans h2, by rw [← h1]; simp⟩`.
-/
theorem lie_Zr (r s : ℕ) : lie E (r + s) (Zr (r + s) r) =
    ∑ w : InfinitePlace E, (Tr1 r s w.embedding + Tr1 r s (ComplexEmbedding.conjugate w.embedding)) := by
  classical
  simp only [Tr1, ← Finset.sum_add_distrib, Eop_add_Eop_conj]
  rw [Finset.sum_comm]
  simp only [← map_sum]
  have h1 : ∑ w : InfinitePlace E, atEmb w.embedding (1 : ℂ) = (1 : Cinf E) := by
    have e : ∀ w : InfinitePlace E, atEmb w.embedding (1 : ℂ) = Pi.single w ((fun _ => (1 : ℂ)) w) := by
      intro w; simp [atEmb, InfinitePlace.mk_embedding]
    simp only [e]
    exact Finset.univ_sum_single _
  rw [h1]
  simp only [lieS_apply, ← map_sum]
  congr 1
  funext a b
  simp only [Zr, toL, Finset.sum_apply, Matrix.of_symm_apply, Matrix.single_apply]
  by_cases hab : a = b ∧ (a : ℕ) < r
  · rw [if_pos hab]
    obtain ⟨rfl, ha⟩ := hab
    rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin r)]
    · rw [if_pos]
      exact ⟨Fin.ext rfl, Fin.ext rfl⟩
    · intro c _ hc
      rw [if_neg]
      rintro ⟨h1, -⟩
      exact hc (Fin.ext (by have := congrArg Fin.val h1; simpa using this))
    · simp
  · rw [if_neg hab]
    refine (Finset.sum_eq_zero fun c _ => ?_).symm
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hab ⟨h1.symm.trans h2, by rw [← h1]; simp⟩

/- English proof (translation)
Unfold `Tr1`. Apply `Commute.sum_left` to reduce the goal to its premises. Introduce `i _`. Apply `Commute.sum_right` to reduce the goal to its premises. Introduce `j _`.

Conclude with `Eop_diag_comm _ _ _ _`.
-/
theorem Tr1_comm (r s : ℕ) (τ τ' : E →+* ℂ) : Commute (Tr1 (E := E) r s τ) (Tr1 r s τ') := by
  unfold Tr1
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact Eop_diag_comm _ _ _ _

omit [IsTotallyComplex E] in
/- English proof (translation)
Rewrite using `[hasDerivAt_pi]`. Introduce `i`. Rewrite using `[hasDerivAt_pi]`. Introduce `j`. Rewrite using `[hasDerivAt_pi]`.

Introduce `w`. Simplify using `only [aInf, toL, Zr, Matrix.of_symm_apply, Matrix.diagonal_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Distinguish the cases in `hi : (i : ℕ) < r`.

Simplify using `only [if_true, hi, and_self, Pi.one_apply]`. Use `(Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal` as an intermediate fact. Simplify using `using this`. Simplify using `only [if_true, hi, and_false, if_false, Pi.zero_apply]`. Conclude with `hasDerivAt_const _ _`.

Simplify using `only [hij, if_false, false_and, Pi.zero_apply]`. Conclude with `hasDerivAt_const _ _`.
-/
theorem hasDerivAt_aInf (N r : ℕ) : HasDerivAt (fun t : ℝ => toL (aInf E N r t).val) (Zr N r) 0 := by
  rw [hasDerivAt_pi]; intro i
  rw [hasDerivAt_pi]; intro j
  rw [hasDerivAt_pi]; intro w
  simp only [aInf, toL, Zr, Matrix.of_symm_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hi : (i : ℕ) < r
    · simp only [if_true, hi, and_self, Pi.one_apply]
      have := (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
      simpa using this
    · simp only [if_true, hi, and_false, if_false, Pi.zero_apply]
      exact hasDerivAt_const _ _
  · simp only [hij, if_false, false_and, Pi.zero_apply]
    exact hasDerivAt_const _ _

/- English proof (translation)
Establish `key` using `hasDerivAt_curve Φ (h * aT E (r + s) r t) (aInf E (r + s) r) (Zr (r + s) r) (aInf_zero' _ _) (hasDerivAt_aInf _ _)`. Establish `e : (fun u => Φ.1 (h * aT E (r + s) r t * infGL E (r + s) (aInf E (r + s) r u))) = fun u => Φ.1 (h * aT E (r + s) r (t + u))`. Use function extensionality and compare the values at `u`. Rewrite using `[aT_add', ← mul_assoc]`. Both sides reduce to the same expression.

Rewrite `key` using `[e]`. Establish `h2` using `HasDerivAt.comp_sub_const (f := fun u => Φ.1 (h * aT E (r + s) r (t + u))) t t (by simpa using key)`. Simplify `h2` using `[lie_apply]`.
-/
theorem hasDerivAt_aT (r s : ℕ) (Φ : Sm E (r + s)) (h : GA E (r + s)) (t : ℝ) :
    HasDerivAt (fun t : ℝ => Φ.1 (h * aT E (r + s) r t))
      ((lie E (r + s) (Zr (r + s) r) Φ).1 (h * aT E (r + s) r t)) t := by
  have key := hasDerivAt_curve Φ (h * aT E (r + s) r t) (aInf E (r + s) r) (Zr (r + s) r) (aInf_zero' _ _)
    (hasDerivAt_aInf _ _)
  have e : (fun u => Φ.1 (h * aT E (r + s) r t * infGL E (r + s) (aInf E (r + s) r u))) =
      fun u => Φ.1 (h * aT E (r + s) r (t + u)) := by
    funext u
    rw [aT_add', ← mul_assoc]
    rfl
  rw [e] at key
  have h2 := HasDerivAt.comp_sub_const (f := fun u => Φ.1 (h * aT E (r + s) r (t + u))) t t (by simpa using key)
  simpa [lie_apply] using h2

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[GlobalTheory.SmGL.val_emb₂, JFinTr.aT_val, JFinTr.aT_val]`. Use extensionality with `i j`. Take `⟨i, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i`. Take `⟨j, rfl⟩` from `(GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j`.

Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;> simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr, Matrix.diagonal_apply]`. Establish `e1 : (fun _ : InfinitePlace E => (1 : ℂ)) = (1 : Cinf E)` using `rfl`. Simplify using `only [Matrix.one_apply, e1, sub_add_cancel]`.
-/
theorem lev_aT (r s : ℕ) (t : ℝ) : lev (Ad E) r s (aT E r r t, 1) = aT E (r + s) r t := by
  apply Units.ext
  rw [GlobalTheory.SmGL.val_emb₂, JFinTr.aT_val, JFinTr.aT_val]
  ext i j
  obtain ⟨i, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective i
  obtain ⟨j, rfl⟩ := (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)).surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> simp [GlobalTheory.SmGL.stdSum_inl, GlobalTheory.SmGL.stdSum_inr, Matrix.diagonal_apply]
  have e1 : (fun _ : InfinitePlace E => (1 : ℂ)) = (1 : Cinf E) := rfl
  simp only [Matrix.one_apply, e1, sub_add_cancel]

/- English proof (translation)
Use `⟨(m.1 * aT E r r t, m.2), ?_⟩` and prove the remaining obligations. Rewrite using `[← lev_aT r s t, ← map_mul]`. Use `congr 1`. Apply the tactic sequence `ext <;> simp`.
-/
theorem lev_mul_aT (r s : ℕ) (m : GA E r × GA E s) (t : ℝ) :
    ∃ m', lev (Ad E) r s m * aT E (r + s) r t = lev (Ad E) r s m' := by
  refine ⟨(m.1 * aT E r r t, m.2), ?_⟩
  rw [← lev_aT r s t, ← map_mul]
  congr 1
  ext <;> simp

/- English proof (translation)
Take `⟨x', hx'⟩` from `JFinTr.diag_mul_unip (aT E (r + s) r t) _ _ (JFinTr.aT_val (r + s) r t) (JFinTr.aT_inv_val (r + s) r t) x`. Establish `e : aT E (r + s) r t * (unip x * lev (Ad E) r s m * y) = unip x' * (aT E (r + s) r t * lev (Ad E) r s m * y)`. Rewrite using `[← mul_assoc, ← mul_assoc, hx']`. Simplify using `only [mul_assoc]`. Rewrite using `[e, hF, JFinTr.aT_comm_lev]`.
-/
theorem aT_mul_decomp (r s : ℕ) (F : GA E (r + s) → ℂ) (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F (unip x * g) = F g)
    (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (y : GA E (r + s)) (t : ℝ) :
    F (aT E (r + s) r t * (unip x * lev (Ad E) r s m * y)) = F (lev (Ad E) r s m * aT E (r + s) r t * y) := by
  obtain ⟨x', hx'⟩ := JFinTr.diag_mul_unip (aT E (r + s) r t) _ _ (JFinTr.aT_val (r + s) r t)
    (JFinTr.aT_inv_val (r + s) r t) x
  have e : aT E (r + s) r t * (unip x * lev (Ad E) r s m * y) = unip x' * (aT E (r + s) r t * lev (Ad E) r s m * y) := by
    rw [← mul_assoc, ← mul_assoc, hx']
    simp only [mul_assoc]
  rw [e, hF, JFinTr.aT_comm_lev]

/- English proof (translation)
Set `n : Fin 2 → ℕ` to `![r, s]`. Establish `h : ∑ i, n i = n 0 + n 1` using `CapFactor.two_sum n`. Take `⟨v, hv, m, k, g', e⟩` from `GlobalTheory.SpehInfChar.exists_iwasawa E n h g`. Take `⟨xv, rfl⟩` from `CapFactor.exists_unip_of_mem n h hv`. Use `⟨xv, (m 0, m 1), k, g', ?_⟩` and prove the remaining obligations.

Establish `hx : lev (Ad E) r s (m 0, m 1) = GlobalTheory.SmGL.leviEmb (Ad E) (GlobalTheory.SmGL.stdBlocks n h) m` using `(CapFactor.lev_eq_leviEmb (R := Ad E) n h (m 0, m 1)).trans (by rw [PositivityTheory.Rg.Rs.PInfInd2A.levPair_eta])`. Rewrite using `[hx]`. Conclude with `e`.
-/
theorem iwasawa2 (r s : ℕ) (g : GA E (r + s)) : ∃ (x : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s)
    (k : Kinf E (r + s)) (g' : GL (Fin (r + s)) (Af E)),
    g = unip x * lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g') := by
  let n : Fin 2 → ℕ := ![r, s]
  have h : ∑ i, n i = n 0 + n 1 := CapFactor.two_sum n
  obtain ⟨v, hv, m, k, g', e⟩ := GlobalTheory.SpehInfChar.exists_iwasawa E n h g
  obtain ⟨xv, rfl⟩ := CapFactor.exists_unip_of_mem n h hv
  refine ⟨xv, (m 0, m 1), k, g', ?_⟩
  have hx : lev (Ad E) r s (m 0, m 1) = GlobalTheory.SmGL.leviEmb (Ad E) (GlobalTheory.SmGL.stdBlocks n h) m :=
    (CapFactor.lev_eq_leviEmb (R := Ad E) n h (m 0, m 1)).trans (by rw [PositivityTheory.Rg.Rs.PInfInd2A.levPair_eta])
  rw [hx]
  exact e

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.NoLogarithmTerms

end
