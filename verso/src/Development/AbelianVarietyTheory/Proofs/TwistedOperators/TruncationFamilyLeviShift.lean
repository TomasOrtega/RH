import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsAUnit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviMonotoneInParabolicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaDecompositionAdelicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicDeterminantMultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModulusCharacterProductEqAbsDetStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelParabolicDeterminantAbsOneStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylConjugateParabolicLogModulusStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviLogModulusVectorStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open GlobalTheory.LeviShift

noncomputable section

namespace GlobalTheory.LeviShift

/- English proof (translation)
Introduce `D V Φ L a hg j q y hq`. Establish `hK` using `hg.isCompact`. Establish `hP0 : ∀ p : PA Φ.flag0, (p : GA D V) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j))` using `fun p => by rw [Φ.sub_stdVec]; exact Φ.flag0.par_le_parab _ _ j.succ p.2`. Take `⟨p, k, hk, rfl⟩` from `GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg y`. Take `⟨p', k', hk', e⟩` from `GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg (q * p)`.

Establish `hqy : q * (p * k) = p' * (k' * k)` using `by rw [← mul_assoc, e, mul_assoc]`. Establish `hk'P : k' ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j))`. Establish `: k' = (p' : GA D V)⁻¹ * (q * p)` using `by rw [e]; group`. Rewrite using `[this]`. Conclude with `mul_mem (inv_mem (hP0 p')) (mul_mem hq (hP0 p))`.

Establish `hpos : ∀ (r : PA Φ.flag0) (i : Fin (wittIndex V)), ((absChi Φ i r : NNReal) : ℝ) ≠ 0` using `fun r i => NNReal.coe_ne_zero.2 (GlobalTheory.Doubling.hom_pos _ r).ne'`. Simplify using `only [hqy, mul_mem_riemannRochSpace_add hK _ (mul_mem hk' hk), mul_mem_riemannRochSpace_add hK _ hk]`. Rewrite using `[← Real.log_prod (fun i _ => hpos p' i), ← Real.log_prod (fun i _ => hpos p i), ← NNReal.coe_prod, ← NNReal.coe_prod, GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j p', GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j p]`. Establish `m1` using `GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) (stdVec j) q p hq (hP0 p)`. Establish `m2` using `GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) (stdVec j) p' k' (hP0 p') hk'P`.

Establish `h3` using `GlobalTheory.T.level_parabolic_determinant_abs_one D V Φ L a hg (stdVec j) k' hk' hk'P`. Rewrite `m2` using `[← e]`. Establish `key : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p') = absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) q) * absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p)`. Use `congrArg (absA D.host.F D.host.E) (m1.symm.trans m2)` as an intermediate fact. Rewrite `this` using `[absA_mul, absA_mul, h3, mul_one]`.

Conclude with `this.symm`. Establish `n1 : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p') ≠ 0`. Rewrite using `[← GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j _]`. Conclude with `(Finset.prod_pos fun i _ => GlobalTheory.Doubling.hom_pos _ _).ne'`. Establish `n2 : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) ≠ 0`.

Rewrite using `[← GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j _]`. Conclude with `(Finset.prod_pos fun i _ => GlobalTheory.Doubling.hom_pos _ _).ne'`. Rewrite `n1`, the goal using `[key]`. Unfold `logDelta`. Rewrite using `[NNReal.coe_mul, Real.log_mul (NNReal.coe_ne_zero.2 (left_ne_zero_of_mul n1)) (NNReal.coe_ne_zero.2 n2)]`.
-/
theorem sum_H0_parabolic_mul : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a →
    ∀ (j : Fin (wittIndex V)) (q y : GA D V),
      q ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) →
      ∑ i ∈ Finset.Iic j, H0 Φ (levelAll D.sp.cm.sig V.gram L a) (q * y) i =
        logDelta Φ (stdVec j) q + ∑ i ∈ Finset.Iic j, H0 Φ (levelAll D.sp.cm.sig V.gram L a) y i := by
  intro D V Φ L a hg j q y hq
  have hK := hg.isCompact
  have hP0 : ∀ p : PA Φ.flag0, (p : GA D V) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) :=
    fun p => by rw [Φ.sub_stdVec]; exact Φ.flag0.par_le_parab _ _ j.succ p.2
  obtain ⟨p, k, hk, rfl⟩ := GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg y
  obtain ⟨p', k', hk', e⟩ := GlobalTheory.T.iwasawa_decomposition_adelic D V Φ L a hg (q * p)
  have hqy : q * (p * k) = p' * (k' * k) := by rw [← mul_assoc, e, mul_assoc]
  have hk'P : k' ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (stdVec j)) := by
    have : k' = (p' : GA D V)⁻¹ * (q * p) := by rw [e]; group
    rw [this]; exact mul_mem (inv_mem (hP0 p')) (mul_mem hq (hP0 p))
  have hpos : ∀ (r : PA Φ.flag0) (i : Fin (wittIndex V)), ((absChi Φ i r : NNReal) : ℝ) ≠ 0 := fun r i =>
    NNReal.coe_ne_zero.2 (GlobalTheory.Doubling.hom_pos _ r).ne'
  simp only [hqy, mul_mem_riemannRochSpace_add hK _ (mul_mem hk' hk), mul_mem_riemannRochSpace_add hK _ hk]
  rw [← Real.log_prod (fun i _ => hpos p' i), ← Real.log_prod (fun i _ => hpos p i), ← NNReal.coe_prod,
    ← NNReal.coe_prod, GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j p', GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j p]
  have m1 := GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) (stdVec j) q p hq (hP0 p)
  have m2 := GlobalTheory.T.parabolic_determinant_multiplicative Φ D.sp.cm (AF D.host.F) (stdVec j) p' k' (hP0 p') hk'P
  have h3 := GlobalTheory.T.level_parabolic_determinant_abs_one D V Φ L a hg (stdVec j) k' hk' hk'P
  rw [← e] at m2
  have key : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p') =
      absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) q) *
        absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) := by
    have := congrArg (absA D.host.F D.host.E) (m1.symm.trans m2)
    rw [absA_mul, absA_mul, h3, mul_one] at this; exact this.symm
  have n1 : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p') ≠ 0 := by
    rw [← GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j _]; exact (Finset.prod_pos fun i _ => GlobalTheory.Doubling.hom_pos _ _).ne'
  have n2 : absA D.host.F D.host.E (detU Φ D.sp.cm (AF D.host.F) (stdVec j) p) ≠ 0 := by
    rw [← GlobalTheory.T.modulus_character_product_eq_abs_det D V Φ j _]; exact (Finset.prod_pos fun i _ => GlobalTheory.Doubling.hom_pos _ _).ne'
  rw [key] at n1 ⊢
  unfold logDelta
  rw [NNReal.coe_mul, Real.log_mul (NNReal.coe_ne_zero.2 (left_ne_zero_of_mul n1)) (NNReal.coe_ne_zero.2 n2)]

/- English proof (translation)
Establish `sq : ∀ e : SignTypeˣ, ((e : SignType) : ℝ) * (e : SignType) = 1` using `fun e => by`. Distinguish the cases in `h : e = 1`. Simplify using `[h]`. Rewrite using `[sign_unit e h]`. Evaluate the numerical expressions.

Simplify using `only [PiLp.inner_apply, vec, invSV, inverseChamberMap, RCLike.inner_apply, conj_trivial]`. Establish `e : ∀ x, ((ε x : SignType) : ℝ) * H.ofLp (π x) * (((ε x : SignType) * stdVec j (π x) : SignType) : ℝ) = H.ofLp (π x) * (stdVec j (π x) : ℝ)` using `fun x => by`. Rewrite using `[SignType.coe_mul]`. Take the linear combination `(H.ofLp (π x) * (stdVec j (π x) : ℝ)) * sq (ε x)`. Simplify using `only [e]`.

Rewrite using `[Equiv.sum_comp π (fun i => H.ofLp i * (stdVec j i : ℝ)), show Finset.Iic j = Finset.univ.filter (· ≤ j) by ext; simp, Finset.sum_filter]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : i ≤ j <;> simp [stdVec, h]`.
-/
theorem inner_vector_inverse_levi_shift {k : ℕ} (π : Equiv.Perm (Fin k)) (ε : Fin k → SignTypeˣ) (j : Fin k) (H : A0 k) :
    inner ℝ (vec (invSV π ε (stdVec j))) (inverseChamberMap π ε H) = ∑ i ∈ Finset.Iic j, H i := by
  have sq : ∀ e : SignTypeˣ, ((e : SignType) : ℝ) * (e : SignType) = 1 := fun e => by
    by_cases h : e = 1
    · simp [h]
    · rw [sign_unit e h]; norm_num
  simp only [PiLp.inner_apply, vec, invSV, inverseChamberMap, RCLike.inner_apply, conj_trivial]
  have e : ∀ x, ((ε x : SignType) : ℝ) * H.ofLp (π x) * (((ε x : SignType) * stdVec j (π x) : SignType) : ℝ) =
      H.ofLp (π x) * (stdVec j (π x) : ℝ) := fun x => by
    rw [SignType.coe_mul]; linear_combination (H.ofLp (π x) * (stdVec j (π x) : ℝ)) * sq (ε x)
  simp only [e]
  rw [Equiv.sum_comp π (fun i => H.ofLp i * (stdVec j i : ℝ)),
    show Finset.Iic j = Finset.univ.filter (· ≤ j) by ext; simp, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ≤ j <;> simp [stdVec, h]

/- English proof (translation)
Introduce `D V Φ L a hg P hP m hm`. Take `⟨h, hh⟩` from `GlobalTheory.T.levi_log_modulus_vector D V Φ P hP m hm`. Use `⟨h, fun Q hQ x T => ?_⟩` and prove the remaining obligations. Take `⟨hQp, hQa, -⟩` from `mem_parP.1 hQ`. Take `⟨π, ε, w, hw, hsub, hY⟩` from `exists_Yfam_eq (Φ := Φ) (K := levelAll D.sp.cm.sig V.gram L a) hQp`.

Rewrite using `[hY, hY, ← sub_eq_iff_eq_add', ← map_sub, ← sub_eq_zero, ← map_sub, pr, Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]`. Introduce `v hv`. Use `Submodule.span_induction (p := fun v _ => inner ℝ v _ = (0:ℝ)) ?_ (by simp) (fun x y _ _ hx hy => by rw [inner_add_left, hx, hy, add_zero]) (fun c x _ hx => by rw [inner_smul_left, hx, mul_zero]) hv` and prove the remaining obligations. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.1 (hsub hu)`.

Take `⟨j, -, rfl⟩` from `Finset.mem_image.1 hs`. Establish `hvu : vec (invSV π ε (stdVec j)) ∈ aP P` using `hQa ▸ Submodule.subset_span ⟨_, hu, rfl⟩`. Establish `hmu : m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j)))`. Use `GlobalTheory.T.levi_monotone_in_parabolic D V Φ (AF D.host.F) P hP _ hvu hm` as an intermediate fact. Establish `h2 : Φ.levi D.sp.cm (AF D.host.F) {invSV π ε (stdVec j)} ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j)))`.

Unfold `WittFrame.levi`. Conclude with `(iInf₂_le (invSV π ε (stdVec j)) (Finset.mem_singleton_self _)).trans inf_le_left`. Conclude with `h2 this`. Take `⟨hg1, hg2⟩` from `GlobalTheory.T.weyl_conjugate_parabolic_log_modulus D V Φ π ε w hw j m hmu`. Establish `e1` using `sum_H0_parabolic_mul D V Φ L a hg j _ (rat V w * x) hg1`.

Establish `e2 : rat V w * (m * x) = rat V w * m * (rat V w)⁻¹ * (rat V w * x)` using `by group`. Simplify using `only [Ys, inner_sub_right, inner_vector_inverse_levi_shift, hh _ hvu, e2, PiLp.sub_apply, Finset.sum_sub_distrib] at e1 ⊢`. Rewrite using `[e1, hg2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem yfam_mul_levi : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (L : _) (a : _), Φ.IsGood D.sp.cm L a → ∀ P, IsPar P → ∀ m ∈ Φ.levi D.sp.cm (AF D.host.F) P, ∃ h : A0 (wittIndex V), ∀ Q ∈ parP (aP P) ∅, ∀ x Tr, Yfam Φ (levelAll D.sp.cm.sig V.gram L a) (m * x) Tr Q = Yfam Φ (levelAll D.sp.cm.sig V.gram L a) x Tr Q + pr Q h := by
  intro D V Φ L a hg P hP m hm
  obtain ⟨h, hh⟩ := GlobalTheory.T.levi_log_modulus_vector D V Φ P hP m hm
  refine ⟨h, fun Q hQ x T => ?_⟩
  obtain ⟨hQp, hQa, -⟩ := mem_parP.1 hQ
  obtain ⟨π, ε, w, hw, hsub, hY⟩ := exists_Yfam_eq (Φ := Φ) (K := levelAll D.sp.cm.sig V.gram L a) hQp
  rw [hY, hY, ← sub_eq_iff_eq_add', ← map_sub, ← sub_eq_zero, ← map_sub, pr, Submodule.starProjection_apply_eq_zero_iff,
    Submodule.mem_orthogonal]
  intro v hv
  refine Submodule.span_induction (p := fun v _ => inner ℝ v _ = (0:ℝ)) ?_ (by simp)
    (fun x y _ _ hx hy => by rw [inner_add_left, hx, hy, add_zero])
    (fun c x _ hx => by rw [inner_smul_left, hx, mul_zero]) hv
  rintro _ ⟨u, hu, rfl⟩
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 (hsub hu)
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hs
  have hvu : vec (invSV π ε (stdVec j)) ∈ aP P := hQa ▸ Submodule.subset_span ⟨_, hu, rfl⟩
  have hmu : m ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) := by
    have := GlobalTheory.T.levi_monotone_in_parabolic D V Φ (AF D.host.F) P hP _ hvu hm
    have h2 : Φ.levi D.sp.cm (AF D.host.F) {invSV π ε (stdVec j)} ≤
        GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.parab D.sp.cm V (AF D.host.F) (Φ.sub (invSV π ε (stdVec j))) := by
      unfold WittFrame.levi
      exact (iInf₂_le (invSV π ε (stdVec j)) (Finset.mem_singleton_self _)).trans inf_le_left
    exact h2 this
  obtain ⟨hg1, hg2⟩ := GlobalTheory.T.weyl_conjugate_parabolic_log_modulus D V Φ π ε w hw j m hmu
  have e1 := sum_H0_parabolic_mul D V Φ L a hg j _ (rat V w * x) hg1
  have e2 : rat V w * (m * x) = rat V w * m * (rat V w)⁻¹ * (rat V w * x) := by group
  simp only [Ys, inner_sub_right, inner_vector_inverse_levi_shift, hh _ hvu, e2, PiLp.sub_apply, Finset.sum_sub_distrib] at e1 ⊢
  rw [e1, hg2]
  ring

end GlobalTheory.LeviShift

end
