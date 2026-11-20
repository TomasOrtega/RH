import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.VaceigenDual
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSubConjNotMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat

noncomputable section

namespace PositivityTheory.ThKG.Loc.Iwa

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.ThK PositivityTheory.ThKH.Iwas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {v : Pl F}

/- English proof (translation)
Introduce `w hw` and use `by haveI := hB.unram haveI := w.isPrime exact w.asIdeal.ramificationIdx_eq_one (𝓞 F)`.
-/
theorem unramAt {B : Base F E} (hB : B.IsGood σ) (v : Pl F) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v := fun w hw => by
  haveI := hB.unram
  haveI := w.isPrime
  exact w.asIdeal.ramificationIdx_eq_one (𝓞 F)

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by simp only [RingHom.coe_coe]; ring`.
-/
theorem hE_smul (ξ : E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : hE σ (ξ • Jᵀ) x y = ξ * form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by simp only [RingHom.coe_coe]; ring

/- English proof (translation)
Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `(HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t).trans_le h`.
-/
theorem mem_int {t : F} (h : v.valuation F t ≤ 1) : algebraMap F (Fv F v) t ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t).trans_le h

/- English proof (translation)
Use `le_antisymm (fun y hy => ?_) ?_` and prove the remaining obligations. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨a, ha, y, hy, rfl⟩` from `hz`. Take `⟨k, S, Φ, e1, hS, hΦ⟩` from `SelfDual.exists_frame L hL`.

Establish `: (fun i => inclR (Fv F v) (y i)) ∈ dualLoc σ J₀ L v` using `(SelfDual.mem_dualLoc_iff_of_frame e1 hS hΦ v _).2 fun j => by`. Rewrite using `[SelfDual.map_mulVec_inclR, ← SelfDual.hform_col]`. Conclude with `h1 y hy _ (hS j)`. Establish `h3` using `(dualLoc σ J₀ L v).smul_mem ⟨_, tmul_mem_intLoc ha (1 : 𝓞 E)⟩ this`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `_ = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] y i)`. Simplify using the standard rewrite rules. Consider the case `zero => exact zero_mem _`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`.

Consider the case `neg a _ ha => exact neg_mem ha`. Rewrite using `[← SelfDual.latLoc_dualGlob hd hL]`. Introduce `y hy`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem z hz`.

Take `⟨a, ha, y, hy, rfl⟩` from `hz`. Establish `hv1 : v.valuation F (s : F) = 1` using `(HeightOneSpectrum.valuation_eq_one_iff_notMem v (K := F)).2 hs`. Establish `hs0 : (s : F) ≠ 0` using `fun h => by simp [h] at hv1`. Establish `hi : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F` using `mem_int (by rw [map_inv₀, hv1, inv_one])`. Establish `h3` using `tmul_mem_latLoc (mul_mem ha hi) (h2 y hy)`.

Use `h3 using 2 with i` and compare the differences between its conclusion and the goal. Rewrite using `[Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_comm a, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hs0, map_one, one_mul]`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b _ _ ha hb => exact add_mem ha hb`. Consider the case `neg a _ ha => exact neg_mem ha`.
-/
theorem selfDual_of {J₀ : Matrix (Fin n) (Fin n) E} (hd : J₀.det ≠ 0) {L : Submodule (𝓞 E) (Fin n → E)}
    (hL : L.IsLattice E) (h1 : ∀ y ∈ L, ∀ x ∈ L, inclR (Fv F v) (hE σ J₀ x y) ∈ intLoc F E v) {s : 𝓞 F} (hs : s ∉ v.asIdeal)
    (h2 : ∀ y ∈ SelfDual.dualGlob σ J₀ L, algebraMap F E s • y ∈ L) : IsSelfDualAt σ J₀ L v := by
  refine le_antisymm (fun y hy => ?_) ?_
  · induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hz
      obtain ⟨k, S, Φ, e1, hS, hΦ⟩ := SelfDual.exists_frame L hL
      have : (fun i => inclR (Fv F v) (y i)) ∈ dualLoc σ J₀ L v := (SelfDual.mem_dualLoc_iff_of_frame e1 hS hΦ v _).2 fun j => by
        rw [SelfDual.map_mulVec_inclR, ← SelfDual.hform_col]
        exact h1 y hy _ (hS j)
      have h3 := (dualLoc σ J₀ L v).smul_mem ⟨_, tmul_mem_intLoc ha (1 : 𝓞 E)⟩ this
      convert h3 using 1
      funext i
      change _ = (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] y i)
      simp
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha
  · rw [← SelfDual.latLoc_dualGlob hd hL]
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hz
      have hv1 : v.valuation F (s : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem v (K := F)).2 hs
      have hs0 : (s : F) ≠ 0 := fun h => by simp [h] at hv1
      have hi : algebraMap F (Fv F v) (s : F)⁻¹ ∈ v.adicCompletionIntegers F := mem_int (by rw [map_inv₀, hv1, inv_one])
      have h3 := tmul_mem_latLoc (mul_mem ha hi) (h2 y hy)
      convert h3 using 2 with i
      rw [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
        mul_comm a, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hs0, map_one, one_mul]
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | neg a _ ha => exact neg_mem ha

/- English proof (translation)
Introduce `a` and use `by have := hz (algebraMap (𝓞 F) (𝓞 E) a * o) rw [← Algebra.trace_trace (S := F)] at this convert this using 2 rw [← smul_eq_mul, ← map_smul, Algebra.smul_def] congr 1 push_cast rw [mul_assoc] rfl`.
-/
theorem inD_trace {z : E} (hz : InD z) (o : 𝓞 E) : InD (Algebra.trace F E (o * z)) := fun a => by
  have := hz (algebraMap (𝓞 F) (𝓞 E) a * o)
  rw [← Algebra.trace_trace (S := F)] at this
  convert this using 2
  rw [← smul_eq_mul, ← map_smul, Algebra.smul_def]
  congr 1
  push_cast
  rw [mul_assoc]
  rfl

/- English proof (translation)
Introduce `a` and use `by rw [← Algebra.trace_trace (S := F), show (a : E) * (algebraMap F E δ * o) = δ • ((a * o : 𝓞 E) : E) by rw [Algebra.smul_def]; push_cast; ring, map_smul, smul_eq_mul, mul_comm] have hi : IsIntegral ℤ (Algebra.trace F E ((a * o : 𝓞 E) : E)) := Algebra.isIntegral_trace (a * o).is …`.
-/
theorem inD_mul {δ : F} (hδ : InD δ) (o : 𝓞 E) : InD (algebraMap F E δ * o) := fun a => by
  rw [← Algebra.trace_trace (S := F), show (a : E) * (algebraMap F E δ * o) = δ • ((a * o : 𝓞 E) : E) by
    rw [Algebra.smul_def]; push_cast; ring, map_smul, smul_eq_mul, mul_comm]
  have hi : IsIntegral ℤ (Algebra.trace F E ((a * o : 𝓞 E) : E)) := Algebra.isIntegral_trace (a * o).isIntegral_coe
  exact hδ ⟨_, hi⟩

/- English proof (translation)
Establish `hdet : ∀ ξ : E, ξ ≠ 0 → (ξ • Y.Jᵀ).det ≠ 0` using `fun ξ h => by`. Rewrite using `[Matrix.det_smul, Matrix.det_transpose]`. Conclude with `mul_ne_zero (pow_ne_zero _ h) (hY.elim (fun h => (Vac.herm_det h).ne_zero) fun h => (Vac.skew_det h).ne_zero)`. Break down `hY with hY | hY` into its components or cases. Use `⟨1, one_ne_zero, ⟨fun i j => by simp [hY.herm], hdet 1 one_ne_zero⟩, selfDual_of (hdet 1 one_ne_zero) hY.lat (fun y hy x hx => SelfDual.inclR_mem_intLoc v ?_) (s := 1) ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top) fun y hy => ?_⟩` and prove the remaining obligations.

Rewrite using `[hE_smul, one_mul]`. Conclude with `⟨⟨_, (hY.dual y).1 hy x hx⟩, rfl⟩`. Simplify using `only [OneMemClass.coe_one, map_one, one_smul]`. Use `(hY.dual y).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨o, ho⟩` from `hy x hx`.

Rewrite `ho` using `[hE_smul, one_mul]`. Rewrite using `[← ho]`. Conclude with `o.isIntegral_coe`. Take `⟨t, dd, s₀, hd, hs, hsv⟩` from `GlobalTheory.UnramConjUnit.exists_sub_conj_notMem hB.cm v (unramAt hB v)`. Take `⟨δ, hδ0, hδ, hmax⟩` from `exists_gen (E := F) v`.

Establish `hσ` using `Vac.sigma_sigma hB.cm`. Establish `hdd : (dd : E) ≠ 0` using `fun h => hsv (by`. Establish `: (s₀ : F) = 0` using `(algebraMap F E).injective (by rw [hs, h, mul_zero, map_zero])`. Rewrite using `[show s₀ = 0 from Subtype.ext this]`. Conclude with `zero_mem _)`.

Establish `hδE : algebraMap F E δ ≠ 0` using `(map_ne_zero _).2 hδ0`. Establish `hξ : (dd : E) / algebraMap F E δ ≠ 0` using `div_ne_zero hdd hδE`. Establish `hv0 : v.valuation F δ ≠ 0` using `(Valuation.ne_zero_iff _).2 hδ0`. Use `⟨_, hξ, ⟨fun i j => ?_, hdet _ hξ⟩, selfDual_of (hdet _ hξ) hY.lat (fun y hy x hx => ?_) hsv fun y hy => ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, map_div₀, AlgHom.commutes, hY.skew, hd, map_sub, hσ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hE_smul]`. Establish `hz : InD (form σ Y.J y x)` using `(hY.dual y).1 hy x hx`. Generalize the expression as in `form σ Y.J y x = z at hz`. Establish `a1` using `hmax _ (inD_trace hz t)`.

Establish `a2` using `hmax _ (inD_trace hz 1)`. Establish `e : (dd : E) / algebraMap F E δ * z = (Algebra.trace F E (t * z) / δ) • ((1 : 𝓞 E) : E) - (Algebra.trace F E ((1 : 𝓞 E) * z) / δ) • ((RingOfIntegers.mapRingHom (σ : E →+* E) t : 𝓞 E) : E)`. Establish `: ((RingOfIntegers.mapRingHom (σ : E →+* E) t : 𝓞 E) : E) = σ t` using `rfl`. Establish `o1 : ((1 : 𝓞 E) : E) = 1` using `rfl`. Simplify using `only [Algebra.smul_def, map_div₀, GlobalTheory.SelfDualLatticeCompare.trace_field hB.cm, this, hd, map_mul, o1, one_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ (c : F) (o : 𝓞 E), v.valuation F c ≤ v.valuation F δ → inclR (Fv F v) ((c / δ) • (o : E)) ∈ intLoc F E v` using `fun c o hc => by`. Use `tmul_mem_intLoc (mem_int (v := v) (t := c / δ) (by rw [map_div₀]; exact div_le_one_of_le₀ hc zero_le)) o` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Express the relevant statement in the definitionally equal form `(1 : Fv F v) ⊗ₜ[F] ((c / δ) • (o : E)) = _`. Rewrite using `[TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]`. Rewrite using `[e, map_sub]`. Conclude with `sub_mem (key _ _ a1) (key _ _ a2)`. Use `(hY.dual _).2 fun x hx => ?_` and prove the remaining obligations.

Take `⟨o, ho⟩` from `hy x hx`. Rewrite `ho` using `[hE_smul]`. Establish `e : form σ Y.J (algebraMap F E s₀ • y) x = algebraMap F E δ * ((dd * o : 𝓞 E) : E)`. Establish `: (o : E) = (dd : E) / algebraMap F E δ * form σ Y.J y x` using `ho`. Establish `o2 : ((dd * o : 𝓞 E) : E) = (dd : E) * (o : E)` using `rfl`.

Rewrite using `[form, smul_dotProduct, smul_eq_mul, hs, o2, this, form]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Conclude with `inD_mul hδ _`.
-/
theorem exists_selfDual {B : Base F E} (hB : B.IsGood σ) {Y : Spc F E n} {r s : ℕ} (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s)
    (v : Pl F) : ∃ ξ : E, ξ ≠ 0 ∧ IsHermND σ (ξ • Y.Jᵀ) ∧ IsSelfDualAt σ (ξ • Y.Jᵀ) Y.L v := by
  have hdet : ∀ ξ : E, ξ ≠ 0 → (ξ • Y.Jᵀ).det ≠ 0 := fun ξ h => by
    rw [Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ h) (hY.elim (fun h => (Vac.herm_det h).ne_zero) fun h => (Vac.skew_det h).ne_zero)
  rcases hY with hY | hY
  · refine ⟨1, one_ne_zero, ⟨fun i j => by simp [hY.herm], hdet 1 one_ne_zero⟩,
      selfDual_of (hdet 1 one_ne_zero) hY.lat (fun y hy x hx => SelfDual.inclR_mem_intLoc v ?_) (s := 1)
        ((Ideal.ne_top_iff_one _).1 v.isPrime.ne_top) fun y hy => ?_⟩
    · rw [hE_smul, one_mul]; exact ⟨⟨_, (hY.dual y).1 hy x hx⟩, rfl⟩
    · simp only [OneMemClass.coe_one, map_one, one_smul]
      refine (hY.dual y).2 fun x hx => ?_
      obtain ⟨o, ho⟩ := hy x hx
      rw [hE_smul, one_mul] at ho
      rw [← ho]; exact o.isIntegral_coe
  · obtain ⟨t, dd, s₀, hd, hs, hsv⟩ := GlobalTheory.UnramConjUnit.exists_sub_conj_notMem hB.cm v (unramAt hB v)
    obtain ⟨δ, hδ0, hδ, hmax⟩ := exists_gen (E := F) v
    have hσ := Vac.sigma_sigma hB.cm
    have hdd : (dd : E) ≠ 0 := fun h => hsv (by
      have : (s₀ : F) = 0 := (algebraMap F E).injective (by rw [hs, h, mul_zero, map_zero])
      rw [show s₀ = 0 from Subtype.ext this]; exact zero_mem _)
    have hδE : algebraMap F E δ ≠ 0 := (map_ne_zero _).2 hδ0
    have hξ : (dd : E) / algebraMap F E δ ≠ 0 := div_ne_zero hdd hδE
    have hv0 : v.valuation F δ ≠ 0 := (Valuation.ne_zero_iff _).2 hδ0
    refine ⟨_, hξ, ⟨fun i j => ?_, hdet _ hξ⟩, selfDual_of (hdet _ hξ) hY.lat (fun y hy x hx => ?_) hsv fun y hy => ?_⟩
    · simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, map_div₀, AlgHom.commutes, hY.skew, hd,
        map_sub, hσ]
      ring
    · rw [hE_smul]
      have hz : InD (form σ Y.J y x) := (hY.dual y).1 hy x hx
      generalize form σ Y.J y x = z at hz
      have a1 := hmax _ (inD_trace hz t)
      have a2 := hmax _ (inD_trace hz 1)
      have e : (dd : E) / algebraMap F E δ * z = (Algebra.trace F E (t * z) / δ) • ((1 : 𝓞 E) : E) -
          (Algebra.trace F E ((1 : 𝓞 E) * z) / δ) • ((RingOfIntegers.mapRingHom (σ : E →+* E) t : 𝓞 E) : E) := by
        have : ((RingOfIntegers.mapRingHom (σ : E →+* E) t : 𝓞 E) : E) = σ t := rfl
        have o1 : ((1 : 𝓞 E) : E) = 1 := rfl
        simp only [Algebra.smul_def, map_div₀, GlobalTheory.SelfDualLatticeCompare.trace_field hB.cm, this, hd, map_mul, o1, one_mul]
        field_simp
        ring
      have key : ∀ (c : F) (o : 𝓞 E), v.valuation F c ≤ v.valuation F δ →
          inclR (Fv F v) ((c / δ) • (o : E)) ∈ intLoc F E v := fun c o hc => by
        have := tmul_mem_intLoc (mem_int (v := v) (t := c / δ) (by rw [map_div₀]; exact div_le_one_of_le₀ hc zero_le)) o
        convert this using 1
        change (1 : Fv F v) ⊗ₜ[F] ((c / δ) • (o : E)) = _
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]
      rw [e, map_sub]
      exact sub_mem (key _ _ a1) (key _ _ a2)
    · refine (hY.dual _).2 fun x hx => ?_
      obtain ⟨o, ho⟩ := hy x hx
      rw [hE_smul] at ho
      have e : form σ Y.J (algebraMap F E s₀ • y) x = algebraMap F E δ * ((dd * o : 𝓞 E) : E) := by
        have : (o : E) = (dd : E) / algebraMap F E δ * form σ Y.J y x := ho
        have o2 : ((dd * o : 𝓞 E) : E) = (dd : E) * (o : E) := rfl
        rw [form, smul_dotProduct, smul_eq_mul, hs, o2, this, form]
        field_simp
      rw [e]
      exact inD_mul hδ _

end PositivityTheory.ThKG.Loc.Iwa

end
