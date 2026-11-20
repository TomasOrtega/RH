import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemEig
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.RatProductFormulaStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsOfNonzeroAdelicStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.ProductFormulaLogNormsStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogNormsExtDegreeAdelicStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicLogIdealMaxElementStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealMulSpanMapStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SumLogIdealEqLogAbsNormStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LogIdealSupportFiniteStatement
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.PadicEmbeddingDiscreteValuationRingStatement

noncomputable section

namespace LevelTowerAlt

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GroundTheory.Heights₂.Heights

section Local

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `hj'inj : Function.Injective (j.comp (algebraMap (𝓞 L) L))` using `j.injective.comp (IsFractionRing.injective (𝓞 L) L)`. Take `⟨V, -, hV, hVO, -⟩` from `GlobalTheory.T.padic_embedding_discrete_valuation_ring L p j`. Establish `hle1 : ∀ r : 𝓞 L, ‖(j.comp (algebraMap (𝓞 L) L)) r‖ ≤ 1` using `fun r => (hV _).2 (hVO r)`. Take `⟨a, haI, ha0, hamax, hlog⟩` from `GlobalTheory.T.padic_logIdeal_max_element L p _ (detIdeal E) hj'inj hD`. Establish `hapos : 0 < ‖(j.comp (algebraMap (𝓞 L) L)) a‖` using `norm_pos_iff.2 (fun h => ha0 (hj'inj (by rw [h, map_zero])))`.

Choose the witnesses or unpack the hypotheses as in `⟨v, hvE, hv⟩ : ∃ v : Fin n → Fin n → 𝓞 L, (∀ i, v i ∈ E) ∧ ‖(j.comp (algebraMap (𝓞 L) L)) a‖ ≤ ‖(j.comp (algebraMap (𝓞 L) L)) (Matrix.of v).det‖ := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hall : ∀ x ∈ detIdeal E, ‖(j.comp (algebraMap (𝓞 L) L)) x‖ < ‖(j.comp (algebraMap (𝓞 L) L)) a‖`. Introduce `x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`. Conclude with `hcon v hv`. Consider the case `zero => simpa using hapos`.

Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)`. Consider the case `smul r x _ hx`. Rewrite using `[smul_eq_mul, map_mul, norm_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hle1 r)) hx`. Conclude with `lt_irrefl _ (hall a haI)`. Establish `hdI : (Matrix.of v).det ∈ detIdeal E` using `det_mem_detIdeal E v hvE`. Establish `hdeq : ‖(j.comp (algebraMap (𝓞 L) L)) (Matrix.of v).det‖ = ‖(j.comp (algebraMap (𝓞 L) L)) a‖` using `le_antisymm (hamax _ hdI) hv`. Establish `hd0 : (Matrix.of v).det ≠ 0`.

Introduce `h`. Rewrite `hdeq` using `[h, map_zero, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨J, hJ⟩` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hdI)`. Establish `hspan0 : Ideal.span {(Matrix.of v).det} ≠ ⊥`.

Rewrite using `[Ne, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Establish `hJ0 : J ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hJ` using `[Ideal.mul_bot]`. Conclude with `hspan0 hJ`.

Take `⟨hmul, hsing, -⟩` from `GlobalTheory.T.log_ideal_mul_span_map L p _ hj'inj`. Establish `hJlog : logIdeal (j.comp (algebraMap (𝓞 L) L)) J = 0`. Use `hmul _ J hD hJ0` as an intermediate fact. Rewrite `this` using `[← hJ, hsing, hdeq, hlog]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨u, huJ, hu0, -, hulog⟩` from `GlobalTheory.T.padic_logIdeal_max_element L p _ J hj'inj hJ0`. Establish `hu1 : ‖(j.comp (algebraMap (𝓞 L) L)) u‖ = 1`. Establish `hpos : 0 < ‖(j.comp (algebraMap (𝓞 L) L)) u‖` using `norm_pos_iff.2 (fun h => hu0 (hj'inj (by rw [h, map_zero])))`. Rewrite `hulog` using `[hJlog]`. Rewrite using `[← Real.exp_log hpos, ← hulog, Real.exp_zero]`.

Use `⟨v, u, hvE, hd0, ?_, hu1, ?_⟩` and prove the remaining obligations. Rewrite using `[hlog, ← hdeq]`. Both sides reduce to the same expression. Introduce `w hw`. Establish `hc : ∀ k, u * (Matrix.of (Function.update v k w)).det ∈ Ideal.span {(Matrix.of v).det}`.

Introduce `k`. Rewrite using `[hJ, mul_comm u]`. Use `Ideal.mul_mem_mul (det_mem_detIdeal E _ fun i => ?_) huJ` and prove the remaining obligations. Distinguish the cases in `h : i = k`. Substitute `h` using the available equality.

Simplify using `using hw`. Simplify `hvE i` using `[h]`. Use `choose t ht using fun k => Ideal.mem_span_singleton'.1 (hc k)`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `hcr` using `Matrix.mulVec_cramer (Matrix.transpose (Matrix.of v)) w`.

Establish `hcr_apply : ∀ k, Matrix.cramer (Matrix.transpose (Matrix.of v)) w k = (Matrix.of (Function.update v k w)).det`. Introduce `k`. Rewrite using `[Matrix.cramer_apply, Matrix.updateCol_transpose, Matrix.det_transpose]`. Both sides reduce to the same expression. Apply `smul_right_injective (Fin n → 𝓞 L) hd0` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Establish `hi` using `congrFun hcr i`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, hcr_apply, Matrix.det_transpose, Pi.smul_apply, smul_eq_mul] at hi`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]`. Rewrite using `[Finset.mul_sum]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Take the linear combination `(-(v k i)) * ht k`.
-/
theorem exists_max_det {n : ℕ} (E : Submodule (𝓞 L) (Fin n → 𝓞 L)) (hD : detIdeal E ≠ ⊥) (p : Nat.Primes)
    (j : L →+* ℂ_[p]) :
    ∃ (v : Fin n → Fin n → 𝓞 L) (u : 𝓞 L), (∀ i, v i ∈ E) ∧ (Matrix.of v).det ≠ 0 ∧
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E) = Real.log ‖j (((Matrix.of v).det : 𝓞 L) : L)‖ ∧
      ‖j (u : L)‖ = 1 ∧ ∀ w ∈ E, ∃ t : Fin n → 𝓞 L, u • w = ∑ k, t k • v k := by
  classical
  have hj'inj : Function.Injective (j.comp (algebraMap (𝓞 L) L)) :=
    j.injective.comp (IsFractionRing.injective (𝓞 L) L)
  obtain ⟨V, -, hV, hVO, -⟩ := GlobalTheory.T.padic_embedding_discrete_valuation_ring L p j
  have hle1 : ∀ r : 𝓞 L, ‖(j.comp (algebraMap (𝓞 L) L)) r‖ ≤ 1 := fun r => (hV _).2 (hVO r)
  obtain ⟨a, haI, ha0, hamax, hlog⟩ := GlobalTheory.T.padic_logIdeal_max_element L p _ (detIdeal E) hj'inj hD
  have hapos : 0 < ‖(j.comp (algebraMap (𝓞 L) L)) a‖ :=
    norm_pos_iff.2 (fun h => ha0 (hj'inj (by rw [h, map_zero])))
  obtain ⟨v, hvE, hv⟩ : ∃ v : Fin n → Fin n → 𝓞 L, (∀ i, v i ∈ E) ∧
      ‖(j.comp (algebraMap (𝓞 L) L)) a‖ ≤ ‖(j.comp (algebraMap (𝓞 L) L)) (Matrix.of v).det‖ := by
    by_contra hcon
    push_neg at hcon
    have hall : ∀ x ∈ detIdeal E, ‖(j.comp (algebraMap (𝓞 L) L)) x‖ < ‖(j.comp (algebraMap (𝓞 L) L)) a‖ := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        exact hcon v hv
      | zero => simpa using hapos
      | add x y _ _ hx hy =>
        rw [map_add]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
      | smul r x _ hx =>
        rw [smul_eq_mul, map_mul, norm_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (hle1 r)) hx
    exact lt_irrefl _ (hall a haI)
  have hdI : (Matrix.of v).det ∈ detIdeal E := det_mem_detIdeal E v hvE
  have hdeq : ‖(j.comp (algebraMap (𝓞 L) L)) (Matrix.of v).det‖ = ‖(j.comp (algebraMap (𝓞 L) L)) a‖ :=
    le_antisymm (hamax _ hdI) hv
  have hd0 : (Matrix.of v).det ≠ 0 := by
    intro h
    rw [h, map_zero, norm_zero] at hdeq
    linarith
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hdI)
  have hspan0 : Ideal.span {(Matrix.of v).det} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at hJ
    exact hspan0 hJ
  obtain ⟨hmul, hsing, -⟩ := GlobalTheory.T.log_ideal_mul_span_map L p _ hj'inj
  have hJlog : logIdeal (j.comp (algebraMap (𝓞 L) L)) J = 0 := by
    have := hmul _ J hD hJ0
    rw [← hJ, hsing, hdeq, hlog] at this
    linarith
  obtain ⟨u, huJ, hu0, -, hulog⟩ := GlobalTheory.T.padic_logIdeal_max_element L p _ J hj'inj hJ0
  have hu1 : ‖(j.comp (algebraMap (𝓞 L) L)) u‖ = 1 := by
    have hpos : 0 < ‖(j.comp (algebraMap (𝓞 L) L)) u‖ :=
      norm_pos_iff.2 (fun h => hu0 (hj'inj (by rw [h, map_zero])))
    rw [hJlog] at hulog
    rw [← Real.exp_log hpos, ← hulog, Real.exp_zero]
  refine ⟨v, u, hvE, hd0, ?_, hu1, ?_⟩
  · rw [hlog, ← hdeq]
    rfl
  · intro w hw
    have hc : ∀ k, u * (Matrix.of (Function.update v k w)).det ∈ Ideal.span {(Matrix.of v).det} := by
      intro k
      rw [hJ, mul_comm u]
      refine Ideal.mul_mem_mul (det_mem_detIdeal E _ fun i => ?_) huJ
      by_cases h : i = k
      · subst h
        simpa using hw
      · simpa [h] using hvE i
    choose t ht using fun k => Ideal.mem_span_singleton'.1 (hc k)
    refine ⟨t, ?_⟩
    have hcr := Matrix.mulVec_cramer (Matrix.transpose (Matrix.of v)) w
    have hcr_apply : ∀ k, Matrix.cramer (Matrix.transpose (Matrix.of v)) w k = (Matrix.of (Function.update v k w)).det := by
      intro k
      rw [Matrix.cramer_apply, Matrix.updateCol_transpose, Matrix.det_transpose]
      rfl
    apply smul_right_injective (Fin n → 𝓞 L) hd0
    funext i
    have hi := congrFun hcr i
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, hcr_apply,
      Matrix.det_transpose, Pi.smul_apply, smul_eq_mul] at hi
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [Finset.mul_sum]
    calc (Matrix.of v).det * (u * w i) = u * ((Matrix.of v).det * w i) := by ring
      _ = u * ∑ k, v k i * (Matrix.of (Function.update v k w)).det := by rw [hi]
      _ = ∑ k, (Matrix.of v).det * (t k * v k i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        linear_combination (-(v k i)) * ht k

/- English proof (translation)
Use `set Φ : (Fin n → 𝓞 L) →ₗ[𝓞 L] M := Fintype.linearCombination (𝓞 L) x with hΦ`. Establish `hΦa : ∀ w, Φ w = ∑ k, w k • x k` using `fun w => Fintype.linearCombination_apply _ _ _`. Establish `hΦi : Function.Injective Φ`. Introduce `a b h`. Establish `h'` using `Fintype.linearIndependent_iff.1 hli (a - b) (by`.

Rewrite using `[← hΦa, map_sub, h, sub_self])`. Use function extensionality and compare the values at `i`. Conclude with `sub_eq_zero.1 (h' i)`. Establish `hrange : Submodule.span (𝓞 L) (Set.range x) = LinearMap.range Φ`. Rewrite using `[hΦ, Fintype.range_linearCombination]`.

Use `set ψ : M →ₗ[𝓞 L] M := c • LinearMap.id with hψ`. Establish `hψa : ∀ z, ψ z = c • z` using `fun z => rfl`. Establish `hψi : Function.Injective ψ`. Introduce `a b h`. Rewrite `h` using `[hψa, hψa]`.

Conclude with `smul_right_injective M hc h`. Use `set E : Submodule (𝓞 L) (Fin n → 𝓞 L) := (F.map ψ).comap Φ with hE`. Establish `hmem : ∀ w, w ∈ E ↔ ∃ z ∈ F, c • z = ∑ k, w k • x k`. Introduce `w`. Simplify using `only [hE, Submodule.mem_comap, Submodule.mem_map, hψa, hΦa]`.

Use `set A : Submodule (𝓞 L) (Fin n → 𝓞 L) := LinearMap.range (c • (1 : Matrix (Fin n) (Fin n) (𝓞 L))).mulVecLin with hA`. Establish `hAmem : ∀ w, w ∈ A ↔ ∃ v, c • v = w`. Introduce `w`. Simplify using `[hA, Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.one_mulVec]`. Establish `hAE : A ≤ E`.

Introduce `w hw`. Take `⟨v, rfl⟩` from `(hAmem w).1 hw`. Rewrite using `[hmem]`. Use `⟨Φ v, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hΦa]`.

Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hx k)`. Rewrite using `[hΦa, Finset.smul_sum]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, smul_smul]`. Establish `hdet : detIdeal E ≠ ⊥`. Introduce `hb`.

Establish `h1` using `det_mem_detIdeal E (fun i => c • Pi.single i (1 : 𝓞 L)) (fun i => hAE ((hAmem _).2 ⟨_, rfl⟩))`. Rewrite `h1` using `[hb, Ideal.mem_bot]`. Establish `e1 : Matrix.of (fun i => c • Pi.single i (1 : 𝓞 L)) = c • (1 : Matrix (Fin n) (Fin n) (𝓞 L))`. Use extensionality with `i j`. Simplify using `[Matrix.one_apply, Pi.single_apply, eq_comm]`.

Rewrite `h1` using `[e1, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]`. Conclude with `pow_ne_zero n hc h1`. Use `⟨E, hmem, hdet, ?_⟩` and prove the remaining obligations. Establish `iA : A.toAddSubgroup.index = Ideal.absNorm (Ideal.span {c ^ n})`. Rewrite using `[Ideal.absNorm_span_singleton]`.

Use `card_quotient_mulVecLin (K := L) (c • (1 : Matrix (Fin n) (Fin n) (𝓞 L))) (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; exact pow_ne_zero n hc)` as an intermediate fact. Rewrite `this` using `[Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]`. Conclude with `this`. Establish `iE : E.toAddSubgroup.index = Ideal.absNorm (detIdeal E)` using `card_quotient_eq_absNorm_detIdeal n E`. Establish `m1 : A.toAddSubgroup.map Φ.toAddMonoidHom = (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.map ψ.toAddMonoidHom`.

Use extensionality with `z`. Simplify using `only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Take `⟨v, rfl⟩` from `(hAmem w).1 hw`.

Conclude with `⟨Φ v, by rw [hrange]; exact ⟨v, rfl⟩, by rw [hψa, map_smul]⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite `hy` using `[hrange]`. Take `⟨v, rfl⟩` from `hy`. Conclude with `⟨c • v, (hAmem _).2 ⟨v, rfl⟩, by rw [hψa, map_smul]⟩`.

Establish `m2 : E.toAddSubgroup.map Φ.toAddMonoidHom = F.toAddSubgroup.map ψ.toAddMonoidHom`. Use extensionality with `z`. Simplify using `only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`.

Take `⟨y, hy, he⟩` from `Submodule.mem_map.1 (Submodule.mem_comap.1 hw)`. Conclude with `⟨y, hy, he⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Establish `h2` using `hF y hy`. Rewrite `h2` using `[hrange]`.

Take `⟨w, hw⟩` from `h2`. Use `⟨w, ?_, by rw [hw, hψa]⟩` and prove the remaining obligations. Conclude with `Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨y, hy, by rw [hw, hψa]⟩)`. Establish `hrel : A.toAddSubgroup.relIndex E.toAddSubgroup = (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup`. Rewrite using `[← AddSubgroup.relIndex_map_map_of_injective (f := Φ.toAddMonoidHom) _ _ hΦi, m1, m2, AddSubgroup.relIndex_map_map_of_injective _ _ hψi]`.

Rewrite using `[← iA, ← AddSubgroup.relIndex_mul_index (show A.toAddSubgroup ≤ E.toAddSubgroup from hAE), hrel, iE]`.
-/
theorem exists_coord_lattice {M : Type} [AddCommGroup M] [Module (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M]
    (F : Submodule (𝓞 L) M) {n : ℕ} (x : Fin n → M) (hx : ∀ i, x i ∈ F) (hli : LinearIndependent (𝓞 L) x)
    (c : 𝓞 L) (hc : c ≠ 0) (hF : ∀ z ∈ F, c • z ∈ Submodule.span (𝓞 L) (Set.range x)) :
    ∃ E : Submodule (𝓞 L) (Fin n → 𝓞 L), (∀ w, w ∈ E ↔ ∃ z ∈ F, c • z = ∑ k, w k • x k) ∧ detIdeal E ≠ ⊥ ∧
      Ideal.absNorm (Ideal.span {c ^ n}) =
        (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup * Ideal.absNorm (detIdeal E) := by
  set Φ : (Fin n → 𝓞 L) →ₗ[𝓞 L] M := Fintype.linearCombination (𝓞 L) x with hΦ
  have hΦa : ∀ w, Φ w = ∑ k, w k • x k := fun w => Fintype.linearCombination_apply _ _ _
  have hΦi : Function.Injective Φ := by
    intro a b h
    have h' := Fintype.linearIndependent_iff.1 hli (a - b) (by
      rw [← hΦa, map_sub, h, sub_self])
    funext i
    exact sub_eq_zero.1 (h' i)
  have hrange : Submodule.span (𝓞 L) (Set.range x) = LinearMap.range Φ := by
    rw [hΦ, Fintype.range_linearCombination]
  set ψ : M →ₗ[𝓞 L] M := c • LinearMap.id with hψ
  have hψa : ∀ z, ψ z = c • z := fun z => rfl
  have hψi : Function.Injective ψ := by
    intro a b h
    rw [hψa, hψa] at h
    exact smul_right_injective M hc h
  set E : Submodule (𝓞 L) (Fin n → 𝓞 L) := (F.map ψ).comap Φ with hE
  have hmem : ∀ w, w ∈ E ↔ ∃ z ∈ F, c • z = ∑ k, w k • x k := by
    intro w
    simp only [hE, Submodule.mem_comap, Submodule.mem_map, hψa, hΦa]
  set A : Submodule (𝓞 L) (Fin n → 𝓞 L) :=
    LinearMap.range (c • (1 : Matrix (Fin n) (Fin n) (𝓞 L))).mulVecLin with hA
  have hAmem : ∀ w, w ∈ A ↔ ∃ v, c • v = w := by
    intro w
    simp [hA, Matrix.mulVecLin_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hAE : A ≤ E := by
    intro w hw
    obtain ⟨v, rfl⟩ := (hAmem w).1 hw
    rw [hmem]
    refine ⟨Φ v, ?_, ?_⟩
    · rw [hΦa]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hx k)
    · rw [hΦa, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_eq_mul, smul_smul]
  have hdet : detIdeal E ≠ ⊥ := by
    intro hb
    have h1 := det_mem_detIdeal E (fun i => c • Pi.single i (1 : 𝓞 L)) (fun i => hAE ((hAmem _).2 ⟨_, rfl⟩))
    rw [hb, Ideal.mem_bot] at h1
    have e1 : Matrix.of (fun i => c • Pi.single i (1 : 𝓞 L)) = c • (1 : Matrix (Fin n) (Fin n) (𝓞 L)) := by
      ext i j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [e1, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    exact pow_ne_zero n hc h1
  refine ⟨E, hmem, hdet, ?_⟩
  have iA : A.toAddSubgroup.index = Ideal.absNorm (Ideal.span {c ^ n}) := by
    rw [Ideal.absNorm_span_singleton]
    have := card_quotient_mulVecLin (K := L) (c • (1 : Matrix (Fin n) (Fin n) (𝓞 L)))
      (by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]; exact pow_ne_zero n hc)
    rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    exact this
  have iE : E.toAddSubgroup.index = Ideal.absNorm (detIdeal E) := card_quotient_eq_absNorm_detIdeal n E
  have m1 : A.toAddSubgroup.map Φ.toAddMonoidHom =
      (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.map ψ.toAddMonoidHom := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨v, rfl⟩ := (hAmem w).1 hw
      exact ⟨Φ v, by rw [hrange]; exact ⟨v, rfl⟩, by rw [hψa, map_smul]⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hrange] at hy
      obtain ⟨v, rfl⟩ := hy
      exact ⟨c • v, (hAmem _).2 ⟨v, rfl⟩, by rw [hψa, map_smul]⟩
  have m2 : E.toAddSubgroup.map Φ.toAddMonoidHom = F.toAddSubgroup.map ψ.toAddMonoidHom := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe]
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨y, hy, he⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hw)
      exact ⟨y, hy, he⟩
    · rintro ⟨y, hy, rfl⟩
      have h2 := hF y hy
      rw [hrange] at h2
      obtain ⟨w, hw⟩ := h2
      refine ⟨w, ?_, by rw [hw, hψa]⟩
      exact Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨y, hy, by rw [hw, hψa]⟩)
  have hrel : A.toAddSubgroup.relIndex E.toAddSubgroup =
      (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup := by
    rw [← AddSubgroup.relIndex_map_map_of_injective (f := Φ.toAddMonoidHom) _ _ hΦi, m1, m2,
      AddSubgroup.relIndex_map_map_of_injective _ _ hψi]
  rw [← iA, ← AddSubgroup.relIndex_mul_index (show A.toAddSubgroup ≤ E.toAddSubgroup from hAE), hrel, iE]

/- English proof (translation)
Take `⟨v, u, hvE, hdet, hlog, hu, hspan⟩` from `exists_max_det E hD p j`. Establish `hz : ∀ i, ∃ z ∈ F, c • z = ∑ k, v i k • x k` using `fun i => (hE (v i)).1 (hvE i)`. Use `choose y hyF hy using hz`. Establish `hinj : Function.Injective (fun z : M => c • z)` using `smul_right_injective M hc`. Establish `key : ∀ z ∈ F, ∃ t : Fin n → 𝓞 L, u • z = ∑ k, t k • y k`.

Introduce `z hz`. Take `⟨w, hw⟩` from `(Submodule.mem_span_range_iff_exists_fun (𝓞 L)).1 (hF z hz)`. Establish `hwE : w ∈ E` using `(hE w).2 ⟨z, hz, hw.symm⟩`. Take `⟨t, ht⟩` from `hspan w hwE`. Use `⟨t, hinj ?_⟩` and prove the remaining obligations.

Establish `e1 : c • (u • z) = ∑ l, (u • w) l • x l`. Rewrite using `[smul_comm, ← hw, Finset.smul_sum]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, mul_smul]`. Establish `e2 : ∑ l, (u • w) l • x l = ∑ k, t k • (c • y k)`. Rewrite using `[ht]`.

Simplify using `only [hy, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul]`. Conclude with `Finset.sum_comm`. Use `show c • (u • z) = c • ∑ k, t k • y k`. Rewrite using `[e1, e2, Finset.smul_sum]`. Simplify using `only [smul_comm (t _) c]`.

Use `choose T0 hT using fun i => key (x i) (hx i)`. Use `set T : Matrix (Fin n) (Fin n) (𝓞 L) := Matrix.of T0 with hTdef`. Establish `hTV : T * Matrix.of v = (u * c) • (1 : Matrix (Fin n) (Fin n) (𝓞 L))`. Use `Matrix.ext fun i l => ?_` and prove the remaining obligations. Establish `h0` using `(Fintype.linearIndependent_iff.1 hli) (fun l => (T * Matrix.of v) i l - ((u * c) • (1 : Matrix (Fin n) (Fin n) (𝓞 L))) i l) ?_ l`.

Conclude with `sub_eq_zero.1 h0`. Simplify using `only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_smul, smul_smul]`. Rewrite using `[sub_eq_zero, Finset.sum_comm]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [hy, Finset.smul_sum, smul_smul, hTdef, Matrix.of_apply]`.

Use `_ = c • (u • x i) := by`. Rewrite using `[hT i, Finset.smul_sum]`. Simplify using `only [smul_comm c]`. Use `_ = (u * c) • x i := by rw [smul_smul, mul_comm]`. Establish `hu0 : u ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hu`. Establish `hdetT : T.det * (Matrix.of v).det = (u * c) ^ n`. Rewrite using `[← Matrix.det_mul, hTV, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]`. Establish `hTne : T.det ≠ 0`.

Introduce `h0`. Rewrite `hdetT` using `[h0, zero_mul]`. Conclude with `pow_ne_zero n (mul_ne_zero hu0 hc) hdetT.symm`. Establish `hji : Function.Injective (j.comp (algebraMap (𝓞 L) L))` using `j.injective.comp (IsFractionRing.injective (𝓞 L) L)`. Establish `hc' : logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) = Real.log ‖j ((c : L))‖ * n`.

Rewrite using `[(GlobalTheory.T.log_ideal_mul_span_map L p _ hji).2.1]`. Simplify using `[map_pow, norm_pow, Real.log_pow, mul_comm]`. Establish `hnorm : ‖j (T.det : L)‖ * ‖j ((Matrix.of v).det : L)‖ = ‖j (c : L)‖ ^ n`. Use `congrArg (fun a : 𝓞 L => ‖j (a : L)‖) hdetT` as an intermediate fact. Simplify `this` using `[map_pow, map_mul, norm_pow, norm_mul, hu]`.

Establish `hpos1 : ‖j (T.det : L)‖ ≠ 0`. Simplify using `using hTne`. Establish `hpos2 : ‖j ((Matrix.of v).det : L)‖ ≠ 0`. Simplify using `using hdet`. Use `⟨y, u, T, hyF, ?_, fun z hz => ?_, hu, fun i => by simpa [hTdef] using hT i, hTne, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h1 : Matrix.vecMul g (Matrix.of v) = 0`. Rewrite `hli` using `[Fintype.linearIndependent_iff]`. Use function extensionality and compare the values at `l`.

Use `hli (Matrix.vecMul g (Matrix.of v)) ?_ l` and prove the remaining obligations. Use `congrArg (fun z => c • z) hg` as an intermediate fact. Simplify using `only [Finset.smul_sum, smul_comm c (g _), hy, smul_zero, Finset.smul_sum, smul_smul] at this`. Rewrite `this` using `[Finset.sum_comm]`. Simplify `this` using `[Matrix.vecMul, dotProduct, Finset.sum_smul]`.

Conclude with `congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet h1)`. Take `⟨t, ht⟩` from `key z hz`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[ht]`. Conclude with `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.

Rewrite using `[hc', hlog]`. Use `congrArg Real.log hnorm` as an intermediate fact. Rewrite `this` using `[Real.log_mul hpos1 hpos2, Real.log_pow]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_local_frame {M : Type} [AddCommGroup M] [Module (𝓞 L) M] [Module.IsTorsionFree (𝓞 L) M]
    (F : Submodule (𝓞 L) M) {n : ℕ} (x : Fin n → M) (hx : ∀ i, x i ∈ F) (hli : LinearIndependent (𝓞 L) x)
    (c : 𝓞 L) (hc : c ≠ 0) (hF : ∀ z ∈ F, c • z ∈ Submodule.span (𝓞 L) (Set.range x))
    (E : Submodule (𝓞 L) (Fin n → 𝓞 L)) (hE : ∀ w, w ∈ E ↔ ∃ z ∈ F, c • z = ∑ k, w k • x k) (hD : detIdeal E ≠ ⊥)
    (p : Nat.Primes) (j : L →+* ℂ_[p]) :
    ∃ (y : Fin n → M) (s : 𝓞 L) (T : Matrix (Fin n) (Fin n) (𝓞 L)), (∀ k, y k ∈ F) ∧ LinearIndependent (𝓞 L) y ∧
      (∀ z ∈ F, ∃ u : 𝓞 L, ‖j (u : L)‖ = 1 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) ∧ ‖j (s : L)‖ = 1 ∧
      (∀ i, s • x i = ∑ k, T i k • y k) ∧ T.det ≠ 0 ∧
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) - logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E) =
        Real.log ‖j ((T.det : 𝓞 L) : L)‖ := by
  obtain ⟨v, u, hvE, hdet, hlog, hu, hspan⟩ := exists_max_det E hD p j
  have hz : ∀ i, ∃ z ∈ F, c • z = ∑ k, v i k • x k := fun i => (hE (v i)).1 (hvE i)
  choose y hyF hy using hz
  have hinj : Function.Injective (fun z : M => c • z) := smul_right_injective M hc
  have key : ∀ z ∈ F, ∃ t : Fin n → 𝓞 L, u • z = ∑ k, t k • y k := by
    intro z hz
    obtain ⟨w, hw⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 L)).1 (hF z hz)
    have hwE : w ∈ E := (hE w).2 ⟨z, hz, hw.symm⟩
    obtain ⟨t, ht⟩ := hspan w hwE
    refine ⟨t, hinj ?_⟩
    have e1 : c • (u • z) = ∑ l, (u • w) l • x l := by
      rw [smul_comm, ← hw, Finset.smul_sum]
      simp only [Pi.smul_apply, smul_eq_mul, mul_smul]
    have e2 : ∑ l, (u • w) l • x l = ∑ k, t k • (c • y k) := by
      rw [ht]
      simp only [hy, Finset.smul_sum, smul_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.sum_smul]
      exact Finset.sum_comm
    show c • (u • z) = c • ∑ k, t k • y k
    rw [e1, e2, Finset.smul_sum]
    simp only [smul_comm (t _) c]
  choose T0 hT using fun i => key (x i) (hx i)
  set T : Matrix (Fin n) (Fin n) (𝓞 L) := Matrix.of T0 with hTdef
  have hTV : T * Matrix.of v = (u * c) • (1 : Matrix (Fin n) (Fin n) (𝓞 L)) := by
    refine Matrix.ext fun i l => ?_
    have h0 := (Fintype.linearIndependent_iff.1 hli)
      (fun l => (T * Matrix.of v) i l - ((u * c) • (1 : Matrix (Fin n) (Fin n) (𝓞 L))) i l) ?_ l
    · exact sub_eq_zero.1 h0
    · simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.of_apply, Matrix.smul_apply,
        Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, if_true, Finset.sum_smul, smul_smul]
      rw [sub_eq_zero, Finset.sum_comm]
      calc ∑ k, ∑ l, (T i k * v k l) • x l = ∑ k, T0 i k • (c • y k) := by
            simp only [hy, Finset.smul_sum, smul_smul, hTdef, Matrix.of_apply]
        _ = c • (u • x i) := by
            rw [hT i, Finset.smul_sum]
            simp only [smul_comm c]
        _ = (u * c) • x i := by rw [smul_smul, mul_comm]
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have hdetT : T.det * (Matrix.of v).det = (u * c) ^ n := by
    rw [← Matrix.det_mul, hTV, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hTne : T.det ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hdetT
    exact pow_ne_zero n (mul_ne_zero hu0 hc) hdetT.symm
  have hji : Function.Injective (j.comp (algebraMap (𝓞 L) L)) :=
    j.injective.comp (IsFractionRing.injective (𝓞 L) L)
  have hc' : logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) = Real.log ‖j ((c : L))‖ * n := by
    rw [(GlobalTheory.T.log_ideal_mul_span_map L p _ hji).2.1]
    simp [map_pow, norm_pow, Real.log_pow, mul_comm]
  have hnorm : ‖j (T.det : L)‖ * ‖j ((Matrix.of v).det : L)‖ = ‖j (c : L)‖ ^ n := by
    have := congrArg (fun a : 𝓞 L => ‖j (a : L)‖) hdetT
    simpa [map_pow, map_mul, norm_pow, norm_mul, hu] using this
  have hpos1 : ‖j (T.det : L)‖ ≠ 0 := by
    simpa using hTne
  have hpos2 : ‖j ((Matrix.of v).det : L)‖ ≠ 0 := by
    simpa using hdet
  refine ⟨y, u, T, hyF, ?_, fun z hz => ?_, hu, fun i => by simpa [hTdef] using hT i, hTne, ?_⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : Matrix.vecMul g (Matrix.of v) = 0 := by
      rw [Fintype.linearIndependent_iff] at hli
      funext l
      refine hli (Matrix.vecMul g (Matrix.of v)) ?_ l
      have := congrArg (fun z => c • z) hg
      simp only [Finset.smul_sum, smul_comm c (g _), hy, smul_zero, Finset.smul_sum, smul_smul] at this
      rw [Finset.sum_comm] at this
      simpa [Matrix.vecMul, dotProduct, Finset.sum_smul] using this
    exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hdet h1)
  · obtain ⟨t, ht⟩ := key z hz
    refine ⟨u, hu, ?_⟩
    rw [ht]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [hc', hlog]
    have := congrArg Real.log hnorm
    rw [Real.log_mul hpos1 hpos2, Real.log_pow] at this
    linarith

end Local

/- English proof (translation)
Establish `heq : B.gramDet σ x = (Matrix.gram ℂ fun i => fibreVec B.metric σ (x i)).det`. Unfold `HermitianBundle.gramDet`. Use `congr 1`. Establish `hnn` using `(Matrix.posSemidef_gram ℂ (fun i => fibreVec B.metric σ (x i))).det_nonneg`. Take `⟨r, hr, hz⟩` from `RCLike.nonneg_iff_exists_ofReal.1 hnn`.

Unfold `gramDet`. Rewrite using `[heq, ← hz]`. Simplify using `[RCLike.norm_ofReal, abs_of_nonneg hr]`.
-/
private theorem exists_logNorms_lemma {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (σ : L →+* ℂ) {n : ℕ} (x : Fin n → B.carrier) :
    Real.log (gramDet B.metric σ x) = Real.log ‖B.gramDet σ x‖ := by
  have heq : B.gramDet σ x = (Matrix.gram ℂ fun i => fibreVec B.metric σ (x i)).det := by
    unfold HermitianBundle.gramDet
    congr 1
  have hnn := (Matrix.posSemidef_gram ℂ (fun i => fibreVec B.metric σ (x i))).det_nonneg
  obtain ⟨r, hr, hz⟩ := RCLike.nonneg_iff_exists_ofReal.1 hnn
  unfold gramDet
  rw [heq, ← hz]
  simp [RCLike.norm_ofReal, abs_of_nonneg hr]

/- English proof (translation)
Set `s : Fin n → F` to `fun i => ⟨x i, hx i⟩`. Establish `hsli : LinearIndependent (𝓞 L) s` using `LinearIndependent.of_comp F.subtype hli`. Set `S` to `Submodule.span (𝓞 L) (Set.range s)`. Establish `hF : Module.rank (𝓞 L) F = n`. Rewrite using `[← hn, HermitianBundle.rank]`.

Conclude with `(Cardinal.cast_toNat_of_lt_aleph0 (Module.rank_lt_aleph0 _ _)).symm`. Establish `hS : Module.rank (𝓞 L) S = n`. Rewrite using `[rank_span hsli, Cardinal.mk_range_eq s hsli.injective, Cardinal.mk_fin]`. Establish `hQ` using `rank_quotient_add_rank_of_isDomain S`. Rewrite `hQ` using `[hS, hF]`.

Take `⟨k, hk⟩` from `Cardinal.lt_aleph0.1 (Module.rank_lt_aleph0 (𝓞 L) (F ⧸ S))`. Rewrite `hQ` using `[hk]`. Establish `hk0 : k = 0`. Establish `: ((k + n : ℕ) : Cardinal) = (n : Cardinal)` using `by rw [Nat.cast_add]; exact hQ`. Use `Nat.cast_injective this` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hr : Module.rank (𝓞 L) (F ⧸ S) = 0` using `by rw [hk, hk0, Nat.cast_zero]`. Establish `htor` using `rank_eq_zero_iff.1 hr`. Use `choose a ha0 hav using htor`. Take `⟨m, g, hg⟩` from `Module.Finite.exists_fin (R := 𝓞 L) (M := F ⧸ S)`.

Use `⟨∏ i, a (g i), Finset.prod_ne_zero_iff.2 fun i _ => ha0 _, fun z hz => ?_⟩` and prove the remaining obligations. Establish `key : ∀ q : F ⧸ S, (∏ i, a (g i)) • q = 0`. Introduce `q`. Establish `hq : q ∈ Submodule.span (𝓞 L) (Set.range g)` using `hg ▸ Submodule.mem_top`. Proceed by induction on `hq using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨i, rfl⟩` from `hy`. Take `⟨d, hd⟩` from `Finset.dvd_prod_of_mem (fun i => a (g i)) (Finset.mem_univ i)`. Rewrite using `[hd, mul_comm, mul_smul, hav, smul_zero]`. Consider the case `zero => exact smul_zero _`.

Consider the case `add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]`. Consider the case `smul r y _ hy => rw [smul_comm, hy, smul_zero]`. Establish `h1` using `key (Submodule.Quotient.mk ⟨z, hz⟩)`. Rewrite `h1` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Establish `h2` using `Submodule.mem_map_of_mem (f := F.subtype) h1`.

Rewrite `h2` using `[Submodule.map_span, ← Set.range_comp]`. Conclude with `h2`.
-/
private theorem exists_logNorms_lemma_2 {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) {n : ℕ} (x : Fin n → B.carrier) (hx : ∀ i, x i ∈ F)
    (hli : LinearIndependent (𝓞 L) x) (hn : B.rank F = n) :
    ∃ c : 𝓞 L, c ≠ 0 ∧ ∀ z ∈ F, c • z ∈ Submodule.span (𝓞 L) (Set.range x) := by
  let s : Fin n → F := fun i => ⟨x i, hx i⟩
  have hsli : LinearIndependent (𝓞 L) s := LinearIndependent.of_comp F.subtype hli
  let S := Submodule.span (𝓞 L) (Set.range s)
  have hF : Module.rank (𝓞 L) F = n := by
    rw [← hn, HermitianBundle.rank]
    exact (Cardinal.cast_toNat_of_lt_aleph0 (Module.rank_lt_aleph0 _ _)).symm
  have hS : Module.rank (𝓞 L) S = n := by
    rw [rank_span hsli, Cardinal.mk_range_eq s hsli.injective, Cardinal.mk_fin]
  have hQ := rank_quotient_add_rank_of_isDomain S
  rw [hS, hF] at hQ
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.1 (Module.rank_lt_aleph0 (𝓞 L) (F ⧸ S))
  rw [hk] at hQ
  have hk0 : k = 0 := by
    have : ((k + n : ℕ) : Cardinal) = (n : Cardinal) := by rw [Nat.cast_add]; exact hQ
    have := Nat.cast_injective this
    omega
  have hr : Module.rank (𝓞 L) (F ⧸ S) = 0 := by rw [hk, hk0, Nat.cast_zero]
  have htor := rank_eq_zero_iff.1 hr
  choose a ha0 hav using htor
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin (R := 𝓞 L) (M := F ⧸ S)
  refine ⟨∏ i, a (g i), Finset.prod_ne_zero_iff.2 fun i _ => ha0 _, fun z hz => ?_⟩
  have key : ∀ q : F ⧸ S, (∏ i, a (g i)) • q = 0 := by
    intro q
    have hq : q ∈ Submodule.span (𝓞 L) (Set.range g) := hg ▸ Submodule.mem_top
    induction hq using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem (fun i => a (g i)) (Finset.mem_univ i)
      rw [hd, mul_comm, mul_smul, hav, smul_zero]
    | zero => exact smul_zero _
    | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
    | smul r y _ hy => rw [smul_comm, hy, smul_zero]
  have h1 := key (Submodule.Quotient.mk ⟨z, hz⟩)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
  have h2 := Submodule.mem_map_of_mem (f := F.subtype) h1
  rw [Submodule.map_span, ← Set.range_comp] at h2
  exact h2

/- English proof (translation)
Take `⟨c, hc, hF⟩` from `exists_logNorms_lemma_2 B F x hx hli hn`. Take `⟨E, hE, hD, hidx⟩` from `exists_coord_lattice F x hx hli c hc hF`. Establish `hcn : Ideal.span {c ^ n} ≠ ⊥`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `pow_ne_zero _ hc`.

Set `N : Fl.LogNorms L` to `⟨fun σ => Real.log ‖B.gramDet σ x‖ / 2, fun p j => logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) - logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E)⟩`. Use `set idx := (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup with hidx_def`. Establish `hprod : Ideal.absNorm (Ideal.span {c ^ n}) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `hcn`.

Rewrite `hprod` using `[hidx]`. Establish `hi0 : idx ≠ 0` using `left_ne_zero_of_mul hprod`. Establish `hd0 : Ideal.absNorm (detIdeal E) ≠ 0` using `right_ne_zero_of_mul hprod`. Establish `hfs : N.finSum = fun p : Nat.Primes => Real.log ‖((idx : ℚ) : ℂ_[p])‖`. Use function extensionality and compare the values at `p`.

Establish `e1` using `GlobalTheory.T.sum_logIdeal_eq_log_absNorm L _ hcn p`. Establish `e2` using `GlobalTheory.T.sum_logIdeal_eq_log_absNorm L _ hD p`. Establish `hne1 : ‖((idx : ℕ) : ℂ_[p])‖ ≠ 0` using `norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 hi0)`. Establish `hne2 : ‖((Ideal.absNorm (detIdeal E) : ℕ) : ℂ_[p])‖ ≠ 0` using `norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 hd0)`. Use `show ∑ j : L →+* ℂ_[p], (logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) - logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E)) = _`.

Rewrite using `[Finset.sum_sub_distrib, e1, e2, hidx, Nat.cast_mul, norm_mul, Real.log_mul hne1 hne2, Rat.cast_natCast]`. Expand and normalize the polynomial expressions, which then agree. Establish `hpf` using `(GlobalTheory.T.rat_product_formula (idx : ℚ) (Nat.cast_ne_zero.2 hi0)).2`. Set `s : Fin n → F` to `fun i => ⟨x i, hx i⟩`. Establish `hsli : LinearIndependent (𝓞 L) s` using `LinearIndependent.of_comp F.subtype hli`.

Establish `hsub : (Submodule.span (𝓞 L) (Set.range s)).toAddSubgroup = (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.addSubgroupOf F.toAddSubgroup`. Use extensionality with `⟨z, hz⟩`. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Simplify using `only [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun, Subtype.ext_iff, Submodule.coe_sum, Submodule.coe_smul, s]`. Establish `hcard : Nat.card (F ⧸ Submodule.span (𝓞 L) (Set.range s)) = idx`.

Rewrite using `[hidx_def, AddSubgroup.relIndex, AddSubgroup.index, ← hsub]`. Both sides reduce to the same expression. Establish `hdeg` using `HermitianBundle.degree_eq_of_linearIndependent B F hsli (by rw [Fintype.card_fin, hn])`. Use `⟨N, ?_, ?_, fun σ => rfl, fun p j => ?_⟩` and prove the remaining obligations. Use `((GlobalTheory.T.logIdeal_support_finite L _ hcn).union (GlobalTheory.T.logIdeal_support_finite L _ hD)).subset ?_` and prove the remaining obligations.

Introduce and unpack `p ⟨j, hj⟩`. Assume the negation of the conclusion as `hc'`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at hc'`. Conclude with `hj (by show _ - _ = (0 : ℝ); rw [hc'.1, hc'.2, sub_zero])`. Unfold `Fl.LogNorms.deg HermitianBundle.normDegree`.

Rewrite using `[hfs, hdeg, hcard]`. Simplify using `only [exists_logNorms_lemma]`. Establish `hq : ‖((idx : ℚ) : ℂ)‖ = (idx : ℝ)` using `by simp`. Rewrite `hpf` using `[hq]`. Establish `hsum : ∑ σ : L →+* ℂ, N.inf σ = (∑ σ : L →+* ℂ, Real.log ‖B.gramDet σ x‖) / 2`.

Rewrite using `[Finset.sum_div]`. Rewrite using `[hsum]`. Use `congr 1`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨y, s', T, h1, h2, h3, h4, h5, h6, h7⟩` from `exists_local_frame F x hx hli c hc hF E hE hD p j`.

Conclude with `⟨y, s', T, h1, h2, h3, h4, h5, h6, h7⟩`.
-/
theorem exists_logNorms {L : Type} [Field L] [NumberField L] (B : HermitianBundle.{0} L)
    (F : Submodule (𝓞 L) B.carrier) {n : ℕ} (x : Fin n → B.carrier) (hx : ∀ i, x i ∈ F)
    (hli : LinearIndependent (𝓞 L) x) (hn : B.rank F = n) :
    ∃ N : Fl.LogNorms L, N.IsAdelic ∧ N.deg = B.normDegree F ∧ (∀ σ, N.inf σ = Real.log ‖B.gramDet σ x‖ / 2) ∧
      ∀ (p : Nat.Primes) (j : L →+* ℂ_[p]), ∃ (y : Fin n → B.carrier) (s : 𝓞 L) (T : Matrix (Fin n) (Fin n) (𝓞 L)),
        (∀ k, y k ∈ F) ∧ LinearIndependent (𝓞 L) y ∧
        (∀ z ∈ F, ∃ u : 𝓞 L, ‖j (u : L)‖ = 1 ∧ u • z ∈ Submodule.span (𝓞 L) (Set.range y)) ∧ ‖j (s : L)‖ = 1 ∧
        (∀ i, s • x i = ∑ k, T i k • y k) ∧ T.det ≠ 0 ∧ N.fin p j = Real.log ‖j ((T.det : 𝓞 L) : L)‖ := by
  obtain ⟨c, hc, hF⟩ := exists_logNorms_lemma_2 B F x hx hli hn
  obtain ⟨E, hE, hD, hidx⟩ := exists_coord_lattice F x hx hli c hc hF
  have hcn : Ideal.span {c ^ n} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero _ hc
  let N : Fl.LogNorms L := ⟨fun σ => Real.log ‖B.gramDet σ x‖ / 2,
    fun p j => logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) -
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E)⟩
  set idx := (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.relIndex F.toAddSubgroup with hidx_def
  have hprod : Ideal.absNorm (Ideal.span {c ^ n}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hcn
  rw [hidx] at hprod
  have hi0 : idx ≠ 0 := left_ne_zero_of_mul hprod
  have hd0 : Ideal.absNorm (detIdeal E) ≠ 0 := right_ne_zero_of_mul hprod
  have hfs : N.finSum = fun p : Nat.Primes => Real.log ‖((idx : ℚ) : ℂ_[p])‖ := by
    funext p
    have e1 := GlobalTheory.T.sum_logIdeal_eq_log_absNorm L _ hcn p
    have e2 := GlobalTheory.T.sum_logIdeal_eq_log_absNorm L _ hD p
    have hne1 : ‖((idx : ℕ) : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 hi0)
    have hne2 : ‖((Ideal.absNorm (detIdeal E) : ℕ) : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (Nat.cast_ne_zero.2 hd0)
    show ∑ j : L →+* ℂ_[p], (logIdeal (j.comp (algebraMap (𝓞 L) L)) (Ideal.span {c ^ n}) -
      logIdeal (j.comp (algebraMap (𝓞 L) L)) (detIdeal E)) = _
    rw [Finset.sum_sub_distrib, e1, e2, hidx, Nat.cast_mul, norm_mul, Real.log_mul hne1 hne2, Rat.cast_natCast]
    ring
  have hpf := (GlobalTheory.T.rat_product_formula (idx : ℚ) (Nat.cast_ne_zero.2 hi0)).2
  let s : Fin n → F := fun i => ⟨x i, hx i⟩
  have hsli : LinearIndependent (𝓞 L) s := LinearIndependent.of_comp F.subtype hli
  have hsub : (Submodule.span (𝓞 L) (Set.range s)).toAddSubgroup =
      (Submodule.span (𝓞 L) (Set.range x)).toAddSubgroup.addSubgroupOf F.toAddSubgroup := by
    ext ⟨z, hz⟩
    rw [AddSubgroup.mem_addSubgroupOf]
    simp only [Submodule.mem_toAddSubgroup,
      Submodule.mem_span_range_iff_exists_fun, Subtype.ext_iff, Submodule.coe_sum, Submodule.coe_smul, s]
  have hcard : Nat.card (F ⧸ Submodule.span (𝓞 L) (Set.range s)) = idx := by
    rw [hidx_def, AddSubgroup.relIndex, AddSubgroup.index, ← hsub]
    rfl
  have hdeg := HermitianBundle.degree_eq_of_linearIndependent B F hsli (by rw [Fintype.card_fin, hn])
  refine ⟨N, ?_, ?_, fun σ => rfl, fun p j => ?_⟩
  · refine ((GlobalTheory.T.logIdeal_support_finite L _ hcn).union (GlobalTheory.T.logIdeal_support_finite L _ hD)).subset ?_
    rintro p ⟨j, hj⟩
    by_contra hc'
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_exists, not_not] at hc'
    exact hj (by show _ - _ = (0 : ℝ); rw [hc'.1, hc'.2, sub_zero])
  · unfold Fl.LogNorms.deg HermitianBundle.normDegree
    rw [hfs, hdeg, hcard]
    simp only [exists_logNorms_lemma]
    have hq : ‖((idx : ℚ) : ℂ)‖ = (idx : ℝ) := by simp
    rw [hq] at hpf
    have hsum : ∑ σ : L →+* ℂ, N.inf σ = (∑ σ : L →+* ℂ, Real.log ‖B.gramDet σ x‖) / 2 := by
      rw [Finset.sum_div]
    rw [hsum]
    congr 1
    linarith
  · obtain ⟨y, s', T, h1, h2, h3, h4, h5, h6, h7⟩ := exists_local_frame F x hx hli c hc hF E hE hD p j
    exact ⟨y, s', T, h1, h2, h3, h4, h5, h6, h7⟩

/- English proof (translation)
Use `h.subset fun p hp => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Simplify using `only [Set.mem_setOf_eq, not_exists, not_not] at h0`. Conclude with `hp (Finset.sum_eq_zero fun j _ => h0 j)`.
-/
theorem finite_finSum {k : Type} [Field k] [NumberField k] {N : Fl.LogNorms k} (h : N.IsAdelic) :
    (Function.support N.finSum).Finite := by
  refine h.subset fun p hp => ?_
  by_contra h0
  simp only [Set.mem_setOf_eq, not_exists, not_not] at h0
  exact hp (Finset.sum_eq_zero fun j _ => h0 j)

/- English proof (translation)
Take `⟨hd, _⟩` from `GlobalTheory.T.logNorms_ext_degree_adelic k L' β N`. Take `⟨hd₁, ha₁⟩` from `GlobalTheory.T.logNorms_ext_degree_adelic L L' e N₁`. Take `⟨hd₂, ha₂⟩` from `GlobalTheory.T.logNorms_ext_degree_adelic L L' e N₂`. Take `⟨_, hpf⟩` from `GlobalTheory.T.product_formula_log_norms L' a ha`. Establish `f0` using `finite_finSum (GlobalTheory.T.log_norms_of_nonzero_adelic L' a ha)`.

Establish `f1` using `finite_finSum (ha₁.2 h₁)`. Establish `f2` using `finite_finSum (ha₂.2 h₂)`. Rewrite using `[← hd, ← hd₁, ← hd₂]`. Establish `hs : (LogNorms.ext β N).finSum = fun p => (LogNorms.ofElt a).finSum p + (LogNorms.ext e N₁).finSum p - (LogNorms.ext e N₂).finSum p`. Use function extensionality and compare the values at `p`.

Simplify using `only [LogNorms.finSum, LogNorms.ext, LogNorms.ofElt, hfin, Finset.sum_sub_distrib, Finset.sum_add_distrib]`. Establish `hfs : ∑ᶠ p, (LogNorms.ext β N).finSum p = ∑ᶠ p, (LogNorms.ofElt a).finSum p + ∑ᶠ p, (LogNorms.ext e N₁).finSum p - ∑ᶠ p, (LogNorms.ext e N₂).finSum p`. Rewrite using `[hs, finsum_sub_distrib ((f0.union f1).subset (Function.support_add _ _)) f2, finsum_add_distrib f0 f1]`. Establish `hi : ∑ s, (LogNorms.ext β N).inf s = ∑ s : L' →+* ℂ, Real.log ‖s a‖ + ∑ s, (LogNorms.ext e N₁).inf s - ∑ s, (LogNorms.ext e N₂).inf s`. Simplify using `only [LogNorms.ext, hinf, Finset.sum_sub_distrib, Finset.sum_add_distrib]`.

Unfold `LogNorms.deg`. Rewrite using `[hi, hfs, ← sub_div]`. Use `congr 1`. Combine the linear relations using `[hpf]`.
-/
theorem deg_eq_sub {k L L' : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Field L'] [NumberField L']
    (β : k →+* L') (e : L →+* L') (N : Fl.LogNorms k) (N₁ N₂ : Fl.LogNorms L) (a : L') (ha : a ≠ 0)
    (hN : N.IsAdelic) (h₁ : N₁.IsAdelic) (h₂ : N₂.IsAdelic)
    (hinf : ∀ s : L' →+* ℂ, N.inf (s.comp β) = Real.log ‖s a‖ + N₁.inf (s.comp e) - N₂.inf (s.comp e))
    (hfin : ∀ (p : Nat.Primes) (j : L' →+* ℂ_[p]),
      N.fin p (j.comp β) = Real.log ‖j a‖ + N₁.fin p (j.comp e) - N₂.fin p (j.comp e)) :
    N.deg = N₁.deg - N₂.deg := by
  obtain ⟨hd, _⟩ := GlobalTheory.T.logNorms_ext_degree_adelic k L' β N
  obtain ⟨hd₁, ha₁⟩ := GlobalTheory.T.logNorms_ext_degree_adelic L L' e N₁
  obtain ⟨hd₂, ha₂⟩ := GlobalTheory.T.logNorms_ext_degree_adelic L L' e N₂
  obtain ⟨_, hpf⟩ := GlobalTheory.T.product_formula_log_norms L' a ha
  have f0 := finite_finSum (GlobalTheory.T.log_norms_of_nonzero_adelic L' a ha)
  have f1 := finite_finSum (ha₁.2 h₁)
  have f2 := finite_finSum (ha₂.2 h₂)
  rw [← hd, ← hd₁, ← hd₂]
  have hs : (LogNorms.ext β N).finSum = fun p => (LogNorms.ofElt a).finSum p +
      (LogNorms.ext e N₁).finSum p - (LogNorms.ext e N₂).finSum p := by
    funext p
    simp only [LogNorms.finSum, LogNorms.ext, LogNorms.ofElt, hfin, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
  have hfs : ∑ᶠ p, (LogNorms.ext β N).finSum p = ∑ᶠ p, (LogNorms.ofElt a).finSum p +
      ∑ᶠ p, (LogNorms.ext e N₁).finSum p - ∑ᶠ p, (LogNorms.ext e N₂).finSum p := by
    rw [hs, finsum_sub_distrib ((f0.union f1).subset (Function.support_add _ _)) f2,
      finsum_add_distrib f0 f1]
  have hi : ∑ s, (LogNorms.ext β N).inf s = ∑ s : L' →+* ℂ, Real.log ‖s a‖ +
      ∑ s, (LogNorms.ext e N₁).inf s - ∑ s, (LogNorms.ext e N₂).inf s := by
    simp only [LogNorms.ext, hinf, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  unfold LogNorms.deg
  rw [hi, hfs, ← sub_div]
  congr 1
  linarith [hpf]

end LevelTowerAlt
