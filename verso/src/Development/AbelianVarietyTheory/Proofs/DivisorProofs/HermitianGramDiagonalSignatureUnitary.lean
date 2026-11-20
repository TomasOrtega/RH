import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUCovolConj
open MeasureTheory Set
open scoped Pointwise

section General

variable {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [MeasurableSpace X]
  [BorelSpace X] [SecondCountableTopology X]

/- English proof (translation)
Use `hD.image_of_equiv (MulAut.conj s).toEquiv ?_ { toFun := fun g => ⟨s⁻¹ * g.1 * s, (hH g.1).1 g.2⟩ invFun := fun g => ⟨s * g.1 * s⁻¹, (hH _).2 (by simpa [mul_assoc] using g.2)⟩ left_inv := fun g => by ext; simp [mul_assoc] right_inv := fun g => by ext; simp [mul_assoc] } ?_` and prove the remaining obligations. Establish `: ((MulAut.conj s).toEquiv.symm : X → X) = (fun x => x * s) ∘ (fun x => s⁻¹ * x)`. Use function extensionality and compare the values at `x`. Simplify using `[mul_assoc]`. Rewrite using `[this]`.

Conclude with `(quasiMeasurePreserving_mul_right μ s).comp (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving`. Introduce `g x`. Simplify using `[Subgroup.smul_def, mul_assoc]`.
-/
theorem isFundamentalDomain_conj (μ : Measure X) [μ.IsMulLeftInvariant] [SFinite μ]
    (H H' : Subgroup X) (s : X) (hH : ∀ g, g ∈ H' ↔ s⁻¹ * g * s ∈ H) {D : Set X}
    (hD : IsFundamentalDomain H D μ) :
    IsFundamentalDomain H' ((MulAut.conj s).toEquiv '' D) μ := by
  refine hD.image_of_equiv (MulAut.conj s).toEquiv ?_
    { toFun := fun g => ⟨s⁻¹ * g.1 * s, (hH g.1).1 g.2⟩
      invFun := fun g => ⟨s * g.1 * s⁻¹, (hH _).2 (by simpa [mul_assoc] using g.2)⟩
      left_inv := fun g => by ext; simp [mul_assoc]
      right_inv := fun g => by ext; simp [mul_assoc] } ?_
  · have : ((MulAut.conj s).toEquiv.symm : X → X) = (fun x => x * s) ∘ (fun x => s⁻¹ * x) := by
      funext x; simp [mul_assoc]
    rw [this]
    exact (quasiMeasurePreserving_mul_right μ s).comp
      (measurePreserving_mul_left μ s⁻¹).quasiMeasurePreserving
  · intro g x
    simp [Subgroup.smul_def, mul_assoc]

/- English proof (translation)
Establish `hH2 : ∀ g, g ∈ H ↔ s⁻¹⁻¹ * g * s⁻¹ ∈ H'` using `fun g => by rw [hH]; simp [mul_assoc]`. Distinguish the cases in `h : HasFundamentalDomain H X μ`. Take `⟨D, hD⟩` from `h.ExistsIsFundamentalDomain`. Establish `h1` using `isFundamentalDomain_conj μ H H' s hH hD`. Establish `h2 : IsFundamentalDomain H ((Equiv.mulRight s⁻¹) '' D) μ`.

Use `hD.image_of_equiv (Equiv.mulRight s⁻¹) ?_ (Equiv.refl _) ?_` and prove the remaining obligations. Establish `: ((Equiv.mulRight s⁻¹).symm : X → X) = fun x => x * s` using `by funext x; simp`. Rewrite using `[this]`. Conclude with `quasiMeasurePreserving_mul_right μ s`. Introduce `g x`.

Simplify using `[Subgroup.smul_def, mul_assoc]`. Rewrite using `[h1.covolume_eq_volume, hD.covolume_eq_volume, hD.measure_eq h2]`. Establish `: (MulAut.conj s).toEquiv '' D = s • ((Equiv.mulRight s⁻¹) '' D)`. Rewrite using `[← Set.image_smul, Set.image_image]`. Use `Set.image_congr fun y _ => ?_` and prove the remaining obligations.

Simplify using `[mul_assoc]`. Rewrite using `[this, measure_smul]`. Establish `h' : ¬ HasFundamentalDomain H' X μ`. Introduce and unpack `⟨D, hD⟩`. Conclude with `h ⟨_, isFundamentalDomain_conj μ H' H s⁻¹ hH2 hD⟩`.

Simplify using `[covolume, h, h']`.
-/
theorem covolume_conj (μ : Measure X) [μ.IsMulLeftInvariant] [SFinite μ]
    (H H' : Subgroup X) [Countable H] [Countable H'] (s : X)
    (hH : ∀ g, g ∈ H' ↔ s⁻¹ * g * s ∈ H) :
    covolume H' X μ = covolume H X μ := by
  have hH2 : ∀ g, g ∈ H ↔ s⁻¹⁻¹ * g * s⁻¹ ∈ H' := fun g => by rw [hH]; simp [mul_assoc]
  by_cases h : HasFundamentalDomain H X μ
  · obtain ⟨D, hD⟩ := h.ExistsIsFundamentalDomain
    have h1 := isFundamentalDomain_conj μ H H' s hH hD
    have h2 : IsFundamentalDomain H ((Equiv.mulRight s⁻¹) '' D) μ := by
      refine hD.image_of_equiv (Equiv.mulRight s⁻¹) ?_ (Equiv.refl _) ?_
      · have : ((Equiv.mulRight s⁻¹).symm : X → X) = fun x => x * s := by funext x; simp
        rw [this]; exact quasiMeasurePreserving_mul_right μ s
      · intro g x; simp [Subgroup.smul_def, mul_assoc]
    rw [h1.covolume_eq_volume, hD.covolume_eq_volume, hD.measure_eq h2]
    have : (MulAut.conj s).toEquiv '' D = s • ((Equiv.mulRight s⁻¹) '' D) := by
      rw [← Set.image_smul, Set.image_image]
      refine Set.image_congr fun y _ => ?_
      simp [mul_assoc]
    rw [this, measure_smul]
  · have h' : ¬ HasFundamentalDomain H' X μ := by
      rintro ⟨D, hD⟩; exact h ⟨_, isFundamentalDomain_conj μ H' H s⁻¹ hH2 hD⟩
    simp [covolume, h, h']

end General
section Concrete

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G M = Mᵀ * G.map τ * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[gram_eq_mul, det_mul, det_mul, det_transpose, (starRingEnd ℂ).map_det M, RingHom.mapMatrix_apply]`.
-/
theorem det_gram (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M : Matrix (Fin r) (Fin r) ℂ) :
    (gram τ G M).det = M.det * (G.map τ).det * starRingEnd ℂ M.det := by
  rw [gram_eq_mul, det_mul, det_mul, det_transpose, (starRingEnd ℂ).map_det M, RingHom.mapMatrix_apply]

/- English proof (translation)
Use extensionality with `k`. Simplify using `[ReciprocityTheory.ChartRestriction.G.FD.col, mulVec, dotProduct, Matrix.one_apply]`.
-/
theorem col_eq_mulVec (M : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    ReciprocityTheory.ChartRestriction.G.FD.col M a = M *ᵥ ReciprocityTheory.ChartRestriction.G.FD.col (1 : Matrix (Fin r) (Fin r) ℂ) a := by
  ext k; simp [ReciprocityTheory.ChartRestriction.G.FD.col, mulVec, dotProduct, Matrix.one_apply]

/- English proof (translation)
Establish `key (a b : Fin r) : ∑ c, ∑ d, τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b)) = τ (G a b)`. Establish `h` using `congrArg τ (h2 (Pi.single a 1) (Pi.single b 1))`. Simplify using `only [herm, cc, mulVec_single_one, Matrix.col_apply, map_sum, map_mul, IsCMField.complexEmbedding_complexConj] at h`. Rewrite using `[h, Finset.sum_eq_single a (by intro c _ hc; simp [hc]) (by simp), Finset.sum_eq_single b (by intro c _ hc; simp [hc]) (by simp)]`. Simplify using the standard rewrite rules.

Establish `hR : hermC τ G u w = ∑ a, ∑ b, u a * (∑ c, ∑ d, τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b))) * (starRingEnd ℂ) (w b)`. Simplify using `only [hermC, key]`. Rewrite using `[hR]`. Simplify using `only [hermC, mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`. Use `_ = _ := by`. Use `(Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)` and prove the remaining obligations.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Conclude with `(Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm`.
-/
theorem hermC_map_of_herm (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (γ : Matrix (Fin r) (Fin r) E)
    (h2 : ∀ x y, herm G (γ *ᵥ x) (γ *ᵥ y) = herm G x y) (u w : Fin r → ℂ) :
    hermC τ G (γ.map τ *ᵥ u) (γ.map τ *ᵥ w) = hermC τ G u w := by
  have key (a b : Fin r) : ∑ c, ∑ d, τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b)) =
      τ (G a b) := by
    have h := congrArg τ (h2 (Pi.single a 1) (Pi.single b 1))
    simp only [herm, cc, mulVec_single_one, Matrix.col_apply, map_sum, map_mul,
      IsCMField.complexEmbedding_complexConj] at h
    rw [h, Finset.sum_eq_single a (by intro c _ hc; simp [hc]) (by simp),
      Finset.sum_eq_single b (by intro c _ hc; simp [hc]) (by simp)]
    simp
  have hR : hermC τ G u w = ∑ a, ∑ b, u a *
      (∑ c, ∑ d, τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b))) * (starRingEnd ℂ) (w b) := by
    simp only [hermC, key]
  rw [hR]
  simp only [hermC, mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  calc _ = ∑ c, ∑ d, ∑ a, ∑ b,
        u a * (τ (γ c a) * τ (G c d) * (starRingEnd ℂ) (τ (γ d b))) * (starRingEnd ℂ) (w b) := by
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    _ = _ := by
        refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans (Finset.sum_comm.trans ?_)
        refine Finset.sum_congr rfl fun a _ => ?_
        exact (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm

/- English proof (translation)
Simplify using `only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring`.
-/
theorem hermC_smul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (c : ℂ) (u w : Fin r → ℂ) :
    hermC τ G (c • u) (c • w) = c * starRingEnd ℂ c * hermC τ G u w := by
  simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/- English proof (translation)
Use `haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm`. Use `haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))`. Use `haveI : Countable (GL (Fin r) E) := Function.Injective.countable (f := (Units.val : GL (Fin r) E → _)) fun _ _ h => Units.ext h`. Establish `: ((inReal Ψ G Γ : Subgroup (realSU Ψ G)) : Set (realSU Ψ G)).Countable`. Use `((Set.countable_range (embGL Ψ r)).preimage Subtype.val_injective).mono fun g hg => ?_` and prove the remaining obligations.

Take `⟨δ, -, hδ⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)`. Conclude with `⟨δ, hδ⟩`. Conclude with `this.to_subtype`.
-/
theorem countable_inReal (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (Γ : Subgroup (GL (Fin r) E)) : Countable (inReal Ψ G Γ) := by
  haveI : Countable E :=
    Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) :=
    Function.Injective.countable (f := (Units.val : GL (Fin r) E → _)) fun _ _ h => Units.ext h
  have : ((inReal Ψ G Γ : Subgroup (realSU Ψ G)) : Set (realSU Ψ G)).Countable := by
    refine ((Set.countable_range (embGL Ψ r)).preimage Subtype.val_injective).mono fun g hg => ?_
    obtain ⟨δ, -, hδ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hg)
    exact ⟨δ, hδ⟩
  exact this.to_subtype

end Concrete

/- English proof (translation)
Introduce `E _ _ _ r p0 Ψ G x γ Δ _hG hx hγ`. Use `set A : Ψ → GL (Fin r) ℂ := embGL Ψ r γ with hAdef`. Establish `hAv : ∀ τ : Ψ, ((A τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1` using `fun τ => rfl`. Establish `hA : ∀ τ : Ψ, ∀ u w, hermC τ.1 G ((A τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u) ((A τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) = hermC τ.1 G u w`. Introduce `τ u w`.

Rewrite using `[hAv]`. Conclude with `hermC_map_of_herm τ.1 G _ hγ u w`. Establish `hdet : ∀ τ : Ψ, (A τ : Matrix (Fin r) (Fin r) ℂ).det * starRingEnd ℂ (A τ : Matrix (Fin r) (Fin r) ℂ).det = 1`. Introduce `τ`. Establish `hg : (G.map τ.1).det ≠ 0`.

Introduce `h0`. Establish `h1` using `congrArg Matrix.det (hx τ)`. Rewrite `h1` using `[det_gram, h0, mul_zero, zero_mul, det_diagonal]`. Use `(Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm` and prove the remaining obligations. Apply the tactic sequence `simp only [sgn]; split_ifs <;> norm_num`.

Establish `e1 : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (A τ : Matrix (Fin r) (Fin r) ℂ) = ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G 1`. Use extensionality with `a b`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply]`. Rewrite using `[col_eq_mulVec (A τ : Matrix (Fin r) (Fin r) ℂ) a, col_eq_mulVec (A τ : Matrix (Fin r) (Fin r) ℂ) b, hA]`. Establish `h2` using `congrArg Matrix.det e1`.

Rewrite `h2` using `[det_gram, det_gram, det_one, map_one, one_mul, mul_one]`. Apply `mul_right_cancel₀ hg` to reduce the goal to its premises. Take the linear combination `h2`. Establish `hroot : ∀ τ : Ψ, ∃ m : ℂ, m ^ r = (A τ : Matrix (Fin r) (Fin r) ℂ).det ∧ m * starRingEnd ℂ m = 1`. Introduce `τ`.

Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Use `⟨1, ?_, by simp⟩` and prove the remaining obligations. Substitute `hr` using the available equality. Simplify using the standard rewrite rules. Take `⟨m, hm⟩` from `IsAlgClosed.exists_pow_nat_eq ((A τ : Matrix (Fin r) (Fin r) ℂ).det) hr`.

Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Establish `h1 : (m * starRingEnd ℂ m) ^ r = 1` using `by rw [mul_pow, ← map_pow, hm, hdet τ]`. Rewrite `h1`, the goal using `[Complex.mul_conj]`. Establish `h3 : (Complex.normSq m) ^ r = 1` using `by exact_mod_cast h1`. Rewrite using `[(pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg m) hr.ne').1 h3]`.

Simplify using the standard rewrite rules. Use `choose m hm using hroot`. Establish `hm0 : ∀ τ, m τ ≠ 0` using `fun τ h => by simpa [h] using (hm τ).2`. Set `z : Ψ → GL (Fin r) ℂ` to `fun τ => Units.map (algebraMap ℂ (Matrix (Fin r) (Fin r) ℂ)).toMonoidHom (Units.mk0 (m τ)⁻¹ (inv_ne_zero (hm0 τ)))`. Establish `hzv : ∀ τ, ((z τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (m τ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ)`.

Introduce `τ`. Simplify using `[z, Algebra.algebraMap_eq_smul_one]`. Establish `hzc : ∀ g : Ψ → GL (Fin r) ℂ, z * g = g * z`. Introduce `g`. Use function extensionality and compare the values at `τ`.

Use `ext1`. Simplify using `only [Pi.mul_apply, Units.val_mul, hzv, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]`. Establish `hs0 : A * z ∈ realSU Ψ G`. Introduce `τ`. Establish `e : (((A * z) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (m τ)⁻¹ • (A τ : Matrix (Fin r) (Fin r) ℂ)`.

Simplify using `only [Pi.mul_apply, Units.val_mul, hzv, Matrix.mul_smul, mul_one]`. Rewrite using `[e]`. Use `⟨?_, fun u w => ?_⟩` and prove the remaining obligations. Rewrite using `[det_smul, Fintype.card_fin, inv_pow, (hm τ).1]`. Establish `: (A τ : Matrix (Fin r) (Fin r) ℂ).det ≠ 0` using `fun h => by simpa [h] using hdet τ`.

Conclude with `inv_mul_cancel₀ this`. Rewrite using `[Matrix.smul_mulVec, Matrix.smul_mulVec, hermC_smul, hA, map_inv₀, ← mul_inv, (hm τ).2, inv_one, one_mul]`. Set `s : realSU Ψ G` to `⟨A * z, hs0⟩`. Establish `hconj : ∀ g : Ψ → GL (Fin r) ℂ, (A * z)⁻¹ * g * (A * z) = A⁻¹ * g * A`. Introduce `g`.

Combine the equalities or inequalities in the displayed calculation. Use `haveI := countable_inReal Ψ G Δ`. Use `haveI := countable_inReal Ψ G (Δ.map (MulAut.conj γ).toMonoidHom)`. Use `haveI : (riemHaar Ψ G x).IsMulLeftInvariant := by unfold riemHaar; infer_instance`. Use `haveI : SFinite (riemHaar Ψ G x) := by unfold riemHaar tangentHaar; infer_instance`.

Establish `key : ∀ δ, embGL Ψ r ((MulAut.conj γ).toMonoidHom δ) = A * embGL Ψ r δ * A⁻¹`. Introduce `δ`. Simplify using `[hAdef, MulAut.conj_apply, map_mul, map_inv]`. Use `covolume_conj (riemHaar Ψ G x) _ _ s fun g => ?_` and prove the remaining obligations. Simplify using `only [inReal, Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_mul, Subgroup.coe_inv]`.

Rewrite using `[hconj]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨δ', ⟨δ, hδ, rfl⟩, h⟩`. Use `⟨δ, hδ, ?_⟩` and prove the remaining obligations. Rewrite using `[← h, key]`.

Use `group`. Introduce and unpack `⟨δ, hδ, h⟩`. Use `⟨_, ⟨δ, hδ, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[key, h]`. Use `group`.
-/
theorem covolume_inReal_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r p0 : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (γ : GL (Fin r) E) (Δ : Subgroup (GL (Fin r) E)), (∀ a b, cc (G a b) = G b a) → (∀ τ : Ψ, gram τ.1 G (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) → (∀ u v, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → covolume (inReal Ψ G (Δ.map (MulAut.conj γ).toMonoidHom)) (realSU Ψ G) (riemHaar Ψ G x) = covolume (inReal Ψ G Δ) (realSU Ψ G) (riemHaar Ψ G x) := by
  intro E _ _ _ r p0 Ψ G x γ Δ _hG hx hγ
  set A : Ψ → GL (Fin r) ℂ := embGL Ψ r γ with hAdef
  have hAv : ∀ τ : Ψ, ((A τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1 := fun τ => rfl
  have hA : ∀ τ : Ψ, ∀ u w, hermC τ.1 G ((A τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ u)
      ((A τ : Matrix (Fin r) (Fin r) ℂ) *ᵥ w) = hermC τ.1 G u w := by
    intro τ u w; rw [hAv]; exact hermC_map_of_herm τ.1 G _ hγ u w
  have hdet : ∀ τ : Ψ, (A τ : Matrix (Fin r) (Fin r) ℂ).det *
      starRingEnd ℂ (A τ : Matrix (Fin r) (Fin r) ℂ).det = 1 := by
    intro τ
    have hg : (G.map τ.1).det ≠ 0 := by
      intro h0
      have h1 := congrArg Matrix.det (hx τ)
      rw [det_gram, h0, mul_zero, zero_mul, det_diagonal] at h1
      refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
      simp only [sgn]; split_ifs <;> norm_num
    have e1 : ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (A τ : Matrix (Fin r) (Fin r) ℂ) =
        ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G 1 := by
      ext a b
      simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, Matrix.of_apply]
      rw [col_eq_mulVec (A τ : Matrix (Fin r) (Fin r) ℂ) a, col_eq_mulVec (A τ : Matrix (Fin r) (Fin r) ℂ) b, hA]
    have h2 := congrArg Matrix.det e1
    rw [det_gram, det_gram, det_one, map_one, one_mul, mul_one] at h2
    apply mul_right_cancel₀ hg
    linear_combination h2
  have hroot : ∀ τ : Ψ, ∃ m : ℂ, m ^ r = (A τ : Matrix (Fin r) (Fin r) ℂ).det ∧ m * starRingEnd ℂ m = 1 := by
    intro τ
    rcases Nat.eq_zero_or_pos r with hr | hr
    · refine ⟨1, ?_, by simp⟩
      subst hr; simp
    · obtain ⟨m, hm⟩ := IsAlgClosed.exists_pow_nat_eq ((A τ : Matrix (Fin r) (Fin r) ℂ).det) hr
      refine ⟨m, hm, ?_⟩
      have h1 : (m * starRingEnd ℂ m) ^ r = 1 := by rw [mul_pow, ← map_pow, hm, hdet τ]
      rw [Complex.mul_conj] at h1 ⊢
      have h3 : (Complex.normSq m) ^ r = 1 := by exact_mod_cast h1
      rw [(pow_eq_one_iff_of_nonneg (Complex.normSq_nonneg m) hr.ne').1 h3]; simp
  choose m hm using hroot
  have hm0 : ∀ τ, m τ ≠ 0 := fun τ h => by simpa [h] using (hm τ).2
  let z : Ψ → GL (Fin r) ℂ := fun τ =>
    Units.map (algebraMap ℂ (Matrix (Fin r) (Fin r) ℂ)).toMonoidHom (Units.mk0 (m τ)⁻¹ (inv_ne_zero (hm0 τ)))
  have hzv : ∀ τ, ((z τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (m τ)⁻¹ • (1 : Matrix (Fin r) (Fin r) ℂ) := by
    intro τ; simp [z, Algebra.algebraMap_eq_smul_one]
  have hzc : ∀ g : Ψ → GL (Fin r) ℂ, z * g = g * z := by
    intro g; funext τ; ext1
    simp only [Pi.mul_apply, Units.val_mul, hzv, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hs0 : A * z ∈ realSU Ψ G := by
    intro τ
    have e : (((A * z) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
        (m τ)⁻¹ • (A τ : Matrix (Fin r) (Fin r) ℂ) := by
      simp only [Pi.mul_apply, Units.val_mul, hzv, Matrix.mul_smul, mul_one]
    rw [e]
    refine ⟨?_, fun u w => ?_⟩
    · rw [det_smul, Fintype.card_fin, inv_pow, (hm τ).1]
      have : (A τ : Matrix (Fin r) (Fin r) ℂ).det ≠ 0 := fun h => by simpa [h] using hdet τ
      exact inv_mul_cancel₀ this
    · rw [Matrix.smul_mulVec, Matrix.smul_mulVec, hermC_smul, hA, map_inv₀, ← mul_inv,
        (hm τ).2, inv_one, one_mul]
  let s : realSU Ψ G := ⟨A * z, hs0⟩
  have hconj : ∀ g : Ψ → GL (Fin r) ℂ, (A * z)⁻¹ * g * (A * z) = A⁻¹ * g * A := by
    intro g
    calc (A * z)⁻¹ * g * (A * z) = z⁻¹ * (A⁻¹ * g * A) * z := by group
      _ = z⁻¹ * (z * (A⁻¹ * g * A)) := by rw [mul_assoc, ← hzc]
      _ = A⁻¹ * g * A := by group
  haveI := countable_inReal Ψ G Δ
  haveI := countable_inReal Ψ G (Δ.map (MulAut.conj γ).toMonoidHom)
  haveI : (riemHaar Ψ G x).IsMulLeftInvariant := by unfold riemHaar; infer_instance
  haveI : SFinite (riemHaar Ψ G x) := by unfold riemHaar tangentHaar; infer_instance
  have key : ∀ δ, embGL Ψ r ((MulAut.conj γ).toMonoidHom δ) = A * embGL Ψ r δ * A⁻¹ := by
    intro δ; simp [hAdef, MulAut.conj_apply, map_mul, map_inv]
  refine covolume_conj (riemHaar Ψ G x) _ _ s fun g => ?_
  simp only [inReal, Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hconj]
  constructor
  · rintro ⟨δ', ⟨δ, hδ, rfl⟩, h⟩
    refine ⟨δ, hδ, ?_⟩
    rw [← h, key]
    group
  · rintro ⟨δ, hδ, h⟩
    refine ⟨_, ⟨δ, hδ, rfl⟩, ?_⟩
    rw [key, h]
    group

end GlobalTheory.SUCovolConj
end
