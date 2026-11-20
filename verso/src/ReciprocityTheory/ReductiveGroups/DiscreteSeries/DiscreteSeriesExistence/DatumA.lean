import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.SingleMulJmComm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.MeasurePreservingMulRight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Unfold `inUJ at hg hh ⊢`. Establish `e : (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[e, hg, hh]`.
-/
theorem pdA_inUJ_mul {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hh : inUJ ε h) :
    inUJ ε (g * h) := by
  unfold inUJ at hg hh ⊢
  have e : (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hg, hh]

/- English proof (translation)
Unfold `inUJ`. Establish `h1 : star k * k = 1` using `Unitary.star_mul_self_of_mem hk.1`. Rewrite `h1` using `[Matrix.star_eq_conjTranspose]`. Rewrite using `[Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.
-/
theorem pdA_inUJ_of_Kset {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : inUJ ε k := by
  unfold inUJ
  have h1 : star k * k = 1 := Unitary.star_mul_self_of_mem hk.1
  rw [Matrix.star_eq_conjTranspose] at h1
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

def pdA_kg {ε : Fin n → Bool} (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε) : S7.KG ε :=
  ⟨⟨⟨k, star k, Unitary.mul_star_self_of_mem hk.1, Unitary.star_mul_self_of_mem hk.1⟩, pdA_inUJ_of_Kset hk⟩, hk⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pdA_toMK_kg {ε : Fin n → Bool} (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε) :
    S7.toMK (pdA_kg k hk) = k := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pdA_toMK_one (ε : Fin n → Bool) : S7.toMK (1 : S7.KG ε) = 1 := rfl

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.
-/
private theorem Jm_mul_self_eq_one' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

/- English proof (translation)
Unfold `Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.star_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem Jm_conjTranspose_eq_self' (ε : Fin n → Bool) : (Jm ε)ᴴ = Jm ε := by
  unfold Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  simp only [Pi.star_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `hJJ` using `Jm_mul_self_eq_one' ε`. Establish `hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hJJ, Matrix.one_mul]`. Establish `hU : IsUnit (Jm ε)` using `⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩`. Establish `hinv : (Jm ε)⁻¹ = Jm ε` using `Matrix.inv_eq_left_inv hJJ`.

Establish `h0 : Aᴴ * Jm ε = -(Jm ε * A)`. Unfold `inG at hA`. Conclude with `eq_neg_of_add_eq_zero_left hA`. Establish `hAH : Aᴴ = Jm ε * (-A) * (Jm ε)⁻¹`. Rewrite using `[hinv]`.

Combine the equalities or inequalities in the displayed calculation. Establish `h1 : NormedSpace.exp (-A) * NormedSpace.exp A = 1`. Rewrite using `[← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]`. Unfold `inUJ`. Rewrite using `[← Matrix.exp_conjTranspose, hAH, Matrix.exp_conj _ _ hU, hinv]`.

Simplify using `only [Matrix.mul_assoc, hJJ']`. Rewrite using `[h1, Matrix.mul_one]`.
-/
private theorem inUJ_exp_of_inG' {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (hA : inG ε A) :
    inUJ ε (NormedSpace.exp A) := by
  have hJJ := Jm_mul_self_eq_one' ε
  have hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hU : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have h0 : Aᴴ * Jm ε = -(Jm ε * A) := by
    unfold inG at hA
    exact eq_neg_of_add_eq_zero_left hA
  have hAH : Aᴴ = Jm ε * (-A) * (Jm ε)⁻¹ := by
    rw [hinv]
    calc Aᴴ = Aᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = Jm ε * (-A) * Jm ε := by rw [h0, Matrix.mul_neg, Matrix.neg_mul]
  have h1 : NormedSpace.exp (-A) * NormedSpace.exp A = 1 := by
    rw [← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_left, neg_add_cancel, NormedSpace.exp_zero]
  unfold inUJ
  rw [← Matrix.exp_conjTranspose, hAH, Matrix.exp_conj _ _ hU, hinv]
  simp only [Matrix.mul_assoc, hJJ']
  rw [h1, Matrix.mul_one]

/- English proof (translation)
Establish `hX' : ∀ t : ℝ, inG ε ((t : ℂ) • X)` using `fun t => by`. Unfold `inG at hX ⊢`. Simplify using `only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul]`. Rewrite using `[← smul_add, hX, smul_zero]`. Establish `e : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) = fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X))`.

Use function extensionality and compare the values at `fun t => he _ (pdA_inUJ_mul hg (inUJ_exp_of_inG' (hX' t)))`. Simplify using `only [Formalism.REAL.RdV]`. Rewrite using `[e]`.
-/
theorem pdA_rdV_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (he : ∀ h, inUJ ε h → f h = f' h) {X g : Matrix (Fin n) (Fin n) ℂ}
    (hX : inG ε X) (hg : inUJ ε g) : Formalism.REAL.RdV X f g = Formalism.REAL.RdV X f' g := by
  have hX' : ∀ t : ℝ, inG ε ((t : ℂ) • X) := fun t => by
    unfold inG at hX ⊢
    simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [← smul_add, hX, smul_zero]
  have e : (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X)) :=
    funext fun t => he _ (pdA_inUJ_mul hg (inUJ_exp_of_inG' (hX' t)))
  simp only [Formalism.REAL.RdV]
  rw [e]

/- English proof (translation)
Establish `hJJ` using `Jm_mul_self_eq_one' ε`. Establish `hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hJJ, Matrix.one_mul]`. Establish `hJH` using `Jm_conjTranspose_eq_self' ε`. Establish `hJr : Formalism.REAL.Jm ε = Jm ε` using `rfl`.

Establish `hs1 : star (1 / 2 : ℂ) = 1 / 2` using `by simp [Complex.star_def]`. Establish `hs2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I))` using `by simp [Complex.star_def]`. Unfold `inG Formalism.REAL.cpart1 Formalism.REAL.cpart2`. Simplify using `only [hJr, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_add, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJH, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, add_mul, mul_add, Matrix.mul_assoc, hJJ, hJJ', mul_one]`. Rewrite using `[hs1, hs2]`.

Apply the tactic sequence `constructor <;> module`.
-/
private theorem inG_cpart1_and_inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inG ε (Formalism.REAL.cpart1 ε Z) ∧ inG ε (Formalism.REAL.cpart2 ε Z) := by
  have hJJ := Jm_mul_self_eq_one' ε
  have hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hJH := Jm_conjTranspose_eq_self' ε
  have hJr : Formalism.REAL.Jm ε = Jm ε := rfl
  have hs1 : star (1 / 2 : ℂ) = 1 / 2 := by simp [Complex.star_def]
  have hs2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by simp [Complex.star_def]
  unfold inG Formalism.REAL.cpart1 Formalism.REAL.cpart2
  simp only [hJr, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_add,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJH, Matrix.smul_mul, Matrix.mul_smul,
    sub_mul, mul_sub, add_mul, mul_add, Matrix.mul_assoc, hJJ, hJJ', mul_one]
  rw [hs1, hs2]
  constructor <;> module

/- English proof (translation)
Take `⟨h1, h2⟩` from `inG_cpart1_and_inG_cpart2 ε (Matrix.single a b (1 : ℂ))`. Simplify using `only [Formalism.REAL.EabV, Formalism.REAL.EcV]`. Rewrite using `[pdA_rdV_congr he h1 hg, pdA_rdV_congr he h2 hg]`.
-/
theorem pdA_eabV_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (he : ∀ h, inUJ ε h → f h = f' h) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : Formalism.REAL.EabV ε a b f g = Formalism.REAL.EabV ε a b f' g := by
  obtain ⟨h1, h2⟩ := inG_cpart1_and_inG_cpart2 ε (Matrix.single a b (1 : ℂ))
  simp only [Formalism.REAL.EabV, Formalism.REAL.EcV]
  rw [pdA_rdV_congr he h1 hg, pdA_rdV_congr he h2 hg]

/- English proof (translation)
Unfold `Formalism.REAL.SmoothOnGV at *`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g₀ hg₀`. Take `⟨U', F', hU', hgU', hF', hfF'⟩` from `hf' g₀ hg₀`. Use `⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)`. Introduce `g hg hgJ show f g + c • f' g = F g + c • F' g`. Rewrite using `[hfF g hg.1 hgJ, hfF' g hg.2 hgJ]`.
-/
theorem pdA_smooth_add_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    {f f' : Matrix (Fin n) (Fin n) ℂ → E} (c : ℂ) (hf : Formalism.REAL.SmoothOnGV ε f) (hf' : Formalism.REAL.SmoothOnGV ε f') :
    Formalism.REAL.SmoothOnGV ε (fun x => f x + c • f' x) := by
  unfold Formalism.REAL.SmoothOnGV at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩, ?_, ?_⟩
  · exact (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c)
  · intro g hg hgJ
    show f g + c • f' g = F g + c • F' g
    rw [hfF g hg.1 hgJ, hfF' g hg.2 hgJ]

/- English proof (translation)
Take `⟨h1, h2⟩` from `inG_cpart1_and_inG_cpart2 ε (Matrix.single a b (1 : ℂ))`. Conclude with `pdA_smooth_add_smul Complex.I (Formalism.REAL.rdSmoothV n ε E f _ hf h1) (Formalism.REAL.rdSmoothV n ε E f _ hf h2)`.
-/
theorem pdA_smooth_eabV {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : Formalism.REAL.SmoothOnGV ε f) (a b : Fin n) :
    Formalism.REAL.SmoothOnGV ε (Formalism.REAL.EabV ε a b f) := by
  obtain ⟨h1, h2⟩ := inG_cpart1_and_inG_cpart2 ε (Matrix.single a b (1 : ℂ))
  exact pdA_smooth_add_smul Complex.I (Formalism.REAL.rdSmoothV n ε E f _ hf h1)
    (Formalism.REAL.rdSmoothV n ε E f _ hf h2)

/- English proof (translation)
Take `⟨h1, h2⟩` from `inG_cpart1_and_inG_cpart2 ε (Matrix.single a b (1 : ℂ))`. Unfold `Formalism.REAL.SmoothOnGV at hf`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g hg`. Establish `key : ∀ X, inG ε X → φ (Formalism.REAL.RdV X f g) = Formalism.REAL.Rd X (fun x => φ (f x)) g`. Introduce `X hX`.

Establish `hd` using `smBr_hasDerivAt_ext f F U g X hU hgU hg hF hfF hX`. Establish `hd' : HasDerivAt (fun t : ℝ => φ (f (g * NormedSpace.exp ((t : ℂ) • X)))) (φ (fderiv ℝ F g (g * X))) 0` using `(φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd`. Simplify using `only [Formalism.REAL.RdV, Formalism.REAL.Rd]`. Rewrite using `[hd.deriv, hd'.deriv]`. Simplify using `only [Formalism.REAL.EabV, Formalism.REAL.EcV, Formalism.REAL.Eab, Formalism.REAL.Ec, map_add, map_smul, smul_eq_mul]`.

Rewrite using `[key _ h1, key _ h2]`.
-/
theorem pdA_eabV_clm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    (φ : E →L[ℂ] ℂ) {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : Formalism.REAL.SmoothOnGV ε f) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    φ (Formalism.REAL.EabV ε a b f g) = Formalism.REAL.Eab ε a b (fun x => φ (f x)) g := by
  obtain ⟨h1, h2⟩ := inG_cpart1_and_inG_cpart2 ε (Matrix.single a b (1 : ℂ))
  unfold Formalism.REAL.SmoothOnGV at hf
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have key : ∀ X, inG ε X → φ (Formalism.REAL.RdV X f g) = Formalism.REAL.Rd X (fun x => φ (f x)) g := by
    intro X hX
    have hd := smBr_hasDerivAt_ext f F U g X hU hgU hg hF hfF hX
    have hd' : HasDerivAt (fun t : ℝ => φ (f (g * NormedSpace.exp ((t : ℂ) • X))))
        (φ (fderiv ℝ F g (g * X))) 0 :=
      (φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
    simp only [Formalism.REAL.RdV, Formalism.REAL.Rd]
    rw [hd.deriv, hd'.deriv]
  simp only [Formalism.REAL.EabV, Formalism.REAL.EcV, Formalism.REAL.Eab, Formalism.REAL.Ec, map_add, map_smul, smul_eq_mul]
  rw [key _ h1, key _ h2]

/- English proof (translation)
Establish `hE : ∀ (F : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n), S7.EabV ε a b F = Formalism.REAL.EabV ε a b F` using `fun _ _ _ => rfl`. Simplify using `only [Formalism.REAL.CasF, S7.casimirV, map_sum, hE]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[pdA_eabV_clm φ (pdA_smooth_eabV hf b a) a b hg]`. Conclude with `pdA_eabV_congr (f := Formalism.REAL.Eab ε b a fun x => φ (f x)) (fun h hh => (pdA_eabV_clm φ hf b a hh).symm) a b hg`.
-/
theorem pdA_casF_clm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    (φ : E →L[ℂ] ℂ) {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : Formalism.REAL.SmoothOnGV ε f)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Formalism.REAL.CasF ε (fun x => φ (f x)) g = φ (S7.casimirV ε f g) := by
  have hE : ∀ (F : Matrix (Fin n) (Fin n) ℂ → E) (a b : Fin n),
      S7.EabV ε a b F = Formalism.REAL.EabV ε a b F := fun _ _ _ => rfl
  simp only [Formalism.REAL.CasF, S7.casimirV, map_sum, hE]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [pdA_eabV_clm φ (pdA_smooth_eabV hf b a) a b hg]
  exact pdA_eabV_congr (f := Formalism.REAL.Eab ε b a fun x => φ (f x))
    (fun h hh => (pdA_eabV_clm φ hf b a hh).symm) a b hg

/- English proof (translation)
Unfold `Formalism.REAL.SmoothOnGV at hf`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g₀ hg₀`. Establish `hFc : ContinuousAt F g₀` using `hF.continuousOn.continuousAt (hU.mem_nhds hgU)`. Use `hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hgU hg₀)` and prove the remaining obligations.

Use `filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgJ`. Conclude with `hfF g hgU' hgJ`.
-/
theorem pdA_continuousOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ε : Fin n → Bool}
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : Formalism.REAL.SmoothOnGV ε f) : ContinuousOn f (UJset ε) := by
  unfold Formalism.REAL.SmoothOnGV at hf
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := hF.continuousOn.continuousAt (hU.mem_nhds hgU)
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hfF g₀ hgU hg₀)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hgU), self_mem_nhdsWithin] with g hgU' hgJ
  exact hfF g hgU' hgJ

def pdA_coef {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (v₀ v : V) : (V →L[ℂ] V) →L[ℂ] ℂ :=
  (innerSL ℂ v₀).comp (ContinuousLinearMap.apply ℂ V v)

/- English proof (translation)
Unfold `Formalism.REAL.SmoothOnGV at *`. Introduce `g₀ hg₀`. Take `⟨U, F, hU, hgU, hF, hfF⟩` from `hf g₀ hg₀`. Use `⟨U, fun x => φ (F x), hU, hgU, ?_, fun g hg hgJ => by simp only [hfF g hg hgJ]⟩` and prove the remaining obligations. Conclude with `(φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF`.
-/
theorem pdA_smooth_clm {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] {ε : Fin n → Bool} (φ : E →L[ℂ] E') {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : Formalism.REAL.SmoothOnGV ε f) : Formalism.REAL.SmoothOnGV ε (fun x => φ (f x)) := by
  unfold Formalism.REAL.SmoothOnGV at *
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun x => φ (F x), hU, hgU, ?_, fun g hg hgJ => by simp only [hfF g hg hgJ]⟩
  exact (φ.restrictScalars ℝ).contDiff.comp_contDiffOn hF

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem pdA_single_comm {ε : Fin n → Bool} {a b : Fin n} (hab : ε a = ε b) :
    Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
  ext i j
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
  split_ifs <;> simp_all

/- English proof (translation)
Establish `hJJ` using `Jm_mul_self_eq_one' ε`. Establish `hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hJJ, Matrix.one_mul]`. Establish `hZH : Zᴴ * Jm ε = Jm ε * Zᴴ`. Establish `e` using `congrArg Matrix.conjTranspose hZ`.

Simplify using `only [Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self'] at e`. Conclude with `e.symm`. Establish `hJr : Formalism.REAL.Jm ε = Jm ε` using `rfl`. Use `⟨⟨(inG_cpart1_and_inG_cpart2 ε Z).1, ?_⟩, ⟨(inG_cpart1_and_inG_cpart2 ε Z).2, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [Formalism.REAL.cpart1, hJr, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, Matrix.mul_assoc, hJJ, hJJ', mul_one, hZ, hZH]`.

Simplify using `only [Formalism.REAL.cpart2, hJr, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, Matrix.mul_assoc, hJJ, hJJ', mul_one, hZ, hZH]`.
-/
theorem pdA_inK_cpart {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z * Jm ε = Jm ε * Z) :
    inK ε (Formalism.REAL.cpart1 ε Z) ∧ inK ε (Formalism.REAL.cpart2 ε Z) := by
  have hJJ := Jm_mul_self_eq_one' ε
  have hJJ' : ∀ X : Matrix (Fin n) (Fin n) ℂ, Jm ε * (Jm ε * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hZH : Zᴴ * Jm ε = Jm ε * Zᴴ := by
    have e := congrArg Matrix.conjTranspose hZ
    simp only [Matrix.conjTranspose_mul, Jm_conjTranspose_eq_self'] at e
    exact e.symm
  have hJr : Formalism.REAL.Jm ε = Jm ε := rfl
  refine ⟨⟨(inG_cpart1_and_inG_cpart2 ε Z).1, ?_⟩, ⟨(inG_cpart1_and_inG_cpart2 ε Z).2, ?_⟩⟩
  · simp only [Formalism.REAL.cpart1, hJr, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, Matrix.mul_assoc,
      hJJ, hJJ', mul_one, hZ, hZH]
  · simp only [Formalism.REAL.cpart2, hJr, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, Matrix.mul_assoc,
      hJJ, hJJ', mul_one, hZ, hZH]

/- English proof (translation)
Take `⟨h1, h2⟩` from `hX`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Unfold `inG at h1 ⊢`. Simplify using `only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul]`. Rewrite using `[← smul_add, h1, smul_zero]`.

Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, h2]`.
-/
theorem pdA_inK_smul {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    inK ε ((t : ℂ) • X) := by
  obtain ⟨h1, h2⟩ := hX
  refine ⟨?_, ?_⟩
  · unfold inG at h1 ⊢
    simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul]
    rw [← smul_add, h1, smul_zero]
  · rw [Matrix.smul_mul, Matrix.mul_smul, h2]

/- English proof (translation)
Simplify using `[S7.KType.op]`.
-/
theorem pdA_op_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) : T.op 1 = 1 := by
  simp [S7.KType.op]

/- English proof (translation)
Establish `hJJ` using `Jm_mul_self_eq_one' ε`. Establish `hU : IsUnit (Jm ε)` using `⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩`. Establish `hinv : (Jm ε)⁻¹ = Jm ε` using `Matrix.inv_eq_left_inv hJJ`. Take `⟨hG, hC⟩` from `pdA_inK_smul hX t`. Use `set A := (t : ℂ) • X with hAdef`.

Establish `h0 : Aᴴ * Jm ε = -(Jm ε * A)`. Unfold `inG at hG`. Conclude with `eq_neg_of_add_eq_zero_left hG`. Establish `hAH : Aᴴ = -A`. Combine the equalities or inequalities in the displayed calculation.

Establish `hconj : Jm ε * A * (Jm ε)⁻¹ = A`. Rewrite using `[hinv, ← hC, Matrix.mul_assoc, hJJ, Matrix.mul_one]`. Unfold `Kset`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hAH, ← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_right, add_neg_cancel, NormedSpace.exp_zero]`.

Establish `e` using `Matrix.exp_conj (Jm ε) A hU`. Rewrite `e` using `[hconj, hinv]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem exp_smul_mem_Kset_of_inK {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := by
  have hJJ := Jm_mul_self_eq_one' ε
  have hU : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  obtain ⟨hG, hC⟩ := pdA_inK_smul hX t
  set A := (t : ℂ) • X with hAdef
  have h0 : Aᴴ * Jm ε = -(Jm ε * A) := by
    unfold inG at hG
    exact eq_neg_of_add_eq_zero_left hG
  have hAH : Aᴴ = -A := by
    calc Aᴴ = Aᴴ * Jm ε * Jm ε := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]
      _ = -A := by rw [h0, ← hC, Matrix.neg_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hconj : Jm ε * A * (Jm ε)⁻¹ = A := by
    rw [hinv, ← hC, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  unfold Kset
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hAH,
      ← Matrix.exp_add_of_commute _ _ (Commute.refl A).neg_right, add_neg_cancel, NormedSpace.exp_zero]
  · have e := Matrix.exp_conj (Jm ε) A hU
    rw [hconj, hinv] at e
    calc NormedSpace.exp A * Jm ε = Jm ε * NormedSpace.exp A * Jm ε * Jm ε := by rw [← e]
      _ = Jm ε * NormedSpace.exp A := by rw [Matrix.mul_assoc, hJJ, Matrix.mul_one]

/- English proof (translation)
Establish `hexp` using `exp_smul_mem_Kset_of_inK hX`. Set `γ : ℝ → S7.KG ε` to `fun t => pdA_kg (NormedSpace.exp ((t : ℂ) • X)) (hexp t)`. Establish `hγ : ∀ t, S7.toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)` using `fun t => pdA_toMK_kg _ _`. Establish `hd` using `T.hasDeriv X hX γ hγ`. Set `L : (T.V →L[ℂ] T.V) →L[ℂ] ℂ` to `((innerSL ℂ v₀).comp (Ψ g)).comp (ContinuousLinearMap.apply ℂ T.V v)`.

Establish `hf : (fun t : ℝ => inner ℂ v₀ (Ψ (g * NormedSpace.exp ((t : ℂ) • X)) v)) = fun t : ℝ => L (T.op (γ t))`. Use function extensionality and compare the values at `t`. Establish `e` using `hΨ 1 (γ t) g hg`. Rewrite `e` using `[pdA_toMK_one, hγ t, Matrix.one_mul, pdA_op_one, one_mul]`. Rewrite using `[e]`.

Both sides reduce to the same expression. Establish `hd2 : HasDerivAt (fun t : ℝ => L (T.op (γ t))) (L (T.dτ X)) 0` using `(L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd`. Simplify using `only [Formalism.REAL.RdV]`. Rewrite using `[hf, hd2.deriv]`. Both sides reduce to the same expression.
-/
theorem pdA_rdV_compact {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hΨ : ∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂)
    (v₀ v : T.V) {X g : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (hg : inUJ ε g) :
    Formalism.REAL.RdV X (fun x => inner ℂ v₀ (Ψ x v)) g = inner ℂ v₀ (Ψ g (T.dτ X v)) := by
  have hexp := exp_smul_mem_Kset_of_inK hX
  let γ : ℝ → S7.KG ε := fun t => pdA_kg (NormedSpace.exp ((t : ℂ) • X)) (hexp t)
  have hγ : ∀ t, S7.toMK (γ t) = NormedSpace.exp ((t : ℂ) • X) := fun t => pdA_toMK_kg _ _
  have hd := T.hasDeriv X hX γ hγ
  let L : (T.V →L[ℂ] T.V) →L[ℂ] ℂ :=
    ((innerSL ℂ v₀).comp (Ψ g)).comp (ContinuousLinearMap.apply ℂ T.V v)
  have hf : (fun t : ℝ => inner ℂ v₀ (Ψ (g * NormedSpace.exp ((t : ℂ) • X)) v)) =
      fun t : ℝ => L (T.op (γ t)) := by
    funext t
    have e := hΨ 1 (γ t) g hg
    rw [pdA_toMK_one, hγ t, Matrix.one_mul, pdA_op_one, one_mul] at e
    rw [e]
    rfl
  have hd2 : HasDerivAt (fun t : ℝ => L (T.op (γ t))) (L (T.dτ X)) 0 :=
    (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd
  simp only [Formalism.REAL.RdV]
  rw [hf, hd2.deriv]
  rfl

/- English proof (translation)
Take `⟨h1, h2⟩` from `pdA_inK_cpart (pdA_single_comm (ε := ε) hab)`. Establish `e1 : Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) (fun x => inner ℂ v₀ (Ψ x v)) g = inner ℂ v₀ (Ψ g (T.dτ (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) v))` using `pdA_rdV_compact T hΨ v₀ v h1 hg`. Establish `e2 : Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) (fun x => inner ℂ v₀ (Ψ x v)) g = inner ℂ v₀ (Ψ g (T.dτ (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) v))` using `pdA_rdV_compact T hΨ v₀ v h2 hg`. Establish `hZ : Matrix.single a b (1 : ℂ) = Formalism.REAL.cpart1 ε (Matrix.single a b 1) + Complex.I • Formalism.REAL.cpart2 ε (Matrix.single a b 1)`. Unfold `Formalism.REAL.cpart1 Formalism.REAL.cpart2`.

Rewrite using `[smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp]`. Use `module`. Simplify using `only [Formalism.REAL.Eab, Formalism.REAL.Ec]`. Rewrite using `[e1, e2]`. Use `conv_rhs => rw [hZ]`.

Simplify using `only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, inner_add_right, inner_smul_right]`.
-/
theorem pdA_eab_compact {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}
    (hΨ : ∀ (k₁ k₂ : S7.KG ε) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Ψ (S7.toMK k₁ * g * S7.toMK k₂) = T.op k₁ * Ψ g * T.op k₂)
    (v₀ v : T.V) {a b : Fin n} (hab : ε a = ε b) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => inner ℂ v₀ (Ψ x v)) g = inner ℂ v₀ (Ψ g (T.dτ (Matrix.single a b 1) v)) := by
  obtain ⟨h1, h2⟩ := pdA_inK_cpart (pdA_single_comm (ε := ε) hab)
  have e1 : Formalism.REAL.Rd (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) (fun x => inner ℂ v₀ (Ψ x v)) g =
      inner ℂ v₀ (Ψ g (T.dτ (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) v)) :=
    pdA_rdV_compact T hΨ v₀ v h1 hg
  have e2 : Formalism.REAL.Rd (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) (fun x => inner ℂ v₀ (Ψ x v)) g =
      inner ℂ v₀ (Ψ g (T.dτ (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) v)) :=
    pdA_rdV_compact T hΨ v₀ v h2 hg
  have hZ : Matrix.single a b (1 : ℂ) = Formalism.REAL.cpart1 ε (Matrix.single a b 1) +
      Complex.I • Formalism.REAL.cpart2 ε (Matrix.single a b 1) := by
    unfold Formalism.REAL.cpart1 Formalism.REAL.cpart2
    rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp]
    module
  simp only [Formalism.REAL.Eab, Formalism.REAL.Ec]
  rw [e1, e2]
  conv_rhs => rw [hZ]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_right, inner_smul_right]

open scoped Classical in

/- English proof (translation)
Establish `hfg : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g)`. Use function extensionality and compare the values at `fun g => h (Formalism.MainNotions.S.umat g) g.2`. Unfold `toL2`. Simplify using `only [hfg]`.
-/
theorem toL2_congr_of_forall_inUJ_eq {ε : Fin n → Bool} {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → F g = G g) : toL2 ε F = toL2 ε G := by
  have hfg : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g) :=
    funext fun g => h (Formalism.MainNotions.S.umat g) g.2
  unfold toL2
  simp only [hfg]

/- English proof (translation)
Establish `key : ∀ (H : Matrix (Fin n) (Fin n) ℂ → ℂ) (hH : MemLp (fun g : Formalism.REAL.UJ ε => H (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)), toL2 ε H = hH.toLp _` using `fun H hH => by`. Unfold `toL2`. Rewrite using `[dif_pos hH]`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Simplify using `only [Finset.sum_empty]`. Unfold `toL2`. Use `split_ifs with h`. Conclude with `MemLp.toLp_zero h`. Both sides reduce to the same expression.

Consider the case `@insert j s hj ih`. Establish `hG : MemLp (fun g : Formalism.REAL.UJ ε => (fun x => ∑ i ∈ s, F i x) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)` using `memLp_finset_sum s (fun i _ => hF i)`. Rewrite using `[Finset.sum_insert hj, ← ih]`. Establish `e : (fun x => ∑ i ∈ insert j s, F i x) = fun x => F j x + ∑ i ∈ s, F i x`. Use function extensionality and compare the values at `x`.

Conclude with `Finset.sum_insert hj`. Rewrite using `[e, key (fun x => F j x + ∑ i ∈ s, F i x) ((hF j).add hG), key (F j) (hF j), key (fun x => ∑ i ∈ s, F i x) hG]`. Conclude with `MemLp.toLp_add (hF j) hG`.
-/
theorem toL2_finset_sum_of_memLp {ε : Fin n → Bool} {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, MemLp (fun g : Formalism.REAL.UJ ε => F i (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    toL2 ε (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, toL2 ε (F i) := by
  classical
  have key : ∀ (H : Matrix (Fin n) (Fin n) ℂ → ℂ)
      (hH : MemLp (fun g : Formalism.REAL.UJ ε => H (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)),
      toL2 ε H = hH.toLp _ := fun H hH => by
    unfold toL2
    rw [dif_pos hH]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold toL2
    split_ifs with h
    · exact MemLp.toLp_zero h
    · rfl
  | @insert j s hj ih =>
    have hG : MemLp (fun g : Formalism.REAL.UJ ε => (fun x => ∑ i ∈ s, F i x) (Formalism.MainNotions.S.umat g)) 2
        (Formalism.REAL.muG ε) := memLp_finset_sum s (fun i _ => hF i)
    rw [Finset.sum_insert hj, ← ih]
    have e : (fun x => ∑ i ∈ insert j s, F i x) = fun x => F j x + ∑ i ∈ s, F i x := by
      funext x
      exact Finset.sum_insert hj
    rw [e, key (fun x => F j x + ∑ i ∈ s, F i x) ((hF j).add hG), key (F j) (hF j),
      key (fun x => ∑ i ∈ s, F i x) hG]
    exact MemLp.toLp_add (hF j) hG

end ReciprocityTheory.ChartRestriction.DS
