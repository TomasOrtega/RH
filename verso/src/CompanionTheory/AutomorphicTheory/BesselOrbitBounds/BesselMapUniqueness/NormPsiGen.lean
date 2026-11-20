import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix MeasureTheory Formalism.QuantumDeterminants CompanionTheory.D.Upq.Sm
open scoped ContDiff InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.Bmu

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Set `b` to `Module.finBasis ℝ S`. Use `⟨_, fun j => (b j : Mat n), fun j => (b j).2, fun Y hY => ⟨fun j => b.repr ⟨Y, hY⟩ j, ?_⟩⟩` and prove the remaining obligations. Establish `h` using `congrArg (Subtype.val) (b.sum_repr ⟨Y, hY⟩)`. Simplify using `only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h`. Simplify using `only [Complex.coe_smul]`.

Conclude with `h.symm`.
-/
theorem spanFam {n : ℕ} (S : Submodule ℝ (Mat n)) : ∃ (d : ℕ) (X : Fin d → Mat n), (∀ j, X j ∈ S) ∧
    ∀ Y ∈ S, ∃ a : Fin d → ℝ, Y = ∑ j, (a j : ℂ) • X j := by
  let b := Module.finBasis ℝ S
  refine ⟨_, fun j => (b j : Mat n), fun j => (b j).2, fun Y hY => ⟨fun j => b.repr ⟨Y, hY⟩ j, ?_⟩⟩
  have h := congrArg (Subtype.val) (b.sum_repr ⟨Y, hY⟩)
  simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
  simp only [Complex.coe_smul]
  exact h.symm

/- English proof (translation)
Unfold `Lie at *`. Rewrite using `[conjTranspose_add, Matrix.add_mul, Matrix.mul_add]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lie_add {n : ℕ} {Hm X Y : Mat n} (hX : Lie Hm X) (hY : Lie Hm Y) : Lie Hm (X + Y) := by
  unfold Lie at *
  rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
  calc Xᴴ * Hm + Yᴴ * Hm + (Hm * X + Hm * Y) = (Xᴴ * Hm + Hm * X) + (Yᴴ * Hm + Hm * Y) := by abel
    _ = 0 := by rw [hX, hY, add_zero]

/- English proof (translation)
Unfold `Lie at *`. Rewrite using `[conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]`.
-/
theorem lie_smul {n : ℕ} {Hm X : Mat n} (c : ℝ) (hX : Lie Hm X) : Lie Hm (c • X) := by
  unfold Lie at *
  rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX, smul_zero]

/- English proof (translation)
Simplify using `[Lie]`.
-/
theorem lie_zero {n : ℕ} (Hm : Mat n) : Lie Hm 0 := by simp [Lie]

variable {k r : ℕ}

def sUw (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InUw k r z X}
  zero_mem' := ⟨lie_zero _, fun _ => ⟨zero_mulVec _, zero_mulVec _⟩, zero_mulVec _⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun a =>
    ⟨by rw [add_mulVec, (hX.2.1 a).1, (hY.2.1 a).1, add_zero], by rw [add_mulVec, (hX.2.1 a).2, (hY.2.1 a).2, add_zero]⟩,
    by rw [add_mulVec, hX.2.2, hY.2.2, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun a =>
    ⟨by rw [smul_mulVec, (hX.2.1 a).1, smul_zero], by rw [smul_mulVec, (hX.2.1 a).2, smul_zero]⟩,
    by rw [smul_mulVec, hX.2.2, smul_zero]⟩

def sN (k r : ℕ) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InN k r X}
  zero_mem' := ⟨lie_zero _, fun _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun a i h => by
    rw [Matrix.add_apply, hX.2.1 a i h, hY.2.1 a i h, add_zero], fun i j h1 h2 h3 => by
    rw [Matrix.add_apply, hX.2.2 i j h1 h2 h3, hY.2.2 i j h1 h2 h3, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun a i h => by
    rw [Matrix.smul_apply, hX.2.1 a i h, smul_zero], fun i j h1 h2 h3 => by
    rw [Matrix.smul_apply, hX.2.2 i j h1 h2 h3, smul_zero]⟩

def sQ (k r : ℕ) (Γ : Mat (2 * r + k + 1)) : Submodule ℝ (Mat (2 * r + k + 1)) where
  carrier := {X | InQ k r Γ X}
  zero_mem' := ⟨lie_zero _, fun _ _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨lie_add hX.1 hY.1, fun i j h => by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, hX.2 i j h, hY.2 i j h, add_zero]⟩
  smul_mem' := fun c X hX => ⟨lie_smul c hX.1, fun i j h => by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, hX.2 i j h, smul_zero]⟩

/- English proof (translation)
Establish `h : ∀ a, PI.BesselMapUniq.ellA k r z 1 a = 0`. Introduce `a`. Unfold `PI.BesselMapUniq.ellA`. Use `split_ifs with h`. Use `Matrix.one_apply_ne fun e => ?_` and prove the remaining obligations.

Use `congrArg Fin.val e` as an intermediate fact. Simplify using `[eI] at this`. Rewrite using `[one_mulVec]`. Conclude with `hz _ (Or.inl a.2)`. Simplify using `[PI.BesselMapUniq.psiGen, h]`.
-/
theorem psiGen_one {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (c : Fin r → ℂ) :
    PI.BesselMapUniq.psiGen k r z c 1 = 1 := by
  have h : ∀ a, PI.BesselMapUniq.ellA k r z 1 a = 0 := by
    intro a
    unfold PI.BesselMapUniq.ellA
    split_ifs with h
    · refine Matrix.one_apply_ne fun e => ?_
      have := congrArg Fin.val e
      simp [eI] at this
    · rw [one_mulVec]
      exact hz _ (Or.inl a.2)
  simp [PI.BesselMapUniq.psiGen, h]

/- English proof (translation)
Establish `h : ∀ a, Continuous fun g => PI.BesselMapUniq.ellA k r z g a`. Introduce `a`. Unfold `PI.BesselMapUniq.ellA`. Use `split_ifs with h`. Conclude with `continuous_id.matrix_elem _ _`.

Conclude with `(continuous_apply (eI k r a)).comp ((continuous_id (X := Mat (2 * r + k + 1))).matrix_mulVec (continuous_const (y := z)))`. Unfold `PI.BesselMapUniq.psiGen`. Conclude with `Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_finset_sum _ fun a _ => continuous_const.mul (h a)))))`.
-/
theorem psiGen_cont (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) :
    Continuous (PI.BesselMapUniq.psiGen k r z c) := by
  have h : ∀ a, Continuous fun g => PI.BesselMapUniq.ellA k r z g a := by
    intro a
    unfold PI.BesselMapUniq.ellA
    split_ifs with h
    · exact continuous_id.matrix_elem _ _
    · exact (continuous_apply (eI k r a)).comp
        ((continuous_id (X := Mat (2 * r + k + 1))).matrix_mulVec (continuous_const (y := z)))
  unfold PI.BesselMapUniq.psiGen
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_re.comp (continuous_finset_sum _ fun a _ => continuous_const.mul (h a)))))

/- English proof (translation)
Unfold `PI.BesselMapUniq.psiGen`. Conclude with `Complex.norm_exp_I_mul_ofReal _`.
-/
theorem norm_psiGen (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (g : Mat (2 * r + k + 1)) :
    ‖PI.BesselMapUniq.psiGen k r z c g‖ = 1 := by
  unfold PI.BesselMapUniq.psiGen
  exact Complex.norm_exp_I_mul_ofReal _

/- English proof (translation)
Assemble the required witnesses or components as `⟨by simp [UH], fun _ => ⟨one_mulVec _, one_mulVec _⟩, one_mulVec _⟩`.
-/
theorem one_uw (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mat (2 * r + k + 1)) ∈ UWset k r z :=
  ⟨by simp [UH], fun _ => ⟨one_mulVec _, one_mulVec _⟩, one_mulVec _⟩

/- English proof (translation)
Introduce `k r H _ _ _ σ hU hk z c hz hT hc V _ _ _ π hπ1 hπi hπc B hB heq w hw`. Take `⟨Γ, hΓ⟩` from `(hAd k r hk).2 z hz hT`. Take `⟨d₁, X₁, hX₁, sp₁⟩` from `spanFam (sUw k r z)`. Take `⟨d₂, X₂, hX₂, sp₂⟩` from `spanFam (sN k r)`. Take `⟨e, Q, hQ, sp₃⟩` from `spanFam (sQ k r Γ)`.

Establish `hX : ∀ j, InUw k r z (Fin.append X₁ X₂ j) ∨ InN k r (Fin.append X₁ X₂ j)`. Introduce `j`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) j` and prove the remaining obligations. Rewrite using `[Fin.append_left]`. Conclude with `Or.inl (hX₁ i)`.

Rewrite using `[Fin.append_right]`. Conclude with `Or.inr (hX₂ i)`. Establish `hspan : Spans (Hpk k r) (Fin.append X₁ X₂) Q`. Introduce `Y hY`. Take `⟨Y₁, Y₂, Y₃, h1, h2, h3, rfl⟩` from `hSp k r z Γ hk hΓ Y hY`.

Take `⟨a₁, e₁⟩` from `sp₁ Y₁ h1`. Take `⟨a₂, e₂⟩` from `sp₂ Y₂ h2`. Take `⟨b, e₃⟩` from `sp₃ Y₃ h3`. Use `⟨Fin.append a₁ a₂, b, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_add]`.

Simplify using `only [Fin.append_left, Fin.append_right]`. Rewrite using `[← e₁, ← e₂, ← e₃]`. Establish `hχ : ∀ j, ∃ χ : ℝ → (V →L[ℂ] V), Continuous χ ∧ χ 0 = 1 ∧ ∀ t v, IsSm (UH (Hpk k r)) σ v → B (σ (ex (Fin.append X₁ X₂ j) t) v) = χ t (B v)`. Introduce `j`. Break down `hX j with h | h` into its components or cases.

Establish `hm` using `fun t => (hEx k r z _ t).1 h`. Use `⟨fun t => π (ex (Fin.append X₁ X₂ j) t), hπc.comp_continuous (continuous_ex _) hm, ?_, fun t v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [ex_zero, hπ1]`. Use `heq _ (hm t) 1 WeylGroupFacts.mem_n_one v hv` as an intermediate fact. Rewrite `this` using `[Matrix.mul_one, psiGen_one hz, one_smul]`. Then use the resulting hypothesis.

Establish `hm` using `fun t => (hEx k r z _ t).2 h`. Use `⟨fun t => PI.BesselMapUniq.psiGen k r z c (ex (Fin.append X₁ X₂ j) t) • (1 : V →L[ℂ] V), ((psiGen_cont z c).comp (continuous_ex _)).smul continuous_const, ?_, fun t v hv => ?_⟩` and prove the remaining obligations. Simplify using `only [ex_zero, psiGen_one hz, one_smul]`. Use `heq 1 (one_uw z) _ (hm t) v hv` as an intermediate fact. Rewrite `this` using `[Matrix.one_mul, hπ1]`.

Conclude with `this`. Use `choose χ hχc hχ0 hχe using hχ`. Establish `hXL : ∀ j, Lie (Hpk k r) (Fin.append X₁ X₂ j)` using `fun j => (hX j).elim (fun h => h.1) fun h => h.1`. Establish `hQL : ∀ i, Lie (Hpk k r) (Q i)` using `fun i => (hQ i).1`. Take `⟨C, m, hC, hQ'⟩` from `hQB _ _ H σ hU V B hB _ e _ Q hXL hQL hspan χ hχc hχ0 hχe`.

Take `⟨C₁, hC₁⟩` from `hRV k r z Γ c hk hΓ hc`. Use `set C₂ : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ∑ i, ‖Γ⁻¹ * Q i * Γ‖ with hC₂`. Take `⟨K, hK⟩` from `hAB _ _ H σ hU V B hB e Q hQL C m hC hQ' (max C₁ C₂) (2 * r + k + 1) w hw`. Use `⟨K, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨h, hh, m', hm', d, R, hd, hR, hg', rfl⟩` from `hDec k r z Γ hk hz hΓ g hg`.

Use `set g' := Γ * dg d * R with hg'def`. Establish `hsm : IsSm (UH (Hpk k r)) σ (σ g' w)` using `hw.apply hU.rep hg'`. Rewrite using `[hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hm'.1) hg', heq h hh m' hm' _ hsm, norm_smul, norm_psiGen, one_mul, hπi h hh]`. Establish `hconj : ∀ M : ℝ, 1 ≤ M → (∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) → ∀ i, ‖g'⁻¹ * Q i * g'‖ ≤ max C₁ C₂ * M ^ (2 * r + k + 1)`. Introduce `M hM hr i`.

Establish `e1 : g'⁻¹ * Q i * g' = (dg d * R)⁻¹ * (Γ⁻¹ * Q i * Γ) * (dg d * R)`. Rewrite using `[hg'def, Matrix.mul_assoc Γ, Matrix.mul_inv_rev]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e1]`. Use `(hTB k r d R _ M hk hd hR hM hr (hQ i).2).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))` and prove the remaining obligations.

Use `le_trans ?_ (le_max_right _ _)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun i => ‖Γ⁻¹ * Q i * Γ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)) (by positivity)`. Distinguish the cases in `hall : ∀ a : Fin r, d (eI k r a) / d (nxt k r a) ≤ 1`. Use `hK g' hg' 1 le_rfl (hconj 1 le_rfl fun a => ?_) (Or.inl rfl)` and prove the remaining obligations. Conclude with `(div_le_iff₀ (hd.1 _)).1 (hall a)`.

Use `push Not at hall`. Take `⟨a₁, ha₁⟩` from `hall`. Take `⟨a₀, -, ha₀⟩` from `Finset.exists_max_image Finset.univ (fun a : Fin r => d (eI k r a) / d (nxt k r a)) ⟨a₁, Finset.mem_univ _⟩`. Establish `hM : 1 ≤ d (eI k r a₀) / d (nxt k r a₀)` using `ha₁.le.trans (ha₀ a₁ (Finset.mem_univ _))`. Take `⟨Y, hY, hYn, hYe⟩` from `hC₁ a₀ d R hd hR hg'`.

Use `hK g' hg' _ hM (hconj _ hM fun a => (div_le_iff₀ (hd.1 _)).1 (ha₀ a (Finset.mem_univ _))) (Or.inr ⟨Y, d (eI k r a₀) / d (nxt k r a₀), hY, hYn.trans (le_max_left _ _), le_abs_self _, fun τ u hu => ?_⟩)` and prove the remaining obligations. Take `⟨hN, hψ⟩` from `hYe τ`. Establish `hinv : g'⁻¹ * g' = 1` using `mul_eq_one_comm.1 (hU.grp.2.2.2 g' hg').2`. Establish `e2 : g' * ex Y τ = 1 * (g' * ex Y τ * g'⁻¹) * g'`. Rewrite using `[Matrix.one_mul, Matrix.mul_assoc (g' * ex Y τ), hinv, Matrix.mul_one]`.

Rewrite using `[e2, hU.rep.apply_mul (hU.rep.mul_mem _ hU.rep.one_mem _ hN.1) hg', heq 1 (one_uw z) _ hN _ (hu.apply hU.rep hg'), hπ1, hψ]`. Both sides reduce to the same expression.
-/
theorem bounded_of (hQB : QBound) (hAB : AbsBound) (hAd : AdaptExists) (hDec : Decomp) (hTB : TorBound)
    (hSp : SpanG) (hEx : ExpMem) (hRV : RootVec) : Bounded := by
  intro k r H _ _ _ σ hU hk z c hz hT hc V _ _ _ π hπ1 hπi hπc B hB heq w hw
  obtain ⟨Γ, hΓ⟩ := (hAd k r hk).2 z hz hT
  obtain ⟨d₁, X₁, hX₁, sp₁⟩ := spanFam (sUw k r z)
  obtain ⟨d₂, X₂, hX₂, sp₂⟩ := spanFam (sN k r)
  obtain ⟨e, Q, hQ, sp₃⟩ := spanFam (sQ k r Γ)
  have hX : ∀ j, InUw k r z (Fin.append X₁ X₂ j) ∨ InN k r (Fin.append X₁ X₂ j) := by
    intro j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]; exact Or.inl (hX₁ i)
    · rw [Fin.append_right]; exact Or.inr (hX₂ i)
  have hspan : Spans (Hpk k r) (Fin.append X₁ X₂) Q := by
    intro Y hY
    obtain ⟨Y₁, Y₂, Y₃, h1, h2, h3, rfl⟩ := hSp k r z Γ hk hΓ Y hY
    obtain ⟨a₁, e₁⟩ := sp₁ Y₁ h1
    obtain ⟨a₂, e₂⟩ := sp₂ Y₂ h2
    obtain ⟨b, e₃⟩ := sp₃ Y₃ h3
    refine ⟨Fin.append a₁ a₂, b, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← e₁, ← e₂, ← e₃]
  have hχ : ∀ j, ∃ χ : ℝ → (V →L[ℂ] V), Continuous χ ∧ χ 0 = 1 ∧
      ∀ t v, IsSm (UH (Hpk k r)) σ v → B (σ (ex (Fin.append X₁ X₂ j) t) v) = χ t (B v) := by
    intro j
    rcases hX j with h | h
    · have hm := fun t => (hEx k r z _ t).1 h
      refine ⟨fun t => π (ex (Fin.append X₁ X₂ j) t), hπc.comp_continuous (continuous_ex _) hm, ?_, fun t v hv => ?_⟩
      · simp only [ex_zero, hπ1]
      · have := heq _ (hm t) 1 WeylGroupFacts.mem_n_one v hv
        rwa [Matrix.mul_one, psiGen_one hz, one_smul] at this
    · have hm := fun t => (hEx k r z _ t).2 h
      refine ⟨fun t => PI.BesselMapUniq.psiGen k r z c (ex (Fin.append X₁ X₂ j) t) • (1 : V →L[ℂ] V),
        ((psiGen_cont z c).comp (continuous_ex _)).smul continuous_const, ?_, fun t v hv => ?_⟩
      · simp only [ex_zero, psiGen_one hz, one_smul]
      · have := heq 1 (one_uw z) _ (hm t) v hv
        rw [Matrix.one_mul, hπ1] at this
        exact this
  choose χ hχc hχ0 hχe using hχ
  have hXL : ∀ j, Lie (Hpk k r) (Fin.append X₁ X₂ j) := fun j => (hX j).elim (fun h => h.1) fun h => h.1
  have hQL : ∀ i, Lie (Hpk k r) (Q i) := fun i => (hQ i).1
  obtain ⟨C, m, hC, hQ'⟩ := hQB _ _ H σ hU V B hB _ e _ Q hXL hQL hspan χ hχc hχ0 hχe
  obtain ⟨C₁, hC₁⟩ := hRV k r z Γ c hk hΓ hc
  set C₂ : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * ∑ i, ‖Γ⁻¹ * Q i * Γ‖ with hC₂
  obtain ⟨K, hK⟩ := hAB _ _ H σ hU V B hB e Q hQL C m hC hQ' (max C₁ C₂) (2 * r + k + 1) w hw
  refine ⟨K, fun g hg => ?_⟩
  obtain ⟨h, hh, m', hm', d, R, hd, hR, hg', rfl⟩ := hDec k r z Γ hk hz hΓ g hg
  set g' := Γ * dg d * R with hg'def
  have hsm : IsSm (UH (Hpk k r)) σ (σ g' w) := hw.apply hU.rep hg'
  rw [hU.rep.apply_mul (hU.rep.mul_mem _ hh.1 _ hm'.1) hg', heq h hh m' hm' _ hsm, norm_smul, norm_psiGen, one_mul,
    hπi h hh]
  have hconj : ∀ M : ℝ, 1 ≤ M → (∀ a : Fin r, d (eI k r a) ≤ M * d (nxt k r a)) →
      ∀ i, ‖g'⁻¹ * Q i * g'‖ ≤ max C₁ C₂ * M ^ (2 * r + k + 1) := by
    intro M hM hr i
    have e1 : g'⁻¹ * Q i * g' = (dg d * R)⁻¹ * (Γ⁻¹ * Q i * Γ) * (dg d * R) := by
      rw [hg'def, Matrix.mul_assoc Γ, Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    rw [e1]
    refine (hTB k r d R _ M hk hd hR hM hr (hQ i).2).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    refine le_trans ?_ (le_max_right _ _)
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => ‖Γ⁻¹ * Q i * Γ‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))
      (by positivity)
  by_cases hall : ∀ a : Fin r, d (eI k r a) / d (nxt k r a) ≤ 1
  · refine hK g' hg' 1 le_rfl (hconj 1 le_rfl fun a => ?_) (Or.inl rfl)
    exact (div_le_iff₀ (hd.1 _)).1 (hall a)
  · push Not at hall
    obtain ⟨a₁, ha₁⟩ := hall
    obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image Finset.univ (fun a : Fin r => d (eI k r a) / d (nxt k r a))
      ⟨a₁, Finset.mem_univ _⟩
    have hM : 1 ≤ d (eI k r a₀) / d (nxt k r a₀) := ha₁.le.trans (ha₀ a₁ (Finset.mem_univ _))
    obtain ⟨Y, hY, hYn, hYe⟩ := hC₁ a₀ d R hd hR hg'
    refine hK g' hg' _ hM (hconj _ hM fun a => (div_le_iff₀ (hd.1 _)).1 (ha₀ a (Finset.mem_univ _)))
      (Or.inr ⟨Y, d (eI k r a₀) / d (nxt k r a₀), hY, hYn.trans (le_max_left _ _), le_abs_self _, fun τ u hu => ?_⟩)
    obtain ⟨hN, hψ⟩ := hYe τ
    have hinv : g'⁻¹ * g' = 1 := mul_eq_one_comm.1 (hU.grp.2.2.2 g' hg').2
    have e2 : g' * ex Y τ = 1 * (g' * ex Y τ * g'⁻¹) * g' := by
      rw [Matrix.one_mul, Matrix.mul_assoc (g' * ex Y τ), hinv, Matrix.mul_one]
    rw [e2, hU.rep.apply_mul (hU.rep.mul_mem _ hU.rep.one_mem _ hN.1) hg',
      heq 1 (one_uw z) _ hN _ (hu.apply hU.rep hg'), hπ1, hψ]
    rfl

end CompanionTheory.Bmu
