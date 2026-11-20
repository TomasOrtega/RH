import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolRepOfIsTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowestWeightMatrixCoefficientDependsOnWeightStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JointHarm.KTypeOp

/- English proof (translation)
Use `⟨Unitary.star_mem hk.1, ?_⟩` and prove the remaining obligations. Establish `hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε`. Simplify using `only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `by_cases h : ε a = true <;> simp [h]`. Use `congrArg Matrix.conjTranspose hk.2` as an intermediate fact. Rewrite `this` using `[Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ]`. Conclude with `this.symm`.
-/
theorem star_mem_K {n : ℕ} {ε : Fin n → Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Formalism.REAL.Kset ε) :
    kᴴ ∈ Formalism.REAL.Kset ε := by
  refine ⟨Unitary.star_mem hk.1, ?_⟩
  have hJ : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
    simp only [Formalism.REAL.Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    by_cases h : ε a = true <;> simp [h]
  have := congrArg Matrix.conjTranspose hk.2
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hJ] at this
  exact this.symm

/- English proof (translation)
Use `⟨mul_mem ha.1 hb.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]`.
-/
theorem mul_mem_K {n : ℕ} {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.REAL.Kset ε)
    (hb : b ∈ Formalism.REAL.Kset ε) : a * b ∈ Formalism.REAL.Kset ε := by
  refine ⟨mul_mem ha.1 hb.1, ?_⟩
  rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨hτ, hbw⟩` from `isHolRep_of_isTau h`. Take `⟨-, ⟨h1, hm⟩, -, ha, hirr, hw, -, -⟩` from `h`. Establish `KC` using `@GlobalTheory.Dec.TauExt.mem_KC n ε`. Set `Φ : (Formalism.REAL.Kset ε →₀ ℂ) →ₗ[ℂ] W` to `Finsupp.linearCombination ℂ fun k => τ k.1 w`. Set `Ψ : (Formalism.REAL.Kset ε →₀ ℂ) →ₗ[ℂ] Module.End ℂ P` to `Finsupp.linearCombination ℂ fun k => π k.1`.

Establish `hΦ : ∀ k a, Φ (Finsupp.single k a) = a • τ k.1 w` using `fun k a => Finsupp.linearCombination_single _ _ _`. Establish `hΨ : ∀ k a, Ψ (Finsupp.single k a) = a • π k.1` using `fun k a => Finsupp.linearCombination_single _ _ _`. Establish `hmul : ∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, τ a (τ b w) = τ (a * b) w` using `fun a ha' b hb => by`. Rewrite using `[hm a (KC ha') b (KC hb)]`. Both sides reduce to the same expression.

Establish `hw1 : Φ (Finsupp.single ⟨1, GlobalTheory.Dec.TauExt.one_mem_K⟩ 1) = w`. Rewrite using `[hΦ, one_smul, h1]`. Both sides reduce to the same expression. Establish `hsurj : LinearMap.range Φ = ⊤`. Use `(hirr _ ?_).resolve_left fun h0 => ?_` and prove the remaining obligations.

Introduce and unpack `g hg _ ⟨c, rfl⟩`. Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => rw [map_add, map_add]`. Conclude with `add_mem ha hb`.

Consider the case `single k a => exact ⟨Finsupp.single ⟨g * k.1, mul_mem_K hg k.2⟩ a, by rw [hΦ, hΦ, map_smul, hmul g hg _ k.2]⟩`. Establish `: w ∈ LinearMap.range Φ` using `⟨_, hw1⟩`. Rewrite `this` using `[h0, Submodule.mem_bot]`. Simplify using `[this] at hw`. Take `⟨R, hR⟩` from `Φ.exists_rightInverse_of_surjective hsurj`.

Establish `hR' : ∀ s, Φ (R s) = s` using `fun s => LinearMap.congr_fun hR s`. Use `⟨Ψ ∘ₗ R, fun s => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[Set.image_eq_range, ← Finsupp.range_linearCombination]`. Conclude with `⟨R s, rfl⟩`. Establish `gram0 : ∀ k k' : Formalism.REAL.Kset ε, B (π k.1 y) (π k'.1 y) = B y y * ⟪τ k.1 w, τ k'.1 w⟫_ℂ`.

Introduce `k k'`. Establish `hk` using `star_mem_K k.2`. Establish `e` using `GlobalTheory.T.lowestWeight_matrixCoefficient_depends_on_weight n ε (-abelian₂) P B π W (innerₛₗ ℂ) (fun g => (τ g : W →ₗ[ℂ] W)) y y w w hπ hτ hy hy hbw hbw _ (mul_mem_K hk k'.2)`. Establish `hww : innerₛₗ ℂ w w = 1`. Rewrite using `[innerₛₗ_apply_apply, inner_self_eq_norm_sq_to_K, hw]`.

Simplify using the standard rewrite rules. Rewrite `e` using `[hww, mul_one]`. Rewrite using `[hπ.2.2.2.1 _ (KC k.2), ha _ (KC k.2), hmul _ hk _ k'.2, ← Module.End.mul_apply, ← hπ.2.2.1 _ (KC hk) _ (KC k'.2), e]`. Both sides reduce to the same expression. Establish `gram : ∀ c c', B (Ψ c y) (Ψ c' y) = B y y * ⟪Φ c, Φ c'⟫_ℂ`.

Introduce `c c'`. Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, inner_add_left, mul_add]`. Consider the case `single k a`.

Proceed by induction on `c' using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, inner_add_right, mul_add]`. Consider the case `single k' a'`. Simplify using `only [hΦ, hΨ, LinearMap.smul_apply, map_smul, LinearMap.map_smulₛₗ, inner_smul_left, inner_smul_right, gram0, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ c, Ψ (R (Φ c)) y = Ψ c y`. Introduce `c`. Use `gram (R (Φ c) - c) (R (Φ c) - c)` as an intermediate fact. Rewrite `this` using `[map_sub Φ, hR', sub_self, inner_zero_left, mul_zero]`.

Use `hπ.1 _ this` as an intermediate fact. Rewrite `this` using `[map_sub, LinearMap.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis. Use `⟨?_, fun g hg s => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, ← hw1, key, hΨ, one_smul, hπ.2.1]`. Both sides reduce to the same expression.

Take `⟨c, rfl⟩ : s ∈ LinearMap.range Φ` from `hsurj ▸ Submodule.mem_top`. Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]`. Consider the case `single k a`.

Establish `e : τ g (Φ (Finsupp.single k a)) = Φ (Finsupp.single ⟨g * k.1, mul_mem_K hg k.2⟩ a)`. Rewrite using `[hΦ, hΦ, map_smul, hmul g hg _ k.2]`. Rewrite using `[e, LinearMap.comp_apply, LinearMap.comp_apply, key, key, hΨ, hΨ, hπ.2.2.1 _ (KC hg) _ (KC k.2)]`. Simplify using the standard rewrite rules.
-/
theorem exists_op_of_isTau {n : ℕ} {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W} (h : GlobalTheory.Dec.IsTau ε abelian₂ τ w)
    {P : Type} [AddCommGroup P] [Module ℂ P] {B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ}
    {π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P} (hπ : IsHolRep ε B π) :
    ∃ T : W →ₗ[ℂ] Module.End ℂ P, (∀ s, T s ∈ Submodule.span ℂ (π '' Formalism.REAL.Kset ε)) ∧
      ∀ y, IsBottom ε π (-abelian₂) y → T w y = y ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ s, T (τ k s) y = π k (T s y) := by
  obtain ⟨hτ, hbw⟩ := isHolRep_of_isTau h
  obtain ⟨-, ⟨h1, hm⟩, -, ha, hirr, hw, -, -⟩ := h
  have KC := @GlobalTheory.Dec.TauExt.mem_KC n ε
  let Φ : (Formalism.REAL.Kset ε →₀ ℂ) →ₗ[ℂ] W := Finsupp.linearCombination ℂ fun k => τ k.1 w
  let Ψ : (Formalism.REAL.Kset ε →₀ ℂ) →ₗ[ℂ] Module.End ℂ P := Finsupp.linearCombination ℂ fun k => π k.1
  have hΦ : ∀ k a, Φ (Finsupp.single k a) = a • τ k.1 w := fun k a => Finsupp.linearCombination_single _ _ _
  have hΨ : ∀ k a, Ψ (Finsupp.single k a) = a • π k.1 := fun k a => Finsupp.linearCombination_single _ _ _
  have hmul : ∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, τ a (τ b w) = τ (a * b) w := fun a ha' b hb => by
    rw [hm a (KC ha') b (KC hb)]; rfl
  have hw1 : Φ (Finsupp.single ⟨1, GlobalTheory.Dec.TauExt.one_mem_K⟩ 1) = w := by
    rw [hΦ, one_smul, h1]; rfl
  have hsurj : LinearMap.range Φ = ⊤ := by
    refine (hirr _ ?_).resolve_left fun h0 => ?_
    · rintro g hg _ ⟨c, rfl⟩
      induction c using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => rw [map_add, map_add]; exact add_mem ha hb
      | single k a => exact ⟨Finsupp.single ⟨g * k.1, mul_mem_K hg k.2⟩ a, by rw [hΦ, hΦ, map_smul, hmul g hg _ k.2]⟩
    · have : w ∈ LinearMap.range Φ := ⟨_, hw1⟩
      rw [h0, Submodule.mem_bot] at this
      simp [this] at hw
  obtain ⟨R, hR⟩ := Φ.exists_rightInverse_of_surjective hsurj
  have hR' : ∀ s, Φ (R s) = s := fun s => LinearMap.congr_fun hR s
  refine ⟨Ψ ∘ₗ R, fun s => ?_, fun y hy => ?_⟩
  · rw [Set.image_eq_range, ← Finsupp.range_linearCombination]
    exact ⟨R s, rfl⟩
  have gram0 : ∀ k k' : Formalism.REAL.Kset ε, B (π k.1 y) (π k'.1 y) = B y y * ⟪τ k.1 w, τ k'.1 w⟫_ℂ := by
    intro k k'
    have hk := star_mem_K k.2
    have e := GlobalTheory.T.lowestWeight_matrixCoefficient_depends_on_weight n ε (-abelian₂) P B π W (innerₛₗ ℂ) (fun g => (τ g : W →ₗ[ℂ] W)) y y w w hπ hτ hy hy
      hbw hbw _ (mul_mem_K hk k'.2)
    have hww : innerₛₗ ℂ w w = 1 := by
      rw [innerₛₗ_apply_apply, inner_self_eq_norm_sq_to_K, hw]; simp
    rw [hww, mul_one] at e
    rw [hπ.2.2.2.1 _ (KC k.2), ha _ (KC k.2), hmul _ hk _ k'.2, ← Module.End.mul_apply,
      ← hπ.2.2.1 _ (KC hk) _ (KC k'.2), e]
    rfl
  have gram : ∀ c c', B (Ψ c y) (Ψ c' y) = B y y * ⟪Φ c, Φ c'⟫_ℂ := by
    intro c c'
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, inner_add_left, mul_add]
    | single k a =>
      induction c' using Finsupp.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb, inner_add_right, mul_add]
      | single k' a' =>
        simp only [hΦ, hΨ, LinearMap.smul_apply, map_smul, LinearMap.map_smulₛₗ, inner_smul_left, inner_smul_right,
          gram0, smul_eq_mul]
        ring
  have key : ∀ c, Ψ (R (Φ c)) y = Ψ c y := by
    intro c
    have := gram (R (Φ c) - c) (R (Φ c) - c)
    rw [map_sub Φ, hR', sub_self, inner_zero_left, mul_zero] at this
    have := hπ.1 _ this
    rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
  refine ⟨?_, fun g hg s => ?_⟩
  · rw [LinearMap.comp_apply, ← hw1, key, hΨ, one_smul, hπ.2.1]; rfl
  · obtain ⟨c, rfl⟩ : s ∈ LinearMap.range Φ := hsurj ▸ Submodule.mem_top
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
    | single k a =>
      have e : τ g (Φ (Finsupp.single k a)) = Φ (Finsupp.single ⟨g * k.1, mul_mem_K hg k.2⟩ a) := by
        rw [hΦ, hΦ, map_smul, hmul g hg _ k.2]
      rw [e, LinearMap.comp_apply, LinearMap.comp_apply, key, key, hΨ, hΨ, hπ.2.2.1 _ (KC hg) _ (KC k.2)]
      simp

/- English proof (translation)
Introduce `n ε abelian₂ H _ _ σ S hσ hS P _ _ B π hπ`. Take `⟨v, hvS, hv0, hv⟩` from `hS.2.2.2.1`. Set `w : S` to `⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, S.smul_mem _ hvS⟩`. Establish `hw : ‖w‖ = 1`. Establish `: ‖v‖ ≠ 0` using `norm_ne_zero_iff.2 hv0`.

Use `show ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1`. Rewrite using `[norm_smul]`. Simplify using `[this]`. Establish `hwt : IsWtOn (Formalism.REAL.Kset ε) σ abelian₂ (w : H)` using `fun θ hθ => by show σ _ (_ • v) = _ • _ • v`. Rewrite using `[map_smul, hv θ hθ, smul_comm]`.

Take `⟨τ, hτ, hτσ⟩` from `GlobalTheory.Dec.TauExt.tauExists n ε abelian₂ H σ S w hσ hS hw hwt`. Take `⟨T, hT1, hT2⟩` from `exists_op_of_isTau hτ hπ`. Use `⟨w, T, fun h0 => by simp [h0] at hw, hT1, fun y hy => ⟨(hT2 y hy).1, fun k hk s s' hs => ?_⟩⟩` and prove the remaining obligations. Establish `hk'` using `GlobalTheory.Dec.TauExt.conj_mem hk`. Rewrite using `[← (hT2 y hy).2 _ hk' s]`.

Use `congr 2`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hτσ _ hk', GlobalTheory.Dec.TauExt.conj_conj, hs]`.
-/
theorem exists_op : ∀ (n : ℕ) (ε : Fin n → Bool) (abelian₂ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), IsURepOn (Formalism.REAL.Kset ε) σ → IsKTypeOf ε σ abelian₂ S → ∀ (P : Type) [AddCommGroup P] [Module ℂ P] (B : P →ₗ⋆[ℂ] P →ₗ[ℂ] ℂ) (π : Matrix (Fin n) (Fin n) ℂ → Module.End ℂ P), IsHolRep ε B π → ∃ (w : S) (T : S →ₗ[ℂ] Module.End ℂ P), w ≠ 0 ∧ (∀ s, T s ∈ Submodule.span ℂ (π '' Formalism.REAL.Kset ε)) ∧ ∀ y, IsBottom ε π (-abelian₂) y → T w y = y ∧ ∀ k ∈ Formalism.REAL.Kset ε, ∀ s s' : S, (s' : H) = σ k s → T s' y = π (k.map star) (T s y) := by
  intro n ε abelian₂ H _ _ σ S hσ hS P _ _ B π hπ
  obtain ⟨v, hvS, hv0, hv⟩ := hS.2.2.2.1
  let w : S := ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, S.smul_mem _ hvS⟩
  have hw : ‖w‖ = 1 := by
    have : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
    show ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1
    rw [norm_smul]; simp [this]
  have hwt : IsWtOn (Formalism.REAL.Kset ε) σ abelian₂ (w : H) := fun θ hθ => by
    show σ _ (_ • v) = _ • _ • v
    rw [map_smul, hv θ hθ, smul_comm]
  obtain ⟨τ, hτ, hτσ⟩ := GlobalTheory.Dec.TauExt.tauExists n ε abelian₂ H σ S w hσ hS hw hwt
  obtain ⟨T, hT1, hT2⟩ := exists_op_of_isTau hτ hπ
  refine ⟨w, T, fun h0 => by simp [h0] at hw, hT1, fun y hy => ⟨(hT2 y hy).1, fun k hk s s' hs => ?_⟩⟩
  have hk' := GlobalTheory.Dec.TauExt.conj_mem hk
  rw [← (hT2 y hy).2 _ hk' s]
  congr 2
  apply Subtype.ext
  rw [hτσ _ hk', GlobalTheory.Dec.TauExt.conj_conj, hs]

end GlobalTheory.JointHarm.KTypeOp
