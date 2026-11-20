import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightCompactDominanceOfMemHighestWeightSpan
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsHighestWeightIrreducibleUnitaryRepU
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsLinearEquivOfIrreducibleIsHW

open Matrix Finset

noncomputable section

namespace GlobalTheory.UnitaryHighestWeightUnique

open PI.UpqRep GlobalTheory.UnitaryHighestWeight

open Matrix Finset in
/- English proof (translation)
Unfold `_root_.PI.UpqRep.CDom at h`. Take `⟨c, hc, h⟩` from `h`. Establish `key : ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x - ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x = ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ))`. Rewrite using `[← Finset.sum_sub_distrib]`. Establish `hx : ∀ x, Λ x - μ x = (Λ - μ) x` using `fun x => rfl`.

Repeatedly rewrite using `[← mul_sub, hx, h]`. Unfold `_root_.PI.UpqRep.root`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `[mul_sub, Finset.sum_sub_distrib, mul_comm, mul_left_comm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hterm : ∀ a b : Fin n, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0`.

Introduce `a b`. Distinguish the cases in `h0 : c a b = 0`. Simplify using `[h0]`. Establish `hab` using `(hc a b h0).1`. Establish `: ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`.

Conclude with `mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)`. Establish `hrow : ∀ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0` using `fun a => Finset.sum_nonpos fun b _ => hterm a b`. Establish `hsum : ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0` using `Finset.sum_nonpos fun a _ => hrow a`. Use `⟨by linarith, fun heq => ?_⟩` and prove the remaining obligations. Establish `hzero : ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) = 0`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc0 : ∀ a b, c a b = 0`. Introduce `a b`. Assume the negation of the conclusion as `h0`. Establish `hab` using `(hc a b h0).1`.

Establish `hlt : ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) < 0`. Establish `: ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Conclude with `mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero h0) (by linarith)`. Establish `ha` using `(Finset.sum_eq_zero_iff_of_nonpos fun a _ => hrow a).1 hzero a (Finset.mem_univ a)`. Establish `hb` using `(Finset.sum_eq_zero_iff_of_nonpos fun b _ => hterm a b).1 ha b (Finset.mem_univ b)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: Λ - μ = 0` using `by simp [h, hc0]`. Conclude with `sub_eq_zero.mp this`.
-/
theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.height_le {n : ℕ} {ε : Fin n → Bool} {μ Λ : Fin n → ℝ}
    (h : _root_.PI.UpqRep.CDom ε μ Λ) :
    ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x ≤ ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x ∧
      (∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x = ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x → Λ = μ) := by
  unfold _root_.PI.UpqRep.CDom at h
  obtain ⟨c, hc, h⟩ := h
  have key : ∑ x : Fin n, ((x : ℕ) : ℝ) * Λ x - ∑ x : Fin n, ((x : ℕ) : ℝ) * μ x =
      ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    have hx : ∀ x, Λ x - μ x = (Λ - μ) x := fun x => rfl
    simp_rw [← mul_sub, hx, h]
    unfold _root_.PI.UpqRep.root
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp [mul_sub, Finset.sum_sub_distrib, mul_comm, mul_left_comm]
    ring
  have hterm : ∀ a b : Fin n, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have hab := (hc a b h0).1
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  have hrow : ∀ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    fun a => Finset.sum_nonpos fun b _ => hterm a b
  have hsum : ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) ≤ 0 :=
    Finset.sum_nonpos fun a _ => hrow a
  refine ⟨by linarith, fun heq => ?_⟩
  have hzero : ∑ a, ∑ b, ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) = 0 := by
    linarith
  have hc0 : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have hab := (hc a b h0).1
    have hlt : ((c a b : ℕ) : ℝ) * (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) < 0 := by
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      exact mul_neg_of_pos_of_neg (by exact_mod_cast Nat.pos_of_ne_zero h0) (by linarith)
    have ha := (Finset.sum_eq_zero_iff_of_nonpos fun a _ => hrow a).1 hzero a (Finset.mem_univ a)
    have hb := (Finset.sum_eq_zero_iff_of_nonpos fun b _ => hterm a b).1 ha b (Finset.mem_univ b)
    linarith
  have : Λ - μ = 0 := by simp [h, hc0]
  exact sub_eq_zero.mp this

open Matrix Finset in

/- English proof (translation)
Take `⟨E, hrel, -, hder⟩` from `_root_.GlobalTheory.UnitaryDerived.exists_derived_action k W π hπ`. Unfold `_root_.PI.UpqRep.IsKTypeOf at hK`. Take `⟨-, -, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩` from `hK`. Use `⟨E, hrel, hder, ?_, v, hv0, ?_⟩` and prove the remaining obligations. Introduce `S hS`.

Establish `hSπ : _root_.PI.UpqRep.IsKStableOn (_root_.PI.UpqRep.allPos k) π S`. Unfold `_root_.PI.UpqRep.IsKStableOn`. Introduce `g hg w hw`. Conclude with `_root_.GlobalTheory.UnitaryHighestWeight.stable_of_derived hπ E hder S (by unfold _root_.Formalism.REAL.KStable; exact fun a b _ x hx => hS a b x hx) g ((_root_.GlobalTheory.UnitaryHighestWeight.mem_K_iff g).1 hg) w hw`. Conclude with `hirr S le_top hSπ`.

Establish `hvE : _root_.Formalism.REAL.IsWeight E Λ v` using `_root_.GlobalTheory.UnitaryHighestWeight.isWeight_of_isWtOn E hder Λ v hvw`. Unfold `_root_.Formalism.REAL.IsWeight at hvE`. Unfold `_root_.Formalism.REAL.IsHW`. Use `⟨fun a => hvE a, fun a b hab => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Unfold `_root_.Formalism.REAL.GlRel at hrel`. Establish `hw : _root_.Formalism.REAL.IsWeight E (Λ + _root_.PI.UpqRep.root a b) (E a b v)`. Unfold `_root_.Formalism.REAL.IsWeight`. Introduce `c`. Establish `hc` using `congrArg (fun T : Module.End ℂ W => T v) (hrel c c a b)`.

Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at hc`. Establish `hsplit : E c c (E a b v) = E a b (E c c v) + ((if c = a then E c b else 0) - if b = c then E a c else 0) v`. Rewrite using `[LinearMap.sub_apply, ← hc]`. Normalize the expressions using the abelian group laws. Rewrite using `[hsplit, hvE c, map_smul]`.

Unfold `_root_.PI.UpqRep.root`. Distinguish the cases in `hca : c = a`. Substitute `hca` using the available equality. Establish `hcb : b ≠ c` using `ne_of_gt hab`. Simplify using `[hcb, Ne.symm hcb, add_smul, add_comm]`.

Distinguish the cases in `hcb : b = c`. Substitute `hcb` using the available equality. Simplify using `[hca, Ne.symm hca, add_smul, sub_eq_add_neg, add_comm]`. Simplify using `[hca, hcb, Ne.symm hcb]`. Establish `ht` using `_root_.GlobalTheory.UnitaryHighestWeight.isWtOn_of_isWeight hπ E hder _ _ hw`.

Establish `hD` using `hdom _ (E a b v) Submodule.mem_top hne ht`. Establish `hle` using `(_root_.GlobalTheory.UnitaryHighestWeightUnique.height_le hD).1`. Establish `hcomp : ∑ x : Fin k, ((x : ℕ) : ℝ) * (Λ + _root_.PI.UpqRep.root a b) x = ∑ x : Fin k, ((x : ℕ) : ℝ) * Λ x + (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ))`. Unfold `_root_.PI.UpqRep.root`. Simplify using `[mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]`.

Establish `: ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest {k : ℕ} {W : Type} [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [Nontrivial W]
    {π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)} {Λ : Fin k → ℝ}
    (hπ : _root_.PI.UpqRep.IsURepOn (_root_.PI.UpqRep.UJset (_root_.PI.UpqRep.allPos k)) π) (hK : _root_.PI.UpqRep.IsKTypeOf (_root_.PI.UpqRep.allPos k) π Λ ⊤) :
    ∃ E : Fin k → Fin k → Module.End ℂ W, _root_.Formalism.REAL.GlRel E ∧
      (∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v,
        HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0) ∧
      (∀ S : Submodule ℂ W, (∀ a b, ∀ x ∈ S, E a b x ∈ S) → S = ⊥ ∨ S = ⊤) ∧
      ∃ x, x ≠ 0 ∧ _root_.Formalism.REAL.IsHW E (fun a => (Λ a : ℂ)) x := by
  obtain ⟨E, hrel, -, hder⟩ := _root_.GlobalTheory.UnitaryDerived.exists_derived_action k W π hπ
  unfold _root_.PI.UpqRep.IsKTypeOf at hK
  obtain ⟨-, -, hirr, ⟨v, -, hv0, hvw⟩, hdom⟩ := hK
  refine ⟨E, hrel, hder, ?_, v, hv0, ?_⟩
  · intro S hS
    have hSπ : _root_.PI.UpqRep.IsKStableOn (_root_.PI.UpqRep.allPos k) π S := by
      unfold _root_.PI.UpqRep.IsKStableOn
      intro g hg w hw
      exact _root_.GlobalTheory.UnitaryHighestWeight.stable_of_derived hπ E hder S
        (by unfold _root_.Formalism.REAL.KStable; exact fun a b _ x hx => hS a b x hx) g
        ((_root_.GlobalTheory.UnitaryHighestWeight.mem_K_iff g).1 hg) w hw
    exact hirr S le_top hSπ
  · have hvE : _root_.Formalism.REAL.IsWeight E Λ v := _root_.GlobalTheory.UnitaryHighestWeight.isWeight_of_isWtOn E hder Λ v hvw
    unfold _root_.Formalism.REAL.IsWeight at hvE
    unfold _root_.Formalism.REAL.IsHW
    refine ⟨fun a => hvE a, fun a b hab => ?_⟩
    by_contra hne
    unfold _root_.Formalism.REAL.GlRel at hrel
    have hw : _root_.Formalism.REAL.IsWeight E (Λ + _root_.PI.UpqRep.root a b) (E a b v) := by
      unfold _root_.Formalism.REAL.IsWeight
      intro c
      have hc := congrArg (fun T : Module.End ℂ W => T v) (hrel c c a b)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at hc
      have hsplit : E c c (E a b v) = E a b (E c c v) +
          ((if c = a then E c b else 0) - if b = c then E a c else 0) v := by
        rw [LinearMap.sub_apply, ← hc]; abel
      rw [hsplit, hvE c, map_smul]
      unfold _root_.PI.UpqRep.root
      by_cases hca : c = a
      · subst hca
        have hcb : b ≠ c := ne_of_gt hab
        simp [hcb, Ne.symm hcb, add_smul, add_comm]
      · by_cases hcb : b = c
        · subst hcb
          simp [hca, Ne.symm hca, add_smul, sub_eq_add_neg, add_comm]
        · simp [hca, hcb, Ne.symm hcb]
    have ht := _root_.GlobalTheory.UnitaryHighestWeight.isWtOn_of_isWeight hπ E hder _ _ hw
    have hD := hdom _ (E a b v) Submodule.mem_top hne ht
    have hle := (_root_.GlobalTheory.UnitaryHighestWeightUnique.height_le hD).1
    have hcomp : ∑ x : Fin k, ((x : ℕ) : ℝ) * (Λ + _root_.PI.UpqRep.root a b) x =
        ∑ x : Fin k, ((x : ℕ) : ℝ) * Λ x + (((a : ℕ) : ℝ) - ((b : ℕ) : ℝ)) := by
      unfold _root_.PI.UpqRep.root
      simp [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply]
    have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
    linarith

open Matrix Finset in

/- English proof (translation)
Set `Tc : W₁ →L[ℝ] W₂` to `(LinearMap.toContinuousLinearMap T).restrictScalars ℝ`. Set `Ac : W₂ →L[ℝ] W₂` to `(LinearMap.toContinuousLinearMap A₂).restrictScalars ℝ`. Establish `hTc : ∀ x, Tc x = T x` using `fun x => rfl`. Establish `hAc : ∀ x, Ac x = A₂ x` using `fun x => rfl`. Establish `hf : ∀ s, HasDerivAt (fun s => T (U₁ s v)) (Ac (T (U₁ s v))) s`.

Introduce `s`. Establish `h` using `_root_.GlobalTheory.UnitaryHighestWeight.deriv_left U₁ A₁ hadd₁ hd₁ v s`. Establish `h'` using `Tc.hasFDerivAt.comp_hasDerivAt s h`. Simplify using `only [Function.comp_def, hTc] at h'`. Rewrite using `[hAc, ← hT]` and apply the resulting hypothesis.

Establish `hg : ∀ s, HasDerivAt (fun s => U₂ s (T v)) (Ac (U₂ s (T v))) s`. Introduce `s`. Rewrite using `[hAc]`. Conclude with `_root_.GlobalTheory.UnitaryHighestWeight.deriv_left U₂ A₂ hadd₂ hd₂ (T v) s`. Establish `heq` using `ODE_solution_unique_univ (v := fun _ => Ac) (s := fun _ => Set.univ) (K := ‖Ac‖₊) (t₀ := 0) (fun _ => Ac.lipschitz.lipschitzOnWith) (fun s => ⟨hf s, Set.mem_univ _⟩) (fun s => ⟨hg s, Set.mem_univ _⟩) (by simp [h₁, h₂])`.

Conclude with `congrFun heq t`.
-/
theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.intertwine_group {W₁ W₂ : Type} [NormedAddCommGroup W₁]
    [InnerProductSpace ℂ W₁] [NormedAddCommGroup W₂] [InnerProductSpace ℂ W₂]
    [FiniteDimensional ℂ W₁] [FiniteDimensional ℂ W₂]
    (U₁ : ℝ → W₁ →L[ℂ] W₁) (A₁ : W₁ →ₗ[ℂ] W₁) (h₁ : ∀ v, U₁ 0 v = v)
    (hadd₁ : ∀ s t v, U₁ (s + t) v = U₁ s (U₁ t v)) (hd₁ : ∀ v, HasDerivAt (fun t => U₁ t v) (A₁ v) 0)
    (U₂ : ℝ → W₂ →L[ℂ] W₂) (A₂ : W₂ →ₗ[ℂ] W₂) (h₂ : ∀ v, U₂ 0 v = v)
    (hadd₂ : ∀ s t v, U₂ (s + t) v = U₂ s (U₂ t v)) (hd₂ : ∀ v, HasDerivAt (fun t => U₂ t v) (A₂ v) 0)
    (T : W₁ →ₗ[ℂ] W₂) (hT : ∀ v, T (A₁ v) = A₂ (T v)) (v : W₁) (t : ℝ) :
    T (U₁ t v) = U₂ t (T v) := by
  let Tc : W₁ →L[ℝ] W₂ := (LinearMap.toContinuousLinearMap T).restrictScalars ℝ
  let Ac : W₂ →L[ℝ] W₂ := (LinearMap.toContinuousLinearMap A₂).restrictScalars ℝ
  have hTc : ∀ x, Tc x = T x := fun x => rfl
  have hAc : ∀ x, Ac x = A₂ x := fun x => rfl
  have hf : ∀ s, HasDerivAt (fun s => T (U₁ s v)) (Ac (T (U₁ s v))) s := by
    intro s
    have h := _root_.GlobalTheory.UnitaryHighestWeight.deriv_left U₁ A₁ hadd₁ hd₁ v s
    have h' := Tc.hasFDerivAt.comp_hasDerivAt s h
    simp only [Function.comp_def, hTc] at h'
    rwa [hAc, ← hT]
  have hg : ∀ s, HasDerivAt (fun s => U₂ s (T v)) (Ac (U₂ s (T v))) s := by
    intro s
    rw [hAc]
    exact _root_.GlobalTheory.UnitaryHighestWeight.deriv_left U₂ A₂ hadd₂ hd₂ (T v) s
  have heq := ODE_solution_unique_univ (v := fun _ => Ac) (s := fun _ => Set.univ)
    (K := ‖Ac‖₊) (t₀ := 0) (fun _ => Ac.lipschitz.lipschitzOnWith)
    (fun s => ⟨hf s, Set.mem_univ _⟩) (fun s => ⟨hg s, Set.mem_univ _⟩) (by simp [h₁, h₂])
  exact congrFun heq t

open Matrix Finset in

/- English proof (translation)
Introduce `k u H₁ _ _ H₂ _ _ π₁ π₂ h₁ h₂`. Establish `h₁' : _root_.PI.UpqRep.IsHCTypeU k u π₁` using `h₁`. Establish `h₂' : _root_.PI.UpqRep.IsHCTypeU k u π₂` using `h₂`. Unfold `_root_.PI.UpqRep.IsHCTypeU at h₁' h₂'`. Take `⟨hnt₁, hfd₁, hπ₁, hK₁⟩` from `h₁'`.

Take `⟨hnt₂, hfd₂, hπ₂, hK₂⟩` from `h₂'`. Take `⟨E₁, hrel₁, hder₁, hirr₁, x₁, hx₁, hw₁⟩` from `_root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest hπ₁ hK₁`. Take `⟨E₂, hrel₂, hder₂, hirr₂, x₂, hx₂, hw₂⟩` from `_root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest hπ₂ hK₂`. Take `⟨T, hT⟩` from `_root_.GlobalTheory.exists_linearEquiv_of_irreducible_isHW H₁ H₂ k E₁ E₂ _ x₁ x₂ hrel₁ hrel₂ hirr₁ hirr₂ hw₁ hw₂ hx₁ hx₂`. Use `⟨T, fun g hg x => ?_⟩` and prove the remaining obligations.

Establish `hL : _root_.Formalism.REAL.Jm (_root_.PI.UpqRep.allPos k) = 1`. Unfold `_root_.Formalism.REAL.Jm _root_.PI.UpqRep.allPos`. Simplify using the standard rewrite rules. Establish `hgL : g ∈ _root_.Formalism.REAL.Kset (_root_.PI.UpqRep.allPos k)`. Unfold `_root_.Formalism.REAL.Kset`.

Simplify using `only [hL, mul_one, one_mul, and_true]`. Conclude with `hg`. Take `⟨Y, hY, hexp, -⟩` from `_root_.Formalism.REAL.compact_exists_log_bounded _ g hgL`. Establish `hskew : Yᴴ = -Y`. Unfold `_root_.Formalism.REAL.inK _root_.Formalism.REAL.inG at hY`.

Rewrite `hY` using `[hL]`. Simplify using `only [mul_one, one_mul, and_true] at hY`. Conclude with `eq_neg_of_add_eq_zero_left hY`. Set `A₁ : H₁ →ₗ[ℂ] H₁` to `∑ a, ∑ b, Y a b • E₁ a b`. Set `A₂ : H₂ →ₗ[ℂ] H₂` to `∑ a, ∑ b, Y a b • E₂ a b`.

Establish `hA₁ : ∀ v, A₁ v = ∑ a, ∑ b, Y a b • E₁ a b v`. Introduce `v`. Simplify using `[A₁, LinearMap.sum_apply]`. Establish `hA₂ : ∀ v, A₂ v = ∑ a, ∑ b, Y a b • E₂ a b v`. Introduce `v`.

Simplify using `[A₂, LinearMap.sum_apply]`. Establish `hTA : ∀ v, T.toLinearMap (A₁ v) = A₂ (T.toLinearMap v)`. Introduce `v`. Simplify using `[hA₁, hA₂, map_sum, map_smul, hT]`. Establish `key` using `_root_.GlobalTheory.UnitaryHighestWeightUnique.intertwine_group (fun t : ℝ => π₁ (NormedSpace.exp ((t : ℂ) • Y))) A₁ (fun v => _root_.GlobalTheory.UnitaryHighestWeight.group_zero hπ₁ Y v) (fun s t v => _root_.GlobalTheory.UnitaryHighestWeight.group_add hπ₁ hskew s t v) (fun v => …`.

Simplify `key` using `[hexp]`.
-/
theorem _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_equiv_of_isHCTypeU : ∀ (k : ℕ) (u : Fin k → ℝ)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂]
    [InnerProductSpace ℂ H₂] (π₁ : Matrix (Fin k) (Fin k) ℂ → (H₁ →L[ℂ] H₁))
    (π₂ : Matrix (Fin k) (Fin k) ℂ → (H₂ →L[ℂ] H₂)), _root_.Formalism.MainNotions.S.IsHCTypeU k u π₁ → _root_.Formalism.MainNotions.S.IsHCTypeU k u π₂ →
    ∃ A : H₁ ≃ₗ[ℂ] H₂, ∀ g ∈ Matrix.unitaryGroup (Fin k) ℂ, ∀ x, A (π₁ g x) = π₂ g (A x) := by
  intro k u H₁ _ _ H₂ _ _ π₁ π₂ h₁ h₂
  have h₁' : _root_.PI.UpqRep.IsHCTypeU k u π₁ := h₁
  have h₂' : _root_.PI.UpqRep.IsHCTypeU k u π₂ := h₂
  unfold _root_.PI.UpqRep.IsHCTypeU at h₁' h₂'
  obtain ⟨hnt₁, hfd₁, hπ₁, hK₁⟩ := h₁'
  obtain ⟨hnt₂, hfd₂, hπ₂, hK₂⟩ := h₂'
  obtain ⟨E₁, hrel₁, hder₁, hirr₁, x₁, hx₁, hw₁⟩ :=
    _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest hπ₁ hK₁
  obtain ⟨E₂, hrel₂, hder₂, hirr₂, x₂, hx₂, hw₂⟩ :=
    _root_.GlobalTheory.UnitaryHighestWeightUnique.exists_derived_highest hπ₂ hK₂
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.exists_linearEquiv_of_irreducible_isHW H₁ H₂ k E₁ E₂ _ x₁ x₂ hrel₁ hrel₂
    hirr₁ hirr₂ hw₁ hw₂ hx₁ hx₂
  refine ⟨T, fun g hg x => ?_⟩
  have hL : _root_.Formalism.REAL.Jm (_root_.PI.UpqRep.allPos k) = 1 := by
    unfold _root_.Formalism.REAL.Jm _root_.PI.UpqRep.allPos
    simp
  have hgL : g ∈ _root_.Formalism.REAL.Kset (_root_.PI.UpqRep.allPos k) := by
    unfold _root_.Formalism.REAL.Kset
    simp only [hL, mul_one, one_mul, and_true]
    exact hg
  obtain ⟨Y, hY, hexp, -⟩ := _root_.Formalism.REAL.compact_exists_log_bounded _ g hgL
  have hskew : Yᴴ = -Y := by
    unfold _root_.Formalism.REAL.inK _root_.Formalism.REAL.inG at hY
    rw [hL] at hY
    simp only [mul_one, one_mul, and_true] at hY
    exact eq_neg_of_add_eq_zero_left hY
  let A₁ : H₁ →ₗ[ℂ] H₁ := ∑ a, ∑ b, Y a b • E₁ a b
  let A₂ : H₂ →ₗ[ℂ] H₂ := ∑ a, ∑ b, Y a b • E₂ a b
  have hA₁ : ∀ v, A₁ v = ∑ a, ∑ b, Y a b • E₁ a b v := by
    intro v; simp [A₁, LinearMap.sum_apply]
  have hA₂ : ∀ v, A₂ v = ∑ a, ∑ b, Y a b • E₂ a b v := by
    intro v; simp [A₂, LinearMap.sum_apply]
  have hTA : ∀ v, T.toLinearMap (A₁ v) = A₂ (T.toLinearMap v) := by
    intro v
    simp [hA₁, hA₂, map_sum, map_smul, hT]
  have key := _root_.GlobalTheory.UnitaryHighestWeightUnique.intertwine_group
    (fun t : ℝ => π₁ (NormedSpace.exp ((t : ℂ) • Y))) A₁
    (fun v => _root_.GlobalTheory.UnitaryHighestWeight.group_zero hπ₁ Y v)
    (fun s t v => _root_.GlobalTheory.UnitaryHighestWeight.group_add hπ₁ hskew s t v)
    (fun v => by rw [hA₁]; exact hder₁ Y hskew v)
    (fun t : ℝ => π₂ (NormedSpace.exp ((t : ℂ) • Y))) A₂
    (fun v => _root_.GlobalTheory.UnitaryHighestWeight.group_zero hπ₂ Y v)
    (fun s t v => _root_.GlobalTheory.UnitaryHighestWeight.group_add hπ₂ hskew s t v)
    (fun v => by rw [hA₂]; exact hder₂ Y hskew v)
    T.toLinearMap hTA x 1
  simpa [hexp] using key

end GlobalTheory.UnitaryHighestWeightUnique
