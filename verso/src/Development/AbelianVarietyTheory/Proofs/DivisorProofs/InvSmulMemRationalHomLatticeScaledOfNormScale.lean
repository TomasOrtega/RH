import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNormStatement

noncomputable section

open NumberField

namespace GlobalTheory.VacRead

/- English proof (translation)
Establish `hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `D.host.ccK_ne_bot`. Establish `hN : (Ideal.absNorm cc : D.host.E) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`.

Conclude with `hc`. Establish `hcE : ((c : D.host.K) : D.host.E) ∈ cE D cc` using `Submodule.subset_span ⟨c, hcc, rfl⟩`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨α, hα, γ₂, hγ₂, rfl⟩` from `hy`.

Take `⟨o₁, h₁⟩` from `(GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).1 γ hγ γ₂ hγ₂`. Take `⟨o₂, h₂⟩` from `(GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).1 α hα _ hcE`. Use `⟨o₁ * o₂, ?_⟩` and prove the remaining obligations. Establish `e : D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * (r * D.host.conj α * γ₂ / (Ideal.absNorm cc : D.host.E)) / (Ideal.absNorm D.host.ccK : D.host.E) = (D.host.conj γ * γ₂ / (Ideal.absNorm D.host.ccK : D.host.E)) * (D.host.conj α * ((c : D.host.K) : D.host.E) / (Ideal.absNorm …`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[e, h₁, h₂, mul_div_cancel_left₀ _ hN0, mul_div_cancel_left₀ _ hN]`. Simplify using the standard rewrite rules. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨u, hu⟩` from `hx`.

Take `⟨v, hv⟩` from `hy`. Conclude with `⟨u + v, by rw [map_add, hu, hv]; ring⟩`. Consider the case `smul o x _ hx`. Take `⟨u, hu⟩` from `hx`. Use `⟨o * u, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hu, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem int_of_mem_bInv (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {γ : D.host.E} (hγ : γ ∈ cE D D.host.ccK) {c : 𝓞 D.host.K} (hcc : c ∈ cc) {y : D.host.E} (hy : y ∈ bInv D cc r) :
    GlobalTheory.InertSign.IntE D (D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * y /
      (Ideal.absNorm D.host.ccK : D.host.E)) := by
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  have hN : (Ideal.absNorm cc : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hc
  have hcE : ((c : D.host.K) : D.host.E) ∈ cE D cc := Submodule.subset_span ⟨c, hcc, rfl⟩
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, hα, γ₂, hγ₂, rfl⟩ := hy
    obtain ⟨o₁, h₁⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).1 γ hγ γ₂ hγ₂
    obtain ⟨o₂, h₂⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).1 α hα _ hcE
    refine ⟨o₁ * o₂, ?_⟩
    have e : D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * (r * D.host.conj α * γ₂ / (Ideal.absNorm cc : D.host.E)) /
        (Ideal.absNorm D.host.ccK : D.host.E) =
        (D.host.conj γ * γ₂ / (Ideal.absNorm D.host.ccK : D.host.E)) *
          (D.host.conj α * ((c : D.host.K) : D.host.E) / (Ideal.absNorm cc : D.host.E)) := by
      field_simp
    rw [e, h₁, h₂, mul_div_cancel_left₀ _ hN0, mul_div_cancel_left₀ _ hN]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, hu, hv]; ring⟩
  | smul o x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨o * u, ?_⟩
    rw [map_mul, hu, Algebra.smul_def]
    ring

/- English proof (translation)
Proceed by induction on `hε using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨c₀, hc₀, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨c₀, hc₀, α, hα, rfl⟩`. Consider the case `zero => rw [zero_mul]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul o x _ hx => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ o hx`.
-/
theorem mul_mem_Iid (D : Formalism.BasicNotions.D7) {ε α : D.host.E} (hε : ε ∈ cE D D.host.ccK)
    (hα : α ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) : ε * α ∈ GlobalTheory.InertSign.Iid D D.host.ccK := by
  induction hε using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c₀, hc₀, rfl⟩ := hx
    exact Submodule.subset_span ⟨c₀, hc₀, α, hα, rfl⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ o hx

/- English proof (translation)
Establish `hA'` using `GlobalTheory.ThetaLatImage.mem_homL.1 hA`. Establish `hint : ∀ i j, GlobalTheory.InertSign.IntE D (A i j)`. Introduce `i j`. Establish `h1 : Pi.single j (1 : D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D a`. Rewrite using `[GlobalTheory.ThetaLatImage.mem_stdL]`.

Introduce `k`. Use `⟨if k = j then 1 else 0, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : k = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`. Establish `h2` using `GlobalTheory.ThetaLatImage.mem_stdL.1 (hA' _ h1) i`. Establish `hcol : A.mulVec (Pi.single j 1) i = A i j`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Rewrite `h2` using `[hcol]`. Then use the resulting hypothesis.

Rewrite using `[GlobalTheory.ThetaLatImage.mem_homL]`. Introduce `x hx`. Rewrite using `[GlobalTheory.ThetaLatImage.mem_stdL]`. Introduce `i`. Establish `hy : A.mulVec x i ∈ bInv D cc r`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Take `⟨o, ho⟩` from `hint i j`. Rewrite using `[← ho, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ o (mem_lsB.1 hx j)`.

Use `int_of_mem_bInv D cc r hc hr hγ hcc hy` as an intermediate fact. Rewrite using `[Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]`. Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem smul_mem_homL (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {γ : D.host.E} (hγ : γ ∈ cE D D.host.ccK) {c : 𝓞 D.host.K} (hcc : c ∈ cc)
    {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)) :
    (D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ / (Ideal.absNorm D.host.ccK : D.host.E)) • A ∈
      Formalism.MainNotions.TaylorLogMetric.homL D (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hA' := GlobalTheory.ThetaLatImage.mem_homL.1 hA
  have hint : ∀ i j, GlobalTheory.InertSign.IntE D (A i j) := by
    intro i j
    have h1 : Pi.single j (1 : D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D a := by
      rw [GlobalTheory.ThetaLatImage.mem_stdL]
      intro k
      refine ⟨if k = j then 1 else 0, ?_⟩
      by_cases h : k = j
      · subst h; simp
      · simp [h]
    have h2 := GlobalTheory.ThetaLatImage.mem_stdL.1 (hA' _ h1) i
    have hcol : A.mulVec (Pi.single j 1) i = A i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rwa [hcol] at h2
  rw [GlobalTheory.ThetaLatImage.mem_homL]
  intro x hx
  rw [GlobalTheory.ThetaLatImage.mem_stdL]
  intro i
  have hy : A.mulVec x i ∈ bInv D cc r := by
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨o, ho⟩ := hint i j
    rw [← ho, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o (mem_lsB.1 hx j)
  have := int_of_mem_bInv D cc r hc hr hγ hcc hy
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  convert this using 1
  ring

/- English proof (translation)
Establish `hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0`. Rewrite using `[Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `D.host.ccK_ne_bot`. Use `set X := r⁻¹ * (((c : D.host.K) : D.host.E) * α) with hX`. Establish `key : ∀ t ∈ Submodule.span (𝓞 D.host.E) {t | ∃ γ ∈ cE D D.host.ccK, ∃ ε ∈ cE D D.host.ccK, t = D.host.conj γ * ε}, (t * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A ∈ GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)`.

Introduce `t ht`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem t ht`. Take `⟨γ, hγ, ε, hε, rfl⟩` from `ht`. Establish `e : (D.host.conj γ * ε * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A = (ε * α) • ((D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ / (Ideal.absNorm D.host.ccK : D.host.E)) • A)`.

Rewrite using `[smul_smul, hX]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Submodule.subset_span ⟨ε * α, mul_mem_Iid D hε hα, _, smul_mem_homL D cc r a d hc hr hγ hcc hA, rfl⟩`.

Consider the case `zero => rw [zero_mul, zero_smul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [add_mul, add_smul]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul o x _ hx => rw [smul_mul_assoc, smul_assoc]`.

Conclude with `Submodule.smul_mem _ o hx`. Establish `h` using `key _ (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).2`. Rewrite `h` using `[mul_inv_cancel_left₀ hN0]`. Then use the resulting hypothesis.
-/
theorem gen_mem_RL (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {c : 𝓞 D.host.K} (hcc : c ∈ cc) {α : D.host.E} (hα : α ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)) :
    (r⁻¹ * (((c : D.host.K) : D.host.E) * α)) • A ∈
      GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  set X := r⁻¹ * (((c : D.host.K) : D.host.E) * α) with hX
  have key : ∀ t ∈ Submodule.span (𝓞 D.host.E) {t | ∃ γ ∈ cE D D.host.ccK, ∃ ε ∈ cE D D.host.ccK,
      t = D.host.conj γ * ε},
      (t * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A ∈
        GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨γ, hγ, ε, hε, rfl⟩ := ht
      have e : (D.host.conj γ * ε * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A =
          (ε * α) • ((D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ /
            (Ideal.absNorm D.host.ccK : D.host.E)) • A) := by
        rw [smul_smul, hX]
        congr 1
        ring
      rw [e]
      exact Submodule.subset_span ⟨ε * α, mul_mem_Iid D hε hα, _, smul_mem_homL D cc r a d hc hr hγ hcc hA, rfl⟩
    | zero => rw [zero_mul, zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_mul, add_smul]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx => rw [smul_mul_assoc, smul_assoc]; exact Submodule.smul_mem _ o hx
  have h := key _ (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).2
  rwa [mul_inv_cancel_left₀ hN0] at h

/- English proof (translation)
Introduce `D cc r a d hc hs z hz`. Establish `hr : r ≠ 0` using `GlobalTheory.NormExact.IsScale.ne_zero hc hs`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨t, ht, A, hA, rfl⟩` from `hz`.

Rewrite using `[smul_smul]`. Proceed by induction on `ht using Submodule.span_induction with`. Consider the case `mem t ht`. Take `⟨c, hcc, α, hα, rfl⟩` from `ht`. Conclude with `gen_mem_RL D cc r a d hc hr hcc hα hA`.

Consider the case `zero => rw [mul_zero, zero_smul]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [mul_add, add_smul]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul o x _ hx => rw [mul_smul_comm, smul_assoc]`.

Conclude with `Submodule.smul_mem _ o hx`. Consider the case `zero => rw [smul_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [smul_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul o x _ hx => rw [smul_comm]`. Conclude with `Submodule.smul_mem _ o hx`.
-/
theorem rl_div_scale : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ), cc ≠ ⊥ →
    GlobalTheory.NormExact.IsScale D cc r → ∀ z ∈ GlobalTheory.InertSign.RL D cc (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d),
      r⁻¹ • z ∈ GlobalTheory.InertSign.RL D D.host.ccK (GlobalTheory.VacRead.lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  intro D cc r a d hc hs z hz
  have hr : r ≠ 0 := GlobalTheory.NormExact.IsScale.ne_zero hc hs
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    rw [smul_smul]
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨c, hcc, α, hα, rfl⟩ := ht
      exact gen_mem_RL D cc r a d hc hr hcc hα hA
    | zero => rw [mul_zero, zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add, add_smul]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx => rw [mul_smul_comm, smul_assoc]; exact Submodule.smul_mem _ o hx
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

end GlobalTheory.VacRead
