import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLeOneIffOfContinuousStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeEigCoset

open GlobalTheory.LFun.ConjPlace

/- English proof (translation)
Introduce `L _ _ _ n s ϖ hϖ k hk i hi V _ _ ρ R hR1 hR2 e he`. Establish `hO : ∀ a, i a ∈ Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w ↔ a ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring`. Introduce `a`. Establish `h` using `GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv _ _ s.v (GlobalTheory.HeckeFrob.conjSplit s).w i hi a`. Conclude with `h.trans (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm`.

Establish `hϖ0 : ϖ ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : Valued.v (0 : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ)` using `hϖ`. Rewrite `h0` using `[map_zero]`. Conclude with `WithZero.exp_ne_zero h0.symm`.

Use `set ϖu : (s.v.adicCompletion (maximalRealSubfield L))ˣ := Units.mk0 ϖ hϖ0 with hϖu`. Establish `ha : invT i n (dGL n ϖu k) = (dGL n (Units.map (i : _ →* _) ϖu) k)⁻¹`. Rewrite using `[← invT_dGL, map_inv, inv_inv]`. Establish `h1 : (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) = Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) (invT i n (dGL n ϖu k))`. Use function extensionality and compare the values at `g`.

Establish `hiϖ : i ϖ = ((Units.map (i : s.v.adicCompletion (maximalRealSubfield L) →* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) ϖu : ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)ˣ) : (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)`. Rewrite using `[Units.coe_map, hϖu, Units.val_mk0]`. Both sides reduce to the same expression. Rewrite using `[hiϖ, Tj_apply, Formalism.UG.dosetInd, Set.indicator_apply, Pi.one_apply]`. Use `if_congr ?_ rfl rfl` and prove the remaining obligations.

Rewrite using `[DoubleCoset.mem_doubleCoset, ha]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, y, hy, h⟩`. Conclude with `⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [← inv_inv g, h]; group⟩`. Introduce and unpack `⟨x, hx, y, hy, h⟩`.

Conclude with `⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [h]; group⟩`. Establish `hK : ∀ x : GAf L n, TrivOutside {s.v} x → (x ∈ tSet L n s ϖ k ↔ invT i n (s.loc n x) ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k)) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n))`. Introduce `x hx`. Rewrite using `[tSet, Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨-, A, hA, B, hB, h⟩`. Use `⟨invT i n A, (mem_iff_invT i hO A).1 hA, invT i n B, (mem_iff_invT i hO B).1 hB, ?_⟩` and prove the remaining obligations. Establish `: s.loc n x = A * dGL n ϖu k * B` using `Units.ext (by rw [Units.val_mul, Units.val_mul, h]; rfl)`. Rewrite using `[this, map_mul, map_mul]`. Introduce and unpack `⟨A', hA', B', hB', h⟩`.

Take `⟨A, rfl⟩` from `(invT i n).surjective A'`. Take `⟨B, rfl⟩` from `(invT i n).surjective B'`. Rewrite `h` using `[← map_mul, ← map_mul, (invT i n).apply_eq_iff_eq]`. Use `⟨hx, A, (mem_iff_invT i hO A).2 hA', B, (mem_iff_invT i hO B).2 hB', ?_⟩` and prove the remaining obligations. Rewrite using `[h]`.

Both sides reduce to the same expression. Establish `hφK : ∀ x : GAf L n, TrivOutside {s.v} x → (invT i n (s.loc n x) ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔ x ∈ Umax L n)` using `fun x hx => (mem_iff_invT i hO _).symm.trans (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx)`. Establish `hRa : ∀ γ' ∈ R.image (fun γ => invT i n (s.loc n γ)), γ' ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k)) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)`. Introduce `γ' hγ'`. Take `⟨γ, hγ, rfl⟩` from `Finset.mem_image.1 hγ'`.

Conclude with `(hK γ (hR1 γ hγ).1).1 (hR1 γ hγ)`. Establish `hRb : ∀ g ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k)) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n), ∃! γ', γ' ∈ R.image (fun γ => invT i n (s.loc n γ)) ∧ γ'⁻¹ * g ∈ GlobalTheory.LFu …`. Introduce `g hg`. Take `⟨-, -, hlift⟩` from `GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s`. Take `⟨x, ⟨hx, hxg⟩, -⟩` from `hlift ((invT i n).symm g)`.

Establish `hgx : g = invT i n (s.loc n x)` using `by rw [hxg]; simp`. Establish `hxT : x ∈ tSet L n s ϖ k` using `(hK x hx).2 (hgx ▸ hg)`. Take `⟨γ, ⟨hγ, hγx⟩, huniq⟩` from `hR2 x hxT`. Establish `key : ∀ δ ∈ R, (invT i n (s.loc n δ))⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔ δ⁻¹ * x ∈ Umax L n`. Introduce `δ hδ`.

Rewrite using `[hgx, ← map_inv, ← map_inv, ← map_mul, ← map_mul]`. Conclude with `hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 δ hδ).1) hx)`. Use `⟨invT i n (s.loc n γ), ⟨Finset.mem_image_of_mem _ hγ, (key γ hγ).2 hγx⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `γ' ⟨hγ', hγ'g⟩`. Take `⟨δ, hδ, rfl⟩` from `Finset.mem_image.1 hγ'`.

Rewrite using `[huniq δ ⟨hδ, (key δ hδ).1 hγ'g⟩]`. Establish `hinj : Set.InjOn (fun γ => invT i n (s.loc n γ)) R`. Introduce `γ₁ h₁ γ₂ h₂ heq`. Establish `hγ₂` using `hR1 γ₂ h₂`. Take `⟨γ, -, huniq⟩` from `hR2 γ₂ hγ₂`.

Establish `e1 : γ₁⁻¹ * γ₂ ∈ Umax L n`. Rewrite using `[← hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 γ₁ h₁).1) hγ₂.1), map_mul, map_mul, map_inv, map_inv]`. Simplify using `only at heq`. Rewrite using `[heq, inv_mul_cancel]`. Conclude with `one_mem _`.

Conclude with `(huniq γ₁ ⟨h₁, e1⟩).trans (huniq γ₂ ⟨h₂, by rw [inv_mul_cancel]; exact one_mem _⟩).symm`. Rewrite using `[h1, GlobalTheory.LFun.heckeVec_dosetInd he hRa hRb, Finset.sum_image hinj]`. Use `Finset.sum_congr rfl fun γ _ => ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.HeckeEigConj.map_loc_conjSplit]`.
-/
theorem heckeVec_Tj_inv_conj_eq_sum : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (ϖ : s.v.adicCompletion (maximalRealSubfield L)), IsUnif L s.v ϖ → ∀ (k : ℕ), k ≤ n →
    ∀ (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L), Continuous i →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)) V)
    (R : Finset (GAf L n)), (∀ γ ∈ R, γ ∈ tSet L n s ϖ k) → (∀ x ∈ tSet L n s ϖ k, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) →
    ∀ e ∈ GlobalTheory.PRep.fixed ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      GlobalTheory.LFun.heckeVec ρ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)
                   (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) e =
        ∑ γ ∈ R, ρ (Matrix.GeneralLinearGroup.map i.toRingHom ((GlobalTheory.HeckeFrob.conjSplit s).loc n γ)) e := by
  intro L _ _ _ n s ϖ hϖ k hk i hi V _ _ ρ R hR1 hR2 e he
  classical
  have hO : ∀ a, i a ∈ Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w ↔
      a ∈ (s.v.adicCompletionIntegers (maximalRealSubfield L)).toSubring := by
    intro a
    have h := GlobalTheory.T.valued_le_one_iff_of_continuous_ringEquiv _ _ s.v (GlobalTheory.HeckeFrob.conjSplit s).w i hi a
    exact h.trans (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).symm
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    have h0 : Valued.v (0 : s.v.adicCompletion (maximalRealSubfield L)) = WithZero.exp (-1 : ℤ) := hϖ
    rw [map_zero] at h0
    exact WithZero.exp_ne_zero h0.symm
  set ϖu : (s.v.adicCompletion (maximalRealSubfield L))ˣ := Units.mk0 ϖ hϖ0 with hϖu
  have ha : invT i n (dGL n ϖu k) = (dGL n (Units.map (i : _ →* _) ϖu) k)⁻¹ := by
    rw [← invT_dGL, map_inv, inv_inv]
  have h1 : (fun g => Formalism.UG.Tj ℂ n (Formalism.UG.Ov L (GlobalTheory.HeckeFrob.conjSplit s).w) (i ϖ) k g⁻¹) =
      Formalism.UG.dosetInd ℂ (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) (invT i n (dGL n ϖu k)) := by
    funext g
    have hiϖ : i ϖ = ((Units.map (i : s.v.adicCompletion (maximalRealSubfield L) →* (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) ϖu :
        ((GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L)ˣ) : (GlobalTheory.HeckeFrob.conjSplit s).w.adicCompletion L) := by
      rw [Units.coe_map, hϖu, Units.val_mk0]
      rfl
    rw [hiϖ, Tj_apply, Formalism.UG.dosetInd, Set.indicator_apply, Pi.one_apply]
    refine if_congr ?_ rfl rfl
    rw [DoubleCoset.mem_doubleCoset, ha]
    constructor
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [← inv_inv g, h]; group⟩
    · rintro ⟨x, hx, y, hy, h⟩
      exact ⟨y⁻¹, inv_mem hy, x⁻¹, inv_mem hx, by rw [h]; group⟩
  have hK : ∀ x : GAf L n, TrivOutside {s.v} x → (x ∈ tSet L n s ϖ k ↔ invT i n (s.loc n x) ∈
      DoubleCoset.doubleCoset (invT i n (dGL n ϖu k)) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _)
        (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n)) := by
    intro x hx
    rw [tSet, Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset]
    constructor
    · rintro ⟨-, A, hA, B, hB, h⟩
      refine ⟨invT i n A, (mem_iff_invT i hO A).1 hA, invT i n B, (mem_iff_invT i hO B).1 hB, ?_⟩
      have : s.loc n x = A * dGL n ϖu k * B := Units.ext (by rw [Units.val_mul, Units.val_mul, h]; rfl)
      rw [this, map_mul, map_mul]
    · rintro ⟨A', hA', B', hB', h⟩
      obtain ⟨A, rfl⟩ := (invT i n).surjective A'
      obtain ⟨B, rfl⟩ := (invT i n).surjective B'
      rw [← map_mul, ← map_mul, (invT i n).apply_eq_iff_eq] at h
      refine ⟨hx, A, (mem_iff_invT i hO A).2 hA', B, (mem_iff_invT i hO B).2 hB', ?_⟩
      rw [h]
      rfl
  have hφK : ∀ x : GAf L n, TrivOutside {s.v} x →
      (invT i n (s.loc n x) ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔ x ∈ Umax L n) :=
    fun x hx => (mem_iff_invT i hO _).symm.trans (GlobalTheory.HeckeScalarSph.loc_mem_GLint_iff s hx)
  have hRa : ∀ γ' ∈ R.image (fun γ => invT i n (s.loc n γ)), γ' ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k))
      (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n) := by
    intro γ' hγ'
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hγ'
    exact (hK γ (hR1 γ hγ).1).1 (hR1 γ hγ)
  have hRb : ∀ g ∈ DoubleCoset.doubleCoset (invT i n (dGL n ϖu k))
      (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n : Set _) (GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n),
      ∃! γ', γ' ∈ R.image (fun γ => invT i n (s.loc n γ)) ∧ γ'⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n := by
    intro g hg
    obtain ⟨-, -, hlift⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
    obtain ⟨x, ⟨hx, hxg⟩, -⟩ := hlift ((invT i n).symm g)
    have hgx : g = invT i n (s.loc n x) := by rw [hxg]; simp
    have hxT : x ∈ tSet L n s ϖ k := (hK x hx).2 (hgx ▸ hg)
    obtain ⟨γ, ⟨hγ, hγx⟩, huniq⟩ := hR2 x hxT
    have key : ∀ δ ∈ R, (invT i n (s.loc n δ))⁻¹ * g ∈ GlobalTheory.LFun.KGL (GlobalTheory.HeckeFrob.conjSplit s).w n ↔
        δ⁻¹ * x ∈ Umax L n := by
      intro δ hδ
      rw [hgx, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
      exact hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 δ hδ).1) hx)
    refine ⟨invT i n (s.loc n γ), ⟨Finset.mem_image_of_mem _ hγ, (key γ hγ).2 hγx⟩, ?_⟩
    rintro γ' ⟨hγ', hγ'g⟩
    obtain ⟨δ, hδ, rfl⟩ := Finset.mem_image.1 hγ'
    rw [huniq δ ⟨hδ, (key δ hδ).1 hγ'g⟩]
  have hinj : Set.InjOn (fun γ => invT i n (s.loc n γ)) R := by
    intro γ₁ h₁ γ₂ h₂ heq
    have hγ₂ := hR1 γ₂ h₂
    obtain ⟨γ, -, huniq⟩ := hR2 γ₂ hγ₂
    have e1 : γ₁⁻¹ * γ₂ ∈ Umax L n := by
      rw [← hφK _ (GlobalTheory.HeckeScalarSph.triv_mul (GlobalTheory.HeckeScalarSph.triv_inv (hR1 γ₁ h₁).1) hγ₂.1), map_mul, map_mul,
        map_inv, map_inv]
      simp only at heq
      rw [heq, inv_mul_cancel]
      exact one_mem _
    exact (huniq γ₁ ⟨h₁, e1⟩).trans (huniq γ₂ ⟨h₂, by rw [inv_mul_cancel]; exact one_mem _⟩).symm
  rw [h1, GlobalTheory.LFun.heckeVec_dosetInd he hRa hRb, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [GlobalTheory.HeckeEigConj.map_loc_conjSplit]

end GlobalTheory.HeckeEigCoset
