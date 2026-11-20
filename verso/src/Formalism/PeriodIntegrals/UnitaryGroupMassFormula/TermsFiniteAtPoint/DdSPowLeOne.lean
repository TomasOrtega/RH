import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermsFiniteAtPoint.ResFin
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.AdjointActionReduction

noncomputable section

open scoped Classical

namespace PI.TermsAtPtFiniteW

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.Saturated

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `ha` using `a.isLt`. Take `⟨m, hm⟩ : ∃ m : ℕ, D.R.rS = (a : ℕ) + m` from `⟨D.R.rS - (a : ℕ), by omega⟩`. Establish `haa : aaS D a = (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹`. Unfold `aaS ddS`. Rewrite using `[FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_neg]`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite `ht` using `[haa]`. Distinguish the cases in `hJ : (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 0`. Rewrite `ht` using `[hJ]`.

Establish `ht0 : t = 0` using `by first`. Consider the case `(rw [FractionalIdeal.inv_zero', FractionalIdeal.mem_zero_iff] at ht; exact ht)`. Consider the case `(rw [inv_zero, FractionalIdeal.mem_zero_iff] at ht; exact ht)`. Consider the case `simpa using ht`. Conclude with `⟨0, by rw [ht0, map_zero, mul_zero]⟩`.

Rewrite `ht`, `first` using `[FractionalIdeal.inv_eq]`. Consider the case `rw [FractionalIdeal.mem_div_iff_of_ne_zero hJ] at ht`. Consider the case `rw [FractionalIdeal.mem_div_iff_of_nonzero hJ] at ht`. Establish `hN : ((Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ m) ∈ ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E))` using `Ideal.pow_mem_pow (Ideal.absNorm_mem _) m`. Establish `hy : algebraMap (𝓞 D.host.E) D.host.E ((Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ m) ∈ (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : Fractio …` using `by first`.

Consider the case `exact FractionalIdeal.mem_coeIdeal_of_mem _ hN`. Consider the case `exact FractionalIdeal.mem_coeIdeal_of_mem hN`. Consider the case `exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, hN, rfl⟩`. Establish `h1` using `ht _ hy`. Rewrite `h1` using `[FractionalIdeal.mem_one_iff]`.

Take `⟨o', ho'⟩` from `h1`. Use `⟨(Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ (a : ℕ) * o', ?_⟩` and prove the remaining obligations. Establish `hsplit : (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ D.R.rS = (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ (a : ℕ) * (Ideal.absNorm (Ideal.map (a …`. Rewrite using `[← pow_add, ← hm]`. Rewrite using `[map_mul, ho']`.

Simplify using `only [ndS, map_pow, map_natCast, Nat.cast_pow, hsplit]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ndS_mul_int (D : D7) (a : Fin D.R.rS) (t : D.host.E) (ht : t ∈ aaS D a) :
    ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * t := by
  have ha := a.isLt
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.R.rS = (a : ℕ) + m := ⟨D.R.rS - (a : ℕ), by omega⟩
  have haa : aaS D a = (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
    unfold aaS ddS
    rw [FractionalIdeal.coeIdeal_pow, ← zpow_natCast, ← zpow_neg]
    congr 1
    omega
  rw [haa] at ht
  by_cases hJ : (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 0
  · rw [hJ] at ht
    have ht0 : t = 0 := by
      first
        | (rw [FractionalIdeal.inv_zero', FractionalIdeal.mem_zero_iff] at ht; exact ht)
        | (rw [inv_zero, FractionalIdeal.mem_zero_iff] at ht; exact ht)
        | simpa using ht
    exact ⟨0, by rw [ht0, map_zero, mul_zero]⟩
  · rw [FractionalIdeal.inv_eq] at ht
    first
      | rw [FractionalIdeal.mem_div_iff_of_ne_zero hJ] at ht
      | rw [FractionalIdeal.mem_div_iff_of_nonzero hJ] at ht
    have hN : ((Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ m) ∈ ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) :=
      Ideal.pow_mem_pow (Ideal.absNorm_mem _) m
    have hy : algebraMap (𝓞 D.host.E) D.host.E ((Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ m) ∈
        (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ m : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      by
        first
          | exact FractionalIdeal.mem_coeIdeal_of_mem _ hN
          | exact FractionalIdeal.mem_coeIdeal_of_mem hN
          | exact (FractionalIdeal.mem_coeIdeal _).mpr ⟨_, hN, rfl⟩
    have h1 := ht _ hy
    rw [FractionalIdeal.mem_one_iff] at h1
    obtain ⟨o', ho'⟩ := h1
    refine ⟨(Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : (𝓞 D.host.E)) ^ (a : ℕ) * o', ?_⟩
    have hsplit : (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ D.R.rS =
        (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ (a : ℕ) * (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) : D.host.E) ^ m := by
      rw [← pow_add, ← hm]
    rw [map_mul, ho']
    simp only [ndS, map_pow, map_natCast, Nat.cast_pow, hsplit]
    ring

/- English proof (translation)
Introduce `D T F0 Λ f L hff hef hL hΛ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hd : differentIdeal ℤ (𝓞 D.host.F) ≠ ⊥` using `by first`. Consider the case `exact differentIdeal_ne_bot`. Consider the case `exact differentIdeal_ne_bot (K := ℚ) (L := D.host.F)`.

Consider the case `exact differentIdeal_ne_bot ℤ ℚ D.host.F (𝓞 D.host.F)`. Establish `hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))` using `by first`. Consider the case `exact FaithfulSMul.algebraMap_injective _ _`. Consider the case `exact NoZeroSMulDivisors.algebraMap_injective _ _`. Consider the case `(have h1 : Function.Injective (algebraMap (𝓞 D.host.F) D.host.E) := by`.

Rewrite using `[IsScalarTower.algebraMap_eq (𝓞 D.host.F) D.host.F D.host.E, RingHom.coe_comp]`. Conclude with `(algebraMap D.host.F D.host.E).injective.comp (IsFractionRing.injective _ _)`. Rewrite `h1` using `[IsScalarTower.algebraMap_eq (𝓞 D.host.F) (𝓞 D.host.E) D.host.E, RingHom.coe_comp]`. Conclude with `h1.of_comp)`. Establish `hmap : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ ⊥`.

Rewrite using `[Ne, Ideal.map_eq_bot_iff_of_injective hinj]` and apply the resulting hypothesis. Establish `hN : Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]` and apply the resulting hypothesis. Unfold `ndS`. Conclude with `pow_pos (Nat.pos_of_ne_zero hN) _`.

Introduce `x hx c`. Establish `hec : ∀ a, (VS D).hT (f c) (F0.e a) = if a = c then 1 else 0`. Introduce `a`. Establish `hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f c)) = (VS D).hT (f c) (F0.e a)` using `by first`. Consider the case `exact (VS D).herm.eq _ _`.

Consider the case `exact (VS D).herm _ _`. Rewrite using `[← hs, hef]`. Apply the tactic sequence `split_ifs <;> simp`. Set `P : Submodule (𝓞 D.host.E) (VS D).V` to `{ carrier := {y | ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y)} add_mem' := by`. Introduce and unpack `y z ⟨o1, h1⟩ ⟨o2, h2⟩`.

Conclude with `(show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y + z) from ⟨o1 + o2, by rw [map_add, map_add, mul_add, h1, h2]⟩)`. Use the proof step `zero_mem' := by`. Conclude with `(show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (0) from ⟨0, by rw [map_zero, map_zero, mul_zero]⟩)`. Use the proof step `smul_mem' := by`. Introduce and unpack `r y ⟨o, h⟩`.

Use `(show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (r • y) from ⟨r * o, ?_⟩)` and prove the remaining obligations. Rewrite using `[← algebraMap_smul D.host.E r y, map_smul, smul_eq_mul, map_mul, h]`. Use `ring }`. Establish `hP : Λ ≤ P`. Rewrite using `[hΛ]`.

Use `sup_le (sup_le ?_ ?_) ?_` and prove the remaining obligations. Unfold `latSpan`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `y ⟨a, t, ht, rfl⟩`. Use `show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (t • F0.e a)`.

Rewrite using `[map_smul, smul_eq_mul, hec a]`. Distinguish the cases in `hac : a = c`. Substitute `hac` using the available equality. Take `⟨o, ho⟩` from `ndS_mul_int D a t ht`. Conclude with `⟨o, by rw [ho, if_pos rfl, mul_one]⟩`.

Conclude with `⟨0, by rw [if_neg hac, mul_zero, mul_zero, map_zero]⟩`. Introduce `y hy show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y)`. Conclude with `⟨0, by rw [(hL y hy c).2, mul_zero, map_zero]⟩`. Unfold `latSpan`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `y ⟨a, t, ht, rfl⟩`. Use `show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (t • f a)`. Conclude with `⟨0, by rw [map_smul, smul_eq_mul, hff c a, mul_zero, mul_zero, map_zero]⟩`. Take `⟨o, ho⟩` from `hP hx`. Conclude with `⟨o, ho⟩`.
-/
theorem fInt_holds : FInt := by
  intro D T F0 Λ f L hff hef hL hΛ
  refine ⟨?_, ?_⟩
  ·
    have hd : differentIdeal ℤ (𝓞 D.host.F) ≠ ⊥ := by
      first
        | exact differentIdeal_ne_bot
        | exact differentIdeal_ne_bot (K := ℚ) (L := D.host.F)
        | exact differentIdeal_ne_bot ℤ ℚ D.host.F (𝓞 D.host.F)
    have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
      first
        | exact FaithfulSMul.algebraMap_injective _ _
        | exact NoZeroSMulDivisors.algebraMap_injective _ _
        | (have h1 : Function.Injective (algebraMap (𝓞 D.host.F) D.host.E) := by
             rw [IsScalarTower.algebraMap_eq (𝓞 D.host.F) D.host.F D.host.E, RingHom.coe_comp]
             exact (algebraMap D.host.F D.host.E).injective.comp (IsFractionRing.injective _ _)
           rw [IsScalarTower.algebraMap_eq (𝓞 D.host.F) (𝓞 D.host.E) D.host.E, RingHom.coe_comp] at h1
           exact h1.of_comp)
    have hmap : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ ⊥ := by
      rwa [Ne, Ideal.map_eq_bot_iff_of_injective hinj]
    have hN : Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    unfold ndS
    exact pow_pos (Nat.pos_of_ne_zero hN) _
  · intro x hx c

    have hec : ∀ a, (VS D).hT (f c) (F0.e a) = if a = c then 1 else 0 := by
      intro a
      have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f c)) = (VS D).hT (f c) (F0.e a) := by
        first
          | exact (VS D).herm.eq _ _
          | exact (VS D).herm _ _
      rw [← hs, hef]
      split_ifs <;> simp
    let P : Submodule (𝓞 D.host.E) (VS D).V :=
      { carrier := {y | ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y)}
        add_mem' := by
          rintro y z ⟨o1, h1⟩ ⟨o2, h2⟩
          exact (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y + z) from ⟨o1 + o2, by rw [map_add, map_add, mul_add, h1, h2]⟩)
        zero_mem' := by
          exact (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (0) from ⟨0, by rw [map_zero, map_zero, mul_zero]⟩)
        smul_mem' := by
          rintro r y ⟨o, h⟩
          refine (show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (r • y) from ⟨r * o, ?_⟩)
          rw [← algebraMap_smul D.host.E r y, map_smul, smul_eq_mul, map_mul, h]
          ring }
    have hP : Λ ≤ P := by
      rw [hΛ]
      refine sup_le (sup_le ?_ ?_) ?_
      · unfold latSpan
        rw [Submodule.span_le]
        rintro y ⟨a, t, ht, rfl⟩
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (t • F0.e a)
        rw [map_smul, smul_eq_mul, hec a]
        by_cases hac : a = c
        · subst hac
          obtain ⟨o, ho⟩ := ndS_mul_int D a t ht
          exact ⟨o, by rw [ho, if_pos rfl, mul_one]⟩
        · exact ⟨0, by rw [if_neg hac, mul_zero, mul_zero, map_zero]⟩
      · intro y hy
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (y)
        exact ⟨0, by rw [(hL y hy c).2, mul_zero, map_zero]⟩
      · unfold latSpan
        rw [Submodule.span_le]
        rintro y ⟨a, t, ht, rfl⟩
        show ∃ o : (𝓞 D.host.E), algebraMap (𝓞 D.host.E) D.host.E o = (ndS D : D.host.E) * (VS D).hT (f c) (t • f a)
        exact ⟨0, by rw [map_smul, smul_eq_mul, hff c a, mul_zero, mul_zero, map_zero]⟩
    obtain ⟨o, ho⟩ := hP hx
    exact ⟨o, ho⟩

end PI.TermsAtPtFiniteW
