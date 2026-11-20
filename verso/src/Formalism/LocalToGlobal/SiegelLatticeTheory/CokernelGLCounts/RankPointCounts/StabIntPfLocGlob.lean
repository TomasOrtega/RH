import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfSk
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.GlobalConditionOfLocalAgreement

noncomputable section

open scoped Classical

open NumberField ValuativeRel IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

namespace Formalism.L2.SG.Pf.StabIntSh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Use `HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.F t fun p => ?_` and prove the remaining obligations. Establish `h1` using `h p`. Rewrite `h1` using `[(D.s.atP p).O_def, (D.s.atP p).compat]`. Establish `: Nontrivial (D.s.atP p).Ep`. Use `(D.s.atP p).free` as an intermediate fact.

Conclude with `Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)`. Establish `h2 : IsIntegral 𝒪[(D.s.atP p).Fp] ((D.s.atP p).ιF t)` using `(isIntegral_algebraMap_iff (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective).1 h1`. Establish `h3` using `(Valuation.integer.integers _).mem_of_integral h2`. Establish `h4 : (D.s.atP p).ιF t ≤ᵥ (D.s.atP p).ιF 1`. Rewrite using `[map_one]`.

Conclude with `(valuation (D.s.atP p).Fp).vle_one_iff.2 h3`. Simplify using `using ((D.s.atP p).val t 1).1 h4`.
-/
theorem lg_int_of_locF (t : D.host.F)
    (h : ∀ p : PlF D, (D.s.atP p).ιE (algebraMap D.host.F D.host.E t) ∈ (D.s.atP p).O) :
    t ∈ (algebraMap (𝓞 D.host.F) D.host.F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.F t fun p => ?_
  have h1 := h p
  rw [(D.s.atP p).O_def, (D.s.atP p).compat] at h1
  have : Nontrivial (D.s.atP p).Ep := by
    have := (D.s.atP p).free
    exact Module.nontrivial_of_finrank_pos (R := (D.s.atP p).Fp) (by rw [(D.s.atP p).rank]; norm_num)
  have h2 : IsIntegral 𝒪[(D.s.atP p).Fp] ((D.s.atP p).ιF t) :=
    (isIntegral_algebraMap_iff (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).injective).1 h1
  have h3 := (Valuation.integer.integers _).mem_of_integral h2
  have h4 : (D.s.atP p).ιF t ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [map_one]
    exact (valuation (D.s.atP p).Fp).vle_one_iff.2 h3
  simpa using ((D.s.atP p).val t 1).1 h4

/- English proof (translation)
Rewrite `hy`, the goal using `[(D.s.atP p).O_def]`. Conclude with `hy.map ((D.s.atP p).cj.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])`.
-/
theorem lg_cj_mem (p : PlF D) {y : (D.s.atP p).Ep} (hy : y ∈ (D.s.atP p).O) :
    (D.s.atP p).cj y ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def] at hy ⊢
  exact hy.map ((D.s.atP p).cj.toAlgHom.restrictScalars 𝒪[(D.s.atP p).Fp])

/- English proof (translation)
Rewrite using `[(D.s.atP p).O_def]`. Establish `h1 : IsIntegral ℤ ((D.s.atP p).ιE (c : D.host.E))` using `(NumberField.RingOfIntegers.isIntegral_coe c).map (D.s.atP p).ιE.toIntAlgHom`. Conclude with `h1.tower_top`.
-/
theorem lg_iota_int (p : PlF D) (c : 𝓞 D.host.E) :
    (D.s.atP p).ιE (algebraMap (𝓞 D.host.E) D.host.E c) ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h1 : IsIntegral ℤ ((D.s.atP p).ιE (c : D.host.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe c).map (D.s.atP p).ιE.toIntAlgHom
  exact h1.tower_top

/- English proof (translation)
Establish `hfix : ∀ y : D.host.E, D.conjF y = y → (∀ p : PlF D, (D.s.atP p).ιE y ∈ (D.s.atP p).O) → IsIntegral ℤ y`. Introduce `y hy hl`. Take `⟨a, rfl⟩` from `Formalism.MainNotions.BridgeLemma.conjF_fix y hy`. Take `⟨b, rfl⟩` from `lg_int_of_locF a hl`. Conclude with `(NumberField.RingOfIntegers.isIntegral_coe b).algebraMap`.

Establish `hc : ∀ p : PlF D, (D.s.atP p).ιE (D.conjF z) ∈ (D.s.atP p).O` using `fun p => by`. Rewrite using `[← (D.s.atP p).cj_ιE]`. Conclude with `lg_cj_mem p (h p)`. Establish `ht` using `hfix (z + D.conjF z) (by rw [map_add, Formalism.MainNotions.BridgeLemma.conjF_inv, add_comm]) fun p => by rw [map_add]; exact add_mem (h p) (hc p)`. Establish `hn` using `hfix (z * D.conjF z) (by rw [map_mul, Formalism.MainNotions.BridgeLemma.conjF_inv, mul_comm]) fun p => by rw [map_mul]; exact mul_mem (h p) (hc p)`.

Establish `hz : IsIntegral (integralClosure ℤ D.host.E) z`. Use `⟨Polynomial.X ^ 2 - Polynomial.C (⟨_, ht⟩ : integralClosure ℤ D.host.E) * Polynomial.X + Polynomial.C (⟨_, hn⟩ : integralClosure ℤ D.host.E), ?_, ?_⟩` and prove the remaining obligations. Use `monicity!`. Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] show z ^ 2 - (z + D.conjF z) * z + z * D.conjF z = 0`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `isIntegral_trans z hz`.
-/
theorem lg_int_of_loc (z : D.host.E) (h : ∀ p : PlF D, (D.s.atP p).ιE z ∈ (D.s.atP p).O) : IsIntegral ℤ z := by
  have hfix : ∀ y : D.host.E, D.conjF y = y → (∀ p : PlF D, (D.s.atP p).ιE y ∈ (D.s.atP p).O) →
      IsIntegral ℤ y := by
    intro y hy hl
    obtain ⟨a, rfl⟩ := Formalism.MainNotions.BridgeLemma.conjF_fix y hy
    obtain ⟨b, rfl⟩ := lg_int_of_locF a hl
    exact (NumberField.RingOfIntegers.isIntegral_coe b).algebraMap
  have hc : ∀ p : PlF D, (D.s.atP p).ιE (D.conjF z) ∈ (D.s.atP p).O := fun p => by
    rw [← (D.s.atP p).cj_ιE]
    exact lg_cj_mem p (h p)
  have ht := hfix (z + D.conjF z) (by rw [map_add, Formalism.MainNotions.BridgeLemma.conjF_inv, add_comm])
    fun p => by rw [map_add]; exact add_mem (h p) (hc p)
  have hn := hfix (z * D.conjF z) (by rw [map_mul, Formalism.MainNotions.BridgeLemma.conjF_inv, mul_comm])
    fun p => by rw [map_mul]; exact mul_mem (h p) (hc p)
  have hz : IsIntegral (integralClosure ℤ D.host.E) z := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (⟨_, ht⟩ : integralClosure ℤ D.host.E) * Polynomial.X +
      Polynomial.C (⟨_, hn⟩ : integralClosure ℤ D.host.E), ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      show z ^ 2 - (z + D.conjF z) * z + z * D.conjF z = 0
      ring
  exact isIntegral_trans z hz

/- English proof (translation)
Introduce `I hI x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `key : ∀ y ∈ (I⁻¹ : FI D), x * y ∈ (1 : FI D)`. Introduce `y hy`.

Rewrite using `[FractionalIdeal.mem_one_iff]`. Use `⟨⟨x * y, lg_int_of_loc _ fun p => ?_⟩, rfl⟩` and prove the remaining obligations. Establish `hp` using `h p`. Unfold `LocMem at hp`. Rewrite using `[map_mul]`.

Use `Submodule.span_induction (p := fun w _ => w * (D.s.atP p).ιE y ∈ (D.s.atP p).O) ?_ ?_ ?_ ?_ hp` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Rewrite using `[← map_mul]`. Establish `hiy : i * y ∈ (1 : FI D)`. Rewrite using `[← mul_inv_cancel₀ hI]`.

Conclude with `FractionalIdeal.mul_mem_mul hi hy`. Take `⟨c, hc⟩` from `(FractionalIdeal.mem_one_iff _).1 hiy`. Rewrite using `[← hc]`. Conclude with `lg_iota_int p c`. Simplify using the standard rewrite rules.

Introduce `a b _ _ ha hb`. Rewrite using `[add_mul]`. Conclude with `add_mem ha hb`. Introduce `o a _ ha`. Rewrite using `[smul_mul_assoc, Subring.smul_def]`.

Conclude with `mul_mem o.2 ha`. Establish `hle : FractionalIdeal.spanSingleton _ x * I⁻¹ ≤ 1`. Rewrite using `[FractionalIdeal.mul_le]`. Introduce `i hi j hj`. Take `⟨c, rfl⟩` from `(FractionalIdeal.mem_spanSingleton _).1 hi`.

Rewrite using `[smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c (key j hj)`. Rewrite using `[← FractionalIdeal.spanSingleton_le_iff_mem]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, inv_mul_cancel₀ hI, mul_one]`.

Use `_ ≤ I := FractionalIdeal.mul_le.2 fun a ha b hb => by`. Take `⟨c, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 (hle ha)`. Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ c hb`. Introduce `hx p`.

Conclude with `Submodule.subset_span ⟨x, hx, rfl⟩`.
-/
theorem locGlob : LocGlob D := by
  intro I hI x
  constructor
  · intro h
    have key : ∀ y ∈ (I⁻¹ : FI D), x * y ∈ (1 : FI D) := by
      intro y hy
      rw [FractionalIdeal.mem_one_iff]
      refine ⟨⟨x * y, lg_int_of_loc _ fun p => ?_⟩, rfl⟩
      have hp := h p
      unfold LocMem at hp
      rw [map_mul]
      refine Submodule.span_induction
        (p := fun w _ => w * (D.s.atP p).ιE y ∈ (D.s.atP p).O) ?_ ?_ ?_ ?_ hp
      · rintro _ ⟨i, hi, rfl⟩
        rw [← map_mul]
        have hiy : i * y ∈ (1 : FI D) := by
          rw [← mul_inv_cancel₀ hI]
          exact FractionalIdeal.mul_mem_mul hi hy
        obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 hiy
        rw [← hc]
        exact lg_iota_int p c
      · simp
      · intro a b _ _ ha hb
        rw [add_mul]
        exact add_mem ha hb
      · intro o a _ ha
        rw [smul_mul_assoc, Subring.smul_def]
        exact mul_mem o.2 ha
    have hle : FractionalIdeal.spanSingleton _ x * I⁻¹ ≤ 1 := by
      rw [FractionalIdeal.mul_le]
      intro i hi j hj
      obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ c (key j hj)
    rw [← FractionalIdeal.spanSingleton_le_iff_mem]
    calc FractionalIdeal.spanSingleton _ x = FractionalIdeal.spanSingleton _ x * I⁻¹ * I := by
          rw [mul_assoc, inv_mul_cancel₀ hI, mul_one]
      _ ≤ I := FractionalIdeal.mul_le.2 fun a ha b hb => by
          obtain ⟨c, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 (hle ha)
          rw [← Algebra.smul_def]
          exact Submodule.smul_mem _ c hb
  · intro hx p
    exact Submodule.subset_span ⟨x, hx, rfl⟩

/- English proof (translation)
Rewrite using `[ddS, Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]`. Conclude with `differentIdeal_ne_bot`. Conclude with `FaithfulSMul.algebraMap_injective _ _`.
-/
theorem lg_ddS_ne : ddS D ≠ 0 := by
  rw [ddS, Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

/- English proof (translation)
Establish `hd : ∀ k, ddPow D k ≠ 0` using `fun k => zpow_ne_zero _ lg_ddS_ne`. Use `⟨hd, fun k => mul_ne_zero ?_ (hd k)⟩` and prove the remaining obligations. Rewrite using `[Ne, FractionalIdeal.coeIdeal_eq_zero, qq]`. Introduce `h0`. Establish `hm : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {((Lat.gS D : ℕ) : 𝓞 D.host.E)}` using `Ideal.mem_span_singleton_self _`.

Rewrite `hm` using `[h0, Ideal.mem_bot]`. Conclude with `(Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne' (by exact_mod_cast hm)`.
-/
theorem shapeNZ : ShapeNZ D := by
  have hd : ∀ k, ddPow D k ≠ 0 := fun k => zpow_ne_zero _ lg_ddS_ne
  refine ⟨hd, fun k => mul_ne_zero ?_ (hd k)⟩
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, qq]
  intro h0
  have hm : ((Lat.gS D : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {((Lat.gS D : ℕ) : 𝓞 D.host.E)} :=
    Ideal.mem_span_singleton_self _
  rw [h0, Ideal.mem_bot] at hm
  exact (Formalism.MainNotions.LocalModelPeriodLattices.gS_pos D).ne' (by exact_mod_cast hm)

end Formalism.L2.SG.Pf.StabIntSh
