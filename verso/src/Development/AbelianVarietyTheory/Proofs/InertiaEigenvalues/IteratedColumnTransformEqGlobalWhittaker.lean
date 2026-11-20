import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import GroundTheory.GlobalFields.TateThesis.AdelicChar
open NumberField Matrix GlobalTheory.CuspRep

noncomputable section

open MeasureTheory GroundTheory.Automorphic.FourierWhittaker

namespace GlobalTheory.CuspGeneric.WhitEq

/- English proof (translation)
Take `⟨rfl⟩` from `hB`. Use `letI : MeasurableSpace G := borel G`. Use `haveI : BorelSpace G := ⟨rfl⟩`. Establish `hex : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1` using `⟨(μ, D), inferInstance, hD, h1⟩`. Unfold `avg`.

Rewrite using `[dif_pos hex]`. Take `⟨hH, hD', h1'⟩` from `hex.choose_spec`. Use `set ν := hex.choose.1`. Use `set D' := hex.choose.2`. Establish `hν : ν = Measure.addHaarScalarFactor ν μ • μ` using `Measure.isAddLeftInvariant_eq_smul ν μ`.

Establish `hc0 : Measure.addHaarScalarFactor ν μ ≠ 0`. Introduce `h0`. Establish `: ν = 0` using `by rw [hν, h0, zero_smul]`. Establish `hpos : 0 < ν Set.univ` using `IsOpen.measure_pos ν isOpen_univ ⟨0, trivial⟩`. Rewrite `hpos` using `[this]`.

Simplify using `at hpos`. Establish `hac : μ ≪ ν`. Rewrite using `[hν]`. Conclude with `Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)`. Establish `hDμ : IsAddFundamentalDomain Γ D' μ` using `hD'.mono hac`.

Establish `hμD' : μ D' = 1` using `by rw [hDμ.measure_eq hD, h1]`. Establish `hc1 : Measure.addHaarScalarFactor ν μ = 1`. Use `h1'` as an intermediate fact. Rewrite `this` using `[hν, Measure.smul_apply, hμD', ENNReal.smul_def, smul_eq_mul, mul_one]`. Conclude with `this` after adjusting the coercions.

Establish `hνμ : ν = μ` using `by rw [hν, hc1, one_smul]`. Rewrite using `[hνμ]`. Conclude with `hDμ.setIntegral_eq hD fun g x => hΦ g g.2 x`.
-/
theorem avg_eq_setIntegral {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [m : MeasurableSpace G] [hB : BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (D : Set G)
    (hD : IsAddFundamentalDomain Γ D μ) (h1 : μ D = 1) (Φ : G → ℂ)
    (hΦ : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) :
    avg Γ Φ = ∫ x in D, Φ x ∂μ := by
  obtain ⟨rfl⟩ := hB
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩
  have hex : ∃ p : Measure G × Set G, p.1.IsAddHaarMeasure ∧ IsAddFundamentalDomain Γ p.2 p.1 ∧ p.1 p.2 = 1 :=
    ⟨(μ, D), inferInstance, hD, h1⟩
  unfold avg
  rw [dif_pos hex]
  obtain ⟨hH, hD', h1'⟩ := hex.choose_spec
  set ν := hex.choose.1
  set D' := hex.choose.2
  have hν : ν = Measure.addHaarScalarFactor ν μ • μ := Measure.isAddLeftInvariant_eq_smul ν μ
  have hc0 : Measure.addHaarScalarFactor ν μ ≠ 0 := by
    intro h0
    have : ν = 0 := by rw [hν, h0, zero_smul]
    have hpos : 0 < ν Set.univ := IsOpen.measure_pos ν isOpen_univ ⟨0, trivial⟩
    rw [this] at hpos
    simp at hpos
  have hac : μ ≪ ν := by
    rw [hν]
    exact Measure.absolutelyContinuous_smul (by exact_mod_cast hc0)
  have hDμ : IsAddFundamentalDomain Γ D' μ := hD'.mono hac
  have hμD' : μ D' = 1 := by rw [hDμ.measure_eq hD, h1]
  have hc1 : Measure.addHaarScalarFactor ν μ = 1 := by
    have := h1'
    rw [hν, Measure.smul_apply, hμD', ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact_mod_cast this
  have hνμ : ν = μ := by rw [hν, hc1, one_smul]
  rw [hνμ]
  exact hDμ.setIntegral_eq hD fun g x => hΦ g g.2 x

def colIx {a k : ℕ} (hk : k < a) : UnipotentBlockColumnIndex a k k ≃ Fin k where
  toFun t := ⟨t.1.1.val, t.2.1⟩
  invFun i := ⟨(⟨i.val, by omega⟩, ⟨k, hk⟩), i.2, le_rfl, le_rfl⟩
  left_inv t := by
    obtain ⟨⟨i, j⟩, h1, h2, h3⟩ := t
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Fin.ext
      show k = (j : ℕ)
      simp only at h2 h3
      omega
  right_inv i := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `(1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i j = uMat (colX (n := a) k _) i j`. Rewrite using `[uMat_apply, Matrix.add_apply, posM, Matrix.sum_apply, Matrix.one_apply]`. Distinguish the cases in `hij : (i : ℕ) < k ∧ (j : ℕ) = k`.

Establish `hne : i ≠ j` using `fun h => by rw [h] at hij; omega`. Establish `hlt : i < j` using `by rw [Fin.lt_def]; omega`. Rewrite using `[Finset.sum_eq_single (⟨(i, j), hij.1, hij.2.ge, hij.2.le⟩ : UnipotentBlockColumnIndex a k k)]`. Rewrite using `[if_neg hne, if_neg hne, dif_pos hlt, colX_apply, dif_pos hij.2, Matrix.single_apply_same, zero_add]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Both sides reduce to the same expression. Apply `Fin.ext show (j : ℕ) = k` to reduce the goal to its premises. Conclude with `hij.2`.

Introduce `t _ ht`. Rewrite using `[Matrix.single_apply_of_ne]`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `ht (Subtype.ext (Prod.ext h1 h2))`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.sum_eq_zero]`. Rewrite using `[add_zero] split_ifs with h1 h2`. Both sides reduce to the same expression. Rewrite using `[colX_apply, dif_neg]`. Introduce `h3`.

Conclude with `hij ⟨by rw [← h3]; exact h2, h3⟩`. Both sides reduce to the same expression. Introduce `t _`. Rewrite using `[Matrix.single_apply_of_ne]`. Introduce and unpack `⟨h1, h2⟩`.

Apply `hij` to reduce the goal to its premises. Use `t.2` as an intermediate fact. Rewrite using `[← h1, ← h2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem blkU_eq_colGL {R : Type} [CommRing R] {a k : ℕ} (hk : k < a) (x : UnipotentBlockColumnIndex a k k → R) :
    (blkU x : GL (Fin a) R) = colGL (n := a) k (fun i => x ((colIx hk).symm i)) := by
  apply Units.ext
  ext i j
  change (1 + posM Subtype.val x : Matrix (Fin a) (Fin a) R) i j = uMat (colX (n := a) k _) i j
  rw [uMat_apply, Matrix.add_apply, posM, Matrix.sum_apply, Matrix.one_apply]
  by_cases hij : (i : ℕ) < k ∧ (j : ℕ) = k
  · have hne : i ≠ j := fun h => by rw [h] at hij; omega
    have hlt : i < j := by rw [Fin.lt_def]; omega
    rw [Finset.sum_eq_single (⟨(i, j), hij.1, hij.2.ge, hij.2.le⟩ : UnipotentBlockColumnIndex a k k)]
    · rw [if_neg hne, if_neg hne, dif_pos hlt, colX_apply, dif_pos hij.2, Matrix.single_apply_same, zero_add]
      congr 1
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · apply Fin.ext
        show (j : ℕ) = k
        exact hij.2
    · intro t _ ht
      rw [Matrix.single_apply_of_ne]
      rintro ⟨h1, h2⟩
      exact ht (Subtype.ext (Prod.ext h1 h2))
    · simp
  · rw [Finset.sum_eq_zero]
    · rw [add_zero]
      split_ifs with h1 h2
      · rfl
      · rw [colX_apply, dif_neg]
        intro h3
        exact hij ⟨by rw [← h3]; exact h2, h3⟩
      · rfl
    · intro t _
      rw [Matrix.single_apply_of_ne]
      rintro ⟨h1, h2⟩
      apply hij
      have := t.2
      rw [← h1, ← h2]
      omega

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Unfold `dot pair`. Use `Fintype.sum_equiv (colIx hk) _ _ fun t => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem dot_eLast {k : ℕ} (hk : k < a) (x : UnipotentBlockColumnIndex a k k → Ad E) :
    dot (eLast a k) x = pair (lastVec k) (fun i => x ((colIx hk).symm i)) := by
  unfold dot pair
  refine Fintype.sum_equiv (colIx hk) _ _ fun t => ?_
  dsimp only
  rw [Equiv.symm_apply_apply]
  rfl

/- English proof (translation)
Use `set ψ₀ : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)`. Establish `hψ : ∀ y, ψ₀ y = (GroundTheory.Global.adelicChar E y : ℂ)` using `fun y => rfl`. Use `set Φ : (UnipotentBlockColumnIndex a k k → Ad E) → ℂ := fun x => ψ₀ (-dot (eLast a k) x) * f (blkU x * g) with hΦdef`. Establish `hΦ : ∀ γ ∈ ratV E (UnipotentBlockColumnIndex a k k), ∀ x, Φ (γ + x) = Φ x`. Introduce and unpack `_ ⟨c, rfl⟩ x`.

Establish `e1 : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (UnipotentBlockColumnIndex a k k)) c = fun t => algebraMap E (Ad E) (c t)` using `rfl`. Rewrite using `[e1]`. Establish `hU : f (blkU ((fun t => algebraMap E (Ad E) (c t)) + x) * g) = f (blkU x * g)`. Express the relevant statement in the definitionally equal form `f (posU _ _ * g) = _`. Rewrite using `[posU_add, mul_assoc]`.

Express the relevant statement in the definitionally equal form `f (blkU _ * _) = _`. Rewrite using `[← ratGL_blkU, blkU_eq_colGL hk, hf]`. Both sides reduce to the same expression. Establish `hD : dot (eLast a k) ((fun t => algebraMap E (Ad E) (c t)) + x) = algebraMap E (Ad E) (∑ t, eLast a k t * c t) + dot (eLast a k) x`. Simplify using `only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_sum, map_mul]`.

Simplify using `only [Φ]`. Rewrite using `[hU, hD, neg_add, AddChar.map_add_eq_mul, hψ (-(algebraMap E (Ad E) _)), ← map_neg, GroundTheory.Global.adelicChar_algebraMap, Circle.coe_one, one_mul]`. Use `haveI : Countable (ratV E (UnipotentBlockColumnIndex a k k)) := countable_vecLattice`. Establish `hA : avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = ∫ x in vecDomain E (UnipotentBlockColumnIndex a k k), Φ x ∂vecMeasure E (UnipotentBlockColumnIndex a k k)` using `avg_eq_setIntegral (ratV E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecDomain E (UnipotentBlockColumnIndex a k k)) isAddFundamentalDomain_vecDomain vecMeasure_vecDomain Φ hΦ`. Express the relevant statement in the definitionally equal form `avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = _`.

Rewrite using `[hA]`. Set `Em` to `MeasurableEquiv.piCongrLeft (fun _ : Fin k => Ad E) (colIx hk)`. Establish `hE : MeasurePreserving Em (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (Fin k))` using `measurePreserving_piCongrLeft (fun _ : Fin k => GroundTheory.Global.adeleMeasure E) (colIx hk)`. Establish `hEx : ∀ x : UnipotentBlockColumnIndex a k k → Ad E, Em x = fun i => x ((colIx hk).symm i)`. Introduce `x`.

Use function extensionality and compare the values at `i`. Simplify using `[Em, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]`. Establish `hpre : Em ⁻¹' vecDomain E (Fin k) = vecDomain E (UnipotentBlockColumnIndex a k k)`. Use extensionality with `x`. Simplify using `only [Set.mem_preimage, hEx, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]`.

Prove the components needed by the constructor for the conclusion. Introduce `h t`. Use `h (colIx hk t)` as an intermediate fact. Rewrite `this` using `[Equiv.symm_apply_apply]`. Then use the resulting hypothesis. Introduce `h i`.

Conclude with `h _`. Rewrite using `[stepCoeff, vecCoeff, ← hE.setIntegral_preimage_emb Em.measurableEmbedding, hpre]`. Use `setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_` and prove the remaining obligations. Simplify using `only [Φ, hEx, hψ]`. Rewrite using `[blkU_eq_colGL hk, dot_eLast hk, mul_comm]`.
-/
theorem colT_eq_stepCoeff {k : ℕ} (hk : k < a) (f : GA E a → ℂ)
    (hf : ∀ (ξ : Fin k → E) g, f (ratGL E a (colGL k ξ) * g) = f g) (g : GA E a) :
    colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) k f g = stepCoeff k f g := by
  set ψ₀ : AddChar (Ad E) ℂ := Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)
  have hψ : ∀ y, ψ₀ y = (GroundTheory.Global.adelicChar E y : ℂ) := fun y => rfl
  set Φ : (UnipotentBlockColumnIndex a k k → Ad E) → ℂ := fun x => ψ₀ (-dot (eLast a k) x) * f (blkU x * g) with hΦdef
  have hΦ : ∀ γ ∈ ratV E (UnipotentBlockColumnIndex a k k), ∀ x, Φ (γ + x) = Φ x := by
    rintro _ ⟨c, rfl⟩ x
    have e1 : (AddMonoidHom.compLeft (algebraMap E (Ad E)).toAddMonoidHom (UnipotentBlockColumnIndex a k k)) c =
        fun t => algebraMap E (Ad E) (c t) := rfl
    rw [e1]
    have hU : f (blkU ((fun t => algebraMap E (Ad E) (c t)) + x) * g) = f (blkU x * g) := by
      change f (posU _ _ * g) = _
      rw [posU_add, mul_assoc]
      change f (blkU _ * _) = _
      rw [← ratGL_blkU, blkU_eq_colGL hk, hf]
      rfl
    have hD : dot (eLast a k) ((fun t => algebraMap E (Ad E) (c t)) + x) =
        algebraMap E (Ad E) (∑ t, eLast a k t * c t) + dot (eLast a k) x := by
      simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, map_sum, map_mul]
    simp only [Φ]
    rw [hU, hD, neg_add, AddChar.map_add_eq_mul, hψ (-(algebraMap E (Ad E) _)), ← map_neg,
      GroundTheory.Global.adelicChar_algebraMap, Circle.coe_one, one_mul]
  haveI : Countable (ratV E (UnipotentBlockColumnIndex a k k)) := countable_vecLattice
  have hA : avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = ∫ x in vecDomain E (UnipotentBlockColumnIndex a k k), Φ x ∂vecMeasure E (UnipotentBlockColumnIndex a k k) :=
    avg_eq_setIntegral (ratV E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecDomain E (UnipotentBlockColumnIndex a k k))
      isAddFundamentalDomain_vecDomain vecMeasure_vecDomain Φ hΦ
  change avg (ratV E (UnipotentBlockColumnIndex a k k)) Φ = _
  rw [hA]
  let Em := MeasurableEquiv.piCongrLeft (fun _ : Fin k => Ad E) (colIx hk)
  have hE : MeasurePreserving Em (vecMeasure E (UnipotentBlockColumnIndex a k k)) (vecMeasure E (Fin k)) :=
    measurePreserving_piCongrLeft (fun _ : Fin k => GroundTheory.Global.adeleMeasure E) (colIx hk)
  have hEx : ∀ x : UnipotentBlockColumnIndex a k k → Ad E, Em x = fun i => x ((colIx hk).symm i) := by
    intro x
    funext i
    simp [Em, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have hpre : Em ⁻¹' vecDomain E (Fin k) = vecDomain E (UnipotentBlockColumnIndex a k k) := by
    ext x
    simp only [Set.mem_preimage, hEx, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h t
      have := h (colIx hk t)
      rwa [Equiv.symm_apply_apply] at this
    · intro h i
      exact h _
  rw [stepCoeff, vecCoeff, ← hE.setIntegral_preimage_emb Em.measurableEmbedding, hpre]
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [Φ, hEx, hψ]
  rw [blkU_eq_colGL hk, dot_eLast hk, mul_comm]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro _`. Both sides reduce to the same expression. Consider the case `succ m ih`.

Introduce `hm`. Establish `hk : m + 1 < a` using `by omega`. Rewrite using `[whit_succ]`. Establish `hcol : colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (m + 1) (partialCoeff F (m + 1 + 1)) = partialCoeff F (m + 1)`. Use function extensionality and compare the values at `g`.

Rewrite using `[colT_eq_stepCoeff hk _ (fun ξ g => partialCoeff_succ_diagonal_colGL (K := E) (n := a) hl hk ξ g), partialCoeff_of_lt F hk]`. Rewrite using `[hcol]`. Conclude with `ih (by omega)`.
-/
theorem whit_partialCoeff (F : GA E a → ℂ) (hl : ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) :
    ∀ m, m + 1 ≤ a → whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) m (partialCoeff F (m + 1)) =
      partialCoeff F 1 := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hk : m + 1 < a := by omega
    rw [whit_succ]
    have hcol : colT (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (m + 1) (partialCoeff F (m + 1 + 1)) =
        partialCoeff F (m + 1) := by
      funext g
      rw [colT_eq_stepCoeff hk _ (fun ξ g => partialCoeff_succ_diagonal_colGL (K := E) (n := a) hl hk ξ g),
        partialCoeff_of_lt F hk]
    rw [hcol]
    exact ih (by omega)

/- English proof (translation)
Introduce `E _ _ a F ha hc hl`. Establish `h` using `whit_partialCoeff F hl (a - 1) (by omega)`. Rewrite `h` using `[Nat.sub_add_cancel ha, partialCoeff_self]`. Rewrite using `[h]`. Use function extensionality and compare the values at `g`.

Conclude with `(whittaker_eq_partialCoeff hc ha g).symm`.
-/
theorem whit_eq_whittaker : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (F : GA E a → ℂ), 0 < a → Continuous F →
    (∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) →
    GlobalTheory.CuspGeneric.whit (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) (a - 1) F = GlobalTheory.JSW.whit F := by
  intro E _ _ a F ha hc hl
  have h := whit_partialCoeff F hl (a - 1) (by omega)
  rw [Nat.sub_add_cancel ha, partialCoeff_self] at h
  rw [h]
  funext g
  exact (whittaker_eq_partialCoeff hc ha g).symm

end GlobalTheory.CuspGeneric.WhitEq
