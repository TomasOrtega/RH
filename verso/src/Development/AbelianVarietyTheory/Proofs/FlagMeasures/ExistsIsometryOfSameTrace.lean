import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualInterSelfDualHermitianLatticeSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AlgebraMapMemO
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SameTrace

open GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

/- English proof (translation)
Simplify using `[hf]`.
-/
theorem hf_zero_l (y : Fin n → E) : hf L Hm 0 y = 0 := by simp [hf]

/- English proof (translation)
Simplify using `[hf]`.
-/
theorem hf_zero_r (y : Fin n → E) : hf L Hm y 0 = 0 := by simp [hf]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hf_zero_l]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]`.
-/
theorem hf_sum_l {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, a i) y = ∑ i ∈ s, hf L Hm (a i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_l]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_l, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [hf_zero_r]`. Consider the case `insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, ih]`.
-/
theorem hf_sum_r {ι : Type} (s : Finset ι) (a : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ i ∈ s, a i) = ∑ i ∈ s, hf L Hm y (a i) := by
  induction s using Finset.induction_on with
  | empty => simp [hf_zero_r]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf_add_r, ih]

/- English proof (translation)
Establish `: Module.Finite F E` using `Module.finite_of_finrank_pos (by rw [L.rank]; omega)`. Establish `h1 : IsAlgebraic F c` using `Algebra.IsAlgebraic.isAlgebraic c`. Establish `h2 : IsAlgebraic 𝒪[F] c` using `(IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1`. Take `⟨t, ht, h⟩` from `h2.exists_integral_multiple`. Use `⟨t, ht, (L.O_def _).2 ?_⟩` and prove the remaining obligations.

Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Algebra.smul_def]`. Both sides reduce to the same expression.
-/
theorem exists_mul_mem [IsNonarchimedeanLocalField F] (c : E) :
    ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E t * c ∈ L.O := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have h1 : IsAlgebraic F c := Algebra.IsAlgebraic.isAlgebraic c
  have h2 : IsAlgebraic 𝒪[F] c := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 h1
  obtain ⟨t, ht, h⟩ := h2.exists_integral_multiple
  refine ⟨t, ht, (L.O_def _).2 ?_⟩
  convert h using 1
  rw [Algebra.smul_def]; rfl

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CommonDenominator.main`. Consider the case `exact _root_.GlobalTheory.CommonDenominator.main`. Consider the case `(apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CommonDenominator.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CommonDenominator.main ..)`.
-/
theorem exists_smul_mem [IsNonarchimedeanLocalField F] {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsLat L Λ) (x : Fin n → E) : ∃ t : 𝒪[F], t ≠ 0 ∧ algebraMap F E t • x ∈ Λ := by
  first
  | exact @_root_.GlobalTheory.CommonDenominator.main
  | exact _root_.GlobalTheory.CommonDenominator.main
  | (apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonDenominator.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonDenominator.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonDenominator.main ..)

noncomputable def shear {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0) :
    (Fin n → E) ≃ₗ[E] (Fin n → E) where
  toFun v := v + ∑ j, hf L Hm v (b j) • d j
  map_add' v w := by simp only [hf_add_l, add_smul, Finset.sum_add_distrib]; abel
  map_smul' c v := by
    simp only [hf_smul_l, RingHom.id_apply, smul_add, Finset.smul_sum, mul_smul]
  invFun v := v - ∑ j, hf L Hm v (b j) • d j
  left_inv v := by simp [hf_add_l, hf_sum_l, hf_smul_l, hdb]
  right_inv v := by simp [hf_sub_l, hf_sum_l, hf_smul_l, hdb]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shear_apply {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (v : Fin n → E) : shear L Hm b d hdb v = v + ∑ j, hf L Hm v (b j) • d j := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem shear_symm_apply {m : ℕ} (b d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (v : Fin n → E) : (shear L Hm b d hdb).symm v = v - ∑ j, hf L Hm v (b j) • d j := rfl

/- English proof (translation)
Introduce `v w`. Establish `hw : ∀ k, hf L Hm (d k) w = ∑ j, L.cj (hf L Hm w (b j)) * hf L Hm (d k) (c j)`. Introduce `k`. Rewrite using `[← hf_cj L h, hv, map_sum]`. Simplify using `only [map_mul, hf_cj L h]`.

Simplify using `only [shear_apply, hf_add_l, hf_add_r, hf_sum_l, hf_sum_r, hf_smul_l, hf_smul_r, hdd, mul_zero, Finset.sum_const_zero, add_zero]`. Simplify using `only [hw]`. Simplify using `only [hv v, Finset.mul_sum]`. Establish `key : ∑ k, ∑ j, L.cj (hf L Hm w (b k)) * (hf L Hm v (b j) * hf L Hm (c j) (d k)) + ∑ j, ∑ k, hf L Hm v (b j) * (L.cj (hf L Hm w (b k)) * hf L Hm (d j) (c k)) = 0`. Rewrite using `[Finset.sum_comm, ← Finset.sum_add_distrib]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Take the linear combination `L.cj (hf L Hm w (b k)) * hf L Hm v (b j) * hcd j k`. Take the linear combination `key`.
-/
theorem shear_mem_isomG {Hm : Matrix (Fin n) (Fin n) E} (h : IsHerm L Hm) {m : ℕ}
    (b c d : Fin m → Fin n → E) (hdb : ∀ i j, hf L Hm (d i) (b j) = 0)
    (hdd : ∀ i j, hf L Hm (d i) (d j) = 0)
    (hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k))
    (hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0) :
    shear L Hm b d hdb ∈ isomG L Hm := by
  intro v w
  have hw : ∀ k, hf L Hm (d k) w = ∑ j, L.cj (hf L Hm w (b j)) * hf L Hm (d k) (c j) := by
    intro k
    rw [← hf_cj L h, hv, map_sum]
    simp only [map_mul, hf_cj L h]
  simp only [shear_apply, hf_add_l, hf_add_r, hf_sum_l, hf_sum_r, hf_smul_l, hf_smul_r, hdd,
    mul_zero, Finset.sum_const_zero, add_zero]
  simp only [hw]
  simp only [hv v, Finset.mul_sum]
  have key : ∑ k, ∑ j, L.cj (hf L Hm w (b k)) * (hf L Hm v (b j) * hf L Hm (c j) (d k))
      + ∑ j, ∑ k, hf L Hm v (b j) * (L.cj (hf L Hm w (b k)) * hf L Hm (d j) (c k)) = 0 := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    linear_combination L.cj (hf L Hm w (b k)) * hf L Hm v (b j) * hcd j k
  linear_combination key

end

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L n Hm hH La Lb hLa hLb m e he hee hab`. Take `⟨-, hA, -, b, c, hb, hc, hbc⟩` from `GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace L Hm hH La hLa m e he`. Take `⟨-, hB, -, -⟩` from `GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace L Hm hH Lb hLb m e he`. Use `set X := Submodule.span E (Set.range e) with hX`. Establish `hcj` using `hf_cj L hH.1`.

Establish `hXp : ∀ x ∈ X, x ∈ perp L Hm X`. Establish `h1 : ∀ i, e i ∈ perp L Hm X`. Introduce `i y hy`. Take `⟨a, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hy`. Simplify using `[hf_sum_r, hf_smul_r, hee]`.

Conclude with `Submodule.span_le.2 (Set.range_subset_iff.2 h1)`. Establish `hbm : ∀ j, b j ∈ La ∧ b j ∈ X` using `fun j => by`. Establish `: b j ∈ La ⊓ X.restrictScalars L.O`. Rewrite using `[hb]`. Conclude with `Submodule.subset_span ⟨j, rfl⟩`.

Conclude with `this`. Establish `hbLb : ∀ j, b j ∈ Lb` using `fun j => (hab _ (hXp _ (hbm j).2)).1 (hbm j).1`. Establish `hcb : ∀ i j, hf L Hm (c i) (b j) = if i = j then 1 else 0` using `fun i j => by`. Rewrite using `[← hcj, hbc]`. Distinguish the cases in `hij : i = j`.

Simplify using `[hij]`. Simplify using `[hij, Ne.symm hij]`. Establish `hperp : ∀ v, (∀ j, hf L Hm v (b j) = 0) → v ∈ perp L Hm X`. Introduce `v hv x hx`. Take `⟨t, ht, htx⟩` from `exists_smul_mem L hLa.1 x`.

Establish `h1 : algebraMap F E t • x ∈ Submodule.span L.O (Set.range b)`. Rewrite using `[← hb]`. Conclude with `⟨htx, X.smul_mem _ hx⟩`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun L.O).1 h1`. Establish `h2 : hf L Hm v (algebraMap F E t • x) = 0`.

Rewrite using `[← ha]`. Simplify using `[hf_sum_r, Subring.smul_def, hf_smul_r, hv]`. Rewrite `h2` using `[hf_smul_r, AlgEquiv.commutes]`. Establish `ht' : (t : F) ≠ 0` using `fun h => ht (Subtype.ext h)`. Conclude with `((IsUnit.mk0 _ ht').map (algebraMap F E)).mul_right_eq_zero.1 h2`.

Establish `hint : ∀ {Λ}, IsSD L Hm Λ → ∀ x ∈ Λ, ∀ y ∈ Λ, hf L Hm x y ∈ L.O` using `fun hΛ x hx y hy => (hΛ.2 y).2 hy x hx`. Establish `hc' : ∀ j, ∃ a ∈ Lb, c j - a ∈ X` using `fun j => (hB (c j)).1 fun x hx hxp => hint hLa x ((hab x hxp).2 hx) _ (hc j)`. Use `choose c' hc'b hc'X using hc'`. Take `⟨ω, hω, ε, hε, hωε⟩` from `exists_sub_cj_mul_eq_one L`. Establish `hε' : (L.cj ω - ω) * L.cj ε = 1` using `by simpa [L.cj_cj] using congrArg L.cj hωε`.

Establish `hcε : L.cj ε = -ε` using `by linear_combination (-ε) * hε' - (L.cj ε) * hωε`. Take `⟨τ, hτO, hτ⟩ : ∃ τ ∈ L.O, τ + L.cj τ = 1` from `⟨ω * ε, L.O.mul_mem hω hε, by rw [map_mul, hcε]; linear_combination hωε⟩`. Set `d₀ : Fin m → Fin n → E` to `fun j => c' j - c j`. Establish `hd₀ : ∀ j, d₀ j ∈ X` using `fun j => by`. Use `X.neg_mem (hc'X j)` as an intermediate fact.

Rewrite `this` using `[neg_sub]`. Then use the resulting hypothesis. Set `H : Fin m → Fin m → E` to `fun j k => hf L Hm (c j) (d₀ k) + hf L Hm (d₀ j) (c k)`. Establish `hHO : ∀ j k, H j k ∈ L.O` using `fun j k => by`. Establish `h0 : hf L Hm (d₀ j) (d₀ k) = 0` using `hXp _ (hd₀ j) _ (hd₀ k)`. Establish `h1 : H j k = hf L Hm (c' j) (c' k) - hf L Hm (c j) (c k)`.

Simplify using `only [H, d₀, hf_sub_l, hf_sub_r] at h0 ⊢`. Take the linear combination `-h0`. Rewrite using `[h1]`. Conclude with `L.O.sub_mem (hint hLb _ (hc'b j) _ (hc'b k)) (hint hLa _ (hc j) _ (hc k))`. Establish `hHc : ∀ j k, L.cj (H k j) = H j k` using `fun j k => by`.

Simplify using `only [H, map_add, hcj]`. Expand and normalize the polynomial expressions, which then agree. Set `d : Fin m → Fin n → E` to `fun j => d₀ j - ∑ l, (τ * H j l) • b l`. Establish `hd : ∀ j, d j ∈ X` using `fun j => X.sub_mem (hd₀ j) (X.sum_mem fun l _ => X.smul_mem _ (hbm l).2)`. Establish `hcdb : ∀ j, c j + d j ∈ Lb` using `fun j => by`.

Establish `h1 : c j + d j = c' j - ∑ l, (τ * H j l) • b l`. Simplify using `only [d, d₀]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1]`. Conclude with `Lb.sub_mem (hc'b j) (Lb.sum_mem fun l _ => Lb.smul_mem ⟨_, L.O.mul_mem hτO (hHO j l)⟩ (hbLb l))`.

Establish `hdb : ∀ i j, hf L Hm (d i) (b j) = 0` using `fun i j => hXp _ (hd i) _ (hbm j).2`. Establish `hdd : ∀ i j, hf L Hm (d i) (d j) = 0` using `fun i j => hXp _ (hd i) _ (hd j)`. Establish `hv0 : ∀ v, v - ∑ j, hf L Hm v (b j) • c j ∈ perp L Hm X` using `fun v => hperp _ fun k => by simp [hf_sub_l, hf_sum_l, hf_smul_l, hcb]`. Establish `hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k)` using `fun v k => by`. Establish `h1` using `hv0 v _ (hd k)`.

Simplify using `only [hf_sub_l, hf_sum_l, hf_smul_l] at h1`. Conclude with `sub_eq_zero.1 h1`. Establish `hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0` using `fun j k => by`. Establish `h1 : hf L Hm (c j) (d k) = hf L Hm (c j) (d₀ k) - L.cj τ * H j k`. Simplify using `[d, hf_sub_r, hf_sum_r, hf_smul_r, hcb, hHc]`.

Establish `h2 : hf L Hm (d j) (c k) = hf L Hm (d₀ j) (c k) - τ * H j k`. Simplify using `[d, hf_sub_l, hf_sum_l, hf_smul_l, hbc]`. Establish `h3 : H j k = hf L Hm (c j) (d₀ k) + hf L Hm (d₀ j) (c k)` using `rfl`. Rewrite using `[h1, h2]`. Take the linear combination `-h3 - H j k * hτ`.

Use `⟨shear L Hm b d hdb, shear_mem_isomG L hH.1 b c d hdb hdd hv hcd, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ j, hf L Hm x (b j) = 0` using `fun j => hx _ (hbm j).2`. Simplify using `[shear_apply, h1]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨v, hva, rfl⟩ show shear L Hm b d hdb v ∈ Lb`.

Establish `hβ : ∀ j, hf L Hm v (b j) ∈ L.O` using `fun j => hint hLa _ hva _ (hbm j).1`. Establish `h1 : shear L Hm b d hdb v = (v - ∑ j, hf L Hm v (b j) • c j) + ∑ j, hf L Hm v (b j) • (c j + d j)`. Simplify using `only [shear_apply, smul_add, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1]`.

Use `Lb.add_mem ((hab _ (hv0 v)).1 (La.sub_mem hva (La.sum_mem fun j _ => La.smul_mem ⟨_, hβ j⟩ (hc j)))) (Lb.sum_mem fun j _ => Lb.smul_mem ⟨_, hβ j⟩ (hcdb j))` and prove the remaining obligations. Introduce `w hw`. Use `⟨(shear L Hm b d hdb).symm w, ?_, (shear L Hm b d hdb).apply_symm_apply w⟩` and prove the remaining obligations. Establish `hβ : ∀ j, hf L Hm w (b j) ∈ L.O` using `fun j => hint hLb _ hw _ (hbLb j)`. Establish `h1 : (shear L Hm b d hdb).symm w = (w - ∑ j, hf L Hm w (b j) • (c j + d j)) + ∑ j, hf L Hm w (b j) • c j`.

Simplify using `only [shear_symm_apply, smul_add, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws. Establish `h2 : w - ∑ j, hf L Hm w (b j) • (c j + d j) ∈ perp L Hm X` using `hperp _ fun k => by simp [hf_sub_l, hf_sum_l, hf_smul_l, hf_add_l, hcb, hdb]`. Use `show (shear L Hm b d hdb).symm w ∈ La`. Rewrite using `[h1]`.

Use `La.add_mem ((hab _ h2).2 (Lb.sub_mem hw (Lb.sum_mem fun j _ => Lb.smul_mem ⟨_, hβ j⟩ (hcdb j)))) (La.sum_mem fun j _ => La.smul_mem ⟨_, hβ j⟩ (hc j))` and prove the remaining obligations.
-/
theorem exists_isometry_of_same_trace : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ La Lb, IsSD L Hm La → IsSD L Hm Lb → ∀ (m : ℕ) (e : Fin m → Fin n → E), LinearIndependent E e → (∀ i j, hf L Hm (e i) (e j) = 0) → (∀ x ∈ perp L Hm (Submodule.span E (Set.range e)), x ∈ La ↔ x ∈ Lb) → ∃ g ∈ isomG L Hm, (∀ x ∈ perp L Hm (Submodule.span E (Set.range e)), g x = x) ∧ g • La = Lb := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH La Lb hLa hLb m e he hee hab
  obtain ⟨-, hA, -, b, c, hb, hc, hbc⟩ := GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace L Hm hH La hLa m e he
  obtain ⟨-, hB, -, -⟩ := GlobalTheory.T.dual_inter_selfDualHermitianLattice_subspace L Hm hH Lb hLb m e he
  set X := Submodule.span E (Set.range e) with hX
  have hcj := hf_cj L hH.1

  have hXp : ∀ x ∈ X, x ∈ perp L Hm X := by
    have h1 : ∀ i, e i ∈ perp L Hm X := by
      intro i y hy
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
      simp [hf_sum_r, hf_smul_r, hee]
    exact Submodule.span_le.2 (Set.range_subset_iff.2 h1)
  have hbm : ∀ j, b j ∈ La ∧ b j ∈ X := fun j => by
    have : b j ∈ La ⊓ X.restrictScalars L.O := by
      rw [hb]; exact Submodule.subset_span ⟨j, rfl⟩
    exact this
  have hbLb : ∀ j, b j ∈ Lb := fun j => (hab _ (hXp _ (hbm j).2)).1 (hbm j).1
  have hcb : ∀ i j, hf L Hm (c i) (b j) = if i = j then 1 else 0 := fun i j => by
    rw [← hcj, hbc]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

  have hperp : ∀ v, (∀ j, hf L Hm v (b j) = 0) → v ∈ perp L Hm X := by
    intro v hv x hx
    obtain ⟨t, ht, htx⟩ := exists_smul_mem L hLa.1 x
    have h1 : algebraMap F E t • x ∈ Submodule.span L.O (Set.range b) := by
      rw [← hb]; exact ⟨htx, X.smul_mem _ hx⟩
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 h1
    have h2 : hf L Hm v (algebraMap F E t • x) = 0 := by
      rw [← ha]
      simp [hf_sum_r, Subring.smul_def, hf_smul_r, hv]
    rw [hf_smul_r, AlgEquiv.commutes] at h2
    have ht' : (t : F) ≠ 0 := fun h => ht (Subtype.ext h)
    exact ((IsUnit.mk0 _ ht').map (algebraMap F E)).mul_right_eq_zero.1 h2
  have hint : ∀ {Λ}, IsSD L Hm Λ → ∀ x ∈ Λ, ∀ y ∈ Λ, hf L Hm x y ∈ L.O :=
    fun hΛ x hx y hy => (hΛ.2 y).2 hy x hx

  have hc' : ∀ j, ∃ a ∈ Lb, c j - a ∈ X := fun j =>
    (hB (c j)).1 fun x hx hxp => hint hLa x ((hab x hxp).2 hx) _ (hc j)
  choose c' hc'b hc'X using hc'
  obtain ⟨ω, hω, ε, hε, hωε⟩ := exists_sub_cj_mul_eq_one L
  have hε' : (L.cj ω - ω) * L.cj ε = 1 := by simpa [L.cj_cj] using congrArg L.cj hωε
  have hcε : L.cj ε = -ε := by linear_combination (-ε) * hε' - (L.cj ε) * hωε
  obtain ⟨τ, hτO, hτ⟩ : ∃ τ ∈ L.O, τ + L.cj τ = 1 :=
    ⟨ω * ε, L.O.mul_mem hω hε, by rw [map_mul, hcε]; linear_combination hωε⟩
  let d₀ : Fin m → Fin n → E := fun j => c' j - c j
  have hd₀ : ∀ j, d₀ j ∈ X := fun j => by
    have := X.neg_mem (hc'X j)
    rwa [neg_sub] at this
  let H : Fin m → Fin m → E := fun j k => hf L Hm (c j) (d₀ k) + hf L Hm (d₀ j) (c k)
  have hHO : ∀ j k, H j k ∈ L.O := fun j k => by
    have h0 : hf L Hm (d₀ j) (d₀ k) = 0 := hXp _ (hd₀ j) _ (hd₀ k)
    have h1 : H j k = hf L Hm (c' j) (c' k) - hf L Hm (c j) (c k) := by
      simp only [H, d₀, hf_sub_l, hf_sub_r] at h0 ⊢
      linear_combination -h0
    rw [h1]
    exact L.O.sub_mem (hint hLb _ (hc'b j) _ (hc'b k)) (hint hLa _ (hc j) _ (hc k))
  have hHc : ∀ j k, L.cj (H k j) = H j k := fun j k => by
    simp only [H, map_add, hcj]; ring
  let d : Fin m → Fin n → E := fun j => d₀ j - ∑ l, (τ * H j l) • b l
  have hd : ∀ j, d j ∈ X := fun j =>
    X.sub_mem (hd₀ j) (X.sum_mem fun l _ => X.smul_mem _ (hbm l).2)
  have hcdb : ∀ j, c j + d j ∈ Lb := fun j => by
    have h1 : c j + d j = c' j - ∑ l, (τ * H j l) • b l := by
      simp only [d, d₀]; abel
    rw [h1]
    exact Lb.sub_mem (hc'b j) (Lb.sum_mem fun l _ =>
      Lb.smul_mem ⟨_, L.O.mul_mem hτO (hHO j l)⟩ (hbLb l))
  have hdb : ∀ i j, hf L Hm (d i) (b j) = 0 := fun i j => hXp _ (hd i) _ (hbm j).2
  have hdd : ∀ i j, hf L Hm (d i) (d j) = 0 := fun i j => hXp _ (hd i) _ (hd j)
  have hv0 : ∀ v, v - ∑ j, hf L Hm v (b j) • c j ∈ perp L Hm X := fun v =>
    hperp _ fun k => by simp [hf_sub_l, hf_sum_l, hf_smul_l, hcb]
  have hv : ∀ v k, hf L Hm v (d k) = ∑ j, hf L Hm v (b j) * hf L Hm (c j) (d k) := fun v k => by
    have h1 := hv0 v _ (hd k)
    simp only [hf_sub_l, hf_sum_l, hf_smul_l] at h1
    exact sub_eq_zero.1 h1
  have hcd : ∀ j k, hf L Hm (c j) (d k) + hf L Hm (d j) (c k) = 0 := fun j k => by
    have h1 : hf L Hm (c j) (d k) = hf L Hm (c j) (d₀ k) - L.cj τ * H j k := by
      simp [d, hf_sub_r, hf_sum_r, hf_smul_r, hcb, hHc]
    have h2 : hf L Hm (d j) (c k) = hf L Hm (d₀ j) (c k) - τ * H j k := by
      simp [d, hf_sub_l, hf_sum_l, hf_smul_l, hbc]
    have h3 : H j k = hf L Hm (c j) (d₀ k) + hf L Hm (d₀ j) (c k) := rfl
    rw [h1, h2]
    linear_combination -h3 - H j k * hτ
  refine ⟨shear L Hm b d hdb, shear_mem_isomG L hH.1 b c d hdb hdd hv hcd, fun x hx => ?_, ?_⟩
  · have h1 : ∀ j, hf L Hm x (b j) = 0 := fun j => hx _ (hbm j).2
    simp [shear_apply, h1]
  · apply le_antisymm
    · rintro _ ⟨v, hva, rfl⟩
      show shear L Hm b d hdb v ∈ Lb
      have hβ : ∀ j, hf L Hm v (b j) ∈ L.O := fun j => hint hLa _ hva _ (hbm j).1
      have h1 : shear L Hm b d hdb v = (v - ∑ j, hf L Hm v (b j) • c j)
          + ∑ j, hf L Hm v (b j) • (c j + d j) := by
        simp only [shear_apply, smul_add, Finset.sum_add_distrib]; abel
      rw [h1]
      refine Lb.add_mem ((hab _ (hv0 v)).1 (La.sub_mem hva (La.sum_mem fun j _ =>
        La.smul_mem ⟨_, hβ j⟩ (hc j)))) (Lb.sum_mem fun j _ => Lb.smul_mem ⟨_, hβ j⟩ (hcdb j))
    · intro w hw
      refine ⟨(shear L Hm b d hdb).symm w, ?_, (shear L Hm b d hdb).apply_symm_apply w⟩
      have hβ : ∀ j, hf L Hm w (b j) ∈ L.O := fun j => hint hLb _ hw _ (hbLb j)
      have h1 : (shear L Hm b d hdb).symm w = (w - ∑ j, hf L Hm w (b j) • (c j + d j))
          + ∑ j, hf L Hm w (b j) • c j := by
        simp only [shear_symm_apply, smul_add, Finset.sum_add_distrib]; abel
      have h2 : w - ∑ j, hf L Hm w (b j) • (c j + d j) ∈ perp L Hm X :=
        hperp _ fun k => by simp [hf_sub_l, hf_sum_l, hf_smul_l, hf_add_l, hcb, hdb]
      show (shear L Hm b d hdb).symm w ∈ La
      rw [h1]
      refine La.add_mem ((hab _ h2).2 (Lb.sub_mem hw (Lb.sum_mem fun j _ =>
        Lb.smul_mem ⟨_, hβ j⟩ (hcdb j)))) (La.sum_mem fun j _ => La.smul_mem ⟨_, hβ j⟩ (hc j))

end GlobalTheory.HL.SameTrace
