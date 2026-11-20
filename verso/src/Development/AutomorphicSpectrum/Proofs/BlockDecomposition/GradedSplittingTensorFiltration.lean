import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrTens

variable {O A Γ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing Γ] [Algebra O Γ]
  {I : Ideal A} {γ : DividedPowers I} {m : ℕ} (S : GrSplit O γ m)

/- English proof (translation)
The claim follows from `Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩`.
-/
theorem dividedPowerFiltration_le {r r' : ℕ} (h : r ≤ r') : pdP γ r' ≤ pdP γ r :=
  Ideal.span_mono fun _ ⟨l, hl, hr, hz⟩ => ⟨l, hl, h.trans hr, hz⟩

/- English proof (translation)
The claim follows from `(Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], by simp, by simp, by simp⟩)`.
-/
theorem dividedPowerFiltration_zero_eq (γ : DividedPowers I) : pdP γ 0 = ⊤ :=
  (Ideal.eq_top_iff_one _).2 (Ideal.subset_span ⟨[], by simp, by simp, by simp⟩)

def sumMap : (∀ i, S.N i) →ₗ[O] A := ∑ i, (S.ν i).comp (LinearMap.proj i)

/- English proof (translation)
Simplify using `[sumMap, LinearMap.sum_apply]`.
-/
theorem sumMap_apply (n : ∀ i, S.N i) : sumMap S n = ∑ i, S.ν i (n i) := by
  simp [sumMap, LinearMap.sum_apply]

/- English proof (translation)
Rewrite using `[sumMap_apply, Finset.sum_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules.
-/
theorem sumMap_single (i : Fin m) (x : S.N i) : sumMap S (Pi.single i x) = S.ν i x := by
  rw [sumMap_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/- English proof (translation)
Rewrite using `[sumMap_apply]`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : (i : ℕ) < r`. Rewrite using `[h i hi, map_zero]`. Conclude with `zero_mem _`.

Conclude with `dividedPowerFiltration_le (not_lt.1 hi) (S.mem i _)`.
-/
theorem sumMap_mem (n : ∀ i, S.N i) (r : ℕ) (h : ∀ i : Fin m, (i : ℕ) < r → n i = 0) :
    sumMap S n ∈ pdP γ r := by
  rw [sumMap_apply]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_cases hi : (i : ℕ) < r
  · rw [h i hi, map_zero]
    exact zero_mem _
  · exact dividedPowerFiltration_le (not_lt.1 hi) (S.mem i _)

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => intro _ i hi`. Use linear arithmetic over natural numbers and integers. Consider the case `succ r ih`. Introduce `h i hi`.

Establish `h0` using `ih (dividedPowerFiltration_le (Nat.le_succ r) h)`. Distinguish the cases in `hlt : (i : ℕ) < r`. Conclude with `h0 i hlt`. Establish `hir : (i : ℕ) = r` using `by omega`. Substitute `hir` using the available equality.

Apply `S.inj i` to reduce the goal to its premises. Establish `hs : sumMap S (Function.update n i 0) ∈ pdP γ ((i : ℕ) + 1)`. Use `sumMap_mem S _ _ fun j hj => ?_` and prove the remaining obligations. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Function.update_of_ne hji]`. Use `h0 j ?_` and prove the remaining obligations. Establish `: (j : ℕ) ≠ i` using `fun e => hji (Fin.ext e)`. Use linear arithmetic over natural numbers and integers.

Establish `hn : n = Function.update n i 0 + Pi.single i (n i)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Function.update_of_ne hji, Pi.single_eq_of_ne hji]`. Establish `e : sumMap S n = sumMap S (Function.update n i 0) + S.ν i (n i)`. Rewrite using `[← sumMap_single, ← map_add, ← hn]`. Rewrite using `[eq_sub_of_add_eq' e.symm]`. Conclude with `sub_mem h hs`.
-/
theorem eq_zero_of_mem (n : ∀ i, S.N i) (r : ℕ) :
    sumMap S n ∈ pdP γ r → ∀ i : Fin m, (i : ℕ) < r → n i = 0 := by
  induction r with
  | zero => intro _ i hi; omega
  | succ r ih =>
    intro h i hi
    have h0 := ih (dividedPowerFiltration_le (Nat.le_succ r) h)
    by_cases hlt : (i : ℕ) < r
    · exact h0 i hlt
    · have hir : (i : ℕ) = r := by omega
      subst hir
      apply S.inj i
      have hs : sumMap S (Function.update n i 0) ∈ pdP γ ((i : ℕ) + 1) := by
        refine sumMap_mem S _ _ fun j hj => ?_
        by_cases hji : j = i
        · subst hji
          simp
        · rw [Function.update_of_ne hji]
          refine h0 j ?_
          have : (j : ℕ) ≠ i := fun e => hji (Fin.ext e)
          omega
      have hn : n = Function.update n i 0 + Pi.single i (n i) := by
        funext j
        by_cases hji : j = i
        · subst hji
          simp
        · simp [Function.update_of_ne hji, Pi.single_eq_of_ne hji]
      have e : sumMap S n = sumMap S (Function.update n i 0) + S.ν i (n i) := by
        rw [← sumMap_single, ← map_add, ← hn]
      rw [eq_sub_of_add_eq' e.symm]
      exact sub_mem h hs

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `r hr x hx`. Take `rfl : r = m` from `by omega`. Rewrite `hx` using `[S.nil]`.

Conclude with `⟨0, by rw [map_zero]; exact ((Ideal.mem_bot).1 hx).symm⟩`. Consider the case `succ k ih`. Introduce `r hr x hx`. Establish `hlt : r < m` using `by omega`. Take `⟨n₀, hn⟩` from `S.surj ⟨r, hlt⟩ x hx`.

Take `⟨n, hn'⟩` from `ih (r + 1) (by omega) _ hn`. Use `⟨n + Pi.single ⟨r, hlt⟩ n₀, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, sumMap_single, hn']`. Conclude with `sub_add_cancel _ _`.
-/
theorem exists_sumMap (k : ℕ) : ∀ r, r + k = m → ∀ x ∈ pdP γ r, ∃ n, sumMap S n = x := by
  induction k with
  | zero =>
    intro r hr x hx
    obtain rfl : r = m := by omega
    rw [S.nil] at hx
    exact ⟨0, by rw [map_zero]; exact ((Ideal.mem_bot).1 hx).symm⟩
  | succ k ih =>
    intro r hr x hx
    have hlt : r < m := by omega
    obtain ⟨n₀, hn⟩ := S.surj ⟨r, hlt⟩ x hx
    obtain ⟨n, hn'⟩ := ih (r + 1) (by omega) _ hn
    refine ⟨n + Pi.single ⟨r, hlt⟩ n₀, ?_⟩
    rw [map_add, sumMap_single, hn']
    exact sub_add_cancel _ _

/- English proof (translation)
Use `⟨(injective_iff_map_eq_zero _).2 fun n h => funext fun i => ?_, fun x => ?_⟩` and prove the remaining obligations. Use `eq_zero_of_mem S n m ?_ i i.2` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `zero_mem _`. Conclude with `exists_sumMap S m 0 (by omega) x (by rw [dividedPowerFiltration_zero_eq]; trivial)`.
-/
theorem sumMap_bij : Function.Bijective (sumMap S) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun n h => funext fun i => ?_, fun x => ?_⟩
  · refine eq_zero_of_mem S n m ?_ i i.2
    rw [h]
    exact zero_mem _
  · exact exists_sumMap S m 0 (by omega) x (by rw [dividedPowerFiltration_zero_eq]; trivial)

def sumEquiv : (∀ i, S.N i) ≃ₗ[O] A := LinearEquiv.ofBijective (sumMap S) (sumMap_bij S)

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem sumEquiv_apply (n : ∀ i, S.N i) : sumEquiv S n = sumMap S n := rfl

/- English proof (translation)
Simplify using `[TensorProduct.piLeft, TensorProduct.piRight]`.
-/
theorem piLeft_tmul_apply (n : ∀ i, S.N i) (x : Γ) (i : Fin m) :
    TensorProduct.piLeft O Γ S.N (n ⊗ₜ x) i = n i ⊗ₜ x := by
  simp [TensorProduct.piLeft, TensorProduct.piRight]

def tensEquiv (Γ : Type) [CommRing Γ] [Algebra O Γ] : (∀ i, S.N i ⊗[O] Γ) ≃ₗ[O] A ⊗[O] Γ :=
  (TensorProduct.piLeft O Γ S.N).symm ≪≫ₗ LinearEquiv.rTensor Γ (sumEquiv S)

/- English proof (translation)
Rewrite using `[LinearEquiv.symm_apply_eq]`. Use function extensionality and compare the values at `j`. Rewrite using `[piLeft_tmul_apply]`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne h]`.
-/
theorem piLeft_symm_single (i : Fin m) (n : S.N i) (x : Γ) :
    (TensorProduct.piLeft O Γ S.N).symm (Pi.single i (n ⊗ₜ x)) = (Pi.single i n : ∀ i, S.N i) ⊗ₜ x := by
  rw [LinearEquiv.symm_apply_eq]
  funext j
  rw [piLeft_tmul_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

/- English proof (translation)
Simplify using `only [tensEquiv, LinearEquiv.trans_apply, piLeft_symm_single]`. Simplify using `[sumMap_single]`.
-/
theorem tensEquiv_single (i : Fin m) (n : S.N i) (x : Γ) :
    tensEquiv S Γ (Pi.single i (n ⊗ₜ x)) = S.ν i n ⊗ₜ x := by
  simp only [tensEquiv, LinearEquiv.trans_apply, piLeft_symm_single]
  simp [sumMap_single]

def coord (i : Fin m) : A →ₗ[O] S.N i := (LinearMap.proj i).comp (sumEquiv S).symm.toLinearMap

/- English proof (translation)
Establish `e : sumMap S ((sumEquiv S).symm a) = a` using `(sumEquiv S).apply_symm_apply a`. Establish `h : sumMap S ((sumEquiv S).symm a) ∈ pdP γ r` using `e.symm ▸ ha`. Conclude with `eq_zero_of_mem S _ r h i hi`.
-/
theorem coord_eq_zero (i : Fin m) {r : ℕ} (hi : (i : ℕ) < r) {a : A} (ha : a ∈ pdP γ r) : coord S i a = 0 := by
  have e : sumMap S ((sumEquiv S).symm a) = a := (sumEquiv S).apply_symm_apply a
  have h : sumMap S ((sumEquiv S).symm a) ∈ pdP γ r := e.symm ▸ ha
  exact eq_zero_of_mem S _ r h i hi

/- English proof (translation)
Take `⟨y, rfl⟩` from `(TensorProduct.piLeft O Γ S.N).surjective z`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul n x`. Establish `e : tensEquiv S Γ (TensorProduct.piLeft O Γ S.N (n ⊗ₜ x)) = sumEquiv S n ⊗ₜ x`.

Simplify using `only [tensEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression. Establish `e' : coord S i (sumEquiv S n) = n i`. Simplify using `only [coord, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression.

Rewrite using `[e, LinearMap.rTensor_tmul, e', piLeft_tmul_apply]`. Consider the case `add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]`.
-/
theorem coord_tensEquiv (i : Fin m) (z : ∀ i, S.N i ⊗[O] Γ) :
    (coord S i).rTensor Γ (tensEquiv S Γ z) = z i := by
  obtain ⟨y, rfl⟩ := (TensorProduct.piLeft O Γ S.N).surjective z
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul n x =>
    have e : tensEquiv S Γ (TensorProduct.piLeft O Γ S.N (n ⊗ₜ x)) = sumEquiv S n ⊗ₜ x := by
      simp only [tensEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      rfl
    have e' : coord S i (sumEquiv S n) = n i := by
      simp only [coord, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      rfl
    rw [e, LinearMap.rTensor_tmul, e', piLeft_tmul_apply]
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

/- English proof (translation)
Establish `key : ∀ c : A ⊗[O] Γ, (coord S i).rTensor Γ (c * w) = 0`. Use `Submodule.span_induction (p := fun w _ => ∀ c : A ⊗[O] Γ, (coord S i).rTensor Γ (c * w) = 0) ?_ ?_ ?_ ?_ hw` and prove the remaining obligations. Introduce and unpack `_ ⟨p, hp, rfl⟩ c`. Proceed by induction on `c using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a x`. Establish `e : (a ⊗ₜ[O] x) * Algebra.TensorProduct.includeLeftRingHom (R` using `O) (A := A) (B := Γ) p = (a * p) ⊗ₜ[O] x := by`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[e, LinearMap.rTensor_tmul, coord_eq_zero S i hi (Ideal.mul_mem_left _ _ hp), TensorProduct.zero_tmul]`. Consider the case `add a b ha hb => rw [add_mul, map_add, ha, hb, add_zero]`.

Introduce `c`. Simplify using the standard rewrite rules. Introduce `u v _ _ hu hv c`. Rewrite using `[mul_add, map_add, hu, hv, add_zero]`. Introduce `b u _ hu c`.

Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hu _`. Simplify using `using key 1`.
-/
theorem coord_map_eq_zero (i : Fin m) {r : ℕ} (hi : (i : ℕ) < r) {w : A ⊗[O] Γ}
    (hw : w ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ))) :
    (coord S i).rTensor Γ w = 0 := by
  have key : ∀ c : A ⊗[O] Γ, (coord S i).rTensor Γ (c * w) = 0 := by
    refine Submodule.span_induction (p := fun w _ => ∀ c : A ⊗[O] Γ, (coord S i).rTensor Γ (c * w) = 0)
      ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨p, hp, rfl⟩ c
      induction c using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        have e : (a ⊗ₜ[O] x) * Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ) p
            = (a * p) ⊗ₜ[O] x := by
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        rw [e, LinearMap.rTensor_tmul, coord_eq_zero S i hi (Ideal.mul_mem_left _ _ hp), TensorProduct.zero_tmul]
      | add a b ha hb => rw [add_mul, map_add, ha, hb, add_zero]
    · intro c
      simp
    · intro u v _ _ hu hv c
      rw [mul_add, map_add, hu, hv, add_zero]
    · intro b u _ hu c
      rw [smul_eq_mul, ← mul_assoc]
      exact hu _
  simpa using key 1

/- English proof (translation)
Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul n x`. Rewrite using `[tensEquiv_single]`. Establish `e : S.ν i n ⊗ₜ[O] x = Algebra.TensorProduct.includeLeftRingHom (R` using `O) (A := A) (B := Γ) (S.ν i n) * ((1 : A) ⊗ₜ[O] x) := by`.

Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (dividedPowerFiltration_le hi (S.mem i n)))`. Consider the case `add a b ha hb`. Rewrite using `[Pi.single_add, map_add]`.

Conclude with `add_mem ha hb`.
-/
theorem single_mem_map (i : Fin m) {r : ℕ} (hi : r ≤ (i : ℕ)) (t : S.N i ⊗[O] Γ) :
    tensEquiv S Γ (Pi.single i t) ∈
      (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ)) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul n x =>
    rw [tensEquiv_single]
    have e : S.ν i n ⊗ₜ[O] x = Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ) (S.ν i n)
        * ((1 : A) ⊗ₜ[O] x) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (dividedPowerFiltration_le hi (S.mem i n)))
  | add a b ha hb =>
    rw [Pi.single_add, map_add]
    exact add_mem ha hb

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i hi`. Rewrite using `[← coord_tensEquiv S i z]`. Conclude with `coord_map_eq_zero S i hi h`. Introduce `h`.

Rewrite using `[← Finset.univ_sum_single z, map_sum]`. Use `Ideal.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : (i : ℕ) < r`. Rewrite using `[h i hi, Pi.single_zero, map_zero]`. Conclude with `zero_mem _`.

Conclude with `single_mem_map S i (not_lt.1 hi) _`.
-/
theorem tensEquiv_mem_iff (r : ℕ) (z : ∀ i, S.N i ⊗[O] Γ) :
    tensEquiv S Γ z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ)) ↔
      ∀ i : Fin m, (i : ℕ) < r → z i = 0 := by
  constructor
  · intro h i hi
    rw [← coord_tensEquiv S i z]
    exact coord_map_eq_zero S i hi h
  · intro h
    rw [← Finset.univ_sum_single z, map_sum]
    refine Ideal.sum_mem _ fun i _ => ?_
    by_cases hi : (i : ℕ) < r
    · rw [h i hi, Pi.single_zero, map_zero]
      exact zero_mem _
    · exact single_mem_map S i (not_lt.1 hi) _

/- English proof (translation)
Introduce `O A Γ _ _ _ _ _ _ I γ m S`. Conclude with `⟨tensEquiv S Γ, tensEquiv_single S, tensEquiv_mem_iff S⟩`.
-/
theorem main : ∀ {O A Γ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing Γ] [Algebra O Γ] [Module.Flat O Γ]
    {I : Ideal A} (γ : DividedPowers I) (m : ℕ) (S : GrSplit O γ m),
    ∃ g : (∀ i, S.N i ⊗[O] Γ) ≃ₗ[O] A ⊗[O] Γ, (∀ i n x, g (Pi.single i (n ⊗ₜ x)) = S.ν i n ⊗ₜ x) ∧
      ∀ (r : ℕ) (z : ∀ i, S.N i ⊗[O] Γ), g z ∈ (pdP γ r).map (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := Γ)) ↔
        ∀ i : Fin m, (i : ℕ) < r → z i = 0 := by
  intro O A Γ _ _ _ _ _ _ I γ m S
  exact ⟨tensEquiv S Γ, tensEquiv_single S, tensEquiv_mem_iff S⟩

end GlobalTheory.CompanionTheory.GrTens
