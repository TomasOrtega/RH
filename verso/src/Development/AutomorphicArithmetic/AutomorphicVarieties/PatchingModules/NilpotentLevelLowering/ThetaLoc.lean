import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `i j hij`. Establish `hne : j ≠ i` using `ne_of_gt hij`. Establish `hsplit : ∏ l, b l = b i * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l)`. Rewrite using `[Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩), Finset.mul_prod_erase _ _ (Finset.mem_univ i)]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hsplit, mul_assoc]`. Use `_ ≤ 1 * (b j * 1) := mul_le_mul' (hab i) (mul_le_mul' le_rfl (Finset.prod_le_one' (fun l _ => hb1 l)))`. Use `_ ≤ a j := by rw [one_mul, mul_one]; exact hba j`.
-/
private theorem mul_prod_le_of_le_one_of_le_of_mul_le_one {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a b : Fin n → G) (hb1 : ∀ l, b l ≤ 1) (hba : ∀ l, b l ≤ a l) (hab : ∀ l, a l * b l ≤ 1) :
    ∀ i j : Fin n, i < j → a i * ∏ l, b l ≤ a j := by
  classical
  intro i j hij
  have hne : j ≠ i := ne_of_gt hij
  have hsplit : ∏ l, b l = b i * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
    rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ j⟩),
      Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  calc a i * ∏ l, b l = (a i * b i) * (b j * ∏ l ∈ (Finset.univ.erase i).erase j, b l) := by
        rw [hsplit, mul_assoc]
    _ ≤ 1 * (b j * 1) := mul_le_mul' (hab i) (mul_le_mul' le_rfl (Finset.prod_le_one' (fun l _ => hb1 l)))
    _ ≤ a j := by rw [one_mul, mul_one]; exact hba j

/- English proof (translation)
Break down `lt_or_eq_of_le hij with h | h` into its components or cases. Take `⟨d, hd⟩ : ∃ d, n - (i : ℕ) = (n - (j : ℕ)) + d + 1` from `⟨(j : ℕ) - i - 1, by have := j.isLt; have := Fin.lt_iff_val_lt_val.mp h; omega⟩`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hd, pow_add, pow_add, pow_one]`. The two sides agree by associativity and commutativity.

Use `_ ≤ a j * 1 * c ^ (n - (j : ℕ)) := mul_le_mul' (mul_le_mul' (hc i j h) (pow_le_one' hc1 d)) le_rfl`. Use `_ = a j * c ^ (n - (j : ℕ)) := by rw [mul_one]`. Rewrite using `[h]`.
-/
private theorem mul_pow_sub_le_of_mul_le_of_le_of_le_one {G : Type} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] {n : ℕ}
    (a : Fin n → G) (c : G) (hc1 : c ≤ 1) (hc : ∀ i j : Fin n, i < j → a i * c ≤ a j) (i j : Fin n)
    (hij : i ≤ j) : a i * c ^ (n - (i : ℕ)) ≤ a j * c ^ (n - (j : ℕ)) := by
  rcases lt_or_eq_of_le hij with h | h
  · obtain ⟨d, hd⟩ : ∃ d, n - (i : ℕ) = (n - (j : ℕ)) + d + 1 :=
      ⟨(j : ℕ) - i - 1, by have := j.isLt; have := Fin.lt_iff_val_lt_val.mp h; omega⟩
    calc a i * c ^ (n - (i : ℕ)) = (a i * c) * c ^ d * c ^ (n - (j : ℕ)) := by
          rw [hd, pow_add, pow_add, pow_one]; ac_rfl
      _ ≤ a j * 1 * c ^ (n - (j : ℕ)) := mul_le_mul' (mul_le_mul' (hc i j h) (pow_le_one' hc1 d)) le_rfl
      _ = a j * c ^ (n - (j : ℕ)) := by rw [mul_one]
  · rw [h]

/- English proof (translation)
Set `φ : kˣ →* (ValueGroupWithZero k)ˣ` to `Units.map (valuation k).toMonoidWithZeroHom.toMonoidHom`. Establish `hφ : ∀ u : kˣ, valuation k (u : k) = ((φ u : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)` using `fun u => rfl`. Set `w : Fin n → kˣ` to `fun l => if φ (t l) ≤ 1 then t l else (t l)⁻¹`. Establish `hw1 : ∀ l, φ (w l) ≤ 1` using `fun l => by`. Simplify using `only [w]`.

Use `split_ifs with h`. Conclude with `h`. Rewrite using `[map_inv]`. Conclude with `inv_le_one'.mpr (le_of_lt (not_le.mp h))`. Establish `hwa : ∀ l, φ (w l) ≤ φ (t l)` using `fun l => by`.

Simplify using `only [w]`. Use `split_ifs with h`. Conclude with `le_rfl`. Rewrite using `[map_inv]`. Conclude with `(inv_le_one'.mpr (le_of_lt (not_le.mp h))).trans (le_of_lt (not_le.mp h))`.

Establish `hwab : ∀ l, φ (t l) * φ (w l) ≤ 1` using `fun l => by`. Simplify using `only [w]`. Use `split_ifs with h`. Conclude with `mul_le_one' h h`. Rewrite using `[map_inv, mul_inv_cancel]`.

Establish `hC : φ (∏ l, w l) = ∏ l, φ (w l)` using `map_prod φ _ _`. Establish `hc1 : ∏ l, φ (w l) ≤ 1` using `Finset.prod_le_one' (fun l _ => hw1 l)`. Use `⟨fun i => (∏ l, w l) ^ (n - (i : ℕ)), ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij dsimp only`. Rewrite using `[hφ, hφ, Units.val_le_val, map_pow, map_pow, hC]`.

Simplify using `using mul_pow_sub_le_of_mul_le_of_le_of_le_one (fun _ => (1 : (ValueGroupWithZero k)ˣ)) _ hc1 (fun _ _ _ => by rw [one_mul]; exact hc1) i j hij`. Introduce `i j hij`. Rewrite using `[Pi.mul_apply, Pi.mul_apply]`. Rewrite using `[hφ, hφ, Units.val_le_val, map_mul, map_mul, map_pow, map_pow, hC]`. Conclude with `mul_pow_sub_le_of_mul_le_of_le_of_le_one (fun l => φ (t l)) _ hc1 (mul_prod_le_of_le_one_of_le_of_mul_le_one (fun l => φ (t l)) (fun l => φ (w l)) hw1 hwa hwab) i j hij`.
-/
private theorem thetaLoc_split {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (t : Fin n → kˣ) : ∃ b : Fin n → kˣ, Dom b ∧ Dom (t * b) := by
  classical
  let φ : kˣ →* (ValueGroupWithZero k)ˣ := Units.map (valuation k).toMonoidWithZeroHom.toMonoidHom
  have hφ : ∀ u : kˣ, valuation k (u : k) = ((φ u : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) :=
    fun u => rfl
  let w : Fin n → kˣ := fun l => if φ (t l) ≤ 1 then t l else (t l)⁻¹
  have hw1 : ∀ l, φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact h
    · rw [map_inv]; exact inv_le_one'.mpr (le_of_lt (not_le.mp h))
  have hwa : ∀ l, φ (w l) ≤ φ (t l) := fun l => by
    simp only [w]
    split_ifs with h
    · exact le_rfl
    · rw [map_inv]
      exact (inv_le_one'.mpr (le_of_lt (not_le.mp h))).trans (le_of_lt (not_le.mp h))
  have hwab : ∀ l, φ (t l) * φ (w l) ≤ 1 := fun l => by
    simp only [w]
    split_ifs with h
    · exact mul_le_one' h h
    · rw [map_inv, mul_inv_cancel]
  have hC : φ (∏ l, w l) = ∏ l, φ (w l) := map_prod φ _ _
  have hc1 : ∏ l, φ (w l) ≤ 1 := Finset.prod_le_one' (fun l _ => hw1 l)
  refine ⟨fun i => (∏ l, w l) ^ (n - (i : ℕ)), ?_, ?_⟩
  · intro i j hij
    dsimp only
    rw [hφ, hφ, Units.val_le_val, map_pow, map_pow, hC]
    simpa using mul_pow_sub_le_of_mul_le_of_le_of_le_one (fun _ => (1 : (ValueGroupWithZero k)ˣ)) _ hc1
      (fun _ _ _ => by rw [one_mul]; exact hc1) i j hij
  · intro i j hij
    rw [Pi.mul_apply, Pi.mul_apply]
    rw [hφ, hφ, Units.val_le_val, map_mul, map_mul, map_pow, map_pow, hC]
    exact mul_pow_sub_le_of_mul_le_of_le_of_le_one (fun l => φ (t l)) _ hc1
      (mul_prod_le_of_le_one_of_le_of_mul_le_one (fun l => φ (t l)) (fun l => φ (w l)) hw1 hwa hwab) i j hij

/- English proof (translation)
Establish `key : ∀ y, ((θ b)⁻¹).val ((θ b).val y) = y` using `fun y => by`. Rewrite using `[← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]`. Establish `h1` using `htb m`. Rewrite `h1` using `[mul_comm t b]`. Simplify using `only [map_mul, Units.val_mul, Module.End.mul_apply] at h1`.

Rewrite `h1` using `[← hb]`. Rewrite using `[← key ((θ t).val (ι m)), h1, key]`.
-/
private theorem thetaLoc_ext {T A M₁ M₂ : Type} [CommGroup T] [CommRing A] [AddCommGroup M₁] [Module A M₁]
    [AddCommGroup M₂] [Module A M₂] (Θ : T →* (Module.End A M₁)ˣ) (θ : T →* (Module.End A M₂)ˣ) (ι : M₁ → M₂)
    (t b : T) (hb : ∀ m, (θ b).val (ι m) = ι ((Θ b).val m))
    (htb : ∀ m, (θ (t * b)).val (ι m) = ι ((Θ (t * b)).val m)) (m : M₁) :
    (θ t).val (ι m) = ι ((Θ t).val m) := by
  have key : ∀ y, ((θ b)⁻¹).val ((θ b).val y) = y := fun y => by
    rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]
  have h1 := htb m
  rw [mul_comm t b] at h1
  simp only [map_mul, Units.val_mul, Module.End.mul_apply] at h1
  rw [← hb] at h1
  rw [← key ((θ t).val (ι m)), h1, key]

/- English proof (translation)
Introduce `L _ _ n q w A M _ _ _ ρ C Θ hΘ j θ hθ t m m' hm`. Establish `hmem : ∀ u ∈ iwC _ n (C j), atJ n w j u ∈ UC n w C`. Introduce `u hu`. Simplify using `only [UC, Subgroup.mem_pi]`. Introduce `i _`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify `hu` using `[atJ]`. Simplify using `[atJ, Pi.mulSingle_eq_of_ne h, Subgroup.one_mem]`. Set `ι : fixd ρ (UC n w C) → fixd (ρ.comp (atJ n w j)) (iwC _ n (C j))` to `fun x => ⟨x, show ∀ u ∈ iwC _ n (C j), (ρ.comp (atJ n w j)) u x = x from fun u hu => (show ∀ u ∈ UC n w C, ρ u x = x from x.2) _ (hmem u hu)⟩`.

Establish `hdom : ∀ s, Dom s → ∀ x, (θ s).val (ι x) = ι ((Θ j s).val x)`. Introduce `s hs x`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hθ s hs]`. Unfold `hk`.

Rewrite using `[(hkApply _ _ _ _ _ _ _ ((heckePairIwC _ n (C j)).1 _)).1]`. Conclude with `(hΘ.1 j s hs x).symm`. Take `⟨b, hb, htb⟩` from `thetaLoc_split t`. Establish `key` using `thetaLoc_ext (Θ j) θ ι t b (hdom b hb) (hdom (t * b) htb) m`. Establish `hm' : m' = ι m` using `Subtype.ext hm`.

Rewrite using `[hm', key]`.
-/
theorem UpperTheory.V.Pa.Lev.thetaLoc :
    ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GV n w) M) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ), IsThetaQ ρ C Θ → ∀ j θ, IsTheta (ρ.comp (atJ n w j)) (C j) θ → ∀ t (m : fixd ρ (UC n w C)) (m' : fixd (ρ.comp (atJ n w j)) (iwC _ n (C j))), (m' : M) = m → ((θ t).val m').val = ((Θ j t).val m).val := by
  intro L _ _ n q w A M _ _ _ ρ C Θ hΘ j θ hθ t m m' hm
  have hmem : ∀ u ∈ iwC _ n (C j), atJ n w j u ∈ UC n w C := by
    intro u hu
    simp only [UC, Subgroup.mem_pi]
    intro i _
    by_cases h : i = j
    · subst h
      simpa [atJ] using hu
    · simp [atJ, Pi.mulSingle_eq_of_ne h, Subgroup.one_mem]
  let ι : fixd ρ (UC n w C) → fixd (ρ.comp (atJ n w j)) (iwC _ n (C j)) := fun x =>
    ⟨x, show ∀ u ∈ iwC _ n (C j), (ρ.comp (atJ n w j)) u x = x from fun u hu =>
      (show ∀ u ∈ UC n w C, ρ u x = x from x.2) _ (hmem u hu)⟩
  have hdom : ∀ s, Dom s → ∀ x, (θ s).val (ι x) = ι ((Θ j s).val x) := by
    intro s hs x
    apply Subtype.ext
    rw [hθ s hs]
    unfold hk
    rw [(hkApply _ _ _ _ _ _ _ ((heckePairIwC _ n (C j)).1 _)).1]
    exact (hΘ.1 j s hs x).symm
  obtain ⟨b, hb, htb⟩ := thetaLoc_split t
  have key := thetaLoc_ext (Θ j) θ ι t b (hdom b hb) (hdom (t * b) htb) m
  have hm' : m' = ι m := Subtype.ext hm
  rw [hm', key]
