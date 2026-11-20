import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelowStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.FinitePosDefFormSublevelStatement

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

/- English proof (translation)
Establish `hmin : ∀ (V : Set (Fin m → ℕ)) (a : Fin m → ℕ), a ∈ V → ∃ v, Minimal (· ∈ V) v ∧ v ≤ a`. Introduce `V a ha`. Take `⟨v, ⟨hvV, hva⟩, hvmin⟩` from `wellFounded_lt.has_min {w | w ∈ V ∧ w ≤ a} ⟨a, ha, le_rfl⟩`. Use `⟨v, ⟨hvV, fun w hwV hwv => ?_⟩, hva⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`.

Conclude with `hvmin w ⟨hwV, hwv.trans hva⟩ (lt_of_le_of_ne hwv fun h => hne (le_of_eq h.symm))`. Use `set e := (Module.finBasis ℤ X).equivFun with he`. Establish `key : ∀ y : X, ∃ x : X, e.symm (fun i => (((e y i : ℤ) : ZMod 2).val : ℤ)) = y + (x + x)`. Introduce `y`. Use `⟨e.symm (fun i => -(e y i / 2)), ?_⟩` and prove the remaining obligations.

Apply `e.injective` to reduce the goal to its premises. Rewrite using `[map_add, map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `i`. Simplify using `only [ZMod.val_intCast, Pi.add_apply, Nat.cast_ofNat]`. Rewrite using `[Int.emod_def]`.

Expand and normalize the polynomial expressions, which then agree. Set `red : X → (Fin (Module.finrank ℤ X) → ZMod 2)` to `fun y i => ((e y i : ℤ) : ZMod 2)`. Establish `hred : ∀ y y' : X, red y' = red y → ∃ x : X, y' = y + (x + x)`. Introduce `y y' h`. Take `⟨x1, h1⟩` from `key y`.

Take `⟨x2, h2⟩` from `key y'`. Use `⟨x1 - x2, ?_⟩` and prove the remaining obligations. Establish `hh : (fun i => ((e y' i : ℤ) : ZMod 2)) = (fun i => ((e y i : ℤ) : ZMod 2))` using `h`. Establish `h2' : e.symm (fun i => (((e y i : ℤ) : ZMod 2).val : ℤ)) = y' + (x2 + x2)`. Rewrite using `[← h2]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[congrFun hh i]`. Establish `h3 : y' + (x2 + x2) = y + (x1 + x1)` using `h2'.symm.trans h1`. Rewrite using `[eq_sub_of_add_eq h3]`.

Normalize the expressions using the abelian group laws. Set `V : (Fin (Module.finrank ℤ X) → ZMod 2) → Set (Fin m → ℕ)` to `fun ε => f '' {y | red y = ε}`. Set `M : (Fin (Module.finrank ℤ X) → ZMod 2) → Set (Fin m → ℕ)` to `fun ε => {v | Minimal (· ∈ V ε) v}`. Establish `hMfin : ∀ ε, (M ε).Finite` using `fun ε => WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain fun x => x ∈ V ε)`. Set `pick : (Fin (Module.finrank ℤ X) → ZMod 2) → (Fin m → ℕ) → X` to `fun ε v => if h : ∃ y, red y = ε ∧ f y = v then h.choose else 0`.

Use `⟨⋃ ε, pick ε '' M ε, Set.finite_iUnion fun ε => (hMfin ε).image _, fun y => ?_⟩` and prove the remaining obligations. Take `⟨v, hvM, hvle⟩` from `hmin (V (red y)) (f y) ⟨y, rfl, rfl⟩`. Establish `hex : ∃ w, red w = red y ∧ f w = v`. Take `⟨w, hw, hwv⟩` from `hvM.1`. Conclude with `⟨w, hw, hwv⟩`.

Establish `hpick : red (pick (red y) v) = red y ∧ f (pick (red y) v) = v` using `by dsimp only [pick]`. Rewrite using `[dif_pos hex]`. Conclude with `hex.choose_spec`. Use `⟨pick (red y) v, Set.mem_iUnion.mpr ⟨red y, v, hvM, rfl⟩, hred y _ hpick.1, ?_⟩` and prove the remaining obligations. Rewrite using `[hpick.2]`.

Conclude with `hvle`.
-/
theorem exists_finite_below_mod_two {X : Type} [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] {m : ℕ}
    (f : X → Fin m → ℕ) :
    ∃ G : Set X, G.Finite ∧ ∀ y, ∃ y' ∈ G, (∃ x : X, y' = y + (x + x)) ∧ f y' ≤ f y := by
  classical
  have hmin : ∀ (V : Set (Fin m → ℕ)) (a : Fin m → ℕ), a ∈ V → ∃ v, Minimal (· ∈ V) v ∧ v ≤ a := by
    intro V a ha
    obtain ⟨v, ⟨hvV, hva⟩, hvmin⟩ := wellFounded_lt.has_min {w | w ∈ V ∧ w ≤ a} ⟨a, ha, le_rfl⟩
    refine ⟨v, ⟨hvV, fun w hwV hwv => ?_⟩, hva⟩
    by_contra hne
    exact hvmin w ⟨hwV, hwv.trans hva⟩ (lt_of_le_of_ne hwv fun h => hne (le_of_eq h.symm))
  set e := (Module.finBasis ℤ X).equivFun with he
  have key : ∀ y : X, ∃ x : X,
      e.symm (fun i => (((e y i : ℤ) : ZMod 2).val : ℤ)) = y + (x + x) := by
    intro y
    refine ⟨e.symm (fun i => -(e y i / 2)), ?_⟩
    apply e.injective
    rw [map_add, map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    funext i
    simp only [ZMod.val_intCast, Pi.add_apply, Nat.cast_ofNat]
    rw [Int.emod_def]
    ring
  let red : X → (Fin (Module.finrank ℤ X) → ZMod 2) := fun y i => ((e y i : ℤ) : ZMod 2)
  have hred : ∀ y y' : X, red y' = red y → ∃ x : X, y' = y + (x + x) := by
    intro y y' h
    obtain ⟨x1, h1⟩ := key y
    obtain ⟨x2, h2⟩ := key y'
    refine ⟨x1 - x2, ?_⟩
    have hh : (fun i => ((e y' i : ℤ) : ZMod 2)) = (fun i => ((e y i : ℤ) : ZMod 2)) := h
    have h2' : e.symm (fun i => (((e y i : ℤ) : ZMod 2).val : ℤ)) = y' + (x2 + x2) := by
      rw [← h2]
      congr 1
      funext i
      rw [congrFun hh i]
    have h3 : y' + (x2 + x2) = y + (x1 + x1) := h2'.symm.trans h1
    rw [eq_sub_of_add_eq h3]
    abel
  let V : (Fin (Module.finrank ℤ X) → ZMod 2) → Set (Fin m → ℕ) := fun ε => f '' {y | red y = ε}
  let M : (Fin (Module.finrank ℤ X) → ZMod 2) → Set (Fin m → ℕ) := fun ε => {v | Minimal (· ∈ V ε) v}
  have hMfin : ∀ ε, (M ε).Finite := fun ε =>
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain fun x => x ∈ V ε)
  let pick : (Fin (Module.finrank ℤ X) → ZMod 2) → (Fin m → ℕ) → X := fun ε v =>
    if h : ∃ y, red y = ε ∧ f y = v then h.choose else 0
  refine ⟨⋃ ε, pick ε '' M ε, Set.finite_iUnion fun ε => (hMfin ε).image _, fun y => ?_⟩
  obtain ⟨v, hvM, hvle⟩ := hmin (V (red y)) (f y) ⟨y, rfl, rfl⟩
  have hex : ∃ w, red w = red y ∧ f w = v := by
    obtain ⟨w, hw, hwv⟩ := hvM.1
    exact ⟨w, hw, hwv⟩
  have hpick : red (pick (red y) v) = red y ∧ f (pick (red y) v) = v := by
    dsimp only [pick]
    rw [dif_pos hex]
    exact hex.choose_spec
  refine ⟨pick (red y) v, Set.mem_iUnion.mpr ⟨red y, v, hvM, rfl⟩, hred y _ hpick.1, ?_⟩
  rw [hpick.2]
  exact hvle

/- English proof (translation)
Introduce `X _ _ _ m P hsym hnn`. Take `⟨G, hG, hGy⟩` from `exists_finite_below_mod_two (fun y i => (P i y y).toNat)`. Use `set C : ℤ := ∑ g ∈ hG.toFinset, ∑ i, P i g g with hC`. Set `Q : Finset (Fin m) → LinearMap.BilinForm ℤ X` to `fun S => ∑ i ∈ S, P i`. Establish `hQ : ∀ S z w, Q S z w = ∑ i ∈ S, P i z w`.

Introduce `S z w`. Simplify using `[Q, LinearMap.sum_apply]`. Use `⟨⋃ S : Finset (Fin m), if (∀ y : X, y ≠ 0 → 0 < Q S y y) then {y | Q S y y ≤ S.card * C} else ∅, ?_, ?_⟩` and prove the remaining obligations. Use `Set.finite_iUnion fun S => ?_ split_ifs with hpos` and prove the remaining obligations. Conclude with `GlobalTheory.T.finite_pos_def_form_sublevel X (Q S) (fun y z => by`.

Rewrite using `[hQ, hQ]`. Conclude with `Finset.sum_congr rfl fun i _ => hsym i y z) hpos _`. Conclude with `Set.finite_empty`. Introduce and unpack `B ⟨t, ht0, rfl⟩ hB y hy`. Take `⟨S, hS⟩ : ∃ S : Finset (Fin m), S = Finset.univ.filter (fun i => 0 < t i)` from `⟨_, rfl⟩`.

Establish `hBapp : ∀ z w : X, (∑ i, t i • GlobalTheory.PolFan.toReal (P i)) z w = ∑ i, t i * ((P i z w : ℤ) : ℝ)`. Introduce `z w`. Simplify using `[GlobalTheory.PolFan.toReal, LinearMap.sum_apply]`. Establish `hBpos : ∀ z : X, z ≠ 0 → 0 < ∑ i, t i * ((P i z z : ℤ) : ℝ)`. Introduce `z hz`.

Establish `h1` using `hB 1 ![z] (linearIndependent_unique_iff.mpr (by simpa using hz)) ![1] (by simp)`. Simplify `h1` using `[hBapp]`. Establish `hterm : ∀ z : X, ∑ i, t i * ((P i z z : ℤ) : ℝ) = ∑ i ∈ S, t i * ((P i z z : ℤ) : ℝ)`. Introduce `z`. Rewrite using `[hS, Finset.sum_filter]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Both sides reduce to the same expression. Establish `h0 : t i = 0` using `le_antisymm (not_lt.mp h) (ht0 i)`. Simplify using `[h0]`.

Establish `hpos : ∀ z : X, z ≠ 0 → 0 < Q S z z`. Introduce `z hz`. Rewrite using `[hQ]`. Assume the negation of the conclusion as `hle`. Establish `h0 : ∑ i ∈ S, P i z z = 0` using `le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun i _ => hnn i z)`.

Establish `hzero : ∀ i ∈ S, P i z z = 0` using `(Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i z).mp h0`. Establish `h1` using `hBpos z hz`. Rewrite `h1` using `[hterm, Finset.sum_eq_zero fun i hi => by rw [hzero i hi]; simp]`. Conclude with `lt_irrefl _ h1`. Take `⟨y', hy'G, ⟨x, hx⟩, hle⟩` from `hGy y`.

Establish `hle' : ∀ i, P i y' y' ≤ P i y y` using `fun i => by`. Establish `h1 : (P i y' y').toNat ≤ (P i y y).toNat` using `hle i`. Establish `h2` using `hnn i y`. Establish `h3` using `hnn i y'`. Use linear arithmetic over natural numbers and integers.

Establish `hmin : ∑ i, t i * ((P i y y : ℤ) : ℝ) ≤ ∑ i, t i * ((P i y' y' : ℤ) : ℝ)`. Establish `h1` using `hy x`. Rewrite `h1` using `[← hx, hBapp, hBapp]`. Conclude with `h1`. Establish `hd : ∀ i ∈ Finset.univ, 0 ≤ t i * (((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ))` using `fun i _ => mul_nonneg (ht0 i) (sub_nonneg.mpr (by exact_mod_cast hle' i))`.

Establish `hsum : ∑ i, t i * (((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ)) = 0`. Apply `le_antisymm` to reduce the goal to its premises. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Finset.sum_nonneg hd`.

Establish `heq : ∀ i ∈ S, P i y y ≤ P i y' y'`. Introduce `i hi`. Establish `hi0` using `(Finset.sum_eq_zero_iff_of_nonneg hd).mp hsum i (Finset.mem_univ i)`. Rewrite `hi` using `[hS, Finset.mem_filter]`. Establish `h4 : ((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ) = 0`.

Break down `mul_eq_zero.mp hi0 with h | h` into its components or cases. Conclude with `absurd h hi.2.ne'`. Conclude with `h`. Establish `h5 : ((P i y y : ℤ) : ℝ) ≤ ((P i y' y' : ℤ) : ℝ)` using `by linarith`. Conclude with `h5` after adjusting the coercions.

Establish `hbound : ∀ i, P i y' y' ≤ C`. Introduce `i`. Rewrite using `[hC]`. Combine the equalities or inequalities in the displayed calculation. Use `Set.mem_iUnion.mpr ⟨S, ?_⟩` and prove the remaining obligations.

Rewrite using `[if_pos hpos]`. Use `show Q S y y ≤ S.card * C`. Rewrite using `[hQ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem finite_isMin2 : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] [Module.Free ℤ X] (m : ℕ)
    (P : Fin m → LinearMap.BilinForm ℤ X), (∀ i y z, P i y z = P i z y) → (∀ i y, 0 ≤ P i y y) →
    ∃ F : Set X, F.Finite ∧ ∀ B ∈ rcone P, IsPosDef B → ∀ y, IsMin2 B y → y ∈ F := by
  intro X _ _ _ m P hsym hnn
  classical
  obtain ⟨G, hG, hGy⟩ := exists_finite_below_mod_two (fun y i => (P i y y).toNat)
  set C : ℤ := ∑ g ∈ hG.toFinset, ∑ i, P i g g with hC
  let Q : Finset (Fin m) → LinearMap.BilinForm ℤ X := fun S => ∑ i ∈ S, P i
  have hQ : ∀ S z w, Q S z w = ∑ i ∈ S, P i z w := by
    intro S z w
    simp [Q, LinearMap.sum_apply]
  refine ⟨⋃ S : Finset (Fin m), if (∀ y : X, y ≠ 0 → 0 < Q S y y) then {y | Q S y y ≤ S.card * C} else ∅,
    ?_, ?_⟩
  · refine Set.finite_iUnion fun S => ?_
    split_ifs with hpos
    · exact GlobalTheory.T.finite_pos_def_form_sublevel X (Q S) (fun y z => by
        rw [hQ, hQ]
        exact Finset.sum_congr rfl fun i _ => hsym i y z) hpos _
    · exact Set.finite_empty
  · rintro B ⟨t, ht0, rfl⟩ hB y hy
    obtain ⟨S, hS⟩ : ∃ S : Finset (Fin m), S = Finset.univ.filter (fun i => 0 < t i) := ⟨_, rfl⟩
    have hBapp : ∀ z w : X, (∑ i, t i • GlobalTheory.PolFan.toReal (P i)) z w = ∑ i, t i * ((P i z w : ℤ) : ℝ) := by
      intro z w
      simp [GlobalTheory.PolFan.toReal, LinearMap.sum_apply]
    have hBpos : ∀ z : X, z ≠ 0 → 0 < ∑ i, t i * ((P i z z : ℤ) : ℝ) := by
      intro z hz
      have h1 := hB 1 ![z] (linearIndependent_unique_iff.mpr (by simpa using hz)) ![1] (by simp)
      simpa [hBapp] using h1
    have hterm : ∀ z : X, ∑ i, t i * ((P i z z : ℤ) : ℝ) = ∑ i ∈ S, t i * ((P i z z : ℤ) : ℝ) := by
      intro z
      rw [hS, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rfl
      · have h0 : t i = 0 := le_antisymm (not_lt.mp h) (ht0 i)
        simp [h0]
    have hpos : ∀ z : X, z ≠ 0 → 0 < Q S z z := by
      intro z hz
      rw [hQ]
      by_contra hle
      have h0 : ∑ i ∈ S, P i z z = 0 := le_antisymm (not_lt.mp hle) (Finset.sum_nonneg fun i _ => hnn i z)
      have hzero : ∀ i ∈ S, P i z z = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hnn i z).mp h0
      have h1 := hBpos z hz
      rw [hterm, Finset.sum_eq_zero fun i hi => by rw [hzero i hi]; simp] at h1
      exact lt_irrefl _ h1
    obtain ⟨y', hy'G, ⟨x, hx⟩, hle⟩ := hGy y
    have hle' : ∀ i, P i y' y' ≤ P i y y := fun i => by
      have h1 : (P i y' y').toNat ≤ (P i y y).toNat := hle i
      have h2 := hnn i y
      have h3 := hnn i y'
      omega
    have hmin : ∑ i, t i * ((P i y y : ℤ) : ℝ) ≤ ∑ i, t i * ((P i y' y' : ℤ) : ℝ) := by
      have h1 := hy x
      rw [← hx, hBapp, hBapp] at h1
      exact h1
    have hd : ∀ i ∈ Finset.univ, 0 ≤ t i * (((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ)) := fun i _ =>
      mul_nonneg (ht0 i) (sub_nonneg.mpr (by exact_mod_cast hle' i))
    have hsum : ∑ i, t i * (((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ)) = 0 := by
      apply le_antisymm
      · simp only [mul_sub, Finset.sum_sub_distrib]
        linarith
      · exact Finset.sum_nonneg hd
    have heq : ∀ i ∈ S, P i y y ≤ P i y' y' := by
      intro i hi
      have hi0 := (Finset.sum_eq_zero_iff_of_nonneg hd).mp hsum i (Finset.mem_univ i)
      rw [hS, Finset.mem_filter] at hi
      have h4 : ((P i y y : ℤ) : ℝ) - ((P i y' y' : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.mp hi0 with h | h
        · exact absurd h hi.2.ne'
        · exact h
      have h5 : ((P i y y : ℤ) : ℝ) ≤ ((P i y' y' : ℤ) : ℝ) := by linarith
      exact_mod_cast h5
    have hbound : ∀ i, P i y' y' ≤ C := by
      intro i
      rw [hC]
      calc P i y' y' ≤ ∑ j, P j y' y' := Finset.single_le_sum (fun j _ => hnn j y') (Finset.mem_univ i)
        _ ≤ ∑ g ∈ hG.toFinset, ∑ j, P j g g :=
          Finset.single_le_sum (f := fun g => ∑ j, P j g g)
            (fun g _ => Finset.sum_nonneg fun j _ => hnn j g) (hG.mem_toFinset.mpr hy'G)
    refine Set.mem_iUnion.mpr ⟨S, ?_⟩
    rw [if_pos hpos]
    show Q S y y ≤ S.card * C
    rw [hQ]
    calc ∑ i ∈ S, P i y y ≤ ∑ i ∈ S, C := Finset.sum_le_sum fun i hi => (heq i hi).trans (hbound i)
      _ = S.card * C := by rw [Finset.sum_const, nsmul_eq_mul]

end GlobalTheory.CompanionTheory.Ar.Fan
