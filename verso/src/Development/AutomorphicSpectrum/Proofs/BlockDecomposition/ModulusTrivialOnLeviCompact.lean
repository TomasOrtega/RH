import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.HalfModCompact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Establish `hopen : ∀ y : kˣ, IsOpen {x : k | valuation k x ≤ valuation k (y : k)}`. Introduce `y`. Establish `hy : valuation k (y : k) ≠ 0` using `by simp`. Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `x hx`.

Rewrite using `[IsValuativeTopology.mem_nhds_iff]`. Use `⟨Units.mk0 (valuation k (y : k)) hy, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Simplify using `only [Set.mem_ofPred_eq] at hz hx ⊢`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨t, ht⟩` from `hC.elim_finite_subcover (fun y : kˣ => {x : k | valuation k x ≤ valuation k (y : k)}) hopen (by`. Introduce `x _`. Rewrite using `[Set.mem_iUnion]`. Distinguish the cases in `hx : x = 0`. Conclude with `⟨1, by simp [hx]⟩`.

Conclude with `⟨Units.mk0 x hx, by simp⟩)`. Take `⟨y, -, hy⟩` from `Finset.exists_max_image (insert 1 t) (fun y : kˣ => valuation k (y : k)) (Finset.insert_nonempty _ _)`. Use `⟨nabs k y, fun u hu => nabs_le_of_valuation_le ?_⟩` and prove the remaining obligations. Take `⟨z, hz, hzu⟩` from `Set.mem_iUnion₂.1 (ht hu)`. Conclude with `le_trans hzu (hy z (Finset.mem_insert_of_mem hz))`.
-/
theorem exists_nabs_le_of_isCompact {C : Set k} (hC : IsCompact C) :
    ∃ B : ℝ, ∀ u : kˣ, (u : k) ∈ C → nabs k u ≤ B := by
  classical
  have hopen : ∀ y : kˣ, IsOpen {x : k | valuation k x ≤ valuation k (y : k)} := by
    intro y
    have hy : valuation k (y : k) ≠ 0 := by simp
    rw [isOpen_iff_mem_nhds]
    intro x hx
    rw [IsValuativeTopology.mem_nhds_iff]
    refine ⟨Units.mk0 (valuation k (y : k)) hy, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    simp only [Set.mem_ofPred_eq] at hz hx ⊢
    calc valuation k (x + z) ≤ max (valuation k x) (valuation k z) := Valuation.map_add _ _ _
      _ ≤ valuation k (y : k) := max_le hx (le_of_lt (by simpa using hz))
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun y : kˣ => {x : k | valuation k x ≤ valuation k (y : k)})
    hopen (by
      intro x _
      rw [Set.mem_iUnion]
      by_cases hx : x = 0
      · exact ⟨1, by simp [hx]⟩
      · exact ⟨Units.mk0 x hx, by simp⟩)
  obtain ⟨y, -, hy⟩ := Finset.exists_max_image (insert 1 t) (fun y : kˣ => valuation k (y : k))
    (Finset.insert_nonempty _ _)
  refine ⟨nabs k y, fun u hu => nabs_le_of_valuation_le ?_⟩
  obtain ⟨z, hz, hzu⟩ := Set.mem_iUnion₂.1 (ht hu)
  exact le_trans hzu (hy z (Finset.mem_insert_of_mem hz))

/- English proof (translation)
Unfold `nabs`. Rewrite using `[map_pow, NNReal.coe_pow]`.
-/
theorem nabs_pow_eq (y : kˣ) (n : ℕ) : nabs k (y ^ n) = nabs k y ^ n := by
  unfold nabs
  rw [map_pow, NNReal.coe_pow]

/- English proof (translation)
Unfold `nabs`. Rewrite using `[map_inv, NNReal.coe_inv]`.
-/
theorem nabs_inv_eq (y : kˣ) : nabs k y⁻¹ = (nabs k y)⁻¹ := by
  unfold nabs
  rw [map_inv, NNReal.coe_inv]

/- English proof (translation)
Establish `hpos : 0 < nabs k y` using `(nabs_properties k).2.1 y`. Break down `lt_trichotomy (nabs k y) 1 with hlt | heq | hgt` into its components or cases. It suffices to derive a contradiction. Establish `hinv : 1 < (nabs k y)⁻¹` using `(one_lt_inv₀ hpos).2 hlt`. Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt B hinv`.

Establish `h3` using `h₂ n`. Rewrite `h3` using `[nabs_pow_eq, nabs_inv_eq]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `heq`. It suffices to derive a contradiction.

Take `⟨n, hn⟩` from `pow_unbounded_of_one_lt B hgt`. Establish `h3` using `h₁ n`. Rewrite `h3` using `[nabs_pow_eq]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nabs_eq_one_of_pow_le (y : kˣ) (B : ℝ) (h₁ : ∀ n : ℕ, nabs k (y ^ n) ≤ B)
    (h₂ : ∀ n : ℕ, nabs k (y⁻¹ ^ n) ≤ B) : nabs k y = 1 := by
  have hpos : 0 < nabs k y := (nabs_properties k).2.1 y
  rcases lt_trichotomy (nabs k y) 1 with hlt | heq | hgt
  · exfalso
    have hinv : 1 < (nabs k y)⁻¹ := (one_lt_inv₀ hpos).2 hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hinv
    have h3 := h₂ n
    rw [nabs_pow_eq, nabs_inv_eq] at h3
    linarith
  · exact heq
  · exfalso
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt B hgt
    have h3 := h₁ n
    rw [nabs_pow_eq] at h3
    linarith

def blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) (g : GL (Fin N) k) : k :=
  Matrix.det (Matrix.of fun i j : Fin (d a) =>
    (g : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩))

/- English proof (translation)
Unfold `blockDet`. Use `first`. Consider the case `fun_prop`. Consider the case `exact Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => (Units.continuous_val.matrix_elem _ _))`.
-/
theorem continuous_blockDet {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h) :
    Continuous (blockDet (k := k) d hd a) := by
  unfold blockDet
  first
    | fun_prop
    | exact Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j =>
        (Units.continuous_val.matrix_elem _ _))

/- English proof (translation)
Unfold `blockDet`. Establish `hm : (Matrix.of fun i j : Fin (d a) => ((leviEmb k (stdBlocks d hd) x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩)) = ((x a : GL (Bl d a) k) : Matrix (Bl d a) (Bl d a) k)`. Use extensionality with `i j`. Simplify using `[leviEmb, Matrix.blockDiagonal'_apply_eq]`. Rewrite using `[hm, Matrix.GeneralLinearGroup.val_det_apply]`.
-/
theorem blockDet_leviEmb {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N) (a : Fin h)
    (x : Levi k (Bl d)) :
    blockDet d hd a (leviEmb k (stdBlocks d hd) x) =
      ((Matrix.GeneralLinearGroup.det (x a) : kˣ) : k) := by
  unfold blockDet
  have hm : (Matrix.of fun i j : Fin (d a) =>
      ((leviEmb k (stdBlocks d hd) x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
        (stdBlocks d hd ⟨a, i⟩) (stdBlocks d hd ⟨a, j⟩)) =
      ((x a : GL (Bl d a) k) : Matrix (Bl d a) (Bl d a) k) := by
    ext i j
    simp [leviEmb, Matrix.blockDiagonal'_apply_eq]
  rw [hm, Matrix.GeneralLinearGroup.val_det_apply]

/- English proof (translation)
Establish `hmem : ∀ z ∈ KM k N J d hd, blockDet d hd a (leviEmb k (stdBlocks d hd) z) ∈ blockDet (k` using `k) d hd a '' (J : Set (GL (Fin N) k)) := fun z hz => ⟨_, hz, rfl⟩`. Take `⟨B, hB⟩` from `exists_nabs_le_of_isCompact (hJ.image (continuous_blockDet d hd a))`. Apply `nabs_eq_one_of_pow_le _ B` to reduce the goal to its premises. Introduce `n`. Apply `hB` to reduce the goal to its premises.

Establish `h1` using `hmem _ ((KM k N J d hd).pow_mem hx n)`. Establish `e : (x ^ n) a = x a ^ n` using `rfl`. Rewrite `h1` using `[blockDet_leviEmb, e, map_pow]`. Conclude with `h1`. Introduce `n`.

Apply `hB` to reduce the goal to its premises. Establish `h1` using `hmem _ ((KM k N J d hd).pow_mem ((KM k N J d hd).inv_mem hx) n)`. Establish `e : (x⁻¹ ^ n) a = (x a)⁻¹ ^ n` using `rfl`. Rewrite `h1` using `[blockDet_leviEmb, e, map_pow, map_inv]`. Conclude with `h1`.
-/
theorem nabs_det_eq_one_of_mem_KM {N h : ℕ} (d : Fin h → ℕ) (hd : ∑ a, d a = N)
    {J : Subgroup (GL (Fin N) k)} (hJ : IsCompact (J : Set (GL (Fin N) k)))
    {x : Levi k (Bl d)} (hx : x ∈ KM k N J d hd) (a : Fin h) :
    nabs k (Matrix.GeneralLinearGroup.det (x a)) = 1 := by
  have hmem : ∀ z ∈ KM k N J d hd, blockDet d hd a (leviEmb k (stdBlocks d hd) z) ∈
      blockDet (k := k) d hd a '' (J : Set (GL (Fin N) k)) :=
    fun z hz => ⟨_, hz, rfl⟩
  obtain ⟨B, hB⟩ := exists_nabs_le_of_isCompact (hJ.image (continuous_blockDet d hd a))
  apply nabs_eq_one_of_pow_le _ B
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem hx n)
    have e : (x ^ n) a = x a ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow] at h1
    exact h1
  · intro n
    apply hB
    have h1 := hmem _ ((KM k N J d hd).pow_mem ((KM k N J d hd).inv_mem hx) n)
    have e : (x⁻¹ ^ n) a = (x a)⁻¹ ^ n := rfl
    rw [blockDet_leviEmb, e, map_pow, map_inv] at h1
    exact h1

/- English proof (translation)
Introduce `k _ _ _ _ N h d hd J hJ x hx`. Unfold `deltaHalf`. Rewrite using `[MonoidHom.finsetProd_apply]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `a _`.

Rewrite using `[MonoidHom.comp_apply, Pi.evalMonoidHom_apply]`. Unfold `detChar`. Rewrite using `[MonoidHom.comp_apply]`. Apply `Units.ext` to reduce the goal to its premises. Simplify using `[absPow, nabs_det_eq_one_of_mem_KM d hd hJ hx a]`.
-/
theorem deltaHalf_eq_one_of_mem_KM :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)),
      IsCompact (J : Set (GL (Fin N) k)) → ∀ x ∈ KM k N J d hd, deltaHalf k (Bl d) x = 1 := by
  intro k _ _ _ _ N h d hd J hJ x hx
  unfold deltaHalf
  rw [MonoidHom.finsetProd_apply]
  apply Finset.prod_eq_one
  intro a _
  rw [MonoidHom.comp_apply, Pi.evalMonoidHom_apply]
  unfold detChar
  rw [MonoidHom.comp_apply]
  apply Units.ext
  simp [absPow, nabs_det_eq_one_of_mem_KM d hd hJ hx a]

end GlobalTheory.CompanionTheory.HalfModCompact
