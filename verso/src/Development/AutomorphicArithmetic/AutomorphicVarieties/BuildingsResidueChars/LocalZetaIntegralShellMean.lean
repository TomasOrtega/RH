import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LaurentBlockInduction.LdDefs
import GroundTheory.AutomorphicForms.GL2.GJFEBlockPoint

noncomputable section

open MeasureTheory Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Parabolic
open GroundTheory.Automorphic.GodementJacquet
open scoped NNReal Classical ValuativeRel

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace UpperTheory.V.Z.Gam

section Mean

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {m : ℕ}

variable [MeasurableSpace (GL (Fin m) F)] [BorelSpace (GL (Fin m) F)]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H] [SecondCountableTopology H]
  {W : Type} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (GL (Fin m) F × H) W}

private def shellForm (ν : Measure (GL (Fin m) F)) (σ : Representation ℂ (GL (Fin m) F × H) W)
    (ℓ : Module.Dual ℂ W) (k : ℤ)
    (hint : ∀ w : W, IntegrableOn (fun g : GL (Fin m) F => ℓ (σ (g, 1) w))
      {g : GL (Fin m) F | ordDet g = k} ν) : Module.Dual ℂ W where
  toFun w := ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g, 1) w) ∂ν
  map_add' a b := by
    simp only [map_add]
    exact integral_add (hint a) (hint b)
  map_smul' c w := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    exact integral_const_mul _ _

end Mean

end UpperTheory.V.Z.Gam

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Establish `h1 : (K : Set G) ∈ nhds (1 : G)` using `hK.mem_nhds K.one_mem`. Establish `h2 : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1)`. Simplify using `using (continuous_mul_left x⁻¹).tendsto x`.

Establish `h3 : ∀ᶠ y in nhds x, f y = f x` using `by filter_upwards [h2 h1] with y hy`. Use `hf x (x⁻¹ * y) hy` as an intermediate fact. Simplify using `using this`. Conclude with `tendsto_nhds_of_eventually_eq h3`.
-/
private theorem lc_lemma {G β : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace β] (K : Subgroup G) (hK : IsOpen (K : Set G)) (f : G → β)
    (hf : ∀ x, ∀ y ∈ K, f (x * y) = f x) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  have h1 : (K : Set G) ∈ nhds (1 : G) := hK.mem_nhds K.one_mem
  have h2 : Filter.Tendsto (fun y => x⁻¹ * y) (nhds x) (nhds 1) := by
    simpa using (continuous_mul_left x⁻¹).tendsto x
  have h3 : ∀ᶠ y in nhds x, f y = f x := by
    filter_upwards [h2 h1] with y hy
    have := hf x (x⁻¹ * y) hy
    simpa using this
  exact tendsto_nhds_of_eventually_eq h3

/- English proof (translation)
Use `Int.induction_on j ?_ ?_ ?_` and prove the remaining obligations. Simplify using `[ordDet_one]`. Introduce `i ih`. Rewrite using `[zpow_add_one, ordDet_mul, ih]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `i ih`. Rewrite using `[zpow_sub_one, ordDet_mul, ordDet_inv, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem ordDet_zpow' {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} (g : GL (Fin n) F) (j : ℤ) :
    ordDet (g ^ j) = j * ordDet g := by
  refine Int.induction_on j ?_ ?_ ?_
  · simp [ordDet_one]
  · intro i ih
    rw [zpow_add_one, ordDet_mul, ih]
    ring
  · intro i ih
    rw [zpow_sub_one, ordDet_mul, ordDet_inv, ih]
    ring

/- English proof (translation)
The claim follows from `lc_lemma (integralGL F n) (isOpen_integralGL F n) _ (fun x y hy => by rw [ordDet_mul, ordDet_eq_zero_of_mem_integralGL hy, add_zero])`.
-/
private theorem continuous_ordDet {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} : Continuous (ordDet : GL (Fin n) F → ℤ) :=
  lc_lemma (integralGL F n) (isOpen_integralGL F n) _ (fun x y hy => by
    rw [ordDet_mul, ordDet_eq_zero_of_mem_integralGL hy, add_zero])

/- English proof (translation)
Set `P : Set W` to `{x | ∃ h w, ordDet h = 0 ∧ x = σ (h, 1) w - χ h • w}`. Establish `hinv : ∀ p : GL (Fin m) F × H, ∀ x ∈ P, σ p x ∈ P`. Introduce and unpack `⟨g0, h0⟩ x ⟨h, w, hh, rfl⟩`. Use `⟨g0 * h * g0⁻¹, σ (g0, h0) w, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[ordDet_mul, ordDet_mul, ordDet_inv, hh]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e : ((g0, h0) : GL (Fin m) F × H) * (h, 1) = (g0 * h * g0⁻¹, 1) * (g0, h0)`. Apply the tactic sequence `ext <;> simp`. Establish `e2 : σ (g0, h0) (σ (h, 1) w) = σ (g0 * h * g0⁻¹, 1) (σ (g0, h0) w)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]`.

Rewrite using `[hχ, map_sub, map_smul, e2]`. Set `V : Subrepresentation σ` to `⟨Submodule.span ℂ P, fun p x hx => by`. Establish `hle : Submodule.span ℂ P ≤ (Submodule.span ℂ P).comap (σ p)` using `Submodule.span_le.2 (fun y hy => Submodule.mem_comap.2 (Submodule.subset_span (hinv p y hy)))`. Conclude with `hle hx⟩`. Use `haveI := hirr`.

Break down `eq_bot_or_eq_top V with hV | hV` into its components or cases. Use `right`. Introduce `h hh w`. Establish `hm : σ (h, 1) w - χ h • w ∈ V` using `(show _ ∈ Submodule.span ℂ P from Submodule.subset_span ⟨h, w, hh, rfl⟩)`. Rewrite `hm` using `[hV]`.

Establish `hm' : σ (h, 1) w - χ h • w ∈ (⊥ : Submodule ℂ W)` using `hm`. Conclude with `sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hm')`. Use `left`. Introduce `w`. Establish `hw : w ∈ V`.

Rewrite using `[hV]`. Conclude with `(Submodule.mem_top : w ∈ (⊤ : Submodule ℂ W))`. Establish `hle : Submodule.span ℂ P ≤ LinearMap.ker Λ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨h, w', hh, rfl⟩`.

Simplify using `[LinearMap.mem_ker, hΛ h hh]`. Conclude with `hle hw`.
-/
private theorem dual_eq_zero_or_smul_of_irreducible_of_conj_invariant {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {m : ℕ} {H : Type*} [Group H] {W : Type*} [AddCommGroup W]
    [Module ℂ W] (σ : Representation ℂ (GL (Fin m) F × H) W) (hirr : σ.IsIrreducible)
    (χ : GL (Fin m) F → ℂ) (hχ : ∀ g h, χ (g * h * g⁻¹) = χ h) (Λ : Module.Dual ℂ W)
    (hΛ : ∀ h, ordDet h = 0 → ∀ w, Λ (σ (h, 1) w) = χ h * Λ w) :
    (∀ w, Λ w = 0) ∨ (∀ h, ordDet h = 0 → ∀ w, σ (h, 1) w = χ h • w) := by
  let P : Set W := {x | ∃ h w, ordDet h = 0 ∧ x = σ (h, 1) w - χ h • w}
  have hinv : ∀ p : GL (Fin m) F × H, ∀ x ∈ P, σ p x ∈ P := by
    rintro ⟨g0, h0⟩ x ⟨h, w, hh, rfl⟩
    refine ⟨g0 * h * g0⁻¹, σ (g0, h0) w, ?_, ?_⟩
    · rw [ordDet_mul, ordDet_mul, ordDet_inv, hh]
      ring
    · have e : ((g0, h0) : GL (Fin m) F × H) * (h, 1) = (g0 * h * g0⁻¹, 1) * (g0, h0) := by
        ext <;> simp
      have e2 : σ (g0, h0) (σ (h, 1) w) = σ (g0 * h * g0⁻¹, 1) (σ (g0, h0) w) := by
        rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
      rw [hχ, map_sub, map_smul, e2]
  let V : Subrepresentation σ := ⟨Submodule.span ℂ P, fun p x hx => by
    have hle : Submodule.span ℂ P ≤ (Submodule.span ℂ P).comap (σ p) :=
      Submodule.span_le.2 (fun y hy => Submodule.mem_comap.2 (Submodule.subset_span (hinv p y hy)))
    exact hle hx⟩
  haveI := hirr
  rcases eq_bot_or_eq_top V with hV | hV
  · right
    intro h hh w
    have hm : σ (h, 1) w - χ h • w ∈ V :=
      (show _ ∈ Submodule.span ℂ P from Submodule.subset_span ⟨h, w, hh, rfl⟩)
    rw [hV] at hm
    have hm' : σ (h, 1) w - χ h • w ∈ (⊥ : Submodule ℂ W) := hm
    exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 hm')
  · left
    intro w
    have hw : w ∈ V := by
      rw [hV]
      exact (Submodule.mem_top : w ∈ (⊤ : Submodule ℂ W))
    have hle : Submodule.span ℂ P ≤ LinearMap.ker Λ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, w', hh, rfl⟩
      simp [LinearMap.mem_ker, hΛ h hh]
    exact hle hw

/- English proof (translation)
Establish `h0 : ValuativeRel.valuation F (uniformizer F : F) ≠ 0` using `(Valuation.ne_zero_iff _).2 (uniformizer_ne_zero F)`. Establish `h1 : ValuativeRel.valuation F (uniformizer F : F) < 1` using `valuation_uniformizer_lt_one F`. Rewrite `ha`, `hb` using `[map_zpow₀]`. Establish `key : ∀ e : ℤ, 0 < e → ValuativeRel.valuation F (uniformizer F : F) ^ e < 1`. Introduce `e he`.

Take `⟨n, rfl⟩` from `Int.eq_ofNat_of_zero_le he.le`. Rewrite using `[zpow_natCast]`. Conclude with `pow_lt_one₀ zero_le' h1 (by omega)`. Establish `prod : ∀ e : ℤ, ValuativeRel.valuation F (uniformizer F : F) ^ e * ValuativeRel.valuation F (uniformizer F : F) ^ (-e) = 1`. Introduce `e`.

Rewrite using `[← zpow_add₀ h0, add_neg_cancel, zpow_zero]`. Assume the negation of the conclusion as `hd`. Break down `lt_or_gt_of_ne hd with h | h` into its components or cases. Establish `h3` using `key (-d) (by omega)`. Establish `h4` using `lt_of_le_of_lt (mul_le_of_le_one_left' ha) h3`.

Rewrite `h4` using `[prod d]`. Conclude with `lt_irrefl _ h4`. Establish `h3` using `key d h`. Establish `h4` using `lt_of_le_of_lt (mul_le_of_le_one_right' hb) h3`. Rewrite `h4` using `[prod d]`.

Conclude with `lt_irrefl _ h4`.
-/
private theorem val_lemma_7 {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (d : ℤ)
    (ha : ValuativeRel.valuation F ((uniformizer F : F) ^ d) ≤ 1)
    (hb : ValuativeRel.valuation F ((uniformizer F : F) ^ (-d)) ≤ 1) : d = 0 := by
  have h0 : ValuativeRel.valuation F (uniformizer F : F) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (uniformizer_ne_zero F)
  have h1 : ValuativeRel.valuation F (uniformizer F : F) < 1 := valuation_uniformizer_lt_one F
  rw [map_zpow₀] at ha hb
  have key : ∀ e : ℤ, 0 < e → ValuativeRel.valuation F (uniformizer F : F) ^ e < 1 := by
    intro e he
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le he.le
    rw [zpow_natCast]
    exact pow_lt_one₀ zero_le' h1 (by omega)
  have prod : ∀ e : ℤ, ValuativeRel.valuation F (uniformizer F : F) ^ e *
      ValuativeRel.valuation F (uniformizer F : F) ^ (-e) = 1 := by
    intro e
    rw [← zpow_add₀ h0, add_neg_cancel, zpow_zero]
  by_contra hd
  rcases lt_or_gt_of_ne hd with h | h
  · have h3 := key (-d) (by omega)
    have h4 := lt_of_le_of_lt (mul_le_of_le_one_left' ha) h3
    rw [prod d] at h4
    exact lt_irrefl _ h4
  · have h3 := key d h
    have h4 := lt_of_le_of_lt (mul_le_of_le_one_right' hb) h3
    rw [prod d] at h4
    exact lt_irrefl _ h4

/- English proof (translation)
Take `⟨g', rfl⟩` from `hg`. Establish `e : ((integralGLHom F n g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = (((g' : Matrix (Fin n) (Fin n) (ValuativeRel.valuation F).integer) i j : (ValuativeRel.valuation F).integer) : F)` using `rfl`. Rewrite using `[e]`. Conclude with `(Valuation.mem_integer_iff _ _).1 ((g' : Matrix (Fin n) (Fin n) (ValuativeRel.valuation F).integer) i j).2`.
-/
private theorem valuation_entry_le_one_of_mem_integralGL {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} (g : GL (Fin n) F) (hg : g ∈ integralGL F n)
    (i j : Fin n) : ValuativeRel.valuation F ((g : Matrix (Fin n) (Fin n) F) i j) ≤ 1 := by
  obtain ⟨g', rfl⟩ := hg
  have e : ((integralGLHom F n g' : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j =
      (((g' : Matrix (Fin n) (Fin n) (ValuativeRel.valuation F).integer) i j :
        (ValuativeRel.valuation F).integer) : F) := rfl
  rw [e]
  exact (Valuation.mem_integer_iff _ _).1
    ((g' : Matrix (Fin n) (Fin n) (ValuativeRel.valuation F).integer) i j).2

/- English proof (translation)
Take `⟨t, ht⟩` from `hT.elim_finite_subcover (fun a : GL (Fin m) F => (fun y => a * y) '' ((integralGL F m : Subgroup _) : Set (GL (Fin m) F))) (fun a => isOpenMap_mul_left a _ (isOpen_integralGL F m)) (fun g _ => Set.mem_iUnion.2 ⟨g, ⟨1, (integralGL F m).one_mem, mul_one g⟩⟩)`. Set `i0 : Fin m` to `⟨0, by omega⟩`. Set `i1 : Fin m` to `⟨1, by omega⟩`. Establish `hi : i1 ≠ i0` using `by simp [i0, i1, Fin.ext_iff]`. Set `e : ℕ → Fin m → ℤ` to `fun n => Pi.single i0 (n : ℤ) - Pi.single i1 (n : ℤ)`.

Set `a : ℕ → GL (Fin m) F` to `fun n => Cartan.diagPow F m (e n)`. Establish `ha0 : ∀ n, ordDet (a n) = 0`. Introduce `n`. Simplify using `[a, e, ordDet_diagPow, Finset.sum_sub_distrib]`. Establish `hcov : ∀ n, ∃ b ∈ t, a n ∈ (fun y => b * y) '' ((integralGL F m : Subgroup _) : Set (GL (Fin m) F))`.

Introduce `n`. Take `⟨b, hbt, hb⟩` from `Set.mem_iUnion₂.1 (ht (hsub _ (ha0 n)))`. Conclude with `⟨b, hbt, hb⟩`. Use `choose b hbt hb using hcov`. Take `⟨n1, n2, hne, h12⟩` from `Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨b n, hbt n⟩ : t))`.

Establish `hb12 : b n1 = b n2` using `congrArg Subtype.val h12`. Take `⟨k1, hk1, e1⟩` from `hb n1`. Take `⟨k2, hk2, e2⟩` from `hb n2`. Establish `hmem : (a n1)⁻¹ * a n2 ∈ integralGL F m`. Rewrite using `[← e1, ← e2, hb12, mul_inv_rev, mul_assoc, inv_mul_cancel_left]`.

Conclude with `(integralGL F m).mul_mem ((integralGL F m).inv_mem hk1) hk2`. Establish `hmem' : (a n2)⁻¹ * a n1 ∈ integralGL F m`. Use `(integralGL F m).inv_mem hmem` as an intermediate fact. Simplify `this` using `[mul_inv_rev]`. Establish `hϖ : (uniformizer F : F) ≠ 0` using `uniformizer_ne_zero F`.

Apply the tactic sequence `have entry : ∀ p q : ℕ, (((a p)⁻¹ * a q : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i0 i0 = (uniformizer F : F) ^ ((q : ℤ) - p) := by`. Introduce `p q`. Rewrite using `[Units.val_mul]`. Establish `hinv : (((a p)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal fun i => (uniformizer F : F) ^ (-(e p i))` using `rfl`. Rewrite using `[hinv, show ((a q : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal fun i => (uniformizer F : F) ^ (e q i) from Cartan.coe_diagPow F m (e q), Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, ← zpow_add₀ hϖ]`.

Use `congr 1`. Simplify using `only [e, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hi.symm]`. Expand and normalize the polynomial expressions, which then agree. Establish `v1` using `valuation_entry_le_one_of_mem_integralGL _ hmem i0 i0`. Establish `v2` using `valuation_entry_le_one_of_mem_integralGL _ hmem' i0 i0`.

Rewrite `v1`, `v2` using `[entry]`. Use `val_lemma_7 ((n2 : ℤ) - n1) v1 (by rw [neg_sub]; exact v2)` as an intermediate fact. Conclude with `hne (by omega)`.
-/
private theorem not_ordDet_eq_zero_subset_compact_of_two_le {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {m : ℕ} (hm : 2 ≤ m) (T : Set (GL (Fin m) F))
    (hT : IsCompact T) (hsub : ∀ g : GL (Fin m) F, ordDet g = 0 → g ∈ T) : False := by
  classical
  obtain ⟨t, ht⟩ := hT.elim_finite_subcover
    (fun a : GL (Fin m) F => (fun y => a * y) '' ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)))
    (fun a => isOpenMap_mul_left a _ (isOpen_integralGL F m))
    (fun g _ => Set.mem_iUnion.2 ⟨g, ⟨1, (integralGL F m).one_mem, mul_one g⟩⟩)
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have hi : i1 ≠ i0 := by simp [i0, i1, Fin.ext_iff]
  let e : ℕ → Fin m → ℤ := fun n => Pi.single i0 (n : ℤ) - Pi.single i1 (n : ℤ)
  let a : ℕ → GL (Fin m) F := fun n => Cartan.diagPow F m (e n)
  have ha0 : ∀ n, ordDet (a n) = 0 := by
    intro n
    simp [a, e, ordDet_diagPow, Finset.sum_sub_distrib]
  have hcov : ∀ n, ∃ b ∈ t, a n ∈ (fun y => b * y) '' ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)) := by
    intro n
    obtain ⟨b, hbt, hb⟩ := Set.mem_iUnion₂.1 (ht (hsub _ (ha0 n)))
    exact ⟨b, hbt, hb⟩
  choose b hbt hb using hcov
  obtain ⟨n1, n2, hne, h12⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => (⟨b n, hbt n⟩ : t))
  have hb12 : b n1 = b n2 := congrArg Subtype.val h12
  obtain ⟨k1, hk1, e1⟩ := hb n1
  obtain ⟨k2, hk2, e2⟩ := hb n2
  have hmem : (a n1)⁻¹ * a n2 ∈ integralGL F m := by
    rw [← e1, ← e2, hb12, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    exact (integralGL F m).mul_mem ((integralGL F m).inv_mem hk1) hk2
  have hmem' : (a n2)⁻¹ * a n1 ∈ integralGL F m := by
    have := (integralGL F m).inv_mem hmem
    simpa [mul_inv_rev] using this
  have hϖ : (uniformizer F : F) ≠ 0 := uniformizer_ne_zero F
  have entry : ∀ p q : ℕ, (((a p)⁻¹ * a q : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) i0 i0 =
      (uniformizer F : F) ^ ((q : ℤ) - p) := by
    intro p q
    rw [Units.val_mul]
    have hinv : (((a p)⁻¹ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        Matrix.diagonal fun i => (uniformizer F : F) ^ (-(e p i)) := rfl
    rw [hinv, show ((a q : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
        Matrix.diagonal fun i => (uniformizer F : F) ^ (e q i) from Cartan.coe_diagPow F m (e q),
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, ← zpow_add₀ hϖ]
    congr 1
    simp only [e, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hi.symm]
    ring
  have v1 := valuation_entry_le_one_of_mem_integralGL _ hmem i0 i0
  have v2 := valuation_entry_le_one_of_mem_integralGL _ hmem' i0 i0
  rw [entry] at v1 v2
  have := val_lemma_7 ((n2 : ℤ) - n1) v1 (by rw [neg_sub]; exact v2)
  exact hne (by omega)

/- English proof (translation)
Introduce `g0 hg0`. Assume the negation of the conclusion as `hne`. Use `not_ordDet_eq_zero_subset_compact_of_two_le hm ((fun y => y * g0⁻¹) '' T) (hT.image (continuous_mul_right g0⁻¹)) ?_` and prove the remaining obligations. Introduce `h hh`. Conclude with `⟨h * g0, hTφ _ (by rw [ordDet_mul, hh, hg0, zero_add]) (hinv h g0 hh hne), by simp⟩`.
-/
private theorem eq_zero_of_ordDet_eq_of_compact_support_of_mul_ne_zero {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {m : ℕ} (hm : 2 ≤ m) (φ : GL (Fin m) F → ℂ) (k : ℤ)
    (T : Set (GL (Fin m) F)) (hT : IsCompact T)
    (hTφ : ∀ g, ordDet g = k → φ g ≠ 0 → g ∈ T)
    (hinv : ∀ h g, ordDet h = 0 → φ g ≠ 0 → φ (h * g) ≠ 0) :
    ∀ g, ordDet g = k → φ g = 0 := by
  intro g0 hg0
  by_contra hne
  refine not_ordDet_eq_zero_subset_compact_of_two_le hm ((fun y => y * g0⁻¹) '' T) (hT.image (continuous_mul_right g0⁻¹)) ?_
  intro h hh
  exact ⟨h * g0, hTφ _ (by rw [ordDet_mul, hh, hg0, zero_add]) (hinv h g0 hh hne), by simp⟩

/- English proof (translation)
Establish `hfin : (ordDet '' C).Finite` using `(hC.image continuous_ordDet).finite_of_discrete`. Establish `hm : (m : ℤ) ≠ 0` using `by exact_mod_cast NeZero.ne m`. Establish `hJ : ((fun j : ℤ => j * (m : ℤ) + k) ⁻¹' (ordDet '' C)).Finite` using `hfin.preimage (fun a _ b _ hab => mul_right_cancel₀ hm (add_right_cancel hab))`. Use `⟨⋃ j ∈ (fun j : ℤ => j * (m : ℤ) + k) ⁻¹' (ordDet '' C), (fun y => (centralUnif F m ^ j)⁻¹ * y) '' C, hJ.isCompact_biUnion (fun j _ => hC.image (continuous_mul_left _)), ?_⟩` and prove the remaining obligations. Introduce and unpack `g hg ⟨j, hj⟩`.

Use `Set.mem_iUnion₂.2 ⟨j, ?_, ⟨_, hj, by simp⟩⟩` and prove the remaining obligations. Conclude with `⟨_, hj, by rw [ordDet_mul, ordDet_zpow', ordDet_centralUnif, hg]⟩`.
-/
private theorem exists_isCompact_ordDet_eq_centralUnif_zpow_mul_mem {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {m : ℕ} [NeZero m] (C : Set (GL (Fin m) F))
    (hC : IsCompact C) (k : ℤ) : ∃ T : Set (GL (Fin m) F), IsCompact T ∧
      ∀ g, ordDet g = k → (∃ j : ℤ, centralUnif F m ^ j * g ∈ C) → g ∈ T := by
  have hfin : (ordDet '' C).Finite := (hC.image continuous_ordDet).finite_of_discrete
  have hm : (m : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hJ : ((fun j : ℤ => j * (m : ℤ) + k) ⁻¹' (ordDet '' C)).Finite :=
    hfin.preimage (fun a _ b _ hab => mul_right_cancel₀ hm (add_right_cancel hab))
  refine ⟨⋃ j ∈ (fun j : ℤ => j * (m : ℤ) + k) ⁻¹' (ordDet '' C),
    (fun y => (centralUnif F m ^ j)⁻¹ * y) '' C,
    hJ.isCompact_biUnion (fun j _ => hC.image (continuous_mul_left _)), ?_⟩
  rintro g hg ⟨j, hj⟩
  refine Set.mem_iUnion₂.2 ⟨j, ?_, ⟨_, hj, by simp⟩⟩
  exact ⟨_, hj, by rw [ordDet_mul, ordDet_zpow', ordDet_centralUnif, hg]⟩

/- English proof (translation)
The claim follows from `(ContinuousOn.integrableOn_compact hT hφ.continuousOn).of_forall_diff_eq_zero hS (fun x hx => by by_contra hne exact hx.2 (h x hx.1 hne))`.
-/
private theorem integrableOn_of_continuous_of_support_inter_subset_compact {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [T2Space X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    (φ : X → ℂ) (hφ : Continuous φ) (S T : Set X) (hS : MeasurableSet S) (hT : IsCompact T)
    (h : ∀ x ∈ S, φ x ≠ 0 → x ∈ T) : IntegrableOn φ S μ :=
  (ContinuousOn.integrableOn_compact hT hφ.continuousOn).of_forall_diff_eq_zero hS
    (fun x hx => by
      by_contra hne
      exact hx.2 (h x hx.1 hne))

/- English proof (translation)
Set `K : Subgroup (GL (Fin m) F)` to `(stabilizerOf σ w).comap (MonoidHom.inl (GL (Fin m) F) H)`. Establish `hK : IsOpen (K : Set (GL (Fin m) F))` using `(hs w).preimage (continuous_id.prodMk continuous_const)`. Use `lc_lemma K hK _ (fun x y hy => ?_)` and prove the remaining obligations. Establish `hy' : σ (y, 1) w = w` using `hy`. Establish `e : ((x * y, (1 : H)) : GL (Fin m) F × H) = (x, 1) * (y, 1)` using `by simp`.

Use `show ℓ (σ (x * y, 1) w) = ℓ (σ (x, 1) w)`. Rewrite using `[e, map_mul, Module.End.mul_apply, hy']`.
-/
private theorem continuous_matrix_coeff_left_factor_of_isSmooth {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {m : ℕ} {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GL (Fin m) F × H) W) (hs : IsSmooth σ) (ℓ : Module.Dual ℂ W)
    (w : W) : Continuous (fun g : GL (Fin m) F => ℓ (σ (g, 1) w)) := by
  let K : Subgroup (GL (Fin m) F) := (stabilizerOf σ w).comap (MonoidHom.inl (GL (Fin m) F) H)
  have hK : IsOpen (K : Set (GL (Fin m) F)) :=
    (hs w).preimage (continuous_id.prodMk continuous_const)
  refine lc_lemma K hK _ (fun x y hy => ?_)
  have hy' : σ (y, 1) w = w := hy
  have e : ((x * y, (1 : H)) : GL (Fin m) F × H) = (x, 1) * (y, 1) := by simp
  show ℓ (σ (x * y, 1) w) = ℓ (σ (x, 1) w)
  rw [e, map_mul, Module.End.mul_apply, hy']

/- English proof (translation)
Introduce `F _ _ _ _ m _ _ _ μ _ H _ _ _ _ _ _ _ W _ _ σ hadm hirr α hα hcen hcpt hnot v ℓ hℓ k`. Establish `hs : IsSmooth σ` using `hadm.1`. Establish `hSm : MeasurableSet {g : GL (Fin m) F | ordDet g = k}` using `((continuous_discrete_rng.1 (continuous_ordDet (F := F) (n := m))) k).measurableSet`. Establish `hmc : ∀ w, Continuous (fun g : GL (Fin m) F => ℓ (σ (g, 1) w))` using `fun w => continuous_matrix_coeff_left_factor_of_isSmooth σ hs ℓ w`. Establish `hT1 : ∀ w, ∃ T : Set (GL (Fin m) F), IsCompact T ∧ ∀ g, ordDet g = k → ℓ (σ (g, 1) w) ≠ 0 → g ∈ T`.

Introduce `w`. Take `⟨C, hC, hCw⟩` from `hcpt w ℓ hℓ`. Take `⟨T, hT, hTC⟩` from `exists_isCompact_ordDet_eq_centralUnif_zpow_mul_mem C hC k`. Conclude with `⟨T, hT, fun g hg hne => hTC g hg (hCw g hne)⟩`. Establish `hT2 : ∀ w, ∃ T : Set (GL (Fin m) F), IsCompact T ∧ ∀ g, ordDet g = k → ℓ (σ (g⁻¹, 1) w) ≠ 0 → g ∈ T`.

Introduce `w`. Take `⟨C, hC, hCw⟩` from `hcpt w ℓ hℓ`. Take `⟨T, hT, hTC⟩` from `exists_isCompact_ordDet_eq_centralUnif_zpow_mul_mem C hC (-k)`. Use `⟨T⁻¹, hT.inv, fun g hg hne => ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_inv.2 (hTC g⁻¹ (by rw [ordDet_inv, hg]) (hCw g⁻¹ hne))`.

Establish `hint1 : ∀ w, IntegrableOn (fun g : GL (Fin m) F => ℓ (σ (g, 1) w)) {g | ordDet g = k} μ`. Introduce `w`. Take `⟨T, hT, hTw⟩` from `hT1 w`. Conclude with `integrableOn_of_continuous_of_support_inter_subset_compact μ _ (hmc w) _ T hSm hT hTw`. Establish `hint2 : ∀ w, IntegrableOn (fun g : GL (Fin m) F => ℓ (σ (g⁻¹, 1) w)) {g | ordDet g = k} μ`.

Introduce `w`. Take `⟨T, hT, hTw⟩` from `hT2 w`. Conclude with `integrableOn_of_continuous_of_support_inter_subset_compact μ _ ((hmc w).comp continuous_inv) _ T hSm hT hTw`. Set `Λ1 : Module.Dual ℂ W` to `UpperTheory.V.Z.Gam.shellForm μ σ ℓ k hint1`. Set `Λ2 : Module.Dual ℂ W` to `{ toFun := fun w => ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g⁻¹, 1) w) ∂μ map_add' := fun a b => by`.

Simplify using `only [map_add]`. Conclude with `integral_add (hint2 a) (hint2 b)`. Use the proof step `map_smul' := fun c w => by`. Simplify using `only [map_smul, smul_eq_mul, RingHom.id_apply]`. Conclude with `integral_const_mul _ _ }`.

Set `c : GL (Fin m) F → ℂ` to `fun h => ((Measure.modularCharacterFun h : ℝ) : ℂ)`. Establish `hcne : ∀ h, c h ≠ 0`. Introduce `h`. Use `show ((Measure.modularCharacterFun h : ℝ) : ℂ) ≠ 0`. Conclude with `(Measure.modularCharacterFun_pos h).ne'` after adjusting the coercions.

Establish `hcconj : ∀ g h, c (g * h * g⁻¹) = c h`. Introduce `g h`. Establish `e : Measure.modularCharacterFun (g * h * g⁻¹) = Measure.modularCharacterFun h`. Rewrite using `[Measure.modularCharacterFun_map_mul, Measure.modularCharacterFun_map_mul, mul_right_comm, ← Measure.modularCharacterFun_map_mul, mul_inv_cancel, Measure.modularCharacterFun_map_one, one_mul]`. Use `show ((Measure.modularCharacterFun (g * h * g⁻¹) : ℝ) : ℂ) = ((Measure.modularCharacterFun h : ℝ) : ℂ)`.

Rewrite using `[e]`. Establish `hc1 : ∀ g ∈ integralGL F m, Measure.modularCharacterFun g = 1`. Introduce `g hg`. Establish `hK : MeasurableSet ((integralGL F m : Subgroup _) : Set (GL (Fin m) F))` using `(isOpen_integralGL F m).measurableSet`. Establish `e1` using `congrArg (fun ν : Measure (GL (Fin m) F) => ν ((integralGL F m : Subgroup _) : Set (GL (Fin m) F))) (Measure.map_right_mul_eq_modularCharacterFun_smul μ g)`.

Establish `hpre : (fun x : GL (Fin m) F => x * g) ⁻¹' ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)) = ((integralGL F m : Subgroup _) : Set (GL (Fin m) F))`. Use extensionality with `x`. Conclude with `Subgroup.mul_mem_cancel_right _ hg`. Rewrite `e1` using `[Measure.map_apply (measurable_mul_const g) hK, hpre, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Establish `h0 : μ ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)) ≠ 0` using `(isOpen_integralGL F m).measure_ne_zero μ ⟨1, (integralGL F m).one_mem⟩`.

Establish `htop : μ ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)) ≠ ⊤` using `(isCompact_integralGL F m).measure_lt_top.ne`. Establish `e2` using `(ENNReal.mul_eq_right h0 htop).1 e1.symm`. Conclude with `e2` after adjusting the coercions. Establish `hΛ1 : ∀ h, ordDet h = 0 → ∀ w, Λ1 (σ (h, 1) w) = c h * Λ1 w`. Introduce `h hh w`.

Establish `hpre : (MeasurableEquiv.mulRight h) ⁻¹' {g : GL (Fin m) F | ordDet g = k} = {g | ordDet g = k}`. Use extensionality with `x`. Simplify using `[MeasurableEquiv.coe_mulRight, ordDet_mul, hh]`. Establish `hmap : Measure.map (MeasurableEquiv.mulRight h) μ = Measure.modularCharacterFun h • μ`. Rewrite using `[MeasurableEquiv.coe_mulRight]`.

Conclude with `Measure.map_right_mul_eq_modularCharacterFun_smul μ h`. Use `show ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g, 1) (σ (h, 1) w)) ∂μ = c h * ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g, 1) w) ∂μ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hpre]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Rewrite using `[MeasurableEquiv.coe_mulRight]`. Use `show ℓ (σ (g, 1) (σ (h, 1) w)) = ℓ (σ (g * h, 1) w)`. Rewrite using `[← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]`. Use `_ = ∫ y in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (y, 1) w) ∂(Measure.map (MeasurableEquiv.mulRight h) μ) := (setIntegral_map_equiv (MeasurableEquiv.mulRight h) (fun y : GL (Fin m) F => ℓ (σ (y, 1) w)) {g | ordDet g = k}).symm`.

Use `_ = c h * ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g, 1) w) ∂μ := by`. Rewrite using `[hmap, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`. Establish `hΛ2 : ∀ h, ordDet h = 0 → ∀ w, Λ2 (σ (h, 1) w) = (fun _ : GL (Fin m) F => (1 : ℂ)) h * Λ2 w`. Introduce `h hh w`. Establish `hpre : (MeasurableEquiv.mulLeft h⁻¹) ⁻¹' {g : GL (Fin m) F | ordDet g = k} = {g | ordDet g = k}`.

Use extensionality with `x`. Simplify using `[MeasurableEquiv.coe_mulLeft, ordDet_mul, ordDet_inv, hh]`. Establish `hmap : Measure.map (MeasurableEquiv.mulLeft h⁻¹) μ = μ`. Rewrite using `[MeasurableEquiv.coe_mulLeft]`. Conclude with `map_mul_left_eq_self μ h⁻¹`.

Use `show ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g⁻¹, 1) (σ (h, 1) w)) ∂μ = 1 * ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g⁻¹, 1) w) ∂μ`. Rewrite using `[one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hpre]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Rewrite using `[MeasurableEquiv.coe_mulLeft]`. Use `show ℓ (σ (g⁻¹, 1) (σ (h, 1) w)) = ℓ (σ ((h⁻¹ * g)⁻¹, 1) w)`. Rewrite using `[mul_inv_rev, inv_inv, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]`. Use `_ = ∫ y in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (y⁻¹, 1) w) ∂(Measure.map (MeasurableEquiv.mulLeft h⁻¹) μ) := (setIntegral_map_equiv (MeasurableEquiv.mulLeft h⁻¹) (fun y : GL (Fin m) F => ℓ (σ (y⁻¹, 1) w)) {g | ordDet g = k}).symm`.

Use `_ = ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g⁻¹, 1) w) ∂μ := by`. Rewrite using `[hmap]`. Break down `dual_eq_zero_or_smul_of_irreducible_of_conj_invariant σ hirr (fun _ => (1 : ℂ)) (fun _ _ => rfl) Λ2 hΛ2 with hA1 | hB1` into its components or cases. Use `⟨?_, hA1 v⟩` and prove the remaining obligations. Break down `dual_eq_zero_or_smul_of_irreducible_of_conj_invariant σ hirr c hcconj Λ1 hΛ1 with hA2 | hB2` into its components or cases.

Conclude with `hA2 v`. Distinguish the cases in `hm1 : m = 1`. It suffices to derive a contradiction. Apply `hnot` to reduce the goal to its premises. Use `⟨hm1, fun g hg => ?_⟩` and prove the remaining obligations.

Use extensionality with `w`. Rewrite using `[hB2 g (ordDet_eq_zero_of_mem_integralGL hg) w]`. Simplify using `[c, hc1 g hg]`. Establish `hm2 : 2 ≤ m`. Use `NeZero.ne m` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Take `⟨T, hT, hTw⟩` from `hT1 v`. Use `setIntegral_eq_zero_of_forall_eq_zero (fun g hg => eq_zero_of_ordDet_eq_of_compact_support_of_mul_ne_zero hm2 (fun g => ℓ (σ (g, 1) v)) k T hT hTw ?_ g hg)` and prove the remaining obligations. Introduce `h g hh hne`. Use `show ℓ (σ (h * g, 1) v) ≠ 0`.

Rewrite using `[show ((h * g, (1 : H)) : GL (Fin m) F × H) = (h, 1) * (g, 1) by simp, map_mul, Module.End.mul_apply, hB2 h hh, map_smul, smul_eq_mul]`. Conclude with `mul_ne_zero (hcne h) hne`. Distinguish the cases in `hm1 : m = 1`. It suffices to derive a contradiction. Apply `hnot` to reduce the goal to its premises.

Use `⟨hm1, fun g hg => ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Rewrite using `[hB1 g (ordDet_eq_zero_of_mem_integralGL hg) w]`. Simplify using the standard rewrite rules. Establish `hm2 : 2 ≤ m`.

Use `NeZero.ne m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨T1, hT1c, hT1w⟩` from `hT1 v`. Take `⟨T2, hT2c, hT2w⟩` from `hT2 v`. Use `⟨setIntegral_eq_zero_of_forall_eq_zero (fun g hg => eq_zero_of_ordDet_eq_of_compact_support_of_mul_ne_zero hm2 (fun g => ℓ (σ (g, 1) v)) k T1 hT1c hT1w ?_ g hg), setIntegral_eq_zero_of_forall_eq_zero (fun g hg => eq_zero_of_ordDet_eq_of_compact_support_of_mul_ne_zero hm2 (fun g = …` and prove the remaining obligations.

Introduce `h g hh hne show ℓ (σ (h * g, 1) v) ≠ 0`. Rewrite using `[show ((h * g, (1 : H)) : GL (Fin m) F × H) = (h, 1) * (g, 1) by simp, map_mul, Module.End.mul_apply, hB1 h hh]`. Simplify using `using hne`. Introduce `h g hh hne show ℓ (σ ((h * g)⁻¹, 1) v) ≠ 0`. Rewrite using `[mul_inv_rev, show ((g⁻¹ * h⁻¹, (1 : H)) : GL (Fin m) F × H) = (g⁻¹, 1) * (h⁻¹, 1) by simp, map_mul, Module.End.mul_apply, hB1 h⁻¹ (by rw [ordDet_inv, hh, neg_zero]) v]`.

Simplify using `using hne`.
-/
theorem UpperTheory.local_zeta_integral_shell_mean :
    UpperTheory.V.Z.Gam.LdMean := by
  intro F _ _ _ _ m _ _ _ μ _ H _ _ _ _ _ _ _ W _ _ σ hadm hirr α hα hcen hcpt hnot v ℓ hℓ k
  classical
  have hs : IsSmooth σ := hadm.1
  have hSm : MeasurableSet {g : GL (Fin m) F | ordDet g = k} :=
    ((continuous_discrete_rng.1 (continuous_ordDet (F := F) (n := m))) k).measurableSet
  have hmc : ∀ w, Continuous (fun g : GL (Fin m) F => ℓ (σ (g, 1) w)) :=
    fun w => continuous_matrix_coeff_left_factor_of_isSmooth σ hs ℓ w
  have hT1 : ∀ w, ∃ T : Set (GL (Fin m) F), IsCompact T ∧
      ∀ g, ordDet g = k → ℓ (σ (g, 1) w) ≠ 0 → g ∈ T := by
    intro w
    obtain ⟨C, hC, hCw⟩ := hcpt w ℓ hℓ
    obtain ⟨T, hT, hTC⟩ := exists_isCompact_ordDet_eq_centralUnif_zpow_mul_mem C hC k
    exact ⟨T, hT, fun g hg hne => hTC g hg (hCw g hne)⟩
  have hT2 : ∀ w, ∃ T : Set (GL (Fin m) F), IsCompact T ∧
      ∀ g, ordDet g = k → ℓ (σ (g⁻¹, 1) w) ≠ 0 → g ∈ T := by
    intro w
    obtain ⟨C, hC, hCw⟩ := hcpt w ℓ hℓ
    obtain ⟨T, hT, hTC⟩ := exists_isCompact_ordDet_eq_centralUnif_zpow_mul_mem C hC (-k)
    refine ⟨T⁻¹, hT.inv, fun g hg hne => ?_⟩
    exact Set.mem_inv.2 (hTC g⁻¹ (by rw [ordDet_inv, hg]) (hCw g⁻¹ hne))
  have hint1 : ∀ w, IntegrableOn (fun g : GL (Fin m) F => ℓ (σ (g, 1) w))
      {g | ordDet g = k} μ := by
    intro w
    obtain ⟨T, hT, hTw⟩ := hT1 w
    exact integrableOn_of_continuous_of_support_inter_subset_compact μ _ (hmc w) _ T hSm hT hTw
  have hint2 : ∀ w, IntegrableOn (fun g : GL (Fin m) F => ℓ (σ (g⁻¹, 1) w))
      {g | ordDet g = k} μ := by
    intro w
    obtain ⟨T, hT, hTw⟩ := hT2 w
    exact integrableOn_of_continuous_of_support_inter_subset_compact μ _ ((hmc w).comp continuous_inv) _ T hSm hT hTw
  let Λ1 : Module.Dual ℂ W := UpperTheory.V.Z.Gam.shellForm μ σ ℓ k hint1
  let Λ2 : Module.Dual ℂ W :=
    { toFun := fun w => ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g⁻¹, 1) w) ∂μ
      map_add' := fun a b => by
        simp only [map_add]
        exact integral_add (hint2 a) (hint2 b)
      map_smul' := fun c w => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact integral_const_mul _ _ }
  let c : GL (Fin m) F → ℂ := fun h => ((Measure.modularCharacterFun h : ℝ) : ℂ)
  have hcne : ∀ h, c h ≠ 0 := by
    intro h
    show ((Measure.modularCharacterFun h : ℝ) : ℂ) ≠ 0
    exact_mod_cast (Measure.modularCharacterFun_pos h).ne'
  have hcconj : ∀ g h, c (g * h * g⁻¹) = c h := by
    intro g h
    have e : Measure.modularCharacterFun (g * h * g⁻¹) = Measure.modularCharacterFun h := by
      rw [Measure.modularCharacterFun_map_mul, Measure.modularCharacterFun_map_mul,
        mul_right_comm, ← Measure.modularCharacterFun_map_mul, mul_inv_cancel,
        Measure.modularCharacterFun_map_one, one_mul]
    show ((Measure.modularCharacterFun (g * h * g⁻¹) : ℝ) : ℂ) =
      ((Measure.modularCharacterFun h : ℝ) : ℂ)
    rw [e]
  have hc1 : ∀ g ∈ integralGL F m, Measure.modularCharacterFun g = 1 := by
    intro g hg
    have hK : MeasurableSet ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)) :=
      (isOpen_integralGL F m).measurableSet
    have e1 := congrArg (fun ν : Measure (GL (Fin m) F) =>
      ν ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)))
      (Measure.map_right_mul_eq_modularCharacterFun_smul μ g)
    have hpre : (fun x : GL (Fin m) F => x * g) ⁻¹'
        ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)) =
        ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)) := by
      ext x
      exact Subgroup.mul_mem_cancel_right _ hg
    rw [Measure.map_apply (measurable_mul_const g) hK, hpre, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at e1
    have h0 : μ ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)) ≠ 0 :=
      (isOpen_integralGL F m).measure_ne_zero μ ⟨1, (integralGL F m).one_mem⟩
    have htop : μ ((integralGL F m : Subgroup _) : Set (GL (Fin m) F)) ≠ ⊤ :=
      (isCompact_integralGL F m).measure_lt_top.ne
    have e2 := (ENNReal.mul_eq_right h0 htop).1 e1.symm
    exact_mod_cast e2
  have hΛ1 : ∀ h, ordDet h = 0 → ∀ w, Λ1 (σ (h, 1) w) = c h * Λ1 w := by
    intro h hh w
    have hpre : (MeasurableEquiv.mulRight h) ⁻¹' {g : GL (Fin m) F | ordDet g = k} =
        {g | ordDet g = k} := by
      ext x
      simp [MeasurableEquiv.coe_mulRight, ordDet_mul, hh]
    have hmap : Measure.map (MeasurableEquiv.mulRight h) μ =
        Measure.modularCharacterFun h • μ := by
      rw [MeasurableEquiv.coe_mulRight]
      exact Measure.map_right_mul_eq_modularCharacterFun_smul μ h
    show ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g, 1) (σ (h, 1) w)) ∂μ =
      c h * ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g, 1) w) ∂μ
    calc ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g, 1) (σ (h, 1) w)) ∂μ
        = ∫ g in (MeasurableEquiv.mulRight h) ⁻¹' {g : GL (Fin m) F | ordDet g = k},
            (fun y : GL (Fin m) F => ℓ (σ (y, 1) w)) (MeasurableEquiv.mulRight h g) ∂μ := by
          rw [hpre]
          congr 1
          funext g
          rw [MeasurableEquiv.coe_mulRight]
          show ℓ (σ (g, 1) (σ (h, 1) w)) = ℓ (σ (g * h, 1) w)
          rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
      _ = ∫ y in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (y, 1) w)
            ∂(Measure.map (MeasurableEquiv.mulRight h) μ) :=
          (setIntegral_map_equiv (MeasurableEquiv.mulRight h)
            (fun y : GL (Fin m) F => ℓ (σ (y, 1) w)) {g | ordDet g = k}).symm
      _ = c h * ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g, 1) w) ∂μ := by
          rw [hmap, Measure.restrict_smul, integral_smul_nnreal_measure, NNReal.smul_def,
            Complex.real_smul]
  have hΛ2 : ∀ h, ordDet h = 0 → ∀ w,
      Λ2 (σ (h, 1) w) = (fun _ : GL (Fin m) F => (1 : ℂ)) h * Λ2 w := by
    intro h hh w
    have hpre : (MeasurableEquiv.mulLeft h⁻¹) ⁻¹' {g : GL (Fin m) F | ordDet g = k} =
        {g | ordDet g = k} := by
      ext x
      simp [MeasurableEquiv.coe_mulLeft, ordDet_mul, ordDet_inv, hh]
    have hmap : Measure.map (MeasurableEquiv.mulLeft h⁻¹) μ = μ := by
      rw [MeasurableEquiv.coe_mulLeft]
      exact map_mul_left_eq_self μ h⁻¹
    show ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g⁻¹, 1) (σ (h, 1) w)) ∂μ =
      1 * ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g⁻¹, 1) w) ∂μ
    rw [one_mul]
    calc ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g⁻¹, 1) (σ (h, 1) w)) ∂μ
        = ∫ g in (MeasurableEquiv.mulLeft h⁻¹) ⁻¹' {g : GL (Fin m) F | ordDet g = k},
            (fun y : GL (Fin m) F => ℓ (σ (y⁻¹, 1) w)) (MeasurableEquiv.mulLeft h⁻¹ g) ∂μ := by
          rw [hpre]
          congr 1
          funext g
          rw [MeasurableEquiv.coe_mulLeft]
          show ℓ (σ (g⁻¹, 1) (σ (h, 1) w)) = ℓ (σ ((h⁻¹ * g)⁻¹, 1) w)
          rw [mul_inv_rev, inv_inv, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
      _ = ∫ y in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (y⁻¹, 1) w)
            ∂(Measure.map (MeasurableEquiv.mulLeft h⁻¹) μ) :=
          (setIntegral_map_equiv (MeasurableEquiv.mulLeft h⁻¹)
            (fun y : GL (Fin m) F => ℓ (σ (y⁻¹, 1) w)) {g | ordDet g = k}).symm
      _ = ∫ g in {g : GL (Fin m) F | ordDet g = k}, ℓ (σ (g⁻¹, 1) w) ∂μ := by
          rw [hmap]
  rcases dual_eq_zero_or_smul_of_irreducible_of_conj_invariant σ hirr (fun _ => (1 : ℂ)) (fun _ _ => rfl) Λ2 hΛ2 with hA1 | hB1
  · refine ⟨?_, hA1 v⟩
    rcases dual_eq_zero_or_smul_of_irreducible_of_conj_invariant σ hirr c hcconj Λ1 hΛ1 with hA2 | hB2
    · exact hA2 v
    · by_cases hm1 : m = 1
      · exfalso
        apply hnot
        refine ⟨hm1, fun g hg => ?_⟩
        ext w
        rw [hB2 g (ordDet_eq_zero_of_mem_integralGL hg) w]
        simp [c, hc1 g hg]
      · have hm2 : 2 ≤ m := by
          have := NeZero.ne m
          omega
        obtain ⟨T, hT, hTw⟩ := hT1 v
        refine setIntegral_eq_zero_of_forall_eq_zero (fun g hg =>
          eq_zero_of_ordDet_eq_of_compact_support_of_mul_ne_zero hm2 (fun g => ℓ (σ (g, 1) v)) k T hT hTw ?_ g hg)
        intro h g hh hne
        show ℓ (σ (h * g, 1) v) ≠ 0
        rw [show ((h * g, (1 : H)) : GL (Fin m) F × H) = (h, 1) * (g, 1) by simp, map_mul,
          Module.End.mul_apply, hB2 h hh, map_smul, smul_eq_mul]
        exact mul_ne_zero (hcne h) hne
  · by_cases hm1 : m = 1
    · exfalso
      apply hnot
      refine ⟨hm1, fun g hg => ?_⟩
      ext w
      rw [hB1 g (ordDet_eq_zero_of_mem_integralGL hg) w]
      simp
    · have hm2 : 2 ≤ m := by
        have := NeZero.ne m
        omega
      obtain ⟨T1, hT1c, hT1w⟩ := hT1 v
      obtain ⟨T2, hT2c, hT2w⟩ := hT2 v
      refine ⟨setIntegral_eq_zero_of_forall_eq_zero (fun g hg =>
          eq_zero_of_ordDet_eq_of_compact_support_of_mul_ne_zero hm2 (fun g => ℓ (σ (g, 1) v)) k T1 hT1c hT1w ?_ g hg),
        setIntegral_eq_zero_of_forall_eq_zero (fun g hg =>
          eq_zero_of_ordDet_eq_of_compact_support_of_mul_ne_zero hm2 (fun g => ℓ (σ (g⁻¹, 1) v)) k T2 hT2c hT2w ?_ g hg)⟩
      · intro h g hh hne
        show ℓ (σ (h * g, 1) v) ≠ 0
        rw [show ((h * g, (1 : H)) : GL (Fin m) F × H) = (h, 1) * (g, 1) by simp, map_mul,
          Module.End.mul_apply, hB1 h hh]
        simpa using hne
      · intro h g hh hne
        show ℓ (σ ((h * g)⁻¹, 1) v) ≠ 0
        rw [mul_inv_rev, show ((g⁻¹ * h⁻¹, (1 : H)) : GL (Fin m) F × H) = (g⁻¹, 1) * (h⁻¹, 1) by simp,
          map_mul, Module.End.mul_apply, hB1 h⁻¹ (by rw [ordDet_inv, hh, neg_zero]) v]
        simpa using hne
