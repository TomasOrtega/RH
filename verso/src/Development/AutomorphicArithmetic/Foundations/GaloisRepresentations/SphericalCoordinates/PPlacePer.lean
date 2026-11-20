import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FinrankOfPlace
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

/- English proof (translation)
Use `choose m u hm h using hd`. Establish `key : ∀ w (n : ℕ) (v : M), n ≠ 0 → n • w = j v → ((m w : ℚ)⁻¹) • P (u w) = ((n : ℚ)⁻¹) • P v`. Introduce `w n v hn hv`. Establish `h1 : n • u w = m w • v` using `hj (by`. Rewrite using `[map_nsmul, map_nsmul, ← h w, ← hv, smul_comm])`.

Establish `h2 : n • P (u w) = m w • P v` using `by rw [← map_nsmul, ← map_nsmul, h1]`. Establish `hn' : (n : ℚ) ≠ 0` using `by exact_mod_cast hn`. Establish `hm' : (m w : ℚ) ≠ 0` using `by exact_mod_cast hm w`. Establish `h3 : (n : ℚ) • P (u w) = (m w : ℚ) • P v`. Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h2]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Use `_ = ((n : ℚ)⁻¹) • P v := by rw [h3, smul_smul]; congr 1; field_simp`.

Use `⟨AddMonoidHom.mk' (fun w => ((m w : ℚ)⁻¹) • P (u w)) ?_, ?_⟩` and prove the remaining obligations. Introduce `a b`. Establish `hab : (m a * m b) • (a + b) = j (m b • u a + m a • u b)`. Rewrite using `[map_add, map_nsmul, map_nsmul, ← h a, ← h b, smul_add, mul_smul, mul_smul, smul_comm (m a) (m b) a]`. Establish `hk` using `key (a + b) (m a * m b) _ (mul_ne_zero (hm a) (hm b)) hab`.

Establish `hma : (m a : ℚ) ≠ 0` using `by exact_mod_cast hm a`. Establish `hmb : (m b : ℚ) ≠ 0` using `by exact_mod_cast hm b`. Rewrite using `[hk, map_add, map_nsmul, map_nsmul, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul]`. Use `push_cast`. Apply the tactic sequence `congr 2 <;> field_simp`.

Introduce `v`. Establish `hk` using `key (j v) 1 v one_ne_zero (by simp)`. Simplify using `using hk`.
-/
private theorem exists_extend {M V E : Type} [AddCommGroup M] [AddCommGroup V] [AddCommGroup E] [Module ℚ E]
    (j : M →+ V) (hj : Function.Injective j) (hd : ∀ w, ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • w = j u) (P : M →+ E) :
    ∃ Q : V →+ E, ∀ u, Q (j u) = P u := by
  choose m u hm h using hd
  have key : ∀ w (n : ℕ) (v : M), n ≠ 0 → n • w = j v →
      ((m w : ℚ)⁻¹) • P (u w) = ((n : ℚ)⁻¹) • P v := by
    intro w n v hn hv
    have h1 : n • u w = m w • v := hj (by
      rw [map_nsmul, map_nsmul, ← h w, ← hv, smul_comm])
    have h2 : n • P (u w) = m w • P v := by rw [← map_nsmul, ← map_nsmul, h1]
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    have hm' : (m w : ℚ) ≠ 0 := by exact_mod_cast hm w
    have h3 : (n : ℚ) • P (u w) = (m w : ℚ) • P v := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h2]
    calc ((m w : ℚ)⁻¹) • P (u w) = ((m w : ℚ)⁻¹ * (n : ℚ)⁻¹) • ((n : ℚ) • P (u w)) := by
          rw [smul_smul]; congr 1; field_simp
      _ = ((n : ℚ)⁻¹) • P v := by rw [h3, smul_smul]; congr 1; field_simp
  refine ⟨AddMonoidHom.mk' (fun w => ((m w : ℚ)⁻¹) • P (u w)) ?_, ?_⟩
  · intro a b
    have hab : (m a * m b) • (a + b) = j (m b • u a + m a • u b) := by
      rw [map_add, map_nsmul, map_nsmul, ← h a, ← h b, smul_add, mul_smul, mul_smul,
        smul_comm (m a) (m b) a]
    have hk := key (a + b) (m a * m b) _ (mul_ne_zero (hm a) (hm b)) hab
    have hma : (m a : ℚ) ≠ 0 := by exact_mod_cast hm a
    have hmb : (m b : ℚ) ≠ 0 := by exact_mod_cast hm b
    rw [hk, map_add, map_nsmul, map_nsmul, smul_add, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, smul_smul]
    push_cast
    congr 2 <;> field_simp
  · intro v
    have hk := key (j v) 1 v one_ne_zero (by simp)
    simpa using hk

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.FinrankIntEqFinrankRat.finrank_eq_of_place j hj hd`.
-/
private theorem finrank_eq_of_place {M V : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    [AddCommGroup V] [Module ℚ V] (j : M →+ V) (hj : Function.Injective j)
    (hd : ∀ w, ∃ (m : ℕ) (u : M), m ≠ 0 ∧ m • w = j u) :
    Module.finrank ℤ M = Module.finrank ℚ V :=
  _root_.UpperTheory.Reformulated.B.FinrankIntEqFinrankRat.finrank_eq_of_place j hj hd

/- English proof (translation)
Set `b` to `Module.finBasis ℤ M`. Set `v : Fin (Module.finrank ℤ M) → (Fin g → ℂ)` to `fun i => P (b i)`. Establish `hPx : ∀ x, P x = ∑ i, (b.repr x i) • v i`. Introduce `x`. Use `conv_lhs => rw [← b.sum_repr x]`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => map_zsmul _ _ _`. Establish `hsp : ⊤ ≤ Submodule.span ℝ (Set.range v)`. Rewrite using `[← hs]`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨x, rfl⟩`. Rewrite using `[hPx]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Conclude with `zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _`. Establish `hfr : Fintype.card (Fin (Module.finrank ℤ M)) = Module.finrank ℝ (Fin g → ℂ)`.

Rewrite using `[Fintype.card_fin, hc, Module.finrank_pi_fintype]`. Simplify using `[Complex.finrank_real_complex, mul_comm]`. Establish `li : LinearIndependent ℝ v` using `linearIndependent_of_top_le_span_of_card_eq_finrank hsp hfr`. Use `⟨(injective_iff_map_eq_zero P).mpr fun x hx => ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : ∑ i, ((b.repr x i : ℤ) : ℝ) • v i = 0`.

Rewrite using `[← hx, hPx]`. Conclude with `Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ _ _`. Establish `h1` using `Fintype.linearIndependent_iff.mp li _ h0`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`.

Simplify using `using h1 i`. Set `bb : Module.Basis (Fin (Module.finrank ℤ M)) ℝ (Fin g → ℂ)` to `Module.Basis.mk li hsp`. Establish `hset : (P.range : Set (Fin g → ℂ)) = (Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ))`. Establish `hb : Set.range bb = Set.range v`. Rewrite using `[Module.Basis.coe_mk]`.

Rewrite using `[hb]`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩ show P x ∈ Submodule.span ℤ (Set.range v)`. Rewrite using `[hPx]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `hy`. Establish `hy' : y ∈ Submodule.span ℤ (Set.range v)` using `hy`. Proceed by induction on `hy' using Submodule.span_induction with`. Consider the case `mem a ha => obtain ⟨i, rfl⟩ := ha`.

Conclude with `⟨b i, rfl⟩`. Consider the case `zero => exact zero_mem P.range`. Consider the case `add a c _ _ h1 h2 => exact add_mem (h1 (by assumption)) (h2 (by assumption))`. Consider the case `smul r a _ h1 => exact zsmul_mem (h1 (by assumption)) r`. Establish `hd : DiscreteTopology (Submodule.span ℤ (Set.range bb))` using `inferInstance`.

Establish `hd' : DiscreteTopology ((Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ)))` using `hd`. Rewrite `hd'` using `[← hset]`. Conclude with `hd'`.
-/
private theorem period_of_basis {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M] {g : ℕ}
    (P : M →+ (Fin g → ℂ)) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (hc : Module.finrank ℤ M = 2 * g) :
    Function.Injective P ∧ DiscreteTopology P.range := by
  let b := Module.finBasis ℤ M
  let v : Fin (Module.finrank ℤ M) → (Fin g → ℂ) := fun i => P (b i)
  have hPx : ∀ x, P x = ∑ i, (b.repr x i) • v i := by
    intro x
    conv_lhs => rw [← b.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hs]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, rfl⟩
    rw [hPx]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i)) _
  have hfr : Fintype.card (Fin (Module.finrank ℤ M)) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Fintype.card_fin, hc, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have li : LinearIndependent ℝ v := linearIndependent_of_top_le_span_of_card_eq_finrank hsp hfr
  refine ⟨(injective_iff_map_eq_zero P).mpr fun x hx => ?_, ?_⟩
  · have h0 : ∑ i, ((b.repr x i : ℤ) : ℝ) • v i = 0 := by
      rw [← hx, hPx]
      exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul ℝ _ _
    have h1 := Fintype.linearIndependent_iff.mp li _ h0
    apply b.repr.injective
    ext i
    simpa using h1 i
  · let bb : Module.Basis (Fin (Module.finrank ℤ M)) ℝ (Fin g → ℂ) := Module.Basis.mk li hsp
    have hset : (P.range : Set (Fin g → ℂ)) = (Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ)) := by
      have hb : Set.range bb = Set.range v := by
        rw [Module.Basis.coe_mk]
      rw [hb]
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        show P x ∈ Submodule.span ℤ (Set.range v)
        rw [hPx]
        exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      · intro hy
        have hy' : y ∈ Submodule.span ℤ (Set.range v) := hy
        induction hy' using Submodule.span_induction with
        | mem a ha => obtain ⟨i, rfl⟩ := ha; exact ⟨b i, rfl⟩
        | zero => exact zero_mem P.range
        | add a c _ _ h1 h2 => exact add_mem (h1 (by assumption)) (h2 (by assumption))
        | smul r a _ h1 => exact zsmul_mem (h1 (by assumption)) r
    have hd : DiscreteTopology (Submodule.span ℤ (Set.range bb)) := inferInstance
    have hd' : DiscreteTopology ((Submodule.span ℤ (Set.range bb) : Set (Fin g → ℂ))) := hd
    rw [← hset] at hd'
    exact hd'

/- English proof (translation)
Simplify using `[hermForm, Matrix.smul_mulVec, dotProduct_smul]`.
-/
private theorem herm_smul_mat {g : ℕ} (r : ℂ) (H : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) :
    hermForm (r • H) x y = r * hermForm H x y := by
  simp [hermForm, Matrix.smul_mulVec, dotProduct_smul]

/- English proof (translation)
Simplify using `only [hermForm]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ m x, ← Nat.cast_smul_eq_nsmul ℂ n y, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]`. Simplify using `only [smul_eq_mul, star_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem herm_nsmul {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ) (m n : ℕ) (x y : Fin g → ℂ) :
    hermForm H (m • x) (n • y) = ((m : ℂ) * n) * hermForm H x y := by
  simp only [hermForm]
  rw [← Nat.cast_smul_eq_nsmul ℂ m x, ← Nat.cast_smul_eq_nsmul ℂ n y, star_smul, Matrix.mulVec_smul,
    smul_dotProduct, dotProduct_smul]
  simp only [smul_eq_mul, star_natCast]
  ring

/- English proof (translation)
Use `⟨?_, fun z hz => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq]`. Simplify using the standard rewrite rules. Rewrite using `[herm_smul_mat, Complex.re_ofReal_mul]`. Conclude with `mul_pos hr (hpos z hz)`.
-/
private theorem herm_scale {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) {r : ℝ} (hr : 0 < r) :
    ((r : ℂ) • Hm).IsHermitian ∧ ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm ((r : ℂ) • Hm) z z).re := by
  refine ⟨?_, fun z hz => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq]
    simp
  · rw [herm_smul_mat, Complex.re_ofReal_mul]
    exact mul_pos hr (hpos z hz)

/- English proof (translation)
Introduce `p _ D G L β ρ D' j hpl`. Take `⟨hinj, hact, hden, s, hs, hEF⟩` from `hpl`. Establish `hsR : (0 : ℝ) < (s : ℝ)` using `by exact_mod_cast hs`. Establish `hform : ∀ (m n : ℕ) (u w : VQ D), formB L β (m • u) (n • w) = (m : ℚ) * n * formB L β u w`. Introduce `m n u w`.

Simplify using `only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun P hP => ?_, fun Q hQ hrk => ?_⟩` and prove the remaining obligations. Take `⟨hPa, -, -, hPs, Hm, hH, hpos, hIm⟩` from `hP`. Take `⟨Q, hQ⟩` from `exists_extend j hinj hden P`.

Establish `hsc` using `herm_scale hH hpos (inv_pos.mpr hsR)`. Use `⟨Q, ⟨fun c w => ?_, ?_, ((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun u w => ?_⟩, hQ⟩` and prove the remaining obligations. Take `⟨m, a, hm, h⟩` from `hden w`. Apply `IsAddTorsionFree.nsmul_right_injective hm` to reduce the goal to its premises. Use `show m • Q (actQ D c w) = m • (ρ c *ᵥ Q w)`.

Establish `e1 : m • Q (actQ D c w) = P (c • a)`. Rewrite using `[← map_nsmul, ← map_nsmul (actQ D c), h, ← hact, hQ]`. Establish `e2 : m • (ρ c *ᵥ Q w) = ρ c *ᵥ P a`. Rewrite using `[← hQ, ← h, map_nsmul, Matrix.mulVec_smul]`. Rewrite using `[e1, e2, hPa]`.

Rewrite using `[eq_top_iff, ← hPs]`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `⟨j x, hQ x⟩`. Take `⟨m, a, hm, ha⟩` from `hden u`.

Take `⟨n, b, hn, hb⟩` from `hden w`. Establish `hmR : (m : ℝ) ≠ 0` using `by exact_mod_cast hm`. Establish `hnR : (n : ℝ) ≠ 0` using `by exact_mod_cast hn`. Establish `h1 : hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b)) = (((m : ℝ) * n : ℝ) : ℂ) * hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w)`. Rewrite using `[← ha, ← hb, map_nsmul, map_nsmul, herm_nsmul]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `h2 : (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b))).im = ((s : ℝ))⁻¹ * (D'.EF a b : ℝ)`. Rewrite using `[herm_smul_mat, hQ, hQ, Complex.im_ofReal_mul, hIm]`. Establish `h3 : (D'.EF a b : ℝ) = (s : ℝ) * ((m : ℝ) * n * (formB L β u w : ℚ))`.

Establish `h4` using `hEF a b`. Rewrite `h4` using `[← ha, ← hb, hform]`. Conclude with `h4` after adjusting the coercions. Rewrite `h2` using `[h1, Complex.im_ofReal_mul, h3]`. Establish `hs0 : (s : ℝ) ≠ 0` using `hsR.ne'`.

Establish `h5 : ((m : ℝ) * n) * (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w)).im = ((m : ℝ) * n) * (formB L β u w : ℚ)`. Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts. Conclude with `mul_left_cancel₀ (mul_ne_zero hmR hnR) h5`. Take `⟨hQa, hQs, Hm, hH, hpos, hIm⟩` from `hQ`.

Establish `hc : Module.finrank ℤ D'.La = 2 * D.g`. Rewrite using `[finrank_eq_of_place j hinj hden, hrk]`. Use `haveI : Module.Free ℤ D.La := D.freeLa`. Conclude with `Module.finrank_baseChange`. Establish `hs' : Submodule.span ℝ (Set.range (Q.comp j)) = ⊤`.

Rewrite using `[eq_top_iff, ← hQs]`. Apply `Submodule.span_le.mpr` to reduce the goal to its premises. Introduce and unpack `_ ⟨w, rfl⟩`. Take `⟨m, a, hm, h⟩` from `hden w`. Establish `hm' : (m : ℝ) ≠ 0` using `by exact_mod_cast hm`.

Establish `e : Q w = (m : ℝ)⁻¹ • Q (j a)`. Rewrite using `[← h, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Take `⟨hi, hdisc⟩` from `period_of_basis (Q.comp j) hs' hc`.

Establish `hsc` using `herm_scale hH hpos hsR`. Use `⟨fun c u => ?_, hi, hdisc, hs', ((s : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun x y => ?_⟩` and prove the remaining obligations. Simplify using `only [AddMonoidHom.comp_apply]`. Rewrite using `[hact, hQa]`. Simplify using `only [AddMonoidHom.comp_apply]`.

Rewrite using `[herm_smul_mat, Complex.im_ofReal_mul, hIm]`. Establish `h4` using `hEF x y`. Conclude with `h4.symm` after adjusting the coercions.
-/
theorem UpperTheory.Gal.W2.placePer_of :
    UpperTheory.Gal.W2.PlacePer := by
  intro p _ D G L β ρ D' j hpl
  obtain ⟨hinj, hact, hden, s, hs, hEF⟩ := hpl
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hform : ∀ (m n : ℕ) (u w : VQ D),
      formB L β (m • u) (n • w) = (m : ℚ) * n * formB L β u w := by
    intro m n u w
    simp only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  refine ⟨fun P hP => ?_, fun Q hQ hrk => ?_⟩
  · obtain ⟨hPa, -, -, hPs, Hm, hH, hpos, hIm⟩ := hP
    obtain ⟨Q, hQ⟩ := exists_extend j hinj hden P
    have hsc := herm_scale hH hpos (inv_pos.mpr hsR)
    refine ⟨Q, ⟨fun c w => ?_, ?_, ((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun u w => ?_⟩, hQ⟩
    · obtain ⟨m, a, hm, h⟩ := hden w
      apply IsAddTorsionFree.nsmul_right_injective hm
      show m • Q (actQ D c w) = m • (ρ c *ᵥ Q w)
      have e1 : m • Q (actQ D c w) = P (c • a) := by
        rw [← map_nsmul, ← map_nsmul (actQ D c), h, ← hact, hQ]
      have e2 : m • (ρ c *ᵥ Q w) = ρ c *ᵥ P a := by
        rw [← hQ, ← h, map_nsmul, Matrix.mulVec_smul]
      rw [e1, e2, hPa]
    · rw [eq_top_iff, ← hPs]
      apply Submodule.span_mono
      rintro _ ⟨x, rfl⟩
      exact ⟨j x, hQ x⟩
    · obtain ⟨m, a, hm, ha⟩ := hden u
      obtain ⟨n, b, hn, hb⟩ := hden w
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      have h1 : hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b)) =
          (((m : ℝ) * n : ℝ) : ℂ) * hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w) := by
        rw [← ha, ← hb, map_nsmul, map_nsmul, herm_nsmul]
        push_cast
        rfl
      have h2 : (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q (j a)) (Q (j b))).im =
          ((s : ℝ))⁻¹ * (D'.EF a b : ℝ) := by
        rw [herm_smul_mat, hQ, hQ, Complex.im_ofReal_mul, hIm]
      have h3 : (D'.EF a b : ℝ) = (s : ℝ) * ((m : ℝ) * n * (formB L β u w : ℚ)) := by
        have h4 := hEF a b
        rw [← ha, ← hb, hform] at h4
        exact_mod_cast h4
      rw [h1, Complex.im_ofReal_mul, h3] at h2
      have hs0 : (s : ℝ) ≠ 0 := hsR.ne'
      have h5 : ((m : ℝ) * n) * (hermForm (((((s : ℝ))⁻¹ : ℝ) : ℂ) • Hm) (Q u) (Q w)).im =
          ((m : ℝ) * n) * (formB L β u w : ℚ) := by
        rw [h2]
        field_simp
      exact mul_left_cancel₀ (mul_ne_zero hmR hnR) h5
  · obtain ⟨hQa, hQs, Hm, hH, hpos, hIm⟩ := hQ
    have hc : Module.finrank ℤ D'.La = 2 * D.g := by
      rw [finrank_eq_of_place j hinj hden, hrk]
      haveI : Module.Free ℤ D.La := D.freeLa
      exact Module.finrank_baseChange
    have hs' : Submodule.span ℝ (Set.range (Q.comp j)) = ⊤ := by
      rw [eq_top_iff, ← hQs]
      apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      obtain ⟨m, a, hm, h⟩ := hden w
      have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have e : Q w = (m : ℝ)⁻¹ • Q (j a) := by
        rw [← h, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hm', one_smul]
      rw [e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    obtain ⟨hi, hdisc⟩ := period_of_basis (Q.comp j) hs' hc
    have hsc := herm_scale hH hpos hsR
    refine ⟨fun c u => ?_, hi, hdisc, hs', ((s : ℝ) : ℂ) • Hm, hsc.1, hsc.2, fun x y => ?_⟩
    · simp only [AddMonoidHom.comp_apply]
      rw [hact, hQa]
    · simp only [AddMonoidHom.comp_apply]
      rw [herm_smul_mat, Complex.im_ofReal_mul, hIm]
      have h4 := hEF x y
      exact_mod_cast h4.symm
