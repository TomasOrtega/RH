import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFrameEx

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private def colM {K : Type*} {n : ℕ} (b : Fin n → Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => b j i

/- English proof (translation)
Use extensionality with `r c`. Distinguish the cases in `h : c = i`. Substitute `h` using the available equality. Simplify using `[colM, Matrix.updateCol_apply]`. Simplify using `[colM, Matrix.updateCol_apply, h, Function.update_of_ne]`.
-/
private theorem colM_update {K : Type*} [Field K] {n : ℕ} (b : Fin n → Fin n → K) (i : Fin n)
    (y : Fin n → K) : (colM b).updateCol i y = colM (Function.update b i y) := by
  ext r c
  by_cases h : c = i
  · subst h; simp [colM, Matrix.updateCol_apply]
  · simp [colM, Matrix.updateCol_apply, h, Function.update_of_ne]

/- English proof (translation)
Use extensionality with `r`. Simplify using `[colM, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.
-/
private theorem colM_mulVec {K : Type*} [Field K] {n : ℕ} (b : Fin n → Fin n → K)
    (c : Fin n → K) : colM b *ᵥ c = ∑ i, c i • b i := by
  ext r
  simp [colM, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Establish `h1 : f 1 = 1`. Establish `h` using `hm 1 1`. Establish `hp` using `hpos 1 one_ne_zero`. Rewrite `h` using `[_root_.one_mul]`. Conclude with `mul_left_cancel₀ hp.ne' (by rw [_root_.mul_one]; exact h.symm)`.

Take `⟨t, hts, hspan, hli⟩` from `exists_linearIndependent K (s : Set (Fin n → K))`. Establish `hfin : t.Finite` using `s.finite_toSet.subset hts`. Use `haveI := hfin.fintype`. Establish `htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : t → Fin n → K))`. Rewrite using `[Subtype.range_coe, hspan, hs]`.

Establish `hcard : Fintype.card t = n`. Use `Module.finrank_eq_card_basis (Module.Basis.mk hli htop)` as an intermediate fact. Rewrite `this` using `[Module.finrank_fin_fun]`. Conclude with `this.symm`. Set `e` to `Fintype.equivFinOfCardEq hcard`.

Set `b0 : Fin n → Fin n → K` to `fun i => (e.symm i).1`. Establish `hb0 : (colM b0).det ≠ 0`. Introduce `hd`. Take `⟨v, hv, hMv⟩` from `(Matrix.exists_mulVec_eq_zero_iff).mpr hd`. Rewrite `hMv` using `[colM_mulVec]`.

Establish `hli' : LinearIndependent K b0` using `hli.comp e.symm e.symm.injective`. Conclude with `hv (funext (Fintype.linearIndependent_iff.mp hli' v hMv))`. Set `F : (Fin n → s) → ℝ` to `fun g => f (colM (fun i => (g i : Fin n → K))).det`. Take `⟨g0, -, hg0⟩` from `Finset.exists_max_image (Finset.univ : Finset (Fin n → s)) F ⟨fun i => ⟨b0 i, hts (e.symm i).2⟩, Finset.mem_univ _⟩`. Set `b : Fin n → Fin n → K` to `fun i => (g0 i : Fin n → K)`.

Establish `hle : F (fun i => ⟨b0 i, hts (e.symm i).2⟩) ≤ f (colM b).det` using `hg0 _ (Finset.mem_univ _)`. Establish `hpos0 : 0 < f (colM b).det` using `lt_of_lt_of_le (hpos _ hb0) hle`. Establish `hdet : (colM b).det ≠ 0`. Introduce `h`. Rewrite `hpos0` using `[h, h0]`.

Conclude with `lt_irrefl _ hpos0`. Use `⟨b, hdet, fun i => (g0 i).2, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Use `set d := (colM b).det with hd`. Use `⟨d⁻¹ • (colM b).cramer y, ?_, ?_⟩` and prove the remaining obligations.

Introduce `i`. Establish `hupd : Function.update b i y = fun j => ((Function.update g0 i ⟨y, hy⟩ j : s) : Fin n → K)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Simplify using `[b]`. Simplify using `[b, Function.update_apply, hj]`. Establish `hmax : f (colM (Function.update b i y)).det ≤ f d`. Rewrite using `[hupd]`. Conclude with `hg0 _ (Finset.mem_univ _)`.

Establish `hinv : f d⁻¹ = (f d)⁻¹`. Apply `eq_inv_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[← hm, mul_inv_cancel₀ hdet, h1]`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, colM_update]`. Rewrite using `[hm, hinv, inv_mul_le_iff₀ hpos0, _root_.mul_one]`.

Conclude with `hmax`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]`.
-/
private theorem exists_frame {K : Type*} [Field K] (f : K → ℝ) (h0 : f 0 = 0)
    (hm : ∀ x y, f (x * y) = f x * f y) (hpos : ∀ x, x ≠ 0 → 0 < f x) (hnn : ∀ x, 0 ≤ f x)
    (ha : ∀ x y, f (x + y) ≤ max (f x) (f y)) {n : ℕ} (s : Finset (Fin n → K))
    (hs : Submodule.span K (s : Set (Fin n → K)) = ⊤) :
    ∃ b : Fin n → Fin n → K, (colM b).det ≠ 0 ∧ (∀ i, b i ∈ s) ∧
      ∀ y ∈ s, ∃ c : Fin n → K, (∀ i, f (c i) ≤ 1) ∧ colM b *ᵥ c = y := by
  classical
  have h1 : f 1 = 1 := by
    have h := hm 1 1
    have hp := hpos 1 one_ne_zero
    rw [_root_.one_mul] at h
    exact mul_left_cancel₀ hp.ne' (by rw [_root_.mul_one]; exact h.symm)
  obtain ⟨t, hts, hspan, hli⟩ := exists_linearIndependent K (s : Set (Fin n → K))
  have hfin : t.Finite := s.finite_toSet.subset hts
  haveI := hfin.fintype
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : t → Fin n → K)) := by
    rw [Subtype.range_coe, hspan, hs]
  have hcard : Fintype.card t = n := by
    have := Module.finrank_eq_card_basis (Module.Basis.mk hli htop)
    rw [Module.finrank_fin_fun] at this
    exact this.symm
  let e := Fintype.equivFinOfCardEq hcard
  let b0 : Fin n → Fin n → K := fun i => (e.symm i).1
  have hb0 : (colM b0).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hd
    rw [colM_mulVec] at hMv
    have hli' : LinearIndependent K b0 := hli.comp e.symm e.symm.injective
    exact hv (funext (Fintype.linearIndependent_iff.mp hli' v hMv))
  let F : (Fin n → s) → ℝ := fun g => f (colM (fun i => (g i : Fin n → K))).det
  obtain ⟨g0, -, hg0⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n → s)) F
    ⟨fun i => ⟨b0 i, hts (e.symm i).2⟩, Finset.mem_univ _⟩
  let b : Fin n → Fin n → K := fun i => (g0 i : Fin n → K)
  have hle : F (fun i => ⟨b0 i, hts (e.symm i).2⟩) ≤ f (colM b).det := hg0 _ (Finset.mem_univ _)
  have hpos0 : 0 < f (colM b).det := lt_of_lt_of_le (hpos _ hb0) hle
  have hdet : (colM b).det ≠ 0 := by
    intro h
    rw [h, h0] at hpos0
    exact lt_irrefl _ hpos0
  refine ⟨b, hdet, fun i => (g0 i).2, ?_⟩
  intro y hy
  set d := (colM b).det with hd
  refine ⟨d⁻¹ • (colM b).cramer y, ?_, ?_⟩
  · intro i
    have hupd : Function.update b i y = fun j => ((Function.update g0 i ⟨y, hy⟩ j : s) : Fin n → K) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [b]
      · simp [b, Function.update_apply, hj]
    have hmax : f (colM (Function.update b i y)).det ≤ f d := by
      rw [hupd]
      exact hg0 _ (Finset.mem_univ _)
    have hinv : f d⁻¹ = (f d)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [← hm, mul_inv_cancel₀ hdet, h1]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cramer_apply, colM_update]
    rw [hm, hinv, inv_mul_le_iff₀ hpos0, _root_.mul_one]
    exact hmax
  · rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet, one_smul]

/- English proof (translation)
Take `⟨b, hdet, hbs, hcoord⟩` from `exists_frame f h0 hm hpos hnn ha s hs`. Establish `hu : IsUnit (colM b)` using `(Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Establish `hl : ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * colM b = 1`. Establish `h` using `Units.inv_mul hu.unit`.

Rewrite `h` using `[IsUnit.unit_spec]`. Then use the resulting hypothesis. Establish `hr : colM b * ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1`. Establish `h` using `Units.mul_inv hu.unit`. Rewrite `h` using `[IsUnit.unit_spec]`. Then use the resulting hypothesis. Establish `hsum : ∀ {α : Type} (t : Finset α) (u : α → K), (∀ i ∈ t, f (u i) ≤ 1) → f (∑ i ∈ t, u i) ≤ 1`.

Introduce `α t u hu'`. Conclude with `Finset.sum_induction u (fun x => f x ≤ 1) (fun x y hx hy => (ha x y).trans (max_le hx hy)) (by rw [h0]; exact zero_le_one) hu'`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz set c := ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z with hc`.

Establish `hzc : z = colM b *ᵥ c`. Rewrite using `[hc, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]`. Use `⟨fun y => ∑ i, if b i = y then c i else 0, ?_, ?_⟩` and prove the remaining obligations. Introduce `y`. Apply `hsum` to reduce the goal to its premises.

Introduce `i _`. Use `split_ifs`. Conclude with `hz i`. Rewrite using `[h0]`. Conclude with `zero_le_one`.

Rewrite using `[hzc, colM_mulVec]`. Simplify using `only [Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [ite_smul, zero_smul]`.

Rewrite using `[Finset.sum_ite_eq, if_pos (hbs i)]`. Introduce and unpack `⟨a, ha1, rfl⟩ i choose! C hC1 hC2 using hcoord`. Establish `hz : ∑ y ∈ s, a y • y = colM b *ᵥ ∑ y ∈ s, a y • C y`. Rewrite using `[Matrix.mulVec_sum]`. Use `Finset.sum_congr rfl fun y hy => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_smul, hC2 y hy]`. Rewrite using `[hz, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Apply `hsum` to reduce the goal to its premises. Introduce `y hy`.

Rewrite using `[hm]`. Conclude with `mul_le_one₀ (ha1 y) (hnn _) (hC1 y hy i)`.
-/
private theorem exists_gl {K : Type} [Field K] (f : K → ℝ) (h0 : f 0 = 0)
    (hm : ∀ x y, f (x * y) = f x * f y) (hpos : ∀ x, x ≠ 0 → 0 < f x) (hnn : ∀ x, 0 ≤ f x)
    (ha : ∀ x y, f (x + y) ≤ max (f x) (f y)) {n : ℕ} (s : Finset (Fin n → K))
    (hs : Submodule.span K (s : Set (Fin n → K)) = ⊤) :
    ∃ g : GL (Fin n) K, ∀ z : Fin n → K,
      (∀ i, f ((((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) i) ≤ 1) ↔
        ∃ a : (Fin n → K) → K, (∀ y, f (a y) ≤ 1) ∧ z = ∑ y ∈ s, a y • y := by
  classical
  obtain ⟨b, hdet, hbs, hcoord⟩ := exists_frame f h0 hm hpos hnn ha s hs
  have hu : IsUnit (colM b) := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  refine ⟨hu.unit, ?_⟩
  have hl : ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * colM b = 1 := by
    have h := Units.inv_mul hu.unit
    rwa [IsUnit.unit_spec] at h
  have hr : colM b * ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
    have h := Units.mul_inv hu.unit
    rwa [IsUnit.unit_spec] at h
  have hsum : ∀ {α : Type} (t : Finset α) (u : α → K), (∀ i ∈ t, f (u i) ≤ 1) →
      f (∑ i ∈ t, u i) ≤ 1 := by
    intro α t u hu'
    exact Finset.sum_induction u (fun x => f x ≤ 1)
      (fun x y hx hy => (ha x y).trans (max_le hx hy)) (by rw [h0]; exact zero_le_one) hu'
  intro z
  constructor
  · intro hz
    set c := ((hu.unit⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z with hc
    have hzc : z = colM b *ᵥ c := by
      rw [hc, Matrix.mulVec_mulVec, hr, Matrix.one_mulVec]
    refine ⟨fun y => ∑ i, if b i = y then c i else 0, ?_, ?_⟩
    · intro y
      apply hsum
      intro i _
      split_ifs
      · exact hz i
      · rw [h0]
        exact zero_le_one
    · rw [hzc, colM_mulVec]
      simp only [Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [ite_smul, zero_smul]
      rw [Finset.sum_ite_eq, if_pos (hbs i)]
  · rintro ⟨a, ha1, rfl⟩ i
    choose! C hC1 hC2 using hcoord
    have hz : ∑ y ∈ s, a y • y = colM b *ᵥ ∑ y ∈ s, a y • C y := by
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [Matrix.mulVec_smul, hC2 y hy]
    rw [hz, Matrix.mulVec_mulVec, hl, Matrix.one_mulVec]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply hsum
    intro y hy
    rw [hm]
    exact mul_le_one₀ (ha1 y) (hnn _) (hC1 y hy i)

/- English proof (translation)
Introduce `p _ G w s hs`. Conclude with `exists_gl (fun x : G.Fw w => ‖(x : PadicAlgCl p)‖) (by simp) (fun x y => by`. Use `push_cast`. Conclude with `norm_mul _ _)`. Use the proof step `(fun x hx => norm_pos_iff.mpr (by exact_mod_cast hx))`.

Use the proof step `(fun x => norm_nonneg _)`. Use the proof step `(fun x y => by`. Use `push_cast`. Conclude with `IsUltrametricDist.norm_add_le_max _ _) s hs`.
-/
theorem UpperTheory.Gal.W2.locLat_of :
    UpperTheory.Gal.W2.LocLat := by
  intro p _ G w s hs
  exact exists_gl (fun x : G.Fw w => ‖(x : PadicAlgCl p)‖) (by simp)
    (fun x y => by
      push_cast
      exact norm_mul _ _)
    (fun x hx => norm_pos_iff.mpr (by exact_mod_cast hx))
    (fun x => norm_nonneg _)
    (fun x y => by
      push_cast
      exact IsUltrametricDist.norm_add_le_max _ _) s hs
