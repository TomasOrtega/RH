import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def RestEdgeCountSrc : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (k : ℕ), 1 ≤ k → ∀ L : Submodule R.W (Fin k → R.Qq), IsLattice R.W L →
    ∃ (Ne : ℕ) (es : Fin Ne → Edge R.W R.Qq k), Function.Injective es ∧
      (∀ i, IsEdge p n' 1 (es i) ∧ (es i).src = L) ∧ gaussianNumber (p ^ n') k ≤ Ne

/- English proof (translation)
Unfold `vLEO at h`. Take `⟨q, hq, hqD⟩` from `h`. Unfold `vO vK ordW at hq`. Establish `hx0 : algebraMap O (KK O) z ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr hz`. Rewrite `hq` using `[if_neg hx0]`.

Simplify using `only at hq`. Establish `hspec` using `Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))`. Generalize the expression as in `Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab at hq hspec`. Establish `h1 : ab.1 = z * (ab.2 : O)`. Apply `IsFractionRing.injective O (KK O)` to reduce the goal to its premises.

Rewrite using `[map_mul]`. Conclude with `hspec.symm`. Establish `hs0 : (ab.2 : O) ≠ 0` using `nonZeroDivisors.coe_ne_zero ab.2`. Establish `hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis.

Establish `hst : IsDiscreteValuationRing.addVal O (ab.2 : O) ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Rewrite `hq` using `[h1, AddValuation.map_mul, ENat.toNat_add hzt hst]`. Simplify using `only [Nat.cast_add, add_sub_cancel_right, WithTop.map_coe, WithTop.coe_inj] at hq`. Establish `hram : ramE p O = 2`.

Unfold `ramE`. Rewrite using `[← hsq, AddValuation.map_pow, IsDiscreteValuationRing.addVal_uniformizer hw]`. Simplify using the standard rewrite rules. Rewrite `hq` using `[hram]`. Establish `hreal : ((IsDiscreteValuationRing.addVal O z).toNat : ℝ) < (c : ℝ)`.

Rewrite `hqD` using `[← hq]`. Move the coercions through the operations in `at hqD`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlt : (IsDiscreteValuationRing.addVal O z).toNat < c` using `by exact_mod_cast hreal`. Establish `hnat : (IsDiscreteValuationRing.addVal O z).toNat ≤ c - 1` using `by omega`.

Rewrite using `[← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow, IsDiscreteValuationRing.addVal_uniformizer hw, ← ENat.coe_toNat hzt, nsmul_eq_mul, mul_one]`. Conclude with `hnat` after adjusting the coercions.
-/
theorem dvd_w_pow_of_vLEO {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {w : O}
    (hw : Irreducible w) (hsq : w ^ 2 = (p : O)) {z : O} (hz : z ≠ 0) {D : ℝ} {c : ℕ} (hc : 2 * D < c)
    (h : vLEO p z D) : z ∣ w ^ (c - 1) := by
  classical
  unfold vLEO at h
  obtain ⟨q, hq, hqD⟩ := h
  unfold vO vK ordW at hq
  have hx0 : algebraMap O (KK O) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr hz
  rw [if_neg hx0] at hq
  dsimp only at hq
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  generalize Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab
    at hq hspec
  have h1 : ab.1 = z * (ab.2 : O) := by
    apply IsFractionRing.injective O (KK O)
    rw [map_mul]
    exact hspec.symm
  have hs0 : (ab.2 : O) ≠ 0 := nonZeroDivisors.coe_ne_zero ab.2
  have hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hst : IsDiscreteValuationRing.addVal O (ab.2 : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [h1, AddValuation.map_mul, ENat.toNat_add hzt hst] at hq
  simp only [Nat.cast_add, add_sub_cancel_right, WithTop.map_coe, WithTop.coe_inj] at hq
  have hram : ramE p O = 2 := by
    unfold ramE
    rw [← hsq, AddValuation.map_pow, IsDiscreteValuationRing.addVal_uniformizer hw]
    simp
  rw [hram] at hq
  have hreal : ((IsDiscreteValuationRing.addVal O z).toNat : ℝ) < (c : ℝ) := by
    rw [← hq] at hqD
    push_cast at hqD
    linarith
  have hlt : (IsDiscreteValuationRing.addVal O z).toNat < c := by exact_mod_cast hreal
  have hnat : (IsDiscreteValuationRing.addVal O z).toNat ≤ c - 1 := by omega
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow,
    IsDiscreteValuationRing.addVal_uniformizer hw, ← ENat.coe_toNat hzt, nsmul_eq_mul, mul_one]
  exact_mod_cast hnat

/- English proof (translation)
Establish `hmap : P.map (IsLocalRing.residue O) = 1`. Use extensionality with `i l`. Establish `h2 : IsLocalRing.residue O (P i l) = IsLocalRing.residue O ((1 : Matrix ι ι O) i l)`. Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `h i l`.

Rewrite using `[Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one]`. Conclude with `one_ne_zero`.
-/
theorem isUnit_det_of_one_add' {O ι : Type*} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι O) (h : ∀ i l, P i l - (1 : Matrix ι ι O) i l ∈ IsLocalRing.maximalIdeal O) :
    IsUnit P.det := by
  have hmap : P.map (IsLocalRing.residue O) = 1 := by
    ext i l
    have h2 : IsLocalRing.residue O (P i l) =
        IsLocalRing.residue O ((1 : Matrix ι ι O) i l) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact h i l
    rw [Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hmap,
    Matrix.det_one]
  exact one_ne_zero

section Clean

variable {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

/- English proof (translation)
Unfold `be`. Rewrite using `[smul_comm, map_smul, smul_eq_mul]`.
-/
theorem be_smulK_left (c : R.Kf) (F : Vsp R.Kf lam0) (G : Module.Dual R.Kf (Vsp R.Kf lam0)) :
    be p 1 lam0 (c • F) G = c * be p 1 lam0 F G := by
  unfold be
  rw [smul_comm, map_smul, smul_eq_mul]

/- English proof (translation)
Unfold `be`. Rewrite using `[smul_add, map_add]`.
-/
theorem be_add_left (F F' : Vsp R.Kf lam0) (G : Module.Dual R.Kf (Vsp R.Kf lam0)) :
    be p 1 lam0 (F + F') G = be p 1 lam0 F G + be p 1 lam0 F' G := by
  unfold be
  rw [smul_add, map_add]

/- English proof (translation)
Unfold `be`. Rewrite using `[Finset.smul_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm, map_smul, smul_eq_mul]`.
-/
theorem be_sum_left {ι : Type*} (s : Finset ι) (c : ι → R.Kf) (F : ι → Vsp R.Kf lam0)
    (G : Module.Dual R.Kf (Vsp R.Kf lam0)) :
    be p 1 lam0 (∑ i ∈ s, c i • F i) G = ∑ i ∈ s, c i * be p 1 lam0 (F i) G := by
  unfold be
  rw [Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, map_smul, smul_eq_mul]

/- English proof (translation)
Unfold `scale at hF`. Take `⟨F0, hF0, rfl⟩` from `Submodule.mem_map.mp hF`. Take `⟨b, hb⟩` from `be_Re R lam0 e hF0 hG`. Use `⟨b, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, zpow_natCast]`.

Rewrite using `[be_smulK_left, hb, ← map_pow, ← map_mul]`.
-/
theorem be_scale_Re (e : Edge R.W R.Qq (m + 1)) (c : ℕ) {F : Vsp R.Kf lam0}
    {G : Module.Dual R.Kf (Vsp R.Kf lam0)}
    (hF : F ∈ scale (algebraMap R.O R.Kf R.w ^ (c : ℤ)) (Re p R.ι R.σ R.w 1 lam0 e))
    (hG : G ∈ Re' p R.ι R.σ R.w 1 lam0 e) :
    ∃ b : R.O, be p 1 lam0 F G = algebraMap R.O R.Kf (R.w ^ c * b) := by
  unfold scale at hF
  obtain ⟨F0, hF0, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨b, hb⟩ := be_Re R lam0 e hF0 hG
  refine ⟨b, ?_⟩
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, zpow_natCast]
  rw [be_smulK_left, hb, ← map_pow, ← map_mul]

end Clean

/- English proof (translation)
Introduce `p n' R m lam0 hDom t c n D hD0 hDc hfac`. Establish `hdnn` using `dL_nonneg R lam0`. Distinguish the cases in `hn0 : n = 0`. Substitute `hn0` using the available equality. Simplify using `using hdnn`.

Establish `hL : IsLattice R.W (colSpan R.W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq))` using `⟨1, by simp, rfl⟩`. Take `⟨Ne, es, hinj, hes, hNe⟩` from `hcnt p n' R (m + 1) (by omega) _ hL`. Establish `hc1 : 1 ≤ c`. Establish `: (0 : ℝ) < c` using `by linarith`. Conclude with `this` after adjusting the coercions.

Establish `hdata : ∀ i : Fin Ne, ∃ (x : Fin n → Vsp R.Kf lam0) (y : Fin n → Module.Dual R.Kf (Vsp R.Kf lam0)) (z z' : R.O), z ≠ 0 ∧ (∀ a, x a ∈ CCL R lam0 t c (es i)) ∧ (∀ a, y a ∈ CCL' R lam0 t c (es i)) ∧ z' * z = R.w ^ (c - 1) ∧ ∀ a b, be p 1 lam0 (x a) (y b) = if a = b then algebraMap R …`. Introduce `i`. Break down `hfac (es i) (hes i).1 with h0 | ⟨x, y, hx, hy, z, Mx, hz, hv, hM⟩` into its components or cases. Conclude with `absurd h0 hn0`. Take `⟨z', hz'⟩` from `dvd_w_pow_of_vLEO R.std.2.1 R.std.1.w_sq hz hDc hv`.

Use `⟨x, fun b => ∑ l, Mx l b • y l, z, z', hz, hx, fun b => Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (hy l)), by rw [hz']; ring, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[be_sum]`. Conclude with `hM a b`. Use `choose x y z z' hz0 hx hy hzz hxy using hdata`. Establish `hβ : ∀ i l : Fin Ne × Fin n, ∃ β : R.O, β ∈ IsLocalRing.maximalIdeal R.O ∧ be p 1 lam0 (x i.1 i.2) (y l.1 l.2) = algebraMap R.O R.Kf (((1 : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O) i l + β) * z l.1)`.

Introduce and unpack `⟨i, a⟩ ⟨l, b⟩`. Distinguish the cases in `hil : i = l`. Substitute `hil` using the available equality. Use `⟨0, Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[hxy, Matrix.one_apply]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Establish `: ((i, a) : Fin Ne × Fin n) ≠ (i, b)` using `fun h => hab (Prod.mk.inj h).2`.

Rewrite using `[if_neg hab, if_neg this]`. Simplify using the standard rewrite rules. Establish `hne : es l ≠ es i` using `fun h => hil (hinj h).symm`. Establish `hXs` using `CCL_other R lam0 t c (es i) (es l) (hes _).1 ((hes _).2.trans (hes _).2.symm) hne (hx i a)`. Take `⟨b', hb⟩` from `be_scale_Re R lam0 (es l) c hXs (hy l b).1.2`.

Establish `h2 : ((i, a) : Fin Ne × Fin n) ≠ (l, b)` using `fun h => hil (Prod.mk.inj h).1`. Use `⟨R.w * b' * z' l, Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ R.w_mem), ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hb, Matrix.one_apply_ne h2, zero_add]`. Use `congr 1`.

Establish `h3 : R.w ^ c = R.w * R.w ^ (c - 1)`. Rewrite using `[← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h3, ← hzz l]`.

Expand and normalize the polynomial expressions, which then agree. Use `choose β hβm hβe using hβ`. Set `P : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O` to `Matrix.of fun i l => (1 : Matrix _ _ R.O) i l + β i l`. Establish `hP : IsUnit P.det`. Apply `isUnit_det_of_one_add'` to reduce the goal to its premises.

Introduce `i l`. Simplify `hβm i l` using `[P]`. Establish `hinjK : Function.Injective (algebraMap R.O R.Kf)`. Establish `hfr : IsFractionRing R.O R.Kf` using `R.std.1.frac_O`. Conclude with `IsFractionRing.injective R.O R.Kf`.

Establish `hPK : ((algebraMap R.O R.Kf).mapMatrix P).det ≠ 0`. Rewrite using `[← RingHom.map_det]`. Introduce `h0`. Establish `: P.det = 0` using `hinjK (by rw [h0, map_zero])`. Rewrite `hP` using `[this]`.

Conclude with `not_isUnit_zero hP`. Establish `hli : LinearIndependent R.Kf (fun i : Fin Ne × Fin n => x i.1 i.2)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h1 : ∀ l : Fin Ne × Fin n, ∑ i, g i * algebraMap R.O R.Kf (P i l) = 0`.

Introduce `l`. Establish `h2 : be p 1 lam0 (∑ i, g i • x i.1 i.2) (y l.1 l.2) = 0`. Rewrite using `[hg]`. Simplify using `[be]`. Rewrite `h2` using `[be_sum_left]`.

Establish `h3 : (∑ i, g i * algebraMap R.O R.Kf (P i l)) * algebraMap R.O R.Kf (z l.1) = 0`. Rewrite using `[← h2, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hβe i l, map_mul, mul_assoc]`. Both sides reduce to the same expression.

Establish `hz : algebraMap R.O R.Kf (z l.1) ≠ 0` using `fun h => hz0 l.1 (hinjK (by rw [h, map_zero]))`. Conclude with `(mul_eq_zero.1 h3).resolve_right hz`. Establish `h4 : Matrix.vecMul g ((algebraMap R.O R.Kf).mapMatrix P) = 0`. Use function extensionality and compare the values at `l`. Simplify `h1 l` using `[Matrix.vecMul, dotProduct]`.

Establish `h5` using `Matrix.eq_zero_of_vecMul_eq_zero hPK h4`. Introduce `i`. Rewrite using `[h5]`. Both sides reduce to the same expression. Establish `hpos : 0 < dimV R.Kf lam0` using `Formalism.MainNotions.G.LatticeSystems.kp_dimV_pos R.Kf lam0 hDom`.

Establish `hfin : Module.Finite R.Kf (Vsp R.Kf lam0)` using `Module.finite_of_finrank_pos hpos`. Establish `hcard : Ne * n ≤ dimV R.Kf lam0`. Use `hli.fintype_card_le_finrank` as an intermediate fact. Simplify `this` using `[dimV]`. Establish `hNpos` using `gaussianNumber_prime_pow_pos R (m + 1) (by omega)`.

Unfold `dL`. Rewrite using `[le_div_iff₀ hNpos]`. Establish `h6 : ((Ne * n : ℕ) : ℝ) ≤ (dimV R.Kf lam0 : ℝ)` using `by exact_mod_cast hcard`. Establish `h7 : (n : ℝ) * gaussianNumber (p ^ n') (m + 1) ≤ (n : ℝ) * Ne` using `mul_le_mul_of_nonneg_left hNe (Nat.cast_nonneg _)`. Move the coercions through the operations in `at h6`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rho_upper_bound_of_edge_count (hcnt : RestEdgeCountSrc) : RhoUpperBoundSmallDepth := by
  classical
  intro p n' R m lam0 hDom t c n D hD0 hDc hfac
  have hdnn := dL_nonneg R lam0
  by_cases hn0 : n = 0
  · subst hn0; simpa using hdnn
  have hL : IsLattice R.W (colSpan R.W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq)) := ⟨1, by simp, rfl⟩
  obtain ⟨Ne, es, hinj, hes, hNe⟩ := hcnt p n' R (m + 1) (by omega) _ hL
  have hc1 : 1 ≤ c := by
    have : (0 : ℝ) < c := by linarith
    exact_mod_cast this
  have hdata : ∀ i : Fin Ne, ∃ (x : Fin n → Vsp R.Kf lam0)
      (y : Fin n → Module.Dual R.Kf (Vsp R.Kf lam0)) (z z' : R.O), z ≠ 0 ∧
      (∀ a, x a ∈ CCL R lam0 t c (es i)) ∧ (∀ a, y a ∈ CCL' R lam0 t c (es i)) ∧
      z' * z = R.w ^ (c - 1) ∧
      ∀ a b, be p 1 lam0 (x a) (y b) = if a = b then algebraMap R.O R.Kf z else 0 := by
    intro i
    rcases hfac (es i) (hes i).1 with h0 | ⟨x, y, hx, hy, z, Mx, hz, hv, hM⟩
    · exact absurd h0 hn0
    · obtain ⟨z', hz'⟩ := dvd_w_pow_of_vLEO R.std.2.1 R.std.1.w_sq hz hDc hv
      refine ⟨x, fun b => ∑ l, Mx l b • y l, z, z', hz, hx,
        fun b => Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (hy l)), by rw [hz']; ring, fun a b => ?_⟩
      rw [be_sum]
      exact hM a b
  choose x y z z' hz0 hx hy hzz hxy using hdata
  have hβ : ∀ i l : Fin Ne × Fin n, ∃ β : R.O, β ∈ IsLocalRing.maximalIdeal R.O ∧
      be p 1 lam0 (x i.1 i.2) (y l.1 l.2) =
        algebraMap R.O R.Kf (((1 : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O) i l + β) * z l.1) := by
    rintro ⟨i, a⟩ ⟨l, b⟩
    by_cases hil : i = l
    · subst hil
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simp only
      rw [hxy, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp
      · have : ((i, a) : Fin Ne × Fin n) ≠ (i, b) := fun h => hab (Prod.mk.inj h).2
        rw [if_neg hab, if_neg this]; simp
    · have hne : es l ≠ es i := fun h => hil (hinj h).symm
      have hXs := CCL_other R lam0 t c (es i) (es l) (hes _).1 ((hes _).2.trans (hes _).2.symm) hne (hx i a)
      obtain ⟨b', hb⟩ := be_scale_Re R lam0 (es l) c hXs (hy l b).1.2
      have h2 : ((i, a) : Fin Ne × Fin n) ≠ (l, b) := fun h => hil (Prod.mk.inj h).1
      refine ⟨R.w * b' * z' l, Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ R.w_mem), ?_⟩
      simp only
      rw [hb, Matrix.one_apply_ne h2, zero_add]
      congr 1
      have h3 : R.w ^ c = R.w * R.w ^ (c - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h3, ← hzz l]
      ring
  choose β hβm hβe using hβ
  let P : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O := Matrix.of fun i l => (1 : Matrix _ _ R.O) i l + β i l
  have hP : IsUnit P.det := by
    apply isUnit_det_of_one_add'
    intro i l
    simpa [P] using hβm i l
  have hinjK : Function.Injective (algebraMap R.O R.Kf) := by
    have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
    exact IsFractionRing.injective R.O R.Kf
  have hPK : ((algebraMap R.O R.Kf).mapMatrix P).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    have : P.det = 0 := hinjK (by rw [h0, map_zero])
    rw [this] at hP
    exact not_isUnit_zero hP
  have hli : LinearIndependent R.Kf (fun i : Fin Ne × Fin n => x i.1 i.2) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ l : Fin Ne × Fin n, ∑ i, g i * algebraMap R.O R.Kf (P i l) = 0 := by
      intro l
      have h2 : be p 1 lam0 (∑ i, g i • x i.1 i.2) (y l.1 l.2) = 0 := by
        rw [hg]; simp [be]
      rw [be_sum_left] at h2
      have h3 : (∑ i, g i * algebraMap R.O R.Kf (P i l)) * algebraMap R.O R.Kf (z l.1) = 0 := by
        rw [← h2, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hβe i l, map_mul, mul_assoc]
        rfl
      have hz : algebraMap R.O R.Kf (z l.1) ≠ 0 := fun h => hz0 l.1 (hinjK (by rw [h, map_zero]))
      exact (mul_eq_zero.1 h3).resolve_right hz
    have h4 : Matrix.vecMul g ((algebraMap R.O R.Kf).mapMatrix P) = 0 := by
      funext l
      simpa [Matrix.vecMul, dotProduct] using h1 l
    have h5 := Matrix.eq_zero_of_vecMul_eq_zero hPK h4
    intro i
    rw [h5]; rfl
  have hpos : 0 < dimV R.Kf lam0 := Formalism.MainNotions.G.LatticeSystems.kp_dimV_pos R.Kf lam0 hDom
  have hfin : Module.Finite R.Kf (Vsp R.Kf lam0) := Module.finite_of_finrank_pos hpos
  have hcard : Ne * n ≤ dimV R.Kf lam0 := by
    have := hli.fintype_card_le_finrank
    simpa [dimV] using this
  have hNpos := gaussianNumber_prime_pow_pos R (m + 1) (by omega)
  unfold dL
  rw [le_div_iff₀ hNpos]
  have h6 : ((Ne * n : ℕ) : ℝ) ≤ (dimV R.Kf lam0 : ℝ) := by exact_mod_cast hcard
  have h7 : (n : ℝ) * gaussianNumber (p ^ n') (m + 1) ≤ (n : ℝ) * Ne := mul_le_mul_of_nonneg_left hNe (Nat.cast_nonneg _)
  push_cast at h6
  linarith

end Formalism.MainNotions.flipOneThree.Pf

end
