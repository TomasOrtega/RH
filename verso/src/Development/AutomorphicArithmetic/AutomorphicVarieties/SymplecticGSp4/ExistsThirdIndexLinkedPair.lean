import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.GeAlgTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EptInt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.XvanExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocVanP
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OrdFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.NormO
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Rewrite using `[residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]`. Break down `eq_or_ne b 0 with rfl | h0` into its components or cases. Simplify using the standard rewrite rules. Establish `h` using `UpperTheory.V.Base.normO l c.O b h0`. Establish `hl : ((l : ℝ)⁻¹) < 1` using `inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)`.

Prove the components needed by the constructor for the conclusion. Introduce `hb`. Establish `hv : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0`. Rewrite using `[Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff, IsDiscreteValuationRing.addVal_eq_top_iff]`. Conclude with `fun h => h.elim hb h0`.

Establish `h1` using `pow_lt_one₀ (by positivity) hl hv`. Rewrite `h1` using `[← h]`. Assume the negation of the conclusion as `hn`. Conclude with `absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))`. Introduce `hb hu`.

Take `⟨-, -, -, -, -, e0, hfin, -, -⟩` from `dvrFacts l c.O`. Establish `hE : (eO l c.O).toNat ≠ 0`. Rewrite using `[Ne, ENat.toNat_eq_zero, not_or]`. Conclude with `⟨e0, ne_top_of_le_ne_top (ENat.coe_ne_top _) hfin⟩`. Rewrite `h` using `[IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu]`.

Use `pow_lt_one₀ (norm_nonneg _) hb hE` as an intermediate fact. Rewrite `this` using `[h]`. Simplify using `at this`.
-/
private theorem mem_max_iff {l : ℕ} [Fact l.Prime] (c : Coef l) (b : c.O) :
    residue c.O b = 0 ↔ ‖(b : PadicAlgCl l)‖ < 1 := by
  rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff]
  rcases eq_or_ne b 0 with rfl | h0
  · simp
  have h := UpperTheory.V.Base.normO l c.O b h0
  have hl : ((l : ℝ)⁻¹) < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  constructor
  · intro hb
    have hv : (IsDiscreteValuationRing.addVal c.O b).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero, IsDiscreteValuationRing.addVal_eq_zero_iff,
        IsDiscreteValuationRing.addVal_eq_top_iff]
      exact fun h => h.elim hb h0
    have h1 := pow_lt_one₀ (by positivity) hl hv
    rw [← h] at h1
    by_contra hn
    exact absurd h1 (not_lt.2 (one_le_pow₀ (not_lt.1 hn)))
  · intro hb hu
    obtain ⟨-, -, -, -, -, e0, hfin, -, -⟩ := dvrFacts l c.O
    have hE : (eO l c.O).toNat ≠ 0 := by
      rw [Ne, ENat.toNat_eq_zero, not_or]
      exact ⟨e0, ne_top_of_le_ne_top (ENat.coe_ne_top _) hfin⟩
    rw [IsDiscreteValuationRing.addVal_eq_zero_iff.2 hu] at h
    have := pow_lt_one₀ (norm_nonneg _) hb hE
    rw [h] at this
    simp at this

/- English proof (translation)
Take `⟨-, -, -, -, -, h0, hfin, -, -⟩` from `dvrFacts l c.O`. Establish `hE : (eO l c.O).toNat ≠ 0`. Rewrite using `[Ne, ENat.toNat_eq_zero, not_or]`. Conclude with `⟨h0, ne_top_of_le_ne_top (ENat.coe_ne_top _) hfin⟩`. Establish `hl : (1 : ℝ) < l` using `by exact_mod_cast (Fact.out : l.Prime).one_lt`.

Establish `hl0 : (0 : ℝ) < (l : ℝ)⁻¹` using `by positivity`. Establish `hl1 : (l : ℝ)⁻¹ < 1` using `inv_lt_one_of_one_lt₀ hl`. Break down `eq_or_ne x 0 with rfl | hx` into its components or cases. Simplify using the standard rewrite rules. Use `normO l c.O x hx` as an intermediate fact.

Rewrite using `[← pow_le_one_iff_of_nonneg (norm_nonneg _) hE, this]`. Conclude with `pow_le_one₀ hl0.le hl1.le`.
-/
private theorem norm_le {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) : ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  obtain ⟨-, -, -, -, -, h0, hfin, -, -⟩ := dvrFacts l c.O
  have hE : (eO l c.O).toNat ≠ 0 := by
    rw [Ne, ENat.toNat_eq_zero, not_or]
    exact ⟨h0, ne_top_of_le_ne_top (ENat.coe_ne_top _) hfin⟩
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  have hl1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have := normO l c.O x hx
    rw [← pow_le_one_iff_of_nonneg (norm_nonneg _) hE, this]
    exact pow_le_one₀ hl0.le hl1.le

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `h : ∀ᶠ y in nhds x, ‖(f y : PadicAlgCl l) - f x‖ < 1`. Establish `hc : Continuous fun y => ‖(f y : PadicAlgCl l) - f x‖` using `(hf.sub continuous_const).norm`. Conclude with `hc.continuousAt.eventually_lt continuousAt_const (by simp)`.

Use `filter_upwards [h] with y hy`. Rewrite using `[← sub_eq_zero, ← map_sub, mem_max_iff]`. Simplify using `using hy`.
-/
private theorem locConst {l : ℕ} [Fact l.Prime] (c : Coef l) {X : Type} [TopologicalSpace X] (f : X → c.O)
    (hf : Continuous fun x => (f x : PadicAlgCl l)) : IsLocallyConstant fun x => residue c.O (f x) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h : ∀ᶠ y in nhds x, ‖(f y : PadicAlgCl l) - f x‖ < 1 := by
    have hc : Continuous fun y => ‖(f y : PadicAlgCl l) - f x‖ := (hf.sub continuous_const).norm
    exact hc.continuousAt.eventually_lt continuousAt_const (by simp)
  filter_upwards [h] with y hy
  rw [← sub_eq_zero, ← map_sub, mem_max_iff]
  simpa using hy

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨g1, hg1⟩ : ∃ g1, ∀ g, r g1 s u ∣ r g s u := by`. Take `⟨_, ⟨g1, rfl⟩, hmin⟩` from `(wellFounded_lt (α := ℕ∞)).has_min (Set.range fun g => IsDiscreteValuationRing.addVal O (r g s u)) ⟨_, 1, rfl⟩`. Conclude with `⟨g1, fun g => IsDiscreteValuationRing.addVal_le_iff_dvd.1 (not_lt.1 (hmin _ ⟨g, rfl⟩))⟩`. Use `choose c hc using hg1`. Establish `hb : r g1 s u ≠ 0`.

Take `⟨g, hg⟩` from `hne`. Introduce `h0`. Conclude with `hg (by rw [hc g, h0, zero_mul])`. Use `⟨_, c, hb, hc, fun m hm => ?_⟩` and prove the remaining obligations. Establish `key : ∀ h, residue O (c h) = m * residue O (r h s s)`.

Introduce `h`. Establish `e1` using `congrFun (congrFun (hE h) s) u`. Establish `e2` using `congrFun (congrFun (hE h) s) s`. Establish `e3` using `congrFun (congrFun (hE h) u) u`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_mul_apply_same, one_mul] at e1 e2 e3`.

Rewrite `e3` using `[Matrix.single_mul_apply_of_ne (h := hsu.symm)]`. Establish `e4 : ∑ g ∈ t, a g * c (g * h) = c h`. Apply `mul_left_cancel₀ hb` to reduce the goal to its premises. Rewrite using `[← hc, ← e1, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[hc (g * h)]`. Expand and normalize the polynomial expressions, which then agree. Establish `e5 : residue O (r h s s) = residue O (r h s s) - residue O 0` using `by simp`. Rewrite using `[← e4, e5, ← e3]`. Use `conv_rhs => rw [← e2]`.

Simplify using `only [map_sum, map_mul, hm, ← Finset.sum_sub_distrib, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `c1 : c 1 = 0`. Use `hc 1` as an intermediate fact.

Rewrite `this` using `[h1, Matrix.one_apply_ne hsu]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left hb`. Establish `hm0 : m = 0`. Use `key 1` as an intermediate fact. Rewrite `this` using `[c1, h1]`.

Simplify using `using this.symm`. Establish `cg : c g1 = 1`. Apply `mul_left_cancel₀ hb` to reduce the goal to its premises. Rewrite using `[← hc, mul_one]`. Use `key g1` as an intermediate fact.

Rewrite `this` using `[cg, hm0]`. Simplify using `at this`.
-/
private theorem lattice {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {H : Type} [Group H]
    (r : H → M4 O) (h1 : r 1 = 1) (s u : Fin 4) (hsu : s ≠ u) (hne : ∃ g, r g s u ≠ 0) (t : Finset H) (a : H → O)
    (hE : ∀ h, ∑ g ∈ t, a g • r (g * h) = Matrix.single s s (1 : O) * r h) :
    ∃ (b : O) (c : H → O), b ≠ 0 ∧ (∀ g, r g s u = b * c g) ∧
      ∀ m, ¬ ∀ g, residue O (c g) = m * (residue O (r g s s) - residue O (r g u u)) := by
  obtain ⟨g1, hg1⟩ : ∃ g1, ∀ g, r g1 s u ∣ r g s u := by
    obtain ⟨_, ⟨g1, rfl⟩, hmin⟩ := (wellFounded_lt (α := ℕ∞)).has_min
      (Set.range fun g => IsDiscreteValuationRing.addVal O (r g s u)) ⟨_, 1, rfl⟩
    exact ⟨g1, fun g => IsDiscreteValuationRing.addVal_le_iff_dvd.1 (not_lt.1 (hmin _ ⟨g, rfl⟩))⟩
  choose c hc using hg1
  have hb : r g1 s u ≠ 0 := by
    obtain ⟨g, hg⟩ := hne
    intro h0
    exact hg (by rw [hc g, h0, zero_mul])
  refine ⟨_, c, hb, hc, fun m hm => ?_⟩
  have key : ∀ h, residue O (c h) = m * residue O (r h s s) := by
    intro h
    have e1 := congrFun (congrFun (hE h) s) u
    have e2 := congrFun (congrFun (hE h) s) s
    have e3 := congrFun (congrFun (hE h) u) u
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.single_mul_apply_same, one_mul] at e1 e2 e3
    rw [Matrix.single_mul_apply_of_ne (h := hsu.symm)] at e3
    have e4 : ∑ g ∈ t, a g * c (g * h) = c h := by
      apply mul_left_cancel₀ hb
      rw [← hc, ← e1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hc (g * h)]; ring
    have e5 : residue O (r h s s) = residue O (r h s s) - residue O 0 := by simp
    rw [← e4, e5, ← e3]
    conv_rhs => rw [← e2]
    simp only [map_sum, map_mul, hm, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    ring
  have c1 : c 1 = 0 := by
    have := hc 1
    rw [h1, Matrix.one_apply_ne hsu] at this
    exact (mul_eq_zero.1 this.symm).resolve_left hb
  have hm0 : m = 0 := by
    have := key 1
    rw [c1, h1] at this
    simpa using this.symm
  have cg : c g1 = 1 := by
    apply mul_left_cancel₀ hb
    rw [← hc, mul_one]
  have := key g1
  rw [cg, hm0] at this
  simp at this

/- English proof (translation)
Set `Q : ℕ → Prop` to `fun n => ∃ x : Fin 4 → K, (∀ k, ¬ P k → x k = 0) ∧ (∀ b : Fin 4, n ≤ b → (u : M4 K).mulVec x b = 0) ∧ (x i ≠ 0 ∨ x j ≠ 0)`. Establish `hQ : ∃ n, Q n` using `⟨4, Pi.single i 1, fun k hk => Pi.single_eq_of_ne (fun h : k = i => hk (h ▸ hi)) _, fun b hb => absurd b.2 (not_lt.2 hb), Or.inl (by simp)⟩`. Establish `h4 : Nat.find hQ ≤ 4` using `Nat.find_min' hQ ⟨Pi.single i 1, fun k hk => Pi.single_eq_of_ne (fun h : k = i => hk (h ▸ hi)) _, fun b hb => absurd b.2 (not_lt.2 hb), Or.inl (by simp)⟩`. Take `⟨x, hx1, hx2, hx3⟩` from `Nat.find_spec hQ`. Establish `hinv : ∀ z : Fin 4 → K, ((u⁻¹ : (M4 K)ˣ) : M4 K).mulVec ((u : M4 K).mulVec z) = z` using `fun z => by`.

Rewrite using `[Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]`. Establish `h0 : Nat.find hQ ≠ 0`. Introduce `h`. Establish `: (u : M4 K).mulVec x = 0` using `funext fun b => hx2 b (by omega)`. Establish `hx` using `hinv x`.

Rewrite `hx` using `[this, Matrix.mulVec_zero]`. Rewrite `hx3` using `[← hx]`. Simplify using `at hx3`. Set `a : Fin 4` to `⟨Nat.find hQ - 1, by omega⟩`. Establish `hmin` using `Nat.find_min hQ (m := a) (by simp only [a]; omega)`.

Use `⟨x i, x j, fun g => ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) a a, hx3, fun g => ?_⟩` and prove the remaining obligations. Use `set T : M4 K := (u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ) with hT`. Establish `hy : ¬ (((r g).mulVec x - T a a • x) i ≠ 0 ∨ ((r g).mulVec x - T a a • x) j ≠ 0)`. Introduce `hy`. Use `hmin ⟨_, fun k hk => ?_, fun b hb => ?_, hy⟩` and prove the remaining obligations.

Rewrite using `[Pi.sub_apply, Pi.smul_apply, hx1 k hk, smul_zero, sub_zero, Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : P b`. Rewrite using `[hP g k b hb hk, zero_mul]`. Rewrite using `[hx1 b hb, mul_zero]`.

Establish `e : (u : M4 K).mulVec ((r g).mulVec x) = T.mulVec ((u : M4 K).mulVec x)`. Rewrite using `[hT, ← Matrix.mulVec_mulVec, hinv, Matrix.mulVec_mulVec]`. Rewrite using `[Matrix.mulVec_sub, Matrix.mulVec_smul, e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]`. Establish `hba : a ≤ b` using `hb`. Rewrite using `[show T.mulVec ((u : M4 K).mulVec x) b = ∑ d, T b d * (u : M4 K).mulVec x d from rfl]`.

Rewrite using `[Finset.sum_eq_single a]`. Break down `hba.eq_or_lt with h | h` into its components or cases. Rewrite using `[h]`. Rewrite using `[show T b a = 0 from tri g b a h, zero_mul, hx2 b (by have : (a : ℕ) < b := h; simp only [a] at this; omega), mul_zero]`. Introduce `d _ hd`.

Break down `lt_or_gt_of_ne hd with h | h` into its components or cases. Rewrite using `[show T b d = 0 from tri g b d (h.trans_le hba), zero_mul]`. Rewrite using `[hx2 d (by have : (a : ℕ) < d := h; simp only [a] at this; omega), mul_zero]`. Simplify using the standard rewrite rules. Rewrite `hy` using `[not_or, not_not, not_not]`.

Establish `hs : ∀ w, (∀ k, P k → k ≠ i → k ≠ j → r g w k = 0) → (r g).mulVec x w = r g w i * x i + r g w j * x j`. Introduce `w hw`. Rewrite using `[Matrix.mulVec, dotProduct, ← Finset.sum_pair (f := fun k => r g w k * x k) hij]`. Use `symm`. Use `Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_` and prove the remaining obligations.

Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk`. Distinguish the cases in `hb : P k`. Rewrite using `[hw k hb hk.1 hk.2, zero_mul]`. Rewrite using `[hx1 k hb, mul_zero]`. Rewrite `hy` using `[Pi.sub_apply, Pi.sub_apply, hs i fun k a b c => (hz g k a b c).1, hs j fun k a b c => (hz g k a b c).2]`.

Conclude with `⟨sub_eq_zero.1 hy.1, sub_eq_zero.1 hy.2⟩`.
-/
private theorem line {H K : Type} [Field K] (r : H → M4 K) (u : (M4 K)ˣ)
    (tri : ∀ g i j, j < i → ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) i j = 0) (P : Fin 4 → Prop) (i j : Fin 4) (hij : i ≠ j)
    (hi : P i) (hP : ∀ g a b, P b → ¬ P a → r g a b = 0) (hz : ∀ g k, P k → k ≠ i → k ≠ j → r g i k = 0 ∧ r g j k = 0) :
    ∃ (x y : K) (φ : H → K), (x ≠ 0 ∨ y ≠ 0) ∧ ∀ g, r g i i * x + r g i j * y = φ g * x ∧ r g j i * x + r g j j * y = φ g * y := by
  classical
  let Q : ℕ → Prop := fun n => ∃ x : Fin 4 → K, (∀ k, ¬ P k → x k = 0) ∧ (∀ b : Fin 4, n ≤ b → (u : M4 K).mulVec x b = 0) ∧
    (x i ≠ 0 ∨ x j ≠ 0)
  have hQ : ∃ n, Q n := ⟨4, Pi.single i 1, fun k hk => Pi.single_eq_of_ne (fun h : k = i => hk (h ▸ hi)) _,
    fun b hb => absurd b.2 (not_lt.2 hb), Or.inl (by simp)⟩
  have h4 : Nat.find hQ ≤ 4 := Nat.find_min' hQ ⟨Pi.single i 1, fun k hk => Pi.single_eq_of_ne (fun h : k = i => hk (h ▸ hi)) _,
    fun b hb => absurd b.2 (not_lt.2 hb), Or.inl (by simp)⟩
  obtain ⟨x, hx1, hx2, hx3⟩ := Nat.find_spec hQ
  have hinv : ∀ z : Fin 4 → K, ((u⁻¹ : (M4 K)ˣ) : M4 K).mulVec ((u : M4 K).mulVec z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have h0 : Nat.find hQ ≠ 0 := by
    intro h
    have : (u : M4 K).mulVec x = 0 := funext fun b => hx2 b (by omega)
    have hx := hinv x
    rw [this, Matrix.mulVec_zero] at hx
    rw [← hx] at hx3
    simp at hx3
  let a : Fin 4 := ⟨Nat.find hQ - 1, by omega⟩
  have hmin := Nat.find_min hQ (m := a) (by simp only [a]; omega)
  refine ⟨x i, x j, fun g => ((u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ)) a a, hx3, fun g => ?_⟩
  set T : M4 K := (u : M4 K) * r g * (u⁻¹ : (M4 K)ˣ) with hT
  have hy : ¬ (((r g).mulVec x - T a a • x) i ≠ 0 ∨ ((r g).mulVec x - T a a • x) j ≠ 0) := by
    intro hy
    refine hmin ⟨_, fun k hk => ?_, fun b hb => ?_, hy⟩
    · rw [Pi.sub_apply, Pi.smul_apply, hx1 k hk, smul_zero, sub_zero, Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun b _ => ?_
      by_cases hb : P b
      · rw [hP g k b hb hk, zero_mul]
      · rw [hx1 b hb, mul_zero]
    · have e : (u : M4 K).mulVec ((r g).mulVec x) = T.mulVec ((u : M4 K).mulVec x) := by
        rw [hT, ← Matrix.mulVec_mulVec, hinv, Matrix.mulVec_mulVec]
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, e, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_eq_zero]
      have hba : a ≤ b := hb
      rw [show T.mulVec ((u : M4 K).mulVec x) b = ∑ d, T b d * (u : M4 K).mulVec x d from rfl]
      rw [Finset.sum_eq_single a]
      · rcases hba.eq_or_lt with h | h
        · rw [h]
        · rw [show T b a = 0 from tri g b a h, zero_mul, hx2 b (by have : (a : ℕ) < b := h; simp only [a] at this; omega), mul_zero]
      · intro d _ hd
        rcases lt_or_gt_of_ne hd with h | h
        · rw [show T b d = 0 from tri g b d (h.trans_le hba), zero_mul]
        · rw [hx2 d (by have : (a : ℕ) < d := h; simp only [a] at this; omega), mul_zero]
      · simp
  rw [not_or, not_not, not_not] at hy
  have hs : ∀ w, (∀ k, P k → k ≠ i → k ≠ j → r g w k = 0) → (r g).mulVec x w = r g w i * x i + r g w j * x j := by
    intro w hw
    rw [Matrix.mulVec, dotProduct, ← Finset.sum_pair (f := fun k => r g w k * x k) hij]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    by_cases hb : P k
    · rw [hw k hb hk.1 hk.2, zero_mul]
    · rw [hx1 k hb, mul_zero]
  rw [Pi.sub_apply, Pi.sub_apply, hs i fun k a b c => (hz g k a b c).1, hs j fun k a b c => (hz g k a b c).2] at hy
  exact ⟨sub_eq_zero.1 hy.1, sub_eq_zero.1 hy.2⟩

/- English proof (translation)
Establish `e1 : D.th * D.Psi⁻¹ = D.al` using `by rw [Raw.th, mul_inv_cancel_right]`. Establish `e2 : D.Psi * D.th⁻¹ = D.al⁻¹` using `by rw [← e1, mul_inv_rev, inv_inv]`. Establish `e3 : D.Psi * D.al⁻¹ = D.be` using `rfl`. Establish `e4 : D.al * D.Psi⁻¹ = D.be⁻¹` using `by rw [← e3, mul_inv_rev, inv_inv]`. Apply the tactic sequence `fin_cases s <;> fin_cases u <;> simp [lamW] at h <;> simp [Raw.ps, e1, e2, e3, e4]`.
-/
private theorem root_mem {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (s u : Fin 4) (h : lamW s ≠ lamW u) : D.ps s * (D.ps u)⁻¹ ∈ [D.al, D.be, D.th, D.al⁻¹, D.be⁻¹, D.th⁻¹] := by
  have e1 : D.th * D.Psi⁻¹ = D.al := by rw [Raw.th, mul_inv_cancel_right]
  have e2 : D.Psi * D.th⁻¹ = D.al⁻¹ := by rw [← e1, mul_inv_rev, inv_inv]
  have e3 : D.Psi * D.al⁻¹ = D.be := rfl
  have e4 : D.al * D.Psi⁻¹ = D.be⁻¹ := by rw [← e3, mul_inv_rev, inv_inv]
  fin_cases s <;> fin_cases u <;> simp [lamW] at h <;> simp [Raw.ps, e1, e2, e3, e4]

/- English proof (translation)
Establish `hne : s ≠ u` using `fun h => hsu (h ▸ rfl)`. Take `⟨hcont, hnorm, c', hle, hmem, hE⟩` from `eptInt D hD r hr`. Take `⟨-, hunr, -⟩` from `ptIn D hD _ r hr`. Take `⟨-, hsg, -⟩` from `facts D hD`. Take `⟨hsg1, -, hsg2⟩` from `hsg l (Finset.mem_insert_self _ _)`.

Take `⟨t, a, ha, hE⟩` from `hE s`. Set `R : G ℚ Ω → M4 c'.O` to `fun g => Matrix.of fun i j => ⟨r g i j, hmem g i j⟩`. Establish `hR : ∀ g i j, (R g i j : PadicAlgCl l) = r g i j` using `fun _ _ _ => rfl`. Establish `hmap : ∀ g, (R g).map c'.O.val = r g` using `fun _ => rfl`. Establish `hinj : Function.Injective fun X : M4 c'.O => X.map c'.O.val` using `Matrix.map_injective Subtype.val_injective`.

Take `⟨b, cc, hb, hc, hns⟩` from `lattice R (by`. Apply `hinj` to reduce the goal to its premises. Simplify using `only [hmap, map_one]`. Conclude with `(Matrix.map_one _ (map_zero _) (map_one _)).symm) s u hne`. Use the proof step `(by`.

Take `⟨g, hg⟩` from `hge`. Conclude with `⟨g, fun h => hg (by rw [← hR, h]; rfl)⟩) t (fun g => ⟨a g, ha g⟩) (by`. Introduce `h`. Establish `e : ∑ g ∈ t, a g • r (g * h) = Matrix.single s s (1 : PadicAlgCl l) * r h`. Rewrite using `[hE, Finset.sum_mul]`.

Simplify using `only [map_mul, smul_mul_assoc]`. Use extensionality with `i j`. Establish `e'` using `congrFun (congrFun e i) j`. Simplify using `only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at e' ⊢`. Use `push_cast`.

Simplify using `only [hR]`. Rewrite using `[e']`. Distinguish the cases in `hi : i = s`. Substitute `hi` using the available equality. Simplify using `[hR]`.

Rewrite using `[Matrix.single_mul_apply_of_ne (h := hi), Matrix.single_mul_apply_of_ne (h := hi)]`. Use the proof step `rfl)`. Establish `hbK : (b : PadicAlgCl l) ≠ 0` using `fun h => hb (Subtype.ext h)`. Establish `hcK : ∀ g, r g s u = b * cc g` using `fun g => by rw [← hR, hc]; rfl`. Use `haveI : Finite (ResidueField c'.O) := (UpperTheory.V.abelian₂.dvr_finite l c'.O).2.1`.

Set `red : c.O →+* ResidueField c'.O` to `(residue c'.O).comp (Subalgebra.inclusion hle).toRingHom`. Establish `hred : ∀ x : c.O, red x = 0 ↔ residue c.O x = 0` using `fun x => by`. Rewrite using `[mem_max_iff]`. Conclude with `mem_max_iff c' _`. Establish `hred0 : ∀ x ∈ maximalIdeal c.O, red x = 0` using `fun x hx => (hred x).2 ((residue_eq_zero_iff x).2 hx)`.

Establish `hdiag : ∀ g i, residue c'.O (R g i i) = red (D.ps i g : c.O)` using `fun g i => by`. Use `hnorm g i i` as an intermediate fact. Rewrite using `[← sub_eq_zero]`. Express the relevant statement in the definitionally equal form `residue c'.O _ - residue c'.O _ = 0`. Rewrite using `[← map_sub, mem_max_iff]`.

Simplify `this` using `[Raw.r0E, Raw.r0, diagRep, hR]`. Establish `hoff : ∀ g, ‖r g u s‖ < 1` using `fun g => by`. Use `hnorm g u s` as an intermediate fact. Simplify `this` using `[Raw.r0E, Raw.r0, diagRep, Matrix.diagonal_apply_ne _ hne.symm]`. Establish `hU : ∀ g, red (D.ps u g : c.O) ≠ 0` using `fun g => ((D.ps u g).isUnit.map red).ne_zero`.

Establish `hγ : ∀ g, red ((D.ps s * (D.ps u)⁻¹) g : c.O) = red (D.ps s g : c.O) / red (D.ps u g : c.O)` using `fun g => by`. Rewrite using `[eq_div_iff (hU g), ← map_mul, ← Units.val_mul]`. Simplify using the standard rewrite rules. Set `z : G ℚ Ω → ResidueField c'.O` to `fun g => residue c'.O (cc g) / red (D.ps u g : c.O)`. Establish `hent : ∀ i j, Continuous fun g => r g i j` using `fun i j => (continuous_apply_apply i j).comp hcont`.

Establish `hzl : IsLocallyConstant z`. Establish `a1` using `locConst c' cc (by`. Establish `: (fun g => (cc g : PadicAlgCl l)) = fun g => r g s u / b` using `funext fun g => by`. Rewrite using `[hcK, mul_div_cancel_left₀ _ hbK]`. Rewrite using `[this]`.

Conclude with `(hent s u).div_const _)`. Establish `a2` using `locConst c' (fun g => R g u u) (hent u u)`. Simplify using `only [hdiag] at a2`. Conclude with `a1.comp₂ a2 fun x y => x / y`. Establish `hcoc : ∀ g h, z (g * h) = z g + red ((D.ps s * (D.ps u)⁻¹) g : c.O) * z h` using `fun g h => by`.

Establish `e : cc (g * h) = R g s s * cc h + cc g * R h u u`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `mul_left_cancel₀ hbK` to reduce the goal to its premises. Use `push_cast`. Rewrite using `[← hcK, hmul, hR, hR, hcK g, hcK h]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [z]`. Rewrite using `[hγ, e, map_add, map_mul, map_mul, hdiag, hdiag, map_mul, Units.val_mul, map_mul]`. Use `hU g` as an intermediate fact. Use `hU h` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨m, hm⟩` from `xvanExt D hD _ red hred0 _ (root_mem D s u hsu) z hzl hcoc (by`. Introduce `A hA g hg h1`. Establish `e` using `hcK g`.

Rewrite `e` using `[hunr A hA g hg h1, Matrix.one_apply_ne hne]`. Establish `: cc g = 0` using `Subtype.ext ((mul_eq_zero.1 e.symm).resolve_left hbK)`. Simplify using `only [z, this, map_zero, zero_div]) (by`. Introduce `p hp`. Break down `Finset.mem_insert.1 hp with rfl | hp` into its components or cases.

Establish `hd : red (D.ps u (D.sg p) : c.O) - red (D.ps s (D.sg p) : c.O) ≠ 0`. Rewrite using `[← map_sub, Ne, hred, map_sub, sub_eq_zero]`. Conclude with `hsg2 u s hsu.symm`. Use `⟨-(residue c'.O (cc (D.sg p)) / (red (D.ps u (D.sg p) : c.O) - red (D.ps s (D.sg p) : c.O))), fun g hg => ?_⟩` and prove the remaining obligations. Establish `e : residue c'.O (cc g * (R (D.sg p) u u - R (D.sg p) s s) - cc (D.sg p) * (R g u u - R g s s)) = 0`.

Rewrite using `[mem_max_iff]`. Establish `e1` using `hl g hg`. Establish `e2` using `hl _ hsg1`. Rewrite `e1`, `e2` using `[hcK]`. Establish `e3 : ((cc g * (R (D.sg p) u u - R (D.sg p) s s) - cc (D.sg p) * (R g u u - R g s s) : c'.O) : PadicAlgCl p) = cc (D.sg p) * v * r g u s + -(cc g * v * r (D.sg p) u s)`.

Apply `mul_left_cancel₀ hbK` to reduce the goal to its premises. Use `push_cast`. Simplify using `only [hR]`. Take the linear combination `(r (D.sg p) u s * v + r (D.sg p) u u - r (D.sg p) s s) * e1 - (r g u s * v + r g u u - r g s s) * e2`. Establish `n : ∀ (x : c'.O) g, ‖(x : PadicAlgCl p) * v * r g u s‖ < 1` using `fun x g => by`.

Rewrite using `[norm_mul, norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right (mul_le_one₀ (norm_le c' x) (norm_nonneg _) hv) (norm_nonneg _) (hoff g)`. Rewrite using `[e3]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (n _ _) ?_)` and prove the remaining obligations. Rewrite using `[norm_neg]`.

Conclude with `n _ _`. Simplify using `only [map_sub, map_mul, hdiag] at e`. Simplify using `only [z]`. Rewrite using `[hγ]`. Use `hU g` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Take the linear combination `e`. Take `⟨m, hm⟩` from `locVanP D hD hL _ red hred0 _ (root_mem D s u hsu) p hp (fun g => z g) (hzl.comp_continuous continuous_subtype_val) (fun g h => hcoc g h)`. Conclude with `⟨m, fun g hg => hm ⟨g, hg⟩⟩)`. Use `hns m fun g => ?_` and prove the remaining obligations.

Use `hm g` as an intermediate fact. Simplify using `only [z] at this`. Rewrite `this` using `[hγ, div_eq_iff (hU g)]`. Rewrite using `[this, hdiag, hdiag]`. Use `hU g` as an intermediate fact.

Clear the denominators using the available nonvanishing facts.
-/
private theorem core {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c)
    (hD : D.Good) (hL : Loc.LocalPublishedTheorems) (r : G ℚ Ω →* M4 (PadicAlgCl l)) (hr : D.EPt r) (s u : Fin 4) (hsu : lamW s ≠ lamW u)
    (hge : Ge r s u) (hmul : ∀ g h, r (g * h) s u = r g s s * r h s u + r g s u * r h u u) (v : PadicAlgCl l) (hv : ‖v‖ ≤ 1)
    (hl : ∀ g ∈ D.Gp l, r g s s * v + r g s u = (r g u s * v + r g u u) * v) : False := by
  have hne : s ≠ u := fun h => hsu (h ▸ rfl)
  obtain ⟨hcont, hnorm, c', hle, hmem, hE⟩ := eptInt D hD r hr
  obtain ⟨-, hunr, -⟩ := ptIn D hD _ r hr
  obtain ⟨-, hsg, -⟩ := facts D hD
  obtain ⟨hsg1, -, hsg2⟩ := hsg l (Finset.mem_insert_self _ _)
  obtain ⟨t, a, ha, hE⟩ := hE s
  let R : G ℚ Ω → M4 c'.O := fun g => Matrix.of fun i j => ⟨r g i j, hmem g i j⟩
  have hR : ∀ g i j, (R g i j : PadicAlgCl l) = r g i j := fun _ _ _ => rfl
  have hmap : ∀ g, (R g).map c'.O.val = r g := fun _ => rfl
  have hinj : Function.Injective fun X : M4 c'.O => X.map c'.O.val := Matrix.map_injective Subtype.val_injective
  obtain ⟨b, cc, hb, hc, hns⟩ := lattice R (by
      apply hinj
      simp only [hmap, map_one]
      exact (Matrix.map_one _ (map_zero _) (map_one _)).symm) s u hne
    (by
      obtain ⟨g, hg⟩ := hge
      exact ⟨g, fun h => hg (by rw [← hR, h]; rfl)⟩) t (fun g => ⟨a g, ha g⟩) (by
      intro h
      have e : ∑ g ∈ t, a g • r (g * h) = Matrix.single s s (1 : PadicAlgCl l) * r h := by
        rw [hE, Finset.sum_mul]
        simp only [map_mul, smul_mul_assoc]
      ext i j
      have e' := congrFun (congrFun e i) j
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at e' ⊢
      push_cast
      simp only [hR]
      rw [e']
      by_cases hi : i = s
      · subst hi
        simp [hR]
      · rw [Matrix.single_mul_apply_of_ne (h := hi), Matrix.single_mul_apply_of_ne (h := hi)]; rfl)
  have hbK : (b : PadicAlgCl l) ≠ 0 := fun h => hb (Subtype.ext h)
  have hcK : ∀ g, r g s u = b * cc g := fun g => by rw [← hR, hc]; rfl
  haveI : Finite (ResidueField c'.O) := (UpperTheory.V.abelian₂.dvr_finite l c'.O).2.1
  let red : c.O →+* ResidueField c'.O := (residue c'.O).comp (Subalgebra.inclusion hle).toRingHom
  have hred : ∀ x : c.O, red x = 0 ↔ residue c.O x = 0 := fun x => by
    rw [mem_max_iff]; exact mem_max_iff c' _
  have hred0 : ∀ x ∈ maximalIdeal c.O, red x = 0 := fun x hx => (hred x).2 ((residue_eq_zero_iff x).2 hx)
  have hdiag : ∀ g i, residue c'.O (R g i i) = red (D.ps i g : c.O) := fun g i => by
    have := hnorm g i i
    rw [← sub_eq_zero]
    change residue c'.O _ - residue c'.O _ = 0
    rw [← map_sub, mem_max_iff]
    simpa [Raw.r0E, Raw.r0, diagRep, hR] using this
  have hoff : ∀ g, ‖r g u s‖ < 1 := fun g => by
    have := hnorm g u s
    simpa [Raw.r0E, Raw.r0, diagRep, Matrix.diagonal_apply_ne _ hne.symm] using this
  have hU : ∀ g, red (D.ps u g : c.O) ≠ 0 := fun g => ((D.ps u g).isUnit.map red).ne_zero
  have hγ : ∀ g, red ((D.ps s * (D.ps u)⁻¹) g : c.O) = red (D.ps s g : c.O) / red (D.ps u g : c.O) := fun g => by
    rw [eq_div_iff (hU g), ← map_mul, ← Units.val_mul]
    simp
  let z : G ℚ Ω → ResidueField c'.O := fun g => residue c'.O (cc g) / red (D.ps u g : c.O)
  have hent : ∀ i j, Continuous fun g => r g i j := fun i j => (continuous_apply_apply i j).comp hcont
  have hzl : IsLocallyConstant z := by
    have a1 := locConst c' cc (by
      have : (fun g => (cc g : PadicAlgCl l)) = fun g => r g s u / b := funext fun g => by
        rw [hcK, mul_div_cancel_left₀ _ hbK]
      rw [this]
      exact (hent s u).div_const _)
    have a2 := locConst c' (fun g => R g u u) (hent u u)
    simp only [hdiag] at a2
    exact a1.comp₂ a2 fun x y => x / y
  have hcoc : ∀ g h, z (g * h) = z g + red ((D.ps s * (D.ps u)⁻¹) g : c.O) * z h := fun g h => by
    have e : cc (g * h) = R g s s * cc h + cc g * R h u u := by
      apply Subtype.ext
      apply mul_left_cancel₀ hbK
      push_cast
      rw [← hcK, hmul, hR, hR, hcK g, hcK h]
      ring
    simp only [z]
    rw [hγ, e, map_add, map_mul, map_mul, hdiag, hdiag, map_mul, Units.val_mul, map_mul]
    have := hU g
    have := hU h
    field_simp
    ring
  obtain ⟨m, hm⟩ := xvanExt D hD _ red hred0 _ (root_mem D s u hsu) z hzl hcoc (by
      intro A hA g hg h1
      have e := hcK g
      rw [hunr A hA g hg h1, Matrix.one_apply_ne hne] at e
      have : cc g = 0 := Subtype.ext ((mul_eq_zero.1 e.symm).resolve_left hbK)
      simp only [z, this, map_zero, zero_div]) (by
      intro p hp
      rcases Finset.mem_insert.1 hp with rfl | hp
      · have hd : red (D.ps u (D.sg p) : c.O) - red (D.ps s (D.sg p) : c.O) ≠ 0 := by
          rw [← map_sub, Ne, hred, map_sub, sub_eq_zero]
          exact hsg2 u s hsu.symm
        refine ⟨-(residue c'.O (cc (D.sg p)) / (red (D.ps u (D.sg p) : c.O) - red (D.ps s (D.sg p) : c.O))), fun g hg => ?_⟩
        have e : residue c'.O (cc g * (R (D.sg p) u u - R (D.sg p) s s) - cc (D.sg p) * (R g u u - R g s s)) = 0 := by
          rw [mem_max_iff]
          have e1 := hl g hg
          have e2 := hl _ hsg1
          rw [hcK] at e1 e2
          have e3 : ((cc g * (R (D.sg p) u u - R (D.sg p) s s) - cc (D.sg p) * (R g u u - R g s s) : c'.O) : PadicAlgCl p) =
              cc (D.sg p) * v * r g u s + -(cc g * v * r (D.sg p) u s) := by
            apply mul_left_cancel₀ hbK
            push_cast
            simp only [hR]
            linear_combination (r (D.sg p) u s * v + r (D.sg p) u u - r (D.sg p) s s) * e1 - (r g u s * v + r g u u - r g s s) * e2
          have n : ∀ (x : c'.O) g, ‖(x : PadicAlgCl p) * v * r g u s‖ < 1 := fun x g => by
            rw [norm_mul, norm_mul]
            exact mul_lt_one_of_nonneg_of_lt_one_right (mul_le_one₀ (norm_le c' x) (norm_nonneg _) hv) (norm_nonneg _) (hoff g)
          rw [e3]
          refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (n _ _) ?_)
          rw [norm_neg]
          exact n _ _
        simp only [map_sub, map_mul, hdiag] at e
        simp only [z]
        rw [hγ]
        have := hU g
        field_simp
        linear_combination e
      · obtain ⟨m, hm⟩ := locVanP D hD hL _ red hred0 _ (root_mem D s u hsu) p hp (fun g => z g)
          (hzl.comp_continuous continuous_subtype_val) (fun g h => hcoc g h)
        exact ⟨m, fun g hg => hm ⟨g, hg⟩⟩)
  refine hns m fun g => ?_
  have := hm g
  simp only [z] at this
  rw [hγ, div_eq_iff (hU g)] at this
  rw [this, hdiag, hdiag]
  have := hU g
  field_simp

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD hL r hr i j hij gij gji`. Assume the negation of the conclusion as `hno`. Establish `hne : i ≠ j` using `fun h => hij (h ▸ rfl)`. Take `⟨hmult, -, -, heq, -, hE, -⟩` from `ptIn D hD _ r hr`. Take `⟨-, grefl, gtr, -⟩` from `geAlg _ r _ hmult hE`.

Take `⟨-, -, -, -, -, -, hinj, -⟩` from `facts D hD`. Establish `hk : ∀ k, k ≠ i → k ≠ j → Ge r i k → Ge r k i → False` using `fun k a b x y => hno ⟨k, a, b, x, y⟩`. Establish `hmul : ∀ a b, Ge r i a → Ge r b i → ∀ g h, r (g * h) a b = r g a i * r h i b + r g a j * r h j b`. Introduce `a b ha hb g h`. Rewrite using `[map_mul, Matrix.mul_apply, ← Finset.sum_pair (f := fun k => r g a k * r h k b) hne]`.

Use `symm`. Use `Finset.sum_subset (Finset.subset_univ _) fun k _ hk' => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'`. Assume the negation of the conclusion as `h0`. Rewrite `h0` using `[mul_eq_zero, not_or]`.

Conclude with `hk k hk'.1 hk'.2 (gtr _ _ _ ha ⟨g, h0.1⟩) (gtr _ _ _ ⟨h, h0.2⟩ hb)`. Take `⟨u, -, tri, -⟩` from `ordFlag _ _ _ _ _ (fun a b h => hinj (Subtype.ext h)) heq.2`. Take `⟨x, y, φ, hxy, hφ⟩` from `line (fun g : D.Gp l => r g) u tri (fun k => Ge r k i) i j hne (grefl i) (fun g a b hb ha => by_contra fun h => ha (gtr _ _ _ ⟨g, h⟩ hb)) (fun g k h a b => ⟨by_contra fun h' => hk k a b ⟨g, h'⟩ h, by_contra fun h' => hk k a b (gtr _ _ _ gij ⟨g, h'⟩) h⟩)`. Break down `le_total ‖x‖ ‖y‖ with h | h` into its components or cases. Establish `hy : y ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at h hxy`. Conclude with `hxy h`. Use `core D hD hL r hr i j hij gij (hmul i j (grefl i) gji) (x / y) (by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)) fun g hg => ?_` and prove the remaining obligations. Take `⟨e1, e2⟩` from `hφ ⟨g, hg⟩`.

Simplify using `only at e1 e2`. Clear the denominators using the available nonvanishing facts. Take the linear combination `y * e1 - x * e2`. Establish `hx : x ≠ 0`. Introduce and unpack `rfl`.

Simplify using `at h hxy`. Conclude with `hxy h`. Use `core D hD hL r hr j i hij.symm gji (fun g h => by rw [hmul j i gij (grefl i), add_comm]) (y / x) (by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)) fun g hg => ?_` and prove the remaining obligations. Take `⟨e1, e2⟩` from `hφ ⟨g, hg⟩`. Simplify using `only at e1 e2`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `x * e2 - y * e1`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.exists_third_index_linked_pair :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → ∀ r, D.EPt r → ∀ i j, lamW i ≠ lamW j → Ge r i j → Ge r j i → ∃ k, k ≠ i ∧ k ≠ j ∧ Ge r i k ∧ Ge r k i := by
  intro Ω _ _ _ l _ c D hD hL r hr i j hij gij gji
  by_contra hno
  have hne : i ≠ j := fun h => hij (h ▸ rfl)
  obtain ⟨hmult, -, -, heq, -, hE, -⟩ := ptIn D hD _ r hr
  obtain ⟨-, grefl, gtr, -⟩ := geAlg _ r _ hmult hE
  obtain ⟨-, -, -, -, -, -, hinj, -⟩ := facts D hD
  have hk : ∀ k, k ≠ i → k ≠ j → Ge r i k → Ge r k i → False := fun k a b x y => hno ⟨k, a, b, x, y⟩
  have hmul : ∀ a b, Ge r i a → Ge r b i → ∀ g h, r (g * h) a b = r g a i * r h i b + r g a j * r h j b := by
    intro a b ha hb g h
    rw [map_mul, Matrix.mul_apply, ← Finset.sum_pair (f := fun k => r g a k * r h k b) hne]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun k _ hk' => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
    by_contra h0
    rw [mul_eq_zero, not_or] at h0
    exact hk k hk'.1 hk'.2 (gtr _ _ _ ha ⟨g, h0.1⟩) (gtr _ _ _ ⟨h, h0.2⟩ hb)
  obtain ⟨u, -, tri, -⟩ := ordFlag _ _ _ _ _ (fun a b h => hinj (Subtype.ext h)) heq.2
  obtain ⟨x, y, φ, hxy, hφ⟩ := line (fun g : D.Gp l => r g) u tri (fun k => Ge r k i) i j hne (grefl i)
    (fun g a b hb ha => by_contra fun h => ha (gtr _ _ _ ⟨g, h⟩ hb))
    (fun g k h a b => ⟨by_contra fun h' => hk k a b ⟨g, h'⟩ h, by_contra fun h' => hk k a b (gtr _ _ _ gij ⟨g, h'⟩) h⟩)
  rcases le_total ‖x‖ ‖y‖ with h | h
  · have hy : y ≠ 0 := by
      rintro rfl
      simp at h hxy
      exact hxy h
    refine core D hD hL r hr i j hij gij (hmul i j (grefl i) gji) (x / y)
      (by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)) fun g hg => ?_
    obtain ⟨e1, e2⟩ := hφ ⟨g, hg⟩
    simp only at e1 e2
    field_simp
    linear_combination y * e1 - x * e2
  · have hx : x ≠ 0 := by
      rintro rfl
      simp at h hxy
      exact hxy h
    refine core D hD hL r hr j i hij.symm gji (fun g h => by rw [hmul j i gij (grefl i), add_comm]) (y / x)
      (by rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)) fun g hg => ?_
    obtain ⟨e1, e2⟩ := hφ ⟨g, hg⟩
    simp only at e1 e2
    field_simp
    linear_combination x * e2 - y * e1
