import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

/- English proof (translation)
Set `φ : Λ →+ Additive H` to `AddMonoidHom.mk' (fun x => Additive.ofMul (L x)) hL`. Establish `hφ : ∀ x, L x = Additive.toMul (φ x)` using `fun x => rfl`. Establish `hc : bas c u = ∑ i, c i • bas (Pi.single i 1) u` using `by conv_lhs => rw [← Finset.univ_sum_single c]`. Rewrite using `[map_sum, Finset.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hs : (Pi.single i (c i) : Fin n → ℤ) = c i • (Pi.single i 1 : Fin n → ℤ)`. Use extensionality with `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`. Rewrite using `[hs, map_zsmul, Pi.smul_apply]`. Rewrite using `[map_prod, hc, hφ, map_sum, toMul_sum]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zpow, hP, map_zsmul, toMul_zsmul]`.

Both sides reduce to the same expression.
-/
theorem levelFactor_comp {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ}
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (c : Fin n → ℤ) (u : Fin m) : π u (∏ i, P i ^ c i) = L (bas c u) := by
  let φ : Λ →+ Additive H := AddMonoidHom.mk' (fun x => Additive.ofMul (L x)) hL
  have hφ : ∀ x, L x = Additive.toMul (φ x) := fun x => rfl
  have hc : bas c u = ∑ i, c i • bas (Pi.single i 1) u := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hs : (Pi.single i (c i) : Fin n → ℤ) = c i • (Pi.single i 1 : Fin n → ℤ) := by
      ext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [hs, map_zsmul, Pi.smul_apply]
  rw [map_prod, hc, hφ, map_sum, toMul_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_zpow, hP, map_zsmul, toMul_zsmul]
  rfl

/- English proof (translation)
Take `⟨c, hc⟩ : ∃ c, bas c = Pi.single u x` from `⟨bas.symm (Pi.single u x), bas.apply_symm_apply _⟩`. Establish `h1` using `levelFactor_comp bas P π L hL hP c u`. Rewrite `h1` using `[hc, Pi.single_eq_same]`. Establish `hk : ∀ i, (P i ^ c i) ^ k = 1` using `fun i => by`. Rewrite using `[← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]`.

Rewrite using `[← h1, ← map_pow, ← Finset.prod_pow, Finset.prod_eq_one (fun i _ => hk i), map_one]`.
-/
theorem levelFactor_torsion {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (ht : ∀ i, P i ^ k = 1) (x : Λ) : L x ^ k = 1 := by
  obtain ⟨c, hc⟩ : ∃ c, bas c = Pi.single u x := ⟨bas.symm (Pi.single u x), bas.apply_symm_apply _⟩
  have h1 := levelFactor_comp bas P π L hL hP c u
  rw [hc, Pi.single_eq_same] at h1
  have hk : ∀ i, (P i ^ c i) ^ k = 1 := fun i => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ht, one_zpow]
  rw [← h1, ← map_pow, ← Finset.prod_pow, Finset.prod_eq_one (fun i _ => hk i), map_one]

/- English proof (translation)
Establish `: NeZero k` using `⟨hk.ne'⟩`. Establish `hcomp` using `levelFactor_comp bas P π L hL hP`. Establish `htor` using `levelFactor_torsion u bas P π L hL hP k ht`. Establish `L0 : L 0 = 1` using `mul_left_cancel (a := L 0) (by rw [← hL, add_zero, _root_.mul_one])`. Establish `hsm : ∀ (j : ℕ) (x : Λ), L (j • x) = L x ^ j`.

Introduce `j x`. Proceed by induction on `j with`. Consider the case `zero => rw [zero_smul, L0, pow_zero]`. Consider the case `succ j ih => rw [succ_nsmul, hL, ih, pow_succ]`. Establish `hone : ∀ a : G, (∀ v, π v a = 1) → a = 1`.

Introduce `a ha`. Take `⟨x, -, hx⟩` from `hπ (fun _ => 1)`. Conclude with `(hx a ha).trans (hx 1 (fun v => map_one _)).symm`. Establish `hred : ∀ w : Fin n → ℤ, ∏ i, P i ^ w i = (List.ofFn fun i => P i ^ ((w i : ZMod k).val)).prod`. Introduce `w`.

Rewrite using `[List.prod_ofFn]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[zpow_eq_zpow_emod (w i) (n := (k : ℤ)) (by rw [zpow_natCast]; exact ht i), ← ZMod.val_intCast, zpow_natCast]`. Use `⟨fun x => ⟨fun hx => ?_, ?_⟩, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩ : ∃ w, bas w = Pi.single u x` from `⟨_, bas.apply_symm_apply _⟩`.

Establish `hg : ∏ i, P i ^ w i = 1` using `hone _ fun v => by`. Rewrite using `[hcomp, hw]`. Distinguish the cases in `hv : v = u`. Substitute `hv` using the available equality. Rewrite using `[Pi.single_eq_same, hx]`.

Rewrite using `[Pi.single_eq_of_ne hv, L0]`. Take `⟨c0, -, huniq⟩` from `hb 1 (one_pow _)`. Establish `e1` using `huniq (fun i => (w i : ZMod k)) ((hred w).symm.trans hg)`. Establish `e2` using `huniq 0 (by simp)`. Establish `hdvd : ∀ i, (k : ℤ) ∣ w i` using `fun i => (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun (e1.trans e2.symm) i)`.

Use `choose w' hw' using hdvd`. Establish `hww : w = (k : ℤ) • w'` using `funext fun i => by rw [Pi.smul_apply, smul_eq_mul, hw' i]`. Use `⟨bas w' u, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨y, rfl⟩`.

Rewrite using `[hsm, htor]`. Take `⟨a, ha, -⟩` from `hπ (Pi.mulSingle u y)`. Establish `hak : a ^ k = 1` using `hone _ fun v => by`. Rewrite using `[map_pow, ha]`. Distinguish the cases in `hv : v = u`.

Substitute `hv` using the available equality. Rewrite using `[Pi.mulSingle_eq_same, hy]`. Rewrite using `[Pi.mulSingle_eq_of_ne hv, one_pow]`. Take `⟨c, hc, -⟩` from `hb a hak`. Use `⟨bas (fun i => ((c i).val : ℤ)) u, ?_⟩` and prove the remaining obligations.

Establish `hprod : ∏ i, P i ^ ((c i).val : ℤ) = a`. Rewrite using `[← hc, List.prod_ofFn]`. Conclude with `Finset.prod_congr rfl fun i _ => zpow_natCast _ _`. Rewrite using `[← hcomp, hprod, ha, Pi.mulSingle_eq_same]`.
-/
theorem levelFactor_bij {G H Λ : Type} [CommGroup G] [CommGroup H] [AddCommGroup Λ] {n m : ℕ} (u : Fin m)
    (bas : (Fin n → ℤ) ≃ₗ[ℤ] (Fin m → Λ)) (P : Fin n → G) (π : Fin m → (G →* H)) (L : Λ → H)
    (hL : ∀ x y, L (x + y) = L x * L y) (hP : ∀ i u, π u (P i) = L (bas (Pi.single i 1) u))
    (k : ℕ) (hk : 0 < k) (ht : ∀ i, P i ^ k = 1)
    (hπ : ∀ y : Fin m → H, ∃! x : G, ∀ u, π u x = y u)
    (hb : ∀ y : G, y ^ k = 1 → ∃! c : Fin n → ZMod k, (List.ofFn fun i => P i ^ (c i).val).prod = y) :
    (∀ x, L x = 1 ↔ ∃ y, x = k • y) ∧ ∀ y : H, y ^ k = 1 → ∃ x, L x = y := by
  have : NeZero k := ⟨hk.ne'⟩
  have hcomp := levelFactor_comp bas P π L hL hP
  have htor := levelFactor_torsion u bas P π L hL hP k ht
  have L0 : L 0 = 1 := mul_left_cancel (a := L 0) (by rw [← hL, add_zero, _root_.mul_one])
  have hsm : ∀ (j : ℕ) (x : Λ), L (j • x) = L x ^ j := by
    intro j x
    induction j with
    | zero => rw [zero_smul, L0, pow_zero]
    | succ j ih => rw [succ_nsmul, hL, ih, pow_succ]
  have hone : ∀ a : G, (∀ v, π v a = 1) → a = 1 := by
    intro a ha
    obtain ⟨x, -, hx⟩ := hπ (fun _ => 1)
    exact (hx a ha).trans (hx 1 (fun v => map_one _)).symm
  have hred : ∀ w : Fin n → ℤ,
      ∏ i, P i ^ w i = (List.ofFn fun i => P i ^ ((w i : ZMod k).val)).prod := by
    intro w
    rw [List.prod_ofFn]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [zpow_eq_zpow_emod (w i) (n := (k : ℤ)) (by rw [zpow_natCast]; exact ht i),
      ← ZMod.val_intCast, zpow_natCast]
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun y hy => ?_⟩
  · obtain ⟨w, hw⟩ : ∃ w, bas w = Pi.single u x := ⟨_, bas.apply_symm_apply _⟩
    have hg : ∏ i, P i ^ w i = 1 := hone _ fun v => by
      rw [hcomp, hw]
      by_cases hv : v = u
      · subst hv; rw [Pi.single_eq_same, hx]
      · rw [Pi.single_eq_of_ne hv, L0]
    obtain ⟨c0, -, huniq⟩ := hb 1 (one_pow _)
    have e1 := huniq (fun i => (w i : ZMod k)) ((hred w).symm.trans hg)
    have e2 := huniq 0 (by simp)
    have hdvd : ∀ i, (k : ℤ) ∣ w i := fun i =>
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun (e1.trans e2.symm) i)
    choose w' hw' using hdvd
    have hww : w = (k : ℤ) • w' := funext fun i => by rw [Pi.smul_apply, smul_eq_mul, hw' i]
    refine ⟨bas w' u, ?_⟩
    calc x = bas w u := by rw [hw, Pi.single_eq_same]
      _ = ((k : ℤ) • bas w') u := by rw [hww, map_zsmul]
      _ = k • bas w' u := by rw [Pi.smul_apply, natCast_zsmul]
  · rintro ⟨y, rfl⟩
    rw [hsm, htor]
  · obtain ⟨a, ha, -⟩ := hπ (Pi.mulSingle u y)
    have hak : a ^ k = 1 := hone _ fun v => by
      rw [map_pow, ha]
      by_cases hv : v = u
      · subst hv; rw [Pi.mulSingle_eq_same, hy]
      · rw [Pi.mulSingle_eq_of_ne hv, one_pow]
    obtain ⟨c, hc, -⟩ := hb a hak
    refine ⟨bas (fun i => ((c i).val : ℤ)) u, ?_⟩
    have hprod : ∏ i, P i ^ ((c i).val : ℤ) = a := by
      rw [← hc, List.prod_ofFn]
      exact Finset.prod_congr rfl fun i _ => zpow_natCast _ _
    rw [← hcomp, hprod, ha, Pi.mulSingle_eq_same]

/- English proof (translation)
Introduce `h g J bas k o _ b S s t A _ _ pr lev hk hpr huniv hlev hpt`. Establish `hcomp : ∀ i u, t.pt i ≫ pr u = lev (bas (Pi.single i 1) u)` using `fun i u => Over.OverMorphism.ext (hpt i u)`. Establish `hinj : ∀ (T : Over S) (x y : T ⟶ t.A), (∀ u, x ≫ pr u = y ≫ pr u) → x = y` using `fun T x y hxy => (huniv T (fun u => y ≫ pr u)).unique hxy (fun u => rfl)`. Set `cg : ∀ T : Over S, CommGroup (T ⟶ t.A)` to `fun T => { (inferInstance : Group (T ⟶ t.A)) with mul_comm := fun x y => hinj T _ _ fun u => by`. Use `hpr u` as an intermediate fact.

Rewrite using `[MonObj.mul_comp, MonObj.mul_comp, _root_.mul_comm] }`. Set `π : ∀ T : Over S, Fin 8 → ((T ⟶ t.A) →* (T ⟶ A))` to `fun T u => MonoidHom.mk' (fun x => x ≫ pr u) (fun x y => by`. Use `hpr u` as an intermediate fact. Conclude with `MonObj.mul_comp x y (pr u))`. Use `⟨?_, fun K _ _ p => ?_⟩` and prove the remaining obligations.

Use `letI := cg (Out.baseOver S)`. Conclude with `levelFactor_torsion (G := Out.baseOver S ⟶ t.A) (H := Out.baseOver S ⟶ A) (0 : Fin 8) bas t.pt (π _) lev hlev hcomp k t.torsion`. Set `T` to `Over.mk p`. Use `letI := cg T`. Set `q : T ⟶ Out.baseOver S` to `Over.homMk p (by simp [T])`.

Set `ρ : (Out.baseOver S ⟶ t.A) →* (T ⟶ t.A)` to `MonoidHom.mk' (fun x => q ≫ x) (fun x y => MonObj.comp_mul q x y)`. Establish `hq : toUnit T = q` using `toUnit_unique _ _`. Use `levelFactor_bij (G := T ⟶ t.A) (0 : Fin 8) bas (fun i => q ≫ t.pt i) (π T) (fun x => toUnit T ≫ lev x) (fun x y => by rw [hlev, MonObj.comp_mul]) (fun i u => ?_) k hk (fun i => by` and prove the remaining obligations. Establish `h1` using `map_pow ρ (t.pt i) k`. Rewrite `h1` using `[t.torsion, map_one]`.

Conclude with `h1.symm)`. Use the proof step `(fun y => huniv T y) (fun y hy => t.bij K p y hy)`. Use `show (q ≫ t.pt i) ≫ pr u = toUnit T ≫ lev (bas (Pi.single i 1) u)`. Rewrite using `[Category.assoc, hcomp, hq]`.
-/
theorem level_on_factor_of_eighth_power : ∀ (h g : ℕ) (J : Type) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))) (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g k J b s) (A : Over S) [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (t.A ⟶ A)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S) ⟶ A)), 0 < k → (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ t.A, ∀ u, x ≫ pr u = y u) → (∀ x y, lev (x + y) = lev x * lev y) → (∀ i u, (t.pt i ≫ pr u).left = (lev (bas (Pi.single i 1) u)).left) → (∀ x, lev x ^ k = 1) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ S), (∀ x, (toUnit (Over.mk p) ≫ lev x = 1 ↔ ∃ y, x = k • y)) ∧ ∀ y : Over.mk p ⟶ A, y ^ k = 1 → ∃ x, toUnit _ ≫ lev x = y := by
  intro h g J bas k o _ b S s t A _ _ pr lev hk hpr huniv hlev hpt
  have hcomp : ∀ i u, t.pt i ≫ pr u = lev (bas (Pi.single i 1) u) := fun i u =>
    Over.OverMorphism.ext (hpt i u)
  have hinj : ∀ (T : Over S) (x y : T ⟶ t.A), (∀ u, x ≫ pr u = y ≫ pr u) → x = y :=
    fun T x y hxy => (huniv T (fun u => y ≫ pr u)).unique hxy (fun u => rfl)
  let cg : ∀ T : Over S, CommGroup (T ⟶ t.A) := fun T =>
    { (inferInstance : Group (T ⟶ t.A)) with
      mul_comm := fun x y => hinj T _ _ fun u => by
        have := hpr u
        rw [MonObj.mul_comp, MonObj.mul_comp, _root_.mul_comm] }
  let π : ∀ T : Over S, Fin 8 → ((T ⟶ t.A) →* (T ⟶ A)) := fun T u =>
    MonoidHom.mk' (fun x => x ≫ pr u) (fun x y => by
      have := hpr u
      exact MonObj.mul_comp x y (pr u))
  refine ⟨?_, fun K _ _ p => ?_⟩
  · letI := cg (Out.baseOver S)
    exact levelFactor_torsion (G := Out.baseOver S ⟶ t.A) (H := Out.baseOver S ⟶ A)
      (0 : Fin 8) bas t.pt (π _) lev hlev hcomp k t.torsion
  let T := Over.mk p
  letI := cg T
  let q : T ⟶ Out.baseOver S := Over.homMk p (by simp [T])
  let ρ : (Out.baseOver S ⟶ t.A) →* (T ⟶ t.A) :=
    MonoidHom.mk' (fun x => q ≫ x) (fun x y => MonObj.comp_mul q x y)
  have hq : toUnit T = q := toUnit_unique _ _
  refine levelFactor_bij (G := T ⟶ t.A) (0 : Fin 8) bas (fun i => q ≫ t.pt i) (π T)
    (fun x => toUnit T ≫ lev x) (fun x y => by rw [hlev, MonObj.comp_mul]) (fun i u => ?_) k hk
    (fun i => by
      have h1 := map_pow ρ (t.pt i) k
      rw [t.torsion, map_one] at h1
      exact h1.symm)
    (fun y => huniv T y) (fun y hy => t.bij K p y hy)
  show (q ≫ t.pt i) ≫ pr u = toUnit T ≫ lev (bas (Pi.single i 1) u)
  rw [Category.assoc, hcomp, hq]

end GlobalTheory.ZM
