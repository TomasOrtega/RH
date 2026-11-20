import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsHaveFiniteDimensionInvarianceIsomorphismStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDivStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTheoremAndSectionsFiniteGrowthAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsIntegralOfIsAbelianSchemeField

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.VolBasic

open Filter Topology GlobalTheory.CechPic

/- English proof (translation)
Establish `ha' : (0 : ℝ) < a` using `by exact_mod_cast ha`. Establish `hk1 : Tendsto k atTop atTop`. Use `tendsto_atTop_atTop.2 fun b => ⟨a * b + C, fun e he => ?_⟩` and prove the remaining obligations. Use `(hk e).1` as an intermediate fact. Conclude with `Nat.le_of_mul_le_mul_left (by omega : a * b ≤ a * k e) ha`.

Establish `hC : Tendsto (fun e : ℕ => (C : ℝ) / e) atTop (𝓝 0)` using `tendsto_const_div_atTop_nhds_zero_nat _`. Establish `h2 : Tendsto (fun e : ℕ => (a : ℝ) * k e / e) atTop (𝓝 1)`. Establish `l : Tendsto (fun e : ℕ => 1 - (C : ℝ) / e) atTop (𝓝 1)` using `by simpa using hC.const_sub 1`. Establish `r : Tendsto (fun e : ℕ => 1 + (C : ℝ) / e) atTop (𝓝 1)` using `by simpa using hC.const_add 1`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' l r ?_ ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_gt_atTop 0] with e he`. Establish `he' : (0 : ℝ) < e` using `by exact_mod_cast he`. Establish `: (e : ℝ) ≤ a * k e + C` using `by exact_mod_cast (hk e).1`. Rewrite using `[le_div_iff₀ he', sub_mul, div_mul_cancel₀ _ he'.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `filter_upwards [eventually_gt_atTop 0] with e he`. Establish `he' : (0 : ℝ) < e` using `by exact_mod_cast he`. Establish `: (a : ℝ) * k e ≤ e + C` using `by exact_mod_cast (hk e).2`. Rewrite using `[div_le_iff₀ he', add_mul, div_mul_cancel₀ _ he'.ne']`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3` using `((hu.comp hk1).mul (h2.pow g)).div_const ((a : ℝ) ^ g)`. Establish `e3 : (a : ℝ) ^ g * δ * 1 ^ g / (a : ℝ) ^ g = δ` using `by rw [one_pow]; field_simp`. Rewrite `h3` using `[e3]`. Use `h3.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0, hk1.eventually_gt_atTop 0] with e he hke`.

Establish `he' : (0 : ℝ) < e` using `by exact_mod_cast he`. Establish `hke' : (0 : ℝ) < k e` using `by exact_mod_cast hke`. Simplify using `only [Function.comp_apply, div_pow, mul_pow]`. Clear the denominators using the available nonvanishing facts.
-/
theorem tendsto_comp_of_near (u : ℕ → ℝ) (a g C : ℕ) (ha : 1 ≤ a) (δ : ℝ) (k : ℕ → ℕ)
    (hk : ∀ e, e ≤ a * k e + C ∧ a * k e ≤ e + C)
    (hu : Tendsto (fun e : ℕ => u e / (e : ℝ) ^ g) atTop (𝓝 ((a : ℝ) ^ g * δ))) :
    Tendsto (fun e : ℕ => u (k e) / (e : ℝ) ^ g) atTop (𝓝 δ) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hk1 : Tendsto k atTop atTop := by
    refine tendsto_atTop_atTop.2 fun b => ⟨a * b + C, fun e he => ?_⟩
    have := (hk e).1
    exact Nat.le_of_mul_le_mul_left (by omega : a * b ≤ a * k e) ha
  have hC : Tendsto (fun e : ℕ => (C : ℝ) / e) atTop (𝓝 0) := tendsto_const_div_atTop_nhds_zero_nat _
  have h2 : Tendsto (fun e : ℕ => (a : ℝ) * k e / e) atTop (𝓝 1) := by
    have l : Tendsto (fun e : ℕ => 1 - (C : ℝ) / e) atTop (𝓝 1) := by simpa using hC.const_sub 1
    have r : Tendsto (fun e : ℕ => 1 + (C : ℝ) / e) atTop (𝓝 1) := by simpa using hC.const_add 1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' l r ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with e he
      have he' : (0 : ℝ) < e := by exact_mod_cast he
      have : (e : ℝ) ≤ a * k e + C := by exact_mod_cast (hk e).1
      rw [le_div_iff₀ he', sub_mul, div_mul_cancel₀ _ he'.ne']
      linarith
    · filter_upwards [eventually_gt_atTop 0] with e he
      have he' : (0 : ℝ) < e := by exact_mod_cast he
      have : (a : ℝ) * k e ≤ e + C := by exact_mod_cast (hk e).2
      rw [div_le_iff₀ he', add_mul, div_mul_cancel₀ _ he'.ne']
      linarith
  have h3 := ((hu.comp hk1).mul (h2.pow g)).div_const ((a : ℝ) ^ g)
  have e3 : (a : ℝ) ^ g * δ * 1 ^ g / (a : ℝ) ^ g = δ := by rw [one_pow]; field_simp
  rw [e3] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0, hk1.eventually_gt_atTop 0] with e he hke
  have he' : (0 : ℝ) < e := by exact_mod_cast he
  have hke' : (0 : ℝ) < k e := by exact_mod_cast hke
  simp only [Function.comp_apply, div_pow, mul_pow]
  field_simp

/- English proof (translation)
Establish `d1 : ∀ n, a * (n / a) ≤ n` using `fun n => Nat.mul_div_le n a`. Establish `d2 : ∀ n, n < a * (n / a) + a` using `fun n => by`. Use `Nat.lt_mul_div_succ n (show 0 < a from ha)` as an intermediate fact. Rewrite `this` using `[Nat.mul_add, Nat.mul_one]`. Then use the resulting hypothesis. Apply the tactic sequence `have l := tendsto_comp_of_near (fun e => (h (a * e) : ℝ)) a g (c + a) ha δ (fun e => (e - c) / a) (fun e => by have := d1 (e - c); have := d2 (e - c); constructor <;> omega) hu`.

Apply the tactic sequence `have r := tendsto_comp_of_near (fun e => (h (a * e) : ℝ)) a g (c + a) ha δ (fun e => (e + c + a) / a) (fun e => by have := d1 (e + c + a); have := d2 (e + c + a); constructor <;> omega) hu`. Use `tendsto_of_tendsto_of_tendsto_of_le_of_le' l r ?_ ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop c] with e he`. Use `d1 (e - c)` as an intermediate fact. Conclude with `div_le_div_of_nonneg_right (by exact_mod_cast hm _ _ (by omega)) (by positivity)`.

Use `Eventually.of_forall fun e => ?_` and prove the remaining obligations. Use `d2 (e + c + a)` as an intermediate fact. Conclude with `div_le_div_of_nonneg_right (by exact_mod_cast hm _ _ (by omega)) (by positivity)`.
-/
theorem tendsto_of_multiples (h : ℕ → ℕ) (a g c : ℕ) (ha : 1 ≤ a) (δ : ℝ)
    (hm : ∀ e e', e + c ≤ e' → h e ≤ h e')
    (hu : Tendsto (fun e : ℕ => (h (a * e) : ℝ) / (e : ℝ) ^ g) atTop (𝓝 ((a : ℝ) ^ g * δ))) :
    Tendsto (fun e : ℕ => (h e : ℝ) / (e : ℝ) ^ g) atTop (𝓝 δ) := by
  have d1 : ∀ n, a * (n / a) ≤ n := fun n => Nat.mul_div_le n a
  have d2 : ∀ n, n < a * (n / a) + a := fun n => by
    have := Nat.lt_mul_div_succ n (show 0 < a from ha)
    rwa [Nat.mul_add, Nat.mul_one] at this
  have l := tendsto_comp_of_near (fun e => (h (a * e) : ℝ)) a g (c + a) ha δ (fun e => (e - c) / a)
    (fun e => by have := d1 (e - c); have := d2 (e - c); constructor <;> omega) hu
  have r := tendsto_comp_of_near (fun e => (h (a * e) : ℝ)) a g (c + a) ha δ (fun e => (e + c + a) / a)
    (fun e => by have := d1 (e + c + a); have := d2 (e + c + a); constructor <;> omega) hu
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' l r ?_ ?_
  · filter_upwards [eventually_ge_atTop c] with e he
    have := d1 (e - c)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm _ _ (by omega)) (by positivity)
  · refine Eventually.of_forall fun e => ?_
    have := d2 (e + c + a)
    exact div_le_div_of_nonneg_right (by exact_mod_cast hm _ _ (by omega)) (by positivity)

variable {K : Type} [Field K] {X : Scheme.{0}}

def cst (p : X ⟶ Sp K) (U : X.Opens) : K →+* Γ(X, U) :=
  (p.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem constFn_eq (p : X ⟶ Sp K) (U : X.Opens) (a : K) : constFn p U a = cst p U a := rfl

/- English proof (translation)
Use `congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) (Scheme.Hom.appLE_map p (U := ⊤) (V := U) le_top (homOfLE h).op)` as an intermediate fact. Conclude with `this`.
-/
theorem res_cst (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) : resG X h (cst p U a) = cst p V a := by
  have := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
    (Scheme.Hom.appLE_map p (U := ⊤) (V := U) le_top (homOfLE h).op)
  exact this

/- English proof (translation)
Rewrite using `[← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem res_res {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    resG X h' (resG X h a) = resG X (h'.trans h) a := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]; rfl

/- English proof (translation)
Establish `h0 : Nat.find hn ≠ 0` using `fun h => by`. Use `Nat.find_spec hn` as an intermediate fact. Rewrite `this` using `[h]`. Take `⟨c, hc, -⟩` from `this Fin.elim0`. Conclude with `hc (Subsingleton.elim _ _)`.

Take `⟨r, hr⟩` from `Nat.exists_eq_succ_of_ne_zero h0`. Establish `h1` using `Nat.find_min hn (m := r) (by omega)`. Establish `h2` using `Nat.find_spec hn`. Rewrite `h2` using `[hr]`. Use `push_neg at h1`.

Take `⟨s, hs⟩` from `h1`. Establish `hs' : ∀ c : Fin r → K, (∀ j, ∑ k, cst p _ (c k) * (s k).f j = 0) → c = 0` using `fun c hc => by`. Assume the negation of the conclusion as `h`. Take `⟨j, hj⟩` from `hs c h`. Conclude with `hj (hc j)`.

Use `⟨r, s, fun t => existsUnique_of_exists_of_unique ?_ fun a b ha hb => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, hz⟩` from `h2 (Fin.cons t s)`. Simplify using `only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hz`. Establish `hc0 : c 0 ≠ 0` using `fun h => hc (by`. Use `hs' (fun k => c k.succ) fun j => by simpa [h] using hz j` as an intermediate fact.

Use function extensionality and compare the values at `k`. Use `Fin.cases h (fun k => congrFun this k) k)` and prove the remaining obligations. Use `⟨fun k => -(c 0)⁻¹ * c k.succ, fun j => ?_⟩` and prove the remaining obligations. Establish `e : cst p (M.U j) (c 0)⁻¹ * cst p _ (c 0) = 1` using `by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]`. Simplify using `only [constFn_eq, map_mul, map_neg, _root_.mul_assoc, ← Finset.mul_sum]`.

Take the linear combination `(cst p (M.U j) (c 0)⁻¹) * hz j - t.f j * e`. Use `sub_eq_zero.1 (hs' _ fun j => ?_)` and prove the remaining obligations. Simplify using `only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]`. Conclude with `sub_eq_zero.2 ((ha j).symm.trans (hb j))`.
-/
theorem exists_h0Is (p : X ⟶ Sp K) (M : LB X)
    (hn : ∃ n : ℕ, ∀ s : Fin n → M.Sec, ∃ c : Fin n → K, c ≠ 0 ∧ ∀ j, ∑ k, cst p _ (c k) * (s k).f j = 0) :
    ∃ r, SectionsHaveFiniteDimension p M r := by
  classical
  have h0 : Nat.find hn ≠ 0 := fun h => by
    have := Nat.find_spec hn
    rw [h] at this
    obtain ⟨c, hc, -⟩ := this Fin.elim0
    exact hc (Subsingleton.elim _ _)
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero h0
  have h1 := Nat.find_min hn (m := r) (by omega)
  have h2 := Nat.find_spec hn
  rw [hr] at h2
  push_neg at h1
  obtain ⟨s, hs⟩ := h1
  have hs' : ∀ c : Fin r → K, (∀ j, ∑ k, cst p _ (c k) * (s k).f j = 0) → c = 0 := fun c hc => by
    by_contra h
    obtain ⟨j, hj⟩ := hs c h
    exact hj (hc j)
  refine ⟨r, s, fun t => existsUnique_of_exists_of_unique ?_ fun a b ha hb => ?_⟩
  · obtain ⟨c, hc, hz⟩ := h2 (Fin.cons t s)
    simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hz
    have hc0 : c 0 ≠ 0 := fun h => hc (by
      have := hs' (fun k => c k.succ) fun j => by simpa [h] using hz j
      funext k
      refine Fin.cases h (fun k => congrFun this k) k)
    refine ⟨fun k => -(c 0)⁻¹ * c k.succ, fun j => ?_⟩
    have e : cst p (M.U j) (c 0)⁻¹ * cst p _ (c 0) = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
    simp only [constFn_eq, map_mul, map_neg, _root_.mul_assoc, ← Finset.mul_sum]
    linear_combination (cst p (M.U j) (c 0)⁻¹) * hz j - t.f j * e
  · refine sub_eq_zero.1 (hs' _ fun j => ?_)
    simp only [Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.2 ((ha j).symm.trans (hb j))

def tensSec {A B : LB X} (s : A.Sec) (t : B.Sec) : (tens A B).Sec where
  f q := resG X (inf_le_left : A.U q.1 ⊓ B.U q.2 ≤ _) (s.f q.1) * resG X (inf_le_right : A.U q.1 ⊓ B.U q.2 ≤ _) (t.f q.2)
  compat q q' := by
    have l₁ : A.U q.1 ⊓ B.U q.2 ⊓ (A.U q'.1 ⊓ B.U q'.2) ≤ A.U q.1 ⊓ A.U q'.1 :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    have l₂ : A.U q.1 ⊓ B.U q.2 ⊓ (A.U q'.1 ⊓ B.U q'.2) ≤ B.U q.2 ⊓ B.U q'.2 :=
      le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
    have e₁ := congrArg (resG X l₁) (s.compat q.1 q'.1)
    have e₂ := congrArg (resG X l₂) (t.compat q.2 q'.2)
    rw [map_mul, res_res, res_res] at e₁ e₂
    show resG X (inf_le_left : A.U q.1 ⊓ B.U q.2 ⊓ (A.U q'.1 ⊓ B.U q'.2) ≤ _) (_ * _) =
      (resG X l₁ (A.g q.1 q'.1).val * resG X l₂ (B.g q.2 q'.2).val) *
        resG X (inf_le_right : A.U q.1 ⊓ B.U q.2 ⊓ (A.U q'.1 ⊓ B.U q'.2) ≤ _) (_ * _)
    rw [map_mul, map_mul, res_res, res_res, res_res, res_res, e₁, e₂]
    ring

/- English proof (translation)
Establish `ne : ∀ {W : X.Opens} {c : Γ(X, W)}, c ≠ 0 → (W : Set X).Nonempty` using `fun {W c} hc => by`. Assume the negation of the conclusion as `h`. Establish `: W = ⊥` using `by simpa [Set.not_nonempty_iff_eq_empty] using h`. Substitute `this` using the available equality. Conclude with `hc (Subsingleton.elim _ _)`.

Establish `: Nonempty (U ⊓ V : X.Opens)` using `(nonempty_preirreducible_inter U.isOpen V.isOpen (ne ha) (ne hb)).to_subtype`. Use `mul_ne_zero (fun h => ha ?_) (fun h => hb ?_)` and prove the remaining obligations. Conclude with `map_injective_of_isIntegral X (homOfLE (inf_le_left : U ⊓ V ≤ U)) (h.trans (map_zero _).symm)`. Conclude with `map_injective_of_isIntegral X (homOfLE (inf_le_right : U ⊓ V ≤ V)) (h.trans (map_zero _).symm)`.
-/
theorem res_mul_res_ne_zero [IsIntegral X] {U V : X.Opens} {a : Γ(X, U)} {b : Γ(X, V)} (ha : a ≠ 0) (hb : b ≠ 0) :
    resG X (inf_le_left : U ⊓ V ≤ U) a * resG X (inf_le_right : U ⊓ V ≤ V) b ≠ 0 := by
  have ne : ∀ {W : X.Opens} {c : Γ(X, W)}, c ≠ 0 → (W : Set X).Nonempty := fun {W c} hc => by
    by_contra h
    have : W = ⊥ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    subst this
    exact hc (Subsingleton.elim _ _)
  have : Nonempty (U ⊓ V : X.Opens) :=
    (nonempty_preirreducible_inter U.isOpen V.isOpen (ne ha) (ne hb)).to_subtype
  refine mul_ne_zero (fun h => ha ?_) (fun h => hb ?_)
  · exact map_injective_of_isIntegral X (homOfLE (inf_le_left : U ⊓ V ≤ U)) (h.trans (map_zero _).symm)
  · exact map_injective_of_isIntegral X (homOfLE (inf_le_right : U ⊓ V ≤ V)) (h.trans (map_zero _).symm)

/- English proof (translation)
Take `⟨s, hs⟩` from `h`. Take `⟨s', hs'⟩` from `h'`. Take `⟨k, hk⟩` from `hu`. Use `choose a ha using fun i => (hs' (tensSec (s i) u)).exists`. Establish `li : LinearIndependent K a`.

Use `Fintype.linearIndependent_iff.2 fun c hc => ?_` and prove the remaining obligations. Establish `hz : ∀ j, ∑ i, cst p _ (c i) * (s i).f j = 0` using `fun j => by`. Assume the negation of the conclusion as `hne`. Use `res_mul_res_ne_zero hne hk ?_` and prove the remaining obligations. Set `w : Fin r' → Γ(X, A.U j ⊓ B.U k)` to `fun l => (s' l).f (j, k)`.

Establish `e : ∀ i, resG X (inf_le_left : A.U j ⊓ B.U k ≤ _) ((s i).f j) * resG X (inf_le_right : A.U j ⊓ B.U k ≤ _) (u.f k) = ∑ l, cst p (A.U j ⊓ B.U k) (a i l) * w l` using `fun i => ha i (j, k)`. Establish `hc' : ∀ l, ∑ i, cst p (A.U j ⊓ B.U k) (c i) * cst p (A.U j ⊓ B.U k) (a i l) = 0` using `fun l => by`. Use `congrArg (cst p (A.U j ⊓ B.U k)) (congrFun hc l)` as an intermediate fact. Simplify `this` using `[Finset.sum_apply]`. Simplify using `only [map_sum, map_mul, res_cst, Finset.sum_mul, _root_.mul_assoc, e, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Simplify using `only [← _root_.mul_assoc, ← Finset.sum_mul, hc', zero_mul]`. Set `z : A.Sec` to `⟨fun _ => 0, fun i j => by simp⟩`. Conclude with `congrFun ((hs z).unique (y₁ := c) (y₂ := 0) (fun j => (hz j).symm) (fun j => by simp [z, constFn_eq]))`.

Simplify using `using li.fintype_card_le_finrank`.
-/
theorem sectionsDim_le_tensor_of_nonzero_section [IsIntegral X] (p : X ⟶ Sp K) {A B : LB X} (u : B.Sec) (hu : ∃ k, u.f k ≠ 0) {r r' : ℕ}
    (h : SectionsHaveFiniteDimension p A r) (h' : SectionsHaveFiniteDimension p (tens A B) r') : r ≤ r' := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨s', hs'⟩ := h'
  obtain ⟨k, hk⟩ := hu
  choose a ha using fun i => (hs' (tensSec (s i) u)).exists
  have li : LinearIndependent K a := by
    refine Fintype.linearIndependent_iff.2 fun c hc => ?_
    have hz : ∀ j, ∑ i, cst p _ (c i) * (s i).f j = 0 := fun j => by
      by_contra hne
      refine res_mul_res_ne_zero hne hk ?_
      let w : Fin r' → Γ(X, A.U j ⊓ B.U k) := fun l => (s' l).f (j, k)
      have e : ∀ i, resG X (inf_le_left : A.U j ⊓ B.U k ≤ _) ((s i).f j) * resG X (inf_le_right : A.U j ⊓ B.U k ≤ _) (u.f k) =
          ∑ l, cst p (A.U j ⊓ B.U k) (a i l) * w l := fun i => ha i (j, k)
      have hc' : ∀ l, ∑ i, cst p (A.U j ⊓ B.U k) (c i) * cst p (A.U j ⊓ B.U k) (a i l) = 0 := fun l => by
        have := congrArg (cst p (A.U j ⊓ B.U k)) (congrFun hc l)
        simpa [Finset.sum_apply] using this
      simp only [map_sum, map_mul, res_cst, Finset.sum_mul, _root_.mul_assoc, e, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun l _ => ?_
      simp only [← _root_.mul_assoc, ← Finset.sum_mul, hc', zero_mul]
    let z : A.Sec := ⟨fun _ => 0, fun i j => by simp⟩
    exact congrFun ((hs z).unique (y₁ := c) (y₂ := 0) (fun j => (hz j).symm) (fun j => by simp [z, constFn_eq]))
  simpa using li.fintype_card_le_finrank

def Eff (c : Pic X) : Prop := ∃ (L : LB X) (hL : L.IsLB), cls L hL = c ∧ ∃ s : L.Sec, ∃ j, s.f j ≠ 0

/- English proof (translation)
Take `⟨A, hA, rfl, s, j, hs⟩` from `hc`. Take `⟨B, hB, rfl, t, k, ht⟩` from `hd`. Conclude with `⟨tens A B, isLB_tens hA hB, rfl, tensSec s t, (j, k), res_mul_res_ne_zero hs ht⟩`.
-/
theorem Eff.add [IsIntegral X] {c d : Pic X} (hc : Eff c) (hd : Eff d) : Eff (c + d) := by
  obtain ⟨A, hA, rfl, s, j, hs⟩ := hc
  obtain ⟨B, hB, rfl, t, k, ht⟩ := hd
  exact ⟨tens A B, isLB_tens hA hB, rfl, tensSec s t, (j, k), res_mul_res_ne_zero hs ht⟩

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using hc`. Consider the case `succ n ih => rw [succ_nsmul]`. Conclude with `ih.add hc`.
-/
theorem Eff.nsmul [IsIntegral X] {c : Pic X} (hc : Eff c) (n : ℕ) : Eff ((n + 1) • c) := by
  induction n with
  | zero => simpa using hc
  | succ n ih => rw [succ_nsmul]; exact ih.add hc

/- English proof (translation)
The claim follows from `((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p A hA).2.1 B hB ((cls_eq_iff hA hB).1 h)).1 r hr`.
-/
theorem sectionsDim_congr_of_cechPicardClass_eq (p : X ⟶ Sp K) {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (h : cls A hA = cls B hB) {r : ℕ}
    (hr : SectionsHaveFiniteDimension p A r) : SectionsHaveFiniteDimension p B r :=
  ((GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K X p A hA).2.1 B hB ((cls_eq_iff hA hB).1 h)).1 r hr

/- English proof (translation)
Take `⟨N, hN, e, u, hu⟩` from `h`. Use `sectionsDim_le_tensor_of_nonzero_section p u hu hr (sectionsDim_congr_of_cechPicardClass_eq p hB (isLB_tens hA hN) ?_ hr')` and prove the remaining obligations. Rewrite using `[cls_tens hA hN, e]`. Normalize the expressions using the abelian group laws.
-/
theorem h0_le [IsIntegral X] (p : X ⟶ Sp K) {A B : LB X} (hA : A.IsLB) (hB : B.IsLB)
    (h : Eff (cls B hB - cls A hA)) {r r' : ℕ} (hr : SectionsHaveFiniteDimension p A r) (hr' : SectionsHaveFiniteDimension p B r') : r ≤ r' := by
  obtain ⟨N, hN, e, u, hu⟩ := h
  refine sectionsDim_le_tensor_of_nonzero_section p u hu hr (sectionsDim_congr_of_cechPicardClass_eq p hB (isLB_tens hA hN) ?_ hr')
  rw [cls_tens hA hN, e]
  abel

/- English proof (translation)
The claim follows from `LB.isLB_linComb hL _ _`.
-/
theorem isLB_pow {L : LB X} (hL : L.IsLB) (n : ℕ) : (lbPow L n).IsLB := LB.isLB_linComb hL _ _

/- English proof (translation)
Rewrite using `[cls_lbPow (isLB_pow hL a), cls_lbPow hL, cls_lbPow hL, mul_nsmul]`.
-/
theorem cls_pow_pow {L : LB X} (hL : L.IsLB) (a e : ℕ) :
    cls _ (isLB_pow (isLB_pow hL a) e) = cls _ (isLB_pow hL (a * e)) := by
  rw [cls_lbPow (isLB_pow hL a), cls_lbPow hL, cls_lbPow hL, mul_nsmul]

/- English proof (translation)
Introduce `K _ _ P M g hM`. Use `polAV_isIntegral_of_isAlgClosed K P` as an intermediate fact. Establish `fin : ∀ N : LB P.A.left, N.IsLB → ∃ r, SectionsHaveFiniteDimension P.A.hom N r` using `fun N hN => by`. Take `⟨n, hn⟩` from `GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.2.1 K P N hN`. Use `exists_h0Is _ N ⟨n, fun s => ?_⟩` and prove the remaining obligations.

Take `⟨c, hc, hz⟩` from `hn s`. Use `⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (c k), fun h => hc (funext fun k => ?_), fun j => ?_⟩` and prove the remaining obligations. Use `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective ?_` and prove the remaining obligations. Conclude with `(congrFun h k).trans (map_zero _).symm`. Use `Eq.trans (Finset.sum_congr rfl fun k _ => congrArg (· * _) ?_) (hz j)` and prove the remaining obligations.

Conclude with `congrArg (P.A.hom.appLE ⊤ (N.U j) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm_apply_apply (c k))`. Establish `uniq : ∀ N : LB P.A.left, N.IsLB → ∀ r r', SectionsHaveFiniteDimension P.A.hom N r → SectionsHaveFiniteDimension P.A.hom N r' → r = r'` using `fun N hN => (GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ _ N hN).1`. Use `⟨fin M hM, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `δ δ' ⟨h, hh, ht⟩ ⟨h', hh', ht'⟩`. Take `rfl : h = h'` from `funext fun e => uniq _ (isLB_pow hM e) _ _ (hh e) (hh' e)`.

Conclude with `tendsto_nhds_unique ht ht'`. Introduce and unpack `M' δ hM' hi ⟨h, hh, ht⟩`. Use `⟨h, fun e => sectionsDim_congr_of_cechPicardClass_eq _ (isLB_pow hM e) (isLB_pow hM' e) ?_ (hh e), ht⟩` and prove the remaining obligations. Rewrite using `[cls_lbPow hM, cls_lbPow hM', (cls_eq_iff hM hM').2 hi]`. Introduce and unpack `a δ ha ⟨h, hh, ht⟩`.

Use `⟨fun e => h (a * e), fun e => sectionsDim_congr_of_cechPicardClass_eq _ _ _ (cls_pow_pow hM a e).symm (hh _), ?_⟩` and prove the remaining obligations. Establish `ha' : (0 : ℝ) < a` using `by exact_mod_cast ha`. Establish `hk : Tendsto (fun e : ℕ => a * e) atTop atTop` using `tendsto_atTop_mono (fun e => Nat.le_mul_of_pos_left e ha) tendsto_id`. Use `((ht.comp hk).const_mul ((a : ℝ) ^ g)).congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with e he`.

Establish `he' : (0 : ℝ) < e` using `by exact_mod_cast he`. Simplify using `only [Function.comp_apply, Nat.cast_mul, mul_pow]`. Clear the denominators using the available nonvanishing facts. Introduce and unpack `a δ ha hamp ⟨h', hh', ht⟩ choose h hh using fun e => fin _ (isLB_pow hM e)`. Take `rfl : h' = fun e => h (a * e)` from `funext fun e => uniq _ (isLB_pow hM (a * e)) _ _ (sectionsDim_congr_of_cechPicardClass_eq _ _ _ (cls_pow_pow hM a e) (hh' e)) (hh _)`.

Take `⟨c, hc⟩` from `eventually_atTop.1 (GlobalTheory.T.eventually_section_and_relAmple_pow_div K P M (lbPow M 0) hM (isLB_pow hM 0) hamp)`. Use `⟨h, hh, tendsto_of_multiples h a g c ha δ (fun e e' he => ?_) ht⟩` and prove the remaining obligations. Take `⟨t, rfl⟩` from `Nat.exists_eq_add_of_le (show e ≤ e' by omega)`. Use `h0_le _ (isLB_pow hM e) (isLB_pow hM (e + t)) ⟨_, LB.isLB_div (isLB_pow hM t) (isLB_pow hM 0), ?_, (hc t (by omega)).1⟩ (hh _) (hh _)` and prove the remaining obligations. Rewrite using `[cls_div (isLB_pow hM t) (isLB_pow hM 0), cls_lbPow hM, cls_lbPow hM, cls_lbPow hM, cls_lbPow hM, add_nsmul, zero_nsmul]`.

Normalize the expressions using the abelian group laws. Introduce `M' s hM' hs`. Establish `he : Eff (cls M' hM' - cls M hM)` using `⟨_, LB.isLB_div hM' hM, cls_div hM' hM _, s, hs⟩`. Use `⟨fun r r' => h0_le _ hM hM' he, ?_⟩` and prove the remaining obligations. Introduce and unpack `δ δ' ⟨h, hh, ht⟩ ⟨h', hh', ht'⟩`.

Use `le_of_tendsto_of_tendsto ht ht' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with e he0`. Take `⟨n, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero he0.ne'`. Establish `: h (n + 1) ≤ h' (n + 1)`. Use `h0_le _ (isLB_pow hM _) (isLB_pow hM' _) ?_ (hh _) (hh' _)` and prove the remaining obligations.

Rewrite using `[cls_lbPow hM, cls_lbPow hM', ← nsmul_sub]`. Conclude with `he.nsmul n`. Conclude with `div_le_div_of_nonneg_right (by exact_mod_cast this) (by positivity)`.
-/
theorem vol_basic : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M : LB P.A.left) (g : ℕ), M.IsLB → (∃ r, SectionsHaveFiniteDimension P.A.hom M r) ∧ (∀ δ δ', Vol P.A.hom M g δ → Vol P.A.hom M g δ' → δ = δ') ∧ (∀ (M' : LB P.A.left) δ, M'.IsLB → LBIso M M' → Vol P.A.hom M g δ → Vol P.A.hom M' g δ) ∧ (∀ (a : ℕ) δ, 1 ≤ a → Vol P.A.hom M g δ → Vol P.A.hom (lbPow M a) g ((a : ℝ) ^ g * δ)) ∧ (∀ (a : ℕ) δ, 1 ≤ a → Out.RelAmple P.A M → Vol P.A.hom (lbPow M a) g ((a : ℝ) ^ g * δ) → Vol P.A.hom M g δ) ∧ ∀ (M' : LB P.A.left) (s : (LB.div M' M).Sec), M'.IsLB → (∃ j, s.f j ≠ 0) → (∀ r r', SectionsHaveFiniteDimension P.A.hom M r → SectionsHaveFiniteDimension P.A.hom M' r' → r ≤ r') ∧ ∀ δ δ', Vol P.A.hom M g δ → Vol P.A.hom M' g δ' → δ ≤ δ' := by
  intro K _ _ P M g hM
  have := polAV_isIntegral_of_isAlgClosed K P
  have fin : ∀ N : LB P.A.left, N.IsLB → ∃ r, SectionsHaveFiniteDimension P.A.hom N r := fun N hN => by
    obtain ⟨n, hn⟩ := GlobalTheory.AbLaw.CubeAssembly.cube_and_sections.2.1 K P N hN
    refine exists_h0Is _ N ⟨n, fun s => ?_⟩
    obtain ⟨c, hc, hz⟩ := hn s
    refine ⟨fun k => (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (c k), fun h => hc (funext fun k => ?_), fun j => ?_⟩
    · refine (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective ?_
      exact (congrFun h k).trans (map_zero _).symm
    · refine Eq.trans (Finset.sum_congr rfl fun k _ => congrArg (· * _) ?_) (hz j)
      exact congrArg (P.A.hom.appLE ⊤ (N.U j) le_top).hom
        ((Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm_apply_apply (c k))
  have uniq : ∀ N : LB P.A.left, N.IsLB → ∀ r r', SectionsHaveFiniteDimension P.A.hom N r → SectionsHaveFiniteDimension P.A.hom N r' → r = r' :=
    fun N hN => (GlobalTheory.T.sectionsHaveFiniteDimension_invariance_isomorphisms K _ _ N hN).1
  refine ⟨fin M hM, ?_, ?_, ?_, ?_, ?_⟩
  · rintro δ δ' ⟨h, hh, ht⟩ ⟨h', hh', ht'⟩
    obtain rfl : h = h' := funext fun e => uniq _ (isLB_pow hM e) _ _ (hh e) (hh' e)
    exact tendsto_nhds_unique ht ht'
  · rintro M' δ hM' hi ⟨h, hh, ht⟩
    refine ⟨h, fun e => sectionsDim_congr_of_cechPicardClass_eq _ (isLB_pow hM e) (isLB_pow hM' e) ?_ (hh e), ht⟩
    rw [cls_lbPow hM, cls_lbPow hM', (cls_eq_iff hM hM').2 hi]
  · rintro a δ ha ⟨h, hh, ht⟩
    refine ⟨fun e => h (a * e), fun e => sectionsDim_congr_of_cechPicardClass_eq _ _ _ (cls_pow_pow hM a e).symm (hh _), ?_⟩
    have ha' : (0 : ℝ) < a := by exact_mod_cast ha
    have hk : Tendsto (fun e : ℕ => a * e) atTop atTop :=
      tendsto_atTop_mono (fun e => Nat.le_mul_of_pos_left e ha) tendsto_id
    refine ((ht.comp hk).const_mul ((a : ℝ) ^ g)).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with e he
    have he' : (0 : ℝ) < e := by exact_mod_cast he
    simp only [Function.comp_apply, Nat.cast_mul, mul_pow]
    field_simp
  · rintro a δ ha hamp ⟨h', hh', ht⟩
    choose h hh using fun e => fin _ (isLB_pow hM e)
    obtain rfl : h' = fun e => h (a * e) := funext fun e =>
      uniq _ (isLB_pow hM (a * e)) _ _ (sectionsDim_congr_of_cechPicardClass_eq _ _ _ (cls_pow_pow hM a e) (hh' e)) (hh _)
    obtain ⟨c, hc⟩ := eventually_atTop.1 (GlobalTheory.T.eventually_section_and_relAmple_pow_div K P M (lbPow M 0) hM (isLB_pow hM 0) hamp)
    refine ⟨h, hh, tendsto_of_multiples h a g c ha δ (fun e e' he => ?_) ht⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (show e ≤ e' by omega)
    refine h0_le _ (isLB_pow hM e) (isLB_pow hM (e + t))
      ⟨_, LB.isLB_div (isLB_pow hM t) (isLB_pow hM 0), ?_, (hc t (by omega)).1⟩ (hh _) (hh _)
    rw [cls_div (isLB_pow hM t) (isLB_pow hM 0), cls_lbPow hM, cls_lbPow hM, cls_lbPow hM, cls_lbPow hM,
      add_nsmul, zero_nsmul]
    abel
  · intro M' s hM' hs
    have he : Eff (cls M' hM' - cls M hM) := ⟨_, LB.isLB_div hM' hM, cls_div hM' hM _, s, hs⟩
    refine ⟨fun r r' => h0_le _ hM hM' he, ?_⟩
    rintro δ δ' ⟨h, hh, ht⟩ ⟨h', hh', ht'⟩
    refine le_of_tendsto_of_tendsto ht ht' ?_
    filter_upwards [eventually_gt_atTop 0] with e he0
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he0.ne'
    have : h (n + 1) ≤ h' (n + 1) := by
      refine h0_le _ (isLB_pow hM _) (isLB_pow hM' _) ?_ (hh _) (hh' _)
      rw [cls_lbPow hM, cls_lbPow hM', ← nsmul_sub]
      exact he.nsmul n
    exact div_le_div_of_nonneg_right (by exact_mod_cast this) (by positivity)

end GlobalTheory.VolBasic
