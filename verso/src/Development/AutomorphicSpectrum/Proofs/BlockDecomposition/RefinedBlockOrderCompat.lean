import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical leviPar normLeviParSqrtModular)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.CellChar

section Finite

variable {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β']
  {c : α → β' → Type} [∀ i j, Fintype (c i j)]

/- English proof (translation)
Rewrite using `[Fintype.prod_sigma, Finset.prod_eq_single i]`. Rewrite using `[Fintype.prod_sigma]`. Combine the equalities or inequalities in the displayed calculation. Introduce `b _ hb`. Conclude with `Finset.prod_eq_one fun q _ => by simp [hb]`.

Simplify using the standard rewrite rules.
-/
theorem prod_row (i : α) (S : β' → Prop) [DecidablePred S] {G : Type} [CommMonoid G] (a : G) :
    ∏ q : (Σ i, Σ j, c i j), (if q.1 = i ∧ S q.2.1 then a else 1) =
      a ^ (∑ b with S b, Fintype.card (c i b)) := by
  rw [Fintype.prod_sigma, Finset.prod_eq_single i]
  · rw [Fintype.prod_sigma]
    calc _ = ∏ j, (if S j then a ^ Fintype.card (c i j) else 1) :=
          Finset.prod_congr rfl fun j _ => by split_ifs with h <;> simp [h]
      _ = ∏ j with S j, a ^ Fintype.card (c i j) := (Finset.prod_filter _ _).symm
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  · intro b _ hb
    exact Finset.prod_eq_one fun q _ => by simp [hb]
  · simp

/- English proof (translation)
Establish `h1 : ∀ p q : (Σ i, Σ j, c i j), (if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p / v q else 1) = (if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p else 1) * (if q.1 = p.1 ∧ p.2.1 < q.2.1 then (v q)⁻¹ else 1)`. Introduce `p q`. Use `split_ifs`. Rewrite using `[div_eq_mul_inv]`. Simplify using the standard rewrite rules.

Repeatedly rewrite using `[h1, Finset.prod_mul_distrib]`. Establish `h3 : (∏ p : (Σ i, Σ j, c i j), ∏ q : (Σ i, Σ j, c i j), if q.1 = p.1 ∧ p.2.1 < q.2.1 then (v q)⁻¹ else 1) = ∏ p : (Σ i, Σ j, c i j), ∏ q : (Σ i, Σ j, c i j), if p.1 = q.1 ∧ q.2.1 < p.2.1 then (v p)⁻¹ else 1` using `Finset.prod_comm`. Rewrite using `[h3, ← Finset.prod_mul_distrib]`. Establish `h2 : ∀ p : (Σ i, Σ j, c i j), (∏ q : (Σ i, Σ j, c i j), if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p else 1) * (∏ q : (Σ i, Σ j, c i j), if p.1 = q.1 ∧ q.2.1 < p.2.1 then (v p)⁻¹ else 1) = v p ^ modExp (c p.1) p.2.1`. Introduce `p`.

Repeatedly rewrite using `[eq_comm (a := p.1)]`. Rewrite using `[prod_row p.1 (fun b => p.2.1 < b), prod_row p.1 (fun b => b < p.2.1), modExp, zpow_sub₀ (hv p), inv_pow, div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[Finset.prod_congr rfl fun p _ => h2 p, Fintype.prod_sigma]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.prod_sigma]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `Finset.prod_zpow (fun t => v ⟨i, j, t⟩) Finset.univ (modExp (c i) j)`.
-/
theorem prod_rel {G : Type} [CommGroupWithZero G] (v : (Σ i, Σ j, c i j) → G) (hv : ∀ q, v q ≠ 0) :
    ∏ p : (Σ i, Σ j, c i j), ∏ q : (Σ i, Σ j, c i j),
        (if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p / v q else 1) =
      ∏ i, ∏ j, (∏ t, v ⟨i, j, t⟩) ^ modExp (c i) j := by
  have h1 : ∀ p q : (Σ i, Σ j, c i j), (if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p / v q else 1) =
      (if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p else 1) *
        (if q.1 = p.1 ∧ p.2.1 < q.2.1 then (v q)⁻¹ else 1) := by
    intro p q
    split_ifs
    · rw [div_eq_mul_inv]
    · simp
  simp_rw [h1, Finset.prod_mul_distrib]
  have h3 : (∏ p : (Σ i, Σ j, c i j), ∏ q : (Σ i, Σ j, c i j),
        if q.1 = p.1 ∧ p.2.1 < q.2.1 then (v q)⁻¹ else 1) =
      ∏ p : (Σ i, Σ j, c i j), ∏ q : (Σ i, Σ j, c i j),
        if p.1 = q.1 ∧ q.2.1 < p.2.1 then (v p)⁻¹ else 1 := Finset.prod_comm
  rw [h3, ← Finset.prod_mul_distrib]
  have h2 : ∀ p : (Σ i, Σ j, c i j),
      (∏ q : (Σ i, Σ j, c i j), if q.1 = p.1 ∧ p.2.1 < q.2.1 then v p else 1) *
        (∏ q : (Σ i, Σ j, c i j), if p.1 = q.1 ∧ q.2.1 < p.2.1 then (v p)⁻¹ else 1) =
      v p ^ modExp (c p.1) p.2.1 := by
    intro p
    simp_rw [eq_comm (a := p.1)]
    rw [prod_row p.1 (fun b => p.2.1 < b), prod_row p.1 (fun b => b < p.2.1), modExp,
      zpow_sub₀ (hv p), inv_pow, div_eq_mul_inv, ← zpow_natCast, ← zpow_natCast]
    push_cast
    rfl
  rw [Finset.prod_congr rfl fun p _ => h2 p, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact Finset.prod_zpow (fun t => v ⟨i, j, t⟩) Finset.univ (modExp (c i) j)

/- English proof (translation)
Set `ε : (Σ i, Σ j, c i j) ≃ Fin N` to `(Equiv.sigmaCongrRight f).trans e`. Establish `hε : ∀ i j t, ε ⟨i, j, t⟩ = e ⟨i, f i ⟨j, t⟩⟩` using `fun _ _ _ => rfl`. Establish `hβe : ∀ x y, β x = β y ↔ blk e x = blk e y` using `fun x y => by`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with h' | h'` into its components or cases. Conclude with `absurd ((hβ x y).2 h') (by omega)`. Conclude with `absurd ((hβ y x).2 h') (by omega)`. Introduce `h`.

Assume the negation of the conclusion as `hne`. Break down `lt_or_gt_of_ne hne with h' | h'` into its components or cases. Conclude with `absurd ((hβ x y).1 h') (by simp [h])`. Conclude with `absurd ((hβ y x).1 h') (by simp [h])`. Establish `hR : ∀ p q : (Σ i, Σ j, c i j), (β (ε p) = β (ε q) ∧ δ (ε p) < δ (ε q)) ↔ (q.1 = p.1 ∧ p.2.1 < q.2.1)`.

Introduce and unpack `⟨i, j, t⟩ ⟨i', j', t'⟩`. Rewrite using `[hε, hε, hβe, blk_apply, blk_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨rfl, hd⟩`. Conclude with `⟨rfl, (hδ _ _ _ _ _).1 hd⟩`.

Introduce and unpack `⟨h1, h2⟩`. Take `rfl : i' = i` from `h1`. Conclude with `⟨rfl, (hδ _ _ _ _ _).2 h2⟩`. Use `Eq.trans ?_ (prod_rel (c := c) (fun p => u (ε p)) fun _ => hu _)` and prove the remaining obligations. Rewrite using `[← Finset.prod_subtype (Finset.univ.filter fun ij : Fin N × Fin N => β ij.1 = β ij.2 ∧ δ ij.1 < δ ij.2) (by simp) (fun ij => u ij.1 / u ij.2), Finset.prod_filter, Fintype.prod_prod_type]`.

Use `(Equiv.prod_comp ε _).symm.trans (Finset.prod_congr rfl fun p _ => ?_)` and prove the remaining obligations. Use `(Equiv.prod_comp ε _).symm.trans (Finset.prod_congr rfl fun q _ => ?_)` and prove the remaining obligations. Simplify using `only [hR]`.
-/
theorem prod_pairs {N : ℕ} {m : α → Type} (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i)
    (β δ : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y)
    (hδ : ∀ i j j' (t : c i j) (t' : c i j'),
      δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j')
    {G : Type} [CommGroupWithZero G] (u : Fin N → G) (hu : ∀ x, u x ≠ 0) :
    ∏ s : {ij : Fin N × Fin N // β ij.1 = β ij.2 ∧ δ ij.1 < δ ij.2}, u s.1.1 / u s.1.2 =
      ∏ i, ∏ j, (∏ t : c i j, u (e ⟨i, f i ⟨j, t⟩⟩)) ^ modExp (c i) j := by
  classical
  let ε : (Σ i, Σ j, c i j) ≃ Fin N := (Equiv.sigmaCongrRight f).trans e
  have hε : ∀ i j t, ε ⟨i, j, t⟩ = e ⟨i, f i ⟨j, t⟩⟩ := fun _ _ _ => rfl
  have hβe : ∀ x y, β x = β y ↔ blk e x = blk e y := fun x y => by
    constructor
    · intro h
      by_contra hne
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd ((hβ x y).2 h') (by omega)
      · exact absurd ((hβ y x).2 h') (by omega)
    · intro h
      by_contra hne
      rcases lt_or_gt_of_ne hne with h' | h'
      · exact absurd ((hβ x y).1 h') (by simp [h])
      · exact absurd ((hβ y x).1 h') (by simp [h])
  have hR : ∀ p q : (Σ i, Σ j, c i j),
      (β (ε p) = β (ε q) ∧ δ (ε p) < δ (ε q)) ↔ (q.1 = p.1 ∧ p.2.1 < q.2.1) := by
    rintro ⟨i, j, t⟩ ⟨i', j', t'⟩
    rw [hε, hε, hβe, blk_apply, blk_apply]
    constructor
    · rintro ⟨rfl, hd⟩
      exact ⟨rfl, (hδ _ _ _ _ _).1 hd⟩
    · rintro ⟨h1, h2⟩
      obtain rfl : i' = i := h1
      exact ⟨rfl, (hδ _ _ _ _ _).2 h2⟩
  refine Eq.trans ?_ (prod_rel (c := c) (fun p => u (ε p)) fun _ => hu _)
  rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin N × Fin N =>
    β ij.1 = β ij.2 ∧ δ ij.1 < δ ij.2) (by simp) (fun ij => u ij.1 / u ij.2), Finset.prod_filter,
    Fintype.prod_prod_type]
  refine (Equiv.prod_comp ε _).symm.trans (Finset.prod_congr rfl fun p _ => ?_)
  refine (Equiv.prod_comp ε _).symm.trans (Finset.prod_congr rfl fun q _ => ?_)
  simp only [hR]

end Finite

end GlobalTheory.CompanionTheory.CellChar

namespace GlobalTheory.CompanionTheory.CellChar

open ValuativeRel GroundTheory.Automorphic.GLnLocal

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {k} in

/- English proof (translation)
Establish `hdet : ∀ M : Matrix n n k, (∀ a b, M a b ∈ (valuation k).integer) → M.det ∈ (valuation k).integer` using `fun M hM => by`. Rewrite using `[Matrix.det_apply']`. Conclude with `Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _) (Subring.prod_mem _ fun i _ => hM _ _)`. Establish `a1 : valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) ≤ 1` using `hdet _ h1`. Establish `a2 : valuation k (((Matrix.GeneralLinearGroup.det A)⁻¹ : kˣ) : k) ≤ 1`.

Rewrite using `[← map_inv]`. Conclude with `hdet _ h2`. Rewrite `a2` using `[Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (Units.ne_zero _)))).1 a2)`.
-/
theorem valuation_det_eq_one {n : Type} [Fintype n] [DecidableEq n] (A : GL n k)
    (h1 : ∀ a b, (A : Matrix n n k) a b ∈ (valuation k).integer)
    (h2 : ∀ a b, ((A⁻¹ : GL n k) : Matrix n n k) a b ∈ (valuation k).integer) :
    valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) = 1 := by
  have hdet : ∀ M : Matrix n n k, (∀ a b, M a b ∈ (valuation k).integer) →
      M.det ∈ (valuation k).integer := fun M hM => by
    rw [Matrix.det_apply']
    exact Subring.sum_mem _ fun σ _ => Subring.mul_mem _ (intCast_mem _ _)
      (Subring.prod_mem _ fun i _ => hM _ _)
  have a1 : valuation k ((Matrix.GeneralLinearGroup.det A : kˣ) : k) ≤ 1 := hdet _ h1
  have a2 : valuation k (((Matrix.GeneralLinearGroup.det A)⁻¹ : kˣ) : k) ≤ 1 := by
    rw [← map_inv]
    exact hdet _ h2
  rw [Units.val_inv_eq_inv_val, map_inv₀] at a2
  exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 (Units.ne_zero _)))).1 a2)

variable {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ}
  {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]

/- English proof (translation)
Take `⟨h1, h2⟩` from `(mem_integralGL_iff k N).1 hint`. Rewrite using `[relDeltaHalf_apply]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Rewrite using `[deltaHalf_apply]`. Use `Finset.prod_eq_one fun j _ => ?_` and prove the remaining obligations.

Use `isUnram_absPow k _ _ (valuation_det_eq_one _ (fun a b => ?_) fun a b => ?_)` and prove the remaining obligations. Use `h1 (e ⟨i, f i ⟨j, a⟩⟩) (e ⟨i, f i ⟨j, b⟩⟩)` as an intermediate fact. Rewrite `this` using `[leviEmb_apply_same]`. Conclude with `this`. Use `h2 (e ⟨i, f i ⟨j, a⟩⟩) (e ⟨i, f i ⟨j, b⟩⟩)` as an intermediate fact.

Rewrite `this` using `[← map_inv, leviEmb_apply_same]`. Establish `e1 : ((relProj k f ⟨x, hx⟩ i j)⁻¹ : GL (c i j) k) = relProj k f (⟨x, hx⟩⁻¹) i j`. Rewrite using `[map_inv]`. Both sides reduce to the same expression. Rewrite using `[e1]`.

Conclude with `this`.
-/
theorem relDeltaHalf_eq_one_of_integral (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i)
    (x : Levi k m) (hx : x ∈ relParab k f) (hint : leviEmb k e x ∈ integralGL k N) :
    relDeltaHalf k c (relProj k f ⟨x, hx⟩) = 1 := by
  obtain ⟨h1, h2⟩ := (mem_integralGL_iff k N).1 hint
  rw [relDeltaHalf_apply]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun j _ => ?_
  refine isUnram_absPow k _ _ (valuation_det_eq_one _ (fun a b => ?_) fun a b => ?_)
  · have := h1 (e ⟨i, f i ⟨j, a⟩⟩) (e ⟨i, f i ⟨j, b⟩⟩)
    rw [leviEmb_apply_same] at this
    exact this
  · have := h2 (e ⟨i, f i ⟨j, a⟩⟩) (e ⟨i, f i ⟨j, b⟩⟩)
    rw [← map_inv, leviEmb_apply_same] at this
    have e1 : ((relProj k f ⟨x, hx⟩ i j)⁻¹ : GL (c i j) k) = relProj k f (⟨x, hx⟩⁻¹) i j := by
      rw [map_inv]
      rfl
    rw [e1]
    exact this

/- English proof (translation)
Establish `hent : ((relProj k f ⟨x, hx⟩ i j : GL (c i j) k) : Matrix (c i j) (c i j) k) = Matrix.diagonal fun t => (uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩)`. Use extensionality with `a b`. Establish `h0 : ((relProj k f ⟨x, hx⟩ i j : GL (c i j) k) : Matrix (c i j) (c i j) k) a b = (leviEmb k e x : Matrix (Fin N) (Fin N) k) (e ⟨i, f i ⟨j, a⟩⟩) (e ⟨i, f i ⟨j, b⟩⟩)`. Rewrite using `[leviEmb_apply_same]`. Both sides reduce to the same expression.

Rewrite using `[h0, hd, GroundTheory.Automorphic.Cartan.coe_diagPow]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules. Establish `hne : e ⟨i, f i ⟨j, a⟩⟩ ≠ e ⟨i, f i ⟨j, b⟩⟩` using `fun h => hab (by simpa using h)`.

Rewrite using `[Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hab]`. Establish `hdet : ((Matrix.GeneralLinearGroup.det (relProj k f ⟨x, hx⟩ i j) : kˣ) : k) = ∏ t, (uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩)`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hent, Matrix.det_diagonal]`. Rewrite using `[GlobalTheory.SplitWeil.nabs, ← GroundTheory.Automorphic.Measures.modulus_units, hdet, map_prod, NNReal.coe_prod]`.
-/
theorem nabs_det_diag (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i)
    (x : Levi k m) (hx : x ∈ relParab k f) (μ : Fin N → ℤ)
    (hd : leviEmb k e x = GroundTheory.Automorphic.Cartan.diagPow k N μ) (i : α) (j : β') :
    GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det (relProj k f ⟨x, hx⟩ i j)) =
      ∏ t : c i j, ((GroundTheory.Automorphic.Measures.modulus
        ((uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩)) : NNReal) : ℝ) := by
  have hent : ((relProj k f ⟨x, hx⟩ i j : GL (c i j) k) : Matrix (c i j) (c i j) k) =
      Matrix.diagonal fun t => (uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩) := by
    ext a b
    have h0 : ((relProj k f ⟨x, hx⟩ i j : GL (c i j) k) : Matrix (c i j) (c i j) k) a b =
        (leviEmb k e x : Matrix (Fin N) (Fin N) k) (e ⟨i, f i ⟨j, a⟩⟩) (e ⟨i, f i ⟨j, b⟩⟩) := by
      rw [leviEmb_apply_same]
      rfl
    rw [h0, hd, GroundTheory.Automorphic.Cartan.coe_diagPow]
    by_cases hab : a = b
    · subst hab
      simp
    · have hne : e ⟨i, f i ⟨j, a⟩⟩ ≠ e ⟨i, f i ⟨j, b⟩⟩ := fun h => hab (by simpa using h)
      rw [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hab]
  have hdet : ((Matrix.GeneralLinearGroup.det (relProj k f ⟨x, hx⟩ i j) : kˣ) : k) =
      ∏ t, (uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hent, Matrix.det_diagonal]
  rw [GlobalTheory.SplitWeil.nabs, ← GroundTheory.Automorphic.Measures.modulus_units, hdet, map_prod, NNReal.coe_prod]

/- English proof (translation)
Establish `h1 : ∀ i, GlobalTheory.SmGL.modulus k (c i) (relProj k f ⟨x, hx⟩ i) = ∏ j, (∏ t : c i j, ((GroundTheory.Automorphic.Measures.modulus ((uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩)) : NNReal) : ℝ)) ^ modExp (c i) j` using `fun i => by`. Rewrite using `[GlobalTheory.SmGL.modulus]`. Conclude with `Finset.prod_congr rfl fun j _ => by rw [nabs_det_diag k e f x hx μ hd i j]`. Repeatedly rewrite using `[← h1]`. Rewrite using `[relDeltaHalf_apply, Units.coe_prod, Real.sqrt_prod _ fun i _ => (GlobalTheory.SmGL.modulus_pos k _).le, Complex.ofReal_prod]`.

Conclude with `Finset.prod_congr rfl fun i _ => val_deltaHalf k _`.
-/
theorem relDeltaHalf_diag (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i)
    (x : Levi k m) (hx : x ∈ relParab k f) (μ : Fin N → ℤ)
    (hd : leviEmb k e x = GroundTheory.Automorphic.Cartan.diagPow k N μ) :
    ((relDeltaHalf k c (relProj k f ⟨x, hx⟩) : ℂˣ) : ℂ) =
      ((√(∏ i, ∏ j, (∏ t : c i j, ((GroundTheory.Automorphic.Measures.modulus
        ((uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩)) : NNReal) : ℝ)) ^ modExp (c i) j) : ℝ) : ℂ) := by
  have h1 : ∀ i, GlobalTheory.SmGL.modulus k (c i) (relProj k f ⟨x, hx⟩ i) =
      ∏ j, (∏ t : c i j, ((GroundTheory.Automorphic.Measures.modulus
        ((uniformizer k : k) ^ μ (e ⟨i, f i ⟨j, t⟩⟩)) : NNReal) : ℝ)) ^ modExp (c i) j := fun i => by
    rw [GlobalTheory.SmGL.modulus]
    exact Finset.prod_congr rfl fun j _ => by rw [nabs_det_diag k e f x hx μ hd i j]
  simp_rw [← h1]
  rw [relDeltaHalf_apply, Units.coe_prod,
    Real.sqrt_prod _ fun i _ => (GlobalTheory.SmGL.modulus_pos k _).le, Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun i _ => val_deltaHalf k _

/- English proof (translation)
Rewrite using `[relDeltaHalf_diag k e f x hx μ hd]`. Use `show ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter _) : ℝ) : ℂ) = _`. Rewrite using `[GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar_diagPow, prod_pairs e f β δ hβ hδ (fun y => GroundTheory.Automorphic.Measures.modulus ((uniformizer k : k) ^ μ y)) fun y => GroundTheory.Automorphic.Measures.modulus_ne_zero (zpow_ne_zero _ (GroundTheory.Automorphic.Car …`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem normLeviParSqrtModular_diag (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i)
    (β δ : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y)
    (hδ : ∀ i j j' (t : c i j) (t' : c i j'),
      δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j')
    (x : Levi k m) (hx : x ∈ relParab k f) (μ : Fin N → ℤ)
    (hd : leviEmb k e x = GroundTheory.Automorphic.Cartan.diagPow k N μ) :
    normLeviParSqrtModular k β δ ⟨GroundTheory.Automorphic.Cartan.diagPow k N μ,
      GroundTheory.Automorphic.Parabolic.diagPow_mem_leviPar μ⟩ =
      ((relDeltaHalf k c (relProj k f ⟨x, hx⟩) : ℂˣ) : ℂ) := by
  rw [relDeltaHalf_diag k e f x hx μ hd]
  show ((NNReal.sqrt (MeasureTheory.Measure.modularCharacter _) : ℝ) : ℂ) = _
  rw [GroundTheory.Automorphic.Parabolic.modularCharacter_leviPar_diagPow,
    prod_pairs e f β δ hβ hδ (fun y => GroundTheory.Automorphic.Measures.modulus
      ((uniformizer k : k) ^ μ y)) fun y => GroundTheory.Automorphic.Measures.modulus_ne_zero
        (zpow_ne_zero _ (GroundTheory.Automorphic.Cartan.uniformizer_ne_zero k)),
    Real.coe_sqrt]
  push_cast
  rfl

end Local

/- English proof (translation)
Introduce `k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f β δ hβ hδ hmem φ hφ x hx h`. Establish `hinv : ∀ y : levi k N β, leviEmb k e (φ.symm y) = (y : GL (Fin N) k)` using `fun y => by`. Rewrite using `[← hφ, φ.apply_symm_apply]`. Set `Θ : leviPar k N β δ →* relParab k f` to `{ toFun := fun l => ⟨φ.symm ⟨l.1, l.2.1⟩, (hmem _).2 (by rw [hinv]; exact l.2.2)⟩ map_one' := Subtype.ext (map_one φ.symm) map_mul' := fun a b => Subtype.ext (map_mul φ.symm ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩) }`. Set `ψ : leviPar k N β δ →* ℂ` to `(Units.coeHom ℂ).comp ((relDeltaHalf k c).comp ((relProj k f).comp Θ))`.

Take `⟨μ, hμ⟩` from `GroundTheory.Automorphic.Parabolic.exists_diagPow_eq (F := k) (γ := β) (δ := δ) ⟨_, h⟩`. Establish `e1` using `hμ (normLeviParSqrtModular k β δ) fun l hl => GroundTheory.Automorphic.Parabolic.normLeviParSqrtModular_eq_one hl`. Establish `e2` using `hμ ψ fun l hl => by show ((relDeltaHalf k c (relProj k f (Θ l)) : ℂˣ) : ℂ) = 1`. Rewrite using `[show Θ l = ⟨(Θ l).1, (Θ l).2⟩ from rfl, relDeltaHalf_eq_one_of_integral k e f _ _ (by show leviEmb k e (φ.symm ⟨l.1, l.2.1⟩) ∈ _`. Rewrite using `[hinv]`.

Conclude with `hl)]`. Both sides reduce to the same expression. Establish `e3 : ψ ⟨_, h⟩ = ((relDeltaHalf k c (relProj k f ⟨x, hx⟩) : ℂˣ) : ℂ)`. Establish `h3 : Θ ⟨_, h⟩ = ⟨x, hx⟩` using `Subtype.ext (φ.symm_apply_apply x)`. Use `show ((relDeltaHalf k c (relProj k f (Θ ⟨_, h⟩)) : ℂˣ) : ℂ) = _`.

Rewrite using `[h3]`. Rewrite using `[e1, ← e3, e2]`. Conclude with `normLeviParSqrtModular_diag k e f β δ hβ hδ _ (Θ _).2 μ (hinv _)`.
-/
theorem normLeviParSqrtModular_eq_relDeltaHalf : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α β' : Type} [Fintype α] [LinearOrder α] [Fintype β'] [LinearOrder β'] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {c : α → β' → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)] (e : (Σ i, m i) ≃ Fin N) (f : ∀ i, (Σ j, c i j) ≃ m i) (β δ : Fin N → ℕ) (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (hδ : ∀ i j j' (t : c i j) (t' : c i j'), δ (e ⟨i, f i ⟨j, t⟩⟩) < δ (e ⟨i, f i ⟨j', t'⟩⟩) ↔ j < j') (hmem : ∀ x : Levi k m, x ∈ relParab k f ↔ leviEmb k e x ∈ blockUpper k N δ) (φ : Levi k m ≃* levi k N β) (hφ : ∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) (x : Levi k m) (hx : x ∈ relParab k f) (h : ((φ x : levi k N β) : GL (Fin N) k) ∈ leviPar k N β δ), normLeviParSqrtModular k β δ ⟨_, h⟩ = ((relDeltaHalf k c (relProj k f ⟨x, hx⟩) : ℂˣ) : ℂ) := by
  intro k _ _ _ _ α β' _ _ _ _ N m _ _ c _ _ e f β δ hβ hδ hmem φ hφ x hx h
  have hinv : ∀ y : levi k N β, leviEmb k e (φ.symm y) = (y : GL (Fin N) k) := fun y => by
    rw [← hφ, φ.apply_symm_apply]
  let Θ : leviPar k N β δ →* relParab k f :=
    { toFun := fun l => ⟨φ.symm ⟨l.1, l.2.1⟩, (hmem _).2 (by rw [hinv]; exact l.2.2)⟩
      map_one' := Subtype.ext (map_one φ.symm)
      map_mul' := fun a b => Subtype.ext (map_mul φ.symm ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩) }
  let ψ : leviPar k N β δ →* ℂ :=
    (Units.coeHom ℂ).comp ((relDeltaHalf k c).comp ((relProj k f).comp Θ))
  obtain ⟨μ, hμ⟩ := GroundTheory.Automorphic.Parabolic.exists_diagPow_eq (F := k) (γ := β) (δ := δ) ⟨_, h⟩
  have e1 := hμ (normLeviParSqrtModular k β δ) fun l hl =>
    GroundTheory.Automorphic.Parabolic.normLeviParSqrtModular_eq_one hl
  have e2 := hμ ψ fun l hl => by
    show ((relDeltaHalf k c (relProj k f (Θ l)) : ℂˣ) : ℂ) = 1
    rw [show Θ l = ⟨(Θ l).1, (Θ l).2⟩ from rfl,
      relDeltaHalf_eq_one_of_integral k e f _ _ (by
        show leviEmb k e (φ.symm ⟨l.1, l.2.1⟩) ∈ _
        rw [hinv]
        exact hl)]
    rfl
  have e3 : ψ ⟨_, h⟩ = ((relDeltaHalf k c (relProj k f ⟨x, hx⟩) : ℂˣ) : ℂ) := by
    have h3 : Θ ⟨_, h⟩ = ⟨x, hx⟩ := Subtype.ext (φ.symm_apply_apply x)
    show ((relDeltaHalf k c (relProj k f (Θ ⟨_, h⟩)) : ℂˣ) : ℂ) = _
    rw [h3]
  rw [e1, ← e3, e2]
  exact normLeviParSqrtModular_diag k e f β δ hβ hδ _ (Θ _).2 μ (hinv _)

end GlobalTheory.CompanionTheory.CellChar
