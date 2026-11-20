import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.GeometricLemma
set_option maxSynthPendingDepth 1

open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.DeltaLevi

open GroundTheory.Automorphic.Measures

/- English proof (translation)
Establish `hz : ∀ (y : G) (f : α → ℤ), ∏ b, y ^ f b = y ^ ∑ b, f b`. Introduce `y f`. Proceed by induction on `(Finset.univ : Finset α) using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]`.

Establish `h1 : ∀ c : α × α, (if c.1 ≤ c.2 then x c.1 ^ (n c.2 : ℤ) * (x c.2)⁻¹ ^ (n c.1 : ℤ) else 1) = x c.1 ^ (if c.1 ≤ c.2 then (n c.2 : ℤ) else 0) * x c.2 ^ (-(if c.1 ≤ c.2 then (n c.1 : ℤ) else 0))`. Introduce `c`. Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [h1]`. Rewrite using `[Finset.prod_mul_distrib, Fintype.prod_prod_type, Fintype.prod_prod_type, Finset.prod_comm (s := Finset.univ) (t := Finset.univ) (f := fun a b => x b ^ (-(if a ≤ b then (n a : ℤ) else 0))), ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hz, hz, ← zpow_add, Finset.sum_neg_distrib, Finset.sum_filter, Finset.sum_filter, ← sub_eq_add_neg, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Break down `lt_trichotomy a b with h | h | h` into its components or cases. Simplify using `[h, h.le, h.not_ge, h.not_gt]`. Simplify using `[h]`. Simplify using `[h, h.le, h.not_ge, h.not_gt]`.
-/
theorem prod_pairs_le {α G : Type} [Fintype α] [LinearOrder α] [CommGroup G] (n : α → ℕ) (x : α → G) :
    ∏ c : α × α, (if c.1 ≤ c.2 then x c.1 ^ (n c.2 : ℤ) * (x c.2)⁻¹ ^ (n c.1 : ℤ) else 1) =
      ∏ a, x a ^ ((∑ b with a < b, (n b : ℤ)) - ∑ b with b < a, (n b : ℤ)) := by
  have hz : ∀ (y : G) (f : α → ℤ), ∏ b, y ^ f b = y ^ ∑ b, f b := by
    intro y f
    induction (Finset.univ : Finset α) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add]
  have h1 : ∀ c : α × α, (if c.1 ≤ c.2 then x c.1 ^ (n c.2 : ℤ) * (x c.2)⁻¹ ^ (n c.1 : ℤ) else 1) =
      x c.1 ^ (if c.1 ≤ c.2 then (n c.2 : ℤ) else 0) *
        x c.2 ^ (-(if c.1 ≤ c.2 then (n c.1 : ℤ) else 0)) := by
    intro c
    split_ifs <;> simp
  simp only [h1]
  rw [Finset.prod_mul_distrib, Fintype.prod_prod_type, Fintype.prod_prod_type,
    Finset.prod_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun a b => x b ^ (-(if a ≤ b then (n a : ℤ) else 0))), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  dsimp only
  rw [hz, hz, ← zpow_add, Finset.sum_neg_distrib, Finset.sum_filter, Finset.sum_filter,
    ← sub_eq_add_neg, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy a b with h | h | h
  · simp [h, h.le, h.not_ge, h.not_gt]
  · simp [h]
  · simp [h, h.le, h.not_ge, h.not_gt]

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)]
  [∀ i, DecidableEq (m i)]

/- English proof (translation)
Take `⟨⟨a, i⟩, rfl⟩` from `e.surjective i`. Take `⟨⟨b, j⟩, rfl⟩` from `e.surjective j`. Conclude with `leviEmb_apply_ne k e g (by simpa using h) i j`.
-/
theorem leviEmb_eq_zero (e : (Σ i, m i) ≃ Fin N) (g : Levi k m) {i j : Fin N}
    (h : blk e i ≠ blk e j) : (leviEmb k e g : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
  exact leviEmb_apply_ne k e g (by simpa using h) i j

/- English proof (translation)
Use `set P : Matrix (Fin N) (Fin N) k := ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) with hPdef`. Use `set Q : Matrix (Fin N) (Fin N) k := (((p : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) with hQdef`. Establish `hP : P = (leviEmb k e g : Matrix (Fin N) (Fin N) k)` using `by rw [hPdef, hp]`. Establish `hQ : Q = (leviEmb k e g⁻¹ : Matrix (Fin N) (Fin N) k)` using `by rw [hQdef, hp, map_inv]`. Set `A : (ParabolicIndex N β → k) →ₗ[k] (ParabolicIndex N β → k)` to `(((parabolicCoord k N β).symm.trans ((adLie k N β p).trans (parabolicCoord k N β))) : (ParabolicIndex N β → k) →ₗ[k] (ParabolicIndex N β → k))`.

Establish `hdet : (LinearEquiv.det (adLie k N β p) : k) = LinearMap.det A`. Rewrite using `[← LinearEquiv.det_conj (adLie k N β p) (parabolicCoord k N β), LinearEquiv.coe_det]`. Both sides reduce to the same expression. Establish `hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2`. Introduce `s t`.

Rewrite using `[LinearMap.toMatrix'_apply]`. Use `show ((adLie k N β p ((parabolicCoord k N β).symm (Pi.single t 1)) : lieParabolic k N β) : Matrix (Fin N) (Fin N) k) s.1.1 s.1.2 = _`. Rewrite using `[coe_adLie, coe_parabolicCoord_symm_single, mul_single_mul_apply]`. Set `κ : ParabolicIndex N β → α ×ₗ α` to `fun s => toLex (blk e s.1.1, blk e s.1.2)`. Establish `hzero : ∀ s t, κ s ≠ κ t → LinearMap.toMatrix' A s t = 0`.

Introduce `s t hst`. Rewrite using `[hM]`. Distinguish the cases in `h1 : blk e s.1.1 = blk e t.1.1`. Establish `h2 : blk e t.1.2 ≠ blk e s.1.2`. Introduce `h2`.

Conclude with `hst (by simp only [κ, h1, h2])`. Rewrite using `[hQ, leviEmb_eq_zero e _ h2, mul_zero]`. Rewrite using `[hP, leviEmb_eq_zero e _ h1, zero_mul]`. Establish `hBT : (LinearMap.toMatrix' A).BlockTriangular κ` using `fun s t hts => hzero s t hts.ne'`. Establish `hblock : ∀ a b : α, ((LinearMap.toMatrix' A).toSquareBlock κ (toLex (a, b))).det = if a ≤ b then ((g a : GL (m a) k) : Matrix (m a) (m a) k).det ^ Fintype.card (m b) * ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).det ^ Fintype.card (m a) else 1`.

Introduce `a b`. Distinguish the cases in `hab : a ≤ b`. Rewrite using `[if_pos hab]`. Establish `hmem : ∀ (i : m a) (j : m b), ¬ β (e ⟨b, j⟩) < β (e ⟨a, i⟩)`. Introduce `i j`.

Rewrite using `[hβ]`. Simplify using `using hab`. Set `f : m a × m b → {t : ParabolicIndex N β // κ t = toLex (a, b)}` to `fun x => ⟨⟨(e ⟨a, x.1⟩, e ⟨b, x.2⟩), hmem x.1 x.2⟩, by simp [κ]⟩`. Establish `hf : Function.Bijective f`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨i, j⟩ ⟨i', j'⟩ h`. Establish `h1` using `congrArg (fun t => t.1.1.1) h`. Establish `h2` using `congrArg (fun t => t.1.1.2) h`. Simplify using `only [f] at h1 h2`. Establish `h1'` using `e.injective h1`.

Establish `h2'` using `e.injective h2`. Simplify using `only [Sigma.mk.injEq, heq_eq_eq, true_and] at h1' h2'`. Rewrite using `[h1', h2']`. Introduce and unpack `⟨⟨⟨i, j⟩, hij⟩, hκ⟩`. Take `⟨⟨a', i⟩, rfl⟩` from `e.surjective i`.

Take `⟨⟨b', j⟩, rfl⟩` from `e.surjective j`. Establish `h3 : a' = a ∧ b' = b` using `by simpa [κ] using hκ`. Take `⟨rfl, rfl⟩` from `h3`. Conclude with `⟨(i, j), rfl⟩`. Rewrite using `[← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf)]`.

Establish `hk : ((LinearMap.toMatrix' A).toSquareBlock κ (toLex (a, b))).submatrix (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) = Matrix.kroneckerMap (· * ·) ((g a : GL (m a) k) : Matrix (m a) (m a) k) ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).transpose`. Use extensionality with `⟨i, j⟩ ⟨i', j'⟩`. Use `show LinearMap.toMatrix' A (f (i, j)).1 (f (i', j')).1 = _`. Rewrite using `[hM, hP, hQ]`. Use `show (leviEmb k e g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, i'⟩) * (leviEmb k e g⁻¹ : Matrix (Fin N) (Fin N) k) (e ⟨b, j'⟩) (e ⟨b, j⟩) = _`.

Rewrite using `[leviEmb_apply_same, leviEmb_apply_same]`. Both sides reduce to the same expression. Rewrite using `[hk, Matrix.det_kronecker, Matrix.det_transpose]`. Rewrite using `[if_neg hab]`. Establish `: IsEmpty {t : ParabolicIndex N β // κ t = toLex (a, b)}`.

Use `⟨fun t => hab ?_⟩` and prove the remaining obligations. Establish `h3 : blk e t.1.1.1 = a ∧ blk e t.1.1.2 = b` using `by simpa [κ] using t.2`. Establish `h4` using `t.1.2`. Rewrite `h4` using `[hβ, h3.1, h3.2]`. Conclude with `not_lt.1 h4`.

Conclude with `Matrix.det_isEmpty`. Rewrite using `[hdet, ← LinearMap.det_toMatrix', hBT.det]`. Rewrite using `[Finset.prod_subset (Finset.subset_univ _) (fun c _ hc => by`. Establish `: IsEmpty {t : ParabolicIndex N β // κ t = c}` using `⟨fun t => hc (Finset.mem_image.2 ⟨t.1, Finset.mem_univ _, t.2⟩)⟩`. Conclude with `Matrix.det_isEmpty)]`.

Rewrite using `[← Equiv.prod_comp toLex]`. Conclude with `Finset.prod_congr rfl fun c _ => hblock c.1 c.2`.
-/
theorem det_adLie_pairs (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ)
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (p : blockUpper k N β) (g : Levi k m)
    (hp : (p : GL (Fin N) k) = leviEmb k e g) :
    (LinearEquiv.det (adLie k N β p) : k) =
      ∏ c : α × α, if c.1 ≤ c.2 then
        ((g c.1 : GL (m c.1) k) : Matrix (m c.1) (m c.1) k).det ^ Fintype.card (m c.2) *
          ((((g c.2)⁻¹ : GL (m c.2) k)) : Matrix (m c.2) (m c.2) k).det ^ Fintype.card (m c.1)
      else 1 := by
  classical
  set P : Matrix (Fin N) (Fin N) k := ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) with hPdef
  set Q : Matrix (Fin N) (Fin N) k :=
    (((p : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) with hQdef
  have hP : P = (leviEmb k e g : Matrix (Fin N) (Fin N) k) := by rw [hPdef, hp]
  have hQ : Q = (leviEmb k e g⁻¹ : Matrix (Fin N) (Fin N) k) := by rw [hQdef, hp, map_inv]
  let A : (ParabolicIndex N β → k) →ₗ[k] (ParabolicIndex N β → k) :=
    (((parabolicCoord k N β).symm.trans ((adLie k N β p).trans (parabolicCoord k N β))) :
      (ParabolicIndex N β → k) →ₗ[k] (ParabolicIndex N β → k))
  have hdet : (LinearEquiv.det (adLie k N β p) : k) = LinearMap.det A := by
    rw [← LinearEquiv.det_conj (adLie k N β p) (parabolicCoord k N β), LinearEquiv.coe_det]
    rfl
  have hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2 := by
    intro s t
    rw [LinearMap.toMatrix'_apply]
    show ((adLie k N β p ((parabolicCoord k N β).symm (Pi.single t 1)) : lieParabolic k N β) :
      Matrix (Fin N) (Fin N) k) s.1.1 s.1.2 = _
    rw [coe_adLie, coe_parabolicCoord_symm_single, mul_single_mul_apply]
  let κ : ParabolicIndex N β → α ×ₗ α := fun s => toLex (blk e s.1.1, blk e s.1.2)
  have hzero : ∀ s t, κ s ≠ κ t → LinearMap.toMatrix' A s t = 0 := by
    intro s t hst
    rw [hM]
    by_cases h1 : blk e s.1.1 = blk e t.1.1
    · have h2 : blk e t.1.2 ≠ blk e s.1.2 := by
        intro h2
        exact hst (by simp only [κ, h1, h2])
      rw [hQ, leviEmb_eq_zero e _ h2, mul_zero]
    · rw [hP, leviEmb_eq_zero e _ h1, zero_mul]
  have hBT : (LinearMap.toMatrix' A).BlockTriangular κ := fun s t hts => hzero s t hts.ne'
  have hblock : ∀ a b : α, ((LinearMap.toMatrix' A).toSquareBlock κ (toLex (a, b))).det =
      if a ≤ b then
        ((g a : GL (m a) k) : Matrix (m a) (m a) k).det ^ Fintype.card (m b) *
          ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).det ^ Fintype.card (m a)
      else 1 := by
    intro a b
    by_cases hab : a ≤ b
    · rw [if_pos hab]
      have hmem : ∀ (i : m a) (j : m b), ¬ β (e ⟨b, j⟩) < β (e ⟨a, i⟩) := by
        intro i j
        rw [hβ]
        simpa using hab
      let f : m a × m b → {t : ParabolicIndex N β // κ t = toLex (a, b)} := fun x =>
        ⟨⟨(e ⟨a, x.1⟩, e ⟨b, x.2⟩), hmem x.1 x.2⟩, by simp [κ]⟩
      have hf : Function.Bijective f := by
        constructor
        · rintro ⟨i, j⟩ ⟨i', j'⟩ h
          have h1 := congrArg (fun t => t.1.1.1) h
          have h2 := congrArg (fun t => t.1.1.2) h
          simp only [f] at h1 h2
          have h1' := e.injective h1
          have h2' := e.injective h2
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h1' h2'
          rw [h1', h2']
        · rintro ⟨⟨⟨i, j⟩, hij⟩, hκ⟩
          obtain ⟨⟨a', i⟩, rfl⟩ := e.surjective i
          obtain ⟨⟨b', j⟩, rfl⟩ := e.surjective j
          have h3 : a' = a ∧ b' = b := by simpa [κ] using hκ
          obtain ⟨rfl, rfl⟩ := h3
          exact ⟨(i, j), rfl⟩
      rw [← Matrix.det_submatrix_equiv_self (Equiv.ofBijective f hf)]
      have hk : ((LinearMap.toMatrix' A).toSquareBlock κ (toLex (a, b))).submatrix
          (Equiv.ofBijective f hf) (Equiv.ofBijective f hf) =
          Matrix.kroneckerMap (· * ·) ((g a : GL (m a) k) : Matrix (m a) (m a) k)
            ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).transpose := by
        ext ⟨i, j⟩ ⟨i', j'⟩
        show LinearMap.toMatrix' A (f (i, j)).1 (f (i', j')).1 = _
        rw [hM, hP, hQ]
        show (leviEmb k e g : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, i'⟩) *
          (leviEmb k e g⁻¹ : Matrix (Fin N) (Fin N) k) (e ⟨b, j'⟩) (e ⟨b, j⟩) = _
        rw [leviEmb_apply_same, leviEmb_apply_same]
        rfl
      rw [hk, Matrix.det_kronecker, Matrix.det_transpose]
    · rw [if_neg hab]
      have : IsEmpty {t : ParabolicIndex N β // κ t = toLex (a, b)} := by
        refine ⟨fun t => hab ?_⟩
        have h3 : blk e t.1.1.1 = a ∧ blk e t.1.1.2 = b := by simpa [κ] using t.2
        have h4 := t.1.2
        rw [hβ, h3.1, h3.2] at h4
        exact not_lt.1 h4
      exact Matrix.det_isEmpty
  rw [hdet, ← LinearMap.det_toMatrix', hBT.det]
  rw [Finset.prod_subset (Finset.subset_univ _) (fun c _ hc => by
    have : IsEmpty {t : ParabolicIndex N β // κ t = c} :=
      ⟨fun t => hc (Finset.mem_image.2 ⟨t.1, Finset.mem_univ _, t.2⟩)⟩
    exact Matrix.det_isEmpty)]
  rw [← Equiv.prod_comp toLex]
  exact Finset.prod_congr rfl fun c _ => hblock c.1 c.2

/- English proof (translation)
Establish `h` using `prod_pairs_le (fun a => Fintype.card (m a)) (fun a => Matrix.GeneralLinearGroup.det (g a))`. Establish `hd : ∀ b, ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).det = (((Matrix.GeneralLinearGroup.det (g b))⁻¹ : kˣ) : k)` using `fun b => by`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression. Establish `hd' : ∀ a, ((g a : GL (m a) k) : Matrix (m a) (m a) k).det = ((Matrix.GeneralLinearGroup.det (g a) : kˣ) : k)` using `fun a => rfl`.

Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[det_adLie_pairs e β hβ p g hp]`. Express the relevant statement in the definitionally equal form `_ = ((∏ a, Matrix.GeneralLinearGroup.det (g a) ^ ((∑ b with a < b, (Fintype.card (m b) : ℤ)) - ∑ b with b < a, (Fintype.card (m b) : ℤ)) : kˣ) : k)`. Rewrite using `[← h, Units.coe_prod]`. Use `Finset.prod_congr rfl fun c _ => ?_` and prove the remaining obligations.

Use `split_ifs with hc`. Simplify using `only [hd, hd', zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]`. Both sides reduce to the same expression.
-/
theorem det_adLie_levi (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ)
    (hβ : ∀ x y, β x < β y ↔ blk e x < blk e y) (p : blockUpper k N β) (g : Levi k m)
    (hp : (p : GL (Fin N) k) = leviEmb k e g) :
    LinearEquiv.det (adLie k N β p) = ∏ a, Matrix.GeneralLinearGroup.det (g a) ^ modExp m a := by
  have h := prod_pairs_le (fun a => Fintype.card (m a))
    (fun a => Matrix.GeneralLinearGroup.det (g a))
  have hd : ∀ b, ((((g b)⁻¹ : GL (m b) k)) : Matrix (m b) (m b) k).det =
      (((Matrix.GeneralLinearGroup.det (g b))⁻¹ : kˣ) : k) := fun b => by
    rw [← map_inv]
    rfl
  have hd' : ∀ a, ((g a : GL (m a) k) : Matrix (m a) (m a) k).det =
      ((Matrix.GeneralLinearGroup.det (g a) : kˣ) : k) := fun a => rfl
  refine Units.ext ?_
  rw [det_adLie_pairs e β hβ p g hp]
  change _ = ((∏ a, Matrix.GeneralLinearGroup.det (g a) ^
    ((∑ b with a < b, (Fintype.card (m b) : ℤ)) - ∑ b with b < a, (Fintype.card (m b) : ℤ)) : kˣ) : k)
  rw [← h, Units.coe_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  split_ifs with hc
  · simp only [hd, hd', zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
  · rfl

/- English proof (translation)
Introduce `k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ g`. Establish `hp : ((leviIncl (φ g) : blockUpper k N β) : GL (Fin N) k) = leviEmb k e g` using `hφ g`. Establish `h` using `modularCharacter_blockUpper (leviIncl (φ g))`. Establish `hs : sqrtModular k N β (leviIncl (φ g)) = ((NNReal.sqrt (MeasureTheory.distribHaarChar k (LinearEquiv.det (adLie k N β (leviIncl (φ g))))) : ℝ) : ℂ)`. Rewrite using `[← h]`.

Both sides reduce to the same expression. Establish `hm : modulus k m g = ((MeasureTheory.distribHaarChar k (LinearEquiv.det (adLie k N β (leviIncl (φ g)))) : NNReal) : ℝ)`. Unfold `GlobalTheory.SmGL.modulus`. Rewrite using `[det_adLie_levi e β hβ _ g hp, map_prod, NNReal.coe_prod]`. Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[map_zpow, NNReal.coe_zpow]`. Both sides reduce to the same expression. Rewrite using `[hs, val_deltaHalf, hm, Real.coe_sqrt]`.
-/
theorem deltaHalf_eq_sqrtModular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type}
    [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ),
    (∀ x y, β x < β y ↔ blk e x < blk e y) → ∀ (φ : Levi k m ≃* levi k N β),
    (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) →
    ∀ g : Levi k m, ((deltaHalf k m g : ℂˣ) : ℂ) = sqrtModular k N β (leviIncl (φ g)) := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ φ hφ g
  have hp : ((leviIncl (φ g) : blockUpper k N β) : GL (Fin N) k) = leviEmb k e g := hφ g
  have h := modularCharacter_blockUpper (leviIncl (φ g))
  have hs : sqrtModular k N β (leviIncl (φ g)) = ((NNReal.sqrt (MeasureTheory.distribHaarChar k
      (LinearEquiv.det (adLie k N β (leviIncl (φ g))))) : ℝ) : ℂ) := by
    rw [← h]
    rfl
  have hm : modulus k m g = ((MeasureTheory.distribHaarChar k
      (LinearEquiv.det (adLie k N β (leviIncl (φ g)))) : NNReal) : ℝ) := by
    unfold GlobalTheory.SmGL.modulus
    rw [det_adLie_levi e β hβ _ g hp, map_prod, NNReal.coe_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [map_zpow, NNReal.coe_zpow]
    rfl
  rw [hs, val_deltaHalf, hm, Real.coe_sqrt]

end

end GlobalTheory.CompanionTheory.DeltaLevi
