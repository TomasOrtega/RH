import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensFFCnt

noncomputable section

namespace PI.VolStabW.FFHS

open Module Polynomial

section matrix

variable {K : Type} [Field K] {σ : K →+* K}

/- English proof (translation)
Simplify using `only [ffH, Pi.add_apply, mul_add, Finset.sum_add_distrib]`. Use `smul_right c x y := by`. Simplify using `only [ffH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))`. Use `herm x y := by`.

Simplify using `only [ffH, map_sum, map_mul, hσ, hJ]`. Use `conv_rhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))`. Use `nondeg x hx := by`. Establish `hv : Matrix.vecMul (fun i => σ (x i)) J = 0`.

Use function extensionality and compare the values at `j0`. Use `hx (Pi.single j0 1)` as an intermediate fact. Simplify `this` using `[ffH, Pi.single_apply, Matrix.vecMul, dotProduct]`. Establish `hinv : (fun i => σ (x i)) = 0`. Use `congrArg (fun v => Matrix.vecMul v J⁻¹) hv` as an intermediate fact.

Simplify `this` using `only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet, Matrix.vecMul_one, Matrix.zero_vecMul]`. Use function extensionality and compare the values at `i`. Conclude with `σ.injective (by simpa using congrFun hinv i)`.
-/
theorem ffH_isHS (hσ : ∀ x, σ (σ x) = x) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)
    (hJ : ∀ i j, σ (J j i) = J i j) (hdet : IsUnit J.det) : IsHS σ (ffH σ J) where
  add_right x y z := by
    simp only [ffH, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  smul_right c x y := by
    simp only [ffH, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  herm x y := by
    simp only [ffH, map_sum, map_mul, hσ, hJ]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  nondeg x hx := by
    have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := by
      funext j0
      have := hx (Pi.single j0 1)
      simpa [ffH, Pi.single_apply, Matrix.vecMul, dotProduct] using this
    have hinv : (fun i => σ (x i)) = 0 := by
      have := congrArg (fun v => Matrix.vecMul v J⁻¹) hv
      simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv J hdet, Matrix.vecMul_one,
        Matrix.zero_vecMul] using this
    funext i
    exact σ.injective (by simpa using congrFun hinv i)

/- English proof (translation)
Simplify using `[ffH, Pi.single_apply, apply_ite σ]`.
-/
theorem ffH_single {n : ℕ} (T : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    ffH σ T (Pi.single i 1) (Pi.single j 1) = T i j := by
  simp [ffH, Pi.single_apply, apply_ite σ]

end matrix

/- English proof (translation)
The claim follows from `Nat.card_congr (Equiv.subtypeEquiv (b.constr K).symm.toEquiv (fun φ => by simp only [LinearEquiv.coe_toEquiv, Basis.constr_symm_apply] constructor · intro H i j; exact H _ _ · intro H x y have hs2 : IsSq σ (fun x y => hV (φ x) (φ y)) := ⟨fun x y z => by simp only [map_add, hsV.ad …`.
-/
theorem card_isom {K : Type} [Field K] {σ : K →+* K} {U V : Type} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {hU : U → U → K} {hV : V → V → K} (hsU : IsSq σ hU)
    (hsV : IsSq σ hV) {ι : Type} (b : Basis ι K U) :
    Nat.card {φ : U →ₗ[K] V // ∀ x y, hV (φ x) (φ y) = hU x y} =
      Nat.card {Y : ι → V // ∀ i j, hV (Y i) (Y j) = hU (b i) (b j)} :=
  Nat.card_congr (Equiv.subtypeEquiv (b.constr K).symm.toEquiv (fun φ => by
    simp only [LinearEquiv.coe_toEquiv, Basis.constr_symm_apply]
    constructor
    · intro H i j; exact H _ _
    · intro H x y
      have hs2 : IsSq σ (fun x y => hV (φ x) (φ y)) :=
        ⟨fun x y z => by simp only [map_add, hsV.add_right],
          fun c x y => by simp only [map_smul, hsV.smul_right],
          fun x y => hsV.herm _ _⟩
      exact (hs2.ext_basis hsU b H x y)))

section field

variable {k K : Type} [Field k] [Fintype k] [Field K] [Fintype K] [DecidableEq K] [Algebra k K]

/- English proof (translation)
Take `⟨⟨n, hn'⟩, hn⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k K).2 σ`. Simplify using `only at hn`. Establish `: n = 0 ∨ n = 1` using `by omega`. Break down `this with rfl | rfl` into its components or cases. Conclude with `absurd (by rw [← hn, pow_zero]; rfl) hne`.

Introduce `x`. Rewrite using `[← hn, pow_one]`. Both sides reduce to the same expression.
-/
theorem frob_of_ne (σ : K ≃ₐ[k] K) (h2 : finrank k K = 2) (hne : σ ≠ AlgEquiv.refl) :
    ∀ x, σ x = x ^ Fintype.card k := by
  obtain ⟨⟨n, hn'⟩, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k K).2 σ
  simp only at hn
  have : n = 0 ∨ n = 1 := by omega
  rcases this with rfl | rfl
  · exact absurd (by rw [← hn, pow_zero]; rfl) hne
  · intro x
    rw [← hn, pow_one]
    rfl

/- English proof (translation)
Establish `hq : 1 < Fintype.card k` using `Fintype.one_lt_card`. Assume the negation of the conclusion as `H`. Use `push_neg at H`. Establish `hdm : d ∉ Finset.univ.image (algebraMap k K)` using `by simpa using H`. Use `card_le_degree_of_subset_roots (p := (X ^ Fintype.card k - X : K[X])) (Z := insert d (Finset.univ.image (algebraMap k K))) (fun x hx => by` as an intermediate fact.

Rewrite using `[mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hq), IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero]`. Break down `Finset.mem_insert.1 hx with rfl | hx` into its components or cases. Conclude with `hd`. Take `⟨c, _, rfl⟩` from `Finset.mem_image.1 hx`. Rewrite using `[← map_pow, FiniteField.pow_card])`.

Rewrite `this` using `[FiniteField.X_pow_card_sub_X_natDegree_eq K hq, Finset.card_insert_of_notMem hdm, Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ]`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_range_of_pow (d : K) (hd : d ^ Fintype.card k = d) :
    ∃ d0 : k, algebraMap k K d0 = d := by
  classical
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  by_contra H
  push_neg at H
  have hdm : d ∉ Finset.univ.image (algebraMap k K) := by simpa using H
  have := card_le_degree_of_subset_roots (p := (X ^ Fintype.card k - X : K[X]))
    (Z := insert d (Finset.univ.image (algebraMap k K))) (fun x hx => by
      rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero K hq), IsRoot, eval_sub, eval_pow,
        eval_X, sub_eq_zero]
      rcases Finset.mem_insert.1 hx with rfl | hx
      · exact hd
      · obtain ⟨c, _, rfl⟩ := Finset.mem_image.1 hx
        rw [← map_pow, FiniteField.pow_card])
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq K hq, Finset.card_insert_of_notMem hdm,
    Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ] at this
  omega

/- English proof (translation)
Establish `hq : 1 < Fintype.card k` using `Fintype.one_lt_card`. Take `⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1` from `⟨Fintype.card k - 1, by omega⟩`. Establish `hr0 : 0 < r` using `by omega`. Establish `hK : Fintype.card K = Fintype.card k ^ 2`. Rewrite using `[Module.card_eq_pow_finrank (K := k), h2]`.

Establish `hnorm : ∀ t : K, t * σ t = algebraMap k K (Algebra.norm k t)`. Introduce `t`. Rewrite using `[FiniteField.algebraMap_norm_eq_pow, hfrob, ← pow_succ', Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hK, hr, Nat.add_sub_cancel, Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = (r + 2) * r + 1 by ring), Nat.mul_div_cancel _ hr0]`. Distinguish the cases in `hd0 : d = 0`. Rewrite using `[if_pos hd0]`.

Substitute `hd0` using the available equality. Conclude with `Nat.card_eq_one_iff_exists.2 ⟨⟨0, by simp⟩, fun y => Subtype.ext (by`. Break down `mul_eq_zero.1 y.2 with h | h` into its components or cases. Conclude with `h`. Conclude with `(map_eq_zero_iff σ σ.injective).1 h)⟩`.

Rewrite using `[if_neg hd0]`. Establish `hfix : d ^ Fintype.card k = d` using `by rw [← hfrob, hd]`. Take `⟨d0, hd0e⟩` from `mem_range_of_pow d hfix`. Establish `hd00 : d0 ≠ 0` using `by rintro rfl; exact hd0 (by rw [← hd0e, map_zero])`. Set `f : Kˣ →* kˣ` to `Units.map (Algebra.norm k (S := K) : K →* k)`.

Establish `hsurj : Function.Surjective f` using `FiniteField.unitsMap_norm_surjective k K`. Establish `hall : ∀ y : kˣ, (Finset.univ.filter (fun g => f g = y)).card = (Finset.univ.filter (fun g => f g = 1)).card` using `fun y => MonoidHom.card_fiber_eq_of_mem_range f (hsurj y) (hsurj 1)`. Establish `htot` using `Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ) (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _))`. Rewrite `htot` using `[Finset.sum_congr rfl (fun y _ => hall y), Finset.sum_const, Finset.card_univ, Finset.card_univ, smul_eq_mul, Fintype.card_units, Fintype.card_units, hK, hr, Nat.add_sub_cancel, Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = (r + 2) * r + 1 by ring), mul_comm]`. Establish `hF : (Finset.univ.filter (fun g => f g = 1)).card = r + 2` using `(Nat.eq_of_mul_eq_mul_left hr0 htot).symm`.

Set `E : {t : K // t * σ t = d} ≃ {g : Kˣ // f g = Units.mk0 d0 hd00}` to `{ toFun := fun t => ⟨Units.mk0 t.1 (fun h0 => hd0 (by rw [← t.2, h0, zero_mul])), Units.ext (by`. Simplify using `only [f, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe]`. Apply `(algebraMap k K).injective` to reduce the goal to its premises. Rewrite using `[← hnorm, t.2, hd0e])⟩`. Use `invFun := fun g => ⟨g.1.1, by`.

Use `congrArg Units.val g.2` as an intermediate fact. Simplify using `only [f, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at this`. Rewrite using `[hnorm, this, hd0e]⟩`. Use `left_inv := fun t => rfl`. Use `right_inv := fun g => Subtype.ext (Units.ext rfl) }`.

Rewrite using `[Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_subtype, hall, hF, hr]`.
-/
theorem card_norm_fiber (σ : K ≃ₐ[k] K) (hfrob : ∀ x, σ x = x ^ Fintype.card k)
    (h2 : finrank k K = 2) (d : K) (hd : σ d = d) :
    Nat.card {t : K // t * σ t = d} = if d = 0 then 1 else Fintype.card k + 1 := by
  classical
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Fintype.card k = r + 1 := ⟨Fintype.card k - 1, by omega⟩
  have hr0 : 0 < r := by omega
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hnorm : ∀ t : K, t * σ t = algebraMap k K (Algebra.norm k t) := by
    intro t
    rw [FiniteField.algebraMap_norm_eq_pow, hfrob, ← pow_succ', Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, hK, hr, Nat.add_sub_cancel,
      Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = (r + 2) * r + 1 by ring),
      Nat.mul_div_cancel _ hr0]
  by_cases hd0 : d = 0
  · rw [if_pos hd0]
    subst hd0
    exact Nat.card_eq_one_iff_exists.2 ⟨⟨0, by simp⟩, fun y => Subtype.ext (by
      rcases mul_eq_zero.1 y.2 with h | h
      · exact h
      · exact (map_eq_zero_iff σ σ.injective).1 h)⟩
  rw [if_neg hd0]
  have hfix : d ^ Fintype.card k = d := by rw [← hfrob, hd]
  obtain ⟨d0, hd0e⟩ := mem_range_of_pow d hfix
  have hd00 : d0 ≠ 0 := by rintro rfl; exact hd0 (by rw [← hd0e, map_zero])
  let f : Kˣ →* kˣ := Units.map (Algebra.norm k (S := K) : K →* k)
  have hsurj : Function.Surjective f := FiniteField.unitsMap_norm_surjective k K
  have hall : ∀ y : kˣ, (Finset.univ.filter (fun g => f g = y)).card =
      (Finset.univ.filter (fun g => f g = 1)).card := fun y =>
    MonoidHom.card_fiber_eq_of_mem_range f (hsurj y) (hsurj 1)
  have htot := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ)
    (t := Finset.univ) (fun x _ => Finset.mem_coe.2 (Finset.mem_univ _))
  rw [Finset.sum_congr rfl (fun y _ => hall y), Finset.sum_const, Finset.card_univ,
    Finset.card_univ, smul_eq_mul, Fintype.card_units, Fintype.card_units, hK, hr,
    Nat.add_sub_cancel, Nat.sub_eq_of_eq_add (show (r + 1) ^ 2 = (r + 2) * r + 1 by ring),
    mul_comm] at htot
  have hF : (Finset.univ.filter (fun g => f g = 1)).card = r + 2 :=
    (Nat.eq_of_mul_eq_mul_left hr0 htot).symm
  let E : {t : K // t * σ t = d} ≃ {g : Kˣ // f g = Units.mk0 d0 hd00} :=
    { toFun := fun t => ⟨Units.mk0 t.1 (fun h0 => hd0 (by rw [← t.2, h0, zero_mul])),
        Units.ext (by
          simp only [f, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe]
          apply (algebraMap k K).injective
          rw [← hnorm, t.2, hd0e])⟩
      invFun := fun g => ⟨g.1.1, by
        have := congrArg Units.val g.2
        simp only [f, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at this
        rw [hnorm, this, hd0e]⟩
      left_inv := fun t => rfl
      right_inv := fun g => Subtype.ext (Units.ext rfl) }
  rw [Nat.card_congr E, Nat.card_eq_fintype_card, Fintype.card_subtype, hall, hF, hr]

end field

/- English proof (translation)
Introduce `k K _ _ _ _ σ hσ h2 hne h2k M a haM J hJ hdJ T hT hdT`. Use `Fintype.ofFinite k` as an intermediate fact. Establish `: Module.Finite k K` using `Module.finite_of_finrank_pos (by omega)`. Establish `: Finite K` using `Module.finite_of_finite k`. Use `Fintype.ofFinite K` as an intermediate fact.

Establish `hq1 : 1 < Fintype.card k` using `Fintype.one_lt_card`. Establish `hK : Fintype.card K = Fintype.card k ^ 2`. Rewrite using `[Module.card_eq_pow_finrank (K := k), h2]`. Establish `hfrob` using `frob_of_ne σ h2 hne`. Establish `hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x` using `fun x => hσ x`.

Establish `hN : ∀ d : K, (σ : K →+* K) d = d → Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Fintype.card k + 1` using `fun d hd => card_norm_fiber σ hfrob h2 d hd`. Establish `h2K : (2 : K) ≠ 0`. Introduce `h`. Conclude with `h2k ((algebraMap k K).injective (by rw [map_ofNat, map_zero]; exact h))`. Establish `hJs` using `ffH_isHS hσ' J hJ hdJ`.

Establish `hTs` using `ffH_isHS hσ' T hT hdT`. Take `⟨f, hf1, hf2⟩` from `exists_orth h2K a (Fin a → K) (ffH (σ : K →+* K) T) hTs (Module.finrank_fin_fun K)`. Set `b` to `basisOfLinearIndependentOfCardEqFinrank' f (linIndep_orth hTs.toIsSq f hf1 hf2) (by simp)`. Establish `e1 : Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} = Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) = ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i) (Pi.basisFun K (Fin a) j)}`. Use `Nat.card_congr (Equiv.subtypeEquivRight (fun X => ?_))` and prove the remaining obligations.

Rewrite using `[← Matrix.ext_iff]`. Simplify using `only [ffGram, Pi.basisFun_apply, ffH_single]`. Establish `e3 : Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) = ffH (σ : K →+* K) T (b i) (b j)} = Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) = if i = j then ffH (σ : K →+* K) T (f i) (f i) else 0}`. Use `Nat.card_congr (Equiv.subtypeEquivRight (fun Y => ?_))` and prove the remaining obligations. Simplify using `only [b, coe_basisOfLinearIndependentOfCardEqFinrank']`.

Use `forall_congr' (fun i => forall_congr' (fun j => ?_))` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hij, hf1 i j hij]`.

Rewrite using `[e1, ← card_isom hTs.toIsSq hJs.toIsSq (Pi.basisFun K (Fin a)), card_isom hTs.toIsSq hJs.toIsSq b, e3, card_diag (Fintype.card k) (by omega) hK hσ' h2K hN a M haM (Fin M → K) _ hJs (Module.finrank_fin_fun K) _ (fun i => hTs.toIsSq.self_fixed (f i)) hf2, Nat.card_eq_fintype_card ( …`.
-/
theorem fFInert_holds : FFInert := by
  intro k K _ _ _ _ σ hσ h2 hne h2k M a haM J hJ hdJ T hT hdT
  classical
  have := Fintype.ofFinite k
  have : Module.Finite k K := Module.finite_of_finrank_pos (by omega)
  have : Finite K := Module.finite_of_finite k
  have := Fintype.ofFinite K
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hK : Fintype.card K = Fintype.card k ^ 2 := by
    rw [Module.card_eq_pow_finrank (K := k), h2]
  have hfrob := frob_of_ne σ h2 hne
  have hσ' : ∀ x, (σ : K →+* K) ((σ : K →+* K) x) = x := fun x => hσ x
  have hN : ∀ d : K, (σ : K →+* K) d = d →
      Nat.card {t : K // t * (σ : K →+* K) t = d} = if d = 0 then 1 else Fintype.card k + 1 :=
    fun d hd => card_norm_fiber σ hfrob h2 d hd
  have h2K : (2 : K) ≠ 0 := by
    intro h
    exact h2k ((algebraMap k K).injective (by rw [map_ofNat, map_zero]; exact h))
  have hJs := ffH_isHS hσ' J hJ hdJ
  have hTs := ffH_isHS hσ' T hT hdT
  obtain ⟨f, hf1, hf2⟩ := exists_orth h2K a (Fin a → K) (ffH (σ : K →+* K) T) hTs
    (Module.finrank_fin_fun K)
  let b := basisOfLinearIndependentOfCardEqFinrank' f (linIndep_orth hTs.toIsSq f hf1 hf2)
    (by simp)
  have e1 : Nat.card {X : Fin a → Fin M → K // ffGram (σ : K →+* K) J X = T} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        ffH (σ : K →+* K) T (Pi.basisFun K (Fin a) i) (Pi.basisFun K (Fin a) j)} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun X => ?_))
    rw [← Matrix.ext_iff]
    simp only [ffGram, Pi.basisFun_apply, ffH_single]
  have e3 : Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        ffH (σ : K →+* K) T (b i) (b j)} =
      Nat.card {Y : Fin a → Fin M → K // ∀ i j, ffH (σ : K →+* K) J (Y i) (Y j) =
        if i = j then ffH (σ : K →+* K) T (f i) (f i) else 0} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight (fun Y => ?_))
    simp only [b, coe_basisOfLinearIndependentOfCardEqFinrank']
    refine forall_congr' (fun i => forall_congr' (fun j => ?_))
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg hij, hf1 i j hij]
  rw [e1, ← card_isom hTs.toIsSq hJs.toIsSq (Pi.basisFun K (Fin a)),
    card_isom hTs.toIsSq hJs.toIsSq b, e3,
    card_diag (Fintype.card k) (by omega) hK hσ' h2K hN a M haM (Fin M → K) _ hJs
      (Module.finrank_fin_fun K) _ (fun i => hTs.toIsSq.self_fixed (f i)) hf2,
    Nat.card_eq_fintype_card (α := k)]

end PI.VolStabW.FFHS
