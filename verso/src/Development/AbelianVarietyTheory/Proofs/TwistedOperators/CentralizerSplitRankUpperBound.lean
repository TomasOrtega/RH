import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent
open GlobalTheory.RegSS

noncomputable section
open Matrix Formalism.UG GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS.SplitRankBound

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, _root_.zpow_add, ih]`.
-/
theorem zpow_sum_eq {M : Type} [CommGroup M] (a : M) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, _root_.zpow_add, ih]

/- English proof (translation)
Establish `h2 : ((2:ℚ) ^ m : ℚ) = (2:ℚ) ^ (0:ℤ)`. Rewrite using `[zpow_zero]`. Apply `(algebraMap ℚ F).injective` to reduce the goal to its premises. Rewrite using `[map_zpow₀, map_ofNat, h, map_one]`. Conclude with `(zpow_right_strictMono₀ one_lt_two).injective h2`.
-/
theorem two_zpow_eq_one {F : Type} [Field F] [CharZero F] {m : ℤ} (h : (2:F) ^ m = 1) : m = 0 := by
  have h2 : ((2:ℚ) ^ m : ℚ) = (2:ℚ) ^ (0:ℤ) := by
    rw [zpow_zero]
    apply (algebraMap ℚ F).injective
    rw [map_zpow₀, map_ofNat, h, map_one]
  exact (zpow_right_strictMono₀ one_lt_two).injective h2

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `F E _ _ _ _ n _ _ σ J γ hR hPl hPC k K _ _ he s hA`. Take `⟨A⟩` from `hA`. Use `haveI : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) := Module.Finite.of_basis hPl.2.1.some`. Take `⟨ψ, hsep, hfield⟩` from `hP F E σ hR.quad (plusAlg σ J (γ : Matrix n n E)) k K he`. Establish `hinj` using `(hPC F).1`.

Establish `hcent` using `(hPC F).2.2`. Take `⟨ρ, hρ⟩` from `LinearMap.exists_leftInverse_of_injective (toMat σ J (γ : Matrix n n E) F).toLinearMap (LinearMap.ker_eq_bot.2 hinj)`. Establish `hρT : ∀ x, ρ (toMat σ J (γ : Matrix n n E) F x) = x` using `fun x => LinearMap.congr_fun hρ x`. Establish `hex : ∀ t : Fin s → Fˣ, ∃ u ∈ normOne σ J (γ : Matrix n n E) F, toMat σ J (γ : Matrix n n E) F (u : LPts σ J (γ : Matrix n n E) F) = ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))` using `fun t => (hcent _).1 (A.mem F t)`. Establish `hTu : ∀ t : Fin s → Fˣ, toMat σ J (γ : Matrix n n E) F (ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))) = ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))`.

Introduce `t`. Take `⟨u, -, hu⟩` from `hex t`. Rewrite using `[← hu, hρT]`. Establish `hnorm : ∀ t : Fin s → Fˣ, ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) * lConj σ J (γ : Matrix n n E) F (ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))) = 1`. Introduce `t`.

Take `⟨u, hu, hu'⟩` from `hex t`. Rewrite using `[← hu', hρT]`. Conclude with `hu`. Set `uu : (Fin s → Fˣ) →* LPts σ J (γ : Matrix n n E) F` to `{ toFun := fun t => ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) map_one' := hinj (by rw [hTu, map_one, Units.val_one, map_one]) map_mul' := fun a b => hinj (by`. Rewrite using `[map_mul (toMat σ J (γ : Matrix n n E) F), hTu a, hTu b, ← Units.val_mul, ← map_mul, hTu]) }`.

Establish `huu : ∀ t, uu t = ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))` using `fun _ => rfl`. Use `clear_value uu`. Take `⟨S, C, hC⟩` from `hL F E n σ J γ s A`. Establish `hmono : ∀ i, ∃ a : Fin s → ℤ, ∀ t : Fin s → Fˣ, ψ i (uu t) = algebraMap F (AlgebraicClosure F) ((∏ j, t j ^ a j : Fˣ) : F)`. Introduce `i`.

Use `hM F (AlgebraicClosure F) s ((ψ i : _ →+* AlgebraicClosure F).toMonoidHom.comp uu) S (fun a => ψ i (ρ (C a))) (fun t => ?_)` and prove the remaining obligations. Simplify using `only [MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, RingHom.coe_coe, huu, hC t, map_sum, map_smul]`. Use `choose a ha using hmono`. Establish `hconj : ∀ i t, ψ i (uu t) * ψ i (lConj σ J (γ : Matrix n n E) F (uu t)) = 1`. Introduce `i t`.

Rewrite using `[← map_mul, huu, hnorm, map_one]`. Establish `hlc : tConj3 (plusAlg σ J (γ : Matrix n n E)) σ F = lConj σ J (γ : Matrix n n E) F` using `rfl`. Establish `hsq : ∀ i, IsField (K i ⊗[F] E) → ∀ t : Fin s → Fˣ, ((∏ j, t j ^ a i j : Fˣ) : F) * ((∏ j, t j ^ a i j : Fˣ) : F) = 1`. Introduce `i hi t`. Establish `h0 : ψ i (uu t - algebraMap F _ ((∏ j, t j ^ a i j : Fˣ) : F)) = 0`.

Rewrite using `[map_sub, AlgHom.commutes, ha, sub_self]`. Establish `h1` using `hfield i hi _ h0`. Rewrite `h1` using `[hlc, map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero]`. Establish `h2` using `hconj i t`. Rewrite `h2` using `[ha, h1, ← map_mul]`.

Conclude with `(algebraMap F (AlgebraicClosure F)).injective (h2.trans (map_one _).symm)`. Set `M : Matrix {i : Fin k // ¬ IsField (K i ⊗[F] E)} (Fin s) ℤ` to `Matrix.of fun i j => a i.1 j`. Establish `hfinj : Function.Injective M.mulVecLin`. Use `(injective_iff_map_eq_zero M.mulVecLin).2 fun w hw => ?_` and prove the remaining obligations. Establish `hw' : ∀ i : {i : Fin k // ¬ IsField (K i ⊗[F] E)}, ∑ j, a i.1 j * w j = 0`.

Introduce `i`. Use `congrFun hw i` as an intermediate fact. Simplify `this` using `[M, Matrix.mulVec, dotProduct]`. Set `u2 : Fˣ` to `Units.mk0 2 two_ne_zero`. Set `t : Fin s → Fˣ` to `fun j => u2 ^ w j`.

Establish `hprod : ∀ i, ((∏ j, t j ^ a i j : Fˣ) : F) = (2:F) ^ (∑ j, a i j * w j)`. Introduce `i`. Establish `: (∏ j, t j ^ a i j : Fˣ) = u2 ^ (∑ j, a i j * w j)`. Rewrite using `[zpow_sum_eq]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [t]`. Rewrite using `[← _root_.zpow_mul, mul_comm]`. Rewrite using `[this, Units.val_zpow_eq_zpow_val, Units.val_mk0]`. Establish `hone : ∀ i, ((∏ j, t j ^ a i j : Fˣ) : F) = 1`. Introduce `i`.

Distinguish the cases in `hi : IsField (K i ⊗[F] E)`. Establish `h` using `hsq i hi t`. Rewrite `h` using `[hprod, ← zpow_add₀ (two_ne_zero)]`. Establish `h0` using `two_zpow_eq_one h`. Rewrite using `[hprod, show ∑ j, a i j * w j = 0 by omega, zpow_zero]`.

Rewrite using `[hprod, hw' ⟨i, hi⟩, zpow_zero]`. Establish `hψ1 : ∀ i, ψ i (uu t) = 1` using `fun i => by rw [ha, hone, map_one]`. Establish `hψc : ∀ i, ψ i (lConj σ J (γ : Matrix n n E) F (uu t)) = 1` using `fun i => by`. Establish `h` using `hconj i t`. Rewrite `h` using `[hψ1, one_mul]`. Then use the resulting hypothesis.

Establish `hut : uu t = 1`. Use `hsep (uu t - 1) fun i => ⟨by rw [map_sub, hψ1, map_one, sub_self], by rw [hlc, map_sub, map_sub, hψc, map_one, map_one, sub_self]⟩` as an intermediate fact. Rewrite `this` using `[sub_eq_zero]`. Then use the resulting hypothesis. Establish `hhom : A.hom F t = A.hom F 1`. Use `Units.ext ?_` and prove the remaining obligations.

Rewrite using `[(A.hom F).map_one, Units.val_one, ← hTu t, ← huu, hut, map_one]`. Establish `ht1 : t = 1` using `A.inj F hhom`. Use function extensionality and compare the values at `j`. Establish `hj` using `congrFun ht1 j`. Establish `hj' : ((u2 ^ w j : Fˣ) : F) = 1`.

Use `congrArg Units.val hj` as an intermediate fact. Simplify `this` using `[t]`. Rewrite `hj'` using `[Units.val_zpow_eq_zpow_val, Units.val_mk0]`. Conclude with `two_zpow_eq_one hj'`. Establish `hle` using `LinearMap.finrank_le_finrank_of_injective hfinj`.

Rewrite `hle` using `[Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `hle`.
-/
theorem splitRankUpper (hL : SubtorusLaurent) (hM : CharacterMonomial) (hP : SeparatingPoints) :
    SplitRankUpper := by
  intro F E _ _ _ _ n _ _ σ J γ hR hPl hPC k K _ _ he s hA
  classical
  obtain ⟨A⟩ := hA
  haveI : Module.Finite F (plusAlg σ J (γ : Matrix n n E)) := Module.Finite.of_basis hPl.2.1.some
  obtain ⟨ψ, hsep, hfield⟩ := hP F E σ hR.quad (plusAlg σ J (γ : Matrix n n E)) k K he
  have hinj := (hPC F).1
  have hcent := (hPC F).2.2
  obtain ⟨ρ, hρ⟩ := LinearMap.exists_leftInverse_of_injective
    (toMat σ J (γ : Matrix n n E) F).toLinearMap (LinearMap.ker_eq_bot.2 hinj)
  have hρT : ∀ x, ρ (toMat σ J (γ : Matrix n n E) F x) = x := fun x => LinearMap.congr_fun hρ x
  have hex : ∀ t : Fin s → Fˣ, ∃ u ∈ normOne σ J (γ : Matrix n n E) F,
      toMat σ J (γ : Matrix n n E) F (u : LPts σ J (γ : Matrix n n E) F) =
        ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) :=
    fun t => (hcent _).1 (A.mem F t)
  have hTu : ∀ t : Fin s → Fˣ, toMat σ J (γ : Matrix n n E) F
      (ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))) =
        ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) := by
    intro t; obtain ⟨u, -, hu⟩ := hex t; rw [← hu, hρT]
  have hnorm : ∀ t : Fin s → Fˣ,
      ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) *
        lConj σ J (γ : Matrix n n E) F (ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)))
          = 1 := by
    intro t; obtain ⟨u, hu, hu'⟩ := hex t; rw [← hu', hρT]; exact hu
  let uu : (Fin s → Fˣ) →* LPts σ J (γ : Matrix n n E) F :=
    { toFun := fun t => ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F))
      map_one' := hinj (by rw [hTu, map_one, Units.val_one, map_one])
      map_mul' := fun a b => hinj (by
        rw [map_mul (toMat σ J (γ : Matrix n n E) F), hTu a, hTu b, ← Units.val_mul, ← map_mul, hTu]) }
  have huu : ∀ t, uu t = ρ ((A.hom F t : GL n (E ⊗[F] F)) : Matrix n n (E ⊗[F] F)) := fun _ => rfl
  clear_value uu
  obtain ⟨S, C, hC⟩ := hL F E n σ J γ s A
  have hmono : ∀ i, ∃ a : Fin s → ℤ, ∀ t : Fin s → Fˣ,
      ψ i (uu t) = algebraMap F (AlgebraicClosure F) ((∏ j, t j ^ a j : Fˣ) : F) := by
    intro i
    refine hM F (AlgebraicClosure F) s ((ψ i : _ →+* AlgebraicClosure F).toMonoidHom.comp uu) S
      (fun a => ψ i (ρ (C a))) (fun t => ?_)
    simp only [MonoidHom.coe_comp, Function.comp_apply, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_coe, RingHom.coe_coe, huu, hC t, map_sum, map_smul]
  choose a ha using hmono
  have hconj : ∀ i t, ψ i (uu t) * ψ i (lConj σ J (γ : Matrix n n E) F (uu t)) = 1 := by
    intro i t; rw [← map_mul, huu, hnorm, map_one]
  have hlc : tConj3 (plusAlg σ J (γ : Matrix n n E)) σ F = lConj σ J (γ : Matrix n n E) F := rfl
  have hsq : ∀ i, IsField (K i ⊗[F] E) → ∀ t : Fin s → Fˣ,
      ((∏ j, t j ^ a i j : Fˣ) : F) * ((∏ j, t j ^ a i j : Fˣ) : F) = 1 := by
    intro i hi t
    have h0 : ψ i (uu t - algebraMap F _ ((∏ j, t j ^ a i j : Fˣ) : F)) = 0 := by
      rw [map_sub, AlgHom.commutes, ha, sub_self]
    have h1 := hfield i hi _ h0
    rw [hlc, map_sub, AlgHom.commutes, map_sub, AlgHom.commutes, sub_eq_zero] at h1
    have h2 := hconj i t
    rw [ha, h1, ← map_mul] at h2
    exact (algebraMap F (AlgebraicClosure F)).injective (h2.trans (map_one _).symm)
  let M : Matrix {i : Fin k // ¬ IsField (K i ⊗[F] E)} (Fin s) ℤ := Matrix.of fun i j => a i.1 j
  have hfinj : Function.Injective M.mulVecLin := by
    refine (injective_iff_map_eq_zero M.mulVecLin).2 fun w hw => ?_
    have hw' : ∀ i : {i : Fin k // ¬ IsField (K i ⊗[F] E)}, ∑ j, a i.1 j * w j = 0 := by
      intro i
      have := congrFun hw i
      simpa [M, Matrix.mulVec, dotProduct] using this
    let u2 : Fˣ := Units.mk0 2 two_ne_zero
    let t : Fin s → Fˣ := fun j => u2 ^ w j
    have hprod : ∀ i, ((∏ j, t j ^ a i j : Fˣ) : F) = (2:F) ^ (∑ j, a i j * w j) := by
      intro i
      have : (∏ j, t j ^ a i j : Fˣ) = u2 ^ (∑ j, a i j * w j) := by
        rw [zpow_sum_eq]
        refine Finset.prod_congr rfl fun j _ => ?_
        simp only [t]
        rw [← _root_.zpow_mul, mul_comm]
      rw [this, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    have hone : ∀ i, ((∏ j, t j ^ a i j : Fˣ) : F) = 1 := by
      intro i
      by_cases hi : IsField (K i ⊗[F] E)
      · have h := hsq i hi t
        rw [hprod, ← zpow_add₀ (two_ne_zero)] at h
        have h0 := two_zpow_eq_one h
        rw [hprod, show ∑ j, a i j * w j = 0 by omega, zpow_zero]
      · rw [hprod, hw' ⟨i, hi⟩, zpow_zero]
    have hψ1 : ∀ i, ψ i (uu t) = 1 := fun i => by rw [ha, hone, map_one]
    have hψc : ∀ i, ψ i (lConj σ J (γ : Matrix n n E) F (uu t)) = 1 := fun i => by
      have h := hconj i t; rwa [hψ1, one_mul] at h
    have hut : uu t = 1 := by
      have := hsep (uu t - 1) fun i => ⟨by rw [map_sub, hψ1, map_one, sub_self],
        by rw [hlc, map_sub, map_sub, hψc, map_one, map_one, sub_self]⟩
      rwa [sub_eq_zero] at this
    have hhom : A.hom F t = A.hom F 1 := by
      refine Units.ext ?_
      rw [(A.hom F).map_one, Units.val_one, ← hTu t, ← huu, hut,
        map_one]
    have ht1 : t = 1 := A.inj F hhom
    funext j
    have hj := congrFun ht1 j
    have hj' : ((u2 ^ w j : Fˣ) : F) = 1 := by
      have := congrArg Units.val hj
      simpa [t] using this
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0] at hj'
    exact two_zpow_eq_one hj'
  have hle := LinearMap.finrank_le_finrank_of_injective hfinj
  rw [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at hle
  rw [Nat.card_eq_fintype_card]
  exact hle

end GlobalTheory.RegSS.SplitRankBound
