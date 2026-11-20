import Mathlib

open Polynomial IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `p hn hp hpv`. Distinguish the cases in `hq : p.map (evalRingHom a) = 0`.

Establish `hdvd : C (X - C a) ∣ p`. Rewrite using `[C_dvd_iff_dvd_coeff]`. Introduce `i`. Rewrite using `[dvd_iff_isRoot]`. Use `congrArg (fun q => q.coeff i) hq` as an intermediate fact.

Simplify `this` using `[coeff_map]`. Take `⟨p', rfl⟩` from `hdvd`. Establish `hp' : p' ≠ 0` using `by rintro rfl; simp at hp`. Establish `hXa : (X - C a : Polynomial K) ≠ 0` using `X_sub_C_ne_zero a`. Use `ih p'.leadingCoeff.natDegree ?_ p' rfl hp' ?_` and prove the remaining obligations.

Rewrite using `[← hn, leadingCoeff_mul, leadingCoeff_C, natDegree_mul hXa (leadingCoeff_ne_zero.mpr hp'), natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Rewrite `hpv` using `[eval₂_mul, eval₂_C]`. Establish `h2 : (eval₂RingHom ιV sV) (X - C a) = sV - ιV a` using `by simp`. Rewrite `hpv` using `[h2]`.

Conclude with `(mul_eq_zero.mp hpv).resolve_left hne`. Use `⟨_, hq, ?_⟩` and prove the remaining obligations. Establish `h1 : (residue V).comp (eval₂RingHom ιV sV) = ((residue V).comp ιV).comp (evalRingHom a)`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`.

Simplify using the standard rewrite rules. Establish `: residue V sV = residue V (ιV a)`. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`. Conclude with `hsa`. Simplify using `using this`.

Rewrite using `[eval₂_map, ← h1, ← hom_eval₂, hpv, map_zero]`.
-/
theorem genval_descent {K : Type} [Field K] {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ιV : K →+* V) (sV v : V) (a : K) (hsa : sV - ιV a ∈ maximalIdeal V) (hne : sV - ιV a ≠ 0) :
    ∀ n : ℕ, ∀ p : Polynomial (Polynomial K), p.leadingCoeff.natDegree = n → p ≠ 0 →
      p.eval₂ (eval₂RingHom ιV sV) v = 0 →
      ∃ q : Polynomial K, q ≠ 0 ∧ q.eval₂ ((residue V).comp ιV) (residue V v) = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro p hn hp hpv
  by_cases hq : p.map (evalRingHom a) = 0
  · have hdvd : C (X - C a) ∣ p := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      rw [dvd_iff_isRoot]
      have := congrArg (fun q => q.coeff i) hq
      simpa [coeff_map] using this
    obtain ⟨p', rfl⟩ := hdvd
    have hp' : p' ≠ 0 := by rintro rfl; simp at hp
    have hXa : (X - C a : Polynomial K) ≠ 0 := X_sub_C_ne_zero a
    refine ih p'.leadingCoeff.natDegree ?_ p' rfl hp' ?_
    · rw [← hn, leadingCoeff_mul, leadingCoeff_C,
        natDegree_mul hXa (leadingCoeff_ne_zero.mpr hp'), natDegree_X_sub_C]
      omega
    · rw [eval₂_mul, eval₂_C] at hpv
      have h2 : (eval₂RingHom ιV sV) (X - C a) = sV - ιV a := by simp
      rw [h2] at hpv
      exact (mul_eq_zero.mp hpv).resolve_left hne
  · refine ⟨_, hq, ?_⟩
    have h1 : (residue V).comp (eval₂RingHom ιV sV) =
        ((residue V).comp ιV).comp (evalRingHom a) := by
      apply Polynomial.ringHom_ext
      · intro c; simp
      · have : residue V sV = residue V (ιV a) := by
          rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsa
        simpa using this
    rw [eval₂_map, ← h1, ← hom_eval₂, hpv, map_zero]

/- English proof (translation)
Apply `IsAlgClosed.ringHom_bijective_of_isIntegral` to reduce the goal to its premises. Introduce `x`. Take `⟨v, rfl⟩` from `residue_surjective x`. Take `⟨p, hp, hpv⟩` from `halg v`. Take `⟨q, hq, hqv⟩` from `genval_descent ιV sV v a hsa hne _ p rfl hp hpv`.

Use `⟨q * C (q.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq, ?_⟩` and prove the remaining obligations. Rewrite using `[eval₂_mul, hqv, zero_mul]`.
-/
theorem genval_residue_bij {K : Type} [Field K] [IsAlgClosed K] {L : Type} [Field L]
    (V : ValuationSubring L) (ιV : K →+* V) (sV : V) (a : K)
    (hsa : sV - ιV a ∈ maximalIdeal V) (hne : sV - ιV a ≠ 0)
    (halg : ∀ v : V, ∃ p : Polynomial (Polynomial K), p ≠ 0 ∧
      p.eval₂ (eval₂RingHom ιV sV) v = 0) :
    Function.Bijective ((residue V).comp ιV) := by
  apply IsAlgClosed.ringHom_bijective_of_isIntegral
  intro x
  obtain ⟨v, rfl⟩ := residue_surjective x
  obtain ⟨p, hp, hpv⟩ := halg v
  obtain ⟨q, hq, hqv⟩ := genval_descent ιV sV v a hsa hne _ p rfl hp hpv
  refine ⟨q * C (q.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq, ?_⟩
  rw [eval₂_mul, hqv, zero_mul]

/- English proof (translation)
Set `L` to `AlgebraicClosure (RatFunc K)`. Set `φ0 : Polynomial K →+* L` to `algebraMap (Polynomial K) L`. Establish `hφ0 : Function.Injective φ0`. Establish `: φ0 = (algebraMap (RatFunc K) L).comp (algebraMap (Polynomial K) (RatFunc K))` using `IsScalarTower.algebraMap_eq _ _ _`. Rewrite using `[this]`.

Conclude with `(algebraMap (RatFunc K) L).injective.comp (IsFractionRing.injective _ _)`. Set `ι : K →+* L` to `φ0.comp C`. Set `s : L` to `φ0 X`. Establish `hev : ∀ P : Polynomial K, P.eval₂ ι s = φ0 P`. Introduce `P`.

Establish `: eval₂RingHom ι s = φ0` using `Polynomial.ringHom_ext (fun c => by simp [ι]) (by simp [s])`. Conclude with `congrArg (fun f => f P) this`. Use `⟨L, inferInstance, inferInstance, ι, s, ?_, ?_⟩` and prove the remaining obligations. Introduce `P hP`. Rewrite `hP` using `[hev]`.

Conclude with `hφ0 (by rw [hP, map_zero])`. Introduce `a`. Set `e : Polynomial K ≃+* φ0.range` to `RingEquiv.ofBijective φ0.rangeRestrict ⟨fun x y h => hφ0 (congrArg Subtype.val h), φ0.rangeRestrict_surjective⟩`. Set `ψ : φ0.range →+* K` to `(evalRingHom a).comp e.symm.toRingHom`. Take `⟨V, hAV, hI⟩` from `Ideal.image_subset_nonunits_valuationSubring (RingHom.ker ψ) (RingHom.ker_ne_top ψ)`.

Establish `hmemA : ∀ P, φ0 P ∈ V` using `fun P => hAV ⟨P, rfl⟩`. Set `ιV : K →+* V` to `ι.codRestrict V (fun c => hmemA (C c))`. Set `sV : V` to `⟨s, hmemA X⟩`. Establish `hsaL : s - ι a ∈ V.nonunits`. Apply `hI` to reduce the goal to its premises.

Use `⟨φ0.rangeRestrict (X - C a), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Establish `: e.symm (φ0.rangeRestrict (X - C a)) = X - C a` using `e.symm_apply_apply (X - C a)`. Use `show evalRingHom a (e.symm (φ0.rangeRestrict (X - C a))) = 0`. Rewrite using `[this]`.

Simplify using the standard rewrite rules. Simplify using `[ι, s]`. Establish `hsa : sV - ιV a ∈ maximalIdeal V`. Establish `hsaL' : s - ι a ∈ ((↑) : V → L) '' (maximalIdeal V : Set V)`. Rewrite using `[ValuationSubring.image_maximalIdeal]`.

Conclude with `hsaL`. Take `⟨w, hw, hw'⟩` from `hsaL'`. Use `hw` and compare the differences between its conclusion and the goal. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hw']`.

Both sides reduce to the same expression. Establish `hne : sV - ιV a ≠ 0`. Introduce `h`. Establish `h1` using `congrArg Subtype.val h`. Establish `h2 : φ0 (X - C a) = 0` using `by simpa [ι, s, sV, ιV] using h1`.

Conclude with `X_sub_C_ne_zero a (hφ0 (by rw [h2, map_zero]))`. Establish `hcomp : (algebraMap V L).comp (eval₂RingHom ιV sV) = φ0` using `Polynomial.ringHom_ext (fun c => by rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]; rfl) (by rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]; rfl)`. Establish `halg : ∀ v : V, ∃ p : Polynomial (Polynomial K), p ≠ 0 ∧ p.eval₂ (eval₂RingHom ιV sV) v = 0`. Introduce `v`. Establish `h1 : IsAlgebraic (Polynomial K) (v : L)` using `(IsFractionRing.isAlgebraic_iff (Polynomial K) (RatFunc K) L).mpr (Algebra.IsAlgebraic.isAlgebraic _)`.

Take `⟨p, hp, hpv⟩` from `h1`. Use `⟨p, hp, ?_⟩` and prove the remaining obligations. Apply `IsFractionRing.injective V L` to reduce the goal to its premises. Rewrite using `[hom_eval₂, hcomp, map_zero]`. Conclude with `hpv`.

Establish `hbij` using `genval_residue_bij V ιV sV a hsa hne halg`. Set `E` to `RingEquiv.ofBijective _ hbij`. Establish `hres : residue V sV = E a` using `by show residue V sV = residue V (ιV a)`. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`. Conclude with `hsa`.

Use `⟨V, ιV, E.symm.toRingHom.comp (residue V), sV, ?_, ?_, ?_, rfl, ?_⟩` and prove the remaining obligations. Conclude with `RingHom.ext fun c => rfl`. Use extensionality with `c`. Conclude with `E.symm_apply_apply c`. Use extensionality with `x`.

Rewrite using `[RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, map_eq_zero_iff _ E.symm.injective, residue_eq_zero_iff]`. Use `show E.symm (residue V sV) = a`. Rewrite using `[hres, E.symm_apply_apply]`.
-/
theorem genval (K : Type) [Field K] [IsAlgClosed K] : ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) ∧ ∀ a : K, ∃ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K) (sV : V), (algebraMap V L).comp ιV = ι ∧ r.comp ιV = RingHom.id K ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ algebraMap V L sV = s ∧ r sV = a := by
  let L := AlgebraicClosure (RatFunc K)
  let φ0 : Polynomial K →+* L := algebraMap (Polynomial K) L
  have hφ0 : Function.Injective φ0 := by
    have : φ0 = (algebraMap (RatFunc K) L).comp (algebraMap (Polynomial K) (RatFunc K)) :=
      IsScalarTower.algebraMap_eq _ _ _
    rw [this]
    exact (algebraMap (RatFunc K) L).injective.comp (IsFractionRing.injective _ _)
  let ι : K →+* L := φ0.comp C
  let s : L := φ0 X
  have hev : ∀ P : Polynomial K, P.eval₂ ι s = φ0 P := by
    intro P
    have : eval₂RingHom ι s = φ0 := Polynomial.ringHom_ext (fun c => by simp [ι]) (by simp [s])
    exact congrArg (fun f => f P) this
  refine ⟨L, inferInstance, inferInstance, ι, s, ?_, ?_⟩
  · intro P hP
    rw [hev] at hP
    exact hφ0 (by rw [hP, map_zero])
  · intro a
    let e : Polynomial K ≃+* φ0.range := RingEquiv.ofBijective φ0.rangeRestrict
      ⟨fun x y h => hφ0 (congrArg Subtype.val h), φ0.rangeRestrict_surjective⟩
    let ψ : φ0.range →+* K := (evalRingHom a).comp e.symm.toRingHom
    obtain ⟨V, hAV, hI⟩ :=
      Ideal.image_subset_nonunits_valuationSubring (RingHom.ker ψ) (RingHom.ker_ne_top ψ)
    have hmemA : ∀ P, φ0 P ∈ V := fun P => hAV ⟨P, rfl⟩
    let ιV : K →+* V := ι.codRestrict V (fun c => hmemA (C c))
    let sV : V := ⟨s, hmemA X⟩
    have hsaL : s - ι a ∈ V.nonunits := by
      apply hI
      refine ⟨φ0.rangeRestrict (X - C a), ?_, ?_⟩
      · rw [SetLike.mem_coe, RingHom.mem_ker]
        have : e.symm (φ0.rangeRestrict (X - C a)) = X - C a :=
          e.symm_apply_apply (X - C a)
        show evalRingHom a (e.symm (φ0.rangeRestrict (X - C a))) = 0
        rw [this]
        simp
      · simp [ι, s]
    have hsa : sV - ιV a ∈ maximalIdeal V := by
      have hsaL' : s - ι a ∈ ((↑) : V → L) '' (maximalIdeal V : Set V) := by
        rw [ValuationSubring.image_maximalIdeal]; exact hsaL
      obtain ⟨w, hw, hw'⟩ := hsaL'
      convert hw
      apply Subtype.ext
      rw [hw']
      rfl
    have hne : sV - ιV a ≠ 0 := by
      intro h
      have h1 := congrArg Subtype.val h
      have h2 : φ0 (X - C a) = 0 := by simpa [ι, s, sV, ιV] using h1
      exact X_sub_C_ne_zero a (hφ0 (by rw [h2, map_zero]))
    have hcomp : (algebraMap V L).comp (eval₂RingHom ιV sV) = φ0 :=
      Polynomial.ringHom_ext (fun c => by rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]; rfl)
        (by rw [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X]; rfl)
    have halg : ∀ v : V, ∃ p : Polynomial (Polynomial K), p ≠ 0 ∧
        p.eval₂ (eval₂RingHom ιV sV) v = 0 := by
      intro v
      have h1 : IsAlgebraic (Polynomial K) (v : L) :=
        (IsFractionRing.isAlgebraic_iff (Polynomial K) (RatFunc K) L).mpr
          (Algebra.IsAlgebraic.isAlgebraic _)
      obtain ⟨p, hp, hpv⟩ := h1
      refine ⟨p, hp, ?_⟩
      apply IsFractionRing.injective V L
      rw [hom_eval₂, hcomp, map_zero]
      exact hpv
    have hbij := genval_residue_bij V ιV sV a hsa hne halg
    let E := RingEquiv.ofBijective _ hbij
    have hres : residue V sV = E a := by
      show residue V sV = residue V (ιV a)
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hsa
    refine ⟨V, ιV, E.symm.toRingHom.comp (residue V), sV, ?_, ?_, ?_, rfl, ?_⟩
    · exact RingHom.ext fun c => rfl
    · ext c
      exact E.symm_apply_apply c
    · ext x
      rw [RingHom.mem_ker, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        map_eq_zero_iff _ E.symm.injective, residue_eq_zero_iff]
    · show E.symm (residue V sV) = a
      rw [hres, E.symm_apply_apply]

end GlobalTheory
