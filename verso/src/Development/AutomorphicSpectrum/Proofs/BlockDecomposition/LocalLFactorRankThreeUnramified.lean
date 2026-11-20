import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableOnTprodCubicFactor

open Ad3 Ad3.S

noncomputable section

open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementSection (localChar)

namespace GlobalTheory.CompanionTheory.EulerThree.HalfWt

open GlobalTheory.CompanionTheory.EulerThree

/- English proof (translation)
Introduce `u hu`. Establish `h1 : μ u = 1` using `hμ hu`. Establish `h2 : κ u = 1` using `hκ hu`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mul_apply, h1, h2, one_mul]`.
-/
theorem unr_mul {v : Pl} {μ κ : (Qv v)ˣ →* ℂˣ} (hμ : IsUnramifiedChar μ)
    (hκ : IsUnramifiedChar κ) : IsUnramifiedChar (μ * κ) := by
  intro u hu
  have h1 : μ u = 1 := hμ hu
  have h2 : κ u = 1 := hκ hu
  rw [MonoidHom.mem_ker, MonoidHom.mul_apply, h1, h2, one_mul]

/- English proof (translation)
Introduce `u hu`. Establish `h1 : μ u = 1` using `hμ hu`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.inv_apply, h1, inv_one]`.
-/
theorem unr_inv {v : Pl} {μ : (Qv v)ˣ →* ℂˣ} (hμ : IsUnramifiedChar μ) :
    IsUnramifiedChar μ⁻¹ := by
  intro u hu
  have h1 : μ u = 1 := hμ hu
  rw [MonoidHom.mem_ker, MonoidHom.inv_apply, h1, inv_one]

def parA (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ℂ :=
  (((D.ν v * localChar c v) (unifUnit (Qv v)) : ℂˣ) : ℂ)

def parB (c : HeckeCharacter ℚ) (v : Pl) : ℂ :=
  ((localChar c v (unifUnit (Qv v)) : ℂˣ) : ℂ)

def parC (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ℂ :=
  ((((D.ν v)⁻¹ * localChar c v) (unifUnit (Qv v)) : ℂˣ) : ℂ)

/- English proof (translation)
The claim follows from `Circle.norm_coe _`.
-/
theorem norm_localChar (c : HeckeCharacter ℚ) (v : Pl) (x : (Qv v)ˣ) :
    ‖((localChar c v x : ℂˣ) : ℂ)‖ = 1 :=
  Circle.norm_coe _

/- English proof (translation)
Rewrite using `[parA, MonoidHom.mul_apply, Units.val_mul, norm_mul, (D.unit v).2, norm_localChar, one_mul]`.
-/
theorem norm_parA (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ‖parA D c v‖ = 1 := by
  rw [parA, MonoidHom.mul_apply, Units.val_mul, norm_mul, (D.unit v).2, norm_localChar, one_mul]

/- English proof (translation)
The claim follows from `norm_localChar c v _`.
-/
theorem norm_parB (c : HeckeCharacter ℚ) (v : Pl) : ‖parB c v‖ = 1 :=
  norm_localChar c v _

/- English proof (translation)
Rewrite using `[parC, MonoidHom.mul_apply, Units.val_mul, norm_mul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, (D.unit v).2, inv_one, norm_localChar, one_mul]`.
-/
theorem norm_parC (D : Dat) (c : HeckeCharacter ℚ) (v : Pl) : ‖parC D c v‖ = 1 := by
  rw [parC, MonoidHom.mul_apply, Units.val_mul, norm_mul, MonoidHom.inv_apply,
    Units.val_inv_eq_inv_val, norm_inv, (D.unit v).2, inv_one, norm_localChar, one_mul]

/- English proof (translation)
Take `⟨e, he⟩` from `hE.1`. Rewrite using `[← he v]`. Conclude with `(e v).2.two_le`.
-/
theorem two_le_pOf (hE : faceMap_comp_succAbove_castSucc) (v : Pl) : 2 ≤ pOf v := by
  obtain ⟨e, he⟩ := hE.1
  rw [← he v]
  exact (e v).2.two_le

/- English proof (translation)
Take `⟨e, he⟩` from `hE.1`. Introduce `v w h`. Apply `e.injective` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[he, he, h]`.
-/
theorem pOf_injective (hE : faceMap_comp_succAbove_castSucc) : Function.Injective pOf := by
  obtain ⟨e, he⟩ := hE.1
  intro v w h
  apply e.injective
  apply Subtype.ext
  rw [he, he, h]

/- English proof (translation)
Establish `hν : IsUnramifiedChar (D.ν v)` using `D.unr v (fun h => hv (hA.bad h))`. Establish `hc : IsUnramifiedChar (localChar c v)` using `hA.unr v hv`. Rewrite using `[lf3, cubicFactor, hE.2 v _ (unr_mul hν hc), hE.2 v _ hc, hE.2 v _ (unr_mul (unr_inv hν) hc)]`. Both sides reduce to the same expression.
-/
theorem local_l_factor_rank_three_unramified (hE : faceMap_comp_succAbove_castSucc) {D : Dat} {c : HeckeCharacter ℚ} {δ : Bool} {S : Finset Pl}
    (hA : admitted D c δ S) {v : Pl} (hv : v ∉ S) (s : ℂ) :
    lf3 (D.ν v) (localChar c v) s = cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) s := by
  have hν : IsUnramifiedChar (D.ν v) := D.unr v (fun h => hv (hA.bad h))
  have hc : IsUnramifiedChar (localChar c v) := hA.unr v hv
  rw [lf3, cubicFactor, hE.2 v _ (unr_mul hν hc), hE.2 v _ hc, hE.2 v _ (unr_mul (unr_inv hν) hc)]
  rfl

/- English proof (translation)
The claim follows from `multipliable_cubicFactor (p := fun v : A => pOf v) (a := fun v : A => parA D c v) (b := fun v : A => parB c v) (c := fun v : A => parC D c v) ((pOf_injective hE).comp Subtype.val_injective) (fun v => two_le_pOf hE v) (fun v => norm_parA D c v) (fun v => norm_parB c v) (fun v => n …`.
-/
theorem multipliable_sub (hE : faceMap_comp_succAbove_castSucc) (D : Dat) (c : HeckeCharacter ℚ) (A : Set Pl) {s : ℂ}
    (hs : 1 < s.re) :
    Multipliable fun v : A => cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) s :=
  multipliable_cubicFactor (p := fun v : A => pOf v) (a := fun v : A => parA D c v)
    (b := fun v : A => parB c v) (c := fun v : A => parC D c v)
    ((pOf_injective hE).comp Subtype.val_injective) (fun v => two_le_pOf hE v)
    (fun v => norm_parA D c v) (fun v => norm_parB c v) (fun v => norm_parC D c v) hs

/- English proof (translation)
Unfold `eul`. Conclude with `tprod_congr fun v => local_l_factor_rank_three_unramified hE hA (fun h => v.2 (hST h)) s`.
-/
theorem eul_eq (hE : faceMap_comp_succAbove_castSucc) {D : Dat} {c : HeckeCharacter ℚ} {δ : Bool} {S : Finset Pl}
    (hA : admitted D c δ S) {T : Finset Pl} (hST : S ⊆ T) (s : ℂ) :
    eul D c T s = ∏' v : {v : Pl // v ∉ T},
      cubicFactor (pOf v.1) (parA D c v.1) (parB c v.1) (parC D c v.1) s := by
  unfold eul
  exact tprod_congr fun v => local_l_factor_rank_three_unramified hE hA (fun h => v.2 (hST h)) s

/- English proof (translation)
Rewrite using `[norm_param_mul hp ha]`. Conclude with `Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < p)) (by linarith)`.
-/
theorem norm_lt_one {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 0 < s.re) :
    ‖a * (p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_param_mul hp ha]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < p)) (by linarith)

/- English proof (translation)
Introduce `h`. Establish `h1 : a * (p : ℂ) ^ (-s) = 1` using `(sub_eq_zero.1 h).symm`. Use `norm_lt_one hp ha hs` as an intermediate fact. Rewrite `this` using `[h1, norm_one]`. Conclude with `lt_irrefl _ this`.
-/
theorem one_sub_ne_zero {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 0 < s.re) :
    1 - a * (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : a * (p : ℂ) ^ (-s) = 1 := (sub_eq_zero.1 h).symm
  have := norm_lt_one hp ha hs
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Establish `hp0 : (p : ℂ) ≠ 0`. Establish `: p ≠ 0` using `by omega`. Conclude with `this` after adjusting the coercions. Establish `hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s` using `(differentiableAt_id.neg).const_cpow (Or.inl hp0)`. Conclude with `((differentiableAt_const _).sub ((differentiableAt_const _).mul hpow)).inv (one_sub_ne_zero hp ha hs)`.
-/
theorem differentiableAt_factor {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 0 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => (1 - a * (p : ℂ) ^ (-z))⁻¹) s := by
  have hp0 : (p : ℂ) ≠ 0 := by
    have : p ≠ 0 := by omega
    exact_mod_cast this
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (p : ℂ) ^ (-z)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hp0)
  exact ((differentiableAt_const _).sub ((differentiableAt_const _).mul hpow)).inv
    (one_sub_ne_zero hp ha hs)

/- English proof (translation)
Establish `hp1 : (1 : ℝ) < p` using `by exact_mod_cast (by omega : 1 < p)`. Establish `ht1 : (p : ℝ) ^ (-(1 / 4 : ℝ)) < 1` using `Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)`. Establish `hx : ‖a * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 / 4 : ℝ))`. Rewrite using `[norm_param_mul hp ha]`. Conclude with `Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)`.

Establish `hlow : 1 - (p : ℝ) ^ (-(1 / 4 : ℝ)) ≤ ‖1 - a * (p : ℂ) ^ (-s)‖`. Use `norm_sub_norm_le (1 : ℂ) (a * (p : ℂ) ^ (-s))` as an intermediate fact. Rewrite `this` using `[norm_one]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[norm_inv]`.

Conclude with `inv_anti₀ (by linarith) hlow`.
-/
theorem norm_factor_le {p : ℕ} (hp : 2 ≤ p) {a s : ℂ} (ha : ‖a‖ = 1) (hs : 1 / 4 ≤ s.re) :
    ‖(1 - a * (p : ℂ) ^ (-s))⁻¹‖ ≤ (1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (by omega : 1 < p)
  have ht1 : (p : ℝ) ^ (-(1 / 4 : ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by norm_num)
  have hx : ‖a * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [norm_param_mul hp ha]
    exact Real.rpow_le_rpow_of_exponent_le hp1.le (by linarith)
  have hlow : 1 - (p : ℝ) ^ (-(1 / 4 : ℝ)) ≤ ‖1 - a * (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) (a * (p : ℂ) ^ (-s))
    rw [norm_one] at this
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hlow

/- English proof (translation)
Introduce `s hs`. Establish `hs : 0 < s.re` using `hs`. Conclude with `(((differentiableAt_factor hp ha hs).mul (differentiableAt_factor hp hb hs)).mul (differentiableAt_factor hp hc hs)).differentiableWithinAt`.
-/
theorem differentiableOn_cubicFactor {p : ℕ} (hp : 2 ≤ p) {a b c : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) : DifferentiableOn ℂ (cubicFactor p a b c) (HP 0) := by
  intro s hs
  have hs : 0 < s.re := hs
  exact (((differentiableAt_factor hp ha hs).mul (differentiableAt_factor hp hb hs)).mul
    (differentiableAt_factor hp hc hs)).differentiableWithinAt

/- English proof (translation)
Establish `hA` using `norm_factor_le hp ha hs`. Establish `hB` using `norm_factor_le hp hb hs`. Establish `hC` using `norm_factor_le hp hc hs`. Establish `hK : 0 ≤ (1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹` using `(norm_nonneg _).trans hA`. Rewrite using `[cubicFactor, norm_mul, norm_mul, pow_three, ← mul_assoc]`.

Conclude with `mul_le_mul (mul_le_mul hA hB (norm_nonneg _) hK) hC (norm_nonneg _) (mul_nonneg hK hK)`.
-/
theorem norm_cubicFactor_le {p : ℕ} (hp : 2 ≤ p) {a b c s : ℂ} (ha : ‖a‖ = 1)
    (hb : ‖b‖ = 1) (hc : ‖c‖ = 1) (hs : 1 / 4 ≤ s.re) :
    ‖cubicFactor p a b c s‖ ≤ ((1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹) ^ 3 := by
  have hA := norm_factor_le hp ha hs
  have hB := norm_factor_le hp hb hs
  have hC := norm_factor_le hp hc hs
  have hK : 0 ≤ (1 - (p : ℝ) ^ (-(1 / 4 : ℝ)))⁻¹ := (norm_nonneg _).trans hA
  rw [cubicFactor, norm_mul, norm_mul, pow_three, ← mul_assoc]
  exact mul_le_mul (mul_le_mul hA hB (norm_nonneg _) hK) hC (norm_nonneg _) (mul_nonneg hK hK)

open Classical in

/- English proof (translation)
Introduce `hE D c δ S hA`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Establish `hd` using `differentiableOn_tprod_cubicFactor (p := fun v : {v : Pl // v ∉ S} => pOf v.1) (a := fun v => parA D c v.1) (b := fun v => parB c v.1) (c := fun v => parC D c v.1) ((pOf_injective hE).comp Subtype.val_injective) (fun v => two_le_pOf hE v.1) (fun v => norm_parA D c v.1) (fun v => …`. Establish `he : eul D c S = fun s => ∏' v : {v : Pl // v ∉ S}, cubicFactor (pOf v.1) (parA D c v.1) (parB c v.1) (parC D c v.1) s`.

Use function extensionality and compare the values at `(eul_eq hE hA (subset_refl S))`. Rewrite using `[he]`. Conclude with `hd s hs`. Introduce `T hST s hs set G : Pl → ℂ := fun v => cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) s with hG`. Establish `h1 : ∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s = ∏ v ∈ T \ S, G v` using `Finset.prod_congr rfl fun v hv => local_l_factor_rank_three_unramified hE hA (Finset.mem_sdiff.1 hv).2 s`.

Rewrite using `[h1, eul_eq hE hA (subset_refl S), eul_eq hE hA hST]`. Express the relevant statement in the definitionally equal form `(∏' v : ({v | v ∉ S} : Set Pl), G v) = (∏ v ∈ T \ S, G v) * ∏' v : ({v | v ∉ T} : Set Pl), G v`. Rewrite using `[tprod_subtype, tprod_subtype, ← Finset.tprod_subtype' (T \ S) G, tprod_subtype]`. Establish `m1 : Multipliable ((↑(T \ S) : Set Pl).mulIndicator G)` using `(multipliable_subtype_iff_mulIndicator).1 (multipliable_sub hE D c _ hs)`. Establish `m2 : Multipliable (({v | v ∉ T} : Set Pl).mulIndicator G)` using `(multipliable_subtype_iff_mulIndicator).1 (multipliable_sub hE D c _ hs)`.

Rewrite using `[← m1.tprod_mul m2]`. Use `tprod_congr fun v => ?_` and prove the remaining obligations. Distinguish the cases in `hS : v ∈ S`. Establish `hT : v ∈ T` using `hST hS`. Simplify using `[Set.mulIndicator_apply, hS, hT]`.

Distinguish the cases in `hT : v ∈ T`. Simplify using `[Set.mulIndicator_apply, hS, hT]`. Simplify using `[Set.mulIndicator_apply, hS, hT]`. Introduce `v hv`. Establish `he : lf3 (D.ν v) (localChar c v) = cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v)` using `funext (local_l_factor_rank_three_unramified hE hA hv)`.

Rewrite using `[he]`. Use `⟨differentiableOn_cubicFactor (two_le_pOf hE v) (norm_parA D c v) (norm_parB c v) (norm_parC D c v), _, fun s hs => norm_cubicFactor_le (two_le_pOf hE v) (norm_parA D c v) (norm_parB c v) (norm_parC D c v) hs⟩` and prove the remaining obligations.
-/
theorem adjoint_lift_twisted_euler_product : faceMap_comp_succAbove_castSucc → E3 := by
  intro hE D c δ S hA
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hd := differentiableOn_tprod_cubicFactor (p := fun v : {v : Pl // v ∉ S} => pOf v.1)
      (a := fun v => parA D c v.1) (b := fun v => parB c v.1) (c := fun v => parC D c v.1)
      ((pOf_injective hE).comp Subtype.val_injective) (fun v => two_le_pOf hE v.1)
      (fun v => norm_parA D c v.1) (fun v => norm_parB c v.1) (fun v => norm_parC D c v.1)
    have he : eul D c S = fun s => ∏' v : {v : Pl // v ∉ S},
        cubicFactor (pOf v.1) (parA D c v.1) (parB c v.1) (parC D c v.1) s :=
      funext (eul_eq hE hA (subset_refl S))
    rw [he]
    exact hd s hs
  · intro T hST s hs
    set G : Pl → ℂ := fun v => cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) s with hG
    have h1 : ∏ v ∈ T \ S, lf3 (D.ν v) (localChar c v) s = ∏ v ∈ T \ S, G v :=
      Finset.prod_congr rfl fun v hv => local_l_factor_rank_three_unramified hE hA (Finset.mem_sdiff.1 hv).2 s
    rw [h1, eul_eq hE hA (subset_refl S), eul_eq hE hA hST]
    change (∏' v : ({v | v ∉ S} : Set Pl), G v) = (∏ v ∈ T \ S, G v) * ∏' v : ({v | v ∉ T} : Set Pl), G v
    rw [tprod_subtype, tprod_subtype, ← Finset.tprod_subtype' (T \ S) G, tprod_subtype]
    have m1 : Multipliable ((↑(T \ S) : Set Pl).mulIndicator G) :=
      (multipliable_subtype_iff_mulIndicator).1 (multipliable_sub hE D c _ hs)
    have m2 : Multipliable (({v | v ∉ T} : Set Pl).mulIndicator G) :=
      (multipliable_subtype_iff_mulIndicator).1 (multipliable_sub hE D c _ hs)
    rw [← m1.tprod_mul m2]
    refine tprod_congr fun v => ?_
    by_cases hS : v ∈ S
    · have hT : v ∈ T := hST hS
      simp [Set.mulIndicator_apply, hS, hT]
    · by_cases hT : v ∈ T
      · simp [Set.mulIndicator_apply, hS, hT]
      · simp [Set.mulIndicator_apply, hS, hT]
  · intro v hv
    have he : lf3 (D.ν v) (localChar c v) =
        cubicFactor (pOf v) (parA D c v) (parB c v) (parC D c v) := funext (local_l_factor_rank_three_unramified hE hA hv)
    rw [he]
    refine ⟨differentiableOn_cubicFactor (two_le_pOf hE v) (norm_parA D c v) (norm_parB c v)
      (norm_parC D c v), _, fun s hs => norm_cubicFactor_le (two_le_pOf hE v) (norm_parA D c v)
      (norm_parB c v) (norm_parC D c v) hs⟩

end GlobalTheory.CompanionTheory.EulerThree.HalfWt
