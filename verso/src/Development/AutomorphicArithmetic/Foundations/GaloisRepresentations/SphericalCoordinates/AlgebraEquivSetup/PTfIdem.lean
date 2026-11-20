import Mathlib
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeActMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq

open Formalism.UG GlobalTheory.LKDef.HeckeTraceForms UpperTheory.Gal.W2.Seed
open scoped Classical

namespace UpperTheory.Gal.W2.Seed.TypeIdempotent

variable {X M : Type} [Group X] [Group M]

/- English proof (translation)
Establish `e : (⟨T.L.pr k⁻¹, T.fact.2 _ hk'⟩ : T.J) = (⟨T.L.pr k, T.fact.2 k hk⟩ : T.J)⁻¹`. Use `ext`. Simplify using the standard rewrite rules. Rewrite using `[e, map_inv, inv_inv]`.
-/
private theorem psi_inv (T : TyLev X M) (k : X) (hk : k ∈ T.K) (hk' : k⁻¹ ∈ T.K) :
    (((T.ψ ⟨T.L.pr k⁻¹, T.fact.2 _ hk'⟩)⁻¹ : ℂˣ) : ℂ) = ((T.ψ ⟨T.L.pr k, T.fact.2 k hk⟩ : ℂˣ) : ℂ) := by
  have e : (⟨T.L.pr k⁻¹, T.fact.2 _ hk'⟩ : T.J) = (⟨T.L.pr k, T.fact.2 k hk⟩ : T.J)⁻¹ := by
    ext
    simp
  rw [e, map_inv, inv_inv]

/- English proof (translation)
Establish `hk : (c : X) ∈ T.K` using `T.le c.2`. Rewrite using `[((hA X M T h hh).2 c hk y).2, T.ker c c.2]`. Simplify using the standard rewrite rules.
-/
private theorem tf_right (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) (y : X) (c : T.K₀) :
    T.tf h (y * c) = T.tf h y := by
  have hk : (c : X) ∈ T.K := T.le c.2
  rw [((hA X M T h hh).2 c hk y).2, T.ker c c.2]
  simp

/- English proof (translation)
Establish `hk : (c : X) ∈ T.K` using `T.le c.2`. Rewrite using `[((hA X M T h hh).2 c hk y).1, T.ker c c.2]`. Simplify using the standard rewrite rules.
-/
private theorem tf_left (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) (y : X) (c : T.K₀) :
    T.tf h ((c : X) * y) = T.tf h y := by
  have hk : (c : X) ∈ T.K := T.le c.2
  rw [((hA X M T h hh).2 c hk y).1, T.ker c c.2]
  simp

/- English proof (translation)
Introduce `k hk g`. Establish `hF : ∀ (y : X) (c : T.K₀), (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) (y * c) = (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) y`. Introduce `y c`. Simplify using `only`. Rewrite using `[← mul_assoc, tf_right hA T h hh _ c, ← mul_assoc, hΦ c c.2]`.

Establish `hs` using `P.finsum_out_mul T.K₀ k (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) hF`. Simplify using `only [inv_mul_cancel_left] at hs`. Simplify using `only [hAct, mul_assoc]`. Rewrite using `[hs, smul_finsum]`. Use `congr 1`.

Use function extensionality and compare the values at `x`. Rewrite using `[((hA X M T h hh).2 k⁻¹ (T.K.inv_mem hk) _).1, mul_smul, psi_inv T k hk (T.K.inv_mem hk)]`.
-/
private theorem ty_act (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1)
    {V : Type} [AddCommGroup V] [Module ℂ V] (Φ : X → V) (hΦ : ∀ k ∈ T.K₀, ∀ g, Φ (g * k) = Φ g) :
    T.IsTy (hAct T.K₀ (T.tf h) Φ) := by
  intro k hk g
  have hF : ∀ (y : X) (c : T.K₀), (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) (y * c) =
      (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) y := by
    intro y c
    simp only
    rw [← mul_assoc, tf_right hA T h hh _ c, ← mul_assoc, hΦ c c.2]
  have hs := P.finsum_out_mul T.K₀ k (fun y => T.tf h (k⁻¹ * y) • Φ (g * y)) hF
  simp only [inv_mul_cancel_left] at hs
  simp only [hAct, mul_assoc]
  rw [hs, smul_finsum]
  congr 1
  funext x
  rw [((hA X M T h hh).2 k⁻¹ (T.K.inv_mem hk) _).1, mul_smul, psi_inv T k hk (T.K.inv_mem hk)]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Use `set Φ : X → ℂ := fun y => T.tf h (y⁻¹ * g) with hΦdef`. Establish `hTy : T.IsTy Φ`. Introduce `k hk y`. Simplify using `only [hΦdef, smul_eq_mul, mul_inv_rev, mul_assoc]`.

Rewrite using `[((hA X M T h hh).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1, psi_inv T k hk (T.K.inv_mem hk)]`. Establish `hc` using `hC X M T 1 (by simp [TyLev.Cen]) ℂ Φ hTy 1`. Simplify using `only [hAct, conv, one_mul, mul_one, inv_one, smul_eq_mul, hΦdef] at hc ⊢`. Conclude with `hc`.
-/
private theorem conv_left (hA : TfAdm) (hC : TfCen) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) :
    conv T.K₀ (T.tf 1) (T.tf h) = T.tf h := by
  funext g
  set Φ : X → ℂ := fun y => T.tf h (y⁻¹ * g) with hΦdef
  have hTy : T.IsTy Φ := by
    intro k hk y
    simp only [hΦdef, smul_eq_mul, mul_inv_rev, mul_assoc]
    rw [((hA X M T h hh).2 k⁻¹ (T.K.inv_mem hk) (y⁻¹ * g)).1, psi_inv T k hk (T.K.inv_mem hk)]
  have hc := hC X M T 1 (by simp [TyLev.Cen]) ℂ Φ hTy 1
  simp only [hAct, conv, one_mul, mul_one, inv_one, smul_eq_mul, hΦdef] at hc ⊢
  exact hc

/- English proof (translation)
Establish `hn : y ∉ DoubleCoset.doubleCoset (1 : X) (T.K : Set X) T.K`. Rewrite using `[DoubleCoset.mem_doubleCoset]`. Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Conclude with `hy (by simpa using T.K.mul_mem ha hb)`. Simplify using `[TyLev.tf, dosetInd, Set.indicator_apply, hn]`.
-/
private theorem tf_one_not_mem (T : TyLev X M) (y : X) (hy : y ∉ T.K) : T.tf 1 y = 0 := by
  have hn : y ∉ DoubleCoset.doubleCoset (1 : X) (T.K : Set X) T.K := by
    rw [DoubleCoset.mem_doubleCoset]
    rintro ⟨a, ha, b, hb, rfl⟩
    exact hy (by simpa using T.K.mul_mem ha hb)
  simp [TyLev.tf, dosetInd, Set.indicator_apply, hn]

/- English proof (translation)
Establish `h1 : (1 : X) ∈ DoubleCoset.doubleCoset (1 : X) (T.K : Set X) T.K` using `DoubleCoset.mem_doubleCoset.2 ⟨1, T.K.one_mem, 1, T.K.one_mem, by simp⟩`. Establish `h2 : T.ψ ⟨1, T.J.one_mem⟩ = 1` using `map_one T.ψ`. Simplify using `[TyLev.tf, tyFn, dosetInd, Set.indicator_apply, h1, T.J.one_mem, h2]`.
-/
private theorem tf_one_one (T : TyLev X M) : T.tf 1 1 = ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ := by
  have h1 : (1 : X) ∈ DoubleCoset.doubleCoset (1 : X) (T.K : Set X) T.K :=
    DoubleCoset.mem_doubleCoset.2 ⟨1, T.K.one_mem, 1, T.K.one_mem, by simp⟩
  have h2 : T.ψ ⟨1, T.J.one_mem⟩ = 1 := map_one T.ψ
  simp [TyLev.tf, tyFn, dosetInd, Set.indicator_apply, h1, T.J.one_mem, h2]

/- English proof (translation)
Set `φ : K ⧸ K₀.subgroupOf K → X ⧸ K₀` to `Quotient.map' (fun k : K => (k : X)) (fun a b hab => QuotientGroup.leftRel_apply.mpr (by`. Establish `hab'` using `QuotientGroup.leftRel_apply.mp hab`. Simplify `hab'))` using `[Subgroup.mem_subgroupOf]`. Establish `hφ : ∀ k : K, φ (k : K ⧸ K₀.subgroupOf K) = ((k : X) : X ⧸ K₀)` using `fun k => rfl`. Establish `hinj : Function.Injective φ`.

Introduce `a b hab`. Proceed by induction on `a using QuotientGroup.induction_on with | H a => ?_`. Proceed by induction on `b using QuotientGroup.induction_on with | H b => ?_`. Rewrite `hab` using `[hφ, hφ, QuotientGroup.eq]`. Rewrite using `[QuotientGroup.eq]`.

Simplify `hab` using `[Subgroup.mem_subgroupOf]`. Establish `hrange : ∀ z : X ⧸ K₀, z ∈ Set.range φ ↔ z.out ∈ K`. Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`.

Proceed by induction on `w using QuotientGroup.induction_on with | H k => ?_`. Rewrite using `[hφ]`. Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul K₀ (k : X)`. Rewrite using `[hc]`. Conclude with `K.mul_mem k.2 (hle c.2)`.

Introduce `hz`. Use `⟨((⟨z.out, hz⟩ : K) : K ⧸ K₀.subgroupOf K), ?_⟩` and prove the remaining obligations. Rewrite using `[hφ]`. Conclude with `QuotientGroup.out_eq' z`. Establish `hG : G = (Set.range φ).indicator (fun _ => c)`.

Use function extensionality and compare the values at `z`. Distinguish the cases in `hz : z.out ∈ K`. Rewrite using `[Set.indicator_of_mem ((hrange z).2 hz), h1 z hz]`. Rewrite using `[Set.indicator_of_notMem (fun h => hz ((hrange z).1 h)), h0 z hz]`. Rewrite using `[hG, ← finsum_mem_def, finsum_mem_range hinj]`.

Establish `hfin : Finite (K ⧸ K₀.subgroupOf K)` using `Nat.finite_of_card_ne_zero (by exact hi)`. Use `haveI := Fintype.ofFinite (K ⧸ K₀.subgroupOf K)`. Rewrite using `[finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Use `congr 1`. Rewrite using `[← Nat.card_eq_fintype_card]`.

Both sides reduce to the same expression.
-/
private theorem finsum_cosets (K K₀ : Subgroup X) (hle : K₀ ≤ K) (hi : K₀.relIndex K ≠ 0) (c : ℂ)
    (G : X ⧸ K₀ → ℂ) (h1 : ∀ z : X ⧸ K₀, z.out ∈ K → G z = c)
    (h0 : ∀ z : X ⧸ K₀, z.out ∉ K → G z = 0) :
    ∑ᶠ z, G z = ((K₀.relIndex K : ℕ) : ℂ) * c := by
  let φ : K ⧸ K₀.subgroupOf K → X ⧸ K₀ :=
    Quotient.map' (fun k : K => (k : X)) (fun a b hab => QuotientGroup.leftRel_apply.mpr (by
      have hab' := QuotientGroup.leftRel_apply.mp hab
      simpa [Subgroup.mem_subgroupOf] using hab'))
  have hφ : ∀ k : K, φ (k : K ⧸ K₀.subgroupOf K) = ((k : X) : X ⧸ K₀) := fun k => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    rw [hφ, hφ, QuotientGroup.eq] at hab
    rw [QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using hab
  have hrange : ∀ z : X ⧸ K₀, z ∈ Set.range φ ↔ z.out ∈ K := by
    intro z
    constructor
    · rintro ⟨w, rfl⟩
      induction w using QuotientGroup.induction_on with | H k => ?_
      rw [hφ]
      obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K₀ (k : X)
      rw [hc]
      exact K.mul_mem k.2 (hle c.2)
    · intro hz
      refine ⟨((⟨z.out, hz⟩ : K) : K ⧸ K₀.subgroupOf K), ?_⟩
      rw [hφ]
      exact QuotientGroup.out_eq' z
  have hG : G = (Set.range φ).indicator (fun _ => c) := by
    funext z
    by_cases hz : z.out ∈ K
    · rw [Set.indicator_of_mem ((hrange z).2 hz), h1 z hz]
    · rw [Set.indicator_of_notMem (fun h => hz ((hrange z).1 h)), h0 z hz]
  rw [hG, ← finsum_mem_def, finsum_mem_range hinj]
  have hfin : Finite (K ⧸ K₀.subgroupOf K) := Nat.finite_of_card_ne_zero (by exact hi)
  haveI := Fintype.ofFinite (K ⧸ K₀.subgroupOf K)
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [← Nat.card_eq_fintype_card]
  rfl

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `hF : ∀ (y : X) (c : T.K₀), (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) (y * c) = (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) y`. Introduce `y c`. Simplify using `only`. Rewrite using `[tf_right hA T h hh y c, mul_inv_rev, mul_assoc, show ((c : X)⁻¹) = ((c⁻¹ : T.K₀) : X) from rfl, tf_left hA T 1 (map_one _) (y⁻¹ * g) c⁻¹]`.

Establish `hs` using `P.finsum_out_mul T.K₀ g (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) hF`. Simplify using `only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] at hs`. Simplify using `only [conv]`. Rewrite using `[← hs]`. Rewrite using `[finsum_cosets T.K T.K₀ T.le T.idx (((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ * T.tf h g) _ ?_ ?_]`.

Establish `hne : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 T.idx`. Clear the denominators using the available nonvanishing facts. Introduce `z hz`. Establish `hz' : (z.out)⁻¹ ∈ T.K` using `T.K.inv_mem hz`. Rewrite using `[((hA X M T h hh).2 _ hz g).2]`.

Establish `e` using `((hA X M T 1 (map_one _)).2 _ hz' 1).1`. Rewrite `e` using `[mul_one]`. Rewrite using `[e, tf_one_one, psi_inv T _ hz hz']`. Establish `hu` using `Units.inv_mul (T.ψ ⟨T.L.pr z.out, T.fact.2 _ hz⟩)`. Take the linear combination `(T.tf h g * ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹) * hu`.

Introduce `z hz`. Rewrite using `[tf_one_not_mem T _ (fun h' => hz (by simpa using T.K.inv_mem h')), mul_zero]`.
-/
private theorem conv_right (hA : TfAdm) (T : TyLev X M) (h : X) (hh : T.L.pr h = 1) :
    conv T.K₀ (T.tf h) (T.tf 1) = T.tf h := by
  funext g
  have hF : ∀ (y : X) (c : T.K₀), (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) (y * c) =
      (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) y := by
    intro y c
    simp only
    rw [tf_right hA T h hh y c, mul_inv_rev, mul_assoc,
      show ((c : X)⁻¹) = ((c⁻¹ : T.K₀) : X) from rfl, tf_left hA T 1 (map_one _) (y⁻¹ * g) c⁻¹]
  have hs := P.finsum_out_mul T.K₀ g (fun y => T.tf h y * T.tf 1 (y⁻¹ * g)) hF
  simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one] at hs
  simp only [conv]
  rw [← hs]
  rw [finsum_cosets T.K T.K₀ T.le T.idx (((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹ * T.tf h g) _ ?_ ?_]
  · have hne : ((T.K₀.relIndex T.K : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 T.idx
    field_simp
  · intro z hz
    have hz' : (z.out)⁻¹ ∈ T.K := T.K.inv_mem hz
    rw [((hA X M T h hh).2 _ hz g).2]
    have e := ((hA X M T 1 (map_one _)).2 _ hz' 1).1
    rw [mul_one] at e
    rw [e, tf_one_one, psi_inv T _ hz hz']
    have hu := Units.inv_mul (T.ψ ⟨T.L.pr z.out, T.fact.2 _ hz⟩)
    linear_combination (T.tf h g * ((T.K₀.relIndex T.K : ℕ) : ℂ)⁻¹) * hu
  · intro z hz
    rw [tf_one_not_mem T _ (fun h' => hz (by simpa using T.K.inv_mem h')), mul_zero]

end UpperTheory.Gal.W2.Seed.TypeIdempotent

open UpperTheory.Gal.W2.Seed.TypeIdempotent in
/- English proof (translation)
Introduce `hA hC X M _ _ T h hh`. Conclude with `⟨fun V _ _ Φ hΦ => ty_act hA T h hh Φ hΦ, conv_right hA T h hh, conv_left hA hC T h hh⟩`.
-/
theorem UpperTheory.Gal.W2.Seed.pTfIdem : TfAdm → TfCen → TfIdem := by
  intro hA hC X M _ _ T h hh
  exact ⟨fun V _ _ Φ hΦ => ty_act hA T h hh Φ hΦ, conv_right hA T h hh, conv_left hA hC T h hh⟩
