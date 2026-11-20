import Mathlib
import Formalism.LocalToGlobal.Columns.InvariantSubspaceCoordsX
import Formalism.LocalToGlobal.Columns.RowFormsNZ
import Formalism.LocalToGlobal.GlobalTheory.GL4.PDetAll

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.DivisionValues

section Idem

variable {K : Type} [Field K] {A : Type} [Group A] {M : Type} [Group M] [Fintype M]

def v0eZ (j : M →* A) (ε : M →* Kˣ) : MonoidAlgebra K A :=
  ∑ ζ : M, MonoidAlgebra.single (j ζ) ((Fintype.card M : K)⁻¹ * (((ε ζ)⁻¹ : Kˣ) : K))

open Classical in
/- English proof (translation)
Rewrite using `[v0eZ, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]`. Use `Finset.sum_congr rfl fun ζ _ => ?_` and prove the remaining obligations. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_apply]`.
-/
theorem centralIdempotent_coeff (j : M →* A) (ε : M →* Kˣ) (u : A) :
    (v0eZ j ε).coeff u = ∑ ζ : M, if j ζ = u then (Fintype.card M : K)⁻¹ * (((ε ζ)⁻¹ : Kˣ) : K) else 0 := by
  classical
  rw [v0eZ, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [MonoidAlgebra.coeff_single, Finsupp.single_apply]

end Idem

section Gen

variable {X : Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 X.E))}
  (C : CoefPk X n (DecoSet X.E n ST SG)) (Λ : LevFam X.E X.K n SG) {A : Type} [Group A] [Fintype A]
  (ι : A →* GLG X.E n SG) (hι : ∀ a w, (Λ w).NormBy (ι a w))
  {M : Type} [Group M] [Fintype M] (j : M →* A) (ε : M →* X.Kˣ)

/- English proof (translation)
Rewrite using `[Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]`.
-/
theorem representation_asAlgebraHom_sum (a : MonoidAlgebra X.K A) :
    (trRep C Λ ι hι).asAlgebraHom a = ∑ t : A, a.coeff t • trRep C Λ ι hι t := by
  rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (by intro i; simp)]

/- English proof (translation)
Establish `hcard : (Fintype.card M : X.K) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `hv : ∀ g : (formGSD C Λ).G, g • d = d → (formGSD C Λ).ρ g v = v`. Introduce and unpack `⟨γ, h⟩ hg`. Conclude with `hfix γ h hg`. Set `φ0 : (formGSD C Λ).EqFun` to `⟨(formGSD C Λ).orbFun d v, GSD.orbFun_mem hv⟩`.

Establish `hφd : (φ0 : DecoSet X.E n ST SG → C.V) d = v`. Establish `h1` using `GSD.orbFun_smul hv 1`. Rewrite `h1` using `[one_smul, map_one]`. Conclude with `h1`. Establish `hval : ∀ u : A, (φ0 : DecoSet X.E n ST SG → C.V) (((1 : UF X.E n), ι u) • d) = ((Fintype.card M : X.K) * (v0eZ j ε).coeff u) • v`.

Introduce `u`. Distinguish the cases in `hu : ∃ ζ, j ζ = u`. Take `⟨ζ0, rfl⟩` from `hu`. Establish `h1 : ((trRep C Λ ι hι (j ζ0⁻¹) φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) d = ((((ε ζ0⁻¹ : X.Kˣ) : X.K) • φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) d`. Rewrite using `[hscal]`.

Rewrite `h1` using `[trRep_apply]`. Simplify using `only [map_inv, inv_inv] at h1`. Rewrite using `[h1, Submodule.coe_smul, Pi.smul_apply, hφd, centralIdempotent_coeff, Finset.sum_eq_single_of_mem ζ0 (Finset.mem_univ _) (fun b _ hb => if_neg (fun e => hb (hj e))), if_pos rfl, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]`. Establish `h0 : (v0eZ j ε).coeff u = 0`. Rewrite using `[centralIdempotent_coeff]`.

Conclude with `Finset.sum_eq_zero fun ζ _ => if_neg fun e => hu ⟨ζ, e⟩`. Rewrite using `[h0, mul_zero, zero_smul]`. Use `show (formGSD C Λ).orbFun d v _ = 0`. Unfold `GSD.orbFun`. Rewrite using `[dif_neg]`.

Introduce and unpack `⟨⟨γ, h⟩, hg⟩`. Take `⟨h', e1, -⟩` from `Λ.normBy (ι u) (fun w => hι u w) h`. Apply `hu` to reduce the goal to its premises. Establish `hst : ((γ, h'.1 * ι u⁻¹) : UF X.E n × GLG X.E n SG) = ((1 : UF X.E n), ι u)⁻¹ * (γ, h.1)` using `Prod.ext (by simp) (by simp only [Prod.snd_mul, Prod.snd_inv, map_inv]; exact e1.symm)`. Establish `hg' : ((γ, h.1) : UF X.E n × GLG X.E n SG) • d = ((1 : UF X.E n), ι u) • d` using `hg`.

Take `⟨ζ, hζ⟩` from `hfree γ h' u⁻¹ (by rw [hst, mul_smul, hg', inv_smul_smul])`. Conclude with `⟨ζ⁻¹, by rw [map_inv, hζ, inv_inv]⟩`. Establish `hterm : ∀ t s : A, ((trRep C Λ ι hι t φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) (((1 : UF X.E n), ι s) • d) = ((Fintype.card M : X.K) * (v0eZ j ε).coeff (t⁻¹ * s)) • v`. Introduce `t s`. Rewrite using `[trRep_apply, smul_smul, Prod.mk_mul_mk, one_mul, ← map_inv, ← map_mul, hval]`.

Establish `hall : ∀ s : A, ((((trRep C Λ ι hι).asAlgebraHom a) φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) (((1 : UF X.E n), ι s) • d) = ((Fintype.card M : X.K) * (a * v0eZ j ε).coeff s) • v`. Introduce `s`. Rewrite using `[representation_asAlgebraHom_sum, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]`. Simplify using `only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, hterm, smul_smul]`. Rewrite using `[← Finset.sum_smul, coeff_mul_fin, Finset.mul_sum]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl fun t _ => by ring`. Introduce `hz`. Apply `ha` to reduce the goal to its premises. Establish `hc : ∀ s : A, (a * v0eZ j ε).coeff s = 0`.

Introduce `s`. Establish `h1` using `hall s`. Rewrite `h1` using `[hz]`. Establish `h2 : ((Fintype.card M : X.K) * (a * v0eZ j ε).coeff s) • v = 0`. Rewrite using `[← h1]`.

Both sides reduce to the same expression. Conclude with `(mul_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)).resolve_left hcard`. Rewrite using `[eq_sum_single (a * v0eZ j ε)]`. Conclude with `Finset.sum_eq_zero fun t _ => by rw [hc t, MonoidAlgebra.single_zero]`.
-/
theorem trRep_asAlgebraHom_ne_zero_of_mul_v0eZ_ne_zero (hj : Function.Injective j)
    (hscal : ∀ (ζ : M) (φ : (formGSD C Λ).EqFun), trRep C Λ ι hι (j ζ) φ = ((ε ζ : X.Kˣ) : X.K) • φ)
    (d : DecoSet X.E n ST SG) (v : C.V) (hv0 : v ≠ 0)
    (hfix : ∀ (γ : UF X.E n) (h : ↥Λ.grp), (γ, h.1) • d = d → ((Λ.chr h : X.Kˣ) : X.K) • C.rho γ v = v)
    (hfree : ∀ (γ : UF X.E n) (h : ↥Λ.grp) (t : A), (γ, h.1 * ι t) • d = d → ∃ ζ, j ζ = t)
    (a : MonoidAlgebra X.K A) (ha : a * v0eZ j ε ≠ 0) : (trRep C Λ ι hι).asAlgebraHom a ≠ 0 := by
  classical
  have hcard : (Fintype.card M : X.K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hv : ∀ g : (formGSD C Λ).G, g • d = d → (formGSD C Λ).ρ g v = v := by
    rintro ⟨γ, h⟩ hg
    exact hfix γ h hg
  let φ0 : (formGSD C Λ).EqFun := ⟨(formGSD C Λ).orbFun d v, GSD.orbFun_mem hv⟩
  have hφd : (φ0 : DecoSet X.E n ST SG → C.V) d = v := by
    have h1 := GSD.orbFun_smul hv 1
    rw [one_smul, map_one] at h1
    exact h1
  have hval : ∀ u : A, (φ0 : DecoSet X.E n ST SG → C.V) (((1 : UF X.E n), ι u) • d) =
      ((Fintype.card M : X.K) * (v0eZ j ε).coeff u) • v := by
    intro u
    by_cases hu : ∃ ζ, j ζ = u
    · obtain ⟨ζ0, rfl⟩ := hu
      have h1 : ((trRep C Λ ι hι (j ζ0⁻¹) φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) d =
          ((((ε ζ0⁻¹ : X.Kˣ) : X.K) • φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V) d := by
        rw [hscal]
      rw [trRep_apply] at h1
      simp only [map_inv, inv_inv] at h1
      rw [h1, Submodule.coe_smul, Pi.smul_apply, hφd, centralIdempotent_coeff,
        Finset.sum_eq_single_of_mem ζ0 (Finset.mem_univ _) (fun b _ hb => if_neg (fun e => hb (hj e))), if_pos rfl,
        ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    · have h0 : (v0eZ j ε).coeff u = 0 := by
        rw [centralIdempotent_coeff]
        exact Finset.sum_eq_zero fun ζ _ => if_neg fun e => hu ⟨ζ, e⟩
      rw [h0, mul_zero, zero_smul]
      show (formGSD C Λ).orbFun d v _ = 0
      unfold GSD.orbFun
      rw [dif_neg]
      rintro ⟨⟨γ, h⟩, hg⟩
      obtain ⟨h', e1, -⟩ := Λ.normBy (ι u) (fun w => hι u w) h
      apply hu
      have hst : ((γ, h'.1 * ι u⁻¹) : UF X.E n × GLG X.E n SG) = ((1 : UF X.E n), ι u)⁻¹ * (γ, h.1) :=
        Prod.ext (by simp) (by simp only [Prod.snd_mul, Prod.snd_inv, map_inv]; exact e1.symm)
      have hg' : ((γ, h.1) : UF X.E n × GLG X.E n SG) • d = ((1 : UF X.E n), ι u) • d := hg
      obtain ⟨ζ, hζ⟩ := hfree γ h' u⁻¹ (by rw [hst, mul_smul, hg', inv_smul_smul])
      exact ⟨ζ⁻¹, by rw [map_inv, hζ, inv_inv]⟩
  have hterm : ∀ t s : A, ((trRep C Λ ι hι t φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V)
      (((1 : UF X.E n), ι s) • d) = ((Fintype.card M : X.K) * (v0eZ j ε).coeff (t⁻¹ * s)) • v := by
    intro t s
    rw [trRep_apply, smul_smul, Prod.mk_mul_mk, one_mul, ← map_inv, ← map_mul, hval]
  have hall : ∀ s : A, ((((trRep C Λ ι hι).asAlgebraHom a) φ0 : (formGSD C Λ).EqFun) : DecoSet X.E n ST SG → C.V)
      (((1 : UF X.E n), ι s) • d) = ((Fintype.card M : X.K) * (a * v0eZ j ε).coeff s) • v := by
    intro s
    rw [representation_asAlgebraHom_sum, LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply, hterm, smul_smul]
    rw [← Finset.sum_smul, coeff_mul_fin, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun t _ => by ring
  intro hz
  apply ha
  have hc : ∀ s : A, (a * v0eZ j ε).coeff s = 0 := by
    intro s
    have h1 := hall s
    rw [hz] at h1
    have h2 : ((Fintype.card M : X.K) * (a * v0eZ j ε).coeff s) • v = 0 := by
      rw [← h1]
      rfl
    exact (mul_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv0)).resolve_left hcard
  rw [eq_sum_single (a * v0eZ j ε)]
  exact Finset.sum_eq_zero fun t _ => by rw [hc t, MonoidAlgebra.single_zero]

end Gen

section StabComb

variable (κ : Type) [CommRing κ] {n : ℕ}

def v0N (r : ℕ) (c : Fin n → κ) : Matrix (Fin n) (Fin n) κ :=
  Matrix.of fun a b => if r ≤ a.val ∧ b.val < r then c b else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nilpotentBlock_apply (r : ℕ) (c : Fin n → κ) (a b : Fin n) : v0N κ r c a b = if r ≤ a.val ∧ b.val < r then c b else 0 := rfl

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[Matrix.mul_apply, Matrix.zero_apply]`. Use `Finset.sum_eq_zero fun x _ => ?_` and prove the remaining obligations. Rewrite using `[nilpotentBlock_apply, nilpotentBlock_apply]`. Distinguish the cases in `h1 : r ≤ a.val ∧ x.val < r`.

Distinguish the cases in `h2 : r ≤ x.val ∧ b.val < r`. Conclude with `absurd h2.1 (Nat.not_le.mpr h1.2)`. Rewrite using `[if_neg h2, mul_zero]`. Rewrite using `[if_neg h1, zero_mul]`.
-/
theorem nilpotentBlock_sq_eq_zero (r : ℕ) (c : Fin n → κ) : v0N κ r c * v0N κ r c = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [nilpotentBlock_apply, nilpotentBlock_apply]
  by_cases h1 : r ≤ a.val ∧ x.val < r
  · by_cases h2 : r ≤ x.val ∧ b.val < r
    · exact absurd h2.1 (Nat.not_le.mpr h1.2)
    · rw [if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

def v0A (r : ℕ) (c : Fin n → κ) : GL (Fin n) κ where
  val := 1 + v0N κ r c
  inv := 1 - v0N κ r c
  val_inv := by
    have : (1 + v0N κ r c) * (1 - v0N κ r c) = 1 - v0N κ r c * v0N κ r c := by noncomm_ring
    rw [this, nilpotentBlock_sq_eq_zero, sub_zero]
  inv_val := by
    have : (1 - v0N κ r c) * (1 + v0N κ r c) = 1 - v0N κ r c * v0N κ r c := by noncomm_ring
    rw [this, nilpotentBlock_sq_eq_zero, sub_zero]

variable {κ}

/- English proof (translation)
Rewrite using `[← coarse_eq_zero (bl := bl), hco, coarse_eq_zero]`.
-/
theorem perm_lt_iff_lt {r : ℕ} {bl : List ℕ} (s : Equiv.Perm (Fin n))
    (hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) (b : Fin n) : (s b).val < r ↔ b.val < r := by
  rw [← coarse_eq_zero (bl := bl), hco, coarse_eq_zero]

/- English proof (translation)
Rewrite using `[← perm_lt_iff_lt s hco (s⁻¹ b), show s (s⁻¹ b) = b by simp]`.
-/
theorem lt_iff_perm_inv_lt {r : ℕ} {bl : List ℕ} (s : Equiv.Perm (Fin n))
    (hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) (b : Fin n) : (s⁻¹ b).val < r ↔ b.val < r := by
  rw [← perm_lt_iff_lt s hco (s⁻¹ b), show s (s⁻¹ b) = b by simp]

/- English proof (translation)
Establish `e' : ∀ a' c', h.1 a' c' + ∑ b, v0N κ r c a' b * h.1 b c' = M a' c' + u (s⁻¹ a') * v0N κ r c (s⁻¹ a') c'`. Introduce `a' c'`. Use `congrFun (congrFun e a') c'` as an intermediate fact. Express the relevant statement in the definitionally equal form `((1 + v0N κ r c) * h.1) a' c' = (M * (1 + v0N κ r c)) a' c' at this`. Rewrite `this` using `[add_mul, mul_add, one_mul, mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.mul_apply]`.

Rewrite using `[this]`. Use `congr 1`. Rewrite using `[Finset.sum_eq_single (s⁻¹ a')]`. Rewrite using `[hM, if_pos (by simp)]`. Introduce `b _ hb`.

Rewrite using `[hM, if_neg (fun h' => hb (by rw [h']; simp)), zero_mul]`. Simplify using the standard rewrite rules. Establish `hrow : ∀ b : Fin n, b.val < r → h.1 b i = M b i`. Introduce `b hb`. Establish `h1` using `e' b i`.

Establish `h2 : ∑ x, v0N κ r c b x * h.1 x i = 0` using `Finset.sum_eq_zero fun x _ => by rw [nilpotentBlock_apply, if_neg (fun hh => absurd hh.1 (Nat.not_le.mpr hb)), zero_mul]`. Rewrite `h1` using `[h2, nilpotentBlock_apply, if_neg (fun hh => absurd hh.1 (Nat.not_le.mpr ((lt_iff_perm_inv_lt s hco b).mpr hb))), mul_zero, add_zero, add_zero]`. Conclude with `h1`. Establish `h1` using `e' a i`. Establish `hsi : (s i).val < r` using `(perm_lt_iff_lt s hco i).mpr hi`.

Establish `h3 : h.1 a i = 0`. Apply `mem_btG.mp hh` to reduce the goal to its premises. Rewrite using `[coarse_of_lt hi, coarse_of_le ha]`. Use linear arithmetic over natural numbers and integers. Establish `h4 : M a i = 0`.

Rewrite using `[hM, if_neg]`. Introduce `hc`. Rewrite `ha` using `[hc]`. Use linear arithmetic over natural numbers and integers. Establish `h5 : ∑ x, v0N κ r c a x * h.1 x i = c (s i) * u i`.

Rewrite using `[Finset.sum_eq_single (s i)]`. Rewrite using `[nilpotentBlock_apply, if_pos ⟨ha, hsi⟩, hrow _ hsi, hM, if_pos rfl]`. Introduce `b _ hb`. Rewrite using `[nilpotentBlock_apply]`. Distinguish the cases in `hb' : b.val < r`.

Rewrite using `[if_pos ⟨ha, hb'⟩, hrow b hb', hM, if_neg hb, mul_zero]`. Rewrite using `[if_neg (fun hh => hb' hh.2), zero_mul]`. Simplify using the standard rewrite rules. Establish `hsa : r ≤ (s⁻¹ a).val` using `Nat.not_lt.mp fun hc => absurd ((lt_iff_perm_inv_lt s hco a).mp hc) (Nat.not_lt.mpr ha)`. Rewrite `h1` using `[h3, h4, h5, nilpotentBlock_apply, if_pos ⟨hsa, hi⟩, zero_add, zero_add]`.

Conclude with `h1`.
-/
theorem conj_nilpotent_scalar_relation {r : ℕ} {bl : List ℕ} (c : Fin n → κ) (s : Equiv.Perm (Fin n)) (u : Fin n → κ)
    (hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) (M : Matrix (Fin n) (Fin n) κ)
    (hM : ∀ a b, M a b = if a = s b then u b else 0) (h : GL (Fin n) κ) (hh : h ∈ blockUT n κ r bl)
    (e : (v0A κ r c).1 * h.1 = M * (v0A κ r c).1) (a i : Fin n) (ha : r ≤ a.val) (hi : i.val < r) :
    c (s i) * u i = u (s⁻¹ a) * c i := by
  have e' : ∀ a' c', h.1 a' c' + ∑ b, v0N κ r c a' b * h.1 b c' =
      M a' c' + u (s⁻¹ a') * v0N κ r c (s⁻¹ a') c' := by
    intro a' c'
    have := congrFun (congrFun e a') c'
    change ((1 + v0N κ r c) * h.1) a' c' = (M * (1 + v0N κ r c)) a' c' at this
    rw [add_mul, mul_add, one_mul, mul_one, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply,
      Matrix.mul_apply] at this
    rw [this]
    congr 1
    rw [Finset.sum_eq_single (s⁻¹ a')]
    · rw [hM, if_pos (by simp)]
    · intro b _ hb
      rw [hM, if_neg (fun h' => hb (by rw [h']; simp)), zero_mul]
    · simp
  have hrow : ∀ b : Fin n, b.val < r → h.1 b i = M b i := by
    intro b hb
    have h1 := e' b i
    have h2 : ∑ x, v0N κ r c b x * h.1 x i = 0 :=
      Finset.sum_eq_zero fun x _ => by rw [nilpotentBlock_apply, if_neg (fun hh => absurd hh.1 (Nat.not_le.mpr hb)), zero_mul]
    rw [h2, nilpotentBlock_apply, if_neg (fun hh => absurd hh.1 (Nat.not_le.mpr ((lt_iff_perm_inv_lt s hco b).mpr hb))), mul_zero,
      add_zero, add_zero] at h1
    exact h1
  have h1 := e' a i
  have hsi : (s i).val < r := (perm_lt_iff_lt s hco i).mpr hi
  have h3 : h.1 a i = 0 := by
    apply mem_btG.mp hh
    rw [coarse_of_lt hi, coarse_of_le ha]
    omega
  have h4 : M a i = 0 := by
    rw [hM, if_neg]
    intro hc
    rw [hc] at ha
    omega
  have h5 : ∑ x, v0N κ r c a x * h.1 x i = c (s i) * u i := by
    rw [Finset.sum_eq_single (s i)]
    · rw [nilpotentBlock_apply, if_pos ⟨ha, hsi⟩, hrow _ hsi, hM, if_pos rfl]
    · intro b _ hb
      rw [nilpotentBlock_apply]
      by_cases hb' : b.val < r
      · rw [if_pos ⟨ha, hb'⟩, hrow b hb', hM, if_neg hb, mul_zero]
      · rw [if_neg (fun hh => hb' hh.2), zero_mul]
    · simp
  have hsa : r ≤ (s⁻¹ a).val := Nat.not_lt.mp fun hc => absurd ((lt_iff_perm_inv_lt s hco a).mp hc) (Nat.not_lt.mpr ha)
  rw [h3, h4, h5, nilpotentBlock_apply, if_pos ⟨hsa, hi⟩, zero_add, zero_add] at h1
  exact h1

/- English proof (translation)
Establish `hPN : pM κ s * v0N κ r c = v0N κ r c * pM κ s`. Use extensionality with `a b`. Rewrite using `[mul_pM_apply, pM_mul_apply, nilpotentBlock_apply, nilpotentBlock_apply]`. Establish `h1 : r ≤ (s⁻¹ a).val ↔ r ≤ a.val`. Use `nz_ge_of_fix s hfix (s⁻¹ a)` as an intermediate fact.

Rewrite `this` using `[show s (s⁻¹ a) = a by simp]`. Conclude with `this.symm`. Distinguish the cases in `hb : b.val < r`. Rewrite using `[hfix b hb]`. Distinguish the cases in `ha : r ≤ a.val`.

Rewrite using `[if_pos ⟨h1.mpr ha, hb⟩, if_pos ⟨ha, hb⟩]`. Rewrite using `[if_neg (fun hh => ha (h1.mp hh.1)), if_neg (fun hh => ha hh.1)]`. Establish `h2 : ¬ (s b).val < r` using `fun hc => by`. Use `(nz_ge_of_fix s hfix b).mpr (Nat.not_lt.mp hb)` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Rewrite using `[if_neg (fun hh => hb hh.2), if_neg (fun hh => h2 hh.2)]`. Use `show (x • pM κ s) * (1 + v0N κ r c) = (1 + v0N κ r c) * (x • pM κ s)`. Rewrite using `[mul_add, add_mul, mul_one, one_mul, Matrix.smul_mul, Matrix.mul_smul, hPN]`.
-/
theorem permutation_commutes_nilpotent {r : ℕ} (c : Fin n → κ) (s : Equiv.Perm (Fin n)) (hfix : ∀ b : Fin n, b.val < r → s b = b) (x : κ) :
    (x • pM κ s) * (v0A κ r c).1 = (v0A κ r c).1 * (x • pM κ s) := by
  have hPN : pM κ s * v0N κ r c = v0N κ r c * pM κ s := by
    ext a b
    rw [mul_pM_apply, pM_mul_apply, nilpotentBlock_apply, nilpotentBlock_apply]
    have h1 : r ≤ (s⁻¹ a).val ↔ r ≤ a.val := by
      have := nz_ge_of_fix s hfix (s⁻¹ a)
      rw [show s (s⁻¹ a) = a by simp] at this
      exact this.symm
    by_cases hb : b.val < r
    · rw [hfix b hb]
      by_cases ha : r ≤ a.val
      · rw [if_pos ⟨h1.mpr ha, hb⟩, if_pos ⟨ha, hb⟩]
      · rw [if_neg (fun hh => ha (h1.mp hh.1)), if_neg (fun hh => ha hh.1)]
    · have h2 : ¬ (s b).val < r := fun hc => by
        have := (nz_ge_of_fix s hfix b).mpr (Nat.not_lt.mp hb)
        omega
      rw [if_neg (fun hh => hb hh.2), if_neg (fun hh => h2 hh.2)]
  show (x • pM κ s) * (1 + v0N κ r c) = (1 + v0N κ r c) * (x • pM κ s)
  rw [mul_add, add_mul, mul_one, one_mul, Matrix.smul_mul, Matrix.mul_smul, hPN]

end StabComb

section Stab

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Establish `h : (((x * y : 𝓞 E)) : E) = ((x : 𝓞 E) : E) * ((y : 𝓞 E) : E)` using `by push_cast; rfl`. Rewrite using `[h, star_mul, mul_assoc, ← mul_assoc (star ((x : 𝓞 E) : E)), hx, one_mul, hy]`.
-/
theorem normOne_mul {x y : 𝓞 E} (hx : star ((x : 𝓞 E) : E) * ((x : 𝓞 E) : E) = 1)
    (hy : star ((y : 𝓞 E) : E) * ((y : 𝓞 E) : E) = 1) : star (((x * y : 𝓞 E)) : E) * (((x * y : 𝓞 E)) : E) = 1 := by
  have h : (((x * y : 𝓞 E)) : E) = ((x : 𝓞 E) : E) * ((y : 𝓞 E) : E) := by push_cast; rfl
  rw [h, star_mul, mul_assoc, ← mul_assoc (star ((x : 𝓞 E) : E)), hx, one_mul, hy]

/- English proof (translation)
Rewrite using `[hx', star_star, mul_comm, hx]`.
-/
theorem normOne_conj {x x' : 𝓞 E} (hx : star ((x : 𝓞 E) : E) * ((x : 𝓞 E) : E) = 1)
    (hx' : ((x' : 𝓞 E) : E) = star ((x : 𝓞 E) : E)) : star ((x' : 𝓞 E) : E) * ((x' : 𝓞 E) : E) = 1 := by
  rw [hx', star_star, mul_comm, hx]

/- English proof (translation)
Take `⟨z', hz', -⟩` from `nz_exists_inv hz`. Set `u : (𝓞 E)ˣ` to `⟨z, z', by rw [mul_comm]; exact hz', hz'⟩`. Use `⟨⟨u, (NumberField.Units.mem_torsion E).mpr fun w => ?_⟩, rfl⟩` and prove the remaining obligations. Establish `h1` using `congrArg w.embedding hz`. Rewrite `h1` using `[map_mul, hconj, map_one]`.

Establish `h2 : ‖w.embedding ((z : 𝓞 E) : E)‖ ^ 2 = 1`. Establish `h3 : ((Complex.normSq (w.embedding ((z : 𝓞 E) : E)) : ℝ) : ℂ) = 1`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`. Conclude with `h1`. Rewrite using `[← Complex.normSq_eq_norm_sq]`.

Conclude with `h3` after adjusting the coercions. Rewrite using `[← NumberField.InfinitePlace.norm_embedding_eq]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2`.
-/
theorem normOne_integer_is_torsion (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) {z : 𝓞 E}
    (hz : star ((z : 𝓞 E) : E) * ((z : 𝓞 E) : E) = 1) :
    ∃ ζ : NumberField.Units.torsion E, (((ζ : (𝓞 E)ˣ) : 𝓞 E)) = z := by
  obtain ⟨z', hz', -⟩ := nz_exists_inv hz
  let u : (𝓞 E)ˣ := ⟨z, z', by rw [mul_comm]; exact hz', hz'⟩
  refine ⟨⟨u, (NumberField.Units.mem_torsion E).mpr fun w => ?_⟩, rfl⟩
  have h1 := congrArg w.embedding hz
  rw [map_mul, hconj, map_one] at h1
  have h2 : ‖w.embedding ((z : 𝓞 E) : E)‖ ^ 2 = 1 := by
    have h3 : ((Complex.normSq (w.embedding ((z : 𝓞 E) : E)) : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact h1
    rw [← Complex.normSq_eq_norm_sq]
    exact_mod_cast h3
  rw [← NumberField.InfinitePlace.norm_embedding_eq]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h2

end Stab

section StabPt

variable {X : Fields} {n : ℕ} [NeZero n] {SG : Finset (HeightOneSpectrum (𝓞 X.E))}

open Classical in

def v0Fr (pos : Equiv.Perm (Fin n)) (r : ℕ) (c : Fin n → 𝓞 X.E) (w1 : SG) : GLG X.E n SG := fun w =>
  if w = w1 then (v0A _ r fun b => Ideal.Quotient.mk w.1.asIdeal (c b))⁻¹ * permGL _ pos⁻¹ else permGL _ pos⁻¹

/- English proof (translation)
Establish `: w1.1.asIdeal.IsPrime` using `w1.1.isPrime`. Take `⟨G, hG, hh⟩` from `nz_stab _ γ h e`. Take `⟨s0, hs1, hs2⟩` from `nz_monomial hX.conjE G (nz_unitary γ G hG)`. Use `set s : Equiv.Perm (Fin n) := pos⁻¹ * s0 * pos with hs`. Establish `hsa : ∀ a b : Fin n, a = s b ↔ pos a = s0 (pos b)`.

Introduce `a b`. Rewrite using `[hs, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.eq_inv_iff_eq]`. Use `set z : Fin n → 𝓞 X.E := fun b => G (s0 (pos b)) (pos b) with hz`. Establish `hzu : ∀ b, star ((z b : 𝓞 X.E) : X.E) * ((z b : 𝓞 X.E) : X.E) = 1` using `fun b => hs1 (pos b)`. Establish `hGz : ∀ a b, G (pos a) (pos b) = if a = s b then z b else 0`.

Introduce `a b`. Distinguish the cases in `hab : a = s b`. Rewrite using `[if_pos hab, hz] show G (pos a) (pos b) = G (s0 (pos b)) (pos b)`. Rewrite using `[(hsa a b).mp hab]`. Rewrite using `[if_neg hab]`.

Conclude with `hs2 _ _ fun hc => hab ((hsa a b).mpr hc)`. Set `Gh : ∀ w : SG, GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal)` to `fun w => permGL _ pos⁻¹ * ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w) * (permGL _ pos⁻¹)⁻¹`. Establish `hGh : ∀ (w : SG) (a b : Fin n), (Gh w).1 a b = if a = s b then Ideal.Quotient.mk w.1.asIdeal (z b) else 0`. Introduce `w a b`. Establish `e1 : ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w).1 = G.map (Ideal.Quotient.mk w.1.asIdeal)`.

Rewrite using `[mul_assoc, Units.val_mul, Units.val_mul, hh w, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]`. Establish `e2 : (Gh w).1 = pM _ pos⁻¹ * G.map (Ideal.Quotient.mk w.1.asIdeal) * pM _ pos` using `by show (permGL _ pos⁻¹ * ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w) * (permGL _ pos⁻¹)⁻¹).1 = _`. Rewrite using `[Units.val_mul, Units.val_mul, e1, ← map_inv, inv_inv]`. Both sides reduce to the same expression. Rewrite using `[e2, mul_pM_apply, pM_mul_apply, inv_inv, Matrix.map_apply, hGz]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `hGhw : ∀ w : SG, w ≠ w1 → Gh w = h w`. Introduce `w hw`. Use `show permGL _ pos⁻¹ * ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w) * (permGL _ pos⁻¹)⁻¹ = h w`. Establish `: v0Fr (X` using `X) pos r c w1 w = permGL _ pos⁻¹ := if_neg hw`.

Rewrite using `[this]`. Use `group`. Establish `hne0 : ∀ (w : SG) (b : Fin n), Ideal.Quotient.mk w.1.asIdeal (z b) ≠ 0` using `fun w b hc => nz_unit_notMem (hzu b) w.1 (Ideal.Quotient.eq_zero_iff_mem.mp hc)`. Establish `hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val`. Introduce `b`.

Use `nz_perm_of_le (φ := fun b : Fin n => coarse r bl b.val) s (fun b => ?_) b` and prove the remaining obligations. Assume the negation of the conclusion as `hcon`. Establish `h0` using `mem_btG.mp h2 (s b) b (Nat.lt_of_not_le hcon)`. Rewrite `h0` using `[← hGhw w2 hne, hGh, if_pos rfl]`. Conclude with `hne0 w2 b h0`.

Establish `hA : v0A _ r (fun b => Ideal.Quotient.mk w1.1.asIdeal (c b)) * h w1 = Gh w1 * v0A _ r (fun b => Ideal.Quotient.mk w1.1.asIdeal (c b))` using `by show _ = permGL _ pos⁻¹ * ((v0Fr pos r c w1 w1)⁻¹ * h w1 * v0Fr pos r c w1 w1) * (permGL _ pos⁻¹)⁻¹ * _`. Establish `: v0Fr (X` using `X) pos r c w1 w1 = (v0A _ r fun b => Ideal.Quotient.mk w1.1.asIdeal (c b))⁻¹ * permGL _ pos⁻¹ := if_pos rfl`. Rewrite using `[this]`. Use `group`. Use `set Q := Ideal.Quotient.mk w1.1.asIdeal with hQ`.

Establish `key : ∀ a i : Fin n, r ≤ a.val → i.val < r → Q (c (s i)) * Q (z i) = Q (z (s⁻¹ a)) * Q (c i)` using `fun a i ha hi => conj_nilpotent_scalar_relation (fun b => Q (c b)) s (fun b => Q (z b)) hco (Gh w1).1 (hGh w1) (h w1) h1 (by rw [← Units.val_mul, ← Units.val_mul, hA]) a i ha hi`. Establish `hci : ∀ i : Fin n, i.val < r → Q (c i) ≠ 0` using `fun i hi h0 => hc0 i hi (Ideal.Quotient.eq_zero_iff_mem.mp h0)`. Set `i0 : Fin n` to `⟨0, lt_trans hr hn⟩`. Set `a0 : Fin n` to `⟨r, hn⟩`. Establish `hi0 : i0.val < r` using `hr`.

Establish `ha0 : r ≤ a0.val` using `le_refl r`. Establish `hzb : ∀ b : Fin n, r ≤ b.val → Q (z b) = Q (z (s⁻¹ a0))`. Introduce `b hb`. Establish `hsb : r ≤ (s b).val` using `Nat.not_lt.mp fun hc => absurd ((perm_lt_iff_lt s hco b).mp hc) (Nat.not_lt.mpr hb)`. Establish `k1` using `key (s b) i0 hsb hi0`.

Establish `k2` using `key a0 i0 ha0 hi0`. Rewrite `k1` using `[show s⁻¹ (s b) = b by simp]`. Conclude with `mul_right_cancel₀ (hci i0 hi0) (k1.symm.trans k2)`. Establish `hsi : ∀ i : Fin n, i.val < r → s i = i`. Introduce `i hi`.

Take `⟨zi', hzi', hzi'c⟩` from `nz_exists_inv (hzu i)`. Establish `k` using `key a0 i ha0 hi`. Use `hc i (s i) hi ((perm_lt_iff_lt s hco i).mpr hi) (z (s⁻¹ a0) * zi') (normOne_mul (hzu _) (normOne_conj (hzu i) hzi'c)) ?_` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul]`. Establish `hq : Q zi' * Q (z i) = 1` using `by rw [← map_mul, hzi', map_one]`.

Take the linear combination `(Q zi') * k - (Q (c (s i))) * hq`. Establish `hzi : ∀ i : Fin n, i.val < r → Q (z i) = Q (z (s⁻¹ a0))`. Introduce `i hi`. Establish `k` using `key a0 i ha0 hi`. Rewrite `k` using `[hsi i hi, mul_comm (Q (z (s⁻¹ a0)))]`.

Conclude with `mul_left_cancel₀ (hci i hi) k`. Establish `hQall : ∀ b : Fin n, Q (z b) = Q (z (s⁻¹ a0))` using `fun b => if hb : b.val < r then hzi b hb else hzb b (Nat.not_lt.mp hb)`. Use `set Z := z (s⁻¹ a0) with hZ`. Establish `hzall : ∀ b : Fin n, z b = Z`. Introduce `b`.

Take `⟨Z', hZ', hZ'c⟩` from `nz_exists_inv (hzu (s⁻¹ a0))`. Establish `h1' : z b * Z' = 1` using `nz_root_one hX w1.1 hg1 hgw1 hb1 (normOne_mul (hzu b) (normOne_conj (hzu _) hZ'c)) (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hQ, hQall b, ← map_mul, mul_comm, hZ', map_one, sub_self])`. Combine the equalities or inequalities in the displayed calculation. Establish `hGp : ∀ (w : SG) (a b : Fin n), (Gh w).1 a b = if a = s b then Ideal.Quotient.mk w.1.asIdeal Z else 0` using `fun w a b => by rw [hGh, hzall]`. Establish `hGw1 : Gh w1 = h w1`.

Establish `hcm : Gh w1 * v0A _ r (fun b => Q (c b)) = v0A _ r (fun b => Q (c b)) * Gh w1`. Establish `hGm : (Gh w1).1 = Q Z • pM _ s`. Use extensionality with `a b`. Rewrite using `[hGp, Matrix.smul_apply, pM_apply, smul_eq_mul]`. Apply the tactic sequence `split_ifs <;> simp [hQ]`.

Apply `Units.ext` to reduce the goal to its premises. Use `show (Gh w1).1 * (v0A _ r (fun b => Q (c b))).1 = (v0A _ r (fun b => Q (c b))).1 * (Gh w1).1`. Rewrite using `[hGm]`. Conclude with `permutation_commutes_nilpotent _ s hsi _`. Conclude with `(mul_left_cancel (hA.trans hcm)).symm`.

Use `⟨Z, s, hzu _, hsi, hco, fun i j => ?_, fun w i j => ?_⟩` and prove the remaining obligations. Rewrite using `[nz_ufGL_apply, ← hG]`. Establish `h3` using `hGz (pos⁻¹ i) (pos⁻¹ j)`. Rewrite `h3` using `[show pos (pos⁻¹ i) = i by simp, show pos (pos⁻¹ j) = j by simp, hzall]`. Rewrite using `[h3]`.

Establish `h4 : pos⁻¹ i = s (pos⁻¹ j) ↔ i = (pos * s * pos⁻¹) j` using `by show pos⁻¹ i = s (pos⁻¹ j) ↔ i = pos (s (pos⁻¹ j))`. Conclude with `Equiv.Perm.inv_eq_iff_eq`. Distinguish the cases in `h5 : pos⁻¹ i = s (pos⁻¹ j)`. Rewrite using `[if_pos h5, if_pos (h4.mp h5)]`. Rewrite using `[if_neg h5, if_neg (fun hc => h5 (h4.mpr hc)), map_zero]`.

Distinguish the cases in `hw : w = w1`. Substitute `hw` using the available equality. Rewrite using `[← hGw1, hGp]`. Rewrite using `[← hGhw w hw, hGp]`.
-/
theorem stabilizer_eq_scalar_mul_permMatrix (hX : X.Ok) (pos : Equiv.Perm (Fin n)) {r : ℕ} (bl : List ℕ) (hr : 0 < r) (hn : r < n)
    (c : Fin n → 𝓞 X.E) (w1 w2 : SG) (hne : w2 ≠ w1) (hc0 : ∀ i : Fin n, i.val < r → c i ∉ w1.1.asIdeal)
    (hc : ∀ i i' : Fin n, i.val < r → i'.val < r → ∀ z : 𝓞 X.E, star ((z : 𝓞 X.E) : X.E) * ((z : 𝓞 X.E) : X.E) = 1 →
      c i' - z * c i ∈ w1.1.asIdeal → i' = i)
    {g1 : ℕ} (hg1 : g1.Prime) (hgw1 : (g1 : 𝓞 X.E) ∈ w1.1.asIdeal) (hb1 : 2 * X.f + 1 < g1)
    (γ : UF X.E n) (h : GLG X.E n SG) (h2 : h w2 ∈ blockUT n _ r bl) (h1 : h w1 ∈ blockUT n _ r bl)
    (e : (γ, h) • nzPt (v0Fr pos r c w1) = nzPt (v0Fr pos r c w1)) :
    ∃ (z : 𝓞 X.E) (s : Equiv.Perm (Fin n)), star ((z : 𝓞 X.E) : X.E) * ((z : 𝓞 X.E) : X.E) = 1 ∧
      (∀ b : Fin n, b.val < r → s b = b) ∧ (∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) ∧
      (∀ i j : Fin n, ((ufGL X.E n γ : GL (Fin n) X.E) : Matrix (Fin n) (Fin n) X.E) i j =
        if i = (pos * s * pos⁻¹) j then algebraMap (𝓞 X.E) X.E z else 0) ∧
      ∀ (w : SG) (i j : Fin n), ((h w : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) i j =
        if i = s j then Ideal.Quotient.mk w.1.asIdeal z else 0 := by
  have : w1.1.asIdeal.IsPrime := w1.1.isPrime
  obtain ⟨G, hG, hh⟩ := nz_stab _ γ h e
  obtain ⟨s0, hs1, hs2⟩ := nz_monomial hX.conjE G (nz_unitary γ G hG)
  set s : Equiv.Perm (Fin n) := pos⁻¹ * s0 * pos with hs
  have hsa : ∀ a b : Fin n, a = s b ↔ pos a = s0 (pos b) := by
    intro a b
    rw [hs, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.Perm.eq_inv_iff_eq]
  set z : Fin n → 𝓞 X.E := fun b => G (s0 (pos b)) (pos b) with hz
  have hzu : ∀ b, star ((z b : 𝓞 X.E) : X.E) * ((z b : 𝓞 X.E) : X.E) = 1 := fun b => hs1 (pos b)
  have hGz : ∀ a b, G (pos a) (pos b) = if a = s b then z b else 0 := by
    intro a b
    by_cases hab : a = s b
    · rw [if_pos hab, hz]
      show G (pos a) (pos b) = G (s0 (pos b)) (pos b)
      rw [(hsa a b).mp hab]
    · rw [if_neg hab]
      exact hs2 _ _ fun hc => hab ((hsa a b).mpr hc)
  let Gh : ∀ w : SG, GL (Fin n) (𝓞 X.E ⧸ w.1.asIdeal) := fun w =>
    permGL _ pos⁻¹ * ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w) * (permGL _ pos⁻¹)⁻¹
  have hGh : ∀ (w : SG) (a b : Fin n), (Gh w).1 a b = if a = s b then Ideal.Quotient.mk w.1.asIdeal (z b) else 0 := by
    intro w a b
    have e1 : ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w).1 = G.map (Ideal.Quotient.mk w.1.asIdeal) := by
      rw [mul_assoc, Units.val_mul, Units.val_mul, hh w, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    have e2 : (Gh w).1 = pM _ pos⁻¹ * G.map (Ideal.Quotient.mk w.1.asIdeal) * pM _ pos := by
      show (permGL _ pos⁻¹ * ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w) * (permGL _ pos⁻¹)⁻¹).1 = _
      rw [Units.val_mul, Units.val_mul, e1, ← map_inv, inv_inv]
      rfl
    rw [e2, mul_pM_apply, pM_mul_apply, inv_inv, Matrix.map_apply, hGz]
    split_ifs <;> simp
  have hGhw : ∀ w : SG, w ≠ w1 → Gh w = h w := by
    intro w hw
    show permGL _ pos⁻¹ * ((v0Fr pos r c w1 w)⁻¹ * h w * v0Fr pos r c w1 w) * (permGL _ pos⁻¹)⁻¹ = h w
    have : v0Fr (X := X) pos r c w1 w = permGL _ pos⁻¹ := if_neg hw
    rw [this]
    group
  have hne0 : ∀ (w : SG) (b : Fin n), Ideal.Quotient.mk w.1.asIdeal (z b) ≠ 0 := fun w b hc =>
    nz_unit_notMem (hzu b) w.1 (Ideal.Quotient.eq_zero_iff_mem.mp hc)
  have hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val := by
    intro b
    refine nz_perm_of_le (φ := fun b : Fin n => coarse r bl b.val) s (fun b => ?_) b
    by_contra hcon
    have h0 := mem_btG.mp h2 (s b) b (Nat.lt_of_not_le hcon)
    rw [← hGhw w2 hne, hGh, if_pos rfl] at h0
    exact hne0 w2 b h0
  have hA : v0A _ r (fun b => Ideal.Quotient.mk w1.1.asIdeal (c b)) * h w1 =
      Gh w1 * v0A _ r (fun b => Ideal.Quotient.mk w1.1.asIdeal (c b)) := by
    show _ = permGL _ pos⁻¹ * ((v0Fr pos r c w1 w1)⁻¹ * h w1 * v0Fr pos r c w1 w1) * (permGL _ pos⁻¹)⁻¹ * _
    have : v0Fr (X := X) pos r c w1 w1 =
        (v0A _ r fun b => Ideal.Quotient.mk w1.1.asIdeal (c b))⁻¹ * permGL _ pos⁻¹ := if_pos rfl
    rw [this]
    group
  set Q := Ideal.Quotient.mk w1.1.asIdeal with hQ
  have key : ∀ a i : Fin n, r ≤ a.val → i.val < r → Q (c (s i)) * Q (z i) = Q (z (s⁻¹ a)) * Q (c i) :=
    fun a i ha hi => conj_nilpotent_scalar_relation (fun b => Q (c b)) s (fun b => Q (z b)) hco (Gh w1).1 (hGh w1) (h w1) h1
      (by rw [← Units.val_mul, ← Units.val_mul, hA]) a i ha hi
  have hci : ∀ i : Fin n, i.val < r → Q (c i) ≠ 0 := fun i hi h0 => hc0 i hi (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  let i0 : Fin n := ⟨0, lt_trans hr hn⟩
  let a0 : Fin n := ⟨r, hn⟩
  have hi0 : i0.val < r := hr
  have ha0 : r ≤ a0.val := le_refl r
  have hzb : ∀ b : Fin n, r ≤ b.val → Q (z b) = Q (z (s⁻¹ a0)) := by
    intro b hb
    have hsb : r ≤ (s b).val := Nat.not_lt.mp fun hc => absurd ((perm_lt_iff_lt s hco b).mp hc) (Nat.not_lt.mpr hb)
    have k1 := key (s b) i0 hsb hi0
    have k2 := key a0 i0 ha0 hi0
    rw [show s⁻¹ (s b) = b by simp] at k1
    exact mul_right_cancel₀ (hci i0 hi0) (k1.symm.trans k2)
  have hsi : ∀ i : Fin n, i.val < r → s i = i := by
    intro i hi
    obtain ⟨zi', hzi', hzi'c⟩ := nz_exists_inv (hzu i)
    have k := key a0 i ha0 hi
    refine hc i (s i) hi ((perm_lt_iff_lt s hco i).mpr hi) (z (s⁻¹ a0) * zi')
      (normOne_mul (hzu _) (normOne_conj (hzu i) hzi'c)) ?_
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_mul]
    have hq : Q zi' * Q (z i) = 1 := by rw [← map_mul, hzi', map_one]
    linear_combination (Q zi') * k - (Q (c (s i))) * hq
  have hzi : ∀ i : Fin n, i.val < r → Q (z i) = Q (z (s⁻¹ a0)) := by
    intro i hi
    have k := key a0 i ha0 hi
    rw [hsi i hi, mul_comm (Q (z (s⁻¹ a0)))] at k
    exact mul_left_cancel₀ (hci i hi) k
  have hQall : ∀ b : Fin n, Q (z b) = Q (z (s⁻¹ a0)) := fun b =>
    if hb : b.val < r then hzi b hb else hzb b (Nat.not_lt.mp hb)
  set Z := z (s⁻¹ a0) with hZ
  have hzall : ∀ b : Fin n, z b = Z := by
    intro b
    obtain ⟨Z', hZ', hZ'c⟩ := nz_exists_inv (hzu (s⁻¹ a0))
    have h1' : z b * Z' = 1 :=
      nz_root_one hX w1.1 hg1 hgw1 hb1 (normOne_mul (hzu b) (normOne_conj (hzu _) hZ'c))
        (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hQ, hQall b, ← map_mul, mul_comm, hZ', map_one, sub_self])
    calc z b = z b * Z' * Z := by rw [mul_assoc, hZ', mul_one]
      _ = Z := by rw [h1', one_mul]
  have hGp : ∀ (w : SG) (a b : Fin n), (Gh w).1 a b = if a = s b then Ideal.Quotient.mk w.1.asIdeal Z else 0 :=
    fun w a b => by rw [hGh, hzall]
  have hGw1 : Gh w1 = h w1 := by
    have hcm : Gh w1 * v0A _ r (fun b => Q (c b)) = v0A _ r (fun b => Q (c b)) * Gh w1 := by
      have hGm : (Gh w1).1 = Q Z • pM _ s := by
        ext a b
        rw [hGp, Matrix.smul_apply, pM_apply, smul_eq_mul]
        split_ifs <;> simp [hQ]
      apply Units.ext
      show (Gh w1).1 * (v0A _ r (fun b => Q (c b))).1 = (v0A _ r (fun b => Q (c b))).1 * (Gh w1).1
      rw [hGm]
      exact permutation_commutes_nilpotent _ s hsi _
    exact (mul_left_cancel (hA.trans hcm)).symm
  refine ⟨Z, s, hzu _, hsi, hco, fun i j => ?_, fun w i j => ?_⟩
  · rw [nz_ufGL_apply, ← hG]
    have h3 := hGz (pos⁻¹ i) (pos⁻¹ j)
    rw [show pos (pos⁻¹ i) = i by simp, show pos (pos⁻¹ j) = j by simp, hzall] at h3
    rw [h3]
    have h4 : pos⁻¹ i = s (pos⁻¹ j) ↔ i = (pos * s * pos⁻¹) j := by
      show pos⁻¹ i = s (pos⁻¹ j) ↔ i = pos (s (pos⁻¹ j))
      exact Equiv.Perm.inv_eq_iff_eq
    by_cases h5 : pos⁻¹ i = s (pos⁻¹ j)
    · rw [if_pos h5, if_pos (h4.mp h5)]
    · rw [if_neg h5, if_neg (fun hc => h5 (h4.mpr hc)), map_zero]
  · by_cases hw : w = w1
    · subst hw
      rw [← hGw1, hGp]
    · rw [← hGhw w hw, hGp]

end StabPt

section Scal

variable {E : Type} [Field E] [NumberField E]

noncomputable instance unitTorsionFintype : Fintype (NumberField.Units.torsion E) := Fintype.ofFinite _

def unitsReductionAtPlace (w : HeightOneSpectrum (𝓞 E)) : (𝓞 E)ˣ →* (𝓞 E ⧸ w.asIdeal)ˣ :=
  Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom

def diagonalUnitsHom (κ : Type) [CommRing κ] (n : ℕ) : (Fin n → κˣ) →* GL (Fin n) κ :=
  (Units.map (Matrix.diagonalRingHom (Fin n) κ).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem v0diag_val (κ : Type) [CommRing κ] (n : ℕ) (u : Fin n → κˣ) :
    ((diagonalUnitsHom κ n u : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = Matrix.diagonal fun i => ((u i : κˣ) : κ) := rfl

/- English proof (translation)
Use `mem_btG.mpr fun i j hij => ?_` and prove the remaining obligations. Rewrite using `[v0diag_val, Matrix.diagonal_apply_ne]`. Introduce and unpack `rfl`. Conclude with `lt_irrefl _ hij`.
-/
theorem v0diag_mem_btG (κ : Type) [CommRing κ] (n : ℕ) (β : ℕ → ℕ) (u : Fin n → κˣ) : diagonalUnitsHom κ n u ∈ btG n κ β := by
  refine mem_btG.mpr fun i j hij => ?_
  rw [v0diag_val, Matrix.diagonal_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

def v0Z (V : Finset (HeightOneSpectrum (𝓞 E))) (r : ℕ) : NumberField.Units.torsion E →* G0 E V r :=
  MonoidHom.pi fun w => (diagonalUnitsHom _ r).comp (MonoidHom.pi fun _ : Fin r => (unitsReductionAtPlace w.1).comp (NumberField.Units.torsion E).subtype)

open Classical in

def v0kG (n : ℕ) (SG V : Finset (HeightOneSpectrum (𝓞 E))) (r : ℕ) : NumberField.Units.torsion E →* GLG E n SG :=
  MonoidHom.pi fun w => (diagonalUnitsHom _ n).comp (MonoidHom.pi fun i : Fin n =>
    if w.1 ∈ V ∧ i.val < r then 1 else (unitsReductionAtPlace w.1).comp (NumberField.Units.torsion E).subtype)

open Classical in
/- English proof (translation)
Use `show Units.val (diagonalUnitsHom (𝓞 E ⧸ w.1.asIdeal) n _) i j = _`. Rewrite using `[v0diag_val, Matrix.diagonal_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Distinguish the cases in `hc : w.1 ∈ V ∧ i.val < r`.

Simplify using `[hc]`. Simplify using `[hc, unitsReductionAtPlace]`. Simplify using `[hij]`.
-/
theorem torsionLevelElement_apply (n : ℕ) (SG V : Finset (HeightOneSpectrum (𝓞 E))) (r : ℕ) (ζ : NumberField.Units.torsion E) (w : SG) (i j : Fin n) :
    Units.val (v0kG n SG V r ζ w) i j =
      if i = j then (if w.1 ∈ V ∧ i.val < r then 1 else Ideal.Quotient.mk w.1.asIdeal ((ζ : (𝓞 E)ˣ) : 𝓞 E)) else 0 := by
  show Units.val (diagonalUnitsHom (𝓞 E ⧸ w.1.asIdeal) n _) i j = _
  rw [v0diag_val, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    by_cases hc : w.1 ∈ V ∧ i.val < r
    · simp [hc]
    · simp [hc, unitsReductionAtPlace]
  · simp [hij]

end Scal

section Rows

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in

/- English proof (translation)
Introduce `w _`. Use `show _ ∈ (rowTyKK Ch sel mu w).H`. Distinguish the cases in `h : w.1 ∈ Pr.vGs`. Rewrite using `[rowTyKK, LevFam.glue_of_mem _ _ w h] show _ ∈ HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t)`. Use `mem_HK.mpr ⟨v0diag_mem_btG _ _ _ _, fun i i' hi hi' => ?_⟩` and prove the remaining obligations.

Rewrite using `[torsionLevelElement_apply]`. Distinguish the cases in `hij : i = i'`. Substitute `hij` using the available equality. Simplify using `[h, hi]`. Rewrite using `[if_neg hij, Matrix.one_apply_ne hij]`.

Rewrite using `[rowTyKK, LevFam.glue_of_not _ _ w h]`. Conclude with `v0diag_mem_btG _ _ _ _`.
-/
theorem torsionLevelElement_mem_X (ζ : NumberField.Units.torsion X.E) :
    v0kG (R.N R.m - 1) (rowSG Pr sel mu) Pr.vGs R.r ζ ∈ (rowTyKK Ch sel mu).inv.grp := by
  intro w _
  show _ ∈ (rowTyKK Ch sel mu w).H
  by_cases h : w.1 ∈ Pr.vGs
  · rw [rowTyKK, LevFam.glue_of_mem _ _ w h]
    show _ ∈ HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t)
    refine mem_HK.mpr ⟨v0diag_mem_btG _ _ _ _, fun i i' hi hi' => ?_⟩
    rw [torsionLevelElement_apply]
    by_cases hij : i = i'
    · subst hij
      simp [h, hi]
    · rw [if_neg hij, Matrix.one_apply_ne hij]
  · rw [rowTyKK, LevFam.glue_of_not _ _ w h]
    exact v0diag_mem_btG _ _ _ _

def v0kX : NumberField.Units.torsion X.E →* ↥(rowTyKK Ch sel mu).inv.grp :=
  (v0kG (R.N R.m - 1) (rowSG Pr sel mu) Pr.vGs R.r).codRestrict _ (torsionLevelElement_mem_X Ch sel mu)

def v0cX : NumberField.Units.torsion X.E →* X.Kˣ :=
  ∏ τ : X.Tau, (zpowGroupHom (∑ i, (W.sgTrue τ).w i)).comp
    ((Units.map (X.emb τ).toMonoidHom).comp ((Units.map (algebraMap (𝓞 X.E) X.E).toMonoidHom).comp (NumberField.Units.torsion X.E).subtype))

def torsionScalarCharacterAtBase : NumberField.Units.torsion X.E →* X.Kˣ :=
  ((rowTyKK Ch sel mu).inv.chr.comp (v0kX Ch sel mu)) * v0cX W

def RegModZX : Prop :=
  ∀ a : MonoidAlgebra X.K (G0 X.E Pr.vGs R.r),
    a * v0eZ (v0Z Pr.vGs R.r) (torsionScalarCharacterAtBase W Ch sel mu) ≠ 0 → (g0HatRepEqFunX W Ch sel mu).asAlgebraHom a ≠ 0

def InvariantSubspaceNonzeroAtBase (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  goodAt Xg P.grp P.chr * v0eZ (v0Z Pr.vGs R.r) (torsionScalarCharacterAtBase W Ch sel mu) ≠ 0 → V0X W Ch sel mu Xg P ≠ ⊥

/- English proof (translation)
Introduce `hne hbot`. Conclude with `h _ hne (LinearMap.range_eq_bot.mp hbot)`.
-/
theorem invariantSubspaceNonzeroX_of_regular (h : RegModZX W Ch sel mu) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs) :
    InvariantSubspaceNonzeroAtBase W Ch sel mu Xg P := by
  intro hne hbot
  exact h _ hne (LinearMap.range_eq_bot.mp hbot)

open Classical in

/- English proof (translation)
Introduce `w _`. Use `show _ ∈ (mtTyKK Ch sel mu j w).H`. Distinguish the cases in `h : w.1 ∈ Pr.vGs`. Rewrite using `[mtTyKK, LevFam.glue_of_mem _ _ w h] show _ ∈ HK R.nV _ R.r [R.t]`. Use `mem_HK.mpr ⟨v0diag_mem_btG _ _ _ _, fun i i' hi hi' => ?_⟩` and prove the remaining obligations.

Rewrite using `[torsionLevelElement_apply]`. Distinguish the cases in `hij : i = i'`. Substitute `hij` using the available equality. Simplify using `[h, hi]`. Rewrite using `[if_neg hij, Matrix.one_apply_ne hij]`.

Rewrite using `[mtTyKK, LevFam.glue_of_not _ _ w h]`. Conclude with `v0diag_mem_btG _ _ _ _`.
-/
theorem torsionLevelElement_mem_V (j : ℕ) (ζ : NumberField.Units.torsion X.E) :
    v0kG R.nV (rowSG Pr sel mu) Pr.vGs R.r ζ ∈ (mtTyKK Ch sel mu j).inv.grp := by
  intro w _
  show _ ∈ (mtTyKK Ch sel mu j w).H
  by_cases h : w.1 ∈ Pr.vGs
  · rw [mtTyKK, LevFam.glue_of_mem _ _ w h]
    show _ ∈ HK R.nV _ R.r [R.t]
    refine mem_HK.mpr ⟨v0diag_mem_btG _ _ _ _, fun i i' hi hi' => ?_⟩
    rw [torsionLevelElement_apply]
    by_cases hij : i = i'
    · subst hij
      simp [h, hi]
    · rw [if_neg hij, Matrix.one_apply_ne hij]
  · rw [mtTyKK, LevFam.glue_of_not _ _ w h]
    exact v0diag_mem_btG _ _ _ _

def v0kV (j : ℕ) : NumberField.Units.torsion X.E →* ↥(mtTyKK Ch sel mu j).inv.grp :=
  (v0kG R.nV (rowSG Pr sel mu) Pr.vGs R.r).codRestrict _ (torsionLevelElement_mem_V Ch sel mu j)

def v0cV (j : ℕ) : NumberField.Units.torsion X.E →* X.Kˣ :=
  ∏ τ : X.Tau, (zpowGroupHom (-∑ i, (W.lamV j τ).w i)).comp
    ((Units.map (X.emb τ).toMonoidHom).comp ((Units.map (algebraMap (𝓞 X.E) X.E).toMonoidHom).comp (NumberField.Units.torsion X.E).subtype))

def torsionScalarCharacterAtLevel (j : ℕ) : NumberField.Units.torsion X.E →* X.Kˣ :=
  ((mtTyKK Ch sel mu j).inv.chr.comp (v0kV Ch sel mu j)) * v0cV W j

def RegModZV (j : ℕ) : Prop :=
  ∀ a : MonoidAlgebra X.K (G0 X.E Pr.vGs R.r),
    a * v0eZ (v0Z Pr.vGs R.r) (torsionScalarCharacterAtLevel W Ch sel mu j) ≠ 0 → (unipotentRightActionFormsV W Ch sel mu j).asAlgebraHom a ≠ 0

def InvariantSubspaceNonzeroAtLevel (j : ℕ) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K)) (P : LevFam X.E X.K R.r Pr.vGs) : Prop :=
  goodAt Xg P.grp P.chr⁻¹ * v0eZ (v0Z Pr.vGs R.r) (torsionScalarCharacterAtLevel W Ch sel mu j) ≠ 0 → invariantSubspaceOfForms W Ch sel mu j Xg P ≠ ⊥

/- English proof (translation)
Introduce `hne hbot`. Conclude with `h _ hne (LinearMap.range_eq_bot.mp hbot)`.
-/
theorem invariantSubspaceNonzeroV_of_regular (j : ℕ) (h : RegModZV W Ch sel mu j) (Xg : Finset (G0 X.E Pr.vGs R.r → X.K))
    (P : LevFam X.E X.K R.r Pr.vGs) : InvariantSubspaceNonzeroAtLevel W Ch sel mu j Xg P := by
  intro hne hbot
  exact h _ hne (LinearMap.range_eq_bot.mp hbot)

end Rows

section ScalAct

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Take `⟨w⟩` from `(inferInstance : Nonempty (NumberField.InfinitePlace E))`. Establish `h1` using `(NumberField.Units.mem_torsion E).mp ζ.2 w`. Rewrite `h1` using `[← NumberField.InfinitePlace.norm_embedding_eq]`. Apply `w.embedding.injective` to reduce the goal to its premises. Rewrite using `[map_mul, hconj, map_one, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h1]`.

Evaluate the numerical expressions.
-/
theorem torsion_normOne (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x))
    (ζ : NumberField.Units.torsion E) :
    star ((((ζ : (𝓞 E)ˣ) : 𝓞 E)) : E) * ((((ζ : (𝓞 E)ˣ) : 𝓞 E)) : E) = 1 := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace E))
  have h1 := (NumberField.Units.mem_torsion E).mp ζ.2 w
  rw [← NumberField.InfinitePlace.norm_embedding_eq] at h1
  apply w.embedding.injective
  rw [map_mul, hconj, map_one, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h1]
  norm_num

def v0uE (ζ : NumberField.Units.torsion E) : Eˣ := Units.map (algebraMap (𝓞 E) E).toMonoidHom (ζ : (𝓞 E)ˣ)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem torsionUnit_val (ζ : NumberField.Units.torsion E) : ((v0uE ζ : Eˣ) : E) = algebraMap (𝓞 E) E ((ζ : (𝓞 E)ˣ) : 𝓞 E) := rfl

def v0sc (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ)
    (ζ : NumberField.Units.torsion E) : UF E n :=
  ⟨LinearEquiv.smulOfUnit (v0uE ζ), fun x y => by
    have hu := torsion_normOne hconj ζ
    show hStd E n ((v0uE ζ : Eˣ) • x) ((v0uE ζ : Eˣ) • y) = hStd E n x y
    rw [hStd_apply, hStd_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul, star_mul', torsionUnit_val]
    linear_combination (star (x i) * y i) * hu⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem torsionScalar_apply (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ)
    (ζ : NumberField.Units.torsion E) (x : Sp E n) :
    (v0sc hconj n ζ).1 x = algebraMap (𝓞 E) E ((ζ : (𝓞 E)ˣ) : 𝓞 E) • x := rfl

/- English proof (translation)
Apply `(v0sc hconj n ζ).1.injective` to reduce the goal to its premises. Rewrite using `[LinearEquiv.apply_symm_apply, torsionScalar_apply, ← algebraMap_smul E z' x, smul_smul, ← map_mul, mul_comm, hz', map_one, one_smul]`.
-/
theorem torsionScalar_symm_apply (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (n : ℕ)
    (ζ : NumberField.Units.torsion E) {z' : 𝓞 E} (hz' : z' * ((ζ : (𝓞 E)ˣ) : 𝓞 E) = 1) (x : Sp E n) :
    (v0sc hconj n ζ).1.symm x = z' • x := by
  apply (v0sc hconj n ζ).1.injective
  rw [LinearEquiv.apply_symm_apply, torsionScalar_apply, ← algebraMap_smul E z' x, smul_smul, ← map_mul, mul_comm, hz', map_one,
    one_smul]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[torsionLevelElement_apply, Matrix.diagonal_apply]`. Simplify using the standard rewrite rules.
-/
theorem torsionLevelElement_scalar_val (n : ℕ) (SG : Finset (HeightOneSpectrum (𝓞 E))) (ζ : NumberField.Units.torsion E) (w : SG) :
    Units.val (v0kG n SG ∅ 0 ζ w) = Matrix.diagonal fun _ => Ideal.Quotient.mk w.1.asIdeal ((ζ : (𝓞 E)ˣ) : 𝓞 E) := by
  ext i j
  rw [torsionLevelElement_apply, Matrix.diagonal_apply]
  simp

/- English proof (translation)
Take `⟨z', hz'1, -⟩` from `nz_exists_inv (torsion_normOne hconj ζ)`. Use `set z : 𝓞 E := ((ζ : (𝓞 E)ˣ) : 𝓞 E) with hz`. Establish `hzz : z * z' = 1` using `by rw [mul_comm]; exact hz'1`. Establish `hsymm` using `torsionScalar_symm_apply hconj n ζ hz'1`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show d.1.act (v0sc hconj n ζ).1 (v0kG n SG ∅ 0 ζ) = d.1`. Use `ext1`. Use `show gmap _ d.1.N = d.1.N`. Use extensionality with `x`. Rewrite using `[mem_gmap, hsymm]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `d.1.N.smul_mem z h` as an intermediate fact. Rewrite `this` using `[smul_smul, hzz, one_smul]`. Then use the resulting hypothesis. Introduce `h`.

Conclude with `d.1.N.smul_mem z' h`. Use function extensionality and compare the values at `P`. Conclude with `(Finset.notMem_empty P.1 P.2).elim`. Use function extensionality and compare the values at `w x show (v0kG n SG ∅ 0 ζ w).1.mulVec (d.1.be w ((v0sc hconj n ζ).1.symm x)) = d.1.be w x`. Rewrite using `[hsymm, torsionLevelElement_scalar_val]`.

Distinguish the cases in `hx : x ∈ d.1.at w.1`. Rewrite using `[d.2.be_smul w z' x hx]`. Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, hzz, map_one, one_mul]`. Establish `hx' : z' • x ∉ d.1.at w.1` using `fun h => hx (by`.

Use `(d.1.at w.1).smul_mem z h` as an intermediate fact. Rewrite using `[smul_smul, hzz, one_smul] at this)` and apply the resulting hypothesis. Rewrite using `[d.2.be_off w _ hx', d.2.be_off w x hx, Matrix.mulVec_zero]`.
-/
theorem torsionScalar_fixes_decoration (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) {n : ℕ}
    {SG : Finset (HeightOneSpectrum (𝓞 E))} (ζ : NumberField.Units.torsion E) (d : DecoSet E n ∅ SG) :
    ((v0sc hconj n ζ, v0kG n SG ∅ 0 ζ) : UF E n × GLG E n SG) • d = d := by
  obtain ⟨z', hz'1, -⟩ := nz_exists_inv (torsion_normOne hconj ζ)
  set z : 𝓞 E := ((ζ : (𝓞 E)ˣ) : 𝓞 E) with hz
  have hzz : z * z' = 1 := by rw [mul_comm]; exact hz'1
  have hsymm := torsionScalar_symm_apply hconj n ζ hz'1
  apply Subtype.ext
  show d.1.act (v0sc hconj n ζ).1 (v0kG n SG ∅ 0 ζ) = d.1
  ext1
  · show gmap _ d.1.N = d.1.N
    ext x
    rw [mem_gmap, hsymm]
    constructor
    · intro h
      have := d.1.N.smul_mem z h
      rwa [smul_smul, hzz, one_smul] at this
    · intro h
      exact d.1.N.smul_mem z' h
  · funext P
    exact (Finset.notMem_empty P.1 P.2).elim
  · funext w x
    show (v0kG n SG ∅ 0 ζ w).1.mulVec (d.1.be w ((v0sc hconj n ζ).1.symm x)) = d.1.be w x
    rw [hsymm, torsionLevelElement_scalar_val]
    by_cases hx : x ∈ d.1.at w.1
    · rw [d.2.be_smul w z' x hx]
      funext i
      rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← map_mul, hzz, map_one, one_mul]
    · have hx' : z' • x ∉ d.1.at w.1 := fun h => hx (by
        have := (d.1.at w.1).smul_mem z h
        rwa [smul_smul, hzz, one_smul] at this)
      rw [d.2.be_off w _ hx', d.2.be_off w x hx, Matrix.mulVec_zero]

end ScalAct

section RhoScal

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
Establish `key : ∀ S : Finset ι, rhoK lam (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) = (∏ τ ∈ S, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam))`. Introduce `S`. Use `Finset.induction_on S ?_ (fun a S ha ih => ?_)` and prove the remaining obligations. Establish `h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then (brpSc K (t τ) : GL (Fin n) K) else 1) = 1`. Use function extensionality and compare the values at `τ`.

Simplify using the standard rewrite rules. Rewrite using `[h0, map_one, Finset.prod_empty, one_smul]`. Establish `h0 : (fun τ => if τ ∈ insert a S then (brpSc K (t τ) : GL (Fin n) K) else 1) = Pi.mulSingle a (brpSc K (t a) : GL (Fin n) K) * (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1)`. Use function extensionality and compare the values at `τ`. Distinguish the cases in `hτ : τ = a`.

Substitute `hτ` using the available equality. Simplify using `[ha]`. Establish `h1 : τ ∈ insert a S ↔ τ ∈ S` using `by simp [hτ]`. Simplify using `only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hτ, one_mul]`. Distinguish the cases in `h2 : τ ∈ S`.

Rewrite using `[if_pos (h1.mpr h2), if_pos h2]`. Rewrite using `[if_neg (fun h => h2 (h1.mp h)), if_neg h2]`. Rewrite using `[h0, map_mul, ih, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.rhoK_single_scalar, Finset.prod_insert ha, smul_mul_smul, one_mul]`. Both sides reduce to the same expression. Establish `h` using `key Finset.univ`.

Simplify using `only [Finset.mem_univ, if_true] at h`. Conclude with `h`.
-/
theorem tensorWeights_scalar_action (lam : ι → DomWeight n) (t : ι → Kˣ) :
    rhoK lam (fun τ => (brpSc K (t τ) : GL (Fin n) K)) =
      (∏ τ, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
  classical
  have key : ∀ S : Finset ι, rhoK lam (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
      (∏ τ ∈ S, ((t τ : K) ^ (∑ i, (lam τ).w i))) • (1 : Module.End K (VV K lam)) := by
    intro S
    refine Finset.induction_on S ?_ (fun a S ha ih => ?_)
    · have h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then (brpSc K (t τ) : GL (Fin n) K) else 1) = 1 := by
        funext τ
        simp
      rw [h0, map_one, Finset.prod_empty, one_smul]
    · have h0 : (fun τ => if τ ∈ insert a S then (brpSc K (t τ) : GL (Fin n) K) else 1) =
          Pi.mulSingle a (brpSc K (t a) : GL (Fin n) K) * (fun τ => if τ ∈ S then (brpSc K (t τ) : GL (Fin n) K) else 1) := by
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · have h1 : τ ∈ insert a S ↔ τ ∈ S := by simp [hτ]
          simp only [Pi.mul_apply, Pi.mulSingle_eq_of_ne hτ, one_mul]
          by_cases h2 : τ ∈ S
          · rw [if_pos (h1.mpr h2), if_pos h2]
          · rw [if_neg (fun h => h2 (h1.mp h)), if_neg h2]
      rw [h0, map_mul, ih, Formalism.L2.GlobalTheoryTheory.TraceIntegrality.rhoK_single_scalar, Finset.prod_insert ha, smul_mul_smul, one_mul]
      rfl
  have h := key Finset.univ
  simp only [Finset.mem_univ, if_true] at h
  exact h

end RhoScal

section RhoScal2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} [NeZero n]

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Use `show (RingHom.mapMatrix (emb τ) ((ufGL E n (v0sc hconj n ζ) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) i j = _`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, nz_ufGL_apply, torsionScalar_apply, brpSc_coe]`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[torsionUnit_val]`. Simplify using `[hij]`.
-/
theorem embeddedGL_torsionScalar (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (emb : ι → (E →+* K))
    (ζ : NumberField.Units.torsion E) :
    embGL emb (ufGL E n (v0sc hconj n ζ)) = fun τ => brpSc K (Units.map (emb τ).toMonoidHom (v0uE ζ)) := by
  funext τ
  apply Units.ext
  ext i j
  show (RingHom.mapMatrix (emb τ) ((ufGL E n (v0sc hconj n ζ) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) i j = _
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, nz_ufGL_apply, torsionScalar_apply, brpSc_coe]
  by_cases hij : i = j
  · subst hij
    simp [torsionUnit_val]
  · simp [hij]

omit [NeZero n] in
/- English proof (translation)
Use function extensionality and compare the values at `τ`. Apply `Units.ext` to reduce the goal to its premises. Use `show ((((brpSc K (t τ))⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).transpose = _`. Establish `e : (brpSc K (t τ))⁻¹ = (brpSc K (t τ)⁻¹ : GL (Fin n) K)`. Unfold `brpSc`.

Rewrite using `[map_inv]`. Rewrite using `[e, brpSc_coe, Matrix.transpose_smul, Matrix.transpose_one]`.
-/
theorem inverseTranspose_scalars (t : ι → Kˣ) :
    invTrK (fun τ => (brpSc K (t τ) : GL (Fin n) K)) = fun τ => (brpSc K (t τ)⁻¹ : GL (Fin n) K) := by
  funext τ
  apply Units.ext
  show ((((brpSc K (t τ))⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K).transpose = _
  have e : (brpSc K (t τ))⁻¹ = (brpSc K (t τ)⁻¹ : GL (Fin n) K) := by
    unfold brpSc
    rw [map_inv]
  rw [e, brpSc_coe, Matrix.transpose_smul, Matrix.transpose_one]

end RhoScal2

section RowsScal

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

/- English proof (translation)
Use `show Units.val (diagonalUnitsHom (𝓞 X.E ⧸ w.1.asIdeal) r _) = _`. Rewrite using `[v0diag_val]`. Both sides reduce to the same expression.
-/
theorem torsionCenter_val (V : Finset (HeightOneSpectrum (𝓞 X.E))) (r : ℕ) (ζ : NumberField.Units.torsion X.E) (w : V) :
    Units.val (v0Z V r ζ w) = Matrix.diagonal fun _ => Ideal.Quotient.mk w.1.asIdeal ((ζ : (𝓞 X.E)ˣ) : 𝓞 X.E) := by
  show Units.val (diagonalUnitsHom (𝓞 X.E ⧸ w.1.asIdeal) r _) = _
  rw [v0diag_val]
  rfl

open Classical in
/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[torsionLevelElement_apply, Matrix.diagonal_apply]`.
-/
theorem torsionLevelElement_diagonal (n : ℕ) (SG V : Finset (HeightOneSpectrum (𝓞 X.E))) (r : ℕ) (ζ : NumberField.Units.torsion X.E) (w : SG) :
    Units.val (v0kG n SG V r ζ w) =
      Matrix.diagonal fun i : Fin n => if w.1 ∈ V ∧ i.val < r then 1 else Ideal.Quotient.mk w.1.asIdeal ((ζ : (𝓞 X.E)ˣ) : 𝓞 X.E) := by
  ext i j
  rw [torsionLevelElement_apply, Matrix.diagonal_apply]

/- English proof (translation)
Use extensionality with `i j`. Distinguish the cases in `hi : i.val < r`. Distinguish the cases in `hj : j.val < r`. Rewrite using `[diagMat_of_lt _ hi hj, Matrix.diagonal_apply, Matrix.diagonal_apply]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `[hi]`. Rewrite using `[if_neg (fun e => hij (Fin.ext (by simpa using congrArg Fin.val e))), if_neg hij]`. Establish `hne : i ≠ j` using `fun e => hj (by rw [← e]; exact hi)`. Rewrite using `[diagMat_of_not_right _ _ hj, Matrix.diagonal_apply, Matrix.one_apply_ne hne, if_neg hne]`.

Rewrite using `[diagMat_of_not_left _ _ hi, Matrix.diagonal_apply, Matrix.one_apply]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[hi]`. Simplify using `[hij]`.
-/
theorem diagonalBlock_scalar {κ : Type} [CommRing κ] {r n : ℕ} (x : κ) :
    diagMat r n (Matrix.diagonal fun _ : Fin r => x) = Matrix.diagonal fun i : Fin n => if i.val < r then x else 1 := by
  ext i j
  by_cases hi : i.val < r
  · by_cases hj : j.val < r
    · rw [diagMat_of_lt _ hi hj, Matrix.diagonal_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp [hi]
      · rw [if_neg (fun e => hij (Fin.ext (by simpa using congrArg Fin.val e))), if_neg hij]
    · have hne : i ≠ j := fun e => hj (by rw [← e]; exact hi)
      rw [diagMat_of_not_right _ _ hj, Matrix.diagonal_apply, Matrix.one_apply_ne hne, if_neg hne]
  · rw [diagMat_of_not_left _ _ hi, Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [hi]
    · simp [hij]

open Classical in

/- English proof (translation)
Use function extensionality and compare the values at `w`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Pi.mul_apply, Units.val_mul, torsionLevelElement_diagonal, torsionLevelElement_diagonal]`. Distinguish the cases in `hw : w.1 ∈ Pr.vGs`. Establish `e : unipotentGroupBlockEmbedding Pr sel mu h (v0Z Pr.vGs R.r ζ) w = diagEmb _ h (v0Z Pr.vGs R.r ζ ⟨w.1, hw⟩)` using `extGLG_of_mem _ w hw`.

Rewrite using `[e, diagEmb_val, torsionCenter_val, diagonalBlock_scalar, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i.val < R.r`. Simplify using `[hi, hw]`.

Simplify using `[hi]`. Establish `e : unipotentGroupBlockEmbedding Pr sel mu h (v0Z Pr.vGs R.r ζ) w = 1` using `extGLG_of_not _ w hw`. Rewrite using `[e, Units.val_one, one_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Simplify using `[hw]`.
-/
theorem unipotentHat_mul_torsionLevel {n : ℕ} (h : R.r ≤ n) (ζ : NumberField.Units.torsion X.E) :
    unipotentGroupBlockEmbedding Pr sel mu h (v0Z Pr.vGs R.r ζ) * v0kG n (rowSG Pr sel mu) Pr.vGs R.r ζ = v0kG n (rowSG Pr sel mu) ∅ 0 ζ := by
  funext w
  apply Units.ext
  rw [Pi.mul_apply, Units.val_mul, torsionLevelElement_diagonal, torsionLevelElement_diagonal]
  by_cases hw : w.1 ∈ Pr.vGs
  · have e : unipotentGroupBlockEmbedding Pr sel mu h (v0Z Pr.vGs R.r ζ) w = diagEmb _ h (v0Z Pr.vGs R.r ζ ⟨w.1, hw⟩) := extGLG_of_mem _ w hw
    rw [e, diagEmb_val, torsionCenter_val, diagonalBlock_scalar, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hi : i.val < R.r
    · simp [hi, hw]
    · simp [hi]
  · have e : unipotentGroupBlockEmbedding Pr sel mu h (v0Z Pr.vGs R.r ζ) w = 1 := extGLG_of_not _ w hw
    rw [e, Units.val_one, one_mul]
    congr 1
    funext i
    simp [hw]

/- English proof (translation)
Establish `: NeZero (R.N R.m - 1)` using `⟨(X'_pos R).ne'⟩`. Use `show rhoK W.sgTrue (embGL X.emb (ufGL X.E _ (v0sc hX.conjE (R.N R.m - 1) ζ))) = _`. Rewrite using `[embeddedGL_torsionScalar, tensorWeights_scalar_action, v0cX, MonoidHom.finsetProd_apply, Units.coe_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Simplify using `only [MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val]`. Both sides reduce to the same expression.
-/
theorem torsion_scalar_acts_X (hX : X.Ok) (ζ : NumberField.Units.torsion X.E) :
    (rowVal W (rowSG Pr sel mu)).rho (v0sc hX.conjE (R.N R.m - 1) ζ) = ((v0cX W ζ : X.Kˣ) : X.K) • 1 := by
  have : NeZero (R.N R.m - 1) := ⟨(X'_pos R).ne'⟩
  show rhoK W.sgTrue (embGL X.emb (ufGL X.E _ (v0sc hX.conjE (R.N R.m - 1) ζ))) = _
  rw [embeddedGL_torsionScalar, tensorWeights_scalar_action, v0cX, MonoidHom.finsetProd_apply, Units.coe_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val]
  rfl

/- English proof (translation)
Establish `: NeZero R.nV` using `⟨(nV_pos R).ne'⟩`. Use `show rhoK (W.lamV j) (invTrK (embGL X.emb (ufGL X.E _ (v0sc hX.conjE R.nV ζ)))) = _`. Rewrite using `[embeddedGL_torsionScalar, inverseTranspose_scalars, tensorWeights_scalar_action, v0cV, MonoidHom.finsetProd_apply, Units.coe_prod]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Simplify using `only [MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, inv_zpow', zpow_neg]`. Both sides reduce to the same expression.
-/
theorem torsion_scalar_acts_V (hX : X.Ok) (j : ℕ) (ζ : NumberField.Units.torsion X.E) :
    (mtVal W j (rowSG Pr sel mu)).rho (v0sc hX.conjE R.nV ζ) = ((v0cV W j ζ : X.Kˣ) : X.K) • 1 := by
  have : NeZero R.nV := ⟨(nV_pos R).ne'⟩
  show rhoK (W.lamV j) (invTrK (embGL X.emb (ufGL X.E _ (v0sc hX.conjE R.nV ζ)))) = _
  rw [embeddedGL_torsionScalar, inverseTranspose_scalars, tensorWeights_scalar_action, v0cV, MonoidHom.finsetProd_apply, Units.coe_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  simp only [MonoidHom.comp_apply, zpowGroupHom_apply, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, inv_zpow',
    zpow_neg]
  rfl

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `d`. Establish `hk` using `unipotentHat_mul_torsionLevel (Pr := Pr) sel mu (r_le_X' R) ζ`. Establish `e1 : (((1 : UF X.E (R.N R.m - 1)), (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) (v0Z Pr.vGs R.r ζ))⁻¹) : UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) = (v0sc hX.conjE _ ζ, v0kG (R.N R.m - 1) (rowSG Pr sel mu) Pr.vGs R.r ζ) * (v0sc hX.conjE _ ζ, v0kG (R.N …`. Rewrite using `[← hk]`.

Apply the tactic sequence `ext <;> simp [mul_inv_rev]`. Establish `hfx` using `torsionScalar_fixes_decoration hX.conjE ζ d`. Establish `h2` using `φ.2 ((v0sc hX.conjE _ ζ, v0kX Ch sel mu ζ) : (mtildeKGSD W Ch sel mu).G) d`. Use `show φ.1 (((1 : UF X.E (R.N R.m - 1)), (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) (v0Z Pr.vGs R.r ζ))⁻¹) • d) = _`. Rewrite using `[e1, mul_smul, inv_smul_eq_iff.mpr hfx.symm]`.

Use `h2.trans ?_` and prove the remaining obligations. Use `show (((rowTyKK Ch sel mu).inv.chr (v0kX Ch sel mu ζ) : X.Kˣ) : X.K) • (rowVal W (rowSG Pr sel mu)).rho (v0sc hX.conjE _ ζ) (φ.1 d) = _`. Rewrite using `[torsion_scalar_acts_X W sel mu hX ζ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, Submodule.coe_smul, Pi.smul_apply]`. Use `congr 1`.
-/
theorem torsionCenter_scalar_X (hX : X.Ok) (ζ : NumberField.Units.torsion X.E) (φ : (mtildeKGSD W Ch sel mu).EqFun) :
    g0HatRepEqFunX W Ch sel mu (v0Z Pr.vGs R.r ζ) φ = ((torsionScalarCharacterAtBase W Ch sel mu ζ : X.Kˣ) : X.K) • φ := by
  apply Subtype.ext
  funext d
  have hk := unipotentHat_mul_torsionLevel (Pr := Pr) sel mu (r_le_X' R) ζ
  have e1 : (((1 : UF X.E (R.N R.m - 1)), (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) (v0Z Pr.vGs R.r ζ))⁻¹) :
      UF X.E (R.N R.m - 1) × GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) =
      (v0sc hX.conjE _ ζ, v0kG (R.N R.m - 1) (rowSG Pr sel mu) Pr.vGs R.r ζ) *
        (v0sc hX.conjE _ ζ, v0kG (R.N R.m - 1) (rowSG Pr sel mu) ∅ 0 ζ)⁻¹ := by
    rw [← hk]
    ext <;> simp [mul_inv_rev]
  have hfx := torsionScalar_fixes_decoration hX.conjE ζ d
  have h2 := φ.2 ((v0sc hX.conjE _ ζ, v0kX Ch sel mu ζ) : (mtildeKGSD W Ch sel mu).G) d
  show φ.1 (((1 : UF X.E (R.N R.m - 1)), (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) (v0Z Pr.vGs R.r ζ))⁻¹) • d) = _
  rw [e1, mul_smul, inv_smul_eq_iff.mpr hfx.symm]
  refine h2.trans ?_
  show (((rowTyKK Ch sel mu).inv.chr (v0kX Ch sel mu ζ) : X.Kˣ) : X.K) •
    (rowVal W (rowSG Pr sel mu)).rho (v0sc hX.conjE _ ζ) (φ.1 d) = _
  rw [torsion_scalar_acts_X W sel mu hX ζ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, Submodule.coe_smul, Pi.smul_apply]
  congr 1

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `d`. Establish `hk` using `unipotentHat_mul_torsionLevel (Pr := Pr) sel mu (r_le_nV R) ζ`. Establish `e1 : (((1 : UF X.E R.nV), (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) (v0Z Pr.vGs R.r ζ))⁻¹) : UF X.E R.nV × GLG X.E R.nV (rowSG Pr sel mu)) = (v0sc hX.conjE _ ζ, v0kG R.nV (rowSG Pr sel mu) Pr.vGs R.r ζ) * (v0sc hX.conjE _ ζ, v0kG R.nV (rowSG Pr sel mu) ∅ 0 ζ)⁻¹`. Rewrite using `[← hk]`.

Apply the tactic sequence `ext <;> simp [mul_inv_rev]`. Establish `hfx` using `torsionScalar_fixes_decoration hX.conjE ζ d`. Establish `h2` using `φ.2 ((v0sc hX.conjE _ ζ, v0kV Ch sel mu j ζ) : (mtKGSD W Ch sel mu j).G) d`. Use `show φ.1 (((1 : UF X.E R.nV), (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) (v0Z Pr.vGs R.r ζ))⁻¹) • d) = _`. Rewrite using `[e1, mul_smul, inv_smul_eq_iff.mpr hfx.symm]`.

Use `h2.trans ?_` and prove the remaining obligations. Use `show (((mtTyKK Ch sel mu j).inv.chr (v0kV Ch sel mu j ζ) : X.Kˣ) : X.K) • (mtVal W j (rowSG Pr sel mu)).rho (v0sc hX.conjE _ ζ) (φ.1 d) = _`. Rewrite using `[torsion_scalar_acts_V W sel mu hX j ζ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, Submodule.coe_smul, Pi.smul_apply]`. Use `congr 1`.
-/
theorem torsionCenter_scalar_V (hX : X.Ok) (j : ℕ) (ζ : NumberField.Units.torsion X.E) (φ : (mtKGSD W Ch sel mu j).EqFun) :
    unipotentRightActionFormsV W Ch sel mu j (v0Z Pr.vGs R.r ζ) φ = ((torsionScalarCharacterAtLevel W Ch sel mu j ζ : X.Kˣ) : X.K) • φ := by
  apply Subtype.ext
  funext d
  have hk := unipotentHat_mul_torsionLevel (Pr := Pr) sel mu (r_le_nV R) ζ
  have e1 : (((1 : UF X.E R.nV), (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) (v0Z Pr.vGs R.r ζ))⁻¹) :
      UF X.E R.nV × GLG X.E R.nV (rowSG Pr sel mu)) =
      (v0sc hX.conjE _ ζ, v0kG R.nV (rowSG Pr sel mu) Pr.vGs R.r ζ) *
        (v0sc hX.conjE _ ζ, v0kG R.nV (rowSG Pr sel mu) ∅ 0 ζ)⁻¹ := by
    rw [← hk]
    ext <;> simp [mul_inv_rev]
  have hfx := torsionScalar_fixes_decoration hX.conjE ζ d
  have h2 := φ.2 ((v0sc hX.conjE _ ζ, v0kV Ch sel mu j ζ) : (mtKGSD W Ch sel mu j).G) d
  show φ.1 (((1 : UF X.E R.nV), (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) (v0Z Pr.vGs R.r ζ))⁻¹) • d) = _
  rw [e1, mul_smul, inv_smul_eq_iff.mpr hfx.symm]
  refine h2.trans ?_
  show (((mtTyKK Ch sel mu j).inv.chr (v0kV Ch sel mu j ζ) : X.Kˣ) : X.K) •
    (mtVal W j (rowSG Pr sel mu)).rho (v0sc hX.conjE _ ζ) (φ.1 d) = _
  rw [torsion_scalar_acts_V W sel mu hX j ζ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, Submodule.coe_smul, Pi.smul_apply]
  congr 1

end RowsScal

section LamKEv

/- English proof (translation)
Establish `hm : permGL κ s ∈ HK n κ r bl`. Use `mem_HK.mpr ⟨nz_pM_bt κ s hco, fun i j hi _ => ?_⟩` and prove the remaining obligations. Rewrite using `[permGL_val, pM_apply, Matrix.one_apply, hfix j ‹_›]`. Rewrite using `[Lev.ev_of_mem _ hm]`. Use `show detChar χ n r bl ⟨permGL κ s, HK_le_blockUT n κ r bl hm⟩ = 1`.

Rewrite using `[detChar_apply]`. Use `Finset.prod_eq_one fun c _ => ?_` and prove the remaining obligations. Take `⟨ε, hε⟩` from `nz_blkDet (β := coarse r bl) s hco (c + 1)`. Rewrite using `[hε κ, hχ]`.
-/
theorem levelCharacter_permutation_eq_one {κ K : Type} [CommRing κ] [Field K] {n r : ℕ} (bl : List ℕ) (χ : ℕ → κˣ →* Kˣ)
    (s : Equiv.Perm (Fin n)) (hfix : ∀ b : Fin n, b.val < r → s b = b)
    (hco : ∀ b : Fin n, coarse r bl (s b).val = coarse r bl b.val) (hχ : ∀ (c : ℕ) (ε : ℤˣ), χ c (sgnU κ ε) = 1) :
    (⟨HK n κ r bl, lamK χ n r bl⟩ : Lev κ K n).ev (permGL κ s) = 1 := by
  have hm : permGL κ s ∈ HK n κ r bl := by
    refine mem_HK.mpr ⟨nz_pM_bt κ s hco, fun i j hi _ => ?_⟩
    rw [permGL_val, pM_apply, Matrix.one_apply, hfix j ‹_›]
  rw [Lev.ev_of_mem _ hm]
  show detChar χ n r bl ⟨permGL κ s, HK_le_blockUT n κ r bl hm⟩ = 1
  rw [detChar_apply]
  refine Finset.prod_eq_one fun c _ => ?_
  obtain ⟨ε, hε⟩ := nz_blkDet (β := coarse r bl) s hco (c + 1)
  rw [hε κ, hχ]

end LamKEv

section RowsMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in
/- English proof (translation)
Take `⟨ε, hε⟩` from `nz_lamQ_ev (K := X.K) (a := R.r) (b := R.m * R.t) (le_of_eq (rank_X'_eq R)) s hfix`. Establish `key : ∀ w : rowSG Pr sel mu, ((rowTyKK Ch sel mu).inv w).ev (h.1 w) = if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε)`. Introduce `w`. Rewrite using `[hh w]`. Use `show ((rowTyKK Ch sel mu w).inv).ev _ = _`.

Rewrite using `[Lev.inv_ev]`. Distinguish the cases in `hw : w.1 ∈ Pr.vGs`. Rewrite using `[if_pos hw, rowTyKK, LevFam.glue_of_mem _ _ w hw] show ((⟨HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t), lamK (chiAt Ch ⟨w.1, hw⟩) (R.N R.m - 1) R.r (List.replicate R.m R.t)⟩ : Lev _ X.K _).ev _)⁻¹ = 1`. Rewrite using `[levelCharacter_permutation_eq_one _ _ s hfix hco (nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩), inv_one]`. Rewrite using `[if_neg hw, rowTyKK, LevFam.glue_of_not _ _ w hw] show (((⟨HQ _ _ R.r (R.m * R.t), lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r (R.m * R.t)⟩ : Lev _ X.K _).inv).ev _)⁻¹ = _`.

Rewrite using `[Lev.inv_ev, inv_inv, hε]`. Rewrite using `[LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w]`. Conclude with `hξ.prod ε`.
-/
theorem character_permutation_X_trivial (hPr : Pr.Ok) (hCh : Ch.Ok) (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (s : Equiv.Perm (Fin (R.N R.m - 1)))
    (hfix : ∀ b : Fin (R.N R.m - 1), b.val < R.r → s b = b)
    (hco : ∀ b : Fin (R.N R.m - 1), coarse R.r (List.replicate R.m R.t) (s b).val = coarse R.r (List.replicate R.m R.t) b.val)
    (h : ↥(rowTyKK Ch sel mu).inv.grp) (hh : ∀ w, h.1 w = permGL _ s) : (rowTyKK Ch sel mu).inv.chr h = 1 := by
  obtain ⟨ε, hε⟩ := nz_lamQ_ev (K := X.K) (a := R.r) (b := R.m * R.t) (le_of_eq (rank_X'_eq R)) s hfix
  have key : ∀ w : rowSG Pr sel mu, ((rowTyKK Ch sel mu).inv w).ev (h.1 w) =
      if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε) := by
    intro w
    rw [hh w]
    show ((rowTyKK Ch sel mu w).inv).ev _ = _
    rw [Lev.inv_ev]
    by_cases hw : w.1 ∈ Pr.vGs
    · rw [if_pos hw, rowTyKK, LevFam.glue_of_mem _ _ w hw]
      show ((⟨HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t),
        lamK (chiAt Ch ⟨w.1, hw⟩) (R.N R.m - 1) R.r (List.replicate R.m R.t)⟩ : Lev _ X.K _).ev _)⁻¹ = 1
      rw [levelCharacter_permutation_eq_one _ _ s hfix hco (nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩), inv_one]
    · rw [if_neg hw, rowTyKK, LevFam.glue_of_not _ _ w hw]
      show (((⟨HQ _ _ R.r (R.m * R.t), lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r (R.m * R.t)⟩ :
        Lev _ X.K _).inv).ev _)⁻¹ = _
      rw [Lev.inv_ev, inv_inv, hε]
  rw [LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w]
  exact hξ.prod ε

open Classical in
/- English proof (translation)
Establish `hm : h.1 w ∈ ((rowTyKK Ch sel mu).inv w).H` using `(rowTyKK Ch sel mu).inv.mem_at h w`. Establish `e : ((rowTyKK Ch sel mu).inv w).H = HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t)` using `by show (rowTyKK Ch sel mu w).H = _`. Rewrite using `[rowTyKK, LevFam.glue_of_mem _ _ w hw]`. Both sides reduce to the same expression. Rewrite `hm` using `[e]`.

Conclude with `hm`.
-/
theorem levelGroup_X_block (h : ↥(rowTyKK Ch sel mu).inv.grp) (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) :
    h.1 w ∈ HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t) := by
  have hm : h.1 w ∈ ((rowTyKK Ch sel mu).inv w).H := (rowTyKK Ch sel mu).inv.mem_at h w
  have e : ((rowTyKK Ch sel mu).inv w).H = HK (R.N R.m - 1) _ R.r (List.replicate R.m R.t) := by
    show (rowTyKK Ch sel mu w).H = _
    rw [rowTyKK, LevFam.glue_of_mem _ _ w hw]
    rfl
  rw [e] at hm
  exact hm

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [restr, Matrix.submatrix_apply]`. Rewrite using `[(mem_HK.mp hM).2 _ _ a.2 b.2]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne (fun e => hab (Fin.castLE_injective hrn e)), Matrix.one_apply_ne hab]`.
-/
theorem restrict_eq_one_of_mem_blockLevel {κ : Type} [CommRing κ] {n r : ℕ} (hrn : r ≤ n) (bl : List ℕ) {M : GL (Fin n) κ} (hM : M ∈ HK n κ r bl) :
    restr hrn (M : Matrix (Fin n) (Fin n) κ) = 1 := by
  ext a b
  simp only [restr, Matrix.submatrix_apply]
  rw [(mem_HK.mp hM).2 _ _ a.2 b.2]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.one_apply_ne (fun e => hab (Fin.castLE_injective hrn e)), Matrix.one_apply_ne hab]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [restr, Matrix.submatrix_apply]`. Rewrite using `[diagMat_of_lt _ (show (Fin.castLE hrn a).val < r from a.2) (show (Fin.castLE hrn b).val < r from b.2)]`. Both sides reduce to the same expression.
-/
theorem restrict_diagonalBlock {κ : Type} [CommRing κ] {n r : ℕ} (hrn : r ≤ n) (g : Matrix (Fin r) (Fin r) κ) :
    restr hrn (diagMat r n g) = g := by
  ext a b
  simp only [restr, Matrix.submatrix_apply]
  rw [diagMat_of_lt _ (show (Fin.castLE hrn a).val < r from a.2) (show (Fin.castLE hrn b).val < r from b.2)]
  rfl

open Classical in

/- English proof (translation)
Establish `: NeZero (R.N R.m - 1)` using `⟨(X'_pos R).ne'⟩`. Take `⟨w1, h1, c, hc0, hc⟩` from `hlam`. Choose the witnesses or unpack the hypotheses as in `⟨w2, h2⟩ : (Pr.vG 1).Nonempty := by`. Rewrite using `[← Finset.card_pos, hPr.vG_card]`. Conclude with `hX.f_pos`.

Establish `hne : w2 ≠ w1` using `fun h => hPr.g_ne (by rw [← hPr.vG_norm 0 w1 h1, ← hPr.vG_norm 1 w2 h2, h])`. Establish `m1 : w1 ∈ Pr.vGs` using `Finset.mem_union_left _ h1`. Establish `m2 : w2 ∈ Pr.vGs` using `Finset.mem_union_right _ h2`. Set `W1 : rowSG Pr sel mu` to `⟨w1, Finset.mem_union_left _ m1⟩`. Set `W2 : rowSG Pr sel mu` to `⟨w2, Finset.mem_union_left _ m2⟩`.

Establish `hW12 : W2 ≠ W1` using `fun h => hne (congrArg Subtype.val h)`. Establish `hr : 0 < R.r` using `nz_r_pos R`. Establish `hn : R.r < R.N R.m - 1`. Rewrite using `[rank_X'_eq R]`. Use `Nat.mul_pos (by have := R.two_le_m; omega : 0 < R.m) (nz_t_pos R)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Set `cF : Fin (R.N R.m - 1) → 𝓞 X.E` to `fun b => c b.val`. Set `bl` to `List.replicate R.m R.t`. Establish `hstab` using `fun (γ : UF X.E (R.N R.m - 1)) (g : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu)) (hg2 : g W2 ∈ blockUT _ _ R.r bl) (hg1 : g W1 ∈ blockUT _ _ R.r bl) e => stabilizer_eq_scalar_mul_permMatrix hX (posX R) bl hr hn cF W1 W2 hW12 (fun i hi => hc0 i.val hi) (fun i i' hi hi' z hz hm => Fin. …`. Establish `hinj : Function.Injective (v0Z (E` using `X.E) Pr.vGs R.r) := by`.

Rewrite using `[injective_iff_map_eq_one]`. Introduce `ζ hζ`. Establish `e` using `congrArg (fun g : G0 X.E Pr.vGs R.r => Units.val (g ⟨w1, m1⟩) ⟨0, hr⟩ ⟨0, hr⟩) hζ`. Simplify using `only at e`. Rewrite `e` using `[torsionCenter_val, Matrix.diagonal_apply_eq, Pi.one_apply, Units.val_one, Matrix.one_apply_eq]`.

Establish `h1'` using `nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) (torsion_normOne hX.conjE ζ) (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self])`. Conclude with `Subtype.ext (Units.ext h1')`. Introduce `a ha`. Use `trRep_asAlgebraHom_ne_zero_of_mul_v0eZ_ne_zero (rowVal W (rowSG Pr sel mu)) (rowTyKK Ch sel mu).inv (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R)) (rowTyKK_inv_normBy_g0Hat Ch sel mu) (v0Z Pr.vGs R.r) (torsionScalarCharacterAtBase W Ch sel mu) hinj (torsionCenter_scalar_X W …` and prove the remaining obligations. Introduce `γ h e`.

Take `⟨z, s, hz, hsfix, hco, hγ, hhw⟩` from `hstab γ h.1 (HK_le_blockUT _ _ _ _ (levelGroup_X_block Ch sel mu h W2 m2)) (HK_le_blockUT _ _ _ _ (levelGroup_X_block Ch sel mu h W1 m1)) e`. Establish `hz1 : z = 1`. Establish `h0` using `(mem_HK.mp (levelGroup_X_block Ch sel mu h W1 m1)).2 ⟨0, lt_trans hr hn⟩ ⟨0, lt_trans hr hn⟩ hr hr`. Rewrite `h0` using `[hhw, if_pos (hsfix _ hr).symm, Matrix.one_apply_eq]`. Conclude with `nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) hz (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h0, map_one, sub_self])`.

Substitute `hz1` using the available equality. Establish `hγ' : ufGL X.E _ γ = permGL X.E (posX R * s * (posX R)⁻¹)`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[hγ, permGL_val, pM_apply, map_one]`.

Establish `hh' : ∀ w, h.1 w = permGL _ s` using `fun w => by`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[hhw, permGL_val, pM_apply, map_one]`. Rewrite using `[character_permutation_X_trivial Ch sel mu hPr hCh hξ s hsfix hco h hh', Units.val_one, one_smul]`.

Use `show rhoV X.emb W.sgTrue (ufGL X.E _ γ) (nzExt X.K W.sgTrue) = _`. Rewrite using `[hγ']`. Establish `hx : ∀ x, (posX R * s * (posX R)⁻¹) x = posX R (s ((posX R)⁻¹ x))` using `fun _ => rfl`. Establish `hx' : ∀ x, posX R ((posX R)⁻¹ x) = x` using `fun x => by simp`. Apply `nz_rhoV_perm` to reduce the goal to its premises.

Introduce `τ x`. Rewrite using `[hx]`. Distinguish the cases in `hb : ((posX R)⁻¹ x).val < R.r`. Rewrite using `[hsfix _ hb, hx']`. Rewrite using `[nz_sg_const hW τ _ _ ((nz_ge_of_fix s hsfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb) (hco _), hx']`.

Introduce `x hne'`. Rewrite `hne'` using `[hx]`. Establish `hb : ¬ ((posX R)⁻¹ x).val < R.r` using `fun hb => hne' (by rw [hsfix _ hb, hx'])`. Use `hpar _ (Nat.not_lt.mp hb)` as an intermediate fact. Rewrite `this` using `[hx']`. Then use the resulting hypothesis.

Introduce `γ h t e`. Establish `hD : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs), unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t w = diagEmb _ (r_le_X' R) (t ⟨w.1, hw⟩)` using `fun w hw => extGLG_of_mem _ w hw`. Establish `hgb : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs), (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t) w ∈ blockUT _ _ R.r bl`. Introduce `w hw`. Rewrite using `[Pi.mul_apply, hD w hw]`.

Conclude with `Subgroup.mul_mem _ (HK_le_blockUT _ _ _ _ (levelGroup_X_block Ch sel mu h w hw)) (diagEmb_mem_blockUT _ _ _)`. Take `⟨z, s, hz, hsfix, -, -, hhw⟩` from `hstab γ (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t) (hgb W2 m2) (hgb W1 m1) e`. Take `⟨ζ, hζ⟩` from `normOne_integer_is_torsion hX.conjE hz`. Use `⟨ζ, funext fun w => ?_⟩` and prove the remaining obligations. Set `W' : rowSG Pr sel mu` to `⟨w.1, Finset.mem_union_left _ w.2⟩`.

Establish `e2 : restr (r_le_X' R) (Units.val ((h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t) W')) = Units.val (t w)`. Rewrite using `[Pi.mul_apply, hD W' w.2, Units.val_mul, restr_mul (r_le_X' R) bl _ (diagEmb_mem_blockUT (r_le_X' R) bl (t ⟨w.1, w.2⟩)), restrict_eq_one_of_mem_blockLevel (r_le_X' R) bl (levelGroup_X_block Ch sel mu h W' w.2), one_mul, diagEmb_val, restrict_diagonalBlock]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Rewrite using `[torsionCenter_val, Matrix.diagonal_apply, hζ, ← e2]`.

Simplify using `only [restr, Matrix.submatrix_apply]`. Rewrite using `[hhw, hsfix _ (show (Fin.castLE (r_le_X' R) b).val < R.r from b.2)]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`.

Rewrite using `[if_neg (fun e => hab (Fin.castLE_injective (r_le_X' R) e)), if_neg hab]`.
-/
theorem regModZX_of (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (hpar : ∀ a : Fin (R.N R.m - 1), R.r ≤ a.val → Even (∑ τ, (W.sgTrue τ).w (posX R a))) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K))
    (hlam : ∃ w1 ∈ Pr.vG 0, ∃ c : ℕ → 𝓞 X.E, (∀ i < R.r, c i ∉ w1.asIdeal) ∧
      ∀ i i', i < R.r → i' < R.r → ∀ z : 𝓞 X.E, star ((z : 𝓞 X.E) : X.E) * ((z : 𝓞 X.E) : X.E) = 1 →
        c i' - z * c i ∈ w1.asIdeal → i' = i) :
    RegModZX W Ch sel mu := by
  have : NeZero (R.N R.m - 1) := ⟨(X'_pos R).ne'⟩
  obtain ⟨w1, h1, c, hc0, hc⟩ := hlam
  obtain ⟨w2, h2⟩ : (Pr.vG 1).Nonempty := by
    rw [← Finset.card_pos, hPr.vG_card]
    exact hX.f_pos
  have hne : w2 ≠ w1 := fun h => hPr.g_ne (by rw [← hPr.vG_norm 0 w1 h1, ← hPr.vG_norm 1 w2 h2, h])
  have m1 : w1 ∈ Pr.vGs := Finset.mem_union_left _ h1
  have m2 : w2 ∈ Pr.vGs := Finset.mem_union_right _ h2
  let W1 : rowSG Pr sel mu := ⟨w1, Finset.mem_union_left _ m1⟩
  let W2 : rowSG Pr sel mu := ⟨w2, Finset.mem_union_left _ m2⟩
  have hW12 : W2 ≠ W1 := fun h => hne (congrArg Subtype.val h)
  have hr : 0 < R.r := nz_r_pos R
  have hn : R.r < R.N R.m - 1 := by
    rw [rank_X'_eq R]
    have := Nat.mul_pos (by have := R.two_le_m; omega : 0 < R.m) (nz_t_pos R)
    omega
  let cF : Fin (R.N R.m - 1) → 𝓞 X.E := fun b => c b.val
  let bl := List.replicate R.m R.t
  have hstab := fun (γ : UF X.E (R.N R.m - 1)) (g : GLG X.E (R.N R.m - 1) (rowSG Pr sel mu))
      (hg2 : g W2 ∈ blockUT _ _ R.r bl) (hg1 : g W1 ∈ blockUT _ _ R.r bl) e =>
    stabilizer_eq_scalar_mul_permMatrix hX (posX R) bl hr hn cF W1 W2 hW12 (fun i hi => hc0 i.val hi)
      (fun i i' hi hi' z hz hm => Fin.ext (hc i.val i'.val hi hi' z hz hm)) (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) γ g hg2 hg1 e
  have hinj : Function.Injective (v0Z (E := X.E) Pr.vGs R.r) := by
    rw [injective_iff_map_eq_one]
    intro ζ hζ
    have e := congrArg (fun g : G0 X.E Pr.vGs R.r => Units.val (g ⟨w1, m1⟩) ⟨0, hr⟩ ⟨0, hr⟩) hζ
    simp only at e
    rw [torsionCenter_val, Matrix.diagonal_apply_eq, Pi.one_apply, Units.val_one, Matrix.one_apply_eq] at e
    have h1' := nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) (torsion_normOne hX.conjE ζ)
      (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self])
    exact Subtype.ext (Units.ext h1')
  intro a ha
  refine trRep_asAlgebraHom_ne_zero_of_mul_v0eZ_ne_zero (rowVal W (rowSG Pr sel mu)) (rowTyKK Ch sel mu).inv (unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R))
    (rowTyKK_inv_normBy_g0Hat Ch sel mu) (v0Z Pr.vGs R.r) (torsionScalarCharacterAtBase W Ch sel mu) hinj (torsionCenter_scalar_X W Ch sel mu hX)
    (nzPt (v0Fr (posX R) R.r cF W1)) (nzExt X.K W.sgTrue) (nzExt_ne_zero _ _) ?_ ?_ a ha
  · intro γ h e
    obtain ⟨z, s, hz, hsfix, hco, hγ, hhw⟩ := hstab γ h.1 (HK_le_blockUT _ _ _ _ (levelGroup_X_block Ch sel mu h W2 m2))
      (HK_le_blockUT _ _ _ _ (levelGroup_X_block Ch sel mu h W1 m1)) e
    have hz1 : z = 1 := by
      have h0 := (mem_HK.mp (levelGroup_X_block Ch sel mu h W1 m1)).2 ⟨0, lt_trans hr hn⟩ ⟨0, lt_trans hr hn⟩ hr hr
      rw [hhw, if_pos (hsfix _ hr).symm, Matrix.one_apply_eq] at h0
      exact nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) hz
        (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h0, map_one, sub_self])
    subst hz1
    have hγ' : ufGL X.E _ γ = permGL X.E (posX R * s * (posX R)⁻¹) := by
      apply Units.ext
      ext i j
      rw [hγ, permGL_val, pM_apply, map_one]
    have hh' : ∀ w, h.1 w = permGL _ s := fun w => by
      apply Units.ext
      ext i j
      rw [hhw, permGL_val, pM_apply, map_one]
    rw [character_permutation_X_trivial Ch sel mu hPr hCh hξ s hsfix hco h hh', Units.val_one, one_smul]
    show rhoV X.emb W.sgTrue (ufGL X.E _ γ) (nzExt X.K W.sgTrue) = _
    rw [hγ']
    have hx : ∀ x, (posX R * s * (posX R)⁻¹) x = posX R (s ((posX R)⁻¹ x)) := fun _ => rfl
    have hx' : ∀ x, posX R ((posX R)⁻¹ x) = x := fun x => by simp
    apply nz_rhoV_perm
    · intro τ x
      rw [hx]
      by_cases hb : ((posX R)⁻¹ x).val < R.r
      · rw [hsfix _ hb, hx']
      · rw [nz_sg_const hW τ _ _ ((nz_ge_of_fix s hsfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb) (hco _), hx']
    · intro x hne'
      rw [hx] at hne'
      have hb : ¬ ((posX R)⁻¹ x).val < R.r := fun hb => hne' (by rw [hsfix _ hb, hx'])
      have := hpar _ (Nat.not_lt.mp hb)
      rwa [hx'] at this
  · intro γ h t e
    have hD : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs),
        unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t w = diagEmb _ (r_le_X' R) (t ⟨w.1, hw⟩) := fun w hw => extGLG_of_mem _ w hw
    have hgb : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs), (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t) w ∈ blockUT _ _ R.r bl := by
      intro w hw
      rw [Pi.mul_apply, hD w hw]
      exact Subgroup.mul_mem _ (HK_le_blockUT _ _ _ _ (levelGroup_X_block Ch sel mu h w hw)) (diagEmb_mem_blockUT _ _ _)
    obtain ⟨z, s, hz, hsfix, -, -, hhw⟩ := hstab γ (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t) (hgb W2 m2) (hgb W1 m1) e
    obtain ⟨ζ, hζ⟩ := normOne_integer_is_torsion hX.conjE hz
    refine ⟨ζ, funext fun w => ?_⟩
    let W' : rowSG Pr sel mu := ⟨w.1, Finset.mem_union_left _ w.2⟩
    have e2 : restr (r_le_X' R) (Units.val ((h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_X' R) t) W')) = Units.val (t w) := by
      rw [Pi.mul_apply, hD W' w.2, Units.val_mul, restr_mul (r_le_X' R) bl _ (diagEmb_mem_blockUT (r_le_X' R) bl (t ⟨w.1, w.2⟩)),
        restrict_eq_one_of_mem_blockLevel (r_le_X' R) bl (levelGroup_X_block Ch sel mu h W' w.2), one_mul, diagEmb_val, restrict_diagonalBlock]
    apply Units.ext
    ext a b
    rw [torsionCenter_val, Matrix.diagonal_apply, hζ, ← e2]
    simp only [restr, Matrix.submatrix_apply]
    rw [hhw, hsfix _ (show (Fin.castLE (r_le_X' R) b).val < R.r from b.2)]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun e => hab (Fin.castLE_injective (r_le_X' R) e)), if_neg hab]

end RowsMain

section RowsMainV

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

open Classical in
/- English proof (translation)
Take `⟨ε, hε⟩` from `nz_lamQ_ev (K := X.K) (a := R.r) (b := R.t) (le_refl R.nV) s hfix`. Establish `key : ∀ w : rowSG Pr sel mu, ((mtTyKK Ch sel mu j).inv w).ev (h.1 w) = (if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε))⁻¹`. Introduce `w`. Rewrite using `[hh w]`. Use `show ((mtTyKK Ch sel mu j w).inv).ev _ = _`.

Rewrite using `[Lev.inv_ev]`. Distinguish the cases in `hw : w.1 ∈ Pr.vGs`. Rewrite using `[if_pos hw, mtTyKK, LevFam.glue_of_mem _ _ w hw] show ((⟨HK R.nV _ R.r [R.t], lamK (fun _ => (chiAt Ch ⟨w.1, hw⟩ (j - 1))⁻¹) R.nV R.r [R.t]⟩ : Lev _ X.K _).ev _)⁻¹ = 1⁻¹`. Rewrite using `[levelCharacter_permutation_eq_one _ _ s hfix hco (fun _ ε' => by rw [MonoidHom.inv_apply, nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩ (j - 1) ε', inv_one])]`. Rewrite using `[if_neg hw, mtTyKK, LevFam.glue_of_not _ _ w hw] show ((⟨HQ _ _ R.r R.t, lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r R.t⟩ : Lev _ X.K _).ev _)⁻¹ = _`.

Rewrite using `[hε]`. Rewrite using `[LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w, Finset.prod_inv_distrib, hξ.prod ε, inv_one]`.
-/
theorem character_permutation_V_trivial (hPr : Pr.Ok) (hCh : Ch.Ok) (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K)) (j : ℕ) (s : Equiv.Perm (Fin R.nV))
    (hfix : ∀ b : Fin R.nV, b.val < R.r → s b = b)
    (hco : ∀ b : Fin R.nV, coarse R.r [R.t] (s b).val = coarse R.r [R.t] b.val)
    (h : ↥(mtTyKK Ch sel mu j).inv.grp) (hh : ∀ w, h.1 w = permGL _ s) : (mtTyKK Ch sel mu j).inv.chr h = 1 := by
  obtain ⟨ε, hε⟩ := nz_lamQ_ev (K := X.K) (a := R.r) (b := R.t) (le_refl R.nV) s hfix
  have key : ∀ w : rowSG Pr sel mu, ((mtTyKK Ch sel mu j).inv w).ev (h.1 w) =
      (if w.1 ∈ Pr.vGs then (1 : X.Kˣ) else resChar (mu : Chr X.F X.E X.K) w.1 (sgnU _ ε))⁻¹ := by
    intro w
    rw [hh w]
    show ((mtTyKK Ch sel mu j w).inv).ev _ = _
    rw [Lev.inv_ev]
    by_cases hw : w.1 ∈ Pr.vGs
    · rw [if_pos hw, mtTyKK, LevFam.glue_of_mem _ _ w hw]
      show ((⟨HK R.nV _ R.r [R.t], lamK (fun _ => (chiAt Ch ⟨w.1, hw⟩ (j - 1))⁻¹) R.nV R.r [R.t]⟩ :
        Lev _ X.K _).ev _)⁻¹ = 1⁻¹
      rw [levelCharacter_permutation_eq_one _ _ s hfix hco (fun _ ε' => by rw [MonoidHom.inv_apply, nz_chiAt_sgn hPr hCh ⟨w.1, hw⟩ (j - 1) ε', inv_one])]
    · rw [if_neg hw, mtTyKK, LevFam.glue_of_not _ _ w hw]
      show ((⟨HQ _ _ R.r R.t, lamQ (resChar (mu : Chr X.F X.E X.K) w.1) _ R.r R.t⟩ : Lev _ X.K _).ev _)⁻¹ = _
      rw [hε]
  rw [LevFam.chr_ev, Finset.prod_congr rfl fun w _ => key w, Finset.prod_inv_distrib, hξ.prod ε, inv_one]

open Classical in
/- English proof (translation)
Establish `hm : h.1 w ∈ ((mtTyKK Ch sel mu j).inv w).H` using `(mtTyKK Ch sel mu j).inv.mem_at h w`. Establish `e : ((mtTyKK Ch sel mu j).inv w).H = HK R.nV _ R.r [R.t]` using `by show (mtTyKK Ch sel mu j w).H = _`. Rewrite using `[mtTyKK, LevFam.glue_of_mem _ _ w hw]`. Both sides reduce to the same expression. Rewrite `hm` using `[e]`.

Conclude with `hm`.
-/
theorem levelGroup_V_block (j : ℕ) (h : ↥(mtTyKK Ch sel mu j).inv.grp) (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs) :
    h.1 w ∈ HK R.nV _ R.r [R.t] := by
  have hm : h.1 w ∈ ((mtTyKK Ch sel mu j).inv w).H := (mtTyKK Ch sel mu j).inv.mem_at h w
  have e : ((mtTyKK Ch sel mu j).inv w).H = HK R.nV _ R.r [R.t] := by
    show (mtTyKK Ch sel mu j w).H = _
    rw [mtTyKK, LevFam.glue_of_mem _ _ w hw]
    rfl
  rw [e] at hm
  exact hm

open Classical in

/- English proof (translation)
Establish `: NeZero R.nV` using `⟨(nV_pos R).ne'⟩`. Take `⟨w1, h1, c, hc0, hc⟩` from `hlam`. Choose the witnesses or unpack the hypotheses as in `⟨w2, h2⟩ : (Pr.vG 1).Nonempty := by`. Rewrite using `[← Finset.card_pos, hPr.vG_card]`. Conclude with `hX.f_pos`.

Establish `hne : w2 ≠ w1` using `fun h => hPr.g_ne (by rw [← hPr.vG_norm 0 w1 h1, ← hPr.vG_norm 1 w2 h2, h])`. Establish `m1 : w1 ∈ Pr.vGs` using `Finset.mem_union_left _ h1`. Establish `m2 : w2 ∈ Pr.vGs` using `Finset.mem_union_right _ h2`. Set `W1 : rowSG Pr sel mu` to `⟨w1, Finset.mem_union_left _ m1⟩`. Set `W2 : rowSG Pr sel mu` to `⟨w2, Finset.mem_union_left _ m2⟩`.

Establish `hW12 : W2 ≠ W1` using `fun h => hne (congrArg Subtype.val h)`. Establish `hr : 0 < R.r` using `nz_r_pos R`. Establish `hn : R.r < R.nV` using `by show R.r < R.r + R.t`. Use `nz_t_pos R` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Set `cF : Fin R.nV → 𝓞 X.E` to `fun b => c b.val`. Set `bl` to `[R.t]`. Establish `hstab` using `fun (γ : UF X.E R.nV) (g : GLG X.E R.nV (rowSG Pr sel mu)) (hg2 : g W2 ∈ blockUT _ _ R.r bl) (hg1 : g W1 ∈ blockUT _ _ R.r bl) e => stabilizer_eq_scalar_mul_permMatrix hX (posV R j) bl hr hn cF W1 W2 hW12 (fun i hi => hc0 i.val hi) (fun i i' hi hi' z hz hm => Fin.ext (hc i.val i' …`. Establish `hinj : Function.Injective (v0Z (E` using `X.E) Pr.vGs R.r) := by`. Rewrite using `[injective_iff_map_eq_one]`.

Introduce `ζ hζ`. Establish `e` using `congrArg (fun g : G0 X.E Pr.vGs R.r => Units.val (g ⟨w1, m1⟩) ⟨0, hr⟩ ⟨0, hr⟩) hζ`. Simplify using `only at e`. Rewrite `e` using `[torsionCenter_val, Matrix.diagonal_apply_eq, Pi.one_apply, Units.val_one, Matrix.one_apply_eq]`. Establish `h1'` using `nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) (torsion_normOne hX.conjE ζ) (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self])`.

Conclude with `Subtype.ext (Units.ext h1')`. Introduce `a ha`. Use `trRep_asAlgebraHom_ne_zero_of_mul_v0eZ_ne_zero (mtVal W j (rowSG Pr sel mu)) (mtTyKK Ch sel mu j).inv (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R)) (mtTyKK_inv_normBy_g0Hat Ch sel mu j) (v0Z Pr.vGs R.r) (torsionScalarCharacterAtLevel W Ch sel mu j) hinj (torsionCenter_scal …` and prove the remaining obligations. Introduce `γ h e`. Take `⟨z, s, hz, hsfix, hco, hγ, hhw⟩` from `hstab γ h.1 (HK_le_blockUT _ _ _ _ (levelGroup_V_block Ch sel mu j h W2 m2)) (HK_le_blockUT _ _ _ _ (levelGroup_V_block Ch sel mu j h W1 m1)) e`.

Establish `hz1 : z = 1`. Establish `h0` using `(mem_HK.mp (levelGroup_V_block Ch sel mu j h W1 m1)).2 ⟨0, lt_trans hr hn⟩ ⟨0, lt_trans hr hn⟩ hr hr`. Rewrite `h0` using `[hhw, if_pos (hsfix _ hr).symm, Matrix.one_apply_eq]`. Conclude with `nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) hz (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h0, map_one, sub_self])`. Substitute `hz1` using the available equality.

Establish `hγ' : ufGL X.E _ γ = permGL X.E (posV R j * s * (posV R j)⁻¹)`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[hγ, permGL_val, pM_apply, map_one]`. Establish `hh' : ∀ w, h.1 w = permGL _ s` using `fun w => by`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[hhw, permGL_val, pM_apply, map_one]`. Rewrite using `[character_permutation_V_trivial Ch sel mu hPr hCh hξ j s hsfix hco h hh', Units.val_one, one_smul]`. Use `show rhoVr X.emb (W.lamV j) (ufGL X.E _ γ) (nzExt X.K (W.lamV j)) = _`.

Rewrite using `[hγ']`. Establish `hx : ∀ x, (posV R j * s * (posV R j)⁻¹) x = posV R j (s ((posV R j)⁻¹ x))` using `fun _ => rfl`. Establish `hx' : ∀ x, posV R j ((posV R j)⁻¹ x) = x` using `fun x => by simp`. Apply `nz_rhoVr_perm` to reduce the goal to its premises. Introduce `τ x`.

Rewrite using `[hx]`. Distinguish the cases in `hb : ((posV R j)⁻¹ x).val < R.r`. Rewrite using `[hsfix _ hb, hx']`. Rewrite using `[nz_lamV_const hW hj1 hj2 τ _ _ ((nz_ge_of_fix s hsfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb), hx']`. Introduce `x hne'`.

Rewrite `hne'` using `[hx]`. Establish `hb : ¬ ((posV R j)⁻¹ x).val < R.r` using `fun hb => hne' (by rw [hsfix _ hb, hx'])`. Use `hpar _ (Nat.not_lt.mp hb)` as an intermediate fact. Rewrite `this` using `[hx']`. Then use the resulting hypothesis. Introduce `γ h t e`.

Establish `hD : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs), unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t w = diagEmb _ (r_le_nV R) (t ⟨w.1, hw⟩)` using `fun w hw => extGLG_of_mem _ w hw`. Establish `hgb : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs), (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t) w ∈ blockUT _ _ R.r bl`. Introduce `w hw`. Rewrite using `[Pi.mul_apply, hD w hw]`. Conclude with `Subgroup.mul_mem _ (HK_le_blockUT _ _ _ _ (levelGroup_V_block Ch sel mu j h w hw)) (diagEmb_mem_blockUT _ _ _)`.

Take `⟨z, s, hz, hsfix, -, -, hhw⟩` from `hstab γ (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t) (hgb W2 m2) (hgb W1 m1) e`. Take `⟨ζ, hζ⟩` from `normOne_integer_is_torsion hX.conjE hz`. Use `⟨ζ, funext fun w => ?_⟩` and prove the remaining obligations. Set `W' : rowSG Pr sel mu` to `⟨w.1, Finset.mem_union_left _ w.2⟩`. Establish `e2 : restr (r_le_nV R) (Units.val ((h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t) W')) = Units.val (t w)`.

Rewrite using `[Pi.mul_apply, hD W' w.2, Units.val_mul, restr_mul (r_le_nV R) bl _ (diagEmb_mem_blockUT (r_le_nV R) bl (t ⟨w.1, w.2⟩)), restrict_eq_one_of_mem_blockLevel (r_le_nV R) bl (levelGroup_V_block Ch sel mu j h W' w.2), one_mul, diagEmb_val, restrict_diagonalBlock]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Rewrite using `[torsionCenter_val, Matrix.diagonal_apply, hζ, ← e2]`. Simplify using `only [restr, Matrix.submatrix_apply]`.

Rewrite using `[hhw, hsfix _ (show (Fin.castLE (r_le_nV R) b).val < R.r from b.2)]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Rewrite using `[if_pos rfl, if_pos rfl]`. Rewrite using `[if_neg (fun e => hab (Fin.castLE_injective (r_le_nV R) e)), if_neg hab]`.
-/
theorem regModZV_of (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ R.m)
    (hpar : ∀ a : Fin R.nV, R.r ≤ a.val → Even (∑ τ, (W.lamV j τ).w (posV R j a))) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K))
    (hlam : ∃ w1 ∈ Pr.vG 0, ∃ c : ℕ → 𝓞 X.E, (∀ i < R.r, c i ∉ w1.asIdeal) ∧
      ∀ i i', i < R.r → i' < R.r → ∀ z : 𝓞 X.E, star ((z : 𝓞 X.E) : X.E) * ((z : 𝓞 X.E) : X.E) = 1 →
        c i' - z * c i ∈ w1.asIdeal → i' = i) :
    RegModZV W Ch sel mu j := by
  have : NeZero R.nV := ⟨(nV_pos R).ne'⟩
  obtain ⟨w1, h1, c, hc0, hc⟩ := hlam
  obtain ⟨w2, h2⟩ : (Pr.vG 1).Nonempty := by
    rw [← Finset.card_pos, hPr.vG_card]
    exact hX.f_pos
  have hne : w2 ≠ w1 := fun h => hPr.g_ne (by rw [← hPr.vG_norm 0 w1 h1, ← hPr.vG_norm 1 w2 h2, h])
  have m1 : w1 ∈ Pr.vGs := Finset.mem_union_left _ h1
  have m2 : w2 ∈ Pr.vGs := Finset.mem_union_right _ h2
  let W1 : rowSG Pr sel mu := ⟨w1, Finset.mem_union_left _ m1⟩
  let W2 : rowSG Pr sel mu := ⟨w2, Finset.mem_union_left _ m2⟩
  have hW12 : W2 ≠ W1 := fun h => hne (congrArg Subtype.val h)
  have hr : 0 < R.r := nz_r_pos R
  have hn : R.r < R.nV := by
    show R.r < R.r + R.t
    have := nz_t_pos R
    omega
  let cF : Fin R.nV → 𝓞 X.E := fun b => c b.val
  let bl := [R.t]
  have hstab := fun (γ : UF X.E R.nV) (g : GLG X.E R.nV (rowSG Pr sel mu))
      (hg2 : g W2 ∈ blockUT _ _ R.r bl) (hg1 : g W1 ∈ blockUT _ _ R.r bl) e =>
    stabilizer_eq_scalar_mul_permMatrix hX (posV R j) bl hr hn cF W1 W2 hW12 (fun i hi => hc0 i.val hi)
      (fun i i' hi hi' z hz hm => Fin.ext (hc i.val i'.val hi hi' z hz hm)) (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) γ g hg2 hg1 e
  have hinj : Function.Injective (v0Z (E := X.E) Pr.vGs R.r) := by
    rw [injective_iff_map_eq_one]
    intro ζ hζ
    have e := congrArg (fun g : G0 X.E Pr.vGs R.r => Units.val (g ⟨w1, m1⟩) ⟨0, hr⟩ ⟨0, hr⟩) hζ
    simp only at e
    rw [torsionCenter_val, Matrix.diagonal_apply_eq, Pi.one_apply, Units.val_one, Matrix.one_apply_eq] at e
    have h1' := nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) (torsion_normOne hX.conjE ζ)
      (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, e, map_one, sub_self])
    exact Subtype.ext (Units.ext h1')
  intro a ha
  refine trRep_asAlgebraHom_ne_zero_of_mul_v0eZ_ne_zero (mtVal W j (rowSG Pr sel mu)) (mtTyKK Ch sel mu j).inv (unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R))
    (mtTyKK_inv_normBy_g0Hat Ch sel mu j) (v0Z Pr.vGs R.r) (torsionScalarCharacterAtLevel W Ch sel mu j) hinj (torsionCenter_scalar_V W Ch sel mu hX j)
    (nzPt (v0Fr (posV R j) R.r cF W1)) (nzExt X.K (W.lamV j)) (nzExt_ne_zero _ _) ?_ ?_ a ha
  · intro γ h e
    obtain ⟨z, s, hz, hsfix, hco, hγ, hhw⟩ := hstab γ h.1 (HK_le_blockUT _ _ _ _ (levelGroup_V_block Ch sel mu j h W2 m2))
      (HK_le_blockUT _ _ _ _ (levelGroup_V_block Ch sel mu j h W1 m1)) e
    have hz1 : z = 1 := by
      have h0 := (mem_HK.mp (levelGroup_V_block Ch sel mu j h W1 m1)).2 ⟨0, lt_trans hr hn⟩ ⟨0, lt_trans hr hn⟩ hr hr
      rw [hhw, if_pos (hsfix _ hr).symm, Matrix.one_apply_eq] at h0
      exact nz_root_one hX w1 (hPr.g_prime 0) (hPr.g_mem h1) (hg 0) hz
        (by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h0, map_one, sub_self])
    subst hz1
    have hγ' : ufGL X.E _ γ = permGL X.E (posV R j * s * (posV R j)⁻¹) := by
      apply Units.ext
      ext i j
      rw [hγ, permGL_val, pM_apply, map_one]
    have hh' : ∀ w, h.1 w = permGL _ s := fun w => by
      apply Units.ext
      ext i j
      rw [hhw, permGL_val, pM_apply, map_one]
    rw [character_permutation_V_trivial Ch sel mu hPr hCh hξ j s hsfix hco h hh', Units.val_one, one_smul]
    show rhoVr X.emb (W.lamV j) (ufGL X.E _ γ) (nzExt X.K (W.lamV j)) = _
    rw [hγ']
    have hx : ∀ x, (posV R j * s * (posV R j)⁻¹) x = posV R j (s ((posV R j)⁻¹ x)) := fun _ => rfl
    have hx' : ∀ x, posV R j ((posV R j)⁻¹ x) = x := fun x => by simp
    apply nz_rhoVr_perm
    · intro τ x
      rw [hx]
      by_cases hb : ((posV R j)⁻¹ x).val < R.r
      · rw [hsfix _ hb, hx']
      · rw [nz_lamV_const hW hj1 hj2 τ _ _ ((nz_ge_of_fix s hsfix _).mpr (Nat.not_lt.mp hb)) (Nat.not_lt.mp hb), hx']
    · intro x hne'
      rw [hx] at hne'
      have hb : ¬ ((posV R j)⁻¹ x).val < R.r := fun hb => hne' (by rw [hsfix _ hb, hx'])
      have := hpar _ (Nat.not_lt.mp hb)
      rwa [hx'] at this
  · intro γ h t e
    have hD : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs),
        unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t w = diagEmb _ (r_le_nV R) (t ⟨w.1, hw⟩) := fun w hw => extGLG_of_mem _ w hw
    have hgb : ∀ (w : rowSG Pr sel mu) (hw : w.1 ∈ Pr.vGs), (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t) w ∈ blockUT _ _ R.r bl := by
      intro w hw
      rw [Pi.mul_apply, hD w hw]
      exact Subgroup.mul_mem _ (HK_le_blockUT _ _ _ _ (levelGroup_V_block Ch sel mu j h w hw)) (diagEmb_mem_blockUT _ _ _)
    obtain ⟨z, s, hz, hsfix, -, -, hhw⟩ := hstab γ (h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t) (hgb W2 m2) (hgb W1 m1) e
    obtain ⟨ζ, hζ⟩ := normOne_integer_is_torsion hX.conjE hz
    refine ⟨ζ, funext fun w => ?_⟩
    let W' : rowSG Pr sel mu := ⟨w.1, Finset.mem_union_left _ w.2⟩
    have e2 : restr (r_le_nV R) (Units.val ((h.1 * unipotentGroupBlockEmbedding Pr sel mu (r_le_nV R) t) W')) = Units.val (t w) := by
      rw [Pi.mul_apply, hD W' w.2, Units.val_mul, restr_mul (r_le_nV R) bl _ (diagEmb_mem_blockUT (r_le_nV R) bl (t ⟨w.1, w.2⟩)),
        restrict_eq_one_of_mem_blockLevel (r_le_nV R) bl (levelGroup_V_block Ch sel mu j h W' w.2), one_mul, diagEmb_val, restrict_diagonalBlock]
    apply Units.ext
    ext a b
    rw [torsionCenter_val, Matrix.diagonal_apply, hζ, ← e2]
    simp only [restr, Matrix.submatrix_apply]
    rw [hhw, hsfix _ (show (Fin.castLE (r_le_nV R) b).val < R.r from b.2)]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun e => hab (Fin.castLE_injective (r_le_nV R) e)), if_neg hab]

end RowsMainV

section Card

variable {E : Type} [Field E] [NumberField E] [StarRing E]

/- English proof (translation)
Use `set Q := 𝓞 E ⧸ w.asIdeal`. Use `set red : NumberField.Units.torsion E → Q := fun ζ => Ideal.Quotient.mk w.asIdeal ((ζ : (𝓞 E)ˣ) : 𝓞 E)`. Establish `hfin : Finite Q` using `Nat.finite_of_card_ne_zero (by omega)`. Use `Fintype.ofFinite Q` as an intermediate fact. Establish `hQ : Nat.card Q = Fintype.card Q` using `Nat.card_eq_fintype_card`.

Establish `hμ : Nat.card (NumberField.Units.torsion E) = Fintype.card (NumberField.Units.torsion E)` using `Nat.card_eq_fintype_card`. Establish `hμ1 : 1 ≤ Fintype.card (NumberField.Units.torsion E)` using `Fintype.card_pos`. Establish `step : ∀ k, k ≤ r → ∃ x : ℕ → Q, (∀ i < k, x i ≠ 0) ∧ ∀ i i' (ζ : NumberField.Units.torsion E), i < k → i' < k → x i' = red ζ * x i → i' = i`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => exact fun _ => ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _), fun i _ _ hi => absurd hi (Nat.not_lt_zero _)⟩`. Consider the case `succ k ih`. Introduce `hk`. Take `⟨x, hx0, hx⟩` from `ih (by omega)`. Set `F : Finset Q` to `insert 0 ((Finset.range k ×ˢ (Finset.univ : Finset (NumberField.Units.torsion E))).image fun p => red p.2 * x p.1)`.

Establish `hF : F.card < Fintype.card Q`. Establish `h1 : F.card ≤ 1 + k * Fintype.card (NumberField.Units.torsion E)`. Establish `h3` using `Finset.card_insert_le (0 : Q) ((Finset.range k ×ˢ (Finset.univ : Finset (NumberField.Units.torsion E))).image fun p => red p.2 * x p.1)`. Establish `h4` using `Finset.card_image_le (s := Finset.range k ×ˢ (Finset.univ : Finset (NumberField.Units.torsion E))) (f := fun p => red p.2 * x p.1)`. Rewrite `h4` using `[Finset.card_product, Finset.card_range, Finset.card_univ]`.

Use `show (insert 0 _ : Finset Q).card ≤ _`. Use linear arithmetic over natural numbers and integers. Establish `h2 : k * Fintype.card (NumberField.Units.torsion E) + Fintype.card (NumberField.Units.torsion E) ≤ r * Fintype.card (NumberField.Units.torsion E)`. Rewrite using `[← Nat.succ_mul]`. Conclude with `Nat.mul_le_mul_right _ hk`.

Rewrite using `[← hQ]`. Rewrite `hcard` using `[hμ]`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y : Q, y ∉ F := by`. Assume the negation of the conclusion as `hc`.

Use `push Not at hc`. Establish `: (Finset.univ : Finset Q) ⊆ F` using `fun y _ => hc y`. Use `Finset.card_le_card this` as an intermediate fact. Rewrite `this` using `[Finset.card_univ]`. Use linear arithmetic over natural numbers and integers.

Establish `hy0 : y ≠ 0` using `fun h => hy (h ▸ Finset.mem_insert_self _ _)`. Establish `hyF : ∀ i < k, ∀ ζ, y ≠ red ζ * x i` using `fun i hi ζ h => hy (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨(i, ζ), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_univ _⟩, h.symm⟩))`. Use `⟨fun i => if i = k then y else x i, fun i hi => ?_, fun i i' ζ hi hi' e => ?_⟩` and prove the remaining obligations. Simplify using `only`. Distinguish the cases in `hik : i = k`.

Rewrite using `[if_pos hik]`. Conclude with `hy0`. Rewrite using `[if_neg hik]`. Conclude with `hx0 i (by omega)`. Simplify using `only at e`.

Apply the tactic sequence `by_cases hik : i = k <;> by_cases hik' : i' = k`. Rewrite using `[hik, hik']`. Rewrite `e` using `[if_pos hik, if_neg hik']`. It suffices to derive a contradiction. Establish `hrinv : red ζ⁻¹ * red ζ = 1`.

Simplify using `only [red]`. Rewrite using `[← map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one, map_one]`. Conclude with `hyF i' (by omega) ζ⁻¹ (by rw [e, ← mul_assoc, hrinv, one_mul])`. Rewrite `e` using `[if_neg hik, if_pos hik']`. Conclude with `absurd e (hyF i (by omega) ζ)`.

Rewrite `e` using `[if_neg hik, if_neg hik']`. Conclude with `hx i i' ζ (by omega) (by omega) e`. Take `⟨x, hx0, hx⟩` from `step r le_rfl`. Use `choose c hc using fun i => Ideal.Quotient.mk_surjective (I := w.asIdeal) (x i)`. Use `⟨c, fun i hi h0 => hx0 i hi (by rw [← hc i]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h0), fun i i' hi hi' z hz hm => ?_⟩` and prove the remaining obligations.

Take `⟨ζ, hζ⟩` from `normOne_integer_is_torsion hconj hz`. Use `hx i i' ζ hi hi' ?_` and prove the remaining obligations. Establish `h1` using `Ideal.Quotient.eq_zero_iff_mem.mpr hm`. Rewrite `h1` using `[map_sub, map_mul, hc, hc, ← hζ]`. Conclude with `sub_eq_zero.mp h1`.
-/
theorem exists_separating_residues (hconj : ∀ (φ : E →+* ℂ) (x : E), φ (star x) = starRingEnd ℂ (φ x)) (w : HeightOneSpectrum (𝓞 E))
    (r : ℕ) (hcard : r * Nat.card (NumberField.Units.torsion E) < Nat.card (𝓞 E ⧸ w.asIdeal)) :
    ∃ c : ℕ → 𝓞 E, (∀ i < r, c i ∉ w.asIdeal) ∧
      ∀ i i', i < r → i' < r → ∀ z : 𝓞 E, star ((z : 𝓞 E) : E) * ((z : 𝓞 E) : E) = 1 →
        c i' - z * c i ∈ w.asIdeal → i' = i := by
  classical
  set Q := 𝓞 E ⧸ w.asIdeal
  set red : NumberField.Units.torsion E → Q := fun ζ => Ideal.Quotient.mk w.asIdeal ((ζ : (𝓞 E)ˣ) : 𝓞 E)
  have hfin : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite Q
  have hQ : Nat.card Q = Fintype.card Q := Nat.card_eq_fintype_card
  have hμ : Nat.card (NumberField.Units.torsion E) = Fintype.card (NumberField.Units.torsion E) := Nat.card_eq_fintype_card
  have hμ1 : 1 ≤ Fintype.card (NumberField.Units.torsion E) := Fintype.card_pos
  have step : ∀ k, k ≤ r → ∃ x : ℕ → Q, (∀ i < k, x i ≠ 0) ∧
      ∀ i i' (ζ : NumberField.Units.torsion E), i < k → i' < k → x i' = red ζ * x i → i' = i := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun _ => 0, fun i hi => absurd hi (Nat.not_lt_zero _), fun i _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨x, hx0, hx⟩ := ih (by omega)
      let F : Finset Q := insert 0 ((Finset.range k ×ˢ (Finset.univ : Finset (NumberField.Units.torsion E))).image
        fun p => red p.2 * x p.1)
      have hF : F.card < Fintype.card Q := by
        have h1 : F.card ≤ 1 + k * Fintype.card (NumberField.Units.torsion E) := by
          have h3 := Finset.card_insert_le (0 : Q) ((Finset.range k ×ˢ (Finset.univ : Finset (NumberField.Units.torsion E))).image
            fun p => red p.2 * x p.1)
          have h4 := Finset.card_image_le (s := Finset.range k ×ˢ (Finset.univ : Finset (NumberField.Units.torsion E)))
            (f := fun p => red p.2 * x p.1)
          rw [Finset.card_product, Finset.card_range, Finset.card_univ] at h4
          show (insert 0 _ : Finset Q).card ≤ _
          omega
        have h2 : k * Fintype.card (NumberField.Units.torsion E) + Fintype.card (NumberField.Units.torsion E) ≤
            r * Fintype.card (NumberField.Units.torsion E) := by
          rw [← Nat.succ_mul]
          exact Nat.mul_le_mul_right _ hk
        rw [← hQ]
        rw [hμ] at hcard
        omega
      obtain ⟨y, hy⟩ : ∃ y : Q, y ∉ F := by
        by_contra hc
        push Not at hc
        have : (Finset.univ : Finset Q) ⊆ F := fun y _ => hc y
        have := Finset.card_le_card this
        rw [Finset.card_univ] at this
        omega
      have hy0 : y ≠ 0 := fun h => hy (h ▸ Finset.mem_insert_self _ _)
      have hyF : ∀ i < k, ∀ ζ, y ≠ red ζ * x i := fun i hi ζ h => hy (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨(i, ζ), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hi, Finset.mem_univ _⟩, h.symm⟩))
      refine ⟨fun i => if i = k then y else x i, fun i hi => ?_, fun i i' ζ hi hi' e => ?_⟩
      · dsimp only
        by_cases hik : i = k
        · rw [if_pos hik]
          exact hy0
        · rw [if_neg hik]
          exact hx0 i (by omega)
      · dsimp only at e
        by_cases hik : i = k <;> by_cases hik' : i' = k
        · rw [hik, hik']
        · rw [if_pos hik, if_neg hik'] at e
          exfalso
          have hrinv : red ζ⁻¹ * red ζ = 1 := by
            simp only [red]
            rw [← map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one, map_one]
          exact hyF i' (by omega) ζ⁻¹ (by rw [e, ← mul_assoc, hrinv, one_mul])
        · rw [if_neg hik, if_pos hik'] at e
          exact absurd e (hyF i (by omega) ζ)
        · rw [if_neg hik, if_neg hik'] at e
          exact hx i i' ζ (by omega) (by omega) e
  obtain ⟨x, hx0, hx⟩ := step r le_rfl
  choose c hc using fun i => Ideal.Quotient.mk_surjective (I := w.asIdeal) (x i)
  refine ⟨c, fun i hi h0 => hx0 i hi (by rw [← hc i]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h0),
    fun i i' hi hi' z hz hm => ?_⟩
  obtain ⟨ζ, hζ⟩ := normOne_integer_is_torsion hconj hz
  refine hx i i' ζ hi hi' ?_
  have h1 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
  rw [map_sub, map_mul, hc, hc, ← hζ] at h1
  exact sub_eq_zero.mp h1

end Card

section RowsCard

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

/- English proof (translation)
Take `⟨w1, h1, hs⟩` from `hsize`. Conclude with `regModZX_of W Ch sel mu hX hPr hCh hW hpar hg hξ ⟨w1, h1, exists_separating_residues hX.conjE w1 R.r hs⟩`.
-/
theorem regModZX_of_card (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok)
    (hpar : ∀ a : Fin (R.N R.m - 1), R.r ≤ a.val → Even (∑ τ, (W.sgTrue τ).w (posX R a))) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K))
    (hsize : ∃ w1 ∈ Pr.vG 0, R.r * Nat.card (NumberField.Units.torsion X.E) < Nat.card (𝓞 X.E ⧸ w1.asIdeal)) :
    RegModZX W Ch sel mu := by
  obtain ⟨w1, h1, hs⟩ := hsize
  exact regModZX_of W Ch sel mu hX hPr hCh hW hpar hg hξ ⟨w1, h1, exists_separating_residues hX.conjE w1 R.r hs⟩

/- English proof (translation)
Take `⟨w1, h1, hs⟩` from `hsize`. Conclude with `regModZV_of W Ch sel mu hX hPr hCh hW j hj1 hj2 hpar hg hξ ⟨w1, h1, exists_separating_residues hX.conjE w1 R.r hs⟩`.
-/
theorem regModZV_of_card (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok) (hW : W.Ok) (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ R.m)
    (hpar : ∀ a : Fin R.nV, R.r ≤ a.val → Even (∑ τ, (W.lamV j τ).w (posV R j a))) (hg : ∀ i, 2 * X.f + 1 < Pr.g i)
    (hξ : XiSign Pr sel (mu : Chr X.F X.E X.K))
    (hsize : ∃ w1 ∈ Pr.vG 0, R.r * Nat.card (NumberField.Units.torsion X.E) < Nat.card (𝓞 X.E ⧸ w1.asIdeal)) :
    RegModZV W Ch sel mu j := by
  obtain ⟨w1, h1, hs⟩ := hsize
  exact regModZV_of W Ch sel mu hX hPr hCh hW j hj1 hj2 hpar hg hξ ⟨w1, h1, exists_separating_residues hX.conjE w1 R.r hs⟩

end RowsCard

section NotFaithful

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def v0m1 (E : Type) [Field E] [NumberField E] : NumberField.Units.torsion E :=
  ⟨-1, (CommGroup.mem_torsion _).mpr ((isOfFinOrder_iff_pow_eq_one).mpr ⟨2, two_pos, by simp⟩)⟩

open Classical in

/- English proof (translation)
Establish `hr : 0 < R.r` using `nz_r_pos R`. Choose the witnesses or unpack the hypotheses as in `⟨w1, h1⟩ : (Pr.vG 0).Nonempty := by`. Rewrite using `[← Finset.card_pos, hPr.vG_card]`. Conclude with `hX.f_pos`. Establish `m1 : w1 ∈ Pr.vGs` using `Finset.mem_union_left _ h1`.

Introduce `hz`. Establish `e` using `congrArg (fun g : G0 X.E Pr.vGs R.r => Units.val (g ⟨w1, m1⟩) ⟨0, hr⟩ ⟨0, hr⟩) hz`. Simplify using `only at e`. Rewrite `e` using `[torsionCenter_val, Matrix.diagonal_apply_eq, Pi.one_apply, Units.val_one, Matrix.one_apply_eq]`. Establish `h2 : (2 : 𝓞 X.E) ∈ w1.asIdeal`.

Establish `: ((-1 : (𝓞 X.E)ˣ) : 𝓞 X.E) - 1 ∈ w1.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]`. Conclude with `sub_eq_zero.mpr e`. Establish `h3 : ((-1 : (𝓞 X.E)ˣ) : 𝓞 X.E) - 1 = -2` using `by push_cast; ring`. Rewrite `this` using `[h3]`.

Simplify using `using w1.asIdeal.neg_mem this`. Establish `hgm : ((Pr.g 0 : ℕ) : 𝓞 X.E) ∈ w1.asIdeal` using `hPr.g_mem h1`. Choose the witnesses or unpack the hypotheses as in `⟨q, hq⟩ : ∃ q, Pr.g 0 = 2 * q + 1 := by`. Break down `(hPr.g_prime 0).eq_two_or_odd' with h | h` into its components or cases. Use `hg 0` as an intermediate fact.

Use `hX.f_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨q, hq⟩` from `h`. Conclude with `⟨q, by omega⟩`. Establish `h1' : (1 : 𝓞 X.E) ∈ w1.asIdeal`.

Establish `: (1 : 𝓞 X.E) = ((Pr.g 0 : ℕ) : 𝓞 X.E) - 2 * (q : 𝓞 X.E)`. Rewrite using `[hq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `w1.asIdeal.sub_mem hgm (w1.asIdeal.mul_mem_right _ h2)`. Conclude with `w1.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1')`.
-/
theorem negOneCenter_ne_one (hX : X.Ok) (hPr : Pr.Ok) (hg : ∀ i, 2 * X.f + 1 < Pr.g i) : v0Z Pr.vGs R.r (v0m1 X.E) ≠ 1 := by
  have hr : 0 < R.r := nz_r_pos R
  obtain ⟨w1, h1⟩ : (Pr.vG 0).Nonempty := by
    rw [← Finset.card_pos, hPr.vG_card]
    exact hX.f_pos
  have m1 : w1 ∈ Pr.vGs := Finset.mem_union_left _ h1
  intro hz
  have e := congrArg (fun g : G0 X.E Pr.vGs R.r => Units.val (g ⟨w1, m1⟩) ⟨0, hr⟩ ⟨0, hr⟩) hz
  simp only at e
  rw [torsionCenter_val, Matrix.diagonal_apply_eq, Pi.one_apply, Units.val_one, Matrix.one_apply_eq] at e
  have h2 : (2 : 𝓞 X.E) ∈ w1.asIdeal := by
    have : ((-1 : (𝓞 X.E)ˣ) : 𝓞 X.E) - 1 ∈ w1.asIdeal := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one]
      exact sub_eq_zero.mpr e
    have h3 : ((-1 : (𝓞 X.E)ˣ) : 𝓞 X.E) - 1 = -2 := by push_cast; ring
    rw [h3] at this
    simpa using w1.asIdeal.neg_mem this
  have hgm : ((Pr.g 0 : ℕ) : 𝓞 X.E) ∈ w1.asIdeal := hPr.g_mem h1
  obtain ⟨q, hq⟩ : ∃ q, Pr.g 0 = 2 * q + 1 := by
    rcases (hPr.g_prime 0).eq_two_or_odd' with h | h
    · have := hg 0
      have := hX.f_pos
      omega
    · obtain ⟨q, hq⟩ := h
      exact ⟨q, by omega⟩
  have h1' : (1 : 𝓞 X.E) ∈ w1.asIdeal := by
    have : (1 : 𝓞 X.E) = ((Pr.g 0 : ℕ) : 𝓞 X.E) - 2 * (q : 𝓞 X.E) := by
      rw [hq]
      push_cast
      ring
    rw [this]
    exact w1.asIdeal.sub_mem hgm (w1.asIdeal.mul_mem_right _ h2)
  exact w1.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1')

open Classical in

/- English proof (translation)
Use `set ζ := v0m1 X.E`. Use `⟨MonoidAlgebra.single 1 1 - MonoidAlgebra.single (v0Z Pr.vGs R.r ζ) (((torsionScalarCharacterAtBase W Ch sel mu ζ)⁻¹ : X.Kˣ) : X.K), ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Use `congrArg (fun x : MonoidAlgebra X.K (G0 X.E Pr.vGs R.r) => x.coeff 1) h0` as an intermediate fact. Simplify using `only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_zero] at this`.

Simplify using `only [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at this`. Rewrite `this` using `[if_pos trivial, if_neg (negOneCenter_ne_one hX hPr hg), sub_zero]`. Conclude with `one_ne_zero this`. Rewrite using `[map_sub, Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, map_one, one_smul]`. Apply `LinearMap.ext` to reduce the goal to its premises.

Introduce `φ`. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, torsionCenter_scalar_X W Ch sel mu hX ζ φ, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero _), one_smul, Module.End.one_apply, sub_self, LinearMap.zero_apply]`.
-/
theorem unipotentAction_not_faithful_X (hX : X.Ok) (hPr : Pr.Ok) (hg : ∀ i, 2 * X.f + 1 < Pr.g i) :
    ∃ a : MonoidAlgebra X.K (G0 X.E Pr.vGs R.r), a ≠ 0 ∧ (g0HatRepEqFunX W Ch sel mu).asAlgebraHom a = 0 := by
  classical
  set ζ := v0m1 X.E
  refine ⟨MonoidAlgebra.single 1 1 - MonoidAlgebra.single (v0Z Pr.vGs R.r ζ) (((torsionScalarCharacterAtBase W Ch sel mu ζ)⁻¹ : X.Kˣ) : X.K), ?_, ?_⟩
  · intro h0
    have := congrArg (fun x : MonoidAlgebra X.K (G0 X.E Pr.vGs R.r) => x.coeff 1) h0
    simp only [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_zero] at this
    simp only [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    rw [if_pos trivial, if_neg (negOneCenter_ne_one hX hPr hg), sub_zero] at this
    exact one_ne_zero this
  · rw [map_sub, Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, map_one, one_smul]
    apply LinearMap.ext
    intro φ
    rw [LinearMap.sub_apply, LinearMap.smul_apply, torsionCenter_scalar_X W Ch sel mu hX ζ φ, smul_smul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (Units.ne_zero _), one_smul, Module.End.one_apply, sub_self, LinearMap.zero_apply]

end NotFaithful

end Formalism.L2.Col
