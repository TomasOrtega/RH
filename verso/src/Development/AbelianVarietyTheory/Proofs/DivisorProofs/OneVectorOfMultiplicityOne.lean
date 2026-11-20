import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalInducedCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalIdempotentCharacters

noncomputable section

open Module NumberField
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.OneForm

section GroupAlgebra

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Take `⟨n, ρ, hi, hρ⟩` from `h`. Set `j` to `algebraMap K (AlgebraicClosure K)`. Establish `hj : Function.Injective j` using `j.injective`. Use `set T : Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K) := ∑ g, ρ (g * s * g⁻¹) with hT`. Establish `hc : ∀ g v, T (ρ g v) = ρ g (T v)`.

Introduce `g v`. Simplify using `only [hT, LinearMap.sum_apply, map_sum]`. Rewrite using `[← Equiv.sum_comp (Equiv.mulLeft g)]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]`.

Use `congr 2`. Simplify using `only [Equiv.coe_mulLeft]`. Use `group`. Take `⟨c, hcT⟩` from `schur_scalar ρ T hc`. Establish `h1 : ∀ u : G, ∑ g, ρ.character (g * s * g⁻¹ * u) = c * ρ.character u`.

Introduce `u`. Establish `: LinearMap.trace _ _ (T * ρ u) = c * ρ.character u`. Rewrite using `[hcT]`. Simplify using `[Representation.character, Module.End.mul_eq_comp]`. Rewrite using `[← this, hT, Finset.sum_mul, map_sum]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Representation.character, map_mul ρ _ u]`. Establish `h2` using `h1 1`. Simplify using `only [mul_one, Representation.char_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2`. Establish `h3` using `h1 u`.

Apply `hj` to reduce the goal to its premises. Simplify using `only [map_mul, map_sum, map_natCast]`. Simplify using `only [hρ] at h2 h3`. Rewrite using `[h3, ← mul_assoc, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_conj_char {χ : G → K} (h : IsAbsIrrChar χ) (s u : G) :
    (∑ g, χ (g * s * g⁻¹ * u)) * χ 1 = (Fintype.card G : K) * (χ s * χ u) := by
  classical
  obtain ⟨n, ρ, hi, hρ⟩ := h
  let j := algebraMap K (AlgebraicClosure K)
  have hj : Function.Injective j := j.injective
  set T : Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K) := ∑ g, ρ (g * s * g⁻¹) with hT
  have hc : ∀ g v, T (ρ g v) = ρ g (T v) := by
    intro g v
    simp only [hT, LinearMap.sum_apply, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft g)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    simp only [Equiv.coe_mulLeft]
    group
  obtain ⟨c, hcT⟩ := schur_scalar ρ T hc
  have h1 : ∀ u : G, ∑ g, ρ.character (g * s * g⁻¹ * u) = c * ρ.character u := by
    intro u
    have : LinearMap.trace _ _ (T * ρ u) = c * ρ.character u := by
      rw [hcT]; simp [Representation.character, Module.End.mul_eq_comp]
    rw [← this, hT, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.character, map_mul ρ _ u]
  have h2 := h1 1
  simp only [mul_one, Representation.char_conj, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h2
  have h3 := h1 u
  apply hj
  simp only [map_mul, map_sum, map_natCast]
  simp only [hρ] at h2 h3
  rw [h3, ← mul_assoc, h2]
  ring

/- English proof (translation)
Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `u`. Establish `e : ∀ g : G, (MonoidAlgebra.single g (1 : K) * MonoidAlgebra.single s a * MonoidAlgebra.single g⁻¹ (1 : K) * chiIdem χ).coeff u = a * (χ 1 / (Fintype.card G : K)) * χ (g * s * g⁻¹ * u⁻¹)`. Introduce `g`. Rewrite using `[MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, coeff_mul_fin, Finset.sum_eq_single (g * s * g⁻¹)]`.

Rewrite using `[coeff_chiIdem]`. Establish `: χ ((g * s * g⁻¹)⁻¹ * u)⁻¹ = χ (g * s * g⁻¹ * u⁻¹)`. Rewrite using `[← h.conj u]`. Use `congr 1`. Use `group`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Introduce `b _ hb`. Rewrite using `[MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hb, zero_mul]`.

Introduce `hh`. Conclude with `absurd (Finset.mem_univ _) hh`. Rewrite using `[MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, Finsupp.smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_congr rfl fun g _ => e g, ← Finset.mul_sum, coeff_chiIdem, smul_eq_mul, smul_eq_mul]`. Use `sum_conj_char h s u⁻¹` as an intermediate fact. Take the linear combination `(a * (χ 1 / (Fintype.card G : K))) * this`.
-/
theorem sum_conj_mul_chiIdem {χ : G → K} (h : IsAbsIrrChar χ) (s : G) (a : K) :
    χ 1 • ∑ g : G, MonoidAlgebra.single g (1 : K) * MonoidAlgebra.single s a * MonoidAlgebra.single g⁻¹ (1 : K) * chiIdem χ =
      ((Fintype.card G : K) * (a * χ s)) • chiIdem χ := by
  classical
  apply MonoidAlgebra.ext
  ext u
  have e : ∀ g : G, (MonoidAlgebra.single g (1 : K) * MonoidAlgebra.single s a * MonoidAlgebra.single g⁻¹ (1 : K) *
      chiIdem χ).coeff u = a * (χ 1 / (Fintype.card G : K)) * χ (g * s * g⁻¹ * u⁻¹) := by
    intro g
    rw [MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, coeff_mul_fin,
      Finset.sum_eq_single (g * s * g⁻¹)]
    · rw [coeff_chiIdem]
      have : χ ((g * s * g⁻¹)⁻¹ * u)⁻¹ = χ (g * s * g⁻¹ * u⁻¹) := by
        rw [← h.conj u]; congr 1; group
      rw [this]; simp; ring
    · intro b _ hb
      rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_of_ne hb, zero_mul]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  rw [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, Finsupp.smul_apply,
    MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_congr rfl fun g _ => e g, ← Finset.mul_sum,
    coeff_chiIdem, smul_eq_mul, smul_eq_mul]
  have := sum_conj_char h s u⁻¹
  linear_combination (a * (χ 1 / (Fintype.card G : K))) * this

open Classical in

def typeSum (P : Subgroup G) (ψ : P →* Kˣ) (χ : G → K) : K := ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K)

/- English proof (translation)
Establish `hN : ((Fintype.card G : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `hP : ((Nat.card P : ℕ) : K) ≠ 0` using `Nat.cast_ne_zero.mpr Nat.card_pos.ne'`. Establish `key : χ 1 • ∑ g : G, MonoidAlgebra.single g (1 : K) * (lvlIdem P ψ * (MonoidAlgebra.single g⁻¹ (1 : K) * chiIdem χ)) = ((Fintype.card G : K) * ((Nat.card P : K)⁻¹ * typeSum P ψ χ)) • chiIdem χ`. Unfold `lvlIdem typeSum`. Simplify using `only [Finset.sum_mul, Finset.mul_sum, ← mul_assoc (MonoidAlgebra.single _ (1 : K))]`.

Rewrite using `[Finset.sum_comm, Finset.smul_sum, Finset.sum_smul]`. Use `Finset.sum_congr (by congr 1) fun k _ => ?_` and prove the remaining obligations. Use `sum_conj_mul_chiIdem h (k : G) ((Nat.card P : K)⁻¹ * ((ψ k⁻¹ : Kˣ) : K))` as an intermediate fact. Simplify using `only [mul_assoc] at this ⊢`. Rewrite using `[this, map_inv]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : (Fintype.card G : K) * ((Nat.card P : K)⁻¹ * typeSum P ψ χ) ≠ 0` using `mul_ne_zero hN (mul_ne_zero (inv_ne_zero hP) hne)`. Use `⟨((Fintype.card G : K) * ((Nat.card P : K)⁻¹ * typeSum P ψ χ))⁻¹ * χ 1, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, key, smul_smul, inv_mul_cancel₀ hc, one_smul]`.
-/
theorem chiIdem_eq_sum {χ : G → K} (h : IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ) (hne : typeSum P ψ χ ≠ 0) :
    ∃ c : K, chiIdem χ =
      c • ∑ g : G, MonoidAlgebra.single g (1 : K) * (lvlIdem P ψ * (MonoidAlgebra.single g⁻¹ (1 : K) * chiIdem χ)) := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hP : ((Nat.card P : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have key : χ 1 • ∑ g : G, MonoidAlgebra.single g (1 : K) * (lvlIdem P ψ * (MonoidAlgebra.single g⁻¹ (1 : K) * chiIdem χ)) =
      ((Fintype.card G : K) * ((Nat.card P : K)⁻¹ * typeSum P ψ χ)) • chiIdem χ := by
    unfold lvlIdem typeSum
    simp only [Finset.sum_mul, Finset.mul_sum, ← mul_assoc (MonoidAlgebra.single _ (1 : K))]
    rw [Finset.sum_comm, Finset.smul_sum, Finset.sum_smul]
    refine Finset.sum_congr (by congr 1) fun k _ => ?_
    have := sum_conj_mul_chiIdem h (k : G) ((Nat.card P : K)⁻¹ * ((ψ k⁻¹ : Kˣ) : K))
    simp only [mul_assoc] at this ⊢
    rw [this, map_inv]
    congr 1
    ring
  have hc : (Fintype.card G : K) * ((Nat.card P : K)⁻¹ * typeSum P ψ χ) ≠ 0 :=
    mul_ne_zero hN (mul_ne_zero (inv_ne_zero hP) hne)
  refine ⟨((Fintype.card G : K) * ((Nat.card P : K)⁻¹ * typeSum P ψ χ))⁻¹ * χ 1, ?_⟩
  rw [mul_smul, key, smul_smul, inv_mul_cancel₀ hc, one_smul]

end GroupAlgebra

section Modules

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V]

omit [CharZero K] in
/- English proof (translation)
Use `conv_lhs => rw [eq_sum_single a]`. Simplify using `[map_sum, LinearMap.sum_apply]`.
-/
theorem asAlg_eq_sum (r : Representation K G V) (a : MonoidAlgebra K G) (x : V) :
    r.asAlgebraHom a x = ∑ g : G, a.coeff g • r g x := by
  conv_lhs => rw [eq_sum_single a]
  simp [map_sum, LinearMap.sum_apply]

omit [CharZero K] in
/- English proof (translation)
Rewrite using `[asAlg_eq_sum]`. Conclude with `Z.sum_mem fun g _ => Z.smul_mem _ (hZ g x hx)`.
-/
theorem asAlg_mem (r : Representation K G V) {Z : Submodule K V} (hZ : ∀ g, ∀ x ∈ Z, r g x ∈ Z)
    (a : MonoidAlgebra K G) {x : V} (hx : x ∈ Z) : r.asAlgebraHom a x ∈ Z := by
  rw [asAlg_eq_sum]
  exact Z.sum_mem fun g _ => Z.smul_mem _ (hZ g x hx)

omit [CharZero K] in
/- English proof (translation)
Rewrite using `[asAlg_eq_sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun g _ => by rw [map_smulₛₗ, hι]`.
-/
theorem semi_asAlg {σ : K →+* ℂ} {E : Type} [AddCommGroup E] [Module ℂ E] (r : Representation K G V)
    (ρ : Representation ℂ G E) (ι : V →ₛₗ[σ] E) (hι : ∀ g x, ι (r g x) = ρ g (ι x)) (a : MonoidAlgebra K G) (x : V) :
    ι (r.asAlgebraHom a x) = ∑ g : G, σ (a.coeff g) • ρ g (ι x) := by
  rw [asAlg_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smulₛₗ, hι]

/- English proof (translation)
Introduce and unpack `x ⟨hxZ, w, hw⟩`. Establish `hidem` using `idemOf_mul_self X hX`. Establish `hcen` using `idemOf_central X hX`. Establish `he : r.asAlgebraHom (idemOf X) x = x`. Rewrite using `[← hw, ← Module.End.mul_apply, ← map_mul, goodAt, ← mul_assoc, hidem]`.

Establish `hg : r.asAlgebraHom (goodAt X P' ψ') x = x`. Rewrite using `[← hw, ← Module.End.mul_apply, ← map_mul, goodAt, mul_assoc, ← mul_assoc (lvlIdem P' ψ'), hcen, mul_assoc, lvlIdem_idem, ← mul_assoc, hidem]`. Set `S : Submodule K V` to `{ carrier := {y | ∃ y₀ ∈ Z₀, ι₀ y₀ = ι y} add_mem' := by`. Introduce and unpack `a b ⟨a₀, ha, ha'⟩ ⟨b₀, hb, hb'⟩`. Conclude with `⟨a₀ + b₀, Z₀.add_mem ha hb, by rw [map_add, map_add, ha', hb']⟩`.

Use the proof step `zero_mem' := ⟨0, Z₀.zero_mem, by simp⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨a₀, ha, ha'⟩`. Conclude with `⟨c • a₀, Z₀.smul_mem c ha, by rw [map_smulₛₗ, map_smulₛₗ, ha']⟩ }`. Establish `hS : ∀ g, ∀ y ∈ S, r g y ∈ S`.

Introduce and unpack `g y ⟨y₀, hy, hy'⟩`. Conclude with `⟨r₀ g y₀, hZ₀ g _ hy, by rw [hι, hι₀, hy']⟩`. Establish `hxS : x ∈ S`. Rewrite using `[← he, idemOf, map_sum, LinearMap.sum_apply]`. Use `S.sum_mem fun χ hχ => ?_` and prove the remaining obligations.

Take `⟨c, hc⟩` from `chiIdem_eq_sum (hX χ hχ) P ψ (hgen χ hχ)`. Rewrite using `[hc, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply]`. Use `S.smul_mem c (S.sum_mem fun g _ => ?_)` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply]`. Use `asAlg_mem r hS _ (h0 _ ⟨asAlg_mem r hZ _ hxZ, ?_⟩)` and prove the remaining obligations.

Use `⟨r.asAlgebraHom (MonoidAlgebra.single g⁻¹ (1 : K) * chiIdem χ) x, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← he]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hcen, goodAt, mul_assoc]`. Take `⟨x₀, hx₀, hx₀'⟩` from `hxS`. Use `⟨r₀.asAlgebraHom (goodAt X P' ψ') x₀, ⟨asAlg_mem r₀ hZ₀ _ hx₀, x₀, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[semi_asAlg r₀ ρ ι₀ hι₀, hx₀', ← semi_asAlg r ρ ι hι, hg]`.
-/
theorem image_le_of_type {V₀ : Type} [AddCommGroup V₀] [Module K V₀] {σ : K →+* ℂ} {E : Type} [AddCommGroup E] [Module ℂ E]
    (r : Representation K G V) (r₀ : Representation K G V₀) (ρ : Representation ℂ G E)
    (ι : V →ₛₗ[σ] E) (ι₀ : V₀ →ₛₗ[σ] E) (hι : ∀ g x, ι (r g x) = ρ g (ι x)) (hι₀ : ∀ g x, ι₀ (r₀ g x) = ρ g (ι₀ x))
    (Z : Submodule K V) (Z₀ : Submodule K V₀) (hZ : ∀ g, ∀ x ∈ Z, r g x ∈ Z) (hZ₀ : ∀ g, ∀ x ∈ Z₀, r₀ g x ∈ Z₀)
    (X : Finset (G → K)) (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (P : Subgroup G) (ψ : P →* Kˣ)
    (hgen : ∀ χ ∈ X, typeSum P ψ χ ≠ 0)
    (h0 : ∀ y ∈ Z ⊓ LinearMap.range (r.asAlgebraHom (goodAt X P ψ)), ∃ y₀ ∈ Z₀, ι₀ y₀ = ι y)
    (P' : Subgroup G) (ψ' : P' →* Kˣ) :
    ∀ x ∈ Z ⊓ LinearMap.range (r.asAlgebraHom (goodAt X P' ψ')),
      ∃ x₀ ∈ Z₀ ⊓ LinearMap.range (r₀.asAlgebraHom (goodAt X P' ψ')), ι₀ x₀ = ι x := by
  classical
  rintro x ⟨hxZ, w, hw⟩
  have hidem := idemOf_mul_self X hX
  have hcen := idemOf_central X hX
  have he : r.asAlgebraHom (idemOf X) x = x := by
    rw [← hw, ← Module.End.mul_apply, ← map_mul, goodAt, ← mul_assoc, hidem]
  have hg : r.asAlgebraHom (goodAt X P' ψ') x = x := by
    rw [← hw, ← Module.End.mul_apply, ← map_mul, goodAt, mul_assoc, ← mul_assoc (lvlIdem P' ψ'), hcen, mul_assoc,
      lvlIdem_idem, ← mul_assoc, hidem]

  let S : Submodule K V :=
    { carrier := {y | ∃ y₀ ∈ Z₀, ι₀ y₀ = ι y}
      add_mem' := by
        rintro a b ⟨a₀, ha, ha'⟩ ⟨b₀, hb, hb'⟩
        exact ⟨a₀ + b₀, Z₀.add_mem ha hb, by rw [map_add, map_add, ha', hb']⟩
      zero_mem' := ⟨0, Z₀.zero_mem, by simp⟩
      smul_mem' := by
        rintro c a ⟨a₀, ha, ha'⟩
        exact ⟨c • a₀, Z₀.smul_mem c ha, by rw [map_smulₛₗ, map_smulₛₗ, ha']⟩ }
  have hS : ∀ g, ∀ y ∈ S, r g y ∈ S := by
    rintro g y ⟨y₀, hy, hy'⟩
    exact ⟨r₀ g y₀, hZ₀ g _ hy, by rw [hι, hι₀, hy']⟩
  have hxS : x ∈ S := by
    rw [← he, idemOf, map_sum, LinearMap.sum_apply]
    refine S.sum_mem fun χ hχ => ?_
    obtain ⟨c, hc⟩ := chiIdem_eq_sum (hX χ hχ) P ψ (hgen χ hχ)
    rw [hc, map_smul, LinearMap.smul_apply, map_sum, LinearMap.sum_apply]
    refine S.smul_mem c (S.sum_mem fun g _ => ?_)
    rw [map_mul, Module.End.mul_apply]
    refine asAlg_mem r hS _ (h0 _ ⟨asAlg_mem r hZ _ hxZ, ?_⟩)
    refine ⟨r.asAlgebraHom (MonoidAlgebra.single g⁻¹ (1 : K) * chiIdem χ) x, ?_⟩
    conv_rhs => rw [← he]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hcen, goodAt, mul_assoc]
  obtain ⟨x₀, hx₀, hx₀'⟩ := hxS
  refine ⟨r₀.asAlgebraHom (goodAt X P' ψ') x₀, ⟨asAlg_mem r₀ hZ₀ _ hx₀, x₀, rfl⟩, ?_⟩
  rw [semi_asAlg r₀ ρ ι₀ hι₀, hx₀', ← semi_asAlg r ρ ι hι, hg]

end Modules

section Coordinates

variable {K : Type} [Field K] [NumberField K] [StarRing K]

/- English proof (translation)
Establish `hop : ∀ (a : MonoidAlgebra K G) (φ : B.S.Forms), B.S.gaOp B.r a φ = B.r.asAlgebraHom a φ`. Introduce `a φ`. Rewrite using `[asAlg_eq_sum, CSD.gaOp, LinearMap.sum_apply]`. Both sides reduce to the same expression. Establish `hV : LinearMap.range (B.vE ℓ).mulVecLin = LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin` using `(image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2`.

Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Use `⟨(B.mem_goodPart_iff ℓ Z _).1 (B.zE_mem ℓ Z y), ?_⟩` and prove the remaining obligations. Establish `: (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y) ∈ LinearMap.range (B.vE ℓ).mulVecLin` using `⟨_, rfl⟩`.

Rewrite `this` using `[hV]`. Take `⟨u, hu⟩` from `this`. Use `⟨B.S.basis.equivFun.symm u, ?_⟩` and prove the remaining obligations. Rewrite using `[B.toF_apply, ← hu, ← hop, LinearEquiv.eq_symm_apply, ← CSD.gaMat_mulVec_equivFun, LinearEquiv.apply_symm_apply]`. Both sides reduce to the same expression.

Introduce and unpack `⟨hZ, w, hw⟩`. Establish `: B.S.basis.equivFun φ ∈ LinearMap.range (B.vE ℓ).mulVecLin`. Rewrite using `[hV]`. Use `⟨B.S.basis.equivFun w, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun, hop, hw]`.

Take `⟨u, hu⟩` from `this`. Rewrite `hu` using `[Matrix.mulVecLin_apply]`. Establish `hu0 : u ∈ B.Z0 ℓ Z`. Rewrite using `[BlockDat.Z0, B.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]`. Conclude with `hZ`.

Take `⟨y, hy⟩` from `B.exists_zE ℓ Z hu0`. Conclude with `⟨y, by rw [B.toF_apply, hy, hu, LinearEquiv.symm_apply_apply]⟩`.
-/
theorem range_toF {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G)
    (Z : Submodule K B.S.Forms) :
    LinearMap.range (B.toF ℓ Z) = Z ⊓ LinearMap.range (B.r.asAlgebraHom (goodAt ℓ.X ℓ.P ℓ.ψ)) := by
  have hop : ∀ (a : MonoidAlgebra K G) (φ : B.S.Forms), B.S.gaOp B.r a φ = B.r.asAlgebraHom a φ := by
    intro a φ
    rw [asAlg_eq_sum, CSD.gaOp, LinearMap.sum_apply]
    rfl
  have hV : LinearMap.range (B.vE ℓ).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
  ext φ
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(B.mem_goodPart_iff ℓ Z _).1 (B.zE_mem ℓ Z y), ?_⟩
    have : (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y) ∈ LinearMap.range (B.vE ℓ).mulVecLin := ⟨_, rfl⟩
    rw [hV] at this
    obtain ⟨u, hu⟩ := this
    refine ⟨B.S.basis.equivFun.symm u, ?_⟩
    rw [B.toF_apply, ← hu, ← hop, LinearEquiv.eq_symm_apply, ← CSD.gaMat_mulVec_equivFun,
      LinearEquiv.apply_symm_apply]
    rfl
  · rintro ⟨hZ, w, hw⟩
    have : B.S.basis.equivFun φ ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
      rw [hV]
      refine ⟨B.S.basis.equivFun w, ?_⟩
      rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun, hop, hw]
    obtain ⟨u, hu⟩ := this
    rw [Matrix.mulVecLin_apply] at hu
    have hu0 : u ∈ B.Z0 ℓ Z := by
      rw [BlockDat.Z0, B.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
      exact hZ
    obtain ⟨y, hy⟩ := B.exists_zE ℓ Z hu0
    exact ⟨y, by rw [B.toF_apply, hy, hu, LinearEquiv.symm_apply_apply]⟩

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

/- English proof (translation)
Use `conv_rhs => rw [← Finset.univ_sum_single x]`. Rewrite using `[CxData.iC, lin_apply, map_sum, map_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: (Pi.single k (x k) : Fin _ → K) = x k • Pi.single k 1`. Apply the tactic sequence `funext i; by_cases hi : i = k <;> simp [hi]`.

Rewrite using `[this, map_smul, map_smulₛₗ, map_smul]`. Both sides reduce to the same expression.
-/
theorem iC_cpt (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  classical
  conv_rhs => rw [← Finset.univ_sum_single x]
  rw [CxData.iC, lin_apply, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (x k) : Fin _ → K) = x k • Pi.single k 1 := by
    funext i; by_cases hi : i = k <;> simp [hi]
  rw [this, map_smul, map_smulₛₗ, map_smul]
  rfl

/- English proof (translation)
Introduce and unpack `_ ⟨x, rfl⟩`. Use `⟨_, ⟨(X.rowMat cr b t).mulVec x, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← iC_cpt, ← iC_cpt, X.key_row cr b h2 hr]`.
-/
theorem image_le_of_rat (h2 : X.H2 cr b) (hr : X.RATmu cr b) (t : Bs.Tup) :
    ∀ y ∈ LinearMap.range (cr.toR X.zs b t), ∃ y₀ ∈ LinearMap.range (cr.toR X.zs b Bs.μ0),
      X.Θ Bs.μ0 (X.jR Bs.μ0 y₀) = X.Θ t (X.jR t y) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨_, ⟨(X.rowMat cr b t).mulVec x, rfl⟩, ?_⟩
  rw [← iC_cpt, ← iC_cpt, X.key_row cr b h2 hr]

/- English proof (translation)
Introduce `t i k`. Take `⟨_, ⟨x₀, rfl⟩, hx⟩` from `h t _ ⟨Pi.single k 1, rfl⟩`. Establish `h1 : X.iC cr b Bs.μ0 (cpt Bs.v0.embedding x₀) = X.iC cr b t (Pi.single k 1)`. Rewrite using `[iC_cpt, hx, CxData.iC, lin_single]`. Establish `h2 : solve (X.iC cr b Bs.μ0) (X.iC cr b t (Pi.single k 1)) = cpt Bs.v0.embedding x₀` using `hinj ((solve_spec _ ⟨_, h1⟩).trans h1.symm)`.

Conclude with `⟨x₀ i, by simp only [CxData.rowMatC, relMat, Matrix.of_apply, h2, cpt]⟩`.
-/
theorem rat_of_image_le (hinj : Function.Injective (X.iC cr b Bs.μ0))
    (h : ∀ t, ∀ y ∈ LinearMap.range (cr.toR X.zs b t), ∃ y₀ ∈ LinearMap.range (cr.toR X.zs b Bs.μ0),
      X.Θ Bs.μ0 (X.jR Bs.μ0 y₀) = X.Θ t (X.jR t y)) : X.RATmu cr b := by
  intro t i k
  obtain ⟨_, ⟨x₀, rfl⟩, hx⟩ := h t _ ⟨Pi.single k 1, rfl⟩
  have h1 : X.iC cr b Bs.μ0 (cpt Bs.v0.embedding x₀) = X.iC cr b t (Pi.single k 1) := by
    rw [iC_cpt, hx, CxData.iC, lin_single]
  have h2 : solve (X.iC cr b Bs.μ0) (X.iC cr b t (Pi.single k 1)) = cpt Bs.v0.embedding x₀ :=
    hinj ((solve_spec _ ⟨_, h1⟩).trans h1.symm)
  exact ⟨x₀ i, by simp only [CxData.rowMatC, relMat, Matrix.of_apply, h2, cpt]⟩

end Coordinates

section Family

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  {A : FamIn K G Pl0 T m}

def ThetaEquivariant (X : CxData A.fam.amb) (ρ : Representation ℂ G X.EE) : Prop :=
  ∃ ρF : ∀ t, Representation ℂ G (X.FC t),
    (∀ t g x, X.jR t (A.leftGroupActionRight t g x) = ρF t g (X.jR t x)) ∧
    (∀ t g x, X.Θ t (ρF t g x) = ρ g (X.Θ t x)) ∧
    ∀ t g y, LinearMap.adjoint (X.Θ t) (ρ g y) = ρF t g (LinearMap.adjoint (X.Θ t) y)

def OneVector (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ χ ∈ X, typeSum P ψ χ = (Nat.card P : K)

def ImageLe (X : CxData A.fam.amb) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ t, ∀ y ∈ LinearMap.range ((A.fam.R t).toF (A.fam.lvl P ψ) (X.Z t)),
    ∃ y₀ ∈ LinearMap.range ((A.fam.R A.μ0).toF (A.fam.lvl P ψ) (X.Z A.μ0)),
      X.Θ A.μ0 (X.jR A.μ0 y₀) = X.Θ t (X.jR t y)

/- English proof (translation)
Take `⟨ρF, hj, hΘ, hup⟩` from `heq`. Establish `hZ : ∀ t g, ∀ x ∈ X.Z t, A.leftGroupActionRight t g x ∈ X.Z t`. Introduce and unpack `t g x ⟨y, hy⟩`. Conclude with `⟨ρ g y, (hup t g y).trans ((congrArg (ρF t g) hy).trans (hj t g x).symm)⟩`. Establish `hι : ∀ t g x, ((X.Θ t).comp (X.jR t)) (A.leftGroupActionRight t g x) = ρ g (((X.Θ t).comp (X.jR t)) x)`.

Introduce `t g x`. Conclude with `(congrArg (X.Θ t) (hj t g x)).trans (hΘ t g _)`. Introduce `t`. Rewrite using `[range_toF, range_toF]`. Use `image_le_of_type (A.leftGroupActionRight t) (A.leftGroupActionRight A.μ0) ρ ((X.Θ t).comp (X.jR t)) ((X.Θ A.μ0).comp (X.jR A.μ0)) (hι t) (hι A.μ0) (X.Z t) (X.Z A.μ0) (hZ t) (hZ A.μ0) A.X hX P ψ hgen ?_ P' ψ'` and prove the remaining obligations.

Introduce `y hy`. Establish `h'` using `h t`. Rewrite `h'` using `[range_toF, range_toF]`. Take `⟨y₀, hy₀, e⟩` from `h' y hy`. Conclude with `⟨y₀, hy₀.1, e⟩`.
-/
theorem imageLe_of_type (hX : ∀ χ ∈ A.X, IsAbsIrrChar χ) (X : CxData A.fam.amb) (ρ : Representation ℂ G X.EE)
    (heq : ThetaEquivariant X ρ) (P : Subgroup G) (ψ : P →* Kˣ) (hgen : ∀ χ ∈ A.X, typeSum P ψ χ ≠ 0)
    (h : ImageLe X P ψ) (P' : Subgroup G) (ψ' : P' →* Kˣ) : ImageLe X P' ψ' := by
  obtain ⟨ρF, hj, hΘ, hup⟩ := heq
  have hZ : ∀ t g, ∀ x ∈ X.Z t, A.leftGroupActionRight t g x ∈ X.Z t := by
    rintro t g x ⟨y, hy⟩
    exact ⟨ρ g y, (hup t g y).trans ((congrArg (ρF t g) hy).trans (hj t g x).symm)⟩
  have hι : ∀ t g x, ((X.Θ t).comp (X.jR t)) (A.leftGroupActionRight t g x) = ρ g (((X.Θ t).comp (X.jR t)) x) := by
    intro t g x
    exact (congrArg (X.Θ t) (hj t g x)).trans (hΘ t g _)
  intro t
  rw [range_toF, range_toF]
  refine image_le_of_type (A.leftGroupActionRight t) (A.leftGroupActionRight A.μ0) ρ ((X.Θ t).comp (X.jR t)) ((X.Θ A.μ0).comp (X.jR A.μ0))
    (hι t) (hι A.μ0) (X.Z t) (X.Z A.μ0) (hZ t) (hZ A.μ0) A.X hX P ψ hgen ?_ P' ψ'
  intro y hy
  have h' := h t
  rw [range_toF, range_toF] at h'
  obtain ⟨y₀, hy₀, e⟩ := h' y hy
  exact ⟨y₀, hy₀.1, e⟩

section Faces

variable (X : CxData A.fam.amb) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

/- English proof (translation)
The claim follows from `image_le_of_rat X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false h2 hr`.
-/
theorem imageLe_of_rat (h2 : X.H2 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false)
    (hr : X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false) : ImageLe X P0 ψ0 :=
  image_le_of_rat X (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) false h2 hr

/- English proof (translation)
Use `rat_of_image_le X _ b h2.1 ?_` and prove the remaining obligations. Consider the cases of `b with`. Consider the case `false => exact h P0 ψ0`. Consider the case `true => exact h P1 ψ1`.
-/
theorem rat_of_imageLe (b : Bool) (h2 : X.H2 (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b)
    (h : ∀ P ψ, ImageLe X P ψ) : X.RATmu (crdOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) b := by
  refine rat_of_image_le X _ b h2.1 ?_
  cases b with
  | false => exact h P0 ψ0
  | true => exact h P1 ψ1

end Faces

/- English proof (translation)
Introduce `χ hχ` and use `by rw [h χ hχ]; exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'`.
-/
theorem OneVector.ne_zero {X : Finset (G → K)} {P : Subgroup G} {ψ : P →* Kˣ} (h : OneVector X P ψ) :
    ∀ χ ∈ X, typeSum P ψ χ ≠ 0 := fun χ hχ => by
  rw [h χ hχ]; exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'

/- English proof (translation)
Introduce `χ hχ`. Take `⟨i, rfl⟩` from `hch χ hχ`. Establish `h` using `hM i`. Unfold `Formalism.MainNotions.PrimeDegreeVariant.nS at h`. Rewrite `h` using `[GlobalTheory.CuspidalIdempotentCharacters.eps_eq_lvlIdem]`.

Conclude with `(GlobalTheory.CuspidalIdempotentCharacters.finrank_eq_one_iff (Tg.tau i) P ψ).1 h`.
-/
theorem one_vector_of_multiplicity_one {X : Finset (G → K)} {P : Subgroup G} {ψ : P →* Kˣ} (Tg : Formalism.MainNotions.PrimeDegreeVariant.GoodSet K G)
    (hch : ∀ χ ∈ X, ∃ i, χ = fun g => LinearMap.trace K (Tg.W i) (Tg.tau i g))
    (hM : Formalism.MainNotions.PrimeDegreeVariant.M1 Tg ⟨P, ψ⟩) : OneVector X P ψ := by
  classical
  intro χ hχ
  obtain ⟨i, rfl⟩ := hch χ hχ
  have h := hM i
  unfold Formalism.MainNotions.PrimeDegreeVariant.nS at h
  rw [GlobalTheory.CuspidalIdempotentCharacters.eps_eq_lvlIdem] at h
  exact (GlobalTheory.CuspidalIdempotentCharacters.finrank_eq_one_iff (Tg.tau i) P ψ).1 h

/- English proof (translation)
Introduce `χ hχ`. Rewrite using `[Finset.mem_singleton.1 hχ]`. Simplify using `only [typeSum, MonoidHom.one_apply, inv_one, Units.val_one, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]`.
-/
example (P : Subgroup G) : OneVector ({fun _ => 1} : Finset (G → K)) P 1 := by
  intro χ hχ
  rw [Finset.mem_singleton.1 hχ]
  classical
  simp only [typeSum, MonoidHom.one_apply, inv_one, Units.val_one, mul_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Nat.card_eq_fintype_card]

end Family

section Concrete

open Formalism.BasicNotions Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def rowSub (R : RealDat D A Ks) (t : T) : Submodule D.what₂.LL (A.fam.amb.FR t) :=
  (LinearMap.range (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A.v0) (R.Th t)))).comap
    (Tw.semi (σ' := A.v0.embedding) (twAt D.what₂.embLL A.v0) R.emb0 (R.jX t))

/- English proof (translation)
Establish `e : ∀ t, (R.toCx F).Z t = rowSub R t` using `fun t => rfl`. Unfold `ImageLe`. Simplify using `only [e]`. Conclude with `Iff.rfl`.
-/
theorem imageLe_iff (R : RealDat D A Ks) (F : Face D A) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) :
    ImageLe (R.toCx F) P ψ ↔
      ∀ t, ∀ y ∈ LinearMap.range ((A.fam.R t).toF (A.fam.lvl P ψ) (rowSub R t)),
        ∃ y₀ ∈ LinearMap.range ((A.fam.R A.μ0).toF (A.fam.lvl P ψ) (rowSub R A.μ0)),
          R.Th A.μ0 (R.jX A.μ0 y₀) = R.Th t (R.jX t y) := by
  have e : ∀ t, (R.toCx F).Z t = rowSub R t := fun t => rfl
  unfold ImageLe
  simp only [e]
  exact Iff.rfl

/- English proof (translation)
The claim follows from `(imageLe_iff R F' P ψ).2 ((imageLe_iff R F P ψ).1 h)`.
-/
theorem imageLe_face (R : RealDat D A Ks) (F F' : Face D A) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ)
    (h : ImageLe (R.toCx F) P ψ) : ImageLe (R.toCx F') P ψ :=
  (imageLe_iff R F' P ψ).2 ((imageLe_iff R F P ψ).1 h)

/- English proof (translation)
The claim follows from `rat_of_imageLe (R.toCx F') F'.P0 F'.ψ0 F'.P1 F'.ψ1 F'.Dc F'.Sp F'.Zsc b h2' fun P ψ => imageLe_face R F F' P ψ (imageLe_of_type hOk.irr (R.toCx F) (R.gEx F) heq F.P0 F.ψ0 hM.ne_zero (imageLe_of_rat (R.toCx F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc h2 hr) P ψ)`.
-/
theorem ratMu_of_base {s : ℕ} (hOk : A.fam.Ok s) (R : RealDat D A Ks) (F F' : Face D A) (b : Bool)
    (hM : OneVector A.X F.P0 F.ψ0) (heq : ThetaEquivariant (R.toCx F) (R.gEx F))
    (h2 : (R.toCx F).H2 F.cr false) (h2' : (R.toCx F').H2 F'.cr b) (hr : (R.toCx F).RATmu F.cr false) :
    (R.toCx F').RATmu F'.cr b :=
  rat_of_imageLe (R.toCx F') F'.P0 F'.ψ0 F'.P1 F'.ψ1 F'.Dc F'.Sp F'.Zsc b h2' fun P ψ =>
    imageLe_face R F F' P ψ (imageLe_of_type hOk.irr (R.toCx F) (R.gEx F) heq F.P0 F.ψ0 hM.ne_zero
      (imageLe_of_rat (R.toCx F) F.P0 F.ψ0 F.P1 F.ψ1 F.Dc F.Sp F.Zsc h2 hr) P ψ)

def principalFace (F : Face D A) : Face D A := ⟨⊥, 1, F.P1, F.ψ1, F.Dc, F.Sp, F.Zsc⟩

/- English proof (translation)
The claim follows from `ratMu_of_base hOk R F (principalFace F) false hM heq h2 h2' hr`.
-/
theorem ratMu_principal {s : ℕ} (hOk : A.fam.Ok s) (R : RealDat D A Ks) (F : Face D A)
    (hM : OneVector A.X F.P0 F.ψ0) (heq : ThetaEquivariant (R.toCx F) (R.gEx F))
    (h2 : (R.toCx F).H2 F.cr false) (h2' : (R.toCx (principalFace F)).H2 (principalFace F).cr false)
    (hr : (R.toCx F).RATmu F.cr false) :
    (R.toCx (principalFace F)).RATmu (principalFace F).cr false :=
  ratMu_of_base hOk R F (principalFace F) false hM heq h2 h2' hr

/- English proof (translation)
Introduce `b` and use `ratMu_of_base hOk R F F b hM heq (h2 false) (h2 b) hr`.
-/
theorem lRatMu_of_base {s : ℕ} (hOk : A.fam.Ok s) (R : RealDat D A Ks) (F : Face D A)
    (hM : OneVector A.X F.P0 F.ψ0) (heq : ThetaEquivariant (R.toCx F) (R.gEx F))
    (h2 : R.LIota F) (hr : (R.toCx F).RATmu F.cr false) : R.LRatMu F :=
  fun b => ratMu_of_base hOk R F F b hM heq (h2 false) (h2 b) hr

def GoodInduced (R : RealDat D A Ks) : Prop :=
  ∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar R.Pg D.R.r D.what₂.embLL fun g => χ (R.eG.symm g)

/- English proof (translation)
Take `⟨ψ, hψ, hP, -⟩` from `hlev`. Introduce `χ hχ`. Establish `h` using `hW D.host.E R.Pg D.R.r ℂ (RingHom.id ℂ) ψ hψ (fun g => D.what₂.embLL (χ (R.eG.symm g))) (hind χ hχ)`. Rewrite `h` using `[← hP]`. Set `e : (R.levR F false).H ≃ F.P0` to `R.eG.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl`.

Apply `D.what₂.embLL.injective` to reduce the goal to its premises. Rewrite using `[map_natCast, ← Nat.card_congr e, ← h, typeSum, map_sum]`. Unfold `GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum`. Use `letI := GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH (R.levR F false)`. Use `(Fintype.sum_equiv e _ _ fun x => ?_).symm` and prove the remaining obligations.

Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem oneVector_of_whittaker (R : RealDat D A Ks) (F : Face D A) (hW : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector)
    (hlev : R.grp_levels F) (hind : GoodInduced R) : OneVector A.X F.P0 F.ψ0 := by
  classical
  obtain ⟨ψ, hψ, hP, -⟩ := hlev
  intro χ hχ
  have h := hW D.host.E R.Pg D.R.r ℂ (RingHom.id ℂ) ψ hψ (fun g => D.what₂.embLL (χ (R.eG.symm g))) (hind χ hχ)
  rw [← hP] at h
  let e : (R.levR F false).H ≃ F.P0 := R.eG.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl
  apply D.what₂.embLL.injective
  rw [map_natCast, ← Nat.card_congr e, ← h, typeSum, map_sum]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum
  letI := GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH (R.levR F false)
  refine (Fintype.sum_equiv e _ _ fun x => ?_).symm
  rw [map_mul]
  rfl

/- English proof (translation)
The claim follows from `ratMu_principal hOk R F (oneVector_of_whittaker R F hW hlev hind) heq h2 h2' hr`.
-/
theorem ratMu_principal_of_whittaker {s : ℕ} (hOk : A.fam.Ok s) (R : RealDat D A Ks) (F : Face D A)
    (hW : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector) (hlev : R.grp_levels F) (hind : GoodInduced R)
    (heq : ThetaEquivariant (R.toCx F) (R.gEx F))
    (h2 : (R.toCx F).H2 F.cr false) (h2' : (R.toCx (principalFace F)).H2 (principalFace F).cr false)
    (hr : (R.toCx F).RATmu F.cr false) :
    (R.toCx (principalFace F)).RATmu (principalFace F).cr false :=
  ratMu_principal hOk R F (oneVector_of_whittaker R F hW hlev hind) heq h2 h2' hr

end Concrete

end GlobalTheory.OneForm
