import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismFiniteness.FiniteOfIntegralBound

noncomputable section

namespace PI.AutLzFinite.SlopeTestRemainingChoices

open Formalism.BasicNotions NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

def indSet (X P : Submodule E S.V) (z : S.V) (Λ : Submodule (𝓞 E) S.V) :
    Set ((P ⧸ X.comap P.subtype) → (P ⧸ X.comap P.subtype)) :=
  {φ | ∃ γ : S.V ≃ₗ[E] S.V, (∀ x y, S.hT (γ x) (γ y) = S.hT x y) ∧ γ z = z ∧ (∀ x ∈ Λ, γ x ∈ Λ) ∧
    (∀ x ∈ P, γ x ∈ P) ∧
    ∀ (x : P) (hx : γ x.1 ∈ P), φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨γ x.1, hx⟩}

/- English proof (translation)
Use `set Xc := X.comap P.subtype`. Establish `hzz0 : S.hT z z ≠ 0`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Introduce `h`. Use `hzz τ` as an intermediate fact.

Rewrite `this` using `[h, map_zero]`. Simplify using `at this`. Use `set bB := Module.finBasis E P`. Establish `hd : ∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧ d • (bB i : S.V) ∈ Λ` using `fun i => exists_smul_mem Λ hΛ _`. Use `choose d hd0 hdΛ using hd`.

Establish `hd0' : ∀ i, algebraMap (𝓞 E) E (d i) ≠ 0` using `fun i => by`. Rewrite using `[ne_eq, ← map_zero (algebraMap (𝓞 E) E), (IsFractionRing.injective (𝓞 E) E).eq_iff]`. Conclude with `hd0 i`. Use `set b := bB.unitsSMul (fun i => Units.mk0 _ (hd0' i))`. Establish `hbΛ : ∀ i, ((b i : P) : S.V) ∈ Λ`.

Introduce `i`. Simplify using `only [b, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, algebraMap_smul]`. Conclude with `hdΛ i`. Use `set cf : Fin (Module.finrank E P) → ℝ := fun i => ∑ τ : E →+* ℂ, |(τ (mj S z (b i : S.V) (b i : S.V))).re| with hcf`. Use `set C : ℝ := ∑ i, cf i with hCdef`.

Establish `hC : ∀ i (τ : E →+* ℂ), (τ (mj S z (b i : S.V) (b i : S.V))).re ≤ C`. Introduce `i τ`. Establish `h1 : |(τ (mj S z (b i : S.V) (b i : S.V))).re| ≤ cf i` using `Finset.single_le_sum (f := fun (τ : E →+* ℂ) => |(τ (mj S z (b i : S.V) (b i : S.V))).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)`. Establish `h2 : cf i ≤ C` using `Finset.single_le_sum (f := cf) (fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)`. Conclude with `(le_abs_self _).trans (h1.trans h2)`.

Establish `hC0 : 0 ≤ C` using `Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _`. Use `set Y : Set (P ⧸ Xc) := {q | ∃ y : P, (y : S.V) ∈ Λ ∧ (∀ τ : E →+* ℂ, (τ (mj S z y y)).re ≤ C) ∧ q = Submodule.Quotient.mk y}`. Set `mjR : Fin (Module.finrank E P) → S.V →ₗ[E] E` to `fun j => S.hT (b j : S.V) - (2 / S.hT z z * S.hT (b j : S.V) z) • S.hT z`. Establish `hmjR : ∀ j y, mjR j y = mj S z (b j : S.V) y`. Introduce `j y`.

Simplify using `only [mjR, mj, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Set `Pm : P →ₗ[E] (Fin (Module.finrank E P) → E)` to `LinearMap.pi fun j => (mjR j).comp P.subtype`. Establish `hPm : ∀ (y : P) j, Pm y j = mj S z (b j : S.V) y`. Introduce `y j`.

Simplify using `[Pm, hmjR]`. Establish `hker : Xc ≤ LinearMap.ker Pm`. Introduce `y hy`. Rewrite using `[LinearMap.mem_ker]`. Use function extensionality and compare the values at `j`.

Rewrite using `[hPm]`. Establish `h1 : S.hT (b j : S.V) y = 0`. Rewrite using `[herm_swap, hPX (y : S.V) hy _ (b j).2, star_zero]`. Establish `h2 : S.hT z y = 0` using `by rw [herm_swap, hPX (y : S.V) hy _ hzP, star_zero]`. Simplify using `[mj, h1, h2]`.

Set `g : (P ⧸ Xc) →ₗ[E] (Fin (Module.finrank E P) → E)` to `Xc.liftQ Pm hker`. Establish `hg : Function.Injective g`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `q hq`. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Rewrite `hq` using `[LinearMap.mem_ker, Submodule.liftQ_apply]`. Establish `hw : ∀ j, mj S z (b j : S.V) w = 0` using `fun j => by rw [← hPm, hq]; rfl`. Establish `hall : ∀ v : P, mj S z v w = 0`. Introduce `v`. Establish `hv : v ∈ Submodule.span E (Set.range b)` using `by rw [b.span_eq]; trivial`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨j, rfl⟩ := hx`. Conclude with `hw j`. Consider the case `zero => simpa using mj_smul_left (S := S) z 0 (0 : S.V) w`. Consider the case `add x y _ _ h1 h2 => rw [Submodule.coe_add, mj_add_left, h1, h2, add_zero]`.

Consider the case `smul c x _ h => rw [Submodule.coe_smul, mj_smul_left, h, mul_zero]`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hw0` using `(mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) w w.2).2 (by rw [hall w]; simp)`. Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`. Conclude with `hw0`.

Establish `hYfin : Y.Finite`. Apply `Set.Finite.of_finite_image (f := g) _ hg.injOn` to reduce the goal to its premises. Apply `(Set.Finite.pi (t := fun _ => {a : E | IsIntegral ℤ (S.hT z z * a) ∧ ∀ τ : E →+* ℂ, ‖τ a‖ ≤ C}) fun _ => finite_of_integral_bound _ hzz0 C).subset` to reduce the goal to its premises. Introduce and unpack `_ ⟨q, ⟨y, hyΛ, hyC, rfl⟩, rfl⟩`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies]`.

Introduce `j`. Establish `hgj : g (Submodule.Quotient.mk y) j = mj S z (b j : S.V) y`. Simplify using `only [g, Submodule.liftQ_apply]`. Conclude with `hPm y j`. Rewrite using `[hgj]`.

Prove the components needed by the constructor for the conclusion. Establish `e1 : S.hT z z * mj S z (b j : S.V) y = S.hT z z * S.hT (b j : S.V) y - (S.hT (b j : S.V) z * S.hT z y + S.hT (b j : S.V) z * S.hT z y)`. Simplify using `only [mj]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1]`. Use `IsIntegral.sub (IsIntegral.mul (hint _ hzΛ _ hzΛ) (hint _ (hbΛ j) _ hyΛ)) (IsIntegral.add (IsIntegral.mul (hint _ (hbΛ j) _ hzΛ) (hint _ hzΛ _ hyΛ)) (IsIntegral.mul (hint _ (hbΛ j) _ hzΛ) (hint _ hzΛ _ hyΛ)))` and prove the remaining obligations. Introduce `τ`. Establish `hcs` using `mj_cs hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ _ (b j).2 y.2`. Establish `ha` using `(mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ (b j).2).1`.

Establish `hb` using `(mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ y.2).1`. Establish `h1` using `hC j τ`. Establish `h2` using `hyC τ`. Establish `hsq : ‖τ (mj S z (b j : S.V) y)‖ ^ 2 ≤ C ^ 2`. Rewrite using `[Complex.sq_norm]`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) hC0 two_ne_zero).mp hsq`. Apply `Set.Finite.of_finite_image (f := fun φ i => φ (Submodule.Quotient.mk (b i)))` to reduce the goal to its premises. Apply `(Set.Finite.pi (t := fun _ => Y) fun _ => hYfin).subset` to reduce the goal to its premises. Introduce and unpack `_ ⟨φ, ⟨γ, hiso, hγz, hγΛ, hγP, hφ⟩, rfl⟩`.

Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies]`. Introduce `i`. Use `⟨⟨γ (b i : S.V), hγP _ (b i).2⟩, hγΛ _ (hbΛ i), fun τ => ?_, hφ _ _⟩` and prove the remaining obligations. Establish `e1 : ∀ x : S.V, S.hT (γ x) z = S.hT x z` using `fun x => by conv_lhs => rw [← hγz]`. Conclude with `hiso x z`.

Establish `e2 : ∀ x : S.V, S.hT z (γ x) = S.hT z x` using `fun x => by conv_lhs => rw [← hγz]`. Conclude with `hiso z x`. Establish `: mj S z (γ (b i : S.V)) (γ (b i : S.V)) = mj S z (b i : S.V) (b i : S.V)`. Simplify using `only [mj, hiso, e1, e2]`. Simplify using `only [this]`.

Conclude with `hC i τ`. Introduce and unpack `φ ⟨γ, hiso, hγz, hγΛ, hγP, hφ⟩ φ' ⟨γ', hiso', hγz', hγΛ', hγP', hφ'⟩ heq`. Set `ψ : P →ₗ[E] (P ⧸ Xc)` to `Xc.mkQ ∘ₗ (γ : S.V →ₗ[E] S.V).restrict hγP`. Set `ψ' : P →ₗ[E] (P ⧸ Xc)` to `Xc.mkQ ∘ₗ (γ' : S.V →ₗ[E] S.V).restrict hγP'`. Establish `hψ : ∀ x : P, φ (Submodule.Quotient.mk x) = ψ x` using `fun x => by`.

Rewrite using `[hφ x (hγP _ x.2)]`. Both sides reduce to the same expression. Establish `hψ' : ∀ x : P, φ' (Submodule.Quotient.mk x) = ψ' x` using `fun x => by`. Rewrite using `[hφ' x (hγP' _ x.2)]`. Both sides reduce to the same expression.

Establish `hψψ : ψ = ψ'` using `b.ext fun i => by`. Rewrite using `[← hψ, ← hψ']`. Conclude with `congrFun heq i`. Use function extensionality and compare the values at `q`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`.

Rewrite using `[hψ, hψ', hψψ]`.
-/
theorem indSet_finite (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
    (hzz : ∀ τ : E →+* ℂ, (τ (S.hT z z)).re < 0)
    (hpos : ∀ τ : E →+* ℂ, ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.span E (Λ : Set S.V) = ⊤)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (S.hT x y)) (hzΛ : z ∈ Λ) :
    (indSet X P z Λ).Finite := by
  classical
  set Xc := X.comap P.subtype
  have hzz0 : S.hT z z ≠ 0 := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    intro h; have := hzz τ; rw [h, map_zero] at this; simp at this

  set bB := Module.finBasis E P
  have hd : ∀ i, ∃ d : 𝓞 E, d ≠ 0 ∧ d • (bB i : S.V) ∈ Λ := fun i => exists_smul_mem Λ hΛ _
  choose d hd0 hdΛ using hd
  have hd0' : ∀ i, algebraMap (𝓞 E) E (d i) ≠ 0 := fun i => by
    rw [ne_eq, ← map_zero (algebraMap (𝓞 E) E), (IsFractionRing.injective (𝓞 E) E).eq_iff]
    exact hd0 i
  set b := bB.unitsSMul (fun i => Units.mk0 _ (hd0' i))
  have hbΛ : ∀ i, ((b i : P) : S.V) ∈ Λ := by
    intro i
    simp only [b, Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0,
      algebraMap_smul]
    exact hdΛ i

  set cf : Fin (Module.finrank E P) → ℝ := fun i =>
    ∑ τ : E →+* ℂ, |(τ (mj S z (b i : S.V) (b i : S.V))).re| with hcf
  set C : ℝ := ∑ i, cf i with hCdef
  have hC : ∀ i (τ : E →+* ℂ), (τ (mj S z (b i : S.V) (b i : S.V))).re ≤ C := by
    intro i τ
    have h1 : |(τ (mj S z (b i : S.V) (b i : S.V))).re| ≤ cf i :=
      Finset.single_le_sum (f := fun (τ : E →+* ℂ) => |(τ (mj S z (b i : S.V) (b i : S.V))).re|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
    have h2 : cf i ≤ C := Finset.single_le_sum (f := cf)
      (fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    exact (le_abs_self _).trans (h1.trans h2)
  have hC0 : 0 ≤ C := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

  set Y : Set (P ⧸ Xc) := {q | ∃ y : P, (y : S.V) ∈ Λ ∧
    (∀ τ : E →+* ℂ, (τ (mj S z y y)).re ≤ C) ∧ q = Submodule.Quotient.mk y}

  let mjR : Fin (Module.finrank E P) → S.V →ₗ[E] E := fun j =>
    S.hT (b j : S.V) - (2 / S.hT z z * S.hT (b j : S.V) z) • S.hT z
  have hmjR : ∀ j y, mjR j y = mj S z (b j : S.V) y := by
    intro j y; simp only [mjR, mj, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]; ring
  let Pm : P →ₗ[E] (Fin (Module.finrank E P) → E) := LinearMap.pi fun j => (mjR j).comp P.subtype
  have hPm : ∀ (y : P) j, Pm y j = mj S z (b j : S.V) y := by
    intro y j; simp [Pm, hmjR]
  have hker : Xc ≤ LinearMap.ker Pm := by
    intro y hy
    rw [LinearMap.mem_ker]
    funext j
    rw [hPm]
    have h1 : S.hT (b j : S.V) y = 0 := by
      rw [herm_swap, hPX (y : S.V) hy _ (b j).2, star_zero]
    have h2 : S.hT z y = 0 := by rw [herm_swap, hPX (y : S.V) hy _ hzP, star_zero]
    simp [mj, h1, h2]
  let g : (P ⧸ Xc) →ₗ[E] (Fin (Module.finrank E P) → E) := Xc.liftQ Pm hker
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro q hq
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [LinearMap.mem_ker, Submodule.liftQ_apply] at hq
    have hw : ∀ j, mj S z (b j : S.V) w = 0 := fun j => by rw [← hPm, hq]; rfl
    have hall : ∀ v : P, mj S z v w = 0 := by
      intro v
      have hv : v ∈ Submodule.span E (Set.range b) := by rw [b.span_eq]; trivial
      induction hv using Submodule.span_induction with
      | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hw j
      | zero => simpa using mj_smul_left (S := S) z 0 (0 : S.V) w
      | add x y _ _ h1 h2 => rw [Submodule.coe_add, mj_add_left, h1, h2, add_zero]
      | smul c x _ h => rw [Submodule.coe_smul, mj_smul_left, h, mul_zero]
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have hw0 := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) w w.2).2 (by rw [hall w]; simp)
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact hw0
  have hYfin : Y.Finite := by
    apply Set.Finite.of_finite_image (f := g) _ hg.injOn
    apply (Set.Finite.pi (t := fun _ => {a : E | IsIntegral ℤ (S.hT z z * a) ∧
      ∀ τ : E →+* ℂ, ‖τ a‖ ≤ C}) fun _ => finite_of_integral_bound _ hzz0 C).subset
    rintro _ ⟨q, ⟨y, hyΛ, hyC, rfl⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro j
    have hgj : g (Submodule.Quotient.mk y) j = mj S z (b j : S.V) y := by
      simp only [g, Submodule.liftQ_apply]; exact hPm y j
    rw [hgj]
    constructor
    · have e1 : S.hT z z * mj S z (b j : S.V) y =
          S.hT z z * S.hT (b j : S.V) y - (S.hT (b j : S.V) z * S.hT z y + S.hT (b j : S.V) z * S.hT z y) := by
        simp only [mj]; field_simp; ring
      rw [e1]
      refine IsIntegral.sub (IsIntegral.mul (hint _ hzΛ _ hzΛ) (hint _ (hbΛ j) _ hyΛ))
        (IsIntegral.add (IsIntegral.mul (hint _ (hbΛ j) _ hzΛ) (hint _ hzΛ _ hyΛ))
          (IsIntegral.mul (hint _ (hbΛ j) _ hzΛ) (hint _ hzΛ _ hyΛ)))
    · intro τ
      have hcs := mj_cs hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ _ (b j).2 y.2
      have ha := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ (b j).2).1
      have hb := (mj_pos hstar τ X P hPX z hzP (hzz τ) (hpos τ) _ y.2).1
      have h1 := hC j τ
      have h2 := hyC τ
      have hsq : ‖τ (mj S z (b j : S.V) y)‖ ^ 2 ≤ C ^ 2 := by
        rw [Complex.sq_norm]; nlinarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC0 two_ne_zero).mp hsq

  apply Set.Finite.of_finite_image (f := fun φ i => φ (Submodule.Quotient.mk (b i)))
  · apply (Set.Finite.pi (t := fun _ => Y) fun _ => hYfin).subset
    rintro _ ⟨φ, ⟨γ, hiso, hγz, hγΛ, hγP, hφ⟩, rfl⟩
    simp only [Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    refine ⟨⟨γ (b i : S.V), hγP _ (b i).2⟩, hγΛ _ (hbΛ i), fun τ => ?_, hφ _ _⟩
    have e1 : ∀ x : S.V, S.hT (γ x) z = S.hT x z := fun x => by
      conv_lhs => rw [← hγz]
      exact hiso x z
    have e2 : ∀ x : S.V, S.hT z (γ x) = S.hT z x := fun x => by
      conv_lhs => rw [← hγz]
      exact hiso z x
    have : mj S z (γ (b i : S.V)) (γ (b i : S.V)) = mj S z (b i : S.V) (b i : S.V) := by
      simp only [mj, hiso, e1, e2]
    simp only [this]
    exact hC i τ
  · rintro φ ⟨γ, hiso, hγz, hγΛ, hγP, hφ⟩ φ' ⟨γ', hiso', hγz', hγΛ', hγP', hφ'⟩ heq
    let ψ : P →ₗ[E] (P ⧸ Xc) := Xc.mkQ ∘ₗ (γ : S.V →ₗ[E] S.V).restrict hγP
    let ψ' : P →ₗ[E] (P ⧸ Xc) := Xc.mkQ ∘ₗ (γ' : S.V →ₗ[E] S.V).restrict hγP'
    have hψ : ∀ x : P, φ (Submodule.Quotient.mk x) = ψ x := fun x => by
      rw [hφ x (hγP _ x.2)]; rfl
    have hψ' : ∀ x : P, φ' (Submodule.Quotient.mk x) = ψ' x := fun x => by
      rw [hφ' x (hγP' _ x.2)]; rfl
    have hψψ : ψ = ψ' := b.ext fun i => by
      rw [← hψ, ← hψ']; exact congrFun heq i
    funext q
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [hψ, hψ', hψψ]

end PI.AutLzFinite.SlopeTestRemainingChoices
