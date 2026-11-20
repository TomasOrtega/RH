import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GEquivIntL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd

noncomputable section

namespace GlobalTheory.SatInd

section Transport

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Take `⟨M, rfl⟩` from `hx`. Use `⟨bc (φ.restrict (intL K) (intL K) hφ) M, ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[bc]`.
-/
theorem bc_mem_range_intL_of (φ : K →+* K) (hφ : ∀ x ∈ intL K, φ x ∈ intL K) {n : ℕ}
    (x : GL (Fin n) K) (hx : x ∈ (bc (n := Fin n) (intL K).subtype).range) :
    bc (n := Fin n) φ x ∈ (bc (n := Fin n) (intL K).subtype).range := by
  obtain ⟨M, rfl⟩ := hx
  refine ⟨bc (φ.restrict (intL K) (intL K) hφ) M, ?_⟩
  apply Units.ext
  ext i j
  simp [bc]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[guMap_val]`.
-/
theorem guMap_symm_comp (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hg' : ∀ x, g.symm (σ' x) = σ (g.symm x)) {n : ℕ} (y : GU σ n) :
    guMap g.symm hg' n (guMap g hg n y) = y := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  simp [guMap_val]

/- English proof (translation)
Establish `hs : ∀ x ∈ intL K, (g.symm : K →+* K) x ∈ intL K`. Introduce `x hx`. Rewrite using `[hint]`. Simplify using `using hx`. Simplify using `only [KU, intPts, Subgroup.mem_subgroupOf, Subgroup.mem_inf]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, h⟩`. Conclude with `⟨(guMap g hg n y).2, bc_mem_range_intL_of (g : K →+* K) (fun x hx => (hint x).1 hx) _ h⟩`. Introduce and unpack `⟨-, h⟩`. Use `⟨y.2, ?_⟩` and prove the remaining obligations.

Use `bc_mem_range_intL_of (g.symm : K →+* K) hs _ h` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Simplify using `[bc, guMap_val]`.
-/
theorem mem_KU_iff_guMap (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x))
    (hint : ∀ x, x ∈ intL K ↔ g x ∈ intL K) {n : ℕ} (y : GU σ n) :
    y ∈ KU σ n ↔ guMap g hg n y ∈ KU σ' n := by
  have hs : ∀ x ∈ intL K, (g.symm : K →+* K) x ∈ intL K := by
    intro x hx
    rw [hint]
    simpa using hx
  simp only [KU, intPts, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, h⟩
    exact ⟨(guMap g hg n y).2, bc_mem_range_intL_of (g : K →+* K) (fun x hx => (hint x).1 hx) _ h⟩
  · rintro ⟨-, h⟩
    refine ⟨y.2, ?_⟩
    have := bc_mem_range_intL_of (g.symm : K →+* K) hs _ h
    convert this using 1
    apply Units.ext
    ext i j
    simp [bc, guMap_val]

end Transport

open Classical in

/- English proof (translation)
Introduce `K _ _ g σ σ' hg hint ϖ ϖ' q n m h' hbi hcond α`. Establish `hg' : ∀ x, g.symm (σ' x) = σ (g.symm x)`. Introduce `x`. Apply `g.injective` to reduce the goal to its premises. Rewrite using `[hg]`.

Simplify using the standard rewrite rules. Set `e : GU σ n ≃* GU σ' n` to `{ toFun := guMap g hg n invFun := guMap g.symm hg' n left_inv := fun y => guMap_symm_comp g hg hg' y right_inv := fun y => by`. Use `guMap_symm_comp g.symm hg' (by simpa using hg) y` as an intermediate fact. Simplify using `using this`. Use the proof step `map_mul' := map_mul _ }`.

Establish `he : ∀ y, e y = guMap g hg n y` using `fun _ => rfl`. Set `E : GU σ n ⧸ KU σ n ≃ GU σ' n ⧸ KU σ' n` to `Quotient.congr e.toEquiv (fun a b => by`. Rewrite using `[QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]`. Express the relevant statement in the definitionally equal form `a⁻¹ * b ∈ KU σ n ↔ (e a)⁻¹ * e b ∈ KU σ' n`. Rewrite using `[← map_inv, ← map_mul, he]`.

Conclude with `mem_KU_iff_guMap g hg hint _)`. Unfold `SatU`. Use `finsum_congr (fun a => ?_)` and prove the remaining obligations. Use `congr 1`. Use `set F' : GU σ' n → ℂ := fun y => if ∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) then h' y else 0 with hF'`.

Establish `hinv : ∀ (y : GU σ' n) (k : KU σ' n), F' (y * k) = F' y`. Introduce `y k`. Simplify using `only [hF']`. Establish `hc : (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n, (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n, ((y …`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨u, hu, k', hk', hy⟩`. Use `⟨u, hu, k' * (k : GU σ' n)⁻¹, (KU σ' n).mul_mem hk' ((KU σ' n).inv_mem k.2), ?_⟩` and prove the remaining obligations. Establish `h1 : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((((k : GU σ' n)⁻¹ : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)`. Simplify using `[Matrix.mul_assoc]`. Rewrite using `[h1, hy]`.

Simplify using `[Matrix.mul_assoc]`. Introduce and unpack `⟨u, hu, k', hk', hy⟩`. Use `⟨u, hu, k' * (k : GU σ' n), (KU σ' n).mul_mem hk' k.2, ?_⟩` and prove the remaining obligations. Simplify using `only [Subgroup.coe_mul, Units.val_mul, hy, Matrix.mul_assoc]`. Establish `hh : h' (y * k) = h' y`.

Use `hbi 1 k y` as an intermediate fact. Simplify using `using this`. Simplify using `only [hc, hh]`. Establish `hmk : ∀ x : GU σ n ⧸ KU σ n, F' (E x).out = F' (guMap g hg n x.out)`. Introduce `x`.

Establish `hx : E x = QuotientGroup.mk (guMap g hg n x.out)` using `by conv_lhs => rw [← Quotient.out_eq x]`. Both sides reduce to the same expression. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul (KU σ' n) (guMap g hg n x.out)`. Rewrite using `[hx, hk, hinv]`. Combine the equalities or inequalities in the displayed calculation.

Use `finsum_congr (fun x => ?_)` and prove the remaining obligations. Rewrite using `[hmk, hF']`. Simplify using `only [hcond a x.out]`. Use `_ = ∑ᶠ x' : GU σ' n ⧸ KU σ' n, F' x'.out := finsum_comp_equiv E (f := fun x' => F' x'.out)`.
-/
theorem satU_guMap : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (g : K ≃+* K) {σ σ' : K →+* K} (hg : ∀ x, g (σ x) = σ' (g x)), (∀ x, x ∈ intL K ↔ g x ∈ intL K) → ∀ (ϖ ϖ' : K) (q n m : ℕ) (h' : GU σ' n → ℂ), IsBiInv (KU σ' n) h' → (∀ (a : Fin m → ℤ) (y : GU σ n), (∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔ (∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n, ((guMap g hg n y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))) → ∀ α : Fin m → ℂ, SatU ϖ q (fun y => h' (guMap g hg n y)) α = SatU ϖ' q h' α := by
  intro K _ _ g σ σ' hg hint ϖ ϖ' q n m h' hbi hcond α
  have hg' : ∀ x, g.symm (σ' x) = σ (g.symm x) := by
    intro x
    apply g.injective
    rw [hg]
    simp
  let e : GU σ n ≃* GU σ' n :=
    { toFun := guMap g hg n
      invFun := guMap g.symm hg' n
      left_inv := fun y => guMap_symm_comp g hg hg' y
      right_inv := fun y => by
        have := guMap_symm_comp g.symm hg' (by simpa using hg) y
        simpa using this
      map_mul' := map_mul _ }
  have he : ∀ y, e y = guMap g hg n y := fun _ => rfl
  let E : GU σ n ⧸ KU σ n ≃ GU σ' n ⧸ KU σ' n :=
    Quotient.congr e.toEquiv (fun a b => by
      rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
      change a⁻¹ * b ∈ KU σ n ↔ (e a)⁻¹ * e b ∈ KU σ' n
      rw [← map_inv, ← map_mul, he]
      exact mem_KU_iff_guMap g hg hint _)
  unfold SatU
  refine finsum_congr (fun a => ?_)
  congr 1
  set F' : GU σ' n → ℂ := fun y => if ∃ u : GU σ' n, IsUnipU u ∧ ∃ k ∈ KU σ' n,
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((k : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) then h' y else 0 with hF'
  have hinv : ∀ (y : GU σ' n) (k : KU σ' n), F' (y * k) = F' y := by
    intro y k
    simp only [hF']
    have hc : (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n,
        (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ↔
        (∃ u : GU σ' n, IsUnipU u ∧ ∃ k' ∈ KU σ' n,
        ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          tMat ϖ' n m a * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((k' : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
      constructor
      · rintro ⟨u, hu, k', hk', hy⟩
        refine ⟨u, hu, k' * (k : GU σ' n)⁻¹, (KU σ' n).mul_mem hk' ((KU σ' n).inv_mem k.2), ?_⟩
        have h1 : ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            (((y * k : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((((k : GU σ' n)⁻¹ : GU σ' n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          simp [Matrix.mul_assoc]
        rw [h1, hy]
        simp [Matrix.mul_assoc]
      · rintro ⟨u, hu, k', hk', hy⟩
        refine ⟨u, hu, k' * (k : GU σ' n), (KU σ' n).mul_mem hk' k.2, ?_⟩
        simp only [Subgroup.coe_mul, Units.val_mul, hy, Matrix.mul_assoc]
    have hh : h' (y * k) = h' y := by
      have := hbi 1 k y
      simpa using this
    simp only [hc, hh]
  have hmk : ∀ x : GU σ n ⧸ KU σ n, F' (E x).out = F' (guMap g hg n x.out) := by
    intro x
    have hx : E x = QuotientGroup.mk (guMap g hg n x.out) := by
      conv_lhs => rw [← Quotient.out_eq x]
      rfl
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (KU σ' n) (guMap g hg n x.out)
    rw [hx, hk, hinv]
  calc (∑ᶠ x : GU σ n ⧸ KU σ n, if ∃ u : GU σ n, IsUnipU u ∧ ∃ k ∈ KU σ n,
          (((x.out : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            tMat ϖ n m a * (((u : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (((k : GU σ n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        then h' (guMap g hg n x.out) else 0)
      = ∑ᶠ x : GU σ n ⧸ KU σ n, F' (E x).out := by
        refine finsum_congr (fun x => ?_)
        rw [hmk, hF']
        simp only [hcond a x.out]
    _ = ∑ᶠ x' : GU σ' n ⧸ KU σ' n, F' x'.out := finsum_comp_equiv E (f := fun x' => F' x'.out)

end GlobalTheory.SatInd
