import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivDescend

section Bialg

variable {R K A B : Type} [CommRing R] [CommRing K] [Algebra R K] [CommRing A] [Bialgebra R A]
  [CommRing B] [Bialgebra R B]

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := A) hK h`.
-/
theorem one_tmul_injective [Module.Flat R A] (hK : Function.Injective (algebraMap R K)) {a b : A}
    (h : (1 : K) ⊗ₜ[R] a = (1 : K) ⊗ₜ[R] b) : a = b :=
  Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := A) hK h

/- English proof (translation)
Establish `e : ∀ c : A ⊗[R] A, (toBaseChange R K A).two c = TensorProduct.AlgebraTensorModule.distribBaseChange R K A A ((1 : K) ⊗ₜ[R] c)` using `fun c => by`. Proceed by induction on `c with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]`. Consider the case `tmul a b => simp`.

Introduce `x y h`. Rewrite `h` using `[e, e]`. Conclude with `Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := A ⊗[R] A) hK ((TensorProduct.AlgebraTensorModule.distribBaseChange R K A A).injective h)`.
-/
theorem two_injective [Module.Flat R A] (hK : Function.Injective (algebraMap R K)) :
    Function.Injective (toBaseChange R K A).two := by
  have e : ∀ c : A ⊗[R] A, (toBaseChange R K A).two c =
      TensorProduct.AlgebraTensorModule.distribBaseChange R K A A ((1 : K) ⊗ₜ[R] c) := fun c => by
    induction c with
    | zero => simp
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul a b => simp
  intro x y h
  rw [e, e] at h
  exact Algebra.TensorProduct.includeRight_injective (R := R) (A := K) (B := A ⊗[R] A) hK
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R K A A).injective h)

/- English proof (translation)
Use `choose g hg using hf`. Establish `hs : ∀ (r : R) (b : B), g (r • b) = r • g b` using `fun r b => one_tmul_injective hK (by`. Rewrite using `[← hg, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hg, ← algebraMap_smul K r, ← algebraMap_smul K r, map_smul])`. Establish `h1 : g 1 = 1` using `one_tmul_injective hK ((hg 1).symm.trans (map_one f))`. Set `g₁ : B →+* A` to `{ toFun := g map_one' := h1 map_mul' := fun a b => one_tmul_injective hK (by`.

Establish `h` using `map_mul f ((1 : K) ⊗ₜ[R] a) ((1 : K) ⊗ₜ[R] b)`. Rewrite `h` using `[hg a, hg b, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, hg]`. Conclude with `h)`. Use the proof step `map_zero' := by simpa using hs 0 0`. Use the proof step `map_add' := fun a b => one_tmul_injective hK (by`.

Rewrite using `[← hg, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, hg, hg]) }`. Set `F` to `(SemiBialgHom.ofBialgHom f).comp (toBaseChange R K B)`. Establish `hF : ∀ b, F b = toBaseChange R K A (g b)` using `hg`. Set `g₂ : SemiBialgHom (RingHom.id R) B A` to `{ toRingHom := g₁ smul_map := hs counit_map := fun b => hK (by`. Establish `h` using `F.counit_map b`.

Rewrite `h` using `[hF, (toBaseChange R K A).counit_map]`. Conclude with `h)`. Use `comul_map := fun b => two_injective hK (by`. Rewrite using `[SemiBialgHom.two_comul]`. Use `((congrArg _ (hF b).symm).trans (F.two_comul b).symm).trans ?_` and prove the remaining obligations.

Generalize the expression as in `comul (R := R) b = c`. Proceed by induction on `c with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Consider the case `tmul a b`.

Simplify using `only [TensorProduct.map_tmul, SemiBialgHom.lin_apply, hF]`. Use the proof step `rfl) }`. Conclude with `⟨g₂.toBialgHom, hg⟩`.
-/
theorem exists_bialgHom [Module.Flat R A] (hK : Function.Injective (algebraMap R K))
    (f : K ⊗[R] B →ₐc[K] K ⊗[R] A)
    (hf : ∀ b : B, ∃ a : A, f ((1 : K) ⊗ₜ[R] b) = (1 : K) ⊗ₜ[R] a) :
    ∃ g : B →ₐc[R] A, ∀ b, f ((1 : K) ⊗ₜ[R] b) = (1 : K) ⊗ₜ[R] g b := by
  choose g hg using hf
  have hs : ∀ (r : R) (b : B), g (r • b) = r • g b := fun r b => one_tmul_injective hK (by
    rw [← hg, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hg, ← algebraMap_smul K r,
      ← algebraMap_smul K r, map_smul])
  have h1 : g 1 = 1 := one_tmul_injective hK ((hg 1).symm.trans (map_one f))
  let g₁ : B →+* A :=
    { toFun := g
      map_one' := h1
      map_mul' := fun a b => one_tmul_injective hK (by
        have h := map_mul f ((1 : K) ⊗ₜ[R] a) ((1 : K) ⊗ₜ[R] b)
        rw [hg a, hg b, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul,
          _root_.mul_one, hg] at h
        exact h)
      map_zero' := by simpa using hs 0 0
      map_add' := fun a b => one_tmul_injective hK (by
        rw [← hg, TensorProduct.tmul_add, TensorProduct.tmul_add, map_add, hg, hg]) }
  let F := (SemiBialgHom.ofBialgHom f).comp (toBaseChange R K B)
  have hF : ∀ b, F b = toBaseChange R K A (g b) := hg
  let g₂ : SemiBialgHom (RingHom.id R) B A :=
    { toRingHom := g₁
      smul_map := hs
      counit_map := fun b => hK (by
        have h := F.counit_map b
        rw [hF, (toBaseChange R K A).counit_map] at h
        exact h)
      comul_map := fun b => two_injective hK (by
        rw [SemiBialgHom.two_comul]
        refine ((congrArg _ (hF b).symm).trans (F.two_comul b).symm).trans ?_
        generalize comul (R := R) b = c
        induction c with
        | zero => simp
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b =>
          simp only [TensorProduct.map_tmul, SemiBialgHom.lin_apply, hF]
          rfl) }
  exact ⟨g₂.toBialgHom, hg⟩

end Bialg

/- English proof (translation)
Establish `hK` using `IsFractionRing.injective R K`. Use `choose g hg using fun n => exists_bialgHom (A := GG.A n) (B := HH.A n) hK (f.app n) (hf n)`. Use `⟨⟨g, fun n => BialgHom.ext fun b => one_tmul_injective hK ?_⟩, baseChange_hom_ext fun n b => (hg n b).symm⟩` and prove the remaining obligations. Establish `h` using `res_app f n ((1 : K) ⊗ₜ[R] b)`. Rewrite `h` using `[hg]`.

Conclude with `h.trans (hg n _)`.
-/
theorem exists_baseChangeMap_eq (p : ℕ) (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (GG HH : PDivGroup p R) (f : GG.baseChange K ⟶ HH.baseChange K)
    (hf : ∀ (n : ℕ) (b : HH.A n), ∃ a : GG.A n, f.app n ((1 : K) ⊗ₜ[R] b) = (1 : K) ⊗ₜ[R] a) :
    ∃ φ : GG ⟶ HH, PDivGroup.baseChangeMap K φ = f := by
  have hK := IsFractionRing.injective R K
  choose g hg using fun n => exists_bialgHom (A := GG.A n) (B := HH.A n) hK (f.app n) (hf n)
  refine ⟨⟨g, fun n => BialgHom.ext fun b => one_tmul_injective hK ?_⟩,
    baseChange_hom_ext fun n b => (hg n b).symm⟩
  have h := res_app f n ((1 : K) ⊗ₜ[R] b)
  rw [hg] at h
  exact h.trans (hg n _)

end GlobalTheory.PDivDescend
