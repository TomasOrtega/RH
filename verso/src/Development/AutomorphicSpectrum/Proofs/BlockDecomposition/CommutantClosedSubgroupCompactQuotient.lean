import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov GlobalTheory.CompanionTheory.ParCocompact
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing

namespace GlobalTheory.CompanionTheory.ParCocompact.Centralizer

section Core

open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

variable {K E : Type} [Field K] [NumberField K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

def ratCent {m : Type} (S : m → Matrix ι ι (K ⊗[K] E)) : Subgroup (GL ι (K ⊗[K] E)) where
  carrier := {g | ∀ k, (g : Matrix ι ι (K ⊗[K] E)) * S k = S k * g}
  one_mem' k := by simp
  mul_mem' {a b} ha hb k := by
    rw [Units.val_mul, Matrix.mul_assoc, hb k, ← Matrix.mul_assoc, ha k, Matrix.mul_assoc]
  inv_mem' {a} ha k := by
    have h := ha k
    calc ((a⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * S k
        = ↑a⁻¹ * (S k * ↑a) * ↑a⁻¹ := by simp [mul_assoc]
      _ = ↑a⁻¹ * (↑a * S k) * ↑a⁻¹ := by rw [h]
      _ = S k * ↑a⁻¹ := by simp

local notation "𝒩'" => Fintype.card (ι × Fin (Module.finrank K E))

/- English proof (translation)
Set `b` to `Module.finBasis K E`. Set `G : Subgroup (AdelicGLn.AdelicGL K 𝒩')` to `G₀.map (trHom b 𝔸[K])`. Establish `hG1 : G ≤ Reduction.normOneGL K 𝒩'`. Introduce and unpack `_ ⟨u, hu, rfl⟩`. Rewrite using `[Reduction.mem_normOneGL]`.

Use `set a := AdelicGLn.det K 𝒩' (trHom b 𝔸[K] u)`. Establish `ha : a * a = 1`. Use `ext`. Simplify `det_trHom_mul_self b 𝔸[K] H hH ⟨u, hU hu⟩` using `[a]`. Establish `h2 : (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) * (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) = 1`.

Establish `h3` using `congrArg (GroundTheory.Global.IdeleGroup.ideleModule K) ha`. Rewrite `h3` using `[map_mul, map_one]`. Simplify using `using congrArg Subtype.val h3`. Establish `hpos` using `(GroundTheory.Global.IdeleGroup.ideleModule K a).2`. Use the polynomial consequences of the given equalities and inequalities.

Set `Lf : Fin (Module.finrank K E) ⊕ m → Matrix (Fin 𝒩') (Fin 𝒩') K` to `Sum.elim (resScalar (ι := ι) b) (fun k => resHom b K (S k)ᵀ)`. Establish `hGL : G ≤ adelicCentralizer Lf`. Introduce and unpack `_ ⟨u, hu, rfl⟩ (j | k)`. Establish `e` using `resScalar_map (ι := ι) b (Algebra.ofId K 𝔸[K]) j`. Express the relevant statement in the definitionally equal form `_ * (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) = (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) * _`.

Rewrite using `[e, trHom_val]`. Conclude with `resHom_commute_scalar b 𝔸[K] _ _`. Express the relevant statement in the definitionally equal form `_ * (resHom b K (S k)ᵀ).map (Algebra.ofId K 𝔸[K]) = (resHom b K (S k)ᵀ).map (Algebra.ofId K 𝔸[K]) * _`. Rewrite using `[← resHom_baseMap, trHom_val, ← map_mul, ← map_mul, transpose_map, ← transpose_mul, ← transpose_mul, hS _ (inv_mem hu) k]`. Take `⟨C, hC, hred⟩` from `exists_isCompact_centralizer_reduction Lf G hG1 hGL hε (by rintro _ ⟨u, hu, rfl⟩ x hx; exact hh u hu x hx)`.

Use `⟨C, hC, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hγC⟩` from `hred _ ⟨u, hu, rfl⟩`. Take `⟨M, hM⟩` from `exists_resHom_eq_of_commute b γ (fun j => hγ (Sum.inl j))`. Use `⟨inside₂ (K ⊗[K] E) M, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`.

Establish `h1 : (M : Matrix ι ι (K ⊗[K] E)) * (S k)ᵀ = (S k)ᵀ * M`. Apply `resHom_injective b K` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, hM]`. Conclude with `hγ (Sum.inr k)`. Establish `h2 : ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * (S k)ᵀ = (S k)ᵀ * ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E))`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `congrArg Matrix.transpose h2`. Rewrite `h3` using `[transpose_mul, transpose_mul, transpose_transpose]`. Conclude with `h3.symm`. Establish `e : trHom b 𝔸[K] (diagGL (Algebra.ofId K 𝔸[K]) (inside₂ (K ⊗[K] E) M)) = AdelicGLn.diagonal K 𝒩' γ`.

Use extensionality with `: 1`. Rewrite using `[← invTr_diagGL, trHom_invTr, diagGL_val, resHom_baseMap, hM]`. Both sides reduce to the same expression. Rewrite using `[map_mul, map_inv, e]`. Conclude with `hγC`.
-/
theorem exists_isCompact_trHom_centralizer (hH : IsUnit H.det) {m : Type} [Finite m]
    (S : m → Matrix ι ι (K ⊗[K] E)) (G₀ : Subgroup (GL ι (𝔸[K] ⊗[K] E)))
    (hU : G₀ ≤ unitaryPoints K E H 𝔸[K])
    (hS : ∀ g ∈ G₀, ∀ k, (g : Matrix ι ι (𝔸[K] ⊗[K] E)) * (S k).map (baseMap (Algebra.ofId K 𝔸[K])) =
      (S k).map (baseMap (Algebra.ofId K 𝔸[K])) * g)
    {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ g ∈ G₀, ∀ x : Fin 𝒩' → K, x ≠ 0 →
      ε ≤ Reduction.height (trHom (Module.finBasis K E) 𝔸[K] g) x) :
    ∃ C : Set (GL (Fin 𝒩') 𝔸[K]), IsCompact C ∧ ∀ u ∈ G₀, ∃ M ∈ ratCent S,
      trHom (Module.finBasis K E) 𝔸[K] ((diagGL (Algebra.ofId K 𝔸[K]) M)⁻¹ * u) ∈ C := by
  classical
  let b := Module.finBasis K E
  let G : Subgroup (AdelicGLn.AdelicGL K 𝒩') := G₀.map (trHom b 𝔸[K])
  have hG1 : G ≤ Reduction.normOneGL K 𝒩' := by
    rintro _ ⟨u, hu, rfl⟩
    rw [Reduction.mem_normOneGL]
    set a := AdelicGLn.det K 𝒩' (trHom b 𝔸[K] u)
    have ha : a * a = 1 := by
      ext
      simpa [a] using det_trHom_mul_self b 𝔸[K] H hH ⟨u, hU hu⟩
    have h2 : (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) *
        (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) = 1 := by
      have h3 := congrArg (GroundTheory.Global.IdeleGroup.ideleModule K) ha
      rw [map_mul, map_one] at h3
      simpa using congrArg Subtype.val h3
    have hpos := (GroundTheory.Global.IdeleGroup.ideleModule K a).2
    nlinarith
  let Lf : Fin (Module.finrank K E) ⊕ m → Matrix (Fin 𝒩') (Fin 𝒩') K :=
    Sum.elim (resScalar (ι := ι) b) (fun k => resHom b K (S k)ᵀ)
  have hGL : G ≤ adelicCentralizer Lf := by
    rintro _ ⟨u, hu, rfl⟩ (j | k)
    · have e := resScalar_map (ι := ι) b (Algebra.ofId K 𝔸[K]) j
      change _ * (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) =
        (resScalar (ι := ι) b j).map (Algebra.ofId K 𝔸[K]) * _
      rw [e, trHom_val]
      exact resHom_commute_scalar b 𝔸[K] _ _
    · change _ * (resHom b K (S k)ᵀ).map (Algebra.ofId K 𝔸[K]) =
        (resHom b K (S k)ᵀ).map (Algebra.ofId K 𝔸[K]) * _
      rw [← resHom_baseMap, trHom_val, ← map_mul, ← map_mul, transpose_map, ← transpose_mul,
        ← transpose_mul, hS _ (inv_mem hu) k]
  obtain ⟨C, hC, hred⟩ := exists_isCompact_centralizer_reduction Lf G hG1 hGL hε
    (by rintro _ ⟨u, hu, rfl⟩ x hx; exact hh u hu x hx)
  refine ⟨C, hC, fun u hu => ?_⟩
  obtain ⟨γ, hγ, hγC⟩ := hred _ ⟨u, hu, rfl⟩
  obtain ⟨M, hM⟩ := exists_resHom_eq_of_commute b γ (fun j => hγ (Sum.inl j))
  refine ⟨inside₂ (K ⊗[K] E) M, ?_, ?_⟩
  · intro k
    have h1 : (M : Matrix ι ι (K ⊗[K] E)) * (S k)ᵀ = (S k)ᵀ * M := by
      apply resHom_injective b K
      rw [map_mul, map_mul, hM]
      exact hγ (Sum.inr k)
    have h2 : ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * (S k)ᵀ =
        (S k)ᵀ * ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) := by
      calc ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * (S k)ᵀ
          = ↑M⁻¹ * ((S k)ᵀ * ↑M) * ↑M⁻¹ := by simp [mul_assoc]
        _ = ↑M⁻¹ * (↑M * (S k)ᵀ) * ↑M⁻¹ := by rw [h1]
        _ = (S k)ᵀ * ↑M⁻¹ := by simp
    have h3 := congrArg Matrix.transpose h2
    rw [transpose_mul, transpose_mul, transpose_transpose] at h3
    exact h3.symm
  · have e : trHom b 𝔸[K] (diagGL (Algebra.ofId K 𝔸[K]) (inside₂ (K ⊗[K] E) M)) =
        AdelicGLn.diagonal K 𝒩' γ := by
      ext : 1
      rw [← invTr_diagGL, trHom_invTr, diagGL_val, resHom_baseMap, hM]
      rfl
    rw [map_mul, map_inv, e]
    exact hγC

section Orbit

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

def formOrbit (g : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E) :=
  cstar ((g⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * baseMatrix K H 𝔸[K] *
    ((g⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))

/- English proof (translation)
Use `set Hb := baseMatrix K H 𝔸[K] with hHb`. Set `Ψ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun x => cstar (x : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * x`. Establish `hΨmul : ∀ x y, Ψ (x * y) = cstar (y : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ x * y`. Introduce `x y`. Simplify using `only [Ψ, Units.val_mul, cstar_mul, Matrix.mul_assoc]`.

Establish `hΨone : Ψ 1 = Hb`. Simplify using `[Ψ, cstar_one]`. Establish `hcancel : ∀ (z : GL ι (𝔸[K] ⊗[K] E)) (X : Matrix ι ι (𝔸[K] ⊗[K] E)), cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) * (cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * X * ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) * (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = X`. Introduce `z X`. Establish `h1 : cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) * cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1`.

Rewrite using `[← cstar_mul, z.inv_mul, cstar_one]`. Establish `h2 : ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1` using `z.inv_mul`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]`.

Establish `e1 : formOrbit H g = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ (g⁻¹ * g') * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))` using `by show Ψ g⁻¹ = _`. Rewrite using `[← hΨmul, mul_inv_cancel_right]`. Establish `e2 : formOrbit H g' = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))` using `by show Ψ g'⁻¹ = _`. Rewrite using `[← hΨone, ← hΨmul, one_mul]`. Rewrite using `[e1, e2]`.

Prove the components needed by the constructor for the conclusion. Introduce `he`. Establish `h` using `congrArg (fun X => cstar (g' : Matrix ι ι (𝔸[K] ⊗[K] E)) * X * (g' : Matrix ι ι (𝔸[K] ⊗[K] E))) he`. Simplify using `only [hcancel] at h`. Conclude with `h`.

Introduce `hu`. Establish `h : Ψ (g⁻¹ * g') = Hb` using `hu`. Rewrite using `[h]`.
-/
theorem formOrbit_eq_iff (g g' : GL ι (𝔸[K] ⊗[K] E)) :
    formOrbit H g = formOrbit H g' ↔ g⁻¹ * g' ∈ unitaryPoints K E H 𝔸[K] := by
  set Hb := baseMatrix K H 𝔸[K] with hHb
  let Ψ : GL ι (𝔸[K] ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun x =>
    cstar (x : Matrix ι ι (𝔸[K] ⊗[K] E)) * Hb * x
  have hΨmul : ∀ x y, Ψ (x * y) = cstar (y : Matrix ι ι (𝔸[K] ⊗[K] E)) * Ψ x * y := by
    intro x y
    simp only [Ψ, Units.val_mul, cstar_mul, Matrix.mul_assoc]
  have hΨone : Ψ 1 = Hb := by
    simp [Ψ, cstar_one]
  have hcancel : ∀ (z : GL ι (𝔸[K] ⊗[K] E)) (X : Matrix ι ι (𝔸[K] ⊗[K] E)),
      cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        (cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) * X *
          ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) *
        (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = X := by
    intro z X
    have h1 : cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1 := by
      rw [← cstar_mul, z.inv_mul, cstar_one]
    have h2 : ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
        (z : Matrix ι ι (𝔸[K] ⊗[K] E)) = 1 := z.inv_mul
    calc _ = (cstar (z : Matrix ι ι (𝔸[K] ⊗[K] E)) *
          cstar ((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E))) * X *
          (((z⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
            (z : Matrix ι ι (𝔸[K] ⊗[K] E))) := by
          simp only [Matrix.mul_assoc]
      _ = X := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  have e1 : formOrbit H g = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
      Ψ (g⁻¹ * g') * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) := by
    show Ψ g⁻¹ = _
    rw [← hΨmul, mul_inv_cancel_right]
  have e2 : formOrbit H g' = cstar ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) *
      Hb * ((g'⁻¹ : GL ι (𝔸[K] ⊗[K] E)) : Matrix ι ι (𝔸[K] ⊗[K] E)) := by
    show Ψ g'⁻¹ = _
    rw [← hΨone, ← hΨmul, one_mul]
  rw [e1, e2]
  constructor
  · intro he
    have h := congrArg (fun X => cstar (g' : Matrix ι ι (𝔸[K] ⊗[K] E)) * X *
      (g' : Matrix ι ι (𝔸[K] ⊗[K] E))) he
    simp only [hcancel] at h
    exact h
  · intro hu
    have h : Ψ (g⁻¹ * g') = Hb := hu
    rw [h]

/- English proof (translation)
Set `b` to `Module.finBasis K E`. Use `set α := Algebra.ofId K 𝔸[K] with hα`. Use `set Hb := baseMatrix K H 𝔸[K] with hHb`. Set `Ψ' : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun A => cstar (readoff b 𝔸[K] A)ᵀ * Hb * (readoff b 𝔸[K] A)ᵀ`. Establish `hΨ'c : Continuous Ψ'`.

Establish `h1 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (readoff (ι` using `ι) b 𝔸[K] A)ᵀ := (continuous_readoff b 𝔸[K]).matrix_transpose`. Establish `h2 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => cstar (readoff (ι` using `ι) b 𝔸[K] A)ᵀ := by show Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (((readoff (ι := ι) b 𝔸[K] A)ᵀ).map (conjBase K E 𝔸[K]))ᵀ`. Conclude with `(h1.matrix_map (continuous_conjBase 𝔸[K])).matrix_transpose`. Conclude with `(h2.matrix_mul continuous_const).matrix_mul h1`. Establish `hC₂ : ∀ w : GL ι (𝔸[K] ⊗[K] E), formOrbit H w = Ψ' (trHom b 𝔸[K] w : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K])`.

Introduce `w`. Simplify using `only [formOrbit, Ψ', trHom_val, readoff_resHom, transpose_transpose, Hb]`. Establish `hX : IsCompact (Ψ' '' (Units.val '' C))` using `(hC.image Units.continuous_val).image hΨ'c`. Set `ψ : Matrix ι ι (K ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E)` to `fun V => V.map (baseMap α)`. Establish `hΓ : ∀ M : GL ι (K ⊗[K] E), formOrbit H (diagGL α M) = ψ (cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K * ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)))`.

Introduce `M`. Simplify using `only [formOrbit, ψ, ← map_inv, diagGL_val]`. Rewrite using `[cstar_mul_baseMatrix_map]`. Establish `hfinV : {V | ψ V ∈ Ψ' '' (Units.val '' C)}.Finite`. Use `finite_of_isCompact_coords hX ψ (fun p : ι × ι × Fin (Module.finrank K E) => fun X => coords b 𝔸[K] (X p.1 p.2.1) p.2.2) (fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp (continuous_id.matrix_elem _ _))) (fun V p => coords b K (V p.1 p.2.1) p.2.2) ?_ ?_` and prove the remaining obligations.

Introduce `V V' h`. Use extensionality with `i j`. Apply `(coords b K).injective` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Conclude with `congrFun h (i, j, k)`.

Introduce `V p`. Simplify using `only [ψ, Matrix.map_apply, coords_baseMap]`. Both sides reduce to the same expression. Use `(hfinV.image ψ).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨w, hw, rfl⟩, _, ⟨M, rfl⟩, he⟩`.

Use `⟨cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K * ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)), ?_, ?_⟩` and prove the remaining obligations. Use `show ψ _ ∈ Ψ' '' (Units.val '' C)`. Rewrite using `[← hΓ M, he, hC₂ w]`. Conclude with `⟨_, ⟨_, hw, rfl⟩, rfl⟩`. Rewrite using `[← hΓ M, he]`.
-/
theorem finite_formOrbit {C : Set (GL (Fin 𝒩') 𝔸[K])} (hC : IsCompact C) :
    (formOrbit H '' {w | trHom (Module.finBasis K E) 𝔸[K] w ∈ C} ∩
      formOrbit H '' Set.range (diagGL (ι := ι) (E := E) (Algebra.ofId K 𝔸[K]))).Finite := by
  classical
  let b := Module.finBasis K E
  set α := Algebra.ofId K 𝔸[K] with hα
  set Hb := baseMatrix K H 𝔸[K] with hHb
  let Ψ' : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → Matrix ι ι (𝔸[K] ⊗[K] E) := fun A =>
    cstar (readoff b 𝔸[K] A)ᵀ * Hb * (readoff b 𝔸[K] A)ᵀ
  have hΨ'c : Continuous Ψ' := by
    have h1 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] => (readoff (ι := ι) b 𝔸[K] A)ᵀ :=
      (continuous_readoff b 𝔸[K]).matrix_transpose
    have h2 : Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] =>
        cstar (readoff (ι := ι) b 𝔸[K] A)ᵀ := by
      show Continuous fun A : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] =>
        (((readoff (ι := ι) b 𝔸[K] A)ᵀ).map (conjBase K E 𝔸[K]))ᵀ
      exact (h1.matrix_map (continuous_conjBase 𝔸[K])).matrix_transpose
    exact (h2.matrix_mul continuous_const).matrix_mul h1
  have hC₂ : ∀ w : GL ι (𝔸[K] ⊗[K] E),
      formOrbit H w = Ψ' (trHom b 𝔸[K] w : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K]) := by
    intro w
    simp only [formOrbit, Ψ', trHom_val, readoff_resHom, transpose_transpose, Hb]
  have hX : IsCompact (Ψ' '' (Units.val '' C)) := (hC.image Units.continuous_val).image hΨ'c
  let ψ : Matrix ι ι (K ⊗[K] E) → Matrix ι ι (𝔸[K] ⊗[K] E) := fun V => V.map (baseMap α)
  have hΓ : ∀ M : GL ι (K ⊗[K] E), formOrbit H (diagGL α M) =
      ψ (cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K *
        ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E))) := by
    intro M
    simp only [formOrbit, ψ, ← map_inv, diagGL_val]
    rw [cstar_mul_baseMatrix_map]
  have hfinV : {V | ψ V ∈ Ψ' '' (Units.val '' C)}.Finite := by
    refine finite_of_isCompact_coords hX ψ
      (fun p : ι × ι × Fin (Module.finrank K E) => fun X => coords b 𝔸[K] (X p.1 p.2.1) p.2.2)
      (fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp
        (continuous_id.matrix_elem _ _)))
      (fun V p => coords b K (V p.1 p.2.1) p.2.2) ?_ ?_
    · intro V V' h
      ext i j
      apply (coords b K).injective
      funext k
      exact congrFun h (i, j, k)
    · intro V p
      simp only [ψ, Matrix.map_apply, coords_baseMap]
      rfl
  refine (hfinV.image ψ).subset ?_
  rintro _ ⟨⟨w, hw, rfl⟩, _, ⟨M, rfl⟩, he⟩
  refine ⟨cstar ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)) * baseMatrix K H K *
      ((M⁻¹ : GL ι (K ⊗[K] E)) : Matrix ι ι (K ⊗[K] E)), ?_, ?_⟩
  · show ψ _ ∈ Ψ' '' (Units.val '' C)
    rw [← hΓ M, he, hC₂ w]
    exact ⟨_, ⟨_, hw, rfl⟩, rfl⟩
  · rw [← hΓ M, he]

/- English proof (translation)
Set `b` to `Module.finBasis K E`. Use `set Ω : Set (unitaryPoints K E H 𝔸[K]) := {v | trHom b 𝔸[K] (v : GL ι (𝔸[K] ⊗[K] E)) ∈ C} with hΩ`. Establish `hΩcl : IsClosed Ω` using `hC.isClosed.preimage ((continuous_trHom b 𝔸[K]).comp continuous_subtype_val)`. Set `Fc : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → ι × ι × Fin (Module.finrank K E) → 𝔸[K]` to `fun A p => coords b 𝔸[K] ((readoff (ι := ι) b 𝔸[K] A)ᵀ p.1 p.2.1) p.2.2`. Establish `hFc : Continuous Fc` using `continuous_pi fun p => (continuous_apply _).comp ((continuous_coords b 𝔸[K]).comp (((continuous_readoff b 𝔸[K]).matrix_transpose).matrix_elem _ _))`.

Use `set D := (unitaryCoords H 𝔸[K] b) ⁻¹' (Fc '' (Units.val '' C)) with hD`. Establish `hDc : IsCompact D` using `(isClosedEmbedding_unitaryCoords H 𝔸[K] b hH).isCompact_preimage ((hC.image Units.continuous_val).image hFc)`. Establish `hsub : Ω ⊆ D⁻¹`. Introduce `v hv`. Use `show v⁻¹ ∈ D`.

Use `⟨_, ⟨_, hv, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Simplify using `only [Fc, trHom_val, readoff_resHom, transpose_transpose]`. Both sides reduce to the same expression. Conclude with `hDc.inv.of_isClosed_subset hΩcl hsub`.
-/
theorem isCompact_setOf_trHom_mem (hH : IsUnit H.det) {C : Set (GL (Fin 𝒩') 𝔸[K])} (hC : IsCompact C) :
    IsCompact {v : unitaryPoints K E H 𝔸[K] |
      trHom (Module.finBasis K E) 𝔸[K] (v : GL ι (𝔸[K] ⊗[K] E)) ∈ C} := by
  classical
  let b := Module.finBasis K E
  set Ω : Set (unitaryPoints K E H 𝔸[K]) := {v | trHom b 𝔸[K] (v : GL ι (𝔸[K] ⊗[K] E)) ∈ C} with hΩ
  have hΩcl : IsClosed Ω :=
    hC.isClosed.preimage ((continuous_trHom b 𝔸[K]).comp continuous_subtype_val)
  let Fc : Matrix (Fin 𝒩') (Fin 𝒩') 𝔸[K] → ι × ι × Fin (Module.finrank K E) → 𝔸[K] :=
    fun A p =>
    coords b 𝔸[K] ((readoff (ι := ι) b 𝔸[K] A)ᵀ p.1 p.2.1) p.2.2
  have hFc : Continuous Fc := continuous_pi fun p => (continuous_apply _).comp
    ((continuous_coords b 𝔸[K]).comp
      (((continuous_readoff b 𝔸[K]).matrix_transpose).matrix_elem _ _))
  set D := (unitaryCoords H 𝔸[K] b) ⁻¹' (Fc '' (Units.val '' C)) with hD
  have hDc : IsCompact D := (isClosedEmbedding_unitaryCoords H 𝔸[K] b hH).isCompact_preimage
    ((hC.image Units.continuous_val).image hFc)
  have hsub : Ω ⊆ D⁻¹ := by
    intro v hv
    show v⁻¹ ∈ D
    refine ⟨_, ⟨_, hv, rfl⟩, ?_⟩
    funext p
    simp only [Fc, trHom_val, readoff_resHom, transpose_transpose]
    rfl
  exact hDc.inv.of_isClosed_subset hΩcl hsub

/- English proof (translation)
Use `set b := Module.finBasis K E with hb`. Take `⟨C, hC, hred⟩` from `exists_isCompact_trHom_centralizer H hH S G₀ hU hS hε hh`. Use `set α := Algebra.ofId K 𝔸[K] with hα`. Set `Γ : Subgroup (GL ι (𝔸[K] ⊗[K] E))` to `(ratCent S).map (diagGL α)`. Set `C₂ : Set (GL ι (𝔸[K] ⊗[K] E))` to `{w | trHom b 𝔸[K] w ∈ C}`.

Establish `hfin : (formOrbit H '' C₂ ∩ formOrbit H '' (Γ : Set (GL ι (𝔸[K] ⊗[K] E)))).Finite`. Use `(finite_formOrbit H hC).subset (Set.inter_subset_inter_right _ (Set.image_mono ?_))` and prove the remaining obligations. Introduce and unpack `_ ⟨M, -, rfl⟩`. Conclude with `⟨M, rfl⟩`. Take `⟨T, hTΓ, hT⟩` from `exists_finset_of_orbit (formOrbit H) (unitaryPoints K E H 𝔸[K]) Γ (formOrbit_eq_iff H) C₂ hfin`.

Set `C₃ : Set (GL (Fin 𝒩') 𝔸[K])` to `⋃ δ ∈ T, (fun c => (trHom b 𝔸[K] δ)⁻¹ * c) '' C`. Establish `hC₃ : IsCompact C₃` using `T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id)`. Use `⟨C₃, hC₃, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨M, hMZ, hM⟩` from `hred u hu`. Take `⟨δ, hδT, hηδ, -⟩` from `hT u (hU hu) (diagGL α M) ⟨M, hMZ, rfl⟩ ((diagGL α M)⁻¹ * u) hM (by rw [mul_inv_cancel_left])`.

Take `⟨m', hm', rfl⟩` from `hTΓ δ hδT`. Rewrite `hηδ` using `[← map_mul]`. Use `⟨M * m', mul_mem hMZ hm', mem_unitaryPoints_of_diagGL H hηδ, ?_⟩` and prove the remaining obligations. Use `Set.mem_biUnion hδT ⟨_, hM, ?_⟩` and prove the remaining obligations. Establish `e : (diagGL α (M * m'))⁻¹ * u = (diagGL α m')⁻¹ * ((diagGL α M)⁻¹ * u)`.

Rewrite using `[map_mul, _root_.mul_inv_rev, mul_assoc]`. Use `show (trHom b 𝔸[K] (diagGL α m'))⁻¹ * trHom b 𝔸[K] ((diagGL α M)⁻¹ * u) = _`. Rewrite using `[e]`. Simplify using `only [map_mul, map_inv]`.
-/
theorem exists_isCompact_rational_centralizer (hH : IsUnit H.det) {m : Type} [Finite m]
    (S : m → Matrix ι ι (K ⊗[K] E)) (G₀ : Subgroup (GL ι (𝔸[K] ⊗[K] E)))
    (hU : G₀ ≤ unitaryPoints K E H 𝔸[K])
    (hS : ∀ g ∈ G₀, ∀ k, (g : Matrix ι ι (𝔸[K] ⊗[K] E)) * (S k).map (baseMap (Algebra.ofId K 𝔸[K])) =
      (S k).map (baseMap (Algebra.ofId K 𝔸[K])) * g)
    {ε : ℝ} (hε : 0 < ε)
    (hh : ∀ g ∈ G₀, ∀ x : Fin 𝒩' → K, x ≠ 0 →
      ε ≤ Reduction.height (trHom (Module.finBasis K E) 𝔸[K] g) x) :
    ∃ C : Set (GL (Fin 𝒩') 𝔸[K]), IsCompact C ∧ ∀ u ∈ G₀, ∃ M ∈ ratCent S,
      M ∈ unitaryPoints K E H K ∧
      trHom (Module.finBasis K E) 𝔸[K] ((diagGL (Algebra.ofId K 𝔸[K]) M)⁻¹ * u) ∈ C := by
  classical
  set b := Module.finBasis K E with hb
  obtain ⟨C, hC, hred⟩ := exists_isCompact_trHom_centralizer H hH S G₀ hU hS hε hh
  set α := Algebra.ofId K 𝔸[K] with hα
  let Γ : Subgroup (GL ι (𝔸[K] ⊗[K] E)) := (ratCent S).map (diagGL α)
  let C₂ : Set (GL ι (𝔸[K] ⊗[K] E)) := {w | trHom b 𝔸[K] w ∈ C}
  have hfin : (formOrbit H '' C₂ ∩ formOrbit H '' (Γ : Set (GL ι (𝔸[K] ⊗[K] E)))).Finite := by
    refine (finite_formOrbit H hC).subset (Set.inter_subset_inter_right _ (Set.image_mono ?_))
    rintro _ ⟨M, -, rfl⟩
    exact ⟨M, rfl⟩
  obtain ⟨T, hTΓ, hT⟩ := exists_finset_of_orbit (formOrbit H) (unitaryPoints K E H 𝔸[K]) Γ
    (formOrbit_eq_iff H) C₂ hfin
  let C₃ : Set (GL (Fin 𝒩') 𝔸[K]) := ⋃ δ ∈ T, (fun c => (trHom b 𝔸[K] δ)⁻¹ * c) '' C
  have hC₃ : IsCompact C₃ :=
    T.isCompact_biUnion fun δ _ => hC.image (continuous_const.mul continuous_id)
  refine ⟨C₃, hC₃, fun u hu => ?_⟩
  obtain ⟨M, hMZ, hM⟩ := hred u hu
  obtain ⟨δ, hδT, hηδ, -⟩ := hT u (hU hu) (diagGL α M) ⟨M, hMZ, rfl⟩
    ((diagGL α M)⁻¹ * u) hM (by rw [mul_inv_cancel_left])
  obtain ⟨m', hm', rfl⟩ := hTΓ δ hδT
  rw [← map_mul] at hηδ
  refine ⟨M * m', mul_mem hMZ hm', mem_unitaryPoints_of_diagGL H hηδ, ?_⟩
  refine Set.mem_biUnion hδT ⟨_, hM, ?_⟩
  have e : (diagGL α (M * m'))⁻¹ * u = (diagGL α m')⁻¹ * ((diagGL α M)⁻¹ * u) := by
    rw [map_mul, _root_.mul_inv_rev, mul_assoc]
  show (trHom b 𝔸[K] (diagGL α m'))⁻¹ * trHom b 𝔸[K] ((diagGL α M)⁻¹ * u) = _
  rw [e]
  simp only [map_mul, map_inv]

/- English proof (translation)
Establish `h` using `(isCompact_setOf_trHom_mem H hH hC).image continuous_subtype_val`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `⟨⟨w, h1⟩, h2, rfl⟩`. Introduce and unpack `⟨v, h2, rfl⟩`. Conclude with `⟨v.2, h2⟩`.
-/
theorem isCompact_mem_unitary_trHom (hH : IsUnit H.det) {C : Set (GL (Fin 𝒩') 𝔸[K])} (hC : IsCompact C) :
    IsCompact {w : GL ι (𝔸[K] ⊗[K] E) | w ∈ unitaryPoints K E H 𝔸[K] ∧
      trHom (Module.finBasis K E) 𝔸[K] w ∈ C} := by
  have h := (isCompact_setOf_trHom_mem H hH hC).image continuous_subtype_val
  convert h using 1
  ext w
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨w, h1⟩, h2, rfl⟩
  · rintro ⟨v, h2, rfl⟩
    exact ⟨v.2, h2⟩

end Orbit

section Rational

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E]

/- English proof (translation)
Establish `: sigR R (conj F E).toAlgHom = conjBase F E R`. Use `RingHom.ext fun z => ?_` and prove the remaining obligations. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e => rfl`.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy]`. Use extensionality with `g`. Use `show cT (sigR R (conj F E).toAlgHom) _ * _ * _ = _ ↔ _`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem HR_conj_eq {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (R : Type) [CommRing R] [Algebra F R] :
    HR R (conj F E).toAlgHom J = unitaryPoints F E J R := by
  have : sigR R (conj F E).toAlgHom = conjBase F E R := by
    refine RingHom.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  ext g
  show cT (sigR R (conj F E).toAlgHom) _ * _ * _ = _ ↔ _
  rw [this]
  rfl

/- English proof (translation)
Set `x : unitaryPoints F E J F` to `⟨m, hm⟩`. Establish `e : ((unitaryDiagonal F J x : unitaryPoints F E J (AF F)) : GL (Fin n) (AF F ⊗[F] E)) = diagGL (Algebra.ofId F (AF F)) m` using `Units.ext rfl`. Establish `hmem : diagGL (Algebra.ofId F (AF F)) m ∈ HR (AF F) (conj F E).toAlgHom J`. Rewrite using `[HR_conj_eq, ← e]`. Conclude with `(unitaryDiagonal F J x).2`.

Use `⟨⟨_, hmem⟩, ?_, rfl⟩` and prove the remaining obligations. Establish `key : diagGL (Algebra.ofId F (AF F)) m = Formalism.UG.bc (inclR (AF F)) (unitaryPointsRationalEquiv F E J x : GL (Fin n) E)`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Use `show tensorMap E (Algebra.ofId F (AF F)) ((m : Matrix _ _ _) i j) = inclR (AF F) (Algebra.TensorProduct.lid F E ((m : Matrix _ _ _) i j))`. Generalize the expression as in `(m : Matrix (Fin n) (Fin n) (F ⊗[F] E)) i j = z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e`. Rewrite using `[tensorMap_tmul, Algebra.TensorProduct.lid_tmul]`. Use `show algebraMap F (AF F) r ⊗ₜ[F] e = (1 : AF F) ⊗ₜ[F] (r • e)`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Conclude with `⟨_, (unitaryPointsRationalEquiv F E J x).2, key.symm⟩`.
-/
theorem exists_mem_ratPts {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {m : GL (Fin n) (F ⊗[F] E)}
    (hm : m ∈ unitaryPoints F E J F) :
    ∃ δ ∈ ratPts (conj F E).toAlgHom J,
      matHom (AF F) (conj F E).toAlgHom J δ = diagGL (Algebra.ofId F (AF F)) m := by
  let x : unitaryPoints F E J F := ⟨m, hm⟩
  have e : ((unitaryDiagonal F J x : unitaryPoints F E J (AF F)) : GL (Fin n) (AF F ⊗[F] E)) =
      diagGL (Algebra.ofId F (AF F)) m := Units.ext rfl
  have hmem : diagGL (Algebra.ofId F (AF F)) m ∈ HR (AF F) (conj F E).toAlgHom J := by
    rw [HR_conj_eq, ← e]
    exact (unitaryDiagonal F J x).2
  refine ⟨⟨_, hmem⟩, ?_, rfl⟩
  have key : diagGL (Algebra.ofId F (AF F)) m =
      Formalism.UG.bc (inclR (AF F)) (unitaryPointsRationalEquiv F E J x : GL (Fin n) E) := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    show tensorMap E (Algebra.ofId F (AF F)) ((m : Matrix _ _ _) i j) =
      inclR (AF F) (Algebra.TensorProduct.lid F E ((m : Matrix _ _ _) i j))
    generalize (m : Matrix (Fin n) (Fin n) (F ⊗[F] E)) i j = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r e =>
      rw [tensorMap_tmul, Algebra.TensorProduct.lid_tmul]
      show algebraMap F (AF F) r ⊗ₜ[F] e = (1 : AF F) ⊗ₜ[F] (r • e)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  exact ⟨_, (unitaryPointsRationalEquiv F E J x).2, key.symm⟩

end Rational

end Core

end GlobalTheory.CompanionTheory.ParCocompact.Centralizer

namespace GlobalTheory.CompanionTheory.ParCocompact

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n J hJ M _ S L hcl hcomm hht hrat`. Take `⟨ε, hε, hh⟩` from `hht`. Take `⟨hF, hE, h2, hc⟩` from `hσ`. Establish `: Algebra.IsQuadraticExtension F E` using `⟨h2⟩`. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Take `rfl : σ = (GroundTheory.Automorphic.conj F E).toAlgHom` from `AlgHom.ext fun x => τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)`. Establish `hu : IsUnit J.det` using `isUnit_iff_ne_zero.2 hJ.2`. Set `α : F →ₐ[F] AF F` to `Algebra.ofId F (AF F)`. Set `S' : M → Matrix (Fin n) (Fin n) (F ⊗[F] E)` to `fun k => GroundTheory.Automorphic.baseMatrix F (S k) F`. Establish `hS' : ∀ k, (S' k).map (GroundTheory.Automorphic.Anisotropic.baseMap α) = (S k).map (inclR (F` using `F) (AF F)) := fun k => GroundTheory.Automorphic.Anisotropic.baseMatrix_baseMap (S k) α`.

Set `G₀ : Subgroup (GL (Fin n) (AF F ⊗[F] E))` to `L.map (matHom (AF F) (GroundTheory.Automorphic.conj F E).toAlgHom J)`. Establish `hU : G₀ ≤ GroundTheory.Automorphic.unitaryPoints F E J (AF F)`. Introduce and unpack `_ ⟨g, -, rfl⟩`. Rewrite using `[← Centralizer.HR_conj_eq]`. Conclude with `g.2`.

Establish `hS : ∀ g ∈ G₀, ∀ k, (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * (S' k).map (GroundTheory.Automorphic.Anisotropic.baseMap α) = (S' k).map (GroundTheory.Automorphic.Anisotropic.baseMap α) * g`. Introduce and unpack `_ ⟨g, hg, rfl⟩ k`. Rewrite using `[hS']`. Conclude with `hcomm g hg k`. Establish `hh' : ∀ g ∈ G₀, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 → ε ≤ GroundTheory.Automorphic.Reduction.height (GroundTheory.Automorphic.Anisotropic.trHom (Module.finBasis F E) (AF F) g) x`.

Introduce and unpack `_ ⟨g, hg, rfl⟩ x hx`. Take `⟨v, rfl⟩` from `GlobalTheory.CompanionTheory.RedCov.Bridge.cvec_surjective (n := n) (E := E) x`. Establish `hv : v ≠ 0`. Introduce and unpack `rfl`. Apply `hx` to reduce the goal to its premises.

Use function extensionality and compare the values at `p`. Simplify using `[GlobalTheory.CompanionTheory.RedCov.Bridge.cvec]`. Establish `h` using `hh g hg v hv`. Rewrite `h` using `[GlobalTheory.CompanionTheory.RedCov.Bridge.hgt_eq]`. Conclude with `h`.

Take `⟨C, hC, hred⟩` from `Centralizer.exists_isCompact_rational_centralizer J hu S' G₀ hU hS hε hh'`. Establish `hA` using `Centralizer.isCompact_mem_unitary_trHom J hu hC`. Establish `hΩ' : IsCompact ((matHom (AF F) (GroundTheory.Automorphic.conj F E).toAlgHom J) ⁻¹' {w : GL (Fin n) (AF F ⊗[F] E) | w ∈ GroundTheory.Automorphic.unitaryPoints F E J (AF F) ∧ GroundTheory.Automorphic.Anisotropic.trHom (Module.finBasis F E) (AF F) w ∈ C})` using `(isClosedEmbedding_matHom_GAd (GroundTheory.Automorphic.conj F E).toAlgHom J).isCompact_preimage hA`. Use `⟨(L : Set (GAd (GroundTheory.Automorphic.conj F E).toAlgHom J)) ∩ _, hΩ'.inter_left hcl, Set.inter_subset_left, fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨m, hmZ, hmU, hmC⟩` from `hred _ ⟨g, hg, rfl⟩`.

Take `⟨δ, hδ, hδm⟩` from `Centralizer.exists_mem_ratPts J hmU`. Establish `hδL : δ ∈ L`. Use `hrat δ hδ fun k => ?_` and prove the remaining obligations. Rewrite using `[hδm, ← hS']`. Establish `h` using `congrArg (fun X => X.map (GroundTheory.Automorphic.Anisotropic.baseMap α)) (hmZ k)`.

Simplify using `only [GroundTheory.Automorphic.Anisotropic.map_baseMap_mul] at h`. Conclude with `h`. Establish `e : matHom (AF F) (GroundTheory.Automorphic.conj F E).toAlgHom J (δ⁻¹ * g) = (GroundTheory.Automorphic.Anisotropic.diagGL α m)⁻¹ * matHom (AF F) (GroundTheory.Automorphic.conj F E).toAlgHom J g`. Rewrite using `[map_mul, map_inv, hδm]`. Establish `hm : δ⁻¹ * g ∈ L` using `mul_mem (inv_mem hδL) hg`.

Use `⟨δ, hδ, hδL, hm, ?_, ?_⟩` and prove the remaining obligations. Conclude with `hU ⟨_, hm, rfl⟩`. Use `show GroundTheory.Automorphic.Anisotropic.trHom _ _ (matHom (AF F) (GroundTheory.Automorphic.conj F E).toAlgHom J (δ⁻¹ * g)) ∈ C`. Rewrite using `[e]`. Conclude with `hmC`.
-/
theorem exists_isCompact_of_centralizer_height : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (M : Type) [Finite M] (S : M → Matrix (Fin n) (Fin n) E) (L : Subgroup (GAd σ J)), IsClosed (L : Set (GAd σ J)) → (∀ g ∈ L, ∀ k, (matHom _ σ J g).1 * (S k).map (inclR (F := F) (AF F)) = (S k).map (inclR (F := F) (AF F)) * (matHom _ σ J g).1) → (∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ L, ∀ ξ : Fin n → E, ξ ≠ 0 → ε ≤ hgt σ J g ξ) → (∀ γ ∈ ratPts σ J, (∀ k, (matHom _ σ J γ).1 * (S k).map (inclR (F := F) (AF F)) = (S k).map (inclR (F := F) (AF F)) * (matHom _ σ J γ).1) → γ ∈ L) → ∃ Ω : Set (GAd σ J), IsCompact Ω ∧ Ω ⊆ L ∧ ∀ g ∈ L, ∃ δ ∈ ratPts σ J, δ ∈ L ∧ δ⁻¹ * g ∈ Ω := by
  intro F E _ _ _ _ _ σ hσ n J hJ M _ S L hcl hcomm hht hrat
  obtain ⟨ε, hε, hh⟩ := hht
  obtain ⟨hF, hE, h2, hc⟩ := hσ
  have : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  obtain rfl : σ = (GroundTheory.Automorphic.conj F E).toAlgHom := AlgHom.ext fun x =>
    τ.injective ((hc τ x).trans (GroundTheory.Heights₂.Heights.FiniteCovolume.embedding_conj τ x).symm)
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ.2
  let α : F →ₐ[F] AF F := Algebra.ofId F (AF F)
  let S' : M → Matrix (Fin n) (Fin n) (F ⊗[F] E) := fun k =>
    GroundTheory.Automorphic.baseMatrix F (S k) F
  have hS' : ∀ k, (S' k).map (GroundTheory.Automorphic.Anisotropic.baseMap α) =
      (S k).map (inclR (F := F) (AF F)) := fun k =>
    GroundTheory.Automorphic.Anisotropic.baseMatrix_baseMap (S k) α
  let G₀ : Subgroup (GL (Fin n) (AF F ⊗[F] E)) := L.map (matHom (AF F) (GroundTheory.Automorphic.conj F E).toAlgHom J)
  have hU : G₀ ≤ GroundTheory.Automorphic.unitaryPoints F E J (AF F) := by
    rintro _ ⟨g, -, rfl⟩
    rw [← Centralizer.HR_conj_eq]
    exact g.2
  have hS : ∀ g ∈ G₀, ∀ k, (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
      (S' k).map (GroundTheory.Automorphic.Anisotropic.baseMap α) =
      (S' k).map (GroundTheory.Automorphic.Anisotropic.baseMap α) * g := by
    rintro _ ⟨g, hg, rfl⟩ k
    rw [hS']
    exact hcomm g hg k
  have hh' : ∀ g ∈ G₀, ∀ x : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) → F, x ≠ 0 →
      ε ≤ GroundTheory.Automorphic.Reduction.height
        (GroundTheory.Automorphic.Anisotropic.trHom (Module.finBasis F E) (AF F) g) x := by
    rintro _ ⟨g, hg, rfl⟩ x hx
    obtain ⟨v, rfl⟩ := GlobalTheory.CompanionTheory.RedCov.Bridge.cvec_surjective (n := n) (E := E) x
    have hv : v ≠ 0 := by
      rintro rfl
      apply hx
      funext p
      simp [GlobalTheory.CompanionTheory.RedCov.Bridge.cvec]
    have h := hh g hg v hv
    rw [GlobalTheory.CompanionTheory.RedCov.Bridge.hgt_eq] at h
    exact h
  obtain ⟨C, hC, hred⟩ := Centralizer.exists_isCompact_rational_centralizer J hu S' G₀ hU hS hε hh'
  have hA := Centralizer.isCompact_mem_unitary_trHom J hu hC
  have hΩ' : IsCompact ((matHom (AF F) (GroundTheory.Automorphic.conj F E).toAlgHom J) ⁻¹' {w : GL (Fin n) (AF F ⊗[F] E) |
      w ∈ GroundTheory.Automorphic.unitaryPoints F E J (AF F) ∧
      GroundTheory.Automorphic.Anisotropic.trHom (Module.finBasis F E) (AF F) w ∈ C}) :=
    (isClosedEmbedding_matHom_GAd (GroundTheory.Automorphic.conj F E).toAlgHom J).isCompact_preimage hA
  refine ⟨(L : Set (GAd (GroundTheory.Automorphic.conj F E).toAlgHom J)) ∩ _, hΩ'.inter_left hcl, Set.inter_subset_left, fun g hg => ?_⟩
  obtain ⟨m, hmZ, hmU, hmC⟩ := hred _ ⟨g, hg, rfl⟩
  obtain ⟨δ, hδ, hδm⟩ := Centralizer.exists_mem_ratPts J hmU
  have hδL : δ ∈ L := by
    refine hrat δ hδ fun k => ?_
    rw [hδm, ← hS']
    have h := congrArg (fun X => X.map (GroundTheory.Automorphic.Anisotropic.baseMap α)) (hmZ k)
    simp only [GroundTheory.Automorphic.Anisotropic.map_baseMap_mul] at h
    exact h
  have e : matHom (AF F) (GroundTheory.Automorphic.conj F E).toAlgHom J (δ⁻¹ * g) =
      (GroundTheory.Automorphic.Anisotropic.diagGL α m)⁻¹ * matHom (AF F) (GroundTheory.Automorphic.conj F E).toAlgHom J g := by
    rw [map_mul, map_inv, hδm]
  have hm : δ⁻¹ * g ∈ L := mul_mem (inv_mem hδL) hg
  refine ⟨δ, hδ, hδL, hm, ?_, ?_⟩
  · exact hU ⟨_, hm, rfl⟩
  · show GroundTheory.Automorphic.Anisotropic.trHom _ _ (matHom (AF F) (GroundTheory.Automorphic.conj F E).toAlgHom J (δ⁻¹ * g)) ∈ C
    rw [e]
    exact hmC

end GlobalTheory.CompanionTheory.ParCocompact

end
