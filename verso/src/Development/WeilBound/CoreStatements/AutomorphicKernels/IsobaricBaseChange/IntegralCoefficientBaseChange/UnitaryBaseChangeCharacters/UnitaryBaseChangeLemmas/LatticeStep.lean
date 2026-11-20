import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ExistsPolyOfCommute

open Polynomial Matrix Formalism.UG

noncomputable section

namespace GlobalTheory.UsideLeaf.UnitaryLocalCharpoly

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Use `set f : intL L →+* L := (intL L).subtype with hf`. Establish `finj : Function.Injective f` using `Subtype.val_injective`. Use `set γ' : Matrix (Fin n) (Fin n) L := (k⁻¹ : GL (Fin n) L).val * γ * k.val with hγ'`. Set `γ₀ : Matrix (Fin n) (Fin n) (intL L)` to `Matrix.of fun i j => ⟨γ i j, hγ i j⟩`. Set `γ₁ : Matrix (Fin n) (Fin n) (intL L)` to `Matrix.of fun i j => ⟨γ' i j, hk i j⟩`.

Establish `e₀ : γ₀.map f = γ`. Use extensionality with `i j`. Both sides reduce to the same expression. Establish `e₁ : γ₁.map f = γ'`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `cγ' : γ'.charpoly = γ.charpoly`. Rewrite using `[hγ', Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]`. Establish `c₀ : γ₀.charpoly = Q₀`. Apply `Polynomial.map_injective f finj` to reduce the goal to its premises.

Rewrite using `[← Matrix.charpoly_map, e₀, hch]`. Establish `c₁ : γ₁.charpoly = Q₀`. Apply `Polynomial.map_injective f finj` to reduce the goal to its premises. Rewrite using `[← Matrix.charpoly_map, e₁, cγ', hch]`. Take `⟨v₀, hv₀⟩` from `GlobalTheory.BCT.UnitStable.exists_cyclic γ₀ (c₀ ▸ hsep)`.

Take `⟨v₁, hv₁⟩` from `GlobalTheory.BCT.UnitStable.exists_cyclic γ₁ (c₁ ▸ hsep)`. Use `set u₀ := hv₀.unit`. Use `set u₁ := hv₁.unit`. Use `set C := GlobalTheory.Orb.companionMat n Q₀`. Establish `h₀ : γ₀ * (u₀ : Matrix (Fin n) (Fin n) (intL L)) = u₀ * C`.

Use `GlobalTheory.Orb.mul_krylov_eq γ₀ v₀` as an intermediate fact. Rewrite `this` using `[c₀]`. Simplify `this` using `[u₀]`. Establish `h₁ : γ₁ * (u₁ : Matrix (Fin n) (Fin n) (intL L)) = u₁ * C`. Use `GlobalTheory.Orb.mul_krylov_eq γ₁ v₁` as an intermediate fact.

Rewrite `this` using `[c₁]`. Simplify `this` using `[u₁]`. Use `set u := u₀ * u₁⁻¹`. Establish `hu : γ₀ * (u : Matrix (Fin n) (Fin n) (intL L)) = u * γ₁`. Establish `e : ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * γ₁ = C * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L))`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Units.val_mul, ← Matrix.mul_assoc, h₀, Matrix.mul_assoc, Matrix.mul_assoc, e]`. Use `set F : Matrix (Fin n) (Fin n) (intL L) →* Matrix (Fin n) (Fin n) L := (f.mapMatrix : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L).toMonoidHom`. Use `set g : GL (Fin n) L := Units.map F u`. Establish `hgval : g.val = (u : Matrix (Fin n) (Fin n) (intL L)).map f` using `rfl`.

Establish `hginv : (g⁻¹ : GL (Fin n) L).val = ((u⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)).map f` using `rfl`. Establish `hgg : γ * g.val = g.val * γ'`. Rewrite using `[hgval, ← e₀, ← e₁, ← Matrix.map_mul, ← Matrix.map_mul, hu]`. Establish `hgi : (g⁻¹ : GL (Fin n) L).val * γ = γ' * (g⁻¹ : GL (Fin n) L).val`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨k * g⁻¹, g, ?_, by group, fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Matrix.mul_assoc, hgi, hγ']`. Simplify using `only [Matrix.mul_assoc, Units.mul_inv_cancel_left]`. Rewrite using `[hgval]`. Conclude with `((u : Matrix (Fin n) (Fin n) (intL L)) i j).2`.

Rewrite using `[hginv]`. Conclude with `(((u⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) i j).2`.
-/
theorem lattice_step {n : ℕ} (γ γi : Matrix (Fin n) (Fin n) L) (Q₀ : (intL L)[X])
    (hγ : ∀ i j, γ i j ∈ intL L) (hγi : ∀ i j, γi i j ∈ intL L) (hγγ : γ * γi = 1)
    (hch : γ.charpoly = Q₀.map (intL L).subtype) (hsep : Q₀.Separable) (k : GL (Fin n) L)
    (hk : ∀ i j, ((k⁻¹ : GL (Fin n) L).val * γ * k.val) i j ∈ intL L)
    (hki : ∀ i j, ((k⁻¹ : GL (Fin n) L).val * γi * k.val) i j ∈ intL L) :
    ∃ a g : GL (Fin n) L, a.val * γ = γ * a.val ∧ k = a * g ∧ (∀ i j, g.val i j ∈ intL L) ∧
      (∀ i j, (g⁻¹ : GL (Fin n) L).val i j ∈ intL L) := by
  set f : intL L →+* L := (intL L).subtype with hf
  have finj : Function.Injective f := Subtype.val_injective
  set γ' : Matrix (Fin n) (Fin n) L := (k⁻¹ : GL (Fin n) L).val * γ * k.val with hγ'
  let γ₀ : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨γ i j, hγ i j⟩
  let γ₁ : Matrix (Fin n) (Fin n) (intL L) := Matrix.of fun i j => ⟨γ' i j, hk i j⟩
  have e₀ : γ₀.map f = γ := by
    ext i j
    rfl
  have e₁ : γ₁.map f = γ' := by
    ext i j
    rfl
  have cγ' : γ'.charpoly = γ.charpoly := by
    rw [hγ', Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have c₀ : γ₀.charpoly = Q₀ := by
    apply Polynomial.map_injective f finj
    rw [← Matrix.charpoly_map, e₀, hch]
  have c₁ : γ₁.charpoly = Q₀ := by
    apply Polynomial.map_injective f finj
    rw [← Matrix.charpoly_map, e₁, cγ', hch]
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.BCT.UnitStable.exists_cyclic γ₀ (c₀ ▸ hsep)
  obtain ⟨v₁, hv₁⟩ := GlobalTheory.BCT.UnitStable.exists_cyclic γ₁ (c₁ ▸ hsep)
  set u₀ := hv₀.unit
  set u₁ := hv₁.unit
  set C := GlobalTheory.Orb.companionMat n Q₀
  have h₀ : γ₀ * (u₀ : Matrix (Fin n) (Fin n) (intL L)) = u₀ * C := by
    have := GlobalTheory.Orb.mul_krylov_eq γ₀ v₀
    rw [c₀] at this
    simpa [u₀] using this
  have h₁ : γ₁ * (u₁ : Matrix (Fin n) (Fin n) (intL L)) = u₁ * C := by
    have := GlobalTheory.Orb.mul_krylov_eq γ₁ v₁
    rw [c₁] at this
    simpa [u₁] using this
  set u := u₀ * u₁⁻¹
  have hu : γ₀ * (u : Matrix (Fin n) (Fin n) (intL L)) = u * γ₁ := by
    have e : ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * γ₁ = C * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) := by
      calc ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * γ₁
          = ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * (γ₁ * (u₁ : Matrix (Fin n) (Fin n) (intL L)) * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L))) := by rw [Units.mul_inv_cancel_right]
        _ = ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) * ((u₁ : Matrix (Fin n) (Fin n) (intL L)) * C * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L))) := by rw [h₁]
        _ = C * ((u₁⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) := by simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
    rw [Units.val_mul, ← Matrix.mul_assoc, h₀, Matrix.mul_assoc, Matrix.mul_assoc, e]
  set F : Matrix (Fin n) (Fin n) (intL L) →* Matrix (Fin n) (Fin n) L := (f.mapMatrix : Matrix (Fin n) (Fin n) (intL L) →+* Matrix (Fin n) (Fin n) L).toMonoidHom
  set g : GL (Fin n) L := Units.map F u
  have hgval : g.val = (u : Matrix (Fin n) (Fin n) (intL L)).map f := rfl
  have hginv : (g⁻¹ : GL (Fin n) L).val = ((u⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)).map f := rfl
  have hgg : γ * g.val = g.val * γ' := by
    rw [hgval, ← e₀, ← e₁, ← Matrix.map_mul, ← Matrix.map_mul, hu]
  have hgi : (g⁻¹ : GL (Fin n) L).val * γ = γ' * (g⁻¹ : GL (Fin n) L).val := by
    calc (g⁻¹ : GL (Fin n) L).val * γ
        = (g⁻¹ : GL (Fin n) L).val * (γ * g.val * (g⁻¹ : GL (Fin n) L).val) := by rw [Units.mul_inv_cancel_right]
      _ = (g⁻¹ : GL (Fin n) L).val * (g.val * γ' * (g⁻¹ : GL (Fin n) L).val) := by rw [hgg]
      _ = γ' * (g⁻¹ : GL (Fin n) L).val := by simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
  refine ⟨k * g⁻¹, g, ?_, by group, fun i j => ?_, fun i j => ?_⟩
  · rw [Units.val_mul, Matrix.mul_assoc, hgi, hγ']
    simp only [Matrix.mul_assoc, Units.mul_inv_cancel_left]
  · rw [hgval]
    exact ((u : Matrix (Fin n) (Fin n) (intL L)) i j).2
  · rw [hginv]
    exact (((u⁻¹ : (Matrix (Fin n) (Fin n) (intL L))ˣ) : Matrix (Fin n) (Fin n) (intL L)) i j).2

end GlobalTheory.UsideLeaf.UnitaryLocalCharpoly
