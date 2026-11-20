import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FlagConj

section Linear

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

/- English proof (translation)
Establish `e : κ ≃ Fin n` using `Fintype.equivFinOfCardEq hκ`. Establish `h1 : G' * Bᴴ * J * B = 1` using `by rw [← hG, ← hB]; simp only [Matrix.mul_assoc]`. Establish `h2 : G' * B'ᴴ * J * B' = 1` using `by rw [← hG, ← hB']; simp only [Matrix.mul_assoc]`. Generalize the expression as in `G' * Bᴴ * J = C at h1`. Generalize the expression as in `G' * B'ᴴ * J = C' at h2`.

Establish `h3 : B * C = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).1 h1`. Establish `h4 : B' * C' = 1` using `(Matrix.mul_eq_one_comm_of_equiv e).1 h2`. Use `⟨⟨B' * C, B * C', ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc C, h1, Matrix.one_mul, h4]`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc C', h2, Matrix.one_mul, h3]`.

Express the relevant statement in the definitionally equal form `(B' * C)ᴴ * J * (B' * C) = J`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (B * C)ᴴ * J * (B * C) := by`. Rewrite using `[hB', ← hB]`.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = J := by rw [h3, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`. Express the relevant statement in the definitionally equal form `B' * C * B = B'`. Rewrite using `[Matrix.mul_assoc, h1, Matrix.mul_one]`.
-/
theorem exists_unitary_of_gram {κ : Type} [Fintype κ] [DecidableEq κ] (hκ : Fintype.card κ = n)
    (J : Matrix (Fin n) (Fin n) E) (B B' : Matrix (Fin n) κ E) (G G' : Matrix κ κ E) (hG : G' * G = 1)
    (hB : Bᴴ * J * B = G) (hB' : B'ᴴ * J * B' = G) :
    ∃ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E)ᴴ * J * γ = J ∧ (γ : Matrix (Fin n) (Fin n) E) * B = B' := by
  have e : κ ≃ Fin n := Fintype.equivFinOfCardEq hκ
  have h1 : G' * Bᴴ * J * B = 1 := by rw [← hG, ← hB]; simp only [Matrix.mul_assoc]
  have h2 : G' * B'ᴴ * J * B' = 1 := by rw [← hG, ← hB']; simp only [Matrix.mul_assoc]
  generalize G' * Bᴴ * J = C at h1
  generalize G' * B'ᴴ * J = C' at h2
  have h3 : B * C = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
  have h4 : B' * C' = 1 := (Matrix.mul_eq_one_comm_of_equiv e).1 h2
  refine ⟨⟨B' * C, B * C', ?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C, h1, Matrix.one_mul, h4]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc C', h2, Matrix.one_mul, h3]
  · change (B' * C)ᴴ * J * (B' * C) = J
    calc (B' * C)ᴴ * J * (B' * C) = Cᴴ * (B'ᴴ * J * B') * C := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (B * C)ᴴ * J * (B * C) := by
          rw [hB', ← hB]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = J := by rw [h3, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  · change B' * C * B = B'
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]

def cat {a : ℕ} {j : Fin a → ℕ} (T : ∀ i, Matrix (Fin n) (Fin (j i)) E) :
    Matrix (Fin n) (Σ i, Fin (j i)) E := Matrix.of fun r p => T p.1 r p.2

/- English proof (translation)
Establish `sw : ∀ {α β : Type} (A : Matrix (Fin n) α E) (B : Matrix (Fin n) β E), Bᴴ * J * A = (Aᴴ * J * B)ᴴ`. Introduce `α β A B`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]`. Establish `a11 : (cat T)ᴴ * J * cat T = 0`. Use extensionality with `⟨i, s⟩ ⟨k, t⟩`.

Conclude with `congrFun (congrFun (h1 i k).1 s) t`. Establish `a22 : (cat T')ᴴ * J * cat T' = 0`. Use extensionality with `⟨i, s⟩ ⟨k, t⟩`. Conclude with `congrFun (congrFun (h1 i k).2.1 s) t`. Establish `a12 : (cat T)ᴴ * J * cat T' = 1`.

Use extensionality with `⟨i, s⟩ ⟨k, t⟩`. Distinguish the cases in `h : i = k`. Substitute `h` using the available equality. Use `(congrFun (congrFun (h2 i).1 s) t).trans ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply]`.

Use `(congrFun (congrFun ((h1 i k).2.2 h) s) t).trans ?_` and prove the remaining obligations. Simplify using `[Matrix.one_apply, h]`. Establish `a13 : (cat T)ᴴ * J * T₀ = 0`. Use extensionality with `⟨i, s⟩ t`. Conclude with `congrFun (congrFun (h2 i).2.1 s) t`.

Establish `a23 : (cat T')ᴴ * J * T₀ = 0`. Use extensionality with `⟨i, s⟩ t`. Conclude with `congrFun (congrFun (h2 i).2.2 s) t`. Establish `a21 : (cat T')ᴴ * J * cat T = 1` using `by rw [sw, a12, Matrix.conjTranspose_one]`. Establish `a31 : T₀ᴴ * J * cat T = 0` using `by rw [sw, a13, Matrix.conjTranspose_zero]`.

Establish `a32 : T₀ᴴ * J * cat T' = 0` using `by rw [sw, a23, Matrix.conjTranspose_zero]`. Use extensionality with `((p | p) | p) ((q | q) | q)`. Conclude with `congrFun (congrFun a11 p) q`. Conclude with `congrFun (congrFun a12 p) q`. Conclude with `congrFun (congrFun a13 p) q`.

Conclude with `congrFun (congrFun a21 p) q`. Conclude with `congrFun (congrFun a22 p) q`. Conclude with `congrFun (congrFun a23 p) q`. Conclude with `congrFun (congrFun a31 p) q`. Conclude with `congrFun (congrFun a32 p) q`.

Conclude with `congrFun (congrFun h3 p) q`.
-/
theorem gram_adapted {a m : ℕ} {j : Fin a → ℕ} (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J)
    (J₀ : Matrix (Fin m) (Fin m) E) (T T' : ∀ i, Matrix (Fin n) (Fin (j i)) E) (T₀ : Matrix (Fin n) (Fin m) E)
    (h1 : ∀ i k, (T i)ᴴ * J * T k = 0 ∧ (T' i)ᴴ * J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * J * T' k = 0))
    (h2 : ∀ i, (T i)ᴴ * J * T' i = 1 ∧ (T i)ᴴ * J * T₀ = 0 ∧ (T' i)ᴴ * J * T₀ = 0)
    (h3 : T₀ᴴ * J * T₀ = J₀) :
    (fromCols (fromCols (cat T) (cat T')) T₀)ᴴ * J * fromCols (fromCols (cat T) (cat T')) T₀ =
      fromBlocks (fromBlocks 0 1 1 0) 0 0 J₀ := by
  have sw : ∀ {α β : Type} (A : Matrix (Fin n) α E) (B : Matrix (Fin n) β E),
      Bᴴ * J * A = (Aᴴ * J * B)ᴴ := by
    intro α β A B
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJ, Matrix.mul_assoc]
  have a11 : (cat T)ᴴ * J * cat T = 0 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    exact congrFun (congrFun (h1 i k).1 s) t
  have a22 : (cat T')ᴴ * J * cat T' = 0 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    exact congrFun (congrFun (h1 i k).2.1 s) t
  have a12 : (cat T)ᴴ * J * cat T' = 1 := by
    ext ⟨i, s⟩ ⟨k, t⟩
    by_cases h : i = k
    · subst h
      refine (congrFun (congrFun (h2 i).1 s) t).trans ?_
      simp [Matrix.one_apply]
    · refine (congrFun (congrFun ((h1 i k).2.2 h) s) t).trans ?_
      simp [Matrix.one_apply, h]
  have a13 : (cat T)ᴴ * J * T₀ = 0 := by
    ext ⟨i, s⟩ t
    exact congrFun (congrFun (h2 i).2.1 s) t
  have a23 : (cat T')ᴴ * J * T₀ = 0 := by
    ext ⟨i, s⟩ t
    exact congrFun (congrFun (h2 i).2.2 s) t
  have a21 : (cat T')ᴴ * J * cat T = 1 := by rw [sw, a12, Matrix.conjTranspose_one]
  have a31 : T₀ᴴ * J * cat T = 0 := by rw [sw, a13, Matrix.conjTranspose_zero]
  have a32 : T₀ᴴ * J * cat T' = 0 := by rw [sw, a23, Matrix.conjTranspose_zero]
  ext ((p | p) | p) ((q | q) | q)
  · exact congrFun (congrFun a11 p) q
  · exact congrFun (congrFun a12 p) q
  · exact congrFun (congrFun a13 p) q
  · exact congrFun (congrFun a21 p) q
  · exact congrFun (congrFun a22 p) q
  · exact congrFun (congrFun a23 p) q
  · exact congrFun (congrFun a31 p) q
  · exact congrFun (congrFun a32 p) q
  · exact congrFun (congrFun h3 p) q

/- English proof (translation)
Take `⟨γ, hγ, hB⟩` from `exists_unitary_of_gram (κ := ((Σ i, Fin (j i)) ⊕ (Σ i, Fin (j i))) ⊕ Fin m) (by simp [hn]; ring) J _ _ _ (fromBlocks (fromBlocks 0 1 1 0) 0 0 J₀⁻¹) (by simp [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ₀)]) (gram_adapted J hJ J₀ T T' T₀ h1 h2 h3) (gram_adapt …`. Use `⟨γ, hγ, fun i => ?_, fun i => ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `r s`. Conclude with `congrFun (congrFun hB r) (Sum.inl (Sum.inl ⟨i, s⟩))`. Use extensionality with `r s`.

Conclude with `congrFun (congrFun hB r) (Sum.inl (Sum.inr ⟨i, s⟩))`. Use extensionality with `r s`. Conclude with `congrFun (congrFun hB r) (Sum.inr s)`.
-/
theorem exists_unitary_adapted {a m : ℕ} {j : Fin a → ℕ} (hn : n = m + 2 * ∑ i, j i)
    (J : Matrix (Fin n) (Fin n) E) (hJ : Jᴴ = J) (J₀ : Matrix (Fin m) (Fin m) E) (hJ₀ : J₀.det ≠ 0)
    (T T' U U' : ∀ i, Matrix (Fin n) (Fin (j i)) E) (T₀ U₀ : Matrix (Fin n) (Fin m) E)
    (h1 : ∀ i k, (T i)ᴴ * J * T k = 0 ∧ (T' i)ᴴ * J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * J * T' k = 0))
    (h2 : ∀ i, (T i)ᴴ * J * T' i = 1 ∧ (T i)ᴴ * J * T₀ = 0 ∧ (T' i)ᴴ * J * T₀ = 0)
    (h3 : T₀ᴴ * J * T₀ = J₀)
    (g1 : ∀ i k, (U i)ᴴ * J * U k = 0 ∧ (U' i)ᴴ * J * U' k = 0 ∧ (i ≠ k → (U i)ᴴ * J * U' k = 0))
    (g2 : ∀ i, (U i)ᴴ * J * U' i = 1 ∧ (U i)ᴴ * J * U₀ = 0 ∧ (U' i)ᴴ * J * U₀ = 0)
    (g3 : U₀ᴴ * J * U₀ = J₀) :
    ∃ γ : GL (Fin n) E, (γ : Matrix (Fin n) (Fin n) E)ᴴ * J * γ = J ∧
      (∀ i, (γ : Matrix (Fin n) (Fin n) E) * T i = U i) ∧ (∀ i, (γ : Matrix (Fin n) (Fin n) E) * T' i = U' i) ∧
      (γ : Matrix (Fin n) (Fin n) E) * T₀ = U₀ := by
  obtain ⟨γ, hγ, hB⟩ := exists_unitary_of_gram
    (κ := ((Σ i, Fin (j i)) ⊕ (Σ i, Fin (j i))) ⊕ Fin m) (by simp [hn]; ring) J _ _ _
    (fromBlocks (fromBlocks 0 1 1 0) 0 0 J₀⁻¹)
    (by simp [Matrix.fromBlocks_multiply, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ₀)])
    (gram_adapted J hJ J₀ T T' T₀ h1 h2 h3) (gram_adapted J hJ J₀ U U' U₀ g1 g2 g3)
  refine ⟨γ, hγ, fun i => ?_, fun i => ?_, ?_⟩
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inl (Sum.inl ⟨i, s⟩))
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inl (Sum.inr ⟨i, s⟩))
  · ext r s
    exact congrFun (congrFun hB r) (Sum.inr s)

end Linear

/- English proof (translation)
Establish `e : Formalism.UG.cT s (g.map φ) = (Formalism.UG.cT σ g).map φ`. Use extensionality with `i k`. Simplify using `[Formalism.UG.cT, h]`. Rewrite using `[e, ← Matrix.map_mul, ← Matrix.map_mul, hg]`.
-/
theorem unitary_map {E A : Type} [CommRing E] [CommRing A] {n : ℕ} (σ : E →+* E) (s : A →+* A) (φ : E →+* A)
    (h : ∀ e, s (φ e) = φ (σ e)) (J g : Matrix (Fin n) (Fin n) E) (hg : Formalism.UG.cT σ g * J * g = J) :
    Formalism.UG.cT s (g.map φ) * J.map φ * g.map φ = J.map φ := by
  have e : Formalism.UG.cT s (g.map φ) = (Formalism.UG.cT σ g).map φ := by
    ext i k
    simp [Formalism.UG.cT, h]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, hg]

/- English proof (translation)
Establish `hφ : ∀ v e, starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e)` using `fun v e => (I.cm.cmUnram.2.1 (I.φ v) e).symm`. Establish `hf : ∀ e, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F` using `I.F) (Af I.F) e) = Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by`. Introduce `e`. Simplify using `[Formalism.UG.sigR, Formalism.UG.inclE]`. Both sides reduce to the same expression.

Establish `hPP : ∀ v, I.P v * (I.P v)⁻¹ = 1` using `fun v => Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))`. Set `u : ∀ v : InfinitePlace I.F, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ` to `fun v => (I.P_unit v).unit⁻¹ * Formalism.UG.bc (I.φ v) γ * (I.P_unit v).unit`. Establish `hu : ∀ v, (u v : Matrix (Fin I.n) (Fin I.n) ℂ) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v`. Introduce `v`. Simplify using `only [u, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]`.

Both sides reduce to the same expression. Establish `hPu : ∀ v, I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v`. Introduce `v`. Rewrite using `[hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]`. Establish `hU : ∀ v, u v ∈ Formalism.REAL.UJ (I.ε v)`.

Introduce `v`. Express the relevant statement in the definitionally equal form `(u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * Formalism.REAL.Jm (I.ε v) * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) = Formalism.REAL.Jm (I.ε v)`. Establish `h` using `unitary_map _ _ (I.φ v) (hφ v) I.J _ hγ`. Establish `hc : Formalism.UG.cT (starRingEnd ℂ) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) = ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ`. Use extensionality with `i j`.

Simplify using `[Formalism.UG.cT]`. Rewrite `h` using `[hc]`. Rewrite using `[← I.P_spec v]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = (I.P v)ᴴ * (((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by`. Rewrite using `[hPu]`. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [h]`. Establish `hF : Formalism.UG.bc (Formalism.UG.inclE (F` using `I.F) (Af I.F)) γ ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := unitary_map _ _ _ hf I.J _ hγ`.

Conclude with `⟨(fun v => ⟨u v, hU v⟩, ⟨_, hF⟩), hu, rfl⟩`.
-/
theorem exists_point (I : AutInst) (γ : GL (Fin I.n) I.E) (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) :
    ∃ a : I.GA,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hφ : ∀ v e, starRingEnd ℂ (I.φ v e) = I.φ v (starRingEnd I.E e) :=
    fun v e => (I.cm.cmUnram.2.1 (I.φ v) e).symm
  have hf : ∀ e, Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) e) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by
    intro e
    simp [Formalism.UG.sigR, Formalism.UG.inclE]
    rfl
  have hPP : ∀ v, I.P v * (I.P v)⁻¹ = 1 := fun v =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))
  let u : ∀ v : InfinitePlace I.F, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Formalism.UG.bc (I.φ v) γ * (I.P_unit v).unit
  have hu : ∀ v, (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [u, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hPu : ∀ v, I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    rw [hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
  have hU : ∀ v, u v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    change (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * Formalism.REAL.Jm (I.ε v) *
      (u v : Matrix (Fin I.n) (Fin I.n) ℂ) = Formalism.REAL.Jm (I.ε v)
    have h := unitary_map _ _ (I.φ v) (hφ v) I.J _ hγ
    have hc : Formalism.UG.cT (starRingEnd ℂ) ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) =
        ((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ := by
      ext i j
      simp [Formalism.UG.cT]
    rw [hc] at h
    rw [← I.P_spec v]
    calc (u v : Matrix (Fin I.n) (Fin I.n) ℂ)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v) *
          (u v : Matrix (Fin I.n) (Fin I.n) ℂ)
        = (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ))ᴴ * I.J.map (I.φ v) *
          (I.P v * (u v : Matrix (Fin I.n) (Fin I.n) ℂ)) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (I.P v)ᴴ * (((γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v))ᴴ * I.J.map (I.φ v) *
          (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v)) * I.P v := by
          rw [hPu]
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h]
  have hF : Formalism.UG.bc (Formalism.UG.inclE (F := I.F) (Af I.F)) γ ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) :=
    unitary_map _ _ _ hf I.J _ hγ
  exact ⟨(fun v => ⟨u v, hU v⟩, ⟨_, hF⟩), hu, rfl⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ratIso (I : AutInst) (γ : GL (Fin I.n) I.E) (N : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (z : Fin I.n → I.E) :
    z ∈ GlobalTheory.PointEquivariance.ratIso I γ N ↔ ∃ y ∈ N, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y = z := Iff.rfl

/- English proof (translation)
Introduce `I I₀ e xf a j S Λ x₀ T T' T₀ _ ⟨_, hn, _, h1, h2, h3, h4, h5⟩ xf' S' U U' U₀ ⟨_, _, _, g1, g2, g3, g4, g5⟩`. Establish `hcT : ∀ M : Matrix (Fin I.n) (Fin I.n) I.E, Formalism.UG.cT (starRingEnd I.E) M = Mᴴ` using `fun M => rfl`. Establish `hJ : I.Jᴴ = I.J` using `(hcT _).symm.trans I.J_herm`. Establish `hJ₀ : (I₀.J.map e).det ≠ 0`. Use `RingHom.map_det (e : I₀.E →+* I.E) I₀.J` as an intermediate fact.

Express the relevant statement in the definitionally equal form `e _ = (I₀.J.map e).det at this`. Rewrite using `[← this]`. Conclude with `(map_ne_zero e).2 I₀.J_det`. Take `⟨γ, hγ, c1, c2, c3⟩` from `exists_unitary_adapted hn I.J hJ _ hJ₀ T T' U U' T₀ U₀ h1 h2 h3 g1 g2 g3`. Establish `hγ' : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J` using `hγ`.

Take `⟨c, hc1, hc2⟩` from `exists_point I γ hγ'`. Establish `d1 : ∀ u : ∀ i, Fin (j i) → I.E, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ ∑ i, T i *ᵥ u i = ∑ i, U i *ᵥ u i`. Introduce `u`. Simplify using `only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, c1]`. Establish `d2 : ∀ u : ∀ i, Fin (j i) → I.E, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ ∑ i, T' i *ᵥ u i = ∑ i, U' i *ᵥ u i`.

Introduce `u`. Simplify using `only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, c2]`. Establish `hS : ∀ k, S' k = GlobalTheory.PointEquivariance.ratIso I γ (S k)`. Introduce `k`. Use extensionality with `z`.

Rewrite using `[g5, mem_ratIso]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, p1, p2, rfl⟩`. Conclude with `⟨_, (h5 k _).2 ⟨u, p1, p2, rfl⟩, d1 u⟩`. Introduce and unpack `⟨y, hy, rfl⟩`.

Take `⟨u, p1, p2, rfl⟩` from `(h5 k y).1 hy`. Conclude with `⟨u, p1, p2, d1 u⟩`. Establish `hL : lamX I (c * (1, xf)) = lamX I (1, xf')`. Rewrite using `[GlobalTheory.PointEquivariance.lamX_rat I _ c γ hc2]`. Use extensionality with `z`.

Rewrite using `[g4, mem_ratIso]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Take `⟨u, u', w, p1, p2, p3, rfl⟩` from `(h4 y).1 hy`. Use `⟨u, u', w, p1, p2, p3, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_add, d1, d2, Matrix.mulVec_mulVec, c3]`. Introduce and unpack `⟨u, u', w, p1, p2, p3, rfl⟩`. Use `⟨_, (h4 _).2 ⟨u, u', w, p1, p2, p3, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_add, d1, d2, Matrix.mulVec_mulVec, c3]`. Use `⟨c, ⟨γ, hγ', hc1, hc2⟩, xf'⁻¹ * (c.2 * xf), ?_, (mul_inv_cancel_left _ _).symm, fun g => ?_⟩` and prove the remaining obligations.

Use `(GlobalTheory.PointEquivariance.lamX_mul_eq_iff I (1, xf') (((1, xf') : I.GA)⁻¹ * (c * (1, xf)))).2 (by rw [mul_inv_cancel_left, hL])` as an intermediate fact. Conclude with `this`. Use function extensionality and compare the values at `i`. Establish `hfr : frm I (c.1 * g, xf') = frm I (c * (g, xf))` using `rfl`. Unfold `sizesAt`.

Rewrite using `[hfr, hS, hS]`. Conclude with `GlobalTheory.PointEquivariance.sizeQ_eq _ _ _ _ (GlobalTheory.PointEquivariance.zl_ratIso I (g, xf) c γ hc1) (GlobalTheory.PointEquivariance.rkK_ratIso I γ) _ _`.
-/
theorem conjugate_of_isAdapted : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), (∀ i, 1 ≤ j i) → IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ (xf' : I.Gf) (S' : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (U U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf' j S' Λ x₀ U U' U₀ → ∃ γ ∈ I.GFset, ∃ k ∈ I.Kset, γ.2 * xf = xf' * k ∧ ∀ g : I.Ginf, sizesAt I xf' S' (γ.1 * g) = sizesAt I xf S g := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ _ ⟨_, hn, _, h1, h2, h3, h4, h5⟩ xf' S' U U' U₀ ⟨_, _, _, g1, g2, g3, g4, g5⟩
  have hcT : ∀ M : Matrix (Fin I.n) (Fin I.n) I.E, Formalism.UG.cT (starRingEnd I.E) M = Mᴴ := fun M => rfl
  have hJ : I.Jᴴ = I.J := (hcT _).symm.trans I.J_herm
  have hJ₀ : (I₀.J.map e).det ≠ 0 := by
    have := RingHom.map_det (e : I₀.E →+* I.E) I₀.J
    change e _ = (I₀.J.map e).det at this
    rw [← this]
    exact (map_ne_zero e).2 I₀.J_det
  obtain ⟨γ, hγ, c1, c2, c3⟩ := exists_unitary_adapted hn I.J hJ _ hJ₀ T T' U U' T₀ U₀ h1 h2 h3 g1 g2 g3
  have hγ' : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := hγ
  obtain ⟨c, hc1, hc2⟩ := exists_point I γ hγ'
  have d1 : ∀ u : ∀ i, Fin (j i) → I.E,
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ ∑ i, T i *ᵥ u i = ∑ i, U i *ᵥ u i := by
    intro u
    simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, c1]
  have d2 : ∀ u : ∀ i, Fin (j i) → I.E,
      (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ ∑ i, T' i *ᵥ u i = ∑ i, U' i *ᵥ u i := by
    intro u
    simp only [Matrix.mulVec_sum, Matrix.mulVec_mulVec, c2]
  have hS : ∀ k, S' k = GlobalTheory.PointEquivariance.ratIso I γ (S k) := by
    intro k
    ext z
    rw [g5, mem_ratIso]
    constructor
    · rintro ⟨u, p1, p2, rfl⟩
      exact ⟨_, (h5 k _).2 ⟨u, p1, p2, rfl⟩, d1 u⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, p1, p2, rfl⟩ := (h5 k y).1 hy
      exact ⟨u, p1, p2, d1 u⟩
  have hL : lamX I (c * (1, xf)) = lamX I (1, xf') := by
    rw [GlobalTheory.PointEquivariance.lamX_rat I _ c γ hc2]
    ext z
    rw [g4, mem_ratIso]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, u', w, p1, p2, p3, rfl⟩ := (h4 y).1 hy
      refine ⟨u, u', w, p1, p2, p3, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_add, d1, d2, Matrix.mulVec_mulVec, c3]
    · rintro ⟨u, u', w, p1, p2, p3, rfl⟩
      refine ⟨_, (h4 _).2 ⟨u, u', w, p1, p2, p3, rfl⟩, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_add, d1, d2, Matrix.mulVec_mulVec, c3]
  refine ⟨c, ⟨γ, hγ', hc1, hc2⟩, xf'⁻¹ * (c.2 * xf), ?_, (mul_inv_cancel_left _ _).symm, fun g => ?_⟩
  · have := (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I (1, xf') (((1, xf') : I.GA)⁻¹ * (c * (1, xf)))).2
      (by rw [mul_inv_cancel_left, hL])
    exact this
  · funext i
    have hfr : frm I (c.1 * g, xf') = frm I (c * (g, xf)) := rfl
    unfold sizesAt
    rw [hfr, hS, hS]
    exact GlobalTheory.PointEquivariance.sizeQ_eq _ _ _ _ (GlobalTheory.PointEquivariance.zl_ratIso I (g, xf) c γ hc1)
      (GlobalTheory.PointEquivariance.rkK_ratIso I γ) _ _

end GlobalTheory.FlagConj
