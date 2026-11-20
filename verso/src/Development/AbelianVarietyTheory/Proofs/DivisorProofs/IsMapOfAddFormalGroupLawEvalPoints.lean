import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedPDivGroupHomCoordinatesExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMapStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz

/- English proof (translation)
Establish `hs : HasSubst (fun i => (C (c.x n i) : MvPowerSeries Empty (G.A n)))` using `hasSubst_of_constantCoeff_nilpotent fun i => by simpa using c.nil n i`. Use `show constantCoeff (substAlgHom (R := k) hs (X i)) = c.x n i`. Rewrite using `[coe_substAlgHom, subst_X hs, constantCoeff_C]`.
-/
theorem Chart.ev_X {p : ℕ} {k : Type} [CommRing k] {d : ℕ} {G : PDivGroup p k} (c : Chart G d)
    (n : ℕ) (i : Fin d) : c.ev n (X i) = c.x n i := by
  have hs : HasSubst (fun i => (C (c.x n i) : MvPowerSeries Empty (G.A n))) :=
    hasSubst_of_constantCoeff_nilpotent fun i => by simpa using c.nil n i
  show constantCoeff (substAlgHom (R := k) hs (X i)) = c.x n i
  rw [coe_substAlgHom, subst_X hs, constantCoeff_C]

/- English proof (translation)
Introduce `p k _ d e G H c c' ν f g φ ψ hν hf hg n j`. Establish `hφ` using `((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d e G H c c' f).2 φ hf).1`. Establish `hψ` using `((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d e G H c c' g).2 ψ hg).1`. Set `L : H.A n ⊗[k] H.A n →ₐ[k] G.A n` to `Algebra.TensorProduct.lift (f.app n : H.A n →ₐ[k] G.A n) (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => Commute.all _ _)`. Establish `hadd : ∀ a, (f + g).app n a = L (Coalgebra.comul a)` using `fun a => by`.

Establish `h` using `congrArg (fun u => u.ofConv a) (map_mul toPts (f.conv n) (g.conv n))`. Simplify using `only [toPts_ofConv] at h`. Conclude with `h.trans (AlgHom.convMul_apply _ _ a)`. Establish `hy : ∀ i, IsNilpotent (L (c'.x₂ n i))` using `fun i => (c'.nil₂ n i).map L`. Establish `ha : ∀ i, constantCoeff (Sum.elim φ ψ i) = 0` using `fun i => by`.

Consider the cases of `i with`. Consider the case `inl i => exact hφ i`. Consider the case `inr i => exact hψ i`. Establish `hnil : ∀ t, IsNilpotent (c.ev n (X t))` using `fun t => by`. Rewrite using `[Chart.ev_X]`.

Conclude with `c.nil n t`. Establish `h1 : ∀ i, c.ev n (Sum.elim φ ψ i) = L (c'.x₂ n i)` using `fun i => by`. Consider the cases of `i with`. Consider the case `inl i`. Express the relevant statement in the definitionally equal form `c.ev n (φ i) = L (c'.x n i ⊗ₜ 1)`.

Rewrite using `[hf, Algebra.TensorProduct.lift_tmul, map_one, mul_one]`. Both sides reduce to the same expression. Consider the case `inr i`. Express the relevant statement in the definitionally equal form `c.ev n (ψ i) = L (1 ⊗ₜ c'.x n i)`. Rewrite using `[hg, Algebra.TensorProduct.lift_tmul, map_one, one_mul]`.

Both sides reduce to the same expression. Establish `e1` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (G.A n)).1 (Fin d) (c.ev n) hnil (Sum.elim φ ψ) ha (fun i => L (c'.x₂ n i)) hy h1 (ν j)`. Establish `e2` using `(GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n) L (c'.x₂ n) (c'.nil₂ n) (fun i => L (c'.x₂ n i)) hy (fun _ => rfl) (ν j)`. Express the relevant statement in the definitionally equal form `c.ev n (subst (Sum.elim φ ψ) (ν j)) = _`. Rewrite using `[e1, ← e2, hadd]`.

Conclude with `congrArg L (hν n j)`.
-/
theorem Chart.isMapOf_add : ∀ (p : ℕ) (k : Type) [CommRing k] (d e : ℕ) (G H : PDivGroup p k)
    (c : Chart G d) (c' : Chart H e), ∀ (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k)
    (f g : G ⟶ H) (φ ψ : Fin e → MvPowerSeries (Fin d) k), c'.IsLawOf ν → c.IsMapOf c' f φ →
    c.IsMapOf c' g ψ → c.IsMapOf c' (f + g) (op ν φ ψ) := by
  intro p k _ d e G H c c' ν f g φ ψ hν hf hg n j
  have hφ := ((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d e G H c c' f).2 φ hf).1
  have hψ := ((GlobalTheory.T.connectedPDivGroupHom_coordinates_existsUnique p k d e G H c c' g).2 ψ hg).1
  let L : H.A n ⊗[k] H.A n →ₐ[k] G.A n := Algebra.TensorProduct.lift
    (f.app n : H.A n →ₐ[k] G.A n) (g.app n : H.A n →ₐ[k] G.A n) (fun _ _ => Commute.all _ _)
  have hadd : ∀ a, (f + g).app n a = L (Coalgebra.comul a) := fun a => by
    have h := congrArg (fun u => u.ofConv a) (map_mul toPts (f.conv n) (g.conv n))
    simp only [toPts_ofConv] at h
    exact h.trans (AlgHom.convMul_apply _ _ a)
  have hy : ∀ i, IsNilpotent (L (c'.x₂ n i)) := fun i => (c'.nil₂ n i).map L
  have ha : ∀ i, constantCoeff (Sum.elim φ ψ i) = 0 := fun i => by
    cases i with
    | inl i => exact hφ i
    | inr i => exact hψ i
  have hnil : ∀ t, IsNilpotent (c.ev n (X t)) := fun t => by
    rw [Chart.ev_X]; exact c.nil n t
  have h1 : ∀ i, c.ev n (Sum.elim φ ψ i) = L (c'.x₂ n i) := fun i => by
    cases i with
    | inl i =>
      change c.ev n (φ i) = L (c'.x n i ⊗ₜ 1)
      rw [hf, Algebra.TensorProduct.lift_tmul, map_one, mul_one]; rfl
    | inr i =>
      change c.ev n (ψ i) = L (1 ⊗ₜ c'.x n i)
      rw [hg, Algebra.TensorProduct.lift_tmul, map_one, one_mul]; rfl
  have e1 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (G.A n)).1 (Fin d) (c.ev n) hnil (Sum.elim φ ψ) ha
    (fun i => L (c'.x₂ n i)) hy h1 (ν j)
  have e2 := (GlobalTheory.T.nilpotent_eval_commutes_subst_and_algebraMap k (Fin e ⊕ Fin e) (H.A n ⊗[k] H.A n)).2 (G.A n) L (c'.x₂ n)
    (c'.nil₂ n) (fun i => L (c'.x₂ n i)) hy (fun _ => rfl) (ν j)
  change c.ev n (subst (Sum.elim φ ψ) (ν j)) = _
  rw [e1, ← e2, hadd]
  exact congrArg L (hν n j)

end GlobalTheory.Katz
