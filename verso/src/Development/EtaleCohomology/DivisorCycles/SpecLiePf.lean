import Development.EtaleCohomology.DivisorCycles.OpenCoset

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div
namespace LateralTheory.DivDb.SpecLiePf
open LateralTheory.DivDb

/- English proof (translation)
Introduce `Γ K K' _ _ _ _ _ N n ρ X e hX hL hR`. Set `x : (Fin N × Fin N) ⊕ Fin n → K'` to `Sum.elim (fun p => X p.1 p.2) e`. Set `gAB : Finset (Fin n) → Finset (Fin n) → MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K` to `fun A B => MvPolynomial.C (B.card : K) * ∑ i ∈ A, MvPolynomial.X (Sum.inr i) - MvPolynomial.C (A.card : K) * ∑ i ∈ B, MvPolynomial.X (Sum.inr i)`. Set `G : Set (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K)` to `{g | ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ g = gAB A B}`. Establish `hGf : G.Finite` using `(Set.finite_range (fun AB : Finset (Fin n) × Finset (Fin n) => gAB AB.1 AB.2)).subset (by rintro g ⟨A, B, -, -, -, rfl⟩; exact ⟨(A, B), rfl⟩)`.

Establish `haG : ∀ g ∈ G, MvPolynomial.aeval x g ≠ 0`. Introduce and unpack `g ⟨A, B, hA, hB, hAB, rfl⟩`. Simplify using `only [gAB, map_sub, map_mul, map_sum, MvPolynomial.aeval_X, x, Sum.elim_inr, map_natCast]`. Conclude with `sub_ne_zero.mpr (hL A B hA hB hAB)`. Take `⟨y, hy, hyG⟩` from `hS K K' _ x G hGf haG`.

Use `⟨Matrix.of fun a b => y (Sum.inl (a, b)), fun i => y (Sum.inr i), ?_, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `∀ f ∈ Van (img ρ ⊤ : Set (Mat K N)), dAt f 1 _ = 0`. Introduce `f hf`. Establish `hf' : ∀ g : Γ, MvPolynomial.eval (fun p : Fin N × Fin N => (ρ g : Matrix (Fin N) (Fin N) K) p.1 p.2) f = 0` using `fun g => hf _ ⟨g, trivial, rfl⟩`. Establish `h0` using `hX f hf'`.

Set `L : MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K` to `∑ p : Fin N × Fin N, MvPolynomial.C (MvPolynomial.eval (fun q : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) K) q.1 q.2) (MvPolynomial.pderiv p f)) * MvPolynomial.X (Sum.inl p)`. Establish `hxL : MvPolynomial.aeval x L = 0`. Simplify `h0` using `only [L, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, x, Sum.elim_inl]`. Establish `h1` using `hy L hxL`. Simplify `h1` using `only [L, dAt, ev, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.of_apply]`.

Introduce `A B hA hB hAB`. Establish `h1` using `hyG _ ⟨A, B, hA, hB, hAB, rfl⟩`. Simplify using `only [gAB, map_sub, map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X] at h1`. Conclude with `sub_ne_zero.mp h1`. Introduce `i`.

Set `M : Matrix (Fin N) (Fin N) (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K)` to `Matrix.scalar (Fin N) (MvPolynomial.X (Sum.inr i)) - Matrix.of (fun a b => MvPolynomial.X (Sum.inl (a, b)))`. Establish `hx : MvPolynomial.aeval x M.det = 0`. Establish `e1 : MvPolynomial.aeval x M.det = ((MvPolynomial.aeval x).toRingHom.mapMatrix M).det`. Rewrite using `[← RingHom.map_det]`. Both sides reduce to the same expression.

Establish `e2 : (MvPolynomial.aeval x).toRingHom.mapMatrix M = Matrix.scalar (Fin N) (e i) - X`. Use extensionality with `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[M, x]`.

Simplify using `[M, x, h]`. Rewrite using `[e1, e2, ← Matrix.eval_charpoly]`. Conclude with `hR i`. Establish `h1` using `hy _ hx`. Establish `e1 : MvPolynomial.eval y M.det = ((MvPolynomial.eval y).mapMatrix M).det`.

Rewrite using `[← RingHom.map_det]`. Establish `e2 : (MvPolynomial.eval y).mapMatrix M = Matrix.scalar (Fin N) (y (Sum.inr i)) - Matrix.of (fun a b => y (Sum.inl (a, b)))`. Use extensionality with `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Simplify using `[M]`. Simplify using `[M, h]`. Rewrite `h1` using `[e1, e2]`. Express the relevant statement in the definitionally equal form `Polynomial.eval (y (Sum.inr i)) (Matrix.charpoly (Matrix.of fun a b => y (Sum.inl (a, b)))) = 0`. Rewrite using `[Matrix.eval_charpoly]`.

Conclude with `h1`.
-/
theorem SpecLie_of (hS : SpecPt) : SpecLie := by
  intro Γ K K' _ _ _ _ _ N n ρ X e hX hL hR
  classical
  let x : (Fin N × Fin N) ⊕ Fin n → K' := Sum.elim (fun p => X p.1 p.2) e
  let gAB : Finset (Fin n) → Finset (Fin n) → MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K := fun A B =>
    MvPolynomial.C (B.card : K) * ∑ i ∈ A, MvPolynomial.X (Sum.inr i) -
      MvPolynomial.C (A.card : K) * ∑ i ∈ B, MvPolynomial.X (Sum.inr i)
  let G : Set (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K) :=
    {g | ∃ A B : Finset (Fin n), A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ g = gAB A B}
  have hGf : G.Finite :=
    (Set.finite_range (fun AB : Finset (Fin n) × Finset (Fin n) => gAB AB.1 AB.2)).subset
      (by rintro g ⟨A, B, -, -, -, rfl⟩; exact ⟨(A, B), rfl⟩)
  have haG : ∀ g ∈ G, MvPolynomial.aeval x g ≠ 0 := by
    rintro g ⟨A, B, hA, hB, hAB, rfl⟩
    simp only [gAB, map_sub, map_mul, map_sum, MvPolynomial.aeval_X, x, Sum.elim_inr, map_natCast]
    exact sub_ne_zero.mpr (hL A B hA hB hAB)
  obtain ⟨y, hy, hyG⟩ := hS K K' _ x G hGf haG
  refine ⟨Matrix.of fun a b => y (Sum.inl (a, b)), fun i => y (Sum.inr i), ?_, ?_, ?_⟩
  · change ∀ f ∈ Van (img ρ ⊤ : Set (Mat K N)), dAt f 1 _ = 0
    intro f hf
    have hf' : ∀ g : Γ, MvPolynomial.eval (fun p : Fin N × Fin N => (ρ g : Matrix (Fin N) (Fin N) K) p.1 p.2) f = 0 :=
      fun g => hf _ ⟨g, trivial, rfl⟩
    have h0 := hX f hf'
    let L : MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K := ∑ p : Fin N × Fin N,
      MvPolynomial.C (MvPolynomial.eval (fun q : Fin N × Fin N => (1 : Matrix (Fin N) (Fin N) K) q.1 q.2)
        (MvPolynomial.pderiv p f)) * MvPolynomial.X (Sum.inl p)
    have hxL : MvPolynomial.aeval x L = 0 := by
      simpa only [L, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X, x, Sum.elim_inl] using h0
    have h1 := hy L hxL
    simpa only [L, dAt, ev, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.of_apply] using h1
  · intro A B hA hB hAB
    have h1 := hyG _ ⟨A, B, hA, hB, hAB, rfl⟩
    simp only [gAB, map_sub, map_mul, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X] at h1
    exact sub_ne_zero.mp h1
  · intro i
    let M : Matrix (Fin N) (Fin N) (MvPolynomial ((Fin N × Fin N) ⊕ Fin n) K) :=
      Matrix.scalar (Fin N) (MvPolynomial.X (Sum.inr i)) - Matrix.of (fun a b => MvPolynomial.X (Sum.inl (a, b)))
    have hx : MvPolynomial.aeval x M.det = 0 := by
      have e1 : MvPolynomial.aeval x M.det = ((MvPolynomial.aeval x).toRingHom.mapMatrix M).det := by
        rw [← RingHom.map_det]; rfl
      have e2 : (MvPolynomial.aeval x).toRingHom.mapMatrix M = Matrix.scalar (Fin N) (e i) - X := by
        ext a b
        by_cases h : a = b
        · subst h; simp [M, x]
        · simp [M, x, h]
      rw [e1, e2, ← Matrix.eval_charpoly]; exact hR i
    have h1 := hy _ hx
    have e1 : MvPolynomial.eval y M.det = ((MvPolynomial.eval y).mapMatrix M).det := by
      rw [← RingHom.map_det]
    have e2 : (MvPolynomial.eval y).mapMatrix M =
        Matrix.scalar (Fin N) (y (Sum.inr i)) - Matrix.of (fun a b => y (Sum.inl (a, b))) := by
      ext a b
      by_cases h : a = b
      · subst h; simp [M]
      · simp [M, h]
    rw [e1, e2] at h1
    change Polynomial.eval (y (Sum.inr i)) (Matrix.charpoly (Matrix.of fun a b => y (Sum.inl (a, b)))) = 0
    rw [Matrix.eval_charpoly]; exact h1

end LateralTheory.DivDb.SpecLiePf
