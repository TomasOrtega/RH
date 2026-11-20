import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLtA

open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev hf {n : Type} [Fintype n] (G : Matrix n n E) (x y : n → E) : E := x ⬝ᵥ G *ᵥ (FD.cc ∘ y)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[mulVec, dotProduct, FD.cc, map_sum, map_mul]`.
-/
theorem cc_mulVec {n m : Type} [Fintype n] [Fintype m] (P : Matrix n m E) (y : m → E) :
    FD.cc ∘ (P *ᵥ y) = P.map FD.cc *ᵥ (FD.cc ∘ y) := by
  funext i
  simp [mulVec, dotProduct, FD.cc, map_sum, map_mul]

/- English proof (translation)
Simplify using `only [hf]`. Rewrite using `[cc_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]`.
-/
theorem hf_congr {n m : Type} [Fintype n] [Fintype m] (G : Matrix n n E) (P : Matrix n m E) (x y : m → E) :
    hf (Pᵀ * G * P.map FD.cc) x y = hf G (P *ᵥ x) (P *ᵥ y) := by
  simp only [hf]
  rw [cc_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

/- English proof (translation)
Simplify using `only [hf, submatrix_mulVec_equiv, Function.comp_def, Equiv.symm_symm]`. Rewrite using `[dotProduct, dotProduct, ← Equiv.sum_comp e (fun i => x (e.symm i) * _)]`. Simplify using the standard rewrite rules.
-/
theorem hf_submatrix {n m : Type} [Fintype n] [Fintype m] (G : Matrix n n E) (e : m ≃ n) (x y : m → E) :
    hf (G.submatrix e e) x y = hf G (x ∘ e.symm) (y ∘ e.symm) := by
  simp only [hf, submatrix_mulVec_equiv, Function.comp_def, Equiv.symm_symm]
  rw [dotProduct, dotProduct, ← Equiv.sum_comp e (fun i => x (e.symm i) * _)]
  simp

/- English proof (translation)
Establish `hc : ∀ s : Finset n, ∀ f : n → E, FD.cc (∑ i ∈ s, f i) = ∑ i ∈ s, FD.cc (f i)` using `fun s f => map_sum (IsCMField.complexConj E) f s`. Establish `hm : ∀ a b : E, FD.cc (a * b) = FD.cc a * FD.cc b` using `fun a b => map_mul (IsCMField.complexConj E) a b`. Simplify using `only [hf, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, hc, hm, cc_cc, hG]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hf_symm {n : Type} [Fintype n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a) (x y : n → E) :
    hf G y x = FD.cc (hf G x y) := by
  have hc : ∀ s : Finset n, ∀ f : n → E, FD.cc (∑ i ∈ s, f i) = ∑ i ∈ s, FD.cc (f i) :=
    fun s f => map_sum (IsCMField.complexConj E) f s
  have hm : ∀ a b : E, FD.cc (a * b) = FD.cc a * FD.cc b := fun a b => map_mul (IsCMField.complexConj E) a b
  simp only [hf, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, hc, hm, cc_cc, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `[hf, add_dotProduct]`.
-/
theorem hf_add_left {n : Type} [Fintype n] (G : Matrix n n E) (x x' y : n → E) :
    hf G (x + x') y = hf G x y + hf G x' y := by simp [hf, add_dotProduct]

/- English proof (translation)
Simplify using `[hf, smul_dotProduct]`.
-/
theorem hf_smul_left {n : Type} [Fintype n] (G : Matrix n n E) (a : E) (x y : n → E) :
    hf G (a • x) y = a * hf G x y := by simp [hf, smul_dotProduct]

/- English proof (translation)
Establish `h : FD.cc ∘ (y + y') = FD.cc ∘ y + FD.cc ∘ y'`. Use function extensionality and compare the values at `fun i => map_add (IsCMField.complexConj E) (y i) (y' i)`. Simplify using `only [hf, h, mulVec_add, dotProduct_add]`.
-/
theorem hf_add_right {n : Type} [Fintype n] (G : Matrix n n E) (x y y' : n → E) :
    hf G x (y + y') = hf G x y + hf G x y' := by
  have h : FD.cc ∘ (y + y') = FD.cc ∘ y + FD.cc ∘ y' :=
    funext fun i => map_add (IsCMField.complexConj E) (y i) (y' i)
  simp only [hf, h, mulVec_add, dotProduct_add]

/- English proof (translation)
Establish `h : FD.cc ∘ (a • y) = FD.cc a • (FD.cc ∘ y)`. Use function extensionality and compare the values at `fun i => map_mul (IsCMField.complexConj E) a (y i)`. Simplify using `only [hf, h, mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem hf_smul_right {n : Type} [Fintype n] (G : Matrix n n E) (a : E) (x y : n → E) :
    hf G x (a • y) = FD.cc a * hf G x y := by
  have h : FD.cc ∘ (a • y) = FD.cc a • (FD.cc ∘ y) :=
    funext fun i => map_mul (IsCMField.complexConj E) a (y i)
  simp only [hf, h, mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Take `⟨P, d, hP, hPd, hdr, hd0⟩` from `GlobalTheory.HermDiag.exists_congr_diagonal_herm hG`. Take `⟨r, rfl⟩ : ∃ r, m = r + 1` from `⟨m - 1, by omega⟩`. Establish `hsig : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (d i)).re) ∧ ∃ j, (τ (d j)).re < 0`. Introduce `τ`. Take `⟨h1, h2⟩` from `hs τ`.

Rewrite `h1` using `[posIndex_map_eq_card_of_congr_diagonal τ hP hPd]`. Establish `hPd' : Pᵀ * (-G) * P.map FD.cc = diagonal (-d)`. Rewrite using `[Matrix.mul_neg, Matrix.neg_mul, hPd, diagonal_neg]`. Both sides reduce to the same expression. Establish `hneg : (-G).map τ = -(G.map τ)`.

Use extensionality with `i j`. Simplify using the standard rewrite rules. Establish `h2' : 1 ≤ posIndex ((-G).map τ)`. Rewrite using `[hneg, posIndex_neg]` and apply the resulting hypothesis. Rewrite `h2'` using `[posIndex_map_eq_card_of_congr_diagonal τ hP hPd']`.

Take `⟨i, hi⟩` from `Finset.card_pos.mp h1`. Take `⟨j, hj⟩` from `Finset.card_pos.mp h2'`. Use `⟨⟨i, by simpa using hi⟩, ⟨j, ?_⟩⟩` and prove the remaining obligations. Simplify using `using hj`. Take `⟨z, hz, hz0⟩` from `iso_diag d (by omega) hdr (hd0 hd) hsig`.

Use `⟨P *ᵥ z, fun h => hz (eq_zero_of_mulVec_eq_zero hP h), ?_⟩` and prove the remaining obligations. Rewrite using `[← hf_congr, hPd]`. Conclude with `hz0`.
-/
private theorem exists_isotropic_of_three_le_of_indefinite {m : ℕ} (G : Matrix (Fin m) (Fin m) E) (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) (h3 : 3 ≤ m)
    (hs : ∀ τ : E →+* ℂ, 1 ≤ posIndex (G.map τ) ∧ 1 ≤ negIndex (G.map τ)) :
    ∃ z : Fin m → E, z ≠ 0 ∧ hf G z z = 0 := by
  obtain ⟨P, d, hP, hPd, hdr, hd0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal_herm hG
  obtain ⟨r, rfl⟩ : ∃ r, m = r + 1 := ⟨m - 1, by omega⟩
  have hsig : ∀ τ : E →+* ℂ, (∃ i, 0 < (τ (d i)).re) ∧ ∃ j, (τ (d j)).re < 0 := by
    intro τ
    obtain ⟨h1, h2⟩ := hs τ
    rw [posIndex_map_eq_card_of_congr_diagonal τ hP hPd] at h1
    have hPd' : Pᵀ * (-G) * P.map FD.cc = diagonal (-d) := by
      rw [Matrix.mul_neg, Matrix.neg_mul, hPd, diagonal_neg]
      rfl
    have hneg : (-G).map τ = -(G.map τ) := by
      ext i j
      simp
    have h2' : 1 ≤ posIndex ((-G).map τ) := by
      rwa [hneg, posIndex_neg]
    rw [posIndex_map_eq_card_of_congr_diagonal τ hP hPd'] at h2'
    obtain ⟨i, hi⟩ := Finset.card_pos.mp h1
    obtain ⟨j, hj⟩ := Finset.card_pos.mp h2'
    refine ⟨⟨i, by simpa using hi⟩, ⟨j, ?_⟩⟩
    simpa using hj
  obtain ⟨z, hz, hz0⟩ := iso_diag d (by omega) hdr (hd0 hd) hsig
  refine ⟨P *ᵥ z, fun h => hz (eq_zero_of_mulVec_eq_zero hP h), ?_⟩
  rw [← hf_congr, hPd]
  exact hz0

/- English proof (translation)
Take `⟨e⟩ : Nonempty (Fin (Fintype.card n) ≃ n)` from `⟨(Fintype.equivFin n).symm⟩`. Take `⟨z, hz, hz0⟩` from `exists_isotropic_of_three_le_of_indefinite (G.submatrix e e) (fun a b => hG _ _) (by rwa [det_submatrix_equiv_self]) h3 (fun τ => by rw [← submatrix_map, posIndex_submatrix_equiv, negIndex_submatrix_equiv]; exact hs τ)`. Use `⟨z ∘ e.symm, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hz` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Simplify using `using congrFun h (e i)`. Rewrite using `[← hf_submatrix]`. Conclude with `hz0`.
-/
theorem iso_gen {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n E) (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) (h3 : 3 ≤ Fintype.card n)
    (hs : ∀ τ : E →+* ℂ, 1 ≤ posIndex (G.map τ) ∧ 1 ≤ negIndex (G.map τ)) :
    ∃ z : n → E, z ≠ 0 ∧ hf G z z = 0 := by
  obtain ⟨e⟩ : Nonempty (Fin (Fintype.card n) ≃ n) := ⟨(Fintype.equivFin n).symm⟩
  obtain ⟨z, hz, hz0⟩ := exists_isotropic_of_three_le_of_indefinite (G.submatrix e e) (fun a b => hG _ _)
    (by rwa [det_submatrix_equiv_self]) h3
    (fun τ => by rw [← submatrix_map, posIndex_submatrix_equiv, negIndex_submatrix_equiv]; exact hs τ)
  refine ⟨z ∘ e.symm, ?_, ?_⟩
  · intro h
    apply hz
    funext i
    simpa using congrFun h (e i)
  · rw [← hf_submatrix]
    exact hz0

end PositivityTheory.Rg.Sw.Glob.WLt

end
