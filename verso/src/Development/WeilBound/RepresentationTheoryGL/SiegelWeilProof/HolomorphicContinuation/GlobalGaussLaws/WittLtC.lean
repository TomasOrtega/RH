import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.WittLtB

open Matrix NumberField GlobalTheory.Inertia
open scoped ComplexConjugate

noncomputable section

namespace PositivityTheory.Rg.Sw.Glob.WLt

open ReciprocityTheory.ChartRestriction.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def hyp : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

/- English proof (translation)
The claim follows from `map_one (IsCMField.complexConj E)`.
-/
theorem cc_one : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)

/- English proof (translation)
The claim follows from `map_zero (IsCMField.complexConj E)`.
-/
theorem cc_zero : FD.cc (0 : E) = 0 := map_zero (IsCMField.complexConj E)

/- English proof (translation)
The claim follows from `map_neg (IsCMField.complexConj E) t`.
-/
theorem cc_neg (t : E) : FD.cc (-t) = -FD.cc t := map_neg (IsCMField.complexConj E) t

/- English proof (translation)
Use `show IsCMField.complexConj E (t / 2) = _`. Rewrite using `[map_div₀, map_ofNat]`. Both sides reduce to the same expression.
-/
theorem cc_div_two (t : E) : FD.cc (t / 2) = FD.cc t / 2 := by
  show IsCMField.complexConj E (t / 2) = _
  rw [map_div₀, map_ofNat]
  rfl

/- English proof (translation)
Establish `hu : z ᵥ* G ≠ 0`. Introduce `h`. Apply `hz0` to reduce the goal to its premises. Establish `h1` using `congrArg (· ᵥ* G⁻¹) h`. Simplify using `only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at h1`.

Rewrite `h1` using `[Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det G).1 ((Matrix.isUnit_iff_isUnit_det G).2 hd.isUnit)), Matrix.vecMul_one]`. Then use the resulting hypothesis. Choose the witnesses or unpack the hypotheses as in `⟨b, hb⟩ : ∃ b, (z ᵥ* G) b ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hu (funext h)`.

Use `set c := (z ᵥ* G) b with hc`. Set `v : n → E` to `c⁻¹ • Pi.single b 1`. Set `w0 : n → E` to `FD.cc ∘ v`. Establish `hw0 : hf G z w0 = 1`. Establish `e1 : FD.cc ∘ w0 = v` using `by ext i; exact cc_cc (v i)`.

Simplify using `only [hf]`. Rewrite using `[e1, Matrix.dotProduct_mulVec]`. Simplify using `only [v, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]`. Conclude with `inv_mul_cancel₀ hb`. Use `set a := hf G w0 w0 with ha`.

Establish `haa : FD.cc a = a` using `by rw [ha, ← hf_symm hG]`. Use `⟨w0 + (-(a / 2)) • z, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hf_add_right, hf_smul_right, hz, hw0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hzw : hf G w0 z = 1` using `by rw [hf_symm hG, hw0, cc_one]`.

Rewrite using `[hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right, hf_smul_right, hz, hw0, hzw, cc_neg, cc_div_two, haa, ← ha]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_pair {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) {z : n → E} (hz0 : z ≠ 0) (hz : hf G z z = 0) :
    ∃ w : n → E, hf G z w = 1 ∧ hf G w w = 0 := by
  have hu : z ᵥ* G ≠ 0 := by
    intro h
    apply hz0
    have h1 := congrArg (· ᵥ* G⁻¹) h
    simp only [Matrix.vecMul_vecMul, Matrix.zero_vecMul] at h1
    rwa [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det G).1 ((Matrix.isUnit_iff_isUnit_det G).2 hd.isUnit)),
      Matrix.vecMul_one] at h1
  obtain ⟨b, hb⟩ : ∃ b, (z ᵥ* G) b ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  set c := (z ᵥ* G) b with hc
  let v : n → E := c⁻¹ • Pi.single b 1
  let w0 : n → E := FD.cc ∘ v
  have hw0 : hf G z w0 = 1 := by
    have e1 : FD.cc ∘ w0 = v := by ext i; exact cc_cc (v i)
    simp only [hf]
    rw [e1, Matrix.dotProduct_mulVec]
    simp only [v, dotProduct_smul, dotProduct_single, mul_one, smul_eq_mul]
    exact inv_mul_cancel₀ hb
  set a := hf G w0 w0 with ha
  have haa : FD.cc a = a := by rw [ha, ← hf_symm hG]
  refine ⟨w0 + (-(a / 2)) • z, ?_, ?_⟩
  · rw [hf_add_right, hf_smul_right, hz, hw0]; ring
  · have hzw : hf G w0 z = 1 := by rw [hf_symm hG, hw0, cc_one]
    rw [hf_add_left, hf_add_right, hf_add_right, hf_smul_left, hf_smul_left, hf_smul_right, hf_smul_right, hz, hw0, hzw,
      cc_neg, cc_div_two, haa, ← ha]
    ring

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨w, hzw, hww⟩` from `exists_pair hG hd hz0 hz`. Establish `hwz : hf G w z = 1` using `by rw [hf_symm hG, hzw, cc_one]`. Apply the tactic sequence `let L : (n → E) →ₗ[E] (Fin 2 → E) := { toFun := fun x => ![hf G x z, hf G x w] map_add' := fun x y => by ext i; fin_cases i <;> simp [hf_add_left] map_smul' := fun t x => by ext i; fin_cases i <;> simp [hf_smul_left] }`. Apply the tactic sequence `have hLz : L z = ![0, 1] := by ext i; fin_cases i <;> simp [L, hz, hzw]`. Apply the tactic sequence `have hLw : L w = ![1, 0] := by ext i; fin_cases i <;> simp [L, hwz, hww]`.

Establish `hLs : Function.Surjective L`. Introduce `v`. Use `⟨v 0 • w + v 1 • z, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, map_smul, hLz, hLw]`. Apply the tactic sequence `ext i; fin_cases i <;> simp`.

Use `set K := LinearMap.ker L`. Establish `hrk : Module.finrank E K + 2 = Fintype.card n` using `by show Module.finrank E (LinearMap.ker L) + 2 = _`. Establish `h` using `LinearMap.finrank_range_add_finrank_ker L`. Rewrite `h` using `[LinearMap.range_eq_top.mpr hLs, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card]`. Use linear arithmetic over natural numbers and integers.

Use `set m := Module.finrank E K`. Set `bK : Module.Basis (Fin m) E K` to `Module.finBasis E K`. Establish `hK : ∀ i, hf G (bK i : n → E) z = 0 ∧ hf G (bK i : n → E) w = 0`. Introduce `i`. Establish `h` using `(bK i).2`.

Rewrite `h` using `[LinearMap.mem_ker]`. Conclude with `⟨congrFun h 0, congrFun h 1⟩`. Set `cols : Fin 2 ⊕ Fin m → (n → E)` to `Sum.elim ![z, w] fun i => (bK i : n → E)`. Establish `hcard : Fintype.card (Fin 2 ⊕ Fin m) = Fintype.card n` using `by simp; omega`. Set `e : Fin 2 ⊕ Fin m ≃ n` to `Fintype.equivOfCardEq hcard`.

Set `G2 : Matrix (Fin m) (Fin m) E` to `fun i j => hf G (bK i : n → E) (bK j : n → E)`. Set `P : Matrix n n E` to `fun k j => cols (e.symm j) k`. Apply the tactic sequence `have hentry : ∀ s t, hf G (cols s) (cols t) = fromBlocks hyp 0 0 G2 s t := by`. Introduce and unpack `(i | i) (j | j)`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [cols, hyp, hz, hzw, hwz, hww]`.

Use `fin_cases i`. Simplify using `[cols]`. Rewrite using `[hf_symm hG (bK j : n → E) z, (hK j).1, cc_zero]`. Simplify using `[cols]`. Rewrite using `[hf_symm hG (bK j : n → E) w, (hK j).2, cc_zero]`.

Use `fin_cases j`. Simplify using `[cols, (hK i).1]`. Simplify using `[cols, (hK i).2]`. Both sides reduce to the same expression. Establish `hT : Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm`.

Use extensionality with `a b`. Rewrite using `[GlobalTheory.HermDiag.transpose_mul_mul_map_apply]`. Apply the tactic sequence `exact hentry (e.symm a) (e.symm b)`. Establish `hlin : ∀ (γ : Fin 2 ⊕ Fin m → E) (y : n → E), hf G (∑ s, γ s • cols s) y = ∑ s, γ s * hf G (cols s) y`. Introduce `γ y`.

Set `Ly : (n → E) →ₗ[E] E` to `{ toFun := fun x => hf G x y map_add' := fun x x' => hf_add_left G x x' y map_smul' := fun t x => hf_smul_left G t x y }`. Establish `h1 : hf G (∑ s, γ s • cols s) y = Ly (∑ s, γ s • cols s)` using `rfl`. Rewrite using `[h1, map_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul]`.

Both sides reduce to the same expression. Establish `hP : P.det ≠ 0`. Establish `hinj : Function.Injective P.mulVec`. Introduce `α β hαβ`. Establish `h0 : P *ᵥ (α - β) = 0` using `by rw [Matrix.mulVec_sub, hαβ, sub_self]`.

Use `set γ : n → E := α - β with hγ`. Establish `hsum : ∑ s, γ (e s) • cols s = 0`. Rewrite using `[← h0]`. Use extensionality with `k`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, P]`.

Rewrite using `[← e.sum_comp]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz1 : γ (e (Sum.inl 1)) = 0`.

Establish `h` using `hlin (fun s => γ (e s)) z`. Rewrite `h` using `[hsum]`. Establish `h' : ∑ s, γ (e s) * hf G (cols s) z = γ (e (Sum.inl 1))`. Apply the tactic sequence `have hc : ∀ s, hf G (cols s) z = fromBlocks hyp 0 0 G2 s (Sum.inl 0) := fun s => hentry s (Sum.inl 0)`. Simplify using `only [hc, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₂₁, hyp]`.

Simplify using the standard rewrite rules. Rewrite using `[← h', ← h]`. Simplify using `[hf]`. Establish `hw1 : γ (e (Sum.inl 0)) = 0`. Establish `h` using `hlin (fun s => γ (e s)) w`.

Rewrite `h` using `[hsum]`. Establish `h' : ∑ s, γ (e s) * hf G (cols s) w = γ (e (Sum.inl 0))`. Apply the tactic sequence `have hc : ∀ s, hf G (cols s) w = fromBlocks hyp 0 0 G2 s (Sum.inl 1) := fun s => hentry s (Sum.inl 1)`. Simplify using `only [hc, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₂₁, hyp]`. Simplify using the standard rewrite rules.

Rewrite using `[← h', ← h]`. Simplify using `[hf]`. Establish `hrest : ∑ i, γ (e (Sum.inr i)) • bK i = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Use `hsum` as an intermediate fact.

Simplify using `only [Fintype.sum_sum_type, Fin.sum_univ_two, hz1, hw1, zero_smul, zero_add] at this`. Simplify `this` using `[cols]`. Establish `hcoef` using `(Fintype.linearIndependent_iff.1 bK.linearIndependent) _ hrest`. Establish `hγ0 : γ = 0`. Use function extensionality and compare the values at `k`.

Take `⟨s, rfl⟩` from `e.surjective k`. Break down `s with i | i` into its components or cases. Use `fin_cases i`. Conclude with `hw1`. Conclude with `hz1`.

Conclude with `hcoef i`. Use `congrFun hγ0` as an intermediate fact. Use function extensionality and compare the values at `k`. Establish `hk` using `this k`. Simplify using `only [hγ, Pi.sub_apply, Pi.zero_apply] at hk`.

Conclude with `sub_eq_zero.mp hk`. Establish `hu : IsUnit P` using `Matrix.mulVec_injective_iff_isUnit.1 hinj`. Conclude with `((Matrix.isUnit_iff_isUnit_det P).1 hu).ne_zero`. Establish `hG2 : ∀ a b, FD.cc (G2 a b) = G2 b a` using `fun a b => (hf_symm hG _ _).symm`. Establish `hdetP : (P.map FD.cc).det ≠ 0`.

Establish `: (P.map FD.cc).det = IsCMField.complexConj E P.det` using `(RingHom.map_det (IsCMField.complexConj E : E →+* E) P).symm`. Rewrite using `[this]`. Conclude with `(map_ne_zero _).2 hP`. Establish `hdetT : ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).det ≠ 0`. Rewrite using `[← hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`.

Conclude with `mul_ne_zero (mul_ne_zero hP hd) hdetP`. Establish `hG2d : G2.det ≠ 0`. Rewrite `hdetT` using `[Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`. Introduce `h`. Rewrite `hdetT` using `[h, mul_zero]`.

Conclude with `hdetT rfl`. Conclude with `⟨m, e, G2, P, hP, hT, hG2, hG2d⟩`.
-/
theorem split {n : Type} [Fintype n] [DecidableEq n] {G : Matrix n n E} (hG : ∀ a b, FD.cc (G a b) = G b a)
    (hd : G.det ≠ 0) {z : n → E} (hz0 : z ≠ 0) (hz : hf G z z = 0) :
    ∃ (m : ℕ) (e : Fin 2 ⊕ Fin m ≃ n) (G2 : Matrix (Fin m) (Fin m) E) (P : Matrix n n E), P.det ≠ 0 ∧
      Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm ∧ (∀ a b, FD.cc (G2 a b) = G2 b a) ∧
        G2.det ≠ 0 := by
  obtain ⟨w, hzw, hww⟩ := exists_pair hG hd hz0 hz
  have hwz : hf G w z = 1 := by rw [hf_symm hG, hzw, cc_one]
  let L : (n → E) →ₗ[E] (Fin 2 → E) :=
    { toFun := fun x => ![hf G x z, hf G x w]
      map_add' := fun x y => by ext i; fin_cases i <;> simp [hf_add_left]
      map_smul' := fun t x => by ext i; fin_cases i <;> simp [hf_smul_left] }
  have hLz : L z = ![0, 1] := by ext i; fin_cases i <;> simp [L, hz, hzw]
  have hLw : L w = ![1, 0] := by ext i; fin_cases i <;> simp [L, hwz, hww]
  have hLs : Function.Surjective L := by
    intro v
    refine ⟨v 0 • w + v 1 • z, ?_⟩
    rw [map_add, map_smul, map_smul, hLz, hLw]
    ext i; fin_cases i <;> simp
  set K := LinearMap.ker L
  have hrk : Module.finrank E K + 2 = Fintype.card n := by
    show Module.finrank E (LinearMap.ker L) + 2 = _
    have h := LinearMap.finrank_range_add_finrank_ker L
    rw [LinearMap.range_eq_top.mpr hLs, finrank_top, Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card] at h
    omega
  set m := Module.finrank E K
  let bK : Module.Basis (Fin m) E K := Module.finBasis E K
  have hK : ∀ i, hf G (bK i : n → E) z = 0 ∧ hf G (bK i : n → E) w = 0 := by
    intro i
    have h := (bK i).2
    rw [LinearMap.mem_ker] at h
    exact ⟨congrFun h 0, congrFun h 1⟩
  let cols : Fin 2 ⊕ Fin m → (n → E) := Sum.elim ![z, w] fun i => (bK i : n → E)
  have hcard : Fintype.card (Fin 2 ⊕ Fin m) = Fintype.card n := by simp; omega
  let e : Fin 2 ⊕ Fin m ≃ n := Fintype.equivOfCardEq hcard
  let G2 : Matrix (Fin m) (Fin m) E := fun i j => hf G (bK i : n → E) (bK j : n → E)
  let P : Matrix n n E := fun k j => cols (e.symm j) k
  have hentry : ∀ s t, hf G (cols s) (cols t) = fromBlocks hyp 0 0 G2 s t := by
    rintro (i | i) (j | j)
    · fin_cases i <;> fin_cases j <;> simp [cols, hyp, hz, hzw, hwz, hww]
    · fin_cases i
      · simp [cols]
        rw [hf_symm hG (bK j : n → E) z, (hK j).1, cc_zero]
      · simp [cols]
        rw [hf_symm hG (bK j : n → E) w, (hK j).2, cc_zero]
    · fin_cases j
      · simp [cols, (hK i).1]
      · simp [cols, (hK i).2]
    · rfl
  have hT : Pᵀ * G * P.map FD.cc = (fromBlocks hyp 0 0 G2).submatrix e.symm e.symm := by
    ext a b
    rw [GlobalTheory.HermDiag.transpose_mul_mul_map_apply]
    exact hentry (e.symm a) (e.symm b)
  have hlin : ∀ (γ : Fin 2 ⊕ Fin m → E) (y : n → E),
      hf G (∑ s, γ s • cols s) y = ∑ s, γ s * hf G (cols s) y := by
    intro γ y
    let Ly : (n → E) →ₗ[E] E :=
      { toFun := fun x => hf G x y
        map_add' := fun x x' => hf_add_left G x x' y
        map_smul' := fun t x => hf_smul_left G t x y }
    have h1 : hf G (∑ s, γ s • cols s) y = Ly (∑ s, γ s • cols s) := rfl
    rw [h1, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  have hP : P.det ≠ 0 := by
    have hinj : Function.Injective P.mulVec := by
      intro α β hαβ
      have h0 : P *ᵥ (α - β) = 0 := by rw [Matrix.mulVec_sub, hαβ, sub_self]
      set γ : n → E := α - β with hγ
      have hsum : ∑ s, γ (e s) • cols s = 0 := by
        rw [← h0]
        ext k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, P]
        rw [← e.sum_comp]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [Equiv.symm_apply_apply]
        ring
      have hz1 : γ (e (Sum.inl 1)) = 0 := by
        have h := hlin (fun s => γ (e s)) z
        rw [hsum] at h
        have h' : ∑ s, γ (e s) * hf G (cols s) z = γ (e (Sum.inl 1)) := by
          have hc : ∀ s, hf G (cols s) z = fromBlocks hyp 0 0 G2 s (Sum.inl 0) := fun s => hentry s (Sum.inl 0)
          simp only [hc, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₂₁, hyp]
          simp
        rw [← h', ← h]
        simp [hf]
      have hw1 : γ (e (Sum.inl 0)) = 0 := by
        have h := hlin (fun s => γ (e s)) w
        rw [hsum] at h
        have h' : ∑ s, γ (e s) * hf G (cols s) w = γ (e (Sum.inl 0)) := by
          have hc : ∀ s, hf G (cols s) w = fromBlocks hyp 0 0 G2 s (Sum.inl 1) := fun s => hentry s (Sum.inl 1)
          simp only [hc, Fintype.sum_sum_type, Fin.sum_univ_two, fromBlocks_apply₁₁, fromBlocks_apply₂₁, hyp]
          simp
        rw [← h', ← h]
        simp [hf]
      have hrest : ∑ i, γ (e (Sum.inr i)) • bK i = 0 := by
        apply Subtype.ext
        have := hsum
        simp only [Fintype.sum_sum_type, Fin.sum_univ_two, hz1, hw1, zero_smul, zero_add] at this
        simpa [cols] using this
      have hcoef := (Fintype.linearIndependent_iff.1 bK.linearIndependent) _ hrest
      have hγ0 : γ = 0 := by
        funext k
        obtain ⟨s, rfl⟩ := e.surjective k
        rcases s with i | i
        · fin_cases i
          · exact hw1
          · exact hz1
        · exact hcoef i
      have := congrFun hγ0
      funext k
      have hk := this k
      simp only [hγ, Pi.sub_apply, Pi.zero_apply] at hk
      exact sub_eq_zero.mp hk
    have hu : IsUnit P := Matrix.mulVec_injective_iff_isUnit.1 hinj
    exact ((Matrix.isUnit_iff_isUnit_det P).1 hu).ne_zero
  have hG2 : ∀ a b, FD.cc (G2 a b) = G2 b a := fun a b => (hf_symm hG _ _).symm
  have hdetP : (P.map FD.cc).det ≠ 0 := by
    have : (P.map FD.cc).det = IsCMField.complexConj E P.det :=
      (RingHom.map_det (IsCMField.complexConj E : E →+* E) P).symm
    rw [this]
    exact (map_ne_zero _).2 hP
  have hdetT : ((fromBlocks hyp 0 0 G2).submatrix e.symm e.symm).det ≠ 0 := by
    rw [← hT, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hP hd) hdetP
  have hG2d : G2.det ≠ 0 := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁] at hdetT
    intro h
    rw [h, mul_zero] at hdetT
    exact hdetT rfl
  exact ⟨m, e, G2, P, hP, hT, hG2, hG2d⟩

end PositivityTheory.Rg.Sw.Glob.WLt

end
