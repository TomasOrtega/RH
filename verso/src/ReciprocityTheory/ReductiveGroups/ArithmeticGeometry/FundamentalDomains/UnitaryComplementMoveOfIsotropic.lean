import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowFixesComplementOfIsotropic

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

/- English proof (translation)
Simplify using `only [ppos, hC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `congr 1`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ppos_smul (x : Frame X.Ψ r) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.ppos x τ (c • v) = c • X.ppos x τ v := by
  simp only [ppos, hC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/- English proof (translation)
Use `ppos_smul X x τ 0 0` as an intermediate fact. Simplify using `using this`.
-/
lemma ppos_zero (x : Frame X.Ψ r) (τ : X.Ψ) : X.ppos x τ 0 = 0 := by
  have := ppos_smul X x τ 0 0
  simpa using this

/- English proof (translation)
Establish `hA` using `gramPos_det_ne X hx τ`. Establish `hsymm : ∀ v v', hermC τ.1 X.Gm v v' = conj (hermC τ.1 X.Gm v' v)` using `fun v v' => hC_symm τ.1 X.Gm X.Gm_herm v' v`. Establish `hspan : ∀ (y v : Fin r → ℂ), (∀ b : Fin X.p0, hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) → hermC τ.1 X.Gm (X.ppos x τ v) y = 0`. Introduce `y v hy`. Unfold `ppos`.

Rewrite using `[hC_sum_left]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Rewrite using `[hC_smul_left, hsymm, hy a, map_zero, mul_zero]`. Establish `h1 : hermC τ.1 X.Gm (X.ppos x τ u) (w - X.ppos x τ w) = 0` using `hspan (w - X.ppos x τ w) u (ppos_orth X x τ hA w)`. Establish `h2 : hermC τ.1 X.Gm (u - X.ppos x τ u) (X.ppos x τ w) = 0` using `hspan (u - X.ppos x τ u) w (ppos_orth X x τ hA u) |> fun h => by rw [hsymm, h, map_zero]`.

Establish `e1 : hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w)`. Establish `: w = X.ppos x τ w + (w - X.ppos x τ w)` using `by abel`. Use `conv_lhs => rw [this]`. Rewrite using `[hC_add_right, h1, add_zero]`. Establish `e2 : hermC τ.1 X.Gm u (X.ppos x τ w) = hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w)`.

Establish `: u = X.ppos x τ u + (u - X.ppos x τ u)` using `by abel`. Use `conv_lhs => rw [this]`. Rewrite using `[hC_add_left, h2, add_zero]`. Rewrite using `[e1, e2]`.
-/
lemma ppos_selfadj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hA := gramPos_det_ne X hx τ
  have hsymm : ∀ v v', hermC τ.1 X.Gm v v' = conj (hermC τ.1 X.Gm v' v) := fun v v' =>
    hC_symm τ.1 X.Gm X.Gm_herm v' v

  have hspan : ∀ (y v : Fin r → ℂ), (∀ b : Fin X.p0, hermC τ.1 X.Gm y (col (mat x τ) (Fin.castLE X.p0_le b)) = 0) →
      hermC τ.1 X.Gm (X.ppos x τ v) y = 0 := by
    intro y v hy
    unfold ppos
    rw [hC_sum_left]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [hC_smul_left, hsymm, hy a, map_zero, mul_zero]
  have h1 : hermC τ.1 X.Gm (X.ppos x τ u) (w - X.ppos x τ w) = 0 :=
    hspan (w - X.ppos x τ w) u (ppos_orth X x τ hA w)
  have h2 : hermC τ.1 X.Gm (u - X.ppos x τ u) (X.ppos x τ w) = 0 :=
    hspan (u - X.ppos x τ u) w (ppos_orth X x τ hA u) |> fun h => by rw [hsymm, h, map_zero]
  have e1 : hermC τ.1 X.Gm (X.ppos x τ u) w =
      hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w) := by
    have : w = X.ppos x τ w + (w - X.ppos x τ w) := by abel
    conv_lhs => rw [this]
    rw [hC_add_right, h1, add_zero]
  have e2 : hermC τ.1 X.Gm u (X.ppos x τ w) =
      hermC τ.1 X.Gm (X.ppos x τ u) (X.ppos x τ w) := by
    have : u = X.ppos x τ u + (u - X.ppos x τ u) := by abel
    conv_lhs => rw [this]
    rw [hC_add_left, h2, add_zero]
  rw [e1, e2]

/- English proof (translation)
Establish `hneg : hermC τ.1 X.Gm u (-w) = - hermC τ.1 X.Gm u w`. Use `hC_smul_right τ.1 X.Gm (-1) u w` as an intermediate fact. Simplify using `using this`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Hf]`.

Rewrite using `[hC_sub_left, hC_smul_left, ppos_selfadj X hx]`. Use `_ = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by`. Rewrite using `[sub_eq_add_neg ((2 : ℂ) • X.ppos x τ w) w, hC_add_right, hC_smul_right, hneg, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma Hf_eq (x : Frame X.Ψ r) (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ u w = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by
  have hneg : hermC τ.1 X.Gm u (-w) = - hermC τ.1 X.Gm u w := by
    have := hC_smul_right τ.1 X.Gm (-1) u w
    simpa using this
  calc X.Hf x τ u w = 2 * hermC τ.1 X.Gm u (X.ppos x τ w) - hermC τ.1 X.Gm u w := by
        simp only [Hf]; rw [hC_sub_left, hC_smul_left, ppos_selfadj X hx]
    _ = hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ w - w) := by
        rw [sub_eq_add_neg ((2 : ℂ) • X.ppos x τ w) w, hC_add_right, hC_smul_right, hneg, map_ofNat]
        ring

section unitary

variable (x : Frame X.Ψ r) (τ : X.Ψ) (g : Matrix (Fin r) (Fin r) ℂ)
  (hg : ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g w) = hermC τ.1 X.Gm u w)

include hg

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gram, Matrix.of_apply, col_mul, hg]`.
-/
lemma gram_unitary : gram τ.1 X.Gm (g * mat x τ) = gram τ.1 X.Gm (mat x τ) := by
  ext a b
  simp only [gram, Matrix.of_apply, col_mul, hg]

/- English proof (translation)
Establish `hcol : ∀ a, col (mat (X.lmulC (fun _ => g) x) τ) a = Matrix.mulVec g (col (mat x τ) a)`. Introduce `a`. Conclude with `col_mul g (mat x τ) a`. Establish `hgram : X.gramPos (X.lmulC (fun _ => g) x) τ = X.gramPos x τ`. Simplify using `only [gramPos]`.

Rewrite using `[show mat (X.lmulC (fun _ => g) x) τ = g * mat x τ from rfl, gram_unitary X x τ g hg]`. Use `set α : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)) * (X.gramPos x τ)⁻¹ b a`. Establish `hpx : X.ppos x τ v = ∑ a, α a • col (mat x τ) (Fin.castLE X.p0_le a)` using `rfl`. Establish `hsum : Matrix.mulVec g (X.ppos x τ v) = ∑ a, α a • col (mat (X.lmulC (fun _ => g) x) τ) (Fin.castLE X.p0_le a)`. Rewrite using `[hpx, mulVec_lin]`.

Simplify using `only [hcol]`. Rewrite using `[hsum]`. Apply `ppos_eq_of X _ τ (by rw [hgram]; exact gramPos_det_ne X hx τ)` to reduce the goal to its premises. Introduce `b`. Rewrite using `[← hsum, hcol, ← Matrix.mulVec_sub, hg]`.

Conclude with `ppos_orth X x τ (gramPos_det_ne X hx τ) v b`.
-/
lemma ppos_unitary (hx : x ∈ X.dom) (v : Fin r → ℂ) :
    X.ppos (X.lmulC (fun _ => g) x) τ (Matrix.mulVec g v) = Matrix.mulVec g (X.ppos x τ v) := by
  have hcol : ∀ a, col (mat (X.lmulC (fun _ => g) x) τ) a = Matrix.mulVec g (col (mat x τ) a) := by
    intro a; exact col_mul g (mat x τ) a
  have hgram : X.gramPos (X.lmulC (fun _ => g) x) τ = X.gramPos x τ := by
    simp only [gramPos]
    rw [show mat (X.lmulC (fun _ => g) x) τ = g * mat x τ from rfl, gram_unitary X x τ g hg]
  set α : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos x τ)⁻¹ b a
  have hpx : X.ppos x τ v = ∑ a, α a • col (mat x τ) (Fin.castLE X.p0_le a) := rfl
  have hsum : Matrix.mulVec g (X.ppos x τ v) =
      ∑ a, α a • col (mat (X.lmulC (fun _ => g) x) τ) (Fin.castLE X.p0_le a) := by
    rw [hpx, mulVec_lin]; simp only [hcol]
  rw [hsum]
  apply ppos_eq_of X _ τ (by rw [hgram]; exact gramPos_det_ne X hx τ)
  intro b
  rw [← hsum, hcol, ← Matrix.mulVec_sub, hg]
  exact ppos_orth X x τ (gramPos_det_ne X hx τ) v b

end unitary

/- English proof (translation)
Introduce `r X ξ hξ x hx h1 hu hfix _hU`. Establish `hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0` using `fun τ => by`. Rewrite using `[← emb_herm, hξ.2.1, map_zero]`. Use `set x' := X.lmulC h1 x with hx'`. Establish `hloc : ∀ τ : X.Ψ, X.lmulC h1 x = X.lmulC (fun _ => h1 τ) x ∨ True` using `fun _ => Or.inr trivial`.

Establish `hmat : ∀ τ, mat x' τ = h1 τ * mat x τ` using `fun τ => rfl`. Establish `hgramτ : ∀ τ, gram τ.1 X.Gm (mat x' τ) = gram τ.1 X.Gm (mat x τ)` using `fun τ => by`. Rewrite using `[hmat]`. Conclude with `gram_unitary X x τ (h1 τ) (hu τ)`. Establish `hfe : ∀ τ, Matrix.mulVec (h1 τ) (emb τ.1 ξ) = emb τ.1 ξ`.

Introduce `τ`. Establish `h` using `congrFun (hfix (fun _ => 1) (fun _ => 0)) τ`. Simplify using `only [applyV, lineV, Jz, Pi.add_apply, one_smul, zero_smul, ppos_zero, smul_zero, sub_zero, add_zero] at h`. Conclude with `h`. Establish `hfJ : ∀ τ, Matrix.mulVec (h1 τ) ((2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ) = (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ`.

Introduce `τ`. Establish `h` using `congrFun (hfix (fun _ => 0) (fun _ => -I)) τ`. Simplify using `only [applyV, lineV, Jz, Pi.add_apply, zero_smul, zero_add, ppos_smul, smul_smul] at h`. Establish `e1 : I • (((2 : ℂ) * -I) • X.ppos x τ (emb τ.1 ξ) - -I • emb τ.1 ξ) = (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ`. Rewrite using `[smul_sub, smul_smul, smul_smul, show I * (2 * -I) = (2 : ℂ) by`.

Take the linear combination `(-2 : ℂ) * Complex.I_mul_I, show I * -I = (1 : ℂ) by`. Take the linear combination `(-1 : ℂ) * Complex.I_mul_I, one_smul]`. Rewrite `h` using `[e1]`. Conclude with `h`. Establish `hdom : x' ∈ X.dom`.

Introduce `τ`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hmat, Matrix.det_mul]`. Use `mul_ne_zero ?_ (hx τ).1` and prove the remaining obligations. Introduce `h0`.

Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr h0`. Apply `hv0` to reduce the goal to its premises. Establish `hrad : ∀ w, hermC τ.1 X.Gm v w = 0` using `fun w => by rw [← hu τ v w, hv]; simp [hermC]`. Establish `hG : (Matrix.map X.Gm τ.1).det ≠ 0`. Establish `h` using `RingHom.map_det τ.1 X.Gm`.

Rewrite `h` using `[show τ.1.mapMatrix X.Gm = X.Gm.map τ.1 from rfl]`. Rewrite using `[← h]`. Conclude with `(map_ne_zero _).mpr X.Gm_det`. Assume the negation of the conclusion as `hne`. Apply `hG` to reduce the goal to its premises.

Apply `Matrix.exists_vecMul_eq_zero_iff.mp` to reduce the goal to its premises. Use `⟨v, hne, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `b`. Use `hrad (Pi.single b 1)` as an intermediate fact. Simplify `this` using `[hermC, Matrix.vecMul, dotProduct, Pi.single_apply, Matrix.map_apply]`.

Establish `: dmin X.Gm x' τ i = dmin X.Gm x τ i`. Simplify using `only [dmin]`. Rewrite using `[hgramτ]`. Rewrite using `[this]`. Conclude with `(hx τ).2 i`.

Use `⟨hdom, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u _`. Use function extensionality and compare the values at `τ`. Establish `hJe : (2 : ℂ) • X.ppos x' τ (emb τ.1 ξ) - emb τ.1 ξ = (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ`. Establish `hp` using `ppos_unitary X x τ (h1 τ) (hu τ) hx (emb τ.1 ξ)`.

Rewrite `hp` using `[hfe τ]`. Rewrite using `[show X.ppos x' τ (emb τ.1 ξ) = X.ppos (X.lmulC (fun _ => h1 τ) x) τ (emb τ.1 ξ) from rfl, hp]`. Rewrite using `[← Matrix.mulVec_smul, ← hfe τ, ← Matrix.mulVec_sub, hfe τ, hfJ τ]`. Simplify using `only [aproj, lineV]`. Rewrite using `[Hf_eq X x' hdom, Hf_eq X x' hdom, Hf_eq X x hx, Hf_eq X x hx, hJe]`.

Introduce `τ`. Establish `hpp : X.posPart x' τ (emb τ.1 ξ) = X.posPart x τ (emb τ.1 ξ)`. Establish `hgp : X.gramPos x' τ = X.gramPos x τ` using `by simp only [gramPos]; rw [hgramτ]`. Simplify using `only [posPart]`. Rewrite using `[hgp]`.

Establish `hc : ∀ a : Fin X.p0, hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x' τ) (Fin.castLE X.p0_le a)) = hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x τ) (Fin.castLE X.p0_le a))`. Introduce `a`. Rewrite using `[hmat, col_mul]`. Use `conv_lhs => rw [← hfe τ]`. Rewrite using `[hu τ]`.

Simplify using `only [hc]`. Simplify using `only [maj, hpp]`. Introduce `u _`. Use function extensionality and compare the values at `τ`. Simplify using `only [Jz, applyV]`.

Establish `hp` using `ppos_unitary X x τ (h1 τ) (hu τ) hx (u τ)`. Rewrite using `[show X.ppos x' τ (Matrix.mulVec (h1 τ) (u τ)) = X.ppos (X.lmulC (fun _ => h1 τ) x) τ (Matrix.mulVec (h1 τ) (u τ)) from rfl, hp]`. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul]`.
-/
theorem unitaryComplementMove_of_isotropic : UnitaryComplementMove (E := E) := by
  intro r X ξ hξ x hx h1 hu hfix _hU
  have hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0 := fun τ => by
    rw [← emb_herm, hξ.2.1, map_zero]
  set x' := X.lmulC h1 x with hx'
  have hloc : ∀ τ : X.Ψ, X.lmulC h1 x = X.lmulC (fun _ => h1 τ) x ∨ True := fun _ => Or.inr trivial

  have hmat : ∀ τ, mat x' τ = h1 τ * mat x τ := fun τ => rfl
  have hgramτ : ∀ τ, gram τ.1 X.Gm (mat x' τ) = gram τ.1 X.Gm (mat x τ) := fun τ => by
    rw [hmat]; exact gram_unitary X x τ (h1 τ) (hu τ)

  have hfe : ∀ τ, Matrix.mulVec (h1 τ) (emb τ.1 ξ) = emb τ.1 ξ := by
    intro τ
    have h := congrFun (hfix (fun _ => 1) (fun _ => 0)) τ
    simp only [applyV, lineV, Jz, Pi.add_apply, one_smul, zero_smul, ppos_zero, smul_zero,
      sub_zero, add_zero] at h
    exact h
  have hfJ : ∀ τ, Matrix.mulVec (h1 τ) ((2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ) =
      (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
    intro τ
    have h := congrFun (hfix (fun _ => 0) (fun _ => -I)) τ
    simp only [applyV, lineV, Jz, Pi.add_apply, zero_smul, zero_add, ppos_smul, smul_smul] at h
    have e1 : I • (((2 : ℂ) * -I) • X.ppos x τ (emb τ.1 ξ) - -I • emb τ.1 ξ) =
        (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
      rw [smul_sub, smul_smul, smul_smul, show I * (2 * -I) = (2 : ℂ) by
        linear_combination (-2 : ℂ) * Complex.I_mul_I, show I * -I = (1 : ℂ) by
        linear_combination (-1 : ℂ) * Complex.I_mul_I, one_smul]
    rw [e1] at h
    exact h

  have hdom : x' ∈ X.dom := by
    intro τ
    refine ⟨?_, fun i => ?_⟩
    · rw [hmat, Matrix.det_mul]
      refine mul_ne_zero ?_ (hx τ).1
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0

      have hrad : ∀ w, hermC τ.1 X.Gm v w = 0 := fun w => by rw [← hu τ v w, hv]; simp [hermC]
      have hG : (Matrix.map X.Gm τ.1).det ≠ 0 := by
        have h := RingHom.map_det τ.1 X.Gm
        rw [show τ.1.mapMatrix X.Gm = X.Gm.map τ.1 from rfl] at h
        rw [← h]; exact (map_ne_zero _).mpr X.Gm_det
      by_contra hne
      apply hG
      apply Matrix.exists_vecMul_eq_zero_iff.mp
      refine ⟨v, hne, ?_⟩
      funext b
      have := hrad (Pi.single b 1)
      simpa [hermC, Matrix.vecMul, dotProduct, Pi.single_apply, Matrix.map_apply] using this
    · have : dmin X.Gm x' τ i = dmin X.Gm x τ i := by
        simp only [dmin]; rw [hgramτ]
      rw [this]; exact (hx τ).2 i
  refine ⟨hdom, ?_, ?_, ?_⟩
  ·
    intro u _
    funext τ
    have hJe : (2 : ℂ) • X.ppos x' τ (emb τ.1 ξ) - emb τ.1 ξ =
        (2 : ℂ) • X.ppos x τ (emb τ.1 ξ) - emb τ.1 ξ := by
      have hp := ppos_unitary X x τ (h1 τ) (hu τ) hx (emb τ.1 ξ)
      rw [hfe τ] at hp
      rw [show X.ppos x' τ (emb τ.1 ξ) = X.ppos (X.lmulC (fun _ => h1 τ) x) τ (emb τ.1 ξ) from rfl, hp]
      rw [← Matrix.mulVec_smul, ← hfe τ, ← Matrix.mulVec_sub, hfe τ, hfJ τ]
    simp only [aproj, lineV]
    rw [Hf_eq X x' hdom, Hf_eq X x' hdom, Hf_eq X x hx, Hf_eq X x hx, hJe]
  · intro τ

    have hpp : X.posPart x' τ (emb τ.1 ξ) = X.posPart x τ (emb τ.1 ξ) := by
      have hgp : X.gramPos x' τ = X.gramPos x τ := by simp only [gramPos]; rw [hgramτ]
      simp only [posPart]
      rw [hgp]
      have hc : ∀ a : Fin X.p0, hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x' τ) (Fin.castLE X.p0_le a)) =
          hermC τ.1 X.Gm (emb τ.1 ξ) (col (mat x τ) (Fin.castLE X.p0_le a)) := by
        intro a
        rw [hmat, col_mul]
        conv_lhs => rw [← hfe τ]
        rw [hu τ]
      simp only [hc]
    simp only [maj, hpp]
  · intro u _
    funext τ
    simp only [Jz, applyV]
    have hp := ppos_unitary X x τ (h1 τ) (hu τ) hx (u τ)
    rw [show X.ppos x' τ (Matrix.mulVec (h1 τ) (u τ)) =
      X.ppos (X.lmulC (fun _ => h1 τ) x) τ (Matrix.mulVec (h1 τ) (u τ)) from rfl, hp]
    rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul]

end Data

/- English proof (translation)
The claim follows from `Data.unitaryComplementMove_of_isotropic`.
-/
theorem unitaryComplementMove : UnitaryComplementMove (E := E) := Data.unitaryComplementMove_of_isotropic

end ReciprocityTheory.ChartRestriction.G.FD
