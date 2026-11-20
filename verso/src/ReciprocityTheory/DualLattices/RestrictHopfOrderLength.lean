import ReciprocityTheory.DualLattices.RestrictedHopfOrderApproximationStatement
import ReciprocityTheory.DualLattices.MemAugIdeal
import ReciprocityTheory.DualLattices.ExistsMatOfEquiv

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up.PullbackHopfOrder

/- English proof (translation)
Use `⟨fun i => ((n i).val : ℤ_[p]), funext fun i => ?_⟩` and prove the remaining obligations. Simplify using `[red]`.
-/
private theorem red_surj {p : ℕ} [Fact p.Prime] {g : ℕ} (n : Nb p g) : ∃ t, red p g t = n := by
  refine ⟨fun i => ((n i).val : ℤ_[p]), funext fun i => ?_⟩
  simp [red]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[red, Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
private theorem red_mulVec {p : ℕ} [Fact p.Prime] {g : ℕ} (M : Matrix (Ix g) (Ix g) ℤ_[p])
    (t : TT p g) : red p g (M *ᵥ t) = M.map PadicInt.toZMod *ᵥ red p g t := by
  funext i
  simp [red, Matrix.mulVec, dotProduct, map_sum, map_mul]

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H a ha r Bw hrange hkerB d hd`. Establish `hE : H.ρ a * H.ρ a = H.ρ a` using `by rw [← map_mul, ha]`. Establish `hcol : ∀ j : Ix g, ∃ k : Fin r → ℤ_[p], Bw *ᵥ k = H.ρ a *ᵥ Pi.single j 1`. Introduce `j`. Establish `hm : H.ρ a *ᵥ Pi.single j 1 ∈ LinearMap.range (Matrix.mulVecLin Bw)`.

Rewrite using `[hrange]`. Conclude with `⟨Pi.single j 1, rfl⟩`. Take `⟨k, hk⟩` from `hm`. Conclude with `⟨k, hk⟩`. Use `choose kk hkk using hcol`.

Set `K : Matrix (Fin r) (Ix g) ℤ_[p]` to `Matrix.of fun i j => kk j i`. Establish `hBK : Bw * K = H.ρ a`. Use extensionality with `i j`. Establish `h1 : (Bw * K) i j = (Bw *ᵥ kk j) i`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct, K]`.

Rewrite using `[h1, hkk j]`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Establish `hKB : K * Bw = 1`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]`. Apply `LinearMap.ker_eq_bot.mp hkerB` to reduce the goal to its premises. Use `show Bw *ᵥ ((K * Bw) *ᵥ x) = Bw *ᵥ x`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin (H.ρ a)) := by`. Rewrite using `[← hrange]`.

Conclude with `⟨x, rfl⟩`. Rewrite using `[← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBK, ← hy]`. Use `show H.ρ a *ᵥ (H.ρ a *ᵥ y) = H.ρ a *ᵥ y`. Rewrite using `[Matrix.mulVec_mulVec, hE]`. Set `ψ` to `psiW Bw`.

Set `χ : Nb p g →+ (Fin r → ZMod p)` to `(Matrix.mulVecLin (K.map PadicInt.toZMod)).toAddMonoidHom`. Establish `hχψ : ∀ x, χ (ψ x) = x`. Introduce `x`. Use `show K.map PadicInt.toZMod *ᵥ (Bw.map PadicInt.toZMod *ᵥ x) = x`. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, hKB, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]`.

Establish `hred : ∀ t, ψ (χ (red p g t)) = red p g (H.ρ a *ᵥ t)`. Introduce `t`. Use `show Bw.map PadicInt.toZMod *ᵥ (K.map PadicInt.toZMod *ᵥ red p g t) = _`. Rewrite using `[Matrix.mulVec_mulVec, ← Matrix.map_mul, hBK, ← red_mulVec]`. Establish `hA : ∀ f ∈ H.AA.carrier, (fun n => f (ψ (χ n))) ∈ H.AA.carrier`.

Introduce `f hf`. Take `⟨f', hf', hff⟩` from `H.h3 a f hf`. Use `hf' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `n`. Take `⟨t, rfl⟩` from `red_surj n`.

Rewrite using `[hff, hred]`. Establish `hinj : Function.Injective ψ` using `fun x y h => by rw [← hχψ x, ← hχψ y, h]`. Establish `hEE : H.ρL a * H.ρL a = H.ρL a` using `by rw [← map_mul, ha]`. Set `e` to `hd.some`. Set `Q1 : Matrix (Fin g) (Fin d) R` to `LinearMap.toMatrix' ((LinearMap.range (H.ρL a).mulVecLin).subtype ∘ₗ e.symm.toLinearMap)`.

Set `Q2 : Matrix (Fin d) (Fin g) R` to `LinearMap.toMatrix' (e.toLinearMap ∘ₗ (H.ρL a).mulVecLin.rangeRestrict)`. Establish `hQ12 : Q1 * Q2 = H.ρL a`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']`. Use `LinearMap.ext fun x => ?_` and prove the remaining obligations.

Simplify using `[Matrix.toLin'_apply]`. Establish `hQ21 : Q2 * Q1 = 1`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]`. Use `LinearMap.ext fun y => ?_` and prove the remaining obligations.

Establish `hz : (H.ρL a).mulVecLin.rangeRestrict ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) = e.symm y`. Apply `Subtype.ext` to reduce the goal to its premises. Take `⟨w, hw⟩` from `(e.symm y).2`. Use `show H.ρL a *ᵥ ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) = e.symm y`. Rewrite using `[← hw]`.

Use `show H.ρL a *ᵥ (H.ρL a *ᵥ w) = H.ρL a *ᵥ w`. Rewrite using `[Matrix.mulVec_mulVec, hEE]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, LinearMap.id_apply]`. Rewrite using `[hz, LinearEquiv.apply_symm_apply]`. Establish `hF : Q2ᵀ * Q1ᵀ = (H.ρL a)ᵀ` using `by rw [← Matrix.transpose_mul, hQ12]`.

Establish `h21 : Q1ᵀ * Q2ᵀ = 1` using `by rw [← Matrix.transpose_mul, hQ21, Matrix.transpose_one]`. Take `⟨eO⟩` from `omega_pull p ψ χ hχψ H.AA.carrier hA H.φ H.cotangent_surjective H.cotangent_ker_eq (H.ρL a)ᵀ Q2ᵀ Q1ᵀ hF h21 (fun f f' l hff hl => H.cotangent_linear a f f' l (fun t => by rw [hff, hred]) hl)`. Use `⟨pullHopf ψ H.AA (isLat_pull v hS.integers ψ hinj H.AA), pullHopf_carrier _ _ _, ?_⟩` and prove the remaining obligations. Rewrite using `[pullHopf_carrier]`. Conclude with `⟨d, fun _ => (p : R), ⟨eO.trans (qPi p d)⟩, by simp [Finset.prod_const]⟩`.
-/
theorem restrict_hopfOrder_length : RestrictedHopfOrderStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H a ha r Bw hrange hkerB d hd
  have hE : H.ρ a * H.ρ a = H.ρ a := by rw [← map_mul, ha]
  have hcol : ∀ j : Ix g, ∃ k : Fin r → ℤ_[p], Bw *ᵥ k = H.ρ a *ᵥ Pi.single j 1 := by
    intro j
    have hm : H.ρ a *ᵥ Pi.single j 1 ∈ LinearMap.range (Matrix.mulVecLin Bw) := by
      rw [hrange]
      exact ⟨Pi.single j 1, rfl⟩
    obtain ⟨k, hk⟩ := hm
    exact ⟨k, hk⟩
  choose kk hkk using hcol
  let K : Matrix (Fin r) (Ix g) ℤ_[p] := Matrix.of fun i j => kk j i
  have hBK : Bw * K = H.ρ a := by
    ext i j
    have h1 : (Bw * K) i j = (Bw *ᵥ kk j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, K]
    rw [h1, hkk j]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hKB : K * Bw = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun x => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    apply LinearMap.ker_eq_bot.mp hkerB
    show Bw *ᵥ ((K * Bw) *ᵥ x) = Bw *ᵥ x
    obtain ⟨y, hy⟩ : Bw *ᵥ x ∈ LinearMap.range (Matrix.mulVecLin (H.ρ a)) := by
      rw [← hrange]
      exact ⟨x, rfl⟩
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hBK, ← hy]
    show H.ρ a *ᵥ (H.ρ a *ᵥ y) = H.ρ a *ᵥ y
    rw [Matrix.mulVec_mulVec, hE]
  let ψ := psiW Bw
  let χ : Nb p g →+ (Fin r → ZMod p) := (Matrix.mulVecLin (K.map PadicInt.toZMod)).toAddMonoidHom
  have hχψ : ∀ x, χ (ψ x) = x := by
    intro x
    show K.map PadicInt.toZMod *ᵥ (Bw.map PadicInt.toZMod *ᵥ x) = x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hKB, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hred : ∀ t, ψ (χ (red p g t)) = red p g (H.ρ a *ᵥ t) := by
    intro t
    show Bw.map PadicInt.toZMod *ᵥ (K.map PadicInt.toZMod *ᵥ red p g t) = _
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hBK, ← red_mulVec]
  have hA : ∀ f ∈ H.AA.carrier, (fun n => f (ψ (χ n))) ∈ H.AA.carrier := by
    intro f hf
    obtain ⟨f', hf', hff⟩ := H.h3 a f hf
    convert hf' using 1
    funext n
    obtain ⟨t, rfl⟩ := red_surj n
    rw [hff, hred]
  have hinj : Function.Injective ψ := fun x y h => by rw [← hχψ x, ← hχψ y, h]
  have hEE : H.ρL a * H.ρL a = H.ρL a := by rw [← map_mul, ha]
  let e := hd.some
  let Q1 : Matrix (Fin g) (Fin d) R :=
    LinearMap.toMatrix' ((LinearMap.range (H.ρL a).mulVecLin).subtype ∘ₗ e.symm.toLinearMap)
  let Q2 : Matrix (Fin d) (Fin g) R :=
    LinearMap.toMatrix' (e.toLinearMap ∘ₗ (H.ρL a).mulVecLin.rangeRestrict)
  have hQ12 : Q1 * Q2 = H.ρL a := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    refine LinearMap.ext fun x => ?_
    simp [Matrix.toLin'_apply]
  have hQ21 : Q2 * Q1 = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    refine LinearMap.ext fun y => ?_
    have hz : (H.ρL a).mulVecLin.rangeRestrict ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) =
        e.symm y := by
      apply Subtype.ext
      obtain ⟨w, hw⟩ := (e.symm y).2
      show H.ρL a *ᵥ ((e.symm y : LinearMap.range (H.ρL a).mulVecLin) : Fin g → R) = e.symm y
      rw [← hw]
      show H.ρL a *ᵥ (H.ρL a *ᵥ w) = H.ρL a *ᵥ w
      rw [Matrix.mulVec_mulVec, hEE]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply, LinearMap.id_apply]
    rw [hz, LinearEquiv.apply_symm_apply]
  have hF : Q2ᵀ * Q1ᵀ = (H.ρL a)ᵀ := by rw [← Matrix.transpose_mul, hQ12]
  have h21 : Q1ᵀ * Q2ᵀ = 1 := by rw [← Matrix.transpose_mul, hQ21, Matrix.transpose_one]
  obtain ⟨eO⟩ := omega_pull p ψ χ hχψ H.AA.carrier hA H.φ H.cotangent_surjective H.cotangent_ker_eq (H.ρL a)ᵀ Q2ᵀ Q1ᵀ hF h21
    (fun f f' l hff hl => H.cotangent_linear a f f' l (fun t => by rw [hff, hred]) hl)
  refine ⟨pullHopf ψ H.AA (isLat_pull v hS.integers ψ hinj H.AA), pullHopf_carrier _ _ _, ?_⟩
  rw [pullHopf_carrier]
  exact ⟨d, fun _ => (p : R), ⟨eO.trans (qPi p d)⟩, by simp [Finset.prod_const]⟩

end ReciprocityTheory.PGsh.Up
