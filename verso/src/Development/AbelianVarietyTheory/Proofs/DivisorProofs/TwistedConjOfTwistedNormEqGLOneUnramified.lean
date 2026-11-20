import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90TensorPadicUnramifiedExtension
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

namespace GlobalTheory.LKMid

/- English proof (translation)
Unfold `nrmG`. Rewrite using `[map_list_prod, List.map_map]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `i _`.

Conclude with `(Function.Semiconj.iterate_right (f := f) (ga := θ) (gb := θ') hf i) x`.
-/
theorem twistedNormProductIterate_map_intertwining {H H' : Type} [Group H] [Group H'] (θ : H →* H) (θ' : H' →* H') (f : H →* H')
    (hf : ∀ x, f (θ x) = θ' (f x)) (r : ℕ) (x : H) : f (nrmG θ r x) = nrmG θ' r (f x) := by
  unfold nrmG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (Function.Semiconj.iterate_right (f := f) (ga := θ) (gb := θ') hf i) x

/- English proof (translation)
Unfold `nrmG`. Rewrite using `[← List.prod_map_mul]`. Use `congr 1`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `i hi`.

Use `clear hi`. Proceed by induction on `i generalizing a b with`. Consider the case `zero => rfl`. Consider the case `succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_mul, ih]`.
-/
theorem twistedNormProductIterate_mul_commGroup {H : Type} [CommGroup H] (θ : H →* H) (r : ℕ) (a b : H) :
    nrmG θ r (a * b) = nrmG θ r a * nrmG θ r b := by
  unfold nrmG
  rw [← List.prod_map_mul]
  congr 1
  apply List.map_congr_left
  intro i hi
  clear hi
  induction i generalizing a b with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_mul, ih]

end GlobalTheory.LKMid

namespace GlobalTheory.LKMid

/- English proof (translation)
Use `ext`. Simplify using `[GlobalTheory.LKLoc.sig, Matrix.det_unique]`. Both sides reduce to the same expression.
-/
theorem det_unramifiedExtFrobeniusGLEntrywise_GL_one (p : ℕ) [Fact p.Prime] (r : ℕ) (x : GL (Fin 1) (Qr p r)) :
    Matrix.GeneralLinearGroup.det (GlobalTheory.LKLoc.sig p (Q0 p) 1 r x) =
      Units.map (frobQ p r).toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det x) := by
  ext
  simp [GlobalTheory.LKLoc.sig, Matrix.det_unique]
  rfl

/- English proof (translation)
Introduce `x y h`. Use extensionality with `i j`. Use `congrArg Units.val h` as an intermediate fact. Simplify using `[Matrix.det_unique] at this`. Use `fin_cases i`.

Use `fin_cases j`. Conclude with `this`.
-/
theorem generalLinearGroup_det_injective_GL_one (R : Type) [CommRing R] :
    Function.Injective (Matrix.GeneralLinearGroup.det : GL (Fin 1) R →* Rˣ) := by
  intro x y h
  ext i j
  have := congrArg Units.val h
  simp [Matrix.det_unique] at this
  fin_cases i; fin_cases j
  exact this

/- English proof (translation)
Use `ext`. Simplify using `[Matrix.det_unique]`.
-/
theorem generalLinearGroup_det_scalar_GL_one (R : Type) [CommRing R] (u : Rˣ) :
    Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) u) = u := by
  ext
  simp [Matrix.det_unique]

/- English proof (translation)
Introduce `p _ r hr δ δ' hN`. Set `D : GL (Fin 1) (Qr p r) →* (Qr p r)ˣ` to `Matrix.GeneralLinearGroup.det`. Set `θ : (Qr p r)ˣ →* (Qr p r)ˣ` to `Units.map (frobQ p r).toRingHom.toMonoidHom`. Establish `hD : ∀ x, D (GlobalTheory.LKLoc.sig p (Q0 p) 1 r x) = θ (D x)` using `det_unramifiedExtFrobeniusGLEntrywise_GL_one p r`. Establish `hN' : nrmG θ r (D δ) = nrmG θ r (D δ')`.

Rewrite using `[← twistedNormProductIterate_map_intertwining _ _ D hD, ← twistedNormProductIterate_map_intertwining _ _ D hD, hN]`. Set `c : (Qr p r)ˣ` to `D δ' * (D δ)⁻¹`. Establish `hc : nrmG θ r c = 1`. Establish `h1 : nrmG θ r c * nrmG θ r (D δ) = nrmG θ r (D δ)`. Rewrite using `[← twistedNormProductIterate_mul_commGroup, inv_mul_cancel_right, hN']`.

Conclude with `mul_eq_right.1 h1`. Set `L` to `Algebra.TensorProduct.lid ℚ_[p] (Qr p r)`. Set `Φ` to `Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (frobQ p r)`. Establish `hL : ∀ x, L (Φ x) = frobQ p r (L x)`. Introduce `x`.

Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul b y`. Simplify using `only [L, Φ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, AlgHom.id_apply]`. Conclude with `((frobQ p r).toLinearMap.map_smul b y).symm`.

Consider the case `add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]`. Establish `hLs : ∀ y, L.symm (frobQ p r y) = Φ (L.symm y)`. Introduce `y`. Apply `L.injective` to reduce the goal to its premises. Rewrite using `[hL, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]`.

Set `fS : (Qr p r)ˣ →* (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ` to `Units.map L.symm.toAlgHom.toRingHom.toMonoidHom`. Set `fL : (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ →* (Qr p r)ˣ` to `Units.map L.toAlgHom.toRingHom.toMonoidHom`. Set `ΦU : (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ →* (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ` to `Units.map Φ.toRingHom.toMonoidHom`. Establish `hfS : ∀ x, fS (θ x) = ΦU (fS x)` using `fun x => Units.ext (hLs x)`. Establish `hfL : ∀ x, fL (ΦU x) = θ (fL x)` using `fun x => Units.ext (hL x)`.

Establish `hLS : ∀ x, fL (fS x) = x` using `fun x => Units.ext (AlgEquiv.apply_symm_apply L x)`. Establish `ha : nrmG ΦU r (fS c) = 1`. Rewrite using `[← twistedNormProductIterate_map_intertwining _ _ fS hfS, hc, map_one]`. Take `⟨g, hg⟩` from `hilbert90_frobenius_tensor_unramified_padic p r hr ℚ_[p] (fS c) ha`. Establish `hc' : c = (fL g)⁻¹ * θ (fL g)`.

Rewrite using `[← hLS c, hg, map_mul, map_inv, hfL]`. Use `⟨GeneralLinearGroup.scalar (Fin 1) (fL g), generalLinearGroup_det_injective_GL_one _ ?_⟩` and prove the remaining obligations. Establish `hs : D (GeneralLinearGroup.scalar (Fin 1) (fL g)) = fL g` using `generalLinearGroup_det_scalar_GL_one _ _`. Establish `e : D δ' = c * D δ` using `by rw [inv_mul_cancel_right]`. Express the relevant statement in the definitionally equal form `D δ' = D ((GeneralLinearGroup.scalar (Fin 1) (fL g))⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r (GeneralLinearGroup.scalar (Fin 1) (fL g)))`.

Rewrite using `[map_mul, map_mul, map_inv, hD, hs, e, hc']`. Conclude with `mul_right_comm _ _ _`.
-/
theorem exists_sig_twisted_conj_of_nrmG_eq : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ δ' : GL (Fin 1) (Qr p r),
    nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ' →
    ∃ h : GL (Fin 1) (Qr p r), δ' = h⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r h := by
  intro p _ r hr δ δ' hN
  let D : GL (Fin 1) (Qr p r) →* (Qr p r)ˣ := Matrix.GeneralLinearGroup.det
  let θ : (Qr p r)ˣ →* (Qr p r)ˣ := Units.map (frobQ p r).toRingHom.toMonoidHom
  have hD : ∀ x, D (GlobalTheory.LKLoc.sig p (Q0 p) 1 r x) = θ (D x) := det_unramifiedExtFrobeniusGLEntrywise_GL_one p r
  have hN' : nrmG θ r (D δ) = nrmG θ r (D δ') := by
    rw [← twistedNormProductIterate_map_intertwining _ _ D hD, ← twistedNormProductIterate_map_intertwining _ _ D hD, hN]
  let c : (Qr p r)ˣ := D δ' * (D δ)⁻¹
  have hc : nrmG θ r c = 1 := by
    have h1 : nrmG θ r c * nrmG θ r (D δ) = nrmG θ r (D δ) := by
      rw [← twistedNormProductIterate_mul_commGroup, inv_mul_cancel_right, hN']
    exact mul_eq_right.1 h1
  let L := Algebra.TensorProduct.lid ℚ_[p] (Qr p r)
  let Φ := Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (frobQ p r)
  have hL : ∀ x, L (Φ x) = frobQ p r (L x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      simp only [L, Φ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, AlgHom.id_apply]
      exact ((frobQ p r).toLinearMap.map_smul b y).symm
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hLs : ∀ y, L.symm (frobQ p r y) = Φ (L.symm y) := by
    intro y
    apply L.injective
    rw [hL, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  let fS : (Qr p r)ˣ →* (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ := Units.map L.symm.toAlgHom.toRingHom.toMonoidHom
  let fL : (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ →* (Qr p r)ˣ := Units.map L.toAlgHom.toRingHom.toMonoidHom
  let ΦU : (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ →* (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ := Units.map Φ.toRingHom.toMonoidHom
  have hfS : ∀ x, fS (θ x) = ΦU (fS x) := fun x => Units.ext (hLs x)
  have hfL : ∀ x, fL (ΦU x) = θ (fL x) := fun x => Units.ext (hL x)
  have hLS : ∀ x, fL (fS x) = x := fun x => Units.ext (AlgEquiv.apply_symm_apply L x)
  have ha : nrmG ΦU r (fS c) = 1 := by
    rw [← twistedNormProductIterate_map_intertwining _ _ fS hfS, hc, map_one]
  obtain ⟨g, hg⟩ := hilbert90_frobenius_tensor_unramified_padic p r hr ℚ_[p] (fS c) ha
  have hc' : c = (fL g)⁻¹ * θ (fL g) := by
    rw [← hLS c, hg, map_mul, map_inv, hfL]
  refine ⟨GeneralLinearGroup.scalar (Fin 1) (fL g), generalLinearGroup_det_injective_GL_one _ ?_⟩
  have hs : D (GeneralLinearGroup.scalar (Fin 1) (fL g)) = fL g := generalLinearGroup_det_scalar_GL_one _ _
  have e : D δ' = c * D δ := by rw [inv_mul_cancel_right]
  change D δ' = D ((GeneralLinearGroup.scalar (Fin 1) (fL g))⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r (GeneralLinearGroup.scalar (Fin 1) (fL g)))
  rw [map_mul, map_mul, map_inv, hD, hs, e, hc']
  exact mul_right_comm _ _ _

end GlobalTheory.LKMid
