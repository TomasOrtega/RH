import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionProductsSlicesOrthogonalDecompositi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SliceModel

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

/- English proof (translation)
Rewrite using `[← p.ι_π (p.ι x), p.π_ι]`.
-/
theorem ι_e (x : k) : p.e * p.ι x = p.ι x := by
  rw [← p.ι_π (p.ι x), p.π_ι]

/- English proof (translation)
Establish `h1 : p.ι (x * y) = p.ι (p.π (p.ι x * p.ι y))` using `by rw [map_mul p.π, p.π_ι, p.π_ι]`. Rewrite using `[h1, p.ι_π, ← mul_assoc, ι_e]`.
-/
theorem ι_mul (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h1 : p.ι (x * y) = p.ι (p.π (p.ι x * p.ι y)) := by rw [map_mul p.π, p.π_ι, p.π_ι]
  rw [h1, p.ι_π, ← mul_assoc, ι_e]

/- English proof (translation)
Rewrite using `[ι_mul, p.ι_π, ← mul_assoc, mul_comm (p.ι x) p.e, ι_e]`.
-/
theorem ι_mul_right (x : k) (z : AE D) : p.ι x * z = p.ι (x * p.π z) := by
  rw [ι_mul, p.ι_π, ← mul_assoc, mul_comm (p.ι x) p.e, ι_e]

/- English proof (translation)
Rewrite using `[mul_comm, ι_mul_right, mul_comm]`.
-/
theorem ι_mul_left (x : k) (z : AE D) : z * p.ι x = p.ι (p.π z * x) := by
  rw [mul_comm, ι_mul_right, mul_comm]

def prH : D.host.E →+* k := p.π.comp (incA D)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prH_apply (a : D.host.E) : prH p a = p.pr a := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_right]`. Both sides reduce to the same expression.
-/
theorem map_ι_mul_rat {l m o : Type} [Fintype m] (M : Matrix l m k) (N : Matrix m o D.host.E) :
    M.map p.ι * N.map (incA D) = (M * N.map (prH p)).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_right]
  rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_left]`. Both sides reduce to the same expression.
-/
theorem rat_mul_map_ι {l m o : Type} [Fintype m] (N : Matrix l m D.host.E) (M : Matrix m o k) :
    N.map (incA D) * M.map p.ι = (N.map (prH p) * M).map p.ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, ι_mul_left]
  rfl

section Frames

variable {ρ : ℕ} (B : BesLev D ρ) (S : HSp D) (s : k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n)

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, B.o.qA_iA, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem qA_iA_k : B.o.qA.map (prH p) * B.o.iA.map (prH p) = 1 := by
  rw [← Matrix.map_mul, B.o.qA_iA, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _)]`.
-/
theorem qA_iB_k : B.o.qA.map (prH p) * B.o.iB.map (prH p) = 0 := by
  rw [← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _)]

variable {p B s FA F₀}

/- English proof (translation)
Use extensionality with `r j`. Break down `j with a | u` into its components or cases. Rewrite using `[h.1 r a]`. Simplify using `[Matrix.mul_apply, fromCols]`. Both sides reduce to the same expression.

Rewrite using `[h.2 r]`. Use `RingHom.map_mulVec (prH p) B.o.iB B.ζ r` as an intermediate fact. Simplify using `only [vecB] at *`. Rewrite `this` using `[prH_apply]`. Rewrite using `[this]`.

Simplify using `[Matrix.mul_apply, fromCols, Matrix.mulVec, dotProduct, Finset.mul_sum]`. Put the polynomial expressions in normal form.
-/
theorem β_eq (h : p.IsCoreFrame B s FA F₀) :
    F₀.β = B.o.iA.map (prH p) * fromCols FA.β 0 +
      B.o.iB.map (prH p) * fromCols 0 (Matrix.of fun i (_ : Unit) => s * prH p (B.ζ i)) := by
  ext r j
  rcases j with a | u
  · rw [h.1 r a]
    simp [Matrix.mul_apply, fromCols]
    rfl
  · rw [h.2 r]
    have := RingHom.map_mulVec (prH p) B.o.iB B.ζ r
    simp only [vecB] at *
    rw [prH_apply] at this
    rw [this]
    simp [Matrix.mul_apply, fromCols, Matrix.mulVec, dotProduct, Finset.mul_sum]
    ring_nf

/- English proof (translation)
Rewrite using `[β_eq h, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, qA_iA_k, qA_iB_k, Matrix.one_mul, Matrix.zero_mul, add_zero]`.
-/
theorem qA_β (h : p.IsCoreFrame B s FA F₀) : B.o.qA.map (prH p) * F₀.β = fromCols FA.β 0 := by
  rw [β_eq h, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, qA_iA_k, qA_iB_k, Matrix.one_mul, Matrix.zero_mul,
    add_zero]

/- English proof (translation)
Establish `e : FA.γ * B.o.qA.map (prH p) = FA.γ * B.o.qA.map (prH p) * (F₀.β * F₀.γ)` using `by rw [F₀.βγ, Matrix.mul_one]`. Rewrite using `[e, ← Matrix.mul_assoc, Matrix.mul_assoc FA.γ, qA_β h, Matrix.mul_fromCols, FA.γβ, Matrix.mul_zero, ← Matrix.fromRows_toRows F₀.γ, Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.toRows₁_fromRows]`.
-/
theorem γ_qA (h : p.IsCoreFrame B s FA F₀) : FA.γ * B.o.qA.map (prH p) = F₀.γ.toRows₁ := by
  have e : FA.γ * B.o.qA.map (prH p) = FA.γ * B.o.qA.map (prH p) * (F₀.β * F₀.γ) := by rw [F₀.βγ, Matrix.mul_one]
  rw [e, ← Matrix.mul_assoc, Matrix.mul_assoc FA.γ, qA_β h, Matrix.mul_fromCols, FA.γβ, Matrix.mul_zero,
    ← Matrix.fromRows_toRows F₀.γ, Matrix.fromCols_mul_fromRows, Matrix.one_mul, Matrix.zero_mul, add_zero, Matrix.toRows₁_fromRows]

/- English proof (translation)
Establish `e1 : B.o.iA.map (prH p) * FA.β = F₀.β * (fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) : Matrix (n' ⊕ Unit) n' k)`. Rewrite using `[← Matrix.fromCols_toCols F₀.β, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]`. Use extensionality with `r a`. Conclude with `(h.1 r a).symm`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, FA.βγ, Matrix.mul_one]`. Use `_ = (F₀.γ * F₀.β) * (fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) : Matrix (n' ⊕ Unit) n' k) * FA.γ := by`. Rewrite using `[e1]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = fromRows FA.γ 0 := by rw [F₀.γβ, Matrix.one_mul, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]`.
-/
theorem γ_iA (h : p.IsCoreFrame B s FA F₀) : F₀.γ * B.o.iA.map (prH p) = fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) := by
  have e1 : B.o.iA.map (prH p) * FA.β = F₀.β * (fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) : Matrix (n' ⊕ Unit) n' k) := by
    rw [← Matrix.fromCols_toCols F₀.β, Matrix.fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
    ext r a
    exact (h.1 r a).symm
  calc F₀.γ * B.o.iA.map (prH p) = F₀.γ * (B.o.iA.map (prH p) * FA.β) * FA.γ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, FA.βγ, Matrix.mul_one]
    _ = (F₀.γ * F₀.β) * (fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) : Matrix (n' ⊕ Unit) n' k) * FA.γ := by
        rw [e1]; simp only [Matrix.mul_assoc]
    _ = fromRows FA.γ 0 := by rw [F₀.γβ, Matrix.one_mul, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]

/- English proof (translation)
Establish `e : fromCols x (0 : Matrix n Unit k) * F₀.γ = x * F₀.γ.toRows₁` using `by conv_lhs => rw [← Matrix.fromRows_toRows F₀.γ]`. Rewrite using `[Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero]`. Rewrite using `[OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, OrthDec.pA, GlobalTheory.MixModel.rat, Place.up, Place.up, map_ι_mul_rat, Matrix.mul_assoc, γ_qA h, Matrix.mul_assoc FS.β (fromCols x 0) F₀.γ, e, Matrix.mul_assoc]`.
-/
theorem up_slice (h : p.IsCoreFrame B s FA F₀) (x : Matrix n n' k) :
    (B.o.resS S).symm (p.up FA FS x, 0) = p.up F₀ FS (fromCols x 0) := by
  have e : fromCols x (0 : Matrix n Unit k) * F₀.γ = x * F₀.γ.toRows₁ := by
    conv_lhs => rw [← Matrix.fromRows_toRows F₀.γ]
    rw [Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero]
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, OrthDec.pA, GlobalTheory.MixModel.rat, Place.up, Place.up, map_ι_mul_rat,
    Matrix.mul_assoc, γ_qA h, Matrix.mul_assoc FS.β (fromCols x 0) F₀.γ, e, Matrix.mul_assoc]

/- English proof (translation)
Establish `e : x * fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) = x.toCols₁ * FA.γ` using `by conv_lhs => rw [← Matrix.fromCols_toCols x]`. Rewrite using `[Matrix.fromCols_mul_fromRows, Matrix.mul_zero, add_zero]`. Use `show (p.up F₀ FS x) * B.o.jA = _`. Rewrite using `[OrthDec.jA, GlobalTheory.MixModel.rat, Place.up, Place.up, map_ι_mul_rat, Matrix.mul_assoc, γ_iA h, Matrix.mul_assoc, e, Matrix.mul_assoc]`.
-/
theorem res_up (h : p.IsCoreFrame B s FA F₀) (x : Matrix n (n' ⊕ Unit) k) :
    (B.o.resS S (p.up F₀ FS x)).1 = p.up FA FS x.toCols₁ := by
  have e : x * fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) = x.toCols₁ * FA.γ := by
    conv_lhs => rw [← Matrix.fromCols_toCols x]
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_zero, add_zero]
  show (p.up F₀ FS x) * B.o.jA = _
  rw [OrthDec.jA, GlobalTheory.MixModel.rat, Place.up, Place.up, map_ι_mul_rat, Matrix.mul_assoc, γ_iA h, Matrix.mul_assoc, e,
    Matrix.mul_assoc]

end Frames

section Tensor

variable (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def splitH : Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × (n → k) where
  toFun x := (x.toCols₁, fun r => x r (Sum.inr ()))
  invFun q := fromCols q.1 (Matrix.of fun r (_ : Unit) => q.2 r)
  left_inv x := by
    ext r j
    rcases j with j | j <;> rfl
  right_inv q := rfl
  continuous_toFun := (continuous_matrix fun i j => continuous_id.matrix_elem i (Sum.inl j)).prodMk
    (continuous_pi fun r => continuous_id.matrix_elem r (Sum.inr ()))
  continuous_invFun := continuous_matrix fun i j => by
    rcases j with j | j
    · exact continuous_fst.matrix_elem i j
    · exact (continuous_apply i).comp continuous_snd

variable {n n'}

def tens (a : (n → k) → ℂ) (ha : a ∈ SB (n → k)) : SB (Matrix n n' k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) where
  toFun Ξ := GlobalTheory.LocFlat.CFac.comapH (splitH n n') (GlobalTheory.LocFlat.CFac.prodSB Ξ ⟨a, ha⟩)
  map_add' Ξ Ξ' := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, add_mul]
  map_smul' c Ξ := by
    ext x
    simp [GlobalTheory.LocFlat.CFac.comapH_apply, GlobalTheory.LocFlat.CFac.prodSB_apply, mul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tens_apply (a : (n → k) → ℂ) (ha : a ∈ SB (n → k)) (Ξ : SB (Matrix n n' k)) (x : Matrix n (n' ⊕ Unit) k) :
    (tens a ha Ξ).1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ()) := rfl

end Tensor

/- English proof (translation)
Simplify using `[symplO, hO]`.
-/
theorem symplO_zero_right'' (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

/- English proof (translation)
Introduce `D k _ _ _ _ p ψ n n' _ _ _ _ ρ B S s FA F₀ FS h T₀ hT a ha v`. Set `T₁ : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ)` to `(LinearMap.funLeft ℂ ℂ fun u => (B.o.resS S).symm (u, v)) ∘ₗ T₀ ∘ₗ tens a ha`. Establish `hT₁ : ∀ Φ u, T₁ Φ u = T₀ (tens a ha Φ) ((B.o.resS S).symm (u, v))` using `fun _ _ => rfl`. Use `⟨T₁, ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.BoxSlice.isThetaFunO_slice_left B.o (hT.theta (tens a ha Φ)) v`.

Establish `h1 : ∀ t, (tens a ha Φ').1 t = (tens a ha Φ).1 (t + fromCols x 0)`. Introduce `t`. Rewrite using `[tens_apply, tens_apply, hΦ]`. Use `congr 2`. Use extensionality with `i j`.

Simplify using `[Matrix.toCols₁, fromCols]`. Establish `h2` using `hT.trans (fromCols x 0) _ _ h1`. Use function extensionality and compare the values at `u`. Rewrite using `[hT₁, h2, ← up_slice S FS h x]`. Simplify using `only [heisO, hT₁]`.

Rewrite using `[← map_add (B.o.resS S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]`. Establish `hY : IsHalf (cA D p.e) ((B.o.resS S).symm (y, 0))`. Introduce `i j`. Rewrite using `[OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, hy i l]`. Establish `h1 : ∀ t, (tens a ha Φ').1 t = ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (y, 0))) * (tens a ha Φ).1 t`. Introduce `t`. Rewrite using `[tens_apply, tens_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, res_up S FS h, symplO_zero_right'', add_zero, mul_assoc]`.

Establish `h2` using `hT.modul _ hY _ _ h1`. Use function extensionality and compare the values at `u`. Rewrite using `[hT₁, h2]`. Simplify using `only [heisO, hT₁]`. Rewrite using `[← map_add (B.o.resS S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]`.

Establish `e : Ψ = tens a ha Ξ` using `Subtype.ext (funext fun x => (hΨ x).trans (tens_apply a ha Ξ x).symm)`. Rewrite using `[e, hT₁]`.
-/
theorem exists_isModel_slice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ρ : ℕ) (B : BesLev D ρ) (S : HSp D) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ T₀, p.IsModel ψ F₀ FS T₀ → ∀ (a : (n → k) → ℂ), a ∈ SB _ → ∀ v : WO B.L S, ∃ T₁, p.IsModel ψ FA FS T₁ ∧ ∀ (Ξ : SB (Matrix n n' k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), (∀ x, Ψ.1 x = Ξ.1 x.toCols₁ * a fun r => x r (Sum.inr ())) → ∀ u, T₀ Ψ ((B.o.resS S).symm (u, v)) = T₁ Ξ u := by
  intro D k _ _ _ _ p ψ n n' _ _ _ _ ρ B S s FA F₀ FS h T₀ hT a ha v
  let T₁ : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ) :=
    (LinearMap.funLeft ℂ ℂ fun u => (B.o.resS S).symm (u, v)) ∘ₗ T₀ ∘ₗ tens a ha
  have hT₁ : ∀ Φ u, T₁ Φ u = T₀ (tens a ha Φ) ((B.o.resS S).symm (u, v)) := fun _ _ => rfl
  refine ⟨T₁, ⟨fun Φ => ?_, fun x Φ Φ' hΦ => ?_, fun y hy Φ Φ' hΦ => ?_⟩, fun Ξ Ψ hΨ u => ?_⟩
  · exact GlobalTheory.BoxSlice.isThetaFunO_slice_left B.o (hT.theta (tens a ha Φ)) v
  · have h1 : ∀ t, (tens a ha Φ').1 t = (tens a ha Φ).1 (t + fromCols x 0) := by
      intro t
      rw [tens_apply, tens_apply, hΦ]
      congr 2
      ext i j; simp [Matrix.toCols₁, fromCols]
    have h2 := hT.trans (fromCols x 0) _ _ h1
    funext u
    rw [hT₁, h2, ← up_slice S FS h x]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resS S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have hY : IsHalf (cA D p.e) ((B.o.resS S).symm (y, 0)) := by
      intro i j
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
      simp only [Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [← mul_assoc, hy i l]
    have h1 : ∀ t, (tens a ha Φ').1 t =
        ψ (symplO B.V₀ S (p.up F₀ FS t) ((B.o.resS S).symm (y, 0))) * (tens a ha Φ).1 t := by
      intro t
      rw [tens_apply, tens_apply, hΦ, B.o.symplO_resS, AddEquiv.apply_symm_apply, res_up S FS h,
        symplO_zero_right'', add_zero, mul_assoc]
    have h2 := hT.modul _ hY _ _ h1
    funext u
    rw [hT₁, h2]
    simp only [heisO, hT₁]
    rw [← map_add (B.o.resS S).symm, Prod.mk_add_mk, add_zero, B.o.symplOH_resS, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, GlobalTheory.MixModel.symplOH_zero_right, add_zero]
  · have e : Ψ = tens a ha Ξ := Subtype.ext (funext fun x => (hΨ x).trans (tens_apply a ha Ξ x).symm)
    rw [e, hT₁]

end GlobalTheory.SliceModel

end
