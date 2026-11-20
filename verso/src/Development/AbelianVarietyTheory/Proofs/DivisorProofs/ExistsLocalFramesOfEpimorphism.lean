import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.MixedLocalChains

/- English proof (translation)
Use `set N := M.transpose`. Establish `hinj : Function.Injective N.mulVecLin`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Conclude with `hM`. Establish `hrank : N.rank = r`.

Rewrite using `[Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]`. Establish `hspan : Submodule.span K (Set.range N.row) = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fin_fun]`. Take `⟨κ, a, ha, hsp, hli⟩` from `exists_linearIndependent' K N.row`.

Establish `: Finite κ` using `Finite.of_injective a ha`. Use `haveI : Fintype κ := Fintype.ofFinite κ`. Set `B` to `Module.Basis.mk hli (by rw [hsp, hspan])`. Establish `hcard : Fintype.card κ = r`. Rewrite using `[← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]`.

Set `e : Fin r ≃ κ` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `⟨a ∘ e, ?_⟩` and prove the remaining obligations. Establish `hli' : LinearIndependent K (N.submatrix (a ∘ e) id).row` using `hli.comp e e.injective`. Establish `hu` using `Matrix.linearIndependent_rows_iff_isUnit.mp hli'`. Establish `h` using `((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero`.

Rewrite `h` using `[show N.submatrix (a ∘ e) id = (M.submatrix id (a ∘ e)).transpose from rfl, Matrix.det_transpose]`. Then use the resulting hypothesis.
-/
theorem exists_cols_det_ne_zero {K : Type*} [Field K] {r m : ℕ} (M : Matrix (Fin r) (Fin m) K)
    (hM : ∀ c : Fin r → K, M.transpose.mulVec c = 0 → c = 0) :
    ∃ J : Fin r → Fin m, (M.submatrix id J).det ≠ 0 := by
  classical
  set N := M.transpose
  have hinj : Function.Injective N.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    exact hM
  have hrank : N.rank = r := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_fin_fun]
  have hspan : Submodule.span K (Set.range N.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [← Matrix.rank_eq_finrank_span_row, hrank, Module.finrank_fin_fun]
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K N.row
  have : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  let B := Module.Basis.mk hli (by rw [hsp, hspan])
  have hcard : Fintype.card κ = r := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hli' : LinearIndependent K (N.submatrix (a ∘ e) id).row := hli.comp e e.injective
  have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hli'
  have h := ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  rwa [show N.submatrix (a ∘ e) id = (M.submatrix id (a ∘ e)).transpose from rfl,
    Matrix.det_transpose] at h

/- English proof (translation)
Set `e` to `Scheme.Modules.restrictFunctorIsoPullback U.ι`. Establish `hψ : (Scheme.Modules.restrictFunctor U.ι).map φ = e.hom.app F ≫ (Scheme.Modules.pullback U.ι).map φ ≫ e.inv.app G` using `(NatIso.naturality_2 e φ).symm`. Use `haveI : Epi ((Scheme.Modules.restrictFunctor U.ι).map φ) := by rw [hψ]; infer_instance`. Set `y : U` to `⟨x, hx⟩`. Establish `hs` using `stalkLinear_surjective ((Scheme.Modules.restrictFunctor U.ι).map φ) y`.

Set `N` to `Scheme.Modules.restrictStalkNatIso U.ι y`. Establish `hn` using `N.hom.naturality φ`. Introduce `t`. Take `⟨t', rfl⟩` from `(N.app G).addCommGroupIsoToAddEquiv.surjective t`. Take `⟨s', rfl⟩` from `hs t'`.

Use `⟨N.hom.app F s', ?_⟩` and prove the remaining obligations. Use `ConcreteCategory.congr_hom hn s'` as an intermediate fact. Simplify using `only [ConcreteCategory.comp_apply] at this`. Conclude with `this.symm`.
-/
theorem surjective_stalkLinear_of_epi_pullback_ι {X : Scheme.{0}} {F G : X.Modules} (φ : F ⟶ G)
    (U : X.Opens) [Epi ((Scheme.Modules.pullback U.ι).map φ)] (x : X) (hx : x ∈ U) :
    Function.Surjective (stalkLinear φ x) := by
  let e := Scheme.Modules.restrictFunctorIsoPullback U.ι
  have hψ : (Scheme.Modules.restrictFunctor U.ι).map φ =
      e.hom.app F ≫ (Scheme.Modules.pullback U.ι).map φ ≫ e.inv.app G :=
    (NatIso.naturality_2 e φ).symm
  haveI : Epi ((Scheme.Modules.restrictFunctor U.ι).map φ) := by rw [hψ]; infer_instance
  let y : U := ⟨x, hx⟩
  have hs := stalkLinear_surjective ((Scheme.Modules.restrictFunctor U.ι).map φ) y
  let N := Scheme.Modules.restrictStalkNatIso U.ι y
  have hn := N.hom.naturality φ
  intro t
  obtain ⟨t', rfl⟩ := (N.app G).addCommGroupIsoToAddEquiv.surjective t
  obtain ⟨s', rfl⟩ := hs t'
  refine ⟨N.hom.app F s', ?_⟩
  have := ConcreteCategory.congr_hom hn s'
  simp only [ConcreteCategory.comp_apply] at this
  exact this.symm

end GlobalTheory.MixedLocalChains

namespace GlobalTheory.MixedLocalChains

open GlobalTheory.VB in

/- English proof (translation)
Introduce `O _ _ _ B r m E F φ hE hF hφ x`. Take `⟨U, eE₀, -, hxU, -, heE₀⟩` from `hE.exists_affine (V := ⊤) (x := x) trivial`. Take `⟨V, eF, hV, hxV, hVU, heF⟩` from `hF.exists_affine hxU`. Set `eE : Fin r → Γ(E, V)` to `fun i => GlobalTheory.Twist.resM E hVU (eE₀ i)`. Establish `heE : IsFrame eE` using `heE₀.res hVU`.

Set `a : Matrix (Fin r) (Fin m) Γ(B.X, V)` to `fun k j => (heE.basis le_rfl).repr (φ.app V (eF j)) k`. Establish `ha : ∀ j, φ.app V (eF j) = ∑ k, a k j • eE k`. Introduce `j`. Use `conv_lhs => rw [← (heE.basis le_rfl).sum_repr (φ.app V (eF j))]`. Simplify using `only [IsFrame.basis_apply, GlobalTheory.Twist.resM_self]`.

Both sides reduce to the same expression. Use `⟨V, eF, eE, a, hxV, hV, heF, heE, ha, ?_⟩` and prove the remaining obligations. Establish `hη : genericPoint B.X ∈ V` using `(genericPoint_specializes x).mem_open V.isOpen hxV`. Establish `hsurj : Function.Surjective (stalkLinear φ (genericPoint B.X))` using `surjective_stalkLinear_of_epi_pullback_ι φ B.gen _ B.genericPoint_mem_gen`. Set `g : Γ(B.X, V) →+* B.X.functionField` to `(B.X.presheaf.germ V _ hη).hom`.

Set `a' : Matrix (Fin r) (Fin m) B.X.functionField` to `a.map g`. Set `bE` to `heE.stalkBasis _ hη`. Set `bF` to `heF.stalkBasis _ hη`. Establish `hmul : ∀ v : Fin r → B.X.functionField, ∃ w, a'.mulVec w = v`. Introduce `v`.

Take `⟨s, hs⟩` from `hsurj (bE.equivFun.symm v)`. Use `⟨bF.repr s, bE.equivFun.symm.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← hs]`. Use `conv_rhs => rw [← bF.sum_repr s]`. Simplify using `only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, bF, bE, IsFrame.stalkBasis_apply, stalkLinear_germ, ha, QCoh.germ_smul, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Take `⟨J, hJ⟩` from `exists_cols_det_ne_zero a' fun c hc => by`.

Use function extensionality and compare the values at `k`. Take `⟨w, hw⟩` from `hmul (Pi.single k 1)`. Establish `h0 : c ⬝ᵥ a'.mulVec w = 0`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hc, zero_dotProduct]`. Rewrite `h0` using `[hw, dotProduct_single, mul_one]`. Then use the resulting hypothesis.

Use `⟨J, fun h0 => hJ ?_⟩` and prove the remaining obligations. Rewrite using `[show a'.submatrix id J = g.mapMatrix (a.submatrix id J) from rfl, ← RingHom.map_det, h0, map_zero]`.
-/
theorem exists_frames_maximal_minor_ne_zero : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (r m : ℕ) (E F : B.X.Modules) (φ : F ⟶ E), GlobalTheory.VB.IsVB E r → GlobalTheory.VB.IsVB F m → Epi (B.genRes.map φ) → ∀ x : B.X, ∃ (V : B.X.Opens) (eF : Fin m → Γ(F, V)) (eE : Fin r → Γ(E, V)) (a : Matrix (Fin r) (Fin m) Γ(B.X, V)), x ∈ V ∧ IsAffineOpen V ∧ GlobalTheory.VB.IsFrame eF ∧ GlobalTheory.VB.IsFrame eE ∧ (∀ j, φ.app V (eF j) = ∑ k, a k j • eE k) ∧ ∃ J : Fin r → Fin m, (a.submatrix id J).det ≠ 0 := by
  intro O _ _ _ B r m E F φ hE hF hφ x
  obtain ⟨U, eE₀, -, hxU, -, heE₀⟩ := hE.exists_affine (V := ⊤) (x := x) trivial
  obtain ⟨V, eF, hV, hxV, hVU, heF⟩ := hF.exists_affine hxU
  let eE : Fin r → Γ(E, V) := fun i => GlobalTheory.Twist.resM E hVU (eE₀ i)
  have heE : IsFrame eE := heE₀.res hVU
  let a : Matrix (Fin r) (Fin m) Γ(B.X, V) := fun k j => (heE.basis le_rfl).repr (φ.app V (eF j)) k
  have ha : ∀ j, φ.app V (eF j) = ∑ k, a k j • eE k := by
    intro j
    conv_lhs => rw [← (heE.basis le_rfl).sum_repr (φ.app V (eF j))]
    simp only [IsFrame.basis_apply, GlobalTheory.Twist.resM_self]
    rfl
  refine ⟨V, eF, eE, a, hxV, hV, heF, heE, ha, ?_⟩
  have hη : genericPoint B.X ∈ V := (genericPoint_specializes x).mem_open V.isOpen hxV
  have hsurj : Function.Surjective (stalkLinear φ (genericPoint B.X)) :=
    surjective_stalkLinear_of_epi_pullback_ι φ B.gen _ B.genericPoint_mem_gen
  let g : Γ(B.X, V) →+* B.X.functionField := (B.X.presheaf.germ V _ hη).hom
  let a' : Matrix (Fin r) (Fin m) B.X.functionField := a.map g
  let bE := heE.stalkBasis _ hη
  let bF := heF.stalkBasis _ hη
  have hmul : ∀ v : Fin r → B.X.functionField, ∃ w, a'.mulVec w = v := by
    intro v
    obtain ⟨s, hs⟩ := hsurj (bE.equivFun.symm v)
    refine ⟨bF.repr s, bE.equivFun.symm.injective ?_⟩
    rw [← hs]
    conv_rhs => rw [← bF.sum_repr s]
    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, bF, bE, IsFrame.stalkBasis_apply,
      stalkLinear_germ, ha, QCoh.germ_smul, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct,
      Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  obtain ⟨J, hJ⟩ := exists_cols_det_ne_zero a' fun c hc => by
    funext k
    obtain ⟨w, hw⟩ := hmul (Pi.single k 1)
    have h0 : c ⬝ᵥ a'.mulVec w = 0 := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hc, zero_dotProduct]
    rwa [hw, dotProduct_single, mul_one] at h0
  refine ⟨J, fun h0 => hJ ?_⟩
  rw [show a'.submatrix id J = g.mapMatrix (a.submatrix id J) from rfl, ← RingHom.map_det, h0, map_zero]

end GlobalTheory.MixedLocalChains
