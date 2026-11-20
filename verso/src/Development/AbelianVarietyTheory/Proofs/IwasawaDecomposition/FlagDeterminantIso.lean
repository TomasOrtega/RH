import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAA
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueEmbeddingEigenspaceSumStatement
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.FlagMod (ev lieBasis rdet detChg)

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}

section Basis

variable {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}

/- English proof (translation)
Establish `heig : ∀ (τ : E →+* ℂ) (a : Fin (Dw.mult τ) → R) (b : 𝓞 E), actR Z.t.act b (∑ i, a i • g.vec τ i) = φ (embK c τ b) • ∑ i, a i • g.vec τ i` using `fun τ a b => by`. Simplify using `only [map_sum, map_smul, g.act_vec, Finset.smul_sum, smul_comm (a _)]`. Establish `hli : LinearIndependent R (fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => g.vec p.1 p.2)`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `a ha p`.

Establish `hw` using `(GlobalTheory.T.existsUnique_embedding_eigenspace_sum c φ (actR Z.t.act) 0).unique (y₁ := fun τ => ∑ i, a ⟨τ, i⟩ • g.vec τ i) (y₂ := fun _ => 0) ⟨fun τ b => heig τ _ b, by rw [← ha, Fintype.sum_sigma]⟩ ⟨fun τ b => by simp, by simp⟩`. Establish `h0` using `congrFun hw p.1`. Conclude with `Fintype.linearIndependent_iff.1 (g.linearIndependent_vec p.1) (fun i => a ⟨p.1, i⟩) h0 p.2`. Establish `hsp : ⊤ ≤ Submodule.span R (Set.range fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => g.vec p.1 p.2)`. Introduce `v _`.

Take `⟨w, ⟨hw, hs⟩, -⟩` from `GlobalTheory.T.existsUnique_embedding_eigenspace_sum c φ (actR Z.t.act) v`. Rewrite using `[← hs]`. Use `Submodule.sum_mem _ fun τ _ => ?_` and prove the remaining obligations. Take `⟨a, ha, -⟩` from `g.existsUnique_sum τ (w τ) (hw τ)`. Rewrite using `[ha]`.

Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨τ, i⟩, rfl⟩)`. Conclude with `⟨Module.Basis.mk hli hsp, fun p => by rw [Module.Basis.mk_apply]⟩`.
-/
theorem exists_eigBasis (g : EigFrame Z φ x) : ∃ b : Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) R (TanM x Z.t.G),
    ∀ p, b p = g.vec p.1 p.2 := by
  have heig : ∀ (τ : E →+* ℂ) (a : Fin (Dw.mult τ) → R) (b : 𝓞 E),
      actR Z.t.act b (∑ i, a i • g.vec τ i) = φ (embK c τ b) • ∑ i, a i • g.vec τ i := fun τ a b => by
    simp only [map_sum, map_smul, g.act_vec, Finset.smul_sum, smul_comm (a _)]
  have hli : LinearIndependent R (fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => g.vec p.1 p.2) := by
    rw [Fintype.linearIndependent_iff]
    intro a ha p
    have hw := (GlobalTheory.T.existsUnique_embedding_eigenspace_sum c φ (actR Z.t.act) 0).unique
      (y₁ := fun τ => ∑ i, a ⟨τ, i⟩ • g.vec τ i) (y₂ := fun _ => 0)
      ⟨fun τ b => heig τ _ b, by rw [← ha, Fintype.sum_sigma]⟩ ⟨fun τ b => by simp, by simp⟩
    have h0 := congrFun hw p.1
    exact Fintype.linearIndependent_iff.1 (g.linearIndependent_vec p.1) (fun i => a ⟨p.1, i⟩) h0 p.2
  have hsp : ⊤ ≤ Submodule.span R (Set.range fun p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => g.vec p.1 p.2) := by
    intro v _
    obtain ⟨w, ⟨hw, hs⟩, -⟩ := GlobalTheory.T.existsUnique_embedding_eigenspace_sum c φ (actR Z.t.act) v
    rw [← hs]
    refine Submodule.sum_mem _ fun τ _ => ?_
    obtain ⟨a, ha, -⟩ := g.existsUnique_sum τ (w τ) (hw τ)
    rw [ha]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨τ, i⟩, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun p => by rw [Module.Basis.mk_apply]⟩

def eigBasis (g : EigFrame Z φ x) : Module.Basis (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) R (TanM x Z.t.G) :=
  (exists_eigBasis g).choose

/- English proof (translation)
The claim follows from `(exists_eigBasis g).choose_spec p`.
-/
theorem eigBasis_apply (g : EigFrame Z φ x) (p : Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : eigBasis g p = g.vec p.1 p.2 :=
  (exists_eigBasis g).choose_spec p

def eigBasisFin (g : EigFrame Z φ x) : Module.Basis (Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ)))) R (TanM x Z.t.G) :=
  (eigBasis g).reindex (Fintype.equivFin _)

def frameDet (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g : EigFrame Z φ x) : R :=
  rdet ((lieBasis M x h).toMatrix (eigBasisFin g))

/- English proof (translation)
The claim follows from `GlobalTheory.FlagMod.isUnit_rdet_toMatrix _ _`.
-/
theorem isUnit_frameDet (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g : EigFrame Z φ x) : IsUnit (frameDet M h g) :=
  GlobalTheory.FlagMod.isUnit_rdet_toMatrix _ _

/- English proof (translation)
Rewrite using `[GlobalTheory.FlagMod.ev_detChg M M' x h h' hh, frameDet, frameDet, GlobalTheory.FlagMod.rdet_toMatrix_mul]`.
-/
theorem ev_detChg_mul_frameDet (M M' : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ M'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ M'.U)) (g : EigFrame Z φ x) :
    ev x _ hh (detChg M M').val * frameDet M' h' g = frameDet M h g := by
  rw [GlobalTheory.FlagMod.ev_detChg M M' x h h' hh, frameDet, frameDet, GlobalTheory.FlagMod.rdet_toMatrix_mul]

open Classical in

/- English proof (translation)
Use extensionality with `⟨σ, b⟩ ⟨τ, i⟩`. Establish `hv : ∀ a, g.vec τ a = eigBasis g ⟨τ, a⟩` using `fun a => (eigBasis_apply g ⟨τ, a⟩).symm`. Rewrite using `[Module.Basis.toMatrix_apply, eigBasis_apply, g.vec_eq g' τ i]`. Simplify using `only [hv, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]`. Distinguish the cases in `h : σ = τ`.

Substitute `h` using the available equality. Simplify using `[Matrix.blockDiagonal'_apply_eq]`. Rewrite using `[Matrix.blockDiagonal'_apply_ne _ _ _ h]`. Conclude with `Finset.sum_eq_zero fun a _ => by rw [if_neg fun e => h (congrArg Sigma.fst e).symm, MulZeroClass.mul_zero]`.
-/
theorem eigBasis_toMatrix (g g' : EigFrame Z φ x) :
    (eigBasis g).toMatrix (eigBasis g') = Matrix.blockDiagonal' fun τ => g.co g' τ := by
  classical
  ext ⟨σ, b⟩ ⟨τ, i⟩
  have hv : ∀ a, g.vec τ a = eigBasis g ⟨τ, a⟩ := fun a => (eigBasis_apply g ⟨τ, a⟩).symm
  rw [Module.Basis.toMatrix_apply, eigBasis_apply, g.vec_eq g' τ i]
  simp only [hv, map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  by_cases h : σ = τ
  · subst h
    simp [Matrix.blockDiagonal'_apply_eq]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    exact Finset.sum_eq_zero fun a _ => by rw [if_neg fun e => h (congrArg Sigma.fst e).symm, MulZeroClass.mul_zero]

open Classical in
/- English proof (translation)
Rewrite using `[frameDet, frameDet, ← GlobalTheory.FlagMod.rdet_toMatrix_mul _ (eigBasisFin g), GlobalTheory.FlagMod.rdet_self]`. Use `congr 1`. Establish `e : (eigBasisFin g).toMatrix (eigBasisFin g') = ((eigBasis g).toMatrix (eigBasis g')).submatrix (Fintype.equivFin _).symm (Fintype.equivFin _).symm`. Use extensionality with `i j`. Simplify using `[eigBasisFin, Module.Basis.toMatrix_apply]`.

Rewrite using `[e, Matrix.det_submatrix_equiv_self, eigBasis_toMatrix, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal']`.
-/
theorem frameDet_change (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (g g' : EigFrame Z φ x) :
    frameDet M h g' = frameDet M h g * ∏ τ, (g.co g' τ).det := by
  rw [frameDet, frameDet, ← GlobalTheory.FlagMod.rdet_toMatrix_mul _ (eigBasisFin g), GlobalTheory.FlagMod.rdet_self]
  congr 1
  have e : (eigBasisFin g).toMatrix (eigBasisFin g') =
      ((eigBasis g).toMatrix (eigBasis g')).submatrix (Fintype.equivFin _).symm (Fintype.equivFin _).symm := by
    ext i j
    simp [eigBasisFin, Module.Basis.toMatrix_apply]
  rw [e, Matrix.det_submatrix_equiv_self, eigBasis_toMatrix, ReciprocityTheory.ChartRestriction.G.T0.HDiscLat.det_blockDiagonal']

/- English proof (translation)
Use extensionality with `i j`. Establish `e : v' j = ∑ k, ψ (b.repr (v j) k) • b' k`. Rewrite using `[← hv, ← b.sum_repr (v j), map_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [map_smulₛₗ, hb, b.sum_repr]`. Rewrite using `[Module.Basis.toMatrix_apply, e, Module.Basis.repr_sum_self]`.

Both sides reduce to the same expression.
-/
theorem toMatrix_map_of_semilinear {R' : Type} [CommRing R'] {N N' : Type} [AddCommGroup N] [Module R N]
    [AddCommGroup N'] [Module R' N'] {ψ : R →+* R'} (f : N →ₛₗ[ψ] N') {n m : ℕ} (b : Module.Basis (Fin n) R N)
    (b' : Module.Basis (Fin n) R' N') (v : Fin m → N) (v' : Fin m → N') (hb : ∀ i, f (b i) = b' i)
    (hv : ∀ j, f (v j) = v' j) : b'.toMatrix v' = (b.toMatrix v).map ψ := by
  ext i j
  have e : v' j = ∑ k, ψ (b.repr (v j) k) • b' k := by
    rw [← hv, ← b.sum_repr (v j), map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smulₛₗ, hb, b.sum_repr]
  rw [Module.Basis.toMatrix_apply, e, Module.Basis.repr_sum_self]
  rfl

/- English proof (translation)
Rewrite using `[frameDet, frameDet, GlobalTheory.FlagMod.map_rdet]`. Use `congr 1`. Use `toMatrix_map_of_semilinear (GlobalTheory.FlagMod.tanPull ψ e) _ _ _ _ (fun j => GlobalTheory.FlagMod.tanPull_lieBasis M ψ e h h' j) fun j => ?_` and prove the remaining obligations. Simplify using `only [eigBasisFin, Module.Basis.reindex_apply, eigBasis_apply]`. Apply `GlobalTheory.FlagMod.tan_ext_left` to reduce the goal to its premises.

Rewrite using `[GlobalTheory.FlagMod.tanPull_left]`. Simplify using `only [EigFrame.vec, GlobalTheory.LieMet.left_tanOf]`. Conclude with `(hg _ _).symm`.
-/
theorem frameDet_isMap {R' : Type} [CommRing R'] {φ' : c.F →+* R'} {x' : Sp R' ⟶ Z.X} (ψ : R →+* R')
    (e : spMap ψ ≫ x = x') (M : GlobalTheory.Reg.MChart Z) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x' ⁻¹ᵁ M.U)
    (g : EigFrame Z φ x) (g' : EigFrame Z φ' x') (hg : g.IsMap ψ g') :
    frameDet M h' g' = ψ (frameDet M h g) := by
  rw [frameDet, frameDet, GlobalTheory.FlagMod.map_rdet]
  congr 1
  refine toMatrix_map_of_semilinear (GlobalTheory.FlagMod.tanPull ψ e) _ _ _ _
    (fun j => GlobalTheory.FlagMod.tanPull_lieBasis M ψ e h h' j) fun j => ?_
  simp only [eigBasisFin, Module.Basis.reindex_apply, eigBasis_apply]
  apply GlobalTheory.FlagMod.tan_ext_left
  rw [GlobalTheory.FlagMod.tanPull_left]
  simp only [EigFrame.vec, GlobalTheory.LieMet.left_tanOf]
  exact (hg _ _).symm

end Basis

section Flag

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

/- English proof (translation)
Establish `: (Y.fromSpecStalk x).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom = Y.presheaf.germ V x hx`. Rewrite using `[Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]`. Simplify using `only [Category.assoc, ← Functor.map_comp]`. Rewrite using `[show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤), (Spec (Y.presheaf.stalk x)).presheaf.map q = 𝟙 _ from fun q => by`. Rewrite using `[Subsingleton.elim q (𝟙 _)]`.

Conclude with `CategoryTheory.Functor.map_id _ _]`. Simplify using the standard rewrite rules. Conclude with `congrArg (fun q => CommRingCat.Hom.hom q u) this`.
-/
theorem ev_fromSpecStalk_eq {Y : Scheme.{0}} (x : Y) {V : Y.Opens} (hx : x ∈ V) (h : ⊤ ≤ Y.fromSpecStalk x ⁻¹ᵁ V)
    (u : Γ(Y, V)) : ev (Y.fromSpecStalk x) V h u = (Y.presheaf.germ V x hx).hom u := by
  have : (Y.fromSpecStalk x).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (Y.presheaf.stalk x)).hom =
      Y.presheaf.germ V x hx := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [show ∀ q : (Opposite.op (⊤ : (Spec (Y.presheaf.stalk x)).Opens) ⟶ Opposite.op ⊤),
      (Spec (Y.presheaf.stalk x)).presheaf.map q = 𝟙 _ from fun q => by
        rw [Subsingleton.elim q (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _]
    simp
  exact congrArg (fun q => CommRingCat.Hom.hom q u) this

/- English proof (translation)
Introduce `z _`. Establish `hz : X.fromSpecStalk y z ⤳ y`. Establish `: X.fromSpecStalk y z ∈ Set.range (X.fromSpecStalk y)` using `⟨z, rfl⟩`. Rewrite `this` using `[Scheme.range_fromSpecStalk]`. Then use the resulting hypothesis. Conclude with `(hz.map f.continuous).mem_open V.isOpen hy`.
-/
theorem top_le_stalk_preimage {X Y : Scheme.{0}} (y : X) (f : X ⟶ Y) {V : Y.Opens} (hy : f y ∈ V) :
    ⊤ ≤ (X.fromSpecStalk y ≫ f) ⁻¹ᵁ V := by
  intro z _
  have hz : X.fromSpecStalk y z ⤳ y := by
    have : X.fromSpecStalk y z ∈ Set.range (X.fromSpecStalk y) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  exact (hz.map f.continuous).mem_open V.isOpen hy

/- English proof (translation)
Establish `h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ (f ⁻¹ᵁ V)` using `top_le_stalk_preimage (genericPoint X) (𝟙 X) hg`. Use `(ev_fromSpecStalk_eq (genericPoint X) hg h1 _).symm.trans (Eq.trans ?_ (GlobalTheory.FlagMod.ev_appLE (X.fromSpecStalk (genericPoint X)) f le_rfl h1 hh a))` and prove the remaining obligations. Rewrite using `[Scheme.Hom.app_eq_appLE]`.
-/
theorem fnOf_app_eq_ev {X Y : Scheme.{0}} [IsIntegral X] (f : X ⟶ Y) {V : Y.Opens} (hg : genericPoint X ∈ f ⁻¹ᵁ V)
    (hh : ⊤ ≤ (X.fromSpecStalk (genericPoint X) ≫ f) ⁻¹ᵁ V) (a : Γ(Y, V)) :
    fnOf (f ⁻¹ᵁ V) hg ((f.app V).hom a) = ev (X.fromSpecStalk (genericPoint X) ≫ f) V hh a := by
  have h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ (f ⁻¹ᵁ V) := top_le_stalk_preimage (genericPoint X) (𝟙 X) hg
  refine (ev_fromSpecStalk_eq (genericPoint X) hg h1 _).symm.trans (Eq.trans ?_
    (GlobalTheory.FlagMod.ev_appLE (X.fromSpecStalk (genericPoint X)) f le_rfl h1 hh a))
  rw [Scheme.Hom.app_eq_appLE]

variable {C}

/- English proof (translation)
The claim follows from `top_le_stalk_preimage y _ (mem_pull.1 hy)`.
-/
theorem top_le_of_mem_pull {y : C.Y.X} {J : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι}
    (hy : y ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J) : ⊤ ≤ (stalkPt C.Y y ≫ C.π ≫ genι Z) ⁻¹ᵁ (J PUnit.unit).U :=
  top_le_stalk_preimage y _ (mem_pull.1 hy)

/- English proof (translation)
The claim follows from `top_le_stalk_preimage _ _ (mem_pull.1 hy)`.
-/
theorem top_le_gen_of_mem_pull {J : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι}
    (hy : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J) :
    ⊤ ≤ (genericPt C.Y ≫ C.π ≫ genι Z) ⁻¹ᵁ (J PUnit.unit).U :=
  top_le_stalk_preimage _ _ (mem_pull.1 hy)

variable (C)

open Classical in

def FlagCpt.detRat (J : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι) : C.Y.X.functionFieldˣ :=
  if h : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J then
    ((isUnit_frameDet (J PUnit.unit) (top_le_gen_of_mem_pull h) C.f0).unit)⁻¹ else 1

/- English proof (translation)
Rewrite using `[FlagCpt.detRat, dif_pos h, Units.val_inv_eq_inv_val, IsUnit.unit_spec]`.
-/
theorem FlagCpt.detRat_val {J : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι}
    (h : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J) :
    (C.detRat J : C.Y.X.functionField) = (frameDet (J PUnit.unit) (top_le_gen_of_mem_pull h) C.f0)⁻¹ := by
  rw [FlagCpt.detRat, dif_pos h, Units.val_inv_eq_inv_val, IsUnit.unit_spec]

end Flag

section Presents

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

/- English proof (translation)
Use `show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _`. Rewrite using `[Fintype.prod_unique]`. Use `erw [zpow_one, LB.val_res, fnOf_resG]`. Establish `hg' : genericPoint C.Y.X ∈ (C.π ≫ genι Z) ⁻¹ᵁ ((J PUnit.unit).U ⊓ (J' PUnit.unit).U)` using `⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩`. Use `(fnOf_app_eq_ev (C.π ≫ genι Z) hg' hh _).trans ?_` and prove the remaining obligations.

Conclude with `map_units_inv (ev (genericPt C.Y ≫ C.π ≫ genι Z) _ hh).toMonoidHom _`.
-/
theorem fnOf_pull_detOm_g (J J' : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι)
    (hg : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J ⊓ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J')
    (hh : ⊤ ≤ (genericPt C.Y ≫ C.π ≫ genι Z) ⁻¹ᵁ ((J PUnit.unit).U ⊓ (J' PUnit.unit).U)) :
    fnOf _ hg (((FlagMod.detOm Z).pull (C.π ≫ genι Z)).g J J' : Γ(C.Y.X, _)) =
      (ev (genericPt C.Y ≫ C.π ≫ genι Z) _ hh (detChg (J PUnit.unit) (J' PUnit.unit)).val)⁻¹ := by
  show fnOf _ hg (Units.val (∏ _k : PUnit.{1}, _ ^ (1 : ℤ))) = _
  rw [Fintype.prod_unique]
  erw [zpow_one, LB.val_res, fnOf_resG]
  have hg' : genericPoint C.Y.X ∈ (C.π ≫ genι Z) ⁻¹ᵁ ((J PUnit.unit).U ⊓ (J' PUnit.unit).U) :=
    ⟨mem_pull.1 hg.1, mem_pull.1 hg.2⟩
  refine (fnOf_app_eq_ev (C.π ≫ genι Z) hg' hh _).trans ?_
  exact map_units_inv (ev (genericPt C.Y ≫ C.π ≫ genι Z) _ hh).toMonoidHom _

end Presents

section Presents2

variable {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e)

/- English proof (translation)
Introduce `J J' hg`. Establish `hJ` using `top_le_gen_of_mem_pull (C := C) hg.1`. Establish `hJ'` using `top_le_gen_of_mem_pull (C := C) hg.2`. Establish `hh` using `GlobalTheory.FlagMod.le_preimage_inf hJ hJ'`. Rewrite using `[C.detRat_val hg.1, C.detRat_val hg.2, fnOf_pull_detOm_g C J J' hg hh, ← ev_detChg_mul_frameDet (J PUnit.unit) (J' PUnit.unit) hJ hJ' hh C.f0, mul_inv]`.
-/
theorem FlagCpt.isRatSec_detRat : IsRatSec ((FlagMod.detOm Z).pull (C.π ≫ genι Z)) C.detRat := by
  intro J J' hg
  have hJ := top_le_gen_of_mem_pull (C := C) hg.1
  have hJ' := top_le_gen_of_mem_pull (C := C) hg.2
  have hh := GlobalTheory.FlagMod.le_preimage_inf hJ hJ'
  rw [C.detRat_val hg.1, C.detRat_val hg.2, fnOf_pull_detOm_g C J J' hg hh,
    ← ev_detChg_mul_frameDet (J PUnit.unit) (J' PUnit.unit) hJ hJ' hh C.f0, mul_inv]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact CartierDiv.isEqn_zero y`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `(ht a).add ih`.
-/
theorem isEqn_finset_sum {X : Scheme.{0}} [IsIntegral X] {T : Type} (s : Finset T) (D : T → CartierDiv X) (y : X)
    (t : T → X.functionFieldˣ) (ht : ∀ i, (D i).IsEqn y (t i)) : (∑ i ∈ s, D i).IsEqn y (∏ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact CartierDiv.isEqn_zero y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (ht a).add ih

/- English proof (translation)
Establish `hgen : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J` using `gen_mem hy`. Establish `hJ` using `top_le_gen_of_mem_pull (C := C) hgen`. Establish `hy'` using `top_le_of_mem_pull (C := C) hy`. Take `⟨φy, fy, t, htri, heq⟩` from `C.gr_spec y`. Take `⟨fy', hmap⟩` from `fy.exists_isMap (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) htri.2.1 htri.1`.

Establish `e1` using `frameDet_isMap _ htri.1.symm (J PUnit.unit) hy' hJ fy fy' hmap`. Establish `e2` using `frameDet_change (J PUnit.unit) hJ fy' C.f0`. Establish `e3 : ∀ τ, (fy'.co C.f0 τ).det = ∏ i, (t τ i : C.Y.Fn)` using `fun τ => by`. Take `⟨h1, h2⟩` from `EigFrame.Tri.co τ htri hmap`. Rewrite using `[Matrix.det_of_upperTriangular (fun i j hij => h1 i j hij)]`.

Conclude with `Finset.prod_congr rfl fun i _ => h2 i`. Establish `h0` using `(isEqn_finset_sum Finset.univ (fun x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => C.gr x.1 x.2) y (fun x => t x.1 x.2) fun x => heq x.1 x.2).neg`. Rewrite using `[h0.iff_unitAt, C.detRat_val hgen, e2, e1]`. Establish `hu` using `isUnit_frameDet (J PUnit.unit) hy' fy`. Establish `hP : ((∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t x.1 x.2 : C.Y.Fnˣ) : C.Y.Fn) = ∏ τ, (fy'.co C.f0 τ).det`.

Rewrite using `[Units.coe_prod, Fintype.prod_sigma]`. Conclude with `Finset.prod_congr rfl fun τ _ => (e3 τ).symm`. Establish `hP0 : (∏ τ, (fy'.co C.f0 τ).det) ≠ 0` using `hP ▸ Units.ne_zero _`. Rewrite using `[Units.val_inv_eq_inv_val, hP, mul_inv, mul_div_assoc, div_self (inv_ne_zero hP0), _root_.mul_one]`. Conclude with `UnitAt.inv ⟨_, hu, rfl⟩`.
-/
theorem FlagCpt.isEqn_detRat (J : ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).ι) (y : C.Y.X)
    (hy : y ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J) :
    (-∑ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), C.gr x.1 x.2).IsEqn y (C.detRat J) := by
  have hgen : genericPoint C.Y.X ∈ ((FlagMod.detOm Z).pull (C.π ≫ genι Z)).U J := gen_mem hy
  have hJ := top_le_gen_of_mem_pull (C := C) hgen
  have hy' := top_le_of_mem_pull (C := C) hy
  obtain ⟨φy, fy, t, htri, heq⟩ := C.gr_spec y
  obtain ⟨fy', hmap⟩ := fy.exists_isMap (algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField) htri.2.1 htri.1
  have e1 := frameDet_isMap _ htri.1.symm (J PUnit.unit) hy' hJ fy fy' hmap
  have e2 := frameDet_change (J PUnit.unit) hJ fy' C.f0
  have e3 : ∀ τ, (fy'.co C.f0 τ).det = ∏ i, (t τ i : C.Y.Fn) := fun τ => by
    obtain ⟨h1, h2⟩ := EigFrame.Tri.co τ htri hmap
    rw [Matrix.det_of_upperTriangular (fun i j hij => h1 i j hij)]
    exact Finset.prod_congr rfl fun i _ => h2 i
  have h0 := (isEqn_finset_sum Finset.univ (fun x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => C.gr x.1 x.2) y
    (fun x => t x.1 x.2) fun x => heq x.1 x.2).neg
  rw [h0.iff_unitAt, C.detRat_val hgen, e2, e1]
  have hu := isUnit_frameDet (J PUnit.unit) hy' fy
  have hP : ((∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t x.1 x.2 : C.Y.Fnˣ) : C.Y.Fn) = ∏ τ, (fy'.co C.f0 τ).det := by
    rw [Units.coe_prod, Fintype.prod_sigma]
    exact Finset.prod_congr rfl fun τ _ => (e3 τ).symm
  have hP0 : (∏ τ, (fy'.co C.f0 τ).det) ≠ 0 := hP ▸ Units.ne_zero _
  rw [Units.val_inv_eq_inv_val, hP, mul_inv, mul_div_assoc, div_self (inv_ne_zero hP0), _root_.mul_one]
  exact UnitAt.inv ⟨_, hu, rfl⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨pull_isLB hL _, C.isRatSec_detRat, fun J y hy => C.isEqn_detRat J y hy⟩`.
-/
theorem FlagCpt.presents_detRat (hL : (FlagMod.detOm Z).IsLB) :
    Presents (-∑ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), C.gr x.1 x.2) ((FlagMod.detOm Z).pull (C.π ≫ genι Z))
      C.detRat :=
  ⟨pull_isLB hL _, C.isRatSec_detRat, fun J y hy => C.isEqn_detRat J y hy⟩

/- English proof (translation)
The claim follows from `(presents_toLB _).lbIso (C.presents_detRat hL)`.
-/
theorem FlagCpt.lbIso_detOm_pull (hL : (FlagMod.detOm Z).IsLB) :
    LBIso (C.Y.lb (-∑ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), C.gr x.1 x.2))
      ((FlagMod.detOm Z).pull (C.π ≫ genι Z)) :=
  (presents_toLB _).lbIso (C.presents_detRat hL)

end Presents2

/- English proof (translation)
Introduce `_ _ _ _ _ _ s Φ k` and use `(Φ.C k).lbIso_detOm_pull s.isRec.isLB_detOm`.
-/
theorem lbIso_detOm_flag : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag)
    (k : s.Comp), LBIso ((Φ.C k).Y.lb (-∑ x : Letter S.Dw, (Φ.C k).gr x.1 x.2))
      ((FlagMod.detOm s.T.Z).pull ((Φ.C k).π ≫ genι s.T.Z)) :=
  fun _ _ _ _ _ _ s Φ k => (Φ.C k).lbIso_detOm_pull s.isRec.isLB_detOm

end GlobalTheory.ShFam
