import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupBplus.Aff.Descent

variable {p : ℕ} {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

/- English proof (translation)
Use `PDivGroup.hom_ext fun n => BialgHom.ext fun a => ?_` and prove the remaining obligations. Establish `hinj : Function.Injective (fun b : G.A n => (1 : K) ⊗ₜ[R] b)`. Establish `h1 : Function.Injective ((Algebra.linearMap R K).rTensor (G.A n))` using `Module.Flat.rTensor_preserves_injective_linearMap _ hi`. Introduce `x y hxy`. Apply `(TensorProduct.lid R (G.A n)).symm.injective` to reduce the goal to its premises.

Apply `h1` to reduce the goal to its premises. Simplify using `using hxy`. Conclude with `hinj (congrArg (fun u => Hom.app u n ((1 : K) ⊗ₜ[R] a)) h)`.
-/
theorem baseChangeMap_injective (hi : Function.Injective (algebraMap R K)) {G H : PDivGroup p R} {f g : G ⟶ H}
    (h : PDivGroup.baseChangeMap K f = PDivGroup.baseChangeMap K g) : f = g := by
  refine PDivGroup.hom_ext fun n => BialgHom.ext fun a => ?_
  have hinj : Function.Injective (fun b : G.A n => (1 : K) ⊗ₜ[R] b) := by
    have h1 : Function.Injective ((Algebra.linearMap R K).rTensor (G.A n)) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ hi
    intro x y hxy
    apply (TensorProduct.lid R (G.A n)).symm.injective
    apply h1
    simpa using hxy
  exact hinj (congrArg (fun u => Hom.app u n ((1 : K) ⊗ₜ[R] a)) h)

end GlobalTheory.GroupBplus.Aff.Descent

namespace GlobalTheory.GroupBplus.Aff.Descent

variable {p : ℕ} [Fact p.Prime] {R K : Type} [CommRing R] [CommRing K] [Algebra R K]

/- English proof (translation)
The claim follows from `PDivGroup.hom_ext fun n => BialgHom.ext fun x => CartierDual.baseChange_map K (f.app n) x`.
-/
theorem dualBaseChange_hom_naturality {G H : PDivGroup p R} (f : G ⟶ H) :
    (dualBaseChange K H).hom ≫ PDivGroup.baseChangeMap K (dualHom G H f) =
      dualHom _ _ (PDivGroup.baseChangeMap K f) ≫ (dualBaseChange K G).hom :=
  PDivGroup.hom_ext fun n => BialgHom.ext fun x => CartierDual.baseChange_map K (f.app n) x

/- English proof (translation)
Use `PDivGroup.baseChange_hom_ext fun n a => ?_` and prove the remaining obligations. Take `⟨b, rfl⟩` from `(CartierDual.bidual R (G.A n)).surjective a`. Express the relevant statement in the definitionally equal form `(1 : K) ⊗ₜ[R] (CartierDual.bidual R (G.A n)).symm (CartierDual.bidual R (G.A n) b) = _`. Rewrite using `[BialgEquiv.symm_apply_apply]`. Use `symm`.

Express the relevant statement in the definitionally equal form `(CartierDual.bidual K (K ⊗[R] G.A n)).symm _ = _`. Use `CartierDual.eq_of_forall_apply (R := K) fun l => ?_` and prove the remaining obligations. Rewrite using `[CartierDual.apply_bidual_symm]`. Take `⟨y, rfl⟩` from `(CartierDual.baseChange R K (G.A n)).surjective l`. Express the relevant statement in the definitionally equal form `CartierDual.baseChangeHom R K (CartierDual R (G.A n)) ((1 : K) ⊗ₜ[R] CartierDual.bidual R (G.A n) b) ((CartierDual.baseChange R K (G.A n)).symm (CartierDual.baseChange R K (G.A n) y)) = _`.

Rewrite using `[BialgEquiv.symm_apply_apply]`. Express the relevant statement in the definitionally equal form `(CartierDual.baseChangeLinear R K (CartierDual R (G.A n)) ((1 : K) ⊗ₜ[R] CartierDual.bidual R (G.A n) b)).ofConv y = (CartierDual.baseChangeLinear R K (G.A n) y).ofConv ((1 : K) ⊗ₜ[R] b)`. Proceed by induction on `y with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply] at hx hy ⊢`.

Rewrite using `[hx, hy]`. Consider the case `tmul r φ`. Rewrite using `[CartierDual.baseChangeLinear_tmul_tmul, CartierDual.baseChangeLinear_tmul_tmul, CartierDual.bidual_apply]`. Simplify using `[mul_comm]`.
-/
theorem baseChangeMap_bidual_hom (G : PDivGroup p R) :
    PDivGroup.baseChangeMap K G.bidual.hom =
      (G.baseChange K).bidual.hom ≫ dualHom _ _ (dualBaseChange K G).inv ≫ (dualBaseChange K G.dual).hom := by
  refine PDivGroup.baseChange_hom_ext fun n a => ?_
  obtain ⟨b, rfl⟩ := (CartierDual.bidual R (G.A n)).surjective a
  change (1 : K) ⊗ₜ[R] (CartierDual.bidual R (G.A n)).symm (CartierDual.bidual R (G.A n) b) = _
  rw [BialgEquiv.symm_apply_apply]
  symm
  change (CartierDual.bidual K (K ⊗[R] G.A n)).symm _ = _
  refine CartierDual.eq_of_forall_apply (R := K) fun l => ?_
  rw [CartierDual.apply_bidual_symm]
  obtain ⟨y, rfl⟩ := (CartierDual.baseChange R K (G.A n)).surjective l
  change CartierDual.baseChangeHom R K (CartierDual R (G.A n)) ((1 : K) ⊗ₜ[R] CartierDual.bidual R (G.A n) b)
      ((CartierDual.baseChange R K (G.A n)).symm (CartierDual.baseChange R K (G.A n) y)) = _
  rw [BialgEquiv.symm_apply_apply]
  change (CartierDual.baseChangeLinear R K (CartierDual R (G.A n)) ((1 : K) ⊗ₜ[R] CartierDual.bidual R (G.A n) b)).ofConv y =
    (CartierDual.baseChangeLinear R K (G.A n) y).ofConv ((1 : K) ⊗ₜ[R] b)
  induction y with
  | zero => simp
  | add x y hx hy => simp only [map_add, WithConv.ofConv_add, LinearMap.add_apply] at hx hy ⊢; rw [hx, hy]
  | tmul r φ =>
    rw [CartierDual.baseChangeLinear_tmul_tmul, CartierDual.baseChangeLinear_tmul_tmul, CartierDual.bidual_apply]
    simp [mul_comm]

end GlobalTheory.GroupBplus.Aff.Descent

namespace GlobalTheory.GroupBplus.Aff.Descent

/- English proof (translation)
Introduce `E _ _ _ H Dw p _ R K _ _ _ _ _ t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ h₀ GG act pol ε τ e hε hact hpol hτ`. Establish `hi : Function.Injective (algebraMap R K)` using `IsFractionRing.injective R K`. Establish `bc_comp : ∀ {X Y Z : PDivGroup p R} (f : X ⟶ Y) (g : Y ⟶ Z), PDivGroup.baseChangeMap K (f ≫ g) = PDivGroup.baseChangeMap K f ≫ PDivGroup.baseChangeMap K g` using `fun f g => (PDivGroup.baseChangeFunctor p R K).map_comp f g`. Establish `bc_neg : ∀ {X Y : PDivGroup p R} (f : X ⟶ Y), PDivGroup.baseChangeMap K (-f) = -PDivGroup.baseChangeMap K f`. Introduce `X Y f`.

Establish `h0 : PDivGroup.baseChangeMap K (0 : X ⟶ Y) = 0`. Establish `h` using `PDivGroup.baseChangeMap_add K (0 : X ⟶ Y) 0`. Rewrite `h` using `[add_zero]`. Simplify using `using h`. Rewrite using `[eq_neg_iff_add_eq_zero, ← PDivGroup.baseChangeMap_add, neg_add_cancel, h0]`.

Establish `hinv : ∀ a, e.inv ≫ (act₀ a : GG₀ ⟶ GG₀) = PDivGroup.baseChangeMap K (act a : GG ⟶ GG) ≫ e.inv` using `fun a => by`. Rewrite using `[Iso.eq_comp_inv, Category.assoc, hact, Iso.inv_hom_id_assoc]`. Establish `tate_inj : ∀ s s' : GG.Tate, bcTate K s = bcTate K s' → s = s'` using `fun s s' h => TateOver.ext (funext fun n => AlgHom.ext fun a => hi (by`. Establish `h1` using `congrArg (fun z => z.pt n ((1 : K) ⊗ₜ[R] a)) h`. Conclude with `(_root_.one_mul _).symm.trans (h1.trans (_root_.one_mul _))))`.

Use `⟨fun a => ?_, ?_, fun n => ?_, fun a x => ?_, fun x y => ?_⟩` and prove the remaining obligations. Apply `baseChangeMap_injective hi` to reduce the goal to its premises. Rewrite using `[← cancel_epi e.hom, bc_comp, bc_comp]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Category.assoc, ← hact, Category.assoc]`.

Use `_ = (act₀ a : GG₀ ⟶ GG₀) ≫ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by rw [hpol]`. Use `_ = pol₀.hom ≫ dualHom _ _ (act₀ (H.bar a)) ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by`. Rewrite using `[← Category.assoc, h₀.adj a, Category.assoc]`. Use `_ = pol₀.hom ≫ dualHom _ _ (e.inv ≫ (act₀ (H.bar a) : GG₀ ⟶ GG₀)) ≫ (dualBaseChange K GG).hom := by`. Rewrite using `[dualHom_comp, Category.assoc]`.

Use `_ = pol₀.hom ≫ dualHom _ _ (PDivGroup.baseChangeMap K (act (H.bar a) : GG ⟶ GG) ≫ e.inv) ≫ (dualBaseChange K GG).hom := by rw [hinv]`. Use `_ = pol₀.hom ≫ dualHom _ _ e.inv ≫ dualHom _ _ (PDivGroup.baseChangeMap K (act (H.bar a) : GG ⟶ GG)) ≫ (dualBaseChange K GG).hom := by rw [dualHom_comp, Category.assoc]`. Use `_ = pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom ≫ PDivGroup.baseChangeMap K (dualHom GG GG (act (H.bar a))) := by rw [dualBaseChange_hom_naturality]`. Use `_ = e.hom ≫ PDivGroup.baseChangeMap K pol.hom ≫ PDivGroup.baseChangeMap K (dualHom GG GG (act (H.bar a))) := by`. Rewrite using `[← Category.assoc e.hom, ← hpol]`.

Simplify using `only [Category.assoc]`. Apply `baseChangeMap_injective hi` to reduce the goal to its premises. Establish `hp' : PDivGroup.baseChangeMap K pol.hom ≫ (dualBaseChange K GG).inv = e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv`. Rewrite using `[← cancel_epi e.hom, ← Category.assoc, ← hpol]`. Simplify using `only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]`.

Rewrite using `[← cancel_epi e.hom, bc_comp, bc_neg, Preadditive.comp_neg, ← hpol]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[baseChangeMap_bidual_hom]`. Simplify using `only [Category.assoc]`. Use `_ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (dualBaseChange K GG).inv ≫ dualHom _ _ (PDivGroup.baseChangeMap K pol.hom) ≫ (dualBaseChange K GG).hom := by`.

Rewrite using `[dualBaseChange_hom_naturality]`. Use `_ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (PDivGroup.baseChangeMap K pol.hom ≫ (dualBaseChange K GG).inv) ≫ (dualBaseChange K GG).hom := by`. Rewrite using `[dualHom_comp, Category.assoc]`. Use `_ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv) ≫ (dualBaseChange K GG).hom := by rw [hp']`. Use `_ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (dualHom _ _ e.inv) ≫ dualHom _ _ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by`.

Rewrite using `[dualHom_comp, dualHom_comp]`. Simplify using `only [Category.assoc]`. Use `_ = GG₀.bidual.hom ≫ dualHom _ _ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by`. Rewrite using `[← Category.assoc (PDivGroup.bidual _).hom, bidual_hom_dualHom_dualHom]`. Simplify using `only [Category.assoc, Iso.hom_inv_id_assoc]`.

Use `_ = -pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by`. Rewrite using `[← Category.assoc, h₀.skew, Preadditive.neg_comp]`. Conclude with `(IsPrimitiveRoot.map_iff_of_injective hi).1 (by rw [← hε]; exact h₀.prim n)`. Apply `tate_inj` to reduce the goal to its premises. Rewrite using `[← hτ, h₀.lin, ← tateMap_comp, hact, tateMap_comp, hτ, tateMap_bcTate]`.

Use `muRoot_ext fun n => hi ?_` and prove the remaining obligations. Rewrite using `[← muRoot_pairing_bc, muRoot_smul, map_pow, ← hε, ← muRoot_smul, ← h₀.pair, ← hτ, pairing_tateMap]`. Use `congr 2`. Establish `h1 : tateMap _ _ K (dualBaseChange K GG).hom (bcChar K (tateMap GG GG.dual R pol.hom (τ y))) = tateMap _ _ K (dualBaseChange K GG).hom (tateMap _ _ K (pol₀.hom ≫ dualHom _ _ e.inv) (τ₀ y))`. Rewrite using `[tateMap_dualBaseChange, ← tateMap_bcTate, ← hτ, ← tateMap_comp, ← tateMap_comp, Category.assoc, hpol]`.

Establish `h2` using `congrArg (tateMap _ _ K (dualBaseChange K GG).inv) h1`. Rewrite `h2` using `[← tateMap_comp, ← tateMap_comp, Iso.hom_inv_id, tateMap_id, tateMap_id]`. Rewrite using `[h2, ← tateMap_comp, Category.assoc, ← dualHom_comp, Iso.hom_inv_id, dualHom_id, Category.comp_id]`.
-/
theorem descends : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (p : ℕ) [Fact p.Prime] (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (t₀ : SAB H (Sp K)) (GG₀ : PDivGroup p K) (act₀ : Action (𝓞 E) GG₀) (pol₀ : GG₀ ≅ GG₀.dual) (θ₀ : TorsionMap t₀.G GG₀) (ε₀ : (PDivGroup.mu p K).Tate) (τ₀ : Dw.La →+ GG₀.Tate), IsPropG Dw t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ → ∀ (GG : PDivGroup p R) (act : Action (𝓞 E) GG) (pol : GG ≅ GG.dual) (ε : (PDivGroup.mu p R).Tate) (τ : Dw.La →+ GG.Tate) (e : GG₀ ≅ GG.baseChange K), (∀ n, muRoot ε₀ n = algebraMap R K (muRoot ε n)) → (∀ a, (act₀ a : GG₀ ⟶ GG₀) ≫ e.hom = e.hom ≫ PDivGroup.baseChangeMap K (act a : GG ⟶ GG)) → pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom = e.hom ≫ PDivGroup.baseChangeMap K pol.hom → (∀ x, tateMap _ _ K e.hom (τ₀ x) = bcTate K (τ x)) → (∀ a, (act a : GG ⟶ GG) ≫ pol.hom = pol.hom ≫ dualHom GG GG (act (H.bar a))) ∧ GG.bidual.hom ≫ dualHom GG GG.dual pol.hom = -pol.hom ∧ (∀ n, IsPrimitiveRoot (muRoot ε n) (p ^ n)) ∧ (∀ (a : 𝓞 E) (x : Dw.La), τ (a • x) = tateMap GG GG R (act a) (τ x)) ∧ ∀ x y, pairing GG R (τ x) (tateMap GG GG.dual R pol.hom (τ y)) = ((Dw.EF x y : ℤ) : ℤ_[p]) • ε := by
  intro E _ _ _ H Dw p _ R K _ _ _ _ _ t₀ GG₀ act₀ pol₀ θ₀ ε₀ τ₀ h₀ GG act pol ε τ e hε hact hpol hτ
  have hi : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have bc_comp : ∀ {X Y Z : PDivGroup p R} (f : X ⟶ Y) (g : Y ⟶ Z),
      PDivGroup.baseChangeMap K (f ≫ g) = PDivGroup.baseChangeMap K f ≫ PDivGroup.baseChangeMap K g :=
    fun f g => (PDivGroup.baseChangeFunctor p R K).map_comp f g
  have bc_neg : ∀ {X Y : PDivGroup p R} (f : X ⟶ Y), PDivGroup.baseChangeMap K (-f) = -PDivGroup.baseChangeMap K f := by
    intro X Y f
    have h0 : PDivGroup.baseChangeMap K (0 : X ⟶ Y) = 0 := by
      have h := PDivGroup.baseChangeMap_add K (0 : X ⟶ Y) 0
      rw [add_zero] at h
      simpa using h
    rw [eq_neg_iff_add_eq_zero, ← PDivGroup.baseChangeMap_add, neg_add_cancel, h0]
  have hinv : ∀ a, e.inv ≫ (act₀ a : GG₀ ⟶ GG₀) = PDivGroup.baseChangeMap K (act a : GG ⟶ GG) ≫ e.inv := fun a => by
    rw [Iso.eq_comp_inv, Category.assoc, hact, Iso.inv_hom_id_assoc]
  have tate_inj : ∀ s s' : GG.Tate, bcTate K s = bcTate K s' → s = s' := fun s s' h =>
    TateOver.ext (funext fun n => AlgHom.ext fun a => hi (by
      have h1 := congrArg (fun z => z.pt n ((1 : K) ⊗ₜ[R] a)) h
      exact (_root_.one_mul _).symm.trans (h1.trans (_root_.one_mul _))))
  refine ⟨fun a => ?_, ?_, fun n => ?_, fun a x => ?_, fun x y => ?_⟩
  ·
    apply baseChangeMap_injective hi
    rw [← cancel_epi e.hom, bc_comp, bc_comp]
    calc e.hom ≫ PDivGroup.baseChangeMap K (act a : GG ⟶ GG) ≫ PDivGroup.baseChangeMap K pol.hom
        = (act₀ a : GG₀ ⟶ GG₀) ≫ e.hom ≫ PDivGroup.baseChangeMap K pol.hom := by
          rw [← Category.assoc, ← hact, Category.assoc]
      _ = (act₀ a : GG₀ ⟶ GG₀) ≫ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by rw [hpol]
      _ = pol₀.hom ≫ dualHom _ _ (act₀ (H.bar a)) ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by
          rw [← Category.assoc, h₀.adj a, Category.assoc]
      _ = pol₀.hom ≫ dualHom _ _ (e.inv ≫ (act₀ (H.bar a) : GG₀ ⟶ GG₀)) ≫ (dualBaseChange K GG).hom := by
          rw [dualHom_comp, Category.assoc]
      _ = pol₀.hom ≫ dualHom _ _ (PDivGroup.baseChangeMap K (act (H.bar a) : GG ⟶ GG) ≫ e.inv) ≫
            (dualBaseChange K GG).hom := by rw [hinv]
      _ = pol₀.hom ≫ dualHom _ _ e.inv ≫ dualHom _ _ (PDivGroup.baseChangeMap K (act (H.bar a) : GG ⟶ GG)) ≫
            (dualBaseChange K GG).hom := by rw [dualHom_comp, Category.assoc]
      _ = pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom ≫
            PDivGroup.baseChangeMap K (dualHom GG GG (act (H.bar a))) := by rw [dualBaseChange_hom_naturality]
      _ = e.hom ≫ PDivGroup.baseChangeMap K pol.hom ≫ PDivGroup.baseChangeMap K (dualHom GG GG (act (H.bar a))) := by
          rw [← Category.assoc e.hom, ← hpol]; simp only [Category.assoc]
  ·
    apply baseChangeMap_injective hi
    have hp' : PDivGroup.baseChangeMap K pol.hom ≫ (dualBaseChange K GG).inv = e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv := by
      rw [← cancel_epi e.hom, ← Category.assoc, ← hpol]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
    rw [← cancel_epi e.hom, bc_comp, bc_neg, Preadditive.comp_neg, ← hpol]
    calc e.hom ≫ PDivGroup.baseChangeMap K GG.bidual.hom ≫ PDivGroup.baseChangeMap K (dualHom GG GG.dual pol.hom)
        = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (dualBaseChange K GG).inv ≫
            (dualBaseChange K GG.dual).hom ≫ PDivGroup.baseChangeMap K (dualHom GG GG.dual pol.hom) := by
          rw [baseChangeMap_bidual_hom]; simp only [Category.assoc]
      _ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (dualBaseChange K GG).inv ≫
            dualHom _ _ (PDivGroup.baseChangeMap K pol.hom) ≫ (dualBaseChange K GG).hom := by
          rw [dualBaseChange_hom_naturality]
      _ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫
            dualHom _ _ (PDivGroup.baseChangeMap K pol.hom ≫ (dualBaseChange K GG).inv) ≫ (dualBaseChange K GG).hom := by
          rw [dualHom_comp, Category.assoc]
      _ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (e.inv ≫ pol₀.hom ≫ dualHom _ _ e.inv) ≫
            (dualBaseChange K GG).hom := by rw [hp']
      _ = e.hom ≫ (PDivGroup.baseChange K GG).bidual.hom ≫ dualHom _ _ (dualHom _ _ e.inv) ≫ dualHom _ _ pol₀.hom ≫
            dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by
          rw [dualHom_comp, dualHom_comp]; simp only [Category.assoc]
      _ = GG₀.bidual.hom ≫ dualHom _ _ pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by
          rw [← Category.assoc (PDivGroup.bidual _).hom, bidual_hom_dualHom_dualHom]
          simp only [Category.assoc, Iso.hom_inv_id_assoc]
      _ = -pol₀.hom ≫ dualHom _ _ e.inv ≫ (dualBaseChange K GG).hom := by
          rw [← Category.assoc, h₀.skew, Preadditive.neg_comp]
  ·
    exact (IsPrimitiveRoot.map_iff_of_injective hi).1 (by rw [← hε]; exact h₀.prim n)
  ·
    apply tate_inj
    rw [← hτ, h₀.lin, ← tateMap_comp, hact, tateMap_comp, hτ, tateMap_bcTate]
  ·
    refine muRoot_ext fun n => hi ?_
    rw [← muRoot_pairing_bc, muRoot_smul, map_pow, ← hε, ← muRoot_smul, ← h₀.pair, ← hτ, pairing_tateMap]
    congr 2
    have h1 : tateMap _ _ K (dualBaseChange K GG).hom (bcChar K (tateMap GG GG.dual R pol.hom (τ y))) =
        tateMap _ _ K (dualBaseChange K GG).hom (tateMap _ _ K (pol₀.hom ≫ dualHom _ _ e.inv) (τ₀ y)) := by
      rw [tateMap_dualBaseChange, ← tateMap_bcTate, ← hτ, ← tateMap_comp, ← tateMap_comp, Category.assoc, hpol]
    have h2 := congrArg (tateMap _ _ K (dualBaseChange K GG).inv) h1
    rw [← tateMap_comp, ← tateMap_comp, Iso.hom_inv_id, tateMap_id, tateMap_id] at h2
    rw [h2, ← tateMap_comp, Category.assoc, ← dualHom_comp, Iso.hom_inv_id, dualHom_id, Category.comp_id]

end GlobalTheory.GroupBplus.Aff.Descent
