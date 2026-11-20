import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.AbLaw.Seesaw

/- English proof (translation)
Take `⟨L, hL⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) (LinearMap.ker_eq_bot'.2 fun w hw => hA w (by simpa using hw))`. Establish `h1 : LinearMap.toMatrix' L * A = 1`. Use `congrArg LinearMap.toMatrix' hL` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]`. Then use the resulting hypothesis. Assume the negation of the conclusion as `hne`.

Use `push Not at hne`. Use `set B := LinearMap.toMatrix' L`. Establish `h2 : (B * A).det = ∑ ρ : n → m, (∏ i, B i (ρ i)) * (A.submatrix ρ id).det`. Establish `e : B * A = fun i => ∑ j, B i j • A j`. Use extensionality with `i k`.

Simplify using `[Matrix.mul_apply, Finset.sum_apply]`. Use `(Matrix.detRowAlternating (n := n) (R := K)).toMultilinearMap.map_sum (fun i j => B i j • A j)` as an intermediate fact. Rewrite using `[e]`. Use `this.trans (Finset.sum_congr rfl fun ρ _ => ?_)` and prove the remaining obligations. Conclude with `(Matrix.detRowAlternating (n := n) (R := K)).toMultilinearMap.map_smul_univ _ _`.

Rewrite `h2` using `[h1, Matrix.det_one]`. Simplify using `[hne] at h2`.
-/
theorem exists_minor {K m n : Type} [Field K] [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n K)
    (hA : ∀ w, A.mulVec w = 0 → w = 0) : ∃ ρ : n → m, (A.submatrix ρ id).det ≠ 0 := by
  classical
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A)
    (LinearMap.ker_eq_bot'.2 fun w hw => hA w (by simpa using hw))
  have h1 : LinearMap.toMatrix' L * A = 1 := by
    have := congrArg LinearMap.toMatrix' hL
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  by_contra hne
  push Not at hne
  set B := LinearMap.toMatrix' L
  have h2 : (B * A).det = ∑ ρ : n → m, (∏ i, B i (ρ i)) * (A.submatrix ρ id).det := by
    have e : B * A = fun i => ∑ j, B i j • A j := by
      ext i k
      simp [Matrix.mul_apply, Finset.sum_apply]
    have := (Matrix.detRowAlternating (n := n) (R := K)).toMultilinearMap.map_sum
      (fun i j => B i j • A j)
    rw [e]
    refine this.trans (Finset.sum_congr rfl fun ρ _ => ?_)
    exact (Matrix.detRowAlternating (n := n) (R := K)).toMultilinearMap.map_smul_univ _ _
  rw [h1, Matrix.det_one] at h2
  simp [hne] at h2

/- English proof (translation)
Take `⟨k, hk⟩` from `Function.ne_iff.1 hv`. Set `D' : Matrix (Option (Fin b)) (Fin a) R` to `fun i => i.elim (Pi.single k 1) D`. Establish `key : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (w : Fin a → R'), (D.map g).mulVec w = 0 → (D'.map g).mulVec w = fun i => w k * g (i.elim 1 fun _ => 0)`. Introduce `R' _ g w hw`. Use function extensionality and compare the values at `i`.

Consider the cases of `i with`. Consider the case `none`. Express the relevant statement in the definitionally equal form `∑ x, g ((Pi.single k 1 : Fin a → R) x) * w x = w k * g 1`. Simplify using `[Pi.single_apply, apply_ite g]`. Consider the case `some i`.

Conclude with `(congrFun hw i).trans ((congrArg (w k * ·) (map_zero g)).trans (mul_zero _)).symm`. Take `⟨ρ, hρ⟩` from `exists_minor (D'.map g₀) (fun w hw => by`. Establish `h₁ : (D.map g₀).mulVec w = 0` using `funext fun i => congrFun hw (some i)`. Establish `h₂` using `congrFun ((key K g₀ w h₁).symm.trans hw) none`. Take `⟨c, rfl⟩` from `hker w h₁`.

Establish `: c = 0` using `by simpa [show v k ≠ 0 from hk] using h₂`. Simplify using `[this])`. Set `N` to `D'.submatrix ρ id`. Set `e : Fin a → R` to `fun j => (ρ j).elim 1 fun _ => 0`. Use `⟨N.det, N.adjugate.mulVec e, by rwa [RingHom.map_det], fun R' _ g hδ w hw => ?_⟩` and prove the remaining obligations.

Take `⟨u, hu⟩` from `hδ`. Establish `h₁ : (N.map g).mulVec w = w k • (g ∘ e)` using `funext fun j => congrFun (key R' g w hw) (ρ j)`. Establish `h₂ : g ∘ N.adjugate.mulVec e = (N.map g).adjugate.mulVec (g ∘ e)`. Use function extensionality and compare the values at `j`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]`.

Conclude with `RingHom.map_mulVec g _ _ j`. Establish `h₃` using `congrArg (N.map g).adjugate.mulVec h₁`. Rewrite `h₃` using `[Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_smul, ← h₂, Matrix.smul_mulVec, Matrix.one_mulVec, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← hu]`. Use `⟨u⁻¹.val * w k, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← h₃, smul_smul, Units.inv_mul, one_smul]`.
-/
theorem exists_kernel_vector {R K : Type} [CommRing R] [Field K] (g₀ : R →+* K) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) (v : Fin a → K) (hv : v ≠ 0)
    (hker : ∀ w, (D.map g₀).mulVec w = 0 → ∃ c : K, w = c • v) :
    ∃ (δ : R) (v₀ : Fin a → R), g₀ δ ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g δ) →
      ∀ w, (D.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀) := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
  let D' : Matrix (Option (Fin b)) (Fin a) R := fun i => i.elim (Pi.single k 1) D
  have key : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (w : Fin a → R'), (D.map g).mulVec w = 0 →
      (D'.map g).mulVec w = fun i => w k * g (i.elim 1 fun _ => 0) := by
    intro R' _ g w hw
    funext i
    cases i with
    | none =>
      change ∑ x, g ((Pi.single k 1 : Fin a → R) x) * w x = w k * g 1
      simp [Pi.single_apply, apply_ite g]
    | some i =>
      exact (congrFun hw i).trans ((congrArg (w k * ·) (map_zero g)).trans (mul_zero _)).symm
  obtain ⟨ρ, hρ⟩ := exists_minor (D'.map g₀) (fun w hw => by
    have h₁ : (D.map g₀).mulVec w = 0 := funext fun i => congrFun hw (some i)
    have h₂ := congrFun ((key K g₀ w h₁).symm.trans hw) none
    obtain ⟨c, rfl⟩ := hker w h₁
    have : c = 0 := by simpa [show v k ≠ 0 from hk] using h₂
    simp [this])
  let N := D'.submatrix ρ id
  let e : Fin a → R := fun j => (ρ j).elim 1 fun _ => 0
  refine ⟨N.det, N.adjugate.mulVec e, by rwa [RingHom.map_det], fun R' _ g hδ w hw => ?_⟩
  obtain ⟨u, hu⟩ := hδ
  have h₁ : (N.map g).mulVec w = w k • (g ∘ e) := funext fun j => congrFun (key R' g w hw) (ρ j)
  have h₂ : g ∘ N.adjugate.mulVec e = (N.map g).adjugate.mulVec (g ∘ e) := by
    funext j
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    exact RingHom.map_mulVec g _ _ j
  have h₃ := congrArg (N.map g).adjugate.mulVec h₁
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_smul, ← h₂, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← hu] at h₃
  refine ⟨u⁻¹.val * w k, ?_⟩
  rw [mul_smul, ← h₃, smul_smul, Units.inv_mul, one_smul]

variable {X X' Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

/- English proof (translation)
Use `Y.basicOpen_res a (homOfLE h).op` as an intermediate fact. Conclude with `(congrArg (y ∈ ·) this).to_iff.trans ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩`.
-/
theorem mem_basicOpen_rs {U V : Y.Opens} (h : V ≤ U) (a : Γ(Y, U)) {y : Y} (hy : y ∈ V) :
    y ∈ Y.basicOpen (rs Y h a) ↔ y ∈ Y.basicOpen a := by
  have := Y.basicOpen_res a (homOfLE h).op
  exact (congrArg (y ∈ ·) this).to_iff.trans ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩

/- English proof (translation)
The claim follows from `Y.toRingedSpace.isUnit_of_isUnit_germ U a fun y hy => (Y.mem_basicOpen a y hy).1 (h y hy)`.
-/
theorem isUnit_of_basicOpen {U : Y.Opens} (a : Γ(Y, U)) (h : ∀ y ∈ U, y ∈ Y.basicOpen a) : IsUnit a :=
  Y.toRingedSpace.isUnit_of_isUnit_germ U a fun y hy => (Y.mem_basicOpen a y hy).1 (h y hy)

/- English proof (translation)
Rewrite using `[Y.basicOpen_of_isUnit h]` and apply the resulting hypothesis.
-/
theorem mem_of_isUnit {U : Y.Opens} {a : Γ(Y, U)} (h : IsUnit a) {y : Y} (hy : y ∈ U) : y ∈ Y.basicOpen a := by
  rwa [Y.basicOpen_of_isUnit h]

/- English proof (translation)
Establish `hj : y ∈ N.U j` using `Y.basicOpen_le _ h`. Establish `hij : y ∈ N.U i ⊓ N.U j` using `⟨hi, hj⟩`. Rewrite using `[← mem_basicOpen_rs inf_le_left _ hij, s.compat i j, Scheme.basicOpen_mul]`. Conclude with `⟨mem_of_isUnit (Units.isUnit _) hij, (mem_basicOpen_rs inf_le_right _ hij).2 h⟩`.
-/
theorem sec_basicOpen {N : LB Y} (s : LB.Sec N) {i j : N.ι} {y : Y} (hi : y ∈ N.U i)
    (h : y ∈ Y.basicOpen (s.f j)) : y ∈ Y.basicOpen (s.f i) := by
  have hj : y ∈ N.U j := Y.basicOpen_le _ h
  have hij : y ∈ N.U i ⊓ N.U j := ⟨hi, hj⟩
  rw [← mem_basicOpen_rs inf_le_left _ hij, s.compat i j, Scheme.basicOpen_mul]
  exact ⟨mem_of_isUnit (Units.isUnit _) hij, (mem_basicOpen_rs inf_le_right _ hij).2 h⟩

/- English proof (translation)
Establish `: s.f = s'.f` using `funext fun j => by`. Use `Y.sheaf.eq_of_locally_eq' (fun i => N.U j ⊓ V i) (N.U j) (fun i => homOfLE inf_le_left) (fun y hy => ?_) _ _ fun i => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `hV y`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hi⟩`. Establish `l : N.U j ⊓ V i ≤ N.U j ⊓ N.U (c i)` using `inf_le_inf_left _ (le i)`.

Establish `e₁` using `congrArg (rs Y l) (s.compat j (c i))`. Establish `e₂` using `congrArg (rs Y l) (s'.compat j (c i))`. Establish `e₃` using `congrArg (rs Y (inf_le_right : N.U j ⊓ V i ≤ V i)) (h i)`. Simplify using `only [map_mul, rs_rs] at e₁ e₂ e₃`. Express the relevant statement in the definitionally equal form `rs Y _ (s.f j) = rs Y _ (s'.f j)`.

Rewrite using `[e₁, e₂, e₃]`. Take `⟨f, _⟩` from `s`. Take `⟨f', _⟩` from `s'`. Take `rfl : f = f'` from `this`. Both sides reduce to the same expression.
-/
theorem sec_ext {N : LB Y} (s s' : LB.Sec N) {I : Type} (V : I → Y.Opens) (c : I → N.ι)
    (le : ∀ i, V i ≤ N.U (c i)) (hV : ∀ y, ∃ i, y ∈ V i)
    (h : ∀ i, rs Y (le i) (s.f (c i)) = rs Y (le i) (s'.f (c i))) : s = s' := by
  have : s.f = s'.f := funext fun j => by
    refine Y.sheaf.eq_of_locally_eq' (fun i => N.U j ⊓ V i) (N.U j) (fun i => homOfLE inf_le_left)
      (fun y hy => ?_) _ _ fun i => ?_
    · obtain ⟨i, hi⟩ := hV y
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hi⟩
    · have l : N.U j ⊓ V i ≤ N.U j ⊓ N.U (c i) := inf_le_inf_left _ (le i)
      have e₁ := congrArg (rs Y l) (s.compat j (c i))
      have e₂ := congrArg (rs Y l) (s'.compat j (c i))
      have e₃ := congrArg (rs Y (inf_le_right : N.U j ⊓ V i ≤ V i)) (h i)
      simp only [map_mul, rs_rs] at e₁ e₂ e₃
      change rs Y _ (s.f j) = rs Y _ (s'.f j)
      rw [e₁, e₂, e₃]
  obtain ⟨f, _⟩ := s
  obtain ⟨f', _⟩ := s'
  obtain rfl : f = f' := this
  rfl

/- English proof (translation)
Take `⟨ρ, hρ⟩` from `TLinPf.glue N.U hc (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by`. Establish `e` using `congrArg (·⁻¹) (ht i j)`. Simplify using `only [mul_inv, ← map_inv] at e`. Establish `e' : rs Y (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) ((t.s i)⁻¹).val = ((N.g i j)⁻¹).val * rs Y (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) ((t.s j)⁻¹).val` using `congrArg Units.val e`. Rewrite using `[map_mul, map_mul, s.compat i j, e', _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul])`.

Use `⟨ρ, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hρ j, Units.inv_mul_cancel_right]`.
-/
theorem sec_ratio {N : LB Y} (hc : ⨆ j, N.U j = ⊤) (s : LB.Sec N) (t : LB.Gen N) (ht : t.IsGen) :
    ∃ ρ : Γ(Y, ⊤), ∀ j, s.f j = rs Y le_top ρ * (t.s j).val := by
  obtain ⟨ρ, hρ⟩ := TLinPf.glue N.U hc (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e := congrArg (·⁻¹) (ht i j)
    simp only [mul_inv, ← map_inv] at e
    have e' : rs Y (inf_le_left : N.U i ⊓ N.U j ≤ N.U i) ((t.s i)⁻¹).val =
      ((N.g i j)⁻¹).val * rs Y (inf_le_right : N.U i ⊓ N.U j ≤ N.U j) ((t.s j)⁻¹).val := congrArg Units.val e
    rw [map_mul, map_mul, s.compat i j, e', _root_.mul_mul_mul_comm, Units.mul_inv, _root_.one_mul])
  refine ⟨ρ, fun j => ?_⟩
  rw [hρ j, Units.inv_mul_cancel_right]

/- English proof (translation)
Establish `e₁` using `congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))`. Establish `e₂` using `congrArg (fun q => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) w`. Establish `e₃` using `congrArg (fun q => q.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) (π.naturality (homOfLE (le_top : W ≤ ⊤)).op)`. Simplify using `only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₁ e₂ e₃`. Use `e₃.trans ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `rs X' le_top (π.appTop.hom _) = rs X' le_top (f'.appTop.hom _)`. Rewrite using `[e₂, ← e₁]`.
-/
theorem app_cst {f : X ⟶ Spec (CommRingCat.of R)} {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
    (w : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) (W : X.Opens) (r : R) :
    (π.app W).hom (cst f W r) = cst f' (π ⁻¹ᵁ W) (g r) := by
  have e₁ := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  have e₂ := congrArg (fun q => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) w
  have e₃ := congrArg (fun q => q.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)))
    (π.naturality (homOfLE (le_top : W ≤ ⊤)).op)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₁ e₂ e₃
  refine e₃.trans ?_
  change rs X' le_top (π.appTop.hom _) = rs X' le_top (f'.appTop.hom _)
  rw [e₂, ← e₁]

/- English proof (translation)
Use `(mem_basicOpen_rs le_top _ hx).trans ?_` and prove the remaining obligations. Establish `e₁` using `f.preimage_basicOpen_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)`. Establish `e₂` using `basicOpen_eq_of_affine (R := CommRingCat.of R) r`. Use `(congrArg (x ∈ ·) e₁).to_iff.symm.trans ?_` and prove the remaining obligations. Conclude with `(congrArg (f x ∈ ·) e₂).to_iff`.
-/
theorem mem_basicOpen_cst (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : R) {x : X} (hx : x ∈ W) :
    x ∈ X.basicOpen (cst f W r) ↔ r ∉ (f x).asIdeal := by
  refine (mem_basicOpen_rs le_top _ hx).trans ?_
  have e₁ := f.preimage_basicOpen_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have e₂ := basicOpen_eq_of_affine (R := CommRingCat.of R) r
  refine (congrArg (x ∈ ·) e₁).to_iff.symm.trans ?_
  exact (congrArg (f x ∈ ·) e₂).to_iff

section
variable {f : X ⟶ Spec (CommRingCat.of R)} {M : LB X} (P : Perf f M)

def loc (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')) (v : Fin P.a → R') (i : P.I) : Γ(X', π ⁻¹ᵁ P.W i) :=
  ∑ k, cst f' (π ⁻¹ᵁ P.W i) (v k) * (π.app (P.W i)).hom (P.u k i)

def loc₀ (v : Fin P.a → R) (i : P.I) : Γ(X, P.W i) := ∑ k, cst f (P.W i) (v k) * P.u k i

/- English proof (translation)
Simplify using `only [loc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]`.
-/
theorem loc_smul (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')) (c : R') (v : Fin P.a → R') (i : P.I) :
    loc P π f' (c • v) i = cst f' _ c * loc P π f' v i := by
  simp only [loc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, _root_.mul_assoc]

/- English proof (translation)
The claim follows from `TopologicalSpace.Opens.mem_iSup.1 (P.cover.ge (Set.mem_univ x))`.
-/
theorem exists_mem (x : X) : ∃ i, x ∈ P.W i :=
  TopologicalSpace.Opens.mem_iSup.1 (P.cover.ge (Set.mem_univ x))

variable {g : R →+* R'} {π : X' ⟶ X} {f' : X' ⟶ Spec (CommRingCat.of R')}
  (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
include h

/- English proof (translation)
Simplify using `only [loc, loc₀, map_sum, map_mul, app_cst h.w, Function.comp_apply]`.
-/
theorem loc_comp (v : Fin P.a → R) (i : P.I) : loc P π f' (g ∘ v) i = (π.app (P.W i)).hom (loc₀ P v i) := by
  simp only [loc, loc₀, map_sum, map_mul, app_cst h.w, Function.comp_apply]

/- English proof (translation)
Take `⟨E, hE⟩` from `P.sec R' g X' π f' h`. Establish `hu : ∀ j, IsUnit ((E ⟨v, hv⟩).f j)` using `fun j => isUnit_of_basicOpen _ fun y hy => by`. Take `⟨i, hi⟩` from `H y`. Use `sec_basicOpen (E ⟨v, hv⟩) (j := fun _ => P.ch i) hy ?_` and prove the remaining obligations. Rewrite using `[← mem_basicOpen_rs (le_pull M π (P.le i)) _ (X'.basicOpen_le _ hi), hE]`.

Conclude with `hi`. Conclude with `⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext ((E ⟨v, hv⟩).compat i j)⟩`.
-/
theorem triv_of_loc (v : Fin P.a → R') (hv : (P.D₀.map g).mulVec v = 0)
    (H : ∀ y : X', ∃ i, y ∈ X'.basicOpen (loc P π f' v i)) : Triv (M.pull π) := by
  obtain ⟨E, hE⟩ := P.sec R' g X' π f' h
  have hu : ∀ j, IsUnit ((E ⟨v, hv⟩).f j) := fun j => isUnit_of_basicOpen _ fun y hy => by
    obtain ⟨i, hi⟩ := H y
    refine sec_basicOpen (E ⟨v, hv⟩) (j := fun _ => P.ch i) hy ?_
    rw [← mem_basicOpen_rs (le_pull M π (P.le i)) _ (X'.basicOpen_le _ hi), hE]
    exact hi
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext ((E ⟨v, hv⟩).compat i j)⟩

/- English proof (translation)
Take `⟨E, hE⟩` from `P.sec R' g X' π f' h`. Take `⟨t, ht⟩` from `H`. Set `s : LB.Sec (M.pull π)` to `⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩`. Take `⟨v, hv⟩` from `E.surjective s`. Establish `e : ∀ i, loc P π f' v.1 i = rs X' (le_pull M π (P.le i)) (t.s fun _ => P.ch i).val` using `fun i => by`.

Use `(hE v i).symm.trans ?_` and prove the remaining obligations. Rewrite using `[hv]`. Use `⟨v.1, v.2, fun i => by rw [e]; exact (Units.isUnit _).map _, fun hs w hw => ?_⟩` and prove the remaining obligations. Take `⟨ρ, hρ⟩` from `sec_ratio (TLinPf.linComb_cover M hM _ _) (E ⟨w, hw⟩) t ht`. Take `⟨c', rfl⟩` from `hs ρ`.

Take `⟨c, rfl⟩` from `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).2 c'`. Establish `hc : (P.D₀.map g).mulVec (c • v.1) = 0` using `by rw [Matrix.mulVec_smul, v.2, smul_zero]`. Use `⟨c, congrArg Subtype.val (E.injective (a₁ := ⟨w, hw⟩) (a₂ := ⟨c • v.1, hc⟩) ?_)⟩` and prove the remaining obligations. Use `sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M π (P.le i)) (fun y => exists_mem P (π y)) fun i => ?_` and prove the remaining obligations. Use `Eq.trans ?_ ((hE ⟨c • v.1, hc⟩ i).trans (loc_smul P π f' c v.1 i)).symm` and prove the remaining obligations.

Conclude with `(congrArg _ (hρ _)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (rs_rs _ _ _) (e i).symm))`.
-/
theorem loc_of_triv (hM : M.IsLB) (H : Triv (M.pull π)) : ∃ v : Fin P.a → R', (P.D₀.map g).mulVec v = 0 ∧
    (∀ i, IsUnit (loc P π f' v i)) ∧ (Function.Surjective f'.appTop.hom →
      ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : R', w = c • v) := by
  obtain ⟨E, hE⟩ := P.sec R' g X' π f' h
  obtain ⟨t, ht⟩ := H
  let s : LB.Sec (M.pull π) := ⟨fun i => (t.s i).val, fun i j => congrArg Units.val (ht i j)⟩
  obtain ⟨v, hv⟩ := E.surjective s
  have e : ∀ i, loc P π f' v.1 i = rs X' (le_pull M π (P.le i)) (t.s fun _ => P.ch i).val := fun i => by
    refine (hE v i).symm.trans ?_
    rw [hv]
  refine ⟨v.1, v.2, fun i => by rw [e]; exact (Units.isUnit _).map _, fun hs w hw => ?_⟩
  obtain ⟨ρ, hρ⟩ := sec_ratio (TLinPf.linComb_cover M hM _ _) (E ⟨w, hw⟩) t ht
  obtain ⟨c', rfl⟩ := hs ρ
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R')).inv).2 c'
  have hc : (P.D₀.map g).mulVec (c • v.1) = 0 := by rw [Matrix.mulVec_smul, v.2, smul_zero]
  refine ⟨c, congrArg Subtype.val (E.injective (a₁ := ⟨w, hw⟩) (a₂ := ⟨c • v.1, hc⟩) ?_)⟩
  refine sec_ext _ _ (fun i => π ⁻¹ᵁ P.W i) (fun i _ => P.ch i) (fun i => le_pull M π (P.le i))
    (fun y => exists_mem P (π y)) fun i => ?_
  refine Eq.trans ?_ ((hE ⟨c • v.1, hc⟩ i).trans (loc_smul P π f' c v.1 i)).symm
  exact (congrArg _ (hρ _)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) (rs_rs _ _ _) (e i).symm))

end

/- English proof (translation)
Introduce and unpack `R _ X f M hM ⟨P⟩ hcl hsurj K _ g₀ X₀ π₀ f₀ h₀ hb ht`. Take `⟨v, hv, hu, hline⟩` from `loc_of_triv P h₀ hM ht`. Set `z : Spec (CommRingCat.of K)` to `(⊥ : PrimeSpectrum K)`. Establish `unit_cst : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (c : R') (w : Fin P.a → R'), (∀ i, IsUnit (loc P π f' (c • w) i)) → IsUnit c`. Introduce `R' _ g X' π f' h c w H`.

Assume the negation of the conclusion as `hc`. Take `⟨m, hm, hcm⟩` from `exists_max_ideal_of_mem_nonunits hc`. Establish `: Surjective f'` using `MorphismProperty.of_isPullback h hsurj`. Take `⟨y, hy⟩` from `f'.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum R')`. Take `⟨i, hi⟩` from `exists_mem P (π y)`.

Establish `h₁` using `H i`. Rewrite `h₁` using `[loc_smul]`. Establish `h₂` using `(mem_basicOpen_cst f' _ c hi).1 (mem_of_isUnit (isUnit_of_mul_isUnit_left h₁) hi)`. Rewrite `h₂` using `[hy]`. Conclude with `h₂ hcm`.

Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`. Conclude with `not_isUnit_zero (unit_cst K g₀ X₀ π₀ f₀ h₀ 0 0 (by rwa [smul_zero]))`. Take `⟨δ, v₀, hδ, hker⟩` from `exists_kernel_vector g₀ P.D₀ v hv0 (hline hb.2)`. Set `G : X.Opens` to `⨆ i, X.basicOpen (loc₀ P v₀ i)`.

Establish `hZ : IsClosed (f '' (G : Set X)ᶜ)` using `f.isClosedMap _ G.isOpen.isClosed_compl`. Establish `hp : Spec.map (CommRingCat.ofHom g₀) z ∈ (f '' (G : Set X)ᶜ)ᶜ`. Introduce and unpack `⟨x, hx, hfx⟩`. Take `⟨y, rfl, -⟩` from `Scheme.exists_preimage_of_isPullback h₀ x z hfx`. Take `⟨i, hi⟩` from `exists_mem P (π₀ y)`.

Take `⟨c, hc⟩` from `hker K g₀ hδ.isUnit v hv`. Establish `h₁` using `hu i`. Rewrite `h₁` using `[hc, loc_smul, loc_comp P h₀]`. Establish `h₂` using `mem_of_isUnit (isUnit_of_mul_isUnit_right h₁) (y := y) hi`. Rewrite `h₂` using `[← Scheme.preimage_basicOpen]`.

Conclude with `hx (TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩)`. Take `⟨_, ⟨r₁, rfl⟩, hr₁, hsub⟩` from `(PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp hZ.isOpen_compl`. Establish `hr₁' : g₀ r₁ ≠ 0` using `hr₁`. Use `⟨δ * r₁, Ideal.span (Set.range (P.D₀.mulVec v₀)), by rw [map_mul]; exact mul_ne_zero hδ hr₁', Submodule.fg_span (Set.finite_range _), fun R' _ g X' π f' h hr => ?_⟩` and prove the remaining obligations. Rewrite `hr` using `[map_mul]`.

Establish `hI : Ideal.span (Set.range (P.D₀.mulVec v₀)) ≤ RingHom.ker g ↔ (P.D₀.map g).mulVec (g ∘ v₀) = 0`. Rewrite using `[Ideal.span_le, Set.range_subset_iff, funext_iff]`. Use `forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[← RingHom.map_mulVec]`. Both sides reduce to the same expression.

Rewrite using `[hI]`. Prove the components needed by the constructor for the conclusion. Introduce `H`. Take `⟨w, hw, hwu, -⟩` from `loc_of_triv P h hM H`. Take `⟨c, rfl⟩` from `hker R' g (isUnit_of_mul_isUnit_left hr) w hw`.

Rewrite `hw` using `[Matrix.mulVec_smul]`. Conclude with `((unit_cst R' g X' π f' h c _ hwu).smul_eq_zero).1 hw`. Introduce `H`. Use `triv_of_loc P h _ H fun y => ?_` and prove the remaining obligations. Establish `hy : π y ∈ G`.

Assume the negation of the conclusion as `hy`. Establish `e : f (π y) = Spec.map (CommRingCat.ofHom g) (f' y)` using `congrArg (fun q => q y) h.w`. Use `hsub (a := f (π y)) ?_ ⟨π y, hy, rfl⟩` and prove the remaining obligations. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `g r₁ ∉ (f' y).asIdeal`.

Conclude with `fun hm => (f' y).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (isUnit_of_mul_isUnit_right hr))`. Take `⟨i, hi⟩` from `TopologicalSpace.Opens.mem_iSup.1 hy`. Use `⟨i, ?_⟩` and prove the remaining obligations. Rewrite using `[loc_comp P h, ← Scheme.preimage_basicOpen]`. Conclude with `hi`.
-/
theorem seesaw : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → Nonempty (Perf f M) → UniversallyClosed f → Surjective f → ∀ (K : Type) [Field K] (g₀ : R →+* K) (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom → Triv (M.pull π₀) → ∃ (r : R) (I : Ideal R), g₀ r ≠ 0 ∧ I.FG ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → IsUnit (g r) → (Triv (M.pull π) ↔ I ≤ RingHom.ker g) := by
  rintro R _ X f M hM ⟨P⟩ hcl hsurj K _ g₀ X₀ π₀ f₀ h₀ hb ht
  obtain ⟨v, hv, hu, hline⟩ := loc_of_triv P h₀ hM ht
  let z : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  have unit_cst : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
      ∀ (c : R') (w : Fin P.a → R'), (∀ i, IsUnit (loc P π f' (c • w) i)) → IsUnit c := by
    intro R' _ g X' π f' h c w H
    by_contra hc
    obtain ⟨m, hm, hcm⟩ := exists_max_ideal_of_mem_nonunits hc
    have : Surjective f' := MorphismProperty.of_isPullback h hsurj
    obtain ⟨y, hy⟩ := f'.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have h₁ := H i
    rw [loc_smul] at h₁
    have h₂ := (mem_basicOpen_cst f' _ c hi).1 (mem_of_isUnit (isUnit_of_mul_isUnit_left h₁) hi)
    rw [hy] at h₂
    exact h₂ hcm
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (unit_cst K g₀ X₀ π₀ f₀ h₀ 0 0 (by rwa [smul_zero]))
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline hb.2)
  let G : X.Opens := ⨆ i, X.basicOpen (loc₀ P v₀ i)
  have hZ : IsClosed (f '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hp : Spec.map (CommRingCat.ofHom g₀) z ∈ (f '' (G : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, hfx⟩
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₀ x z hfx
    obtain ⟨i, hi⟩ := exists_mem P (π₀ y)
    obtain ⟨c, hc⟩ := hker K g₀ hδ.isUnit v hv
    have h₁ := hu i
    rw [hc, loc_smul, loc_comp P h₀] at h₁
    have h₂ := mem_of_isUnit (isUnit_of_mul_isUnit_right h₁) (y := y) hi
    rw [← Scheme.preimage_basicOpen] at h₂
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩)
  obtain ⟨_, ⟨r₁, rfl⟩, hr₁, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp hZ.isOpen_compl
  have hr₁' : g₀ r₁ ≠ 0 := hr₁
  refine ⟨δ * r₁, Ideal.span (Set.range (P.D₀.mulVec v₀)), by rw [map_mul]; exact mul_ne_zero hδ hr₁',
    Submodule.fg_span (Set.finite_range _), fun R' _ g X' π f' h hr => ?_⟩
  rw [map_mul] at hr
  have hI : Ideal.span (Set.range (P.D₀.mulVec v₀)) ≤ RingHom.ker g ↔ (P.D₀.map g).mulVec (g ∘ v₀) = 0 := by
    rw [Ideal.span_le, Set.range_subset_iff, funext_iff]
    refine forall_congr' fun j => ?_
    rw [← RingHom.map_mulVec]
    rfl
  rw [hI]
  constructor
  · intro H
    obtain ⟨w, hw, hwu, -⟩ := loc_of_triv P h hM H
    obtain ⟨c, rfl⟩ := hker R' g (isUnit_of_mul_isUnit_left hr) w hw
    rw [Matrix.mulVec_smul] at hw
    exact ((unit_cst R' g X' π f' h c _ hwu).smul_eq_zero).1 hw
  · intro H
    refine triv_of_loc P h _ H fun y => ?_
    have hy : π y ∈ G := by
      by_contra hy
      have e : f (π y) = Spec.map (CommRingCat.ofHom g) (f' y) := congrArg (fun q => q y) h.w
      refine hsub (a := f (π y)) ?_ ⟨π y, hy, rfl⟩
      rw [e]
      change g r₁ ∉ (f' y).asIdeal
      exact fun hm => (f' y).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (isUnit_of_mul_isUnit_right hr))
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨i, ?_⟩
    rw [loc_comp P h, ← Scheme.preimage_basicOpen]
    exact hi

end GlobalTheory.AbLaw.Seesaw
