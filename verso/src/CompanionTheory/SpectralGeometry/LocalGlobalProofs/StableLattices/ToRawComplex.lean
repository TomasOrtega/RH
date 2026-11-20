import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

noncomputable section

namespace GlobalTheory.CompanionTheory.ZuckToRaw

variable {k r : ℕ}

/- English proof (translation)
Proceed by induction on `W with`. Consider the case `nil => rfl`. Consider the case `cons X W ih => show PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0) = 0`. Rewrite using `[ih]`. Simplify using `[PI.UpqRep.dsig]`.
-/
theorem dsigW_zero' (R : Rep k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :
    PI.UpqRep.dsigW (k := k) (r := r) R.σ W (0 : R.H) = 0 := by
  induction W with
  | nil => rfl
  | cons X W ih =>
    show PI.UpqRep.dsig (k := k) (r := r) R.σ X (PI.UpqRep.dsigW (k := k) (r := r) R.σ W 0) = 0
    rw [ih]
    simp [PI.UpqRep.dsig]

open Classical in

def extZ {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub) (y : R.H) : R'.H :=
  if h : y ∈ R.smSub then (f ⟨y, h⟩ : R'.H) else 0

/- English proof (translation)
Simplify using `only [extZ, dif_pos y.2]`.
-/
theorem extZ_coe {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub) (y : R.smSub) :
    extZ f (y : R.H) = (f y : R'.H) := by
  simp only [extZ, dif_pos y.2]

/- English proof (translation)
Use `extZ_coe f ⟨v, hv⟩` as an intermediate fact. Rewrite using `[show extZ f v = _ from this]`. Conclude with `(f _).2`. Use `add v hv w hw := by`. Establish `h1` using `extZ_coe f ⟨v, hv⟩`.

Establish `h2` using `extZ_coe f ⟨w, hw⟩`. Establish `h3` using `extZ_coe f (⟨v, hv⟩ + ⟨w, hw⟩)`. Rewrite using `[show extZ f v = _ from h1, show extZ f w = _ from h2, show extZ f (v + w) = _ from h3, map_add]`. Both sides reduce to the same expression. Use `smul a v hv := by`.

Establish `h1` using `extZ_coe f ⟨v, hv⟩`. Establish `h3` using `extZ_coe f (a • ⟨v, hv⟩)`. Rewrite using `[show extZ f v = _ from h1, show extZ f (a • v) = _ from h3, map_smul]`. Both sides reduce to the same expression. Use `cont W hW := by`.

Take `⟨C, Ws, h1, h2⟩` from `hf W hW`. Use `⟨C, Ws, h1, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h3` using `extZ_coe f ⟨v, hv⟩`. Use `show ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (extZ f v)‖ ≤ _`. Rewrite using `[show extZ f v = _ from h3]`.

Conclude with `h2 ⟨v, hv⟩`.
-/
theorem smMap_extZ {R R' : Rep k r} (f : R.smSub →ₗ[ℂ] R'.smSub)
    (hf : ∀ W, LieWd k r W → ∃ (C : ℝ) (Ws : List (List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ))), (∀ W' ∈ Ws, LieWd k r W') ∧
      ∀ y : R.smSub, ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (f y : R'.H)‖ ≤
        C * (Ws.map fun W' => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W' (y : R.H)‖).sum) :
    SmMap R R' (extZ f) where
  mem v hv := by
    have := extZ_coe f ⟨v, hv⟩
    rw [show extZ f v = _ from this]
    exact (f _).2
  add v hv w hw := by
    have h1 := extZ_coe f ⟨v, hv⟩
    have h2 := extZ_coe f ⟨w, hw⟩
    have h3 := extZ_coe f (⟨v, hv⟩ + ⟨w, hw⟩)
    rw [show extZ f v = _ from h1, show extZ f w = _ from h2, show extZ f (v + w) = _ from h3, map_add]
    rfl
  smul a v hv := by
    have h1 := extZ_coe f ⟨v, hv⟩
    have h3 := extZ_coe f (a • ⟨v, hv⟩)
    rw [show extZ f v = _ from h1, show extZ f (a • v) = _ from h3, map_smul]
    rfl
  cont W hW := by
    obtain ⟨C, Ws, h1, h2⟩ := hf W hW
    refine ⟨C, Ws, h1, fun v hv => ?_⟩
    have h3 := extZ_coe f ⟨v, hv⟩
    show ‖PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (extZ f v)‖ ≤ _
    rw [show extZ f v = _ from h3]
    exact h2 ⟨v, hv⟩

/- English proof (translation)
Unfold `sn`. Rewrite using `[Finset.sum_eq_single c]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Pi.single_eq_of_ne hb, ZeroMemClass.coe_zero, dsigW_zero', norm_zero]`.

Simplify using the standard rewrite rules.
-/
theorem sn_single (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (v : X.2.R.smSub) :
    sn X W (Pi.single c v) = ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (v : X.2.R.H)‖ := by
  unfold sn
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, ZeroMemClass.coe_zero, dsigW_zero', norm_zero]
  · simp

/- English proof (translation)
The claim follows from `Finset.single_le_sum (f := fun c => ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ c)`.
-/
theorem le_sn (X : Obj k r) (W : List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) (c : X.1.ι) (x : M X) :
    ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖ ≤ sn X W x :=
  Finset.single_le_sum (f := fun c => ‖PI.UpqRep.dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ c)

def coord {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (c : X.1.ι) : X.2.R.smSub →ₗ[ℂ] Y.2.R.smSub :=
  LinearMap.proj d ∘ₗ f ∘ₗ LinearMap.single ℂ (fun _ : X.1.ι => X.2.R.smSub) c

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coord_apply {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (c : X.1.ι) (v : X.2.R.smSub) :
    coord f d c v = f (Pi.single c v) d := rfl

/- English proof (translation)
Use `smMap_extZ _ fun W hW => ?_` and prove the remaining obligations. Take `⟨C, Ws, h1, h2⟩` from `hf.cont W hW`. Use `⟨C, Ws, h1, fun y => ?_⟩` and prove the remaining obligations. Use `(le_sn Y W d _).trans (h2 (Pi.single c y))` as an intermediate fact. Simplify `this` using `only [sn_single, coord_apply]`.
-/
theorem smMap_coord {X Y : Obj k r} {f : M X →ₗ[ℂ] M Y} (hf : IsHom X Y f) (d : Y.1.ι) (c : X.1.ι) :
    SmMap X.2.R Y.2.R (extZ (coord f d c)) := by
  refine smMap_extZ _ fun W hW => ?_
  obtain ⟨C, Ws, h1, h2⟩ := hf.cont W hW
  refine ⟨C, Ws, h1, fun y => ?_⟩
  have := (le_sn Y W d _).trans (h2 (Pi.single c y))
  simpa only [sn_single, coord_apply] using this

/- English proof (translation)
Simplify using `only [extZ_coe, coord_apply]`. Use `conv_rhs => rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply]`. Simplify using the standard rewrite rules.
-/
theorem sum_coord {X Y : Obj k r} (f : M X →ₗ[ℂ] M Y) (d : Y.1.ι) (x : M X) :
    ∑ c, extZ (coord f d c) (x c : X.2.R.H) = (f x d : Y.2.R.H) := by
  simp only [extZ_coe, coord_apply]
  conv_rhs => rw [← Finset.univ_sum_single x, map_sum, Finset.sum_apply]
  simp

/- English proof (translation)
Simplify using `[CompanionTheory.Zuck.act, BranchingSupport.act, mAct, dOp, URep.sig_coe _ hg]`.
-/
theorem act_coe (X : Obj k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ GG k r) (x : M X) (c : X.1.ι) :
    (CompanionTheory.Zuck.act X g x c : X.2.R.H) = BranchingSupport.act X.1.ρ X.2.R g (fun d => (x d : X.2.R.H)) c := by
  simp [CompanionTheory.Zuck.act, BranchingSupport.act, mAct, dOp, URep.sig_coe _ hg]

/- English proof (translation)
Rewrite using `[← sum_coord f d x]`. Simplify using the standard rewrite rules.
-/
theorem one_coord {U : URep k r} {Y : Obj k r} (f : M (one U) →ₗ[ℂ] M Y) (d : Y.1.ι) (x : M (one U)) :
    extZ (coord f d ()) (x () : U.R.H) = (f x d : Y.2.R.H) := by
  rw [← sum_coord f d x]
  simp

/- English proof (translation)
Rewrite using `[act_coe (one U) hg]`. Simplify using `[BranchingSupport.act]`.
-/
theorem act_one (U : URep k r) {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ GG k r) (x : M (one U)) :
    (CompanionTheory.Zuck.act (one U) g x () : U.R.H) = U.R.σ g (x ()) := by
  rw [act_coe (one U) hg]
  simp [BranchingSupport.act]

/- English proof (translation)
Introduce and unpack `k r F U κ _ _ T ⟨io, pr, h⟩`. Use `⟨fun a c => extZ (coord (io a) c ()), fun a c => extZ (coord (pr a) () c), ?_⟩` and prove the remaining obligations. Use `⟨fun I c => smMap_coord (h.io_hom I) c (), fun I c => smMap_coord (h.pr_hom I) () c, fun I g hg y hy => ?_, fun I g hg x hx => ?_, fun x hx c => ?_, fun I y hy => ?_, fun I J hIJ y hy => ?_⟩` and prove the remaining obligations. Set `y' : M (one (T I))` to `fun _ => ⟨y, hy⟩`. Use function extensionality and compare the values at `c`.

Establish `e1 : (T I).R.σ g y = (CompanionTheory.Zuck.act (one (T I)) g y' () : (T I).R.H)` using `(act_one (T I) hg y').symm`. Establish `e2 : ∀ d, extZ (coord (io I) d ()) y = (io I y' d : U.R.H)` using `fun d => one_coord (io I) d y'`. Establish `e3` using `LinearMap.congr_fun ((h.io_hom I).equiv g hg) y'`. Simplify using `only [LinearMap.comp_apply] at e3`. Simplify using `only [e2]`.

Rewrite using `[e1, one_coord, e3]`. Conclude with `act_coe (F, U) hg _ c`. Set `x' : M (F, U)` to `fun c => ⟨x c, hx c⟩`. Establish `e1 : ∀ c, BranchingSupport.act F.ρ U.R g x c = (CompanionTheory.Zuck.act (F, U) g x' c : U.R.H)` using `fun c => (act_coe (F, U) hg x' c).symm`. Establish `e2 : ∑ c, extZ (coord (pr I) () c) (x c) = (pr I x' () : (T I).R.H)` using `sum_coord (pr I) () x'`.

Establish `e3` using `LinearMap.congr_fun ((h.pr_hom I).equiv g hg) x'`. Simplify using `only [LinearMap.comp_apply] at e3`. Simplify using `only [e1]`. Rewrite using `[e2, ← act_one (T I) hg, ← e3]`. Conclude with `sum_coord (pr I) () _`.

Set `x' : M (F, U)` to `fun c => ⟨x c, hx c⟩`. Establish `e2 : ∀ I, ∑ c, extZ (coord (pr I) () c) (x c) = (pr I x' () : (T I).R.H)` using `fun I => sum_coord (pr I) () x'`. Establish `e4 : ∀ I, extZ (coord (io I) c ()) (pr I x' () : (T I).R.H) = (io I (pr I x') c : U.R.H)` using `fun I => one_coord (io I) c _`. Establish `e3` using `congrFun (LinearMap.congr_fun h.sum x') c`. Simplify using `only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at e3`.

Simplify using `only [e2, e4]`. Rewrite using `[← Submodule.coe_sum, e3]`. Set `y' : M (one (T I))` to `fun _ => ⟨y, hy⟩`. Establish `e2 : ∀ d, extZ (coord (io I) d ()) y = (io I y' d : U.R.H)` using `fun d => one_coord (io I) d y'`. Establish `e3` using `LinearMap.congr_fun (h.pr_io I) y'`.

Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at e3`. Simplify using `only [e2]`. Use `(sum_coord (pr I) () (io I y')).trans ?_` and prove the remaining obligations. Rewrite using `[e3]`. Set `y' : M (one (T J))` to `fun _ => ⟨y, hy⟩`.

Establish `e2 : ∀ d, extZ (coord (io J) d ()) y = (io J y' d : U.R.H)` using `fun d => one_coord (io J) d y'`. Establish `e3` using `LinearMap.congr_fun (h.pr_io_ne I J hIJ) y'`. Simplify using `only [LinearMap.comp_apply, LinearMap.zero_apply] at e3`. Simplify using `only [e2]`. Use `(sum_coord (pr I) () (io J y')).trans ?_` and prove the remaining obligations.

Rewrite using `[e3]`. Both sides reduce to the same expression.
-/
theorem toRaw : ToRaw := by
  rintro k r F U κ _ _ T ⟨io, pr, h⟩
  refine ⟨fun a c => extZ (coord (io a) c ()), fun a c => extZ (coord (pr a) () c), ?_⟩
  refine ⟨fun I c => smMap_coord (h.io_hom I) c (), fun I c => smMap_coord (h.pr_hom I) () c,
    fun I g hg y hy => ?_, fun I g hg x hx => ?_, fun x hx c => ?_, fun I y hy => ?_, fun I J hIJ y hy => ?_⟩
  · let y' : M (one (T I)) := fun _ => ⟨y, hy⟩
    funext c
    have e1 : (T I).R.σ g y = (CompanionTheory.Zuck.act (one (T I)) g y' () : (T I).R.H) := (act_one (T I) hg y').symm
    have e2 : ∀ d, extZ (coord (io I) d ()) y = (io I y' d : U.R.H) := fun d => one_coord (io I) d y'
    have e3 := LinearMap.congr_fun ((h.io_hom I).equiv g hg) y'
    simp only [LinearMap.comp_apply] at e3
    simp only [e2]
    rw [e1, one_coord, e3]
    exact act_coe (F, U) hg _ c
  · let x' : M (F, U) := fun c => ⟨x c, hx c⟩
    have e1 : ∀ c, BranchingSupport.act F.ρ U.R g x c = (CompanionTheory.Zuck.act (F, U) g x' c : U.R.H) :=
      fun c => (act_coe (F, U) hg x' c).symm
    have e2 : ∑ c, extZ (coord (pr I) () c) (x c) = (pr I x' () : (T I).R.H) := sum_coord (pr I) () x'
    have e3 := LinearMap.congr_fun ((h.pr_hom I).equiv g hg) x'
    simp only [LinearMap.comp_apply] at e3
    simp only [e1]
    rw [e2, ← act_one (T I) hg, ← e3]
    exact sum_coord (pr I) () _
  · let x' : M (F, U) := fun c => ⟨x c, hx c⟩
    have e2 : ∀ I, ∑ c, extZ (coord (pr I) () c) (x c) = (pr I x' () : (T I).R.H) :=
      fun I => sum_coord (pr I) () x'
    have e4 : ∀ I, extZ (coord (io I) c ()) (pr I x' () : (T I).R.H) = (io I (pr I x') c : U.R.H) :=
      fun I => one_coord (io I) c _
    have e3 := congrFun (LinearMap.congr_fun h.sum x') c
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, LinearMap.id_apply] at e3
    simp only [e2, e4]
    rw [← Submodule.coe_sum, e3]
  · let y' : M (one (T I)) := fun _ => ⟨y, hy⟩
    have e2 : ∀ d, extZ (coord (io I) d ()) y = (io I y' d : U.R.H) := fun d => one_coord (io I) d y'
    have e3 := LinearMap.congr_fun (h.pr_io I) y'
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at e3
    simp only [e2]
    refine (sum_coord (pr I) () (io I y')).trans ?_
    rw [e3]
  · let y' : M (one (T J)) := fun _ => ⟨y, hy⟩
    have e2 : ∀ d, extZ (coord (io J) d ()) y = (io J y' d : U.R.H) := fun d => one_coord (io J) d y'
    have e3 := LinearMap.congr_fun (h.pr_io_ne I J hIJ) y'
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at e3
    simp only [e2]
    refine (sum_coord (pr I) () (io J y')).trans ?_
    rw [e3]
    rfl

end GlobalTheory.CompanionTheory.ZuckToRaw

end
