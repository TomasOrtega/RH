import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiDefs
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiCoreDefs
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.QiPtsA

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

open TensorProduct

namespace PositivityTheory.PrwZar.QiP

open GlobalTheory.CompanionTheory.Ar.GR

section BaseChange

variable {R : Type} [CommRing R] {C : Type} [Field C] [Algebra R C] {F : Type} [CommRing F] [Algebra R F]

def uu : F →ₐ[R] (C ⊗[R] F) := (Algebra.TensorProduct.includeRight : F →ₐ[R] C ⊗[R] F)

def lft {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T] (g : F →ₐ[R] T) :
    (C ⊗[R] F) →ₐ[C] T :=
  Algebra.TensorProduct.lift (Algebra.ofId C T) g (fun _ _ => Commute.all _ _)

/- English proof (translation)
Use extensionality with `x`. Simplify using `[lft, uu]`.
-/
theorem lft_uu {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T] (g : F →ₐ[R] T) :
    ((lft g).restrictScalars R).comp (uu (C := C)) = g := by
  ext x
  simp [lft, uu]

/- English proof (translation)
Apply `Algebra.TensorProduct.ext` to reduce the goal to its premises. Conclude with `Subsingleton.elim _ _`. Conclude with `e`.
-/
theorem ext_uu {T : Type} [CommRing T] [Algebra C T] [Algebra R T] [IsScalarTower R C T]
    (x y : (C ⊗[R] F) →ₐ[C] T)
    (e : (x.restrictScalars R).comp (uu (C := C)) = (y.restrictScalars R).comp (uu (C := C))) : x = y := by
  apply Algebra.TensorProduct.ext
  · exact Subsingleton.elim _ _
  · exact e

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {h : sp (R₀ := R) F ⟶ G}

def u1 : F →ₐ[R] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  (((Algebra.TensorProduct.includeLeft : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F))).restrictScalars R).comp (uu (R := R) (C := C) (F := F))

def u2 : F →ₐ[R] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  (((Algebra.TensorProduct.includeRight : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F))).restrictScalars R).comp (uu (R := R) (C := C) (F := F))

def dlt (hs : IsFinFlatSub G F h) : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F) ⊗[C] (C ⊗[R] F) :=
  lft (mulPt hs (u1 (C := C)) u2)

def eps (hs : IsFinFlatSub G F h) : (C ⊗[R] F) →ₐ[C] C :=
  lft (onePt hs C)

/- English proof (translation)
Rewrite using `[← comp_onePt hs ((Algebra.ofId C (C ⊗[R] F)).restrictScalars R), ← lft_uu (C := C) (onePt hs C)]`. Both sides reduce to the same expression.
-/
theorem eps_uu (hs : IsFinFlatSub G F h) :
    ((((Algebra.ofId C (C ⊗[R] F)).comp (eps (C := C) hs)).restrictScalars R).comp (uu (C := C))) = onePt hs (C ⊗[R] F) := by
  rw [← comp_onePt hs ((Algebra.ofId C (C ⊗[R] F)).restrictScalars R), ← lft_uu (C := C) (onePt hs C)]
  rfl

/- English proof (translation)
Establish `e : (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C` using `C) hs))).restrictScalars R).comp (uu (C := C)) = ((((Algebra.TensorProduct.lmul' C).comp (Algebra.TensorProduct.map f g))).restrictScalars R).comp (((dlt (C := C) hs).restrictScalars R).comp uu) := rfl`. Rewrite using `[e, dlt, lft_uu, comp_mulPt]`. Use `congr 1`. Use extensionality with `x`. Simplify using `[u1, uu]`.

Use extensionality with `x`. Simplify using `[u2, uu]`.
-/
theorem mul_dlt_uu (hs : IsFinFlatSub G F h) (f g : (C ⊗[R] F) →ₐ[C] (C ⊗[R] F)) :
    ((((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C := C) hs))).restrictScalars R).comp
      (uu (C := C))) = mulPt hs ((f.restrictScalars R).comp uu) ((g.restrictScalars R).comp uu) := by
  have e : (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map f g).comp (dlt (C := C) hs))).restrictScalars R).comp
      (uu (C := C)) = ((((Algebra.TensorProduct.lmul' C).comp (Algebra.TensorProduct.map f g))).restrictScalars R).comp
        (((dlt (C := C) hs).restrictScalars R).comp uu) := rfl
  rw [e, dlt, lft_uu, comp_mulPt]
  congr 1
  · ext x
    simp [u1, uu]
  · ext x
    simp [u2, uu]

/- English proof (translation)
Apply `ext_uu` to reduce the goal to its premises. Rewrite using `[mul_dlt_uu, eps_uu]`. Conclude with `mulPt_onePt hs _`.
-/
theorem counitL (hs : IsFinFlatSub G F h) : Qi.CounitL (dlt (C := C) hs) (eps (C := C) hs) := by
  apply ext_uu
  rw [mul_dlt_uu, eps_uu]
  exact mulPt_onePt hs _

/- English proof (translation)
Apply `ext_uu` to reduce the goal to its premises. Rewrite using `[mul_dlt_uu, eps_uu]`. Conclude with `mulPt_onePt' hs _`.
-/
theorem counitR (hs : IsFinFlatSub G F h) : Qi.CounitR (dlt (C := C) hs) (eps (C := C) hs) := by
  apply ext_uu
  rw [mul_dlt_uu, eps_uu]
  exact mulPt_onePt' hs _

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => exact eps_uu hs`. Consider the case `succ n ih`. Express the relevant statement in the definitionally equal form `(((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n) (AlgHom.id C (C ⊗[R] F))).comp (dlt (C := C) hs))).restrictScalars R).comp uu = _`. Rewrite using `[mul_dlt_uu, ih]`.

Both sides reduce to the same expression.
-/
theorem pw_uu (hs : IsFinFlatSub G F h) (n : ℕ) :
    ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n).restrictScalars R).comp uu = powPt hs uu n := by
  induction n with
  | zero => exact eps_uu hs
  | succ n ih =>
    change (((Algebra.TensorProduct.lmul' C).comp ((Algebra.TensorProduct.map (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) n)
      (AlgHom.id C (C ⊗[R] F))).comp (dlt (C := C) hs))).restrictScalars R).comp uu = _
    rw [mul_dlt_uu, ih]
    rfl

/- English proof (translation)
Apply `ext_uu` to reduce the goal to its premises. Rewrite using `[pw_uu, powPt_mul]`. Establish `hc : (((Qi.pw (dlt (C` using `C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b)).restrictScalars R).comp (uu (C := C)) = ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).restrictScalars R).comp (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b).restrictScalars R).comp uu) := rfl`. Rewrite using `[hc, pw_uu, comp_powPt, pw_uu]`.
-/
theorem pw_mul (hs : IsFinFlatSub G F h) (a b : ℕ) :
    Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (a * b) = (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b) := by
  apply ext_uu
  rw [pw_uu, powPt_mul]
  have hc : (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b)).restrictScalars R).comp
      (uu (C := C)) = ((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) a).restrictScalars R).comp
        (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) b).restrictScalars R).comp uu) := rfl
  rw [hc, pw_uu, comp_powPt, pw_uu]

def ptGrp (hs : IsFinFlatSub G F h) (S : Type) [CommRing S] [Algebra R S] : Subgroup (sp (R₀ := R) S ⟶ G) where
  carrier := {g | ∃ φ : F →ₐ[R] S, spMap φ ≫ h = g}
  mul_mem' := by
    rintro _ _ ⟨φ, rfl⟩ ⟨φ', rfl⟩
    exact ⟨mulPt hs φ φ', mulPt_spec hs φ φ'⟩
  one_mem' := ⟨onePt hs S, onePt_spec hs S⟩
  inv_mem' := by
    rintro _ ⟨φ, rfl⟩
    obtain ⟨χ, hχ⟩ := hs.inv S φ
    exact ⟨χ, eq_inv_of_mul_eq_one_left hχ⟩

/- English proof (translation)
Use `haveI : Finite (ptGrp hs C) := Finite.of_surjective (fun φ : F →ₐ[R] C => (⟨_, φ, rfl⟩ : ptGrp hs C)) (by rintro ⟨_, φ, rfl⟩; exact ⟨φ, rfl⟩)`. Use `⟨Nat.card (ptGrp hs C), Nat.card_pos, fun x => ?_⟩` and prove the remaining obligations. Apply `ext_uu` to reduce the goal to its premises. Establish `hx : ((x.comp (Qi.pw (dlt (C` using `C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C)))).restrictScalars R).comp (uu (C := C)) = (x.restrictScalars R).comp (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C))).restrictScalars R).comp uu) := rfl`. Establish `he : ((eps (C` using `C) hs).restrictScalars R).comp uu = onePt hs C := lft_uu _`.

Rewrite using `[hx, pw_uu, comp_powPt, he]`. Apply `pt_ext hs` to reduce the goal to its premises. Rewrite using `[powPt_spec, onePt_spec]`. Establish `h1` using `pow_card_eq_one' (G := ptGrp hs C) (x := ⟨_, (x.restrictScalars R).comp uu, rfl⟩)`. Conclude with `congrArg Subtype.val h1`.
-/
theorem pts_killed [Module.Finite R F] (hs : IsFinFlatSub G F h) :
    ∃ m : ℕ, 0 < m ∧ ∀ x : (C ⊗[R] F) →ₐ[C] C, x.comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) m) = eps hs := by
  haveI : Finite (ptGrp hs C) :=
    Finite.of_surjective (fun φ : F →ₐ[R] C => (⟨_, φ, rfl⟩ : ptGrp hs C))
      (by rintro ⟨_, φ, rfl⟩; exact ⟨φ, rfl⟩)
  refine ⟨Nat.card (ptGrp hs C), Nat.card_pos, fun x => ?_⟩
  apply ext_uu
  have hx : ((x.comp (Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C)))).restrictScalars R).comp
      (uu (C := C)) = (x.restrictScalars R).comp
        (((Qi.pw (dlt (C := C) hs) (eps (C := C) hs) (Nat.card (ptGrp hs C))).restrictScalars R).comp uu) := rfl
  have he : ((eps (C := C) hs).restrictScalars R).comp uu = onePt hs C := lft_uu _
  rw [hx, pw_uu, comp_powPt, he]
  apply pt_ext hs
  rw [powPt_spec, onePt_spec]
  have h1 := pow_card_eq_one' (G := ptGrp hs C) (x := ⟨_, (x.restrictScalars R).comp uu, rfl⟩)
  exact congrArg Subtype.val h1

/- English proof (translation)
The claim follows from `Algebra.TensorProduct.includeRight_injective hR`.
-/
theorem uu_injective [Module.Flat R F] (hR : Function.Injective (algebraMap R C)) :
    Function.Injective (uu (R := R) (C := C) (F := F)) := Algebra.TensorProduct.includeRight_injective hR

end BaseChange

end PositivityTheory.PrwZar.QiP

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR QiP

/- English proof (translation)
Introduce `C _ _ v R _ _ hv G _ _ F _ _ h hs`. Use `haveI := hs.fin`. Use `haveI := hs.proj`. Take `⟨N, hN0, hN⟩` from `hc C (C ⊗[R] F) (dlt (C := C) hs) (eps hs) (counitL hs) (counitR hs) (pw_mul hs) (pts_killed hs)`. Establish `hinj : Function.Injective (algebraMap R C)` using `hv.hom_inj`.

Establish `key : powPt hs (AlgHom.id R F) N = onePt hs F`. Establish `e1` using `pw_uu (C := C) hs N`. Establish `e0` using `pw_uu (C := C) hs 0`. Rewrite `e1` using `[hN, e0]`. Establish `a1 : (uu (R` using `R) (C := C) (F := F)).comp (powPt hs (AlgHom.id R F) N) = powPt hs uu N := by`.

Rewrite using `[comp_powPt, AlgHom.comp_id]`. Establish `a0 : (uu (R` using `R) (C := C) (F := F)).comp (onePt hs F) = powPt hs uu 0 := by`. Rewrite using `[comp_onePt]`. Both sides reduce to the same expression. Use extensionality with `y`.

Apply `uu_injective (C := C) hinj` to reduce the goal to its premises. Conclude with `congrArg (fun f => f y) (a1.trans (e1.symm.trans a0.symm))`. Use `⟨N, hN0, fun S _ _ φ => ?_⟩` and prove the remaining obligations. Rewrite using `[← powPt_spec hs, ← onePt_spec hs S]`. Establish `e : φ.comp (powPt hs (AlgHom.id R F) N) = φ.comp (onePt hs F)` using `by rw [key]`.

Rewrite `e` using `[comp_powPt, comp_onePt, AlgHom.comp_id]`. Rewrite using `[e]`.
-/
theorem killedAny_of (hc : Qi.KilledCore) : KilledAny := by
  intro C _ _ v R _ _ hv G _ _ F _ _ h hs
  haveI := hs.fin
  haveI := hs.proj
  obtain ⟨N, hN0, hN⟩ := hc C (C ⊗[R] F) (dlt (C := C) hs) (eps hs) (counitL hs) (counitR hs) (pw_mul hs)
    (pts_killed hs)
  have hinj : Function.Injective (algebraMap R C) := hv.hom_inj
  have key : powPt hs (AlgHom.id R F) N = onePt hs F := by
    have e1 := pw_uu (C := C) hs N
    have e0 := pw_uu (C := C) hs 0
    rw [hN, e0] at e1
    have a1 : (uu (R := R) (C := C) (F := F)).comp (powPt hs (AlgHom.id R F) N) = powPt hs uu N := by
      rw [comp_powPt, AlgHom.comp_id]
    have a0 : (uu (R := R) (C := C) (F := F)).comp (onePt hs F) = powPt hs uu 0 := by
      rw [comp_onePt]
      rfl
    ext y
    apply uu_injective (C := C) hinj
    exact congrArg (fun f => f y) (a1.trans (e1.symm.trans a0.symm))
  refine ⟨N, hN0, fun S _ _ φ => ?_⟩
  rw [← powPt_spec hs, ← onePt_spec hs S]
  have e : φ.comp (powPt hs (AlgHom.id R F) N) = φ.comp (onePt hs F) := by rw [key]
  rw [comp_powPt, comp_onePt, AlgHom.comp_id] at e
  rw [e]

end PositivityTheory.PrwZar
