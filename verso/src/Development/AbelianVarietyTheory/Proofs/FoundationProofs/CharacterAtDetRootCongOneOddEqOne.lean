import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostFieldStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DetRootCong

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a x => simp [sigR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem map_sigR {F E R R' : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] [CommRing R']
    [Algebra F R'] (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    (Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom (sigR R σ x) =
      sigR R' σ ((Algebra.TensorProduct.map f (AlgHom.id F E)).toRingHom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Establish `hs : s y * s y' = 1` using `by rw [← map_mul, hyy, map_one]`. Express the relevant statement in the definitionally equal form `s (f ((x : A) * (Y⁻¹ : Aˣ))) = f ((x : A) * (Y⁻¹ : Aˣ))`. Rewrite using `[map_mul, hY, map_mul]`. Take the linear combination `(-y') * hx + (s (f x) * s y' * y') * hy - (s (f x) * s y') * hyy + (u * s (f x) * y') * hs`.
-/
theorem quot_fixed {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (s : B →+* B) (x Y : Aˣ) (u y y' : B)
    (hx : f x = u * s (f x)) (hy : y = u * s y) (hyy : y * y' = 1) (hY : f (Y⁻¹ : Aˣ) = y') :
    s ((Units.map f.toMonoidHom (x * Y⁻¹) : Bˣ) : B) = (Units.map f.toMonoidHom (x * Y⁻¹) : Bˣ) := by
  have hs : s y * s y' = 1 := by rw [← map_mul, hyy, map_one]
  change s (f ((x : A) * (Y⁻¹ : Aˣ))) = f ((x : A) * (Y⁻¹ : Aˣ))
  rw [map_mul, hY, map_mul]
  linear_combination (-y') * hx + (s (f x) * s y' * y') * hy - (s (f x) * s y') * hyy
    + (u * s (f x) * y') * hs

/- English proof (translation)
The claim follows from `map_sigR _ _ x`.
-/
theorem finPart_sigR (D : D7) (x : AE D) :
    finPart D (sigR (AF D.host.F) D.sp.cm.sig x) = sigR (Af D.host.F) D.sp.cm.sig (finPart D x) :=
  map_sigR _ _ x

/- English proof (translation)
Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Establish `h1 : e.symm (1, y) * e.symm (1, y') = 1`. Rewrite using `[← map_mul, Prod.mk_mul_mk, h, mul_one]`. Conclude with `map_one e.symm`. Apply the tactic sequence `refine ⟨⟨e.symm (1, y), e.symm (1, y'), h1, by rw [mul_comm, h1]⟩, (he _).1.symm.trans ?_, (he _).2.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp`.
-/
theorem exists_idele (D : D7) (y y' : Af D.host.F ⊗[D.host.F] D.host.E) (h : y * y' = 1) :
    ∃ Y : (AE D)ˣ, infPart D (Y : AE D) = 1 ∧ finPart D (Y : AE D) = y ∧
      finPart D ((Y⁻¹ : (AE D)ˣ) : AE D) = y' := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have h1 : e.symm (1, y) * e.symm (1, y') = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, h, mul_one]
    exact map_one e.symm
  refine ⟨⟨e.symm (1, y), e.symm (1, y'), h1, by rw [mul_comm, h1]⟩,
    (he _).1.symm.trans ?_, (he _).2.symm.trans ?_, (he _).2.symm.trans ?_⟩ <;> simp

/- English proof (translation)
Use `⟨⟨(1, b), (1, (b⁻¹ : (Af D.host.F)ˣ)), Prod.ext (mul_one _) b.mul_inv, Prod.ext (mul_one _) b.inv_mul⟩, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem exists_idF (D : D7) (b : (Af D.host.F)ˣ) :
    ∃ a : (AF D.host.F)ˣ, finPart D (idF D a : AE D) =
      algebraMap (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) b := by
  refine ⟨⟨(1, b), (1, (b⁻¹ : (Af D.host.F)ˣ)), Prod.ext (mul_one _) b.mul_inv,
    Prod.ext (mul_one _) b.inv_mul⟩, ?_⟩
  rfl

/- English proof (translation)
Introduce `D V c N hN hF hinf hcong g x hx ⟨w, hw, hwe⟩`. Establish `hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x` using `fun x => star_star x`. Establish `htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x`. Introduce `x`. Apply `(D.sp.cm.fixed _).1` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `D.sp.cm.sig _ = _`. Rewrite using `[map_add, hσ, add_comm]`. Rewrite `hwe` using `[Matrix.GeneralLinearGroup.val_det_apply]`. Establish `hn` using `GlobalTheory.RecDict.det_finHom_norm V g`. Take `⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩` from `GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN _ w hw hwe hn`.

Take `⟨Y, hY1, hY2, hY3⟩` from `exists_idele D y y' hyy`. Establish `hcY : c Y = 1` using `hcong Y ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩ ⟨p, hp, hY2 ▸ hpe⟩`. Establish `hdet : (finHom V g).1.det = finPart D (matHom V g).1.det` using `((finPart D).map_det _).symm`. Establish `hxf : finPart D (x : AE D) = (finHom V g).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D))`. Rewrite using `[hdet, ← finPart_sigR, ← RingHom.map_mul]`.

Conclude with `congrArg _ hx`. Take `⟨b, hb⟩` from `GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr (Units.map (finPart D).toMonoidHom (x * Y⁻¹)) (quot_fixed (finPart D) _ x Y _ y y' hxf hroot hyy hY3)`. Take `⟨a, ha⟩` from `exists_idF D b`. Establish `hb' : finPart D (idF D a : AE D) = finPart D ((x * Y⁻¹ : (AE D)ˣ) : AE D)` using `ha.trans (congrArg Units.val hb)`. Establish `h1` using `hinf (x * Y⁻¹ * (idF D a)⁻¹) (by`.

Rewrite using `[Units.val_mul, RingHom.map_mul, ← hb', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])`. Simplify `h1` using `[hcY, hF a]`.
-/
theorem char_root_eq_one : ∀ (D : D7) (V : HSp D) (c : (AE D)ˣ →* Circle) (N : ℕ), Odd N → (∀ a, c (idF D a) = 1) → (∀ x : (AE D)ˣ, finPart D (x : AE D) = 1 → c x = 1) → (∀ x : (AE D)ˣ, FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y) → c x = 1) → ∀ (g : GA D V) (x : (AE D)ˣ), IsDetRoot V g x → (∃ w ∈ intAE D, (((Matrix.GeneralLinearGroup.det (finHom V g)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = N • w) → c x = 1 := by
  intro D V c N hN hF hinf hcong g x hx ⟨w, hw, hwe⟩
  have hσ : ∀ x, D.sp.cm.sig (D.sp.cm.sig x) = x := fun x => star_star x
  have htr : ∀ x : D.host.E, ∃ t : D.host.F, algebraMap _ _ t = x + D.sp.cm.sig x := by
    intro x
    apply (D.sp.cm.fixed _).1
    change D.sp.cm.sig _ = _
    rw [map_add, hσ, add_comm]
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hwe
  have hn := GlobalTheory.RecDict.det_finHom_norm V g
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.T.exists_normOne_root_congruent_odd_hostField D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := exists_idele D y y' hyy
  have hcY : c Y = 1 := hcong Y ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩ ⟨p, hp, hY2 ▸ hpe⟩
  have hdet : (finHom V g).1.det = finPart D (matHom V g).1.det := ((finPart D).map_det _).symm
  have hxf : finPart D (x : AE D) =
      (finHom V g).1.det * sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) := by
    rw [hdet, ← finPart_sigR, ← RingHom.map_mul]
    exact congrArg _ hx
  obtain ⟨b, hb⟩ := GlobalTheory.Member.exists_unit_of_sigR_fixed (Af D.host.F) D.sp.cm.sig htr
    (Units.map (finPart D).toMonoidHom (x * Y⁻¹)) (quot_fixed (finPart D) _ x Y _ y y' hxf hroot hyy hY3)
  obtain ⟨a, ha⟩ := exists_idF D b
  have hb' : finPart D (idF D a : AE D) = finPart D ((x * Y⁻¹ : (AE D)ˣ) : AE D) :=
    ha.trans (congrArg Units.val hb)
  have h1 := hinf (x * Y⁻¹ * (idF D a)⁻¹) (by
    rw [Units.val_mul, RingHom.map_mul, ← hb', ← RingHom.map_mul, Units.mul_inv, RingHom.map_one])
  simpa [hcY, hF a] using h1

end GlobalTheory.DetRootCong
