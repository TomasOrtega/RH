import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.EmptyFirstBlock

section Reindex

variable {R : Type} [CommRing R] {t : ℕ} {c : Bool → ℕ}

def trueEquiv (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) : Fin (c true) ≃ Fin t :=
  Equiv.ofBijective (fun i => f ⟨true, i⟩) ⟨fun i j h => by
    have := f.injective h
    simpa using this, fun x => by
    obtain ⟨⟨b, i⟩, rfl⟩ := f.surjective x
    cases b with
    | false => exact absurd i.2 (by omega)
    | true => exact ⟨i, rfl⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem trueEquiv_apply (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) (i : Fin (c true)) :
    trueEquiv f hc i = f ⟨true, i⟩ := rfl

def reindexGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) :
    GL m R →* GL n R :=
  Units.map (Matrix.reindexAlgEquiv R R e).toRingEquiv.toMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_reindexGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m R) (i j : n) :
    (reindexGL e g : Matrix n n R) i j = (g : Matrix m m R) (e.symm i) (e.symm j) := rfl

/- English proof (translation)
Use `ext`. Simplify using `only [Matrix.GeneralLinearGroup.val_det_apply]`. Establish `: (reindexGL e g : Matrix n n R) = (g : Matrix m m R).submatrix e.symm e.symm`. Use extensionality with `i j`. Both sides reduce to the same expression.

Rewrite using `[this, Matrix.det_submatrix_equiv_self]`.
-/
theorem det_reindexGL {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (g : GL m R) : Matrix.GeneralLinearGroup.det (reindexGL e g) = Matrix.GeneralLinearGroup.det g := by
  ext
  simp only [Matrix.GeneralLinearGroup.val_det_apply]
  have : (reindexGL e g : Matrix n n R) = (g : Matrix m m R).submatrix e.symm e.symm := by
    ext i j; rfl
  rw [this, Matrix.det_submatrix_equiv_self]

def liftT (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) (h : GL (Fin t) R) :
    SmGL.Levi R (fun j => Fin (c j)) :=
  Pi.mulSingle (M := fun j => GL (Fin (c j)) R) true (reindexGL (trueEquiv f hc).symm h)

/- English proof (translation)
Use `Units.ext (Matrix.ext fun x y => ?_)` and prove the remaining obligations. Take `⟨⟨a, i⟩, rfl⟩` from `f.surjective x`. Take `⟨⟨b, j⟩, rfl⟩` from `f.surjective y`. Consider the cases of `a with`. Consider the case `false => exact absurd i.2 (by omega)`.

Consider the case `true`. Consider the cases of `b with`. Consider the case `false => exact absurd j.2 (by omega)`. Consider the case `true`. Rewrite using `[SmGL.leviEmb_apply_same]`.

Simplify using `[liftT, val_reindexGL]`.
-/
theorem leviEmb_liftT (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) (h : GL (Fin t) R) :
    SmGL.leviEmb R f (liftT f hc h) = h := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective y
  cases a with
  | false => exact absurd i.2 (by omega)
  | true =>
    cases b with
    | false => exact absurd j.2 (by omega)
    | true =>
      rw [SmGL.leviEmb_apply_same]
      simp [liftT, val_reindexGL]

/- English proof (translation)
Take `⟨-, h2⟩` from `SmGL.mem_unipRad.1 hg`. Use `Units.ext (Matrix.ext fun x y => ?_)` and prove the remaining obligations. Take `⟨⟨a, i⟩, rfl⟩` from `f.surjective x`. Take `⟨⟨b, j⟩, rfl⟩` from `f.surjective y`. Consider the cases of `a with`.

Consider the case `false => exact absurd i.2 (by omega)`. Consider the case `true`. Consider the cases of `b with`. Consider the case `false => exact absurd j.2 (by omega)`. Consider the case `true`.

Rewrite using `[h2 true i j]`. Simplify using `[Matrix.one_apply]`.
-/
theorem eq_one_of_mem_unipRad (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0) {g : GL (Fin t) R}
    (hg : g ∈ SmGL.unipRad R f) : g = 1 := by
  obtain ⟨-, h2⟩ := SmGL.mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := f.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := f.surjective y
  cases a with
  | false => exact absurd i.2 (by omega)
  | true =>
    cases b with
    | false => exact absurd j.2 (by omega)
    | true =>
      rw [h2 true i j]
      simp [Matrix.one_apply]

end Reindex

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {t : ℕ} {c : Bool → ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Use `eq_bot_iff.2 (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨n, v, rfl⟩`. Establish `: (n : GL (Fin t) k) = 1` using `eq_one_of_mem_unipRad f hc n.2`. Simplify using `[this]`.
-/
theorem twKer_eq_bot (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0)
    (π : Representation ℂ (GL (Fin t) k) W) : twKer π (SmGL.unipRad k f) 1 = ⊥ := by
  refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
  rintro _ ⟨n, v, rfl⟩
  have : (n : GL (Fin t) k) = 1 := eq_one_of_mem_unipRad f hc n.2
  simp [this]

/- English proof (translation)
Use `haveI : IsEmpty (Fin (c false)) := by rw [hc]; infer_instance`. Rewrite using `[SmGL.deltaHalf_apply, Fintype.prod_bool]`. Establish `h1 : SmGL.modExp (fun j => Fin (c j)) true = 0`. Simplify using `only [SmGL.modExp, Finset.sum_filter, Fintype.sum_bool]`. Simplify using `[hc]`.

Establish `h2 : Matrix.GeneralLinearGroup.det (g false) = 1` using `by ext; simp [Matrix.det_isEmpty]`. Establish `h0 : SmGL.absPow k 0 = 1`. Use extensionality with `x`. Simplify using `[SmGL.val_absPow]`. Rewrite using `[h1, h2]`.

Simplify using `[h0]`.
-/
theorem deltaHalf_eq_one (hc : c false = 0) (g : SmGL.Levi k (fun j => Fin (c j))) :
    SmGL.deltaHalf k (fun j => Fin (c j)) g = 1 := by
  haveI : IsEmpty (Fin (c false)) := by rw [hc]; infer_instance
  rw [SmGL.deltaHalf_apply, Fintype.prod_bool]
  have h1 : SmGL.modExp (fun j => Fin (c j)) true = 0 := by
    simp only [SmGL.modExp, Finset.sum_filter, Fintype.sum_bool]
    simp [hc]
  have h2 : Matrix.GeneralLinearGroup.det (g false) = 1 := by
    ext; simp [Matrix.det_isEmpty]
  have h0 : SmGL.absPow k 0 = 1 := by
    ext x; simp [SmGL.val_absPow]
  rw [h1, h2]
  simp [h0]

/- English proof (translation)
Rewrite using `[SmGL.jac_mk, deltaHalf_eq_one hc, inv_one, Units.val_one, one_smul, leviEmb_liftT]`.
-/
theorem jac_liftT_mk (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0)
    (π : Representation ℂ (GL (Fin t) k) W) (h : GL (Fin t) k) (w : W) :
    SmGL.jac f π (liftT f hc h) (Submodule.Quotient.mk w) = Submodule.Quotient.mk (π h w) := by
  rw [SmGL.jac_mk, deltaHalf_eq_one hc, inv_one, Units.val_one, one_smul, leviEmb_liftT]

/- English proof (translation)
Set `T : Subrepresentation π` to `⟨S.toSubmodule.comap (twKer π (SmGL.unipRad k f) 1).mkQ, fun h w hw => by show Submodule.Quotient.mk (π h w) ∈ S.toSubmodule`. Rewrite using `[← jac_liftT_mk f hc]`. Conclude with `S.apply_mem_toSubmodule _ hw⟩`. Break down `eq_bot_or_eq_top T with h | h` into its components or cases. Use `left`.

Use `Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun u hu => ?_)` and prove the remaining obligations. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Establish `: w ∈ T.toSubmodule` using `hu`. Rewrite `this` using `[h]`. Establish `hw : w = 0` using `(Submodule.mem_bot ℂ).1 this`.

Rewrite using `[hw]`. Conclude with `Submodule.zero_mem _`. Use `right`. Use `Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun u _ => ?_)` and prove the remaining obligations. Take `⟨w, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`.

Establish `: w ∈ T.toSubmodule` using `by rw [h]; trivial`. Conclude with `this`.
-/
theorem subrep_dichotomy (f : (Σ j, Fin (c j)) ≃ Fin t) (hc : c false = 0)
    {π : Representation ℂ (GL (Fin t) k) W} (hπ : π.IsIrreducible)
    (S : Subrepresentation (SmGL.jac f π)) : S = ⊥ ∨ S = ⊤ := by
  let T : Subrepresentation π := ⟨S.toSubmodule.comap (twKer π (SmGL.unipRad k f) 1).mkQ,
    fun h w hw => by
      show Submodule.Quotient.mk (π h w) ∈ S.toSubmodule
      rw [← jac_liftT_mk f hc]
      exact S.apply_mem_toSubmodule _ hw⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun u hu => ?_)
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have : w ∈ T.toSubmodule := hu
    rw [h] at this
    have hw : w = 0 := (Submodule.mem_bot ℂ).1 this
    rw [hw]
    exact Submodule.zero_mem _
  · right
    refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun u _ => ?_)
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ u
    have : w ∈ T.toSubmodule := by rw [h]; trivial
    exact this

end Main

end GlobalTheory.EmptyFirstBlock

namespace GlobalTheory.EmptyFirstBlock

section Tensor

/- English proof (translation)
Establish `: ∀ i, ∃ φ : Module.Dual ℂ (X i), φ (x i) ≠ 0` using `fun i => by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hx i ((Module.forall_dual_apply_eq_zero_iff ℂ (x i)).1 h)`. Use `choose φ hφ using this`.

Introduce `h0`. Use `congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) h0` as an intermediate fact. Rewrite `this` using `[PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]`. Conclude with `Finset.prod_ne_zero_iff.2 (fun i _ => hφ i) this`.
-/
theorem tprod_ne_zero {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (x : ∀ i, X i) (hx : ∀ i, x i ≠ 0) : PiTensorProduct.tprod ℂ x ≠ 0 := by
  have : ∀ i, ∃ φ : Module.Dual ℂ (X i), φ (x i) ≠ 0 := fun i => by
    by_contra h
    push_neg at h
    exact hx i ((Module.forall_dual_apply_eq_zero_iff ℂ (x i)).1 h)
  choose φ hφ using this
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap φ)) h0
  rw [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] at this
  exact Finset.prod_ne_zero_iff.2 (fun i _ => hφ i) this

end Tensor

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Take `⟨h0, rfl⟩` from `hh`. Conclude with `⟨reindexGL e h0, Units.ext (Matrix.ext fun i j => rfl)⟩`.
-/
theorem reindexGL_mem_KO {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    {h : GL m k} (hh : h ∈ KO k m) : reindexGL e h ∈ KO k n := by
  obtain ⟨h0, rfl⟩ := hh
  exact ⟨reindexGL e h0, Units.ext (Matrix.ext fun i j => rfl)⟩

/- English proof (translation)
Introduce `k _ _ _ _ t W _ _ π c f s χ z _ hπ hc hsub hz0 hz`. Use `haveI := nontrivial_of_irreducible (s false).irr`. Take `⟨w0, hw0⟩` from `exists_ne (0 : (s false).V)`. Set `x : ∀ j, (s j).V` to `fun j => Bool.rec (motive := fun j => (s j).V) w0 z j`. Establish `hx : ∀ j, x j ≠ 0`.

Introduce `j`. Consider the cases of `j`. Conclude with `hw0`. Conclude with `hz0`. Establish `hX : PiTensorProduct.tprod ℂ x ≠ 0` using `tprod_ne_zero x hx`.

Take `⟨S, F, hF⟩` from `hsub`. Break down `subrep_dichotomy f hc hπ S with rfl | rfl` into its components or cases. It suffices to derive a contradiction. Take `⟨u, hu⟩` from `hF (PiTensorProduct.tprod ℂ x)`. Conclude with `hX (by rw [← hu, show u = 0 from Subtype.ext u.2, map_zero])`.

Set `j : (SmGL.jac f π).IntertwiningMap (⊤ : Subrepresentation (SmGL.jac f π)).toRepresentation` to `⟨LinearMap.codRestrict _ LinearMap.id (fun _ => trivial), fun _ => rfl⟩`. Set `G` to `F.comp j`. Establish `hG : Function.Surjective G` using `fun w => by`. Take `⟨u, rfl⟩` from `hF w`. Conclude with `⟨u.1, rfl⟩`.

Establish `hGi : Function.Injective G`. Use `(injective_iff_map_eq_zero G).2 fun y hy => ?_` and prove the remaining obligations. Break down `subrep_dichotomy f hc hπ G.ker with h | h` into its components or cases. Establish `: y ∈ G.ker` using `hy`. Rewrite `this` using `[h]`.

Conclude with `this`. It suffices to derive a contradiction. Take `⟨u, hu⟩` from `hG (PiTensorProduct.tprod ℂ x)`. Establish `: u ∈ G.ker` using `by rw [h]; trivial`. Conclude with `hX (hu ▸ this)`.

Take `⟨u, hu⟩` from `hG (PiTensorProduct.tprod ℂ x)`. Take `⟨v, rfl⟩` from `Submodule.Quotient.mk_surjective _ u`. Establish `hv0 : v ≠ 0`. Introduce and unpack `rfl`. Apply `hX` to reduce the goal to its premises.

Rewrite using `[← hu, Submodule.Quotient.mk_zero, map_zero]`. Establish `key : ∀ h ∈ KO k (Fin t), π h v = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • v`. Introduce `h hh`. Establish `hg' : reindexGL (trueEquiv f hc).symm h ∈ KO k (Fin (c true))` using `reindexGL_mem_KO _ hh`. Establish `hdet` using `det_reindexGL (R := k) (trueEquiv f hc).symm h`.

Establish `htens : (piTensor fun j => (s j).ρ) (liftT f hc h) (PiTensorProduct.tprod ℂ x) = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • PiTensorProduct.tprod ℂ x`. Rewrite using `[piTensor_tprod]`. Establish `hfun : (fun a => (s a).ρ (liftT f hc h a) (x a)) = Function.update x true ((χ (Matrix.GeneralLinearGroup.det h) : ℂ) • x true)`. Use function extensionality and compare the values at `a`. Consider the cases of `a`.

Simplify using `[liftT, x]`. Simplify using `[liftT, x, hz _ hg', hdet]`. Rewrite using `[hfun, MultilinearMap.map_update_smul, Function.update_eq_self]`. Establish `h1 : G (SmGL.jac f π (liftT f hc h) (Submodule.Quotient.mk v)) = G ((χ (Matrix.GeneralLinearGroup.det h) : ℂ) • Submodule.Quotient.mk v)`. Rewrite using `[G.isIntertwining, hu, map_smul, hu, htens]`.

Establish `h2` using `hGi h1`. Rewrite `h2` using `[jac_liftT_mk f hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, twKer_eq_bot f hc, Submodule.mem_bot, sub_eq_zero]`. Conclude with `h2`. Use `show fixed (twist π (detChar (Fin t) χ⁻¹)) (KO k (Fin t)) ≠ ⊥`. Introduce `hbot`.

Establish `hmem : v ∈ fixed (twist π (detChar (Fin t) χ⁻¹)) (KO k (Fin t))`. Introduce `h`. Use `show twist π (detChar (Fin t) χ⁻¹) (h : GL (Fin t) k) v = (((1 : _ →* ℂˣ) h : ℂˣ) : ℂ) • v`. Rewrite using `[twist_apply, key h h.2, smul_smul]`. Simplify using the standard rewrite rules.

Rewrite `hmem` using `[hbot]`. Conclude with `hv0 ((Submodule.mem_bot ℂ).1 hmem)`.
-/
theorem isSpherical_twist_of_empty_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin t) k) W) (c : Bool → ℕ) (f : (Σ j, Fin (c j)) ≃ Fin t) (s : ∀ j, IrrRep (GL (Fin (c j)) k)) (χ : kˣ →* ℂˣ) (z : (s true).V), IsSmooth π → π.IsIrreducible → c false = 0 → IsSubquotient (piTensor fun j => (s j).ρ) (jac f π) → z ≠ 0 → (∀ g ∈ KO k (Fin (c true)), (s true).ρ g z = (χ (Matrix.GeneralLinearGroup.det g) : ℂ) • z) → IsSpherical (twist π (detChar (Fin t) χ⁻¹)) := by
  intro k _ _ _ _ t W _ _ π c f s χ z _ hπ hc hsub hz0 hz
  haveI := nontrivial_of_irreducible (s false).irr
  obtain ⟨w0, hw0⟩ := exists_ne (0 : (s false).V)
  let x : ∀ j, (s j).V := fun j => Bool.rec (motive := fun j => (s j).V) w0 z j
  have hx : ∀ j, x j ≠ 0 := by
    intro j
    cases j
    · exact hw0
    · exact hz0
  have hX : PiTensorProduct.tprod ℂ x ≠ 0 := tprod_ne_zero x hx
  obtain ⟨S, F, hF⟩ := hsub
  rcases subrep_dichotomy f hc hπ S with rfl | rfl
  · exfalso
    obtain ⟨u, hu⟩ := hF (PiTensorProduct.tprod ℂ x)
    exact hX (by rw [← hu, show u = 0 from Subtype.ext u.2, map_zero])
  let j : (SmGL.jac f π).IntertwiningMap (⊤ : Subrepresentation (SmGL.jac f π)).toRepresentation :=
    ⟨LinearMap.codRestrict _ LinearMap.id (fun _ => trivial), fun _ => rfl⟩
  let G := F.comp j
  have hG : Function.Surjective G := fun w => by
    obtain ⟨u, rfl⟩ := hF w
    exact ⟨u.1, rfl⟩
  have hGi : Function.Injective G := by
    refine (injective_iff_map_eq_zero G).2 fun y hy => ?_
    rcases subrep_dichotomy f hc hπ G.ker with h | h
    · have : y ∈ G.ker := hy
      rw [h] at this
      exact this
    · exfalso
      obtain ⟨u, hu⟩ := hG (PiTensorProduct.tprod ℂ x)
      have : u ∈ G.ker := by rw [h]; trivial
      exact hX (hu ▸ this)
  obtain ⟨u, hu⟩ := hG (PiTensorProduct.tprod ℂ x)
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ u
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hX
    rw [← hu, Submodule.Quotient.mk_zero, map_zero]
  have key : ∀ h ∈ KO k (Fin t), π h v = (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • v := by
    intro h hh
    have hg' : reindexGL (trueEquiv f hc).symm h ∈ KO k (Fin (c true)) := reindexGL_mem_KO _ hh
    have hdet := det_reindexGL (R := k) (trueEquiv f hc).symm h
    have htens : (piTensor fun j => (s j).ρ) (liftT f hc h) (PiTensorProduct.tprod ℂ x) =
        (χ (Matrix.GeneralLinearGroup.det h) : ℂ) • PiTensorProduct.tprod ℂ x := by
      rw [piTensor_tprod]
      have hfun : (fun a => (s a).ρ (liftT f hc h a) (x a)) =
          Function.update x true ((χ (Matrix.GeneralLinearGroup.det h) : ℂ) • x true) := by
        funext a
        cases a
        · simp [liftT, x]
        · simp [liftT, x, hz _ hg', hdet]
      rw [hfun, MultilinearMap.map_update_smul, Function.update_eq_self]
    have h1 : G (SmGL.jac f π (liftT f hc h) (Submodule.Quotient.mk v)) =
        G ((χ (Matrix.GeneralLinearGroup.det h) : ℂ) • Submodule.Quotient.mk v) := by
      rw [G.isIntertwining, hu, map_smul, hu, htens]
    have h2 := hGi h1
    rw [jac_liftT_mk f hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, twKer_eq_bot f hc,
      Submodule.mem_bot, sub_eq_zero] at h2
    exact h2
  show fixed (twist π (detChar (Fin t) χ⁻¹)) (KO k (Fin t)) ≠ ⊥
  intro hbot
  have hmem : v ∈ fixed (twist π (detChar (Fin t) χ⁻¹)) (KO k (Fin t)) := by
    intro h
    show twist π (detChar (Fin t) χ⁻¹) (h : GL (Fin t) k) v = (((1 : _ →* ℂˣ) h : ℂˣ) : ℂ) • v
    rw [twist_apply, key h h.2, smul_smul]
    simp
  rw [hbot] at hmem
  exact hv0 ((Submodule.mem_bot ℂ).1 hmem)

end GlobalTheory.EmptyFirstBlock
