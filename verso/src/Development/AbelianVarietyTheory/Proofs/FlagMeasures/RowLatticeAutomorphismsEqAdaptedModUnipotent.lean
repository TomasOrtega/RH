import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UnitriangularLatticeStabiliserSubFrameAutomorphi
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfUnimodular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticesSameInnerDifferByRationalUnipotentStatement
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AutLzFinite
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.LiftsConjugateUnderStabilizer
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsLatticeRepresentativeNormalisedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryUnitriangularizingFlagStabilizerStatement

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AutQuot

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mul_apply' (a b : GV D) (x : (VS D).V) : (a * b) x = a (b x) := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem inv_apply' (a : GV D) (x : (VS D).V) : a⁻¹ x = a.symm x := rfl

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun k (hk : k.1 < i) => lt_of_lt_of_le hk h)`.
-/
theorem Xa_mono {i j : ℕ} (h : i ≤ j) : F0.Xa i ≤ F0.Xa j :=
  Submodule.span_mono (Set.image_mono fun k (hk : k.1 < i) => lt_of_lt_of_le hk h)

/- English proof (translation)
Unfold `FlagG.Xa FlagG.X`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem Xa_top : F0.Xa D.R.rS = F0.X := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext x
  simp

/- English proof (translation)
Simplify using `[frame, FlagG.fvec]`.
-/
theorem frame_cs (i : Fin D.R.rS) : frame (lf D F0) i.castSucc = F0.e i := by
  simp [frame, FlagG.fvec]

/- English proof (translation)
Simplify using `[frame, FlagG.fvec]`.
-/
theorem frame_last : frame (lf D F0) (Fin.last _) = F0.z := by
  simp [frame, FlagG.fvec]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_perpS {U : Submodule D.host.E (VS D).V} {y : (VS D).V} :
    y ∈ perpS (VS D) U ↔ ∀ x ∈ U, (VS D).hT x y = 0 := Iff.rfl

/- English proof (translation)
Use extensionality with `y`. Simplify using `[orth, Submodule.mem_iInf, mem_perpS]`.
-/
theorem orth_eq (U : Submodule D.host.E (VS D).V) : orth (VS D) U = perpS (VS D) U := by
  ext y
  simp [orth, Submodule.mem_iInf, mem_perpS]

/- English proof (translation)
Introduce `x hx`. Use `Submodule.span_induction (p := fun x _ => (VS D).hT x F0.z = 0) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `F0.z_orth a`. Simplify using the standard rewrite rules.

Introduce `x y _ _ ha hb`. Simplify using `[ha, hb]`. Introduce `c x _ ha`. Simplify using `[ha]`.
-/
theorem z_perp : F0.z ∈ perpS (VS D) F0.X := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => (VS D).hT x F0.z = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩; exact F0.z_orth a
  · simp
  · intro x y _ _ ha hb; simp [ha, hb]
  · intro c x _ ha; simp [ha]

/- English proof (translation)
Introduce `y hy x hx`. Use `Submodule.span_induction (p := fun x _ => (VS D).hT x y = 0) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Use `Submodule.span_induction (p := fun y _ => (VS D).hT (F0.e a) y = 0) ?_ ?_ ?_ ?_ hy` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`.

Conclude with `F0.e_iso a b`. Simplify using the standard rewrite rules. Introduce `x y _ _ ha hb`. Simplify using `[ha, hb]`. Introduce `c x _ ha`.

Simplify using `[ha]`. Simplify using the standard rewrite rules. Introduce `x y _ _ ha hb`. Simplify using `[ha, hb]`. Introduce `c x _ ha`.

Simplify using `[ha]`.
-/
theorem X_le_perp : F0.X ≤ perpS (VS D) F0.X := by
  intro y hy x hx
  refine Submodule.span_induction (p := fun x _ => (VS D).hT x y = 0) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨a, rfl⟩
    refine Submodule.span_induction (p := fun y _ => (VS D).hT (F0.e a) y = 0) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨b, rfl⟩; exact F0.e_iso a b
    · simp
    · intro x y _ _ ha hb; simp [ha, hb]
    · intro c x _ ha; simp [ha]
  · simp
  · intro x y _ _ ha hb; simp [ha, hb]
  · intro c x _ ha; simp [ha]

/- English proof (translation)
Set `f : A →ₗ[D.host.E] A` to `(g : (VS D).V →ₗ[D.host.E] (VS D).V).restrict h`. Establish `hi : Function.Injective f`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `g.injective` to reduce the goal to its premises.

Simplify `congrArg Subtype.val hab` using `[f]`. Introduce `x hx`. Take `⟨y, hy⟩` from `(LinearMap.injective_iff_surjective.mp hi) ⟨x, hx⟩`. Establish `: g y.1 = x` using `by simpa [f] using congrArg Subtype.val hy`. Rewrite using `[← this, LinearEquiv.symm_apply_apply]`.

Conclude with `y.2`.
-/
theorem symm_mapsTo (g : GV D) (A : Submodule D.host.E (VS D).V) (h : ∀ x ∈ A, g x ∈ A) :
    ∀ x ∈ A, g.symm x ∈ A := by
  let f : A →ₗ[D.host.E] A := (g : (VS D).V →ₗ[D.host.E] (VS D).V).restrict h
  have hi : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply g.injective
    simpa [f] using congrArg Subtype.val hab
  intro x hx
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hi) ⟨x, hx⟩
  have : g y.1 = x := by simpa [f] using congrArg Subtype.val hy
  rw [← this, LinearEquiv.symm_apply_apply]; exact y.2

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `h x hx`. Introduce `y hy`. Conclude with `⟨g.symm y, symm_mapsTo g A h y hy, by simp⟩`.
-/
theorem map_eq_of_mapsTo (g : GV D) (A : Submodule D.host.E (VS D).V) (h : ∀ x ∈ A, g x ∈ A) :
    A.map (g : (VS D).V →ₗ[D.host.E] (VS D).V) = A := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩; exact h x hx
  · intro y hy
    exact ⟨g.symm y, symm_mapsTo g A h y hy, by simp⟩

/- English proof (translation)
Establish `hg' : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y` using `hg`. Introduce `y hy x hx`. Establish `hx'` using `symm_mapsTo g U hU x hx`. Use `hg' (g.symm x) y` as an intermediate fact. Rewrite `this` using `[LinearEquiv.apply_symm_apply]`.

Rewrite using `[this]`. Conclude with `hy _ hx'`.
-/
theorem isom_mapsTo_perp {g : GV D} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) {U : Submodule D.host.E (VS D).V}
    (hU : ∀ x ∈ U, g x ∈ U) : ∀ y ∈ perpS (VS D) U, g y ∈ perpS (VS D) U := by
  have hg' : ∀ x y, (VS D).hT (g x) (g y) = (VS D).hT x y := hg
  intro y hy x hx
  have hx' := symm_mapsTo g U hU x hx
  have := hg' (g.symm x) y
  rw [LinearEquiv.apply_symm_apply] at this
  rw [this]; exact hy _ hx'

/- English proof (translation)
Introduce `x hx`. Use `Submodule.span_induction (p := fun x _ => g x ∈ F0.Xa j) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Establish `h1 : g (F0.e i) - F0.e i ∈ F0.Xa i.1` using `by simpa [frame_cs] using hg.2 i.castSucc`. Establish `h2 : g (F0.e i) = F0.e i + (g (F0.e i) - F0.e i)` using `by abel`.

Rewrite using `[h2]`. Conclude with `add_mem (Submodule.subset_span ⟨i, hi, rfl⟩) (Xa_mono F0 (le_of_lt hi) h1)`. Simplify using the standard rewrite rules. Introduce `x y _ _ ha hb`. Simplify using `using add_mem ha hb`.

Introduce `c x _ ha`. Simplify using `using Submodule.smul_mem _ c ha`.
-/
theorem adapt_mapsTo {g : GV D} (hg : Adapt g (lf D F0) (lf D F0)) (j : ℕ) :
    ∀ x ∈ F0.Xa j, g x ∈ F0.Xa j := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => g x ∈ F0.Xa j) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨i, hi, rfl⟩
    have h1 : g (F0.e i) - F0.e i ∈ F0.Xa i.1 := by simpa [frame_cs] using hg.2 i.castSucc
    have h2 : g (F0.e i) = F0.e i + (g (F0.e i) - F0.e i) := by abel
    rw [h2]
    exact add_mem (Submodule.subset_span ⟨i, hi, rfl⟩) (Xa_mono F0 (le_of_lt hi) h1)
  · simp
  · intro x y _ _ ha hb; simpa using add_mem ha hb
  · intro c x _ ha; simpa using Submodule.smul_mem _ c ha

/- English proof (translation)
Establish `h` using `hg.2 (Fin.last _)`. Rewrite `h` using `[frame_last]`. Simplify `h` using `[Xflag, Fin.val_last, Xa_top]`.
-/
theorem frameAdaptedIsometry_vector_sub_mem_flag {g : GV D} (hg : Adapt g (lf D F0) (lf D F0)) : g F0.z - F0.z ∈ F0.X := by
  have h := hg.2 (Fin.last _)
  rw [frame_last] at h
  simpa [Xflag, Fin.val_last, Xa_top] using h

end GlobalTheory.AutQuot

namespace GlobalTheory.AutQuot
variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D)

def A0 : Subgroup (GV D) where
  carrier := Aut0 (lf D F0) Λ
  one_mem' := ⟨GlobalTheory.Unfold.Model.adapt_one _, GlobalTheory.Unfold.Model.gmap_one Λ⟩
  mul_mem' := by
    rintro a b ⟨ha, hΛa⟩ ⟨hb, hΛb⟩
    refine ⟨⟨Subgroup.mul_mem _ ha.1 hb.1, fun k => ?_⟩, by rw [GlobalTheory.Unfold.Model.gmap_mul, hΛb, hΛa]⟩
    have e : (a * b) (frame (lf D F0) k) - frame (lf D F0) k =
        a (b (frame (lf D F0) k) - frame (lf D F0) k) + (a (frame (lf D F0) k) - frame (lf D F0) k) := by
      rw [mul_apply', map_sub]; abel
    rw [e]
    exact add_mem (adapt_mapsTo F0 ha _ _ (hb.2 k)) (ha.2 k)
  inv_mem' := by
    rintro a ⟨ha, hΛa⟩
    refine ⟨⟨Subgroup.inv_mem _ ha.1, fun k => ?_⟩, ?_⟩
    · have e : a⁻¹ (frame (lf D F0) k) - frame (lf D F0) k =
          a.symm (-(a (frame (lf D F0) k) - frame (lf D F0) k)) := by
        rw [inv_apply', map_neg, map_sub, LinearEquiv.symm_apply_apply]; abel
      rw [e]
      exact symm_mapsTo a _ (adapt_mapsTo F0 ha _) _ (neg_mem (ha.2 k))
    · conv_lhs => rw [← hΛa]
      rw [← GlobalTheory.Unfold.Model.gmap_mul, inv_mul_cancel, GlobalTheory.Unfold.Model.gmap_one]

variable {F0 Λ}

/- English proof (translation)
Rewrite using `[← Xa_top]`. Conclude with `adapt_mapsTo F0 ha.1 _`.
-/
theorem adaptedLatticeAutomorphism_mapsTo_flag {a : GV D} (ha : a ∈ A0 F0 Λ) : ∀ x ∈ F0.X, a x ∈ F0.X := by
  rw [← Xa_top]; exact adapt_mapsTo F0 ha.1 _

/- English proof (translation)
The claim follows from `isom_mapsTo_perp ha.1.1 (adaptedLatticeAutomorphism_mapsTo_flag ha)`.
-/
theorem adaptedLatticeAutomorphism_mapsTo_perp {a : GV D} (ha : a ∈ A0 F0 Λ) : ∀ y ∈ perpS (VS D) F0.X, a y ∈ perpS (VS D) F0.X :=
  isom_mapsTo_perp ha.1.1 (adaptedLatticeAutomorphism_mapsTo_flag ha)

variable (F0)

def indL {a : GV D} (hP : ∀ y ∈ perpS (VS D) F0.X, a y ∈ perpS (VS D) F0.X) (hX : ∀ x ∈ F0.X, a x ∈ F0.X) :
    Module.End D.host.E (WbQ D F0) :=
  (F0.X.comap (perpS (VS D) F0.X).subtype).mapQ (F0.X.comap (perpS (VS D) F0.X).subtype)
    ((a : (VS D).V →ₗ[D.host.E] (VS D).V).restrict hP) (fun x hx => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype] at hx ⊢
      simpa using hX _ hx)

/- English proof (translation)
Rewrite using `[Submodule.Quotient.eq]`. Simplify using the standard rewrite rules.
-/
theorem mk_eq_iff (x y : perpS (VS D) F0.X) :
    (Submodule.Quotient.mk x : WbQ D F0) = Submodule.Quotient.mk y ↔ x.1 - y.1 ∈ F0.X := by
  rw [Submodule.Quotient.eq]; simp

variable (Λ)

def ind : A0 F0 Λ →* Module.End D.host.E (WbQ D F0) where
  toFun a := indL F0 (adaptedLatticeAutomorphism_mapsTo_perp a.2) (adaptedLatticeAutomorphism_mapsTo_flag a.2)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    rfl
  map_mul' a b := by
    apply Submodule.linearMap_qext
    ext x
    rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ind_apply_mk (a : A0 F0 Λ) (x : perpS (VS D) F0.X) :
    ind F0 Λ a (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨(a : GV D) x.1, adaptedLatticeAutomorphism_mapsTo_perp a.2 x.1 x.2⟩ := rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h y hy`. Use `congrArg (fun f : Module.End D.host.E (WbQ D F0) => f (Submodule.Quotient.mk ⟨y, hy⟩)) h` as an intermediate fact. Simplify using `only [ind_apply_mk, Module.End.one_apply] at this`. Conclude with `(mk_eq_iff F0 _ _).1 this`.

Introduce `h`. Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]`. Rewrite using `[ind_apply_mk, Module.End.one_apply, mk_eq_iff]`.

Conclude with `h _ x.2`.
-/
theorem ind_eq_one_iff (a : A0 F0 Λ) : ind F0 Λ a = 1 ↔ ∀ y ∈ perpS (VS D) F0.X, (a : GV D) y - y ∈ F0.X := by
  constructor
  · intro h y hy
    have := congrArg (fun f : Module.End D.host.E (WbQ D F0) => f (Submodule.Quotient.mk ⟨y, hy⟩)) h
    simp only [ind_apply_mk, Module.End.one_apply] at this
    exact (mk_eq_iff F0 _ _).1 this
  · intro h
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [ind_apply_mk, Module.End.one_apply, mk_eq_iff]
    exact h _ x.2

end GlobalTheory.AutQuot

namespace GlobalTheory.AutQuot
variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hn`. Conclude with `⟨GlobalTheory.Unfold.Model.unitriangular_lattice_stabiliser_sub_frame_automorphisms _ _ hn, fun y hy => hn.2.2 y (by rw [orth_eq]; exact hy)⟩`. Introduce and unpack `⟨ha, h⟩`. Use `⟨⟨ha.1.1, ha.2⟩, fun j x hx => ?_, fun y hy => h y (by rw [orth_eq] at hy; exact hy)⟩` and prove the remaining obligations.

Use `Submodule.span_induction (p := fun x _ => n x - x ∈ F0.Xa j) ?_ ?_ ?_ ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Establish `h1 : n (F0.e i) - F0.e i ∈ F0.Xa i.1` using `by simpa [frame_cs] using ha.1.2 i.castSucc`. Conclude with `Xa_mono F0 (Nat.lt_succ_iff.mp hi) h1`. Simplify using the standard rewrite rules.

Introduce `x y _ _ hx hy`. Use `add_mem hx hy` as an intermediate fact. Rewrite using `[map_add, add_sub_add_comm]` and apply the resulting hypothesis. Introduce `c x _ hx`. Rewrite using `[map_smul, ← smul_sub]`.

Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem mem_NLam_iff (n : GV D) :
    n ∈ NLam Λ (lf D F0) ↔ n ∈ A0 F0 Λ ∧ ∀ y ∈ perpS (VS D) F0.X, n y - y ∈ F0.X := by
  constructor
  · intro hn
    exact ⟨GlobalTheory.Unfold.Model.unitriangular_lattice_stabiliser_sub_frame_automorphisms _ _ hn, fun y hy => hn.2.2 y (by rw [orth_eq]; exact hy)⟩
  · rintro ⟨ha, h⟩
    refine ⟨⟨ha.1.1, ha.2⟩, fun j x hx => ?_, fun y hy => h y (by rw [orth_eq] at hy; exact hy)⟩
    refine Submodule.span_induction (p := fun x _ => n x - x ∈ F0.Xa j) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, hi, rfl⟩
      have h1 : n (F0.e i) - F0.e i ∈ F0.Xa i.1 := by simpa [frame_cs] using ha.1.2 i.castSucc
      exact Xa_mono F0 (Nat.lt_succ_iff.mp hi) h1
    · simp
    · intro x y _ _ hx hy
      have := add_mem hx hy
      rwa [map_add, add_sub_add_comm]
    · intro c x _ hx
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ c hx

variable {F0 Λ}

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[← Xa_top]`. Rewrite using `[← hγ.2.1 D.R.rS]`. Conclude with `⟨x, hx, rfl⟩`.
-/
theorem stab_mapsX {γ : GV D} (hγ : γ ∈ stabF D F0) : ∀ x ∈ F0.X, γ x ∈ F0.X := by
  intro x hx
  rw [← Xa_top] at hx ⊢
  rw [← hγ.2.1 D.R.rS]
  exact ⟨x, hx, rfl⟩

/- English proof (translation)
The claim follows from `isom_mapsTo_perp hγ.1 (stab_mapsX hγ)`.
-/
theorem stab_mapsP {γ : GV D} (hγ : γ ∈ stabF D F0) : ∀ y ∈ perpS (VS D) F0.X, γ y ∈ perpS (VS D) F0.X :=
  isom_mapsTo_perp hγ.1 (stab_mapsX hγ)

/- English proof (translation)
Take `⟨σ, hσ, hσz⟩` from `GlobalTheory.T.exists_lattice_representative_normalised D T F0 Λ hΛ`. Take `⟨-, ⟨-, hU, ⟨hzΛ, -⟩, -⟩, -⟩` from `hΛ`. Establish `hzΛ' : F0.z ∈ Λ` using `hzΛ`. Establish `hx0X : a F0.z - F0.z ∈ F0.X` using `frameAdaptedIsometry_vector_sub_mem_flag F0 ha.1`. Establish `haz : a F0.z ∈ Λ`.

Establish `: a F0.z ∈ Formalism.HermitianLatticesTheory.gmap a Λ` using `⟨F0.z, hzΛ', rfl⟩`. Rewrite `this` using `[ha.2]`. Then use the resulting hypothesis. Establish `hx0L : a F0.z - F0.z ∈ XLam Λ (lf D F0)` using `⟨Λ.sub_mem haz hzΛ', hx0X⟩`. Take `⟨n, hn, t, hnX, hnf⟩` from `GlobalTheory.EichlerUnip.eichler_mem_unipotent D T (lf D F0) Λ hU σ hσ (a F0.z - F0.z) hx0L`. Establish `hx0z : (hS D).hT (a F0.z - F0.z) F0.z = 0` using `z_perp F0 _ hx0X`.

Establish `hσz' : (hS D).hT σ F0.z = 1` using `hσz`. Establish `hnz : n (a F0.z) = F0.z`. Establish `e : a F0.z = F0.z + (a F0.z - F0.z)` using `by abel`. Rewrite using `[e, map_add, hnX _ hx0X, hnf F0.z, hσz', hx0z]`. Simplify using the standard rewrite rules.

Establish `hnA` using `(mem_NLam_iff F0 Λ n).1 hn`. Use `⟨n * a, ⟨Subgroup.mul_mem _ hnA.1.1.1 ha.1.1, fun j => ?_, by rw [mul_apply', hnz]⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `map_eq_of_mapsTo _ _ fun x hx => adapt_mapsTo F0 hnA.1.1 j _ (adapt_mapsTo F0 ha.1 j x hx)`. Rewrite using `[GlobalTheory.Unfold.Model.gmap_mul, ha.2, hnA.1.2]`. Introduce `y hy`.

Conclude with `hnA.2 _ (adaptedLatticeAutomorphism_mapsTo_perp ha y hy)`.
-/
theorem lift_fix (hΛ : IsRowLat D F0 Λ) {a : GV D} (ha : a ∈ A0 F0 Λ) :
    ∃ γ ∈ stabF D F0, Formalism.HermitianLatticesTheory.gmap γ Λ = Λ ∧ ∀ y ∈ perpS (VS D) F0.X, γ y - a y ∈ F0.X := by
  obtain ⟨σ, hσ, hσz⟩ := GlobalTheory.T.exists_lattice_representative_normalised D T F0 Λ hΛ
  obtain ⟨-, ⟨-, hU, ⟨hzΛ, -⟩, -⟩, -⟩ := hΛ
  have hzΛ' : F0.z ∈ Λ := hzΛ
  have hx0X : a F0.z - F0.z ∈ F0.X := frameAdaptedIsometry_vector_sub_mem_flag F0 ha.1
  have haz : a F0.z ∈ Λ := by
    have : a F0.z ∈ Formalism.HermitianLatticesTheory.gmap a Λ := ⟨F0.z, hzΛ', rfl⟩
    rwa [ha.2] at this
  have hx0L : a F0.z - F0.z ∈ XLam Λ (lf D F0) := ⟨Λ.sub_mem haz hzΛ', hx0X⟩
  obtain ⟨n, hn, t, hnX, hnf⟩ :=
    GlobalTheory.EichlerUnip.eichler_mem_unipotent D T (lf D F0) Λ hU σ hσ (a F0.z - F0.z) hx0L
  have hx0z : (hS D).hT (a F0.z - F0.z) F0.z = 0 := z_perp F0 _ hx0X
  have hσz' : (hS D).hT σ F0.z = 1 := hσz
  have hnz : n (a F0.z) = F0.z := by
    have e : a F0.z = F0.z + (a F0.z - F0.z) := by abel
    rw [e, map_add, hnX _ hx0X, hnf F0.z, hσz', hx0z]
    simp
  have hnA := (mem_NLam_iff F0 Λ n).1 hn
  refine ⟨n * a, ⟨Subgroup.mul_mem _ hnA.1.1.1 ha.1.1, fun j => ?_, by rw [mul_apply', hnz]⟩, ?_, ?_⟩
  · exact map_eq_of_mapsTo _ _ fun x hx => adapt_mapsTo F0 hnA.1.1 j _ (adapt_mapsTo F0 ha.1 j x hx)
  · rw [GlobalTheory.Unfold.Model.gmap_mul, ha.2, hnA.1.2]
  · intro y hy
    exact hnA.2 _ (adaptedLatticeAutomorphism_mapsTo_perp ha y hy)

/- English proof (translation)
Take `⟨t, ht, htP, hσ⟩` from `GlobalTheory.T.exists_isometry_unitriangularizing_flag_stabilizer D T F0 γ hγ`. Establish `hγX` using `stab_mapsX hγ`. Establish `hγP` using `stab_mapsP hγ`. Establish `htX : ∀ x ∈ F0.X, t x ∈ F0.X` using `fun x hx => by`. Use `add_mem (htP x (X_le_perp F0 hx)) hx` as an intermediate fact.

Simplify using `using this`. Establish `htP' : ∀ y ∈ perpS (VS D) F0.X, t y ∈ perpS (VS D) F0.X` using `fun y hy => by`. Use `add_mem (X_le_perp F0 (htP y hy)) hy` as an intermediate fact. Simplify using `using this`. Establish `hσX : F0.X.map ((t * γ : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X` using `map_eq_of_mapsTo _ _ (fun x hx => htX _ (hγX x hx))`.

Establish `hγX' : F0.X.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X` using `map_eq_of_mapsTo _ _ hγX`. Establish `hL : Lsub (Formalism.HermitianLatticesTheory.gmap (t * γ) Λ) (lf D F0) = Lsub Λ (lf D F0)`. Apply the tactic sequence `rw [Formalism.MainNotions.BridgeLemma₂.Lsub_gmap_of_isometry F0 _ hσ.1 hσX, GlobalTheory.Unfold.Model.gmap_mul, ← Formalism.MainNotions.BridgeLemma₂.Lsub_gmap_of_isometry F0 _ hγ.1 hγX', hγΛ]`. Establish `hXL` using `Formalism.MainNotions.BridgeLemma₂.isotropic_le_Lsub F0 Λ`. Establish `hLP : ∀ y ∈ Lsub Λ (lf D F0), y ∈ perpS (VS D) F0.X` using `fun y hy => by`.

Use `hy.2` as an intermediate fact. Rewrite `this` using `[orth_eq]`. Conclude with `this`. Use extensionality with `y`. Rewrite using `[GlobalTheory.Unfold.Model.mem_gmap]`.

Prove the components needed by the constructor for the conclusion. Introduce `hw`. Establish `hwP` using `hLP _ hw`. Establish `e : y = t.symm y + (t (t.symm y) - t.symm y)` using `by simp`. Rewrite using `[e]`.

Conclude with `add_mem hw (hXL (htP _ hwP))`. Introduce `hy`. Establish `hyP` using `hLP _ hy`. Establish `hwP` using `symm_mapsTo t _ htP' y hyP`. Establish `e : t.symm y = y - (t (t.symm y) - t.symm y)` using `by simp`.

Rewrite using `[e]`. Conclude with `sub_mem hy (hXL (htP _ hwP))`. Take `⟨n, hn, hnΛ⟩` from `GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D T F0 Λ Λ (t * γ) hΛ hΛ hσ hL`. Use `⟨n * (t * γ), ⟨⟨Subgroup.mul_mem _ hn.1 hσ.1, fun k => ?_⟩, hnΛ⟩, fun y hy => ?_⟩` and prove the remaining obligations. Establish `e : (n * (t * γ)) (frame (lf D F0) k) - frame (lf D F0) k = (n ((t * γ) (frame (lf D F0) k)) - (t * γ) (frame (lf D F0) k)) + ((t * γ) (frame (lf D F0) k) - frame (lf D F0) k)`.

Rewrite using `[mul_apply']`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `add_mem ?_ (hσ.2 k)` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun i => ?_) k` and prove the remaining obligations.

Rewrite using `[frame_last]`. Establish `hz : (t * γ) F0.z ∈ orth (VS D) (Xsp (lf D F0))`. Rewrite using `[orth_eq]`. Use `add_mem (X_le_perp F0 (frameAdaptedIsometry_vector_sub_mem_flag F0 hσ)) (z_perp F0)` as an intermediate fact. Simplify using `using this`.

Use `hn.2.2 _ hz` as an intermediate fact. Use `show _ ∈ F0.Xa (Fin.last D.R.rS).val`. Rewrite using `[Fin.val_last, Xa_top]`. Conclude with `this`. Rewrite using `[frame_cs]`.

Establish `he : (t * γ) (F0.e i) ∈ F0.Xa (i.1 + 1)` using `adapt_mapsTo F0 hσ _ _ (Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)`. Use `hn.2.1 i.1 _ he` as an intermediate fact. Simplify using `using this`. Establish `e : (n * (t * γ)) y - γ y = (n (t (γ y)) - t (γ y)) + (t (γ y) - γ y)`. Rewrite using `[mul_apply', mul_apply']`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `add_mem (hn.2.2 _ ?_) (htP _ (hγP y hy))` and prove the remaining obligations. Rewrite using `[orth_eq]`. Conclude with `htP' _ (hγP y hy)`.
-/
theorem stab_fix (hΛ : IsRowLat D F0 Λ) {γ : GV D} (hγ : γ ∈ stabF D F0) (hγΛ : Formalism.HermitianLatticesTheory.gmap γ Λ = Λ) :
    ∃ a ∈ A0 F0 Λ, ∀ y ∈ perpS (VS D) F0.X, a y - γ y ∈ F0.X := by
  obtain ⟨t, ht, htP, hσ⟩ := GlobalTheory.T.exists_isometry_unitriangularizing_flag_stabilizer D T F0 γ hγ
  have hγX := stab_mapsX hγ
  have hγP := stab_mapsP hγ
  have htX : ∀ x ∈ F0.X, t x ∈ F0.X := fun x hx => by
    have := add_mem (htP x (X_le_perp F0 hx)) hx
    simpa using this
  have htP' : ∀ y ∈ perpS (VS D) F0.X, t y ∈ perpS (VS D) F0.X := fun y hy => by
    have := add_mem (X_le_perp F0 (htP y hy)) hy
    simpa using this
  have hσX : F0.X.map ((t * γ : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X :=
    map_eq_of_mapsTo _ _ (fun x hx => htX _ (hγX x hx))
  have hγX' : F0.X.map (γ : (VS D).V →ₗ[D.host.E] (VS D).V) = F0.X := map_eq_of_mapsTo _ _ hγX
  have hL : Lsub (Formalism.HermitianLatticesTheory.gmap (t * γ) Λ) (lf D F0) = Lsub Λ (lf D F0) := by
    rw [Formalism.MainNotions.BridgeLemma₂.Lsub_gmap_of_isometry F0 _ hσ.1 hσX, GlobalTheory.Unfold.Model.gmap_mul,
      ← Formalism.MainNotions.BridgeLemma₂.Lsub_gmap_of_isometry F0 _ hγ.1 hγX', hγΛ]
    have hXL := Formalism.MainNotions.BridgeLemma₂.isotropic_le_Lsub F0 Λ
    have hLP : ∀ y ∈ Lsub Λ (lf D F0), y ∈ perpS (VS D) F0.X := fun y hy => by
      have := hy.2; rw [orth_eq] at this; exact this
    ext y
    rw [GlobalTheory.Unfold.Model.mem_gmap]
    constructor
    · intro hw
      have hwP := hLP _ hw
      have e : y = t.symm y + (t (t.symm y) - t.symm y) := by simp
      rw [e]
      exact add_mem hw (hXL (htP _ hwP))
    · intro hy
      have hyP := hLP _ hy
      have hwP := symm_mapsTo t _ htP' y hyP
      have e : t.symm y = y - (t (t.symm y) - t.symm y) := by simp
      rw [e]
      exact sub_mem hy (hXL (htP _ hwP))
  obtain ⟨n, hn, hnΛ⟩ := GlobalTheory.T.row_lattices_same_inner_differ_by_rational_unipotent D T F0 Λ Λ (t * γ) hΛ hΛ hσ hL
  refine ⟨n * (t * γ), ⟨⟨Subgroup.mul_mem _ hn.1 hσ.1, fun k => ?_⟩, hnΛ⟩, fun y hy => ?_⟩
  · have e : (n * (t * γ)) (frame (lf D F0) k) - frame (lf D F0) k =
        (n ((t * γ) (frame (lf D F0) k)) - (t * γ) (frame (lf D F0) k)) +
          ((t * γ) (frame (lf D F0) k) - frame (lf D F0) k) := by
      rw [mul_apply']; abel
    rw [e]
    refine add_mem ?_ (hσ.2 k)
    refine Fin.lastCases ?_ (fun i => ?_) k
    · rw [frame_last]
      have hz : (t * γ) F0.z ∈ orth (VS D) (Xsp (lf D F0)) := by
        rw [orth_eq]
        have := add_mem (X_le_perp F0 (frameAdaptedIsometry_vector_sub_mem_flag F0 hσ)) (z_perp F0)
        simpa using this
      have := hn.2.2 _ hz
      show _ ∈ F0.Xa (Fin.last D.R.rS).val
      rw [Fin.val_last, Xa_top]
      exact this
    · rw [frame_cs]
      have he : (t * γ) (F0.e i) ∈ F0.Xa (i.1 + 1) :=
        adapt_mapsTo F0 hσ _ _ (Submodule.subset_span ⟨i, Nat.lt_succ_self _, rfl⟩)
      have := hn.2.1 i.1 _ he
      simpa using this
  · have e : (n * (t * γ)) y - γ y = (n (t (γ y)) - t (γ y)) + (t (γ y) - γ y) := by
      rw [mul_apply', mul_apply']; abel
    rw [e]
    refine add_mem (hn.2.2 _ ?_) (htP _ (hγP y hy))
    rw [orth_eq]; exact htP' _ (hγP y hy)

end GlobalTheory.AutQuot

namespace GlobalTheory.AutQuot
variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (Λ : LV D)

def indU : A0 F0 Λ →* (Module.End D.host.E (WbQ D F0))ˣ := (ind F0 Λ).toHomUnits

def NU : Subgroup (GV D) := (indU F0 Λ).ker.map (A0 F0 Λ).subtype

/- English proof (translation)
Rewrite using `[MonoidHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg Units.val h` as an intermediate fact. Simplify `this` using `[indU]`.

Introduce `h ext1`. Simplify `h` using `[indU]`.
-/
theorem mem_ker_iff (a : A0 F0 Λ) : a ∈ (indU F0 Λ).ker ↔ ind F0 Λ a = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    have := congrArg Units.val h
    simpa [indU] using this
  · intro h
    ext1
    simpa [indU] using h

/- English proof (translation)
Use extensionality with `n`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Conclude with `(mem_NLam_iff F0 Λ _).2 ⟨a.2, (ind_eq_one_iff F0 Λ a).1 ((mem_ker_iff F0 Λ a).1 ha)⟩`. Introduce `hn`.

Establish `h` using `(mem_NLam_iff F0 Λ n).1 hn`. Conclude with `⟨⟨n, h.1⟩, (mem_ker_iff F0 Λ _).2 ((ind_eq_one_iff F0 Λ ⟨n, h.1⟩).2 h.2), rfl⟩`.
-/
theorem NU_coe : (NU F0 Λ : Set (GV D)) = NLam Λ (lf D F0) := by
  ext n
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (mem_NLam_iff F0 Λ _).2 ⟨a.2, (ind_eq_one_iff F0 Λ a).1 ((mem_ker_iff F0 Λ a).1 ha)⟩
  · intro hn
    have h := (mem_NLam_iff F0 Λ n).1 hn
    exact ⟨⟨n, h.1⟩, (mem_ker_iff F0 Λ _).2 ((ind_eq_one_iff F0 Λ ⟨n, h.1⟩).2 h.2), rfl⟩

/- English proof (translation)
Use extensionality with `a`. Rewrite using `[Subgroup.mem_subgroupOf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, e⟩`. Establish `: b = a` using `Subtype.ext e`.

Rewrite using `[← this]` and apply the resulting hypothesis. Introduce `ha`. Conclude with `⟨a, ha, rfl⟩`.
-/
theorem NU_subgroupOf : (NU F0 Λ).subgroupOf (A0 F0 Λ) = (indU F0 Λ).ker := by
  ext a
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨b, hb, e⟩
    have : b = a := Subtype.ext e
    rwa [← this]
  · intro ha
    exact ⟨a, ha, rfl⟩

/- English proof (translation)
Introduce and unpack `a ha _ ⟨k, hk, rfl⟩`. Establish `hk' : (⟨a, ha⟩ : A0 F0 Λ) * k * (⟨a, ha⟩ : A0 F0 Λ)⁻¹ ∈ (indU F0 Λ).ker` using `Subgroup.Normal.conj_mem (MonoidHom.normal_ker _) k hk _`. Conclude with `⟨_, hk', rfl⟩`.
-/
theorem NU_conj : ∀ a ∈ A0 F0 Λ, ∀ n ∈ NU F0 Λ, a * n * a⁻¹ ∈ NU F0 Λ := by
  rintro a ha _ ⟨k, hk, rfl⟩
  have hk' : (⟨a, ha⟩ : A0 F0 Λ) * k * (⟨a, ha⟩ : A0 F0 Λ)⁻¹ ∈ (indU F0 Λ).ker :=
    Subgroup.Normal.conj_mem (MonoidHom.normal_ker _) k hk _
  exact ⟨_, hk', rfl⟩

def toFun' (u : (Module.End D.host.E (WbQ D F0))ˣ) : WbQ D F0 → WbQ D F0 := ⇑(u : Module.End D.host.E (WbQ D F0))

/- English proof (translation)
Introduce `u v h`. Use `ext1`. Conclude with `LinearMap.ext (congrFun h)`.
-/
theorem toFun'_inj : Function.Injective (toFun' F0) := by
  intro u v h
  ext1
  exact LinearMap.ext (congrFun h)

variable {F0 Λ}

/- English proof (translation)
Use extensionality with `ψ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Take `⟨γ, hγ, hγΛ, hγa⟩` from `lift_fix hΛ a.2`. Use `⟨γ, hγ, hγΛ, fun x hx => ?_⟩` and prove the remaining obligations.

Use `show ind F0 Λ a (Submodule.Quotient.mk x) = _`. Rewrite using `[ind_apply_mk, mk_eq_iff, ← neg_sub]`. Conclude with `neg_mem (hγa x.1 x.2)`. Introduce and unpack `⟨γ, hγ, hγΛ, hψ⟩`. Take `⟨a, ha, hag⟩` from `stab_fix hΛ hγ hγΛ`.

Use `⟨⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H x`. Establish `hx : γ x.1 ∈ perpS (VS D) F0.X` using `stab_mapsP hγ x.1 x.2`.

Use `show ind F0 Λ ⟨a, ha⟩ (Submodule.Quotient.mk x) = ψ (Submodule.Quotient.mk x)`. Rewrite using `[hψ x hx, ind_apply_mk, mk_eq_iff]`. Conclude with `hag x.1 x.2`.
-/
theorem range_eq (hΛ : IsRowLat D F0 Λ) : Set.range (toFun' F0 ∘ indU F0 Λ) = autLz D F0 Λ := by
  ext ψ
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨γ, hγ, hγΛ, hγa⟩ := lift_fix hΛ a.2
    refine ⟨γ, hγ, hγΛ, fun x hx => ?_⟩
    show ind F0 Λ a (Submodule.Quotient.mk x) = _
    rw [ind_apply_mk, mk_eq_iff, ← neg_sub]
    exact neg_mem (hγa x.1 x.2)
  · rintro ⟨γ, hγ, hγΛ, hψ⟩
    obtain ⟨a, ha, hag⟩ := stab_fix hΛ hγ hγΛ
    refine ⟨⟨a, ha⟩, ?_⟩
    funext w
    induction w using Submodule.Quotient.induction_on with
    | H x =>
      have hx : γ x.1 ∈ perpS (VS D) F0.X := stab_mapsP hγ x.1 x.2
      show ind F0 Λ ⟨a, ha⟩ (Submodule.Quotient.mk x) = ψ (Submodule.Quotient.mk x)
      rw [hψ x hx, ind_apply_mk, mk_eq_iff]
      exact hag x.1 x.2

/- English proof (translation)
Establish `h1 : Nat.card (indU F0 Λ).range = Nat.card (Set.range (indU F0 Λ))`. Rewrite using `[← MonoidHom.coe_range]`. Both sides reduce to the same expression. Establish `h2 : Nat.card (Set.range (toFun' F0 ∘ indU F0 Λ)) = Nat.card (Set.range (indU F0 Λ))`. Rewrite using `[Set.range_comp]`.

Conclude with `Nat.card_image_of_injective (toFun'_inj F0) _`. Use `⟨A0 F0 Λ, NU F0 Λ, rfl, NU_coe F0 Λ, Subgroup.map_subtype_le _, NU_conj F0 Λ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.relIndex, NU_subgroupOf, Subgroup.index_ker, h1, ← h2, range_eq hΛ]`. Use `haveI : Finite (autLz D F0 Λ) := hfin.to_subtype haveI : Nonempty (autLz D F0 Λ) := by`. Rewrite using `[← range_eq hΛ]`.

Conclude with `⟨⟨_, 1, rfl⟩⟩`. Conclude with `Nat.card_pos`.
-/
theorem main_gen (hΛ : IsRowLat D F0 Λ) (hfin : (autLz D F0 Λ).Finite) :
    ∃ A N : Subgroup (GV D), (A : Set (GV D)) = Aut0 (lf D F0) Λ ∧ (N : Set (GV D)) = NLam Λ (lf D F0) ∧ N ≤ A ∧
      (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) ∧ N.relIndex A = Nat.card (autLz D F0 Λ) ∧
        0 < Nat.card (autLz D F0 Λ) := by
  have h1 : Nat.card (indU F0 Λ).range = Nat.card (Set.range (indU F0 Λ)) := by
    rw [← MonoidHom.coe_range]; rfl
  have h2 : Nat.card (Set.range (toFun' F0 ∘ indU F0 Λ)) = Nat.card (Set.range (indU F0 Λ)) := by
    rw [Set.range_comp]; exact Nat.card_image_of_injective (toFun'_inj F0) _
  refine ⟨A0 F0 Λ, NU F0 Λ, rfl, NU_coe F0 Λ, Subgroup.map_subtype_le _, NU_conj F0 Λ, ?_, ?_⟩
  · rw [Subgroup.relIndex, NU_subgroupOf, Subgroup.index_ker, h1, ← h2, range_eq hΛ]
  · haveI : Finite (autLz D F0 Λ) := hfin.to_subtype
    haveI : Nonempty (autLz D F0 Λ) := by
      rw [← range_eq hΛ]; exact ⟨⟨_, 1, rfl⟩⟩
    exact Nat.card_pos

end GlobalTheory.AutQuot

/- English proof (translation)
Introduce `D X Y u _ Λ hΛ`. Establish `hR : IsRowLat D (X.Fu u) Λ` using `(Y.rowsOK u).1 Λ hΛ`. Conclude with `GlobalTheory.AutQuot.main_gen hR (_root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u).A.T_prime.pos (X.Fu u) Λ hR)`.
-/
theorem GlobalTheory.AutQuot.autQuot : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ Λ ∈ Y.what₂ u,
    ∃ A N : Subgroup (GV D), (A : Set (GV D)) = Aut0 (lf D (X.Fu u)) Λ ∧ (N : Set (GV D)) = NLam Λ (lf D (X.Fu u)) ∧
      N ≤ A ∧ (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) ∧ N.relIndex A = Nat.card (autLz D (X.Fu u) Λ) ∧
        0 < Nat.card (autLz D (X.Fu u) Λ) := by
  intro D X Y u _ Λ hΛ
  have hR : IsRowLat D (X.Fu u) Λ := (Y.rowsOK u).1 Λ hΛ
  exact GlobalTheory.AutQuot.main_gen hR
    (_root_.automorphism_lattice_finite D (D.sp.Y_sig 0) _ (D.mem u).A.T_prime.pos (X.Fu u) Λ hR)
