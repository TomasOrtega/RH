import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full
  Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Substitute `h` using the available equality. Establish `h2 : Quot.mk _ x = Quot.mk _ y` using `eq_of_heq he`. Establish `h3` using `Quot.eqvGen_exact h2`. Use `clear he h2`. Proceed by induction on `h3 with`.

Consider the case `rel a b hab => exact hab`. Consider the case `refl a => apply Formalism.L2.SG.TermDef.dcrel_refl`. Consider the case `symm a b _ ih => exact Formalism.L2.SG.Pf.dcrel_symm (h := ih)`. Consider the case `trans a b c _ _ ih1 ih2 => exact Formalism.L2.SG.Pf.dcrel_trans (h := ih1) (h' := ih2)`.
-/
theorem dcrel_of_heq {Λ₁ Λ₂ : Submodule (𝓞 E) S.V} (h : Λ₁ = Λ₂) {T T' : E} (F : LFlag S r T)
    (P : Submodule (𝓞 E) S.V → LFlag S r T' → Prop) (x : TermDef.Carrier (P Λ₁)) (y : TermDef.Carrier (P Λ₂))
    (he : HEq (TermDef.mk Λ₁ F (P Λ₁) x) (TermDef.mk Λ₂ F (P Λ₂) y)) : TermDef.DCRel Λ₂ F x.1 y.1 := by
  subst h
  have h2 : Quot.mk _ x = Quot.mk _ y := eq_of_heq he
  have h3 := Quot.eqvGen_exact h2
  clear he h2
  induction h3 with
  | rel a b hab => exact hab
  | refl a => apply Formalism.L2.SG.TermDef.dcrel_refl
  | symm a b _ ih => exact Formalism.L2.SG.Pf.dcrel_symm (h := ih)
  | trans a b c _ _ ih1 ih2 => exact Formalism.L2.SG.Pf.dcrel_trans (h := ih1) (h' := ih2)

/- English proof (translation)
The claim follows from `hn.1.1`.
-/
theorem nlam_isom {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    n ∈ Formalism.HermitianLatticesTheory.isom S.hT := hn.1.1

/- English proof (translation)
The claim follows from `hn.1.2`.
-/
theorem nlam_gmap {Λ : Submodule (𝓞 E) S.V} {T : E} {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    Formalism.HermitianLatticesTheory.gmap n Λ = Λ := hn.1.2

/- English proof (translation)
Establish `hinv : ∀ y : S.V, g⁻¹ (g y) = y` using `fun y => g.symm_apply_apply y`. Use extensionality with `x`. Simplify using `only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Establish `hy' : y ∈ Formalism.HermitianLatticesTheory.gmap g Λ` using `by rw [h]; exact hy`. Simplify using `only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hy'`. Take `⟨z, hz, rfl⟩` from `hy'`. Rewrite using `[hinv]`. Conclude with `hz`.

Introduce `hx`. Use `⟨g x, ?_, hinv x⟩` and prove the remaining obligations. Rewrite using `[← h]`. Conclude with `Submodule.mem_map_of_mem hx`.
-/
theorem gmap_inv_of {Λ : Submodule (𝓞 E) S.V} {g : S.V ≃ₗ[E] S.V} (h : Formalism.HermitianLatticesTheory.gmap g Λ = Λ) :
    Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ = Λ := by
  have hinv : ∀ y : S.V, g⁻¹ (g y) = y := fun y => g.symm_apply_apply y
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.HermitianLatticesTheory.gmap g Λ := by rw [h]; exact hy
    simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe] at hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    rw [hinv]
    exact hz
  · intro hx
    refine ⟨g x, ?_, hinv x⟩
    rw [← h]
    exact Submodule.mem_map_of_mem hx

end Gen

section Fib

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem frame_lf {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) (a : Fin (D.R.rS + 1)) :
    frame (lf D F0) a = F0.fvec a := rfl

/- English proof (translation)
The claim follows from `s.rep.2.2.1`.
-/
theorem lin_isom (s : TT Y u u') : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1

/- English proof (translation)
The claim follows from `s.rep.2.2.2.1`.
-/
theorem lin_gmap (s : TT Y u u') : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1

/- English proof (translation)
Unfold `Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF`. Rewrite using `[dif_pos (lin_isom s)]`. Both sides reduce to the same expression.
-/
theorem frame_eq (s : TT Y u u') : s.frame = Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u')) := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dif_pos (lin_isom s)]
  rfl

/- English proof (translation)
Rewrite using `[frame_eq]`. Use `show (Formalism.L2.SG.Saturated.mapFlag s.lin (lin_isom s) (lf D (X.Fu u')).fl).fvec a = s.lin ((lf D (X.Fu u')).fl.fvec a)`. Generalize the expression as in `(lf D (X.Fu u')).fl = F`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Simplify using `only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, Formalism.L2.SG.Saturated.mapFlag]`.

Simplify using `only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Formalism.L2.SG.Saturated.mapFlag]`.
-/
theorem frame_apply (s : TT Y u u') (a : Fin (D.R.rS + 1)) : frame s.frame a = s.lin ((X.Fu u').fvec a) := by
  rw [frame_eq]
  show (Formalism.L2.SG.Saturated.mapFlag s.lin (lin_isom s) (lf D (X.Fu u')).fl).fvec a =
    s.lin ((lf D (X.Fu u')).fl.fvec a)
  generalize (lf D (X.Fu u')).fl = F
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, Formalism.L2.SG.Saturated.mapFlag]
  · simp only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, Formalism.L2.SG.Saturated.mapFlag]

/- English proof (translation)
Establish `he : ∀ i, c (F0.e i) = F0.e i` using `fun i => by`. Establish `h1` using `hfix i.castSucc`. Simplify `h1` using `only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]`. Use `⟨hc, fun j => ?_, ?_⟩` and prove the remaining obligations. Unfold `Formalism.MainNotions.S.FlagG.Xa`.

Rewrite using `[Submodule.map_span, Set.image_image]`. Simplify using `only [LinearEquiv.coe_coe, he]`. Establish `h1` using `hfix (Fin.last _)`. Simplify `h1` using `only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]`.
-/
theorem stabF_of_fix {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T) {c : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hc : c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (hfix : ∀ a, c (F0.fvec a) = F0.fvec a) : c ∈ stabF D F0 := by
  have he : ∀ i, c (F0.e i) = F0.e i := fun i => by
    have h1 := hfix i.castSucc
    simpa only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc] using h1
  refine ⟨hc, fun j => ?_, ?_⟩
  · unfold Formalism.MainNotions.S.FlagG.Xa
    rw [Submodule.map_span, Set.image_image]
    simp only [LinearEquiv.coe_coe, he]
  · have h1 := hfix (Fin.last _)
    simpa only [Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last] using h1

/- English proof (translation)
Establish `hmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), (f * g) x = f (g x)` using `fun _ _ _ => rfl`. Establish `hinv : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f⁻¹ (f x) = x` using `fun f x => f.symm_apply_apply x`. Establish `hinv' : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f (f⁻¹ x) = x` using `fun f x => f.apply_symm_apply x`. Establish `gmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V), Formalism.HermitianLatticesTheory.gmap (f * g) L = Formalism.HermitianLatticesTheory.gmap f (Formalism.HermitianLatticesTheory.gmap g L)`. Introduce `f g L`.

Unfold `Formalism.HermitianLatticesTheory.gmap`. Rewrite using `[← Submodule.map_comp]`. Both sides reduce to the same expression. Establish `gone : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L`. Introduce `L`.

Unfold `Formalism.HermitianLatticesTheory.gmap`. Conclude with `Submodule.map_id L`. Establish `h'` using `h`. Unfold `Formalism.L2.SG.TermOp.GTerm.toTerm at h'`. Use `injection h' with h1 h3`.

Establish `hd : TermDef.DCRel s'.lam (lf D (X.Fu u)) s.frame s'.frame` using `dcrel_of_heq h1 (lf D (X.Fu u)) (fun Λ => TermDef.PD D Λ (lf D (X.Fu u)) u') ⟨s.frame, s.rep.2.2.2.2⟩ ⟨s'.frame, s'.rep.2.2.2.2⟩ h3`. Take `⟨n, hn, m, hm, hfr, -⟩` from `hd`. Establish `hnL : n ∈ NLam s.lam (lf D (X.Fu u))` using `by rw [h1]; exact hn`. Establish `hm' : m ∈ NLam (Formalism.HermitianLatticesTheory.gmap s.lin s.lam') (Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u')))`. Rewrite using `[lin_gmap, h1, ← frame_eq]`.

Conclude with `hm`. Establish `hν : s.lin⁻¹ * m * s.lin ∈ NLam s.lam' (lf D (X.Fu u'))` using `(Formalism.L2.SG.Pf.mem_NLam_map _ _ _ _ _).1 hm'`. Establish `hback : Formalism.HermitianLatticesTheory.gmap s.lin⁻¹ s.lam = s.lam'`. Rewrite using `[← lin_gmap s, ← gmul, inv_mul_cancel, gone]`. Generalize the expression as in `hνdef : s.lin⁻¹ * m * s.lin = ν at hν`.

Use `⟨h1, n, hnL, ν, hν, (n * s.lin * ν)⁻¹ * s'.lin, ?_, ?_, ?_, (mul_inv_cancel_left _ _).symm⟩` and prove the remaining obligations. Conclude with `Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (nlam_isom hn) (lin_isom s)) (nlam_isom hν))) (lin_isom s')`. Rewrite using `[gmul, lin_gmap s', ← h1, mul_inv_rev (n * s.lin) ν, mul_inv_rev n s.lin, gmul, gmul, gmap_inv_of (nlam_gmap hnL), hback, gmap_inv_of (nlam_gmap hν)]`. Introduce `a`. Establish `e1` using `hfr a`.

Rewrite `e1` using `[frame_apply, frame_apply]`. Rewrite using `[hmul, e1]`. Establish `e2 : n (m (s.lin ((X.Fu u').fvec a))) = (n * s.lin * ν) ((X.Fu u').fvec a)`. Rewrite using `[← hνdef]`. Simplify using `only [hmul, hinv']`.

Rewrite using `[e2, hinv]`.
-/
theorem fib_dec {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) :
    s.lam = s'.lam ∧ ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s.lam' (lf D (X.Fu u')),
      ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V, c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧
        Formalism.HermitianLatticesTheory.gmap c s'.lam' = s.lam' ∧ (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
        s'.lin = n * s.lin * ν * c := by

  have hmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), (f * g) x = f (g x) :=
    fun _ _ _ => rfl
  have hinv : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f⁻¹ (f x) = x :=
    fun f x => f.symm_apply_apply x
  have hinv' : ∀ (f : (VS D).V ≃ₗ[D.host.E] (VS D).V) (x : (VS D).V), f (f⁻¹ x) = x :=
    fun f x => f.apply_symm_apply x
  have gmul : ∀ (f g : (VS D).V ≃ₗ[D.host.E] (VS D).V) (L : Submodule (𝓞 D.host.E) (VS D).V),
      Formalism.HermitianLatticesTheory.gmap (f * g) L = Formalism.HermitianLatticesTheory.gmap f (Formalism.HermitianLatticesTheory.gmap g L) := by
    intro f g L
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have gone : ∀ L : Submodule (𝓞 D.host.E) (VS D).V, Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) L = L := by
    intro L
    unfold Formalism.HermitianLatticesTheory.gmap
    exact Submodule.map_id L

  have h' := h
  unfold Formalism.L2.SG.TermOp.GTerm.toTerm at h'
  injection h' with h1 h3
  have hd : TermDef.DCRel s'.lam (lf D (X.Fu u)) s.frame s'.frame :=
    dcrel_of_heq h1 (lf D (X.Fu u)) (fun Λ => TermDef.PD D Λ (lf D (X.Fu u)) u')
      ⟨s.frame, s.rep.2.2.2.2⟩ ⟨s'.frame, s'.rep.2.2.2.2⟩ h3
  obtain ⟨n, hn, m, hm, hfr, -⟩ := hd
  have hnL : n ∈ NLam s.lam (lf D (X.Fu u)) := by rw [h1]; exact hn

  have hm' : m ∈ NLam (Formalism.HermitianLatticesTheory.gmap s.lin s.lam')
      (Formalism.L2.SG.Saturated.mapL s.lin (lin_isom s) (lf D (X.Fu u'))) := by
    rw [lin_gmap, h1, ← frame_eq]
    exact hm
  have hν : s.lin⁻¹ * m * s.lin ∈ NLam s.lam' (lf D (X.Fu u')) :=
    (Formalism.L2.SG.Pf.mem_NLam_map _ _ _ _ _).1 hm'
  have hback : Formalism.HermitianLatticesTheory.gmap s.lin⁻¹ s.lam = s.lam' := by
    rw [← lin_gmap s, ← gmul, inv_mul_cancel, gone]
  generalize hνdef : s.lin⁻¹ * m * s.lin = ν at hν
  refine ⟨h1, n, hnL, ν, hν, (n * s.lin * ν)⁻¹ * s'.lin,
    ?_, ?_, ?_, (mul_inv_cancel_left _ _).symm⟩
  · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mul_mem _
      (Subgroup.mul_mem _ (nlam_isom hn) (lin_isom s)) (nlam_isom hν))) (lin_isom s')
  · rw [gmul, lin_gmap s', ← h1, mul_inv_rev (n * s.lin) ν, mul_inv_rev n s.lin, gmul, gmul, gmap_inv_of (nlam_gmap hnL),
      hback, gmap_inv_of (nlam_gmap hν)]
  · intro a
    have e1 := hfr a
    rw [frame_apply, frame_apply] at e1
    rw [hmul, e1]
    have e2 : n (m (s.lin ((X.Fu u').fvec a))) = (n * s.lin * ν) ((X.Fu u').fvec a) := by
      rw [← hνdef]
      simp only [hmul, hinv']
    rw [e2, hinv]

/- English proof (translation)
Take `⟨-, n, -, ν, -, c, hc, hgc, hfix, -⟩` from `fib_dec h`. Establish `hstab : c ∈ stabF D (X.Fu u')` using `stabF_of_fix (X.Fu u') hc hfix`. Establish `hone : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D (X.Fu u')` using `stabF_of_fix (X.Fu u') (Subgroup.one_mem _) (fun _ => rfl)`. Establish `hg1 : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) s.lam' = s.lam'`. Unfold `Formalism.HermitianLatticesTheory.gmap`.

Conclude with `Submodule.map_id _`. Establish `hR` using `Y.rowsOK u'`. Take `⟨Λ0, -, huniq⟩` from `hR.2 s.lam' (hR.1 _ s.mem')`. Establish `e1` using `huniq s.lam' ⟨s.mem', 1, hone, hg1⟩`. Establish `e2` using `huniq s'.lam' ⟨s'.mem', c, hstab, hgc⟩`.

Conclude with `e1.trans e2.symm`.
-/
theorem lam'_eq {s s' : TT Y u u'} (h : s.toTerm = s'.toTerm) : s.lam' = s'.lam' := by
  obtain ⟨-, n, -, ν, -, c, hc, hgc, hfix, -⟩ := fib_dec h
  have hstab : c ∈ stabF D (X.Fu u') := stabF_of_fix (X.Fu u') hc hfix
  have hone : (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) ∈ stabF D (X.Fu u') :=
    stabF_of_fix (X.Fu u') (Subgroup.one_mem _) (fun _ => rfl)
  have hg1 : Formalism.HermitianLatticesTheory.gmap (1 : (VS D).V ≃ₗ[D.host.E] (VS D).V) s.lam' = s.lam' := by
    unfold Formalism.HermitianLatticesTheory.gmap
    exact Submodule.map_id _
  have hR := Y.rowsOK u'
  obtain ⟨Λ0, -, huniq⟩ := hR.2 s.lam' (hR.1 _ s.mem')
  have e1 := huniq s.lam' ⟨s.mem', 1, hone, hg1⟩
  have e2 := huniq s'.lam' ⟨s'.mem', c, hstab, hgc⟩
  exact e1.trans e2.symm

/- English proof (translation)
Take `⟨n, hn, n', hn', hq⟩` from `h`. Break down `s with ⟨l, hm, l', hm', c⟩` into its components or cases. Break down `s' with ⟨k, km, k', km', c'⟩` into its components or cases. Simplify using `only at hl hl'`. Substitute `hl` using the available equality.

Substitute `hl'` using the available equality. Establish `hc : c = c'` using `(Quot.out_eq c).symm.trans ((Quot.sound ⟨n, hn, n', hn', hq⟩).trans (Quot.out_eq c'))`. Substitute `hc` using the available equality. Both sides reduce to the same expression.
-/
theorem gterm_eq {s s' : TT Y u u'} (hl : s.lam = s'.lam) (hl' : s.lam' = s'.lam')
    (h : ∃ n ∈ NLam s.lam (lf D (X.Fu u)), ∃ n' ∈ NLam s.lam' (lf D (X.Fu u')), s'.lin = n * s.lin * n') : s = s' := by
  obtain ⟨n, hn, n', hn', hq⟩ := h
  rcases s with ⟨l, hm, l', hm', c⟩
  rcases s' with ⟨k, km, k', km', c'⟩
  simp only at hl hl'
  subst hl
  subst hl'
  have hc : c = c' :=
    (Quot.out_eq c).symm.trans ((Quot.sound ⟨n, hn, n', hn', hq⟩).trans (Quot.out_eq c'))
  subst hc
  rfl

end Fib

end Formalism.L2.SG.Pf.FibreCounting
