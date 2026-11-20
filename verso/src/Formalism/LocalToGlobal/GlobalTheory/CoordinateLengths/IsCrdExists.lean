import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.LenLen2OfCoord
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

variable {D : D7} {u : D.what₂.Word}

def IsCrd (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0)
    (Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) : Prop :=
  ∀ z, (D.fm u).emb 0 x c z = fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0))
    (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1) Q (T.val0.eY z)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem atInf_unit (B : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    IsUnit (atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det := by
  exact (Matrix.isUnit_iff_isUnit_det _).1 ((Units.isUnit B).map (RingHom.mapMatrix (embT D τ)))

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.
-/
theorem isCrd_unique (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) {Q Q' : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T B x c Q) (h' : IsCrd T B x c Q') : Q = Q' := by
  apply polynomial_function_frames_injective _ _ _ (atInf_unit (B⁻¹))
  funext y
  obtain ⟨z, rfl⟩ := T.val0.eY.surjective y
  rw [← h z, h' z]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem isCrd_exists (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) : ∃ Q, IsCrd T B x c Q := by
  obtain ⟨P, -, hP⟩ := ((T.val0.5 ((D.fm u).emb 0 x)).1 ⟨x, rfl⟩).2 c
  refine ⟨MvPolynomial.C (∏ τ, (atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ).det ^
      shiftOf (lamT u 0) τ) * subP (atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)) P, fun z => ?_⟩
  have hN : (fun τ => atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E) τ *
      atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ) = 1 := by
    funext τ
    simp only [atInf, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _), Pi.one_apply]
  rw [hP z, ← fnOf_mul _ _ (atInf (embT D) (B : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.host.E)), hN]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem isCrd_add (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) {x y : ((D.fm u).lat 0).V}
    {c : (D.mem u).C.cls 0} {Q Q' : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T B x c Q) (h' : IsCrd T B y c Q') : IsCrd T B (x + y) c (Q + Q') := by
  intro z
  rw [map_add, Pi.add_apply, Pi.add_apply, h z, h' z, map_add, Pi.add_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem isCrd_smul (T : Forms0 D u) (B : GL (Fin (D.R.N 0)) D.host.E) {x : ((D.fm u).lat 0).V}
    {c : (D.mem u).C.cls 0} {Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T B x c Q) (r : D.what₂.LL) : IsCrd T B (r • x) c (D.what₂.embLL r • Q) := by
  intro z
  rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, h z, map_smul, Pi.smul_apply]

def crd (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V) :
    (D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ :=
  fun c => Classical.choose (isCrd_exists T (B c) x c)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem crd_spec (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (x : ((D.fm u).lat 0).V)
    (c : (D.mem u).C.cls 0) : IsCrd T (B c) x c (crd T B x c) :=
  Classical.choose_spec (isCrd_exists T (B c) x c)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem crd_eq (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) {x : ((D.fm u).lat 0).V}
    {c : (D.mem u).C.cls 0} {Q : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ}
    (h : IsCrd T (B c) x c Q) : crd T B x c = Q :=
  isCrd_unique T (B c) x c (crd_spec T B x c) h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem owEquiv_coe (w : D.what₂.places.Pl) (r : Ow D w) :
    ((((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w) r : bwA_Ow D w) : ℂ) =
      D.what₂.embLL (r : D.what₂.LL) := by
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem crd_add (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (x y : ((D.fm u).lat 0).V) :
    crd T B (x + y) = crd T B x + crd T B y :=
  funext fun c => crd_eq T B (isCrd_add T (B c) (crd_spec T B x c) (crd_spec T B y c))

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem crd_smul (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (r : D.what₂.LL)
    (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) : crd T B (r • x) c = D.what₂.embLL r • crd T B x c :=
  crd_eq T B (isCrd_smul T (B c) (crd_spec T B x c) r)

def crdL (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (w : D.what₂.places.Pl) :
    Vl D u 0 →ₛₗ[((owEquiv D w : Ow D w ≃+* bwA_Ow D w) : Ow D w →+* bwA_Ow D w)]
      ((D.mem u).C.cls 0 → MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ) where
  toFun := crd T B
  map_add' x y := crd_add T B x y
  map_smul' r x := by
    funext c
    have h := crd_smul T B (r : D.what₂.LL) x c
    rw [Pi.smul_apply, Subring.smul_def r x, h, Subring.smul_def, owEquiv_coe]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem crdL_apply (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (w : D.what₂.places.Pl)
    (x : Vl D u 0) : crdL T B w x = crd T B x := rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem crdL_inj (T : Forms0 D u) (B : (D.mem u).C.cls 0 → GL (Fin (D.R.N 0)) D.host.E) (w : D.what₂.places.Pl) :
    Function.Injective (crdL T B w) := by
  intro x y hxy
  apply (D.fm u).emb_inj 0
  funext c z
  have hc : crd T B x c = crd T B y c := congrFun hxy c
  rw [crd_spec T B x c z, crd_spec T B y c z, hc]

end Formalism.L2.GlobalTheoryTheory.LemB
