import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIdemOfAlgebraMap

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.SuppLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Establish `h3 : finP F E z = finP F E z'` using `evF_ext h2`. Set `b` to `Module.Basis.ofVectorSpace F E`. Use `(Algebra.TensorProduct.basis (AF F) b).repr.injective (Finsupp.ext fun k => Prod.ext ?_ ?_)` and prove the remaining obligations. Establish `a1` using `GlobalTheory.LatticeLocalGlobal.repr_map (fstA F) b z k`. Establish `a2` using `GlobalTheory.LatticeLocalGlobal.repr_map (fstA F) b z' k`.

Conclude with `a1.symm.trans ((congrArg (fun x => (Algebra.TensorProduct.basis (Ainf F) b).repr x k) h1).trans a2)`. Establish `a1` using `GlobalTheory.LatticeLocalGlobal.repr_map (sndA F) b z k`. Establish `a2` using `GlobalTheory.LatticeLocalGlobal.repr_map (sndA F) b z' k`. Conclude with `a1.symm.trans ((congrArg (fun x => (Algebra.TensorProduct.basis (Af F) b).repr x k) h3).trans a2)`.
-/
theorem adele_ext {z z' : AF F ⊗[F] E} (h1 : infP F E z = infP F E z')
    (h2 : ∀ w, evF E w (finP F E z) = evF E w (finP F E z')) : z = z' := by
  have h3 : finP F E z = finP F E z' := evF_ext h2
  let b := Module.Basis.ofVectorSpace F E
  refine (Algebra.TensorProduct.basis (AF F) b).repr.injective (Finsupp.ext fun k => Prod.ext ?_ ?_)
  · have a1 := GlobalTheory.LatticeLocalGlobal.repr_map (fstA F) b z k
    have a2 := GlobalTheory.LatticeLocalGlobal.repr_map (fstA F) b z' k
    exact a1.symm.trans ((congrArg (fun x => (Algebra.TensorProduct.basis (Ainf F) b).repr x k) h1).trans a2)
  · have a1 := GlobalTheory.LatticeLocalGlobal.repr_map (sndA F) b z k
    have a2 := GlobalTheory.LatticeLocalGlobal.repr_map (sndA F) b z' k
    exact a1.symm.trans ((congrArg (fun x => (Algebra.TensorProduct.basis (Af F) b).repr x k) h3).trans a2)

/- English proof (translation)
Take `⟨e1, e2, e3⟩` from `he`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `⟨?_, fun w hw => ?_⟩` and prove the remaining obligations. Rewrite using `[← h, map_mul, e1, zero_mul]`.

Rewrite using `[← h, map_mul, map_mul, e3 w hw, zero_mul]`. Introduce and unpack `⟨h1, h2⟩`. Use `adele_ext ?_ fun w => ?_` and prove the remaining obligations. Rewrite using `[map_mul, h1, mul_zero]`. Rewrite using `[map_mul, map_mul]`.

Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Rewrite using `[e2, one_mul]`. Rewrite using `[h2 w hw, mul_zero]`.
-/
theorem idem_mul_iff {v : HeightOneSpectrum (𝓞 F)} {e : AF F ⊗[F] E} (he : IsIdemOf E v e) (x : AF F ⊗[F] E) :
    e * x = x ↔ infP F E x = 0 ∧ ∀ w, w ≠ v → evF E w (finP F E x) = 0 := by
  obtain ⟨e1, e2, e3⟩ := he
  constructor
  · intro h
    refine ⟨?_, fun w hw => ?_⟩
    · rw [← h, map_mul, e1, zero_mul]
    · rw [← h, map_mul, map_mul, e3 w hw, zero_mul]
  · rintro ⟨h1, h2⟩
    refine adele_ext ?_ fun w => ?_
    · rw [map_mul, h1, mul_zero]
    · rw [map_mul, map_mul]
      by_cases hw : w = v
      · subst hw
        rw [e2, one_mul]
      · rw [h2 w hw, mul_zero]

/- English proof (translation)
Rewrite using `[Units.ext_iff, ← Matrix.ext_iff]`. Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Use `show φ (g.1 i j) = (1 : Matrix (Fin n) (Fin n) B) i j ↔ _`. Rewrite using `[Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem bc_eq_one_iff {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (φ : A →+* B) (g : GL (Fin n) A) :
    Formalism.UG.bc φ g = 1 ↔ ∀ i j, φ ((g.1 - 1) i j) = 0 := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  show φ (g.1 i j) = (1 : Matrix (Fin n) (Fin n) B) i j ↔ _
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

variable [NumberField E] [StarRing E] (hc : CMData F E) (V : HSpace E)

/- English proof (translation)
Establish `h1 : IsFin hc V g ↔ ∀ i j, infP F E (((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j) = 0` using `bc_eq_one_iff _ _`. Establish `h2 : ∀ w, locMat hc V w g = 1 ↔ ∀ i j, evF E w (finP F E (((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j)) = 0` using `fun w => bc_eq_one_iff ((evF E w).comp (finP F E)) (HA.mat (AF F) hc.sig V.gram g)`. Rewrite using `[h1]`. Simplify using `only [h2, Supp, idem_mul_iff he]`. Conclude with `⟨fun h => ⟨fun i j => (h i j).1, fun w hw i j => (h i j).2 w hw⟩, fun h i j => ⟨h.1 i j, fun w hw => h.2 w hw i j⟩⟩`.
-/
theorem supp_iff {v : HeightOneSpectrum (𝓞 F)} {e : AF F ⊗[F] E} (he : IsIdemOf E v e)
    (g : HA (AF F) hc.sig V.gram) :
    Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1 := by
  have h1 : IsFin hc V g ↔ ∀ i j, infP F E (((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j) = 0 :=
    bc_eq_one_iff _ _
  have h2 : ∀ w, locMat hc V w g = 1 ↔
      ∀ i j, evF E w (finP F E (((HA.mat (AF F) hc.sig V.gram g).1 - 1) i j)) = 0 :=
    fun w => bc_eq_one_iff ((evF E w).comp (finP F E)) (HA.mat (AF F) hc.sig V.gram g)
  rw [h1]
  simp only [h2, Supp, idem_mul_iff he]
  exact ⟨fun h => ⟨fun i j => (h i j).1, fun w hw i j => (h i j).2 w hw⟩,
    fun h i j => ⟨h.1 i j, fun w hw => h.2 w hw i j⟩⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ _ hc V v e he`. Use `⟨supp_iff hc V he, fun g g' hg hg' h => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨a1, a2⟩` from `(supp_iff hc V he g).1 hg`. Take `⟨b1, b2⟩` from `(supp_iff hc V he g').1 hg'`. Establish `hw : ∀ w, locMat hc V w g = locMat hc V w g'` using `fun w => by`.

Distinguish the cases in `hw : w = v`. Conclude with `hw ▸ h`. Rewrite using `[a2 w hw, b2 w hw]`. Establish `hi` using `Eq.trans a1 (Eq.symm b1)`. Use `Subtype.ext (Units.ext (Matrix.ext fun i j => adele_ext ?_ fun w => ?_))` and prove the remaining obligations.

Conclude with `congrArg (fun x => x.1 i j) hi`. Conclude with `congrArg (fun x => x.1 i j) (hw w)`. Set `u' : HA (Fv F v) hc.sig V.gram` to `⟨u, hu⟩`. Take `⟨k, hk⟩` from `GlobalTheory.LocalUnitaryGlue.exists_of_finite hc.sig V.gram (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) v u') ((Set.finite_singleton v).subset fun w hw => by`. Assume the negation of the conclusion as `hne`.

Conclude with `hw (Pi.mulSingle_eq_of_ne (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) (i := v) (i' := w) hne u'))`. Establish `hl : ∀ w, locMat hc V w (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ofFin hc V k) = HA.mat _ _ _ (Pi.mulSingle (M` using `fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) v u' w) := fun w => by`. Rewrite using `[← hk w]`. Conclude with `congrArg (fun x => HA.mat _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projLoc hc V w x)) (GlobalTheory.AutFunCompare.projFin_ofFin hc V k)`. Use `⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ofFin hc V k, (supp_iff hc V he _).2 ⟨?_, fun w hw => ?_⟩, ?_⟩` and prove the remaining obligations.

Conclude with `congrArg (HA.mat _ _ _) (GlobalTheory.AutFunCompare.projInf_ofFin hc V k)`. Rewrite using `[hl, Pi.mulSingle_eq_of_ne hw]`. Both sides reduce to the same expression. Rewrite using `[hl, Pi.mulSingle_eq_same]`. Both sides reduce to the same expression.
-/
theorem supp_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (e : AF F ⊗[F] E), IsIdemOf E v e → (∀ g, Supp hc V e g ↔ IsFin hc V g ∧ ∀ w, w ≠ v → locMat hc V w g = 1) ∧ (∀ g g', Supp hc V e g → Supp hc V e g' → locMat hc V v g = locMat hc V v g' → g = g') ∧ ∀ u ∈ HR (Fv F v) hc.sig V.gram, ∃ g, Supp hc V e g ∧ locMat hc V v g = u := by
  classical
  intro F E _ _ _ _ _ _ hc V v e he
  refine ⟨supp_iff hc V he, fun g g' hg hg' h => ?_, fun u hu => ?_⟩
  · obtain ⟨a1, a2⟩ := (supp_iff hc V he g).1 hg
    obtain ⟨b1, b2⟩ := (supp_iff hc V he g').1 hg'
    have hw : ∀ w, locMat hc V w g = locMat hc V w g' := fun w => by
      by_cases hw : w = v
      · exact hw ▸ h
      · rw [a2 w hw, b2 w hw]
    have hi := Eq.trans a1 (Eq.symm b1)
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => adele_ext ?_ fun w => ?_))
    · exact congrArg (fun x => x.1 i j) hi
    · exact congrArg (fun x => x.1 i j) (hw w)
  · let u' : HA (Fv F v) hc.sig V.gram := ⟨u, hu⟩
    obtain ⟨k, hk⟩ := GlobalTheory.LocalUnitaryGlue.exists_of_finite hc.sig V.gram
      (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) v u')
      ((Set.finite_singleton v).subset fun w hw => by
        by_contra hne
        exact hw (Pi.mulSingle_eq_of_ne
          (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) (i := v) (i' := w) hne u'))
    have hl : ∀ w, locMat hc V w (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ofFin hc V k) = HA.mat _ _ _
        (Pi.mulSingle (M := fun w : HeightOneSpectrum (𝓞 F) => HA (Fv F w) hc.sig V.gram) v u' w) := fun w => by
      rw [← hk w]
      exact congrArg (fun x => HA.mat _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.projLoc hc V w x))
        (GlobalTheory.AutFunCompare.projFin_ofFin hc V k)
    refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ofFin hc V k, (supp_iff hc V he _).2 ⟨?_, fun w hw => ?_⟩, ?_⟩
    · exact congrArg (HA.mat _ _ _) (GlobalTheory.AutFunCompare.projInf_ofFin hc V k)
    · rw [hl, Pi.mulSingle_eq_of_ne hw]; rfl
    · rw [hl, Pi.mulSingle_eq_same]; rfl

end GlobalTheory.SuppLocal
