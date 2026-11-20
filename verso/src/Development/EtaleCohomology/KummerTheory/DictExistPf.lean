import Development.EtaleCohomology.KummerTheory.DictPf
import Development.EtaleCohomology.KummerTheory.CupAWCutEv

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.DE
variable {R : Type} [CommRing R] {I : Cx R} {X : Scheme.{0}} {n : ℤ}

def eta (a : Sec (I.X n) X) : (freeP R).obj (yoneda.obj X) ⟶ (I.X n).obj where
  app U := ModuleCat.freeDesc (↾fun y : ULift.{1} (U.unop ⟶ X) => ((I.X n).obj.map y.down.op).hom a)
  naturality := by
    intro U V g
    apply ModuleCat.free_hom_ext
    intro y
    erw [ModuleCat.comp_apply, ModuleCat.comp_apply, ModuleCat.free_map_apply]
    erw [ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    erw [← ModuleCat.comp_apply, ← Functor.map_comp]
    rfl

/- English proof (translation)
Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem eta_app (a : Sec (I.X n) X) (U : Scheme.{0}) (x : U ⟶ X) :
    ((eta a).app (op U)).hom (ModuleCat.freeMk (ULift.up x)) = Sec.res x a := by
  erw [eta, ModuleCat.freeDesc_apply]
  rfl

def phi (a : Sec (I.X n) X) : (free R).obj (yoneda.obj X) ⟶ I.X n :=
  ⟨sheafifyLift Scheme.etaleTopology (eta a) (I.X n).property⟩

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem phi_gen (a : Sec (I.X n) X) (U : Scheme.{0}) (x : U ⟶ X) :
    Sec.map (phi a) (freeGen R (yoneda.obj X) U x) = Sec.res x a := by
  have key := congrArg (fun t => (t.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (eta a) (I.X n).property)
  simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply] at key
  exact key.trans (eta_app a U x)

def coch (a : Sec (I.X n) X) : Cochain ((chains R).obj (sch.obj X)) I n :=
  Cochain.single (p := -((0 : ℕ) : ℤ)) (q := n) ((chainsXIso R (sch.obj X) 0).hom ≫ phi a) n

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem coch_zero (a : Sec (I.X n) X) (h : -((0 : ℕ) : ℤ) + n = n) (U : Scheme.{0}) (x : U ⟶ X) :
    ev (coch a) 0 n h U x = Sec.res x a := by
  change Sec.map ((chainsXIso R _ 0).inv ≫ (coch a).v _ _ h) (freeGen R ((sch.obj X).obj (op (SimplexCategory.mk 0))) U x) = _
  rw [coch, Cochain.single_v]
  erw [Iso.inv_hom_id_assoc]
  exact phi_gen a U x

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem coch_succ (a : Sec (I.X n) X) (p : ℕ) (s : ℤ) (h : -((p + 1 : ℕ) : ℤ) + n = s) (U : Scheme.{0})
    (x : Sx (sch.obj X) (p + 1) U) : ev (coch a) (p + 1) s h U x = 0 := by
  rw [AW.ev_eq, coch, Cochain.single_v_eq_zero _ _ _ _ _ (by omega), comp_zero]
  rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem ev_zero_cochain {E : Spc} (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  simp [ev]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Substitute using the available equality. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem coch_delta (a : Sec (I.X n) X) (ha : Sec.map (I.d n (n + 1)) a = 0) : δ n (n + 1) (coch a) = 0 := by
  apply AW.ev_ext
  intro p s h U x
  rw [ev_zero_cochain]
  rcases p with _ | p
  · obtain rfl : s = n + 1 := by omega
    rw [AW.ev_delta_zero rfl (coch a) n (n + 1) (by simp) h U x, coch_zero a (by simp) U x]
    have e := AW.sec_map_res (I.d n (n + 1)) (show U ⟶ X from x) a
    rw [ha] at e
    exact e.symm.trans (LinearMap.map_zero _)
  · rw [AW.ev_delta_succ rfl (coch a) p (-((p + 1 : ℕ) : ℤ) + n) s rfl h U x, coch_succ]
    rw [show Sec.map (I.d (-((p + 1 : ℕ) : ℤ) + n) s) (0 : Sec (I.X (-((p + 1 : ℕ) : ℤ) + n)) U) = 0 from LinearMap.map_zero _, zero_add]
    rcases p with _ | p
    · have hs : n = s := by omega
      subst hs
      rw [Fin.sum_univ_two]
      have e : ∀ i : Fin 2, ev (coch a) 0 n (by omega) U (x.face i) =
          Sec.res (show U ⟶ X from x) a := fun i => coch_zero a _ U _
      rw [e 0, e 1]
      simp
    · simp only [coch_succ, smul_zero, Finset.sum_const_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem dictExist : DictExist := by
  intro R _ I X n a ha
  refine ⟨⟨coch a, (Cocycle.mem_iff n (n + 1) rfl _).2 (coch_delta a ha)⟩, ?_, ?_⟩
  · exact (coch_zero a (by simp) X (𝟙 X)).trans (by rw [Sec.res, op_id, CategoryTheory.Functor.map_id]; rfl)
  · intro p s h U y
    exact coch_succ a p s h U y

end LateralTheory.KummerTheory.DE

namespace LateralTheory.KummerTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DictExist_of : DictExist := DE.dictExist
end LateralTheory.KummerTheory
