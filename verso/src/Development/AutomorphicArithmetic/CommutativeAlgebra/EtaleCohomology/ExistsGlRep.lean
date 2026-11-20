import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrysCopy
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.AdmCrys

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc CrystallineSemistableComparison Module

namespace UpperTheory.Ru.crystallineComparison

/- English proof (translation)
Set `f : G →* Matrix (Fin a) (Fin a) k` to `{ toFun := fun g => LinearMap.toMatrix b b (π g) map_one' := by rw [map_one]; exact LinearMap.toMatrix_one b map_mul' := fun g h => by rw [map_mul]; exact LinearMap.toMatrix_mul b _ _ }`. Conclude with `⟨f.toHomUnits, fun g => MonoidHom.coe_toHomUnits f g⟩`.
-/
private theorem exists_glRep {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] {a : ℕ}
    (b : Basis (Fin a) k V) (π : Representation k G V) :
    ∃ r : G →* GL (Fin a) k, ∀ g, (r g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix b b (π g) := by
  let f : G →* Matrix (Fin a) (Fin a) k :=
    { toFun := fun g => LinearMap.toMatrix b b (π g)
      map_one' := by rw [map_one]; exact LinearMap.toMatrix_one b
      map_mul' := fun g h => by rw [map_mul]; exact LinearMap.toMatrix_mul b _ _ }
  exact ⟨f.toHomUnits, fun g => MonoidHom.coe_toHomUnits f g⟩

private noncomputable def actRep {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (M : Model l K) (n : ℕ) :
    Representation ℚ_[l] K.fixingSubgroup (M.V n) :=
  (GlobalTheory.EtC.galHQ l (PadicAlgCl l) M.q n 0).comp (IntermediateField.fixingSubgroupEquiv K).toMonoidHom

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
/- English proof (translation)
Introduce `hC l _ P AI hT K M hM j a b`. Use `haveI := K.2`. Take `⟨FreeQuotientRank⟩` from `UpperTheory.Lit.Cmp.locTied6 l P AI hT`. Take `⟨T⟩` from `hT`. Establish `hadm` using `UpperTheory.Gal.Seam.isAdmP_of_isAdm FreeQuotientRank (hC l K.1 M hM.1 hM.2 j a b)`.

Take `⟨r, hr⟩ : ∃ r : ↥(GK K) →* GL (Fin a) ℚ_[l], ∀ g : ↥(GK K), (r g : Matrix (Fin a) (Fin a) ℚ_[l]) = LinearMap.toMatrix b b (M.act j g)` from `exists_glRep b (actRep M j)`. Establish `hadm' : UpperTheory.Gal.Seam.IsAdmP P (GK K) (fun σ => (r σ : Matrix (Fin a) (Fin a) ℚ_[l]))`. Establish `h0 : (fun σ : ↥(GK K) => (r σ : Matrix (Fin a) (Fin a) ℚ_[l])) = (M.mat j b : ↥(GK K) → _)` using `funext hr`. Rewrite using `[h0]`. Conclude with `hadm`.

Set `r' : ↥(GK K) →* GL (Fin a) ↥K.1` to `(Units.map (RingHom.mapMatrix (algebraMap ℚ_[l] ↥K.1)).toMonoidHom).comp r`. Establish `hr' : ∀ σ i j, (r' σ).val i j = algebraMap ℚ_[l] ↥K.1 ((r σ).val i j)` using `fun σ i j => rfl`. Establish `hc` using `UpperTheory.Gal.Seam.isCrys_of_isAdmP l P AI T K K a r r' hr' hadm'`. Establish `hcρ : WeaklyAdmissibleFiltrations.IsCrys (P.PD K) (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp ((Units.coeHom _).comp r) : Representation ℚ_[l] ↥(GK K) (Fin a → ℚ_[l]))` using `(GlobalTheory.Pst.isCrys_ext_iff (P.PD K) (fun g => ⟨(r g : Matrix (Fin a) (Fin a) ℚ_[l]), fun x => rfl, fun x => rfl⟩)).1 hc`. Use `⟨_, fun g v => ?_, hcρ⟩` and prove the remaining obligations.

Use `show (r g : Matrix (Fin a) (Fin a) ℚ_[l]).mulVec (b.equivFun v) = b.equivFun (M.act j g v)`. Rewrite using `[hr g]`. Simplify using `using LinearMap.toMatrix_mulVec_repr b b (M.act j g) v`.
-/
theorem UpperTheory.Ru.crystallineComparison.crysCopy :
    UpperTheory.Ru.crystallineComparison.CrysCopy := by
  intro hC l _ P AI hT K M hM j a b
  haveI := K.2
  obtain ⟨FreeQuotientRank⟩ := UpperTheory.Lit.Cmp.locTied6 l P AI hT
  obtain ⟨T⟩ := hT
  have hadm := UpperTheory.Gal.Seam.isAdmP_of_isAdm FreeQuotientRank (hC l K.1 M hM.1 hM.2 j a b)
  obtain ⟨r, hr⟩ : ∃ r : ↥(GK K) →* GL (Fin a) ℚ_[l], ∀ g : ↥(GK K),
      (r g : Matrix (Fin a) (Fin a) ℚ_[l]) = LinearMap.toMatrix b b (M.act j g) := exists_glRep b (actRep M j)
  have hadm' : UpperTheory.Gal.Seam.IsAdmP P (GK K) (fun σ => (r σ : Matrix (Fin a) (Fin a) ℚ_[l])) := by
    have h0 : (fun σ : ↥(GK K) => (r σ : Matrix (Fin a) (Fin a) ℚ_[l])) = (M.mat j b : ↥(GK K) → _) := funext hr
    rw [h0]
    exact hadm
  let r' : ↥(GK K) →* GL (Fin a) ↥K.1 :=
    (Units.map (RingHom.mapMatrix (algebraMap ℚ_[l] ↥K.1)).toMonoidHom).comp r
  have hr' : ∀ σ i j, (r' σ).val i j = algebraMap ℚ_[l] ↥K.1 ((r σ).val i j) := fun σ i j => rfl
  have hc := UpperTheory.Gal.Seam.isCrys_of_isAdmP l P AI T K K a r r' hr' hadm'
  have hcρ : WeaklyAdmissibleFiltrations.IsCrys (P.PD K) (((Matrix.toLinAlgEquiv' : Matrix (Fin a) (Fin a) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp
      ((Units.coeHom _).comp r) : Representation ℚ_[l] ↥(GK K) (Fin a → ℚ_[l])) :=
    (GlobalTheory.Pst.isCrys_ext_iff (P.PD K) (fun g => ⟨(r g : Matrix (Fin a) (Fin a) ℚ_[l]), fun x => rfl, fun x => rfl⟩)).1 hc
  refine ⟨_, fun g v => ?_, hcρ⟩
  show (r g : Matrix (Fin a) (Fin a) ℚ_[l]).mulVec (b.equivFun v) = b.equivFun (M.act j g v)
  rw [hr g]
  simpa using LinearMap.toMatrix_mulVec_repr b b (M.act j g) v
