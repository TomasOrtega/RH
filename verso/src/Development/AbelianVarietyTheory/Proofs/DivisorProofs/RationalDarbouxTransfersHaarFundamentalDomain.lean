import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRatPairIff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatDarbouxTransfer

/- English proof (translation)
Use `haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial`. Use `haveI : FiniteDimensional D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)`. Set `bA` to `Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)`. Conclude with `⟨Module.Free.of_basis bA, Module.Finite.of_basis bA, by`. Rewrite using `[Module.finrank_eq_card_basis bA, Fintype.card_fin, D.sp.cm.deg2]⟩`.
-/
theorem finrank_AE (D : D7) : Module.Free (AF D.host.F) (AE D) ∧ Module.Finite (AF D.host.F) (AE D) ∧
    Module.finrank (AF D.host.F) (AE D) = 2 := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  let bA := Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)
  exact ⟨Module.Free.of_basis bA, Module.Finite.of_basis bA, by
    rw [Module.finrank_eq_card_basis bA, Fintype.card_fin, D.sp.cm.deg2]⟩

/- English proof (translation)
Rewrite using `[Module.finrank_prod, Module.finrank_fintype_fun_eq_card]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_pair (K : Type) [Field K] (κ : Type) [Fintype κ] :
    Module.finrank K ((κ → K) × (κ → K)) = 2 * Fintype.card κ := by
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
  ring

/- English proof (translation)
Use `show Module.finrank K (Fin m → Fin n → L) = _`. Simplify using `[Module.finrank_pi_fintype, mul_assoc]`.
-/
theorem finrank_mat (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] (m n : ℕ) :
    Module.finrank K (Matrix (Fin m) (Fin n) L) = m * n * Module.finrank K L := by
  show Module.finrank K (Fin m → Fin n → L) = _
  simp [Module.finrank_pi_fintype, mul_assoc]

/- English proof (translation)
Use `haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial`. Take `⟨h1, h2, hAE⟩` from `finrank_AE D`. Establish `h` using `e.finrank_eq`. Establish `ha : Module.finrank (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (AE D)) = T.rank * S.rank * 2` using `by show Module.finrank (AF D.host.F) (Fin T.rank → Fin S.rank → AE D) = _`. Simplify using `[Module.finrank_pi_fintype, hAE, mul_assoc]`.

Establish `hb : Module.finrank (AF D.host.F) ((κ → AF D.host.F) × (κ → AF D.host.F)) = 2 * Fintype.card κ`. Rewrite using `[Module.finrank_prod, Module.finrank_fintype_fun_eq_card]`. Expand and normalize the polynomial expressions, which then agree. Establish `: T.rank * S.rank * 2 = 2 * Fintype.card κ` using `ha.symm.trans (h.trans hb)`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_eq (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) :
    Fintype.card κ = T.rank * S.rank := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  obtain ⟨h1, h2, hAE⟩ := finrank_AE D
  have h := e.finrank_eq
  have ha : Module.finrank (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (AE D)) = T.rank * S.rank * 2 := by
    show Module.finrank (AF D.host.F) (Fin T.rank → Fin S.rank → AE D) = _
    simp [Module.finrank_pi_fintype, hAE, mul_assoc]
  have hb : Module.finrank (AF D.host.F) ((κ → AF D.host.F) × (κ → AF D.host.F)) = 2 * Fintype.card κ := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]
    ring
  have : T.rank * S.rank * 2 = 2 * Fintype.card κ := ha.symm.trans (h.trans hb)
  omega

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Use `haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial`. Take `⟨h1, h2, hAE⟩` from `finrank_AE D`. Establish `hκ` using `card_eq D S T κ e`. Use `haveI : FiniteDimensional D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)`. Set `J1 : (κ → D.host.F) →ₗ[D.host.F] (κ → AF D.host.F)` to `LinearMap.compLeft (Algebra.linearMap D.host.F (AF D.host.F)) κ`.

Set `J : ((κ → D.host.F) × (κ → D.host.F)) →ₗ[D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)` to `J1.prodMap J1`. Set `I : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F] Matrix (Fin T.rank) (Fin S.rank) (AE D)` to `(Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix`. Set `L` to `(e.toLinearMap.restrictScalars D.host.F).comp I`. Use `haveI : Nontrivial (AE D) := Module.nontrivial_of_finrank_pos (R := AF D.host.F) (by rw [hAE]; norm_num)`. Establish `hJinj : Function.Injective J`.

Introduce and unpack `⟨y, z⟩ ⟨y', z'⟩ h`. Establish `hi` using `AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F`. Simplify using `only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h`. Use `Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)` and prove the remaining obligations. Conclude with `congrFun h.1 i`.

Conclude with `congrFun h.2 i`. Establish `hLinj : Function.Injective L`. Establish `hr : Function.Injective (inclR (F` using `D.host.F) (E := D.host.E) (AF D.host.F)) := RingHom.injective _`. Introduce `x x' h`. Use `e.injective h` as an intermediate fact.

Conclude with `Matrix.ext fun i j => hr (congrFun (congrFun this i) j)`. Establish `hle : LinearMap.range L ≤ LinearMap.range J`. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨y, z, h⟩` from `hrat x`. Conclude with `⟨(y, z), by rw [show L x = e (incM D.host.F x) from rfl, h]; rfl⟩`.

Establish `heq : LinearMap.range L = LinearMap.range J`. Use `Submodule.eq_of_le_of_finrank_eq hle ?_` and prove the remaining obligations. Rewrite using `[LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]`. Use `(finrank_mat D.host.F D.host.E T.rank S.rank).trans ((finrank_pair D.host.F κ).trans ?_).symm` and prove the remaining obligations. Rewrite using `[hκ, D.sp.cm.deg2]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `p hp`. Take `⟨y, z, rfl⟩` from `(GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp`. Establish `hm : J (y, z) ∈ LinearMap.range L` using `heq ▸ LinearMap.mem_range_self J (y, z)`. Take `⟨x, hx⟩` from `hm`.

Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `hx' : e (incM D.host.F x) = J (y, z)` using `hx`. Use `show incM D.host.F x = e.symm (J (y, z))`. Rewrite using `[← hx']`. Conclude with `(e.symm_apply_apply _).symm`.
-/
theorem onto (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F))
    (hrat : ∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i),
        fun i => algebraMap D.host.F (AF D.host.F) (z i))) :
    ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, e.symm p ∈ ratL T S := by
  haveI : Nontrivial (AF D.host.F) := (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F).nontrivial
  obtain ⟨h1, h2, hAE⟩ := finrank_AE D
  have hκ := card_eq D S T κ e
  haveI : FiniteDimensional D.host.F D.host.E :=
    Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
  let J1 : (κ → D.host.F) →ₗ[D.host.F] (κ → AF D.host.F) :=
    LinearMap.compLeft (Algebra.linearMap D.host.F (AF D.host.F)) κ
  let J : ((κ → D.host.F) × (κ → D.host.F)) →ₗ[D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) := J1.prodMap J1
  let I : Matrix (Fin T.rank) (Fin S.rank) D.host.E →ₗ[D.host.F] Matrix (Fin T.rank) (Fin S.rank) (AE D) :=
    (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toLinearMap.mapMatrix
  let L := (e.toLinearMap.restrictScalars D.host.F).comp I
  haveI : Nontrivial (AE D) := Module.nontrivial_of_finrank_pos (R := AF D.host.F) (by rw [hAE]; norm_num)
  have hJinj : Function.Injective J := by
    rintro ⟨y, z⟩ ⟨y', z'⟩ h
    have hi := AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F
    simp only [J, J1, LinearMap.prodMap_apply, Prod.mk.injEq] at h
    refine Prod.ext (funext fun i => hi ?_) (funext fun i => hi ?_)
    · exact congrFun h.1 i
    · exact congrFun h.2 i
  have hLinj : Function.Injective L := by
    have hr : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := RingHom.injective _
    intro x x' h
    have := e.injective h
    exact Matrix.ext fun i j => hr (congrFun (congrFun this i) j)
  have hle : LinearMap.range L ≤ LinearMap.range J := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact ⟨(y, z), by rw [show L x = e (incM D.host.F x) from rfl, h]; rfl⟩
  have heq : LinearMap.range L = LinearMap.range J := by
    refine Submodule.eq_of_le_of_finrank_eq hle ?_
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hJinj]
    refine (finrank_mat D.host.F D.host.E T.rank S.rank).trans ((finrank_pair D.host.F κ).trans ?_).symm
    rw [hκ, D.sp.cm.deg2]
    ring
  intro p hp
  obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
  have hm : J (y, z) ∈ LinearMap.range L := heq ▸ LinearMap.mem_range_self J (y, z)
  obtain ⟨x, hx⟩ := hm
  refine ⟨x, ?_⟩
  have hx' : e (incM D.host.F x) = J (y, z) := hx
  show incM D.host.F x = e.symm (J (y, z))
  rw [← hx']
  exact (e.symm_apply_apply _).symm

end GlobalTheory.RatDarbouxTransfer

namespace GlobalTheory.RatDarbouxTransfer

open scoped Pointwise

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D ψ _ S T JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕`. Use `haveI hMT : IsModuleTopology (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (AE D)) := inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → AE D))`. Use `letI mP : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _`. Use `haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩`. Use `haveI : BorelSpace (Formalism.IndefR.Datum.WO S T) := ⟨rfl⟩`.

Set `ce : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃L[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)` to `{ co.e with continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }`. Set `ca : Formalism.IndefR.Datum.WO S T ≃ₜ+ (κ → AF D.host.F) × (κ → AF D.host.F)` to `{ co.e.toAddEquiv with continuous_toFun := ce.continuous continuous_invFun := ce.symm.continuous }`. Set `me : Formalism.IndefR.Datum.WO S T ≃ᵐ (κ → AF D.host.F) × (κ → AF D.host.F)` to `ca.toHomeomorph.toMeasurableEquiv`. Establish `into : ∀ g ∈ ratL T S, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ`. Introduce and unpack `_ ⟨x, rfl⟩`.

Take `⟨y, z, h⟩` from `hrat x`. Conclude with `(GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩`. Establish `onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, co.e.symm p ∈ ratL T S` using `onto D S T κ co.e hrat`. Use `⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `ca.isAddHaarMeasure_map ν`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hqmp : Measure.QuasiMeasurePreserving me.symm (ν.map me) ν` using `(MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving`. Establish `hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕` using `Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩`. Rewrite using `[hpre]`. Conclude with `h𝓕.nullMeasurableSet.preimage hqmp`.

Rewrite using `[me.measurableEmbedding.ae_map_iff] filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩`. Use `⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩` and prove the remaining obligations. Use `show co.e ((g : Formalism.IndefR.Datum.WO S T) + x) = co.e g + co.e x`. Rewrite using `[map_add]`. Introduce `p q hpq`.

Set `g : ratL T S` to `⟨co.e.symm p, onto' p p.2⟩`. Set `h : ratL T S` to `⟨co.e.symm q, onto' q q.2⟩`. Establish `hgh : g ≠ h`. Introduce `e`. Apply `hpq` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (fun t : ratL T S => co.e (t : Formalism.IndefR.Datum.WO S T)) e` as an intermediate fact. Simplify `this` using `[g, h]`. Establish `himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) (k : ratL T S), (k : Formalism.IndefR.Datum.WO S T) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕)`. Introduce `r k hk`.

Rewrite using `[← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]`. Use `Set.image_congr fun w _ => ?_` and prove the remaining obligations. Use `show (r : (κ → AF D.host.F) × (κ → AF D.host.F)) + co.e w = co.e ((k : Formalism.IndefR.Datum.WO S T) + w)`. Rewrite using `[map_add, hk, LinearEquiv.apply_symm_apply]`. Use `show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)`.

Rewrite using `[himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply, me.preimage_image]`. Conclude with `h𝓕.aedisjoint hgh`. Introduce `f`. Rewrite using `[MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]`. Both sides reduce to the same expression.
-/
theorem haar_fundDomain_transfer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
      (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
      ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
      ∀ (κ : Type) [Fintype κ]
        (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
        (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
          co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
        ∀ (ν : Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)), ν.IsAddHaarMeasure →
          IsAddFundamentalDomain (ratL T S) 𝓕 ν →
          ∃ (ν' : @Measure ((κ → AF D.host.F) × (κ → AF D.host.F)) (borel _)) (𝓕' : Set ((κ → AF D.host.F) × (κ → AF D.host.F))),
            @Measure.IsAddHaarMeasure _ _ _ (borel _) ν' ∧
            @IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) _ _ _ (borel _) 𝓕' ν' ∧
            ∀ f : (κ → AF D.host.F) × (κ → AF D.host.F) → ℂ,
              ∫⁻ w in 𝓕, ‖f (co.e w)‖ₑ ^ 2 ∂ν = ∫⁻ w in 𝓕', ‖f w‖ₑ ^ 2 ∂ν' := by
  intro D ψ _ S T JA JB ξ _ _ κ _ co hrat ν 𝓕 hν h𝓕
  haveI hMT : IsModuleTopology (AF D.host.F) (Matrix (Fin T.rank) (Fin S.rank) (AE D)) :=
    inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin T.rank → Fin S.rank → AE D))
  letI mP : MeasurableSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := borel _
  haveI : BorelSpace ((κ → AF D.host.F) × (κ → AF D.host.F)) := ⟨rfl⟩
  haveI : BorelSpace (Formalism.IndefR.Datum.WO S T) := ⟨rfl⟩
  let ce : Matrix (Fin T.rank) (Fin S.rank) (AE D) ≃L[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F) :=
    { co.e with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap co.e.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap co.e.symm.toLinearMap }
  let ca : Formalism.IndefR.Datum.WO S T ≃ₜ+ (κ → AF D.host.F) × (κ → AF D.host.F) :=
    { co.e.toAddEquiv with
      continuous_toFun := ce.continuous
      continuous_invFun := ce.symm.continuous }
  let me : Formalism.IndefR.Datum.WO S T ≃ᵐ (κ → AF D.host.F) × (κ → AF D.host.F) := ca.toHomeomorph.toMeasurableEquiv
  have into : ∀ g ∈ ratL T S, co.e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ, co.e.symm p ∈ ratL T S :=
    onto D S T κ co.e hrat
  refine ⟨ν.map me, me '' 𝓕, ?_, ?_, ?_⟩
  · exact ca.isAddHaarMeasure_map ν
  · refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (ν.map me) ν :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕 = me.symm ⁻¹' 𝓕 :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨co.e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show co.e ((g : Formalism.IndefR.Datum.WO S T) + x) = co.e g + co.e x
      rw [map_add]
    · intro p q hpq
      let g : ratL T S := ⟨co.e.symm p, onto' p p.2⟩
      let h : ratL T S := ⟨co.e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro e
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratL T S => co.e (t : Formalism.IndefR.Datum.WO S T)) e
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ) (k : ratL T S),
          (k : Formalism.IndefR.Datum.WO S T) = co.e.symm r → r +ᵥ me '' 𝓕 = me '' (k +ᵥ 𝓕) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : (κ → AF D.host.F) × (κ → AF D.host.F)) + co.e w = co.e ((k : Formalism.IndefR.Datum.WO S T) + w)
        rw [map_add, hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (ν.map me) (p +ᵥ me '' 𝓕) (q +ᵥ me '' 𝓕)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕.aedisjoint hgh
  · intro f
    rw [MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, lintegral_map_equiv]
    rfl

end GlobalTheory.RatDarbouxTransfer
