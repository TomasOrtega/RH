import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ nS nT N e hrat y z`. Use `haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial`. Set `I : Matrix (Fin nT) (Fin nS) E →ₗ[F] Formalism.IndefR.DatumF.WOF F E nS nT` to `(Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix`. Establish `hI : ∀ x, I x = Formalism.IndefR.DatumF.ratWF x` using `fun x => rfl`. Set `L : Matrix (Fin nT) (Fin nS) E →ₗ[F] GlobalTheory.ThetaTransform.VA F N` to `(e.toLinearMap.restrictScalars F).comp I`.

Establish `hL : ∀ x, L x = e (Formalism.IndefR.DatumF.ratWF x)` using `fun x => by rw [← hI]; rfl`. Set `r : (Fin N → F) →ₗ[F] (Fin N → AF F)` to `LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)`. Set `R : ((Fin N → F) × (Fin N → F)) →ₗ[F] GlobalTheory.ThetaTransform.VA F N` to `LinearMap.prodMap r r`. Establish `hR : ∀ y z, R (y, z) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)` using `fun _ _ => rfl`. Establish `hAinj : Function.Injective (algebraMap F (AF F))` using `AdeleRing.algebraMap_injective _ _`.

Establish `hrinj : Function.Injective r` using `fun a b h => funext fun i => hAinj (congrFun h i)`. Establish `hRinj : Function.Injective R` using `fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))`. Establish `hIinj : Function.Injective I` using `fun a b h => Matrix.ext fun i j => Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)`. Establish `hLinj : Function.Injective L` using `e.injective.comp hIinj`. Establish `hle : LinearMap.range L ≤ LinearMap.range R`.

Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨y', z', h⟩` from `hrat x`. Conclude with `⟨(y', z'), by rw [hR, hL, h]⟩`. Establish `hdim : Fintype.card (Fin nT) * Fintype.card (Fin nS) * Module.finrank F E = N + N`. Establish `h1` using `e.finrank_eq`.

Rewrite `h1` using `[Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun]`. Conclude with `h1`. Establish `hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R)`. Rewrite using `[LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix, Module.finrank_prod, Module.finrank_fin_fun, hdim]`. Establish `heq` using `Submodule.eq_of_le_of_finrank_eq hle hfin`.

Take `⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L` from `heq ▸ ⟨(y, z), rfl⟩`. Conclude with `⟨x, by rw [← hL, hx, hR]⟩`.
-/
theorem GlobalTheory.WeilSchrodinger.rat_onto_of_rat_maps_F : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT N : ℕ)
    (e : Formalism.IndefR.DatumF.WOF F E nS nT ≃ₗ[AF F] GlobalTheory.ThetaTransform.VA F N),
    (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : Fin N → F, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) →
    ∀ y z : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, e (Formalism.IndefR.DatumF.ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := by
  intro F E _ _ _ _ _ nS nT N e hrat y z
  haveI : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  let I : Matrix (Fin nT) (Fin nS) E →ₗ[F] Formalism.IndefR.DatumF.WOF F E nS nT :=
    (Algebra.TensorProduct.includeRight (R := F) (A := AF F) (B := E)).toLinearMap.mapMatrix
  have hI : ∀ x, I x = Formalism.IndefR.DatumF.ratWF x := fun x => rfl
  let L : Matrix (Fin nT) (Fin nS) E →ₗ[F] GlobalTheory.ThetaTransform.VA F N := (e.toLinearMap.restrictScalars F).comp I
  have hL : ∀ x, L x = e (Formalism.IndefR.DatumF.ratWF x) := fun x => by rw [← hI]; rfl
  let r : (Fin N → F) →ₗ[F] (Fin N → AF F) :=
    LinearMap.pi fun i => (Algebra.linearMap F (AF F)).comp (LinearMap.proj i)
  let R : ((Fin N → F) × (Fin N → F)) →ₗ[F] GlobalTheory.ThetaTransform.VA F N := LinearMap.prodMap r r
  have hR : ∀ y z, R (y, z) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) := fun _ _ => rfl
  have hAinj : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective _ _
  have hrinj : Function.Injective r := fun a b h => funext fun i => hAinj (congrFun h i)
  have hRinj : Function.Injective R := fun a b h => Prod.ext (hrinj (congrArg Prod.fst h)) (hrinj (congrArg Prod.snd h))
  have hIinj : Function.Injective I := fun a b h => Matrix.ext fun i j =>
    Algebra.TensorProduct.includeRight_injective hAinj (congrFun (congrFun h i) j)
  have hLinj : Function.Injective L := e.injective.comp hIinj
  have hle : LinearMap.range L ≤ LinearMap.range R := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y', z', h⟩ := hrat x
    exact ⟨(y', z'), by rw [hR, hL, h]⟩
  have hdim : Fintype.card (Fin nT) * Fintype.card (Fin nS) * Module.finrank F E = N + N := by
    have h1 := e.finrank_eq
    rw [Module.finrank_matrix, Module.finrank_baseChange, Module.finrank_prod, Module.finrank_fin_fun] at h1
    exact h1
  have hfin : Module.finrank F (LinearMap.range L) = Module.finrank F (LinearMap.range R) := by
    rw [LinearMap.finrank_range_of_inj hLinj, LinearMap.finrank_range_of_inj hRinj, Module.finrank_matrix,
      Module.finrank_prod, Module.finrank_fin_fun, hdim]
  have heq := Submodule.eq_of_le_of_finrank_eq hle hfin
  obtain ⟨x, hx⟩ : (R (y, z)) ∈ LinearMap.range L := heq ▸ ⟨(y, z), rfl⟩
  exact ⟨x, by rw [← hL, hx, hR]⟩
