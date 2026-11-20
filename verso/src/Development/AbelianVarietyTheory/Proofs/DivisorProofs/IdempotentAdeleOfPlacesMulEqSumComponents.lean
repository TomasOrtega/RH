import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PlaneStrongApproxGeneratorImports
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct Pointwise

noncomputable section

namespace GlobalTheory.PlaceIdemSum

open GlobalTheory.CompanionTheory.SaGen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

/- English proof (translation)
Take `⟨h1, h2, h3, h4⟩` from `h`. Use `adele_ext ?_ (finAdele_ext fun u => ?_)` and prove the remaining obligations. Establish `hfin : ∀ v ∈ S₂, fstA F ((placeMapFin v).inj 1) = 0` using `fun v _ => rfl`. Establish `hinf : ∀ w ∈ S₁, fstA F ((placeMapInf w).inj 1) = singleI w 1` using `fun w _ => rfl`. Rewrite using `[map_add, map_sum, map_sum, Finset.sum_congr rfl hfin, Finset.sum_const_zero, add_zero, Finset.sum_congr rfl hinf]`.

Use `ainf_ext fun u => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `fstA F ε u = (∑ w ∈ S₁, (singleI w 1 : ∀ u : InfinitePlace F, u.Completion)) u`. Use `Eq.trans ?_ (Finset.sum_apply u S₁ (fun w => (singleI w 1 : ∀ u : InfinitePlace F, u.Completion))).symm` and prove the remaining obligations. Distinguish the cases in `hu : u ∈ S₁`. Rewrite using `[h1 u hu, Finset.sum_eq_single u (fun w _ hw => singleI_ne (Ne.symm hw) 1) (fun h => absurd hu h), singleI_self]`.

Rewrite using `[h2 u hu, Finset.sum_eq_zero fun w hw => singleI_ne (fun e : u = w => hu (e ▸ hw)) 1]`. Establish `hinf : ∀ w ∈ S₁, sndA F ((placeMapInf w).inj 1) = 0` using `fun w _ => rfl`. Establish `hfin : ∀ v ∈ S₂, sndA F ((placeMapFin v).inj 1) = singleV F v 1` using `fun v _ => rfl`. Rewrite using `[map_add, map_sum, map_sum, Finset.sum_congr rfl hinf, Finset.sum_const_zero, zero_add, Finset.sum_congr rfl hfin, map_sum]`. Distinguish the cases in `hu : u ∈ S₂`.

Rewrite using `[h3 u hu, Finset.sum_eq_single u (fun v _ hv => StrongApprox.evalV_single_ne (Ne.symm hv) 1) (fun h => absurd hu h), StrongApprox.evalV_single_same]`. Rewrite using `[h4 u hu, Finset.sum_eq_zero fun v hv => StrongApprox.evalV_single_ne (fun e : u = v => hu (e ▸ hv)) 1]`.
-/
theorem idem_eq_sum (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F)
    (h : IsPlacesIdem S₁ S₂ ε) :
    ε = ∑ w ∈ S₁, (placeMapInf w).inj 1 + ∑ v ∈ S₂, (placeMapFin v).inj 1 := by
  classical
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine adele_ext ?_ (finAdele_ext fun u => ?_)
  · have hfin : ∀ v ∈ S₂, fstA F ((placeMapFin v).inj 1) = 0 := fun v _ => rfl
    have hinf : ∀ w ∈ S₁, fstA F ((placeMapInf w).inj 1) = singleI w 1 := fun w _ => rfl
    rw [map_add, map_sum, map_sum, Finset.sum_congr rfl hfin, Finset.sum_const_zero, add_zero,
      Finset.sum_congr rfl hinf]
    refine ainf_ext fun u => ?_
    change fstA F ε u = (∑ w ∈ S₁, (singleI w 1 : ∀ u : InfinitePlace F, u.Completion)) u
    refine Eq.trans ?_ (Finset.sum_apply u S₁ (fun w => (singleI w 1 : ∀ u : InfinitePlace F, u.Completion))).symm
    by_cases hu : u ∈ S₁
    · rw [h1 u hu, Finset.sum_eq_single u (fun w _ hw => singleI_ne (Ne.symm hw) 1) (fun h => absurd hu h),
        singleI_self]
    · rw [h2 u hu, Finset.sum_eq_zero fun w hw => singleI_ne (fun e : u = w => hu (e ▸ hw)) 1]
  · have hinf : ∀ w ∈ S₁, sndA F ((placeMapInf w).inj 1) = 0 := fun w _ => rfl
    have hfin : ∀ v ∈ S₂, sndA F ((placeMapFin v).inj 1) = singleV F v 1 := fun v _ => rfl
    rw [map_add, map_sum, map_sum, Finset.sum_congr rfl hinf, Finset.sum_const_zero, zero_add,
      Finset.sum_congr rfl hfin, map_sum]
    by_cases hu : u ∈ S₂
    · rw [h3 u hu, Finset.sum_eq_single u (fun v _ hv => StrongApprox.evalV_single_ne (Ne.symm hv) 1)
        (fun h => absurd hu h), StrongApprox.evalV_single_same]
    · rw [h4 u hu, Finset.sum_eq_zero fun v hv => StrongApprox.evalV_single_ne (fun e : u = v => hu (e ▸ hv)) 1]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem iB_tmul {K : Type} [Field K] [Algebra F K] [TopologicalSpace K] (P : PlaceMap F K) (y : K) (e : E) :
    iB (E := E) P (y ⊗ₜ[F] e) = P.inj y ⊗ₜ[F] e := rfl

/- English proof (translation)
Rewrite using `[Algebra.TensorProduct.map_tmul, AlgHom.id_apply, iB_tmul, P.inj_proj]`.
-/
theorem iB_map_tmul {K : Type} [Field K] [Algebra F K] [TopologicalSpace K] (P : PlaceMap F K) (x : AF F) (e : E) :
    iB P (Algebra.TensorProduct.map P.proj (AlgHom.id F E) (x ⊗ₜ[F] e)) = (P.inj 1 * x) ⊗ₜ[F] e := by
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, iB_tmul, P.inj_proj]

/- English proof (translation)
Introduce `F E _ _ _ _ S₁ S₂ ε hε a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => simp only [mul_zero, map_zero, Finset.sum_const_zero, add_zero]`. Consider the case `tmul x e`. Simplify using `only [iB_map_tmul]`.

Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.sum_tmul, ← TensorProduct.add_tmul, ← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, ← idem_eq_sum S₁ S₂ ε hε]`. Consider the case `add a b ha hb`. Rewrite using `[mul_add, ha, hb]`. Simplify using `only [map_add, Finset.sum_add_distrib]`. Normalize the expressions using the abelian group laws.
-/
theorem idem_mul_eq_sum : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε →
    ∀ a : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * a =
      ∑ w ∈ S₁, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapInf w)
          (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapInf w).proj (AlgHom.id F E) a) +
        ∑ v ∈ S₂, GlobalTheory.CompanionTheory.SaGen.iB (GlobalTheory.CompanionTheory.SaGen.placeMapFin v)
          (Algebra.TensorProduct.map (GlobalTheory.CompanionTheory.SaGen.placeMapFin v).proj (AlgHom.id F E) a) := by
  intro F E _ _ _ _ S₁ S₂ ε hε a
  induction a using TensorProduct.induction_on with
  | zero => simp only [mul_zero, map_zero, Finset.sum_const_zero, add_zero]
  | tmul x e =>
    simp only [iB_map_tmul]
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← TensorProduct.sum_tmul, ← TensorProduct.sum_tmul,
      ← TensorProduct.add_tmul, ← Finset.sum_mul, ← Finset.sum_mul, ← add_mul, ← idem_eq_sum S₁ S₂ ε hε]
  | add a b ha hb =>
    rw [mul_add, ha, hb]
    simp only [map_add, Finset.sum_add_distrib]
    abel

end GlobalTheory.PlaceIdemSum
