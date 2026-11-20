import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgAtLeAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobal.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => exact S.zero_mem`. Consider the case `tmul x y`. Proceed by induction on `y using PiTensorProduct.induction_on with`.

Consider the case `smul_tprod r φ => rw [TensorProduct.tmul_smul]`. Conclude with `S.smul_mem r (h x φ)`. Consider the case `add y z hy hz => rw [TensorProduct.tmul_add]`. Conclude with `S.add_mem hy hz`. Consider the case `add s t hs ht => exact S.add_mem hs ht`.
-/
theorem mem_of_pure {A : Type} [AddCommGroup A] [Module ℂ A] {ι : Type} [Fintype ι] {B : ι → Type}
    [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)] (S : Submodule ℂ (A ⊗[ℂ] (⨂[ℂ] i, B i)))
    (h : ∀ x φ, x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ ∈ S) : ∀ t, t ∈ S := by
  intro t
  induction t using TensorProduct.induction_on with
  | zero => exact S.zero_mem
  | tmul x y =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r φ => rw [TensorProduct.tmul_smul]; exact S.smul_mem r (h x φ)
    | add y z hy hz => rw [TensorProduct.tmul_add]; exact S.add_mem hy hz
  | add s t hs ht => exact S.add_mem hs ht

/- English proof (translation)
Introduce `y`. Proceed by induction on `y using PiTensorProduct.induction_on with`. Consider the case `smul_tprod r φ => exact S.smul_mem r (h φ)`. Consider the case `add y z hy hz => exact S.add_mem hy hz`.
-/
theorem mem_of_tprod {ι : Type} [Fintype ι] {B : ι → Type} [∀ i, AddCommGroup (B i)] [∀ i, Module ℂ (B i)]
    (S : Submodule ℂ (⨂[ℂ] i, B i)) (h : ∀ φ, PiTensorProduct.tprod ℂ φ ∈ S) : ∀ y, y ∈ S := by
  intro y
  induction y using PiTensorProduct.induction_on with
  | smul_tprod r φ => exact S.smul_mem r (h φ)
  | add y z hy hz => exact S.add_mem hy hz

def ext (M : Model σ Y W) (T : Finset (Pl F)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ :=
  fun v => if h : v ∈ T then ((φ ⟨v, h⟩ : ↥(SB (Fin n × Fin d → Fv F v))) : (Fin n × Fin d → Fv F v) → ℂ) else M.vac v

variable (M : Model σ Y W) (T : Finset (Pl F))

/- English proof (translation)
Simplify using `[ext, v.2]`.
-/
theorem ext_of_mem (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) :
    ext M T φ v.1 = (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) := by
  simp [ext, v.2]

/- English proof (translation)
Simplify using `[ext, hv]`.
-/
theorem ext_of_not_mem (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : Pl F) (hv : v ∉ T) :
    ext M T φ v = M.vac v := by
  simp [ext, hv]

/- English proof (translation)
Distinguish the cases in `hv : v ∈ T`. Rewrite using `[ext_of_mem M T φ ⟨v, hv⟩]`. Conclude with `(φ ⟨v, hv⟩).2`. Rewrite using `[ext_of_not_mem M T φ v hv]`. Conclude with `(hM.vac v).1`.
-/
theorem ext_mem_SB {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
    (v : Pl F) : ext M T φ v ∈ SB _ := by
  by_cases hv : v ∈ T
  · rw [ext_of_mem M T φ ⟨v, hv⟩]; exact (φ ⟨v, hv⟩).2
  · rw [ext_of_not_mem M T φ v hv]; exact (hM.vac v).1

/- English proof (translation)
Use `filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv`. Conclude with `ext_of_not_mem M T φ v hv`.
-/
theorem ext_vac (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = M.vac v := by
  filter_upwards [T.finite_toSet.compl_mem_cofinite] with v hv
  exact ext_of_not_mem M T φ v hv

/- English proof (translation)
Use `filter_upwards [ext_vac M T φ, hM.std] with v h1 h2`. Rewrite using `[h1, h2]`.
-/
theorem ext_std {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ∀ᶠ v in Filter.cofinite, ext M T φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [ext_vac M T φ, hM.std] with v h1 h2
  rw [h1, h2]

/- English proof (translation)
Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w ∈ T`. Distinguish the cases in `hwv : w = v.1`. Substitute `hwv` using the available equality. Rewrite using `[ext_of_mem M T _ v, Function.update_self, Function.update_self]`.

Establish `hne : (⟨w, hw⟩ : T) ≠ v` using `fun e => hwv (congrArg Subtype.val e)`. Rewrite using `[ext_of_mem M T _ ⟨w, hw⟩, Function.update_of_ne hwv, Function.update_of_ne hne, ext_of_mem M T _ ⟨w, hw⟩]`. Establish `hwv : w ≠ v.1` using `fun e => hw (e ▸ v.2)`. Rewrite using `[ext_of_not_mem M T _ w hw, Function.update_of_ne hwv, ext_of_not_mem M T _ w hw]`.
-/
theorem ext_update [DecidableEq T] (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T)
    (z : ↥(SB (Fin n × Fin d → Fv F v.1))) :
    ext M T (Function.update φ v z) = Function.update (ext M T φ) v.1 (z : (Fin n × Fin d → Fv F v.1) → ℂ) := by
  funext w
  by_cases hw : w ∈ T
  · by_cases hwv : w = v.1
    · subst hwv
      rw [ext_of_mem M T _ v, Function.update_self, Function.update_self]
    · have hne : (⟨w, hw⟩ : T) ≠ v := fun e => hwv (congrArg Subtype.val e)
      rw [ext_of_mem M T _ ⟨w, hw⟩, Function.update_of_ne hwv, Function.update_of_ne hne, ext_of_mem M T _ ⟨w, hw⟩]
  · have hwv : w ≠ v.1 := fun e => hw (e ▸ v.2)
    rw [ext_of_not_mem M T _ w hw, Function.update_of_ne hwv, ext_of_not_mem M T _ w hw]

end GlobalTheory.HoweGlobal.Transfer

end

noncomputable section

open scoped Classical

namespace GlobalTheory.HoweGlobal.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (T : Finset (Pl F))

/- English proof (translation)
The claim follows from `GlobalTheory.ThK.EvUniqInf.rest_pure f _ (ext_mem_SB M T hM φ) (ext_std M T hM φ)`.
-/
theorem rest_ext {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    Rest (evI F) ⇑f (fun x => ∏ᶠ v, ext M T φ v fun i => evFin F v (x i)) :=
  GlobalTheory.ThK.EvUniqInf.rest_pure f _ (ext_mem_SB M T hM φ) (ext_std M T hM φ)

/- English proof (translation)
Rewrite using `[ext_update]`. Use `GlobalTheory.ThK.LocalOps.acts_pure v.1 Op f (ext M T φ) _ (GlobalTheory.TensUniq.pure_mem_schA f _ (ext_mem_SB M T hM φ) (ext_std M T hM φ)) (GlobalTheory.PureFactor.mulSupport_finite _ (ext_std M T hM φ)) ?_` and prove the remaining obligations. Rewrite using `[ext_of_mem]`. Conclude with `h`.
-/
theorem acts_ext [DecidableEq T] {ψ : AddChar (AF F) ℂ} (hM : M.IsGood ψ) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (v : T) (z : ↥(SB (Fin n × Fin d → Fv F v.1)))
    (Op : ((Fin n × Fin d → AF F) → ℂ) → (Fin n × Fin d → AF F) → ℂ)
    (h : Acts (evFin F v.1) Op (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) (z : (Fin n × Fin d → Fv F v.1) → ℂ)) :
    Op (pure f (ext M T φ)) = pure f (ext M T (Function.update φ v z)) := by
  rw [ext_update]
  refine GlobalTheory.ThK.LocalOps.acts_pure v.1 Op f (ext M T φ) _
    (GlobalTheory.TensUniq.pure_mem_schA f _ (ext_mem_SB M T hM φ) (ext_std M T hM φ))
    (GlobalTheory.PureFactor.mulSupport_finite _ (ext_std M T hM φ)) ?_
  rw [ext_of_mem]
  exact h

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨f, ext M T φ, hf, ext_mem_SB M T hM φ, ext_vac M T φ, rfl⟩`.
-/
theorem pure_mem_algD {ψ : AddChar (AF F) ℂ} (emb : ∀ w : InfinitePlace F, EmbOver E w) (hM : M.IsGood ψ)
    (f : SInf F (Fin n × Fin d)) (hf : f ∈ M.Pol ψ emb) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    pure f (ext M T φ) ∈ GlobalTheory.SquareAgree.algD M ψ emb :=
  Submodule.subset_span ⟨f, ext M T φ, hf, ext_mem_SB M T hM φ, ext_vac M T φ, rfl⟩

end GlobalTheory.HoweGlobal.Transfer

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HoweGlobal.Transfer in

/- English proof (translation)
Introduce `_ F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hm N hN T _ L hL`. Establish `hM` using `hm.triple.geo.hM`. Establish `hLe : ∀ (f : ↥(G.M.Pol Bs.ψ Bs.emb)) (φ : ∀ v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1))), L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = pure (f : SInf F (Fin a × Fin (a + a'))) (ext G.M T φ)` using `fun f φ => hL f φ _ (fun v h => ext_of_mem G.M T φ ⟨v, h⟩) (fun v h => ext_of_not_mem G.M T φ v h)`. Establish `hpA` using `pure_mem_algD G.M T Bs.emb hM`. Establish `hR` using `rest_ext G.M T hM`.

Establish `hLA : ∀ t, L t ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb`. Introduce `t`. Use `mem_of_pure ((GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb).comap L) (fun x φ => ?_) t` and prove the remaining obligations. Rewrite using `[Submodule.mem_comap, hLe]`. Conclude with `hpA _ x.2 φ`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `key : ∀ φ : ∀ v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1)), GlobalTheory.HoweGlobal.relInf Bs G om ≤ N.comap (L ∘ₗ (TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ φ))`. Introduce `φ`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `x (⟨γ, hγ, f, hf, hD⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)`.

Use `show L (x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N`. Rewrite using `[hLe]`. Conclude with `hN.2.2.2 γ hγ _ (hpA f hf φ) _ (hpA _ x.2 φ) (fun z => hD _ (hR f φ) z)`. Use `show L ((f₁ - f) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N`. Establish `e : pure ((f₁ : SInf F (Fin a × Fin (a + a')))) (ext G.M T φ) = om (k, 1) (pure (f : SInf F (Fin a × Fin (a + a'))) (ext G.M T φ))` using `(hA _ (hR _ φ)).symm`.

Rewrite using `[TensorProduct.sub_tmul, map_sub, hLe, hLe, e]`. Conclude with `hN.2.2.1 k hk _ (hpA _ f.2 φ)`. Introduce `x hx y`. Conclude with `mem_of_tprod (N.comap (L ∘ₗ TensorProduct.mk ℂ _ _ x)) (fun φ => key φ hx) y`. Introduce `v x hx x₀ y`.

Set `ℓ` to `L ∘ₗ TensorProduct.mk ℂ _ _ x₀ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap y v`. Establish `hℓ : ∀ z, ℓ z = L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y v z))` using `fun z => rfl`. Establish `hsub : augAt om v.1 ≤ (N.comap ℓ).map (SB (Fin a × Fin (a + a') → Fv F v.1)).subtype`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩`.

Use `⟨⟨φ₁, hφ₁⟩ - ⟨φ, hφ⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, Submodule.mem_comap, map_sub, hℓ, hℓ, hLe, hLe]`. Establish `e : om (g, 1) (pure (x₀ : SInf F (Fin a × Fin (a + a'))) (ext G.M T (Function.update y v ⟨φ, hφ⟩))) = pure (x₀ : SInf F (Fin a × Fin (a + a'))) (ext G.M T (Function.update y v ⟨φ₁, hφ₁⟩))`. Rewrite using `[acts_ext G.M T hM (x₀ : SInf F (Fin a × Fin (a + a'))) (Function.update y v ⟨φ, hφ⟩) v ⟨φ₁, hφ₁⟩ ⇑(om (g, 1)) (by rw [Function.update_self]; exact hA), Function.update_idem]`. Rewrite using `[← e]`.

Conclude with `hN.2.1 v.1 g hg _ (hpA _ x₀.2 _)`. Take `⟨x', hx', he⟩` from `hsub (Submodule.mem_comap.1 hx)`. Establish `: x' = x` using `Subtype.ext he`. Rewrite using `[← hℓ, ← this]`. Conclude with `hx'`.

Introduce `g hg t ht`. Break down `hg with ⟨k, hk, hkA⟩ | ⟨γ, hγ, hgD⟩` into its components or cases. Establish `e : ∀ t, L (TensorProduct.map g LinearMap.id t) = om (1, k) (L t)`. Introduce `t`. Use `LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map g LinearMap.id) ((om (1, k)) ∘ₗ L)) (fun x φ => ?_) t)` and prove the remaining obligations.

Use `LinearMap.mem_eqLocus.2 ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, hLe]`. Conclude with `(hkA x _ (hR _ φ)).symm`. Rewrite using `[e]`. Conclude with `hN.1.2.2.1 k hk _ ht`.

Set `S : Submodule ℂ (↥(G.M.Pol Bs.ψ Bs.emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1))))` to `{ carrier := {t | ∀ z, HasDerivAt (fun s : ℝ => om (1, γ (Multiplicative.ofAdd s)) (L t) z) (L (TensorProduct.map g LinearMap.id t) z) 0} add_mem' := fun {t₁ t₂} h₁ h₂ z => by`. Simplify using `only [map_add, Pi.add_apply]`. Conclude with `(h₁ z).add (h₂ z)`. Use the proof step `zero_mem' := fun z => by`. Simplify using `only [map_zero, Pi.zero_apply]`.

Conclude with `hasDerivAt_const 0 0`. Use the proof step `smul_mem' := fun c t h z => by`. Simplify using `only [map_smul, Pi.smul_apply, smul_eq_mul]`. Conclude with `(h z).const_mul c }`. Establish `hS : ∀ t, t ∈ S` using `mem_of_pure S (fun x φ z => by`.

Simplify using `only [TensorProduct.map_tmul, LinearMap.id_apply, hLe]`. Conclude with `hgD x _ (hR _ φ) z)`. Conclude with `hN.1.2.2.2 γ hγ _ ht _ (hLA _) (hS t)`. Introduce `v g hg t ht`. Take `⟨h, hh, hA⟩` from `hg`.

Establish `e : ∀ t, L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g)) t) = om (1, h) (L t)`. Introduce `t`. Use `LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g))) ((om (1, h)) ∘ₗ L)) (fun x φ => ?_) t)` and prove the remaining obligations. Use `LinearMap.mem_eqLocus.2 ?_` and prove the remaining obligations. Establish `hφ : (fun w => (Function.update (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g w) (φ w)) = Function.update φ v (g (φ v))`.

Use function extensionality and compare the values at `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne hw]`.

Simplify using `only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod, hLe]`. Rewrite using `[hφ, acts_ext G.M T hM _ φ v (g (φ v)) _ (hA (φ v))]`. Rewrite using `[e]`. Conclude with `hN.1.2.1 v.1 h hh _ ht`.
-/
theorem GlobalTheory.HoweGlobal.tensor_transfer : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ∀ N, GlobalTheory.CoinvKer.IsThetaSub om Bs.emb (GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb) N →
    ∀ (T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) [DecidableEq {v // v ∈ T}]
      (L : ↥(G.M.Pol Bs.ψ Bs.emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ] ((Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)),
      (∀ (f : ↥(G.M.Pol Bs.ψ Bs.emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = G.M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a × Fin (a + a'))) φ') →
      (∀ x ∈ GlobalTheory.HoweGlobal.relInf Bs G om, ∀ y, L (x ⊗ₜ[ℂ] y) ∈ N) ∧
      (∀ v : T, ∀ x ∈ GlobalTheory.HoweGlobal.relFin G om v.1, ∀ (x₀ : ↥(G.M.Pol Bs.ψ Bs.emb))
          (y : ∀ w : T, ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1))),
          L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y v x)) ∈ N) ∧
      (∀ g ∈ GlobalTheory.HoweGlobal.opInf Bs G om, ∀ t, L t ∈ N → L (TensorProduct.map g LinearMap.id t) ∈ N) ∧
      (∀ v : T, ∀ g ∈ GlobalTheory.HoweGlobal.opFin G om v.1, ∀ t, L t ∈ N →
        L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
          (fun w : T => (LinearMap.id : ↥(GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w.1)) →ₗ[ℂ] _)) v g)) t) ∈ N) := by
  intro _ F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hm N hN T _ L hL
  have hM := hm.triple.geo.hM
  have hLe : ∀ (f : ↥(G.M.Pol Bs.ψ Bs.emb)) (φ : ∀ v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1))),
      L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = pure (f : SInf F (Fin a × Fin (a + a'))) (ext G.M T φ) :=
    fun f φ => hL f φ _ (fun v h => ext_of_mem G.M T φ ⟨v, h⟩) (fun v h => ext_of_not_mem G.M T φ v h)
  have hpA := pure_mem_algD G.M T Bs.emb hM
  have hR := rest_ext G.M T hM
  have hLA : ∀ t, L t ∈ GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb := by
    intro t
    refine mem_of_pure ((GlobalTheory.SquareAgree.algD G.M Bs.ψ Bs.emb).comap L) (fun x φ => ?_) t
    rw [Submodule.mem_comap, hLe]
    exact hpA _ x.2 φ
  refine ⟨?_, ?_, ?_, ?_⟩
  · have key : ∀ φ : ∀ v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1)),
        GlobalTheory.HoweGlobal.relInf Bs G om ≤ N.comap (L ∘ₗ (TensorProduct.mk ℂ _ _).flip (PiTensorProduct.tprod ℂ φ)) := by
      intro φ
      refine Submodule.span_le.2 ?_
      rintro x (⟨γ, hγ, f, hf, hD⟩ | ⟨k, hk, f, f₁, hA, rfl⟩)
      · show L (x ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        rw [hLe]
        exact hN.2.2.2 γ hγ _ (hpA f hf φ) _ (hpA _ x.2 φ) (fun z => hD _ (hR f φ) z)
      · show L ((f₁ - f) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) ∈ N
        have e : pure ((f₁ : SInf F (Fin a × Fin (a + a')))) (ext G.M T φ) =
            om (k, 1) (pure (f : SInf F (Fin a × Fin (a + a'))) (ext G.M T φ)) := (hA _ (hR _ φ)).symm
        rw [TensorProduct.sub_tmul, map_sub, hLe, hLe, e]
        exact hN.2.2.1 k hk _ (hpA _ f.2 φ)
    intro x hx y
    exact mem_of_tprod (N.comap (L ∘ₗ TensorProduct.mk ℂ _ _ x)) (fun φ => key φ hx) y
  · intro v x hx x₀ y
    let ℓ := L ∘ₗ TensorProduct.mk ℂ _ _ x₀ ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap y v
    have hℓ : ∀ z, ℓ z = L (x₀ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (Function.update y v z)) := fun z => rfl
    have hsub : augAt om v.1 ≤ (N.comap ℓ).map (SB (Fin a × Fin (a + a') → Fv F v.1)).subtype := by
      refine Submodule.span_le.2 ?_
      rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
      refine ⟨⟨φ₁, hφ₁⟩ - ⟨φ, hφ⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, map_sub, hℓ, hℓ, hLe, hLe]
      have e : om (g, 1) (pure (x₀ : SInf F (Fin a × Fin (a + a'))) (ext G.M T (Function.update y v ⟨φ, hφ⟩))) =
          pure (x₀ : SInf F (Fin a × Fin (a + a'))) (ext G.M T (Function.update y v ⟨φ₁, hφ₁⟩)) := by
        rw [acts_ext G.M T hM (x₀ : SInf F (Fin a × Fin (a + a'))) (Function.update y v ⟨φ, hφ⟩) v ⟨φ₁, hφ₁⟩ ⇑(om (g, 1))
          (by rw [Function.update_self]; exact hA), Function.update_idem]
      rw [← e]
      exact hN.2.1 v.1 g hg _ (hpA _ x₀.2 _)
    obtain ⟨x', hx', he⟩ := hsub (Submodule.mem_comap.1 hx)
    have : x' = x := Subtype.ext he
    rw [← hℓ, ← this]
    exact hx'
  · intro g hg t ht
    rcases hg with ⟨k, hk, hkA⟩ | ⟨γ, hγ, hgD⟩
    · have e : ∀ t, L (TensorProduct.map g LinearMap.id t) = om (1, k) (L t) := by
        intro t
        refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map g LinearMap.id)
          ((om (1, k)) ∘ₗ L)) (fun x φ => ?_) t)
        refine LinearMap.mem_eqLocus.2 ?_
        simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact (hkA x _ (hR _ φ)).symm
      rw [e]
      exact hN.1.2.2.1 k hk _ ht
    · let S : Submodule ℂ (↥(G.M.Pol Bs.ψ Bs.emb) ⊗[ℂ]
          (⨂[ℂ] v : T, ↥(SB (Fin a × Fin (a + a') → Fv F v.1)))) :=
        { carrier := {t | ∀ z, HasDerivAt (fun s : ℝ => om (1, γ (Multiplicative.ofAdd s)) (L t) z)
            (L (TensorProduct.map g LinearMap.id t) z) 0}
          add_mem' := fun {t₁ t₂} h₁ h₂ z => by
            simp only [map_add, Pi.add_apply]
            exact (h₁ z).add (h₂ z)
          zero_mem' := fun z => by
            simp only [map_zero, Pi.zero_apply]
            exact hasDerivAt_const 0 0
          smul_mem' := fun c t h z => by
            simp only [map_smul, Pi.smul_apply, smul_eq_mul]
            exact (h z).const_mul c }
      have hS : ∀ t, t ∈ S := mem_of_pure S (fun x φ z => by
        simp only [TensorProduct.map_tmul, LinearMap.id_apply, hLe]
        exact hgD x _ (hR _ φ) z)
      exact hN.1.2.2.2 γ hγ _ ht _ (hLA _) (hS t)
  · intro v g hg t ht
    obtain ⟨h, hh, hA⟩ := hg
    have e : ∀ t, L (TensorProduct.map LinearMap.id (PiTensorProduct.map (Function.update
        (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g)) t) = om (1, h) (L t) := by
      intro t
      refine LinearMap.mem_eqLocus.1 (mem_of_pure (LinearMap.eqLocus (L ∘ₗ TensorProduct.map LinearMap.id
        (PiTensorProduct.map (Function.update
          (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g)))
          ((om (1, h)) ∘ₗ L)) (fun x φ => ?_) t)
      refine LinearMap.mem_eqLocus.2 ?_
      have hφ : (fun w => (Function.update
          (fun w : T => (LinearMap.id : ↥(SB (Fin a × Fin (a + a') → Fv F w.1)) →ₗ[ℂ] _)) v g w) (φ w)) =
          Function.update φ v (g (φ v)) := by
        funext w
        by_cases hw : w = v
        · subst hw; simp
        · simp [Function.update_of_ne hw]
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply, PiTensorProduct.map_tprod, hLe]
      rw [hφ, acts_ext G.M T hM _ φ v (g (φ v)) _ (hA (φ v))]
    rw [e]
    exact hN.1.2.1 v.1 h hh _ ht

end
