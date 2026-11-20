import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProduStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterRestrictionStatement

noncomputable section

namespace GlobalTheory.ThK.ModelPol

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def finPr {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : (κ → Af F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pure_eq {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure f φ = pureA F f (finPr φ) := rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩`.
-/
theorem finPr_mem {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) : finPr φ ∈ SB _ :=
  ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩

/- English proof (translation)
Establish `key : ∀ v : Pl F, ∃ p : κ → Fv F v, φ v p ≠ 0 ∧ (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, p i ∈ v.adicCompletionIntegers F)`. Introduce `v`. Take `⟨p, hp⟩` from `Function.ne_iff.1 (h0 v)`. Use `⟨p, hp, fun h => ?_⟩` and prove the remaining obligations. Rewrite `hp` using `[h]`.

Conclude with `Set.mem_of_indicator_ne_zero hp`. Use `choose p hp hp' using key`. Use `⟨fun i => ⟨fun v => p v i, ?_⟩, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hstd] with v hv using hp' v hv i`. Conclude with `finprod_induction (fun z : ℂ => z ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) fun v => hp v`.
-/
theorem exists_finPr_ne {κ : Type} [Fintype κ] (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) : ∃ y, finPr φ y ≠ 0 := by
  have key : ∀ v : Pl F, ∃ p : κ → Fv F v, φ v p ≠ 0 ∧
      (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, p i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨p, hp⟩ := Function.ne_iff.1 (h0 v)
    refine ⟨p, hp, fun h => ?_⟩
    rw [h] at hp
    exact Set.mem_of_indicator_ne_zero hp
  choose p hp hp' using key
  refine ⟨fun i => ⟨fun v => p v i, ?_⟩, ?_⟩
  · filter_upwards [hstd] with v hv using hp' v hv i
  · exact finprod_induction (fun z : ℂ => z ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) fun v => hp v

def pt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain MeasureTheory Filter Topology in
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.WeilM.pureA _root_.GlobalTheory.ThK.ModelPol.pt`. Simplify using the standard rewrite rules.
-/
theorem _root_.GlobalTheory.ThK.ModelPol.pureA_pt {κ : Type}
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) :
    _root_.GlobalTheory.WeilM.pureA F f g (_root_.GlobalTheory.ThK.ModelPol.pt x y) = f x * g y := by
  unfold _root_.GlobalTheory.WeilM.pureA _root_.GlobalTheory.ThK.ModelPol.pt
  simp

open scoped Classical in

/- English proof (translation)
Introduce `g _`. Use `⟨g y • (BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.proj_apply, pureA_pt]`. Simplify using `[mul_comm]`.
-/
theorem proj_adm {κ : Type} [Fintype κ] (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) :
    (LinearMap.proj (pt x y) : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g y • (BoundedContinuousFunction.evalCLM ℂ x).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩
  rw [LinearMap.proj_apply, pureA_pt]
  simp [mul_comm]

section

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

/- English proof (translation)
Establish `hG : ∀ f, M.IsGauss ψ τ f ↔ M'.IsGauss ψ τ (ei f)` using `fun f => by`. Use `exists_congr fun ε => forall₂_congr fun u u' => forall₃_congr fun hu hu' _ => ⟨fun h g g' hg hg' => ?_, fun h g g' hg hg' => ?_⟩` and prove the remaining obligations. Rewrite using `[(hD' u hu _ _).1 hg, (hD' u' hu' _ _).1 hg', ← hi u hu, ← hi u' hu', h _ _ ((hD u hu _ _).2 rfl) ((hD u' hu' _ _).2 rfl), map_smul]`. Apply `hb.1` to reduce the goal to its premises. Rewrite using `[(hD u hu _ _).1 hg, (hD u' hu' _ _).1 hg', map_smul, hi u hu, hi u' hu']`.

Conclude with `h _ _ ((hD' u hu _ _).2 rfl) ((hD' u' hu' _ _).2 rfl)`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.map_le_iff_le_comap]`. Use `sInf_le ⟨fun f hf => ?_, fun u hu f hf f₁ h₁ => ?_⟩` and prove the remaining obligations. Conclude with `Submodule.mem_sInf.2 fun N hN => hN.1 _ ((hG f).1 hf)`.

Use `Submodule.mem_sInf.2 fun N hN => hN.2 u hu (ei f) (Submodule.mem_sInf.1 hf N hN) _ ?_` and prove the remaining obligations. Rewrite using `[hD' u hu, (hD u hu _ _).1 h₁, hi u hu]`. Use `sInf_le ⟨fun g hg => ?_, ?_⟩` and prove the remaining obligations. Take `⟨f, rfl⟩` from `hb.2 g`. Conclude with `Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun N hN => hN.1 _ ((hG f).2 hg))`.

Introduce and unpack `u hu _ ⟨f, hf, rfl⟩ g₁ h₁`. Rewrite using `[(hD' u hu _ _).1 h₁, ← hi u hu]`. Conclude with `Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ ((hD u hu _ _).2 rfl))`.
-/
theorem pol_map (M M' : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (D D' : Matrix (Fin n) (Fin d) (AE F E) → SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hD : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D u f)
    (hD' : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M'.heisLine ψ u) f f₁ ↔ f₁ = D' u f)
    (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) (hb : Function.Bijective ei)
    (hi : ∀ u, At (evI F) u → ∀ f, ei (D u f) = D' u (ei f)) : (M.Pol ψ τ).map ei = M'.Pol ψ τ := by
  have hG : ∀ f, M.IsGauss ψ τ f ↔ M'.IsGauss ψ τ (ei f) := fun f => by
    refine exists_congr fun ε => forall₂_congr fun u u' => forall₃_congr fun hu hu' _ => ⟨fun h g g' hg hg' => ?_, fun h g g' hg hg' => ?_⟩
    · rw [(hD' u hu _ _).1 hg, (hD' u' hu' _ _).1 hg', ← hi u hu, ← hi u' hu',
        h _ _ ((hD u hu _ _).2 rfl) ((hD u' hu' _ _).2 rfl), map_smul]
    · apply hb.1
      rw [(hD u hu _ _).1 hg, (hD u' hu' _ _).1 hg', map_smul, hi u hu, hi u' hu']
      exact h _ _ ((hD' u hu _ _).2 rfl) ((hD' u' hu' _ _).2 rfl)
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    refine sInf_le ⟨fun f hf => ?_, fun u hu f hf f₁ h₁ => ?_⟩
    · exact Submodule.mem_sInf.2 fun N hN => hN.1 _ ((hG f).1 hf)
    · refine Submodule.mem_sInf.2 fun N hN => hN.2 u hu (ei f) (Submodule.mem_sInf.1 hf N hN) _ ?_
      rw [hD' u hu, (hD u hu _ _).1 h₁, hi u hu]
  · refine sInf_le ⟨fun g hg => ?_, ?_⟩
    · obtain ⟨f, rfl⟩ := hb.2 g
      exact Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun N hN => hN.1 _ ((hG f).2 hg))
    · rintro u hu _ ⟨f, hf, rfl⟩ g₁ h₁
      rw [(hD' u hu _ _).1 h₁, ← hi u hu]
      exact Submodule.mem_map_of_mem (Submodule.mem_sInf.2 fun N hN =>
        hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) _ ((hD u hu _ _).2 rfl))

/- English proof (translation)
Establish `h1 : ActsD (evI F) (M.heisLine ψ u) f g` using `(hA F _ f g g).1 _ (fun t => by`. Use function extensionality and compare the values at `x`. Simplify using `[Model.heisLine, Darboux.rho, schr]) h`. Conclude with `⟨fun h2 => (hA F _ f f₁ g).2.2.1 _ h2 h1, fun e => e ▸ h1⟩`.
-/
theorem actsD_iff (hA : GlobalTheory.RealLift.ActsLaws) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f g : SInf F (Fin n × Fin d)) (h : GlobalTheory.RealLift.SD (fun t => M.co.rho ψ (realAd F t • u)) f g) (f₁ : SInf F (Fin n × Fin d)) :
    ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = g := by
  have h1 : ActsD (evI F) (M.heisLine ψ u) f g := (hA F _ f g g).1 _ (fun t => by
    funext x; simp [Model.heisLine, Darboux.rho, schr]) h
  exact ⟨fun h2 => (hA F _ f f₁ g).2.2.1 _ h2 h1, fun e => e ▸ h1⟩

end

/- English proof (translation)
Take `⟨χ, hχ, hr⟩` from `GlobalTheory.T.exists_hecke_character_restriction F E σ B hB`. Use `⟨χ ^ m, ⟨hχ.1.pow m, fun x => ?_⟩, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.pow_apply, hχ.2 x, one_pow]`. Apply the tactic sequence `rw [MonoidHom.pow_apply, Circle.coe_pow, hr a] split_ifs <;> simp`.
-/
theorem exists_chr (B : Base F E) (hB : B.IsGood σ) (m : ℕ) :
    ∃ χ : Chr F E, IsHecke F E χ ∧ ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m := by
  obtain ⟨χ, hχ, hr⟩ := GlobalTheory.T.exists_hecke_character_restriction F E σ B hB
  refine ⟨χ ^ m, ⟨hχ.1.pow m, fun x => ?_⟩, fun a => ?_⟩
  · rw [MonoidHom.pow_apply, hχ.2 x, one_pow]
  · rw [MonoidHom.pow_apply, Circle.coe_pow, hr a]
    split_ifs <;> simp

/- English proof (translation)
Introduce `hK F E _ _ _ _ _ σ B n d r s r' s' X W M M' hB hX hW hM hM'`. Take `⟨χX, hcX, rX⟩` from `exists_chr B hB n`. Take `⟨χW, hcW, rW⟩` from `exists_chr B hB d`. Take `⟨om, hom⟩` from `GlobalTheory.WeilExGen.exists_isWeil hK F E σ B hB n d X W r s r' s' hX hW M hM χX χW hcX hcW rX rW`. Take `⟨om', hom'⟩` from `GlobalTheory.WeilExGen.exists_isWeil hK F E σ B hB n d X W r s r' s' hX hW M' hM' χX χW hcX hcW rX rW`.

Take `⟨e, -, -, hE, hbij, -⟩` from `GlobalTheory.T.theta_model_change hK F E σ B n d X W M χX χW om r s r' s' ⟨hB, hX, hW, hM, hcX, hcW, rX, rW, hom⟩ M' om' ⟨hB, hX, hW, hM', hcX, hcW, rX, rW, hom'⟩`. Take `⟨ei, ev, -, hv, hl⟩` from `hE.loc`. Establish `hg : finPr M.vac ∈ SB _` using `finPr_mem _ (fun v => (hM.vac v).1) hM.std`. Establish `hg' : finPr M'.vac ∈ SB _` using `finPr_mem _ (fun v => (hM'.vac v).1) hM'.std`. Take `⟨y, hy⟩` from `exists_finPr_ne M.vac (fun v => (hM.vac v).2.1) hM.std`.

Take `⟨y', hy'⟩` from `exists_finPr_ne M'.vac (fun v => (hM'.vac v).2.1) hM'.std`. Establish `mem : ∀ (f : SInf F (Fin n × Fin d)) g, g ∈ SB (Fin n × Fin d → Af F) → pureA F f g ∈ schA F (Fin n × Fin d)` using `fun f g h => Submodule.subset_span ⟨f, g, h, rfl⟩`. Establish `hvac : ∀ f : SInf F (Fin n × Fin d), e (pureA F f (finPr M.vac)) = pureA F (ei f) (finPr M'.vac)` using `fun f => by`. Use `hl f M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)` as an intermediate fact. Simplify using `only [fun v => (hv v).1] at this`.

Conclude with `this`. Establish `hinj : Function.Injective ei` using `(injective_iff_map_eq_zero ei).2 fun f hf => by`. Establish `h1 : e (pureA F f (finPr M.vac)) = e 0`. Rewrite using `[hvac, hf, map_zero]`. Use function extensionality and compare the values at `x`.

Simplify using `[pureA]`. Establish `h2` using `hbij.injOn (mem f _ hg) (zero_mem _) h1`. Use `SchwartzMap.ext fun x => ?_` and prove the remaining obligations. Establish `h3` using `congrFun h2 (pt x y)`. Rewrite `h3` using `[pureA_pt]`.

Conclude with `(mul_eq_zero.1 h3).resolve_right hy`. Establish `hsl : ∀ Φ ∈ schA F (Fin n × Fin d), ∃ f, ∀ x, e Φ (pt x y') = ei f x`. Introduce `Φ hΦ`. Proceed by induction on `hΦ using Submodule.span_induction with`. Consider the case `zero => exact ⟨0, fun x => by simp⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨f, hf⟩` from `ha`. Take `⟨g, hg⟩` from `hb`. Conclude with `⟨f + g, fun x => by simp [hf, hg]⟩`. Consider the case `smul c a _ ha`.

Take `⟨f, hf⟩` from `ha`. Conclude with `⟨c • f, fun x => by simp [hf]⟩`. Consider the case `mem Φ hΦ`. Take `⟨f, g, hg, rfl⟩` from `hΦ`. Use `replace hg := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F _ g hg`.

Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `zero => exact ⟨0, fun x => by`. Rewrite using `[show pureA F f 0 = 0 from funext fun _ => mul_zero _]`. Use the proof step `simp⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨f₁, hf⟩` from `ha`. Take `⟨f₂, hg⟩` from `hb`. Conclude with `⟨f₁ + f₂, fun x => by`. Rewrite using `[show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]`. Simplify using `[hf, hg]⟩`.

Consider the case `smul c a _ ha`. Take `⟨f₁, hf⟩` from `ha`. Conclude with `⟨c • f₁, fun x => by`. Rewrite using `[show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]`. Simplify using `[hf]⟩`.

Consider the case `mem p hp`. Take `⟨φ, hφ, hs, rfl⟩` from `hp`. Establish `h1` using `hl f φ hφ (by filter_upwards [hs, hM.std] with v h1 h2 using h1.trans h2.symm)`. Use `⟨finPr (fun v => ev v (φ v)) y' • f, fun x => ?_⟩` and prove the remaining obligations. Rewrite `h1` using `[pure_eq, pure_eq]`.

Use `(congrFun h1 _).trans ?_` and prove the remaining obligations. Rewrite using `[pureA_pt]`. Simplify using `[mul_comm]`. Establish `hsurj : Function.Surjective ei` using `fun g => by`. Take `⟨Φ, hΦ, h1⟩` from `hbij.surjOn (mem g _ hg')`.

Take `⟨f, hf⟩` from `hsl Φ hΦ`. Use `⟨(finPr M'.vac y')⁻¹ • f, ?_⟩` and prove the remaining obligations. Use `SchwartzMap.ext fun x => ?_` and prove the remaining obligations. Establish `h2` using `hf x`. Rewrite `h2` using `[h1, pureA_pt]`.

Rewrite using `[map_smul, smul_apply, ← h2, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Take `⟨D, hD⟩` from `GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std`. Take `⟨D', hD'⟩` from `GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M'.co hB.std`. Establish `Heisenberg₂ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = M'.co.rho B.ψ u (e Φ)`.

Introduce `u Φ hΦ`. Establish `h1 : ∀ m : ℕ, incM F (1 : Matrix (Fin m) (Fin m) E) = 1` using `fun m => Matrix.map_one _ (map_zero _) (map_one _)`. Use `hE.Heisenberg₂ u Φ hΦ` as an intermediate fact. Rewrite `this` using `[h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]`. Then use the resulting hypothesis. Use `⟨e, hE, ei, ev, hsurj, ?_, hv, hl⟩` and prove the remaining obligations.

Use `pol_map M M' B.ψ B.emb (fun u f => D u f) (fun u f => D' u f) (fun u hu f => actsD_iff GlobalTheory.T.archActionReadings_compatible M B.ψ u f _ (hD u hu f).1) (fun u hu f => actsD_iff GlobalTheory.T.archActionReadings_compatible M' B.ψ u f _ (hD' u hu f).1) _ ⟨hinj, hsurj⟩ fun u …` and prove the remaining obligations. Use `SchwartzMap.ext fun x => ?_` and prove the remaining obligations. Establish `h1` using `(hD u hu f).1 _ hg _ (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W M M' 1 1 ∅ e hM hM' hE _ (proj_adm x y'))`. Establish `h2` using `(hD' u hu (ei f)).1 _ hg' _ (proj_adm x y')`. Simplify using `only [LinearMap.comp_apply, Heisenberg₂ _ _ (mem f _ hg), hvac] at h1`.

Establish `h3` using `h1.unique h2`. Rewrite `h3` using `[LinearMap.proj_apply, LinearMap.proj_apply, pureA_pt, pureA_pt]`. Conclude with `mul_right_cancel₀ hy' h3`.
-/
theorem exists_modelChange_pol : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d r s r' s' : ℕ) (X : Spc F E n) (W : Spc F E d) (M M' : Model σ X W), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    M.IsGood B.ψ → M'.IsGood B.ψ →
    ∃ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M' 1 1 ∅ e ∧
      ∃ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (M.Pol B.ψ B.emb).map (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) = M'.Pol B.ψ B.emb ∧
        (∀ v, ev v (M.vac v) = M'.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
  intro hK F E _ _ _ _ _ σ B n d r s r' s' X W M M' hB hX hW hM hM'
  classical
  obtain ⟨χX, hcX, rX⟩ := exists_chr B hB n
  obtain ⟨χW, hcW, rW⟩ := exists_chr B hB d
  obtain ⟨om, hom⟩ := GlobalTheory.WeilExGen.exists_isWeil hK F E σ B hB n d X W r s r' s' hX hW M hM χX χW hcX hcW rX rW
  obtain ⟨om', hom'⟩ := GlobalTheory.WeilExGen.exists_isWeil hK F E σ B hB n d X W r s r' s' hX hW M' hM' χX χW hcX hcW rX rW
  obtain ⟨e, -, -, hE, hbij, -⟩ := GlobalTheory.T.theta_model_change hK F E σ B n d X W M χX χW om r s r' s'
    ⟨hB, hX, hW, hM, hcX, hcW, rX, rW, hom⟩ M' om' ⟨hB, hX, hW, hM', hcX, hcW, rX, rW, hom'⟩
  obtain ⟨ei, ev, -, hv, hl⟩ := hE.loc
  have hg : finPr M.vac ∈ SB _ := finPr_mem _ (fun v => (hM.vac v).1) hM.std
  have hg' : finPr M'.vac ∈ SB _ := finPr_mem _ (fun v => (hM'.vac v).1) hM'.std
  obtain ⟨y, hy⟩ := exists_finPr_ne M.vac (fun v => (hM.vac v).2.1) hM.std
  obtain ⟨y', hy'⟩ := exists_finPr_ne M'.vac (fun v => (hM'.vac v).2.1) hM'.std
  have mem : ∀ (f : SInf F (Fin n × Fin d)) g, g ∈ SB (Fin n × Fin d → Af F) → pureA F f g ∈ schA F (Fin n × Fin d) :=
    fun f g h => Submodule.subset_span ⟨f, g, h, rfl⟩
  have hvac : ∀ f : SInf F (Fin n × Fin d), e (pureA F f (finPr M.vac)) = pureA F (ei f) (finPr M'.vac) := fun f => by
    have := hl f M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)
    simp only [fun v => (hv v).1] at this
    exact this
  have hinj : Function.Injective ei := (injective_iff_map_eq_zero ei).2 fun f hf => by
    have h1 : e (pureA F f (finPr M.vac)) = e 0 := by
      rw [hvac, hf, map_zero]; funext x; simp [pureA]
    have h2 := hbij.injOn (mem f _ hg) (zero_mem _) h1
    refine SchwartzMap.ext fun x => ?_
    have h3 := congrFun h2 (pt x y)
    rw [pureA_pt] at h3
    exact (mul_eq_zero.1 h3).resolve_right hy
  have hsl : ∀ Φ ∈ schA F (Fin n × Fin d), ∃ f, ∀ x, e Φ (pt x y') = ei f x := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | zero => exact ⟨0, fun x => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨f, hf⟩ := ha
      obtain ⟨g, hg⟩ := hb
      exact ⟨f + g, fun x => by simp [hf, hg]⟩
    | smul c a _ ha =>
      obtain ⟨f, hf⟩ := ha
      exact ⟨c • f, fun x => by simp [hf]⟩
    | mem Φ hΦ =>
      obtain ⟨f, g, hg, rfl⟩ := hΦ
      replace hg := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F _ g hg
      induction hg using Submodule.span_induction with
      | zero => exact ⟨0, fun x => by
          rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨f₁, hf⟩ := ha
        obtain ⟨f₂, hg⟩ := hb
        exact ⟨f₁ + f₂, fun x => by
          rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; simp [hf, hg]⟩
      | smul c a _ ha =>
        obtain ⟨f₁, hf⟩ := ha
        exact ⟨c • f₁, fun x => by
          rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; simp [hf]⟩
      | mem p hp =>
        obtain ⟨φ, hφ, hs, rfl⟩ := hp
        have h1 := hl f φ hφ (by filter_upwards [hs, hM.std] with v h1 h2 using h1.trans h2.symm)
        refine ⟨finPr (fun v => ev v (φ v)) y' • f, fun x => ?_⟩
        rw [pure_eq, pure_eq] at h1
        refine (congrFun h1 _).trans ?_
        rw [pureA_pt]
        simp [mul_comm]
  have hsurj : Function.Surjective ei := fun g => by
    obtain ⟨Φ, hΦ, h1⟩ := hbij.surjOn (mem g _ hg')
    obtain ⟨f, hf⟩ := hsl Φ hΦ
    refine ⟨(finPr M'.vac y')⁻¹ • f, ?_⟩
    refine SchwartzMap.ext fun x => ?_
    have h2 := hf x
    rw [h1, pureA_pt] at h2
    rw [map_smul, smul_apply, ← h2, smul_eq_mul]
    field_simp
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M.co hB.std
  obtain ⟨D', hD'⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ _ _ _ B.ψ _ _ M'.co hB.std
  have Heisenberg₂ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = M'.co.rho B.ψ u (e Φ) := by
    intro u Φ hΦ
    have h1 : ∀ m : ℕ, incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := fun m => Matrix.map_one _ (map_zero _) (map_one _)
    have := hE.Heisenberg₂ u Φ hΦ
    rwa [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  refine ⟨e, hE, ei, ev, hsurj, ?_, hv, hl⟩
  refine pol_map M M' B.ψ B.emb (fun u f => D u f) (fun u f => D' u f)
    (fun u hu f => actsD_iff GlobalTheory.T.archActionReadings_compatible M B.ψ u f _ (hD u hu f).1) (fun u hu f => actsD_iff GlobalTheory.T.archActionReadings_compatible M' B.ψ u f _ (hD' u hu f).1)
    _ ⟨hinj, hsurj⟩ fun u hu f => ?_
  refine SchwartzMap.ext fun x => ?_
  have h1 := (hD u hu f).1 _ hg _ (GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d X W X W M M' 1 1 ∅ e hM hM' hE _ (proj_adm x y'))
  have h2 := (hD' u hu (ei f)).1 _ hg' _ (proj_adm x y')
  simp only [LinearMap.comp_apply, Heisenberg₂ _ _ (mem f _ hg), hvac] at h1
  have h3 := h1.unique h2
  rw [LinearMap.proj_apply, LinearMap.proj_apply, pureA_pt, pureA_pt] at h3
  exact mul_right_cancel₀ hy' h3

end GlobalTheory.ThK.ModelPol

end
