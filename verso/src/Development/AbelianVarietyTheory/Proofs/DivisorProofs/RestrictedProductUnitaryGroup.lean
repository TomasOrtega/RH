import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvIOneSubEInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompMemOfIsStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCommutesMajorant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler

noncomputable section

namespace GlobalTheory.UnitaryRestr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

abbrev toG {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J ≃* GAd σ Jᵀ := (GlobalTheory.IwLine.ofGAd σ J).symm

/- English proof (translation)
The claim follows from `continuous_induced_rng.2 continuous_subtype_val`.
-/
theorem continuous_toG {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Continuous (toG (σ := σ) J) :=
  continuous_induced_rng.2 continuous_subtype_val

/- English proof (translation)
The claim follows from `continuous_induced_rng.2 continuous_subtype_val`.
-/
theorem continuous_ofGAd {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : Continuous (GlobalTheory.IwLine.ofGAd σ J) :=
  continuous_induced_rng.2 continuous_subtype_val

/- English proof (translation)
Distinguish the cases in `h : r = s`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]`.
-/
theorem compFin_one_apply {n : ℕ} (v : Pl F) (r s : Fin n) :
    compFin F E v ((1 : Matrix (Fin n) (Fin n) (AE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) r s := by
  by_cases h : r = s
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

/- English proof (translation)
Distinguish the cases in `h : r = s`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne h]`.
-/
theorem compInf_one_apply {n : ℕ} (w : InfinitePlace F) (r s : Fin n) :
    compInf F E w ((1 : Matrix (Fin n) (Fin n) (AE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) r s := by
  by_cases h : r = s
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

/- English proof (translation)
Rewrite using `[← LemF.QuotInv.IwasawaAt.compFin_mat, ← LemF.QuotInv.IwasawaAt.compFin_mat, GlobalTheory.IwLine.matHom_ofGAd_symm, GlobalTheory.IwLine.matHom_ofGAd_symm]`. Use `show compFin F E v ((ε • mat x + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (AE F E))) r s) = _`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, map_add, compFin_smul, compFin_smul, compFin_one_apply]`.
-/
theorem proj_idemU_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : AF F) (hε : ε * ε = ε) (x : UA σ J) (v : Pl F)
    (r s : Fin n) :
    (matHom (Fv F v) σ Jᵀ (proj σ Jᵀ v (toG J (idemU σ J ε hε x)))).1 r s =
      evFin F v ε • (matHom (Fv F v) σ Jᵀ (proj σ Jᵀ v (toG J x))).1 r s +
        evFin F v (1 - ε) • (1 : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) r s := by
  rw [← LemF.QuotInv.IwasawaAt.compFin_mat, ← LemF.QuotInv.IwasawaAt.compFin_mat, GlobalTheory.IwLine.matHom_ofGAd_symm,
    GlobalTheory.IwLine.matHom_ofGAd_symm]
  show compFin F E v ((ε • mat x + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (AE F E))) r s) = _
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, map_add, compFin_smul, compFin_smul, compFin_one_apply]

/- English proof (translation)
Rewrite using `[← LemF.QuotInv.IwasawaAt.compInf_mat, ← LemF.QuotInv.IwasawaAt.compInf_mat, GlobalTheory.IwLine.matHom_ofGAd_symm, GlobalTheory.IwLine.matHom_ofGAd_symm]`. Use `show compInf F E w ((ε • mat x + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (AE F E))) r s) = _`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, map_add, compInf_smul, compInf_smul, compInf_one_apply]`.
-/
theorem projArch_idemU_apply {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : AF F) (hε : ε * ε = ε) (x : UA σ J)
    (w : InfinitePlace F) (r s : Fin n) :
    (matHom w.Completion σ Jᵀ (projArch σ Jᵀ w (toG J (idemU σ J ε hε x)))).1 r s =
      evInf F w ε • (matHom w.Completion σ Jᵀ (projArch σ Jᵀ w (toG J x))).1 r s +
        evInf F w (1 - ε) • (1 : Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) r s := by
  rw [← LemF.QuotInv.IwasawaAt.compInf_mat, ← LemF.QuotInv.IwasawaAt.compInf_mat, GlobalTheory.IwLine.matHom_ofGAd_symm,
    GlobalTheory.IwLine.matHom_ofGAd_symm]
  show compInf F E w ((ε • mat x + (1 - ε) • (1 : Matrix (Fin n) (Fin n) (AE F E))) r s) = _
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, map_add, compInf_smul, compInf_smul, compInf_one_apply]

/- English proof (translation)
The claim follows from `GlobalTheory.LatVac.evFin_liftV v 1`.
-/
theorem evFin_eFin_self (v : Pl F) : evFin F v (eFin v) = 1 := GlobalTheory.LatVac.evFin_liftV v 1

/- English proof (translation)
The claim follows from `GlobalTheory.AutFunCompare.HA_ext σ Jᵀ fun r s => by rw [← matHom_apply, ← matHom_apply] rw [compAt, proj_idemU_apply, evFin_eFin_self, map_sub, map_one, evFin_eFin_self, sub_self, zero_smul, add_zero, one_smul]`.
-/
theorem proj_compAt_self {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (x : UA σ J) :
    proj σ Jᵀ v (toG J (compAt σ J v x)) = proj σ Jᵀ v (toG J x) :=
  GlobalTheory.AutFunCompare.HA_ext σ Jᵀ fun r s => by
    rw [← matHom_apply, ← matHom_apply]
    rw [compAt, proj_idemU_apply, evFin_eFin_self, map_sub, map_one, evFin_eFin_self, sub_self, zero_smul, add_zero,
      one_smul]

/- English proof (translation)
The claim follows from `GlobalTheory.AutFunCompare.HA_ext σ Jᵀ fun r s => by rw [← matHom_apply, ← matHom_apply] rw [compArch, proj_idemU_apply, map_sub, map_one, SuppOne.evFin_eInf, sub_zero, zero_smul, zero_add, one_smul, map_one, Units.val_one]`.
-/
theorem proj_compArch {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (x : UA σ J) :
    proj σ Jᵀ v (toG J (compArch σ J x)) = 1 :=
  GlobalTheory.AutFunCompare.HA_ext σ Jᵀ fun r s => by
    rw [← matHom_apply, ← matHom_apply]
    rw [compArch, proj_idemU_apply, map_sub, map_one, SuppOne.evFin_eInf, sub_zero, zero_smul, zero_add, one_smul,
      map_one, Units.val_one]

/- English proof (translation)
The claim follows from `GlobalTheory.AutFunCompare.HA_ext σ Jᵀ fun r s => by rw [← matHom_apply, ← matHom_apply] rw [compArch, projArch_idemU_apply, map_sub, map_one, StabComp.evInf_eInf, sub_self, zero_smul, add_zero, one_smul]`.
-/
theorem projArch_compArch {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) (x : UA σ J) :
    projArch σ Jᵀ w (toG J (compArch σ J x)) = projArch σ Jᵀ w (toG J x) :=
  GlobalTheory.AutFunCompare.HA_ext σ Jᵀ fun r s => by
    rw [← matHom_apply, ← matHom_apply]
    rw [compArch, projArch_idemU_apply, map_sub, map_one, StabComp.evInf_eInf, sub_self, zero_smul, add_zero,
      one_smul]

end GlobalTheory.UnitaryRestr

namespace GlobalTheory.UnitaryRestr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `e : GlobalTheory.IwLine.ofGAd σ X.J (toG X.J u) = u` using `MulEquiv.apply_symm_apply _ u`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h' : GlobalTheory.IwLine.ofGAd σ X.J (toG X.J u) ∈ GlobalTheory.StabHaar.stabK (σ` using `σ) B X := by`. Rewrite using `[e]`.

Conclude with `(hK u).1 h`. Conclude with `(GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK F E σ B n X hL _ h').2 v`. Introduce `h`. Take `⟨h1, h2⟩` from `LemF.QuotInv.IwasawaAt.proj_eq_one_of_at hu`. Establish `h'` using `GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B n X hL (toG X.J u) (fun w => by`.

Rewrite using `[h2 w, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `Commute.one_left _) (fun u' => by`. Distinguish the cases in `hu' : u' = v`. Substitute `hu'` using the available equality. Conclude with `h`.

Rewrite using `[h1 u' hu']`. Conclude with `one_mem _)`. Rewrite `h'` using `[e]`. Conclude with `(hK u).2 h'`.
-/
theorem mem_iff_proj_mem_stabLoc {B : Base F E} {n : ℕ} {X : Spc F E n} (hL : X.L.IsLattice E)
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {v : Pl F} {u : UA σ X.J} (hu : u ∈ UAt σ X (evFin F v)) :
    u ∈ K ↔ proj σ X.Jᵀ v (toG X.J u) ∈ stabLoc σ X.Jᵀ X.L v := by
  have e : GlobalTheory.IwLine.ofGAd σ X.J (toG X.J u) = u := MulEquiv.apply_symm_apply _ u
  constructor
  · intro h
    have h' : GlobalTheory.IwLine.ofGAd σ X.J (toG X.J u) ∈ GlobalTheory.StabHaar.stabK (σ := σ) B X := by
      rw [e]; exact (hK u).1 h
    exact (GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK F E σ B n X hL _ h').2 v
  · intro h
    obtain ⟨h1, h2⟩ := LemF.QuotInv.IwasawaAt.proj_eq_one_of_at hu
    have h' := GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B n X hL (toG X.J u) (fun w => by
        rw [h2 w, map_one, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
        exact Commute.one_left _) (fun u' => by
        by_cases hu' : u' = v
        · subst hu'; exact h
        · rw [h1 u' hu']; exact one_mem _)
    rw [e] at h'
    exact (hK u).2 h'

end GlobalTheory.UnitaryRestr

open GlobalTheory.UnitaryRestr in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n r s' X hB hX K hK`. Establish `hL : X.L.IsLattice E` using `hX.lat`. Use `haveI := hL`. Take `⟨hTG, -, -, hT2⟩` from `GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J`. Take `⟨hcf, hca⟩` from `continuous_components F E σ n X.J`.

Establish `hR` using `restrGroup_GAd σ X.Jᵀ X.L`. Establish `hψ` using `continuous_toG (σ := σ) X.J`. Establish `hKc : IsCompact (K : Set (UA σ X.J))`. Establish `e : (K : Set (UA σ X.J)) = (GlobalTheory.StabHaar.stabK (σ` using `σ) B X : Set (UA σ X.J)) := Set.ext fun g => hK g`. Take `⟨C, hC, hsub⟩` from `GlobalTheory.T.relatively_compact_stabilizer F E σ B n X r s' hB hX`.

Rewrite using `[e]`. Conclude with `hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.T.isClosed_adelic_lattice_closure F E n X hL)) hsub`. Establish `hKv : ∀ v : Pl F, ((K.subgroupOf (UAtSub σ X (evFin F v)) : Subgroup _) : Set (UAtSub σ X (evFin F v))) = (fun y : UAtSub σ X (evFin F v) => proj σ X.Jᵀ v (toG X.J y.1)) ⁻¹' (stabLoc σ X.Jᵀ X.L v : Set _)` using `fun v => Set.ext fun y => Subgroup.mem_subgroupOf.trans (mem_iff_proj_mem_stabLoc hL hK (mem_UAtSub.1 y.2))`. Establish `hoK : ∀ v : Pl F, IsOpen ((K.subgroupOf (UAtSub σ X (evFin F v)) : Subgroup _) : Set (UAtSub σ X (evFin F v)))` using `fun v => by`. Rewrite using `[hKv v]`.

Conclude with `(isOpen_stabLoc σ X.Jᵀ X.L v).preimage ((continuous_proj σ X.Jᵀ v).comp (hψ.comp continuous_subtype_val))`. Establish `hlev : ∀ (x : UA σ X.J) (v : Pl F), (compAt σ X.J v).codRestrict (UAtSub σ X (evFin F v)) (compAt_mem v) x ∈ K.subgroupOf (UAtSub σ X (evFin F v)) ↔ proj σ X.Jᵀ v (toG X.J x) ∈ stabLoc σ X.Jᵀ X.L v` using `fun x v => Subgroup.mem_subgroupOf.trans ((mem_iff_proj_mem_stabLoc hL hK (compAt_mem v x)).trans (by`. Rewrite using `[proj_compAt_self]))`. Use `⟨fun _ => hca.subtype_mk _, fun v => (hcf v).subtype_mk _, hoK, fun v => ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hce : Topology.IsClosedEmbedding (Subtype.val : UAtSub σ X (evFin F v) → UA σ X.J)` using `(isClosed_UAtSub (σ := σ) X (evFin F v)).isClosedEmbedding_subtypeVal`.

Conclude with `hce.isCompact_preimage hKc`. Introduce `x y ha hf`. Apply `(toG (σ := σ) X.J).injective` to reduce the goal to its premises. Use `GAd_ext σ X.Jᵀ (fun w => ?_) fun v => ?_` and prove the remaining obligations. Establish `h : compArch σ X.J x = compArch σ X.J y` using `congrArg Subtype.val (ha ())`.

Rewrite using `[← projArch_compArch, h, projArch_compArch]`. Establish `h : compAt σ X.J v x = compAt σ X.J v y` using `congrArg Subtype.val (hf v)`. Rewrite using `[← proj_compAt_self, h, proj_compAt_self]`. Introduce `x`. Conclude with `(eventually_proj_mem_stabLoc σ X.Jᵀ X.L (toG X.J x)).mono fun v h => (hlev x v).2 h`.

Introduce `a y hy`. Take `⟨g, hg1, hg2⟩` from `hR.exists_eq (fun w => projArch σ X.Jᵀ w (toG X.J (a ()).1)) (fun v => proj σ X.Jᵀ v (toG X.J (y v).1)) (hy.mono fun v h => (mem_iff_proj_mem_stabLoc hL hK (mem_UAtSub.1 (y v).2)).1 (Subgroup.mem_subgroupOf.1 h))`. Establish `hgg : toG X.J (GlobalTheory.IwLine.ofGAd σ X.J g) = g` using `MulEquiv.symm_apply_apply _ g`. Use `⟨GlobalTheory.IwLine.ofGAd σ X.J g, fun _ => Subtype.ext ?_, fun v => Subtype.ext ?_⟩` and prove the remaining obligations. Use `show compArch σ X.J (GlobalTheory.IwLine.ofGAd σ X.J g) = (a ()).1`.

Apply `(toG (σ := σ) X.J).injective` to reduce the goal to its premises. Use `GAd_ext σ X.Jᵀ (fun w => ?_) fun v => ?_` and prove the remaining obligations. Rewrite using `[projArch_compArch, hgg, hg1 w]`. Establish `ha : compArch σ X.J (a ()).1 = (a ()).1` using `((SuppOne.comp_of_supp F E σ n X (a ()).1).2 (mem_UAtSub.1 (a ()).2)).1`. Rewrite using `[proj_compArch, ← ha, proj_compArch]`.

Use `show compAt σ X.J v (GlobalTheory.IwLine.ofGAd σ X.J g) = (y v).1`. Apply `(toG (σ := σ) X.J).injective` to reduce the goal to its premises. Establish `hy1` using `LemF.QuotInv.IwasawaAt.proj_eq_one_of_at (mem_UAtSub.1 (y v).2)`. Establish `hx1` using `LemF.QuotInv.IwasawaAt.proj_eq_one_of_at (compAt_mem (X := X) v (GlobalTheory.IwLine.ofGAd σ X.J g))`. Use `GAd_ext σ X.Jᵀ (fun w => ?_) fun u => ?_` and prove the remaining obligations.

Rewrite using `[hx1.2 w, hy1.2 w]`. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality. Rewrite using `[proj_compAt_self, hgg, hg2 u]`. Rewrite using `[hx1.1 u huv, hy1.1 u huv]`.

Establish `e : {x : UA σ X.J | ∀ v, (compAt σ X.J v).codRestrict (UAtSub σ X (evFin F v)) (compAt_mem v) x ∈ K.subgroupOf (UAtSub σ X (evFin F v))} = toG X.J ⁻¹' {g | ∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v}` using `Set.ext fun x => forall_congr' fun v => hlev x v`. Rewrite using `[e]`. Conclude with `hR.isOpen_level.preimage hψ`. Introduce `C hC`. Establish `hD` using `hR.isCompact_level (fun w => (fun z : UAtSub σ X (evI F) => projArch σ X.Jᵀ w (toG X.J z.1)) '' C ()) (fun w => (hC ()).image ((continuous_projArch σ X.Jᵀ w).comp (hψ.comp continuous_subtype_val)))`.

Use `(hD.image (continuous_ofGAd (σ := σ) X.J)).of_isClosed_subset ?_ ?_` and prove the remaining obligations. Establish `e : {x : UA σ X.J | (∀ w : Unit, (compArch σ X.J).codRestrict (UAtSub σ X (evI F)) compArch_mem x ∈ C w) ∧ ∀ v, (compAt σ X.J v).codRestrict (UAtSub σ X (evFin F v)) (compAt_mem v) x ∈ K.subgroupOf (UAtSub σ X (evFin F v))} = ((compArch σ X.J).codRestrict (UAtSub σ X (evI F)) com …`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]`. Conclude with `and_congr_left' ⟨fun h => h (), fun h _ => h⟩`.

Rewrite using `[e]`. Conclude with `((hC ()).isClosed.preimage (hca.subtype_mk _)).inter (isClosed_iInter fun v => (Subgroup.isClosed_of_isOpen _ (hoK v)).preimage ((hcf v).subtype_mk _))`. Introduce and unpack `x ⟨h1, h2⟩`. Use `⟨toG X.J x, ⟨fun w => ⟨_, h1 (), ?_⟩, fun v => (hlev x v).1 (h2 v)⟩, MulEquiv.apply_symm_apply _ x⟩` and prove the remaining obligations. Use `show projArch σ X.Jᵀ w (toG X.J (compArch σ X.J x)) = _`.

Conclude with `projArch_compArch X.J w x`.
-/
theorem GlobalTheory.UnitaryRestr.isRestrGroup_UA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n r s' : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s' → ∀ K : Subgroup (UA σ X.J), IsStab B K →
    GlobalTheory.RestrMeas.IsRestrGroup (X := UA σ X.J) (W := Unit) (V := Pl F)
      (fun _ => (compArch σ X.J).codRestrict (UAtSub σ X (evI F)) compArch_mem)
      (fun v => (compAt σ X.J v).codRestrict (UAtSub σ X (evFin F v)) (compAt_mem v))
      (fun v => K.subgroupOf (UAtSub σ X (evFin F v))) := by
  intro F E _ _ _ _ _ σ B n r s' X hB hX K hK
  have hL : X.L.IsLattice E := hX.lat
  haveI := hL
  obtain ⟨hTG, -, -, hT2⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  obtain ⟨hcf, hca⟩ := continuous_components F E σ n X.J
  have hR := restrGroup_GAd σ X.Jᵀ X.L
  have hψ := continuous_toG (σ := σ) X.J
  have hKc : IsCompact (K : Set (UA σ X.J)) := by
    have e : (K : Set (UA σ X.J)) = (GlobalTheory.StabHaar.stabK (σ := σ) B X : Set (UA σ X.J)) := Set.ext fun g => hK g
    obtain ⟨C, hC, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B n X r s' hB hX
    rw [e]
    exact hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.T.isClosed_adelic_lattice_closure F E n X hL)) hsub
  have hKv : ∀ v : Pl F, ((K.subgroupOf (UAtSub σ X (evFin F v)) : Subgroup _) : Set (UAtSub σ X (evFin F v))) =
      (fun y : UAtSub σ X (evFin F v) => proj σ X.Jᵀ v (toG X.J y.1)) ⁻¹' (stabLoc σ X.Jᵀ X.L v : Set _) :=
    fun v => Set.ext fun y => Subgroup.mem_subgroupOf.trans (mem_iff_proj_mem_stabLoc hL hK (mem_UAtSub.1 y.2))
  have hoK : ∀ v : Pl F, IsOpen ((K.subgroupOf (UAtSub σ X (evFin F v)) : Subgroup _) : Set (UAtSub σ X (evFin F v))) :=
    fun v => by
      rw [hKv v]
      exact (isOpen_stabLoc σ X.Jᵀ X.L v).preimage ((continuous_proj σ X.Jᵀ v).comp (hψ.comp continuous_subtype_val))
  have hlev : ∀ (x : UA σ X.J) (v : Pl F),
      (compAt σ X.J v).codRestrict (UAtSub σ X (evFin F v)) (compAt_mem v) x ∈ K.subgroupOf (UAtSub σ X (evFin F v)) ↔
        proj σ X.Jᵀ v (toG X.J x) ∈ stabLoc σ X.Jᵀ X.L v := fun x v =>
    Subgroup.mem_subgroupOf.trans ((mem_iff_proj_mem_stabLoc hL hK (compAt_mem v x)).trans (by
      rw [proj_compAt_self]))
  refine ⟨fun _ => hca.subtype_mk _, fun v => (hcf v).subtype_mk _, hoK, fun v => ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hce : Topology.IsClosedEmbedding (Subtype.val : UAtSub σ X (evFin F v) → UA σ X.J) :=
      (isClosed_UAtSub (σ := σ) X (evFin F v)).isClosedEmbedding_subtypeVal
    exact hce.isCompact_preimage hKc
  ·
    intro x y ha hf
    apply (toG (σ := σ) X.J).injective
    refine GAd_ext σ X.Jᵀ (fun w => ?_) fun v => ?_
    · have h : compArch σ X.J x = compArch σ X.J y := congrArg Subtype.val (ha ())
      rw [← projArch_compArch, h, projArch_compArch]
    · have h : compAt σ X.J v x = compAt σ X.J v y := congrArg Subtype.val (hf v)
      rw [← proj_compAt_self, h, proj_compAt_self]
  ·
    intro x
    exact (eventually_proj_mem_stabLoc σ X.Jᵀ X.L (toG X.J x)).mono fun v h => (hlev x v).2 h
  ·
    intro a y hy
    obtain ⟨g, hg1, hg2⟩ := hR.exists_eq (fun w => projArch σ X.Jᵀ w (toG X.J (a ()).1))
      (fun v => proj σ X.Jᵀ v (toG X.J (y v).1))
      (hy.mono fun v h => (mem_iff_proj_mem_stabLoc hL hK (mem_UAtSub.1 (y v).2)).1 (Subgroup.mem_subgroupOf.1 h))
    have hgg : toG X.J (GlobalTheory.IwLine.ofGAd σ X.J g) = g := MulEquiv.symm_apply_apply _ g
    refine ⟨GlobalTheory.IwLine.ofGAd σ X.J g, fun _ => Subtype.ext ?_, fun v => Subtype.ext ?_⟩
    · show compArch σ X.J (GlobalTheory.IwLine.ofGAd σ X.J g) = (a ()).1
      apply (toG (σ := σ) X.J).injective
      refine GAd_ext σ X.Jᵀ (fun w => ?_) fun v => ?_
      · rw [projArch_compArch, hgg, hg1 w]
      · have ha : compArch σ X.J (a ()).1 = (a ()).1 :=
          ((SuppOne.comp_of_supp F E σ n X (a ()).1).2 (mem_UAtSub.1 (a ()).2)).1
        rw [proj_compArch, ← ha, proj_compArch]
    · show compAt σ X.J v (GlobalTheory.IwLine.ofGAd σ X.J g) = (y v).1
      apply (toG (σ := σ) X.J).injective
      have hy1 := LemF.QuotInv.IwasawaAt.proj_eq_one_of_at (mem_UAtSub.1 (y v).2)
      have hx1 := LemF.QuotInv.IwasawaAt.proj_eq_one_of_at (compAt_mem (X := X) v (GlobalTheory.IwLine.ofGAd σ X.J g))
      refine GAd_ext σ X.Jᵀ (fun w => ?_) fun u => ?_
      · rw [hx1.2 w, hy1.2 w]
      · by_cases huv : u = v
        · subst huv
          rw [proj_compAt_self, hgg, hg2 u]
        · rw [hx1.1 u huv, hy1.1 u huv]
  ·
    have e : {x : UA σ X.J | ∀ v, (compAt σ X.J v).codRestrict (UAtSub σ X (evFin F v)) (compAt_mem v) x ∈
        K.subgroupOf (UAtSub σ X (evFin F v))} = toG X.J ⁻¹' {g | ∀ v, proj σ X.Jᵀ v g ∈ stabLoc σ X.Jᵀ X.L v} :=
      Set.ext fun x => forall_congr' fun v => hlev x v
    rw [e]
    exact hR.isOpen_level.preimage hψ
  ·
    intro C hC
    have hD := hR.isCompact_level (fun w => (fun z : UAtSub σ X (evI F) => projArch σ X.Jᵀ w (toG X.J z.1)) '' C ())
      (fun w => (hC ()).image ((continuous_projArch σ X.Jᵀ w).comp (hψ.comp continuous_subtype_val)))
    refine (hD.image (continuous_ofGAd (σ := σ) X.J)).of_isClosed_subset ?_ ?_
    · have e : {x : UA σ X.J | (∀ w : Unit, (compArch σ X.J).codRestrict (UAtSub σ X (evI F)) compArch_mem x ∈ C w) ∧
          ∀ v, (compAt σ X.J v).codRestrict (UAtSub σ X (evFin F v)) (compAt_mem v) x ∈
            K.subgroupOf (UAtSub σ X (evFin F v))} =
          ((compArch σ X.J).codRestrict (UAtSub σ X (evI F)) compArch_mem) ⁻¹' C () ∩
            ⋂ v, ((compAt σ X.J v).codRestrict (UAtSub σ X (evFin F v)) (compAt_mem v)) ⁻¹'
              ((K.subgroupOf (UAtSub σ X (evFin F v)) : Subgroup _) : Set (UAtSub σ X (evFin F v))) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, SetLike.mem_coe]
        exact and_congr_left' ⟨fun h => h (), fun h _ => h⟩
      rw [e]
      exact ((hC ()).isClosed.preimage (hca.subtype_mk _)).inter
        (isClosed_iInter fun v => (Subgroup.isClosed_of_isOpen _ (hoK v)).preimage ((hcf v).subtype_mk _))
    · rintro x ⟨h1, h2⟩
      refine ⟨toG X.J x, ⟨fun w => ⟨_, h1 (), ?_⟩, fun v => (hlev x v).1 (h2 v)⟩, MulEquiv.apply_symm_apply _ x⟩
      show projArch σ X.Jᵀ w (toG X.J (compArch σ X.J x)) = _
      exact projArch_compArch X.J w x
