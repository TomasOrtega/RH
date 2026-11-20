import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
open Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open scoped ComplexConjugate
open Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.LatOpenCpt

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LatOpenCptAny

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X Y r s r' s' hX hY co v`. Take `⟨sX, hsX⟩` from `exists_gen X.L hX.lat`. Take `⟨sY, hsY⟩` from `exists_gen Y.L hY.lat`. Set `ι` to `↥sX × ↥sY`. Set `t : ι → Matrix (Fin n) (Fin d) E` to `fun i => vecMulVec ((i.1 : X.L) : Fin n → E) ((i.2 : Y.L) : Fin d → E)`.

Set `ρ : ι → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)` to `fun i => GlobalTheory.LatVac.locCo co v (incM F (t i))`. Set `φ : (ι → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)` to `{ toFun := fun f => ∑ i, f i • ρ i map_add' := fun f g => by simp [add_smul, Finset.sum_add_distrib] map_smul' := fun c f => by simp [Finset.smul_sum, smul_smul] }`. Establish `hφ : ∀ f, φ f = ∑ i, f i • ρ i` using `fun f => rfl`. Set `Opi : AddSubgroup (ι → Fv F v)` to `AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup`. Establish `hO : ∀ f, f ∈ Opi ↔ ∀ i, f i ∈ v.adicCompletionIntegers F` using `fun f => by`.

Simplify using `only [Opi, AddSubgroup.mem_pi, Set.mem_univ, true_implies]`. Both sides reduce to the same expression. Use `set Λ := (latAtV X Y v).map (GlobalTheory.LatVac.locCo co v) with hΛdef`. Establish `hgen : ∀ x ∈ X.L, ∀ y ∈ Y.L, ∀ a : Fv F v, a ∈ v.adicCompletionIntegers F → a • GlobalTheory.LatVac.locCo co v (incM F (vecMulVec x y)) ∈ Λ`. Introduce `x hx y hy a ha`.

Use `⟨GlobalTheory.LatVac.liftV v a • incM F (vecMulVec x y), AddSubgroup.subset_closure ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, x, hx, y, hy, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[locCo_smul, GlobalTheory.LatVac.evFin_liftV]`. Establish `hle1 : Opi.map φ.toAddMonoidHom ≤ Λ`. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Use `replace hf := (hO _).1 hf`.

Use `show ∑ i, f i • ρ i ∈ Λ`. Conclude with `Λ.sum_mem fun i _ => hgen _ (i.1 : X.L).2 _ (i.2 : Y.L).2 _ (hf i)`. Establish `hsmul : ∀ a ∈ v.adicCompletionIntegers F, ∀ w ∈ Opi.map φ.toAddMonoidHom, a • w ∈ Opi.map φ.toAddMonoidHom`. Introduce and unpack `a ha _ ⟨f, hf, rfl⟩`. Use `replace hf := (hO _).1 hf`.

Conclude with `⟨a • f, (hO _).2 fun i => mul_mem ha (hf i), (φ.map_smul a f)⟩`. Establish `hρ : ∀ x ∈ X.L, ∀ y ∈ Y.L, GlobalTheory.LatVac.locCo co v (incM F (vecMulVec x y)) ∈ Opi.map φ.toAddMonoidHom`. Set `rA : Matrix (Fin n) (Fin d) E →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)` to `(GlobalTheory.LatVac.locCo co v).comp (AddMonoidHom.mapMatrix (inclR (F := F) (AF F)).toAddMonoidHom)`. Use `vecMulVec_mem sX hsX sY hsY ((Opi.map φ.toAddMonoidHom).comap rA) ?_` and prove the remaining obligations. Introduce `x hx y hy`.

Use `⟨Pi.single (⟨x, hx⟩, ⟨y, hy⟩) 1, (hO _).2 fun i => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : i = (⟨x, hx⟩, ⟨y, hy⟩)`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, h]`.

Use `show ∑ i, (Pi.single ((⟨x, hx⟩, ⟨y, hy⟩) : ι) (1 : Fv F v) : ι → Fv F v) i • ρ i = _`. Rewrite using `[Finset.sum_eq_single ((⟨x, hx⟩, ⟨y, hy⟩) : ι) (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]`. Simplify using `only [Pi.single_eq_same, one_smul]`. Both sides reduce to the same expression. Establish `hle2 : Λ ≤ Opi.map φ.toAddMonoidHom`.

Rewrite using `[hΛdef, AddSubgroup.map_le_iff_le_comap, latAtV, AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨a, -, ha, x, hx, y, hy, rfl⟩`. Rewrite using `[SetLike.mem_coe, AddSubgroup.mem_comap, locCo_smul]`. Conclude with `hsmul _ ha _ (hρ x hx y hy)`. Establish `hΛ : Λ = Opi.map φ.toAddMonoidHom` using `le_antisymm hle2 hle1`.

Establish `hsurj : ∀ u, ∃ f, φ f = u`. Introduce `u`. Set `U : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F)` to `(fun k => GlobalTheory.LatVac.liftV v (u.1 k), fun k => GlobalTheory.LatVac.liftV v (u.2 k))`. Establish `ht : ∀ x ∈ X.L, ∀ y ∈ Y.L, incM F (vecMulVec x y) ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i))` using `vecMulVec_mem sX hsX sY hsY ((Submodule.span (AF F) (Set.range fun i => incM F (t i))).toAddSubgroup.comap (AddMonoidHom.mapMatrix (inclR (F := F) (AF F)).toAddMonoidHom)) (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩)`. Establish `hZ` using `span_top hX.lat hY.lat t ht (co.e.symm U)`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hZ`. Use `⟨fun i => GlobalTheory.AdelicU.evFin F v (c i), ?_⟩` and prove the remaining obligations. Rewrite using `[hφ]`. Establish `hu : GlobalTheory.LatVac.locCo co v (co.e.symm U) = u`. Apply the tactic sequence `ext k <;> simp [GlobalTheory.LatVac.locCo, U, GlobalTheory.LatVac.evFin_liftV]`.

Rewrite using `[← hu, ← hc, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => (locCo_smul _ _ _ _).symm`. Establish `hOc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v))` using `PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v`. Establish `hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v))` using `Valued.isOpen_valuationSubring _`. Establish `hφc : Continuous φ`.

Rewrite using `[show (φ : (ι → Fv F v) → _) = fun f => ∑ i, f i • ρ i from rfl]`. Conclude with `continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const`. Establish `hset : ((Opi.map φ.toAddMonoidHom : AddSubgroup _) : Set _) = φ '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))`. Use extensionality with `w`. Simplify using `only [AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, hO, Set.mem_pi, Set.mem_univ, true_implies]`.

Both sides reduce to the same expression. Use `choose f1 hf1 using fun k : Fin n × Fin d => hsurj (Pi.single k 1, 0)`. Use `choose f2 hf2 using fun k : Fin n × Fin d => hsurj (0, Pi.single k 1)`. Set `sec : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ι → Fv F v` to `fun u => ∑ k, u.1 k • f1 k + ∑ k, u.2 k • f2 k`. Establish `hsec : ∀ u, φ (sec u) = u`.

Introduce `u`. Simplify using `only [sec, map_add, map_sum, map_smul, hf1, hf2]`. Apply the tactic sequence `ext k <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]`. Establish `hsc : Continuous sec` using `(continuous_finset_sum _ fun k _ => ((continuous_apply k).comp continuous_fst).smul continuous_const).add (continuous_finset_sum _ fun k _ => ((continuous_apply k).comp continuous_snd).smul continuous_const)`. Prove the components needed by the constructor for the conclusion.

Apply `AddSubgroup.isOpen_of_mem_nhds (g := 0)` to reduce the goal to its premises. Establish `hU : IsOpen (sec ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))` using `(isOpen_set_pi Set.finite_univ fun _ _ => hOo).preimage hsc`. Establish `h0 : (0 : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) ∈ sec ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))`. Introduce `i _`. Simplify using `[sec]`.

Use `Filter.mem_of_superset (hU.mem_nhds h0) ?_` and prove the remaining obligations. Introduce `u hu`. Rewrite using `[SetLike.mem_coe, hΛ]`. Conclude with `⟨sec u, (hO _).2 fun i => hu i (Set.mem_univ _), hsec u⟩`. Rewrite using `[hΛ, hset]`.

Conclude with `(isCompact_univ_pi fun _ => hOc).image hφc`.
-/
theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)) (v : Pl F),
      IsOpen (((latAtV X W v).map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) :
        Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) ∧
      IsCompact (((latAtV X W v).map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) :
        Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hX hY co v
  obtain ⟨sX, hsX⟩ := exists_gen X.L hX.lat
  obtain ⟨sY, hsY⟩ := exists_gen Y.L hY.lat
  let ι := ↥sX × ↥sY
  let t : ι → Matrix (Fin n) (Fin d) E := fun i => vecMulVec ((i.1 : X.L) : Fin n → E) ((i.2 : Y.L) : Fin d → E)
  let ρ : ι → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) := fun i => GlobalTheory.LatVac.locCo co v (incM F (t i))
  let φ : (ι → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun f => ∑ i, f i • ρ i
      map_add' := fun f g => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c f => by simp [Finset.smul_sum, smul_smul] }
  have hφ : ∀ f, φ f = ∑ i, f i • ρ i := fun f => rfl
  let Opi : AddSubgroup (ι → Fv F v) := AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup
  have hO : ∀ f, f ∈ Opi ↔ ∀ i, f i ∈ v.adicCompletionIntegers F := fun f => by
    simp only [Opi, AddSubgroup.mem_pi, Set.mem_univ, true_implies]; rfl
  set Λ := (latAtV X Y v).map (GlobalTheory.LatVac.locCo co v) with hΛdef
  have hgen : ∀ x ∈ X.L, ∀ y ∈ Y.L, ∀ a : Fv F v, a ∈ v.adicCompletionIntegers F →
      a • GlobalTheory.LatVac.locCo co v (incM F (vecMulVec x y)) ∈ Λ := by
    intro x hx y hy a ha
    refine ⟨GlobalTheory.LatVac.liftV v a • incM F (vecMulVec x y), AddSubgroup.subset_closure
      ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, x, hx, y, hy, rfl⟩, ?_⟩
    rw [locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hle1 : Opi.map φ.toAddMonoidHom ≤ Λ := by
    rintro _ ⟨f, hf, rfl⟩
    replace hf := (hO _).1 hf
    show ∑ i, f i • ρ i ∈ Λ
    exact Λ.sum_mem fun i _ => hgen _ (i.1 : X.L).2 _ (i.2 : Y.L).2 _ (hf i)
  have hsmul : ∀ a ∈ v.adicCompletionIntegers F, ∀ w ∈ Opi.map φ.toAddMonoidHom, a • w ∈ Opi.map φ.toAddMonoidHom := by
    rintro a ha _ ⟨f, hf, rfl⟩
    replace hf := (hO _).1 hf
    exact ⟨a • f, (hO _).2 fun i => mul_mem ha (hf i), (φ.map_smul a f)⟩
  have hρ : ∀ x ∈ X.L, ∀ y ∈ Y.L,
      GlobalTheory.LatVac.locCo co v (incM F (vecMulVec x y)) ∈ Opi.map φ.toAddMonoidHom := by
    let rA : Matrix (Fin n) (Fin d) E →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
      (GlobalTheory.LatVac.locCo co v).comp (AddMonoidHom.mapMatrix (inclR (F := F) (AF F)).toAddMonoidHom)
    refine vecMulVec_mem sX hsX sY hsY ((Opi.map φ.toAddMonoidHom).comap rA) ?_
    intro x hx y hy
    refine ⟨Pi.single (⟨x, hx⟩, ⟨y, hy⟩) 1, (hO _).2 fun i => ?_, ?_⟩
    · by_cases h : i = (⟨x, hx⟩, ⟨y, hy⟩)
      · rw [h]; simp
      · simp [Pi.single_apply, h]
    · show ∑ i, (Pi.single ((⟨x, hx⟩, ⟨y, hy⟩) : ι) (1 : Fv F v) : ι → Fv F v) i • ρ i = _
      rw [Finset.sum_eq_single ((⟨x, hx⟩, ⟨y, hy⟩) : ι) (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simp only [Pi.single_eq_same, one_smul]
      rfl
  have hle2 : Λ ≤ Opi.map φ.toAddMonoidHom := by
    rw [hΛdef, AddSubgroup.map_le_iff_le_comap, latAtV, AddSubgroup.closure_le]
    rintro _ ⟨a, -, ha, x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, locCo_smul]
    exact hsmul _ ha _ (hρ x hx y hy)
  have hΛ : Λ = Opi.map φ.toAddMonoidHom := le_antisymm hle2 hle1
  have hsurj : ∀ u, ∃ f, φ f = u := by
    intro u
    let U : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (fun k => GlobalTheory.LatVac.liftV v (u.1 k), fun k => GlobalTheory.LatVac.liftV v (u.2 k))
    have ht : ∀ x ∈ X.L, ∀ y ∈ Y.L, incM F (vecMulVec x y) ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i)) :=
      vecMulVec_mem sX hsX sY hsY ((Submodule.span (AF F) (Set.range fun i => incM F (t i))).toAddSubgroup.comap
        (AddMonoidHom.mapMatrix (inclR (F := F) (AF F)).toAddMonoidHom)) (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩)
    have hZ := span_top hX.lat hY.lat t ht (co.e.symm U)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hZ
    refine ⟨fun i => GlobalTheory.AdelicU.evFin F v (c i), ?_⟩
    rw [hφ]
    have hu : GlobalTheory.LatVac.locCo co v (co.e.symm U) = u := by
      ext k <;> simp [GlobalTheory.LatVac.locCo, U, GlobalTheory.LatVac.evFin_liftV]
    rw [← hu, ← hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => (locCo_smul _ _ _ _).symm
  have hOc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hφc : Continuous φ := by
    rw [show (φ : (ι → Fv F v) → _) = fun f => ∑ i, f i • ρ i from rfl]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hset : ((Opi.map φ.toAddMonoidHom : AddSubgroup _) : Set _) =
      φ '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext w
    simp only [AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, hO, Set.mem_pi, Set.mem_univ, true_implies]
    rfl
  choose f1 hf1 using fun k : Fin n × Fin d => hsurj (Pi.single k 1, 0)
  choose f2 hf2 using fun k : Fin n × Fin d => hsurj (0, Pi.single k 1)
  let sec : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ι → Fv F v :=
    fun u => ∑ k, u.1 k • f1 k + ∑ k, u.2 k • f2 k
  have hsec : ∀ u, φ (sec u) = u := by
    intro u
    simp only [sec, map_add, map_sum, map_smul, hf1, hf2]
    ext k <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hsc : Continuous sec :=
    (continuous_finset_sum _ fun k _ => ((continuous_apply k).comp continuous_fst).smul continuous_const).add
      (continuous_finset_sum _ fun k _ => ((continuous_apply k).comp continuous_snd).smul continuous_const)
  constructor
  · apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hU : IsOpen (sec ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
      (isOpen_set_pi Set.finite_univ fun _ _ => hOo).preimage hsc
    have h0 : (0 : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) ∈
        sec ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
      intro i _; simp [sec]
    refine Filter.mem_of_superset (hU.mem_nhds h0) ?_
    intro u hu
    rw [SetLike.mem_coe, hΛ]
    exact ⟨sec u, (hO _).2 fun i => hu i (Set.mem_univ _), hsec u⟩
  · rw [hΛ, hset]
    exact (isCompact_univ_pi fun _ => hOc).image hφc

end GlobalTheory.LatOpenCptAny
