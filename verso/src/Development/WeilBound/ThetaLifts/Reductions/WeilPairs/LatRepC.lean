import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepA
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SumFourEqTrace
import Development.WeilBound.ThetaLifts.TowerModels.PlaneCodiff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinTensMemLatO

noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {ψ : AddChar (AF F) ℂ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

namespace LatC

/- English proof (translation)
Use `haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK`. Establish `h1 : ((H.addSubgroupOf K : AddSubgroup K) : Set K) ∈ 𝓝 (0 : K)`. Establish `h2 : (Subtype.val ⁻¹' V : Set K) ∈ 𝓝 (0 : K)` using `continuous_subtype_val.continuousAt.preimage_mem_nhds hV`. Conclude with `Filter.mem_of_superset h2 fun u hu => h u.1 hu u.2`. Use `haveI := AddSubgroup.quotient_finite_of_isOpen (H.addSubgroupOf K) (AddSubgroup.isOpen_of_mem_nhds _ h1)`.

Conclude with `AddSubgroup.index_ne_zero_of_finite`.
-/
theorem relIndex_ne_zero_of_compact {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (H K : AddSubgroup G) (hK : IsCompact (K : Set G)) {V : Set G} (hV : V ∈ 𝓝 (0 : G))
    (h : ∀ u ∈ V, u ∈ K → u ∈ H) : H.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have h1 : ((H.addSubgroupOf K : AddSubgroup K) : Set K) ∈ 𝓝 (0 : K) := by
    have h2 : (Subtype.val ⁻¹' V : Set K) ∈ 𝓝 (0 : K) := continuous_subtype_val.continuousAt.preimage_mem_nhds hV
    exact Filter.mem_of_superset h2 fun u hu => h u.1 hu u.2
  haveI := AddSubgroup.quotient_finite_of_isOpen (H.addSubgroupOf K) (AddSubgroup.isOpen_of_mem_nhds _ h1)
  exact AddSubgroup.index_ne_zero_of_finite

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨α, hα, γ, hγ, rfl⟩`.
-/
theorem ft_mem {α : Af F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf F) {γ : Matrix (Fin nT) (Fin nS) E} (hγ : γ ∈ Λ) :
    algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) γ ∈ latOF F E nS nT Λ :=
  AddSubgroup.subset_closure ⟨α, hα, γ, hγ, rfl⟩

/- English proof (translation)
Simplify using `only [hOF, hRatF, ratWF, Matrix.map_apply, GlobalTheory.HeisLineF.cAF_incAF, map_sum, map_mul]`.
-/
theorem hOF_rat (M N : Matrix (Fin nT) (Fin nS) E) :
    hOF σ JS JT (ratWF (F := F) M) (ratWF (F := F) N) = incAF F E (hRatF σ JS JT M N) := by
  simp only [hOF, hRatF, ratWF, Matrix.map_apply, GlobalTheory.HeisLineF.cAF_incAF, map_sum, map_mul]

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Establish `e : hOF σ JS JT (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F` using `F) M) (algebraMap (AF F) (AEF F E) (pairA F 0 β) • ratWF (F := F) N) = algebraMap (AF F) (AEF F E) (pairA F 0 α) * (algebraMap (AF F) (AEF F E) (pairA F 0 β) * incAF F E (hRatF σ JS JT M N)) := by`. Rewrite using `[hOF_smul_left, ← hOF_rat, ← hOF_smul_right σ JS JT hσ (algebraMap (AF F) (AEF F E) (pairA F 0 β)), GlobalTheory.HeisThetaF.cAF_algebraMap]`. Establish `e2 : incAF F E ξ₀ * (algebraMap (AF F) (AEF F E) (pairA F 0 α) * (algebraMap (AF F) (AEF F E) (pairA F 0 β) * incAF F E (hRatF σ JS JT M N))) = (pairA F 0 α * pairA F 0 β) ⊗ₜ[F] (ξ₀ * hRatF σ JS JT M N)` using `by show ((1 : AF F) ⊗ₜ[F] ξ₀) * ((pairA F 0 α ⊗ₜ[F] (1 : E)) * ((pairA F 0 β ⊗ₜ[F] (1 : E)) * ((1 : AF F) ⊗ₜ[F] hRatF σ JS JT M N))) = _`. Simplify using `only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]`.

Rewrite using `[symplOF, e, e2, GlobalTheory.LatVac.trace_tmul]`. Use `Prod.ext ?_ rfl` and prove the remaining obligations. Use `show (0 : Ainf F) * 0 * _ = 0`. Rewrite using `[zero_mul, zero_mul]`.
-/
theorem sympl_ft (hσ : ∀ x, σ (σ x) = x) (α β : Af F) (M N : Matrix (Fin nT) (Fin nS) E) :
    symplOF σ JS JT ξ₀ (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M)
      (algebraMap (AF F) (AEF F E) (pairA F 0 β) • ratWF (F := F) N) =
      pairA F 0 (α * β * algebraMap F (Af F) (Algebra.trace F E (ξ₀ * hRatF σ JS JT M N))) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have e : hOF σ JS JT (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M)
      (algebraMap (AF F) (AEF F E) (pairA F 0 β) • ratWF (F := F) N) =
      algebraMap (AF F) (AEF F E) (pairA F 0 α) * (algebraMap (AF F) (AEF F E) (pairA F 0 β) *
        incAF F E (hRatF σ JS JT M N)) := by
    rw [hOF_smul_left, ← hOF_rat, ← hOF_smul_right σ JS JT hσ (algebraMap (AF F) (AEF F E) (pairA F 0 β)),
      GlobalTheory.HeisThetaF.cAF_algebraMap]
  have e2 : incAF F E ξ₀ * (algebraMap (AF F) (AEF F E) (pairA F 0 α) * (algebraMap (AF F) (AEF F E) (pairA F 0 β) *
        incAF F E (hRatF σ JS JT M N))) = (pairA F 0 α * pairA F 0 β) ⊗ₜ[F] (ξ₀ * hRatF σ JS JT M N) := by
    show ((1 : AF F) ⊗ₜ[F] ξ₀) * ((pairA F 0 α ⊗ₜ[F] (1 : E)) * ((pairA F 0 β ⊗ₜ[F] (1 : E)) *
      ((1 : AF F) ⊗ₜ[F] hRatF σ JS JT M N))) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  rw [symplOF, e, e2, GlobalTheory.LatVac.trace_tmul]
  refine Prod.ext ?_ rfl
  show (0 : Ainf F) * 0 * _ = 0
  rw [zero_mul, zero_mul]

/- English proof (translation)
Simplify using `only [hRatF, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations.
-/
theorem hRatF_smul (c : E) (M N : Matrix (Fin nT) (Fin nS) E) : hRatF σ JS JT (c • M) N = c * hRatF σ JS JT M N := by
  simp only [hRatF, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Rewrite using `[sympl_ft hσ]`. Use `PositivityTheory.ThKG.Tow.Pln.psi_int hψ _ (fun a => ?_) _ (fun v => mul_mem (hα v) (hβ v))` and prove the remaining obligations. Take `⟨n, hn⟩` from `(h _).1 (Λ.smul_mem (algebraMap (𝓞 F) (𝓞 E) a) hM) N hN`. Use `⟨n, ?_⟩` and prove the remaining obligations.

Establish `e : algebraMap (𝓞 F) (𝓞 E) a • M = algebraMap F E (a : F) • M` using `rfl`. Rewrite using `[← hn, e, hRatF_smul, ← smul_eq_mul, ← map_smul, Algebra.trace_trace, Algebra.smul_def, mul_left_comm]`.
-/
theorem psi_ft (hσ : ∀ x, σ (σ x) = x) (hψ : IsStd ψ) (h : RatSD σ JS JT ξ₀ Λ) {α β : Af F} (hα : α ∈ Formalism.MainNotions.StandardLattice.intAf F)
    (hβ : β ∈ Formalism.MainNotions.StandardLattice.intAf F) {M N : Matrix (Fin nT) (Fin nS) E} (hM : M ∈ Λ) (hN : N ∈ Λ) :
    ψ (symplOF σ JS JT ξ₀ (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M)
      (algebraMap (AF F) (AEF F E) (pairA F 0 β) • ratWF (F := F) N)) = 1 := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [sympl_ft hσ]
  refine PositivityTheory.ThKG.Tow.Pln.psi_int hψ _ (fun a => ?_) _ (fun v => mul_mem (hα v) (hβ v))
  obtain ⟨n, hn⟩ := (h _).1 (Λ.smul_mem (algebraMap (𝓞 F) (𝓞 E) a) hM) N hN
  refine ⟨n, ?_⟩
  have e : algebraMap (𝓞 F) (𝓞 E) a • M = algebraMap F E (a : F) • M := rfl
  rw [← hn, e, hRatF_smul, ← smul_eq_mul, ← map_smul, Algebra.trace_trace, Algebra.smul_def, mul_left_comm]

/- English proof (translation)
Establish `z1 : ∀ y, symplOF σ JS JT ξ₀ (0 : WOF F E nS nT) y = 0` using `fun y => by`. Use `GlobalTheory.HeisLineF.symplOF_add_left σ JS JT ξ₀ (0 : WOF F E nS nT) 0 y` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.1 this`. Proceed by induction on `hx using AddSubgroup.closure_induction with`.

Consider the case `mem x hx`. Take `⟨α, hα, M, hM, rfl⟩` from `hx`. Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨β, hβ, N, hN, rfl⟩` from `hy`.

Conclude with `psi_ft hσ hψ h hα hβ hM hN`. Consider the case `zero => rw [GlobalTheory.HeisLineF.symplOF_zero_right, AddChar.map_zero_eq_one]`. Consider the case `add u v _ _ hu hv => rw [GlobalTheory.HeisLineF.symplOF_add_right, AddChar.map_add_eq_mul, hu, hv, one_mul]`. Consider the case `neg u _ hu`. Use `GlobalTheory.HeisLineF.symplOF_add_right σ JS JT ξ₀ (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M) u (-u)` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel, GlobalTheory.HeisLineF.symplOF_zero_right]`. Establish `h2` using `congrArg ψ this`. Rewrite `h2` using `[AddChar.map_zero_eq_one, AddChar.map_add_eq_mul, hu, one_mul]`. Conclude with `h2.symm`. Consider the case `zero => rw [z1, AddChar.map_zero_eq_one]`.

Consider the case `add u v _ _ hu hv => rw [GlobalTheory.HeisLineF.symplOF_add_left, AddChar.map_add_eq_mul, hu, hv, one_mul]`. Consider the case `neg u _ hu`. Use `GlobalTheory.HeisLineF.symplOF_add_left σ JS JT ξ₀ u (-u) y` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, z1]`. Establish `h2` using `congrArg ψ this`.

Rewrite `h2` using `[AddChar.map_zero_eq_one, AddChar.map_add_eq_mul, hu, one_mul]`. Conclude with `h2.symm`.
-/
theorem psi_lat (hσ : ∀ x, σ (σ x) = x) (hψ : IsStd ψ) (h : RatSD σ JS JT ξ₀ Λ) {x y : WOF F E nS nT}
    (hx : x ∈ latOF F E nS nT Λ) (hy : y ∈ latOF F E nS nT Λ) : ψ (symplOF σ JS JT ξ₀ x y) = 1 := by
  have z1 : ∀ y, symplOF σ JS JT ξ₀ (0 : WOF F E nS nT) y = 0 := fun y => by
    have := GlobalTheory.HeisLineF.symplOF_add_left σ JS JT ξ₀ (0 : WOF F E nS nT) 0 y
    rw [add_zero] at this
    exact left_eq_add.1 this
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, M, hM, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, N, hN, rfl⟩ := hy
      exact psi_ft hσ hψ h hα hβ hM hN
    | zero => rw [GlobalTheory.HeisLineF.symplOF_zero_right, AddChar.map_zero_eq_one]
    | add u v _ _ hu hv => rw [GlobalTheory.HeisLineF.symplOF_add_right, AddChar.map_add_eq_mul, hu, hv, one_mul]
    | neg u _ hu =>
      have := GlobalTheory.HeisLineF.symplOF_add_right σ JS JT ξ₀
        (algebraMap (AF F) (AEF F E) (pairA F 0 α) • ratWF (F := F) M) u (-u)
      rw [add_neg_cancel, GlobalTheory.HeisLineF.symplOF_zero_right] at this
      have h2 := congrArg ψ this
      rw [AddChar.map_zero_eq_one, AddChar.map_add_eq_mul, hu, one_mul] at h2
      exact h2.symm
  | zero => rw [z1, AddChar.map_zero_eq_one]
  | add u v _ _ hu hv => rw [GlobalTheory.HeisLineF.symplOF_add_left, AddChar.map_add_eq_mul, hu, hv, one_mul]
  | neg u _ hu =>
    have := GlobalTheory.HeisLineF.symplOF_add_left σ JS JT ξ₀ u (-u) y
    rw [add_neg_cancel, z1] at this
    have h2 := congrArg ψ this
    rw [AddChar.map_zero_eq_one, AddChar.map_add_eq_mul, hu, one_mul] at h2
    exact h2.symm

/- English proof (translation)
Introduce `v` and use `by rw [map_one]; exact one_mem _`.
-/
theorem one_int : (1 : Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
  rw [map_one]; exact one_mem _

/- English proof (translation)
Use `haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E`. Introduce `x`. Use `⟨fun hx a ha => psi_lat hσ hψ h hx ha, fun H => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ⟩` from `lat_approx hg (x : WOF F E nS nT) x.fin`. Establish `hΛ : γ ∈ Λ` using `(h γ).2 fun N hN => by`.

Establish `h1` using `ft_mem (F := F) one_int hN`. Establish `h2 : ψ (symplOF σ JS JT ξ₀ (x : WOF F E nS nT) _) = 1` using `H (XFF.mk _ (lat_fin h1)) h1`. Establish `h3` using `psi_lat (JS := JS) (JT := JT) (ξ₀ := ξ₀) hσ hψ h hγ h1`. Rewrite `h2` using `[← sub_add_cancel (x : WOF F E nS nT) (algebraMap (AF F) (AEF F E) (pairA F 0 1) • ratWF (F := F) γ), GlobalTheory.HeisLineF.symplOF_add_left, AddChar.map_add_eq_mul, XFF.coe_mk, h3, one_mul, sympl_ft hσ, one_mul, one_mul, PositivityTheory.ThKG.Tow.Pln.psi_fin_rat hψ, Algebra.tra …`. Take `⟨n, hn⟩` from `h2`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `h4 : ((Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT γ N) : ℚ) : ℂ) = (n : ℂ)`. Apply `mul_left_cancel₀ Complex.two_pi_I_ne_zero` to reduce the goal to its premises. Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h4` after adjusting the coercions. Establish `h5` using `add_mem hγ (ft_mem (F := F) one_int hΛ)`. Rewrite `h5` using `[sub_add_cancel]`. Conclude with `h5`.
-/
theorem lat_sd (hσ : ∀ x, σ (σ x) = x) (hψ : IsStd ψ) (hg : GoodLat Λ) (h : RatSD σ JS JT ξ₀ Λ) :
    SelfDual (gamFF σ JS JT ξ₀ ψ) (latF F E nS nT Λ) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  intro x
  refine ⟨fun hx a ha => psi_lat hσ hψ h hx ha, fun H => ?_⟩
  obtain ⟨γ, hγ⟩ := lat_approx hg (x : WOF F E nS nT) x.fin
  have hΛ : γ ∈ Λ := (h γ).2 fun N hN => by
    have h1 := ft_mem (F := F) one_int hN
    have h2 : ψ (symplOF σ JS JT ξ₀ (x : WOF F E nS nT) _) = 1 := H (XFF.mk _ (lat_fin h1)) h1
    have h3 := psi_lat (JS := JS) (JT := JT) (ξ₀ := ξ₀) hσ hψ h hγ h1
    rw [← sub_add_cancel (x : WOF F E nS nT) (algebraMap (AF F) (AEF F E) (pairA F 0 1) • ratWF (F := F) γ),
      GlobalTheory.HeisLineF.symplOF_add_left, AddChar.map_add_eq_mul, XFF.coe_mk, h3, one_mul, sympl_ft hσ, one_mul, one_mul,
      PositivityTheory.ThKG.Tow.Pln.psi_fin_rat hψ, Algebra.trace_trace, Complex.exp_eq_one_iff] at h2
    obtain ⟨n, hn⟩ := h2
    refine ⟨n, ?_⟩
    have h4 : ((Algebra.trace ℚ E (ξ₀ * hRatF σ JS JT γ N) : ℚ) : ℂ) = (n : ℂ) := by
      apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
      rw [hn]; ring
    exact_mod_cast h4
  have h5 := add_mem hγ (ft_mem (F := F) one_int hΛ)
  rw [sub_add_cancel] at h5
  exact h5

/- English proof (translation)
Assemble the required witnesses or components as `⟨Units.continuous_val.comp continuous_subtype_val, Units.continuous_coe_inv.comp continuous_subtype_val⟩`.
-/
theorem continuous_mtF {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    Continuous (mtF (F := F) σ J) ∧ Continuous fun g : GAF (F := F) σ J => mtF σ J g⁻¹ :=
  ⟨Units.continuous_val.comp continuous_subtype_val, Units.continuous_coe_inv.comp continuous_subtype_val⟩

/- English proof (translation)
Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Conclude with `(((continuous_mtF JT).1.comp (continuous_snd.comp continuous_fst)).matrix_mul continuous_snd).matrix_mul ((continuous_mtF JS).2.comp (continuous_fst.comp continuous_fst))`.
-/
theorem continuous_act : Continuous fun z : (GAF (F := F) σ JS × GAF (F := F) σ JT) × WOF F E nS nT =>
    actOF σ JS JT z.1.1 z.1.2 z.2 := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  exact (((continuous_mtF JT).1.comp (continuous_snd.comp continuous_fst)).matrix_mul continuous_snd).matrix_mul
    ((continuous_mtF JS).2.comp (continuous_fst.comp continuous_fst))

/- English proof (translation)
Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Conclude with `(((continuous_mtF JT).1.comp continuous_snd).matrix_mul continuous_const).matrix_mul ((continuous_mtF JS).2.comp continuous_fst)`.
-/
theorem continuous_act_left (x : WOF F E nS nT) :
    Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  exact (((continuous_mtF JT).1.comp continuous_snd).matrix_mul continuous_const).matrix_mul
    ((continuous_mtF JS).2.comp continuous_fst)

/- English proof (translation)
Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Conclude with `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`.
-/
theorem continuous_act_right (g : GAF (F := F) σ JS) (h : GAF (F := F) σ JT) :
    Continuous fun x : WOF F E nS nT => actOF σ JS JT g h x := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

/- English proof (translation)
Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Establish `e : idx (latF F E nS nT Λ) B = (latOF F E nS nT Λ).relIndex (B.toAddSubgroup.map (XFF.incl F E nS nT))` using `AddSubgroup.relIndex_comap (latOF F E nS nT Λ) (XFF.incl F E nS nT) B.toAddSubgroup`. Take `⟨V, hV, hV'⟩` from `lat_nhds (F := F) hg`. Establish `h3` using `relIndex_ne_zero_of_compact (latOF F E nS nT Λ) ((latOF F E nS nT Λ).map φ) ((lat_compact hg).image hφ) hV (by rintro _ hu ⟨l, hl, rfl⟩; exact hV' _ hu (h1 l hl))`. Rewrite using `[e]`.

Use `fun h0 => h3 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)` and prove the remaining obligations. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Conclude with `h2 b hb`.
-/
theorem idx_ne_zero (hg : GoodLat Λ) (B : Submodule (𝓞 E) (XFF F E nS nT)) (φ : WOF F E nS nT →+ WOF F E nS nT)
    (hφ : Continuous φ) (h1 : ∀ l ∈ latOF F E nS nT Λ, (φ l).map (infPartF F E) = 0)
    (h2 : ∀ b ∈ B, ∃ l ∈ latOF F E nS nT Λ, φ l = b) : idx (latF F E nS nT Λ) B ≠ 0 := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have e : idx (latF F E nS nT Λ) B = (latOF F E nS nT Λ).relIndex (B.toAddSubgroup.map (XFF.incl F E nS nT)) :=
    AddSubgroup.relIndex_comap (latOF F E nS nT Λ) (XFF.incl F E nS nT) B.toAddSubgroup
  obtain ⟨V, hV, hV'⟩ := lat_nhds (F := F) hg
  have h3 := relIndex_ne_zero_of_compact (latOF F E nS nT Λ) ((latOF F E nS nT Λ).map φ)
    ((lat_compact hg).image hφ) hV (by rintro _ hu ⟨l, hl, rfl⟩; exact hV' _ hu (h1 l hl))
  rw [e]
  refine fun h0 => h3 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
  rintro _ ⟨b, hb, rfl⟩
  exact h2 b hb

/- English proof (translation)
Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Establish `h` using `relIndex_ne_zero_of_compact U (latOF F E nS nT Λ) (lat_compact hg) (hU.mem_nhds U.zero_mem) fun u hu _ => hu`. Conclude with `⟨_, Nat.pos_of_ne_zero h, fun u hu => AddSubgroup.nsmul_relIndex_mem U hu⟩`.
-/
theorem lat_lev (hg : GoodLat Λ) (U : AddSubgroup (WOF F E nS nT)) (hU : IsOpen (U : Set (WOF F E nS nT))) :
    ∃ N : ℕ, 0 < N ∧ ∀ u ∈ latOF F E nS nT Λ, N • u ∈ U := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have h := relIndex_ne_zero_of_compact U (latOF F E nS nT Λ) (lat_compact hg) (hU.mem_nhds U.zero_mem)
    fun u hu _ => hu
  exact ⟨_, Nat.pos_of_ne_zero h, fun u hu => AddSubgroup.nsmul_relIndex_mem U hu⟩

/- English proof (translation)
Establish `h : (N : E) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Rewrite using `[← Nat.cast_smul_eq_nsmul (AEF F E), smul_smul, ← map_natCast (incAF F E) N, ← map_mul, mul_inv_cancel₀ h, map_one, one_smul]`.
-/
theorem nsmul_inv_smul {M : Type} [AddCommGroup M] [Module (AEF F E) M] {N : ℕ} (hN : 0 < N) (x : M) :
    N • (incAF F E (N : E)⁻¹ • x) = x := by
  have h : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [← Nat.cast_smul_eq_nsmul (AEF F E), smul_smul, ← map_natCast (incAF F E) N, ← map_mul, mul_inv_cancel₀ h, map_one,
    one_smul]

/- English proof (translation)
The claim follows from `(finSubF F E nS nT).smul_mem a hu`.
-/
theorem fin_smul (a : AEF F E) {u : WOF F E nS nT} (hu : u.map (infPartF F E) = 0) : (a • u).map (infPartF F E) = 0 :=
  (finSubF F E nS nT).smul_mem a hu

/- English proof (translation)
Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Take `⟨V, hV, hV'⟩` from `lat_nhds (F := F) hg`. Establish `h` using `(lat_compact (F := F) hg).eventually_forall_of_forall_eventually (x₀ := (1 : GAF (F := F) σ JS × GAF (F := F) σ JT)) (P := fun p y => actOF σ JS JT p.1 p.2 y - y ∈ V) fun y _ => by`. Establish `h1` using `((continuous_act (σ := σ) (JS := JS) (JT := JT)).sub continuous_snd).continuousAt (x := ((1 : GAF (F := F) σ JS × GAF (F := F) σ JT), y))`. Use `h1.preimage_mem_nhds ?_` and prove the remaining obligations.

Use `show V ∈ 𝓝 (actOF σ JS JT 1 1 y - y)`. Rewrite using `[actOF_one, sub_self]`. Conclude with `hV`. Use `filter_upwards [h] with p hp a ha`. Establish `h2` using `hV' _ (hp a ha) (rhoFF σ JS JT p a - a).fin`.

Establish `h3` using `add_mem h2 (show (a : WOF F E nS nT) ∈ latOF F E nS nT Λ from ha)`. Rewrite `h3` using `[sub_add_cancel]`. Conclude with `h3`.
-/
theorem near (hg : GoodLat Λ) : ∀ᶠ p in 𝓝 (1 : GAF (F := F) σ JS × GAF (F := F) σ JT),
    ∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨V, hV, hV'⟩ := lat_nhds (F := F) hg
  have h := (lat_compact (F := F) hg).eventually_forall_of_forall_eventually
    (x₀ := (1 : GAF (F := F) σ JS × GAF (F := F) σ JT)) (P := fun p y => actOF σ JS JT p.1 p.2 y - y ∈ V) fun y _ => by
      have h1 := ((continuous_act (σ := σ) (JS := JS) (JT := JT)).sub continuous_snd).continuousAt
        (x := ((1 : GAF (F := F) σ JS × GAF (F := F) σ JT), y))
      refine h1.preimage_mem_nhds ?_
      show V ∈ 𝓝 (actOF σ JS JT 1 1 y - y)
      rw [actOF_one, sub_self]
      exact hV
  filter_upwards [h] with p hp a ha
  have h2 := hV' _ (hp a ha) (rhoFF σ JS JT p a - a).fin
  have h3 := add_mem h2 (show (a : WOF F E nS nT) ∈ latOF F E nS nT Λ from ha)
  rw [sub_add_cancel] at h3
  exact h3

/- English proof (translation)
Use `haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)`. Take `⟨V, hV, hV'⟩` from `lat_nhds (F := F) hg`. Establish `h0 : Continuous fun p : GAF (F` using `F) σ JS × GAF (F := F) σ JT => incAF F E (N : E)⁻¹ • (actOF σ JS JT p.1 p.2 x - x) := by`. Establish `h00 : Continuous fun p : GAF (F` using `F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x := continuous_act_left _`. Establish `h01 : Continuous fun p : GAF (F` using `F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x - x := h00.sub continuous_const`.

Conclude with `h01.const_smul (incAF F E (N : E)⁻¹)`. Establish `h1 : (fun p : GAF (F` using `F) σ JS × GAF (F := F) σ JT => incAF F E (N : E)⁻¹ • (actOF σ JS JT p.1 p.2 x - x)) ⁻¹' V ∈ 𝓝 1 := by`. Use `h0.continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Use `show V ∈ 𝓝 (incAF F E (N : E)⁻¹ • (actOF σ JS JT 1 1 x - x))`. Rewrite using `[actOF_one, sub_self, smul_zero]`.

Conclude with `hV`. Use `filter_upwards [h1] with p hp`. Use `⟨incAF F E (N : E)⁻¹ • (rhoFF σ JS JT p x - x), hV' _ hp (XFF.fin _), ?_⟩` and prove the remaining obligations. Rewrite using `[nsmul_inv_smul hN, add_sub_cancel]`.
-/
theorem near' (hg : GoodLat Λ) (x : XFF F E nS nT) (N : ℕ) (hN : 0 < N) :
    ∀ᶠ p in 𝓝 (1 : GAF (F := F) σ JS × GAF (F := F) σ JT), ∃ l ∈ latF F E nS nT Λ, rhoFF σ JS JT p x = x + N • l := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  obtain ⟨V, hV, hV'⟩ := lat_nhds (F := F) hg
  have h0 : Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT =>
      incAF F E (N : E)⁻¹ • (actOF σ JS JT p.1 p.2 x - x) :=
    by
      have h00 : Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x :=
        continuous_act_left _
      have h01 : Continuous fun p : GAF (F := F) σ JS × GAF (F := F) σ JT => actOF σ JS JT p.1 p.2 x - x :=
        h00.sub continuous_const
      exact h01.const_smul (incAF F E (N : E)⁻¹)
  have h1 : (fun p : GAF (F := F) σ JS × GAF (F := F) σ JT =>
      incAF F E (N : E)⁻¹ • (actOF σ JS JT p.1 p.2 x - x)) ⁻¹' V ∈ 𝓝 1 := by
    refine h0.continuousAt.preimage_mem_nhds ?_
    show V ∈ 𝓝 (incAF F E (N : E)⁻¹ • (actOF σ JS JT 1 1 x - x))
    rw [actOF_one, sub_self, smul_zero]
    exact hV
  filter_upwards [h1] with p hp
  refine ⟨incAF F E (N : E)⁻¹ • (rhoFF σ JS JT p x - x), hV' _ hp (XFF.fin _), ?_⟩
  rw [nsmul_inv_smul hN, add_sub_cancel]

end LatC

end PositivityTheory.ThKW

end
