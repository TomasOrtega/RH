import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemIK
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MatrixExtendByZeroApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

/- English proof (translation)
Use `letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])`. Use `haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl`. Set `e₀` to `Module.finBasis ℚ_[l] V`. Set `Λ : Submodule ℤ_[l] V` to `Submodule.span ℤ_[l] (Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (e₀ p.2))`. Establish `hc : Continuous fun g : G => (fun i j => e₀.repr (ρ g (e₀ j)) i)` using `continuous_pi fun i => continuous_pi fun j => (IsModuleTopology.continuous_of_linearMap (e₀.coord i)).comp (hρ _)`.

Take `⟨C, hC⟩` from `(isCompact_range hc).isBounded.exists_norm_le`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc0, hcC⟩ : ∃ c : ℚ_[l], c ≠ 0 ∧ C ≤ ‖c‖ := by`. Take `⟨c, hc⟩` from `NormedField.exists_lt_norm ℚ_[l] (max C 0)`. Conclude with `⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), ((le_max_left _ _).trans hc.le)⟩`. Establish `hle : Λ ≤ Submodule.span ℤ_[l] (Set.range fun i => c • e₀ i)`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨g, j⟩, rfl⟩`. Express the relevant statement in the definitionally equal form `ρ g (e₀ j) ∈ _`. Rewrite using `[← e₀.sum_repr (ρ g (e₀ j))]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Establish `h1 : ‖e₀.repr (ρ g (e₀ j)) i / c‖ ≤ 1`. Rewrite using `[norm_div]`. Use `div_le_one_of_le₀ (le_trans ?_ hcC) (norm_nonneg _)` and prove the remaining obligations. Conclude with `((norm_le_pi_norm _ j).trans (norm_le_pi_norm (fun i j => e₀.repr (ρ g (e₀ j)) i) i)).trans (hC _ ⟨g, rfl⟩)`. Set `z : ℤ_[l]` to `⟨_, h1⟩`.

Establish `h2 : e₀.repr (ρ g (e₀ j)) i • e₀ i = z • c • e₀ i`. Express the relevant statement in the definitionally equal form `_ = (e₀.repr (ρ g (e₀ j)) i / c) • c • e₀ i`. Rewrite using `[smul_smul, div_mul_cancel₀ _ hc0]`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.

Use `haveI : Submodule.IsLattice ℚ_[l] Λ := { fg := (Submodule.fg_span (Set.finite_range _)).of_le hle span_eq_top := by`. Rewrite using `[eq_top_iff, ← e₀.span_eq]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span ⟨(1, i), by simp⟩ }`.

Use `haveI : Module.Free ℤ_[l] Λ := Submodule.IsLattice.free ℚ_[l] Λ`. Use `haveI : Module.Finite ℤ_[l] Λ := Submodule.IsLattice.finite ℚ_[l] Λ`. Set `b` to `Module.finBasis ℤ_[l] Λ`. Establish `hst : ∀ g, ∀ x ∈ Λ, ρ g x ∈ Λ`. Introduce `g x hx`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨⟨h, j⟩, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨(g * h, j), by simp⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `Λ.add_mem hx hy`. Consider the case `smul a x _ hx => rw [LinearMap.map_smul_of_tower]`. Conclude with `Λ.smul_mem a hx`. Use `⟨_, b.extendOfIsLattice ℚ_[l], fun g i j => ?_⟩` and prove the remaining obligations.

Establish `h1 : ρ g (b.extendOfIsLattice ℚ_[l] j) = ∑ k, ((b.repr ⟨_, hst g _ (b j).2⟩ k : ℤ_[l]) : ℚ_[l]) • b.extendOfIsLattice ℚ_[l] k`. Use `congrArg Λ.subtype (b.sum_repr ⟨_, hst g _ (b j).2⟩)` as an intermediate fact. Rewrite `this` using `[map_sum]`. Simplify using `only [Basis.extendOfIsLattice_apply]`. Conclude with `this.symm`.

Rewrite using `[h1, Basis.repr_sum_self]`. Conclude with `PadicInt.norm_le_one _`.
-/
private theorem exists_int_basis {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V) (hρ : ∀ x, Continuous fun g => ρ g x) :
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] V), ∀ g i j, ‖e.repr (ρ g (e j)) i‖ ≤ 1 := by
  classical
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e₀ := Module.finBasis ℚ_[l] V
  let Λ : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (e₀ p.2))
  have hc : Continuous fun g : G => (fun i j => e₀.repr (ρ g (e₀ j)) i) :=
    continuous_pi fun i => continuous_pi fun j =>
      (IsModuleTopology.continuous_of_linearMap (e₀.coord i)).comp (hρ _)
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨c, hc0, hcC⟩ : ∃ c : ℚ_[l], c ≠ 0 ∧ C ≤ ‖c‖ := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
    exact ⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), ((le_max_left _ _).trans hc.le)⟩
  have hle : Λ ≤ Submodule.span ℤ_[l] (Set.range fun i => c • e₀ i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, j⟩, rfl⟩
    change ρ g (e₀ j) ∈ _
    rw [← e₀.sum_repr (ρ g (e₀ j))]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : ‖e₀.repr (ρ g (e₀ j)) i / c‖ ≤ 1 := by
      rw [norm_div]
      refine div_le_one_of_le₀ (le_trans ?_ hcC) (norm_nonneg _)
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm (fun i j => e₀.repr (ρ g (e₀ j)) i) i)).trans
        (hC _ ⟨g, rfl⟩)
    let z : ℤ_[l] := ⟨_, h1⟩
    have h2 : e₀.repr (ρ g (e₀ j)) i • e₀ i = z • c • e₀ i := by
      change _ = (e₀.repr (ρ g (e₀ j)) i / c) • c • e₀ i
      rw [smul_smul, div_mul_cancel₀ _ hc0]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Submodule.IsLattice ℚ_[l] Λ :=
    { fg := (Submodule.fg_span (Set.finite_range _)).of_le hle
      span_eq_top := by
        rw [eq_top_iff, ← e₀.span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨(1, i), by simp⟩ }
  haveI : Module.Free ℤ_[l] Λ := Submodule.IsLattice.free ℚ_[l] Λ
  haveI : Module.Finite ℤ_[l] Λ := Submodule.IsLattice.finite ℚ_[l] Λ
  let b := Module.finBasis ℤ_[l] Λ
  have hst : ∀ g, ∀ x ∈ Λ, ρ g x ∈ Λ := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, j⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * h, j), by simp⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Λ.add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Λ.smul_mem a hx
  refine ⟨_, b.extendOfIsLattice ℚ_[l], fun g i j => ?_⟩
  have h1 : ρ g (b.extendOfIsLattice ℚ_[l] j) =
      ∑ k, ((b.repr ⟨_, hst g _ (b j).2⟩ k : ℤ_[l]) : ℚ_[l]) • b.extendOfIsLattice ℚ_[l] k := by
    have := congrArg Λ.subtype (b.sum_repr ⟨_, hst g _ (b j).2⟩)
    rw [map_sum] at this
    simp only [Basis.extendOfIsLattice_apply]
    exact this.symm
  rw [h1, Basis.repr_sum_self]
  exact PadicInt.norm_le_one _

open GlobalTheory.UnramifiedRep GlobalTheory.UnramifiedCrys GlobalTheory.Cyc in

/- English proof (translation)
Use `compactSpace_GK K` as an intermediate fact. Take `⟨n, e, hint⟩` from `exists_int_basis ρ hcont`. Take `⟨M, hM⟩` from `exists_matrixHom ρ e hint`. Take `⟨W, hW, hWg⟩` from `exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype) (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually (eventually_actT_eq AI y m hm hy)) M (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by`. Establish `h` using `(IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hcont (e j))`.

Conclude with `h.congr fun g => (hM g i j).symm))`. Use the proof step `(fun g hg => by`. Establish `h` using `hI g (Subgroup.subset_closure fun x hx => norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)`. Rewrite using `[← map_one M]`. Use extensionality with `i j`.

Apply `PadicInt.ext` to reduce the goal to its premises. Rewrite using `[hM, hM, h, map_one, Module.End.one_apply])`. Establish `hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (ρ g (e j)) i)) * (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W` using `fun g => by conv_rhs => rw [← hWg g, map_mul]`. Use `congr 1`. Use extensionality with `i j`.

Rewrite using `[Matrix.of_apply, ← hM]`. Conclude with `(ιA_zlW AI Ti (M g i j)).symm`. Use extensionality with `i j`. Conclude with `(P.PD_actB K g _).trans (AI.ιA_act g _).symm`. Set `f : Ainf l →+* P.R.BdR` to `((P.PD K).ι : P.R.B →+* P.R.BdR).comp AI.ιA`.

Establish `hf : ∀ a, f a ∈ (P.PD K).Fil 0` using `fun a => by`. Express the relevant statement in the definitionally equal form `(P.PD K).ι (AI.ιA a) ∈ _`. Rewrite using `[P.PD_ι]`. Conclude with `AI.ainf_image_mem_filtration_zero K a`. Use `⟨n, e, f.mapMatrix W, f.mapMatrix W⁻¹, ?_, fun i j => hf _, fun i j => hf _, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]`. Establish `hι : ∀ c : ℚ_[l], ((P.PD K).ι : P.R.B →+* P.R.BdR) (algebraMap ℚ_[l] P.R.B c) = algebraMap ℚ_[l] P.R.BdR c` using `fun c => (P.PD_ι K _).trans (P.ιB.commutes c)`. Conclude with `map_mul_map_eq ((P.PD K).ι : P.R.B →+* P.R.BdR) (hB g) (fun i j => hι _) ((P.PD K).ι_comm g)`.
-/
private theorem exists_split {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI)
    (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (hcont : ∀ x, Continuous fun g => ρ g x)
    (hI : ∀ g ∈ IK K, ∀ x, ρ g x = x) :
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] V) (W W' : Matrix (Fin n) (Fin n) P.R.BdR), W * W' = 1 ∧
      (∀ i j, W i j ∈ (P.PD K).Fil 0) ∧ (∀ i j, W' i j ∈ (P.PD K).Fil 0) ∧
      ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.BdR (e.repr (ρ g (e j)) i)) * W.map ((P.PD K).actdR g) = W := by
  have := compactSpace_GK K
  obtain ⟨n, e, hint⟩ := exists_int_basis ρ hcont
  obtain ⟨M, hM⟩ := exists_matrixHom ρ e hint
  obtain ⟨W, hW, hWg⟩ := exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hcont (e j))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      apply PadicInt.ext
      rw [hM, hM, h, map_one, Module.End.one_apply])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (ρ g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  let f : Ainf l →+* P.R.BdR := ((P.PD K).ι : P.R.B →+* P.R.BdR).comp AI.ιA
  have hf : ∀ a, f a ∈ (P.PD K).Fil 0 := fun a => by
    change (P.PD K).ι (AI.ιA a) ∈ _
    rw [P.PD_ι]
    exact AI.ainf_image_mem_filtration_zero K a
  refine ⟨n, e, f.mapMatrix W, f.mapMatrix W⁻¹, ?_, fun i j => hf _, fun i j => hf _, fun g => ?_⟩
  · rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
  · have hι : ∀ c : ℚ_[l], ((P.PD K).ι : P.R.B →+* P.R.BdR) (algebraMap ℚ_[l] P.R.B c) =
        algebraMap ℚ_[l] P.R.BdR c := fun c => (P.PD_ι K _).trans (P.ιB.commutes c)
    exact map_mul_map_eq ((P.PD K).ι : P.R.B →+* P.R.BdR) (hB g) (fun i j => hι _)
      ((P.PD K).ι_comm g)

/- English proof (translation)
Take `⟨Θ⟩` from `GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI Ti`. Take `⟨a, ha⟩` from `(P.PD K).Fil_exh b`. Establish `key : ∀ c, min a 0 ≤ c → c ≤ 0 → b ∈ (P.PD K).Fil c`. Introduce `c hc`. Proceed by induction on `c, hc using Int.leInduction with`.

Consider the case `base => exact fun _ => GlobalTheory.SplitJump.fil_mono _ (min_le_left _ _) ha`. Consider the case `succ c hc ih`. Introduce `h0`. Take `⟨κ, -, -, h3, h4⟩` from `GlobalTheory.DRFil.graded_invariants Ti Θ K c b (ih (by omega)) fun g => GlobalTheory.SplitJump.fil_mono _ h0 (hb g)`. Rewrite `h4` using `[h3 (by omega), sub_zero]`. Then use the resulting hypothesis.

Conclude with `key 0 (min_le_right _ _) le_rfl`.
-/
private theorem mem_fil_zero {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI)
    (K : FinExt l) (b : P.R.BdR) (hb : ∀ g, (P.PD K).actdR g b - b ∈ (P.PD K).Fil 0) : b ∈ (P.PD K).Fil 0 := by
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI Ti
  obtain ⟨a, ha⟩ := (P.PD K).Fil_exh b
  have key : ∀ c, min a 0 ≤ c → c ≤ 0 → b ∈ (P.PD K).Fil c := by
    intro c hc
    induction c, hc using Int.leInduction with
    | base => exact fun _ => GlobalTheory.SplitJump.fil_mono _ (min_le_left _ _) ha
    | succ c hc ih =>
      intro h0
      obtain ⟨κ, -, -, h3, h4⟩ := GlobalTheory.DRFil.graded_invariants Ti Θ K c b (ih (by omega))
        fun g => GlobalTheory.SplitJump.fil_mono _ h0 (hb g)
      rwa [h3 (by omega), sub_zero] at h4
  exact key 0 (min_le_right _ _) le_rfl

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Use `(P.PD K).Fil_mul 0 a _ _ (hW i j) (hu j)` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.
-/
private theorem mulVec_mem {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) {n : ℕ}
    (W : Matrix (Fin n) (Fin n) P.R.BdR) (hW : ∀ i j, W i j ∈ (P.PD K).Fil 0) (a : ℤ) (u : Fin n → P.R.BdR)
    (hu : ∀ i, u i ∈ (P.PD K).Fil a) (i : Fin n) : W.mulVec u i ∈ (P.PD K).Fil a := by
  simp only [Matrix.mulVec, dotProduct]
  refine Submodule.sum_mem _ fun j _ => ?_
  have := (P.PD K).Fil_mul 0 a _ _ (hW i j) (hu j)
  rwa [zero_add] at this

open GlobalTheory.SplitJump in
/- English proof (translation)
Take `⟨n, e, W, W', hWW, hW, hW', hg⟩` from `exists_split P AI Ti K ρ hcont hI`. Establish `hW'W : W' * W = 1` using `mul_eq_one_comm.1 hWW`. Prove the components needed by the constructor for the conclusion. Introduce `h set u := W'.mulVec (coord e P.R.BdR y) with hu`. Establish `hc : coord e P.R.BdR y = W.mulVec u`.

Rewrite using `[hu, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]`. Establish `key : ∀ g, (fun i => (P.PD K).actdR g (u i)) - u = W'.mulVec (coord e P.R.BdR (actVdR (P.PD K) ρ g y - y))`. Introduce `g`. Establish `h1` using `coord_act (P.PD K) ρ e g y`. Establish `h2 : (fun i => (P.PD K).actdR g (coord e P.R.BdR y i)) = (W.map ((P.PD K).actdR g)).mulVec fun i => (P.PD K).actdR g (u i)`.

Use function extensionality and compare the values at `i`. Rewrite using `[hc]`. Simplify using `[Matrix.mulVec, dotProduct]`. Rewrite `h1` using `[h2, Matrix.mulVec_mulVec, hg]`. Rewrite using `[map_sub, Matrix.mulVec_sub, h1, Matrix.mulVec_mulVec, hW'W, Matrix.one_mulVec]`.

Rewrite using `[mem_filV _ e, hc]`. Use `mulVec_mem P K W hW 0 u fun i => mem_fil_zero P AI Ti K _ fun g => ?_` and prove the remaining obligations. Use `mulVec_mem P K W' hW' 0 _ ((mem_filV _ e _ _).1 (h g)) i` as an intermediate fact. Rewrite `this` using `[← key]`. Then use the resulting hypothesis. Introduce `h h1`.

Take `⟨k, hk⟩` from `exists_coord (P.PD K) ρ e W W' hWW hg y ((Submodule.mem_iInf _).2 fun g => by`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, h, LinearMap.id_apply, sub_self])`. Establish `hk0 : ∀ i, k i = 0` using `fun i => by`. Use `eq_zero_of_mem_fil_one (P.PD K) _ ?_` and prove the remaining obligations. Rewrite using `[congrFun hk i]`.

Conclude with `mulVec_mem P K W' hW' 1 _ ((mem_filV _ e _ _).1 h1) i`. Establish `hc : coord e P.R.BdR y = W.mulVec fun i => algebraMap K.1 P.R.BdR (k i)`. Rewrite using `[hk, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]`. Apply `(coord e P.R.BdR).injective` to reduce the goal to its premises. Rewrite using `[hc, map_zero]`.

Use function extensionality and compare the values at `i`. Simplify using `[hk0, Matrix.mulVec, dotProduct]`.
-/
private theorem gal_case {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI)
    (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (hcont : ∀ x, Continuous fun g => ρ g x)
    (hI : ∀ g ∈ IK K, ∀ x, ρ g x = x) (y : V ⊗[ℚ_[l]] P.R.BdR) :
    ((∀ g, actVdR (P.PD K) ρ g y - y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0) →
      y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 0) ∧
    ((∀ g, actVdR (P.PD K) ρ g y = y) → y ∈ FilV (P.PD K) (LL := ℚ_[l]) (V := V) 1 → y = 0) := by
  obtain ⟨n, e, W, W', hWW, hW, hW', hg⟩ := exists_split P AI Ti K ρ hcont hI
  have hW'W : W' * W = 1 := mul_eq_one_comm.1 hWW
  constructor
  · intro h
    set u := W'.mulVec (coord e P.R.BdR y) with hu
    have hc : coord e P.R.BdR y = W.mulVec u := by
      rw [hu, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]
    have key : ∀ g, (fun i => (P.PD K).actdR g (u i)) - u =
        W'.mulVec (coord e P.R.BdR (actVdR (P.PD K) ρ g y - y)) := by
      intro g
      have h1 := coord_act (P.PD K) ρ e g y
      have h2 : (fun i => (P.PD K).actdR g (coord e P.R.BdR y i)) =
          (W.map ((P.PD K).actdR g)).mulVec fun i => (P.PD K).actdR g (u i) := by
        funext i
        rw [hc]
        simp [Matrix.mulVec, dotProduct]
      rw [h2, Matrix.mulVec_mulVec, hg] at h1
      rw [map_sub, Matrix.mulVec_sub, h1, Matrix.mulVec_mulVec, hW'W, Matrix.one_mulVec]
    rw [mem_filV _ e, hc]
    refine mulVec_mem P K W hW 0 u fun i => mem_fil_zero P AI Ti K _ fun g => ?_
    have := mulVec_mem P K W' hW' 0 _ ((mem_filV _ e _ _).1 (h g)) i
    rwa [← key] at this
  · intro h h1
    obtain ⟨k, hk⟩ := exists_coord (P.PD K) ρ e W W' hWW hg y ((Submodule.mem_iInf _).2 fun g => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, h, LinearMap.id_apply, sub_self])
    have hk0 : ∀ i, k i = 0 := fun i => by
      refine eq_zero_of_mem_fil_one (P.PD K) _ ?_
      rw [congrFun hk i]
      exact mulVec_mem P K W' hW' 1 _ ((mem_filV _ e _ _).1 h1) i
    have hc : coord e P.R.BdR y = W.mulVec fun i => algebraMap K.1 P.R.BdR (k i) := by
      rw [hk, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]
    apply (coord e P.R.BdR).injective
    rw [hc, map_zero]
    funext i
    simp [hk0, Matrix.mulVec, dotProduct]

/- English proof (translation)
Take `⟨K, e, -, he, hφe, hr, -⟩` from `openField φ hφ`. Take `⟨T⟩` from `tiedP l`. Establish `hφ' : ∀ g : ↥(GK K), φ (e.symm g) = g` using `fun g => by`. Rewrite using `[← hφe]`. Simplify using the standard rewrite rules.

Set `ρ' : Representation ℚ_[l] ↥(GK K) V` to `ρ.comp e.symm.toMonoidHom`. Establish `h1 : ∀ g, actVdR ((PP l).PD K) ρ' g = actD φ ρ (e.symm g)` using `fun g => by`. Unfold `actD actVdR`. Use `congr 1`. Use extensionality with `b`.

Rewrite using `[hφ']`. Conclude with `(PP l).PD_actdR K g b`. Establish `h2 : ∀ a, FilV ((PP l).PD K) (LL` using `ℚ_[l]) (V := V) a = FilT ℚ_[l] V a := fun a => by`. Establish `: (((PP l).PD K).Fil a).restrictScalars ℚ_[l] = (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l]` using `Submodule.ext fun x => GlobalTheory.DRFil.fil_iff K (botExt l) a x`. Unfold `FilV FilT`.

Rewrite using `[this]`. Use `gal_case (PP l) (AIP l) T K ρ' (fun x => hρ.comp (he.prodMk continuous_const)) (fun g hg x => by` as an intermediate fact. Express the relevant statement in the definitionally equal form `ρ (e.symm g) x = x`. Rewrite using `[hI _ (by rw [hφ']; exact (memIK K g).1 hg), Module.End.one_apply]) y`. Simplify using `only [h1, h2] at this`.

Conclude with `⟨fun h => this.1 fun g => h _, fun h => this.2 fun g => h _⟩`.
-/
theorem UpperTheory.V.Loc.unrFil {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V)
    (hρ : ContAction ρ) (hI : ∀ g, φ g ∈ Iq l → ρ g = 1) (y : V ⊗[ℚ_[l]] Bdr l) :
    ((∀ g, actD φ ρ g y - y ∈ FilT ℚ_[l] V 0) → y ∈ FilT ℚ_[l] V 0) ∧
    ((∀ g, actD φ ρ g y = y) → y ∈ FilT ℚ_[l] V 1 → y = 0) := by
  obtain ⟨K, e, -, he, hφe, hr, -⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  have hφ' : ∀ g : ↥(GK K), φ (e.symm g) = g := fun g => by
    rw [← hφe]
    simp
  let ρ' : Representation ℚ_[l] ↥(GK K) V := ρ.comp e.symm.toMonoidHom
  have h1 : ∀ g, actVdR ((PP l).PD K) ρ' g = actD φ ρ (e.symm g) := fun g => by
    unfold actD actVdR
    congr 1
    ext b
    rw [hφ']
    exact (PP l).PD_actdR K g b
  have h2 : ∀ a, FilV ((PP l).PD K) (LL := ℚ_[l]) (V := V) a = FilT ℚ_[l] V a := fun a => by
    have : (((PP l).PD K).Fil a).restrictScalars ℚ_[l] = (((PP l).PD (botExt l)).Fil a).restrictScalars ℚ_[l] :=
      Submodule.ext fun x => GlobalTheory.DRFil.fil_iff K (botExt l) a x
    unfold FilV FilT
    rw [this]
  have := gal_case (PP l) (AIP l) T K ρ' (fun x => hρ.comp (he.prodMk continuous_const))
    (fun g hg x => by
      change ρ (e.symm g) x = x
      rw [hI _ (by rw [hφ']; exact (memIK K g).1 hg), Module.End.one_apply]) y
  simp only [h1, h2] at this
  exact ⟨fun h => this.1 fun g => h _, fun h => this.2 fun g => h _⟩

section Ext

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] (φ : G →* GQ l)

/- English proof (translation)
Establish `hs : Function.Surjective (⊤ : Subgroup G).subtype` using `fun g => ⟨⟨g, trivial⟩, rfl⟩`. Establish `h1 : (φ.comp (⊤ : Subgroup G).subtype).range = φ.range`. Rewrite using `[MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.range_eq_map]`. Establish `h2 : Dcr (φ.comp (⊤ : Subgroup G).subtype) (resCoef ℚ_[l] (ρ.comp (⊤ : Subgroup G).subtype : Representation ℚ_[l] (⊤ : Subgroup G) V)) = Dcr φ (resCoef ℚ_[l] ρ)`. Unfold `Dcr`.

Conclude with `hs.iInf_congr _ fun g => rfl`. Unfold `CrOn IsCr`. Rewrite using `[h1, h2]`.
-/
private theorem crOn_top {V : Type} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] G V) :
    CrOn φ ρ ⊤ ↔ IsCr φ ρ := by
  have hs : Function.Surjective (⊤ : Subgroup G).subtype := fun g => ⟨⟨g, trivial⟩, rfl⟩
  have h1 : (φ.comp (⊤ : Subgroup G).subtype).range = φ.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, ← MonoidHom.range_eq_map]
  have h2 : Dcr (φ.comp (⊤ : Subgroup G).subtype)
      (resCoef ℚ_[l] (ρ.comp (⊤ : Subgroup G).subtype : Representation ℚ_[l] (⊤ : Subgroup G) V)) =
      Dcr φ (resCoef ℚ_[l] ρ) := by
    unfold Dcr
    exact hs.iInf_congr _ fun g => rfl
  unfold CrOn IsCr
  rw [h1, h2]

/- English proof (translation)
Take `⟨x, rfl⟩` from `hy`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => exact ⟨f v ⊗ₜ ⟨s b.1, hs _ b.2⟩, rfl⟩`. Consider the case `add x y hx hy => rw [map_add, map_add]`.

Conclude with `Submodule.add_mem _ hx hy`.
-/
private theorem map_mem_FilT {V V' : Type} [AddCommGroup V] [Module ℚ_[l] V] [AddCommGroup V'] [Module ℚ_[l] V']
    (f : V →ₗ[ℚ_[l]] V') (s : Bdr l →ₗ[ℚ_[l]] Bdr l) (a : ℤ)
    (hs : ∀ b ∈ ((PP l).PD (botExt l)).Fil a, s b ∈ ((PP l).PD (botExt l)).Fil a)
    (y : V ⊗[ℚ_[l]] Bdr l) (hy : y ∈ FilT ℚ_[l] V a) : TensorProduct.map f s y ∈ FilT ℚ_[l] V' a := by
  obtain ⟨x, rfl⟩ := hy
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨f v ⊗ₜ ⟨s b.1, hs _ b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy

/- English proof (translation)
Establish `hg : g ∈ GK (botExt l)`. Express the relevant statement in the definitionally equal form `g ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup`. Rewrite using `[IntermediateField.fixingSubgroup_bot]`. Discharge the goal by the elementary cases of `trivial`. Use `((PP l).PD (botExt l)).Fil_G ⟨g, hg⟩ a b hb` as an intermediate fact.

Rewrite `this` using `[(PP l).PD_actdR]`. Then use the resulting hypothesis.
-/
private theorem act_mem_fil (g : GQ l) (a : ℤ) (b : Bdr l) (hb : b ∈ ((PP l).PD (botExt l)).Fil a) :
    (PP l).actQdR g b ∈ ((PP l).PD (botExt l)).Fil a := by
  have hg : g ∈ GK (botExt l) := by
    change g ∈ (⊥ : IntermediateField ℚ_[l] (Om l)).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    trivial
  have := ((PP l).PD (botExt l)).Fil_G ⟨g, hg⟩ a b hb
  rwa [(PP l).PD_actdR] at this

variable {V : Type} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] G V)

private noncomputable def extRep (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) :
    Representation ℚ_[l] G (V × ℚ_[l]) where
  toFun g := ((ρ g).coprod (LinearMap.toSpanSingleton ℚ_[l] V (c g))).prod (LinearMap.snd ℚ_[l] V ℚ_[l])
  map_one' := by
    have : c 1 = 0 := by simpa using hc 1 1
    refine LinearMap.ext fun p => ?_
    simp [this]
  map_mul' g h := by
    refine LinearMap.ext fun p => ?_
    simp [hc, add_assoc, add_comm, add_left_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem extRep_apply (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G) (p : V × ℚ_[l]) :
    extRep ρ c hc g p = (ρ g p.1 + p.2 • c g, p.2) := rfl

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [UpperTheory.V.Loc.actD, extRep_apply, add_tmul]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`. Normalize the expressions using the abelian group laws.
-/
private theorem fst_act (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G)
    (z : (V × ℚ_[l]) ⊗[ℚ_[l]] Bdr l) :
    TensorProduct.map (LinearMap.fst ℚ_[l] V ℚ_[l]) LinearMap.id (actD φ (extRep ρ c hc) g z) =
      actD φ ρ g (TensorProduct.map (LinearMap.fst ℚ_[l] V ℚ_[l]) LinearMap.id z) +
      TensorProduct.map (LinearMap.toSpanSingleton ℚ_[l] V (c g)) ((PP l).actQdR (φ g)).toLinearMap
        (TensorProduct.map (LinearMap.snd ℚ_[l] V ℚ_[l]) LinearMap.id z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [UpperTheory.V.Loc.actD, extRep_apply, add_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]; abel

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [UpperTheory.V.Loc.actD, extRep_apply]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
private theorem snd_act (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (g : G)
    (z : (V × ℚ_[l]) ⊗[ℚ_[l]] Bdr l) :
    TensorProduct.map (LinearMap.snd ℚ_[l] V ℚ_[l]) LinearMap.id (actD φ (extRep ρ c hc) g z) =
      actD φ (1 : Representation ℚ_[l] G ℚ_[l]) g
        (TensorProduct.map (LinearMap.snd ℚ_[l] V ℚ_[l]) LinearMap.id z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [UpperTheory.V.Loc.actD, extRep_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [← add_tmul]`. Consider the case `add x y hx hy`. Simplify using `only [map_add]`.

Use `conv_lhs => rw [hx, hy]`. Normalize the expressions using the abelian group laws.
-/
private theorem decomp (z : (V × ℚ_[l]) ⊗[ℚ_[l]] Bdr l) :
    z = TensorProduct.map (LinearMap.inl ℚ_[l] V ℚ_[l]) LinearMap.id
        (TensorProduct.map (LinearMap.fst ℚ_[l] V ℚ_[l]) LinearMap.id z) +
      TensorProduct.map (LinearMap.inr ℚ_[l] V ℚ_[l]) LinearMap.id
        (TensorProduct.map (LinearMap.snd ℚ_[l] V ℚ_[l]) LinearMap.id z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [← add_tmul]
  | add x y hx hy =>
    simp only [map_add]
    conv_lhs => rw [hx, hy]
    abel

/- English proof (translation)
Establish `hinv : ∀ z ∈ Ddr φ (extRep ρ c hc), ∀ g, actD φ (extRep ρ c hc) g z = z` using `fun z hz g => by`. Use `(Submodule.mem_iInf _).1 hz g` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]`. Then use the resulting hypothesis. Establish `h1` using `unrFil φ hφ (1 : Representation ℚ_[l] G ℚ_[l]) continuous_snd (fun _ _ => rfl)`. Establish `h2` using `unrFil φ hφ ρ hρ hI`.

Prove the components needed by the constructor for the conclusion. Use `inf_eq_left.2 fun z hz => ?_` and prove the remaining obligations. Establish `hb` using `(h1 (TensorProduct.map (LinearMap.snd ℚ_[l] V ℚ_[l]) LinearMap.id z)).1 fun g => by`. Rewrite using `[← snd_act φ ρ c hc, hinv z hz, sub_self]`. Conclude with `Submodule.zero_mem _`.

Establish `hy` using `(h2 (TensorProduct.map (LinearMap.fst ℚ_[l] V ℚ_[l]) LinearMap.id z)).1 fun g => by`. Establish `h3` using `fst_act φ ρ c hc g z`. Rewrite `h3` using `[hinv z hz]`. Rewrite using `[sub_eq_neg_add, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg, sub_eq_of_eq_add' h3]`. Conclude with `map_mem_FilT _ _ 0 (act_mem_fil _ 0) _ hb`.

Rewrite using `[decomp z]`. Conclude with `Submodule.add_mem _ (map_mem_FilT _ _ 0 (fun _ h => h) _ hy) (map_mem_FilT _ _ 0 (fun _ h => h) _ hb)`. Use `(Submodule.eq_bot_iff _).2 fun z hz => ?_` and prove the remaining obligations. Establish `hb` using `(h1 (TensorProduct.map (LinearMap.snd ℚ_[l] V ℚ_[l]) LinearMap.id z)).2 (fun g => by rw [← snd_act φ ρ c hc, hinv z hz.1]) (map_mem_FilT _ _ 1 (fun _ h => h) _ hz.2)`. Establish `hy` using `(h2 (TensorProduct.map (LinearMap.fst ℚ_[l] V ℚ_[l]) LinearMap.id z)).2 (fun g => by`.

Establish `h3` using `fst_act φ ρ c hc g z`. Rewrite `h3` using `[hinv z hz.1, hb, map_zero, add_zero]`. Conclude with `h3.symm) (map_mem_FilT _ _ 1 (fun _ h => h) _ hz.2)`. Rewrite using `[decomp z, hb, hy, map_zero, map_zero, add_zero]`.
-/
private theorem ext_fil [TopologicalSpace G] [IsTopologicalGroup G] (hφ : IsOpenEmbedding φ)
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    (hρ : ContAction ρ) (hI : ∀ g, φ g ∈ Iq l → ρ g = 1)
    (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) :
    FilD φ (extRep ρ c hc) 0 = Ddr φ (extRep ρ c hc) ∧ FilD φ (extRep ρ c hc) 1 = ⊥ := by
  have hinv : ∀ z ∈ Ddr φ (extRep ρ c hc), ∀ g, actD φ (extRep ρ c hc) g z = z := fun z hz g => by
    have := (Submodule.mem_iInf _).1 hz g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at this
  have h1 := unrFil φ hφ (1 : Representation ℚ_[l] G ℚ_[l]) continuous_snd (fun _ _ => rfl)
  have h2 := unrFil φ hφ ρ hρ hI
  constructor
  · refine inf_eq_left.2 fun z hz => ?_
    have hb := (h1 (TensorProduct.map (LinearMap.snd ℚ_[l] V ℚ_[l]) LinearMap.id z)).1 fun g => by
      rw [← snd_act φ ρ c hc, hinv z hz, sub_self]
      exact Submodule.zero_mem _
    have hy := (h2 (TensorProduct.map (LinearMap.fst ℚ_[l] V ℚ_[l]) LinearMap.id z)).1 fun g => by
      have h3 := fst_act φ ρ c hc g z
      rw [hinv z hz] at h3
      rw [sub_eq_neg_add, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg, sub_eq_of_eq_add' h3]
      exact map_mem_FilT _ _ 0 (act_mem_fil _ 0) _ hb
    rw [decomp z]
    exact Submodule.add_mem _ (map_mem_FilT _ _ 0 (fun _ h => h) _ hy) (map_mem_FilT _ _ 0 (fun _ h => h) _ hb)
  · refine (Submodule.eq_bot_iff _).2 fun z hz => ?_
    have hb := (h1 (TensorProduct.map (LinearMap.snd ℚ_[l] V ℚ_[l]) LinearMap.id z)).2
      (fun g => by rw [← snd_act φ ρ c hc, hinv z hz.1]) (map_mem_FilT _ _ 1 (fun _ h => h) _ hz.2)
    have hy := (h2 (TensorProduct.map (LinearMap.fst ℚ_[l] V ℚ_[l]) LinearMap.id z)).2
      (fun g => by
        have h3 := fst_act φ ρ c hc g z
        rw [hinv z hz.1, hb, map_zero, add_zero] at h3
        exact h3.symm) (map_mem_FilT _ _ 1 (fun _ h => h) _ hz.2)
    rw [decomp z, hb, hy, map_zero, map_zero, add_zero]

/- English proof (translation)
Use `haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V`. Establish `hρ' : ContAction (extRep ρ c hc.2)`. Establish `h1 : Continuous fun p : G × (V × ℚ_[l]) => ρ p.1 p.2.1` using `Continuous.comp (f := fun p : G × (V × ℚ_[l]) => (p.1, p.2.1)) hρ (by fun_prop)`. Establish `h2` using `hc.1`. Conclude with `(h1.add ((continuous_snd.comp continuous_snd).smul (h2.comp continuous_fst))).prodMk (continuous_snd.comp continuous_snd)`.

Establish `ht : twist (1 : G →* ℚ_[l]ˣ)⁻¹ ρ = ρ`. Use extensionality with `g x`. Simplify using `[twist]`. Establish `hch : ∀ g x, chRep (1 : G →* ℚ_[l]ˣ) g x = x` using `fun g x => by simp [chRep]`. Establish `key` using `crExt φ hφ ρ (extRep ρ c hc.2) hρ hρ' 1 (LinearMap.inl ℚ_[l] V ℚ_[l]) (LinearMap.snd ℚ_[l] V ℚ_[l]) (0, 1) c LinearMap.inl_injective Function.Exact.inl_snd rfl (fun g x => by simp [extRep_apply]) (fun g => by simp [extRep_apply]) ⊤ isOpen_univ ((crOn_top φ _).2 (crUnr φ hφ ρ hρ 0 …`.

Unfold `ReciprocityTheory.Gal.ContAction`. Simplify using `only [hch]`. Conclude with `continuous_snd) 0 fun g hg x => by simp [hch]))`. Rewrite `key` using `[ht, crOn_top]`. Rewrite using `[← key]`.

Prove the components needed by the constructor for the conclusion. Introduce `h g hg`. Take `⟨h0, h1⟩` from `ext_fil φ ρ hφ hρ hI c hc.2`. Use `DFunLike.congr_fun (crWt0 φ hφ _ hρ' h h0 h1 g hg) (0, 1)` as an intermediate fact. Simplify `this` using `[extRep_apply]`.

Introduce `h`. Conclude with `crUnr φ hφ _ hρ' 0 fun g hg x => by simp [extRep_apply, hI g hg, h g hg]`.
-/
private theorem rat_case [TopologicalSpace G] [IsTopologicalGroup G] (hφ : IsOpenEmbedding φ)
    [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul ℚ_[l] V] (hρ : ContAction ρ) (hI : ∀ g, φ g ∈ Iq l → ρ g = 1)
    (c : G → V) (hc : c ∈ Z1 ρ) : c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ ↔ ∀ g, φ g ∈ Iq l → c g = 0 := by
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  have hρ' : ContAction (extRep ρ c hc.2) := by
    have h1 : Continuous fun p : G × (V × ℚ_[l]) => ρ p.1 p.2.1 :=
      Continuous.comp (f := fun p : G × (V × ℚ_[l]) => (p.1, p.2.1)) hρ (by fun_prop)
    have h2 := hc.1
    exact (h1.add ((continuous_snd.comp continuous_snd).smul (h2.comp continuous_fst))).prodMk
      (continuous_snd.comp continuous_snd)
  have ht : twist (1 : G →* ℚ_[l]ˣ)⁻¹ ρ = ρ := by
    ext g x
    simp [twist]
  have hch : ∀ g x, chRep (1 : G →* ℚ_[l]ˣ) g x = x := fun g x => by simp [chRep]
  have key := crExt φ hφ ρ (extRep ρ c hc.2) hρ hρ' 1 (LinearMap.inl ℚ_[l] V ℚ_[l]) (LinearMap.snd ℚ_[l] V ℚ_[l])
    (0, 1) c LinearMap.inl_injective Function.Exact.inl_snd rfl (fun g x => by simp [extRep_apply])
    (fun g => by simp [extRep_apply]) ⊤ isOpen_univ
    ((crOn_top φ _).2 (crUnr φ hφ ρ hρ 0 fun g hg x => by simp [hI g hg]))
    ((crOn_top φ _).2 (crUnr φ hφ _ (by
      unfold ReciprocityTheory.Gal.ContAction
      simp only [hch]
      exact continuous_snd) 0 fun g hg x => by simp [hch]))
  rw [ht, crOn_top] at key
  rw [← key]
  constructor
  · intro h g hg
    obtain ⟨h0, h1⟩ := ext_fil φ ρ hφ hρ hI c hc.2
    have := DFunLike.congr_fun (crWt0 φ hφ _ hρ' h h0 h1 g hg) (0, 1)
    simpa [extRep_apply] using this
  · intro h
    exact crUnr φ hφ _ hρ' 0 fun g hg x => by simp [extRep_apply, hI g hg, h g hg]

end Ext

/- English proof (translation)
Introduce `_ l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ hρ hI c hc`. Use `haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V`. Conclude with `rat_case φ (resCoef ℚ_[l] ρ) hφ hρ (fun g hg => LinearMap.ext fun x => DFunLike.congr_fun (hI g hg) x) c hc`.
-/
theorem UpperTheory.V.Loc.z1fUnr :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → (∀ g, φ g ∈ Iq l → ρ g = 1) → ∀ c ∈ Z1 ρ, (c ∈ UpperTheory.V.Loc.finiteCocycles φ ρ ↔ ∀ g, φ g ∈ Iq l → c g = 0) := by
  intro _ l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ ρ hρ hI c hc
  haveI : ContinuousSMul ℚ_[l] V := IsModuleTopology.toContinuousSMul ℚ_[l] V
  exact rat_case φ (resCoef ℚ_[l] ρ) hφ hρ
    (fun g hg => LinearMap.ext fun x => DFunLike.congr_fun (hI g hg) x) c hc
