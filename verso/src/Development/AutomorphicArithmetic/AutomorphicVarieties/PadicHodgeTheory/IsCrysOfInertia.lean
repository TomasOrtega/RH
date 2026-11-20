import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.MemIK
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycFacts
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
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
Use `compactSpace_GK K` as an intermediate fact. Set `χ` to `(P.PD K).χ`. Set `ρ' : Representation ℚ_[l] ↥(GK K) V` to `twist (χ ^ (-w)) ρ`. Establish `hρ' : ∀ g x, ρ' g x = ((χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) • ρ g x` using `fun g x => rfl`. Establish `hcont : ∀ x, Continuous fun g => ρ' g x` using `fun x => by`.

Simplify using `only [hρ', Units.val_zpow_eq_zpow_val]`. Conclude with `(hχ.zpow₀ _ fun g => Or.inl (Units.ne_zero _)).smul (hρ x)`. Establish `hI' : ∀ g ∈ IK K, ∀ x, ρ' g x = x` using `fun g hg x => by`. Rewrite using `[hρ', hI g hg, smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_smul]`. Take `⟨n, e, hint⟩` from `exists_int_basis ρ' hcont`.

Take `⟨M, hM⟩` from `exists_matrixHom ρ' e hint`. Take `⟨W, hW, hWg⟩` from `exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype) (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually (eventually_actT_eq AI y m hm hy)) M (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by`. Establish `h` using `(IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hcont (e j))`. Conclude with `h.congr fun g => (hM g i j).symm))`. Use the proof step `(fun g hg => by`.

Establish `h` using `hI' g (Subgroup.subset_closure fun x hx => norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)`. Rewrite using `[← map_one M]`. Use extensionality with `i j`. Apply `PadicInt.ext` to reduce the goal to its premises. Rewrite using `[hM, hM, h, map_one, Module.End.one_apply])`.

Establish `hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (ρ' g (e j)) i)) * (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W` using `fun g => by conv_rhs => rw [← hWg g, map_mul]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[Matrix.of_apply, ← hM]`. Conclude with `(ιA_zlW AI Ti (M g i j)).symm`.

Use extensionality with `i j`. Conclude with `(P.PD_actB K g _).trans (AI.ιA_act g _).symm`. Take `⟨u, hu⟩` from `(P.PD K).t_unit`. Establish `hact : ∀ g, (P.PD K).actB g ((u ^ (-w) : (P.R.B)ˣ) : P.R.B) = algebraMap ℚ_[l] P.R.B ((χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) * ((u ^ (-w) : (P.R.B)ˣ) : P.R.B)` using `fun g => by`. Establish `h1 : Units.map ((P.PD K).actB g : P.R.B →* P.R.B) u = Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (χ g) * u`.

Use `ext`. Express the relevant statement in the definitionally equal form `(P.PD K).actB g u = algebraMap ℚ_[l] P.R.B (χ g : ℚ_[l]ˣ) * u`. Rewrite using `[hu, (P.PD K).t_act, Algebra.smul_def]`. Establish `h2` using `congrArg (fun x : (P.R.B)ˣ => ((x ^ (-w) : (P.R.B)ˣ) : P.R.B)) h1`. Use `beta_reduce at h2`.

Rewrite `h2` using `[mul_zpow, ← map_zpow, ← map_zpow, Units.val_mul]`. Conclude with `h2`. Use `GlobalTheory.T.isCrys_of_split_alt (P.PD K) ρ e (((u ^ (-w) : (P.R.B)ˣ) : P.R.B) • AI.ιA.mapMatrix W) ?_ fun g => ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_smul, ← RingHom.map_det]`. Conclude with `((Units.isUnit _).pow _).mul (hW.map _)`.

Use `conv_rhs => rw [← hB g]`. Use extensionality with `i j`. Simplify using `only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, map_mul, hact, hρ', map_smul, Finsupp.smul_apply, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`.
-/
private theorem isCrys_of_inertia {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI)
    (K : FinExt l) (hχ : Continuous fun g => (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]))
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (hρ : ∀ x, Continuous fun g => ρ g x) (w : ℤ)
    (hI : ∀ g ∈ IK K, ∀ x, ρ g x = (((P.PD K).χ g ^ w : ℚ_[l]ˣ) : ℚ_[l]) • x) : IsCrys (P.PD K) ρ := by
  have := compactSpace_GK K
  let χ := (P.PD K).χ
  let ρ' : Representation ℚ_[l] ↥(GK K) V := twist (χ ^ (-w)) ρ
  have hρ' : ∀ g x, ρ' g x = ((χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) • ρ g x := fun g x => rfl
  have hcont : ∀ x, Continuous fun g => ρ' g x := fun x => by
    simp only [hρ', Units.val_zpow_eq_zpow_val]
    exact (hχ.zpow₀ _ fun g => Or.inl (Units.ne_zero _)).smul (hρ x)
  have hI' : ∀ g ∈ IK K, ∀ x, ρ' g x = x := fun g hg x => by
    rw [hρ', hI g hg, smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_smul]
  obtain ⟨n, e, hint⟩ := exists_int_basis ρ' hcont
  obtain ⟨M, hM⟩ := exists_matrixHom ρ' e hint
  obtain ⟨W, hW, hWg⟩ := exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hcont (e j))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI' g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      apply PadicInt.ext
      rw [hM, hM, h, map_one, Module.End.one_apply])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (ρ' g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  obtain ⟨u, hu⟩ := (P.PD K).t_unit
  have hact : ∀ g, (P.PD K).actB g ((u ^ (-w) : (P.R.B)ˣ) : P.R.B) =
      algebraMap ℚ_[l] P.R.B ((χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) * ((u ^ (-w) : (P.R.B)ˣ) : P.R.B) := fun g => by
    have h1 : Units.map ((P.PD K).actB g : P.R.B →* P.R.B) u =
        Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (χ g) * u := by
      ext
      change (P.PD K).actB g u = algebraMap ℚ_[l] P.R.B (χ g : ℚ_[l]ˣ) * u
      rw [hu, (P.PD K).t_act, Algebra.smul_def]
    have h2 := congrArg (fun x : (P.R.B)ˣ => ((x ^ (-w) : (P.R.B)ˣ) : P.R.B)) h1
    beta_reduce at h2
    rw [mul_zpow, ← map_zpow, ← map_zpow, Units.val_mul] at h2
    exact h2
  refine GlobalTheory.T.isCrys_of_split_alt (P.PD K) ρ e (((u ^ (-w) : (P.R.B)ˣ) : P.R.B) • AI.ιA.mapMatrix W) ?_ fun g => ?_
  · rw [Matrix.det_smul, ← RingHom.map_det]
    exact ((Units.isUnit _).pow _).mul (hW.map _)
  · conv_rhs => rw [← hB g]
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, map_mul, hact,
      hρ', map_smul, Finsupp.smul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Introduce `l _ G _ _ _ φ hφ A _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ w hI`. Take `⟨K, e, -, he, hφe, hr, -⟩` from `openField φ hφ`. Take `⟨T⟩` from `tiedP l`. Take `⟨hc, -, hq⟩` from `cycFacts l l`. Establish `hφ' : ∀ g : ↥(GK K), φ (e.symm g) = g` using `fun g => by`.

Rewrite using `[← hφe]`. Simplify using the standard rewrite rules. Set `ρ' : Representation A ↥(GK K) V` to `ρ.comp e.symm.toMonoidHom`. Establish `hχ : ∀ g : ↥(GK K), ((((PP l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])` using `fun g => by rw [(PP l).PD_χ, hq]`. Establish `h1 : Crys K ρ'`.

Use `isCrys_of_inertia (PP l) (AIP l) T K ?_ _ (fun x => ?_) w fun g hg x => ?_` and prove the remaining obligations. Simplify using `only [hχ]`. Establish `h0 : Continuous fun g : ↥(GK K) => ((cyc l l g : ℤ_[l]ˣ) : ℤ_[l])` using `Units.continuous_val.comp (hc.comp continuous_subtype_val)`. Conclude with `continuous_subtype_val.comp h0`. Conclude with `hρ.comp (he.prodMk continuous_const)`.

Express the relevant statement in the definitionally equal form `ρ (e.symm g) x = _`. Rewrite using `[hI _ (by rw [hφ']; exact (memIK K g).1 hg), hφ']`. Establish `h2 : cycA l l A g = Units.map (algebraMap ℚ_[l] A : ℚ_[l] →* A) (((PP l).PD K).χ g)`. Use `ext`. Express the relevant statement in the definitionally equal form `algebraMap ℤ_[l] A _ = algebraMap ℚ_[l] A _`.

Rewrite using `[hχ, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] A]`. Both sides reduce to the same expression. Rewrite using `[h2, ← map_zpow]`. Conclude with `algebraMap_smul A _ x`. Establish `h2` using `(isCrIff K ρ').1.2 h1`.

Establish `h3 : Dcr φ (resCoef ℚ_[l] ρ) = Dcr (GK K).subtype (resCoef ℚ_[l] ρ')`. Unfold `Dcr`. Use `(e.symm.surjective.iInf_congr _ fun g => ?_).symm` and prove the remaining obligations. Unfold `actC`. Rewrite using `[hφ']`.

Both sides reduce to the same expression. Unfold `IsCr at h2 ⊢`. Rewrite using `[h3, h2, hr, Subgroup.range_subtype]`.
-/
theorem UpperTheory.V.Loc.crUnr :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Algebra ℤ_[l] A] [IsScalarTower ℤ_[l] ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → ∀ w : ℤ, (∀ g, φ g ∈ Iq l → ∀ x, ρ g x = ((cycA l l A (φ g) ^ w : Aˣ) : A) • x) → IsCr φ ρ := by
  intro l _ G _ _ _ φ hφ A _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ w hI
  obtain ⟨K, e, -, he, hφe, hr, -⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  obtain ⟨hc, -, hq⟩ := cycFacts l l
  have hφ' : ∀ g : ↥(GK K), φ (e.symm g) = g := fun g => by
    rw [← hφe]
    simp
  let ρ' : Representation A ↥(GK K) V := ρ.comp e.symm.toMonoidHom
  have hχ : ∀ g : ↥(GK K), ((((PP l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) :=
    fun g => by rw [(PP l).PD_χ, hq]
  have h1 : Crys K ρ' := by
    refine isCrys_of_inertia (PP l) (AIP l) T K ?_ _ (fun x => ?_) w fun g hg x => ?_
    · simp only [hχ]
      have h0 : Continuous fun g : ↥(GK K) => ((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) :=
        Units.continuous_val.comp (hc.comp continuous_subtype_val)
      exact continuous_subtype_val.comp h0
    · exact hρ.comp (he.prodMk continuous_const)
    · change ρ (e.symm g) x = _
      rw [hI _ (by rw [hφ']; exact (memIK K g).1 hg), hφ']
      have h2 : cycA l l A g = Units.map (algebraMap ℚ_[l] A : ℚ_[l] →* A) (((PP l).PD K).χ g) := by
        ext
        change algebraMap ℤ_[l] A _ = algebraMap ℚ_[l] A _
        rw [hχ, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] A]
        rfl
      rw [h2, ← map_zpow]
      exact algebraMap_smul A _ x
  have h2 := (isCrIff K ρ').1.2 h1
  have h3 : Dcr φ (resCoef ℚ_[l] ρ) = Dcr (GK K).subtype (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    refine (e.symm.surjective.iInf_congr _ fun g => ?_).symm
    unfold actC
    rw [hφ']
    rfl
  unfold IsCr at h2 ⊢
  rw [h3, h2, hr, Subgroup.range_subtype]
