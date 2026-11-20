import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralUnitaryScalarOfNormOneIdeleStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualImageAdelicPointWittCoreStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatGlue

variable {D : D7}

/- English proof (translation)
Apply the tactic sequence `first | rfl | simp [Formalism.L2.Theta.mt, map_mul]`.
-/
theorem mt_mul (S : HSp D) (a b : GA D S) : Formalism.L2.Theta.mt S (a * b) = Formalism.L2.Theta.mt S a * Formalism.L2.Theta.mt S b := by
  first | rfl | simp [Formalism.L2.Theta.mt, map_mul]

/- English proof (translation)
Apply the tactic sequence `first | rfl | simp [Formalism.L2.Theta.mt]`.
-/
theorem mt_one (S : HSp D) : Formalism.L2.Theta.mt S 1 = 1 := by
  first | rfl | simp [Formalism.L2.Theta.mt]

/- English proof (translation)
Unfold `GlobalTheory.FinPl.congGrp`. Rewrite using `[MonoidHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h` as an intermediate fact.

Rewrite using `[← Ideal.Quotient.eq]`. Simplify using `[Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢`. Conclude with `this`. Introduce `h`. Use extensionality with `i j`.

Use `h i j` as an intermediate fact. Rewrite `this` using `[← Ideal.Quotient.eq]`. Simplify using `[Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢`. Conclude with `this`.
-/
theorem mem_congGrp {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ GlobalTheory.FinPl.congGrp V I ↔ ∀ i j, Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold GlobalTheory.FinPl.congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

/- English proof (translation)
Introduce `a ha`. Unfold `idAt at ha`. Unfold `GlobalTheory.FinPl.idOff`. Simplify using `only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢`. Introduce `u`.

Establish `hu : u.1 = v` using `u.2`. Conclude with `ha.2 ⟨u.1, fun e => h (hu.symm.trans e)⟩`.
-/
theorem idAt_le_idOff {v w : GlobalTheory.FinPl.Pl D} (h : v ≠ w) : idAt D (· = w) ≤ GlobalTheory.FinPl.idOff D (· = v) := by
  intro a ha
  unfold idAt at ha
  unfold GlobalTheory.FinPl.idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = v := u.2
  exact ha.2 ⟨u.1, fun e => h (hu.symm.trans e)⟩

/- English proof (translation)
Take `⟨ε, -, -, -, hA, hO⟩` from `(GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1`. Establish `hh'` using `(mem_congGrp).1 hh`. Establish `key : (Formalism.L2.Theta.mt S h - 1) *ᵥ y = 0`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply]`.

Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `h1 : (Formalism.L2.Theta.mt S h - 1) i j * y j ∈ idAt D (· = v)` using `Ideal.mul_mem_left _ _ (hy j)`. Establish `h2 : (Formalism.L2.Theta.mt S h - 1) i j * y j ∈ GlobalTheory.FinPl.idOff D (· = v)` using `Ideal.mul_mem_right _ _ (idAt_le_idOff hvw (by simpa using hh' i j))`. Rewrite using `[← (hA _).1 h1]`. Conclude with `(hO _).1 h2`.

Rewrite `key` using `[Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec]`. Conclude with `key`.
-/
theorem mulVec_fix {S : HSp D} {v w : GlobalTheory.FinPl.Pl D} (hvw : v ≠ w) {h : GA D S} (hh : h ∈ grpAt S (· = w))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) : Formalism.L2.Theta.mt S h *ᵥ y = y := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1
  have hh' := (mem_congGrp).1 hh
  have key : (Formalism.L2.Theta.mt S h - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 : (Formalism.L2.Theta.mt S h - 1) i j * y j ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ (hy j)
    have h2 : (Formalism.L2.Theta.mt S h - 1) i j * y j ∈ GlobalTheory.FinPl.idOff D (· = v) :=
      Ideal.mul_mem_right _ _ (idAt_le_idOff hvw (by simpa using hh' i j))
    rw [← (hA _).1 h1]
    exact (hO _).1 h2
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

/- English proof (translation)
Apply the tactic sequence `first | rw [Matrix.smul_mulVec, Matrix.one_mulVec] | simp [Matrix.smul_mulVec] | (ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])`.
-/
theorem scal_mulVec {n : ℕ} (c : AE D) (y : Fin n → AE D) : (c • (1 : Matrix (Fin n) (Fin n) (AE D))) *ᵥ y = c • y := by
  first | rw [Matrix.smul_mulVec, Matrix.one_mulVec] | simp [Matrix.smul_mulVec] | (ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])

end GlobalTheory.Core.Mi.LatGlue

namespace GlobalTheory.Core.Mi.LatGlue

variable {D : D7}

set_option maxHeartbeats 800000 in

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨1, one_mem _, one_mem _, 1, one_mem _, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ y _ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_one, mt_one, Matrix.one_mulVec]`. Conclude with `⟨rfl, rfl⟩`.

Consider the case `insert w s hws ih`. Take `⟨α, hαG, hαC, ζ, hζC, hin, hout⟩` from `ih`. Establish `hwG : a w ∈ GfC A` using `((GlobalTheory.FinPl.KOpen.mem_grpAt_iff A _ (a w)).1 (ha w).1).1`. Use `⟨a w * α, mul_mem hwG hαG, mul_mem (ha w).2 hαC, z w * ζ, mul_mem (hz w).2 hζC, ?_, ?_⟩` and prove the remaining obligations. Introduce `v hv y hy`.

Break down `Finset.mem_insert.1 hv with rfl | hvs` into its components or cases. Take `⟨h1, h2⟩` from `hout v hws y hy`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mt_mul, ← Matrix.mulVec_mulVec, h1]`. Rewrite using `[mt_mul, ← Matrix.mulVec_mulVec, h2, hzm, scal_mulVec]`.

Establish `hvw : v ≠ w` using `fun h => hws (h ▸ hvs)`. Take `⟨h1, h2⟩` from `hin v hvs y hy`. Establish `ca : a w * α = α * a w` using `((Subgroup.mem_center_iff.1 (ha w).2) α).symm`. Establish `cz : z w * ζ = ζ * z w` using `((Subgroup.mem_center_iff.1 (hz w).2) ζ).symm`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[ca, map_mul, mt_mul, ← Matrix.mulVec_mulVec, mulVec_fix hvw (he w _ (ha w).1) hy, h1]`. Rewrite using `[cz, mt_mul, ← Matrix.mulVec_mulVec, mulVec_fix hvw (hz w).1 hy, h2]`. Introduce `v hv y hy`. Establish `hvw : v ≠ w` using `fun h => hv (h ▸ Finset.mem_insert_self w s)`. Establish `hvs : v ∉ s` using `fun h => hv (Finset.mem_insert_of_mem h)`.

Take `⟨h1, h2⟩` from `hout v hvs y hy`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, mt_mul, ← Matrix.mulVec_mulVec, h1, mulVec_fix hvw (he w _ (ha w).1) hy]`. Rewrite using `[mt_mul, ← Matrix.mulVec_mulVec, h2, mulVec_fix hvw (hz w).1 hy]`.
-/
theorem glue_finset {V A : HSp D} (e : GA D A →* GA D V)
    (he : ∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v))
    (a : GlobalTheory.FinPl.Pl D → GA D A) (c : GlobalTheory.FinPl.Pl D → AE D) (z : GlobalTheory.FinPl.Pl D → GA D V)
    (ha : ∀ v, CenAt A v (a v)) (hz : ∀ v, CenAt V v (z v))
    (hzm : ∀ v, Formalism.L2.Theta.mt V (z v) = c v • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) (s : Finset (GlobalTheory.FinPl.Pl D)) :
    ∃ α ∈ GfC A, α ∈ Subgroup.center (GA D A) ∧ ∃ ζ ∈ Subgroup.center (GA D V),
      (∀ v ∈ s, ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
        Formalism.L2.Theta.mt V (e α) *ᵥ y = Formalism.L2.Theta.mt V (e (a v)) *ᵥ y ∧ Formalism.L2.Theta.mt V ζ *ᵥ y = c v • y) ∧
      (∀ v ∉ s, ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
        Formalism.L2.Theta.mt V (e α) *ᵥ y = y ∧ Formalism.L2.Theta.mt V ζ *ᵥ y = y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, one_mem _, one_mem _, 1, one_mem _, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ y _ => ?_⟩
    rw [map_one, mt_one, Matrix.one_mulVec]
    exact ⟨rfl, rfl⟩
  | insert w s hws ih =>
    obtain ⟨α, hαG, hαC, ζ, hζC, hin, hout⟩ := ih
    have hwG : a w ∈ GfC A := ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff A _ (a w)).1 (ha w).1).1
    refine ⟨a w * α, mul_mem hwG hαG, mul_mem (ha w).2 hαC, z w * ζ, mul_mem (hz w).2 hζC, ?_, ?_⟩
    · intro v hv y hy
      rcases Finset.mem_insert.1 hv with rfl | hvs
      · obtain ⟨h1, h2⟩ := hout v hws y hy
        refine ⟨?_, ?_⟩
        · rw [map_mul, mt_mul, ← Matrix.mulVec_mulVec, h1]
        · rw [mt_mul, ← Matrix.mulVec_mulVec, h2, hzm, scal_mulVec]
      · have hvw : v ≠ w := fun h => hws (h ▸ hvs)
        obtain ⟨h1, h2⟩ := hin v hvs y hy
        have ca : a w * α = α * a w := ((Subgroup.mem_center_iff.1 (ha w).2) α).symm
        have cz : z w * ζ = ζ * z w := ((Subgroup.mem_center_iff.1 (hz w).2) ζ).symm
        refine ⟨?_, ?_⟩
        · rw [ca, map_mul, mt_mul, ← Matrix.mulVec_mulVec, mulVec_fix hvw (he w _ (ha w).1) hy, h1]
        · rw [cz, mt_mul, ← Matrix.mulVec_mulVec, mulVec_fix hvw (hz w).1 hy, h2]
    · intro v hv y hy
      have hvw : v ≠ w := fun h => hv (h ▸ Finset.mem_insert_self w s)
      have hvs : v ∉ s := fun h => hv (Finset.mem_insert_of_mem h)
      obtain ⟨h1, h2⟩ := hout v hvs y hy
      refine ⟨?_, ?_⟩
      · rw [map_mul, mt_mul, ← Matrix.mulVec_mulVec, h1, mulVec_fix hvw (he w _ (ha w).1) hy]
      · rw [mt_mul, ← Matrix.mulVec_mulVec, h2, mulVec_fix hvw (hz w).1 hy]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `D V A e g L M hL hM he hloc`. Use `choose a c ha hc hs using hloc`. Use `choose z hz hzm using fun v => GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D V v (c v) (hc v)`. Take `⟨M', hM'sd, hgM'⟩` from `(GlobalTheory.T.selfDual_image_adelicPoint_wittCore D V L hL).1 g`. Take `⟨T, hT⟩` from `GlobalTheory.FinPl.latV_eq_off_finite D V M' M hM'sd.1 hM.1`.

Establish `hoff : ∀ v ∉ T, Moves V g L M (· = v)` using `fun v hv y hy => by`. Rewrite using `[hgM' _ y hy, hT v hv]`. Take `⟨α, hαG, hαC, ζ, hζC, hin, hout⟩` from `glue_finset e he a c z ha hz hzm T`. Use `⟨α, hαG, hαC, ζ, hζC, ?_⟩` and prove the remaining obligations. Establish `comm : ζ * (g * e α) = g * e α * ζ` using `((Subgroup.mem_center_iff.1 hζC) _).symm`.

Establish `hmt : ∀ y : Fin V.rank → AE D, Formalism.L2.Theta.mt V (ζ * (g * e α)) *ᵥ y = Formalism.L2.Theta.mt V g *ᵥ (Formalism.L2.Theta.mt V (e α) *ᵥ (Formalism.L2.Theta.mt V ζ *ᵥ y))` using `fun y => by`. Rewrite using `[comm, mt_mul, mt_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]`. Establish `loc : ∀ v, Moves V (ζ * (g * e α)) L M (· = v)`. Introduce `v y hy`. Rewrite using `[hmt]`.

Distinguish the cases in `hv : v ∈ T`. Take `⟨h1, h2⟩` from `hin v hv y hy`. Rewrite using `[h2, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mt_mul]`. Conclude with `hs v y hy`. Take `⟨h1, h2⟩` from `hout v hv y hy`.

Rewrite using `[h2, h1]`. Conclude with `hoff v hv y hy`. Introduce `y hy`. Rewrite using `[GlobalTheory.FinPlLoc.part_lat _ V L y hL.1, GlobalTheory.FinPlLoc.part_lat _ V M _ hM.1]`. Establish `hsupp : ∀ i, (Formalism.L2.Theta.mt V (ζ * (g * e α)) *ᵥ y) i ∈ idAt D (fun _ => True)` using `fun i => by`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)`. Use `and_congr (iff_of_true hy hsupp) (forall_congr' fun v => imp_congr_right fun _ => forall_congr' fun x => forall_congr' fun hx => ?_)` and prove the remaining obligations. Establish `hxy : ∀ i, (x • y) i ∈ idAt D (· = v)` using `fun i => by`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`.

Conclude with `Ideal.mul_mem_right _ _ hx.1`. Rewrite using `[← Matrix.mulVec_smul]`. Conclude with `loc v (x • y) hxy`.
-/
theorem glue : ∀ (D : D7) (V A : HSp D) (e : GA D A →* GA D V) (g : GA D V) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → (∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v)) → (∀ v : GlobalTheory.FinPl.Pl D, ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves V c (g * e a) L M v) → ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ z ∈ Subgroup.center (GA D V), Moves V (z * (g * e a)) L M (fun _ => True) := by
  intro D V A e g L M hL hM he hloc
  classical
  choose a c ha hc hs using hloc
  choose z hz hzm using fun v => GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D V v (c v) (hc v)
  obtain ⟨M', hM'sd, hgM'⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D V L hL).1 g
  obtain ⟨T, hT⟩ := GlobalTheory.FinPl.latV_eq_off_finite D V M' M hM'sd.1 hM.1
  have hoff : ∀ v ∉ T, Moves V g L M (· = v) := fun v hv y hy => by
    rw [hgM' _ y hy, hT v hv]
  obtain ⟨α, hαG, hαC, ζ, hζC, hin, hout⟩ := glue_finset e he a c z ha hz hzm T
  refine ⟨α, hαG, hαC, ζ, hζC, ?_⟩
  have comm : ζ * (g * e α) = g * e α * ζ := ((Subgroup.mem_center_iff.1 hζC) _).symm
  have hmt : ∀ y : Fin V.rank → AE D, Formalism.L2.Theta.mt V (ζ * (g * e α)) *ᵥ y =
      Formalism.L2.Theta.mt V g *ᵥ (Formalism.L2.Theta.mt V (e α) *ᵥ (Formalism.L2.Theta.mt V ζ *ᵥ y)) := fun y => by
    rw [comm, mt_mul, mt_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have loc : ∀ v, Moves V (ζ * (g * e α)) L M (· = v) := by
    intro v y hy
    rw [hmt]
    by_cases hv : v ∈ T
    · obtain ⟨h1, h2⟩ := hin v hv y hy
      rw [h2, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mt_mul]
      exact hs v y hy
    · obtain ⟨h1, h2⟩ := hout v hv y hy
      rw [h2, h1]
      exact hoff v hv y hy
  intro y hy
  rw [GlobalTheory.FinPlLoc.part_lat _ V L y hL.1, GlobalTheory.FinPlLoc.part_lat _ V M _ hM.1]
  have hsupp : ∀ i, (Formalism.L2.Theta.mt V (ζ * (g * e α)) *ᵥ y) i ∈ idAt D (fun _ => True) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  refine and_congr (iff_of_true hy hsupp) (forall_congr' fun v => imp_congr_right fun _ =>
    forall_congr' fun x => forall_congr' fun hx => ?_)
  have hxy : ∀ i, (x • y) i ∈ idAt D (· = v) := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hx.1
  rw [← Matrix.mulVec_smul]
  exact loc v (x • y) hxy

end GlobalTheory.Core.Mi.LatGlue

end
