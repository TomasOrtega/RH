import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

/- English proof (translation)
Unfold `res`. Use `ext`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)ˣ) :
    res h₂ (res h₁ a) = res (h₂.trans h₁) a := by
  unfold res
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Introduce `x hx`. Unfold `LB.pull LB.LinComb LB.wchart`. Simplify using `using hx`.
-/
private lemma U_le_pull_id_U {X : Scheme.{0}} (N : LB X) (i : N.ι) :
    N.U i ≤ (N.pull (𝟙 X)).U (fun _ => i) := by
  intro x hx
  unfold LB.pull LB.LinComb LB.wchart
  simpa using hx

/- English proof (translation)
Unfold `res pullU`. Use `ext`. Simplify using `only [Units.coe_map, MonoidHom.coe_coe]`. Both sides reduce to the same expression.
-/
private lemma res_pullU_id_moduli {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ (𝟙 X) ⁻¹ᵁ U) (h' : V ≤ U)
    (a : Γ(X, U)ˣ) : res h (pullU (𝟙 X) U a) = res h' a := by
  unfold res pullU
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rfl

/- English proof (translation)
Unfold `res`. Use `ext`. Simplify using the standard rewrite rules.
-/
private lemma res_self_moduli {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a := by
  unfold res
  ext
  simp

/- English proof (translation)
Use `⟨⟨fun i => res (U_le_pull_id_U N i) (t.s (fun _ => i))⟩, ?_⟩` and prove the remaining obligations. Introduce `i j`. Establish `key` using `congrArg (res (inf_le_inf (U_le_pull_id_U N i) (U_le_pull_id_U N j))) (ht (fun _ => i) (fun _ => j))`. Rewrite `key` using `[map_mul, res_res_lemma, res_res_lemma]`. Simplify using `only [res_res_lemma]`.

Use `key.trans ?_` and prove the remaining obligations. Use `congr 1`. Establish `hle : (N.pull (𝟙 X)).U (fun _ => i) ⊓ (N.pull (𝟙 X)).U (fun _ => j) ≤ (𝟙 X) ⁻¹ᵁ (N.U i ⊓ N.U j)`. Introduce `x hx`. Take `⟨h1, h2⟩` from `hx`.

Simplify using `only [LB.pull, LB.LinComb, LB.wchart] at h1 h2`. Establish `a : x ∈ N.U i` using `by simpa using h1`. Establish `b : x ∈ N.U j` using `by simpa using h2`. Conclude with `⟨a, b⟩`. Establish `hG : (N.pull (𝟙 X)).g (fun _ => i) (fun _ => j) = res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j))` using `by show ∏ _k : PUnit, (res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j))) ^ (1 : ℤ) = _`.

Rewrite using `[Fintype.prod_unique, zpow_one]`. Rewrite using `[hG, res_res_lemma]`. Conclude with `(res_pullU_id_moduli _ le_rfl _).trans (res_self_moduli _ _)`.
-/
theorem exists_gen_of_pull_id {X : Scheme.{0}} (N : LB X) (t : (N.pull (𝟙 X)).Gen) (ht : t.IsGen) :
    ∃ t : N.Gen, t.IsGen := by
  refine ⟨⟨fun i => res (U_le_pull_id_U N i) (t.s (fun _ => i))⟩, ?_⟩
  intro i j
  have key := congrArg (res (inf_le_inf (U_le_pull_id_U N i) (U_le_pull_id_U N j))) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, res_res_lemma, res_res_lemma] at key
  simp only [res_res_lemma]
  refine key.trans ?_
  congr 1
  have hle : (N.pull (𝟙 X)).U (fun _ => i) ⊓ (N.pull (𝟙 X)).U (fun _ => j) ≤ (𝟙 X) ⁻¹ᵁ (N.U i ⊓ N.U j) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    simp only [LB.pull, LB.LinComb, LB.wchart] at h1 h2
    have a : x ∈ N.U i := by simpa using h1
    have b : x ∈ N.U j := by simpa using h2
    exact ⟨a, b⟩
  have hG : (N.pull (𝟙 X)).g (fun _ => i) (fun _ => j) = res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j)) := by
    show ∏ _k : PUnit, (res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j))) ^ (1 : ℤ) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [hG, res_res_lemma]
  exact (res_pullU_id_moduli _ le_rfl _).trans (res_self_moduli _ _)

/- English proof (translation)
Establish `hπ : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π`. Rewrite using `[← pullback.condition, ← Category.assoc, ← Category.assoc, hg]`. Set `FinalForm : Over S` to `Over.mk (g₁ ≫ pullback.snd A.hom π ≫ π)`. Establish `hw1 : (fst A FinalForm).left ≫ A.hom = (snd A FinalForm).left ≫ (g₁ ≫ pullback.snd A.hom π ≫ π)` using `(Over.w (fst A FinalForm)).trans (Over.w (snd A FinalForm)).symm`. Set `a : (A ⊗ FinalForm).left ⟶ pullback A.hom π` to `pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₁ ≫ pullback.snd A.hom π) (by rw [hw1]; simp)`.

Set `a' : (A ⊗ FinalForm).left ⟶ pullback A.hom π` to `pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₂ ≫ pullback.snd A.hom π) (by rw [hw1, hπ]; simp)`. Set `p0 : (A ⊗ FinalForm).left ⟶ Z` to `(snd A FinalForm).left`. Set `e : Z ⟶ (A ⊗ FinalForm).left` to `(lift (toUnit FinalForm ≫ η[A]) (𝟙 FinalForm)).left`. Establish `he : e ≫ p0 = 𝟙 Z`. Simplify using `only [e, p0]`.

Rewrite using `[← Over.comp_left, lift_snd]`. Both sides reduce to the same expression. Establish `hap : a ≫ pullback.fst A.hom π = a' ≫ pullback.fst A.hom π`. Simplify using `only [a, a']`. Rewrite using `[pullback.lift_fst, pullback.lift_fst]`.

Establish `hU : (toUnit FinalForm).left = g₁ ≫ pullback.snd A.hom π ≫ π` using `(Category.comp_id _).symm.trans (Over.w (toUnit FinalForm))`. Establish `hea : e ≫ a = g₁ ≫ pullback.snd A.hom π ≫ e'`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [a, e, Category.assoc, pullback.lift_fst, he'p]`. Rewrite using `[← Over.comp_left, lift_fst, Over.comp_left, hU]`.

Both sides reduce to the same expression. Simplify using `only [a, e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]`. Rewrite using `[← Category.assoc, ← Over.comp_left, lift_snd]`. Both sides reduce to the same expression. Establish `hea' : e ≫ a' = g₂ ≫ pullback.snd A.hom π ≫ e'`.

Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [a', e, Category.assoc, pullback.lift_fst, he'p]`. Rewrite using `[← Over.comp_left, lift_fst, Over.comp_left, hU, hπ]`. Both sides reduce to the same expression. Simplify using `only [a', e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]`.

Rewrite using `[← Category.assoc, ← Over.comp_left, lift_snd]`. Both sides reduce to the same expression. Set `x : FinalForm ⟶ A` to `Over.homMk (g₁ ≫ pullback.fst A.hom π) (by simp [FinalForm, pullback.condition])`. Set `ρ : Z ⟶ (A ⊗ FinalForm).left` to `(lift x (𝟙 FinalForm)).left`. Establish `hρp : ρ ≫ p0 = 𝟙 Z`.

Simplify using `only [ρ, p0]`. Rewrite using `[← Over.comp_left, lift_snd]`. Both sides reduce to the same expression. Establish `hρa : ρ ≫ a = g₁`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Simplify using `only [a, ρ, Category.assoc, pullback.lift_fst]`. Rewrite using `[← Over.comp_left, lift_fst]`. Both sides reduce to the same expression. Simplify using `only [a, Category.assoc, pullback.lift_snd]`. Rewrite using `[← Category.assoc, hρp, Category.id_comp]`.

Establish `hρa' : ρ ≫ a' = g₂`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [a', ρ, Category.assoc, pullback.lift_fst]`. Rewrite using `[← Over.comp_left, lift_fst, ← hg]`. Both sides reduce to the same expression.

Simplify using `only [a', Category.assoc, pullback.lift_snd]`. Rewrite using `[← Category.assoc, hρp, Category.id_comp]`. Set `u` to `LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a) (LB.pullGen N _ _ w (p0 ≫ e ≫ a'))`. Set `u'` to `LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a') (LB.pullGen N _ _ w (p0 ≫ e ≫ a))`. Establish `hu : u.IsGen` using `ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)`.

Establish `hu' : u'.IsGen` using `ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a') (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)`. Establish `hF : FormEq (Sum.elim (fun _ : PUnit.{1} => a' ≫ pullback.fst A.hom π) (fun _ : PUnit.{1} => (p0 ≫ e ≫ a) ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1)) (Sum.elim (fun _ : PUnit.{1} => a ≫ pullback.fst A.hom π) (fun _ : PUnit.{1} => (p0 ≫ e ≫ a') ≫ pullback.f …`. Introduce `U _ h`. Simplify using `[Fintype.prod_sum_type, hap]`. Establish `key` using `ReciprocityTheory.ChartRestriction.G.Geo.Tor.gen_unique' hN hF p0 e he (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_snd hG hA FinalForm) hu hu' ?_ Z ρ z J hJ`.

Simplify using `only [u, u'] at key`. Rewrite `key` using `[val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ]`. Establish `hρp' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), ρ ≫ p0 ≫ h = h` using `fun h => by`. Rewrite using `[← Category.assoc, hρp, Category.id_comp]`. Rewrite `key` using `[hρp', hρp', hea', hea, hρa, hρa']`.

Conclude with `key`. Introduce `y J' hJ'`. Simplify using `only [u, u']`. Rewrite using `[val_mul hJ', val_mul hJ', val_pull hJ', val_pull hJ', val_pull hJ', val_pull hJ']`. Establish `he' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), e ≫ p0 ≫ h = h` using `fun h => by`.

Rewrite using `[← Category.assoc, he, Category.id_comp]`. Rewrite using `[he', he', mul_comm]`.
-/
private theorem val_mul_val_comm_of_fst_eq (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} (π : S' ⟶ S) (A : Over S) [GrpObj A]
    (N : LB A.left) (hA : IsAbelianScheme A) (hN : N.IsLB)
    (w : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen) (hw : w.IsGen)
    (e' : S' ⟶ pullback A.hom π) (he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A)
    (he'q : e' ≫ pullback.snd A.hom π = 𝟙 S')
    {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ pullback A.hom π)
    (hg : g₁ ≫ pullback.fst A.hom π = g₂ ≫ pullback.fst A.hom π) (z : Z) (J : (Z ⟶ A.left) → N.ι)
    (hJ : Good N z J) :
    val w g₁ z J * val w (g₂ ≫ pullback.snd A.hom π ≫ e') z J =
      val w g₂ z J * val w (g₁ ≫ pullback.snd A.hom π ≫ e') z J := by
  have hπ : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π := by
    rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hg]
  let FinalForm : Over S := Over.mk (g₁ ≫ pullback.snd A.hom π ≫ π)
  have hw1 : (fst A FinalForm).left ≫ A.hom = (snd A FinalForm).left ≫ (g₁ ≫ pullback.snd A.hom π ≫ π) :=
    (Over.w (fst A FinalForm)).trans (Over.w (snd A FinalForm)).symm
  let a : (A ⊗ FinalForm).left ⟶ pullback A.hom π :=
    pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₁ ≫ pullback.snd A.hom π) (by rw [hw1]; simp)
  let a' : (A ⊗ FinalForm).left ⟶ pullback A.hom π :=
    pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₂ ≫ pullback.snd A.hom π) (by rw [hw1, hπ]; simp)
  let p0 : (A ⊗ FinalForm).left ⟶ Z := (snd A FinalForm).left
  let e : Z ⟶ (A ⊗ FinalForm).left := (lift (toUnit FinalForm ≫ η[A]) (𝟙 FinalForm)).left
  have he : e ≫ p0 = 𝟙 Z := by
    simp only [e, p0]
    rw [← Over.comp_left, lift_snd]
    rfl
  have hap : a ≫ pullback.fst A.hom π = a' ≫ pullback.fst A.hom π := by
    simp only [a, a']
    rw [pullback.lift_fst, pullback.lift_fst]
  have hU : (toUnit FinalForm).left = g₁ ≫ pullback.snd A.hom π ≫ π :=
    (Category.comp_id _).symm.trans (Over.w (toUnit FinalForm))
  have hea : e ≫ a = g₁ ≫ pullback.snd A.hom π ≫ e' := by
    apply pullback.hom_ext
    · simp only [a, e, Category.assoc, pullback.lift_fst, he'p]
      rw [← Over.comp_left, lift_fst, Over.comp_left, hU]
      rfl
    · simp only [a, e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have hea' : e ≫ a' = g₂ ≫ pullback.snd A.hom π ≫ e' := by
    apply pullback.hom_ext
    · simp only [a', e, Category.assoc, pullback.lift_fst, he'p]
      rw [← Over.comp_left, lift_fst, Over.comp_left, hU, hπ]
      rfl
    · simp only [a', e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  let x : FinalForm ⟶ A := Over.homMk (g₁ ≫ pullback.fst A.hom π) (by simp [FinalForm, pullback.condition])
  let ρ : Z ⟶ (A ⊗ FinalForm).left := (lift x (𝟙 FinalForm)).left
  have hρp : ρ ≫ p0 = 𝟙 Z := by
    simp only [ρ, p0]
    rw [← Over.comp_left, lift_snd]
    rfl
  have hρa : ρ ≫ a = g₁ := by
    apply pullback.hom_ext
    · simp only [a, ρ, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left, lift_fst]
      rfl
    · simp only [a, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hρp, Category.id_comp]
  have hρa' : ρ ≫ a' = g₂ := by
    apply pullback.hom_ext
    · simp only [a', ρ, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left, lift_fst, ← hg]
      rfl
    · simp only [a', Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hρp, Category.id_comp]
  let u := LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a) (LB.pullGen N _ _ w (p0 ≫ e ≫ a'))
  let u' := LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a') (LB.pullGen N _ _ w (p0 ≫ e ≫ a))
  have hu : u.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)
  have hu' : u'.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a') (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)
  have hF : FormEq (Sum.elim (fun _ : PUnit.{1} => a' ≫ pullback.fst A.hom π)
        (fun _ : PUnit.{1} => (p0 ≫ e ≫ a) ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1))
      (Sum.elim (fun _ : PUnit.{1} => a ≫ pullback.fst A.hom π)
        (fun _ : PUnit.{1} => (p0 ≫ e ≫ a') ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1)) := by
    intro U _ h
    simp [Fintype.prod_sum_type, hap]
  have key := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gen_unique' hN hF p0 e he
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_snd hG hA FinalForm) hu hu' ?_ Z ρ z J hJ
  · simp only [u, u'] at key
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ] at key
    have hρp' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), ρ ≫ p0 ≫ h = h := fun h => by
      rw [← Category.assoc, hρp, Category.id_comp]
    rw [hρp', hρp', hea', hea, hρa, hρa'] at key
    exact key
  · intro y J' hJ'
    simp only [u, u']
    rw [val_mul hJ', val_mul hJ', val_pull hJ', val_pull hJ', val_pull hJ', val_pull hJ']
    have he' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), e ≫ p0 ≫ h = h := fun h => by
      rw [← Category.assoc, he, Category.id_comp]
    rw [he', he', mul_comm]

/- English proof (translation)
Introduce `hG S S' π A _ N hA hN hfl hsu hqc hr hw`. Take `⟨r, hr⟩` from `hr`. Take `⟨w, hw⟩` from `hw`. Use `hfl` as an intermediate fact. Use `hsu` as an intermediate fact.

Use `hqc` as an intermediate fact. Establish `hz : (π ≫ eSec A) ≫ A.hom = 𝟙 S' ≫ π`. Rewrite using `[Category.assoc, Category.id_comp]`. Establish `h0 : (η[A]).left ≫ A.hom = 𝟙 S` using `Over.w (η[A])`. Unfold `eSec`.

Rewrite using `[h0, Category.comp_id]`. Set `e' : S' ⟶ pullback A.hom π` to `pullback.lift (π ≫ eSec A) (𝟙 S') hz`. Establish `he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A` using `pullback.lift_fst _ _ _`. Establish `he'q : e' ≫ pullback.snd A.hom π = 𝟙 S'` using `pullback.lift_snd _ _ _`. Set `w' : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen` to `w`.

Establish `hw' : w'.IsGen` using `hw`. Set `r' : (N.LinComb (fun _ : PUnit.{1} => eSec A) (fun _ => (1 : ℤ))).Gen` to `r`. Establish `hr' : r'.IsGen` using `hr`. Set `v` to `LB.mulGen N _ _ _ _ w' (LB.mulGen N _ _ _ _ (LB.pullGen N _ _ r' (pullback.snd A.hom π ≫ π)) (LB.invGen N _ _ (LB.pullGen N _ _ w' (pullback.snd A.hom π ≫ e'))))`. Establish `hv : v.IsGen` using `ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ hw' (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ r' hr' _) (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ _ (Rec …`.

Take `⟨t', ht', hvv⟩` from `ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN (φ' := fun _ : PUnit.{1} => pullback.fst A.hom π ≫ 𝟙 A.left) (ε' := fun _ => (1 : ℤ)) (by intro U _ h; simp [Fintype.prod_sum_type, he'p]) v hv`. Use `Exists.elim (GlobalTheory.CubeDescent.exists_gen_descend hN (pullback.fst A.hom π) (fun _ : PUnit.{1} => 𝟙 A.left) (fun _ => (1 : ℤ)) t' ht' ?_) (fun t ht => exists_gen_of_pull_id N t ht)` and prove the remaining obligations. Introduce `Z g₁ g₂ z J hJ hg`. Rewrite using `[hvv Z g₁ z J hJ, hvv Z g₂ z J hJ]`. Simplify using `only [v, val_mul hJ, val_pull hJ, val_inv]`.

Establish `hq : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π`. Rewrite using `[← pullback.condition, ← Category.assoc, ← Category.assoc, hg]`. Rewrite using `[hq]`. Establish `key` using `val_mul_val_comm_of_fst_eq hG π A N hA hN w' hw' e' he'p he'q g₁ g₂ hg z J hJ`. Rewrite using `[mul_left_comm (val w' g₁ z J), mul_left_comm (val w' g₂ z J)]`.

Use `congr 1`. Rewrite using `[← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]`. Conclude with `key`.
-/
theorem exists_gen_of_rigidified_of_flat_baseChange :
    Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro hG S S' π A _ N hA hN hfl hsu hqc hr hw
  obtain ⟨r, hr⟩ := hr
  obtain ⟨w, hw⟩ := hw
  have := hfl
  have := hsu
  have := hqc
  have hz : (π ≫ eSec A) ≫ A.hom = 𝟙 S' ≫ π := by
    rw [Category.assoc, Category.id_comp]
    have h0 : (η[A]).left ≫ A.hom = 𝟙 S := Over.w (η[A])
    unfold eSec
    rw [h0, Category.comp_id]
  let e' : S' ⟶ pullback A.hom π := pullback.lift (π ≫ eSec A) (𝟙 S') hz
  have he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A := pullback.lift_fst _ _ _
  have he'q : e' ≫ pullback.snd A.hom π = 𝟙 S' := pullback.lift_snd _ _ _
  let w' : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen := w
  have hw' : w'.IsGen := hw
  let r' : (N.LinComb (fun _ : PUnit.{1} => eSec A) (fun _ => (1 : ℤ))).Gen := r
  have hr' : r'.IsGen := hr
  let v := LB.mulGen N _ _ _ _ w' (LB.mulGen N _ _ _ _ (LB.pullGen N _ _ r' (pullback.snd A.hom π ≫ π))
    (LB.invGen N _ _ (LB.pullGen N _ _ w' (pullback.snd A.hom π ≫ e'))))
  have hv : v.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ hw'
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ r' hr' _)
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w' hw' _)))
  obtain ⟨t', ht', hvv⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
    (φ' := fun _ : PUnit.{1} => pullback.fst A.hom π ≫ 𝟙 A.left) (ε' := fun _ => (1 : ℤ))
    (by intro U _ h; simp [Fintype.prod_sum_type, he'p]) v hv
  refine Exists.elim (GlobalTheory.CubeDescent.exists_gen_descend hN (pullback.fst A.hom π)
    (fun _ : PUnit.{1} => 𝟙 A.left) (fun _ => (1 : ℤ)) t' ht' ?_) (fun t ht => exists_gen_of_pull_id N t ht)
  · intro Z g₁ g₂ z J hJ hg
    rw [hvv Z g₁ z J hJ, hvv Z g₂ z J hJ]
    simp only [v, val_mul hJ, val_pull hJ, val_inv]
    have hq : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π := by
      rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hg]
    rw [hq]
    have key := val_mul_val_comm_of_fst_eq hG π A N hA hN w' hw' e' he'p he'q g₁ g₂ hg z J hJ
    rw [mul_left_comm (val w' g₁ z J), mul_left_comm (val w' g₂ z J)]
    congr 1
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    exact key

end GlobalTheory
