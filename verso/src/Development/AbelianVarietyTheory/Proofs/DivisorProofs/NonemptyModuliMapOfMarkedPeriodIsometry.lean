import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedBundleIsoOfWeilPairingEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsMonHomOfLinearMapKernelsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfPeriod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullGenLBIsGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTIso

/- English proof (translation)
Rewrite using `[Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]`.
-/
theorem one_comp_monHom {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (f : A ⟶ A') [IsMonHom f] :
    (1 : A ⟶ A) ≫ f = 1 := by
  rw [Hom.one_def, Hom.one_def, Category.assoc, IsMonHom.one_hom]

/- English proof (translation)
Rewrite using `[Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]`.
-/
theorem comp_one' {S : Scheme.{0}} {A A' : Over S} [GrpObj A'] (f : A ⟶ A') : f ≫ (1 : A' ⟶ A') = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, comp_toUnit]

/- English proof (translation)
Introduce `S A A' _ _ _ _ f hf P hP ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hs`. Use `haveI := hf`. Use `set φ₂ := (lift (fst A A ≫ f) (snd A A ≫ f)).left with hφ₂`. Establish `hP₂ : (P.pull φ₂).IsLB` using `pull_isLB hP _`. Establish `triv : ∀ (l : A ⟶ G2 A) (l' : A' ⟶ G2 A'), l ≫ lift (fst A A ≫ f) (snd A A ≫ f) = f ≫ l' → ∀ t : (P.pull l'.left).Gen, t.IsGen → ∃ s : ((P.pull φ₂).pull l.left).Gen, s.IsGen`.

Introduce `l l' hl t ht`. Establish `e₁ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull l'.left).pull f.left)` using `GlobalTheory.GenSpread.lbIso_pull_pull hP f.left rfl`. Establish `e₂ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull φ₂).pull l.left)` using `GlobalTheory.GenSpread.lbIso_pull_pull hP l.left (by rw [hφ₂, ← Over.comp_left, ← Over.comp_left, hl])`. Take `⟨s, hs⟩` from `GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e₁.symm (pullGenLB t f.left) (pullGenLB_isGen ht f.left)`. Conclude with `GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP _) (pull_isLB hP₂ _) e₂ s hs`.

Use `⟨hP₂, triv _ _ ?_ t₁ ht₁, triv _ _ ?_ t₂ ht₂, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']`. Establish `eq : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A' A') (fst A' A')).left`. Rewrite using `[hφ₂, ← Over.comp_left, ← Over.comp_left]`.

Use `congr 1`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Establish `e₁ : LBIso (P.pull φ₂) ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂)` using `GlobalTheory.GenSpread.lbIso_pullback hs φ₂`. Establish `e₂ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left)) ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂)` using `GlobalTheory.GenSpread.lbIso_pull_pull hP φ₂ rfl`. Establish `e₃ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left)) ((P.pull φ₂).pull (lift (snd A A) (fst A A)).left)` using `GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq.symm`.

Conclude with `LBIso.trans hP₂ (pull_isLB (pull_isLB hP _) _) (pull_isLB hP₂ _) e₁ (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hP₂ _) e₂.symm e₃)`.
-/
theorem pull_birig : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (f : A ⟶ A'), IsMonHom f → ∀ P : LB (G2 A').left, P.IsLB →
    (∃ t : (P.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A' A') (fst A' A')).left) →
    (P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).IsLB ∧
    (∃ t : ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧
    LBIso (P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left)
      ((P.pull (lift (fst A A ≫ f) (snd A A ≫ f)).left).pull (lift (snd A A) (fst A A)).left) := by
  intro S A A' _ _ _ _ f hf P hP ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩ hs
  haveI := hf
  set φ₂ := (lift (fst A A ≫ f) (snd A A ≫ f)).left with hφ₂
  have hP₂ : (P.pull φ₂).IsLB := pull_isLB hP _

  have triv : ∀ (l : A ⟶ G2 A) (l' : A' ⟶ G2 A'), l ≫ lift (fst A A ≫ f) (snd A A ≫ f) = f ≫ l' →
      ∀ t : (P.pull l'.left).Gen, t.IsGen → ∃ s : ((P.pull φ₂).pull l.left).Gen, s.IsGen := by
    intro l l' hl t ht
    have e₁ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull l'.left).pull f.left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP f.left rfl
    have e₂ : LBIso (P.pull (f.left ≫ l'.left)) ((P.pull φ₂).pull l.left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP l.left (by rw [hφ₂, ← Over.comp_left, ← Over.comp_left, hl])
    obtain ⟨s, hs⟩ := GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) e₁.symm
      (pullGenLB t f.left) (pullGenLB_isGen ht f.left)
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP _) (pull_isLB hP₂ _) e₂ s hs
  refine ⟨hP₂, triv _ _ ?_ t₁ ht₁, triv _ _ ?_ t₂ ht₂, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']
  · apply CartesianMonoidalCategory.hom_ext <;> simp [one_comp_monHom, comp_one']
  · have eq : (lift (snd A A) (fst A A)).left ≫ φ₂ = φ₂ ≫ (lift (snd A' A') (fst A' A')).left := by
      rw [hφ₂, ← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext <;> simp
    have e₁ : LBIso (P.pull φ₂) ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂) :=
      GlobalTheory.GenSpread.lbIso_pullback hs φ₂
    have e₂ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left))
        ((P.pull (lift (snd A' A') (fst A' A')).left).pull φ₂) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP φ₂ rfl
    have e₃ : LBIso (P.pull (φ₂ ≫ (lift (snd A' A') (fst A' A')).left)) ((P.pull φ₂).pull (lift (snd A A) (fst A A)).left) :=
      GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq.symm
    exact LBIso.trans hP₂ (pull_isLB (pull_isLB hP _) _) (pull_isLB hP₂ _) e₁
      (LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB hP₂ _) e₂.symm e₃)

/- English proof (translation)
Introduce `S A A' _ _ _ _ F hF P hP T k x y c H`. Use `haveI := hF`. Use `set φ₂ := (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left with hφ₂`. Establish `eq : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = F.hom.left ≫ (lift (𝟙 A') (𝟙 A')).left`. Rewrite using `[hφ₂, ← Over.comp_left, ← Over.comp_left]`.

Use `congr 1`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp`. Establish `e₁ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left)` using `GlobalTheory.GenSpread.lbIso_pull_pull hP _ rfl`. Establish `e₂ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull (lift (𝟙 A') (𝟙 A')).left).pull F.hom.left)` using `GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq`. Establish `iso` using `LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁.symm e₂`.

Set `x₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A'` to `Over.homMk (x.left ≫ F.hom.left) (by simp)`. Set `y₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A'` to `Over.homMk (y.left ≫ F.hom.left) (by simp)`. Use `(GlobalTheory.weilIs_iff_of_isGrpPullback_comm S S A' A (𝟙 S) F.hom.left _ _ (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) (isGrpPullback_of_iso F) iso T k x y x₀ y₀ c rfl rfl).2 ?_` and prove the remaining obligations. Conclude with `GlobalTheory.UnifPoint.weilIs_congr (Category.comp_id _).symm rfl rfl H`.
-/
theorem weil_pull_iso : ∀ (S : Scheme.{0}) (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (F : A ≅ A'), IsMonHom F.hom → ∀ P : LB (G2 A').left, P.IsLB → ∀ (T : Over S) (k : ℤ) (x y : T ⟶ A)
    (c : Γ(T.left, ⊤)ˣ), Out.WeilIs A' (P.pull (lift (𝟙 A') (𝟙 A')).left) k (x ≫ F.hom) (y ≫ F.hom) c →
    Out.WeilIs A ((P.pull (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left).pull (lift (𝟙 A) (𝟙 A)).left) k x y c := by
  intro S A A' _ _ _ _ F hF P hP T k x y c H
  haveI := hF
  set φ₂ := (lift (fst A A ≫ F.hom) (snd A A ≫ F.hom)).left with hφ₂
  have eq : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = F.hom.left ≫ (lift (𝟙 A') (𝟙 A')).left := by
    rw [hφ₂, ← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have e₁ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP _ rfl
  have e₂ : LBIso (P.pull ((lift (𝟙 A) (𝟙 A)).left ≫ φ₂)) ((P.pull (lift (𝟙 A') (𝟙 A')).left).pull F.hom.left) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP _ eq
  have iso := LBIso.trans (pull_isLB (pull_isLB hP _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁.symm e₂
  let x₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A' := Over.homMk (x.left ≫ F.hom.left) (by simp)
  let y₀ : Over.mk (T.hom ≫ 𝟙 S) ⟶ A' := Over.homMk (y.left ≫ F.hom.left) (by simp)
  refine (GlobalTheory.weilIs_iff_of_isGrpPullback_comm S S A' A (𝟙 S) F.hom.left _ _ (pull_isLB hP _)
    (pull_isLB (pull_isLB hP _) _) (isGrpPullback_of_iso F) iso T k x y x₀ y₀ c rfl rfl).2 ?_
  exact GlobalTheory.UnifPoint.weilIs_congr (Category.comp_id _).symm rfl rfl H

/- English proof (translation)
Introduce and unpack `p _ D R _ b N σ ρ o o' h hL h' hL' D' D'' t t' Q Q' e e' w u hN0 ⟨-, hP, he, hk, hl, hw, hη⟩ ⟨-, hP', he', hk', hl', hw', hη'⟩ ⟨hiso, hmark⟩ hu`. Establish `k1 : ∀ z, e z = 1 → e' (u z) = 1`. Introduce `z hz`. Take `⟨x, rfl⟩` from `(hk z).1 hz`. Conclude with `(hk' _).2 ⟨w x, hu x⟩`.

Establish `k2 : ∀ z, e' z = 1 → e (u.symm z) = 1`. Introduce `z hz`. Take `⟨x, rfl⟩` from `(hk' z).1 hz`. Use `(hk _).2 ⟨w.symm x, ?_⟩` and prove the remaining obligations. Apply `u.injective` to reduce the goal to its premises.

Rewrite using `[u.apply_symm_apply, ← hu, w.apply_symm_apply]`. Take `⟨f, ⟨hf, hfe⟩, -⟩` from `GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o'.A D.g D.g o.ab o'.ab h h' e e' u.toLinearMap he he' k1`. Take `⟨f', ⟨hf', hfe'⟩, -⟩` from `GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o'.A o.A D.g D.g o'.ab o.ab h' h e' e u.symm.toLinearMap he' he k2`. Take `⟨f₀, -, uid⟩` from `GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o.A D.g D.g o.ab o.ab h h e e LinearMap.id he he (fun z hz => hz)`. Take `⟨f₀', -, uid'⟩` from `GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o'.A o'.A D.g D.g o'.ab o'.ab h' h' e' e' LinearMap.id he' he' (fun z hz => hz)`.

Establish `hfe2 : ∀ z, e' (u z) = e z ≫ f` using `hfe`. Establish `hfe2' : ∀ z, e (u.symm z) = e' z ≫ f'` using `hfe'`. Use `haveI := hf`. Use `haveI := hf'`. Establish `c1 : f ≫ f' = 𝟙 _`.

Rewrite using `[uid (f ≫ f') ⟨inferInstance, fun z => ?_⟩, uid (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]`. Use `Eq.trans ?_ (Category.assoc (e z) f f')` and prove the remaining obligations. Rewrite using `[← hfe2]`. Conclude with `(by rw [u.symm_apply_apply]; rfl : e (LinearMap.id z) = e (u.symm (u z))).trans (hfe2' (u z))`. Establish `c2 : f' ≫ f = 𝟙 _`.

Rewrite using `[uid' (f' ≫ f) ⟨inferInstance, fun z => ?_⟩, uid' (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]`. Use `Eq.trans ?_ (Category.assoc (e' z) f' f)` and prove the remaining obligations. Rewrite using `[← hfe2']`. Conclude with `(by rw [u.apply_symm_apply]; rfl : e' (LinearMap.id z) = e' (u (u.symm z))).trans (hfe2 (u.symm z))`. Set `F : o.A ≅ o'.A` to `⟨f, f', c1, c2⟩`.

Use `haveI : IsMonHom F.hom := hf`. Establish `hcomm : ∀ (c : D.O) z, u (ρ c *ᵥ z) = ρ c *ᵥ u z`. Introduce `c`. Use `LinearMap.ext_on_range (R := ℝ) (v := fun x => Q x) hP.2.2.2.1 (f := (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)).restrictScalars ℝ) (g := (Matrix.toLin' (ρ c) ∘ₗ u.toLinearMap).restrictScalars ℝ) (fun x => by` as an intermediate fact. Simplify using `only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]`.

Rewrite using `[← hP.1, ← hu, ← hu, w.map_smul, hP'.1])`. Introduce `z`. Simplify using `using LinearMap.congr_fun this z`. Establish `hact : ∀ c, o.act.act c ≫ f = f ≫ o'.act.act c`. Introduce `c`.

Use `haveI := o.act.hom c`. Use `haveI := o'.act.hom c`. Take `⟨fa, -, ua⟩` from `GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o'.A D.g D.g o.ab o'.ab h h' e e' (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)) he he' (fun z hz => by`. Take `⟨x, rfl⟩` from `(hk z).1 hz`. Simplify using `only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]`.

Rewrite using `[← hP.1]`. Conclude with `k1 _ ((hk _).2 ⟨_, rfl⟩))`. Rewrite using `[ua (o.act.act c ≫ f) ⟨inferInstance, fun z => ?_⟩, ua (f ≫ o'.act.act c) ⟨inferInstance, fun z => ?_⟩]`. Simplify using `only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]`. Use `Eq.trans ?_ (Category.assoc (e z) f (o'.act.act c))` and prove the remaining obligations.

Rewrite using `[← hfe2, hcomm]`. Conclude with `hl' c (u z)`. Simplify using `only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]`. Use `Eq.trans ?_ (Category.assoc (e z) (o.act.act c) f)` and prove the remaining obligations. Rewrite using `[hfe2]`.

Conclude with `congrArg (· ≫ f) (hl c z)`. Establish `hT : (toUnit (Over.mk (𝟙 (Sp ℂ)))).left = 𝟙 _`. Simplify using `using Over.w (toUnit (Over.mk (𝟙 (Sp ℂ))))`. Establish `heta : ∀ y, (o.eta y).left ≫ f.left = 𝟙 _ ≫ (o'.eta y).left`. Introduce `y`.

Take `⟨e₀, he₀⟩` from `hmark y`. Establish `hN : (N : ℂ) ≠ 0` using `by exact_mod_cast hN0.ne'`. Establish `hη2 : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y = e ((N : ℂ)⁻¹ • Q (t y))` using `hη y`. Establish `hη2' : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y = e' ((N : ℂ)⁻¹ • Q' (t' y))` using `hη' y`. Establish `a1 : (toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y) ≫ f = toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y`.

Use `(congrArg (· ≫ f) hη2).trans ((hfe2 _).symm.trans (Eq.trans ?_ hη2'.symm))` and prove the remaining obligations. Establish `hz : (N : ℂ)⁻¹ • N • Q' e₀ = Q' e₀`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]`. Rewrite using `[map_smul, ← hu, he₀, map_add, map_nsmul, smul_add, hz, he'.1, (hk' (Q' e₀)).2 ⟨e₀, rfl⟩, _root_.mul_one]`. Establish `a2` using `congrArg (fun q => q.left) a1`.

Simplify using `only [Over.comp_left, hT, Category.id_comp] at a2`. Rewrite using `[Category.id_comp]`. Conclude with `a2`. Take `⟨B1, B2, B3, B4⟩` from `pull_birig (Sp ℂ) o.A o'.A f hf o'.P o'.isLB o'.rig₁ o'.rig₂ o'.symm`. Establish `ew : ∀ (k : ℕ) a, e' ((k : ℂ)⁻¹ • Q' (w a)) = e ((k : ℂ)⁻¹ • Q a) ≫ f`.

Introduce `k a`. Rewrite using `[hu, ← u.map_smul]`. Conclude with `hfe2 _`. Establish `pol` using `GlobalTheory.T.birigidified_bundle_iso_of_weil_pairing_eq o.A D.g o.ab h o.P (o'.P.pull (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left) o.isLB o.rig₁ o.rig₂ o.symm B1 B2 B3 B4 e D'.La Q D'.EF he hP.2.1 hk hw (fun k a a₂ c hk0 hc => by`. Establish `W'` using `hw' k (w a) (w a₂) c hk0 (by rw [hiso]; exact hc)`.

Rewrite `W'` using `[ew, ew]`. Conclude with `weil_pull_iso (Sp ℂ) o.A o'.A F inferInstance o'.P o'.isLB _ k _ _ _ W')`. Conclude with `⟨{ φ := f.left φ₂ := (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left cart := isGrpPullback_of_iso F sq := ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩ act := fun c => by rw [← Over.comp_left, hact c, Over.comp_left] pol …`.
-/
theorem nonempty_objMap_of_markedIsom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o o' : Obj b N (spMap σ)) h hL h' hL' (D' D'' : PLat D.O D.inv) t t' Q Q' e e' (w : D'.La ≃ₗ[D.O] D''.La) (u : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)), 0 < N → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → UnifAt (o'.fam h' hL') σ ρ N D'' t' Q' (𝟙 _) e' → IsMarkedIsom N D' D'' t t' w → (∀ x, Q' (w x) = u (Q x)) → Nonempty (ObjMap o o' (𝟙 _)) := by
  rintro p _ D R _ b N σ ρ o o' h hL h' hL' D' D'' t t' Q Q' e e' w u hN0
    ⟨-, hP, he, hk, hl, hw, hη⟩ ⟨-, hP', he', hk', hl', hw', hη'⟩ ⟨hiso, hmark⟩ hu

  have k1 : ∀ z, e z = 1 → e' (u z) = 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hk z).1 hz
    exact (hk' _).2 ⟨w x, hu x⟩
  have k2 : ∀ z, e' z = 1 → e (u.symm z) = 1 := by
    intro z hz
    obtain ⟨x, rfl⟩ := (hk' z).1 hz
    refine (hk _).2 ⟨w.symm x, ?_⟩
    apply u.injective
    rw [u.apply_symm_apply, ← hu, w.apply_symm_apply]
  obtain ⟨f, ⟨hf, hfe⟩, -⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o'.A D.g D.g o.ab o'.ab h h' e e' u.toLinearMap he he' k1
  obtain ⟨f', ⟨hf', hfe'⟩, -⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o'.A o.A D.g D.g o'.ab o.ab h' h e' e u.symm.toLinearMap he' he k2
  obtain ⟨f₀, -, uid⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o.A D.g D.g o.ab o.ab h h e e LinearMap.id he he (fun z hz => hz)
  obtain ⟨f₀', -, uid'⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o'.A o'.A D.g D.g o'.ab o'.ab h' h' e' e' LinearMap.id he' he' (fun z hz => hz)
  have hfe2 : ∀ z, e' (u z) = e z ≫ f := hfe
  have hfe2' : ∀ z, e (u.symm z) = e' z ≫ f' := hfe'
  haveI := hf
  haveI := hf'
  have c1 : f ≫ f' = 𝟙 _ := by
    rw [uid (f ≫ f') ⟨inferInstance, fun z => ?_⟩, uid (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]
    refine Eq.trans ?_ (Category.assoc (e z) f f')
    rw [← hfe2]
    exact (by rw [u.symm_apply_apply]; rfl : e (LinearMap.id z) = e (u.symm (u z))).trans (hfe2' (u z))
  have c2 : f' ≫ f = 𝟙 _ := by
    rw [uid' (f' ≫ f) ⟨inferInstance, fun z => ?_⟩, uid' (𝟙 _) ⟨inferInstance, fun z => (Category.comp_id _).symm⟩]
    refine Eq.trans ?_ (Category.assoc (e' z) f' f)
    rw [← hfe2']
    exact (by rw [u.apply_symm_apply]; rfl : e' (LinearMap.id z) = e' (u (u.symm z))).trans (hfe2 (u.symm z))
  let F : o.A ≅ o'.A := ⟨f, f', c1, c2⟩
  haveI : IsMonHom F.hom := hf

  have hcomm : ∀ (c : D.O) z, u (ρ c *ᵥ z) = ρ c *ᵥ u z := by
    intro c
    have := LinearMap.ext_on_range (R := ℝ) (v := fun x => Q x) hP.2.2.2.1
      (f := (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)).restrictScalars ℝ)
      (g := (Matrix.toLin' (ρ c) ∘ₗ u.toLinearMap).restrictScalars ℝ) (fun x => by
        simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
        rw [← hP.1, ← hu, ← hu, w.map_smul, hP'.1])
    intro z
    simpa using LinearMap.congr_fun this z
  have hact : ∀ c, o.act.act c ≫ f = f ≫ o'.act.act c := by
    intro c
    haveI := o.act.hom c
    haveI := o'.act.hom c
    obtain ⟨fa, -, ua⟩ := GlobalTheory.T.existsUnique_isMonHom_of_linear_map_kernels o.A o'.A D.g D.g o.ab o'.ab h h' e e'
      (u.toLinearMap ∘ₗ Matrix.toLin' (ρ c)) he he' (fun z hz => by
        obtain ⟨x, rfl⟩ := (hk z).1 hz
        simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
        rw [← hP.1]
        exact k1 _ ((hk _).2 ⟨_, rfl⟩))
    rw [ua (o.act.act c ≫ f) ⟨inferInstance, fun z => ?_⟩, ua (f ≫ o'.act.act c) ⟨inferInstance, fun z => ?_⟩]
    · simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
      refine Eq.trans ?_ (Category.assoc (e z) f (o'.act.act c))
      rw [← hfe2, hcomm]
      exact hl' c (u z)
    · simp only [LinearMap.comp_apply, Matrix.toLin'_apply, LinearEquiv.coe_coe]
      refine Eq.trans ?_ (Category.assoc (e z) (o.act.act c) f)
      rw [hfe2]
      exact congrArg (· ≫ f) (hl c z)
  have hT : (toUnit (Over.mk (𝟙 (Sp ℂ)))).left = 𝟙 _ := by
    simpa using Over.w (toUnit (Over.mk (𝟙 (Sp ℂ))))
  have heta : ∀ y, (o.eta y).left ≫ f.left = 𝟙 _ ≫ (o'.eta y).left := by
    intro y
    obtain ⟨e₀, he₀⟩ := hmark y
    have hN : (N : ℂ) ≠ 0 := by exact_mod_cast hN0.ne'
    have hη2 : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y = e ((N : ℂ)⁻¹ • Q (t y)) := hη y
    have hη2' : toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y = e' ((N : ℂ)⁻¹ • Q' (t' y)) := hη' y
    have a1 : (toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o.eta y) ≫ f = toUnit (Over.mk (𝟙 (Sp ℂ))) ≫ o'.eta y := by
      refine (congrArg (· ≫ f) hη2).trans ((hfe2 _).symm.trans (Eq.trans ?_ hη2'.symm))
      have hz : (N : ℂ)⁻¹ • N • Q' e₀ = Q' e₀ := by
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]
      rw [map_smul, ← hu, he₀, map_add, map_nsmul, smul_add, hz, he'.1, (hk' (Q' e₀)).2 ⟨e₀, rfl⟩, _root_.mul_one]
    have a2 := congrArg (fun q => q.left) a1
    simp only [Over.comp_left, hT, Category.id_comp] at a2
    rw [Category.id_comp]
    exact a2
  obtain ⟨B1, B2, B3, B4⟩ := pull_birig (Sp ℂ) o.A o'.A f hf o'.P o'.isLB o'.rig₁ o'.rig₂ o'.symm
  have ew : ∀ (k : ℕ) a, e' ((k : ℂ)⁻¹ • Q' (w a)) = e ((k : ℂ)⁻¹ • Q a) ≫ f := by
    intro k a
    rw [hu, ← u.map_smul]
    exact hfe2 _
  have pol := GlobalTheory.T.birigidified_bundle_iso_of_weil_pairing_eq o.A D.g o.ab h o.P (o'.P.pull (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left)
    o.isLB o.rig₁ o.rig₂ o.symm B1 B2 B3 B4 e D'.La Q D'.EF he hP.2.1 hk hw (fun k a a₂ c hk0 hc => by
      have W' := hw' k (w a) (w a₂) c hk0 (by rw [hiso]; exact hc)
      rw [ew, ew] at W'
      exact weil_pull_iso (Sp ℂ) o.A o'.A F inferInstance o'.P o'.isLB _ k _ _ _ W')
  exact ⟨{ φ := f.left
           φ₂ := (lift (fst o.A o.A ≫ f) (snd o.A o.A ≫ f)).left
           cart := isGrpPullback_of_iso F
           sq := ⟨by rw [← Over.comp_left, lift_fst, Over.comp_left], by rw [← Over.comp_left, lift_snd, Over.comp_left]⟩
           act := fun c => by rw [← Over.comp_left, hact c, Over.comp_left]
           pol := pol
           eta := heta }⟩

end GlobalTheory.HTIso
