import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.IsConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackFormVanishesTangentsOfLieBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExist

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

/- English proof (translation)
Simplify using `only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]`.
-/
private theorem sp {X Y Z : Type} [CommRing X] [CommRing Y] [CommRing Z] (f : X →+* Y) (g : Y →+* Z) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

/- English proof (translation)
Rewrite using `[Hom.one_def, Over.comp_left]`. Use `congr 1`.
-/
private theorem one_left' {S : Scheme.{0}} {A : Over S} [GrpObj A] (T : Over S) :
    (1 : T ⟶ A).left = T.hom ≫ η[A].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

/- English proof (translation)
Set `T : Over (Sp k)` to `𝟙_ (Over (Sp k))`. Set `x₀ : Over.mk (T.hom ≫ spMap σ) ⟶ A` to `Over.homMk (η[A].left ≫ ψ) (by`. Establish `h1` using `Over.w η[A]`. Establish `h2` using `hψ.w`. Simplify using `only [Category.assoc, h2]`.

Rewrite using `[← Category.assoc, h1]`. Use the proof step `rfl)`. Establish `h` using `hψ.mul T (1 : T ⟶ A) (1 : T ⟶ A) x₀ x₀ (by simp [x₀, one_left'] ; rfl) (by simp [x₀, one_left']; rfl)`. Establish `h1 : x₀ * x₀ = x₀`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises.

Rewrite using `[h, _root_.mul_one]`. Simplify using `[x₀, one_left']`. Both sides reduce to the same expression. Establish `h2 : x₀ = 1` using `by simpa using h1`. Establish `h3` using `congrArg Over.Hom.left h2`.

Rewrite `h3` using `[one_left']`. Establish `h4 : T.hom = 𝟙 _` using `rfl`. Simplify `h3` using `[x₀, h4]`.
-/
private theorem eta_comp {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {σ : k →+* k} {ψ : A.left ⟶ A.left}
    (hψ : SMor A σ ψ) : η[A].left ≫ ψ = spMap σ ≫ η[A].left := by
  let T : Over (Sp k) := 𝟙_ (Over (Sp k))
  let x₀ : Over.mk (T.hom ≫ spMap σ) ⟶ A := Over.homMk (η[A].left ≫ ψ) (by
    have h1 := Over.w η[A]
    have h2 := hψ.w
    simp only [Category.assoc, h2]
    rw [← Category.assoc, h1]
    rfl)
  have h := hψ.mul T (1 : T ⟶ A) (1 : T ⟶ A) x₀ x₀ (by simp [x₀, one_left'] ; rfl) (by simp [x₀, one_left']; rfl)
  have h1 : x₀ * x₀ = x₀ := by
    apply Over.OverMorphism.ext
    rw [h, _root_.mul_one]
    simp [x₀, one_left']
    rfl
  have h2 : x₀ = 1 := by simpa using h1
  have h3 := congrArg Over.Hom.left h2
  rw [one_left'] at h3
  have h4 : T.hom = 𝟙 _ := rfl
  simpa [x₀, h4] using h3

/- English proof (translation)
Establish `h0` using `congrArg Over.Hom.left ((GlobalTheory.GrpTangent.isTangent_iff w).1 hw)`. Rewrite `h0` using `[Over.comp_left, one_left']`. Establish `h1 : (GlobalTheory.GrpTangent.epsZero k).left ≫ w.left = η[A].left` using `by simpa using h0`. Conclude with `h1`.
-/
private theorem tan_left {k : Type} [Field k] {A : Over (Sp k)} [GrpObj A] {w : epsR k ⟶ A} (hw : IsTangent w) :
    spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = η[A].left := by
  have h0 := congrArg Over.Hom.left ((GlobalTheory.GrpTangent.isTangent_iff w).1 hw)
  rw [Over.comp_left, one_left'] at h0
  have h1 : (GlobalTheory.GrpTangent.epsZero k).left ≫ w.left = η[A].left := by simpa using h0
  exact h1

/- English proof (translation)
Introduce `k _ A _ hA σ ψ hψ hs v hv`. Set `e : k ≃+* k` to `RingEquiv.ofBijective σ ⟨σ.injective, hs⟩`. Set `τ : k →+* k` to `(e.symm : k →+* k)`. Establish `τσ : τ.comp σ = RingHom.id k` using `RingHom.ext fun x ↦ e.symm_apply_apply x`. Establish `στ : σ.comp τ = RingHom.id k` using `RingHom.ext fun x ↦ e.apply_symm_apply x`.

Set `d` to `Chart.dualMapR τ`. Set `u` to `Chart.dualMapR σ`. Set `fst : DualNumber k →+* k` to `(TrivSqZeroExt.fstHom k k k).toRingHom`. Set `alg` to `algebraMap k (DualNumber k)`. Establish `ud : u.comp d = RingHom.id _`.

Use `RingHom.ext fun x ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [d, u, Chart.dualMapR, ← RingHom.comp_apply, στ]`. Establish `fd : fst.comp d = τ.comp fst`. Use `RingHom.ext fun x ↦ ?_` and prove the remaining obligations. Simplify using `[d, fst, Chart.dualMapR]`.

Establish `dalg : d.comp (alg.comp σ) = alg`. Use `RingHom.ext fun x ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [d, alg, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl, ← RingHom.comp_apply, τσ]`. Establish `dc : d.comp (alg.comp fst) = (alg.comp fst).comp d`. Use `RingHom.ext fun x ↦ ?_` and prove the remaining obligations.

Apply the tactic sequence `ext <;> simp [d, alg, fst, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]`. Establish `cu : (alg.comp fst).comp (u.comp alg) = u.comp alg`. Use `RingHom.ext fun x ↦ ?_` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp [u, alg, fst, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]`. Set `v' : epsR k ⟶ A` to `Over.homMk (spMap d ≫ v.left ≫ ψ) (by`.

Establish `hv0` using `Over.w v`. Establish `h2` using `hψ.w`. Express the relevant statement in the definitionally equal form `(spMap d ≫ v.left ≫ ψ) ≫ A.hom = spMap alg`. Rewrite using `[Category.assoc, Category.assoc, h2, ← Category.assoc v.left, hv0]`. Express the relevant statement in the definitionally equal form `spMap d ≫ spMap alg ≫ spMap σ = _`.

Rewrite using `[sp, sp, dalg])`. Establish `e1 : v.left ≫ ψ = spMap u ≫ v'.left`. Express the relevant statement in the definitionally equal form `_ = spMap u ≫ spMap d ≫ v.left ≫ ψ`. Rewrite using `[← Category.assoc, sp, ud, spMap_id, Category.id_comp]`. Establish `hval` using `fun f ↦ GlobalTheory.LieDual.tanVal_pullForm_baseChange (v := v') (v' := v) hψ.isMor e1 f`.

Establish `htan : IsTangent v'`. Rewrite using `[GlobalTheory.GrpTangent.isTangent_iff]`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Over.comp_left, one_left']`. Express the relevant statement in the definitionally equal form `spMap fst ≫ spMap d ≫ v.left ≫ ψ = 𝟙 _ ≫ η[A].left`.

Establish `h00 : spMap fst ≫ v.left = η[A].left` using `tan_left hv`. Combine the equalities or inequalities in the displayed calculation. Take `⟨g, hg⟩` from `GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k A hA`. Establish `L : LieExact A` using `(GlobalTheory.abelianDeRham.2.1 k A g hA hg).1`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h0 : ∀ f : Form (A.hom ≫ 𝟙 _), Form.cl _ f ∈ primDR A → tanVal v' f = 0` using `fun f hf ↦ (map_eq_zero σ).1 ((hval f).symm.trans (h f hf))`. Take `⟨H, hH⟩` from `L.2 v' htan`. Establish `hF : H ∈ Fil A` using `mem_Fil.2 fun f hf ↦ by rw [hH.2, h0 f hf]`. Establish `h1 : v' = 1` using `(L.1 H).unique hH (isLieImage_one_iff.2 hF)`.

Establish `h2 : v'.left = spMap alg ≫ η[A].left` using `by rw [h1, one_left']; rfl`. Establish `h3 : spMap (alg.comp fst) ≫ spMap u ≫ spMap alg = spMap u ≫ spMap alg`. Rewrite using `[sp, sp, cu]`. Express the relevant statement in the definitionally equal form `spMap (alg.comp fst) ≫ v.left ≫ ψ = v.left ≫ ψ`. Rewrite using `[e1, h2]`.

Simplify `h3 =≫ η[A].left` using `only [Category.assoc]`. Introduce `h f hf`. Establish `h' : spMap (alg.comp fst) ≫ v.left ≫ ψ = v.left ≫ ψ` using `h`. Establish `h1 : v'.left = spMap (alg.comp fst) ≫ v'.left`. Express the relevant statement in the definitionally equal form `spMap d ≫ v.left ≫ ψ = spMap (alg.comp fst) ≫ spMap d ≫ v.left ≫ ψ`.

Combine the equalities or inequalities in the displayed calculation. Establish `h2 : v' = 1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[one_left', h1, ← sp, Category.assoc, tan_left htan]`. Both sides reduce to the same expression.

Rewrite using `[hval, h2, tanVal_one, map_zero]`.
-/
theorem UpperTheory.Gal.Ord.tan :
    ∀ (k : Type) [Field k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
      ∀ (σ : k →+* k) (ψ : A.left ⟶ A.left) (hψ : SMor A σ ψ), Function.Surjective σ →
      ∀ v : epsR k ⟶ A, IsTangent v →
        ((∀ f : Form (A.hom ≫ 𝟙 _), Form.cl _ f ∈ primDR A → tanVal v (hψ.isMor.pullForm f) = 0) ↔
          IsConst (v.left ≫ ψ)) := by
  intro k _ A _ hA σ ψ hψ hs v hv
  let e : k ≃+* k := RingEquiv.ofBijective σ ⟨σ.injective, hs⟩
  let τ : k →+* k := (e.symm : k →+* k)
  have τσ : τ.comp σ = RingHom.id k := RingHom.ext fun x ↦ e.symm_apply_apply x
  have στ : σ.comp τ = RingHom.id k := RingHom.ext fun x ↦ e.apply_symm_apply x
  let d := Chart.dualMapR τ
  let u := Chart.dualMapR σ
  let fst : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom
  let alg := algebraMap k (DualNumber k)
  have ud : u.comp d = RingHom.id _ := by
    refine RingHom.ext fun x ↦ ?_
    ext <;> simp [d, u, Chart.dualMapR, ← RingHom.comp_apply, στ]
  have fd : fst.comp d = τ.comp fst := by
    refine RingHom.ext fun x ↦ ?_
    simp [d, fst, Chart.dualMapR]
  have dalg : d.comp (alg.comp σ) = alg := by
    refine RingHom.ext fun x ↦ ?_
    ext <;> simp [d, alg, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl, ← RingHom.comp_apply, τσ]
  have dc : d.comp (alg.comp fst) = (alg.comp fst).comp d := by
    refine RingHom.ext fun x ↦ ?_
    ext <;> simp [d, alg, fst, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have cu : (alg.comp fst).comp (u.comp alg) = u.comp alg := by
    refine RingHom.ext fun x ↦ ?_
    ext <;> simp [u, alg, fst, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : epsR k ⟶ A := Over.homMk (spMap d ≫ v.left ≫ ψ) (by
    have hv0 := Over.w v
    have h2 := hψ.w
    change (spMap d ≫ v.left ≫ ψ) ≫ A.hom = spMap alg
    rw [Category.assoc, Category.assoc, h2, ← Category.assoc v.left, hv0]
    change spMap d ≫ spMap alg ≫ spMap σ = _
    rw [sp, sp, dalg])
  have e1 : v.left ≫ ψ = spMap u ≫ v'.left := by
    change _ = spMap u ≫ spMap d ≫ v.left ≫ ψ
    rw [← Category.assoc, sp, ud, spMap_id, Category.id_comp]
  have hval := fun f ↦ GlobalTheory.LieDual.tanVal_pullForm_baseChange (v := v') (v' := v) hψ.isMor e1 f
  have htan : IsTangent v' := by
    rw [GlobalTheory.GrpTangent.isTangent_iff]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, one_left']
    change spMap fst ≫ spMap d ≫ v.left ≫ ψ = 𝟙 _ ≫ η[A].left
    have h00 : spMap fst ≫ v.left = η[A].left := tan_left hv
    calc spMap fst ≫ spMap d ≫ v.left ≫ ψ = (spMap fst ≫ spMap d) ≫ v.left ≫ ψ := by rw [Category.assoc]
      _ = (spMap τ ≫ spMap fst) ≫ v.left ≫ ψ := by rw [sp, sp, fd]
      _ = spMap τ ≫ (spMap fst ≫ v.left) ≫ ψ := by simp only [Category.assoc]
      _ = spMap τ ≫ η[A].left ≫ ψ := by rw [h00]
      _ = (spMap τ ≫ spMap σ) ≫ η[A].left := by rw [eta_comp hψ, Category.assoc]
      _ = 𝟙 _ ≫ η[A].left := by rw [sp, τσ, spMap_id]; rfl
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k A hA
  have L : LieExact A := (GlobalTheory.abelianDeRham.2.1 k A g hA hg).1
  constructor
  · intro h
    have h0 : ∀ f : Form (A.hom ≫ 𝟙 _), Form.cl _ f ∈ primDR A → tanVal v' f = 0 := fun f hf ↦
      (map_eq_zero σ).1 ((hval f).symm.trans (h f hf))
    obtain ⟨H, hH⟩ := L.2 v' htan
    have hF : H ∈ Fil A := mem_Fil.2 fun f hf ↦ by rw [hH.2, h0 f hf]
    have h1 : v' = 1 := (L.1 H).unique hH (isLieImage_one_iff.2 hF)
    have h2 : v'.left = spMap alg ≫ η[A].left := by rw [h1, one_left']; rfl
    have h3 : spMap (alg.comp fst) ≫ spMap u ≫ spMap alg = spMap u ≫ spMap alg := by
      rw [sp, sp, cu]
    change spMap (alg.comp fst) ≫ v.left ≫ ψ = v.left ≫ ψ
    rw [e1, h2]
    simpa only [Category.assoc] using h3 =≫ η[A].left
  · intro h f hf
    have h' : spMap (alg.comp fst) ≫ v.left ≫ ψ = v.left ≫ ψ := h
    have h1 : v'.left = spMap (alg.comp fst) ≫ v'.left := by
      change spMap d ≫ v.left ≫ ψ = spMap (alg.comp fst) ≫ spMap d ≫ v.left ≫ ψ
      calc spMap d ≫ v.left ≫ ψ = spMap d ≫ spMap (alg.comp fst) ≫ v.left ≫ ψ := by rw [h']
        _ = (spMap d ≫ spMap (alg.comp fst)) ≫ v.left ≫ ψ := by rw [Category.assoc]
        _ = (spMap (alg.comp fst) ≫ spMap d) ≫ v.left ≫ ψ := by rw [sp, sp, dc]
        _ = _ := by rw [Category.assoc]
    have h2 : v' = 1 := by
      apply Over.OverMorphism.ext
      rw [one_left', h1, ← sp, Category.assoc, tan_left htan]
      rfl
    rw [hval, h2, tanVal_one, map_zero]
