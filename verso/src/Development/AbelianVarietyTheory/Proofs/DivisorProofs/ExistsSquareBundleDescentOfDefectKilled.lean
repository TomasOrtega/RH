import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot
open GlobalTheory.LBDescent GlobalTheory.DescNorm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SqDatum

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => by simpa using Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => by simpa using h⟩`.
-/
theorem mem_lbPow_U {X : Scheme.{0}} {M : LB X} {n : ℕ} {x : X} {i : PUnit → M.ι} :
    x ∈ (lbPow M n).U i ↔ x ∈ M.U (i PUnit.unit) :=
  ⟨fun h => by simpa using Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => by simpa using h⟩

/- English proof (translation)
Introduce `_ h` and use `mem_lbPow_U.1 h`.
-/
theorem lbPow_U_le {X : Scheme.{0}} (M : LB X) (n : ℕ) (i : PUnit → M.ι) :
    (lbPow M n).U i ≤ M.U (i PUnit.unit) := fun _ h => mem_lbPow_U.1 h

/- English proof (translation)
The claim follows from `inf_le_inf (Scheme.Hom.preimage_mono _ (lbPow_U_le M n i)) (Scheme.Hom.preimage_mono _ (lbPow_U_le M n j))`.
-/
theorem chart_le {X Y : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (n : ℕ) (i j : PUnit → M.ι) :
    chart f (lbPow M n) i j ≤ chart f M (i PUnit.unit) (j PUnit.unit) :=
  inf_le_inf (Scheme.Hom.preimage_mono _ (lbPow_U_le M n i)) (Scheme.Hom.preimage_mono _ (lbPow_U_le M n j))

/- English proof (translation)
Use `show gm p z _ (∏ _k : PUnit, (res _ (pullU (𝟙 X) _ (M.g (i PUnit.unit) (i' PUnit.unit)))) ^ ((n : ℕ) : ℤ)) = _`. Rewrite using `[Fintype.prod_unique, map_zpow, zpow_natCast]`. Use `congr 1`. Use `(gm_res p z _ (show p z ∈ LB.wchart M (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart M (fun _ : PUnit => 𝟙 X) i' from ⟨(mem_lbPow_U (n := n)).2 hi, (mem_lbPow_U (n := n)).2 hi'⟩) _).trans ?_` and prove the remaining obligations. Use `(gm_pull p (𝟙 X) z _ (by simpa using And.intro hi hi') _).trans ?_` and prove the remaining obligations.

Rewrite using `[Category.comp_id]`.
-/
theorem gm_lbPow_g {X Z : Scheme.{0}} (M : LB X) (n : ℕ) (p : Z ⟶ X) (z : Z) (i i' : PUnit → M.ι)
    (hi : p z ∈ M.U (i PUnit.unit)) (hi' : p z ∈ M.U (i' PUnit.unit)) :
    gm p z _ ((lbPow M n).g i i') = gm p z _ (M.g (i PUnit.unit) (i' PUnit.unit)) ^ n := by
  show gm p z _ (∏ _k : PUnit, (res _ (pullU (𝟙 X) _ (M.g (i PUnit.unit) (i' PUnit.unit)))) ^ ((n : ℕ) : ℤ)) = _
  rw [Fintype.prod_unique, map_zpow, zpow_natCast]
  congr 1
  refine (gm_res p z _ (show p z ∈ LB.wchart M (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart M (fun _ : PUnit => 𝟙 X) i' from
    ⟨(mem_lbPow_U (n := n)).2 hi, (mem_lbPow_U (n := n)).2 hi'⟩) _).trans ?_
  refine (gm_pull p (𝟙 X) z _ (by simpa using And.intro hi hi') _).trans ?_
  rw [Category.comp_id]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[gm_val _ w ⊤ trivial, gm_val _ w ⊤ trivial]`. Simplify using `[GlobalTheory.CharKer.pullTop]`. Both sides reduce to the same expression.
-/
theorem gm_pullTop {X Y : Scheme.{0}} (p : X ⟶ Y) (w : X) (u : Γ(Y, ⊤)ˣ) :
    gm (𝟙 X) w ⊤ (GlobalTheory.CharKer.pullTop p u) = gm p w ⊤ u := by
  apply Units.ext
  rw [gm_val _ w ⊤ trivial, gm_val _ w ⊤ trivial]
  simp [GlobalTheory.CharKer.pullTop]
  rfl

end GlobalTheory.SqDatum

namespace GlobalTheory.SqDatum

/- English proof (translation)
Rewrite using `[← h₂]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem commGroup_mul_eq_mul_mul_div {G : Type*} [CommGroup G] (a b c d x y z : G) (h₁ : d * c = a * b) (h₂ : d ^ 2 * x * y = z) :
    (a ^ 2 * x) * (b ^ 2 * y) = c ^ 2 * z := by
  rw [← h₂]
  calc (a ^ 2 * x) * (b ^ 2 * y) = (a * b) ^ 2 * x * y := by simp only [mul_pow]; ac_rfl
    _ = (d * c) ^ 2 * x * y := by rw [h₁]
    _ = c ^ 2 * (d ^ 2 * x * y) := by simp only [mul_pow]; ac_rfl

def psi {X Y : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ)
    (u : Γ(pullback f f, ⊤)ˣ) : ∀ i j, Γ(pullback f f, chart f (lbPow M 2) i j)ˣ :=
  fun i j => res (chart_le f M 2 i j) (φ (i PUnit.unit) (j PUnit.unit)) ^ 2 * res le_top u

/- English proof (translation)
Simplify using `only [psi]`. Rewrite using `[map_mul, map_pow, gm_res p z _ h, gm_res p z _ h]`.
-/
theorem gm_psi {X Y Z : Scheme.{0}} (f : X ⟶ Y) (M : LB X) (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ)
    (u : Γ(pullback f f, ⊤)ˣ) (p : Z ⟶ pullback f f) (z : Z) (i j : PUnit → M.ι)
    (h : p z ∈ chart f (lbPow M 2) i j) :
    gm p z _ (psi f M φ u i j) = gm p z _ (φ (i PUnit.unit) (j PUnit.unit)) ^ 2 * gm p z ⊤ u := by
  dsimp only [psi]
  rw [map_mul, map_pow, gm_res p z _ h, gm_res p z _ h]

/- English proof (translation)
Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]`.
-/
theorem pullback_fst_snd_triple_eq_snd_fst {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) =
      pullback.snd f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]

/- English proof (translation)
Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pr13, pullback.lift_fst]`.
-/
theorem pullback_fst_tripleFibreProductProjOneThree {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.fst f f (pr13 f w) = pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pr13, pullback.lift_fst]

/- English proof (translation)
Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pr13, pullback.lift_snd]`.
-/
theorem pullback_snd_tripleFibreProductProjOneThree {X Y : Scheme.{0}} (f : X ⟶ Y) (w : Triple f) :
    pullback.snd f f (pr13 f w) = pullback.snd f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pr13, pullback.lift_snd]

/- English proof (translation)
Introduce `X Y f M hM φ D u hC hD hK`. Establish `h₂ : (lbPow M 2).IsLB` using `LB.isLB_linComb hM _ _`. Use `⟨lbPow M 2, psi f M φ u, h₂, GlobalTheory.lbIso_refl h₂, ?_, ?_⟩` and prove the remaining obligations. Introduce `z i i' j j' hi hi' hj hj'`. Rewrite using `[gm_psi f M φ u (𝟙 _) z i' j' ⟨hi', hj'⟩, gm_psi f M φ u (𝟙 _) z i j ⟨hi, hj⟩, gm_lbPow_g M 2 _ z i i' (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hi'), gm_lbPow_g M 2 _ z j' j (mem_lbPow_U.1 hj') (mem_lbPow_U.1 hj), hC z _ _ _ _ (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hi') (mem_lbPow_U.1 hj) (m …`.

Simplify using `only [mul_pow]`. The two sides agree by associativity and commutativity. Introduce `w i j k hi hj hk`. Establish `hj' : pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) ∈ (lbPow M 2).U j`. Rewrite using `[pullback_fst_snd_triple_eq_snd_fst]`.

Conclude with `hj`. Establish `h13 : pr13 f w ∈ chart f (lbPow M 2) i k`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(show pullback.fst f f (pr13 f w) ∈ (lbPow M 2).U i by rw [pullback_fst_tripleFibreProductProjOneThree]; exact hi)`. Conclude with `(show pullback.snd f f (pr13 f w) ∈ (lbPow M 2).U k by rw [pullback_snd_tripleFibreProductProjOneThree]; exact hk)`.

Rewrite using `[gm_psi f M φ u _ w i j ⟨hi, hj⟩, gm_psi f M φ u _ w j k ⟨hj', hk⟩, gm_psi f M φ u _ w i k h13]`. Establish `hd` using `hD (Triple f) (𝟙 _) w (i PUnit.unit) (j PUnit.unit) (k PUnit.unit) (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hj) (mem_lbPow_U.1 hk)`. Simplify using `only [Category.id_comp] at hd`. Establish `hk'` using `congrArg (gm (𝟙 _) w ⊤) hK`. Simplify using `only [map_mul, map_pow, gm_pullTop] at hk'`.

Conclude with `commGroup_mul_eq_mul_mul_div _ _ _ _ _ _ _ hd hk'`.
-/
theorem exists_sq_descent : ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (M : LB X), M.IsLB →
    ∀ (φ : ∀ i j, Γ(pullback f f, chart f M i j)ˣ) (D : Γ(Triple f, ⊤)ˣ) (u : Γ(pullback f f, ⊤)ˣ),
    DescCompat f M φ → Defect f M φ D → KillsSq f D u →
    ∃ (M₂ : LB X) (ψ : ∀ i j, Γ(pullback f f, chart f M₂ i j)ˣ),
      M₂.IsLB ∧ LBIso (lbPow M 2) M₂ ∧ DescCompat f M₂ ψ ∧ DescCocycle f M₂ ψ := by
  intro X Y f M hM φ D u hC hD hK
  have h₂ : (lbPow M 2).IsLB := LB.isLB_linComb hM _ _
  refine ⟨lbPow M 2, psi f M φ u, h₂, GlobalTheory.lbIso_refl h₂, ?_, ?_⟩
  · intro z i i' j j' hi hi' hj hj'
    rw [gm_psi f M φ u (𝟙 _) z i' j' ⟨hi', hj'⟩, gm_psi f M φ u (𝟙 _) z i j ⟨hi, hj⟩,
      gm_lbPow_g M 2 _ z i i' (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hi'),
      gm_lbPow_g M 2 _ z j' j (mem_lbPow_U.1 hj') (mem_lbPow_U.1 hj),
      hC z _ _ _ _ (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hi') (mem_lbPow_U.1 hj) (mem_lbPow_U.1 hj')]
    simp only [mul_pow]
    ac_rfl
  · intro w i j k hi hj hk
    have hj' : pullback.fst f f (pullback.snd (pullback.snd f f) (pullback.fst f f) w) ∈ (lbPow M 2).U j := by
      rw [pullback_fst_snd_triple_eq_snd_fst]; exact hj
    have h13 : pr13 f w ∈ chart f (lbPow M 2) i k := by
      refine ⟨?_, ?_⟩
      · exact (show pullback.fst f f (pr13 f w) ∈ (lbPow M 2).U i by rw [pullback_fst_tripleFibreProductProjOneThree]; exact hi)
      · exact (show pullback.snd f f (pr13 f w) ∈ (lbPow M 2).U k by rw [pullback_snd_tripleFibreProductProjOneThree]; exact hk)
    rw [gm_psi f M φ u _ w i j ⟨hi, hj⟩, gm_psi f M φ u _ w j k ⟨hj', hk⟩, gm_psi f M φ u _ w i k h13]
    have hd := hD (Triple f) (𝟙 _) w (i PUnit.unit) (j PUnit.unit) (k PUnit.unit)
      (mem_lbPow_U.1 hi) (mem_lbPow_U.1 hj) (mem_lbPow_U.1 hk)
    simp only [Category.id_comp] at hd
    have hk' := congrArg (gm (𝟙 _) w ⊤) hK
    simp only [map_mul, map_pow, gm_pullTop] at hk'
    exact commGroup_mul_eq_mul_mul_div _ _ _ _ _ _ _ hd hk'

end GlobalTheory.SqDatum
