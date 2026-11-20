import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

/- English proof (translation)
Establish `e₁ : A' = G₁⁻¹ * (A * G₂)` using `by rw [h₁, inv_mul_cancel_left]`. Establish `e₂ : B' = G₂⁻¹ * (B * G₃)` using `by rw [h₂, inv_mul_cancel_left]`. Establish `e₃ : C' = G₁⁻¹ * (C * G₃)` using `by rw [h₃, inv_mul_cancel_left]`. Substitute `e₁ e₂ e₃` using the available equality. Apply `Additive.ofMul.injective` to reduce the goal to its premises.

Simplify using `only [ofMul_mul, ofMul_inv]`. Normalize the expressions using the abelian group laws.
-/
theorem cocycle_defect_eq {G : Type} [CommGroup G] {A B C A' B' C' G₁ G₂ G₃ : G} (h₁ : A * G₂ = G₁ * A')
    (h₂ : B * G₃ = G₂ * B') (h₃ : C * G₃ = G₁ * C') : A * B * C⁻¹ = A' * B' * C'⁻¹ := by
  have e₁ : A' = G₁⁻¹ * (A * G₂) := by rw [h₁, inv_mul_cancel_left]
  have e₂ : B' = G₂⁻¹ * (B * G₃) := by rw [h₂, inv_mul_cancel_left]
  have e₃ : C' = G₁⁻¹ * (C * G₃) := by rw [h₃, inv_mul_cancel_left]
  subst e₁ e₂ e₃
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- English proof (translation)
Rewrite using `[mul_inv_eq_one]`. Apply `mul_right_cancel (b := R₃)` to reduce the goal to its premises. Rewrite using `[_root_.mul_assoc, h₂, h₁, h₃]`.
-/
theorem cocycle_defect_one {G : Type} [CommGroup G] {A B C R₁ R₂ R₃ : G} (h₁ : A * R₂ = R₁) (h₂ : B * R₃ = R₂)
    (h₃ : C * R₃ = R₁) : A * B * C⁻¹ = 1 := by
  rw [mul_inv_eq_one]
  apply mul_right_cancel (b := R₃)
  rw [_root_.mul_assoc, h₂, h₁, h₃]

/- English proof (translation)
Introduce `X Y p e hep hp V W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ L₁ L₂ L₃ w₁₂ w₂₃ w₁₃ r₁ r₂ r₃ h₁ h₂ h₃ hVW hVW' i₁₂ i₂₃ i₁₃ n₁₂ n₂₃ n₁₃ x a b c hx ha hb hc`. Set `O : L₁.ι × L₂.ι × L₃.ι → X.Opens` to `fun j ↦ p ⁻¹ᵁ V ⊓ (L₁.U j.1 ⊓ L₂.U j.2.1 ⊓ L₃.U j.2.2)`. Establish `mO : ∀ (j : L₁.ι × L₂.ι × L₃.ι) (z : X), z ∈ O j ↔ p z ∈ V ∧ z ∈ L₁.U j.1 ∧ z ∈ L₂.U j.2.1 ∧ z ∈ L₃.U j.2.2`. Introduce `j z`. Simplify using `only [O, TopologicalSpace.Opens.mem_inf, and_assoc]`.

Both sides reduce to the same expression. Establish `mW : ∀ z : X, p z ∈ V → (z ∈ W₁ ∧ z ∈ W₂ ∧ z ∈ W₃) ∧ z ∈ W₁₂ ∧ z ∈ W₂₃ ∧ z ∈ W₁₃`. Introduce `z hz`. Establish `e₁` using `hVW (show z ∈ p ⁻¹ᵁ V from hz)`. Establish `e₂` using `hVW' (show z ∈ p ⁻¹ᵁ V from hz)`.

Simplify using `only [TopologicalSpace.Opens.mem_inf] at e₁ e₂`. Conclude with `⟨⟨e₁.1.1, e₁.1.2, e₁.2⟩, e₂.1.1, e₂.1.2, e₂.2⟩`. Establish `l₁₂ : ∀ j, O j ≤ W₁₂ ⊓ (L₁.U j.1 ⊓ L₂.U j.2.1)` using `fun j z hz ↦ by`. Rewrite `hz` using `[mO]`. Simplify using `only [TopologicalSpace.Opens.mem_inf]`.

Conclude with `⟨(mW z hz.1).2.1, hz.2.1, hz.2.2.1⟩`. Establish `l₂₃ : ∀ j, O j ≤ W₂₃ ⊓ (L₂.U j.2.1 ⊓ L₃.U j.2.2)` using `fun j z hz ↦ by`. Rewrite `hz` using `[mO]`. Simplify using `only [TopologicalSpace.Opens.mem_inf]`. Conclude with `⟨(mW z hz.1).2.2.1, hz.2.2.1, hz.2.2.2⟩`.

Establish `l₁₃ : ∀ j, O j ≤ W₁₃ ⊓ (L₁.U j.1 ⊓ L₃.U j.2.2)` using `fun j z hz ↦ by`. Rewrite `hz` using `[mO]`. Simplify using `only [TopologicalSpace.Opens.mem_inf]`. Conclude with `⟨(mW z hz.1).2.2.2, hz.2.1, hz.2.2.2⟩`. Set `u : ∀ j, Γ(X, O j)ˣ` to `fun j ↦ res (l₁₂ j) (w₁₂ j.1 j.2.1) * res (l₂₃ j) (w₂₃ j.2.1 j.2.2) * (res (l₁₃ j) (w₁₃ j.1 j.2.2))⁻¹`.

Establish `hu : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (j : L₁.ι × L₂.ι × L₃.ι), f z ∈ O j → gm f z (O j) (u j) = gm f z _ (w₁₂ j.1 j.2.1) * gm f z _ (w₂₃ j.2.1 j.2.2) * (gm f z _ (w₁₃ j.1 j.2.2))⁻¹`. Introduce `Z f z j hz`. Simplify using `only [u, map_mul, map_inv]`. Rewrite using `[gm_res f z (l₁₂ j) hz, gm_res f z (l₂₃ j) hz, gm_res f z (l₁₃ j) hz]`. Establish `compat : ∀ i j, ∀ z ∈ O i ⊓ O j, gm (𝟙 X) z (O i) (u i) = gm (𝟙 X) z (O j) (u j)`.

Introduce `i j z hz`. Rewrite `hz` using `[TopologicalSpace.Opens.mem_inf]`. Establish `hzi` using `hz.1`. Establish `hzj` using `hz.2`. Rewrite using `[hu (𝟙 X) z i hzi, hu (𝟙 X) z j hzj]`.

Rewrite `hzi`, `hzj` using `[mO]`. Establish `hW` using `mW z hzi.1`. Conclude with `cocycle_defect_eq (i₁₂ z hW.2.1 i.1 j.1 i.2.1 j.2.1 hzi.2.1 hzj.2.1 hzi.2.2.1 hzj.2.2.1) (i₂₃ z hW.2.2.1 i.2.1 j.2.1 i.2.2 j.2.2 hzi.2.2.1 hzj.2.2.1 hzi.2.2.2 hzj.2.2.2) (i₁₃ z hW.2.2.2 i.1 j.1 i.2.2 j.2.2 hzi.2.1 hzj.2.1 hzi.2.2.2 hzj.2.2.2)`. Establish `chart : ∀ z : X, p z ∈ V → ∃ j, z ∈ O j`. Introduce `z hz`.

Establish `hW` using `mW z hz`. Take `⟨a', ha'⟩` from `h₁.cov z hW.1.1`. Take `⟨b', hb'⟩` from `h₂.cov z hW.1.2.1`. Take `⟨c', hc'⟩` from `h₃.cov z hW.1.2.2`. Conclude with `⟨(a', b', c'), (mO _ z).2 ⟨hz, ha', hb', hc'⟩⟩`.

Establish `hcov : p ⁻¹ᵁ V ≤ iSup O` using `fun z hz ↦ by`. Take `⟨j, hj⟩` from `chart z hz`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩`. Take `⟨ρ, hρ⟩` from `glue_unit (p ⁻¹ᵁ V) O (fun j ↦ inf_le_left) hcov u compat`. Set `φ` to `RingEquiv.ofBijective (p.app V).hom (hp V)`.

Set `v : Γ(Y, V)ˣ` to `Units.map φ.symm.toMonoidHom ρ`. Establish `hv : pullU p V v = ρ`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `φ.apply_symm_apply ρ.val`. Establish `hepy : ∀ y : Y, p (e y) = y` using `fun y ↦ by`.

Express the relevant statement in the definitionally equal form `(e ≫ p) y = y`. Rewrite using `[hep]`. Both sides reduce to the same expression. Establish `hρe : ∀ y : Y, y ∈ V → gm e y (p ⁻¹ᵁ V) ρ = 1`. Introduce `y hy`.

Establish `hy' : p (e y) ∈ V` using `by rw [hepy]; exact hy`. Take `⟨j, hj⟩` from `chart (e y) hy'`. Rewrite using `[← gm_res e y (inf_le_left : O j ≤ p ⁻¹ᵁ V) hj, hρ j, hu e y j hj]`. Rewrite `hj` using `[mO]`. Establish `hW` using `mW (e y) hj.1`.

Conclude with `cocycle_defect_one (n₁₂ y j.1 j.2.1 hW.2.1 hj.2.1 hj.2.2.1) (n₂₃ y j.2.1 j.2.2 hW.2.2.1 hj.2.2.1 hj.2.2.2) (n₁₃ y j.1 j.2.2 hW.2.2.2 hj.2.1 hj.2.2.2)`. Establish `hv1 : v = 1`. Apply `unit_ext` to reduce the goal to its premises. Introduce `y hy`. Rewrite using `[map_one]`.

Establish `hy' : p (e y) ∈ V` using `by rw [hepy]; exact hy`. Establish `h` using `gm_pull e p y V hy' v`. Rewrite `h` using `[hep, hv]`. Rewrite using `[← h]`. Conclude with `hρe y hy`.

Establish `hρ1 : ρ = 1` using `by rw [← hv, hv1, map_one]`. Establish `hxO : x ∈ O (a, b, c)` using `(mO _ x).2 ⟨hx, ha, hb, hc⟩`. Establish `h` using `hu (𝟙 X) x (a, b, c) hxO`. Rewrite `h` using `[← hρ, hρ1, map_one, map_one]`. Conclude with `(mul_inv_eq_one.1 h.symm)`.
-/
theorem norm_cocycle : ∀ (X Y : Scheme.{0}) (p : X ⟶ Y) (e : Y ⟶ X), e ≫ p = 𝟙 Y → FnBij p → ∀ (V : Y.Opens) (W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ : X.Opens) (L₁ L₂ L₃ : LB X) (w₁₂ : Cmp W₁₂ L₁ L₂) (w₂₃ : Cmp W₂₃ L₂ L₃) (w₁₃ : Cmp W₁₃ L₁ L₃) (r₁ : RigD e L₁) (r₂ : RigD e L₂) (r₃ : RigD e L₃), IsOn W₁ L₁ → IsOn W₂ L₂ → IsOn W₃ L₃ → p ⁻¹ᵁ V ≤ W₁ ⊓ W₂ ⊓ W₃ → p ⁻¹ᵁ V ≤ W₁₂ ⊓ W₂₃ ⊓ W₁₃ → IsoOn W₁₂ L₁ L₂ w₁₂ → IsoOn W₂₃ L₂ L₃ w₂₃ → IsoOn W₁₃ L₁ L₃ w₁₃ → Norm e W₁₂ L₁ L₂ w₁₂ r₁ r₂ → Norm e W₂₃ L₂ L₃ w₂₃ r₂ r₃ → Norm e W₁₃ L₁ L₃ w₁₃ r₁ r₃ → ∀ (x : X) (a : L₁.ι) (b : L₂.ι) (c : L₃.ι), p x ∈ V → x ∈ L₁.U a → x ∈ L₂.U b → x ∈ L₃.U c → gm (𝟙 X) x _ (w₁₂ a b) * gm (𝟙 X) x _ (w₂₃ b c) = gm (𝟙 X) x _ (w₁₃ a c) := by
  intro X Y p e hep hp V W₁ W₂ W₃ W₁₂ W₂₃ W₁₃ L₁ L₂ L₃ w₁₂ w₂₃ w₁₃ r₁ r₂ r₃ h₁ h₂ h₃ hVW hVW' i₁₂ i₂₃ i₁₃
    n₁₂ n₂₃ n₁₃ x a b c hx ha hb hc
  let O : L₁.ι × L₂.ι × L₃.ι → X.Opens := fun j ↦ p ⁻¹ᵁ V ⊓ (L₁.U j.1 ⊓ L₂.U j.2.1 ⊓ L₃.U j.2.2)
  have mO : ∀ (j : L₁.ι × L₂.ι × L₃.ι) (z : X),
      z ∈ O j ↔ p z ∈ V ∧ z ∈ L₁.U j.1 ∧ z ∈ L₂.U j.2.1 ∧ z ∈ L₃.U j.2.2 := by
    intro j z
    simp only [O, TopologicalSpace.Opens.mem_inf, and_assoc]
    rfl
  have mW : ∀ z : X, p z ∈ V → (z ∈ W₁ ∧ z ∈ W₂ ∧ z ∈ W₃) ∧ z ∈ W₁₂ ∧ z ∈ W₂₃ ∧ z ∈ W₁₃ := by
    intro z hz
    have e₁ := hVW (show z ∈ p ⁻¹ᵁ V from hz)
    have e₂ := hVW' (show z ∈ p ⁻¹ᵁ V from hz)
    simp only [TopologicalSpace.Opens.mem_inf] at e₁ e₂
    exact ⟨⟨e₁.1.1, e₁.1.2, e₁.2⟩, e₂.1.1, e₂.1.2, e₂.2⟩
  have l₁₂ : ∀ j, O j ≤ W₁₂ ⊓ (L₁.U j.1 ⊓ L₂.U j.2.1) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.1, hz.2.1, hz.2.2.1⟩
  have l₂₃ : ∀ j, O j ≤ W₂₃ ⊓ (L₂.U j.2.1 ⊓ L₃.U j.2.2) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.2.1, hz.2.2.1, hz.2.2.2⟩
  have l₁₃ : ∀ j, O j ≤ W₁₃ ⊓ (L₁.U j.1 ⊓ L₃.U j.2.2) := fun j z hz ↦ by
    rw [mO] at hz
    simp only [TopologicalSpace.Opens.mem_inf]
    exact ⟨(mW z hz.1).2.2.2, hz.2.1, hz.2.2.2⟩
  let u : ∀ j, Γ(X, O j)ˣ := fun j ↦
    res (l₁₂ j) (w₁₂ j.1 j.2.1) * res (l₂₃ j) (w₂₃ j.2.1 j.2.2) * (res (l₁₃ j) (w₁₃ j.1 j.2.2))⁻¹
  have hu : ∀ {Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) (j : L₁.ι × L₂.ι × L₃.ι), f z ∈ O j →
      gm f z (O j) (u j) = gm f z _ (w₁₂ j.1 j.2.1) * gm f z _ (w₂₃ j.2.1 j.2.2) * (gm f z _ (w₁₃ j.1 j.2.2))⁻¹ := by
    intro Z f z j hz
    simp only [u, map_mul, map_inv]
    rw [gm_res f z (l₁₂ j) hz, gm_res f z (l₂₃ j) hz, gm_res f z (l₁₃ j) hz]
  have compat : ∀ i j, ∀ z ∈ O i ⊓ O j, gm (𝟙 X) z (O i) (u i) = gm (𝟙 X) z (O j) (u j) := by
    intro i j z hz
    rw [TopologicalSpace.Opens.mem_inf] at hz
    have hzi := hz.1
    have hzj := hz.2
    rw [hu (𝟙 X) z i hzi, hu (𝟙 X) z j hzj]
    rw [mO] at hzi hzj
    have hW := mW z hzi.1
    exact cocycle_defect_eq (i₁₂ z hW.2.1 i.1 j.1 i.2.1 j.2.1 hzi.2.1 hzj.2.1 hzi.2.2.1 hzj.2.2.1)
      (i₂₃ z hW.2.2.1 i.2.1 j.2.1 i.2.2 j.2.2 hzi.2.2.1 hzj.2.2.1 hzi.2.2.2 hzj.2.2.2)
      (i₁₃ z hW.2.2.2 i.1 j.1 i.2.2 j.2.2 hzi.2.1 hzj.2.1 hzi.2.2.2 hzj.2.2.2)
  have chart : ∀ z : X, p z ∈ V → ∃ j, z ∈ O j := by
    intro z hz
    have hW := mW z hz
    obtain ⟨a', ha'⟩ := h₁.cov z hW.1.1
    obtain ⟨b', hb'⟩ := h₂.cov z hW.1.2.1
    obtain ⟨c', hc'⟩ := h₃.cov z hW.1.2.2
    exact ⟨(a', b', c'), (mO _ z).2 ⟨hz, ha', hb', hc'⟩⟩
  have hcov : p ⁻¹ᵁ V ≤ iSup O := fun z hz ↦ by
    obtain ⟨j, hj⟩ := chart z hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨ρ, hρ⟩ := glue_unit (p ⁻¹ᵁ V) O (fun j ↦ inf_le_left) hcov u compat

  let φ := RingEquiv.ofBijective (p.app V).hom (hp V)
  let v : Γ(Y, V)ˣ := Units.map φ.symm.toMonoidHom ρ
  have hv : pullU p V v = ρ := by
    apply Units.ext
    exact φ.apply_symm_apply ρ.val

  have hepy : ∀ y : Y, p (e y) = y := fun y ↦ by
    change (e ≫ p) y = y
    rw [hep]
    rfl
  have hρe : ∀ y : Y, y ∈ V → gm e y (p ⁻¹ᵁ V) ρ = 1 := by
    intro y hy
    have hy' : p (e y) ∈ V := by rw [hepy]; exact hy
    obtain ⟨j, hj⟩ := chart (e y) hy'
    rw [← gm_res e y (inf_le_left : O j ≤ p ⁻¹ᵁ V) hj, hρ j, hu e y j hj]
    rw [mO] at hj
    have hW := mW (e y) hj.1
    exact cocycle_defect_one (n₁₂ y j.1 j.2.1 hW.2.1 hj.2.1 hj.2.2.1) (n₂₃ y j.2.1 j.2.2 hW.2.2.1 hj.2.2.1 hj.2.2.2)
      (n₁₃ y j.1 j.2.2 hW.2.2.2 hj.2.1 hj.2.2.2)
  have hv1 : v = 1 := by
    apply unit_ext
    intro y hy
    rw [map_one]
    have hy' : p (e y) ∈ V := by rw [hepy]; exact hy
    have h := gm_pull e p y V hy' v
    rw [hep, hv] at h
    rw [← h]
    exact hρe y hy
  have hρ1 : ρ = 1 := by rw [← hv, hv1, map_one]

  have hxO : x ∈ O (a, b, c) := (mO _ x).2 ⟨hx, ha, hb, hc⟩
  have h := hu (𝟙 X) x (a, b, c) hxO
  rw [← hρ, hρ1, map_one, map_one] at h
  exact (mul_inv_eq_one.1 h.symm)

end GlobalTheory.PicGlue
