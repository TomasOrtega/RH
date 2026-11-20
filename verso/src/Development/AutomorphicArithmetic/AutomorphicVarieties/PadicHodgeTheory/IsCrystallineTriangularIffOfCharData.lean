import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.AdmSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module Topology UpperTheory.V.Loc UpperTheory.V.U3

/- English proof (translation)
Establish `e : (((a / b) g : Bˣ) : B) * b g = a g`. Rewrite using `[← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]`. Use `(b (g * h)).mul_left_inj.1 ?_` and prove the remaining obligations. Rewrite using `[H, map_mul, Units.val_mul, ← e]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem coc {G B : Type} [Group G] [CommRing B] (a b : G →* Bˣ) (x : G → B) (g h : G)
    (H : x (g * h) * (b (g * h) : B) = (a g : B) * (x h * b h) + x g * b g * b h) :
    x (g * h) = x g + ((a / b) g : Bˣ) * x h := by
  have e : (((a / b) g : Bˣ) : B) * b g = a g := by
    rw [← Units.val_mul, MonoidHom.div_apply, div_mul_cancel]
  refine (b (g * h)).mul_left_inj.1 ?_
  rw [H, map_mul, Units.val_mul, ← e]
  ring

/- English proof (translation)
Introduce `l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π _ e ψ κ hκ x y z ρ hx hy hz hρ hcr`. Establish `hm : ∀ g h, triM (fun i => κ i (g * h)) (x (g * h)) (y (g * h)) (z (g * h)) = triM (fun i => κ i g) (x g) (y g) (z g) * triM (fun i => κ i h) (x h) (y h) (z h)` using `fun g h => by`. Rewrite using `[← hρ, ← hρ, ← hρ, map_mul, Units.val_mul]`. Establish `cx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h` using `fun g h => by`. Use `coc _ _ _ g h ?_` and prove the remaining obligations.

Use `congrFun (congrFun (hm g h) 0) 1` as an intermediate fact. Simplify `this` using `[triM, Matrix.mul_apply, Fin.sum_univ_three]`. Establish `cy : ∀ g h, y (g * h) = y g + ((κ 1 / κ 2) g : Bˣ) * y h` using `fun g h => by`. Use `coc _ _ _ g h ?_` and prove the remaining obligations. Use `congrFun (congrFun (hm g h) 1) 2` as an intermediate fact.

Simplify `this` using `[triM, Matrix.mul_apply, Fin.sum_univ_three]`. Establish `hch : ∀ i, IsCr φ (chRep (κ i))` using `fun i => crUnr φ hφ (chRep (κ i)) (contAction_chRep (hκ.cont i)) ((e : ℤ) * wt1 i) fun g hg v => by`. Rewrite using `[chRep_apply, hκ.ine g hg i, smul_eq_mul]`. Establish `hc : ContAction (colRep ρ)` using `contAction_colRep (by`. Simplify using `only [hρ]`.

Conclude with `continuous_triM (t := fun g i => κ i g) hκ.cont hx hy hz)`. Apply the tactic sequence `let f1 : (B × B) →ₗ[ℚ_[l]] (Fin 3 → B) := { toFun := fun v => ![v.1, v.2, 0] map_add' := fun v w => by ext i; fin_cases i <;> simp map_smul' := fun c v => by ext i; fin_cases i <;> simp }`. Set `f2 : (Fin 3 → B) →ₗ[ℚ_[l]] (B × B)` to `{ toFun := fun v => (v 1, v 2) map_add' := fun v w => rfl map_smul' := fun c v => rfl }`. Use `⟨(UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 0) (hκ.cont 1) x cx hx (hch 0) (hch 1)).1 ?_, (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 1) (hκ.cont 2) y cy hy (hch 1) (hch 2)).1 ?_⟩` and prove the remaining obligations. Use `((isCrys_isDR_sub_quot φ hφ _ _ (contAction_charExtension_of_continuous_cocycle (hκ.cont 0) (hκ.cont 1) cx hx) hc f1 fun g v => ?_).1 fun v w h => ?_).1 hcr` and prove the remaining obligations.

Rewrite using `[colRep_apply, hρ, characterExtensionRep_apply]`. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp [f1, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]`. Conclude with `Prod.ext (congrFun h 0) (congrFun h 1)`. Use `((isCrys_isDR_sub_quot φ hφ _ _ hc (contAction_charExtension_of_continuous_cocycle (hκ.cont 1) (hκ.cont 2) cy hy) f2 fun g v => ?_).2 fun v => ⟨![0, v.1, v.2], rfl⟩).1 hcr` and prove the remaining obligations.

Rewrite using `[colRep_apply, hρ, characterExtensionRep_apply]`. Apply the tactic sequence `ext <;> simp [f2, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]`.
-/
theorem UpperTheory.isCrystalline_triangular_iff_of_charData :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) {e : ℕ} {ψ : G →* Eˣ} {κ : Fin 3 → G →* Bˣ}, Chars φ π e ψ κ → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous x → Continuous y → Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → IsCr φ (colRep ρ) → x ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 0 / κ 1)) ∧ y ∈ UpperTheory.V.Loc.finiteCocycles φ (chRep (κ 1 / κ 2)) := by
  intro l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π _ e ψ κ hκ x y z ρ hx hy hz hρ hcr
  have hm : ∀ g h, triM (fun i => κ i (g * h)) (x (g * h)) (y (g * h)) (z (g * h)) =
      triM (fun i => κ i g) (x g) (y g) (z g) * triM (fun i => κ i h) (x h) (y h) (z h) := fun g h => by
    rw [← hρ, ← hρ, ← hρ, map_mul, Units.val_mul]
  have cx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := fun g h => by
    refine coc _ _ _ g h ?_
    have := congrFun (congrFun (hm g h) 0) 1
    simpa [triM, Matrix.mul_apply, Fin.sum_univ_three] using this
  have cy : ∀ g h, y (g * h) = y g + ((κ 1 / κ 2) g : Bˣ) * y h := fun g h => by
    refine coc _ _ _ g h ?_
    have := congrFun (congrFun (hm g h) 1) 2
    simpa [triM, Matrix.mul_apply, Fin.sum_univ_three] using this
  have hch : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ (chRep (κ i)) (contAction_chRep (hκ.cont i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hκ.ine g hg i, smul_eq_mul]
  have hc : ContAction (colRep ρ) := contAction_colRep (by
    simp only [hρ]
    exact continuous_triM (t := fun g i => κ i g) hκ.cont hx hy hz)
  let f1 : (B × B) →ₗ[ℚ_[l]] (Fin 3 → B) :=
    { toFun := fun v => ![v.1, v.2, 0]
      map_add' := fun v w => by ext i; fin_cases i <;> simp
      map_smul' := fun c v => by ext i; fin_cases i <;> simp }
  let f2 : (Fin 3 → B) →ₗ[ℚ_[l]] (B × B) :=
    { toFun := fun v => (v 1, v 2)
      map_add' := fun v w => rfl
      map_smul' := fun c v => rfl }
  refine ⟨(UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 0) (hκ.cont 1) x cx hx (hch 0) (hch 1)).1 ?_,
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ _ _ (hκ.cont 1) (hκ.cont 2) y cy hy (hch 1) (hch 2)).1 ?_⟩
  · refine ((isCrys_isDR_sub_quot φ hφ _ _ (contAction_charExtension_of_continuous_cocycle (hκ.cont 0) (hκ.cont 1) cx hx) hc f1 fun g v => ?_).1
      fun v w h => ?_).1 hcr
    · rw [colRep_apply, hρ, characterExtensionRep_apply]
      ext i
      fin_cases i <;> simp [f1, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    · exact Prod.ext (congrFun h 0) (congrFun h 1)
  · refine ((isCrys_isDR_sub_quot φ hφ _ _ hc (contAction_charExtension_of_continuous_cocycle (hκ.cont 1) (hκ.cont 2) cy hy) f2 fun g v => ?_).2
      fun v => ⟨![0, v.1, v.2], rfl⟩).1 hcr
    rw [colRep_apply, hρ, characterExtensionRep_apply]
    ext <;> simp [f2, triM, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
