import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HeatConn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatConn

/- English proof (translation)
Establish `e` using `congrArg δ (congrArg Units.val hu)`. Simplify using `only [Units.val_mul, hδ, h₁, h₂, h₃, ht] at e`. Establish `hπ` using `congrArg π (congrArg Units.val hu)`. Simplify using `only [Units.val_mul, map_mul] at hπ`. Establish `hunit : IsUnit (π u₃ * π t)` using `by simpa only [Units.val_mul, map_mul] using (u₃ * t).isUnit.map π`.

Apply `hunit.mul_left_cancel` to reduce the goal to its premises. Take the linear combination `e - (k₁ + k₂) * hπ`.
-/
theorem dlog_const_add {S S' : Type} [CommRing S] [CommRing S'] (π : S →+* S') (δ : S → S')
    (hδ : ∀ x y, δ (x * y) = π x * δ y + π y * δ x) (u₁ u₂ u₃ t : Sˣ) (hu : u₃ * t = u₁ * u₂)
    (k₁ k₂ k₃ : S') (h₁ : δ u₁ = π u₁ * k₁) (h₂ : δ u₂ = π u₂ * k₂) (h₃ : δ u₃ = π u₃ * k₃) (ht : δ t = 0) :
    k₃ = k₁ + k₂ := by
  have e := congrArg δ (congrArg Units.val hu)
  simp only [Units.val_mul, hδ, h₁, h₂, h₃, ht] at e
  have hπ := congrArg π (congrArg Units.val hu)
  simp only [Units.val_mul, map_mul] at hπ
  have hunit : IsUnit (π u₃ * π t) := by simpa only [Units.val_mul, map_mul] using (u₃ * t).isUnit.map π
  apply hunit.mul_left_cancel
  linear_combination e - (k₁ + k₂) * hπ

/- English proof (translation)
Introduce `R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD hCm α β c₁ c₂ c₃ H₁ H₂ H₃`. Take `⟨hd, hcov, hV, -⟩` from `hC`. Establish `P` using `hF.pull.1`. Set `z : Sp K` to `IsLocalRing.closedPoint K`. Set `a : Sp K ⟶ Y.H.left` to `spMap φ ≫ η[Y.H].left`.

Establish `hb : (spMap φ ≫ η[Q.P.A].left) ≫ Q.P.A.hom = 𝟙 (Sp K) ≫ spMap φ`. Rewrite using `[Category.assoc, Over.w η[Q.P.A], Category.id_comp]`. Both sides reduce to the same expression. Set `b : Sp K ⟶ A₀.left` to `P.lift _ _ hb`. Establish `hbm : b ≫ m₀ = spMap φ ≫ η[Q.P.A].left` using `P.lift_fst _ _ _`.

Establish `hbA : b ≫ A₀.hom = 𝟙 _` using `P.lift_snd _ _ _`. Establish `w : a ≫ Y.q.left = b ≫ m₀`. Use `Y.q_linear.isMonHom` as an intermediate fact. Rewrite using `[hbm, Category.assoc, ← Over.comp_left, IsMonHom.one_hom]`. Establish `hA3 : ∀ χ : Q.X, η[Q.P.A].left ≫ Q.famφB χ 3 = η[Q.P.A].left` using `fun χ => by`.

Express the relevant statement in the definitionally equal form `η[Q.P.A].left ≫ (toUnit Q.P.A ≫ η[Q.P.A]).left = _`. Rewrite using `[← Over.comp_left, ← Category.assoc, toUnit_unique (η[Q.P.A] ≫ toUnit Q.P.A) (𝟙 _), Category.id_comp]`. Establish `hA12 : ∀ χ : Q.X, η[Q.P.A].left ≫ Q.famφB χ 1 = η[Q.P.A].left ≫ Q.famφB χ 2` using `fun χ => by`. Express the relevant statement in the definitionally equal form `η[Q.P.A].left ≫ (padd Q.P.A (𝟙 Q.P.A) (toUnit _ ≫ Q.c χ)).left = η[Q.P.A].left ≫ (toUnit Q.P.A ≫ Q.c χ).left`. Rewrite using `[← Over.comp_left, ← Over.comp_left]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `η[Q.P.A] ≫ (𝟙 Q.P.A * (toUnit _ ≫ Q.c χ)) = _`. Rewrite using `[MonObj.comp_mul, Category.comp_id, ← Category.assoc η[Q.P.A] (toUnit _), toUnit_unique (η[Q.P.A] ≫ toUnit Q.P.A) (𝟙 _), Category.id_comp]`. Establish `e1 : (η[Q.P.A] : 𝟙_ _ ⟶ Q.P.A) = 1` using `by rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]`. Rewrite using `[e1, _root_.one_mul]`.

Establish `hTb : ∀ (χ : Q.X) (j : Fin 4) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ j → T' ≫ A₀.hom = A₀.hom → b ≫ T' ≫ m₀ = spMap φ ≫ η[Q.P.A].left ≫ Q.famφB χ j` using `fun χ j T' h₁ _ => by`. Rewrite using `[h₁, reassoc_of% hbm]`. Establish `e3 : ∀ (χ : Q.X) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ 3 → T' ≫ A₀.hom = A₀.hom → b ≫ T' = b` using `fun χ T' h₁ h₂ => P.hom_ext (by rw [Category.assoc, hTb χ 3 T' h₁ h₂, hA3, hbm]) (by rw [Category.assoc, h₂])`. Establish `e0 : ∀ (χ : Q.X) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ 0 → T' ≫ A₀.hom = A₀.hom → b ≫ T' = b` using `fun χ T' h₁ h₂ => by rw [hF.T_zero h₁ h₂, Category.comp_id]`. Establish `e12 : ∀ (χ : Q.X) (T₁ T₂ : A₀.left ⟶ A₀.left), T₁ ≫ m₀ = m₀ ≫ Q.famφB χ 1 → T₁ ≫ A₀.hom = A₀.hom → T₂ ≫ m₀ = m₀ ≫ Q.famφB χ 2 → T₂ ≫ A₀.hom = A₀.hom → b ≫ T₁ = b ≫ T₂` using `fun χ T₁ T₂ h₁ h₂ h₃ h₄ => P.hom_ext (by rw [Category.assoc, Category.assoc, hTb χ 1 T₁ h₁ h₂, hTb χ 2 T₂ h₃ h₄, hA12]) (by rw [Category.assoc, Category.assoc, h₂, h₄])`.

Establish `hcov' : ∀ p : Q.P.A.left, ∃ i, p ∈ V i` using `fun p => by`. Establish `: p ∈ (⨆ i, V i)` using `by rw [hcov]; trivial`. Conclude with `TopologicalSpace.Opens.mem_iSup.1 this`. Use `choose I hI using hcov'`. Set `p₀ : Q.P.A.left` to `(b ≫ m₀) z`.

Set `i₀ : h.J` to `I p₀`. Set `y : Y.H.left` to `a z`. Establish `hy : Y.q.left y = p₀`. Express the relevant statement in the definitionally equal form `(a ≫ Y.q.left) z = _`. Rewrite using `[w]`.

Establish `h₀ : a z ∈ h.W i₀`. Rewrite using `[hD.1 i₀]`. Express the relevant statement in the definitionally equal form `Y.q.left y ∈ V i₀`. Rewrite using `[hy]`. Conclude with `hI p₀`.

Take `⟨δ, -, δmul, δeq⟩` from `exists_stalkDer_field (isField_dE h ν hF.field i₀) a z h₀`. Set `π` to `(a.stalkMap z).hom`. Set `g` to `Y.Φ Y.H (𝟙 _)`. Set `J : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι` to `fun ψ => h.j (I (ψ y))`. Establish `hJ : Good Q.P.L y J` using `fun ψ => hV _ (hI _)`.

Establish `key : ∀ (χ : Q.X) (c : K), CoordEq Y h ν m₀ V pb χ c → δ (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val = π (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val * cst (b ≫ A₀.hom) z c`. Introduce `χ c Hc`. Take `⟨T, hT1, hT2⟩` from `hF.exists_strictHenselian_absolutely_closed_local_ring χ`. Establish `f0` using `e0 χ (T 0) (hT1 0) (hT2 0)`. Establish `f3` using `e3 χ (T 3) (hT1 3) (hT2 3)`.

Establish `f12` using `e12 χ (T 1) (T 2) (hT1 1) (hT2 1) (hT1 2) (hT2 2)`. Set `i₁ : h.J` to `I (((b ≫ T 1) ≫ m₀) z)`. Set `i : Fin 4 → h.J` to `![i₀, i₁, i₁, i₀]`. Establish `hpt : ∀ j, (b ≫ T j ≫ m₀) z = Q.famφB χ j p₀` using `fun j => by`. Rewrite using `[hT1 j, ← Category.assoc]`.

Both sides reduce to the same expression. Establish `hIi : ∀ j, I ((b ≫ T j ≫ m₀) z) = i j`. Introduce `j`. Use `fin_cases j`. Use `show I ((b ≫ T 0 ≫ m₀) z) = i₀`.

Rewrite using `[← Category.assoc, f0]`. Use `show I ((b ≫ T 1 ≫ m₀) z) = i₁`. Rewrite using `[← Category.assoc]`. Use `show I ((b ≫ T 2 ≫ m₀) z) = i₁`. Rewrite using `[← Category.assoc, ← f12]`.

Use `show I ((b ≫ T 3 ≫ m₀) z) = i₀`. Rewrite using `[← Category.assoc, f3]`. Establish `hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j)` using `fun j => hIi j ▸ hI _`. Establish `Hc'` using `Hc T hT1 hT2 (Sp K) a b w z i hi`. Establish `hm` using `hF.mem_chart hD hV hT1 w hi`.

Unfold `CoordAt at Hc'`. Establish `hP : ∀ w' : (Sp K).presheaf.stalk z, - gs (b ≫ T 0) z (m₀ ⁻¹ᵁ V (i 0)) (pb (i 0)) + gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V (i 1)) (pb (i 1)) - gs (b ≫ T 2) z (m₀ ⁻¹ᵁ V (i 2)) (pb (i 2)) + gs (b ≫ T 3) z (m₀ ⁻¹ᵁ V (i 3)) (pb (i 3)) + w' = w'`. Introduce `w'`. Rewrite using `[f0, f3, ← f12]`. Use `show - gs b z (m₀ ⁻¹ᵁ V i₀) (pb i₀) + gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V i₁) (pb i₁) - gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V i₁) (pb i₁) + gs b z (m₀ ⁻¹ᵁ V i₀) (pb i₀) + w' = w'`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `Hc'` using `[hP]`. Establish `hcv : (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val = gs (𝟙 _) y (xU Y χ fun j => h.j (i j)) (xc Y χ fun j => h.j (i j)).val`. Rewrite using `[gs_unit (𝟙 _) y _ hm.2]`. Use `congr 1`.

Use `val_of _ _ _ _ _ fun k => ?_` and prove the remaining obligations. Use `show h.j (I ((𝟙 _ ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b χ k) y)) = h.j (i (![1, 2, 0, 3] k))`. Rewrite using `[Category.id_comp, gtφT_eq, ← hIi, hpt]`. Use `show h.j (I (Q.famφB χ _ (Y.q.left y))) = _`. Rewrite using `[hy]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcv, GlobalTheory.KS.DlogPol.gs_rsT (𝟙 Y.H.left) y (O := h.W i₀ ⊓ xU Y χ fun j => h.j (i j)) inf_le_right hm]`. Use `_ = gs a z (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)) (dE h ν i₀ _ (rsT (xc Y χ fun j => h.j (i j)).val (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)))) := δeq _ inf_le_left hm _`. Use `_ = gs a z (xU Y χ fun j => h.j (i j)) (xc Y χ fun j => h.j (i j)).val * cst (b ≫ A₀.hom) z c := Hc'`. Use `_ = _ := by rw [gs_stalkMap a z _ hm.2, ← hcv]`.

Establish `hθ : δ (ReciprocityTheory.ChartRestriction.G.DVR.th Q y J (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H α) (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H β) (Y.Φ Y.H (𝟙 _)).b).val = 0`. Set `Λ : Q.P.A ⟶ Q.P.A ⊗ (Q.P.A ⊗ Q.P.A)` to `lift (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A α) (lift (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A β) (𝟙 _))`. Set `G` to `LB.pullGen Q.P.L (thφ Q.P.A (x3 Q.P.A)) thε Q.cub.t Λ.left`. Establish `a1 : ∀ χ, Y.q ≫ ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A χ = ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H χ` using `fun χ => by`. Simplify using `only [ReciprocityTheory.ChartRestriction.G.DVR.cP, comp_toUnit_assoc]`.

Establish `e₁ : ReciprocityTheory.ChartRestriction.G.DVR.th Q y J (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H α) (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H β) (Y.Φ Y.H (𝟙 _)).b = val G Y.q.left y J`. Use `Eq.trans ?_ (val_cub Q.cub Y.q hJ _ _ _).symm` and prove the remaining obligations. Rewrite using `[a1, a1, Category.comp_id]`. Both sides reduce to the same expression. Set `j₀` to `fun k => J (Y.q.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k)`.

Set `Wc` to `LB.wchart Q.P.L (fun k => Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) j₀`. Set `θ₀ : Γ(Q.P.A.left, Wc)ˣ` to `G.s j₀`. Establish `hWc : Y.q.left y ∈ Wc` using `hJ.mem _ Y.q.left`. Establish `hp₀W : p₀ ∈ Wc` using `hy ▸ hWc`. Set `U : Q.P.A.left.Opens` to `V i₀ ⊓ Wc`.

Establish `hp₀U : p₀ ∈ U` using `⟨hI p₀, hp₀W⟩`. Establish `hyU : Y.q.left y ∈ U` using `hy ▸ hp₀U`. Set `f : Γ(Q.P.A.left, U)` to `resG Q.P.A.left (inf_le_right : U ≤ Wc) θ₀.val`. Establish `s1 : (val G Y.q.left y J).val = gs (𝟙 _) y (Y.q.left ⁻¹ᵁ U) ((Y.q.left.app U).hom f)`. Rewrite using `[gs_pull (𝟙 _) Y.q.left y U hyU f, Category.id_comp, gs_res Y.q.left y inf_le_right hyU]`.

Conclude with `(gs_unit _ _ _ hWc _).symm`. Establish `hle : Y.q.left ⁻¹ᵁ U ≤ h.W i₀`. Rewrite using `[hD.1 i₀]`. Conclude with `fun x hx => hx.1`. Establish `s2` using `δeq (Y.q.left ⁻¹ᵁ U) hle hyU ((Y.q.left.app U).hom f)`.

Establish `s3` using `hD.2.1 (Sp K) a b w z i₀ U inf_le_left hp₀U f`. Take `⟨T, hT1, hT2⟩` from `hF.exists_strictHenselian_absolutely_closed_local_ring α`. Establish `f3` using `e3 α (T 3) (hT1 3) (hT2 3)`. Establish `hmem3 : (b ≫ T 3 ≫ m₀) z ∈ U` using `by rw [← Category.assoc, f3]; exact hp₀U`. Establish `s4` using `hCm α 3 (T 3) (hT1 3) (hT2 3) U f (Sp K) b z hmem3`.

Rewrite `s4` using `[f3]`. Establish `hfix : Q.famφB α 3 p₀ = p₀`. Establish `: (b ≫ T 3 ≫ m₀) z = Q.famφB α 3 p₀` using `by rw [hT1 3, ← Category.assoc]; rfl`. Rewrite using `[← this, ← Category.assoc, f3]`. Take `⟨δ', -, δ'mul, δ'eq⟩` from `exists_stalkDer_along hd b z`.

Establish `hc3 : (b ≫ m₀) z ∈ Q.famφB α 3 ⁻¹ᵁ U` using `by show Q.famφB α 3 p₀ ∈ U; rw [hfix]; exact hp₀U`. Establish `s5` using `δ'eq _ hc3 ((Q.famφB α 3).app U |>.hom f)`. Set `C3 : Q.P.A ⟶ Q.P.A` to `toUnit Q.P.A ≫ η[Q.P.A]`. Set `J' : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι` to `fun ψ => h.j (I (ψ p₀))`. Establish `hJ' : Good Q.P.L p₀ J'` using `fun ψ => hV _ (hI _)`.

Establish `hc3' : C3.left p₀ ∈ Wc` using `by show Q.famφB α 3 p₀ ∈ Wc; rw [hfix]; exact hp₀W`. Establish `s6 : gs (𝟙 _) ((b ≫ m₀) z) (Q.famφB α 3 ⁻¹ᵁ U) ((Q.famφB α 3).app U |>.hom f) = 1`. Express the relevant statement in the definitionally equal form `gs (𝟙 _) p₀ (C3.left ⁻¹ᵁ U) ((C3.left.app U).hom f) = 1`. Rewrite using `[gs_pull (𝟙 _) C3.left p₀ U (hfix.symm ▸ hp₀U) f, Category.id_comp, gs_res C3.left p₀ inf_le_right (hfix.symm ▸ hp₀U), gs_unit _ _ _ hc3']`. Establish `v` using `val_of G C3.left p₀ J' j₀ fun k => by show h.j (I ((C3.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) p₀)) = h.j (I ((Y.q.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) y)) show h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) (C3.left p₀))) = h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) (Y.q.left y)))`.

Rewrite using `[hy]`. Conclude with `congrArg (fun p => h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) p))) hfix`. Use `(congrArg Units.val v.symm).trans ?_` and prove the remaining obligations. Rewrite using `[val_cub Q.cub C3 hJ' _ _ _, Category.comp_id, show C3 = 1 from Hom.one_def.symm, (isCub_cubV Q.cub hJ').face₃, Units.val_one]`. Establish `δ'1 : δ' 1 = 0`.

Use `δ'mul 1 1` as an intermediate fact. Simplify using `only [_root_.mul_one, map_one, _root_.one_mul] at this`. Take the linear combination `-this`. Rewrite using `[e₁, s1, s2, ← s3, ← s4, ← s5, s6, δ'1]`. Establish `E` using `dlog_const_add π δ δmul _ _ _ _ (GlobalTheory.TorusModel.cv_add (Y.Φ Y.H (𝟙 _)) hJ α β) _ _ _ (key α c₁ H₁) (key β c₂ H₂) (key (α + β) c₃ H₃) hθ`.

Rewrite `E` using `[cst_eq_cstH, cst_eq_cstH, cst_eq_cstH, ← map_add]`. Conclude with `(cstH (b ≫ A₀.hom) z).injective E`.
-/
theorem coordEq_const_add : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D) {K : Type} [Field K] [CharZero K] (φ : R →+* K) (e : ℕ) (ν : R) (A₀ : Over (Sp K)) [GrpObj A₀] (m₀ : A₀.left ⟶ Q.P.A.left), IsFibre Y h φ e ν A₀ m₀ → ∀ (V : h.J → Q.P.A.left.Opens) (ed : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), IsConnK Q.P.A Q.P.L A₀ m₀ (fun r => φ (D r)) V h.j ed pb → IsDesc Y h ν m₀ V ed pb → Commutes Q m₀ ed → ∀ (α β : Q.X) (c₁ c₂ c₃ : K), CoordEq Y h ν m₀ V pb α c₁ → CoordEq Y h ν m₀ V pb β c₂ → CoordEq Y h ν m₀ V pb (α + β) c₃ → c₃ = c₁ + c₂ := by
  intro R _ _ Q O _ _ _ oa Y n dd D h K _ _ φ e ν A₀ _ m₀ hF V ed pb hC hD hCm α β c₁ c₂ c₃ H₁ H₂ H₃
  obtain ⟨hd, hcov, hV, -⟩ := hC
  have P := hF.pull.1
  let z : Sp K := IsLocalRing.closedPoint K
  let a : Sp K ⟶ Y.H.left := spMap φ ≫ η[Y.H].left
  have hb : (spMap φ ≫ η[Q.P.A].left) ≫ Q.P.A.hom = 𝟙 (Sp K) ≫ spMap φ := by
    rw [Category.assoc, Over.w η[Q.P.A], Category.id_comp]
    rfl
  let b : Sp K ⟶ A₀.left := P.lift _ _ hb
  have hbm : b ≫ m₀ = spMap φ ≫ η[Q.P.A].left := P.lift_fst _ _ _
  have hbA : b ≫ A₀.hom = 𝟙 _ := P.lift_snd _ _ _
  have w : a ≫ Y.q.left = b ≫ m₀ := by
    have := Y.q_linear.isMonHom
    rw [hbm, Category.assoc, ← Over.comp_left, IsMonHom.one_hom]
  have hA3 : ∀ χ : Q.X, η[Q.P.A].left ≫ Q.famφB χ 3 = η[Q.P.A].left := fun χ => by
    change η[Q.P.A].left ≫ (toUnit Q.P.A ≫ η[Q.P.A]).left = _
    rw [← Over.comp_left, ← Category.assoc, toUnit_unique (η[Q.P.A] ≫ toUnit Q.P.A) (𝟙 _), Category.id_comp]
  have hA12 : ∀ χ : Q.X, η[Q.P.A].left ≫ Q.famφB χ 1 = η[Q.P.A].left ≫ Q.famφB χ 2 := fun χ => by
    change η[Q.P.A].left ≫ (padd Q.P.A (𝟙 Q.P.A) (toUnit _ ≫ Q.c χ)).left = η[Q.P.A].left ≫ (toUnit Q.P.A ≫ Q.c χ).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    change η[Q.P.A] ≫ (𝟙 Q.P.A * (toUnit _ ≫ Q.c χ)) = _
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc η[Q.P.A] (toUnit _), toUnit_unique (η[Q.P.A] ≫ toUnit Q.P.A) (𝟙 _),
      Category.id_comp]
    have e1 : (η[Q.P.A] : 𝟙_ _ ⟶ Q.P.A) = 1 := by rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    rw [e1, _root_.one_mul]
  have hTb : ∀ (χ : Q.X) (j : Fin 4) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ j → T' ≫ A₀.hom = A₀.hom →
      b ≫ T' ≫ m₀ = spMap φ ≫ η[Q.P.A].left ≫ Q.famφB χ j := fun χ j T' h₁ _ => by
    rw [h₁, reassoc_of% hbm]
  have e3 : ∀ (χ : Q.X) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ 3 → T' ≫ A₀.hom = A₀.hom → b ≫ T' = b :=
    fun χ T' h₁ h₂ => P.hom_ext (by rw [Category.assoc, hTb χ 3 T' h₁ h₂, hA3, hbm]) (by rw [Category.assoc, h₂])
  have e0 : ∀ (χ : Q.X) (T' : A₀.left ⟶ A₀.left), T' ≫ m₀ = m₀ ≫ Q.famφB χ 0 → T' ≫ A₀.hom = A₀.hom → b ≫ T' = b :=
    fun χ T' h₁ h₂ => by rw [hF.T_zero h₁ h₂, Category.comp_id]
  have e12 : ∀ (χ : Q.X) (T₁ T₂ : A₀.left ⟶ A₀.left), T₁ ≫ m₀ = m₀ ≫ Q.famφB χ 1 → T₁ ≫ A₀.hom = A₀.hom →
      T₂ ≫ m₀ = m₀ ≫ Q.famφB χ 2 → T₂ ≫ A₀.hom = A₀.hom → b ≫ T₁ = b ≫ T₂ :=
    fun χ T₁ T₂ h₁ h₂ h₃ h₄ => P.hom_ext (by rw [Category.assoc, Category.assoc, hTb χ 1 T₁ h₁ h₂, hTb χ 2 T₂ h₃ h₄, hA12])
      (by rw [Category.assoc, Category.assoc, h₂, h₄])
  have hcov' : ∀ p : Q.P.A.left, ∃ i, p ∈ V i := fun p => by
    have : p ∈ (⨆ i, V i) := by rw [hcov]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  choose I hI using hcov'
  let p₀ : Q.P.A.left := (b ≫ m₀) z
  let i₀ : h.J := I p₀
  let y : Y.H.left := a z
  have hy : Y.q.left y = p₀ := by
    change (a ≫ Y.q.left) z = _
    rw [w]
  have h₀ : a z ∈ h.W i₀ := by
    rw [hD.1 i₀]
    change Y.q.left y ∈ V i₀
    rw [hy]
    exact hI p₀
  obtain ⟨δ, -, δmul, δeq⟩ := exists_stalkDer_field (isField_dE h ν hF.field i₀) a z h₀
  let π := (a.stalkMap z).hom
  let g := Y.Φ Y.H (𝟙 _)
  let J : (Y.H.left ⟶ Q.P.A.left) → Q.P.L.ι := fun ψ => h.j (I (ψ y))
  have hJ : Good Q.P.L y J := fun ψ => hV _ (hI _)
  have key : ∀ (χ : Q.X) (c : K), CoordEq Y h ν m₀ V pb χ c →
      δ (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val =
        π (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val * cst (b ≫ A₀.hom) z c := by
    intro χ c Hc
    obtain ⟨T, hT1, hT2⟩ := hF.exists_strictHenselian_absolutely_closed_local_ring χ
    have f0 := e0 χ (T 0) (hT1 0) (hT2 0)
    have f3 := e3 χ (T 3) (hT1 3) (hT2 3)
    have f12 := e12 χ (T 1) (T 2) (hT1 1) (hT2 1) (hT1 2) (hT2 2)
    let i₁ : h.J := I (((b ≫ T 1) ≫ m₀) z)
    let i : Fin 4 → h.J := ![i₀, i₁, i₁, i₀]
    have hpt : ∀ j, (b ≫ T j ≫ m₀) z = Q.famφB χ j p₀ := fun j => by
      rw [hT1 j, ← Category.assoc]; rfl
    have hIi : ∀ j, I ((b ≫ T j ≫ m₀) z) = i j := by
      intro j; fin_cases j
      · show I ((b ≫ T 0 ≫ m₀) z) = i₀; rw [← Category.assoc, f0]
      · show I ((b ≫ T 1 ≫ m₀) z) = i₁; rw [← Category.assoc]
      · show I ((b ≫ T 2 ≫ m₀) z) = i₁; rw [← Category.assoc, ← f12]
      · show I ((b ≫ T 3 ≫ m₀) z) = i₀; rw [← Category.assoc, f3]
    have hi : ∀ j, (b ≫ T j ≫ m₀) z ∈ V (i j) := fun j => hIi j ▸ hI _
    have Hc' := Hc T hT1 hT2 (Sp K) a b w z i hi
    have hm := hF.mem_chart hD hV hT1 w hi
    unfold CoordAt at Hc'
    have hP : ∀ w' : (Sp K).presheaf.stalk z, - gs (b ≫ T 0) z (m₀ ⁻¹ᵁ V (i 0)) (pb (i 0)) +
        gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V (i 1)) (pb (i 1)) - gs (b ≫ T 2) z (m₀ ⁻¹ᵁ V (i 2)) (pb (i 2)) +
        gs (b ≫ T 3) z (m₀ ⁻¹ᵁ V (i 3)) (pb (i 3)) + w' = w' := by
      intro w'
      rw [f0, f3, ← f12]
      show - gs b z (m₀ ⁻¹ᵁ V i₀) (pb i₀) + gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V i₁) (pb i₁) -
        gs (b ≫ T 1) z (m₀ ⁻¹ᵁ V i₁) (pb i₁) + gs b z (m₀ ⁻¹ᵁ V i₀) (pb i₀) + w' = w'
      ring
    rw [hP] at Hc'
    have hcv : (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val =
        gs (𝟙 _) y (xU Y χ fun j => h.j (i j)) (xc Y χ fun j => h.j (i j)).val := by
      rw [gs_unit (𝟙 _) y _ hm.2]
      congr 1
      refine val_of _ _ _ _ _ fun k => ?_
      show h.j (I ((𝟙 _ ≫ DegPre.gtφT Q Y.H (Y.Φ Y.H (𝟙 _)).b χ k) y)) = h.j (i (![1, 2, 0, 3] k))
      rw [Category.id_comp, gtφT_eq, ← hIi, hpt]
      show h.j (I (Q.famφB χ _ (Y.q.left y))) = _
      rw [hy]
    calc δ (GlobalTheory.TorusModel.cv (Y.Φ Y.H (𝟙 _)) χ y J).val
        = δ (gs (𝟙 _) y (h.W i₀ ⊓ xU Y χ fun j => h.j (i j))
            (rsT (xc Y χ fun j => h.j (i j)).val (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)))) := by
          rw [hcv, GlobalTheory.KS.DlogPol.gs_rsT (𝟙 Y.H.left) y (O := h.W i₀ ⊓ xU Y χ fun j => h.j (i j)) inf_le_right hm]
      _ = gs a z (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)) (dE h ν i₀ _
            (rsT (xc Y χ fun j => h.j (i j)).val (h.W i₀ ⊓ xU Y χ fun j => h.j (i j)))) := δeq _ inf_le_left hm _
      _ = gs a z (xU Y χ fun j => h.j (i j)) (xc Y χ fun j => h.j (i j)).val * cst (b ≫ A₀.hom) z c := Hc'
      _ = _ := by rw [gs_stalkMap a z _ hm.2, ← hcv]
  have hθ : δ (ReciprocityTheory.ChartRestriction.G.DVR.th Q y J (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H α) (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H β)
      (Y.Φ Y.H (𝟙 _)).b).val = 0 := by
    let Λ : Q.P.A ⟶ Q.P.A ⊗ (Q.P.A ⊗ Q.P.A) :=
      lift (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A α) (lift (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A β) (𝟙 _))
    let G := LB.pullGen Q.P.L (thφ Q.P.A (x3 Q.P.A)) thε Q.cub.t Λ.left
    have a1 : ∀ χ, Y.q ≫ ReciprocityTheory.ChartRestriction.G.DVR.cP Q Q.P.A χ = ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H χ := fun χ => by
      simp only [ReciprocityTheory.ChartRestriction.G.DVR.cP, comp_toUnit_assoc]
    have e₁ : ReciprocityTheory.ChartRestriction.G.DVR.th Q y J (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H α) (ReciprocityTheory.ChartRestriction.G.DVR.cP Q Y.H β)
        (Y.Φ Y.H (𝟙 _)).b = val G Y.q.left y J := by
      refine Eq.trans ?_ (val_cub Q.cub Y.q hJ _ _ _).symm
      rw [a1, a1, Category.comp_id]
      rfl
    let j₀ := fun k => J (Y.q.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k)
    let Wc := LB.wchart Q.P.L (fun k => Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) j₀
    let θ₀ : Γ(Q.P.A.left, Wc)ˣ := G.s j₀
    have hWc : Y.q.left y ∈ Wc := hJ.mem _ Y.q.left
    have hp₀W : p₀ ∈ Wc := hy ▸ hWc
    let U : Q.P.A.left.Opens := V i₀ ⊓ Wc
    have hp₀U : p₀ ∈ U := ⟨hI p₀, hp₀W⟩
    have hyU : Y.q.left y ∈ U := hy ▸ hp₀U
    let f : Γ(Q.P.A.left, U) := resG Q.P.A.left (inf_le_right : U ≤ Wc) θ₀.val
    have s1 : (val G Y.q.left y J).val = gs (𝟙 _) y (Y.q.left ⁻¹ᵁ U) ((Y.q.left.app U).hom f) := by
      rw [gs_pull (𝟙 _) Y.q.left y U hyU f, Category.id_comp, gs_res Y.q.left y inf_le_right hyU]
      exact (gs_unit _ _ _ hWc _).symm
    have hle : Y.q.left ⁻¹ᵁ U ≤ h.W i₀ := by
      rw [hD.1 i₀]; exact fun x hx => hx.1
    have s2 := δeq (Y.q.left ⁻¹ᵁ U) hle hyU ((Y.q.left.app U).hom f)
    have s3 := hD.2.1 (Sp K) a b w z i₀ U inf_le_left hp₀U f
    obtain ⟨T, hT1, hT2⟩ := hF.exists_strictHenselian_absolutely_closed_local_ring α
    have f3 := e3 α (T 3) (hT1 3) (hT2 3)
    have hmem3 : (b ≫ T 3 ≫ m₀) z ∈ U := by rw [← Category.assoc, f3]; exact hp₀U
    have s4 := hCm α 3 (T 3) (hT1 3) (hT2 3) U f (Sp K) b z hmem3
    rw [f3] at s4
    have hfix : Q.famφB α 3 p₀ = p₀ := by
      have : (b ≫ T 3 ≫ m₀) z = Q.famφB α 3 p₀ := by rw [hT1 3, ← Category.assoc]; rfl
      rw [← this, ← Category.assoc, f3]
    obtain ⟨δ', -, δ'mul, δ'eq⟩ := exists_stalkDer_along hd b z
    have hc3 : (b ≫ m₀) z ∈ Q.famφB α 3 ⁻¹ᵁ U := by
      show Q.famφB α 3 p₀ ∈ U; rw [hfix]; exact hp₀U
    have s5 := δ'eq _ hc3 ((Q.famφB α 3).app U |>.hom f)
    let C3 : Q.P.A ⟶ Q.P.A := toUnit Q.P.A ≫ η[Q.P.A]
    let J' : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι := fun ψ => h.j (I (ψ p₀))
    have hJ' : Good Q.P.L p₀ J' := fun ψ => hV _ (hI _)
    have hc3' : C3.left p₀ ∈ Wc := by
      show Q.famφB α 3 p₀ ∈ Wc; rw [hfix]; exact hp₀W
    have s6 : gs (𝟙 _) ((b ≫ m₀) z) (Q.famφB α 3 ⁻¹ᵁ U) ((Q.famφB α 3).app U |>.hom f) = 1 := by
      change gs (𝟙 _) p₀ (C3.left ⁻¹ᵁ U) ((C3.left.app U).hom f) = 1
      rw [gs_pull (𝟙 _) C3.left p₀ U (hfix.symm ▸ hp₀U) f, Category.id_comp,
        gs_res C3.left p₀ inf_le_right (hfix.symm ▸ hp₀U), gs_unit _ _ _ hc3']
      have v := val_of G C3.left p₀ J' j₀ fun k => by
        show h.j (I ((C3.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) p₀)) =
          h.j (I ((Y.q.left ≫ Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) y))
        show h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) (C3.left p₀))) =
          h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) (Y.q.left y)))
        rw [hy]; exact congrArg (fun p => h.j (I ((Λ.left ≫ thφ Q.P.A (x3 Q.P.A) k) p))) hfix
      refine (congrArg Units.val v.symm).trans ?_
      rw [val_cub Q.cub C3 hJ' _ _ _, Category.comp_id, show C3 = 1 from Hom.one_def.symm,
        (isCub_cubV Q.cub hJ').face₃, Units.val_one]
    have δ'1 : δ' 1 = 0 := by
      have := δ'mul 1 1
      simp only [_root_.mul_one, map_one, _root_.one_mul] at this
      linear_combination -this
    rw [e₁, s1, s2, ← s3, ← s4, ← s5, s6, δ'1]
  have E := dlog_const_add π δ δmul _ _ _ _ (GlobalTheory.TorusModel.cv_add (Y.Φ Y.H (𝟙 _)) hJ α β) _ _ _
    (key α c₁ H₁) (key β c₂ H₂) (key (α + β) c₃ H₃) hθ
  rw [cst_eq_cstH, cst_eq_cstH, cst_eq_cstH, ← map_add] at E
  exact (cstH (b ≫ A₀.hom) z).injective E

end GlobalTheory.HeatConn
