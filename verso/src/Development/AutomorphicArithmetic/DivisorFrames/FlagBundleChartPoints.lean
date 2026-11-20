import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
import Development.AutomorphicArithmetic.DivisorFrames.ExistsAdaptedFlagCharts
import Development.AutomorphicArithmetic.DivisorFrames.FlagChartTransitionTriangular
import Development.AutomorphicArithmetic.DivisorFrames.FlagConnectionAdapted
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

section SlopeTestRemainingChoices

open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply)

/- English proof (translation)
Use `isFrame_of_forall_exists fun V h x hx => ?_` and prove the remaining obligations. Take `⟨W, a, -, hxW, hle, ha⟩` from `hA.exists_affine hx`. Use `⟨W, hle, hxW, ?_⟩` and prove the remaining obligations. Set `p : Γ(A, W) →ₗ[Γ(X, W)] (Fin k → Γ(X, W))` to `LinearMap.funLeft _ _ g ∘ₗ (he.basis (hle.trans h)).equivFun.toLinearMap ∘ₗ appLinear u W`. Establish `hp : p ∘ₗ (Fintype.linearCombination Γ(X, W) fun i => resM A (hle.trans h) (s i)) = LinearMap.id`.

Use `(Pi.basisFun _ _).ext fun j => ?_` and prove the remaining obligations. Establish `h₁ : appLinear u W (resM A (hle.trans h) (s j)) = he.basis (hle.trans h) (g j)`. Rewrite using `[appLinear_apply, app_resM, hs, IsFrame.basis_apply]`. Use function extensionality and compare the values at `i`. Simplify using `[p, h₁, Finsupp.single_apply, Pi.single_apply, hg.eq_iff, eq_comm, -IsFrame.basis_apply]`.

Establish `hp' (c) : p (Fintype.linearCombination Γ(X, W) (fun i => resM A (hle.trans h) (s i)) c) = c` using `LinearMap.congr_fun hp c`. Establish `hsurj : Function.Surjective p` using `fun c => ⟨_, hp' c⟩`. Establish `hinj : Function.Injective p`. Use `OrzechProperty.injective_of_surjective_endomorphism (p ∘ₗ (ha.basis le_rfl).equivFun.symm.toLinearMap) (hsurj.comp (ha.basis le_rfl).equivFun.symm.surjective)` as an intermediate fact. Conclude with `(Function.Injective.of_comp_iff' _ (ha.basis le_rfl).equivFun.symm.bijective).1 this`.

Conclude with `⟨fun c c' hc => by rw [← hp' c, hc, hp'], fun y => ⟨p y, hinj (hp' _)⟩⟩`.
-/
private theorem UpperTheory.subbundle_frame_injective_global {X : Scheme.{0}} {A M : X.Modules} {k r : ℕ} (hA : IsVB A k) (u : A ⟶ M)
    {U : X.Opens} {e : Fin r → Γ(M, U)} (he : IsFrame e) (g : Fin k → Fin r) (hg : Function.Injective g)
    (s : Fin k → Γ(A, U)) (hs : ∀ j, u.app U (s j) = e (g j)) : IsFrame s := by
  refine isFrame_of_forall_exists fun V h x hx => ?_
  obtain ⟨W, a, -, hxW, hle, ha⟩ := hA.exists_affine hx
  refine ⟨W, hle, hxW, ?_⟩
  let p : Γ(A, W) →ₗ[Γ(X, W)] (Fin k → Γ(X, W)) :=
    LinearMap.funLeft _ _ g ∘ₗ (he.basis (hle.trans h)).equivFun.toLinearMap ∘ₗ appLinear u W
  have hp : p ∘ₗ (Fintype.linearCombination Γ(X, W) fun i => resM A (hle.trans h) (s i)) = LinearMap.id := by
    refine (Pi.basisFun _ _).ext fun j => ?_
    have h₁ : appLinear u W (resM A (hle.trans h) (s j)) = he.basis (hle.trans h) (g j) := by
      rw [appLinear_apply, app_resM, hs, IsFrame.basis_apply]
    funext i
    simp [p, h₁, Finsupp.single_apply, Pi.single_apply, hg.eq_iff, eq_comm, -IsFrame.basis_apply]
  have hp' (c) : p (Fintype.linearCombination Γ(X, W) (fun i => resM A (hle.trans h) (s i)) c) = c :=
    LinearMap.congr_fun hp c
  have hsurj : Function.Surjective p := fun c => ⟨_, hp' c⟩
  have hinj : Function.Injective p := by
    have := OrzechProperty.injective_of_surjective_endomorphism
      (p ∘ₗ (ha.basis le_rfl).equivFun.symm.toLinearMap) (hsurj.comp (ha.basis le_rfl).equivFun.symm.surjective)
    exact (Function.Injective.of_comp_iff' _ (ha.basis le_rfl).equivFun.symm.bijective).1 this
  exact ⟨fun c c' hc => by rw [← hp' c, hc, hp'], fun y => ⟨p y, hinj (hp' _)⟩⟩

/- English proof (translation)
Proceed by induction on `b using Fin.induction with`. Consider the case `zero`. Take `rfl : a = 0` from `Fin.le_zero_iff.1 h`. Conclude with `⟨𝟙 _, Category.id_comp _⟩`. Consider the case `succ b ih`.

Break down `h.eq_or_lt with rfl | h'` into its components or cases. Conclude with `⟨𝟙 _, Category.id_comp _⟩`. Take `⟨φ, hφ⟩` from `ih (Fin.le_castSucc_iff.2 h')`. Conclude with `⟨φ ≫ fl.step b, by rw [Category.assoc, fl.step_ι, hφ]⟩`.
-/
private theorem UpperTheory.flag_nested_global {X : Scheme.{0}} {M : X.Modules} {r : ℕ} (fl : Vert.Flag M r) (a b : Fin (r + 1))
    (h : a ≤ b) : ∃ φ : fl.F a ⟶ fl.F b, φ ≫ fl.ι b = fl.ι a := by
  induction b using Fin.induction with
  | zero =>
    obtain rfl : a = 0 := Fin.le_zero_iff.1 h
    exact ⟨𝟙 _, Category.id_comp _⟩
  | succ b ih =>
    rcases h.eq_or_lt with rfl | h'
    · exact ⟨𝟙 _, Category.id_comp _⟩
    · obtain ⟨φ, hφ⟩ := ih (Fin.le_castSucc_iff.2 h')
      exact ⟨φ ≫ fl.step b, by rw [Category.assoc, fl.step_ι, hφ]⟩

/- English proof (translation)
Use extensionality with `V s`. Use `congr($((he.basis le_top).ext (f₁ := QCoh.appLinear φ V) (f₂ := QCoh.appLinear ψ V) fun i => ?_) s)` and prove the remaining obligations. Rewrite using `[IsFrame.basis_apply]`. Conclude with `(Twist.app_resM φ _ _).trans ((congrArg _ (h i)).trans (Twist.app_resM ψ _ _).symm)`.
-/
private theorem UpperTheory.ext_of_global_frame {X : Scheme.{0}} {F G : X.Modules} {κ : Type} [Fintype κ] {e : κ → Γ(F, ⊤)}
    (he : IsFrame e) {φ ψ : F ⟶ G} (h : ∀ i, φ.app ⊤ (e i) = ψ.app ⊤ (e i)) : φ = ψ := by
  ext V s
  refine congr($((he.basis le_top).ext (f₁ := QCoh.appLinear φ V) (f₂ := QCoh.appLinear ψ V)
    fun i => ?_) s)
  rw [IsFrame.basis_apply]
  exact (Twist.app_resM φ _ _).trans ((congrArg _ (h i)).trans (Twist.app_resM ψ _ _).symm)

/- English proof (translation)
Take `⟨s₀, hs₀⟩` from `h j`. Take `⟨φ, hφ⟩` from `UpperTheory.flag_nested_global fl j.succ k hj`. Conclude with `⟨φ.app U s₀, by rw [QCoh.app_app, hφ, hs₀]⟩`.
-/
private theorem UpperTheory.flag_lift_frame {X : Scheme.{0}} {M : X.Modules} {r : ℕ} (fl : Vert.Flag M r) {U : X.Opens}
    (e : Fin r → Γ(M, U)) (h : ∀ i : Fin r, ∃ s : Γ(fl.F i.succ, U), (fl.ι i.succ).app U s = e i)
    (k : Fin (r + 1)) (j : Fin r) (hj : (j : ℕ) < k) : ∃ s : Γ(fl.F k, U), (fl.ι k).app U s = e j := by
  obtain ⟨s₀, hs₀⟩ := h j
  obtain ⟨φ, hφ⟩ := UpperTheory.flag_nested_global fl j.succ k hj
  exact ⟨φ.app U s₀, by rw [QCoh.app_app, hφ, hs₀]⟩

/- English proof (translation)
Establish `hk : (k : ℕ) ≤ r` using `Nat.lt_succ_iff.1 k.2`. Use `choose s hs using fun j : Fin k => UpperTheory.flag_lift_frame fl e h k (j.castLE hk) j.2`. Use `choose s' hs' using fun j : Fin k => UpperTheory.flag_lift_frame fl' e h' k (j.castLE hk) j.2`. Establish `f` using `UpperTheory.subbundle_frame_injective_global (fl.isVB k) (fl.ι k) he _ (Fin.castLE_injective hk) s hs`. Establish `f'` using `UpperTheory.subbundle_frame_injective_global (fl'.isVB k) (fl'.ι k) he _ (Fin.castLE_injective hk) s' hs'`.

Use `⟨IsFrame.iso f f', UpperTheory.ext_of_global_frame f fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[← QCoh.app_app, IsFrame.iso_hom_app, hs, hs']`.
-/
private theorem UpperTheory.flag_iso_of_global_frame {X : Scheme.{0}} {M : X.Modules} {r : ℕ} (fl fl' : Vert.Flag M r)
    {e : Fin r → Γ(M, ⊤)} (he : IsFrame e) (h : ∀ i : Fin r, ∃ s : Γ(fl.F i.succ, ⊤), (fl.ι i.succ).app ⊤ s = e i)
    (h' : ∀ i : Fin r, ∃ s : Γ(fl'.F i.succ, ⊤), (fl'.ι i.succ).app ⊤ s = e i) (k : Fin (r + 1)) :
    ∃ φ : fl.F k ≅ fl'.F k, φ.hom ≫ fl'.ι k = fl.ι k := by
  have hk : (k : ℕ) ≤ r := Nat.lt_succ_iff.1 k.2
  choose s hs using fun j : Fin k => UpperTheory.flag_lift_frame fl e h k (j.castLE hk) j.2
  choose s' hs' using fun j : Fin k => UpperTheory.flag_lift_frame fl' e h' k (j.castLE hk) j.2
  have f := UpperTheory.subbundle_frame_injective_global (fl.isVB k) (fl.ι k) he _ (Fin.castLE_injective hk) s hs
  have f' := UpperTheory.subbundle_frame_injective_global (fl'.isVB k) (fl'.ι k) he _ (Fin.castLE_injective hk) s' hs'
  refine ⟨IsFrame.iso f f', UpperTheory.ext_of_global_frame f fun j => ?_⟩
  rw [← QCoh.app_app, IsFrame.iso_hom_app, hs, hs']

/- English proof (translation)
Rewrite using `[← (c.isFrame.basis hW).sum_repr (e i)]`. Express the relevant statement in the definitionally equal form `_ ∈ LinearMap.range (appLinear (fl.ι i.succ) W)`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `ha : i < a`. Rewrite using `[h a i ha, zero_smul]`.

Conclude with `zero_mem _`. Take `⟨s, hs⟩` from `UpperTheory.flag_lift_frame fl c.e hc i.succ a (Nat.lt_succ_of_le (not_lt.1 ha))`. Use `Submodule.smul_mem _ _ ⟨resM _ hW s, ?_⟩` and prove the remaining obligations. Rewrite using `[appLinear_apply, app_resM, hs, IsFrame.basis_apply]`.
-/
private theorem UpperTheory.adapted_chart_triangular_lift {X : Scheme.{0}} {M : X.Modules} {r : ℕ} (fl : Vert.Flag M r) (c : Chart M r)
    (hc : IsAdapted fl c) {W : X.Opens} (hW : W ≤ c.U) (e : Fin r → Γ(M, W))
    (h : ∀ a i, i < a → (c.isFrame.basis hW).repr (e i) a = 0) (i : Fin r) :
    ∃ s : Γ(fl.F i.succ, W), (fl.ι i.succ).app W s = e i := by
  rw [← (c.isFrame.basis hW).sum_repr (e i)]
  change _ ∈ LinearMap.range (appLinear (fl.ι i.succ) W)
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases ha : i < a
  · rw [h a i ha, zero_smul]
    exact zero_mem _
  · obtain ⟨s, hs⟩ := UpperTheory.flag_lift_frame fl c.e hc i.succ a (Nat.lt_succ_of_le (not_lt.1 ha))
    refine Submodule.smul_mem _ _ ⟨resM _ hW s, ?_⟩
    rw [appLinear_apply, app_resM, hs, IsFrame.basis_apply]

/- English proof (translation)
Introduce `a b hab`. Unfold `evalPt at hab`. Establish `e : Scheme.Hom.appLE (𝟙 (Sp K)) ⊤ ⊤ h = 𝟙 _`. Rewrite using `[Scheme.Hom.appLE, Scheme.Hom.id_app]`. Conclude with `(Category.id_comp _).trans ((Sp K).presheaf.map_id _)`.

Rewrite `hab` using `[e, Category.id_comp]`. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective hab`.
-/
private theorem UpperTheory.evalPt_identity_injective {K : Type} [CommRing K] (h : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ ⊤) :
    Function.Injective (evalPt (𝟙 (Sp K)) ⊤ h) := by
  intro a b hab
  unfold evalPt at hab
  have e : Scheme.Hom.appLE (𝟙 (Sp K)) ⊤ ⊤ h = 𝟙 _ := by
    rw [Scheme.Hom.appLE, Scheme.Hom.id_app]
    exact (Category.id_comp _).trans ((Sp K).presheaf.map_id _)
  rw [e, Category.id_comp] at hab
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.injective hab

/- English proof (translation)
Introduce `B Y π ι M n hM fl hfl K _ q q' w b ch ch' hb h h' hT`. Use `((FlagConnect.isFlagBundle_iff π M n fl).1 hfl (Sp K) (q ≫ π) (FlagConnect.carried π M n fl q _ rfl)).unique ⟨rfl, FlagConnect.carries_carried π M n fl q _ rfl⟩ ⟨w.symm, fun a i => ?_⟩` and prove the remaining obligations. Establish `hC'` using `FlagConnect.carries_carried π M n fl q' _ w.symm`. Take `⟨c, hU, hc, ht⟩` from `UpperTheory.flag_connection_adapted B Y _ π ι M n hM fl q _ rfl _ (FlagConnect.carries_carried π M n fl q _ rfl) a (ch a) (h a).2`. Take `⟨c', hU', hc', ht'⟩` from `UpperTheory.flag_connection_adapted B Y _ π ι M n hM fl q' _ w.symm _ hC' a (ch' a) (h' a).2`.

Take `⟨T, hT, e⟩` from `hT a`. Establish `l : ⊤ ≤ c.U` using `hU ▸ (h a).1`. Establish `l' : ⊤ ≤ c'.U` using `hU' ▸ (h' a).1`. Establish `e₁` using `ht K (𝟙 _) (b a) (hb a) (h a).1`. Establish `e₂` using `ht' K (𝟙 _) (b a) (hb a) (h' a).1`.

Rewrite `e₁`, `e₂` using `[Category.id_comp]`. Establish `lb : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ ((b a).pull (hM a) (q ≫ π)).U` using `hb a`. Rewrite `e` using `[← e₁, ← e₂, ← trAt_mul (x := 𝟙 _) _ c c' lb l l', ((isUnit_iff_isUnit_det _).2 (isUnit_det_trAt _ c lb l)).mul_right_inj]`. Establish `h₀ (k j) (hjk : j < k) : (c.isFrame.basis l).repr (resM _ l' (c'.e j)) k = 0`. Use `UpperTheory.evalPt_identity_injective le_rfl ?_` and prove the remaining obligations.

Rewrite using `[← trAt_apply c c' l l' le_rfl, e, hT k j hjk, map_zero]`. Take `⟨φ, hφ⟩` from `UpperTheory.flag_iso_of_global_frame (FlagConnect.carried π M n fl q' _ w.symm a) (FlagConnect.carried π M n fl q _ rfl a) (c'.isFrame.res l') (fun j => by`. Take `⟨s, hs⟩` from `hc' j`. Conclude with `⟨resM _ l' s, by rw [app_resM, hs]⟩) (UpperTheory.adapted_chart_triangular_lift _ c hc l _ h₀) i`. Take `⟨ψ, hψ⟩` from `hC' a i`.

Conclude with `⟨ψ ≪≫ φ, by rw [Iso.trans_hom, Category.assoc, hφ, hψ]⟩`.
-/
theorem UpperTheory.flag_bundle_chart_points :
    ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (M : ι → B.Modules) (n : ι → ℕ) (hM : ∀ a, IsVB (M a) (n a)) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (n a)), IsFlagBundle π M n fl → ∀ (K : Type) [Field K] (q q' : Sp K ⟶ Y), q ≫ π = q' ≫ π → ∀ (b : ∀ a, Chart (M a) (n a)) (ch ch' : ∀ a, Chart ((Scheme.Modules.pullback π).obj (M a)) (n a)), (∀ a, ⊤ ≤ (q ≫ π) ⁻¹ᵁ (b a).U) → (∀ a, ⊤ ≤ q ⁻¹ᵁ (ch a).U ∧ IsAdapted (fl a) (ch a)) → (∀ a, ⊤ ≤ q' ⁻¹ᵁ (ch' a).U ∧ IsAdapted (fl a) (ch' a)) → (∀ a, ∃ T, IsTri T ∧ trAt q' ((b a).pull (hM a) π) (ch' a) = trAt q ((b a).pull (hM a) π) (ch a) * T) → q = q' := by
  intro B Y π ι M n hM fl hfl K _ q q' w b ch ch' hb h h' hT
  refine ((FlagConnect.isFlagBundle_iff π M n fl).1 hfl (Sp K) (q ≫ π)
    (FlagConnect.carried π M n fl q _ rfl)).unique ⟨rfl, FlagConnect.carries_carried π M n fl q _ rfl⟩
    ⟨w.symm, fun a i => ?_⟩
  have hC' := FlagConnect.carries_carried π M n fl q' _ w.symm
  obtain ⟨c, hU, hc, ht⟩ := UpperTheory.flag_connection_adapted B Y _ π ι M n hM fl q _ rfl _
    (FlagConnect.carries_carried π M n fl q _ rfl) a (ch a) (h a).2
  obtain ⟨c', hU', hc', ht'⟩ := UpperTheory.flag_connection_adapted B Y _ π ι M n hM fl q' _ w.symm _ hC' a (ch' a) (h' a).2
  obtain ⟨T, hT, e⟩ := hT a
  have l : ⊤ ≤ c.U := hU ▸ (h a).1
  have l' : ⊤ ≤ c'.U := hU' ▸ (h' a).1
  have e₁ := ht K (𝟙 _) (b a) (hb a) (h a).1
  have e₂ := ht' K (𝟙 _) (b a) (hb a) (h' a).1
  rw [Category.id_comp] at e₁ e₂
  have lb : ⊤ ≤ (𝟙 (Sp K)) ⁻¹ᵁ ((b a).pull (hM a) (q ≫ π)).U := hb a
  rw [← e₁, ← e₂, ← trAt_mul (x := 𝟙 _) _ c c' lb l l',
    ((isUnit_iff_isUnit_det _).2 (isUnit_det_trAt _ c lb l)).mul_right_inj] at e
  have h₀ (k j) (hjk : j < k) : (c.isFrame.basis l).repr (resM _ l' (c'.e j)) k = 0 := by
    refine UpperTheory.evalPt_identity_injective le_rfl ?_
    rw [← trAt_apply c c' l l' le_rfl, e, hT k j hjk, map_zero]
  obtain ⟨φ, hφ⟩ := UpperTheory.flag_iso_of_global_frame (FlagConnect.carried π M n fl q' _ w.symm a)
    (FlagConnect.carried π M n fl q _ rfl a) (c'.isFrame.res l') (fun j => by
      obtain ⟨s, hs⟩ := hc' j
      exact ⟨resM _ l' s, by rw [app_resM, hs]⟩) (UpperTheory.adapted_chart_triangular_lift _ c hc l _ h₀) i
  obtain ⟨ψ, hψ⟩ := hC' a i
  exact ⟨ψ ≪≫ φ, by rw [Iso.trans_hom, Category.assoc, hφ, hψ]⟩

end SlopeTestRemainingChoices
