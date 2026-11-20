import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsTwistPullBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ThetaPullback

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

/- English proof (translation)
Establish `key : X.presheaf.map (homOfLE hle).op ≫ r.app V ≫ Z.presheaf.germ (r ⁻¹ᵁ V) z hz = r.app U ≫ Z.presheaf.germ (r ⁻¹ᵁ U) z (hle hz)`. Rewrite using `[Scheme.Hom.naturality_assoc]`. Use `congr 1`. Conclude with `TopCat.Presheaf.germ_res _ _ _ _`. Unfold `gm res pullU`.

Rewrite using `[dif_pos hz, dif_pos (hle hz)]`. Use `ext`. Simplify using `only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]`. Conclude with `congrArg (fun φ => φ.hom (a : Γ(X, U))) key`.
-/
private theorem gm_res_eq_gm {X Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U) (hz : r z ∈ V)
    (a : Γ(X, U)ˣ) : gm r z V (res hle a) = gm r z U a := by
  have key : X.presheaf.map (homOfLE hle).op ≫ r.app V ≫ Z.presheaf.germ (r ⁻¹ᵁ V) z hz =
      r.app U ≫ Z.presheaf.germ (r ⁻¹ᵁ U) z (hle hz) := by
    rw [Scheme.Hom.naturality_assoc]
    congr 1
    exact TopCat.Presheaf.germ_res _ _ _ _
  unfold gm res pullU
  rw [dif_pos hz, dif_pos (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  exact congrArg (fun φ => φ.hom (a : Γ(X, U))) key

/- English proof (translation)
Substitute `hφ` using the available equality. Conclude with `⟨t, ht, fun _ _ _ _ => rfl⟩`.
-/
private theorem exists_isGen_linComb_val_eq_of_eq {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ' ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val t' r z J = val t r z J := by
  subst hφ
  exact ⟨t, ht, fun _ _ _ _ => rfl⟩

/- English proof (translation)
Unfold `translPt`. Rewrite using `[← Category.assoc, comp_lift]`. Simplify using the standard rewrite rules.
-/
theorem whiskerRight_translPt {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    h ▷ A ≫ translPt A x = translPt A (h ≫ x) := by
  unfold translPt
  rw [← Category.assoc, comp_lift]
  simp

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [translT, whiskerRight_translPt]`.
-/
theorem translT_whiskerRight {T T' : Over S} (h : T' ⟶ T) (x : T ⟶ A) :
    translT A (h ≫ x) ≫ h ▷ A = h ▷ A ≫ translT A x := by
  ext <;> simp [translT, whiskerRight_translPt]

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [negT]`.
-/
theorem negT_whiskerRight {T T' : Over S} (h : T' ⟶ T) :
    negT A T' ≫ h ▷ A = h ▷ A ≫ negT A T := by
  ext <;> simp [negT]

/- English proof (translation)
Establish `e : ∀ j : Fin n, val (L` using `L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J = val (LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j : ℕ))).left) r z J := fun j => (val_pull hJ _ _ r).symm`. Rewrite using `[Finset.prod_congr rfl fun j _ => e j]`. Unfold `powGen val`. Simplify using `only`. Use `erw [map_prod]`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `gm_res_eq_gm _ _ _ (hJ.mem _ r) _`.
-/
theorem val_powGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (powGen A L k θ n) r z J = ∏ j : Fin n,
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J := by
  have e : ∀ j : Fin n, val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
      (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J =
      val (LB.pullGen L _ _ θ.φ (translT A (θ.pt ^ (j : ℕ))).left) r z J := fun j => (val_pull hJ _ _ r).symm
  rw [Finset.prod_congr rfl fun j _ => e j]
  unfold powGen val
  dsimp only
  erw [map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  exact gm_res_eq_gm _ _ _ (hJ.mem _ r) _

/- English proof (translation)
Unfold `symGen`. Rewrite using `[val_mul hJ, val_mul hJ, val_inv]`. Establish `e1` using `val_mul hJ (LB.pullGen L _ _ θ.φ (translT A θ.pt⁻¹).left) ν r`. Establish `e2` using `val_pull hJ θ.φ (translT A θ.pt⁻¹).left r`. Establish `e3` using `val_pull hJ θ.φ (negT A T).left r`.

Establish `e4` using `val_pull hJ ν (translT A θ.pt⁻¹).left r`. Rewrite using `[e1, e2, e3, e4]`.
-/
theorem val_symGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (ν : LB.Gen (negLB A L k T))
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) {z : Z} {J} (hJ : Good L z J) :
    val (symGen A L k θ ν) r z J =
      val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (translT A θ.pt⁻¹).left) z J *
        val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν r z J *
        (val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
          (r ≫ (negT A T).left) z J *
        (val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) ν
          (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) := by
  unfold symGen
  rw [val_mul hJ, val_mul hJ, val_inv]
  have e1 := val_mul hJ (LB.pullGen L _ _ θ.φ (translT A θ.pt⁻¹).left) ν r
  have e2 := val_pull hJ θ.φ (translT A θ.pt⁻¹).left r
  have e3 := val_pull hJ θ.φ (negT A T).left r
  have e4 := val_pull hJ ν (translT A θ.pt⁻¹).left r
  rw [e1, e2, e3, e4]

/- English proof (translation)
Introduce `S A _ _ L hL k T T' h θ`. Establish `hφ : (fun b => (h ▷ A).left ≫ (![(snd T A).left, (translPt A θ.pt).left] : Fin 2 → _) b) = ![(snd T' A).left, (translPt A (h ≫ θ.pt)).left]`. Use function extensionality and compare the values at `b`. Use `fin_cases b`. Simplify using `only [Fin.zero_eta, Matrix.cons_val_zero]`.

Rewrite using `[← Over.comp_left, whiskerRight_snd]`. Simplify using `only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]`. Rewrite using `[← Over.comp_left, whiskerRight_translPt]`. Take `⟨φ', gφ', vφ'⟩` from `exists_isGen_linComb_val_eq_of_eq hφ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ θ.φ θ.3 (h ▷ A).left)`. Establish `vθ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J → val φ' r z J = val (L` using `L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ (r ≫ (h ▷ A).left) z J := fun Z r z J hJ => (vφ' Z r z J).trans (val_pull hJ _ _ r)`.

Establish `hcorr : LB.Gen.Corr L _ _ _ _ φ' (LB.pullGen L _ _ θ.φ (h ▷ A).left)` using `corr_of_val hL fun y J _ => vφ' _ _ y J`. Establish `hpow : ∀ j : ℕ, h ≫ θ.pt ^ j = (h ≫ θ.pt) ^ j`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`.

Consider the case `succ j ih => rw [pow_succ, pow_succ, comp_mul, ih]`. Establish `hinv : h ≫ θ.pt⁻¹ = (h ≫ θ.pt)⁻¹` using `GrpObj.comp_inv h θ.pt`. Use `⟨⟨h ≫ θ.pt, φ', gφ'⟩, rfl, hcorr, ?_, ?_⟩` and prove the remaining obligations. Introduce `n x hs`. Take `⟨hpt, hpw, nu, gnu, hsym⟩` from `hs`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Use `show h ≫ θ.pt = h ≫ x`. Rewrite using `[hpt]`. Use `corr_of_val hL fun y J hJ => ?_` and prove the remaining obligations. Establish `hθ1` using `val_corr hJ hpw (h ▷ A).left`.

Rewrite `hθ1` using `[val_one, val_powGen _ _ _ hJ]`. Rewrite using `[val_one, val_powGen _ _ _ hJ, ← hθ1]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[vθ _ _ _ _ hJ]`.

Establish `e : (𝟙 _ ≫ (translT A ((h ≫ θ.pt) ^ (j : ℕ))).left) ≫ (h ▷ A).left = (h ▷ A).left ≫ (translT A (θ.pt ^ (j : ℕ))).left`. Rewrite using `[Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hpow, translT_whiskerRight]`. Rewrite using `[e]`. Establish `hφn : (fun b => (h ▷ A).left ≫ (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) b) = ![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left]`. Use function extensionality and compare the values at `b`.

Use `fin_cases b`. Simplify using `only [Fin.zero_eta, Matrix.cons_val_zero]`. Rewrite using `[← Over.comp_left, whiskerRight_snd]`. Simplify using `only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]`. Rewrite using `[← Over.comp_left, whiskerRight_snd_assoc]`.

Take `⟨nu', gnu', vnu'⟩` from `exists_isGen_linComb_val_eq_of_eq hφn _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ nu gnu (h ▷ A).left)`. Establish `vnu : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J → val nu' r z J = val (L` using `L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) nu (r ≫ (h ▷ A).left) z J := fun Z r z J hJ => (vnu' Z r z J).trans (val_pull hJ _ _ r)`. Use `⟨nu', gnu', corr_of_val hL fun y J hJ => ?_⟩` and prove the remaining obligations. Establish `hθ2` using `val_corr hJ hsym (h ▷ A).left`. Rewrite `hθ2` using `[val_one, val_symGen _ _ _ hJ]`.

Rewrite using `[val_one]`. Use `(val_symGen _ _ _ hJ).trans ?_` and prove the remaining obligations. Rewrite using `[← hθ2]`. Simplify using `only`. Rewrite using `[vθ _ _ _ _ hJ, vθ _ _ _ _ hJ, vnu _ _ _ _ hJ, vnu _ _ _ _ hJ]`.

Establish `e1 : (𝟙 _ ≫ (translT A (h ≫ θ.pt)⁻¹).left) ≫ (h ▷ A).left = (h ▷ A).left ≫ (translT A θ.pt⁻¹).left`. Rewrite using `[Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hinv, translT_whiskerRight]`. Establish `e3 : (𝟙 _ ≫ (negT A T').left) ≫ (h ▷ A).left = (h ▷ A).left ≫ (negT A T).left`. Rewrite using `[Category.id_comp, ← Over.comp_left, ← Over.comp_left, negT_whiskerRight]`. Rewrite using `[e1, e3, Category.id_comp]`.

Introduce `s t s' t' hact hs ht`. Unfold `IsActOf at hact ⊢`. Conclude with `GlobalTheory.TwistBaseChange.isTwistPull_baseChange S A L hL T T' h _ _ _ _ _ _ (translT_whiskerRight h θ.pt) k k θ.φ φ' θ.3 gφ' hcorr s t s' t' hact hs ht`.
-/
theorem exists_thetaGrp_pullback : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (k : ℤ) (T T' : Over S) (h : T' ⟶ T) (θ : ThetaGrp A L k T), ∃ θ' : ThetaGrp A L k T', θ'.pt = h ≫ θ.pt ∧ LB.Gen.Corr L _ _ _ _ θ'.φ (LB.pullGen L _ _ θ.φ (h ▷ A).left) ∧ (∀ (n : ℕ) (x : T ⟶ A), SymLift A L k n x θ → SymLift A L k n (h ≫ x) θ') ∧ ∀ (s t : LB.Sec (LPow A L k T)) (s' t' : LB.Sec (LPow A L k T')), IsActOf A L k θ s t → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L k (h ▷ A) (whiskerRight_snd _ _) t t' → IsActOf A L k θ' s' t' := by
  intro S A _ _ L hL k T T' h θ
  have hφ : (fun b => (h ▷ A).left ≫ (![(snd T A).left, (translPt A θ.pt).left] : Fin 2 → _) b) =
      ![(snd T' A).left, (translPt A (h ≫ θ.pt)).left] := by
    funext b
    fin_cases b
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← Over.comp_left, whiskerRight_snd]
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [← Over.comp_left, whiskerRight_translPt]
  obtain ⟨φ', gφ', vφ'⟩ :=
    exists_isGen_linComb_val_eq_of_eq hφ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ θ.φ θ.3 (h ▷ A).left)
  have vθ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
      val φ' r z J = val (L := L) (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
        (r ≫ (h ▷ A).left) z J :=
    fun Z r z J hJ => (vφ' Z r z J).trans (val_pull hJ _ _ r)
  have hcorr : LB.Gen.Corr L _ _ _ _ φ' (LB.pullGen L _ _ θ.φ (h ▷ A).left) :=
    corr_of_val hL fun y J _ => vφ' _ _ y J
  have hpow : ∀ j : ℕ, h ≫ θ.pt ^ j = (h ≫ θ.pt) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, pow_succ, comp_mul, ih]
  have hinv : h ≫ θ.pt⁻¹ = (h ≫ θ.pt)⁻¹ := GrpObj.comp_inv h θ.pt
  refine ⟨⟨h ≫ θ.pt, φ', gφ'⟩, rfl, hcorr, ?_, ?_⟩
  · intro n x hs
    obtain ⟨hpt, hpw, nu, gnu, hsym⟩ := hs
    refine ⟨?_, ?_, ?_⟩
    · show h ≫ θ.pt = h ≫ x
      rw [hpt]
    · refine corr_of_val hL fun y J hJ => ?_
      have hθ1 := val_corr hJ hpw (h ▷ A).left
      rw [val_one, val_powGen _ _ _ hJ] at hθ1
      rw [val_one, val_powGen _ _ _ hJ, ← hθ1]
      refine Finset.prod_congr rfl fun j _ => ?_
      dsimp only
      rw [vθ _ _ _ _ hJ]
      have e : (𝟙 _ ≫ (translT A ((h ≫ θ.pt) ^ (j : ℕ))).left) ≫ (h ▷ A).left =
          (h ▷ A).left ≫ (translT A (θ.pt ^ (j : ℕ))).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hpow, translT_whiskerRight]
      rw [e]
    · have hφn : (fun b => (h ▷ A).left ≫
            (![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] : Fin 2 → _) b) =
          ![(snd T' A).left, (snd T' A ≫ (GrpObj.inv : A ⟶ A)).left] := by
        funext b
        fin_cases b
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          rw [← Over.comp_left, whiskerRight_snd]
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
          rw [← Over.comp_left, whiskerRight_snd_assoc]
      obtain ⟨nu', gnu', vnu'⟩ :=
        exists_isGen_linComb_val_eq_of_eq hφn _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L _ _ nu gnu (h ▷ A).left)
      have vnu : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T' ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι), Good L z J →
          val nu' r z J = val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
            (ε := ![k, -k]) nu (r ≫ (h ▷ A).left) z J :=
        fun Z r z J hJ => (vnu' Z r z J).trans (val_pull hJ _ _ r)
      refine ⟨nu', gnu', corr_of_val hL fun y J hJ => ?_⟩
      have hθ2 := val_corr hJ hsym (h ▷ A).left
      rw [val_one, val_symGen _ _ _ hJ] at hθ2
      rw [val_one]
      refine (val_symGen _ _ _ hJ).trans ?_
      rw [← hθ2]
      dsimp only
      rw [vθ _ _ _ _ hJ, vθ _ _ _ _ hJ, vnu _ _ _ _ hJ, vnu _ _ _ _ hJ]
      have e1 : (𝟙 _ ≫ (translT A (h ≫ θ.pt)⁻¹).left) ≫ (h ▷ A).left =
          (h ▷ A).left ≫ (translT A θ.pt⁻¹).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← hinv, translT_whiskerRight]
      have e3 : (𝟙 _ ≫ (negT A T').left) ≫ (h ▷ A).left = (h ▷ A).left ≫ (negT A T).left := by
        rw [Category.id_comp, ← Over.comp_left, ← Over.comp_left, negT_whiskerRight]
      rw [e1, e3, Category.id_comp]
  · intro s t s' t' hact hs ht
    unfold IsActOf at hact ⊢
    exact GlobalTheory.TwistBaseChange.isTwistPull_baseChange S A L hL T T' h _ _ _ _ _ _
      (translT_whiskerRight h θ.pt) k k θ.φ φ' θ.3 gφ' hcorr s t s' t' hact hs ht

end GlobalTheory.ThetaPullback
