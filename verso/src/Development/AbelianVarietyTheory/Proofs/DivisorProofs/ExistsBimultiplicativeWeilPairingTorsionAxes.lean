import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilCommutatorPairingTorsionGeometricPoint
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionCommPairing

open GlobalTheory.CechPic

/- English proof (translation)
Introduce `a b h`. Use `ext`. Use `congrArg (fun u : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u.val) h` as an intermediate fact. Simplify `this` using `[unitOn]`.
-/
theorem unitOn_inj {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  ext
  have := congrArg (fun u : (Γ(Sp R, ⊤))ˣ => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom u.val) h
  simpa [unitOn] using this

/- English proof (translation)
Use `⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom c, ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[unitOn]`.
-/
theorem unitOn_surj {R : Type} [CommRing R] (c : (Γ(Sp R, ⊤))ˣ) : ∃ z : Rˣ, unitOn z = c := by
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom c, ?_⟩
  ext
  simp [unitOn]

/- English proof (translation)
The claim follows from `map_mul _ a b`.
-/
theorem unitOn_mul {R : Type} [CommRing R] (a b : Rˣ) : unitOn (a * b) = unitOn a * unitOn b :=
  map_mul _ a b

/- English proof (translation)
Establish `hQ : (Hecke.lbPow L k).IsLB` using `LB.isLB_linComb hL _ _`. Establish `hcls : cls _ hQ = k • cls L hL`. Use `(cls_linComb hL (K := Fin k) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_` and prove the remaining obligations. Simplify using `[pull_id]`. Establish `h0` using `(cls_eq_zero_iff (LB.isLB_linComb hL _ _ : (Out.thetaLB B L (k : ℤ) θ.pt).IsLB)).2 ⟨θ.φ, θ.isGen⟩`.

Choose the witnesses or unpack the hypotheses as in `⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB B (Hecke.lbPow L k) 1 θ.pt), u.IsGen := by`. Use `(cls_eq_zero_iff (LB.isLB_linComb hQ _ _)).1 ?_` and prove the remaining obligations. Rewrite using `[cls_linComb hQ, Fin.sum_univ_two, hcls]`. Rewrite `h0` using `[cls_linComb hL, Fin.sum_univ_two]`. Simplify using `at h0 ⊢`.

Conclude with `h0`. Conclude with `⟨⟨_, u, hu⟩, rfl⟩`.
-/
theorem theta_lbPow {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (k : ℕ)
    {T : Over S} (θ : Out.ThetaGrp B L (k : ℤ) T) :
    ∃ θ' : Out.ThetaGrp B (Hecke.lbPow L k) 1 T, θ'.pt = θ.pt := by
  have hQ : (Hecke.lbPow L k).IsLB := LB.isLB_linComb hL _ _
  have hcls : cls _ hQ = k • cls L hL := by
    refine (cls_linComb hL (K := Fin k) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have h0 := (cls_eq_zero_iff (LB.isLB_linComb hL _ _ : (Out.thetaLB B L (k : ℤ) θ.pt).IsLB)).2 ⟨θ.φ, θ.isGen⟩
  obtain ⟨u, hu⟩ : ∃ u : LB.Gen (Out.thetaLB B (Hecke.lbPow L k) 1 θ.pt), u.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hQ _ _)).1 ?_
    rw [cls_linComb hQ, Fin.sum_univ_two, hcls]
    rw [cls_linComb hL, Fin.sum_univ_two] at h0
    simp at h0 ⊢
    exact h0
  exact ⟨⟨_, u, hu⟩, rfl⟩

/- English proof (translation)
Establish `hQ : (Hecke.lbPow L k).IsLB` using `LB.isLB_linComb hL _ _`. Use `CommutatorPairing.exists_weilIs GlobalTheory.globalFns_holds hB hQ (fun p => ?_) (fun p => ?_)` and prove the remaining obligations. Take `⟨V, hV, ⟨θx, -, hx, -⟩, -⟩` from `h p`. Take `⟨θ, hθ⟩` from `theta_lbPow hL k θx`. Conclude with `⟨V, hV, θ, hθ.trans hx⟩`.

Take `⟨V, hV, ⟨-, θy, -, hy⟩, -⟩` from `h p`. Take `⟨θ, hθ⟩` from `theta_lbPow hL k θy`. Conclude with `⟨V, hV, θ, hθ.trans hy⟩`.
-/
theorem exists_weilIs_lbPow {S : Scheme.{0}} {B : Over S} [GrpObj B] (hB : IsAbelianScheme B) {L : LB B.left}
    (hL : L.IsLB) (k : ℕ) {T : Over S} {x y : T ⟶ B} {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs B L (k : ℤ) x y c) :
    ∃ c' : Γ(T.left, ⊤)ˣ, Out.WeilIs B (Hecke.lbPow L k) 1 x y c' := by
  have hQ : (Hecke.lbPow L k).IsLB := LB.isLB_linComb hL _ _
  refine CommutatorPairing.exists_weilIs GlobalTheory.globalFns_holds hB hQ (fun p => ?_) (fun p => ?_)
  · obtain ⟨V, hV, ⟨θx, -, hx, -⟩, -⟩ := h p
    obtain ⟨θ, hθ⟩ := theta_lbPow hL k θx
    exact ⟨V, hV, θ, hθ.trans hx⟩
  · obtain ⟨V, hV, ⟨-, θy, -, hy⟩, -⟩ := h p
    obtain ⟨θ, hθ⟩ := theta_lbPow hL k θy
    exact ⟨V, hV, θ, hθ.trans hy⟩

/- English proof (translation)
Apply the tactic sequence `ext1 <;> simp only [MonObj.mul_comp, lift_fst, lift_snd]`.
-/
theorem lift_mul_lift {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x x' : T ⟶ A) (y y' : T ⟶ B) :
    lift x y * lift x' y' = lift (x * x') (y * y') := by
  ext1 <;> simp only [MonObj.mul_comp, lift_fst, lift_snd]

/- English proof (translation)
Apply the tactic sequence `ext1 <;> simp only [MonObj.pow_comp, lift_fst, lift_snd]`.
-/
theorem lift_pow {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x : T ⟶ A) (y : T ⟶ B) (m : ℕ) :
    lift x y ^ m = lift (x ^ m) (y ^ m) := by
  ext1 <;> simp only [MonObj.pow_comp, lift_fst, lift_snd]

/- English proof (translation)
Apply the tactic sequence `ext1 <;> simp only [MonObj.one_comp, lift_fst, lift_snd]`.
-/
theorem lift_one_one {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] :
    (1 : T ⟶ A ⊗ B) = lift (1 : T ⟶ A) (1 : T ⟶ B) := by
  ext1 <;> simp only [MonObj.one_comp, lift_fst, lift_snd]

/- English proof (translation)
Introduce `S A _ _ P hA hP κ _ _ x c hc`. Establish `hG : Out.GlobalFnsSt` using `GlobalTheory.globalFns_holds`. Establish `hAA : IsAbelianScheme (G2 A)` using `AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA`. Establish `hQ : (Hecke.lbPow P c).IsLB` using `LB.isLB_linComb hP _ _`. Establish `hc0 : 0 < c` using `Nat.pos_of_ne_zero fun h => hc (by rw [h, Nat.cast_zero])`.

Establish `ex : ∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 → ∃ z : κˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') (unitOn z)`. Introduce `g g' hg hg'`. Establish `hx : (lift g 1 : Over.mk x ⟶ G2 A) ^ c = 1` using `by rw [lift_pow, hg, one_pow, lift_one_one]`. Establish `hy : (lift 1 g' : Over.mk x ⟶ G2 A) ^ c = 1` using `by rw [lift_pow, hg', one_pow, lift_one_one]`. Take `⟨u, hu⟩` from `GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 A) P hAA hP κ x c hc0 hc _ _ hx hy`.

Take `⟨u', hu'⟩` from `exists_weilIs_lbPow hAA hP c hu`. Take `⟨z, rfl⟩` from `unitOn_surj u'`. Conclude with `⟨z, hu'⟩`. Set `e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ` to `fun g g' => if h : g ^ c = 1 ∧ g' ^ c = 1 then (ex g g' h.1 h.2).choose else 1`. Establish `he : ∀ g g' : Over.mk x ⟶ A, ∀ hg : g ^ c = 1, ∀ hg' : g' ^ c = 1, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') (unitOn (e g g'))`.

Introduce `g g' hg hg'`. Simplify using `only [e, dif_pos (And.intro hg hg')]`. Conclude with `(ex g g' hg hg').choose_spec`. Establish `hmulc : ∀ g₁ g₂ : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → (g₁ * g₂) ^ c = 1`. Introduce `g₁ g₂ h₁ h₂`.

Rewrite using `[mul_pow, h₁, h₂, _root_.one_mul]`. Use `⟨e, fun g g' hg hg' u => ⟨fun h => CommutatorPairing.weilIs_unique hG hAA hQ h (he g g' hg hg'), fun h => h ▸ he g g' hg hg'⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `g₁ g₂ g' h₁ h₂ h'`. Establish `hm` using `DiagPairing.weilIs_mul_left hG hAA hQ (he g₁ g' h₁ h') (he g₂ g' h₂ h')`. Rewrite `hm` using `[lift_mul_lift, _root_.mul_one]`.

Apply `unitOn_inj` to reduce the goal to its premises. Rewrite using `[unitOn_mul]`. Conclude with `CommutatorPairing.weilIs_unique hG hAA hQ (he _ _ (hmulc g₁ g₂ h₁ h₂) h') hm`. Introduce `g g₁ g₂ hg h₁ h₂`. Establish `hm` using `CommPairing.weilIs_symm hQ (DiagPairing.weilIs_mul_left hG hAA hQ (CommPairing.weilIs_symm hQ (he g g₁ hg h₁)) (CommPairing.weilIs_symm hQ (he g g₂ hg h₂)))`.

Rewrite `hm` using `[lift_mul_lift, _root_.mul_one, mul_inv, inv_inv, inv_inv]`. Apply `unitOn_inj` to reduce the goal to its premises. Rewrite using `[unitOn_mul]`. Conclude with `CommutatorPairing.weilIs_unique hG hAA hQ (he _ _ hg (hmulc g₁ g₂ h₁ h₂)) hm`.
-/
theorem exists_pairing : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (c : ℕ), (c : κ) ≠ 0 → ∃ e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ, (∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 → ∀ u : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') u ↔ u = unitOn (e g g')) ∧ (∀ g₁ g₂ g' : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → g' ^ c = 1 → e (g₁ * g₂) g' = e g₁ g' * e g₂ g') ∧ (∀ g g₁ g₂ : Over.mk x ⟶ A, g ^ c = 1 → g₁ ^ c = 1 → g₂ ^ c = 1 → e g (g₁ * g₂) = e g g₁ * e g g₂) := by
  intro S A _ _ P hA hP κ _ _ x c hc
  classical
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hQ : (Hecke.lbPow P c).IsLB := LB.isLB_linComb hP _ _
  have hc0 : 0 < c := Nat.pos_of_ne_zero fun h => hc (by rw [h, Nat.cast_zero])
  have ex : ∀ g g' : Over.mk x ⟶ A, g ^ c = 1 → g' ^ c = 1 →
      ∃ z : κˣ, Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') (unitOn z) := by
    intro g g' hg hg'
    have hx : (lift g 1 : Over.mk x ⟶ G2 A) ^ c = 1 := by rw [lift_pow, hg, one_pow, lift_one_one]
    have hy : (lift 1 g' : Over.mk x ⟶ G2 A) ^ c = 1 := by rw [lift_pow, hg', one_pow, lift_one_one]
    obtain ⟨u, hu⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 A) P hAA hP κ x c hc0 hc _ _ hx hy
    obtain ⟨u', hu'⟩ := exists_weilIs_lbPow hAA hP c hu
    obtain ⟨z, rfl⟩ := unitOn_surj u'
    exact ⟨z, hu'⟩
  let e : (Over.mk x ⟶ A) → (Over.mk x ⟶ A) → κˣ := fun g g' =>
    if h : g ^ c = 1 ∧ g' ^ c = 1 then (ex g g' h.1 h.2).choose else 1
  have he : ∀ g g' : Over.mk x ⟶ A, ∀ hg : g ^ c = 1, ∀ hg' : g' ^ c = 1,
      Out.WeilIs (G2 A) (Hecke.lbPow P c) 1 (lift g 1 : Over.mk x ⟶ G2 A) (lift 1 g') (unitOn (e g g')) := by
    intro g g' hg hg'
    simp only [e, dif_pos (And.intro hg hg')]
    exact (ex g g' hg hg').choose_spec
  have hmulc : ∀ g₁ g₂ : Over.mk x ⟶ A, g₁ ^ c = 1 → g₂ ^ c = 1 → (g₁ * g₂) ^ c = 1 := by
    intro g₁ g₂ h₁ h₂
    rw [mul_pow, h₁, h₂, _root_.one_mul]
  refine ⟨e, fun g g' hg hg' u => ⟨fun h => CommutatorPairing.weilIs_unique hG hAA hQ h (he g g' hg hg'),
    fun h => h ▸ he g g' hg hg'⟩, ?_, ?_⟩
  · intro g₁ g₂ g' h₁ h₂ h'
    have hm := DiagPairing.weilIs_mul_left hG hAA hQ (he g₁ g' h₁ h') (he g₂ g' h₂ h')
    rw [lift_mul_lift, _root_.mul_one] at hm
    apply unitOn_inj
    rw [unitOn_mul]
    exact CommutatorPairing.weilIs_unique hG hAA hQ (he _ _ (hmulc g₁ g₂ h₁ h₂) h') hm
  · intro g g₁ g₂ hg h₁ h₂
    have hm := CommPairing.weilIs_symm hQ (DiagPairing.weilIs_mul_left hG hAA hQ
      (CommPairing.weilIs_symm hQ (he g g₁ hg h₁)) (CommPairing.weilIs_symm hQ (he g g₂ hg h₂)))
    rw [lift_mul_lift, _root_.mul_one, mul_inv, inv_inv, inv_inv] at hm
    apply unitOn_inj
    rw [unitOn_mul]
    exact CommutatorPairing.weilIs_unique hG hAA hQ (he _ _ hg (hmulc g₁ g₂ h₁ h₂)) hm

end GlobalTheory.TorsionCommPairing
