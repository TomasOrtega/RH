import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackProdInjectiveBirigidifiedGaloisIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.LbIsoLinComb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.HeckeSym

/- English proof (translation)
Unfold `GlobalTheory.UPel.HT.Hecke.sq2`. Rewrite using `[← Over.comp_left, ← Over.comp_left]`. Use `congr 1`. Apply the tactic sequence `ext <;> simp`.
-/
theorem grpSchemeSquareProductMap_comm_swap {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (ψ : A ⟶ A') :
    GlobalTheory.UPel.HT.Hecke.sq2 ψ ≫ (lift (snd A' A') (fst A' A')).left =
      (lift (snd A A) (fst A A)).left ≫ GlobalTheory.UPel.HT.Hecke.sq2 ψ := by
  unfold GlobalTheory.UPel.HT.Hecke.sq2
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp

/- English proof (translation)
Introduce `p _ D R _ b M S s o A' _ _ ψ G hA' hψ hG m P' hP' H r₁ r₂`. Use `set sw' := (lift (snd A' A') (fst A' A')).left with hsw'`. Use `set sw := (lift (snd o.A o.A) (fst o.A o.A)).left with hsw`. Use `set q := GlobalTheory.UPel.HT.Hecke.sq2 ψ with hq`. Establish `hQ : (P'.pull sw').IsLB` using `pull_isLB hP' sw'`.

Establish `ax : ∀ (e₁ e₂ : A' ⟶ G2 A'), e₁ ≫ lift (snd A' A') (fst A' A') = e₂ → (∃ t : (P'.pull e₂.left).Gen, t.IsGen) → ∃ t : ((P'.pull sw').pull e₁.left).Gen, t.IsGen`. Introduce `e₁ e₂ he ⟨t, ht⟩`. Establish `hc : ∀ k : PUnit, (fun _ : PUnit => e₁.left) k ≫ sw' = 𝟙 _ ≫ (fun _ : PUnit => e₂.left) k`. Introduce `_`. Rewrite using `[Category.id_comp, hsw', ← Over.comp_left, he]`.

Establish `iso : LBIso ((P'.pull sw').pull e₁.left) (P'.pull e₂.left)` using `LBIso.chartPull (chartPullLinComb P' sw' (fun _ => e₁.left) (fun _ => e₂.left) (fun _ => 1) (𝟙 _) hc) (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP' _))`. Conclude with `GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP' _) (pull_isLB hQ _) iso.symm t ht`. Apply the tactic sequence `have a₁ := ax (lift (1 : A' ⟶ A') (𝟙 A')) (lift (𝟙 A') (1 : A' ⟶ A')) (by ext <;> simp) r₂`. Apply the tactic sequence `have a₂ := ax (lift (𝟙 A') (1 : A' ⟶ A')) (lift (1 : A' ⟶ A') (𝟙 A')) (by ext <;> simp) r₁`. Establish `E` using `grpSchemeSquareProductMap_comm_swap ψ`.

Establish `hPow : (GlobalTheory.UPel.HT.Hecke.lbPow o.P m).IsLB` using `DVR.linComb_isLB _ o.isLB _ _`. Establish `step1 : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (LB.LinComb (o.P.pull sw) (K` using `Fin m) (fun _ => 𝟙 _) (fun _ => 1)) := GlobalTheory.PowPrimitive.lbIso_linComb o.symm _ _`. Establish `step2 : LBIso (LB.LinComb (o.P.pull sw) (K` using `Fin m) (fun _ => 𝟙 _) (fun _ => 1)) ((P'.pull sw').pull q) := by`. Use `LBIso.chartPull (h := sw) (chartPullLinComb o.P sw (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) sw (fun _ => by simp)) (chartPullLinComb P' sw' (fun _ : PUnit => q) (fun _ : PUnit => q) (fun _ => 1) sw (fun _ => E)) H` and prove the remaining obligations. Establish `hmid : (LB.LinComb (o.P.pull sw) (K` using `Fin m) (fun _ => 𝟙 _) (fun _ => 1)).IsLB := DVR.linComb_isLB _ (pull_isLB o.isLB _) _ _`.

Establish `key : LBIso (P'.pull q) ((P'.pull sw').pull q)` using `LBIso.trans (pull_isLB hP' q) hPow (pull_isLB hQ q) H.symm (LBIso.trans hPow hmid (pull_isLB hQ q) step1 step2)`. Conclude with `GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A A' G ψ o.ab hA' hψ hG P' (P'.pull sw') hP' hQ r₁ r₂ a₁ a₂ key`.
-/
theorem descended_symm : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A') (G : Subgroup (𝟙_ (Over S) ⟶ o.A)), IsAbelianScheme A' → IsMonHom ψ → GlobalTheory.ZM.IsGaloisCover G (fun h => (GlobalTheory.UPel.HT.Hecke.transl h.1).left) ψ.left → ∀ (m : ℕ) (P' : LB (G2 A').left), P'.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) → (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) → LBIso P' (P'.pull (lift (snd A' A') (fst A' A')).left) := by
  intro p _ D R _ b M S s o A' _ _ ψ G hA' hψ hG m P' hP' H r₁ r₂
  set sw' := (lift (snd A' A') (fst A' A')).left with hsw'
  set sw := (lift (snd o.A o.A) (fst o.A o.A)).left with hsw
  set q := GlobalTheory.UPel.HT.Hecke.sq2 ψ with hq
  have hQ : (P'.pull sw').IsLB := pull_isLB hP' sw'

  have ax : ∀ (e₁ e₂ : A' ⟶ G2 A'), e₁ ≫ lift (snd A' A') (fst A' A') = e₂ →
      (∃ t : (P'.pull e₂.left).Gen, t.IsGen) → ∃ t : ((P'.pull sw').pull e₁.left).Gen, t.IsGen := by
    intro e₁ e₂ he ⟨t, ht⟩
    have hc : ∀ k : PUnit, (fun _ : PUnit => e₁.left) k ≫ sw' = 𝟙 _ ≫ (fun _ : PUnit => e₂.left) k := by
      intro _
      rw [Category.id_comp, hsw', ← Over.comp_left, he]
    have iso : LBIso ((P'.pull sw').pull e₁.left) (P'.pull e₂.left) :=
      LBIso.chartPull (chartPullLinComb P' sw' (fun _ => e₁.left) (fun _ => e₂.left) (fun _ => 1) (𝟙 _) hc)
        (chartPullId _) (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hP' _))
    exact GlobalTheory.RigidTranslate.gen_of_lbIso (pull_isLB hP' _) (pull_isLB hQ _) iso.symm t ht
  have a₁ := ax (lift (1 : A' ⟶ A') (𝟙 A')) (lift (𝟙 A') (1 : A' ⟶ A')) (by ext <;> simp) r₂
  have a₂ := ax (lift (𝟙 A') (1 : A' ⟶ A')) (lift (1 : A' ⟶ A') (𝟙 A')) (by ext <;> simp) r₁

  have E := grpSchemeSquareProductMap_comm_swap ψ
  have hPow : (GlobalTheory.UPel.HT.Hecke.lbPow o.P m).IsLB := DVR.linComb_isLB _ o.isLB _ _
  have step1 : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m)
      (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb o.symm _ _
  have step2 : LBIso (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1))
      ((P'.pull sw').pull q) := by
    refine LBIso.chartPull (h := sw)
      (chartPullLinComb o.P sw (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) sw (fun _ => by simp))
      (chartPullLinComb P' sw' (fun _ : PUnit => q) (fun _ : PUnit => q) (fun _ => 1) sw (fun _ => E)) H
  have hmid : (LB.LinComb (o.P.pull sw) (K := Fin m) (fun _ => 𝟙 _) (fun _ => 1)).IsLB :=
    DVR.linComb_isLB _ (pull_isLB o.isLB _) _ _
  have key : LBIso (P'.pull q) ((P'.pull sw').pull q) :=
    LBIso.trans (pull_isLB hP' q) hPow (pull_isLB hQ q) H.symm
      (LBIso.trans hPow hmid (pull_isLB hQ q) step1 step2)
  exact GlobalTheory.T.pullback_prod_injective_birigidified_galois_isogeny S o.A A' G ψ o.ab hA' hψ hG P' (P'.pull sw') hP' hQ r₁ r₂ a₁ a₂ key

end GlobalTheory.HeckeSym
