import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NuChain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtDone
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `hs`.
-/
theorem secScal_cast {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (h : Y ⟶ G.left)
    (k : ℕ) {L1 L2 : RigLB G} (e : L1 = L2)
    (s1 : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ))))
    (σ1 : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (hs : GeneratorPullback.SecScal L1.L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) s1 (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ1 h 1) :
    GeneratorPullback.SecScal L2.L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) (e ▸ s1) (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
      (e ▸ σ1) h 1 := by
  subst e; exact hs

/- English proof (translation)
Introduce `E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hvK tK m w _ k hk F hF`. Take `⟨s, Ex, htie, hexp, hnu⟩` from `hF`. Use `haveI := t.semi.smooth`. Use `haveI := t.semi.separated`. Use `haveI := t.semi.quasiCompact`.

Take `⟨σ', hσ'⟩` from `nuExt V ϖ hϖ P.D Q hQ vK hvK P.A t.G P.U k hk s Ex hexp hnu`. Establish `hsc` using `secScal_cast (pullback.fst t.G.hom (Out.jK V)) k P.bundle s σ' hσ'`. Use `⟨P.bundle ▸ σ', fun Z r zp hzp z J J' hJ hJ' => ?_⟩` and prove the remaining obligations. Establish `e1` using `ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_sval hsc (r ≫ iotaK m) z hJ`. Rewrite `e1` using `[Category.assoc, iotaK, pullback.lift_fst]`.

Conclude with `e1.trans (htie Z r zp hzp z J J' hJ hJ')`.
-/
theorem nuReg : NuRegSt := by
  intro E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hvK tK m w _ k hk F hF
  obtain ⟨s, Ex, htie, hexp, hnu⟩ := hF
  haveI := t.semi.smooth
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  obtain ⟨σ', hσ'⟩ := nuExt V ϖ hϖ P.D Q hQ vK hvK P.A t.G P.U k hk s Ex hexp hnu
  have hsc := secScal_cast (pullback.fst t.G.hom (Out.jK V)) k P.bundle s σ' hσ'
  refine ⟨P.bundle ▸ σ', fun Z r zp hzp z J J' hJ hJ' => ?_⟩
  have e1 := ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_sval hsc (r ≫ iotaK m) z hJ
  rw [Category.assoc, iotaK, pullback.lift_fst] at e1
  exact e1.trans (htie Z r zp hzp z J J' hJ hJ')

/- English proof (translation)
Substitute `h` using the available equality. Substitute `h'` using the available equality. Both sides reduce to the same expression.
-/
theorem zCast_trans {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ k₃ : ℤ} (h : k₁ = k₂) (h' : k₂ = k₃)
    (F : LB.Sec (LPow A L k₁ T)) : zCast A h' (zCast A h F) = zCast A (h.trans h') F := by
  subst h; subst h'; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zCast_self {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k : ℤ} (h : k = k)
    (F : LB.Sec (LPow A L k T)) : zCast A h F = F := rfl

/- English proof (translation)
Introduce `E _ _ _ H V _ _ _ _ _ t P hTor θ _ M hMu tK m w hrig θK hθK t₀ F hVt`. Take `⟨ϖ, Q, vK, hϖ, hQ, hvK⟩` from `hN E H V t P`. Take `⟨t', α₀, α, s₁, U, hok1, hok2, hα₀, hnorm, hαc, htw, hsym, hact⟩` from `hVt`. Establish `hM1 : 1 ≤ M`. Break down `Nat.eq_zero_or_pos M with h | h` into its components or cases.

Substitute `h` using the available equality. Simplify using `at hMu`. Conclude with `h`. Establish `n0` using `hT E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig θ θK hθK`. Establish `n0' : NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm (zCast tK.G Nat.cast_one θK))`.

Rewrite using `[zCast_trans, zCast_self]`. Conclude with `n0`. Establish `n1` using `hM E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig M hM1 (zCast tK.G Nat.cast_one θK) α₀ α s₁ n0' hα₀ hnorm hαc htw`. Establish `hk : 0 < M ^ 2` using `pow_pos hM1 2`. Apply the tactic sequence `have n2 := hF E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig ((M : ℤ) ^ 2) (M ^ 2) (natCast_sq M) hk s₁ F t' U n1 (by first | exact hok1 | exact hok2) hsym hact`.

Conclude with `nuReg E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig (M ^ 2) hk (zCast tK.G (natCast_sq M) F) n2`.
-/
theorem regUnif_of (hN : NuDataSt) (hT : ThetaNuSt) (hM : MulNuSt) (hF : FinNuSt) : RegUnifSt := by
  intro E _ _ _ H V _ _ _ _ _ t P hTor θ _ M hMu tK m w hrig θK hθK t₀ F hVt
  obtain ⟨ϖ, Q, vK, hϖ, hQ, hvK⟩ := hN E H V t P
  obtain ⟨t', α₀, α, s₁, U, hok1, hok2, hα₀, hnorm, hαc, htw, hsym, hact⟩ := hVt
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMu
    · exact h
  have n0 := hT E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig θ θK hθK
  have n0' : NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm (zCast tK.G Nat.cast_one θK)) := by
    rw [zCast_trans, zCast_self]; exact n0
  have n1 := hM E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig M hM1 (zCast tK.G Nat.cast_one θK) α₀ α s₁ n0'
    hα₀ hnorm hαc htw
  have hk : 0 < M ^ 2 := pow_pos hM1 2
  have n2 := hF E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig ((M : ℤ) ^ 2) (M ^ 2) (natCast_sq M) hk s₁ F t' U n1
    (by first | exact hok1 | exact hok2) hsym hact
  exact nuReg E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig (M ^ 2) hk (zCast tK.G (natCast_sq M) F) n2

/- English proof (translation)
Introduce `E _ _ _ H V _ _ _ _ _ t P`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Use `choose Q hQ using fun χ => QForm.exists_QVal hϖ P.D χ`. Conclude with `⟨ϖ, Q, TG.vK hϖ, hϖ, hQ, TG.valOver_vK hϖ⟩`.
-/
theorem nuData : NuDataSt := by
  intro E _ _ _ H V _ _ _ _ _ t P
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using fun χ => QForm.exists_QVal hϖ P.D χ
  exact ⟨ϖ, Q, TG.vK hϖ, hϖ, hQ, TG.valOver_vK hϖ⟩

/- English proof (translation)
The claim follows from `regUnif_of nuData hT hM hF`.
-/
theorem regUnif_of' (hT : ThetaNuSt) (hM : MulNuSt) (hF : FinNuSt) : RegUnifSt := regUnif_of nuData hT hM hF

end ReciprocityTheory.ChartRestriction.G.PullbackSections
