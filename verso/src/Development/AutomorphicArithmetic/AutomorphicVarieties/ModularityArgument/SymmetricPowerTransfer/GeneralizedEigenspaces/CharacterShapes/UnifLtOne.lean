import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RpExistsUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.GOpsEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ValInvAnti
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.IndicatorEqOneOfTrue
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.DiagonalParameterDominant
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.PosSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.ExpoEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.TFId0
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.BaseSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.FinG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.ExIota
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CommOfConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.FormsFin

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Rewrite using `[GlAx.unif_spec]`. Conclude with `ValuativeRel.uniformizer_lt_one`.
-/
private theorem unif_lt_one (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (unif k : k) < 1 := by
  rw [GlAx.unif_spec]
  exact ValuativeRel.uniformizer_lt_one

variable {F : Type} [Field F] [NumberField F] {Δ : F} (A : SD Δ)

private def coneS : Subsemigroup (Dat.Par F) where
  carrier := {t | A.Cone t}
  mul_mem' {a b} ha hb v hv := by
    have h1 := ha v hv
    have h2 := hb v hv
    have h3 : valuation (Kv v) (unif (Kv v) : Kv v) ^ 2 ≤ 1 := pow_le_one₀ zero_le (le_of_lt (unif_lt_one _))
    rw [Pi.mul_apply, Units.val_mul, map_mul]
    exact (mul_le_of_le_one_right' (h2.le.trans h3)).trans_lt h1

/- English proof (translation)
Introduce `h`. Establish `hp : A.Cone fun v => unif (Kv v) ^ 3` using `fun v _ => by`. Rewrite using `[Units.val_pow_eq_pow_val, map_pow]`. Conclude with `pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))) (unif_lt_one _) (by norm_num)`. Use `congrFun h ⟨_, hp⟩` as an intermediate fact.

Conclude with `Finset.prod_ne_zero_iff.2 (fun v _ => ((expoEq (Kv v) (a v)).2.2 2 _).1 _) this`.
-/
private theorem exS_ne (a : Chs F) : (fun p : coneS A => A.exS a p.1) ≠ 0 := by
  intro h
  have hp : A.Cone fun v => unif (Kv v) ^ 3 := fun v _ => by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))) (unif_lt_one _) (by norm_num)
  have := congrFun h ⟨_, hp⟩
  exact Finset.prod_ne_zero_iff.2 (fun v _ => ((expoEq (Kv v) (a v)).2.2 2 _).1 _) this

/- English proof (translation)
Establish `h` using `elEx F Δ A hA`. Establish `h2` using `(h.2.1 (SD.dS t)).exists`. Conclude with `h2.elim fun g hg => ⟨⟨g, h.2.2.2.2 g t hg⟩, hg⟩`.
-/
private theorem elS (hA : A.Ok) (t : Dat.Par F) : ∃ g : SA Δ, A.IsElD g (SD.dS t) := by
  have h := elEx F Δ A hA
  have h2 := (h.2.1 (SD.dS t)).exists
  exact h2.elim fun g hg => ⟨⟨g, h.2.2.2.2 g t hg⟩, hg⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Take `⟨g, hg⟩` from `elS A hA t`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[(sOps F Δ A hA V ch x B hx hB).2.1 t g ht hg φ]`. Conclude with `hE t g ht hg`.
-/
private theorem eigS (hA : A.Ok) (ch : F → ℂ) (x : DA Δ) (B : Base (SU Δ) (SA Δ) V) (hx : A.dat.Off x) (hB : A.dat.IsBS ch x B)
    (a : Chs F) (φ : B.Forms) (hE : A.EigS B.U φ.1 a) (t : Dat.Par F) (ht : A.Cone t) :
    (Base.Tw.one B).R (A.dat.FSx t x) φ = A.exS a t • φ := by
  obtain ⟨g, hg⟩ := elS A hA t
  apply Subtype.ext
  rw [(sOps F Δ A hA V ch x B hx hB).2.1 t g ht hg φ]
  exact hE t g ht hg

/- English proof (translation)
Establish `hW` using `fun i => baseS F Δ D hD V B.W ch hB.tr (y i)`. Use `⟨fun i => if i = 0 then B else (hW i).choose, fun i => ?_, by simp⟩` and prove the remaining obligations. Distinguish the cases in `h : i = 0`. Substitute `h` using the available equality. Simplify using `using hB`.

Simplify using `only [h, ↓reduceIte]`. Conclude with `(hW i).choose_spec.1`.
-/
private theorem bases (D : Dat Δ) (hD : D.Ok) (ch : F → ℂ) {n : ℕ} (y : Fin (n + 1) → DA Δ) (B : Base (SU Δ) (SA Δ) V)
    (hB : D.IsBS ch (y 0) B) : ∃ B' : Fin (n + 1) → Base (SU Δ) (SA Δ) V, (∀ i, D.IsBS ch (y i) (B' i)) ∧ B' 0 = B := by
  classical
  have hW := fun i => baseS F Δ D hD V B.W ch hB.tr (y i)
  refine ⟨fun i => if i = 0 then B else (hW i).choose, fun i => ?_, by simp⟩
  by_cases h : i = 0
  · subst h
    simpa using hB
  · simp only [h, ↓reduceIte]
    exact (hW i).choose_spec.1

/- English proof (translation)
Introduce `F _ _ Δ A hA VG VS VK _ _ _ _ _ _ _ _ _ ch BG s x BS BK hG hx hS hK a φ hφ h0 hE`. Establish `hD` using `(datOk F Δ A hA).1`. Establish `hC` using `(datOk F Δ A hA).2.1`. Use `(tFId0 F Δ A.dat hD x hx).elim fun n H => H.elim fun y H => H.elim fun c₁ H => H.elim fun c₂ H => ?_` and prove the remaining obligations. Establish `hy` using `H.2.1`.

Use `(bases A.dat hD ch y BS (H.1 ▸ hS)).elim fun B' hB => ?_` and prove the remaining obligations. Establish `hB'` using `hB.1`. Establish `e0` using `hB.2`. Substitute `e0` using the available equality. Use `haveI : FiniteDimensional ℂ BG.Forms := Tf.formsFin _ _ _ BG (finG F Δ A.dat hD VG ch BG s hG).1`.

Use `haveI : FiniteDimensional ℂ BK.Forms := Tf.formsFin _ _ _ BK (finK F Δ A.dat hD VK ch BK hK).1`. Use `haveI : ∀ i, FiniteDimensional ℂ (B' i).Forms := fun i => Tf.formsFin _ _ _ (B' i) (finS F Δ A.dat hD VS ch (y i) (B' i) (hB' i)).1`. Use `(gOpsEx F Δ A hA VG ch BG s hG).elim fun u hu => hu.elim fun Θ hu => ?_` and prove the remaining obligations. Use `(gSpec F Δ A hA VG BG s u Θ hu).elim fun I h => h.elim fun X h => h.elim fun b h => h.elim fun β h => ?_` and prove the remaining obligations. Establish `k` using `kSpec F Δ A hA VK ch BK hK`.

Establish `key` using `posSpec (coneS A) BK.Forms I (Fin (n + 1)) (fun i => (B' i).Forms) (fun i p => (Base.Tw.one (B' i)).R (A.dat.FSx p.1 (y i))) (fun p => (Base.Tw.one BK).R (A.dat.FK p.1)) (fun i p q => (sOps F Δ A hA VS ch (y i) (B' i) (hy i) (hB' i)).2.2 p.1 q.1 p.2 q.2) (fun p q => k.1 p.1 q.1 p …`. Use `key.elim (fun e => e.elim fun i e => ?_) fun e => e.elim fun v e => ?_` and prove the remaining obligations. Conclude with `Or.inl (h.2.2 i e.1 e.2.1 a fun t ht => congrFun e.2.2 ⟨t, ht⟩)`. Conclude with `Or.inr ⟨v.1, v.2, fun h => e.1 (Subtype.ext h), k.2 a v fun t ht => e.2 ⟨t, ht⟩⟩`.
-/
theorem UpperTheory.V.Z.Sym.So.specF : SpecF := by
  intro F _ _ Δ A hA VG VS VK _ _ _ _ _ _ _ _ _ ch BG s x BS BK hG hx hS hK a φ hφ h0 hE
  have hD := (datOk F Δ A hA).1
  have hC := (datOk F Δ A hA).2.1
  refine (tFId0 F Δ A.dat hD x hx).elim fun n H => H.elim fun y H => H.elim fun c₁ H => H.elim fun c₂ H => ?_
  have hy := H.2.1
  refine (bases A.dat hD ch y BS (H.1 ▸ hS)).elim fun B' hB => ?_
  have hB' := hB.1
  have e0 := hB.2
  subst e0
  haveI : FiniteDimensional ℂ BG.Forms := Tf.formsFin _ _ _ BG (finG F Δ A.dat hD VG ch BG s hG).1
  haveI : FiniteDimensional ℂ BK.Forms := Tf.formsFin _ _ _ BK (finK F Δ A.dat hD VK ch BK hK).1
  haveI : ∀ i, FiniteDimensional ℂ (B' i).Forms := fun i => Tf.formsFin _ _ _ (B' i) (finS F Δ A.dat hD VS ch (y i) (B' i) (hB' i)).1
  refine (gOpsEx F Δ A hA VG ch BG s hG).elim fun u hu => hu.elim fun Θ hu => ?_
  refine (gSpec F Δ A hA VG BG s u Θ hu).elim fun I h => h.elim fun X h => h.elim fun b h => h.elim fun β h => ?_
  have k := kSpec F Δ A hA VK ch BK hK
  have key := posSpec (coneS A) BK.Forms I (Fin (n + 1)) (fun i => (B' i).Forms)
    (fun i p => (Base.Tw.one (B' i)).R (A.dat.FSx p.1 (y i))) (fun p => (Base.Tw.one BK).R (A.dat.FK p.1))
    (fun i p q => (sOps F Δ A hA VS ch (y i) (B' i) (hy i) (hB' i)).2.2 p.1 q.1 p.2 q.2) (fun p q => k.1 p.1 q.1 p.2 q.2)
    X b (fun i p => β i p.1) (fun i hi p q => h.1 i hi p.1 q.1 p.2 q.2) c₁ c₂ H.2.2.1
    (fun p => (h.2.1 p.1 p.2).symm.trans (H.2.2.2 VG VS VK ch BG s B' BK hG hB' hK p.1 ((hC _).2 p.2))) _ (exS_ne A a)
    ⟨0, ⟨φ, hφ⟩, fun h => h0 (congrArg Subtype.val h), fun p => eigS A hA ch (y 0) (B' 0) (hy 0) (hB' 0) a ⟨φ, hφ⟩ hE p.1 p.2⟩
  refine key.elim (fun e => e.elim fun i e => ?_) fun e => e.elim fun v e => ?_
  · exact Or.inl (h.2.2 i e.1 e.2.1 a fun t ht => congrFun e.2.2 ⟨t, ht⟩)
  · exact Or.inr ⟨v.1, v.2, fun h => e.1 (Subtype.ext h), k.2 a v fun t ht => e.2 ⟨t, ht⟩⟩

end
