import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymplecticSystem
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHoldStatement
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicOfSectionsOfVeryAmple

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelInhabitant

def halves (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

/- English proof (translation)
Establish `l : ∀ a, (halves g (.inl a) : ℕ) = a` using `fun _ => rfl`. Establish `r : ∀ a, (halves g (.inr a) : ℕ) = g + a` using `fun _ => rfl`. Establish `ll : ∀ i j, Out.stdSymp g (halves g (.inl i)) (halves g (.inl j)) = 0` using `fun i j => by`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact.

Simplify using `only [Out.stdSymp, l]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `rr : ∀ i j, Out.stdSymp g (halves g (.inr i)) (halves g (.inr j)) = 0` using `fun i j => by`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact.

Simplify using `only [Out.stdSymp, r]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `lr : ∀ i j, Out.stdSymp g (halves g (.inl i)) (halves g (.inr j)) = if i = j then 1 else 0` using `fun i j => by`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact.

Simplify using `only [Out.stdSymp, l, r, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> omega`. Establish `rl : ∀ i j, Out.stdSymp g (halves g (.inr i)) (halves g (.inl j)) = if i = j then -1 else 0` using `fun i j => by`. Use `i.2` as an intermediate fact. Use `j.2` as an intermediate fact.

Simplify using `only [Out.stdSymp, l, r, Fin.ext_iff]`. Apply the tactic sequence `split_ifs <;> omega`. Simplify using `only [Fintype.sum_sum_type, ll, rr, lr, rl, omegaStd, Finset.sum_sub_distrib]`. Simplify using `[sub_eq_add_neg, _root_.mul_comm]`.
-/
theorem sum_stdSymp {g : ℕ} (a b : Fin g ⊕ Fin g → ℤ) :
    ∑ i, ∑ j, Out.stdSymp g (halves g i) (halves g j) * b j * a i = omegaStd a b := by
  have l : ∀ a, (halves g (.inl a) : ℕ) = a := fun _ => rfl
  have r : ∀ a, (halves g (.inr a) : ℕ) = g + a := fun _ => rfl
  have ll : ∀ i j, Out.stdSymp g (halves g (.inl i)) (halves g (.inl j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l]
    split_ifs <;> omega
  have rr : ∀ i j, Out.stdSymp g (halves g (.inr i)) (halves g (.inr j)) = 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, r]
    split_ifs <;> omega
  have lr : ∀ i j, Out.stdSymp g (halves g (.inl i)) (halves g (.inr j)) = if i = j then 1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]
    split_ifs <;> omega
  have rl : ∀ i j, Out.stdSymp g (halves g (.inr i)) (halves g (.inl j)) = if i = j then -1 else 0 := fun i j => by
    have := i.2; have := j.2
    simp only [Out.stdSymp, l, r, Fin.ext_iff]
    split_ifs <;> omega
  simp only [Fintype.sum_sum_type, ll, rr, lr, rl, omegaStd, Finset.sum_sub_distrib]
  simp [sub_eq_add_neg, _root_.mul_comm]

/- English proof (translation)
Set `T : Subgroup G` to `(powMonoidHom k).ker`. Use `choose w hw hw' using fun x y : T => hW x y x.2 y.2`. Establish `wl : ∀ x x' y, w (x * x') y = w x y * w x' y` using `fun x x' y => (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm`. Establish `ws : ∀ x y, w y x = (w x y)⁻¹` using `fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm`. Establish `wr : ∀ x y y', w x (y * y') = w x y * w x y'` using `fun x y y' => by`.

Rewrite using `[ws _ x, wl, mul_inv, ← ws, ← ws]`. Set `e : T →* T →* U` to `MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x)) fun x x' => MonoidHom.ext fun y => wl x x' y`. Set `u : Fin g ⊕ Fin g → T` to `fun i => ⟨v (halves g i), hv _⟩`. Establish `hu : ∀ i j, e (u i) (u j) = ze ^ Out.stdSymp g (halves g i) (halves g j)` using `fun i j => (hw' (u i) (u j) _ (hp _ _)).symm`. Set `l : (Fin g ⊕ Fin g → ℤ) → T` to `fun a => ∏ i, u i ^ a i`.

Use `⟨fun a => (l a).1, fun x y => ?_, fun x => (l x).2, fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[← Subgroup.coe_mul]`. Use `congr 1`. Simplify using `only [l, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]`. Establish `: w (l x) (l y) = ze ^ omegaStd x y` using `by show e (l x) (l y) = _`.

Establish `z : ∀ {I : Type} [Fintype I] (n : I → ℤ), ze ^ ∑ i, n i = ∏ i, ze ^ n i` using `fun n => map_prod (zpowersHom U ze) (fun i => Multiplicative.ofAdd (n i)) _`. Establish `s : ∀ i, e.flip (l y) (u i) = ze ^ ∑ j, Out.stdSymp g (halves g i) (halves g j) * y j` using `fun i => by`. Rewrite using `[z, MonoidHom.flip_apply]`. Simplify using `only [l, map_prod, map_zpow, hu, ← zpow_mul]`. Rewrite using `[← sum_stdSymp, ← MonoidHom.flip_apply, z]`.

Use `show e.flip (l y) (∏ i, u i ^ x i) = _`. Simplify using `only [map_prod, map_zpow, s, ← zpow_mul, Finset.sum_mul]`. Conclude with `this ▸ hw _ _`.
-/
theorem exists_lev_of_rel {k g : ℕ} {G U : Type} [CommGroup G] [CommGroup U] {ze : U}
    (W : G → G → U → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c'))
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹) (v : Fin (2 * g) → G) (hv : ∀ i, v i ^ k = 1)
    (hp : ∀ i j, W (v i) (v j) (ze ^ Out.stdSymp g i j)) :
    ∃ lev : (Fin g ⊕ Fin g → ℤ) → G, (∀ x y, lev (x + y) = lev x * lev y) ∧ (∀ x, lev x ^ k = 1) ∧
      ∀ x y, W (lev x) (lev y) (ze ^ omegaStd x y) := by
  let T : Subgroup G := (powMonoidHom k).ker
  choose w hw hw' using fun x y : T => hW x y x.2 y.2
  have wl : ∀ x x' y, w (x * x') y = w x y * w x' y := fun x x' y =>
    (hw' _ _ _ (hmul _ _ _ _ _ (hw x y) (hw x' y))).symm
  have ws : ∀ x y, w y x = (w x y)⁻¹ := fun x y => (hw' _ _ _ (hsymm _ _ _ (hw x y))).symm
  have wr : ∀ x y y', w x (y * y') = w x y * w x y' := fun x y y' => by
    rw [ws _ x, wl, mul_inv, ← ws, ← ws]
  let e : T →* T →* U := MonoidHom.mk' (fun x => MonoidHom.mk' (w x) (wr x))
    fun x x' => MonoidHom.ext fun y => wl x x' y
  let u : Fin g ⊕ Fin g → T := fun i => ⟨v (halves g i), hv _⟩
  have hu : ∀ i j, e (u i) (u j) = ze ^ Out.stdSymp g (halves g i) (halves g j) := fun i j =>
    (hw' (u i) (u j) _ (hp _ _)).symm
  let l : (Fin g ⊕ Fin g → ℤ) → T := fun a => ∏ i, u i ^ a i
  refine ⟨fun a => (l a).1, fun x y => ?_, fun x => (l x).2, fun x y => ?_⟩
  · rw [← Subgroup.coe_mul]
    congr 1
    simp only [l, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · have : w (l x) (l y) = ze ^ omegaStd x y := by
      show e (l x) (l y) = _
      have z : ∀ {I : Type} [Fintype I] (n : I → ℤ), ze ^ ∑ i, n i = ∏ i, ze ^ n i := fun n =>
        map_prod (zpowersHom U ze) (fun i => Multiplicative.ofAdd (n i)) _
      have s : ∀ i, e.flip (l y) (u i) = ze ^ ∑ j, Out.stdSymp g (halves g i) (halves g j) * y j := fun i => by
        rw [z, MonoidHom.flip_apply]
        simp only [l, map_prod, map_zpow, hu, ← zpow_mul]
      rw [← sum_stdSymp, ← MonoidHom.flip_apply, z]
      show e.flip (l y) (∏ i, u i ^ x i) = _
      simp only [map_prod, map_zpow, s, ← zpow_mul, Finset.sum_mul]
    exact this ▸ hw _ _

end GlobalTheory.SiegelInhabitant

namespace GlobalTheory

open SiegelInhabitant in

/- English proof (translation)
Introduce `h k hk o _ em ζ hζ`. Establish `hL : Out.Laws` using `GlobalTheory.T.all_six_abelian_scheme_laws_hold.1`. Take `⟨P, -, -, hg, -⟩` from `polarisedTorus_algebraic h (Complex.I • (1 : Matrix (Fin h) (Fin h) ℂ)) 0 0 (Matrix.isSymm_one.smul _) (by`. Establish `: (Complex.I • (1 : Matrix (Fin h) (Fin h) ℂ)).map Complex.im = 1`. Use extensionality with `i j`.

Apply the tactic sequence `by_cases e : i = j <;> simp [Matrix.one_apply, e]`. Rewrite using `[this]`. Conclude with `Matrix.PosDef.one)`. Use the proof step `(fun _ => Or.inl rfl) (fun _ => Or.inl rfl)`. Substitute `hg` using the available equality.

Establish `hk' : (k : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 hk.ne'`. Set `ze : ℂˣ` to `(hζ.isUnit hk.ne').unit`. Establish `hze : IsPrimitiveRoot ze k` using `IsPrimitiveRoot.coe_units_iff.1 hζ`. Use `P.isAb.comm` as an intermediate fact. Take `⟨pt, hpt, hw⟩` from `EllipticLevel.exists_symplectic_system hL P k hk' ze hze`.

Take `⟨w₁, w₂, -⟩` from `hL.weil _ P k (Out.baseOver _)`. Take `⟨lev, add, tors, weil⟩` from `exists_lev_of_rel (G := Out.baseOver _ ⟶ P.A) (fun x y c => Out.WeilIs P.A P.L k x y c) w₁ w₂ (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) pt hpt hw`. Take `⟨c, φ, -, hc, -⟩` from `exists_siegPre_of_polAV hL GlobalTheory.T.theorem_of_cube_polAbelianScheme o ℂ em P.g k ζ ze P lev rfl hk' rfl hze add tors (fun x y => by`. Establish `e : unitOn (ze ^ omegaStd x y) = unitOn ze ^ omegaStd x y` using `map_zpow (Units.map _) _ _`. Rewrite using `[e]`.

Conclude with `weil x y)`. Use `⟨c, hc, ?_⟩` and prove the remaining obligations. Use `P.smoothDim` as an intermediate fact. Rewrite using `[← Over.w φ.hom]`. Establish `: IsIso φ.hom.left` using `inferInstanceAs (IsIso ((Over.forget _).map φ.hom))`.

Establish `H : SmoothOfRelativeDimension (0 + P.g) (φ.hom.left ≫ P.A.hom)` using `inferInstance`. Rewrite `H` using `[Nat.zero_add]`. Then use the resulting hypothesis.
-/
theorem exists_principal_siegPre_complex : ∀ (h k : ℕ), 0 < k → ∀ (o : Type) [CommRing o] (em : o →+* ℂ) (ζ : o), IsPrimitiveRoot (em ζ) k → ∃ c : SiegPre h k ζ (spMap em), c.Principal ∧ SmoothOfRelativeDimension h c.A.hom := by
  intro h k hk o _ em ζ hζ
  have hL : Out.Laws := GlobalTheory.T.all_six_abelian_scheme_laws_hold.1
  obtain ⟨P, -, -, hg, -⟩ := polarisedTorus_algebraic h (Complex.I • (1 : Matrix (Fin h) (Fin h) ℂ)) 0 0
    (Matrix.isSymm_one.smul _)
    (by
      have : (Complex.I • (1 : Matrix (Fin h) (Fin h) ℂ)).map Complex.im = 1 := by
        ext i j
        by_cases e : i = j <;> simp [Matrix.one_apply, e]
      rw [this]
      exact Matrix.PosDef.one)
    (fun _ => Or.inl rfl) (fun _ => Or.inl rfl)
  subst hg
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  let ze : ℂˣ := (hζ.isUnit hk.ne').unit
  have hze : IsPrimitiveRoot ze k := IsPrimitiveRoot.coe_units_iff.1 hζ
  have := P.isAb.comm
  obtain ⟨pt, hpt, hw⟩ := EllipticLevel.exists_symplectic_system hL P k hk' ze hze
  obtain ⟨w₁, w₂, -⟩ := hL.weil _ P k (Out.baseOver _)
  obtain ⟨lev, add, tors, weil⟩ := exists_lev_of_rel (G := Out.baseOver _ ⟶ P.A)
    (fun x y c => Out.WeilIs P.A P.L k x y c) w₁ w₂ (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) pt hpt hw
  obtain ⟨c, φ, -, hc, -⟩ := exists_siegPre_of_polAV hL GlobalTheory.T.theorem_of_cube_polAbelianScheme o ℂ em P.g k ζ ze P lev rfl hk' rfl hze add tors
    (fun x y => by
      have e : unitOn (ze ^ omegaStd x y) = unitOn ze ^ omegaStd x y := map_zpow (Units.map _) _ _
      rw [e]
      exact weil x y)
  refine ⟨c, hc, ?_⟩
  have := P.smoothDim
  rw [← Over.w φ.hom]
  have : IsIso φ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map φ.hom))
  have H : SmoothOfRelativeDimension (0 + P.g) (φ.hom.left ≫ P.A.hom) := inferInstance
  rwa [Nat.zero_add] at H

end GlobalTheory
