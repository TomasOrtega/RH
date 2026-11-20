import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelCarry

/- English proof (translation)
The claim follows from `List.prod_ofFn`.
-/
theorem linComb_prod' {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) : linComb y a = ∏ i, y i ^ a i := List.prod_ofFn

/- English proof (translation)
The claim follows from `map_zpow _ _ _`.
-/
theorem unitOn_zpow' {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n :=
  map_zpow _ _ _

/- English proof (translation)
Introduce `a b h`. Apply `Units.ext` to reduce the goal to its premises. Establish `h'` using `congrArg Units.val h`. Simplify using `only [unitOn, Units.coe_map] at h'`. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective h'`.
-/
theorem unitOn_inj' {R : Type} [CommRing R] : Function.Injective (unitOn (R := R)) := by
  intro a b h
  apply Units.ext
  have h' := congrArg Units.val h
  simp only [unitOn, Units.coe_map] at h'
  exact (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective h'

end GlobalTheory.LevelCarry

open GlobalTheory.LevelCarry in

/- English proof (translation)
Introduce `K C _ _ _ f P P' io hW g k hg ζ lev hk`. Substitute `hg` using the available equality. Use `P'.isAb.comm` as an intermediate fact. Establish `hk0 : NeZero k` using `⟨by omega⟩`. Establish `E : ∀ c : Fin (2 * P'.g) → ℕ, linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c = linComb lev.pt c` using `fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))`.

Establish `LP : ∀ a, levelPoint lev rfl a = ∏ i, lev.pt i ^ (a i).val` using `fun a => by`. Rewrite using `[levelPoint_rfl]`. Conclude with `linComb_prod' _ _`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `IsPrimitiveRoot.of_map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.toMonoidHom) lev.prim unitOn_inj'`.

Introduce `a b`. Rewrite using `[← map_mul]`. Use `congr 1`. Rewrite using `[LP, LP, LP, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← pow_add, pow_eq_pow_mod ((a i).val + (b i).val) (lev.torsion i), Pi.add_apply, ZMod.val_add]`. Establish `inj : Function.Injective (levelPoint lev rfl)`. Introduce `a b h`. Establish `h₀` using `lev.indep C (𝟙 _) (fun i => ⟨(a i).val, ZMod.val_lt _⟩) (fun i => ⟨(b i).val, ZMod.val_lt _⟩) ((E _).trans (h.trans (E _).symm))`. Conclude with `funext fun i => ZMod.val_injective k (congrArg Fin.val (congrFun h₀ i))`.

Conclude with `io.symm.injective.comp inj`. Introduce `z hz`. Establish `hz' : (io z) ^ k = 1` using `by rw [← map_pow, hz, map_one]`. Take `⟨c, hc⟩` from `lev.span C (𝟙 _) (io z) hz'`. Use `⟨fun i => ((c i : ℕ) : ZMod k), ?_⟩` and prove the remaining obligations.

Rewrite using `[MulEquiv.symm_apply_eq, levelPoint_rfl, Level.toPt]`. Conclude with `(congrArg (linComb lev.pt) (funext fun i => ZMod.val_natCast_of_lt (c i).isLt)).trans ((E _).symm.trans hc)`. Introduce `i j haveI : Fact (1 < k) := ⟨by omega⟩`. Establish `hs : ∀ i, levelPoint lev rfl (Pi.single i 1) = lev.pt i` using `fun i => by`. Rewrite using `[LP, Finset.prod_eq_single i]`.

Rewrite using `[Pi.single_eq_same, ZMod.val_one, pow_one]`. Introduce `j _ hj`. Rewrite using `[Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.

Rewrite using `[hs, hs]`. Apply `hW` to reduce the goal to its premises. Rewrite using `[MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, unitOn_zpow']`. Conclude with `lev.pairing i j`.
-/
theorem GlobalTheory.levelPoint_baseChange_label : ∀ (K C : Type) [Field K] [Field C] [IsAlgClosed C] (f : K →+* C) (P : PolAV (Sp K))
    (P' : PolAV (Sp C)) (io : (Over.mk (spMap f) ⟶ P.A) ≃* (baseOver (Sp C) ⟶ P'.A)),
    (∀ (k : ℕ) a b (z : Γ(Sp C, ⊤)ˣ), WeilIs P'.A P'.L k (io a) (io b) z → WeilIs P.A P.L k a b z) →
    ∀ (g k : ℕ) (hg : P'.g = g) (ζ : Cˣ) (lev : Out.Level P' k (unitOn ζ)), 2 ≤ k →
      IsPrimitiveRoot ζ k ∧
      (∀ a b, io.symm (levelPoint lev hg (a + b)) = io.symm (levelPoint lev hg a) * io.symm (levelPoint lev hg b)) ∧
      Function.Injective (fun a => io.symm (levelPoint lev hg a)) ∧
      (∀ z : Over.mk (spMap f) ⟶ P.A, z ^ k = 1 → ∃ a, io.symm (levelPoint lev hg a) = z) ∧
      ∀ i j, WeilIs P.A P.L k (io.symm (levelPoint lev hg (Pi.single i 1))) (io.symm (levelPoint lev hg (Pi.single j 1)))
        (unitOn (ζ ^ stdSymp g i j)) := by
  intro K C _ _ _ f P P' io hW g k hg ζ lev hk
  subst hg
  have := P'.isAb.comm
  have hk0 : NeZero k := ⟨by omega⟩
  have E : ∀ c : Fin (2 * P'.g) → ℕ,
      linComb (fun i => (Over.homMk (𝟙 _) (by simp) : Over.mk (𝟙 _) ⟶ baseOver _) ≫ lev.pt i) c =
      linComb lev.pt c := fun c => congrArg (linComb · _) (funext fun i => Category.id_comp (lev.pt i))
  have LP : ∀ a, levelPoint lev rfl a = ∏ i, lev.pt i ^ (a i).val := fun a => by
    rw [levelPoint_rfl]; exact linComb_prod' _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsPrimitiveRoot.of_map_of_injective
      (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom.toMonoidHom) lev.prim unitOn_inj'
  · intro a b
    rw [← map_mul]
    congr 1
    rw [LP, LP, LP, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add, pow_eq_pow_mod ((a i).val + (b i).val) (lev.torsion i), Pi.add_apply, ZMod.val_add]
  · have inj : Function.Injective (levelPoint lev rfl) := by
      intro a b h
      have h₀ := lev.indep C (𝟙 _) (fun i => ⟨(a i).val, ZMod.val_lt _⟩) (fun i => ⟨(b i).val, ZMod.val_lt _⟩)
        ((E _).trans (h.trans (E _).symm))
      exact funext fun i => ZMod.val_injective k (congrArg Fin.val (congrFun h₀ i))
    exact io.symm.injective.comp inj
  · intro z hz
    have hz' : (io z) ^ k = 1 := by rw [← map_pow, hz, map_one]
    obtain ⟨c, hc⟩ := lev.span C (𝟙 _) (io z) hz'
    refine ⟨fun i => ((c i : ℕ) : ZMod k), ?_⟩
    rw [MulEquiv.symm_apply_eq, levelPoint_rfl, Level.toPt]
    exact (congrArg (linComb lev.pt) (funext fun i => ZMod.val_natCast_of_lt (c i).isLt)).trans
      ((E _).symm.trans hc)
  · intro i j
    haveI : Fact (1 < k) := ⟨by omega⟩
    have hs : ∀ i, levelPoint lev rfl (Pi.single i 1) = lev.pt i := fun i => by
      rw [LP, Finset.prod_eq_single i]
      · rw [Pi.single_eq_same, ZMod.val_one, pow_one]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hs, hs]
    apply hW
    rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, unitOn_zpow']
    exact lev.pairing i j
