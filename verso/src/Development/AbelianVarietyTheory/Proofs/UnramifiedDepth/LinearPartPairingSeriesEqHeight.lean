import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NEvalSqZero

set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

/- English proof (translation)
Introduce `R₀ _ B p Tw Dt g Y gb S hS τ u hu hP ht hH`. Use function extensionality and compare the values at `l`. Rewrite using `[← sub_eq_zero]`. Use `Tw.sep _ fun n => (Dt.Dp n).free _ ?_` and prove the remaining obligations. Use `set Dp := Dt.Dp n`.

Take `⟨z, hz, hz'⟩` from `hH n (gb l)`. Set `s : LHom Tw.O Dp.D` to `Dp.σ.comp (Tw.q n)`. Establish `hs : ∀ x, s.1 x = Dp.σ.1 ((Tw.q n).1 x)` using `fun _ => rfl`. Establish `hc : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type)) = 0`. Rewrite using `[← map_natCast (Tw.π n).1, Tw.char n, map_zero]`.

Establish `hp : IsNilpotent (p : (Dp.D : Type))` using `⟨n + 1, by rw [← Nat.cast_pow, ← map_natCast Dp.σ.1, hc, map_zero]⟩`. Establish `hsq : ∀ x y : (Dp.D : Type), x * Dp.η * (y * Dp.η) = 0` using `fun x y => by`. Rewrite using `[_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]`. Establish `ha : ∀ k, IsNilpotent (s.1 (S k l) * Dp.η)` using `fun k => ⟨2, by rw [pow_two, hsq]⟩`. Rewrite `hz` using `[hS Dp.D _ s Dp.π Dp.sqZero l Dp.ηk, ← B.map_comp]`.

Establish `h1` using `hP Dp.D s (fun k => s.1 (S k l) * Dp.η) n z hp ha hz`. Establish `h2` using `(nv_calculus _ _ s.1.toRingHom 1 g ![fun k => s.1 (S k l) * Dp.η] (fun i j => by simpa using ha j)).2.2.2.2.2 (fun i j i' j' => by simpa using hsq _ _) u`. Rewrite `h1` using `[h2, hz', hu, map_one, add_right_inj, Fintype.sum_prod_type, Fin.sum_univ_one]`. Rewrite using `[← hs, map_sub, sub_mul, sub_eq_zero]`. Use `Eq.trans ?_ h1.symm` and prove the remaining obligations.

Simplify using `only [mulVec, dotProduct, transpose_apply, dl, map_sum, map_mul, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_fin_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dl_pairSer_eq_height : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (p : ℕ) (Tw : ATowerL R₀ p) (Dt : DualTower Tw) (g : ℕ) (Y : ∀ R : LAlg R₀, LHom Tw.O R → (Fin g → (R : Type)) → B.G R) (gb : Module.Basis (Fin g) R₀ B.gg) (S : Matrix (Fin g) (Fin g) (Tw.O : Type)), TanMat B Tw.O Y gb S → ∀ (τ : ℕ → B.G Tw.O) (u : PS (Tw.O : Type) 1 g), MvPowerSeries.constantCoeff u = 1 → PairSer B Tw.O Y p τ u → ∀ ht : B.gg →ₗ[R₀] (Tw.O : Type), (∀ n, B.IsHeight (Dt.Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ n)) ((Tw.q n).1.toLinearMap ∘ₗ ht)) → Sᵀ *ᵥ dl u = fun l => ht (gb l) := by
  intro R₀ _ B p Tw Dt g Y gb S hS τ u hu hP ht hH
  funext l
  rw [← sub_eq_zero]
  refine Tw.sep _ fun n => (Dt.Dp n).free _ ?_
  set Dp := Dt.Dp n
  obtain ⟨z, hz, hz'⟩ := hH n (gb l)
  let s : LHom Tw.O Dp.D := Dp.σ.comp (Tw.q n)
  have hs : ∀ x, s.1 x = Dp.σ.1 ((Tw.q n).1 x) := fun _ => rfl
  have hc : ((p ^ (n + 1) : ℕ) : (Tw.R n : Type)) = 0 := by
    rw [← map_natCast (Tw.π n).1, Tw.char n, map_zero]
  have hp : IsNilpotent (p : (Dp.D : Type)) :=
    ⟨n + 1, by rw [← Nat.cast_pow, ← map_natCast Dp.σ.1, hc, map_zero]⟩
  have hsq : ∀ x y : (Dp.D : Type), x * Dp.η * (y * Dp.η) = 0 := fun x y => by
    rw [_root_.mul_mul_mul_comm, Dp.η_sq, mul_zero]
  have ha : ∀ k, IsNilpotent (s.1 (S k l) * Dp.η) := fun k => ⟨2, by rw [pow_two, hsq]⟩
  rw [hS Dp.D _ s Dp.π Dp.sqZero l Dp.ηk, ← B.map_comp] at hz
  have h1 := hP Dp.D s (fun k => s.1 (S k l) * Dp.η) n z hp ha hz
  have h2 := (nv_calculus _ _ s.1.toRingHom 1 g ![fun k => s.1 (S k l) * Dp.η]
    (fun i j => by simpa using ha j)).2.2.2.2.2 (fun i j i' j' => by simpa using hsq _ _) u
  rw [h2, hz', hu, map_one, add_right_inj, Fintype.sum_prod_type, Fin.sum_univ_one] at h1
  rw [← hs, map_sub, sub_mul, sub_eq_zero]
  refine Eq.trans ?_ h1.symm
  simp only [mulVec, dotProduct, transpose_apply, dl, map_sum, map_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.cons_val_fin_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  ring

end GlobalTheory.ChF
