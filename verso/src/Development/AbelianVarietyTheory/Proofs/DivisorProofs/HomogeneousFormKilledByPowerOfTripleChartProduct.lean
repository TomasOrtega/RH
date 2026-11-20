import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ProjectiveNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLoca
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormChartChangeCoeffIdealPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningTowerLiftedRatiosProjectiveRelationsStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg.TripleKill

/- English proof (translation)
Simplify using `only [rs]`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.
-/
theorem rs_rs {X : Scheme} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    rs X h2 (rs X h1 x) = rs X (h2.trans h1) x := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/- English proof (translation)
Introduce `R _ I Y β hpb n C e d F hF hI i j l h0`. Establish `hlev` using `(GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hpb n C).1`. Establish `htr` using `GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hpb n C e d F hF hI`. Establish `key : ∀ m, ∃ L : ℕ, (C.ρ e m i * C.ρ e m j * C.ρ e m l) ^ L * C.ev e m F = 0`. Introduce `m`.

Apply `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen _ (C.aff e m)` to reduce the goal to its premises. Establish `hb : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) = (C.D e m ⊓ C.D e i) ⊓ (C.D e m ⊓ C.D e j) ⊓ (C.D e m ⊓ C.D e l)`. Rewrite using `[Scheme.basicOpen_mul, Scheme.basicOpen_mul, hlev, hlev, hlev]`. Establish `hW1 : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) ≤ C.D e m ⊓ C.D e i` using `hb.le.trans (inf_le_left.trans inf_le_left)`. Establish `hW2 : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) ≤ C.D e i ⊓ C.D e j ⊓ C.D e l` using `hb.le.trans (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right)) (inf_le_left.trans (inf_le_right.trans inf_le_right))) (inf_le_right.trans inf_le_right))`.

Express the relevant statement in the definitionally equal form `rs (Y e).left ((Y e).left.basicOpen_le _) (C.ev e m F) = 0`. Establish `h1` using `(htr m i).2.2`. Establish `h2 : rs (Y e).left hW1 (rs (Y e).left (inf_le_left : C.D e m ⊓ C.D e i ≤ C.D e m) (C.ev e m F)) = 0`. Rewrite using `[h1, map_mul, rs_rs, ← rs_rs (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) hW2, h0, map_zero, mul_zero]`. Rewrite `h2` using `[rs_rs]`.

Conclude with `h2`. Use `choose Lf hL using key`. Use `⟨Finset.univ.sup Lf, fun m => ?_⟩` and prove the remaining obligations. Establish `hle : Lf m ≤ Finset.univ.sup Lf` using `Finset.le_sup (Finset.mem_univ m)`. Establish `hev : C.ev e m ((MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l) ^ Finset.univ.sup Lf * F) = (C.ρ e m i * C.ρ e m j * C.ρ e m l) ^ Finset.univ.sup Lf * C.ev e m F`.

Simplify using `[Charts.ev, map_mul, map_pow]`. Rewrite using `[hev, ← Nat.sub_add_cancel hle, pow_add (C.ρ e m i * C.ρ e m j * C.ρ e m l), mul_assoc, hL m, mul_zero]`.
-/
theorem ev_triple_kill : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d → (∀ m, MvPolynomial.coeff m F ∈ I ^ e) → ∀ i j l, rs (Y e).left (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) (C.ev e i F) = 0 → ∃ L : ℕ, ∀ m, C.ev e m ((MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l) ^ L * F) = 0 := by
  intro R _ I Y β hpb n C e d F hF hI i j l h0
  have hlev := (GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hpb n C).1
  have htr := GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hpb n C e d F hF hI
  have key : ∀ m, ∃ L : ℕ, (C.ρ e m i * C.ρ e m j * C.ρ e m l) ^ L * C.ev e m F = 0 := by
    intro m
    apply exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen _ (C.aff e m)
    have hb : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) =
        (C.D e m ⊓ C.D e i) ⊓ (C.D e m ⊓ C.D e j) ⊓ (C.D e m ⊓ C.D e l) := by
      rw [Scheme.basicOpen_mul, Scheme.basicOpen_mul, hlev, hlev, hlev]
    have hW1 : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) ≤ C.D e m ⊓ C.D e i :=
      hb.le.trans (inf_le_left.trans inf_le_left)
    have hW2 : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) ≤ C.D e i ⊓ C.D e j ⊓ C.D e l :=
      hb.le.trans (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (inf_le_left.trans (inf_le_right.trans inf_le_right))) (inf_le_right.trans inf_le_right))
    change rs (Y e).left ((Y e).left.basicOpen_le _) (C.ev e m F) = 0
    have h1 := (htr m i).2.2
    have h2 : rs (Y e).left hW1 (rs (Y e).left (inf_le_left : C.D e m ⊓ C.D e i ≤ C.D e m) (C.ev e m F)) = 0 := by
      rw [h1, map_mul, rs_rs, ← rs_rs (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) hW2, h0,
        map_zero, mul_zero]
    rw [rs_rs] at h2
    exact h2
  choose Lf hL using key
  refine ⟨Finset.univ.sup Lf, fun m => ?_⟩
  have hle : Lf m ≤ Finset.univ.sup Lf := Finset.le_sup (Finset.mem_univ m)
  have hev : C.ev e m ((MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l) ^ Finset.univ.sup Lf * F) =
      (C.ρ e m i * C.ρ e m j * C.ρ e m l) ^ Finset.univ.sup Lf * C.ev e m F := by
    simp [Charts.ev, map_mul, map_pow]
  rw [hev, ← Nat.sub_add_cancel hle, pow_add (C.ρ e m i * C.ρ e m j * C.ρ e m l), mul_assoc, hL m, mul_zero]

end GlobalTheory.FormalAlg.TripleKill
