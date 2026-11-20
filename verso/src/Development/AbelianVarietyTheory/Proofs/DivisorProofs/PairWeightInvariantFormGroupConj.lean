import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MinpolyIrreducibleNatDegreeOfRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixLineConjIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPositivityInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionDivisorSupport
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CxUnfold

/- English proof (translation)
Introduce `p _ G v wt Kf f hf K' f' hf' β x t hx η a y`. Establish `ha1 : (η • a).1 = LeftCosets.mk ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (((toAfF G β x t hx).prod (toP1 G β)) η * LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1)` using `by show η • a.1 = _ conv_lhs => rw [← LeftCosets.mk_rep a.1]`. Both sides reduce to the same expression. Take `⟨k, hk, hrep⟩` from `LeftCosets.rep_mk (ι := (toAfF G β x t hx).prod (toP1 G β)) (K := Kf.prod K') (((toAfF G β x t hx).prod (toP1 G β)) η * LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1)`. Rewrite `hrep` using `[← ha1]`.

Rewrite `hk` using `[Subgroup.mem_prod]`. Establish `hF : f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).1⁻¹ * toAfF G β x t hx (η * y * η⁻¹) * (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).1) = f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1). …`. Rewrite using `[hrep, ← hf k.1 hk.1 ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ * toAfF G β x t hx y * (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1)]`. Use `congr 1`. Simplify using `only [Prod.fst_mul, MonoidHom.prod_apply, map_mul, map_inv]`.

Use `group`. Establish `hF' : f' ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).2⁻¹ * toP1 G β (η * y * η⁻¹) * (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).2) = f' ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2⁻¹ * …`. Rewrite using `[hrep, ← hf' k.2 hk.2 ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2⁻¹ * toP1 G β y * (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2)]`. Use `congr 1`. Simplify using `only [Prod.snd_mul, MonoidHom.prod_apply, map_mul, map_inv]`.

Use `group`. Establish `hM : minpoly G.F ((((η * y * η⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = minpoly G.F ((((y : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)`. Establish `e : ((((η * y * η⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = (((η : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((((y : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((((η : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) : G.C)`. Simplify using `[Units.val_mul]`. Rewrite using `[e, minpoly_units_conj]`.

Take `⟨c, hc, hrepl⟩` from `rep_smul G v β η a.2`. Establish `hcond : (0 < (star (Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ (herm G v β *ᵥ Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))).re ∧ FixL G v β (η * y * η⁻¹) (Projectivization.rep (((η • a).2 : PLv G v β …`. Express the relevant statement in the definitionally equal form `(0 < (star (Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ (herm G v β *ᵥ Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))).re ∧ FixL G v β (η * y * η⁻¹) (Projectivization.rep ((η • a.2 : PLv G v β) : Projectivi …`. Rewrite using `[hrepl, fixL_smul_iff G v β _ _ c hc, ← fixL_conj_iff p G v β y η, ← pos_iff_smul_toV p G v β η _ c hc]`. Unfold `cxF`.

Distinguish the cases in `hca : (0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧ FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))))`. Rewrite using `[if_pos hca, if_pos (hcond.2 hca), hF, hF', hM]`. Rewrite using `[if_neg hca, if_neg (mt hcond.1 hca)]`.
-/
theorem cxF_smul_conj_gen : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F)
    (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ),
    (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ),
    (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t), ∀ (η : grp G β) (a : GlobalTheory.CxUnfold.Ys G v β x t hx Kf K') (y : grp G β),
    GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' (η • a) (η * y * η⁻¹) =
      GlobalTheory.CxUnfold.cxF G v wt β x t hx Kf f K' f' a y := by
  intro p _ G v wt Kf f hf K' f' hf' β x t hx η a y

  have ha1 : (η • a).1 = LeftCosets.mk ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K')
      (((toAfF G β x t hx).prod (toP1 G β)) η *
        LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1) := by
    show η • a.1 = _
    conv_lhs => rw [← LeftCosets.mk_rep a.1]
    rfl
  obtain ⟨k, hk, hrep⟩ := LeftCosets.rep_mk (ι := (toAfF G β x t hx).prod (toP1 G β))
    (K := Kf.prod K') (((toAfF G β x t hx).prod (toP1 G β)) η *
        LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1)
  rw [← ha1] at hrep
  rw [Subgroup.mem_prod] at hk
  have hF : f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).1⁻¹ *
        toAfF G β x t hx (η * y * η⁻¹) *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).1) =
      f ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ *
        toAfF G β x t hx y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1) := by
    rw [hrep, ← hf k.1 hk.1 ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1⁻¹ *
        toAfF G β x t hx y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).1)]
    congr 1
    simp only [Prod.fst_mul, MonoidHom.prod_apply, map_mul, map_inv]
    group
  have hF' : f' ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).2⁻¹ *
        toP1 G β (η * y * η⁻¹) *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') (η • a).1).2) =
      f' ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2⁻¹ *
        toP1 G β y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2) := by
    rw [hrep, ← hf' k.2 hk.2 ((LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2⁻¹ *
        toP1 G β y *
        (LeftCosets.rep ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1).2)]
    congr 1
    simp only [Prod.snd_mul, MonoidHom.prod_apply, map_mul, map_inv]
    group

  have hM : minpoly G.F ((((η * y * η⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      minpoly G.F ((((y : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := by
    have e : ((((η * y * η⁻¹ : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
        (((η : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) * ((((y : grp G β) : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) *
          ((((η : G.Cˣ × ℚˣ).1)⁻¹ : G.Cˣ) : G.C) := by
      simp [Units.val_mul]
    rw [e, minpoly_units_conj]

  obtain ⟨c, hc, hrepl⟩ := rep_smul G v β η a.2
  have hcond : (0 < (star (Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β (η * y * η⁻¹)
        (Projectivization.rep (((η • a).2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))) ↔
      (0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))) := by
    change (0 < (star (Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β (η * y * η⁻¹)
        (Projectivization.rep ((η • a.2 : PLv G v β) : Projectivization ℂ (Fin G.n → ℂ)))) ↔ _
    rw [hrepl, fixL_smul_iff G v β _ _ c hc, ← fixL_conj_iff p G v β y η,
      ← pos_iff_smul_toV p G v β η _ c hc]
  unfold cxF
  by_cases hca : (0 < (star (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))) ⬝ᵥ
        (herm G v β *ᵥ Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ)))).re ∧
      FixL G v β y (Projectivization.rep (a.2 : Projectivization ℂ (Fin G.n → ℂ))))
  · rw [if_pos hca, if_pos (hcond.2 hca), hF, hF', hM]
  · rw [if_neg hca, if_neg (mt hcond.1 hca)]

end GlobalTheory.CxUnfold
