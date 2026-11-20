import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuTwistedTupleRamifiedAtTwistPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistAndNuRamifiedPlaceDegreeOneExponentTwo
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.NuExpModulus

open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.SqTop

/- English proof (translation)
Introduce `x hx hv` and use `h x hx (hv.trans (WithZero.exp_le_exp.2 (by omega)))`.
-/
theorem levelLe_mono {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {m n : ℕ}
    (h : χ.LevelLe w m) (hmn : m ≤ n) : χ.LevelLe w n := fun x hx hv =>
  h x hx (hv.trans (WithZero.exp_le_exp.2 (by omega)))

/- English proof (translation)
Establish `a` using `(hc _).1 h1`. Establish `b` using `(hc n).not.1 h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem exp_eq {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {c n : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt χ w c) (h1 : χ.LevelLe w (n + 1)) (h2 : ¬ χ.LevelLe w n) : c = n + 1 := by
  have a := (hc _).1 h1
  have b := (hc n).not.1 h2
  omega

/- English proof (translation)
Use `exp_eq hc ?_ fun h => h2 ?_` and prove the remaining obligations. Rewrite using `[div_eq_mul_inv]`. Conclude with `Formalism.L2.Host.HChar.LevelLe.mul (levelLe_mono ha (Nat.le_succ n)) (Formalism.L2.Host.HChar.LevelLe.inv h1)`. Establish `e : b = a * (a / b)⁻¹` using `by rw [inv_div, mul_div_cancel]`. Rewrite using `[e]`.

Conclude with `Formalism.L2.Host.HChar.LevelLe.mul ha (Formalism.L2.Host.HChar.LevelLe.inv h)`.
-/
theorem exp_div {E : Type} [Field E] [NumberField E] {a b : Formalism.L2.Host.HChar E} {w : HeightOneSpectrum (𝓞 E)} {c n : ℕ}
    (hc : GlobalTheory.CMVal.ExpAt (a / b) w c) (ha : a.LevelLe w n) (h1 : b.LevelLe w (n + 1)) (h2 : ¬ b.LevelLe w n) :
    c = n + 1 := by
  refine exp_eq hc ?_ fun h => h2 ?_
  · rw [div_eq_mul_inv]
    exact Formalism.L2.Host.HChar.LevelLe.mul (levelLe_mono ha (Nat.le_succ n)) (Formalism.L2.Host.HChar.LevelLe.inv h1)
  · have e : b = a * (a / b)⁻¹ := by rw [inv_div, mul_div_cancel]
    rw [e]
    exact Formalism.L2.Host.HChar.LevelLe.mul ha (Formalism.L2.Host.HChar.LevelLe.inv h)

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

/- English proof (translation)
Use `(L.C.isMu0 j).unr P fun k hk => hS ((S1_mem_OmF D).2 ?_)` and prove the remaining obligations. Establish `: ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal` using `by show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal`. Rewrite using `[map_natCast]`. Conclude with `hk`. Use `fin_cases k`.

Conclude with `Or.inl this`. Conclude with `Or.inr (Or.inl this)`.
-/
theorem gridBaseCharacter_unramified_off_badPlaces (j : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)} (hS : P.under (𝓞 D.host.F) ∉ S1 D) :
    (L.C.mu0 j).UnrAt P := by
  refine (L.C.isMu0 j).unr P fun k hk => hS ((S1_mem_OmF D).2 ?_)
  have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (P.under (𝓞 D.host.F)).asIdeal := by
    show algebraMap _ (𝓞 D.host.E) _ ∈ P.asIdeal
    rw [map_natCast]; exact hk
  fin_cases k
  · exact Or.inl this
  · exact Or.inr (Or.inl this)

/- English proof (translation)
Establish `a1 : 1 ≤ D.R.m - i` using `by have := i.2; omega`. Establish `a2 : D.R.m - i ≤ D.R.m` using `by omega`. Establish `hu` using `G.pl.under_w hv`. Distinguish the cases in `h0 : v = G.pl.v0`. Rewrite using `[condExp, if_pos h0]`.

Establish `hu0 : (G.pl.w v).under (𝓞 D.host.F) = G.pl.v0` using `hu.trans h0`. Take `⟨l1, l2⟩` from `G.ch.lev0 _ a1 a2 _ hu0`. Establish `hmu : (L.C.mu0 j).UnrAt (G.pl.w v)` using `gridBaseCharacter_unramified_off_badPlaces j (by rw [hu0]; exact G.ch.basePlace_not_mem_chiGridBadPlaces)`. Establish `hxi : (L.xiH t).UnrAt (G.pl.w v)`. Assume the negation of the conclusion as `hn`.

Break down `(hL.Q_ram t _).1 hn with hq | ⟨PP', hq, hcj⟩` into its components or cases. Conclude with `G.pl.levelPlace_ne_basePlace t _ hq hu0`. Conclude with `G.pl.levelPlace_ne_basePlace t _ hq ((GlobalTheory.BadPlaceExp.under_eq_of_isConjPl hcj).trans hu0)`. Conclude with `exp_div (n := 0) hc (Formalism.L2.Host.HChar.UnrAt.levelLe (hmu.mul hxi) 0) l1 (fun h => l2 ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h))`. Rewrite using `[condExp, if_neg h0]`.

Establish `h1 : v ∈ S1 D` using `(G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0`. Take `⟨l1, l2⟩` from `G.ch.lev1 _ a1 a2 (G.pl.w v) (by rw [hu]; exact h1)`. Conclude with `exp_div (n := 1) hc (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame _) (hL.xi_tame t _)) l1 l2`.
-/
theorem exp_w (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {v : HeightOneSpectrum (𝓞 D.host.F)}
    (hv : v ∈ G.pl.S0) {c : ℕ} (hc : GlobalTheory.CMVal.ExpAt (nuH G t i j) (G.pl.w v) c) : c = condExp G.pl v := by
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hu := G.pl.under_w hv
  by_cases h0 : v = G.pl.v0
  · rw [condExp, if_pos h0]
    have hu0 : (G.pl.w v).under (𝓞 D.host.F) = G.pl.v0 := hu.trans h0
    obtain ⟨l1, l2⟩ := G.ch.lev0 _ a1 a2 _ hu0
    have hmu : (L.C.mu0 j).UnrAt (G.pl.w v) := gridBaseCharacter_unramified_off_badPlaces j (by rw [hu0]; exact G.ch.basePlace_not_mem_chiGridBadPlaces)
    have hxi : (L.xiH t).UnrAt (G.pl.w v) := by
      by_contra hn
      rcases (hL.Q_ram t _).1 hn with hq | ⟨PP', hq, hcj⟩
      · exact G.pl.levelPlace_ne_basePlace t _ hq hu0
      · exact G.pl.levelPlace_ne_basePlace t _ hq ((GlobalTheory.BadPlaceExp.under_eq_of_isConjPl hcj).trans hu0)
    exact exp_div (n := 0) hc (Formalism.L2.Host.HChar.UnrAt.levelLe (hmu.mul hxi) 0) l1
      (fun h => l2 ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h))
  · rw [condExp, if_neg h0]
    have h1 : v ∈ S1 D := (G.pl.mem_S0_of_sum_eq.1 hv).resolve_left h0
    obtain ⟨l1, l2⟩ := G.ch.lev1 _ a1 a2 (G.pl.w v) (by rw [hu]; exact h1)
    exact exp_div (n := 1) hc (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame _) (hL.xi_tame t _)) l1 l2

/- English proof (translation)
Establish `a1 : 1 ≤ D.R.m - i` using `by have := i.2; omega`. Establish `a2 : D.R.m - i ≤ D.R.m` using `by omega`. Establish `hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0`. Simplify using `only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hP`. Conclude with `⟨hP.1.resolve_left hP.2, hP.2⟩`.

Establish `hS1 : P.under (𝓞 D.host.F) ∉ S1 D` using `fun h => by`. Establish `e` using `G.pl.w_Q t P hP'.1 h`. Use `hP'.2 ?_` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))`.

Establish `hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0` using `fun h => (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t P hP'.1) hS1`. Use `exp_eq (n := 0) hc ?_ fun h => nuH_not_unrAt_twPl G hL t i j P hP ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)` and prove the remaining obligations. Rewrite using `[nuH, div_eq_mul_inv]`. Conclude with `Formalism.L2.Host.HChar.LevelLe.mul (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame _) (hL.xi_tame t _)) (Formalism.L2.Host.HChar.LevelLe.inv (Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ a1 a2 P hS0) _))`.
-/
theorem exp_twPl (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (hP : P ∈ twPl G t) {c : ℕ} (hc : GlobalTheory.CMVal.ExpAt (nuH G t i j) P c) : c = 1 := by
  have a1 : 1 ≤ D.R.m - i := by have := i.2; omega
  have a2 : D.R.m - i ≤ D.R.m := by omega
  have hP' : P ∈ L.Q t ∧ P ∉ G.pl.W0 := by
    simp only [twPl, GlobalTheory.FunObj.locPl, Finset.mem_filter, Finset.mem_union] at hP
    exact ⟨hP.1.resolve_left hP.2, hP.2⟩
  have hS1 : P.under (𝓞 D.host.F) ∉ S1 D := fun h => by
    have e := G.pl.w_Q t P hP'.1 h
    refine hP'.2 ?_
    rw [e]
    exact Finset.mem_image_of_mem _ (G.pl.mem_S0_of_sum_eq.2 (Or.inr h))
  have hS0 : P.under (𝓞 D.host.F) ∉ G.pl.S0 := fun h =>
    (G.pl.mem_S0_of_sum_eq.1 h).elim (G.pl.levelPlace_ne_basePlace t P hP'.1) hS1
  refine exp_eq (n := 0) hc ?_ fun h => nuH_not_unrAt_twPl G hL t i j P hP ((Formalism.L2.Host.HChar.unrAt_iff _ _).2 h)
  rw [nuH, div_eq_mul_inv]
  exact Formalism.L2.Host.HChar.LevelLe.mul (Formalism.L2.Host.HChar.LevelLe.mul ((L.C.isMu0 j).tame _) (hL.xi_tame t _))
    (Formalism.L2.Host.HChar.LevelLe.inv (Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ a1 a2 P hS0) _))

/- English proof (translation)
Introduce `D T L sc G μ₀ hL t i j c hc`. Establish `hW : ∀ v ∈ G.pl.S0, G.pl.w v ∈ locPl G t` using `fun v hv => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)`. Establish `hT : ∀ P ∈ twPl G t, P ∈ locPl G t` using `fun P hP => (Finset.mem_filter.1 hP).1`. Establish `h1 : ∀ v ∈ G.pl.S0, c (G.pl.w v) = condExp G.pl v` using `fun v hv => exp_w G hL t i j hv (hc _ (hW v hv))`. Establish `h2 : ∀ P ∈ twPl G t, c P = 1` using `fun P hP => exp_twPl G hL t i j hP (hc _ (hT P hP))`.

Use `⟨fun w hw => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h : w ∈ G.pl.W0`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 h`. Rewrite using `[h1 v hv, condExp]`. Apply the tactic sequence `split_ifs <;> omega`.

Rewrite using `[h2 w (Finset.mem_filter.2 ⟨hw, h⟩)]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← Finset.prod_filter_mul_prod_filter_not (locPl G t) (fun w => w ∈ G.pl.W0), modT]`. Use `congr 1`. Establish `e : (locPl G t).filter (fun w => w ∈ G.pl.W0) = G.pl.S0.image G.pl.w`.

Use extensionality with `w`. Rewrite using `[Finset.mem_filter]`. Conclude with `⟨fun h => h.2, fun h => ⟨Finset.mem_union_left _ h, h⟩⟩`. Rewrite using `[e, Finset.prod_image fun v hv v' hv' h => (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv')), condE]`. Conclude with `Finset.prod_congr rfl fun v hv => by rw [h1 v hv]`.

Use `Finset.prod_congr ?_ fun P hP => by rw [h2 P hP, pow_one]` and prove the remaining obligations. Use extensionality with `w`. Simplify using `only [twPl, Finset.mem_filter]`.
-/
theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) {μ₀ : T}, L.Is μ₀ →
  ∀ (t : T) (i j : Fin D.R.m) (c : Formalism.L2.DIV.Pl D.host.E → ℕ),
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, GlobalTheory.CMVal.ExpAt (GlobalTheory.FunObj.SqNum.nuH G t i j) w (c w)) →
  (∀ w ∈ GlobalTheory.FunObj.locPl G t, 0 < c w) ∧ ∏ w ∈ GlobalTheory.FunObj.locPl G t, w.asIdeal ^ c w = GlobalTheory.SqTop.modT G t := by
  intro D T L sc G μ₀ hL t i j c hc
  have hW : ∀ v ∈ G.pl.S0, G.pl.w v ∈ locPl G t := fun v hv =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)
  have hT : ∀ P ∈ twPl G t, P ∈ locPl G t := fun P hP => (Finset.mem_filter.1 hP).1
  have h1 : ∀ v ∈ G.pl.S0, c (G.pl.w v) = condExp G.pl v := fun v hv => exp_w G hL t i j hv (hc _ (hW v hv))
  have h2 : ∀ P ∈ twPl G t, c P = 1 := fun P hP => exp_twPl G hL t i j hP (hc _ (hT P hP))
  refine ⟨fun w hw => ?_, ?_⟩
  · by_cases h : w ∈ G.pl.W0
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
      rw [h1 v hv, condExp]
      split_ifs <;> omega
    · rw [h2 w (Finset.mem_filter.2 ⟨hw, h⟩)]
      omega
  · rw [← Finset.prod_filter_mul_prod_filter_not (locPl G t) (fun w => w ∈ G.pl.W0), modT]
    congr 1
    · have e : (locPl G t).filter (fun w => w ∈ G.pl.W0) = G.pl.S0.image G.pl.w := by
        ext w
        rw [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨Finset.mem_union_left _ h, h⟩⟩
      rw [e, Finset.prod_image fun v hv v' hv' h =>
        (G.pl.under_w hv).symm.trans ((congrArg _ h).trans (G.pl.under_w hv')), condE]
      exact Finset.prod_congr rfl fun v hv => by rw [h1 v hv]
    · refine Finset.prod_congr ?_ fun P hP => by rw [h2 P hP, pow_one]
      ext w
      simp only [twPl, Finset.mem_filter]

end GlobalTheory.NuExpModulus
