import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamLowNumericalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainEqSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableAbsNormInvSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpNegLeNormTprodOneSubInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsLogInvOneSubLeTwoMulAbs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultRealElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjFrameMemUH
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolEqIndexMulMass

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.AdelicScalar

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

/- English proof (translation)
Establish `h : ((χ x : ℂˣ) : ℂ) ^ Nat.card H = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]`. Conclude with `Complex.norm_eq_one_of_pow_eq_one h Nat.card_pos.ne'`.
-/
theorem norm_char_finite {H : Type} [Group H] [Finite H] (χ : H →* ℂˣ) (x : H) : ‖((χ x : ℂˣ) : ℂ)‖ = 1 := by
  have h : ((χ x : ℂˣ) : ℂ) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Nat.card_pos.ne'

instance finite_kP (PP : Pl D.host.E) : Finite (kP PP) := PP.asIdeal.finiteQuotientOfFreeOfNeBot PP.ne_bot

/- English proof (translation)
Unfold `levFn`. Simplify using `only [Units.val_mul, Units.coe_prod, norm_mul, norm_prod, norm_char_finite, Finset.prod_const_one, mul_one]`. Unfold `ext1`. Use `split_ifs`. Conclude with `norm_char_finite _ _`.

Simplify using the standard rewrite rules.
-/
theorem norm_levFn {n : ℕ} (β x : GL (Fin n) (Lev.EAf D)) (L : LevDat D.host.E ℂ n) : ‖((levFn β L x : ℂˣ) : ℂ)‖ = 1 := by
  unfold levFn
  simp only [Units.val_mul, Units.coe_prod, norm_mul, norm_prod, norm_char_finite, Finset.prod_const_one, mul_one]
  unfold ext1
  split_ifs
  · exact norm_char_finite _ _
  · simp

/- English proof (translation)
Use `haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh`. Take `⟨h1, h2, h3⟩` from `hh`. Conclude with `Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩`.
-/
theorem isOpen_level (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) :
    IsOpen (((lev D.sp.cm V.gram β L).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
  classical
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ V β (L.Pg ∪ L.Q)] with κ hh
  obtain ⟨h1, h2, h3⟩ := hh
  exact Kg_le_lev (D := L) (T := L.Pg ∪ L.Q) Finset.subset_union_left Finset.subset_union_right
      ⟨⟨h1, h2⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => mem_princAt.2 ⟨h2, h3 PP hP⟩⟩

/- English proof (translation)
Take `⟨_, g, rfl⟩` from `u`. Take `⟨h1, h2⟩` from `GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram`. Take `⟨k, k1, k2⟩` from `h2 1 (finHom V g)`. Establish `hk : k ∈ HR (AF D.host.F) D.sp.cm.sig V.gram` using `(h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩`. Conclude with `⟨⟨k, hk⟩, k1, Subtype.ext k2⟩`.
-/
theorem exists_finLift (V : HSp D) (u : Bridge.Gf V) : ∃ k : GA D V, k ∈ GfC V ∧ (finHom V).rangeRestrict k = u := by
  obtain ⟨_, g, rfl⟩ := u
  obtain ⟨h1, h2⟩ := GlobalTheory.Mass.parts_spec D.sp.cm.sig V.gram
  obtain ⟨k, k1, k2⟩ := h2 1 (finHom V g)
  have hk : k ∈ HR (AF D.host.F) D.sp.cm.sig V.gram :=
    (h1 k).2 ⟨k1 ▸ one_mem _, k2 ▸ ((h1 _).1 g.2).2⟩
  exact ⟨⟨k, hk⟩, k1, Subtype.ext k2⟩

def finLift (V : HSp D) (u : Bridge.Gf V) : GA D V := (exists_finLift V u).choose

/- English proof (translation)
The claim follows from `(exists_finLift V u).choose_spec.1`.
-/
theorem finLift_mem (V : HSp D) (u : Bridge.Gf V) : finLift V u ∈ GfC V := (exists_finLift V u).choose_spec.1

/- English proof (translation)
The claim follows from `(exists_finLift V u).choose_spec.2`.
-/
theorem finLift_spec (V : HSp D) (u : Bridge.Gf V) : (finHom V).rangeRestrict (finLift V u) = u :=
  (exists_finLift V u).choose_spec.2

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_grpOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (k : GA D V) :
    (finHom V).rangeRestrict k ∈ grpOf V β L ↔ Lev.finE V k ∈ lev D.sp.cm V.gram β L := Iff.rfl

/- English proof (translation)
Establish `key` using `(GlobalTheory.ClassIntegral.integral_fundamentalDomain_eq_sum Γ (J.comap π) μ hK h1 s ?_ 𝓕 h𝓕 Φ hΦ).2`. Rewrite using `[key]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 3`. Use `Nat.card_congr (Equiv.subtypeEquivRight fun γ => ?_)` and prove the remaining obligations.

Rewrite using `[Bridge.mem_stab, Subgroup.mem_comap, map_mul, map_mul, map_inv, hs]`. Both sides reduce to the same expression. Introduce `x`. Use `(existsUnique_congr fun j => ?_).1 (hy (π x))` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨γ, k, e⟩`. Use `⟨γ, γ.2, ((γ : G) * s j)⁻¹ * x, ?_, by group⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_comap, map_mul, map_inv, map_mul, hs, e]`. Establish `: π (γ : G) = (π.comp Γ.subtype) γ` using `rfl`. Rewrite using `[this, inv_mul_cancel_left]`.

Conclude with `k.2`. Introduce and unpack `⟨γ, hγ, k, hk, rfl⟩`. Conclude with `⟨⟨γ, hγ⟩, ⟨_, hk⟩, by rw [map_mul, map_mul, hs]; rfl⟩`.
-/
theorem integral_eq_classSum_of_hom {G H : Type} [Group G] [Group H] [MeasurableSpace G] [MeasurableMul G] (π : G →* H)
    (Γ : Subgroup G) [Countable Γ] (J : Subgroup H) (μ : Measure G) [μ.IsMulLeftInvariant]
    (hK : MeasurableSet ((J.comap π : Subgroup G) : Set G)) (h1 : μ (J.comap π) = 1) {I : Type} [Fintype I] {y : I → H}
    (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (s : I → G) (hs : ∀ j, π (s j) = y j) {𝓕 : Set G}
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (Φ : G → ℂ) (hΦ : ∀ γ ∈ Γ, ∀ k, π k ∈ J → ∀ x, Φ (γ * x * k) = Φ x) :
    ∫ x in 𝓕, Φ x ∂μ = ∑ j, ((Nat.card (Bridge.stab (π.comp Γ.subtype) J (y j)) : ℂ))⁻¹ * Φ (s j) := by
  have key := (GlobalTheory.ClassIntegral.integral_fundamentalDomain_eq_sum Γ (J.comap π) μ hK h1 s ?_ 𝓕 h𝓕 Φ hΦ).2
  · rw [key]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 3
    refine Nat.card_congr (Equiv.subtypeEquivRight fun γ => ?_)
    rw [Bridge.mem_stab, Subgroup.mem_comap, map_mul, map_mul, map_inv, hs]
    rfl
  · intro x
    refine (existsUnique_congr fun j => ?_).1 (hy (π x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, ((γ : G) * s j)⁻¹ * x, ?_, by group⟩
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, hs, e]
      have : π (γ : G) = (π.comp Γ.subtype) γ := rfl
      rw [this, inv_mul_cancel_left]
      exact k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, ⟨_, hk⟩, by rw [map_mul, map_mul, hs]; rfl⟩

/- English proof (translation)
Use `haveI := hν.1.1`. Use `haveI : MeasurableMul (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA _ _`. Use `haveI : BorelSpace (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _`. Use `haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _`. Establish `e : (grpOf V β L).comap (finHom V).rangeRestrict = (lev D.sp.cm V.gram β L).comap (Lev.finE V)` using `Subgroup.ext fun k => mem_grpOf V β L k`.

Use `integral_eq_classSum_of_hom (finHom V).rangeRestrict (GQ V) (grpOf V β L) ν ?_ ?_ hy _ (fun j => finLift_spec V (y j)) hν.2 Φ fun γ hγ k hk x => hΦ γ hγ k ((mem_grpOf V β L k).1 hk) x` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `(isOpen_level V β L).measurableSet`. Rewrite using `[e]`. Conclude with `GlobalTheory.Mass.Levels.measure_comap_finE hν.1`.
-/
theorem integral_eq_classSum (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    {ν : Measure (GA D V)} {𝓕 : Set (GA D V)} (hν : IsMeasDef V (lev D.sp.cm V.gram β L) ν 𝓕) {I : Type} [Fintype I]
    {y : I → Bridge.Gf V} (hy : Bridge.IsReps (Bridge.ratF V) (grpOf V β L) y) (Φ : GA D V → ℂ)
    (hΦ : ∀ γ ∈ GQ V, ∀ k, Lev.finE V k ∈ lev D.sp.cm V.gram β L → ∀ x, Φ (γ * x * k) = Φ x) :
    ∫ x in 𝓕, Φ x ∂ν =
      ∑ j, ((Nat.card (Bridge.stab (Bridge.ratF V) (grpOf V β L) (y j)) : ℂ))⁻¹ * Φ (finLift V (y j)) := by
  haveI := hν.1.1
  haveI : MeasurableMul (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableMulHA _ _
  haveI : BorelSpace (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA _ _
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  have e : (grpOf V β L).comap (finHom V).rangeRestrict = (lev D.sp.cm V.gram β L).comap (Lev.finE V) :=
    Subgroup.ext fun k => mem_grpOf V β L k
  refine integral_eq_classSum_of_hom (finHom V).rangeRestrict (GQ V) (grpOf V β L) ν ?_ ?_ hy _
    (fun j => finLift_spec V (y j)) hν.2 Φ fun γ hγ k hk x => hΦ γ hγ k ((mem_grpOf V β L k).1 hk) x
  · rw [e]; exact (isOpen_level V β L).measurableSet
  · rw [e]; exact GlobalTheory.Mass.Levels.measure_comap_finE hν.1

section Schur

variable {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}

/- English proof (translation)
Establish `h1 : ∀ x y : H.H, inner ℂ x y ≠ 0 → ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c` using `fun x y hxy => by`. Assume the negation of the conclusion as `hc`. Apply `hxy` to reduce the goal to its premises. Rewrite using `[h, ipM, dif_neg hc, mul_zero]`. Use `ipM_spec _ _ _ _ _ ?_` and prove the remaining obligations.

Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Conclude with `⟨0, fun v v' => by simp⟩`. Distinguish the cases in `hxy : inner ℂ x y = 0`. Take `⟨c, hc⟩` from `h1 x (x + y) (by rw [inner_add_right, hxy, add_zero]; exact inner_self_ne_zero.2 hx)`.

Take `⟨c', hc'⟩` from `h1 x x (inner_self_ne_zero.2 hx)`. Use `⟨c - c', fun v v' => ?_⟩` and prove the remaining obligations. Establish `e : (fun g => star (H.e x v g) * H.e y v' g) = fun g => star (H.e x v g) * H.e (x + y) v' g - star (H.e x v g) * H.e x v' g`. Use function extensionality and compare the values at `g`. Simplify using `[mul_add]`.

Rewrite using `[e]`. Conclude with `⟨(hc v v').1.sub (hc' v v').1, by rw [integral_sub (hc v v').1 (hc' v v').1, (hc v v').2, (hc' v v').2, sub_mul]⟩`. Conclude with `h1 x y hxy`.
-/
theorem isMultiplicityInner_of_model (H : HMod (MMap M)) {N : ℂ} (h : ∀ x y, inner ℂ x y = N * ipM M μ 𝓕 (H.e x) (H.e y)) (x y : H.H) :
    IsMultIP M μ 𝓕 (H.e x) (H.e y) (ipM M μ 𝓕 (H.e x) (H.e y)) := by
  have h1 : ∀ x y : H.H, inner ℂ x y ≠ 0 → ∃ c, IsMultIP M μ 𝓕 (H.e x) (H.e y) c := fun x y hxy => by
    by_contra hc
    apply hxy
    rw [h, ipM, dif_neg hc, mul_zero]
  refine ipM_spec _ _ _ _ _ ?_
  by_cases hx : x = 0
  · subst hx
    exact ⟨0, fun v v' => by simp⟩
  by_cases hxy : inner ℂ x y = 0
  · obtain ⟨c, hc⟩ := h1 x (x + y) (by rw [inner_add_right, hxy, add_zero]; exact inner_self_ne_zero.2 hx)
    obtain ⟨c', hc'⟩ := h1 x x (inner_self_ne_zero.2 hx)
    refine ⟨c - c', fun v v' => ?_⟩
    have e : (fun g => star (H.e x v g) * H.e y v' g) =
        fun g => star (H.e x v g) * H.e (x + y) v' g - star (H.e x v g) * H.e x v' g := by
      funext g; simp [mul_add]
    rw [e]
    exact ⟨(hc v v').1.sub (hc' v v').1, by rw [integral_sub (hc v v').1 (hc' v v').1, (hc v v').2, (hc' v v').2, sub_mul]⟩
  · exact h1 x y hxy

end Schur

/- English proof (translation)
Use `Finset.prod_induction _ (1 ≤ ·) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun i _ => ?_` and prove the remaining obligations. Use `Finset.prod_induction _ (1 ≤ ·) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun j hj => ?_` and prove the remaining obligations. Establish `hij : i < j` using `(Finset.mem_filter.1 hj).2`. Establish `h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ)` using `by exact_mod_cast hij`. Establish `h2 : (0 : ℚ) ≤ ((lam i - lam j : ℤ) : ℚ)` using `by exact_mod_cast sub_nonneg.2 (h i j hij.le)`.

Rewrite using `[le_div_iff₀ (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem one_le_weylDimU {p : ℕ} (lam : Fin p → ℤ) (h : ∀ i j, i ≤ j → lam j ≤ lam i) : 1 ≤ weylDimU lam := by
  refine Finset.prod_induction _ (1 ≤ ·) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun i _ => ?_
  refine Finset.prod_induction _ (1 ≤ ·) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.1 hj).2
  have h1 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
  have h2 : (0 : ℚ) ≤ ((lam i - lam j : ℤ) : ℚ) := by exact_mod_cast sub_nonneg.2 (h i j hij.le)
  rw [le_div_iff₀ (by linarith)]
  linarith

/- English proof (translation)
Use `D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D ρ)` as an intermediate fact. Establish `h1` using `D.R.m_add_three_le_k`. Establish `h2` using `i.2`. Unfold `pW qW`. Rewrite using `[this]`.

Simplify using `only [Ranks.sigW, Ranks.r]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sig_add (i : Fin D.R.m) (ρ : D.what₂.Tau) : pW D i ρ + qW D i ρ = D.R.r := by
  have := D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D ρ)
  have h1 := D.R.m_add_three_le_k
  have h2 := i.2
  unfold pW qW
  rw [this]
  simp only [Ranks.sigW, Ranks.r]
  omega

/- English proof (translation)
Establish `h` using `Formalism.L2.NTheta.holOK_kapW (D.hc (lab σ ρ)) _ _ (sig_add i ρ)`. Conclude with `one_le_mul_of_one_le_of_one_le (one_le_weylDimU _ h.1) (one_le_weylDimU _ h.2.1)`.
-/
theorem one_le_dimK (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) : 1 ≤ dimK _ _ (kapAt (Wc D i) σ ρ) := by
  have h := Formalism.L2.NTheta.holOK_kapW (D.hc (lab σ ρ)) _ _ (sig_add i ρ)
  exact one_le_mul_of_one_le_of_one_le (one_le_weylDimU _ h.1) (one_le_weylDimU _ h.2.1)

/- English proof (translation)
Use `Finset.prod_pos fun x hx => ?_` and prove the remaining obligations. Establish `hx'` using `(YoungDiagram.mem_cells _).1 hx`. Establish `h1` using `YoungDiagram.mem_iff_lt_rowLen.1 (show (x.1, x.2) ∈ _ from hx')`. Establish `h2` using `YoungDiagram.mem_iff_lt_colLen.1 (show (x.1, x.2) ∈ _ from hx')`. Use linear arithmetic over natural numbers and integers.
-/
theorem hookOf_pos (n : ℕ) (a : ℕ → ℕ) : 0 < hookOf n a := by
  refine Finset.prod_pos fun x hx => ?_
  have hx' := (YoungDiagram.mem_cells _).1 hx
  have h1 := YoungDiagram.mem_iff_lt_rowLen.1 (show (x.1, x.2) ∈ _ from hx')
  have h2 := YoungDiagram.mem_iff_lt_colLen.1 (show (x.1, x.2) ∈ _ from hx')
  omega

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, -⟩` from `GlobalTheory.UpqTopology.upq_lcsc p q`. Use `infer_instance`.
-/
theorem sigmaFinite_haar {p q : ℕ} (m : Measure (UpqT p q)) (hm : m.IsHaarMeasure) : SigmaFinite m := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := GlobalTheory.UpqTopology.upq_lcsc p q
  infer_instance

/- English proof (translation)
Establish `h0 : Ideal.absNorm w.asIdeal ≠ 0` using `fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)`. Establish `h1 : Ideal.absNorm w.asIdeal ≠ 1` using `fun h => w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)`. Establish `: 2 ≤ Ideal.absNorm w.asIdeal` using `by omega`. Conclude with `this` after adjusting the coercions.
-/
theorem two_le_absNorm {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) :
    (2 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℕ) := by
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := fun h => w.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have : 2 ≤ Ideal.absNorm w.asIdeal := by omega
  exact_mod_cast this

/- English proof (translation)
Take `⟨hs, hb⟩` from `GlobalTheory.PrimeSquareSum.summable_absNorm_inv_sq K`. Use `set N : HeightOneSpectrum (𝓞 K) → ℝ := fun w => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹`. Establish `hN : ∀ w, 0 ≤ N w` using `fun w => by positivity`. Establish `hs1 : Summable fun w : {w // p w} => N w.1` using `hs.subtype _`. Establish `hb1 : ∑' w : {w // p w}, N w.1 ≤ (Module.finrank ℚ K : ℝ)` using `(Summable.tsum_subtype_le N _ hN hs).trans hb`.

Establish `hs2 : Summable fun a : {w // p w} × κ => N a.1.1` using `(summable_prod_of_nonneg fun a => hN _).2 ⟨fun _ => Summable.of_finite, by`. Simplify `hs1.mul_left (Fintype.card κ : ℝ)⟩` using `[tsum_fintype]`. Establish `hs3 : Summable u` using `Summable.of_nonneg_of_le h0 h hs2`. Use `⟨fun a => (h a).trans ?_, hs3, (hs3.tsum_le_tsum h hs2).trans ?_⟩` and prove the remaining obligations. Use `two_le_absNorm a.1.1` as an intermediate fact.

Rewrite using `[one_div]`. Conclude with `inv_anti₀ (by norm_num) (by nlinarith)`. Rewrite using `[hs2.tsum_prod]`. Simplify using `only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[tsum_mul_left]`.

Conclude with `mul_le_mul_of_nonneg_left hb1 (Nat.cast_nonneg _)`.
-/
theorem sum_bound {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K) → Prop) {κ : Type} [Fintype κ]
    (u : {w // p w} × κ → ℝ) (h0 : ∀ a, 0 ≤ u a) (h : ∀ a, u a ≤ (((Ideal.absNorm a.1.1.asIdeal : ℕ) : ℝ) ^ 2)⁻¹) :
    (∀ a, u a ≤ 1 / 2) ∧ Summable u ∧ ∑' a, u a ≤ Fintype.card κ * (Module.finrank ℚ K : ℝ) := by
  obtain ⟨hs, hb⟩ := GlobalTheory.PrimeSquareSum.summable_absNorm_inv_sq K
  set N : HeightOneSpectrum (𝓞 K) → ℝ := fun w => (((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ 2)⁻¹
  have hN : ∀ w, 0 ≤ N w := fun w => by positivity
  have hs1 : Summable fun w : {w // p w} => N w.1 := hs.subtype _
  have hb1 : ∑' w : {w // p w}, N w.1 ≤ (Module.finrank ℚ K : ℝ) := (Summable.tsum_subtype_le N _ hN hs).trans hb
  have hs2 : Summable fun a : {w // p w} × κ => N a.1.1 :=
    (summable_prod_of_nonneg fun a => hN _).2 ⟨fun _ => Summable.of_finite, by
      simpa [tsum_fintype] using hs1.mul_left (Fintype.card κ : ℝ)⟩
  have hs3 : Summable u := Summable.of_nonneg_of_le h0 h hs2
  refine ⟨fun a => (h a).trans ?_, hs3, (hs3.tsum_le_tsum h hs2).trans ?_⟩
  · have := two_le_absNorm a.1.1
    rw [one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith)
  · rw [hs2.tsum_prod]
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb1 (Nat.cast_nonneg _)

/- English proof (translation)
Rewrite using `[D.host.finrank_cmField]`. Unfold `Ranks.f Ranks.n`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem finrank_E (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.finrank_cmField]
  unfold Ranks.f Ranks.n
  ring

/- English proof (translation)
Rewrite using `[← finrank_E]`. Conclude with `LinearMap.finrank_le_finrank_of_injective (f := (IsScalarTower.toAlgHom ℚ D.host.F D.host.E).toLinearMap) (algebraMap D.host.F D.host.E).injective`.
-/
theorem finrank_F_le (D : D7) : Module.finrank ℚ D.host.F ≤ 2 * D.R.f := by
  rw [← finrank_E]
  exact LinearMap.finrank_le_finrank_of_injective (f := (IsScalarTower.toAlgHom ℚ D.host.F D.host.E).toLinearMap)
    (algebraMap D.host.F D.host.E).injective

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `sum_bound (OffS D S) (κ := Fin D.R.r) (fun a => ‖x a.1.1 a.2‖) (fun _ => norm_nonneg _) fun a => by`. Use `(hx _ _).trans ?_` and prove the remaining obligations. Establish `ht : (D.R.r : ℝ) + 5 ≤ D.R.t` using `by exact_mod_cast D.R.rank_add_five_le`. Use `two_le_absNorm a.1.1` as an intermediate fact. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]`.

Conclude with `Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)`. Rewrite `h3` using `[finrank_E, Fintype.card_fin]`. Conclude with `GlobalTheory.exp_neg_le_norm_tprod_one_sub_inv _ _ h1 h2 (by exact_mod_cast h3)`.
-/
theorem eulerOff_lower (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (x : HeightOneSpectrum (𝓞 D.host.E) → Fin D.R.r → ℂ)
    (hx : ∀ w a, ‖x w a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2 - (1 + (D.R.t : ℝ)) / 2)) :
    Real.exp (-(D.R.r * (2 * D.R.f))) ≤ ‖eulerOff D S x‖ := by
  obtain ⟨h1, h2, h3⟩ := sum_bound (OffS D S) (κ := Fin D.R.r) (fun a => ‖x a.1.1 a.2‖) (fun _ => norm_nonneg _) fun a => by
    refine (hx _ _).trans ?_
    have ht : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast D.R.rank_add_five_le
    have := two_le_absNorm a.1.1
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
  rw [finrank_E, Fintype.card_fin] at h3
  exact GlobalTheory.exp_neg_le_norm_tprod_one_sub_inv _ _ h1 h2 (by exact_mod_cast h3)

/- English proof (translation)
The claim follows from `|quadTerm D v i| ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ := by have h := two_le_absNorm v have hs : |quadSign D v| = 1 := by unfold quadSign; split_ifs <;> simp rw [quadTerm, abs_div, abs_pow, hs, one_pow, one_div, abs_of_pos (by positivity)] exact inv_anti₀ (by positivity) …`.
-/
theorem abs_quadTerm_le (v : HeightOneSpectrum (𝓞 D.host.F)) {i : ℕ} (hi : 2 ≤ i) :
    |quadTerm D v i| ≤ (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ 2)⁻¹ := by
  have h := two_le_absNorm v
  have hs : |quadSign D v| = 1 := by unfold quadSign; split_ifs <;> simp
  rw [quadTerm, abs_div, abs_pow, hs, one_pow, one_div, abs_of_pos (by positivity)]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by linarith) hi)

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `sum_bound p (κ := Finset.Ioc D.R.t D.R.nV) (fun a => |quadTerm D a.1.1 a.2.1|) (fun _ => abs_nonneg _) fun a => abs_quadTerm_le _ (by`. Use `(Finset.mem_Ioc.1 a.2.2).1` as an intermediate fact. Use `D.R.rank_add_five_le` as an intermediate fact. Use the proof step `omega)`. Use `GlobalTheory.tprod_inv_one_sub_pos_and_le_exp _ _ h1 h2 (h3.trans ?_)` and prove the remaining obligations.

Rewrite using `[Fintype.card_coe, Nat.card_Ioc, show D.R.nV - D.R.t = D.R.r by unfold Ranks.nV; omega]`. Conclude with `mul_le_mul_of_nonneg_left (by exact_mod_cast finrank_F_le D) (Nat.cast_nonneg _)`.
-/
theorem quad_bound (p : HeightOneSpectrum (𝓞 D.host.F) → Prop) :
    0 < ∏' a : {v // p v} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D a.1.1 a.2.1)⁻¹ ∧
      ∏' a : {v // p v} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D a.1.1 a.2.1)⁻¹ ≤ Real.exp (2 * (D.R.r * (2 * D.R.f))) := by
  obtain ⟨h1, h2, h3⟩ := sum_bound p (κ := Finset.Ioc D.R.t D.R.nV) (fun a => |quadTerm D a.1.1 a.2.1|)
    (fun _ => abs_nonneg _) fun a => abs_quadTerm_le _ (by
      have := (Finset.mem_Ioc.1 a.2.2).1
      have := D.R.rank_add_five_le
      omega)
  refine GlobalTheory.tprod_inv_one_sub_pos_and_le_exp _ _ h1 h2 (h3.trans ?_)
  rw [Fintype.card_coe, Nat.card_Ioc, show D.R.nV - D.R.t = D.R.r by unfold Ranks.nV; omega]
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast finrank_F_le D) (Nat.cast_nonneg _)

/- English proof (translation)
The claim follows from `quad_bound _`.
-/
theorem dOff_bound (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    0 < dOff D S ∧ dOff D S ≤ Real.exp (2 * (D.R.r * (2 * D.R.f))) := quad_bound _

/- English proof (translation)
Establish `h` using `quad_bound (D := D) (· ∈ S)`. Establish `e : ∏' a : {v // v ∈ S} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D a.1.1 a.2.1)⁻¹ = ∏ v ∈ S, dLoc D v`. Rewrite using `[tprod_fintype, Fintype.prod_prod_type, ← Finset.prod_coe_sort S]`. Conclude with `Finset.prod_congr rfl fun v _ => Finset.prod_coe_sort (Finset.Ioc D.R.t D.R.nV) fun i => (1 - quadTerm D v i)⁻¹`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem dLoc_bound (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    0 < ∏ v ∈ S, dLoc D v ∧ ∏ v ∈ S, dLoc D v ≤ Real.exp (2 * (D.R.r * (2 * D.R.f))) := by
  have h := quad_bound (D := D) (· ∈ S)
  have e : ∏' a : {v // v ∈ S} × Finset.Ioc D.R.t D.R.nV, (1 - quadTerm D a.1.1 a.2.1)⁻¹ = ∏ v ∈ S, dLoc D v := by
    rw [tprod_fintype, Fintype.prod_prod_type, ← Finset.prod_coe_sort S]
    exact Finset.prod_congr rfl fun v _ => Finset.prod_coe_sort (Finset.Ioc D.R.t D.R.nV) fun i => (1 - quadTerm D v i)⁻¹
  rwa [e] at h

section Smooth

open Formalism.QuantumDeterminants

variable {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}

/- English proof (translation)
Establish `hd : IsUnit G.det` using `(Matrix.isUnit_iff_isUnit_det G).1 hG`. Establish `h1 : (t • X)ᴴ = G * (-(t • X)) * G⁻¹`. Establish `h2 : Xᴴ = G * (-X) * G⁻¹`. Rewrite using `[Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]`. Rewrite using `[conjTranspose_smul, h2]`.

Simplify using the standard rewrite rules. Use `show (NormedSpace.exp (t • X))ᴴ * G * NormedSpace.exp (t • X) = G`. Rewrite using `[← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hG, Matrix.exp_neg]`. Establish `hu : IsUnit (NormedSpace.exp (t • X)).det` using `(Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)`. Rewrite using `[Matrix.mul_assoc (G * _), Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]`.
-/
theorem exp_mem_UH {X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) (hX : Xᴴ * G + G * X = 0) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ UH G := by
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : (t • X)ᴴ = G * (-(t • X)) * G⁻¹ := by
    have h2 : Xᴴ = G * (-X) * G⁻¹ := by
      rw [Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
        Matrix.mul_one]
    rw [conjTranspose_smul, h2]
    simp
  show (NormedSpace.exp (t • X))ᴴ * G * NormedSpace.exp (t • X) = G
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hG, Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp (t • X)).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  rw [Matrix.mul_assoc (G * _), Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G`. Simplify using the standard rewrite rules. Consider the case `cons a l ih`. Establish `ha : aᴴ * G * a = G` using `h a (by simp)`.

Establish `hl : l.prodᴴ * G * l.prod = G` using `ih fun g hg => h g (by simp [hg])`. Use `show (a * l.prod)ᴴ * G * (a * l.prod) = G`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = G := by rw [ha, hl]`.
-/
theorem prod_mem_UH (l : List (Matrix (Fin n) (Fin n) ℂ)) (h : ∀ g ∈ l, g ∈ UH G) : l.prod ∈ UH G := by
  induction l with
  | nil => show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * G * 1 = G; simp
  | cons a l ih =>
    have ha : aᴴ * G * a = G := h a (by simp)
    have hl : l.prodᴴ * G * l.prod = G := ih fun g hg => h g (by simp [hg])
    show (a * l.prod)ᴴ * G * (a * l.prod) = G
    calc (a * l.prod)ᴴ * G * (a * l.prod) = l.prodᴴ * (aᴴ * G * a) * l.prod := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [ha, hl]

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det g).1 hu`. Establish `h1 : G * g⁻¹ = gᴴ * G` using `by conv_lhs => rw [← h]`. Rewrite using `[Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]`. Establish `h2 : (g⁻¹)ᴴ * G = G * g` using `by conv_lhs => rw [← h]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = gᴴ * (Xᴴ * G + G * X) * g := by rw [h1, h2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`. Use `_ = 0 := by rw [hX']; simp`.
-/
theorem conj_mem_lie {g X : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit g) (h : gᴴ * G * g = G) (hX' : Xᴴ * G + G * X = 0) :
    (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = 0 := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hu
  have h1 : G * g⁻¹ = gᴴ * G := by
    conv_lhs => rw [← h]
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.mul_one]
  have h2 : (g⁻¹)ᴴ * G = G * g := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, mul_nonsing_inv _ hd]; simp
  calc (g⁻¹ * X * g)ᴴ * G + G * (g⁻¹ * X * g) = gᴴ * Xᴴ * ((g⁻¹)ᴴ * G) + (G * g⁻¹) * X * g := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * G + G * X) * g := by rw [h1, h2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX']; simp

/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det g).1 hg`. Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons x l ih`. Rewrite using `[List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]`.

Simplify using `only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]`.
-/
theorem prod_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : IsUnit g) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    g * (l.map fun x => g⁻¹ * x * g).prod = l.prod * g := by
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 hg
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, Matrix.mul_assoc x, ← ih]
    simp only [← Matrix.mul_assoc, mul_nonsing_inv _ hd, Matrix.one_mul]

/- English proof (translation)
Introduce `k Xs hXs`. Establish `hg' : gᴴ * G * g = G` using `hg`. Establish `hu : IsUnit g` using `isUnit_of_mul_isUnit_right (hg'.symm ▸ hG : IsUnit (gᴴ * G * g))`. Establish `hY : ∀ i, g⁻¹ * Xs i * g ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * G + G * X = 0}` using `fun i => conj_mem_lie hu hg' (hXs i)`. Establish `hP : ∀ (Ys : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Ys i ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * G + G * X = 0}) → ∀ t : Fin k → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • Ys i)).prod ∈ UH G` using `fun Ys hYs t => prod_mem_UH _ fun g hg => by`.

Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 hg`. Conclude with `exp_mem_UH hG (hYs i) _`. Establish `hc : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ), NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g` using `fun X t => by`. Rewrite using `[← Matrix.exp_conj' _ _ hu, Matrix.mul_smul, Matrix.smul_mul]`. Establish `h1` using `((π g).restrictScalars ℝ).contDiff.comp (hw k _ hY)`.

Use `h1 using 2 with t` and compare the differences between its conclusion and the goal. Use `show _ = π g _`. Rewrite using `[← hπ _ (hP _ hXs t) _ hg, ← hπ _ hg _ (hP _ hY t), ← prod_conj hu, List.map_ofFn]`. Simplify using `only [hc, Function.comp_def]`.
-/
theorem smoothVec_rep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hG : IsUnit G) (hπ : ∀ a ∈ UH G, ∀ b ∈ UH G, ∀ w, π (a * b) w = π a (π b w)) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} π w) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) :
    SmoothVec {X | Xᴴ * G + G * X = 0} π (π g w) := by
  intro k Xs hXs
  have hg' : gᴴ * G * g = G := hg
  have hu : IsUnit g := isUnit_of_mul_isUnit_right (hg'.symm ▸ hG : IsUnit (gᴴ * G * g))
  have hY : ∀ i, g⁻¹ * Xs i * g ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * G + G * X = 0} := fun i => conj_mem_lie hu hg' (hXs i)
  have hP : ∀ (Ys : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, Ys i ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * G + G * X = 0}) →
      ∀ t : Fin k → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • Ys i)).prod ∈ UH G := fun Ys hYs t =>
    prod_mem_UH _ fun g hg => by
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
      exact exp_mem_UH hG (hYs i) _
  have hc : ∀ (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ),
      NormedSpace.exp (t • (g⁻¹ * X * g)) = g⁻¹ * NormedSpace.exp (t • X) * g := fun X t => by
    rw [← Matrix.exp_conj' _ _ hu, Matrix.mul_smul, Matrix.smul_mul]
  have h1 := ((π g).restrictScalars ℝ).contDiff.comp (hw k _ hY)
  convert h1 using 2 with t
  show _ = π g _
  rw [← hπ _ (hP _ hXs t) _ hg, ← hπ _ hg _ (hP _ hY t), ← prod_conj hu, List.map_ofFn]
  simp only [hc, Function.comp_def]

/- English proof (translation)
Establish `hd : IsUnit P.det` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`. Establish `hg' : gᴴ * G * g = G` using `hg`. Use `show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`.

Use `_ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by`. Rewrite using `[h, hg', ← h]`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp`.
-/
theorem conj_mem_UJ {ε : Fin n → Bool} {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P)
    (h : Pᴴ * Formalism.REAL.Jm ε * P = G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH G) : P * g * P⁻¹ ∈ UJset ε := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hg' : gᴴ * G * g = G := hg
  show (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹) = Formalism.REAL.Jm ε
  calc (P * g * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * g * P⁻¹)
      = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * g) * P⁻¹ := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
        rw [h, hg', ← h]; simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by rw [Matrix.mul_nonsing_inv _ hd]; simp

/- English proof (translation)
Establish `hP` using `M.fr_unit τ`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).1 hP`. Establish `hG : IsUnit (gramAt D V τ)`. Rewrite using `[← M.fr_gram τ]`. Conclude with `(((Matrix.isUnit_conjTranspose _).2 hP).mul (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self _))).mul hP`.

Establish `hπ : ∀ a ∈ UH (gramAt D V τ), ∀ b ∈ UH (gramAt D V τ), ∀ w, M.rep τ (a * b) w = M.rep τ a (M.rep τ b w)`. Introduce `a ha b hb w`. Establish `h` using `(M.ds τ).2.2.1.1.2 _ (conj_mem_UJ hP (M.fr_gram τ) ha) _ (conj_mem_UJ hP (M.fr_gram τ) hb)`. Establish `e : M.fr τ * a * (M.fr τ)⁻¹ * (M.fr τ * b * (M.fr τ)⁻¹) = M.fr τ * (a * b) * (M.fr τ)⁻¹`. Simplify using `only [Matrix.mul_assoc]`.

Rewrite using `[← Matrix.mul_assoc (M.fr τ)⁻¹, nonsing_inv_mul _ hd, Matrix.one_mul]`. Unfold `DSModel.rep`. Rewrite using `[← e, h]`. Both sides reduce to the same expression. Proceed by induction on `hw using Submodule.span_induction with`.

Consider the case `mem x hx => exact Submodule.subset_span (smoothVec_rep hG hπ hx hg)`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`.

Consider the case `smul a x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ a hx`.
-/
theorem rep_mem_sm {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ UH (gramAt D V τ)) (w : M.H τ) (hw : w ∈ M.sm τ) :
    M.rep τ g w ∈ M.sm τ := by
  have hP := M.fr_unit τ
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have hG : IsUnit (gramAt D V τ) := by
    rw [← M.fr_gram τ]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self _))).mul hP
  have hπ : ∀ a ∈ UH (gramAt D V τ), ∀ b ∈ UH (gramAt D V τ), ∀ w, M.rep τ (a * b) w = M.rep τ a (M.rep τ b w) := by
    intro a ha b hb w
    have h := (M.ds τ).2.2.1.1.2 _ (conj_mem_UJ hP (M.fr_gram τ) ha) _ (conj_mem_UJ hP (M.fr_gram τ) hb)
    have e : M.fr τ * a * (M.fr τ)⁻¹ * (M.fr τ * b * (M.fr τ)⁻¹) = M.fr τ * (a * b) * (M.fr τ)⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (M.fr τ)⁻¹, nonsing_inv_mul _ hd, Matrix.one_mul]
    unfold DSModel.rep
    rw [← e, h]
    rfl
  induction hw using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span (smoothVec_rep hG hπ hx hg)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

end Smooth

/- English proof (translation)
The claim follows from `h.2.1.le (LinearMap.mem_range_self _ x)`.
-/
theorem HMod_mem {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ} (h : M.Is V ip)
    (x : M.H) : M.e x ∈ V := h.2.1.le (LinearMap.mem_range_self _ x)

/- English proof (translation)
The claim follows from `h.2.1.ge hz`.
-/
theorem HMod_onto {X : Type} [AddCommGroup X] [Module ℂ X] {M : HMod X} {V : Submodule ℂ X} {ip : X → X → ℂ} (h : M.Is V ip)
    {z : X} (hz : z ∈ V) : ∃ x, M.e x = z := h.2.1.ge hz

end GlobalTheory.AdelicScalar

end
