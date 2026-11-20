import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AddHomExtSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemNormWeightSumLeExpOfTest

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ShortVec

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h : q a < 0` using `not_le.1 h`. Establish `hfin : {x | ¬ (0 : ℝ) ≤ q x}.Finite` using `Filter.eventually_cofinite.1 (hq.eventually_ge_atTop 0)`. Establish `hv : ∀ n : ℕ, q (((n : ℤ) + 1) • a) = ((n : ℝ) + 1) ^ 2 * q a` using `fun n => by`. Rewrite using `[QuadraticMap.map_smul, zsmul_eq_mul]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℤ) + 1) • a) (fun m n e => ?_) (fun n => ?_) hfin` and prove the remaining obligations. Establish `e'` using `congrArg q e`. Simplify using `only [hv] at e'`.

Establish `e2` using `mul_right_cancel₀ h.ne e'`. Establish `e3` using `(pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 e2`. Conclude with `add_right_cancel e3` after adjusting the coercions. Simplify using `only [Set.mem_setOf_eq, hv, not_le]`. Conclude with `mul_neg_of_pos_of_neg (by positivity) h`.
-/
theorem nonneg_of_tendsto {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) : 0 ≤ q a := by
  by_contra h
  have h : q a < 0 := not_le.1 h
  have hfin : {x | ¬ (0 : ℝ) ≤ q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_ge_atTop 0)
  have hv : ∀ n : ℕ, q (((n : ℤ) + 1) • a) = ((n : ℝ) + 1) ^ 2 * q a := fun n => by
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    ring
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℤ) + 1) • a) (fun m n e => ?_)
    (fun n => ?_) hfin
  · have e' := congrArg q e
    simp only [hv] at e'
    have e2 := mul_right_cancel₀ h.ne e'
    have e3 := (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 e2
    exact_mod_cast add_right_cancel e3
  · simp only [Set.mem_setOf_eq, hv, not_le]
    exact mul_neg_of_pos_of_neg (by positivity) h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}

/- English proof (translation)
The claim follows from `RatModel.val_mul (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)) ha hb`.
-/
theorem val_mul_gen {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) {a b : Ω}
    (ha : a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))))
    (hb : b ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)))) :
    M.val (gPt p ≫ y) (a * b) = M.val (gPt p ≫ y) a * M.val (gPt p ≫ y) b :=
  RatModel.val_mul (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)) ha hb

/- English proof (translation)
Establish `hsp` using `RatModel.gPt_specializes hc (IsLocalRing.closedPoint (PadicAlgCl p))`. Establish `hy : ∀ x, y₀ ⟨S.th x, S.th_mem x⟩ = M.val (gPt p ≫ y) (S.th x)` using `fun x => hAt _`. Establish `hmul : ∀ x, ‖M.val (gPt p ≫ y) (S.th x)‖ = ‖M.val (gPt p ≫ y) (S.th x / S.th x₀)‖ * ‖M.val (gPt p ≫ y) (S.th x₀)‖`. Introduce `x`. Rewrite using `[← norm_mul, ← val_mul_gen y (RatModel.O_le_of_specializes hsp (hx₀.2 x)) (hR _ (S.th_mem x₀)), div_mul_cancel₀ _ hx₀.1]`.

Establish `hδ : ‖M.val (gPt p ≫ y) (S.th x₀)‖ = τ.δ`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hy]`. Conclude with `τ.δ_max.2 ⟨x₀, rfl⟩`. Take `⟨x₁, hx₁⟩` from `τ.δ_max.1`.

Simplify using `only [hy] at hx₁`. Rewrite using `[← hx₁, hmul x₁]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one hc (hx₀.2 x₁))`. Establish `key : ∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ`. Introduce `x`.

Express the relevant statement in the definitionally equal form `M.Div S.th x z ↔ _`. Rewrite using `[hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff hc (hx₀.2 x), hmul x, hδ]`. Conclude with `(mul_eq_right₀ τ.δ_pos.ne').symm`. Use `⟨hδ, ?_⟩` and prove the remaining obligations. Rewrite using `[← τ.supp, ThetaSys.HH]`.

Use `congr 1`. Use extensionality with `x`. Rewrite using `[key x, Set.mem_setOf_eq, hy]`.
-/
theorem norm_th_eq_and_HH_eq {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}
    (hc : y (cPt p) = z) (hR : ∀ a ∈ S.R, a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))))
    (hAt : S.At M y y₀) (τ : S.Test p y₀) {x₀ : S.Gam} (hx₀ : M.Div S.th x₀ z) :
    ‖M.val (gPt p ≫ y) (S.th x₀)‖ = τ.δ ∧ S.HH M z = τ.yy.ker := by
  have hsp := RatModel.gPt_specializes hc (IsLocalRing.closedPoint (PadicAlgCl p))
  have hy : ∀ x, y₀ ⟨S.th x, S.th_mem x⟩ = M.val (gPt p ≫ y) (S.th x) := fun x => hAt _
  have hmul : ∀ x, ‖M.val (gPt p ≫ y) (S.th x)‖ =
      ‖M.val (gPt p ≫ y) (S.th x / S.th x₀)‖ * ‖M.val (gPt p ≫ y) (S.th x₀)‖ := by
    intro x
    rw [← norm_mul, ← val_mul_gen y (RatModel.O_le_of_specializes hsp (hx₀.2 x))
      (hR _ (S.th_mem x₀)), div_mul_cancel₀ _ hx₀.1]
  have hδ : ‖M.val (gPt p ≫ y) (S.th x₀)‖ = τ.δ := by
    apply le_antisymm
    · rw [← hy]
      exact τ.δ_max.2 ⟨x₀, rfl⟩
    · obtain ⟨x₁, hx₁⟩ := τ.δ_max.1
      simp only [hy] at hx₁
      rw [← hx₁, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one hc (hx₀.2 x₁))
  have key : ∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x
    change M.Div S.th x z ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff hc (hx₀.2 x), hmul x, hδ]
    exact (mul_eq_right₀ τ.δ_pos.ne').symm
  refine ⟨hδ, ?_⟩
  rw [← τ.supp, ThetaSys.HH]
  congr 1
  ext x
  rw [key x, Set.mem_setOf_eq, hy]

/- English proof (translation)
Take `⟨s, hs⟩` from `S.fg`. Use `⟨⟨{z | b ∈ M.O z} ∩ ⋂ a ∈ s, {z | a ∈ M.O z}, (M.isOpen_setOf_mem_O b).inter (isOpen_biInter_finset fun a _ => M.isOpen_setOf_mem_O a)⟩, ⟨genericPoint M.Z, ?_, ?_⟩, ?_, RatModel.mem_ringOn.2 fun z hz => hz.1⟩` and prove the remaining obligations. Simplify using `[RatModel.O_genericPoint]`. Simplify using `[RatModel.O_genericPoint]`. Rewrite using `[← hs]`.

Conclude with `Algebra.adjoin_le fun a ha => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter₂.1 hz.2 a ha`.
-/
theorem exists_open (S : ThetaSys o Ω) (M : RatModel o Ω) (b : Ω) :
    ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ S.R ≤ M.ringOn U ∧ b ∈ M.ringOn U := by
  obtain ⟨s, hs⟩ := S.fg
  refine ⟨⟨{z | b ∈ M.O z} ∩ ⋂ a ∈ s, {z | a ∈ M.O z},
    (M.isOpen_setOf_mem_O b).inter (isOpen_biInter_finset fun a _ => M.isOpen_setOf_mem_O a)⟩,
    ⟨genericPoint M.Z, ?_, ?_⟩, ?_, RatModel.mem_ringOn.2 fun z hz => hz.1⟩
  · simp [RatModel.O_genericPoint]
  · simp [RatModel.O_genericPoint]
  · rw [← hs]
    exact Algebra.adjoin_le fun a ha => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter₂.1 hz.2 a ha

end GlobalTheory.ShortVec

namespace GlobalTheory

open ShortVec

/- English proof (translation)
Introduce `o Ω _ _ _ hb S M hn hd hT z hz p _ y y₀ hc hR hAt τ α hα hpos`. Use `haveI := hb.ft`. Use `haveI := hb.char`. Take `⟨j, hj⟩` from `hd z`. Take `⟨hδ, hH⟩` from `norm_th_eq_and_HH_eq hc hR hAt τ hj`.

Take `⟨k, hk, he⟩` from `τ.eq α hα`. Take `⟨U, hU, hRU, hbU⟩` from `exists_open S M (S.FF _ (τ.wt α) k / S.th j)`. Establish `hreg : S.FF _ (τ.wt α) k / S.th j ∈ M.O z`. Use `((classical_points_and_local_regularity o Ω M U fun x => ⟨hn.1 x, hn.2 x⟩).1 U le_rfl hU z hz).2 _ hbU fun p' _ y' hy' => ?_` and prove the remaining obligations. Set `w : Sp (PadicAlgCl p')` to `IsLocalRing.closedPoint (PadicAlgCl p')`.

Establish `hw : (gPt p' ≫ y') w ∈ (U : Set M.Z)` using `hy'.2 ⟨w, rfl⟩`. Establish `hle : S.R ≤ M.O ((gPt p' ≫ y') w)` using `hRU.trans (RatModel.ringOn_le_O hw)`. Set `y₀' : S.R →+* PadicAlgCl p'` to `(RatModel.valHom (gPt p' ≫ y') _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom`. Establish `hint : ∀ a : o, ‖y₀' (algebraMap o S.R a)‖ ≤ 1` using `fun a => hy'.norm_val_le_one (x := algebraMap o Ω a) ((M.O z).algebraMap_mem a)`. Establish `hAt' : S.At M y' y₀'` using `fun _ => rfl`.

Take `⟨τ'⟩` from `hT p' y₀' hint`. Take `⟨hδ', hH'⟩` from `norm_th_eq_and_HH_eq hy'.1 (fun a ha => hle ha) hAt' τ' hj`. Take `⟨β, -, -, hβ⟩` from `(thetaSys_norm_FF_le_exp o Ω S (test_weights o Ω S) p' y₀' τ' hint _ (τ.wt α) k hk τ.isoFree).2 (by rw [← hH', hH])`. Establish `hexp : Real.exp (-(τ'.q β / S.N)) ≤ 1` using `Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (nonneg_of_tendsto _ τ'.pos β) (Nat.cast_nonneg _)))`. Establish `hmul` using `val_mul_gen y' (RatModel.ringOn_le_O hw hbU) (hle (S.th_mem j))`.

Rewrite `hmul` using `[div_mul_cancel₀ _ hj.1]`. Rewrite `hβ` using `[hAt']`. Express the relevant statement in the definitionally equal form `‖M.val (gPt p' ≫ y') (S.FF _ (τ.wt α) k)‖ ≤ _ at hβ`. Rewrite `hβ` using `[hmul, norm_mul, hδ', mul_comm]`. Conclude with `(le_of_mul_le_mul_left hβ τ'.δ_pos).trans hexp`.

Establish `hmul` using `val_mul_gen y (RatModel.O_le_of_specializes (RatModel.gPt_specializes hc _) hreg) (hR _ (S.th_mem j))`. Rewrite `hmul` using `[div_mul_cancel₀ _ hj.1]`. Rewrite `he` using `[hAt]`. Express the relevant statement in the definitionally equal form `‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k)‖ = _ at he`. Rewrite `he` using `[hmul, norm_mul, hδ, mul_comm]`.

Establish `he'` using `mul_left_cancel₀ τ.δ_pos.ne' he`. Establish `hN : (0 : ℝ) < S.N`. Use `S.N_ge` as an intermediate fact. Conclude with `(by omega : 0 < S.N)` after adjusting the coercions. Establish `hlt : ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k / S.th j)‖ < 1`.

Rewrite using `[he']`. Conclude with `Real.exp_lt_one_iff.2 (neg_neg_of_pos (div_pos hpos hN))`. Establish `hnu` using `(RatModel.norm_val_lt_one_iff hc hreg).1 hlt`. Use `⟨(M.stalkEquiv z).symm ⟨_, hreg⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MulEquiv.isUnit_map]`.

Conclude with `hnu`. Rewrite using `[← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]`. Conclude with `he'.ge`.
-/
theorem exists_mem_maximalIdeal_exp_le_norm_val :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω),
    IsNormalScheme M.Z → M.HasDiv S.th → S.HasTests → ∀ (z₁ : M.Z), IsClosed ({z₁} : Set M.Z) →
    ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p), y (cPt p) = z₁ →
    (∀ a ∈ S.R, a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)))) → S.At M y y₀ →
    ∀ (τ : S.Test p y₀) (α : τ.X), (∀ v0, τ.q α ≤ τ.q (α + S.N • v0)) → 0 < τ.q α →
    ∃ h ∈ maximalIdeal (M.Z.presheaf.stalk z₁),
      Real.exp (-(τ.q α / S.N)) ≤ ‖M.val (gPt p ≫ y) (M.stalkHom z₁ h)‖ := by
  intro o Ω _ _ _ hb S M hn hd hT z hz p _ y y₀ hc hR hAt τ α hα hpos
  haveI := hb.ft
  haveI := hb.char
  obtain ⟨j, hj⟩ := hd z
  obtain ⟨hδ, hH⟩ := norm_th_eq_and_HH_eq hc hR hAt τ hj
  obtain ⟨k, hk, he⟩ := τ.eq α hα
  obtain ⟨U, hU, hRU, hbU⟩ := exists_open S M (S.FF _ (τ.wt α) k / S.th j)
  have hreg : S.FF _ (τ.wt α) k / S.th j ∈ M.O z := by
    refine ((classical_points_and_local_regularity o Ω M U fun x => ⟨hn.1 x, hn.2 x⟩).1 U le_rfl hU z hz).2 _ hbU fun p' _ y' hy' => ?_
    let w : Sp (PadicAlgCl p') := IsLocalRing.closedPoint (PadicAlgCl p')
    have hw : (gPt p' ≫ y') w ∈ (U : Set M.Z) := hy'.2 ⟨w, rfl⟩
    have hle : S.R ≤ M.O ((gPt p' ≫ y') w) := hRU.trans (RatModel.ringOn_le_O hw)
    let y₀' : S.R →+* PadicAlgCl p' :=
      (RatModel.valHom (gPt p' ≫ y') _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
    have hint : ∀ a : o, ‖y₀' (algebraMap o S.R a)‖ ≤ 1 := fun a =>
      hy'.norm_val_le_one (x := algebraMap o Ω a) ((M.O z).algebraMap_mem a)
    have hAt' : S.At M y' y₀' := fun _ => rfl
    obtain ⟨τ'⟩ := hT p' y₀' hint
    obtain ⟨hδ', hH'⟩ := norm_th_eq_and_HH_eq hy'.1 (fun a ha => hle ha) hAt' τ' hj
    obtain ⟨β, -, -, hβ⟩ := (thetaSys_norm_FF_le_exp o Ω S (test_weights o Ω S) p' y₀' τ' hint _ (τ.wt α) k hk
      τ.isoFree).2 (by rw [← hH', hH])
    have hexp : Real.exp (-(τ'.q β / S.N)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (nonneg_of_tendsto _ τ'.pos β) (Nat.cast_nonneg _)))
    have hmul := val_mul_gen y' (RatModel.ringOn_le_O hw hbU) (hle (S.th_mem j))
    rw [div_mul_cancel₀ _ hj.1] at hmul
    rw [hAt'] at hβ
    change ‖M.val (gPt p' ≫ y') (S.FF _ (τ.wt α) k)‖ ≤ _ at hβ
    rw [hmul, norm_mul, hδ', mul_comm] at hβ
    exact (le_of_mul_le_mul_left hβ τ'.δ_pos).trans hexp
  have hmul := val_mul_gen y (RatModel.O_le_of_specializes (RatModel.gPt_specializes hc _) hreg) (hR _ (S.th_mem j))
  rw [div_mul_cancel₀ _ hj.1] at hmul
  rw [hAt] at he
  change ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k)‖ = _ at he
  rw [hmul, norm_mul, hδ, mul_comm] at he
  have he' := mul_left_cancel₀ τ.δ_pos.ne' he
  have hN : (0 : ℝ) < S.N := by
    have := S.N_ge
    exact_mod_cast (by omega : 0 < S.N)
  have hlt : ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k / S.th j)‖ < 1 := by
    rw [he']
    exact Real.exp_lt_one_iff.2 (neg_neg_of_pos (div_pos hpos hN))
  have hnu := (RatModel.norm_val_lt_one_iff hc hreg).1 hlt
  refine ⟨(M.stalkEquiv z).symm ⟨_, hreg⟩, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MulEquiv.isUnit_map]
    exact hnu
  · rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    exact he'.ge

end GlobalTheory
