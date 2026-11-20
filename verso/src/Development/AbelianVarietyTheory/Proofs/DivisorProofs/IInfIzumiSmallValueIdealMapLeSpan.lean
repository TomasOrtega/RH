import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroClassicalPointOfLocalHomAvoidingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominatingLocalDomainEqMulMaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomPadicAlgClNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingEssFiniteTypeIntStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelLocalRingResidueFieldFiniteOfClosedPointStatement

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
open GlobalTheory.Izumi

noncomputable section
namespace GlobalTheory.Izumi

/- English proof (translation)
Introduce `A _ _ _`. Establish `h : IsHausdorff (maximalIdeal A) A` using `inferInstance`. Introduce `a b hab`. Conclude with `AdicCompletion.of_injective (maximalIdeal A) A (by simpa [AdicCompletion.algebraMap_apply] using hab)`.
-/
theorem algebraMap_completion_injective : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A], Function.Injective (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
  intro A _ _ _
  have h : IsHausdorff (maximalIdeal A) A := inferInstance
  intro a b hab
  exact AdicCompletion.of_injective (maximalIdeal A) A (by simpa [AdicCompletion.algebraMap_apply] using hab)

/- English proof (translation)
Introduce `A _ _ _ b`. Use `set ψ := AdicCompletion.evalₐ (maximalIdeal A) (R := A) 1`. Establish `hψ : ∀ r : A, ψ (algebraMap A (AdicCompletion (maximalIdeal A) A) r) = Ideal.Quotient.mk _ r` using `fun r => ψ.commutes r`. Take `⟨a, ha⟩` from `Ideal.Quotient.mk_surjective (ψ b)`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Establish `hu : IsUnit (b - algebraMap A (AdicCompletion (maximalIdeal A) A) a)`. Simplify `hn` using `[mem_maximalIdeal, mem_nonunits_iff]`. Establish `h0 : ψ (b - algebraMap A (AdicCompletion (maximalIdeal A) A) a) = 0`. Rewrite using `[map_sub, hψ, ha, sub_self]`.

Establish `h1` using `hu.map ψ`. Rewrite `h1` using `[h0]`. Use `haveI : Nontrivial (A ⧸ maximalIdeal A ^ 1) := by`. Rewrite using `[pow_one]`. Conclude with `Ideal.Quotient.nontrivial_iff.2 (maximalIdeal.isMaximal A).ne_top`.

Conclude with `not_isUnit_zero h1`.
-/
theorem exists_sub_algebraMap_mem_maximalIdeal_completion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (b : AdicCompletion (maximalIdeal A) A), ∃ a : A, b - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
  intro A _ _ _ b
  set ψ := AdicCompletion.evalₐ (maximalIdeal A) (R := A) 1
  have hψ : ∀ r : A, ψ (algebraMap A (AdicCompletion (maximalIdeal A) A) r) = Ideal.Quotient.mk _ r := fun r => ψ.commutes r
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ b)
  refine ⟨a, ?_⟩
  by_contra hn
  have hu : IsUnit (b - algebraMap A (AdicCompletion (maximalIdeal A) A) a) := by
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hn
  have h0 : ψ (b - algebraMap A (AdicCompletion (maximalIdeal A) A) a) = 0 := by
    rw [map_sub, hψ, ha, sub_self]
  have h1 := hu.map ψ
  rw [h0] at h1
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ 1) := by
    rw [pow_one]
    exact Ideal.Quotient.nontrivial_iff.2 (maximalIdeal.isMaximal A).ne_top
  exact not_isUnit_zero h1

/- English proof (translation)
Introduce `o Ω _ _ _ _ M U x f p _ y hy ψ hψ1 hψv G hG`. Use `haveI := ArithBase.ded (o := o) (Ω := Ω)`. Use `haveI : IsNoetherianRing (M.O x) := RatModel.isNoetherianRing_O M x`. Establish `hadd : ∀ a b : M.O x, ‖M.val (gPt p ≫ y) ((a + b : M.O x) : Ω)‖ ≤ max ‖M.val (gPt p ≫ y) (a : Ω)‖ ‖M.val (gPt p ≫ y) (b : Ω)‖` using `norm_val_add_le M hy`. Establish `hmul : ∀ c a : M.O x, ‖M.val (gPt p ≫ y) ((c * a : M.O x) : Ω)‖ ≤ ‖M.val (gPt p ≫ y) (a : Ω)‖` using `norm_val_mul_le M hy`.

Take `⟨S, hS⟩` from `(IsNoetherian.noetherian (maximalIdeal (M.O x)) : (maximalIdeal (M.O x)).FG)`. Use `set ρ : ℝ := ((S.sup fun g => ‖M.val (gPt p ≫ y) (g : Ω)‖₊ : NNReal) : ℝ) with hρdef`. Establish `hρ0 : 0 ≤ ρ` using `NNReal.coe_nonneg _`. Establish `hρ1 : ρ < 1`. Rewrite using `[hρdef, ← NNReal.coe_one, NNReal.coe_lt_coe, Finset.sup_lt_iff (by simp)]`.

Introduce `g hg`. Establish `hgm : g ∈ maximalIdeal (M.O x)` using `hS ▸ Submodule.subset_span hg`. Establish `h1` using `(hy.norm_val_lt_one_iff g.2).2 (by simpa using hgm)`. Rewrite using `[← NNReal.coe_lt_coe, coe_nnnorm]`. Simplify using `using h1`.

Establish `hρ : ∀ h ∈ maximalIdeal (M.O x), ‖M.val (gPt p ≫ y) (h : Ω)‖ ≤ ρ`. Introduce `h hh`. Rewrite `hh` using `[← hS]`. Proceed by induction on `hh using Submodule.span_induction with`. Consider the case `mem g hg`.

Rewrite using `[hρdef, ← coe_nnnorm, NNReal.coe_le_coe]`. Conclude with `Finset.le_sup (f := fun g : M.O x => ‖M.val (gPt p ≫ y) (g : Ω)‖₊) hg`. Consider the case `zero`. Establish `h0 : ((0 : M.O x) : Ω) = 0` using `rfl`. Rewrite using `[h0, RatModel.val_zero, norm_zero]`.

Conclude with `hρ0`. Consider the case `add a b _ _ ha hb => exact (hadd a b).trans (max_le ha hb)`. Consider the case `smul c a _ ha => exact (hmul c a).trans ha`. Establish `hnu : ∀ h, NonUnitAt M x h → ∀ hO : h ∈ M.O x, (⟨h, hO⟩ : M.O x) ∈ maximalIdeal (M.O x)`. Introduce `h hh hO`.

Rewrite using `[mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Break down `hh.2 with h0 | hinv` into its components or cases. Substitute `h0` using the available equality. Establish `: (⟨0, hO⟩ : M.O x) = 0` using `rfl`.

Rewrite `hu` using `[this]`. Conclude with `not_isUnit_zero hu`. Take `⟨w, hw⟩` from `hu.exists_right_inv`. Establish `e : h * (w : Ω) = 1` using `congrArg Subtype.val hw`. Apply `hinv` to reduce the goal to its premises.

Rewrite using `[← eq_inv_of_mul_eq_one_right e]`. Conclude with `w.2`. Establish `hN : ∀ N, ∀ g ∈ (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))), ‖ψ g‖ ≤ max ‖M.val (gPt p ≫ y) f‖ (ρ ^ N)`. Introduce `N g hg`. Proceed by induction on `hg using Submodule.span_induction with`.

Consider the case `mem g hg`. Take `⟨k, hk, rfl⟩` from `hg`. Rewrite using `[hψv]`. Break down `(mem_smallIdeal.1 hk) p y hy with h | ⟨h, hh, hle⟩` into its components or cases. Conclude with `h.trans (le_max_left _ _)`.

Use `le_max_of_le_right (hle.trans ?_)` and prove the remaining obligations. Conclude with `pow_le_pow_left₀ (norm_nonneg _) (hρ _ (hnu h hh hh.1)) N`. Consider the case `zero => rw [map_zero, norm_zero]`. Conclude with `le_max_of_le_right (pow_nonneg hρ0 N)`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)`. Consider the case `smul c a _ ha`. Rewrite using `[smul_eq_mul, map_mul, norm_mul]`. Conclude with `(mul_le_of_le_one_left (norm_nonneg _) (hψ1 c)).trans ha`. Assume the negation of the conclusion as `hlt`.

Use `push_neg at hlt`. Establish `hpos : 0 < ‖ψ G‖` using `lt_of_le_of_lt (norm_nonneg _) hlt`. Take `⟨N, hNlt⟩` from `exists_pow_lt_of_lt_one hpos hρ1`. Establish `h1` using `hN N G (Submodule.mem_iInf _ |>.1 hG N)`. Break down `le_max_iff.1 h1 with h2 | h2` into its components or cases.

Conclude with `absurd h2 (not_le.2 hlt)`. Conclude with `absurd h2 (not_le.2 hNlt)`.
-/
theorem norm_le_of_mem_iInf_map_smallIdeal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (U : M.Z.Opens) (x : M.Z) (f : Ω) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ∀ ψ : AdicCompletion (maximalIdeal (M.O x)) (M.O x) →+* PadicAlgCl p, (∀ g, ‖ψ g‖ ≤ 1) → (∀ a : M.O x, ψ (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x)) a) = M.val (gPt p ≫ y) a) → ∀ G ∈ ⨅ N, (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))), ‖ψ G‖ ≤ ‖M.val (gPt p ≫ y) f‖ := by
  intro o Ω _ _ _ _ M U x f p _ y hy ψ hψ1 hψv G hG
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI : IsNoetherianRing (M.O x) := RatModel.isNoetherianRing_O M x
  have hadd : ∀ a b : M.O x, ‖M.val (gPt p ≫ y) ((a + b : M.O x) : Ω)‖ ≤
      max ‖M.val (gPt p ≫ y) (a : Ω)‖ ‖M.val (gPt p ≫ y) (b : Ω)‖ := norm_val_add_le M hy
  have hmul : ∀ c a : M.O x, ‖M.val (gPt p ≫ y) ((c * a : M.O x) : Ω)‖ ≤ ‖M.val (gPt p ≫ y) (a : Ω)‖ :=
    norm_val_mul_le M hy
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (maximalIdeal (M.O x)) : (maximalIdeal (M.O x)).FG)
  set ρ : ℝ := ((S.sup fun g => ‖M.val (gPt p ≫ y) (g : Ω)‖₊ : NNReal) : ℝ) with hρdef
  have hρ0 : 0 ≤ ρ := NNReal.coe_nonneg _
  have hρ1 : ρ < 1 := by
    rw [hρdef, ← NNReal.coe_one, NNReal.coe_lt_coe, Finset.sup_lt_iff (by simp)]
    intro g hg
    have hgm : g ∈ maximalIdeal (M.O x) := hS ▸ Submodule.subset_span hg
    have h1 := (hy.norm_val_lt_one_iff g.2).2 (by simpa using hgm)
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    simpa using h1
  have hρ : ∀ h ∈ maximalIdeal (M.O x), ‖M.val (gPt p ≫ y) (h : Ω)‖ ≤ ρ := by
    intro h hh
    rw [← hS] at hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
      rw [hρdef, ← coe_nnnorm, NNReal.coe_le_coe]
      exact Finset.le_sup (f := fun g : M.O x => ‖M.val (gPt p ≫ y) (g : Ω)‖₊) hg
    | zero =>
      have h0 : ((0 : M.O x) : Ω) = 0 := rfl
      rw [h0, RatModel.val_zero, norm_zero]
      exact hρ0
    | add a b _ _ ha hb => exact (hadd a b).trans (max_le ha hb)
    | smul c a _ ha => exact (hmul c a).trans ha
  have hnu : ∀ h, NonUnitAt M x h → ∀ hO : h ∈ M.O x, (⟨h, hO⟩ : M.O x) ∈ maximalIdeal (M.O x) := by
    intro h hh hO
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rcases hh.2 with h0 | hinv
    · subst h0
      have : (⟨0, hO⟩ : M.O x) = 0 := rfl
      rw [this] at hu
      exact not_isUnit_zero hu
    · obtain ⟨w, hw⟩ := hu.exists_right_inv
      have e : h * (w : Ω) = 1 := congrArg Subtype.val hw
      apply hinv
      rw [← eq_inv_of_mul_eq_one_right e]
      exact w.2
  have hN : ∀ N, ∀ g ∈ (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))),
      ‖ψ g‖ ≤ max ‖M.val (gPt p ≫ y) f‖ (ρ ^ N) := by
    intro N g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      rw [hψv]
      rcases (mem_smallIdeal.1 hk) p y hy with h | ⟨h, hh, hle⟩
      · exact h.trans (le_max_left _ _)
      · refine le_max_of_le_right (hle.trans ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (hρ _ (hnu h hh hh.1)) N
    | zero => rw [map_zero, norm_zero]; exact le_max_of_le_right (pow_nonneg hρ0 N)
    | add a b _ _ ha hb => rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | smul c a _ ha =>
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hψ1 c)).trans ha
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < ‖ψ G‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  obtain ⟨N, hNlt⟩ := exists_pow_lt_of_lt_one hpos hρ1
  have h1 := hN N G (Submodule.mem_iInf _ |>.1 hG N)
  rcases le_max_iff.1 h1 with h2 | h2
  · exact absurd h2 (not_le.2 hlt)
  · exact absurd h2 (not_le.2 hNlt)

set_option maxHeartbeats 800000 in

/- English proof (translation)
Introduce `o Ω _ _ _ _ M hN U hU x hx f hf hf0`. Use `haveI := ArithBase.ded (o := o) (Ω := Ω)`. Use `haveI := ArithBase.char (o := o) (Ω := Ω)`. Use `haveI : IsNoetherianRing (M.O x) := RatModel.isNoetherianRing_O M x`. Use `haveI : IsIntegrallyClosed (M.O x) := RatModel.isIntegrallyClosed_O hN x`.

Use `haveI : CharZero (M.O x) := ⟨fun a b h => by`. Use `congrArg Subtype.val h` as an intermediate fact. Simplify using `using this⟩`. Use `haveI : Algebra.EssFiniteType ℤ (M.O x) := GlobalTheory.T.modelLocalRing_essFiniteType_int o Ω M x`. Use `haveI : Finite (ResidueField (M.O x)) := GlobalTheory.T.modelLocalRing_residueField_finite_of_closedPoint o Ω M x hx`.

Use `set A := M.O x with hA`. Use `set R := AdicCompletion (maximalIdeal A) A with hR`. Use `set φ := algebraMap A R with hφ`. Take `⟨hdom, hic⟩` from `GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed A`. Use `haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _`.

Establish `hinj : Function.Injective φ` using `algebraMap_completion_injective A`. Introduce `G hG`. Assume the negation of the conclusion as `hGf`. Take `⟨s, hs0, hs⟩` from `GlobalTheory.T.exists_nonzero_classicalPoint_of_localHom_avoiding o Ω M U hU x`. Take `⟨B, _, _, _, _, ι, hιinj, hιloc, hιres, u, hu, hfu⟩` from `GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal R (φ ⟨f, hf⟩) G hGf`.

Establish `hG0 : G ≠ 0`. Introduce and unpack `rfl`. Conclude with `hGf (Submodule.zero_mem _)`. Use `haveI : CharZero B := ⟨fun a b h => by`. Establish `h1 : ι (φ (a : A)) = ι (φ (b : A))` using `by simpa using h`.

Establish `h2` using `hinj (hιinj h1)`. Conclude with `h2⟩` after adjusting the coercions. Use `haveI : Finite (ResidueField B) := by`. Set `g : A → ResidueField B` to `fun a => residue B (ι (φ a))`. Establish `hg : Function.Surjective g`.

Introduce `c`. Take `⟨b, rfl⟩` from `residue_surjective c`. Take `⟨r, hr⟩` from `hιres b`. Take `⟨a, ha⟩` from `exists_sub_algebraMap_mem_maximalIdeal_completion A r`. Use `⟨a, ?_⟩` and prove the remaining obligations.

Establish `h1 : ι r - ι (φ a) ∈ maximalIdeal B`. Rewrite using `[← map_sub]`. Conclude with `map_nonunit ι _ ha`. Use `show residue B (ι (φ a)) = residue B b`. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff]`.

Use `Ideal.add_mem _ h1 hr` as an intermediate fact. Establish `e : ι (φ a) - b = -((ι r - ι (φ a)) + (b - ι r))` using `by ring`. Rewrite using `[e]`. Conclude with `(Ideal.neg_mem_iff _).2 this`. Establish `hker : ∀ a a' : A, a - a' ∈ maximalIdeal A → g a = g a'`.

Introduce `a a' h`. Use `show residue B _ = residue B _`. Rewrite using `[← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub, ← map_sub]`. Use `map_nonunit ι _ (map_nonunit φ _ h)` and prove the remaining obligations. Set `g' : ResidueField A → ResidueField B` to `fun c => g (Classical.choose (residue_surjective c))`.

Use `Finite.of_surjective g' fun c => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `hg c`. Use `⟨residue A a, hker _ _ ?_⟩` and prove the remaining obligations. Rewrite using `[← residue_eq_zero_iff, map_sub, Classical.choose_spec (residue_surjective (residue A a)), sub_self]`. Establish `hh : ι (G * φ s) ≠ 0`.

Rewrite using `[Ne, ← map_zero ι]`. Introduce `h`. Conclude with `mul_ne_zero hG0 ((map_ne_zero_iff φ hinj).2 hs0) (hιinj h)`. Take `⟨p, hp, χ, hχ1, hχm, hχh⟩` from `GlobalTheory.T.exists_ringHom_padicAlgCl_ne_zero' B inferInstance (ι (G * φ s)) hh`. Use `set ψ : R →+* PadicAlgCl p := χ.comp ι with hψ`.

Establish `hψ1 : ∀ g, ‖ψ g‖ ≤ 1` using `fun g => hχ1 _`. Establish `hψG : ψ G ≠ 0`. Introduce `h`. Apply `hχh` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul]`.

Simplify using `[hψ] at h`. Simplify using `[h]`. Establish `hψs : ψ (φ s) ≠ 0`. Introduce `h`. Apply `hχh` to reduce the goal to its premises.

Rewrite using `[map_mul, map_mul]`. Simplify using `[hψ] at h`. Simplify using `[h]`. Establish `hlt : ‖ψ (φ ⟨f, hf⟩)‖ < ‖ψ G‖`. Establish `e : ψ (φ ⟨f, hf⟩) = ψ G * χ u`.

Simplify using `only [hψ, RingHom.comp_apply, hfu, map_mul]`. Rewrite using `[e, norm_mul]`. Establish `h1 : ‖χ u‖ < 1` using `hχm u hu`. Establish `h2 : 0 < ‖ψ G‖` using `norm_pos_iff.2 hψG`. Use polynomial arithmetic with `[norm_nonneg (χ u)]`.

Set `χ0 : A →+* OO p` to `(ψ.comp φ).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hψ1 _)`. Establish `hloc : IsLocalHom χ0`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hna`. Establish `hm : a ∈ maximalIdeal A` using `hna`.

Establish `h1 : ι (φ a) ∈ maximalIdeal B` using `map_nonunit ι _ (map_nonunit φ _ hm)`. Establish `e : ((χ0 a : OO p) : PadicAlgCl p) = χ (ι (φ a))` using `rfl`. Establish `h2 : ‖((χ0 a : OO p) : PadicAlgCl p)‖ < 1` using `by rw [e]; exact hχm _ h1`. Conclude with `(not_isUnit_OO_iff (χ0 a)).2 h2 ha`. Establish `hχ0s : χ0 s ≠ 0` using `fun h => hψs (congrArg Subtype.val h)`.

Take `⟨y, hy, hval⟩` from `hs p χ0 hloc hχ0s`. Establish `hb` using `norm_le_of_mem_iInf_map_smallIdeal o Ω M U x f p y hy ψ hψ1 (fun a => (hval a).symm) G hG`. Establish `hf'` using `hval ⟨f, hf⟩`. Simplify using `only at hf'`. Rewrite `hb` using `[hf']`.

Conclude with `absurd hb (not_le.2 hlt)`.
-/
theorem iInf_map_smallIdeal_le_span : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ (f : Ω) (hf : f ∈ M.O x), f ≠ 0 → ⨅ N, (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))) ≤ Ideal.span {algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x)) ⟨f, hf⟩} := by
  intro o Ω _ _ _ _ M hN U hU x hx f hf hf0
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := ArithBase.char (o := o) (Ω := Ω)
  haveI : IsNoetherianRing (M.O x) := RatModel.isNoetherianRing_O M x
  haveI : IsIntegrallyClosed (M.O x) := RatModel.isIntegrallyClosed_O hN x
  haveI : CharZero (M.O x) := ⟨fun a b h => by
    have := congrArg Subtype.val h
    simpa using this⟩
  haveI : Algebra.EssFiniteType ℤ (M.O x) := GlobalTheory.T.modelLocalRing_essFiniteType_int o Ω M x
  haveI : Finite (ResidueField (M.O x)) := GlobalTheory.T.modelLocalRing_residueField_finite_of_closedPoint o Ω M x hx
  set A := M.O x with hA
  set R := AdicCompletion (maximalIdeal A) A with hR
  set φ := algebraMap A R with hφ
  obtain ⟨hdom, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed A
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  have hinj : Function.Injective φ := algebraMap_completion_injective A
  intro G hG
  by_contra hGf
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.exists_nonzero_classicalPoint_of_localHom_avoiding o Ω M U hU x
  obtain ⟨B, _, _, _, _, ι, hιinj, hιloc, hιres, u, hu, hfu⟩ := GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal R (φ ⟨f, hf⟩) G hGf
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hGf (Submodule.zero_mem _)
  haveI : CharZero B := ⟨fun a b h => by
    have h1 : ι (φ (a : A)) = ι (φ (b : A)) := by simpa using h
    have h2 := hinj (hιinj h1)
    exact_mod_cast h2⟩
  haveI : Finite (ResidueField B) := by
    let g : A → ResidueField B := fun a => residue B (ι (φ a))
    have hg : Function.Surjective g := by
      intro c
      obtain ⟨b, rfl⟩ := residue_surjective c
      obtain ⟨r, hr⟩ := hιres b
      obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_maximalIdeal_completion A r
      refine ⟨a, ?_⟩
      have h1 : ι r - ι (φ a) ∈ maximalIdeal B := by
        rw [← map_sub]
        exact map_nonunit ι _ ha
      show residue B (ι (φ a)) = residue B b
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      have := Ideal.add_mem _ h1 hr
      have e : ι (φ a) - b = -((ι r - ι (φ a)) + (b - ι r)) := by ring
      rw [e]
      exact (Ideal.neg_mem_iff _).2 this
    have hker : ∀ a a' : A, a - a' ∈ maximalIdeal A → g a = g a' := by
      intro a a' h
      show residue B _ = residue B _
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub, ← map_sub]
      refine map_nonunit ι _ (map_nonunit φ _ h)
    let g' : ResidueField A → ResidueField B := fun c => g (Classical.choose (residue_surjective c))
    refine Finite.of_surjective g' fun c => ?_
    obtain ⟨a, rfl⟩ := hg c
    refine ⟨residue A a, hker _ _ ?_⟩
    rw [← residue_eq_zero_iff, map_sub, Classical.choose_spec (residue_surjective (residue A a)), sub_self]
  have hh : ι (G * φ s) ≠ 0 := by
    rw [Ne, ← map_zero ι]
    intro h
    exact mul_ne_zero hG0 ((map_ne_zero_iff φ hinj).2 hs0) (hιinj h)
  obtain ⟨p, hp, χ, hχ1, hχm, hχh⟩ := GlobalTheory.T.exists_ringHom_padicAlgCl_ne_zero' B inferInstance (ι (G * φ s)) hh
  set ψ : R →+* PadicAlgCl p := χ.comp ι with hψ
  have hψ1 : ∀ g, ‖ψ g‖ ≤ 1 := fun g => hχ1 _
  have hψG : ψ G ≠ 0 := by
    intro h; apply hχh; rw [map_mul, map_mul]; simp [hψ] at h; simp [h]
  have hψs : ψ (φ s) ≠ 0 := by
    intro h; apply hχh; rw [map_mul, map_mul]; simp [hψ] at h; simp [h]
  have hlt : ‖ψ (φ ⟨f, hf⟩)‖ < ‖ψ G‖ := by
    have e : ψ (φ ⟨f, hf⟩) = ψ G * χ u := by
      simp only [hψ, RingHom.comp_apply, hfu, map_mul]
    rw [e, norm_mul]
    have h1 : ‖χ u‖ < 1 := hχm u hu
    have h2 : 0 < ‖ψ G‖ := norm_pos_iff.2 hψG
    nlinarith [norm_nonneg (χ u)]
  let χ0 : A →+* OO p := (ψ.comp φ).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hψ1 _)
  have hloc : IsLocalHom χ0 := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal A := hna
    have h1 : ι (φ a) ∈ maximalIdeal B := map_nonunit ι _ (map_nonunit φ _ hm)
    have e : ((χ0 a : OO p) : PadicAlgCl p) = χ (ι (φ a)) := rfl
    have h2 : ‖((χ0 a : OO p) : PadicAlgCl p)‖ < 1 := by rw [e]; exact hχm _ h1
    exact (not_isUnit_OO_iff (χ0 a)).2 h2 ha
  have hχ0s : χ0 s ≠ 0 := fun h => hψs (congrArg Subtype.val h)
  obtain ⟨y, hy, hval⟩ := hs p χ0 hloc hχ0s
  have hb := norm_le_of_mem_iInf_map_smallIdeal o Ω M U x f p y hy ψ hψ1 (fun a => (hval a).symm) G hG
  have hf' := hval ⟨f, hf⟩
  simp only at hf'
  rw [hf'] at hb
  exact absurd hb (not_le.2 hlt)

end GlobalTheory.Izumi
