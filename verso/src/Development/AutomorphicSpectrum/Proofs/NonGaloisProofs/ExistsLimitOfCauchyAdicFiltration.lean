import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GoodOAdicCompleteCompactBasisStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfNormLeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsMore
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.CobDetect

open CategoryTheory in

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.DYdc6.main f`.
-/
theorem exists_compat {X : ℕ → Type} [∀ n, Finite (X n)] [∀ n, Nonempty (X n)]
    (f : ∀ n, X (n + 1) → X n) : ∃ x : ∀ n, X n, ∀ n, f n (x (n + 1)) = x n :=
  _root_.UpperTheory.Reformulated.B.DYdc6.main f

section Lim

variable {G : Type} [Group G] [TopologicalSpace G] {LL : Type} [Field LL] {O : Type} [CommRing O]
    [Algebra O LL] {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (ϖ : O)

abbrev pw (n : ℕ) : Submodule O ↥L.T := Ideal.span {ϖ ^ n} • ⊤

/- English proof (translation)
Rewrite using `[pw, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, rfl⟩`. Conclude with `⟨y, rfl⟩`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨y, trivial, rfl⟩`.
-/
theorem mem_pw {n : ℕ} {x : ↥L.T} : x ∈ pw L ϖ n ↔ ∃ y : ↥L.T, x = ϖ ^ n • y := by
  rw [pw, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, trivial, rfl⟩

/- English proof (translation)
Introduce `g x hx`. Take `⟨y, rfl⟩` from `(mem_pw L ϖ).1 hx`. Conclude with `(mem_pw L ϖ).2 ⟨actT L g y, map_smul _ _ _⟩`.
-/
theorem stable_pw (n : ℕ) : StableSub L (pw L ϖ n) := by
  intro g x hx
  obtain ⟨y, rfl⟩ := (mem_pw L ϖ).1 hx
  exact (mem_pw L ϖ).2 ⟨actT L g y, map_smul _ _ _⟩

/- English proof (translation)
Introduce `x hx`. Take `⟨y, rfl⟩` from `(mem_pw L ϖ).1 hx`. Conclude with `(mem_pw L ϖ).2 ⟨ϖ • y, by rw [pow_succ, mul_smul]⟩`.
-/
theorem pw_succ_le (n : ℕ) : pw L ϖ (n + 1) ≤ pw L ϖ n := by
  intro x hx
  obtain ⟨y, rfl⟩ := (mem_pw L ϖ).1 hx
  exact (mem_pw L ϖ).2 ⟨ϖ • y, by rw [pow_succ, mul_smul]⟩

def proj (n : ℕ) : (↥L.T ⧸ pw L ϖ (n + 1)) →ₗ[O] (↥L.T ⧸ pw L ϖ n) :=
  Submodule.mapQ _ _ LinearMap.id (pw_succ_le L ϖ n)

/- English proof (translation)
The claim follows from `Submodule.mapQ_apply _ _ _ _`.
-/
theorem proj_mk (n : ℕ) (y : ↥L.T) :
    proj L ϖ n (Submodule.Quotient.mk y) = Submodule.Quotient.mk y :=
  Submodule.mapQ_apply _ _ _ _

/- English proof (translation)
The claim follows from `Submodule.mapQ_apply _ _ _ _`.
-/
theorem actQ_mk (I : Submodule O ↥L.T) (hI : StableSub L I) (g : G) (y : ↥L.T) :
    actQ L I hI g (Submodule.Quotient.mk y) = Submodule.Quotient.mk (actT L g y) :=
  Submodule.mapQ_apply _ _ _ _

def Sol (w : G × G → ↥L.T) (n : ℕ) (c : G → ↥L.T ⧸ pw L ϖ n) : Prop :=
  IsLocallyConstant c ∧ ∀ g h, actQ L _ (stable_pw L ϖ n) g (c h) - c (g * h) + c g =
    Submodule.Quotient.mk (w (g, h))

/- English proof (translation)
Use `⟨hc.1.comp _, fun g h => ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (CobDetect.proj L ϖ n) (hc.2 g h)`. Rewrite `h1` using `[map_add, map_sub, proj_mk]`. Rewrite using `[← h1]`. Take `⟨y, hy⟩` from `Submodule.Quotient.mk_surjective _ (c h)`.

Use `beta_reduce`. Rewrite using `[← hy, proj_mk, actQ_mk, actQ_mk, proj_mk]`.
-/
theorem Sol.proj {w : G × G → ↥L.T} {n : ℕ} {c : G → ↥L.T ⧸ pw L ϖ (n + 1)} (hc : Sol L ϖ w (n + 1) c) :
    Sol L ϖ w n fun g => proj L ϖ n (c g) := by
  refine ⟨hc.1.comp _, fun g h => ?_⟩
  have h1 := congrArg (CobDetect.proj L ϖ n) (hc.2 g h)
  rw [map_add, map_sub, proj_mk] at h1
  rw [← h1]
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (c h)
  beta_reduce
  rw [← hy, proj_mk, actQ_mk, actQ_mk, proj_mk]

/- English proof (translation)
Distinguish the cases in `hne : Nonempty {c // Sol L ϖ w n c}`. Take `⟨c₀, h₀⟩` from `hne`. Establish `hm : ∀ c : {c // Sol L ϖ w n c}, c.1 - c₀ ∈ quotientCocycles L (pw L ϖ n) (stable_pw L ϖ n)`. Introduce and unpack `⟨c, hc⟩`. Use `⟨hc.1.sub h₀.1, fun g h => ?_⟩` and prove the remaining obligations.

Establish `h1` using `(hc.2 g h).trans (h₀.2 g h).symm`. Simplify using `only [Pi.sub_apply, map_sub]`. Use `grind`. Use `Finite.of_injective (fun c => (⟨c.1 - c₀, hm c⟩ : ↥(quotientCocycles L (pw L ϖ n) (stable_pw L ϖ n)))) fun a b hab => ?_` and prove the remaining obligations. Conclude with `Subtype.ext (sub_left_injective (congrArg Subtype.val hab))`.

Use `haveI := not_nonempty_iff.1 hne infer_instance`.
-/
theorem finite_sol (w : G × G → ↥L.T) (n : ℕ) (hfin : Finite ↥(quotientCocycles L (pw L ϖ n) (stable_pw L ϖ n))) :
    Finite {c // Sol L ϖ w n c} := by
  by_cases hne : Nonempty {c // Sol L ϖ w n c}
  · obtain ⟨c₀, h₀⟩ := hne
    have hm : ∀ c : {c // Sol L ϖ w n c}, c.1 - c₀ ∈ quotientCocycles L (pw L ϖ n) (stable_pw L ϖ n) := by
      rintro ⟨c, hc⟩
      refine ⟨hc.1.sub h₀.1, fun g h => ?_⟩
      have h1 := (hc.2 g h).trans (h₀.2 g h).symm
      simp only [Pi.sub_apply, map_sub]
      grind
    refine Finite.of_injective (fun c => (⟨c.1 - c₀, hm c⟩ :
      ↥(quotientCocycles L (pw L ϖ n) (stable_pw L ϖ n)))) fun a b hab => ?_
    exact Subtype.ext (sub_left_injective (congrArg Subtype.val hab))
  · haveI := not_nonempty_iff.1 hne
    infer_instance

/- English proof (translation)
Use `haveI : ∀ n, Finite {c // Sol L ϖ w n c} := fun n => finite_sol L ϖ w n (hfin n)`. Use `haveI : ∀ n, Nonempty {c // Sol L ϖ w n c} := fun n =>`. Set `⟨c, hc⟩` to `hne n`. Use the proof step `⟨⟨c, hc⟩⟩`. Take `⟨x, hx⟩` from `exists_compat (X := fun n => {c // Sol L ϖ w n c}) (fun n c => ⟨fun g => proj L ϖ n (c.1 g), c.2.proj⟩)`.

Use `choose a ha using fun n g => Submodule.Quotient.mk_surjective (pw L ϖ n) ((x n).1 g)`. Establish `step : ∀ g n, a (n + 1) g - a n g ∈ pw L ϖ n`. Introduce `g n`. Rewrite using `[← Submodule.Quotient.eq]`. Establish `h1 : proj L ϖ n ((x (n + 1)).1 g) = (x n).1 g` using `congrFun (congrArg Subtype.val (hx n)) g`.

Rewrite using `[ha n g, ← h1, ← ha (n + 1) g, proj_mk]`. Use `choose F hF using fun g => hC (fun n => a n g) (step g)`. Establish `hmk : ∀ n g, (Submodule.Quotient.mk (F g) : ↥L.T ⧸ pw L ϖ n) = (x n).1 g`. Introduce `n g`. Rewrite using `[← ha n g]`.

Conclude with `(Submodule.Quotient.eq _).2 (hF g n)`. Use `⟨F, fun n => ?_, fun g h => ?_⟩` and prove the remaining obligations. Repeatedly rewrite using `[hmk n]`. Conclude with `(x n).2.1`. Rewrite using `[← sub_eq_zero]`.

Use `hS _ fun n => ?_` and prove the remaining obligations. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add, Submodule.Quotient.mk_sub, sub_eq_zero, hmk n, hmk n, ← (x n).2.2 g h, ← hmk n h, actQ_mk]`.
-/
theorem exists_limit (w : G × G → ↥L.T)
    (hfin : ∀ n, Finite ↥(quotientCocycles L (pw L ϖ n) (stable_pw L ϖ n)))
    (hne : ∀ n, ∃ c, Sol L ϖ w n c)
    (hC : ∀ a : ℕ → ↥L.T, (∀ n, a (n + 1) - a n ∈ pw L ϖ n) → ∃ b, ∀ n, b - a n ∈ pw L ϖ n)
    (hS : ∀ x : ↥L.T, (∀ n, x ∈ pw L ϖ n) → x = 0) :
    ∃ F : G → ↥L.T, (∀ n, IsLocallyConstant fun g => (Submodule.Quotient.mk (F g) : ↥L.T ⧸ pw L ϖ n)) ∧
      ∀ g h, actT L g (F h) - F (g * h) + F g = w (g, h) := by
  haveI : ∀ n, Finite {c // Sol L ϖ w n c} := fun n => finite_sol L ϖ w n (hfin n)
  haveI : ∀ n, Nonempty {c // Sol L ϖ w n c} := fun n =>
    let ⟨c, hc⟩ := hne n
    ⟨⟨c, hc⟩⟩
  obtain ⟨x, hx⟩ := exists_compat (X := fun n => {c // Sol L ϖ w n c})
    (fun n c => ⟨fun g => proj L ϖ n (c.1 g), c.2.proj⟩)
  choose a ha using fun n g => Submodule.Quotient.mk_surjective (pw L ϖ n) ((x n).1 g)
  have step : ∀ g n, a (n + 1) g - a n g ∈ pw L ϖ n := by
    intro g n
    rw [← Submodule.Quotient.eq]
    have h1 : proj L ϖ n ((x (n + 1)).1 g) = (x n).1 g := congrFun (congrArg Subtype.val (hx n)) g
    rw [ha n g, ← h1, ← ha (n + 1) g, proj_mk]
  choose F hF using fun g => hC (fun n => a n g) (step g)
  have hmk : ∀ n g, (Submodule.Quotient.mk (F g) : ↥L.T ⧸ pw L ϖ n) = (x n).1 g := by
    intro n g
    rw [← ha n g]
    exact (Submodule.Quotient.eq _).2 (hF g n)
  refine ⟨F, fun n => ?_, fun g h => ?_⟩
  · simp_rw [hmk n]
    exact (x n).2.1
  · rw [← sub_eq_zero]
    refine hS _ fun n => ?_
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add,
      Submodule.Quotient.mk_sub, sub_eq_zero, hmk n, hmk n, ← (x n).2.2 g h, ← hmk n h, actQ_mk]

end Lim

section Adic

variable {O : Type} [CommRing O] (ϖ : O)

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`.
-/
theorem pow_smul_top (m : ℕ) :
    ((Ideal.span {ϖ}) ^ m • ⊤ : Submodule O O) = Ideal.span {ϖ ^ m} := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]

/- English proof (translation)
Establish `hle : ∀ m n, m ≤ n → a n - a m ∈ Ideal.span {ϖ ^ m}`. Introduce `m n hmn`. Proceed by induction on `n, hmn using Nat.le_induction with`. Consider the case `base => simp`. Consider the case `succ n hmn ih`.

Establish `h1 : Ideal.span {ϖ ^ n} ≤ Ideal.span {ϖ ^ m}` using `Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ hmn)`. Establish `h2` using `Ideal.add_mem _ (h1 (h n)) ih`. Simplify using `using h2`. Take `⟨L, hL⟩` from `hc.toIsPrecomplete.prec (f := a) (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, pow_smul_top, ← neg_sub]`.

Conclude with `Ideal.neg_mem_iff _ |>.2 (hle m n hmn))`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations. Establish `h1` using `SModEq.sub_mem.1 (hL n)`. Rewrite `h1` using `[pow_smul_top, ← neg_sub]`. Conclude with `(Ideal.neg_mem_iff _).1 h1`.
-/
theorem lim_O (hc : IsAdicComplete (Ideal.span {ϖ}) O) (a : ℕ → O)
    (h : ∀ n, a (n + 1) - a n ∈ Ideal.span {ϖ ^ n}) :
    ∃ b, ∀ n, b - a n ∈ Ideal.span {ϖ ^ n} := by
  have hle : ∀ m n, m ≤ n → a n - a m ∈ Ideal.span {ϖ ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : Ideal.span {ϖ ^ n} ≤ Ideal.span {ϖ ^ m} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ hmn)
      have h2 := Ideal.add_mem _ (h1 (h n)) ih
      simpa using h2
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec (f := a) (fun {m n} hmn => by
    rw [SModEq.sub_mem, pow_smul_top, ← neg_sub]
    exact Ideal.neg_mem_iff _ |>.2 (hle m n hmn))
  refine ⟨L, fun n => ?_⟩
  have h1 := SModEq.sub_mem.1 (hL n)
  rw [pow_smul_top, ← neg_sub] at h1
  exact (Ideal.neg_mem_iff _).1 h1

/- English proof (translation)
Use `hc.toIsHausdorff.haus' x fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.zero, pow_smul_top]`. Conclude with `h n`.
-/
theorem sep_O (hc : IsAdicComplete (Ideal.span {ϖ}) O) (x : O)
    (h : ∀ n, x ∈ Ideal.span {ϖ ^ n}) : x = 0 := by
  refine hc.toIsHausdorff.haus' x fun n => ?_
  rw [SModEq.zero, pow_smul_top]
  exact h n

end Adic

section Cyc

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O] [Algebra O LL]

/- English proof (translation)
Simplify using `[charRep]`.
-/
theorem charRep_apply (g : G) (y : LL) :
    charRep (cycLL PD LL) g y = ((cycLL PD LL g : LLˣ) : LL) * y := by
  simp [charRep]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem repD_mk {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : WeaklyAdmissibleFiltrations.Lattice (O := O) ρ) (g : G) (y : V) :
    repD L g (Submodule.Quotient.mk y) = Submodule.Quotient.mk (ρ g y) :=
  rfl

variable {PD} (L1 : WeaklyAdmissibleFiltrations.Lattice (O := O) (charRep (cycLL PD LL)))

/- English proof (translation)
Take `⟨f, hf, rfl⟩` from `h`. Unfold `CobO`. Use `Submodule.mem_map.2 ⟨fun g => Submodule.Quotient.mk (a * f g), ⟨?_, fun _ => trivial⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g₀`.

Establish `hc : Continuous fun g => a * f g - a * f g₀` using `(continuous_const.mul hf).sub continuous_const`. Establish `h0 : (L1.T : Set LL) ∈ nhds ((fun g => a * f g - a * f g₀) g₀)`. Simplify using `using hop.mem_nhds L1.T.zero_mem`. Use `filter_upwards [hc.continuousAt h0] with g hg`. Conclude with `(Submodule.Quotient.eq _).2 hg`.

Use function extensionality and compare the values at `x`. Express the relevant statement in the definitionally equal form `repD L1 x.1 (Submodule.Quotient.mk (a * f x.2)) - Submodule.Quotient.mk (a * f (x.1 * x.2)) + Submodule.Quotient.mk (a * f x.1) = Submodule.Quotient.mk (a * (charRep (cycLL PD LL) x.1 (f x.2) - f (x.1 * x.2) + f x.1))`. Rewrite using `[repD_mk, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, charRep_apply, charRep_apply]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cobO_of_cobL [IsTopologicalRing LL] (hop : IsOpen (L1.T : Set LL)) {z : G × G → LL}
    (h : CobL PD z) (a : LL) : CobO PD L1 (a • z) := by
  obtain ⟨f, hf, rfl⟩ := h
  unfold CobO
  refine Submodule.mem_map.2 ⟨fun g => Submodule.Quotient.mk (a * f g), ⟨?_, fun _ => trivial⟩, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro g₀
    have hc : Continuous fun g => a * f g - a * f g₀ :=
      (continuous_const.mul hf).sub continuous_const
    have h0 : (L1.T : Set LL) ∈ nhds ((fun g => a * f g - a * f g₀) g₀) := by
      simpa using hop.mem_nhds L1.T.zero_mem
    filter_upwards [hc.continuousAt h0] with g hg
    exact (Submodule.Quotient.eq _).2 hg
  · funext x
    change repD L1 x.1 (Submodule.Quotient.mk (a * f x.2)) - Submodule.Quotient.mk (a * f (x.1 * x.2)) +
      Submodule.Quotient.mk (a * f x.1) = Submodule.Quotient.mk
        (a * (charRep (cycLL PD LL) x.1 (f x.2) - f (x.1 * x.2) + f x.1))
    rw [repD_mk, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add, charRep_apply, charRep_apply]
    congr 1
    ring

/- English proof (translation)
Rewrite using `[hT]`. Both sides reduce to the same expression.
-/
theorem mem_T (hT : L1.T = LinearMap.range (Algebra.linearMap O LL)) {y : LL} :
    y ∈ L1.T ↔ ∃ o : O, algebraMap O LL o = y := by
  rw [hT]
  rfl

def eT (hT : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (hinj : Function.Injective (algebraMap O LL)) : O ≃ₗ[O] ↥L1.T :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict L1.T (Algebra.linearMap O LL) fun o => (mem_T L1 hT).2 ⟨o, rfl⟩)
    ⟨fun a b h => hinj (congrArg Subtype.val h), fun y => by
      obtain ⟨o, ho⟩ := (mem_T L1 hT).1 y.2
      exact ⟨o, Subtype.ext ho⟩⟩

/- English proof (translation)
Rewrite using `[mem_pw, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `⟨(eT L1 hT hinj).symm y, (eT L1 hT hinj).injective ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, ← smul_eq_mul, map_smul, LinearEquiv.apply_symm_apply, hy]`.

Introduce and unpack `⟨c, rfl⟩`. Use `⟨eT L1 hT hinj c, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm, ← smul_eq_mul, map_smul]`.
-/
theorem eT_mem_pw_iff (hT : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (hinj : Function.Injective (algebraMap O LL)) (ϖ : O) (n : ℕ) (o : O) :
    eT L1 hT hinj o ∈ pw L1 ϖ n ↔ o ∈ Ideal.span {ϖ ^ n} := by
  rw [mem_pw, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(eT L1 hT hinj).symm y, (eT L1 hT hinj).injective ?_⟩
    rw [mul_comm, ← smul_eq_mul, map_smul, LinearEquiv.apply_symm_apply, hy]
  · rintro ⟨c, rfl⟩
    refine ⟨eT L1 hT hinj c, ?_⟩
    rw [mul_comm, ← smul_eq_mul, map_smul]

/- English proof (translation)
Use `set e := eT L1 hT hinj with he`. Take `⟨b, hb⟩` from `lim_O ϖ hc (fun n => e.symm (a n)) fun n => by`. Rewrite using `[← eT_mem_pw_iff L1 hT hinj, ← he, map_sub, e.apply_symm_apply, e.apply_symm_apply]`. Conclude with `h n`. Use `⟨e b, fun n => ?_⟩` and prove the remaining obligations.

Establish `h1` using `(eT_mem_pw_iff L1 hT hinj ϖ n _).2 (hb n)`. Rewrite `h1` using `[← he, map_sub, e.apply_symm_apply]`. Then use the resulting hypothesis.
-/
theorem exists_limit_of_cauchy_adic_filtration (hT : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (hinj : Function.Injective (algebraMap O LL)) (ϖ : O) (hc : IsAdicComplete (Ideal.span {ϖ}) O)
    (a : ℕ → ↥L1.T) (h : ∀ n, a (n + 1) - a n ∈ pw L1 ϖ n) :
    ∃ b, ∀ n, b - a n ∈ pw L1 ϖ n := by
  set e := eT L1 hT hinj with he
  obtain ⟨b, hb⟩ := lim_O ϖ hc (fun n => e.symm (a n)) fun n => by
    rw [← eT_mem_pw_iff L1 hT hinj, ← he, map_sub, e.apply_symm_apply, e.apply_symm_apply]
    exact h n
  refine ⟨e b, fun n => ?_⟩
  have h1 := (eT_mem_pw_iff L1 hT hinj ϖ n _).2 (hb n)
  rwa [← he, map_sub, e.apply_symm_apply] at h1

/- English proof (translation)
Use `set e := eT L1 hT hinj with he`. Establish `h0 : e.symm x = 0` using `sep_O ϖ hc _ fun n => by`. Rewrite using `[← eT_mem_pw_iff L1 hT hinj, ← he, e.apply_symm_apply]`. Conclude with `h n`. Simplify using `using h0`.
-/
theorem sep_T (hT : L1.T = LinearMap.range (Algebra.linearMap O LL))
    (hinj : Function.Injective (algebraMap O LL)) (ϖ : O) (hc : IsAdicComplete (Ideal.span {ϖ}) O)
    (x : ↥L1.T) (h : ∀ n, x ∈ pw L1 ϖ n) : x = 0 := by
  set e := eT L1 hT hinj with he
  have h0 : e.symm x = 0 := sep_O ϖ hc _ fun n => by
    rw [← eT_mem_pw_iff L1 hT hinj, ← he, e.apply_symm_apply]
    exact h n
  simpa using h0

/- English proof (translation)
Set `U : ℕ → Set LL` to `fun n => {y | algebraMap O LL ϖ ^ n * y ∈ Set.range (algebraMap O LL)}`. Establish `hU : ∀ n, IsOpen (U n)` using `fun n => hop.preimage (continuous_const.mul continuous_id)`. Establish `hmono : Monotone U`. Use `monotone_nat_of_le_succ fun n y hy => ?_` and prove the remaining obligations. Take `⟨o, ho⟩` from `hy`.

Use `⟨ϖ * o, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ho, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcov : Set.range z ⊆ ⋃ n, U n`. Introduce `y _`.

Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := O) y`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ`. Establish `hb1 : algebraMap O LL b ≠ 0` using `fun h0 => hb0 (IsFractionRing.injective O LL (h0.trans (map_zero _).symm))`. Use `Set.mem_iUnion.2 ⟨n, (u : O) * a, ?_⟩` and prove the remaining obligations.

Establish `hu' : algebraMap O LL b * algebraMap O LL (u : O) = algebraMap O LL ϖ ^ n`. Rewrite using `[← map_mul, hu, map_pow]`. Rewrite using `[← hu', map_mul]`. Clear the denominators using the available nonvanishing facts. Take `⟨s, hs⟩` from `(isCompact_range hz).elim_directed_cover U hU hcov hmono.directed_le`.

Conclude with `⟨s, fun x => hs ⟨x, rfl⟩⟩`.
-/
theorem exists_scale {X : Type} [TopologicalSpace X] [CompactSpace X] [IsTopologicalRing LL] [IsDomain O]
    [IsDiscreteValuationRing O] [IsFractionRing O LL] {ϖ : O} (hϖ : Irreducible ϖ)
    (hop : IsOpen (Set.range (algebraMap O LL))) {z : X → LL} (hz : Continuous z) :
    ∃ s : ℕ, ∀ x, algebraMap O LL ϖ ^ s * z x ∈ Set.range (algebraMap O LL) := by
  let U : ℕ → Set LL := fun n => {y | algebraMap O LL ϖ ^ n * y ∈ Set.range (algebraMap O LL)}
  have hU : ∀ n, IsOpen (U n) := fun n => hop.preimage (continuous_const.mul continuous_id)
  have hmono : Monotone U := by
    refine monotone_nat_of_le_succ fun n y hy => ?_
    obtain ⟨o, ho⟩ := hy
    refine ⟨ϖ * o, ?_⟩
    rw [map_mul, ho, pow_succ]
    ring
  have hcov : Set.range z ⊆ ⋃ n, U n := by
    intro y _
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) y
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hb0 hϖ
    have hb1 : algebraMap O LL b ≠ 0 := fun h0 =>
      hb0 (IsFractionRing.injective O LL (h0.trans (map_zero _).symm))
    refine Set.mem_iUnion.2 ⟨n, (u : O) * a, ?_⟩
    have hu' : algebraMap O LL b * algebraMap O LL (u : O) = algebraMap O LL ϖ ^ n := by
      rw [← map_mul, hu, map_pow]
    rw [← hu', map_mul]
    field_simp
  obtain ⟨s, hs⟩ := (isCompact_range hz).elim_directed_cover U hU hcov hmono.directed_le
  exact ⟨s, fun x => hs ⟨x, rfl⟩⟩

/- English proof (translation)
Use `set u := algebraMap O LL ϖ with hudef`. Use `set a : LL := u⁻¹ ^ n * u ^ s with ha`. Establish `hna : u ^ n * a = u ^ s`. Rewrite using `[ha, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, one_mul]`. Take `⟨f, hf1, hf2, hf3⟩` from `hTop n (a • z) (fun x => by`.

Establish `h1 : u ^ n * (a • z) x = ((w x : ↥L1.T) : LL)`. Rewrite using `[hw, Pi.smul_apply, smul_eq_mul, ← mul_assoc, hna]`. Rewrite using `[h1]`. Conclude with `(w x).2) (h a)`. Establish `hsm : ∀ y : ↥L1.T, ((ϖ ^ n • y : ↥L1.T) : LL) = u ^ n * (y : LL)`.

Introduce `y`. Rewrite using `[Submodule.coe_smul, Algebra.smul_def, map_pow]`. Use `⟨fun g => Submodule.Quotient.mk (⟨u ^ n * f g, hf1 g⟩ : ↥L1.T), ?_, fun g h' => ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g₀`.

Use `filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 hf2 g₀] with g hg`. Establish `h1 : f g - f g₀ ∈ L1.T` using `(Submodule.Quotient.eq _).1 hg`. Use `(Submodule.Quotient.eq _).2 ((mem_pw L1 ϖ).2 ⟨⟨_, h1⟩, Subtype.ext ?_⟩)` and prove the remaining obligations. Rewrite using `[hsm]`. Express the relevant statement in the definitionally equal form `u ^ n * f g - u ^ n * f g₀ = _`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[actQ_mk, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]`. Use `(Submodule.Quotient.eq _).2 ((mem_pw L1 ϖ).2 ⟨⟨_, hf3 (g, h')⟩, Subtype.ext ?_⟩)` and prove the remaining obligations. Rewrite using `[hsm]`. Express the relevant statement in the definitionally equal form `charRep (cycLL PD LL) g (u ^ n * f h') - u ^ n * f (g * h') + u ^ n * f g - ((w (g, h') : ↥L1.T) : LL) = u ^ n * (charRep (cycLL PD LL) g (f h') - f (g * h') + f g - (a • z) (g, h'))`.

Rewrite using `[hw, charRep_apply, charRep_apply, Pi.smul_apply, smul_eq_mul]`. Take the linear combination `(z (g, h')) * hna`.
-/
theorem exists_sol (hT : L1.T = LinearMap.range (Algebra.linearMap O LL)) {ϖ : O}
    (hu : algebraMap O LL ϖ ≠ 0) {z : G × G → LL}
    (h : ∀ a : LL, CobO PD L1 (a • z)) (s : ℕ)
    (w : G × G → ↥L1.T) (hw : ∀ x, ((w x : ↥L1.T) : LL) = algebraMap O LL ϖ ^ s * z x)
    (hTop : ∀ (r : ℕ) (z : G × G → LL), (∀ x, algebraMap O LL ϖ ^ r * z x ∈ L1.T) → CobO PD L1 z →
      ∃ f : G → LL, (∀ g, algebraMap O LL ϖ ^ r * f g ∈ L1.T) ∧
        IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : LL ⧸ L1.T)) ∧
        ∀ x, ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f x - z x ∈ L1.T) (n : ℕ) :
    ∃ c, Sol L1 ϖ w n c := by
  set u := algebraMap O LL ϖ with hudef
  set a : LL := u⁻¹ ^ n * u ^ s with ha
  have hna : u ^ n * a = u ^ s := by
    rw [ha, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hu, one_pow, one_mul]
  obtain ⟨f, hf1, hf2, hf3⟩ := hTop n (a • z) (fun x => by
    have h1 : u ^ n * (a • z) x = ((w x : ↥L1.T) : LL) := by
      rw [hw, Pi.smul_apply, smul_eq_mul, ← mul_assoc, hna]
    rw [h1]
    exact (w x).2) (h a)
  have hsm : ∀ y : ↥L1.T, ((ϖ ^ n • y : ↥L1.T) : LL) = u ^ n * (y : LL) := by
    intro y
    rw [Submodule.coe_smul, Algebra.smul_def, map_pow]
  refine ⟨fun g => Submodule.Quotient.mk (⟨u ^ n * f g, hf1 g⟩ : ↥L1.T), ?_, fun g h' => ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro g₀
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 hf2 g₀] with g hg
    have h1 : f g - f g₀ ∈ L1.T := (Submodule.Quotient.eq _).1 hg
    refine (Submodule.Quotient.eq _).2 ((mem_pw L1 ϖ).2 ⟨⟨_, h1⟩, Subtype.ext ?_⟩)
    rw [hsm]
    change u ^ n * f g - u ^ n * f g₀ = _
    ring
  · rw [actQ_mk, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
    refine (Submodule.Quotient.eq _).2 ((mem_pw L1 ϖ).2 ⟨⟨_, hf3 (g, h')⟩, Subtype.ext ?_⟩)
    rw [hsm]
    change charRep (cycLL PD LL) g (u ^ n * f h') - u ^ n * f (g * h') + u ^ n * f g - ((w (g, h') : ↥L1.T) : LL) =
      u ^ n * (charRep (cycLL PD LL) g (f h') - f (g * h') + f g - (a • z) (g, h'))
    rw [hw, charRep_apply, charRep_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (z (g, h')) * hna

/- English proof (translation)
Establish `hinj : Function.Injective (algebraMap O LL)` using `IsFractionRing.injective O LL`. Establish `hu : algebraMap O LL ϖ ≠ 0` using `fun h0 => hϖ.ne_zero (hinj (h0.trans (map_zero _).symm))`. Take `⟨s, hs⟩` from `exists_scale hϖ hop hz`. Establish `hs' : ∀ x, algebraMap O LL ϖ ^ s * z x ∈ L1.T` using `fun x => (mem_T L1 hT).2 (hs x)`. Set `w : G × G → ↥L1.T` to `fun x => ⟨_, hs' x⟩`.

Take `⟨F, hF1, hF2⟩` from `exists_limit L1 ϖ w hfin (exists_sol L1 hT hu h s w (fun _ => rfl) hTop) (exists_limit_of_cauchy_adic_filtration L1 hT hinj ϖ hc) (sep_T L1 hT hinj ϖ hc)`. Establish `hFc : Continuous fun g => ((F g : ↥L1.T) : LL)`. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`. Rewrite using `[ContinuousAt, ← tendsto_sub_nhds_zero_iff, hb.tendsto_right_iff]`.

Introduce `n _`. Use `filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hF1 n) g₀] with g hg`. Take `⟨y, hy⟩` from `(mem_pw L1 ϖ).1 ((Submodule.Quotient.eq _).1 hg)`. Take `⟨o, ho⟩` from `(mem_T L1 hT).1 y.2`. Use `⟨o, trivial, ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg Subtype.val hy`. Rewrite `h1` using `[Submodule.coe_smul, Algebra.smul_def, ← ho, ← map_mul]`. Conclude with `h1.symm`. Use `⟨fun g => (algebraMap O LL ϖ)⁻¹ ^ s * (F g : LL), continuous_const.mul hFc, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `⟨g, h'⟩`.

Establish `h1 : charRep (cycLL PD LL) g (F h' : LL) - (F (g * h') : LL) + (F g : LL) = algebraMap O LL ϖ ^ s * z (g, h')` using `congrArg Subtype.val (hF2 g h')`. Express the relevant statement in the definitionally equal form `charRep (cycLL PD LL) g ((algebraMap O LL ϖ)⁻¹ ^ s * (F h' : LL)) - (algebraMap O LL ϖ)⁻¹ ^ s * (F (g * h') : LL) + (algebraMap O LL ϖ)⁻¹ ^ s * (F g : LL) = z (g, h')`. Rewrite `h1`, the goal using `[charRep_apply]`. Establish `h2 : (algebraMap O LL ϖ)⁻¹ ^ s * algebraMap O LL ϖ ^ s = 1`. Rewrite using `[← mul_pow, inv_mul_cancel₀ hu, one_pow]`.

Take the linear combination `((algebraMap O LL ϖ)⁻¹ ^ s) * h1 + z (g, h') * h2`.
-/
theorem cobL_of_all [CompactSpace G] [IsTopologicalRing LL] [IsDomain O] [IsDiscreteValuationRing O]
    [IsFractionRing O LL] (hT : L1.T = LinearMap.range (Algebra.linearMap O LL)) {ϖ : O}
    (hϖ : Irreducible ϖ) (hop : IsOpen (Set.range (algebraMap O LL)))
    (hc : IsAdicComplete (Ideal.span {ϖ}) O)
    (hb : (nhds (0 : LL)).HasBasis (fun _ : ℕ => True)
      (fun n => (fun o : O => algebraMap O LL (ϖ ^ n * o)) '' Set.univ))
    (hfin : ∀ n, Finite ↥(quotientCocycles L1 (pw L1 ϖ n) (stable_pw L1 ϖ n)))
    (hTop : ∀ (r : ℕ) (z : G × G → LL), (∀ x, algebraMap O LL ϖ ^ r * z x ∈ L1.T) → CobO PD L1 z →
      ∃ f : G → LL, (∀ g, algebraMap O LL ϖ ^ r * f g ∈ L1.T) ∧
        IsLocallyConstant (fun g => (Submodule.Quotient.mk (f g) : LL ⧸ L1.T)) ∧
        ∀ x, ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f x - z x ∈ L1.T)
    {z : G × G → LL} (hz : Continuous z) (h : ∀ a : LL, CobO PD L1 (a • z)) : CobL PD z := by
  have hinj : Function.Injective (algebraMap O LL) := IsFractionRing.injective O LL
  have hu : algebraMap O LL ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinj (h0.trans (map_zero _).symm))
  obtain ⟨s, hs⟩ := exists_scale hϖ hop hz
  have hs' : ∀ x, algebraMap O LL ϖ ^ s * z x ∈ L1.T := fun x => (mem_T L1 hT).2 (hs x)
  let w : G × G → ↥L1.T := fun x => ⟨_, hs' x⟩
  obtain ⟨F, hF1, hF2⟩ := exists_limit L1 ϖ w hfin
    (exists_sol L1 hT hu h s w (fun _ => rfl) hTop) (exists_limit_of_cauchy_adic_filtration L1 hT hinj ϖ hc) (sep_T L1 hT hinj ϖ hc)
  have hFc : Continuous fun g => ((F g : ↥L1.T) : LL) := by
    rw [continuous_iff_continuousAt]
    intro g₀
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff, hb.tendsto_right_iff]
    intro n _
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).1 (hF1 n) g₀] with g hg
    obtain ⟨y, hy⟩ := (mem_pw L1 ϖ).1 ((Submodule.Quotient.eq _).1 hg)
    obtain ⟨o, ho⟩ := (mem_T L1 hT).1 y.2
    refine ⟨o, trivial, ?_⟩
    have h1 := congrArg Subtype.val hy
    rw [Submodule.coe_smul, Algebra.smul_def, ← ho, ← map_mul] at h1
    exact h1.symm
  refine ⟨fun g => (algebraMap O LL ϖ)⁻¹ ^ s * (F g : LL), continuous_const.mul hFc, ?_⟩
  funext ⟨g, h'⟩
  have h1 : charRep (cycLL PD LL) g (F h' : LL) - (F (g * h') : LL) + (F g : LL) =
      algebraMap O LL ϖ ^ s * z (g, h') := congrArg Subtype.val (hF2 g h')
  change charRep (cycLL PD LL) g ((algebraMap O LL ϖ)⁻¹ ^ s * (F h' : LL)) -
    (algebraMap O LL ϖ)⁻¹ ^ s * (F (g * h') : LL) + (algebraMap O LL ϖ)⁻¹ ^ s * (F g : LL) = z (g, h')
  rw [charRep_apply] at h1 ⊢
  have h2 : (algebraMap O LL ϖ)⁻¹ ^ s * algebraMap O LL ϖ ^ s = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hu, one_pow]
  linear_combination ((algebraMap O LL ϖ)⁻¹ ^ s) * h1 + z (g, h') * h2

end Cyc

/- English proof (translation)
Introduce `D l _ K hfin htop LL _ _ _ O _ _ hO L1 hL1 z hz`. Establish `hO'` using `hO`. Take `⟨⟨hdom, hdvr, hfr⟩, hfd, hmt, htr, hop⟩` from `hO'`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨hc, -, -, -, hb, -⟩` from `GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ`.

Use `haveI : CompactSpace ↥(GK K) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K`. Use `haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL`. Establish `hAlg : Continuous (algebraMap ℚ_[l] LL)` using `continuous_algebraMap ℚ_[l] LL`. Establish `hχ : Continuous fun g : ↥(GK K) => ((cycLL ((D.loc l).PD K) LL g : LLˣ) : LL)`. Establish `h1 : (fun g : ↥(GK K) => ((cycLL ((D.loc l).PD K) LL g : LLˣ) : LL)) = fun g : ↥(GK K) => algebraMap ℚ_[l] LL ((D.loc l).χQ (g : GQ l) : ℚ_[l])`.

Use function extensionality and compare the values at `g`. Rewrite using `[← (D.loc l).PD_χ K g]`. Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `hAlg.comp ((GlobalTheory.Cyc.IsCyc.continuous (D.loc l).χQ_cyc).comp continuous_subtype_val)`.

Set `A : GRep ↥(GK K) ℚ_[l] LL O` to `{ V := LL ρ := charRep (cycLL ((D.loc l).PD K) LL) cont := fun x => by`. Simplify using `only [charRep_apply]`. Conclude with `hχ.mul continuous_const }`. Establish `hopT : IsOpen (L1.T : Set LL)`. Establish `h1 : (L1.T : Set LL) = Set.range (algebraMap O LL)`.

Use extensionality with `y`. Conclude with `mem_T L1 hL1`. Rewrite using `[h1]`. Conclude with `hop`. Conclude with `⟨fun h a => cobO_of_cobL L1 hopT h a, fun h => cobL_of_all L1 hL1 hϖ hop hc hb (fun n => hfin LL O hO A L1 ϖ hϖ n (stable_pw L1 ϖ n)) (fun r z hr hz' => htop LL O hO L1 hL1 ϖ hϖ r z hr hz') hz h⟩`.
-/
theorem cobLO_of_fin_inj : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), FinZQ ((D.loc l).PD K) → TopInj ((D.loc l).PD K) → CobLO ((D.loc l).PD K) := by
  intro D l _ K hfin htop LL _ _ _ O _ _ hO L1 hL1 z hz
  have hO' := hO
  obtain ⟨⟨hdom, hdvr, hfr⟩, hfd, hmt, htr, hop⟩ := hO'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hc, -, -, -, hb, -⟩ := GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hO ϖ hϖ
  haveI : CompactSpace ↥(GK K) := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK K
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  have hAlg : Continuous (algebraMap ℚ_[l] LL) := continuous_algebraMap ℚ_[l] LL
  have hχ : Continuous fun g : ↥(GK K) => ((cycLL ((D.loc l).PD K) LL g : LLˣ) : LL) := by
    have h1 : (fun g : ↥(GK K) => ((cycLL ((D.loc l).PD K) LL g : LLˣ) : LL)) =
        fun g : ↥(GK K) => algebraMap ℚ_[l] LL ((D.loc l).χQ (g : GQ l) : ℚ_[l]) := by
      funext g
      rw [← (D.loc l).PD_χ K g]
      rfl
    rw [h1]
    exact hAlg.comp ((GlobalTheory.Cyc.IsCyc.continuous (D.loc l).χQ_cyc).comp continuous_subtype_val)
  let A : GRep ↥(GK K) ℚ_[l] LL O :=
    { V := LL
      ρ := charRep (cycLL ((D.loc l).PD K) LL)
      cont := fun x => by
        simp only [charRep_apply]
        exact hχ.mul continuous_const }
  have hopT : IsOpen (L1.T : Set LL) := by
    have h1 : (L1.T : Set LL) = Set.range (algebraMap O LL) := by
      ext y
      exact mem_T L1 hL1
    rw [h1]
    exact hop
  exact ⟨fun h a => cobO_of_cobL L1 hopT h a, fun h =>
    cobL_of_all L1 hL1 hϖ hop hc hb (fun n => hfin LL O hO A L1 ϖ hϖ n (stable_pw L1 ϖ n))
      (fun r z hr hz' => htop LL O hO L1 hL1 ϖ hϖ r z hr hz') hz h⟩

end GlobalTheory.CompanionTheory.LocDual.CobDetect
