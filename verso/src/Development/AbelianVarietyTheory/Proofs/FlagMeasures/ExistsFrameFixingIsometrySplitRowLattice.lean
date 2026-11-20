import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LoopC.RowSplit

section Lattices

variable {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Set `q : V →ₗ[𝓞 K] V ⧸ W` to `W.mkQ.restrictScalars (𝓞 K)`. Set `Lb : Submodule (𝓞 K) (V ⧸ W)` to `L.map q`. Establish `hfin : Module.Finite (𝓞 K) Lb` using `Module.Finite.iff_fg.2 (hfg.map q)`. Establish `hcancel : ∀ (d : 𝓞 K) (x : V ⧸ W), d ≠ 0 → d • x = 0 → x = 0`. Introduce `d x hd h`.

Rewrite `h` using `[← IsScalarTower.algebraMap_smul K d x]`. Conclude with `(smul_eq_zero.1 h).resolve_left (by simpa using hd)`. Establish `hflat : Module.Flat (𝓞 K) Lb`. Rewrite using `[IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]`. Introduce and unpack `x ⟨d, hd⟩`.

Establish `: (d : 𝓞 K) • (x : V ⧸ W) = 0` using `congrArg Subtype.val hd`. Conclude with `Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)`. Establish `hfp : Module.FinitePresentation (𝓞 K) Lb` using `Module.finitePresentation_of_finite _ _`. Establish `hproj : Module.Projective (𝓞 K) Lb` using `Module.Flat.projective_of_finitePresentation`. Set `qL : L →ₗ[𝓞 K] Lb` to `q.submoduleMap L`.

Take `⟨s, hs⟩` from `Module.projective_lifting_property qL LinearMap.id (LinearMap.submoduleMap_surjective q L)`. Establish `hs' : ∀ y : Lb, q (s y : V) = y` using `fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)`. Set `p0 : L →ₗ[𝓞 K] V` to `L.subtype - L.subtype ∘ₗ s ∘ₗ qL`. Establish `hp0 : ∀ x : L, p0 x = (x : V) - s (qL x)` using `fun x => rfl`. Establish `hden : ∀ v : V, ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L`.

Introduce `v`. Establish `hv : v ∈ Submodule.span K (L : Set V)` using `by rw [hsp]; trivial`. Take `⟨d, hd⟩` from `multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (L : Set V) v hv`. Rewrite `hd` using `[Submodule.span_eq]`. Conclude with `⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩`.

Establish `hunit : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) V) x)` using `(isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K).map_units`. Use `haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by`. Use `⟨hunit, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩` and prove the remaining obligations. Take `⟨d, hd, hv⟩` from `hden v`. Conclude with `⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩`.

Set `P0 : V →ₗ[𝓞 K] V` to `IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) L.subtype p0 hunit`. Establish `hP0 : ∀ x : L, P0 (x : V) = p0 x` using `fun x => IsLocalizedModule.lift_apply _ L.subtype p0 hunit x`. Set `P : V →ₗ[K] V` to `P0.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K`. Establish `hP : ∀ v, P v = P0 v` using `fun v => rfl`. Establish `hW : ∀ x : L, p0 x ∈ W`.

Introduce `x`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Express the relevant statement in the definitionally equal form `q (p0 x) = 0`. Rewrite using `[hp0, map_sub, hs']`. Conclude with `sub_self _`.

Use `⟨P, fun v => ?_, fun w hw => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨d, hd, hv⟩` from `hden v`. Rewrite using `[← Submodule.Quotient.mk_eq_zero]`. Apply `hcancel d _ hd` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `d • q (P0 v) = 0`.

Rewrite using `[← map_smul, ← map_smul, show d • v = ((⟨d • v, hv⟩ : L) : V) from rfl, hP0]`. Conclude with `(Submodule.Quotient.mk_eq_zero W).2 (hW _)`. Take `⟨d, hd, hv⟩` from `hden w`. Establish `h0 : qL ⟨d • w, hv⟩ = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `q (d • w) = 0`. Rewrite using `[map_smul]`. Express the relevant statement in the definitionally equal form `d • (Submodule.Quotient.mk w : V ⧸ W) = 0`. Rewrite using `[(Submodule.Quotient.mk_eq_zero W).2 hw, smul_zero]`. Establish `h1 : d • P0 w = d • w`.

Rewrite using `[← map_smul, show d • w = ((⟨d • w, hv⟩ : L) : V) from rfl, hP0, hp0, h0, map_zero]`. Simplify using the standard rewrite rules. Rewrite using `[hP]`. Rewrite `h1` using `[← IsScalarTower.algebraMap_smul K d, ← IsScalarTower.algebraMap_smul K d w]`. Conclude with `smul_right_injective V (by simpa using hd) h1`.

Rewrite using `[hP, show v = ((⟨v, hv⟩ : L) : V) from rfl, hP0, hp0]`. Conclude with `L.sub_mem hv (s _).2`.
-/
theorem exists_proj (L : Submodule (𝓞 K) V) (hfg : L.FG) (hsp : Submodule.span K (L : Set V) = ⊤) (W : Submodule K V) :
    ∃ P : V →ₗ[K] V, (∀ v, P v ∈ W) ∧ (∀ w ∈ W, P w = w) ∧ ∀ v ∈ L, P v ∈ L := by
  classical
  let q : V →ₗ[𝓞 K] V ⧸ W := W.mkQ.restrictScalars (𝓞 K)
  let Lb : Submodule (𝓞 K) (V ⧸ W) := L.map q
  have hfin : Module.Finite (𝓞 K) Lb := Module.Finite.iff_fg.2 (hfg.map q)
  have hcancel : ∀ (d : 𝓞 K) (x : V ⧸ W), d ≠ 0 → d • x = 0 → x = 0 := by
    intro d x hd h
    rw [← IsScalarTower.algebraMap_smul K d x] at h
    exact (smul_eq_zero.1 h).resolve_left (by simpa using hd)
  have hflat : Module.Flat (𝓞 K) Lb := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
    rintro x ⟨d, hd⟩
    have : (d : 𝓞 K) • (x : V ⧸ W) = 0 := congrArg Subtype.val hd
    exact Subtype.ext (hcancel d x (nonZeroDivisors.coe_ne_zero d) this)
  have hfp : Module.FinitePresentation (𝓞 K) Lb := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 K) Lb := Module.Flat.projective_of_finitePresentation
  let qL : L →ₗ[𝓞 K] Lb := q.submoduleMap L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property qL LinearMap.id (LinearMap.submoduleMap_surjective q L)
  have hs' : ∀ y : Lb, q (s y : V) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let p0 : L →ₗ[𝓞 K] V := L.subtype - L.subtype ∘ₗ s ∘ₗ qL
  have hp0 : ∀ x : L, p0 x = (x : V) - s (qL x) := fun x => rfl
  have hden : ∀ v : V, ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ L := by
    intro v
    have hv : v ∈ Submodule.span K (L : Set V) := by rw [hsp]; trivial
    obtain ⟨d, hd⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K (L : Set V) v hv
    rw [Submodule.span_eq] at hd
    exact ⟨d, nonZeroDivisors.coe_ne_zero d, hd⟩
  have hunit : ∀ x : nonZeroDivisors (𝓞 K), IsUnit (algebraMap (𝓞 K) (Module.End (𝓞 K) V) x) :=
    (isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K).map_units
  haveI hloc : IsLocalizedModule (nonZeroDivisors (𝓞 K)) L.subtype := by
    refine ⟨hunit, fun v => ?_, fun {x y} h => ⟨1, by simpa using Subtype.ext h⟩⟩
    obtain ⟨d, hd, hv⟩ := hden v
    exact ⟨(⟨d • v, hv⟩, ⟨d, mem_nonZeroDivisors_of_ne_zero hd⟩), rfl⟩
  let P0 : V →ₗ[𝓞 K] V := IsLocalizedModule.lift (nonZeroDivisors (𝓞 K)) L.subtype p0 hunit
  have hP0 : ∀ x : L, P0 (x : V) = p0 x := fun x => IsLocalizedModule.lift_apply _ L.subtype p0 hunit x
  let P : V →ₗ[K] V := P0.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 K)) K
  have hP : ∀ v, P v = P0 v := fun v => rfl
  have hW : ∀ x : L, p0 x ∈ W := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    change q (p0 x) = 0
    rw [hp0, map_sub, hs']
    exact sub_self _
  refine ⟨P, fun v => ?_, fun w hw => ?_, fun v hv => ?_⟩
  · obtain ⟨d, hd, hv⟩ := hden v
    rw [← Submodule.Quotient.mk_eq_zero]
    apply hcancel d _ hd
    change d • q (P0 v) = 0
    rw [← map_smul, ← map_smul, show d • v = ((⟨d • v, hv⟩ : L) : V) from rfl, hP0]
    exact (Submodule.Quotient.mk_eq_zero W).2 (hW _)
  · obtain ⟨d, hd, hv⟩ := hden w
    have h0 : qL ⟨d • w, hv⟩ = 0 := by
      apply Subtype.ext
      change q (d • w) = 0
      rw [map_smul]
      change d • (Submodule.Quotient.mk w : V ⧸ W) = 0
      rw [(Submodule.Quotient.mk_eq_zero W).2 hw, smul_zero]
    have h1 : d • P0 w = d • w := by
      rw [← map_smul, show d • w = ((⟨d • w, hv⟩ : L) : V) from rfl, hP0, hp0, h0, map_zero]
      simp
    rw [hP]
    rw [← IsScalarTower.algebraMap_smul K d, ← IsScalarTower.algebraMap_smul K d w] at h1
    exact smul_right_injective V (by simpa using hd) h1
  · rw [hP, show v = ((⟨v, hv⟩ : L) : V) from rfl, hP0, hp0]
    exact L.sub_mem hv (s _).2

end Lattices

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ}

/- English proof (translation)
The claim follows from `S.herm.eq x y`.
-/
theorem hsym (x y : S.V) : star (S.hT x y) = S.hT y x := S.herm.eq x y

/- English proof (translation)
Simplify using `[starRingEnd_apply]`.
-/
theorem hsmul (c : E) (x y : S.V) : S.hT (c • x) y = star c * S.hT x y := by
  simp [starRingEnd_apply]

/- English proof (translation)
Simplify using `[orth, Submodule.mem_iInf]`.
-/
theorem mem_orth {U : Submodule E S.V} {x : S.V} : x ∈ orth S U ↔ ∀ y ∈ U, S.hT y x = 0 := by
  simp [orth, Submodule.mem_iInf]

/- English proof (translation)
Rewrite using `[mem_orth]`. Use `⟨fun h y hy => h y (Submodule.subset_span hy), fun h y hy => ?_⟩` and prove the remaining obligations. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact h x hx`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul c x _ hx => rw [hsmul, hx, mul_zero]`.
-/
theorem mem_orth_span {s : Set S.V} {x : S.V} :
    x ∈ orth S (Submodule.span E s) ↔ ∀ y ∈ s, S.hT y x = 0 := by
  rw [mem_orth]
  refine ⟨fun h y hy => h y (Submodule.subset_span hy), fun h y hy => ?_⟩
  induction hy using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => rw [hsmul, hx, mul_zero]

/- English proof (translation)
Establish `h1 : (LinearMap.range S.hT).dualCoannihilator = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Rewrite `hx` using `[Submodule.mem_dualCoannihilator]`. Conclude with `S.nondeg.2 x fun y => hx _ ⟨y, rfl⟩`.

Establish `h2` using `Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range S.hT)`. Rewrite `h2` using `[h1, Submodule.dualAnnihilator_bot]`. Establish `h3 : φ ∈ LinearMap.range S.hT` using `h2 ▸ Submodule.mem_top`. Take `⟨y, hy⟩` from `h3`. Conclude with `⟨y, fun x => by rw [← hy]⟩`.
-/
theorem exists_rep (φ : S.V →ₗ[E] E) : ∃ y, ∀ x, S.hT y x = φ x := by
  have h1 : (LinearMap.range S.hT).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_dualCoannihilator] at hx
    exact S.nondeg.2 x fun y => hx _ ⟨y, rfl⟩
  have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range S.hT)
  rw [h1, Submodule.dualAnnihilator_bot] at h2
  have h3 : φ ∈ LinearMap.range S.hT := h2 ▸ Submodule.mem_top
  obtain ⟨y, hy⟩ := h3
  exact ⟨y, fun x => by rw [← hy]⟩

abbrev FI (E : Type) [Field E] [NumberField E] : Type := FractionalIdeal (nonZeroDivisors (𝓞 E)) E

omit [StarRing E] in
/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.isIntegral_coe`. Introduce `h`.

Conclude with `⟨⟨x, h⟩, rfl⟩`.
-/
theorem mem_one_iff (x : E) : x ∈ (1 : FI E) ↔ IsIntegral ℤ x := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.isIntegral_coe
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

/- English proof (translation)
The claim follows from `map_isIntegral_int (starRingEnd E) h`.
-/
theorem star_int {x : E} (h : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  map_isIntegral_int (starRingEnd E) h

/- English proof (translation)
Use `conv_lhs => rw [← hu]`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one]`. Use `forall_congr' fun y => forall_congr' fun hy => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨o, ho⟩`.

Establish `ho' : (o : E) = S.hT y x` using `ho`. Rewrite using `[← ho']`. Conclude with `o.isIntegral_coe`. Introduce `h`. Conclude with `⟨⟨_, h⟩, rfl⟩`.
-/
theorem mem_unimod {Λ : Submodule (𝓞 E) S.V} (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (x : S.V) :
    x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (S.hT y x) := by
  conv_lhs => rw [← hu]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one]
  refine forall_congr' fun y => forall_congr' fun hy => ?_
  constructor
  · rintro ⟨o, ho⟩
    have ho' : (o : E) = S.hT y x := ho
    rw [← ho']
    exact o.isIntegral_coe
  · intro h
    exact ⟨⟨_, h⟩, rfl⟩

def StarStable (I : FI E) : Prop := ∀ x ∈ I, star x ∈ I

/- English proof (translation)
Introduce `x hx` and use `(mem_one_iff _).2 (star_int ((mem_one_iff _).1 hx))`.
-/
theorem starStable_one : StarStable (1 : FI E) := fun x hx =>
  (mem_one_iff _).2 (star_int ((mem_one_iff _).1 hx))

/- English proof (translation)
Introduce `x hx`. Use `FractionalIdeal.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[star_mul']`. Conclude with `FractionalIdeal.mul_mem_mul (hI a ha) (hJ b hb)`. Rewrite using `[star_add]`.

Conclude with `Submodule.add_mem (I * J : FI E).1 ha hb`.
-/
theorem StarStable.mul {I J : FI E} (hI : StarStable I) (hJ : StarStable J) : StarStable (I * J) := by
  intro x hx
  refine FractionalIdeal.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · rw [star_mul']
    exact FractionalIdeal.mul_mem_mul (hI a ha) (hJ b hb)
  · rw [star_add]
    exact Submodule.add_mem (I * J : FI E).1 ha hb

omit [StarRing E] in
/- English proof (translation)
Rewrite using `[FractionalIdeal.mem_inv_iff h0]`. Simplify using `only [mem_one_iff]`.
-/
theorem mem_inv {I : FI E} (h0 : I ≠ 0) (x : E) : x ∈ I⁻¹ ↔ ∀ y ∈ I, IsIntegral ℤ (x * y) := by
  rw [FractionalIdeal.mem_inv_iff h0]
  simp only [mem_one_iff]

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[mem_inv h0]`. Introduce `y hy`. Use `star_int (hx _ (hI y hy))` as an intermediate fact. Rewrite `this` using `[star_mul, star_star, mul_comm]`. Then use the resulting hypothesis.
-/
theorem StarStable.inv {I : FI E} (hI : StarStable I) (h0 : I ≠ 0) : StarStable I⁻¹ := by
  intro x hx
  rw [mem_inv h0] at hx ⊢
  intro y hy
  have := star_int (hx _ (hI y hy))
  rwa [star_mul, star_star, mul_comm] at this

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `starStable_one`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul hI`.
-/
theorem StarStable.pow {I : FI E} (hI : StarStable I) (n : ℕ) : StarStable (I ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact starStable_one
  | succ n ih => rw [pow_succ]; exact ih.mul hI

/- English proof (translation)
Consider the cases of `n with`. Consider the case `ofNat n => simpa using hI.pow n`. Consider the case `negSucc n => rw [zpow_negSucc]`. Conclude with `(hI.pow _).inv (pow_ne_zero _ h0)`.
-/
theorem StarStable.zpow {I : FI E} (hI : StarStable I) (h0 : I ≠ 0) (n : ℤ) : StarStable (I ^ n) := by
  cases n with
  | ofNat n => simpa using hI.pow n
  | negSucc n => rw [zpow_negSucc]; exact (hI.pow _).inv (pow_ne_zero _ h0)

def idSpan (I : Fin r → FI E) (v : Fin r → S.V) : Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ I a ∧ y = x • v a}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, x, hx, rfl⟩`.
-/
theorem smul_mem_idSpan {I : Fin r → FI E} (v : Fin r → S.V) {a : Fin r} {x : E} (hx : x ∈ I a) :
    x • v a ∈ idSpan I v := Submodule.subset_span ⟨a, x, hx, rfl⟩

/- English proof (translation)
The claim follows from `(IsScalarTower.algebraMap_smul E o x).symm`.
-/
theorem osmul (o : 𝓞 E) (x : S.V) : o • x = (o : E) • x := (IsScalarTower.algebraMap_smul E o x).symm

def IsHyp (e f : Fin r → S.V) : Prop :=
  (∀ a b, S.hT (e a) (e b) = 0) ∧ (∀ a b, S.hT (f a) (f b) = 0) ∧
    ∀ a b, S.hT (e a) (f b) = if a = b then 1 else 0

/- English proof (translation)
Rewrite using `[← hsym, h.2.2]`. Distinguish the cases in `hab : a = b`. Simplify using `[hab]`. Simplify using `[hab, Ne.symm hab]`.
-/
theorem IsHyp.fe {e f : Fin r → S.V} (h : IsHyp e f) (a b : Fin r) :
    S.hT (f a) (e b) = if a = b then 1 else 0 := by
  rw [← hsym, h.2.2]
  by_cases hab : a = b
  · simp [hab]
  · simp [hab, Ne.symm hab]

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨b, c, hc, rfl⟩` from `hx`. Rewrite using `[map_smul, h.fe]`. Use `split_ifs with hab`.

Substitute `hab` using the available equality. Rewrite using `[smul_eq_mul, mul_one, mul_comm]`. Conclude with `(mem_inv (h0 a) c).1 hc β hβ`. Simplify using `using isIntegral_zero`. Consider the case `zero => simpa using isIntegral_zero`.

Consider the case `add x y _ _ hx hy => rw [map_add, mul_add]`. Conclude with `hx.add hy`. Consider the case `smul c x _ hx`. Rewrite using `[osmul, map_smul, smul_eq_mul, mul_left_comm]`. Conclude with `c.isIntegral_coe.mul hx`.
-/
theorem pair_idSpan {e f : Fin r → S.V} (h : IsHyp e f) {B : Fin r → FI E} (h0 : ∀ a, B a ≠ 0)
    {x : S.V} (hx : x ∈ idSpan (fun a => (B a)⁻¹) e) (a : Fin r) {β : E} (hβ : β ∈ B a) :
    IsIntegral ℤ (β * S.hT (f a) x) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, c, hc, rfl⟩ := hx
    rw [map_smul, h.fe]
    split_ifs with hab
    · subst hab
      rw [smul_eq_mul, mul_one, mul_comm]
      exact (mem_inv (h0 a) c).1 hc β hβ
    · simpa using isIntegral_zero
  | zero => simpa using isIntegral_zero
  | add x y _ _ hx hy => rw [map_add, mul_add]; exact hx.add hy
  | smul c x _ hx =>
    rw [osmul, map_smul, smul_eq_mul, mul_left_comm]
    exact c.isIntegral_coe.mul hx

/- English proof (translation)
Take `⟨t, ht⟩` from `GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram E hE`. Take `⟨P, hPU, hPid, hPL⟩` from `exists_proj Λ hl.fg hl.span_eq_top (Submodule.span E (Set.range e) ⊔ Submodule.span E {z})`. Use `choose g hg using fun a => exists_rep (S := S) (S.hT (f a) ∘ₗ P)`. Establish `hge : ∀ a b, S.hT (g a) (e b) = if a = b then 1 else 0`. Introduce `a b`.

Rewrite using `[hg, LinearMap.comp_apply, hPid _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩)), h.fe]`. Establish `heg : ∀ a b, S.hT (e a) (g b) = if a = b then 1 else 0`. Introduce `a b`. Rewrite using `[← hsym, hge]`. Distinguish the cases in `hab : a = b`.

Simplify using `[hab]`. Simplify using `[hab, Ne.symm hab]`. Establish `hgz : ∀ a, S.hT (g a) z = 0`. Introduce `a`. Rewrite using `[hg, LinearMap.comp_apply, hPid _ (Submodule.mem_sup_right (Submodule.subset_span rfl)), hfz]`.

Establish `hgL : ∀ a, ∀ β ∈ B a, β • g a ∈ Λ`. Introduce `a β hβ`. Rewrite using `[mem_unimod hu]`. Introduce `y hy`. Rewrite using `[← hsym, hsmul, hg, LinearMap.comp_apply]`.

Apply `star_int` to reduce the goal to its premises. Take `⟨x, hx, w, hw, hxw⟩` from `Submodule.mem_sup.1 (hPU y)`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hw`. Establish `hm : x + c • z ∈ Λ` using `hxw ▸ hPL y hy`. Take `⟨o, rfl⟩` from `hprim c x hx hm`.

Establish `hxL : x ∈ Λ`. Use `Λ.sub_mem hm (Λ.smul_mem o hz)` as an intermediate fact. Rewrite `this` using `[osmul, add_sub_cancel_right]`. Then use the resulting hypothesis. Rewrite using `[← hxw, map_add, map_smul, hfz, smul_zero, add_zero]`. Conclude with `pair_idSpan h h0 (hX ▸ ⟨hxL, hx⟩) a (hB a β hβ)`.

Use `⟨fun b => g b - ∑ a, ((t : E) * S.hT (g a) (g b)) • e a, ⟨h.1, fun a b => ?_, fun a b => ?_⟩, fun a => ?_, fun b β hβ => ?_⟩` and prove the remaining obligations. Simplify using `only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hsmul, map_smul, h.1, hge, heg, smul_eq_mul, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, star_mul, hsym]`. Take the linear combination `(-(S.hT (g a) (g b))) * ht`. Simplify using `only [map_sub, map_sum, map_smul, h.1, heg, smul_eq_mul, mul_zero, Finset.sum_const_zero, sub_zero]`. Simplify using `only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hsmul, hez, hgz, mul_zero, Finset.sum_const_zero, sub_zero]`.

Rewrite using `[smul_sub, Finset.smul_sum]`. Use `Λ.sub_mem (hgL b β hβ) (Λ.sum_mem fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul]`. Establish `: (β * ((t : E) * S.hT (g a) (g b))) • e a ∈ idSpan (fun a => (B a)⁻¹) e`. Apply `smul_mem_idSpan` to reduce the goal to its premises.

Rewrite using `[mem_inv (h0 a)]`. Introduce `y hy`. Establish `h1` using `(mem_unimod hu _).1 (hgL b β hβ) _ (hgL a _ (hB a y hy))`. Rewrite `h1` using `[hsmul, star_star, map_smul, smul_eq_mul]`. Establish `h2` using `t.isIntegral_coe.mul h1`.

Establish `e1 : β * ((t : E) * S.hT (g a) (g b)) * y = (t : E) * (y * (β * S.hT (g a) (g b)))` using `by ring`. Rewrite using `[e1]`. Conclude with `h2`. Rewrite `this` using `[← hX]`. Conclude with `this.1`.
-/
theorem exists_dual_frame (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) {e f : Fin r → S.V} (h : IsHyp e f) {z : S.V}
    (hez : ∀ a, S.hT (e a) z = 0) (hfz : ∀ a, S.hT (f a) z = 0)
    {B : Fin r → FI E} (h0 : ∀ a, B a ≠ 0) (hB : ∀ a, StarStable (B a))
    {Λ : Submodule (𝓞 E) S.V} (hl : Submodule.IsLattice E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hz : z ∈ Λ)
    (hX : Λ ⊓ toO S (Submodule.span E (Set.range e)) = idSpan (fun a => (B a)⁻¹) e)
    (hprim : ∀ (c : E), ∀ x ∈ Submodule.span E (Set.range e), x + c • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ f' : Fin r → S.V, IsHyp e f' ∧ (∀ a, S.hT (f' a) z = 0) ∧ ∀ a, ∀ β ∈ B a, β • f' a ∈ Λ := by
  obtain ⟨t, ht⟩ := GlobalTheory.exists_integer_add_star_eq_one_of_isCMUnram E hE
  obtain ⟨P, hPU, hPid, hPL⟩ := exists_proj Λ hl.fg hl.span_eq_top
    (Submodule.span E (Set.range e) ⊔ Submodule.span E {z})
  choose g hg using fun a => exists_rep (S := S) (S.hT (f a) ∘ₗ P)
  have hge : ∀ a b, S.hT (g a) (e b) = if a = b then 1 else 0 := by
    intro a b
    rw [hg, LinearMap.comp_apply, hPid _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩)), h.fe]
  have heg : ∀ a b, S.hT (e a) (g b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hsym, hge]
    by_cases hab : a = b
    · simp [hab]
    · simp [hab, Ne.symm hab]
  have hgz : ∀ a, S.hT (g a) z = 0 := by
    intro a
    rw [hg, LinearMap.comp_apply, hPid _ (Submodule.mem_sup_right (Submodule.subset_span rfl)), hfz]
  have hgL : ∀ a, ∀ β ∈ B a, β • g a ∈ Λ := by
    intro a β hβ
    rw [mem_unimod hu]
    intro y hy
    rw [← hsym, hsmul, hg, LinearMap.comp_apply]
    apply star_int
    obtain ⟨x, hx, w, hw, hxw⟩ := Submodule.mem_sup.1 (hPU y)
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    have hm : x + c • z ∈ Λ := hxw ▸ hPL y hy
    obtain ⟨o, rfl⟩ := hprim c x hx hm
    have hxL : x ∈ Λ := by
      have := Λ.sub_mem hm (Λ.smul_mem o hz)
      rwa [osmul, add_sub_cancel_right] at this
    rw [← hxw, map_add, map_smul, hfz, smul_zero, add_zero]
    exact pair_idSpan h h0 (hX ▸ ⟨hxL, hx⟩) a (hB a β hβ)
  refine ⟨fun b => g b - ∑ a, ((t : E) * S.hT (g a) (g b)) • e a, ⟨h.1, fun a b => ?_, fun a b => ?_⟩,
    fun a => ?_, fun b β hβ => ?_⟩
  · simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hsmul, map_smul, h.1, hge, heg,
      smul_eq_mul, mul_zero, Finset.sum_const_zero, sub_zero, mul_ite, mul_one, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, star_mul, hsym]
    linear_combination (-(S.hT (g a) (g b))) * ht
  · simp only [map_sub, map_sum, map_smul, h.1, heg, smul_eq_mul, mul_zero, Finset.sum_const_zero, sub_zero]
  · simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hsmul, hez, hgz, mul_zero,
      Finset.sum_const_zero, sub_zero]
  · rw [smul_sub, Finset.smul_sum]
    refine Λ.sub_mem (hgL b β hβ) (Λ.sum_mem fun a _ => ?_)
    rw [smul_smul]
    have : (β * ((t : E) * S.hT (g a) (g b))) • e a ∈ idSpan (fun a => (B a)⁻¹) e := by
      apply smul_mem_idSpan
      rw [mem_inv (h0 a)]
      intro y hy
      have h1 := (mem_unimod hu _).1 (hgL b β hβ) _ (hgL a _ (hB a y hy))
      rw [hsmul, star_star, map_smul, smul_eq_mul] at h1
      have h2 := t.isIntegral_coe.mul h1
      have e1 : β * ((t : E) * S.hT (g a) (g b)) * y = (t : E) * (y * (β * S.hT (g a) (g b))) := by ring
      rw [e1]
      exact h2
    rw [← hX] at this
    exact this.1

def prj (e f : Fin r → S.V) : S.V →ₗ[E] S.V :=
  LinearMap.id - ∑ a, (S.hT (f a)).smulRight (e a) - ∑ a, (S.hT (e a)).smulRight (f a)

/- English proof (translation)
Simplify using `[prj, LinearMap.sum_apply]`.
-/
theorem prj_apply (e f : Fin r → S.V) (v : S.V) :
    prj e f v = v - ∑ a, S.hT (f a) v • e a - ∑ a, S.hT (e a) v • f a := by
  simp [prj, LinearMap.sum_apply]

/- English proof (translation)
Simplify using `[prj_apply, map_sum, h.1, h.2.2]`.
-/
theorem e_prj {e f : Fin r → S.V} (h : IsHyp e f) (a : Fin r) (v : S.V) : S.hT (e a) (prj e f v) = 0 := by
  simp [prj_apply, map_sum, h.1, h.2.2]

/- English proof (translation)
Simplify using `[prj_apply, map_sum, h.2.1, h.fe]`.
-/
theorem f_prj {e f : Fin r → S.V} (h : IsHyp e f) (a : Fin r) (v : S.V) : S.hT (f a) (prj e f v) = 0 := by
  simp [prj_apply, map_sum, h.2.1, h.fe]

/- English proof (translation)
Establish `h1 : S.hT (prj e f u) (prj e f v) = S.hT u (prj e f v)`. Rewrite using `[prj_apply e f u]`. Simplify using `only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hsmul, e_prj h, f_prj h, mul_zero, Finset.sum_const_zero, sub_zero]`. Rewrite using `[h1, prj_apply]`. Simplify using `only [map_sub, map_sum, map_smul, smul_eq_mul, hsym]`.
-/
theorem prj_prj {e f : Fin r → S.V} (h : IsHyp e f) (u v : S.V) :
    S.hT (prj e f u) (prj e f v) = S.hT u v - ∑ a, S.hT (f a) v * star (S.hT (e a) u) -
      ∑ a, S.hT (e a) v * star (S.hT (f a) u) := by
  have h1 : S.hT (prj e f u) (prj e f v) = S.hT u (prj e f v) := by
    rw [prj_apply e f u]
    simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, hsmul, e_prj h, f_prj h, mul_zero,
      Finset.sum_const_zero, sub_zero]
  rw [h1, prj_apply]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul, hsym]

def chg (e f f' : Fin r → S.V) : S.V →ₗ[E] S.V :=
  ∑ a, (S.hT (f' a)).smulRight (e a) + prj e f ∘ₗ prj e f' + ∑ a, (S.hT (e a)).smulRight (f a)

/- English proof (translation)
Simplify using `[chg, LinearMap.sum_apply]`.
-/
theorem chg_apply (e f f' : Fin r → S.V) (v : S.V) :
    chg e f f' v = ∑ a, S.hT (f' a) v • e a + prj e f (prj e f' v) + ∑ a, S.hT (e a) v • f a := by
  simp [chg, LinearMap.sum_apply]

/- English proof (translation)
Establish `h1 : ∀ a v, S.hT (e a) (chg e f f' v) = S.hT (e a) v`. Introduce `a v`. Simplify using `[chg_apply, map_sum, h.1, h.2.2, e_prj h]`. Establish `h2 : ∀ a v, S.hT (f a) (chg e f f' v) = S.hT (f' a) v`. Introduce `a v`.

Simplify using `[chg_apply, map_sum, h.2.1, h.fe, f_prj h]`. Establish `h3 : ∀ v, prj e f (chg e f f' v) = prj e f (prj e f' v)`. Introduce `v`. Rewrite using `[prj_apply e f (chg e f f' v)]`. Simplify using `only [h1, h2]`.

Rewrite using `[chg_apply]`. Normalize the expressions using the abelian group laws. Establish `h4` using `prj_prj h (chg e f f' u) (chg e f f' v)`. Establish `h5` using `prj_prj h (prj e f' u) (prj e f' v)`. Establish `h6` using `prj_prj h' u v`.

Simplify using `only [h1, h2, h3] at h4`. Simplify using `only [e_prj h', star_zero, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero] at h5`. Take the linear combination `h5 + h6 - h4`.
-/
theorem chg_isom {e f f' : Fin r → S.V} (h : IsHyp e f) (h' : IsHyp e f') (u v : S.V) :
    S.hT (chg e f f' u) (chg e f f' v) = S.hT u v := by
  have h1 : ∀ a v, S.hT (e a) (chg e f f' v) = S.hT (e a) v := by
    intro a v
    simp [chg_apply, map_sum, h.1, h.2.2, e_prj h]
  have h2 : ∀ a v, S.hT (f a) (chg e f f' v) = S.hT (f' a) v := by
    intro a v
    simp [chg_apply, map_sum, h.2.1, h.fe, f_prj h]
  have h3 : ∀ v, prj e f (chg e f f' v) = prj e f (prj e f' v) := by
    intro v
    rw [prj_apply e f (chg e f f' v)]
    simp only [h1, h2]
    rw [chg_apply]
    abel
  have h4 := prj_prj h (chg e f f' u) (chg e f f' v)
  have h5 := prj_prj h (prj e f' u) (prj e f' v)
  have h6 := prj_prj h' u v
  simp only [h1, h2, h3] at h4
  simp only [e_prj h', star_zero, mul_zero, zero_mul, Finset.sum_const_zero, sub_zero] at h5
  linear_combination h5 + h6 - h4

/- English proof (translation)
Rewrite using `[chg_apply, prj_apply e f]`. Simplify using `only [e_prj h', hx, zero_smul, Finset.sum_const_zero, sub_zero, add_zero]`. Rewrite using `[prj_apply e f' x]`. Simplify using `only [hx, zero_smul, Finset.sum_const_zero, sub_zero]`. Normalize the expressions using the abelian group laws.
-/
theorem chg_of_orth {e f f' : Fin r → S.V} (h' : IsHyp e f') {x : S.V} (hx : ∀ a, S.hT (e a) x = 0) :
    chg e f f' x = x - ∑ a, S.hT (f a) (prj e f' x) • e a := by
  rw [chg_apply, prj_apply e f]
  simp only [e_prj h', hx, zero_smul, Finset.sum_const_zero, sub_zero, add_zero]
  rw [prj_apply e f' x]
  simp only [hx, zero_smul, Finset.sum_const_zero, sub_zero]
  abel

/- English proof (translation)
Establish `hi : Function.Injective (chg e f f')`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Use `S.nondeg.2 x fun y => ?_` and prove the remaining obligations. Rewrite using `[← chg_isom h h', hx, map_zero]`.

Conclude with `⟨LinearEquiv.ofInjectiveEndo _ hi, fun x y => chg_isom h h' x y, fun v => rfl⟩`.
-/
theorem exists_chg {e f f' : Fin r → S.V} (h : IsHyp e f) (h' : IsHyp e f') :
    ∃ n : S.V ≃ₗ[E] S.V, n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ ∀ v, n v = chg e f f' v := by
  have hi : Function.Injective (chg e f f') := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    refine S.nondeg.2 x fun y => ?_
    rw [← chg_isom h h', hx, map_zero]
  exact ⟨LinearEquiv.ofInjectiveEndo _ hi, fun x y => chg_isom h h' x y, fun v => rfl⟩

/- English proof (translation)
Take `⟨f', h', hf'z, hf'L⟩` from `exists_dual_frame hE h hez hfz h0 hB hl hu hz hX hprim`. Take `⟨n, hn, hnv⟩` from `exists_chg h h'`. Establish `hne : ∀ a, n (e a) = e a`. Introduce `a`. Establish `: prj e f' (e a) = 0` using `by simp [prj_apply, h.1, h'.fe]`.

Rewrite using `[hnv, chg_of_orth h' (fun b => h.1 b a), this]`. Simplify using the standard rewrite rules. Establish `hnf : ∀ a, n (f' a) = f a`. Introduce `a`. Establish `: prj e f' (f' a) = 0` using `by simp [prj_apply, h'.2.1, h'.2.2]`.

Rewrite using `[hnv, chg_apply, this]`. Simplify using `[h'.2.1, h'.2.2]`. Establish `heL : ∀ a, ∀ x ∈ (B a)⁻¹, x • e a ∈ Λ`. Introduce `a x hx`. Use `smul_mem_idSpan (I := fun a => (B a)⁻¹) e hx` as an intermediate fact.

Rewrite `this` using `[← hX]`. Conclude with `this.1`. Use `⟨n, hn, hne, ?_, fun x hx => ?_, le_antisymm ?_ (sup_le (sup_le ?_ inf_le_left) ?_)⟩` and prove the remaining obligations. Establish `: prj e f' z = z` using `by simp [prj_apply, hez, hf'z]`. Rewrite using `[hnv, chg_of_orth h' hez, this]`.

Simplify using `[hfz]`. Rewrite using `[hnv, chg_of_orth h' (fun a => mem_orth_span.1 hx _ ⟨a, rfl⟩), sub_sub_cancel_left]`. Conclude with `Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))`. Introduce and unpack `_ ⟨v, hv, rfl⟩`. Establish `h1 : ∀ a, S.hT (f' a) v ∈ (B a)⁻¹`.

Introduce `a`. Rewrite using `[mem_inv (h0 a)]`. Introduce `y hy`. Use `(mem_unimod hu v).1 hv _ (hf'L a _ (hB a y hy))` as an intermediate fact. Rewrite `this` using `[hsmul, star_star, mul_comm]`. Then use the resulting hypothesis.

Establish `h2 : ∀ a, S.hT (e a) v ∈ B a`. Introduce `a`. Rewrite using `[← inv_inv (B a), mem_inv (inv_ne_zero (h0 a))]`. Introduce `y hy`. Use `(mem_unimod hu v).1 hv _ (heL a _ ((hB a).inv (h0 a) y hy))` as an intermediate fact.

Rewrite `this` using `[hsmul, star_star, mul_comm]`. Then use the resulting hypothesis. Establish `h3 : prj e f' v ∈ Λ`. Rewrite using `[prj_apply]`. Conclude with `Λ.sub_mem (Λ.sub_mem hv (Λ.sum_mem fun a _ => heL a _ (h1 a))) (Λ.sum_mem fun a _ => hf'L a _ (h2 a))`. Use `show n v ∈ _`.

Rewrite using `[hnv, chg_apply]`. Use `Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ⟨⟨_, h3, ?_⟩, ?_⟩) ?_` and prove the remaining obligations. Conclude with `Submodule.sum_mem _ fun a _ => smul_mem_idSpan (I := fun a => (B a)⁻¹) e (h1 a)`. Use `show n _ = _`. Rewrite using `[hnv, chg_apply]`.

Simplify using `[e_prj h', f_prj h', prj_apply e f' (prj e f' v)]`. Use `mem_orth_span.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨a, rfl⟩)`. Conclude with `e_prj h a _`. Conclude with `f_prj h a _`.

Conclude with `Submodule.sum_mem _ fun a _ => smul_mem_idSpan f (h2 a)`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, x, hx, rfl⟩`. Use `⟨_, heL a x hx, ?_⟩` and prove the remaining obligations. Use `show n _ = _`.

Rewrite using `[map_smul, hne]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, x, hx, rfl⟩`. Use `⟨_, hf'L a x hx, ?_⟩` and prove the remaining obligations. Use `show n _ = _`.

Rewrite using `[map_smul, hnf]`.
-/
theorem exists_split (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) {e f : Fin r → S.V} (h : IsHyp e f) {z : S.V}
    (hez : ∀ a, S.hT (e a) z = 0) (hfz : ∀ a, S.hT (f a) z = 0)
    {B : Fin r → FI E} (h0 : ∀ a, B a ≠ 0) (hB : ∀ a, StarStable (B a))
    {Λ : Submodule (𝓞 E) S.V} (hl : Submodule.IsLattice E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (hz : z ∈ Λ)
    (hX : Λ ⊓ toO S (Submodule.span E (Set.range e)) = idSpan (fun a => (B a)⁻¹) e)
    (hprim : ∀ (c : E), ∀ x ∈ Submodule.span E (Set.range e), x + c • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = c) :
    ∃ n : S.V ≃ₗ[E] S.V, n ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ a, n (e a) = e a) ∧ n z = z ∧
      (∀ x ∈ orth S (Submodule.span E (Set.range e)), n x - x ∈ Submodule.span E (Set.range e)) ∧
      Formalism.HermitianLatticesTheory.gmap n Λ = idSpan (fun a => (B a)⁻¹) e ⊔
        (Formalism.HermitianLatticesTheory.gmap n Λ ⊓ toO S (orth S (Submodule.span E (Set.range e ∪ Set.range f)))) ⊔ idSpan B f := by
  obtain ⟨f', h', hf'z, hf'L⟩ := exists_dual_frame hE h hez hfz h0 hB hl hu hz hX hprim
  obtain ⟨n, hn, hnv⟩ := exists_chg h h'
  have hne : ∀ a, n (e a) = e a := by
    intro a
    have : prj e f' (e a) = 0 := by simp [prj_apply, h.1, h'.fe]
    rw [hnv, chg_of_orth h' (fun b => h.1 b a), this]
    simp
  have hnf : ∀ a, n (f' a) = f a := by
    intro a
    have : prj e f' (f' a) = 0 := by simp [prj_apply, h'.2.1, h'.2.2]
    rw [hnv, chg_apply, this]
    simp [h'.2.1, h'.2.2]
  have heL : ∀ a, ∀ x ∈ (B a)⁻¹, x • e a ∈ Λ := by
    intro a x hx
    have := smul_mem_idSpan (I := fun a => (B a)⁻¹) e hx
    rw [← hX] at this
    exact this.1
  refine ⟨n, hn, hne, ?_, fun x hx => ?_, le_antisymm ?_ (sup_le (sup_le ?_ inf_le_left) ?_)⟩
  · have : prj e f' z = z := by simp [prj_apply, hez, hf'z]
    rw [hnv, chg_of_orth h' hez, this]
    simp [hfz]
  · rw [hnv, chg_of_orth h' (fun a => mem_orth_span.1 hx _ ⟨a, rfl⟩), sub_sub_cancel_left]
    exact Submodule.neg_mem _ (Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  · rintro _ ⟨v, hv, rfl⟩
    have h1 : ∀ a, S.hT (f' a) v ∈ (B a)⁻¹ := by
      intro a
      rw [mem_inv (h0 a)]
      intro y hy
      have := (mem_unimod hu v).1 hv _ (hf'L a _ (hB a y hy))
      rwa [hsmul, star_star, mul_comm] at this
    have h2 : ∀ a, S.hT (e a) v ∈ B a := by
      intro a
      rw [← inv_inv (B a), mem_inv (inv_ne_zero (h0 a))]
      intro y hy
      have := (mem_unimod hu v).1 hv _ (heL a _ ((hB a).inv (h0 a) y hy))
      rwa [hsmul, star_star, mul_comm] at this
    have h3 : prj e f' v ∈ Λ := by
      rw [prj_apply]
      exact Λ.sub_mem (Λ.sub_mem hv (Λ.sum_mem fun a _ => heL a _ (h1 a)))
        (Λ.sum_mem fun a _ => hf'L a _ (h2 a))
    show n v ∈ _
    rw [hnv, chg_apply]
    refine Submodule.add_mem_sup (Submodule.add_mem_sup ?_ ⟨⟨_, h3, ?_⟩, ?_⟩) ?_
    · exact Submodule.sum_mem _ fun a _ => smul_mem_idSpan (I := fun a => (B a)⁻¹) e (h1 a)
    · show n _ = _
      rw [hnv, chg_apply]
      simp [e_prj h', f_prj h', prj_apply e f' (prj e f' v)]
    · refine mem_orth_span.2 ?_
      rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · exact e_prj h a _
      · exact f_prj h a _
    · exact Submodule.sum_mem _ fun a _ => smul_mem_idSpan f (h2 a)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    refine ⟨_, heL a x hx, ?_⟩
    show n _ = _
    rw [map_smul, hne]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    refine ⟨_, hf'L a x hx, ?_⟩
    show n _ = _
    rw [map_smul, hnf]

/- English proof (translation)
Rewrite using `[mem_orth, mem_orth]`. Use `forall_congr' fun y => forall_congr' fun hy => ?_` and prove the remaining obligations. Establish `h` using `hi y x`. Rewrite `h` using `[hn y hy]`. Rewrite using `[h]`.
-/
theorem orth_iff (U : Submodule E S.V) (n : S.V ≃ₗ[E] S.V) (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hn : ∀ x ∈ U, n x = x) (x : S.V) : n x ∈ orth S U ↔ x ∈ orth S U := by
  rw [mem_orth, mem_orth]
  refine forall_congr' fun y => forall_congr' fun hy => ?_
  have h := hi y x
  rw [hn y hy] at h
  rw [h]

/- English proof (translation)
Unfold `Lsub`. Use `inf_le_inf_right _ (sup_le ?_ le_sup_right)` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨l, hl, rfl⟩, hlo⟩`. Establish `hlo' : l ∈ orth S (Xsp F)` using `(orth_iff _ n hi hn l).1 hlo`. Establish `e : n l = l + (n l - l)` using `by abel`.

Use `show n l ∈ _`. Rewrite using `[e]`. Conclude with `Submodule.add_mem_sup ⟨hl, hlo'⟩ (hq l hlo')`.
-/
theorem Lsub_gmap_le {T : E} (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (n : S.V ≃ₗ[E] S.V)
    (hi : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hn : ∀ x ∈ Xsp F, n x = x)
    (hq : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) :
    Lsub (Formalism.HermitianLatticesTheory.gmap n Λ) F ≤ Lsub Λ F := by
  unfold Lsub
  refine inf_le_inf_right _ (sup_le ?_ le_sup_right)
  rintro _ ⟨⟨l, hl, rfl⟩, hlo⟩
  have hlo' : l ∈ orth S (Xsp F) := (orth_iff _ n hi hn l).1 hlo
  have e : n l = l + (n l - l) := by abel
  show n l ∈ _
  rw [e]
  exact Submodule.add_mem_sup ⟨hl, hlo'⟩ (hq l hlo')

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨y, hy, hyx⟩, hx⟩`. Establish `: y = x` using `n.injective ((show n y = x from hyx).trans (hn x hx).symm)`. Conclude with `⟨this ▸ hy, hx⟩`.

Introduce and unpack `⟨hx, hx'⟩`. Conclude with `⟨⟨x, hx, hn x hx'⟩, hx'⟩`.
-/
theorem XLam_gmap {T : E} (F : LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (n : S.V ≃ₗ[E] S.V)
    (hn : ∀ x ∈ Xsp F, n x = x) : XLam (Formalism.HermitianLatticesTheory.gmap n Λ) F = XLam Λ F := by
  ext x
  constructor
  · rintro ⟨⟨y, hy, hyx⟩, hx⟩
    have : y = x := n.injective ((show n y = x from hyx).trans (hn x hx).symm)
    exact ⟨this ▸ hy, hx⟩
  · rintro ⟨hx, hx'⟩
    exact ⟨⟨x, hx, hn x hx'⟩, hx'⟩

end Generic

/- English proof (translation)
Unfold `ddS`. Rewrite using `[FractionalIdeal.coeIdeal_ne_zero, Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `differentIdeal_ne_bot`.
-/
theorem ddS_ne_zero (D : D7) : ddS D ≠ 0 := by
  unfold ddS
  rw [FractionalIdeal.coeIdeal_ne_zero, Ne, Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective _ _)]
  exact differentIdeal_ne_bot

/- English proof (translation)
Introduce `x hx`. Unfold `ddS at hx ⊢`. Take `⟨y, hy, rfl⟩` from `(FractionalIdeal.mem_coeIdeal _).1 hx`. Use `clear hx`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨w, hw, rfl⟩` from `hy`. Establish `: star (algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) w)) = algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) w)` using `(D.sp.cm.fixed _).2 ⟨(w : D.host.F), rfl⟩`. Rewrite using `[this]`. Conclude with `FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem _ hw)`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, star_add]`. Conclude with `Submodule.add_mem (FractionalIdeal.coeToSubmodule _) ha hb`. Consider the case `smul c a _ ha`. Rewrite using `[smul_eq_mul, map_mul, star_mul, mul_comm]`.

Conclude with `Submodule.smul_mem (FractionalIdeal.coeToSubmodule _) (⟨star (c : D.host.E), star_int c.isIntegral_coe⟩ : 𝓞 D.host.E) ha`.
-/
theorem starStable_ddS (D : D7) : StarStable (ddS D) := by
  intro x hx
  unfold ddS at hx ⊢
  obtain ⟨y, hy, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
  clear hx
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, rfl⟩ := hy
    have : star (algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) w)) =
        algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) w) :=
      (D.sp.cm.fixed _).2 ⟨(w : D.host.F), rfl⟩
    rw [this]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem _ hw)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, star_add]; exact Submodule.add_mem (FractionalIdeal.coeToSubmodule _) ha hb
  | smul c a _ ha =>
    rw [smul_eq_mul, map_mul, star_mul, mul_comm]
    exact Submodule.smul_mem (FractionalIdeal.coeToSubmodule _)
      (⟨star (c : D.host.E), star_int c.isIntegral_coe⟩ : 𝓞 D.host.E) ha

/- English proof (translation)
Introduce and unpack `D u F0 Λ ⟨he, hz⟩ ⟨hgen, ⟨hl, hu, hlift, hloc, hprim⟩, hX⟩ -`. Establish `h : IsHyp (S` using `hS D) F0.e D.sp.hypF := by`. Rewrite using `[he]`. Conclude with `⟨D.sp.hyp_ee, D.sp.hyp_ff, D.sp.hyp_ef⟩`. Establish `hXS : XS D F0 = idSpan (S` using `hS D) (fun a => (ddS D ^ ((D.R.rS : ℤ) - (a : ℕ)))⁻¹) F0.e := by`.

Simplify using `only [XS, idSpan, _root_.zpow_neg]`. Establish `hfz : ∀ a, (hS D).hT (D.sp.hypF a) F0.z = 0`. Introduce `a`. Rewrite using `[hz]`. Use `show (hS D).hT (D.sp.hypF a) ((D.cOf u)⁻¹ • D.sp.zm) = 0`.

Rewrite using `[map_smul, ← hsym, (D.sp.hyp_orthz a).2]`. Simplify using the standard rewrite rules. Establish `hzo : F0.z ∈ orth (hS D) F0.X` using `mem_orth_span.2 (by rintro _ ⟨a, rfl⟩; exact F0.z_orth a)`. Establish `hXo : ∀ x ∈ F0.X, x ∈ orth (hS D) F0.X`. Introduce `x hx`.

Use `Submodule.span_le.2 ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `mem_orth_span.2 (by rintro _ ⟨a, rfl⟩; exact F0.e_iso a b)`. Take `⟨n, hn, hne, hnz, hq, hs⟩` from `exists_split (S := hS D) D.sp.cm.cmUnram h F0.z_orth hfz (B := fun a => ddS D ^ ((D.R.rS : ℤ) - (a : ℕ))) (fun a => zpow_ne_zero _ (ddS_ne_zero D)) (fun a => (starStable_ddS D).zpow (ddS_ne_zero D) _) hl hu hlift.1 (hX.trans hXS) (by`. Introduce `c x hx hm`.

Apply `hprim c` to reduce the goal to its premises. Use `⟨?_, Submodule.smul_mem (orth (hS D) F0.X) c hzo⟩` and prove the remaining obligations. Establish `e : c • F0.z = (x + c • F0.z) + -x` using `by abel`. Use `show c • F0.z ∈ _`. Rewrite using `[e]`.

Conclude with `Submodule.add_mem_sup ⟨hm, Submodule.add_mem (orth (hS D) F0.X) (hXo x hx) (Submodule.smul_mem _ c hzo)⟩ (F0.X.neg_mem hx))`. Establish `hnX : ∀ x ∈ F0.X, n x = x`. Introduce `x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨a, rfl⟩ := hx`.

Conclude with `hne a`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp [hx, hy]`. Consider the case `smul c x _ hx => simp [hx]`. Establish `hXL` using `XLam_gmap (lf D F0) Λ n hnX`.

Take `⟨-, -, -, hu', hl'⟩` from `Formalism.HermitianLatticesTheory.isomAct _ _ _ (hS D).hT n hn Λ`. Take `⟨heq, hsg, -⟩` from `Formalism.HermitianLatticesTheory.genusBasic (𝓞 D.host.E) D.host.E _ (hS D).hT (hS D).herm (fun r => ⟨⟨_, star_int r.isIntegral_coe⟩, rfl⟩)`. Use `⟨n, ⟨hn, fun b => ?_, hq⟩, ?_, ⟨hl'.2 hl, heq.trans hgen.2 (hsg Λ n hn)⟩, ⟨hl'.2 hl, hu'.2 hu, ⟨⟨_, hlift.1, hnz⟩, rfl⟩, ?_, fun c hc => ?_⟩, hXL.trans hX⟩` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun a => ?_) b` and prove the remaining obligations. Simplify `hnz` using `[frame, FlagG.fvec]`.

Simplify `hne a` using `[frame, FlagG.fvec]`. Unfold `IsSplit`. Rewrite using `[hXS, Wb, ← he]`. Conclude with `hs`. Rewrite using `[hXL]`.

Conclude with `hloc`. Conclude with `hprim c (Lsub_gmap_le (lf D F0) Λ n hn hnX hq hc)`.
-/
theorem main : ∀ (D : D7) (u : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → 1 ≤ Tu D u → ∃ n : ((hS D).V ≃ₗ[D.host.E] (hS D).V), FixFr D (lf D F0) n ∧ IsSplit D F0 (Formalism.HermitianLatticesTheory.gmap n Λ) ∧ IsRowLat D F0 (Formalism.HermitianLatticesTheory.gmap n Λ) := by
  rintro D u F0 Λ ⟨he, hz⟩ ⟨hgen, ⟨hl, hu, hlift, hloc, hprim⟩, hX⟩ -
  have h : IsHyp (S := hS D) F0.e D.sp.hypF := by
    rw [he]; exact ⟨D.sp.hyp_ee, D.sp.hyp_ff, D.sp.hyp_ef⟩
  have hXS : XS D F0 = idSpan (S := hS D) (fun a => (ddS D ^ ((D.R.rS : ℤ) - (a : ℕ)))⁻¹) F0.e := by
    simp only [XS, idSpan, _root_.zpow_neg]
  have hfz : ∀ a, (hS D).hT (D.sp.hypF a) F0.z = 0 := by
    intro a
    rw [hz]
    show (hS D).hT (D.sp.hypF a) ((D.cOf u)⁻¹ • D.sp.zm) = 0
    rw [map_smul, ← hsym, (D.sp.hyp_orthz a).2]
    simp
  have hzo : F0.z ∈ orth (hS D) F0.X := mem_orth_span.2 (by rintro _ ⟨a, rfl⟩; exact F0.z_orth a)
  have hXo : ∀ x ∈ F0.X, x ∈ orth (hS D) F0.X := by
    intro x hx
    refine Submodule.span_le.2 ?_ hx
    rintro _ ⟨b, rfl⟩
    exact mem_orth_span.2 (by rintro _ ⟨a, rfl⟩; exact F0.e_iso a b)
  obtain ⟨n, hn, hne, hnz, hq, hs⟩ := exists_split (S := hS D) D.sp.cm.cmUnram h F0.z_orth hfz
    (B := fun a => ddS D ^ ((D.R.rS : ℤ) - (a : ℕ))) (fun a => zpow_ne_zero _ (ddS_ne_zero D))
    (fun a => (starStable_ddS D).zpow (ddS_ne_zero D) _) hl hu hlift.1 (hX.trans hXS) (by
      intro c x hx hm
      apply hprim c
      refine ⟨?_, Submodule.smul_mem (orth (hS D) F0.X) c hzo⟩
      have e : c • F0.z = (x + c • F0.z) + -x := by abel
      show c • F0.z ∈ _
      rw [e]
      exact Submodule.add_mem_sup ⟨hm, Submodule.add_mem (orth (hS D) F0.X) (hXo x hx)
        (Submodule.smul_mem _ c hzo)⟩ (F0.X.neg_mem hx))
  have hnX : ∀ x ∈ F0.X, n x = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => obtain ⟨a, rfl⟩ := hx; exact hne a
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  have hXL := XLam_gmap (lf D F0) Λ n hnX
  obtain ⟨-, -, -, hu', hl'⟩ := Formalism.HermitianLatticesTheory.isomAct _ _ _ (hS D).hT n hn Λ
  obtain ⟨heq, hsg, -⟩ := Formalism.HermitianLatticesTheory.genusBasic (𝓞 D.host.E) D.host.E _ (hS D).hT (hS D).herm
    (fun r => ⟨⟨_, star_int r.isIntegral_coe⟩, rfl⟩)
  refine ⟨n, ⟨hn, fun b => ?_, hq⟩, ?_, ⟨hl'.2 hl, heq.trans hgen.2 (hsg Λ n hn)⟩,
    ⟨hl'.2 hl, hu'.2 hu, ⟨⟨_, hlift.1, hnz⟩, rfl⟩, ?_, fun c hc => ?_⟩, hXL.trans hX⟩
  · refine Fin.lastCases ?_ (fun a => ?_) b
    · simpa [frame, FlagG.fvec] using hnz
    · simpa [frame, FlagG.fvec] using hne a
  · unfold IsSplit
    rw [hXS, Wb, ← he]
    exact hs
  · rw [hXL]; exact hloc
  · exact hprim c (Lsub_gmap_le (lf D F0) Λ n hn hnX hq hc)

end GlobalTheory.LoopC.RowSplit

end
