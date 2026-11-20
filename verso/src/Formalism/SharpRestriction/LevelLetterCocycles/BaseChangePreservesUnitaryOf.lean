import Mathlib
import Formalism.WachLatticeTwists.LagrangeExtensionCocycles.DualWByLettersExtended
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds

noncomputable section

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LiftKerD

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `h0 : 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 x)` using `(P.v_O LL _).2 x.2`. Break down `h0.lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Apply `hx` to reduce the goal to its premises.

Establish `hne : algebraMap ↥(OL LL) ↥LL.1 x ≠ 0`. Introduce `h'`. Rewrite `h` using `[h', AddValuation.map_zero]`. Conclude with `WithTop.zero_ne_top h`. Establish `hinv : P.v LL (algebraMap ↥(OL LL) ↥LL.1 x)⁻¹ = 0`.

Establish `h1 : P.v LL (algebraMap ↥(OL LL) ↥LL.1 x) + P.v LL (algebraMap ↥(OL LL) ↥LL.1 x)⁻¹ = 0`. Rewrite using `[← AddValuation.map_mul, mul_inv_cancel₀ hne, AddValuation.map_one]`. Rewrite `h1` using `[← h, zero_add]`. Conclude with `h1`. Establish `hmem : (algebraMap ↥(OL LL) ↥LL.1 x)⁻¹ ∈ OL LL` using `(P.v_O LL _).1 (by rw [hinv])`.

Conclude with `isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩`.
-/
theorem lkd_pos (P : LocPrime l) (LL : FinExt l) (x : ↥(OL LL)) (hx : ¬ IsUnit x) :
    0 < P.v LL (algebraMap ↥(OL LL) ↥LL.1 x) := by
  have h0 : 0 ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 x) := (P.v_O LL _).2 x.2
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply hx
    have hne : algebraMap ↥(OL LL) ↥LL.1 x ≠ 0 := by
      intro h'
      rw [h', AddValuation.map_zero] at h
      exact WithTop.zero_ne_top h
    have hinv : P.v LL (algebraMap ↥(OL LL) ↥LL.1 x)⁻¹ = 0 := by
      have h1 : P.v LL (algebraMap ↥(OL LL) ↥LL.1 x) + P.v LL (algebraMap ↥(OL LL) ↥LL.1 x)⁻¹ = 0 := by
        rw [← AddValuation.map_mul, mul_inv_cancel₀ hne, AddValuation.map_one]
      rw [← h, zero_add] at h1
      exact h1
    have hmem : (algebraMap ↥(OL LL) ↥LL.1 x)⁻¹ ∈ OL LL := (P.v_O LL _).1 (by rw [hinv])
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hne)⟩

/- English proof (translation)
Apply `IsLocalRing.of_nonunits_add` to reduce the goal to its premises. Introduce `a b ha hb hu`. Establish `ha'` using `lkd_pos P LL a ha`. Establish `hb'` using `lkd_pos P LL b hb`. Establish `h0` using `zl_v_unit P LL hu.unit`.

Rewrite `h0` using `[IsUnit.unit_spec, map_add]`. Establish `h1` using `AddValuation.map_add (P.v LL) (algebraMap ↥(OL LL) ↥LL.1 a) (algebraMap ↥(OL LL) ↥LL.1 b)`. Rewrite `h1` using `[h0]`. Conclude with `absurd h1 (not_le.2 (lt_min ha' hb'))`.
-/
theorem lkd_local (P : LocPrime l) (LL : FinExt l) : IsLocalRing ↥(OL LL) := by
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb hu
  have ha' := lkd_pos P LL a ha
  have hb' := lkd_pos P LL b hb
  have h0 := zl_v_unit P LL hu.unit
  rw [IsUnit.unit_spec, map_add] at h0
  have h1 := AddValuation.map_add (P.v LL) (algebraMap ↥(OL LL) ↥LL.1 a)
    (algebraMap ↥(OL LL) ↥LL.1 b)
  rw [h0] at h1
  exact absurd h1 (not_le.2 (lt_min ha' hb'))

/- English proof (translation)
Distinguish the cases in `hc : c = 0`. Conclude with `⟨1, by rw [map_one]; exact one_ne_zero, 0, by rw [hc, mul_zero, map_zero]⟩`. Establish `hl0 : ∀ k : ℕ, ((l : ℕ) : ↥LL.1) ^ k ≠ 0`. Introduce `k h`. Use `zl_v_pow P LL k` as an intermediate fact.

Rewrite `this` using `[h, AddValuation.map_zero]`. Conclude with `WithTop.natCast_ne_top k this.symm`. Establish `hvc : P.v LL c ≠ ⊤` using `fun h => hc ((AddValuation.top_iff (P.v LL)).1 h)`. Take `⟨q, hq⟩` from `WithTop.ne_top_iff_exists.1 hvc`. Take `⟨k, hk⟩` from `exists_nat_ge (-q)`.

Establish `hmap : algebraMap ↥(OL LL) ↥LL.1 (((l : ℕ) : ↥(OL LL)) ^ k) = ((l : ℕ) : ↥LL.1) ^ k`. Rewrite using `[map_pow, map_natCast]`. Establish `hv : 0 ≤ P.v LL (((l : ℕ) : ↥LL.1) ^ k * c)`. Rewrite using `[AddValuation.map_mul, zl_v_pow, ← hq]`. Establish `h2 : (0 : ℚ) ≤ (k : ℚ) + q` using `by linarith`.

Conclude with `h2` after adjusting the coercions. Conclude with `⟨((l : ℕ) : ↥(OL LL)) ^ k, by rw [hmap]; exact hl0 k, ⟨_, (P.v_O LL _).1 hv⟩, by rw [hmap]; rfl⟩`.
-/
theorem lkd_den (P : LocPrime l) (LL : FinExt l) (c : ↥LL.1) :
    ∃ a : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a ≠ 0 ∧
      ∃ o : ↥(OL LL), algebraMap ↥(OL LL) ↥LL.1 a * c = algebraMap ↥(OL LL) ↥LL.1 o := by
  by_cases hc : c = 0
  · exact ⟨1, by rw [map_one]; exact one_ne_zero, 0, by rw [hc, mul_zero, map_zero]⟩
  have hl0 : ∀ k : ℕ, ((l : ℕ) : ↥LL.1) ^ k ≠ 0 := by
    intro k h
    have := zl_v_pow P LL k
    rw [h, AddValuation.map_zero] at this
    exact WithTop.natCast_ne_top k this.symm
  have hvc : P.v LL c ≠ ⊤ := fun h => hc ((AddValuation.top_iff (P.v LL)).1 h)
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hvc
  obtain ⟨k, hk⟩ := exists_nat_ge (-q)
  have hmap : algebraMap ↥(OL LL) ↥LL.1 (((l : ℕ) : ↥(OL LL)) ^ k) = ((l : ℕ) : ↥LL.1) ^ k := by
    rw [map_pow, map_natCast]
  have hv : 0 ≤ P.v LL (((l : ℕ) : ↥LL.1) ^ k * c) := by
    rw [AddValuation.map_mul, zl_v_pow, ← hq]
    have h2 : (0 : ℚ) ≤ (k : ℚ) + q := by linarith
    exact_mod_cast h2
  exact ⟨((l : ℕ) : ↥(OL LL)) ^ k, by rw [hmap]; exact hl0 k,
    ⟨_, (P.v_O LL _).1 hv⟩, by rw [hmap]; rfl⟩

end LiftKerD

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LiftBCoh

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

/- English proof (translation)
Unfold `latticeFiniteCohomology`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc, rfl⟩`. Conclude with `⟨c.1, c.2, hc, rfl⟩`.

Introduce and unpack `⟨c, hc, hf, rfl⟩`. Conclude with `⟨⟨c, hc⟩, hf, rfl⟩`.
-/
theorem liftb_mem_H1fT (PD : PeriodData G Qp K₀ K B BdR) (T : LocLat G Qp LL O) (κ : LatticeCohomology T.L) :
    κ ∈ latticeFiniteCohomology PD T.L ↔ ∃ (c : G → T.V) (hc : c ∈ latticeCocycles T.L), c ∈ latticeFiniteCocycles PD T.L ∧
      (Submodule.Quotient.mk (⟨c, hc⟩ : ↥(latticeCocycles T.L)) : LatticeCohomology T.L) = κ := by
  unfold latticeFiniteCohomology
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.1, c.2, hc, rfl⟩
  · rintro ⟨c, hc, hf, rfl⟩
    exact ⟨⟨c, hc⟩, hf, rfl⟩

/- English proof (translation)
Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Both sides reduce to the same expression.
-/
theorem liftb_mk_eq_zero (T : LocLat G Qp LL O) (c : ↥(latticeCocycles T.L)) :
    (Submodule.Quotient.mk c : LatticeCohomology T.L) = 0 ↔ (c : G → T.V) ∈ latticeCoboundaries T.L := by
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/- English proof (translation)
Introduce `c hc`. Establish `hcZ : c ∈ latticeCocycles T'.L` using `hc.1`. Take `⟨κ₁, hκ₁, hh⟩` from `h (Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T'.L))) ((liftb_mem_H1fT PD T' _).2 ⟨c, hcZ, hc, rfl⟩)`. Take `⟨c₁, hc₁Z, hc₁, rfl⟩` from `(liftb_mem_H1fT PD T κ₁).1 hκ₁`. Establish `hmap : F.H1map (Submodule.Quotient.mk (⟨c₁, hc₁Z⟩ : ↥(latticeCocycles T.L)) : LatticeCohomology T.L) = (Submodule.Quotient.mk (⟨F.post c₁, F.post_Z1T c₁ hc₁Z⟩ : ↥(latticeCocycles T'.L)) : LatticeCohomology T'.L)` using `rfl`.

Rewrite `hh` using `[hmap, ← Submodule.Quotient.mk_smul]`. Establish `h0 : (Submodule.Quotient.mk (((PD.p : O) ^ e) • (⟨c, hcZ⟩ : ↥(latticeCocycles T'.L)) - (⟨F.post c₁, F.post_Z1T c₁ hc₁Z⟩ : ↥(latticeCocycles T'.L))) : LatticeCohomology T'.L) = 0`. Rewrite using `[Submodule.Quotient.mk_sub, hh, sub_self]`. Establish `h1` using `(liftb_mk_eq_zero T' _).1 h0`. Establish `h2 : ((PD.p : O) ^ e) • c = F.post c₁ + ((((PD.p : O) ^ e) • (⟨c, hcZ⟩ : ↥(latticeCocycles T'.L)) - (⟨F.post c₁, F.post_Z1T c₁ hc₁Z⟩ : ↥(latticeCocycles T'.L)) : ↥(latticeCocycles T'.L)) : G → T'.V)`.

Simplify using the standard rewrite rules. Rewrite using `[h2]`. Conclude with `Submodule.add_mem_sup (Submodule.mem_map_of_mem hc₁) h1`.
-/
theorem liftb_LiftF_of (PD : PeriodData G Qp K₀ K B BdR) {T T' : LocLat G Qp LL O}
    (F : LatHom T.L T'.L) (e : ℕ)
    (h : ∀ κ ∈ latticeFiniteCohomology PD T'.L, ∃ κ₁ ∈ latticeFiniteCohomology PD T.L, F.H1map κ₁ = ((PD.p : O) ^ e) • κ) :
    F.LiftF PD e := by
  intro c hc
  have hcZ : c ∈ latticeCocycles T'.L := hc.1
  obtain ⟨κ₁, hκ₁, hh⟩ := h (Submodule.Quotient.mk (⟨c, hcZ⟩ : ↥(latticeCocycles T'.L)))
    ((liftb_mem_H1fT PD T' _).2 ⟨c, hcZ, hc, rfl⟩)
  obtain ⟨c₁, hc₁Z, hc₁, rfl⟩ := (liftb_mem_H1fT PD T κ₁).1 hκ₁
  have hmap : F.H1map (Submodule.Quotient.mk (⟨c₁, hc₁Z⟩ : ↥(latticeCocycles T.L)) : LatticeCohomology T.L) =
      (Submodule.Quotient.mk (⟨F.post c₁, F.post_Z1T c₁ hc₁Z⟩ : ↥(latticeCocycles T'.L)) : LatticeCohomology T'.L) := rfl
  rw [hmap, ← Submodule.Quotient.mk_smul] at hh
  have h0 : (Submodule.Quotient.mk (((PD.p : O) ^ e) • (⟨c, hcZ⟩ : ↥(latticeCocycles T'.L)) -
      (⟨F.post c₁, F.post_Z1T c₁ hc₁Z⟩ : ↥(latticeCocycles T'.L))) : LatticeCohomology T'.L) = 0 := by
    rw [Submodule.Quotient.mk_sub, hh, sub_self]
  have h1 := (liftb_mk_eq_zero T' _).1 h0
  have h2 : ((PD.p : O) ^ e) • c = F.post c₁ + ((((PD.p : O) ^ e) • (⟨c, hcZ⟩ : ↥(latticeCocycles T'.L)) -
      (⟨F.post c₁, F.post_Z1T c₁ hc₁Z⟩ : ↥(latticeCocycles T'.L)) : ↥(latticeCocycles T'.L)) : G → T'.V) := by
    simp
  rw [h2]
  exact Submodule.add_mem_sup (Submodule.mem_map_of_mem hc₁) h1

/- English proof (translation)
Proceed by induction on `κ using Submodule.Quotient.induction_on with`. Consider the case `H c => rfl`.
-/
theorem liftb_res_nat (H : Subgroup G) {T T' : LocLat G Qp LL O} (F : LatHom T.L T'.L)
    (κ : LatticeCohomology T.L) :
    (Formalism.BasicNotions.resHom F H).H1map (Formalism.MainNotions.DeltaInvariantLattices.res H T κ) = Formalism.MainNotions.DeltaInvariantLattices.res H T' (F.H1map κ) := by
  induction κ using Submodule.Quotient.induction_on with
  | H c => rfl

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `κ`. Proceed by induction on `κ using Submodule.Quotient.induction_on with`. Consider the case `H c`. Introduce `h0`.

Establish `h1 : (Submodule.Quotient.mk (⟨Formalism.MainNotions.DeltaInvariantLattices.resFun H T c, Formalism.MainNotions.DeltaInvariantLattices.resFun_Z1T H T c c.2⟩ : ↥(latticeCocycles (resLat T H))) : LatticeCohomology (resLat T H)) = 0` using `h0`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨x, hx, hxc⟩` from `h1`. Rewrite using `[liftb_mk_eq_zero]`. Use `⟨x, hx, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `g`. Establish `hg : g ∈ H` using `hH ▸ Subgroup.mem_top g`. Conclude with `congrFun hxc ⟨g, hg⟩`.
-/
theorem liftb_res_inj (H : Subgroup G) (hH : H = ⊤) (T : LocLat G Qp LL O) :
    Function.Injective (Formalism.MainNotions.DeltaInvariantLattices.res H T) := by
  rw [injective_iff_map_eq_zero]
  intro κ
  induction κ using Submodule.Quotient.induction_on with
  | H c =>
    intro h0
    have h1 : (Submodule.Quotient.mk (⟨Formalism.MainNotions.DeltaInvariantLattices.resFun H T c, Formalism.MainNotions.DeltaInvariantLattices.resFun_Z1T H T c c.2⟩ :
        ↥(latticeCocycles (resLat T H))) : LatticeCohomology (resLat T H)) = 0 := h0
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨x, hx, hxc⟩ := h1
    rw [liftb_mk_eq_zero]
    refine ⟨x, hx, ?_⟩
    funext g
    have hg : g ∈ H := hH ▸ Subgroup.mem_top g
    exact congrFun hxc ⟨g, hg⟩

/- English proof (translation)
Introduce `κ`. Proceed by induction on `κ using Submodule.Quotient.induction_on with`. Consider the case `H c`. Establish `hm : ∀ g : G, g ∈ H` using `fun g => hH ▸ Subgroup.mem_top g`. Take `⟨⟨hcont, hcoc⟩, hT⟩` from `c.2`.

Establish `hc' : (fun g : G => (c : ↥H → T.V) ⟨g, hm g⟩) ∈ latticeCocycles T.L`. Use `⟨⟨hcont.comp (continuous_id.subtype_mk hm), fun g h => ?_⟩, fun g _ => hT _ (Set.mem_univ _)⟩` and prove the remaining obligations. Conclude with `hcoc ⟨g, hm g⟩ ⟨h, hm h⟩`. Use `⟨Submodule.Quotient.mk ⟨_, hc'⟩, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem liftb_res_surj (H : Subgroup G) (hH : H = ⊤) (T : LocLat G Qp LL O) :
    Function.Surjective (Formalism.MainNotions.DeltaInvariantLattices.res H T) := by
  intro κ
  induction κ using Submodule.Quotient.induction_on with
  | H c =>
    have hm : ∀ g : G, g ∈ H := fun g => hH ▸ Subgroup.mem_top g
    obtain ⟨⟨hcont, hcoc⟩, hT⟩ := c.2
    have hc' : (fun g : G => (c : ↥H → T.V) ⟨g, hm g⟩) ∈ latticeCocycles T.L := by
      refine ⟨⟨hcont.comp (continuous_id.subtype_mk hm), fun g h => ?_⟩, fun g _ => hT _ (Set.mem_univ _)⟩
      exact hcoc ⟨g, hm g⟩ ⟨h, hm h⟩
    refine ⟨Submodule.Quotient.mk ⟨_, hc'⟩, ?_⟩
    rfl

end LiftBCoh

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LiftBLocal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O]

@[reducible] def liftb_modZ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Module ℤ_[ℓ] (W.DD T) :=
  Module.compHom _ (algebraMap ℤ_[ℓ] O)

attribute [local instance] liftb_modZ

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun z c x => by change (z • c) • x = (algebraMap ℤ_[ℓ] O z) • (c • x) rw [Algebra.smul_def, mul_smul]⟩`.
-/
theorem liftb_towZO (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    IsScalarTower ℤ_[ℓ] O (W.DD T) :=
  ⟨fun z c x => by
    change (z • c) • x = (algebraMap ℤ_[ℓ] O z) • (c • x)
    rw [Algebra.smul_def, mul_smul]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun z a x => by change (z • a) • x = (algebraMap ℤ_[ℓ] O z) • (a • x) rw [← algebraMap_smul O z a, smul_assoc]⟩`.
-/
theorem liftb_towZA (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    IsScalarTower ℤ_[ℓ] (LetA O n) (W.DD T) :=
  ⟨fun z a x => by
    change (z • a) • x = (algebraMap ℤ_[ℓ] O z) • (a • x)
    rw [← algebraMap_smul O z a, smul_assoc]⟩

attribute [local instance] liftb_towZO liftb_towZA

/- English proof (translation)
Rewrite using `[← Nat.cast_pow, Nat.cast_smul_eq_nsmul]`.
-/
theorem liftb_ns {R D : Type} [Semiring R] [AddCommMonoid D] [Module R D] (p k : ℕ) (x : D) :
    ((p : R) ^ k) • x = (p ^ k : ℕ) • x := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

def liftb_base (W : LocWach PD LL O v n) : Formalism.CoboundaryTransfers.Base ℤ_[ℓ] (LetA O n) where
  p := PD.p
  hp := PD.hp
  φ := W.φA.restrictScalars ℤ_[ℓ]
  γ := (W.γA W.gam).restrictScalars ℤ_[ℓ]
  X := W.X
  Q := W.Q
  comm := fun a => W.φA_γA W.gam a
  φX := ⟨W.Q, W.φA_X⟩

/- English proof (translation)
Use `W.φD_smul T (algebraMap (LetA O n) W.EE a) x` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, W.φE_ext, algebraMap_smul]`. Conclude with `this`.
-/
theorem liftb_φ_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.φE_ext, algebraMap_smul] at this
  exact this

/- English proof (translation)
Use `W.γD_smul T W.gam (algebraMap (LetA O n) W.EE a) x` as an intermediate fact. Rewrite `this` using `[algebraMap_smul, W.γE_ext, algebraMap_smul]`. Conclude with `this`.
-/
theorem liftb_γ_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  have := W.γD_smul T W.gam (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

structure liftb_Good (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M : ℕ) : Prop where
  φN : ∀ x ∈ W.N T, W.Q ^ M • W.φD T x ∈ W.N T
  γN : ∀ x ∈ W.N T, ∃ x' ∈ W.N T, W.γ T x - x = W.X • x'
  γQN : ∀ y : W.DD T, W.Q ^ M • y ∈ W.N T →
    ∃ y' : W.DD T, W.Q ^ M • y' ∈ W.N T ∧ W.γ T y - y = W.X • y'

  crys : IsCrys PD T.ρ

def liftb_wach (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M : ℕ) (g : liftb_Good W T M) :
    Formalism.CoboundaryTransfers.WachMod (liftb_base (ℓ := ℓ) W) M (W.DD T) where
  N := W.N T
  φ := (W.φD T).restrictScalars ℤ_[ℓ]
  γ := (W.γ T).restrictScalars ℤ_[ℓ]
  φ_smul := liftb_φ_smul W T
  γ_smul := liftb_γ_smul W T
  comm := fun x => W.φγ_comm T W.gam x
  X_inj := liftb_X_inj W T
  Q_bij := liftb_Q_bij W T
  φ_N := g.φN
  γ_N := g.γN
  γ_QN := g.γQN

def liftb_hom (W : LocWach PD LL O v n) {T T' : LocLat G Qp LL O} (F : LatHom T.L T'.L) (M : ℕ)
    (g : liftb_Good W T M) (g' : liftb_Good W T' M) :
    Formalism.CoboundaryTransfers.Hom (liftb_wach (ℓ := ℓ) W T M g) (liftb_wach (ℓ := ℓ) W T' M g') where
  f := (W.map F).restrictScalars (LetA O n)
  φ_comm := W.map_φ F
  γ_comm := fun x => W.map_γ F W.gam x
  N_le := W.map_N F g.crys g'.crys

def liftb_DDExact (W : LocWach PD LL O v n) {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L)
    (π : LatHom T₁.L T₂.L) : Prop :=
  Function.Injective (W.map ι) ∧ ∀ x, W.map π x = 0 ↔ ∃ x₀, W.map ι x₀ = x

def liftb_ses (W : LocWach PD LL O v n) {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L)
    (π : LatHom T₁.L T₂.L) (M : ℕ) (g₀ : liftb_Good W T₀ M) (g₁ : liftb_Good W T₁ M)
    (g₂ : liftb_Good W T₂ M) (hE : liftb_DDExact W ι π)
    (hsat : ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) :
    Formalism.CoboundaryTransfers.SES (liftb_wach (ℓ := ℓ) W T₀ M g₀) (liftb_wach (ℓ := ℓ) W T₁ M g₁)
      (liftb_wach (ℓ := ℓ) W T₂ M g₂) where
  ι := liftb_hom W ι M g₀ g₁
  π := liftb_hom W π M g₁ g₂
  ι_inj := hE.1
  exact := hE.2
  sat := hsat

/- English proof (translation)
Assemble the required witnesses or components as `⟨by have := PD.finK₀ rw [W.n_eq] exact (Module.finrank_pos (R := Qp) (M := K₀)).ne'⟩`.
-/
theorem liftb_neZero (W : LocWach PD LL O v n) : NeZero n :=
  ⟨by
    have := PD.finK₀
    rw [W.n_eq]
    exact (Module.finrank_pos (R := Qp) (M := K₀)).ne'⟩

/- English proof (translation)
Use `Finset.univ_sum_single (1 : LetA O n)` as an intermediate fact. Simplify `this` using `[letE]`.
-/
theorem liftb_sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  have := Finset.univ_sum_single (1 : LetA O n)
  simpa [letE] using this

/- English proof (translation)
The claim follows from `Submodule.mem_map.2 ⟨x, hx, rfl⟩`.
-/
theorem liftb_letE_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) {x : W.DD T}
    (hx : x ∈ W.N T) : (letE i : LetA O n) • x ∈ W.Nl T i :=
  Submodule.mem_map.2 ⟨x, hx, rfl⟩

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `(W.N T).smul_mem _ hx`.
-/
theorem liftb_Nl_le (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) :
    W.Nl T i ≤ W.N T := by
  rintro _ ⟨x, hx, rfl⟩
  exact (W.N T).smul_mem _ hx

/- English proof (translation)
Rewrite using `[← Finset.sum_smul, liftb_sum_letE, one_smul]`.
-/
theorem liftb_split [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (x : W.DD T) :
    x = ∑ i : ZMod n, (letE i : LetA O n) • x := by
  rw [← Finset.sum_smul, liftb_sum_letE, one_smul]

/- English proof (translation)
Establish `h` using `Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n)) (Finset.mem_range.2 (ZMod.val_lt i))`. Simplify `h` using `[Mmax, ZMod.natCast_zmod_val]`.
-/
theorem liftb_le_Mmax [NeZero n] (Mi : ZMod n → ℕ) (i : ZMod n) : Mi i ≤ Mmax n Mi := by
  have h := Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n)) (Finset.mem_range.2 (ZMod.val_lt i))
  simpa [Mmax, ZMod.natCast_zmod_val] using h

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `ciSup_le (fun i => liftb_le_Mmax Mi i)`. Conclude with `Finset.sup_le (fun k _ => le_ciSup (Set.finite_range Mi).bddAbove (k : ZMod n))`.
-/
theorem liftb_mx_eq [NeZero n] (Mi : ZMod n → ℕ) : Formalism.MainNotions.DeltaInvariantLattices.mx Mi = Mmax n Mi := by
  apply le_antisymm
  · exact ciSup_le (fun i => liftb_le_Mmax Mi i)
  · exact Finset.sup_le (fun k _ => le_ciSup (Set.finite_range Mi).bddAbove (k : ZMod n))

/- English proof (translation)
Introduce `τ i hτ` and use `h i τ hτ`.
-/
theorem liftb_jl (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ)
    (h : JumpsLet W T Mi hi) : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mi hi := fun τ i hτ => h i τ hτ

/- English proof (translation)
Establish `hγN : ∀ x ∈ W.N T, ∃ x' ∈ W.N T, W.γ T x - x = W.X • x'`. Introduce `x hx`. Take `⟨x', hx', h⟩` from `h2.2.2 x hx`. Conclude with `⟨x', hx', h.symm⟩`. Use `⟨?_, hγN, ?_, hc⟩` and prove the remaining obligations.

Introduce `x hx`. Rewrite using `[liftb_split W T x, map_sum, Finset.smul_sum]`. Use `Submodule.sum_mem _ (fun j _ => ?_)` and prove the remaining obligations. Establish `h` using `h5.1 (j + 1) ((letE j : LetA O n) • x) (by rw [add_sub_cancel_right]; exact liftb_letE_mem W T j hx)`. Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le (liftb_le_Mmax Mi (j + 1))`.

Rewrite using `[hd, add_comm, pow_add, mul_smul]`. Conclude with `(W.N T).smul_mem _ h`. Introduce `y hy`. Take `⟨w, hw, hw1⟩` from `hQ`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hw1`.

Generalize the expression as in `Mmax n Mi = M at hy ⊢`. Establish `hwU : IsUnit w`. Establish `: w = 1 + W.X * t` using `by rw [mul_comm, ht]; ring`. Rewrite using `[this]`. Conclude with `liftb_one_add_X_unit W t`.

Take `⟨wi, hwi⟩` from `(hwU.pow M).exists_left_inv`. Take `⟨c0, hc0⟩ : (w - 1) ∣ (w ^ M - 1)` from `by simpa using sub_dvd_pow_sub_pow w 1 M`. Establish `hc : wi = 1 + W.X * (-(wi * t * c0))`. Establish `h1 : wi - 1 = -(wi * (w ^ M - 1))` using `by rw [mul_sub, hwi]; ring`. Establish `h2 : wi = 1 + -(wi * (w ^ M - 1))` using `by rw [← h1]; ring`.

Rewrite `h2` using `[hc0, ← ht]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨n', hn', hγ⟩` from `hγN (W.Q ^ M • y) hy`. Establish `e1 : W.γ T (W.Q ^ M • y) = (w ^ M * W.Q ^ M) • W.γ T y`. Rewrite using `[liftb_γ_smul, map_pow, hw, mul_pow]`.

Establish `e2 : W.Q ^ M • W.γ T y = wi • (W.Q ^ M • y + W.X • n')`. Establish `: W.γ T (W.Q ^ M • y) = W.Q ^ M • y + W.X • n'` using `by rw [← hγ]; abel`. Rewrite using `[← this, e1, smul_smul, ← mul_assoc, hwi, one_mul]`. Use `set c := -(wi * t * c0) with hcdef`. Establish `hn'' : c • (W.Q ^ M • y) + wi • n' ∈ W.N T` using `(W.N T).add_mem ((W.N T).smul_mem _ hy) ((W.N T).smul_mem _ hn')`.

Establish `hbij` using `liftb_unit_bij W T (W.Q ^ M) (by rw [map_pow]; exact (liftb_Q_unit W).pow M)`. Take `⟨y', hy'⟩` from `hbij.2 (c • (W.Q ^ M • y) + wi • n')`. Establish `hy'' : W.Q ^ M • y' = c • (W.Q ^ M • y) + wi • n'` using `hy'`. Use `⟨y', by rw [hy'']; exact hn'', ?_⟩` and prove the remaining obligations. Apply `hbij.1` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `W.Q ^ M • (W.γ T y - y) = W.Q ^ M • (W.X • y')`. Rewrite using `[smul_comm (W.Q ^ M) W.X y', hy'', smul_sub, e2]`. Establish `e3 : wi • (W.Q ^ M • y + W.X • n') = (1 + W.X * c) • (W.Q ^ M • y) + W.X • (wi • n')`. Rewrite using `[← hc, smul_add, smul_comm wi W.X n']`. Rewrite using `[e3, add_smul, one_smul, mul_smul, smul_add]`.

Normalize the expressions using the abelian group laws.
-/
theorem liftb_good_of [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hc : IsCrys PD T.ρ)
    (Mi hi : ZMod n → ℕ) (h2 : Formalism.MainNotions.DeltaInvariantLattices.p2 W T) (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T Mi hi)
    (hQ : ∃ w : LetA O n, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X}) :
    liftb_Good W T (Mmax n Mi) := by
  have hγN : ∀ x ∈ W.N T, ∃ x' ∈ W.N T, W.γ T x - x = W.X • x' := by
    intro x hx
    obtain ⟨x', hx', h⟩ := h2.2.2 x hx
    exact ⟨x', hx', h.symm⟩
  refine ⟨?_, hγN, ?_, hc⟩
  · intro x hx
    rw [liftb_split W T x, map_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    have h := h5.1 (j + 1) ((letE j : LetA O n) • x)
      (by rw [add_sub_cancel_right]; exact liftb_letE_mem W T j hx)
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (liftb_le_Mmax Mi (j + 1))
    rw [hd, add_comm, pow_add, mul_smul]
    exact (W.N T).smul_mem _ h
  · intro y hy
    obtain ⟨w, hw, hw1⟩ := hQ
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hw1
    generalize Mmax n Mi = M at hy ⊢
    have hwU : IsUnit w := by
      have : w = 1 + W.X * t := by rw [mul_comm, ht]; ring
      rw [this]
      exact liftb_one_add_X_unit W t
    obtain ⟨wi, hwi⟩ := (hwU.pow M).exists_left_inv
    obtain ⟨c0, hc0⟩ : (w - 1) ∣ (w ^ M - 1) := by simpa using sub_dvd_pow_sub_pow w 1 M
    have hc : wi = 1 + W.X * (-(wi * t * c0)) := by
      have h1 : wi - 1 = -(wi * (w ^ M - 1)) := by rw [mul_sub, hwi]; ring
      have h2 : wi = 1 + -(wi * (w ^ M - 1)) := by rw [← h1]; ring
      rw [hc0, ← ht] at h2
      calc wi = 1 + -(wi * (t * W.X * c0)) := h2
        _ = 1 + W.X * (-(wi * t * c0)) := by ring
    obtain ⟨n', hn', hγ⟩ := hγN (W.Q ^ M • y) hy
    have e1 : W.γ T (W.Q ^ M • y) = (w ^ M * W.Q ^ M) • W.γ T y := by
      rw [liftb_γ_smul, map_pow, hw, mul_pow]
    have e2 : W.Q ^ M • W.γ T y = wi • (W.Q ^ M • y + W.X • n') := by
      have : W.γ T (W.Q ^ M • y) = W.Q ^ M • y + W.X • n' := by rw [← hγ]; abel
      rw [← this, e1, smul_smul, ← mul_assoc, hwi, one_mul]
    set c := -(wi * t * c0) with hcdef
    have hn'' : c • (W.Q ^ M • y) + wi • n' ∈ W.N T :=
      (W.N T).add_mem ((W.N T).smul_mem _ hy) ((W.N T).smul_mem _ hn')
    have hbij := liftb_unit_bij W T (W.Q ^ M) (by rw [map_pow]; exact (liftb_Q_unit W).pow M)
    obtain ⟨y', hy'⟩ := hbij.2 (c • (W.Q ^ M • y) + wi • n')
    have hy'' : W.Q ^ M • y' = c • (W.Q ^ M • y) + wi • n' := hy'
    refine ⟨y', by rw [hy'']; exact hn'', ?_⟩
    apply hbij.1
    change W.Q ^ M • (W.γ T y - y) = W.Q ^ M • (W.X • y')
    rw [smul_comm (W.Q ^ M) W.X y', hy'', smul_sub, e2]
    have e3 : wi • (W.Q ^ M • y + W.X • n') =
        (1 + W.X * c) • (W.Q ^ M • y) + W.X • (wi • n') := by
      rw [← hc, smul_add, smul_comm wi W.X n']
    rw [e3, add_smul, one_smul, mul_smul, smul_add]
    abel

/- English proof (translation)
Introduce `y hy`. Establish `: ∀ i : ZMod n, ∃ x ∈ W.N T₁, W.map F x = a • ((letE i : LetA O n) • y)`. Introduce `i`. Take `⟨x, hx, hxe⟩` from `h i _ (liftb_letE_mem W T₂ i hy)`. Conclude with `⟨x, liftb_Nl_le W T₁ i hx, hxe⟩`.

Use `choose x hx hxe using this`. Use `⟨∑ i, x i, Submodule.sum_mem _ (fun i _ => hx i), ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum, Finset.sum_congr rfl (fun i _ => hxe i), ← Finset.smul_sum, ← liftb_split W T₂ y]`.
-/
theorem liftb_kills_all [NeZero n] (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O}
    (F : LatHom T₁.L T₂.L) (a : LetA O n) (h : ∀ i, Kills W F i a) :
    ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁, W.map F x = a • y := by
  intro y hy
  have : ∀ i : ZMod n, ∃ x ∈ W.N T₁, W.map F x = a • ((letE i : LetA O n) • y) := by
    intro i
    obtain ⟨x, hx, hxe⟩ := h i _ (liftb_letE_mem W T₂ i hy)
    exact ⟨x, liftb_Nl_le W T₁ i hx, hxe⟩
  choose x hx hxe using this
  refine ⟨∑ i, x i, Submodule.sum_mem _ (fun i _ => hx i), ?_⟩
  rw [map_sum, Finset.sum_congr rfl (fun i _ => hxe i), ← Finset.smul_sum, ← liftb_split W T₂ y]

/- English proof (translation)
Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add p q hp hq`. Introduce `x hx`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `N.add_mem (hp x hx) (hq x hx)`.

Consider the case `monomial k a`. Introduce `x hx`. Rewrite using `[Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]`. Apply `N.smul_mem` to reduce the goal to its premises. Proceed by induction on `k with`.

Consider the case `zero => simpa using hx`. Consider the case `succ k ih => rw [pow_succ', Module.End.mul_apply]`. Conclude with `h _ ih`.
-/
theorem liftb_aeval_mem {R D : Type} [CommRing R] [AddCommGroup D] [Module R D] (N : Submodule R D)
    (f : D →ₗ[R] D) (h : ∀ x ∈ N, f x ∈ N) (P : Polynomial R) :
    ∀ x ∈ N, Polynomial.aeval f P x ∈ N := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    intro x hx
    rw [map_add, LinearMap.add_apply]
    exact N.add_mem (hp x hx) (hq x hx)
  | monomial k a =>
    intro x hx
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    apply N.smul_mem
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact h _ ih

/- English proof (translation)
Proceed by induction on `P using Polynomial.induction_on' with`. Consider the case `add p q hp hq => simp only [map_add, Polynomial.map_add, LinearMap.add_apply, hp, hq]`. Consider the case `monomial k a`. Rewrite using `[Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, algebraMap_smul, Module.End.pow_apply, Module.End.pow_apply]`. Both sides reduce to the same expression.
-/
theorem liftb_aeval_res {D : Type} [AddCommGroup D] [Module O D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] O D] (f : D →ₗ[O] D) (P : Polynomial ℤ_[ℓ]) (y : D) :
    Polynomial.aeval (f.restrictScalars ℤ_[ℓ]) P y =
      Polynomial.aeval f (P.map (algebraMap ℤ_[ℓ] O)) y := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.map_add, LinearMap.add_apply, hp, hq]
  | monomial k a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
      Module.End.mul_apply, Module.End.mul_apply, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, algebraMap_smul, Module.End.pow_apply, Module.End.pow_apply]
    rfl

/- English proof (translation)
Simplify using `[JSet]`.
-/
theorem liftb_zero_notMem_JSet (jumps : Finset ℤ) (M : ℕ) : (0 : ℤ) ∉ JSet jumps M := by
  simp [JSet]

/- English proof (translation)
Introduce `y hy`. Express the relevant statement in the definitionally equal form `Polynomial.aeval ((W.γ T₀).restrictScalars ℤ_[ℓ]) _ y ∈ W.N T₀`. Rewrite using `[liftb_aeval_res]`. Establish `hy' : W.Q ^ M • y ∈ W.N T₀` using `hy`. Establish `stab : ∀ x ∈ (W.N T₀).restrictScalars O, W.γ T₀ x ∈ (W.N T₀).restrictScalars O`.

Introduce `x hx`. Take `⟨x', hx', h⟩` from `g₀.γN x hx`. Establish `: W.γ T₀ x = x + W.X • x'` using `by rw [← h]; abel`. Rewrite using `[this]`. Conclude with `(W.N T₀).add_mem hx ((W.N T₀).smul_mem _ hx')`.

Distinguish the cases in `hM : M = 0`. Substitute `hM` using the available equality. Conclude with `liftb_aeval_mem _ _ stab _ y (by simpa using hy')`. Take `⟨_, _, F, hF, hkill, _⟩` from `hss (Nat.one_le_iff_ne_zero.2 hM)`. Establish `hU : Units.map (algebraMap ℤ_[ℓ] O).toMonoidHom u = Formalism.MainNotions.DeltaInvariantLattices.uU W` using `Units.ext hu`.

Establish `hz : ∀ j : ℤ, algebraMap ℤ_[ℓ] O (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) = (((Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-j) : Oˣ) : O)`. Introduce `j`. Rewrite using `[← hU, ← map_zpow]`. Both sides reduce to the same expression. Establish `hP : ((Polynomial.X - 1) * ∏ j ∈ JSet jumps M, (Polynomial.X - Polynomial.C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))).map (algebraMap ℤ_[ℓ] O) = ∏ j ∈ insert 0 (JSet jumps M), (Polynomial.X - Polynomial.C ((((Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-j) : Oˣ) : O)))`.

Rewrite using `[Finset.prod_insert (liftb_zero_notMem_JSet jumps M), Polynomial.map_mul, Polynomial.map_prod]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hz]`.

Establish `hsub : F ⊆ (insert 0 (JSet jumps M)).image (fun j : ℤ => (Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-j))`. Introduce `c hc`. Establish `hc' : c ∈ (F : Set Oˣ)` using `hc`. Rewrite `hc'` using `[hF]`. Take `⟨a, ha, j, hj1, hjM, rfl⟩` from `hc'`.

Use `Finset.mem_image.2 ⟨a + j, ?_, rfl⟩` and prove the remaining obligations. Distinguish the cases in `h0 : a + (j : ℤ) = 0`. Rewrite using `[h0]`. Conclude with `Finset.mem_insert_self _ _`. Apply `Finset.mem_insert_of_mem` to reduce the goal to its premises.

Apply `Finset.mem_union_left` to reduce the goal to its premises. Use `Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(a, (j : ℤ)), ?_, rfl⟩, h0⟩` and prove the remaining obligations. Conclude with `Finset.mem_product.2 ⟨hj a ha, Finset.mem_Icc.2 ⟨by show (1 : ℤ) ≤ (j : ℤ); exact_mod_cast hj1, by show (j : ℤ) ≤ (M : ℤ); exact_mod_cast hjM⟩⟩`. Establish `hdvd : (∏ c ∈ F, (Polynomial.X - Polynomial.C (c : O))) ∣ ∏ j ∈ insert 0 (JSet jumps M), (Polynomial.X - Polynomial.C ((((Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-j) : Oˣ) : O)))`. Rewrite using `[Finset.prod_comp (fun c : Oˣ => (Polynomial.X - Polynomial.C (c : O))) (fun j : ℤ => (Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-j))]`.

Use `(Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans ?_` and prove the remaining obligations. Use `Finset.prod_dvd_prod_of_dvd _ _ (fun c hc => dvd_pow_self _ ?_)` and prove the remaining obligations. Take `⟨j, hj, rfl⟩` from `Finset.mem_image.1 hc`. Establish `hne : (Finset.filter (fun a : ℤ => Formalism.MainNotions.DeltaInvariantLattices.uU W ^ (-a) = Formalism.MainNotions.DeltaInvariantLattices.uU W ^ (-j)) (insert 0 (JSet jumps M))).Nonempty` using `⟨j, Finset.mem_filter.2 ⟨hj, rfl⟩⟩`. Conclude with `(Finset.card_pos.2 hne).ne'`.

Take `⟨R, hR⟩` from `hdvd`. Rewrite using `[hP, hR, mul_comm, map_mul, Module.End.mul_apply]`. Conclude with `liftb_aeval_mem _ _ stab R _ (hkill y hy')`.
-/
theorem liftb_semi (W : LocWach PD LL O v n) (T₀ : LocLat G Qp LL O) (M : ℕ)
    (g₀ : liftb_Good W T₀ M) (u : ℤ_[ℓ]ˣ)
    (hu : algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ]) = ((W.χΓ W.gam : Oˣ) : O)) (jumps : Finset ℤ)
    (hj : ∀ a ∈ Formalism.MainNotions.DeltaInvariantLattices.Jumps (PD := PD) T₀, a ∈ jumps)
    (hss : 1 ≤ M → Formalism.MainNotions.DeltaInvariantLattices.SSEig W T₀ (Formalism.MainNotions.DeltaInvariantLattices.invN W T₀ (W.Q ^ M)) (W.N T₀)
      {c | ∃ a ∈ Formalism.MainNotions.DeltaInvariantLattices.Jumps (PD := PD) T₀, ∃ j : ℕ, 1 ≤ j ∧ j ≤ M ∧
        c = (Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-(a + j))}) :
    ∀ y, (liftb_wach (ℓ := ℓ) W T₀ M g₀).QInv y →
      Polynomial.aeval (liftb_wach (ℓ := ℓ) W T₀ M g₀).γ ((Polynomial.X - 1) *
        ∏ j ∈ JSet jumps M, (Polynomial.X - Polynomial.C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))) y ∈
        (liftb_wach (ℓ := ℓ) W T₀ M g₀).N := by
  classical
  intro y hy
  change Polynomial.aeval ((W.γ T₀).restrictScalars ℤ_[ℓ]) _ y ∈ W.N T₀
  rw [liftb_aeval_res]
  have hy' : W.Q ^ M • y ∈ W.N T₀ := hy
  have stab : ∀ x ∈ (W.N T₀).restrictScalars O, W.γ T₀ x ∈ (W.N T₀).restrictScalars O := by
    intro x hx
    obtain ⟨x', hx', h⟩ := g₀.γN x hx
    have : W.γ T₀ x = x + W.X • x' := by rw [← h]; abel
    rw [this]
    exact (W.N T₀).add_mem hx ((W.N T₀).smul_mem _ hx')
  by_cases hM : M = 0
  · subst hM
    exact liftb_aeval_mem _ _ stab _ y (by simpa using hy')
  obtain ⟨_, _, F, hF, hkill, _⟩ := hss (Nat.one_le_iff_ne_zero.2 hM)
  have hU : Units.map (algebraMap ℤ_[ℓ] O).toMonoidHom u = Formalism.MainNotions.DeltaInvariantLattices.uU W := Units.ext hu
  have hz : ∀ j : ℤ, algebraMap ℤ_[ℓ] O (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])) =
      (((Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-j) : Oˣ) : O) := by
    intro j
    rw [← hU, ← map_zpow]
    rfl
  have hP : ((Polynomial.X - 1) * ∏ j ∈ JSet jumps M,
      (Polynomial.X - Polynomial.C (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))).map (algebraMap ℤ_[ℓ] O) =
      ∏ j ∈ insert 0 (JSet jumps M),
        (Polynomial.X - Polynomial.C ((((Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-j) : Oˣ) : O))) := by
    rw [Finset.prod_insert (liftb_zero_notMem_JSet jumps M), Polynomial.map_mul,
      Polynomial.map_prod]
    congr 1
    · simp
    · refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hz]
  have hsub : F ⊆ (insert 0 (JSet jumps M)).image (fun j : ℤ => (Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-j)) := by
    intro c hc
    have hc' : c ∈ (F : Set Oˣ) := hc
    rw [hF] at hc'
    obtain ⟨a, ha, j, hj1, hjM, rfl⟩ := hc'
    refine Finset.mem_image.2 ⟨a + j, ?_, rfl⟩
    by_cases h0 : a + (j : ℤ) = 0
    · rw [h0]; exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_union_left
      refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(a, (j : ℤ)), ?_, rfl⟩, h0⟩
      exact Finset.mem_product.2 ⟨hj a ha, Finset.mem_Icc.2
        ⟨by show (1 : ℤ) ≤ (j : ℤ); exact_mod_cast hj1, by show (j : ℤ) ≤ (M : ℤ); exact_mod_cast hjM⟩⟩
  have hdvd : (∏ c ∈ F, (Polynomial.X - Polynomial.C (c : O))) ∣
      ∏ j ∈ insert 0 (JSet jumps M),
        (Polynomial.X - Polynomial.C ((((Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-j) : Oˣ) : O))) := by
    rw [Finset.prod_comp (fun c : Oˣ => (Polynomial.X - Polynomial.C (c : O)))
      (fun j : ℤ => (Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-j))]
    refine (Finset.prod_dvd_prod_of_subset _ _ _ hsub).trans ?_
    refine Finset.prod_dvd_prod_of_dvd _ _ (fun c hc => dvd_pow_self _ ?_)
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hc
    have hne : (Finset.filter (fun a : ℤ => Formalism.MainNotions.DeltaInvariantLattices.uU W ^ (-a) = Formalism.MainNotions.DeltaInvariantLattices.uU W ^ (-j))
        (insert 0 (JSet jumps M))).Nonempty := ⟨j, Finset.mem_filter.2 ⟨hj, rfl⟩⟩
    exact (Finset.card_pos.2 hne).ne'
  obtain ⟨R, hR⟩ := hdvd
  rw [hP, hR, mul_comm, map_mul, Module.End.mul_apply]
  exact liftb_aeval_mem _ _ stab R _ (hkill y hy')

/- English proof (translation)
Simplify using `[LocWach.divisibleCocycles, herrCocycles, LinearMap.mem_ker, sub_eq_add_neg]`.
-/
theorem liftb_mem_Z1D (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (y z : W.DD T) :
    (y, z) ∈ W.divisibleCocycles T ↔ (W.γ T y - y) - (W.φD T z - z) = 0 := by
  simp [LocWach.divisibleCocycles, herrCocycles, LinearMap.mem_ker, sub_eq_add_neg]

/- English proof (translation)
The claim follows from `((W.map F).restrictScalars (LetA O n)).map_smul a x`.
-/
theorem liftb_map_smul (W : LocWach PD LL O v n) {T T' : LocLat G Qp LL O} (F : LatHom T.L T'.L)
    (a : LetA O n) (x : W.DD T) : W.map F (a • x) = a • W.map F x :=
  ((W.map F).restrictScalars (LetA O n)).map_smul a x

/- English proof (translation)
The claim follows from `liftb_unit_bij W T (W.Q ^ M) (by rw [map_pow]; exact (liftb_Q_unit W).pow M)`.
-/
theorem liftb_Qpow_bij (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M : ℕ) :
    Function.Bijective (fun x : W.DD T => W.Q ^ M • x) :=
  liftb_unit_bij W T (W.Q ^ M) (by rw [map_pow]; exact (liftb_Q_unit W).pow M)

/- English proof (translation)
Introduce `y z hyz`. Take `⟨⟨hyQ, m, hm, hz⟩, hd1⟩` from `hyz`. Establish `hyQ' : W.Q ^ M • y ∈ W.N T₂` using `hyQ`. Establish `hz' : z = W.X • m` using `hz`. Establish `hm' : m ∈ W.N T₂` using `hm`.

Establish `hd1' : (W.γ T₂ y - y) - (W.φD T₂ z - z) = 0` using `hd1`. Take `⟨n₁, hn₁, hπn₁⟩` from `hCK _ hyQ'`. Take `⟨m₁, hm₁, hπm₁⟩` from `hCK m hm'`. Take `⟨y₁, hy₁⟩` from `(liftb_Qpow_bij W T₁ M).2 n₁`. Establish `hy₁' : W.Q ^ M • y₁ = n₁` using `hy₁`.

Establish `hπy₁ : W.map π y₁ = (PD.p ^ e : ℕ) • y`. Apply `(liftb_Qpow_bij W T₂ M).1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `W.Q ^ M • W.map π y₁ = W.Q ^ M • ((PD.p ^ e : ℕ) • y)`. Rewrite using `[← liftb_map_smul, hy₁', hπn₁, smul_comm]`. Establish `hπz₁ : W.map π (W.X • m₁) = (PD.p ^ e : ℕ) • z`.

Rewrite using `[liftb_map_smul, hπm₁, hz', smul_comm]`. Take `⟨w, hw, _, k, y₀, hy₀, z₀, hz₀, hk⟩` from `hd hses ((PD.p ^ e : ℕ) • y) ((PD.p ^ e : ℕ) • z) (by`. Express the relevant statement in the definitionally equal form `W.Q ^ M • ((PD.p ^ e : ℕ) • y) ∈ W.N T₂`. Rewrite using `[smul_comm]`. Conclude with `(W.N T₂).smul_of_tower_mem _ hyQ')`.

Use the proof step `⟨(PD.p ^ e : ℕ) • m, (W.N T₂).smul_of_tower_mem _ hm', by`. Express the relevant statement in the definitionally equal form `W.X • ((PD.p ^ e : ℕ) • m) = _`. Rewrite using `[hz', smul_comm]⟩`. Use the proof step `(by`. Establish `h0 : (y, z) ∈ W.divisibleCocycles T₂` using `(liftb_mem_Z1D W T₂ y z).2 hd1'`.

Use `(W.divisibleCocycles T₂).smul_of_tower_mem (PD.p ^ e : ℕ) h0` as an intermediate fact. Conclude with `this)`. Use `y₁ (W.X • m₁) (by change W.Q ^ M • y₁ ∈ W.N T₁; rw [hy₁']; exact hn₁) ⟨m₁, hm₁, rfl⟩ hπy₁ hπz₁`. Establish `hy₀' : W.Q ^ M • y₀ ∈ W.N T₀` using `hy₀`. Take `⟨z₀', hz₀', hz₀e⟩` from `hz₀`.

Establish `hz₀e' : W.X • z₀' = z₀` using `hz₀e`. Establish `hk' : (PD.p ^ k : ℕ) • w = (W.γ T₀ y₀ - y₀) - (W.φD T₀ z₀ - z₀)`. Rewrite using `[← hk, liftb_ns]`. Establish `hπι : ∀ x, W.map π (W.map ι x) = 0` using `fun x => (hE.2 _).2 ⟨x, rfl⟩`. Use `⟨k + e, (PD.p ^ k : ℕ) • y₁ - W.map ι y₀, (PD.p ^ k : ℕ) • (W.X • m₁) - W.map ι z₀, ⟨⟨?_, ?_⟩, ?_⟩, 0, (W.N T₂).zero_mem, ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `W.Q ^ M • ((PD.p ^ k : ℕ) • y₁ - W.map ι y₀) ∈ W.N T₁`. Rewrite using `[smul_sub, smul_comm, hy₁', ← liftb_map_smul]`. Conclude with `(W.N T₁).sub_mem ((W.N T₁).smul_of_tower_mem _ hn₁) (W.map_N ι g₀.crys g₁.crys _ hy₀')`. Use `⟨(PD.p ^ k : ℕ) • m₁ - W.map ι z₀', (W.N T₁).sub_mem ((W.N T₁).smul_of_tower_mem _ hm₁) (W.map_N ι g₀.crys g₁.crys _ hz₀'), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = W.X • ((PD.p ^ k : ℕ) • m₁ - W.map ι z₀')`.

Rewrite using `[smul_sub, ← liftb_map_smul, hz₀e', smul_comm]`. Express the relevant statement in the definitionally equal form `(W.γ T₁ ((PD.p ^ k : ℕ) • y₁ - W.map ι y₀) - ((PD.p ^ k : ℕ) • y₁ - W.map ι y₀)) - (W.φD T₁ ((PD.p ^ k : ℕ) • (W.X • m₁) - W.map ι z₀) - ((PD.p ^ k : ℕ) • (W.X • m₁) - W.map ι z₀)) = 0`. Establish `hγι : W.γ T₁ (W.map ι y₀) = W.map ι (W.γ T₀ y₀)` using `(W.map_γ ι W.gam y₀).symm`. Establish `hφι : W.φD T₁ (W.map ι z₀) = W.map ι (W.φD T₀ z₀)` using `(W.map_φ ι z₀).symm`. Establish `h1 : W.map ι ((PD.p ^ k : ℕ) • w) = (W.map ι (W.γ T₀ y₀) - W.map ι y₀) - (W.map ι (W.φD T₀ z₀) - W.map ι z₀)`.

Rewrite using `[hk', map_sub, map_sub, map_sub]`. Rewrite `h1` using `[map_nsmul, hw]`. Rewrite using `[map_sub, map_sub, map_nsmul, map_nsmul, hγι, hφι]`. Establish `h3 : ((PD.p ^ k : ℕ) • W.γ T₁ y₁ - W.map ι (W.γ T₀ y₀) - ((PD.p ^ k : ℕ) • y₁ - W.map ι y₀)) - ((PD.p ^ k : ℕ) • W.φD T₁ (W.X • m₁) - W.map ι (W.φD T₀ z₀) - ((PD.p ^ k : ℕ) • (W.X • m₁) - W.map ι z₀)) = (PD.p ^ k : ℕ) • ((W.γ T₁ y₁ - y₁) - (W.φD T₁ (W.X • m₁) - W.X • m₁)) - ((W.m …`. Rewrite using `[smul_sub, smul_sub, smul_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h3, h1, sub_self]`. Express the relevant statement in the definitionally equal form `W.map π ((PD.p ^ k : ℕ) • y₁ - W.map ι y₀) = (((PD.p : ℕ) : ℤ_[ℓ]) ^ (k + e)) • y + (W.φD T₂ 0 - 0)`. Rewrite using `[map_sub, hπι, map_nsmul, hπy₁, liftb_ns, map_zero, pow_add, mul_smul]`. Simplify using the standard rewrite rules.

Express the relevant statement in the definitionally equal form `W.map π ((PD.p ^ k : ℕ) • (W.X • m₁) - W.map ι z₀) = (((PD.p : ℕ) : ℤ_[ℓ]) ^ (k + e)) • z + (W.γ T₂ 0 - 0)`. Rewrite using `[map_sub, hπι, map_nsmul, hπz₁, liftb_ns, map_zero, pow_add, mul_smul]`. Simplify using the standard rewrite rules.
-/
theorem liftb_ratSurj (W : LocWach PD LL O v n) {T₀ T₁ T₂ : LocLat G Qp LL O}
    (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L) (M : ℕ) (g₀ : liftb_Good W T₀ M)
    (g₁ : liftb_Good W T₁ M) (g₂ : liftb_Good W T₂ M) (hE : liftb_DDExact W ι π)
    (hsat : ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) (e : ℕ)
    (hses : IsSESLat (Qp := Qp) ι π) (hd : Formalism.MainNotions.DeltaInvariantLattices.p2d W ι π M)
    (hCK : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁, W.map π x = (PD.p ^ e : ℕ) • y) :
    Formalism.CoboundaryTransfers.RatSurj (liftb_ses (ℓ := ℓ) W ι π M g₀ g₁ g₂ hE hsat) := by
  intro y z hyz
  obtain ⟨⟨hyQ, m, hm, hz⟩, hd1⟩ := hyz
  have hyQ' : W.Q ^ M • y ∈ W.N T₂ := hyQ
  have hz' : z = W.X • m := hz
  have hm' : m ∈ W.N T₂ := hm
  have hd1' : (W.γ T₂ y - y) - (W.φD T₂ z - z) = 0 := hd1
  obtain ⟨n₁, hn₁, hπn₁⟩ := hCK _ hyQ'
  obtain ⟨m₁, hm₁, hπm₁⟩ := hCK m hm'
  obtain ⟨y₁, hy₁⟩ := (liftb_Qpow_bij W T₁ M).2 n₁
  have hy₁' : W.Q ^ M • y₁ = n₁ := hy₁
  have hπy₁ : W.map π y₁ = (PD.p ^ e : ℕ) • y := by
    apply (liftb_Qpow_bij W T₂ M).1
    change W.Q ^ M • W.map π y₁ = W.Q ^ M • ((PD.p ^ e : ℕ) • y)
    rw [← liftb_map_smul, hy₁', hπn₁, smul_comm]
  have hπz₁ : W.map π (W.X • m₁) = (PD.p ^ e : ℕ) • z := by
    rw [liftb_map_smul, hπm₁, hz', smul_comm]
  obtain ⟨w, hw, _, k, y₀, hy₀, z₀, hz₀, hk⟩ := hd hses ((PD.p ^ e : ℕ) • y) ((PD.p ^ e : ℕ) • z)
    (by
      change W.Q ^ M • ((PD.p ^ e : ℕ) • y) ∈ W.N T₂
      rw [smul_comm]
      exact (W.N T₂).smul_of_tower_mem _ hyQ')
    ⟨(PD.p ^ e : ℕ) • m, (W.N T₂).smul_of_tower_mem _ hm', by
      change W.X • ((PD.p ^ e : ℕ) • m) = _
      rw [hz', smul_comm]⟩
    (by
      have h0 : (y, z) ∈ W.divisibleCocycles T₂ := (liftb_mem_Z1D W T₂ y z).2 hd1'
      have := (W.divisibleCocycles T₂).smul_of_tower_mem (PD.p ^ e : ℕ) h0
      exact this)
    y₁ (W.X • m₁) (by change W.Q ^ M • y₁ ∈ W.N T₁; rw [hy₁']; exact hn₁) ⟨m₁, hm₁, rfl⟩ hπy₁ hπz₁
  have hy₀' : W.Q ^ M • y₀ ∈ W.N T₀ := hy₀
  obtain ⟨z₀', hz₀', hz₀e⟩ := hz₀
  have hz₀e' : W.X • z₀' = z₀ := hz₀e
  have hk' : (PD.p ^ k : ℕ) • w = (W.γ T₀ y₀ - y₀) - (W.φD T₀ z₀ - z₀) := by
    rw [← hk, liftb_ns]
  have hπι : ∀ x, W.map π (W.map ι x) = 0 := fun x => (hE.2 _).2 ⟨x, rfl⟩
  refine ⟨k + e, (PD.p ^ k : ℕ) • y₁ - W.map ι y₀, (PD.p ^ k : ℕ) • (W.X • m₁) - W.map ι z₀,
    ⟨⟨?_, ?_⟩, ?_⟩, 0, (W.N T₂).zero_mem, ?_, ?_⟩
  · change W.Q ^ M • ((PD.p ^ k : ℕ) • y₁ - W.map ι y₀) ∈ W.N T₁
    rw [smul_sub, smul_comm, hy₁', ← liftb_map_smul]
    exact (W.N T₁).sub_mem ((W.N T₁).smul_of_tower_mem _ hn₁) (W.map_N ι g₀.crys g₁.crys _ hy₀')
  · refine ⟨(PD.p ^ k : ℕ) • m₁ - W.map ι z₀', (W.N T₁).sub_mem ((W.N T₁).smul_of_tower_mem _ hm₁)
      (W.map_N ι g₀.crys g₁.crys _ hz₀'), ?_⟩
    change _ = W.X • ((PD.p ^ k : ℕ) • m₁ - W.map ι z₀')
    rw [smul_sub, ← liftb_map_smul, hz₀e', smul_comm]
  · change (W.γ T₁ ((PD.p ^ k : ℕ) • y₁ - W.map ι y₀) - ((PD.p ^ k : ℕ) • y₁ - W.map ι y₀)) -
      (W.φD T₁ ((PD.p ^ k : ℕ) • (W.X • m₁) - W.map ι z₀) -
        ((PD.p ^ k : ℕ) • (W.X • m₁) - W.map ι z₀)) = 0
    have hγι : W.γ T₁ (W.map ι y₀) = W.map ι (W.γ T₀ y₀) := (W.map_γ ι W.gam y₀).symm
    have hφι : W.φD T₁ (W.map ι z₀) = W.map ι (W.φD T₀ z₀) := (W.map_φ ι z₀).symm
    have h1 : W.map ι ((PD.p ^ k : ℕ) • w) =
        (W.map ι (W.γ T₀ y₀) - W.map ι y₀) - (W.map ι (W.φD T₀ z₀) - W.map ι z₀) := by
      rw [hk', map_sub, map_sub, map_sub]
    rw [map_nsmul, hw] at h1
    rw [map_sub, map_sub, map_nsmul, map_nsmul, hγι, hφι]
    have h3 : ((PD.p ^ k : ℕ) • W.γ T₁ y₁ - W.map ι (W.γ T₀ y₀) - ((PD.p ^ k : ℕ) • y₁ - W.map ι y₀)) -
        ((PD.p ^ k : ℕ) • W.φD T₁ (W.X • m₁) - W.map ι (W.φD T₀ z₀) -
          ((PD.p ^ k : ℕ) • (W.X • m₁) - W.map ι z₀)) =
        (PD.p ^ k : ℕ) • ((W.γ T₁ y₁ - y₁) - (W.φD T₁ (W.X • m₁) - W.X • m₁)) -
          ((W.map ι (W.γ T₀ y₀) - W.map ι y₀) - (W.map ι (W.φD T₀ z₀) - W.map ι z₀)) := by
      rw [smul_sub, smul_sub, smul_sub]
      abel
    rw [h3, h1, sub_self]
  · change W.map π ((PD.p ^ k : ℕ) • y₁ - W.map ι y₀) =
      (((PD.p : ℕ) : ℤ_[ℓ]) ^ (k + e)) • y + (W.φD T₂ 0 - 0)
    rw [map_sub, hπι, map_nsmul, hπy₁, liftb_ns, map_zero, pow_add, mul_smul]
    simp
  · change W.map π ((PD.p ^ k : ℕ) • (W.X • m₁) - W.map ι z₀) =
      (((PD.p : ℕ) : ℤ_[ℓ]) ^ (k + e)) • z + (W.γ T₂ 0 - 0)
    rw [map_sub, hπι, map_nsmul, hπz₁, liftb_ns, map_zero, pow_add, mul_smul]
    simp

def liftb_Complete (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Prop :=
  ∃ I : Ideal (LetA O n), W.Q ∈ I ∧ (∀ a ∈ I, W.φA a ∈ I) ∧ IsAdicComplete I ↥(W.N T)

def liftb_RegXQ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Prop :=
  ∀ x ∈ W.N T, (∃ m ∈ W.N T, W.Q • x = W.X • m) → ∃ m ∈ W.N T, x = W.X • m

/- English proof (translation)
Substitute `hp` using the available equality. Take `⟨I, hQI, hφI, hI⟩` from `hC`. Establish `: IsAdicComplete I ↥(liftb_wach (ℓ` using `PD.p) W T₀ M g₀).N := hI`. Establish `hγX : (liftb_base (ℓ` using `PD.p) W).GammaX (u : ℤ_[PD.p]) := by`. Take `⟨t, ht⟩` from `liftb_gammaX W`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[PD.p] O (LetA O n), hu]`. Conclude with `ht`. Establish `hγQ : (liftb_base (ℓ` using `PD.p) W).GammaQ := by`. Take `⟨w, hw, hw1⟩` from `hQ`.

Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hw1`. Establish `hwt : w = 1 + W.X * t` using `by rw [mul_comm, ht]; ring`. Conclude with `⟨w, by rw [hwt]; exact liftb_one_add_X_unit W t, ⟨t, hwt⟩, hw⟩`. Establish `h1` using `Formalism.RepresentationBoundsCohomology.N2.phi_map_surjective ℤ_[PD.p] (LetA O n) (liftb_base (ℓ := PD.p) W) M (W.DD T₀) (liftb_wach (ℓ := PD.p) W T₀ M g₀) I 1 (M + 1) ⟨1, by rw [pow_one, mul_one]; exact W.φA_X⟩ (by omega) hQI hφI`. Establish `hRX` using `Formalism.RepresentationBoundsCohomology.N2.regulator_bound_for_x PD.p (LetA O n) (liftb_base (ℓ := PD.p) W) M (W.DD T₀) (liftb_wach (ℓ := PD.p) W T₀ M g₀) hR`.

Establish `hRL : ∀ y, (liftb_wach (ℓ` using `PD.p) W T₀ M g₀).QInv y → ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ (liftb_wach (ℓ := PD.p) W T₀ M g₀).N → y ∈ (liftb_wach (ℓ := PD.p) W T₀ M g₀).N := by`. Introduce `y _ hy`. Use `h6 y ⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, Nat.cast_smul_eq_nsmul]`. Rewrite `hy` using `[Nat.cast_smul_eq_nsmul]`.

Conclude with `hy`. Establish `hL` using `Formalism.CoboundaryTransfers.wachLatticeUnramified_statement PD.p (LetA O n) (liftb_base (ℓ := PD.p) W) M u rfl W.φA_X hγX hγQ (W.DD T₀) (W.DD T₁) (W.DD T₂) _ _ _ (liftb_ses (ℓ := PD.p) W ι π M g₀ g₁ g₂ hE hsat) e W.s (JSet jumps M) W.s_pos W.s_two hv (liftb_zero_notMem_JSet jum …`. Introduce `y hy`. Take `⟨x, hx, hxe⟩` from `hCK y hy`. Conclude with `⟨x, hx, by rw [liftb_ns]; exact hxe⟩)`.

Use the proof step `(liftb_ratSurj W ι π M g₀ g₁ g₂ hE hsat e hses hd hCK)`. Introduce `y z hy hz hyz`. Take `⟨y₁, z₁, ⟨⟨hy₁, hz₁⟩, hd₁⟩, e1, e2⟩` from `hL y z ⟨⟨hy, hz⟩, (liftb_mem_Z1D W T₂ y z).1 hyz⟩`. Use `⟨y₁, z₁, hy₁, hz₁, (liftb_mem_Z1D W T₁ y₁ z₁).2 hd₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← liftb_ns (R := ℤ_[PD.p])]`.

Conclude with `e1`. Rewrite using `[← liftb_ns (R := ℤ_[PD.p])]`. Conclude with `e2`.
-/
theorem liftb_lifts (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (u : ℤ_[ℓ]ˣ)
    (hu : algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ]) = ((W.χΓ W.gam : Oˣ) : O))
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = W.s)
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L) (M : ℕ)
    (g₀ : liftb_Good W T₀ M) (g₁ : liftb_Good W T₁ M) (g₂ : liftb_Good W T₂ M)
    (hE : liftb_DDExact W ι π) (hsat : ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) (e : ℕ)
    (jumps : Finset ℤ)
    (hQ : ∃ w : LetA O n, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X})
    (hses : IsSESLat (Qp := Qp) ι π) (hd : Formalism.MainNotions.DeltaInvariantLattices.p2d W ι π M)
    (hCK : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁, W.map π x = (PD.p ^ e : ℕ) • y)
    (hj : ∀ a ∈ Formalism.MainNotions.DeltaInvariantLattices.Jumps (PD := PD) T₀, a ∈ jumps)
    (hss : 1 ≤ M → Formalism.MainNotions.DeltaInvariantLattices.SSEig W T₀ (Formalism.MainNotions.DeltaInvariantLattices.invN W T₀ (W.Q ^ M)) (W.N T₀)
      {c | ∃ a ∈ Formalism.MainNotions.DeltaInvariantLattices.Jumps (PD := PD) T₀, ∃ j : ℕ, 1 ≤ j ∧ j ≤ M ∧
        c = (Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-(a + j))})
    (hC : liftb_Complete W T₀) (hR : liftb_RegXQ W T₀) (h6 : Formalism.MainNotions.DeltaInvariantLattices.wachSaturated W T₀) :
    ∀ y z : W.DD T₂, W.Q ^ M • y ∈ W.N T₂ → (∃ m ∈ W.N T₂, z = W.X • m) → (y, z) ∈ W.divisibleCocycles T₂ →
      ∃ y₁ z₁ : W.DD T₁, W.Q ^ M • y₁ ∈ W.N T₁ ∧ (∃ m ∈ W.N T₁, z₁ = W.X • m) ∧
        (y₁, z₁) ∈ W.divisibleCocycles T₁ ∧
        W.map π y₁ = (PD.p ^ (e + Formalism.LIFT.eU PD.p M W.s (JSet jumps M)) : ℕ) • y ∧
        W.map π z₁ = (PD.p ^ (e + Formalism.LIFT.eU PD.p M W.s (JSet jumps M)) : ℕ) • z := by
  subst hp
  obtain ⟨I, hQI, hφI, hI⟩ := hC
  have : IsAdicComplete I ↥(liftb_wach (ℓ := PD.p) W T₀ M g₀).N := hI
  have hγX : (liftb_base (ℓ := PD.p) W).GammaX (u : ℤ_[PD.p]) := by
    obtain ⟨t, ht⟩ := liftb_gammaX W
    refine ⟨t, ?_⟩
    rw [IsScalarTower.algebraMap_apply ℤ_[PD.p] O (LetA O n), hu]
    exact ht
  have hγQ : (liftb_base (ℓ := PD.p) W).GammaQ := by
    obtain ⟨w, hw, hw1⟩ := hQ
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hw1
    have hwt : w = 1 + W.X * t := by rw [mul_comm, ht]; ring
    exact ⟨w, by rw [hwt]; exact liftb_one_add_X_unit W t, ⟨t, hwt⟩, hw⟩
  have h1 := Formalism.RepresentationBoundsCohomology.N2.phi_map_surjective ℤ_[PD.p] (LetA O n) (liftb_base (ℓ := PD.p) W) M (W.DD T₀)
    (liftb_wach (ℓ := PD.p) W T₀ M g₀) I 1 (M + 1)
    ⟨1, by rw [pow_one, mul_one]; exact W.φA_X⟩ (by omega) hQI hφI
  have hRX := Formalism.RepresentationBoundsCohomology.N2.regulator_bound_for_x PD.p (LetA O n) (liftb_base (ℓ := PD.p) W) M (W.DD T₀)
    (liftb_wach (ℓ := PD.p) W T₀ M g₀) hR
  have hRL : ∀ y, (liftb_wach (ℓ := PD.p) W T₀ M g₀).QInv y →
      ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ (liftb_wach (ℓ := PD.p) W T₀ M g₀).N →
      y ∈ (liftb_wach (ℓ := PD.p) W T₀ M g₀).N := by
    intro y _ hy
    refine h6 y ⟨1, ?_⟩
    rw [pow_one, Nat.cast_smul_eq_nsmul]
    rw [Nat.cast_smul_eq_nsmul] at hy
    exact hy
  have hL := Formalism.CoboundaryTransfers.wachLatticeUnramified_statement PD.p (LetA O n) (liftb_base (ℓ := PD.p) W) M u rfl W.φA_X hγX hγQ
    (W.DD T₀) (W.DD T₁) (W.DD T₂) _ _ _ (liftb_ses (ℓ := PD.p) W ι π M g₀ g₁ g₂ hE hsat) e W.s
    (JSet jumps M) W.s_pos W.s_two hv (liftb_zero_notMem_JSet jumps M) h1 hRX
    (liftb_semi W T₀ M g₀ u hu jumps hj hss) hRL
    (by
      intro y hy
      obtain ⟨x, hx, hxe⟩ := hCK y hy
      exact ⟨x, hx, by rw [liftb_ns]; exact hxe⟩)
    (liftb_ratSurj W ι π M g₀ g₁ g₂ hE hsat e hses hd hCK)
  intro y z hy hz hyz
  obtain ⟨y₁, z₁, ⟨⟨hy₁, hz₁⟩, hd₁⟩, e1, e2⟩ := hL y z ⟨⟨hy, hz⟩, (liftb_mem_Z1D W T₂ y z).1 hyz⟩
  refine ⟨y₁, z₁, hy₁, hz₁, (liftb_mem_Z1D W T₁ y₁ z₁).2 hd₁, ?_, ?_⟩
  · rw [← liftb_ns (R := ℤ_[PD.p])]; exact e1
  · rw [← liftb_ns (R := ℤ_[PD.p])]; exact e2

def liftb_HKer (W : LocWach PD LL O v n) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Sur W F →
    ∃ (T₀ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L), IsSESLat (Qp := Qp) ι F ∧ IsCrys PD T₀.ρ

def liftb_HExact (W : LocWach PD LL O v n) : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → liftb_DDExact W ι π

def liftb_HStr (W : LocWach PD LL O v n) : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → liftb_Complete W T ∧ liftb_RegXQ W T

def liftb_HExt (W : LocWach PD LL O v n) : Prop :=
  ∀ (T : LocLat G Qp LL O) (c : G → T.V), IsCrys PD T.ρ → c ∈ latticeFiniteCocycles PD T.L →
    ∃ (Tp : LocLat G Qp LL O) (ι : LatHom T.L Tp.L) (π : LatHom Tp.L W.one.L),
      IsCrys PD Tp.ρ ∧ IsExtOf W ι π c

def liftb_HOne (W : LocWach PD LL O v n) : Prop :=
  IsCrys PD W.one.ρ ∧ (∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD W.one.ρ τ a → a = 0) ∧
    ∃ e ∈ W.N W.one, W.N W.one = Submodule.span (LetA O n) {e} ∧ W.φD W.one e = e ∧
      ∀ g, W.γD W.one g e = e

def liftb_HOne0 (W : LocWach PD LL O v n) : Prop :=
  IsCrys PD W.one.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD W.one.ρ τ a → a = 0

/- English proof (translation)
Take `⟨e, e₀, _, hj, hN⟩` from `E.one_e`. Use `⟨e, by rw [hN]; exact Submodule.mem_span_singleton_self e, hN, ?_, ?_⟩` and prove the remaining obligations. Apply `E.jD_inj` to reduce the goal to its premises. Rewrite using `[E.jD_φ, hj]`. Simplify using `[TWmap]`.

Introduce `g`. Take `⟨g', rfl⟩` from `W.resΓ_onto g`. Apply `E.jD_inj` to reduce the goal to its premises. Rewrite using `[E.jD_act, hj]`. Establish `h0 : W.one.actT g' e₀ = e₀` using `Subtype.ext (W.one_triv g' (e₀ : W.one.V))`.

Simplify using `[TWact, h0]`.
-/
theorem liftb_oneGen (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW]
    [Algebra O RA] [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW}
    {gR : G → (RW →ₐ[O] RW)} {πA : RA} (E : EtTie W RA RW inclR φR gR πA) :
    ∃ e ∈ W.N W.one, W.N W.one = Submodule.span (LetA O n) {e} ∧ W.φD W.one e = e ∧
      ∀ g, W.γD W.one g e = e := by
  obtain ⟨e, e₀, _, hj, hN⟩ := E.one_e
  refine ⟨e, by rw [hN]; exact Submodule.mem_span_singleton_self e, hN, ?_, ?_⟩
  · apply E.jD_inj
    rw [E.jD_φ, hj]
    simp [TWmap]
  · intro g
    obtain ⟨g', rfl⟩ := W.resΓ_onto g
    apply E.jD_inj
    rw [E.jD_act, hj]
    have h0 : W.one.actT g' e₀ = e₀ := Subtype.ext (W.one_triv g' (e₀ : W.one.V))
    simp [TWact, h0]

/- English proof (translation)
Take `⟨i, hi'⟩` from `W.emb_bij.2 (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))`. Establish `h` using `hJ i τ hi'.symm a ha`. Unfold `jumpSet`. Use `Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, τ, ha⟩` and prove the remaining obligations. Establish `: ((Mi i : ℕ) : ℤ) ≤ (Mmax n Mi : ℤ)` using `by exact_mod_cast liftb_le_Mmax Mi i`.

Combine the linear relations using `[h.1]`. Establish `: ((hi i : ℕ) : ℤ) ≤ (Mmax n hi : ℤ)` using `by exact_mod_cast liftb_le_Mmax hi i`. Combine the linear relations using `[h.2]`.
-/
theorem liftb_mem_jumpSet [NeZero n] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (Mi hi : ZMod n → ℕ) (hJ : JumpsLet W T Mi hi) (a : ℤ) (τ : K →ₐ[Qp] LL)
    (ha : IsJumpV PD T.ρ τ a) : a ∈ jumpSet W T (Mmax n Mi) (Mmax n hi) := by
  classical
  obtain ⟨i, hi'⟩ := W.emb_bij.2 (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))
  have h := hJ i τ hi'.symm a ha
  unfold jumpSet
  refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨?_, ?_⟩, τ, ha⟩
  · have : ((Mi i : ℕ) : ℤ) ≤ (Mmax n Mi : ℤ) := by exact_mod_cast liftb_le_Mmax Mi i
    linarith [h.1]
  · have : ((hi i : ℕ) : ℤ) ≤ (Mmax n hi : ℤ) := by exact_mod_cast liftb_le_Mmax hi i
    linarith [h.2]

/- English proof (translation)
Use `liftb_neZero W` as an intermediate fact. Introduce `hB T₁ T₂ F Mi hi hS hJ1`. Take `⟨c1, c2, hOnto⟩` from `hS`. Take `⟨T₀, ι, hses, c0⟩` from `hKer T₁ T₂ F ⟨c1, c2, hOnto⟩`. Establish `hJ` using `hJmp T₀ T₁ T₂ ι F hses c0 c1 c2`.

Establish `hJ0 : JumpsLet W T₀ Mi hi` using `fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inl ha))`. Establish `hJ2 : JumpsLet W T₂ Mi hi` using `fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inr ha))`. Establish `hc0` using `h2c T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)`. Establish `hc1` using `h2c T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)`. Establish `hd` using `h2d T₀ T₁ T₂ ι F Mi hi c0 c1 c2 (liftb_jl W T₁ Mi hi hJ1)`.

Rewrite `hc0`, `hc1`, `hd` using `[liftb_mx_eq]`. Establish `hQ` using `hc0.1`. Establish `g₀` using `liftb_good_of W T₀ c0 Mi hi (h2 T₀ c0) (h5 T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)) hQ`. Establish `g₁` using `liftb_good_of W T₁ c1 Mi hi (h2 T₁ c1) (h5 T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)) hQ`. Establish `g₂` using `liftb_good_of W T₂ c2 Mi hi (h2 T₂ c2) (h5 T₂ Mi hi c2 (liftb_jl W T₂ Mi hi hJ2)) hQ`.

Establish `hE` using `hExact T₀ T₁ T₂ ι F hses`. Establish `hsat` using `(h6.2.2 T₀ T₁ T₂ ι F c0 c1 c2 hses).2.2.2.1`. Establish `hCK : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁, W.map F x = (PD.p ^ (eWB PD.p W.s (Hmax n Mi hi)) : ℕ) • y`. Introduce `y hy`. Take `⟨x, hx, hxe⟩` from `liftb_kills_all W F _ (hWB hB T₁ T₂ F Mi hi ⟨c1, c2, hOnto⟩ hJ1) y hy`.

Conclude with `⟨x, hx, by rw [hxe, lp, liftb_ns]⟩`. Establish `hL` using `liftb_lifts W hp u hu hv ι F (Mmax n Mi) g₀ g₁ g₂ hE hsat (eWB PD.p W.s (Hmax n Mi hi)) (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) hQ hses hd hCK (by`. Introduce and unpack `a ⟨τ, ha⟩`. Conclude with `liftb_mem_jumpSet W T₁ Mi hi hJ1 a τ ((hJ τ a).2 (Or.inl ha)))`. Use the proof step `(fun hM => (hcons T₀ c0) _ hM) (hStr T₀ c0).1 (hStr T₀ c0).2 (h6.1 T₀ c0)`.

Apply `liftb_LiftF_of PD F` to reduce the goal to its premises. Introduce `κ hκ`. Take `⟨c, hc, hcf, rfl⟩` from `(liftb_mem_H1fT PD T₂ κ).1 hκ`. Take `⟨Tp, ι', π', cp, hext⟩` from `hExt T₂ c c2 hcf`. Take `⟨cone, hone0, e, he, hspan, hφe, hγe⟩` from `hOne`.

Establish `hJp'` using `hJmp T₂ Tp W.one ι' π' hext.1 c2 cp cone`. Establish `hJp : JumpsLet W Tp Mi hi`. Introduce `i τ hτ a ha`. Break down `(hJp' τ a).1 ha with h | h` into its components or cases. Conclude with `hJ2 i τ hτ a h`.

Rewrite using `[hone0 τ a h]`. Conclude with `⟨by simp, by simp⟩`. Establish `hImg : InImgA W π' (eWB PD.p W.s (Hmax n Mi hi))`. Take `⟨x, hx, hxe⟩` from `liftb_kills_all W π' _ (hWB hB Tp W.one π' Mi hi ⟨cp, cone, hext.1.2.2.1⟩ hJp) e he`. Conclude with `⟨e, he, hspan, hφe, hγe, x, hx, by rw [hxe, lp, liftb_ns, liftb_ns]⟩`.

Take `⟨y, z, h, hy, hz, hcl⟩` from `hExtC T₂ Tp ι' π' Mi hi c2 cp hJ2 c hc hext _ hImg`. Take `⟨y₁, z₁, hy₁, ⟨m₁, hm₁, hz₁⟩, h₁, e1, e2⟩` from `hL y z hy hz h`. Establish `hf₁` using `(hc1.2 y₁ z₁ hy₁ ⟨m₁, hm₁, hz₁.symm⟩ h₁).1`. Take `⟨κ₁, hκ₁⟩` from `liftb_res_surj W.GKs hB.1 T₁ (W.cl T₁ ⟨(y₁, z₁), h₁⟩)`. Use `⟨κ₁, (h2b T₁ c1 κ₁).2 (by rw [hκ₁]; exact hf₁), ?_⟩` and prove the remaining obligations.

Apply `liftb_res_inj W.GKs hB.1 T₂` to reduce the goal to its premises. Rewrite using `[← liftb_res_nat, hκ₁]`. Establish `hN` using `hNat F ⟨(y₁, z₁), h₁⟩ ((PD.p ^ (eWB PD.p W.s (Hmax n Mi hi) + Formalism.LIFT.eU PD.p (Mmax n Mi) W.s (JSet (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (Mmax n Mi))) : ℕ) • (⟨(y, z), h⟩ : ↥(W.divisibleCocycles T₂))) (by`. Rewrite using `[e1, e2]`. Use the proof step `rfl)`.

Use `Eq.trans hN ?_` and prove the remaining obligations. Use `Eq.trans (map_nsmul (W.cl T₂) _ _) ?_` and prove the remaining obligations. Use `Eq.trans (congrArg _ hcl) ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← liftb_ns (R := O), smul_smul, ← pow_add]`. Use `congr 2`.

Simplify using `only [ePB]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coreLiftB_of (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (u : ℤ_[ℓ]ˣ)
    (hu : algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ]) = ((W.χΓ W.gam : Oˣ) : O))
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = W.s)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (h2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W)
    (hcons : Formalism.MainNotions.DeltaInvariantLattices.GammaSemisimpleQuotient W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W) (h2c : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexThirdProperty W)
    (h2d : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFourthProperty W) (hExtC : coreExt W) (hNat : W.ClNat)
    (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O) (hWB : coreWB W)
    (hKer : liftb_HKer W) (hExact : liftb_HExact W) (hStr : liftb_HStr W) (hExt : liftb_HExt W)
    (hOne : liftb_HOne W) : coreLiftB W := by
  have := liftb_neZero W
  intro hB T₁ T₂ F Mi hi hS hJ1
  obtain ⟨c1, c2, hOnto⟩ := hS
  obtain ⟨T₀, ι, hses, c0⟩ := hKer T₁ T₂ F ⟨c1, c2, hOnto⟩
  have hJ := hJmp T₀ T₁ T₂ ι F hses c0 c1 c2
  have hJ0 : JumpsLet W T₀ Mi hi := fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inl ha))
  have hJ2 : JumpsLet W T₂ Mi hi := fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inr ha))
  have hc0 := h2c T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)
  have hc1 := h2c T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)
  have hd := h2d T₀ T₁ T₂ ι F Mi hi c0 c1 c2 (liftb_jl W T₁ Mi hi hJ1)
  rw [liftb_mx_eq] at hc0 hc1 hd
  have hQ := hc0.1
  have g₀ := liftb_good_of W T₀ c0 Mi hi (h2 T₀ c0) (h5 T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)) hQ
  have g₁ := liftb_good_of W T₁ c1 Mi hi (h2 T₁ c1) (h5 T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)) hQ
  have g₂ := liftb_good_of W T₂ c2 Mi hi (h2 T₂ c2) (h5 T₂ Mi hi c2 (liftb_jl W T₂ Mi hi hJ2)) hQ
  have hE := hExact T₀ T₁ T₂ ι F hses
  have hsat := (h6.2.2 T₀ T₁ T₂ ι F c0 c1 c2 hses).2.2.2.1
  have hCK : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁,
      W.map F x = (PD.p ^ (eWB PD.p W.s (Hmax n Mi hi)) : ℕ) • y := by
    intro y hy
    obtain ⟨x, hx, hxe⟩ := liftb_kills_all W F _ (hWB hB T₁ T₂ F Mi hi ⟨c1, c2, hOnto⟩ hJ1) y hy
    exact ⟨x, hx, by rw [hxe, lp, liftb_ns]⟩
  have hL := liftb_lifts W hp u hu hv ι F (Mmax n Mi) g₀ g₁ g₂ hE hsat
    (eWB PD.p W.s (Hmax n Mi hi)) (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) hQ hses hd hCK
    (by
      rintro a ⟨τ, ha⟩
      exact liftb_mem_jumpSet W T₁ Mi hi hJ1 a τ ((hJ τ a).2 (Or.inl ha)))
    (fun hM => (hcons T₀ c0) _ hM) (hStr T₀ c0).1 (hStr T₀ c0).2 (h6.1 T₀ c0)
  apply liftb_LiftF_of PD F
  intro κ hκ
  obtain ⟨c, hc, hcf, rfl⟩ := (liftb_mem_H1fT PD T₂ κ).1 hκ
  obtain ⟨Tp, ι', π', cp, hext⟩ := hExt T₂ c c2 hcf
  obtain ⟨cone, hone0, e, he, hspan, hφe, hγe⟩ := hOne
  have hJp' := hJmp T₂ Tp W.one ι' π' hext.1 c2 cp cone
  have hJp : JumpsLet W Tp Mi hi := by
    intro i τ hτ a ha
    rcases (hJp' τ a).1 ha with h | h
    · exact hJ2 i τ hτ a h
    · rw [hone0 τ a h]
      exact ⟨by simp, by simp⟩
  have hImg : InImgA W π' (eWB PD.p W.s (Hmax n Mi hi)) := by
    obtain ⟨x, hx, hxe⟩ := liftb_kills_all W π' _
      (hWB hB Tp W.one π' Mi hi ⟨cp, cone, hext.1.2.2.1⟩ hJp) e he
    exact ⟨e, he, hspan, hφe, hγe, x, hx, by rw [hxe, lp, liftb_ns, liftb_ns]⟩
  obtain ⟨y, z, h, hy, hz, hcl⟩ := hExtC T₂ Tp ι' π' Mi hi c2 cp hJ2 c hc hext _ hImg
  obtain ⟨y₁, z₁, hy₁, ⟨m₁, hm₁, hz₁⟩, h₁, e1, e2⟩ := hL y z hy hz h
  have hf₁ := (hc1.2 y₁ z₁ hy₁ ⟨m₁, hm₁, hz₁.symm⟩ h₁).1
  obtain ⟨κ₁, hκ₁⟩ := liftb_res_surj W.GKs hB.1 T₁ (W.cl T₁ ⟨(y₁, z₁), h₁⟩)
  refine ⟨κ₁, (h2b T₁ c1 κ₁).2 (by rw [hκ₁]; exact hf₁), ?_⟩
  apply liftb_res_inj W.GKs hB.1 T₂
  rw [← liftb_res_nat, hκ₁]
  have hN := hNat F ⟨(y₁, z₁), h₁⟩
    ((PD.p ^ (eWB PD.p W.s (Hmax n Mi hi) + Formalism.LIFT.eU PD.p (Mmax n Mi) W.s
      (JSet (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (Mmax n Mi))) : ℕ) •
        (⟨(y, z), h⟩ : ↥(W.divisibleCocycles T₂)))
    (by
      rw [e1, e2]
      rfl)
  refine Eq.trans hN ?_
  refine Eq.trans (map_nsmul (W.cl T₂) _ _) ?_
  refine Eq.trans (congrArg _ hcl) ?_
  rw [map_smul, ← liftb_ns (R := O), smul_smul, ← pow_add]
  congr 2
  simp only [ePB]
  ring

end LiftBLocal

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LiftAAvg

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O]

def lifta_avg (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d : O) : W.DD T →ₗ[O] W.DD T :=
  d • ∑ δ ∈ W.DelF, W.γD T δ

/- English proof (translation)
Simplify using `[lifta_avg, LinearMap.sum_apply]`.
-/
theorem lifta_avg_apply (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d : O) (x : W.DD T) :
    lifta_avg W T d x = d • ∑ δ ∈ W.DelF, W.γD T δ x := by
  simp [lifta_avg, LinearMap.sum_apply]

/- English proof (translation)
Take `⟨k, hk, hak⟩` from `(W.DelF_def a).1 ha`. Take `⟨m, hm, hbm⟩` from `(W.DelF_def b).1 hb`. Use `(W.DelF_def _).2 ⟨k * m, Nat.mul_pos hk hm, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_pow, pow_mul, hak, one_pow, mul_comm k m, pow_mul, hbm, one_pow, one_mul]`.
-/
theorem lifta_Del_mul (W : LocWach PD LL O v n) {a b : W.Gam} (ha : a ∈ W.DelF) (hb : b ∈ W.DelF) :
    a * b ∈ W.DelF := by
  obtain ⟨k, hk, hak⟩ := (W.DelF_def a).1 ha
  obtain ⟨m, hm, hbm⟩ := (W.DelF_def b).1 hb
  refine (W.DelF_def _).2 ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hak, one_pow, mul_comm k m, pow_mul, hbm, one_pow, one_mul]

/- English proof (translation)
Take `⟨k, hk, hak⟩` from `(W.DelF_def a).1 ha`. Conclude with `(W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩`.
-/
theorem lifta_Del_inv (W : LocWach PD LL O v n) {a : W.Gam} (ha : a ∈ W.DelF) : a⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, hak⟩ := (W.DelF_def a).1 ha
  exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hak, inv_one]⟩

/- English proof (translation)
Introduce `δ hδ`. Rewrite using `[lifta_avg_apply, map_smul, map_sum]`. Use `congr 1`. Use `Finset.sum_bij' (fun a _ => δ * a) (fun a _ => δ⁻¹ * a) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`.

Conclude with `lifta_Del_mul W hδ ha`. Introduce `a ha`. Conclude with `lifta_Del_mul W (lifta_Del_inv W hδ) ha`. Introduce `a _`. Simplify using the standard rewrite rules.

Introduce `a _`. Simplify using the standard rewrite rules. Introduce `a _`. Rewrite using `[W.γD_mul]`.
-/
theorem lifta_avg_inv (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d : O) (x : W.DD T) :
    ∀ δ ∈ W.DelF, W.γD T δ (lifta_avg W T d x) = lifta_avg W T d x := by
  intro δ hδ
  rw [lifta_avg_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_bij' (fun a _ => δ * a) (fun a _ => δ⁻¹ * a) ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact lifta_Del_mul W hδ ha
  · intro a ha; exact lifta_Del_mul W (lifta_Del_inv W hδ) ha
  · intro a _; simp
  · intro a _; simp
  · intro a _; rw [W.γD_mul]

/- English proof (translation)
Rewrite using `[lifta_avg_apply, Finset.sum_congr rfl hx, Finset.sum_const, ← Nat.cast_smul_eq_nsmul O, smul_smul, hd, one_smul]`.
-/
theorem lifta_avg_fix (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d : O)
    (hd : d * (W.DelF.card : O) = 1) (x : W.DD T) (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    lifta_avg W T d x = x := by
  rw [lifta_avg_apply, Finset.sum_congr rfl hx, Finset.sum_const, ← Nat.cast_smul_eq_nsmul O,
    smul_smul, hd, one_smul]

/- English proof (translation)
Use `⟨?_, lifta_avg_inv W T d x⟩` and prove the remaining obligations. Rewrite using `[lifta_avg_apply]`. Conclude with `(W.N T).smul_of_tower_mem d (Submodule.sum_mem _ (fun δ _ => W.N_Γ T δ x hx))`.
-/
theorem lifta_avg_N (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d : O) (x : W.DD T)
    (hx : x ∈ W.N T) : lifta_avg W T d x ∈ W.NΔ T := by
  refine ⟨?_, lifta_avg_inv W T d x⟩
  rw [lifta_avg_apply]
  exact (W.N T).smul_of_tower_mem d (Submodule.sum_mem _ (fun δ _ => W.N_Γ T δ x hx))

/- English proof (translation)
Rewrite using `[lifta_avg_apply, lifta_avg_apply, map_smul, map_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl (fun δ _ => (W.φγ_comm T δ x).symm)`.
-/
theorem lifta_avg_φ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d : O) (x : W.DD T) :
    lifta_avg W T d (W.φD T x) = W.φD T (lifta_avg W T d x) := by
  rw [lifta_avg_apply, lifta_avg_apply, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun δ _ => (W.φγ_comm T δ x).symm)

/- English proof (translation)
Rewrite using `[lifta_avg_apply, lifta_avg_apply, map_smul, map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun δ _ => ?_)` and prove the remaining obligations. Rewrite using `[← W.γD_mul, ← W.γD_mul, mul_comm]`.
-/
theorem lifta_avg_γ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d : O) (g : W.Gam)
    (x : W.DD T) : lifta_avg W T d (W.γD T g x) = W.γD T g (lifta_avg W T d x) := by
  rw [lifta_avg_apply, lifta_avg_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [← W.γD_mul, ← W.γD_mul, mul_comm]

/- English proof (translation)
Rewrite using `[lifta_avg_apply, lifta_avg_apply, ← algebraMap_smul W.EE d (∑ δ ∈ W.DelF, W.γD T δ x), map_smul, algebraMap_smul, map_sum]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl (fun δ _ => W.map_γ F δ x)`.
-/
theorem lifta_avg_map (W : LocWach PD LL O v n) {T T' : LocLat G Qp LL O} (F : LatHom T.L T'.L)
    (d : O) (x : W.DD T) : W.map F (lifta_avg W T d x) = lifta_avg W T' d (W.map F x) := by
  rw [lifta_avg_apply, lifta_avg_apply, ← algebraMap_smul W.EE d (∑ δ ∈ W.DelF, W.γD T δ x), map_smul,
    algebraMap_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl (fun δ _ => W.map_γ F δ x)

/- English proof (translation)
Establish `h : ∑ δ ∈ W.DelF, W.γD T δ (a • x) = ∑ δ ∈ W.DelF, a • W.γD T δ x` using `Finset.sum_congr rfl (fun δ hδ => by rw [gammaD_semilinear, ha δ hδ])`. Rewrite using `[lifta_avg_apply, lifta_avg_apply, h, ← Finset.smul_sum, smul_comm]`.
-/
theorem lifta_avg_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d : O) (a : LetA O n)
    (ha : a ∈ W.AΔ) (x : W.DD T) : lifta_avg W T d (a • x) = a • lifta_avg W T d x := by
  have h : ∑ δ ∈ W.DelF, W.γD T δ (a • x) = ∑ δ ∈ W.DelF, a • W.γD T δ x :=
    Finset.sum_congr rfl (fun δ hδ => by rw [gammaD_semilinear, ha δ hδ])
  rw [lifta_avg_apply, lifta_avg_apply, h, ← Finset.smul_sum, smul_comm]

/- English proof (translation)
Introduce `y hy`. Take `⟨x, hx, hxe⟩` from `h y hy.1`. Use `⟨lifta_avg W T₁ d x, lifta_avg_N W T₁ d x hx, ?_⟩` and prove the remaining obligations. Rewrite using `[lifta_avg_map, hxe, map_nsmul, lifta_avg_fix W T₂ d hd y hy.2]`.
-/
theorem lifta_cokerΔ (W : LocWach PD LL O v n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (d : O) (hd : d * (W.DelF.card : O) = 1) (k : ℕ)
    (h : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁, W.map F x = k • y) :
    ∀ y ∈ W.NΔ T₂, ∃ x ∈ W.NΔ T₁, W.map F x = k • y := by
  intro y hy
  obtain ⟨x, hx, hxe⟩ := h y hy.1
  refine ⟨lifta_avg W T₁ d x, lifta_avg_N W T₁ d x hx, ?_⟩
  rw [lifta_avg_map, hxe, map_nsmul, lifta_avg_fix W T₂ d hd y hy.2]

/- English proof (translation)
Take `⟨hπΔ, hsub, ⟨w, hw⟩, -⟩` from `h9`. Take `⟨c, hc⟩` from `hπ`. Establish `hk : PD.p - 1 ≠ 0` using `by have := PD.hp.two_le; omega`. Establish `hreg : ∀ a b : LetA O n, W.π₀ * a = W.π₀ * b → a = b` using `fun a b hab => by`. Rewrite `hab` using `[hw]`.

Conclude with `unit_mul_pi_pow_left_cancel w _ a b hab`. Establish `h0 : ∀ i, PowerSeries.constantCoeff (W.π₀ i) = 0`. Introduce `i`. Establish `: W.π₀ i = (w : LetA O n) i * PowerSeries.X ^ (PD.p - 1)`. Rewrite using `[hw]`.

Both sides reduce to the same expression. Rewrite using `[this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hk, mul_zero]`. Take `⟨f, hf, -⟩` from `hsub a ha`. Establish `hS : ∀ i, PowerSeries.HasSubst (W.π₀ i)` using `fun i => PowerSeries.HasSubst.of_constantCoeff_zero' (h0 i)`. Establish `key : ∀ i, a i = W.π₀ i * PowerSeries.subst (W.π₀ i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i))`.

Introduce `i`. Establish `e1 : a i = W.π₀ i * PowerSeries.subst (W.π₀ i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i)) + PowerSeries.C (PowerSeries.constantCoeff (f i))` using `by conv_lhs => rw [hf i, PowerSeries.eq_X_mul_shift_add_const (f i)]`. Rewrite using `[PowerSeries.subst_add (hS i), PowerSeries.subst_mul (hS i), PowerSeries.subst_X (hS i), PowerSeries.subst_C]`. Both sides reduce to the same expression. Establish `e2 : PowerSeries.constantCoeff (a i) = 0`.

Establish `: a i = PowerSeries.X * c i` using `by rw [hc]; rfl`. Rewrite using `[this, map_mul, PowerSeries.constantCoeff_X, zero_mul]`. Establish `e3 : PowerSeries.constantCoeff (f i) = 0`. Use `congrArg PowerSeries.constantCoeff e1` as an intermediate fact. Rewrite `this` using `[e2, map_add, map_mul, h0 i, zero_mul, zero_add, PowerSeries.constantCoeff_C]`.

Conclude with `this.symm`. Rewrite `e1` using `[e3, map_zero, add_zero]`. Conclude with `e1`. Use `set b : LetA O n := fun i => PowerSeries.subst (W.π₀ i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i)) with hb`. Establish `hab : a = W.π₀ * b`.

Use function extensionality and compare the values at `i`. Conclude with `key i`. Use `⟨b, ?_, hab⟩` and prove the remaining obligations. Introduce `δ hδ`. Apply `hreg` to reduce the goal to its premises.

Establish `h1 : W.γA δ (W.π₀ * b) = W.π₀ * b` using `by rw [← hab]; exact ha δ hδ`. Rewrite `h1` using `[map_mul, hπΔ δ hδ]`. Conclude with `h1`.
-/
theorem lifta_interA (W : LocWach PD LL O v n) (h9 : P9π₀ W) (a : LetA O n) (ha : a ∈ W.AΔ)
    (hπ : ∃ c, a = letπ * c) : ∃ b ∈ W.AΔ, a = W.π₀ * b := by
  obtain ⟨hπΔ, hsub, ⟨w, hw⟩, -⟩ := h9
  obtain ⟨c, hc⟩ := hπ
  have hk : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  have hreg : ∀ a b : LetA O n, W.π₀ * a = W.π₀ * b → a = b := fun a b hab => by
    rw [hw] at hab
    exact unit_mul_pi_pow_left_cancel w _ a b hab
  have h0 : ∀ i, PowerSeries.constantCoeff (W.π₀ i) = 0 := by
    intro i
    have : W.π₀ i = (w : LetA O n) i * PowerSeries.X ^ (PD.p - 1) := by
      rw [hw]; rfl
    rw [this, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hk, mul_zero]
  obtain ⟨f, hf, -⟩ := hsub a ha
  have hS : ∀ i, PowerSeries.HasSubst (W.π₀ i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (h0 i)
  have key : ∀ i, a i = W.π₀ i *
      PowerSeries.subst (W.π₀ i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i)) := by
    intro i
    have e1 : a i = W.π₀ i *
        PowerSeries.subst (W.π₀ i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i)) +
        PowerSeries.C (PowerSeries.constantCoeff (f i)) := by
      conv_lhs => rw [hf i, PowerSeries.eq_X_mul_shift_add_const (f i)]
      rw [PowerSeries.subst_add (hS i), PowerSeries.subst_mul (hS i), PowerSeries.subst_X (hS i),
        PowerSeries.subst_C]
      rfl
    have e2 : PowerSeries.constantCoeff (a i) = 0 := by
      have : a i = PowerSeries.X * c i := by rw [hc]; rfl
      rw [this, map_mul, PowerSeries.constantCoeff_X, zero_mul]
    have e3 : PowerSeries.constantCoeff (f i) = 0 := by
      have := congrArg PowerSeries.constantCoeff e1
      rw [e2, map_add, map_mul, h0 i, zero_mul, zero_add, PowerSeries.constantCoeff_C] at this
      exact this.symm
    rw [e3, map_zero, add_zero] at e1
    exact e1
  set b : LetA O n := fun i =>
    PowerSeries.subst (W.π₀ i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i)) with hb
  have hab : a = W.π₀ * b := by
    funext i
    exact key i
  refine ⟨b, ?_, hab⟩
  intro δ hδ
  apply hreg
  have h1 : W.γA δ (W.π₀ * b) = W.π₀ * b := by rw [← hab]; exact ha δ hδ
  rw [map_mul, hπΔ δ hδ] at h1
  exact h1

/- English proof (translation)
Take `⟨⟨r, b, hb, huniq, hΔ⟩, -⟩` from `hm`. Take `⟨m, hmN, hxm⟩` from `hπ`. Take `⟨a, haΔ, hxa⟩` from `hΔ x hx`. Take `⟨c, hmc, -⟩` from `huniq m hmN`. Take `⟨a', -, ha'⟩` from `huniq x hx.1`.

Establish `e1 : a = a'` using `ha' a hxa`. Establish `e2 : (fun j => (letπ : LetA O n) * c j) = a'`. Apply `ha'` to reduce the goal to its premises. Use `show x = ∑ j, ((letπ : LetA O n) * c j) • b j`. Rewrite using `[hxm, hmc, Finset.smul_sum]`.

Conclude with `Finset.sum_congr rfl (fun j _ => by rw [mul_smul])`. Establish `e3 : ∀ j, a j = letπ * c j` using `fun j => by rw [e1, ← e2]`. Establish `: ∀ j, ∃ b' ∈ W.AΔ, a j = W.π₀ * b'` using `fun j => lifta_interA W h9 (a j) (haΔ j) ⟨c j, e3 j⟩`. Use `choose b' hb' hab' using this`. Use `⟨∑ j, b' j • b j, Submodule.sum_mem _ (fun j _ => invariant_smul_mem_invariants' W T (b' j) (hb' j) (b j) (hb j)), ?_⟩` and prove the remaining obligations.

Rewrite using `[hxa, Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl (fun j _ => by rw [hab' j, mul_smul])`.
-/
theorem lifta_interN (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (h9 : P9π₀ W)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (x : W.DD T) (hx : x ∈ W.NΔ T)
    (hπ : ∃ m ∈ W.N T, x = (letπ : LetA O n) • m) : ∃ x' ∈ W.NΔ T, x = W.π₀ • x' := by
  obtain ⟨⟨r, b, hb, huniq, hΔ⟩, -⟩ := hm
  obtain ⟨m, hmN, hxm⟩ := hπ
  obtain ⟨a, haΔ, hxa⟩ := hΔ x hx
  obtain ⟨c, hmc, -⟩ := huniq m hmN
  obtain ⟨a', -, ha'⟩ := huniq x hx.1
  have e1 : a = a' := ha' a hxa
  have e2 : (fun j => (letπ : LetA O n) * c j) = a' := by
    apply ha'
    show x = ∑ j, ((letπ : LetA O n) * c j) • b j
    rw [hxm, hmc, Finset.smul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [mul_smul])
  have e3 : ∀ j, a j = letπ * c j := fun j => by rw [e1, ← e2]
  have : ∀ j, ∃ b' ∈ W.AΔ, a j = W.π₀ * b' := fun j => lifta_interA W h9 (a j) (haΔ j) ⟨c j, e3 j⟩
  choose b' hb' hab' using this
  refine ⟨∑ j, b' j • b j, Submodule.sum_mem _ (fun j _ => invariant_smul_mem_invariants' W T (b' j) (hb' j) (b j) (hb j)),
    ?_⟩
  rw [hxa, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [hab' j, mul_smul])

/- English proof (translation)
Establish `hprime : ℓ.Prime` using `Fact.out`. Establish `hunit : IsUnit (((ℓ - 1 : ℕ)) : ℤ_[ℓ])`. Rewrite using `[PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]`. Establish `h2` using `hprime.two_le`. Conclude with `(Nat.Prime.coprime_iff_not_dvd hprime).2 (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))`.

Use `⟨algebraMap ℤ_[ℓ] O ((hunit.unit⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]), ?_⟩` and prove the remaining obligations. Rewrite using `[hcard, hp, ← map_natCast (algebraMap ℤ_[ℓ] O), ← map_mul, hunit.val_inv_mul, map_one]`.
-/
theorem lifta_exists_d (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (hcard : W.DelF.card = PD.p - 1) :
    ∃ d : O, d * (W.DelF.card : O) = 1 := by
  have hprime : ℓ.Prime := Fact.out
  have hunit : IsUnit (((ℓ - 1 : ℕ)) : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    have h2 := hprime.two_le
    exact (Nat.Prime.coprime_iff_not_dvd hprime).2
      (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))
  refine ⟨algebraMap ℤ_[ℓ] O ((hunit.unit⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]), ?_⟩
  rw [hcard, hp, ← map_natCast (algebraMap ℤ_[ℓ] O), ← map_mul, hunit.val_inv_mul, map_one]

end LiftAAvg

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LiftADss

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def lifta_δ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : W.EE) : W.DD T →ₗ[O] W.DD T :=
  ((LinearMap.lsmul W.EE (W.DD T) c).restrictScalars O).comp (W.γ T - LinearMap.id)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lifta_δ_apply (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : W.EE) (y : W.DD T) :
    lifta_δ W T c y = c • (W.γ T y - y) := rfl

/- English proof (translation)
Rewrite using `[lifta_δ_apply, ← algebraMap_smul W.EE W.π₀, smul_smul, hc, one_smul]`.
-/
theorem lifta_δ_spec (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : W.EE)
    (hc : algebraMap (LetA O n) W.EE W.π₀ * c = 1) (y : W.DD T) :
    W.π₀ • lifta_δ W T c y = W.γ T y - y := by
  rw [lifta_δ_apply, ← algebraMap_smul W.EE W.π₀, smul_smul, hc, one_smul]

/- English proof (translation)
Establish `h'` using `congrArg (fun z => c • z) h`. Simplify using `only [← algebraMap_smul W.EE W.π₀, smul_smul, mul_comm c, hc, one_smul] at h'`. Conclude with `h'`.
-/
theorem lifta_π₀_cancel (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : W.EE)
    (hc : algebraMap (LetA O n) W.EE W.π₀ * c = 1) (x y : W.DD T) (h : W.π₀ • x = W.π₀ • y) :
    x = y := by
  have h' := congrArg (fun z => c • z) h
  simp only [← algebraMap_smul W.EE W.π₀, smul_smul, mul_comm c, hc, one_smul] at h'
  exact h'

/- English proof (translation)
Rewrite using `[map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply]`.
-/
theorem lifta_aeval_lin {D : Type} [AddCommGroup D] [Module O D] (f : D →ₗ[O] D) (a : O) (z : D) :
    Polynomial.aeval f (Polynomial.X - Polynomial.C a : Polynomial O) z = f z - a • z := by
  rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply,
    Module.algebraMap_end_apply]

/- English proof (translation)
Proceed by induction on `xs generalizing seq with`. Consider the case `nil => simp`. Consider the case `cons x xs ih`. Establish `h1 : seq 1 = lifta_δ W T c (seq 0) - cO x • seq 0`. Establish `h` using `hstep 0 (by simp)`.

Establish `h' : W.π₀ • (seq 1 + cO x • seq 0) = W.π₀ • lifta_δ W T c (seq 0)`. Rewrite using `[lifta_δ_spec W T c hc]`. Establish `h'' : W.π₀ • (seq 1 + cO x • seq 0) = W.γD T W.gam (seq 0) - seq 0` using `by simpa using h`. Conclude with `h''`. Use `lifta_π₀_cancel W T c hc _ _ h'` as an intermediate fact.

Rewrite using `[← this]`. Normalize the expressions using the abelian group laws. Establish `h2` using `ih (fun k => seq (k + 1)) (by`. Introduce `k hk`. Establish `h` using `hstep (k + 1) (by simpa using hk)`.

Simplify using `using h)`. Rewrite using `[List.length_cons, h2, List.map_cons, List.prod_cons, mul_comm, map_mul, Module.End.mul_apply, lifta_aeval_lin]`. Simplify using `only [zero_add]`. Rewrite using `[h1]`.
-/
theorem lifta_seq (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : W.EE)
    (hc : algebraMap (LetA O n) W.EE W.π₀ * c = 1) (cO : ℤ → O) (xs : List ℤ) (seq : ℕ → W.DD T)
    (hstep : ∀ k : ℕ, k < xs.length →
      W.π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) = W.γD T W.gam (seq k) - seq k) :
    seq xs.length = Polynomial.aeval (lifta_δ W T c)
      ((xs.map fun x => (Polynomial.X - Polynomial.C (cO x) : Polynomial O)).prod) (seq 0) := by
  induction xs generalizing seq with
  | nil => simp
  | cons x xs ih =>
    have h1 : seq 1 = lifta_δ W T c (seq 0) - cO x • seq 0 := by
      have h := hstep 0 (by simp)
      have h' : W.π₀ • (seq 1 + cO x • seq 0) = W.π₀ • lifta_δ W T c (seq 0) := by
        rw [lifta_δ_spec W T c hc]
        have h'' : W.π₀ • (seq 1 + cO x • seq 0) = W.γD T W.gam (seq 0) - seq 0 := by simpa using h
        exact h''
      have := lifta_π₀_cancel W T c hc _ _ h'
      rw [← this]
      abel
    have h2 := ih (fun k => seq (k + 1)) (by
      intro k hk
      have h := hstep (k + 1) (by simpa using hk)
      simpa using h)
    rw [List.length_cons, h2, List.map_cons, List.prod_cons, mul_comm, map_mul,
      Module.End.mul_apply, lifta_aeval_lin]
    simp only [zero_add]
    rw [h1]

/- English proof (translation)
Establish `hv : v (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1)) = 1`. Rewrite using `[map_sub, map_one, W.gam_gen, hA.2.1]`. Simplify using the standard rewrite rules. Take `⟨seq, h0, hstep, hN⟩` from `hD hA T Mi hi hT hJ (W.χΓ W.gam) rfl hv cO hcO Y y hy hyΔ`. Establish `h` using `lifta_seq W T c hc cO (xList W T (Mmax n Mi) (Mmax n hi) Y) seq hstep`.

Rewrite `hN` using `[h, h0]`. Establish `hprod : ((xList W T (Mmax n Mi) (Mmax n hi) Y).map fun x => (Polynomial.X - Polynomial.C (cO x) : Polynomial O)).prod = ∏ x ∈ ((jumpSet W T (Mmax n Mi) (Mmax n hi)) ×ˢ Finset.Icc (1 : ℤ) Y).image (fun p : ℤ × ℤ => p.1 + p.2), (Polynomial.X - Polynomial.C (cO x) : Polynomial O)`. Unfold `xList`. Rewrite using `[← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]`. Rewrite `hN` using `[hprod]`.

Conclude with `hN`.
-/
theorem lifta_semiO (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : W.EE)
    (hc : algebraMap (LetA O n) W.EE W.π₀ * c = 1) (hA : CaseA W) (hD : coreDss W)
    (Mi hi : ZMod n → ℕ) (hT : IsCrys PD T.ρ) (hJ : JumpsLet W T Mi hi) (cO : ℤ → O)
    (hcO : ∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) (Y : ℕ)
    (y : W.DD T) (hy : qp W ^ Y • y ∈ W.N T) (hyΔ : ∀ δ ∈ W.DelF, W.γD T δ y = y) :
    Polynomial.aeval (lifta_δ W T c)
      (∏ x ∈ ((jumpSet W T (Mmax n Mi) (Mmax n hi)) ×ˢ Finset.Icc (1 : ℤ) Y).image
        (fun p : ℤ × ℤ => p.1 + p.2), (Polynomial.X - Polynomial.C (cO x) : Polynomial O)) y ∈
      W.N T := by
  have hv : v (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1)) = 1 := by
    rw [map_sub, map_one, W.gam_gen, hA.2.1]
    simp
  obtain ⟨seq, h0, hstep, hN⟩ := hD hA T Mi hi hT hJ (W.χΓ W.gam) rfl hv cO hcO Y y hy hyΔ
  have h := lifta_seq W T c hc cO (xList W T (Mmax n Mi) (Mmax n hi) Y) seq hstep
  rw [h, h0] at hN
  have hprod : ((xList W T (Mmax n Mi) (Mmax n hi) Y).map
      fun x => (Polynomial.X - Polynomial.C (cO x) : Polynomial O)).prod =
      ∏ x ∈ ((jumpSet W T (Mmax n Mi) (Mmax n hi)) ×ˢ Finset.Icc (1 : ℤ) Y).image
        (fun p : ℤ × ℤ => p.1 + p.2), (Polynomial.X - Polynomial.C (cO x) : Polynomial O) := by
    unfold xList
    rw [← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rw [hprod] at hN
  exact hN

end LiftADss

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LiftACore

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O]

open Polynomial Formalism.CoboundaryTransfers in

/- English proof (translation)
Establish `hprime : ℓ.Prime` using `Fact.out`. Establish `h3 : 3 ≤ ℓ` using `by have := hprime.two_le; omega`. Use `set u₁ : ℤ_[ℓ]ˣ := u ^ (ℓ - 1) with hu₁`. Establish `hu₁c : (u₁ : ℤ_[ℓ]) = (u : ℤ_[ℓ]) ^ (ℓ - 1)` using `by rw [hu₁, Units.val_pow_eq_pow_val]`. Establish `hγX₁ : B.GammaX (u₁ : ℤ_[ℓ])` using `by rw [hu₁c]; exact hγX`.

Establish `hv₁ : PadicInt.valuation ((u₁ : ℤ_[ℓ]) - 1) = 1`. Rewrite using `[hu₁c, Formalism.ResultantValuation.powSubOneValuation ℓ hℓ (u : ℤ_[ℓ]) hv (ℓ - 1) (by omega), padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))]`. Use `set a := M / (ℓ - 1) with ha`. Establish `hMa : M + 1 ≤ (ℓ - 1) * (a + 1)` using `Nat.lt_mul_div_succ M (by omega)`. Establish `h1` using `Formalism.RepresentationBoundsCohomology.N2.phi_map_surjective ℤ_[ℓ] A B M D₀ W₀ I (ℓ - 1) (a + 1) hPhi hMa hQI hφI`.

Establish `hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0` using `by exact_mod_cast hprime.ne_zero`. Establish `hc0 : c 0 = 0`. Use `hc 0` as an intermediate fact. Simplify using `only [neg_zero, zpow_zero, Units.val_one, sub_self, mul_eq_zero] at this`. Conclude with `this.resolve_left hℓ0`.

Establish `hstab : ∀ n ∈ W₀.N.restrictScalars ℤ_[ℓ], δ n ∈ W₀.N.restrictScalars ℤ_[ℓ]`. Introduce `n hn`. Take `⟨x', hx', h⟩` from `W₀.γ_N n hn`. Establish `: δ n = x'`. Establish `h0 : B.X • (δ n - x') = 0` using `by rw [smul_sub, hδ, h, sub_self]`.

Conclude with `sub_eq_zero.1 (W₀.X_inj _ h0)`. Rewrite using `[this]`. Conclude with `hx'`. Use `set R : ℤ_[ℓ][X] := ∏ j ∈ Formalism.RepresentationBoundsCohomology.N2.JSet jumps M, (X - C (c j)) with hRdef`. Establish `hR : ∀ y, W₀.QInv y → aeval δ (X * R) y ∈ W₀.N`.

Introduce `y hy`. Take `⟨R', hR'⟩` from `Formalism.RepresentationBoundsCohomology.N2.prod_eig_dvd jumps M (fun j => (X - C (c j)))`. Simplify using `only [hc0, map_zero, sub_zero] at hR'`. Rewrite using `[hRdef, hR', mul_comm, map_mul, Module.End.mul_apply]`. Conclude with `Formalism.RepresentationBoundsCohomology.N2.aeval_mem _ δ hstab R' _ (hSemi y hy)`.

Establish `hprod` using `Formalism.RepresentationBoundsCohomology.N2.prod_sub_one_dvd ℓ hℓ u₁ hv₁ a`. Establish `hZu : ∀ y, W₀.QInv y → (∏ i ∈ Finset.Icc 1 a, (1 - (u₁ : ℤ_[ℓ]) ^ i)) • y ∈ W₀.N → y ∈ W₀.N`. Introduce `y hy h`. Take `⟨w, hw⟩` from `hprod`. Apply `Formalism.RepresentationBoundsCohomology.N2.noTors_pow W₀ hZ _ y hy` to reduce the goal to its premises.

Rewrite using `[hw, mul_comm, mul_smul]`. Conclude with `W₀.smulO_mem w h`. Establish `hgr : ∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W₀.N, ∃ n' ∈ W₀.N, W₀.γ (B.X ^ i • n) = (u₁ : ℤ_[ℓ]) ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n'`. Introduce `i _ _ n hn`. Take `⟨n', hn', h⟩` from `gammaGradedStep_holds ℤ_[ℓ] A B M D₀ W₀ (u₁ : ℤ_[ℓ]) hγX₁ i n hn`.

Conclude with `⟨n', hn', by rw [← h]; abel⟩`. Establish `hL0` using `lift_wach ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S eW hCK hRS δ R a (ℓ - 1) (u₁ : ℤ_[ℓ]) hPhi (by omega) hδ hR (by rw [hp]; exact hZ) hZu hgr h1`. Establish `hcj : ∀ j ∈ Formalism.RepresentationBoundsCohomology.N2.JSet jumps M, (0 - c j) ∣ (ℓ : ℤ_[ℓ]) ^ padicValInt ℓ j`. Introduce `j hj`. Establish `hj0 : j ≠ 0` using `fun h => Formalism.RepresentationBoundsCohomology.N2.zero_notMem_JSet jumps M (h ▸ hj)`.

Take `⟨hne, hval⟩` from `Formalism.WindowSums.arc_ZpowVal ℓ u 1 le_rfl (fun h => absurd h hℓ) hv (-j) (neg_ne_zero.2 hj0)`. Establish `hneg : padicValInt ℓ (-j) = padicValInt ℓ j` using `by simp [padicValInt]`. Rewrite `hval` using `[hneg]`. Take `⟨w, hw⟩` from `Formalism.RepresentationBoundsCohomology.N2.dvd_pow_of_val hne hval`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Apply `mul_left_cancel₀ hℓ0` to reduce the goal to its premises. Establish `e : (ℓ : ℤ_[ℓ]) * ((0 - c j) * w) = (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) * w`. Use `hc j` as an intermediate fact. Take the linear combination `(-w) * this`. Rewrite using `[e, ← hw, pow_add, pow_one]`.

Establish `hR0 : R.eval 0 ∣ (ℓ : ℤ_[ℓ]) ^ (∑ j ∈ Formalism.RepresentationBoundsCohomology.N2.JSet jumps M, padicValInt ℓ j)`. Rewrite using `[hRdef, eval_prod, ← Finset.prod_pow_eq_pow_sum]`. Apply `Finset.prod_dvd_prod_of_dvd` to reduce the goal to its premises. Introduce `j hj`. Simplify using `using hcj j hj`.

Establish `hfac : a + padicValNat ℓ a.factorial ≤ Formalism.RepresentationBoundsCohomology.N2.aStar ℓ M + padicValNat ℓ (Formalism.RepresentationBoundsCohomology.N2.aStar ℓ M).factorial`. Establish `: padicValNat ℓ (a + 1).factorial = padicValNat ℓ (a + 1) + padicValNat ℓ a.factorial`. Rewrite using `[Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero a) (Nat.factorial_ne_zero _)]`. Simplify using `only [Formalism.RepresentationBoundsCohomology.N2.aStar, ← ha]`. Use linear arithmetic over natural numbers and integers.

Use `Formalism.RepresentationBoundsCohomology.N2.lifts_of_dvd S ?_ hL0` and prove the remaining obligations. Rewrite using `[hp, pow_add]`. Apply `mul_dvd_mul_left` to reduce the goal to its premises. Simplify using `only [Formalism.RepresentationBoundsCohomology.N2.eUA]`. Rewrite using `[add_assoc, pow_add]`.

Conclude with `mul_dvd_mul hR0 (dvd_trans hprod (pow_dvd_pow _ hfac))`.
-/
theorem lifta_core (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) (A : Type) [CommRing A] [Algebra ℤ_[ℓ] A]
    (B : Base ℤ_[ℓ] A) (M : ℕ) (u : ℤ_[ℓ]ˣ) (jumps : Finset ℤ) (c : ℤ → ℤ_[ℓ])
    (hp : B.p = ℓ) (hPhi : B.PhiX (ℓ - 1)) (hγX : B.GammaX ((u : ℤ_[ℓ]) ^ (ℓ - 1)))
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1)
    (hc : ∀ j : ℤ, (ℓ : ℤ_[ℓ]) * c j = 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]))
    (D₀ D₁ D₂ : Type)
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    (W₀ : WachMod B M D₀) (W₁ : WachMod B M D₁) (W₂ : WachMod B M D₂) (S : SES W₀ W₁ W₂)
    (δ : D₀ →ₗ[ℤ_[ℓ]] D₀) (I : Ideal A) [IsAdicComplete I W₀.N]
    (hδ : ∀ y, B.X • δ y = W₀.γ y - y) (hQI : B.Q ∈ I) (hφI : ∀ a ∈ I, B.φ a ∈ I)
    (hZ : ∀ y, W₀.QInv y → (ℓ : ℤ_[ℓ]) • y ∈ W₀.N → y ∈ W₀.N)
    (hSemi : Formalism.RepresentationBoundsCohomology.N2.SemiA W₀ δ c jumps) (eW : ℕ) (hCK : CokerKilled S eW) (hRS : RatSurj S) :
    Lifts S ((ℓ : ℤ_[ℓ]) ^ (eW + Formalism.RepresentationBoundsCohomology.N2.eUA ℓ M (Formalism.RepresentationBoundsCohomology.N2.JSet jumps M))) := by
  have hprime : ℓ.Prime := Fact.out
  have h3 : 3 ≤ ℓ := by have := hprime.two_le; omega
  set u₁ : ℤ_[ℓ]ˣ := u ^ (ℓ - 1) with hu₁
  have hu₁c : (u₁ : ℤ_[ℓ]) = (u : ℤ_[ℓ]) ^ (ℓ - 1) := by rw [hu₁, Units.val_pow_eq_pow_val]
  have hγX₁ : B.GammaX (u₁ : ℤ_[ℓ]) := by rw [hu₁c]; exact hγX
  have hv₁ : PadicInt.valuation ((u₁ : ℤ_[ℓ]) - 1) = 1 := by
    rw [hu₁c, Formalism.ResultantValuation.powSubOneValuation ℓ hℓ (u : ℤ_[ℓ]) hv (ℓ - 1) (by omega),
      padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))]
  set a := M / (ℓ - 1) with ha
  have hMa : M + 1 ≤ (ℓ - 1) * (a + 1) := Nat.lt_mul_div_succ M (by omega)
  have h1 := Formalism.RepresentationBoundsCohomology.N2.phi_map_surjective ℤ_[ℓ] A B M D₀ W₀ I (ℓ - 1) (a + 1) hPhi hMa hQI hφI
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hc0 : c 0 = 0 := by
    have := hc 0
    simp only [neg_zero, zpow_zero, Units.val_one, sub_self, mul_eq_zero] at this
    exact this.resolve_left hℓ0
  have hstab : ∀ n ∈ W₀.N.restrictScalars ℤ_[ℓ], δ n ∈ W₀.N.restrictScalars ℤ_[ℓ] := by
    intro n hn
    obtain ⟨x', hx', h⟩ := W₀.γ_N n hn
    have : δ n = x' := by
      have h0 : B.X • (δ n - x') = 0 := by rw [smul_sub, hδ, h, sub_self]
      exact sub_eq_zero.1 (W₀.X_inj _ h0)
    rw [this]; exact hx'
  set R : ℤ_[ℓ][X] := ∏ j ∈ Formalism.RepresentationBoundsCohomology.N2.JSet jumps M, (X - C (c j)) with hRdef
  have hR : ∀ y, W₀.QInv y → aeval δ (X * R) y ∈ W₀.N := by
    intro y hy
    obtain ⟨R', hR'⟩ := Formalism.RepresentationBoundsCohomology.N2.prod_eig_dvd jumps M (fun j => (X - C (c j)))
    simp only [hc0, map_zero, sub_zero] at hR'
    rw [hRdef, hR', mul_comm, map_mul, Module.End.mul_apply]
    exact Formalism.RepresentationBoundsCohomology.N2.aeval_mem _ δ hstab R' _ (hSemi y hy)
  have hprod := Formalism.RepresentationBoundsCohomology.N2.prod_sub_one_dvd ℓ hℓ u₁ hv₁ a
  have hZu : ∀ y, W₀.QInv y → (∏ i ∈ Finset.Icc 1 a, (1 - (u₁ : ℤ_[ℓ]) ^ i)) • y ∈ W₀.N → y ∈ W₀.N := by
    intro y hy h
    obtain ⟨w, hw⟩ := hprod
    apply Formalism.RepresentationBoundsCohomology.N2.noTors_pow W₀ hZ _ y hy
    rw [hw, mul_comm, mul_smul]
    exact W₀.smulO_mem w h
  have hgr : ∀ i, 1 ≤ i → i ≤ a → ∀ n ∈ W₀.N, ∃ n' ∈ W₀.N,
      W₀.γ (B.X ^ i • n) = (u₁ : ℤ_[ℓ]) ^ i • (B.X ^ i • n) + B.X ^ (i + 1) • n' := by
    intro i _ _ n hn
    obtain ⟨n', hn', h⟩ := gammaGradedStep_holds ℤ_[ℓ] A B M D₀ W₀ (u₁ : ℤ_[ℓ]) hγX₁ i n hn
    exact ⟨n', hn', by rw [← h]; abel⟩
  have hL0 := lift_wach ℤ_[ℓ] A B M D₀ D₁ D₂ W₀ W₁ W₂ S eW hCK hRS δ R a (ℓ - 1) (u₁ : ℤ_[ℓ]) hPhi
    (by omega) hδ hR (by rw [hp]; exact hZ) hZu hgr h1
  have hcj : ∀ j ∈ Formalism.RepresentationBoundsCohomology.N2.JSet jumps M, (0 - c j) ∣ (ℓ : ℤ_[ℓ]) ^ padicValInt ℓ j := by
    intro j hj
    have hj0 : j ≠ 0 := fun h => Formalism.RepresentationBoundsCohomology.N2.zero_notMem_JSet jumps M (h ▸ hj)
    obtain ⟨hne, hval⟩ := Formalism.WindowSums.arc_ZpowVal ℓ u 1 le_rfl (fun h => absurd h hℓ) hv (-j)
      (neg_ne_zero.2 hj0)
    have hneg : padicValInt ℓ (-j) = padicValInt ℓ j := by simp [padicValInt]
    rw [hneg] at hval
    obtain ⟨w, hw⟩ := Formalism.RepresentationBoundsCohomology.N2.dvd_pow_of_val hne hval
    refine ⟨w, ?_⟩
    apply mul_left_cancel₀ hℓ0
    have e : (ℓ : ℤ_[ℓ]) * ((0 - c j) * w) = (((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) * w := by
      have := hc j
      linear_combination (-w) * this
    rw [e, ← hw, pow_add, pow_one]
  have hR0 : R.eval 0 ∣ (ℓ : ℤ_[ℓ]) ^ (∑ j ∈ Formalism.RepresentationBoundsCohomology.N2.JSet jumps M, padicValInt ℓ j) := by
    rw [hRdef, eval_prod, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_dvd_prod_of_dvd
    intro j hj
    simpa using hcj j hj
  have hfac : a + padicValNat ℓ a.factorial ≤
      Formalism.RepresentationBoundsCohomology.N2.aStar ℓ M + padicValNat ℓ (Formalism.RepresentationBoundsCohomology.N2.aStar ℓ M).factorial := by
    have : padicValNat ℓ (a + 1).factorial = padicValNat ℓ (a + 1) + padicValNat ℓ a.factorial := by
      rw [Nat.factorial_succ, padicValNat.mul (Nat.succ_ne_zero a) (Nat.factorial_ne_zero _)]
    simp only [Formalism.RepresentationBoundsCohomology.N2.aStar, ← ha]
    omega
  refine Formalism.RepresentationBoundsCohomology.N2.lifts_of_dvd S ?_ hL0
  rw [hp, pow_add]
  apply mul_dvd_mul_left
  simp only [Formalism.RepresentationBoundsCohomology.N2.eUA]
  rw [add_assoc, pow_add]
  exact mul_dvd_mul hR0 (dvd_trans hprod (pow_dvd_pow _ hfac))

end LiftACore

section LiftALocal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O]

attribute [local instance] liftb_modZ liftb_towZO liftb_towZA

/- English proof (translation)
Apply `W.EE_inj` to reduce the goal to its premises. Apply `h.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[← map_mul, ← map_mul, hxy]`.
-/
theorem lifta_reg (W : LocWach PD LL O v n) (a x y : LetA O n)
    (h : IsUnit (algebraMap (LetA O n) W.EE a)) (hxy : a * x = a * y) : x = y := by
  apply W.EE_inj
  apply h.mul_left_cancel
  rw [← map_mul, ← map_mul, hxy]

structure lifta_Ring (W : LocWach PD LL O v n) : Prop where
  πΔ : W.π₀ ∈ W.AΔ
  πU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)
  qU : IsUnit (algebraMap (LetA O n) W.EE (qp W))
  ππ : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)
  qq : ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * qp W
  φπ : ∃ t ∈ W.AΔ, W.φA W.π₀ = W.π₀ * qp W ^ (PD.p - 1) * t
  γπ : ∃ t ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * (algebraMap O (LetA O n) (u₁ W) + W.π₀ * t)
  γq : ∃ t ∈ W.AΔ, W.γA W.gam (qp W) = (1 + W.π₀ * t) * qp W

/- English proof (translation)
The claim follows from `W.AΔ.add_mem hπ (natCast_mem W.AΔ PD.p)`.
-/
theorem lifta_qΔ (W : LocWach PD LL O v n) (hπ : W.π₀ ∈ W.AΔ) : qp W ∈ W.AΔ :=
  W.AΔ.add_mem hπ (natCast_mem W.AΔ PD.p)

/- English proof (translation)
Introduce `δ hδ` and use `by rw [← W.φA_γA, ha δ hδ]`.
-/
theorem lifta_φΔ (W : LocWach PD LL O v n) (a : LetA O n) (ha : a ∈ W.AΔ) : W.φA a ∈ W.AΔ :=
  fun δ hδ => by rw [← W.φA_γA, ha δ hδ]

/- English proof (translation)
Introduce `δ hδ` and use `by rw [gammaA_comm, ha δ hδ]`.
-/
theorem lifta_γΔ (W : LocWach PD LL O v n) (g : W.Gam) (a : LetA O n) (ha : a ∈ W.AΔ) :
    W.γA g a ∈ W.AΔ :=
  fun δ hδ => by rw [gammaA_comm, ha δ hδ]

/- English proof (translation)
Introduce `δ hδ`. Apply `lifta_reg W a _ _ hU` to reduce the goal to its premises. Use `hat δ hδ` as an intermediate fact. Rewrite `this` using `[map_mul, ha δ hδ]`. Conclude with `this`.
-/
theorem lifta_divΔ (W : LocWach PD LL O v n) (a t : LetA O n) (ha : a ∈ W.AΔ)
    (hU : IsUnit (algebraMap (LetA O n) W.EE a)) (hat : a * t ∈ W.AΔ) : t ∈ W.AΔ := by
  intro δ hδ
  apply lifta_reg W a _ _ hU
  have := hat δ hδ
  rw [map_mul, ha δ hδ] at this
  exact this

/- English proof (translation)
Establish `hπΔ : W.π₀ ∈ W.AΔ` using `h9.1`. Take `⟨w, hw⟩` from `h9.2.2.1`. Take `⟨wq, hwq⟩` from `h9.2.2.2.2.1`. Take `⟨wγ, hwγ⟩` from `h9.2.2.2.2.2.2.1`. Rewrite `hwq`, `hwγ` using `[eisenstein_at_uniformizer]`.

Establish `hUA : ∀ z : (LetA O n)ˣ, IsUnit (algebraMap (LetA O n) W.EE (z : LetA O n))` using `fun z => z.isUnit.map _`. Establish `hπU : IsUnit (algebraMap (LetA O n) W.EE W.π₀)`. Rewrite using `[hw, map_mul, map_pow]`. Conclude with `(hUA w).mul (W.EE_π.pow _)`. Establish `hqU : IsUnit (algebraMap (LetA O n) W.EE (qp W))`.

Establish `h1 : IsUnit (algebraMap (LetA O n) W.EE W.q)` using `liftb_q_unit W`. Rewrite `h1` using `[hwq, map_mul]`. Conclude with `isUnit_of_mul_isUnit_right h1`. Establish `hqΔ` using `lifta_qΔ W hπΔ`. Take `⟨wφ, hwφ⟩` from `pullback_projection_frobenius W h9`.

Use `⟨hπΔ, hπU, hqU, ⟨w, hw⟩, ⟨wq, hwq⟩, ⟨wφ, ?_, by rw [hwφ]; ring⟩, gamma_uniformizer_eq_mul_unit' W h9, ⟨wγ, ?_, ?_⟩⟩` and prove the remaining obligations. Apply `lifta_divΔ W (W.π₀ * qp W ^ (PD.p - 1)) _ (W.AΔ.mul_mem hπΔ (W.AΔ.pow_mem hqΔ _)) (by rw [map_mul, map_pow]; exact hπU.mul (hqU.pow _))` to reduce the goal to its premises. Establish `: W.π₀ * qp W ^ (PD.p - 1) * (wφ : LetA O n) = W.φA W.π₀` using `by rw [hwφ]; ring`. Rewrite using `[this]`. Conclude with `lifta_φΔ W _ hπΔ`.

Apply `lifta_divΔ W (W.π₀ * qp W) _ (W.AΔ.mul_mem hπΔ hqΔ) (by rw [map_mul]; exact hπU.mul hqU)` to reduce the goal to its premises. Establish `: W.π₀ * qp W * (wγ : LetA O n) = W.γA W.gam W.π₀ - W.π₀` using `by rw [hwγ]; ring`. Rewrite using `[this]`. Conclude with `W.AΔ.sub_mem (lifta_γΔ W _ _ hπΔ) hπΔ`. Establish `h1 : W.γA W.gam (qp W) = W.γA W.gam W.π₀ + ((PD.p : ℕ) : LetA O n)`.

Rewrite using `[qp, map_add, map_natCast]`. Establish `h2 : W.γA W.gam W.π₀ = W.π₀ + (wγ : LetA O n) * W.π₀ * qp W` using `by rw [← hwγ]; ring`. Rewrite using `[h1, h2]`. Simplify using `only [qp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lifta_ring_of (W : LocWach PD LL O v n) (h9 : P9π₀ W) : lifta_Ring W := by
  have hπΔ : W.π₀ ∈ W.AΔ := h9.1
  obtain ⟨w, hw⟩ := h9.2.2.1
  obtain ⟨wq, hwq⟩ := h9.2.2.2.2.1
  obtain ⟨wγ, hwγ⟩ := h9.2.2.2.2.2.2.1
  rw [eisenstein_at_uniformizer] at hwq hwγ
  have hUA : ∀ z : (LetA O n)ˣ, IsUnit (algebraMap (LetA O n) W.EE (z : LetA O n)) :=
    fun z => z.isUnit.map _
  have hπU : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw, map_mul, map_pow]
    exact (hUA w).mul (W.EE_π.pow _)
  have hqU : IsUnit (algebraMap (LetA O n) W.EE (qp W)) := by
    have h1 : IsUnit (algebraMap (LetA O n) W.EE W.q) := liftb_q_unit W
    rw [hwq, map_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  have hqΔ := lifta_qΔ W hπΔ
  obtain ⟨wφ, hwφ⟩ := pullback_projection_frobenius W h9
  refine ⟨hπΔ, hπU, hqU, ⟨w, hw⟩, ⟨wq, hwq⟩, ⟨wφ, ?_, by rw [hwφ]; ring⟩, gamma_uniformizer_eq_mul_unit' W h9,
    ⟨wγ, ?_, ?_⟩⟩
  · apply lifta_divΔ W (W.π₀ * qp W ^ (PD.p - 1)) _ (W.AΔ.mul_mem hπΔ (W.AΔ.pow_mem hqΔ _))
      (by rw [map_mul, map_pow]; exact hπU.mul (hqU.pow _))
    have : W.π₀ * qp W ^ (PD.p - 1) * (wφ : LetA O n) = W.φA W.π₀ := by rw [hwφ]; ring
    rw [this]
    exact lifta_φΔ W _ hπΔ
  · apply lifta_divΔ W (W.π₀ * qp W) _ (W.AΔ.mul_mem hπΔ hqΔ) (by rw [map_mul]; exact hπU.mul hqU)
    have : W.π₀ * qp W * (wγ : LetA O n) = W.γA W.gam W.π₀ - W.π₀ := by rw [hwγ]; ring
    rw [this]
    exact W.AΔ.sub_mem (lifta_γΔ W _ _ hπΔ) hπΔ
  · have h1 : W.γA W.gam (qp W) = W.γA W.gam W.π₀ + ((PD.p : ℕ) : LetA O n) := by
      rw [qp, map_add, map_natCast]
    have h2 : W.γA W.gam W.π₀ = W.π₀ + (wγ : LetA O n) * W.π₀ * qp W := by rw [← hwγ]; ring
    rw [h1, h2]
    simp only [qp]
    ring

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun z a x => smul_assoc z (a : LetA O n) x⟩`.
-/
theorem lifta_towZ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    IsScalarTower ℤ_[ℓ] ↥W.AΔ (W.DD T) :=
  ⟨fun z a x => smul_assoc z (a : LetA O n) x⟩

attribute [local instance] lifta_towZ

def lifta_φ₀ (W : LocWach PD LL O v n) : ↥W.AΔ →ₐ[O] ↥W.AΔ :=
  (W.φA.comp W.AΔ.val).codRestrict W.AΔ (fun a => lifta_φΔ W a a.2)

def lifta_γ₀ (W : LocWach PD LL O v n) : ↥W.AΔ →ₐ[O] ↥W.AΔ :=
  ((W.γA W.gam).comp W.AΔ.val).codRestrict W.AΔ (fun a => lifta_γΔ W W.gam a a.2)

def lifta_base (W : LocWach PD LL O v n) (R : lifta_Ring W) : Formalism.CoboundaryTransfers.Base ℤ_[ℓ] ↥W.AΔ where
  p := PD.p
  hp := PD.hp
  φ := (lifta_φ₀ W).restrictScalars ℤ_[ℓ]
  γ := (lifta_γ₀ W).restrictScalars ℤ_[ℓ]
  X := ⟨W.π₀, R.πΔ⟩
  Q := ⟨qp W, lifta_qΔ W R.πΔ⟩
  comm := fun a => Subtype.ext (W.φA_γA W.gam a)
  φX := by
    obtain ⟨t, ht, h⟩ := R.φπ
    exact ⟨⟨qp W ^ (PD.p - 1) * t, W.AΔ.mul_mem (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) _) ht⟩,
      Subtype.ext (h.trans (mul_assoc _ _ _))⟩

def lifta_N (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Submodule ↥W.AΔ (W.DD T) where
  carrier := {x | x ∈ W.NΔ T}
  add_mem' := fun ha hb => (W.NΔ T).add_mem ha hb
  zero_mem' := (W.NΔ T).zero_mem
  smul_mem' := fun a x hx => invariant_smul_mem_invariants' W T a a.2 x hx

structure lifta_Good (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (M : ℕ) : Prop where
  φN : ∀ x ∈ W.NΔ T, qp W ^ M • W.φD T x ∈ W.NΔ T
  γN : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T x - x = W.π₀ • x'
  γQN : ∀ y : W.DD T, qp W ^ M • y ∈ W.NΔ T →
    ∃ y' : W.DD T, qp W ^ M • y' ∈ W.NΔ T ∧ W.γ T y - y = W.π₀ • y'

  crys : IsCrys PD T.ρ

def lifta_wach (W : LocWach PD LL O v n) (R : lifta_Ring W) (T : LocLat G Qp LL O) (M : ℕ)
    (g : lifta_Good W T M) : Formalism.CoboundaryTransfers.WachMod (lifta_base (ℓ := ℓ) W R) M (W.DD T) where
  N := lifta_N W T
  φ := (W.φD T).restrictScalars ℤ_[ℓ]
  γ := (W.γ T).restrictScalars ℤ_[ℓ]
  φ_smul := fun a x => liftb_φ_smul W T (a : LetA O n) x
  γ_smul := fun a x => liftb_γ_smul W T (a : LetA O n) x
  comm := fun x => W.φγ_comm T W.gam x
  X_inj := fun x hx => (liftb_unit_bij W T W.π₀ R.πU).1 (by
    change W.π₀ • x = W.π₀ • (0 : W.DD T)
    rw [smul_zero]; exact hx)
  Q_bij := liftb_unit_bij W T (qp W) R.qU
  φ_N := g.φN
  γ_N := g.γN
  γ_QN := g.γQN

def lifta_hom (W : LocWach PD LL O v n) (R : lifta_Ring W) {T T' : LocLat G Qp LL O}
    (F : LatHom T.L T'.L) (M : ℕ) (g : lifta_Good W T M) (g' : lifta_Good W T' M) :
    Formalism.CoboundaryTransfers.Hom (lifta_wach (ℓ := ℓ) W R T M g) (lifta_wach (ℓ := ℓ) W R T' M g') where
  f := ((W.map F).restrictScalars (LetA O n)).restrictScalars ↥W.AΔ
  φ_comm := W.map_φ F
  γ_comm := fun x => W.map_γ F W.gam x
  N_le := fun x hx => ⟨W.map_N F g.crys g'.crys x hx.1, fun δ hδ => by
    change W.γD T' δ (W.map F x) = W.map F x
    rw [← W.map_γ, hx.2 δ hδ]⟩

def lifta_ses (W : LocWach PD LL O v n) (R : lifta_Ring W) {T₀ T₁ T₂ : LocLat G Qp LL O}
    (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L) (M : ℕ) (g₀ : lifta_Good W T₀ M)
    (g₁ : lifta_Good W T₁ M) (g₂ : lifta_Good W T₂ M) (hE : liftb_DDExact W ι π)
    (hsat : ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) :
    Formalism.CoboundaryTransfers.SES (lifta_wach (ℓ := ℓ) W R T₀ M g₀) (lifta_wach (ℓ := ℓ) W R T₁ M g₁)
      (lifta_wach (ℓ := ℓ) W R T₂ M g₂) where
  ι := lifta_hom W R ι M g₀ g₁
  π := lifta_hom W R π M g₁ g₂
  ι_inj := hE.1
  exact := hE.2
  sat := fun x hx => ⟨hsat x hx.1, fun δ hδ => hE.1 (by rw [W.map_γ]; exact hx.2 δ hδ)⟩

/- English proof (translation)
The claim follows from `liftb_unit_bij W T (qp W ^ M) (by rw [map_pow]; exact R.qU.pow M)`.
-/
theorem lifta_qpow_bij (W : LocWach PD LL O v n) (R : lifta_Ring W) (T : LocLat G Qp LL O) (M : ℕ) :
    Function.Bijective (fun x : W.DD T => qp W ^ M • x) :=
  liftb_unit_bij W T (qp W ^ M) (by rw [map_pow]; exact R.qU.pow M)

/- English proof (translation)
Introduce `δ hδ`. Apply `(lifta_qpow_bij W R T M).1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `qp W ^ M • W.γD T δ y = qp W ^ M • y`. Establish `h` using `hy δ hδ`. Rewrite `h` using `[gammaD_semilinear, (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) M) δ hδ]`.

Conclude with `h`.
-/
theorem lifta_inv_of_q (W : LocWach PD LL O v n) (R : lifta_Ring W) (T : LocLat G Qp LL O) (M : ℕ)
    (y : W.DD T) (hy : ∀ δ ∈ W.DelF, W.γD T δ (qp W ^ M • y) = qp W ^ M • y) :
    ∀ δ ∈ W.DelF, W.γD T δ y = y := by
  intro δ hδ
  apply (lifta_qpow_bij W R T M).1
  change qp W ^ M • W.γD T δ y = qp W ^ M • y
  have h := hy δ hδ
  rw [gammaD_semilinear, (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) M) δ hδ] at h
  exact h

/- English proof (translation)
Unfold `LocWach.Q`. Rewrite using `[hs]`. Both sides reduce to the same expression.
-/
theorem lifta_Q_eq (W : LocWach PD LL O v n) (hs : W.s = 1) : W.Q = W.q := by
  unfold LocWach.Q
  rw [hs]
  rfl

/- English proof (translation)
Unfold `LocWach.X`. Rewrite using `[hs]`. Both sides reduce to the same expression.
-/
theorem lifta_X_eq (W : LocWach PD LL O v n) (hs : W.s = 1) : W.X = letπ := by
  unfold LocWach.X
  rw [hs]
  rfl

/- English proof (translation)
Take `⟨w, hw⟩` from `R.qq`. Rewrite using `[lifta_Q_eq W hs, hw, mul_pow, mul_smul]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(W.N T).smul_mem (((w⁻¹ : (LetA O n)ˣ) : LetA O n) ^ M) h` as an intermediate fact.

Rewrite `this` using `[smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]`. Then use the resulting hypothesis. Introduce `h`. Conclude with `(W.N T).smul_mem _ h`.
-/
theorem lifta_Qq (W : LocWach PD LL O v n) (R : lifta_Ring W) (hs : W.s = 1)
    (T : LocLat G Qp LL O) (M : ℕ) (y : W.DD T) : W.Q ^ M • y ∈ W.N T ↔ qp W ^ M • y ∈ W.N T := by
  obtain ⟨w, hw⟩ := R.qq
  rw [lifta_Q_eq W hs, hw, mul_pow, mul_smul]
  constructor
  · intro h
    have := (W.N T).smul_mem (((w⁻¹ : (LetA O n)ˣ) : LetA O n) ^ M) h
    rwa [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at this
  · intro h
    exact (W.N T).smul_mem _ h

/- English proof (translation)
Establish `hqΔ` using `lifta_qΔ W R.πΔ`. Use `⟨?_, hm.2, ?_, g.crys⟩` and prove the remaining obligations. Introduce `x hx`. Use `⟨(lifta_Qq W R hs T M _).1 (g.φN x hx.1), fun δ hδ => ?_⟩` and prove the remaining obligations. Rewrite using `[gammaD_semilinear, (W.AΔ.pow_mem hqΔ M) δ hδ, ← W.φγ_comm, hx.2 δ hδ]`.

Introduce `y hy`. Take `⟨t, htΔ, hw⟩` from `R.γq`. Take `⟨wπ, hwπ⟩` from `R.ππ`. Establish `hp1 : PD.p - 1 = (PD.p - 2) + 1` using `by have := PD.hp.two_le; omega`. Establish `hvΔ : 1 + W.π₀ * t ∈ W.AΔ` using `W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem R.πΔ htΔ)`.

Establish `hwU : IsUnit (1 + W.π₀ * t)`. Establish `: 1 + W.π₀ * t = 1 + W.X * ((wπ : LetA O n) * letπ ^ (PD.p - 2) * t)`. Rewrite using `[lifta_X_eq W hs, hwπ, hp1, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `liftb_one_add_X_unit W _`. Take `⟨wi, hwi⟩` from `(hwU.pow M).exists_left_inv`. Establish `hwiΔ : wi ∈ W.AΔ`. Apply `lifta_divΔ W ((1 + W.π₀ * t) ^ M) wi (W.AΔ.pow_mem hvΔ M) ((hwU.pow M).map _)` to reduce the goal to its premises. Rewrite using `[mul_comm, hwi]`.

Conclude with `W.AΔ.one_mem`. Use `set c0 := ∑ i ∈ Finset.range M, (1 + W.π₀ * t) ^ i with hc0def`. Establish `hc0Δ : c0 ∈ W.AΔ` using `W.AΔ.sum_mem (fun i _ => W.AΔ.pow_mem hvΔ i)`. Establish `hc0 : (1 + W.π₀ * t) ^ M - 1 = c0 * (W.π₀ * t)`. Use `geom_sum_mul (1 + W.π₀ * t) M` as an intermediate fact.

Rewrite using `[← this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : wi = 1 + W.π₀ * (-(wi * t * c0))`. Establish `h1 : wi - 1 = -(wi * ((1 + W.π₀ * t) ^ M - 1))` using `by rw [mul_sub, hwi]; ring`. Establish `h2 : wi = 1 + -(wi * ((1 + W.π₀ * t) ^ M - 1))` using `by rw [← h1]; ring`.

Rewrite `h2` using `[hc0]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨n', hn', hγ⟩` from `hm.2 (qp W ^ M • y) hy`. Establish `e1 : W.γ T (qp W ^ M • y) = ((1 + W.π₀ * t) ^ M * qp W ^ M) • W.γ T y`. Rewrite using `[liftb_γ_smul, map_pow, hw, mul_pow]`.

Establish `e2 : qp W ^ M • W.γ T y = wi • (qp W ^ M • y + W.π₀ • n')`. Establish `: W.γ T (qp W ^ M • y) = qp W ^ M • y + W.π₀ • n'` using `by rw [← hγ]; abel`. Rewrite using `[← this, e1, smul_smul, ← mul_assoc, hwi, one_mul]`. Use `set c := -(wi * t * c0) with hcdef`. Establish `hcΔ : c ∈ W.AΔ` using `W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hwiΔ htΔ) hc0Δ)`.

Establish `hn'' : c • (qp W ^ M • y) + wi • n' ∈ W.NΔ T` using `(W.NΔ T).add_mem (invariant_smul_mem_invariants' W T c hcΔ _ hy) (invariant_smul_mem_invariants' W T wi hwiΔ _ hn')`. Establish `hbij` using `lifta_qpow_bij W R T M`. Take `⟨y', hy'⟩` from `hbij.2 (c • (qp W ^ M • y) + wi • n')`. Establish `hy'' : qp W ^ M • y' = c • (qp W ^ M • y) + wi • n'` using `hy'`. Use `⟨y', by rw [hy'']; exact hn'', ?_⟩` and prove the remaining obligations.

Apply `hbij.1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `qp W ^ M • (W.γ T y - y) = qp W ^ M • (W.π₀ • y')`. Rewrite using `[smul_comm (qp W ^ M) W.π₀ y', hy'', smul_sub, e2]`. Establish `e3 : wi • (qp W ^ M • y + W.π₀ • n') = (1 + W.π₀ * c) • (qp W ^ M • y) + W.π₀ • (wi • n')`. Rewrite using `[← hc, smul_add, smul_comm wi W.π₀ n']`.

Rewrite using `[e3, add_smul, one_smul, mul_smul, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem lifta_good_of (W : LocWach PD LL O v n) (R : lifta_Ring W) (hs : W.s = 1)
    (T : LocLat G Qp LL O) (M : ℕ) (g : liftb_Good W T M) (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) :
    lifta_Good W T M := by
  have hqΔ := lifta_qΔ W R.πΔ
  refine ⟨?_, hm.2, ?_, g.crys⟩
  · intro x hx
    refine ⟨(lifta_Qq W R hs T M _).1 (g.φN x hx.1), fun δ hδ => ?_⟩
    rw [gammaD_semilinear, (W.AΔ.pow_mem hqΔ M) δ hδ, ← W.φγ_comm, hx.2 δ hδ]
  · intro y hy
    obtain ⟨t, htΔ, hw⟩ := R.γq
    obtain ⟨wπ, hwπ⟩ := R.ππ
    have hp1 : PD.p - 1 = (PD.p - 2) + 1 := by have := PD.hp.two_le; omega
    have hvΔ : 1 + W.π₀ * t ∈ W.AΔ := W.AΔ.add_mem W.AΔ.one_mem (W.AΔ.mul_mem R.πΔ htΔ)
    have hwU : IsUnit (1 + W.π₀ * t) := by
      have : 1 + W.π₀ * t = 1 + W.X * ((wπ : LetA O n) * letπ ^ (PD.p - 2) * t) := by
        rw [lifta_X_eq W hs, hwπ, hp1, pow_succ]; ring
      rw [this]
      exact liftb_one_add_X_unit W _
    obtain ⟨wi, hwi⟩ := (hwU.pow M).exists_left_inv
    have hwiΔ : wi ∈ W.AΔ := by
      apply lifta_divΔ W ((1 + W.π₀ * t) ^ M) wi (W.AΔ.pow_mem hvΔ M) ((hwU.pow M).map _)
      rw [mul_comm, hwi]
      exact W.AΔ.one_mem
    set c0 := ∑ i ∈ Finset.range M, (1 + W.π₀ * t) ^ i with hc0def
    have hc0Δ : c0 ∈ W.AΔ := W.AΔ.sum_mem (fun i _ => W.AΔ.pow_mem hvΔ i)
    have hc0 : (1 + W.π₀ * t) ^ M - 1 = c0 * (W.π₀ * t) := by
      have := geom_sum_mul (1 + W.π₀ * t) M
      rw [← this]
      ring
    have hc : wi = 1 + W.π₀ * (-(wi * t * c0)) := by
      have h1 : wi - 1 = -(wi * ((1 + W.π₀ * t) ^ M - 1)) := by rw [mul_sub, hwi]; ring
      have h2 : wi = 1 + -(wi * ((1 + W.π₀ * t) ^ M - 1)) := by rw [← h1]; ring
      rw [hc0] at h2
      calc wi = 1 + -(wi * (c0 * (W.π₀ * t))) := h2
        _ = 1 + W.π₀ * (-(wi * t * c0)) := by ring
    obtain ⟨n', hn', hγ⟩ := hm.2 (qp W ^ M • y) hy
    have e1 : W.γ T (qp W ^ M • y) = ((1 + W.π₀ * t) ^ M * qp W ^ M) • W.γ T y := by
      rw [liftb_γ_smul, map_pow, hw, mul_pow]
    have e2 : qp W ^ M • W.γ T y = wi • (qp W ^ M • y + W.π₀ • n') := by
      have : W.γ T (qp W ^ M • y) = qp W ^ M • y + W.π₀ • n' := by rw [← hγ]; abel
      rw [← this, e1, smul_smul, ← mul_assoc, hwi, one_mul]
    set c := -(wi * t * c0) with hcdef
    have hcΔ : c ∈ W.AΔ := W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.mul_mem hwiΔ htΔ) hc0Δ)
    have hn'' : c • (qp W ^ M • y) + wi • n' ∈ W.NΔ T :=
      (W.NΔ T).add_mem (invariant_smul_mem_invariants' W T c hcΔ _ hy) (invariant_smul_mem_invariants' W T wi hwiΔ _ hn')
    have hbij := lifta_qpow_bij W R T M
    obtain ⟨y', hy'⟩ := hbij.2 (c • (qp W ^ M • y) + wi • n')
    have hy'' : qp W ^ M • y' = c • (qp W ^ M • y) + wi • n' := hy'
    refine ⟨y', by rw [hy'']; exact hn'', ?_⟩
    apply hbij.1
    change qp W ^ M • (W.γ T y - y) = qp W ^ M • (W.π₀ • y')
    rw [smul_comm (qp W ^ M) W.π₀ y', hy'', smul_sub, e2]
    have e3 : wi • (qp W ^ M • y + W.π₀ • n') =
        (1 + W.π₀ * c) • (qp W ^ M • y) + W.π₀ • (wi • n') := by
      rw [← hc, smul_add, smul_comm wi W.π₀ n']
    rw [e3, add_smul, one_smul, mul_smul, smul_add]
    abel

/- English proof (translation)
Assemble the required witnesses or components as `⟨W.map_N F hT hT' x hx.1, fun δ hδ => by rw [← W.map_γ, hx.2 δ hδ]⟩`.
-/
theorem lifta_map_NΔ (W : LocWach PD LL O v n) {T T' : LocLat G Qp LL O} (F : LatHom T.L T'.L)
    (hT : IsCrys PD T.ρ) (hT' : IsCrys PD T'.ρ) (x : W.DD T) (hx : x ∈ W.NΔ T) : W.map F x ∈ W.NΔ T' :=
  ⟨W.map_N F hT hT' x hx.1, fun δ hδ => by rw [← W.map_γ, hx.2 δ hδ]⟩

/- English proof (translation)
Take `⟨wπ, hwπ⟩` from `R.ππ`. Establish `hp1 : PD.p - 1 = (PD.p - 2) + 1` using `by have := PD.hp.two_le; omega`. Use `⟨((wπ : LetA O n) * letπ ^ (PD.p - 2)) • m, (W.N T).smul_mem _ hm, ?_⟩` and prove the remaining obligations. Rewrite using `[lifta_X_eq W hs, smul_smul]`. Use `congr 1`.

Rewrite using `[hwπ, hp1, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lifta_π₀_X (W : LocWach PD LL O v n) (R : lifta_Ring W) (hs : W.s = 1)
    (T : LocLat G Qp LL O) (m : W.DD T) (hm : m ∈ W.N T) : ∃ m' ∈ W.N T, W.X • m' = W.π₀ • m := by
  obtain ⟨wπ, hwπ⟩ := R.ππ
  have hp1 : PD.p - 1 = (PD.p - 2) + 1 := by have := PD.hp.two_le; omega
  refine ⟨((wπ : LetA O n) * letπ ^ (PD.p - 2)) • m, (W.N T).smul_mem _ hm, ?_⟩
  rw [lifta_X_eq W hs, smul_smul]
  congr 1
  rw [hwπ, hp1, pow_succ]
  ring

/- English proof (translation)
Take `⟨m, hm, rfl⟩` from `hz`. Establish `hzN : (letπ : LetA O n) • m ∈ W.N T` using `(W.N T).smul_mem _ hm`. Establish `h : ∀ δ : W.Gam, ∃ y ∈ W.N T, W.γD T δ ((letπ : LetA O n) • m) = (letπ : LetA O n) • y`. Introduce `δ`. Take `⟨y, hy, hyy⟩` from `W.N_π T δ _ hzN`.

Use `⟨m + y, (W.N T).add_mem hm hy, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add, ← hyy]`. Normalize the expressions using the abelian group laws. Use `choose y hy hyy using h`. Use `⟨d • ∑ δ ∈ W.DelF, y δ, (W.N T).smul_of_tower_mem d (Submodule.sum_mem _ (fun δ _ => hy δ)), ?_⟩` and prove the remaining obligations.

Rewrite using `[lifta_avg_apply, Finset.sum_congr rfl (fun δ _ => hyy δ), ← Finset.smul_sum, smul_comm]`.
-/
theorem lifta_avg_πN (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (d : O) (z : W.DD T)
    (hz : ∃ m ∈ W.N T, z = (letπ : LetA O n) • m) :
    ∃ m ∈ W.N T, lifta_avg W T d z = (letπ : LetA O n) • m := by
  obtain ⟨m, hm, rfl⟩ := hz
  have hzN : (letπ : LetA O n) • m ∈ W.N T := (W.N T).smul_mem _ hm
  have h : ∀ δ : W.Gam, ∃ y ∈ W.N T, W.γD T δ ((letπ : LetA O n) • m) = (letπ : LetA O n) • y := by
    intro δ
    obtain ⟨y, hy, hyy⟩ := W.N_π T δ _ hzN
    refine ⟨m + y, (W.N T).add_mem hm hy, ?_⟩
    rw [smul_add, ← hyy]
    abel
  choose y hy hyy using h
  refine ⟨d • ∑ δ ∈ W.DelF, y δ, (W.N T).smul_of_tower_mem d (Submodule.sum_mem _ (fun δ _ => hy δ)), ?_⟩
  rw [lifta_avg_apply, Finset.sum_congr rfl (fun δ _ => hyy δ), ← Finset.smul_sum, smul_comm]

/- English proof (translation)
Introduce `y z hyz`. Take `⟨⟨hyQ, m, hm, hz⟩, hd1'⟩` from `hyz`. Establish `hyQ' : qp W ^ M • y ∈ W.NΔ T₂` using `hyQ`. Establish `hz' : z = W.π₀ • m` using `hz`. Establish `hm' : m ∈ W.NΔ T₂` using `hm`.

Establish `hcoc : (W.γ T₂ y - y) - (W.φD T₂ z - z) = 0` using `hd1'`. Take `⟨n₁, hn₁, hπn₁⟩` from `hCK _ hyQ'`. Take `⟨m₁, hm₁, hπm₁⟩` from `hCK m hm'`. Take `⟨y₁, hy₁⟩` from `(lifta_qpow_bij W R T₁ M).2 n₁`. Establish `hy₁' : qp W ^ M • y₁ = n₁` using `hy₁`.

Establish `hy₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ y₁ = y₁` using `lifta_inv_of_q W R T₁ M y₁ (by rw [hy₁']; exact hn₁.2)`. Establish `hz₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ (W.π₀ • m₁) = W.π₀ • m₁` using `(invariant_smul_mem_invariants' W T₁ W.π₀ R.πΔ m₁ hm₁).2`. Establish `hπy₁ : W.map π y₁ = (PD.p ^ e : ℕ) • y`. Apply `(lifta_qpow_bij W R T₂ M).1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `qp W ^ M • W.map π y₁ = qp W ^ M • ((PD.p ^ e : ℕ) • y)`.

Rewrite using `[← liftb_map_smul, hy₁', hπn₁, smul_comm]`. Establish `hπz₁ : W.map π (W.π₀ • m₁) = (PD.p ^ e : ℕ) • z`. Rewrite using `[liftb_map_smul, hπm₁, hz', smul_comm]`. Take `⟨mX, hmX, hmXe⟩` from `lifta_π₀_X W R hs T₂ m hm'.1`. Take `⟨m₁X, hm₁X, hm₁Xe⟩` from `lifta_π₀_X W R hs T₁ m₁ hm₁.1`.

Take `⟨w, hw, _, k, y₀, hy₀, z₀, hz₀, hk⟩` from `hd hses ((PD.p ^ e : ℕ) • y) ((PD.p ^ e : ℕ) • z) (by`. Express the relevant statement in the definitionally equal form `W.Q ^ M • ((PD.p ^ e : ℕ) • y) ∈ W.N T₂`. Rewrite using `[smul_comm]`. Conclude with `(W.N T₂).smul_of_tower_mem _ ((lifta_Qq W R hs T₂ M y).2 hyQ'.1))`. Use the proof step `⟨(PD.p ^ e : ℕ) • mX, (W.N T₂).smul_of_tower_mem _ hmX, by`.

Express the relevant statement in the definitionally equal form `W.X • ((PD.p ^ e : ℕ) • mX) = _`. Rewrite using `[smul_comm, hmXe, hz']⟩`. Use the proof step `(by`. Establish `h0 : (y, z) ∈ W.divisibleCocycles T₂` using `(liftb_mem_Z1D W T₂ y z).2 hcoc`. Conclude with `(W.divisibleCocycles T₂).smul_of_tower_mem (PD.p ^ e : ℕ) h0)`.

Use `y₁ (W.π₀ • m₁)`. Use the proof step `(by`. Express the relevant statement in the definitionally equal form `W.Q ^ M • y₁ ∈ W.N T₁`. Conclude with `(lifta_Qq W R hs T₁ M y₁).2 (by rw [hy₁']; exact hn₁.1))`. Use the proof step `⟨m₁X, hm₁X, hm₁Xe⟩ hπy₁ hπz₁`.

Establish `hy₀' : qp W ^ M • y₀ ∈ W.N T₀` using `(lifta_Qq W R hs T₀ M y₀).1 hy₀`. Take `⟨z₀', hz₀', hz₀e⟩` from `hz₀`. Establish `hz₀e' : z₀ = (letπ : LetA O n) • z₀'` using `by rw [← lifta_X_eq W hs]; exact hz₀e.symm`. Establish `hk' : (PD.p ^ k : ℕ) • w = (W.γ T₀ y₀ - y₀) - (W.φD T₀ z₀ - z₀)`. Rewrite using `[← hk, liftb_ns]`.

Use `set Y₀ := lifta_avg W T₀ d y₀ with hY₀`. Use `set Z₀ := lifta_avg W T₀ d z₀ with hZ₀`. Establish `hQY₀ : qp W ^ M • Y₀ ∈ W.NΔ T₀`. Rewrite using `[hY₀, ← lifta_avg_smul W T₀ d _ (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) M)]`. Conclude with `lifta_avg_N W T₀ d _ hy₀'`.

Establish `hZ₀N : Z₀ ∈ W.NΔ T₀` using `lifta_avg_N W T₀ d _ (by rw [hz₀e']; exact (W.N T₀).smul_mem _ hz₀')`. Take `⟨x', hx', hx'e⟩` from `lifta_interN W T₀ h9 hm0 Z₀ hZ₀N (lifta_avg_πN W T₀ d z₀ ⟨z₀', hz₀', hz₀e'⟩)`. Establish `havg : (PD.p ^ k : ℕ) • lifta_avg W T₀ d w = (W.γ T₀ Y₀ - Y₀) - (W.φD T₀ Z₀ - Z₀)`. Rewrite using `[← map_nsmul, hk', map_sub, map_sub, map_sub, lifta_avg_φ]`. Establish `: lifta_avg W T₀ d (W.γ T₀ y₀) = W.γ T₀ (lifta_avg W T₀ d y₀)` using `lifta_avg_γ W T₀ d W.gam y₀`.

Rewrite using `[this]`. Establish `hιavg : W.map ι (lifta_avg W T₀ d w) = (W.γ T₁ y₁ - y₁) - (W.φD T₁ (W.π₀ • m₁) - W.π₀ • m₁)`. Rewrite using `[lifta_avg_map, hw, map_sub, map_sub, map_sub, lifta_avg_φ]`. Establish `h1 : lifta_avg W T₁ d (W.γ T₁ y₁) = W.γ T₁ (lifta_avg W T₁ d y₁)` using `lifta_avg_γ W T₁ d W.gam y₁`. Rewrite using `[h1, lifta_avg_fix W T₁ d hd1 y₁ hy₁Δ, lifta_avg_fix W T₁ d hd1 _ hz₁Δ]`.

Establish `hπι : ∀ x, W.map π (W.map ι x) = 0` using `fun x => (hE.2 _).2 ⟨x, rfl⟩`. Use `⟨k + e, (PD.p ^ k : ℕ) • y₁ - W.map ι Y₀, (PD.p ^ k : ℕ) • (W.π₀ • m₁) - W.map ι Z₀, ⟨⟨?_, ?_⟩, ?_⟩, 0, (W.NΔ T₂).zero_mem, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `qp W ^ M • ((PD.p ^ k : ℕ) • y₁ - W.map ι Y₀) ∈ W.NΔ T₁`. Rewrite using `[smul_sub, smul_comm, hy₁', ← liftb_map_smul]`. Conclude with `(W.NΔ T₁).sub_mem ((W.NΔ T₁).smul_of_tower_mem _ hn₁) (lifta_map_NΔ W ι g₀.crys g₁.crys _ hQY₀)`.

Use `⟨(PD.p ^ k : ℕ) • m₁ - W.map ι x', (W.NΔ T₁).sub_mem ((W.NΔ T₁).smul_of_tower_mem _ hm₁) (lifta_map_NΔ W ι g₀.crys g₁.crys _ hx'), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = W.π₀ • ((PD.p ^ k : ℕ) • m₁ - W.map ι x')`. Rewrite using `[smul_sub, ← liftb_map_smul, ← hx'e, smul_comm]`. Express the relevant statement in the definitionally equal form `(W.γ T₁ ((PD.p ^ k : ℕ) • y₁ - W.map ι Y₀) - ((PD.p ^ k : ℕ) • y₁ - W.map ι Y₀)) - (W.φD T₁ ((PD.p ^ k : ℕ) • (W.π₀ • m₁) - W.map ι Z₀) - ((PD.p ^ k : ℕ) • (W.π₀ • m₁) - W.map ι Z₀)) = 0`. Establish `hγι : W.γ T₁ (W.map ι Y₀) = W.map ι (W.γ T₀ Y₀)` using `(W.map_γ ι W.gam Y₀).symm`.

Establish `hφι : W.φD T₁ (W.map ι Z₀) = W.map ι (W.φD T₀ Z₀)` using `(W.map_φ ι Z₀).symm`. Establish `h1 : W.map ι ((PD.p ^ k : ℕ) • lifta_avg W T₀ d w) = (W.map ι (W.γ T₀ Y₀) - W.map ι Y₀) - (W.map ι (W.φD T₀ Z₀) - W.map ι Z₀)`. Rewrite using `[havg, map_sub, map_sub, map_sub]`. Rewrite `h1` using `[map_nsmul, hιavg]`. Rewrite using `[map_sub, map_sub, map_nsmul, map_nsmul, hγι, hφι]`.

Establish `h3 : ((PD.p ^ k : ℕ) • W.γ T₁ y₁ - W.map ι (W.γ T₀ Y₀) - ((PD.p ^ k : ℕ) • y₁ - W.map ι Y₀)) - ((PD.p ^ k : ℕ) • W.φD T₁ (W.π₀ • m₁) - W.map ι (W.φD T₀ Z₀) - ((PD.p ^ k : ℕ) • (W.π₀ • m₁) - W.map ι Z₀)) = (PD.p ^ k : ℕ) • ((W.γ T₁ y₁ - y₁) - (W.φD T₁ (W.π₀ • m₁) - W.π₀ • m₁)) - ( …`. Rewrite using `[smul_sub, smul_sub, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[h3, h1, sub_self]`. Express the relevant statement in the definitionally equal form `W.map π ((PD.p ^ k : ℕ) • y₁ - W.map ι Y₀) = (((PD.p : ℕ) : ℤ_[ℓ]) ^ (k + e)) • y + (W.φD T₂ 0 - 0)`.

Rewrite using `[map_sub, hπι, map_nsmul, hπy₁, liftb_ns, map_zero, pow_add, mul_smul]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `W.map π ((PD.p ^ k : ℕ) • (W.π₀ • m₁) - W.map ι Z₀) = (((PD.p : ℕ) : ℤ_[ℓ]) ^ (k + e)) • z + (W.γ T₂ 0 - 0)`. Rewrite using `[map_sub, hπι, map_nsmul, hπz₁, liftb_ns, map_zero, pow_add, mul_smul]`. Simplify using the standard rewrite rules.
-/
theorem lifta_ratSurj (W : LocWach PD LL O v n) (R : lifta_Ring W) (hs : W.s = 1)
    {T₀ T₁ T₂ : LocLat G Qp LL O}
    (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L) (M : ℕ) (g₀ : lifta_Good W T₀ M)
    (g₁ : lifta_Good W T₁ M) (g₂ : lifta_Good W T₂ M) (hE : liftb_DDExact W ι π)
    (hsat : ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) (e : ℕ)
    (hses : IsSESLat (Qp := Qp) ι π) (hd : Formalism.MainNotions.DeltaInvariantLattices.p2d W ι π M)
    (d : O) (hd1 : d * (W.DelF.card : O) = 1) (h9 : P9π₀ W)
    (hm0 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₀ W.π₀)
    (hCK : ∀ y ∈ W.NΔ T₂, ∃ x ∈ W.NΔ T₁, W.map π x = (PD.p ^ e : ℕ) • y) :
    Formalism.CoboundaryTransfers.RatSurj (lifta_ses (ℓ := ℓ) W R ι π M g₀ g₁ g₂ hE hsat) := by
  intro y z hyz
  obtain ⟨⟨hyQ, m, hm, hz⟩, hd1'⟩ := hyz
  have hyQ' : qp W ^ M • y ∈ W.NΔ T₂ := hyQ
  have hz' : z = W.π₀ • m := hz
  have hm' : m ∈ W.NΔ T₂ := hm
  have hcoc : (W.γ T₂ y - y) - (W.φD T₂ z - z) = 0 := hd1'
  obtain ⟨n₁, hn₁, hπn₁⟩ := hCK _ hyQ'
  obtain ⟨m₁, hm₁, hπm₁⟩ := hCK m hm'
  obtain ⟨y₁, hy₁⟩ := (lifta_qpow_bij W R T₁ M).2 n₁
  have hy₁' : qp W ^ M • y₁ = n₁ := hy₁
  have hy₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ y₁ = y₁ :=
    lifta_inv_of_q W R T₁ M y₁ (by rw [hy₁']; exact hn₁.2)
  have hz₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ (W.π₀ • m₁) = W.π₀ • m₁ :=
    (invariant_smul_mem_invariants' W T₁ W.π₀ R.πΔ m₁ hm₁).2
  have hπy₁ : W.map π y₁ = (PD.p ^ e : ℕ) • y := by
    apply (lifta_qpow_bij W R T₂ M).1
    change qp W ^ M • W.map π y₁ = qp W ^ M • ((PD.p ^ e : ℕ) • y)
    rw [← liftb_map_smul, hy₁', hπn₁, smul_comm]
  have hπz₁ : W.map π (W.π₀ • m₁) = (PD.p ^ e : ℕ) • z := by
    rw [liftb_map_smul, hπm₁, hz', smul_comm]
  obtain ⟨mX, hmX, hmXe⟩ := lifta_π₀_X W R hs T₂ m hm'.1
  obtain ⟨m₁X, hm₁X, hm₁Xe⟩ := lifta_π₀_X W R hs T₁ m₁ hm₁.1
  obtain ⟨w, hw, _, k, y₀, hy₀, z₀, hz₀, hk⟩ := hd hses ((PD.p ^ e : ℕ) • y) ((PD.p ^ e : ℕ) • z)
    (by
      change W.Q ^ M • ((PD.p ^ e : ℕ) • y) ∈ W.N T₂
      rw [smul_comm]
      exact (W.N T₂).smul_of_tower_mem _ ((lifta_Qq W R hs T₂ M y).2 hyQ'.1))
    ⟨(PD.p ^ e : ℕ) • mX, (W.N T₂).smul_of_tower_mem _ hmX, by
      change W.X • ((PD.p ^ e : ℕ) • mX) = _
      rw [smul_comm, hmXe, hz']⟩
    (by
      have h0 : (y, z) ∈ W.divisibleCocycles T₂ := (liftb_mem_Z1D W T₂ y z).2 hcoc
      exact (W.divisibleCocycles T₂).smul_of_tower_mem (PD.p ^ e : ℕ) h0)
    y₁ (W.π₀ • m₁)
    (by
      change W.Q ^ M • y₁ ∈ W.N T₁
      exact (lifta_Qq W R hs T₁ M y₁).2 (by rw [hy₁']; exact hn₁.1))
    ⟨m₁X, hm₁X, hm₁Xe⟩ hπy₁ hπz₁
  have hy₀' : qp W ^ M • y₀ ∈ W.N T₀ := (lifta_Qq W R hs T₀ M y₀).1 hy₀
  obtain ⟨z₀', hz₀', hz₀e⟩ := hz₀
  have hz₀e' : z₀ = (letπ : LetA O n) • z₀' := by rw [← lifta_X_eq W hs]; exact hz₀e.symm
  have hk' : (PD.p ^ k : ℕ) • w = (W.γ T₀ y₀ - y₀) - (W.φD T₀ z₀ - z₀) := by
    rw [← hk, liftb_ns]

  set Y₀ := lifta_avg W T₀ d y₀ with hY₀
  set Z₀ := lifta_avg W T₀ d z₀ with hZ₀
  have hQY₀ : qp W ^ M • Y₀ ∈ W.NΔ T₀ := by
    rw [hY₀, ← lifta_avg_smul W T₀ d _ (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) M)]
    exact lifta_avg_N W T₀ d _ hy₀'
  have hZ₀N : Z₀ ∈ W.NΔ T₀ :=
    lifta_avg_N W T₀ d _ (by rw [hz₀e']; exact (W.N T₀).smul_mem _ hz₀')
  obtain ⟨x', hx', hx'e⟩ := lifta_interN W T₀ h9 hm0 Z₀ hZ₀N
    (lifta_avg_πN W T₀ d z₀ ⟨z₀', hz₀', hz₀e'⟩)
  have havg : (PD.p ^ k : ℕ) • lifta_avg W T₀ d w = (W.γ T₀ Y₀ - Y₀) - (W.φD T₀ Z₀ - Z₀) := by
    rw [← map_nsmul, hk', map_sub, map_sub, map_sub, lifta_avg_φ]
    have : lifta_avg W T₀ d (W.γ T₀ y₀) = W.γ T₀ (lifta_avg W T₀ d y₀) := lifta_avg_γ W T₀ d W.gam y₀
    rw [this]
  have hιavg : W.map ι (lifta_avg W T₀ d w) =
      (W.γ T₁ y₁ - y₁) - (W.φD T₁ (W.π₀ • m₁) - W.π₀ • m₁) := by
    rw [lifta_avg_map, hw, map_sub, map_sub, map_sub, lifta_avg_φ]
    have h1 : lifta_avg W T₁ d (W.γ T₁ y₁) = W.γ T₁ (lifta_avg W T₁ d y₁) :=
      lifta_avg_γ W T₁ d W.gam y₁
    rw [h1, lifta_avg_fix W T₁ d hd1 y₁ hy₁Δ, lifta_avg_fix W T₁ d hd1 _ hz₁Δ]
  have hπι : ∀ x, W.map π (W.map ι x) = 0 := fun x => (hE.2 _).2 ⟨x, rfl⟩
  refine ⟨k + e, (PD.p ^ k : ℕ) • y₁ - W.map ι Y₀, (PD.p ^ k : ℕ) • (W.π₀ • m₁) - W.map ι Z₀,
    ⟨⟨?_, ?_⟩, ?_⟩, 0, (W.NΔ T₂).zero_mem, ?_, ?_⟩
  · change qp W ^ M • ((PD.p ^ k : ℕ) • y₁ - W.map ι Y₀) ∈ W.NΔ T₁
    rw [smul_sub, smul_comm, hy₁', ← liftb_map_smul]
    exact (W.NΔ T₁).sub_mem ((W.NΔ T₁).smul_of_tower_mem _ hn₁) (lifta_map_NΔ W ι g₀.crys g₁.crys _ hQY₀)
  · refine ⟨(PD.p ^ k : ℕ) • m₁ - W.map ι x', (W.NΔ T₁).sub_mem ((W.NΔ T₁).smul_of_tower_mem _ hm₁)
      (lifta_map_NΔ W ι g₀.crys g₁.crys _ hx'), ?_⟩
    change _ = W.π₀ • ((PD.p ^ k : ℕ) • m₁ - W.map ι x')
    rw [smul_sub, ← liftb_map_smul, ← hx'e, smul_comm]
  · change (W.γ T₁ ((PD.p ^ k : ℕ) • y₁ - W.map ι Y₀) - ((PD.p ^ k : ℕ) • y₁ - W.map ι Y₀)) -
      (W.φD T₁ ((PD.p ^ k : ℕ) • (W.π₀ • m₁) - W.map ι Z₀) -
        ((PD.p ^ k : ℕ) • (W.π₀ • m₁) - W.map ι Z₀)) = 0
    have hγι : W.γ T₁ (W.map ι Y₀) = W.map ι (W.γ T₀ Y₀) := (W.map_γ ι W.gam Y₀).symm
    have hφι : W.φD T₁ (W.map ι Z₀) = W.map ι (W.φD T₀ Z₀) := (W.map_φ ι Z₀).symm
    have h1 : W.map ι ((PD.p ^ k : ℕ) • lifta_avg W T₀ d w) =
        (W.map ι (W.γ T₀ Y₀) - W.map ι Y₀) - (W.map ι (W.φD T₀ Z₀) - W.map ι Z₀) := by
      rw [havg, map_sub, map_sub, map_sub]
    rw [map_nsmul, hιavg] at h1
    rw [map_sub, map_sub, map_nsmul, map_nsmul, hγι, hφι]
    have h3 : ((PD.p ^ k : ℕ) • W.γ T₁ y₁ - W.map ι (W.γ T₀ Y₀) - ((PD.p ^ k : ℕ) • y₁ - W.map ι Y₀)) -
        ((PD.p ^ k : ℕ) • W.φD T₁ (W.π₀ • m₁) - W.map ι (W.φD T₀ Z₀) -
          ((PD.p ^ k : ℕ) • (W.π₀ • m₁) - W.map ι Z₀)) =
        (PD.p ^ k : ℕ) • ((W.γ T₁ y₁ - y₁) - (W.φD T₁ (W.π₀ • m₁) - W.π₀ • m₁)) -
          ((W.map ι (W.γ T₀ Y₀) - W.map ι Y₀) - (W.map ι (W.φD T₀ Z₀) - W.map ι Z₀)) := by
      rw [smul_sub, smul_sub, smul_sub]
      abel
    rw [h3, h1, sub_self]
  · change W.map π ((PD.p ^ k : ℕ) • y₁ - W.map ι Y₀) =
      (((PD.p : ℕ) : ℤ_[ℓ]) ^ (k + e)) • y + (W.φD T₂ 0 - 0)
    rw [map_sub, hπι, map_nsmul, hπy₁, liftb_ns, map_zero, pow_add, mul_smul]
    simp
  · change W.map π ((PD.p ^ k : ℕ) • (W.π₀ • m₁) - W.map ι Z₀) =
      (((PD.p : ℕ) : ℤ_[ℓ]) ^ (k + e)) • z + (W.γ T₂ 0 - 0)
    rw [map_sub, hπι, map_nsmul, hπz₁, liftb_ns, map_zero, pow_add, mul_smul]
    simp

def lifta_Complete (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Prop :=
  ∃ I : Ideal ↥W.AΔ, (∀ h : qp W ∈ W.AΔ, (⟨qp W, h⟩ : ↥W.AΔ) ∈ I) ∧ (∀ a ∈ I, lifta_φ₀ W a ∈ I) ∧
    IsAdicComplete I ↥(lifta_N W T)

/- English proof (translation)
Establish `hne : (u : ℤ_[ℓ]) - 1 ≠ 0`. Introduce `h`. Rewrite `hv` using `[h]`. Simplify using `at hv`. Establish `hu1 : (u : ℤ_[ℓ]) - 1 ∈ Ideal.span {(ℓ : ℤ_[ℓ])}`.

Rewrite using `[Ideal.mem_span_singleton]`. Establish `h` using `PadicInt.unitCoeff_spec hne`. Rewrite `h` using `[hv, pow_one]`. Conclude with `⟨_, by rw [h]; ring⟩`. Use `set f : ℤ_[ℓ]ˣ →* (ℤ_[ℓ] ⧸ Ideal.span {(ℓ : ℤ_[ℓ])})ˣ := Units.map (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ])})).toMonoidHom with hf`.

Establish `hfu : f u = 1`. Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk _ (u : ℤ_[ℓ]) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ])})), Ideal.Quotient.eq]`. Conclude with `hu1`.

Establish `hd : ∀ j : ℤ, (ℓ : ℤ_[ℓ]) ∣ 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])`. Introduce `j`. Establish `h1 : f (u ^ (-j)) = 1` using `by rw [map_zpow, hfu, one_zpow]`. Establish `h2 : Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ])}) ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1` using `congrArg Units.val h1`. Rewrite `h2` using `[← map_one (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ])})), eq_comm, Ideal.Quotient.eq, Ideal.mem_span_singleton]`.

Conclude with `h2`. Use `choose c hc using hd`. Conclude with `⟨c, fun j => (hc j).symm⟩`.
-/
theorem lifta_exists_c (u : ℤ_[ℓ]ˣ) (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1) :
    ∃ c : ℤ → ℤ_[ℓ], ∀ j : ℤ, (ℓ : ℤ_[ℓ]) * c j = 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
  have hne : (u : ℤ_[ℓ]) - 1 ≠ 0 := by
    intro h
    rw [h] at hv
    simp at hv
  have hu1 : (u : ℤ_[ℓ]) - 1 ∈ Ideal.span {(ℓ : ℤ_[ℓ])} := by
    rw [Ideal.mem_span_singleton]
    have h := PadicInt.unitCoeff_spec hne
    rw [hv, pow_one] at h
    exact ⟨_, by rw [h]; ring⟩
  set f : ℤ_[ℓ]ˣ →* (ℤ_[ℓ] ⧸ Ideal.span {(ℓ : ℤ_[ℓ])})ˣ :=
    Units.map (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ])})).toMonoidHom with hf
  have hfu : f u = 1 := by
    apply Units.ext
    change Ideal.Quotient.mk _ (u : ℤ_[ℓ]) = 1
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ])})), Ideal.Quotient.eq]
    exact hu1
  have hd : ∀ j : ℤ, (ℓ : ℤ_[ℓ]) ∣ 1 - ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) := by
    intro j
    have h1 : f (u ^ (-j)) = 1 := by rw [map_zpow, hfu, one_zpow]
    have h2 : Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ])}) ((u ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) = 1 :=
      congrArg Units.val h1
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(ℓ : ℤ_[ℓ])})), eq_comm, Ideal.Quotient.eq,
      Ideal.mem_span_singleton] at h2
    exact h2
  choose c hc using hd
  exact ⟨c, fun j => (hc j).symm⟩

/- English proof (translation)
Unfold `Formalism.RepresentationBoundsCohomology.N2.JSet JSet Formalism.RepresentationBoundsCohomology.N2.eigSet`. Rewrite using `[Finset.filter_ne']`.
-/
theorem lifta_JSet_eq (jumps : Finset ℤ) (M : ℕ) : Formalism.RepresentationBoundsCohomology.N2.JSet jumps M = JSet jumps M := by
  unfold Formalism.RepresentationBoundsCohomology.N2.JSet JSet Formalism.RepresentationBoundsCohomology.N2.eigSet
  rw [Finset.filter_ne']

def lifta_Inv (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Submodule O (W.DD T) where
  carrier := {x | ∀ δ ∈ W.DelF, W.γD T δ x = x}
  add_mem' := fun ha hb δ hδ => by rw [map_add, ha δ hδ, hb δ hδ]
  zero_mem' := fun δ _ => map_zero _
  smul_mem' := fun c x hx δ hδ => by rw [map_smul, hx δ hδ]

/- English proof (translation)
Introduce `x hx δ hδ`. Apply `lifta_π₀_cancel W T c hc` to reduce the goal to its premises. Establish `h1 : W.π₀ • W.γD T δ (lifta_δ W T c x) = W.γD T δ (W.π₀ • lifta_δ W T c x)`. Rewrite using `[gammaD_semilinear, R.πΔ δ hδ]`. Rewrite using `[h1, lifta_δ_spec W T c hc, map_sub, hx δ hδ]`.

Use `congr 1`. Express the relevant statement in the definitionally equal form `W.γD T δ (W.γD T W.gam x) = W.γD T W.gam x`. Rewrite using `[← W.γD_mul, mul_comm, W.γD_mul, hx δ hδ]`.
-/
theorem lifta_δ_Inv (W : LocWach PD LL O v n) (R : lifta_Ring W) (T : LocLat G Qp LL O) (c : W.EE)
    (hc : algebraMap (LetA O n) W.EE W.π₀ * c = 1) :
    ∀ x ∈ lifta_Inv W T, lifta_δ W T c x ∈ lifta_Inv W T := by
  intro x hx δ hδ
  apply lifta_π₀_cancel W T c hc
  have h1 : W.π₀ • W.γD T δ (lifta_δ W T c x) = W.γD T δ (W.π₀ • lifta_δ W T c x) := by
    rw [gammaD_semilinear, R.πΔ δ hδ]
  rw [h1, lifta_δ_spec W T c hc, map_sub, hx δ hδ]
  congr 1
  change W.γD T δ (W.γD T W.gam x) = W.γD T W.gam x
  rw [← W.γD_mul, mul_comm, W.γD_mul, hx δ hδ]

/- English proof (translation)
Substitute `hp` using the available equality. Establish `R` using `lifta_ring_of W h9`. Take `⟨I, hQI, hφI, hI⟩` from `hC`. Establish `: IsAdicComplete I ↥(lifta_wach (ℓ` using `PD.p) W R T₀ (Mmax n Mi) g₀).N := hI`. Take `⟨cE, hcE⟩` from `R.πU.exists_right_inv`.

Take `⟨c, hc⟩` from `lifta_exists_c u hv`. Establish `hPhi : (lifta_base (ℓ` using `PD.p) W R).PhiX (PD.p - 1) := by`. Take `⟨t, ht, h⟩` from `R.φπ`. Conclude with `⟨⟨t, ht⟩, Subtype.ext h⟩`. Establish `hγX : (lifta_base (ℓ` using `PD.p) W R).GammaX ((u : ℤ_[PD.p]) ^ (PD.p - 1)) := by`.

Take `⟨t, ht, h⟩` from `R.γπ`. Use `⟨⟨t, ht⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `W.γA W.gam W.π₀ = W.π₀ * (algebraMap ℤ_[PD.p] (LetA O n) ((u : ℤ_[PD.p]) ^ (PD.p - 1)) + W.π₀ * t)`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[PD.p] O (LetA O n), map_pow, hu]`. Conclude with `h`.

Establish `hU : Units.map (algebraMap ℤ_[PD.p] O).toMonoidHom u = W.χΓ W.gam` using `Units.ext hu`. Establish `hcO : ∀ x : ℤ, ((PD.p : ℕ) : O) * algebraMap ℤ_[PD.p] O (c x) = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)`. Introduce `x`. Establish `h` using `congrArg (algebraMap ℤ_[PD.p] O) (hc x)`. Rewrite `h` using `[map_mul, map_natCast, map_sub, map_one]`.

Rewrite using `[h, ← hU, ← map_zpow]`. Both sides reduce to the same expression. Establish `hstabN : ∀ x ∈ W.NΔ T₀, lifta_δ W T₀ cE x ∈ W.NΔ T₀`. Introduce `x hx`. Take `⟨x', hx', h⟩` from `g₀.γN x hx`.

Establish `: lifta_δ W T₀ cE x = x'`. Apply `lifta_π₀_cancel W T₀ cE hcE` to reduce the goal to its premises. Rewrite using `[lifta_δ_spec W T₀ cE hcE, h]`. Rewrite using `[this]`. Conclude with `hx'`.

Establish `hSemi : Formalism.RepresentationBoundsCohomology.N2.SemiA (lifta_wach (ℓ` using `PD.p) W R T₀ (Mmax n Mi) g₀) ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) c jumps := by`. Introduce `y hy`. Establish `hy' : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₀` using `hy`. Establish `hyΔ` using `lifta_inv_of_q W R T₀ (Mmax n Mi) y hy'.2`. Express the relevant statement in the definitionally equal form `Polynomial.aeval ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) _ y ∈ W.NΔ T₀`.

Rewrite using `[liftb_aeval_res, Polynomial.map_prod]`. Establish `h0` using `lifta_semiO W T₀ cE hcE hA hD Mi hi c0 hJ0 (fun x => algebraMap ℤ_[PD.p] O (c x)) hcO (Mmax n Mi) y hy'.1 hyΔ`. Establish `hsub : ((jumpSet W T₀ (Mmax n Mi) (Mmax n hi)) ×ˢ Finset.Icc (1 : ℤ) (Mmax n Mi)).image (fun p : ℤ × ℤ => p.1 + p.2) ⊆ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi)` using `Finset.image_subset_image (Finset.product_subset_product hj (Finset.Subset.refl _))`. Take `⟨R', hR'⟩` from `Finset.prod_dvd_prod_of_subset _ _ (fun x : ℤ => (Polynomial.X - Polynomial.C (algebraMap ℤ_[PD.p] O (c x)) : Polynomial O)) hsub`. Establish `hmap : ∏ j ∈ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi), (Polynomial.X - Polynomial.C (c j)).map (algebraMap ℤ_[PD.p] O) = ∏ j ∈ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi), (Polynomial.X - Polynomial.C (algebraMap ℤ_[PD.p] O (c …` using `Finset.prod_congr rfl (fun j _ => by`.

Rewrite using `[Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C])`. Rewrite using `[hmap, hR', mul_comm, map_mul, Module.End.mul_apply]`. Use `liftb_aeval_mem (W.NΔ T₀) _ hstabN R' _ ⟨h0, ?_⟩` and prove the remaining obligations. Conclude with `liftb_aeval_mem (lifta_Inv W T₀) _ (lifta_δ_Inv W R T₀ cE hcE) _ y hyΔ`. Establish `hZ : ∀ y, (lifta_wach (ℓ` using `PD.p) W R T₀ (Mmax n Mi) g₀).QInv y → ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N → y ∈ (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N := by`.

Introduce `y hyQ hy`. Establish `hyQ' : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₀` using `hyQ`. Establish `hy' : ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ W.NΔ T₀` using `hy`. Use `⟨h6 y ⟨1, ?_⟩, lifta_inv_of_q W R T₀ (Mmax n Mi) y hyQ'.2⟩` and prove the remaining obligations. Rewrite using `[pow_one, Nat.cast_smul_eq_nsmul]`.

Use `hy'.1` as an intermediate fact. Rewrite `this` using `[Nat.cast_smul_eq_nsmul]`. Conclude with `this`. Establish `hL` using `lifta_core PD.p hA.2.2 ↥W.AΔ (lifta_base (ℓ := PD.p) W R) (Mmax n Mi) u jumps c rfl hPhi hγX hv hc (W.DD T₀) (W.DD T₁) (W.DD T₂) _ _ _ (lifta_ses (ℓ := PD.p) W R ι π (Mmax n Mi) g₀ g₁ g₂ hE hsat) ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) I (lifta_δ_spec W T₀ cE hcE) (hQI _) hφ …`. Introduce `y hy`.

Take `⟨x, hx, hxe⟩` from `hCK y hy`. Conclude with `⟨x, hx, by rw [liftb_ns]; exact hxe⟩)`. Use the proof step `(lifta_ratSurj W R hA.2.1 ι π (Mmax n Mi) g₀ g₁ g₂ hE hsat e hses hd d hd1 h9 hm0 hCK)`. Introduce `y z hy hz hyz`. Take `⟨y₁, z₁, ⟨⟨hy₁, hz₁⟩, hd₁⟩, e1, e2⟩` from `hL y z ⟨⟨hy, hz⟩, (liftb_mem_Z1D W T₂ y z).1 hyz⟩`.

Rewrite `e1`, `e2` using `[lifta_JSet_eq]`. Use `⟨y₁, z₁, hy₁, hz₁, (liftb_mem_Z1D W T₁ y₁ z₁).2 hd₁, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← liftb_ns (R := ℤ_[PD.p])]`. Conclude with `e1`. Rewrite using `[← liftb_ns (R := ℤ_[PD.p])]`.

Conclude with `e2`.
-/
theorem lifta_lifts (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (hA : CaseA W) (u : ℤ_[ℓ]ˣ)
    (hu : algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ]) = ((W.χΓ W.gam : Oˣ) : O))
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1) (h9 : P9π₀ W)
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)
    (Mi hi : ZMod n → ℕ)
    (g₀ : lifta_Good W T₀ (Mmax n Mi)) (g₁ : lifta_Good W T₁ (Mmax n Mi))
    (g₂ : lifta_Good W T₂ (Mmax n Mi))
    (hE : liftb_DDExact W ι π) (hsat : ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) (e : ℕ)
    (hses : IsSESLat (Qp := Qp) ι π) (hd : Formalism.MainNotions.DeltaInvariantLattices.p2d W ι π (Mmax n Mi))
    (d : O) (hd1 : d * (W.DelF.card : O) = 1) (hm0 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₀ W.π₀)
    (hCK : ∀ y ∈ W.NΔ T₂, ∃ x ∈ W.NΔ T₁, W.map π x = (PD.p ^ e : ℕ) • y)
    (c0 : IsCrys PD T₀.ρ) (hJ0 : JumpsLet W T₀ Mi hi) (hD : coreDss W) (jumps : Finset ℤ)
    (hj : jumpSet W T₀ (Mmax n Mi) (Mmax n hi) ⊆ jumps)
    (hC : lifta_Complete W T₀) (h6 : Formalism.MainNotions.DeltaInvariantLattices.wachSaturated W T₀) :
    ∀ y z : W.DD T₂, qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₂ → (∃ m ∈ W.NΔ T₂, z = W.π₀ • m) →
      (y, z) ∈ W.divisibleCocycles T₂ →
      ∃ y₁ z₁ : W.DD T₁, qp W ^ (Mmax n Mi) • y₁ ∈ W.NΔ T₁ ∧ (∃ m ∈ W.NΔ T₁, z₁ = W.π₀ • m) ∧
        (y₁, z₁) ∈ W.divisibleCocycles T₁ ∧
        W.map π y₁ = (PD.p ^ (e + eUA PD.p (Mmax n Mi) (JSet jumps (Mmax n Mi))) : ℕ) • y ∧
        W.map π z₁ = (PD.p ^ (e + eUA PD.p (Mmax n Mi) (JSet jumps (Mmax n Mi))) : ℕ) • z := by
  subst hp
  have R := lifta_ring_of W h9
  obtain ⟨I, hQI, hφI, hI⟩ := hC
  have : IsAdicComplete I ↥(lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N := hI
  obtain ⟨cE, hcE⟩ := R.πU.exists_right_inv
  obtain ⟨c, hc⟩ := lifta_exists_c u hv
  have hPhi : (lifta_base (ℓ := PD.p) W R).PhiX (PD.p - 1) := by
    obtain ⟨t, ht, h⟩ := R.φπ
    exact ⟨⟨t, ht⟩, Subtype.ext h⟩
  have hγX : (lifta_base (ℓ := PD.p) W R).GammaX ((u : ℤ_[PD.p]) ^ (PD.p - 1)) := by
    obtain ⟨t, ht, h⟩ := R.γπ
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    change W.γA W.gam W.π₀ =
      W.π₀ * (algebraMap ℤ_[PD.p] (LetA O n) ((u : ℤ_[PD.p]) ^ (PD.p - 1)) + W.π₀ * t)
    rw [IsScalarTower.algebraMap_apply ℤ_[PD.p] O (LetA O n), map_pow, hu]
    exact h
  have hU : Units.map (algebraMap ℤ_[PD.p] O).toMonoidHom u = W.χΓ W.gam := Units.ext hu
  have hcO : ∀ x : ℤ, ((PD.p : ℕ) : O) * algebraMap ℤ_[PD.p] O (c x) =
      1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) := by
    intro x
    have h := congrArg (algebraMap ℤ_[PD.p] O) (hc x)
    rw [map_mul, map_natCast, map_sub, map_one] at h
    rw [h, ← hU, ← map_zpow]
    rfl
  have hstabN : ∀ x ∈ W.NΔ T₀, lifta_δ W T₀ cE x ∈ W.NΔ T₀ := by
    intro x hx
    obtain ⟨x', hx', h⟩ := g₀.γN x hx
    have : lifta_δ W T₀ cE x = x' := by
      apply lifta_π₀_cancel W T₀ cE hcE
      rw [lifta_δ_spec W T₀ cE hcE, h]
    rw [this]
    exact hx'
  have hSemi : Formalism.RepresentationBoundsCohomology.N2.SemiA (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀)
      ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) c jumps := by
    intro y hy
    have hy' : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₀ := hy
    have hyΔ := lifta_inv_of_q W R T₀ (Mmax n Mi) y hy'.2
    change Polynomial.aeval ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) _ y ∈ W.NΔ T₀
    rw [liftb_aeval_res, Polynomial.map_prod]
    have h0 := lifta_semiO W T₀ cE hcE hA hD Mi hi c0 hJ0 (fun x => algebraMap ℤ_[PD.p] O (c x)) hcO
      (Mmax n Mi) y hy'.1 hyΔ
    have hsub : ((jumpSet W T₀ (Mmax n Mi) (Mmax n hi)) ×ˢ Finset.Icc (1 : ℤ) (Mmax n Mi)).image
        (fun p : ℤ × ℤ => p.1 + p.2) ⊆ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi) :=
      Finset.image_subset_image (Finset.product_subset_product hj (Finset.Subset.refl _))
    obtain ⟨R', hR'⟩ := Finset.prod_dvd_prod_of_subset _ _
      (fun x : ℤ => (Polynomial.X - Polynomial.C (algebraMap ℤ_[PD.p] O (c x)) : Polynomial O)) hsub
    have hmap : ∏ j ∈ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi),
        (Polynomial.X - Polynomial.C (c j)).map (algebraMap ℤ_[PD.p] O) =
        ∏ j ∈ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi),
          (Polynomial.X - Polynomial.C (algebraMap ℤ_[PD.p] O (c j)) : Polynomial O) :=
      Finset.prod_congr rfl (fun j _ => by
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C])
    rw [hmap, hR', mul_comm, map_mul, Module.End.mul_apply]
    refine liftb_aeval_mem (W.NΔ T₀) _ hstabN R' _ ⟨h0, ?_⟩
    exact liftb_aeval_mem (lifta_Inv W T₀) _ (lifta_δ_Inv W R T₀ cE hcE) _ y hyΔ
  have hZ : ∀ y, (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).QInv y →
      ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N →
      y ∈ (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N := by
    intro y hyQ hy
    have hyQ' : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₀ := hyQ
    have hy' : ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ W.NΔ T₀ := hy
    refine ⟨h6 y ⟨1, ?_⟩, lifta_inv_of_q W R T₀ (Mmax n Mi) y hyQ'.2⟩
    rw [pow_one, Nat.cast_smul_eq_nsmul]
    have := hy'.1
    rw [Nat.cast_smul_eq_nsmul] at this
    exact this
  have hL := lifta_core PD.p hA.2.2 ↥W.AΔ (lifta_base (ℓ := PD.p) W R) (Mmax n Mi) u jumps c rfl hPhi
    hγX hv hc (W.DD T₀) (W.DD T₁) (W.DD T₂) _ _ _
    (lifta_ses (ℓ := PD.p) W R ι π (Mmax n Mi) g₀ g₁ g₂ hE hsat)
    ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) I (lifta_δ_spec W T₀ cE hcE) (hQI _) hφI hZ hSemi e
    (by
      intro y hy
      obtain ⟨x, hx, hxe⟩ := hCK y hy
      exact ⟨x, hx, by rw [liftb_ns]; exact hxe⟩)
    (lifta_ratSurj W R hA.2.1 ι π (Mmax n Mi) g₀ g₁ g₂ hE hsat e hses hd d hd1 h9 hm0 hCK)
  intro y z hy hz hyz
  obtain ⟨y₁, z₁, ⟨⟨hy₁, hz₁⟩, hd₁⟩, e1, e2⟩ := hL y z ⟨⟨hy, hz⟩, (liftb_mem_Z1D W T₂ y z).1 hyz⟩
  rw [lifta_JSet_eq] at e1 e2
  refine ⟨y₁, z₁, hy₁, hz₁, (liftb_mem_Z1D W T₁ y₁ z₁).2 hd₁, ?_, ?_⟩
  · rw [← liftb_ns (R := ℤ_[PD.p])]; exact e1
  · rw [← liftb_ns (R := ℤ_[PD.p])]; exact e2

def lifta_HStr (W : LocWach PD LL O v n) : Prop :=
  CaseA W → ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → lifta_Complete W T

/- English proof (translation)
Introduce `a ha`. Unfold `jumpSet at *`. Take `⟨h1, τ, h2⟩` from `Finset.mem_filter.1 ha`. Conclude with `Finset.mem_filter.2 ⟨h1, τ, hh τ a h2⟩`.
-/
theorem lifta_jumpSet_mono (W : LocWach PD LL O v n) (T T' : LocLat G Qp LL O) (M h : ℕ)
    (hh : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), IsJumpV PD T.ρ τ a → IsJumpV PD T'.ρ τ a) :
    jumpSet W T M h ⊆ jumpSet W T' M h := by
  classical
  intro a ha
  unfold jumpSet at *
  obtain ⟨h1, τ, h2⟩ := Finset.mem_filter.1 ha
  exact Finset.mem_filter.2 ⟨h1, τ, hh τ a h2⟩

/- English proof (translation)
Simplify using `[LocWach.wachCocyclesDelta, herrZ1Δ, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero, Prod.ext_iff]`.
-/
theorem lifta_mem_Z1DΔ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (y z : W.DD T) :
    (y, z) ∈ W.wachCocyclesDelta T ↔ (y, z) ∈ herrCocycles (W.γD T W.gamK) (W.φD T) ∧
      ∀ δ ∈ W.DelF, W.γD T δ y = y ∧ W.γD T δ z = z := by
  simp [LocWach.wachCocyclesDelta, herrZ1Δ, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    sub_eq_zero, Prod.ext_iff]

/- English proof (translation)
Use `liftb_neZero W` as an intermediate fact. Introduce `hA T₁ T₂ F Mi hi hS hJ1`. Establish `hs : W.s = 1` using `hA.2.1`. Establish `hp2 : PD.p ≠ 2` using `hA.2.2`. Rewrite `hv` using `[hs]`.

Take `⟨c1, c2, hOnto⟩` from `hS`. Take `⟨T₀, ι, hses, c0⟩` from `hKer T₁ T₂ F ⟨c1, c2, hOnto⟩`. Establish `hJ` using `hJmp T₀ T₁ T₂ ι F hses c0 c1 c2`. Establish `hJ0 : JumpsLet W T₀ Mi hi` using `fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inl ha))`. Establish `hJ2 : JumpsLet W T₂ Mi hi` using `fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inr ha))`.

Establish `hc0` using `h2c T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)`. Establish `hc1` using `h2c T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)`. Establish `hd` using `h2d T₀ T₁ T₂ ι F Mi hi c0 c1 c2 (liftb_jl W T₁ Mi hi hJ1)`. Rewrite `hc0`, `hc1`, `hd` using `[liftb_mx_eq]`. Establish `hQ` using `hc0.1`.

Establish `gb₀` using `liftb_good_of W T₀ c0 Mi hi (h2 T₀ c0) (h5 T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)) hQ`. Establish `gb₁` using `liftb_good_of W T₁ c1 Mi hi (h2 T₁ c1) (h5 T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)) hQ`. Establish `gb₂` using `liftb_good_of W T₂ c2 Mi hi (h2 T₂ c2) (h5 T₂ Mi hi c2 (liftb_jl W T₂ Mi hi hJ2)) hQ`. Establish `h90` using `uniformizer_ring_and_module_clauses W h9 hA T₀ c0`. Establish `R` using `lifta_ring_of W h90.1`.

Establish `g₀` using `lifta_good_of W R hs T₀ _ gb₀ h90.2`. Establish `g₁` using `lifta_good_of W R hs T₁ _ gb₁ (uniformizer_ring_and_module_clauses W h9 hA T₁ c1).2`. Establish `g₂` using `lifta_good_of W R hs T₂ _ gb₂ (uniformizer_ring_and_module_clauses W h9 hA T₂ c2).2`. Establish `hcard : W.DelF.card = PD.p - 1`. Rewrite using `[(h9 T₀ c0 hs hp2).1, finrank_eq_one_case_A W hA, Nat.div_one]`.

Take `⟨d, hd1⟩` from `lifta_exists_d W hp hcard`. Establish `hE` using `hExact T₀ T₁ T₂ ι F hses`. Establish `hsat` using `(h6.2.2 T₀ T₁ T₂ ι F c0 c1 c2 hses).2.2.2.1`. Establish `hCKN : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁, W.map F x = (PD.p ^ (eWA PD.p (Hmax n Mi hi)) : ℕ) • y`. Introduce `y hy`.

Take `⟨x, hx, hxe⟩` from `liftb_kills_all W F _ (hWA hA T₁ T₂ F Mi hi ⟨c1, c2, hOnto⟩ hJ1) y hy`. Conclude with `⟨x, hx, by rw [hxe, lp, liftb_ns]⟩`. Establish `hL` using `lifta_lifts W hp hA u hu hv h90.1 ι F Mi hi g₀ g₁ g₂ hE hsat (eWA PD.p (Hmax n Mi hi)) hses hd d hd1 h90.2 (lifta_cokerΔ W F d hd1 _ hCKN) c0 hJ0 hD (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (lifta_jumpSet_mono W T₀ T₁ _ _ (fun τ a ha => (hJ τ a).2 (Or.inl ha))) (hStr hA T₀ c0) (h6. …`. Apply `liftb_LiftF_of PD F` to reduce the goal to its premises. Introduce `κ hκ`.

Take `⟨c, hc, hcf, rfl⟩` from `(liftb_mem_H1fT PD T₂ κ).1 hκ`. Take `⟨Tp, ι', π', cp, hext⟩` from `hExt T₂ c c2 hcf`. Take `⟨cone, hone0, e, he, hspan, hφe, hγe⟩` from `hOne`. Establish `hJp'` using `hJmp T₂ Tp W.one ι' π' hext.1 c2 cp cone`. Establish `hJp : JumpsLet W Tp Mi hi`.

Introduce `i τ hτ a ha`. Break down `(hJp' τ a).1 ha with h | h` into its components or cases. Conclude with `hJ2 i τ hτ a h`. Rewrite using `[hone0 τ a h]`. Conclude with `⟨by simp, by simp⟩`.

Establish `hImg : InImgA W π' (eWA PD.p (Hmax n Mi hi))`. Take `⟨x, hx, hxe⟩` from `liftb_kills_all W π' _ (hWA hA Tp W.one π' Mi hi ⟨cp, cone, hext.1.2.2.1⟩ hJp) e he`. Conclude with `⟨e, he, hspan, hφe, hγe, x, hx, by rw [hxe, lp, liftb_ns, liftb_ns]⟩`. Take `⟨y, z, h, hy, hz, hcl⟩` from `hExtC hA T₂ Tp ι' π' Mi hi c2 cp hJ2 c hc hext _ hImg`. Establish `hΔ` using `((lifta_mem_Z1DΔ W T₂ y z).1 h).2`.

Establish `hyΔ : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₂` using `⟨hy, fun δ hδ => by`. Rewrite using `[gammaD_semilinear, (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) _) δ hδ, (hΔ δ hδ).1]⟩`. Take `⟨y₁, z₁, hy₁, ⟨m₁, hm₁, hz₁⟩, h₁, e1, e2⟩` from `hL y z hyΔ hz (Formalism.MainNotions.CrystallineLiftingBounds.invariant_cocycle_le_gamma_cocycle W hs hp2 T₂ h)`. Establish `hy₁Δ` using `lifta_inv_of_q W R T₁ _ y₁ hy₁.2`. Establish `hz₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ z₁ = z₁`.

Rewrite using `[hz₁]`. Conclude with `(invariant_smul_mem_invariants' W T₁ W.π₀ R.πΔ m₁ hm₁).2`. Establish `h₁Δ : (y₁, z₁) ∈ W.wachCocyclesDelta T₁`. Use `(lifta_mem_Z1DΔ W T₁ y₁ z₁).2 ⟨?_, fun δ hδ => ⟨hy₁Δ δ hδ, hz₁Δ δ hδ⟩⟩` and prove the remaining obligations. Rewrite using `[W.gamK_eq_one hs hp2]`.

Conclude with `h₁`. Take `⟨m₁X, hm₁X, hm₁Xe⟩` from `lifta_π₀_X W R hs T₁ m₁ hm₁.1`. Establish `hf₁` using `(hc1.2 y₁ z₁ ((lifta_Qq W R hs T₁ _ y₁).2 hy₁.1) ⟨m₁X, hm₁X, by rw [hz₁]; exact hm₁Xe⟩ h₁).1`. Use `⟨W.clK T₁ ⟨(y₁, z₁), h₁Δ⟩, (h2b T₁ c1 _).2 ?_, ?_⟩` and prove the remaining obligations. Establish `hr` using `hRes hs hp2 T₁ ⟨(y₁, z₁), h₁Δ⟩`.

Conclude with `hr.symm ▸ hf₁`. Establish `hN` using `hNat hs hp2 F ⟨(y₁, z₁), h₁Δ⟩ ((PD.p ^ (eWA PD.p (Hmax n Mi hi) + eUA PD.p (Mmax n Mi) (JSet (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (Mmax n Mi))) : ℕ) • (⟨(y, z), h⟩ : ↥(W.wachCocyclesDelta T₂))) (by`. Rewrite using `[e1, e2]`. Use the proof step `rfl)`. Use `Eq.trans hN ?_` and prove the remaining obligations.

Use `Eq.trans (map_nsmul (W.clK T₂) _ _) ?_` and prove the remaining obligations. Use `Eq.trans (congrArg _ hcl) ?_` and prove the remaining obligations. Rewrite using `[← liftb_ns (R := O), smul_smul, ← pow_add]`. Use `congr 2`. Simplify using `only [ePA]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coreLiftA_of (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (u : ℤ_[ℓ]ˣ)
    (hu : algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ]) = ((W.χΓ W.gam : Oˣ) : O))
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = W.s)
    (h2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W) (h2c : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexThirdProperty W)
    (h2d : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFourthProperty W) (hExtC : coreExtΔ W) (hD : coreDss W)
    (hNat : W.s = 1 → PD.p ≠ 2 → W.ClKNat) (hRes : Formalism.MainNotions.CrystallineLiftingBounds.coreResK W)
    (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O) (hWA : coreWA W)
    (hKer : liftb_HKer W) (hExact : liftb_HExact W) (hStr : lifta_HStr W) (hExt : liftb_HExt W)
    (hOne : liftb_HOne W) : coreLiftA W := by
  have := liftb_neZero W
  intro hA T₁ T₂ F Mi hi hS hJ1
  have hs : W.s = 1 := hA.2.1
  have hp2 : PD.p ≠ 2 := hA.2.2
  rw [hs] at hv
  obtain ⟨c1, c2, hOnto⟩ := hS
  obtain ⟨T₀, ι, hses, c0⟩ := hKer T₁ T₂ F ⟨c1, c2, hOnto⟩
  have hJ := hJmp T₀ T₁ T₂ ι F hses c0 c1 c2
  have hJ0 : JumpsLet W T₀ Mi hi := fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inl ha))
  have hJ2 : JumpsLet W T₂ Mi hi := fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inr ha))
  have hc0 := h2c T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)
  have hc1 := h2c T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)
  have hd := h2d T₀ T₁ T₂ ι F Mi hi c0 c1 c2 (liftb_jl W T₁ Mi hi hJ1)
  rw [liftb_mx_eq] at hc0 hc1 hd
  have hQ := hc0.1
  have gb₀ := liftb_good_of W T₀ c0 Mi hi (h2 T₀ c0) (h5 T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)) hQ
  have gb₁ := liftb_good_of W T₁ c1 Mi hi (h2 T₁ c1) (h5 T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)) hQ
  have gb₂ := liftb_good_of W T₂ c2 Mi hi (h2 T₂ c2) (h5 T₂ Mi hi c2 (liftb_jl W T₂ Mi hi hJ2)) hQ
  have h90 := uniformizer_ring_and_module_clauses W h9 hA T₀ c0
  have R := lifta_ring_of W h90.1
  have g₀ := lifta_good_of W R hs T₀ _ gb₀ h90.2
  have g₁ := lifta_good_of W R hs T₁ _ gb₁ (uniformizer_ring_and_module_clauses W h9 hA T₁ c1).2
  have g₂ := lifta_good_of W R hs T₂ _ gb₂ (uniformizer_ring_and_module_clauses W h9 hA T₂ c2).2
  have hcard : W.DelF.card = PD.p - 1 := by
    rw [(h9 T₀ c0 hs hp2).1, finrank_eq_one_case_A W hA, Nat.div_one]
  obtain ⟨d, hd1⟩ := lifta_exists_d W hp hcard
  have hE := hExact T₀ T₁ T₂ ι F hses
  have hsat := (h6.2.2 T₀ T₁ T₂ ι F c0 c1 c2 hses).2.2.2.1
  have hCKN : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁,
      W.map F x = (PD.p ^ (eWA PD.p (Hmax n Mi hi)) : ℕ) • y := by
    intro y hy
    obtain ⟨x, hx, hxe⟩ := liftb_kills_all W F _ (hWA hA T₁ T₂ F Mi hi ⟨c1, c2, hOnto⟩ hJ1) y hy
    exact ⟨x, hx, by rw [hxe, lp, liftb_ns]⟩
  have hL := lifta_lifts W hp hA u hu hv h90.1 ι F Mi hi g₀ g₁ g₂ hE hsat
    (eWA PD.p (Hmax n Mi hi)) hses hd d hd1 h90.2 (lifta_cokerΔ W F d hd1 _ hCKN) c0 hJ0 hD
    (jumpSet W T₁ (Mmax n Mi) (Mmax n hi))
    (lifta_jumpSet_mono W T₀ T₁ _ _ (fun τ a ha => (hJ τ a).2 (Or.inl ha))) (hStr hA T₀ c0) (h6.1 T₀ c0)
  apply liftb_LiftF_of PD F
  intro κ hκ
  obtain ⟨c, hc, hcf, rfl⟩ := (liftb_mem_H1fT PD T₂ κ).1 hκ
  obtain ⟨Tp, ι', π', cp, hext⟩ := hExt T₂ c c2 hcf
  obtain ⟨cone, hone0, e, he, hspan, hφe, hγe⟩ := hOne
  have hJp' := hJmp T₂ Tp W.one ι' π' hext.1 c2 cp cone
  have hJp : JumpsLet W Tp Mi hi := by
    intro i τ hτ a ha
    rcases (hJp' τ a).1 ha with h | h
    · exact hJ2 i τ hτ a h
    · rw [hone0 τ a h]
      exact ⟨by simp, by simp⟩
  have hImg : InImgA W π' (eWA PD.p (Hmax n Mi hi)) := by
    obtain ⟨x, hx, hxe⟩ := liftb_kills_all W π' _
      (hWA hA Tp W.one π' Mi hi ⟨cp, cone, hext.1.2.2.1⟩ hJp) e he
    exact ⟨e, he, hspan, hφe, hγe, x, hx, by rw [hxe, lp, liftb_ns, liftb_ns]⟩
  obtain ⟨y, z, h, hy, hz, hcl⟩ := hExtC hA T₂ Tp ι' π' Mi hi c2 cp hJ2 c hc hext _ hImg
  have hΔ := ((lifta_mem_Z1DΔ W T₂ y z).1 h).2
  have hyΔ : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₂ := ⟨hy, fun δ hδ => by
    rw [gammaD_semilinear, (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) _) δ hδ, (hΔ δ hδ).1]⟩
  obtain ⟨y₁, z₁, hy₁, ⟨m₁, hm₁, hz₁⟩, h₁, e1, e2⟩ :=
    hL y z hyΔ hz (Formalism.MainNotions.CrystallineLiftingBounds.invariant_cocycle_le_gamma_cocycle W hs hp2 T₂ h)
  have hy₁Δ := lifta_inv_of_q W R T₁ _ y₁ hy₁.2
  have hz₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ z₁ = z₁ := by
    rw [hz₁]
    exact (invariant_smul_mem_invariants' W T₁ W.π₀ R.πΔ m₁ hm₁).2
  have h₁Δ : (y₁, z₁) ∈ W.wachCocyclesDelta T₁ := by
    refine (lifta_mem_Z1DΔ W T₁ y₁ z₁).2 ⟨?_, fun δ hδ => ⟨hy₁Δ δ hδ, hz₁Δ δ hδ⟩⟩
    rw [W.gamK_eq_one hs hp2]
    exact h₁
  obtain ⟨m₁X, hm₁X, hm₁Xe⟩ := lifta_π₀_X W R hs T₁ m₁ hm₁.1
  have hf₁ := (hc1.2 y₁ z₁ ((lifta_Qq W R hs T₁ _ y₁).2 hy₁.1)
    ⟨m₁X, hm₁X, by rw [hz₁]; exact hm₁Xe⟩ h₁).1
  refine ⟨W.clK T₁ ⟨(y₁, z₁), h₁Δ⟩, (h2b T₁ c1 _).2 ?_, ?_⟩
  · have hr := hRes hs hp2 T₁ ⟨(y₁, z₁), h₁Δ⟩
    exact hr.symm ▸ hf₁
  have hN := hNat hs hp2 F ⟨(y₁, z₁), h₁Δ⟩
    ((PD.p ^ (eWA PD.p (Hmax n Mi hi) + eUA PD.p (Mmax n Mi)
      (JSet (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (Mmax n Mi))) : ℕ) •
        (⟨(y, z), h⟩ : ↥(W.wachCocyclesDelta T₂)))
    (by
      rw [e1, e2]
      rfl)
  refine Eq.trans hN ?_
  refine Eq.trans (map_nsmul (W.clK T₂) _ _) ?_
  refine Eq.trans (congrArg _ hcl) ?_
  rw [← liftb_ns (R := O), smul_smul, ← pow_add]
  congr 2
  simp only [ePA]
  ring

end LiftALocal

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LiftOne

open Module TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

include PD in
/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_nontrivial_iff_subsingleton]`. Apply `PD.not_mem_filtration_two` to reduce the goal to its premises. Rewrite using `[Subsingleton.elim (PD.ι PD.t) 0]`. Conclude with `(PD.Fil 2).zero_mem`.
-/
theorem lone_nontrivial_BdR : Nontrivial BdR := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim (PD.ι PD.t) 0]
  exact (PD.Fil 2).zero_mem

include PD in
/- English proof (translation)
Use `lone_nontrivial_BdR PD` as an intermediate fact. Conclude with `PD.ι.toRingHom.domain_nontrivial`.
-/
theorem lone_nontrivial_B : Nontrivial B := by
  have := lone_nontrivial_BdR PD
  exact PD.ι.toRingHom.domain_nontrivial

def lone_coord {ι : Type} (b : Basis ι Qp V) (i : ι) (C : Type) [AddCommGroup C] [Module Qp C] :
    V ⊗[Qp] C →ₗ[Qp] C :=
  (TensorProduct.lid Qp C).toLinearMap ∘ₗ LinearMap.rTensor C (b.coord i)

/- English proof (translation)
Simplify using `[lone_coord]`.
-/
theorem lone_coord_tmul {ι : Type} (b : Basis ι Qp V) (i : ι) {C : Type} [AddCommGroup C]
    [Module Qp C] (x : V) (c : C) : lone_coord b i C (x ⊗ₜ[Qp] c) = b.coord i x • c := by
  simp [lone_coord]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l c`. Simplify using `only [lone_coord_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]`. Use `congr 1`.

Simplify using `[Basis.coord_apply]`. Consider the case `add x y hx hy => conv_lhs => rw [hx, hy]`. Simplify using `[Finset.sum_add_distrib, TensorProduct.tmul_add]`.
-/
theorem lone_decomp {ι : Type} [Fintype ι] (b : Basis ι Qp V) {C : Type} [AddCommGroup C]
    [Module Qp C] (x : V ⊗[Qp] C) : x = ∑ i, b i ⊗ₜ[Qp] lone_coord b i C x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    simp only [lone_coord_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    simp [Basis.coord_apply]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp [Finset.sum_add_distrib, TensorProduct.tmul_add]

variable (ρ : Representation LL G V) (hρ : ∀ g x, ρ g x = x)

include hρ in
/- English proof (translation)
Simplify using `[actVB, hρ]`.
-/
theorem lone_actB_tmul (g : G) (x : V) (c : B) :
    actVB PD ρ g (x ⊗ₜ[Qp] c) = x ⊗ₜ[Qp] PD.actB g c := by
  simp [actVB, hρ]

include hρ in
/- English proof (translation)
Simplify using `[actVdR, hρ]`.
-/
theorem lone_actdR_tmul (g : G) (x : V) (c : BdR) :
    actVdR PD ρ g (x ⊗ₜ[Qp] c) = x ⊗ₜ[Qp] PD.actdR g c := by
  simp [actVdR, hρ]

include hρ in
/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l c`. Rewrite using `[lone_actB_tmul PD ρ hρ, lone_coord_tmul, lone_coord_tmul]`. Conclude with `(((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp).map_smul _ _ |>.symm`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem lone_coord_actB {ι : Type} (b : Basis ι Qp V) (i : ι) (g : G) (x : V ⊗[Qp] B) :
    lone_coord b i B (actVB PD ρ g x) = PD.actB g (lone_coord b i B x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    rw [lone_actB_tmul PD ρ hρ, lone_coord_tmul, lone_coord_tmul]
    exact (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp).map_smul _ _ |>.symm
  | add x y hx hy => simp only [map_add, hx, hy]

include hρ in
/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l c`. Rewrite using `[lone_actdR_tmul PD ρ hρ, lone_coord_tmul, lone_coord_tmul]`. Conclude with `(((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp).map_smul _ _ |>.symm`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem lone_coord_actdR {ι : Type} (b : Basis ι Qp V) (i : ι) (g : G) (x : V ⊗[Qp] BdR) :
    lone_coord b i BdR (actVdR PD ρ g x) = PD.actdR g (lone_coord b i BdR x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    rw [lone_actdR_tmul PD ρ hρ, lone_coord_tmul, lone_coord_tmul]
    exact (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp).map_smul _ _ |>.symm
  | add x y hx hy => simp only [map_add, hx, hy]

def lone_map : V ⊗[Qp] K₀ →ₗ[LL] V ⊗[Qp] B :=
  AlgebraTensorModule.lTensor LL V ((Algebra.linearMap K₀ B).restrictScalars Qp)

include hρ in
/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hinv : ∀ g, actVB PD ρ g x = x`. Introduce `g`. Use `(Submodule.mem_iInf _).mp hx g` as an intermediate fact.

Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Conclude with `this`. Set `b` to `Module.finBasis Qp V`. Establish `hc : ∀ i, ∃ c : K₀, algebraMap K₀ B c = lone_coord b i B x`. Introduce `i`.

Apply `PD.invB` to reduce the goal to its premises. Introduce `g`. Rewrite using `[← lone_coord_actB PD ρ hρ, hinv]`. Use `choose c hc using hc`. Use `⟨∑ i, b i ⊗ₜ[Qp] c i, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sum]`. Use `conv_rhs => rw [lone_decomp b x]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [lone_map, AlgebraTensorModule.lTensor_tmul]`. Rewrite using `[← hc i]`.

Both sides reduce to the same expression. Introduce and unpack `_ ⟨y, rfl⟩`. Use `(Submodule.mem_iInf _).mpr fun g => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul l k`. Simplify using `only [lone_map, AlgebraTensorModule.lTensor_tmul, lone_actB_tmul PD ρ hρ]`. Simplify using the standard rewrite rules. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem lone_Dcris_eq [FiniteDimensional Qp V] :
    Dcris PD ρ = LinearMap.range (lone_map (Qp := Qp) (K₀ := K₀) (B := B) (LL := LL) (V := V)) := by
  apply le_antisymm
  · intro x hx
    have hinv : ∀ g, actVB PD ρ g x = x := by
      intro g
      have := (Submodule.mem_iInf _).mp hx g
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      exact this
    let b := Module.finBasis Qp V
    have hc : ∀ i, ∃ c : K₀, algebraMap K₀ B c = lone_coord b i B x := by
      intro i
      apply PD.invB
      intro g
      rw [← lone_coord_actB PD ρ hρ, hinv]
    choose c hc using hc
    refine ⟨∑ i, b i ⊗ₜ[Qp] c i, ?_⟩
    rw [map_sum]
    conv_rhs => rw [lone_decomp b x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [lone_map, AlgebraTensorModule.lTensor_tmul]
    rw [← hc i]
    rfl
  · rintro _ ⟨y, rfl⟩
    refine (Submodule.mem_iInf _).mpr fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul l k =>
      simp only [lone_map, AlgebraTensorModule.lTensor_tmul, lone_actB_tmul PD ρ hρ]
      simp
    | add a b ha hb => simp only [map_add, ha, hb]

include PD in
/- English proof (translation)
Use `lone_nontrivial_B PD` as an intermediate fact. Establish `hi : Function.Injective ((Algebra.linearMap K₀ B).restrictScalars Qp)` using `(algebraMap K₀ B).injective`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ hi`.
-/
theorem lone_map_injective :
    Function.Injective (lone_map (Qp := Qp) (K₀ := K₀) (B := B) (LL := LL) (V := V)) := by
  have := lone_nontrivial_B PD
  have hi : Function.Injective ((Algebra.linearMap K₀ B).restrictScalars Qp) :=
    (algebraMap K₀ B).injective
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ hi

include hρ in

/- English proof (translation)
Use `PD.finK₀` as an intermediate fact. Unfold `IsCrys`. Rewrite using `[lone_Dcris_eq PD ρ hρ, LinearMap.finrank_range_of_inj (lone_map_injective PD), Module.finrank_tensorProduct, mul_comm]`.
-/
theorem lone_isCrys [FiniteDimensional Qp V] [FiniteDimensional LL V] : IsCrys PD ρ := by
  have := PD.finK₀
  unfold IsCrys
  rw [lone_Dcris_eq PD ρ hρ, LinearMap.finrank_range_of_inj (lone_map_injective PD),
    Module.finrank_tensorProduct, mul_comm]

include PD in
/- English proof (translation)
The claim follows from `antitone_int_of_succ_le PD.Fil_anti`.
-/
theorem lone_Fil_anti : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti

include PD in

/- English proof (translation)
Apply `lone_Fil_anti PD ha` to reduce the goal to its premises. Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `(PD.Fil 0).smul_mem c PD.one_mem`.
-/
theorem lone_K_mem (c : K) (a : ℤ) (ha : a ≤ 0) : algebraMap K BdR c ∈ PD.Fil a := by
  apply lone_Fil_anti PD ha
  rw [Algebra.algebraMap_eq_smul_one]
  exact (PD.Fil 0).smul_mem c PD.one_mem

include PD in

/- English proof (translation)
Introduce `h`. Use `lone_nontrivial_BdR PD` as an intermediate fact. Establish `hk : ∀ k : ℕ, (1 : BdR) ∈ PD.Fil ((k : ℤ) + 1)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => simpa using h`. Consider the case `succ k ih`. Use `PD.Fil_mul _ _ 1 1 ih h` as an intermediate fact. Rewrite `this` using `[mul_one]`. Use `push_cast`.

Conclude with `this`. Apply `one_ne_zero (α := BdR)` to reduce the goal to its premises. Apply `PD.Fil_sep` to reduce the goal to its premises. Introduce `a`. Conclude with `lone_Fil_anti PD (by have := Int.self_le_toNat a; omega : a ≤ ((a.toNat : ℕ) : ℤ) + 1) (hk a.toNat)`.
-/
theorem lone_one_notMem : (1 : BdR) ∉ PD.Fil 1 := by
  intro h
  have := lone_nontrivial_BdR PD
  have hk : ∀ k : ℕ, (1 : BdR) ∈ PD.Fil ((k : ℤ) + 1) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have := PD.Fil_mul _ _ 1 1 ih h
      rw [mul_one] at this
      push_cast
      exact this
  apply one_ne_zero (α := BdR)
  apply PD.Fil_sep
  intro a
  exact lone_Fil_anti PD (by have := Int.self_le_toNat a; omega : a ≤ ((a.toNat : ℕ) : ℤ) + 1) (hk a.toNat)

include PD in

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Apply `lone_one_notMem PD` to reduce the goal to its premises. Establish `h1 : algebraMap K BdR c ∈ PD.Fil 1` using `lone_Fil_anti PD ha h`. Use `(PD.Fil 1).smul_mem c⁻¹ h1` as an intermediate fact. Rewrite `this` using `[Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc, map_one]`. Then use the resulting hypothesis.
-/
theorem lone_K_inter (c : K) (a : ℤ) (ha : 1 ≤ a) (h : algebraMap K BdR c ∈ PD.Fil a) : c = 0 := by
  by_contra hc
  apply lone_one_notMem PD
  have h1 : algebraMap K BdR c ∈ PD.Fil 1 := lone_Fil_anti PD ha h
  have := (PD.Fil 1).smul_mem c⁻¹ h1
  rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc, map_one] at this

/- English proof (translation)
Take `⟨y, rfl⟩` from `hx`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l f`. Rewrite using `[AlgebraTensorModule.map_tmul, lone_coord_tmul]`.

Conclude with `((PD.Fil a).restrictScalars Qp).smul_mem _ f.2`. Consider the case `add y z hy hz`. Rewrite using `[map_add, map_add]`. Conclude with `(PD.Fil a).add_mem hy hz`.
-/
theorem lone_coord_FilV {ι : Type} (b : Basis ι Qp V) (i : ι) (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) : lone_coord b i BdR x ∈ PD.Fil a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul l f =>
    rw [AlgebraTensorModule.map_tmul, lone_coord_tmul]
    exact ((PD.Fil a).restrictScalars Qp).smul_mem _ f.2
  | add y z hy hz =>
    rw [map_add, map_add]
    exact (PD.Fil a).add_mem hy hz

include hρ in

/- English proof (translation)
Apply `PD.invdR` to reduce the goal to its premises. Introduce `g`. Use `(Submodule.mem_iInf _).mp hx g` as an intermediate fact. Rewrite `this` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Rewrite using `[← lone_coord_actdR PD ρ hρ, this]`.
-/
theorem lone_coord_DdR {ι : Type} (b : Basis ι Qp V) (i : ι) (x : V ⊗[Qp] BdR)
    (hx : x ∈ DdR PD ρ) : ∃ c : K, algebraMap K BdR c = lone_coord b i BdR x := by
  apply PD.invdR
  intro g
  have := (Submodule.mem_iInf _).mp hx g
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  rw [← lone_coord_actdR PD ρ hρ, this]

include hρ in
/- English proof (translation)
Introduce `x hx`. Set `b` to `Module.finBasis Qp V`. Rewrite using `[lone_decomp b x]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `lone_coord_DdR PD ρ hρ b i x hx`.

Use `⟨b i ⊗ₜ[Qp] (⟨algebraMap K BdR c, lone_K_mem PD c a ha⟩ : ↥((PD.Fil a).restrictScalars Qp)), ?_⟩` and prove the remaining obligations. Rewrite using `[AlgebraTensorModule.map_tmul, ← hc]`. Both sides reduce to the same expression.
-/
theorem lone_DdR_le [FiniteDimensional Qp V] (a : ℤ) (ha : a ≤ 0) :
    DdR PD ρ ≤ FilV PD (LL := LL) (V := V) a := by
  intro x hx
  let b := Module.finBasis Qp V
  rw [lone_decomp b x]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨c, hc⟩ := lone_coord_DdR PD ρ hρ b i x hx
  refine ⟨b i ⊗ₜ[Qp] (⟨algebraMap K BdR c, lone_K_mem PD c a ha⟩ :
    ↥((PD.Fil a).restrictScalars Qp)), ?_⟩
  rw [AlgebraTensorModule.map_tmul, ← hc]
  rfl

include hρ in
/- English proof (translation)
Set `b` to `Module.finBasis Qp V`. Rewrite using `[lone_decomp b x]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `lone_coord_DdR PD ρ hρ b i x hx`. Establish `h0 : c = 0` using `lone_K_inter PD c a ha (by rw [hc]; exact lone_coord_FilV PD b i a x hx')`.

Rewrite using `[← hc, h0, map_zero, TensorProduct.tmul_zero]`.
-/
theorem lone_DdR_inf [FiniteDimensional Qp V] (a : ℤ) (ha : 1 ≤ a) (x : V ⊗[Qp] BdR)
    (hx : x ∈ DdR PD ρ) (hx' : x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  let b := Module.finBasis Qp V
  rw [lone_decomp b x]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨c, hc⟩ := lone_coord_DdR PD ρ hρ b i x hx
  have h0 : c = 0 := lone_K_inter PD c a ha (by rw [hc]; exact lone_coord_FilV PD b i a x hx')
  rw [← hc, h0, map_zero, TensorProduct.tmul_zero]

include hρ in

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Apply `h` to reduce the goal to its premises. Unfold `FildR`. Break down `lt_or_gt_of_ne ha with h1 | h1` into its components or cases. Establish `e1 : DdRE PD ρ τ ≤ FilV PD (LL` using `LL) (V := V) (a + 1) := le_trans inf_le_left (lone_DdR_le PD ρ hρ (a + 1) (by omega))`.

Establish `e2 : DdRE PD ρ τ ≤ FilV PD (LL` using `LL) (V := V) a := le_trans inf_le_left (lone_DdR_le PD ρ hρ a (by omega))`. Rewrite using `[inf_eq_left.2 e1, inf_eq_left.2 e2]`. Establish `e : ∀ c : ℤ, 1 ≤ c → DdRE PD ρ τ ⊓ FilV PD (LL` using `LL) (V := V) c = ⊥ := by`. Introduce `c hc`. Rewrite using `[eq_bot_iff]`.

Introduce and unpack `x ⟨hx1, hx2⟩`. Conclude with `lone_DdR_inf PD ρ hρ c hc x hx1.1 hx2`. Rewrite using `[e (a + 1) (by omega), e a (by omega)]`.
-/
theorem lone_jump [FiniteDimensional Qp V] (τ : K →ₐ[Qp] LL) (a : ℤ) (h : IsJumpV PD ρ τ a) :
    a = 0 := by
  by_contra ha
  apply h
  unfold FildR
  rcases lt_or_gt_of_ne ha with h1 | h1
  · have e1 : DdRE PD ρ τ ≤ FilV PD (LL := LL) (V := V) (a + 1) :=
      le_trans inf_le_left (lone_DdR_le PD ρ hρ (a + 1) (by omega))
    have e2 : DdRE PD ρ τ ≤ FilV PD (LL := LL) (V := V) a :=
      le_trans inf_le_left (lone_DdR_le PD ρ hρ a (by omega))
    rw [inf_eq_left.2 e1, inf_eq_left.2 e2]
  · have e : ∀ c : ℤ, 1 ≤ c → DdRE PD ρ τ ⊓ FilV PD (LL := LL) (V := V) c = ⊥ := by
      intro c hc
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      exact lone_DdR_inf PD ρ hρ c hc x hx1.1 hx2
    rw [e (a + 1) (by omega), e a (by omega)]

end LiftOne

section LiftOneW

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

/- English proof (translation)
Establish `: FiniteDimensional Qp W.one.V` using `FiniteDimensional.trans Qp LL W.one.V`. Conclude with `⟨lone_isCrys PD W.one.ρ W.one_triv, fun τ a h => lone_jump PD W.one.ρ W.one_triv τ a h⟩`.
-/
theorem lone_HOne0 (W : LocWach PD LL O v n) [FiniteDimensional Qp LL] : liftb_HOne0 W := by
  have : FiniteDimensional Qp W.one.V := FiniteDimensional.trans Qp LL W.one.V
  exact ⟨lone_isCrys PD W.one.ρ W.one_triv, fun τ a h => lone_jump PD W.one.ρ W.one_triv τ a h⟩

end LiftOneW

/- English proof (translation)
Establish `: FiniteDimensional ℚ_[l] ↥LL.1` using `LL.2`. Conclude with `lone_HOne0 _`.
-/
theorem lone_HOne0_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) : liftb_HOne0 ((HW l).W K s LL h) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact lone_HOne0 _

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section LiftInj

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

abbrev linj_res {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) : ↥T.L.T →ₗ[O] ↥T'.L.T :=
  (f.f.restrictScalars O).restrict f.T_le

/- English proof (translation)
Take `⟨hinj, _, hOnto, hex, hsat⟩` from `hses`. Establish `hsurj : Function.Surjective (linj_res π)` using `fun y => by`. Take `⟨x, hx, hxy⟩` from `hOnto y y.2`. Conclude with `⟨⟨x, hx⟩, Subtype.ext hxy⟩`. Establish `: Module.Free O ↥T₂.L.T` using `T₂.L.free`.

Take `⟨s, hs⟩` from `Module.projective_lifting_property (linj_res π) LinearMap.id hsurj`. Establish `hι : Function.Injective (linj_res ι)` using `fun a b h => Subtype.ext (hinj (congrArg Subtype.val h))`. Establish `hker : ∀ x : ↥T₁.L.T, linj_res π x = 0 → ∃ y : ↥T₀.L.T, linj_res ι y = x` using `fun x hx => by`. Take `⟨y, hy⟩` from `(hex (x : T₁.V)).1 (congrArg Subtype.val hx)`. Conclude with `⟨⟨y, hsat y (by rw [hy]; exact x.2)⟩, Subtype.ext hy⟩`.

Establish `hπι : linj_res π ∘ₗ linj_res ι = 0`. Use extensionality with `y`. Conclude with `(hex _).2 ⟨(y : T₀.V), rfl⟩`. Establish `hsπ : ∀ y, linj_res π (s y) = y` using `fun y => LinearMap.congr_fun hs y`. Set `e` to `LinearEquiv.ofInjective (linj_res ι) hι`.

Set `q : ↥T₁.L.T →ₗ[O] ↥T₁.L.T` to `LinearMap.id - s ∘ₗ linj_res π`. Set `p : ↥T₁.L.T →ₗ[O] ↥(LinearMap.range (linj_res ι))` to `q.codRestrict (LinearMap.range (linj_res ι)) (fun x => by`. Take `⟨y, hy⟩` from `hker (q x) (by`. Simplify using `only [q, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hsπ, sub_self])`. Conclude with `⟨y, hy⟩)`.

Establish `hιr : linj_res ι ∘ₗ (e.symm.toLinearMap ∘ₗ p) = LinearMap.id - s ∘ₗ linj_res π` using `by ext1 x`. Establish `h1 : (e (e.symm (p x)) : ↥(LinearMap.range (linj_res ι))) = p x` using `e.apply_symm_apply _`. Establish `h2` using `congrArg Subtype.val h1`. Rewrite `h2` using `[LinearEquiv.ofInjective_apply]`. Conclude with `h2`.

Use `⟨e.symm.toLinearMap ∘ₗ p, s, ?_, hιr, hπι⟩` and prove the remaining obligations. Use `ext1 y`. Apply `hι` to reduce the goal to its premises. Establish `h3` using `LinearMap.congr_fun hιr (linj_res ι y)`. Establish `h4 : linj_res π (linj_res ι y) = 0` using `LinearMap.congr_fun hπι y`.

Simplify using `only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, h4, map_zero, sub_zero] at h3 ⊢`. Conclude with `h3`.
-/
theorem linj_split {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)
    (hses : IsSESLat (Qp := Qp) ι π) :
    ∃ (r : ↥T₁.L.T →ₗ[O] ↥T₀.L.T) (s : ↥T₂.L.T →ₗ[O] ↥T₁.L.T),
      r ∘ₗ linj_res ι = LinearMap.id ∧ linj_res ι ∘ₗ r = LinearMap.id - s ∘ₗ linj_res π ∧
      linj_res π ∘ₗ linj_res ι = 0 := by
  obtain ⟨hinj, _, hOnto, hex, hsat⟩ := hses
  have hsurj : Function.Surjective (linj_res π) := fun y => by
    obtain ⟨x, hx, hxy⟩ := hOnto y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have : Module.Free O ↥T₂.L.T := T₂.L.free
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (linj_res π) LinearMap.id hsurj
  have hι : Function.Injective (linj_res ι) := fun a b h =>
    Subtype.ext (hinj (congrArg Subtype.val h))
  have hker : ∀ x : ↥T₁.L.T, linj_res π x = 0 → ∃ y : ↥T₀.L.T, linj_res ι y = x := fun x hx => by
    obtain ⟨y, hy⟩ := (hex (x : T₁.V)).1 (congrArg Subtype.val hx)
    exact ⟨⟨y, hsat y (by rw [hy]; exact x.2)⟩, Subtype.ext hy⟩
  have hπι : linj_res π ∘ₗ linj_res ι = 0 := by
    ext y
    exact (hex _).2 ⟨(y : T₀.V), rfl⟩
  have hsπ : ∀ y, linj_res π (s y) = y := fun y => LinearMap.congr_fun hs y
  let e := LinearEquiv.ofInjective (linj_res ι) hι
  let q : ↥T₁.L.T →ₗ[O] ↥T₁.L.T := LinearMap.id - s ∘ₗ linj_res π
  let p : ↥T₁.L.T →ₗ[O] ↥(LinearMap.range (linj_res ι)) :=
    q.codRestrict (LinearMap.range (linj_res ι)) (fun x => by
      obtain ⟨y, hy⟩ := hker (q x) (by
        simp only [q, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, hsπ,
          sub_self])
      exact ⟨y, hy⟩)
  have hιr : linj_res ι ∘ₗ (e.symm.toLinearMap ∘ₗ p) = LinearMap.id - s ∘ₗ linj_res π := by
    ext1 x
    have h1 : (e (e.symm (p x)) : ↥(LinearMap.range (linj_res ι))) = p x := e.apply_symm_apply _
    have h2 := congrArg Subtype.val h1
    rw [LinearEquiv.ofInjective_apply] at h2
    exact h2
  refine ⟨e.symm.toLinearMap ∘ₗ p, s, ?_, hιr, hπι⟩
  ext1 y
  apply hι
  have h3 := LinearMap.congr_fun hιr (linj_res ι y)
  have h4 : linj_res π (linj_res ι y) = 0 := LinearMap.congr_fun hπι y
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, h4, map_zero,
    sub_zero] at h3 ⊢
  exact h3

/- English proof (translation)
Rewrite using `[← LinearMap.comp_apply, ← TensorProduct.map_comp]`.
-/
theorem linj_tmap {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [Module O M₁] [AddCommGroup M₂] [Module O M₂]
    [AddCommGroup M₃] [Module O M₃] (a b : RW →ₗ[O] RW) (f : M₁ →ₗ[O] M₂) (g : M₂ →ₗ[O] M₃)
    (z : RW ⊗[O] M₁) :
    TensorProduct.map b g (TensorProduct.map a f z) = TensorProduct.map (b ∘ₗ a) (g ∘ₗ f) z := by
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]

/- English proof (translation)
Take `⟨r, s, hr, _, _⟩` from `linj_split ι π hses`. Introduce `x y hxy`. Apply `E.jD_inj T₀` to reduce the goal to its premises. Establish `h` using `congrArg (E.jD T₁) hxy`. Rewrite `h` using `[E.jD_map, E.jD_map]`.

Establish `h'` using `congrArg (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r) h`. Rewrite `h'` using `[linj_tmap, linj_tmap, hr, LinearMap.id_comp, TensorProduct.map_id]`. Conclude with `h'`.
-/
theorem linj_map_inj (W : LocWach PD LL O v n) (E : EtTie W RA RW inclR φR gR πA)
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)
    (hses : IsSESLat (Qp := Qp) ι π) : Function.Injective (W.map ι) := by
  obtain ⟨r, s, hr, _, _⟩ := linj_split ι π hses
  intro x y hxy
  apply E.jD_inj T₀
  have h := congrArg (E.jD T₁) hxy
  rw [E.jD_map, E.jD_map] at h
  have h' := congrArg (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r) h
  rw [linj_tmap, linj_tmap, hr, LinearMap.id_comp, TensorProduct.map_id] at h'
  exact h'

/- English proof (translation)
Take `⟨r, s, _, _, h0⟩` from `linj_split ι π hses`. Apply `E.jD_inj T₂` to reduce the goal to its premises. Rewrite using `[E.jD_map, E.jD_map, linj_tmap, h0, TensorProduct.map_zero_right, map_zero]`. Both sides reduce to the same expression.
-/
theorem linj_map_zero (W : LocWach PD LL O v n) (E : EtTie W RA RW inclR φR gR πA)
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)
    (hses : IsSESLat (Qp := Qp) ι π) (x : W.DD T₀) : W.map π (W.map ι x) = 0 := by
  obtain ⟨r, s, _, _, h0⟩ := linj_split ι π hses
  apply E.jD_inj T₂
  rw [E.jD_map, E.jD_map, linj_tmap, h0, TensorProduct.map_zero_right, map_zero]
  rfl

def linj_HMid (W : LocWach PD LL O v n) : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → ∀ x : W.DD T₁, W.map π x = 0 → ∃ x₀, W.map ι x₀ = x

/- English proof (translation)
Introduce `T₀ T₁ T₂ ι π hses` and use `⟨linj_map_inj W E ι π hses, fun x => ⟨h T₀ T₁ T₂ ι π hses x, by rintro ⟨x₀, rfl⟩ exact linj_map_zero W E ι π hses x₀⟩⟩`.
-/
theorem linj_HExact_of (W : LocWach PD LL O v n) (E : EtTie W RA RW inclR φR gR πA)
    (h : linj_HMid W) : liftb_HExact W := fun T₀ T₁ T₂ ι π hses =>
  ⟨linj_map_inj W E ι π hses, fun x => ⟨h T₀ T₁ T₂ ι π hses x, by
    rintro ⟨x₀, rfl⟩
    exact linj_map_zero W E ι π hses x₀⟩⟩

/- English proof (translation)
Take `⟨r, s, hr, hιr, _⟩` from `linj_split ι π hses`. Introduce `x hx`. Establish `hπ : TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res π) (E.jD T₁ x) = 0`. Rewrite using `[← E.jD_map, hx, map_zero]`. Establish `hb : TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res ι) (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r (E.jD T₁ x)) = E.jD T₁ x`.

Establish `hsum : linj_res ι ∘ₗ r + s ∘ₗ linj_res π = LinearMap.id` using `by rw [hιr, sub_add_cancel]`. Establish `h1 : TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res ι ∘ₗ r + s ∘ₗ linj_res π) (E.jD T₁ x) = E.jD T₁ x` using `by rw [hsum, TensorProduct.map_id, LinearMap.id_apply]`. Establish `h2 : TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (s ∘ₗ linj_res π) (E.jD T₁ x) = TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) s (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res π) (E.jD T₁ x))`. Rewrite using `[linj_tmap, LinearMap.id_comp]`. Rewrite `h1` using `[TensorProduct.map_add_right, LinearMap.add_apply, h2, hπ, map_zero, add_zero]`.

Rewrite using `[linj_tmap, LinearMap.id_comp]`. Conclude with `h1`. Establish `hinjT : Function.Injective (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res ι))`. Introduce `a b hab`. Establish `h'` using `congrArg (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r) hab`.

Rewrite `h'` using `[linj_tmap, linj_tmap, hr, LinearMap.id_comp, TensorProduct.map_id]`. Conclude with `h'`. Take `⟨x₀, hx₀⟩` from `hF₀ _ (hS r _ (hF₁ x)) (by`. Introduce `g hg`. Apply `hinjT` to reduce the goal to its premises.

Establish `hact : linj_res ι ∘ₗ T₀.actT g = T₁.actT g ∘ₗ linj_res ι`. Use extensionality with `y`. Conclude with `ι.equiv g (y : T₀.V)`. Establish `h1 : TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res ι) (TWact (gR g) T₀ g (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r (E.jD T₁ x))) = TWact (gR g) T₁ g (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res ι) (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r ( …`. Unfold `TWact`.

Rewrite using `[linj_tmap, linj_tmap _ _ (linj_res ι), hact, LinearMap.id_comp, LinearMap.comp_id]`. Rewrite using `[h1, hb, ← E.jD_act, hg, W.γD_one])`. Use `⟨x₀, E.jD_inj T₁ ?_⟩` and prove the remaining obligations. Rewrite using `[E.jD_map, hx₀, hb]`.
-/
theorem linj_mid (W : LocWach PD LL O v n) (E : EtTie W RA RW inclR φR gR πA)
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)
    (hses : IsSESLat (Qp := Qp) ι π) (S₀ : Set (TW RW T₀)) (S₁ : Set (TW RW T₁))
    (hS : ∀ r : ↥T₁.L.T →ₗ[O] ↥T₀.L.T, ∀ y ∈ S₁,
      TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r y ∈ S₀)
    (hF₀ : ∀ b, b ∈ S₀ → (∀ g, W.resΓ g = 1 → TWact (gR g) T₀ g b = b) → ∃ x₀, E.jD T₀ x₀ = b)
    (hF₁ : ∀ x, E.jD T₁ x ∈ S₁) :
    ∀ x : W.DD T₁, W.map π x = 0 → ∃ x₀, W.map ι x₀ = x := by
  obtain ⟨r, s, hr, hιr, _⟩ := linj_split ι π hses
  intro x hx
  have hπ : TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res π) (E.jD T₁ x) = 0 := by
    rw [← E.jD_map, hx, map_zero]
  have hb : TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res ι)
      (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r (E.jD T₁ x)) = E.jD T₁ x := by
    have hsum : linj_res ι ∘ₗ r + s ∘ₗ linj_res π = LinearMap.id := by rw [hιr, sub_add_cancel]
    have h1 : TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res ι ∘ₗ r + s ∘ₗ linj_res π)
        (E.jD T₁ x) = E.jD T₁ x := by rw [hsum, TensorProduct.map_id, LinearMap.id_apply]
    have h2 : TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (s ∘ₗ linj_res π) (E.jD T₁ x) =
        TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) s
          (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res π) (E.jD T₁ x)) := by
      rw [linj_tmap, LinearMap.id_comp]
    rw [TensorProduct.map_add_right, LinearMap.add_apply, h2, hπ, map_zero, add_zero] at h1
    rw [linj_tmap, LinearMap.id_comp]
    exact h1
  have hinjT : Function.Injective
      (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res ι)) := by
    intro a b hab
    have h' := congrArg (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r) hab
    rw [linj_tmap, linj_tmap, hr, LinearMap.id_comp, TensorProduct.map_id] at h'
    exact h'
  obtain ⟨x₀, hx₀⟩ := hF₀ _ (hS r _ (hF₁ x)) (by
    intro g hg
    apply hinjT
    have hact : linj_res ι ∘ₗ T₀.actT g = T₁.actT g ∘ₗ linj_res ι := by
      ext y
      exact ι.equiv g (y : T₀.V)
    have h1 : TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res ι)
        (TWact (gR g) T₀ g (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r (E.jD T₁ x))) =
        TWact (gR g) T₁ g (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) (linj_res ι)
          (TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) r (E.jD T₁ x))) := by
      unfold TWact
      rw [linj_tmap, linj_tmap _ _ (linj_res ι), hact, LinearMap.id_comp, LinearMap.comp_id]
    rw [h1, hb, ← E.jD_act, hg, W.γD_one])
  refine ⟨x₀, E.jD_inj T₁ ?_⟩
  rw [E.jD_map, hx₀, hb]

end LiftInj

section LiftInjD

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {H : LocHW l P} {AI : LocAinf l P} {K : FinExt l} {s : ℕ}
    {LL : FinExt l} {h : Good K s LL}

end LiftInjD

/- English proof (translation)
The claim follows from `linj_map_inj _ ((F l).E K s LL h).tie ι π hses`.
-/
theorem linj_left_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) {T₀ T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)} (ι : LatHom T₀.L T₁.L)
    (π : LatHom T₁.L T₂.L) (hses : IsSESLat (Qp := ℚ_[l]) ι π) :
    Function.Injective (((HW l).W K s LL h).map ι) :=
  linj_map_inj _ ((F l).E K s LL h).tie ι π hses

def linjMidOpen (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    linj_HMid ((HW l).W K s LL h)

/- English proof (translation)
The claim follows from `linj_HExact_of _ ((F l).E K s LL h).tie (hM l K s LL h)`.
-/
theorem linj_HExact_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (hM : linjMidOpen D HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (h : Good K s LL) : liftb_HExact ((HW l).W K s LL h) :=
  linj_HExact_of _ ((F l).E K s LL h).tie (hM l K s LL h)

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section LiftExt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def lext_act {T U : LocLat G Qp LL O} (lam : U.V →ₗ[LL] LL) (c : G → T.V) (g : G) :
    T.V × U.V →ₗ[LL] T.V × U.V :=
  (((T.ρ g).comp (LinearMap.fst LL T.V U.V)) +
    ((lam.smulRight (c g)).comp (LinearMap.snd LL T.V U.V))).prod (LinearMap.snd LL T.V U.V)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lext_act_apply {T U : LocLat G Qp LL O} (lam : U.V →ₗ[LL] LL) (c : G → T.V) (g : G)
    (z : T.V × U.V) : lext_act lam c g z = (T.ρ g z.1 + lam z.2 • c g, z.2) := rfl

def lext_rep {T U : LocLat G Qp LL O} (lam : U.V →ₗ[LL] LL) (c : G → T.V)
    (hc : ∀ g h, c (g * h) = c g + T.ρ g (c h)) : Representation LL G (T.V × U.V) where
  toFun := lext_act lam c
  map_one' := by
    have h1 : c 1 = 0 := by
      have := hc 1 1
      rw [mul_one, map_one] at this
      simpa using this
    ext z <;> simp [lext_act_apply, h1]
  map_mul' := fun g h => by
    apply LinearMap.ext
    intro z
    rw [Module.End.mul_apply, lext_act_apply, lext_act_apply, lext_act_apply, hc, map_mul]
    ext
    · simp only [Module.End.mul_apply, map_add, map_smul, smul_add]
      abel
    · rfl

def lext_prodEquiv {M M' : Type} [AddCommGroup M] [AddCommGroup M'] [Module O M] [Module O M']
    (p : Submodule O M) (q : Submodule O M') : ↥(p.prod q) ≃ₗ[O] ↥p × ↥q where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun w := ⟨(w.1.1, w.2.1), ⟨w.1.2, w.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[reducible] def lext_Tp [IsTopologicalRing LL] (T U : LocLat G Qp LL O) (lam : U.V →ₗ[LL] LL)
    (c : G → T.V) (hc : c ∈ latticeCocycles T.L) (hlam : ∀ y ∈ U.L.T, ∃ o : O, lam y = algebraMap O LL o) :
    LocLat G Qp LL O where
  V := T.V × U.V
  ρ := lext_rep lam c hc.1.2
  cont := fun z => ((T.cont z.1).add (hc.1.1.const_smul (lam z.2))).prodMk continuous_const
  L :=
    { T := T.L.T.prod U.L.T
      stable := fun g z hz => by
        refine ⟨T.L.T.add_mem (T.L.stable g _ hz.1) ?_, hz.2⟩
        obtain ⟨o, ho⟩ := hlam z.2 hz.2
        change lam z.2 • c g ∈ T.L.T
        rw [ho, algebraMap_smul]
        exact T.L.T.smul_mem o (hc.2 g (Set.mem_univ g))
      fg := T.L.fg.prod U.L.fg
      free := by
        have := T.L.free
        have := U.L.free
        exact Module.Free.of_equiv (lext_prodEquiv T.L.T U.L.T).symm
      span := by
        rw [eq_top_iff]
        rintro ⟨x, y⟩ -
        have hx : x ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
        have hy : y ∈ Submodule.span LL (U.L.T : Set U.V) := by rw [U.L.span]; trivial
        have h1 : (Submodule.span LL (T.L.T : Set T.V)).map (LinearMap.inl LL T.V U.V) ≤
            Submodule.span LL ((T.L.T.prod U.L.T : Submodule O (T.V × U.V)) : Set (T.V × U.V)) := by
          rw [Submodule.map_span]
          apply Submodule.span_mono
          rintro _ ⟨t, ht, rfl⟩
          exact ⟨ht, U.L.T.zero_mem⟩
        have h2 : (Submodule.span LL (U.L.T : Set U.V)).map (LinearMap.inr LL T.V U.V) ≤
            Submodule.span LL ((T.L.T.prod U.L.T : Submodule O (T.V × U.V)) : Set (T.V × U.V)) := by
          rw [Submodule.map_span]
          apply Submodule.span_mono
          rintro _ ⟨t, ht, rfl⟩
          exact ⟨T.L.T.zero_mem, ht⟩
        have : ((x, y) : T.V × U.V) = LinearMap.inl LL T.V U.V x + LinearMap.inr LL T.V U.V y := by
          simp
        rw [this]
        exact Submodule.add_mem _ (h1 ⟨x, hx, rfl⟩) (h2 ⟨y, hy, rfl⟩) }

def lext_ι [IsTopologicalRing LL] (T U : LocLat G Qp LL O) (lam : U.V →ₗ[LL] LL)
    (c : G → T.V) (hc : c ∈ latticeCocycles T.L) (hlam : ∀ y ∈ U.L.T, ∃ o : O, lam y = algebraMap O LL o) :
    LatHom T.L (lext_Tp T U lam c hc hlam).L where
  f := LinearMap.inl LL T.V U.V
  equiv := fun g x => by
    change (T.ρ g x, (0 : U.V)) = (T.ρ g x + lam 0 • c g, (0 : U.V))
    simp
  cont := continuous_id.prodMk continuous_const
  T_le := fun x hx => ⟨hx, U.L.T.zero_mem⟩

def lext_π [IsTopologicalRing LL] (T U : LocLat G Qp LL O) (lam : U.V →ₗ[LL] LL)
    (c : G → T.V) (hc : c ∈ latticeCocycles T.L) (hlam : ∀ y ∈ U.L.T, ∃ o : O, lam y = algebraMap O LL o)
    (htriv : ∀ g x, U.ρ g x = x) : LatHom (lext_Tp T U lam c hc hlam).L U.L where
  f := LinearMap.snd LL T.V U.V
  equiv := fun g z => (htriv g z.2).symm
  cont := continuous_snd
  T_le := fun _ hz => hz.2

/- English proof (translation)
Use `⟨LinearMap.inl_injective, LinearMap.snd_surjective, fun y hy => ⟨(0, y), ⟨T.L.T.zero_mem, hy⟩, rfl⟩, fun z => ⟨fun h => ⟨z.1, ?_⟩, ?_⟩, fun y hy => hy.1⟩` and prove the remaining obligations. Conclude with `Prod.ext rfl (Eq.symm h)`. Introduce and unpack `⟨y, rfl⟩`. Both sides reduce to the same expression.
-/
theorem lext_ses [IsTopologicalRing LL] (T U : LocLat G Qp LL O) (lam : U.V →ₗ[LL] LL)
    (c : G → T.V) (hc : c ∈ latticeCocycles T.L) (hlam : ∀ y ∈ U.L.T, ∃ o : O, lam y = algebraMap O LL o)
    (htriv : ∀ g x, U.ρ g x = x) :
    IsSESLat (Qp := Qp) (lext_ι T U lam c hc hlam) (lext_π T U lam c hc hlam htriv) := by
  refine ⟨LinearMap.inl_injective, LinearMap.snd_surjective,
    fun y hy => ⟨(0, y), ⟨T.L.T.zero_mem, hy⟩, rfl⟩, fun z => ⟨fun h => ⟨z.1, ?_⟩, ?_⟩,
    fun y hy => hy.1⟩
  · exact Prod.ext rfl (Eq.symm h)
  · rintro ⟨y, rfl⟩
    rfl

/- English proof (translation)
Take `⟨e, he, hT⟩` from `W.one_line`. Take `⟨lam, hlam⟩` from `LinearMap.exists_leftInverse_of_injective (LinearMap.toSpanSingleton LL W.one.V e) (LinearMap.ker_toSpanSingleton LL he)`. Establish `h1 : lam e = 1`. Use `congrArg (fun f : LL →ₗ[LL] LL => f 1) hlam` as an intermediate fact. Simplify using `using this`.

Use `⟨e, lam, hT, h1, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite `hy` using `[hT, Submodule.mem_span_singleton]`. Take `⟨o, rfl⟩` from `hy`. Use `⟨o, ?_⟩` and prove the remaining obligations. Rewrite using `[← algebraMap_smul LL o e, map_smul, h1, smul_eq_mul, mul_one]`.
-/
theorem lext_lam (W : LocWach PD LL O v n) : ∃ (e : W.one.V) (lam : W.one.V →ₗ[LL] LL),
    W.one.L.T = Submodule.span O {e} ∧ lam e = 1 ∧
      ∀ y ∈ W.one.L.T, ∃ o : O, lam y = algebraMap O LL o := by
  obtain ⟨e, he, hT⟩ := W.one_line
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective
    (LinearMap.toSpanSingleton LL W.one.V e) (LinearMap.ker_toSpanSingleton LL he)
  have h1 : lam e = 1 := by
    have := congrArg (fun f : LL →ₗ[LL] LL => f 1) hlam
    simpa using this
  refine ⟨e, lam, hT, h1, fun y hy => ?_⟩
  rw [hT, Submodule.mem_span_singleton] at hy
  obtain ⟨o, rfl⟩ := hy
  refine ⟨o, ?_⟩
  rw [← algebraMap_smul LL o e, map_smul, h1, smul_eq_mul, mul_one]

/- English proof (translation)
Use `⟨lext_ses T W.one lam c hc hlam W.one_triv, (0, e), ⟨T.L.T.zero_mem, by rw [hT]; exact Submodule.mem_span_singleton_self e⟩, hT.symm, fun g => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(c g, (0 : W.one.V)) = (T.ρ g 0 + lam e • c g, e) - (0, e)`. Simplify using `[h1]`.
-/
theorem lext_isExtOf [IsTopologicalRing LL] (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)
    (c : G → T.V) (hc : c ∈ latticeCocycles T.L) (e : W.one.V) (lam : W.one.V →ₗ[LL] LL)
    (hT : W.one.L.T = Submodule.span O {e}) (h1 : lam e = 1)
    (hlam : ∀ y ∈ W.one.L.T, ∃ o : O, lam y = algebraMap O LL o) :
    IsExtOf W (lext_ι T W.one lam c hc hlam) (lext_π T W.one lam c hc hlam W.one_triv) c := by
  refine ⟨lext_ses T W.one lam c hc hlam W.one_triv, (0, e),
    ⟨T.L.T.zero_mem, by rw [hT]; exact Submodule.mem_span_singleton_self e⟩, hT.symm, fun g => ?_⟩
  change (c g, (0 : W.one.V)) = (T.ρ g 0 + lam e • c g, e) - (0, e)
  simp [h1]

section Crys

variable {V U V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

/- English proof (translation)
Unfold `Dcris`. Rewrite using `[Submodule.mem_iInf]`. Use `forall_congr' fun g => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`.
-/
theorem lext_mem_Dcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ Dcris PD ρ ↔ ∀ g, actVB PD ρ g x = x := by
  unfold Dcris
  rw [Submodule.mem_iInf]
  refine forall_congr' fun g => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

/- English proof (translation)
Simplify using `[actVB]`.
-/
theorem lext_act_tmul (ρ : Representation LL G V) (g : G) (x : V) (b : B) :
    actVB PD ρ g (x ⊗ₜ[Qp] b) = ρ g x ⊗ₜ[Qp] PD.actB g b := by
  simp [actVB]

def lext_mapB (f : V →ₗ[LL] V') : V ⊗[Qp] B →ₗ[LL] V' ⊗[Qp] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)

/- English proof (translation)
Simplify using `[lext_mapB]`.
-/
theorem lext_mapB_tmul (f : V →ₗ[LL] V') (x : V) (b : B) :
    lext_mapB (Qp := Qp) (B := B) f (x ⊗ₜ[Qp] b) = f x ⊗ₜ[Qp] b := by
  simp [lext_mapB]

/- English proof (translation)
Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp only [lext_act_tmul, lext_mapB_tmul, hf]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem lext_funct (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (g : G) (m : V ⊗[Qp] B) :
    lext_mapB f (actVB PD ρ g m) = actVB PD ρ' g (lext_mapB f m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp only [lext_act_tmul, lext_mapB_tmul, hf]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Simplify using `[mulVB]`.
-/
theorem lext_mul_tmul (κ : K₀) (x : V) (b : B) :
    mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) κ (x ⊗ₜ[Qp] b) =
      x ⊗ₜ[Qp] (algebraMap K₀ B κ * b) := by
  simp [mulVB]

/- English proof (translation)
Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp only [lext_act_tmul, lext_mul_tmul, map_mul, AlgEquiv.commutes]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem lext_act_mul (ρ : Representation LL G V) (g : G) (κ : K₀) (m : V ⊗[Qp] B) :
    actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) κ m) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) κ (actVB PD ρ g m) := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp only [lext_act_tmul, lext_mul_tmul, map_mul, AlgEquiv.commutes]
  | add a b ha hb => simp only [map_add, ha, hb]

def lext_coord {ι : Type} (b : Module.Basis ι Qp U) (i : ι) : U ⊗[Qp] B →ₗ[Qp] B :=
  (TensorProduct.lid Qp B).toLinearMap ∘ₗ LinearMap.rTensor B (b.coord i)

/- English proof (translation)
Simplify using `[lext_coord]`.
-/
theorem lext_coord_tmul {ι : Type} (b : Module.Basis ι Qp U) (i : ι) (y : U) (c : B) :
    lext_coord (B := B) b i (y ⊗ₜ[Qp] c) = b.coord i y • c := by
  simp [lext_coord]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l c`. Simplify using `only [lext_coord_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]`. Use `congr 1`.

Simplify using `[Module.Basis.coord_apply]`. Consider the case `add x y hx hy => conv_lhs => rw [hx, hy]`. Simplify using `[Finset.sum_add_distrib, TensorProduct.tmul_add]`.
-/
theorem lext_decomp {ι : Type} [Fintype ι] (b : Module.Basis ι Qp U) (x : U ⊗[Qp] B) :
    x = ∑ i, b i ⊗ₜ[Qp] lext_coord (B := B) b i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    simp only [lext_coord_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.sum_tmul]
    congr 1
    simp [Module.Basis.coord_apply]
  | add x y hx hy =>
    conv_lhs => rw [hx, hy]
    simp [Finset.sum_add_distrib, TensorProduct.tmul_add]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul l c`. Rewrite using `[lext_act_tmul, hU, lext_coord_tmul, lext_coord_tmul]`. Conclude with `(((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp).map_smul _ _ |>.symm`.

Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem lext_coord_act {ι : Type} (b : Module.Basis ι Qp U) (i : ι) (ρU : Representation LL G U)
    (hU : ∀ g y, ρU g y = y) (g : G) (x : U ⊗[Qp] B) :
    lext_coord (B := B) b i (actVB PD ρU g x) = PD.actB g (lext_coord (B := B) b i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    rw [lext_act_tmul, hU, lext_coord_tmul, lext_coord_tmul]
    exact (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp).map_smul _ _ |>.symm
  | add x y hx hy => simp only [map_add, hx, hy]

/- English proof (translation)
Use `PD.finK₀` as an intermediate fact. Distinguish the cases in `h0 : Module.finrank LL V = 0`. Establish `hs : Subsingleton V` using `Module.finrank_zero_iff.1 h0`. Establish `hs' : Subsingleton (V ⊗[Qp] B)`. Use `⟨fun a b => ?_⟩` and prove the remaining obligations.

Establish `hz : ∀ a : V ⊗[Qp] B, a = 0`. Introduce `a`. Proceed by induction on `a using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul x b => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]`.

Consider the case `add a b ha hb => rw [ha, hb, add_zero]`. Rewrite using `[hz a, hz b]`. Use `infer_instance`. Apply `Module.finite_of_finrank_pos` to reduce the goal to its premises. Unfold `IsCrys at h`.

Rewrite using `[h]`. Conclude with `Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero h0)`.
-/
theorem lext_fin [FiniteDimensional LL V] (ρ : Representation LL G V) (h : IsCrys PD ρ) :
    Module.Finite LL ↥(Dcris PD ρ) := by
  have := PD.finK₀
  by_cases h0 : Module.finrank LL V = 0
  · have hs : Subsingleton V := Module.finrank_zero_iff.1 h0
    have hs' : Subsingleton (V ⊗[Qp] B) := by
      refine ⟨fun a b => ?_⟩
      have hz : ∀ a : V ⊗[Qp] B, a = 0 := by
        intro a
        induction a using TensorProduct.induction_on with
        | zero => rfl
        | tmul x b => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
        | add a b ha hb => rw [ha, hb, add_zero]
      rw [hz a, hz b]
    infer_instance
  · apply Module.finite_of_finrank_pos
    unfold IsCrys at h
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero h0)

/- English proof (translation)
Establish `fV` using `lext_fin ρ hV`. Establish `fU` using `lext_fin ρU hUc`. Use `set iB : V ⊗[Qp] B →ₗ[LL] (V × U) ⊗[Qp] B := lext_mapB (LinearMap.inl LL V U) with hiB`. Use `set pB : (V × U) ⊗[Qp] B →ₗ[LL] U ⊗[Qp] B := lext_mapB (LinearMap.snd LL V U) with hpB`. Use `set rB : (V × U) ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B := lext_mapB (LinearMap.fst LL V U) with hrB`.

Use `set sB : U ⊗[Qp] B →ₗ[LL] (V × U) ⊗[Qp] B := lext_mapB (LinearMap.inr LL V U) with hsB`. Establish `hri : ∀ m, rB (iB m) = m`. Introduce `m`. Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x b => simp [hiB, hrB, lext_mapB_tmul]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Establish `hpi : ∀ m, pB (iB m) = 0`. Introduce `m`. Proceed by induction on `m using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul x b => simp [hiB, hpB, lext_mapB_tmul]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb, add_zero]`. Establish `hsum : ∀ z, iB (rB z) + sB (pB z) = z`. Introduce `z`.

Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b`. Simplify using `only [hiB, hpB, hrB, hsB, lext_mapB_tmul, ← TensorProduct.add_tmul]`. Use `congr 1`.

Simplify using the standard rewrite rules. Consider the case `add a b ha hb`. Simplify using `only [map_add]`. Use `conv_rhs => rw [← ha, ← hb]`. Normalize the expressions using the abelian group laws.

Establish `hiE : ∀ g m, iB (actVB PD ρ g m) = actVB PD ρp g (iB m)` using `lext_funct ρ ρp (LinearMap.inl LL V U) (by intro g x; rw [hp]; simp)`. Establish `hpE : ∀ g z, pB (actVB PD ρp g z) = actVB PD ρU g (pB z)` using `lext_funct ρp ρU (LinearMap.snd LL V U) (by intro g z; rw [hp, hU]; rfl)`. Set `a : ↥(Dcris PD ρ) →ₗ[LL] ↥(Dcris PD ρp)` to `(iB.comp (Dcris PD ρ).subtype).codRestrict (Dcris PD ρp) (fun m => (lext_mem_Dcris ρp _).2 fun g => by`. Express the relevant statement in the definitionally equal form `actVB PD ρp g (iB m) = iB m`. Rewrite using `[← hiE, (lext_mem_Dcris ρ _).1 m.2 g])`.

Set `P : ↥(Dcris PD ρp) →ₗ[LL] ↥(Dcris PD ρU)` to `(pB.comp (Dcris PD ρp).subtype).codRestrict (Dcris PD ρU) (fun z => (lext_mem_Dcris ρU _).2 fun g => by`. Express the relevant statement in the definitionally equal form `actVB PD ρU g (pB z) = pB z`. Rewrite using `[← hpE, (lext_mem_Dcris ρp _).1 z.2 g])`. Establish `ha : Function.Injective a`. Introduce `m m' h`.

Establish `h1 : iB m = iB m'` using `congrArg Subtype.val h`. Establish `h2` using `congrArg rB h1`. Rewrite `h2` using `[hri, hri]`. Conclude with `Subtype.ext h2`. Establish `hex : LinearMap.range a = LinearMap.ker P`.

Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, rfl⟩`. Conclude with `Subtype.ext (hpi m)`. Introduce `hz`.

Establish `hz' : pB z.1 = 0` using `congrArg Subtype.val hz`. Establish `e : iB (rB z.1) = z.1`. Use `hsum z.1` as an intermediate fact. Rewrite `this` using `[hz', map_zero, add_zero]`. Conclude with `this`.

Use `⟨⟨rB z.1, (lext_mem_Dcris ρ _).2 fun g => ?_⟩, Subtype.ext e⟩` and prove the remaining obligations. Establish `h1 : iB (actVB PD ρ g (rB z.1)) = iB (rB z.1)`. Rewrite using `[hiE, e, (lext_mem_Dcris ρp _).1 z.2 g]`. Establish `h2` using `congrArg rB h1`. Rewrite `h2` using `[hri, hri]`. Then use the resulting hypothesis.

Establish `hP : Function.Surjective P`. Introduce and unpack `⟨w, hw⟩`. Establish `: Module.Finite Qp U` using `Module.Finite.trans LL U`. Set `b` to `Module.finBasis Qp U`. Establish `hinv` using `(lext_mem_Dcris ρU w).1 hw`.

Establish `hc : ∀ i, ∃ κ : K₀, algebraMap K₀ B κ = lext_coord (B` using `B) b i w := fun i => PD.invB _ (fun g => by rw [← lext_coord_act b i ρU hU, hinv])`. Use `choose κ hκ using hc`. Establish `hz : ∀ i, ((0 : V), b i) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) - iB (mulVB (K₀` using `K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • x₀)) ∈ Dcris PD ρp := by`. Introduce `i`. Rewrite using `[lext_mem_Dcris]`.

Introduce `g`. Establish `e1 : actVB PD ρp g (((0 : V), b i) ⊗ₜ[Qp] (algebraMap K₀ B (κ i))) = ((0 : V), b i) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) + iB ((lam (b i) • c g) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)))`. Rewrite using `[lext_act_tmul, hp, AlgEquiv.commutes, hiB, lext_mapB_tmul, ← TensorProduct.add_tmul]`. Use `congr 1`. Simplify using the standard rewrite rules.

Establish `e2 : (lam (b i) • c g) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) = actVB PD ρ g (mulVB (K₀` using `K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • x₀)) - mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • x₀) := by`. Establish `h1 : mulVB (K₀` using `K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • (c g ⊗ₜ[Qp] (1 : B))) = (lam (b i) • c g) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) := by`. Rewrite using `[TensorProduct.smul_tmul', lext_mul_tmul, mul_one]`. Rewrite using `[← h1, hx₀, smul_sub, map_sub, lext_act_mul, map_smul (actVB PD ρ g)]`. Rewrite using `[map_sub, e1, e2, map_sub, ← hiE]`.

Normalize the expressions using the abelian group laws. Use `⟨⟨∑ i, (((0 : V), b i) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) - iB (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • x₀))), Submodule.sum_mem _ (fun i _ => hz i)⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pB (∑ i, (((0 : V), b i) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) - iB (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • x₀)))) = w`. Rewrite using `[map_sum]`. Use `conv_rhs => rw [lext_decomp b w]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, hpi, sub_zero, hpB, lext_mapB_tmul, hκ]`. Both sides reduce to the same expression. Establish `f1 : Module.Finite LL ↥(LinearMap.ker P)` using `by rw [← hex]; infer_instance`. Establish `f2 : Module.Finite LL (↥(Dcris PD ρp) ⧸ LinearMap.ker P)` using `Module.Finite.equiv (P.quotKerEquivOfSurjective hP).symm`.

Establish `f3 : Module.Finite LL ↥(Dcris PD ρp)` using `Module.Finite.of_submodule_quotient (LinearMap.ker P)`. Establish `h` using `LinearMap.finrank_range_add_finrank_ker P`. Rewrite `h` using `[LinearMap.range_eq_top.2 hP, finrank_top, ← hex, LinearMap.finrank_range_of_inj ha]`. Unfold `IsCrys at *`. Rewrite using `[← h, hV, hUc, Module.finrank_prod]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lext_crys [FiniteDimensional Qp LL] [FiniteDimensional LL V] [FiniteDimensional LL U]
    (ρ : Representation LL G V) (ρU : Representation LL G U) (ρp : Representation LL G (V × U))
    (lam : U →ₗ[LL] LL) (c : G → V) (hU : ∀ g y, ρU g y = y)
    (hp : ∀ g z, ρp g z = (ρ g z.1 + lam z.2 • c g, z.2)) (x₀ : V ⊗[Qp] B)
    (hx₀ : ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x₀ - x₀) (hV : IsCrys PD ρ)
    (hUc : IsCrys PD ρU) : IsCrys PD ρp := by
  have fV := lext_fin ρ hV
  have fU := lext_fin ρU hUc
  set iB : V ⊗[Qp] B →ₗ[LL] (V × U) ⊗[Qp] B := lext_mapB (LinearMap.inl LL V U) with hiB
  set pB : (V × U) ⊗[Qp] B →ₗ[LL] U ⊗[Qp] B := lext_mapB (LinearMap.snd LL V U) with hpB
  set rB : (V × U) ⊗[Qp] B →ₗ[LL] V ⊗[Qp] B := lext_mapB (LinearMap.fst LL V U) with hrB
  set sB : U ⊗[Qp] B →ₗ[LL] (V × U) ⊗[Qp] B := lext_mapB (LinearMap.inr LL V U) with hsB
  have hri : ∀ m, rB (iB m) = m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [hiB, hrB, lext_mapB_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hpi : ∀ m, pB (iB m) = 0 := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp
    | tmul x b => simp [hiB, hpB, lext_mapB_tmul]
    | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  have hsum : ∀ z, iB (rB z) + sB (pB z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x b =>
      simp only [hiB, hpB, hrB, hsB, lext_mapB_tmul, ← TensorProduct.add_tmul]
      congr 1
      simp
    | add a b ha hb =>
      simp only [map_add]
      conv_rhs => rw [← ha, ← hb]
      abel
  have hiE : ∀ g m, iB (actVB PD ρ g m) = actVB PD ρp g (iB m) :=
    lext_funct ρ ρp (LinearMap.inl LL V U) (by intro g x; rw [hp]; simp)
  have hpE : ∀ g z, pB (actVB PD ρp g z) = actVB PD ρU g (pB z) :=
    lext_funct ρp ρU (LinearMap.snd LL V U) (by intro g z; rw [hp, hU]; rfl)
  let a : ↥(Dcris PD ρ) →ₗ[LL] ↥(Dcris PD ρp) :=
    (iB.comp (Dcris PD ρ).subtype).codRestrict (Dcris PD ρp) (fun m =>
      (lext_mem_Dcris ρp _).2 fun g => by
        change actVB PD ρp g (iB m) = iB m
        rw [← hiE, (lext_mem_Dcris ρ _).1 m.2 g])
  let P : ↥(Dcris PD ρp) →ₗ[LL] ↥(Dcris PD ρU) :=
    (pB.comp (Dcris PD ρp).subtype).codRestrict (Dcris PD ρU) (fun z =>
      (lext_mem_Dcris ρU _).2 fun g => by
        change actVB PD ρU g (pB z) = pB z
        rw [← hpE, (lext_mem_Dcris ρp _).1 z.2 g])
  have ha : Function.Injective a := by
    intro m m' h
    have h1 : iB m = iB m' := congrArg Subtype.val h
    have h2 := congrArg rB h1
    rw [hri, hri] at h2
    exact Subtype.ext h2
  have hex : LinearMap.range a = LinearMap.ker P := by
    ext z
    constructor
    · rintro ⟨m, rfl⟩
      exact Subtype.ext (hpi m)
    · intro hz
      have hz' : pB z.1 = 0 := congrArg Subtype.val hz
      have e : iB (rB z.1) = z.1 := by
        have := hsum z.1
        rw [hz', map_zero, add_zero] at this
        exact this
      refine ⟨⟨rB z.1, (lext_mem_Dcris ρ _).2 fun g => ?_⟩, Subtype.ext e⟩
      have h1 : iB (actVB PD ρ g (rB z.1)) = iB (rB z.1) := by
        rw [hiE, e, (lext_mem_Dcris ρp _).1 z.2 g]
      have h2 := congrArg rB h1
      rwa [hri, hri] at h2
  have hP : Function.Surjective P := by
    rintro ⟨w, hw⟩
    have : Module.Finite Qp U := Module.Finite.trans LL U
    let b := Module.finBasis Qp U
    have hinv := (lext_mem_Dcris ρU w).1 hw
    have hc : ∀ i, ∃ κ : K₀, algebraMap K₀ B κ = lext_coord (B := B) b i w := fun i =>
      PD.invB _ (fun g => by rw [← lext_coord_act b i ρU hU, hinv])
    choose κ hκ using hc
    have hz : ∀ i, ((0 : V), b i) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) -
        iB (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • x₀)) ∈ Dcris PD ρp := by
      intro i
      rw [lext_mem_Dcris]
      intro g
      have e1 : actVB PD ρp g (((0 : V), b i) ⊗ₜ[Qp] (algebraMap K₀ B (κ i))) =
          ((0 : V), b i) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) +
            iB ((lam (b i) • c g) ⊗ₜ[Qp] (algebraMap K₀ B (κ i))) := by
        rw [lext_act_tmul, hp, AlgEquiv.commutes, hiB, lext_mapB_tmul, ← TensorProduct.add_tmul]
        congr 1
        simp
      have e2 : (lam (b i) • c g) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) =
          actVB PD ρ g (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • x₀)) -
            mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • x₀) := by
        have h1 : mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (κ i)
            (lam (b i) • (c g ⊗ₜ[Qp] (1 : B))) =
            (lam (b i) • c g) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) := by
          rw [TensorProduct.smul_tmul', lext_mul_tmul, mul_one]
        rw [← h1, hx₀, smul_sub, map_sub, lext_act_mul, map_smul (actVB PD ρ g)]
      rw [map_sub, e1, e2, map_sub, ← hiE]
      abel
    refine ⟨⟨∑ i, (((0 : V), b i) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) -
      iB (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • x₀))),
      Submodule.sum_mem _ (fun i _ => hz i)⟩, Subtype.ext ?_⟩
    change pB (∑ i, (((0 : V), b i) ⊗ₜ[Qp] (algebraMap K₀ B (κ i)) -
      iB (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (κ i) (lam (b i) • x₀)))) = w
    rw [map_sum]
    conv_rhs => rw [lext_decomp b w]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_sub, hpi, sub_zero, hpB, lext_mapB_tmul, hκ]
    rfl
  have f1 : Module.Finite LL ↥(LinearMap.ker P) := by rw [← hex]; infer_instance
  have f2 : Module.Finite LL (↥(Dcris PD ρp) ⧸ LinearMap.ker P) :=
    Module.Finite.equiv (P.quotKerEquivOfSurjective hP).symm
  have f3 : Module.Finite LL ↥(Dcris PD ρp) := Module.Finite.of_submodule_quotient (LinearMap.ker P)
  have h := LinearMap.finrank_range_add_finrank_ker P
  rw [LinearMap.range_eq_top.2 hP, finrank_top, ← hex, LinearMap.finrank_range_of_inj ha] at h
  unfold IsCrys at *
  rw [← h, hV, hUc, Module.finrank_prod]
  ring

end Crys

/- English proof (translation)
Introduce `T c hT hc`. Take `⟨e, lam, hTe, hle, hlam⟩` from `lext_lam W`. Take `⟨x₀, hx₀⟩` from `hc.2.2`. Use `⟨lext_Tp T W.one lam c hc.1 hlam, lext_ι T W.one lam c hc.1 hlam, lext_π T W.one lam c hc.1 hlam W.one_triv, ?_, lext_isExtOf W T c hc.1 e lam hTe hle hlam⟩` and prove the remaining obligations. Conclude with `lext_crys T.ρ W.one.ρ _ lam c W.one_triv (fun g z => rfl) x₀ hx₀ hT h1`.
-/
theorem lext_HExt [IsTopologicalRing LL] [FiniteDimensional Qp LL] (W : LocWach PD LL O v n)
    (h1 : IsCrys PD W.one.ρ) : liftb_HExt W := by
  intro T c hT hc
  obtain ⟨e, lam, hTe, hle, hlam⟩ := lext_lam W
  obtain ⟨x₀, hx₀⟩ := hc.2.2
  refine ⟨lext_Tp T W.one lam c hc.1 hlam, lext_ι T W.one lam c hc.1 hlam,
    lext_π T W.one lam c hc.1 hlam W.one_triv, ?_, lext_isExtOf W T c hc.1 e lam hTe hle hlam⟩
  exact lext_crys T.ρ W.one.ρ _ lam c W.one_triv (fun g z => rfl) x₀ hx₀ hT h1

end LiftExt

/- English proof (translation)
Establish `: FiniteDimensional ℚ_[l] ↥LL.1` using `LL.2`. Conclude with `lext_HExt _ h1`.
-/
theorem lext_HExt_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) (h1 : IsCrys ((D.loc l).PD K) ((HW l).W K s LL h).one.ρ) :
    liftb_HExt ((HW l).W K s LL h) := by
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  exact lext_HExt _ h1

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section LiftKer

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section KerCrys

variable {V₀ V₁ V₂ : Type} [AddCommGroup V₀] [Module LL V₀] [Module Qp V₀] [IsScalarTower Qp LL V₀]
    [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]

/- English proof (translation)
Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp only [lext_mapB_tmul, LinearMap.comp_apply]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem lker_mapB_comp (f : V₀ →ₗ[LL] V₁) (g : V₁ →ₗ[LL] V₂) (m : V₀ ⊗[Qp] B) :
    lext_mapB (Qp := Qp) (B := B) g (lext_mapB f m) = lext_mapB (g ∘ₗ f) m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp only [lext_mapB_tmul, LinearMap.comp_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp only [lext_mapB_tmul, LinearMap.id_apply]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`.
-/
theorem lker_mapB_id (m : V₀ ⊗[Qp] B) :
    lext_mapB (Qp := Qp) (B := B) (LinearMap.id : V₀ →ₗ[LL] V₀) m = m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp only [lext_mapB_tmul, LinearMap.id_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

/- English proof (translation)
Proceed by induction on `m using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x b => simp only [lext_mapB_tmul, LinearMap.add_apply, TensorProduct.add_tmul]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Normalize the expressions using the abelian group laws.
-/
theorem lker_mapB_add (f g : V₀ →ₗ[LL] V₁) (m : V₀ ⊗[Qp] B) :
    lext_mapB (Qp := Qp) (B := B) (f + g) m = lext_mapB f m + lext_mapB g m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp only [lext_mapB_tmul, LinearMap.add_apply, TensorProduct.add_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]; abel

/- English proof (translation)
Establish `fin1` using `lext_fin ρ₁ h1`. Establish `fin2` using `lext_fin ρ₂ h2`. Establish `hiB : Function.Injective (lext_mapB (Qp` using `Qp) (B := B) i) := by`. Introduce `a b hab`. Use `congrArg (lext_mapB (Qp := Qp) (B := B) r) hab` as an intermediate fact.

Rewrite `this` using `[lker_mapB_comp, lker_mapB_comp, hri, lker_mapB_id, lker_mapB_id]`. Then use the resulting hypothesis. Set `Φ₀ : ↥(Dcris PD ρ₀) →ₗ[LL] ↥(Dcris PD ρ₁)` to `((lext_mapB (Qp := Qp) (B := B) i).comp (Dcris PD ρ₀).subtype).codRestrict (Dcris PD ρ₁) (fun x => (lext_mem_Dcris ρ₁ _).2 (fun g => by`. Express the relevant statement in the definitionally equal form `actVB PD ρ₁ g (lext_mapB i (x : V₀ ⊗[Qp] B)) = lext_mapB i (x : V₀ ⊗[Qp] B)`. Rewrite using `[← lext_funct ρ₀ ρ₁ i hi, (lext_mem_Dcris ρ₀ _).1 x.2 g]))`. Establish `hΦ₀ : Function.Injective Φ₀` using `fun a b hab => Subtype.ext (hiB (congrArg Subtype.val hab))`.

Establish `fin0 : Module.Finite LL ↥(Dcris PD ρ₀)` using `Module.Finite.of_injective Φ₀ hΦ₀`. Set `Φ : ↥(Dcris PD ρ₁) →ₗ[LL] ↥(Dcris PD ρ₂)` to `((lext_mapB (Qp := Qp) (B := B) f).comp (Dcris PD ρ₁).subtype).codRestrict (Dcris PD ρ₂) (fun x => (lext_mem_Dcris ρ₂ _).2 (fun g => by`. Express the relevant statement in the definitionally equal form `actVB PD ρ₂ g (lext_mapB f (x : V₁ ⊗[Qp] B)) = lext_mapB f (x : V₁ ⊗[Qp] B)`. Rewrite using `[← lext_funct ρ₁ ρ₂ f hf, (lext_mem_Dcris ρ₁ _).1 x.2 g]))`. Establish `hback : ∀ x : V₁ ⊗[Qp] B, lext_mapB (Qp` using `Qp) (B := B) f x = 0 → lext_mapB i (lext_mapB r x) = x := by`.

Introduce `x hx`. Establish `h` using `lker_mapB_id (Qp := Qp) (B := B) (LL := LL) x`. Rewrite `h` using `[← hsplit, lker_mapB_add, ← lker_mapB_comp, ← lker_mapB_comp, hx, map_zero, add_zero]`. Conclude with `h`. Set `Ψ : ↥(LinearMap.ker Φ) →ₗ[LL] ↥(Dcris PD ρ₀)` to `((lext_mapB (Qp := Qp) (B := B) r).comp ((Dcris PD ρ₁).subtype.comp (LinearMap.ker Φ).subtype)).codRestrict (Dcris PD ρ₀) (fun x => (lext_mem_Dcris ρ₀ _).2 (fun g => by`.

Establish `hx0 : lext_mapB (Qp` using `Qp) (B := B) f ((x : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 x.2)`. Apply `hiB` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `lext_mapB i (actVB PD ρ₀ g (lext_mapB r ((x : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B))) = lext_mapB i (lext_mapB r ((x : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B))`. Rewrite using `[lext_funct ρ₀ ρ₁ i hi, hback _ hx0, (lext_mem_Dcris ρ₁ _).1 (x : ↥(Dcris PD ρ₁)).2 g]))`. Establish `hΨ : Function.Injective Ψ`.

Introduce `a b hab`. Establish `ha0 : lext_mapB (Qp` using `Qp) (B := B) f ((a : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 a.2)`. Establish `hb0 : lext_mapB (Qp` using `Qp) (B := B) f ((b : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B) = 0 := congrArg Subtype.val (LinearMap.mem_ker.1 b.2)`. Establish `h : lext_mapB (Qp` using `Qp) (B := B) r ((a : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B) = lext_mapB r ((b : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B) := congrArg Subtype.val hab`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hback _ ha0, ← hback _ hb0, h]`. Establish `e1` using `LinearMap.finrank_range_add_finrank_ker Φ`. Establish `e2 : Module.finrank LL ↥(LinearMap.range Φ) ≤ Module.finrank LL ↥(Dcris PD ρ₂)` using `Submodule.finrank_le _`. Establish `e3 : Module.finrank LL ↥(LinearMap.ker Φ) ≤ Module.finrank LL ↥(Dcris PD ρ₀)` using `LinearMap.finrank_le_finrank_of_injective hΨ`.

Establish `hfsurj : Function.Surjective f` using `fun y => ⟨s y, LinearMap.congr_fun hfs y⟩`. Establish `hiinj : Function.Injective i` using `fun a b hab => by`. Use `congrArg r hab` as an intermediate fact. Establish `h' : ∀ z, r (i z) = z` using `fun z => LinearMap.congr_fun hri z`. Rewrite `this` using `[h', h']`. Then use the resulting hypothesis.

Establish `hker : LinearMap.ker f = LinearMap.range i`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `LinearMap.congr_fun hsplit x` as an intermediate fact.

Simplify using `only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, LinearMap.mem_ker.1 hx, map_zero, add_zero] at this`. Conclude with `⟨r x, this⟩`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `LinearMap.congr_fun hfi y`. Establish `d1` using `LinearMap.finrank_range_add_finrank_ker f`.

Rewrite `d1` using `[LinearMap.range_eq_top.2 hfsurj, finrank_top, hker, LinearMap.finrank_range_of_inj hiinj]`. Unfold `IsCrys at h1 h2 ⊢`. Apply `le_antisymm hF` to reduce the goal to its premises. Establish `: Module.finrank Qp K₀ * Module.finrank LL V₁ = Module.finrank Qp K₀ * Module.finrank LL V₂ + Module.finrank Qp K₀ * Module.finrank LL V₀`. Rewrite using `[← d1, mul_add]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem lker_crys [FiniteDimensional LL V₀] [FiniteDimensional LL V₁] [FiniteDimensional LL V₂]
    (ρ₀ : Representation LL G V₀) (ρ₁ : Representation LL G V₁) (ρ₂ : Representation LL G V₂)
    (i : V₀ →ₗ[LL] V₁) (f : V₁ →ₗ[LL] V₂) (r : V₁ →ₗ[LL] V₀) (s : V₂ →ₗ[LL] V₁)
    (hri : r ∘ₗ i = LinearMap.id) (hsplit : i ∘ₗ r + s ∘ₗ f = LinearMap.id)
    (hfs : f ∘ₗ s = LinearMap.id) (hfi : f ∘ₗ i = 0)
    (hi : ∀ g x, i (ρ₀ g x) = ρ₁ g (i x)) (hf : ∀ g x, f (ρ₁ g x) = ρ₂ g (f x))
    (h1 : IsCrys PD ρ₁) (h2 : IsCrys PD ρ₂)
    (hF : Module.finrank LL ↥(Dcris PD ρ₀) ≤ Module.finrank Qp K₀ * Module.finrank LL V₀) :
    IsCrys PD ρ₀ := by
  have fin1 := lext_fin ρ₁ h1
  have fin2 := lext_fin ρ₂ h2
  have hiB : Function.Injective (lext_mapB (Qp := Qp) (B := B) i) := by
    intro a b hab
    have := congrArg (lext_mapB (Qp := Qp) (B := B) r) hab
    rwa [lker_mapB_comp, lker_mapB_comp, hri, lker_mapB_id, lker_mapB_id] at this

  let Φ₀ : ↥(Dcris PD ρ₀) →ₗ[LL] ↥(Dcris PD ρ₁) :=
    ((lext_mapB (Qp := Qp) (B := B) i).comp (Dcris PD ρ₀).subtype).codRestrict (Dcris PD ρ₁)
      (fun x => (lext_mem_Dcris ρ₁ _).2 (fun g => by
        change actVB PD ρ₁ g (lext_mapB i (x : V₀ ⊗[Qp] B)) = lext_mapB i (x : V₀ ⊗[Qp] B)
        rw [← lext_funct ρ₀ ρ₁ i hi, (lext_mem_Dcris ρ₀ _).1 x.2 g]))
  have hΦ₀ : Function.Injective Φ₀ := fun a b hab =>
    Subtype.ext (hiB (congrArg Subtype.val hab))
  have fin0 : Module.Finite LL ↥(Dcris PD ρ₀) := Module.Finite.of_injective Φ₀ hΦ₀

  let Φ : ↥(Dcris PD ρ₁) →ₗ[LL] ↥(Dcris PD ρ₂) :=
    ((lext_mapB (Qp := Qp) (B := B) f).comp (Dcris PD ρ₁).subtype).codRestrict (Dcris PD ρ₂)
      (fun x => (lext_mem_Dcris ρ₂ _).2 (fun g => by
        change actVB PD ρ₂ g (lext_mapB f (x : V₁ ⊗[Qp] B)) = lext_mapB f (x : V₁ ⊗[Qp] B)
        rw [← lext_funct ρ₁ ρ₂ f hf, (lext_mem_Dcris ρ₁ _).1 x.2 g]))

  have hback : ∀ x : V₁ ⊗[Qp] B, lext_mapB (Qp := Qp) (B := B) f x = 0 →
      lext_mapB i (lext_mapB r x) = x := by
    intro x hx
    have h := lker_mapB_id (Qp := Qp) (B := B) (LL := LL) x
    rw [← hsplit, lker_mapB_add, ← lker_mapB_comp, ← lker_mapB_comp, hx, map_zero, add_zero] at h
    exact h
  let Ψ : ↥(LinearMap.ker Φ) →ₗ[LL] ↥(Dcris PD ρ₀) :=
    ((lext_mapB (Qp := Qp) (B := B) r).comp
      ((Dcris PD ρ₁).subtype.comp (LinearMap.ker Φ).subtype)).codRestrict (Dcris PD ρ₀)
      (fun x => (lext_mem_Dcris ρ₀ _).2 (fun g => by
        have hx0 : lext_mapB (Qp := Qp) (B := B) f ((x : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B) = 0 :=
          congrArg Subtype.val (LinearMap.mem_ker.1 x.2)
        apply hiB
        change lext_mapB i (actVB PD ρ₀ g (lext_mapB r ((x : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B))) =
          lext_mapB i (lext_mapB r ((x : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B))
        rw [lext_funct ρ₀ ρ₁ i hi, hback _ hx0, (lext_mem_Dcris ρ₁ _).1 (x : ↥(Dcris PD ρ₁)).2 g]))
  have hΨ : Function.Injective Ψ := by
    intro a b hab
    have ha0 : lext_mapB (Qp := Qp) (B := B) f ((a : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.1 a.2)
    have hb0 : lext_mapB (Qp := Qp) (B := B) f ((b : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B) = 0 :=
      congrArg Subtype.val (LinearMap.mem_ker.1 b.2)
    have h : lext_mapB (Qp := Qp) (B := B) r ((a : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B) =
        lext_mapB r ((b : ↥(Dcris PD ρ₁)) : V₁ ⊗[Qp] B) := congrArg Subtype.val hab
    apply Subtype.ext
    apply Subtype.ext
    rw [← hback _ ha0, ← hback _ hb0, h]
  have e1 := LinearMap.finrank_range_add_finrank_ker Φ
  have e2 : Module.finrank LL ↥(LinearMap.range Φ) ≤ Module.finrank LL ↥(Dcris PD ρ₂) :=
    Submodule.finrank_le _
  have e3 : Module.finrank LL ↥(LinearMap.ker Φ) ≤ Module.finrank LL ↥(Dcris PD ρ₀) :=
    LinearMap.finrank_le_finrank_of_injective hΨ

  have hfsurj : Function.Surjective f := fun y => ⟨s y, LinearMap.congr_fun hfs y⟩
  have hiinj : Function.Injective i := fun a b hab => by
    have := congrArg r hab
    have h' : ∀ z, r (i z) = z := fun z => LinearMap.congr_fun hri z
    rwa [h', h'] at this
  have hker : LinearMap.ker f = LinearMap.range i := by
    ext x
    constructor
    · intro hx
      have := LinearMap.congr_fun hsplit x
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
        LinearMap.mem_ker.1 hx, map_zero, add_zero] at this
      exact ⟨r x, this⟩
    · rintro ⟨y, rfl⟩
      exact LinearMap.congr_fun hfi y
  have d1 := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.2 hfsurj, finrank_top, hker, LinearMap.finrank_range_of_inj hiinj] at d1
  unfold IsCrys at h1 h2 ⊢
  apply le_antisymm hF
  have : Module.finrank Qp K₀ * Module.finrank LL V₁ =
      Module.finrank Qp K₀ * Module.finrank LL V₂ + Module.finrank Qp K₀ * Module.finrank LL V₀ := by
    rw [← d1, mul_add]
  omega

end KerCrys

def lker_Den (LL O : Type) [Field LL] [CommRing O] [Algebra O LL] : Prop :=
  ∀ c : LL, ∃ a : O, algebraMap O LL a ≠ 0 ∧ ∃ o : O, algebraMap O LL a * c = algebraMap O LL o

/- English proof (translation)
Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← T₂.L.span, Submodule.span_le]`. Introduce `y hy`. Take `⟨x, _, h⟩` from `hOnto y hy`. Conclude with `⟨x, h⟩`.
-/
theorem lker_surj {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hOnto : F.Onto) :
    Function.Surjective F.f := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← T₂.L.span, Submodule.span_le]
  intro y hy
  obtain ⟨x, _, h⟩ := hOnto y hy
  exact ⟨x, h⟩

def lker_rep {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) :
    Representation LL G ↥(LinearMap.ker F.f) where
  toFun g := (T₁.ρ g).restrict (fun x hx => by
    rw [LinearMap.mem_ker, F.equiv, LinearMap.mem_ker.1 hx, map_zero])
  map_one' := by
    ext x
    simp
  map_mul' g h := by
    ext x
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lker_rep_coe {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (g : G)
    (x : ↥(LinearMap.ker F.f)) : ((lker_rep F g x : ↥(LinearMap.ker F.f)) : T₁.V) = T₁.ρ g x := rfl

/- English proof (translation)
Take `⟨s, hs⟩` from `F.f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 (lker_surj F hOnto))`. Establish `hs' : ∀ y, F.f (s y) = y` using `fun y => LinearMap.congr_fun hs y`. Use `⟨(LinearMap.id - s ∘ₗ F.f).codRestrict (LinearMap.ker F.f) (fun x => by` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker]`. Simplify using `[hs']), s, ?_, ?_, hs⟩`.

Use extensionality with `x`. Simplify using `[LinearMap.mem_ker.1 x.2]`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem lker_splitV {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hOnto : F.Onto) :
    ∃ (r : T₁.V →ₗ[LL] ↥(LinearMap.ker F.f)) (s : T₂.V →ₗ[LL] T₁.V),
      r ∘ₗ (LinearMap.ker F.f).subtype = LinearMap.id ∧
      (LinearMap.ker F.f).subtype ∘ₗ r + s ∘ₗ F.f = LinearMap.id ∧ F.f ∘ₗ s = LinearMap.id := by
  obtain ⟨s, hs⟩ := F.f.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 (lker_surj F hOnto))
  have hs' : ∀ y, F.f (s y) = y := fun y => LinearMap.congr_fun hs y
  refine ⟨(LinearMap.id - s ∘ₗ F.f).codRestrict (LinearMap.ker F.f) (fun x => by
    rw [LinearMap.mem_ker]
    simp [hs']), s, ?_, ?_, hs⟩
  · ext x
    simp [LinearMap.mem_ker.1 x.2]
  · ext x
    simp

def lker_lat {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) :
    Submodule O ↥(LinearMap.ker F.f) :=
  T₁.L.T.comap ((LinearMap.ker F.f).subtype.restrictScalars O)

/- English proof (translation)
Establish `: Module.Free O ↥T₂.L.T` using `T₂.L.free`. Set `φ : ↥T₁.L.T →ₗ[O] ↥T₂.L.T` to `(F.f.restrictScalars O).restrict F.T_le`. Establish `hφ : Function.Surjective φ` using `fun y => by`. Take `⟨x, hx, hxy⟩` from `hOnto y y.2`. Conclude with `⟨⟨x, hx⟩, Subtype.ext hxy⟩`.

Take `⟨σ, hσ⟩` from `Module.projective_lifting_property φ LinearMap.id hφ`. Establish `hσ' : ∀ y, F.f ((σ y : ↥T₁.L.T) : T₁.V) = (y : T₂.V)` using `fun y => congrArg Subtype.val (LinearMap.congr_fun hσ y)`. Establish `hk : ∀ x : ↥T₁.L.T, (x : T₁.V) - ((σ (φ x) : ↥T₁.L.T) : T₁.V) ∈ LinearMap.ker F.f`. Introduce `x`. Rewrite using `[LinearMap.mem_ker, map_sub, hσ']`.

Conclude with `sub_self _`. Set `i : ↥(lker_lat F) →ₗ[O] ↥T₁.L.T` to `{ toFun := fun x => ⟨((x : ↥(LinearMap.ker F.f)) : T₁.V), x.2⟩ map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Set `p : ↥T₁.L.T →ₗ[O] ↥(lker_lat F)` to `{ toFun := fun x => ⟨⟨(x : T₁.V) - ((σ (φ x) : ↥T₁.L.T) : T₁.V), hk x⟩, T₁.L.T.sub_mem x.2 (σ (φ x)).2⟩ map_add' := fun a b => by`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `((a + b : ↥T₁.L.T) : T₁.V) - ((σ (φ (a + b)) : ↥T₁.L.T) : T₁.V) = ((a : T₁.V) - ((σ (φ a) : ↥T₁.L.T) : T₁.V)) + ((b : T₁.V) - ((σ (φ b) : ↥T₁.L.T) : T₁.V))`. Rewrite using `[map_add, map_add]`. Use `push_cast`. Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := fun c a => by`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((c • a : ↥T₁.L.T) : T₁.V) - ((σ (φ (c • a)) : ↥T₁.L.T) : T₁.V) = c • ((a : T₁.V) - ((σ (φ a) : ↥T₁.L.T) : T₁.V))`. Rewrite using `[map_smul, map_smul, smul_sub]`. Use `rfl }`.

Use `⟨i, p, ?_⟩` and prove the remaining obligations. Use `ext1 x`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `((x : ↥(LinearMap.ker F.f)) : T₁.V) - ((σ (φ (i x)) : ↥T₁.L.T) : T₁.V) = _`.

Establish `h0 : φ (i x) = 0` using `Subtype.ext (LinearMap.mem_ker.1 (x : ↥(LinearMap.ker F.f)).2)`. Rewrite using `[h0, map_zero]`. Simplify using the standard rewrite rules.
-/
theorem lker_lat_split {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hOnto : F.Onto) :
    ∃ (i : ↥(lker_lat F) →ₗ[O] ↥T₁.L.T) (p : ↥T₁.L.T →ₗ[O] ↥(lker_lat F)),
      p ∘ₗ i = LinearMap.id := by
  have : Module.Free O ↥T₂.L.T := T₂.L.free
  let φ : ↥T₁.L.T →ₗ[O] ↥T₂.L.T := (F.f.restrictScalars O).restrict F.T_le
  have hφ : Function.Surjective φ := fun y => by
    obtain ⟨x, hx, hxy⟩ := hOnto y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property φ LinearMap.id hφ
  have hσ' : ∀ y, F.f ((σ y : ↥T₁.L.T) : T₁.V) = (y : T₂.V) := fun y =>
    congrArg Subtype.val (LinearMap.congr_fun hσ y)
  have hk : ∀ x : ↥T₁.L.T, (x : T₁.V) - ((σ (φ x) : ↥T₁.L.T) : T₁.V) ∈ LinearMap.ker F.f := by
    intro x
    rw [LinearMap.mem_ker, map_sub, hσ']
    exact sub_self _
  let i : ↥(lker_lat F) →ₗ[O] ↥T₁.L.T :=
    { toFun := fun x => ⟨((x : ↥(LinearMap.ker F.f)) : T₁.V), x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p : ↥T₁.L.T →ₗ[O] ↥(lker_lat F) :=
    { toFun := fun x => ⟨⟨(x : T₁.V) - ((σ (φ x) : ↥T₁.L.T) : T₁.V), hk x⟩,
        T₁.L.T.sub_mem x.2 (σ (φ x)).2⟩
      map_add' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        change ((a + b : ↥T₁.L.T) : T₁.V) - ((σ (φ (a + b)) : ↥T₁.L.T) : T₁.V) =
          ((a : T₁.V) - ((σ (φ a) : ↥T₁.L.T) : T₁.V)) + ((b : T₁.V) - ((σ (φ b) : ↥T₁.L.T) : T₁.V))
        rw [map_add, map_add]
        push_cast
        abel
      map_smul' := fun c a => by
        apply Subtype.ext
        apply Subtype.ext
        change ((c • a : ↥T₁.L.T) : T₁.V) - ((σ (φ (c • a)) : ↥T₁.L.T) : T₁.V) =
          c • ((a : T₁.V) - ((σ (φ a) : ↥T₁.L.T) : T₁.V))
        rw [map_smul, map_smul, smul_sub]
        rfl }
  refine ⟨i, p, ?_⟩
  ext1 x
  apply Subtype.ext
  apply Subtype.ext
  change ((x : ↥(LinearMap.ker F.f)) : T₁.V) - ((σ (φ (i x)) : ↥T₁.L.T) : T₁.V) = _
  have h0 : φ (i x) = 0 := Subtype.ext (LinearMap.mem_ker.1 (x : ↥(LinearMap.ker F.f)).2)
  rw [h0, map_zero]
  simp

/- English proof (translation)
Establish `hy : y ∈ Submodule.span LL (T.L.T : Set T.V)` using `by rw [T.L.span]; trivial`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem x hx => exact ⟨1, by simp, by simpa using hx⟩`. Consider the case `zero => exact ⟨1, by simp, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨b, hb, hby⟩` from `hy`. Use `⟨a * b, by rw [map_mul]; exact mul_ne_zero ha hb, ?_⟩` and prove the remaining obligations. Rewrite using `[smul_add]`. Use `T.L.T.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[mul_comm, mul_smul]`. Conclude with `T.L.T.smul_mem b hax`. Rewrite using `[mul_smul]`. Conclude with `T.L.T.smul_mem a hby`. Consider the case `smul c x _ hx`.

Take `⟨a, ha, hax⟩` from `hx`. Take `⟨a', ha', o, ho⟩` from `hden c`. Use `⟨a' * a, by rw [map_mul]; exact mul_ne_zero ha' ha, ?_⟩` and prove the remaining obligations. Establish `: (a' * a) • (c • x) = o • (a • x)`. Rewrite using `[← algebraMap_smul LL (a' * a), ← algebraMap_smul LL o, ← algebraMap_smul LL a, smul_smul, smul_smul, map_mul, ← ho]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `T.L.T.smul_mem o hax`.
-/
theorem lker_den (hden : lker_Den LL O) (T : LocLat G Qp LL O) (y : T.V) :
    ∃ a : O, algebraMap O LL a ≠ 0 ∧ a • y ∈ T.L.T := by
  have hy : y ∈ Submodule.span LL (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, by simp, by simpa using hx⟩
  | zero => exact ⟨1, by simp, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, by rw [map_mul]; exact mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine T.L.T.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact T.L.T.smul_mem b hax
    · rw [mul_smul]; exact T.L.T.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨a', ha', o, ho⟩ := hden c
    refine ⟨a' * a, by rw [map_mul]; exact mul_ne_zero ha' ha, ?_⟩
    have : (a' * a) • (c • x) = o • (a • x) := by
      rw [← algebraMap_smul LL (a' * a), ← algebraMap_smul LL o, ← algebraMap_smul LL a, smul_smul,
        smul_smul, map_mul, ← ho]
      congr 1
      ring
    rw [this]
    exact T.L.T.smul_mem o hax

def lker_T₀ [IsLocalRing O] {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (hOnto : F.Onto) (hden : lker_Den LL O) : LocLat G Qp LL O :=
  letI : TopologicalSpace ↥(LinearMap.ker F.f) := moduleTopology LL ↥(LinearMap.ker F.f)
  haveI : IsModuleTopology LL ↥(LinearMap.ker F.f) := ⟨rfl⟩
  haveI : ContinuousAdd ↥(LinearMap.ker F.f) := ModuleTopology.continuousAdd LL _
  haveI : ContinuousSMul LL ↥(LinearMap.ker F.f) := ModuleTopology.continuousSMul LL _
  { V := ↥(LinearMap.ker F.f)
    ρ := lker_rep F
    cont := fun x => by
      obtain ⟨r, s, hr, _, _⟩ := lker_splitV F hOnto
      have hc : Continuous r := IsModuleTopology.continuous_of_linearMap r
      have : (fun g => lker_rep F g x) = fun g => r (T₁.ρ g (x : T₁.V)) := by
        funext g
        exact (LinearMap.congr_fun hr (lker_rep F g x)).symm
      rw [this]
      exact hc.comp (T₁.cont (x : T₁.V))
    L :=
      { T := lker_lat F
        stable := fun g x hx => T₁.L.stable g _ hx
        fg := by
          obtain ⟨i, p, hpi⟩ := lker_lat_split F hOnto
          have : Module.Finite O ↥T₁.L.T := Module.Finite.iff_fg.2 T₁.L.fg
          have hp : Function.Surjective p := fun y => ⟨i y, LinearMap.congr_fun hpi y⟩
          exact Module.Finite.iff_fg.1 (Module.Finite.of_surjective p hp)
        free := by
          obtain ⟨i, p, hpi⟩ := lker_lat_split F hOnto
          have : Module.Finite O ↥T₁.L.T := Module.Finite.iff_fg.2 T₁.L.fg
          have : Module.Free O ↥T₁.L.T := T₁.L.free
          have hp : Function.Surjective p := fun y => ⟨i y, LinearMap.congr_fun hpi y⟩
          have : Module.Finite O ↥(lker_lat F) := Module.Finite.of_surjective p hp
          have : Module.Projective O ↥(lker_lat F) := Module.Projective.of_split i p hpi
          exact Module.free_of_flat_of_isLocalRing
        span := by
          rw [eq_top_iff]
          intro x _
          obtain ⟨a, ha, hax⟩ := lker_den hden T₁ (x : T₁.V)
          have hx : x = (algebraMap O LL a)⁻¹ • (a • x) := by
            rw [← algebraMap_smul LL a x, smul_smul, inv_mul_cancel₀ ha, one_smul]
          rw [hx]
          exact Submodule.smul_mem _ _ (Submodule.subset_span hax) } }

def lker_ι [IsLocalRing O] {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (hOnto : F.Onto)
    (hden : lker_Den LL O) : LatHom (lker_T₀ F hOnto hden).L T₁.L where
  f := (LinearMap.ker F.f).subtype
  equiv := fun _ _ => rfl
  cont := by
    have : ContinuousSMul LL T₁.V := IsModuleTopology.toContinuousSMul LL T₁.V
    change @Continuous ↥(LinearMap.ker F.f) T₁.V (moduleTopology LL ↥(LinearMap.ker F.f)) _
      (LinearMap.ker F.f).subtype
    let _ : TopologicalSpace ↥(LinearMap.ker F.f) := moduleTopology LL ↥(LinearMap.ker F.f)
    have : IsModuleTopology LL ↥(LinearMap.ker F.f) := ⟨rfl⟩
    exact IsModuleTopology.continuous_of_linearMap (LinearMap.ker F.f).subtype
  T_le := fun _ hx => hx

/- English proof (translation)
The claim follows from `lker_crys T₀.ρ T₁.ρ T₂.ρ i f r s hri hsplit hfs hfi hi hf h1 h2 (hFont T₀.V T₀.ρ)`.
-/
theorem lker_crysT (T₀ T₁ T₂ : LocLat G Qp LL O) (i : T₀.V →ₗ[LL] T₁.V) (f : T₁.V →ₗ[LL] T₂.V)
    (r : T₁.V →ₗ[LL] T₀.V) (s : T₂.V →ₗ[LL] T₁.V)
    (hri : r ∘ₗ i = LinearMap.id) (hsplit : i ∘ₗ r + s ∘ₗ f = LinearMap.id)
    (hfs : f ∘ₗ s = LinearMap.id) (hfi : f ∘ₗ i = 0)
    (hi : ∀ g x, i (T₀.ρ g x) = T₁.ρ g (i x)) (hf : ∀ g x, f (T₁.ρ g x) = T₂.ρ g (f x))
    (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (hFont : FontaineLe PD LL) : IsCrys PD T₀.ρ :=
  lker_crys T₀.ρ T₁.ρ T₂.ρ i f r s hri hsplit hfs hfi hi hf h1 h2 (hFont T₀.V T₀.ρ)

/- English proof (translation)
Introduce `T₁ T₂ F hS`. Take `⟨c1, c2, hOnto⟩` from `hS`. Use `⟨lker_T₀ F hOnto hden, lker_ι F hOnto hden, ⟨Subtype.val_injective, lker_surj F hOnto, hOnto, fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, ?_⟩, fun y hy => hy⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, rfl⟩`. Conclude with `y.2`.

Take `⟨r, s, hr, hsp, hfs⟩` from `lker_splitV F hOnto`. Conclude with `lker_crysT (lker_T₀ F hOnto hden) T₁ T₂ (lker_ι F hOnto hden).f F.f r s hr hsp hfs (LinearMap.ext fun x => LinearMap.mem_ker.1 x.2) (fun _ _ => rfl) F.equiv c1 c2 hFont`.
-/
theorem lker_HKer [IsLocalRing O] (W : LocWach PD LL O v n) (hden : lker_Den LL O)
    (hFont : FontaineLe PD LL) : liftb_HKer W := by
  intro T₁ T₂ F hS
  obtain ⟨c1, c2, hOnto⟩ := hS
  refine ⟨lker_T₀ F hOnto hden, lker_ι F hOnto hden,
    ⟨Subtype.val_injective, lker_surj F hOnto, hOnto,
      fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, ?_⟩, fun y hy => hy⟩, ?_⟩
  · rintro ⟨y, rfl⟩
    exact y.2
  · obtain ⟨r, s, hr, hsp, hfs⟩ := lker_splitV F hOnto
    exact lker_crysT (lker_T₀ F hOnto hden) T₁ T₂ (lker_ι F hOnto hden).f F.f r s hr hsp hfs
      (LinearMap.ext fun x => LinearMap.mem_ker.1 x.2) (fun _ _ => rfl) F.equiv c1 c2 hFont

end LiftKer

/- English proof (translation)
Use `lkd_local (D.loc l) LL` as an intermediate fact. Conclude with `lker_HKer _ (lkd_den (D.loc l) LL) (a22 l K LL)`.
-/
theorem lker_HKer_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l)
    (s : ℕ) (LL : FinExt l) (h : Good K s LL) : liftb_HKer ((HW l).W K s LL h) := by
  have := lkd_local (D.loc l) LL
  exact lker_HKer _ (lkd_den (D.loc l) LL) (a22 l K LL)

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LiftReg

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

/- English proof (translation)
Establish `hpC : (p : PowerSeries O) = PowerSeries.C (p : O)` using `(map_natCast PowerSeries.C p).symm`. Use `set b := m - r' * a with hb`. Establish `h1 : (p : PowerSeries O) * a = x * b`. Rewrite using `[hb, mul_sub, ← h, hq]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : PowerSeries.X ^ d * b = (p : PowerSeries O) * (a - r * b)`. Establish `: x * b = PowerSeries.X ^ d * b + (p : PowerSeries O) * (r * b)` using `by rw [hx]; ring`. Take the linear combination `-h1 - this`. Use `set b' : PowerSeries O := PowerSeries.mk fun k => PowerSeries.coeff (k + d) (a - r * b) with hb'`. Establish `h3 : b = (p : PowerSeries O) * b'`.

Use extensionality with `k`. Use `congrArg (PowerSeries.coeff (k + d)) h2` as an intermediate fact. Rewrite `this` using `[PowerSeries.coeff_X_pow_mul, hpC, PowerSeries.coeff_C_mul]`. Rewrite using `[hpC, PowerSeries.coeff_C_mul, hb', PowerSeries.coeff_mk]`. Conclude with `this`.

Use `⟨b', ?_⟩` and prove the remaining obligations. Establish `h4 : (p : PowerSeries O) * (a - x * b') = 0`. Rewrite using `[mul_sub, h1, h3]`. Expand and normalize the polynomial expressions, which then agree. Establish `h5 : a - x * b' = 0`.

Use extensionality with `k`. Use `congrArg (PowerSeries.coeff k) h4` as an intermediate fact. Rewrite `this` using `[hpC, PowerSeries.coeff_C_mul, map_zero]`. Rewrite using `[map_zero]`. Conclude with `hreg _ this`.

Conclude with `sub_eq_zero.1 h5`.
-/
theorem lreg_ring (p : ℕ) (hreg : ∀ c : O, (p : O) * c = 0 → c = 0) (x q a m r r' : PowerSeries O)
    (d : ℕ) (hx : x = PowerSeries.X ^ d + (p : PowerSeries O) * r)
    (hq : q = (p : PowerSeries O) + x * r') (h : q * a = x * m) : ∃ a', a = x * a' := by
  have hpC : (p : PowerSeries O) = PowerSeries.C (p : O) := (map_natCast PowerSeries.C p).symm
  set b := m - r' * a with hb
  have h1 : (p : PowerSeries O) * a = x * b := by
    rw [hb, mul_sub, ← h, hq]; ring
  have h2 : PowerSeries.X ^ d * b = (p : PowerSeries O) * (a - r * b) := by
    have : x * b = PowerSeries.X ^ d * b + (p : PowerSeries O) * (r * b) := by rw [hx]; ring
    linear_combination -h1 - this
  set b' : PowerSeries O := PowerSeries.mk fun k => PowerSeries.coeff (k + d) (a - r * b) with hb'
  have h3 : b = (p : PowerSeries O) * b' := by
    ext k
    have := congrArg (PowerSeries.coeff (k + d)) h2
    rw [PowerSeries.coeff_X_pow_mul, hpC, PowerSeries.coeff_C_mul] at this
    rw [hpC, PowerSeries.coeff_C_mul, hb', PowerSeries.coeff_mk]
    exact this
  refine ⟨b', ?_⟩
  have h4 : (p : PowerSeries O) * (a - x * b') = 0 := by
    rw [mul_sub, h1, h3]; ring
  have h5 : a - x * b' = 0 := by
    ext k
    have := congrArg (PowerSeries.coeff k) h4
    rw [hpC, PowerSeries.coeff_C_mul, map_zero] at this
    rw [map_zero]
    exact hreg _ this
  exact sub_eq_zero.1 h5

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `succ k ih`. Take `⟨r, hr⟩` from `ih`. Take `⟨w, hw⟩` from `liftb_q W`.

Establish `hp : PD.p = (PD.p - 1) + 1` using `(Nat.sub_add_cancel PD.hp.one_le).symm`. Establish `hφπ : W.φA letπ = letπ ^ PD.p + ((PD.p : ℕ) : LetA O n) * (letπ * w)`. Establish `hpow : (letπ : LetA O n) ^ PD.p = letπ * letπ ^ (PD.p - 1)` using `by conv_lhs => rw [hp, pow_succ']`. Rewrite using `[W.φA_π, hw, hpow]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨c, hc⟩` from `sub_dvd_pow_sub_pow (W.φA letπ) (letπ ^ PD.p : LetA O n) (PD.p ^ k)`. Establish `hdiff : W.φA letπ - letπ ^ PD.p = ((PD.p : ℕ) : LetA O n) * (letπ * w)`. Rewrite using `[hφπ]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨letπ * w * c + W.φA r, ?_⟩` and prove the remaining obligations.

Rewrite using `[pow_succ', AlgHom.mul_apply, hr, map_add, map_mul, map_pow, map_natCast]`. Establish `: W.φA letπ ^ (PD.p ^ k) = (letπ ^ PD.p : LetA O n) ^ (PD.p ^ k) + ((PD.p : ℕ) : LetA O n) * (letπ * w) * c`. Rewrite using `[← hdiff, ← hc]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, ← pow_mul, ← pow_succ']`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem lreg_X (W : LocWach PD LL O v n) (k : ℕ) :
    ∃ r : LetA O n, (W.φA ^ k) letπ = letπ ^ (PD.p ^ k) + ((PD.p : ℕ) : LetA O n) * r := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨w, hw⟩ := liftb_q W
    have hp : PD.p = (PD.p - 1) + 1 := (Nat.sub_add_cancel PD.hp.one_le).symm
    have hφπ : W.φA letπ = letπ ^ PD.p + ((PD.p : ℕ) : LetA O n) * (letπ * w) := by
      have hpow : (letπ : LetA O n) ^ PD.p = letπ * letπ ^ (PD.p - 1) := by
        conv_lhs => rw [hp, pow_succ']
      rw [W.φA_π, hw, hpow]
      ring
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (W.φA letπ) (letπ ^ PD.p : LetA O n) (PD.p ^ k)
    have hdiff : W.φA letπ - letπ ^ PD.p = ((PD.p : ℕ) : LetA O n) * (letπ * w) := by
      rw [hφπ]; ring
    refine ⟨letπ * w * c + W.φA r, ?_⟩
    rw [pow_succ', AlgHom.mul_apply, hr, map_add, map_mul, map_pow, map_natCast]
    have : W.φA letπ ^ (PD.p ^ k) = (letπ ^ PD.p : LetA O n) ^ (PD.p ^ k) +
        ((PD.p : ℕ) : LetA O n) * (letπ * w) * c := by
      rw [← hdiff, ← hc]; ring
    rw [this, ← pow_mul, ← pow_succ']
    ring

/- English proof (translation)
Establish `h1 : W.q₀ = ∑ i ∈ Finset.range PD.p, (1 + PowerSeries.X : PowerSeries O) ^ i`. Apply `liftb_X_cancel` to reduce the goal to its premises. Rewrite using `[W.q₀_def]`. Use `mul_geom_sum (1 + PowerSeries.X : PowerSeries O) PD.p` as an intermediate fact. Rewrite using `[← this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : (PowerSeries.X : PowerSeries O) ∣ ∑ i ∈ Finset.range PD.p, ((1 + PowerSeries.X : PowerSeries O) ^ i - 1)`. Apply `Finset.dvd_sum` to reduce the goal to its premises. Introduce `i _`. Use `sub_dvd_pow_sub_pow (1 + PowerSeries.X : PowerSeries O) 1 i` as an intermediate fact.

Simplify using `using this`. Take `⟨r, hr⟩` from `h2`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[← hr, h1, Finset.sum_sub_distrib]`. Simplify using the standard rewrite rules.
-/
theorem lreg_q₀ (W : LocWach PD LL O v n) :
    ∃ r : PowerSeries O, W.q₀ = ((PD.p : ℕ) : PowerSeries O) + PowerSeries.X * r := by
  have h1 : W.q₀ = ∑ i ∈ Finset.range PD.p, (1 + PowerSeries.X : PowerSeries O) ^ i := by
    apply liftb_X_cancel
    rw [W.q₀_def]
    have := mul_geom_sum (1 + PowerSeries.X : PowerSeries O) PD.p
    rw [← this]
    ring
  have h2 : (PowerSeries.X : PowerSeries O) ∣
      ∑ i ∈ Finset.range PD.p, ((1 + PowerSeries.X : PowerSeries O) ^ i - 1) := by
    apply Finset.dvd_sum
    intro i _
    have := sub_dvd_pow_sub_pow (1 + PowerSeries.X : PowerSeries O) 1 i
    simpa using this
  obtain ⟨r, hr⟩ := h2
  refine ⟨r, ?_⟩
  rw [← hr, h1, Finset.sum_sub_distrib]
  simp

/- English proof (translation)
Take `⟨r₀, hr₀⟩` from `lreg_q₀ W`. Establish `hq : W.q = ((PD.p : ℕ) : LetA O n) + letπ * (fun _ => r₀)`. Use function extensionality and compare the values at `i`. Simplify using `only [LocWach.q, letπ, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply]`. Conclude with `hr₀`.

Use `⟨(W.φA ^ (W.s - 1)) (fun _ => r₀), ?_⟩` and prove the remaining obligations. Unfold `LocWach.Q LocWach.X`. Rewrite using `[hq, map_add, map_mul, map_natCast]`.
-/
theorem lreg_Q (W : LocWach PD LL O v n) :
    ∃ r : LetA O n, W.Q = ((PD.p : ℕ) : LetA O n) + W.X * r := by
  obtain ⟨r₀, hr₀⟩ := lreg_q₀ W
  have hq : W.q = ((PD.p : ℕ) : LetA O n) + letπ * (fun _ => r₀) := by
    funext i
    simp only [LocWach.q, letπ, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply]
    exact hr₀
  refine ⟨(W.φA ^ (W.s - 1)) (fun _ => r₀), ?_⟩
  unfold LocWach.Q LocWach.X
  rw [hq, map_add, map_mul, map_natCast]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hj]`.
-/
theorem lreg_mul_single (c : LetA O n) (i : ZMod n) (y : PowerSeries O) :
    c * (Pi.single i y : LetA O n) = Pi.single i (c i * y) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

/- English proof (translation)
Use `liftb_neZero W` as an intermediate fact. Take `⟨rX, hrX⟩` from `lreg_X W (W.s - 1)`. Take `⟨rQ, hrQ⟩` from `lreg_Q W`. Establish `hXi : ∀ i : ZMod n, W.X i = PowerSeries.X ^ (PD.p ^ (W.s - 1)) + ((PD.p : ℕ) : PowerSeries O) * rX i`. Introduce `i`.

Use `show ((W.φA ^ (W.s - 1)) letπ) i = _`. Rewrite using `[hrX]`. Both sides reduce to the same expression. Establish `hQi : ∀ i : ZMod n, W.Q i = ((PD.p : ℕ) : PowerSeries O) + W.X i * rQ i`. Introduce `i`.

Rewrite using `[hrQ]`. Both sides reduce to the same expression. Introduce `x hx ⟨m, hm, hxm⟩`. Establish `key : ∀ i : ZMod n, ∃ y ∈ W.N T, (letE i : LetA O n) • x = W.X • y`. Introduce `i`.

Take `⟨r, b, hb, huniq⟩` from `hfree.2 i`. Take `⟨a, ha, _⟩` from `huniq _ (liftb_letE_mem W T i hx)`. Take `⟨c, hc, _⟩` from `huniq _ (liftb_letE_mem W T i hm)`. Establish `hmem : W.Q • ((letE i : LetA O n) • x) ∈ W.Nl T i` using `(W.Nl T i).smul_mem _ (liftb_letE_mem W T i hx)`. Establish `e1 : W.Q • ((letE i : LetA O n) • x) = ∑ j, (Pi.single i (W.Q i * a j) : LetA O n) • b j`.

Rewrite using `[ha, Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, lreg_mul_single]`. Establish `e2 : W.Q • ((letE i : LetA O n) • x) = ∑ j, (Pi.single i (W.X i * c j) : LetA O n) • b j`. Rewrite using `[smul_comm, hxm, smul_comm, hc, Finset.smul_sum]`.

Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, lreg_mul_single]`. Establish `heq : (fun j => W.Q i * a j) = fun j => W.X i * c j` using `(huniq _ hmem).unique e1 e2`. Establish `hdiv : ∀ j, ∃ a', a j = W.X i * a'` using `fun j => lreg_ring PD.p hreg (W.X i) (W.Q i) (a j) (c j) (rX i) (rQ i) _ (hXi i) (hQi i) (congrFun heq j)`. Use `choose a' ha' using hdiv`.

Use `⟨∑ j, (Pi.single i (a' j) : LetA O n) • b j, Submodule.sum_mem _ (fun j _ => (W.N T).smul_mem _ (liftb_Nl_le W T i (hb j))), ?_⟩` and prove the remaining obligations. Rewrite using `[ha, Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, lreg_mul_single, ← ha']`. Use `choose y hy hyy using key`.

Use `⟨∑ i, y i, Submodule.sum_mem _ (fun i _ => hy i), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum, ← Finset.sum_congr rfl (fun i _ => hyy i), ← liftb_split W T x]`.
-/
theorem lreg_RegXQ (W : LocWach PD LL O v n) (hreg : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0)
    (T : LocLat G Qp LL O) (hfree : Formalism.MainNotions.DeltaInvariantLattices.wachFree W T) : liftb_RegXQ W T := by
  have := liftb_neZero W
  obtain ⟨rX, hrX⟩ := lreg_X W (W.s - 1)
  obtain ⟨rQ, hrQ⟩ := lreg_Q W
  have hXi : ∀ i : ZMod n, W.X i = PowerSeries.X ^ (PD.p ^ (W.s - 1)) +
      ((PD.p : ℕ) : PowerSeries O) * rX i := by
    intro i
    show ((W.φA ^ (W.s - 1)) letπ) i = _
    rw [hrX]
    rfl
  have hQi : ∀ i : ZMod n, W.Q i = ((PD.p : ℕ) : PowerSeries O) + W.X i * rQ i := by
    intro i
    rw [hrQ]
    rfl
  intro x hx ⟨m, hm, hxm⟩
  have key : ∀ i : ZMod n, ∃ y ∈ W.N T, (letE i : LetA O n) • x = W.X • y := by
    intro i
    obtain ⟨r, b, hb, huniq⟩ := hfree.2 i
    obtain ⟨a, ha, _⟩ := huniq _ (liftb_letE_mem W T i hx)
    obtain ⟨c, hc, _⟩ := huniq _ (liftb_letE_mem W T i hm)
    have hmem : W.Q • ((letE i : LetA O n) • x) ∈ W.Nl T i :=
      (W.Nl T i).smul_mem _ (liftb_letE_mem W T i hx)
    have e1 : W.Q • ((letE i : LetA O n) • x) =
        ∑ j, (Pi.single i (W.Q i * a j) : LetA O n) • b j := by
      rw [ha, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_smul, lreg_mul_single]
    have e2 : W.Q • ((letE i : LetA O n) • x) =
        ∑ j, (Pi.single i (W.X i * c j) : LetA O n) • b j := by
      rw [smul_comm, hxm, smul_comm, hc, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [smul_smul, lreg_mul_single]
    have heq : (fun j => W.Q i * a j) = fun j => W.X i * c j :=
      (huniq _ hmem).unique e1 e2
    have hdiv : ∀ j, ∃ a', a j = W.X i * a' := fun j =>
      lreg_ring PD.p hreg (W.X i) (W.Q i) (a j) (c j) (rX i) (rQ i) _ (hXi i) (hQi i)
        (congrFun heq j)
    choose a' ha' using hdiv
    refine ⟨∑ j, (Pi.single i (a' j) : LetA O n) • b j,
      Submodule.sum_mem _ (fun j _ => (W.N T).smul_mem _ (liftb_Nl_le W T i (hb j))), ?_⟩
    rw [ha, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_smul, lreg_mul_single, ← ha']
  choose y hy hyy using key
  refine ⟨∑ i, y i, Submodule.sum_mem _ (fun i _ => hy i), ?_⟩
  rw [Finset.smul_sum, ← Finset.sum_congr rfl (fun i _ => hyy i), ← liftb_split W T x]

def lreg_HCompl (W : LocWach PD LL O v n) : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → liftb_Complete W T

/- English proof (translation)
Introduce `T hT` and use `⟨hC T hT, lreg_RegXQ W hreg T (h1 T hT)⟩`.
-/
theorem lreg_HStr_of (W : LocWach PD LL O v n)
    (hreg : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0) (h1 : Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFree W)
    (hC : lreg_HCompl W) : liftb_HStr W :=
  fun T hT => ⟨hC T hT, lreg_RegXQ W hreg T (h1 T hT)⟩

end LiftReg

/- English proof (translation)
Introduce `c hc`. Rewrite `hc` using `[(D.loc l).PD_p K]`. Establish `hl : ((l : ℕ) : ↥(OL LL)) ≠ 0`. Introduce `h0`. Establish `h1 : algebraMap ℤ_[l] ↥(OL LL) ((l : ℕ) : ℤ_[l]) = algebraMap ℤ_[l] ↥(OL LL) 0`.

Rewrite using `[map_natCast, map_zero, h0]`. Establish `h2` using `zl_inj_O LL h1`. Conclude with `(Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)`. Conclude with `(mul_eq_zero.1 hc).resolve_left hl`.
-/
theorem lreg_reg_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) :
    ∀ c : ↥(OL LL), ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) * c = 0 → c = 0 := by
  intro c hc
  rw [(D.loc l).PD_p K] at hc
  have hl : ((l : ℕ) : ↥(OL LL)) ≠ 0 := by
    intro h0
    have h1 : algebraMap ℤ_[l] ↥(OL LL) ((l : ℕ) : ℤ_[l]) = algebraMap ℤ_[l] ↥(OL LL) 0 := by
      rw [map_natCast, map_zero, h0]
    have h2 := zl_inj_O LL h1
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast h2)
  exact (mul_eq_zero.1 hc).resolve_left hl

/- English proof (translation)
The claim follows from `lreg_RegXQ _ (lreg_reg_D D HW F l K LL) T ((a1 l K s LL h) T hT)`.
-/
theorem lreg_RegXQ_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a1 : adm1 D HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys ((D.loc l).PD K) T.ρ) : liftb_RegXQ ((HW l).W K s LL h) T :=
  lreg_RegXQ _ (lreg_reg_D D HW F l K LL) T ((a1 l K s LL h) T hT)

/- English proof (translation)
The claim follows from `lreg_HStr_of _ (lreg_reg_D D HW F l K LL) (a1 l K s LL h) hC`.
-/
theorem lreg_HStr_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a1 : adm1 D HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (hC : lreg_HCompl ((HW l).W K s LL h)) :
    liftb_HStr ((HW l).W K s LL h) :=
  lreg_HStr_of _ (lreg_reg_D D HW F l K LL) (a1 l K s LL h) hC

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def liftOpen (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    linj_HMid ((HW l).W K s LL h)

def liftBOpen (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    liftb_HStr ((HW l).W K s LL h)

def liftAOpen (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    lifta_HStr ((HW l).W K s LL h)

/- English proof (translation)
Introduce `l _ K s LL h` and use `lreg_HStr_D D HW F a1 l K s LL h (hC l K s LL h)`.
-/
theorem liftBOpen_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a1 : adm1 D HW F)
    (hC : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      lreg_HCompl ((HW l).W K s LL h)) : liftBOpen D HW F :=
  fun l _ K s LL h => lreg_HStr_D D HW F a1 l K s LL h (hC l K s LL h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨(lone_HOne0_holds D HW F l K s LL h).1, (lone_HOne0_holds D HW F l K s LL h).2, liftb_oneGen _ ((F l).E K s LL h).tie⟩`.
-/
theorem liftb_HOne_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) : liftb_HOne ((HW l).W K s LL h) :=
  ⟨(lone_HOne0_holds D HW F l K s LL h).1, (lone_HOne0_holds D HW F l K s LL h).2,
    liftb_oneGen _ ((F l).E K s LL h).tie⟩

/- English proof (translation)
The claim follows from `lext_HExt_D D HW F l K s LL h (lone_HOne0_holds D HW F l K s LL h).1`.
-/
theorem liftb_HExt_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) : liftb_HExt ((HW l).W K s LL h) :=
  lext_HExt_D D HW F l K s LL h (lone_HOne0_holds D HW F l K s LL h).1

/- English proof (translation)
Introduce `l _ K s LL h`. Take `⟨z, hz, hzv⟩` from `gam_zl (P := D.loc l) (H := HW l) h`. Conclude with `coreLiftB_of (ℓ := l) ((HW l).W K s LL h) ((D.loc l).PD_p K) z hz (by rw [(HW l).W_s]; exact hzv) (fun _ _ _ => True) (a2 l K s LL h) (a5 l K s LL h) (a6 l K s LL h) (a11 l K s LL h) (a13 l K s LL h) (a14 l K s LL h) (a15 l K s LL h) (a17 l K s LL h) (a21 l K s LL h).1 (a23 l K L …`.
-/
theorem lifting_case_B_of_open (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a2 : adm2 D HW F) (a5 : adm5 D HW F) (a6 : adm6 D HW F) (a11 : adm11 D HW F)
    (a13 : adm13 D HW F) (a14 : adm14 D HW F) (a15 : adm15 D HW F) (a17 : adm17 D HW F) (a21 : Formalism.MainNotions.CrystallineLiftingBounds.adm21 D HW F)
    (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F) (a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F) (hWB : WachKillsCaseB D HW F) (hO : liftOpen D HW F) (hOB : liftBOpen D HW F) :
    LiftTheoremCaseB D HW F := by
  intro l _ K s LL h
  obtain ⟨z, hz, hzv⟩ := gam_zl (P := D.loc l) (H := HW l) h
  exact coreLiftB_of (ℓ := l) ((HW l).W K s LL h) ((D.loc l).PD_p K) z hz
    (by rw [(HW l).W_s]; exact hzv) (fun _ _ _ => True) (a2 l K s LL h) (a5 l K s LL h) (a6 l K s LL h)
    (a11 l K s LL h) (a13 l K s LL h) (a14 l K s LL h) (a15 l K s LL h) (a17 l K s LL h)
    (a21 l K s LL h).1 (a23 l K LL) (hWB l K s LL h) (lker_HKer_D D HW F a22 l K s LL h)
    (linj_HExact_of _ ((F l).E K s LL h).tie (hO l K s LL h)) (hOB l K s LL h)
    (liftb_HExt_holds D HW F l K s LL h) (liftb_HOne_holds D HW F l K s LL h)

/- English proof (translation)
Introduce `l _ K s LL h`. Take `⟨z, hz, hzv⟩` from `gam_zl (P := D.loc l) (H := HW l) h`. Conclude with `coreLiftA_of (ℓ := l) ((HW l).W K s LL h) ((D.loc l).PD_p K) z hz (by rw [(HW l).W_s]; exact hzv) (a2 l K s LL h) (a5 l K s LL h) (a6 l K s LL h) (a9 l K s LL h) (a13 l K s LL h) (a14 l K s LL h) (a15 l K s LL h) (a18 l K s LL h) (a19 l K s LL h) (fun h1 h2 => (a21 l K s LL h).2 …`.
-/
theorem lifting_case_A_of_open (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a2 : adm2 D HW F) (a5 : adm5 D HW F) (a6 : adm6 D HW F) (a9 : adm9 D HW F)
    (a13 : adm13 D HW F) (a14 : adm14 D HW F) (a15 : adm15 D HW F) (a18 : adm18 D HW F) (a19 : adm19 D HW F)
    (a21 : Formalism.MainNotions.CrystallineLiftingBounds.adm21 D HW F) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F) (a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F) (hWA : WachKillsCaseA D HW F) (hO : liftOpen D HW F)
    (hOA : liftAOpen D HW F) : LiftTheoremCaseA D HW F := by
  intro l _ K s LL h
  obtain ⟨z, hz, hzv⟩ := gam_zl (P := D.loc l) (H := HW l) h
  exact coreLiftA_of (ℓ := l) ((HW l).W K s LL h) ((D.loc l).PD_p K) z hz
    (by rw [(HW l).W_s]; exact hzv) (a2 l K s LL h) (a5 l K s LL h) (a6 l K s LL h)
    (a9 l K s LL h) (a13 l K s LL h) (a14 l K s LL h) (a15 l K s LL h) (a18 l K s LL h)
    (a19 l K s LL h)
    (fun h1 h2 => (a21 l K s LL h).2 (by rw [← (HW l).W_s K s LL h]; exact h1)
      (by rw [← (D.loc l).PD_p K]; exact h2))
    (Formalism.MainNotions.CrystallineLiftingBounds.resK_holds D HW F l K s LL h) (a23 l K LL) (hWA l K s LL h) (lker_HKer_D D HW F a22 l K s LL h)
    (linj_HExact_of _ ((F l).E K s LL h).tie (hO l K s LL h)) (hOA l K s LL h)
    (liftb_HExt_holds D HW F l K s LL h) (liftb_HOne_holds D HW F l K s LL h)

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open PowerSeries

section HStr1

variable {O : Type} [CommRing O]

def gradedIdeal (ϖ : O) (k : ℕ) : Ideal (PowerSeries O) where
  carrier := {f | ∀ j, coeff j f ∈ Ideal.span {ϖ} ^ (k - j)}
  add_mem' := by
    intro a b ha hb j
    rw [map_add]
    exact Ideal.add_mem _ (ha j) (hb j)
  zero_mem' := by
    intro j
    rw [map_zero]
    exact Ideal.zero_mem _
  smul_mem' := by
    intro c f hf j
    rw [smul_eq_mul, coeff_mul]
    refine Ideal.sum_mem _ (fun p hp => ?_)
    have hle : p.2 ≤ j := by
      have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
      omega
    exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) (hf p.2))

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_gradedIdeal_iff (ϖ : O) (k : ℕ) (f : PowerSeries O) :
    f ∈ gradedIdeal ϖ k ↔ ∀ j, coeff j f ∈ Ideal.span {ϖ} ^ (k - j) := Iff.rfl

/- English proof (translation)
Introduce `j`. Rewrite using `[coeff_C_mul]`. Establish `h1 : ϖ * coeff j f ∈ Ideal.span {ϖ} ^ (k - j + 1)`. Rewrite using `[pow_succ']`. Conclude with `Ideal.mul_mem_mul (Ideal.mem_span_singleton_self ϖ) (hf j)`.

Conclude with `Ideal.pow_le_pow_right (by omega) h1`.
-/
theorem C_mul_mem_graded_ideal (ϖ : O) (k : ℕ) (f : PowerSeries O) (hf : f ∈ gradedIdeal ϖ k) :
    C ϖ * f ∈ gradedIdeal ϖ (k + 1) := by
  intro j
  rw [coeff_C_mul]
  have h1 : ϖ * coeff j f ∈ Ideal.span {ϖ} ^ (k - j + 1) := by
    rw [pow_succ']
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self ϖ) (hf j)
  exact Ideal.pow_le_pow_right (by omega) h1

/- English proof (translation)
Introduce `j`. Consider the cases of `j with`. Consider the case `zero`. Rewrite using `[coeff_zero_X_mul]`. Conclude with `Ideal.zero_mem _`.

Consider the case `succ j`. Rewrite using `[coeff_succ_X_mul]`. Use `hf j` as an intermediate fact. Rewrite using `[show k + 1 - (j + 1) = k - j by omega]` and apply the resulting hypothesis.
-/
theorem X_mul_mem_graded_ideal (ϖ : O) (k : ℕ) (f : PowerSeries O) (hf : f ∈ gradedIdeal ϖ k) :
    X * f ∈ gradedIdeal ϖ (k + 1) := by
  intro j
  cases j with
  | zero =>
    rw [coeff_zero_X_mul]
    exact Ideal.zero_mem _
  | succ j =>
    rw [coeff_succ_X_mul]
    have := hf j
    rwa [show k + 1 - (j + 1) = k - j by omega]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `f _ j`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Rewrite using `[pow_succ']`. Use `Ideal.mul_le.2 (fun r hr s hs => ?_)` and prove the remaining obligations. Take `⟨a, b, rfl⟩` from `Ideal.mem_span_pair.1 hr`. Establish `e : (a * C ϖ + b * X) * s = a * (C ϖ * s) + b * (X * s)` using `by ring`. Rewrite using `[e]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ _ (C_mul_mem_graded_ideal ϖ k s (ih hs))) (Ideal.mul_mem_left _ _ (X_mul_mem_graded_ideal ϖ k s (ih hs)))`.
-/
theorem pow_le_graded_ideal (ϖ : O) (k : ℕ) :
    (Ideal.span {C ϖ, X} : Ideal (PowerSeries O)) ^ k ≤ gradedIdeal ϖ k := by
  induction k with
  | zero =>
    intro f _ j
    simp
  | succ k ih =>
    rw [pow_succ']
    refine Ideal.mul_le.2 (fun r hr s hs => ?_)
    obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.1 hr
    have e : (a * C ϖ + b * X) * s = a * (C ϖ * s) + b * (X * s) := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (C_mul_mem_graded_ideal ϖ k s (ih hs)))
      (Ideal.mul_mem_left _ _ (X_mul_mem_graded_ideal ϖ k s (ih hs)))

/- English proof (translation)
Establish `h1 : C c ∈ (Ideal.span {ϖ} ^ m).map (C : O →+* PowerSeries O)` using `Ideal.mem_map_of_mem _ hc`. Rewrite `h1` using `[Ideal.map_pow, Ideal.map_span, Set.image_singleton]`. Use `Ideal.pow_right_mono ?_ m h1` and prove the remaining obligations. Conclude with `Ideal.span_mono (by simp)`.
-/
theorem C_mem_ideal_pow (ϖ : O) (m : ℕ) (c : O) (hc : c ∈ Ideal.span {ϖ} ^ m) :
    C c ∈ (Ideal.span {C ϖ, X} : Ideal (PowerSeries O)) ^ m := by
  have h1 : C c ∈ (Ideal.span {ϖ} ^ m).map (C : O →+* PowerSeries O) := Ideal.mem_map_of_mem _ hc
  rw [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at h1
  refine Ideal.pow_right_mono ?_ m h1
  exact Ideal.span_mono (by simp)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `f _`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `f hf`. Rewrite using `[eq_shift_mul_X_add_const f]`. Use `Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Rewrite using `[pow_succ]`. Use `Ideal.mul_mem_mul (ih ?_) (Ideal.subset_span (by simp))` and prove the remaining obligations.

Introduce `j`. Rewrite using `[coeff_mk]`. Use `hf (j + 1)` as an intermediate fact. Rewrite `this` using `[show k + 1 - (j + 1) = k - j by omega]`. Then use the resulting hypothesis. Use `C_mem_ideal_pow ϖ (k + 1) _ ?_` and prove the remaining obligations.

Use `hf 0` as an intermediate fact. Rewrite `this` using `[coeff_zero_eq_constantCoeff_apply]`. Then use the resulting hypothesis.
-/
theorem graded_ideal_le_pow (ϖ : O) (k : ℕ) :
    gradedIdeal ϖ k ≤ (Ideal.span {C ϖ, X} : Ideal (PowerSeries O)) ^ k := by
  induction k with
  | zero =>
    intro f _
    simp
  | succ k ih =>
    intro f hf
    rw [eq_shift_mul_X_add_const f]
    refine Ideal.add_mem _ ?_ ?_
    · rw [pow_succ]
      refine Ideal.mul_mem_mul (ih ?_) (Ideal.subset_span (by simp))
      intro j
      rw [coeff_mk]
      have := hf (j + 1)
      rwa [show k + 1 - (j + 1) = k - j by omega] at this
    · refine C_mem_ideal_pow ϖ (k + 1) _ ?_
      have := hf 0
      rwa [coeff_zero_eq_constantCoeff_apply] at this

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => pow_le_graded_ideal ϖ k h, fun h => graded_ideal_le_pow ϖ k h⟩`.
-/
theorem mem_ideal_pow_iff_coeff (ϖ : O) (k : ℕ) (f : PowerSeries O) :
    f ∈ (Ideal.span {C ϖ, X} : Ideal (PowerSeries O)) ^ k ↔
      ∀ j, coeff j f ∈ Ideal.span {ϖ} ^ (k - j) :=
  ⟨fun h => pow_le_graded_ideal ϖ k h, fun h => graded_ideal_le_pow ϖ k h⟩

/- English proof (translation)
Introduce `x hx`. Use extensionality with `j`. Rewrite using `[map_zero]`. Use `IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) O) _ (fun m => ?_)` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`.

Establish `h1` using `hx (m + j)`. Rewrite `h1` using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`. Establish `h2` using `(mem_ideal_pow_iff_coeff ϖ (m + j) x).1 h1 j`. Rewrite `h2` using `[show m + j - j = m by omega]`. Then use the resulting hypothesis. Use the proof step `prec' := by`.

Introduce `f hf`. Establish `hc : ∀ j, ∃ c : O, ∀ m, coeff j (f (m + j)) ≡ c [SMOD (Ideal.span {ϖ} ^ m • ⊤ : Submodule O O)]`. Introduce `j`. Use `IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) O) (f := fun m => coeff j (f (m + j))) ?_` and prove the remaining obligations. Introduce `m m' hmm`.

Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Establish `h1` using `hf (show m + j ≤ m' + j by omega)`. Rewrite `h1` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Establish `h2` using `(mem_ideal_pow_iff_coeff ϖ (m + j) _).1 h1 j`. Rewrite `h2` using `[show m + j - j = m by omega, map_sub]`. Then use the resulting hypothesis.

Use `choose c hcc using hc`. Use `⟨PowerSeries.mk c, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_ideal_pow_iff_coeff]`. Introduce `j`. Rewrite using `[map_sub, coeff_mk]`.

Distinguish the cases in `hj : j ≤ m`. Establish `h1` using `hcc j (m - j)`. Rewrite `h1` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, show m - j + j = m by omega]`. Conclude with `h1`. Rewrite using `[show m - j = 0 by omega]`.

Simplify using the standard rewrite rules.
-/
theorem hstr_ps_complete (ϖ : O) [IsAdicComplete (Ideal.span {ϖ}) O] :
    IsAdicComplete (Ideal.span {PowerSeries.C ϖ, PowerSeries.X}) (PowerSeries O) where
  haus' := by
    intro x hx
    ext j
    rw [map_zero]
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {ϖ}) O) _ (fun m => ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have h1 := hx (m + j)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top] at h1
    have h2 := (mem_ideal_pow_iff_coeff ϖ (m + j) x).1 h1 j
    rwa [show m + j - j = m by omega] at h2
  prec' := by
    intro f hf
    have hc : ∀ j, ∃ c : O, ∀ m,
        coeff j (f (m + j)) ≡ c [SMOD (Ideal.span {ϖ} ^ m • ⊤ : Submodule O O)] := by
      intro j
      refine IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {ϖ}) O)
        (f := fun m => coeff j (f (m + j))) ?_
      intro m m' hmm
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have h1 := hf (show m + j ≤ m' + j by omega)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
      have h2 := (mem_ideal_pow_iff_coeff ϖ (m + j) _).1 h1 j
      rwa [show m + j - j = m by omega, map_sub] at h2
    choose c hcc using hc
    refine ⟨PowerSeries.mk c, fun m => ?_⟩
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_ideal_pow_iff_coeff]
    intro j
    rw [map_sub, coeff_mk]
    by_cases hj : j ≤ m
    · have h1 := hcc j (m - j)
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, show m - j + j = m by omega] at h1
      exact h1
    · rw [show m - j = 0 by omega]
      simp

end HStr1

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

/- English proof (translation)
Introduce `x hx`. Establish `h0 : e x = 0`. Use function extensionality and compare the values at `κ`. Use `IsHausdorff.haus (inferInstance : IsHausdorff I₀ R) _ (fun k => ?_)` and prove the remaining obligations. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`.

Conclude with `(h k x).1 (by simpa [SModEq.zero] using hx k) κ`. Conclude with `e.map_eq_zero_iff.1 h0`. Use the proof step `prec' := by`. Introduce `f hf`. Establish `hc : ∀ κ, ∃ L : R, ∀ k, e (f k) κ ≡ L [SMOD (I₀ ^ k • ⊤ : Submodule R R)]`.

Introduce `κ`. Use `IsPrecomplete.prec (inferInstance : IsPrecomplete I₀ R) (f := fun k => e (f k) κ) ?_` and prove the remaining obligations. Introduce `m k hmk`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Use `(h m (f m - f k)).1 (SModEq.sub_mem.1 (hf hmk)) κ` as an intermediate fact.

Simplify using `using this`. Use `choose L hL using hc`. Use `⟨e.symm L, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, h]`. Introduce `κ`.

Use `hL κ k` as an intermediate fact. Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]`. Simplify using `using this`.
-/
theorem hstr_coord {A M R ι : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing R]
    (I : Ideal A) (I₀ : Ideal R) [IsAdicComplete I₀ R] (e : M ≃+ (ι → R))
    (h : ∀ (k : ℕ) (x : M), x ∈ (I ^ k • ⊤ : Submodule A M) ↔ ∀ κ, e x κ ∈ I₀ ^ k) :
    IsAdicComplete I M where
  haus' := by
    intro x hx
    have h0 : e x = 0 := by
      funext κ
      refine IsHausdorff.haus (inferInstance : IsHausdorff I₀ R) _ (fun k => ?_)
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact (h k x).1 (by simpa [SModEq.zero] using hx k) κ
    exact e.map_eq_zero_iff.1 h0
  prec' := by
    intro f hf
    have hc : ∀ κ, ∃ L : R, ∀ k, e (f k) κ ≡ L [SMOD (I₀ ^ k • ⊤ : Submodule R R)] := by
      intro κ
      refine IsPrecomplete.prec (inferInstance : IsPrecomplete I₀ R) (f := fun k => e (f k) κ) ?_
      intro m k hmk
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have := (h m (f m - f k)).1 (SModEq.sub_mem.1 (hf hmk)) κ
      simpa using this
    choose L hL using hc
    refine ⟨e.symm L, fun k => ?_⟩
    rw [SModEq.sub_mem, h]
    intro κ
    have := hL κ k
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
    simpa using this

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section HStrRing

variable (O : Type) [CommRing O] (n p : ℕ)

def hstrConst : PowerSeries O →+* LetA O n := Pi.constRingHom (ZMod n) (PowerSeries O)

def hstrI₀ : Ideal (PowerSeries O) := Ideal.span {PowerSeries.C ((p : ℕ) : O), PowerSeries.X}

def hstrI : Ideal (LetA O n) := (hstrI₀ O p).map (hstrConst O n)

variable {O n p}

/- English proof (translation)
Establish `h1 : (Pi.single i r : LetA O n) = letE i * hstrConst O n r`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using `[letE, hstrConst]`.

Simplify using `[letE, Pi.single_eq_of_ne hj]`. Rewrite using `[h1]`. Use `Ideal.mul_mem_left _ _ ?_` and prove the remaining obligations. Rewrite using `[hstrI, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ hr`.
-/
theorem hstr_single_mem (i : ZMod n) (k : ℕ) {r : PowerSeries O} (hr : r ∈ hstrI₀ O p ^ k) :
    (Pi.single i r : LetA O n) ∈ hstrI O n p ^ k := by
  have h1 : (Pi.single i r : LetA O n) = letE i * hstrConst O n r := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [letE, hstrConst]
    · simp [letE, Pi.single_eq_of_ne hj]
  rw [h1]
  refine Ideal.mul_mem_left _ _ ?_
  rw [hstrI, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hr

/- English proof (translation)
Establish `h` using `Ideal.mem_map_of_mem (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i) ha`. Rewrite `h` using `[Ideal.map_pow, hstrI, Ideal.map_map]`. Establish `hc : (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i).comp (hstrConst O n) = RingHom.id _` using `rfl`. Rewrite `h` using `[hc, Ideal.map_id]`. Conclude with `h`.
-/
theorem hstr_eval_mem (i : ZMod n) (k : ℕ) {a : LetA O n} (ha : a ∈ hstrI O n p ^ k) :
    a i ∈ hstrI₀ O p ^ k := by
  have h := Ideal.mem_map_of_mem (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i) ha
  rw [Ideal.map_pow, hstrI, Ideal.map_map] at h
  have hc : (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i).comp (hstrConst O n) =
      RingHom.id _ := rfl
  rw [hc, Ideal.map_id] at h
  exact h

/- English proof (translation)
Establish `h : hstrConst O n (PowerSeries.C ((p : ℕ) : O)) = ((p : ℕ) : LetA O n)`. Rewrite using `[map_natCast, map_natCast]`. Rewrite using `[← h]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))`.
-/
theorem hstr_p_mem : ((p : ℕ) : LetA O n) ∈ hstrI O n p := by
  have h : hstrConst O n (PowerSeries.C ((p : ℕ) : O)) = ((p : ℕ) : LetA O n) := by
    rw [map_natCast, map_natCast]
  rw [← h]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))

/- English proof (translation)
Establish `h : hstrConst O n PowerSeries.X = (letπ : LetA O n)` using `rfl`. Rewrite using `[← h]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))`.
-/
theorem hstr_π_mem : (letπ : LetA O n) ∈ hstrI O n p := by
  have h : hstrConst O n PowerSeries.X = (letπ : LetA O n) := rfl
  rw [← h]
  exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hj]`.
-/
theorem hstr_mul_single (c : LetA O n) (i : ZMod n) (y : PowerSeries O) :
    c * (Pi.single i y : LetA O n) = Pi.single i (c i * y) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne hj]

end HStrRing

section HStrB

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

/- English proof (translation)
Establish `h : hstrI O n PD.p ≤ (hstrI O n PD.p).comap (W.φA : LetA O n →+* LetA O n)` using `by conv_lhs => rw [hstrI, hstrI₀, Ideal.map_span]`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Break down `hx with rfl | hx` into its components or cases. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap]`.

Establish `h : (W.φA : LetA O n →+* LetA O n) (hstrConst O n (PowerSeries.C ((PD.p : ℕ) : O))) = ((PD.p : ℕ) : LetA O n)`. Rewrite using `[map_natCast, map_natCast, map_natCast]`. Rewrite using `[h]`. Conclude with `hstr_p_mem`. Rewrite `hx` using `[Set.mem_singleton_iff]`.

Substitute `hx` using the available equality. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap]`. Establish `h : (W.φA : LetA O n →+* LetA O n) (hstrConst O n PowerSeries.X) = letπ * W.q` using `W.φA_π`. Rewrite using `[h]`. Conclude with `Ideal.mul_mem_right _ _ hstr_π_mem`.

Conclude with `fun a ha => h ha`.
-/
theorem hstr_φ_mem (W : LocWach PD LL O v n) : ∀ a ∈ hstrI O n PD.p, W.φA a ∈ hstrI O n PD.p := by
  have h : hstrI O n PD.p ≤ (hstrI O n PD.p).comap (W.φA : LetA O n →+* LetA O n) := by
    conv_lhs => rw [hstrI, hstrI₀, Ideal.map_span]
    rw [Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with rfl | hx
    · rw [SetLike.mem_coe, Ideal.mem_comap]
      have h : (W.φA : LetA O n →+* LetA O n) (hstrConst O n (PowerSeries.C ((PD.p : ℕ) : O))) =
          ((PD.p : ℕ) : LetA O n) := by
        rw [map_natCast, map_natCast, map_natCast]
      rw [h]
      exact hstr_p_mem
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, Ideal.mem_comap]
      have h : (W.φA : LetA O n →+* LetA O n) (hstrConst O n PowerSeries.X) = letπ * W.q := W.φA_π
      rw [h]
      exact Ideal.mul_mem_right _ _ hstr_π_mem
  exact fun a ha => h ha

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => exact fun a ha => by simpa using ha`. Consider the case `succ k ih`. Introduce `a ha`. Rewrite using `[pow_succ', AlgHom.mul_apply]`.

Conclude with `hstr_φ_mem W _ (ih a ha)`.
-/
theorem hstr_φpow_mem (W : LocWach PD LL O v n) (k : ℕ) :
    ∀ a ∈ hstrI O n PD.p, (W.φA ^ k) a ∈ hstrI O n PD.p := by
  induction k with
  | zero => exact fun a ha => by simpa using ha
  | succ k ih =>
    intro a ha
    rw [pow_succ', AlgHom.mul_apply]
    exact hstr_φ_mem W _ (ih a ha)

/- English proof (translation)
Take `⟨r, hr⟩` from `lreg_Q W`. Rewrite using `[hr]`. Conclude with `Ideal.add_mem _ hstr_p_mem (Ideal.mul_mem_right _ _ (hstr_φpow_mem W _ _ hstr_π_mem))`.
-/
theorem hstr_Q_mem (W : LocWach PD LL O v n) : W.Q ∈ hstrI O n PD.p := by
  obtain ⟨r, hr⟩ := lreg_Q W
  rw [hr]
  exact Ideal.add_mem _ hstr_p_mem (Ideal.mul_mem_right _ _ (hstr_φpow_mem W _ _ hstr_π_mem))

variable [NeZero n]

def hstrSyn (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (r : ZMod n → ℕ)
    (b : ∀ i, Fin (r i) → W.DD T) (hb : ∀ i j, b i j ∈ W.Nl T i) :
    ((Σ i, Fin (r i)) → PowerSeries O) →+ ↥(W.N T) where
  toFun c := ∑ κ : (Σ i, Fin (r i)), (Pi.single κ.1 (c κ) : LetA O n) •
    (⟨b κ.1 κ.2, liftb_Nl_le W T κ.1 (hb κ.1 κ.2)⟩ : ↥(W.N T))
  map_zero' := by simp
  map_add' c c' := by
    simp only [Pi.add_apply, Pi.single_add, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Rewrite using `[← Fintype.sum_sigma' (fun i j => (Pi.single i (c ⟨i, j⟩) : LetA O n) • b i j)]`. Simplify using `[hstrSyn]`.
-/
theorem hstr_syn_coe (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (r : ZMod n → ℕ)
    (b : ∀ i, Fin (r i) → W.DD T) (hb : ∀ i j, b i j ∈ W.Nl T i)
    (c : (Σ i, Fin (r i)) → PowerSeries O) :
    ((hstrSyn W T r b hb c : ↥(W.N T)) : W.DD T) =
      ∑ i, ∑ j, (Pi.single i (c ⟨i, j⟩) : LetA O n) • b i j := by
  rw [← Fintype.sum_sigma' (fun i j => (Pi.single i (c ⟨i, j⟩) : LetA O n) • b i j)]
  simp [hstrSyn]

/- English proof (translation)
Rewrite using `[hstr_syn_coe, Finset.smul_sum, Finset.sum_eq_single i]`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, hstr_mul_single]`. Simplify using `[letE]`.

Introduce `i' _ hi'`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_eq_zero (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[smul_smul, hstr_mul_single]`. Simplify using `[letE, Pi.single_eq_of_ne hi']`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem hstr_syn_letter (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (r : ZMod n → ℕ)
    (b : ∀ i, Fin (r i) → W.DD T) (hb : ∀ i j, b i j ∈ W.Nl T i)
    (c : (Σ i, Fin (r i)) → PowerSeries O) (i : ZMod n) :
    (letE i : LetA O n) • ((hstrSyn W T r b hb c : ↥(W.N T)) : W.DD T) =
      ∑ j, (Pi.single i (c ⟨i, j⟩) : LetA O n) • b i j := by
  rw [hstr_syn_coe, Finset.smul_sum, Finset.sum_eq_single i]
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_smul, hstr_mul_single]
    simp [letE]
  · intro i' _ hi'
    rw [Finset.smul_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [smul_smul, hstr_mul_single]
    simp [letE, Pi.single_eq_of_ne hi']
  · intro h; exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Simplify using `only [hstrSyn, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.smul_sum, smul_smul, hstr_mul_single]`.
-/
theorem hstr_syn_smul (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (r : ZMod n → ℕ)
    (b : ∀ i, Fin (r i) → W.DD T) (hb : ∀ i j, b i j ∈ W.Nl T i)
    (c : (Σ i, Fin (r i)) → PowerSeries O) (a : LetA O n) :
    a • hstrSyn W T r b hb c = hstrSyn W T r b hb (fun κ => a κ.1 * c κ) := by
  simp only [hstrSyn, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.smul_sum, smul_smul,
    hstr_mul_single]

/- English proof (translation)
Use `⟨hstrI O n PD.p, hstr_Q_mem W, hstr_φ_mem W, ?_⟩` and prove the remaining obligations. Use `choose r b hb huniq using hfree.2`. Establish `hinj : Function.Injective (hstrSyn W T r b hb)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`.

Use function extensionality and compare the values at `κ`. Take `⟨i, j⟩` from `κ`. Establish `h1` using `hstr_syn_letter W T r b hb c i`. Rewrite `h1` using `[hc]`. Establish `h2 : (0 : W.DD T) = ∑ j, (Pi.single i (c ⟨i, j⟩) : LetA O n) • b i j`.

Rewrite using `[← h1]`. Simplify using the standard rewrite rules. Establish `h3 : (0 : W.DD T) = ∑ j, (Pi.single i ((fun _ => 0 : Fin (r i) → PowerSeries O) j) : LetA O n) • b i j` using `by simp`. Conclude with `congrFun ((huniq i 0 (W.Nl T i).zero_mem).unique h2 h3) j`. Establish `hsurj : Function.Surjective (hstrSyn W T r b hb)`.

Introduce `x`. Establish `h1 : ∀ i, ∃ a : Fin (r i) → PowerSeries O, (letE i : LetA O n) • (x : W.DD T) = ∑ j, (Pi.single i (a j) : LetA O n) • b i j` using `fun i => (huniq i _ (liftb_letE_mem W T i x.2)).exists`. Use `choose a ha using h1`. Use `⟨fun κ => a κ.1 κ.2, Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hstr_syn_coe, liftb_split W T (x : W.DD T)]`.

Conclude with `Finset.sum_congr rfl (fun i _ => (ha i).symm)`. Set `e : ↥(W.N T) ≃+ ((Σ i, Fin (r i)) → PowerSeries O)` to `(AddEquiv.ofBijective (hstrSyn W T r b hb) ⟨hinj, hsurj⟩).symm`. Establish `he : ∀ c, e (hstrSyn W T r b hb c) = c` using `fun c => (AddEquiv.ofBijective (hstrSyn W T r b hb) ⟨hinj, hsurj⟩).symm_apply_apply c`. Establish `he' : ∀ x, hstrSyn W T r b hb (e x) = x` using `fun x => (AddEquiv.ofBijective (hstrSyn W T r b hb) ⟨hinj, hsurj⟩).apply_symm_apply x`. Use `hstr_coord (hstrI O n PD.p) (hstrI₀ O PD.p) e (fun k x => ⟨fun hx => ?_, fun hx => ?_⟩)` and prove the remaining obligations.

Use `Submodule.smul_induction_on (p := fun x => ∀ κ, e x κ ∈ hstrI₀ O PD.p ^ k) hx ?_ ?_` and prove the remaining obligations. Introduce `a ha y _ κ`. Rewrite using `[← he' y, hstr_syn_smul, he]`. Conclude with `Ideal.mul_mem_right _ _ (hstr_eval_mem κ.1 k ha)`. Introduce `y z hy hz κ`.

Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ (hy κ) (hz κ)`. Rewrite using `[← he' x] show (∑ κ : (Σ i, Fin (r i)), (Pi.single κ.1 (e x κ) : LetA O n) • (⟨b κ.1 κ.2, liftb_Nl_le W T κ.1 (hb κ.1 κ.2)⟩ : ↥(W.N T))) ∈ _`. Conclude with `Submodule.sum_mem _ (fun κ _ => Submodule.smul_mem_smul (hstr_single_mem κ.1 k (hx κ)) Submodule.mem_top)`.
-/
theorem hstr_CompleteB (W : LocWach PD LL O v n) [IsAdicComplete (hstrI₀ O PD.p) (PowerSeries O)]
    (T : LocLat G Qp LL O) (hfree : Formalism.MainNotions.DeltaInvariantLattices.wachFree W T) : liftb_Complete W T := by
  refine ⟨hstrI O n PD.p, hstr_Q_mem W, hstr_φ_mem W, ?_⟩
  choose r b hb huniq using hfree.2
  have hinj : Function.Injective (hstrSyn W T r b hb) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    funext κ
    obtain ⟨i, j⟩ := κ
    have h1 := hstr_syn_letter W T r b hb c i
    rw [hc] at h1
    have h2 : (0 : W.DD T) = ∑ j, (Pi.single i (c ⟨i, j⟩) : LetA O n) • b i j := by
      rw [← h1]; simp
    have h3 : (0 : W.DD T) = ∑ j, (Pi.single i ((fun _ => 0 : Fin (r i) → PowerSeries O) j) :
        LetA O n) • b i j := by simp
    exact congrFun ((huniq i 0 (W.Nl T i).zero_mem).unique h2 h3) j
  have hsurj : Function.Surjective (hstrSyn W T r b hb) := by
    intro x
    have h1 : ∀ i, ∃ a : Fin (r i) → PowerSeries O,
        (letE i : LetA O n) • (x : W.DD T) = ∑ j, (Pi.single i (a j) : LetA O n) • b i j :=
      fun i => (huniq i _ (liftb_letE_mem W T i x.2)).exists
    choose a ha using h1
    refine ⟨fun κ => a κ.1 κ.2, Subtype.ext ?_⟩
    rw [hstr_syn_coe, liftb_split W T (x : W.DD T)]
    exact Finset.sum_congr rfl (fun i _ => (ha i).symm)
  let e : ↥(W.N T) ≃+ ((Σ i, Fin (r i)) → PowerSeries O) :=
    (AddEquiv.ofBijective (hstrSyn W T r b hb) ⟨hinj, hsurj⟩).symm
  have he : ∀ c, e (hstrSyn W T r b hb c) = c := fun c =>
    (AddEquiv.ofBijective (hstrSyn W T r b hb) ⟨hinj, hsurj⟩).symm_apply_apply c
  have he' : ∀ x, hstrSyn W T r b hb (e x) = x := fun x =>
    (AddEquiv.ofBijective (hstrSyn W T r b hb) ⟨hinj, hsurj⟩).apply_symm_apply x
  refine hstr_coord (hstrI O n PD.p) (hstrI₀ O PD.p) e (fun k x => ⟨fun hx => ?_, fun hx => ?_⟩)
  · refine Submodule.smul_induction_on (p := fun x => ∀ κ, e x κ ∈ hstrI₀ O PD.p ^ k) hx ?_ ?_
    · intro a ha y _ κ
      rw [← he' y, hstr_syn_smul, he]
      exact Ideal.mul_mem_right _ _ (hstr_eval_mem κ.1 k ha)
    · intro y z hy hz κ
      rw [map_add]
      exact Ideal.add_mem _ (hy κ) (hz κ)
  · rw [← he' x]
    show (∑ κ : (Σ i, Fin (r i)), (Pi.single κ.1 (e x κ) : LetA O n) •
      (⟨b κ.1 κ.2, liftb_Nl_le W T κ.1 (hb κ.1 κ.2)⟩ : ↥(W.N T))) ∈ _
    exact Submodule.sum_mem _ (fun κ _ =>
      Submodule.smul_mem_smul (hstr_single_mem κ.1 k (hx κ)) Submodule.mem_top)

end HStrB

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

/- English proof (translation)
Rewrite using `[(D.loc l).PD_p K]`. Use `phib_OL_complete LL` as an intermediate fact. Conclude with `hstr_ps_complete ((l : ℕ) : ↥(OL LL))`.
-/
theorem hstr_ps_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) :
    IsAdicComplete (hstrI₀ ↥(OL LL) ((D.loc l).PD K).p) (PowerSeries ↥(OL LL)) := by
  rw [(D.loc l).PD_p K]
  have := phib_OL_complete LL
  exact hstr_ps_complete ((l : ℕ) : ↥(OL LL))

/- English proof (translation)
Use `liftb_neZero ((HW l).W K s LL h)` as an intermediate fact. Use `hstr_ps_D D HW F l K LL` as an intermediate fact. Conclude with `hstr_CompleteB _ T ((a1 l K s LL h) T hT)`.
-/
theorem hstr_CompleteB_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a1 : adm1 D HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys ((D.loc l).PD K) T.ρ) : liftb_Complete ((HW l).W K s LL h) T := by
  have := liftb_neZero ((HW l).W K s LL h)
  have := hstr_ps_D D HW F l K LL
  exact hstr_CompleteB _ T ((a1 l K s LL h) T hT)

/- English proof (translation)
The claim follows from `lreg_HStr_D D HW F a1 l K s LL h (fun T hT => hstr_CompleteB_D D HW F a1 l K s LL h T hT)`.
-/
theorem hstr_HStr_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a1 : adm1 D HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) : liftb_HStr ((HW l).W K s LL h) :=
  lreg_HStr_D D HW F a1 l K s LL h (fun T hT => hstr_CompleteB_D D HW F a1 l K s LL h T hT)

/- English proof (translation)
Introduce `l _ K s LL h` and use `hstr_HStr_D D HW F a1 l K s LL h`.
-/
theorem hstr_B (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a1 : adm1 D HW F) : liftBOpen D HW F :=
  fun l _ K s LL h => hstr_HStr_D D HW F a1 l K s LL h

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section HStrAbs

/- English proof (translation)
Set `bM : ι₁ → ↥N'` to `fun j => ⟨b j, hb j⟩`. Set `g : (ι₁ × ι₂ → R) →+ ↥N'` to `{ toFun := fun c => ∑ j, Θ (fun i => c (j, i)) • bM j map_zero' := by`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Establish `: (fun i : ι₂ => (0 : ι₁ × ι₂ → R) (j, i)) = (0 : ι₂ → R)` using `rfl`.

Rewrite using `[this, map_zero, zero_smul]`. Use the proof step `map_add' := by`. Introduce `c c'`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises.

Introduce `j _`. Establish `: (fun i : ι₂ => (c + c') (j, i)) = ((fun i => c (j, i)) + fun i => c' (j, i) : ι₂ → R)` using `rfl`. Rewrite using `[this, map_add, add_smul] }`. Establish `hg : ∀ c, g c = ∑ j, Θ (fun i => c (j, i)) • bM j` using `fun _ => rfl`. Establish `hgc : ∀ c, ((g c : ↥N') : D) = ∑ j, Θ (fun i => c (j, i)) • b j`.

Introduce `c`. Rewrite using `[hg, Submodule.coe_sum]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective g`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `c hc`. Establish `h0 : ∑ j, Θ (fun i => c (j, i)) • b j = 0`. Rewrite using `[← hgc, hc]`. Both sides reduce to the same expression. Establish `h1` using `huniq _ h0`.

Use function extensionality and compare the values at `κ`. Establish `h2 : Θ (fun i => c (κ.1, i)) = Θ 0`. Rewrite using `[map_zero]`. Conclude with `congrFun h1 κ.1`. Conclude with `congrFun (hΘ.1 h2) κ.2`.

Establish `hsurj : Function.Surjective g`. Introduce `x`. Take `⟨a, hx⟩` from `hspan x x.2`. Use `choose f hf using fun j => hΘ.2 (a j)`. Use `⟨fun κ => f κ.1 κ.2, Subtype.ext ?_⟩` and prove the remaining obligations.

Rewrite using `[hgc, hx]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Establish `: (fun i => f j i) = f j` using `rfl`. Rewrite using `[this, hf]`.

Set `e : ↥N' ≃+ (ι₁ × ι₂ → R)` to `(AddEquiv.ofBijective g ⟨hinj, hsurj⟩).symm`. Establish `hge : ∀ x, g (e x) = x` using `fun x => (AddEquiv.ofBijective g ⟨hinj, hsurj⟩).apply_symm_apply x`. Establish `heg : ∀ c, e (g c) = c` using `fun c => (AddEquiv.ofBijective g ⟨hinj, hsurj⟩).symm_apply_apply c`. Establish `hsmul : ∀ (f : ι₂ → R) c, Θ f • g c = g (fun κ => f κ.2 * c κ)`. Introduce `f c`.

Rewrite using `[hg, hg, Finset.smul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[smul_smul, ← map_mul]`. Both sides reduce to the same expression.

Use `hstr_coord I I₀ e (fun k x => ⟨fun hx => ?_, fun hc => ?_⟩)` and prove the remaining obligations. Use `Submodule.smul_induction_on (p := fun y => ∀ κ, e y κ ∈ I₀ ^ k) hx ?_ ?_` and prove the remaining obligations. Introduce `a ha y _ κ`. Take `⟨f, hf, rfl⟩` from `(hI k a).1 ha`. Rewrite using `[← hge y, hsmul, heg]`.

Conclude with `Ideal.mul_mem_right _ _ (hf κ.2)`. Introduce `y z hy hz κ`. Rewrite using `[map_add]`. Conclude with `Ideal.add_mem _ (hy κ) (hz κ)`. Rewrite using `[← hge x, hg]`.

Use `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem_smul ?_ trivial)` and prove the remaining obligations. Conclude with `(hI k _).2 ⟨_, fun i => hc (j, i), rfl⟩`.
-/
theorem hstra_abs {A' R D ι₁ ι₂ : Type} [CommRing A'] [CommRing R] [AddCommGroup D] [Module A' D]
    (N' : Submodule A' D) [Fintype ι₁] (Θ : (ι₂ → R) →+* A') (hΘ : Function.Bijective Θ)
    (I : Ideal A') (I₀ : Ideal R) [IsAdicComplete I₀ R]
    (hI : ∀ (k : ℕ) (a : A'), a ∈ I ^ k ↔ ∃ f : ι₂ → R, (∀ i, f i ∈ I₀ ^ k) ∧ Θ f = a)
    (b : ι₁ → D) (hb : ∀ j, b j ∈ N') (huniq : ∀ a : ι₁ → A', ∑ j, a j • b j = 0 → a = 0)
    (hspan : ∀ x ∈ N', ∃ a : ι₁ → A', x = ∑ j, a j • b j) : IsAdicComplete I ↥N' := by
  let bM : ι₁ → ↥N' := fun j => ⟨b j, hb j⟩
  let g : (ι₁ × ι₂ → R) →+ ↥N' :=
    { toFun := fun c => ∑ j, Θ (fun i => c (j, i)) • bM j
      map_zero' := by
        apply Finset.sum_eq_zero
        intro j _
        have : (fun i : ι₂ => (0 : ι₁ × ι₂ → R) (j, i)) = (0 : ι₂ → R) := rfl
        rw [this, map_zero, zero_smul]
      map_add' := by
        intro c c'
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        have : (fun i : ι₂ => (c + c') (j, i)) =
            ((fun i => c (j, i)) + fun i => c' (j, i) : ι₂ → R) := rfl
        rw [this, map_add, add_smul] }
  have hg : ∀ c, g c = ∑ j, Θ (fun i => c (j, i)) • bM j := fun _ => rfl
  have hgc : ∀ c, ((g c : ↥N') : D) = ∑ j, Θ (fun i => c (j, i)) • b j := by
    intro c
    rw [hg, Submodule.coe_sum]
    rfl
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have h0 : ∑ j, Θ (fun i => c (j, i)) • b j = 0 := by
      rw [← hgc, hc]
      rfl
    have h1 := huniq _ h0
    funext κ
    have h2 : Θ (fun i => c (κ.1, i)) = Θ 0 := by
      rw [map_zero]
      exact congrFun h1 κ.1
    exact congrFun (hΘ.1 h2) κ.2
  have hsurj : Function.Surjective g := by
    intro x
    obtain ⟨a, hx⟩ := hspan x x.2
    choose f hf using fun j => hΘ.2 (a j)
    refine ⟨fun κ => f κ.1 κ.2, Subtype.ext ?_⟩
    rw [hgc, hx]
    apply Finset.sum_congr rfl
    intro j _
    have : (fun i => f j i) = f j := rfl
    rw [this, hf]
  let e : ↥N' ≃+ (ι₁ × ι₂ → R) := (AddEquiv.ofBijective g ⟨hinj, hsurj⟩).symm
  have hge : ∀ x, g (e x) = x := fun x => (AddEquiv.ofBijective g ⟨hinj, hsurj⟩).apply_symm_apply x
  have heg : ∀ c, e (g c) = c := fun c => (AddEquiv.ofBijective g ⟨hinj, hsurj⟩).symm_apply_apply c
  have hsmul : ∀ (f : ι₂ → R) c, Θ f • g c = g (fun κ => f κ.2 * c κ) := by
    intro f c
    rw [hg, hg, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul, ← map_mul]
    rfl
  refine hstr_coord I I₀ e (fun k x => ⟨fun hx => ?_, fun hc => ?_⟩)
  · refine Submodule.smul_induction_on (p := fun y => ∀ κ, e y κ ∈ I₀ ^ k) hx ?_ ?_
    · intro a ha y _ κ
      obtain ⟨f, hf, rfl⟩ := (hI k a).1 ha
      rw [← hge y, hsmul, heg]
      exact Ideal.mul_mem_right _ _ (hf κ.2)
    · intro y z hy hz κ
      rw [map_add]
      exact Ideal.add_mem _ (hy κ) (hz κ)
  · rw [← hge x, hg]
    refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem_smul ?_ trivial)
    exact (hI k _).2 ⟨_, fun i => hc (j, i), rfl⟩

end HStrAbs

section HStrA0

variable {O : Type} [CommRing O]

/- English proof (translation)
Establish `hpoly : ∀ P : Polynomial O, F (P : PowerSeries O) = G (P : PowerSeries O)`. Introduce `P`. Establish `h : F.comp (Polynomial.coeToPowerSeries.algHom O) = G.comp (Polynomial.coeToPowerSeries.algHom O)`. Apply `Polynomial.algHom_ext` to reduce the goal to its premises. Simplify using `[Polynomial.coeToPowerSeries.algHom_apply, hX]`.

Establish `h2` using `DFunLike.congr_fun h P`. Simplify `h2` using `[Polynomial.coeToPowerSeries.algHom_apply]`. Apply `AlgHom.ext` to reduce the goal to its premises. Introduce `f`. Rewrite using `[← sub_eq_zero]`.

Use extensionality with `k`. Establish `hdiv : (PowerSeries.X : PowerSeries O) ^ (k + 1) ∣ F f - G f`. Establish `hf` using `PowerSeries.eq_shift_mul_X_pow_add_trunc (k + 1) f`. Use `set g : PowerSeries O := PowerSeries.mk fun i => PowerSeries.coeff (i + (k + 1)) f with hg`. Establish `e1 : F f = F g * (F PowerSeries.X) ^ (k + 1) + F ((f.trunc (k + 1) : Polynomial O) : PowerSeries O)` using `by conv_lhs => rw [hf]`.

Rewrite using `[map_add, map_mul, map_pow]`. Establish `e2 : G f = G g * (G PowerSeries.X) ^ (k + 1) + G ((f.trunc (k + 1) : Polynomial O) : PowerSeries O)` using `by conv_lhs => rw [hf]`. Rewrite using `[map_add, map_mul, map_pow]`. Establish `e3 : F f - G f = (F g - G g) * (F PowerSeries.X) ^ (k + 1)`. Rewrite using `[e1, e2, hpoly, ← hX]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e3]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hd _) _`. Rewrite using `[map_zero]`. Conclude with `(PowerSeries.X_pow_dvd_iff.1 hdiv) k (Nat.lt_succ_self k)`.
-/
theorem hstra_algHom_ext (F G : PowerSeries O →ₐ[O] PowerSeries O)
    (hX : F PowerSeries.X = G PowerSeries.X) (hd : PowerSeries.X ∣ F PowerSeries.X) : F = G := by
  have hpoly : ∀ P : Polynomial O, F (P : PowerSeries O) = G (P : PowerSeries O) := by
    intro P
    have h : F.comp (Polynomial.coeToPowerSeries.algHom O) =
        G.comp (Polynomial.coeToPowerSeries.algHom O) := by
      apply Polynomial.algHom_ext
      simp [Polynomial.coeToPowerSeries.algHom_apply, hX]
    have h2 := DFunLike.congr_fun h P
    simpa [Polynomial.coeToPowerSeries.algHom_apply] using h2
  apply AlgHom.ext
  intro f
  rw [← sub_eq_zero]
  ext k
  have hdiv : (PowerSeries.X : PowerSeries O) ^ (k + 1) ∣ F f - G f := by
    have hf := PowerSeries.eq_shift_mul_X_pow_add_trunc (k + 1) f
    set g : PowerSeries O := PowerSeries.mk fun i => PowerSeries.coeff (i + (k + 1)) f with hg
    have e1 : F f = F g * (F PowerSeries.X) ^ (k + 1) +
        F ((f.trunc (k + 1) : Polynomial O) : PowerSeries O) := by
      conv_lhs => rw [hf]
      rw [map_add, map_mul, map_pow]
    have e2 : G f = G g * (G PowerSeries.X) ^ (k + 1) +
        G ((f.trunc (k + 1) : Polynomial O) : PowerSeries O) := by
      conv_lhs => rw [hf]
      rw [map_add, map_mul, map_pow]
    have e3 : F f - G f = (F g - G g) * (F PowerSeries.X) ^ (k + 1) := by
      rw [e1, e2, hpoly, ← hX]
      ring
    rw [e3]
    exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hd _) _
  rw [map_zero]
  exact (PowerSeries.X_pow_dvd_iff.1 hdiv) k (Nat.lt_succ_self k)

end HStrA0

section HStrA1

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

/- English proof (translation)
Take `⟨w, hw⟩` from `h9.2.2.1`. Establish `h0` using `congrFun hw (0 : ZMod n)`. Establish `hk : PD.p - 1 ≠ 0` using `by have := PD.hp.two_le; omega`. Establish `h1 : W.π₀₁ = (w : LetA O n) 0 * PowerSeries.X ^ (PD.p - 1)` using `h0`. Rewrite using `[h1, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hk, mul_zero]`.
-/
theorem hstra_cc (W : LocWach PD LL O v n) (h9 : P9π₀ W) :
    PowerSeries.constantCoeff W.π₀₁ = 0 := by
  obtain ⟨w, hw⟩ := h9.2.2.1
  have h0 := congrFun hw (0 : ZMod n)
  have hk : PD.p - 1 ≠ 0 := by have := PD.hp.two_le; omega
  have h1 : W.π₀₁ = (w : LetA O n) 0 * PowerSeries.X ^ (PD.p - 1) := h0
  rw [h1, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hk, mul_zero]

/- English proof (translation)
The claim follows from `PowerSeries.HasSubst.of_constantCoeff_zero' (hstra_cc W h9)`.
-/
theorem hstra_hasSubst (W : LocWach PD LL O v n) (h9 : P9π₀ W) : PowerSeries.HasSubst W.π₀₁ :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (hstra_cc W h9)

def hstraS (W : LocWach PD LL O v n) (h9 : P9π₀ W) : PowerSeries O →ₐ[O] PowerSeries O :=
  PowerSeries.substAlgHom (hstra_hasSubst W h9)

/- English proof (translation)
Unfold `hstraS`. Rewrite using `[PowerSeries.coe_substAlgHom]`.
-/
theorem hstraS_apply (W : LocWach PD LL O v n) (h9 : P9π₀ W) (f : PowerSeries O) :
    hstraS W h9 f = PowerSeries.subst W.π₀₁ f := by
  unfold hstraS
  rw [PowerSeries.coe_substAlgHom]

/- English proof (translation)
The claim follows from `PowerSeries.substAlgHom_X (hstra_hasSubst W h9)`.
-/
theorem hstraS_X (W : LocWach PD LL O v n) (h9 : P9π₀ W) : hstraS W h9 PowerSeries.X = W.π₀₁ :=
  PowerSeries.substAlgHom_X (hstra_hasSubst W h9)

/- English proof (translation)
Establish `hπ : W.γ₀ δ W.π₀₁ = W.π₀₁` using `congrFun (h9.1 δ hδ) (0 : ZMod n)`. Establish `h` using `hstra_algHom_ext ((W.γ₀ δ).comp (hstraS W h9)) (hstraS W h9) (by rw [AlgHom.comp_apply, hstraS_X, hπ]) (by rw [AlgHom.comp_apply, hstraS_X, hπ]; exact PowerSeries.X_dvd_iff.2 (hstra_cc W h9))`. Conclude with `DFunLike.congr_fun h f`.
-/
theorem hstraS_inv (W : LocWach PD LL O v n) (h9 : P9π₀ W) (δ : W.Gam) (hδ : δ ∈ W.DelF)
    (f : PowerSeries O) : W.γ₀ δ (hstraS W h9 f) = hstraS W h9 f := by
  have hπ : W.γ₀ δ W.π₀₁ = W.π₀₁ := congrFun (h9.1 δ hδ) (0 : ZMod n)
  have h := hstra_algHom_ext ((W.γ₀ δ).comp (hstraS W h9)) (hstraS W h9)
    (by rw [AlgHom.comp_apply, hstraS_X, hπ])
    (by rw [AlgHom.comp_apply, hstraS_X, hπ]; exact PowerSeries.X_dvd_iff.2 (hstra_cc W h9))
  exact DFunLike.congr_fun h f

def hstraΘ (W : LocWach PD LL O v n) (h9 : P9π₀ W) : LetA O n →ₐ[O] ↥W.AΔ :=
  (letγ (hstraS W h9)).codRestrict W.AΔ (fun a δ hδ => by
    funext i
    exact hstraS_inv W h9 δ hδ (a i))

/- English proof (translation)
The claim follows from `hstraS_apply W h9 (a i)`.
-/
theorem hstraΘ_apply (W : LocWach PD LL O v n) (h9 : P9π₀ W) (a : LetA O n) (i : ZMod n) :
    ((hstraΘ W h9 a : ↥W.AΔ) : LetA O n) i = PowerSeries.subst (W.π₀ i) (a i) :=
  hstraS_apply W h9 (a i)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b hab`. Take `⟨f, _, hf⟩` from `h9.2.1 (hstraΘ W h9 a : ↥W.AΔ) (hstraΘ W h9 a).2`. Rewrite using `[hf a (fun i => hstraΘ_apply W h9 a i), hf b (fun i => by rw [hab]; exact hstraΘ_apply W h9 b i)]`. Introduce `a`.

Take `⟨f, hf, _⟩` from `h9.2.1 a a.2`. Use `⟨f, Subtype.ext ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[hstraΘ_apply, hf i]`.
-/
theorem hstraΘ_bij (W : LocWach PD LL O v n) (h9 : P9π₀ W) : Function.Bijective (hstraΘ W h9) := by
  constructor
  · intro a b hab
    obtain ⟨f, _, hf⟩ := h9.2.1 (hstraΘ W h9 a : ↥W.AΔ) (hstraΘ W h9 a).2
    rw [hf a (fun i => hstraΘ_apply W h9 a i), hf b (fun i => by rw [hab]; exact hstraΘ_apply W h9 b i)]
  · intro a
    obtain ⟨f, hf, _⟩ := h9.2.1 a a.2
    refine ⟨f, Subtype.ext ?_⟩
    funext i
    rw [hstraΘ_apply, hf i]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Conclude with `hstraS_X W h9`.
-/
theorem hstraΘ_π (W : LocWach PD LL O v n) (h9 : P9π₀ W) :
    hstraΘ W h9 letπ = ⟨W.π₀, h9.1⟩ := by
  apply Subtype.ext
  funext i
  exact hstraS_X W h9

end HStrA1

section HStrA2

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def hstraIA (O : Type) [CommRing O] (n p : ℕ) : Ideal (LetA O n) :=
  Ideal.span {((p : ℕ) : LetA O n), letπ}

def maximalIdealPowerSeries (O : Type) [CommRing O] (p : ℕ) : Ideal (PowerSeries O) :=
  Ideal.span {PowerSeries.C ((p : ℕ) : O), PowerSeries.X}

def hstraI (W : LocWach PD LL O v n) (h9 : P9π₀ W) : Ideal ↥W.AΔ :=
  Ideal.span {((PD.p : ℕ) : ↥W.AΔ), ⟨W.π₀, h9.1⟩}

/- English proof (translation)
Unfold `hstraIA hstraI`. Rewrite using `[Ideal.map_span, Set.image_pair, map_natCast, hstraΘ_π]`.
-/
theorem hstra_map_IA (W : LocWach PD LL O v n) (h9 : P9π₀ W) :
    Ideal.map (hstraΘ W h9) (hstraIA O n PD.p) = hstraI W h9 := by
  unfold hstraIA hstraI
  rw [Ideal.map_span, Set.image_pair, map_natCast, hstraΘ_π]

/- English proof (translation)
Rewrite using `[← hstra_map_IA, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_iff_of_surjective _ (hstraΘ_bij W h9).2`.
-/
theorem hstra_mem_I_pow (W : LocWach PD LL O v n) (h9 : P9π₀ W) (k : ℕ) (a : ↥W.AΔ) :
    a ∈ hstraI W h9 ^ k ↔ ∃ f ∈ hstraIA O n PD.p ^ k, hstraΘ W h9 f = a := by
  rw [← hstra_map_IA, ← Ideal.map_pow]
  exact Ideal.mem_map_iff_of_surjective _ (hstraΘ_bij W h9).2

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hf i`. Establish `h1 : Ideal.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i) (hstraIA O n p) ≤ maximalIdealPowerSeries O p`. Unfold `hstraIA maximalIdealPowerSeries`. Rewrite using `[Ideal.map_span, Set.image_pair, map_natCast]`.

Apply `Ideal.span_mono` to reduce the goal to its premises. Establish `: ((p : ℕ) : PowerSeries O) = PowerSeries.C ((p : ℕ) : O)` using `by rw [map_natCast]`. Rewrite using `[this]`. Both sides reduce to the same expression. Establish `h2` using `Ideal.mem_map_of_mem (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i) hf`.

Rewrite `h2` using `[Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono h1 k h2`. Introduce `hf`. Establish `h1 : Ideal.map (Pi.constRingHom (ZMod n) (PowerSeries O)) (maximalIdealPowerSeries O p) ≤ hstraIA O n p`. Unfold `hstraIA maximalIdealPowerSeries`.

Rewrite using `[Ideal.map_span, Set.image_pair]`. Apply `Ideal.span_mono` to reduce the goal to its premises. Establish `: Pi.constRingHom (ZMod n) (PowerSeries O) (PowerSeries.C ((p : ℕ) : O)) = ((p : ℕ) : LetA O n)`. Rewrite using `[map_natCast, map_natCast]`. Rewrite using `[this]`.

Both sides reduce to the same expression. Establish `h2 : ∀ i, Pi.constRingHom (ZMod n) (PowerSeries O) (f i) ∈ hstraIA O n p ^ k`. Introduce `i`. Establish `h3` using `Ideal.mem_map_of_mem (Pi.constRingHom (ZMod n) (PowerSeries O)) (hf i)`. Rewrite `h3` using `[Ideal.map_pow]`.

Conclude with `Ideal.pow_right_mono h1 k h3`. Establish `h4 : f = ∑ i : ZMod n, (letE i : LetA O n) * Pi.constRingHom (ZMod n) (PowerSeries O) (f i)`. Use function extensionality and compare the values at `j`. Rewrite using `[Finset.sum_apply]`. Simplify using `[letE, Pi.single_apply]`.

Rewrite using `[h4]`. Conclude with `Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (h2 i))`.
-/
theorem hstra_mem_IA_pow [NeZero n] (p k : ℕ) (f : LetA O n) :
    f ∈ hstraIA O n p ^ k ↔ ∀ i, f i ∈ maximalIdealPowerSeries O p ^ k := by
  constructor
  · intro hf i
    have h1 : Ideal.map (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i) (hstraIA O n p) ≤
        maximalIdealPowerSeries O p := by
      unfold hstraIA maximalIdealPowerSeries
      rw [Ideal.map_span, Set.image_pair, map_natCast]
      apply Ideal.span_mono
      have : ((p : ℕ) : PowerSeries O) = PowerSeries.C ((p : ℕ) : O) := by rw [map_natCast]
      rw [this]
      rfl
    have h2 := Ideal.mem_map_of_mem (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i) hf
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 k h2
  · intro hf
    have h1 : Ideal.map (Pi.constRingHom (ZMod n) (PowerSeries O)) (maximalIdealPowerSeries O p) ≤
        hstraIA O n p := by
      unfold hstraIA maximalIdealPowerSeries
      rw [Ideal.map_span, Set.image_pair]
      apply Ideal.span_mono
      have : Pi.constRingHom (ZMod n) (PowerSeries O) (PowerSeries.C ((p : ℕ) : O)) =
          ((p : ℕ) : LetA O n) := by
        rw [map_natCast, map_natCast]
      rw [this]
      rfl
    have h2 : ∀ i, Pi.constRingHom (ZMod n) (PowerSeries O) (f i) ∈ hstraIA O n p ^ k := by
      intro i
      have h3 := Ideal.mem_map_of_mem (Pi.constRingHom (ZMod n) (PowerSeries O)) (hf i)
      rw [Ideal.map_pow] at h3
      exact Ideal.pow_right_mono h1 k h3
    have h4 : f = ∑ i : ZMod n, (letE i : LetA O n) * Pi.constRingHom (ZMod n) (PowerSeries O) (f i) := by
      funext j
      rw [Finset.sum_apply]
      simp [letE, Pi.single_apply]
    rw [h4]
    exact Ideal.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (h2 i))

/- English proof (translation)
Use `liftb_neZero W` as an intermediate fact. Take `⟨⟨r, b, hb, huniq, hΔ⟩, -⟩` from `hm`. Use `⟨hstraI W h9, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Establish `e : (⟨qp W, h⟩ : ↥W.AΔ) = ⟨W.π₀, h9.1⟩ + ((PD.p : ℕ) : ↥W.AΔ)`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[qp]`. Rewrite using `[e]`. Conclude with `Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))`. Establish `hle : hstraI W h9 ≤ Ideal.comap (lifta_φ₀ W) (hstraI W h9)` using `by conv_lhs => unfold hstraI`.

Rewrite using `[Ideal.span_le]`. Introduce and unpack `x (rfl | rfl)`. Use `show lifta_φ₀ W ((PD.p : ℕ) : ↥W.AΔ) ∈ hstraI W h9`. Rewrite using `[map_natCast]`. Conclude with `Ideal.subset_span (by simp)`.

Use `show lifta_φ₀ W ⟨W.π₀, h9.1⟩ ∈ hstraI W h9`. Take `⟨t, ht, hφ⟩` from `(lifta_ring_of W h9).φπ`. Establish `hq : qp W ∈ W.AΔ` using `W.AΔ.add_mem h9.1 (natCast_mem _ _)`. Establish `e : lifta_φ₀ W ⟨W.π₀, h9.1⟩ = (⟨qp W, hq⟩ ^ (PD.p - 1) * ⟨t, ht⟩ : ↥W.AΔ) * ⟨W.π₀, h9.1⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `Eq.trans hφ ?_` and prove the remaining obligations. Simplify using `only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`.

Conclude with `fun a ha => hle ha`. Use `hstra_abs (lifta_N W T) (hstraΘ W h9 : LetA O n →+* ↥W.AΔ) (hstraΘ_bij W h9) (hstraI W h9) (maximalIdealPowerSeries O PD.p) (fun k a => ?_) b hb (fun a ha => ?_) (fun x hx => ?_)` and prove the remaining obligations. Rewrite using `[hstra_mem_I_pow]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`.

Conclude with `⟨f, (hstra_mem_IA_pow PD.p k f).1 hf, rfl⟩`. Introduce and unpack `⟨f, hf, rfl⟩`. Conclude with `⟨f, (hstra_mem_IA_pow PD.p k f).2 hf, rfl⟩`. Establish `h0 : (0 : W.DD T) = ∑ j, ((a j : ↥W.AΔ) : LetA O n) • b j` using `ha.symm`. Establish `h00 : (0 : W.DD T) = ∑ j, ((fun _ => 0 : Fin r → LetA O n) j) • b j` using `by simp`.

Establish `h1` using `(huniq 0 (W.N T).zero_mem).unique h0 h00`. Use function extensionality and compare the values at `j`. Conclude with `Subtype.ext (congrFun h1 j)`. Take `⟨a, ha, hxa⟩` from `hΔ x hx`. Conclude with `⟨fun j => ⟨a j, ha j⟩, hxa⟩`.
-/
theorem hstra_complete (W : LocWach PD LL O v n)
    [IsAdicComplete (maximalIdealPowerSeries O PD.p) (PowerSeries O)] (h9 : P9π₀ W) (T : LocLat G Qp LL O)
    (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) : lifta_Complete W T := by
  have := liftb_neZero W
  obtain ⟨⟨r, b, hb, huniq, hΔ⟩, -⟩ := hm
  refine ⟨hstraI W h9, ?_, ?_, ?_⟩
  · intro h
    have e : (⟨qp W, h⟩ : ↥W.AΔ) = ⟨W.π₀, h9.1⟩ + ((PD.p : ℕ) : ↥W.AΔ) := by
      apply Subtype.ext
      simp [qp]
    rw [e]
    exact Ideal.add_mem _ (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp))
  · have hle : hstraI W h9 ≤ Ideal.comap (lifta_φ₀ W) (hstraI W h9) := by
      conv_lhs => unfold hstraI
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · show lifta_φ₀ W ((PD.p : ℕ) : ↥W.AΔ) ∈ hstraI W h9
        rw [map_natCast]
        exact Ideal.subset_span (by simp)
      · show lifta_φ₀ W ⟨W.π₀, h9.1⟩ ∈ hstraI W h9
        obtain ⟨t, ht, hφ⟩ := (lifta_ring_of W h9).φπ
        have hq : qp W ∈ W.AΔ := W.AΔ.add_mem h9.1 (natCast_mem _ _)
        have e : lifta_φ₀ W ⟨W.π₀, h9.1⟩ =
            (⟨qp W, hq⟩ ^ (PD.p - 1) * ⟨t, ht⟩ : ↥W.AΔ) * ⟨W.π₀, h9.1⟩ := by
          apply Subtype.ext
          refine Eq.trans hφ ?_
          simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
          ring
        rw [e]
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    exact fun a ha => hle ha
  · refine hstra_abs (lifta_N W T) (hstraΘ W h9 : LetA O n →+* ↥W.AΔ) (hstraΘ_bij W h9) (hstraI W h9)
      (maximalIdealPowerSeries O PD.p) (fun k a => ?_) b hb (fun a ha => ?_) (fun x hx => ?_)
    · rw [hstra_mem_I_pow]
      constructor
      · rintro ⟨f, hf, rfl⟩
        exact ⟨f, (hstra_mem_IA_pow PD.p k f).1 hf, rfl⟩
      · rintro ⟨f, hf, rfl⟩
        exact ⟨f, (hstra_mem_IA_pow PD.p k f).2 hf, rfl⟩
    · have h0 : (0 : W.DD T) = ∑ j, ((a j : ↥W.AΔ) : LetA O n) • b j := ha.symm
      have h00 : (0 : W.DD T) = ∑ j, ((fun _ => 0 : Fin r → LetA O n) j) • b j := by simp
      have h1 := (huniq 0 (W.N T).zero_mem).unique h0 h00
      funext j
      exact Subtype.ext (congrFun h1 j)
    · obtain ⟨a, ha, hxa⟩ := hΔ x hx
      exact ⟨fun j => ⟨a j, ha j⟩, hxa⟩

end HStrA2

/- English proof (translation)
Establish `hO : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL)`. Rewrite using `[(D.loc l).PD_p K]`. Conclude with `phib_OL_complete LL`. Establish `hR : IsAdicComplete (maximalIdealPowerSeries ↥(OL LL) ((D.loc l).PD K).p) (PowerSeries ↥(OL LL))` using `hstr_ps_complete _`. Take `⟨h9, hm⟩` from `uniformizer_ring_and_module_clauses _ (a9 l K s LL h) hA T hT`.

Conclude with `hstra_complete _ h9 T hm`.
-/
theorem hstr_CompleteA_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a9 : adm9 D HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (hA : CaseA ((HW l).W K s LL h))
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ) :
    lifta_Complete ((HW l).W K s LL h) T := by
  have hO : IsAdicComplete (Ideal.span {((((D.loc l).PD K).p : ℕ) : ↥(OL LL))}) ↥(OL LL) := by
    rw [(D.loc l).PD_p K]
    exact phib_OL_complete LL
  have hR : IsAdicComplete (maximalIdealPowerSeries ↥(OL LL) ((D.loc l).PD K).p) (PowerSeries ↥(OL LL)) :=
    hstr_ps_complete _
  obtain ⟨h9, hm⟩ := uniformizer_ring_and_module_clauses _ (a9 l K s LL h) hA T hT
  exact hstra_complete _ h9 T hm

/- English proof (translation)
Introduce `l _ K s LL h hA T hT` and use `hstr_CompleteA_D D HW F a9 l K s LL h hA T hT`.
-/
theorem hstr_A (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a9 : adm9 D HW F) : liftAOpen D HW F :=
  fun l _ K s LL h hA T hT => hstr_CompleteA_D D HW F a9 l K s LL h hA T hT

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.CrystallineLiftingBounds

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

/- English proof (translation)
Assemble the required witnesses or components as `⟨Formalism.MainNotions.LiftingTheory.wach_first_claim_of_lemma D HW F h16, Formalism.MainNotions.LiftingTheory.wach_statement_case_B D HW F h2 h16, Formalism.MainNotions.LiftingTheory.wach_statement_case_A D HW F h9 h16⟩`.
-/
theorem baseChange_preserves_unitary_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h2 : adm2 D HW F) (h9 : adm9 D HW F) (h16 : adm16 D HW F) : Conclusion1 D HW F :=
  ⟨Formalism.MainNotions.LiftingTheory.wach_first_claim_of_lemma D HW F h16, Formalism.MainNotions.LiftingTheory.wach_statement_case_B D HW F h2 h16, Formalism.MainNotions.LiftingTheory.wach_statement_case_A D HW F h9 h16⟩

/- English proof (translation)
Take `⟨-, h2, -, -, -, -, -, -, h9, -, -, -, -, -, -, h16, -⟩` from `h`. Conclude with `baseChange_preserves_unitary_of D HW F h2 h9 h16`.
-/
theorem wach_lemma_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) : Conclusion1 D HW F := by
  obtain ⟨-, h2, -, -, -, -, -, -, h9, -, -, -, -, -, -, h16, -⟩ := h
  exact baseChange_preserves_unitary_of D HW F h2 h9 h16

end Formalism.MainNotions.CrystallineLiftingBounds

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LqbAbs

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Formalism.CoboundaryTransfers.Base O A} {M : ℕ}
  {D₀ D₁ : Type} [AddCommGroup D₀] [Module A D₀] [Module O D₀] [IsScalarTower O A D₀]
  [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
  {W₀ : Formalism.CoboundaryTransfers.WachMod B M D₀} {W₁ : Formalism.CoboundaryTransfers.WachMod B M D₁}

def lqb_semi (f : D₁ →ₗ[O] D₁) (σ : A →ₐ[O] A) (h : ∀ (a : A) (x : D₁), f (a • x) = σ a • f x) :
    D₁ →ₛₗ[(σ : A →+* A)] D₁ where
  toFun := f
  map_add' := f.map_add
  map_smul' := h

def lqb_desc (P : Submodule A D₁) (f : D₁ →ₗ[O] D₁) (σ : A →ₐ[O] A)
    (h : ∀ (a : A) (x : D₁), f (a • x) = σ a • f x) (hP : ∀ x ∈ P, f x ∈ P) :
    (D₁ ⧸ P) →ₗ[O] (D₁ ⧸ P) where
  toFun := P.mapQ P (lqb_semi f σ h) (fun x hx => hP x hx)
  map_add' := map_add _
  map_smul' := fun c x => by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      change (Submodule.Quotient.mk (f (c • x)) : D₁ ⧸ P) = c • Submodule.Quotient.mk (f x)
      rw [f.map_smul]
      rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lqb_desc_mk (P : Submodule A D₁) (f : D₁ →ₗ[O] D₁) (σ : A →ₐ[O] A)
    (h : ∀ (a : A) (x : D₁), f (a • x) = σ a • f x) (hP : ∀ x ∈ P, f x ∈ P) (x : D₁) :
    lqb_desc P f σ h hP (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x) := rfl

abbrev lqbD (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) : Type := D₁ ⧸ LinearMap.range ι.f

/- English proof (translation)
Rewrite using `[Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]`.
-/
theorem lqb_mk_eq_zero (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (x : D₁) :
    (Submodule.Quotient.mk x : lqbD ι) = 0 ↔ ∃ d, ι.f d = x := by
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro x; exact ⟨x, by simp⟩`. Consider the case `succ k ih`. Introduce `x`. Take `⟨y, hy⟩` from `W.Q_bij.2 x`.

Take `⟨z, hz⟩` from `ih y`. Use `⟨z, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `B.Q ^ (k + 1) • z = x`. Rewrite using `[pow_succ', mul_smul]`. Establish `hz' : B.Q ^ k • z = y` using `hz`.

Rewrite using `[hz']`. Conclude with `hy`.
-/
theorem lqb_Qpow_surj (W : Formalism.CoboundaryTransfers.WachMod B M D₀) (k : ℕ) :
    Function.Surjective (fun x : D₀ => B.Q ^ k • x) := by
  induction k with
  | zero => intro x; exact ⟨x, by simp⟩
  | succ k ih =>
    intro x
    obtain ⟨y, hy⟩ := W.Q_bij.2 x
    obtain ⟨z, hz⟩ := ih y
    refine ⟨z, ?_⟩
    change B.Q ^ (k + 1) • z = x
    rw [pow_succ', mul_smul]
    have hz' : B.Q ^ k • z = y := hz
    rw [hz']
    exact hy

def lqbW (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : Function.Surjective (fun x : D₀ => B.X • x)) :
    Formalism.CoboundaryTransfers.WachMod B M (lqbD ι) where
  N := W₁.N.map (LinearMap.range ι.f).mkQ
  φ := lqb_desc _ W₁.φ B.φ W₁.φ_smul (by rintro _ ⟨d, rfl⟩; exact ⟨W₀.φ d, ι.φ_comm d⟩)
  γ := lqb_desc _ W₁.γ B.γ W₁.γ_smul (by rintro _ ⟨d, rfl⟩; exact ⟨W₀.γ d, ι.γ_comm d⟩)
  φ_smul := fun a x => by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, lqb_desc_mk, lqb_desc_mk, W₁.φ_smul]
      rfl
  γ_smul := fun a x => by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, lqb_desc_mk, lqb_desc_mk, W₁.γ_smul]
      rfl
  comm := fun x => by
    induction x using Submodule.Quotient.induction_on with
    | H x => rw [lqb_desc_mk, lqb_desc_mk, lqb_desc_mk, lqb_desc_mk, W₁.comm]
  X_inj := fun x => by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      intro h
      rw [← Submodule.Quotient.mk_smul, lqb_mk_eq_zero] at h
      obtain ⟨d, hd⟩ := h
      obtain ⟨d', hd'⟩ := hX d
      have hd'' : B.X • d' = d := hd'
      rw [lqb_mk_eq_zero]
      refine ⟨d', ?_⟩
      have : B.X • (x - ι.f d') = 0 := by rw [smul_sub, ← map_smul, hd'', hd, sub_self]
      exact (sub_eq_zero.1 (W₁.X_inj _ this)).symm
  Q_bij := by
    constructor
    · intro x y hxy
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        induction y using Submodule.Quotient.induction_on with
        | H y =>
          have h : (Submodule.Quotient.mk (B.Q • (x - y)) : lqbD ι) = 0 := by
            have hxy' : B.Q • (Submodule.Quotient.mk x : lqbD ι) = B.Q • Submodule.Quotient.mk y := hxy
            rw [smul_sub, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
              Submodule.Quotient.mk_smul, hxy', sub_self]
          rw [lqb_mk_eq_zero] at h
          obtain ⟨d, hd⟩ := h
          obtain ⟨d', hd'⟩ := W₀.Q_bij.2 d
          have hd'' : B.Q • d' = d := hd'
          have h2 : B.Q • (x - y) = B.Q • ι.f d' := by rw [← map_smul, hd'', hd]
          have h3 : x - y = ι.f d' := W₁.Q_bij.1 h2
          have h4 : (Submodule.Quotient.mk (x - y) : lqbD ι) = 0 := (lqb_mk_eq_zero ι _).2 ⟨d', h3.symm⟩
          rw [Submodule.Quotient.mk_sub] at h4
          exact sub_eq_zero.1 h4
    · intro x
      induction x using Submodule.Quotient.induction_on with
      | H x =>
        obtain ⟨y, hy⟩ := W₁.Q_bij.2 x
        have hy' : B.Q • y = x := hy
        exact ⟨Submodule.Quotient.mk y, by
          change B.Q • (Submodule.Quotient.mk y : lqbD ι) = _
          rw [← Submodule.Quotient.mk_smul, hy']⟩
  φ_N := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨B.Q ^ M • W₁.φ x, W₁.φ_N x hx, rfl⟩
  γ_N := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨x', hx', h⟩ := W₁.γ_N x hx
    refine ⟨Submodule.Quotient.mk x', ⟨x', hx', rfl⟩, ?_⟩
    change (Submodule.Quotient.mk (W₁.γ x) : lqbD ι) - Submodule.Quotient.mk x = _
    rw [← Submodule.Quotient.mk_sub, h]
    rfl
  γ_QN := fun y => by
    induction y using Submodule.Quotient.induction_on with
    | H y =>
      rintro ⟨n₁, hn₁, hn⟩
      have h0 : (Submodule.Quotient.mk (B.Q ^ M • y - n₁) : lqbD ι) = 0 := by
        rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
        exact sub_eq_zero.2 hn.symm
      obtain ⟨d, hd⟩ := (lqb_mk_eq_zero ι _).1 h0
      obtain ⟨d', hd'⟩ := lqb_Qpow_surj W₀ M d
      have hd'' : B.Q ^ M • d' = d := hd'
      have hy1 : B.Q ^ M • (y - ι.f d') = n₁ := by
        rw [smul_sub, ← map_smul, hd'', hd]; abel
      obtain ⟨y', hy', h⟩ := W₁.γ_QN (y - ι.f d') (by rw [hy1]; exact hn₁)
      refine ⟨Submodule.Quotient.mk y', ⟨B.Q ^ M • y', hy', rfl⟩, ?_⟩
      have hmk : (Submodule.Quotient.mk (y - ι.f d') : lqbD ι) = Submodule.Quotient.mk y := by
        rw [Submodule.Quotient.mk_sub, (lqb_mk_eq_zero ι _).2 ⟨d', rfl⟩, sub_zero]
      rw [← hmk]
      change (Submodule.Quotient.mk (W₁.γ (y - ι.f d')) : lqbD ι) - Submodule.Quotient.mk _ = _
      rw [← Submodule.Quotient.mk_sub, h]
      rfl

def lqbπ (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : Function.Surjective (fun x : D₀ => B.X • x)) :
    Formalism.CoboundaryTransfers.Hom W₁ (lqbW ι hX) where
  f := (LinearMap.range ι.f).mkQ
  φ_comm := fun _ => rfl
  γ_comm := fun _ => rfl
  N_le := fun x hx => ⟨x, hx, rfl⟩

def lqbS (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : Function.Surjective (fun x : D₀ => B.X • x))
    (hinj : Function.Injective ι.f) (hsat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N) :
    Formalism.CoboundaryTransfers.SES W₀ W₁ (lqbW ι hX) where
  ι := ι
  π := lqbπ ι hX
  ι_inj := hinj
  exact := fun x => lqb_mk_eq_zero ι x
  sat := hsat

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `⟨x, hx, by rw [pow_zero, one_smul]; rfl⟩`.
-/
theorem lqb_coker (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : Function.Surjective (fun x : D₀ => B.X • x))
    (hinj : Function.Injective ι.f) (hsat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N) :
    Formalism.CoboundaryTransfers.CokerKilled (lqbS ι hX hinj hsat) 0 := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, hx, by rw [pow_zero, one_smul]; rfl⟩

/- English proof (translation)
Take `⟨hy, m, hm, hz⟩` from `h`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `H y`. Take `⟨n₁, hn₁, hn⟩` from `hy`. Take `⟨m₁, hm₁, rfl⟩` from `hm`.

Establish `h0 : (Submodule.Quotient.mk (B.Q ^ M • y - n₁) : lqbD ι) = 0`. Rewrite using `[Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]`. Conclude with `sub_eq_zero.2 hn.symm`. Take `⟨d, hd⟩` from `(lqb_mk_eq_zero ι _).1 h0`. Take `⟨d', hd'⟩` from `lqb_Qpow_surj W₀ M d`.

Establish `hd'' : B.Q ^ M • d' = d` using `hd'`. Establish `hy1 : B.Q ^ M • (y - ι.f d') = n₁`. Rewrite using `[smul_sub, ← map_smul, hd'', hd]`. Normalize the expressions using the abelian group laws. Use `⟨y - ι.f d', B.X • m₁, ⟨?_, m₁, hm₁, rfl⟩, ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `B.Q ^ M • (y - ι.f d') ∈ W₁.N`. Rewrite using `[hy1]`. Conclude with `hn₁`. Rewrite using `[Submodule.Quotient.mk_sub, (lqb_mk_eq_zero ι _).2 ⟨d', rfl⟩, sub_zero]`. Rewrite using `[hz]`.

Both sides reduce to the same expression.
-/
theorem cocycle_lifts_to_cover (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : Function.Surjective (fun x : D₀ => B.X • x))
    (y z : lqbD ι) (h : (lqbW ι hX).C1 y z) :
    ∃ y₁ z₁, W₁.C1 y₁ z₁ ∧ (Submodule.Quotient.mk y₁ : lqbD ι) = y ∧
      (Submodule.Quotient.mk z₁ : lqbD ι) = z := by
  obtain ⟨hy, m, hm, hz⟩ := h
  induction y using Submodule.Quotient.induction_on with
  | H y =>
    obtain ⟨n₁, hn₁, hn⟩ := hy
    obtain ⟨m₁, hm₁, rfl⟩ := hm
    have h0 : (Submodule.Quotient.mk (B.Q ^ M • y - n₁) : lqbD ι) = 0 := by
      rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      exact sub_eq_zero.2 hn.symm
    obtain ⟨d, hd⟩ := (lqb_mk_eq_zero ι _).1 h0
    obtain ⟨d', hd'⟩ := lqb_Qpow_surj W₀ M d
    have hd'' : B.Q ^ M • d' = d := hd'
    have hy1 : B.Q ^ M • (y - ι.f d') = n₁ := by
      rw [smul_sub, ← map_smul, hd'', hd]; abel
    refine ⟨y - ι.f d', B.X • m₁, ⟨?_, m₁, hm₁, rfl⟩, ?_, ?_⟩
    · change B.Q ^ M • (y - ι.f d') ∈ W₁.N
      rw [hy1]; exact hn₁
    · rw [Submodule.Quotient.mk_sub, (lqb_mk_eq_zero ι _).2 ⟨d', rfl⟩, sub_zero]
    · rw [hz]; rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quotient_differential_mk (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : Function.Surjective (fun x : D₀ => B.X • x))
    (y z : D₁) : (lqbW ι hX).d1 (Submodule.Quotient.mk y) (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (W₁.d1 y z) := rfl

/- English proof (translation)
Unfold `Formalism.CoboundaryTransfers.WachMod.d1`. Rewrite using `[map_sub, map_sub, map_sub, ι.γ_comm, ι.φ_comm]`.
-/
theorem hom_differential_comm (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (y z : D₀) : ι.f (W₀.d1 y z) = W₁.d1 (ι.f y) (ι.f z) := by
  unfold Formalism.CoboundaryTransfers.WachMod.d1
  rw [map_sub, map_sub, map_sub, ι.γ_comm, ι.φ_comm]

/- English proof (translation)
Unfold `Formalism.CoboundaryTransfers.WachMod.d1`. Rewrite using `[map_sub, map_sub, map_smul, map_smul, smul_sub, smul_sub, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem differential_linear_combination (W : Formalism.CoboundaryTransfers.WachMod B M D₁) (c : O) (y z y' z' : D₁) :
    W.d1 (c • y - y') (c • z - z') = c • W.d1 y z - W.d1 y' z' := by
  unfold Formalism.CoboundaryTransfers.WachMod.d1
  rw [map_sub, map_sub, map_smul, map_smul, smul_sub, smul_sub, smul_sub]
  abel

/- English proof (translation)
Introduce `y z hyz`. Take `⟨y₁, z₁, hC, rfl, rfl⟩` from `cocycle_lifts_to_cover ι hX y z hyz.1`. Establish `hd : (Submodule.Quotient.mk (W₁.d1 y₁ z₁) : lqbD ι) = 0` using `hyz.2`. Take `⟨k, y₀, z₀, hC₀, hk⟩` from `hrat y₁ z₁ hC ((lqb_mk_eq_zero ι _).1 hd)`. Take `⟨hy₁, m₁, hm₁, hz₁⟩` from `hC`.

Take `⟨hy₀, m₀, hm₀, hz₀⟩` from `hC₀`. Use `⟨k, ((B.p : O) ^ k) • y₁ - ι.f y₀, ((B.p : O) ^ k) • z₁ - ι.f z₀, ⟨⟨?_, ?_⟩, ?_⟩, 0, Submodule.zero_mem _, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `B.Q ^ M • (((B.p : O) ^ k) • y₁ - ι.f y₀) ∈ W₁.N`. Rewrite using `[smul_sub, smul_comm, ← map_smul]`. Conclude with `W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hy₁) (ι.N_le _ hy₀)`.

Use `⟨((B.p : O) ^ k) • m₁ - ι.f m₀, W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hm₁) (ι.N_le _ hm₀), ?_⟩` and prove the remaining obligations. Rewrite using `[smul_sub, ← map_smul, ← hz₀, smul_comm, ← hz₁]`. Rewrite using `[differential_linear_combination, ← hom_differential_comm, hk, sub_self]`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (((B.p : O) ^ k) • y₁ - ι.f y₀) : lqbD ι) = _`. Rewrite using `[Submodule.Quotient.mk_sub, (lqb_mk_eq_zero ι _).2 ⟨y₀, rfl⟩, sub_zero, map_zero, sub_zero, add_zero]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (((B.p : O) ^ k) • z₁ - ι.f z₀) : lqbD ι) = _`. Rewrite using `[Submodule.Quotient.mk_sub, (lqb_mk_eq_zero ι _).2 ⟨z₀, rfl⟩, sub_zero, map_zero, sub_zero, add_zero]`. Both sides reduce to the same expression.
-/
theorem lqb_ratSurj (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : Function.Surjective (fun x : D₀ => B.X • x))
    (hinj : Function.Injective ι.f) (hsat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N)
    (hrat : ∀ y₁ z₁, W₁.C1 y₁ z₁ → (∃ d, ι.f d = W₁.d1 y₁ z₁) →
      ∃ k : ℕ, ∃ y₀ z₀, W₀.C1 y₀ z₀ ∧ ι.f (W₀.d1 y₀ z₀) = ((B.p : O) ^ k) • W₁.d1 y₁ z₁) :
    Formalism.CoboundaryTransfers.RatSurj (lqbS ι hX hinj hsat) := by
  intro y z hyz
  obtain ⟨y₁, z₁, hC, rfl, rfl⟩ := cocycle_lifts_to_cover ι hX y z hyz.1
  have hd : (Submodule.Quotient.mk (W₁.d1 y₁ z₁) : lqbD ι) = 0 := hyz.2
  obtain ⟨k, y₀, z₀, hC₀, hk⟩ := hrat y₁ z₁ hC ((lqb_mk_eq_zero ι _).1 hd)
  obtain ⟨hy₁, m₁, hm₁, hz₁⟩ := hC
  obtain ⟨hy₀, m₀, hm₀, hz₀⟩ := hC₀
  refine ⟨k, ((B.p : O) ^ k) • y₁ - ι.f y₀, ((B.p : O) ^ k) • z₁ - ι.f z₀, ⟨⟨?_, ?_⟩, ?_⟩, 0,
    Submodule.zero_mem _, ?_, ?_⟩
  · change B.Q ^ M • (((B.p : O) ^ k) • y₁ - ι.f y₀) ∈ W₁.N
    rw [smul_sub, smul_comm, ← map_smul]
    exact W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hy₁) (ι.N_le _ hy₀)
  · refine ⟨((B.p : O) ^ k) • m₁ - ι.f m₀,
      W₁.N.sub_mem (W₁.N.smul_of_tower_mem _ hm₁) (ι.N_le _ hm₀), ?_⟩
    rw [smul_sub, ← map_smul, ← hz₀, smul_comm, ← hz₁]
  · rw [differential_linear_combination, ← hom_differential_comm, hk, sub_self]
  · change (Submodule.Quotient.mk (((B.p : O) ^ k) • y₁ - ι.f y₀) : lqbD ι) = _
    rw [Submodule.Quotient.mk_sub, (lqb_mk_eq_zero ι _).2 ⟨y₀, rfl⟩, sub_zero, map_zero, sub_zero,
      add_zero]
    rfl
  · change (Submodule.Quotient.mk (((B.p : O) ^ k) • z₁ - ι.f z₀) : lqbD ι) = _
    rw [Submodule.Quotient.mk_sub, (lqb_mk_eq_zero ι _).2 ⟨z₀, rfl⟩, sub_zero, map_zero, sub_zero,
      add_zero]
    rfl

/- English proof (translation)
Introduce `y₁ z₁ hC hd`. Take `⟨hy₁, m₁, hm₁, hz₁⟩` from `hC`. Establish `hcoc : (lqbW ι hX).Cocycle (Submodule.Quotient.mk y₁) (Submodule.Quotient.mk z₁)`. Use `⟨⟨⟨B.Q ^ M • y₁, hy₁, rfl⟩, Submodule.Quotient.mk m₁, ⟨m₁, hm₁, rfl⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hz₁]`.

Both sides reduce to the same expression. Rewrite using `[quotient_differential_mk]`. Conclude with `(lqb_mk_eq_zero ι _).2 hd`. Take `⟨y, z, hyz, e1, e2⟩` from `hL _ _ hcoc`. Use `⟨y, z, hyz, (lqb_mk_eq_zero ι _).1 ?_, (lqb_mk_eq_zero ι _).1 ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.Quotient.mk_sub]`. Conclude with `sub_eq_zero.2 e1`. Rewrite using `[Submodule.Quotient.mk_sub]`. Conclude with `sub_eq_zero.2 e2`.
-/
theorem lqb_lifts_abs (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : Function.Surjective (fun x : D₀ => B.X • x))
    (hinj : Function.Injective ι.f) (hsat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N) (c : O)
    (hL : Formalism.CoboundaryTransfers.Lifts (lqbS ι hX hinj hsat) c) :
    ∀ y₁ z₁, W₁.C1 y₁ z₁ → (∃ d, ι.f d = W₁.d1 y₁ z₁) →
      ∃ y z, W₁.Cocycle y z ∧ (∃ d, ι.f d = y - c • y₁) ∧ ∃ d, ι.f d = z - c • z₁ := by
  intro y₁ z₁ hC hd
  obtain ⟨hy₁, m₁, hm₁, hz₁⟩ := hC
  have hcoc : (lqbW ι hX).Cocycle (Submodule.Quotient.mk y₁) (Submodule.Quotient.mk z₁) := by
    refine ⟨⟨⟨B.Q ^ M • y₁, hy₁, rfl⟩, Submodule.Quotient.mk m₁, ⟨m₁, hm₁, rfl⟩, ?_⟩, ?_⟩
    · rw [hz₁]; rfl
    · rw [quotient_differential_mk]; exact (lqb_mk_eq_zero ι _).2 hd
  obtain ⟨y, z, hyz, e1, e2⟩ := hL _ _ hcoc
  refine ⟨y, z, hyz, (lqb_mk_eq_zero ι _).1 ?_, (lqb_mk_eq_zero ι _).1 ?_⟩
  · rw [Submodule.Quotient.mk_sub]
    exact sub_eq_zero.2 e1
  · rw [Submodule.Quotient.mk_sub]
    exact sub_eq_zero.2 e2

abbrev lqaQ (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) : Type := lqbD ι

abbrev lqaW (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : ∀ x₀ : D₀, ∃ x, B.X • x = x₀) :
    Formalism.CoboundaryTransfers.WachMod B M (lqaQ ι) := lqbW ι hX

abbrev lqaS (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : ∀ x₀ : D₀, ∃ x, B.X • x = x₀)
    (hinj : Function.Injective ι.f) (hsat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N) :
    Formalism.CoboundaryTransfers.SES W₀ W₁ (lqaW ι hX) := lqbS ι hX hinj hsat

/- English proof (translation)
The claim follows from `lqb_coker ι hX hinj hsat`.
-/
theorem lqa_coker (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : ∀ x₀ : D₀, ∃ x, B.X • x = x₀)
    (hinj : Function.Injective ι.f) (hsat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N) :
    Formalism.CoboundaryTransfers.CokerKilled (lqaS ι hX hinj hsat) 0 := lqb_coker ι hX hinj hsat

/- English proof (translation)
The claim follows from `lqb_ratSurj ι hX hinj hsat H`.
-/
theorem lqa_ratSurj (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : ∀ x₀ : D₀, ∃ x, B.X • x = x₀)
    (hinj : Function.Injective ι.f) (hsat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N)
    (H : ∀ y₁ z₁, W₁.C1 y₁ z₁ → (∃ w, ι.f w = W₁.d1 y₁ z₁) →
      ∃ k : ℕ, ∃ y₀ z₀, W₀.C1 y₀ z₀ ∧ ι.f (W₀.d1 y₀ z₀) = ((B.p : O) ^ k) • W₁.d1 y₁ z₁) :
    Formalism.CoboundaryTransfers.RatSurj (lqaS ι hX hinj hsat) := lqb_ratSurj ι hX hinj hsat H

/- English proof (translation)
The claim follows from `lqb_lifts_abs ι hX hinj hsat c hL y₁ z₁ hC hd`.
-/
theorem lqa_use_lifts (ι : Formalism.CoboundaryTransfers.Hom W₀ W₁) (hX : ∀ x₀ : D₀, ∃ x, B.X • x = x₀)
    (hinj : Function.Injective ι.f) (hsat : ∀ x₀, ι.f x₀ ∈ W₁.N → x₀ ∈ W₀.N) (c : O)
    (hL : Formalism.CoboundaryTransfers.Lifts (lqaS ι hX hinj hsat) c) (y₁ z₁ : D₁) (hC : W₁.C1 y₁ z₁)
    (hd : ∃ w, ι.f w = W₁.d1 y₁ z₁) :
    ∃ y₁' z₁', W₁.Cocycle y₁' z₁' ∧ (∃ a, ι.f a = y₁' - c • y₁) ∧ ∃ b, ι.f b = z₁' - c • z₁ :=
  lqb_lifts_abs ι hX hinj hsat c hL y₁ z₁ hC hd

end LqbAbs

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LqbLocal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O]

attribute [local instance] liftb_modZ liftb_towZO liftb_towZA

def lqb_DDLeft (W : LocWach PD LL O v n) {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L)
    (π : LatHom T₁.L T₂.L) : Prop :=
  Function.Injective (W.map ι) ∧ ∀ x, W.map π (W.map ι x) = 0

/- English proof (translation)
The claim follows from `(liftb_unit_bij W T W.X (liftb_X_unit W)).2`.
-/
theorem lqb_X_surj (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) :
    Function.Surjective (fun x : W.DD T => W.X • x) :=
  (liftb_unit_bij W T W.X (liftb_X_unit W)).2

/- English proof (translation)
Take `⟨m₁, hm₁, hzm⟩` from `hz₁`. Take `⟨d, hdd⟩` from `hdef`. Establish `hcoc : (W.map π y₁, W.map π z₁) ∈ W.divisibleCocycles T₂`. Rewrite using `[liftb_mem_Z1D]`. Establish `hγ : W.γ T₂ (W.map π y₁) = W.map π (W.γ T₁ y₁)` using `(W.map_γ π W.gam y₁).symm`.

Establish `hφ : W.φD T₂ (W.map π z₁) = W.map π (W.φD T₁ z₁)` using `(W.map_φ π z₁).symm`. Rewrite using `[hγ, hφ, ← map_sub, ← map_sub, ← map_sub, ← hdd, hE.2]`. Take `⟨w, hw, _, k, y₀, hy₀, z₀, hz₀, hk⟩` from `hd hses (W.map π y₁) (W.map π z₁) (by`. Express the relevant statement in the definitionally equal form `W.Q ^ M • W.map π y₁ ∈ W.N T₂`. Rewrite using `[← liftb_map_smul]`.

Conclude with `W.map_N π hc₁ hc₂ _ hy₁)`. Use the proof step `⟨W.map π m₁, W.map_N π hc₁ hc₂ _ hm₁, by`. Express the relevant statement in the definitionally equal form `W.X • W.map π m₁ = _`. Rewrite using `[← liftb_map_smul, ← hzm]⟩`. Use `hcoc y₁ z₁ hy₁ ⟨m₁, hm₁, hzm.symm⟩ rfl rfl`.

Take `⟨z₀', hz₀', hz₀e⟩` from `hz₀`. Use `⟨k, y₀, z₀, hy₀, ⟨z₀', hz₀', hz₀e.symm⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk, liftb_ns, map_nsmul, hw]`.
-/
theorem lqb_rat (W : LocWach PD LL O v n) {T₀ T₁ T₂ : LocLat G Qp LL O}
    (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L) (hc₁ : IsCrys PD T₁.ρ) (hc₂ : IsCrys PD T₂.ρ) (M : ℕ) (hE : lqb_DDLeft W ι π)
    (hses : IsSESLat (Qp := Qp) ι π) (hd : Formalism.MainNotions.DeltaInvariantLattices.p2d W ι π M)
    (y₁ z₁ : W.DD T₁) (hy₁ : W.Q ^ M • y₁ ∈ W.N T₁) (hz₁ : ∃ m ∈ W.N T₁, z₁ = W.X • m)
    (hdef : ∃ d, W.map ι d = (W.γ T₁ y₁ - y₁) - (W.φD T₁ z₁ - z₁)) :
    ∃ k : ℕ, ∃ y₀ z₀ : W.DD T₀, W.Q ^ M • y₀ ∈ W.N T₀ ∧ (∃ m ∈ W.N T₀, z₀ = W.X • m) ∧
      W.map ι ((W.γ T₀ y₀ - y₀) - (W.φD T₀ z₀ - z₀)) =
        (PD.p ^ k : ℕ) • ((W.γ T₁ y₁ - y₁) - (W.φD T₁ z₁ - z₁)) := by
  obtain ⟨m₁, hm₁, hzm⟩ := hz₁
  obtain ⟨d, hdd⟩ := hdef
  have hcoc : (W.map π y₁, W.map π z₁) ∈ W.divisibleCocycles T₂ := by
    rw [liftb_mem_Z1D]
    have hγ : W.γ T₂ (W.map π y₁) = W.map π (W.γ T₁ y₁) := (W.map_γ π W.gam y₁).symm
    have hφ : W.φD T₂ (W.map π z₁) = W.map π (W.φD T₁ z₁) := (W.map_φ π z₁).symm
    rw [hγ, hφ, ← map_sub, ← map_sub, ← map_sub, ← hdd, hE.2]
  obtain ⟨w, hw, _, k, y₀, hy₀, z₀, hz₀, hk⟩ := hd hses (W.map π y₁) (W.map π z₁)
    (by
      change W.Q ^ M • W.map π y₁ ∈ W.N T₂
      rw [← liftb_map_smul]
      exact W.map_N π hc₁ hc₂ _ hy₁)
    ⟨W.map π m₁, W.map_N π hc₁ hc₂ _ hm₁, by
      change W.X • W.map π m₁ = _
      rw [← liftb_map_smul, ← hzm]⟩
    hcoc y₁ z₁ hy₁ ⟨m₁, hm₁, hzm.symm⟩ rfl rfl
  obtain ⟨z₀', hz₀', hz₀e⟩ := hz₀
  refine ⟨k, y₀, z₀, hy₀, ⟨z₀', hz₀', hz₀e.symm⟩, ?_⟩
  rw [← hk, liftb_ns, map_nsmul, hw]

/- English proof (translation)
Substitute `hp` using the available equality. Take `⟨I, hQI, hφI, hI⟩` from `hC`. Establish `: IsAdicComplete I ↥(liftb_wach (ℓ` using `PD.p) W T₀ M g₀).N := hI`. Establish `hγX : (liftb_base (ℓ` using `PD.p) W).GammaX (u : ℤ_[PD.p]) := by`. Take `⟨t, ht⟩` from `liftb_gammaX W`.

Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[PD.p] O (LetA O n), hu]`. Conclude with `ht`. Establish `hγQ : (liftb_base (ℓ` using `PD.p) W).GammaQ := by`. Take `⟨w, hw, hw1⟩` from `hQ`.

Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 hw1`. Establish `hwt : w = 1 + W.X * t` using `by rw [mul_comm, ht]; ring`. Conclude with `⟨w, by rw [hwt]; exact liftb_one_add_X_unit W t, ⟨t, hwt⟩, hw⟩`. Establish `h1` using `Formalism.RepresentationBoundsCohomology.N2.phi_map_surjective ℤ_[PD.p] (LetA O n) (liftb_base (ℓ := PD.p) W) M (W.DD T₀) (liftb_wach (ℓ := PD.p) W T₀ M g₀) I 1 (M + 1) ⟨1, by rw [pow_one, mul_one]; exact W.φA_X⟩ (by omega) hQI hφI`. Establish `hRX` using `Formalism.RepresentationBoundsCohomology.N2.regulator_bound_for_x PD.p (LetA O n) (liftb_base (ℓ := PD.p) W) M (W.DD T₀) (liftb_wach (ℓ := PD.p) W T₀ M g₀) hR`.

Establish `hRL : ∀ y, (liftb_wach (ℓ` using `PD.p) W T₀ M g₀).QInv y → ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ (liftb_wach (ℓ := PD.p) W T₀ M g₀).N → y ∈ (liftb_wach (ℓ := PD.p) W T₀ M g₀).N := by`. Introduce `y _ hy`. Use `h6 y ⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, Nat.cast_smul_eq_nsmul]`. Rewrite `hy` using `[Nat.cast_smul_eq_nsmul]`.

Conclude with `hy`. Establish `hrat : ∀ y₁ z₁, (liftb_wach (ℓ` using `PD.p) W T₁ M g₁).C1 y₁ z₁ → (∃ d, (liftb_hom (ℓ := PD.p) W ι M g₀ g₁).f d = (liftb_wach (ℓ := PD.p) W T₁ M g₁).d1 y₁ z₁) → ∃ k : ℕ, ∃ y₀ z₀, (liftb_wach (ℓ := PD.p) W T₀ M g₀).C1 y₀ z₀ ∧ (liftb_hom (ℓ := PD.p) W ι M g₀ g₁).f ((liftb_wach (ℓ := PD.p) W T₀ M g₀).d1 y₀ z₀) = ((((lif …`. Introduce `y₁ z₁ hC1 hdef`. Take `⟨k, y₀, z₀, hy₀, hz₀, hk⟩` from `lqb_rat W ι π g₁.crys c2 M hE hses hd y₁ z₁ hC1.1 hC1.2 hdef`. Conclude with `⟨k, y₀, z₀, ⟨hy₀, hz₀⟩, by rw [liftb_ns]; exact hk⟩`.

Establish `hL` using `Formalism.CoboundaryTransfers.wachLatticeUnramified_statement PD.p (LetA O n) (liftb_base (ℓ := PD.p) W) M u rfl W.φA_X hγX hγQ (W.DD T₀) (W.DD T₁) (lqbD (liftb_hom (ℓ := PD.p) W ι M g₀ g₁)) _ _ _ (lqbS (liftb_hom (ℓ := PD.p) W ι M g₀ g₁) (lqb_X_surj W T₀) hE.1 hsat) 0 W.s (JSet …`. Establish `hU` using `lqb_lifts_abs _ _ _ _ _ hL`. Introduce `y z hy hz hyz`. Take `⟨m, hm, hzm⟩` from `hz`. Take `⟨n₁, hn₁, hπn₁⟩` from `hCK _ hy`.

Take `⟨m₁, hm₁, hπm₁⟩` from `hCK m hm`. Take `⟨y₁, hy₁⟩` from `(liftb_Qpow_bij W T₁ M).2 n₁`. Establish `hy₁' : W.Q ^ M • y₁ = n₁` using `hy₁`. Establish `hπy₁ : W.map π y₁ = (PD.p ^ e : ℕ) • y`. Apply `(liftb_Qpow_bij W T₂ M).1` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `W.Q ^ M • W.map π y₁ = W.Q ^ M • ((PD.p ^ e : ℕ) • y)`. Rewrite using `[← liftb_map_smul, hy₁', hπn₁, smul_comm]`. Establish `hπz₁ : W.map π (W.X • m₁) = (PD.p ^ e : ℕ) • z`. Rewrite using `[liftb_map_smul, hπm₁, hzm, smul_comm]`. Take `⟨w, hw, _⟩` from `hd hses ((PD.p ^ e : ℕ) • y) ((PD.p ^ e : ℕ) • z) (by`.

Express the relevant statement in the definitionally equal form `W.Q ^ M • ((PD.p ^ e : ℕ) • y) ∈ W.N T₂`. Rewrite using `[smul_comm]`. Conclude with `(W.N T₂).smul_of_tower_mem _ hy)`. Use the proof step `⟨(PD.p ^ e : ℕ) • m, (W.N T₂).smul_of_tower_mem _ hm, by`. Express the relevant statement in the definitionally equal form `W.X • ((PD.p ^ e : ℕ) • m) = _`.

Rewrite using `[hzm, smul_comm]⟩`. Use the proof step `((W.divisibleCocycles T₂).smul_of_tower_mem (PD.p ^ e : ℕ) hyz)`. Use `y₁ (W.X • m₁) (by change W.Q ^ M • y₁ ∈ W.N T₁; rw [hy₁']; exact hn₁) ⟨m₁, hm₁, rfl⟩ hπy₁ hπz₁`. Take `⟨y', z', ⟨⟨hy', hz'⟩, hd'⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩` from `hU y₁ (W.X • m₁) ⟨by change W.Q ^ M • y₁ ∈ W.N T₁; rw [hy₁']; exact hn₁, m₁, hm₁, rfl⟩ ⟨w, hw⟩`. Establish `ha' : W.map ι a = y' - (((PD.p : ℕ) : ℤ_[PD.p]) ^ (0 + Formalism.LIFT.eU PD.p M W.s (JSet jumps M))) • y₁` using `ha`.

Establish `hb' : W.map ι b = z' - (((PD.p : ℕ) : ℤ_[PD.p]) ^ (0 + Formalism.LIFT.eU PD.p M W.s (JSet jumps M))) • (W.X • m₁)` using `hb`. Rewrite `ha'`, `hb'` using `[liftb_ns, zero_add]`. Use `⟨y', z', hy', hz', (liftb_mem_Z1D W T₁ y' z').2 hd', ?_, ?_⟩` and prove the remaining obligations. Establish `: y' = W.map ι a + (PD.p ^ Formalism.LIFT.eU PD.p M W.s (JSet jumps M) : ℕ) • y₁`. Rewrite using `[ha']`.

Normalize the expressions using the abelian group laws. Rewrite using `[this, map_add, hE.2, zero_add, map_nsmul, hπy₁, smul_smul, ← pow_add, add_comm]`. Establish `: z' = W.map ι b + (PD.p ^ Formalism.LIFT.eU PD.p M W.s (JSet jumps M) : ℕ) • (W.X • m₁)`. Rewrite using `[hb']`. Normalize the expressions using the abelian group laws.

Rewrite using `[this, map_add, hE.2, zero_add, map_nsmul, hπz₁, smul_smul, ← pow_add, add_comm]`.
-/
theorem lqb_lifts (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (u : ℤ_[ℓ]ˣ)
    (hu : algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ]) = ((W.χΓ W.gam : Oˣ) : O))
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = W.s)
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L) (M : ℕ)
    (g₀ : liftb_Good W T₀ M) (g₁ : liftb_Good W T₁ M) (c2 : IsCrys PD T₂.ρ)
    (hE : lqb_DDLeft W ι π) (hsat : ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) (e : ℕ)
    (jumps : Finset ℤ)
    (hQ : ∃ w : LetA O n, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X})
    (hses : IsSESLat (Qp := Qp) ι π) (hd : Formalism.MainNotions.DeltaInvariantLattices.p2d W ι π M)
    (hCK : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁, W.map π x = (PD.p ^ e : ℕ) • y)
    (hj : ∀ a ∈ Formalism.MainNotions.DeltaInvariantLattices.Jumps (PD := PD) T₀, a ∈ jumps)
    (hss : 1 ≤ M → Formalism.MainNotions.DeltaInvariantLattices.SSEig W T₀ (Formalism.MainNotions.DeltaInvariantLattices.invN W T₀ (W.Q ^ M)) (W.N T₀)
      {c | ∃ a ∈ Formalism.MainNotions.DeltaInvariantLattices.Jumps (PD := PD) T₀, ∃ j : ℕ, 1 ≤ j ∧ j ≤ M ∧
        c = (Formalism.MainNotions.DeltaInvariantLattices.uU W) ^ (-(a + j))})
    (hC : liftb_Complete W T₀) (hR : liftb_RegXQ W T₀) (h6 : Formalism.MainNotions.DeltaInvariantLattices.wachSaturated W T₀) :
    ∀ y z : W.DD T₂, W.Q ^ M • y ∈ W.N T₂ → (∃ m ∈ W.N T₂, z = W.X • m) → (y, z) ∈ W.divisibleCocycles T₂ →
      ∃ y₁ z₁ : W.DD T₁, W.Q ^ M • y₁ ∈ W.N T₁ ∧ (∃ m ∈ W.N T₁, z₁ = W.X • m) ∧
        (y₁, z₁) ∈ W.divisibleCocycles T₁ ∧
        W.map π y₁ = (PD.p ^ (e + Formalism.LIFT.eU PD.p M W.s (JSet jumps M)) : ℕ) • y ∧
        W.map π z₁ = (PD.p ^ (e + Formalism.LIFT.eU PD.p M W.s (JSet jumps M)) : ℕ) • z := by
  subst hp
  obtain ⟨I, hQI, hφI, hI⟩ := hC
  have : IsAdicComplete I ↥(liftb_wach (ℓ := PD.p) W T₀ M g₀).N := hI
  have hγX : (liftb_base (ℓ := PD.p) W).GammaX (u : ℤ_[PD.p]) := by
    obtain ⟨t, ht⟩ := liftb_gammaX W
    refine ⟨t, ?_⟩
    rw [IsScalarTower.algebraMap_apply ℤ_[PD.p] O (LetA O n), hu]
    exact ht
  have hγQ : (liftb_base (ℓ := PD.p) W).GammaQ := by
    obtain ⟨w, hw, hw1⟩ := hQ
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 hw1
    have hwt : w = 1 + W.X * t := by rw [mul_comm, ht]; ring
    exact ⟨w, by rw [hwt]; exact liftb_one_add_X_unit W t, ⟨t, hwt⟩, hw⟩
  have h1 := Formalism.RepresentationBoundsCohomology.N2.phi_map_surjective ℤ_[PD.p] (LetA O n) (liftb_base (ℓ := PD.p) W) M (W.DD T₀)
    (liftb_wach (ℓ := PD.p) W T₀ M g₀) I 1 (M + 1)
    ⟨1, by rw [pow_one, mul_one]; exact W.φA_X⟩ (by omega) hQI hφI
  have hRX := Formalism.RepresentationBoundsCohomology.N2.regulator_bound_for_x PD.p (LetA O n) (liftb_base (ℓ := PD.p) W) M (W.DD T₀)
    (liftb_wach (ℓ := PD.p) W T₀ M g₀) hR
  have hRL : ∀ y, (liftb_wach (ℓ := PD.p) W T₀ M g₀).QInv y →
      ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ (liftb_wach (ℓ := PD.p) W T₀ M g₀).N →
      y ∈ (liftb_wach (ℓ := PD.p) W T₀ M g₀).N := by
    intro y _ hy
    refine h6 y ⟨1, ?_⟩
    rw [pow_one, Nat.cast_smul_eq_nsmul]
    rw [Nat.cast_smul_eq_nsmul] at hy
    exact hy
  have hrat : ∀ y₁ z₁, (liftb_wach (ℓ := PD.p) W T₁ M g₁).C1 y₁ z₁ →
      (∃ d, (liftb_hom (ℓ := PD.p) W ι M g₀ g₁).f d = (liftb_wach (ℓ := PD.p) W T₁ M g₁).d1 y₁ z₁) →
      ∃ k : ℕ, ∃ y₀ z₀, (liftb_wach (ℓ := PD.p) W T₀ M g₀).C1 y₀ z₀ ∧
        (liftb_hom (ℓ := PD.p) W ι M g₀ g₁).f ((liftb_wach (ℓ := PD.p) W T₀ M g₀).d1 y₀ z₀) =
          ((((liftb_base (ℓ := PD.p) W).p : ℕ) : ℤ_[PD.p]) ^ k) •
            (liftb_wach (ℓ := PD.p) W T₁ M g₁).d1 y₁ z₁ := by
    intro y₁ z₁ hC1 hdef
    obtain ⟨k, y₀, z₀, hy₀, hz₀, hk⟩ := lqb_rat W ι π g₁.crys c2 M hE hses hd y₁ z₁ hC1.1 hC1.2 hdef
    exact ⟨k, y₀, z₀, ⟨hy₀, hz₀⟩, by rw [liftb_ns]; exact hk⟩
  have hL := Formalism.CoboundaryTransfers.wachLatticeUnramified_statement PD.p (LetA O n) (liftb_base (ℓ := PD.p) W) M u rfl W.φA_X hγX hγQ
    (W.DD T₀) (W.DD T₁) (lqbD (liftb_hom (ℓ := PD.p) W ι M g₀ g₁)) _ _ _
    (lqbS (liftb_hom (ℓ := PD.p) W ι M g₀ g₁) (lqb_X_surj W T₀) hE.1 hsat) 0 W.s
    (JSet jumps M) W.s_pos W.s_two hv (liftb_zero_notMem_JSet jumps M) h1 hRX
    (liftb_semi W T₀ M g₀ u hu jumps hj hss) hRL
    (lqb_coker _ _ _ _) (lqb_ratSurj _ _ _ _ hrat)
  have hU := lqb_lifts_abs _ _ _ _ _ hL
  intro y z hy hz hyz
  obtain ⟨m, hm, hzm⟩ := hz
  obtain ⟨n₁, hn₁, hπn₁⟩ := hCK _ hy
  obtain ⟨m₁, hm₁, hπm₁⟩ := hCK m hm
  obtain ⟨y₁, hy₁⟩ := (liftb_Qpow_bij W T₁ M).2 n₁
  have hy₁' : W.Q ^ M • y₁ = n₁ := hy₁
  have hπy₁ : W.map π y₁ = (PD.p ^ e : ℕ) • y := by
    apply (liftb_Qpow_bij W T₂ M).1
    change W.Q ^ M • W.map π y₁ = W.Q ^ M • ((PD.p ^ e : ℕ) • y)
    rw [← liftb_map_smul, hy₁', hπn₁, smul_comm]
  have hπz₁ : W.map π (W.X • m₁) = (PD.p ^ e : ℕ) • z := by
    rw [liftb_map_smul, hπm₁, hzm, smul_comm]
  obtain ⟨w, hw, _⟩ := hd hses ((PD.p ^ e : ℕ) • y) ((PD.p ^ e : ℕ) • z)
    (by
      change W.Q ^ M • ((PD.p ^ e : ℕ) • y) ∈ W.N T₂
      rw [smul_comm]
      exact (W.N T₂).smul_of_tower_mem _ hy)
    ⟨(PD.p ^ e : ℕ) • m, (W.N T₂).smul_of_tower_mem _ hm, by
      change W.X • ((PD.p ^ e : ℕ) • m) = _
      rw [hzm, smul_comm]⟩
    ((W.divisibleCocycles T₂).smul_of_tower_mem (PD.p ^ e : ℕ) hyz)
    y₁ (W.X • m₁) (by change W.Q ^ M • y₁ ∈ W.N T₁; rw [hy₁']; exact hn₁) ⟨m₁, hm₁, rfl⟩ hπy₁ hπz₁
  obtain ⟨y', z', ⟨⟨hy', hz'⟩, hd'⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩ := hU y₁ (W.X • m₁)
    ⟨by change W.Q ^ M • y₁ ∈ W.N T₁; rw [hy₁']; exact hn₁, m₁, hm₁, rfl⟩ ⟨w, hw⟩
  have ha' : W.map ι a = y' - (((PD.p : ℕ) : ℤ_[PD.p]) ^
      (0 + Formalism.LIFT.eU PD.p M W.s (JSet jumps M))) • y₁ := ha
  have hb' : W.map ι b = z' - (((PD.p : ℕ) : ℤ_[PD.p]) ^
      (0 + Formalism.LIFT.eU PD.p M W.s (JSet jumps M))) • (W.X • m₁) := hb
  rw [liftb_ns, zero_add] at ha' hb'
  refine ⟨y', z', hy', hz', (liftb_mem_Z1D W T₁ y' z').2 hd', ?_, ?_⟩
  · have : y' = W.map ι a + (PD.p ^ Formalism.LIFT.eU PD.p M W.s (JSet jumps M) : ℕ) • y₁ := by
      rw [ha']; abel
    rw [this, map_add, hE.2, zero_add, map_nsmul, hπy₁, smul_smul, ← pow_add, add_comm]
  · have : z' = W.map ι b + (PD.p ^ Formalism.LIFT.eU PD.p M W.s (JSet jumps M) : ℕ) • (W.X • m₁) := by
      rw [hb']; abel
    rw [this, map_add, hE.2, zero_add, map_nsmul, hπz₁, smul_smul, ← pow_add, add_comm]

def lqb_HLeft (W : LocWach PD LL O v n) : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π → lqb_DDLeft W ι π

/- English proof (translation)
Use `liftb_neZero W` as an intermediate fact. Introduce `hB T₁ T₂ F Mi hi hS hJ1`. Take `⟨c1, c2, hOnto⟩` from `hS`. Take `⟨T₀, ι, hses, c0⟩` from `hKer T₁ T₂ F ⟨c1, c2, hOnto⟩`. Establish `hJ` using `hJmp T₀ T₁ T₂ ι F hses c0 c1 c2`.

Establish `hJ0 : JumpsLet W T₀ Mi hi` using `fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inl ha))`. Establish `hJ2 : JumpsLet W T₂ Mi hi` using `fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inr ha))`. Establish `hc0` using `h2c T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)`. Establish `hc1` using `h2c T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)`. Establish `hd` using `h2d T₀ T₁ T₂ ι F Mi hi c0 c1 c2 (liftb_jl W T₁ Mi hi hJ1)`.

Rewrite `hc0`, `hc1`, `hd` using `[liftb_mx_eq]`. Establish `hQ` using `hc0.1`. Establish `g₀` using `liftb_good_of W T₀ c0 Mi hi (h2 T₀ c0) (h5 T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)) hQ`. Establish `g₁` using `liftb_good_of W T₁ c1 Mi hi (h2 T₁ c1) (h5 T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)) hQ`. Establish `hE` using `hLeft T₀ T₁ T₂ ι F hses`.

Establish `hsat` using `(h6.2.2 T₀ T₁ T₂ ι F c0 c1 c2 hses).2.2.2.1`. Establish `hCK : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁, W.map F x = (PD.p ^ (eWB PD.p W.s (Hmax n Mi hi)) : ℕ) • y`. Introduce `y hy`. Take `⟨x, hx, hxe⟩` from `liftb_kills_all W F _ (hWB hB T₁ T₂ F Mi hi ⟨c1, c2, hOnto⟩ hJ1) y hy`. Conclude with `⟨x, hx, by rw [hxe, lp, liftb_ns]⟩`.

Establish `hL` using `lqb_lifts W hp u hu hv ι F (Mmax n Mi) g₀ g₁ c2 hE hsat (eWB PD.p W.s (Hmax n Mi hi)) (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) hQ hses hd hCK (by`. Introduce and unpack `a ⟨τ, ha⟩`. Conclude with `liftb_mem_jumpSet W T₁ Mi hi hJ1 a τ ((hJ τ a).2 (Or.inl ha)))`. Use the proof step `(fun hM => (hcons T₀ c0) _ hM) (hStr T₀ c0).1 (hStr T₀ c0).2 (h6.1 T₀ c0)`. Apply `liftb_LiftF_of PD F` to reduce the goal to its premises.

Introduce `κ hκ`. Take `⟨c, hc, hcf, rfl⟩` from `(liftb_mem_H1fT PD T₂ κ).1 hκ`. Take `⟨Tp, ι', π', cp, hext⟩` from `hExt T₂ c c2 hcf`. Take `⟨cone, hone0, e, he, hspan, hφe, hγe⟩` from `hOne`. Establish `hJp'` using `hJmp T₂ Tp W.one ι' π' hext.1 c2 cp cone`.

Establish `hJp : JumpsLet W Tp Mi hi`. Introduce `i τ hτ a ha`. Break down `(hJp' τ a).1 ha with h | h` into its components or cases. Conclude with `hJ2 i τ hτ a h`. Rewrite using `[hone0 τ a h]`.

Conclude with `⟨by simp, by simp⟩`. Establish `hImg : InImgA W π' (eWB PD.p W.s (Hmax n Mi hi))`. Take `⟨x, hx, hxe⟩` from `liftb_kills_all W π' _ (hWB hB Tp W.one π' Mi hi ⟨cp, cone, hext.1.2.2.1⟩ hJp) e he`. Conclude with `⟨e, he, hspan, hφe, hγe, x, hx, by rw [hxe, lp, liftb_ns, liftb_ns]⟩`. Take `⟨y, z, h, hy, hz, hcl⟩` from `hExtC T₂ Tp ι' π' Mi hi c2 cp hJ2 c hc hext _ hImg`.

Take `⟨y₁, z₁, hy₁, ⟨m₁, hm₁, hz₁⟩, h₁, e1, e2⟩` from `hL y z hy hz h`. Establish `hf₁` using `(hc1.2 y₁ z₁ hy₁ ⟨m₁, hm₁, hz₁.symm⟩ h₁).1`. Take `⟨κ₁, hκ₁⟩` from `liftb_res_surj W.GKs hB.1 T₁ (W.cl T₁ ⟨(y₁, z₁), h₁⟩)`. Use `⟨κ₁, (h2b T₁ c1 κ₁).2 (by rw [hκ₁]; exact hf₁), ?_⟩` and prove the remaining obligations. Apply `liftb_res_inj W.GKs hB.1 T₂` to reduce the goal to its premises.

Rewrite using `[← liftb_res_nat, hκ₁]`. Establish `hN` using `hNat F ⟨(y₁, z₁), h₁⟩ ((PD.p ^ (eWB PD.p W.s (Hmax n Mi hi) + Formalism.LIFT.eU PD.p (Mmax n Mi) W.s (JSet (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (Mmax n Mi))) : ℕ) • (⟨(y, z), h⟩ : ↥(W.divisibleCocycles T₂))) (by`. Rewrite using `[e1, e2]`. Use the proof step `rfl)`. Use `Eq.trans hN ?_` and prove the remaining obligations.

Use `Eq.trans (map_nsmul (W.cl T₂) _ _) ?_` and prove the remaining obligations. Use `Eq.trans (congrArg _ hcl) ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← liftb_ns (R := O), smul_smul, ← pow_add]`. Use `congr 2`. Simplify using `only [ePB]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coreLiftB_of' (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (u : ℤ_[ℓ]ˣ)
    (hu : algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ]) = ((W.χΓ W.gam : Oˣ) : O))
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = W.s)
    (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (h2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W)
    (hcons : Formalism.MainNotions.DeltaInvariantLattices.GammaSemisimpleQuotient W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W) (h2c : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexThirdProperty W)
    (h2d : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFourthProperty W) (hExtC : coreExt W) (hNat : W.ClNat)
    (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O) (hWB : coreWB W)
    (hKer : liftb_HKer W) (hLeft : lqb_HLeft W) (hStr : liftb_HStr W) (hExt : liftb_HExt W)
    (hOne : liftb_HOne W) : coreLiftB W := by
  have := liftb_neZero W
  intro hB T₁ T₂ F Mi hi hS hJ1
  obtain ⟨c1, c2, hOnto⟩ := hS
  obtain ⟨T₀, ι, hses, c0⟩ := hKer T₁ T₂ F ⟨c1, c2, hOnto⟩
  have hJ := hJmp T₀ T₁ T₂ ι F hses c0 c1 c2
  have hJ0 : JumpsLet W T₀ Mi hi := fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inl ha))
  have hJ2 : JumpsLet W T₂ Mi hi := fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inr ha))
  have hc0 := h2c T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)
  have hc1 := h2c T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)
  have hd := h2d T₀ T₁ T₂ ι F Mi hi c0 c1 c2 (liftb_jl W T₁ Mi hi hJ1)
  rw [liftb_mx_eq] at hc0 hc1 hd
  have hQ := hc0.1
  have g₀ := liftb_good_of W T₀ c0 Mi hi (h2 T₀ c0) (h5 T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)) hQ
  have g₁ := liftb_good_of W T₁ c1 Mi hi (h2 T₁ c1) (h5 T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)) hQ
  have hE := hLeft T₀ T₁ T₂ ι F hses
  have hsat := (h6.2.2 T₀ T₁ T₂ ι F c0 c1 c2 hses).2.2.2.1
  have hCK : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁,
      W.map F x = (PD.p ^ (eWB PD.p W.s (Hmax n Mi hi)) : ℕ) • y := by
    intro y hy
    obtain ⟨x, hx, hxe⟩ := liftb_kills_all W F _ (hWB hB T₁ T₂ F Mi hi ⟨c1, c2, hOnto⟩ hJ1) y hy
    exact ⟨x, hx, by rw [hxe, lp, liftb_ns]⟩
  have hL := lqb_lifts W hp u hu hv ι F (Mmax n Mi) g₀ g₁ c2 hE hsat
    (eWB PD.p W.s (Hmax n Mi hi)) (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) hQ hses hd hCK
    (by
      rintro a ⟨τ, ha⟩
      exact liftb_mem_jumpSet W T₁ Mi hi hJ1 a τ ((hJ τ a).2 (Or.inl ha)))
    (fun hM => (hcons T₀ c0) _ hM) (hStr T₀ c0).1 (hStr T₀ c0).2 (h6.1 T₀ c0)
  apply liftb_LiftF_of PD F
  intro κ hκ
  obtain ⟨c, hc, hcf, rfl⟩ := (liftb_mem_H1fT PD T₂ κ).1 hκ
  obtain ⟨Tp, ι', π', cp, hext⟩ := hExt T₂ c c2 hcf
  obtain ⟨cone, hone0, e, he, hspan, hφe, hγe⟩ := hOne
  have hJp' := hJmp T₂ Tp W.one ι' π' hext.1 c2 cp cone
  have hJp : JumpsLet W Tp Mi hi := by
    intro i τ hτ a ha
    rcases (hJp' τ a).1 ha with h | h
    · exact hJ2 i τ hτ a h
    · rw [hone0 τ a h]
      exact ⟨by simp, by simp⟩
  have hImg : InImgA W π' (eWB PD.p W.s (Hmax n Mi hi)) := by
    obtain ⟨x, hx, hxe⟩ := liftb_kills_all W π' _
      (hWB hB Tp W.one π' Mi hi ⟨cp, cone, hext.1.2.2.1⟩ hJp) e he
    exact ⟨e, he, hspan, hφe, hγe, x, hx, by rw [hxe, lp, liftb_ns, liftb_ns]⟩
  obtain ⟨y, z, h, hy, hz, hcl⟩ := hExtC T₂ Tp ι' π' Mi hi c2 cp hJ2 c hc hext _ hImg
  obtain ⟨y₁, z₁, hy₁, ⟨m₁, hm₁, hz₁⟩, h₁, e1, e2⟩ := hL y z hy hz h
  have hf₁ := (hc1.2 y₁ z₁ hy₁ ⟨m₁, hm₁, hz₁.symm⟩ h₁).1
  obtain ⟨κ₁, hκ₁⟩ := liftb_res_surj W.GKs hB.1 T₁ (W.cl T₁ ⟨(y₁, z₁), h₁⟩)
  refine ⟨κ₁, (h2b T₁ c1 κ₁).2 (by rw [hκ₁]; exact hf₁), ?_⟩
  apply liftb_res_inj W.GKs hB.1 T₂
  rw [← liftb_res_nat, hκ₁]
  have hN := hNat F ⟨(y₁, z₁), h₁⟩
    ((PD.p ^ (eWB PD.p W.s (Hmax n Mi hi) + Formalism.LIFT.eU PD.p (Mmax n Mi) W.s
      (JSet (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (Mmax n Mi))) : ℕ) •
        (⟨(y, z), h⟩ : ↥(W.divisibleCocycles T₂)))
    (by
      rw [e1, e2]
      rfl)
  refine Eq.trans hN ?_
  refine Eq.trans (map_nsmul (W.cl T₂) _ _) ?_
  refine Eq.trans (congrArg _ hcl) ?_
  rw [map_smul, ← liftb_ns (R := O), smul_smul, ← pow_add]
  congr 2
  simp only [ePB]
  ring

end LqbLocal

/- English proof (translation)
Introduce `_ _ _ ι π hses` and use `⟨linj_map_inj _ ((F l).E K s LL h).tie ι π hses, linj_map_zero _ ((F l).E K s LL h).tie ι π hses⟩`.
-/
theorem lqb_HLeft_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l)
    (h : Good K s LL) : lqb_HLeft ((HW l).W K s LL h) := fun _ _ _ ι π hses =>
  ⟨linj_map_inj _ ((F l).E K s LL h).tie ι π hses, linj_map_zero _ ((F l).E K s LL h).tie ι π hses⟩

/- English proof (translation)
Introduce `l _ K s LL h`. Take `⟨z, hz, hzv⟩` from `gam_zl (P := D.loc l) (H := HW l) h`. Conclude with `coreLiftB_of' (ℓ := l) ((HW l).W K s LL h) ((D.loc l).PD_p K) z hz (by rw [(HW l).W_s]; exact hzv) (fun _ _ _ => True) (a2 l K s LL h) (a5 l K s LL h) (a6 l K s LL h) (a11 l K s LL h) (a13 l K s LL h) (a14 l K s LL h) (a15 l K s LL h) (a17 l K s LL h) (a21 l K s LL h).1 (a23 l K …`.
-/
theorem lifting_case_B_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a1 : adm1 D HW F) (a2 : adm2 D HW F) (a5 : adm5 D HW F) (a6 : adm6 D HW F) (a11 : adm11 D HW F)
    (a13 : adm13 D HW F) (a14 : adm14 D HW F) (a15 : adm15 D HW F) (a17 : adm17 D HW F) (a21 : Formalism.MainNotions.CrystallineLiftingBounds.adm21 D HW F)
    (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F) (a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F) (hWB : WachKillsCaseB D HW F) : LiftTheoremCaseB D HW F := by
  intro l _ K s LL h
  obtain ⟨z, hz, hzv⟩ := gam_zl (P := D.loc l) (H := HW l) h
  exact coreLiftB_of' (ℓ := l) ((HW l).W K s LL h) ((D.loc l).PD_p K) z hz
    (by rw [(HW l).W_s]; exact hzv) (fun _ _ _ => True) (a2 l K s LL h) (a5 l K s LL h) (a6 l K s LL h)
    (a11 l K s LL h) (a13 l K s LL h) (a14 l K s LL h) (a15 l K s LL h) (a17 l K s LL h)
    (a21 l K s LL h).1 (a23 l K LL) (hWB l K s LL h) (lker_HKer_D D HW F a22 l K s LL h)
    (lqb_HLeft_holds D HW F l K s LL h) (hstr_B D HW F a1 l K s LL h)
    (liftb_HExt_holds D HW F l K s LL h) (liftb_HOne_holds D HW F l K s LL h)

/- English proof (translation)
Take `⟨a1, a2, -, -, a5, a6, -, -, -, -, a11, -, a13, a14, a15, a16, a17, -, -, -, a21, a22, a23⟩` from `h`. Conclude with `lifting_case_B_of_hypotheses D HW F a1 a2 a5 a6 a11 a13 a14 a15 a17 a21 a22 a23 (wach_statement_case_B D HW F a2 a16)`.
-/
theorem lifting_case_B_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) : LiftTheoremCaseB D HW F := by
  obtain ⟨a1, a2, -, -, a5, a6, -, -, -, -, a11, -, a13, a14, a15, a16, a17, -, -, -, a21, a22,
    a23⟩ := h
  exact lifting_case_B_of_hypotheses D HW F a1 a2 a5 a6 a11 a13 a14 a15 a17 a21 a22 a23 (wach_statement_case_B D HW F a2 a16)

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

section LqaLocal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {ℓ : ℕ} [Fact ℓ.Prime] [Algebra ℤ_[ℓ] O]

attribute [local instance] liftb_modZ liftb_towZO liftb_towZA lifta_towZ

def lqa_HLeft (W : LocWach PD LL O v n) : Prop :=
  ∀ (T₀ T₁ T₂ : LocLat G Qp LL O) (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L),
    IsSESLat (Qp := Qp) ι π →
      Function.Injective (W.map ι) ∧ ∀ x, W.map π (W.map ι x) = 0

/- English proof (translation)
Take `⟨w0, hw0⟩` from `hw0`. Establish `hy₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ y₁ = y₁` using `lifta_inv_of_q W R T₁ M y₁ hyQ.2`. Establish `hz₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ (W.π₀ • m₁) = W.π₀ • m₁` using `(invariant_smul_mem_invariants' W T₁ W.π₀ R.πΔ m₁ hm₁).2`. Take `⟨m₁X, hm₁X, hm₁Xe⟩` from `lifta_π₀_X W R hs T₁ m₁ hm₁.1`. Take `⟨w, hw, _, k, y₀, hy₀, z₀, hz₀, hk⟩` from `hd hses (W.map π y₁) (W.map π (W.π₀ • m₁)) (by`.

Express the relevant statement in the definitionally equal form `W.Q ^ M • W.map π y₁ ∈ W.N T₂`. Rewrite using `[← liftb_map_smul]`. Conclude with `W.map_N π hc₁ hc₂ _ ((lifta_Qq W R hs T₁ M y₁).2 hyQ.1))`. Use the proof step `⟨W.map π m₁X, W.map_N π hc₁ hc₂ _ hm₁X, by`. Express the relevant statement in the definitionally equal form `W.X • W.map π m₁X = _`.

Rewrite using `[← liftb_map_smul, hm₁Xe]⟩`. Use the proof step `(by`. Use `(liftb_mem_Z1D W T₂ _ _).2 ?_` and prove the remaining obligations. Establish `hγ : W.γ T₂ (W.map π y₁) = W.map π (W.γ T₁ y₁)` using `(W.map_γ π W.gam y₁).symm`. Establish `hφ : W.φD T₂ (W.map π (W.π₀ • m₁)) = W.map π (W.φD T₁ (W.π₀ • m₁))` using `(W.map_φ π _).symm`.

Rewrite using `[hγ, hφ, ← map_sub, ← map_sub, ← map_sub, ← hw0, hπι])`. Use `y₁ (W.π₀ • m₁)`. Use the proof step `(by`. Express the relevant statement in the definitionally equal form `W.Q ^ M • y₁ ∈ W.N T₁`. Conclude with `(lifta_Qq W R hs T₁ M y₁).2 hyQ.1)`.

Use the proof step `⟨m₁X, hm₁X, hm₁Xe⟩ rfl rfl`. Establish `hy₀' : qp W ^ M • y₀ ∈ W.N T₀` using `(lifta_Qq W R hs T₀ M y₀).1 hy₀`. Take `⟨z₀', hz₀', hz₀e⟩` from `hz₀`. Establish `hz₀e' : z₀ = (letπ : LetA O n) • z₀'` using `by rw [← lifta_X_eq W hs]; exact hz₀e.symm`. Establish `hk' : (PD.p ^ k : ℕ) • w = (W.γ T₀ y₀ - y₀) - (W.φD T₀ z₀ - z₀)`.

Rewrite using `[← hk, liftb_ns]`. Use `set Y₀ := lifta_avg W T₀ d y₀ with hY₀`. Use `set Z₀ := lifta_avg W T₀ d z₀ with hZ₀`. Establish `hQY₀ : qp W ^ M • Y₀ ∈ W.NΔ T₀`. Rewrite using `[hY₀, ← lifta_avg_smul W T₀ d _ (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) M)]`.

Conclude with `lifta_avg_N W T₀ d _ hy₀'`. Establish `hZ₀N : Z₀ ∈ W.NΔ T₀` using `lifta_avg_N W T₀ d _ (by rw [hz₀e']; exact (W.N T₀).smul_mem _ hz₀')`. Take `⟨x', hx', hx'e⟩` from `lifta_interN W T₀ h9 hm0 Z₀ hZ₀N (lifta_avg_πN W T₀ d z₀ ⟨z₀', hz₀', hz₀e'⟩)`. Establish `havg : (PD.p ^ k : ℕ) • lifta_avg W T₀ d w = (W.γ T₀ Y₀ - Y₀) - (W.φD T₀ Z₀ - Z₀)`. Rewrite using `[← map_nsmul, hk', map_sub, map_sub, map_sub, lifta_avg_φ]`.

Establish `: lifta_avg W T₀ d (W.γ T₀ y₀) = W.γ T₀ (lifta_avg W T₀ d y₀)` using `lifta_avg_γ W T₀ d W.gam y₀`. Rewrite using `[this]`. Establish `hιavg : W.map ι (lifta_avg W T₀ d w) = (W.γ T₁ y₁ - y₁) - (W.φD T₁ (W.π₀ • m₁) - W.π₀ • m₁)`. Rewrite using `[lifta_avg_map, hw, map_sub, map_sub, map_sub, lifta_avg_φ]`. Establish `h1 : lifta_avg W T₁ d (W.γ T₁ y₁) = W.γ T₁ (lifta_avg W T₁ d y₁)` using `lifta_avg_γ W T₁ d W.gam y₁`.

Rewrite using `[h1, lifta_avg_fix W T₁ d hd1 y₁ hy₁Δ, lifta_avg_fix W T₁ d hd1 _ hz₁Δ]`. Use `⟨k, Y₀, x', hQY₀, hx', ?_⟩` and prove the remaining obligations. Rewrite using `[← hx'e, ← havg, map_nsmul, hιavg]`.
-/
theorem lqa_defect (W : LocWach PD LL O v n) (R : lifta_Ring W) (hs : W.s = 1)
    {T₀ T₁ T₂ : LocLat G Qp LL O}
    (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L) (hc₁ : IsCrys PD T₁.ρ) (hc₂ : IsCrys PD T₂.ρ) (M : ℕ)
    (hπι : ∀ x, W.map π (W.map ι x) = 0)
    (hses : IsSESLat (Qp := Qp) ι π) (hd : Formalism.MainNotions.DeltaInvariantLattices.p2d W ι π M)
    (d : O) (hd1 : d * (W.DelF.card : O) = 1) (h9 : P9π₀ W)
    (hm0 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₀ W.π₀)
    (y₁ m₁ : W.DD T₁) (hyQ : qp W ^ M • y₁ ∈ W.NΔ T₁) (hm₁ : m₁ ∈ W.NΔ T₁)
    (hw0 : ∃ w, W.map ι w = (W.γ T₁ y₁ - y₁) - (W.φD T₁ (W.π₀ • m₁) - W.π₀ • m₁)) :
    ∃ (k : ℕ) (Y₀ x' : W.DD T₀), qp W ^ M • Y₀ ∈ W.NΔ T₀ ∧ x' ∈ W.NΔ T₀ ∧
      W.map ι ((W.γ T₀ Y₀ - Y₀) - (W.φD T₀ (W.π₀ • x') - W.π₀ • x')) =
        (PD.p ^ k : ℕ) • ((W.γ T₁ y₁ - y₁) - (W.φD T₁ (W.π₀ • m₁) - W.π₀ • m₁)) := by
  obtain ⟨w0, hw0⟩ := hw0
  have hy₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ y₁ = y₁ := lifta_inv_of_q W R T₁ M y₁ hyQ.2
  have hz₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ (W.π₀ • m₁) = W.π₀ • m₁ :=
    (invariant_smul_mem_invariants' W T₁ W.π₀ R.πΔ m₁ hm₁).2
  obtain ⟨m₁X, hm₁X, hm₁Xe⟩ := lifta_π₀_X W R hs T₁ m₁ hm₁.1
  obtain ⟨w, hw, _, k, y₀, hy₀, z₀, hz₀, hk⟩ := hd hses (W.map π y₁) (W.map π (W.π₀ • m₁))
    (by
      change W.Q ^ M • W.map π y₁ ∈ W.N T₂
      rw [← liftb_map_smul]
      exact W.map_N π hc₁ hc₂ _ ((lifta_Qq W R hs T₁ M y₁).2 hyQ.1))
    ⟨W.map π m₁X, W.map_N π hc₁ hc₂ _ hm₁X, by
      change W.X • W.map π m₁X = _
      rw [← liftb_map_smul, hm₁Xe]⟩
    (by
      refine (liftb_mem_Z1D W T₂ _ _).2 ?_
      have hγ : W.γ T₂ (W.map π y₁) = W.map π (W.γ T₁ y₁) := (W.map_γ π W.gam y₁).symm
      have hφ : W.φD T₂ (W.map π (W.π₀ • m₁)) = W.map π (W.φD T₁ (W.π₀ • m₁)) :=
        (W.map_φ π _).symm
      rw [hγ, hφ, ← map_sub, ← map_sub, ← map_sub, ← hw0, hπι])
    y₁ (W.π₀ • m₁)
    (by
      change W.Q ^ M • y₁ ∈ W.N T₁
      exact (lifta_Qq W R hs T₁ M y₁).2 hyQ.1)
    ⟨m₁X, hm₁X, hm₁Xe⟩ rfl rfl
  have hy₀' : qp W ^ M • y₀ ∈ W.N T₀ := (lifta_Qq W R hs T₀ M y₀).1 hy₀
  obtain ⟨z₀', hz₀', hz₀e⟩ := hz₀
  have hz₀e' : z₀ = (letπ : LetA O n) • z₀' := by rw [← lifta_X_eq W hs]; exact hz₀e.symm
  have hk' : (PD.p ^ k : ℕ) • w = (W.γ T₀ y₀ - y₀) - (W.φD T₀ z₀ - z₀) := by
    rw [← hk, liftb_ns]
  set Y₀ := lifta_avg W T₀ d y₀ with hY₀
  set Z₀ := lifta_avg W T₀ d z₀ with hZ₀
  have hQY₀ : qp W ^ M • Y₀ ∈ W.NΔ T₀ := by
    rw [hY₀, ← lifta_avg_smul W T₀ d _ (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) M)]
    exact lifta_avg_N W T₀ d _ hy₀'
  have hZ₀N : Z₀ ∈ W.NΔ T₀ :=
    lifta_avg_N W T₀ d _ (by rw [hz₀e']; exact (W.N T₀).smul_mem _ hz₀')
  obtain ⟨x', hx', hx'e⟩ := lifta_interN W T₀ h9 hm0 Z₀ hZ₀N
    (lifta_avg_πN W T₀ d z₀ ⟨z₀', hz₀', hz₀e'⟩)
  have havg : (PD.p ^ k : ℕ) • lifta_avg W T₀ d w = (W.γ T₀ Y₀ - Y₀) - (W.φD T₀ Z₀ - Z₀) := by
    rw [← map_nsmul, hk', map_sub, map_sub, map_sub, lifta_avg_φ]
    have : lifta_avg W T₀ d (W.γ T₀ y₀) = W.γ T₀ (lifta_avg W T₀ d y₀) := lifta_avg_γ W T₀ d W.gam y₀
    rw [this]
  have hιavg : W.map ι (lifta_avg W T₀ d w) =
      (W.γ T₁ y₁ - y₁) - (W.φD T₁ (W.π₀ • m₁) - W.π₀ • m₁) := by
    rw [lifta_avg_map, hw, map_sub, map_sub, map_sub, lifta_avg_φ]
    have h1 : lifta_avg W T₁ d (W.γ T₁ y₁) = W.γ T₁ (lifta_avg W T₁ d y₁) :=
      lifta_avg_γ W T₁ d W.gam y₁
    rw [h1, lifta_avg_fix W T₁ d hd1 y₁ hy₁Δ, lifta_avg_fix W T₁ d hd1 _ hz₁Δ]
  refine ⟨k, Y₀, x', hQY₀, hx', ?_⟩
  rw [← hx'e, ← havg, map_nsmul, hιavg]

/- English proof (translation)
Substitute `hp` using the available equality. Establish `R` using `lifta_ring_of W h9`. Take `⟨I, hQI, hφI, hI⟩` from `hC`. Establish `: IsAdicComplete I ↥(lifta_wach (ℓ` using `PD.p) W R T₀ (Mmax n Mi) g₀).N := hI`. Take `⟨cE, hcE⟩` from `R.πU.exists_right_inv`.

Take `⟨c, hc⟩` from `lifta_exists_c u hv`. Establish `hPhi : (lifta_base (ℓ` using `PD.p) W R).PhiX (PD.p - 1) := by`. Take `⟨t, ht, h⟩` from `R.φπ`. Conclude with `⟨⟨t, ht⟩, Subtype.ext h⟩`. Establish `hγX : (lifta_base (ℓ` using `PD.p) W R).GammaX ((u : ℤ_[PD.p]) ^ (PD.p - 1)) := by`.

Take `⟨t, ht, h⟩` from `R.γπ`. Use `⟨⟨t, ht⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `W.γA W.gam W.π₀ = W.π₀ * (algebraMap ℤ_[PD.p] (LetA O n) ((u : ℤ_[PD.p]) ^ (PD.p - 1)) + W.π₀ * t)`. Rewrite using `[IsScalarTower.algebraMap_apply ℤ_[PD.p] O (LetA O n), map_pow, hu]`. Conclude with `h`.

Establish `hU : Units.map (algebraMap ℤ_[PD.p] O).toMonoidHom u = W.χΓ W.gam` using `Units.ext hu`. Establish `hcO : ∀ x : ℤ, ((PD.p : ℕ) : O) * algebraMap ℤ_[PD.p] O (c x) = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)`. Introduce `x`. Establish `h` using `congrArg (algebraMap ℤ_[PD.p] O) (hc x)`. Rewrite `h` using `[map_mul, map_natCast, map_sub, map_one]`.

Rewrite using `[h, ← hU, ← map_zpow]`. Both sides reduce to the same expression. Establish `hstabN : ∀ x ∈ W.NΔ T₀, lifta_δ W T₀ cE x ∈ W.NΔ T₀`. Introduce `x hx`. Take `⟨x', hx', h⟩` from `g₀.γN x hx`.

Establish `: lifta_δ W T₀ cE x = x'`. Apply `lifta_π₀_cancel W T₀ cE hcE` to reduce the goal to its premises. Rewrite using `[lifta_δ_spec W T₀ cE hcE, h]`. Rewrite using `[this]`. Conclude with `hx'`.

Establish `hSemi : Formalism.RepresentationBoundsCohomology.N2.SemiA (lifta_wach (ℓ` using `PD.p) W R T₀ (Mmax n Mi) g₀) ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) c jumps := by`. Introduce `y hy`. Establish `hy' : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₀` using `hy`. Establish `hyΔ` using `lifta_inv_of_q W R T₀ (Mmax n Mi) y hy'.2`. Express the relevant statement in the definitionally equal form `Polynomial.aeval ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) _ y ∈ W.NΔ T₀`.

Rewrite using `[liftb_aeval_res, Polynomial.map_prod]`. Establish `h0` using `lifta_semiO W T₀ cE hcE hA hD Mi hi c0 hJ0 (fun x => algebraMap ℤ_[PD.p] O (c x)) hcO (Mmax n Mi) y hy'.1 hyΔ`. Establish `hsub : ((jumpSet W T₀ (Mmax n Mi) (Mmax n hi)) ×ˢ Finset.Icc (1 : ℤ) (Mmax n Mi)).image (fun p : ℤ × ℤ => p.1 + p.2) ⊆ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi)` using `Finset.image_subset_image (Finset.product_subset_product hj (Finset.Subset.refl _))`. Take `⟨R', hR'⟩` from `Finset.prod_dvd_prod_of_subset _ _ (fun x : ℤ => (Polynomial.X - Polynomial.C (algebraMap ℤ_[PD.p] O (c x)) : Polynomial O)) hsub`. Establish `hmap : ∏ j ∈ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi), (Polynomial.X - Polynomial.C (c j)).map (algebraMap ℤ_[PD.p] O) = ∏ j ∈ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi), (Polynomial.X - Polynomial.C (algebraMap ℤ_[PD.p] O (c …` using `Finset.prod_congr rfl (fun j _ => by`.

Rewrite using `[Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C])`. Rewrite using `[hmap, hR', mul_comm, map_mul, Module.End.mul_apply]`. Use `liftb_aeval_mem (W.NΔ T₀) _ hstabN R' _ ⟨h0, ?_⟩` and prove the remaining obligations. Conclude with `liftb_aeval_mem (lifta_Inv W T₀) _ (lifta_δ_Inv W R T₀ cE hcE) _ y hyΔ`. Establish `hZ : ∀ y, (lifta_wach (ℓ` using `PD.p) W R T₀ (Mmax n Mi) g₀).QInv y → ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N → y ∈ (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N := by`.

Introduce `y hyQ hy`. Establish `hyQ' : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₀` using `hyQ`. Establish `hy' : ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ W.NΔ T₀` using `hy`. Use `⟨h6 y ⟨1, ?_⟩, lifta_inv_of_q W R T₀ (Mmax n Mi) y hyQ'.2⟩` and prove the remaining obligations. Rewrite using `[pow_one, Nat.cast_smul_eq_nsmul]`.

Use `hy'.1` as an intermediate fact. Rewrite `this` using `[Nat.cast_smul_eq_nsmul]`. Conclude with `this`. Establish `hX₀ : ∀ x₀ : W.DD T₀, ∃ x, (lifta_base (ℓ` using `PD.p) W R).X • x = x₀ := (liftb_unit_bij W T₀ W.π₀ R.πU).2`. Establish `hinj' : Function.Injective (lifta_hom (ℓ` using `PD.p) W R ι (Mmax n Mi) g₀ g₁).f := hinj`.

Establish `hsat' : ∀ x₀, (lifta_hom (ℓ` using `PD.p) W R ι (Mmax n Mi) g₀ g₁).f x₀ ∈ (lifta_wach (ℓ := PD.p) W R T₁ (Mmax n Mi) g₁).N → x₀ ∈ (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N := fun x hx => ⟨hsat x hx.1, fun δ hδ => hinj (by rw [W.map_γ]; exact hx.2 δ hδ)⟩`. Establish `hRS : Formalism.CoboundaryTransfers.RatSurj (lqaS (lifta_hom (ℓ` using `PD.p) W R ι (Mmax n Mi) g₀ g₁) hX₀ hinj' hsat') := by`. Apply `lqa_ratSurj` to reduce the goal to its premises. Introduce and unpack `y₁ z₁ ⟨hyQ, m₁, hm₁, hz₁⟩ hw`. Establish `hz₁' : z₁ = W.π₀ • m₁` using `hz₁`.

Substitute `hz₁'` using the available equality. Take `⟨k, Y₀, x', hY₀, hx', hk⟩` from `lqa_defect W R hA.2.1 ι π g₁.crys c2 (Mmax n Mi) hπι hses hd d hd1 h9 hm0 y₁ m₁ hyQ hm₁ hw`. Use `⟨k, Y₀, W.π₀ • x', ⟨hY₀, x', hx', rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[liftb_ns]`. Conclude with `hk`.

Establish `hL` using `lifta_core PD.p hA.2.2 ↥W.AΔ (lifta_base (ℓ := PD.p) W R) (Mmax n Mi) u jumps c rfl hPhi hγX hv hc (W.DD T₀) (W.DD T₁) (lqaQ (lifta_hom (ℓ := PD.p) W R ι (Mmax n Mi) g₀ g₁)) _ _ _ (lqaS (lifta_hom (ℓ := PD.p) W R ι (Mmax n Mi) g₀ g₁) hX₀ hinj' hsat') ((lifta_δ W T₀ cE).restrictSc …`. Introduce `y z hy hz hyz`. Take `⟨m, hm, hz'⟩` from `hz`. Take `⟨n₁, hn₁, hπn₁⟩` from `hCK _ hy`. Take `⟨m₁, hm₁, hπm₁⟩` from `hCK m hm`.

Take `⟨y₁, hy₁⟩` from `(lifta_qpow_bij W R T₁ (Mmax n Mi)).2 n₁`. Establish `hy₁' : qp W ^ (Mmax n Mi) • y₁ = n₁` using `hy₁`. Establish `hπy₁ : W.map π y₁ = (PD.p ^ e : ℕ) • y`. Apply `(lifta_qpow_bij W R T₂ (Mmax n Mi)).1` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `qp W ^ (Mmax n Mi) • W.map π y₁ = qp W ^ (Mmax n Mi) • ((PD.p ^ e : ℕ) • y)`.

Rewrite using `[← liftb_map_smul, hy₁', hπn₁, smul_comm]`. Establish `hπz₁ : W.map π (W.π₀ • m₁) = (PD.p ^ e : ℕ) • z`. Rewrite using `[liftb_map_smul, hπm₁, hz', smul_comm]`. Take `⟨mX, hmX, hmXe⟩` from `lifta_π₀_X W R hA.2.1 T₂ m hm.1`. Take `⟨m₁X, hm₁X, hm₁Xe⟩` from `lifta_π₀_X W R hA.2.1 T₁ m₁ hm₁.1`.

Take `⟨w, hw, _⟩` from `hd hses ((PD.p ^ e : ℕ) • y) ((PD.p ^ e : ℕ) • z) (by`. Express the relevant statement in the definitionally equal form `W.Q ^ (Mmax n Mi) • ((PD.p ^ e : ℕ) • y) ∈ W.N T₂`. Rewrite using `[smul_comm]`. Conclude with `(W.N T₂).smul_of_tower_mem _ ((lifta_Qq W R hA.2.1 T₂ (Mmax n Mi) y).2 hy.1))`. Use the proof step `⟨(PD.p ^ e : ℕ) • mX, (W.N T₂).smul_of_tower_mem _ hmX, by`.

Express the relevant statement in the definitionally equal form `W.X • ((PD.p ^ e : ℕ) • mX) = _`. Rewrite using `[smul_comm, hmXe, hz']⟩`. Use the proof step `((W.divisibleCocycles T₂).smul_of_tower_mem (PD.p ^ e : ℕ) hyz)`. Use `y₁ (W.π₀ • m₁)`. Use the proof step `(by`.

Express the relevant statement in the definitionally equal form `W.Q ^ (Mmax n Mi) • y₁ ∈ W.N T₁`. Conclude with `(lifta_Qq W R hA.2.1 T₁ (Mmax n Mi) y₁).2 (by rw [hy₁']; exact hn₁.1))`. Use the proof step `⟨m₁X, hm₁X, hm₁Xe⟩ hπy₁ hπz₁`. Take `⟨y₁', z₁', ⟨⟨hy₁Q, hz₁X⟩, hd₁⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩` from `lqa_use_lifts (lifta_hom (ℓ := PD.p) W R ι (Mmax n Mi) g₀ g₁) hX₀ hinj' hsat' _ hL y₁ (W.π₀ • m₁) ⟨by rw [← hy₁'] at hn₁; exact hn₁, m₁, hm₁, rfl⟩ ⟨w, hw⟩`. Rewrite `ha`, `hb` using `[lifta_JSet_eq, zero_add, liftb_ns]`.

Establish `ha' : W.map ι a = y₁' - (PD.p ^ eUA PD.p (Mmax n Mi) (JSet jumps (Mmax n Mi)) : ℕ) • y₁` using `ha`. Establish `hb' : W.map ι b = z₁' - (PD.p ^ eUA PD.p (Mmax n Mi) (JSet jumps (Mmax n Mi)) : ℕ) • (W.π₀ • m₁)` using `hb`. Use `⟨y₁', z₁', hy₁Q, hz₁X, (liftb_mem_Z1D W T₁ y₁' z₁').2 hd₁, ?_, ?_⟩` and prove the remaining obligations. Establish `h0` using `hπι a`. Rewrite `h0` using `[ha', map_sub, map_nsmul, hπy₁, sub_eq_zero]`.

Rewrite using `[h0, smul_smul, ← pow_add, add_comm]`. Establish `h0` using `hπι b`. Rewrite `h0` using `[hb', map_sub, map_nsmul, hπz₁, sub_eq_zero]`. Rewrite using `[h0, smul_smul, ← pow_add, add_comm]`.
-/
theorem lqa_lifts (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (hA : CaseA W) (u : ℤ_[ℓ]ˣ)
    (hu : algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ]) = ((W.χΓ W.gam : Oˣ) : O))
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = 1) (h9 : P9π₀ W)
    {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)
    (Mi hi : ZMod n → ℕ)
    (g₀ : lifta_Good W T₀ (Mmax n Mi)) (g₁ : lifta_Good W T₁ (Mmax n Mi)) (c2 : IsCrys PD T₂.ρ)
    (hinj : Function.Injective (W.map ι)) (hπι : ∀ x, W.map π (W.map ι x) = 0)
    (hsat : ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) (e : ℕ)
    (hses : IsSESLat (Qp := Qp) ι π) (hd : Formalism.MainNotions.DeltaInvariantLattices.p2d W ι π (Mmax n Mi))
    (d : O) (hd1 : d * (W.DelF.card : O) = 1) (hm0 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₀ W.π₀)
    (hCK : ∀ y ∈ W.NΔ T₂, ∃ x ∈ W.NΔ T₁, W.map π x = (PD.p ^ e : ℕ) • y)
    (c0 : IsCrys PD T₀.ρ) (hJ0 : JumpsLet W T₀ Mi hi) (hD : coreDss W) (jumps : Finset ℤ)
    (hj : jumpSet W T₀ (Mmax n Mi) (Mmax n hi) ⊆ jumps)
    (hC : lifta_Complete W T₀) (h6 : Formalism.MainNotions.DeltaInvariantLattices.wachSaturated W T₀) :
    ∀ y z : W.DD T₂, qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₂ → (∃ m ∈ W.NΔ T₂, z = W.π₀ • m) →
      (y, z) ∈ W.divisibleCocycles T₂ →
      ∃ y₁ z₁ : W.DD T₁, qp W ^ (Mmax n Mi) • y₁ ∈ W.NΔ T₁ ∧ (∃ m ∈ W.NΔ T₁, z₁ = W.π₀ • m) ∧
        (y₁, z₁) ∈ W.divisibleCocycles T₁ ∧
        W.map π y₁ = (PD.p ^ (e + eUA PD.p (Mmax n Mi) (JSet jumps (Mmax n Mi))) : ℕ) • y ∧
        W.map π z₁ = (PD.p ^ (e + eUA PD.p (Mmax n Mi) (JSet jumps (Mmax n Mi))) : ℕ) • z := by
  subst hp
  have R := lifta_ring_of W h9
  obtain ⟨I, hQI, hφI, hI⟩ := hC
  have : IsAdicComplete I ↥(lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N := hI
  obtain ⟨cE, hcE⟩ := R.πU.exists_right_inv
  obtain ⟨c, hc⟩ := lifta_exists_c u hv
  have hPhi : (lifta_base (ℓ := PD.p) W R).PhiX (PD.p - 1) := by
    obtain ⟨t, ht, h⟩ := R.φπ
    exact ⟨⟨t, ht⟩, Subtype.ext h⟩
  have hγX : (lifta_base (ℓ := PD.p) W R).GammaX ((u : ℤ_[PD.p]) ^ (PD.p - 1)) := by
    obtain ⟨t, ht, h⟩ := R.γπ
    refine ⟨⟨t, ht⟩, Subtype.ext ?_⟩
    change W.γA W.gam W.π₀ =
      W.π₀ * (algebraMap ℤ_[PD.p] (LetA O n) ((u : ℤ_[PD.p]) ^ (PD.p - 1)) + W.π₀ * t)
    rw [IsScalarTower.algebraMap_apply ℤ_[PD.p] O (LetA O n), map_pow, hu]
    exact h
  have hU : Units.map (algebraMap ℤ_[PD.p] O).toMonoidHom u = W.χΓ W.gam := Units.ext hu
  have hcO : ∀ x : ℤ, ((PD.p : ℕ) : O) * algebraMap ℤ_[PD.p] O (c x) =
      1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) := by
    intro x
    have h := congrArg (algebraMap ℤ_[PD.p] O) (hc x)
    rw [map_mul, map_natCast, map_sub, map_one] at h
    rw [h, ← hU, ← map_zpow]
    rfl
  have hstabN : ∀ x ∈ W.NΔ T₀, lifta_δ W T₀ cE x ∈ W.NΔ T₀ := by
    intro x hx
    obtain ⟨x', hx', h⟩ := g₀.γN x hx
    have : lifta_δ W T₀ cE x = x' := by
      apply lifta_π₀_cancel W T₀ cE hcE
      rw [lifta_δ_spec W T₀ cE hcE, h]
    rw [this]
    exact hx'
  have hSemi : Formalism.RepresentationBoundsCohomology.N2.SemiA (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀)
      ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) c jumps := by
    intro y hy
    have hy' : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₀ := hy
    have hyΔ := lifta_inv_of_q W R T₀ (Mmax n Mi) y hy'.2
    change Polynomial.aeval ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) _ y ∈ W.NΔ T₀
    rw [liftb_aeval_res, Polynomial.map_prod]
    have h0 := lifta_semiO W T₀ cE hcE hA hD Mi hi c0 hJ0 (fun x => algebraMap ℤ_[PD.p] O (c x)) hcO
      (Mmax n Mi) y hy'.1 hyΔ
    have hsub : ((jumpSet W T₀ (Mmax n Mi) (Mmax n hi)) ×ˢ Finset.Icc (1 : ℤ) (Mmax n Mi)).image
        (fun p : ℤ × ℤ => p.1 + p.2) ⊆ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi) :=
      Finset.image_subset_image (Finset.product_subset_product hj (Finset.Subset.refl _))
    obtain ⟨R', hR'⟩ := Finset.prod_dvd_prod_of_subset _ _
      (fun x : ℤ => (Polynomial.X - Polynomial.C (algebraMap ℤ_[PD.p] O (c x)) : Polynomial O)) hsub
    have hmap : ∏ j ∈ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi),
        (Polynomial.X - Polynomial.C (c j)).map (algebraMap ℤ_[PD.p] O) =
        ∏ j ∈ Formalism.RepresentationBoundsCohomology.N2.eigSet jumps (Mmax n Mi),
          (Polynomial.X - Polynomial.C (algebraMap ℤ_[PD.p] O (c j)) : Polynomial O) :=
      Finset.prod_congr rfl (fun j _ => by
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C])
    rw [hmap, hR', mul_comm, map_mul, Module.End.mul_apply]
    refine liftb_aeval_mem (W.NΔ T₀) _ hstabN R' _ ⟨h0, ?_⟩
    exact liftb_aeval_mem (lifta_Inv W T₀) _ (lifta_δ_Inv W R T₀ cE hcE) _ y hyΔ
  have hZ : ∀ y, (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).QInv y →
      ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N →
      y ∈ (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N := by
    intro y hyQ hy
    have hyQ' : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₀ := hyQ
    have hy' : ((PD.p : ℕ) : ℤ_[PD.p]) • y ∈ W.NΔ T₀ := hy
    refine ⟨h6 y ⟨1, ?_⟩, lifta_inv_of_q W R T₀ (Mmax n Mi) y hyQ'.2⟩
    rw [pow_one, Nat.cast_smul_eq_nsmul]
    have := hy'.1
    rw [Nat.cast_smul_eq_nsmul] at this
    exact this
  have hX₀ : ∀ x₀ : W.DD T₀, ∃ x, (lifta_base (ℓ := PD.p) W R).X • x = x₀ :=
    (liftb_unit_bij W T₀ W.π₀ R.πU).2
  have hinj' : Function.Injective (lifta_hom (ℓ := PD.p) W R ι (Mmax n Mi) g₀ g₁).f := hinj
  have hsat' : ∀ x₀, (lifta_hom (ℓ := PD.p) W R ι (Mmax n Mi) g₀ g₁).f x₀ ∈
      (lifta_wach (ℓ := PD.p) W R T₁ (Mmax n Mi) g₁).N →
      x₀ ∈ (lifta_wach (ℓ := PD.p) W R T₀ (Mmax n Mi) g₀).N :=
    fun x hx => ⟨hsat x hx.1, fun δ hδ => hinj (by rw [W.map_γ]; exact hx.2 δ hδ)⟩
  have hRS : Formalism.CoboundaryTransfers.RatSurj
      (lqaS (lifta_hom (ℓ := PD.p) W R ι (Mmax n Mi) g₀ g₁) hX₀ hinj' hsat') := by
    apply lqa_ratSurj
    rintro y₁ z₁ ⟨hyQ, m₁, hm₁, hz₁⟩ hw
    have hz₁' : z₁ = W.π₀ • m₁ := hz₁
    subst hz₁'
    obtain ⟨k, Y₀, x', hY₀, hx', hk⟩ := lqa_defect W R hA.2.1 ι π g₁.crys c2 (Mmax n Mi) hπι hses hd d hd1 h9 hm0
      y₁ m₁ hyQ hm₁ hw
    refine ⟨k, Y₀, W.π₀ • x', ⟨hY₀, x', hx', rfl⟩, ?_⟩
    rw [liftb_ns]
    exact hk
  have hL := lifta_core PD.p hA.2.2 ↥W.AΔ (lifta_base (ℓ := PD.p) W R) (Mmax n Mi) u jumps c rfl hPhi
    hγX hv hc (W.DD T₀) (W.DD T₁) (lqaQ (lifta_hom (ℓ := PD.p) W R ι (Mmax n Mi) g₀ g₁)) _ _ _
    (lqaS (lifta_hom (ℓ := PD.p) W R ι (Mmax n Mi) g₀ g₁) hX₀ hinj' hsat')
    ((lifta_δ W T₀ cE).restrictScalars ℤ_[PD.p]) I (lifta_δ_spec W T₀ cE hcE) (hQI _) hφI hZ hSemi 0
    (lqa_coker _ hX₀ hinj' hsat') hRS
  intro y z hy hz hyz
  obtain ⟨m, hm, hz'⟩ := hz
  obtain ⟨n₁, hn₁, hπn₁⟩ := hCK _ hy
  obtain ⟨m₁, hm₁, hπm₁⟩ := hCK m hm
  obtain ⟨y₁, hy₁⟩ := (lifta_qpow_bij W R T₁ (Mmax n Mi)).2 n₁
  have hy₁' : qp W ^ (Mmax n Mi) • y₁ = n₁ := hy₁
  have hπy₁ : W.map π y₁ = (PD.p ^ e : ℕ) • y := by
    apply (lifta_qpow_bij W R T₂ (Mmax n Mi)).1
    change qp W ^ (Mmax n Mi) • W.map π y₁ = qp W ^ (Mmax n Mi) • ((PD.p ^ e : ℕ) • y)
    rw [← liftb_map_smul, hy₁', hπn₁, smul_comm]
  have hπz₁ : W.map π (W.π₀ • m₁) = (PD.p ^ e : ℕ) • z := by
    rw [liftb_map_smul, hπm₁, hz', smul_comm]
  obtain ⟨mX, hmX, hmXe⟩ := lifta_π₀_X W R hA.2.1 T₂ m hm.1
  obtain ⟨m₁X, hm₁X, hm₁Xe⟩ := lifta_π₀_X W R hA.2.1 T₁ m₁ hm₁.1
  obtain ⟨w, hw, _⟩ := hd hses ((PD.p ^ e : ℕ) • y) ((PD.p ^ e : ℕ) • z)
    (by
      change W.Q ^ (Mmax n Mi) • ((PD.p ^ e : ℕ) • y) ∈ W.N T₂
      rw [smul_comm]
      exact (W.N T₂).smul_of_tower_mem _ ((lifta_Qq W R hA.2.1 T₂ (Mmax n Mi) y).2 hy.1))
    ⟨(PD.p ^ e : ℕ) • mX, (W.N T₂).smul_of_tower_mem _ hmX, by
      change W.X • ((PD.p ^ e : ℕ) • mX) = _
      rw [smul_comm, hmXe, hz']⟩
    ((W.divisibleCocycles T₂).smul_of_tower_mem (PD.p ^ e : ℕ) hyz)
    y₁ (W.π₀ • m₁)
    (by
      change W.Q ^ (Mmax n Mi) • y₁ ∈ W.N T₁
      exact (lifta_Qq W R hA.2.1 T₁ (Mmax n Mi) y₁).2 (by rw [hy₁']; exact hn₁.1))
    ⟨m₁X, hm₁X, hm₁Xe⟩ hπy₁ hπz₁
  obtain ⟨y₁', z₁', ⟨⟨hy₁Q, hz₁X⟩, hd₁⟩, ⟨a, ha⟩, ⟨b, hb⟩⟩ :=
    lqa_use_lifts (lifta_hom (ℓ := PD.p) W R ι (Mmax n Mi) g₀ g₁) hX₀ hinj' hsat' _ hL y₁ (W.π₀ • m₁)
      ⟨by rw [← hy₁'] at hn₁; exact hn₁, m₁, hm₁, rfl⟩ ⟨w, hw⟩
  rw [lifta_JSet_eq, zero_add, liftb_ns] at ha hb
  have ha' : W.map ι a = y₁' - (PD.p ^ eUA PD.p (Mmax n Mi) (JSet jumps (Mmax n Mi)) : ℕ) • y₁ := ha
  have hb' : W.map ι b =
      z₁' - (PD.p ^ eUA PD.p (Mmax n Mi) (JSet jumps (Mmax n Mi)) : ℕ) • (W.π₀ • m₁) := hb
  refine ⟨y₁', z₁', hy₁Q, hz₁X, (liftb_mem_Z1D W T₁ y₁' z₁').2 hd₁, ?_, ?_⟩
  · have h0 := hπι a
    rw [ha', map_sub, map_nsmul, hπy₁, sub_eq_zero] at h0
    rw [h0, smul_smul, ← pow_add, add_comm]
  · have h0 := hπι b
    rw [hb', map_sub, map_nsmul, hπz₁, sub_eq_zero] at h0
    rw [h0, smul_smul, ← pow_add, add_comm]

/- English proof (translation)
Use `liftb_neZero W` as an intermediate fact. Introduce `hA T₁ T₂ F Mi hi hS hJ1`. Establish `hs : W.s = 1` using `hA.2.1`. Establish `hp2 : PD.p ≠ 2` using `hA.2.2`. Rewrite `hv` using `[hs]`.

Take `⟨c1, c2, hOnto⟩` from `hS`. Take `⟨T₀, ι, hses, c0⟩` from `hKer T₁ T₂ F ⟨c1, c2, hOnto⟩`. Establish `hJ` using `hJmp T₀ T₁ T₂ ι F hses c0 c1 c2`. Establish `hJ0 : JumpsLet W T₀ Mi hi` using `fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inl ha))`. Establish `hJ2 : JumpsLet W T₂ Mi hi` using `fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inr ha))`.

Establish `hc0` using `h2c T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)`. Establish `hc1` using `h2c T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)`. Establish `hd` using `h2d T₀ T₁ T₂ ι F Mi hi c0 c1 c2 (liftb_jl W T₁ Mi hi hJ1)`. Rewrite `hc0`, `hc1`, `hd` using `[liftb_mx_eq]`. Establish `hQ` using `hc0.1`.

Establish `gb₀` using `liftb_good_of W T₀ c0 Mi hi (h2 T₀ c0) (h5 T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)) hQ`. Establish `gb₁` using `liftb_good_of W T₁ c1 Mi hi (h2 T₁ c1) (h5 T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)) hQ`. Establish `h90` using `uniformizer_ring_and_module_clauses W h9 hA T₀ c0`. Establish `R` using `lifta_ring_of W h90.1`. Establish `g₀` using `lifta_good_of W R hs T₀ _ gb₀ h90.2`.

Establish `g₁` using `lifta_good_of W R hs T₁ _ gb₁ (uniformizer_ring_and_module_clauses W h9 hA T₁ c1).2`. Establish `hcard : W.DelF.card = PD.p - 1`. Rewrite using `[(h9 T₀ c0 hs hp2).1, finrank_eq_one_case_A W hA, Nat.div_one]`. Take `⟨d, hd1⟩` from `lifta_exists_d W hp hcard`. Establish `hE` using `hLeft T₀ T₁ T₂ ι F hses`.

Establish `hsat` using `(h6.2.2 T₀ T₁ T₂ ι F c0 c1 c2 hses).2.2.2.1`. Establish `hCKN : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁, W.map F x = (PD.p ^ (eWA PD.p (Hmax n Mi hi)) : ℕ) • y`. Introduce `y hy`. Take `⟨x, hx, hxe⟩` from `liftb_kills_all W F _ (hWA hA T₁ T₂ F Mi hi ⟨c1, c2, hOnto⟩ hJ1) y hy`. Conclude with `⟨x, hx, by rw [hxe, lp, liftb_ns]⟩`.

Establish `hL` using `lqa_lifts W hp hA u hu hv h90.1 ι F Mi hi g₀ g₁ c2 hE.1 hE.2 hsat (eWA PD.p (Hmax n Mi hi)) hses hd d hd1 h90.2 (lifta_cokerΔ W F d hd1 _ hCKN) c0 hJ0 hD (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (lifta_jumpSet_mono W T₀ T₁ _ _ (fun τ a ha => (hJ τ a).2 (Or.inl ha))) (hStr hA T₀ c0) …`. Apply `liftb_LiftF_of PD F` to reduce the goal to its premises. Introduce `κ hκ`. Take `⟨c, hc, hcf, rfl⟩` from `(liftb_mem_H1fT PD T₂ κ).1 hκ`. Take `⟨Tp, ι', π', cp, hext⟩` from `hExt T₂ c c2 hcf`.

Take `⟨cone, hone0, e, he, hspan, hφe, hγe⟩` from `hOne`. Establish `hJp'` using `hJmp T₂ Tp W.one ι' π' hext.1 c2 cp cone`. Establish `hJp : JumpsLet W Tp Mi hi`. Introduce `i τ hτ a ha`. Break down `(hJp' τ a).1 ha with h | h` into its components or cases.

Conclude with `hJ2 i τ hτ a h`. Rewrite using `[hone0 τ a h]`. Conclude with `⟨by simp, by simp⟩`. Establish `hImg : InImgA W π' (eWA PD.p (Hmax n Mi hi))`. Take `⟨x, hx, hxe⟩` from `liftb_kills_all W π' _ (hWA hA Tp W.one π' Mi hi ⟨cp, cone, hext.1.2.2.1⟩ hJp) e he`.

Conclude with `⟨e, he, hspan, hφe, hγe, x, hx, by rw [hxe, lp, liftb_ns, liftb_ns]⟩`. Take `⟨y, z, h, hy, hz, hcl⟩` from `hExtC hA T₂ Tp ι' π' Mi hi c2 cp hJ2 c hc hext _ hImg`. Establish `hΔ` using `((lifta_mem_Z1DΔ W T₂ y z).1 h).2`. Establish `hyΔ : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₂` using `⟨hy, fun δ hδ => by`. Rewrite using `[gammaD_semilinear, (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) _) δ hδ, (hΔ δ hδ).1]⟩`.

Take `⟨y₁, z₁, hy₁, ⟨m₁, hm₁, hz₁⟩, h₁, e1, e2⟩` from `hL y z hyΔ hz (Formalism.MainNotions.CrystallineLiftingBounds.invariant_cocycle_le_gamma_cocycle W hs hp2 T₂ h)`. Establish `hy₁Δ` using `lifta_inv_of_q W R T₁ _ y₁ hy₁.2`. Establish `hz₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ z₁ = z₁`. Rewrite using `[hz₁]`. Conclude with `(invariant_smul_mem_invariants' W T₁ W.π₀ R.πΔ m₁ hm₁).2`.

Establish `h₁Δ : (y₁, z₁) ∈ W.wachCocyclesDelta T₁`. Use `(lifta_mem_Z1DΔ W T₁ y₁ z₁).2 ⟨?_, fun δ hδ => ⟨hy₁Δ δ hδ, hz₁Δ δ hδ⟩⟩` and prove the remaining obligations. Rewrite using `[W.gamK_eq_one hs hp2]`. Conclude with `h₁`. Take `⟨m₁X, hm₁X, hm₁Xe⟩` from `lifta_π₀_X W R hs T₁ m₁ hm₁.1`.

Establish `hf₁` using `(hc1.2 y₁ z₁ ((lifta_Qq W R hs T₁ _ y₁).2 hy₁.1) ⟨m₁X, hm₁X, by rw [hz₁]; exact hm₁Xe⟩ h₁).1`. Use `⟨W.clK T₁ ⟨(y₁, z₁), h₁Δ⟩, (h2b T₁ c1 _).2 ?_, ?_⟩` and prove the remaining obligations. Establish `hr` using `hRes hs hp2 T₁ ⟨(y₁, z₁), h₁Δ⟩`. Conclude with `hr.symm ▸ hf₁`. Establish `hN` using `hNat hs hp2 F ⟨(y₁, z₁), h₁Δ⟩ ((PD.p ^ (eWA PD.p (Hmax n Mi hi) + eUA PD.p (Mmax n Mi) (JSet (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (Mmax n Mi))) : ℕ) • (⟨(y, z), h⟩ : ↥(W.wachCocyclesDelta T₂))) (by`.

Rewrite using `[e1, e2]`. Use the proof step `rfl)`. Use `Eq.trans hN ?_` and prove the remaining obligations. Use `Eq.trans (map_nsmul (W.clK T₂) _ _) ?_` and prove the remaining obligations. Use `Eq.trans (congrArg _ hcl) ?_` and prove the remaining obligations.

Rewrite using `[← liftb_ns (R := O), smul_smul, ← pow_add]`. Use `congr 2`. Simplify using `only [ePA]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coreLiftA_of' (W : LocWach PD LL O v n) (hp : PD.p = ℓ) (u : ℤ_[ℓ]ˣ)
    (hu : algebraMap ℤ_[ℓ] O (u : ℤ_[ℓ]) = ((W.χΓ W.gam : Oˣ) : O))
    (hv : PadicInt.valuation ((u : ℤ_[ℓ]) - 1) = W.s)
    (h2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h2b : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexSecondProperty W) (h2c : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexThirdProperty W)
    (h2d : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFourthProperty W) (hExtC : coreExtΔ W) (hD : coreDss W)
    (hNat : W.s = 1 → PD.p ≠ 2 → W.ClKNat) (hRes : Formalism.MainNotions.CrystallineLiftingBounds.coreResK W)
    (hJmp : Formalism.MainNotions.CrystallineLiftingBounds.coreJumps PD LL O) (hWA : coreWA W)
    (hKer : liftb_HKer W) (hLeft : lqa_HLeft W) (hStr : lifta_HStr W) (hExt : liftb_HExt W)
    (hOne : liftb_HOne W) : coreLiftA W := by
  have := liftb_neZero W
  intro hA T₁ T₂ F Mi hi hS hJ1
  have hs : W.s = 1 := hA.2.1
  have hp2 : PD.p ≠ 2 := hA.2.2
  rw [hs] at hv
  obtain ⟨c1, c2, hOnto⟩ := hS
  obtain ⟨T₀, ι, hses, c0⟩ := hKer T₁ T₂ F ⟨c1, c2, hOnto⟩
  have hJ := hJmp T₀ T₁ T₂ ι F hses c0 c1 c2
  have hJ0 : JumpsLet W T₀ Mi hi := fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inl ha))
  have hJ2 : JumpsLet W T₂ Mi hi := fun i τ hτ a ha => hJ1 i τ hτ a ((hJ τ a).2 (Or.inr ha))
  have hc0 := h2c T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)
  have hc1 := h2c T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)
  have hd := h2d T₀ T₁ T₂ ι F Mi hi c0 c1 c2 (liftb_jl W T₁ Mi hi hJ1)
  rw [liftb_mx_eq] at hc0 hc1 hd
  have hQ := hc0.1
  have gb₀ := liftb_good_of W T₀ c0 Mi hi (h2 T₀ c0) (h5 T₀ Mi hi c0 (liftb_jl W T₀ Mi hi hJ0)) hQ
  have gb₁ := liftb_good_of W T₁ c1 Mi hi (h2 T₁ c1) (h5 T₁ Mi hi c1 (liftb_jl W T₁ Mi hi hJ1)) hQ
  have h90 := uniformizer_ring_and_module_clauses W h9 hA T₀ c0
  have R := lifta_ring_of W h90.1
  have g₀ := lifta_good_of W R hs T₀ _ gb₀ h90.2
  have g₁ := lifta_good_of W R hs T₁ _ gb₁ (uniformizer_ring_and_module_clauses W h9 hA T₁ c1).2
  have hcard : W.DelF.card = PD.p - 1 := by
    rw [(h9 T₀ c0 hs hp2).1, finrank_eq_one_case_A W hA, Nat.div_one]
  obtain ⟨d, hd1⟩ := lifta_exists_d W hp hcard
  have hE := hLeft T₀ T₁ T₂ ι F hses
  have hsat := (h6.2.2 T₀ T₁ T₂ ι F c0 c1 c2 hses).2.2.2.1
  have hCKN : ∀ y ∈ W.N T₂, ∃ x ∈ W.N T₁,
      W.map F x = (PD.p ^ (eWA PD.p (Hmax n Mi hi)) : ℕ) • y := by
    intro y hy
    obtain ⟨x, hx, hxe⟩ := liftb_kills_all W F _ (hWA hA T₁ T₂ F Mi hi ⟨c1, c2, hOnto⟩ hJ1) y hy
    exact ⟨x, hx, by rw [hxe, lp, liftb_ns]⟩
  have hL := lqa_lifts W hp hA u hu hv h90.1 ι F Mi hi g₀ g₁ c2 hE.1 hE.2 hsat
    (eWA PD.p (Hmax n Mi hi)) hses hd d hd1 h90.2 (lifta_cokerΔ W F d hd1 _ hCKN) c0 hJ0 hD
    (jumpSet W T₁ (Mmax n Mi) (Mmax n hi))
    (lifta_jumpSet_mono W T₀ T₁ _ _ (fun τ a ha => (hJ τ a).2 (Or.inl ha))) (hStr hA T₀ c0) (h6.1 T₀ c0)
  apply liftb_LiftF_of PD F
  intro κ hκ
  obtain ⟨c, hc, hcf, rfl⟩ := (liftb_mem_H1fT PD T₂ κ).1 hκ
  obtain ⟨Tp, ι', π', cp, hext⟩ := hExt T₂ c c2 hcf
  obtain ⟨cone, hone0, e, he, hspan, hφe, hγe⟩ := hOne
  have hJp' := hJmp T₂ Tp W.one ι' π' hext.1 c2 cp cone
  have hJp : JumpsLet W Tp Mi hi := by
    intro i τ hτ a ha
    rcases (hJp' τ a).1 ha with h | h
    · exact hJ2 i τ hτ a h
    · rw [hone0 τ a h]
      exact ⟨by simp, by simp⟩
  have hImg : InImgA W π' (eWA PD.p (Hmax n Mi hi)) := by
    obtain ⟨x, hx, hxe⟩ := liftb_kills_all W π' _
      (hWA hA Tp W.one π' Mi hi ⟨cp, cone, hext.1.2.2.1⟩ hJp) e he
    exact ⟨e, he, hspan, hφe, hγe, x, hx, by rw [hxe, lp, liftb_ns, liftb_ns]⟩
  obtain ⟨y, z, h, hy, hz, hcl⟩ := hExtC hA T₂ Tp ι' π' Mi hi c2 cp hJ2 c hc hext _ hImg
  have hΔ := ((lifta_mem_Z1DΔ W T₂ y z).1 h).2
  have hyΔ : qp W ^ (Mmax n Mi) • y ∈ W.NΔ T₂ := ⟨hy, fun δ hδ => by
    rw [gammaD_semilinear, (W.AΔ.pow_mem (lifta_qΔ W R.πΔ) _) δ hδ, (hΔ δ hδ).1]⟩
  obtain ⟨y₁, z₁, hy₁, ⟨m₁, hm₁, hz₁⟩, h₁, e1, e2⟩ :=
    hL y z hyΔ hz (Formalism.MainNotions.CrystallineLiftingBounds.invariant_cocycle_le_gamma_cocycle W hs hp2 T₂ h)
  have hy₁Δ := lifta_inv_of_q W R T₁ _ y₁ hy₁.2
  have hz₁Δ : ∀ δ ∈ W.DelF, W.γD T₁ δ z₁ = z₁ := by
    rw [hz₁]
    exact (invariant_smul_mem_invariants' W T₁ W.π₀ R.πΔ m₁ hm₁).2
  have h₁Δ : (y₁, z₁) ∈ W.wachCocyclesDelta T₁ := by
    refine (lifta_mem_Z1DΔ W T₁ y₁ z₁).2 ⟨?_, fun δ hδ => ⟨hy₁Δ δ hδ, hz₁Δ δ hδ⟩⟩
    rw [W.gamK_eq_one hs hp2]
    exact h₁
  obtain ⟨m₁X, hm₁X, hm₁Xe⟩ := lifta_π₀_X W R hs T₁ m₁ hm₁.1
  have hf₁ := (hc1.2 y₁ z₁ ((lifta_Qq W R hs T₁ _ y₁).2 hy₁.1)
    ⟨m₁X, hm₁X, by rw [hz₁]; exact hm₁Xe⟩ h₁).1
  refine ⟨W.clK T₁ ⟨(y₁, z₁), h₁Δ⟩, (h2b T₁ c1 _).2 ?_, ?_⟩
  · have hr := hRes hs hp2 T₁ ⟨(y₁, z₁), h₁Δ⟩
    exact hr.symm ▸ hf₁
  have hN := hNat hs hp2 F ⟨(y₁, z₁), h₁Δ⟩
    ((PD.p ^ (eWA PD.p (Hmax n Mi hi) + eUA PD.p (Mmax n Mi)
      (JSet (jumpSet W T₁ (Mmax n Mi) (Mmax n hi)) (Mmax n Mi))) : ℕ) •
        (⟨(y, z), h⟩ : ↥(W.wachCocyclesDelta T₂)))
    (by
      rw [e1, e2]
      rfl)
  refine Eq.trans hN ?_
  refine Eq.trans (map_nsmul (W.clK T₂) _ _) ?_
  refine Eq.trans (congrArg _ hcl) ?_
  rw [← liftb_ns (R := O), smul_smul, ← pow_add]
  congr 2
  simp only [ePA]
  ring

end LqaLocal

/- English proof (translation)
Introduce `l _ K s LL h`. Take `⟨z, hz, hzv⟩` from `gam_zl (P := D.loc l) (H := HW l) h`. Conclude with `coreLiftA_of' (ℓ := l) ((HW l).W K s LL h) ((D.loc l).PD_p K) z hz (by rw [(HW l).W_s]; exact hzv) (a2 l K s LL h) (a5 l K s LL h) (a6 l K s LL h) (a9 l K s LL h) (a13 l K s LL h) (a14 l K s LL h) (a15 l K s LL h) (a18 l K s LL h) (a19 l K s LL h) (fun h1 h2 => (a21 l K s LL h).2 …`.
-/
theorem lifting_case_A_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a2 : adm2 D HW F) (a5 : adm5 D HW F) (a6 : adm6 D HW F) (a9 : adm9 D HW F)
    (a13 : adm13 D HW F) (a14 : adm14 D HW F) (a15 : adm15 D HW F) (a18 : adm18 D HW F) (a19 : adm19 D HW F)
    (a21 : Formalism.MainNotions.CrystallineLiftingBounds.adm21 D HW F) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F) (a23 : Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F)
    (hWA : WachKillsCaseA D HW F) : LiftTheoremCaseA D HW F := by
  intro l _ K s LL h
  obtain ⟨z, hz, hzv⟩ := gam_zl (P := D.loc l) (H := HW l) h
  exact coreLiftA_of' (ℓ := l) ((HW l).W K s LL h) ((D.loc l).PD_p K) z hz
    (by rw [(HW l).W_s]; exact hzv) (a2 l K s LL h) (a5 l K s LL h) (a6 l K s LL h)
    (a9 l K s LL h) (a13 l K s LL h) (a14 l K s LL h) (a15 l K s LL h) (a18 l K s LL h)
    (a19 l K s LL h)
    (fun h1 h2 => (a21 l K s LL h).2 (by rw [← (HW l).W_s K s LL h]; exact h1)
      (by rw [← (D.loc l).PD_p K]; exact h2))
    (Formalism.MainNotions.CrystallineLiftingBounds.resK_holds D HW F l K s LL h) (a23 l K LL) (hWA l K s LL h) (lker_HKer_D D HW F a22 l K s LL h)
    (fun T₀ T₁ T₂ ι π hses => ⟨linj_map_inj _ ((F l).E K s LL h).tie ι π hses,
      linj_map_zero _ ((F l).E K s LL h).tie ι π hses⟩) (hstr_A D HW F a9 l K s LL h)
    (liftb_HExt_holds D HW F l K s LL h) (liftb_HOne_holds D HW F l K s LL h)

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.LiftingTheory

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

/- English proof (translation)
The claim follows from `opnJumpsQuot_of D HW F a23 (fun l _ K s LL h => lker_HKer_D D HW F a22 l K s LL h)`.
-/
theorem opnJumpsQuot_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (a22 : adm22 D HW F) (a23 : adm23 D HW F) : opnJumpsQuot D HW F :=
  opnJumpsQuot_of D HW F a23 (fun l _ K s LL h => lker_HKer_D D HW F a22 l K s LL h)

/- English proof (translation)
Take `⟨a1, a2, -, -, a5, a6, -, -, a9, -, a11, -, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22, a23⟩` from `h`. Establish `hB : LiftTheoremCaseB D HW F` using `lifting_case_B_of_hypotheses D HW F a1 a2 a5 a6 a11 a13 a14 a15 a17 a21 a22 a23 (wach_statement_case_B D HW F a2 a16)`. Establish `hA : LiftTheoremCaseA D HW F` using `lifting_case_A_of_admitted D HW F a2 a5 a6 a9 a13 a14 a15 a18 a19 a21 a22 a23 (wach_statement_case_A D HW F a9 a16)`. Conclude with `⟨hA, hB, lifting_bracket_units_times_powers D HW F, lifting_exponent_shapes D HW F, lifting_descent_to_subfields D HW F hA hB a20⟩`.
-/
theorem lifting_all_parts_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) : LiftTheoremAllCases D HW F 23 32 32 := by
  obtain ⟨a1, a2, -, -, a5, a6, -, -, a9, -, a11, -, a13, a14, a15, a16, a17, a18, a19, a20, a21, a22,
    a23⟩ := h
  have hB : LiftTheoremCaseB D HW F := lifting_case_B_of_hypotheses D HW F a1 a2 a5 a6 a11 a13 a14 a15 a17 a21 a22 a23
    (wach_statement_case_B D HW F a2 a16)
  have hA : LiftTheoremCaseA D HW F := lifting_case_A_of_admitted D HW F a2 a5 a6 a9 a13 a14 a15 a18 a19 a21 a22 a23
    (wach_statement_case_A D HW F a9 a16)
  exact ⟨hA, hB, lifting_bracket_units_times_powers D HW F, lifting_exponent_shapes D HW F, lifting_descent_to_subfields D HW F hA hB a20⟩

/- English proof (translation)
Establish `a9 : adm9 D HW F` using `h.2.2.2.2.2.2.2.2.1`. Establish `a22 : adm22 D HW F` using `h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `a23 : adm23 D HW F` using `h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2`. Establish `hW` using `wach_second_and_result_of_admitted D HW F Cm h (opnJumpsQuot_holds D HW F a22 a23)`. Conclude with `⟨lattice_clause_every_situation D HW F, wach_statement_of_admitted D HW F Cm h, wach_first_clause_of_admitted D HW F Cm h, hW.1, hW.2, gamma_equation_clause_of_uniformizer D HW F a9, truncation_of_uniformizer_clause D HW F a9, lifting_bracket_units_times_powers D HW F, lifting_ex …`.
-/
theorem local_parts_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) :
    ConclusionL D HW F ∧ ConclusionW D HW F ∧ WachAnnihilatorAll D HW F ∧ WachExponentRecursionAll D HW F ∧ WachResultConstant D HW F 10 ∧ ConclusionH D HW F ∧ ExistsUnitClasses D HW F ∧ LiftBracketR D HW F ∧
      LiftExponentShapes D HW F 23 32 32 := by
  have a9 : adm9 D HW F := h.2.2.2.2.2.2.2.2.1
  have a22 : adm22 D HW F := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have a23 : adm23 D HW F := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hW := wach_second_and_result_of_admitted D HW F Cm h (opnJumpsQuot_holds D HW F a22 a23)
  exact ⟨lattice_clause_every_situation D HW F, wach_statement_of_admitted D HW F Cm h, wach_first_clause_of_admitted D HW F Cm h, hW.1, hW.2, gamma_equation_clause_of_uniformizer D HW F a9,
    truncation_of_uniformizer_clause D HW F a9, lifting_bracket_units_times_powers D HW F, lifting_exponent_shapes D HW F⟩

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩` from `local_parts_of_admitted D HW F Cm h`. Conclude with `⟨h1, h2, h3, h4, h5, h6, h7, lifting_all_parts_of_admitted D HW F Cm h⟩`.
-/
theorem local_theory_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) : aux₃ D HW F 10 23 32 32 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ := local_parts_of_admitted D HW F Cm h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, lifting_all_parts_of_admitted D HW F Cm h⟩

/- English proof (translation)
Introduce `h` and use `local_theory_of_admitted D HW F Cm h`.
-/
theorem frobenius_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Stmt D HW F Cm 10 23 32 32 := fun h => local_theory_of_admitted D HW F Cm h

/- English proof (translation)
Assemble the required witnesses or components as `⟨10, 23, 32, 32, fun D HW F Cm => frobenius_lifting D HW F Cm⟩`.
-/
theorem local_theory_closed_form : RealisationStatementAll := ⟨10, 23, 32, 32, fun D HW F Cm => frobenius_lifting D HW F Cm⟩

end Formalism.MainNotions.LiftingTheory

namespace Formalism.MainNotions.CrystallineLiftingBounds

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

/- English proof (translation)
The claim follows from `h`.
-/
theorem admitted_iff_base_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) : Formalism.MainNotions.LiftingTheory.admitted D HW F Cm := h

/- English proof (translation)
The claim follows from `Formalism.MainNotions.LiftingTheory.lifting_all_parts_of_admitted D HW F Cm (admitted_iff_base_admitted D HW F Cm h)`.
-/
theorem lifting_theorem_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) : Conclusion2 D HW F 23 32 32 :=
  Formalism.MainNotions.LiftingTheory.lifting_all_parts_of_admitted D HW F Cm (admitted_iff_base_admitted D HW F Cm h)

/- English proof (translation)
Assemble the required witnesses or components as `⟨wach_lemma_of_admitted D HW F Cm h, lifting_theorem_of_admitted D HW F Cm h⟩`.
-/
theorem local_theory_of_admitted (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (h : admitted D HW F Cm) : aux₃ D HW F 23 32 32 :=
  ⟨wach_lemma_of_admitted D HW F Cm h, lifting_theorem_of_admitted D HW F Cm h⟩

/- English proof (translation)
Introduce `h` and use `local_theory_of_admitted D HW F Cm h`.
-/
theorem frobenius_lifting (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) : Stmt D HW F Cm 23 32 32 := fun h => local_theory_of_admitted D HW F Cm h

end Formalism.MainNotions.CrystallineLiftingBounds
