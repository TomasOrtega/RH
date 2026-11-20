import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.GramJoint
import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.LocalToGlobal.SiegelLatticeTheory.EFSymmCont

noncomputable section

open scoped Classical BigOperators

namespace Formalism.L2.SG.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef
  Formalism.L2.SG.Saturated Formalism.L2.SG.TermLoc ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable (D : D7)

def LocEqC (Z : LocDat D) : Prop :=
  ∀ (p : PlF D) (A B : Submodule (𝓞 D.host.E) (VS D).V), A.FG → B.FG →
    (lattice₂ D Z.M p A = lattice₂ D Z.M p B ↔
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal →
        (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal A = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B))

def LocSatC (Z : LocDat D) : Prop :=
  ∀ (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (W : Submodule D.host.E (VS D).V), Λ.FG →
    (lattice₂ D Z.M p (Λ ⊓ toO (VS D) W) : Set (Vp D p)) =
      (lattice₂ D Z.M p Λ : Set (Vp D p)) ∩ Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (W : Set (VS D).V))

def LocDiffC (Z : LocDat D) : Prop :=
  ∀ (p : PlF D) (a : Fin (D.R.rS + 1)),
    Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E))) =
    Submodule.span (Z.M p).L.O {frFac Z.δ p a}

def LocUnimodC (Z : LocDat D) : Prop :=
  ∀ (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V), Submodule.IsLattice D.host.E Λ →
    Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ → ∀ x : Vp D p,
      x ∈ lattice₂ D Z.M p Λ ↔ ∀ y ∈ lattice₂ D Z.M p Λ, LocFacts₂ Z.M p x y ∈ (Z.M p).L.O

variable {D}

namespace BBTie

section Basic

variable (Z : LocDat D) (p : PlF D)

/- English proof (translation)
Rewrite using `[(Z.M p).L.O_def]`. Establish `h1 : IsIntegral ℤ ((D.s.atP p).ιE (x : D.host.E))` using `(NumberField.RingOfIntegers.isIntegral_coe x).map (D.s.atP p).ιE.toIntAlgHom`. Conclude with `h1.tower_top`.
-/
theorem bt_iota_int (x : 𝓞 D.host.E) : (D.s.atP p).ιE (x : D.host.E) ∈ (Z.M p).L.O := by
  rw [(Z.M p).L.O_def]
  have h1 : IsIntegral ℤ ((D.s.atP p).ιE (x : D.host.E)) :=
    (NumberField.RingOfIntegers.isIntegral_coe x).map (D.s.atP p).ιE.toIntAlgHom
  exact h1.tower_top

/- English proof (translation)
Rewrite using `[(Z.M p).L.O_def]`. Use `IsIntegral.of_pow (n := 2) two_pos ?_` and prove the remaining obligations. Rewrite using `[sq, hs]`. Conclude with `isIntegral_one`.
-/
theorem bt_sq_one_mem {s : (D.s.atP p).Ep} (hs : s * s = 1) : s ∈ (Z.M p).L.O := by
  rw [(Z.M p).L.O_def]
  refine IsIntegral.of_pow (n := 2) two_pos ?_
  rw [sq, hs]; exact isIntegral_one

/- English proof (translation)
The claim follows from `(algebraMap_smul D.host.E o x).symm`.
-/
theorem bt_smul_O (o : 𝓞 D.host.E) (x : (VS D).V) : o • x = ((o : D.host.E)) • x :=
  (algebraMap_smul D.host.E o x).symm

/- English proof (translation)
Rewrite using `[bt_smul_O, baseChange_smul₂]`. Both sides reduce to the same expression.
-/
theorem bt_bc_smulO (o : 𝓞 D.host.E) (x : (VS D).V) :
    baseChange₂ D p (o • x) = ((⟨(D.s.atP p).ιE (o : D.host.E), bt_iota_int Z p o⟩ : (Z.M p).L.O)) • baseChange₂ D p x := by
  rw [bt_smul_O, baseChange_smul₂]; rfl

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono h)`.
-/
theorem latP_mono {A B : Submodule (𝓞 D.host.E) (VS D).V} (h : A ≤ B) : lattice₂ D Z.M p A ≤ lattice₂ D Z.M p B :=
  Submodule.span_mono (Set.image_mono h)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[lattice₂, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul o y _ hy => rw [bt_bc_smulO Z]`. Conclude with `Submodule.smul_mem _ _ hy`.

Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem latP_span (S : Set (VS D).V) :
    lattice₂ D Z.M p (Submodule.span (𝓞 D.host.E) S) = Submodule.span (Z.M p).L.O (baseChange₂ D p '' S) := by
  apply le_antisymm
  · rw [lattice₂, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul o y _ hy => rw [bt_bc_smulO Z]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[lattice₂, Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add]`.

Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨a, ha, rfl⟩)) (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))`. Conclude with `sup_le (latP_mono Z p le_sup_left) (latP_mono Z p le_sup_right)`.
-/
theorem latP_sup (A B : Submodule (𝓞 D.host.E) (VS D).V) :
    lattice₂ D Z.M p (A ⊔ B) = lattice₂ D Z.M p A ⊔ lattice₂ D Z.M p B := by
  apply le_antisymm
  · rw [lattice₂, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨a, ha, rfl⟩))
      (Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩))
  · exact sup_le (latP_mono Z p le_sup_left) (latP_mono Z p le_sup_right)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`.

Consider the case `zero => simp`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul c y _ hy => rw [baseChange_smul₂]`. Conclude with `Submodule.smul_mem _ _ hy`.

Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span)`.
-/
theorem bt_spanEp_spanE (N : Submodule (𝓞 D.host.E) (VS D).V) :
    Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (Submodule.span D.host.E (N : Set (VS D).V) : Set (VS D).V)) =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (N : Set (VS D).V)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [baseChange_smul₂]; exact Submodule.smul_mem _ _ hy
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

/- English proof (translation)
The claim follows from `Submodule.span_span_of_tower _ _ _`.
-/
theorem bt_spanEp_spanO (S : Set (Vp D p)) :
    Submodule.span (D.s.atP p).Ep (Submodule.span (Z.M p).L.O S : Set (Vp D p)) =
      Submodule.span (D.s.atP p).Ep S :=
  Submodule.span_span_of_tower _ _ _

/- English proof (translation)
Rewrite using `[← bt_spanEp_spanO Z p S]`. Conclude with `Submodule.subset_span`.
-/
theorem bt_spanO_le_spanEp (S : Set (Vp D p)) :
    (Submodule.span (Z.M p).L.O S : Set (Vp D p)) ⊆ Submodule.span (D.s.atP p).Ep S := by
  rw [← bt_spanEp_spanO Z p S]; exact Submodule.subset_span

end Basic

section Bridge

variable (Z : LocDat D) (p : PlF D)

/- English proof (translation)
Establish `key` using `hS p Λ W hΛ`. Establish `hNsub : lattice₂ D Z.M p N ≤ lattice₂ D Z.M p (Λ ⊓ toO (VS D) W)`. Introduce `x hx`. Rewrite using `[← SetLike.mem_coe, key]`. Use `⟨hNΛ hx, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hE]`. Apply `bt_spanO_le_spanEp Z p` to reduce the goal to its premises. Rewrite using `[hO]`. Conclude with `hx`. Unfold `LocNG.BBne`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨v, hv, hvE, hvO⟩ heq`. Rewrite `hv` using `[hL]`. Rewrite `hvO` using `[hO]`. Establish `hv' : v ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) W)`.

Rewrite using `[← SetLike.mem_coe, key]`. Conclude with `⟨hv, hE ▸ hvE⟩`. Rewrite `hv'` using `[heq]`. Conclude with `hvO hv'`. Introduce `hne`.

Establish `hnl : ¬ lattice₂ D Z.M p (Λ ⊓ toO (VS D) W) ≤ lattice₂ D Z.M p N` using `fun h => hne (le_antisymm h hNsub)`. Take `⟨v, hv, hvN⟩` from `SetLike.not_le_iff_exists.1 hnl`. Establish `hv2 : v ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) W) : Set (Vp D p))` using `hv`. Rewrite `hv2` using `[key]`. Use `⟨v, hL ▸ hv2.1, hE ▸ hv2.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[hO]`. Conclude with `hvN`.
-/
theorem bt_bbne_iff (hS : LocSatC D Z) (t : Loc.Term (Vp D p) (Z.M p) D.R.rS)
    (Λ N : Submodule (𝓞 D.host.E) (VS D).V) (W : Submodule D.host.E (VS D).V) (hΛ : Λ.FG)
    (hL : t.abelian₂ = lattice₂ D Z.M p Λ)
    (hO : Submodule.span (Z.M p).L.O (Set.range ((locH Z p).MMfam t)) = lattice₂ D Z.M p N)
    (hE : Submodule.span (D.s.atP p).Ep (Set.range ((locH Z p).MMfam t)) =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (W : Set (VS D).V)))
    (hNΛ : lattice₂ D Z.M p N ≤ lattice₂ D Z.M p Λ) :
    LocNG.BBne (H := locH Z p) t ↔ lattice₂ D Z.M p (Λ ⊓ toO (VS D) W) ≠ lattice₂ D Z.M p N := by
  have key := hS p Λ W hΛ
  have hNsub : lattice₂ D Z.M p N ≤ lattice₂ D Z.M p (Λ ⊓ toO (VS D) W) := by
    intro x hx
    rw [← SetLike.mem_coe, key]
    refine ⟨hNΛ hx, ?_⟩
    rw [← hE]
    apply bt_spanO_le_spanEp Z p
    rw [hO]; exact hx
  unfold LocNG.BBne
  constructor
  · rintro ⟨v, hv, hvE, hvO⟩ heq
    rw [hL] at hv
    rw [hO] at hvO
    have hv' : v ∈ lattice₂ D Z.M p (Λ ⊓ toO (VS D) W) := by
      rw [← SetLike.mem_coe, key]; exact ⟨hv, hE ▸ hvE⟩
    rw [heq] at hv'
    exact hvO hv'
  · intro hne
    have hnl : ¬ lattice₂ D Z.M p (Λ ⊓ toO (VS D) W) ≤ lattice₂ D Z.M p N := fun h => hne (le_antisymm h hNsub)
    obtain ⟨v, hv, hvN⟩ := SetLike.not_le_iff_exists.1 hnl
    have hv2 : v ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) W) : Set (Vp D p)) := hv
    rw [key] at hv2
    refine ⟨v, hL ▸ hv2.1, hE ▸ hv2.2, ?_⟩
    rw [hO]; exact hvN

/- English proof (translation)
Rewrite using `[Ne, hE p B N hB hN]`. Use `push Not`. Both sides reduce to the same expression.
-/
theorem bt_glob_iff (hE : LocEqC D Z) (B N : Submodule (𝓞 D.host.E) (VS D).V) (hB : B.FG) (hN : N.FG) :
    (∃ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal ∧
      (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal B ≠ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal N)) ↔
      lattice₂ D Z.M p B ≠ lattice₂ D Z.M p N := by
  rw [Ne, hE p B N hB hN]
  push Not
  rfl

end Bridge

section Places

variable (p : PlF D)

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Conclude with `ringChar.spec _ n`.
-/
theorem bt_natCast_mem_iff (n : ℕ) : ((n : 𝓞 D.host.F) ∈ p.asIdeal) ↔ Loc.resChar p ∣ n := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact ringChar.spec _ n

/- English proof (translation)
Rewrite using `[bt_natCast_mem_iff]`. Use `(D.s.atP p).ellPrime` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce `h`. Break down `(Nat.Prime.eq_one_or_self_of_dvd hn _ h) with h1 | h1` into its components or cases.

Conclude with `absurd h1 (Fact.out : (Loc.resChar p).Prime).one_lt.ne'`. Conclude with `h1`. Introduce `h`. Rewrite using `[h]`.
-/
theorem bt_natCast_prime_mem_iff {n : ℕ} (hn : n.Prime) : ((n : 𝓞 D.host.F) ∈ p.asIdeal) ↔ Loc.resChar p = n := by
  rw [bt_natCast_mem_iff]
  have := (D.s.atP p).ellPrime
  constructor
  · intro h
    rcases (Nat.Prime.eq_one_or_self_of_dvd hn _ h) with h1 | h1
    · exact absurd h1 (Fact.out : (Loc.resChar p).Prime).one_lt.ne'
    · exact h1
  · intro h; rw [h]

/- English proof (translation)
Establish `e : ((gS D : ℕ) : 𝓞 D.host.E) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((gS D : ℕ) : 𝓞 D.host.F)` using `(map_natCast _ _).symm`. Rewrite using `[e, ← Ideal.mem_comap, hP, gS, Nat.cast_mul]`. Rewrite using `[p.isPrime.mul_mem_iff_mem_or_mem, bt_natCast_prime_mem_iff p (D.host.g_prime 0), bt_natCast_prime_mem_iff p (D.host.g_prime 1)]`. Simplify using the standard rewrite rules.
-/
theorem bt_g_mem_iff (P : HeightOneSpectrum (𝓞 D.host.E))
    (hP : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal) :
    ((gS D : 𝓞 D.host.E) ∈ P.asIdeal) ↔ Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
  have e : ((gS D : ℕ) : 𝓞 D.host.E) = algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((gS D : ℕ) : 𝓞 D.host.F) :=
    (map_natCast _ _).symm
  rw [e, ← Ideal.mem_comap, hP, gS, Nat.cast_mul]
  rw [p.isPrime.mul_mem_iff_mem_or_mem, bt_natCast_prime_mem_iff p (D.host.g_prime 0),
    bt_natCast_prime_mem_iff p (D.host.g_prime 1)]
  simp

end Places

section Units

variable (Z : LocDat D) (p : PlF D)

def btT : (D.s.atP p).Ep :=
  algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E)

/- English proof (translation)
Unfold `gpart`. Establish `h0` using `(D.host.g_prime 0).ne_zero`. Establish `h1` using `(D.host.g_prime 1).ne_zero`. Apply the tactic sequence `split_ifs <;> simp [h0, h1]`.
-/
theorem bt_gpart_ne (p : PlF D) : (gpart p : ℚ) ≠ 0 := by
  unfold gpart
  have h0 := (D.host.g_prime 0).ne_zero
  have h1 := (D.host.g_prime 1).ne_zero
  split_ifs <;> simp [h0, h1]

/- English proof (translation)
Establish `hg : (gS D : ℚ) ≠ 0`. Simplify using `[gS, (D.host.g_prime 0).ne_zero, (D.host.g_prime 1).ne_zero]`. Establish `: uP p ≠ 0` using `div_ne_zero (bt_gpart_ne p) hg`. Conclude with `this` after adjusting the coercions.
-/
theorem uP_ne : (uP p : D.host.E) ≠ 0 := by
  have hg : (gS D : ℚ) ≠ 0 := by
    simp [gS, (D.host.g_prime 0).ne_zero, (D.host.g_prime 1).ne_zero]
  have : uP p ≠ 0 := div_ne_zero (bt_gpart_ne p) hg
  exact_mod_cast this

/- English proof (translation)
The claim follows from `isUnit_iff_exists_inv.2 ⟨(D.s.atP p).ιE x⁻¹, by rw [← map_mul, mul_inv_cancel₀ hx, map_one]⟩`.
-/
theorem bt_iota_unit {x : D.host.E} (hx : x ≠ 0) : IsUnit ((D.s.atP p).ιE x) :=
  isUnit_iff_exists_inv.2 ⟨(D.s.atP p).ιE x⁻¹, by rw [← map_mul, mul_inv_cancel₀ hx, map_one]⟩

/- English proof (translation)
The claim follows from `isUnit_iff_exists_inv.2 ⟨algebraMap _ _ x⁻¹, by rw [← map_mul, mul_inv_cancel₀ hx, map_one]⟩`.
-/
theorem bt_alg_unit {x : (D.s.atP p).Fp} (hx : x ≠ 0) :
    IsUnit (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep x) :=
  isUnit_iff_exists_inv.2 ⟨algebraMap _ _ x⁻¹, by rw [← map_mul, mul_inv_cancel₀ hx, map_one]⟩

/- English proof (translation)
The claim follows from `(bt_alg_unit p (Z.agree p).2.1).mul (bt_iota_unit p (uP_ne p))`.
-/
theorem bt_T_unit : IsUnit (btT Z p) :=
  (bt_alg_unit p (Z.agree p).2.1).mul (bt_iota_unit p (uP_ne p))

/- English proof (translation)
Unfold `frFac`. Establish `e : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^ (D.R.rS - a.val) = (((bt_T_unit Z p).unit ^ (D.R.rS - a.val) : (D.s.atP p).Epˣ) : (D.s.atP p).Ep)`. Rewrite using `[Units.val_pow_eq_pow_val, IsUnit.unit_spec]`. Both sides reduce to the same expression. Rewrite using `[e, Ring.inverse_unit, inv_pow]`.
-/
theorem bt_frFac_eq (a : Fin (D.R.rS + 1)) :
    frFac Z.δ p a = (((bt_T_unit Z p).unit⁻¹ ^ (D.R.rS - a.val) : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) := by
  unfold frFac
  have e : (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (Z.δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
      (D.R.rS - a.val) = (((bt_T_unit Z p).unit ^ (D.R.rS - a.val) : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) := by
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]; rfl
  rw [e, Ring.inverse_unit, inv_pow]

/- English proof (translation)
Rewrite using `[bt_frFac_eq]`. Simplify using the standard rewrite rules.
-/
theorem bt_frFac_last : frFac Z.δ p (Fin.last D.R.rS) = 1 := by
  rw [bt_frFac_eq]; simp

/- English proof (translation)
Rewrite using `[bt_frFac_eq]`. Conclude with `Units.isUnit _`.
-/
theorem bt_frFac_unit (a : Fin (D.R.rS + 1)) : IsUnit (frFac Z.δ p a) := by
  rw [bt_frFac_eq]; exact Units.isUnit _

/- English proof (translation)
Rewrite using `[bt_frFac_eq, bt_frFac_eq]`. Use `set U := (bt_T_unit Z p).unit`. Establish `hU : (U : (D.s.atP p).Ep) = btT Z p` using `IsUnit.unit_spec _`. Rewrite using `[← hU, ← Units.val_pow_eq_pow_val, ← Units.val_mul]`. Use `congr 1`.

Establish `hb` using `b.isLt`. Establish `hcb : c.val ≤ b.val` using `h`. Establish `e1 : D.R.rS - c.val = (D.R.rS - b.val) + (b.val - c.val)` using `by omega`. Rewrite using `[e1, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel, one_pow, mul_one]`.
-/
theorem bt_frFac_ratio (c b : Fin (D.R.rS + 1)) (h : c ≤ b) :
    frFac Z.δ p b = frFac Z.δ p c * btT Z p ^ (b.val - c.val) := by
  rw [bt_frFac_eq, bt_frFac_eq]
  set U := (bt_T_unit Z p).unit
  have hU : (U : (D.s.atP p).Ep) = btT Z p := IsUnit.unit_spec _
  rw [← hU, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 1
  have hb := b.isLt
  have hcb : c.val ≤ b.val := h
  have e1 : D.R.rS - c.val = (D.R.rS - b.val) + (b.val - c.val) := by omega
  rw [e1, pow_add, mul_assoc, ← mul_pow, inv_mul_cancel, one_pow, mul_one]

/- English proof (translation)
Establish `hmem : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal)` using `by rwa [bt_natCast_mem_iff]`. Establish `hv : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F (n : 𝓞 D.host.F)) = 1` using `(HeightOneSpectrum.valuation_eq_one_iff_notMem p).2 hmem`. Rewrite `hv` using `[map_natCast]`. Establish `h1 : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp)`. Use `((D.s.atP p).val 1 (n : D.host.F)).2 (by rw [hv, map_one])` as an intermediate fact.

Simplify using `using this`. Establish `hn0 : (n : (D.s.atP p).Fp) ≠ 0`. Use `(D.s.atP p).char0` as an intermediate fact. Establish `: n ≠ 0` using `by rintro rfl; exact hn (dvd_zero _)`. Conclude with `this` after adjusting the coercions.

Establish `hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]`. Rewrite using `[Valuation.mem_integer_iff, ← Valuation.vle_one_iff]`. Conclude with `(ValuativeRel.inv_vle_one hn0).2 h1`. Use `⟨?_, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(Z.M p).L.O_def]`.

Simplify using `using (isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (A := (D.s.atP p).Ep) (x := (n : 𝒪[(D.s.atP p).Fp])))`. Rewrite using `[(Z.M p).L.O_def]`. Establish `: algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹ = algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨_, hinv⟩` using `rfl`. Rewrite using `[this]`. Conclude with `isIntegral_algebraMap`.

Rewrite using `[← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), ← map_mul, inv_mul_cancel₀ hn0, map_one]`.
-/
theorem bt_nat_unit (n : ℕ) (hn : ¬ Loc.resChar p ∣ n) :
    ((n : (D.s.atP p).Ep) ∈ (Z.M p).L.O) ∧ ∃ w ∈ (Z.M p).L.O, w * (n : (D.s.atP p).Ep) = 1 := by
  have hmem : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal) := by rwa [bt_natCast_mem_iff]
  have hv : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F (n : 𝓞 D.host.F)) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem p).2 hmem
  rw [map_natCast] at hv
  have h1 : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp) := by
    have := ((D.s.atP p).val 1 (n : D.host.F)).2 (by rw [hv, map_one])
    simpa using this
  have hn0 : (n : (D.s.atP p).Fp) ≠ 0 := by
    have := (D.s.atP p).char0
    have : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
    exact_mod_cast this
  have hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
    rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff]
    exact (ValuativeRel.inv_vle_one hn0).2 h1
  refine ⟨?_, algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹, ?_, ?_⟩
  · rw [(Z.M p).L.O_def]; simpa using (isIntegral_algebraMap (R := 𝒪[(D.s.atP p).Fp]) (A := (D.s.atP p).Ep) (x := (n : 𝒪[(D.s.atP p).Fp])))
  · rw [(Z.M p).L.O_def]
    have : algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)⁻¹ =
        algebraMap 𝒪[(D.s.atP p).Fp] (D.s.atP p).Ep ⟨_, hinv⟩ := rfl
    rw [this]; exact isIntegral_algebraMap
  · rw [← map_natCast (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep), ← map_mul, inv_mul_cancel₀ hn0, map_one]

end Units

section Spans

variable (Z : LocDat D) (p : PlF D)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.smul_mem _ (⟨u i, hu i⟩ : (Z.M p).L.O) (Submodule.subset_span ⟨i, rfl⟩)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Establish `e : v i = (⟨w i, hw i⟩ : (Z.M p).L.O) • (u i • v i)` using `by show v i = w i • (u i • v i)`. Rewrite using `[smul_smul, huw i, one_smul]`. Rewrite using `[SetLike.mem_coe, e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem bt_span_units {ι : Type*} (u w : ι → (D.s.atP p).Ep) (v : ι → Vp D p)
    (hu : ∀ i, u i ∈ (Z.M p).L.O) (hw : ∀ i, w i ∈ (Z.M p).L.O) (huw : ∀ i, w i * u i = 1) :
    Submodule.span (Z.M p).L.O (Set.range fun i => u i • v i) = Submodule.span (Z.M p).L.O (Set.range v) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ (⟨u i, hu i⟩ : (Z.M p).L.O) (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have e : v i = (⟨w i, hw i⟩ : (Z.M p).L.O) • (u i • v i) := by
      show v i = w i • (u i • v i)
      rw [smul_smul, huw i, one_smul]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Rewrite using `[map_sum]`. Simplify using `only [baseChange_smul₂]`.
-/
theorem bt_bc_sum {ι : Type*} (s : Finset ι) (c : ι → D.host.E) (v : ι → (VS D).V) :
    baseChange₂ D p (∑ i ∈ s, c i • v i) = ∑ i ∈ s, (D.s.atP p).ιE (c i) • baseChange₂ D p (v i) := by
  rw [map_sum]; simp only [baseChange_smul₂]

/- English proof (translation)
Use function extensionality and compare the values at `b`. Simplify using `only [frameAct, Finset.smul_sum, smul_smul, Matrix.mul_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`.

Use `congr 1`. Use `push_cast`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bt_frameAct_comp {n : ℕ} (v : Fin n → (VS D).V) (A B : Matrix (Fin n) (Fin n) (𝓞 D.host.E)) :
    frameAct (frameAct v A) B = frameAct v (A * B) := by
  funext b
  simp only [frameAct, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

/- English proof (translation)
Use function extensionality and compare the values at `b`. Simplify using `[frameAct, Matrix.one_apply]`.
-/
theorem bt_frameAct_one {n : ℕ} (v : Fin n → (VS D).V) : frameAct v 1 = v := by
  funext b
  simp [frameAct, Matrix.one_apply]

/- English proof (translation)
Rewrite using `[frameAct, bt_bc_sum, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hcb : c ≤ b`. Take `⟨k, hk, hkb⟩` from `hφ c b hcb`. Establish `e : φ b • ((D.s.atP p).ιE ((m c b : 𝓞 D.host.E) : D.host.E) • baseChange₂ D p (v c)) = (⟨(D.s.atP p).ιE ((m c b : 𝓞 D.host.E) : D.host.E) * k, Subring.mul_mem _ (bt_iota_int Z p _) hk⟩ : (Z.M p).L.O) • (φ c • baseChange₂ D p (v c))` using `by show _ = ((D.s.atP p).ιE ((m c b : 𝓞 D.host.E) : D.host.E) * k) • (φ c • baseChange₂ D p (v c))`.

Rewrite using `[smul_smul, smul_smul, hkb]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)`.

Rewrite using `[hm c b (lt_of_not_ge hcb)]`. Simplify using the standard rewrite rules.
-/
theorem bt_tri {n : ℕ} (φ : Fin n → (D.s.atP p).Ep)
    (hφ : ∀ c b : Fin n, c ≤ b → ∃ k ∈ (Z.M p).L.O, φ b = k * φ c)
    (v : Fin n → (VS D).V) (m : Matrix (Fin n) (Fin n) (𝓞 D.host.E)) (hm : ∀ a b, b < a → m a b = 0)
    (b : Fin n) :
    φ b • baseChange₂ D p (frameAct v m b) ∈ Submodule.span (Z.M p).L.O (Set.range fun c => φ c • baseChange₂ D p (v c)) := by
  rw [frameAct, bt_bc_sum, Finset.smul_sum]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hcb : c ≤ b
  · obtain ⟨k, hk, hkb⟩ := hφ c b hcb
    have e : φ b • ((D.s.atP p).ιE ((m c b : 𝓞 D.host.E) : D.host.E) • baseChange₂ D p (v c)) =
        (⟨(D.s.atP p).ιE ((m c b : 𝓞 D.host.E) : D.host.E) * k,
          Subring.mul_mem _ (bt_iota_int Z p _) hk⟩ : (Z.M p).L.O) • (φ c • baseChange₂ D p (v c)) := by
      show _ = ((D.s.atP p).ιE ((m c b : 𝓞 D.host.E) : D.host.E) * k) • (φ c • baseChange₂ D p (v c))
      rw [smul_smul, smul_smul, hkb]; congr 1; ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  · rw [hm c b (lt_of_not_ge hcb)]
    simp

/- English proof (translation)
Establish `hbt : ξ.BlockTriangular id` using `fun i j hij => h1 i j hij`. Rewrite using `[Matrix.det_of_isUpperTriangular hbt]`. Simplify using `[h2]`.
-/
theorem bt_unitri_det {n : ℕ} (ξ : Matrix (Fin n) (Fin n) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) : IsUnit ξ.det := by
  have hbt : ξ.BlockTriangular id := fun i j hij => h1 i j hij
  rw [Matrix.det_of_isUpperTriangular hbt]; simp [h2]

/- English proof (translation)
Establish `hinv` using `inv_unitri ξ h1 h2`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `bt_tri Z p φ hφ v _ hinv.1 b`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`. Establish `e : v = frameAct (frameAct v ξ⁻¹) ξ`. Rewrite using `[bt_frameAct_comp, Matrix.nonsing_inv_mul ξ (bt_unitri_det ξ h1 h2), bt_frameAct_one]`. Use `bt_tri Z p φ hφ (frameAct v ξ⁻¹) ξ h1 b` as an intermediate fact.

Rewrite `this` using `[← e]`. Conclude with `this`.
-/
theorem bt_span_tri {n : ℕ} (φ : Fin n → (D.s.atP p).Ep)
    (hφ : ∀ c b : Fin n, c ≤ b → ∃ k ∈ (Z.M p).L.O, φ b = k * φ c)
    (v : Fin n → (VS D).V) (ξ : Matrix (Fin n) (Fin n) (𝓞 D.host.E))
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1) :
    Submodule.span (Z.M p).L.O (Set.range fun b => φ b • baseChange₂ D p (frameAct v ξ⁻¹ b)) =
      Submodule.span (Z.M p).L.O (Set.range fun b => φ b • baseChange₂ D p (v b)) := by
  have hinv := inv_unitri ξ h1 h2
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact bt_tri Z p φ hφ v _ hinv.1 b
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have e : v = frameAct (frameAct v ξ⁻¹) ξ := by
      rw [bt_frameAct_comp, Matrix.nonsing_inv_mul ξ (bt_unitri_det ξ h1 h2), bt_frameAct_one]
    have := bt_tri Z p φ hφ (frameAct v ξ⁻¹) ξ h1 b
    rw [← e] at this
    exact this

/- English proof (translation)
Rewrite using `[← Submodule.span_union]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨i, rfl⟩`.

Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => exact Or.inr rfl`. Consider the case `cast a => exact Or.inl ⟨a, rfl⟩`. Introduce and unpack `(⟨a, rfl⟩ | h)`. Conclude with `⟨_, rfl⟩`.

Conclude with `⟨_, h.symm⟩`.
-/
theorem bt_span_snoc {n : ℕ} (w : Fin (n + 1) → Vp D p) :
    Submodule.span (Z.M p).L.O (Set.range w) =
      Submodule.span (Z.M p).L.O (Set.range fun a : Fin n => w a.castSucc) ⊔
        Submodule.span (Z.M p).L.O {w (Fin.last n)} := by
  rw [← Submodule.span_union]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    induction i using Fin.lastCases with
    | last => exact Or.inr rfl
    | cast a => exact Or.inl ⟨a, rfl⟩
  · rintro (⟨a, rfl⟩ | h)
    · exact ⟨_, rfl⟩
    · exact ⟨_, h.symm⟩

end Spans

section Frames

variable (Z : LocDat D) (p : PlF D)

/- English proof (translation)
Proceed by induction on `hc using Submodule.span_induction with`. Consider the case `mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_smul]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul o x _ hx`. Establish `e : (o • x) • v = o • (x • v)` using `by show ((o : (D.s.atP p).Ep) * x) • v = (o : (D.s.atP p).Ep) • (x • v)`. Rewrite using `[mul_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem bt_smul_mem_span_image (S : Set (D.s.atP p).Ep) (v : Vp D p) {c : (D.s.atP p).Ep}
    (hc : c ∈ Submodule.span (Z.M p).L.O S) :
    c • v ∈ Submodule.span (Z.M p).L.O ((fun s => s • v) '' S) := by
  induction hc using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [add_smul]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx =>
    have e : (o • x) • v = o • (x • v) := by
      show ((o : (D.s.atP p).Ep) * x) • v = (o : (D.s.atP p).Ep) • (x • v)
      rw [mul_smul]
    rw [e]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Rewrite using `[XS, latP_span]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, ⟨a, x, hx, rfl⟩, rfl⟩`. Establish `hmem : (D.s.atP p).ιE x ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a.castSucc}`.

Rewrite using `[← hD p a.castSucc]`. Conclude with `Submodule.subset_span ⟨x, by simpa using hx, rfl⟩`. Take `⟨o, ho⟩` from `Submodule.mem_span_singleton.1 hmem`. Rewrite using `[SetLike.mem_coe, baseChange_smul₂, ← ho]`. Establish `e : (o • frFac Z.δ p a.castSucc) • baseChange₂ D p (F.e a) = o • (frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a))` using `by show ((o : (D.s.atP p).Ep) * frFac Z.δ p a.castSucc) • baseChange₂ D p (F.e a) = (o : (D.s.atP p).Ep) • (frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a))`.

Rewrite using `[mul_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`.

Establish `hmem : frFac Z.δ p a.castSucc ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE '' (((ddS D ^ (-((D.R.rS : ℤ) - (a.castSucc : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E)))`. Rewrite using `[hD p a.castSucc]`. Conclude with `Submodule.subset_span rfl`. Establish `h2` using `bt_smul_mem_span_image Z p _ (baseChange₂ D p (F.e a)) hmem`. Use `Submodule.span_mono ?_ h2` and prove the remaining obligations.

Introduce and unpack `_ ⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Use `⟨x • F.e a, ⟨a, x, by simpa using hx, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[baseChange_smul₂]`.
-/
theorem bt_latP_XS (hD : LocDiffC D Z) {T : D.host.E} (F : FlagG (VS D) D.R.rS T) :
    lattice₂ D Z.M p (XS D F) =
      Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a)) := by
  rw [XS, latP_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, ⟨a, x, hx, rfl⟩, rfl⟩
    have hmem : (D.s.atP p).ιE x ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a.castSucc} := by
      rw [← hD p a.castSucc]
      exact Submodule.subset_span ⟨x, by simpa using hx, rfl⟩
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hmem
    rw [SetLike.mem_coe, baseChange_smul₂, ← ho]
    have e : (o • frFac Z.δ p a.castSucc) • baseChange₂ D p (F.e a) = o • (frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a)) := by
      show ((o : (D.s.atP p).Ep) * frFac Z.δ p a.castSucc) • baseChange₂ D p (F.e a) =
        (o : (D.s.atP p).Ep) • (frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a))
      rw [mul_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have hmem : frFac Z.δ p a.castSucc ∈ Submodule.span (Z.M p).L.O ((D.s.atP p).ιE ''
        (((ddS D ^ (-((D.R.rS : ℤ) - (a.castSucc : ℕ))) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E))) := by
      rw [hD p a.castSucc]; exact Submodule.subset_span rfl
    have h2 := bt_smul_mem_span_image Z p _ (baseChange₂ D p (F.e a)) hmem
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x • F.e a, ⟨a, x, by simpa using hx, rfl⟩, ?_⟩
    rw [baseChange_smul₂]

/- English proof (translation)
Use `set a : Fin (D.R.rS + 1) := ⟨D.R.rS - 1, by omega⟩`. Establish `hfa : frFac Z.δ p a = (((bt_T_unit Z p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep)`. Rewrite using `[bt_frFac_eq]`. Establish `: D.R.rS - a.val = 1` using `by simp [a]; omega`. Rewrite using `[this, pow_one]`.

Establish `hspan` using `hD p a`. Establish `hexp : (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) = -1`. Simplify using `only [a]`. Move the coercions through the operations in `[Nat.cast_sub hr]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hspan` using `[hexp, zpow_neg_one]`. Distinguish the cases in `hdd : ddS D = 0`. It suffices to derive a contradiction. Rewrite `hspan` using `[hdd, inv_zero]`. Establish `h0 : frFac Z.δ p a ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a}` using `Submodule.subset_span rfl`.

Rewrite `h0` using `[← hspan]`. Establish `hsub : ((D.s.atP p).ιE '' (((0 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) : Set D.host.E)) ⊆ {0}`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Establish `: x = 0` using `by simpa using hx`. Simplify using `[this]`.

Establish `h00` using `Submodule.span_mono (R := (Z.M p).L.O) hsub h0`. Rewrite `h00` using `[Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot]`. Conclude with `(bt_frFac_unit Z p a).ne_zero h00`. Establish `h1 : (1 : D.host.E) ∈ ((ddS D)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)`. Rewrite using `[FractionalIdeal.mem_inv_iff hdd]`.

Introduce `y hy`. Rewrite using `[one_mul]`. Conclude with `FractionalIdeal.coeIdeal_le_one hy`. Establish `hmem : (1 : (D.s.atP p).Ep) ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a}`. Rewrite using `[← hspan]`.

Conclude with `Submodule.subset_span ⟨1, h1, map_one _⟩`. Take `⟨o, ho⟩` from `Submodule.mem_span_singleton.1 hmem`. Establish `ho' : (o : (D.s.atP p).Ep) * (((bt_T_unit Z p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = 1`. Rewrite using `[← hfa]`. Conclude with `ho`.

Establish `: (o : (D.s.atP p).Ep) = btT Z p`. Establish `hU : (((bt_T_unit Z p).unit : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = btT Z p` using `IsUnit.unit_spec _`. Rewrite using `[← hU, ← mul_one (o : (D.s.atP p).Ep), ← Units.inv_mul (bt_T_unit Z p).unit, ← mul_assoc, ho', one_mul]`. Rewrite using `[← this]`. Conclude with `o.2`.
-/
theorem bt_T_mem (hD : LocDiffC D Z) (hr : 1 ≤ D.R.rS) : btT Z p ∈ (Z.M p).L.O := by
  set a : Fin (D.R.rS + 1) := ⟨D.R.rS - 1, by omega⟩
  have hfa : frFac Z.δ p a = (((bt_T_unit Z p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) := by
    rw [bt_frFac_eq]
    have : D.R.rS - a.val = 1 := by simp [a]; omega
    rw [this, pow_one]
  have hspan := hD p a
  have hexp : (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))) = -1 := by
    simp only [a]; push_cast [Nat.cast_sub hr]; ring
  rw [hexp, zpow_neg_one] at hspan
  by_cases hdd : ddS D = 0
  · exfalso
    rw [hdd, inv_zero] at hspan
    have h0 : frFac Z.δ p a ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a} := Submodule.subset_span rfl
    rw [← hspan] at h0
    have hsub : ((D.s.atP p).ιE '' (((0 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) :
        Set D.host.E)) ⊆ {0} := by
      rintro _ ⟨x, hx, rfl⟩
      have : x = 0 := by simpa using hx
      simp [this]
    have h00 := Submodule.span_mono (R := (Z.M p).L.O) hsub h0
    rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at h00
    exact (bt_frFac_unit Z p a).ne_zero h00
  · have h1 : (1 : D.host.E) ∈ ((ddS D)⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [FractionalIdeal.mem_inv_iff hdd]
      intro y hy
      rw [one_mul]
      exact FractionalIdeal.coeIdeal_le_one hy
    have hmem : (1 : (D.s.atP p).Ep) ∈ Submodule.span (Z.M p).L.O {frFac Z.δ p a} := by
      rw [← hspan]; exact Submodule.subset_span ⟨1, h1, map_one _⟩
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 hmem
    have ho' : (o : (D.s.atP p).Ep) * (((bt_T_unit Z p).unit⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = 1 := by
      rw [← hfa]; exact ho
    have : (o : (D.s.atP p).Ep) = btT Z p := by
      have hU : (((bt_T_unit Z p).unit : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) = btT Z p := IsUnit.unit_spec _
      rw [← hU, ← mul_one (o : (D.s.atP p).Ep), ← Units.inv_mul (bt_T_unit Z p).unit, ← mul_assoc, ho', one_mul]
    rw [← this]; exact o.2

/- English proof (translation)
Use `⟨btT Z p ^ (b.val - c.val), ?_, by rw [bt_frFac_ratio Z p c b h, mul_comm]⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos (b.val - c.val) with h0 | h0` into its components or cases. Rewrite using `[h0, pow_zero]`. Conclude with `Subring.one_mem _`. Establish `hr : 1 ≤ D.R.rS` using `by have := b.isLt; omega`.

Conclude with `Subring.pow_mem _ (bt_T_mem Z p hD hr) _`.
-/
theorem bt_frFac_step (hD : LocDiffC D Z) (c b : Fin (D.R.rS + 1)) (h : c ≤ b) :
    ∃ k ∈ (Z.M p).L.O, frFac Z.δ p b = k * frFac Z.δ p c := by
  refine ⟨btT Z p ^ (b.val - c.val), ?_, by rw [bt_frFac_ratio Z p c b h, mul_comm]⟩
  rcases Nat.eq_zero_or_pos (b.val - c.val) with h0 | h0
  · rw [h0, pow_zero]; exact Subring.one_mem _
  · have hr : 1 ≤ D.R.rS := by have := b.isLt; omega
    exact Subring.pow_mem _ (bt_T_mem Z p hD hr) _

/- English proof (translation)
Establish `e1 : (fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (F.fvec a)) = fun a => sg a • (frFac Z.δ p a • baseChange₂ D p (F.fvec a))`. Use function extensionality and compare the values at `a`. Rewrite using `[mul_smul]`. Establish `hsg'` using `fun a => bt_sq_one_mem Z p (hsg a)`. Establish `hU` using `bt_span_units Z p sg sg (fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a)) hsg' hsg' hsg`.

Establish `hs` using `bt_span_snoc Z p (fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a))`. Establish `h4 : (fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.fvec a.castSucc)) = fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a)`. Use function extensionality and compare the values at `a`. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`. Establish `h5 : frFac Z.δ p (Fin.last D.R.rS) • baseChange₂ D p (F.fvec (Fin.last D.R.rS)) = baseChange₂ D p F.z`.

Simplify using `only [FlagG.fvec, Fin.snoc_last, bt_frFac_last, one_smul]`. Establish `h6 : lattice₂ D Z.M p (XS D F ⊔ Submodule.span (𝓞 D.host.E) {F.z}) = Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a)) ⊔ Submodule.span (Z.M p).L.O {baseChange₂ D p F.z}`. Rewrite using `[latP_sup, bt_latP_XS Z p hD, latP_span, Set.image_singleton]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bt_span_frame (hD : LocDiffC D Z) {T : D.host.E} (F : FlagG (VS D) D.R.rS T)
    (sg : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hsg : ∀ a, sg a * sg a = 1) :
    Submodule.span (Z.M p).L.O (Set.range fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (F.fvec a)) =
      lattice₂ D Z.M p (XS D F ⊔ Submodule.span (𝓞 D.host.E) {F.z}) := by
  have e1 : (fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (F.fvec a)) =
      fun a => sg a • (frFac Z.δ p a • baseChange₂ D p (F.fvec a)) := by
    funext a; rw [mul_smul]
  have hsg' := fun a => bt_sq_one_mem Z p (hsg a)
  have hU := bt_span_units Z p sg sg (fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a)) hsg' hsg' hsg
  have hs := bt_span_snoc Z p (fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a))
  have h4 : (fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.fvec a.castSucc)) =
      fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a) := by
    funext a; simp only [FlagG.fvec, Fin.snoc_castSucc]
  have h5 : frFac Z.δ p (Fin.last D.R.rS) • baseChange₂ D p (F.fvec (Fin.last D.R.rS)) = baseChange₂ D p F.z := by
    simp only [FlagG.fvec, Fin.snoc_last, bt_frFac_last, one_smul]
  have h6 : lattice₂ D Z.M p (XS D F ⊔ Submodule.span (𝓞 D.host.E) {F.z}) =
      Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a)) ⊔
        Submodule.span (Z.M p).L.O {baseChange₂ D p F.z} := by
    rw [latP_sup, bt_latP_XS Z p hD, latP_span, Set.image_singleton]
  calc Submodule.span (Z.M p).L.O (Set.range fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (F.fvec a))
      = Submodule.span (Z.M p).L.O (Set.range fun a => sg a • (frFac Z.δ p a • baseChange₂ D p (F.fvec a))) :=
        congrArg (fun f => Submodule.span (Z.M p).L.O (Set.range f)) e1
    _ = Submodule.span (Z.M p).L.O (Set.range fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a)) := hU
    _ = Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.fvec a.castSucc)) ⊔
        Submodule.span (Z.M p).L.O {frFac Z.δ p (Fin.last D.R.rS) • baseChange₂ D p (F.fvec (Fin.last D.R.rS))} := hs
    _ = Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a)) ⊔
        Submodule.span (Z.M p).L.O {baseChange₂ D p F.z} :=
        congrArg₂ (· ⊔ ·) (congrArg (fun f => Submodule.span (Z.M p).L.O (Set.range f)) h4)
          (congrArg (fun x => Submodule.span (Z.M p).L.O {x}) h5)
    _ = _ := h6.symm

/- English proof (translation)
Establish `e1 : (fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a)) = fun a => sg a • (frFac Z.δ p a • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a))`. Use function extensionality and compare the values at `a`. Rewrite using `[mul_smul]`. Establish `hsg'` using `fun a => bt_sq_one_mem Z p (hsg a)`. Establish `hU` using `bt_span_units Z p sg sg (fun a => frFac Z.δ p a • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a)) hsg' hsg' hsg`.

Establish `h1` using `bt_span_frame Z p hD F (fun _ => 1) (fun _ => one_mul 1)`. Establish `e2 : (fun a => ((1 : (D.s.atP p).Ep) * frFac Z.δ p a) • baseChange₂ D p (F.fvec a)) = fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a)`. Use function extensionality and compare the values at `a`. Rewrite using `[one_mul]`. Establish `h3` using `bt_span_tri Z p (frFac Z.δ p) (bt_frFac_step Z p hD) F.fvec ξ h1' h2'`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem bt_span_frame_tri (hD : LocDiffC D Z) {T : D.host.E} (F : FlagG (VS D) D.R.rS T)
    (sg : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hsg : ∀ a, sg a * sg a = 1)
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (h1' : ∀ a b, b < a → ξ a b = 0) (h2' : ∀ a, ξ a a = 1) :
    Submodule.span (Z.M p).L.O (Set.range fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a)) =
      lattice₂ D Z.M p (XS D F ⊔ Submodule.span (𝓞 D.host.E) {F.z}) := by
  have e1 : (fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a)) =
      fun a => sg a • (frFac Z.δ p a • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a)) := by
    funext a; rw [mul_smul]
  have hsg' := fun a => bt_sq_one_mem Z p (hsg a)
  have hU := bt_span_units Z p sg sg (fun a => frFac Z.δ p a • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a)) hsg' hsg' hsg
  have h1 := bt_span_frame Z p hD F (fun _ => 1) (fun _ => one_mul 1)
  have e2 : (fun a => ((1 : (D.s.atP p).Ep) * frFac Z.δ p a) • baseChange₂ D p (F.fvec a)) =
      fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a) := by
    funext a; rw [one_mul]
  have h3 := bt_span_tri Z p (frFac Z.δ p) (bt_frFac_step Z p hD) F.fvec ξ h1' h2'
  calc Submodule.span (Z.M p).L.O (Set.range fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a))
      = Submodule.span (Z.M p).L.O (Set.range fun a => sg a • (frFac Z.δ p a • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a))) :=
        congrArg (fun f => Submodule.span (Z.M p).L.O (Set.range f)) e1
    _ = Submodule.span (Z.M p).L.O (Set.range fun a => frFac Z.δ p a • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a)) := hU
    _ = Submodule.span (Z.M p).L.O (Set.range fun a => frFac Z.δ p a • baseChange₂ D p (F.fvec a)) := h3
    _ = Submodule.span (Z.M p).L.O (Set.range fun a => ((1 : (D.s.atP p).Ep) * frFac Z.δ p a) • baseChange₂ D p (F.fvec a)) :=
        (congrArg (fun f => Submodule.span (Z.M p).L.O (Set.range f)) e2).symm
    _ = _ := h1

end Frames

section Coord

variable (Z : LocDat D) (p : PlF D)

/- English proof (translation)
Take `⟨lam, hlam⟩` from `LinearMap.exists_extend ((Finsupp.lapply b).comp F.e_indep.repr)`. Establish `hl : ∀ a, lam (F.e a) = if a = b then 1 else 0`. Introduce `a`. Establish `hmem : F.e a ∈ Submodule.span D.host.E (Set.range F.e)` using `Submodule.subset_span ⟨a, rfl⟩`. Establish `h1` using `congrArg (fun f => f ⟨F.e a, hmem⟩) hlam`.

Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1`. Rewrite using `[h1, F.e_indep.repr_eq_single a _ rfl]`. Simplify using `[Finsupp.single_apply]`. Set `Φ : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep` to `{ toFun := fun v => ∑ i, (D.s.atP p).ιE (lam ((VS D).frame i)) * v i map_add' := fun v w => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] map_smul' := fun c v => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `ring }`. Use `⟨Φ, fun a => ?_⟩` and prove the remaining obligations. Establish `key : ∀ x : (VS D).V, Φ (baseChange₂ D p x) = (D.s.atP p).ιE (lam x)`. Introduce `x`.

Use `show ∑ i, (D.s.atP p).ιE (lam ((VS D).frame i)) * (D.s.atP p).ιE ((VS D).frame.repr x i) = _`. Use `conv_rhs => rw [← (VS D).frame.sum_repr x]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_eq_mul, map_mul, mul_comm]`.

Rewrite using `[key, hl a]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem bt_coord {T : D.host.E} (F : FlagG (VS D) D.R.rS T) (b : Fin D.R.rS) :
    ∃ Φ : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep, ∀ a, Φ (baseChange₂ D p (F.e a)) = if a = b then 1 else 0 := by
  obtain ⟨lam, hlam⟩ := LinearMap.exists_extend ((Finsupp.lapply b).comp F.e_indep.repr)
  have hl : ∀ a, lam (F.e a) = if a = b then 1 else 0 := by
    intro a
    have hmem : F.e a ∈ Submodule.span D.host.E (Set.range F.e) := Submodule.subset_span ⟨a, rfl⟩
    have h1 := congrArg (fun f => f ⟨F.e a, hmem⟩) hlam
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1, F.e_indep.repr_eq_single a _ rfl]
    simp [Finsupp.single_apply]
  let Φ : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep :=
    { toFun := fun v => ∑ i, (D.s.atP p).ιE (lam ((VS D).frame i)) * v i
      map_add' := fun v w => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring }
  refine ⟨Φ, fun a => ?_⟩
  have key : ∀ x : (VS D).V, Φ (baseChange₂ D p x) = (D.s.atP p).ιE (lam x) := by
    intro x
    show ∑ i, (D.s.atP p).ιE (lam ((VS D).frame i)) * (D.s.atP p).ιE ((VS D).frame.repr x i) = _
    conv_rhs => rw [← (VS D).frame.sum_repr x]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, map_mul, mul_comm]
  rw [key, hl a]
  split_ifs <;> simp

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact hS hy`. Consider the case `zero => exact Subring.zero_mem _`. Consider the case `add y z _ _ hy hz => exact Subring.add_mem _ hy hz`. Consider the case `smul o y _ hy => exact Subring.mul_mem _ o.2 hy`.
-/
theorem bt_mem_O_of_span {S : Set (D.s.atP p).Ep} (hS : S ⊆ (Z.M p).L.O) {x : (D.s.atP p).Ep}
    (hx : x ∈ Submodule.span (Z.M p).L.O S) : x ∈ (Z.M p).L.O := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact hS hy
  | zero => exact Subring.zero_mem _
  | add y z _ _ hy hz => exact Subring.add_mem _ hy hz
  | smul o y _ hy => exact Subring.mul_mem _ o.2 hy

/- English proof (translation)
Take `⟨Φ, hΦ⟩` from `bt_coord p F b`. Set `ΦO` to `Φ.restrictScalars (Z.M p).L.O`. Prove the components needed by the constructor for the conclusion. Establish `hm : frFac Z.δ p b.castSucc • baseChange₂ D p (F.e b) ∈ Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => baseChange₂ D p (F.e a))`. Rewrite using `[← h]`.

Conclude with `Submodule.subset_span ⟨b, rfl⟩`. Establish `h2` using `Submodule.apply_mem_span_image_of_mem_span ΦO hm`. Establish `e : ΦO (frFac Z.δ p b.castSucc • baseChange₂ D p (F.e b)) = frFac Z.δ p b.castSucc` using `by show Φ _ = _`. Rewrite using `[map_smul, hΦ, if_pos rfl, smul_eq_mul, mul_one]`. Rewrite `h2` using `[e]`.

Use `bt_mem_O_of_span Z p ?_ h2` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨a, rfl⟩, rfl⟩`. Use `show Φ _ ∈ _`. Rewrite using `[hΦ]`. Use `split_ifs`.

Conclude with `Subring.one_mem _`. Conclude with `Subring.zero_mem _`. Establish `hm : baseChange₂ D p (F.e b) ∈ Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a))`. Rewrite using `[h]`. Conclude with `Submodule.subset_span ⟨b, rfl⟩`.

Establish `h2` using `Submodule.apply_mem_span_image_of_mem_span ΦO hm`. Establish `e : ΦO (baseChange₂ D p (F.e b)) = 1` using `by show Φ _ = _; rw [hΦ, if_pos rfl]`. Rewrite `h2` using `[e]`. Establish `hsub : ΦO '' (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a)) ⊆ (Submodule.span (Z.M p).L.O {frFac Z.δ p b.castSucc} : Set (D.s.atP p).Ep)`. Introduce and unpack `_ ⟨_, ⟨a, rfl⟩, rfl⟩`.

Use `show Φ _ ∈ _`. Rewrite using `[map_smul, hΦ, smul_eq_mul]`. Use `split_ifs with hab`. Substitute `hab` using the available equality. Rewrite using `[mul_one]`.

Conclude with `Submodule.subset_span rfl`. Rewrite using `[mul_zero]`. Conclude with `Submodule.zero_mem _`. Establish `h3` using `Submodule.span_le.2 hsub h2`. Take `⟨o, ho⟩` from `Submodule.mem_span_singleton.1 h3`.

Conclude with `⟨o, o.2, ho⟩`.
-/
theorem bt_frFac_unitO {T : D.host.E} (F : FlagG (VS D) D.R.rS T)
    (h : Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a)) =
      Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => baseChange₂ D p (F.e a))) (b : Fin D.R.rS) :
    frFac Z.δ p b.castSucc ∈ (Z.M p).L.O ∧ ∃ w ∈ (Z.M p).L.O, w * frFac Z.δ p b.castSucc = 1 := by
  obtain ⟨Φ, hΦ⟩ := bt_coord p F b
  let ΦO := Φ.restrictScalars (Z.M p).L.O
  constructor
  · have hm : frFac Z.δ p b.castSucc • baseChange₂ D p (F.e b) ∈
        Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => baseChange₂ D p (F.e a)) := by
      rw [← h]; exact Submodule.subset_span ⟨b, rfl⟩
    have h2 := Submodule.apply_mem_span_image_of_mem_span ΦO hm
    have e : ΦO (frFac Z.δ p b.castSucc • baseChange₂ D p (F.e b)) = frFac Z.δ p b.castSucc := by
      show Φ _ = _
      rw [map_smul, hΦ, if_pos rfl, smul_eq_mul, mul_one]
    rw [e] at h2
    refine bt_mem_O_of_span Z p ?_ h2
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    show Φ _ ∈ _
    rw [hΦ]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · have hm : baseChange₂ D p (F.e b) ∈ Submodule.span (Z.M p).L.O
        (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a)) := by
      rw [h]; exact Submodule.subset_span ⟨b, rfl⟩
    have h2 := Submodule.apply_mem_span_image_of_mem_span ΦO hm
    have e : ΦO (baseChange₂ D p (F.e b)) = 1 := by show Φ _ = _; rw [hΦ, if_pos rfl]
    rw [e] at h2
    have hsub : ΦO '' (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F.e a)) ⊆
        (Submodule.span (Z.M p).L.O {frFac Z.δ p b.castSucc} : Set (D.s.atP p).Ep) := by
      rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
      show Φ _ ∈ _
      rw [map_smul, hΦ, smul_eq_mul]
      split_ifs with hab
      · subst hab; rw [mul_one]; exact Submodule.subset_span rfl
      · rw [mul_zero]; exact Submodule.zero_mem _
    have h3 := Submodule.span_le.2 hsub h2
    obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 h3
    exact ⟨o, o.2, ho⟩

end Coord

section LocP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

/- English proof (translation)
Introduce `x hx` and use `show ∃ s ∈ P.primeCompl, s • x ∈ L from ⟨1, P.primeCompl.one_mem, by simpa using hx⟩`.
-/
theorem bt_le_locP (P : Ideal (𝓞 E)) [P.IsPrime] (L : Submodule (𝓞 E) S.V) : L ≤ Formalism.HermitianLatticesTheory.localization₂ P L :=
  fun x hx => show ∃ s ∈ P.primeCompl, s • x ∈ L from ⟨1, P.primeCompl.one_mem, by simpa using hx⟩

/- English proof (translation)
Introduce `x hx` and use `by obtain ⟨s, hs, hx⟩ := hx exact show ∃ s ∈ P.primeCompl, s • x ∈ B from ⟨s, hs, h hx⟩`.
-/
theorem localization_mono₄ (P : Ideal (𝓞 E)) [P.IsPrime] {A B : Submodule (𝓞 E) S.V} (h : A ≤ B) :
    Formalism.HermitianLatticesTheory.localization₂ P A ≤ Formalism.HermitianLatticesTheory.localization₂ P B :=
  fun x hx => by
    obtain ⟨s, hs, hx⟩ := hx
    exact show ∃ s ∈ P.primeCompl, s • x ∈ B from ⟨s, hs, h hx⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨s, hs, hx⟩` from `hx`. Take `⟨t, ht, hx⟩` from `hx`. Conclude with `show ∃ s ∈ P.primeCompl, s • x ∈ L from ⟨t * s, P.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hx⟩`.

Conclude with `bt_le_locP P _`.
-/
theorem localization_le_of_le_localization (P : Ideal (𝓞 E)) [P.IsPrime] (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.localization₂ P (Formalism.HermitianLatticesTheory.localization₂ P L) = Formalism.HermitianLatticesTheory.localization₂ P L := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hx⟩ := hx
    obtain ⟨t, ht, hx⟩ := hx
    exact show ∃ s ∈ P.primeCompl, s • x ∈ L from ⟨t * s, P.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hx⟩
  · exact bt_le_locP P _

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Conclude with `localization_mono₄ P le_sup_left`.
-/
theorem localization_sup_of_le (P : Ideal (𝓞 E)) [P.IsPrime] {L N : Submodule (𝓞 E) S.V}
    (h : N ≤ Formalism.HermitianLatticesTheory.localization₂ P L) : Formalism.HermitianLatticesTheory.localization₂ P (L ⊔ N) = Formalism.HermitianLatticesTheory.localization₂ P L := by
  apply le_antisymm
  · calc Formalism.HermitianLatticesTheory.localization₂ P (L ⊔ N) ≤ Formalism.HermitianLatticesTheory.localization₂ P (Formalism.HermitianLatticesTheory.localization₂ P L) :=
          localization_mono₄ P (sup_le (bt_le_locP P L) h)
      _ = _ := localization_le_of_le_localization P L
  · exact localization_mono₄ P le_sup_left

/- English proof (translation)
Use `P.isPrime` as an intermediate fact. Rewrite using `[Mplus, Submodule.span_le]`. Introduce and unpack `x ((hx | hx) | ⟨b, rfl⟩)`. Conclude with `bt_le_locP P.asIdeal Λ (Submodule.mem_inf.1 hx).1`. Rewrite `hx` using `[Set.mem_singleton_iff]`.

Rewrite using `[hx, hL.2]`. Conclude with `bt_le_locP P.asIdeal Λ hL.1`. Take `⟨s, hs, hsx⟩` from `hξ.2.2 b P hgP`. Rewrite `hsx` using `[Submodule.ideal_span_singleton_smul]`. Take `⟨l, hl, hle⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hsx`.

Establish `hgE : (g : E) ≠ 0` using `by exact_mod_cast hg0`. Establish `h1 : ∀ (o : 𝓞 E) (v : S.V), o • v = (o : E) • v` using `fun o v => (algebraMap_smul E o v).symm`. Establish `hgc : ((g : 𝓞 E) : E) = (g : E)` using `by simp`. Establish `e : s • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) = l`. Rewrite using `[h1 s, smul_smul, mul_comm, ← smul_smul, ← h1 s, ← hle, h1, hgc, smul_smul, inv_mul_cancel₀ hgE, one_smul]`.

Conclude with `show ∃ s ∈ P.asIdeal.primeCompl, s • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) ∈ Λ from ⟨s, hs, by rw [e]; exact hl⟩`.
-/
theorem bt_Mplus_le_locP {r : ℕ} {T T' : E} {g : ℕ} (hg0 : g ≠ 0) (Λ : Submodule (𝓞 E) S.V)
    (F : LFlag S r T) (F' : LFlag S r T') (hL : IsLift Λ F) (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (hξ : AdmWit Λ g F F' ξ) (P : HeightOneSpectrum (𝓞 E)) (hgP : (g : 𝓞 E) ∈ P.asIdeal) :
    Mplus Λ g F F' ξ ≤ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  have := P.isPrime
  rw [Mplus, Submodule.span_le]
  rintro x ((hx | hx) | ⟨b, rfl⟩)
  · exact bt_le_locP P.asIdeal Λ (Submodule.mem_inf.1 hx).1
  · rw [Set.mem_singleton_iff] at hx; rw [hx, hL.2]; exact bt_le_locP P.asIdeal Λ hL.1
  · obtain ⟨s, hs, hsx⟩ := hξ.2.2 b P hgP
    rw [Submodule.ideal_span_singleton_smul] at hsx
    obtain ⟨l, hl, hle⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hsx
    have hgE : (g : E) ≠ 0 := by exact_mod_cast hg0
    have h1 : ∀ (o : 𝓞 E) (v : S.V), o • v = (o : E) • v := fun o v => (algebraMap_smul E o v).symm
    have hgc : ((g : 𝓞 E) : E) = (g : E) := by simp
    have e : s • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) = l := by
      rw [h1 s, smul_smul, mul_comm, ← smul_smul, ← h1 s, ← hle, h1, hgc, smul_smul, inv_mul_cancel₀ hgE, one_smul]
    exact show ∃ s ∈ P.asIdeal.primeCompl, s • ((g : E)⁻¹ • (frame F' b - frameAct (frame F) ξ b)) ∈ Λ from
      ⟨s, hs, by rw [e]; exact hl⟩

end LocP

section Main

variable (Z : LocDat D)

/- English proof (translation)
Use `isNoetherian_of_fg_of_noetherian Λ hΛ` as an intermediate fact. Conclude with `Submodule.FG.of_le_of_isNoetherian h`.
-/
theorem bt_fg_le {Λ N : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Λ.FG) (h : N ≤ Λ) : N.FG := by
  have := isNoetherian_of_fg_of_noetherian Λ hΛ
  exact Submodule.FG.of_le_of_isNoetherian h

/- English proof (translation)
Rewrite using `[Mplus, Submodule.span_union, Submodule.span_union, Submodule.span_eq]`. Conclude with `(hX.sup (Submodule.fg_span (Set.finite_singleton _))).sup (Submodule.fg_span (Set.finite_range _))`.
-/
theorem bt_Mplus_fg {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} {F : LFlag (VS D) D.R.rS T}
    {F' : LFlag (VS D) D.R.rS T'} (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (hX : (XLam Λ F).FG) : (Mplus Λ (gS D) F F' ξ).FG := by
  rw [Mplus, Submodule.span_union, Submodule.span_union, Submodule.span_eq]
  exact (hX.sup (Submodule.fg_span (Set.finite_singleton _))).sup (Submodule.fg_span (Set.finite_range _))

/- English proof (translation)
Simplify using `only [frameAct, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> rw [smul_comm]`.
-/
theorem bt_frameAct_lin {n : ℕ} (c : D.host.E) (u v : Fin n → (VS D).V) (m : Matrix (Fin n) (Fin n) (𝓞 D.host.E))
    (b : Fin n) : frameAct (fun i => c • (u i - v i)) m b = c • (frameAct u m b - frameAct v m b) := by
  simp only [frameAct, smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun i _ => ?_ <;> rw [smul_comm]

/- English proof (translation)
Establish `hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)` using `by rw [← D.s_split p, hs]; rfl`. Use `(D.s.atP p).char0` as an intermediate fact. Establish `hq : (sg.q : (D.s.atP p).Fp) = (Loc.resChar p : (D.s.atP p).Fp)` using `sg.q_eq`. Establish `hcast : ∀ n : ℕ, (n : (D.s.atP p).Ep) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp)` using `fun n => (map_natCast _ n).symm`. Establish `hne` using `D.host.g_ne`.

Rewrite using `[map_natCast, gS, Nat.cast_mul, hq]`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hin`. Establish `key : ∀ i j : ℕ, i.Prime → j.Prime → i ≠ j → Loc.resChar p = i → algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((Loc.resChar p : (D.s.atP p).Fp)⁻¹) * ((i : (D.s.atP p).Ep) * (j : (D.s.atP p).Ep)) = (j : (D.s.atP p).Ep)`. Introduce `i j hi _ _ hri`. Rewrite using `[hri, ← mul_assoc, hcast i, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hi.ne_zero), map_one, one_mul]`.

Establish `hnd : ∀ i j : ℕ, i.Prime → j.Prime → i ≠ j → Loc.resChar p = i → ¬ Loc.resChar p ∣ j`. Introduce `i j hi hj hij hri h`. Rewrite `h` using `[hri]`. Conclude with `hij ((Nat.prime_dvd_prime_iff_eq hi hj).1 h)`. Break down `hin with h0 | h1` into its components or cases.

Rewrite using `[key _ _ (D.host.g_prime 0) (D.host.g_prime 1) hne h0]`. Conclude with `bt_nat_unit Z p _ (hnd _ _ (D.host.g_prime 0) (D.host.g_prime 1) hne h0)`. Rewrite using `[mul_comm ((D.host.g 0 : ℕ) : (D.s.atP p).Ep), key _ _ (D.host.g_prime 1) (D.host.g_prime 0) hne.symm h1]`. Conclude with `bt_nat_unit Z p _ (hnd _ _ (D.host.g_prime 1) (D.host.g_prime 0) hne.symm h1)`.
-/
theorem bt_kappa (p : PlF D) (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hs : (D.s.atP p).split = some sg) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) * (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)
      ∈ (Z.M p).L.O ∧ ∃ w ∈ (Z.M p).L.O, w * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
        (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)) = 1 := by
  have hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by rw [← D.s_split p, hs]; rfl
  have := (D.s.atP p).char0
  have hq : (sg.q : (D.s.atP p).Fp) = (Loc.resChar p : (D.s.atP p).Fp) := sg.q_eq
  have hcast : ∀ n : ℕ, (n : (D.s.atP p).Ep) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (n : (D.s.atP p).Fp) :=
    fun n => (map_natCast _ n).symm
  have hne := D.host.g_ne
  rw [map_natCast, gS, Nat.cast_mul, hq]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hin
  have key : ∀ i j : ℕ, i.Prime → j.Prime → i ≠ j → Loc.resChar p = i →
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((Loc.resChar p : (D.s.atP p).Fp)⁻¹) * ((i : (D.s.atP p).Ep) *
        (j : (D.s.atP p).Ep)) = (j : (D.s.atP p).Ep) := by
    intro i j hi _ _ hri
    rw [hri, ← mul_assoc, hcast i, ← map_mul, inv_mul_cancel₀ (by exact_mod_cast hi.ne_zero), map_one, one_mul]
  have hnd : ∀ i j : ℕ, i.Prime → j.Prime → i ≠ j → Loc.resChar p = i → ¬ Loc.resChar p ∣ j := by
    intro i j hi hj hij hri h
    rw [hri] at h
    exact hij ((Nat.prime_dvd_prime_iff_eq hi hj).1 h)
  rcases hin with h0 | h1
  · rw [key _ _ (D.host.g_prime 0) (D.host.g_prime 1) hne h0]
    exact bt_nat_unit Z p _ (hnd _ _ (D.host.g_prime 0) (D.host.g_prime 1) hne h0)
  · rw [mul_comm ((D.host.g 0 : ℕ) : (D.s.atP p).Ep), key _ _ (D.host.g_prime 1) (D.host.g_prime 0) hne.symm h1]
    exact bt_nat_unit Z p _ (hnd _ _ (D.host.g_prime 1) (D.host.g_prime 0) hne.symm h1)

/- English proof (translation)
Rewrite using `[Submodule.span_union]`. Establish `h1 : Submodule.span (Z.M p).L.O (Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f) = lattice₂ D Z.M p (XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z})` using `bt_span_frame Z p hD F0 (sgnP D p) (localSign_sq p)`. Establish `hu` using `admissibility_witness_unitriangular Λ (lf D F0) F'`. Establish `h2 : Submodule.span (Z.M p).L.O (Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f') = lattice₂ D Z.M p (XS D F'.fl ⊔ Submodule.span (𝓞 D.host.E) {F'.fl.z})` using `bt_span_frame_tri Z p hD F'.fl (sgnP' D p) (sgnP'_sq p) _ hu.1 hu.2`. Establish `e : UU Λ (lf D F0) F' = (XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z}) ⊔ (XS D F'.fl ⊔ Submodule.span (𝓞 D.host.E) {F'.fl.z})`.

Rewrite using `[UU, hXL, hXL', hz']`. Simplify using `only [sup_assoc]`. Rewrite using `[h1, h2, e]`. Conclude with `(latP_sup Z p _ _).symm`.
-/
theorem bt_spanO_ff (hD : LocDiffC D Z) (p : PlF D) {T T' : ℕ} (F0 : FlagG (VS D) D.R.rS (T : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS (T' : D.host.E))
    (hXL : XLam Λ (lf D F0) = XS D F0) (hXL' : XLam Λ F' = XS D F'.fl) (hz' : F'.zt = F'.fl.z) (Tn T'n : ℕ) :
    Submodule.span (Z.M p).L.O (Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f ∪
      Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f') = lattice₂ D Z.M p (UU Λ (lf D F0) F') := by
  rw [Submodule.span_union]
  have h1 : Submodule.span (Z.M p).L.O (Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f) =
      lattice₂ D Z.M p (XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z}) :=
    bt_span_frame Z p hD F0 (sgnP D p) (localSign_sq p)
  have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
  have h2 : Submodule.span (Z.M p).L.O (Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f') =
      lattice₂ D Z.M p (XS D F'.fl ⊔ Submodule.span (𝓞 D.host.E) {F'.fl.z}) :=
    bt_span_frame_tri Z p hD F'.fl (sgnP' D p) (sgnP'_sq p) _ hu.1 hu.2
  have e : UU Λ (lf D F0) F' = (XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z}) ⊔
      (XS D F'.fl ⊔ Submodule.span (𝓞 D.host.E) {F'.fl.z}) := by
    rw [UU, hXL, hXL', hz']
    simp only [sup_assoc]
  rw [h1, h2, e]
  exact (latP_sup Z p _ _).symm

/- English proof (translation)
Establish `hXfg : (XLam Λ (lf D F0)).FG` using `bt_fg_le hΛfg inf_le_left`. Establish `hX : lattice₂ D Z.M p (XLam Λ (lf D F0)) = lattice₂ D Z.M p (Submodule.span (𝓞 D.host.E) (Set.range F0.e))`. Use `(hE p _ _ hXfg (Submodule.fg_span (Set.finite_range _))).2 ?_` and prove the remaining obligations. Introduce `P hP`. Take `⟨c, -, hc1, hc⟩` from `hFC.1 P`.

Establish `hce : (fun a => c a • F0.e a) = F0.e`. Use function extensionality and compare the values at `b`. Rewrite using `[hc1 (hgP P hP) b, one_smul]`. Use `hc.trans ?_` and prove the remaining obligations. Conclude with `congrArg (fun f => (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range f)))) hce`.

Establish `hspanX : Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F0.e a)) = Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => baseChange₂ D p (F0.e a))`. Combine the equalities or inequalities in the displayed calculation. Break down `Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl` into its components or cases. Conclude with `bt_frFac_unitO Z p F0 hspanX b`. Rewrite using `[bt_frFac_last]`.

Conclude with `⟨Subring.one_mem _, 1, Subring.one_mem _, one_mul 1⟩`.
-/
theorem bt_typed_frFac (hE : LocEqC D Z) (hD : LocDiffC D Z) (p : PlF D) {T : ℕ} (F0 : FlagG (VS D) D.R.rS (T : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛfg : Λ.FG) (hXL : XLam Λ (lf D F0) = XS D F0)
    (hFC : IsFixedConv Λ (gS D) (lf D F0))
    (hgP : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P.asIdeal)
    (a : Fin (D.R.rS + 1)) : frFac Z.δ p a ∈ (Z.M p).L.O ∧ ∃ w ∈ (Z.M p).L.O, w * frFac Z.δ p a = 1 := by
  have hXfg : (XLam Λ (lf D F0)).FG := bt_fg_le hΛfg inf_le_left
  have hX : lattice₂ D Z.M p (XLam Λ (lf D F0)) = lattice₂ D Z.M p (Submodule.span (𝓞 D.host.E) (Set.range F0.e)) := by
    refine (hE p _ _ hXfg (Submodule.fg_span (Set.finite_range _))).2 ?_
    intro P hP
    obtain ⟨c, -, hc1, hc⟩ := hFC.1 P
    have hce : (fun a => c a • F0.e a) = F0.e := by
      funext b
      rw [hc1 (hgP P hP) b, one_smul]
    refine hc.trans ?_
    exact congrArg (fun f => (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Submodule.span (𝓞 D.host.E) (Set.range f)))) hce
  have hspanX : Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F0.e a)) =
      Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => baseChange₂ D p (F0.e a)) :=
    calc Submodule.span (Z.M p).L.O (Set.range fun a : Fin D.R.rS => frFac Z.δ p a.castSucc • baseChange₂ D p (F0.e a))
        = lattice₂ D Z.M p (XS D F0) := (bt_latP_XS Z p hD F0).symm
      _ = lattice₂ D Z.M p (XLam Λ (lf D F0)) := congrArg (lattice₂ D Z.M p) hXL.symm
      _ = lattice₂ D Z.M p (Submodule.span (𝓞 D.host.E) (Set.range F0.e)) := hX
      _ = Submodule.span (Z.M p).L.O (baseChange₂ D p '' Set.range F0.e) := latP_span Z p _
      _ = _ := congrArg (Submodule.span (Z.M p).L.O) (Set.range_comp _ _).symm
  rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
  · exact bt_frFac_unitO Z p F0 hspanX b
  · rw [bt_frFac_last]; exact ⟨Subring.one_mem _, 1, Subring.one_mem _, one_mul 1⟩

/- English proof (translation)
Establish `hu` using `admissibility_witness_unitriangular Λ (lf D F0) F'`. Establish `hgS0 : gS D ≠ 0` using `by simp [gS, (D.host.g_prime 0).ne_zero, (D.host.g_prime 1).ne_zero]`. Establish `hgE : ((gS D : ℕ) : D.host.E) ≠ 0` using `by exact_mod_cast hgS0`. Establish `hyw : ((gS D : ℕ) : D.host.E) • frameAct (fun c => ((gS D : D.host.E))⁻¹ • (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c)) (admXi D Λ (lf D F0) F')⁻¹ a = frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹ a - frame (lf D F0) a`. Rewrite using `[bt_frameAct_lin, bt_frameAct_comp, Matrix.mul_nonsing_inv _ (bt_unitri_det _ hu.1 hu.2), bt_frameAct_one, smul_smul, mul_inv_cancel₀ hgE, one_smul]`.

Establish `hss : sgnP' D p a = sgnP D p a`. Simplify using `only [sgnP', hs]`. Use `show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) • ((sgnP' D p a * frFac Z.δ p a) • baseChange₂ D p (frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹ a) - (sgnP D p a * frFac Z.δ p a) • baseChange₂ D p (frame (lf D F0) a)) = _`. Rewrite using `[hss, ← smul_sub, ← map_sub, ← hyw, baseChange_smul₂, smul_smul, smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem bt_typed_sec (p : PlF D) {T T' : ℕ} (F0 : FlagG (VS D) D.R.rS (T : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS (T' : D.host.E)) (Tn T'n : ℕ)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hs : (D.s.atP p).split = some sg) (a : Fin (D.R.rS + 1)) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) •
        ((locTerm Z p Λ (lf D F0) F' Tn T'n).f' a - (locTerm Z p Λ (lf D F0) F' Tn T'n).f a) =
      (sgnP D p a * frFac Z.δ p a * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
        (D.s.atP p).ιE ((gS D : ℕ) : D.host.E))) •
        baseChange₂ D p (frameAct (fun c => ((gS D : D.host.E))⁻¹ •
          (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c)) (admXi D Λ (lf D F0) F')⁻¹ a) := by
  have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
  have hgS0 : gS D ≠ 0 := by simp [gS, (D.host.g_prime 0).ne_zero, (D.host.g_prime 1).ne_zero]
  have hgE : ((gS D : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hgS0
  have hyw : ((gS D : ℕ) : D.host.E) • frameAct (fun c => ((gS D : D.host.E))⁻¹ •
      (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c)) (admXi D Λ (lf D F0) F')⁻¹ a =
      frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹ a - frame (lf D F0) a := by
    rw [bt_frameAct_lin, bt_frameAct_comp, Matrix.mul_nonsing_inv _ (bt_unitri_det _ hu.1 hu.2), bt_frameAct_one,
      smul_smul, mul_inv_cancel₀ hgE, one_smul]
  have hss : sgnP' D p a = sgnP D p a := by
    simp only [sgnP', hs]
  show algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) •
      ((sgnP' D p a * frFac Z.δ p a) • baseChange₂ D p (frameAct (frame F') (admXi D Λ (lf D F0) F')⁻¹ a) -
        (sgnP D p a * frFac Z.δ p a) • baseChange₂ D p (frame (lf D F0) a)) = _
  rw [hss, ← smul_sub, ← map_sub, ← hyw, baseChange_smul₂, smul_smul, smul_smul]
  congr 1
  ring

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hu` using `admissibility_witness_unitriangular Λ (lf D F0) F'`. Rewrite using `[Submodule.span_union]`. Establish `h1 : Submodule.span (Z.M p).L.O (Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f) = lattice₂ D Z.M p (XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z})` using `bt_span_frame Z p hD F0 (sgnP D p) (localSign_sq p)`. Take `⟨hκO, wκ, hwκO, hwκ⟩` from `bt_kappa Z p sg hs`. Establish `hU` using `bt_span_units Z p (fun a => sgnP D p a * frFac Z.δ p a * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) * (D.s.atP p).ιE ((gS D : ℕ) : D.host.E))) (fun a => sgnP D p a * (hφ a).2.choose * wκ) (fun a => baseChange₂ D p (frameAct (fun c => ((gS D : D.host.E)) …`.

Establish `h3` using `(hφ a).2.choose_spec.2`. Establish `h4` using `localSign_sq p a`. Combine the equalities or inequalities in the displayed calculation. Expand and normalize the polynomial expressions, which then agree. Use `_ = 1 := by rw [h4, h3, hwκ]; ring)`.

Establish `h4` using `bt_span_tri Z p (fun _ => (1 : (D.s.atP p).Ep)) (fun c b _ => ⟨1, Subring.one_mem _, by ring⟩) (fun c => ((gS D : D.host.E))⁻¹ • (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c)) (admXi D Λ (lf D F0) F') hu.1 hu.2`. Establish `h2 : Submodule.span (Z.M p).L.O (Set.range fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) • ((locTerm Z p Λ (lf D F0) F' Tn T'n).f' a - (locTerm Z p Λ (lf D F0) F' Tn T'n).f a)) = lattice₂ D Z.M p (Submodule.span (𝓞 D.host.E) (Set.range fun c => ((g …`. Use `(congrArg (fun f => Submodule.span (Z.M p).L.O (Set.range f)) (funext (bt_typed_sec Z p F0 Λ F' Tn T'n sg hs))).trans ?_` and prove the remaining obligations. Use `hU.trans ?_` and prove the remaining obligations. Establish `e1 : (fun a => baseChange₂ D p (frameAct (fun c => ((gS D : D.host.E))⁻¹ • (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c)) (admXi D Λ (lf D F0) F')⁻¹ a)) = fun a => (1 : (D.s.atP p).Ep) • baseChange₂ D p (frameAct (fun c => ((gS D : D.host.E))⁻¹ • (frame F' …`.

Use function extensionality and compare the values at `a`. Rewrite using `[one_smul]`. Establish `e2 : (fun a => (1 : (D.s.atP p).Ep) • baseChange₂ D p (((gS D : D.host.E))⁻¹ • (frame F' a - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') a))) = baseChange₂ D p ∘ (fun c => ((gS D : D.host.E))⁻¹ • (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c))`. Use function extensionality and compare the values at `a`. Rewrite using `[one_smul]`.

Both sides reduce to the same expression. Use `(congrArg (fun f => Submodule.span (Z.M p).L.O (Set.range f)) e1).trans ?_` and prove the remaining obligations. Use `h4.trans ?_` and prove the remaining obligations. Use `(congrArg (fun f => Submodule.span (Z.M p).L.O (Set.range f)) e2).trans ?_` and prove the remaining obligations. Rewrite using `[Set.range_comp, ← latP_span]`.

Establish `h5 : lattice₂ D Z.M p (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) = lattice₂ D Z.M p (XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z}) ⊔ lattice₂ D Z.M p (Submodule.span (𝓞 D.host.E) (Set.range fun c => ((gS D : D.host.E))⁻¹ • (frame F' c - frameAct (frame (lf D F0)) (adm …`. Rewrite using `[← latP_sup, ← hXL, Mplus, Submodule.span_union, Submodule.span_union, Submodule.span_eq]`. Rewrite using `[h1, h2, h5]`.
-/
theorem bt_typed_O (hD : LocDiffC D Z) (p : PlF D) {T T' : ℕ} (F0 : FlagG (VS D) D.R.rS (T : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS (T' : D.host.E)) (Tn T'n : ℕ)
    (hXL : XLam Λ (lf D F0) = XS D F0)
    (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
    (hs : (D.s.atP p).split = some sg)
    (hφ : ∀ a, frFac Z.δ p a ∈ (Z.M p).L.O ∧ ∃ w ∈ (Z.M p).L.O, w * frFac Z.δ p a = 1) :
    Submodule.span (Z.M p).L.O (Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f ∪
      Set.range fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) •
        ((locTerm Z p Λ (lf D F0) F' Tn T'n).f' a - (locTerm Z p Λ (lf D F0) F' Tn T'n).f a)) =
      lattice₂ D Z.M p (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) := by
  have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
  rw [Submodule.span_union]
  have h1 : Submodule.span (Z.M p).L.O (Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f) =
      lattice₂ D Z.M p (XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z}) :=
    bt_span_frame Z p hD F0 (sgnP D p) (localSign_sq p)
  obtain ⟨hκO, wκ, hwκO, hwκ⟩ := bt_kappa Z p sg hs
  have hU := bt_span_units Z p
    (fun a => sgnP D p a * frFac Z.δ p a * (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) *
        (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)))
    (fun a => sgnP D p a * (hφ a).2.choose * wκ)
    (fun a => baseChange₂ D p (frameAct (fun c => ((gS D : D.host.E))⁻¹ •
          (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c)) (admXi D Λ (lf D F0) F')⁻¹ a))
    (fun a => Subring.mul_mem _ (Subring.mul_mem _ (bt_sq_one_mem Z p (localSign_sq p a)) (hφ a).1) hκO)
    (fun a => Subring.mul_mem _ (Subring.mul_mem _ (bt_sq_one_mem Z p (localSign_sq p a)) (hφ a).2.choose_spec.1) hwκO)
    (fun a => by
      have h3 := (hφ a).2.choose_spec.2
      have h4 := localSign_sq p a
      calc sgnP D p a * (hφ a).2.choose * wκ * (sgnP D p a * frFac Z.δ p a *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) * (D.s.atP p).ιE ((gS D : ℕ) : D.host.E)))
          = (sgnP D p a * sgnP D p a) * ((hφ a).2.choose * frFac Z.δ p a) * (wκ *
            (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) * (D.s.atP p).ιE ((gS D : ℕ) : D.host.E))) := by
            ring
        _ = 1 := by rw [h4, h3, hwκ]; ring)
  have h4 := bt_span_tri Z p (fun _ => (1 : (D.s.atP p).Ep))
    (fun c b _ => ⟨1, Subring.one_mem _, by ring⟩)
    (fun c => ((gS D : D.host.E))⁻¹ • (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c))
    (admXi D Λ (lf D F0) F') hu.1 hu.2
  have h2 : Submodule.span (Z.M p).L.O (Set.range fun a =>
      algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) •
        ((locTerm Z p Λ (lf D F0) F' Tn T'n).f' a - (locTerm Z p Λ (lf D F0) F' Tn T'n).f a)) =
      lattice₂ D Z.M p (Submodule.span (𝓞 D.host.E) (Set.range fun c => ((gS D : D.host.E))⁻¹ •
          (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c))) := by
    refine (congrArg (fun f => Submodule.span (Z.M p).L.O (Set.range f))
      (funext (bt_typed_sec Z p F0 Λ F' Tn T'n sg hs))).trans ?_
    refine hU.trans ?_
    have e1 : (fun a => baseChange₂ D p (frameAct (fun c => ((gS D : D.host.E))⁻¹ •
          (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c)) (admXi D Λ (lf D F0) F')⁻¹ a)) =
        fun a => (1 : (D.s.atP p).Ep) • baseChange₂ D p (frameAct (fun c => ((gS D : D.host.E))⁻¹ •
          (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c)) (admXi D Λ (lf D F0) F')⁻¹ a) := by
      funext a; rw [one_smul]
    have e2 : (fun a => (1 : (D.s.atP p).Ep) • baseChange₂ D p (((gS D : D.host.E))⁻¹ •
          (frame F' a - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') a))) =
        baseChange₂ D p ∘ (fun c => ((gS D : D.host.E))⁻¹ •
          (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c)) := by
      funext a; rw [one_smul]; rfl
    refine (congrArg (fun f => Submodule.span (Z.M p).L.O (Set.range f)) e1).trans ?_
    refine h4.trans ?_
    refine (congrArg (fun f => Submodule.span (Z.M p).L.O (Set.range f)) e2).trans ?_
    rw [Set.range_comp, ← latP_span]
  have h5 : lattice₂ D Z.M p (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) =
      lattice₂ D Z.M p (XS D F0 ⊔ Submodule.span (𝓞 D.host.E) {F0.z}) ⊔
        lattice₂ D Z.M p (Submodule.span (𝓞 D.host.E) (Set.range fun c => ((gS D : D.host.E))⁻¹ •
          (frame F' c - frameAct (frame (lf D F0)) (admXi D Λ (lf D F0) F') c))) := by
    rw [← latP_sup, ← hXL, Mplus, Submodule.span_union, Submodule.span_union, Submodule.span_eq]
  rw [h1, h2, h5]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨a, rfl⟩)`. Conclude with `Submodule.subset_span (Or.inl ⟨a, rfl⟩)`. Conclude with `Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩)) (Submodule.subset_span (Or.inl ⟨a, rfl⟩)))`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨a, rfl⟩)`. Conclude with `Submodule.subset_span (Or.inl ⟨a, rfl⟩)`. Establish `e : (locTerm Z p Λ (lf D F0) F' Tn T'n).f' a = (locTerm Z p Λ (lf D F0) F' Tn T'n).f a + algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q • (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ • ((locTerm Z p Λ (lf D F0) F' Tn T'n).f' a - (locTerm Z p Λ (lf D F0) F' Tn T'n).f a))`. Rewrite using `[smul_smul, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_smul, add_sub_cancel]`.

Rewrite using `[SetLike.mem_coe, e]`. Conclude with `Submodule.add_mem _ (Submodule.subset_span (Or.inl ⟨a, rfl⟩)) (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩)))`.
-/
theorem bt_typed_Ep (p : PlF D) {T T' : ℕ} (F0 : FlagG (VS D) D.R.rS (T : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS (T' : D.host.E)) (Tn T'n : ℕ)
    (q : (D.s.atP p).Fp) (hq0 : q ≠ 0) :
    Submodule.span (D.s.atP p).Ep (Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f ∪
      Set.range fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ •
        ((locTerm Z p Λ (lf D F0) F' Tn T'n).f' a - (locTerm Z p Λ (lf D F0) F' Tn T'n).f a)) =
    Submodule.span (D.s.atP p).Ep (Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f ∪
      Set.range (locTerm Z p Λ (lf D F0) F' Tn T'n).f') := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Submodule.subset_span (Or.inl ⟨a, rfl⟩)
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩))
        (Submodule.subset_span (Or.inl ⟨a, rfl⟩)))
  · rw [Submodule.span_le]
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact Submodule.subset_span (Or.inl ⟨a, rfl⟩)
    · have e : (locTerm Z p Λ (lf D F0) F' Tn T'n).f' a = (locTerm Z p Λ (lf D F0) F' Tn T'n).f a +
          algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q • (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ •
            ((locTerm Z p Λ (lf D F0) F' Tn T'n).f' a - (locTerm Z p Λ (lf D F0) F' Tn T'n).f a)) := by
        rw [smul_smul, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_smul, add_sub_cancel]
      rw [SetLike.mem_coe, e]
      exact Submodule.add_mem _ (Submodule.subset_span (Or.inl ⟨a, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩)))

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `u u' F0 Λ F' hR hPD hMI p`. Establish `hFix` using `hR.2.1`. Establish `hΛfg : Λ.FG` using `hFix.1.fg`. Establish `hLift : IsLift Λ (lf D F0)` using `hFix.2.2.1`. Establish `hFC : IsFixedConv Λ (gS D) (lf D F0)` using `hFix.2.2.2`.

Establish `hXL : XLam Λ (lf D F0) = XS D F0` using `hR.2.2`. Establish `hLift' : IsLift Λ F'` using `hPD.1`. Establish `hadm : IsAdmissible Λ (gS D) (lf D F0) F'` using `hPD.2.1`. Establish `hXL' : XLam Λ F' = XS D F'.fl` using `hPD.2.2.2`. Establish `hξ : AdmWit Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')`.

Unfold `admXi`. Rewrite using `[dif_pos hadm]`. Conclude with `hadm.choose_spec`. Establish `hUUle : UU Λ (lf D F0) F' ≤ Λ`. Use `sup_le (sup_le (sup_le inf_le_left ?_) inf_le_left) ?_` and prove the remaining obligations.

Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `hLift.1`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff, hLift'.2]`. Conclude with `hLift'.1`. Establish `hUUfg` using `bt_fg_le hΛfg hUUle`.

Establish `hBfg : (BLat Λ (lf D F0) F').FG` using `bt_fg_le hΛfg inf_le_left`. Establish `hff` using `bt_spanO_ff Z hD p F0 Λ F' hXL hXL' hLift'.2 (Tu D u) (Tu D u')`. Establish `hagree` using `(Z.agree p).2.2.2.2.2`. Unfold `locBBne`. Use `set t := locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with ht`.

Establish `hEff : Submodule.span (D.s.atP p).Ep (Set.range t.f ∪ Set.range t.f') = Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (UUE Λ (lf D F0) F' : Set (VS D).V))`. Rewrite using `[← bt_spanEp_spanO Z p (Set.range t.f ∪ Set.range t.f'), hff, lattice₂, bt_spanEp_spanO Z p, UUE, spanE, bt_spanEp_spanE]`. Break down `hs : (D.s.atP p).split with _ | sg` into its components or cases. Establish `hMs : (Z.M p).split = none`. Break down `hM : (Z.M p).split with _ | g'` into its components or cases.

Both sides reduce to the same expression. Rewrite `hagree` using `[hM, hs]`. Conclude with `hagree.elim`. Establish `hnot : Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ)`. Rewrite using `[← D.s_split p, hs]`.

Simplify using the standard rewrite rules. Establish `hgP : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∉ P.asIdeal` using `fun P hP => by rw [bt_g_mem_iff p P hP]; exact hnot`. Establish `hglob : BBneF D Λ (lf D F0) F' p ↔ ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal ∧ (haveI` using `P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ (lf D F0) F') ≠ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ (lf D F0) F')) := by`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨P, hP, -, h2⟩`.

Conclude with `⟨P, hP, h2 (hgP P hP)⟩`. Introduce and unpack `⟨P, hP, h⟩`. Conclude with `⟨P, hP, fun hg => absurd hg (hgP P hP), fun _ => h⟩`. Rewrite using `[hglob, bt_glob_iff Z p hE _ _ hBfg hUUfg]`. Establish `hMM : (locH Z p).MMfam t = Sum.elim t.f t.f'`.

Simplify using `only [Loc.HermSp.MMfam, hMs]`. Establish `hO : Submodule.span (Z.M p).L.O (Set.range ((locH Z p).MMfam t)) = lattice₂ D Z.M p (UU Λ (lf D F0) F')`. Rewrite using `[hMM, Set.Sum.elim_range]`. Conclude with `hff`. Establish `hEp : Submodule.span (D.s.atP p).Ep (Set.range ((locH Z p).MMfam t)) = Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (UUE Λ (lf D F0) F' : Set (VS D).V))`.

Rewrite using `[hMM, Set.Sum.elim_range]`. Conclude with `hEff`. Conclude with `(bt_bbne_iff Z p hS t Λ (UU Λ (lf D F0) F') (UUE Λ (lf D F0) F') hΛfg rfl hO hEp (latP_mono Z p hUUle)).symm`. Choose the witnesses or unpack the hypotheses as in `⟨g', hMs, hgq⟩ : ∃ g', (Z.M p).split = some g' ∧ g'.q = sg.q := by`. Break down `hM : (Z.M p).split with _ | g'` into its components or cases.

Rewrite `hagree` using `[hM, hs]`. Conclude with `hagree.elim`. Rewrite `hagree` using `[hM, hs]`. Conclude with `⟨g', rfl, hagree.2⟩`. Establish `hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)` using `by rw [← D.s_split p, hs]; rfl`.

Establish `hgP : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P.asIdeal` using `fun P hP => (bt_g_mem_iff p P hP).2 hin`. Establish `hXfg : (XLam Λ (lf D F0)).FG` using `bt_fg_le hΛfg inf_le_left`. Establish `hMfg : (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')).FG` using `bt_Mplus_fg _ hXfg`. Establish `hglob : BBneF D Λ (lf D F0) F' p ↔ ∃ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal ∧ (haveI` using `P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ (lf D F0) F') ≠ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F'))) := by`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨P, hP, h1, -⟩`. Conclude with `⟨P, hP, h1 (hgP P hP) _ hξ⟩`. Introduce and unpack `⟨P, hP, h⟩`. Use `⟨P, hP, fun hg ξ' hξ' heq => h ?_, fun hng => absurd (hgP P hP) hng⟩` and prove the remaining obligations. Rewrite using `[heq]`.

Conclude with `hMI hLift hFC P hg ξ' _ hξ' hξ`. Rewrite using `[hglob, bt_glob_iff Z p hE _ _ hBfg hMfg]`. Establish `hgS0 : gS D ≠ 0` using `by simp [gS, (D.host.g_prime 0).ne_zero, (D.host.g_prime 1).ne_zero]`. Establish `hMΛ : lattice₂ D Z.M p (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) ≤ lattice₂ D Z.M p Λ`. Establish `hsup : lattice₂ D Z.M p (Λ ⊔ Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) = lattice₂ D Z.M p Λ`.

Use `(hE p _ _ (hΛfg.sup hMfg) hΛfg).2 ?_` and prove the remaining obligations. Introduce `P hP`. Use `P.isPrime` as an intermediate fact. Conclude with `localization_sup_of_le P.asIdeal (bt_Mplus_le_locP hgS0 Λ (lf D F0) F' hLift _ hξ P (hgP P hP))`. Conclude with `(latP_mono Z p le_sup_right).trans hsup.le`.

Establish `hφ` using `bt_typed_frFac Z hE hD p F0 Λ hΛfg hXL hFC hgP`. Establish `hMM : (locH Z p).MMfam t = Sum.elim t.f (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) • (t.f' a - t.f a))`. Simplify using `only [Loc.HermSp.MMfam, hMs, hgq]`. Establish `hO : Submodule.span (Z.M p).L.O (Set.range ((locH Z p).MMfam t)) = lattice₂ D Z.M p (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F'))`. Rewrite using `[hMM, Set.Sum.elim_range]`.

Conclude with `bt_typed_O Z hD p F0 Λ F' (Tu D u) (Tu D u') hXL sg hs hφ`. Establish `hq0 : (sg.q : (D.s.atP p).Fp) ≠ 0`. Introduce `h`. Conclude with `sg.q_irr.ne_zero (Subtype.ext h)`. Establish `hEp : Submodule.span (D.s.atP p).Ep (Set.range ((locH Z p).MMfam t)) = Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (UUE Λ (lf D F0) F' : Set (VS D).V))`.

Rewrite using `[hMM, Set.Sum.elim_range]`. Conclude with `(bt_typed_Ep Z p F0 Λ F' (Tu D u) (Tu D u') _ hq0).trans hEff`. Conclude with `(bt_bbne_iff Z p hS t Λ _ (UUE Λ (lf D F0) F') hΛfg rfl hO hEp hMΛ).symm`.
-/
theorem bbTie_core (hE : LocEqC D Z) (hS : LocSatC D Z) (hD : LocDiffC D Z) : BBTie D Z := by
  intro u u' F0 Λ F' hR hPD hMI p
  have hFix := hR.2.1
  have hΛfg : Λ.FG := hFix.1.fg
  have hLift : IsLift Λ (lf D F0) := hFix.2.2.1
  have hFC : IsFixedConv Λ (gS D) (lf D F0) := hFix.2.2.2
  have hXL : XLam Λ (lf D F0) = XS D F0 := hR.2.2
  have hLift' : IsLift Λ F' := hPD.1
  have hadm : IsAdmissible Λ (gS D) (lf D F0) F' := hPD.2.1
  have hXL' : XLam Λ F' = XS D F'.fl := hPD.2.2.2
  have hξ : AdmWit Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F') := by
    unfold admXi; rw [dif_pos hadm]; exact hadm.choose_spec
  have hUUle : UU Λ (lf D F0) F' ≤ Λ := by
    refine sup_le (sup_le (sup_le inf_le_left ?_) inf_le_left) ?_
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hLift.1
    · rw [Submodule.span_le, Set.singleton_subset_iff, hLift'.2]; exact hLift'.1
  have hUUfg := bt_fg_le hΛfg hUUle
  have hBfg : (BLat Λ (lf D F0) F').FG := bt_fg_le hΛfg inf_le_left
  have hff := bt_spanO_ff Z hD p F0 Λ F' hXL hXL' hLift'.2 (Tu D u) (Tu D u')
  have hagree := (Z.agree p).2.2.2.2.2
  unfold locBBne
  set t := locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u') with ht
  have hEff : Submodule.span (D.s.atP p).Ep (Set.range t.f ∪ Set.range t.f') =
      Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (UUE Λ (lf D F0) F' : Set (VS D).V)) := by
    rw [← bt_spanEp_spanO Z p (Set.range t.f ∪ Set.range t.f'), hff, lattice₂, bt_spanEp_spanO Z p, UUE, spanE,
      bt_spanEp_spanE]
  rcases hs : (D.s.atP p).split with _ | sg
  ·
    have hMs : (Z.M p).split = none := by
      rcases hM : (Z.M p).split with _ | g'
      · rfl
      · rw [hM, hs] at hagree; exact hagree.elim
    have hnot : Loc.resChar p ∉ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by
      rw [← D.s_split p, hs]; simp
    have hgP : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
        P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∉ P.asIdeal :=
      fun P hP => by rw [bt_g_mem_iff p P hP]; exact hnot
    have hglob : BBneF D Λ (lf D F0) F' p ↔ ∃ P : HeightOneSpectrum (𝓞 D.host.E),
        P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal ∧
        (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ (lf D F0) F') ≠
          Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (UU Λ (lf D F0) F')) := by
      constructor
      · rintro ⟨P, hP, -, h2⟩; exact ⟨P, hP, h2 (hgP P hP)⟩
      · rintro ⟨P, hP, h⟩; exact ⟨P, hP, fun hg => absurd hg (hgP P hP), fun _ => h⟩
    rw [hglob, bt_glob_iff Z p hE _ _ hBfg hUUfg]
    have hMM : (locH Z p).MMfam t = Sum.elim t.f t.f' := by
      simp only [Loc.HermSp.MMfam, hMs]
    have hO : Submodule.span (Z.M p).L.O (Set.range ((locH Z p).MMfam t)) = lattice₂ D Z.M p (UU Λ (lf D F0) F') := by
      rw [hMM, Set.Sum.elim_range]; exact hff
    have hEp : Submodule.span (D.s.atP p).Ep (Set.range ((locH Z p).MMfam t)) =
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (UUE Λ (lf D F0) F' : Set (VS D).V)) := by
      rw [hMM, Set.Sum.elim_range]; exact hEff
    exact (bt_bbne_iff Z p hS t Λ (UU Λ (lf D F0) F') (UUE Λ (lf D F0) F') hΛfg rfl hO hEp
      (latP_mono Z p hUUle)).symm
  ·
    obtain ⟨g', hMs, hgq⟩ : ∃ g', (Z.M p).split = some g' ∧ g'.q = sg.q := by
      rcases hM : (Z.M p).split with _ | g'
      · rw [hM, hs] at hagree; exact hagree.elim
      · rw [hM, hs] at hagree; exact ⟨g', rfl, hagree.2⟩
    have hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by rw [← D.s_split p, hs]; rfl
    have hgP : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
        P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P.asIdeal :=
      fun P hP => (bt_g_mem_iff p P hP).2 hin
    have hXfg : (XLam Λ (lf D F0)).FG := bt_fg_le hΛfg inf_le_left
    have hMfg : (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')).FG := bt_Mplus_fg _ hXfg
    have hglob : BBneF D Λ (lf D F0) F' p ↔ ∃ P : HeightOneSpectrum (𝓞 D.host.E),
        P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal ∧
        (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (BLat Λ (lf D F0) F') ≠
          Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F'))) := by
      constructor
      · rintro ⟨P, hP, h1, -⟩; exact ⟨P, hP, h1 (hgP P hP) _ hξ⟩
      · rintro ⟨P, hP, h⟩
        refine ⟨P, hP, fun hg ξ' hξ' heq => h ?_, fun hng => absurd (hgP P hP) hng⟩
        rw [heq]; exact hMI hLift hFC P hg ξ' _ hξ' hξ
    rw [hglob, bt_glob_iff Z p hE _ _ hBfg hMfg]
    have hgS0 : gS D ≠ 0 := by simp [gS, (D.host.g_prime 0).ne_zero, (D.host.g_prime 1).ne_zero]
    have hMΛ : lattice₂ D Z.M p (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) ≤ lattice₂ D Z.M p Λ := by
      have hsup : lattice₂ D Z.M p (Λ ⊔ Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) = lattice₂ D Z.M p Λ := by
        refine (hE p _ _ (hΛfg.sup hMfg) hΛfg).2 ?_
        intro P hP
        have := P.isPrime
        exact localization_sup_of_le P.asIdeal (bt_Mplus_le_locP hgS0 Λ (lf D F0) F' hLift _ hξ P (hgP P hP))
      exact (latP_mono Z p le_sup_right).trans hsup.le
    have hφ := bt_typed_frFac Z hE hD p F0 Λ hΛfg hXL hFC hgP
    have hMM : (locH Z p).MMfam t = Sum.elim t.f
        (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((sg.q : (D.s.atP p).Fp)⁻¹) • (t.f' a - t.f a)) := by
      simp only [Loc.HermSp.MMfam, hMs, hgq]
    have hO : Submodule.span (Z.M p).L.O (Set.range ((locH Z p).MMfam t)) =
        lattice₂ D Z.M p (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) := by
      rw [hMM, Set.Sum.elim_range]
      exact bt_typed_O Z hD p F0 Λ F' (Tu D u) (Tu D u') hXL sg hs hφ
    have hq0 : (sg.q : (D.s.atP p).Fp) ≠ 0 := by
      intro h; exact sg.q_irr.ne_zero (Subtype.ext h)
    have hEp : Submodule.span (D.s.atP p).Ep (Set.range ((locH Z p).MMfam t)) =
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (UUE Λ (lf D F0) F' : Set (VS D).V)) := by
      rw [hMM, Set.Sum.elim_range]
      exact (bt_typed_Ep Z p F0 Λ F' (Tu D u) (Tu D u') _ hq0).trans hEff
    exact (bt_bbne_iff Z p hS t Λ _ (UUE Λ (lf D F0) F') hΛfg rfl hO hEp hMΛ).symm

end Main

section GenA

variable (Z : LocDat D) (p : PlF D)

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i`. Take `⟨lam, hlam⟩` from `LinearMap.exists_extend ((Finsupp.lapply i).comp hv.repr)`. Establish `hl : ∀ j, lam (v j) = if j = i then 1 else 0`. Introduce `j`.

Establish `hmem : v j ∈ Submodule.span D.host.E (Set.range v)` using `Submodule.subset_span ⟨j, rfl⟩`. Establish `h1` using `congrArg (fun f => f ⟨v j, hmem⟩) hlam`. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1`. Rewrite using `[h1, hv.repr_eq_single j _ rfl]`. Simplify using `[Finsupp.single_apply]`.

Set `Φ : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep` to `{ toFun := fun w => ∑ k, (D.s.atP p).ιE (lam ((VS D).frame k)) * w k map_add' := fun w w' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] map_smul' := fun a w => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `ring }`. Establish `key : ∀ x : (VS D).V, Φ (baseChange₂ D p x) = (D.s.atP p).ιE (lam x)`.

Introduce `x`. Use `show ∑ k, (D.s.atP p).ιE (lam ((VS D).frame k)) * (D.s.atP p).ιE ((VS D).frame.repr x k) = _`. Use `conv_rhs => rw [← (VS D).frame.sum_repr x]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, smul_eq_mul, map_mul, mul_comm]`. Establish `h2` using `congrArg Φ hc`. Rewrite `h2` using `[map_sum, map_zero]`. Simplify using `only [map_smul, key, hl, smul_eq_mul] at h2`. Simplify `h2` using `[apply_ite, Finset.sum_ite_eq']`.
-/
theorem bt_bc_linIndep {ι : Type*} [Fintype ι] (v : ι → (VS D).V) (hv : LinearIndependent D.host.E v) :
    LinearIndependent (D.s.atP p).Ep (fun i => baseChange₂ D p (v i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  obtain ⟨lam, hlam⟩ := LinearMap.exists_extend ((Finsupp.lapply i).comp hv.repr)
  have hl : ∀ j, lam (v j) = if j = i then 1 else 0 := by
    intro j
    have hmem : v j ∈ Submodule.span D.host.E (Set.range v) := Submodule.subset_span ⟨j, rfl⟩
    have h1 := congrArg (fun f => f ⟨v j, hmem⟩) hlam
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1, hv.repr_eq_single j _ rfl]
    simp [Finsupp.single_apply]
  let Φ : Vp D p →ₗ[(D.s.atP p).Ep] (D.s.atP p).Ep :=
    { toFun := fun w => ∑ k, (D.s.atP p).ιE (lam ((VS D).frame k)) * w k
      map_add' := fun w w' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a w => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring }
  have key : ∀ x : (VS D).V, Φ (baseChange₂ D p x) = (D.s.atP p).ιE (lam x) := by
    intro x
    show ∑ k, (D.s.atP p).ιE (lam ((VS D).frame k)) * (D.s.atP p).ιE ((VS D).frame.repr x k) = _
    conv_rhs => rw [← (VS D).frame.sum_repr x]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, smul_eq_mul, map_mul, mul_comm]
  have h2 := congrArg Φ hc
  rw [map_sum, map_zero] at h2
  simp only [map_smul, key, hl, smul_eq_mul] at h2
  simpa [apply_ite, Finset.sum_ite_eq'] using h2

/- English proof (translation)
Simplify using `only [LocFacts₂, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formP_smul_right (p : PlF D) (x y : Vp D p) (c : (D.s.atP p).Ep) :
    LocFacts₂ Z.M p x (c • y) = (Z.M p).L.cj c * LocFacts₂ Z.M p x y := by
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Simplify using `only [LocFacts₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formP_smul_left (p : PlF D) (x y : Vp D p) (c : (D.s.atP p).Ep) :
    LocFacts₂ Z.M p (c • x) y = c * LocFacts₂ Z.M p x y := by
  simp only [LocFacts₂, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GenA

section GenC

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

/- English proof (translation)
Establish `h1 : ∀ a, F.Xplus ≤ LinearMap.ker (S.hT (F.e a))`. Introduce `a`. Use `sup_le ?_ ?_` and prove the remaining obligations. Rewrite using `[FlagG.X, Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`.

Conclude with `F.e_iso a b`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `F.z_orth a`. Establish `h2 : F.X ≤ LinearMap.ker (S.hT.flip y)`. Rewrite using `[FlagG.X, Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `h1 a hy`. Conclude with `h2 hx`.
-/
theorem bt_X_orth {T : E} (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.Xplus) :
    S.hT x y = 0 := by
  have h1 : ∀ a, F.Xplus ≤ LinearMap.ker (S.hT (F.e a)) := by
    intro a
    refine sup_le ?_ ?_
    · rw [FlagG.X, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      exact F.e_iso a b
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact F.z_orth a
  have h2 : F.X ≤ LinearMap.ker (S.hT.flip y) := by
    rw [FlagG.X, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact h1 a hy
  exact h2 hx

/- English proof (translation)
Establish `h` using `S.herm.eq x y`. Rewrite `h` using `[bt_X_orth F hx hy]`. Simplify using `using h.symm`.
-/
theorem bt_X_orth' {T : E} (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.Xplus) :
    S.hT y x = 0 := by
  have h := S.herm.eq x y
  rw [bt_X_orth F hx hy] at h
  simpa using h.symm

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, rfl⟩`.
-/
theorem bt_e_mem_X {T : E} (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.X := Submodule.subset_span ⟨a, rfl⟩

/- English proof (translation)
The claim follows from `le_sup_left`.
-/
theorem bt_X_le_Xplus {T : E} (F : FlagG S r T) : F.X ≤ F.Xplus := le_sup_left

/- English proof (translation)
The claim follows from `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`.
-/
theorem bt_z_mem_Xplus {T : E} (F : FlagG S r T) : F.z ∈ F.Xplus :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

/- English proof (translation)
Break down `Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl` into its components or cases. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`. Conclude with `bt_X_le_Xplus F (bt_e_mem_X F b)`. Simplify using `only [FlagG.fvec, Fin.snoc_last]`. Conclude with `bt_z_mem_Xplus F`.
-/
theorem bt_fvec_mem {T : E} (F : FlagG S r T) (a : Fin (r + 1)) : F.fvec a ∈ F.Xplus := by
  rcases Fin.eq_castSucc_or_eq_last a with ⟨b, rfl⟩ | rfl
  · simp only [FlagG.fvec, Fin.snoc_castSucc]; exact bt_X_le_Xplus F (bt_e_mem_X F b)
  · simp only [FlagG.fvec, Fin.snoc_last]; exact bt_z_mem_Xplus F

/- English proof (translation)
Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`. Conclude with `bt_e_mem_X F a`.
-/
theorem bt_fvec_X {T : E} (F : FlagG S r T) (a : Fin r) : F.fvec a.castSucc ∈ F.X := by
  simp only [FlagG.fvec, Fin.snoc_castSucc]; exact bt_e_mem_X F a

/- English proof (translation)
Establish `key : frameAct F.fvec m b = F.fvec b + ∑ c ∈ Finset.univ.erase b, ((m c b : 𝓞 E) : E) • F.fvec c`. Rewrite using `[frameAct, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), h2 b]`. Simplify using the standard rewrite rules. Rewrite using `[key, add_sub_cancel_left]`. Use `Submodule.sum_mem _ fun c hc => ?_` and prove the remaining obligations.

Break down `lt_or_gt_of_ne (Finset.ne_of_mem_erase hc) with hcb | hcb` into its components or cases. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hc' : c.val < r` using `lt_of_lt_of_le hcb (Nat.lt_succ_iff.1 b.isLt)`. Establish `: c = (⟨c.val, hc'⟩ : Fin r).castSucc` using `Fin.ext rfl`. Rewrite using `[this]`.

Conclude with `bt_fvec_X F _`. Rewrite using `[h1 c b hcb]`. Simplify using the standard rewrite rules.
-/
theorem bt_frameAct_sub_X {T : E} (F : FlagG S r T) (m : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (h1 : ∀ a b, b < a → m a b = 0) (h2 : ∀ a, m a a = 1) (b : Fin (r + 1)) :
    frameAct F.fvec m b - F.fvec b ∈ F.X := by
  have key : frameAct F.fvec m b = F.fvec b +
      ∑ c ∈ Finset.univ.erase b, ((m c b : 𝓞 E) : E) • F.fvec c := by
    rw [frameAct, ← Finset.add_sum_erase _ _ (Finset.mem_univ b), h2 b]
    simp
  rw [key, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun c hc => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hc) with hcb | hcb
  · refine Submodule.smul_mem _ _ ?_
    have hc' : c.val < r := lt_of_lt_of_le hcb (Nat.lt_succ_iff.1 b.isLt)
    have : c = (⟨c.val, hc'⟩ : Fin r).castSucc := Fin.ext rfl
    rw [this]; exact bt_fvec_X F _
  · rw [h1 c b hcb]; simp

/- English proof (translation)
Establish `h1 : ∀ o : 𝓞 E, ∀ v : S.V, o • v = (o : E) • v` using `fun o v => (algebraMap_smul E o v).symm`. Introduce `x hx`. Take `⟨hxΛ, hxE⟩` from `Submodule.mem_inf.1 hx`. Establish `hsub : spanE S (XLam Λ F ⊔ Submodule.span (𝓞 E) {F.fl.z}) ≤ F.fl.Xplus`. Rewrite using `[spanE, Submodule.span_le]`.

Introduce `y hy`. Take `⟨w, hw, t, ht, rfl⟩` from `Submodule.mem_sup.1 hy`. Use `Submodule.add_mem _ (bt_X_le_Xplus F.fl (Submodule.mem_inf.1 hw).2) ?_` and prove the remaining obligations. Take `⟨o, rfl⟩` from `Submodule.mem_span_singleton.1 ht`. Rewrite using `[h1]`.

Conclude with `Submodule.smul_mem _ _ (bt_z_mem_Xplus F.fl)`. Establish `hxX : x ∈ F.fl.Xplus` using `hsub hxE`. Take `⟨w, hw, t, ht, hwt⟩` from `Submodule.mem_sup.1 hxX`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 ht`. Establish `horth : ∀ v ∈ F.fl.Xplus, v ∈ orth S (Xsp F)`.

Introduce `v hv`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `y hy`. Conclude with `bt_X_orth F.fl hy hv`. Establish `hcz : c • F.fl.z ∈ Lsub Λ F`.

Use `Submodule.mem_inf.2 ⟨?_, horth _ (Submodule.smul_mem _ _ (bt_z_mem_Xplus F.fl))⟩` and prove the remaining obligations. Establish `e : c • F.fl.z = x + (-w)` using `by rw [← hwt]; abel`. Rewrite using `[e]`. Use `Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hxΛ, horth x hxX⟩)) (Submodule.mem_sup_right (Submodule.neg_mem _ hw))` and prove the remaining obligations. Take `⟨o, ho⟩` from `hprim c hcz`.

Establish `hwΛ : w ∈ Λ`. Establish `e : w = x - o • F.fl.z` using `by rw [h1, ho, ← hwt]; abel`. Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ hxΛ (Submodule.smul_mem _ _ hz)`. Establish `e : x = w + o • F.fl.z` using `by rw [h1, ho, hwt]`.

Rewrite using `[e]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hwΛ, hw⟩)) (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))`.
-/
theorem bt_sat_Xplus (Λ : Submodule (𝓞 E) S.V) {T : E} (F : LFlag S r T) (hz : F.fl.z ∈ Λ)
    (hprim : ∀ c : E, c • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = c) :
    Λ ⊓ toO S (spanE S (XLam Λ F ⊔ Submodule.span (𝓞 E) {F.fl.z})) ≤
      XLam Λ F ⊔ Submodule.span (𝓞 E) {F.fl.z} := by
  have h1 : ∀ o : 𝓞 E, ∀ v : S.V, o • v = (o : E) • v := fun o v => (algebraMap_smul E o v).symm
  intro x hx
  obtain ⟨hxΛ, hxE⟩ := Submodule.mem_inf.1 hx
  have hsub : spanE S (XLam Λ F ⊔ Submodule.span (𝓞 E) {F.fl.z}) ≤ F.fl.Xplus := by
    rw [spanE, Submodule.span_le]
    intro y hy
    obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    refine Submodule.add_mem _ (bt_X_le_Xplus F.fl (Submodule.mem_inf.1 hw).2) ?_
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 ht
    rw [h1]; exact Submodule.smul_mem _ _ (bt_z_mem_Xplus F.fl)
  have hxX : x ∈ F.fl.Xplus := hsub hxE
  obtain ⟨w, hw, t, ht, hwt⟩ := Submodule.mem_sup.1 hxX
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 ht
  have horth : ∀ v ∈ F.fl.Xplus, v ∈ orth S (Xsp F) := by
    intro v hv
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro y hy
    exact bt_X_orth F.fl hy hv
  have hcz : c • F.fl.z ∈ Lsub Λ F := by
    refine Submodule.mem_inf.2 ⟨?_, horth _ (Submodule.smul_mem _ _ (bt_z_mem_Xplus F.fl))⟩
    have e : c • F.fl.z = x + (-w) := by rw [← hwt]; abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hxΛ, horth x hxX⟩))
      (Submodule.mem_sup_right (Submodule.neg_mem _ hw))
  obtain ⟨o, ho⟩ := hprim c hcz
  have hwΛ : w ∈ Λ := by
    have e : w = x - o • F.fl.z := by rw [h1, ho, ← hwt]; abel
    rw [e]; exact Submodule.sub_mem _ hxΛ (Submodule.smul_mem _ _ hz)
  have e : x = w + o • F.fl.z := by rw [h1, ho, hwt]
  rw [e]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hwΛ, hw⟩))
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))

end GenC

section GenB

variable (Z : LocDat D)

/- English proof (translation)
Unfold `sgnP`. Use `split`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
theorem sgnP_last₂ (p : PlF D) : sgnP D p (Fin.last D.R.rS) = 1 := by
  unfold sgnP
  split
  · simp
  · rfl

/- English proof (translation)
Unfold `sgnP'`. Use `split`. Conclude with `sgnP_last₂ p`. Simplify using the standard rewrite rules.
-/
theorem bt_sgnP'_last (p : PlF D) : sgnP' D p (Fin.last D.R.rS) = 1 := by
  unfold sgnP'
  split
  · exact sgnP_last₂ p
  · simp

/- English proof (translation)
The claim follows from `isUnit_iff_exists_inv.2 ⟨s, h⟩`.
-/
theorem bt_isUnit_sq {R : Type*} [CommRing R] {s : R} (h : s * s = 1) : IsUnit s :=
  isUnit_iff_exists_inv.2 ⟨s, h⟩

/- English proof (translation)
Rewrite `hv`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `c hc`. Establish `h1 : ∀ a, ∑ b, ((m a b : 𝓞 D.host.E) : D.host.E) * c b = 0`. Apply `hv` to reduce the goal to its premises. Rewrite using `[← hc]`.

Simplify using `only [frameAct, Finset.smul_sum, smul_smul, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Establish `h2 : (m.map (fun x : 𝓞 D.host.E => (x : D.host.E))).mulVec c = 0`.

Use function extensionality and compare the values at `a`. Simplify `h1 a` using `[Matrix.mulVec, dotProduct]`. Establish `hdet : (m.map (fun x : 𝓞 D.host.E => (x : D.host.E))).det ≠ 0`. Establish `e : (m.map (fun x : 𝓞 D.host.E => (x : D.host.E))).det = ((m.det : 𝓞 D.host.E) : D.host.E)`. Use `RingHom.map_det (algebraMap (𝓞 D.host.E) D.host.E) m` as an intermediate fact.

Simplify using `using this.symm`. Rewrite using `[e]`. Introduce `h0`. Establish `: m.det = 0` using `by exact_mod_cast h0`. Conclude with `hm.ne_zero this`.

Use `Matrix.eq_zero_of_mulVec_eq_zero hdet h2` as an intermediate fact. Introduce `b`. Conclude with `congrFun this b`.
-/
theorem bt_frameAct_linIndep {n : ℕ} (v : Fin n → (VS D).V) (hv : LinearIndependent D.host.E v)
    (m : Matrix (Fin n) (Fin n) (𝓞 D.host.E)) (hm : IsUnit m.det) :
    LinearIndependent D.host.E (frameAct v m) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro c hc
  have h1 : ∀ a, ∑ b, ((m a b : 𝓞 D.host.E) : D.host.E) * c b = 0 := by
    apply hv
    rw [← hc]
    simp only [frameAct, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
  have h2 : (m.map (fun x : 𝓞 D.host.E => (x : D.host.E))).mulVec c = 0 := by
    funext a; simpa [Matrix.mulVec, dotProduct] using h1 a
  have hdet : (m.map (fun x : 𝓞 D.host.E => (x : D.host.E))).det ≠ 0 := by
    have e : (m.map (fun x : 𝓞 D.host.E => (x : D.host.E))).det = ((m.det : 𝓞 D.host.E) : D.host.E) := by
      have := RingHom.map_det (algebraMap (𝓞 D.host.E) D.host.E) m
      simpa using this.symm
    rw [e]
    intro h0
    have : m.det = 0 := by exact_mod_cast h0
    exact hm.ne_zero this
  have := Matrix.eq_zero_of_mulVec_eq_zero hdet h2
  intro b; exact congrFun this b

/- English proof (translation)
Use `⟨fun a => ?_, hli, ?_⟩` and prove the remaining obligations. Establish `h1 : f a ∈ Submodule.span (Z.M p).L.O (Set.range f)` using `Submodule.subset_span ⟨a, rfl⟩`. Rewrite `h1` using `[hspan]`. Conclude with `latP_mono Z p hNΛ h1`. Introduce `x hx hxE`.

Establish `hE' : Submodule.span (D.s.atP p).Ep (Set.range f) = Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (spanE (VS D) N : Set (VS D).V))`. Rewrite using `[← bt_spanEp_spanO Z p (Set.range f), hspan, lattice₂, bt_spanEp_spanO Z p, spanE, bt_spanEp_spanE]`. Establish `hx2 : x ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (spanE (VS D) N)) : Set (Vp D p))`. Rewrite using `[hS p Λ _ hΛ]`. Conclude with `⟨hx, hE' ▸ hxE⟩`.

Rewrite using `[hspan]`. Conclude with `latP_mono Z p hsat hx2`.
-/
theorem bt_prim (hS : LocSatC D Z) (p : PlF D) {ι : Type} (f : ι → Vp D p)
    (Λ N : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ.FG)
    (hspan : Submodule.span (Z.M p).L.O (Set.range f) = lattice₂ D Z.M p N) (hNΛ : N ≤ Λ)
    (hsat : Λ ⊓ toO (VS D) (spanE (VS D) N) ≤ N) (hli : LinearIndependent (D.s.atP p).Ep f) :
    (locH Z p).Prim (lattice₂ D Z.M p Λ) f := by
  refine ⟨fun a => ?_, hli, ?_⟩
  · have h1 : f a ∈ Submodule.span (Z.M p).L.O (Set.range f) := Submodule.subset_span ⟨a, rfl⟩
    rw [hspan] at h1
    exact latP_mono Z p hNΛ h1
  · intro x hx hxE
    have hE' : Submodule.span (D.s.atP p).Ep (Set.range f) =
        Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (spanE (VS D) N : Set (VS D).V)) := by
      rw [← bt_spanEp_spanO Z p (Set.range f), hspan, lattice₂, bt_spanEp_spanO Z p, spanE, bt_spanEp_spanE]
    have hx2 : x ∈ (lattice₂ D Z.M p (Λ ⊓ toO (VS D) (spanE (VS D) N)) : Set (Vp D p)) := by
      rw [hS p Λ _ hΛ]; exact ⟨hx, hE' ▸ hxE⟩
    rw [hspan]
    exact latP_mono Z p hsat hx2

/- English proof (translation)
Rewrite using `[formP_smul_left, formP_smul_right, baseChangeAt_form Z.M p (Z.hcj p)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem formP_bc (p : PlF D) (a b : (D.s.atP p).Ep) (x y : (VS D).V) :
    LocFacts₂ Z.M p (a • baseChange₂ D p x) (b • baseChange₂ D p y) =
      a * (Z.M p).L.cj b * (D.s.atP p).ιE (brS (VS D) x y) := by
  rw [formP_smul_left, formP_smul_right, baseChangeAt_form Z.M p (Z.hcj p)]
  ring

end GenB

section GenMat

variable (Z : LocDat D)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_apply]`. Establish `e` using `(Finset.sum_image (s := Finset.univ) (g := Fin.castLE hl) (f := fun k => Z (Fin.castLE hl i) k * U k (Fin.castLE hl j)) (fun a _ b _ h => Fin.castLE_injective hl h))`. Rewrite using `[← e]`. Use `symm`.

Apply `Finset.sum_subset (Finset.subset_univ _)` to reduce the goal to its premises. Introduce `k _ hk`. Establish `hjk : Fin.castLE hl j < k`. Assume the negation of the conclusion as `hkj`. Use `push Not at hkj`.

Apply `hk` to reduce the goal to its premises. Use `Finset.mem_image.2 ⟨⟨k.val, lt_of_le_of_lt hkj j.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩` and prove the remaining obligations. Rewrite using `[hU k _ hjk, mul_zero]`.
-/
theorem bt_lead_tri {n l : ℕ} (hl : l ≤ n) {R : Type*} [CommRing R] (Z U : Matrix (Fin n) (Fin n) R)
    (hU : ∀ a b, b < a → U a b = 0) :
    (Z * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Z.submatrix (Fin.castLE hl) (Fin.castLE hl) * U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have e := (Finset.sum_image (s := Finset.univ) (g := Fin.castLE hl)
    (f := fun k => Z (Fin.castLE hl i) k * U k (Fin.castLE hl j))
    (fun a _ b _ h => Fin.castLE_injective hl h))
  rw [← e]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  have hjk : Fin.castLE hl j < k := by
    by_contra hkj
    push Not at hkj
    apply hk
    refine Finset.mem_image.2 ⟨⟨k.val, lt_of_le_of_lt hkj j.isLt⟩, Finset.mem_univ _, Fin.ext rfl⟩
  rw [hU k _ hjk, mul_zero]

/- English proof (translation)
Establish `hbt : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id`. Introduce `i j hij`. Conclude with `h1 _ _ hij`. Rewrite using `[Matrix.det_of_isUpperTriangular hbt]`. Simplify using `[h2]`.
-/
theorem bt_det_unitri_sub {n l : ℕ} (hl : l ≤ n) {R : Type*} [CommRing R] (U : Matrix (Fin n) (Fin n) R)
    (h1 : ∀ a b, b < a → U a b = 0) (h2 : ∀ a, U a a = 1) :
    (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
  have hbt : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).BlockTriangular id := by
    intro i j hij
    exact h1 _ _ hij
  rw [Matrix.det_of_isUpperTriangular hbt]
  simp [h2]

/- English proof (translation)
Simplify using `only [brS, frameAct, map_sum, map_smul, smul_eq_mul]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bt_brS_frameAct {n : ℕ} (v : Fin n → (VS D).V) (m : Matrix (Fin n) (Fin n) (𝓞 D.host.E)) (b : Fin n)
    (x : (VS D).V) :
    brS (VS D) (frameAct v m b) x = ∑ c, brS (VS D) (v c) x * ((m c b : 𝓞 D.host.E) : D.host.E) := by
  simp only [brS, frameAct, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/- English proof (translation)
Establish `hu` using `admissibility_witness_unitriangular Λ (lf D F0) F'`. Establish `hinv` using `inv_unitri _ hu.1 hu.2`. Use `set Ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E := (admXi D Λ (lf D F0) F')⁻¹.map (fun x : 𝓞 D.host.E => (x : D.host.E)) with hΞ`. Establish `hΞ1 : ∀ a b, b < a → Ξ a b = 0` using `fun a b h => by simp [hΞ, hinv.1 a b h]`. Establish `hΞ2 : ∀ a, Ξ a a = 1` using `fun a => by simp [hΞ, hinv.2 a]`.

Establish `hZ : (locH Z p).Zhat (locTerm Z p Λ (lf D F0) F' Tn T'n).f (locTerm Z p Λ (lf D F0) F' Tn T'n).f' = Matrix.diagonal (fun a => (Z.M p).L.cj (sgnP D p a * frFac Z.δ p a)) * (Formalism.MainNotions.S.Zhat F0 F'.fl * Ξ).map (D.s.atP p).ιE * Matrix.diagonal (fun b => sgnP' D p b * frFa …`. Use extensionality with `a b`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Use `show LocFacts₂ Z.M p ((sgnP' D p b * frFac Z.δ p b) • baseChange₂ D p (frameAct F'.fl.fvec (admXi D Λ (lf D F0) F')⁻¹ b)) ((sgnP D p a * frFac Z.δ p a) • baseChange₂ D p (F0.fvec a)) = _`. Rewrite using `[formP_bc, bt_brS_frameAct, Matrix.map_apply, Matrix.mul_apply]`.

Simplify using `only [Formalism.MainNotions.S.Zhat, hΞ, Matrix.map_apply]`. Expand and normalize the polynomial expressions, which then agree. Unfold `Loc.HermSp.Dl Formalism.MainNotions.S.Dl leadMinorE`. Rewrite using `[dif_pos hl, dif_pos hl, hZ]`. Establish `hsub : (Matrix.diagonal (fun a => (Z.M p).L.cj (sgnP D p a * frFac Z.δ p a)) * (Formalism.MainNotions.S.Zhat F0 F'.fl * Ξ).map (D.s.atP p).ιE * Matrix.diagonal (fun b => sgnP' D p b * frFac Z.δ p b)).submatrix (Fin.castLE hl) (Fin.castLE hl) = Matrix.diagonal (fun i => (Z.M p).L. …`.

Use extensionality with `i j`. Simplify using `only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]`. Establish `hdm : ∀ A : Matrix (Fin l) (Fin l) D.host.E, (A.map (D.s.atP p).ιE).det = (D.s.atP p).ιE A.det` using `fun A => (RingHom.map_det _ A).symm`. Rewrite using `[hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hdm, bt_lead_tri hl _ _ hΞ1, Matrix.det_mul, bt_det_unitri_sub hl _ hΞ1 hΞ2, mul_one]`. Establish `hp : (∏ i : Fin l, (Z.M p).L.cj (sgnP D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i)) * (sgnP' D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i))) = (∏ i : Fin l, (Z.M p).L.cj (sgnP D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i))) * ∏ i : Fin l, (sgnP' D p (Fin. …` using `Finset.prod_mul_distrib`.

Rewrite using `[hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bt_Dl_loc (p : PlF D) {T T' : ℕ} (F0 : FlagG (VS D) D.R.rS (T : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS (T' : D.host.E)) (Tn T'n : ℕ)
    (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    (locH Z p).Dl (locTerm Z p Λ (lf D F0) F' Tn T'n).f (locTerm Z p Λ (lf D F0) F' Tn T'n).f' l =
      (∏ i : Fin l, (Z.M p).L.cj (sgnP D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i)) *
        (sgnP' D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i))) *
      (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F0 F'.fl l) := by
  have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
  have hinv := inv_unitri _ hu.1 hu.2
  set Ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E :=
    (admXi D Λ (lf D F0) F')⁻¹.map (fun x : 𝓞 D.host.E => (x : D.host.E)) with hΞ
  have hΞ1 : ∀ a b, b < a → Ξ a b = 0 := fun a b h => by simp [hΞ, hinv.1 a b h]
  have hΞ2 : ∀ a, Ξ a a = 1 := fun a => by simp [hΞ, hinv.2 a]
  have hZ : (locH Z p).Zhat (locTerm Z p Λ (lf D F0) F' Tn T'n).f (locTerm Z p Λ (lf D F0) F' Tn T'n).f' =
      Matrix.diagonal (fun a => (Z.M p).L.cj (sgnP D p a * frFac Z.δ p a)) *
        (Formalism.MainNotions.S.Zhat F0 F'.fl * Ξ).map (D.s.atP p).ιE *
        Matrix.diagonal (fun b => sgnP' D p b * frFac Z.δ p b) := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    show LocFacts₂ Z.M p ((sgnP' D p b * frFac Z.δ p b) • baseChange₂ D p (frameAct F'.fl.fvec (admXi D Λ (lf D F0) F')⁻¹ b))
      ((sgnP D p a * frFac Z.δ p a) • baseChange₂ D p (F0.fvec a)) = _
    rw [formP_bc, bt_brS_frameAct, Matrix.map_apply, Matrix.mul_apply]
    simp only [Formalism.MainNotions.S.Zhat, hΞ, Matrix.map_apply]
    ring
  unfold Loc.HermSp.Dl Formalism.MainNotions.S.Dl leadMinorE
  rw [dif_pos hl, dif_pos hl, hZ]
  have hsub : (Matrix.diagonal (fun a => (Z.M p).L.cj (sgnP D p a * frFac Z.δ p a)) *
        (Formalism.MainNotions.S.Zhat F0 F'.fl * Ξ).map (D.s.atP p).ιE *
        Matrix.diagonal (fun b => sgnP' D p b * frFac Z.δ p b)).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      Matrix.diagonal (fun i => (Z.M p).L.cj (sgnP D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i))) *
        ((Formalism.MainNotions.S.Zhat F0 F'.fl * Ξ).submatrix (Fin.castLE hl) (Fin.castLE hl)).map (D.s.atP p).ιE *
        Matrix.diagonal (fun i => sgnP' D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply]
  have hdm : ∀ A : Matrix (Fin l) (Fin l) D.host.E, (A.map (D.s.atP p).ιE).det = (D.s.atP p).ιE A.det :=
    fun A => (RingHom.map_det _ A).symm
  rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    hdm, bt_lead_tri hl _ _ hΞ1, Matrix.det_mul, bt_det_unitri_sub hl _ hΞ1 hΞ2, mul_one]
  have hp : (∏ i : Fin l, (Z.M p).L.cj (sgnP D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i)) *
        (sgnP' D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i))) =
      (∏ i : Fin l, (Z.M p).L.cj (sgnP D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i))) *
        ∏ i : Fin l, (sgnP' D p (Fin.castLE hl i) * frFac Z.δ p (Fin.castLE hl i)) :=
    Finset.prod_mul_distrib
  rw [hp]
  ring

end GenMat

section GenDet

variable (Z : LocDat D)

/- English proof (translation)
Establish `h1 : IsUnit (sgnP D p a * frFac Z.δ p a)` using `(bt_isUnit_sq (localSign_sq p a)).mul (bt_frFac_unit Z p a)`. Establish `h2 : IsUnit (sgnP' D p a * frFac Z.δ p a)` using `(bt_isUnit_sq (sgnP'_sq p a)).mul (bt_frFac_unit Z p a)`. Conclude with `(h1.map (Z.M p).L.cj).mul h2`.
-/
theorem bt_loc_scal_unit (p : PlF D) (a : Fin (D.R.rS + 1)) :
    IsUnit ((Z.M p).L.cj (sgnP D p a * frFac Z.δ p a) * (sgnP' D p a * frFac Z.δ p a)) := by
  have h1 : IsUnit (sgnP D p a * frFac Z.δ p a) := (bt_isUnit_sq (localSign_sq p a)).mul (bt_frFac_unit Z p a)
  have h2 : IsUnit (sgnP' D p a * frFac Z.δ p a) := (bt_isUnit_sq (sgnP'_sq p a)).mul (bt_frFac_unit Z p a)
  exact (h1.map (Z.M p).L.cj).mul h2

/- English proof (translation)
Rewrite using `[bt_Dl_loc Z p F0 Λ F' Tn T'n _ le_rfl]`. Use `IsUnit.mul ?_ (bt_iota_unit p hD1)` and prove the remaining obligations. Conclude with `Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => bt_loc_scal_unit Z p _)`.
-/
theorem local_discriminant_is_unit (p : PlF D) {T T' : ℕ} (F0 : FlagG (VS D) D.R.rS (T : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS (T' : D.host.E)) (Tn T'n : ℕ)
    (hD1 : Formalism.MainNotions.S.Dl F0 F'.fl (D.R.rS + 1) ≠ 0) :
    IsUnit ((locH Z p).Dl (locTerm Z p Λ (lf D F0) F' Tn T'n).f (locTerm Z p Λ (lf D F0) F' Tn T'n).f'
      (D.R.rS + 1)) := by
  rw [bt_Dl_loc Z p F0 Λ F' Tn T'n _ le_rfl]
  refine IsUnit.mul ?_ (bt_iota_unit p hD1)
  exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
    (fun i _ => bt_loc_scal_unit Z p _)

/- English proof (translation)
Use `set c := ∏ i : Fin D.R.rS, (Z.M p).L.cj (sgnP D p i.castSucc * frFac Z.δ p i.castSucc) * (sgnP' D p i.castSucc * frFac Z.δ p i.castSucc) with hc`. Establish `hcu : IsUnit c` using `Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun i _ => bt_loc_scal_unit Z p _)`. Establish `h1 : (locH Z p).Dl (locTerm Z p Λ (lf D F0) F' T T').f (locTerm Z p Λ (lf D F0) F' T T').f' (D.R.rS + 1) = c * (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F0 F'.fl (D.R.rS + 1))`. Rewrite using `[bt_Dl_loc Z p F0 Λ F' T T' _ le_rfl, Fin.prod_univ_castSucc]`. Simplify using `only [Fin.castLE_rfl, id, sgnP_last₂, bt_sgnP'_last, bt_frFac_last, mul_one, map_one]`.

Both sides reduce to the same expression. Establish `h2 : (locH Z p).Dl (locTerm Z p Λ (lf D F0) F' T T').f (locTerm Z p Λ (lf D F0) F' T T').f' D.R.rS = c * (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F0 F'.fl D.R.rS)`. Rewrite using `[bt_Dl_loc Z p F0 Λ F' T T' _ (Nat.le_succ _)]`. Use `congr 1`. Establish `hcj : ∀ x : D.host.E, (Z.M p).L.cj ((D.s.atP p).ιE x) = (D.s.atP p).ιE (star x)` using `fun x => cj_iota (Z.hcj p) x`.

Establish `hG' : (locH Z p).Gdet (locTerm Z p Λ (lf D F0) F' T T').f (locTerm Z p Λ (lf D F0) F' T T').f' (T : (D.s.atP p).Fp) (T' : (D.s.atP p).Fp) = (c * (Z.M p).L.cj c) * (D.s.atP p).ιE (Gflag F0 F'.fl)`. Unfold `Loc.HermSp.Gdet Loc.HermSp.normE`. Rewrite using `[h1, h2]`. Simplify using `only [map_mul, hcj, Gflag, map_sub, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hG']`. Conclude with `((hcu.mul (hcu.map (Z.M p).L.cj)).mul (bt_iota_unit p hG)).ne_zero`.
-/
theorem bt_Gdet_ne (p : PlF D) {T T' : ℕ} (F0 : FlagG (VS D) D.R.rS (T : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS (T' : D.host.E))
    (hG : Gflag F0 F'.fl ≠ 0) :
    (locH Z p).Gdet (locTerm Z p Λ (lf D F0) F' T T').f (locTerm Z p Λ (lf D F0) F' T T').f'
      (T : (D.s.atP p).Fp) (T' : (D.s.atP p).Fp) ≠ 0 := by
  set c := ∏ i : Fin D.R.rS, (Z.M p).L.cj (sgnP D p i.castSucc * frFac Z.δ p i.castSucc) *
    (sgnP' D p i.castSucc * frFac Z.δ p i.castSucc) with hc
  have hcu : IsUnit c := Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one
    (fun i _ => bt_loc_scal_unit Z p _)
  have h1 : (locH Z p).Dl (locTerm Z p Λ (lf D F0) F' T T').f (locTerm Z p Λ (lf D F0) F' T T').f' (D.R.rS + 1) =
      c * (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F0 F'.fl (D.R.rS + 1)) := by
    rw [bt_Dl_loc Z p F0 Λ F' T T' _ le_rfl, Fin.prod_univ_castSucc]
    simp only [Fin.castLE_rfl, id, sgnP_last₂, bt_sgnP'_last, bt_frFac_last, mul_one, map_one]
    rfl
  have h2 : (locH Z p).Dl (locTerm Z p Λ (lf D F0) F' T T').f (locTerm Z p Λ (lf D F0) F' T T').f' D.R.rS =
      c * (D.s.atP p).ιE (Formalism.MainNotions.S.Dl F0 F'.fl D.R.rS) := by
    rw [bt_Dl_loc Z p F0 Λ F' T T' _ (Nat.le_succ _)]
    congr 1
  have hcj : ∀ x : D.host.E, (Z.M p).L.cj ((D.s.atP p).ιE x) = (D.s.atP p).ιE (star x) :=
    fun x => cj_iota (Z.hcj p) x
  have hG' : (locH Z p).Gdet (locTerm Z p Λ (lf D F0) F' T T').f (locTerm Z p Λ (lf D F0) F' T T').f'
      (T : (D.s.atP p).Fp) (T' : (D.s.atP p).Fp) = (c * (Z.M p).L.cj c) * (D.s.atP p).ιE (Gflag F0 F'.fl) := by
    unfold Loc.HermSp.Gdet Loc.HermSp.normE
    rw [h1, h2]
    simp only [map_mul, hcj, Gflag, map_sub, map_natCast]
    ring
  rw [hG']
  exact ((hcu.mul (hcu.map (Z.M p).L.cj)).mul (bt_iota_unit p hG)).ne_zero

end GenDet

section GenFrame

variable (Z : LocDat D)

/- English proof (translation)
Use `⟨?_, ?_, hDu p Λ hL hU⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `hL.fg`. Rewrite using `[← hs, latP_span]`. Conclude with `Submodule.fg_span (s.finite_toSet.image _)`. Rewrite using `[lattice₂, bt_spanEp_spanO Z p, ← bt_spanEp_spanE p Λ, hL.span_eq_top, Submodule.top_coe, Set.image_univ]`.

Conclude with `span_baseChange_eq_top p`.
-/
theorem bt_selfDual (hDu : LocUnimodC D Z) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (hL : Submodule.IsLattice D.host.E Λ) (hU : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ) :
    (locH Z p).IsSelfDual (lattice₂ D Z.M p Λ) := by
  refine ⟨?_, ?_, hDu p Λ hL hU⟩
  · obtain ⟨s, hs⟩ := hL.fg
    rw [← hs, latP_span]
    exact Submodule.fg_span (s.finite_toSet.image _)
  · rw [lattice₂, bt_spanEp_spanO Z p, ← bt_spanEp_spanE p Λ, hL.span_eq_top, Submodule.top_coe, Set.image_univ]
    exact span_baseChange_eq_top p

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, rfl⟩`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨b, rfl⟩`. Establish `e : v = frameAct (frameAct v m) m⁻¹`. Rewrite using `[bt_frameAct_comp, Matrix.mul_nonsing_inv m hm, bt_frameAct_one]`. Establish `eb : v b = frameAct (frameAct v m) m⁻¹ b` using `congrFun e b`. Rewrite using `[SetLike.mem_coe, eb]`.

Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
theorem bt_span_frameAct_eq {n : ℕ} (v : Fin n → (VS D).V) (m : Matrix (Fin n) (Fin n) (𝓞 D.host.E))
    (hm : IsUnit m.det) :
    Submodule.span D.host.E (Set.range (frameAct v m)) = Submodule.span D.host.E (Set.range v) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have e : v = frameAct (frameAct v m) m⁻¹ := by
      rw [bt_frameAct_comp, Matrix.mul_nonsing_inv m hm, bt_frameAct_one]
    have eb : v b = frameAct (frameAct v m) m⁻¹ b := congrFun e b
    rw [SetLike.mem_coe, eb]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Establish `hinv` using `inv_unitri ξ h1 h2`. Use `set W := frameAct F.fvec ξ⁻¹ with hW`. Establish `hWX : ∀ a, W a - F.fvec a ∈ F.X` using `fun a => bt_frameAct_sub_X F _ hinv.1 hinv.2 a`. Establish `hWp : ∀ a, W a ∈ F.Xplus` using `fun a => by`. Use `Submodule.add_mem _ (bt_X_le_Xplus F (hWX a)) (bt_fvec_mem F a)` as an intermediate fact.

Simplify using `using this`. Establish `hWc : ∀ a : Fin D.R.rS, W a.castSucc ∈ F.X` using `fun a => by`. Use `Submodule.add_mem _ (hWX a.castSucc) (bt_fvec_X F a)` as an intermediate fact. Simplify using `using this`. Establish `hWl : W (Fin.last D.R.rS) - F.z ∈ F.X`.

Use `hWX (Fin.last D.R.rS)` as an intermediate fact. Simplify `this` using `[FlagG.fvec]`. Establish `hspan` using `bt_span_frame_tri Z p hD F sg hsg ξ h1 h2`. Establish `hNΛ : XS D F ⊔ Submodule.span (𝓞 D.host.E) {F.z} ≤ Λ`. Use `sup_le ?_ ?_` and prove the remaining obligations.

Rewrite using `[← hXL]`. Conclude with `inf_le_left`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `hz`. Establish `hsat` using `bt_sat_Xplus Λ (⟨F, F.z⟩ : LFlag (VS D) D.R.rS (T : D.host.E)) hz hprim`.

Rewrite `hsat` using `[hXL]`. Establish `hliW : LinearIndependent D.host.E W` using `bt_frameAct_linIndep _ hli0 _ (bt_unitri_det _ hinv.1 hinv.2)`. Establish `hli1` using `bt_bc_linIndep p W hliW`. Establish `hu : ∀ a, IsUnit (sg a * frFac Z.δ p a)` using `fun a => (bt_isUnit_sq (hsg a)).mul (bt_frFac_unit Z p a)`. Establish `hli : LinearIndependent (D.s.atP p).Ep (fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (W a))`.

Establish `e : (fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (W a)) = (fun a => (hu a).unit) • (fun a => baseChange₂ D p (W a))`. Use function extensionality and compare the values at `a`. Simplify using `[Units.smul_def]`. Rewrite using `[e]`. Conclude with `hli1.units_smul _`.

Use `⟨bt_prim Z hS p _ Λ _ hΛ hspan hNΛ hsat hli, ?_, ?_, natCast_mem _ T, ?_⟩` and prove the remaining obligations. Introduce `a b hab show LocFacts₂ Z.M p _ _ = 0`. Rewrite using `[formP_bc]`. Establish `h0 : brS (VS D) (W a) (W b) = 0`. Break down `hab with ha | hb` into its components or cases.

Take `⟨a', rfl⟩` from `Fin.exists_castSucc_eq.2 ha`. Conclude with `bt_X_orth' F (hWc a') (hWp b)`. Take `⟨b', rfl⟩` from `Fin.exists_castSucc_eq.2 hb`. Conclude with `bt_X_orth F (hWc b') (hWp a)`. Rewrite using `[h0, map_zero, mul_zero]`.

Use `show LocFacts₂ Z.M p _ _ = _`. Rewrite using `[formP_bc, hsgl, bt_frFac_last, mul_one, map_one, mul_one, one_mul]`. Establish `e : W (Fin.last D.R.rS) = F.z + (W (Fin.last D.R.rS) - F.z)` using `by abel`. Establish `hx` using `hWl`. Use `set x := W (Fin.last D.R.rS) - F.z`.

Establish `hb : brS (VS D) (W (Fin.last D.R.rS)) (W (Fin.last D.R.rS)) = -(T : D.host.E)`. Rewrite using `[e]`. Simplify using `only [brS, map_add, LinearMap.add_apply]`. Rewrite using `[bt_X_orth F hx (bt_z_mem_Xplus F), bt_X_orth F hx (bt_X_le_Xplus F hx), bt_X_orth' F hx (bt_z_mem_Xplus F), F.z_norm]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hb, map_neg, map_natCast, map_natCast]`. Use `(D.s.atP p).char0` as an intermediate fact. Conclude with `hT` after adjusting the coercions.
-/
theorem bt_isFrame (hS : LocSatC D Z) (hD : LocDiffC D Z) (p : PlF D) {T : ℕ}
    (F : FlagG (VS D) D.R.rS (T : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ.FG)
    (hXL : XLam Λ ⟨F, F.z⟩ = XS D F) (hz : F.z ∈ Λ)
    (hprim : ∀ c : D.host.E, c • F.z ∈ Lsub Λ ⟨F, F.z⟩ → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c)
    (sg : Fin (D.R.rS + 1) → (D.s.atP p).Ep) (hsg : ∀ a, sg a * sg a = 1) (hsgl : sg (Fin.last D.R.rS) = 1)
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)) (h1 : ∀ a b, b < a → ξ a b = 0)
    (h2 : ∀ a, ξ a a = 1) (hli0 : LinearIndependent D.host.E F.fvec) (hT : T ≠ 0) :
    (locH Z p).IsFrame (lattice₂ D Z.M p Λ) D.R.rS
      (fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (frameAct F.fvec ξ⁻¹ a)) (T : (D.s.atP p).Fp) := by
  have hinv := inv_unitri ξ h1 h2
  set W := frameAct F.fvec ξ⁻¹ with hW
  have hWX : ∀ a, W a - F.fvec a ∈ F.X := fun a => bt_frameAct_sub_X F _ hinv.1 hinv.2 a
  have hWp : ∀ a, W a ∈ F.Xplus := fun a => by
    have := Submodule.add_mem _ (bt_X_le_Xplus F (hWX a)) (bt_fvec_mem F a)
    simpa using this
  have hWc : ∀ a : Fin D.R.rS, W a.castSucc ∈ F.X := fun a => by
    have := Submodule.add_mem _ (hWX a.castSucc) (bt_fvec_X F a)
    simpa using this
  have hWl : W (Fin.last D.R.rS) - F.z ∈ F.X := by
    have := hWX (Fin.last D.R.rS); simpa [FlagG.fvec] using this

  have hspan := bt_span_frame_tri Z p hD F sg hsg ξ h1 h2
  have hNΛ : XS D F ⊔ Submodule.span (𝓞 D.host.E) {F.z} ≤ Λ := by
    refine sup_le ?_ ?_
    · rw [← hXL]; exact inf_le_left
    · rw [Submodule.span_le, Set.singleton_subset_iff]; exact hz
  have hsat := bt_sat_Xplus Λ (⟨F, F.z⟩ : LFlag (VS D) D.R.rS (T : D.host.E)) hz hprim
  rw [hXL] at hsat
  have hliW : LinearIndependent D.host.E W :=
    bt_frameAct_linIndep _ hli0 _ (bt_unitri_det _ hinv.1 hinv.2)
  have hli1 := bt_bc_linIndep p W hliW
  have hu : ∀ a, IsUnit (sg a * frFac Z.δ p a) := fun a => (bt_isUnit_sq (hsg a)).mul (bt_frFac_unit Z p a)
  have hli : LinearIndependent (D.s.atP p).Ep (fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (W a)) := by
    have e : (fun a => (sg a * frFac Z.δ p a) • baseChange₂ D p (W a)) =
        (fun a => (hu a).unit) • (fun a => baseChange₂ D p (W a)) := by
      funext a; simp [Units.smul_def]
    rw [e]; exact hli1.units_smul _
  refine ⟨bt_prim Z hS p _ Λ _ hΛ hspan hNΛ hsat hli, ?_, ?_, natCast_mem _ T, ?_⟩
  · intro a b hab
    show LocFacts₂ Z.M p _ _ = 0
    rw [formP_bc]
    have h0 : brS (VS D) (W a) (W b) = 0 := by
      rcases hab with ha | hb
      · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 ha
        exact bt_X_orth' F (hWc a') (hWp b)
      · obtain ⟨b', rfl⟩ := Fin.exists_castSucc_eq.2 hb
        exact bt_X_orth F (hWc b') (hWp a)
    rw [h0, map_zero, mul_zero]
  · show LocFacts₂ Z.M p _ _ = _
    rw [formP_bc, hsgl, bt_frFac_last, mul_one, map_one, mul_one, one_mul]
    have e : W (Fin.last D.R.rS) = F.z + (W (Fin.last D.R.rS) - F.z) := by abel
    have hx := hWl
    set x := W (Fin.last D.R.rS) - F.z
    have hb : brS (VS D) (W (Fin.last D.R.rS)) (W (Fin.last D.R.rS)) = -(T : D.host.E) := by
      rw [e]
      simp only [brS, map_add, LinearMap.add_apply]
      rw [bt_X_orth F hx (bt_z_mem_Xplus F), bt_X_orth F hx (bt_X_le_Xplus F hx),
        bt_X_orth' F hx (bt_z_mem_Xplus F), F.z_norm]
      ring
    rw [hb, map_neg, map_natCast, map_natCast]
  · have := (D.s.atP p).char0
    exact_mod_cast hT

end GenFrame

section GenTerm

variable (Z : LocDat D)

/- English proof (translation)
Rewrite `h`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `key` using `h (Sum.elim (fun a => g (Sum.inl a) - g (Sum.inr a) * c) (fun b => g (Sum.inr b) * c)) (by`. Rewrite `hg`, the goal using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr] at hg ⊢`.

Rewrite using `[← hg]`. Simplify using `only [smul_sub, sub_smul, smul_smul, Finset.sum_sub_distrib]`. Use the proof step `abel)`. Take `⟨ci, hci⟩` from `isUnit_iff_exists_inv.1 hc`. Establish `hr : ∀ b, g (Sum.inr b) = 0`.

Introduce `b`. Use `key (Sum.inr b)` as an intermediate fact. Simplify using `only [Sum.elim_inr] at this`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `(a | b)`.

Use `key (Sum.inl a)` as an intermediate fact. Simplify using `only [Sum.elim_inl, hr a, zero_mul, sub_zero] at this`. Conclude with `this`. Conclude with `hr b`.
-/
theorem bt_li_shear {ι R M : Type*} [Fintype ι] [CommRing R] [AddCommGroup M] [Module R M] (x y : ι → M) (c : R)
    (hc : IsUnit c) (h : LinearIndependent R (Sum.elim x y)) :
    LinearIndependent R (Sum.elim x (fun i => c • (y i - x i))) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg
  have key := h (Sum.elim (fun a => g (Sum.inl a) - g (Sum.inr a) * c) (fun b => g (Sum.inr b) * c)) (by
    rw [Fintype.sum_sum_type] at hg ⊢
    simp only [Sum.elim_inl, Sum.elim_inr] at hg ⊢
    rw [← hg]
    simp only [smul_sub, sub_smul, smul_smul, Finset.sum_sub_distrib]
    abel)
  obtain ⟨ci, hci⟩ := isUnit_iff_exists_inv.1 hc
  have hr : ∀ b, g (Sum.inr b) = 0 := by
    intro b
    have := key (Sum.inr b)
    simp only [Sum.elim_inr] at this
    calc g (Sum.inr b) = g (Sum.inr b) * c * ci := by rw [mul_assoc, hci, mul_one]
      _ = 0 := by rw [this, zero_mul]
  rintro (a | b)
  · have := key (Sum.inl a)
    simp only [Sum.elim_inl, hr a, zero_mul, sub_zero] at this
    exact this
  · exact hr b

/- English proof (translation)
Establish `hgS0 : gS D ≠ 0` using `by simp [gS, (D.host.g_prime 0).ne_zero, (D.host.g_prime 1).ne_zero]`. Establish `hXfg : (XLam Λ (lf D F0)).FG` using `bt_fg_le hΛfg inf_le_left`. Establish `hMfg : (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')).FG` using `bt_Mplus_fg _ hXfg`. Establish `hsup : lattice₂ D Z.M p (Λ ⊔ Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) = lattice₂ D Z.M p Λ`. Use `(hE p _ _ (hΛfg.sup hMfg) hΛfg).2 ?_` and prove the remaining obligations.

Introduce `P hP`. Use `P.isPrime` as an intermediate fact. Conclude with `localization_sup_of_le P.asIdeal (bt_Mplus_le_locP hgS0 Λ (lf D F0) F' hLift _ hξ P (hgP P hP))`. Conclude with `(latP_mono Z p le_sup_right).trans hsup.le`.
-/
theorem bt_typed_Mle (hE : LocEqC D Z) (p : PlF D) {T T' : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS T') (hΛfg : Λ.FG)
    (hLift : IsLift Λ (lf D F0)) (hξ : AdmWit Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F'))
    (hgP : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P.asIdeal) :
    lattice₂ D Z.M p (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) ≤ lattice₂ D Z.M p Λ := by
  have hgS0 : gS D ≠ 0 := by simp [gS, (D.host.g_prime 0).ne_zero, (D.host.g_prime 1).ne_zero]
  have hXfg : (XLam Λ (lf D F0)).FG := bt_fg_le hΛfg inf_le_left
  have hMfg : (Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')).FG := bt_Mplus_fg _ hXfg
  have hsup : lattice₂ D Z.M p (Λ ⊔ Mplus Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')) = lattice₂ D Z.M p Λ := by
    refine (hE p _ _ (hΛfg.sup hMfg) hΛfg).2 ?_
    intro P hP
    have := P.isPrime
    exact localization_sup_of_le P.asIdeal (bt_Mplus_le_locP hgS0 Λ (lf D F0) F' hLift _ hξ P (hgP P hP))
  exact (latP_mono Z p le_sup_right).trans hsup.le

/- English proof (translation)
The claim follows from `(Formalism.L2.SG.GramJoint.Tu_pos D u).ne'`.
-/
theorem bt_Tu_ne (u : D.what₂.Word) : Tu D u ≠ 0 := (Formalism.L2.SG.GramJoint.Tu_pos D u).ne'

/- English proof (translation)
Establish `hsq : (Loc.resChar p) ^ 2 ∣ D.modT`. Establish `h0 : (Loc.resChar p) ∣ D.host.g 0 * D.host.g 1`. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at hin`. Apply the tactic sequence `rcases hin with h | h <;> rw [h]`. Conclude with `dvd_mul_right _ _`.

Conclude with `dvd_mul_left _ _`. Conclude with `(pow_dvd_pow_of_dvd h0 2).mul_left _`. Use `(D.s.atP p).ellPrime` as an intermediate fact. Establish `hℓ : 1 < Loc.resChar p` using `(Fact.out : (Loc.resChar p).Prime).one_lt`. Establish `hd : Loc.resChar p ∣ D.modT` using `(dvd_pow_self _ two_ne_zero).trans hsq`.

Use `⟨fun h => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `D.T_modEq_of_dvd u hd`. Establish `h2 : (D.mem u).A.T % Loc.resChar p = 0` using `Nat.mod_eq_zero_of_dvd h`. Rewrite `h1` using `[Nat.ModEq, Nat.mod_eq_of_lt hℓ]`. Conclude with `absurd (h2.symm.trans h1) zero_ne_one`.

Establish `h1` using `D.T_modEq_of_dvd u hsq`. Establish `h2` using `D.T_modEq_of_dvd u' hsq`. Establish `h3 : (D.mem u').A.T ≡ (D.mem u).A.T [MOD (Loc.resChar p) ^ 2]` using `h2.trans h1.symm`. Take `⟨k, hk⟩` from `(Nat.modEq_iff_dvd.1 h3)`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Simplify using `only [Tu]`. Move the coercions through the operations in `at hk ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bt_T_typed (p : PlF D) (hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)) (u u' : D.what₂.Word) :
    ¬ Loc.resChar p ∣ Tu D u ∧ ∃ k : ℤ, ((Tu D u : ℤ) - (Tu D u' : ℤ)) = (Loc.resChar p : ℤ) ^ 2 * k := by
  have hsq : (Loc.resChar p) ^ 2 ∣ D.modT := by
    have h0 : (Loc.resChar p) ∣ D.host.g 0 * D.host.g 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hin
      rcases hin with h | h <;> rw [h]
      · exact dvd_mul_right _ _
      · exact dvd_mul_left _ _
    exact (pow_dvd_pow_of_dvd h0 2).mul_left _
  have := (D.s.atP p).ellPrime
  have hℓ : 1 < Loc.resChar p := (Fact.out : (Loc.resChar p).Prime).one_lt
  have hd : Loc.resChar p ∣ D.modT := (dvd_pow_self _ two_ne_zero).trans hsq
  refine ⟨fun h => ?_, ?_⟩
  · have h1 := D.T_modEq_of_dvd u hd
    have h2 : (D.mem u).A.T % Loc.resChar p = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.ModEq, Nat.mod_eq_of_lt hℓ] at h1
    exact absurd (h2.symm.trans h1) zero_ne_one
  · have h1 := D.T_modEq_of_dvd u hsq
    have h2 := D.T_modEq_of_dvd u' hsq
    have h3 : (D.mem u').A.T ≡ (D.mem u).A.T [MOD (Loc.resChar p) ^ 2] := h2.trans h1.symm
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd.1 h3)
    refine ⟨k, ?_⟩
    simp only [Tu]
    push_cast at hk ⊢
    linarith

/- English proof (translation)
Establish `hmem : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal)` using `by rwa [bt_natCast_mem_iff]`. Establish `hv : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F (n : 𝓞 D.host.F)) = 1` using `(HeightOneSpectrum.valuation_eq_one_iff_notMem p).2 hmem`. Rewrite `hv` using `[map_natCast]`. Establish `h1 : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp)`. Use `((D.s.atP p).val 1 (n : D.host.F)).2 (by rw [hv, map_one])` as an intermediate fact.

Simplify using `using this`. Establish `hn0 : (n : (D.s.atP p).Fp) ≠ 0`. Use `(D.s.atP p).char0` as an intermediate fact. Establish `: n ≠ 0` using `by rintro rfl; exact hn (dvd_zero _)`. Conclude with `this` after adjusting the coercions.

Establish `hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ 𝒪[(D.s.atP p).Fp]`. Rewrite using `[Valuation.mem_integer_iff, ← Valuation.vle_one_iff]`. Conclude with `(ValuativeRel.inv_vle_one hn0).2 h1`. Conclude with `⟨⟨_, hinv⟩, inv_mul_cancel₀ hn0⟩`.
-/
theorem bt_natF_unit (p : PlF D) (n : ℕ) (hn : ¬ Loc.resChar p ∣ n) :
    ∃ w : 𝒪[(D.s.atP p).Fp], (w : (D.s.atP p).Fp) * (n : (D.s.atP p).Fp) = 1 := by
  have hmem : ¬ ((n : 𝓞 D.host.F) ∈ p.asIdeal) := by rwa [bt_natCast_mem_iff]
  have hv : p.valuation D.host.F (algebraMap (𝓞 D.host.F) D.host.F (n : 𝓞 D.host.F)) = 1 :=
    (HeightOneSpectrum.valuation_eq_one_iff_notMem p).2 hmem
  rw [map_natCast] at hv
  have h1 : (1 : (D.s.atP p).Fp) ≤ᵥ (n : (D.s.atP p).Fp) := by
    have := ((D.s.atP p).val 1 (n : D.host.F)).2 (by rw [hv, map_one])
    simpa using this
  have hn0 : (n : (D.s.atP p).Fp) ≠ 0 := by
    have := (D.s.atP p).char0
    have : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
    exact_mod_cast this
  have hinv : (n : (D.s.atP p).Fp)⁻¹ ∈ 𝒪[(D.s.atP p).Fp] := by
    rw [Valuation.mem_integer_iff, ← Valuation.vle_one_iff]
    exact (ValuativeRel.inv_vle_one hn0).2 h1
  exact ⟨⟨_, hinv⟩, inv_mul_cancel₀ hn0⟩

end GenTerm

section GenMain

variable (Z : LocDat D)

/- English proof (translation)
Establish `h` using `(Formalism.L2.SG.GramJoint.gramIndep D.host.E (VS D) D.R.rS _ _ F0 F'.fl hG).1`. Rewrite `h` using `[Formalism.L2.SG.GramJoint.pairVec, linearIndependent_sum]`. Simplify using `using h`.
-/
theorem bt_pair_li {T T' : ℕ} (F0 : FlagG (VS D) D.R.rS (T : D.host.E))
    (F' : LFlag (VS D) D.R.rS (T' : D.host.E)) (hG : Gflag F0 F'.fl ≠ 0) :
    LinearIndependent D.host.E F0.fvec ∧ LinearIndependent D.host.E F'.fl.fvec ∧
      Disjoint (Submodule.span D.host.E (Set.range F0.fvec)) (Submodule.span D.host.E (Set.range F'.fl.fvec)) := by
  have h := (Formalism.L2.SG.GramJoint.gramIndep D.host.E (VS D) D.R.rS _ _ F0 F'.fl hG).1
  rw [Formalism.L2.SG.GramJoint.pairVec, linearIndependent_sum] at h
  simpa using h

/- English proof (translation)
Take `⟨h1, h2, hd⟩` from `bt_pair_li F0 F' hG`. Establish `hu` using `admissibility_witness_unitriangular Λ (lf D F0) F'`. Establish `hinv` using `inv_unitri _ hu.1 hu.2`. Establish `hdet` using `bt_unitri_det _ hinv.1 hinv.2`. Establish `hWli : LinearIndependent D.host.E (frameAct F'.fl.fvec (admXi D Λ (lf D F0) F')⁻¹)` using `bt_frameAct_linIndep _ h2 _ hdet`.

Establish `hsum : LinearIndependent D.host.E (Sum.elim F0.fvec (frameAct F'.fl.fvec (admXi D Λ (lf D F0) F')⁻¹))`. Rewrite using `[linearIndependent_sum]`. Use `⟨by simpa using h1, by simpa using hWli, ?_⟩` and prove the remaining obligations. Simplify using `only [Sum.elim_comp_inl, Sum.elim_comp_inr]`. Rewrite using `[bt_span_frameAct_eq _ _ hdet]`.

Conclude with `hd`. Establish `hbc` using `bt_bc_linIndep p _ hsum`. Establish `hu' : ∀ i : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1), IsUnit (Sum.elim (fun a => sgnP D p a * frFac Z.δ p a) (fun b => sgnP' D p b * frFac Z.δ p b) i)`. Introduce and unpack `(a | b)`. Conclude with `(bt_isUnit_sq (localSign_sq p a)).mul (bt_frFac_unit Z p a)`.

Conclude with `(bt_isUnit_sq (sgnP'_sq p b)).mul (bt_frFac_unit Z p b)`. Establish `e : Sum.elim (locTerm Z p Λ (lf D F0) F' Tn T'n).f (locTerm Z p Λ (lf D F0) F' Tn T'n).f' = (fun i => (hu' i).unit) • (fun i => baseChange₂ D p (Sum.elim F0.fvec (frameAct F'.fl.fvec (admXi D Λ (lf D F0) F')⁻¹) i))`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases i with a | b <;> rfl`. Rewrite using `[e]`.

Conclude with `hbc.units_smul _`.
-/
theorem bt_ff_li (p : PlF D) {T T' : ℕ} (F0 : FlagG (VS D) D.R.rS (T : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS (T' : D.host.E)) (Tn T'n : ℕ)
    (hG : Gflag F0 F'.fl ≠ 0) :
    LinearIndependent (D.s.atP p).Ep (Sum.elim (locTerm Z p Λ (lf D F0) F' Tn T'n).f
      (locTerm Z p Λ (lf D F0) F' Tn T'n).f') := by
  obtain ⟨h1, h2, hd⟩ := bt_pair_li F0 F' hG
  have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
  have hinv := inv_unitri _ hu.1 hu.2
  have hdet := bt_unitri_det _ hinv.1 hinv.2
  have hWli : LinearIndependent D.host.E (frameAct F'.fl.fvec (admXi D Λ (lf D F0) F')⁻¹) :=
    bt_frameAct_linIndep _ h2 _ hdet
  have hsum : LinearIndependent D.host.E (Sum.elim F0.fvec (frameAct F'.fl.fvec (admXi D Λ (lf D F0) F')⁻¹)) := by
    rw [linearIndependent_sum]
    refine ⟨by simpa using h1, by simpa using hWli, ?_⟩
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [bt_span_frameAct_eq _ _ hdet]
    exact hd
  have hbc := bt_bc_linIndep p _ hsum
  have hu' : ∀ i : Fin (D.R.rS + 1) ⊕ Fin (D.R.rS + 1),
      IsUnit (Sum.elim (fun a => sgnP D p a * frFac Z.δ p a) (fun b => sgnP' D p b * frFac Z.δ p b) i) := by
    rintro (a | b)
    · exact (bt_isUnit_sq (localSign_sq p a)).mul (bt_frFac_unit Z p a)
    · exact (bt_isUnit_sq (sgnP'_sq p b)).mul (bt_frFac_unit Z p b)
  have e : Sum.elim (locTerm Z p Λ (lf D F0) F' Tn T'n).f (locTerm Z p Λ (lf D F0) F' Tn T'n).f' =
      (fun i => (hu' i).unit) • (fun i => baseChange₂ D p (Sum.elim F0.fvec
        (frameAct F'.fl.fvec (admXi D Λ (lf D F0) F')⁻¹) i)) := by
    funext i
    rcases i with a | b <;> rfl
  rw [e]; exact hbc.units_smul _

/- English proof (translation)
Establish `hFix` using `hR.2.1`. Establish `hΛfg : Λ.FG` using `hFix.1.fg`. Establish `hagree` using `(Z.agree p).2.2.2.2.2`. Choose the witnesses or unpack the hypotheses as in `⟨sg, hs, hgq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.q = sg.q := by`. Break down `hs : (D.s.atP p).split with _ | sg` into its components or cases.

Rewrite `hagree` using `[hg, hs]`. Conclude with `hagree.elim`. Rewrite `hagree` using `[hg, hs]`. Conclude with `⟨sg, rfl, hagree.2⟩`. Establish `hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)` using `by rw [← D.s_split p, hs]; rfl`.

Establish `hgP : ∀ P : HeightOneSpectrum (𝓞 D.host.E), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P.asIdeal` using `fun P hP => (bt_g_mem_iff p P hP).2 hin`. Establish `hφ` using `bt_typed_frFac Z hE hD p F0 Λ hΛfg hR.2.2 hFix.2.2.2 hgP`. Establish `hO` using `bt_typed_O Z hD p F0 Λ F' (Tu D u) (Tu D u') hR.2.2 sg hs hφ`. Establish `hξ : AdmWit Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F')`. Unfold `admXi`.

Rewrite using `[dif_pos hPD.2.1]`. Conclude with `hPD.2.1.choose_spec`. Establish `hMΛ` using `bt_typed_Mle Z hE p F0 Λ F' hΛfg hFix.2.2.1 hξ hgP`. Apply `hMΛ` to reduce the goal to its premises. Rewrite using `[← hO, hgq]`.

Conclude with `Submodule.subset_span (Or.inr ⟨b, rfl⟩)`.
-/
theorem bt_typed_second (hE : LocEqC D Z) (hD : LocDiffC D Z) (p : PlF D) {u u' : D.what₂.Word}
    (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V)
    (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (hR : IsRowLat D F0 Λ) (hPD : PD D Λ (lf D F0) u' F')
    (g : Loc.SplitG (Z.M p).L) (hg : (Z.M p).split = some g) (b : Fin (D.R.rS + 1)) :
    algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) •
      ((locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' b - (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f b)
        ∈ lattice₂ D Z.M p Λ := by
  have hFix := hR.2.1
  have hΛfg : Λ.FG := hFix.1.fg
  have hagree := (Z.agree p).2.2.2.2.2
  obtain ⟨sg, hs, hgq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.q = sg.q := by
    rcases hs : (D.s.atP p).split with _ | sg
    · rw [hg, hs] at hagree; exact hagree.elim
    · rw [hg, hs] at hagree; exact ⟨sg, rfl, hagree.2⟩
  have hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by rw [← D.s_split p, hs]; rfl
  have hgP : ∀ P : HeightOneSpectrum (𝓞 D.host.E),
      P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = p.asIdeal → (gS D : 𝓞 D.host.E) ∈ P.asIdeal :=
    fun P hP => (bt_g_mem_iff p P hP).2 hin
  have hφ := bt_typed_frFac Z hE hD p F0 Λ hΛfg hR.2.2 hFix.2.2.2 hgP
  have hO := bt_typed_O Z hD p F0 Λ F' (Tu D u) (Tu D u') hR.2.2 sg hs hφ
  have hξ : AdmWit Λ (gS D) (lf D F0) F' (admXi D Λ (lf D F0) F') := by
    unfold admXi; rw [dif_pos hPD.2.1]; exact hPD.2.1.choose_spec
  have hMΛ := bt_typed_Mle Z hE p F0 Λ F' hΛfg hFix.2.2.1 hξ hgP
  apply hMΛ
  rw [← hO, hgq]
  exact Submodule.subset_span (Or.inr ⟨b, rfl⟩)

/- English proof (translation)
Introduce `h` and use `g.q_irr.ne_zero (Subtype.ext h)`.
-/
theorem bt_q_ne (p : PlF D) (g : Loc.SplitG (Z.M p).L) : (g.q : (D.s.atP p).Fp) ≠ 0 :=
  fun h => g.q_irr.ne_zero (Subtype.ext h)

/- English proof (translation)
Take `⟨h1, h2, -⟩` from `bt_pair_li F0 F' hG`. Establish `hFix` using `hR.2.1`. Establish `hΛfg : Λ.FG` using `hFix.1.fg`. Establish `hu` using `admissibility_witness_unitriangular Λ (lf D F0) F'`. Establish `hf : (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f = fun a => (sgnP D p a * frFac Z.δ p a) • baseChange₂ D p (frameAct F0.fvec (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))⁻¹ a)`.

Use function extensionality and compare the values at `a`. Rewrite using `[inv_one, bt_frameAct_one]`. Both sides reduce to the same expression. Establish `hF1 : (locH Z p).IsFrame (lattice₂ D Z.M p Λ) D.R.rS (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f ((Tu D u : ℕ) : (D.s.atP p).Fp)`. Rewrite using `[hf]`.

Conclude with `bt_isFrame Z hS hD p F0 Λ hΛfg hR.2.2 hFix.2.2.1.1 hFix.2.2.2.2 (sgnP D p) (localSign_sq p) (sgnP_last₂ p) 1 (fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm) (fun a => Matrix.one_apply_eq a) h1 (bt_Tu_ne u)`. Establish `hF2 : (locH Z p).IsFrame (lattice₂ D Z.M p Λ) D.R.rS (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' ((Tu D u' : ℕ) : (D.s.atP p).Fp)` using `bt_isFrame Z hS hD p F'.fl Λ hΛfg hPD.2.2.2 hPD.1.1 hPD.2.2.1.2 (sgnP' D p) (sgnP'_sq p) (bt_sgnP'_last p) _ hu.1 hu.2 h2 (bt_Tu_ne u')`. Use `⟨bt_selfDual Z hDu p Λ hFix.1 hFix.2.1, hF1, hF2, local_discriminant_is_unit Z p F0 Λ F' _ _ hD1, bt_Gdet_ne Z p F0 Λ F' hG, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Establish `hagree` using `(Z.agree p).2.2.2.2.2`.

Choose the witnesses or unpack the hypotheses as in `⟨sg, hs, hgq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.q = sg.q := by`. Break down `hs : (D.s.atP p).split with _ | sg` into its components or cases. Rewrite `hagree` using `[hg, hs]`. Conclude with `hagree.elim`. Rewrite `hagree` using `[hg, hs]`.

Conclude with `⟨sg, rfl, hagree.2⟩`. Establish `hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ)` using `by rw [← D.s_split p, hs]; rfl`. Take `⟨hTu, k, hk⟩` from `bt_T_typed p hin u u'`. Take `⟨hTu', -⟩` from `bt_T_typed p hin u' u`. Establish `hq : (g.q : (D.s.atP p).Fp) = (Loc.resChar p : (D.s.atP p).Fp)` using `by rw [hgq]; exact sg.q_eq`.

Use `⟨⟨(bt_natF_unit p _ hTu).choose, (bt_natF_unit p _ hTu').choose, (bt_natF_unit p _ hTu).choose_spec, (bt_natF_unit p _ hTu').choose_spec⟩, ⟨(k : 𝒪[(D.s.atP p).Fp]), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`. Use `congrArg (fun z : ℤ => (z : (D.s.atP p).Fp)) hk` as an intermediate fact. Move the coercions through the operations in `at this`. Use `show ((Tu D u : ℕ) : (D.s.atP p).Fp) - ((Tu D u' : ℕ) : (D.s.atP p).Fp) = (Loc.resChar p : (D.s.atP p).Fp) ^ 2 * ((k : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp)`.

Simplify using `using this`. Introduce `b`. Establish `hmem` using `bt_typed_second Z hE hD p F0 Λ F' hR hPD g hg b`. Establish `e : (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' b - (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f b = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) • (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) • ((locTerm Z p Λ (lf D F0) F' ( …`. Rewrite using `[smul_smul, ← map_mul, mul_inv_cancel₀ (bt_q_ne Z p g), map_one, one_smul]`.

Rewrite using `[e]`. Conclude with `Submodule.subset_span ⟨_, hmem, rfl⟩`.
-/
theorem bt_isTerm (hE : LocEqC D Z) (hS : LocSatC D Z) (hD : LocDiffC D Z) (hDu : LocUnimodC D Z) (p : PlF D)
    {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hR : IsRowLat D F0 Λ) (hPD : PD D Λ (lf D F0) u' F') (hG : Gflag F0 F'.fl ≠ 0)
    (hD1 : Formalism.MainNotions.S.Dl F0 F'.fl (D.R.rS + 1) ≠ 0) :
    (locH Z p).IsTerm (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
  obtain ⟨h1, h2, -⟩ := bt_pair_li F0 F' hG
  have hFix := hR.2.1
  have hΛfg : Λ.FG := hFix.1.fg
  have hu := admissibility_witness_unitriangular Λ (lf D F0) F'
  have hf : (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f = fun a => (sgnP D p a * frFac Z.δ p a) •
      baseChange₂ D p (frameAct F0.fvec (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))⁻¹ a) := by
    funext a; rw [inv_one, bt_frameAct_one]; rfl
  have hF1 : (locH Z p).IsFrame (lattice₂ D Z.M p Λ) D.R.rS (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f
      ((Tu D u : ℕ) : (D.s.atP p).Fp) := by
    rw [hf]
    exact bt_isFrame Z hS hD p F0 Λ hΛfg hR.2.2 hFix.2.2.1.1 hFix.2.2.2.2 (sgnP D p) (localSign_sq p)
      (sgnP_last₂ p) 1 (fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm) (fun a => Matrix.one_apply_eq a) h1
      (bt_Tu_ne u)
  have hF2 : (locH Z p).IsFrame (lattice₂ D Z.M p Λ) D.R.rS (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f'
      ((Tu D u' : ℕ) : (D.s.atP p).Fp) :=
    bt_isFrame Z hS hD p F'.fl Λ hΛfg hPD.2.2.2 hPD.1.1 hPD.2.2.1.2 (sgnP' D p) (sgnP'_sq p) (bt_sgnP'_last p) _
      hu.1 hu.2 h2 (bt_Tu_ne u')
  refine ⟨bt_selfDual Z hDu p Λ hFix.1 hFix.2.1, hF1, hF2, local_discriminant_is_unit Z p F0 Λ F' _ _ hD1,
    bt_Gdet_ne Z p F0 Λ F' hG, ?_⟩
  intro g hg
  have hagree := (Z.agree p).2.2.2.2.2
  obtain ⟨sg, hs, hgq⟩ : ∃ sg, (D.s.atP p).split = some sg ∧ g.q = sg.q := by
    rcases hs : (D.s.atP p).split with _ | sg
    · rw [hg, hs] at hagree; exact hagree.elim
    · rw [hg, hs] at hagree; exact ⟨sg, rfl, hagree.2⟩
  have hin : Loc.resChar p ∈ ({D.host.g 0, D.host.g 1} : Finset ℕ) := by rw [← D.s_split p, hs]; rfl
  obtain ⟨hTu, k, hk⟩ := bt_T_typed p hin u u'
  obtain ⟨hTu', -⟩ := bt_T_typed p hin u' u
  have hq : (g.q : (D.s.atP p).Fp) = (Loc.resChar p : (D.s.atP p).Fp) := by rw [hgq]; exact sg.q_eq
  refine ⟨⟨(bt_natF_unit p _ hTu).choose, (bt_natF_unit p _ hTu').choose, (bt_natF_unit p _ hTu).choose_spec,
    (bt_natF_unit p _ hTu').choose_spec⟩, ⟨(k : 𝒪[(D.s.atP p).Fp]), ?_⟩, ?_⟩
  · rw [hq]
    have := congrArg (fun z : ℤ => (z : (D.s.atP p).Fp)) hk
    push_cast at this
    show ((Tu D u : ℕ) : (D.s.atP p).Fp) - ((Tu D u' : ℕ) : (D.s.atP p).Fp) =
      (Loc.resChar p : (D.s.atP p).Fp) ^ 2 * ((k : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp)
    simpa using this
  · intro b
    have hmem := bt_typed_second Z hE hD p F0 Λ F' hR hPD g hg b
    have e : (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' b - (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f b =
        algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (g.q : (D.s.atP p).Fp) •
        (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) •
          ((locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' b - (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f b)) := by
      rw [smul_smul, ← map_mul, mul_inv_cancel₀ (bt_q_ne Z p g), map_one, one_smul]
    rw [e]
    exact Submodule.subset_span ⟨_, hmem, rfl⟩

set_option maxHeartbeats 800000 in

/- English proof (translation)
Establish `hFix` using `hR.2.1`. Establish `key : ∀ p : PlF D, (locH Z p).IsGeneric (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ↔ ¬ locBBne Z p Λ (lf D F0) F' (Tu D u) (Tu D u')`. Introduce `p`. Establish `hT` using `bt_isTerm Z hE hS hD hDu p F0 Λ F' hR hPD hG hD1`. Establish `hmem : ∀ i, (locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) i ∈ lattice₂ D Z.M p Λ`.

Break down `hM : (Z.M p).split with _ | g` into its components or cases. Establish `hMM : (locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) = Sum.elim (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f'`. Simplify using `only [Loc.HermSp.MMfam, hM]`. Rewrite using `[hMM]`. Introduce and unpack `(a | b)`.

Conclude with `hT.2.1.1.1 a`. Conclude with `hT.2.2.1.1.1 b`. Establish `hMM : (locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) = Sum.elim (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) • ((locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' a - (locTerm Z p …`. Simplify using `only [Loc.HermSp.MMfam, hM]`. Rewrite using `[hMM]`.

Introduce and unpack `(a | b)`. Conclude with `hT.2.1.1.1 a`. Conclude with `bt_typed_second Z hE hD p F0 Λ F' hR hPD g hM b`. Establish `hli : LinearIndependent (D.s.atP p).Ep ((locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')))`. Establish `hff` using `bt_ff_li Z p F0 Λ F' (Tu D u) (Tu D u') hG`.

Break down `hM : (Z.M p).split with _ | g` into its components or cases. Establish `hMM : (locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) = Sum.elim (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f'`. Simplify using `only [Loc.HermSp.MMfam, hM]`. Rewrite using `[hMM]`. Conclude with `hff`.

Establish `hMM : (locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) = Sum.elim (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f (fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) • ((locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' a - (locTerm Z p …`. Simplify using `only [Loc.HermSp.MMfam, hM]`. Rewrite using `[hMM]`. Conclude with `bt_li_shear _ _ _ (bt_alg_unit p (inv_ne_zero (bt_q_ne Z p g))) hff`. Unfold `Loc.HermSp.IsGeneric Loc.HermSp.Prim locBBne LocNG.BBne`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, -, -, h⟩ ⟨v, hv, hvE, hvO⟩`. Conclude with `hvO (h v hv hvE)`. Introduce `h`. Use `⟨hT, hmem, hli, fun x hx hxE => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hn`. Conclude with `h ⟨x, hx, hxE, hn⟩`. Rewrite using `[forall_congr' key]`. Prove the components needed by the constructor for the conclusion. Introduce `hg p hbb`.

Rewrite `hbb` using `[← bbTie_core Z hE hS hD u u' F0 Λ F' hR hPD hMI p]`. Take `⟨P, -, hP⟩` from `hbb`. Conclude with `not_BBneP_of_generic hg P hP`. Introduce `h`. Use `generic_of_not_BBneP hMI hFix.2.2.1 hFix.2.2.2 hPD.2.1 fun P hP => ?_` and prove the remaining obligations.

Conclude with `h (below D P) ((bbTie_core Z hE hS hD u u' F0 Λ F' hR hPD hMI (below D P)).1 ⟨P, rfl, hP⟩)`.
-/
theorem frameGenLoc_core (hE : LocEqC D Z) (hS : LocSatC D Z) (hD : LocDiffC D Z) (hDu : LocUnimodC D Z)
    {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hR : IsRowLat D F0 Λ) (hPD : PD D Λ (lf D F0) u' F') (hMI : MplusIndep Λ (lf D F0) (gS D) F')
    (hG : Gval (lf D F0) F' ≠ 0) (hD1 : Dr1 (lf D F0) F' ≠ 0) :
    IsGeneric Λ (gS D) (lf D F0) F' ↔
      ∀ p : PlF D, (locH Z p).IsGeneric (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
  have hFix := hR.2.1
  have key : ∀ p : PlF D, (locH Z p).IsGeneric (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) ↔
      ¬ locBBne Z p Λ (lf D F0) F' (Tu D u) (Tu D u') := by
    intro p
    have hT := bt_isTerm Z hE hS hD hDu p F0 Λ F' hR hPD hG hD1
    have hmem : ∀ i, (locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) i ∈ lattice₂ D Z.M p Λ := by
      rcases hM : (Z.M p).split with _ | g
      · have hMM : (locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) =
            Sum.elim (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f
              (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' := by
          simp only [Loc.HermSp.MMfam, hM]
        rw [hMM]
        rintro (a | b)
        · exact hT.2.1.1.1 a
        · exact hT.2.2.1.1.1 b
      · have hMM : (locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) =
            Sum.elim (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f (fun a =>
              algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) •
                ((locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' a -
                  (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f a)) := by
          simp only [Loc.HermSp.MMfam, hM]
        rw [hMM]
        rintro (a | b)
        · exact hT.2.1.1.1 a
        · exact bt_typed_second Z hE hD p F0 Λ F' hR hPD g hM b
    have hli : LinearIndependent (D.s.atP p).Ep
        ((locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u'))) := by
      have hff := bt_ff_li Z p F0 Λ F' (Tu D u) (Tu D u') hG
      rcases hM : (Z.M p).split with _ | g
      · have hMM : (locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) =
            Sum.elim (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f
              (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' := by
          simp only [Loc.HermSp.MMfam, hM]
        rw [hMM]; exact hff
      · have hMM : (locH Z p).MMfam (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) =
            Sum.elim (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f (fun a =>
              algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((g.q : (D.s.atP p).Fp)⁻¹) •
                ((locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f' a -
                  (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')).f a)) := by
          simp only [Loc.HermSp.MMfam, hM]
        rw [hMM]
        exact bt_li_shear _ _ _ (bt_alg_unit p (inv_ne_zero (bt_q_ne Z p g))) hff
    unfold Loc.HermSp.IsGeneric Loc.HermSp.Prim locBBne LocNG.BBne
    constructor
    · rintro ⟨-, -, -, h⟩ ⟨v, hv, hvE, hvO⟩
      exact hvO (h v hv hvE)
    · intro h
      refine ⟨hT, hmem, hli, fun x hx hxE => ?_⟩
      by_contra hn
      exact h ⟨x, hx, hxE, hn⟩
  rw [forall_congr' key]
  constructor
  · intro hg p hbb
    rw [← bbTie_core Z hE hS hD u u' F0 Λ F' hR hPD hMI p] at hbb
    obtain ⟨P, -, hP⟩ := hbb
    exact not_BBneP_of_generic hg P hP
  · intro h
    refine generic_of_not_BBneP hMI hFix.2.2.1 hFix.2.2.2 hPD.2.1 fun P hP => ?_
    exact h (below D P) ((bbTie_core Z hE hS hD u u' F0 Λ F' hR hPD hMI (below D P)).1 ⟨P, rfl, hP⟩)

end GenMain

end BBTie

open BBTie

/- English proof (translation)
The claim follows from `bbTie_core Z hE hS hD`.
-/
theorem bbTie_of (Z : LocDat D) (hE : LocEqC D Z) (hS : LocSatC D Z) (hD : LocDiffC D Z) : BBTie D Z :=
  bbTie_core Z hE hS hD

/- English proof (translation)
The claim follows from `frameGenLoc_core Z hE hS hD hDu F0 Λ F' hR hPD hMI hG hD1`.
-/
theorem frameGenLoc_of (Z : LocDat D) (hE : LocEqC D Z) (hS : LocSatC D Z) (hD : LocDiffC D Z)
    (hDu : LocUnimodC D Z) {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hR : IsRowLat D F0 Λ) (hPD : PD D Λ (lf D F0) u' F') (hMI : MplusIndep Λ (lf D F0) (gS D) F')
    (hG : Gval (lf D F0) F' ≠ 0) (hD1 : Dr1 (lf D F0) F' ≠ 0) :
    IsGeneric Λ (gS D) (lf D F0) F' ↔
      ∀ p : PlF D, (locH Z p).IsGeneric (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) :=
  frameGenLoc_core Z hE hS hD hDu F0 Λ F' hR hPD hMI hG hD1

section Tied

variable (D) in

def LocTied : Prop := ∀ p : PlF D, Nonempty (Formalism.L2.S.LocIso (D.s.atP p) (Formalism.L2.S.locC D p))

variable (D) in

def LocEqT : Prop := LocTied D → ∀ Z : LocDat D, LocEqC D Z

variable (D) in

def LocSatT : Prop := LocTied D → ∀ Z : LocDat D, LocSatC D Z

variable (D) in

def LocDiffT : Prop := LocTied D → ∀ Z : LocDat D, LocDiffC D Z

variable (D) in

def LocUnimodT : Prop := LocTied D → ∀ Z : LocDat D, LocUnimodC D Z

/- English proof (translation)
The claim follows from `bbTie_of Z (hE hT Z) (hS hT Z) (hD hT Z)`.
-/
theorem bbTie_of_tied (hT : LocTied D) (hE : LocEqT D) (hS : LocSatT D) (hD : LocDiffT D) (Z : LocDat D) :
    BBTie D Z :=
  bbTie_of Z (hE hT Z) (hS hT Z) (hD hT Z)

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (D.host.E →+* ℂ)` from `inferInstance`. Conclude with `frameGenLoc_of Z hE hS hD hDu F0 Λ F' hR hPD hMI hG (hDN D.host.E (VS D) τ (D.sp.cm.cmUnram.2.1 τ) (D.sp.Y_sig 0) D.R.rS (Tu D u) (Tu D u') (Formalism.L2.SG.GramJoint.sig_hS D τ) (Formalism.L2.SG.GramJoint.Tu_pos D u) (Formalism.L2.SG.GramJoint.Tu_pos D u') F0 F'.fl hG)`.
-/
theorem frameGenLoc_of' (hDN : Formalism.L2.SG.GramJoint.DNeZeroAt) (Z : LocDat D) (hE : LocEqC D Z)
    (hS : LocSatC D Z) (hD : LocDiffC D Z) (hDu : LocUnimodC D Z)
    {u u' : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))
    (hR : IsRowLat D F0 Λ) (hPD : PD D Λ (lf D F0) u' F') (hMI : MplusIndep Λ (lf D F0) (gS D) F')
    (hG : Gval (lf D F0) F' ≠ 0) :
    IsGeneric Λ (gS D) (lf D F0) F' ↔
      ∀ p : PlF D, (locH Z p).IsGeneric (locTerm Z p Λ (lf D F0) F' (Tu D u) (Tu D u')) := by
  obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  exact frameGenLoc_of Z hE hS hD hDu F0 Λ F' hR hPD hMI hG
    (hDN D.host.E (VS D) τ (D.sp.cm.cmUnram.2.1 τ) (D.sp.Y_sig 0) D.R.rS (Tu D u) (Tu D u')
      (Formalism.L2.SG.GramJoint.sig_hS D τ) (Formalism.L2.SG.GramJoint.Tu_pos D u) (Formalism.L2.SG.GramJoint.Tu_pos D u') F0 F'.fl hG)

end Tied

end Formalism.L2.SG.Pf
