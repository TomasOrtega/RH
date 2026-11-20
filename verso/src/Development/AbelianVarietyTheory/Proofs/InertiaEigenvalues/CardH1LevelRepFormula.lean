import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import ReciprocityTheory.Hypotheses.GalCohDefs
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg.SeqCount

open Formalism.NG ReciprocityTheory.ChartRestriction.T2

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module O M]

/- English proof (translation)
Proceed by induction on `n generalizing m with`. Consider the case `zero => exact ⟨m, by rw [pow_zero, one_smul]⟩`. Consider the case `succ k ih`. Take `⟨a, ha⟩` from `ih m`. Take `⟨b, hb⟩` from `hdiv a`.

Conclude with `⟨b, by rw [pow_succ, mul_smul, hb, ha]⟩`.
-/
theorem exists_pow_smul_eq {ϖ : O} (hdiv : ∀ m : M, ∃ m' : M, ϖ • m' = m) (n : ℕ) (m : M) :
    ∃ m' : M, ϖ ^ n • m' = m := by
  induction n generalizing m with
  | zero => exact ⟨m, by rw [pow_zero, one_smul]⟩
  | succ k ih =>
    obtain ⟨a, ha⟩ := ih m
    obtain ⟨b, hb⟩ := hdiv a
    exact ⟨b, by rw [pow_succ, mul_smul, hb, ha]⟩

/- English proof (translation)
Introduce `_ _ h` and use `Lev.ext h`.
-/
theorem lev_val_injective {c : O} : Function.Injective (Lev.val : Lev M c → M) :=
  fun _ _ h => Lev.ext h

def levelCocycleToModuleCocycle (ρ : Representation O G M) (c : O) : Z1 (levRep ρ c) →ₗ[O] coZ1s ρ where
  toFun f := ⟨fun g => (f.1 g).val, fun g h => by
    have := ((mem_Z1_iff_cocycle _ _).1 f.2).2 g h
    show (f.1 (g * h)).val = (f.1 g).val + ρ g (f.1 h).val
    rw [this, Lev.val_add, levRep_val]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def levelH1ToModuleH1 (ρ : Representation O G M) (c : O) : H1 (levRep ρ c) →ₗ[O] H1z ρ :=
  Submodule.mapQ _ _ (levelCocycleToModuleCocycle ρ c) (by
    intro f hf
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hf
    exact ⟨m.val, funext fun g => by
      have h2 : f.1 g = levRep ρ c g m - m := hm g
      show ρ g m.val - m.val = (f.1 g).val
      rw [h2]; rfl⟩)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valuation_H1_mk (ρ : Representation O G M) (c : O) (f : Z1 (levRep ρ c)) :
    levelH1ToModuleH1 ρ c (Submodule.Quotient.mk f) = Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c f) := rfl

/- English proof (translation)
Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `⟨levelCocycleToModuleCocycle ρ c f, ?_, rfl⟩` and prove the remaining obligations. Use `show IsLocallyConstant (fun g => (f.1 g).val)`. Establish `h1 : IsLocallyConstant f.1` using `(IsLocallyConstant.iff_continuous f.1).2 ((mem_Z1_iff_cocycle _ _).1 f.2).1`. Conclude with `h1.comp _`.
-/
theorem valuation_H1_mem (ρ : Representation O G M) (c : O) (x : H1 (levRep ρ c)) : levelH1ToModuleH1 ρ c x ∈ HcLC ρ := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨levelCocycleToModuleCocycle ρ c f, ?_, rfl⟩
  show IsLocallyConstant (fun g => (f.1 g).val)
  have h1 : IsLocallyConstant f.1 := (IsLocallyConstant.iff_continuous f.1).2 ((mem_Z1_iff_cocycle _ _).1 f.2).1
  exact h1.comp _

/- English proof (translation)
Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[valuation_H1_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Use `⟨0, funext fun g => ?_⟩` and prove the remaining obligations. Use `show ρ g 0 - 0 = c • (f.1 g).val`. Rewrite using `[Lev.smul_val, map_zero, sub_zero]`.
-/
theorem smul_valuation_H1 (ρ : Representation O G M) (c : O) (x : H1 (levRep ρ c)) : c • levelH1ToModuleH1 ρ c x = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [valuation_H1_mk, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨0, funext fun g => ?_⟩
  show ρ g 0 - 0 = c • (f.1 g).val
  rw [Lev.smul_val, map_zero, sub_zero]

def phi (ρ : Representation O G M) (c : O) :
    H1 (levRep ρ c) →ₗ[O] LinearMap.ker (c • LinearMap.id : HcLC ρ →ₗ[O] HcLC ρ) :=
  LinearMap.codRestrict _ (LinearMap.codRestrict (HcLC ρ) (levelH1ToModuleH1 ρ c) (valuation_H1_mem ρ c)) (fun x => by
    rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    exact Subtype.ext (smul_valuation_H1 ρ c x))

/- English proof (translation)
Introduce and unpack `⟨⟨y, hy⟩, hk⟩`. Take `⟨z, hz, rfl⟩` from `hy`. Establish `hk' : c • (Submodule.mkQ _ z : H1z ρ) = 0`. Use `congrArg Subtype.val (LinearMap.mem_ker.1 hk)` as an intermediate fact. Simplify using `using this`.

Rewrite `hk'` using `[← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Take `⟨m, hm⟩` from `hk'`. Take `⟨m', hm'⟩` from `hdiv m`. Establish `hz2 : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h)` using `z.2`. Establish `hzlc : IsLocallyConstant (z.1 : G → M)` using `hz`.

Set `w : G → M` to `fun g => z.1 g - (ρ g m' - m')`. Establish `hw : ∀ g, c • w g = 0` using `fun g => by`. Establish `h1 : ρ g m - m = c • z.1 g` using `congrFun hm g`. Use `show c • (z.1 g - (ρ g m' - m')) = 0`. Rewrite using `[smul_sub, smul_sub, ← map_smul (ρ g) c m', hm', h1, sub_self]`.

Establish `hwlc : IsLocallyConstant w` using `hzlc.sub ((hlc m').sub (IsLocallyConstant.const m'))`. Establish `hwc : ∀ g h, w (g * h) = w g + ρ g (w h)` using `fun g h => by show z.1 (g * h) - (ρ (g * h) m' - m') = (z.1 g - (ρ g m' - m')) + ρ g (z.1 h - (ρ h m' - m'))`. Rewrite using `[hz2, map_mul, Module.End.mul_apply, map_sub, map_sub]`. Normalize the expressions using the abelian group laws. Establish `hf : (fun g => Lev.mk (w g) (hw g) : G → Lev M c) ∈ Z1 (levRep ρ c)`.

Use `(mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => Lev.ext ?_⟩` and prove the remaining obligations. Conclude with `(IsLocallyConstant.desc _ Lev.val hwlc lev_val_injective).continuous`. Use `show w (g * h) = w g + ρ g (w h)`. Conclude with `hwc g h`. Use `⟨Submodule.Quotient.mk ⟨_, hf⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `show levelH1ToModuleH1 ρ c (Submodule.Quotient.mk ⟨_, hf⟩) = Submodule.mkQ _ z`. Rewrite using `[valuation_H1_mk, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Use `⟨-m', funext fun g => ?_⟩` and prove the remaining obligations.

Use `show ρ g (-m') - -m' = (z.1 g - (ρ g m' - m')) - z.1 g`. Rewrite using `[map_neg]`. Normalize the expressions using the abelian group laws.
-/
theorem phi_surjective (ρ : Representation O G M) (c : O) (hdiv : ∀ m : M, ∃ m' : M, c • m' = m)
    (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) : Function.Surjective (phi ρ c) := by
  rintro ⟨⟨y, hy⟩, hk⟩
  obtain ⟨z, hz, rfl⟩ := hy
  have hk' : c • (Submodule.mkQ _ z : H1z ρ) = 0 := by
    have := congrArg Subtype.val (LinearMap.mem_ker.1 hk)
    simpa using this
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hk'
  obtain ⟨m, hm⟩ := hk'
  obtain ⟨m', hm'⟩ := hdiv m
  have hz2 : ∀ g h, z.1 (g * h) = z.1 g + ρ g (z.1 h) := z.2
  have hzlc : IsLocallyConstant (z.1 : G → M) := hz
  let w : G → M := fun g => z.1 g - (ρ g m' - m')
  have hw : ∀ g, c • w g = 0 := fun g => by
    have h1 : ρ g m - m = c • z.1 g := congrFun hm g
    show c • (z.1 g - (ρ g m' - m')) = 0
    rw [smul_sub, smul_sub, ← map_smul (ρ g) c m', hm', h1, sub_self]
  have hwlc : IsLocallyConstant w := hzlc.sub ((hlc m').sub (IsLocallyConstant.const m'))
  have hwc : ∀ g h, w (g * h) = w g + ρ g (w h) := fun g h => by
    show z.1 (g * h) - (ρ (g * h) m' - m') = (z.1 g - (ρ g m' - m')) + ρ g (z.1 h - (ρ h m' - m'))
    rw [hz2, map_mul, Module.End.mul_apply, map_sub, map_sub]
    abel
  have hf : (fun g => Lev.mk (w g) (hw g) : G → Lev M c) ∈ Z1 (levRep ρ c) := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => Lev.ext ?_⟩
    · exact (IsLocallyConstant.desc _ Lev.val hwlc lev_val_injective).continuous
    · show w (g * h) = w g + ρ g (w h)
      exact hwc g h
  refine ⟨Submodule.Quotient.mk ⟨_, hf⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  show levelH1ToModuleH1 ρ c (Submodule.Quotient.mk ⟨_, hf⟩) = Submodule.mkQ _ z
  rw [valuation_H1_mk, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨-m', funext fun g => ?_⟩
  show ρ g (-m') - -m' = (z.1 g - (ρ g m' - m')) - z.1 g
  rw [map_neg]
  abel

def preInv (ρ : Representation O G M) (c : O) : Submodule O M :=
  ρ.invariants.comap (c • LinearMap.id : M →ₗ[O] M)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_preInv {ρ : Representation O G M} {c : O} (m : M) :
    m ∈ preInv ρ c ↔ ∀ g, ρ g (c • m) = c • m := Iff.rfl

/- English proof (translation)
Rewrite using `[smul_sub, ← map_smul (ρ g) c, (mem_preInv _).1 m.2 g, sub_self]`.
-/
theorem smul_cob_eq_zero {ρ : Representation O G M} {c : O} (m : preInv ρ c) (g : G) :
    c • (ρ g m.1 - m.1) = 0 := by
  rw [smul_sub, ← map_smul (ρ g) c, (mem_preInv _).1 m.2 g, sub_self]

def cobLev (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    preInv ρ c →ₗ[O] Z1 (levRep ρ c) where
  toFun m := ⟨fun g => Lev.mk (ρ g m.1 - m.1) (smul_cob_eq_zero m g), by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => Lev.ext ?_⟩
    · exact (IsLocallyConstant.desc _ Lev.val ((hlc m.1).sub (IsLocallyConstant.const m.1))
        lev_val_injective).continuous
    · show ρ (g * h) m.1 - m.1 = (ρ g m.1 - m.1) + ρ g (ρ h m.1 - m.1)
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel⟩
  map_add' a b := Subtype.ext (funext fun g => Lev.ext (by
    show ρ g (a.1 + b.1) - (a.1 + b.1) = (ρ g a.1 - a.1) + (ρ g b.1 - b.1)
    rw [map_add]; abel))
  map_smul' r a := Subtype.ext (funext fun g => Lev.ext (by
    show ρ g (r • a.1) - r • a.1 = r • (ρ g a.1 - a.1)
    rw [map_smul, smul_sub]))

def kappa (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    preInv ρ c →ₗ[O] H1 (levRep ρ c) :=
  (Submodule.mkQ _) ∘ₗ cobLev ρ c hlc

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h1 : (Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c f) : H1z ρ) = 0` using `hx`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero]`.

Take `⟨m, hm⟩` from `h1`. Establish `hm' : ∀ g, ρ g m - m = (f.1 g).val` using `fun g => congrFun hm g`. Establish `hP : m ∈ preInv ρ c` using `(mem_preInv m).2 fun g => by`. Use `congrArg (c • ·) (hm' g)` as an intermediate fact. Simplify using `only [Lev.smul_val, smul_sub] at this`.

Rewrite using `[map_smul, ← sub_eq_zero, ← this]`. Use `⟨⟨m, hP⟩, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk (cobLev ρ c hlc ⟨m, hP⟩) = Submodule.Quotient.mk f`. Use `congr 1`. Conclude with `Subtype.ext (funext fun g => Lev.ext (hm' g))`.

Introduce and unpack `x ⟨m, rfl⟩`. Rewrite using `[LinearMap.mem_ker]`. Use `show (Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c (cobLev ρ c hlc m)) : H1z ρ) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨m.1, rfl⟩`.
-/
theorem ker_valuation_H1 (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    LinearMap.ker (levelH1ToModuleH1 ρ c) = LinearMap.range (kappa ρ c hlc) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : (Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c f) : H1z ρ) = 0 := hx
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨m, hm⟩ := h1
    have hm' : ∀ g, ρ g m - m = (f.1 g).val := fun g => congrFun hm g
    have hP : m ∈ preInv ρ c := (mem_preInv m).2 fun g => by
      have := congrArg (c • ·) (hm' g)
      simp only [Lev.smul_val, smul_sub] at this
      rw [map_smul, ← sub_eq_zero, ← this]
    refine ⟨⟨m, hP⟩, ?_⟩
    show Submodule.Quotient.mk (cobLev ρ c hlc ⟨m, hP⟩) = Submodule.Quotient.mk f
    congr 1
    exact Subtype.ext (funext fun g => Lev.ext (hm' g))
  · rintro x ⟨m, rfl⟩
    rw [LinearMap.mem_ker]
    show (Submodule.Quotient.mk (levelCocycleToModuleCocycle ρ c (cobLev ρ c hlc m)) : H1z ρ) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m.1, rfl⟩

def toQ (ρ : Representation O G M) (c : O) :
    preInv ρ c →ₗ[O] (ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) :=
  (Submodule.mkQ _) ∘ₗ (LinearMap.codRestrict ρ.invariants
    ((c • LinearMap.id : M →ₗ[O] M) ∘ₗ (preInv ρ c).subtype) (fun m =>
      (Representation.mem_invariants _ _).2 ((mem_preInv _).1 m.2)))

/- English proof (translation)
Introduce `y`. Take `⟨t, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨m, hm⟩` from `hdiv t.1`. Establish `hP : m ∈ preInv ρ c` using `(mem_preInv m).2 fun g => by`. Rewrite using `[hm]`.

Conclude with `(Representation.mem_invariants _ _).1 t.2 g`. Use `⟨⟨m, hP⟩, ?_⟩` and prove the remaining obligations. Use `show Submodule.Quotient.mk _ = Submodule.Quotient.mk t`. Use `congr 1`. Conclude with `Subtype.ext hm`.
-/
theorem toQ_surjective (ρ : Representation O G M) (c : O) (hdiv : ∀ m : M, ∃ m' : M, c • m' = m) :
    Function.Surjective (toQ ρ c) := by
  intro y
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨m, hm⟩ := hdiv t.1
  have hP : m ∈ preInv ρ c := (mem_preInv m).2 fun g => by
    rw [hm]; exact (Representation.mem_invariants _ _).1 t.2 g
  refine ⟨⟨m, hP⟩, ?_⟩
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk t
  congr 1
  exact Subtype.ext hm

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : (Submodule.Quotient.mk (cobLev ρ c hlc m) : H1 (levRep ρ c)) = 0` using `h`.

Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨ℓ, hℓ⟩` from `(mem_coboundaries1 _ _).1 h1`. Establish `hℓ' : ∀ g, ρ g m.1 - m.1 = ρ g ℓ.val - ℓ.val` using `fun g => congrArg Lev.val (hℓ g)`. Establish `hinv : m.1 - ℓ.val ∈ ρ.invariants` using `(Representation.mem_invariants _ _).2 fun g => by`. Rewrite using `[map_sub]`.

Conclude with `sub_eq_sub_iff_sub_eq_sub.mp (hℓ' g)`. Use `show Submodule.Quotient.mk _ = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `⟨⟨m.1 - ℓ.val, hinv⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show c • (m.1 - ℓ.val) = c • m.1`.

Rewrite using `[smul_sub, Lev.smul_val, sub_zero]`. Introduce `h`. Establish `h1 : (Submodule.Quotient.mk _ : ρ.invariants ⧸ LinearMap.range (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) = 0` using `h`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨t, ht⟩` from `h1`.

Establish `ht' : c • t.1 = c • m.1` using `congrArg Subtype.val ht`. Establish `hl : c • (m.1 - t.1) = 0` using `by rw [smul_sub, ht', sub_self]`. Use `show (Submodule.Quotient.mk (cobLev ρ c hlc m) : H1 (levRep ρ c)) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Use `(mem_coboundaries1 _ _).2 ⟨Lev.mk (m.1 - t.1) hl, fun g => Lev.ext ?_⟩` and prove the remaining obligations.

Use `show ρ g m.1 - m.1 = ρ g (m.1 - t.1) - (m.1 - t.1)`. Rewrite using `[map_sub, (Representation.mem_invariants _ _).1 t.2 g]`. Normalize the expressions using the abelian group laws.
-/
theorem ker_kappa (ρ : Representation O G M) (c : O) (hlc : ∀ m : M, IsLocallyConstant (fun g => ρ g m)) :
    LinearMap.ker (kappa ρ c hlc) = LinearMap.ker (toQ ρ c) := by
  ext m
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h
    have h1 : (Submodule.Quotient.mk (cobLev ρ c hlc m) : H1 (levRep ρ c)) = 0 := h
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨ℓ, hℓ⟩ := (mem_coboundaries1 _ _).1 h1
    have hℓ' : ∀ g, ρ g m.1 - m.1 = ρ g ℓ.val - ℓ.val := fun g => congrArg Lev.val (hℓ g)
    have hinv : m.1 - ℓ.val ∈ ρ.invariants := (Representation.mem_invariants _ _).2 fun g => by
      rw [map_sub]; exact sub_eq_sub_iff_sub_eq_sub.mp (hℓ' g)
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨⟨m.1 - ℓ.val, hinv⟩, Subtype.ext ?_⟩
    show c • (m.1 - ℓ.val) = c • m.1
    rw [smul_sub, Lev.smul_val, sub_zero]
  · intro h
    have h1 : (Submodule.Quotient.mk _ : ρ.invariants ⧸ LinearMap.range
        (c • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) = 0 := h
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨t, ht⟩ := h1
    have ht' : c • t.1 = c • m.1 := congrArg Subtype.val ht
    have hl : c • (m.1 - t.1) = 0 := by rw [smul_sub, ht', sub_self]
    show (Submodule.Quotient.mk (cobLev ρ c hlc m) : H1 (levRep ρ c)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine (mem_coboundaries1 _ _).2 ⟨Lev.mk (m.1 - t.1) hl, fun g => Lev.ext ?_⟩
    show ρ g m.1 - m.1 = ρ g (m.1 - t.1) - (m.1 - t.1)
    rw [map_sub, (Representation.mem_invariants _ _).1 t.2 g]
    abel

/- English proof (translation)
Introduce `O _ G _ _ M _ _ ρ ϖ n hdiv hlc hfin`. Establish `hdivc` using `exists_pow_smul_eq hdiv n`. Establish `hs` using `phi_surjective ρ (ϖ ^ n) hdivc hlc`. Use `⟨Finite.of_surjective _ hs, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (phi ρ (ϖ ^ n))), Nat.card_congr ((phi ρ (ϖ ^ n)).quotKerEquivOfSurjective hs).toEquiv, mul_comm]`.

Use `congr 1`. Establish `hker : LinearMap.ker (phi ρ (ϖ ^ n)) = LinearMap.range (kappa ρ (ϖ ^ n) hlc)`. Rewrite using `[phi, LinearMap.ker_codRestrict, LinearMap.ker_codRestrict, ker_valuation_H1]`. Rewrite using `[hker]`. Conclude with `Nat.card_congr (((kappa ρ (ϖ ^ n) hlc).quotKerEquivRange.symm.trans ((Submodule.quotEquivOfEq _ _ (ker_kappa ρ (ϖ ^ n) hlc)).trans ((toQ ρ (ϖ ^ n)).quotKerEquivOfSurjective (toQ_surjective ρ (ϖ ^ n) hdivc)))).toEquiv)`.
-/
theorem card_H1_level_rep_eq : ∀ {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    {M : Type} [AddCommGroup M] [Module O M] (ρ : Representation O G M) (ϖ : O) (n : ℕ),
    (∀ m : M, ∃ m' : M, ϖ • m' = m) → (∀ m : M, IsLocallyConstant (fun g => ρ g m)) →
    Finite (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) →
    Finite (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) ∧
    Nat.card (ReciprocityTheory.Gal.H1 (GlobalTheory.ShapeNeg.levRep ρ (ϖ ^ n))) =
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : ReciprocityTheory.ChartRestriction.T2.HcLC ρ →ₗ[O] ReciprocityTheory.ChartRestriction.T2.HcLC ρ)) *
      Nat.card (ρ.invariants ⧸ LinearMap.range (ϖ ^ n • LinearMap.id : ρ.invariants →ₗ[O] ρ.invariants)) := by
  intro O _ G _ _ M _ _ ρ ϖ n hdiv hlc hfin
  have hdivc := exists_pow_smul_eq hdiv n
  have hs := phi_surjective ρ (ϖ ^ n) hdivc hlc
  refine ⟨Finite.of_surjective _ hs, ?_⟩
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker (phi ρ (ϖ ^ n))),
    Nat.card_congr ((phi ρ (ϖ ^ n)).quotKerEquivOfSurjective hs).toEquiv, mul_comm]
  congr 1
  have hker : LinearMap.ker (phi ρ (ϖ ^ n)) = LinearMap.range (kappa ρ (ϖ ^ n) hlc) := by
    rw [phi, LinearMap.ker_codRestrict, LinearMap.ker_codRestrict, ker_valuation_H1]
  rw [hker]
  exact Nat.card_congr (((kappa ρ (ϖ ^ n) hlc).quotKerEquivRange.symm.trans
    ((Submodule.quotEquivOfEq _ _ (ker_kappa ρ (ϖ ^ n) hlc)).trans
      ((toQ ρ (ϖ ^ n)).quotKerEquivOfSurjective (toQ_surjective ρ (ϖ ^ n) hdivc)))).toEquiv)

end GlobalTheory.ShapeNeg.SeqCount
