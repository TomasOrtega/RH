import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.StandardLattice

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB

open NumberField
open scoped Matrix

def pZ (l : ℕ) : Ideal ℤ := Ideal.span {(l : ℤ)}

variable (l : ℕ) [hl : Fact l.Prime]

instance pZ_isPrime : (pZ l).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2 (Nat.prime_iff_prime_int.1 hl.out)

/- English proof (translation)
Unfold `pZ`. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hl.out.ne_zero` after adjusting the coercions.
-/
theorem pZ_ne_bot : pZ l ≠ ⊥ := by
  unfold pZ
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hl.out.ne_zero

/- English proof (translation)
The claim follows from `Ideal.mem_span_singleton`.
-/
theorem mem_pZ_iff (z : ℤ) : z ∈ pZ l ↔ (l : ℤ) ∣ z := Ideal.mem_span_singleton

variable (K : Type) [Field K] [NumberField K]

abbrev Ml : Submonoid (𝓞 K) := Algebra.algebraMapSubmonoid (𝓞 K) (pZ l).primeCompl

abbrev Rl : Type := Localization (Ml l K)

variable {l K}

/- English proof (translation)
Unfold `Ml Algebra.algebraMapSubmonoid`. Rewrite using `[Submonoid.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, fun h => hz ((mem_pZ_iff l z).2 h), rfl⟩`.

Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨z, fun h => hz ((mem_pZ_iff l z).1 h), rfl⟩`.
-/
theorem mem_Ml_iff (s : 𝓞 K) : s ∈ Ml l K ↔ ∃ z : ℤ, ¬ (l : ℤ) ∣ z ∧ algebraMap ℤ (𝓞 K) z = s := by
  unfold Ml Algebra.algebraMapSubmonoid
  rw [Submonoid.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, fun h => hz ((mem_pZ_iff l z).2 h), rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, fun h => hz ((mem_pZ_iff l z).1 h), rfl⟩

/- English proof (translation)
The claim follows from `(mem_Ml_iff _).2 ⟨s, fun h => hs (Int.natCast_dvd_natCast.1 h), by simp⟩`.
-/
theorem natCast_mem_Ml {s : ℕ} (hs : ¬ l ∣ s) : (s : 𝓞 K) ∈ Ml l K :=
  (mem_Ml_iff _).2 ⟨s, fun h => hs (Int.natCast_dvd_natCast.1 h), by simp⟩

/- English proof (translation)
Introduce `h`. Take `⟨z, hz, h0⟩` from `(mem_Ml_iff _).1 h`. Establish `: z = 0` using `(algebraMap ℤ (𝓞 K)).injective_int (h0.trans (map_zero _).symm)`. Conclude with `hz (this ▸ dvd_zero _)`.
-/
theorem zero_notMem_Ml : (0 : 𝓞 K) ∉ Ml l K := by
  intro h
  obtain ⟨z, hz, h0⟩ := (mem_Ml_iff _).1 h
  have : z = 0 := (algebraMap ℤ (𝓞 K)).injective_int (h0.trans (map_zero _).symm)
  exact hz (this ▸ dvd_zero _)

variable (l K)

/- English proof (translation)
The claim follows from `le_nonZeroDivisors_of_noZeroDivisors zero_notMem_Ml`.
-/
theorem Ml_le : Ml l K ≤ nonZeroDivisors (𝓞 K) := le_nonZeroDivisors_of_noZeroDivisors zero_notMem_Ml

instance Rl_isDomain : IsDomain (Rl l K) := IsLocalization.isDomain_localization (Ml_le l K)

def rlToK : Rl l K →+* K :=
  IsLocalization.lift (M := Ml l K) (g := algebraMap (𝓞 K) K) (fun y => by
    refine IsUnit.mk0 _ ?_
    intro h
    have h0 : (y : 𝓞 K) = 0 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [h, map_zero]
    exact zero_notMem_Ml (h0 ▸ y.2))

instance rlAlgebra : Algebra (Rl l K) K := (rlToK l K).toAlgebra

instance rlTower : IsScalarTower (𝓞 K) (Rl l K) K :=
  IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq _ x).symm)

instance rlFrac : IsFractionRing (Rl l K) K :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ml l K) (Rl l K) K

instance rlDedekind : IsDedekindDomain (Rl l K) :=
  IsLocalization.isDedekindDomain (𝓞 K) (Ml_le l K) (Rl l K)

/- English proof (translation)
The claim follows from `IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) (pZ l) (pZ_ne_bot l)`.
-/
theorem rl_pid : IsPrincipalIdealRing (Rl l K) :=
  IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) (pZ l) (pZ_ne_bot l)

/- English proof (translation)
The claim follows from `IsFractionRing.injective (Rl l K) K`.
-/
theorem algebraMap_rl_injective : Function.Injective (algebraMap (Rl l K) K) :=
  IsFractionRing.injective (Rl l K) K

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, rfl⟩`. Take `⟨a, ⟨m, hm⟩, rfl⟩` from `IsLocalization.exists_mk'_eq (Ml l K) r`. Take `⟨z, hz, rfl⟩` from `(mem_Ml_iff _).1 hm`. Establish `key : (z : K) * algebraMap (Rl l K) K (IsLocalization.mk' (Rl l K) a ⟨_, hm⟩) = algebraMap (𝓞 K) K a`.

Establish `h1` using `IsLocalization.mk'_spec (Rl l K) a ⟨_, hm⟩`. Establish `h2` using `congrArg (algebraMap (Rl l K) K) h1`. Rewrite `h2` using `[map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (Rl l K) K a, ← IsScalarTower.algebraMap_apply (𝓞 K) (Rl l K) K]`. Establish `h5 : algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) z) = (z : K)` using `by simp`. Rewrite using `[← h2, mul_comm]`.

Use `congr 1`. Use `⟨z.natAbs, fun h => hz (Int.natCast_dvd.2 h), ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq z with h | h` into its components or cases. Establish `e : ((z.natAbs : ℕ) : K) = (z : K)`. Establish `e' : ((z.natAbs : ℕ) : ℤ) = z` using `by omega`.

Rewrite using `[← Int.cast_natCast, e']`. Rewrite using `[e, key]`. Conclude with `⟨a, rfl⟩`. Establish `e : ((z.natAbs : ℕ) : K) = -(z : K)`. Establish `e' : ((z.natAbs : ℕ) : ℤ) = -z` using `by omega`.

Rewrite using `[← Int.cast_natCast, e', Int.cast_neg]`. Rewrite using `[e, neg_mul, key]`. Conclude with `⟨-a, by simp⟩`. Introduce and unpack `⟨s, hs, a, ha⟩`. Establish `hs0 : (s : K) ≠ 0`.

Establish `: s ≠ 0` using `fun h => hs (h ▸ dvd_zero l)`. Conclude with `this` after adjusting the coercions. Use `⟨IsLocalization.mk' (Rl l K) a ⟨(s : 𝓞 K), natCast_mem_Ml hs⟩, ?_⟩` and prove the remaining obligations. Establish `h1` using `IsLocalization.mk'_spec (Rl l K) a ⟨(s : 𝓞 K), natCast_mem_Ml hs⟩`. Establish `h2` using `congrArg (algebraMap (Rl l K) K) h1`.

Rewrite `h2` using `[map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha]`. Simplify using `only [map_natCast] at h2`. Apply `mul_left_cancel₀ hs0` to reduce the goal to its premises. Rewrite using `[← h2, mul_comm]`.
-/
theorem mem_range_rl_iff (y : K) :
    y ∈ (algebraMap (Rl l K) K).range ↔ ∃ s : ℕ, ¬ l ∣ s ∧ (s : K) * y ∈ (algebraMap (𝓞 K) K).range := by
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨a, ⟨m, hm⟩, rfl⟩ := IsLocalization.exists_mk'_eq (Ml l K) r
    obtain ⟨z, hz, rfl⟩ := (mem_Ml_iff _).1 hm
    have key : (z : K) * algebraMap (Rl l K) K (IsLocalization.mk' (Rl l K) a ⟨_, hm⟩) = algebraMap (𝓞 K) K a := by
      have h1 := IsLocalization.mk'_spec (Rl l K) a ⟨_, hm⟩
      have h2 := congrArg (algebraMap (Rl l K) K) h1
      rw [map_mul, ← IsScalarTower.algebraMap_apply (𝓞 K) (Rl l K) K a,
        ← IsScalarTower.algebraMap_apply (𝓞 K) (Rl l K) K] at h2
      have h5 : algebraMap (𝓞 K) K (algebraMap ℤ (𝓞 K) z) = (z : K) := by simp
      rw [← h2, mul_comm]
      congr 1
    refine ⟨z.natAbs, fun h => hz (Int.natCast_dvd.2 h), ?_⟩
    rcases Int.natAbs_eq z with h | h
    · have e : ((z.natAbs : ℕ) : K) = (z : K) := by
        have e' : ((z.natAbs : ℕ) : ℤ) = z := by omega
        rw [← Int.cast_natCast, e']
      rw [e, key]
      exact ⟨a, rfl⟩
    · have e : ((z.natAbs : ℕ) : K) = -(z : K) := by
        have e' : ((z.natAbs : ℕ) : ℤ) = -z := by omega
        rw [← Int.cast_natCast, e', Int.cast_neg]
      rw [e, neg_mul, key]
      exact ⟨-a, by simp⟩
  · rintro ⟨s, hs, a, ha⟩
    have hs0 : (s : K) ≠ 0 := by
      have : s ≠ 0 := fun h => hs (h ▸ dvd_zero l)
      exact_mod_cast this
    refine ⟨IsLocalization.mk' (Rl l K) a ⟨(s : 𝓞 K), natCast_mem_Ml hs⟩, ?_⟩
    have h1 := IsLocalization.mk'_spec (Rl l K) a ⟨(s : 𝓞 K), natCast_mem_Ml hs⟩
    have h2 := congrArg (algebraMap (Rl l K) K) h1
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ha] at h2
    simp only [map_natCast] at h2
    apply mul_left_cancel₀ hs0
    rw [← h2, mul_comm]

section Mod

variable (V : Type) [AddCommGroup V] [Module K V]

@[reducible] def rlModule : Module (Rl l K) V := Module.compHom V (algebraMap (Rl l K) K)

attribute [local instance] rlModule

instance rlTowerK : IsScalarTower (Rl l K) K V :=
  ⟨fun r a x => by
    show (r • a) • x = algebraMap (Rl l K) K r • (a • x)
    rw [Algebra.smul_def, mul_smul]⟩

instance rlTowerO [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] : IsScalarTower (𝓞 K) (Rl l K) V :=
  ⟨fun r s x => by
    show algebraMap (Rl l K) K (r • s) • x = r • (algebraMap (Rl l K) K s • x)
    rw [Algebra.smul_def, map_mul, mul_smul, ← IsScalarTower.algebraMap_apply, algebraMap_smul]⟩

instance rlTorsionFree : Module.IsTorsionFree (Rl l K) V :=
  Module.IsTorsionFree.of_smul_eq_zero (fun r x h => by
    change algebraMap (Rl l K) K r • x = 0 at h
    rcases smul_eq_zero.1 h with h | h
    · left
      exact algebraMap_rl_injective l K (by rw [h, map_zero])
    · exact Or.inr h)

variable {V} [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def atL (L : Submodule (𝓞 K) V) : Submodule (Rl l K) V := Submodule.span (Rl l K) (L : Set V)

/- English proof (translation)
Apply the tactic sequence `first | exact UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff .. | (apply UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> assumption) | (intros; apply UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> assumption) | (apply @UpperTheory.Reformulated.B.Sta …`.
-/
theorem mem_atL_iff {L : Submodule (𝓞 K) V} {x : V} :
    x ∈ atL l K L ↔ ∃ s ∈ Ml l K, s • x ∈ L := by
  first | exact UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff .. | (apply UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> assumption) | (intros; apply UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> assumption) | (apply @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> assumption) | (apply @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› L x | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› L | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› ‹_› ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› V | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K ‹_› | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl K | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l hl | exact @UpperTheory.Reformulated.B.StandardLattice.mem_atL_iff l

/- English proof (translation)
Take `⟨S, hS⟩` from `h`. Use `⟨S, ?_⟩` and prove the remaining obligations. Unfold `atL`. Rewrite using `[← hS, Submodule.span_span_of_tower]`.
-/
theorem atL_fg {L : Submodule (𝓞 K) V} (h : L.FG) : (atL l K L).FG := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, ?_⟩
  unfold atL
  rw [← hS, Submodule.span_span_of_tower]

/- English proof (translation)
The claim follows from `Submodule.subset_span`.
-/
theorem le_atL (L : Submodule (𝓞 K) V) : (L : Set V) ⊆ atL l K L := Submodule.subset_span

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Establish `: atL l K L ≤ (Submodule.span K (L : Set V)).restrictScalars (Rl l K)` using `Submodule.span_le.2 Submodule.subset_span`. Conclude with `this`. Conclude with `Submodule.span_mono (le_atL l K L)`.
-/
theorem span_atL (L : Submodule (𝓞 K) V) :
    Submodule.span K (atL l K L : Set V) = Submodule.span K (L : Set V) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    have : atL l K L ≤ (Submodule.span K (L : Set V)).restrictScalars (Rl l K) :=
      Submodule.span_le.2 Submodule.subset_span
    exact this
  · exact Submodule.span_mono (le_atL l K L)

/- English proof (translation)
Use `rl_pid l K` as an intermediate fact. Establish `: Module.Finite (Rl l K) (atL l K A)` using `Module.Finite.iff_fg.2 (atL_fg l K hfg)`. Establish `: Module.Free (Rl l K) (atL l K A)` using `inferInstance`. Set `b` to `Module.Free.chooseBasis (Rl l K) (atL l K A)`. Establish `hli : LinearIndependent (Rl l K) (fun i => ((b i : atL l K A) : V))` using `b.linearIndependent.map' (atL l K A).subtype (Submodule.ker_subtype _)`.

Establish `hliK : LinearIndependent K (fun i => ((b i : atL l K A) : V))` using `(LinearIndependent.iff_fractionRing (Rl l K) K).1 hli`. Establish `hs : Submodule.span (Rl l K) (Set.range fun i => ((b i : atL l K A) : V)) = atL l K A`. Establish `h1 : (Set.range fun i => ((b i : atL l K A) : V)) = (atL l K A).subtype '' Set.range b`. Rewrite using `[← Set.range_comp]`. Both sides reduce to the same expression.

Rewrite using `[h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]`. Establish `key : ∀ S : Set V, Submodule.span (Rl l K) S = atL l K A → Submodule.span K S = ⊤` using `fun S hS => by`. Rewrite using `[← hsp, ← span_atL l K A, ← hS, Submodule.span_span_of_tower]`. Conclude with `⟨_, inferInstance, b, Module.Basis.mk hliK (key _ hs).ge, fun i => Module.Basis.mk_apply _ _ i⟩`.
-/
theorem exists_basis_atL {A : Submodule (𝓞 K) V} (hfg : A.FG)
    (hsp : Submodule.span K (A : Set V) = ⊤) :
    ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι (Rl l K) (atL l K A)) (bK : Module.Basis ι K V),
      ∀ i, bK i = (b i : V) := by
  have := rl_pid l K
  have : Module.Finite (Rl l K) (atL l K A) := Module.Finite.iff_fg.2 (atL_fg l K hfg)
  have : Module.Free (Rl l K) (atL l K A) := inferInstance
  let b := Module.Free.chooseBasis (Rl l K) (atL l K A)
  have hli : LinearIndependent (Rl l K) (fun i => ((b i : atL l K A) : V)) :=
    b.linearIndependent.map' (atL l K A).subtype (Submodule.ker_subtype _)
  have hliK : LinearIndependent K (fun i => ((b i : atL l K A) : V)) :=
    (LinearIndependent.iff_fractionRing (Rl l K) K).1 hli
  have hs : Submodule.span (Rl l K) (Set.range fun i => ((b i : atL l K A) : V)) = atL l K A := by
    have h1 : (Set.range fun i => ((b i : atL l K A) : V)) = (atL l K A).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have key : ∀ S : Set V, Submodule.span (Rl l K) S = atL l K A → Submodule.span K S = ⊤ := fun S hS => by
    rw [← hsp, ← span_atL l K A, ← hS, Submodule.span_span_of_tower]
  exact ⟨_, inferInstance, b, Module.Basis.mk hliK (key _ hs).ge, fun i => Module.Basis.mk_apply _ _ i⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx i`. Establish `e : x = ∑ j, algebraMap (Rl l K) K (b.repr ⟨x, hx⟩ j) • bK j`. Establish `h1` using `congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at h1`.

Use `conv_lhs => rw [← h1]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hb j]`. Both sides reduce to the same expression. Rewrite using `[e, bK.repr_sum_self]`.

Conclude with `⟨_, rfl⟩`. Introduce `h choose r hr using h`. Establish `e : x = ∑ j, r j • (b j : V)` using `by conv_lhs => rw [← bK.sum_repr x]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hr j, hb j]`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2`.
-/
theorem mem_atL_iff_repr {A : Submodule (𝓞 K) V} {ι : Type} [Fintype ι] (b : Module.Basis ι (Rl l K) (atL l K A))
    (bK : Module.Basis ι K V) (hb : ∀ i, bK i = (b i : V)) (x : V) :
    x ∈ atL l K A ↔ ∀ i, bK.repr x i ∈ (algebraMap (Rl l K) K).range := by
  classical
  constructor
  · intro hx i
    have e : x = ∑ j, algebraMap (Rl l K) K (b.repr ⟨x, hx⟩ j) • bK j := by
      have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
      conv_lhs => rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hb j]
      rfl
    rw [e, bK.repr_sum_self]
    exact ⟨_, rfl⟩
  · intro h
    choose r hr using h
    have e : x = ∑ j, r j • (b j : V) := by
      conv_lhs => rw [← bK.sum_repr x]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hr j, hb j]
      rfl
    rw [e]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (b j).2

/- English proof (translation)
Rewrite using `[mem_atL_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hx⟩`. Take `⟨z, hz, rfl⟩` from `(mem_Ml_iff _).1 hs`. Establish `e0 : algebraMap ℤ (𝓞 K) z • x = z • x`.

Rewrite using `[algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul]`. Rewrite `hx` using `[e0]`. Use `⟨z.natAbs, fun h => hz (Int.natCast_dvd.2 h), ?_⟩` and prove the remaining obligations. Break down `Int.natAbs_eq z with h | h` into its components or cases. Establish `e : z.natAbs • x = z • x` using `by conv_rhs => rw [h]`.

Rewrite using `[natCast_zsmul]`. Rewrite using `[e]` and apply the resulting hypothesis. Establish `e : z.natAbs • x = -(z • x)` using `by conv_rhs => rw [h]`. Rewrite using `[neg_zsmul, natCast_zsmul, neg_neg]`. Rewrite using `[e]`.

Conclude with `L.neg_mem hx`. Introduce and unpack `⟨s, hs, hx⟩`. Use `⟨(s : 𝓞 K), natCast_mem_Ml hs, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul]` and apply the resulting hypothesis.
-/
theorem mem_atL_iff_nat {L : Submodule (𝓞 K) V} {x : V} :
    x ∈ atL l K L ↔ ∃ s : ℕ, ¬ l ∣ s ∧ s • x ∈ L := by
  rw [mem_atL_iff]
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨z, hz, rfl⟩ := (mem_Ml_iff _).1 hs
    have e0 : algebraMap ℤ (𝓞 K) z • x = z • x := by
      rw [algebraMap_int_eq, eq_intCast, Int.cast_smul_eq_zsmul]
    rw [e0] at hx
    refine ⟨z.natAbs, fun h => hz (Int.natCast_dvd.2 h), ?_⟩
    rcases Int.natAbs_eq z with h | h
    · have e : z.natAbs • x = z • x := by
        conv_rhs => rw [h]
        rw [natCast_zsmul]
      rwa [e]
    · have e : z.natAbs • x = -(z • x) := by
        conv_rhs => rw [h]
        rw [neg_zsmul, natCast_zsmul, neg_neg]
      rw [e]
      exact L.neg_mem hx
  · rintro ⟨s, hs, hx⟩
    refine ⟨(s : 𝓞 K), natCast_mem_Ml hs, ?_⟩
    rwa [Nat.cast_smul_eq_nsmul]

end Mod

section Vec

variable {n : ℕ}

/- English proof (translation)
Set `_` to `rlModule l K (Fin n → K)`. Take `⟨ι, hι, b, bK, hb⟩` from `exists_basis_atL l K hfg hsp`. Establish `hcard : Fintype.card ι = n`. Rewrite using `[← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]`. Set `e : ι ≃ Fin n` to `Fintype.equivFinOfCardEq hcard`.

Set `b' : Module.Basis (Fin n) K (Fin n → K)` to `bK.reindex e`. Set `b''` to `b.reindex e`. Establish `hb' : ∀ i, b' i = (b'' i : Fin n → K)` using `fun i => by`. Simplify using `only [b', b'', Module.Basis.reindex_apply]`. Conclude with `hb _`.

Set `B : GL (Fin n) K` to `⟨(Pi.basisFun K (Fin n)).toMatrix b', b'.toMatrix (Pi.basisFun K (Fin n)), Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩`. Establish `key : ∀ x, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = b'.repr x` using `fun x => by show b'.toMatrix (Pi.basisFun K (Fin n)) *ᵥ x = _`. Establish `hx : ((Pi.basisFun K (Fin n)).repr x : Fin n → K) = x` using `funext fun a => by simp`. Establish `h` using `Module.Basis.toMatrix_mulVec_repr (Pi.basisFun K (Fin n)) b' x`. Rewrite `h` using `[hx]`.

Conclude with `h`. Use `⟨B, fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : (∃ s : ℕ, ¬ l ∣ s ∧ (s : K) • x ∈ A) ↔ x ∈ atL l K A`. Rewrite using `[mem_atL_iff_nat]`. Simplify using `only [Nat.cast_smul_eq_nsmul]`.

Simplify using `only [SetLike.mem_coe]`. Rewrite using `[h1, mem_atL_iff_repr l K b'' b' hb']`. Simplify using `only [key]`. Prove the components needed by the constructor for the conclusion. Introduce `h choose s hs hy using fun a => (mem_range_rl_iff l K (b'.repr x a)).1 (h a)`.

Use `⟨∏ a, s a, fun hd => ?_, fun a => ?_⟩` and prove the remaining obligations. Take `⟨a, _, ha⟩` from `(Prime.dvd_finsetProd_iff hl.out.prime _).1 hd`. Conclude with `hs a ha`. Rewrite using `[← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ a), mul_comm (s a), Nat.cast_mul, mul_assoc]`. Take `⟨r, hr⟩` from `hy a`.

Rewrite using `[← hr]`. Conclude with `⟨((∏ b ∈ Finset.univ.erase a, s b : ℕ) : 𝓞 K) * r, by rw [map_mul, map_natCast]⟩`. Introduce and unpack `⟨s, hs, h⟩ a`. Conclude with `(mem_range_rl_iff l K _).2 ⟨s, hs, h a⟩`.
-/
theorem exists_isLocBasis (A : Submodule (𝓞 K) (Fin n → K)) (hfg : A.FG)
    (hsp : Submodule.span K (A : Set (Fin n → K)) = ⊤) :
    ∃ B : GL (Fin n) K, Formalism.L2.Forms.IsLocBasis l (A : Set (Fin n → K)) B := by
  classical
  let _ := rlModule l K (Fin n → K)
  obtain ⟨ι, hι, b, bK, hb⟩ := exists_basis_atL l K hfg hsp
  have hcard : Fintype.card ι = n := by
    rw [← Module.finrank_eq_card_basis bK, Module.finrank_fin_fun]
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let b' : Module.Basis (Fin n) K (Fin n → K) := bK.reindex e
  let b'' := b.reindex e
  have hb' : ∀ i, b' i = (b'' i : Fin n → K) := fun i => by
    simp only [b', b'', Module.Basis.reindex_apply]
    exact hb _
  let B : GL (Fin n) K :=
    ⟨(Pi.basisFun K (Fin n)).toMatrix b', b'.toMatrix (Pi.basisFun K (Fin n)),
      Module.Basis.toMatrix_mul_toMatrix_flip _ _, Module.Basis.toMatrix_mul_toMatrix_flip _ _⟩
  have key : ∀ x, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x = b'.repr x := fun x => by
    show b'.toMatrix (Pi.basisFun K (Fin n)) *ᵥ x = _
    have hx : ((Pi.basisFun K (Fin n)).repr x : Fin n → K) = x := funext fun a => by simp
    have h := Module.Basis.toMatrix_mulVec_repr (Pi.basisFun K (Fin n)) b' x
    rw [hx] at h
    exact h
  refine ⟨B, fun x => ?_⟩
  have h1 : (∃ s : ℕ, ¬ l ∣ s ∧ (s : K) • x ∈ A) ↔ x ∈ atL l K A := by
    rw [mem_atL_iff_nat]
    simp only [Nat.cast_smul_eq_nsmul]
  simp only [SetLike.mem_coe]
  rw [h1, mem_atL_iff_repr l K b'' b' hb']
  simp only [key]
  constructor
  · intro h
    choose s hs hy using fun a => (mem_range_rl_iff l K (b'.repr x a)).1 (h a)
    refine ⟨∏ a, s a, fun hd => ?_, fun a => ?_⟩
    · obtain ⟨a, _, ha⟩ := (Prime.dvd_finsetProd_iff hl.out.prime _).1 hd
      exact hs a ha
    · rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ a), mul_comm (s a), Nat.cast_mul, mul_assoc]
      obtain ⟨r, hr⟩ := hy a
      rw [← hr]
      exact ⟨((∏ b ∈ Finset.univ.erase a, s b : ℕ) : 𝓞 K) * r, by rw [map_mul, map_natCast]⟩
  · rintro ⟨s, hs, h⟩ a
    exact (mem_range_rl_iff l K _).2 ⟨s, hs, h a⟩

end Vec

section Bound

open Formalism.L2.DIV Formalism.L2.Col

variable {K} {n : ℕ}

def bnd (d : 𝓞 K) : Submodule (𝓞 K) (Fin n → K) := (colLat (1 : GL (Fin n) K)).comap (d • LinearMap.id)

/- English proof (translation)
Unfold `bnd`. Rewrite using `[Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, lc_mem_colLat_one]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[lc_mem_one_iff, Pi.smul_apply, Algebra.smul_def, RingHom.mem_range]`.
-/
theorem mem_bnd (d : 𝓞 K) (x : Fin n → K) :
    x ∈ bnd d ↔ ∀ a, algebraMap (𝓞 K) K d * x a ∈ (algebraMap (𝓞 K) K).range := by
  unfold bnd
  rw [Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply, lc_mem_colLat_one]
  refine forall_congr' fun a => ?_
  rw [lc_mem_one_iff, Pi.smul_apply, Algebra.smul_def, RingHom.mem_range]

/- English proof (translation)
The claim follows from `(map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 hd`.
-/
theorem algebraMap_ne_zero {d : 𝓞 K} (hd : d ≠ 0) : algebraMap (𝓞 K) K d ≠ 0 :=
  (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).2 hd

/- English proof (translation)
Establish `: IsNoetherian (𝓞 K) (colLat (1 : GL (Fin n) K))` using `isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))`. Set `φ : L →ₗ[𝓞 K] colLat (1 : GL (Fin n) K)` to `{ toFun := fun x => ⟨d • (x : Fin n → K), h x.2⟩ map_add' := fun x y => by ext1; simp [smul_add] map_smul' := fun a x => by ext1; simp [smul_comm d a] }`. Establish `hinj : Function.Injective φ`. Introduce `x y hxy`. Establish `h1 : d • (x : Fin n → K) = d • (y : Fin n → K)` using `congrArg Subtype.val hxy`.

Rewrite `h1` using `[← algebraMap_smul K d (x : Fin n → K), ← algebraMap_smul K d (y : Fin n → K)]`. Conclude with `Subtype.ext (smul_right_injective _ (algebraMap_ne_zero hd) h1)`. Establish `: IsNoetherian (𝓞 K) L` using `isNoetherian_of_injective φ hinj`. Conclude with `(Submodule.fg_top _).1 (IsNoetherian.noetherian ⊤)`.
-/
theorem fg_of_le_bnd {L : Submodule (𝓞 K) (Fin n → K)} {d : 𝓞 K} (hd : d ≠ 0) (h : L ≤ bnd d) : L.FG := by
  have : IsNoetherian (𝓞 K) (colLat (1 : GL (Fin n) K)) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  let φ : L →ₗ[𝓞 K] colLat (1 : GL (Fin n) K) :=
    { toFun := fun x => ⟨d • (x : Fin n → K), h x.2⟩
      map_add' := fun x y => by ext1; simp [smul_add]
      map_smul' := fun a x => by ext1; simp [smul_comm d a] }
  have hinj : Function.Injective φ := by
    intro x y hxy
    have h1 : d • (x : Fin n → K) = d • (y : Fin n → K) := congrArg Subtype.val hxy
    rw [← algebraMap_smul K d (x : Fin n → K), ← algebraMap_smul K d (y : Fin n → K)] at h1
    exact Subtype.ext (smul_right_injective _ (algebraMap_ne_zero hd) h1)
  have : IsNoetherian (𝓞 K) L := isNoetherian_of_injective φ hinj
  exact (Submodule.fg_top _).1 (IsNoetherian.noetherian ⊤)

/- English proof (translation)
Introduce `x hx`. Rewrite `hx`, the goal using `[mem_bnd]`. Introduce `a`. Take `⟨r, hr⟩` from `hx a`. Conclude with `⟨e * r, by rw [map_mul, hr, map_mul, mul_assoc]⟩`.
-/
theorem bnd_mono (d e : 𝓞 K) : (bnd d : Submodule (𝓞 K) (Fin n → K)) ≤ bnd (e * d) := by
  intro x hx
  rw [mem_bnd] at hx ⊢
  intro a
  obtain ⟨r, hr⟩ := hx a
  exact ⟨e * r, by rw [map_mul, hr, map_mul, mul_assoc]⟩

/- English proof (translation)
Take `⟨d, hd, h1, -⟩` from `lc_sandwich L hL`. Conclude with `⟨d, hd, fun x hx => h1 x hx⟩`.
-/
theorem exists_le_bnd (L : Submodule (𝓞 K) (Fin n → K)) (hL : Submodule.IsLattice K L) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ L ≤ bnd d := by
  obtain ⟨d, hd, h1, -⟩ := lc_sandwich L hL
  exact ⟨d, hd, fun x hx => h1 x hx⟩

/- English proof (translation)
The claim follows from `IsIntegralClosure.isIntegral_iff.1 ((NumberField.RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom)`.
-/
theorem sig_int (σ : K →+* K) (r : 𝓞 K) : ∃ r' : 𝓞 K, algebraMap (𝓞 K) K r' = σ (algebraMap (𝓞 K) K r) :=
  IsIntegralClosure.isIntegral_iff.1 ((NumberField.RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom)

/- English proof (translation)
The claim follows from `(map_ne_zero_iff σ σ.injective).2 (algebraMap_ne_zero hd)`.
-/
theorem sig_ne_zero (σ : K →+* K) {d : 𝓞 K} (hd : d ≠ 0) : σ (algebraMap (𝓞 K) K d) ≠ 0 :=
  (map_ne_zero_iff σ σ.injective).2 (algebraMap_ne_zero hd)

/- English proof (translation)
Take `⟨d0, hd0, -, h2⟩` from `lc_sandwich L hL`. Take `⟨d0', hd0'⟩` from `sig_int σ d0`. Take `⟨d1, hd1⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (Finset.univ.image fun p : Fin n × Fin n => J⁻¹ p.1 p.2)`. Establish `hd0'0 : d0' ≠ 0`. Introduce `h`.

Apply `sig_ne_zero σ hd0` to reduce the goal to its premises. Rewrite using `[← hd0', h, map_zero]`. Use `⟨(d1 : 𝓞 K) * d0', mul_ne_zero (nonZeroDivisors.ne_zero d1.2) hd0'0, Submodule.span_le.2 fun y hy => ?_⟩` and prove the remaining obligations. Establish `hJy : ∀ a, σ (algebraMap (𝓞 K) K d0) * (J *ᵥ y) a ∈ (algebraMap (𝓞 K) K).range`. Introduce `a`.

Establish `hx : d0 • (fun b : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b a) ∈ L` using `h2 _ (lc_col_mem_colLat 1 a)`. Establish `h3` using `hy _ hx`. Establish `e : Formalism.UG.hform σ J (d0 • (fun b : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b a)) y = σ (algebraMap (𝓞 K) K d0) * (J *ᵥ y) a`. Unfold `Formalism.UG.hform`. Rewrite using `[Finset.sum_eq_single a]`.

Simplify using `only [Pi.smul_apply, Units.val_one, Matrix.one_apply_eq, Algebra.smul_def, mul_one, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Introduce `b _ hb`. Simplify using `[Matrix.one_apply, hb]`. Simplify using the standard rewrite rules. Rewrite using `[← e]`.

Conclude with `h3`. Rewrite using `[SetLike.mem_coe, mem_bnd]`. Introduce `a`. Establish `ey : y = J⁻¹ *ᵥ (J *ᵥ y)`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]`.

Rewrite using `[ey, map_mul, hd0', Matrix.mulVec, dotProduct, Finset.mul_sum]`. Use `Subring.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `hd1 (J⁻¹ a c) (Finset.mem_image.2 ⟨(a, c), Finset.mem_univ _, rfl⟩)`. Take `⟨q, hq⟩` from `hJy c`. Use `⟨r * q, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hr, hq, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dual_le_bnd (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K) (hJ : IsUnit J.det)
    (L : Submodule (𝓞 K) (Fin n → K)) (hL : Submodule.IsLattice K L) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ Submodule.span (𝓞 K) (Formalism.BasicNotions.dualSet σ J L) ≤ bnd d := by
  classical
  obtain ⟨d0, hd0, -, h2⟩ := lc_sandwich L hL
  obtain ⟨d0', hd0'⟩ := sig_int σ d0
  obtain ⟨d1, hd1⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin n × Fin n => J⁻¹ p.1 p.2)
  have hd0'0 : d0' ≠ 0 := by
    intro h
    apply sig_ne_zero σ hd0
    rw [← hd0', h, map_zero]
  refine ⟨(d1 : 𝓞 K) * d0', mul_ne_zero (nonZeroDivisors.ne_zero d1.2) hd0'0, Submodule.span_le.2 fun y hy => ?_⟩
  have hJy : ∀ a, σ (algebraMap (𝓞 K) K d0) * (J *ᵥ y) a ∈ (algebraMap (𝓞 K) K).range := by
    intro a
    have hx : d0 • (fun b : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b a) ∈ L :=
      h2 _ (lc_col_mem_colLat 1 a)
    have h3 := hy _ hx
    have e : Formalism.UG.hform σ J (d0 • (fun b : Fin n => ((1 : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) b a)) y =
        σ (algebraMap (𝓞 K) K d0) * (J *ᵥ y) a := by
      unfold Formalism.UG.hform
      rw [Finset.sum_eq_single a]
      · simp only [Pi.smul_apply, Units.val_one, Matrix.one_apply_eq, Algebra.smul_def, mul_one, Matrix.mulVec,
          dotProduct, Finset.mul_sum, mul_assoc]
      · intro b _ hb
        simp [Matrix.one_apply, hb]
      · simp
    rw [← e]
    exact h3
  rw [SetLike.mem_coe, mem_bnd]
  intro a
  have ey : y = J⁻¹ *ᵥ (J *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
  rw [ey, map_mul, hd0', Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Subring.sum_mem _ fun c _ => ?_
  obtain ⟨r, hr⟩ := hd1 (J⁻¹ a c) (Finset.mem_image.2 ⟨(a, c), Finset.mem_univ _, rfl⟩)
  obtain ⟨q, hq⟩ := hJy c
  refine ⟨r * q, ?_⟩
  rw [map_mul, hr, hq, Algebra.smul_def]
  ring

/- English proof (translation)
Take `⟨d0, hd0, h1, -⟩` from `lc_sandwich L hL`. Take `⟨d0', hd0'⟩` from `sig_int σ d0`. Establish `hd0'0 : d0' ≠ 0`. Introduce `h`. Apply `sig_ne_zero σ hd0` to reduce the goal to its premises.

Rewrite using `[← hd0', h, map_zero]`. Use `eq_top_iff.2 fun z _ => ?_` and prove the remaining obligations. Take `⟨e, he⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) (Finset.univ.image fun p : Fin n × Fin n => J p.1 p.2 * z p.2)`. Use `set c : K := algebraMap (𝓞 K) K d0' * algebraMap (𝓞 K) K (e : 𝓞 K) with hc`. Establish `hc0 : c ≠ 0` using `mul_ne_zero (algebraMap_ne_zero hd0'0) (algebraMap_ne_zero (nonZeroDivisors.ne_zero e.2))`.

Establish `hmem : c • z ∈ Formalism.BasicNotions.dualSet σ J L`. Introduce `x hx`. Establish `hx'` using `(lc_mem_colLat_one _).1 (h1 x hx)`. Unfold `Formalism.UG.hform`. Use `Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Take `⟨r, hr⟩` from `(lc_mem_one_iff _).1 (hx' i)`. Take `⟨r', hr'⟩` from `sig_int σ r`. Take `⟨q, hq⟩` from `he (J i j * z j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)`. Use `⟨r' * q, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr', hq, hr, Pi.smul_apply, Algebra.smul_def, map_mul, ← hd0', Pi.smul_apply, smul_eq_mul, Algebra.smul_def, hc]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : z = c⁻¹ • (c • z)` using `by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]`. Rewrite using `[e2]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span hmem))`.
-/
theorem dual_span (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)
    (L : Submodule (𝓞 K) (Fin n → K)) (hL : Submodule.IsLattice K L) :
    Submodule.span K ((Submodule.span (𝓞 K) (Formalism.BasicNotions.dualSet σ J L) : Submodule (𝓞 K) (Fin n → K)) :
      Set (Fin n → K)) = ⊤ := by
  classical
  obtain ⟨d0, hd0, h1, -⟩ := lc_sandwich L hL
  obtain ⟨d0', hd0'⟩ := sig_int σ d0
  have hd0'0 : d0' ≠ 0 := by
    intro h
    apply sig_ne_zero σ hd0
    rw [← hd0', h, map_zero]
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨e, he⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin n × Fin n => J p.1 p.2 * z p.2)
  set c : K := algebraMap (𝓞 K) K d0' * algebraMap (𝓞 K) K (e : 𝓞 K) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (algebraMap_ne_zero hd0'0) (algebraMap_ne_zero (nonZeroDivisors.ne_zero e.2))
  have hmem : c • z ∈ Formalism.BasicNotions.dualSet σ J L := by
    intro x hx
    have hx' := (lc_mem_colLat_one _).1 (h1 x hx)
    unfold Formalism.UG.hform
    refine Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => ?_
    obtain ⟨r, hr⟩ := (lc_mem_one_iff _).1 (hx' i)
    obtain ⟨r', hr'⟩ := sig_int σ r
    obtain ⟨q, hq⟩ := he (J i j * z j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    refine ⟨r' * q, ?_⟩
    rw [map_mul, hr', hq, hr, Pi.smul_apply, Algebra.smul_def, map_mul, ← hd0', Pi.smul_apply, smul_eq_mul,
      Algebra.smul_def, hc]
    ring
  have e2 : z = c⁻¹ • (c • z) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [e2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span hmem))

end Bound

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB
