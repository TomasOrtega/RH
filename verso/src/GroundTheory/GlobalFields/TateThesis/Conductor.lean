import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.InfiniteProjInfiniteEmbeddingOfNe
import GroundTheory.GlobalFields.IdeleGroups.Restricted
import GroundTheory.GlobalFields.TateThesis.LocalConductor

open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing RestrictedProduct

namespace GroundTheory.Global

noncomputable section

namespace IdeleGroup

variable {K : Type*} [Field K] [NumberField K]

def finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    (FiniteAdeleRing (𝓞 K) K)ˣ →* (v.adicCompletion K)ˣ :=
  Units.map (_root_.RestrictedProduct.evalMonoidHom
    (fun w : HeightOneSpectrum (𝓞 K) ↦ w.adicCompletion K) v)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_finiteComponent (v : HeightOneSpectrum (𝓞 K)) (x : (FiniteAdeleRing (𝓞 K) K)ˣ) :
    ((finiteComponent v x : (v.adicCompletion K)ˣ) : v.adicCompletion K) =
      (x : FiniteAdeleRing (𝓞 K) K) v :=
  rfl

/- English proof (translation)
The claim follows from `Units.continuous_map (_root_.RestrictedProduct.continuous_eval v)`.
-/
theorem continuous_finiteComponent (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteComponent (K := K) v) :=
  Units.continuous_map (_root_.RestrictedProduct.continuous_eval v)

def finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* (FiniteAdeleRing (𝓞 K) K)ˣ :=
  Units.map (finiteAdeleSingle v)

/- English proof (translation)
The claim follows from `Units.continuous_map (continuous_finiteAdeleSingle v) @[simp]`.
-/
theorem continuous_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K)) :
    Continuous (finiteUnitsSingle (K := K) v) :=
  Units.continuous_map (continuous_finiteAdeleSingle v)

@[simp]
/- English proof (translation)
Use `ext`. Simplify using `[finiteUnitsSingle]`.
-/
theorem finiteComponent_finiteUnitsSingle (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : finiteComponent v (finiteUnitsSingle v x) = x := by
  ext
  simp [finiteUnitsSingle]

/- English proof (translation)
Use `ext`. Simplify using `[finiteUnitsSingle, finiteAdeleSingle_apply_of_ne h]`.
-/
theorem finiteComponent_finiteUnitsSingle_of_ne {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : finiteComponent w (finiteUnitsSingle v x) = 1 := by
  ext
  simp [finiteUnitsSingle, finiteAdeleSingle_apply_of_ne h]

def finiteLevel (n : HeightOneSpectrum (𝓞 K) → ℕ) : Subgroup (FiniteAdeleRing (𝓞 K) K)ˣ :=
  ⨅ v, (unitsLevel v (n v)).comap (finiteComponent v)

/- English proof (translation)
Simplify using `only [finiteLevel, Subgroup.mem_iInf, Subgroup.mem_comap]`.
-/
theorem mem_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} {x : (FiniteAdeleRing (𝓞 K) K)ˣ} :
    x ∈ finiteLevel n ↔ ∀ v, finiteComponent v x ∈ unitsLevel v (n v) := by
  simp only [finiteLevel, Subgroup.mem_iInf, Subgroup.mem_comap]

/- English proof (translation)
The claim follows from `fun _ hx ↦ mem_finiteLevel.2 fun v ↦ unitsLevel_antitone v (h v) (mem_finiteLevel.1 hx v)`.
-/
theorem finiteLevel_antitone {m n : HeightOneSpectrum (𝓞 K) → ℕ} (h : m ≤ n) :
    finiteLevel n ≤ finiteLevel m := fun _ hx ↦
  mem_finiteLevel.2 fun v ↦ unitsLevel_antitone v (h v) (mem_finiteLevel.1 hx v)

/- English proof (translation)
The claim follows from `finiteLevel_antitone fun v ↦ Nat.zero_le (n v)`.
-/
theorem finiteLevel_le_finiteLevel_zero (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ finiteLevel 0 :=
  finiteLevel_antitone fun v ↦ Nat.zero_le (n v)

/- English proof (translation)
Use `mem_finiteLevel.2 fun w ↦ ?_` and prove the remaining obligations. Distinguish the cases in `h : w = v`. Substitute `h` using the available equality. Simplify using `using hx`. Rewrite using `[finiteComponent_finiteUnitsSingle_of_ne h]`.

Conclude with `one_mem _`.
-/
theorem finiteUnitsSingle_mem_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ}
    {v : HeightOneSpectrum (𝓞 K)} {x : (v.adicCompletion K)ˣ} (hx : x ∈ unitsLevel v (n v)) :
    finiteUnitsSingle v x ∈ finiteLevel n := by
  refine mem_finiteLevel.2 fun w ↦ ?_
  by_cases h : w = v
  · subst h
    simpa using hx
  · rw [finiteComponent_finiteUnitsSingle_of_ne h]
    exact one_mem _

/- English proof (translation)
The claim follows from `Units.ext rfl`.
-/
theorem finiteUnitsEquiv_apply_eq (x : (FiniteAdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    finiteUnitsEquiv K x v = finiteComponent v x :=
  Units.ext rfl

/- English proof (translation)
Establish `h` using `(_root_.RestrictedProduct.isOpen_forall_mem (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ) (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)) (fun v ↦ isOpen_units_adicCompletionIntegers K v)).preimage (finiteUnitsE …`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, mem_finiteLevel, Pi.zero_apply, unitsLevel_zero, Set.mem_preimage, Set.mem_ofPred_eq]`. Conclude with `forall_congr' fun v ↦ by rw [← finiteUnitsEquiv_apply_eq]; rfl`.
-/
theorem isOpen_finiteLevel_zero :
    IsOpen (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  have h := (_root_.RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ))
    (fun v ↦ isOpen_units_adicCompletionIntegers K v)).preimage (finiteUnitsEquiv K).continuous
  convert h using 1
  ext x
  simp only [SetLike.mem_coe, mem_finiteLevel, Pi.zero_apply, unitsLevel_zero, Set.mem_preimage,
    Set.mem_ofPred_eq]
  exact forall_congr' fun v ↦ by rw [← finiteUnitsEquiv_apply_eq]; rfl

/- English proof (translation)
Establish `: (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) = (finiteLevel (K` using `K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∩ ⋂ v ∈ hn.toFinset, finiteComponent v ⁻¹' (unitsLevel (K := K) v (n v) : Set (v.adicCompletion K)ˣ) := by`. Use extensionality with `x`. Simplify using `only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]`. Use `⟨fun hx ↦ ⟨finiteLevel_le_finiteLevel_zero n hx, fun v _ ↦ mem_finiteLevel.1 hx v⟩, fun ⟨h0, h⟩ ↦ mem_finiteLevel.2 fun v ↦ ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : n v = 0`.

Rewrite using `[hv]`. Conclude with `mem_finiteLevel.1 h0 v`. Conclude with `h v (by simpa using hv)`. Rewrite using `[this]`. Conclude with `isOpen_finiteLevel_zero.inter (isOpen_biInter_finset fun v _ ↦ (isOpen_unitsLevel v (n v)).preimage (continuous_finiteComponent v))`.
-/
theorem isOpen_finiteLevel {n : HeightOneSpectrum (𝓞 K) → ℕ} (hn : (support n).Finite) :
    IsOpen (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  have : (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) =
      (finiteLevel (K := K) 0 : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ∩
      ⋂ v ∈ hn.toFinset, finiteComponent v ⁻¹'
        (unitsLevel (K := K) v (n v) : Set (v.adicCompletion K)ˣ) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    refine ⟨fun hx ↦ ⟨finiteLevel_le_finiteLevel_zero n hx, fun v _ ↦ mem_finiteLevel.1 hx v⟩,
      fun ⟨h0, h⟩ ↦ mem_finiteLevel.2 fun v ↦ ?_⟩
    by_cases hv : n v = 0
    · rw [hv]
      exact mem_finiteLevel.1 h0 v
    · exact h v (by simpa using hv)
  rw [this]
  exact isOpen_finiteLevel_zero.inter (isOpen_biInter_finset fun v _ ↦
    (isOpen_unitsLevel v (n v)).preimage (continuous_finiteComponent v))

/- English proof (translation)
Set `e` to `finiteUnitsEquiv K`. Set `es` to `ContinuousMulEquiv.symm e`. Establish `hS : (cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 Set.univ` using `by simp`. Establish `hW1 : es ⁻¹' W ∈ 𝓝 (1 : Πʳ v : HeightOneSpectrum (𝓞 K), [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units])` using `es.continuous.continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (es 1); rwa [map_one es])`. Establish `hW2` using `(_root_.RestrictedProduct.continuous_inclusion (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ) (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units : Set (v.adicCompletion K)ˣ)) hS).continuousAt.preimage_mem_nhds (x := 1) hW1`.

Rewrite `hW2` using `[_root_.RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap, mem_comap]`. Take `⟨t, ht, htW⟩` from `hW2`. Rewrite `ht` using `[nhds_pi, Filter.mem_pi']`. Take `⟨I, u, hu, hIu⟩` from `ht`. Use `choose N hN hNu using fun v ↦ exists_unitsLevel_subset v (hu v)`.

Use `⟨I, fun v ↦ if v ∈ I then N v else 0, fun v hv ↦ by simp [hv, hN v], fun v hv ↦ by simp [hv], ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[SetLike.mem_coe, mem_finiteLevel]`. Establish `hx0 : ∀ v, e x v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units` using `fun v ↦ by`. Rewrite using `[finiteUnitsEquiv_apply_eq, ← unitsLevel_zero]`.

Conclude with `unitsLevel_antitone v (Nat.zero_le _) (hx v)`. Set `z : Πʳ v : HeightOneSpectrum (𝓞 K), [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[𝓟 Set.univ]` to `⟨fun v ↦ e x v, Filter.eventually_principal.2 fun v _ ↦ hx0 v⟩`. Establish `hz` using `htW (show (z : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) ∈ t from hIu fun v hv ↦ by`. Use `hx v` as an intermediate fact. Simplify using `only [Finset.mem_coe.1 hv, if_true] at this`.

Conclude with `hNu v (by rw [← finiteUnitsEquiv_apply_eq] at this; exact this))`. Establish `hzx : _root_.RestrictedProduct.inclusion _ _ hS z = e x` using `rfl`. Rewrite `hz` using `[Set.mem_preimage, Set.mem_preimage, hzx]`. Rewrite `hz` using `[show es (e x) = x from ContinuousMulEquiv.symm_apply_apply e x]`. Then use the resulting hypothesis.
-/
theorem exists_finiteLevel_subset {W : Set (FiniteAdeleRing (𝓞 K) K)ˣ} (hW : W ∈ 𝓝 1) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧
        (finiteLevel n : Set (FiniteAdeleRing (𝓞 K) K)ˣ) ⊆ W := by
  classical
  let e := finiteUnitsEquiv K
  let es := ContinuousMulEquiv.symm e
  have hS : (cofinite : Filter (HeightOneSpectrum (𝓞 K))) ≤ 𝓟 Set.univ := by simp
  have hW1 : es ⁻¹' W ∈ 𝓝 (1 : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]) :=
    es.continuous.continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (es 1); rwa [map_one es])
  have hW2 := (_root_.RestrictedProduct.continuous_inclusion
    (R := fun v : HeightOneSpectrum (𝓞 K) ↦ (v.adicCompletion K)ˣ)
    (A := fun v ↦ ((Submonoid.ofClass (v.adicCompletionIntegers K)).units :
      Set (v.adicCompletion K)ˣ)) hS).continuousAt.preimage_mem_nhds (x := 1) hW1
  rw [_root_.RestrictedProduct.isEmbedding_coe_of_principal.nhds_eq_comap, mem_comap] at hW2
  obtain ⟨t, ht, htW⟩ := hW2
  rw [nhds_pi, Filter.mem_pi'] at ht
  obtain ⟨I, u, hu, hIu⟩ := ht
  choose N hN hNu using fun v ↦ exists_unitsLevel_subset v (hu v)
  refine ⟨I, fun v ↦ if v ∈ I then N v else 0, fun v hv ↦ by simp [hv, hN v],
    fun v hv ↦ by simp [hv], ?_⟩
  intro x hx
  rw [SetLike.mem_coe, mem_finiteLevel] at hx
  have hx0 : ∀ v, e x v ∈ (Submonoid.ofClass (v.adicCompletionIntegers K)).units := fun v ↦ by
    rw [finiteUnitsEquiv_apply_eq, ← unitsLevel_zero]
    exact unitsLevel_antitone v (Nat.zero_le _) (hx v)
  let z : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (Submonoid.ofClass (v.adicCompletionIntegers K)).units]_[𝓟 Set.univ] :=
    ⟨fun v ↦ e x v, Filter.eventually_principal.2 fun v _ ↦ hx0 v⟩
  have hz := htW (show (z : Π v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ) ∈ t from
    hIu fun v hv ↦ by
      have := hx v
      simp only [Finset.mem_coe.1 hv, if_true] at this
      exact hNu v (by rw [← finiteUnitsEquiv_apply_eq] at this; exact this))
  have hzx : _root_.RestrictedProduct.inclusion _ _ hS z = e x := rfl
  rw [Set.mem_preimage, Set.mem_preimage, hzx] at hz
  rwa [show es (e x) = x from ContinuousMulEquiv.symm_apply_apply e x] at hz

section Character

variable {H : Type*} [Group H] [TopologicalSpace H]

/- English proof (translation)
Take `⟨L, ⟨S, n, h1, h0, rfl⟩, hL⟩` from `exists_le_ker_of_noSmallSubgroups (P := fun L ↦ ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ, (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ L = finiteLevel n) (fun W hW ↦ by`. Take `⟨S, n, h1, h0, h⟩` from `exists_finiteLevel_subset hW`. Conclude with `⟨_, ⟨S, n, h1, h0, rfl⟩, h⟩) hH χ hχ`. Conclude with `⟨S, n, h1, h0, hL⟩`.
-/
theorem exists_finiteLevel_le_ker (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ finiteLevel n ≤ χ.ker := by
  obtain ⟨L, ⟨S, n, h1, h0, rfl⟩, hL⟩ := exists_le_ker_of_noSmallSubgroups
    (P := fun L ↦ ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ L = finiteLevel n)
    (fun W hW ↦ by
      obtain ⟨S, n, h1, h0, h⟩ := exists_finiteLevel_subset hW
      exact ⟨_, ⟨S, n, h1, h0, rfl⟩, h⟩) hH χ hχ
  exact ⟨S, n, h1, h0, hL⟩

/- English proof (translation)
The claim follows from `exists_finiteLevel_le_ker Circle.noSmallSubgroups χ hχ`.
-/
theorem exists_finiteLevel_le_ker_circle (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* Circle)
    (hχ : Continuous χ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∃ n : HeightOneSpectrum (𝓞 K) → ℕ,
      (∀ v ∈ S, 1 ≤ n v) ∧ (∀ v ∉ S, n v = 0) ∧ finiteLevel n ≤ χ.ker :=
  exists_finiteLevel_le_ker Circle.noSmallSubgroups χ hχ

/- English proof (translation)
Take `⟨S, n, -, h0, hn⟩` from `exists_finiteLevel_le_ker hH χ hχ`. Use `Subgroup.isOpen_mono hn (isOpen_finiteLevel (S.finite_toSet.subset fun v hv ↦ ?_))` and prove the remaining obligations. Assume the negation of the conclusion as `hvS`. Conclude with `hv (h0 v hvS)`.
-/
theorem isOpen_ker_of_continuous (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) : IsOpen (χ.ker : Set (FiniteAdeleRing (𝓞 K) K)ˣ) := by
  obtain ⟨S, n, -, h0, hn⟩ := exists_finiteLevel_le_ker hH χ hχ
  refine Subgroup.isOpen_mono hn (isOpen_finiteLevel (S.finite_toSet.subset fun v hv ↦ ?_))
  by_contra hvS
  exact hv (h0 v hvS)

def conductorExponentAt (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  conductorExponent v (χ.comp (finiteUnitsSingle v))

/- English proof (translation)
Establish `hloc : ∀ v, Continuous (χ.comp (finiteUnitsSingle v))` using `fun v ↦ hχ.comp (continuous_finiteUnitsSingle v)`. Prove the components needed by the constructor for the conclusion. Introduce `h v`. Rewrite using `[conductorExponentAt, ← unitsLevel_le_ker_iff v hH _ (hloc v)]`. Introduce `x hx`.

Conclude with `h (finiteUnitsSingle_mem_finiteLevel hx)`. Introduce `h x hx classical`. Take `⟨S, n₀, -, h0, hker⟩` from `exists_finiteLevel_le_ker hH χ hχ`. Use `set p := ∏ v ∈ S, finiteUnitsSingle v (finiteComponent v x) with hp`. Establish `hcomp : ∀ w, finiteComponent w p = if w ∈ S then finiteComponent w x else 1`.

Introduce `w`. Rewrite using `[hp, map_prod]`. Use `split_ifs with hw`. Rewrite using `[Finset.prod_eq_single_of_mem w hw fun v _ hv ↦ finiteComponent_finiteUnitsSingle_of_ne (Ne.symm hv) _, finiteComponent_finiteUnitsSingle]`. Conclude with `Finset.prod_eq_one fun v hv ↦ finiteComponent_finiteUnitsSingle_of_ne (fun h ↦ hw (by rw [h]; exact hv)) _`.

Establish `hy : x * p⁻¹ ∈ finiteLevel n₀`. Use `mem_finiteLevel.2 fun w ↦ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_inv, hcomp]`. Use `split_ifs with hw`. Rewrite using `[mul_inv_cancel]`.

Conclude with `one_mem _`. Rewrite using `[inv_one, mul_one, h0 w hw]`. Conclude with `unitsLevel_antitone w (Nat.zero_le _) (mem_finiteLevel.1 hx w)`. Establish `hpk : p ∈ χ.ker` using `Subgroup.prod_mem _ fun v _ ↦ (unitsLevel_le_ker_iff v hH _ (hloc v)).2 (h v) (mem_finiteLevel.1 hx v)`. Establish `hxp : x = x * p⁻¹ * p` using `by rw [inv_mul_cancel_right]`.

Rewrite using `[hxp]`. Conclude with `mul_mem (hker hy) hpk`.
-/
theorem finiteLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (n : HeightOneSpectrum (𝓞 K) → ℕ) :
    finiteLevel n ≤ χ.ker ↔ ∀ v, conductorExponentAt χ v ≤ n v := by
  have hloc : ∀ v, Continuous (χ.comp (finiteUnitsSingle v)) := fun v ↦
    hχ.comp (continuous_finiteUnitsSingle v)
  constructor
  · intro h v
    rw [conductorExponentAt, ← unitsLevel_le_ker_iff v hH _ (hloc v)]
    intro x hx
    exact h (finiteUnitsSingle_mem_finiteLevel hx)
  · intro h x hx
    classical
    obtain ⟨S, n₀, -, h0, hker⟩ := exists_finiteLevel_le_ker hH χ hχ
    set p := ∏ v ∈ S, finiteUnitsSingle v (finiteComponent v x) with hp
    have hcomp : ∀ w, finiteComponent w p = if w ∈ S then finiteComponent w x else 1 := by
      intro w
      rw [hp, map_prod]
      split_ifs with hw
      · rw [Finset.prod_eq_single_of_mem w hw fun v _ hv ↦
          finiteComponent_finiteUnitsSingle_of_ne (Ne.symm hv) _,
          finiteComponent_finiteUnitsSingle]
      · exact Finset.prod_eq_one fun v hv ↦
          finiteComponent_finiteUnitsSingle_of_ne (fun h ↦ hw (by rw [h]; exact hv)) _
    have hy : x * p⁻¹ ∈ finiteLevel n₀ := by
      refine mem_finiteLevel.2 fun w ↦ ?_
      rw [map_mul, map_inv, hcomp]
      split_ifs with hw
      · rw [mul_inv_cancel]
        exact one_mem _
      · rw [inv_one, mul_one, h0 w hw]
        exact unitsLevel_antitone w (Nat.zero_le _) (mem_finiteLevel.1 hx w)
    have hpk : p ∈ χ.ker := Subgroup.prod_mem _ fun v _ ↦
      (unitsLevel_le_ker_iff v hH _ (hloc v)).2 (h v) (mem_finiteLevel.1 hx v)
    have hxp : x = x * p⁻¹ * p := by rw [inv_mul_cancel_right]
    rw [hxp]
    exact mul_mem (hker hy) hpk

/- English proof (translation)
Take `⟨S, n, -, h0, hker⟩` from `exists_finiteLevel_le_ker hH χ hχ`. Establish `h` using `(finiteLevel_le_ker_iff hH χ hχ n).1 hker`. Use `S.finite_toSet.subset fun v hv ↦ ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hvS`. Conclude with `hv (Nat.eq_zero_of_le_zero ((h v).trans (h0 v hvS).le))`.
-/
theorem finite_support_conductorExponentAt (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) :
    (support (conductorExponentAt χ)).Finite := by
  obtain ⟨S, n, -, h0, hker⟩ := exists_finiteLevel_le_ker hH χ hχ
  have h := (finiteLevel_le_ker_iff hH χ hχ n).1 hker
  refine S.finite_toSet.subset fun v hv ↦ ?_
  by_contra hvS
  exact hv (Nat.eq_zero_of_le_zero ((h v).trans (h0 v hvS).le))

/- English proof (translation)
The claim follows from `conductorExponent_eq_zero_iff v hH _ (hχ.comp (continuous_finiteUnitsSingle v))`.
-/
theorem conductorExponentAt_eq_zero_iff (hH : NoSmallSubgroups H)
    (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponentAt χ v = 0 ↔
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (χ.comp (finiteUnitsSingle v)).ker :=
  conductorExponent_eq_zero_iff v hH _ (hχ.comp (continuous_finiteUnitsSingle v))

end Character

end IdeleGroup

end

end GroundTheory.Global
