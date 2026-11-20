import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsOpenSubgroupMemFixedModule
import GroundTheory.LocalFields.AbstractLocalReciprocity.ExistsEqNsmulOfProjEqZero
import GroundTheory.LocalFields.AbstractLocalReciprocity.UniqueQuotientSubgroupOfSelf
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.RelIndexSup

namespace GroundTheory.LocalField.Abstract

section Degrees

variable {G : Type*} [Group G]

/- English proof (translation)
The claim follows from `_root_.GroundTheory.Variant₂.N1.relIndex_sup_of_le_normalizer hLE`.
-/
theorem relIndex_sup_of_le_normalizer {H N : Subgroup G} (hLE : H ≤ Subgroup.normalizer (N : Set G)) :
    H.relIndex (H ⊔ N) = H.relIndex N :=
  _root_.GroundTheory.Variant₂.N1.relIndex_sup_of_le_normalizer hLE

variable (d : G →* Multiplicative ℤ̂)

noncomputable def relInertiaDegree (K L : Subgroup G) : ℕ :=
  (L.map d).relIndex (K.map d)

noncomputable def relRamificationIndex (K L : Subgroup G) : ℕ :=
  L.relIndex (d.ker ⊓ K)

variable {d}

/- English proof (translation)
Rewrite using `[relRamificationIndex, ramificationIndex, inf_top_eq]`.
-/
theorem relRamificationIndex_top (K : Subgroup G) :
    relRamificationIndex d ⊤ K = ramificationIndex d K := by
  rw [relRamificationIndex, ramificationIndex, inf_top_eq]

/- English proof (translation)
Rewrite using `[relInertiaDegree, inertiaDegree, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top_of_surjective d hd, Subgroup.relIndex_top_right]`.
-/
theorem relInertiaDegree_top (hd : Function.Surjective d) (K : Subgroup G) :
    relInertiaDegree d ⊤ K = inertiaDegree d K := by
  rw [relInertiaDegree, inertiaDegree, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top_of_surjective d hd, Subgroup.relIndex_top_right]

/- English proof (translation)
The claim follows from `Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_mono hML) (Subgroup.map_mono hLK)`.
-/
theorem relInertiaDegree_mul {K L M : Subgroup G} (hML : M ≤ L) (hLK : L ≤ K) :
    relInertiaDegree d L M * relInertiaDegree d K L = relInertiaDegree d K M :=
  Subgroup.relIndex_mul_relIndex _ _ _ (Subgroup.map_mono hML) (Subgroup.map_mono hLK)

/- English proof (translation)
Unfold `relRamificationIndex`. Establish `h` using `Subgroup.relIndex_inf_mul_relIndex M L (d.ker ⊓ K)`. Establish `h1 : L ⊓ (d.ker ⊓ K) = d.ker ⊓ L`. Rewrite using `[inf_comm d.ker K, ← inf_assoc, inf_eq_left.2 hLK, inf_comm]`. Rewrite `h` using `[h1, inf_eq_left.2 hML]`.

Conclude with `h`.
-/
theorem relRamificationIndex_mul {K L M : Subgroup G} (hML : M ≤ L) (hLK : L ≤ K) :
    relRamificationIndex d L M * relRamificationIndex d K L = relRamificationIndex d K M := by
  unfold relRamificationIndex
  have h := Subgroup.relIndex_inf_mul_relIndex M L (d.ker ⊓ K)
  have h1 : L ⊓ (d.ker ⊓ K) = d.ker ⊓ L := by
    rw [inf_comm d.ker K, ← inf_assoc, inf_eq_left.2 hLK, inf_comm]
  rw [h1, inf_eq_left.2 hML] at h
  exact h

/- English proof (translation)
Rewrite using `[← relInertiaDegree_top hd, ← relInertiaDegree_top hd, relInertiaDegree_mul hLK le_top]`.
-/
theorem inertiaDegree_eq_mul (hd : Function.Surjective d) {K L : Subgroup G} (hLK : L ≤ K) :
    inertiaDegree d L = relInertiaDegree d K L * inertiaDegree d K := by
  rw [← relInertiaDegree_top hd, ← relInertiaDegree_top hd, relInertiaDegree_mul hLK le_top]

/- English proof (translation)
Rewrite using `[← relRamificationIndex_top, ← relRamificationIndex_top, relRamificationIndex_mul hLK le_top]`.
-/
theorem ramificationIndex_eq_mul {K L : Subgroup G} (hLK : L ≤ K) :
    ramificationIndex d L = relRamificationIndex d K L * ramificationIndex d K := by
  rw [← relRamificationIndex_top, ← relRamificationIndex_top, relRamificationIndex_mul hLK le_top]

/- English proof (translation)
Establish `hP : L ⊔ (d.ker ⊓ K) ≤ K` using `sup_le hLK inf_le_right`. Rewrite using `[← Subgroup.relIndex_mul_relIndex L (L ⊔ (d.ker ⊓ K)) K le_sup_left hP]`. Use `congr 1`. Rewrite using `[relRamificationIndex]`. Use `relIndex_sup_of_le_normalizer ?_` and prove the remaining obligations.

Introduce `g hg`. Rewrite using `[Subgroup.mem_normalizer_iff]`. Introduce `x`. Establish `hgK : g ∈ K` using `hLK hg`. Simplify using `only [Subgroup.mem_inf, MonoidHom.mem_ker, map_mul, map_inv]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨?_, K.mul_mem (K.mul_mem hgK h2) (K.inv_mem hgK)⟩` and prove the remaining obligations. Rewrite using `[h1, mul_one, mul_inv_cancel]`. Introduce and unpack `⟨h1, h2⟩`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: d x = (d g)⁻¹ * (d g * d x * (d g)⁻¹) * d g` using `by group`. Rewrite using `[this, h1]`. Use `group`. Establish `: x = g⁻¹ * (g * x * g⁻¹) * g` using `by group`.

Rewrite using `[this]`. Conclude with `K.mul_mem (K.mul_mem (K.inv_mem hgK) h2) hgK`. Rewrite using `[relInertiaDegree, ← Subgroup.relIndex_comap, Subgroup.comap_map_eq, ← Subgroup.inf_relIndex_right (L ⊔ d.ker) K]`. Use `congr 1`. Use `le_antisymm (le_inf (sup_le_sup_left inf_le_left L) hP) ?_` and prove the remaining obligations.

Introduce `x hx`. Take `⟨hx1, hx2⟩` from `Subgroup.mem_inf.1 hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Subgroup.mem_sup_of_normal_right.1 hx1`. Establish `hzK : z ∈ K`. Use `K.mul_mem (K.inv_mem (hLK hy)) hx2` as an intermediate fact.

Simplify using `using this`. Conclude with `Subgroup.mul_mem_sup hy (Subgroup.mem_inf.2 ⟨hz, hzK⟩)`.
-/
theorem relIndex_eq_mul {K L : Subgroup G} (hLK : L ≤ K) :
    L.relIndex K = relRamificationIndex d K L * relInertiaDegree d K L := by
  have hP : L ⊔ (d.ker ⊓ K) ≤ K := sup_le hLK inf_le_right
  rw [← Subgroup.relIndex_mul_relIndex L (L ⊔ (d.ker ⊓ K)) K le_sup_left hP]
  congr 1
  · rw [relRamificationIndex]
    refine relIndex_sup_of_le_normalizer ?_
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgK : g ∈ K := hLK hg
    simp only [Subgroup.mem_inf, MonoidHom.mem_ker, map_mul, map_inv]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, K.mul_mem (K.mul_mem hgK h2) (K.inv_mem hgK)⟩
      rw [h1, mul_one, mul_inv_cancel]
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · have : d x = (d g)⁻¹ * (d g * d x * (d g)⁻¹) * d g := by group
        rw [this, h1]; group
      · have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
        rw [this]
        exact K.mul_mem (K.mul_mem (K.inv_mem hgK) h2) hgK
  · rw [relInertiaDegree, ← Subgroup.relIndex_comap, Subgroup.comap_map_eq,
      ← Subgroup.inf_relIndex_right (L ⊔ d.ker) K]
    congr 1
    refine le_antisymm (le_inf (sup_le_sup_left inf_le_left L) hP) ?_
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hx1
    have hzK : z ∈ K := by
      have := K.mul_mem (K.inv_mem (hLK hy)) hx2
      simpa using this
    exact Subgroup.mul_mem_sup hy (Subgroup.mem_inf.2 ⟨hz, hzK⟩)

/- English proof (translation)
Rewrite using `[← relRamificationIndex_top, ← relInertiaDegree_top hd, ← relIndex_eq_mul le_top, Subgroup.relIndex_top_right]`.
-/
theorem index_eq_mul (hd : Function.Surjective d) (K : Subgroup G) :
    K.index = ramificationIndex d K * inertiaDegree d K := by
  rw [← relRamificationIndex_top, ← relInertiaDegree_top hd, ← relIndex_eq_mul le_top,
    Subgroup.relIndex_top_right]

end Degrees

section PowProfinite

namespace ProfiniteInteger

/- English proof (translation)
Introduce `x y h`. Apply `Multiplicative.toAdd.injective` to reduce the goal to its premises. Establish `h' : n • Multiplicative.toAdd x = n • Multiplicative.toAdd y`. Rewrite using `[← toAdd_pow, ← toAdd_pow]`. Conclude with `congrArg Multiplicative.toAdd h`.

Conclude with `nsmul_right_injective hn h'`.
-/
theorem pow_left_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun x : Multiplicative ℤ̂ => x ^ n) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  have h' : n • Multiplicative.toAdd x = n • Multiplicative.toAdd y := by
    rw [← toAdd_pow, ← toAdd_pow]
    exact congrArg Multiplicative.toAdd h
  exact nsmul_right_injective hn h'

/- English proof (translation)
The claim follows from `(pow_left_injective hn).eq_iff`.
-/
theorem pow_left_inj {n : ℕ} (hn : n ≠ 0) {x y : Multiplicative ℤ̂} : x ^ n = y ^ n ↔ x = y :=
  (pow_left_injective hn).eq_iff

/- English proof (translation)
Establish `hi : (Subgroup.toAddSubgroup' H).index = H.index` using `rfl`. Establish `h` using `eq_multiples_index (H := Subgroup.toAddSubgroup' H) (by rwa [hi])`. Rewrite `h` using `[hi]`. Establish `hx : x ∈ H ↔ Multiplicative.toAdd x ∈ Subgroup.toAddSubgroup' H` using `Iff.rfl`. Rewrite using `[hx, h, mem_multiples]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Use `⟨Multiplicative.ofAdd y, Multiplicative.toAdd.injective ?_⟩` and prove the remaining obligations. Rewrite using `[toAdd_pow, toAdd_ofAdd, hy]`. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨Multiplicative.toAdd y, by rw [toAdd_pow]⟩`.
-/
theorem mem_of_index_ne_zero {H : Subgroup (Multiplicative ℤ̂)} (hH : H.index ≠ 0)
    {x : Multiplicative ℤ̂} : x ∈ H ↔ ∃ y, y ^ H.index = x := by
  have hi : (Subgroup.toAddSubgroup' H).index = H.index := rfl
  have h := eq_multiples_index (H := Subgroup.toAddSubgroup' H) (by rwa [hi])
  rw [hi] at h
  have hx : x ∈ H ↔ Multiplicative.toAdd x ∈ Subgroup.toAddSubgroup' H := Iff.rfl
  rw [hx, h, mem_multiples]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨Multiplicative.ofAdd y, Multiplicative.toAdd.injective ?_⟩
    rw [toAdd_pow, toAdd_ofAdd, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨Multiplicative.toAdd y, by rw [toAdd_pow]⟩

/- English proof (translation)
Establish `h : Subgroup.toAddSubgroup' (powMonoidHom n : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range = multiples n`. Use extensionality with `x`. Rewrite using `[mem_multiples]`. Express the relevant statement in the definitionally equal form `Multiplicative.ofAdd x ∈ (powMonoidHom n).range ↔ _`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy⟩`. Use `⟨Multiplicative.toAdd y, ?_⟩` and prove the remaining obligations. Rewrite using `[← toAdd_pow, ← powMonoidHom_apply, hy, toAdd_ofAdd]`. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨Multiplicative.ofAdd y, by rw [powMonoidHom_apply, ← ofAdd_nsmul]⟩`.

Establish `hi` using `index_multiples ⟨n, Nat.pos_of_ne_zero hn⟩`. Simplify using `only [PNat.mk_coe] at hi`. Rewrite `hi` using `[← h]`. Conclude with `hi`.
-/
theorem index_range_powMonoidHom {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range.index = n := by
  have h : Subgroup.toAddSubgroup' (powMonoidHom n : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range =
      multiples n := by
    ext x
    rw [mem_multiples]
    change Multiplicative.ofAdd x ∈ (powMonoidHom n).range ↔ _
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨Multiplicative.toAdd y, ?_⟩
      rw [← toAdd_pow, ← powMonoidHom_apply, hy, toAdd_ofAdd]
    · rintro ⟨y, rfl⟩
      exact ⟨Multiplicative.ofAdd y, by rw [powMonoidHom_apply, ← ofAdd_nsmul]⟩
  have hi := index_multiples ⟨n, Nat.pos_of_ne_zero hn⟩
  simp only [PNat.mk_coe] at hi
  rw [← h] at hi
  exact hi

end ProfiniteInteger

end PowProfinite

namespace ClassFieldData

open ProfiniteInteger

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)

/- English proof (translation)
Introduce `h` and use `Subgroup.FiniteIndex.index_ne_zero (H := (K : Subgroup G)) (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_map_dvd _ D.surjective_deg))`.
-/
theorem inertiaDegree_ne_zero (K : OpenSubgroup G) : inertiaDegree D.deg K ≠ 0 :=
  fun h => Subgroup.FiniteIndex.index_ne_zero (H := (K : Subgroup G))
    (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_map_dvd _ D.surjective_deg))

/- English proof (translation)
The claim follows from `mem_of_index_ne_zero (D.inertiaDegree_ne_zero K)`.
-/
theorem mem_map_deg_iff (K : OpenSubgroup G) {x : Multiplicative ℤ̂} :
    x ∈ (K : Subgroup G).map D.deg ↔ ∃ y, y ^ inertiaDegree D.deg K = x :=
  mem_of_index_ne_zero (D.inertiaDegree_ne_zero K)

/- English proof (translation)
The claim follows from `(D.mem_map_deg_iff K).1 ⟨σ, σ.2, rfl⟩`.
-/
theorem exists_pow_eq_deg (K : OpenSubgroup G) (σ : (K : Subgroup G)) :
    ∃ x, x ^ inertiaDegree D.deg K = D.deg σ :=
  (D.mem_map_deg_iff K).1 ⟨σ, σ.2, rfl⟩

noncomputable def relDeg (K : OpenSubgroup G) : (K : Subgroup G) →* Multiplicative ℤ̂ where
  toFun σ := (D.exists_pow_eq_deg K σ).choose
  map_one' := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_pow_eq_deg K 1).choose_spec, one_pow, OneMemClass.coe_one, map_one]
  map_mul' σ τ := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_pow_eq_deg K (σ * τ)).choose_spec, mul_pow, (D.exists_pow_eq_deg K σ).choose_spec,
      (D.exists_pow_eq_deg K τ).choose_spec, Subgroup.coe_mul, map_mul]

/- English proof (translation)
The claim follows from `(D.exists_pow_eq_deg K σ).choose_spec`.
-/
theorem relDeg_pow (K : OpenSubgroup G) (σ : (K : Subgroup G)) :
    D.relDeg K σ ^ inertiaDegree D.deg K = D.deg σ :=
  (D.exists_pow_eq_deg K σ).choose_spec

/- English proof (translation)
Rewrite using `[← ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K), relDeg_pow]`.
-/
theorem relDeg_eq_iff (K : OpenSubgroup G) (σ : (K : Subgroup G)) (x : Multiplicative ℤ̂) :
    D.relDeg K σ = x ↔ D.deg σ = x ^ inertiaDegree D.deg K := by
  rw [← ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K), relDeg_pow]

/- English proof (translation)
Introduce `x`. Take `⟨σ, hσ, hσx⟩` from `(D.mem_map_deg_iff K).2 ⟨x, rfl⟩`. Conclude with `⟨⟨σ, hσ⟩, (D.relDeg_eq_iff K _ x).2 hσx⟩`.
-/
theorem relDeg_surjective (K : OpenSubgroup G) : Function.Surjective (D.relDeg K) := by
  intro x
  obtain ⟨σ, hσ, hσx⟩ := (D.mem_map_deg_iff K).2 ⟨x, rfl⟩
  exact ⟨⟨σ, hσ⟩, (D.relDeg_eq_iff K _ x).2 hσx⟩

/- English proof (translation)
Establish `hp : Topology.IsClosedEmbedding (fun x : Multiplicative ℤ̂ => x ^ inertiaDegree D.deg K)` using `(continuous_pow _).isClosedEmbedding (ProfiniteInteger.pow_left_injective (D.inertiaDegree_ne_zero K))`. Rewrite using `[hp.isEmbedding.continuous_iff]`. Establish `h : ((fun x : Multiplicative ℤ̂ => x ^ inertiaDegree D.deg K) ∘ D.relDeg K) = D.deg ∘ Subtype.val` using `funext (D.relDeg_pow K)`. Rewrite using `[h]`. Conclude with `D.continuous_deg.comp continuous_subtype_val`.
-/
theorem continuous_relDeg (K : OpenSubgroup G) : Continuous (D.relDeg K) := by
  have hp : Topology.IsClosedEmbedding (fun x : Multiplicative ℤ̂ => x ^ inertiaDegree D.deg K) :=
    (continuous_pow _).isClosedEmbedding (ProfiniteInteger.pow_left_injective (D.inertiaDegree_ne_zero K))
  rw [hp.isEmbedding.continuous_iff]
  have h : ((fun x : Multiplicative ℤ̂ => x ^ inertiaDegree D.deg K) ∘ D.relDeg K) =
      D.deg ∘ Subtype.val := funext (D.relDeg_pow K)
  rw [h]
  exact D.continuous_deg.comp continuous_subtype_val

/- English proof (translation)
Establish `hf` using `inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨σ, hσ, rfl⟩`. Take `⟨y, hy⟩` from `D.exists_pow_eq_deg L ⟨σ, hσ⟩`. Use `⟨y, ?_⟩` and prove the remaining obligations.

Rewrite using `[eq_comm, relDeg_eq_iff, ← pow_mul, ← hf]`. Conclude with `hy.symm`. Introduce and unpack `⟨y, rfl⟩`. Take `⟨σ, hσ, hσy⟩` from `(D.mem_map_deg_iff L).2 ⟨y, rfl⟩`. Use `⟨⟨σ, hLK hσ⟩, hσ, ?_⟩` and prove the remaining obligations.

Rewrite using `[relDeg_eq_iff, ← pow_mul, ← hf]`. Conclude with `hσy`.
-/
theorem mem_map_relDeg_iff {K L : OpenSubgroup G} (hLK : L ≤ K) {x : Multiplicative ℤ̂} :
    x ∈ ((L : Subgroup G).subgroupOf K).map (D.relDeg K) ↔
      ∃ y, y ^ relInertiaDegree D.deg K L = x := by
  have hf := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨y, hy⟩ := D.exists_pow_eq_deg L ⟨σ, hσ⟩
    refine ⟨y, ?_⟩
    rw [eq_comm, relDeg_eq_iff, ← pow_mul, ← hf]
    exact hy.symm
  · rintro ⟨y, rfl⟩
    obtain ⟨σ, hσ, hσy⟩ := (D.mem_map_deg_iff L).2 ⟨y, rfl⟩
    refine ⟨⟨σ, hLK hσ⟩, hσ, ?_⟩
    rw [relDeg_eq_iff, ← pow_mul, ← hf]
    exact hσy

/- English proof (translation)
Establish `hf` using `inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK`. Establish `hne : relInertiaDegree D.deg K L ≠ 0` using `fun h => D.inertiaDegree_ne_zero L (by rw [hf, h, zero_mul])`. Establish `h : ((L : Subgroup G).subgroupOf K).map (D.relDeg K) = (powMonoidHom (relInertiaDegree D.deg K L) : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range`. Use extensionality with `x`. Rewrite using `[D.mem_map_relDeg_iff hLK]`.

Both sides reduce to the same expression. Rewrite using `[inertiaDegree, h, index_range_powMonoidHom hne]`.
-/
theorem inertiaDegree_relDeg {K L : OpenSubgroup G} (hLK : L ≤ K) :
    inertiaDegree (D.relDeg K) ((L : Subgroup G).subgroupOf K) = relInertiaDegree D.deg K L := by
  have hf := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK
  have hne : relInertiaDegree D.deg K L ≠ 0 := fun h => D.inertiaDegree_ne_zero L (by rw [hf, h, zero_mul])
  have h : ((L : Subgroup G).subgroupOf K).map (D.relDeg K) =
      (powMonoidHom (relInertiaDegree D.deg K L) : Multiplicative ℤ̂ →* Multiplicative ℤ̂).range := by
    ext x
    rw [D.mem_map_relDeg_iff hLK]
    rfl
  rw [inertiaDegree, h, index_range_powMonoidHom hne]

/- English proof (translation)
Introduce `h` and use `D.inertiaDegree_ne_zero L (by rw [inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK, h, zero_mul])`.
-/
theorem relInertiaDegree_ne_zero {K L : OpenSubgroup G} (hLK : L ≤ K) :
    relInertiaDegree D.deg K L ≠ 0 := fun h =>
  D.inertiaDegree_ne_zero L (by
    rw [inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK, h,
      zero_mul])

/- English proof (translation)
Establish `h : D.val (norm A ⊤ (K : Subgroup G) a) ∈ (D.val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range` using `⟨a, rfl⟩`. Rewrite `h` using `[D.range_val_comp_norm K]`. Take `⟨z, hz, hza⟩` from `h`. Conclude with `⟨z, hz, hza⟩`.
-/
theorem exists_valuation (K : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) :
    ∃ z ∈ D.val.range, z ^ inertiaDegree D.deg K = D.val (norm A ⊤ (K : Subgroup G) a) := by
  have h : D.val (norm A ⊤ (K : Subgroup G) a) ∈ (D.val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range :=
    ⟨a, rfl⟩
  rw [D.range_val_comp_norm K] at h
  obtain ⟨z, hz, hza⟩ := h
  exact ⟨z, hz, hza⟩

noncomputable def valuation (K : OpenSubgroup G) : fixedModule A (K : Subgroup G) →* Multiplicative ℤ̂ where
  toFun a := (D.exists_valuation K a).choose
  map_one' := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_valuation K 1).choose_spec.2, one_pow, map_one, map_one]
  map_mul' a b := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [(D.exists_valuation K (a * b)).choose_spec.2, mul_pow, (D.exists_valuation K a).choose_spec.2,
      (D.exists_valuation K b).choose_spec.2, map_mul, map_mul]

/- English proof (translation)
The claim follows from `(D.exists_valuation K a).choose_spec.2`.
-/
theorem valuation_pow (K : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) :
    D.valuation K a ^ inertiaDegree D.deg K = D.val (norm A ⊤ (K : Subgroup G) a) :=
  (D.exists_valuation K a).choose_spec.2

/- English proof (translation)
Rewrite using `[← ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K), valuation_pow]`.
-/
theorem valuation_eq_iff (K : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) (z : Multiplicative ℤ̂) :
    D.valuation K a = z ↔ D.val (norm A ⊤ (K : Subgroup G) a) = z ^ inertiaDegree D.deg K := by
  rw [← ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K), valuation_pow]

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Conclude with `(D.exists_valuation K a).choose_spec.1`. Introduce `hz`.

Establish `h : z ^ inertiaDegree D.deg K ∈ (D.val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range`. Rewrite using `[D.range_val_comp_norm K]`. Conclude with `⟨z, hz, rfl⟩`. Take `⟨a, ha⟩` from `h`. Conclude with `⟨a, (D.valuation_eq_iff K a z).2 ha⟩`.
-/
theorem range_valuation (K : OpenSubgroup G) : (D.valuation K).range = D.val.range := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    exact (D.exists_valuation K a).choose_spec.1
  · intro hz
    have h : z ^ inertiaDegree D.deg K ∈
        (D.val.comp (norm A (⊤ : Subgroup G) (K : Subgroup G))).range := by
      rw [D.range_val_comp_norm K]
      exact ⟨z, hz, rfl⟩
    obtain ⟨a, ha⟩ := h
    exact ⟨a, (D.valuation_eq_iff K a z).2 ha⟩

noncomputable def units (K : OpenSubgroup G) : Subgroup (fixedModule A (K : Subgroup G)) :=
  (D.valuation K).ker

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_units {K : OpenSubgroup G} {a : fixedModule A (K : Subgroup G)} : a ∈ D.units K ↔ D.valuation K a = 1 :=
  Iff.rfl

/- English proof (translation)
Rewrite using `[valuation_eq_iff, norm_norm (M := (L : Subgroup G)) (L := (K : Subgroup G)) hLK le_top, ← valuation_pow, ← pow_mul, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK]`.
-/
theorem valuation_norm {K L : OpenSubgroup G} (hLK : L ≤ K) (a : fixedModule A (L : Subgroup G)) :
    D.valuation K (norm A (K : Subgroup G) (L : Subgroup G) a) = D.valuation L a ^ relInertiaDegree D.deg K L := by
  rw [valuation_eq_iff, norm_norm (M := (L : Subgroup G)) (L := (K : Subgroup G)) hLK le_top, ← valuation_pow,
    ← pow_mul, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (L : Subgroup G)) hLK]

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, rfl⟩`. Use `⟨D.valuation L a, ?_, (D.valuation_norm hLK a).symm⟩` and prove the remaining obligations. Rewrite using `[range_valuation, ← D.range_valuation L]`.

Conclude with `⟨a, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite `hy` using `[range_valuation, ← D.range_valuation L]`. Take `⟨a, rfl⟩` from `hy`. Conclude with `⟨a, D.valuation_norm hLK a⟩`.
-/
theorem range_valuation_comp_norm {K L : OpenSubgroup G} (hLK : L ≤ K) :
    ((D.valuation K).comp (norm A (K : Subgroup G) (L : Subgroup G))).range =
      (D.valuation K).range.map (powMonoidHom (relInertiaDegree D.deg K L)) := by
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨D.valuation L a, ?_, (D.valuation_norm hLK a).symm⟩
    rw [range_valuation, ← D.range_valuation L]
    exact ⟨a, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    rw [range_valuation, ← D.range_valuation L] at hy
    obtain ⟨a, rfl⟩ := hy
    exact ⟨a, D.valuation_norm hLK a⟩

/- English proof (translation)
Use `(ProfiniteInteger.pow_left_inj (D.relInertiaDegree_ne_zero hLK)).1 ?_` and prove the remaining obligations. Rewrite using `[← valuation_norm D hLK, ← pow_mul, ← relIndex_eq_mul hLK]`. Establish `hn : norm A (K : Subgroup G) (L : Subgroup G) ⟨a, fixedModule_anti hLK ha⟩ = ⟨a, ha⟩ ^ (L : Subgroup G).relIndex K` using `Subtype.ext (by rw [coe_norm_of_mem hLK ha]; rfl)`. Rewrite using `[hn, map_pow]`.
-/
theorem valuation_of_mem {K L : OpenSubgroup G} (hLK : L ≤ K) {a : A} (ha : a ∈ fixedModule A (K : Subgroup G)) :
    D.valuation L ⟨a, fixedModule_anti hLK ha⟩ =
      D.valuation K ⟨a, ha⟩ ^ relRamificationIndex D.deg K L := by
  refine (ProfiniteInteger.pow_left_inj (D.relInertiaDegree_ne_zero hLK)).1 ?_
  rw [← valuation_norm D hLK, ← pow_mul, ← relIndex_eq_mul hLK]
  have hn : norm A (K : Subgroup G) (L : Subgroup G) ⟨a, fixedModule_anti hLK ha⟩ =
      ⟨a, ha⟩ ^ (L : Subgroup G).relIndex K :=
    Subtype.ext (by rw [coe_norm_of_mem hLK ha]; rfl)
  rw [hn, map_pow]

end ClassFieldData

end GroundTheory.LocalField.Abstract
