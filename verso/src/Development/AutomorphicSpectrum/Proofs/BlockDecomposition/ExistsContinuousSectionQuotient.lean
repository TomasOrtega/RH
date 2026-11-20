import Mathlib
import GroundTheory.AutomorphicForms.LocallyProfinite

open Topology Filter Set

namespace GlobalTheory.CompanionTheory.LGroupSection

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def cosetImage (H K : Subgroup G) (d : G) : Set (G ⧸ H) :=
  {x | ∃ k ∈ K, ((d * k : G) : G ⧸ H) = x}

/- English proof (translation)
Establish `himg : cosetImage H K d = ((↑) : G → G ⧸ H) '' ((fun k : G => d * k) '' (K : Set G))`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨d * k, ⟨k, hk, rfl⟩, rfl⟩`.

Introduce and unpack `⟨_, ⟨k, hk, rfl⟩, rfl⟩`. Conclude with `⟨k, hk, rfl⟩`. Rewrite using `[himg]`. Establish `hopen : IsOpen ((fun k : G => d * k) '' (K : Set G))` using `(Homeomorph.mulLeft d).isOpenMap _ hKo`. Establish `hcomp : IsCompact ((fun k : G => d * k) '' (K : Set G))` using `hKc.image (continuous_const.mul continuous_id)`.

Establish `hcomp' : IsCompact (((↑) : G → G ⧸ H) '' ((fun k : G => d * k) '' (K : Set G)))` using `hcomp.image continuous_quotient_mk'`. Conclude with `⟨hcomp'.isClosed, QuotientGroup.isOpenMap_coe _ hopen⟩`.
-/
theorem isClopen_cosetImage (H K : Subgroup G) [IsClosed (H : Set G)]
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G)) (d : G) :
    IsClopen (cosetImage H K d) := by
  have himg : cosetImage H K d =
      ((↑) : G → G ⧸ H) '' ((fun k : G => d * k) '' (K : Set G)) := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨d * k, ⟨k, hk, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨k, hk, rfl⟩
  rw [himg]
  have hopen : IsOpen ((fun k : G => d * k) '' (K : Set G)) :=
    (Homeomorph.mulLeft d).isOpenMap _ hKo
  have hcomp : IsCompact ((fun k : G => d * k) '' (K : Set G)) :=
    hKc.image (continuous_const.mul continuous_id)
  have hcomp' : IsCompact (((↑) : G → G ⧸ H) '' ((fun k : G => d * k) '' (K : Set G))) :=
    hcomp.image continuous_quotient_mk'
  exact ⟨hcomp'.isClosed, QuotientGroup.isOpenMap_coe _ hopen⟩

/- English proof (translation)
Use `⟨fun x => Nat.find (hcov x), ?_, fun x => Nat.find_spec (hcov x)⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_exists_open]`. Introduce `x`. Use `⟨V (Nat.find (hcov x)) ∩ ⋂ j ∈ Finset.range (Nat.find (hcov x)), (V j)ᶜ, (hV _).isOpen.inter (isOpen_biInter_finset fun j _ => (hV j).compl.isOpen), ?_, ?_⟩` and prove the remaining obligations. Use `⟨Nat.find_spec (hcov x), ?_⟩` and prove the remaining obligations.

Simplify using `only [mem_iInter, Finset.mem_range]`. Conclude with `fun j hj => Nat.find_min (hcov x) hj`. Introduce and unpack `y ⟨hy1, hy2⟩`. Simplify using `only [mem_iInter, Finset.mem_range] at hy2`. Use `le_antisymm (Nat.find_min' _ hy1) ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hlt`. Conclude with `hy2 _ (not_le.1 hlt) (Nat.find_spec (hcov y))`.
-/
theorem exists_isLocallyConstant_mem {X : Type*} [TopologicalSpace X] (V : ℕ → Set X)
    (hV : ∀ n, IsClopen (V n)) (hcov : ∀ x, ∃ n, x ∈ V n) :
    ∃ f : X → ℕ, IsLocallyConstant f ∧ ∀ x, x ∈ V (f x) := by
  classical
  refine ⟨fun x => Nat.find (hcov x), ?_, fun x => Nat.find_spec (hcov x)⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨V (Nat.find (hcov x)) ∩ ⋂ j ∈ Finset.range (Nat.find (hcov x)), (V j)ᶜ,
    (hV _).isOpen.inter (isOpen_biInter_finset fun j _ => (hV j).compl.isOpen), ?_, ?_⟩
  · refine ⟨Nat.find_spec (hcov x), ?_⟩
    simp only [mem_iInter, Finset.mem_range]
    exact fun j hj => Nat.find_min (hcov x) hj
  · rintro y ⟨hy1, hy2⟩
    simp only [mem_iInter, Finset.mem_range] at hy2
    refine le_antisymm (Nat.find_min' _ hy1) ?_
    by_contra hlt
    exact hy2 _ (not_le.1 hlt) (Nat.find_spec (hcov y))

/- English proof (translation)
Set `e : ℕ → G` to `TopologicalSpace.denseSeq G`. Establish `he : DenseRange e` using `TopologicalSpace.denseRange_denseSeq G`. Set `V : ℕ → Set (G ⧸ H)` to `fun n => (t ⁻¹' {g | g⁻¹ * e n ∈ K}) ∩ cosetImage H L (e n)`. Establish `hV : ∀ n, IsClopen (V n)` using `fun n => IsClopen.inter ⟨isOpen_compl_iff.1 (ht _ᶜ), ht _⟩ (isClopen_cosetImage H L hLo hLc (e n))`. Establish `hcov : ∀ x, ∃ n, x ∈ V n`.

Introduce `x`. Take `⟨k, hk, hkx⟩` from `h x`. Establish `hopen : IsOpen ((fun l : G => t x * k * l) '' (L : Set G))` using `(Homeomorph.mulLeft (t x * k)).isOpenMap _ hLo`. Take `⟨n, l, hl, hn⟩` from `he.exists_mem_open hopen ⟨t x * k * 1, 1, L.one_mem, rfl⟩`. Use `⟨n, ?_, l⁻¹, L.inv_mem hl, ?_⟩` and prove the remaining obligations.

Simplify using `only [mem_preimage, mem_setOf_eq, ← hn]`. Establish `: (t x)⁻¹ * (t x * k * l) = k * l` using `by group`. Rewrite using `[this]`. Conclude with `K.mul_mem hk (hLK hl)`. Rewrite using `[← hn, mul_inv_cancel_right]`.

Conclude with `hkx`. Take `⟨f, hf, hfV⟩` from `exists_isLocallyConstant_mem V hV hcov`. Conclude with `⟨fun x => e (f x), hf.comp e, fun x => (hfV x).2, fun x => (hfV x).1⟩`.
-/
theorem exists_refine [SecondCountableTopology G] (H K L : Subgroup G) [IsClosed (H : Set G)]
    (hLK : L ≤ K) (hLo : IsOpen (L : Set G)) (hLc : IsCompact (L : Set G))
    (t : G ⧸ H → G) (ht : IsLocallyConstant t) (h : ∀ x, x ∈ cosetImage H K (t x)) :
    ∃ t' : G ⧸ H → G, IsLocallyConstant t' ∧ (∀ x, x ∈ cosetImage H L (t' x)) ∧
      ∀ x, (t x)⁻¹ * t' x ∈ K := by
  let e : ℕ → G := TopologicalSpace.denseSeq G
  have he : DenseRange e := TopologicalSpace.denseRange_denseSeq G
  let V : ℕ → Set (G ⧸ H) := fun n =>
    (t ⁻¹' {g | g⁻¹ * e n ∈ K}) ∩ cosetImage H L (e n)
  have hV : ∀ n, IsClopen (V n) := fun n =>
    IsClopen.inter ⟨isOpen_compl_iff.1 (ht _ᶜ), ht _⟩ (isClopen_cosetImage H L hLo hLc (e n))
  have hcov : ∀ x, ∃ n, x ∈ V n := by
    intro x
    obtain ⟨k, hk, hkx⟩ := h x
    have hopen : IsOpen ((fun l : G => t x * k * l) '' (L : Set G)) :=
      (Homeomorph.mulLeft (t x * k)).isOpenMap _ hLo
    obtain ⟨n, l, hl, hn⟩ := he.exists_mem_open hopen ⟨t x * k * 1, 1, L.one_mem, rfl⟩
    refine ⟨n, ?_, l⁻¹, L.inv_mem hl, ?_⟩
    · simp only [mem_preimage, mem_setOf_eq, ← hn]
      have : (t x)⁻¹ * (t x * k * l) = k * l := by group
      rw [this]
      exact K.mul_mem hk (hLK hl)
    · rw [← hn, mul_inv_cancel_right]
      exact hkx
  obtain ⟨f, hf, hfV⟩ := exists_isLocallyConstant_mem V hV hcov
  exact ⟨fun x => e (f x), hf.comp e, fun x => (hfV x).2, fun x => (hfV x).1⟩

/- English proof (translation)
Take `⟨U, hU⟩` from `(𝓝 (1 : G)).exists_antitone_basis`. Use `choose L hLc hLU using fun n => GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset (hU.1.mem_of_mem (i := n) trivial)`. Take `⟨K, hK0, hsucc⟩ : ∃ K : ℕ → Subgroup G, K 0 = ⊤ ∧ ∀ n, K (n + 1) = K n ⊓ (L n : Subgroup G)` from `⟨fun n => Nat.rec (motive := fun _ => Subgroup G) ⊤ (fun n S => S ⊓ (L n : Subgroup G)) n, rfl, fun _ => rfl⟩`. Establish `hopen : ∀ n, IsOpen (K n : Set G)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[hK0]`. Conclude with `isOpen_univ`. Consider the case `succ n ih`.

Rewrite using `[hsucc, Subgroup.coe_inf]`. Conclude with `ih.inter (L n).isOpen`. Establish `hle : ∀ n, K (n + 1) ≤ L n` using `fun n => by`. Rewrite using `[hsucc]`. Conclude with `inf_le_right`.

Use `⟨K, hK0, fun n => by rw [hsucc]; exact inf_le_left, hopen, fun n => ?_, fun W hW => ?_⟩` and prove the remaining obligations. Establish `hclosed : IsClosed (K (n + 1) : Set G)` using `(⟨K (n + 1), hopen (n + 1)⟩ : OpenSubgroup G).isClosed`. Conclude with `(hLc n).of_isClosed_subset hclosed (hle n)`. Take `⟨n, -, hn⟩` from `hU.1.mem_iff.1 hW`. Conclude with `⟨n + 1, fun g hg => hn (hLU n (hle n hg))⟩`.
-/
theorem exists_subgroup_seq [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [FirstCountableTopology G] :
    ∃ K : ℕ → Subgroup G, K 0 = ⊤ ∧ (∀ n, K (n + 1) ≤ K n) ∧ (∀ n, IsOpen (K n : Set G)) ∧
      (∀ n, IsCompact (K (n + 1) : Set G)) ∧ ∀ W ∈ 𝓝 (1 : G), ∃ n, (K n : Set G) ⊆ W := by
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose L hLc hLU using fun n =>
    GroundTheory.Automorphic.exists_openSubgroup_isCompact_subset (hU.1.mem_of_mem (i := n) trivial)
  obtain ⟨K, hK0, hsucc⟩ : ∃ K : ℕ → Subgroup G, K 0 = ⊤ ∧
      ∀ n, K (n + 1) = K n ⊓ (L n : Subgroup G) :=
    ⟨fun n => Nat.rec (motive := fun _ => Subgroup G) ⊤
      (fun n S => S ⊓ (L n : Subgroup G)) n, rfl, fun _ => rfl⟩
  have hopen : ∀ n, IsOpen (K n : Set G) := by
    intro n
    induction n with
    | zero =>
      rw [hK0]
      exact isOpen_univ
    | succ n ih =>
      rw [hsucc, Subgroup.coe_inf]
      exact ih.inter (L n).isOpen
  have hle : ∀ n, K (n + 1) ≤ L n := fun n => by
    rw [hsucc]
    exact inf_le_right
  refine ⟨K, hK0, fun n => by rw [hsucc]; exact inf_le_left, hopen, fun n => ?_, fun W hW => ?_⟩
  · have hclosed : IsClosed (K (n + 1) : Set G) :=
      (⟨K (n + 1), hopen (n + 1)⟩ : OpenSubgroup G).isClosed
    exact (hLc n).of_isClosed_subset hclosed (hle n)
  · obtain ⟨n, -, hn⟩ := hU.1.mem_iff.1 hW
    exact ⟨n + 1, fun g hg => hn (hLU n (hle n hg))⟩

/- English proof (translation)
Use `haveI : IsClosed (H : Set G) := hH`. Take `⟨K, hK0, hKle, hKo, hKc, hKb⟩` from `exists_subgroup_seq (G := G)`. Set `P : ℕ → (G ⧸ H → G) → Prop` to `fun n t => IsLocallyConstant t ∧ ∀ x, x ∈ cosetImage H (K n) (t x)`. Establish `hstep : ∀ n (t : {t // P n t}), ∃ t' : {t // P (n + 1) t}, ∀ x, (t.1 x)⁻¹ * t'.1 x ∈ K n`. Introduce and unpack `n ⟨t, ht, hmem⟩`.

Take `⟨t', h1, h2, h3⟩` from `exists_refine H (K n) (K (n + 1)) (hKle n) (hKo _) (hKc n) t ht hmem`. Conclude with `⟨⟨t', h1, h2⟩, h3⟩`. Establish `h0 : P 0 (fun _ => 1)`. Use `⟨IsLocallyConstant.const _, fun x => ?_⟩` and prove the remaining obligations. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`.

Conclude with `⟨g, by simp [hK0], by simp⟩`. Use `choose nxt hnxt using hstep`. Set `T : (n : ℕ) → {t // P n t}` to `fun n => Nat.rec ⟨_, h0⟩ (fun n t => nxt n t) n`. Establish `hT : ∀ n x, ((T n).1 x)⁻¹ * (T (n + 1)).1 x ∈ K n` using `fun n x => hnxt n (T n) x`. Set `C : G ⧸ H → ℕ → Set G` to `fun x n => (fun k => (T (n + 1)).1 x * k) '' (K (n + 1) : Set G)`.

Establish `hCmem : ∀ x n g, g ∈ C x n ↔ ((T (n + 1)).1 x)⁻¹ * g ∈ K (n + 1)`. Introduce `x n g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Simplify using `using hk`.

Introduce `hg`. Conclude with `⟨_, hg, by simp⟩`. Establish `hCanti : ∀ x n, C x (n + 1) ⊆ C x n`. Introduce `x n g hg`. Rewrite `hg`, the goal using `[hCmem]`.

Establish `h1` using `hT (n + 1) x`. Establish `: ((T (n + 1)).1 x)⁻¹ * g = (((T (n + 1)).1 x)⁻¹ * (T (n + 1 + 1)).1 x) * (((T (n + 1 + 1)).1 x)⁻¹ * g)` using `by group`. Rewrite using `[this]`. Conclude with `(K (n + 1)).mul_mem h1 (hKle _ hg)`. Establish `hCne : ∀ x, (⋂ n, C x n).Nonempty` using `fun x => IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (C x) (hCanti x) (fun n => ⟨_, 1, (K (n + 1)).one_mem, rfl⟩) ((hKc 0).image (continuous_const.mul continuous_id)) (fun n => ((hKc n).image (continuous_const.mul continuous_id)).isClosed)`.

Use `choose s hs using hCne`. Establish `hsC : ∀ x n, ((T (n + 1)).1 x)⁻¹ * s x ∈ K (n + 1)` using `fun x n => (hCmem x n _).1 (mem_iInter.1 (hs x) n)`. Use `⟨s, ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`.

Rewrite using `[ContinuousAt, tendsto_def]`. Introduce `W hW`. Establish `hW1 : (fun k => s x * k) ⁻¹' W ∈ 𝓝 (1 : G)`. Use `(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Simplify using `using hW`.

Take `⟨m, hm⟩` from `hKb _ hW1`. Establish `hmm : (K (m + 1) : Set G) ⊆ (fun k => s x * k) ⁻¹' W` using `fun g hg => hm (hKle m hg)`. Establish `hloc : {y | (T (m + 1)).1 y = (T (m + 1)).1 x} ∈ 𝓝 x` using `((T (m + 1)).2.1.isOpen_fiber _).mem_nhds rfl`. Use `filter_upwards [hloc] with y hy`. Establish `h1` using `hsC y m`.

Establish `h2` using `hsC x m`. Rewrite `h1` using `[hy]`. Establish `: (s x)⁻¹ * s y = (((T (m + 1)).1 x)⁻¹ * s x)⁻¹ * (((T (m + 1)).1 x)⁻¹ * s y)` using `by group`. Establish `hk : (s x)⁻¹ * s y ∈ K (m + 1)`. Rewrite using `[this]`.

Conclude with `(K (m + 1)).mul_mem ((K (m + 1)).inv_mem h2) h1`. Simplify using `using hmm hk`. Assume the negation of the conclusion as `hne`. Establish `hopen : IsOpen {g : G | (g : G ⧸ H) ≠ c}` using `(isOpen_compl_singleton (x := c)).preimage continuous_quotient_mk'`. Establish `hW1 : (fun k => s c * k) ⁻¹' {g : G | (g : G ⧸ H) ≠ c} ∈ 𝓝 (1 : G)`.

Use `(continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_` and prove the remaining obligations. Simplify using `using hopen.mem_nhds hne`. Take `⟨m, hm⟩` from `hKb _ hW1`. Take `⟨k, hk, hkc⟩` from `(T (m + 1)).2.2 c`. Establish `hk' : (s c)⁻¹ * ((T (m + 1)).1 c * k) ∈ K (m + 1)`.

Establish `h2` using `hsC c m`. Establish `: (s c)⁻¹ * ((T (m + 1)).1 c * k) = (((T (m + 1)).1 c)⁻¹ * s c)⁻¹ * k` using `by group`. Rewrite using `[this]`. Conclude with `(K (m + 1)).mul_mem ((K (m + 1)).inv_mem h2) hk`. Use `hm (hKle m hk')` as an intermediate fact.

Simplify using `only [mem_preimage, mem_setOf_eq, mul_inv_cancel_left] at this`. Conclude with `this hkc`.
-/
theorem exists_continuous_section (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
    (H : Subgroup G) (hH : IsClosed (H : Set G)) :
    ∃ s : G ⧸ H → G, Continuous s ∧ ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c := by
  classical
  haveI : IsClosed (H : Set G) := hH
  obtain ⟨K, hK0, hKle, hKo, hKc, hKb⟩ := exists_subgroup_seq (G := G)

  let P : ℕ → (G ⧸ H → G) → Prop := fun n t =>
    IsLocallyConstant t ∧ ∀ x, x ∈ cosetImage H (K n) (t x)
  have hstep : ∀ n (t : {t // P n t}), ∃ t' : {t // P (n + 1) t},
      ∀ x, (t.1 x)⁻¹ * t'.1 x ∈ K n := by
    rintro n ⟨t, ht, hmem⟩
    obtain ⟨t', h1, h2, h3⟩ :=
      exists_refine H (K n) (K (n + 1)) (hKle n) (hKo _) (hKc n) t ht hmem
    exact ⟨⟨t', h1, h2⟩, h3⟩
  have h0 : P 0 (fun _ => 1) := by
    refine ⟨IsLocallyConstant.const _, fun x => ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    exact ⟨g, by simp [hK0], by simp⟩
  choose nxt hnxt using hstep
  let T : (n : ℕ) → {t // P n t} := fun n => Nat.rec ⟨_, h0⟩ (fun n t => nxt n t) n
  have hT : ∀ n x, ((T n).1 x)⁻¹ * (T (n + 1)).1 x ∈ K n := fun n x => hnxt n (T n) x

  let C : G ⧸ H → ℕ → Set G := fun x n => (fun k => (T (n + 1)).1 x * k) '' (K (n + 1) : Set G)
  have hCmem : ∀ x n g, g ∈ C x n ↔ ((T (n + 1)).1 x)⁻¹ * g ∈ K (n + 1) := by
    intro x n g
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa using hk
    · intro hg
      exact ⟨_, hg, by simp⟩
  have hCanti : ∀ x n, C x (n + 1) ⊆ C x n := by
    intro x n g hg
    rw [hCmem] at hg ⊢
    have h1 := hT (n + 1) x
    have : ((T (n + 1)).1 x)⁻¹ * g = (((T (n + 1)).1 x)⁻¹ * (T (n + 1 + 1)).1 x) *
        (((T (n + 1 + 1)).1 x)⁻¹ * g) := by group
    rw [this]
    exact (K (n + 1)).mul_mem h1 (hKle _ hg)
  have hCne : ∀ x, (⋂ n, C x n).Nonempty := fun x =>
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed (C x) (hCanti x)
      (fun n => ⟨_, 1, (K (n + 1)).one_mem, rfl⟩)
      ((hKc 0).image (continuous_const.mul continuous_id))
      (fun n => ((hKc n).image (continuous_const.mul continuous_id)).isClosed)
  choose s hs using hCne
  have hsC : ∀ x n, ((T (n + 1)).1 x)⁻¹ * s x ∈ K (n + 1) := fun x n =>
    (hCmem x n _).1 (mem_iInter.1 (hs x) n)
  refine ⟨s, ?_, fun c => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_def]
    intro W hW

    have hW1 : (fun k => s x * k) ⁻¹' W ∈ 𝓝 (1 : G) := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hW
    obtain ⟨m, hm⟩ := hKb _ hW1
    have hmm : (K (m + 1) : Set G) ⊆ (fun k => s x * k) ⁻¹' W :=
      fun g hg => hm (hKle m hg)
    have hloc : {y | (T (m + 1)).1 y = (T (m + 1)).1 x} ∈ 𝓝 x :=
      ((T (m + 1)).2.1.isOpen_fiber _).mem_nhds rfl
    filter_upwards [hloc] with y hy
    have h1 := hsC y m
    have h2 := hsC x m
    rw [hy] at h1
    have : (s x)⁻¹ * s y = (((T (m + 1)).1 x)⁻¹ * s x)⁻¹ * (((T (m + 1)).1 x)⁻¹ * s y) := by group
    have hk : (s x)⁻¹ * s y ∈ K (m + 1) := by
      rw [this]
      exact (K (m + 1)).mul_mem ((K (m + 1)).inv_mem h2) h1
    simpa using hmm hk
  · by_contra hne

    have hopen : IsOpen {g : G | (g : G ⧸ H) ≠ c} :=
      (isOpen_compl_singleton (x := c)).preimage continuous_quotient_mk'
    have hW1 : (fun k => s c * k) ⁻¹' {g : G | (g : G ⧸ H) ≠ c} ∈ 𝓝 (1 : G) := by
      refine (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds ?_
      simpa using hopen.mem_nhds hne
    obtain ⟨m, hm⟩ := hKb _ hW1
    obtain ⟨k, hk, hkc⟩ := (T (m + 1)).2.2 c
    have hk' : (s c)⁻¹ * ((T (m + 1)).1 c * k) ∈ K (m + 1) := by
      have h2 := hsC c m
      have : (s c)⁻¹ * ((T (m + 1)).1 c * k) = (((T (m + 1)).1 c)⁻¹ * s c)⁻¹ * k := by group
      rw [this]
      exact (K (m + 1)).mul_mem ((K (m + 1)).inv_mem h2) hk
    have := hm (hKle m hk')
    simp only [mem_preimage, mem_setOf_eq, mul_inv_cancel_left] at this
    exact this hkc

end GlobalTheory.CompanionTheory.LGroupSection
