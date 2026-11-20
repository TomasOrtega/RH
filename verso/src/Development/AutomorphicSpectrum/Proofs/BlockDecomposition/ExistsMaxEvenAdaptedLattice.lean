import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.Adapted

section Lemmas

variable {R : Type} [CommRing R] {c : R →+* R} {𝔬 : Subring R}
  {V : Type} [AddCommGroup V] [Module R V] {h : V → V → R}

/- English proof (translation)
Use `H.smul_right 0 x 0` as an intermediate fact. Simplify using `using this`.
-/
theorem herm_zero_right (H : IsHerm c h) (x : V) : h x 0 = 0 := by
  have := H.smul_right 0 x 0
  simpa using this

/- English proof (translation)
Rewrite using `[H.symm x 0, herm_zero_right H, map_zero]`.
-/
theorem herm_zero_left (H : IsHerm c h) (x : V) : h 0 x = 0 := by
  rw [H.symm x 0, herm_zero_right H, map_zero]

/- English proof (translation)
Rewrite using `[H.symm z (x + y), H.add_right, map_add, ← H.symm z x, ← H.symm z y]`.
-/
theorem herm_add_left (H : IsHerm c h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [H.symm z (x + y), H.add_right, map_add, ← H.symm z x, ← H.symm z y]

/- English proof (translation)
Rewrite using `[H.symm y (a • x), H.smul_right, map_mul, ← H.symm y x]`.
-/
theorem herm_smul_left (H : IsHerm c h) (a : R) (x y : V) : h (a • x) y = c a * h x y := by
  rw [H.symm y (a • x), H.smul_right, map_mul, ← H.symm y x]

def hl (H : IsHerm c h) (w : V) : V →ₗ[R] R where
  toFun := h w
  map_add' := H.add_right w
  map_smul' a y := by simpa using H.smul_right a w y

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem hl_apply (H : IsHerm c h) (w z : V) : hl H w z = h w z := rfl

/- English proof (translation)
The claim follows from `L.smul_mem ⟨a, ha⟩ hv`.
-/
theorem smul_mem_of {L : Submodule 𝔬 V} {a : R} (ha : a ∈ 𝔬) {v : V} (hv : v ∈ L) : a • v ∈ L :=
  L.smul_mem ⟨a, ha⟩ hv

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, 𝔬.one_mem, isUnit_one, by simp⟩`. Consider the case `insert i S _ ih`. Take `⟨s, hs, hu, hS⟩` from `ih`. Take `⟨t, ht, hv, hi⟩` from `den (a i)`.

Use `⟨s * t, 𝔬.mul_mem hs ht, hu.mul hv, fun j hj => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hj with rfl | hj` into its components or cases. Rewrite using `[mul_assoc]`. Conclude with `𝔬.mul_mem hs hi`. Rewrite using `[mul_right_comm]`.

Conclude with `𝔬.mul_mem (hS j hj) ht`.
-/
theorem common_denom (den : ∀ a : R, ∃ s ∈ 𝔬, IsUnit s ∧ s * a ∈ 𝔬) {ι : Type} (S : Finset ι) (a : ι → R) :
    ∃ s ∈ 𝔬, IsUnit s ∧ ∀ i ∈ S, s * a i ∈ 𝔬 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 𝔬.one_mem, isUnit_one, by simp⟩
  | insert i S _ ih =>
    obtain ⟨s, hs, hu, hS⟩ := ih
    obtain ⟨t, ht, hv, hi⟩ := den (a i)
    refine ⟨s * t, 𝔬.mul_mem hs ht, hu.mul hv, fun j hj => ?_⟩
    rcases Finset.mem_insert.1 hj with rfl | hj
    · rw [mul_assoc]; exact 𝔬.mul_mem hs hi
    · rw [mul_right_comm]; exact 𝔬.mul_mem (hS j hj) ht

/- English proof (translation)
Establish `s1 : ∀ g ∈ G, ∀ z ∈ Submodule.span 𝔬 G, h g z ∈ 𝔬`. Introduce `g hg z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact h1 g hg x hx`. Consider the case `zero => rw [herm_zero_right H]`.

Conclude with `𝔬.zero_mem`. Consider the case `add x y _ _ hx hy => rw [H.add_right]`. Conclude with `𝔬.add_mem hx hy`. Consider the case `smul a x _ hx`. Rewrite using `[Subring.smul_def, H.smul_right]`.

Conclude with `𝔬.mul_mem a.2 hx`. Establish `s2 : ∀ z ∈ Submodule.span 𝔬 G, ∀ z' ∈ Submodule.span 𝔬 G, h z z' ∈ 𝔬`. Introduce `z hz z' hz'`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact s1 x hx z' hz'`.

Consider the case `zero => rw [herm_zero_left H]`. Conclude with `𝔬.zero_mem`. Consider the case `add x y _ _ hx hy => rw [herm_add_left H]`. Conclude with `𝔬.add_mem hx hy`. Consider the case `smul a x _ hx`.

Rewrite using `[Subring.smul_def, herm_smul_left H]`. Conclude with `𝔬.mul_mem (cm _ a.2) hx`. Use `⟨s2, fun z hz => ?_⟩` and prove the remaining obligations. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact h2 x hx`.

Consider the case `zero => exact ⟨0, 𝔬.zero_mem, by simp [herm_zero_right H]⟩`. Consider the case `add x y hx' hy' hx hy`. Take `⟨a, ha, ea⟩` from `hx`. Take `⟨b, hb, eb⟩` from `hy`. Use `⟨a + b + h x y, 𝔬.add_mem (𝔬.add_mem ha hb) (s2 x hx' y hy'), ?_⟩` and prove the remaining obligations.

Rewrite using `[H.add_right, herm_add_left H, herm_add_left H, ea, eb, H.symm x y, map_add, map_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `smul a x _ hx`. Take `⟨b, hb, eb⟩` from `hx`. Use `⟨c a * a * b, 𝔬.mul_mem (𝔬.mul_mem (cm _ a.2) a.2) hb, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subring.smul_def, H.smul_right, herm_smul_left H, eb, map_mul, map_mul, inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem evenInt_span (H : IsHerm c h) (inv : ∀ a, c (c a) = a) (cm : ∀ a ∈ 𝔬, c a ∈ 𝔬) (G : Set V)
    (h1 : ∀ g ∈ G, ∀ g' ∈ G, h g g' ∈ 𝔬) (h2 : ∀ g ∈ G, ∃ a ∈ 𝔬, h g g = a + c a) :
    IsEvenInt c 𝔬 h (Submodule.span 𝔬 G) := by
  have s1 : ∀ g ∈ G, ∀ z ∈ Submodule.span 𝔬 G, h g z ∈ 𝔬 := by
    intro g hg z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact h1 g hg x hx
    | zero => rw [herm_zero_right H]; exact 𝔬.zero_mem
    | add x y _ _ hx hy => rw [H.add_right]; exact 𝔬.add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, H.smul_right]
      exact 𝔬.mul_mem a.2 hx
  have s2 : ∀ z ∈ Submodule.span 𝔬 G, ∀ z' ∈ Submodule.span 𝔬 G, h z z' ∈ 𝔬 := by
    intro z hz z' hz'
    induction hz using Submodule.span_induction with
    | mem x hx => exact s1 x hx z' hz'
    | zero => rw [herm_zero_left H]; exact 𝔬.zero_mem
    | add x y _ _ hx hy => rw [herm_add_left H]; exact 𝔬.add_mem hx hy
    | smul a x _ hx =>
      rw [Subring.smul_def, herm_smul_left H]
      exact 𝔬.mul_mem (cm _ a.2) hx
  refine ⟨s2, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem x hx => exact h2 x hx
  | zero => exact ⟨0, 𝔬.zero_mem, by simp [herm_zero_right H]⟩
  | add x y hx' hy' hx hy =>
    obtain ⟨a, ha, ea⟩ := hx
    obtain ⟨b, hb, eb⟩ := hy
    refine ⟨a + b + h x y, 𝔬.add_mem (𝔬.add_mem ha hb) (s2 x hx' y hy'), ?_⟩
    rw [H.add_right, herm_add_left H, herm_add_left H, ea, eb, H.symm x y, map_add, map_add]
    ring
  | smul a x _ hx =>
    obtain ⟨b, hb, eb⟩ := hx
    refine ⟨c a * a * b, 𝔬.mul_mem (𝔬.mul_mem (cm _ a.2) a.2) hb, ?_⟩
    rw [Subring.smul_def, H.smul_right, herm_smul_left H, eb, map_mul, map_mul, inv]
    ring

/- English proof (translation)
Use `haveI := Hr.noeth`. Take `⟨m, g, hg⟩` from `Submodule.fg_iff_exists_fin_generating_family.1 hL.1`. Establish `hgL : ∀ i, g i ∈ L₀` using `fun i => hg ▸ Submodule.subset_span ⟨i, rfl⟩`. Set `D : Submodule 𝔬 V` to `{ carrier := {z | ∀ i, h (g i) z ∈ 𝔬} add_mem' := fun {a b} ha hb i => by`. Rewrite using `[H.add_right]`.

Conclude with `𝔬.add_mem (ha i) (hb i)`. Use the proof step `zero_mem' := fun i => by rw [herm_zero_right H]; exact 𝔬.zero_mem`. Use the proof step `smul_mem' := fun a z hz i => by`. Rewrite using `[Subring.smul_def, H.smul_right]`. Conclude with `𝔬.mul_mem a.2 (hz i) }`.

Set `f : D →ₗ[𝔬] (Fin m → 𝔬)` to `{ toFun := fun z i => ⟨h (g i) z, z.2 i⟩ map_add' := fun a b => by`. Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `H.add_right _ _ _`. Use the proof step `map_smul' := fun a z => by`.

Use function extensionality and compare the values at `i`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `h (g i) ((a : R) • (z : V)) = (a : R) * h (g i) z`. Conclude with `H.smul_right _ _ _ }`. Establish `finj : Function.Injective f`.

Use `(injective_iff_map_eq_zero f).2 fun z hz => ?_` and prove the remaining obligations. Establish `h0 : ∀ i, h (g i) z = 0` using `fun i => congrArg Subtype.val (congrFun hz i)`. Establish `h1 : ∀ w ∈ L₀, h w z = 0`. Introduce `w hw`. Rewrite `hw` using `[← hg]`.

Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨i, rfl⟩ := hx`. Conclude with `h0 i`. Consider the case `zero => exact herm_zero_left H _`. Consider the case `add x y _ _ hx hy => rw [herm_add_left H, hx, hy, add_zero]`.

Consider the case `smul a x _ hx => rw [Subring.smul_def, herm_smul_left H, hx, mul_zero]`. Establish `h2 : ∀ w ∈ Submodule.span R (L₀ : Set V), h w z = 0`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact h1 x hx`.

Consider the case `zero => exact herm_zero_left H _`. Consider the case `add x y _ _ hx hy => rw [herm_add_left H, hx, hy, add_zero]`. Consider the case `smul a x _ hx => rw [herm_smul_left H, hx, mul_zero]`. Apply `Subtype.ext` to reduce the goal to its premises. Use `Hp.nondeg _ fun w => ?_` and prove the remaining obligations.

Rewrite using `[H.symm w, h2 w (by rw [hL.2]; trivial), map_zero]`. Use `haveI : IsNoetherian 𝔬 D := isNoetherian_of_injective f finj`. Establish `hD : ∀ L' : Submodule 𝔬 V, IsEvenInt c 𝔬 h L' → L₀ ≤ L' → L' ≤ D` using `fun L' hE' hle z hz i => hE'.1 _ (hle (hgL i)) _ hz`. Set `S : Set (Submodule 𝔬 D)` to `{N | IsEvenInt c 𝔬 h (N.map D.subtype) ∧ L₀ ≤ N.map D.subtype}`. Establish `hcm : ∀ L' : Submodule 𝔬 V, L' ≤ D → (L'.comap D.subtype).map D.subtype = L'` using `fun L' hl => by`.

Rewrite using `[Submodule.map_comap_subtype]`. Conclude with `inf_eq_right.2 hl`. Establish `hS : (L₀.comap D.subtype) ∈ S`. Use `hcm L₀ (hD L₀ hE le_rfl)` as an intermediate fact. Simplify using `only [S, Set.mem_setOf_eq, this]`.

Conclude with `⟨hE, le_rfl⟩`. Take `⟨N, hN, hmin⟩` from `(wellFounded_gt (α := Submodule 𝔬 D)).has_min S ⟨_, hS⟩`. Use `⟨N.map D.subtype, hN.2, ⟨?_, ?_⟩, hN.1, fun L' hE' hle => ?_⟩` and prove the remaining obligations. Conclude with `(IsNoetherian.noetherian N).map _`. Use `top_le_iff.1 ?_` and prove the remaining obligations.

Rewrite using `[← hL.2]`. Conclude with `Submodule.span_mono hN.2`. Establish `hDL : L' ≤ D` using `hD L' hE' (hN.2.trans hle)`. Establish `hmem : L'.comap D.subtype ∈ S`. Simplify using `only [S, Set.mem_setOf_eq, hcm L' hDL]`.

Conclude with `⟨hE', hN.2.trans hle⟩`. Establish `hNle : N ≤ L'.comap D.subtype`. Rewrite using `[← Submodule.map_le_iff_le_comap]`. Conclude with `hle`. Establish `: ¬ N < L'.comap D.subtype` using `hmin _ hmem`.

Establish `heq : N = L'.comap D.subtype`. Assume the negation of the conclusion as `hne`. Conclude with `this (lt_of_le_of_ne hNle hne)`. Rewrite using `[heq, hcm L' hDL]`.
-/
theorem exists_maxEven (Hr : IsHermRing c 𝔬) (H : IsHerm c h) (Hp : IsPerfect h) (L₀ : Submodule 𝔬 V)
    (hL : IsLat 𝔬 L₀) (hE : IsEvenInt c 𝔬 h L₀) : ∃ L, L₀ ≤ L ∧ IsMaxEven c 𝔬 h L := by
  haveI := Hr.noeth
  obtain ⟨m, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hL.1
  have hgL : ∀ i, g i ∈ L₀ := fun i => hg ▸ Submodule.subset_span ⟨i, rfl⟩
  let D : Submodule 𝔬 V :=
    { carrier := {z | ∀ i, h (g i) z ∈ 𝔬}
      add_mem' := fun {a b} ha hb i => by
        rw [H.add_right]; exact 𝔬.add_mem (ha i) (hb i)
      zero_mem' := fun i => by rw [herm_zero_right H]; exact 𝔬.zero_mem
      smul_mem' := fun a z hz i => by
        rw [Subring.smul_def, H.smul_right]; exact 𝔬.mul_mem a.2 (hz i) }
  let f : D →ₗ[𝔬] (Fin m → 𝔬) :=
    { toFun := fun z i => ⟨h (g i) z, z.2 i⟩
      map_add' := fun a b => by
        funext i; apply Subtype.ext; exact H.add_right _ _ _
      map_smul' := fun a z => by
        funext i; apply Subtype.ext
        change h (g i) ((a : R) • (z : V)) = (a : R) * h (g i) z
        exact H.smul_right _ _ _ }
  have finj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun z hz => ?_
    have h0 : ∀ i, h (g i) z = 0 := fun i => congrArg Subtype.val (congrFun hz i)
    have h1 : ∀ w ∈ L₀, h w z = 0 := by
      intro w hw
      rw [← hg] at hw
      induction hw using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h0 i
      | zero => exact herm_zero_left H _
      | add x y _ _ hx hy => rw [herm_add_left H, hx, hy, add_zero]
      | smul a x _ hx => rw [Subring.smul_def, herm_smul_left H, hx, mul_zero]
    have h2 : ∀ w ∈ Submodule.span R (L₀ : Set V), h w z = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem x hx => exact h1 x hx
      | zero => exact herm_zero_left H _
      | add x y _ _ hx hy => rw [herm_add_left H, hx, hy, add_zero]
      | smul a x _ hx => rw [herm_smul_left H, hx, mul_zero]
    apply Subtype.ext
    refine Hp.nondeg _ fun w => ?_
    rw [H.symm w, h2 w (by rw [hL.2]; trivial), map_zero]
  haveI : IsNoetherian 𝔬 D := isNoetherian_of_injective f finj
  have hD : ∀ L' : Submodule 𝔬 V, IsEvenInt c 𝔬 h L' → L₀ ≤ L' → L' ≤ D :=
    fun L' hE' hle z hz i => hE'.1 _ (hle (hgL i)) _ hz
  let S : Set (Submodule 𝔬 D) := {N | IsEvenInt c 𝔬 h (N.map D.subtype) ∧ L₀ ≤ N.map D.subtype}
  have hcm : ∀ L' : Submodule 𝔬 V, L' ≤ D → (L'.comap D.subtype).map D.subtype = L' := fun L' hl => by
    rw [Submodule.map_comap_subtype]; exact inf_eq_right.2 hl
  have hS : (L₀.comap D.subtype) ∈ S := by
    have := hcm L₀ (hD L₀ hE le_rfl)
    simp only [S, Set.mem_setOf_eq, this]
    exact ⟨hE, le_rfl⟩
  obtain ⟨N, hN, hmin⟩ := (wellFounded_gt (α := Submodule 𝔬 D)).has_min S ⟨_, hS⟩
  refine ⟨N.map D.subtype, hN.2, ⟨?_, ?_⟩, hN.1, fun L' hE' hle => ?_⟩
  · exact (IsNoetherian.noetherian N).map _
  · refine top_le_iff.1 ?_
    rw [← hL.2]
    exact Submodule.span_mono hN.2
  · have hDL : L' ≤ D := hD L' hE' (hN.2.trans hle)
    have hmem : L'.comap D.subtype ∈ S := by
      simp only [S, Set.mem_setOf_eq, hcm L' hDL]
      exact ⟨hE', hN.2.trans hle⟩
    have hNle : N ≤ L'.comap D.subtype := by
      rw [← Submodule.map_le_iff_le_comap]; exact hle
    have : ¬ N < L'.comap D.subtype := hmin _ hmem
    have heq : N = L'.comap D.subtype := by
      by_contra hne
      exact this (lt_of_le_of_ne hNle hne)
    rw [heq, hcm L' hDL]

/- English proof (translation)
Introduce `z`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Establish `ha : ∀ i, h (x i) z ∈ 𝔬` using `fun i => hE.1 _ (hx i) _ hz`. Establish `hb : ∀ i, h (y i) z ∈ 𝔬` using `fun i => hE.1 _ (hy i) _ hz`.

Use `⟨ha, hb, L.sub_mem (L.sub_mem hz ?_) ?_⟩` and prove the remaining obligations. Conclude with `L.sum_mem fun i _ => smul_mem_of (hb i) (hx i)`. Conclude with `L.sum_mem fun i _ => smul_mem_of (ha i) (hy i)`. Introduce and unpack `⟨ha, hb, hz⟩`. Establish `e : z = (z - ∑ i, h (y i) z • x i - ∑ i, h (x i) z • y i) + ∑ i, h (y i) z • x i + ∑ i, h (x i) z • y i` using `by abel`.

Rewrite using `[e]`. Use `L.add_mem (L.add_mem hz ?_) ?_` and prove the remaining obligations. Conclude with `L.sum_mem fun i _ => smul_mem_of (hb i) (hx i)`. Conclude with `L.sum_mem fun i _ => smul_mem_of (ha i) (hy i)`.
-/
theorem isAdapted_of {r : ℕ} {x y : Fin r → V} {L : Submodule 𝔬 V} (hE : IsEvenInt c 𝔬 h L)
    (hx : ∀ i, x i ∈ L) (hy : ∀ i, y i ∈ L) : IsAdapted 𝔬 h x y L := by
  intro z
  constructor
  · intro hz
    have ha : ∀ i, h (x i) z ∈ 𝔬 := fun i => hE.1 _ (hx i) _ hz
    have hb : ∀ i, h (y i) z ∈ 𝔬 := fun i => hE.1 _ (hy i) _ hz
    refine ⟨ha, hb, L.sub_mem (L.sub_mem hz ?_) ?_⟩
    · exact L.sum_mem fun i _ => smul_mem_of (hb i) (hx i)
    · exact L.sum_mem fun i _ => smul_mem_of (ha i) (hy i)
  · rintro ⟨ha, hb, hz⟩
    have e : z = (z - ∑ i, h (y i) z • x i - ∑ i, h (x i) z • y i) + ∑ i, h (y i) z • x i
        + ∑ i, h (x i) z • y i := by abel
    rw [e]
    refine L.add_mem (L.add_mem hz ?_) ?_
    · exact L.sum_mem fun i _ => smul_mem_of (hb i) (hx i)
    · exact L.sum_mem fun i _ => smul_mem_of (ha i) (hy i)

end Lemmas

/- English proof (translation)
Introduce `R _ c 𝔬 Hr V _ _ _ h H Hp r x y F`. Take `⟨m, e, he⟩` from `Module.Finite.exists_fin (R := R) (M := V)`. Establish `hyx : ∀ j i, h (y j) (x i) = if i = j then 1 else 0`. Introduce `j i`. Rewrite using `[H.symm (x i) (y j), F.xy]`.

Apply the tactic sequence `split_ifs <;> simp`. Set `u : Fin m → V` to `fun k => e k - ∑ i, h (y i) (e k) • x i - ∑ i, h (x i) (e k) • y i`. Establish `hux : ∀ j k, h (x j) (u k) = 0`. Introduce `j k`. Establish `: hl H (x j) (u k) = 0`.

Simplify using `only [u, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul, F.xx, F.xy]`. Simplify using the standard rewrite rules. Conclude with `this`. Establish `huy : ∀ j k, h (y j) (u k) = 0`. Introduce `j k`.

Establish `: hl H (y j) (u k) = 0`. Simplify using `only [u, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul, F.yy, hyx]`. Simplify using the standard rewrite rules. Conclude with `this`. Take `⟨t, ht⟩` from `Hr.two.exists_right_inv`.

Establish `hct : c t = t`. Establish `h2 : (2 : R) * c t = 1`. Use `congrArg c ht` as an intermediate fact. Rewrite `this` using `[map_mul, map_ofNat c 2, map_one]`. Conclude with `this`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨s, hs𝔬, hsu, hs⟩` from `common_denom Hr.denom (Finset.univ : Finset (Fin m × Fin m)) (fun p => h (u p.1) (u p.2) * t)`. Establish `two𝔬 : (2 : R) ∈ 𝔬`. Establish `: (2 : R) = 1 + 1` using `by norm_num`. Rewrite using `[this]`.

Conclude with `𝔬.add_mem 𝔬.one_mem 𝔬.one_mem`. Set `w : Fin m → V` to `fun k => s • u k`. Establish `hxw : ∀ i k, h (x i) (w k) = 0` using `fun i k => by`. Simplify using `only [w, H.smul_right, hux, mul_zero]`. Establish `hyw : ∀ i k, h (y i) (w k) = 0` using `fun i k => by`.

Simplify using `only [w, H.smul_right, huy, mul_zero]`. Establish `hwx : ∀ k i, h (w k) (x i) = 0` using `fun k i => by`. Rewrite using `[H.symm (x i) (w k), hxw, map_zero]`. Establish `hwy : ∀ k i, h (w k) (y i) = 0` using `fun k i => by`. Rewrite using `[H.symm (y i) (w k), hyw, map_zero]`.

Establish `hA : ∀ i j, c s * (s * (h (u i) (u j) * t)) ∈ 𝔬` using `fun i j => 𝔬.mul_mem (Hr.conj_mem _ hs𝔬) (hs (i, j) (Finset.mem_univ _))`. Establish `hww : ∀ i j, h (w i) (w j) = 2 * (c s * (s * (h (u i) (u j) * t)))` using `fun i j => by`. Simplify using `only [w, H.smul_right, herm_smul_left H]`. Take the linear combination `(-(c s * s * h (u i) (u j))) * ht`. Establish `ite𝔬 : ∀ i j : Fin r, (if i = j then (1 : R) else 0) ∈ 𝔬` using `fun i j => by split_ifs`.

Conclude with `𝔬.one_mem`. Conclude with `𝔬.zero_mem`. Set `G : Set V` to `Set.range x ∪ Set.range y ∪ Set.range w`. Establish `g1 : ∀ g ∈ G, ∀ g' ∈ G, h g g' ∈ 𝔬`. Introduce and unpack `g ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) g' ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)`.

Rewrite using `[F.xx]`. Conclude with `𝔬.zero_mem`. Rewrite using `[F.xy]`. Conclude with `ite𝔬 _ _`. Rewrite using `[hxw]`.

Conclude with `𝔬.zero_mem`. Rewrite using `[hyx]`. Conclude with `ite𝔬 _ _`. Rewrite using `[F.yy]`. Conclude with `𝔬.zero_mem`.

Rewrite using `[hyw]`. Conclude with `𝔬.zero_mem`. Rewrite using `[hwx]`. Conclude with `𝔬.zero_mem`. Rewrite using `[hwy]`.

Conclude with `𝔬.zero_mem`. Rewrite using `[hww]`. Conclude with `𝔬.mul_mem two𝔬 (hA i j)`. Establish `g2 : ∀ g ∈ G, ∃ a ∈ 𝔬, h g g = a + c a`. Introduce and unpack `g ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)`.

Conclude with `⟨0, 𝔬.zero_mem, by simp [F.xx]⟩`. Conclude with `⟨0, 𝔬.zero_mem, by simp [F.yy]⟩`. Use `⟨_, hA i i, ?_⟩` and prove the remaining obligations. Establish `hc : c (c s * (s * (h (u i) (u i) * t))) = c s * (s * (h (u i) (u i) * t))`. Simplify using `only [map_mul, Hr.invol, hct, ← H.symm]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hc, hww]`. Expand and normalize the polynomial expressions, which then agree. Establish `hE` using `evenInt_span (𝔬 := 𝔬) H Hr.invol Hr.conj_mem G g1 g2`. Establish `hfin : G.Finite` using `((Set.finite_range x).union (Set.finite_range y)).union (Set.finite_range w)`.

Establish `hLat : IsLat 𝔬 (Submodule.span 𝔬 G)`. Use `⟨Submodule.fg_span hfin, ?_⟩` and prove the remaining obligations. Use `set T := Submodule.span R ((Submodule.span 𝔬 G : Submodule 𝔬 V) : Set V) with hT`. Establish `hG : ∀ g ∈ G, g ∈ T` using `fun g hg => Submodule.subset_span (Submodule.subset_span hg)`. Establish `hu : ∀ k, u k ∈ T`.

Introduce `k`. Take `⟨v, rfl⟩` from `hsu`. Establish `: u k = (↑v⁻¹ : R) • w k`. Simplify using `only [w, smul_smul, Units.inv_mul, one_smul]`. Rewrite using `[this]`.

Conclude with `T.smul_mem _ (hG _ (Or.inr ⟨k, rfl⟩))`. Use `top_le_iff.1 ?_` and prove the remaining obligations. Rewrite using `[← he, Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Establish `ek : e k = u k + ∑ i, h (y i) (e k) • x i + ∑ i, h (x i) (e k) • y i`.

Simplify using `only [u]`. Normalize the expressions using the abelian group laws. Express the relevant statement in the definitionally equal form `e k ∈ T`. Rewrite using `[ek]`. Use `T.add_mem (T.add_mem (hu k) ?_) ?_` and prove the remaining obligations.

Conclude with `T.sum_mem fun i _ => T.smul_mem _ (hG _ (Or.inl (Or.inl ⟨i, rfl⟩)))`. Conclude with `T.sum_mem fun i _ => T.smul_mem _ (hG _ (Or.inl (Or.inr ⟨i, rfl⟩)))`. Take `⟨L, hle, hmax⟩` from `exists_maxEven Hr H Hp _ hLat hE`. Use `⟨L, hmax, isAdapted_of hmax.2.1 (fun i => hle ?_) (fun i => hle ?_)⟩` and prove the remaining obligations. Conclude with `Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩))`.

Conclude with `Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))`.
-/
theorem exists_maxEven_adapted : ∀ {R : Type} [CommRing R] (c : R →+* R) (𝔬 : Subring R), IsHermRing c 𝔬 →
    ∀ {V : Type} [AddCommGroup V] [Module R V] [Module.Finite R V] (h : V → V → R), IsHerm c h → IsPerfect h →
    ∀ {r : ℕ} (x y : Fin r → V), IsFrame h x y → ∃ L : Submodule 𝔬 V, IsMaxEven c 𝔬 h L ∧ IsAdapted 𝔬 h x y L := by
  intro R _ c 𝔬 Hr V _ _ _ h H Hp r x y F
  obtain ⟨m, e, he⟩ := Module.Finite.exists_fin (R := R) (M := V)
  have hyx : ∀ j i, h (y j) (x i) = if i = j then 1 else 0 := by
    intro j i
    rw [H.symm (x i) (y j), F.xy]
    split_ifs <;> simp
  let u : Fin m → V := fun k => e k - ∑ i, h (y i) (e k) • x i - ∑ i, h (x i) (e k) • y i
  have hux : ∀ j k, h (x j) (u k) = 0 := by
    intro j k
    have : hl H (x j) (u k) = 0 := by
      simp only [u, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul, F.xx, F.xy]
      simp
    exact this
  have huy : ∀ j k, h (y j) (u k) = 0 := by
    intro j k
    have : hl H (y j) (u k) = 0 := by
      simp only [u, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul, F.yy, hyx]
      simp
    exact this
  obtain ⟨t, ht⟩ := Hr.two.exists_right_inv
  have hct : c t = t := by
    have h2 : (2 : R) * c t = 1 := by
      have := congrArg c ht
      rw [map_mul, map_ofNat c 2, map_one] at this
      exact this
    calc c t = (2 * t) * c t := by rw [ht, one_mul]
      _ = t * (2 * c t) := by ring
      _ = t := by rw [h2, mul_one]
  obtain ⟨s, hs𝔬, hsu, hs⟩ := common_denom Hr.denom
    (Finset.univ : Finset (Fin m × Fin m)) (fun p => h (u p.1) (u p.2) * t)
  have two𝔬 : (2 : R) ∈ 𝔬 := by
    have : (2 : R) = 1 + 1 := by norm_num
    rw [this]; exact 𝔬.add_mem 𝔬.one_mem 𝔬.one_mem
  let w : Fin m → V := fun k => s • u k
  have hxw : ∀ i k, h (x i) (w k) = 0 := fun i k => by
    simp only [w, H.smul_right, hux, mul_zero]
  have hyw : ∀ i k, h (y i) (w k) = 0 := fun i k => by
    simp only [w, H.smul_right, huy, mul_zero]
  have hwx : ∀ k i, h (w k) (x i) = 0 := fun k i => by
    rw [H.symm (x i) (w k), hxw, map_zero]
  have hwy : ∀ k i, h (w k) (y i) = 0 := fun k i => by
    rw [H.symm (y i) (w k), hyw, map_zero]
  have hA : ∀ i j, c s * (s * (h (u i) (u j) * t)) ∈ 𝔬 := fun i j =>
    𝔬.mul_mem (Hr.conj_mem _ hs𝔬) (hs (i, j) (Finset.mem_univ _))
  have hww : ∀ i j, h (w i) (w j) = 2 * (c s * (s * (h (u i) (u j) * t))) := fun i j => by
    simp only [w, H.smul_right, herm_smul_left H]
    linear_combination (-(c s * s * h (u i) (u j))) * ht
  have ite𝔬 : ∀ i j : Fin r, (if i = j then (1 : R) else 0) ∈ 𝔬 := fun i j => by
    split_ifs
    · exact 𝔬.one_mem
    · exact 𝔬.zero_mem
  let G : Set V := Set.range x ∪ Set.range y ∪ Set.range w
  have g1 : ∀ g ∈ G, ∀ g' ∈ G, h g g' ∈ 𝔬 := by
    rintro g ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) g' ((⟨j, rfl⟩ | ⟨j, rfl⟩) | ⟨j, rfl⟩)
    · rw [F.xx]; exact 𝔬.zero_mem
    · rw [F.xy]; exact ite𝔬 _ _
    · rw [hxw]; exact 𝔬.zero_mem
    · rw [hyx]; exact ite𝔬 _ _
    · rw [F.yy]; exact 𝔬.zero_mem
    · rw [hyw]; exact 𝔬.zero_mem
    · rw [hwx]; exact 𝔬.zero_mem
    · rw [hwy]; exact 𝔬.zero_mem
    · rw [hww]; exact 𝔬.mul_mem two𝔬 (hA i j)
  have g2 : ∀ g ∈ G, ∃ a ∈ 𝔬, h g g = a + c a := by
    rintro g ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
    · exact ⟨0, 𝔬.zero_mem, by simp [F.xx]⟩
    · exact ⟨0, 𝔬.zero_mem, by simp [F.yy]⟩
    · refine ⟨_, hA i i, ?_⟩
      have hc : c (c s * (s * (h (u i) (u i) * t))) = c s * (s * (h (u i) (u i) * t)) := by
        simp only [map_mul, Hr.invol, hct, ← H.symm]
        ring
      rw [hc, hww]
      ring
  have hE := evenInt_span (𝔬 := 𝔬) H Hr.invol Hr.conj_mem G g1 g2
  have hfin : G.Finite := ((Set.finite_range x).union (Set.finite_range y)).union (Set.finite_range w)
  have hLat : IsLat 𝔬 (Submodule.span 𝔬 G) := by
    refine ⟨Submodule.fg_span hfin, ?_⟩
    set T := Submodule.span R ((Submodule.span 𝔬 G : Submodule 𝔬 V) : Set V) with hT
    have hG : ∀ g ∈ G, g ∈ T := fun g hg => Submodule.subset_span (Submodule.subset_span hg)
    have hu : ∀ k, u k ∈ T := by
      intro k
      obtain ⟨v, rfl⟩ := hsu
      have : u k = (↑v⁻¹ : R) • w k := by
        simp only [w, smul_smul, Units.inv_mul, one_smul]
      rw [this]
      exact T.smul_mem _ (hG _ (Or.inr ⟨k, rfl⟩))
    refine top_le_iff.1 ?_
    rw [← he, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have ek : e k = u k + ∑ i, h (y i) (e k) • x i + ∑ i, h (x i) (e k) • y i := by
      simp only [u]; abel
    change e k ∈ T
    rw [ek]
    refine T.add_mem (T.add_mem (hu k) ?_) ?_
    · exact T.sum_mem fun i _ => T.smul_mem _ (hG _ (Or.inl (Or.inl ⟨i, rfl⟩)))
    · exact T.sum_mem fun i _ => T.smul_mem _ (hG _ (Or.inl (Or.inr ⟨i, rfl⟩)))
  obtain ⟨L, hle, hmax⟩ := exists_maxEven Hr H Hp _ hLat hE
  refine ⟨L, hmax, isAdapted_of hmax.2.1 (fun i => hle ?_) (fun i => hle ?_)⟩
  · exact Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩))
  · exact Submodule.subset_span (Or.inl (Or.inr ⟨i, rfl⟩))

end GlobalTheory.CompanionTheory.KFin.Adapted

end
