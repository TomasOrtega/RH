import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd

open GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace PositivityTheory.HtPt.Gi

variable {R : Type} [CommRing R] {T T' : Type} [CommGroup T] [CommGroup T']

/- English proof (translation)
Proceed by induction on `k generalizing f with`. Consider the case `zero`. Establish `e : (fun t : T => f (t ^ 0)) = algebraMap R (T → R) (f 1)`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `B.algebraMap_mem _`. Consider the case `succ k ih`. Set `L : (T × T → R) →ₗ[R] (T → R)` to `{ toFun := fun g t => g (t ^ k, t) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hmem : ∀ g ∈ prodSpan B, L g ∈ B`.

Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, b, hb, rfl⟩` from `hx`. Conclude with `B.mul_mem (ih ha) hb`.

Consider the case `zero`. Rewrite using `[map_zero]`. Conclude with `B.zero_mem`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`.

Conclude with `B.add_mem hx hy`. Consider the case `smul r x _ hx`. Rewrite using `[map_smul]`. Conclude with `B.smul_mem hx r`. Establish `e : (fun t : T => f (t ^ (k + 1))) = L (fun z : T × T => f (z.1 * z.2))`.

Use function extensionality and compare the values at `t`. Simplify using `[L, pow_succ]`. Rewrite using `[e]`. Conclude with `hmem _ (hB.comul f hf)`.
-/
theorem pow_pull [Finite T] {B : Subalgebra R (T → R)} (hB : IsHopfOrder B) {f : T → R} (hf : f ∈ B) (k : ℕ) :
    (fun t => f (t ^ k)) ∈ B := by
  induction k generalizing f with
  | zero =>
    have e : (fun t : T => f (t ^ 0)) = algebraMap R (T → R) (f 1) := by
      funext t
      simp
    rw [e]
    exact B.algebraMap_mem _
  | succ k ih =>
    let L : (T × T → R) →ₗ[R] (T → R) :=
      { toFun := fun g t => g (t ^ k, t)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hmem : ∀ g ∈ prodSpan B, L g ∈ B := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        exact B.mul_mem (ih ha) hb
      | zero =>
        rw [map_zero]
        exact B.zero_mem
      | add x y _ _ hx hy =>
        rw [map_add]
        exact B.add_mem hx hy
      | smul r x _ hx =>
        rw [map_smul]
        exact B.smul_mem hx r
    have e : (fun t : T => f (t ^ (k + 1))) = L (fun z : T × T => f (z.1 * z.2)) := by
      funext t
      simp [L, pow_succ]
    rw [e]
    exact hmem _ (hB.comul f hf)

def IsLoc (H : Subgroup T) (B : Subalgebra R (T → R)) : Prop :=
  ∀ f : T → R, (∀ t, ∃ b ∈ B, ∀ h ∈ H, b h = f (t * h)) → f ∈ B

/- English proof (translation)
Introduce `f hf`. Rewrite using `[h]`. Express the relevant statement in the definitionally equal form `∀ t : T, (fun x : H => f (t * H.subtype x)) ∈ resOrder H.subtype B`. Introduce `t`. Take `⟨b, hb, hbf⟩` from `hf t`.

Use `Subalgebra.mem_map.2 ⟨b, hb, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.CompanionTheory.Ar.BT.pullFun, hbf x x.2]`.
-/
theorem isLoc_of_ind {H : Subgroup T} {B : Subalgebra R (T → R)}
    (h : B = indOrder H.subtype (resOrder H.subtype B)) : IsLoc H B := by
  intro f hf
  rw [h]
  change ∀ t : T, (fun x : H => f (t * H.subtype x)) ∈ resOrder H.subtype B
  intro t
  obtain ⟨b, hb, hbf⟩ := hf t
  refine Subalgebra.mem_map.2 ⟨b, hb, ?_⟩
  funext x
  simp [GlobalTheory.CompanionTheory.Ar.BT.pullFun, hbf x x.2]

open Classical in

def cosetInd (R : Type) [CommRing R] (H : Subgroup T) (c : T ⧸ H) : T → R :=
  fun t => if (t : T ⧸ H) = c then 1 else 0

/- English proof (translation)
Establish `e : ((t * h : T) : T ⧸ H) = (t : T ⧸ H)` using `QuotientGroup.mk_mul_of_mem t hh`. Unfold `cosetInd`. Rewrite using `[e]`.
-/
theorem cosetInd_mul (H : Subgroup T) (c : T ⧸ H) (t : T) {h : T} (hh : h ∈ H) :
    cosetInd R H c (t * h) = cosetInd R H c t := by
  have e : ((t * h : T) : T ⧸ H) = (t : T ⧸ H) := QuotientGroup.mk_mul_of_mem t hh
  unfold cosetInd
  rw [e]

/- English proof (translation)
Apply `hl` to reduce the goal to its premises. Introduce `t`. Use `⟨algebraMap R (T → R) (cosetInd R H c t), B.algebraMap_mem _, fun h hh => ?_⟩` and prove the remaining obligations. Simplify using `[cosetInd_mul H c t hh]`.
-/
theorem cosetInd_mem {H : Subgroup T} {B : Subalgebra R (T → R)} (hl : IsLoc H B) (c : T ⧸ H) :
    cosetInd R H c ∈ B := by
  apply hl
  intro t
  refine ⟨algebraMap R (T → R) (cosetInd R H c t), B.algebraMap_mem _, fun h hh => ?_⟩
  simp [cosetInd_mul H c t hh]

/- English proof (translation)
Simplify using `[cosetInd, Finset.sum_apply]`.
-/
theorem sum_cosetInd (H : Subgroup T) [Fintype (T ⧸ H)] (F : T ⧸ H → T → R) (t : T) :
    (∑ c, cosetInd R H c * F c) t = F t t := by
  simp [cosetInd, Finset.sum_apply]

variable [Finite T'] {H : Subgroup T} {H' : Subgroup T'} {B : Subalgebra R (T → R)} {B' : Subalgebra R (T' → R)}
  (ι : T →* T')

/- English proof (translation)
Set `L : (U × U → R) →ₗ[R] (U → R)` to `{ toFun := fun g x => g (u, x) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hmem : ∀ g ∈ prodSpan A, L g ∈ A`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨a, ha, b, hb, rfl⟩` from `hx`. Use `A.smul_mem hb (a u) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using `[L]`. Consider the case `zero`.

Rewrite using `[map_zero]`. Conclude with `A.zero_mem`. Consider the case `add x y _ _ hx hy`. Rewrite using `[map_add]`. Conclude with `A.add_mem hx hy`.

Consider the case `smul r x _ hx`. Rewrite using `[map_smul]`. Conclude with `A.smul_mem hx r`. Conclude with `hmem _ (hA.comul f hf)`.
-/
private theorem translate_mem_of_isHopfOrder' {U : Type} [CommGroup U] {A : Subalgebra R (U → R)} (hA : IsHopfOrder A)
    {f : U → R} (hf : f ∈ A) (u : U) : (fun x => f (u * x)) ∈ A := by
  let L : (U × U → R) →ₗ[R] (U → R) :=
    { toFun := fun g x => g (u, x)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hmem : ∀ g ∈ prodSpan A, L g ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      convert A.smul_mem hb (a u) using 1
      funext x
      simp [L]
    | zero =>
      rw [map_zero]
      exact A.zero_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      exact A.add_mem hx hy
    | smul r x _ hx =>
      rw [map_smul]
      exact A.smul_mem hx r
  exact hmem _ (hA.comul f hf)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hg haveI : Fintype (T' ⧸ H') := Fintype.ofFinite _`. Establish `hex : ∀ t : T, ∃ f ∈ B', ∀ h ∈ H, g (t * h) = f (ι h)` using `fun t => hb _ (translate_mem_of_isHopfOrder' hB hg t)`. Use `choose fr hfr hfrH using hex`. Set `rep : T' ⧸ H' → T` to `fun c => if hc : ∃ t : T, (ι t : T' ⧸ H') = c then hc.choose else 1`.

Establish `hrep : ∀ t0 : T, ((ι (rep (ι t0 : T' ⧸ H')) : T') : T' ⧸ H') = (ι t0 : T' ⧸ H')`. Introduce `t0`. Establish `hc : ∃ t : T, (ι t : T' ⧸ H') = (ι t0 : T' ⧸ H')` using `⟨t0, rfl⟩`. Simplify using `only [rep, dif_pos hc]`. Conclude with `hc.choose_spec`.

Set `F : T' ⧸ H' → T' → R` to `fun c s => fr (rep c) ((ι (rep c))⁻¹ * s)`. Use `⟨∑ c, cosetInd R H' c * F c, ?_, ?_⟩` and prove the remaining obligations. Use `Subalgebra.sum_mem _ (fun c _ => Subalgebra.mul_mem _ (cosetInd_mem hl' c) ?_)` and prove the remaining obligations. Conclude with `translate_mem_of_isHopfOrder' hB' (hfr (rep c)) _`. Introduce `t0`.

Rewrite using `[sum_cosetInd]`. Use `set r := rep (ι t0 : T' ⧸ H') with hr`. Establish `hmem' : (ι r)⁻¹ * ι t0 ∈ H'` using `QuotientGroup.eq.mp (hrep t0)`. Establish `hmem : r⁻¹ * t0 ∈ H` using `hH _ (by simpa [map_mul, map_inv] using hmem')`. Use `hfrH r _ hmem` as an intermediate fact.

Simplify using `only [mul_inv_cancel_left] at this`. Simplify using `only [F, ← hr]`. Rewrite using `[this, map_mul, map_inv]`. Introduce and unpack `⟨f, hf, hgf⟩`. Apply `hl` to reduce the goal to its premises.

Introduce `t`. Take `⟨g', hg', hg'H⟩` from `ha _ (translate_mem_of_isHopfOrder' hB' hf (ι t))`. Use `⟨g', hg', fun h hh => ?_⟩` and prove the remaining obligations. Rewrite using `[hg'H h hh, hgf, map_mul]`.
-/
theorem res_iff_abs (hB : IsHopfOrder B) (hB' : IsHopfOrder B') (hl : IsLoc H B) (hl' : IsLoc H' B')
    (hH : ∀ t, ι t ∈ H' → t ∈ H)
    (ha : ∀ f ∈ B', ∃ g ∈ B, ∀ h ∈ H, g h = f (ι h)) (hb : ∀ g ∈ B, ∃ f ∈ B', ∀ h ∈ H, g h = f (ι h))
    (g : T → R) : g ∈ B ↔ ∃ f ∈ B', ∀ t, g t = f (ι t) := by
  classical
  constructor
  · intro hg
    haveI : Fintype (T' ⧸ H') := Fintype.ofFinite _
    have hex : ∀ t : T, ∃ f ∈ B', ∀ h ∈ H, g (t * h) = f (ι h) :=
      fun t => hb _ (translate_mem_of_isHopfOrder' hB hg t)
    choose fr hfr hfrH using hex
    let rep : T' ⧸ H' → T := fun c =>
      if hc : ∃ t : T, (ι t : T' ⧸ H') = c then hc.choose else 1
    have hrep : ∀ t0 : T, ((ι (rep (ι t0 : T' ⧸ H')) : T') : T' ⧸ H') = (ι t0 : T' ⧸ H') := by
      intro t0
      have hc : ∃ t : T, (ι t : T' ⧸ H') = (ι t0 : T' ⧸ H') := ⟨t0, rfl⟩
      simp only [rep, dif_pos hc]
      exact hc.choose_spec
    let F : T' ⧸ H' → T' → R := fun c s => fr (rep c) ((ι (rep c))⁻¹ * s)
    refine ⟨∑ c, cosetInd R H' c * F c, ?_, ?_⟩
    · refine Subalgebra.sum_mem _ (fun c _ => Subalgebra.mul_mem _ (cosetInd_mem hl' c) ?_)
      exact translate_mem_of_isHopfOrder' hB' (hfr (rep c)) _
    · intro t0
      rw [sum_cosetInd]
      set r := rep (ι t0 : T' ⧸ H') with hr
      have hmem' : (ι r)⁻¹ * ι t0 ∈ H' := QuotientGroup.eq.mp (hrep t0)
      have hmem : r⁻¹ * t0 ∈ H := hH _ (by simpa [map_mul, map_inv] using hmem')
      have := hfrH r _ hmem
      simp only [mul_inv_cancel_left] at this
      simp only [F, ← hr]
      rw [this, map_mul, map_inv]
  · rintro ⟨f, hf, hgf⟩
    apply hl
    intro t
    obtain ⟨g', hg', hg'H⟩ := ha _ (translate_mem_of_isHopfOrder' hB' hf (ι t))
    refine ⟨g', hg', fun h hh => ?_⟩
    rw [hg'H h hh, hgf, map_mul]

abbrev torsJ (B' : Subalgebra R (T' → R)) (N : ℕ) : Ideal B' :=
  Ideal.span {g : B' | ∃ h ∈ B', ∀ t, g.1 t = h (t ^ N) - h 1}

/- English proof (translation)
Set `τ : B' →+* B'` to `{ toFun := fun g => ⟨fun x => g.1 (v * x), translate_mem_of_isHopfOrder' hB' g.2 v⟩ map_one' := rfl map_mul' := fun _ _ => rfl map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `hle : torsJ B' N ≤ Ideal.comap τ (torsJ B' N)`. Use `Ideal.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `g ⟨h, hh, hg⟩`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap]`.

Apply `Ideal.subset_span` to reduce the goal to its premises. Use `⟨h, hh, fun x => ?_⟩` and prove the remaining obligations. Use `show g.1 (v * x) = h (x ^ N) - h 1`. Rewrite using `[hg, mul_pow, hv, one_mul]`. Conclude with `hle hj`.
-/
private theorem translate_mem_torsJ_of_pow_eq_one {N : ℕ} (hB' : IsHopfOrder B') {v : T'} (hv : v ^ N = 1) (j : B')
    (hj : j ∈ torsJ B' N) :
    (⟨fun x => j.1 (v * x), translate_mem_of_isHopfOrder' hB' j.2 v⟩ : B') ∈ torsJ B' N := by
  let τ : B' →+* B' :=
    { toFun := fun g => ⟨fun x => g.1 (v * x), translate_mem_of_isHopfOrder' hB' g.2 v⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hle : torsJ B' N ≤ Ideal.comap τ (torsJ B' N) := by
    refine Ideal.span_le.2 ?_
    rintro g ⟨h, hh, hg⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    apply Ideal.subset_span
    refine ⟨h, hh, fun x => ?_⟩
    show g.1 (v * x) = h (x ^ N) - h 1
    rw [hg, mul_pow, hv, one_mul]
  exact hle hj

/- English proof (translation)
Use `haveI : Fintype (T' ⧸ H') := Fintype.ofFinite _`. Establish `hE : ∀ c : T' ⧸ H', cosetInd R H' c ∈ B'` using `fun c => cosetInd_mem hl' c`. Establish `hdecomp : f = ∑ c, (⟨cosetInd R H' c, hE c⟩ : B') * f`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`.

Establish `key` using `sum_cosetInd (R := R) H' (fun _ => f.1) x`. Simplify using `only [Finset.sum_apply, Pi.mul_apply] at key`. Simplify using `[Finset.sum_apply, key]`. Rewrite using `[hdecomp]`. Use `Ideal.sum_mem _ (fun c _ => ?_)` and prove the remaining obligations.

Take `⟨s, rfl⟩` from `QuotientGroup.mk_surjective c`. Distinguish the cases in `hs : s ^ N ∈ H'`. Take `⟨t, ht⟩` from `hdiv s hs`. Establish `hfu : (fun x => f.1 (ι t * x)) ∈ B'` using `translate_mem_of_isHopfOrder' hB' f.2 (ι t)`. Take `⟨j, hj, hjH⟩` from `hc _ hfu (fun t' => by show f.1 (ι t * ι t') = 0`.

Rewrite using `[← map_mul]`. Conclude with `hf _)`. Establish `hv : (ι t)⁻¹ ^ N = 1` using `by rw [inv_pow, hN, inv_one]`. Establish `hτ` using `translate_mem_torsJ_of_pow_eq_one hB' hv j hj`. Establish `heq : (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f = (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * ⟨fun x => j.1 ((ι t)⁻¹ * x), translate_mem_of_isHopfOrder' hB' j.2 (ι t)⁻¹⟩`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show cosetInd R H' (s : T' ⧸ H') x * f.1 x = cosetInd R H' (s : T' ⧸ H') x * j.1 ((ι t)⁻¹ * x)`. Distinguish the cases in `hx : (x : T' ⧸ H') = s`. Establish `hmem : (ι t)⁻¹ * x ∈ H'` using `QuotientGroup.eq.mp (ht.trans hx.symm)`.

Simplify using `only [hjH _ hmem, mul_inv_cancel_left]`. Simplify using `[cosetInd, hx]`. Rewrite using `[heq]`. Conclude with `Ideal.mul_mem_left _ _ hτ`. Set `h0 : T' → R` to `cosetInd R H' ((s : T' ⧸ H') ^ N)`.

Establish `hG : (fun x => h0 (x ^ N) - h0 1) ∈ B'`. Establish `h1` using `pow_pull hB' (hE ((s : T' ⧸ H') ^ N)) N`. Conclude with `Subalgebra.sub_mem _ h1 (B'.algebraMap_mem (h0 1))`. Set `G : B'` to `⟨fun x => h0 (x ^ N) - h0 1, hG⟩`. Establish `hGJ : G ∈ torsJ B' N` using `Ideal.subset_span ⟨h0, hE _, fun x => rfl⟩`.

Establish `heq : (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f = ((⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f) * G`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `x`. Use `show cosetInd R H' (s : T' ⧸ H') x * f.1 x = cosetInd R H' (s : T' ⧸ H') x * f.1 x * (h0 (x ^ N) - h0 1)`. Distinguish the cases in `hx : (x : T' ⧸ H') = s`.

Establish `e1 : h0 (x ^ N) = 1`. Simplify using `[h0, cosetInd, QuotientGroup.mk_pow, hx]`. Establish `e2 : h0 1 = 0`. Simplify using `only [h0, cosetInd]`. Rewrite using `[if_neg]`.

Introduce `h1`. Apply `hs` to reduce the goal to its premises. Rewrite `h1` using `[← QuotientGroup.mk_pow]`. Use `QuotientGroup.eq.mp h1` as an intermediate fact. Simplify using `using this`.

Rewrite using `[e1, e2, sub_zero, mul_one]`. Simplify using `[cosetInd, hx]`. Rewrite using `[heq]`. Conclude with `Ideal.mul_mem_left _ _ hGJ`.
-/
theorem ker_abs {N : ℕ} (hB' : IsHopfOrder B') (hl' : IsLoc H' B') (hN : ∀ t, ι t ^ N = 1)
    (hdiv : ∀ s : T', s ^ N ∈ H' → ∃ t, (ι t : T' ⧸ H') = s)
    (hc : ∀ f ∈ B', (∀ t, f (ι t) = 0) → ∃ j ∈ torsJ B' N, ∀ h ∈ H', j.1 h = f h)
    (f : B') (hf : ∀ t, f.1 (ι t) = 0) : f ∈ torsJ B' N := by
  classical
  haveI : Fintype (T' ⧸ H') := Fintype.ofFinite _
  have hE : ∀ c : T' ⧸ H', cosetInd R H' c ∈ B' := fun c => cosetInd_mem hl' c
  have hdecomp : f = ∑ c, (⟨cosetInd R H' c, hE c⟩ : B') * f := by
    apply Subtype.ext
    funext x
    have key := sum_cosetInd (R := R) H' (fun _ => f.1) x
    simp only [Finset.sum_apply, Pi.mul_apply] at key
    simp [Finset.sum_apply, key]
  rw [hdecomp]
  refine Ideal.sum_mem _ (fun c _ => ?_)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective c
  by_cases hs : s ^ N ∈ H'
  · obtain ⟨t, ht⟩ := hdiv s hs
    have hfu : (fun x => f.1 (ι t * x)) ∈ B' := translate_mem_of_isHopfOrder' hB' f.2 (ι t)
    obtain ⟨j, hj, hjH⟩ := hc _ hfu (fun t' => by
      show f.1 (ι t * ι t') = 0
      rw [← map_mul]
      exact hf _)
    have hv : (ι t)⁻¹ ^ N = 1 := by rw [inv_pow, hN, inv_one]
    have hτ := translate_mem_torsJ_of_pow_eq_one hB' hv j hj
    have heq : (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f =
        (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') *
          ⟨fun x => j.1 ((ι t)⁻¹ * x), translate_mem_of_isHopfOrder' hB' j.2 (ι t)⁻¹⟩ := by
      apply Subtype.ext
      funext x
      show cosetInd R H' (s : T' ⧸ H') x * f.1 x = cosetInd R H' (s : T' ⧸ H') x * j.1 ((ι t)⁻¹ * x)
      by_cases hx : (x : T' ⧸ H') = s
      · have hmem : (ι t)⁻¹ * x ∈ H' := QuotientGroup.eq.mp (ht.trans hx.symm)
        simp only [hjH _ hmem, mul_inv_cancel_left]
      · simp [cosetInd, hx]
    rw [heq]
    exact Ideal.mul_mem_left _ _ hτ
  · let h0 : T' → R := cosetInd R H' ((s : T' ⧸ H') ^ N)
    have hG : (fun x => h0 (x ^ N) - h0 1) ∈ B' := by
      have h1 := pow_pull hB' (hE ((s : T' ⧸ H') ^ N)) N
      exact Subalgebra.sub_mem _ h1 (B'.algebraMap_mem (h0 1))
    let G : B' := ⟨fun x => h0 (x ^ N) - h0 1, hG⟩
    have hGJ : G ∈ torsJ B' N := Ideal.subset_span ⟨h0, hE _, fun x => rfl⟩
    have heq : (⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f =
        ((⟨cosetInd R H' (s : T' ⧸ H'), hE _⟩ : B') * f) * G := by
      apply Subtype.ext
      funext x
      show cosetInd R H' (s : T' ⧸ H') x * f.1 x =
        cosetInd R H' (s : T' ⧸ H') x * f.1 x * (h0 (x ^ N) - h0 1)
      by_cases hx : (x : T' ⧸ H') = s
      · have e1 : h0 (x ^ N) = 1 := by
          simp [h0, cosetInd, QuotientGroup.mk_pow, hx]
        have e2 : h0 1 = 0 := by
          simp only [h0, cosetInd]
          rw [if_neg]
          intro h1
          apply hs
          rw [← QuotientGroup.mk_pow] at h1
          have := QuotientGroup.eq.mp h1
          simpa using this
        rw [e1, e2, sub_zero, mul_one]
      · simp [cosetInd, hx]
    rw [heq]
    exact Ideal.mul_mem_left _ _ hGJ

end PositivityTheory.HtPt.Gi
