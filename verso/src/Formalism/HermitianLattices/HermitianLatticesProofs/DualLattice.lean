import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic

open Module
noncomputable section
namespace Formalism.HermitianLatticesTheory

section
variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

omit [IsFractionRing R K] in
/- English proof (translation)
Use `haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL`. Use `haveI : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L`. Establish `htor : Submodule.torsion R L = ⊥`. Rewrite using `[Submodule.eq_bot_iff]`. Introduce `x hx`.

Take `⟨a, ha⟩` from `(Submodule.mem_torsion_iff x).mp hx`. Establish `ha' : (algebraMap R K (a : R)) • (x : V) = 0`. Rewrite using `[algebraMap_smul]`. Conclude with `congrArg Subtype.val ha`. Establish `hne : algebraMap R K (a : R) ≠ 0`.

Rewrite using `[Ne, ← map_zero (algebraMap R K)]`. Conclude with `fun h0 => nonZeroDivisors.ne_zero a.2 (hK h0)`. Conclude with `Subtype.ext ((smul_eq_zero.mp ha').resolve_left hne)`. Use `haveI : Module.Flat R L := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htor`. Use `haveI : Module.Projective R L := Module.Flat.projective_of_finitePresentation`.

Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' R L`. Take `⟨σ, hσ⟩` from `Module.projective_lifting_property π LinearMap.id hπ`. Use `⟨n, fun i => π (Pi.single i 1), fun i => (LinearMap.proj i) ∘ₗ σ, fun y => ?_⟩` and prove the remaining obligations. Establish `e1 : π (σ y) = y` using `LinearMap.congr_fun hσ y`. Establish `e2 : σ y = ∑ i, σ y i • (Pi.single i (1 : R) : Fin n → R)`.

Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `conv_lhs => rw [← e1, e2]`. Simplify using `[map_sum, map_smul]`.
-/
theorem finitely_generated_projective_coords (L : Submodule R V) (hL : L.FG) (hK : Function.Injective (algebraMap R K)) :
    ∃ (n : ℕ) (g : Fin n → L) (f : Fin n → (L →ₗ[R] R)), ∀ y : L, y = ∑ i, f i y • g i := by
  classical
  haveI : Module.Finite R L := Module.Finite.iff_fg.mpr hL
  haveI : Module.FinitePresentation R L := Module.finitePresentation_of_finite R L
  have htor : Submodule.torsion R L = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).mp hx
    have ha' : (algebraMap R K (a : R)) • (x : V) = 0 := by
      rw [algebraMap_smul]
      exact congrArg Subtype.val ha
    have hne : algebraMap R K (a : R) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap R K)]
      exact fun h0 => nonZeroDivisors.ne_zero a.2 (hK h0)
    exact Subtype.ext ((smul_eq_zero.mp ha').resolve_left hne)
  haveI : Module.Flat R L := IsDedekindDomain.flat_iff_torsion_eq_bot.mpr htor
  haveI : Module.Projective R L := Module.Flat.projective_of_finitePresentation
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R L
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨n, fun i => π (Pi.single i 1), fun i => (LinearMap.proj i) ∘ₗ σ, fun y => ?_⟩
  have e1 : π (σ y) = y := LinearMap.congr_fun hσ y
  have e2 : σ y = ∑ i, σ y i • (Pi.single i (1 : R) : Fin n → R) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [← e1, e2]
  simp [map_sum, map_smul]

/- English proof (translation)
Take `⟨s, hsL, hspan, hli⟩` from `exists_linearIndependent K (L : Set V)`. Establish `hfin : s.Finite` using `hli.setFinite`. Use `⟨s, hfin.fintype, Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp]), fun i => ?_, hsL⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem dualLattice_basis [FiniteDimensional K V] (L : Submodule R V)
    (hsp : Submodule.span K (L : Set V) = ⊤) :
    ∃ (s : Set V) (_ : Fintype s) (b : Basis s K V), (∀ i, b i = (i : V)) ∧ s ⊆ L := by
  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent K (L : Set V)
  have hfin : s.Finite := hli.setFinite
  refine ⟨s, hfin.fintype, Basis.mk hli (by rw [Subtype.range_coe, hspan, hsp]), fun i => ?_, hsL⟩
  simp

/- English proof (translation)
Take `⟨S, hS⟩` from `hL`. Take `⟨⟨d, hd⟩, hint⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R) (Finset.image (fun p : V × ι => b.repr p.1 p.2) (S ×ˢ Finset.univ))`. Use `⟨d, nonZeroDivisors.ne_zero hd, ?_⟩` and prove the remaining obligations. Establish `key : ∀ v ∈ S, d • v ∈ Submodule.span R (Set.range b)`. Introduce `v hv`.

Rewrite using `[← b.sum_repr v, Finset.smul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `hint (b.repr v i) (Finset.mem_image.mpr ⟨(v, i), by simp [hv], rfl⟩)`. Establish `hr' : algebraMap R K r = d • b.repr v i` using `hr`. Rewrite using `[← smul_assoc, ← hr', algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)`. Establish `hle : Submodule.span R (S : Set V) ≤ (Submodule.span R (Set.range b)).comap (d • LinearMap.id : V →ₗ[R] V)`. Rewrite using `[Submodule.span_le]`. Introduce `v hv`. Simplify using `using key v hv`.

Introduce `y hy`. Rewrite `hy` using `[← hS]`. Simplify using `using hle hy`.
-/
theorem dualLattice_denom {ι : Type*} [Fintype ι] (b : Basis ι K V) (L : Submodule R V)
    (hL : L.FG) : ∃ d : R, d ≠ 0 ∧ ∀ y ∈ L, d • y ∈ Submodule.span R (Set.range b) := by
  classical
  obtain ⟨S, hS⟩ := hL
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors R)
    (Finset.image (fun p : V × ι => b.repr p.1 p.2) (S ×ˢ Finset.univ))
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  have key : ∀ v ∈ S, d • v ∈ Submodule.span R (Set.range b) := by
    intro v hv
    rw [← b.sum_repr v, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨r, hr⟩ := hint (b.repr v i) (Finset.mem_image.mpr ⟨(v, i), by simp [hv], rfl⟩)
    have hr' : algebraMap R K r = d • b.repr v i := hr
    rw [← smul_assoc, ← hr', algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨i, rfl⟩)
  have hle : Submodule.span R (S : Set V) ≤
      (Submodule.span R (Set.range b)).comap (d • LinearMap.id : V →ₗ[R] V) := by
    rw [Submodule.span_le]
    intro v hv
    simpa using key v hv
  intro y hy
  rw [← hS] at hy
  simpa using hle hy

variable [StarRing K]

/- English proof (translation)
Use `haveI := Module.Finite.of_basis b`. Set `T : V →ₗ[K] (ι → K)` to `LinearMap.pi fun i => h (b i)`. Establish `hinj : Function.Injective T`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `x hx`.

Establish `h0 : ∀ i, h (b i) x = 0` using `fun i => congrFun hx i`. Establish `hflip : h.flip x = 0` using `b.ext fun i => by simp [h0 i]`. Conclude with `hnd.2 x fun y => by simpa using LinearMap.congr_fun hflip y`. Establish `hsurj` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [Module.finrank_eq_card_basis b])).mp hinj`. Use `choose bs hbs using fun j => hsurj (Pi.single j 1)`.

Use `⟨bs, fun i j => ?_⟩` and prove the remaining obligations. Use `congrFun (hbs j) i` as an intermediate fact. Simplify `this` using `[T, Pi.single_apply]`.
-/
theorem dualLattice_dualBasis {ι : Type*} [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hnd : h.Nondegenerate) (b : Basis ι K V) :
    ∃ bs : ι → V, ∀ i j, h (b i) (bs j) = if i = j then 1 else 0 := by
  classical
  haveI := Module.Finite.of_basis b
  let T : V →ₗ[K] (ι → K) := LinearMap.pi fun i => h (b i)
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 : ∀ i, h (b i) x = 0 := fun i => congrFun hx i
    have hflip : h.flip x = 0 := b.ext fun i => by simp [h0 i]
    exact hnd.2 x fun y => by simpa using LinearMap.congr_fun hflip y
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simp [Module.finrank_eq_card_basis b])).mp hinj
  choose bs hbs using fun j => hsurj (Pi.single j 1)
  refine ⟨bs, fun i j => ?_⟩
  have := congrFun (hbs j) i
  simpa [T, Pi.single_apply] using this

/- English proof (translation)
Use `set z := x - ∑ j, h (b j) x • bs j with hzdef`. Establish `hz : ∀ i, h (b i) z = 0`. Introduce `i`. Simplify using `[z, map_sub, map_sum, map_smul, hbs, smul_eq_mul]`. Establish `hflip : h.flip z = 0` using `b.ext fun i => by simp [hz i]`.

Establish `hz0 : z = 0` using `hnd.2 z fun y => by simpa using LinearMap.congr_fun hflip y`. Conclude with `sub_eq_zero.mp hz0`.
-/
theorem dualLattice_expand {ι : Type*} [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hnd : h.Nondegenerate) (b : Basis ι K V) (bs : ι → V)
    (hbs : ∀ i j, h (b i) (bs j) = if i = j then 1 else 0) (x : V) :
    x = ∑ j, h (b j) x • bs j := by
  classical
  set z := x - ∑ j, h (b j) x • bs j with hzdef
  have hz : ∀ i, h (b i) z = 0 := by
    intro i
    simp [z, map_sub, map_sum, map_smul, hbs, smul_eq_mul]
  have hflip : h.flip z = 0 := b.ext fun i => by simp [hz i]
  have hz0 : z = 0 := hnd.2 z fun y => by simpa using LinearMap.congr_fun hflip y
  exact sub_eq_zero.mp hz0

/- English proof (translation)
Set `w : V` to `∑ j, star (algebraMap R K (f ⟨b j, hb j⟩)) • bs j`. Establish `hsym : ∀ i j, h (bs j) (b i) = if i = j then 1 else 0`. Introduce `i j`. Rewrite using `[← hs.eq (b i) (bs j), hbs]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hwb : ∀ i, h w (b i) = algebraMap R K (f ⟨b i, hb i⟩)`. Introduce `i`. Simplify using `[w, map_sum, LinearMap.map_smulₛₗ₂, hsym, starRingEnd_apply, star_star, Algebra.smul_def]`. Establish `hspL : Submodule.span R (Set.range b) ≤ L` using `Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)`. Establish `hspan : ∀ z ∈ Submodule.span R (Set.range b), ∀ hz : z ∈ L, h w z = algebraMap R K (f ⟨z, hz⟩)`.

Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Introduce `_`.

Conclude with `hwb i`. Consider the case `zero`. Introduce `hz`. Establish `e : (⟨0, hz⟩ : L) = 0` using `rfl`. Rewrite using `[e, map_zero, map_zero, map_zero]`.

Consider the case `add x y hx hy ihx ihy`. Introduce `hxy`. Establish `e : (⟨x + y, hxy⟩ : L) = ⟨x, hspL hx⟩ + ⟨y, hspL hy⟩` using `rfl`. Rewrite using `[e, map_add, map_add, map_add, ihx (hspL hx), ihy (hspL hy)]`. Consider the case `smul r x hx ih`.

Introduce `hrx`. Establish `e1 : h w (r • x) = algebraMap R K r * h w x`. Rewrite using `[← algebraMap_smul K r x, LinearMap.map_smul, smul_eq_mul]`. Establish `e2 : (⟨r • x, hrx⟩ : L) = r • ⟨x, hspL hx⟩` using `rfl`. Rewrite using `[e1, e2, map_smul, smul_eq_mul, map_mul, ih (hspL hx)]`.

Use `⟨w, fun y hy => ?_⟩` and prove the remaining obligations. Establish `h1` using `hspan _ (hdL y hy) (L.smul_mem d hy)`. Establish `e1 : h w (d • y) = algebraMap R K d * h w y`. Rewrite using `[← algebraMap_smul K d y, LinearMap.map_smul, smul_eq_mul]`. Establish `e2 : (⟨d • y, L.smul_mem d hy⟩ : L) = d • ⟨y, hy⟩` using `rfl`.

Rewrite `h1` using `[e1, e2, map_smul, smul_eq_mul, map_mul]`. Establish `hne : algebraMap R K d ≠ 0`. Rewrite using `[Ne, ← map_zero (algebraMap R K)]`. Conclude with `fun h0 => hd (IsFractionRing.injective R K h0)`. Conclude with `mul_left_cancel₀ hne h1`.
-/
theorem dualLattice_repr {ι : Type*} [Fintype ι] [DecidableEq ι] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hs : h.IsSymm) (b : Basis ι K V) (bs : ι → V)
    (hbs : ∀ i j, h (b i) (bs j) = if i = j then 1 else 0) (L : Submodule R V)
    (hb : ∀ i, b i ∈ L) (d : R) (hd : d ≠ 0)
    (hdL : ∀ y ∈ L, d • y ∈ Submodule.span R (Set.range b)) (f : L →ₗ[R] R) :
    ∃ w : V, ∀ y (hy : y ∈ L), h w y = algebraMap R K (f ⟨y, hy⟩) := by
  classical
  let w : V := ∑ j, star (algebraMap R K (f ⟨b j, hb j⟩)) • bs j
  have hsym : ∀ i j, h (bs j) (b i) = if i = j then 1 else 0 := by
    intro i j
    rw [← hs.eq (b i) (bs j), hbs]
    split_ifs <;> simp
  have hwb : ∀ i, h w (b i) = algebraMap R K (f ⟨b i, hb i⟩) := by
    intro i
    simp [w, map_sum, LinearMap.map_smulₛₗ₂, hsym, starRingEnd_apply, star_star, Algebra.smul_def]
  have hspL : Submodule.span R (Set.range b) ≤ L :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hspan : ∀ z ∈ Submodule.span R (Set.range b), ∀ hz : z ∈ L,
      h w z = algebraMap R K (f ⟨z, hz⟩) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro _
      exact hwb i
    | zero =>
      intro hz
      have e : (⟨0, hz⟩ : L) = 0 := rfl
      rw [e, map_zero, map_zero, map_zero]
    | add x y hx hy ihx ihy =>
      intro hxy
      have e : (⟨x + y, hxy⟩ : L) = ⟨x, hspL hx⟩ + ⟨y, hspL hy⟩ := rfl
      rw [e, map_add, map_add, map_add, ihx (hspL hx), ihy (hspL hy)]
    | smul r x hx ih =>
      intro hrx
      have e1 : h w (r • x) = algebraMap R K r * h w x := by
        rw [← algebraMap_smul K r x, LinearMap.map_smul, smul_eq_mul]
      have e2 : (⟨r • x, hrx⟩ : L) = r • ⟨x, hspL hx⟩ := rfl
      rw [e1, e2, map_smul, smul_eq_mul, map_mul, ih (hspL hx)]
  refine ⟨w, fun y hy => ?_⟩
  have h1 := hspan _ (hdL y hy) (L.smul_mem d hy)
  have e1 : h w (d • y) = algebraMap R K d * h w y := by
    rw [← algebraMap_smul K d y, LinearMap.map_smul, smul_eq_mul]
  have e2 : (⟨d • y, L.smul_mem d hy⟩ : L) = d • ⟨y, hy⟩ := rfl
  rw [e1, e2, map_smul, smul_eq_mul, map_mul] at h1
  have hne : algebraMap R K d ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K)]
    exact fun h0 => hd (IsFractionRing.injective R K h0)
  exact mul_left_cancel₀ hne h1

end

/- English proof (translation)
Introduce `R K V _ _ _ _ _ _ _ _ _ _ _ h hs hnd hst L hL`. Establish `mem_dual : ∀ (M : Submodule R V) (x : V), x ∈ dual h M ↔ ∀ y ∈ M, ∃ r : R, algebraMap R K r = h y x`. Introduce `M x`. Simplify using `only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]`. Establish `hLfg` using `hL.fg`.

Establish `hLsp` using `hL.span_eq_top`. Take `⟨s, hfs, b, hbi, hsL⟩` from `dualLattice_basis (R := R) L hLsp`. Establish `hbL : ∀ i, b i ∈ L` using `fun i => hsL (by rw [hbi]; exact i.2)`. Take `⟨bs, hbs⟩` from `dualLattice_dualBasis h hnd b`. Take `⟨d, hd0, hdL⟩` from `dualLattice_denom b L hLfg`.

Establish `hexp` using `dualLattice_expand h hnd b bs hbs`. Establish `hdK : algebraMap R K d ≠ 0`. Rewrite using `[Ne, ← map_zero (algebraMap R K)]`. Conclude with `fun h0 => hd0 (IsFractionRing.injective R K h0)`. Establish `hA : ∀ z ∈ Submodule.span R (Set.range b), ∀ j, ∃ r : R, algebraMap R K r = h z (bs j)`.

Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨i, rfl⟩` from `hx`. Introduce `j`.

Use `⟨if i = j then 1 else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[hbs]`. Apply the tactic sequence `split_ifs <;> simp`. Consider the case `zero => intro j; exact ⟨0, by simp⟩`. Consider the case `add x y _ _ ihx ihy`.

Introduce `j`. Take `⟨r1, hr1⟩` from `ihx j`. Take `⟨r2, hr2⟩` from `ihy j`. Conclude with `⟨r1 + r2, by rw [map_add, hr1, hr2, map_add, LinearMap.add_apply]⟩`. Consider the case `smul r x _ ih`.

Introduce `j`. Take `⟨r1, hr1⟩` from `ih j`. Take `⟨r', hr'⟩` from `hst r`. Use `⟨r' * r1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hr', hr1, ← algebraMap_smul K r x, LinearMap.map_smulₛₗ₂]`.

Simplify using `only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]`. Establish `hle : dual h L ≤ Submodule.span R (Set.range bs)`. Introduce `x hx`. Rewrite using `[hexp x]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Take `⟨r, hr⟩` from `(mem_dual L x).mp hx (b j) (hbL j)`. Rewrite using `[← hr, algebraMap_smul]`. Conclude with `Submodule.smul_mem _ r (Submodule.subset_span ⟨j, rfl⟩)`. Establish `hfg : (dual h L).FG` using `Submodule.FG.of_le (Submodule.fg_span (Set.finite_range bs)) hle`. Establish `hbsK : ∀ j, bs j ∈ Submodule.span K (dual h L : Set V)`.

Introduce `j`. Take `⟨d', hd'⟩` from `hst d`. Establish `hd'0 : algebraMap R K d' ≠ 0` using `by rw [hd']; exact star_ne_zero.mpr hdK`. Establish `hmem : d' • bs j ∈ dual h L`. Rewrite using `[mem_dual]`.

Introduce `y hy`. Take `⟨r, hr⟩` from `hA _ (hdL y hy) j`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `e1 : h y (d' • bs j) = algebraMap R K d' * h y (bs j)`. Rewrite using `[← algebraMap_smul K d' (bs j), LinearMap.map_smul, smul_eq_mul]`.

Establish `e2 : h (d • y) (bs j) = star (algebraMap R K d) * h y (bs j)`. Rewrite using `[← algebraMap_smul K d y, LinearMap.map_smulₛₗ₂]`. Simplify using `only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]`. Rewrite using `[hr, e1, e2, hd']`. Establish `e : bs j = (algebraMap R K d')⁻¹ • (d' • bs j)`.

Rewrite using `[← algebraMap_smul K d' (bs j), smul_smul, inv_mul_cancel₀ hd'0, one_smul]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span hmem)`. Establish `hspd : Submodule.span K (dual h L : Set V) = ⊤`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Rewrite using `[hexp x]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbsK j)`. Use `⟨⟨hfg, hspd⟩, ?_, ?_⟩` and prove the remaining obligations. Use `le_antisymm ?_ ((dualBasic R K V h hs hst).2.1 L)` and prove the remaining obligations.

Take `⟨n, g, f, hgf⟩` from `finitely_generated_projective_coords L hLfg (IsFractionRing.injective R K)`. Use `choose w hw using fun k => dualLattice_repr h hs b bs hbs L hbL d hd0 hdL (f k)`. Establish `hwd : ∀ k, w k ∈ dual h L`. Introduce `k`. Rewrite using `[mem_dual]`.

Introduce `y hy`. Take `⟨r', hr'⟩` from `hst (f k ⟨y, hy⟩)`. Use `⟨r', ?_⟩` and prove the remaining obligations. Rewrite using `[hr', ← hs.eq (w k) y, hw k y hy, starRingEnd_apply]`. Set `Pm : V →ₗ[K] V` to `∑ k, (h (w k)).smulRight (g k : V)`.

Establish `hP : Pm = LinearMap.id`. Use `LinearMap.ext_on hLsp ?_` and prove the remaining obligations. Introduce `y hy`. Establish `e` using `congrArg Subtype.val (hgf ⟨y, hy⟩)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul] at e`.

Simplify using `only [Pm, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply, hw _ y hy, algebraMap_smul]`. Conclude with `e.symm`. Introduce `x hx`. Establish `ex : x = ∑ k, h (w k) x • (g k : V)`. Use `LinearMap.congr_fun hP x` as an intermediate fact.

Simplify `this.symm` using `[Pm]`. Rewrite using `[ex]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Take `⟨r, hr⟩` from `(mem_dual _ x).mp hx (w k) (hwd k)`. Rewrite using `[← hr, algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ r (g k).2`. Introduce `a ha`. Establish `hsa : star a ≠ 0` using `star_ne_zero.mpr ha`. Use extensionality with `x`. Simplify using `only [Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨star a • x, ?_, by rw [smul_smul, inv_mul_cancel₀ hsa, one_smul]⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[mem_dual]`. Introduce `z hz`.

Take `⟨r, hr⟩` from `hx (a • z) ⟨z, hz, rfl⟩`. Use `⟨r, ?_⟩` and prove the remaining obligations. Rewrite using `[hr, LinearMap.map_smulₛₗ₂, LinearMap.map_smul]`. Simplify using `only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]`. Introduce and unpack `⟨y, hy, rfl⟩`.

Rewrite `hy`, the goal using `[mem_dual]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`. Take `⟨r, hr⟩` from `hy z hz`. Use `⟨r, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]`.

Rewrite using `[hr, LinearMap.map_smulₛₗ₂, LinearMap.map_smul]`. Simplify using `only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hsa, one_mul]`.
-/
theorem dualLattice : DualLattice := by
  intro R K V _ _ _ _ _ _ _ _ _ _ _ h hs hnd hst L hL
  classical
  have mem_dual : ∀ (M : Submodule R V) (x : V),
      x ∈ dual h M ↔ ∀ y ∈ M, ∃ r : R, algebraMap R K r = h y x := by
    intro M x
    simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]
  have hLfg := hL.fg
  have hLsp := hL.span_eq_top
  obtain ⟨s, hfs, b, hbi, hsL⟩ := dualLattice_basis (R := R) L hLsp
  have hbL : ∀ i, b i ∈ L := fun i => hsL (by rw [hbi]; exact i.2)
  obtain ⟨bs, hbs⟩ := dualLattice_dualBasis h hnd b
  obtain ⟨d, hd0, hdL⟩ := dualLattice_denom b L hLfg
  have hexp := dualLattice_expand h hnd b bs hbs
  have hdK : algebraMap R K d ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap R K)]
    exact fun h0 => hd0 (IsFractionRing.injective R K h0)

  have hA : ∀ z ∈ Submodule.span R (Set.range b), ∀ j, ∃ r : R, algebraMap R K r = h z (bs j) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro j
      refine ⟨if i = j then 1 else 0, ?_⟩
      rw [hbs]
      split_ifs <;> simp
    | zero => intro j; exact ⟨0, by simp⟩
    | add x y _ _ ihx ihy =>
      intro j
      obtain ⟨r1, hr1⟩ := ihx j
      obtain ⟨r2, hr2⟩ := ihy j
      exact ⟨r1 + r2, by rw [map_add, hr1, hr2, map_add, LinearMap.add_apply]⟩
    | smul r x _ ih =>
      intro j
      obtain ⟨r1, hr1⟩ := ih j
      obtain ⟨r', hr'⟩ := hst r
      refine ⟨r' * r1, ?_⟩
      rw [map_mul, hr', hr1, ← algebraMap_smul K r x, LinearMap.map_smulₛₗ₂]
      simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]

  have hle : dual h L ≤ Submodule.span R (Set.range bs) := by
    intro x hx
    rw [hexp x]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨r, hr⟩ := (mem_dual L x).mp hx (b j) (hbL j)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨j, rfl⟩)
  have hfg : (dual h L).FG :=
    Submodule.FG.of_le (Submodule.fg_span (Set.finite_range bs)) hle

  have hbsK : ∀ j, bs j ∈ Submodule.span K (dual h L : Set V) := by
    intro j
    obtain ⟨d', hd'⟩ := hst d
    have hd'0 : algebraMap R K d' ≠ 0 := by rw [hd']; exact star_ne_zero.mpr hdK
    have hmem : d' • bs j ∈ dual h L := by
      rw [mem_dual]
      intro y hy
      obtain ⟨r, hr⟩ := hA _ (hdL y hy) j
      refine ⟨r, ?_⟩
      have e1 : h y (d' • bs j) = algebraMap R K d' * h y (bs j) := by
        rw [← algebraMap_smul K d' (bs j), LinearMap.map_smul, smul_eq_mul]
      have e2 : h (d • y) (bs j) = star (algebraMap R K d) * h y (bs j) := by
        rw [← algebraMap_smul K d y, LinearMap.map_smulₛₗ₂]
        simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
      rw [hr, e1, e2, hd']
    have e : bs j = (algebraMap R K d')⁻¹ • (d' • bs j) := by
      rw [← algebraMap_smul K d' (bs j), smul_smul, inv_mul_cancel₀ hd'0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  have hspd : Submodule.span K (dual h L : Set V) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [hexp x]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hbsK j)
  refine ⟨⟨hfg, hspd⟩, ?_, ?_⟩
  ·
    refine le_antisymm ?_ ((dualBasic R K V h hs hst).2.1 L)
    obtain ⟨n, g, f, hgf⟩ := finitely_generated_projective_coords L hLfg (IsFractionRing.injective R K)
    choose w hw using fun k => dualLattice_repr h hs b bs hbs L hbL d hd0 hdL (f k)
    have hwd : ∀ k, w k ∈ dual h L := by
      intro k
      rw [mem_dual]
      intro y hy
      obtain ⟨r', hr'⟩ := hst (f k ⟨y, hy⟩)
      refine ⟨r', ?_⟩
      rw [hr', ← hs.eq (w k) y, hw k y hy, starRingEnd_apply]
    let Pm : V →ₗ[K] V := ∑ k, (h (w k)).smulRight (g k : V)
    have hP : Pm = LinearMap.id := by
      refine LinearMap.ext_on hLsp ?_
      intro y hy
      have e := congrArg Subtype.val (hgf ⟨y, hy⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      simp only [Pm, LinearMap.sum_apply, LinearMap.smulRight_apply,
        LinearMap.id_apply, hw _ y hy, algebraMap_smul]
      exact e.symm
    intro x hx
    have ex : x = ∑ k, h (w k) x • (g k : V) := by
      have := LinearMap.congr_fun hP x
      simpa [Pm] using this.symm
    rw [ex]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨r, hr⟩ := (mem_dual _ x).mp hx (w k) (hwd k)
    rw [← hr, algebraMap_smul]
    exact Submodule.smul_mem _ r (g k).2
  ·
    intro a ha
    have hsa : star a ≠ 0 := star_ne_zero.mpr ha
    ext x
    simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
    constructor
    · intro hx
      refine ⟨star a • x, ?_, by rw [smul_smul, inv_mul_cancel₀ hsa, one_smul]⟩
      rw [mem_dual] at hx ⊢
      intro z hz
      obtain ⟨r, hr⟩ := hx (a • z) ⟨z, hz, rfl⟩
      refine ⟨r, ?_⟩
      rw [hr, LinearMap.map_smulₛₗ₂, LinearMap.map_smul]
      simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
    · rintro ⟨y, hy, rfl⟩
      rw [mem_dual] at hy ⊢
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨r, hr⟩ := hy z hz
      refine ⟨r, ?_⟩
      simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply]
      rw [hr, LinearMap.map_smulₛₗ₂, LinearMap.map_smul]
      simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hsa, one_mul]

end Formalism.HermitianLatticesTheory
