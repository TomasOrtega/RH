import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm

noncomputable section

namespace GlobalTheory.Mem.IdxFin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

/- English proof (translation)
Take `⟨S, rfl⟩` from `hA`. Use `choose! f hf using h`. Use `⟨∏ y ∈ S, f y, Finset.prod_ne_zero_iff.2 fun y hy => (hf y (Submodule.subset_span hy)).1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: Submodule.span R (S : Set V) ≤ B.comap ((∏ y ∈ S, f y) • LinearMap.id)`. Rewrite using `[Submodule.span_le]`.

Introduce `y hy`. Use `show (∏ y ∈ S, f y) • y ∈ B`. Rewrite using `[← Finset.prod_erase_mul S f hy, mul_smul]`. Conclude with `B.smul_mem _ (hf y (Submodule.subset_span hy)).2`. Conclude with `this hx`.
-/
theorem exists_unif {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V] (A B : Submodule R V)
    (hA : A.FG) (h : ∀ x ∈ A, ∃ s : R, s ≠ 0 ∧ s • x ∈ B) : ∃ s : R, s ≠ 0 ∧ ∀ x ∈ A, s • x ∈ B := by
  classical
  obtain ⟨S, rfl⟩ := hA
  choose! f hf using h
  refine ⟨∏ y ∈ S, f y, Finset.prod_ne_zero_iff.2 fun y hy => (hf y (Submodule.subset_span hy)).1, fun x hx => ?_⟩
  have : Submodule.span R (S : Set V) ≤ B.comap ((∏ y ∈ S, f y) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro y hy
    show (∏ y ∈ S, f y) • y ∈ B
    rw [← Finset.prod_erase_mul S f hy, mul_smul]
    exact B.smul_mem _ (hf y (Submodule.subset_span hy)).2
  exact this hx

/- English proof (translation)
Distinguish the cases in `h : ∀ x ∈ A, ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ C`. Take `⟨s, hs, hC⟩` from `exists_unif A C hA h`. Establish `hf` using `Ideal.finite_factors (I := Ideal.span {s}) (by simpa using hs)`. Use `hf.subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`.

Establish `hsw : s ∉ w.asIdeal` using `fun h => hn (Ideal.dvd_span_singleton.2 h)`. Establish `: (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨x, t, ht, hx⟩ -`. Conclude with `⟨s * t, Submonoid.mul_mem _ hsw ht, by rw [mul_smul]; exact hC _ hx⟩`.

Apply `hw` to reduce the goal to its premises. Unfold `Formalism.HermitianLatticesTheory.locLen`. Rewrite using `[this]`. Simplify using `[Module.length_eq_zero]`. Use `push Not at h`.

Take `⟨x, hx, hxC⟩` from `h`. Use `Set.Finite.subset Set.finite_empty fun w hw => hw ?_` and prove the remaining obligations. Unfold `Formalism.HermitianLatticesTheory.locLen`. Establish `hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A` using `⟨1, Submonoid.one_mem _, by simpa using hx⟩`. Set `φ : 𝓞 K →ₗ[𝓞 K] ((Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A) ⧸ (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype)` to `LinearMap.toSpanSingleton _ _ (Submodule.Quotient.mk ⟨x, hxA⟩)`.

Establish `hφ : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr`. Assume the negation of the conclusion as `hr0`. Establish `h1 : Submodule.Quotient.mk (p` using `(Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype) (r • (⟨x, hxA⟩ : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A)) = 0 := hr`.

Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero]`. Take `⟨t, ht, h2⟩` from `h1`. Use `hxC (t * r) (mul_ne_zero (fun h0 => ht (h0 ▸ w.asIdeal.zero_mem)) hr0) ?_` and prove the remaining obligations. Rewrite using `[mul_smul]`. Conclude with `h2`.

Establish `hle` using `Module.length_le_of_injective φ hφ`. Establish `htop : Module.length (𝓞 K) (𝓞 K) = ⊤`. Assume the negation of the conclusion as `hne`. Establish `hfl` using `Module.length_ne_top_iff.1 hne`. Establish `hart : IsArtinianRing (𝓞 K)` using `(isFiniteLength_iff_isNoetherian_isArtinian.1 hfl).2`.

Conclude with `RingOfIntegers.not_isField K (IsArtinianRing.isField_of_isDomain _)`. Rewrite `hle` using `[htop, top_le_iff]`. Rewrite using `[hle]`. Both sides reduce to the same expression.
-/
theorem locLen_finite {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A C : Submodule (𝓞 K) V) (hA : A.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.locLen w.asIdeal A C ≠ 0}.Finite := by
  by_cases h : ∀ x ∈ A, ∃ s : 𝓞 K, s ≠ 0 ∧ s • x ∈ C
  · obtain ⟨s, hs, hC⟩ := exists_unif A C hA h
    have hf := Ideal.finite_factors (I := Ideal.span {s}) (by simpa using hs)
    refine hf.subset fun w hw => ?_
    by_contra hn
    have hsw : s ∉ w.asIdeal := fun h => hn (Ideal.dvd_span_singleton.2 h)
    have : (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype = ⊤ := by
      rw [eq_top_iff]
      rintro ⟨x, t, ht, hx⟩ -
      exact ⟨s * t, Submonoid.mul_mem _ hsw ht, by rw [mul_smul]; exact hC _ hx⟩
    apply hw
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [this]
    simp [Module.length_eq_zero]
  · push Not at h
    obtain ⟨x, hx, hxC⟩ := h
    refine Set.Finite.subset Set.finite_empty fun w hw => hw ?_
    unfold Formalism.HermitianLatticesTheory.locLen
    have hxA : x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A := ⟨1, Submonoid.one_mem _, by simpa using hx⟩
    let φ : 𝓞 K →ₗ[𝓞 K] ((Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A) ⧸
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype) :=
      LinearMap.toSpanSingleton _ _ (Submodule.Quotient.mk ⟨x, hxA⟩)
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro r hr
      by_contra hr0
      have h1 : Submodule.Quotient.mk (p := (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal C).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype)
          (r • (⟨x, hxA⟩ : Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A)) = 0 := hr
      rw [Submodule.Quotient.mk_eq_zero] at h1
      obtain ⟨t, ht, h2⟩ := h1
      refine hxC (t * r) (mul_ne_zero (fun h0 => ht (h0 ▸ w.asIdeal.zero_mem)) hr0) ?_
      rw [mul_smul]
      exact h2
    have hle := Module.length_le_of_injective φ hφ
    have htop : Module.length (𝓞 K) (𝓞 K) = ⊤ := by
      by_contra hne
      have hfl := Module.length_ne_top_iff.1 hne
      have hart : IsArtinianRing (𝓞 K) := (isFiniteLength_iff_isNoetherian_isArtinian.1 hfl).2
      exact RingOfIntegers.not_isField K (IsArtinianRing.isField_of_isDomain _)
    rw [htop, top_le_iff] at hle
    rw [hle]
    rfl

/- English proof (translation)
Use `((locLen_finite A (A ⊓ B) hA).union (locLen_finite B (A ⊓ B) hB)).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn`. Apply `hw` to reduce the goal to its premises. Unfold `Formalism.HermitianLatticesTheory.lidx`.

Rewrite using `[hn.1, hn.2]`. Simplify using the standard rewrite rules.
-/
theorem lidx_finite {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V) (hA : A.FG) (hB : B.FG) :
    {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.lidx w.asIdeal A B ≠ 0}.Finite := by
  refine ((locLen_finite A (A ⊓ B) hA).union (locLen_finite B (A ⊓ B) hB)).subset fun w hw => ?_
  by_contra hn
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hn
  apply hw
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [hn.1, hn.2]
  simp

/- English proof (translation)
Establish `hli` using `(D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)).1`. Use `hli.finite` as an intermediate fact. Use `Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))` as an intermediate fact. Conclude with `inj_of_li D.what₂.embLL (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _) hli`.
-/
theorem jMt_inj (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis _ _)).1
  have := hli.finite
  have := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  exact inj_of_li D.what₂.embLL (D.what₂.jMt μ j) (Module.Free.chooseBasis _ _) hli

/- English proof (translation)
Use `choose f hf using h`. Use `choose! g hg using D.what₂.MtLat_sub μ j`. Use `Submodule.FG.of_le (Submodule.fg_span (((D.what₂.MtLat μ j).gen.finite_toSet.image fun v => f (g v)))) ?_` and prove the remaining obligations. Rewrite using `[Idx.TjL, Submodule.span_le]`. Introduce and unpack `x ⟨_, ⟨c, rfl⟩, hx⟩`.

Establish `: x = ∑ v ∈ (D.what₂.MtLat μ j).gen, (⟨D.what₂.OtoLL (c v), D.O_int _⟩ : 𝓞 D.what₂.LL) • f (g v)`. Apply `jMt_inj D μ j` to reduce the goal to its premises. Rewrite using `[← hx]`. Simplify using `only [map_sum, map_smul]`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations.

Use `show _ = D.what₂.jMt μ j (D.what₂.OtoLL (c v) • f (g v))`. Rewrite using `[LinearMap.map_smulₛₗ, hf, hg v hv]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, hv, rfl⟩)`.
-/
theorem TjL_fg (D : D7) (μ : D.what₂.Tup) (j : ℕ)
    (h : ∀ x : D.what₂.MtL μ j,
      ∃ y, D.what₂.jMt μ j y = D.what₂.eMt μ j ((D.what₂.Zj μ j).starProjection (D.what₂.jMt μ j x))) :
    (Idx.TjL D μ j).FG := by
  classical
  choose f hf using h
  choose! g hg using D.what₂.MtLat_sub μ j
  refine Submodule.FG.of_le (Submodule.fg_span
    (((D.what₂.MtLat μ j).gen.finite_toSet.image fun v => f (g v)))) ?_
  rw [Idx.TjL, Submodule.span_le]
  rintro x ⟨_, ⟨c, rfl⟩, hx⟩
  have : x = ∑ v ∈ (D.what₂.MtLat μ j).gen,
      (⟨D.what₂.OtoLL (c v), D.O_int _⟩ : 𝓞 D.what₂.LL) • f (g v) := by
    apply jMt_inj D μ j
    rw [← hx]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun v hv => ?_
    show _ = D.what₂.jMt μ j (D.what₂.OtoLL (c v) • f (g v))
    rw [LinearMap.map_smulₛₗ, hf, hg v hv]
    rfl
  rw [this]
  exact Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ⟨v, hv, rfl⟩)

/- English proof (translation)
Set `C : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j × (X.MjH j).V)` to `{ carrier := {p | p.1 ∈ A ∧ X.jM j p.2 = D.what₂.thetaP μ j (D.what₂.jMt μ j p.1)} add_mem' := by`. Introduce and unpack `a b ⟨hx, h1⟩ ⟨hy, h2⟩`. Conclude with `⟨A.add_mem hx hy, by rw [Prod.fst_add, Prod.snd_add, map_add, map_add, map_add, h1, h2]⟩`. Use the proof step `zero_mem' := ⟨A.zero_mem, by simp⟩`. Use the proof step `smul_mem' := by`.

Introduce and unpack `s a ⟨hx, h1⟩`. Use `⟨A.smul_mem s hx, ?_⟩` and prove the remaining obligations. Rewrite using `[Prod.smul_fst, Prod.smul_snd, Idx.smul_def, ← algebraMap_smul D.what₂.LL s a.2, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1, LinearMap.map_smul] }`. Establish `hAf : Module.Finite (𝓞 D.what₂.LL) A` using `Module.Finite.iff_fg.2 hA`. Set `φ : C →ₗ[𝓞 D.what₂.LL] A` to `LinearMap.codRestrict A ((LinearMap.fst _ _ _).comp C.subtype) fun p => p.2.1`.

Establish `hφ : Function.Injective φ`. Introduce `p q hpq`. Establish `h1 : p.1.1 = q.1.1` using `congrArg Subtype.val hpq`. Conclude with `Subtype.ext (Prod.ext h1 (Idx.jM_inj X j (by rw [p.2.2, q.2.2, h1])))`. Establish `hC : C.FG` using `Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)`.

Use `(hC.map (LinearMap.snd _ _ _)).of_le ?_` and prove the remaining obligations. Introduce and unpack `y ⟨x, hx, hy⟩`. Conclude with `⟨(x, y), ⟨hx, hy⟩, rfl⟩`.
-/
theorem thImg_fg {D : D7} (X : DivX D) (μ : D.what₂.Tup) (j : ℕ)
    (A : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j)) (hA : A.FG) : (Idx.thImg X μ j A).FG := by
  let C : Submodule (𝓞 D.what₂.LL) (D.what₂.MtL μ j × (X.MjH j).V) :=
    { carrier := {p | p.1 ∈ A ∧ X.jM j p.2 = D.what₂.thetaP μ j (D.what₂.jMt μ j p.1)}
      add_mem' := by
        rintro a b ⟨hx, h1⟩ ⟨hy, h2⟩
        exact ⟨A.add_mem hx hy, by rw [Prod.fst_add, Prod.snd_add, map_add, map_add, map_add, h1, h2]⟩
      zero_mem' := ⟨A.zero_mem, by simp⟩
      smul_mem' := by
        rintro s a ⟨hx, h1⟩
        refine ⟨A.smul_mem s hx, ?_⟩
        rw [Prod.smul_fst, Prod.smul_snd, Idx.smul_def, ← algebraMap_smul D.what₂.LL s a.2, LinearMap.map_smulₛₗ,
          LinearMap.map_smulₛₗ, h1, LinearMap.map_smul] }
  have hAf : Module.Finite (𝓞 D.what₂.LL) A := Module.Finite.iff_fg.2 hA
  let φ : C →ₗ[𝓞 D.what₂.LL] A :=
    LinearMap.codRestrict A ((LinearMap.fst _ _ _).comp C.subtype) fun p => p.2.1
  have hφ : Function.Injective φ := by
    intro p q hpq
    have h1 : p.1.1 = q.1.1 := congrArg Subtype.val hpq
    exact Subtype.ext (Prod.ext h1 (Idx.jM_inj X j (by rw [p.2.2, q.2.2, h1])))
  have hC : C.FG := Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)
  refine (hC.map (LinearMap.snd _ _ _)).of_le ?_
  rintro y ⟨x, hx, hy⟩
  exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩

/- English proof (translation)
Take `⟨S, hS⟩` from `id hfg`. Establish `hSm : ∀ a ∈ S, a ∈ Idx.TjL D D.what₂.mu0 j` using `fun a ha => hS ▸ Submodule.subset_span ha`. Establish `hB : (Idx.TjDual D D.what₂.mu0 j).FG` using `by choose g hg using fun (x : Idx.TjDual D D.what₂.mu0 j) (a : S) => x.2.2 a (hSm a a.2)`. Establish `inj : ∀ c d : 𝓞 D.what₂.LL, D.what₂.embLL (c : D.what₂.LL) = D.what₂.embLL (d : D.what₂.LL) → c = d` using `fun c d h => RingOfIntegers.ext (D.what₂.embLL.injective h)`. Set `φ : Idx.TjDual D D.what₂.mu0 j →ₗ[𝓞 D.what₂.LL] (S → 𝓞 D.what₂.LL)` to `{ toFun := g map_add' := fun x y => funext fun a => inj _ _ (by`.

Rewrite using `[← hg, Submodule.coe_add, map_add, inner_add_right, hg, hg]`. Use the proof step `simp)`. Use the proof step `map_smul' := fun s x => funext fun a => inj _ _ (by`. Rewrite using `[← hg, Submodule.coe_smul, Idx.smul_def, LinearMap.map_smulₛₗ, inner_smul_right, hg]`. Use the proof step `simp) }`.

Establish `hφ : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h0 : ∀ a ∈ S, inner ℂ (D.what₂.jMt D.what₂.mu0 j a) (D.what₂.jMt D.what₂.mu0 j x) = 0`. Introduce `a ha`.

Rewrite using `[hg x ⟨a, ha⟩, show g x ⟨a, ha⟩ = 0 from congrFun hx ⟨a, ha⟩]`. Simplify using the standard rewrite rules. Establish `hL : ∀ a ∈ Idx.TjL D D.what₂.mu0 j, inner ℂ (D.what₂.jMt D.what₂.mu0 j a) (D.what₂.jMt D.what₂.mu0 j x) = 0`. Introduce `a ha`. Rewrite `ha` using `[← hS]`.

Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a ha => exact h0 a ha`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, inner_add_left, ha, hb, add_zero]`. Consider the case `smul s a _ ha => rw [Idx.smul_def, LinearMap.map_smulₛₗ, inner_smul_left, ha, mul_zero]`.

Establish `hV : ∀ a ∈ Idx.TjV D D.what₂.mu0 j, inner ℂ (D.what₂.jMt D.what₂.mu0 j a) (D.what₂.jMt D.what₂.mu0 j x) = 0`. Introduce `a ha`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a ha => exact hL a ha`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [map_add, inner_add_left, ha, hb, add_zero]`. Consider the case `smul s a _ ha => rw [LinearMap.map_smulₛₗ, inner_smul_left, ha, mul_zero]`. Establish `hz` using `inner_self_eq_zero.1 (hV x x.2.1)`. Set `b` to `Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL D.what₂.mu0 j)`. Establish `: Fintype (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL D.what₂.mu0 j))` using `@Fintype.ofFinite _ (D.what₂.jMt_basis _ j b).1.finite`.

Establish `hinj : Function.Injective (D.what₂.jMt D.what₂.mu0 j)` using `inj_of_li D.what₂.embLL (D.what₂.jMt D.what₂.mu0 j) b (D.what₂.jMt_basis _ j b).1`. Conclude with `Subtype.ext (hinj (by rw [hz]; simp))`. Conclude with `Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)`. Use `lidx_finite (Idx.TjL D D.what₂.mu0 j) (Idx.TjDual D D.what₂.mu0 j) hfg hB` as an intermediate fact. Conclude with `this.preimage D.plEq.injective.injOn`.
-/
theorem jw_finite {D : D7} (j : ℕ) (hfg : (Idx.TjL D D.what₂.mu0 j).FG) :
    {w | Idx.jwIdx D D.what₂.mu0 j w ≠ 0}.Finite := by
  classical
  obtain ⟨S, hS⟩ := id hfg
  have hSm : ∀ a ∈ S, a ∈ Idx.TjL D D.what₂.mu0 j := fun a ha => hS ▸ Submodule.subset_span ha
  have hB : (Idx.TjDual D D.what₂.mu0 j).FG := by
    choose g hg using fun (x : Idx.TjDual D D.what₂.mu0 j) (a : S) => x.2.2 a (hSm a a.2)
    have inj : ∀ c d : 𝓞 D.what₂.LL, D.what₂.embLL (c : D.what₂.LL) = D.what₂.embLL (d : D.what₂.LL) → c = d :=
      fun c d h => RingOfIntegers.ext (D.what₂.embLL.injective h)
    let φ : Idx.TjDual D D.what₂.mu0 j →ₗ[𝓞 D.what₂.LL] (S → 𝓞 D.what₂.LL) :=
      { toFun := g
        map_add' := fun x y => funext fun a => inj _ _ (by
          rw [← hg, Submodule.coe_add, map_add, inner_add_right, hg, hg]; simp)
        map_smul' := fun s x => funext fun a => inj _ _ (by
          rw [← hg, Submodule.coe_smul, Idx.smul_def, LinearMap.map_smulₛₗ, inner_smul_right, hg]; simp) }
    have hφ : Function.Injective φ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      have h0 : ∀ a ∈ S, inner ℂ (D.what₂.jMt D.what₂.mu0 j a) (D.what₂.jMt D.what₂.mu0 j x) = 0 := by
        intro a ha
        rw [hg x ⟨a, ha⟩, show g x ⟨a, ha⟩ = 0 from congrFun hx ⟨a, ha⟩]
        simp
      have hL : ∀ a ∈ Idx.TjL D D.what₂.mu0 j,
          inner ℂ (D.what₂.jMt D.what₂.mu0 j a) (D.what₂.jMt D.what₂.mu0 j x) = 0 := by
        intro a ha
        rw [← hS] at ha
        induction ha using Submodule.span_induction with
        | mem a ha => exact h0 a ha
        | zero => simp
        | add a b _ _ ha hb => rw [map_add, inner_add_left, ha, hb, add_zero]
        | smul s a _ ha => rw [Idx.smul_def, LinearMap.map_smulₛₗ, inner_smul_left, ha, mul_zero]
      have hV : ∀ a ∈ Idx.TjV D D.what₂.mu0 j,
          inner ℂ (D.what₂.jMt D.what₂.mu0 j a) (D.what₂.jMt D.what₂.mu0 j x) = 0 := by
        intro a ha
        induction ha using Submodule.span_induction with
        | mem a ha => exact hL a ha
        | zero => simp
        | add a b _ _ ha hb => rw [map_add, inner_add_left, ha, hb, add_zero]
        | smul s a _ ha => rw [LinearMap.map_smulₛₗ, inner_smul_left, ha, mul_zero]
      have hz := inner_self_eq_zero.1 (hV x x.2.1)
      let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL D.what₂.mu0 j)
      have : Fintype (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL D.what₂.mu0 j)) :=
        @Fintype.ofFinite _ (D.what₂.jMt_basis _ j b).1.finite
      have hinj : Function.Injective (D.what₂.jMt D.what₂.mu0 j) :=
        inj_of_li D.what₂.embLL (D.what₂.jMt D.what₂.mu0 j) b (D.what₂.jMt_basis _ j b).1
      exact Subtype.ext (hinj (by rw [hz]; simp))
    exact Module.Finite.iff_fg.1 (Module.Finite.of_injective φ hφ)
  have := lidx_finite (Idx.TjL D D.what₂.mu0 j) (Idx.TjDual D D.what₂.mu0 j) hfg hB
  exact this.preimage D.plEq.injective.injOn

/- English proof (translation)
Introduce `D X hI _ hP`. Establish `hN : ∀ j ∈ Set.Icc 1 D.R.m, ({w | Idx.IjIdx X D.what₂.mu0 j w ≠ 0} ∪ {w | Idx.jwIdx D D.what₂.mu0 j w ≠ 0}).Finite`. Introduce `j hj`. Establish `hfg` using `TjL_fg D D.what₂.mu0 j (hP _ j hj.1 hj.2)`. Use `Set.Finite.union ?_ (jw_finite j hfg)` and prove the remaining obligations.

Conclude with `(lidx_finite (X.MjH j).L (Idx.thTj X D.what₂.mu0 j) (X.MjH_good j).2.1 (thImg_fg X _ j _ hfg)).preimage D.plEq.injective.injOn`. Establish `hf` using `((Set.finite_Icc 1 D.R.m).biUnion hN).image D.what₂.places.resChar`. Use `⟨hf.toFinset, fun w hw j h1 h2 => ?_⟩` and prove the remaining obligations. Rewrite using `[hI.Ij_def _ j w h1 h2, hI.jw_def _ j w h1 h2]`. Assume the negation of the conclusion as `hn`.

Rewrite `hn` using `[not_and_or]`. Conclude with `hw (hf.mem_toFinset.2 ⟨w, Set.mem_biUnion (x := j) ⟨h1, h2⟩ hn, rfl⟩)`.
-/
theorem idx_vanish_off_finite : ∀ (D : D7) (X : DivX D), IdxDefs D X → Idx.HermRat D → Idx.PrRat D → ∃ P : Finset ℕ, ∀ w, D.what₂.places.resChar w ∉ P → ∀ j, 1 ≤ j → j ≤ D.R.m → D.what₂.Ij D.what₂.mu0 j w = 0 ∧ D.what₂.jw D.what₂.mu0 j w = 0 := by
  intro D X hI _ hP
  classical
  have hN : ∀ j ∈ Set.Icc 1 D.R.m,
      ({w | Idx.IjIdx X D.what₂.mu0 j w ≠ 0} ∪ {w | Idx.jwIdx D D.what₂.mu0 j w ≠ 0}).Finite := by
    intro j hj
    have hfg := TjL_fg D D.what₂.mu0 j (hP _ j hj.1 hj.2)
    refine Set.Finite.union ?_ (jw_finite j hfg)
    exact (lidx_finite (X.MjH j).L (Idx.thTj X D.what₂.mu0 j) (X.MjH_good j).2.1
      (thImg_fg X _ j _ hfg)).preimage D.plEq.injective.injOn
  have hf := ((Set.finite_Icc 1 D.R.m).biUnion hN).image D.what₂.places.resChar
  refine ⟨hf.toFinset, fun w hw j h1 h2 => ?_⟩
  rw [hI.Ij_def _ j w h1 h2, hI.jw_def _ j w h1 h2]
  by_contra hn
  rw [not_and_or] at hn
  exact hw (hf.mem_toFinset.2 ⟨w, Set.mem_biUnion (x := j) ⟨h1, h2⟩ hn, rfl⟩)

end GlobalTheory.Mem.IdxFin

end
