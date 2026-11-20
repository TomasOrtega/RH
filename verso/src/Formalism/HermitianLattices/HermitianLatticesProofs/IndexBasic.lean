import Mathlib
import Formalism.HermitianLattices.StatementLat
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Fin

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

/- English proof (translation)
Establish `hfl : IsFiniteLength R (R ⧸ Ideal.span {d})` using `isFiniteLength_quotient_span_singleton R hd`. Establish `hart : IsArtinian R (R ⧸ Ideal.span {d})` using `(isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2`. Take `⟨n, y, hy⟩` from `IsArtinian.exists_pow_succ_smul_dvd s (1 : R ⧸ Ideal.span {d})`. Take `⟨t, rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `hy' : Ideal.Quotient.mk (Ideal.span {d}) (s ^ (n + 1) * t) = Ideal.Quotient.mk (Ideal.span {d}) (s ^ n)`.

Simplify `hy` using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq]`. Establish `: Ideal.Quotient.mk (Ideal.span {d}) (s ^ n - s ^ (n + 1) * t) = 0`. Rewrite using `[map_sub, hy', sub_self]`. Rewrite `this` using `[Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Take `⟨u, hu⟩` from `this`.

Conclude with `⟨n, t, u, by rw [← hu, mul_comm]⟩`.
-/
theorem indexBasic_key [IsNoetherianRing R] [Ring.KrullDimLE 1 R] {d : R}
    (hd : d ∈ nonZeroDivisors R) (s : R) :
    ∃ n : ℕ, ∃ t : R, ∃ u : R, s ^ n - s ^ (n + 1) * t = d * u := by
  have hfl : IsFiniteLength R (R ⧸ Ideal.span {d}) := isFiniteLength_quotient_span_singleton R hd
  have hart : IsArtinian R (R ⧸ Ideal.span {d}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).2
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd s (1 : R ⧸ Ideal.span {d})
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hy' : Ideal.Quotient.mk (Ideal.span {d}) (s ^ (n + 1) * t) =
      Ideal.Quotient.mk (Ideal.span {d}) (s ^ n) := by
    simpa [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hy
  have : Ideal.Quotient.mk (Ideal.span {d}) (s ^ n - s ^ (n + 1) * t) = 0 := by
    rw [map_sub, hy', sub_self]
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at this
  obtain ⟨u, hu⟩ := this
  exact ⟨n, t, u, by rw [← hu, mul_comm]⟩

/- English proof (translation)
Establish `: z ∈ localization₂ p (localization₂ p Y)` using `⟨s, hs, hz⟩`. Unfold `localization₂ at this ⊢`. Rewrite `this` using `[locBasic_locS_idem]`. Then use the resulting hypothesis.
-/
theorem indexBasic_smul_locP (p : Ideal R) [p.IsPrime] (Y : Submodule R W) {s : R} (hs : s ∉ p)
    {z : W} (hz : s • z ∈ localization₂ p Y) : z ∈ localization₂ p Y := by
  have : z ∈ localization₂ p (localization₂ p Y) := ⟨s, hs, hz⟩
  unfold localization₂ at this ⊢
  rwa [locBasic_locS_idem] at this

/- English proof (translation)
Use `set P := localization₂ p X with hP`. Use `set Q := (localization₂ p Y).comap P.subtype with hQ`. Establish `hXP : X ≤ P` using `locBasic_le_locS _ X`. Establish `hdP : ∀ x ∈ P, d • x ∈ localization₂ p Y`. Introduce and unpack `x ⟨s, hs, hsx⟩`.

Conclude with `⟨s, hs, by rw [smul_comm]; exact hdY _ hsx⟩`. Establish `hkill : ∀ m : ↥P ⧸ Q, d • m = 0`. Introduce `m`. Proceed by induction on `m using Submodule.Quotient.induction_on with`. Consider the case `H x`.

Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Conclude with `hdP x.1 x.2`. Set `ψ : ↥X →ₗ[R] ↥P ⧸ Q` to `Q.mkQ ∘ₗ Submodule.inclusion hXP`. Establish `hsurj : Function.Surjective ψ`. Introduce `z`.

Proceed by induction on `z using Submodule.Quotient.induction_on with`. Consider the case `H x`. Take `⟨s, hs, hsx⟩` from `x.2`. Take `⟨n, t, u, htu⟩` from `indexBasic_key hd s`. Use `⟨⟨t • s • (x : W), X.smul_mem t hsx⟩, ?_⟩` and prove the remaining obligations.

Use `show Q.mkQ _ = Submodule.Quotient.mk x`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.eq]`. Use `show (t • s • (x : W) - x) ∈ localization₂ p Y`. Establish `hsn : s ^ n ∉ p` using `fun h => hs (‹p.IsPrime›.mem_of_pow_mem n h)`. Apply `indexBasic_smul_locP p Y hsn` to reduce the goal to its premises.

Establish `e : s ^ n • (t • s • (x : W) - x) = - (u • (d • (x : W)))`. Take the linear combination `(norm := module) -(htu • (x : W))`. Rewrite using `[e]`. Conclude with `(localization₂ p Y).neg_mem ((localization₂ p Y).smul_mem u (hdP x.1 x.2))`. Take `⟨n, g, hg⟩` from `Submodule.fg_iff_exists_fin_generating_family.mp hX`.

Establish `hgX : ∀ i, g i ∈ X` using `fun i => hg ▸ Submodule.subset_span (Set.mem_range_self i)`. Set `m : Fin n → ↥P ⧸ Q` to `fun i => ψ ⟨g i, hgX i⟩`. Set `F : (Fin n → R ⧸ Ideal.span {d}) →ₗ[R] ↥P ⧸ Q` to `∑ i, ((Ideal.span {d}).liftQ (LinearMap.toSpanSingleton R _ (m i)) (by`. Introduce `r hr`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hr`.

Simplify using `[LinearMap.mem_ker, mul_smul, hkill])) ∘ₗ LinearMap.proj i`. Establish `hF : Function.Surjective F`. Introduce `z`. Take `⟨x, rfl⟩` from `hsurj z`. Establish `hx : (x : W) ∈ Submodule.span R (Set.range g)` using `hg ▸ x.2`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp hx`. Use `⟨fun i => Submodule.Quotient.mk (c i), ?_⟩` and prove the remaining obligations. Establish `hx' : x = ∑ i, c i • (⟨g i, hgX i⟩ : ↥X)` using `Subtype.ext (by simp [hc])`. Rewrite using `[hx', map_sum]`. Simplify using `only [F, m]`.

Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, LinearMap.proj_apply, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, map_smul]`. Establish `hfin : IsFiniteLength R (Fin n → R ⧸ Ideal.span {d})`. Establish `hfl : IsFiniteLength R (R ⧸ Ideal.span {d})` using `isFiniteLength_quotient_span_singleton R hd`.

Take `⟨h1, h2⟩` from `isFiniteLength_iff_isNoetherian_isArtinian.mp hfl`. Conclude with `isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩`. Conclude with `hfin.of_surjective hF`.
-/
theorem indexBasic_finLen [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (p : Ideal R) [p.IsPrime]
    (X Y : Submodule R W) (hX : X.FG) {d : R} (hd : d ∈ nonZeroDivisors R)
    (hdY : ∀ x ∈ X, d • x ∈ Y) :
    IsFiniteLength R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) := by
  set P := localization₂ p X with hP
  set Q := (localization₂ p Y).comap P.subtype with hQ
  have hXP : X ≤ P := locBasic_le_locS _ X
  have hdP : ∀ x ∈ P, d • x ∈ localization₂ p Y := by
    rintro x ⟨s, hs, hsx⟩
    exact ⟨s, hs, by rw [smul_comm]; exact hdY _ hsx⟩
  have hkill : ∀ m : ↥P ⧸ Q, d • m = 0 := by
    intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact hdP x.1 x.2
  let ψ : ↥X →ₗ[R] ↥P ⧸ Q := Q.mkQ ∘ₗ Submodule.inclusion hXP
  have hsurj : Function.Surjective ψ := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨s, hs, hsx⟩ := x.2
      obtain ⟨n, t, u, htu⟩ := indexBasic_key hd s
      refine ⟨⟨t • s • (x : W), X.smul_mem t hsx⟩, ?_⟩
      show Q.mkQ _ = Submodule.Quotient.mk x
      rw [Submodule.mkQ_apply, Submodule.Quotient.eq]
      show (t • s • (x : W) - x) ∈ localization₂ p Y
      have hsn : s ^ n ∉ p := fun h => hs (‹p.IsPrime›.mem_of_pow_mem n h)
      apply indexBasic_smul_locP p Y hsn
      have e : s ^ n • (t • s • (x : W) - x) = - (u • (d • (x : W))) := by
        linear_combination (norm := module) -(htu • (x : W))
      rw [e]
      exact (localization₂ p Y).neg_mem ((localization₂ p Y).smul_mem u (hdP x.1 x.2))
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hX
  have hgX : ∀ i, g i ∈ X := fun i => hg ▸ Submodule.subset_span (Set.mem_range_self i)
  let m : Fin n → ↥P ⧸ Q := fun i => ψ ⟨g i, hgX i⟩
  let F : (Fin n → R ⧸ Ideal.span {d}) →ₗ[R] ↥P ⧸ Q :=
    ∑ i, ((Ideal.span {d}).liftQ (LinearMap.toSpanSingleton R _ (m i)) (by
      intro r hr
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
      simp [LinearMap.mem_ker, mul_smul, hkill])) ∘ₗ LinearMap.proj i
  have hF : Function.Surjective F := by
    intro z
    obtain ⟨x, rfl⟩ := hsurj z
    have hx : (x : W) ∈ Submodule.span R (Set.range g) := hg ▸ x.2
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hx
    refine ⟨fun i => Submodule.Quotient.mk (c i), ?_⟩
    have hx' : x = ∑ i, c i • (⟨g i, hgX i⟩ : ↥X) := Subtype.ext (by simp [hc])
    rw [hx', map_sum]
    simp only [F, m]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply, LinearMap.proj_apply, Submodule.liftQ_apply,
      LinearMap.toSpanSingleton_apply, map_smul]
  have hfin : IsFiniteLength R (Fin n → R ⧸ Ideal.span {d}) := by
    have hfl : IsFiniteLength R (R ⧸ Ideal.span {d}) := isFiniteLength_quotient_span_singleton R hd
    obtain ⟨h1, h2⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  exact hfin.of_surjective hF

/- English proof (translation)
Set `f : (↥Mm ⧸ N.comap Mm.subtype) →ₗ[R] (↥P ⧸ N.comap P.subtype)` to `Submodule.mapQ _ _ (Submodule.inclusion hMP) (by`. Introduce `x hx`. Simplify using `only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢`. Conclude with `hx)`. Set `g : (↥P ⧸ N.comap P.subtype) →ₗ[R] (↥P ⧸ Mm.comap P.subtype)` to `Submodule.mapQ _ _ LinearMap.id (fun x hx => hNM hx)`.

Use `Module.length_eq_add_of_exact f g ?_ ?_ ?_` and prove the remaining obligations. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `y hy`. Proceed by induction on `y using Submodule.Quotient.induction_on with`. Consider the case `H x`.

Rewrite `hy` using `[LinearMap.mem_ker]`. Simplify using `only [f] at hy`. Rewrite `hy` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]`. Conclude with `hy`.

Introduce `z`. Proceed by induction on `z using Submodule.Quotient.induction_on with`. Consider the case `H x => exact ⟨Submodule.Quotient.mk x, rfl⟩`. Introduce `y`. Proceed by induction on `y using Submodule.Quotient.induction_on with`.

Consider the case `H x`. Prove the components needed by the constructor for the conclusion. Introduce `hy dsimp only [g] at hy`. Rewrite `hy` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨Submodule.Quotient.mk ⟨x, hy⟩, rfl⟩`.

Introduce and unpack `⟨w, hw⟩`. Rewrite using `[← hw]`. Proceed by induction on `w using Submodule.Quotient.induction_on with`. Consider the case `H z => dsimp only [f, g]`. Rewrite using `[Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`.

Conclude with `z.2`.
-/
theorem indexBasic_len_add (N Mm P : Submodule R W) (hNM : N ≤ Mm) (hMP : Mm ≤ P) :
    Module.length R (↥P ⧸ N.comap P.subtype) =
      Module.length R (↥Mm ⧸ N.comap Mm.subtype) + Module.length R (↥P ⧸ Mm.comap P.subtype) := by
  let f : (↥Mm ⧸ N.comap Mm.subtype) →ₗ[R] (↥P ⧸ N.comap P.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hMP) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact hx)
  let g : (↥P ⧸ N.comap P.subtype) →ₗ[R] (↥P ⧸ Mm.comap P.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => hNM hx)
  refine Module.length_eq_add_of_exact f g ?_ ?_ ?_
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker] at hy
      dsimp only [f] at hy
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact hy
  · intro z
    induction z using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro hy
        dsimp only [g] at hy
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
        exact ⟨Submodule.Quotient.mk ⟨x, hy⟩, rfl⟩
      · rintro ⟨w, hw⟩
        rw [← hw]
        induction w using Submodule.Quotient.induction_on with
        | H z =>
          dsimp only [f, g]
          rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
          exact z.2

/- English proof (translation)
Unfold `locLen`. Rewrite using `[Submodule.comap_subtype_self]`. Simplify using the standard rewrite rules.
-/
theorem indexBasic_locLen_self (p : Ideal R) [p.IsPrime] (X : Submodule R W) :
    locLen p X X = 0 := by
  unfold locLen
  rw [Submodule.comap_subtype_self]
  simp

/- English proof (translation)
Establish `e1` using `indexBasic_len_add (localization₂ p D) (localization₂ p (A ⊓ B)) (localization₂ p A) (locBasic_locS_mono _ (le_inf hDA hDB)) (locBasic_locS_mono _ inf_le_left)`. Establish `e2` using `indexBasic_len_add (localization₂ p D) (localization₂ p (A ⊓ B)) (localization₂ p B) (locBasic_locS_mono _ (le_inf hDA hDB)) (locBasic_locS_mono _ inf_le_right)`. Rewrite `hA` using `[e1]`. Rewrite `hB` using `[e2]`. Take `⟨ha, hx⟩` from `WithTop.add_ne_top.mp hA`.

Take `⟨-, hy⟩` from `WithTop.add_ne_top.mp hB`. Unfold `lidx locLen`. Rewrite using `[e1, e2, ENat.toNat_add ha hx, ENat.toNat_add ha hy]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem indexBasic_lidx_via (p : Ideal R) [p.IsPrime] (A B D : Submodule R W) (hDA : D ≤ A)
    (hDB : D ≤ B)
    (hA : Module.length R (↥(localization₂ p A) ⧸ (localization₂ p D).comap (localization₂ p A).subtype) ≠ ⊤)
    (hB : Module.length R (↥(localization₂ p B) ⧸ (localization₂ p D).comap (localization₂ p B).subtype) ≠ ⊤) :
    lidx p A B = (locLen p A D : ℤ) - locLen p B D := by
  have e1 := indexBasic_len_add (localization₂ p D) (localization₂ p (A ⊓ B)) (localization₂ p A)
    (locBasic_locS_mono _ (le_inf hDA hDB)) (locBasic_locS_mono _ inf_le_left)
  have e2 := indexBasic_len_add (localization₂ p D) (localization₂ p (A ⊓ B)) (localization₂ p B)
    (locBasic_locS_mono _ (le_inf hDA hDB)) (locBasic_locS_mono _ inf_le_right)
  rw [e1] at hA
  rw [e2] at hB
  obtain ⟨ha, hx⟩ := WithTop.add_ne_top.mp hA
  obtain ⟨-, hy⟩ := WithTop.add_ne_top.mp hB
  unfold lidx locLen
  rw [e1, e2, ENat.toNat_add ha hx, ENat.toNat_add ha hy]
  push_cast
  ring

/- English proof (translation)
Take `⟨s, rfl⟩` from `hX`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `⟨1, S.one_mem, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot]`. Substitute `hx` using the available equality. Simplify using the standard rewrite rules. Consider the case `insert a s ha ih`. Rewrite `hY`, the goal using `[Finset.coe_insert, Submodule.span_insert]`.

Take `⟨d, hd, hds⟩` from `ih (le_trans le_sup_right hY)`. Take `⟨e, he, hea⟩` from `hY (Submodule.mem_sup_left (Submodule.mem_span_singleton_self a))`. Use `⟨e * d, S.mul_mem he hd, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`.

Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.mp hy`. Rewrite using `[smul_add]`. Use `Y.add_mem ?_ ?_` and prove the remaining obligations. Establish `: (e * d) • (r • a) = r • d • (e • a)` using `by module`. Rewrite using `[this]`.

Conclude with `Y.smul_mem r (Y.smul_mem d hea)`. Rewrite using `[mul_smul]`. Conclude with `Y.smul_mem e (hds z hz)`.
-/
theorem indexBasic_denom (S : Submonoid R) (X Y : Submodule R W) (hX : X.FG)
    (hY : X ≤ locS S Y) : ∃ d ∈ S, ∀ x ∈ X, d • x ∈ Y := by
  classical
  obtain ⟨s, rfl⟩ := hX
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, S.one_mem, ?_⟩
    intro x hx
    rw [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
    subst hx
    simp
  | insert a s ha ih =>
    rw [Finset.coe_insert, Submodule.span_insert] at hY ⊢
    obtain ⟨d, hd, hds⟩ := ih (le_trans le_sup_right hY)
    obtain ⟨e, he, hea⟩ := hY (Submodule.mem_sup_left (Submodule.mem_span_singleton_self a))
    refine ⟨e * d, S.mul_mem he hd, ?_⟩
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · have : (e * d) • (r • a) = r • d • (e • a) := by module
      rw [this]
      exact Y.smul_mem r (Y.smul_mem d hea)
    · rw [mul_smul]
      exact Y.smul_mem e (hds z hz)

end Fin

section K

variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/- English proof (translation)
Set `T : Submodule K V` to `{ carrier := locS (nonZeroDivisors R) Y add_mem' := (locS (nonZeroDivisors R) Y).add_mem zero_mem' := (locS (nonZeroDivisors R) Y).zero_mem smul_mem' := by`. Introduce and unpack `c v ⟨d, hd, hdv⟩`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective R c`. Establish `hb0 : algebraMap R K b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Use `⟨b * d, Submonoid.mul_mem _ hb hd, ?_⟩` and prove the remaining obligations.

Establish `hc : algebraMap R K b * (algebraMap R K a / algebraMap R K b) = algebraMap R K a`. Clear the denominators using the available nonvanishing facts. Establish `: (b * d) • ((algebraMap R K a / algebraMap R K b) • v) = a • (d • v)`. Rewrite using `[mul_comm, mul_smul, ← algebraMap_smul K b, smul_smul, hc, algebraMap_smul, smul_comm]`. Rewrite using `[this]`.

Conclude with `Y.smul_mem a hdv }`. Establish `hle : Submodule.span K (Y : Set V) ≤ T` using `Submodule.span_le.mpr (fun y hy => locBasic_le_locS _ Y hy)`. Rewrite `hle` using `[hY]`. Conclude with `eq_top_iff.mpr (fun v _ => hle Submodule.mem_top)`.
-/
theorem indexBasic_locS_top (Y : Submodule R V) (hY : Submodule.span K (Y : Set V) = ⊤) :
    locS (nonZeroDivisors R) Y = ⊤ := by
  let T : Submodule K V :=
    { carrier := locS (nonZeroDivisors R) Y
      add_mem' := (locS (nonZeroDivisors R) Y).add_mem
      zero_mem' := (locS (nonZeroDivisors R) Y).zero_mem
      smul_mem' := by
        rintro c v ⟨d, hd, hdv⟩
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R c
        have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
        refine ⟨b * d, Submonoid.mul_mem _ hb hd, ?_⟩
        have hc : algebraMap R K b * (algebraMap R K a / algebraMap R K b) = algebraMap R K a := by
          field_simp
        have : (b * d) • ((algebraMap R K a / algebraMap R K b) • v) = a • (d • v) := by
          rw [mul_comm, mul_smul, ← algebraMap_smul K b, smul_smul, hc, algebraMap_smul,
            smul_comm]
        rw [this]
        exact Y.smul_mem a hdv }
  have hle : Submodule.span K (Y : Set V) ≤ T :=
    Submodule.span_le.mpr (fun y hy => locBasic_le_locS _ Y hy)
  rw [hY] at hle
  exact eq_top_iff.mpr (fun v _ => hle Submodule.mem_top)

end K

/- English proof (translation)
Take `⟨b, hbA, hspan, hli⟩` from `exists_linearIndependent K (A : Set V)`. Establish `htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → V))`. Rewrite using `[Subtype.range_coe, hspan, hA]`. Set `e : Module.Basis b K V` to `Module.Basis.mk hli htop`. Establish `: Finite b` using `Module.Finite.finite_basis e`.

Establish `: Fintype b` using `Fintype.ofFinite b`. Set `φ : V →ₗ[K] (b → K)` to `LinearMap.pi (fun i => h (e i))`. Establish `hφ : Function.Injective φ`. Rewrite using `[← LinearMap.ker_eq_bot, eq_bot_iff]`. Introduce `x hx`.

Rewrite `hx` using `[LinearMap.mem_ker]`. Rewrite using `[Submodule.mem_bot]`. Establish `h0 : h.flip x = 0` using `e.ext (fun i => by`. Use `congr_fun hx i` as an intermediate fact. Simplify `this)` using `[φ]`.

Conclude with `hnd.2 x (fun z => by`. Use `LinearMap.congr_fun h0 z` as an intermediate fact. Simplify using `using this)`. Establish `hφs : Function.Surjective φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by`. Rewrite using `[Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis e])).mp hφ`.

Set `ψ` to `LinearEquiv.ofBijective φ ⟨hφ, hφs⟩`. Use `⟨Submodule.span R (Set.range (fun j : b => ψ.symm (Pi.single j 1))), Submodule.fg_span (Set.finite_range _), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[dualBasic_mem_dual]`. Establish `hxj : ∀ j : b, ∃ r : R, algebraMap R K r = h (e j) x` using `fun j => by`.

Use `hx (e j) (by rw [Module.Basis.mk_apply]; exact hbA j.2)` as an intermediate fact. Rewrite `this` using `[Submodule.mem_one]`. Then use the resulting hypothesis. Use `choose r hr using hxj`. Establish `hψ : ∀ y, ψ y = φ y` using `fun y => LinearEquiv.ofBijective_apply φ y`. Establish `hx' : x = ∑ j, (algebraMap R K (r j)) • ψ.symm (Pi.single j 1)`.

Apply `ψ.injective` to reduce the goal to its premises. Rewrite using `[map_sum]`. Simplify using `only [map_smul, LinearEquiv.apply_symm_apply]`. Use extensionality with `i`. Rewrite using `[hψ]`.

Simplify using `[Finset.sum_apply, Pi.single_apply, hr, φ]`. Rewrite using `[hx']`. Repeatedly rewrite using `[algebraMap_smul]`. Conclude with `Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))`.
-/
theorem indexBasic_dual_le_fg {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (hnd : h.Nondegenerate) (A : Submodule R V)
    (hA : Submodule.span K (A : Set V) = ⊤) :
    ∃ F : Submodule R V, F.FG ∧ dual h A ≤ F := by
  classical
  obtain ⟨b, hbA, hspan, hli⟩ := exists_linearIndependent K (A : Set V)
  have htop : ⊤ ≤ Submodule.span K (Set.range ((↑) : b → V)) := by
    rw [Subtype.range_coe, hspan, hA]
  let e : Module.Basis b K V := Module.Basis.mk hli htop
  have : Finite b := Module.Finite.finite_basis e
  have : Fintype b := Fintype.ofFinite b
  let φ : V →ₗ[K] (b → K) := LinearMap.pi (fun i => h (e i))
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    have h0 : h.flip x = 0 := e.ext (fun i => by
      have := congr_fun hx i
      simpa [φ] using this)
    exact hnd.2 x (fun z => by
      have := LinearMap.congr_fun h0 z
      simpa using this)
  have hφs : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis e])).mp hφ
  let ψ := LinearEquiv.ofBijective φ ⟨hφ, hφs⟩
  refine ⟨Submodule.span R (Set.range (fun j : b => ψ.symm (Pi.single j 1))),
    Submodule.fg_span (Set.finite_range _), ?_⟩
  intro x hx
  rw [dualBasic_mem_dual] at hx
  have hxj : ∀ j : b, ∃ r : R, algebraMap R K r = h (e j) x := fun j => by
    have := hx (e j) (by rw [Module.Basis.mk_apply]; exact hbA j.2)
    rwa [Submodule.mem_one] at this
  choose r hr using hxj
  have hψ : ∀ y, ψ y = φ y := fun y => LinearEquiv.ofBijective_apply φ y
  have hx' : x = ∑ j, (algebraMap R K (r j)) • ψ.symm (Pi.single j 1) := by
    apply ψ.injective
    rw [map_sum]
    simp only [map_smul, LinearEquiv.apply_symm_apply]
    ext i
    rw [hψ]
    simp [Finset.sum_apply, Pi.single_apply, hr, φ]
  rw [hx']
  simp_rw [algebraMap_smul]
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/- English proof (translation)
Introduce `R K V _ _ _ _ _ _ _ _ _ _ _ h hs hnd hstar p _ A B C hA hB hC`. Establish `hfin : ∀ X Y : Submodule R V, X.FG → locS (nonZeroDivisors R) Y = ⊤ → Module.length R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) ≠ ⊤`. Introduce `X Y hX hY`. Take `⟨d, hd, hdY⟩` from `indexBasic_denom (nonZeroDivisors R) X Y hX (by rw [hY]; exact le_top)`. Conclude with `Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hd hdY)`.

Establish `hAt` using `indexBasic_locS_top (K := K) A (Submodule.IsLattice.span_eq_top (self := hA))`. Establish `hBt` using `indexBasic_locS_top (K := K) B (Submodule.IsLattice.span_eq_top (self := hB))`. Establish `hCt` using `indexBasic_locS_top (K := K) C (Submodule.IsLattice.span_eq_top (self := hC))`. Establish `hAfg : A.FG` using `Submodule.IsLattice.fg (self := hA)`. Establish `hBfg : B.FG` using `Submodule.IsLattice.fg (self := hB)`.

Establish `hCfg : C.FG` using `Submodule.IsLattice.fg (self := hC)`. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `lidx`. Conclude with `sub_self _`. Unfold `lidx`.

Rewrite using `[inf_comm]`. Expand and normalize the polynomial expressions, which then agree. Establish `hDt : locS (nonZeroDivisors R) (A ⊓ B ⊓ C) = ⊤`. Rewrite using `[locBasic_locS_inf, locBasic_locS_inf, hAt, hBt, hCt]`. Simplify using the standard rewrite rules.

Establish `hAD` using `hfin A _ hAfg hDt`. Establish `hBD` using `hfin B _ hBfg hDt`. Establish `hCD` using `hfin C _ hCfg hDt`. Rewrite using `[indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right hAD hCD, indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) (le_trans inf_le_left inf_le_right) hAD hBD, indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le …`. Expand and normalize the polynomial expressions, which then agree.

Introduce `hBA`. Unfold `lidx`. Rewrite using `[inf_eq_right.mpr hBA, indexBasic_locLen_self]`. Simplify using the standard rewrite rules. Introduce `hU`.

Unfold `jIdx`. Rewrite using `[show dual h A = A from hU]`. Unfold `lidx`. Conclude with `sub_self _`. Introduce `hI`.

Establish `hle : A ≤ dual h A`. Introduce `x hx`. Rewrite using `[dualBasic_mem_dual]`. Introduce `y hy`. Conclude with `hI y hy x hx`.

Establish `hDfg : (dual h A).FG`. Take `⟨F, hF, hDF⟩` from `indexBasic_dual_le_fg h hnd A (Submodule.IsLattice.span_eq_top (self := hA))`. Conclude with `hF.of_le hDF`. Establish `hDfin` using `hfin (dual h A) A hDfg hAt`. Unfold `jIdx lidx`.

Rewrite using `[inf_eq_left.mpr hle, indexBasic_locLen_self]`. Use `⟨by simp, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_zero, zero_sub, neg_eq_zero, Nat.cast_eq_zero]`. Unfold `locLen`. Rewrite using `[ENat.toNat_eq_zero]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h0 | htop)`. Rewrite `h0` using `[Module.length_eq_zero_iff]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`.

Establish `h1 : (Submodule.Quotient.mk ⟨x, hx⟩ : ↥(localization₂ p (dual h A)) ⧸ (localization₂ p A).comap (localization₂ p (dual h A)).subtype) = 0` using `Subsingleton.elim _ _`. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `h1`. Conclude with `locBasic_locS_mono _ hle`. Conclude with `absurd htop hDfin`.

Introduce `heq left`. Rewrite using `[Module.length_eq_zero_iff]`. Establish `htop' : (localization₂ p A).comap (localization₂ p (dual h A)).subtype = ⊤`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨x, hx⟩ -`.

Rewrite `hx` using `[heq]`. Conclude with `hx`. Rewrite using `[htop']`. Use `infer_instance`.
-/
theorem indexBasic : IndexBasic := by
  intro R K V _ _ _ _ _ _ _ _ _ _ _ h hs hnd hstar p _ A B C hA hB hC
  have hfin : ∀ X Y : Submodule R V, X.FG → locS (nonZeroDivisors R) Y = ⊤ →
      Module.length R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) ≠ ⊤ := by
    intro X Y hX hY
    obtain ⟨d, hd, hdY⟩ :=
      indexBasic_denom (nonZeroDivisors R) X Y hX (by rw [hY]; exact le_top)
    exact Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hd hdY)
  have hAt := indexBasic_locS_top (K := K) A (Submodule.IsLattice.span_eq_top (self := hA))
  have hBt := indexBasic_locS_top (K := K) B (Submodule.IsLattice.span_eq_top (self := hB))
  have hCt := indexBasic_locS_top (K := K) C (Submodule.IsLattice.span_eq_top (self := hC))
  have hAfg : A.FG := Submodule.IsLattice.fg (self := hA)
  have hBfg : B.FG := Submodule.IsLattice.fg (self := hB)
  have hCfg : C.FG := Submodule.IsLattice.fg (self := hC)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold lidx
    exact sub_self _
  · unfold lidx
    rw [inf_comm]
    ring
  · have hDt : locS (nonZeroDivisors R) (A ⊓ B ⊓ C) = ⊤ := by
      rw [locBasic_locS_inf, locBasic_locS_inf, hAt, hBt, hCt]
      simp
    have hAD := hfin A _ hAfg hDt
    have hBD := hfin B _ hBfg hDt
    have hCD := hfin C _ hCfg hDt
    rw [indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right
        hAD hCD,
      indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
        (le_trans inf_le_left inf_le_right) hAD hBD,
      indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right
        hBD hCD]
    ring
  · intro hBA
    unfold lidx
    rw [inf_eq_right.mpr hBA, indexBasic_locLen_self]
    simp
  · intro hU
    unfold jIdx
    rw [show dual h A = A from hU]
    unfold lidx
    exact sub_self _
  · intro hI
    have hle : A ≤ dual h A := by
      intro x hx
      rw [dualBasic_mem_dual]
      intro y hy
      exact hI y hy x hx
    have hDfg : (dual h A).FG := by
      obtain ⟨F, hF, hDF⟩ :=
        indexBasic_dual_le_fg h hnd A (Submodule.IsLattice.span_eq_top (self := hA))
      exact hF.of_le hDF
    have hDfin := hfin (dual h A) A hDfg hAt
    unfold jIdx lidx
    rw [inf_eq_left.mpr hle, indexBasic_locLen_self]
    refine ⟨by simp, ?_⟩
    rw [Nat.cast_zero, zero_sub, neg_eq_zero, Nat.cast_eq_zero]
    unfold locLen
    rw [ENat.toNat_eq_zero]
    constructor
    · rintro (h0 | htop)
      · rw [Module.length_eq_zero_iff] at h0
        apply le_antisymm
        · intro x hx
          have h1 : (Submodule.Quotient.mk ⟨x, hx⟩ : ↥(localization₂ p (dual h A)) ⧸
              (localization₂ p A).comap (localization₂ p (dual h A)).subtype) = 0 := Subsingleton.elim _ _
          rw [Submodule.Quotient.mk_eq_zero] at h1
          exact h1
        · exact locBasic_locS_mono _ hle
      · exact absurd htop hDfin
    · intro heq
      left
      rw [Module.length_eq_zero_iff]
      have htop' : (localization₂ p A).comap (localization₂ p (dual h A)).subtype = ⊤ := by
        rw [eq_top_iff]
        rintro ⟨x, hx⟩ -
        rw [heq] at hx
        exact hx
      rw [htop']
      infer_instance

end Formalism.HermitianLatticesTheory
