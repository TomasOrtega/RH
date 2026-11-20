import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlmostEverywhereSpherical
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFMapSubtype
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsHermSemilocalLocRing
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsASDOfTuple

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

/- English proof (translation)
Use `haveI := h𝔭`. Use `Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 ?_` and prove the remaining obligations. Introduce `t ht`. Rewrite `ht` using `[RingHom.mem_ker]`. Establish `h1 : algebraMap F K (t : F) = 0`.

Establish `h2` using `congrArg (algebraMap (𝓞 K) K) ht`. Rewrite `h2` using `[map_zero]`. Conclude with `h2`. Establish `h3 : (t : F) = 0` using `(algebraMap F K).injective (by rw [h1, map_zero])`. Establish `h4 : t = 0` using `by exact_mod_cast h3`.

Rewrite using `[h4]`. Conclude with `𝔭.zero_mem`.
-/
theorem exists_over (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by
  haveI := h𝔭
  refine Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 ?_
  intro t ht
  rw [RingHom.mem_ker] at ht
  have h1 : algebraMap F K (t : F) = 0 := by
    have h2 := congrArg (algebraMap (𝓞 K) K) ht
    rw [map_zero] at h2
    exact h2
  have h3 : (t : F) = 0 := (algebraMap F K).injective (by rw [h1, map_zero])
  have h4 : t = 0 := by exact_mod_cast h3
  rw [h4]
  exact 𝔭.zero_mem

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Introduce `v hv` and use `spanS_induction (p := fun v => v ∈ X) X.zero_mem (fun a b ha hb => X.add_mem ha hb) (fun c _ a ha => X.smul_mem c ha) hx v hv`.
-/
theorem spanS_le_of {S : Subring K} {n : ℕ} {x : Fin n → V} {X : Submodule K V} (hx : ∀ i, x i ∈ X) :
    ∀ v ∈ spanS S x, v ∈ X := fun v hv =>
  spanS_induction (p := fun v => v ∈ X) X.zero_mem (fun a b ha hb => X.add_mem ha hb)
    (fun c _ a ha => X.smul_mem c ha) hx v hv

/- English proof (translation)
Establish `inj` using `IsFractionRing.injective (𝓞 K) K`. Establish `hcomp : ∀ t : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F)` using `fun t => rfl`. Establish `hconj_conj : ∀ a : 𝓞 K, conjO K (conjO K a) = a` using `fun a => inj (by rw [algebraMap_conjO, algebraMap_conjO, star_star])`. Take `⟨P, hP, rfl⟩` from `exists_over (K := K) 𝔭 h𝔭`. Take `⟨π, hπ, hfin⟩` from `exists_unif_fin hF hP`.

Establish `hS` using `isHermSemilocal_locRing hK hP`. Take `⟨x, hxL, hli, hsp, hloc⟩` from `exists_basis_in hL h𝔭`. Establish `hdet0 : (U0.gram h x).det ≠ 0` using `det_gram_ne_zero hnd hli hsp`. Take `⟨N, hN⟩` from `hfin _ hdet0`. Establish `hint : ∀ r : 𝓞 K, algebraMap (𝓞 K) K r ∈ locRing P`.

Introduce `r`. Express the relevant statement in the definitionally equal form `_ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P`. Rewrite using `[Formalism.HermitianLatticesTheory.locDual_mem_locR]`. Conclude with `⟨1, one_mem _, Submodule.mem_one.mpr ⟨r, by rw [map_one, one_mul]⟩⟩`. Establish `hxS : ∀ i j, h (x i) (x j) ∈ locRing P`.

Introduce `i j`. Take `⟨r, hr⟩` from `Submodule.mem_one.mp (hLi _ (hxL i) _ (hxL j))`. Rewrite using `[← hr]`. Conclude with `hint r`. Take `⟨y, hyo, hys⟩` from `exists_orth_gen hS hπ _ N h hs x hxS hN`.

Establish `hxy : ∀ i, x i ∈ spanS (locRing P) y` using `fun i => by rw [hys]; exact mem_spanS x i`. Take `⟨c, -, hc⟩` from `gram_det_of_le (h := h) hS hxy`. Establish `hdety : (U0.gram h y).det ≠ 0` using `fun h0 => hdet0 (by rw [hc, h0, mul_zero])`. Establish `hdiag : U0.gram h y = Matrix.diagonal (fun i => h (y i) (y i))`. Use extensionality with `i j`.

Use `show h (y i) (y j) = Matrix.diagonal (fun i => h (y i) (y i)) i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Rewrite using `[Matrix.diagonal_apply_eq]`. Rewrite using `[Matrix.diagonal_apply_ne _ hij]`.

Conclude with `hyo i j hij`. Establish `hyy : ∀ i, h (y i) (y i) ≠ 0`. Rewrite `hdety` using `[hdiag, Matrix.det_diagonal]`. Conclude with `fun i => Finset.prod_ne_zero_iff.mp hdety i (Finset.mem_univ i)`. Establish `hgen : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `K) P, ∃ w : 𝓞 K, ∃ t : 𝓞 F, t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧ w * s = algebraMap (𝓞 F) (𝓞 K) t := by`.

Introduce `s hs`. Proceed by induction on `hs using Submonoid.closure_induction with`. Consider the case `mem s hs`. Establish `hfix : conjO K (conjO K s * s) = conjO K s * s`. Rewrite using `[map_mul, hconj_conj, mul_comm]`.

Take `⟨t, ht⟩` from `(conjO_eq_iff_mem_range hF _).mp hfix`. Use `⟨conjO K s, t, ?_, ht.symm⟩` and prove the remaining obligations. Use `show algebraMap (𝓞 F) (𝓞 K) t ∉ P`. Rewrite using `[ht]`. Introduce `h0`.

Break down `hP.isPrime.mem_or_mem h0 with h1 | h1` into its components or cases. Conclude with `hs.2 (conjO K s) (algebraMap_conjO s) h1`. Conclude with `hs.1 h1`. Consider the case `one`. Use `⟨1, 1, ?_, by rw [one_mul, map_one]⟩` and prove the remaining obligations.

Use `show algebraMap (𝓞 F) (𝓞 K) 1 ∉ P`. Rewrite using `[map_one]`. Conclude with `fun h0 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h0)`. Consider the case `mul x y _ _ hx hy`. Take `⟨wx, tx, htx, hx⟩` from `hx`.

Take `⟨wy, ty, hty, hy⟩` from `hy`. Use `⟨wx * wy, tx * ty, ?_, ?_⟩` and prove the remaining obligations. Use `show algebraMap (𝓞 F) (𝓞 K) (tx * ty) ∉ P`. Rewrite using `[map_mul]`. Conclude with `fun h0 => (hP.isPrime.mem_or_mem h0).elim htx hty`.

Rewrite using `[map_mul, ← hx, ← hy]`. Expand and normalize the polynomial expressions, which then agree. Establish `hclaim : ∀ c ∈ locRing P, star c = c → ∃ t : 𝓞 F, t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧ ∃ a : 𝓞 F, algebraMap F K (a : F) = (algebraMap F K (t : F)) ^ 2 * c`. Introduce `c hc hcs`. Take `⟨s, hs, hsc⟩` from `(Formalism.HermitianLatticesTheory.locDual_mem_locR (K := K) P c).mp hc`.

Take `⟨r, hr⟩` from `Submodule.mem_one.mp hsc`. Take `⟨w, t, ht, hwt⟩` from `hgen s hs`. Establish `e1 : algebraMap F K (t : F) * c = algebraMap (𝓞 K) K (w * r)`. Rewrite using `[← hcomp, ← hwt, map_mul, map_mul, hr, mul_assoc]`. Establish `hfixt : star (algebraMap F K (t : F)) = algebraMap F K (t : F)` using `(hF _).mpr ⟨_, rfl⟩`.

Establish `hfix : conjO K (w * r) = w * r` using `inj (by rw [algebraMap_conjO, ← e1, star_mul', hfixt, hcs])`. Take `⟨a0, ha0⟩` from `(conjO_eq_iff_mem_range hF _).mp hfix`. Use `⟨t, ht, t * a0, ?_⟩` and prove the remaining obligations. Establish `e2 : algebraMap F K (a0 : F) = algebraMap F K (t : F) * c`. Rewrite using `[← hcomp, ha0, ← e1]`.

Use `show algebraMap F K ((t : F) * (a0 : F)) = _`. Rewrite using `[map_mul, e2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hyS : ∀ i, h (y i) (y i) ∈ locRing P` using `fun i => int_spanS hS hxS (y i) (by rw [← hys]; exact mem_spanS y i) (y i) (by rw [← hys]; exact mem_spanS y i)`. Establish `hyfix : ∀ i, star (h (y i) (y i)) = h (y i) (y i)` using `fun i => hs.eq (y i) (y i)`.

Use `choose t ht a ha using fun i => hclaim _ (hyS i) (hyfix i)`. Establish `hτ0 : ∀ i, algebraMap F K (t i : F) ≠ 0`. Introduce `i h0`. Apply `ht i` to reduce the goal to its premises. Establish `h1 : (t i : F) = 0` using `(algebraMap F K).injective (by rw [h0, map_zero])`.

Establish `h2 : t i = 0` using `by exact_mod_cast h1`. Rewrite using `[h2]`. Conclude with `Submodule.zero_mem _`. Establish `hτfix : ∀ i, star (algebraMap F K (t i : F)) = algebraMap F K (t i : F)` using `fun i => (hF _).mpr ⟨_, rfl⟩`. Establish `hτS : ∀ i, algebraMap F K (t i : F) ∈ locRing P` using `fun i => by`.

Rewrite using `[← hcomp]`. Conclude with `hint _`. Establish `hτinv : ∀ i, (algebraMap F K (t i : F))⁻¹ ∈ locRing P`. Introduce `i`. Express the relevant statement in the definitionally equal form `_ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P`.

Rewrite using `[Formalism.HermitianLatticesTheory.locDual_mem_locR]`. Use `⟨algebraMap (𝓞 F) (𝓞 K) (t i), Submonoid.subset_closure ⟨ht i, fun t' ht' => ?_⟩, Submodule.mem_one.mpr ⟨1, ?_⟩⟩` and prove the remaining obligations. Establish `e : t' = algebraMap (𝓞 F) (𝓞 K) (t i)` using `inj (by rw [ht', hcomp, hτfix])`. Rewrite using `[e]`. Conclude with `ht i`.

Rewrite using `[map_one, hcomp, mul_inv_cancel₀ (hτ0 i)]`. Take `⟨b, hb⟩ : ∃ b : Fin (finrank K X) → V, ∀ i, b i = algebraMap F K (t i : F) • y i` from `⟨_, fun _ => rfl⟩`. Establish `hyX : ∀ i, y i ∈ X` using `fun i => spanS_le_of (S := locRing P) (x := x) (fun j => by rw [← hsp]; exact Submodule.subset_span ⟨j, rfl⟩) (y i) (by rw [← hys]; exact mem_spanS y i)`. Establish `hbS : spanS (locRing P) b = spanS (locRing P) y`. Apply `le_antisymm` to reduce the goal to its premises.

Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[hb i]`. Conclude with `smul_mem_spanS (hτS i) (mem_spanS y i)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[show y i = (algebraMap F K (t i : F))⁻¹ • b i by rw [hb i, inv_smul_smul₀ (hτ0 i)]]`. Conclude with `smul_mem_spanS (hτinv i) (mem_spanS b i)`. Use `⟨b, a, fun i => ?_, ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hb i]`.

Conclude with `X.smul_mem _ (hyX i)`. Rewrite using `[← hloc]`. Use extensionality with `v`. Rewrite using `[mem_locF_span_iff hK hF hP b v, mem_locF_span_iff hK hF hP x v, hbS, hys]`. Rewrite using `[hb i, hb j]`.

Simplify using `only [map_smulₛₗ, LinearMap.smul_apply, map_smul, hyo i j hij, smul_zero]`. Rewrite using `[hb i, ha i, map_smulₛₗ h, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul, starRingEnd_apply, hτfix]`. Expand and normalize the polynomial expressions, which then agree. Introduce `h0`. Establish `h1` using `ha i`.

Rewrite `h1` using `[h0]`. Establish `h2 : (algebraMap F K (t i : F)) ^ 2 * h (y i) (y i) = 0`. Rewrite using `[← h1]`. Simplify using the standard rewrite rules. Conclude with `mul_ne_zero (pow_ne_zero 2 (hτ0 i)) (hyy i) h2`.
-/
theorem jordan_exists (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (X : Submodule K V) (L : Submodule (𝓞 K) V) (hnd : Cnt.NondegOn h X)
    (hL : Cnt.IsLatIn X L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F))
    (h𝔭 : 𝔭.IsMaximal) : ∃ b a, Cnt.IsJordanIn h X L 𝔭 b a := by
  have inj := IsFractionRing.injective (𝓞 K) K
  have hcomp : ∀ t : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) :=
    fun t => rfl
  have hconj_conj : ∀ a : 𝓞 K, conjO K (conjO K a) = a := fun a =>
    inj (by rw [algebraMap_conjO, algebraMap_conjO, star_star])
  obtain ⟨P, hP, rfl⟩ := exists_over (K := K) 𝔭 h𝔭
  obtain ⟨π, hπ, hfin⟩ := exists_unif_fin hF hP
  have hS := isHermSemilocal_locRing hK hP
  obtain ⟨x, hxL, hli, hsp, hloc⟩ := exists_basis_in hL h𝔭
  have hdet0 : (U0.gram h x).det ≠ 0 := det_gram_ne_zero hnd hli hsp
  obtain ⟨N, hN⟩ := hfin _ hdet0
  have hint : ∀ r : 𝓞 K, algebraMap (𝓞 K) K r ∈ locRing P := by
    intro r
    change _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, Submodule.mem_one.mpr ⟨r, by rw [map_one, one_mul]⟩⟩
  have hxS : ∀ i j, h (x i) (x j) ∈ locRing P := by
    intro i j
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hLi _ (hxL i) _ (hxL j))
    rw [← hr]
    exact hint r
  obtain ⟨y, hyo, hys⟩ := exists_orth_gen hS hπ _ N h hs x hxS hN
  have hxy : ∀ i, x i ∈ spanS (locRing P) y := fun i => by rw [hys]; exact mem_spanS x i
  obtain ⟨c, -, hc⟩ := gram_det_of_le (h := h) hS hxy
  have hdety : (U0.gram h y).det ≠ 0 := fun h0 => hdet0 (by rw [hc, h0, mul_zero])
  have hdiag : U0.gram h y = Matrix.diagonal (fun i => h (y i) (y i)) := by
    ext i j
    show h (y i) (y j) = Matrix.diagonal (fun i => h (y i) (y i)) i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hyo i j hij
  have hyy : ∀ i, h (y i) (y i) ≠ 0 := by
    rw [hdiag, Matrix.det_diagonal] at hdety
    exact fun i => Finset.prod_ne_zero_iff.mp hdety i (Finset.mem_univ i)

  have hgen : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, ∃ w : 𝓞 K, ∃ t : 𝓞 F,
      t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧ w * s = algebraMap (𝓞 F) (𝓞 K) t := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      have hfix : conjO K (conjO K s * s) = conjO K s * s := by
        rw [map_mul, hconj_conj, mul_comm]
      obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF _).mp hfix
      refine ⟨conjO K s, t, ?_, ht.symm⟩
      show algebraMap (𝓞 F) (𝓞 K) t ∉ P
      rw [ht]
      intro h0
      rcases hP.isPrime.mem_or_mem h0 with h1 | h1
      · exact hs.2 (conjO K s) (algebraMap_conjO s) h1
      · exact hs.1 h1
    | one =>
      refine ⟨1, 1, ?_, by rw [one_mul, map_one]⟩
      show algebraMap (𝓞 F) (𝓞 K) 1 ∉ P
      rw [map_one]
      exact fun h0 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h0)
    | mul x y _ _ hx hy =>
      obtain ⟨wx, tx, htx, hx⟩ := hx
      obtain ⟨wy, ty, hty, hy⟩ := hy
      refine ⟨wx * wy, tx * ty, ?_, ?_⟩
      · show algebraMap (𝓞 F) (𝓞 K) (tx * ty) ∉ P
        rw [map_mul]
        exact fun h0 => (hP.isPrime.mem_or_mem h0).elim htx hty
      · rw [map_mul, ← hx, ← hy]
        ring
  have hclaim : ∀ c ∈ locRing P, star c = c → ∃ t : 𝓞 F, t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧
      ∃ a : 𝓞 F, algebraMap F K (a : F) = (algebraMap F K (t : F)) ^ 2 * c := by
    intro c hc hcs
    obtain ⟨s, hs, hsc⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR (K := K) P c).mp hc
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hsc
    obtain ⟨w, t, ht, hwt⟩ := hgen s hs
    have e1 : algebraMap F K (t : F) * c = algebraMap (𝓞 K) K (w * r) := by
      rw [← hcomp, ← hwt, map_mul, map_mul, hr, mul_assoc]
    have hfixt : star (algebraMap F K (t : F)) = algebraMap F K (t : F) := (hF _).mpr ⟨_, rfl⟩
    have hfix : conjO K (w * r) = w * r :=
      inj (by rw [algebraMap_conjO, ← e1, star_mul', hfixt, hcs])
    obtain ⟨a0, ha0⟩ := (conjO_eq_iff_mem_range hF _).mp hfix
    refine ⟨t, ht, t * a0, ?_⟩
    have e2 : algebraMap F K (a0 : F) = algebraMap F K (t : F) * c := by
      rw [← hcomp, ha0, ← e1]
    show algebraMap F K ((t : F) * (a0 : F)) = _
    rw [map_mul, e2]
    ring
  have hyS : ∀ i, h (y i) (y i) ∈ locRing P := fun i =>
    int_spanS hS hxS (y i) (by rw [← hys]; exact mem_spanS y i) (y i)
      (by rw [← hys]; exact mem_spanS y i)
  have hyfix : ∀ i, star (h (y i) (y i)) = h (y i) (y i) := fun i => hs.eq (y i) (y i)
  choose t ht a ha using fun i => hclaim _ (hyS i) (hyfix i)
  have hτ0 : ∀ i, algebraMap F K (t i : F) ≠ 0 := by
    intro i h0
    apply ht i
    have h1 : (t i : F) = 0 := (algebraMap F K).injective (by rw [h0, map_zero])
    have h2 : t i = 0 := by exact_mod_cast h1
    rw [h2]
    exact Submodule.zero_mem _
  have hτfix : ∀ i, star (algebraMap F K (t i : F)) = algebraMap F K (t i : F) :=
    fun i => (hF _).mpr ⟨_, rfl⟩
  have hτS : ∀ i, algebraMap F K (t i : F) ∈ locRing P := fun i => by
    rw [← hcomp]
    exact hint _
  have hτinv : ∀ i, (algebraMap F K (t i : F))⁻¹ ∈ locRing P := by
    intro i
    change _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    refine ⟨algebraMap (𝓞 F) (𝓞 K) (t i), Submonoid.subset_closure ⟨ht i, fun t' ht' => ?_⟩,
      Submodule.mem_one.mpr ⟨1, ?_⟩⟩
    · have e : t' = algebraMap (𝓞 F) (𝓞 K) (t i) := inj (by rw [ht', hcomp, hτfix])
      rw [e]
      exact ht i
    · rw [map_one, hcomp, mul_inv_cancel₀ (hτ0 i)]
  obtain ⟨b, hb⟩ : ∃ b : Fin (finrank K X) → V, ∀ i, b i = algebraMap F K (t i : F) • y i :=
    ⟨_, fun _ => rfl⟩
  have hyX : ∀ i, y i ∈ X := fun i => spanS_le_of (S := locRing P) (x := x)
    (fun j => by rw [← hsp]; exact Submodule.subset_span ⟨j, rfl⟩) (y i)
    (by rw [← hys]; exact mem_spanS y i)
  have hbS : spanS (locRing P) b = spanS (locRing P) y := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [hb i]
      exact smul_mem_spanS (hτS i) (mem_spanS y i)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [show y i = (algebraMap F K (t i : F))⁻¹ • b i by rw [hb i, inv_smul_smul₀ (hτ0 i)]]
      exact smul_mem_spanS (hτinv i) (mem_spanS b i)
  refine ⟨b, a, fun i => ?_, ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hb i]
    exact X.smul_mem _ (hyX i)
  · rw [← hloc]
    ext v
    rw [mem_locF_span_iff hK hF hP b v, mem_locF_span_iff hK hF hP x v, hbS, hys]
  · rw [hb i, hb j]
    simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, hyo i j hij, smul_zero]
  · rw [hb i, ha i, map_smulₛₗ h, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, hτfix]
    ring
  · intro h0
    have h1 := ha i
    rw [h0] at h1
    have h2 : (algebraMap F K (t i : F)) ^ 2 * h (y i) (y i) = 0 := by
      rw [← h1]
      simp
    exact mul_ne_zero (pow_ne_zero 2 (hτ0 i)) (hyy i) h2

end Formalism.L2.SG.Pf.G1
