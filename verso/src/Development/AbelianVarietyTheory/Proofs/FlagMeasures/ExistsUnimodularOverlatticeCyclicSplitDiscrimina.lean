import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.SplitOver

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e⟩`. Take `⟨x, hx⟩` from `Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))`. Establish `key : ∀ r : R, e (Submodule.Quotient.mk (r • x)) = Submodule.Quotient.mk r`. Introduce `r`.

Rewrite using `[Submodule.Quotient.mk_smul, map_smul, hx, e.apply_symm_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]`. Use `⟨x, x.2, fun y hy => ?_, fun r => ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `Submodule.Quotient.mk_surjective I (e (Submodule.Quotient.mk ⟨y, hy⟩))`. Rewrite `hr` using `[← key, e.injective.eq_iff, eq_comm, Submodule.Quotient.eq]`. Conclude with `⟨r, hr⟩`.

Rewrite using `[← Submodule.Quotient.mk_eq_zero I, ← key, EmbeddingLike.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero]`. Both sides reduce to the same expression. Introduce and unpack `⟨x, hx, h1, h2⟩`. Set `f : R →ₗ[R] (↥A ⧸ B.comap A.subtype)` to `(B.comap A.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton R A ⟨x, hx⟩`. Establish `hk : I = LinearMap.ker f`.

Use extensionality with `r`. Rewrite using `[← h2, LinearMap.mem_ker]`. Conclude with `(Submodule.Quotient.mk_eq_zero (B.comap A.subtype) (x := r • (⟨x, hx⟩ : A))).symm`. Establish `hsurj : Function.Surjective f`. Introduce `z`.

Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Take `⟨r, hr⟩` from `h1 y y.2`. Use `⟨r, Eq.symm ?_⟩` and prove the remaining obligations. Conclude with `(Submodule.Quotient.eq (B.comap A.subtype) (x := y) (y := r • (⟨x, hx⟩ : A))).2 hr`. Conclude with `⟨((Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hsurj)).symm⟩`.
-/
theorem cyc_iff {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (A B : Submodule R W) (I : Ideal R) :
    Nonempty ((↥A ⧸ B.comap A.subtype) ≃ₗ[R] (R ⧸ I)) ↔
      ∃ x ∈ A, (∀ y ∈ A, ∃ r : R, y - r • x ∈ B) ∧ ∀ r : R, r • x ∈ B ↔ r ∈ I := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
    have key : ∀ r : R, e (Submodule.Quotient.mk (r • x)) = Submodule.Quotient.mk r := by
      intro r
      rw [Submodule.Quotient.mk_smul, map_smul, hx, e.apply_symm_apply, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, mul_one]
    refine ⟨x, x.2, fun y hy => ?_, fun r => ?_⟩
    · obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective I (e (Submodule.Quotient.mk ⟨y, hy⟩))
      rw [← key, e.injective.eq_iff, eq_comm, Submodule.Quotient.eq] at hr
      exact ⟨r, hr⟩
    · rw [← Submodule.Quotient.mk_eq_zero I, ← key, EmbeddingLike.map_eq_zero_iff,
        Submodule.Quotient.mk_eq_zero]
      rfl
  · rintro ⟨x, hx, h1, h2⟩
    let f : R →ₗ[R] (↥A ⧸ B.comap A.subtype) :=
      (B.comap A.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton R A ⟨x, hx⟩
    have hk : I = LinearMap.ker f := by
      ext r
      rw [← h2, LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero (B.comap A.subtype) (x := r • (⟨x, hx⟩ : A))).symm
    have hsurj : Function.Surjective f := by
      intro z
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨r, hr⟩ := h1 y y.2
      refine ⟨r, Eq.symm ?_⟩
      exact (Submodule.Quotient.eq (B.comap A.subtype) (x := y) (y := r • (⟨x, hx⟩ : A))).2 hr
    exact ⟨((Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hsurj)).symm⟩

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

noncomputable abbrev cj : 𝓞 K →+* 𝓞 K := locBasic_sigma (genusCovol_hinj (K := K)) star_algebraMap_ringOfIntegers_mem_range

/- English proof (translation)
The claim follows from `genusCovol_hinj (by rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])`.
-/
theorem cj_cj (r : 𝓞 K) : cj (cj r) = r := genusCovol_hinj (by
  rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])

/- English proof (translation)
Rewrite using `[locBasic_conj_eq genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, Ideal.mem_comap]`.
-/
theorem mem_conj (P : Ideal (𝓞 K)) (r : 𝓞 K) : r ∈ conjIdeal (K := K) P ↔ cj r ∈ P := by
  rw [locBasic_conj_eq genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, Ideal.mem_comap]

omit [FiniteDimensional K V] in
/- English proof (translation)
Rewrite using `[genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right]`. Conclude with `congrArg (fun t => algebraMap (𝓞 K) K t * h v w) (cj_cj r).symm`.
-/
theorem adj (h : V →ₗ⋆[K] V →ₗ[K] K) (r : 𝓞 K) (v w : V) : h v (r • w) = h (cj r • v) w := by
  rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right]
  exact congrArg (fun t => algebraMap (𝓞 K) K t * h v w) (cj_cj r).symm

/- English proof (translation)
Take `⟨r, hr⟩` from `h1 y hy`. Establish `: s • y = s • (y - r • x) + (s * r) • x` using `by rw [smul_sub, mul_smul, sub_add_cancel]`. Rewrite using `[this]`. Conclude with `B.add_mem (B.smul_mem s hr) ((h2 _).2 (I.mul_mem_right r hs))`.
-/
theorem smul_mem_of_gen {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {A B : Submodule R W}
    {I : Ideal R} {x : W} (h1 : ∀ y ∈ A, ∃ r : R, y - r • x ∈ B) (h2 : ∀ r : R, r • x ∈ B ↔ r ∈ I)
    {s : R} (hs : s ∈ I) {y : W} (hy : y ∈ A) : s • y ∈ B := by
  obtain ⟨r, hr⟩ := h1 y hy
  have : s • y = s • (y - r • x) + (s * r) • x := by rw [smul_sub, mul_smul, sub_add_cancel]
  rw [this]
  exact B.add_mem (B.smul_mem s hr) ((h2 _).2 (I.mul_mem_right r hs))

variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn

/- English proof (translation)
Establish `dl` using `dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range`. Take `⟨an, -, -, hint, huni⟩` from `dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range`. Take `⟨p, hp, q, hq, hpq⟩` from `Ideal.isCoprime_iff_exists.1 hc`. Take `⟨x, hx, g1, g2⟩` from `(cyc_iff _ _ _).1 e`. Establish `hLD` using `(hint L).1 hL.2`.

Establish `hDD` using `(dl L hL.1).2.1`. Establish `split : ∀ y : V, p • y + q • y = y` using `fun y => by rw [← add_smul, hpq, one_smul]`. Establish `kill : ∀ a ∈ P, ∀ b ∈ conjIdeal (K` using `K) P, ∀ y ∈ dual h L, a • b • y ∈ L := fun a ha b hb y hy => by`. Rewrite using `[← mul_smul]`. Conclude with `smul_mem_of_gen g1 g2 (Ideal.mul_mem_mul ha hb) hy`.

Set `M : Submodule (𝓞 K) V` to `dual h L ⊓ L.comap (LinearMap.lsmul (𝓞 K) V p)`. Establish `mem : ∀ y, y ∈ M ↔ y ∈ dual h L ∧ p • y ∈ L` using `fun y => Iff.rfl`. Establish `hLM : L ≤ M` using `fun y hy => (mem y).2 ⟨hLD hy, L.smul_mem p hy⟩`. Establish `hMD : M ≤ dual h L` using `inf_le_left`. Establish `hQ : ∀ b ∈ conjIdeal (K` using `K) P, ∀ y ∈ dual h L, b • y ∈ M := fun b hb y hy => (mem _).2 ⟨Submodule.smul_mem _ b hy, kill p hp b hb y hy⟩`.

Establish `hP : ∀ a ∈ P, ∀ y ∈ M, a • y ∈ L` using `fun a ha y hy => by`. Rewrite using `[← split y, smul_add]`. Conclude with `L.add_mem (L.smul_mem a ((mem y).1 hy).2) (kill a ha q hq y (hMD hy))`. Establish `hMu : IsUnimodular h M`. Use `(huni M).2 ⟨fun y hy y' hy' => ?_, fun y hy => (mem y).2 ⟨an _ _ hLM hy, ?_⟩⟩` and prove the remaining obligations.

Rewrite using `[← split y', map_add]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Use `((mem y').1 hy').2` as an intermediate fact. Rewrite `this` using `[← hDD, dualBasic_mem_dual]`. Conclude with `this y (hMD hy)`.

Rewrite using `[adj]`. Conclude with `(dualBasic_mem_dual h L y').1 (hMD hy') _ (hP _ ((mem_conj P q).1 hq) y hy)`. Rewrite using `[← hDD, dualBasic_mem_dual]`. Introduce `d hd`. Rewrite using `[adj]`.

Conclude with `(dualBasic_mem_dual h M y).1 hy _ (hQ _ ((mem_conj P _).2 (by rwa [cj_cj])) d hd)`. Use `⟨M, ⟨DiscOrder.lattice_between hL.1 (dl L hL.1).1 hLM hMD, hMu, hLM, (cyc_iff _ _ _).2 ⟨q • x, hQ q hq x hx, fun y hy => ?_, fun r => ⟨fun hr => ?_, fun hr => kill r hr q hq x hx⟩⟩⟩, ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `g1 y (hMD hy)`. Use `⟨r, ?_⟩` and prove the remaining obligations. Establish `: y - r • q • x = p • y + q • (y - r • x)`.

Rewrite using `[smul_sub, smul_comm q r x, ← add_sub_assoc, split]`. Rewrite using `[this]`. Conclude with `L.add_mem ((mem y).1 hy).2 (L.smul_mem q hr)`. Rewrite `hr` using `[← mul_smul, g2]`. Establish `: r = r * p + r * q` using `by rw [← mul_add, hpq, mul_one]`.

Rewrite using `[this]`. Conclude with `P.add_mem (P.mul_mem_left r hp) (Ideal.mul_le_left hr)`. Introduce and unpack `N ⟨-, hNu, hLN, eN⟩`. Take `⟨m, -, k1, k2⟩` from `(cyc_iff _ _ _).1 eN`. Establish `hNu' : dual h N = N` using `hNu`.

Establish `hMu' : dual h M = M` using `hMu`. Establish `hNM : N ≤ M` using `fun y hy => (mem y).2 ⟨an _ _ hLN (hNu'.symm ▸ hy), smul_mem_of_gen k1 k2 hp hy⟩`. Use `le_antisymm hNM ?_` and prove the remaining obligations. Rewrite using `[← hNu', ← hMu']`. Conclude with `an _ _ hNM`.
-/
theorem exists_unique_over (P : Ideal (𝓞 K)) (hc : IsCoprime P (conjIdeal (K := K) P))
    (L : Submodule (𝓞 K) V) (hL : IsIntLat h L)
    (e : Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P * conjIdeal (K := K) P))) :
    ∃! M : Submodule (𝓞 K) V, Submodule.IsLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧
      Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) := by
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨an, -, -, hint, huni⟩ := dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨x, hx, g1, g2⟩ := (cyc_iff _ _ _).1 e
  have hLD := (hint L).1 hL.2
  have hDD := (dl L hL.1).2.1
  have split : ∀ y : V, p • y + q • y = y := fun y => by rw [← add_smul, hpq, one_smul]
  have kill : ∀ a ∈ P, ∀ b ∈ conjIdeal (K := K) P, ∀ y ∈ dual h L, a • b • y ∈ L := fun a ha b hb y hy => by
    rw [← mul_smul]
    exact smul_mem_of_gen g1 g2 (Ideal.mul_mem_mul ha hb) hy
  let M : Submodule (𝓞 K) V := dual h L ⊓ L.comap (LinearMap.lsmul (𝓞 K) V p)
  have mem : ∀ y, y ∈ M ↔ y ∈ dual h L ∧ p • y ∈ L := fun y => Iff.rfl
  have hLM : L ≤ M := fun y hy => (mem y).2 ⟨hLD hy, L.smul_mem p hy⟩
  have hMD : M ≤ dual h L := inf_le_left
  have hQ : ∀ b ∈ conjIdeal (K := K) P, ∀ y ∈ dual h L, b • y ∈ M := fun b hb y hy =>
    (mem _).2 ⟨Submodule.smul_mem _ b hy, kill p hp b hb y hy⟩
  have hP : ∀ a ∈ P, ∀ y ∈ M, a • y ∈ L := fun a ha y hy => by
    rw [← split y, smul_add]
    exact L.add_mem (L.smul_mem a ((mem y).1 hy).2) (kill a ha q hq y (hMD hy))
  have hMu : IsUnimodular h M := by
    refine (huni M).2 ⟨fun y hy y' hy' => ?_, fun y hy => (mem y).2 ⟨an _ _ hLM hy, ?_⟩⟩
    · rw [← split y', map_add]
      refine Submodule.add_mem _ ?_ ?_
      · have := ((mem y').1 hy').2
        rw [← hDD, dualBasic_mem_dual] at this
        exact this y (hMD hy)
      · rw [adj]
        exact (dualBasic_mem_dual h L y').1 (hMD hy') _ (hP _ ((mem_conj P q).1 hq) y hy)
    · rw [← hDD, dualBasic_mem_dual]
      intro d hd
      rw [adj]
      exact (dualBasic_mem_dual h M y).1 hy _ (hQ _ ((mem_conj P _).2 (by rwa [cj_cj])) d hd)
  refine ⟨M, ⟨DiscOrder.lattice_between hL.1 (dl L hL.1).1 hLM hMD, hMu, hLM,
    (cyc_iff _ _ _).2 ⟨q • x, hQ q hq x hx, fun y hy => ?_, fun r => ⟨fun hr => ?_, fun hr => kill r hr q hq x hx⟩⟩⟩, ?_⟩
  · obtain ⟨r, hr⟩ := g1 y (hMD hy)
    refine ⟨r, ?_⟩
    have : y - r • q • x = p • y + q • (y - r • x) := by
      rw [smul_sub, smul_comm q r x, ← add_sub_assoc, split]
    rw [this]
    exact L.add_mem ((mem y).1 hy).2 (L.smul_mem q hr)
  · rw [← mul_smul, g2] at hr
    have : r = r * p + r * q := by rw [← mul_add, hpq, mul_one]
    rw [this]
    exact P.add_mem (P.mul_mem_left r hp) (Ideal.mul_le_left hr)
  · rintro N ⟨-, hNu, hLN, eN⟩
    obtain ⟨m, -, k1, k2⟩ := (cyc_iff _ _ _).1 eN
    have hNu' : dual h N = N := hNu
    have hMu' : dual h M = M := hMu
    have hNM : N ≤ M := fun y hy =>
      (mem y).2 ⟨an _ _ hLN (hNu'.symm ▸ hy), smul_mem_of_gen k1 k2 hp hy⟩
    refine le_antisymm hNM ?_
    rw [← hNu', ← hMu']
    exact an _ _ hNM

/- English proof (translation)
Establish `dl` using `dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range`. Take `⟨an, -, -, hint, huni⟩` from `dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range`. Take `⟨p, hp, q, hq, hpq⟩` from `Ideal.isCoprime_iff_exists.1 hc`. Take `⟨m, hm, k1, k2⟩` from `(cyc_iff _ _ _).1 e`. Take `⟨t, ht, ht0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP0`.

Establish `hMu' : dual h M = M` using `hMu`. Establish `hP : ∀ a ∈ P, ∀ y ∈ M, a • y ∈ L` using `fun a ha y hy => smul_mem_of_gen k1 k2 ha hy`. Establish `hL : Submodule.IsLattice K L`. Use `⟨hM.fg.of_le hLM, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hM.span_eq_top, Submodule.span_le]`.

Introduce `y hy`. Establish `hne : algebraMap (𝓞 K) K t ≠ 0` using `(map_ne_zero_iff _ genusCovol_hinj).2 ht0`. Establish `: y = (algebraMap (𝓞 K) K t)⁻¹ • (t • y)`. Rewrite using `[← algebraMap_smul K t y, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Rewrite using `[this]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (hP t ht y hy))`. Establish `hMD : M ≤ dual h L` using `hMu' ▸ an _ _ hLM`. Establish `hDD` using `(dl L hL).2.1`. Use `⟨⟨hL, (hint L).2 (hLM.trans hMD)⟩, ?_⟩` and prove the remaining obligations. Establish `test : ∀ d ∈ dual h L, h m d ∈ (1 : Submodule (𝓞 K) K) → d ∈ M`.

Introduce `d hd hmd`. Rewrite using `[← hMu', dualBasic_mem_dual]`. Introduce `y hy`. Take `⟨r, hr⟩` from `k1 y hy`. Establish `: h y d = h (y - r • m) d + h (r • m) d` using `by simp`.

Rewrite using `[this]`. Use `Submodule.add_mem _ ((dualBasic_mem_dual h L d).1 hd _ hr) ?_` and prove the remaining obligations. Rewrite using `[genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range]`. Conclude with `genusBasic_mem_one_mul _ hmd _`. Establish `hQ : ∀ b ∈ conjIdeal (K` using `K) P, ∀ d ∈ dual h L, b • d ∈ M := by`.

Introduce `b hb d hd`. Use `test _ (Submodule.smul_mem _ b hd) ?_` and prove the remaining obligations. Rewrite using `[adj]`. Conclude with `(dualBasic_mem_dual h L d).1 hd _ ((k2 _).2 ((mem_conj P b).1 hb))`. Establish `hQ' : ∀ b, (∀ d ∈ dual h L, b • d ∈ M) → b ∈ conjIdeal (K` using `K) P := by`.

Introduce `b hb`. Rewrite using `[mem_conj, ← k2, ← hDD, dualBasic_mem_dual]`. Introduce `d hd`. Rewrite using `[adj, cj_cj]`. Conclude with `(dualBasic_mem_dual h M m).1 (hMu'.symm ▸ hm) _ (hb d hd)`.

Choose the witnesses or unpack the hypotheses as in `⟨d₀, hd₀, gen⟩ : ∃ d₀ ∈ dual h L, ∀ d ∈ dual h L, ∃ v : 𝓞 K, d - v • d₀ ∈ M := by`. Establish `hs0 : cj t ≠ 0` using `fun e => ht0 (by rw [← cj_cj t, e, map_zero])`. Establish `hne : algebraMap (𝓞 K) K (cj t) ≠ 0` using `(map_ne_zero_iff _ genusCovol_hinj).2 hs0`. Set `φ : V →ₗ[𝓞 K] K` to `(h (t • m)).restrictScalars (𝓞 K)`. Establish `hφ : ∀ d, φ d = algebraMap (𝓞 K) K (cj t) * h m d` using `fun d => genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range h t m d`.

Set `J : Ideal (𝓞 K)` to `((dual h L).map φ).comap (Algebra.linearMap (𝓞 K) K)`. Take `⟨a, ha⟩` from `IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {cj t}) (J := Ideal.span {cj t} ⊔ J) le_sup_left (by simpa using hs0)`. Establish `ha1 : a ∈ Ideal.span {cj t} ⊔ J` using `ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)`. Take `⟨b, hb, c₀, hc₀, rfl⟩` from `Submodule.mem_sup.1 ha1`. Take `⟨u, rfl⟩` from `Ideal.mem_span_singleton'.1 hb`.

Take `⟨d₀, hd₀, e₀⟩` from `Submodule.mem_map.1 (Submodule.mem_comap.1 hc₀)`. Use `⟨d₀, hd₀, fun d hd => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Submodule.mem_one.1 ((dualBasic_mem_dual h L d).1 hd _ (hP t ht m hm))`. Establish `hcJ : c ∈ Ideal.span {cj t} ⊔ J` using `Ideal.mem_sup_right (Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨d, hd, hc.symm⟩))`. Rewrite `hcJ` using `[← ha]`.

Take `⟨b, hb, b', hb', e1⟩` from `Submodule.mem_sup.1 hcJ`. Take `⟨x, rfl⟩` from `Ideal.mem_span_singleton'.1 hb`. Take `⟨v, rfl⟩` from `Ideal.mem_span_singleton'.1 hb'`. Use `⟨v, test _ (Submodule.sub_mem _ hd (Submodule.smul_mem _ v hd₀)) (Submodule.mem_one.2 ⟨x + v * u, mul_left_cancel₀ hne ?_⟩)⟩` and prove the remaining obligations. Establish `e2 : φ d = algebraMap (𝓞 K) K c` using `hc.symm`.

Establish `e3 : φ d₀ = algebraMap (𝓞 K) K c₀` using `e₀`. Rewrite using `[← hφ, map_sub, map_smul, e2, e3, ← e1, Algebra.smul_def]`. Simplify using `only [map_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `gen' : ∀ r, r • d₀ ∈ M ↔ r ∈ conjIdeal (K` using `K) P := by`.

Use `fun r => ⟨fun hr => hQ' r fun d hd => ?_, fun hr => hQ r hr d₀ hd₀⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `gen d hd`. Establish `: r • d = r • (d - v • d₀) + v • r • d₀` using `by rw [smul_sub, smul_comm r v, sub_add_cancel]`. Rewrite using `[this]`. Conclude with `M.add_mem (M.smul_mem r hv) (M.smul_mem v hr)`.

Establish `hq' : q = 1 - p` using `by rw [← hpq]; ring`. Use `(cyc_iff _ _ _).2 ⟨q • m + p • d₀, Submodule.add_mem _ (Submodule.smul_mem _ _ (hMD hm)) (Submodule.smul_mem _ _ hd₀), fun d hd => ?_, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩` and prove the remaining obligations. Take `⟨v, hv⟩` from `gen d hd`. Take `⟨u, hu⟩` from `k1 _ (M.add_mem hv (M.smul_mem v (hQ q hq d₀ hd₀)))`. Use `⟨v * p + u * q, ?_⟩` and prove the remaining obligations.

Establish `: d - (v * p + u * q) • (q • m + p • d₀) = (d - v • d₀ + v • q • d₀ - u • m) + p • ((u * (2 - p) - v * q) • m) + p • ((v - u) • q • d₀)`. Rewrite using `[hq']`. Use `module`. Rewrite using `[this]`. Conclude with `L.add_mem (L.add_mem hu (hP p hp _ (M.smul_mem _ hm))) (hP p hp _ (M.smul_mem _ (hQ q hq d₀ hd₀)))`.

Establish `e1 : r = r * p + r * q` using `by rw [← mul_add, hpq, mul_one]`. Establish `h1 : r ∈ conjIdeal (K` using `K) P := by`. Establish `: (r * p) • d₀ = r • (q • m + p • d₀) - (r * q) • m` using `by module`. Establish `h2 : (r * p) • d₀ ∈ M` using `this ▸ M.sub_mem (hLM hr) (M.smul_mem _ hm)`. Rewrite using `[e1]`.

Conclude with `Ideal.add_mem _ ((gen' _).1 h2) (Ideal.mul_mem_left _ r hq)`. Establish `h2 : r ∈ P`. Establish `: (r * q) • m = r • (q • m + p • d₀) - p • r • d₀` using `by module`. Establish `h3 : (r * q) • m ∈ L` using `this ▸ L.sub_mem hr (hP p hp _ (hQ r h1 d₀ hd₀))`. Rewrite using `[e1]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_left _ r hp) ((k2 _).1 h3)`. Rewrite using `[e1]`. Conclude with `Ideal.add_mem _ (mul_comm r p ▸ Ideal.mul_mem_mul hp h1) (Ideal.mul_mem_mul h2 hq)`. Establish `: r • (q • m + p • d₀) = r • q • m + p • r • d₀` using `by module`. Rewrite using `[this]`.

Conclude with `L.add_mem (hP r (Ideal.mul_le_left hr) _ (M.smul_mem q hm)) (hP p hp _ (hQ r (Ideal.mul_le_right hr) d₀ hd₀))`.
-/
theorem disc_of_over (P : Ideal (𝓞 K)) (hP0 : P ≠ ⊥) (hc : IsCoprime P (conjIdeal (K := K) P))
    (M L : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) (hMu : IsUnimodular h M) (hLM : L ≤ M)
    (e : Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P))) :
    IsIntLat h L ∧
      Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P * conjIdeal (K := K) P)) := by
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨an, -, -, hint, huni⟩ := dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨m, hm, k1, k2⟩ := (cyc_iff _ _ _).1 e
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hMu' : dual h M = M := hMu
  have hP : ∀ a ∈ P, ∀ y ∈ M, a • y ∈ L := fun a ha y hy => smul_mem_of_gen k1 k2 ha hy
  have hL : Submodule.IsLattice K L := by
    refine ⟨hM.fg.of_le hLM, ?_⟩
    rw [eq_top_iff, ← hM.span_eq_top, Submodule.span_le]
    intro y hy
    have hne : algebraMap (𝓞 K) K t ≠ 0 := (map_ne_zero_iff _ genusCovol_hinj).2 ht0
    have : y = (algebraMap (𝓞 K) K t)⁻¹ • (t • y) := by
      rw [← algebraMap_smul K t y, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hP t ht y hy))
  have hMD : M ≤ dual h L := hMu' ▸ an _ _ hLM
  have hDD := (dl L hL).2.1
  refine ⟨⟨hL, (hint L).2 (hLM.trans hMD)⟩, ?_⟩
  have test : ∀ d ∈ dual h L, h m d ∈ (1 : Submodule (𝓞 K) K) → d ∈ M := by
    intro d hd hmd
    rw [← hMu', dualBasic_mem_dual]
    intro y hy
    obtain ⟨r, hr⟩ := k1 y hy
    have : h y d = h (y - r • m) d + h (r • m) d := by simp
    rw [this]
    refine Submodule.add_mem _ ((dualBasic_mem_dual h L d).1 hd _ hr) ?_
    rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range]
    exact genusBasic_mem_one_mul _ hmd _
  have hQ : ∀ b ∈ conjIdeal (K := K) P, ∀ d ∈ dual h L, b • d ∈ M := by
    intro b hb d hd
    refine test _ (Submodule.smul_mem _ b hd) ?_
    rw [adj]
    exact (dualBasic_mem_dual h L d).1 hd _ ((k2 _).2 ((mem_conj P b).1 hb))
  have hQ' : ∀ b, (∀ d ∈ dual h L, b • d ∈ M) → b ∈ conjIdeal (K := K) P := by
    intro b hb
    rw [mem_conj, ← k2, ← hDD, dualBasic_mem_dual]
    intro d hd
    rw [adj, cj_cj]
    exact (dualBasic_mem_dual h M m).1 (hMu'.symm ▸ hm) _ (hb d hd)

  obtain ⟨d₀, hd₀, gen⟩ : ∃ d₀ ∈ dual h L, ∀ d ∈ dual h L, ∃ v : 𝓞 K, d - v • d₀ ∈ M := by
    have hs0 : cj t ≠ 0 := fun e => ht0 (by rw [← cj_cj t, e, map_zero])
    have hne : algebraMap (𝓞 K) K (cj t) ≠ 0 := (map_ne_zero_iff _ genusCovol_hinj).2 hs0
    let φ : V →ₗ[𝓞 K] K := (h (t • m)).restrictScalars (𝓞 K)
    have hφ : ∀ d, φ d = algebraMap (𝓞 K) K (cj t) * h m d := fun d =>
      genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range h t m d
    let J : Ideal (𝓞 K) := ((dual h L).map φ).comap (Algebra.linearMap (𝓞 K) K)
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {cj t})
      (J := Ideal.span {cj t} ⊔ J) le_sup_left (by simpa using hs0)
    have ha1 : a ∈ Ideal.span {cj t} ⊔ J := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    obtain ⟨b, hb, c₀, hc₀, rfl⟩ := Submodule.mem_sup.1 ha1
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨d₀, hd₀, e₀⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hc₀)
    refine ⟨d₀, hd₀, fun d hd => ?_⟩
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 ((dualBasic_mem_dual h L d).1 hd _ (hP t ht m hm))
    have hcJ : c ∈ Ideal.span {cj t} ⊔ J :=
      Ideal.mem_sup_right (Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨d, hd, hc.symm⟩))
    rw [← ha] at hcJ
    obtain ⟨b, hb, b', hb', e1⟩ := Submodule.mem_sup.1 hcJ
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hb'
    refine ⟨v, test _ (Submodule.sub_mem _ hd (Submodule.smul_mem _ v hd₀))
      (Submodule.mem_one.2 ⟨x + v * u, mul_left_cancel₀ hne ?_⟩)⟩
    have e2 : φ d = algebraMap (𝓞 K) K c := hc.symm
    have e3 : φ d₀ = algebraMap (𝓞 K) K c₀ := e₀
    rw [← hφ, map_sub, map_smul, e2, e3, ← e1, Algebra.smul_def]
    simp only [map_add, map_mul]
    ring
  have gen' : ∀ r, r • d₀ ∈ M ↔ r ∈ conjIdeal (K := K) P := by
    refine fun r => ⟨fun hr => hQ' r fun d hd => ?_, fun hr => hQ r hr d₀ hd₀⟩
    obtain ⟨v, hv⟩ := gen d hd
    have : r • d = r • (d - v • d₀) + v • r • d₀ := by rw [smul_sub, smul_comm r v, sub_add_cancel]
    rw [this]
    exact M.add_mem (M.smul_mem r hv) (M.smul_mem v hr)
  have hq' : q = 1 - p := by rw [← hpq]; ring
  refine (cyc_iff _ _ _).2 ⟨q • m + p • d₀,
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hMD hm)) (Submodule.smul_mem _ _ hd₀), fun d hd => ?_,
    fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · obtain ⟨v, hv⟩ := gen d hd
    obtain ⟨u, hu⟩ := k1 _ (M.add_mem hv (M.smul_mem v (hQ q hq d₀ hd₀)))
    refine ⟨v * p + u * q, ?_⟩
    have : d - (v * p + u * q) • (q • m + p • d₀) = (d - v • d₀ + v • q • d₀ - u • m)
        + p • ((u * (2 - p) - v * q) • m) + p • ((v - u) • q • d₀) := by
      rw [hq']; module
    rw [this]
    exact L.add_mem (L.add_mem hu (hP p hp _ (M.smul_mem _ hm)))
      (hP p hp _ (M.smul_mem _ (hQ q hq d₀ hd₀)))
  · have e1 : r = r * p + r * q := by rw [← mul_add, hpq, mul_one]
    have h1 : r ∈ conjIdeal (K := K) P := by
      have : (r * p) • d₀ = r • (q • m + p • d₀) - (r * q) • m := by module
      have h2 : (r * p) • d₀ ∈ M := this ▸ M.sub_mem (hLM hr) (M.smul_mem _ hm)
      rw [e1]
      exact Ideal.add_mem _ ((gen' _).1 h2) (Ideal.mul_mem_left _ r hq)
    have h2 : r ∈ P := by
      have : (r * q) • m = r • (q • m + p • d₀) - p • r • d₀ := by module
      have h3 : (r * q) • m ∈ L := this ▸ L.sub_mem hr (hP p hp _ (hQ r h1 d₀ hd₀))
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ r hp) ((k2 _).1 h3)
    rw [e1]
    exact Ideal.add_mem _ (mul_comm r p ▸ Ideal.mul_mem_mul hp h1) (Ideal.mul_mem_mul h2 hq)
  · have : r • (q • m + p • d₀) = r • q • m + p • r • d₀ := by module
    rw [this]
    exact L.add_mem (hP r (Ideal.mul_le_left hr) _ (M.smul_mem q hm))
      (hP p hp _ (hQ r (Ideal.mul_le_right hr) d₀ hd₀))

end GlobalTheory.Mass.SplitOver

namespace GlobalTheory.Mass.SplitOver

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ h _ hs hn P hP0 hc`. Conclude with `⟨exists_unique_over h hs hn P hc, disc_of_over h hs hn P hP0 hc⟩`.
-/
theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (𝔓 : Ideal (𝓞 K)), 𝔓 ≠ ⊥ → IsCoprime 𝔓 (conjIdeal (K := K) 𝔓) → (∀ L : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓 * conjIdeal (K := K) 𝔓)) → ∃! M : Submodule (𝓞 K) V, Submodule.IsLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓))) ∧ ∀ M L : Submodule (𝓞 K) V, Submodule.IsLattice K M → IsUnimodular h M → L ≤ M → Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓)) → IsIntLat h L ∧ Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓 * conjIdeal (K := K) 𝔓)) := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hn P hP0 hc
  exact ⟨exists_unique_over h hs hn P hc, disc_of_over h hs hn P hP0 hc⟩

end GlobalTheory.Mass.SplitOver
