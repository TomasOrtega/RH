import Mathlib

open Matrix Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `: Fact (Irreducible p)` using `⟨hp⟩`. Set `L` to `AdjoinRoot p`. Set `M'` to `M.map (algebraMap K L)`. Establish `hM' : aeval M' q = 0`. Use `Polynomial.aeval_algHom_apply ((Algebra.ofId K L).mapMatrix (m := Fin h)) M q` as an intermediate fact.

Rewrite `this` using `[hq, map_zero]`. Conclude with `this`. Establish `hroot : M'.charpoly.IsRoot (AdjoinRoot.root p)`. Rewrite using `[Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]`. Conclude with `hd`.

Establish `hs : AdjoinRoot.root p ∈ spectrum L M'` using `Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot`. Establish `h2` using `spectrum.subset_polynomial_aeval M' (q.map (algebraMap K L)) ⟨_, hs, rfl⟩`. Rewrite `h2` using `[aeval_map_algebraMap, hM']`. Establish `hnt : Nontrivial (Matrix (Fin h) (Fin h) L)`. Assume the negation of the conclusion as `hn`.

Rewrite `hn` using `[not_nontrivial_iff_subsingleton]`. Conclude with `(spectrum.mem_iff.1 hs) (isUnit_of_subsingleton _)`. Rewrite `h2` using `[spectrum.zero_eq, Set.mem_singleton_iff]`. Simplify using `only [eval_map, ← aeval_def] at h2`. Rewrite `h2` using `[AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]`.

Conclude with `h2`.
-/
theorem irreducible_dvd_of_dvd_charpoly_of_aeval_matrix {K : Type} [Field K] {h : ℕ}
    (M : Matrix (Fin h) (Fin h) K) (p q : K[X]) (hp : Irreducible p)
    (hd : p ∣ M.charpoly) (hq : aeval M q = 0) : p ∣ q := by
  classical
  have : Fact (Irreducible p) := ⟨hp⟩
  let L := AdjoinRoot p
  let M' := M.map (algebraMap K L)
  have hM' : aeval M' q = 0 := by
    have := Polynomial.aeval_algHom_apply ((Algebra.ofId K L).mapMatrix (m := Fin h)) M q
    rw [hq, map_zero] at this
    exact this
  have hroot : M'.charpoly.IsRoot (AdjoinRoot.root p) := by
    rw [Matrix.charpoly_map, IsRoot.def, eval_map, ← aeval_def,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero]
    exact hd
  have hs : AdjoinRoot.root p ∈ spectrum L M' := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  have h2 := spectrum.subset_polynomial_aeval M' (q.map (algebraMap K L)) ⟨_, hs, rfl⟩
  rw [aeval_map_algebraMap, hM'] at h2
  have hnt : Nontrivial (Matrix (Fin h) (Fin h) L) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact (spectrum.mem_iff.1 hs) (isUnit_of_subsingleton _)
  rw [spectrum.zero_eq, Set.mem_singleton_iff] at h2
  simp only [eval_map, ← aeval_def] at h2
  rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero] at h2
  exact h2

/- English proof (translation)
Introduce `K _ h N M f hfm hfi hf hh`. Establish `hc0 : M.charpoly ≠ 0` using `(Matrix.charpoly_monic M).ne_zero`. Establish `hmem : ∀ b ∈ UniqueFactorizationMonoid.normalizedFactors M.charpoly, b = f`. Introduce `b hb`. Establish `hbi` using `UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb`.

Establish `hbd` using `UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb`. Establish `hbn` using `UniqueFactorizationMonoid.normalize_normalized_factor b hb`. Establish `hbm : b.Monic`. Rewrite using `[← hbn]`. Conclude with `Polynomial.monic_normalize hbi.ne_zero`.

Establish `hbf` using `irreducible_dvd_of_dvd_charpoly_of_aeval_matrix M b f hbi hbd hf`. Conclude with `eq_of_monic_of_associated hbm hfm (hbi.associated_of_dvd hfi hbf)`. Use `set n := Multiset.card (UniqueFactorizationMonoid.normalizedFactors M.charpoly)`. Establish `hrep : UniqueFactorizationMonoid.normalizedFactors M.charpoly = Multiset.replicate n f` using `Multiset.eq_replicate.mpr ⟨rfl, hmem⟩`. Establish `hass` using `UniqueFactorizationMonoid.prod_normalizedFactors hc0`.

Rewrite `hass` using `[hrep, Multiset.prod_replicate]`. Establish `hcp : M.charpoly = f ^ n` using `(eq_of_monic_of_associated (hfm.pow n) (Matrix.charpoly_monic M) hass).symm`. Establish `hdeg : f.natDegree * n = f.natDegree * N`. Use `congrArg Polynomial.natDegree hcp` as an intermediate fact. Rewrite `this` using `[Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hfm.natDegree_pow]`.

Rewrite using `[← hh]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hpos : 0 < f.natDegree` using `Irreducible.natDegree_pos hfi`. Rewrite using `[hcp, Nat.eq_of_mul_eq_mul_left hpos hdeg]`.
-/
theorem charpoly_eq_pow_of_aeval_irreducible_eq_zero :
    ∀ (K : Type) [Field K] (h N : ℕ) (M : Matrix (Fin h) (Fin h) K) (f : K[X]), f.Monic →
      Irreducible f → Polynomial.aeval M f = 0 → h = f.natDegree * N → M.charpoly = f ^ N := by
  intro K _ h N M f hfm hfi hf hh
  classical
  have hc0 : M.charpoly ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  have hmem : ∀ b ∈ UniqueFactorizationMonoid.normalizedFactors M.charpoly, b = f := by
    intro b hb
    have hbi := UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb
    have hbd := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hb
    have hbn := UniqueFactorizationMonoid.normalize_normalized_factor b hb
    have hbm : b.Monic := by
      rw [← hbn]; exact Polynomial.monic_normalize hbi.ne_zero
    have hbf := irreducible_dvd_of_dvd_charpoly_of_aeval_matrix M b f hbi hbd hf
    exact eq_of_monic_of_associated hbm hfm (hbi.associated_of_dvd hfi hbf)
  set n := Multiset.card (UniqueFactorizationMonoid.normalizedFactors M.charpoly)
  have hrep : UniqueFactorizationMonoid.normalizedFactors M.charpoly = Multiset.replicate n f :=
    Multiset.eq_replicate.mpr ⟨rfl, hmem⟩
  have hass := UniqueFactorizationMonoid.prod_normalizedFactors hc0
  rw [hrep, Multiset.prod_replicate] at hass
  have hcp : M.charpoly = f ^ n :=
    (eq_of_monic_of_associated (hfm.pow n) (Matrix.charpoly_monic M) hass).symm
  have hdeg : f.natDegree * n = f.natDegree * N := by
    have := congrArg Polynomial.natDegree hcp
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, hfm.natDegree_pow] at this
    rw [← hh]; linarith
  have hpos : 0 < f.natDegree := Irreducible.natDegree_pos hfi
  rw [hcp, Nat.eq_of_mul_eq_mul_left hpos hdeg]

end GlobalTheory
