import Formalism.WachLatticeTwists.WachProductBases.NontrivialWachExample
import Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.SaturationIntersectionHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers Finset

/- English proof (translation)
Introduce `L R _ _ _ P _ _ _ _ t u γR γ κ _ n a y Sx hγt hγs hmod hbij hn hS x hx`. Establish `hbijm` using `pow_smul_bij t hbij`. Use `choose wv hwv using fun (k : κ) (m : ℕ) => (hbijm m).2 (n k)`. Simplify using `only at hwv`. Establish `hstep : ∀ k m, t • wv k (m + 1) = wv k m`.

Introduce `k m`. Apply `(hbijm m).1` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[smul_smul, ← pow_succ, hwv, hwv]`. Establish `heig : ∀ k (m : ℕ), γ (wv k m) = ((u ^ (-(a k + m)) : Lˣ) : L) • wv k m`.

Introduce `k m`. Apply `(hbijm m).1` to reduce the goal to its premises. Simplify using `only`. Establish `h1 : γ (t ^ m • wv k m) = ((u : L) ^ m) • (t ^ m • γ (wv k m))`. Rewrite using `[hγs, map_pow, hγt, smul_pow, smul_assoc]`.

Rewrite `h1` using `[hwv, hn]`. Rewrite using `[smul_comm (t ^ m), hwv]`. Establish `h2 : t ^ m • γ (wv k m) = ((u ^ (-(m : ℤ)) : Lˣ) : L) • (((u : L) ^ m) • (t ^ m • γ (wv k m)))`. Rewrite using `[smul_smul]`. Establish `: ((u ^ (-(m : ℤ)) : Lˣ) : L) * (u : L) ^ m = 1`.

Rewrite using `[← Units.val_pow_eq_pow_val, ← Units.val_mul, zpow_neg, zpow_natCast, inv_mul_cancel, Units.val_one]`. Rewrite using `[this, one_smul]`. Rewrite using `[h2, ← h1, smul_smul, ← Units.val_mul, ← zpow_add]`. Use `congr 3`. Expand and normalize the polynomial expressions, which then agree.

Establish `key1 : ∀ k m (b : ℤ) (r : R), ∃ r' : R, γ (r • wv k m) - ((u ^ (-b) : Lˣ) : L) • (r • wv k m) = r' • wv k m`. Introduce `k m b r`. Use `⟨γR r * algebraMap L R ((u ^ (-(a k + m)) : Lˣ) : L) - algebraMap L R ((u ^ (-b) : Lˣ) : L) * r, ?_⟩` and prove the remaining obligations. Rewrite using `[hγs, heig, ← algebraMap_smul R (((u ^ (-(a k + m)) : Lˣ) : L)) (wv k m), ← algebraMap_smul R (((u ^ (-b) : Lˣ) : L)) (r • wv k m)]`. Use `module`.

Establish `key2 : ∀ k (m : ℕ) (r : R), ∃ r' : R, γ (r • wv k (m + 1)) - ((u ^ (-(a k + ((m + 1 : ℕ) : ℤ))) : Lˣ) : L) • (r • wv k (m + 1)) = r' • wv k m`. Introduce `k m r`. Take `⟨r', hr'⟩` from `hmod r`. Use `set μ : L := ((u ^ (-(a k + ((m + 1 : ℕ) : ℤ))) : Lˣ) : L) with hμ`. Use `⟨r' * algebraMap L R μ, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hstep k m]`. Establish `e2 : γR r = r + t * r'` using `by rw [← hr']; ring`. Rewrite using `[hγs, heig, ← hμ, ← algebraMap_smul R μ (wv k (m + 1)), ← algebraMap_smul R μ (r • wv k (m + 1)), e2]`. Use `module`. Establish `pres : ∀ k m (T : Finset ℤ) (r : R), ∃ r' : R, Polynomial.aeval γ (∏ b ∈ T, (Polynomial.X - Polynomial.C (((u ^ (-b) : Lˣ) : L)))) (r • wv k m) = r' • wv k m`.

Introduce `k m T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => intro r; exact ⟨r, by simp⟩`. Consider the case `insert b T hb ih`. Introduce `r`.

Take `⟨r₁, h1⟩` from `ih r`. Take `⟨r₂, h2⟩` from `key1 k m b r₁`. Use `⟨r₂, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.prod_insert hb, map_mul, Module.End.mul_apply, h1, ← h2]`. Simplify using `[Module.algebraMap_end_apply]`.

Establish `main : ∀ k (m : ℕ) (T : Finset ℤ), (∀ j ∈ Finset.Icc (1 : ℤ) m, a k + j ∈ T) → ∀ r : R, ∃ r' : R, Polynomial.aeval γ (∏ b ∈ T, (Polynomial.X - Polynomial.C (((u ^ (-b) : Lˣ) : L)))) (r • wv k m) = r' • wv k 0`. Introduce `k m`. Proceed by induction on `m with`. Consider the case `zero => intro T _ r`. Conclude with `pres k 0 T r`.

Consider the case `succ m ih`. Introduce `T hT r`. Establish `hb₀ : a k + ((m + 1 : ℕ) : ℤ) ∈ T` using `hT _ (Finset.mem_Icc.2 ⟨by push_cast; omega, le_refl _⟩)`. Take `⟨r₁, h1⟩` from `key2 k m r`. Take `⟨r₂, h2⟩` from `ih (T.erase (a k + ((m + 1 : ℕ) : ℤ))) (by`.

Introduce `j hj`. Take `⟨hj1, hj2⟩` from `Finset.mem_Icc.1 hj`. Use `Finset.mem_erase.2 ⟨by push_cast; omega, hT j (Finset.mem_Icc.2 ⟨hj1, ?_⟩)⟩` and prove the remaining obligations. Use `push_cast`. Use the proof step `omega) r₁`.

Use `⟨r₂, ?_⟩` and prove the remaining obligations. Rewrite using `[← Finset.prod_erase_mul T _ hb₀, map_mul, Module.End.mul_apply, ← h2, ← h1]`. Simplify using `[Module.algebraMap_end_apply]`. Take `⟨r, hr⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 hx`. Establish `hxsum : x = ∑ k, r k • wv k y`.

Apply `(hbijm y).1` to reduce the goal to its premises. Simplify using `only`. Rewrite using `[← hr, smul_sum]`. Use `sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm, hwv]`.

Rewrite using `[hxsum, map_sum]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Take `⟨r', h'⟩` from `main k y Sx (hS k) (r k)`. Rewrite using `[h']`. Establish `h0 : wv k 0 = n k` using `by simpa using hwv k 0`.

Rewrite using `[h0]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)`.
-/
theorem consequence_two_triangular : TriangularConsequence := by
  intro L R _ _ _ P _ _ _ _ t u γR γ κ _ n a y Sx hγt hγs hmod hbij hn hS x hx
  classical
  have hbijm := pow_smul_bij t hbij
  choose wv hwv using fun (k : κ) (m : ℕ) => (hbijm m).2 (n k)
  simp only at hwv
  have hstep : ∀ k m, t • wv k (m + 1) = wv k m := by
    intro k m
    apply (hbijm m).1
    simp only
    rw [smul_smul, ← pow_succ, hwv, hwv]
  have heig : ∀ k (m : ℕ), γ (wv k m) = ((u ^ (-(a k + m)) : Lˣ) : L) • wv k m := by
    intro k m
    apply (hbijm m).1
    simp only
    have h1 : γ (t ^ m • wv k m) = ((u : L) ^ m) • (t ^ m • γ (wv k m)) := by
      rw [hγs, map_pow, hγt, smul_pow, smul_assoc]
    rw [hwv, hn] at h1
    rw [smul_comm (t ^ m), hwv]
    have h2 : t ^ m • γ (wv k m) =
        ((u ^ (-(m : ℤ)) : Lˣ) : L) • (((u : L) ^ m) • (t ^ m • γ (wv k m))) := by
      rw [smul_smul]
      have : ((u ^ (-(m : ℤ)) : Lˣ) : L) * (u : L) ^ m = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, zpow_neg, zpow_natCast, inv_mul_cancel,
          Units.val_one]
      rw [this, one_smul]
    rw [h2, ← h1, smul_smul, ← Units.val_mul, ← zpow_add]
    congr 3
    ring
  have key1 : ∀ k m (b : ℤ) (r : R), ∃ r' : R,
      γ (r • wv k m) - ((u ^ (-b) : Lˣ) : L) • (r • wv k m) = r' • wv k m := by
    intro k m b r
    refine ⟨γR r * algebraMap L R ((u ^ (-(a k + m)) : Lˣ) : L) -
      algebraMap L R ((u ^ (-b) : Lˣ) : L) * r, ?_⟩
    rw [hγs, heig, ← algebraMap_smul R (((u ^ (-(a k + m)) : Lˣ) : L)) (wv k m),
      ← algebraMap_smul R (((u ^ (-b) : Lˣ) : L)) (r • wv k m)]
    module
  have key2 : ∀ k (m : ℕ) (r : R), ∃ r' : R,
      γ (r • wv k (m + 1)) - ((u ^ (-(a k + ((m + 1 : ℕ) : ℤ))) : Lˣ) : L) • (r • wv k (m + 1)) =
        r' • wv k m := by
    intro k m r
    obtain ⟨r', hr'⟩ := hmod r
    set μ : L := ((u ^ (-(a k + ((m + 1 : ℕ) : ℤ))) : Lˣ) : L) with hμ
    refine ⟨r' * algebraMap L R μ, ?_⟩
    rw [← hstep k m]
    have e2 : γR r = r + t * r' := by rw [← hr']; ring
    rw [hγs, heig, ← hμ, ← algebraMap_smul R μ (wv k (m + 1)),
      ← algebraMap_smul R μ (r • wv k (m + 1)), e2]
    module
  have pres : ∀ k m (T : Finset ℤ) (r : R), ∃ r' : R,
      Polynomial.aeval γ (∏ b ∈ T, (Polynomial.X - Polynomial.C (((u ^ (-b) : Lˣ) : L))))
        (r • wv k m) = r' • wv k m := by
    intro k m T
    induction T using Finset.induction_on with
    | empty => intro r; exact ⟨r, by simp⟩
    | insert b T hb ih =>
      intro r
      obtain ⟨r₁, h1⟩ := ih r
      obtain ⟨r₂, h2⟩ := key1 k m b r₁
      refine ⟨r₂, ?_⟩
      rw [Finset.prod_insert hb, map_mul, Module.End.mul_apply, h1, ← h2]
      simp [Module.algebraMap_end_apply]
  have main : ∀ k (m : ℕ) (T : Finset ℤ), (∀ j ∈ Finset.Icc (1 : ℤ) m, a k + j ∈ T) → ∀ r : R,
      ∃ r' : R, Polynomial.aeval γ (∏ b ∈ T, (Polynomial.X - Polynomial.C (((u ^ (-b) : Lˣ) : L))))
        (r • wv k m) = r' • wv k 0 := by
    intro k m
    induction m with
    | zero => intro T _ r; exact pres k 0 T r
    | succ m ih =>
      intro T hT r
      have hb₀ : a k + ((m + 1 : ℕ) : ℤ) ∈ T :=
        hT _ (Finset.mem_Icc.2 ⟨by push_cast; omega, le_refl _⟩)
      obtain ⟨r₁, h1⟩ := key2 k m r
      obtain ⟨r₂, h2⟩ := ih (T.erase (a k + ((m + 1 : ℕ) : ℤ))) (by
        intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
        refine Finset.mem_erase.2 ⟨by push_cast; omega, hT j (Finset.mem_Icc.2 ⟨hj1, ?_⟩)⟩
        push_cast; omega) r₁
      refine ⟨r₂, ?_⟩
      rw [← Finset.prod_erase_mul T _ hb₀, map_mul, Module.End.mul_apply, ← h2, ← h1]
      simp [Module.algebraMap_end_apply]
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hx
  have hxsum : x = ∑ k, r k • wv k y := by
    apply (hbijm y).1
    simp only
    rw [← hr, smul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [smul_comm, hwv]
  rw [hxsum, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨r', h'⟩ := main k y Sx (hS k) (r k)
  rw [h']
  have h0 : wv k 0 = n k := by simpa using hwv k 0
  rw [h0]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/- English proof (translation)
Introduce `O A R _ _ _ _ _ B M D P _ _ _ _ _ _ _ _ W u y Sx ρ κ _ t γR locA loc γl n a hGQ hγt hmod hbij hγls hlocs hlocγ hQt hP4 hP4e hP5 hS d hd`. Set `Ll : ρ → Submodule O P` to `fun x => (Submodule.span R (Set.range (n x))).restrictScalars O`. Set `Ly : ρ → Submodule O P` to `fun x => ((Submodule.span R (Set.range (n x))).comap (t ^ y • (LinearMap.id : P →ₗ[R] P))).restrictScalars O`. Use `consequence_two_global O A D W.N W.γ B.Q y _ ρ (fun _ => P) loc γl Ll Ly hlocγ hP5 ?_ ?_ ?_ d hd` and prove the remaining obligations. Introduce and unpack `d ⟨k, hk⟩`.

Take `⟨x', hx', h⟩` from `affineLine_localAcyclicity_of_strictHenselian_points O A B M D W k hGQ d hk`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `: W.γ d = d + B.X • x'` using `by rw [← h]; abel`. Rewrite using `[this, smul_add, smul_comm]`. Conclude with `W.N.add_mem hk (W.N.smul_mem _ hx')`.

Introduce `d hd x`. Take `⟨v, hv, hQ⟩` from `hQt x`. Take `⟨vi, hvi⟩` from `hv.exists_left_inv`. Use `show t ^ y • loc x d ∈ Submodule.span R (Set.range (n x))`. Establish `h1` using `hP4 x _ hd`.

Rewrite `h1` using `[hlocs x _ d ⟨y, hd⟩, map_pow, hQ, mul_pow, mul_smul]`. Establish `h2 : t ^ y • loc x d = vi ^ y • (v ^ y • t ^ y • loc x d)`. Rewrite using `[smul_smul, ← mul_pow, hvi, one_pow, one_smul]`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ h1`.

Introduce `x v hv`. Conclude with `consequence_two_triangular O R P t u γR (γl x) κ (n x) (a x) y Sx hγt (hγls x) hmod hbij (hP4e x) (hS x) v hv`.
-/
theorem consequence_two_top : TopDegreeTriangularConsequence := by
  intro O A R _ _ _ _ _ B M D P _ _ _ _ _ _ _ _ W u y Sx ρ κ _ t γR locA loc γl n a hGQ hγt hmod
    hbij hγls hlocs hlocγ hQt hP4 hP4e hP5 hS d hd
  let Ll : ρ → Submodule O P := fun x => (Submodule.span R (Set.range (n x))).restrictScalars O
  let Ly : ρ → Submodule O P := fun x =>
    ((Submodule.span R (Set.range (n x))).comap (t ^ y • (LinearMap.id : P →ₗ[R] P))).restrictScalars O
  refine consequence_two_global O A D W.N W.γ B.Q y _ ρ (fun _ => P) loc γl Ll Ly hlocγ hP5 ?_ ?_ ?_ d hd
  · rintro d ⟨k, hk⟩
    obtain ⟨x', hx', h⟩ := affineLine_localAcyclicity_of_strictHenselian_points O A B M D W k hGQ d hk
    refine ⟨k, ?_⟩
    have : W.γ d = d + B.X • x' := by rw [← h]; abel
    rw [this, smul_add, smul_comm]
    exact W.N.add_mem hk (W.N.smul_mem _ hx')
  · intro d hd x
    obtain ⟨v, hv, hQ⟩ := hQt x
    obtain ⟨vi, hvi⟩ := hv.exists_left_inv
    show t ^ y • loc x d ∈ Submodule.span R (Set.range (n x))
    have h1 := hP4 x _ hd
    rw [hlocs x _ d ⟨y, hd⟩, map_pow, hQ, mul_pow, mul_smul] at h1
    have h2 : t ^ y • loc x d = vi ^ y • (v ^ y • t ^ y • loc x d) := by
      rw [smul_smul, ← mul_pow, hvi, one_pow, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  · intro x v hv
    exact consequence_two_triangular O R P t u γR (γl x) κ (n x) (a x) y Sx hγt (hγls x) hmod hbij (hP4e x) (hS x)
      v hv

end Formalism.RepresentationBoundsCohomology.N1
