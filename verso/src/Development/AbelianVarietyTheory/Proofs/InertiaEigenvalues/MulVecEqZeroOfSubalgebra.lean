import Mathlib

namespace GlobalTheory.SubalgebraMulVecZero

/- English proof (translation)
Take `⟨⟨b, hbM⟩, hb⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors B) Finset.univ v`. Use `choose u hu using fun i => hb i (Finset.mem_univ i)`. Establish `hAu : A.mulVec u = 0`. Use function extensionality and compare the values at `k`. Apply `IsFractionRing.injective B (FractionRing B)` to reduce the goal to its premises.

Rewrite using `[Pi.zero_apply, map_zero]`. Establish `e : algebraMap B (FractionRing B) (A.mulVec u k) = (A.map (algebraMap B (FractionRing B))).mulVec (fun i => algebraMap B (FractionRing B) (u i)) k`. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`. Rewrite using `[e]`. Establish `e2 : (fun i => algebraMap B (FractionRing B) (u i)) = b • v` using `funext hu`.

Rewrite using `[e2, Matrix.mulVec_smul, hv, smul_zero]`. Both sides reduce to the same expression. Establish `hu0` using `hA u hAu`. Use function extensionality and compare the values at `i`. Establish `h1` using `hu i`.

Rewrite `h1` using `[hu0, Pi.zero_apply, map_zero]`. Establish `hb0 : algebraMap B (FractionRing B) b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbM`. Rewrite `h1` using `[Algebra.smul_def]`. Conclude with `(mul_eq_zero.1 h1.symm).resolve_left hb0`.
-/
theorem mulVec_frac_eq_zero {B : Type} [CommRing B] [IsDomain B] {ι κ : Type} [Fintype ι]
    (A : Matrix κ ι B) (hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0)
    (v : ι → FractionRing B)
    (hv : (A.map (algebraMap B (FractionRing B))).mulVec v = 0) : v = 0 := by
  classical
  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors B) Finset.univ v
  choose u hu using fun i => hb i (Finset.mem_univ i)
  have hAu : A.mulVec u = 0 := by
    funext k
    apply IsFractionRing.injective B (FractionRing B)
    rw [Pi.zero_apply, map_zero]
    have e : algebraMap B (FractionRing B) (A.mulVec u k) =
        (A.map (algebraMap B (FractionRing B))).mulVec (fun i => algebraMap B (FractionRing B) (u i)) k := by
      simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rw [e]
    have e2 : (fun i => algebraMap B (FractionRing B) (u i)) = b • v := funext hu
    rw [e2, Matrix.mulVec_smul, hv, smul_zero]
    rfl
  have hu0 := hA u hAu
  funext i
  have h1 := hu i
  rw [hu0, Pi.zero_apply, map_zero] at h1
  have hb0 : algebraMap B (FractionRing B) b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hbM
  rw [Algebra.smul_def] at h1
  exact (mul_eq_zero.1 h1.symm).resolve_left hb0

/- English proof (translation)
Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) (by`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `v hv`. Conclude with `hA v hv)`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations.

Establish `e : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' A) = LinearMap.toMatrix' g * A`. Rewrite using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']`. Rewrite using `[← e, hg, LinearMap.toMatrix'_id]`.
-/
theorem exists_left_inv {K : Type} [Field K] {ι κ : Type} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (A : Matrix κ ι K) (hA : ∀ v : ι → K, A.mulVec v = 0 → v = 0) :
    ∃ N : Matrix ι κ K, N * A = 1 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A) (by
    rw [LinearMap.ker_eq_bot']
    intro v hv
    exact hA v hv)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have e : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' A) = LinearMap.toMatrix' g * A := by
    rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin']
  rw [← e, hg, LinearMap.toMatrix'_id]

/- English proof (translation)
Set `A : Matrix κ ι B` to `Matrix.of fun i j => ⟨M i j, hM i j⟩`. Set `c : B →+* S` to `B.val.toRingHom`. Establish `hc : Function.Injective c` using `Subtype.val_injective`. Establish `hAM : A.map c = M`. Use extensionality with `i j`.

Both sides reduce to the same expression. Establish `hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0`. Introduce `u hu`. Establish `h1 : M.mulVec (c ∘ u) = 0`. Use function extensionality and compare the values at `i`.

Rewrite using `[← hAM, ← RingHom.map_mulVec, hu]`. Simplify using the standard rewrite rules. Establish `h2` using `hinj (c ∘ u) (fun j => (u j).2) h1`. Use function extensionality and compare the values at `j`. Apply `hc` to reduce the goal to its premises.

Use `congrFun h2 j` as an intermediate fact. Simplify using `using this`. Take `⟨N, hN⟩` from `exists_left_inv (A.map (algebraMap B (FractionRing B))) (mulVec_frac_eq_zero A hA)`. Establish `hL` using `IsFractionRing.injective S (FractionRing S)`. Set `g : B →+* FractionRing S` to `(algebraMap S (FractionRing S)).comp c`.

Establish `hg : Function.Injective g` using `hL.comp hc`. Set `φ : FractionRing B →+* FractionRing S` to `IsFractionRing.lift hg`. Establish `hmap : (A.map (algebraMap B (FractionRing B))).map φ = M.map (algebraMap S (FractionRing S))`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply]`.

Conclude with `IsFractionRing.lift_algebraMap hg (A i j)`. Establish `hN' : N.map φ * M.map (algebraMap S (FractionRing S)) = 1`. Rewrite using `[← hmap, ← Matrix.map_mul, hN]`. Conclude with `Matrix.map_one _ (map_zero φ) (map_one φ)`. Establish `hw' : (M.map (algebraMap S (FractionRing S))).mulVec ((algebraMap S (FractionRing S)) ∘ w) = 0`.

Use function extensionality and compare the values at `i`. Rewrite using `[← RingHom.map_mulVec, hw]`. Simplify using the standard rewrite rules. Establish `h0 : (algebraMap S (FractionRing S)) ∘ w = 0`. Rewrite using `[← Matrix.one_mulVec ((algebraMap S (FractionRing S)) ∘ w), ← hN', ← Matrix.mulVec_mulVec, hw', Matrix.mulVec_zero]`.

Use function extensionality and compare the values at `j`. Apply `hL` to reduce the goal to its premises. Use `congrFun h0 j` as an intermediate fact. Simplify using `using this`.
-/
theorem mulVec_eq_zero_of_subalgebra {O S : Type} [CommRing O] [CommRing S] [IsDomain S]
    [Algebra O S] (B : Subalgebra O S) {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix κ ι S) (hM : ∀ (i : κ) (j : ι), M i j ∈ B)
    (hinj : ∀ v : ι → S, (∀ j, v j ∈ B) → Matrix.mulVec M v = 0 → v = 0)
    (w : ι → S) (hw : Matrix.mulVec M w = 0) : w = 0 := by
  let A : Matrix κ ι B := Matrix.of fun i j => ⟨M i j, hM i j⟩
  let c : B →+* S := B.val.toRingHom
  have hc : Function.Injective c := Subtype.val_injective
  have hAM : A.map c = M := by
    ext i j
    rfl
  have hA : ∀ u : ι → B, A.mulVec u = 0 → u = 0 := by
    intro u hu
    have h1 : M.mulVec (c ∘ u) = 0 := by
      funext i
      rw [← hAM, ← RingHom.map_mulVec, hu]
      simp
    have h2 := hinj (c ∘ u) (fun j => (u j).2) h1
    funext j
    apply hc
    have := congrFun h2 j
    simpa using this
  obtain ⟨N, hN⟩ := exists_left_inv (A.map (algebraMap B (FractionRing B)))
    (mulVec_frac_eq_zero A hA)
  have hL := IsFractionRing.injective S (FractionRing S)
  let g : B →+* FractionRing S := (algebraMap S (FractionRing S)).comp c
  have hg : Function.Injective g := hL.comp hc
  let φ : FractionRing B →+* FractionRing S := IsFractionRing.lift hg
  have hmap : (A.map (algebraMap B (FractionRing B))).map φ
      = M.map (algebraMap S (FractionRing S)) := by
    ext i j
    simp only [Matrix.map_apply]
    exact IsFractionRing.lift_algebraMap hg (A i j)
  have hN' : N.map φ * M.map (algebraMap S (FractionRing S)) = 1 := by
    rw [← hmap, ← Matrix.map_mul, hN]
    exact Matrix.map_one _ (map_zero φ) (map_one φ)
  have hw' : (M.map (algebraMap S (FractionRing S))).mulVec
      ((algebraMap S (FractionRing S)) ∘ w) = 0 := by
    funext i
    rw [← RingHom.map_mulVec, hw]
    simp
  have h0 : (algebraMap S (FractionRing S)) ∘ w = 0 := by
    rw [← Matrix.one_mulVec ((algebraMap S (FractionRing S)) ∘ w), ← hN',
      ← Matrix.mulVec_mulVec, hw', Matrix.mulVec_zero]
  funext j
  apply hL
  have := congrFun h0 j
  simpa using this

end GlobalTheory.SubalgebraMulVecZero
