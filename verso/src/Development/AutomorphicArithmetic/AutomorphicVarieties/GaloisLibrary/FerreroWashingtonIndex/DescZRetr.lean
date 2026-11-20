import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle

open UpperTheory.V.FW

/- English proof (translation)
Use `letI := ZMod.algebra k l`. Establish `hinj : LinearMap.ker (LinearMap.toSpanSingleton (ZMod l) k 1) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot]`. Introduce `a b h`. Simplify using `only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_one] at h`.

Conclude with `(algebraMap (ZMod l) k).injective h`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hinj`. Use `⟨g.toAddMonoidHom, ?_⟩` and prove the remaining obligations. Establish `h1` using `LinearMap.congr_fun hg 1`. Simplify using `using h1`.
-/
private theorem UpperTheory.V.FW.descZ_retr (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] :
    ∃ ϖ : k →+ ZMod l, ϖ 1 = 1 := by
  letI := ZMod.algebra k l
  have hinj : LinearMap.ker (LinearMap.toSpanSingleton (ZMod l) k 1) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b h
    simp only [LinearMap.toSpanSingleton_apply, Algebra.smul_def, mul_one] at h
    exact (algebraMap (ZMod l) k).injective h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  refine ⟨g.toAddMonoidHom, ?_⟩
  have h1 := LinearMap.congr_fun hg 1
  simpa using h1

/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => rw [map_add, mul_add, MonoidAlgebra.map_add, hx, hy, map_add, mul_add]`. Consider the case `single g n`. Use extensionality with `h`.

Simplify using `only [toK, MonoidAlgebra.mapRingHom_single, eq_intCast, MonoidAlgebra.coeff_map, Finsupp.mapRange_apply, MonoidAlgebra.mul_single_apply, AddMonoidHom.coe_coe]`. Rewrite using `[← zsmul_eq_mul', map_zsmul, zsmul_eq_mul']`.
-/
private theorem UpperTheory.V.FW.descZ_mul {k F G : Type} [CommRing k] [CommRing F] [CommGroup G] (ϖ : k →+ F)
    (u : MonoidAlgebra k G) (a : MonoidAlgebra ℤ G) :
    MonoidAlgebra.map ϖ (u * toK k G a) = MonoidAlgebra.map ϖ u * toK F G a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, mul_add, MonoidAlgebra.map_add, hx, hy, map_add, mul_add]
  | single g n =>
    ext h
    simp only [toK, MonoidAlgebra.mapRingHom_single, eq_intCast, MonoidAlgebra.coeff_map,
      Finsupp.mapRange_apply, MonoidAlgebra.mul_single_apply, AddMonoidHom.coe_coe]
    rw [← zsmul_eq_mul', map_zsmul, zsmul_eq_mul']

/- English proof (translation)
Use `⟨MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun n : ℤ => n / (l : ℤ)) (by simp) y.coeff), ?_⟩` and prove the remaining obligations. Use extensionality with `g`. Establish `hg : (l : ℤ) ∣ y.coeff g`. Establish `h0` using `congrArg (fun w => w.coeff g) hy`. Simplify using `only [toK, MonoidAlgebra.coeff_mapRingHom, eq_intCast, MonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at h0`.

Conclude with `(CharP.intCast_eq_zero_iff (ZMod l) l _).mp h0`. Rewrite using `[MonoidAlgebra.natCast_def, MonoidAlgebra.mul_single_apply, inv_one, mul_one, MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply, Int.ediv_mul_cancel hg]`.
-/
private theorem UpperTheory.V.FW.descZ_ker (l : ℕ) {G : Type} [CommGroup G] (y : MonoidAlgebra ℤ G)
    (hy : toK (ZMod l) G y = 0) : ∃ z, y = z * (l : MonoidAlgebra ℤ G) := by
  classical
  refine ⟨MonoidAlgebra.ofCoeff (Finsupp.mapRange (fun n : ℤ => n / (l : ℤ)) (by simp) y.coeff), ?_⟩
  ext g
  have hg : (l : ℤ) ∣ y.coeff g := by
    have h0 := congrArg (fun w => w.coeff g) hy
    simp only [toK, MonoidAlgebra.coeff_mapRingHom, eq_intCast, MonoidAlgebra.coeff_zero,
      Finsupp.coe_zero, Pi.zero_apply] at h0
    exact (CharP.intCast_eq_zero_iff (ZMod l) l _).mp h0
  rw [MonoidAlgebra.natCast_def, MonoidAlgebra.mul_single_apply, inv_one, mul_one,
    MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply, Int.ediv_mul_cancel hg]

/- English proof (translation)
Introduce `l _ k G _ _ _ x a b hx`. Take `⟨ϖ, hϖ⟩` from `descZ_retr l k`. Take `⟨u, v, huv⟩` from `Ideal.mem_span_pair.1 hx`. Establish `h1 : MonoidAlgebra.map ϖ (1 : MonoidAlgebra k G) = 1`. Rewrite using `[MonoidAlgebra.one_def, MonoidAlgebra.map_single, hϖ, MonoidAlgebra.one_def]`.

Establish `h2` using `descZ_mul ϖ 1 x`. Rewrite `h2` using `[one_mul, h1, one_mul, ← huv, MonoidAlgebra.map_add, descZ_mul, descZ_mul]`. Establish `hs : Function.Surjective (toK (ZMod l) G)` using `MonoidAlgebra.map_surjective (Int.castRingHom (ZMod l) : ℤ →+ ZMod l) ZMod.intCast_surjective`. Take `⟨u', hu⟩` from `hs (MonoidAlgebra.map ϖ u)`. Take `⟨v', hv⟩` from `hs (MonoidAlgebra.map ϖ v)`.

Take `⟨z, hz⟩` from `descZ_ker l (x - (u' * a + v' * b)) (by`. Rewrite using `[map_sub, map_add, map_mul, map_mul, hu, hv, h2, sub_self])`. Establish `hx' : x = u' * a + v' * b + z * (l : MonoidAlgebra ℤ G)` using `by rw [← hz]; ring`. Rewrite using `[hx']`. Apply the tactic sequence `refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))`.
-/
theorem UpperTheory.V.FW.descZ :
    ∀ (l : ℕ) [Fact l.Prime] (k G : Type) [Field k] [CharP k l] [CommGroup G] (x a b : MonoidAlgebra ℤ G), toK k G x ∈ Ideal.span {toK k G a, toK k G b} → x ∈ Ideal.span {a, b, (l : MonoidAlgebra ℤ G)} := by
  intro l _ k G _ _ _ x a b hx
  obtain ⟨ϖ, hϖ⟩ := descZ_retr l k
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 hx
  have h1 : MonoidAlgebra.map ϖ (1 : MonoidAlgebra k G) = 1 := by
    rw [MonoidAlgebra.one_def, MonoidAlgebra.map_single, hϖ, MonoidAlgebra.one_def]
  have h2 := descZ_mul ϖ 1 x
  rw [one_mul, h1, one_mul, ← huv, MonoidAlgebra.map_add, descZ_mul, descZ_mul] at h2
  have hs : Function.Surjective (toK (ZMod l) G) :=
    MonoidAlgebra.map_surjective (Int.castRingHom (ZMod l) : ℤ →+ ZMod l) ZMod.intCast_surjective
  obtain ⟨u', hu⟩ := hs (MonoidAlgebra.map ϖ u)
  obtain ⟨v', hv⟩ := hs (MonoidAlgebra.map ϖ v)
  obtain ⟨z, hz⟩ := descZ_ker l (x - (u' * a + v' * b)) (by
    rw [map_sub, map_add, map_mul, map_mul, hu, hv, h2, sub_self])
  have hx' : x = u' * a + v' * b + z * (l : MonoidAlgebra ℤ G) := by rw [← hz]; ring
  rw [hx']
  refine Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_ <;>
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
