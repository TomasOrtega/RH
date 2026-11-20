import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ContConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.CoefEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MapAdjAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Establish `k : ∀ a b : O, residue O a = residue O b → a • η = b • η` using `fun a b h => by`. Rewrite using `[← sub_eq_zero, ← sub_smul, Algebra.smul_def]`. Use `hη _ ?_` and prove the remaining obligations. Rewrite using `[← res_eq_zero_iff O, AlgHom.commutes, ResidueField.algebraMap_eq, map_sub, h, sub_self]`. Use `choose s hs using residue_surjective (R := O)`.

Establish `k2 : ∀ a : O, s (residue O a) • η = a • η` using `fun a => k _ _ (hs _)`. Use `⟨AddMonoidHom.mk' (fun c => s c • η) fun c d => ?_, k2, fun a c => ?_⟩` and prove the remaining obligations. Rewrite using `[← add_smul]`. Conclude with `k _ _ (by rw [map_add, hs, hs, hs])`. Take `⟨b, hb⟩` from `IsCO.res_surj (O := O) a`.

Establish `e : res O A a = residue O b`. Use `(res_eq_zero_iff O A _).2 hb` as an intermediate fact. Rewrite `this` using `[map_sub, AlgHom.commutes, sub_eq_zero]`. Then use the resulting hypothesis. Establish `e2 : a * η = b • η`. Use `hη _ hb` as an intermediate fact.

Rewrite `this` using `[sub_mul, sub_eq_zero, ← Algebra.smul_def]`. Then use the resulting hypothesis. Use `show s _ • η = a * (s c • η)`. Rewrite using `[mul_smul_comm, e2, smul_smul]`. Conclude with `k _ _ (by rw [map_mul, hs, hs, e, mul_comm])`.
-/
private theorem ex_mu {O A : Type} [CommRing O] [IsLocalRing O] [CommRing A] [Algebra O A] [IsCO O A] (η : A)
    (hη : ∀ x ∈ maximalIdeal A, x * η = 0) :
    ∃ μ : ResidueField O →+ A, (∀ a : O, μ (residue O a) = a • η) ∧ ∀ (a : A) c, μ (res O A a * c) = a * μ c := by
  have k : ∀ a b : O, residue O a = residue O b → a • η = b • η := fun a b h => by
    rw [← sub_eq_zero, ← sub_smul, Algebra.smul_def]
    refine hη _ ?_
    rw [← res_eq_zero_iff O, AlgHom.commutes, ResidueField.algebraMap_eq, map_sub, h, sub_self]
  choose s hs using residue_surjective (R := O)
  have k2 : ∀ a : O, s (residue O a) • η = a • η := fun a => k _ _ (hs _)
  refine ⟨AddMonoidHom.mk' (fun c => s c • η) fun c d => ?_, k2, fun a c => ?_⟩
  · rw [← add_smul]
    exact k _ _ (by rw [map_add, hs, hs, hs])
  · obtain ⟨b, hb⟩ := IsCO.res_surj (O := O) a
    have e : res O A a = residue O b := by
      have := (res_eq_zero_iff O A _).2 hb
      rwa [map_sub, AlgHom.commutes, sub_eq_zero] at this
    have e2 : a * η = b • η := by
      have := hη _ hb
      rwa [sub_mul, sub_eq_zero, ← Algebra.smul_def] at this
    show s _ • η = a * (s c • η)
    rw [mul_smul_comm, e2, smul_smul]
    exact k _ _ (by rw [map_mul, hs, hs, e, mul_comm])

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := (f : R →+* S))`.
-/
private theorem mmap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A B : M4 R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
private theorem smap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A B : M4 R) : (A - B).map f = A.map f - B.map f := by
  ext i j
  simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, adj_apply, adj_apply, map_zsmul, Matrix.map_apply]`.
-/
private theorem amap {O R S : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    (f : R →ₐ[O] S) (A : M4 R) : (adj A).map f = adj (A.map f) := by
  ext i j
  rw [Matrix.map_apply, adj_apply, adj_apply, map_zsmul, Matrix.map_apply]

/- English proof (translation)
Introduce `O _ _ _ _ h2 Γ V _ _ _ Gv _ _ _ loc hloc R _ _ _ ν r n hν hw hr rb nb hb hrb hnb A _ _ _ p hp hs κ _ ε hK hind`. Take `⟨D, hD⟩` from `X1.slEx h2 loc hloc p hp hs ν r n hν hw hr`. Take `⟨co, k1, k2, k4⟩` from `X1.coefEx (RingHom.ker p) hs κ ε hK hind`. Use `choose z z0 z1 z2 using fun u : κ => X1.obCoc loc hloc p hp hs ν r n hν hw hr rb nb hb hrb hnb D (co u) (k1 u) (k2 u)`. Establish `d1 : ∀ s t, (D.om s t).map p = 0` using `fun s t => by`.

Rewrite using `[SL.om, smap, mmap, D.rt_map, D.rt_map, D.rt_map, map_mul, sub_self]`. Establish `d2 : ∀ v s, (D.de v s).map p = 0` using `fun v s => by`. Establish `e1 : adj (n v) * n v = 1`. Use `hw.sp v` as an intermediate fact. Rewrite `this` using `[IsGSp, one_smul]`. Then use the resulting hypothesis.

Establish `e2 : n v * adj (n v) = 1` using `mul_eq_one_comm.1 e1`. Rewrite using `[SL.de, smap, mmap, mmap, amap, D.rt_map, D.nt_map, D.t_map, ← mul_assoc, ← mul_assoc, e2, one_mul, mul_assoc, e2, mul_one, sub_self]`. Use `⟨fun u => Submodule.Quotient.mk ⟨z u, z0 u⟩, ?_⟩` and prove the remaining obligations. Introduce `c hc A' _ _ _ p' p'' η hp' hpp hη hη0 e1`. Establish `hx : ∑ u, residue O (c u) • z u ∈ Fr.continuousCoboundaries2 loc (adSp rb hb) (fun v => bor (nb v))`.

Establish `h1 : (Submodule.Quotient.mk (∑ u, residue O (c u) • (⟨z u, z0 u⟩ : Fr.continuousCocycles2 loc (adSp rb hb) (fun v => bor (nb v)))) : Fr.coneH2 loc (adSp rb hb) (fun v => bor (nb v))) = 0`. Rewrite using `[← hc, ← Submodule.mkQ_apply, map_sum]`. Both sides reduce to the same expression. Rewrite `h1` using `[Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_sum]`. Conclude with `h1`.

Take `⟨μ, m1, m2⟩` from `ex_mu (O := O) η hη`. Establish `pp : ∀ x, p'' (p' x) = p x` using `fun x => DFunLike.congr_fun hpp x`. Establish `key : ∀ x, p x = 0 → p' x = μ (∑ u, residue O (c u) * co u x)` using `fun x hx => by`. Take `⟨a, ha, hxa⟩` from `k4 x hx`. Establish `: ∑ u, residue O (c u) * co u x = residue O (∑ u, a u * c u)`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun u _ => by rw [map_mul, ha, mul_comm]`. Rewrite using `[this, m1, Finset.sum_smul]`. Use `conv_lhs => rw [hxa]`. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, e1, mul_smul]`. Establish `keyM : ∀ (M : M4 A) (Y : κ → sp4 (ResidueField O)) (g : M4 (ResidueField O)), M.map p = 0 → (∀ u, (Y u).1 * g = M.map (co u)) → M.map p' = ((∑ u, residue O (c u) • Y u).1 * g).map μ` using `fun M Y g h1 h3 => by`. Use extensionality with `a b`. Establish `h4 : p (M a b) = 0` using `congrFun (congrFun h1 a) b`.

Rewrite using `[Matrix.map_apply, key _ h4, Matrix.map_apply, Submodule.coe_sum, Finset.sum_mul, Matrix.sum_apply]`. Use `congr 1`. Use `Finset.sum_congr rfl fun u _ => ?_` and prove the remaining obligations. Rewrite using `[Submodule.coe_smul, smul_mul_assoc, h3]`. Both sides reduce to the same expression.

Establish `m3 : ∀ d, p'' (μ d) = 0` using `fun d => by`. Take `⟨a, rfl⟩` from `residue_surjective d`. Rewrite using `[m1, map_smul, hη0, smul_zero]`. Establish `hp'' : Function.Surjective p''` using `fun y => by`. Take `⟨x, rfl⟩` from `hp y`.

Conclude with `⟨p' x, pp x⟩`. Establish `hs' : maximalIdeal A' * RingHom.ker p'' = ⊥`. Rewrite using `[eq_bot_iff, Ideal.mul_le]`. Introduce `x hx y hy`. Take `⟨y, rfl⟩` from `hp' y`.

Rewrite `hy` using `[RingHom.mem_ker, pp]`. Rewrite using `[Ideal.mem_bot, key y hy, ← m2, (res_eq_zero_iff O A' x).2 hx, zero_mul, map_zero]`. Take `⟨D', f1, f2⟩` from `hD A' p' p'' hpp`. Use `⟨hp'', hs', X1.obCor loc hloc p'' hp'' hs' ν r n hν hw hr rb nb hb hrb hnb D' μ μ.map_add m2 m3 _ hx (fun s t => ?_) (fun v s => ?_)⟩` and prove the remaining obligations. Rewrite using `[f1, keyM _ (fun u => (z u).1 (s, t)) _ (d1 s t) fun u => z1 u s t, Prod.fst_sum, Finset.sum_apply]`.

Both sides reduce to the same expression. Rewrite using `[f2, keyM _ (fun u => (z u).2 v s) _ (d2 v s) fun u => z2 u v s, Prod.snd_sum, Finset.sum_apply, Finset.sum_apply]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Ws.X1.obWeak :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {R : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R], ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∀ (rb : Γ →* M4 (ResidueField Λ)) (nb : V → M4 (ResidueField Λ)) (hb : ∀ g, ∃ x, IsGSp x (rb g)), (∀ g, (r g).map (res Λ R) = rb g) → (∀ v, (n v).map (res Λ R) = nb v) → Obs Λ R (Fr.coneH2 loc (adSp rb hb) fun v => bor (nb v)) fun A' _ _ _ q => Function.Surjective q ∧ maximalIdeal A' * RingHom.ker q = ⊥ ∧ WLift loc ν r n q := by
  intro O _ _ _ _ h2 Γ V _ _ _ Gv _ _ _ loc hloc R _ _ _ ν r n hν hw hr rb nb hb hrb hnb A _ _ _ p hp hs κ _ ε hK hind
  classical
  obtain ⟨D, hD⟩ := X1.slEx h2 loc hloc p hp hs ν r n hν hw hr
  obtain ⟨co, k1, k2, k4⟩ := X1.coefEx (RingHom.ker p) hs κ ε hK hind
  choose z z0 z1 z2 using fun u : κ =>
    X1.obCoc loc hloc p hp hs ν r n hν hw hr rb nb hb hrb hnb D (co u) (k1 u) (k2 u)
  have d1 : ∀ s t, (D.om s t).map p = 0 := fun s t => by
    rw [SL.om, smap, mmap, D.rt_map, D.rt_map, D.rt_map, map_mul, sub_self]
  have d2 : ∀ v s, (D.de v s).map p = 0 := fun v s => by
    have e1 : adj (n v) * n v = 1 := by
      have := hw.sp v
      rwa [IsGSp, one_smul] at this
    have e2 : n v * adj (n v) = 1 := mul_eq_one_comm.1 e1
    rw [SL.de, smap, mmap, mmap, amap, D.rt_map, D.nt_map, D.t_map, ← mul_assoc, ← mul_assoc, e2, one_mul,
      mul_assoc, e2, mul_one, sub_self]
  refine ⟨fun u => Submodule.Quotient.mk ⟨z u, z0 u⟩, ?_⟩
  intro c hc A' _ _ _ p' p'' η hp' hpp hη hη0 e1
  have hx : ∑ u, residue O (c u) • z u ∈ Fr.continuousCoboundaries2 loc (adSp rb hb) (fun v => bor (nb v)) := by
    have h1 : (Submodule.Quotient.mk (∑ u, residue O (c u) •
        (⟨z u, z0 u⟩ : Fr.continuousCocycles2 loc (adSp rb hb) (fun v => bor (nb v)))) :
        Fr.coneH2 loc (adSp rb hb) (fun v => bor (nb v))) = 0 := by
      rw [← hc, ← Submodule.mkQ_apply, map_sum]
      rfl
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, map_sum] at h1
    exact h1
  obtain ⟨μ, m1, m2⟩ := ex_mu (O := O) η hη
  have pp : ∀ x, p'' (p' x) = p x := fun x => DFunLike.congr_fun hpp x
  have key : ∀ x, p x = 0 → p' x = μ (∑ u, residue O (c u) * co u x) := fun x hx => by
    obtain ⟨a, ha, hxa⟩ := k4 x hx
    have : ∑ u, residue O (c u) * co u x = residue O (∑ u, a u * c u) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun u _ => by rw [map_mul, ha, mul_comm]
    rw [this, m1, Finset.sum_smul]
    conv_lhs => rw [hxa]
    rw [map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [map_smul, e1, mul_smul]
  have keyM : ∀ (M : M4 A) (Y : κ → sp4 (ResidueField O)) (g : M4 (ResidueField O)),
      M.map p = 0 → (∀ u, (Y u).1 * g = M.map (co u)) →
      M.map p' = ((∑ u, residue O (c u) • Y u).1 * g).map μ := fun M Y g h1 h3 => by
    ext a b
    have h4 : p (M a b) = 0 := congrFun (congrFun h1 a) b
    rw [Matrix.map_apply, key _ h4, Matrix.map_apply, Submodule.coe_sum, Finset.sum_mul, Matrix.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Submodule.coe_smul, smul_mul_assoc, h3]
    rfl
  have m3 : ∀ d, p'' (μ d) = 0 := fun d => by
    obtain ⟨a, rfl⟩ := residue_surjective d
    rw [m1, map_smul, hη0, smul_zero]
  have hp'' : Function.Surjective p'' := fun y => by
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨p' x, pp x⟩
  have hs' : maximalIdeal A' * RingHom.ker p'' = ⊥ := by
    rw [eq_bot_iff, Ideal.mul_le]
    intro x hx y hy
    obtain ⟨y, rfl⟩ := hp' y
    rw [RingHom.mem_ker, pp] at hy
    rw [Ideal.mem_bot, key y hy, ← m2, (res_eq_zero_iff O A' x).2 hx, zero_mul, map_zero]
  obtain ⟨D', f1, f2⟩ := hD A' p' p'' hpp
  refine ⟨hp'', hs', X1.obCor loc hloc p'' hp'' hs' ν r n hν hw hr rb nb hb hrb hnb D' μ μ.map_add m2 m3 _ hx
    (fun s t => ?_) (fun v s => ?_)⟩
  · rw [f1, keyM _ (fun u => (z u).1 (s, t)) _ (d1 s t) fun u => z1 u s t, Prod.fst_sum, Finset.sum_apply]
    rfl
  · rw [f2, keyM _ (fun u => (z u).2 v s) _ (d2 v s) fun u => z2 u v s, Prod.snd_sum, Finset.sum_apply,
      Finset.sum_apply]
    rfl
