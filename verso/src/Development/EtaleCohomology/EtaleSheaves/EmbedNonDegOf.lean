import Development.EtaleCohomology.EtaleSheaves.EmbedNonDeg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut LateralTheory.E.StandardEtaleChartsIdempotentGluing LateralTheory.E.ChartsGeom_vpaPf
  LateralTheory.E.GeometricData

namespace LateralTheory.E.EmbedNonDeg₂

/- English proof (translation)
Simplify using `only [Scheme.germToFunctionField]`. Conclude with `TopCat.Presheaf.germ_res_apply _ _ _ _ _`.
-/
theorem germ_res {Z : Scheme.{0}} [IsIntegral Z] (U W : Z.Opens) (h : W ≤ U) [Nonempty U] [Nonempty W]
    (s : Γ(Z, U)) : Z.germToFunctionField W (Z.presheaf.map (homOfLE h).op s) = Z.germToFunctionField U s := by
  simp only [Scheme.germToFunctionField]
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

/- English proof (translation)
Establish `e` using `Scheme.Hom.appLE_map p (U := ⊤) (V := X) le_top (homOfLE h).op`. Simplify using `only [rA, RingHom.comp_apply]`. Conclude with `congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) e`.
-/
theorem rA_res {A : Type} [CommRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) {W X : Z.Opens}
    (h : W ≤ X) (a : A) : Z.presheaf.map (homOfLE h).op (rA p X a) = rA p W a := by
  have e := Scheme.Hom.appLE_map p (U := ⊤) (V := X) le_top (homOfLE h).op
  simp only [rA, RingHom.comp_apply]
  exact congrArg (fun f => f.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) e

/- English proof (translation)
Take `⟨P, hm, hP⟩` from `hf x`. Set `ψ : Polynomial A →+* Algebra.adjoin A {t}` to `(Polynomial.aeval (⟨t, Algebra.self_mem_adjoin_singleton A t⟩ : Algebra.adjoin A {t})).toRingHom`. Establish `key : (algebraMap (Algebra.adjoin A {t}) K).comp ψ = φ.comp f`. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`.

Simplify using `[ψ, hc]`. Simplify using `[ψ, hX]`. Use `⟨P.map ψ, hm.map ψ, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, key, ← Polynomial.hom_eval₂, hP, map_zero]`.
-/
theorem int_adjoin {A S K : Type} [CommRing A] [CommRing S] [Field K] [Algebra A K]
    (f : Polynomial A →+* S) (hf : f.IsIntegral) (φ : S →+* K) (t : K)
    (hc : ∀ a, φ (f (Polynomial.C a)) = algebraMap A K a) (hX : φ (f Polynomial.X) = t) (x : S) :
    IsIntegral (Algebra.adjoin A {t}) (φ x) := by
  obtain ⟨P, hm, hP⟩ := hf x
  let ψ : Polynomial A →+* Algebra.adjoin A {t} :=
    (Polynomial.aeval (⟨t, Algebra.self_mem_adjoin_singleton A t⟩ : Algebra.adjoin A {t})).toRingHom
  have key : (algebraMap (Algebra.adjoin A {t}) K).comp ψ = φ.comp f := by
    apply Polynomial.ringHom_ext
    · intro a; simp [ψ, hc]
    · simp [ψ, hX]
  refine ⟨P.map ψ, hm.map ψ, ?_⟩
  rw [Polynomial.eval₂_map, key, ← Polynomial.hom_eval₂, hP, map_zero]

/- English proof (translation)
Take `⟨P, hm, hP⟩` from `hf x`. Use `⟨P, hm, ?_⟩` and prove the remaining obligations. Establish `: algebraMap A K = φ.comp f` using `RingHom.ext fun a => (hc a).symm`. Rewrite using `[this, ← Polynomial.hom_eval₂, hP, map_zero]`.
-/
theorem int_A {A S K : Type} [CommRing A] [CommRing S] [Field K] [Algebra A K]
    (f : A →+* S) (hf : f.IsIntegral) (φ : S →+* K) (hc : ∀ a, φ (f a) = algebraMap A K a) (x : S) :
    IsIntegral A (φ x) := by
  obtain ⟨P, hm, hP⟩ := hf x
  refine ⟨P, hm, ?_⟩
  have : algebraMap A K = φ.comp f := RingHom.ext fun a => (hc a).symm
  rw [this, ← Polynomial.hom_eval₂, hP, map_zero]

/- English proof (translation)
Substitute `hW` using the available equality. Use `hU.isLocalization_basicOpen s` as an intermediate fact. Use extensionality with `k`. Prove the components needed by the constructor for the conclusion. Introduce `hk0`.

Take `⟨z, rfl⟩` from `hk0`. Take `⟨⟨x, ⟨_, n, rfl⟩⟩, e1⟩` from `IsLocalization.surj (Submonoid.powers s) z`. Establish `e2` using `congrArg φW e1`. Rewrite `e2` using `[map_mul]`. Express the relevant statement in the definitionally equal form `φW z * φW (Z.presheaf.map (homOfLE hle).op (s ^ n)) = φW (Z.presheaf.map (homOfLE hle).op x) at e2`.

Rewrite `e2` using `[hres, hres, map_pow]`. Establish `e3 : φW z = φU x * ((φU s)⁻¹) ^ n`. Rewrite using `[← e2, mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs), mul_one]`. Express the relevant statement in the definitionally equal form `φW z ∈ AdjoinInv B (φU s)`. Rewrite using `[e3]`.

Use `Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ ?_ _)` and prove the remaining obligations. Conclude with `Algebra.subset_adjoin (Or.inl ((hB _).mpr ⟨x, rfl⟩))`. Conclude with `Algebra.subset_adjoin (Or.inr rfl)`. Introduce `hk`. Establish `hBW : ∀ k ∈ B, k ∈ φW.rangeS`.

Introduce `k hk`. Take `⟨x, rfl⟩` from `(hB k).mp hk`. Conclude with `⟨_, hres x⟩`. Set `R : Subalgebra A K` to `{ toSubsemiring := φW.rangeS, algebraMap_mem' := fun a => hBW _ (B.algebraMap_mem a) }`. Establish `hle' : AdjoinInv B (φU s) ≤ R`.

Rewrite using `[AdjoinInv, Algebra.adjoin_le_iff]`. Introduce and unpack `k (hk | hk)`. Conclude with `hBW k hk`. Rewrite using `[Set.mem_singleton_iff.mp hk]`. Take `⟨y, hy⟩` from `hinv`.

Conclude with `⟨y, hy⟩`. Take `⟨y, hy⟩` from `hle' hk`. Conclude with `⟨y, hy⟩`.
-/
theorem range_loc {A K : Type} [CommRing A] [Field K] [Algebra A K] {Z : Scheme.{0}} {U W : Z.Opens}
    (hU : IsAffineOpen U) (s : Γ(Z, U)) (hW : Z.basicOpen s = W) (hle : W ≤ U)
    (φU : Γ(Z, U) →+* K) (φW : Γ(Z, W) →+* K)
    (hres : ∀ x, φW (Z.presheaf.map (homOfLE hle).op x) = φU x) (B : Subalgebra A K)
    (hB : ∀ k, k ∈ B ↔ ∃ x, φU x = k) (hs : φU s ≠ 0) (hinv : (φU s)⁻¹ ∈ φW.range) :
    φW.range = (AdjoinInv B (φU s)).toSubring := by
  subst hW
  have := hU.isLocalization_basicOpen s
  ext k; constructor
  · intro hk0
    obtain ⟨z, rfl⟩ := hk0
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, e1⟩ := IsLocalization.surj (Submonoid.powers s) z
    have e2 := congrArg φW e1
    rw [map_mul] at e2
    change φW z * φW (Z.presheaf.map (homOfLE hle).op (s ^ n)) = φW (Z.presheaf.map (homOfLE hle).op x) at e2
    rw [hres, hres, map_pow] at e2
    have e3 : φW z = φU x * ((φU s)⁻¹) ^ n := by
      rw [← e2, mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hs), mul_one]
    change φW z ∈ AdjoinInv B (φU s)
    rw [e3]
    refine Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ ?_ _)
    · exact Algebra.subset_adjoin (Or.inl ((hB _).mpr ⟨x, rfl⟩))
    · exact Algebra.subset_adjoin (Or.inr rfl)
  · intro hk
    have hBW : ∀ k ∈ B, k ∈ φW.rangeS := by
      intro k hk; obtain ⟨x, rfl⟩ := (hB k).mp hk
      exact ⟨_, hres x⟩
    let R : Subalgebra A K :=
      { toSubsemiring := φW.rangeS, algebraMap_mem' := fun a => hBW _ (B.algebraMap_mem a) }
    have hle' : AdjoinInv B (φU s) ≤ R := by
      rw [AdjoinInv, Algebra.adjoin_le_iff]
      rintro k (hk | hk)
      · exact hBW k hk
      · rw [Set.mem_singleton_iff.mp hk]; obtain ⟨y, hy⟩ := hinv; exact ⟨y, hy⟩
    obtain ⟨y, hy⟩ := hle' hk
    exact ⟨y, hy⟩

/- English proof (translation)
Introduce `A _ _ Z p hI hTop hN`. Take `⟨U, V, s, s', hU, hV, hUV, hsU, hsV, ⟨z, hz⟩, hss, hiU, hiV⟩` from `hN`. Establish `hzU : z ∈ U` using `(inf_le_left : U ⊓ V ≤ U) hz`. Establish `hzV : z ∈ V` using `(inf_le_right : U ⊓ V ≤ V) hz`. Establish `: Nonempty U` using `⟨⟨z, hzU⟩⟩`.

Establish `: Nonempty V` using `⟨⟨z, hzV⟩⟩`. Establish `: Nonempty (U ⊓ V : Z.Opens)` using `⟨⟨z, hz⟩⟩`. Establish `: Nonempty (U ⊔ V : Z.Opens)` using `⟨⟨z, (le_sup_left : U ≤ U ⊔ V) hzU⟩⟩`. Set `φU : Γ(Z, U) →+* Z.functionField` to `(Z.germToFunctionField U).hom`. Set `φV : Γ(Z, V) →+* Z.functionField` to `(Z.germToFunctionField V).hom`.

Set `φW : Γ(Z, U ⊓ V) →+* Z.functionField` to `(Z.germToFunctionField (U ⊓ V)).hom`. Set `φT : Γ(Z, U ⊔ V) →+* Z.functionField` to `(Z.germToFunctionField (U ⊔ V)).hom`. Set `_ : Algebra A Z.functionField` to `(φU.comp (rA p U)).toAlgebra`. Establish `hcU : ∀ a, φU (rA p U a) = algebraMap A Z.functionField a` using `fun a => rfl`. Establish `rL : ∀ x, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x) = φU x` using `fun x => germ_res U (U ⊓ V) inf_le_left x`.

Establish `rR : ∀ x, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op x) = φV x` using `fun x => germ_res V (U ⊓ V) inf_le_right x`. Establish `hcV : ∀ a, φV (rA p V a) = algebraMap A Z.functionField a`. Introduce `a`. Rewrite using `[← hcU a, ← rL, ← rR, rA_res, rA_res]`. Establish `hmul : φU s * φV s' = 1`.

Establish `h` using `congrArg φW hss`. Rewrite `h` using `[map_mul, map_one, rL, rR]`. Conclude with `h`. Establish `ht : φU s ≠ 0` using `left_ne_zero_of_mul_eq_one hmul`. Establish `hs0' : φV s' ≠ 0` using `right_ne_zero_of_mul_eq_one hmul`.

Establish `hs'inv : φV s' = (φU s)⁻¹` using `eq_inv_of_mul_eq_one_right hmul`. Set `B : Subalgebra A Z.functionField` to `{ toSubsemiring := φU.rangeS, algebraMap_mem' := fun a => ⟨rA p U a, hcU a⟩ }`. Set `C : Subalgebra A Z.functionField` to `{ toSubsemiring := φV.rangeS, algebraMap_mem' := fun a => ⟨rA p V a, hcV a⟩ }`. Establish `hWB : φW.range = (AdjoinInv B (φU s)).toSubring` using `range_loc hU s hsU inf_le_left φU φW rL B (fun _ => Iff.rfl) ht ⟨_, (rR s').trans hs'inv⟩`. Establish `hWC : φW.range = (AdjoinInv C (φV s')).toSubring` using `range_loc hV s' hsV inf_le_right φV φW rR C (fun _ => Iff.rfl) hs0' ⟨_, (rL s).trans (by rw [hs'inv, inv_inv])⟩`.

Establish `hglue : AdjoinInv B (φU s) = Algebra.adjoin A ((C : Set Z.functionField) ∪ {φU s})`. Establish `h2` using `Subalgebra.toSubring_injective (hWB.symm.trans hWC)`. Rewrite using `[h2, AdjoinInv, hs'inv, inv_inv]`. Establish `hTop' : (rA p (U ⊔ V)).IsIntegral` using `by rw [hUV]; exact hTop`. Establish `hcT : ∀ a, φT (rA p (U ⊔ V) a) = algebraMap A Z.functionField a`.

Introduce `a`. Rewrite using `[← hcU a, ← rA_res p (le_sup_left : U ≤ U ⊔ V) a]`. Conclude with `(germ_res (U ⊔ V) U le_sup_left _).symm`. Establish `hBC : ∀ x ∈ B, x ∈ C → IsIntegral A x`. Introduce `x hxB hxC`.

Take `⟨u, hu⟩` from `hxB`. Take `⟨v, hv⟩` from `hxC`. Establish `heq : Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op u = Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op v` using `Z.germToFunctionField_injective (U ⊓ V) (((rL u).trans (hu.trans hv.symm)).trans (rR v).symm)`. Set `g` to `(Z.sheaf.objSupIsoProdEqLocus U V).inv ⟨(u, v), heq⟩`. Establish `hg : Z.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op g = u` using `Z.sheaf.objSupIsoProdEqLocus_inv_fst U V _`.

Establish `hx : x = φT g`. Rewrite using `[← hu, ← hg]`. Conclude with `germ_res (U ⊔ V) U le_sup_left g`. Rewrite using `[hx]`. Conclude with `int_A (rA p (U ⊔ V)) hTop' φT hcT g`.

Establish `intB : ∀ b ∈ B, IsIntegral (Algebra.adjoin A {φU s}) b`. Introduce `b hb`. Take `⟨x, rfl⟩` from `hb`. Conclude with `int_adjoin (Polynomial.eval₂RingHom (rA p U) s) hiU φU (φU s) (fun a => by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact hcU a) (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]) x`. Establish `intC : ∀ c ∈ C, IsIntegral (Algebra.adjoin A {(φU s)⁻¹}) c`.

Introduce `c hc`. Take `⟨x, rfl⟩` from `hc`. Conclude with `int_adjoin (Polynomial.eval₂RingHom (rA p V) s') hiV φV (φU s)⁻¹ (fun a => by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact hcV a) (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]; exact hs'inv) x`. Use `⟨Z.functionField, inferInstance, inferInstance, B, C, φU s, ⟨ht, ⟨s, rfl⟩, ⟨s', hs'inv⟩, intB, intC, hglue⟩, hBC, ?_⟩` and prove the remaining obligations. Conclude with `⟨U, V, φU, φV, φW, hU, hV, hsU ▸ hU.basicOpen s, hUV, Z.germToFunctionField_injective U, Z.germToFunctionField_injective V, Z.germToFunctionField_injective (U ⊓ V), SetLike.ext fun _ => Iff.rfl, SetLike.ext fun _ => Iff.rfl, hWB, rL, rR, fun a => rfl, hcV⟩`.
-/
theorem EmbedNonDeg_of : EmbedNonDeg := by
  intro A _ _ Z p hI hTop hN
  obtain ⟨U, V, s, s', hU, hV, hUV, hsU, hsV, ⟨z, hz⟩, hss, hiU, hiV⟩ := hN
  have hzU : z ∈ U := (inf_le_left : U ⊓ V ≤ U) hz
  have hzV : z ∈ V := (inf_le_right : U ⊓ V ≤ V) hz
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  have : Nonempty (U ⊓ V : Z.Opens) := ⟨⟨z, hz⟩⟩
  have : Nonempty (U ⊔ V : Z.Opens) := ⟨⟨z, (le_sup_left : U ≤ U ⊔ V) hzU⟩⟩
  let φU : Γ(Z, U) →+* Z.functionField := (Z.germToFunctionField U).hom
  let φV : Γ(Z, V) →+* Z.functionField := (Z.germToFunctionField V).hom
  let φW : Γ(Z, U ⊓ V) →+* Z.functionField := (Z.germToFunctionField (U ⊓ V)).hom
  let φT : Γ(Z, U ⊔ V) →+* Z.functionField := (Z.germToFunctionField (U ⊔ V)).hom
  let _ : Algebra A Z.functionField := (φU.comp (rA p U)).toAlgebra
  have hcU : ∀ a, φU (rA p U a) = algebraMap A Z.functionField a := fun a => rfl
  have rL : ∀ x, φW (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op x) = φU x :=
    fun x => germ_res U (U ⊓ V) inf_le_left x
  have rR : ∀ x, φW (Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op x) = φV x :=
    fun x => germ_res V (U ⊓ V) inf_le_right x
  have hcV : ∀ a, φV (rA p V a) = algebraMap A Z.functionField a := by
    intro a
    rw [← hcU a, ← rL, ← rR, rA_res, rA_res]
  have hmul : φU s * φV s' = 1 := by
    have h := congrArg φW hss
    rw [map_mul, map_one, rL, rR] at h
    exact h
  have ht : φU s ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hs0' : φV s' ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  have hs'inv : φV s' = (φU s)⁻¹ := eq_inv_of_mul_eq_one_right hmul
  let B : Subalgebra A Z.functionField :=
    { toSubsemiring := φU.rangeS, algebraMap_mem' := fun a => ⟨rA p U a, hcU a⟩ }
  let C : Subalgebra A Z.functionField :=
    { toSubsemiring := φV.rangeS, algebraMap_mem' := fun a => ⟨rA p V a, hcV a⟩ }
  have hWB : φW.range = (AdjoinInv B (φU s)).toSubring :=
    range_loc hU s hsU inf_le_left φU φW rL B (fun _ => Iff.rfl) ht ⟨_, (rR s').trans hs'inv⟩
  have hWC : φW.range = (AdjoinInv C (φV s')).toSubring :=
    range_loc hV s' hsV inf_le_right φV φW rR C (fun _ => Iff.rfl) hs0'
      ⟨_, (rL s).trans (by rw [hs'inv, inv_inv])⟩
  have hglue : AdjoinInv B (φU s) = Algebra.adjoin A ((C : Set Z.functionField) ∪ {φU s}) := by
    have h2 := Subalgebra.toSubring_injective (hWB.symm.trans hWC)
    rw [h2, AdjoinInv, hs'inv, inv_inv]
  have hTop' : (rA p (U ⊔ V)).IsIntegral := by rw [hUV]; exact hTop
  have hcT : ∀ a, φT (rA p (U ⊔ V) a) = algebraMap A Z.functionField a := by
    intro a
    rw [← hcU a, ← rA_res p (le_sup_left : U ≤ U ⊔ V) a]
    exact (germ_res (U ⊔ V) U le_sup_left _).symm
  have hBC : ∀ x ∈ B, x ∈ C → IsIntegral A x := by
    intro x hxB hxC
    obtain ⟨u, hu⟩ := hxB
    obtain ⟨v, hv⟩ := hxC
    have heq : Z.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op u =
        Z.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op v :=
      Z.germToFunctionField_injective (U ⊓ V) (((rL u).trans (hu.trans hv.symm)).trans (rR v).symm)
    let g := (Z.sheaf.objSupIsoProdEqLocus U V).inv ⟨(u, v), heq⟩
    have hg : Z.presheaf.map (homOfLE (le_sup_left : U ≤ U ⊔ V)).op g = u :=
      Z.sheaf.objSupIsoProdEqLocus_inv_fst U V _
    have hx : x = φT g := by
      rw [← hu, ← hg]; exact germ_res (U ⊔ V) U le_sup_left g
    rw [hx]
    exact int_A (rA p (U ⊔ V)) hTop' φT hcT g
  have intB : ∀ b ∈ B, IsIntegral (Algebra.adjoin A {φU s}) b := by
    intro b hb
    obtain ⟨x, rfl⟩ := hb
    exact int_adjoin (Polynomial.eval₂RingHom (rA p U) s) hiU φU (φU s)
      (fun a => by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact hcU a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]) x
  have intC : ∀ c ∈ C, IsIntegral (Algebra.adjoin A {(φU s)⁻¹}) c := by
    intro c hc
    obtain ⟨x, rfl⟩ := hc
    exact int_adjoin (Polynomial.eval₂RingHom (rA p V) s') hiV φV (φU s)⁻¹
      (fun a => by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact hcV a)
      (by rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]; exact hs'inv) x
  refine ⟨Z.functionField, inferInstance, inferInstance, B, C, φU s,
    ⟨ht, ⟨s, rfl⟩, ⟨s', hs'inv⟩, intB, intC, hglue⟩, hBC, ?_⟩
  exact ⟨U, V, φU, φV, φW, hU, hV, hsU ▸ hU.basicOpen s, hUV,
    Z.germToFunctionField_injective U, Z.germToFunctionField_injective V,
    Z.germToFunctionField_injective (U ⊓ V), SetLike.ext fun _ => Iff.rfl, SetLike.ext fun _ => Iff.rfl, hWB,
    rL, rR, fun a => rfl, hcV⟩

end LateralTheory.E.EmbedNonDeg₂
