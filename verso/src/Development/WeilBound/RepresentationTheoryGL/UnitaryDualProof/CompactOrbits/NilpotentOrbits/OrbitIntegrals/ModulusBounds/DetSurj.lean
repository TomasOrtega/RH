import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusBounds.DetEqOfSurj

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Module

namespace PositivityTheory.RgUd.T.Nil.Orb.BModbound

open PositivityTheory.RgUd.T

section Surj

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W] [FiniteDimensional K W]

/- English proof (translation)
Substitute `hP` using the available equality. Rewrite using `[LinearMap.det_eq_det_mul_det (LinearMap.ker L) f hf]`. Use `congr 1`. Use `set e := L.quotKerEquivOfSurjective hL`. Establish `key : (e : (V ⧸ LinearMap.ker L) →ₗ[K] W) ∘ₗ (LinearMap.ker L).mapQ (LinearMap.ker L) f hf = F ∘ₗ (e : (V ⧸ LinearMap.ker L) →ₗ[K] W)`.

Apply `Submodule.linearMap_qext` to reduce the goal to its premises. Use extensionality with `v`. Simplify using `[e, h]`. Establish `hF : F = (e : (V ⧸ LinearMap.ker L) →ₗ[K] W) ∘ₗ (LinearMap.ker L).mapQ (LinearMap.ker L) f hf ∘ₗ (e.symm : W →ₗ[K] (V ⧸ LinearMap.ker L))`. Rewrite using `[← LinearMap.comp_assoc, key, LinearMap.comp_assoc]`.

Use extensionality with `w`. Simplify using the standard rewrite rules. Rewrite using `[hF, LinearMap.det_conj]`.
-/
theorem det_surj (f : V →ₗ[K] V) (F : W →ₗ[K] W) (L : V →ₗ[K] W)
    (hL : Function.Surjective L) (h : ∀ v, L (f v) = F (L v)) (P : Submodule K V) (hP : P = LinearMap.ker L)
    (hf : ∀ y ∈ P, f y ∈ P) : LinearMap.det f = LinearMap.det (f.restrict hf) * LinearMap.det F := by
  subst hP
  rw [LinearMap.det_eq_det_mul_det (LinearMap.ker L) f hf]
  congr 1
  set e := L.quotKerEquivOfSurjective hL
  have key : (e : (V ⧸ LinearMap.ker L) →ₗ[K] W) ∘ₗ (LinearMap.ker L).mapQ (LinearMap.ker L) f hf =
      F ∘ₗ (e : (V ⧸ LinearMap.ker L) →ₗ[K] W) := by
    apply Submodule.linearMap_qext
    ext v
    simp [e, h]
  have hF : F = (e : (V ⧸ LinearMap.ker L) →ₗ[K] W) ∘ₗ (LinearMap.ker L).mapQ (LinearMap.ker L) f hf ∘ₗ
      (e.symm : W →ₗ[K] (V ⧸ LinearMap.ker L)) := by
    rw [← LinearMap.comp_assoc, key, LinearMap.comp_assoc]
    ext w
    simp
  rw [hF, LinearMap.det_conj]

end Surj

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Establish `hu : IsUnit F` using `(LinearMap.isUnit_iff_isUnit_det F).mpr (by rw [hdet]; exact isUnit_one)`. Establish `hFinj : Function.Injective F` using `((Module.End.isUnit_iff F).mp hu).1`. Establish `hFKinj : Function.Injective (F.restrict hK)`. Introduce `a b hab`. Conclude with `Subtype.ext (hFinj (congrArg Subtype.val hab))`.

Use `set eK := LinearEquiv.ofInjectiveEndo (F.restrict hK) hFKinj with heK`. Establish `hI : ∀ y ∈ LinearMap.range D, F y ∈ LinearMap.range D`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `⟨t • F w, by rw [map_smul, hFD]⟩`. Establish `htK : ∀ y ∈ LinearMap.ker D, (t • F) y ∈ LinearMap.ker D` using `fun y hy => Submodule.smul_mem _ t (hK y hy)`.

Establish `h3` using `det_surj (t • F) (F.restrict hI) D.rangeRestrict D.surjective_rangeRestrict (fun v => Subtype.ext (by show D ((t • F) v) = F (D v)`. Rewrite using `[LinearMap.smul_apply, map_smul, hFD])) (LinearMap.ker D)`. Use the proof step `(LinearMap.ker_rangeRestrict D).symm htK`. Establish `hres : (t • F).restrict htK = t • F.restrict hK` using `LinearMap.ext fun y => rfl`. Rewrite `h3` using `[hres, LinearMap.det_smul, LinearMap.det_smul, hdet]`.

Set `ψ' : ↥(LinearMap.ker D) →ₗ[K] Module.Dual K W` to `B.flip ∘ₗ (LinearMap.ker D).subtype`. Establish `hψ'inj : Function.Injective ψ'`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `b hb`. Conclude with `Subtype.ext (hnd b (fun a => LinearMap.congr_fun hb a))`.

Set `ψ : W →ₗ[K] Module.Dual K ↥(LinearMap.ker D)` to `ψ'.dualMap ∘ₗ (Module.evalEquiv K W).toLinearMap`. Establish `hψ : ∀ w b, ψ w b = B w b` using `fun w b => rfl`. Establish `hψsurj : Function.Surjective ψ` using `(LinearMap.dualMap_surjective_of_injective hψ'inj).comp (Module.evalEquiv K W).surjective`. Establish `hfψ : ∀ w, ψ (F w) = (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)).dualMap (ψ w)`. Introduce `w`.

Use extensionality with `b`. Rewrite using `[LinearMap.dualMap_apply, hψ, hψ]`. Establish `hb : (b : W) = F ((eK.symm b : ↥(LinearMap.ker D)) : W)` using `congrArg Subtype.val (eK.apply_symm_apply b).symm`. Rewrite using `[hb]`. Conclude with `hB w _`.

Establish `hker : LinearMap.ker ψ = LinearMap.range D`. Use `symm`. Apply `Submodule.eq_of_le_of_finrank_eq` to reduce the goal to its premises. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[LinearMap.mem_ker]`.

Use extensionality with `b`. Rewrite using `[hψ, LinearMap.zero_apply]`. Conclude with `hBD a b (LinearMap.mem_ker.mp b.2)`. Establish `e1` using `LinearMap.finrank_range_add_finrank_ker ψ`. Establish `e2` using `LinearMap.finrank_range_add_finrank_ker D`.

Rewrite `e1` using `[LinearMap.range_eq_top.mpr hψsurj, finrank_top, Subspace.dual_finrank_eq]`. Use linear arithmetic over natural numbers and integers. Establish `h4` using `det_surj F ((eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)).dualMap) ψ hψsurj hfψ (LinearMap.range D) hker.symm hI`. Rewrite `h4` using `[LinearMap.det_dualMap, hdet]`. Establish `hs : LinearMap.det (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)) * LinearMap.det (F.restrict hK) = 1`.

Rewrite using `[← LinearMap.det_comp]`. Establish `hid : (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)) ∘ₗ F.restrict hK = LinearMap.id` using `LinearMap.ext fun y => eK.symm_apply_apply y`. Rewrite using `[hid, LinearMap.det_id]`. Establish `hdI : LinearMap.det (F.restrict hI) = LinearMap.det (F.restrict hK)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite `h3` using `[hdI]`. Rewrite using `[pow_sub₀ t ht (Submodule.finrank_le _), eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ ht)]`. Take the linear combination `-h3`.
-/
private theorem det_sq_lemma {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (F D : W →ₗ[K] W) (B : W →ₗ[K] W →ₗ[K] K) (t : K) (ht : t ≠ 0)
    (hFD : ∀ w, F (D w) = t • D (F w)) (hB : ∀ a b, B (F a) (F b) = B a b)
    (hBD : ∀ a b, D b = 0 → B (D a) b = 0) (hnd : ∀ b, (∀ a, B a b = 0) → b = 0)
    (hdet : LinearMap.det F = 1) (hK : ∀ y ∈ LinearMap.ker D, F y ∈ LinearMap.ker D) :
    LinearMap.det (F.restrict hK) ^ 2 = t ^ (finrank K W - finrank K (LinearMap.ker D)) := by
  have hu : IsUnit F := (LinearMap.isUnit_iff_isUnit_det F).mpr (by rw [hdet]; exact isUnit_one)
  have hFinj : Function.Injective F := ((Module.End.isUnit_iff F).mp hu).1
  have hFKinj : Function.Injective (F.restrict hK) := by
    intro a b hab
    exact Subtype.ext (hFinj (congrArg Subtype.val hab))
  set eK := LinearEquiv.ofInjectiveEndo (F.restrict hK) hFKinj with heK
  have hI : ∀ y ∈ LinearMap.range D, F y ∈ LinearMap.range D := by
    rintro _ ⟨w, rfl⟩
    exact ⟨t • F w, by rw [map_smul, hFD]⟩
  have htK : ∀ y ∈ LinearMap.ker D, (t • F) y ∈ LinearMap.ker D := fun y hy =>
    Submodule.smul_mem _ t (hK y hy)
  have h3 := det_surj (t • F) (F.restrict hI) D.rangeRestrict D.surjective_rangeRestrict
    (fun v => Subtype.ext (by
      show D ((t • F) v) = F (D v)
      rw [LinearMap.smul_apply, map_smul, hFD])) (LinearMap.ker D)
    (LinearMap.ker_rangeRestrict D).symm htK
  have hres : (t • F).restrict htK = t • F.restrict hK := LinearMap.ext fun y => rfl
  rw [hres, LinearMap.det_smul, LinearMap.det_smul, hdet] at h3
  let ψ' : ↥(LinearMap.ker D) →ₗ[K] Module.Dual K W := B.flip ∘ₗ (LinearMap.ker D).subtype
  have hψ'inj : Function.Injective ψ' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro b hb
    exact Subtype.ext (hnd b (fun a => LinearMap.congr_fun hb a))
  let ψ : W →ₗ[K] Module.Dual K ↥(LinearMap.ker D) :=
    ψ'.dualMap ∘ₗ (Module.evalEquiv K W).toLinearMap
  have hψ : ∀ w b, ψ w b = B w b := fun w b => rfl
  have hψsurj : Function.Surjective ψ :=
    (LinearMap.dualMap_surjective_of_injective hψ'inj).comp (Module.evalEquiv K W).surjective
  have hfψ : ∀ w, ψ (F w) = (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)).dualMap (ψ w) := by
    intro w
    ext b
    rw [LinearMap.dualMap_apply, hψ, hψ]
    have hb : (b : W) = F ((eK.symm b : ↥(LinearMap.ker D)) : W) :=
      congrArg Subtype.val (eK.apply_symm_apply b).symm
    rw [hb]
    exact hB w _
  have hker : LinearMap.ker ψ = LinearMap.range D := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      ext b
      rw [hψ, LinearMap.zero_apply]
      exact hBD a b (LinearMap.mem_ker.mp b.2)
    · have e1 := LinearMap.finrank_range_add_finrank_ker ψ
      have e2 := LinearMap.finrank_range_add_finrank_ker D
      rw [LinearMap.range_eq_top.mpr hψsurj, finrank_top, Subspace.dual_finrank_eq] at e1
      omega
  have h4 := det_surj F ((eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)).dualMap) ψ hψsurj hfψ
    (LinearMap.range D) hker.symm hI
  rw [LinearMap.det_dualMap, hdet] at h4
  have hs : LinearMap.det (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)) *
      LinearMap.det (F.restrict hK) = 1 := by
    rw [← LinearMap.det_comp]
    have hid : (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)) ∘ₗ F.restrict hK = LinearMap.id :=
      LinearMap.ext fun y => eK.symm_apply_apply y
    rw [hid, LinearMap.det_id]
  have hdI : LinearMap.det (F.restrict hI) = LinearMap.det (F.restrict hK) := by
    calc LinearMap.det (F.restrict hI)
        = LinearMap.det (F.restrict hI) * (LinearMap.det (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D)) *
          LinearMap.det (F.restrict hK)) := by rw [hs, mul_one]
      _ = (LinearMap.det (F.restrict hI) * LinearMap.det (eK.symm : ↥(LinearMap.ker D) →ₗ[K] ↥(LinearMap.ker D))) *
          LinearMap.det (F.restrict hK) := by ring
      _ = LinearMap.det (F.restrict hK) := by rw [← h4, one_mul]
  rw [hdI] at h3
  rw [pow_sub₀ t ht (Submodule.finrank_le _), eq_mul_inv_iff_mul_eq₀ (pow_ne_zero _ ht)]
  linear_combination -h3

/- English proof (translation)
Set `φ : Matrix (Fin n) (Fin n) k →ₐ[k] Module.End k (Fin n → k)` to `(Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom`. Set `Z'` to `Z.map φ`. Establish `hcomm : ∀ a c : Z', a * c = c * a`. Introduce and unpack `⟨_, z1, hz1, rfl⟩ ⟨_, z2, hz2, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show φ z1 * φ z2 = φ z2 * φ z1`. Rewrite using `[← map_mul, ← map_mul, hZ.1 z1 hz1 z2 hz2]`. Use `letI : CommRing Z' := { (inferInstance : Ring Z') with mul_comm := hcomm }`. Use `haveI : IsReduced Z' := by`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, z, hz, rfl⟩ ⟨m, hm⟩`. Establish `hzm : (⟨z, hz⟩ : Z) ^ m = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `(Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).injective` to reduce the goal to its premises. Establish `h1` using `congrArg Subtype.val hm`.

Simplify `h1` using `[φ]`. Establish `h2` using `hZ.2.eq_zero _ ⟨m, hzm⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h3 : z = 0` using `congrArg Subtype.val h2`. Simplify using `[h3]`.

Use `haveI : IsArtinianRing Z' := IsArtinianRing.of_finite k Z'`. Use `haveI : IsSemisimpleRing Z' := IsArtinianRing.isSemisimpleRing_of_isReduced Z'`. Conclude with `inferInstance`.
-/
private theorem det_sq_lemma_3 (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    IsSemisimpleModule ↥(Z.map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k]
      Module.End k (Fin n → k)).toAlgHom) (Fin n → k) := by
  let φ : Matrix (Fin n) (Fin n) k →ₐ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom
  let Z' := Z.map φ
  have hcomm : ∀ a c : Z', a * c = c * a := by
    rintro ⟨_, z1, hz1, rfl⟩ ⟨_, z2, hz2, rfl⟩
    apply Subtype.ext
    show φ z1 * φ z2 = φ z2 * φ z1
    rw [← map_mul, ← map_mul, hZ.1 z1 hz1 z2 hz2]
  letI : CommRing Z' := { (inferInstance : Ring Z') with mul_comm := hcomm }
  haveI : IsReduced Z' := by
    constructor
    rintro ⟨_, z, hz, rfl⟩ ⟨m, hm⟩
    have hzm : (⟨z, hz⟩ : Z) ^ m = 0 := by
      apply Subtype.ext
      apply (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).injective
      have h1 := congrArg Subtype.val hm
      simpa [φ] using h1
    have h2 := hZ.2.eq_zero _ ⟨m, hzm⟩
    apply Subtype.ext
    have h3 : z = 0 := congrArg Subtype.val h2
    simp [h3]
  haveI : IsArtinianRing Z' := IsArtinianRing.of_finite k Z'
  haveI : IsSemisimpleRing Z' := IsArtinianRing.isSemisimpleRing_of_isReduced Z'
  exact inferInstance

/- English proof (translation)
Assume the negation of the conclusion as `hb0`. Set `φ : Matrix (Fin n) (Fin n) k →ₐ[k] Module.End k (Fin n → k)` to `(Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom`. Establish `hφ : ∀ z v, φ z v = z *ᵥ v` using `fun z v => rfl`. Set `Z'` to `Z.map φ`. Use `haveI : IsSemisimpleModule Z' (Fin n → k) := det_sq_lemma_3 Z hZ`.

Establish `hzb : ∀ z ∈ Z, z * b = b * z` using `fun z hz => (Subalgebra.mem_centralizer_iff k).mp hb z hz`. Set `β : (Fin n → k) →ₗ[Z'] (Fin n → k)` to `{ toFun := fun v => b *ᵥ v map_add' := fun u v => Matrix.mulVec_add b u v map_smul' := by`. Introduce and unpack `⟨_, z, hz, rfl⟩ v`. Use `show b *ᵥ (φ z v) = φ z (b *ᵥ v)`. Rewrite using `[hφ, hφ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hzb z hz] }`.

Establish `hβ : ∀ v, β v = b *ᵥ v` using `fun v => rfl`. Establish `hβ0 : β ≠ 0`. Introduce `h0`. Apply `hb0` to reduce the goal to its premises. Apply `Matrix.toLin'.injective` to reduce the goal to its premises.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use `LinearMap.congr_fun h0 v` as an intermediate fact. Rewrite `this` using `[hβ]`. Simplify `this` using `[Matrix.toLin'_apply]`.

Take `⟨Wc, hWc⟩` from `exists_isCompl (LinearMap.ker β)`. Take `⟨U, hU⟩` from `exists_isCompl (LinearMap.range β)`. Set `σ : ↥Wc ≃ₗ[Z'] ↥(LinearMap.range β)` to `(Submodule.quotientEquivOfIsCompl _ _ hWc).symm.trans β.quotKerEquivRange`. Establish `hσ : ∀ w : ↥Wc, ((σ w : ↥(LinearMap.range β)) : Fin n → k) = β w`. Introduce `w`.

Simplify using `[σ, Submodule.quotientEquivOfIsCompl_symm_apply, LinearMap.quotKerEquivRange_apply_mk]`. Set `π` to `(LinearMap.range β).projectionOnto U hU`. Set `pW` to `Wc.projectionOnto (LinearMap.ker β) hWc.symm`. Set `A : (Fin n → k) →ₗ[Z'] (Fin n → k)` to `Wc.subtype ∘ₗ (σ.symm : _ →ₗ[Z'] _) ∘ₗ π`. Set `P : (Fin n → k) →ₗ[Z'] (Fin n → k)` to `Wc.subtype ∘ₗ pW`.

Establish `hAP : A ∘ₗ β = P`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Use `show ((σ.symm (π (β v)) : ↥Wc) : Fin n → k) = (pW v : Fin n → k)`. Use `congr 1`.

Rewrite using `[LinearEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h1 : ((π (β v) : ↥(LinearMap.range β)) : Fin n → k) = β v` using `congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨β v, LinearMap.mem_range_self β v⟩)`. Rewrite using `[h1, hσ]`. Establish `hsplit` using `Submodule.projection_add_projection_eq_self hWc.symm v`.

Establish `hk : β ((LinearMap.ker β).projection Wc hWc.symm.symm v) = 0` using `LinearMap.mem_ker.mp (Submodule.projection_apply_mem _ v)`. Use `conv_lhs => rw [← hsplit]`. Rewrite using `[map_add, hk, add_zero]`. Both sides reduce to the same expression. Set `Pk : (Fin n → k) →ₗ[k] (Fin n → k)` to `P.restrictScalars k`.

Establish `hPk : ∀ v, Pk v = P v` using `fun v => rfl`. Establish `hPidem : IsIdempotentElem Pk`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Conclude with `congrArg Subtype.val (Submodule.projectionOnto_apply_left hWc.symm (pW v))`.

Establish `hWc0 : Wc ≠ ⊥`. Introduce `hW`. Apply `hβ0` to reduce the goal to its premises. Establish `htop` using `hWc.sup_eq_top`. Rewrite `htop` using `[hW, sup_bot_eq]`.

Conclude with `LinearMap.ker_eq_top.mp htop`. Establish `hP0 : Pk ≠ 0`. Introduce `hP`. Take `⟨w, hw, hw0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hWc0`. Apply `hw0` to reduce the goal to its premises.

Establish `h1` using `LinearMap.congr_fun hP w`. Establish `h2 : ((pW w : ↥Wc) : Fin n → k) = w` using `congrArg Subtype.val (Submodule.projectionOnto_apply_left hWc.symm ⟨w, hw⟩)`. Rewrite using `[← h2]`. Conclude with `h1`. Establish `htrP : LinearMap.trace k (Fin n → k) Pk ≠ 0` using `fun ht0 => hP0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hPidem).mp ht0)`.

Set `Ak : (Fin n → k) →ₗ[k] (Fin n → k)` to `A.restrictScalars k`. Set `a` to `LinearMap.toMatrix' Ak`. Establish `ha : a ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))`. Rewrite using `[Subalgebra.mem_centralizer_iff]`. Introduce `z hz`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Establish `hs` using `A.map_smul (⟨φ z, Subalgebra.mem_map.mpr ⟨z, hz, rfl⟩⟩ : Z') v`.

Express the relevant statement in the definitionally equal form `A (φ z v) = φ z (A v) at hs`. Use `show Matrix.toLin' z (A v) = A (Matrix.toLin' z v)`. Rewrite using `[Matrix.toLin'_apply, Matrix.toLin'_apply, ← hφ, ← hφ, hs]`. Establish `htr : Matrix.trace (a * b) = LinearMap.trace k (Fin n → k) Pk`. Rewrite using `[LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix']`.

Use `congr 1`. Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Use `show A (β v) = P v`. Rewrite using `[← hAP]`. Both sides reduce to the same expression. Conclude with `htrP (htr ▸ h a ha)`.
-/
private theorem det_sq_lemma_2 [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)
    (b : Matrix (Fin n) (Fin n) k) (hb : b ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)))
    (h : ∀ a ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)), Matrix.trace (a * b) = 0) :
    b = 0 := by
  classical
  by_contra hb0
  let φ : Matrix (Fin n) (Fin n) k →ₐ[k] Module.End k (Fin n → k) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k)).toAlgHom
  have hφ : ∀ z v, φ z v = z *ᵥ v := fun z v => rfl
  let Z' := Z.map φ
  haveI : IsSemisimpleModule Z' (Fin n → k) := det_sq_lemma_3 Z hZ
  have hzb : ∀ z ∈ Z, z * b = b * z := fun z hz => (Subalgebra.mem_centralizer_iff k).mp hb z hz
  let β : (Fin n → k) →ₗ[Z'] (Fin n → k) :=
    { toFun := fun v => b *ᵥ v
      map_add' := fun u v => Matrix.mulVec_add b u v
      map_smul' := by
        rintro ⟨_, z, hz, rfl⟩ v
        show b *ᵥ (φ z v) = φ z (b *ᵥ v)
        rw [hφ, hφ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hzb z hz] }
  have hβ : ∀ v, β v = b *ᵥ v := fun v => rfl
  have hβ0 : β ≠ 0 := by
    intro h0
    apply hb0
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    have := LinearMap.congr_fun h0 v
    rw [hβ] at this
    simpa [Matrix.toLin'_apply] using this
  obtain ⟨Wc, hWc⟩ := exists_isCompl (LinearMap.ker β)
  obtain ⟨U, hU⟩ := exists_isCompl (LinearMap.range β)
  let σ : ↥Wc ≃ₗ[Z'] ↥(LinearMap.range β) :=
    (Submodule.quotientEquivOfIsCompl _ _ hWc).symm.trans β.quotKerEquivRange
  have hσ : ∀ w : ↥Wc, ((σ w : ↥(LinearMap.range β)) : Fin n → k) = β w := by
    intro w
    simp [σ, Submodule.quotientEquivOfIsCompl_symm_apply, LinearMap.quotKerEquivRange_apply_mk]
  let π := (LinearMap.range β).projectionOnto U hU
  let pW := Wc.projectionOnto (LinearMap.ker β) hWc.symm
  let A : (Fin n → k) →ₗ[Z'] (Fin n → k) := Wc.subtype ∘ₗ (σ.symm : _ →ₗ[Z'] _) ∘ₗ π
  let P : (Fin n → k) →ₗ[Z'] (Fin n → k) := Wc.subtype ∘ₗ pW
  have hAP : A ∘ₗ β = P := by
    apply LinearMap.ext
    intro v
    show ((σ.symm (π (β v)) : ↥Wc) : Fin n → k) = (pW v : Fin n → k)
    congr 1
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    have h1 : ((π (β v) : ↥(LinearMap.range β)) : Fin n → k) = β v :=
      congrArg Subtype.val (Submodule.projectionOnto_apply_left hU ⟨β v, LinearMap.mem_range_self β v⟩)
    rw [h1, hσ]
    have hsplit := Submodule.projection_add_projection_eq_self hWc.symm v
    have hk : β ((LinearMap.ker β).projection Wc hWc.symm.symm v) = 0 :=
      LinearMap.mem_ker.mp (Submodule.projection_apply_mem _ v)
    conv_lhs => rw [← hsplit]
    rw [map_add, hk, add_zero]
    rfl
  let Pk : (Fin n → k) →ₗ[k] (Fin n → k) := P.restrictScalars k
  have hPk : ∀ v, Pk v = P v := fun v => rfl
  have hPidem : IsIdempotentElem Pk := by
    apply LinearMap.ext
    intro v
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hWc.symm (pW v))
  have hWc0 : Wc ≠ ⊥ := by
    intro hW
    apply hβ0
    have htop := hWc.sup_eq_top
    rw [hW, sup_bot_eq] at htop
    exact LinearMap.ker_eq_top.mp htop
  have hP0 : Pk ≠ 0 := by
    intro hP
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWc0
    apply hw0
    have h1 := LinearMap.congr_fun hP w
    have h2 : ((pW w : ↥Wc) : Fin n → k) = w :=
      congrArg Subtype.val (Submodule.projectionOnto_apply_left hWc.symm ⟨w, hw⟩)
    rw [← h2]
    exact h1
  have htrP : LinearMap.trace k (Fin n → k) Pk ≠ 0 :=
    fun ht0 => hP0 ((LinearMap.IsIdempotentElem.trace_eq_zero_iff hPidem).mp ht0)
  let Ak : (Fin n → k) →ₗ[k] (Fin n → k) := A.restrictScalars k
  let a := LinearMap.toMatrix' Ak
  have ha : a ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) := by
    rw [Subalgebra.mem_centralizer_iff]
    intro z hz
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    have hs := A.map_smul (⟨φ z, Subalgebra.mem_map.mpr ⟨z, hz, rfl⟩⟩ : Z') v
    change A (φ z v) = φ z (A v) at hs
    show Matrix.toLin' z (A v) = A (Matrix.toLin' z v)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← hφ, ← hφ, hs]
  have htr : Matrix.trace (a * b) = LinearMap.trace k (Fin n → k) Pk := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix']
    congr 1
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    show A (β v) = P v
    rw [← hAP]
    rfl
  exact htrP (htr ▸ h a ha)

/- English proof (translation)
Establish `hxC : x ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))` using `(Subalgebra.mem_centralizer_iff k).mpr (fun a ha => hx a ha)`. Use `set S := Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) with hS`. Use `set C := Subalgebra.toSubmodule S with hC`. Set `Dx : Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k` to `LinearMap.mulRight k x - LinearMap.mulLeft k x`. Establish `hDx : ∀ y, Dx y = y * x - x * y` using `fun y => rfl`.

Establish `hDC : ∀ y ∈ C, Dx y ∈ C` using `fun y hy => by`. Rewrite using `[hDx]`. Conclude with `S.sub_mem (S.mul_mem hy hxC) (S.mul_mem hxC hy)`. Set `F` to `(adL g).restrict (cC_inv Z g hg)`. Set `D` to `Dx.restrict hDC`.

Set `B : ↥C →ₗ[k] ↥C →ₗ[k] k` to `((LinearMap.mul k (Matrix (Fin n) (Fin n) k)).compr₂ (Matrix.traceLinearMap (Fin n) k k)).compl₁₂ C.subtype C.subtype`. Establish `hBapp : ∀ a b : ↥C, B a b = Matrix.trace ((a : Matrix (Fin n) (Fin n) k) * (b : Matrix (Fin n) (Fin n) k))` using `fun a b => rfl`. Establish `hFD : ∀ w, F (D w) = t • D (F w)`. Introduce `w`. Apply `Subtype.ext` to reduce the goal to its premises.

Use `show adL g ((w : Matrix (Fin n) (Fin n) k) * x - x * (w : Matrix (Fin n) (Fin n) k)) = t • (adL g (w : Matrix (Fin n) (Fin n) k) * x - x * adL g (w : Matrix (Fin n) (Fin n) k))`. Rewrite using `[adL_apply, adL_apply]`. Establish `e2 : ∀ P : Matrix (Fin n) (Fin n) k, t • (P * x - x * P) = P * (t • x) - (t • x) * P`. Introduce `P`. Rewrite using `[smul_sub, mul_smul_comm, smul_mul_assoc]`.

Rewrite using `[e2, ← hgx]`. Simplify using `only [mul_assoc, mul_sub, sub_mul, Units.inv_mul_cancel_left]`. Establish `hB : ∀ a b, B (F a) (F b) = B a b`. Introduce `a b`. Rewrite using `[hBapp, hBapp]`.

Use `show Matrix.trace (adL g (a : Matrix (Fin n) (Fin n) k) * adL g (b : Matrix (Fin n) (Fin n) k)) = Matrix.trace ((a : Matrix (Fin n) (Fin n) k) * (b : Matrix (Fin n) (Fin n) k))`. Rewrite using `[adL_apply, adL_apply]`. Simplify using `only [mul_assoc, Units.inv_mul_cancel_left]`. Rewrite using `[Matrix.trace_mul_comm]`. Simplify using `only [mul_assoc, Units.inv_mul, mul_one]`.

Establish `hBD : ∀ a b, D b = 0 → B (D a) b = 0`. Introduce `a b hb`. Establish `h0 : (b : Matrix (Fin n) (Fin n) k) * x - x * (b : Matrix (Fin n) (Fin n) k) = 0` using `congrArg Subtype.val hb`. Establish `hb' : (b : Matrix (Fin n) (Fin n) k) * x = x * (b : Matrix (Fin n) (Fin n) k)` using `sub_eq_zero.mp h0`. Rewrite using `[hBapp]`.

Use `show Matrix.trace (((a : Matrix (Fin n) (Fin n) k) * x - x * (a : Matrix (Fin n) (Fin n) k)) * (b : Matrix (Fin n) (Fin n) k)) = 0`. Rewrite using `[sub_mul, Matrix.trace_sub, sub_eq_zero, mul_assoc x, Matrix.trace_mul_comm x, mul_assoc (a : Matrix (Fin n) (Fin n) k) (b : Matrix (Fin n) (Fin n) k), hb', ← mul_assoc]`. Establish `hnd : ∀ b, (∀ a, B a b = 0) → b = 0`. Introduce `b h`. Apply `Subtype.ext` to reduce the goal to its premises.

Conclude with `det_sq_lemma_2 Z hZ b b.2 (fun a ha => h ⟨a, ha⟩)`. Establish `hK : ∀ y ∈ LinearMap.ker D, F y ∈ LinearMap.ker D`. Introduce `y hy`. Rewrite `hy`, the goal using `[LinearMap.mem_ker]`. Use `hFD y` as an intermediate fact.

Rewrite `this` using `[hy, map_zero]`. Conclude with `(smul_eq_zero.mp this.symm).resolve_left ht`. Establish `key` using `det_sq_lemma F D B t ht hFD hB hBD hnd (det_C Z hZ g hg) hK`. Establish `hmap : (LinearMap.ker D).map C.subtype = cA Z x`. Use extensionality with `y`.

Simplify using `only [Submodule.mem_map, LinearMap.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Establish `h0 : (z : Matrix (Fin n) (Fin n) k) * x - x * (z : Matrix (Fin n) (Fin n) k) = 0` using `congrArg Subtype.val hz`. Conclude with `⟨fun a ha => (Subalgebra.mem_centralizer_iff k).mp z.2 a ha, sub_eq_zero.mp h0⟩`.

Introduce and unpack `⟨hyB, hyx⟩`. Establish `hyC : y ∈ C` using `(Subalgebra.mem_centralizer_iff k).mpr (fun a ha => hyB a ha)`. Conclude with `⟨⟨y, hyC⟩, Subtype.ext (sub_eq_zero.mpr hyx), rfl⟩`. Set `e : ↥(LinearMap.ker D) ≃ₗ[k] ↥(cA Z x)` to `(Submodule.equivMapOfInjective C.subtype C.injective_subtype (LinearMap.ker D)).trans (LinearEquiv.ofEq _ _ hmap)`. Establish `hG : (adL g).restrict (cA_inv Z x g hg t ht hgx) = (e : ↥(LinearMap.ker D) →ₗ[k] ↥(cA Z x)) ∘ₗ F.restrict hK ∘ₗ (e.symm : ↥(cA Z x) →ₗ[k] ↥(LinearMap.ker D))`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `y`. Take `⟨z, rfl⟩` from `e.surjective y`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`. Both sides reduce to the same expression.

Establish `hfr : finrank k ↥S = finrank k ↥C` using `rfl`. Rewrite using `[hG, LinearMap.det_conj, ← LinearEquiv.finrank_eq e, hfr]`. Conclude with `key`.
-/
theorem det_sq [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (x : Matrix (Fin n) (Fin n) k)
    (hx : x ∈ Bz Z) (g : GL (Fin n) k) (hg : g ∈ Gz Z) (t : k) (ht : t ≠ 0) (hgx : g.val * x * g⁻¹.val = t • x) :
    (LinearMap.det ((adL g).restrict (cA_inv Z x g hg t ht hgx))) ^ 2 =
      t ^ (finrank k (Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k))) - finrank k (cA Z x)) := by
  have hxC : x ∈ Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) :=
    (Subalgebra.mem_centralizer_iff k).mpr (fun a ha => hx a ha)
  set S := Subalgebra.centralizer k (Z : Set (Matrix (Fin n) (Fin n) k)) with hS
  set C := Subalgebra.toSubmodule S with hC
  let Dx : Matrix (Fin n) (Fin n) k →ₗ[k] Matrix (Fin n) (Fin n) k :=
    LinearMap.mulRight k x - LinearMap.mulLeft k x
  have hDx : ∀ y, Dx y = y * x - x * y := fun y => rfl
  have hDC : ∀ y ∈ C, Dx y ∈ C := fun y hy => by
    rw [hDx]
    exact S.sub_mem (S.mul_mem hy hxC) (S.mul_mem hxC hy)
  let F := (adL g).restrict (cC_inv Z g hg)
  let D := Dx.restrict hDC
  let B : ↥C →ₗ[k] ↥C →ₗ[k] k :=
    ((LinearMap.mul k (Matrix (Fin n) (Fin n) k)).compr₂ (Matrix.traceLinearMap (Fin n) k k)).compl₁₂
      C.subtype C.subtype
  have hBapp : ∀ a b : ↥C, B a b = Matrix.trace ((a : Matrix (Fin n) (Fin n) k) * (b : Matrix (Fin n) (Fin n) k)) := fun a b => rfl
  have hFD : ∀ w, F (D w) = t • D (F w) := by
    intro w
    apply Subtype.ext
    show adL g ((w : Matrix (Fin n) (Fin n) k) * x - x * (w : Matrix (Fin n) (Fin n) k)) = t • (adL g (w : Matrix (Fin n) (Fin n) k) * x - x * adL g (w : Matrix (Fin n) (Fin n) k))
    rw [adL_apply, adL_apply]
    have e2 : ∀ P : Matrix (Fin n) (Fin n) k, t • (P * x - x * P) = P * (t • x) - (t • x) * P := by
      intro P
      rw [smul_sub, mul_smul_comm, smul_mul_assoc]
    rw [e2, ← hgx]
    simp only [mul_assoc, mul_sub, sub_mul, Units.inv_mul_cancel_left]
  have hB : ∀ a b, B (F a) (F b) = B a b := by
    intro a b
    rw [hBapp, hBapp]
    show Matrix.trace (adL g (a : Matrix (Fin n) (Fin n) k) * adL g (b : Matrix (Fin n) (Fin n) k)) = Matrix.trace ((a : Matrix (Fin n) (Fin n) k) * (b : Matrix (Fin n) (Fin n) k))
    rw [adL_apply, adL_apply]
    simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [Matrix.trace_mul_comm]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  have hBD : ∀ a b, D b = 0 → B (D a) b = 0 := by
    intro a b hb
    have h0 : (b : Matrix (Fin n) (Fin n) k) * x - x * (b : Matrix (Fin n) (Fin n) k) = 0 := congrArg Subtype.val hb
    have hb' : (b : Matrix (Fin n) (Fin n) k) * x = x * (b : Matrix (Fin n) (Fin n) k) := sub_eq_zero.mp h0
    rw [hBapp]
    show Matrix.trace (((a : Matrix (Fin n) (Fin n) k) * x - x * (a : Matrix (Fin n) (Fin n) k)) * (b : Matrix (Fin n) (Fin n) k)) = 0
    rw [sub_mul, Matrix.trace_sub, sub_eq_zero, mul_assoc x, Matrix.trace_mul_comm x,
      mul_assoc (a : Matrix (Fin n) (Fin n) k) (b : Matrix (Fin n) (Fin n) k), hb', ← mul_assoc]
  have hnd : ∀ b, (∀ a, B a b = 0) → b = 0 := by
    intro b h
    apply Subtype.ext
    exact det_sq_lemma_2 Z hZ b b.2 (fun a ha => h ⟨a, ha⟩)
  have hK : ∀ y ∈ LinearMap.ker D, F y ∈ LinearMap.ker D := by
    intro y hy
    rw [LinearMap.mem_ker] at hy ⊢
    have := hFD y
    rw [hy, map_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left ht
  have key := det_sq_lemma F D B t ht hFD hB hBD hnd (det_C Z hZ g hg) hK
  have hmap : (LinearMap.ker D).map C.subtype = cA Z x := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h0 : (z : Matrix (Fin n) (Fin n) k) * x - x * (z : Matrix (Fin n) (Fin n) k) = 0 := congrArg Subtype.val hz
      exact ⟨fun a ha => (Subalgebra.mem_centralizer_iff k).mp z.2 a ha, sub_eq_zero.mp h0⟩
    · rintro ⟨hyB, hyx⟩
      have hyC : y ∈ C := (Subalgebra.mem_centralizer_iff k).mpr (fun a ha => hyB a ha)
      exact ⟨⟨y, hyC⟩, Subtype.ext (sub_eq_zero.mpr hyx), rfl⟩
  let e : ↥(LinearMap.ker D) ≃ₗ[k] ↥(cA Z x) :=
    (Submodule.equivMapOfInjective C.subtype C.injective_subtype (LinearMap.ker D)).trans
      (LinearEquiv.ofEq _ _ hmap)
  have hG : (adL g).restrict (cA_inv Z x g hg t ht hgx) =
      (e : ↥(LinearMap.ker D) →ₗ[k] ↥(cA Z x)) ∘ₗ F.restrict hK ∘ₗ
        (e.symm : ↥(cA Z x) →ₗ[k] ↥(LinearMap.ker D)) := by
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rfl
  have hfr : finrank k ↥S = finrank k ↥C := rfl
  rw [hG, LinearMap.det_conj, ← LinearEquiv.finrank_eq e, hfr]
  exact key
