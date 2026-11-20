import Mathlib
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.Complexify

open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset

namespace GlobalTheory.QuotCoord

/- English proof (translation)
Set `W` to `U.comap U'.subtype`. Set `e : (U' ⧸ W) ≃ₗ[K] (Fin (Module.finrank K (U' ⧸ W)) → K)` to `(Module.finBasis K (U' ⧸ W)).equivFun`. Take `⟨g, hg⟩` from `LinearMap.exists_extend (e.toLinearMap ∘ₗ W.mkQ)`. Establish `hg' : ∀ y : U', g y = e (W.mkQ y)` using `fun y => LinearMap.congr_fun hg y`. Use `⟨_, LinearMap.toMatrix' g, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← (Submodule.comapSubtypeEquivOfLe h).finrank_eq]`. Conclude with `Submodule.finrank_quotient_add_finrank W`. Introduce `y hy`. Rewrite using `[LinearMap.toMatrix'_mulVec, hg' ⟨y, hy⟩, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Both sides reduce to the same expression.

Rewrite using `[Matrix.toLin'_toMatrix', eq_top_iff]`. Introduce `z _`. Take `⟨y, hy⟩` from `W.mkQ_surjective (e.symm z)`. Conclude with `⟨y, y.2, by rw [hg', hy, LinearEquiv.apply_symm_apply]⟩`.
-/
theorem exists_quot_matrix {K : Type} [Field K] {n : ℕ} (U U' : Submodule K (Fin n → K))
    (h : U ≤ U') : ∃ (m : ℕ) (q : Matrix (Fin m) (Fin n) K),
      m + Module.finrank K U = Module.finrank K U' ∧ (∀ y ∈ U', q *ᵥ y = 0 ↔ y ∈ U) ∧
      U'.map (Matrix.toLin' q) = ⊤ := by
  let W := U.comap U'.subtype
  let e : (U' ⧸ W) ≃ₗ[K] (Fin (Module.finrank K (U' ⧸ W)) → K) := (Module.finBasis K (U' ⧸ W)).equivFun
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (e.toLinearMap ∘ₗ W.mkQ)
  have hg' : ∀ y : U', g y = e (W.mkQ y) := fun y => LinearMap.congr_fun hg y
  refine ⟨_, LinearMap.toMatrix' g, ?_, ?_, ?_⟩
  · rw [← (Submodule.comapSubtypeEquivOfLe h).finrank_eq]
    exact Submodule.finrank_quotient_add_finrank W
  · intro y hy
    rw [LinearMap.toMatrix'_mulVec, hg' ⟨y, hy⟩, LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    rfl
  · rw [Matrix.toLin'_toMatrix', eq_top_iff]
    intro z _
    obtain ⟨y, hy⟩ := W.mkQ_surjective (e.symm z)
    exact ⟨y, y.2, by rw [hg', hy, LinearEquiv.apply_symm_apply]⟩

/- English proof (translation)
Set `T : Submodule ℂ (EuclideanSpace ℂ (Fin n))` to `Pᗮ ⊓ P'`. Establish `hT : Module.finrank ℂ T = m`. Use `Submodule.finrank_add_inf_finrank_orthogonal h` as an intermediate fact. Simplify using `only [T]`. Use linear arithmetic over natural numbers and integers.

Set `ob : OrthonormalBasis (Fin m) ℂ T` to `(stdOrthonormalBasis ℂ T).reindex (finCongr hT)`. Set `Q : Matrix (Fin m) (Fin n) ℂ` to `Matrix.of fun i j => star ((ob i : EuclideanSpace ℂ (Fin n)) j)`. Establish `hQ : ∀ (u : EuclideanSpace ℂ (Fin n)) i, (Q *ᵥ u.ofLp) i = inner ℂ (ob i : EuclideanSpace ℂ (Fin n)) u`. Introduce `u i`. Simplify using `[Q, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]`.

Establish `hQh : ∀ z, (WithLp.toLp 2 (Qᴴ *ᵥ z) : EuclideanSpace ℂ (Fin n)) = ((∑ i, z i • ob i : T) : EuclideanSpace ℂ (Fin n))`. Introduce `z`. Use extensionality with `j`. Simplify using `[Q, Matrix.mulVec, dotProduct, mul_comm]`. Establish `hproj : ∀ u ∈ P', ∃ t : T, (t : EuclideanSpace ℂ (Fin n)) = Pᗮ.starProjection u ∧ Q *ᵥ u.ofLp = (ob.repr t).ofLp ∧ u - t ∈ P`.

Introduce `u hu`. Establish `h1 : u - Pᗮ.starProjection u ∈ P`. Rewrite using `[Submodule.starProjection_orthogonal_val, sub_sub_cancel]`. Conclude with `Submodule.starProjection_apply_mem _ _`. Establish `h2 : Pᗮ.starProjection u ∈ T`.

Use `⟨Submodule.starProjection_apply_mem _ _, ?_⟩` and prove the remaining obligations. Use `P'.sub_mem hu (h h1)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Use `⟨⟨_, h2⟩, rfl, ?_, h1⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Rewrite using `[hQ, ob.repr_apply_apply, Submodule.coe_inner]`. Establish `h3` using `Submodule.inner_left_of_mem_orthogonal h1 (ob i).2.1`. Rewrite `h3` using `[inner_sub_right, sub_eq_zero]`. Then use the resulting hypothesis. Use `⟨Q, ?_, fun z => ?_, fun u hu => ?_, fun u hu => ?_⟩` and prove the remaining obligations. Use extensionality with `i k`.

Establish `h1` using `hQ (ob k) i`. Establish `h2` using `orthonormal_iff_ite.1 ob.orthonormal i k`. Rewrite `h2` using `[Submodule.coe_inner, ← h1]`. Rewrite using `[Matrix.one_apply, ← h2]`. Simplify using `[Q, Matrix.mul_apply, Matrix.mulVec, dotProduct]`.

Rewrite using `[hQh]`. Conclude with `(∑ i, z i • ob i : T).2.2`. Take `⟨t, -, h2, h3⟩` from `hproj u hu`. Rewrite using `[hQh, h2, ob.sum_repr]`. Conclude with `h3`.

Take `⟨t, h1, h2, -⟩` from `hproj u hu`. Rewrite using `[← h1, h2, PlaceOperatorNorms.cnorm_eq]`. Simplify using the standard rewrite rules.
-/
theorem exists_coisometry {n m : ℕ} (P P' : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (h : P ≤ P')
    (hm : m + Module.finrank ℂ P = Module.finrank ℂ P') :
    ∃ Q : Matrix (Fin m) (Fin n) ℂ, Q * Qᴴ = 1 ∧
      (∀ z, (WithLp.toLp 2 (Qᴴ *ᵥ z) : EuclideanSpace ℂ (Fin n)) ∈ P') ∧
      (∀ u ∈ P', u - WithLp.toLp 2 (Qᴴ *ᵥ (Q *ᵥ u.ofLp)) ∈ P) ∧
      (∀ u ∈ P', ‖Pᗮ.starProjection u‖ = cnorm (Q *ᵥ u.ofLp)) := by
  let T : Submodule ℂ (EuclideanSpace ℂ (Fin n)) := Pᗮ ⊓ P'
  have hT : Module.finrank ℂ T = m := by
    have := Submodule.finrank_add_inf_finrank_orthogonal h
    simp only [T]; omega
  let ob : OrthonormalBasis (Fin m) ℂ T := (stdOrthonormalBasis ℂ T).reindex (finCongr hT)
  let Q : Matrix (Fin m) (Fin n) ℂ := Matrix.of fun i j => star ((ob i : EuclideanSpace ℂ (Fin n)) j)
  have hQ : ∀ (u : EuclideanSpace ℂ (Fin n)) i, (Q *ᵥ u.ofLp) i =
      inner ℂ (ob i : EuclideanSpace ℂ (Fin n)) u := by
    intro u i
    simp [Q, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
  have hQh : ∀ z, (WithLp.toLp 2 (Qᴴ *ᵥ z) : EuclideanSpace ℂ (Fin n)) =
      ((∑ i, z i • ob i : T) : EuclideanSpace ℂ (Fin n)) := by
    intro z
    ext j
    simp [Q, Matrix.mulVec, dotProduct, mul_comm]
  have hproj : ∀ u ∈ P', ∃ t : T, (t : EuclideanSpace ℂ (Fin n)) = Pᗮ.starProjection u ∧
      Q *ᵥ u.ofLp = (ob.repr t).ofLp ∧ u - t ∈ P := by
    intro u hu
    have h1 : u - Pᗮ.starProjection u ∈ P := by
      rw [Submodule.starProjection_orthogonal_val, sub_sub_cancel]
      exact Submodule.starProjection_apply_mem _ _
    have h2 : Pᗮ.starProjection u ∈ T := by
      refine ⟨Submodule.starProjection_apply_mem _ _, ?_⟩
      have := P'.sub_mem hu (h h1)
      rwa [sub_sub_cancel] at this
    refine ⟨⟨_, h2⟩, rfl, ?_, h1⟩
    funext i
    rw [hQ, ob.repr_apply_apply, Submodule.coe_inner]
    have h3 := Submodule.inner_left_of_mem_orthogonal h1 (ob i).2.1
    rwa [inner_sub_right, sub_eq_zero] at h3
  refine ⟨Q, ?_, fun z => ?_, fun u hu => ?_, fun u hu => ?_⟩
  · ext i k
    have h1 := hQ (ob k) i
    have h2 := orthonormal_iff_ite.1 ob.orthonormal i k
    rw [Submodule.coe_inner, ← h1] at h2
    rw [Matrix.one_apply, ← h2]
    simp [Q, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  · rw [hQh]
    exact (∑ i, z i • ob i : T).2.2
  · obtain ⟨t, -, h2, h3⟩ := hproj u hu
    rw [hQh, h2, ob.sum_repr]
    exact h3
  · obtain ⟨t, h1, h2, -⟩ := hproj u hu
    rw [← h1, h2, PlaceOperatorNorms.cnorm_eq]
    simp

open QuotientRealization

section
variable {K : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {n m : ℕ}

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨y, hy, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨y, Submodule.subset_span hy, rfl⟩`. Consider the case `zero => exact Submodule.zero_mem _`.

Consider the case `add y w _ _ h1 h2 => rw [WithLp.toLp_add]`. Conclude with `Submodule.add_mem _ h1 h2`. Consider the case `smul a y _ h => rw [WithLp.toLp_smul]`. Conclude with `Submodule.smul_mem _ _ h`.
-/
theorem toLp_mem_pv (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (A : Submodule (𝓞 K) (Fin n → K)) (w : InfinitePlace K) (u : Fin n → ℂ)
    (hu : u ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K)))) :
    (WithLp.toLp 2 u : EuclideanSpace ℂ (Fin n)) ∈
      pv (Pi.basisFun K (Fin n)) X (Submodule.span K (A : Set (Fin n → K))) w := by
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨y, hy, rfl⟩ := hy
    exact Submodule.subset_span ⟨y, Submodule.subset_span hy, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add y w _ _ h1 h2 => rw [WithLp.toLp_add]; exact Submodule.add_mem _ h1 h2
  | smul a y _ h => rw [WithLp.toLp_smul]; exact Submodule.smul_mem _ _ h

omit [StarRing K] [IsTotallyComplex K] in
/- English proof (translation)
Rewrite using `[fcoord, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]`. Use function extensionality and compare the values at `i`. Simplify using `[vecAt, Matrix.mulVec, dotProduct]`.
-/
theorem mul_fcoord (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace K)
    (hX : IsUnit (X w).det) (q : Matrix (Fin m) (Fin n) K) (y : Fin n → K) :
    (q.map w.embedding * X w) *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y =
      vecAt (Pi.basisFun K (Fin m)) w (q *ᵥ y) := by
  rw [fcoord, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hX, Matrix.mul_one]
  funext i
  simp [vecAt, Matrix.mulVec, dotProduct]

/- English proof (translation)
Use `set M := q.map w.embedding * X w with hM`. Establish `hker : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) ≤ LinearMap.ker (Matrix.toLin' M)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Use `show Matrix.toLin' M _ = 0`.

Rewrite using `[Matrix.toLin'_apply, hM, mul_fcoord X w hX, hS y hy]`. Use function extensionality and compare the values at `i`. Simplify using `[vecAt]`. Establish `hkey : ∀ y ∈ A, vecAt (Pi.basisFun K (Fin m)) w (q *ᵥ y) = (M * Qᴴ) *ᵥ (Q *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y)`. Introduce `y hy`.

Establish `h1` using `hker (hQ _ (Submodule.subset_span ⟨y, hy, rfl⟩))`. Rewrite `h1` using `[LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.mulVec_sub, sub_eq_zero]`. Rewrite using `[← Matrix.mulVec_mulVec, ← h1, hM, mul_fcoord X w hX]`. Establish `hu : IsUnit (M * Qᴴ).det`. Rewrite using `[← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]`.

Establish `hle : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin m)) (fun _ => 1) w '' (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K))) ≤ LinearMap.range (Matrix.toLin' (M * Qᴴ))`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨_, ⟨y, hy, rfl⟩, rfl⟩`. Use `⟨Q *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.toLin'_apply, ← hkey y hy]`.

Simplify using `[fcoord]`. Establish `htop : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin m)) (fun _ => 1) w '' (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K))) = ⊤`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Rewrite using `[PlaceDecomposition.finrank_span_complex _ _ (fun _ => by simp), rkK, hA]`. Simplify using the standard rewrite rules.

Introduce `z`. Take `⟨x, hx⟩` from `hle (htop ▸ Submodule.mem_top (x := z))`. Conclude with `⟨x, by simpa using hx⟩`. Use `⟨M * Qᴴ, hu, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[hkey y hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`.
-/
theorem exists_frame (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (w : InfinitePlace K)
    (hX : IsUnit (X w).det) (q : Matrix (Fin m) (Fin n) K) (A S : Submodule (𝓞 K) (Fin n → K))
    (hS : ∀ y ∈ S, q *ᵥ y = 0)
    (hA : Submodule.span K (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K)) = ⊤)
    (Q : Matrix (Fin m) (Fin n) ℂ)
    (hQ : ∀ u ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K))),
      u - Qᴴ *ᵥ (Q *ᵥ u) ∈
        Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))) :
    ∃ Y : Matrix (Fin m) (Fin m) ℂ, IsUnit Y.det ∧ ∀ y ∈ A,
      Y⁻¹ *ᵥ vecAt (Pi.basisFun K (Fin m)) w (q *ᵥ y) =
        Q *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y := by
  set M := q.map w.embedding * X w with hM
  have hker : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) ≤
      LinearMap.ker (Matrix.toLin' M) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show Matrix.toLin' M _ = 0
    rw [Matrix.toLin'_apply, hM, mul_fcoord X w hX, hS y hy]
    funext i; simp [vecAt]
  have hkey : ∀ y ∈ A, vecAt (Pi.basisFun K (Fin m)) w (q *ᵥ y) =
      (M * Qᴴ) *ᵥ (Q *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) := by
    intro y hy
    have h1 := hker (hQ _ (Submodule.subset_span ⟨y, hy, rfl⟩))
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.mulVec_sub, sub_eq_zero] at h1
    rw [← Matrix.mulVec_mulVec, ← h1, hM, mul_fcoord X w hX]
  have hu : IsUnit (M * Qᴴ).det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
    have hle : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin m)) (fun _ => 1) w ''
        (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K))) ≤
        LinearMap.range (Matrix.toLin' (M * Qᴴ)) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨Q *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y, ?_⟩
      rw [Matrix.toLin'_apply, ← hkey y hy]
      simp [fcoord]
    have htop : Submodule.span ℂ (fcoord (Pi.basisFun K (Fin m)) (fun _ => 1) w ''
        (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K))) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [PlaceDecomposition.finrank_span_complex _ _ (fun _ => by simp), rkK, hA]
      simp
    intro z
    obtain ⟨x, hx⟩ := hle (htop ▸ Submodule.mem_top (x := z))
    exact ⟨x, by simpa using hx⟩
  refine ⟨M * Qᴴ, hu, fun y hy => ?_⟩
  rw [hkey y hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

/- English proof (translation)
Use `set U := Submodule.span K (S : Set (Fin n → K)) with hU`. Use `set b := Pi.basisFun K (Fin n)`. Use `set b'' := Pi.basisFun K (Fin m)`. Establish `hNfg : N.FG` using `Submodule.FG.of_le hA hNA`. Use `set N'' := N.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) with hN''`.

Establish `hUle : U ≤ Submodule.span K (N : Set (Fin n → K))` using `Submodule.span_mono hSN`. Establish `hrk : rkK N'' + rkK S = rkK N`. Establish `hspan : Submodule.span K (N'' : Set (Fin m → K)) = (Submodule.span K (N : Set (Fin n → K))).map (Matrix.toLin' q)`. Rewrite using `[hN'', Submodule.map_coe]`. Conclude with `Submodule.span_image (Matrix.toLin' q)`.

Set `W` to `Submodule.span K (N : Set (Fin n → K))`. Set `fW : W →ₗ[K] (Fin m → K)` to `Matrix.toLin' q ∘ₗ W.subtype`. Establish `h1` using `LinearMap.finrank_range_add_finrank_ker fW`. Establish `hr : LinearMap.range fW = W.map (Matrix.toLin' q)`. Rewrite using `[LinearMap.range_comp, Submodule.range_subtype]`.

Establish `hk : LinearMap.ker fW = U.comap W.subtype`. Use extensionality with `y`. Conclude with `hker y (Submodule.span_mono hNA y.2)`. Rewrite `h1` using `[hr, hk, (Submodule.comapSubtypeEquivOfLe hUle).finrank_eq]`. Unfold `rkK`.

Rewrite using `[hspan]`. Conclude with `h1`. Establish `hrkR : ((rkK N : ℝ) - rkK S) = rkK N''`. Rewrite using `[← hrk]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Set `ρ` to `realize b X`. Set `ρ''` to `realize b'' X'`. Establish `hNlat` using `plLat K _ _ b X hX N hNfg`. Establish `hN''lat` using `plLat K _ _ b'' X' hX' N'' (hNfg.map _)`.

Establish `: DiscreteTopology (zl ρ N)` using `hNlat.1.2`. Establish `hsatN : Formalism.F.IsSaturated (zl ρ N) (zl ρ S)` using `⟨zl_mono ρ hSN, fun x hx hxs => hSat.2.2 x (zl_mono ρ hNA hx) hxs⟩`. Establish `: DiscreteTopology (Formalism.F.quot (zl ρ N) (zl ρ S))` using `(Formalism.F.degQuot _ _ _ inferInstance hsatN).1`. Establish `: DiscreteTopology (zl ρ'' N'')` using `hN''lat.1.2`. Set `W` to `Submodule.span ℝ (zl ρ S : Set (EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2)))`.

Set `f : N →+ EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2)` to `(Wᗮ.starProjection.toLinearMap.toAddMonoidHom).comp (ρ.comp N.subtype.toAddMonoidHom)`. Set `g : N →+ EuclideanSpace ℝ (InfinitePlace K × Fin m × Fin 2)` to `ρ''.comp (((Matrix.toLin' q).toAddMonoidHom).comp N.subtype.toAddMonoidHom)`. Establish `h1 : ∀ y, y ∈ Formalism.F.quot (zl ρ N) (zl ρ S) ↔ ∃ m : N, f m = y`. Introduce `y`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Introduce and unpack `⟨⟨x, hx⟩, rfl⟩`. Conclude with `⟨ρ x, ⟨x, hx, rfl⟩, rfl⟩`. Establish `h2 : ∀ y, y ∈ zl ρ'' N'' ↔ ∃ m : N, g m = y`.

Introduce `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨x, hx, rfl⟩, rfl⟩`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Introduce and unpack `⟨⟨x, hx⟩, rfl⟩`.

Conclude with `⟨Matrix.toLin' q x, ⟨x, hx, rfl⟩, rfl⟩`. Establish `hn : ∀ m, ‖f m‖ = ‖g m‖`. Introduce and unpack `⟨x, hx⟩`. Establish `hsq : ‖f ⟨x, hx⟩‖ ^ 2 = ‖g ⟨x, hx⟩‖ ^ 2` using `by show ‖Wᗮ.starProjection (ρ x)‖ ^ 2 = ‖ρ'' (q *ᵥ x)‖ ^ 2`. Rewrite using `[proj_norm_sq b X S x, PlaceOperatorNorms.norm_sq_realize]`.

Simplify using `only [hnorm _ x (hNA hx)]`. Both sides reduce to the same expression. Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq`. Establish `hcov` using `covol_eq_of_norm_eq f g _ _ h1 h2 hn`. Establish `hht : htQ b X N S = ht b'' X' N''`.

Unfold `htQ ht`. Rewrite using `[hcov, hrkR, ← Nat.cast_mul, Real.rpow_natCast]`. Unfold `sizeQ size`. Rewrite using `[hht, hrkR]`.
-/
theorem sizeQ_eq_size (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ w, IsUnit (X w).det)
    (X' : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (hX' : ∀ w, IsUnit (X' w).det)
    (q : Matrix (Fin m) (Fin n) K) (A S N : Submodule (𝓞 K) (Fin n → K)) (hA : A.FG)
    (hSat : IsSat (realize (Pi.basisFun K (Fin n)) X) A S) (hSN : S ≤ N) (hNA : N ≤ A)
    (hker : ∀ y ∈ Submodule.span K (A : Set (Fin n → K)),
      q *ᵥ y = 0 ↔ y ∈ Submodule.span K (S : Set (Fin n → K)))
    (hnorm : ∀ w, ∀ y ∈ A, normAt (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) =
      ‖(pv (Pi.basisFun K (Fin n)) X (Submodule.span K (S : Set (Fin n → K))) w)ᗮ.starProjection
        (WithLp.toLp 2 (fcoord (Pi.basisFun K (Fin n)) X w y))‖) :
    sizeQ (Pi.basisFun K (Fin n)) X N S = size (Pi.basisFun K (Fin m)) X'
      (N.map ((Matrix.toLin' q).restrictScalars (𝓞 K))) := by
  classical
  set U := Submodule.span K (S : Set (Fin n → K)) with hU
  set b := Pi.basisFun K (Fin n)
  set b'' := Pi.basisFun K (Fin m)
  have hNfg : N.FG := Submodule.FG.of_le hA hNA
  set N'' := N.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) with hN''
  have hUle : U ≤ Submodule.span K (N : Set (Fin n → K)) := Submodule.span_mono hSN
  have hrk : rkK N'' + rkK S = rkK N := by
    have hspan : Submodule.span K (N'' : Set (Fin m → K)) =
        (Submodule.span K (N : Set (Fin n → K))).map (Matrix.toLin' q) := by
      rw [hN'', Submodule.map_coe]
      exact Submodule.span_image (Matrix.toLin' q)
    let W := Submodule.span K (N : Set (Fin n → K))
    let fW : W →ₗ[K] (Fin m → K) := Matrix.toLin' q ∘ₗ W.subtype
    have h1 := LinearMap.finrank_range_add_finrank_ker fW
    have hr : LinearMap.range fW = W.map (Matrix.toLin' q) := by
      rw [LinearMap.range_comp, Submodule.range_subtype]
    have hk : LinearMap.ker fW = U.comap W.subtype := by
      ext y
      exact hker y (Submodule.span_mono hNA y.2)
    rw [hr, hk, (Submodule.comapSubtypeEquivOfLe hUle).finrank_eq] at h1
    unfold rkK
    rw [hspan]
    exact h1
  have hrkR : ((rkK N : ℝ) - rkK S) = rkK N'' := by
    rw [← hrk]; push_cast; ring
  let ρ := realize b X
  let ρ'' := realize b'' X'
  have hNlat := plLat K _ _ b X hX N hNfg
  have hN''lat := plLat K _ _ b'' X' hX' N'' (hNfg.map _)
  have : DiscreteTopology (zl ρ N) := hNlat.1.2
  have hsatN : Formalism.F.IsSaturated (zl ρ N) (zl ρ S) :=
    ⟨zl_mono ρ hSN, fun x hx hxs => hSat.2.2 x (zl_mono ρ hNA hx) hxs⟩
  have : DiscreteTopology (Formalism.F.quot (zl ρ N) (zl ρ S)) :=
    (Formalism.F.degQuot _ _ _ inferInstance hsatN).1
  have : DiscreteTopology (zl ρ'' N'') := hN''lat.1.2
  let W := Submodule.span ℝ (zl ρ S : Set (EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2)))
  let f : N →+ EuclideanSpace ℝ (InfinitePlace K × Fin n × Fin 2) :=
    (Wᗮ.starProjection.toLinearMap.toAddMonoidHom).comp (ρ.comp N.subtype.toAddMonoidHom)
  let g : N →+ EuclideanSpace ℝ (InfinitePlace K × Fin m × Fin 2) :=
    ρ''.comp (((Matrix.toLin' q).toAddMonoidHom).comp N.subtype.toAddMonoidHom)
  have h1 : ∀ y, y ∈ Formalism.F.quot (zl ρ N) (zl ρ S) ↔ ∃ m : N, f m = y := by
    intro y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨ρ x, ⟨x, hx, rfl⟩, rfl⟩
  have h2 : ∀ y, y ∈ zl ρ'' N'' ↔ ∃ m : N, g m = y := by
    intro y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨Matrix.toLin' q x, ⟨x, hx, rfl⟩, rfl⟩
  have hn : ∀ m, ‖f m‖ = ‖g m‖ := by
    rintro ⟨x, hx⟩
    have hsq : ‖f ⟨x, hx⟩‖ ^ 2 = ‖g ⟨x, hx⟩‖ ^ 2 := by
      show ‖Wᗮ.starProjection (ρ x)‖ ^ 2 = ‖ρ'' (q *ᵥ x)‖ ^ 2
      rw [proj_norm_sq b X S x, PlaceOperatorNorms.norm_sq_realize]
      simp only [hnorm _ x (hNA hx)]
      rfl
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 hsq
  have hcov := covol_eq_of_norm_eq f g _ _ h1 h2 hn
  have hht : htQ b X N S = ht b'' X' N'' := by
    unfold htQ ht
    rw [hcov, hrkR, ← Nat.cast_mul, Real.rpow_natCast]
  unfold sizeQ size
  rw [hht, hrkR]

end

/- English proof (translation)
Introduce `K _ _ _ _ n X A S hX hA hSat`. Establish `hSA : S ≤ A` using `hSat.1`. Establish `hUU : Submodule.span K (S : Set (Fin n → K)) ≤ Submodule.span K (A : Set (Fin n → K))` using `Submodule.span_mono hSA`. Take `⟨m, q, hm, hker, hsurj⟩` from `exists_quot_matrix _ _ hUU`. Establish `hS : ∀ y ∈ S, q *ᵥ y = 0` using `fun y hy => (hker y (Submodule.subset_span (hSA hy))).2 (Submodule.subset_span hy)`.

Establish `htop : Submodule.span K (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K)) = ⊤`. Rewrite using `[← hsurj, Submodule.map_coe]`. Conclude with `Submodule.span_image (Matrix.toLin' q)`. Apply the tactic sequence `have hQ := fun w => exists_coisometry (m := m) (pv (Pi.basisFun K (Fin n)) X (Submodule.span K (S : Set (Fin n → K))) w) (pv (Pi.basisFun K (Fin n)) X (Submodule.span K (A : Set (Fin n → K))) w) (Submodule.span_mono (Set.image_mono hUU)) (by rw [finrank_pv _ _ hX, finrank_pv _ _ …`. Use `choose Q hQ1 hQ2 hQ3 hQ4 using hQ`.

Establish `hQ3' : ∀ w, ∀ u ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K))), u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))` using `fun w u hu => pv_le _ X S w _ (hQ3 w _ (toLp_mem_pv X A w u hu))`. Establish `hY` using `fun w => exists_frame X w (hX w) q A S hS htop (Q w) (hQ3' w)`. Use `choose X' hX' hc using hY`. Use `⟨m, q, X', Q, hm, hX', hQ1, hc, fun w z => pv_le _ X A w _ (hQ2 w z), hQ3', hS, htop, ?_⟩` and prove the remaining obligations. Introduce `N' hN' hne`.

Establish `hmap : (A ⊓ N'.comap ((Matrix.toLin' q).restrictScalars (𝓞 K))).map ((Matrix.toLin' q).restrictScalars (𝓞 K)) = N'`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hy.2`. Introduce `z hz`.

Take `⟨y, hy, rfl⟩` from `hN' hz`. Conclude with `⟨y, ⟨hy, hz⟩, rfl⟩`. Establish `hSN : S ≤ A ⊓ N'.comap ((Matrix.toLin' q).restrictScalars (𝓞 K))`. Introduce `y hy`. Use `⟨hSA hy, ?_⟩` and prove the remaining obligations.

Use `show q *ᵥ y ∈ N'`. Rewrite using `[hS y hy]`. Conclude with `N'.zero_mem`. Use `⟨_, lt_of_le_of_ne hSN ?_, inf_le_left, ?_⟩` and prove the remaining obligations. Introduce `h`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hmap, ← h, eq_bot_iff]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `hS y hy`. Rewrite using `[sizeQ_eq_size X hX X' hX' q A S _ hA hSat hSN inf_le_left hker ?_, hmap]`.

Introduce `w y hy`. Rewrite using `[hQ4 w _ (toLp_mem_pv X A w _ (Submodule.subset_span ⟨y, hy, rfl⟩)), normAt]`. Conclude with `congrArg cnorm (hc w y hy)`.
-/
theorem quot_realized : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (A S : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → A.FG → IsSat (realize (Pi.basisFun K (Fin n)) X) A S → ∃ (m : ℕ) (q : Matrix (Fin m) (Fin n) K) (X' : InfinitePlace K → Matrix (Fin m) (Fin m) ℂ) (Q : InfinitePlace K → Matrix (Fin m) (Fin n) ℂ), m + rkK S = rkK A ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, Q w * (Q w)ᴴ = 1) ∧ (∀ w, ∀ y ∈ A, fcoord (Pi.basisFun K (Fin m)) X' w (q *ᵥ y) = Q w *ᵥ fcoord (Pi.basisFun K (Fin n)) X w y) ∧ (∀ w z, (Q w)ᴴ *ᵥ z ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K)))) ∧ (∀ w, ∀ u ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K))), u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈ Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K)))) ∧ (∀ y ∈ S, q *ᵥ y = 0) ∧ Submodule.span K (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K)) = ⊤ ∧ ∀ N', N' ≤ A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) → N' ≠ ⊥ → ∃ N, S < N ∧ N ≤ A ∧ sizeQ (Pi.basisFun K (Fin n)) X N S = size (Pi.basisFun K (Fin m)) X' N' := by
  intro K _ _ _ _ n X A S hX hA hSat
  have hSA : S ≤ A := hSat.1
  have hUU : Submodule.span K (S : Set (Fin n → K)) ≤ Submodule.span K (A : Set (Fin n → K)) :=
    Submodule.span_mono hSA
  obtain ⟨m, q, hm, hker, hsurj⟩ := exists_quot_matrix _ _ hUU
  have hS : ∀ y ∈ S, q *ᵥ y = 0 := fun y hy =>
    (hker y (Submodule.subset_span (hSA hy))).2 (Submodule.subset_span hy)
  have htop : Submodule.span K
      (A.map ((Matrix.toLin' q).restrictScalars (𝓞 K)) : Set (Fin m → K)) = ⊤ := by
    rw [← hsurj, Submodule.map_coe]
    exact Submodule.span_image (Matrix.toLin' q)
  have hQ := fun w => exists_coisometry (m := m)
    (pv (Pi.basisFun K (Fin n)) X (Submodule.span K (S : Set (Fin n → K))) w)
    (pv (Pi.basisFun K (Fin n)) X (Submodule.span K (A : Set (Fin n → K))) w)
    (Submodule.span_mono (Set.image_mono hUU))
    (by rw [finrank_pv _ _ hX, finrank_pv _ _ hX]; exact hm)
  choose Q hQ1 hQ2 hQ3 hQ4 using hQ
  have hQ3' : ∀ w, ∀ u ∈ Submodule.span ℂ
      (fcoord (Pi.basisFun K (Fin n)) X w '' (A : Set (Fin n → K))), u - (Q w)ᴴ *ᵥ (Q w *ᵥ u) ∈
      Submodule.span ℂ (fcoord (Pi.basisFun K (Fin n)) X w '' (S : Set (Fin n → K))) :=
    fun w u hu => pv_le _ X S w _ (hQ3 w _ (toLp_mem_pv X A w u hu))
  have hY := fun w => exists_frame X w (hX w) q A S hS htop (Q w) (hQ3' w)
  choose X' hX' hc using hY
  refine ⟨m, q, X', Q, hm, hX', hQ1, hc, fun w z => pv_le _ X A w _ (hQ2 w z), hQ3', hS, htop, ?_⟩
  intro N' hN' hne
  have hmap : (A ⊓ N'.comap ((Matrix.toLin' q).restrictScalars (𝓞 K))).map
      ((Matrix.toLin' q).restrictScalars (𝓞 K)) = N' := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hy.2
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := hN' hz
      exact ⟨y, ⟨hy, hz⟩, rfl⟩
  have hSN : S ≤ A ⊓ N'.comap ((Matrix.toLin' q).restrictScalars (𝓞 K)) := by
    intro y hy
    refine ⟨hSA hy, ?_⟩
    show q *ᵥ y ∈ N'
    rw [hS y hy]
    exact N'.zero_mem
  refine ⟨_, lt_of_le_of_ne hSN ?_, inf_le_left, ?_⟩
  · intro h
    apply hne
    rw [← hmap, ← h, eq_bot_iff]
    rintro _ ⟨y, hy, rfl⟩
    exact hS y hy
  · rw [sizeQ_eq_size X hX X' hX' q A S _ hA hSat hSN inf_le_left hker ?_, hmap]
    intro w y hy
    rw [hQ4 w _ (toLp_mem_pv X A w _ (Submodule.subset_span ⟨y, hy, rfl⟩)), normAt]
    exact congrArg cnorm (hc w y hy)

end GlobalTheory.QuotCoord
