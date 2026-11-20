import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtGrSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtUpper
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtRedConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtBasis
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtCorr
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.LtTorus

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Rewrite `*` using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Use `filter_upwards [hη x, hr x] with y h1 h2`. Apply `SemidirectProduct.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `h2`. Rewrite using `[hm y, hm x]`. Conclude with `h1`.
-/
private theorem lc_hom {R D : Type} [CommRing R] [Group D] [TopologicalSpace D] (η : D →* ℤˣ) (r : D →* GG 3 R)
    (hη : IsLocallyConstant η) (hm : HasMult η r) (hr : IsLocallyConstant (mats r)) : IsLocallyConstant r := by
  rw [IsLocallyConstant.iff_eventually_eq] at *
  intro x
  filter_upwards [hη x, hr x] with y h1 h2
  apply SemidirectProduct.ext
  · apply Units.ext
    exact h2
  · rw [hm y, hm x]
    exact h1

/- English proof (translation)
The claim follows from `SemidirectProduct.ext (Units.ext h) h'`.
-/
private theorem gg_ext {R : Type} [CommRing R] {x y : GG 3 R} (h : x.mat = y.mat) (h' : x.right = y.right) : x = y :=
  SemidirectProduct.ext (Units.ext h) h'

/- English proof (translation)
The claim follows from `sub_self _`.
-/
private theorem wt_self (a : Fin 3) : wt a a = 0 := sub_self _

/- English proof (translation)
Assume the negation of the conclusion as `ha`. Take `⟨u, hu⟩` from `h`. Take `⟨b, hb⟩` from `hp (↑u⁻¹ : R')`. Establish `hk : a * b - 1 ∈ RingHom.ker p`. Rewrite using `[RingHom.mem_ker, map_sub, map_mul, hb, ← hu, map_one]`.

Simplify using the standard rewrite rules. Establish `hker : RingHom.ker p ≤ maximalIdeal R` using `IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top p)`. Establish `h1 : a * b ∈ maximalIdeal R` using `Ideal.mul_mem_right b _ ((IsLocalRing.mem_maximalIdeal a).2 ha)`. Establish `h2` using `Ideal.sub_mem _ h1 (hker hk)`. Rewrite `h2` using `[sub_sub_cancel]`.

Conclude with `(IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)`.
-/
private theorem isUnit_of_isUnit_surjective_localRingHom {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
    (p : R →+* R') (hp : Function.Surjective p) (a : R) (h : IsUnit (p a)) : IsUnit a := by
  by_contra ha
  obtain ⟨u, hu⟩ := h
  obtain ⟨b, hb⟩ := hp (↑u⁻¹ : R')
  have hk : a * b - 1 ∈ RingHom.ker p := by
    rw [RingHom.mem_ker, map_sub, map_mul, hb, ← hu, map_one]
    simp
  have hker : RingHom.ker p ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top p)
  have h1 : a * b ∈ maximalIdeal R := Ideal.mul_mem_right b _ ((IsLocalRing.mem_maximalIdeal a).2 ha)
  have h2 := Ideal.sub_mem _ h1 (hker hk)
  rw [sub_sub_cancel] at h2
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h2)

/- English proof (translation)
Take `⟨X, hXg, hXp⟩` from `hX`. Set `M : Matrix (Fin 3) (Fin 3) R` to `fun a b => if wt a b < 0 then 0 else if a = b then t.mat a a else X a b`. Establish `hMp : M.map (p : R →+* R') = y.mat`. Use extensionality with `a b`. Use `show (p : R →+* R') (M a b) = y.mat a b`.

Simplify using `only [M]`. Use `split_ifs with h1 h2`. Rewrite using `[map_zero, hy a b h1]`. Substitute `h2` using the available equality. Conclude with `hty a`.

Rewrite using `[← hXp]`. Both sides reduce to the same expression. Establish `hdet : IsUnit M.det`. Apply `isUnit_of_isUnit_surjective_localRingHom (p : R →+* R') hp` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, hMp]`.

Conclude with `Matrix.isUnits_det_units y.left`. Use `⟨⟨Matrix.nonsingInvUnit M hdet, y.right⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `SemidirectProduct.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hMp`.

Both sides reduce to the same expression. Introduce `a b show M a b ∈ _`. Simplify using `only [M]`. Use `split_ifs with h1 h2`. Conclude with `Submodule.zero_mem _`.

Substitute `h2` using the available equality. Rewrite using `[wt_self]`. Conclude with `ht a`. Conclude with `hXg a b`. Introduce `a b h show M a b = 0`.

Simplify using `[M, h]`. Introduce `a show M a a = t.mat a a`. Simplify using `[M, wt_self]`.
-/
private theorem lift_elt {O R R' : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing R']
    [IsLocalRing R'] [Algebra O R'] (𝒜 : ℤ → Submodule O R) (p : R →ₐ[O] R') (hp : Function.Surjective p)
    (y : GG 3 R') (t : GG 3 R) (hy : ∀ a b, wt a b < 0 → y.mat a b = 0) (hX : ∃ X, GrMat 𝒜 X ∧ X.map p = y.mat)
    (ht : ∀ a, t.mat a a ∈ 𝒜 0) (hty : ∀ a, p (t.mat a a) = y.mat a a) :
    ∃ x : GG 3 R, GG.map (p : R →+* R') x = y ∧ GrMat 𝒜 x.mat ∧ (∀ a b, wt a b < 0 → x.mat a b = 0) ∧
      ∀ a, x.mat a a = t.mat a a := by
  classical
  obtain ⟨X, hXg, hXp⟩ := hX
  let M : Matrix (Fin 3) (Fin 3) R := fun a b => if wt a b < 0 then 0 else if a = b then t.mat a a else X a b
  have hMp : M.map (p : R →+* R') = y.mat := by
    ext a b
    show (p : R →+* R') (M a b) = y.mat a b
    simp only [M]
    split_ifs with h1 h2
    · rw [map_zero, hy a b h1]
    · subst h2
      exact hty a
    · rw [← hXp]
      rfl
  have hdet : IsUnit M.det := by
    apply isUnit_of_isUnit_surjective_localRingHom (p : R →+* R') hp
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hMp]
    exact Matrix.isUnits_det_units y.left
  refine ⟨⟨Matrix.nonsingInvUnit M hdet, y.right⟩, ?_, ?_, ?_, ?_⟩
  · apply SemidirectProduct.ext
    · apply Units.ext
      exact hMp
    · rfl
  · intro a b
    show M a b ∈ _
    simp only [M]
    split_ifs with h1 h2
    · exact Submodule.zero_mem _
    · subst h2
      rw [wt_self]
      exact ht a
    · exact hXg a b
  · intro a b h
    show M a b = 0
    simp [M, h]
  · intro a
    show M a a = t.mat a a
    simp [M, wt_self]

/- English proof (translation)
Establish `h1` using `DirectSum.decompose_of_mem_same 𝒜 hj`. Establish `h2` using `DirectSum.decompose_of_mem_ne 𝒜 hi h`. Rewrite `h1` using `[h2]`. Conclude with `h1.symm`.
-/
private theorem gr_eq_zero {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : ℤ → Submodule O R)
    [GradedAlgebra 𝒜] {i j : ℤ} {x : R} (hi : x ∈ 𝒜 i) (hj : x ∈ 𝒜 j) (h : i ≠ j) : x = 0 := by
  have h1 := DirectSum.decompose_of_mem_same 𝒜 hj
  have h2 := DirectSum.decompose_of_mem_ne 𝒜 hi h
  rw [h2] at h1
  exact h1.symm

/- English proof (translation)
Introduce `a b`. Rewrite using `[Matrix.mul_apply]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Establish `h` using `SetLike.mul_mem_graded (hX a c) (hY c b)`. Establish `e : wt a c + wt c b = wt a b`.

Simplify using `only [wt]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
private theorem grMat_mul {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (𝒜 : ℤ → Submodule O R)
    [GradedAlgebra 𝒜] {X Y : Matrix (Fin 3) (Fin 3) R} (hX : GrMat 𝒜 X) (hY : GrMat 𝒜 Y) : GrMat 𝒜 (X * Y) := by
  intro a b
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have h := SetLike.mul_mem_graded (hX a c) (hY c b)
  have e : wt a c + wt c b = wt a b := by
    simp only [wt]
    ring
  rwa [e] at h

/- English proof (translation)
Rewrite using `[add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]`. Introduce `d _`. Distinguish the cases in `hd : wt a d ≤ 0`. Rewrite using `[hb a d hd, zero_mul]`. Establish `e : wt a d + wt d c = wt a c`.

Simplify using `only [wt]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlt : wt d c < 0` using `by omega`. Rewrite using `[hX d c hlt, mul_zero]`.
-/
private theorem strict_mul {R : Type} [CommRing R] {b X : Matrix (Fin 3) (Fin 3) R}
    (hb : ∀ a c, wt a c ≤ 0 → b a c = 0) (hX : ∀ a c, wt a c < 0 → X a c = 0) (a c : Fin 3) (h : wt a c ≤ 0) :
    ((1 + b) * X) a c = X a c := by
  rw [add_mul, one_mul, Matrix.add_apply, Matrix.mul_apply, Finset.sum_eq_zero, add_zero]
  intro d _
  by_cases hd : wt a d ≤ 0
  · rw [hb a d hd, zero_mul]
  · have e : wt a d + wt d c = wt a c := by
      simp only [wt]
      ring
    have hlt : wt d c < 0 := by omega
    rw [hX d c hlt, mul_zero]

/- English proof (translation)
Establish `hloc : IsLocalHom (algebraMap O R)` using `IsCO.isLocalHom`. Establish `hnil : IsNilpotent (Ideal.jacobson (⊥ : Ideal R))` using `IsArtinianRing.isNilpotent_jacobson_bot`. Rewrite `hnil` using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Take `⟨n, hn⟩` from `hnil`. Establish `hle : Ideal.map (algebraMap O R) (maximalIdeal O ^ n) ≤ maximalIdeal R ^ n`.

Rewrite using `[Ideal.map_pow]`. Apply `Ideal.pow_right_mono` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Conclude with `map_nonunit (algebraMap O R) x hx`.

Establish `hker : ∀ x ∈ maximalIdeal O ^ n, algebraMap O R x = 0`. Introduce `x hx`. Establish `h` using `hle (Ideal.mem_map_of_mem _ hx)`. Rewrite `h` using `[hn]`. Simplify using `using h`.

Establish `h` using `(hf n).comp (Ideal.Quotient.lift (maximalIdeal O ^ n) (algebraMap O R) hker)`. Conclude with `h`.
-/
private theorem psi_lc {O R D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [Finite R]
    [TopologicalSpace D] (f : D → O)
    (hf : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ n) (f g)) :
    IsLocallyConstant fun g => algebraMap O R (f g) := by
  have hloc : IsLocalHom (algebraMap O R) := IsCO.isLocalHom
  have hnil : IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) := IsArtinianRing.isNilpotent_jacobson_bot
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hnil
  obtain ⟨n, hn⟩ := hnil
  have hle : Ideal.map (algebraMap O R) (maximalIdeal O ^ n) ≤ maximalIdeal R ^ n := by
    rw [Ideal.map_pow]
    apply Ideal.pow_right_mono
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact map_nonunit (algebraMap O R) x hx
  have hker : ∀ x ∈ maximalIdeal O ^ n, algebraMap O R x = 0 := by
    intro x hx
    have h := hle (Ideal.mem_map_of_mem _ hx)
    rw [hn] at h
    simpa using h
  have h := (hf n).comp (Ideal.Quotient.lift (maximalIdeal O ^ n) (algebraMap O R) hker)
  exact h

/- English proof (translation)
Use `show ((z * v).left : Matrix (Fin 3) (Fin 3) R) = _`. Rewrite using `[SemidirectProduct.mul_left, h, map_one]`. Both sides reduce to the same expression.
-/
private theorem gg_mul_mat_of_right_eq_one {R : Type} [CommRing R] (z v : GG 3 R) (h : z.right = 1) :
    (z * v).mat = z.mat * v.mat := by
  show ((z * v).left : Matrix (Fin 3) (Fin 3) R) = _
  rw [SemidirectProduct.mul_left, h, map_one]
  rfl

/- English proof (translation)
Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp_all [wt, wt1]`.
-/
private theorem eq_of_wt_eq_zero (a b : Fin 3) (h : wt a b = 0) : a = b := by
  fin_cases a <;> fin_cases b <;> simp_all [wt, wt1]

/- English proof (translation)
Use `haveI : Finite R := hs.fin`. Use `haveI : Finite R' := Finite.of_surjective p hp`. Take `⟨B, dg, hB, hdg⟩` from `lt_diag (R := R')`. Take `⟨B0, dg0, hB0, hdg0⟩` from `lt_diag (R := R)`. Take `⟨S, hS⟩` from `lt_grSub (O := O) 𝒜`.

Set `rB : D →* B` to `r'.codRestrict B (fun g => (hB _).2 (hup g))`. Set `u' : D →* GG 3 R'` to `dg.comp rB`. Establish `hu'mat : ∀ g, (u' g).mat = Matrix.diagonal fun a => (r' g).mat a a` using `fun g => (hdg (rB g)).2`. Establish `hu'right : ∀ g, (u' g).right = η g` using `fun g => (hdg (rB g)).1.trans (hr.mult g)`. Establish `hu'lc : IsLocallyConstant (mats u')`.

Establish `e : mats u' = (fun M : Matrix (Fin 3) (Fin 3) R' => Matrix.diagonal fun a => M a a) ∘ mats r'`. Use function extensionality and compare the values at `hu'mat`. Rewrite using `[e]`. Conclude with `hlc.comp _`. Establish `hu'diag : ∀ g, (u' g).mat.IsDiag`.

Introduce `g`. Rewrite using `[hu'mat]`. Conclude with `Matrix.isDiag_diagonal _`. Establish `hu'A : ∀ g a, ∃ y ∈ SetLike.GradeZero.subalgebra 𝒜, p y = (u' g).mat a a`. Introduce `g a`.

Take `⟨X, hX, hXp⟩` from `hgr g`. Use `⟨X a a, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `hX a a`. Rewrite `h` using `[wt_self]`. Conclude with `h`.

Rewrite using `[hu'mat, Matrix.diagonal_apply_eq, ← hXp]`. Both sides reduce to the same expression. Establish `hu'I : ∀ s ∈ I, ∀ a, (u' s).mat a a = algebraMap O R' (psi Ψ a s)`. Introduce `s hsI a`. Rewrite using `[hu'mat, Matrix.diagonal_apply_eq, hI s hsI a]`.

Take `⟨u, hpu, hulc, hudiag, huA, huI⟩` from `lt_torus (SetLike.GradeZero.subalgebra 𝒜) p hp η Ψ I φ hφ hd hη hηI hΨ u' hu'right hu'lc hu'diag hu'A hu'I`. Establish `hur : ∀ g, (u g).right = η g` using `fun g => (congrArg SemidirectProduct.right (DFunLike.congr_fun hpu g)).trans (hu'right g)`. Establish `hupm : ∀ g, (u g).mat.map p = (u' g).mat` using `fun g => congrArg GG.mat (DFunLike.congr_fun hpu g)`. Set `P : GG 3 R' → GG 3 R → GG 3 R → Prop` to `fun y t x => GG.map (p : R →+* R') x = y ∧ GrMat 𝒜 x.mat ∧ (∀ a b, wt a b < 0 → x.mat a b = 0) ∧ ∀ a, x.mat a a = t.mat a a`. Set `L : GG 3 R' → GG 3 R → GG 3 R` to `fun y t => if h : ∃ x, P y t x then h.choose else 1`.

Set `s : D → GG 3 R` to `fun g => L (r' g) (u g)`. Establish `hsP : ∀ g, P (r' g) (u g) (s g)`. Introduce `g`. Establish `h : ∃ x, P (r' g) (u g) x`. Apply `lift_elt 𝒜 p hp (r' g) (u g) (hup g) (hgr g)` to reduce the goal to its premises.

Introduce `a`. Conclude with `huA g a`. Introduce `a`. Establish `h1` using `congrFun (congrFun (hupm g) a) a`. Rewrite `h1` using `[hu'mat, Matrix.diagonal_apply_eq]`.

Conclude with `h1`. Simplify using `only [s, L, dif_pos h]`. Conclude with `h.choose_spec`. Establish `hr'lc : IsLocallyConstant r'` using `lc_hom η r' hη hr.mult hlc`. Establish `hulc' : IsLocallyConstant u` using `lc_hom η u hη hur hulc`.

Establish `hslc : IsLocallyConstant s` using `(hr'lc.prodMk hulc').comp (fun q => L q.1 q.2)`. Establish `hsr : ∀ g, (s g).right = η g` using `fun g => (congrArg SemidirectProduct.right (hsP g).1).trans (hr.mult g)`. Establish `hsred : ∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R))`. Introduce `g a b`. Establish `h1` using `hr.red g a b`.

Assume the negation of the conclusion as `hn`. Establish `hu : IsUnit (((s g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R)) a b)`. Assume the negation of the conclusion as `h`. Conclude with `hn ((IsLocalRing.mem_maximalIdeal _).2 h)`. Apply `(IsLocalRing.mem_maximalIdeal _).1 h1` to reduce the goal to its premises.

Establish `e : p (((s g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R)) a b) = ((r' g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R')) a b`. Rewrite using `[Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.map_apply, AlgHom.commutes]`. Use `congr 1`. Rewrite using `[← (hsP g).1]`. Both sides reduce to the same expression.

Rewrite using `[← e]`. Conclude with `hu.map p`. Establish `hsB : ∀ g, s g ∈ B0` using `fun g => (hB0 _).2 (hsP g).2.2.1`. Establish `hsS : ∀ g, s g ∈ S` using `fun g => (hS _).2 (hsP g).2.1`. Establish `hdgs : ∀ g, dg0 ⟨s g, hsB g⟩ = u g`.

Introduce `g`. Apply `gg_ext` to reduce the goal to its premises. Rewrite using `[(hdg0 _).2, ← (hudiag g).diagonal_diag]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Conclude with `(hsP g).2.2.2 a`. Rewrite using `[(hdg0 _).1]`. Conclude with `(hsr g).trans (hur g).symm`. Establish `hone : ∀ a b, (1 : Matrix (Fin 3) (Fin 3) R) a b ∈ 𝒜 (wt a b)`. Introduce `a b`.

Rewrite using `[Matrix.one_apply]`. Use `split_ifs with hab`. Substitute `hab` using the available equality. Rewrite using `[wt_self]`. Conclude with `SetLike.GradedOne.one_mem`.

Conclude with `Submodule.zero_mem _`. Establish `hcoc : ∀ g h, ∃ c : Matrix (Fin 3) (Fin 3) R, c ∈ gw R j ∧ EntIn (RingHom.ker p) c ∧ (∀ a, c a a = 0) ∧ (∀ a b, wt a b < 0 → c a b = 0) ∧ (s g * s h).mat = (1 + c) * (s (g * h)).mat`. Introduce `g h`. Use `set z := s g * s h * (s (g * h))⁻¹ with hz`. Establish `hzr : z.right = 1`.

Simplify using `only [hz, SemidirectProduct.mul_right, SemidirectProduct.inv_right, hsr, map_mul]`. Conclude with `mul_inv_cancel _`. Establish `hzB : z ∈ B0` using `B0.mul_mem (B0.mul_mem (hsB g) (hsB h)) (B0.inv_mem (hsB _))`. Establish `hzS : z ∈ S` using `S.mul_mem (S.mul_mem (hsS g) (hsS h)) (S.inv_mem (hsS _))`. Establish `hzp : GG.map (p : R →+* R') z = 1`.

Simplify using `only [hz, map_mul, map_inv, (hsP _).1, r'.map_mul, mul_inv_cancel]`. Establish `hzd : ∀ a, z.mat a a = 1`. Introduce `a`. Establish `e : dg0 ⟨z, hzB⟩ = 1`. Establish `e0 : (⟨z, hzB⟩ : B0) = ⟨s g, hsB g⟩ * ⟨s h, hsB h⟩ * (⟨s (g * h), hsB _⟩)⁻¹` using `rfl`.

Rewrite using `[e0, map_mul, map_mul, map_inv, hdgs, hdgs, hdgs, ← u.map_mul, mul_inv_cancel]`. Establish `e2` using `(hdg0 ⟨z, hzB⟩).2`. Rewrite `e2` using `[e]`. Establish `e3` using `congrFun (congrFun e2 a) a`. Establish `e4 : (1 : GG 3 R).mat = 1` using `rfl`.

Rewrite `e3` using `[e4, Matrix.one_apply_eq, Matrix.diagonal_apply_eq]`. Conclude with `e3.symm`. Establish `hzK : ∀ a b, (z.mat - 1) a b ∈ RingHom.ker p`. Introduce `a b`. Rewrite using `[RingHom.mem_ker, Matrix.sub_apply, map_sub]`.

Establish `e1 : p (z.mat a b) = (GG.map (p : R →+* R') z).mat a b` using `rfl`. Rewrite using `[e1, hzp]`. Express the relevant statement in the definitionally equal form `(1 : Matrix (Fin 3) (Fin 3) R') a b - p ((1 : Matrix (Fin 3) (Fin 3) R) a b) = 0`. Rewrite using `[Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hzg : GrMat 𝒜 z.mat` using `(hS z).1 hzS`. Use `⟨z.mat - 1, ?_, hzK, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b hne`. Conclude with `gr_eq_zero 𝒜 (Submodule.sub_mem _ (hzg a b) (hone a b)) (hs.wt _ (hzK a b)) hne`. Introduce `a`.

Rewrite using `[Matrix.sub_apply, hzd, Matrix.one_apply_eq, sub_self]`. Introduce `a b hab`. Establish `hne : a ≠ b`. Introduce and unpack `rfl`. Rewrite `hab` using `[wt_self]`.

Conclude with `lt_irrefl _ hab`. Rewrite using `[Matrix.sub_apply, (hB0 z).1 hzB a b hab, Matrix.one_apply_ne hne, sub_self]`. Rewrite using `[add_sub_cancel, ← gg_mul_mat_of_right_eq_one z (s (g * h)) hzr, hz, inv_mul_cancel_right]`. Choose the witnesses or unpack the hypotheses as in `⟨r, hrlc, hrg⟩ : ∃ r : D →* GG 3 R, IsLocallyConstant (mats r) ∧ ∀ g, (r g).right = η g ∧ ∃ b : Matrix (Fin 3) (Fin 3) R, (∀ a c, wt a c ≤ 0 → b a c = 0) ∧ EntIn (RingHom.ker p) b ∧ GrMat 𝒜 b ∧ (r g).mat = (1 + b) * (s g).mat := by`. Distinguish the cases in `hj : 0 < j`.

Take `⟨r, hrlc, hrg⟩` from `lt_corr η Ψ (RingHom.ker p) j hs.kill hs.le (h2 hj) s hslc hsr hsred (fun g h => by`. Take `⟨c, hc, hcK, -, -, hce⟩` from `hcoc g h`. Conclude with `⟨c, hc, hcK, hce⟩)`. Use `⟨r, hrlc, fun g => ⟨(hrg g).1, ?_⟩⟩` and prove the remaining obligations. Take `⟨b, hb, hbK, hbe⟩` from `(hrg g).2`.

Use `⟨b, ?_, hbK, ?_, hbe⟩` and prove the remaining obligations. Introduce `a c hac`. Conclude with `hb a c (by omega)`. Introduce `a c`. Distinguish the cases in `hw : wt a c = j`.

Rewrite using `[hw]`. Conclude with `hs.wt _ (hbK a c)`. Rewrite using `[hb a c hw]`. Conclude with `Submodule.zero_mem _`. Establish `hmul : ∀ g h, s (g * h) = s g * s h`.

Introduce `g h`. Take `⟨c, hc, -, hcd, hcl, hce⟩` from `hcoc g h`. Establish `hc0 : c = 0`. Use extensionality with `a b`. Distinguish the cases in `hw : wt a b = j`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Conclude with `hcd a`. Establish `hlt : wt a b < 0`. Use `mt (eq_of_wt_eq_zero a b) hab` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `hcl a b hlt`. Conclude with `hc a b hw`. Apply `gg_ext` to reduce the goal to its premises. Rewrite using `[hce, hc0, add_zero, one_mul]`.

Rewrite using `[SemidirectProduct.mul_right, hsr, hsr, hsr, map_mul]`. Use `⟨MonoidHom.mk' s hmul, hslc.comp GG.mat, fun g => ⟨hsr g, 0, fun _ _ _ => rfl, fun a b => Ideal.zero_mem _, fun a b => Submodule.zero_mem _, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[add_zero, one_mul]`. Both sides reduce to the same expression. Use `⟨r, ?_, hrlc, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `g : 1`. Apply `gg_ext` to reduce the goal to its premises. Take `⟨b, -, hbK, -, hbe⟩` from `(hrg g).2`. Express the relevant statement in the definitionally equal form `(r g).mat.map (p : R →+* R') = (r' g).mat`. Rewrite using `[hbe, Matrix.map_mul, ← (hsP g).1]`.

Establish `hb0 : (1 + b).map (p : R →+* R') = 1`. Use extensionality with `a c`. Express the relevant statement in the definitionally equal form `p ((1 + b) a c) = (1 : Matrix (Fin 3) (Fin 3) R') a c`. Rewrite using `[Matrix.add_apply, map_add, RingHom.mem_ker.1 (hbK a c), add_zero, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite using `[hb0, one_mul]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(r g).right = (r' g).right`. Rewrite using `[(hrg g).1, hr.mult g]`. Introduce `g`.

Take `⟨b, -, -, hbg, hbe⟩` from `(hrg g).2`. Rewrite using `[hbe]`. Apply `grMat_mul 𝒜 _ (hsP g).2.1` to reduce the goal to its premises. Introduce `a c`. Rewrite using `[Matrix.add_apply]`.

Conclude with `Submodule.add_mem _ (hone a c) (hbg a c)`. Introduce `g a c hac`. Take `⟨b, hb, -, -, hbe⟩` from `(hrg g).2`. Rewrite using `[hbe, strict_mul hb (hsP g).2.2.1 a c hac.le]`. Conclude with `(hsP g).2.2.1 a c hac`.

Introduce `t ht a`. Take `⟨b, hb, -, -, hbe⟩` from `(hrg t).2`. Rewrite using `[hbe, strict_mul hb (hsP t).2.2.1 a a (by rw [wt_self]), (hsP t).2.2.2 a, huI t ht a]`.
-/
private theorem tri_lift {O R R' D : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ) (hp : Function.Surjective p)
    (hs : SmallExt O 𝒜 (RingHom.ker p) j) (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (φ : D)
    (hφ : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (hη : IsLocallyConstant η) (hηI : ∀ s ∈ I, η s = 1) (hΨ : IsLocallyConstant fun g => algebraMap O R (Ψ g : O))
    (h2 : 0 < j → Subsingleton (H2 (gRep η ((Units.map (residue O).toMonoidHom).comp Ψ) j)))
    (r' : D →* GG 3 R') (hr : Red η Ψ r') (hlc : IsLocallyConstant (mats r'))
    (hup : ∀ g a b, wt a b < 0 → (r' g).mat a b = 0)
    (hI : ∀ s ∈ I, ∀ a, (r' s).mat a a = algebraMap O R' (psi Ψ a s))
    (hgr : ∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) :
    ∃ r : D →* GG 3 R, push p r = r' ∧ IsLocallyConstant (mats r) ∧ (∀ g, GrMat 𝒜 (r g).mat) ∧
      (∀ g a b, wt a b < 0 → (r g).mat a b = 0) ∧ ∀ s ∈ I, ∀ a, (r s).mat a a = algebraMap O R (psi Ψ a s) := by
  classical
  haveI : Finite R := hs.fin
  haveI : Finite R' := Finite.of_surjective p hp
  obtain ⟨B, dg, hB, hdg⟩ := lt_diag (R := R')
  obtain ⟨B0, dg0, hB0, hdg0⟩ := lt_diag (R := R)
  obtain ⟨S, hS⟩ := lt_grSub (O := O) 𝒜
  let rB : D →* B := r'.codRestrict B (fun g => (hB _).2 (hup g))
  let u' : D →* GG 3 R' := dg.comp rB
  have hu'mat : ∀ g, (u' g).mat = Matrix.diagonal fun a => (r' g).mat a a := fun g => (hdg (rB g)).2
  have hu'right : ∀ g, (u' g).right = η g := fun g => (hdg (rB g)).1.trans (hr.mult g)
  have hu'lc : IsLocallyConstant (mats u') := by
    have e : mats u' = (fun M : Matrix (Fin 3) (Fin 3) R' => Matrix.diagonal fun a => M a a) ∘ mats r' :=
      funext hu'mat
    rw [e]
    exact hlc.comp _
  have hu'diag : ∀ g, (u' g).mat.IsDiag := by
    intro g
    rw [hu'mat]
    exact Matrix.isDiag_diagonal _
  have hu'A : ∀ g a, ∃ y ∈ SetLike.GradeZero.subalgebra 𝒜, p y = (u' g).mat a a := by
    intro g a
    obtain ⟨X, hX, hXp⟩ := hgr g
    refine ⟨X a a, ?_, ?_⟩
    · have h := hX a a
      rw [wt_self] at h
      exact h
    · rw [hu'mat, Matrix.diagonal_apply_eq, ← hXp]
      rfl
  have hu'I : ∀ s ∈ I, ∀ a, (u' s).mat a a = algebraMap O R' (psi Ψ a s) := by
    intro s hsI a
    rw [hu'mat, Matrix.diagonal_apply_eq, hI s hsI a]
  obtain ⟨u, hpu, hulc, hudiag, huA, huI⟩ := lt_torus (SetLike.GradeZero.subalgebra 𝒜) p hp η Ψ I φ hφ hd hη hηI hΨ
    u' hu'right hu'lc hu'diag hu'A hu'I
  have hur : ∀ g, (u g).right = η g := fun g =>
    (congrArg SemidirectProduct.right (DFunLike.congr_fun hpu g)).trans (hu'right g)
  have hupm : ∀ g, (u g).mat.map p = (u' g).mat := fun g =>
    congrArg GG.mat (DFunLike.congr_fun hpu g)
  let P : GG 3 R' → GG 3 R → GG 3 R → Prop := fun y t x =>
    GG.map (p : R →+* R') x = y ∧ GrMat 𝒜 x.mat ∧ (∀ a b, wt a b < 0 → x.mat a b = 0) ∧ ∀ a, x.mat a a = t.mat a a
  let L : GG 3 R' → GG 3 R → GG 3 R := fun y t => if h : ∃ x, P y t x then h.choose else 1
  let s : D → GG 3 R := fun g => L (r' g) (u g)
  have hsP : ∀ g, P (r' g) (u g) (s g) := by
    intro g
    have h : ∃ x, P (r' g) (u g) x := by
      apply lift_elt 𝒜 p hp (r' g) (u g) (hup g) (hgr g)
      · intro a
        exact huA g a
      · intro a
        have h1 := congrFun (congrFun (hupm g) a) a
        rw [hu'mat, Matrix.diagonal_apply_eq] at h1
        exact h1
    simp only [s, L, dif_pos h]
    exact h.choose_spec
  have hr'lc : IsLocallyConstant r' := lc_hom η r' hη hr.mult hlc
  have hulc' : IsLocallyConstant u := lc_hom η u hη hur hulc
  have hslc : IsLocallyConstant s := (hr'lc.prodMk hulc').comp (fun q => L q.1 q.2)
  have hsr : ∀ g, (s g).right = η g := fun g =>
    (congrArg SemidirectProduct.right (hsP g).1).trans (hr.mult g)
  have hsred : ∀ g, EntIn (maximalIdeal R) ((s g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R)) := by
    intro g a b
    have h1 := hr.red g a b
    by_contra hn
    have hu : IsUnit (((s g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R)) a b) := by
      by_contra h
      exact hn ((IsLocalRing.mem_maximalIdeal _).2 h)
    apply (IsLocalRing.mem_maximalIdeal _).1 h1
    have e : p (((s g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R)) a b) =
        ((r' g).mat - ((r0 η Ψ) g).mat.map (algebraMap O R')) a b := by
      rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.map_apply, AlgHom.commutes]
      congr 1
      rw [← (hsP g).1]
      rfl
    rw [← e]
    exact hu.map p
  have hsB : ∀ g, s g ∈ B0 := fun g => (hB0 _).2 (hsP g).2.2.1
  have hsS : ∀ g, s g ∈ S := fun g => (hS _).2 (hsP g).2.1
  have hdgs : ∀ g, dg0 ⟨s g, hsB g⟩ = u g := by
    intro g
    apply gg_ext
    · rw [(hdg0 _).2, ← (hudiag g).diagonal_diag]
      congr 1
      funext a
      exact (hsP g).2.2.2 a
    · rw [(hdg0 _).1]
      exact (hsr g).trans (hur g).symm
  have hone : ∀ a b, (1 : Matrix (Fin 3) (Fin 3) R) a b ∈ 𝒜 (wt a b) := by
    intro a b
    rw [Matrix.one_apply]
    split_ifs with hab
    · subst hab
      rw [wt_self]
      exact SetLike.GradedOne.one_mem
    · exact Submodule.zero_mem _
  have hcoc : ∀ g h, ∃ c : Matrix (Fin 3) (Fin 3) R, c ∈ gw R j ∧ EntIn (RingHom.ker p) c ∧
      (∀ a, c a a = 0) ∧ (∀ a b, wt a b < 0 → c a b = 0) ∧
      (s g * s h).mat = (1 + c) * (s (g * h)).mat := by
    intro g h
    set z := s g * s h * (s (g * h))⁻¹ with hz
    have hzr : z.right = 1 := by
      simp only [hz, SemidirectProduct.mul_right, SemidirectProduct.inv_right, hsr, map_mul]
      exact mul_inv_cancel _
    have hzB : z ∈ B0 := B0.mul_mem (B0.mul_mem (hsB g) (hsB h)) (B0.inv_mem (hsB _))
    have hzS : z ∈ S := S.mul_mem (S.mul_mem (hsS g) (hsS h)) (S.inv_mem (hsS _))
    have hzp : GG.map (p : R →+* R') z = 1 := by
      simp only [hz, map_mul, map_inv, (hsP _).1, r'.map_mul, mul_inv_cancel]
    have hzd : ∀ a, z.mat a a = 1 := by
      intro a
      have e : dg0 ⟨z, hzB⟩ = 1 := by
        have e0 : (⟨z, hzB⟩ : B0) = ⟨s g, hsB g⟩ * ⟨s h, hsB h⟩ * (⟨s (g * h), hsB _⟩)⁻¹ := rfl
        rw [e0, map_mul, map_mul, map_inv, hdgs, hdgs, hdgs, ← u.map_mul, mul_inv_cancel]
      have e2 := (hdg0 ⟨z, hzB⟩).2
      rw [e] at e2
      have e3 := congrFun (congrFun e2 a) a
      have e4 : (1 : GG 3 R).mat = 1 := rfl
      rw [e4, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at e3
      exact e3.symm
    have hzK : ∀ a b, (z.mat - 1) a b ∈ RingHom.ker p := by
      intro a b
      rw [RingHom.mem_ker, Matrix.sub_apply, map_sub]
      have e1 : p (z.mat a b) = (GG.map (p : R →+* R') z).mat a b := rfl
      rw [e1, hzp]
      change (1 : Matrix (Fin 3) (Fin 3) R') a b - p ((1 : Matrix (Fin 3) (Fin 3) R) a b) = 0
      rw [Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have hzg : GrMat 𝒜 z.mat := (hS z).1 hzS
    refine ⟨z.mat - 1, ?_, hzK, ?_, ?_, ?_⟩
    · intro a b hne
      exact gr_eq_zero 𝒜 (Submodule.sub_mem _ (hzg a b) (hone a b)) (hs.wt _ (hzK a b)) hne
    · intro a
      rw [Matrix.sub_apply, hzd, Matrix.one_apply_eq, sub_self]
    · intro a b hab
      have hne : a ≠ b := by
        rintro rfl
        rw [wt_self] at hab
        exact lt_irrefl _ hab
      rw [Matrix.sub_apply, (hB0 z).1 hzB a b hab, Matrix.one_apply_ne hne, sub_self]
    · rw [add_sub_cancel, ← gg_mul_mat_of_right_eq_one z (s (g * h)) hzr, hz, inv_mul_cancel_right]
  obtain ⟨r, hrlc, hrg⟩ : ∃ r : D →* GG 3 R, IsLocallyConstant (mats r) ∧ ∀ g, (r g).right = η g ∧
      ∃ b : Matrix (Fin 3) (Fin 3) R, (∀ a c, wt a c ≤ 0 → b a c = 0) ∧ EntIn (RingHom.ker p) b ∧
        GrMat 𝒜 b ∧ (r g).mat = (1 + b) * (s g).mat := by
    by_cases hj : 0 < j
    · obtain ⟨r, hrlc, hrg⟩ := lt_corr η Ψ (RingHom.ker p) j hs.kill hs.le (h2 hj) s hslc hsr hsred
        (fun g h => by
          obtain ⟨c, hc, hcK, -, -, hce⟩ := hcoc g h
          exact ⟨c, hc, hcK, hce⟩)
      refine ⟨r, hrlc, fun g => ⟨(hrg g).1, ?_⟩⟩
      obtain ⟨b, hb, hbK, hbe⟩ := (hrg g).2
      refine ⟨b, ?_, hbK, ?_, hbe⟩
      · intro a c hac
        exact hb a c (by omega)
      · intro a c
        by_cases hw : wt a c = j
        · rw [hw]
          exact hs.wt _ (hbK a c)
        · rw [hb a c hw]
          exact Submodule.zero_mem _
    · have hmul : ∀ g h, s (g * h) = s g * s h := by
        intro g h
        obtain ⟨c, hc, -, hcd, hcl, hce⟩ := hcoc g h
        have hc0 : c = 0 := by
          ext a b
          by_cases hw : wt a b = j
          · by_cases hab : a = b
            · subst hab
              exact hcd a
            · have hlt : wt a b < 0 := by
                have := mt (eq_of_wt_eq_zero a b) hab
                omega
              exact hcl a b hlt
          · exact hc a b hw
        apply gg_ext
        · rw [hce, hc0, add_zero, one_mul]
        · rw [SemidirectProduct.mul_right, hsr, hsr, hsr, map_mul]
      refine ⟨MonoidHom.mk' s hmul, hslc.comp GG.mat, fun g => ⟨hsr g, 0, fun _ _ _ => rfl,
        fun a b => Ideal.zero_mem _, fun a b => Submodule.zero_mem _, ?_⟩⟩
      rw [add_zero, one_mul]
      rfl
  refine ⟨r, ?_, hrlc, ?_, ?_, ?_⟩
  · ext g : 1
    apply gg_ext
    · obtain ⟨b, -, hbK, -, hbe⟩ := (hrg g).2
      change (r g).mat.map (p : R →+* R') = (r' g).mat
      rw [hbe, Matrix.map_mul, ← (hsP g).1]
      have hb0 : (1 + b).map (p : R →+* R') = 1 := by
        ext a c
        change p ((1 + b) a c) = (1 : Matrix (Fin 3) (Fin 3) R') a c
        rw [Matrix.add_apply, map_add, RingHom.mem_ker.1 (hbK a c), add_zero, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      rw [hb0, one_mul]
      rfl
    · change (r g).right = (r' g).right
      rw [(hrg g).1, hr.mult g]
  · intro g
    obtain ⟨b, -, -, hbg, hbe⟩ := (hrg g).2
    rw [hbe]
    apply grMat_mul 𝒜 _ (hsP g).2.1
    intro a c
    rw [Matrix.add_apply]
    exact Submodule.add_mem _ (hone a c) (hbg a c)
  · intro g a c hac
    obtain ⟨b, hb, -, -, hbe⟩ := (hrg g).2
    rw [hbe, strict_mul hb (hsP g).2.2.1 a c hac.le]
    exact (hsP g).2.2.1 a c hac
  · intro t ht a
    obtain ⟨b, hb, -, -, hbe⟩ := (hrg t).2
    rw [hbe, strict_mul hb (hsP t).2.2.1 a a (by rw [wt_self]), (hsP t).2.2.2 a, huI t ht a]

/- English proof (translation)
Establish `hdet : IsUnit M.det`. Apply `isUnit_of_isUnit_surjective_localRingHom (p : R →+* R') hp` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply]`. Establish `e : M.map (p : R →+* R') = y.mat` using `hM`. Rewrite using `[e]`.

Conclude with `Matrix.isUnits_det_units y.left`. Use `⟨⟨Matrix.nonsingInvUnit M hdet, y.right⟩, ?_, rfl⟩` and prove the remaining obligations. Apply `SemidirectProduct.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Conclude with `hM`.

Both sides reduce to the same expression.
-/
private theorem lift_gg {O R R' : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [CommRing R']
    [IsLocalRing R'] [Algebra O R'] (p : R →ₐ[O] R') (hp : Function.Surjective p)
    (y : GG 3 R') (M : Matrix (Fin 3) (Fin 3) R) (hM : M.map p = y.mat) :
    ∃ x : GG 3 R, GG.map (p : R →+* R') x = y ∧ x.mat = M := by
  have hdet : IsUnit M.det := by
    apply isUnit_of_isUnit_surjective_localRingHom (p : R →+* R') hp
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have e : M.map (p : R →+* R') = y.mat := hM
    rw [e]
    exact Matrix.isUnits_det_units y.left
  refine ⟨⟨Matrix.nonsingInvUnit M hdet, y.right⟩, ?_, rfl⟩
  apply SemidirectProduct.ext
  · apply Units.ext
    exact hM
  · rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem conjBy_app {C D : Type} [CommRing C] [Group D] (h : GL (Fin 3) C) (r : D →* GG 3 C) (g : D) :
    conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl

/- English proof (translation)
Simplify using `[GG.map, GG.ofGL, SemidirectProduct.map_inl]`.
-/
private theorem map_ofGL {C C' : Type} [CommRing C] [CommRing C'] (f : C →+* C') (h : GL (Fin 3) C) :
    GG.map f (GG.ofGL h) = GG.ofGL (GeneralLinearGroup.map f h) := by
  simp [GG.map, GG.ofGL, SemidirectProduct.map_inl]

end UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Introduce `O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hV R R' _ _ _ _ _ _ 𝒜 _ p j hp hs v hv r' hr hloc hlc hgr`. Substitute `hv` using the available equality. Use `haveI : Finite R := hs.fin`. Establish `hvT : F.vl ∈ F.Tb` using `Set.mem_insert _ _`. Establish `hlocc : Continuous (F.loc F.vl)` using `hF.π_cont.comp continuous_subtype_val`.

Establish `hηlc : IsLocallyConstant (F.ηv F.vl)` using `hF.η_cont.comp_continuous hlocc`. Take `⟨x, hx1, hx2⟩` from `hF.x F.vl hvT`. Take `⟨h, hhin, hhg, hh'in, hhtri⟩` from `lt_basis 𝒜 p hp (F.ηv F.vl) (F.Ψv F.vl) (F.Iv F.vl) r' x hr hx1 hx2 (hloc.1 rfl) (hgr x)`. Use `set h' := GeneralLinearGroup.map (p : R →+* R') h with hh'`. Take `⟨hinv, -, -⟩` from `lt_red_conj (F.ηv F.vl) (F.Ψv F.vl) r' h' hh'in hr`.

Take `⟨-, hr'', hlc''⟩` from `lt_red_conj (F.ηv F.vl) (F.Ψv F.vl) r' h'⁻¹ hinv hr`. Establish `hup : ∀ g a b, wt a b < 0 → ((conjBy h'⁻¹ r') g).mat a b = 0` using `lt_upper _ _ _ x hr'' hx1 hx2 hhtri.tri`. Establish `hI : ∀ s ∈ F.Iv F.vl, ∀ a, ((conjBy h'⁻¹ r') s).mat a a = algebraMap O R' (psi (F.Ψv F.vl) a s)` using `fun s hs a => hhtri.ine s hs (hF.η_I F.vl hvT s hs) a`. Take `⟨S, hS⟩` from `lt_grSub (O := O) 𝒜`. Establish `hhS : GG.ofGL h ∈ S` using `(hS _).2 hhg`.

Establish `hmapS : GG.map (p : R →+* R') (GG.ofGL h) = GG.ofGL h'` using `map_ofGL _ h`. Establish `hgr'' : ∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = ((conjBy h'⁻¹ r') g).mat`. Introduce `g`. Take `⟨X, hX, hXp⟩` from `hgr g`. Take `⟨y, hy, hyX⟩` from `lift_gg p hp (r' g) X hXp`.

Establish `hyS : y ∈ S` using `(hS _).2 (hyX ▸ hX)`. Use `⟨((GG.ofGL h)⁻¹ * y * GG.ofGL h).mat, (hS _).1 (S.mul_mem (S.mul_mem (S.inv_mem hhS) hyS) hhS), ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(GG.map (p : R →+* R') ((GG.ofGL h)⁻¹ * y * GG.ofGL h)).mat = _`. Rewrite using `[map_mul, map_mul, map_inv, hmapS, hy, conjBy_app, map_inv, inv_inv]`. Establish `hΨ : IsLocallyConstant fun g => algebraMap O R ((F.Ψv F.vl g : Oˣ) : O)` using `psi_lc (fun g => ((F.Ψv F.vl g : Oˣ) : O)) (fun n => (hF.Ψ_cont n).comp_continuous hlocc)`.

Establish `h2 : 0 < j → Subsingleton (H2 (gRep (F.ηv F.vl) ((Units.map (residue O).toMonoidHom).comp (F.Ψv F.vl)) j))` using `fun hj => hV.h2 F.vl hvT j (ne_of_gt hj)`. Take `⟨φ, hφ, hd⟩` from `hF.frob F.vl`. Take `⟨r0', hpush, hlc0, hgr0, hup0, hI0⟩` from `tri_lift 𝒜 p j hp hs (F.ηv F.vl) (F.Ψv F.vl) (F.Iv F.vl) φ hφ hd hηlc (hF.η_I F.vl hvT) hΨ h2 (conjBy h'⁻¹ r') hr'' (hlc'' hηlc hlc) hup hI hgr''`. Establish `hr0r : ∀ g, (r0' g).right = F.ηv F.vl g` using `fun g => (congrArg SemidirectProduct.right (DFunLike.congr_fun hpush g)).trans (hr''.mult g)`. Establish `hr0lc : IsLocallyConstant r0'` using `lc_hom _ r0' hηlc hr0r hlc0`.

Establish `hback : conjBy h⁻¹ (conjBy h r0') = r0'`. Use extensionality with `g : 1`. Rewrite using `[conjBy_app, conjBy_app, map_inv]`. Use `group`. Use `⟨conjBy h r0', ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use extensionality with `g : 1`. Express the relevant statement in the definitionally equal form `GG.map (p : R →+* R') ((conjBy h r0') g) = r' g`. Rewrite using `[conjBy_app, map_mul, map_mul, map_inv, hmapS]`. Establish `e` using `DFunLike.congr_fun hpush g`. Express the relevant statement in the definitionally equal form `GG.map (p : R →+* R') (r0' g) = (conjBy h'⁻¹ r') g at e`.

Rewrite using `[e, conjBy_app, map_inv, inv_inv]`. Use `group`. Unfold `Frame.LocAt`. Use `⟨fun _ => ⟨h, hhin, ?_, ?_⟩, fun hSb => absurd hSb hF.vl_notMem, fun hT => absurd hvT hT⟩` and prove the remaining obligations. Rewrite using `[hback]`.

Introduce `g _ a b hab`. Conclude with `hup0 g a b hab`. Rewrite using `[hback]`. Introduce `s hs _ a`. Conclude with `hI0 s hs a`.

Establish `e : mats (conjBy h r0') = GG.mat ∘ (fun y => GG.ofGL h * y * (GG.ofGL h)⁻¹) ∘ r0'`. Use function extensionality and compare the values at `g`. Use `show ((conjBy h r0') g).mat = (GG.ofGL h * r0' g * (GG.ofGL h)⁻¹).mat`. Rewrite using `[conjBy_app]`. Rewrite using `[e]`.

Conclude with `(hr0lc.comp _).comp _`. Introduce `g`. Rewrite using `[conjBy_app]`. Conclude with `(hS _).1 (S.mul_mem (S.mul_mem hhS ((hS _).2 (hgr0 g))) (S.inv_mem hhS))`.
-/
theorem UpperTheory.V.UnitaryThreeInertia.exists_graded_lift_unitary_local_tame :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ), Function.Surjective p → SmallExt O 𝒜 (RingHom.ker p) j →
    ∀ (v : ι), v = F.vl → ∀ (r' : F.D v →* GG 3 R'), Red (F.ηv v) (F.Ψv v) r' → F.LocAt v r' → IsLocallyConstant (mats r') →
      (∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) →
      ∃ r : F.D v →* GG 3 R, push p r = r' ∧ F.LocAt v r ∧ IsLocallyConstant (mats r) ∧ ∀ g, GrMat 𝒜 (r g).mat := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hV R R' _ _ _ _ _ _ 𝒜 _ p j hp hs v hv r' hr hloc hlc hgr
  subst hv
  classical
  haveI : Finite R := hs.fin
  have hvT : F.vl ∈ F.Tb := Set.mem_insert _ _
  have hlocc : Continuous (F.loc F.vl) := hF.π_cont.comp continuous_subtype_val
  have hηlc : IsLocallyConstant (F.ηv F.vl) := hF.η_cont.comp_continuous hlocc
  obtain ⟨x, hx1, hx2⟩ := hF.x F.vl hvT
  obtain ⟨h, hhin, hhg, hh'in, hhtri⟩ := lt_basis 𝒜 p hp (F.ηv F.vl) (F.Ψv F.vl) (F.Iv F.vl) r' x hr hx1 hx2
    (hloc.1 rfl) (hgr x)
  set h' := GeneralLinearGroup.map (p : R →+* R') h with hh'
  obtain ⟨hinv, -, -⟩ := lt_red_conj (F.ηv F.vl) (F.Ψv F.vl) r' h' hh'in hr
  obtain ⟨-, hr'', hlc''⟩ := lt_red_conj (F.ηv F.vl) (F.Ψv F.vl) r' h'⁻¹ hinv hr
  have hup : ∀ g a b, wt a b < 0 → ((conjBy h'⁻¹ r') g).mat a b = 0 :=
    lt_upper _ _ _ x hr'' hx1 hx2 hhtri.tri
  have hI : ∀ s ∈ F.Iv F.vl, ∀ a, ((conjBy h'⁻¹ r') s).mat a a = algebraMap O R' (psi (F.Ψv F.vl) a s) :=
    fun s hs a => hhtri.ine s hs (hF.η_I F.vl hvT s hs) a
  obtain ⟨S, hS⟩ := lt_grSub (O := O) 𝒜
  have hhS : GG.ofGL h ∈ S := (hS _).2 hhg
  have hmapS : GG.map (p : R →+* R') (GG.ofGL h) = GG.ofGL h' := map_ofGL _ h
  have hgr'' : ∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = ((conjBy h'⁻¹ r') g).mat := by
    intro g
    obtain ⟨X, hX, hXp⟩ := hgr g
    obtain ⟨y, hy, hyX⟩ := lift_gg p hp (r' g) X hXp
    have hyS : y ∈ S := (hS _).2 (hyX ▸ hX)
    refine ⟨((GG.ofGL h)⁻¹ * y * GG.ofGL h).mat, (hS _).1 (S.mul_mem (S.mul_mem (S.inv_mem hhS) hyS) hhS), ?_⟩
    change (GG.map (p : R →+* R') ((GG.ofGL h)⁻¹ * y * GG.ofGL h)).mat = _
    rw [map_mul, map_mul, map_inv, hmapS, hy, conjBy_app, map_inv, inv_inv]
  have hΨ : IsLocallyConstant fun g => algebraMap O R ((F.Ψv F.vl g : Oˣ) : O) :=
    psi_lc (fun g => ((F.Ψv F.vl g : Oˣ) : O)) (fun n => (hF.Ψ_cont n).comp_continuous hlocc)
  have h2 : 0 < j → Subsingleton (H2 (gRep (F.ηv F.vl)
      ((Units.map (residue O).toMonoidHom).comp (F.Ψv F.vl)) j)) :=
    fun hj => hV.h2 F.vl hvT j (ne_of_gt hj)
  obtain ⟨φ, hφ, hd⟩ := hF.frob F.vl
  obtain ⟨r0', hpush, hlc0, hgr0, hup0, hI0⟩ := tri_lift 𝒜 p j hp hs (F.ηv F.vl) (F.Ψv F.vl) (F.Iv F.vl) φ hφ hd
    hηlc (hF.η_I F.vl hvT) hΨ h2 (conjBy h'⁻¹ r') hr'' (hlc'' hηlc hlc) hup hI hgr''
  have hr0r : ∀ g, (r0' g).right = F.ηv F.vl g := fun g =>
    (congrArg SemidirectProduct.right (DFunLike.congr_fun hpush g)).trans (hr''.mult g)
  have hr0lc : IsLocallyConstant r0' := lc_hom _ r0' hηlc hr0r hlc0
  have hback : conjBy h⁻¹ (conjBy h r0') = r0' := by
    ext g : 1
    rw [conjBy_app, conjBy_app, map_inv]
    group
  refine ⟨conjBy h r0', ?_, ?_, ?_, ?_⟩
  · ext g : 1
    change GG.map (p : R →+* R') ((conjBy h r0') g) = r' g
    rw [conjBy_app, map_mul, map_mul, map_inv, hmapS]
    have e := DFunLike.congr_fun hpush g
    change GG.map (p : R →+* R') (r0' g) = (conjBy h'⁻¹ r') g at e
    rw [e, conjBy_app, map_inv, inv_inv]
    group
  · unfold Frame.LocAt
    refine ⟨fun _ => ⟨h, hhin, ?_, ?_⟩, fun hSb => absurd hSb hF.vl_notMem, fun hT => absurd hvT hT⟩
    · rw [hback]
      intro g _ a b hab
      exact hup0 g a b hab
    · rw [hback]
      intro s hs _ a
      exact hI0 s hs a
  · have e : mats (conjBy h r0') = GG.mat ∘ (fun y => GG.ofGL h * y * (GG.ofGL h)⁻¹) ∘ r0' := by
      funext g
      show ((conjBy h r0') g).mat = (GG.ofGL h * r0' g * (GG.ofGL h)⁻¹).mat
      rw [conjBy_app]
    rw [e]
    exact (hr0lc.comp _).comp _
  · intro g
    rw [conjBy_app]
    exact (hS _).1 (S.mul_mem (S.mul_mem hhS ((hS _).2 (hgr0 g))) (S.inv_mem hhS))
