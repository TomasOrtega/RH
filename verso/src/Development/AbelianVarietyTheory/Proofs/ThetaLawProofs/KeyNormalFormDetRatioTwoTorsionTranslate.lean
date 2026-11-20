import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.SameObj
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalAtScale
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DetNeZeroOfNormalAt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaNormalFormTranslateHalfPeriodStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq

noncomputable section
namespace GlobalTheory.KeyEq.TrVal

section Lie
variable {R : Type} [CommRing R] {G G' : Over (Sp R)} [GrpObj G] [GrpObj G']

/- English proof (translation)
Substitute `e` using the available equality. Take `⟨u, hu, rfl⟩` from `h`. Use `⟨fun i => u i ≫ f, fun i => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Over.comp_left, Over.comp_left, hu, Category.assoc]`. Both sides reduce to the same expression.

Conclude with `(map_list_prod (IsMonHom.monoidHom f (epsR R)) (List.ofFn u)).trans (by rw [List.map_ofFn]; rfl)`.
-/
theorem isLieComb_comp_cast (f : G ⟶ G') [IsMonHom f] {n m : ℕ} (e : m = n) {c : Fin n → R}
    {v : Fin n → (epsR R ⟶ G)} {w : epsR R ⟶ G} (h : IsLieComb c v w) :
    IsLieComb (fun i => c (Fin.cast e i)) (fun i => v (Fin.cast e i) ≫ f) (w ≫ f) := by
  subst e
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨fun i => u i ≫ f, fun i => ?_, ?_⟩
  · rw [Over.comp_left, Over.comp_left, hu, Category.assoc]
    rfl
  · exact (map_list_prod (IsMonHom.monoidHom f (epsR R)) (List.ofFn u)).trans (by rw [List.map_ofFn]; rfl)

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `h`.
-/
theorem isLieBasis_cast {n m : ℕ} (e : m = n) {v : Fin n → (epsR R ⟶ G)} (h : IsLieBasis v) :
    IsLieBasis (fun i => v (Fin.cast e i)) := by
  subst e
  exact h

end Lie

/- English proof (translation)
Take `⟨ex, tan, comp, sgl, bas⟩` from `GlobalTheory.LieComb.lieComb_algebra ℂ G n v hv.1`. Use `choose v₀ hv₀ using fun i => (ex (M⁻¹ i)).exists`. Establish `hb₀ : IsLieBasis v₀` using `(bas M⁻¹ v₀ hv hv₀).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit)`. Take `⟨ex₀, -, -, -, -⟩` from `GlobalTheory.LieComb.lieComb_algebra ℂ G n v₀ hb₀.1`. Use `⟨v₀, hb₀, hv₀, fun i => ?_⟩` and prove the remaining obligations.

Take `⟨w, hw⟩` from `(ex₀ (M i)).exists`. Establish `h1` using `comp _ (fun i => M⁻¹ i) v₀ (M i) w hv₀ hw`. Establish `e : ∑ j, M i j • M⁻¹ j = Pi.single i 1`. Rewrite using `[← Matrix.vecMul_eq_sum]`. Use `(congrFun (Matrix.mul_nonsing_inv M hM.isUnit) i).trans ?_` and prove the remaining obligations.

Simplify using `using smul_one_row (1 : ℂ) i`. Rewrite `h1` using `[e]`. Rewrite using `[(ex _).unique (sgl i) h1]` and apply the resulting hypothesis.
-/
theorem exists_basis_div {G : Over (Sp ℂ)} [GrpObj G] [IsCommMonObj G] {n : ℕ} {v : Fin n → (epsR ℂ ⟶ G)}
    (hv : IsLieBasis v) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) :
    ∃ v₀ : Fin n → (epsR ℂ ⟶ G), IsLieBasis v₀ ∧ (∀ i, IsLieComb (M⁻¹ i) v (v₀ i)) ∧
      ∀ i, IsLieComb (M i) v₀ (v i) := by
  obtain ⟨ex, tan, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ G n v hv.1
  choose v₀ hv₀ using fun i => (ex (M⁻¹ i)).exists
  have hb₀ : IsLieBasis v₀ := (bas M⁻¹ v₀ hv hv₀).2 (Matrix.isUnit_nonsing_inv_det M hM.isUnit)
  obtain ⟨ex₀, -, -, -, -⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ G n v₀ hb₀.1
  refine ⟨v₀, hb₀, hv₀, fun i => ?_⟩
  obtain ⟨w, hw⟩ := (ex₀ (M i)).exists
  have h1 := comp _ (fun i => M⁻¹ i) v₀ (M i) w hv₀ hw
  have e : ∑ j, M i j • M⁻¹ j = Pi.single i 1 := by
    rw [← Matrix.vecMul_eq_sum]
    refine (congrFun (Matrix.mul_nonsing_inv M hM.isUnit) i).trans ?_
    simpa using smul_one_row (1 : ℂ) i
  rw [e] at h1
  rwa [(ex _).unique (sgl i) h1]

/- English proof (translation)
Apply the tactic sequence `obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n <;> rcases ha with rfl | rfl`. Conclude with `⟨0, .inl rfl, -k, by push_cast; ring⟩`. Conclude with `⟨1 / 2, .inr rfl, -k, by push_cast; ring⟩`. Conclude with `⟨1 / 2, .inr rfl, -k, by push_cast; ring⟩`. Conclude with `⟨0, .inl rfl, -k - 1, by push_cast; ring⟩`.
-/
theorem exists_half (a : ℂ) (ha : a = 0 ∨ a = 1 / 2) (n : ℤ) :
    ∃ a' : ℂ, (a' = 0 ∨ a' = 1 / 2) ∧ ∃ k : ℤ, a' = a + n / 2 + k := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n <;> rcases ha with rfl | rfl
  · exact ⟨0, .inl rfl, -k, by push_cast; ring⟩
  · exact ⟨1 / 2, .inr rfl, -k, by push_cast; ring⟩
  · exact ⟨1 / 2, .inr rfl, -k, by push_cast; ring⟩
  · exact ⟨0, .inl rfl, -k - 1, by push_cast; ring⟩

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨u, h₁, h₂, h₃, h₄, h₅, fun i => by rw [smul_one_row]; exact h₆ i⟩`.
-/
theorem normalAt_of_param (y : KeyIn ℂ) {g : ℕ} (h : y.P.g = g) (u : HolUnif y.P.A y.P.L g)
    {τ : Matrix (Fin g) (Fin g) ℂ} {a b : Fin g → ℂ} {c : ℂ} (h₁ : τ.IsSymm) (h₂ : (τ.map Complex.im).PosDef)
    (h₃ : ∀ z, z ∈ u.Λ ↔ ∃ m n : Fin g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ)))
    (h₄ : u.IsRig y.rig) (h₅ : u.IsFn y.th (fun z => c * thetaChar τ a b z))
    (h₆ : ∀ i : Fin g, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (y.v (i.cast h.symm))) :
    NormalAt y (τ.submatrix (Fin.cast h) (Fin.cast h)) 1 (fun i => a (i.cast h)) (fun i => b (i.cast h)) c := by
  subst h
  exact ⟨u, h₁, h₂, h₃, h₄, h₅, fun i => by rw [smul_one_row]; exact h₆ i⟩

end TrVal
open TrVal

/- English proof (translation)
Introduce and unpack `hL hU x x' p ν t ⟨φ, hg, w, mu, rp, hp, hφ, hw, hmu, hrp, hvv, hth, r₁, r₂, r₃⟩ ⟨τ, M, a, b, c, hab, hc, hN, rfl⟩`. Establish `hM` using `det_ne_zero_of_normalAt hU x hN`. Use `haveI := x.P.isAb.comm`. Use `haveI := hφ`. Take `⟨v₀, hb₀, hv₀, hv₁⟩` from `exists_basis_div x.basis M hM`.

Take `⟨th₀, e₀, -, hle⟩` from `exists_sec_div x.P.A.hom (mul_inv_cancel₀ hc) x.th`. Take `⟨th₀', e₀', e₁', hle'⟩` from `exists_sec_div x'.P.A.hom (mul_inv_cancel₀ hc) x'.th`. Establish `hth₀ : ∀ s : Sp ℂ, ∃ y : x.P.A.left, x.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀` using `fun s => (x.th_ne s).imp fun y hy => ⟨hy.1, hle hy.2⟩`. Establish `hth₀' : ∀ s : Sp ℂ, ∃ y : x'.P.A.left, x'.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀'` using `fun s => (x'.th_ne s).imp fun y hy => ⟨hy.1, hle' hy.2⟩`. Establish `hb₀' : IsLieBasis fun i : Fin x'.P.g => v₀ (i.cast hg) ≫ φ.inv` using `Chart.isLieBasis_iso φ (by simpa using isLieBasis_cast hg hb₀)`.

Establish `hv₁' : ∀ i, IsLieComb (M.submatrix (Fin.cast hg) (Fin.cast hg) i) (fun i : Fin x'.P.g => v₀ (i.cast hg) ≫ φ.inv) (x'.v i)` using `fun i => by`. Use `isLieComb_comp_cast φ.inv hg (hv₁ (i.cast hg))` as an intermediate fact. Rewrite `this` using `[← hvv, Category.assoc, φ.hom_inv_id, Category.comp_id]`. Conclude with `this`. Establish `hN₀` using `(normalAt_scale x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis th₀ hth₀ v₀ hb₀ c⁻¹ M⁻¹ e₀ hv₀).2.2 τ M a b c hN`.

Rewrite `hN₀` using `[Matrix.nonsing_inv_mul M hM.isUnit, inv_mul_cancel₀ hc]`. Take `⟨u, hu⟩` from `(normalAt_one_iff _ _ _ _).1 hN₀`. Take `⟨z, rfl⟩` from `u.ex_onto p`. Take `⟨m, n, hz⟩` from `(hu.2.2.1 (z + z)).1 ((u.ker _).1 (by rw [u.ex_add, ← sq]; exact hp))`. Establish `hz' : z = frac τ 2 m n`.

Rewrite using `[frac, ← hz]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Substitute `hz'` using the available equality. Use `choose a' ha' ka using fun i => exists_half (a i) (hab.1 i) (n i)`. Use `choose b' hb' kb using fun i => exists_half (b i) (hab.2 i) (m i)`. Take `⟨h', u', -, c', -, -, hc', hΛ, q₄, q₅, q₆⟩` from `GlobalTheory.T.thetaNormalForm_translate_halfPeriod hL hU ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, v₀, hb₀⟩ ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th₀', hth₀', _, hb₀'⟩ x.P.g rfl u τ a b a' b' m n ν hab ⟨ha', hb'⟩ hu ka kb ⟨φ, hg, w, mu, rp, hp, hφ, hw, hmu, hrp, fun i => by sim …`. Establish `e` using `hth z j k hj hk`.

Express the relevant statement in the definitionally equal form `gs _ z _ (th₀.f j) = _ * gs _ z _ (th₀'.f k)`. Rewrite using `[e₀, e₀', gs_mul _ _ _ hj, gs_mul _ _ _ hk, gs_constFn _ _ _ _ hj, gs_constFn _ _ _ _ hk, e, Over.w, Category.id_comp, mul_left_comm], r₁, r₂, r₃⟩`. Establish `hN₁` using `normalAt_of_param ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th₀', hth₀', _, hb₀'⟩ hg u' hu.1 hu.2.1 (fun z => (hΛ z).trans (hu.2.2.1 z)) q₄ q₅ q₆`. Establish `hN₂` using `(normalAt_scale x'.P x'.g_pos x'.rig x'.rig_gen th₀' hth₀' _ hb₀' x'.th x'.th_ne x'.v x'.basis c _ e₁' hv₁').2.2 _ _ _ _ _ hN₁`. Establish `hc0 : c' ≠ 0`.

Introduce and unpack `rfl`. Simplify using `at hc'`. Use `⟨_, _, _, _, _, ⟨fun i => ha' _, fun i => hb' _⟩, mul_ne_zero hc hc0, hN₂, ?_⟩` and prove the remaining obligations. Establish `hd : (M.submatrix (Fin.cast hg) (Fin.cast hg)).det = M.det` using `Matrix.det_submatrix_equiv_self (finCongr hg) M`. Rewrite using `[Matrix.mul_one, hd, eq_inv_of_mul_eq_one_right hc', mul_pow, div_mul_eq_div_div, div_eq_mul_inv _ (c' ^ 8)]`.
-/
theorem val_of_isTrl : Out.Laws → ThetaUnifAV → ∀ (x x' : KeyIn ℂ) (p : 𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) (ν : ℂˣ) (t : ℂ), IsTrl x' x p ν → Val x t → Val x' (t * (ν : ℂ) ^ 2) := by
  rintro hL hU x x' p ν t ⟨φ, hg, w, mu, rp, hp, hφ, hw, hmu, hrp, hvv, hth, r₁, r₂, r₃⟩
    ⟨τ, M, a, b, c, hab, hc, hN, rfl⟩
  have hM := det_ne_zero_of_normalAt hU x hN
  haveI := x.P.isAb.comm
  haveI := hφ
  obtain ⟨v₀, hb₀, hv₀, hv₁⟩ := exists_basis_div x.basis M hM
  obtain ⟨th₀, e₀, -, hle⟩ := exists_sec_div x.P.A.hom (mul_inv_cancel₀ hc) x.th
  obtain ⟨th₀', e₀', e₁', hle'⟩ := exists_sec_div x'.P.A.hom (mul_inv_cancel₀ hc) x'.th
  have hth₀ : ∀ s : Sp ℂ, ∃ y : x.P.A.left, x.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀ :=
    fun s => (x.th_ne s).imp fun y hy => ⟨hy.1, hle hy.2⟩
  have hth₀' : ∀ s : Sp ℂ, ∃ y : x'.P.A.left, x'.P.A.hom y = s ∧ y ∈ Out.nonzeroLocus th₀' :=
    fun s => (x'.th_ne s).imp fun y hy => ⟨hy.1, hle' hy.2⟩
  have hb₀' : IsLieBasis fun i : Fin x'.P.g => v₀ (i.cast hg) ≫ φ.inv :=
    Chart.isLieBasis_iso φ (by simpa using isLieBasis_cast hg hb₀)
  have hv₁' : ∀ i, IsLieComb (M.submatrix (Fin.cast hg) (Fin.cast hg) i)
      (fun i : Fin x'.P.g => v₀ (i.cast hg) ≫ φ.inv) (x'.v i) := fun i => by
    have := isLieComb_comp_cast φ.inv hg (hv₁ (i.cast hg))
    rw [← hvv, Category.assoc, φ.hom_inv_id, Category.comp_id] at this
    exact this
  have hN₀ := (normalAt_scale x.P x.g_pos x.rig x.rig_gen x.th x.th_ne x.v x.basis th₀ hth₀ v₀ hb₀ c⁻¹ M⁻¹
    e₀ hv₀).2.2 τ M a b c hN
  rw [Matrix.nonsing_inv_mul M hM.isUnit, inv_mul_cancel₀ hc] at hN₀
  obtain ⟨u, hu⟩ := (normalAt_one_iff _ _ _ _).1 hN₀
  obtain ⟨z, rfl⟩ := u.ex_onto p
  obtain ⟨m, n, hz⟩ := (hu.2.2.1 (z + z)).1 ((u.ker _).1 (by rw [u.ex_add, ← sq]; exact hp))
  have hz' : z = frac τ 2 m n := by
    rw [frac, ← hz]
    funext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast
    ring
  subst hz'
  choose a' ha' ka using fun i => exists_half (a i) (hab.1 i) (n i)
  choose b' hb' kb using fun i => exists_half (b i) (hab.2 i) (m i)
  obtain ⟨h', u', -, c', -, -, hc', hΛ, q₄, q₅, q₆⟩ := GlobalTheory.T.thetaNormalForm_translate_halfPeriod hL hU
    ⟨x.P, x.g_pos, x.rig, x.rig_gen, th₀, hth₀, v₀, hb₀⟩
    ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th₀', hth₀', _, hb₀'⟩ x.P.g rfl u τ a b a' b' m n ν hab ⟨ha', hb'⟩ hu ka kb
    ⟨φ, hg, w, mu, rp, hp, hφ, hw, hmu, hrp, fun i => by simp, fun z j k hj hk => by
      have e := hth z j k hj hk
      change gs _ z _ (th₀.f j) = _ * gs _ z _ (th₀'.f k)
      rw [e₀, e₀', gs_mul _ _ _ hj, gs_mul _ _ _ hk, gs_constFn _ _ _ _ hj, gs_constFn _ _ _ _ hk, e,
        Over.w, Category.id_comp, mul_left_comm], r₁, r₂, r₃⟩
  have hN₁ := normalAt_of_param ⟨x'.P, x'.g_pos, x'.rig, x'.rig_gen, th₀', hth₀', _, hb₀'⟩ hg u' hu.1 hu.2.1
    (fun z => (hΛ z).trans (hu.2.2.1 z)) q₄ q₅ q₆
  have hN₂ := (normalAt_scale x'.P x'.g_pos x'.rig x'.rig_gen th₀' hth₀' _ hb₀' x'.th x'.th_ne x'.v x'.basis c _
    e₁' hv₁').2.2 _ _ _ _ _ hN₁
  have hc0 : c' ≠ 0 := by
    rintro rfl
    simp at hc'
  refine ⟨_, _, _, _, _, ⟨fun i => ha' _, fun i => hb' _⟩, mul_ne_zero hc hc0, hN₂, ?_⟩
  have hd : (M.submatrix (Fin.cast hg) (Fin.cast hg)).det = M.det := Matrix.det_submatrix_equiv_self (finCongr hg) M
  rw [Matrix.mul_one, hd, eq_inv_of_mul_eq_one_right hc', mul_pow, div_mul_eq_div_div, div_eq_mul_inv _ (c' ^ 8)]

end GlobalTheory.KeyEq
end
