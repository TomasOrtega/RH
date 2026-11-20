import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormAlgebraMapLeOneBis
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral`. Consider the case `exact _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral`. Consider the case `(apply _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral ..)`.
-/
private theorem commHt_norm_le_one_of_isIntegral (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) :
    ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlgebraMapNormLeOne.norm_le_one_of_isIntegral ..)

/- English proof (translation)
The claim follows from `commHt_norm_le_one_of_isIntegral l x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)`.
-/
theorem commHt_norm_le_one_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) (x : Qbar l) (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  commHt_norm_le_one_of_isIntegral l x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `hx.2 s t` as an intermediate fact. Simplify `this` using `[Loc.colRep, Matrix.toLin'_apply]`.
-/
theorem commHt_cocycle_mulVec (V : R2 Ω l) {x : G ℚ Ω → Fin 2 → Qbar l} (hx : x ∈ Z1 (Loc.colRep V)) (s t : G ℚ Ω) :
    x (s * t) = x s + mat V s *ᵥ x t := by
  have := hx.2 s t
  simpa [Loc.colRep, Matrix.toLin'_apply] using this

/- English proof (translation)
Establish `hm` using `commHt_cocycle_mulVec V hx`. Establish `m1 : ∀ s, V s = 1 → mat V s = 1` using `fun s hs => by simp [mat, hs]`. Establish `h1 : x 1 = 0`. Use `hm 1 1` as an intermediate fact. Rewrite `this` using `[m1 1 (map_one V), Matrix.one_mulVec, mul_one]`.

Simplify using `using this`. Establish `hinv : ∀ s, V s = 1 → x s⁻¹ = - x s`. Introduce `s hs`. Use `hm s s⁻¹` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, h1, m1 s hs, Matrix.one_mulVec]`.

Conclude with `(neg_eq_of_add_eq_zero_right this.symm).symm`. Establish `hai : V a⁻¹ = 1` using `by rw [map_inv, ha, inv_one]`. Establish `hab : V (a * b) = 1` using `by rw [map_mul, ha, hb, one_mul]`. Establish `haba : V (a * b * a⁻¹) = 1` using `by rw [map_mul, hab, hai, one_mul]`. Rewrite using `[hm, m1 _ haba, Matrix.one_mulVec, hm, m1 _ hab, Matrix.one_mulVec, hm, m1 _ ha, Matrix.one_mulVec, hinv a ha, hinv b hb]`.

Normalize the expressions using the abelian group laws.
-/
theorem commHt_cocycle_commutator (V : R2 Ω l) {x : G ℚ Ω → Fin 2 → Qbar l} (hx : x ∈ Z1 (Loc.colRep V)) (a b : G ℚ Ω)
    (ha : V a = 1) (hb : V b = 1) : x (a * b * a⁻¹ * b⁻¹) = 0 := by
  have hm := commHt_cocycle_mulVec V hx
  have m1 : ∀ s, V s = 1 → mat V s = 1 := fun s hs => by simp [mat, hs]
  have h1 : x 1 = 0 := by
    have := hm 1 1
    rw [m1 1 (map_one V), Matrix.one_mulVec, mul_one] at this
    simpa using this
  have hinv : ∀ s, V s = 1 → x s⁻¹ = - x s := by
    intro s hs
    have := hm s s⁻¹
    rw [mul_inv_cancel, h1, m1 s hs, Matrix.one_mulVec] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm
  have hai : V a⁻¹ = 1 := by rw [map_inv, ha, inv_one]
  have hab : V (a * b) = 1 := by rw [map_mul, ha, hb, one_mul]
  have haba : V (a * b * a⁻¹) = 1 := by rw [map_mul, hab, hai, one_mul]
  rw [hm, m1 _ haba, Matrix.one_mulVec, hm, m1 _ hab, Matrix.one_mulVec, hm, m1 _ ha, Matrix.one_mulVec,
    hinv a ha, hinv b hb]
  abel

/- English proof (translation)
Take `⟨hc, hw⟩` from `Subgroup.mem_inf.1 hs`. Rewrite `hc`, `hw` using `[MonoidHom.mem_ker]`. Establish `hd : dt W s = 1` using `by simp [dt, hw]`. Simplify using `[dual1, tw, hw, hc, hd]`.
-/
theorem commHt_dual1_eq_one {W : R2 Ω l} {s : G ℚ Ω} (hs : s ∈ N0g W) : dual1 W s = 1 := by
  obtain ⟨hc, hw⟩ := Subgroup.mem_inf.1 hs
  rw [MonoidHom.mem_ker] at hc hw
  have hd : dt W s = 1 := by simp [dt, hw]
  simp [dual1, tw, hw, hc, hd]

/- English proof (translation)
Introduce `l _ Ω _ _ _ n c W y z u hO hy hz hu φ hφ g hg h hh`. Establish `hk : g * h * g⁻¹ * h⁻¹ ∈ N0g W` using `mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)`. Use `set k := g * h * g⁻¹ * h⁻¹ with hkdef`. Establish `kerW : ∀ s ∈ N0g W, W s = 1` using `fun s hs => (Subgroup.mem_inf.1 hs).2`. Establish `epsN : ∀ s ∈ N0g W, eps l s = 1` using `fun s hs => by`.

Use `(Subgroup.mem_inf.1 hs).1` as an intermediate fact. Rewrite `this` using `[MonoidHom.mem_ker]`. Simplify using `[eps, this]`. Establish `epsφ : eps l φ = 1`. Use `(Subgroup.mem_inf.1 hφ).1` as an intermediate fact.

Rewrite `this` using `[MonoidHom.mem_ker]`. Simplify using `[eps, this]`. Establish `matN : ∀ s ∈ N0g W, mat W s = 1` using `fun s hs => by simp [mat, kerW s hs]`. Establish `matD : ∀ s ∈ N0g W, mat (dual1 W) s = 1` using `fun s hs => by simp [mat, commHt_dual1_eq_one hs]`. Establish `hyk : y k = 0` using `commHt_cocycle_commutator W hy g h (kerW g hg) (kerW h hh)`.

Establish `hzk : z k = 0` using `commHt_cocycle_commutator (dual1 W) hz g h (commHt_dual1_eq_one hg) (commHt_dual1_eq_one hh)`. Establish `hmat : mat W (φ * k) = mat W φ` using `by simp [mat, map_mul, kerW k hk]`. Establish `hyφ : y (φ * k) = y φ` using `by rw [commHt_cocycle_mulVec W hy, hyk, Matrix.mulVec_zero, add_zero]`. Establish `hzφ : z (φ * k) = z φ` using `by rw [commHt_cocycle_mulVec (dual1 W) hz, hzk, Matrix.mulVec_zero, add_zero]`. Establish `hdiff : ht W y z u (φ * k) - ht W y z u φ = (mat W φ - 1).det * (u (φ * k) - u φ)`.

Simplify using `only [ht, hmat, hyφ, hzφ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hkhg : k * (h * g) = g * h` using `by simp only [hkdef]; group`. Use `set E : G ℚ Ω → G ℚ Ω → Qbar l := fun s t => cup W y z s t - (eps l s * u t - u (s * t) + u s) with hEdef`. Establish `hE : ∀ s t, ‖E s t‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖` using `fun s t => hu s t`.

Establish `c1 : cup W y z φ k = 0` using `by simp [cup, hzk, om]`. Establish `c2 : cup W y z k (h * g) = 0` using `by simp [cup, hyk, om]`. Establish `c3 : cup W y z g h = om (y g) (z h)` using `by simp [cup, matD g hg]`. Establish `c4 : cup W y z h g = om (y h) (z g)` using `by simp [cup, matD h hh]`. Establish `key : (u (φ * k) - u φ) - (om (y h) (z g) - om (y g) (z h)) = E φ k + E g h - E h g - E k (h * g)`.

Simplify using `only [hEdef, c1, c2, c3, c4, hkhg, epsφ, epsN k hk, epsN g hg, epsN h hh]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdet : ‖(mat W φ - 1).det‖ ≤ 1`. Apply `commHt_norm_le_one_of_mem c` to reduce the goal to its premises. Rewrite using `[Matrix.det_fin_two]`.

Establish `he : ∀ i j, (mat W φ - 1) i j ∈ c.O`. Introduce `i j`. Rewrite using `[Matrix.sub_apply, Matrix.one_apply]`. Use `split_ifs`. Conclude with `sub_mem (hO φ i j) (one_mem _)`.

Conclude with `sub_mem (hO φ i j) (zero_mem _)`. Conclude with `sub_mem (mul_mem (he 0 0) (he 1 1)) (mul_mem (he 0 1) (he 1 0))`. Establish `hsum : ‖E φ k + E g h - E h g - E k (h * g)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖`. Establish `hs : ∀ a b : Qbar l, ‖a‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ → ‖b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ → ‖a - b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖` using `fun a b ha hb => by`. Rewrite using `[sub_eq_add_neg]`.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))`. Conclude with `hs _ _ (hs _ _ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE _ _) (hE _ _))) (hE _ _)) (hE _ _)`. Unfold `Cg`. Rewrite using `[hdiff, ← mul_sub, norm_mul, key]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ht_commutator : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (c : Coef l) (W : R2 Ω l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ φ ∈ H0g W, ∀ g ∈ N0g W, ∀ h ∈ N0g W, Cg n (ht W y z u (φ * (g * h * g⁻¹ * h⁻¹)) - ht W y z u φ) ((mat W φ - 1).det * (om (y h) (z g) - om (y g) (z h))) := by
  intro l _ Ω _ _ _ n c W y z u hO hy hz hu φ hφ g hg h hh
  have hk : g * h * g⁻¹ * h⁻¹ ∈ N0g W :=
    mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  set k := g * h * g⁻¹ * h⁻¹ with hkdef
  have kerW : ∀ s ∈ N0g W, W s = 1 := fun s hs => (Subgroup.mem_inf.1 hs).2
  have epsN : ∀ s ∈ N0g W, eps l s = 1 := fun s hs => by
    have := (Subgroup.mem_inf.1 hs).1
    rw [MonoidHom.mem_ker] at this
    simp [eps, this]
  have epsφ : eps l φ = 1 := by
    have := (Subgroup.mem_inf.1 hφ).1
    rw [MonoidHom.mem_ker] at this
    simp [eps, this]
  have matN : ∀ s ∈ N0g W, mat W s = 1 := fun s hs => by simp [mat, kerW s hs]
  have matD : ∀ s ∈ N0g W, mat (dual1 W) s = 1 := fun s hs => by simp [mat, commHt_dual1_eq_one hs]
  have hyk : y k = 0 := commHt_cocycle_commutator W hy g h (kerW g hg) (kerW h hh)
  have hzk : z k = 0 := commHt_cocycle_commutator (dual1 W) hz g h (commHt_dual1_eq_one hg) (commHt_dual1_eq_one hh)
  have hmat : mat W (φ * k) = mat W φ := by simp [mat, map_mul, kerW k hk]
  have hyφ : y (φ * k) = y φ := by rw [commHt_cocycle_mulVec W hy, hyk, Matrix.mulVec_zero, add_zero]
  have hzφ : z (φ * k) = z φ := by rw [commHt_cocycle_mulVec (dual1 W) hz, hzk, Matrix.mulVec_zero, add_zero]
  have hdiff : ht W y z u (φ * k) - ht W y z u φ = (mat W φ - 1).det * (u (φ * k) - u φ) := by
    simp only [ht, hmat, hyφ, hzφ]; ring
  have hkhg : k * (h * g) = g * h := by simp only [hkdef]; group

  set E : G ℚ Ω → G ℚ Ω → Qbar l := fun s t => cup W y z s t - (eps l s * u t - u (s * t) + u s) with hEdef
  have hE : ∀ s t, ‖E s t‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun s t => hu s t
  have c1 : cup W y z φ k = 0 := by simp [cup, hzk, om]
  have c2 : cup W y z k (h * g) = 0 := by simp [cup, hyk, om]
  have c3 : cup W y z g h = om (y g) (z h) := by simp [cup, matD g hg]
  have c4 : cup W y z h g = om (y h) (z g) := by simp [cup, matD h hh]
  have key : (u (φ * k) - u φ) - (om (y h) (z g) - om (y g) (z h)) =
      E φ k + E g h - E h g - E k (h * g) := by
    simp only [hEdef, c1, c2, c3, c4, hkhg, epsφ, epsN k hk, epsN g hg, epsN h hh]
    ring
  have hdet : ‖(mat W φ - 1).det‖ ≤ 1 := by
    apply commHt_norm_le_one_of_mem c
    rw [Matrix.det_fin_two]
    have he : ∀ i j, (mat W φ - 1) i j ∈ c.O := by
      intro i j
      rw [Matrix.sub_apply, Matrix.one_apply]
      split_ifs
      · exact sub_mem (hO φ i j) (one_mem _)
      · exact sub_mem (hO φ i j) (zero_mem _)
    exact sub_mem (mul_mem (he 0 0) (he 1 1)) (mul_mem (he 0 1) (he 1 0))
  have hsum : ‖E φ k + E g h - E h g - E k (h * g)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    have hs : ∀ a b : Qbar l, ‖a‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ → ‖b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ →
        ‖a - b‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun a b ha hb => by
      rw [sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))
    exact hs _ _ (hs _ _ ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hE _ _) (hE _ _))) (hE _ _)) (hE _ _)
  unfold Cg
  rw [hdiff, ← mul_sub, norm_mul, key]
  calc ‖(mat W φ - 1).det‖ * ‖E φ k + E g h - E h g - E k (h * g)‖ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ n‖ :=
        mul_le_mul hdet hsum (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.Ord2

end
