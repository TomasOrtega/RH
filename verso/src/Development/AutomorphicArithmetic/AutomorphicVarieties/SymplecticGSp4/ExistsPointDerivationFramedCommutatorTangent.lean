import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsLocalFirstOrderLifts
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Dual

variable {O : Type} [CommRing O]

private def dm (X Z : M4 O) : M4 (DualNumber O) :=
  Matrix.of fun a b => TrivSqZeroExt.inl (X a b) + TrivSqZeroExt.inr (Z a b)

/- English proof (translation)
Simplify using `[dm]`.
-/
private theorem dm_fst (X Z : M4 O) (a b : Fin 4) : (dm X Z a b).fst = X a b := by simp [dm]

/- English proof (translation)
Simplify using `[dm]`.
-/
private theorem dm_snd (X Z : M4 O) (a b : Fin 4) : (dm X Z a b).snd = Z a b := by simp [dm]

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[(h a b).1, dm_fst]`. Rewrite using `[(h a b).2, dm_snd]`.
-/
private theorem dm_ext {M : M4 (DualNumber O)} {X Z : M4 O} (h : ∀ a b, (M a b).fst = X a b ∧ (M a b).snd = Z a b) :
    M = dm X Z := by
  ext a b
  · rw [(h a b).1, dm_fst]
  · rw [(h a b).2, dm_snd]

/- English proof (translation)
Apply `dm_ext` to reduce the goal to its premises. Introduce `a b`. Prove the components needed by the constructor for the conclusion. Simplify using `[Matrix.mul_apply, dm_fst, TrivSqZeroExt.fst_sum]`. Simplify using `[Matrix.mul_apply, dm_fst, dm_snd, TrivSqZeroExt.snd_sum, Matrix.add_apply, Finset.sum_add_distrib, mul_comm]`.
-/
private theorem dm_mul (X Z X' Z' : M4 O) : dm X Z * dm X' Z' = dm (X * X') (X * Z' + Z * X') := by
  apply dm_ext
  intro a b
  constructor
  · simp [Matrix.mul_apply, dm_fst, TrivSqZeroExt.fst_sum]
  · simp [Matrix.mul_apply, dm_fst, dm_snd, TrivSqZeroExt.snd_sum, Matrix.add_apply, Finset.sum_add_distrib, mul_comm]

/- English proof (translation)
Use `symm`. Apply `dm_ext` to reduce the goal to its premises. Introduce `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply, h]`.
-/
private theorem dm_one : dm (1 : M4 O) 0 = 1 := by
  symm
  apply dm_ext
  intro a b
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply, h]

/- English proof (translation)
Apply `dm_ext` to reduce the goal to its premises. Introduce `a b`. Simplify using `[adj_apply, dm_fst, dm_snd]`.
-/
private theorem dm_adj (X Z : M4 O) : adj (dm X Z) = dm (adj X) (adj Z) := by
  apply dm_ext
  intro a b
  simp [adj_apply, dm_fst, dm_snd]

/- English proof (translation)
Apply `dm_ext` to reduce the goal to its premises. Introduce `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[TrivSqZeroExt.algebraMap_eq_inl]`.

Simplify using `[Matrix.one_apply, h]`.
-/
private theorem dm_smul (a : O) : algebraMap O (DualNumber O) a • (1 : M4 (DualNumber O)) = dm (a • 1) 0 := by
  apply dm_ext
  intro i j
  by_cases h : i = j
  · subst h
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  · simp [Matrix.one_apply, h]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [sgn] <;> ring`.
-/
private theorem adj_mul_eq_adj_mul_adj (A B : M4 O) : adj (A * B) = adj B * adj A := by
  ext i j
  simp only [adj_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp [sgn] <;> ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[adj_apply, smul_sub]`.
-/
private theorem adj_sub_eq_adj_sub_adj (A B : M4 O) : adj (A - B) = adj A - adj B := by
  ext i j
  simp [adj_apply, smul_sub]

/- English proof (translation)
Unfold `IsGSp at hX ⊢`. Rewrite using `[dm_adj, dm_mul, dm_smul]`. Establish `hY' : adj Y = -Y` using `hY`. Establish `e1 : adj X * (X * Y) = ν • Y`. Rewrite using `[← Matrix.mul_assoc, hX, Matrix.smul_mul, Matrix.one_mul]`.

Establish `e2 : Y * (adj X * X) = ν • Y`. Rewrite using `[hX, Matrix.mul_smul, Matrix.mul_one]`. Establish `hZ : adj X * (Y * X - X * Y) + adj (Y * X - X * Y) * X = 0`. Rewrite using `[adj_sub_eq_adj_sub_adj, adj_mul_eq_adj_mul_adj, adj_mul_eq_adj_mul_adj, hY']`. Simplify using `only [mul_sub, sub_mul, mul_neg, neg_mul, Matrix.mul_assoc, e1, e2]`.

Normalize the expressions using the abelian group laws. Rewrite using `[hX, hZ]`.
-/
private theorem dm_gsp {ν : O} {X Y : M4 O} (hX : IsGSp ν X) (hY : Y ∈ sp4 O) :
    IsGSp (algebraMap O (DualNumber O) ν) (dm X (Y * X - X * Y)) := by
  unfold IsGSp at hX ⊢
  rw [dm_adj, dm_mul, dm_smul]
  have hY' : adj Y = -Y := hY
  have e1 : adj X * (X * Y) = ν • Y := by
    rw [← Matrix.mul_assoc, hX, Matrix.smul_mul, Matrix.one_mul]
  have e2 : Y * (adj X * X) = ν • Y := by
    rw [hX, Matrix.mul_smul, Matrix.mul_one]
  have hZ : adj X * (Y * X - X * Y) + adj (Y * X - X * Y) * X = 0 := by
    rw [adj_sub_eq_adj_sub_adj, adj_mul_eq_adj_mul_adj, adj_mul_eq_adj_mul_adj, hY']
    simp only [mul_sub, sub_mul, mul_neg, neg_mul, Matrix.mul_assoc, e1, e2]
    abel
  rw [hX, hZ]

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Matrix.one_apply] <;> decide`.
-/
private theorem adj_one_eq_one : adj (1 : M4 O) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Matrix.one_apply] <;> decide

/- English proof (translation)
Establish `hY' : adj Y = -Y` using `hY`. Unfold `IsGSp`. Rewrite using `[dm_adj, dm_mul, adj_one_eq_one, hY', one_smul, ← dm_one]`. Use `congr 1`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules.
-/
private theorem dm_sp {Y : M4 O} (hY : Y ∈ sp4 O) : IsGSp 1 (dm 1 Y) := by
  have hY' : adj Y = -Y := hY
  unfold IsGSp
  rw [dm_adj, dm_mul, adj_one_eq_one, hY', one_smul, ← dm_one]
  congr 1
  · simp
  · simp

variable [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

/- English proof (translation)
Simplify using `[res, RingEquiv.symm_apply_eq]`.
-/
private theorem res_self (x : O) : res O O x = residue O x := by
  simp [res, RingEquiv.symm_apply_eq]

/- English proof (translation)
Rewrite using `[← res_map (TrivSqZeroExt.fstHom O O O), res_self]`. Use `congr 1`. Conclude with `dm_fst X Z a b`.
-/
private theorem dm_res (X Z : M4 O) (a b : Fin 4) : res O (DualNumber O) (dm X Z a b) = residue O (X a b) := by
  rw [← res_map (TrivSqZeroExt.fstHom O O O), res_self]
  congr 1
  exact dm_fst X Z a b

/- English proof (translation)
Introduce `N`. Use `(hf N).mul (hg N) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
private theorem adicCont_mul {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f g : Γ → R)
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I (fun x => f x * g x) := by
  intro N
  convert (hf N).mul (hg N) using 1
  funext x
  simp

/- English proof (translation)
Introduce `N`. Use `(hf N).add (hg N) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.
-/
private theorem adicCont_add {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f g : Γ → R)
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I (fun x => f x + g x) := by
  intro N
  convert (hf N).add (hg N) using 1
  funext x
  simp

/- English proof (translation)
Introduce `N`. Conclude with `IsLocallyConstant.const _`.
-/
private theorem adicCont_const {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I (fun _ : Γ => c) := by
  intro N
  exact IsLocallyConstant.const _

/- English proof (translation)
Establish `h` using `adicCont_add I f (fun x => (-1) * g x) hf (adicCont_mul I _ g (adicCont_const I (-1)) hg)`. Simplify `h` using `[sub_eq_add_neg]`.
-/
private theorem adicCont_sub {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (f g : Γ → R)
    (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I (fun x => f x - g x) := by
  have h := adicCont_add I f (fun x => (-1) * g x) hf (adicCont_mul I _ g (adicCont_const I (-1)) hg)
  simpa [sub_eq_add_neg] using h

/- English proof (translation)
Set `m'` to `Lift.map (Algebra.ofId O (DualNumber O)) r`. Establish `hm : ∀ g i j, m'.hom g i j = TrivSqZeroExt.inl (r.hom g i j)`. Introduce `g i j`. Both sides reduce to the same expression. Use `⟨⟨⟨⟨fun g => dm (r.hom g) (Y * r.hom g - r.hom g * Y), ?_⟩, ?_⟩, ?_, ?_⟩, fun g => rfl⟩` and prove the remaining obligations.

Simplify using `only [map_one, Matrix.mul_one, Matrix.one_mul, sub_self]`. Conclude with `dm_one`. Introduce `g h`. Simplify using `only [map_mul]`. Rewrite using `[dm_mul]`.

Use `congr 1`. Simplify using `only [mul_sub, sub_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Introduce `a b`. Establish `key : (fun g => dm (r.hom g) (Y * r.hom g - r.hom g * Y) a b) = fun g => m'.hom g a b + TrivSqZeroExt.inr 1 * ∑ k, (TrivSqZeroExt.inl (Y a k) * m'.hom g k b - m'.hom g a k * TrivSqZeroExt.inl (Y k b))`.

Use function extensionality and compare the values at `g`. Simplify using `only [hm]`. Apply `TrivSqZeroExt.ext` to reduce the goal to its premises. Simplify using `[dm_fst]`. Simplify using `[dm_snd, Matrix.mul_apply, TrivSqZeroExt.fst_sum, Finset.sum_sub_distrib]`.

Use `show AdicCont (maximalIdeal (DualNumber O)) (fun g => dm (r.hom g) (Y * r.hom g - r.hom g * Y) a b)`. Rewrite using `[key]`. Use `adicCont_add _ _ _ (m'.cont a b) (adicCont_mul _ _ _ (adicCont_const _ _) ?_)` and prove the remaining obligations. Establish `hs` using `Finset.sum_induction (s := Finset.univ) (fun k : Fin 4 => fun g => TrivSqZeroExt.inl (Y a k) * m'.hom g k b - m'.hom g a k * TrivSqZeroExt.inl (Y k b)) (fun h => AdicCont (maximalIdeal (DualNumber O)) h) (fun f g hf hg => adicCont_add _ f g hf hg) (adicCont_const _ 0) (fun k _ => …`. Simplify `hs` using `[Finset.sum_fn]`.

Introduce `g a b`. Express the relevant statement in the definitionally equal form `res O (DualNumber O) (dm (r.hom g) (Y * r.hom g - r.hom g * Y) a b) = rbar g a b`. Rewrite using `[dm_res, ← res_self, r.red]`.
-/
private theorem dm_lift {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* M4 (ResidueField O)} (r : Lift O rbar O)
    (Y : M4 O) : ∃ r' : Lift O rbar (DualNumber O), ∀ g, r'.hom g = dm (r.hom g) (Y * r.hom g - r.hom g * Y) := by
  let m' := Lift.map (Algebra.ofId O (DualNumber O)) r
  have hm : ∀ g i j, m'.hom g i j = TrivSqZeroExt.inl (r.hom g i j) := by
    intro g i j
    rfl
  refine ⟨⟨⟨⟨fun g => dm (r.hom g) (Y * r.hom g - r.hom g * Y), ?_⟩, ?_⟩, ?_, ?_⟩, fun g => rfl⟩
  · simp only [map_one, Matrix.mul_one, Matrix.one_mul, sub_self]
    exact dm_one
  · intro g h
    simp only [map_mul]
    rw [dm_mul]
    congr 1
    simp only [mul_sub, sub_mul, Matrix.mul_assoc]
    abel
  · intro a b
    have key : (fun g => dm (r.hom g) (Y * r.hom g - r.hom g * Y) a b) = fun g =>
        m'.hom g a b + TrivSqZeroExt.inr 1 * ∑ k, (TrivSqZeroExt.inl (Y a k) * m'.hom g k b
          - m'.hom g a k * TrivSqZeroExt.inl (Y k b)) := by
      funext g
      simp only [hm]
      apply TrivSqZeroExt.ext
      · simp [dm_fst]
      · simp [dm_snd, Matrix.mul_apply, TrivSqZeroExt.fst_sum, Finset.sum_sub_distrib]
    show AdicCont (maximalIdeal (DualNumber O)) (fun g => dm (r.hom g) (Y * r.hom g - r.hom g * Y) a b)
    rw [key]
    refine adicCont_add _ _ _ (m'.cont a b) (adicCont_mul _ _ _ (adicCont_const _ _) ?_)
    have hs := Finset.sum_induction (s := Finset.univ) (fun k : Fin 4 => fun g => TrivSqZeroExt.inl (Y a k) * m'.hom g k b
          - m'.hom g a k * TrivSqZeroExt.inl (Y k b)) (fun h => AdicCont (maximalIdeal (DualNumber O)) h)
      (fun f g hf hg => adicCont_add _ f g hf hg) (adicCont_const _ 0)
      (fun k _ => adicCont_sub _ _ _ (adicCont_mul _ _ _ (adicCont_const _ _) (m'.cont k b))
        (adicCont_mul _ _ _ (m'.cont a k) (adicCont_const _ _)))
    simpa [Finset.sum_fn] using hs
  · intro g a b
    change res O (DualNumber O) (dm (r.hom g) (Y * r.hom g - r.hom g * Y) a b) = rbar g a b
    rw [dm_res, ← res_self, r.red]

end Dual

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `Ω _ _ _ l _ c D hD L F Y hY A hA hAl`. Set `r₀` to `Lift.map (F.W.origin F.org) F.r`. Establish `hr₀ : ∀ g, r₀.hom g = D.r0 g` using `fun g => Matrix.ext fun a b => F.at0r g a b`. Take `⟨ρl, hρeq, hρ⟩` from `UpperTheory.exists_local_first_order_lifts D hD (fun v => Y - A v) (fun v => sub_mem hY (hA v))`. Take `⟨i', hi', -⟩` from `L.univ (DualNumber c.O) ρl hρeq`.

Establish `hiρ : ∀ v g a b, i' ((L.ρ v).hom g a b) = (ρl v).hom g a b`. Introduce `v g a b`. Rewrite using `[← hi' v]`. Both sides reduce to the same expression. Take `⟨r', hr'⟩` from `dm_lift r₀ Y`.

Set `α' : D.T → M4 (DualNumber c.O)` to `fun v => dm 1 (A v)`. Establish `hfr : IsFr L i' r' α'`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Rewrite using `[hr' g]`.

Establish `hX` using `Ex.mult_map D (F.W.origin F.org) F.r F.fr.mult g`. Establish `h2` using `dm_gsp hX hY`. Rewrite `h2` using `[Algebra.algebraMap_self, RingHom.id_apply]`. Then use the resulting hypothesis. Introduce `Aa hAa g hg hbar`. Rewrite using `[hr' g, Ex.unr_map D (F.W.origin F.org) F.r F.fr.unr Aa hAa g hg hbar]`.

Simplify using `only [Matrix.mul_one, Matrix.one_mul, sub_self]`. Conclude with `dm_one`. Introduce `v`. Use `⟨dm_sp (hA v), ?_⟩` and prove the remaining obligations. Use extensionality with `a b`.

Rewrite using `[Matrix.map_apply, dm_res]`. Apply the tactic sequence `by_cases h : a = b <;> simp [Matrix.one_apply, h]`. Use `show dm 1 (A _) = 1`. Rewrite using `[hAl]`. Conclude with `dm_one`.

Introduce `v g`. Establish `hloc : ((L.ρ v).hom g).map i' = dm (D.r0 ↑g) ((Y - A v) * D.r0 ↑g - D.r0 ↑g * (Y - A v))`. Apply `dm_ext` to reduce the goal to its premises. Introduce `a b`. Rewrite using `[Matrix.map_apply, hiρ]`.

Conclude with `hρ v g a b`. Rewrite using `[hloc, hr' ↑g, hr₀]`. Use `show dm _ _ * dm 1 (A v) = dm 1 (A v) * dm _ _`. Rewrite using `[dm_mul, dm_mul]`. Use `congr 1`.

Simplify using the standard rewrite rules. Simplify using `only [mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws. Take `⟨y, ⟨hyi, hyr, hyα⟩, -⟩` from `F.univ (DualNumber c.O) i' r' α' hfr`. Establish `hyR : ∀ g a b, y (F.r.hom g a b) = r'.hom g a b`.

Introduce `g a b`. Rewrite using `[← hyr]`. Both sides reduce to the same expression. Establish `hyA : ∀ v a b, y (F.α v a b) = α' v a b`. Introduce `v a b`.

Rewrite using `[← hyα v]`. Both sides reduce to the same expression. Establish `hy0 : ∀ f, (y f).fst = F.W.origin F.org f`. Set `y0` to `(TrivSqZeroExt.fstHom c.O c.O c.O).comp y`. Establish `hfr0 : IsFr L (L.W.origin L.org) r₀ (fun _ => 1)`.

Use `⟨Ex.mult_map D _ F.r F.fr.mult, Ex.unr_map D _ F.r F.fr.unr, ?_, rfl, ?_⟩` and prove the remaining obligations. Introduce `v`. Use `⟨?_, Matrix.map_one _ (map_zero _) (map_one _)⟩` and prove the remaining obligations. Unfold `IsGSp`. Rewrite using `[(grp _).2.2.2.2.1]`.

Simplify using the standard rewrite rules. Introduce `v g`. Rewrite using `[mul_one, one_mul, hr₀]`. Conclude with `Matrix.ext fun a b => (L.at0 v g a b).symm`. Take `⟨x0, -, huniq⟩` from `F.univ c.O (L.W.origin L.org) r₀ (fun _ => 1) hfr0`.

Establish `e1` using `huniq (F.W.origin F.org) ⟨F.at0i, rfl, F.at0α⟩`. Establish `hloc0 : (TrivSqZeroExt.fstHom c.O c.O c.O).comp i' = L.W.origin L.org`. Take `⟨x1, -, hu2⟩` from `L.univ c.O (fun v => Lift.map (L.W.origin L.org) (L.ρ v)) (L.eqs.map _)`. Use `(hu2 _ fun v => ?_).trans (hu2 _ fun v => rfl).symm` and prove the remaining obligations. Apply `Lift.ext` to reduce the goal to its premises.

Use `MonoidHom.ext fun g => Matrix.ext fun a b => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `TrivSqZeroExt.fst (i' ((L.ρ v).hom g a b)) = (L.W.origin L.org) ((L.ρ v).hom g a b)`. Rewrite using `[hiρ, (hρ v g a b).1, L.at0]`. Establish `e2` using `huniq y0 ⟨?_, ?_, ?_⟩`. Introduce `f`.

Conclude with `congrArg (fun φ => φ f) (e2.trans e1.symm)`. Rewrite using `[← hloc0, ← hyi]`. Both sides reduce to the same expression. Apply `Lift.ext` to reduce the goal to its premises. Use `MonoidHom.ext fun g => Matrix.ext fun a b => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `TrivSqZeroExt.fst (y (F.r.hom g a b)) = (F.W.origin F.org) (F.r.hom g a b)`. Rewrite using `[hyR, hr' g, dm_fst]`. Both sides reduce to the same expression. Introduce `v`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `TrivSqZeroExt.fst (y (F.α v a b)) = (1 : M4 c.O) a b`. Rewrite using `[hyA]`. Conclude with `dm_fst _ _ a b`. Take `⟨δ, hδ, hδeq⟩` from `(der_hom c.O F.U c.O c.O (F.W.origin F.org) (fun f => (y f).snd)).mpr ⟨y, fun f => ⟨hy0 f, rfl⟩⟩`. Use `⟨δ, hδ, ?_, ?_⟩` and prove the remaining obligations.

Introduce `g a b`. Rewrite using `[show δ (F.r.hom g a b) = (y (F.r.hom g a b)).snd from congrFun hδeq _]`. Rewrite using `[hyR, hr' g, dm_snd, hr₀]`. Introduce `v a b`. Rewrite using `[show δ (F.α v a b) = (y (F.α v a b)).snd from congrFun hδeq _]`.

Rewrite using `[hyA]`. Conclude with `dm_snd _ _ a b`.
-/
theorem UpperTheory.exists_pointDerivation_framed_commutator_tangent :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (L : LocBase D) (F : Fr D L), ∀ Y ∈ sp4 c.O, ∀ A : D.T → M4 c.O, (∀ v, A v ∈ sp4 c.O) → A ⟨l, D.residueChar_mem_levelPrimes⟩ = 0 → ∃ δ ∈ PtDer (F.W.origin F.org) c.O, (∀ g a b, δ (F.r.hom g a b) = (Y * D.r0 g - D.r0 g * Y) a b) ∧ ∀ v a b, δ (F.α v a b) = A v a b := by
  intro Ω _ _ _ l _ c D hD L F Y hY A hA hAl
  let r₀ := Lift.map (F.W.origin F.org) F.r
  have hr₀ : ∀ g, r₀.hom g = D.r0 g := fun g => Matrix.ext fun a b => F.at0r g a b
  obtain ⟨ρl, hρeq, hρ⟩ := UpperTheory.exists_local_first_order_lifts D hD (fun v => Y - A v) (fun v => sub_mem hY (hA v))
  obtain ⟨i', hi', -⟩ := L.univ (DualNumber c.O) ρl hρeq
  have hiρ : ∀ v g a b, i' ((L.ρ v).hom g a b) = (ρl v).hom g a b := by
    intro v g a b
    rw [← hi' v]
    rfl
  obtain ⟨r', hr'⟩ := dm_lift r₀ Y
  let α' : D.T → M4 (DualNumber c.O) := fun v => dm 1 (A v)
  have hfr : IsFr L i' r' α' := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro g
      rw [hr' g]
      have hX := Ex.mult_map D (F.W.origin F.org) F.r F.fr.mult g
      have h2 := dm_gsp hX hY
      rwa [Algebra.algebraMap_self, RingHom.id_apply] at h2
    · intro Aa hAa g hg hbar
      rw [hr' g, Ex.unr_map D (F.W.origin F.org) F.r F.fr.unr Aa hAa g hg hbar]
      simp only [Matrix.mul_one, Matrix.one_mul, sub_self]
      exact dm_one
    · intro v
      refine ⟨dm_sp (hA v), ?_⟩
      ext a b
      rw [Matrix.map_apply, dm_res]
      by_cases h : a = b <;> simp [Matrix.one_apply, h]
    · show dm 1 (A _) = 1
      rw [hAl]
      exact dm_one
    · intro v g
      have hloc : ((L.ρ v).hom g).map i' = dm (D.r0 ↑g) ((Y - A v) * D.r0 ↑g - D.r0 ↑g * (Y - A v)) := by
        apply dm_ext
        intro a b
        rw [Matrix.map_apply, hiρ]
        exact hρ v g a b
      rw [hloc, hr' ↑g, hr₀]
      show dm _ _ * dm 1 (A v) = dm 1 (A v) * dm _ _
      rw [dm_mul, dm_mul]
      congr 1
      · simp
      · simp only [mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
        abel
  obtain ⟨y, ⟨hyi, hyr, hyα⟩, -⟩ := F.univ (DualNumber c.O) i' r' α' hfr
  have hyR : ∀ g a b, y (F.r.hom g a b) = r'.hom g a b := by
    intro g a b
    rw [← hyr]
    rfl
  have hyA : ∀ v a b, y (F.α v a b) = α' v a b := by
    intro v a b
    rw [← hyα v]
    rfl
  have hy0 : ∀ f, (y f).fst = F.W.origin F.org f := by
    let y0 := (TrivSqZeroExt.fstHom c.O c.O c.O).comp y
    have hfr0 : IsFr L (L.W.origin L.org) r₀ (fun _ => 1) := by
      refine ⟨Ex.mult_map D _ F.r F.fr.mult, Ex.unr_map D _ F.r F.fr.unr, ?_, rfl, ?_⟩
      · intro v
        refine ⟨?_, Matrix.map_one _ (map_zero _) (map_one _)⟩
        unfold IsGSp
        rw [(grp _).2.2.2.2.1]
        simp
      · intro v g
        rw [mul_one, one_mul, hr₀]
        exact Matrix.ext fun a b => (L.at0 v g a b).symm
    obtain ⟨x0, -, huniq⟩ := F.univ c.O (L.W.origin L.org) r₀ (fun _ => 1) hfr0
    have e1 := huniq (F.W.origin F.org) ⟨F.at0i, rfl, F.at0α⟩
    have hloc0 : (TrivSqZeroExt.fstHom c.O c.O c.O).comp i' = L.W.origin L.org := by
      obtain ⟨x1, -, hu2⟩ := L.univ c.O (fun v => Lift.map (L.W.origin L.org) (L.ρ v)) (L.eqs.map _)
      refine (hu2 _ fun v => ?_).trans (hu2 _ fun v => rfl).symm
      apply Lift.ext
      refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
      change TrivSqZeroExt.fst (i' ((L.ρ v).hom g a b)) = (L.W.origin L.org) ((L.ρ v).hom g a b)
      rw [hiρ, (hρ v g a b).1, L.at0]
    have e2 := huniq y0 ⟨?_, ?_, ?_⟩
    · intro f
      exact congrArg (fun φ => φ f) (e2.trans e1.symm)
    · rw [← hloc0, ← hyi]
      rfl
    · apply Lift.ext
      refine MonoidHom.ext fun g => Matrix.ext fun a b => ?_
      change TrivSqZeroExt.fst (y (F.r.hom g a b)) = (F.W.origin F.org) (F.r.hom g a b)
      rw [hyR, hr' g, dm_fst]
      rfl
    · intro v
      refine Matrix.ext fun a b => ?_
      change TrivSqZeroExt.fst (y (F.α v a b)) = (1 : M4 c.O) a b
      rw [hyA]
      exact dm_fst _ _ a b
  obtain ⟨δ, hδ, hδeq⟩ := (der_hom c.O F.U c.O c.O (F.W.origin F.org) (fun f => (y f).snd)).mpr
    ⟨y, fun f => ⟨hy0 f, rfl⟩⟩
  refine ⟨δ, hδ, ?_, ?_⟩
  · intro g a b
    rw [show δ (F.r.hom g a b) = (y (F.r.hom g a b)).snd from congrFun hδeq _]
    rw [hyR, hr' g, dm_snd, hr₀]
  · intro v a b
    rw [show δ (F.α v a b) = (y (F.α v a b)).snd from congrFun hδeq _]
    rw [hyA]
    exact dm_snd _ _ a b
