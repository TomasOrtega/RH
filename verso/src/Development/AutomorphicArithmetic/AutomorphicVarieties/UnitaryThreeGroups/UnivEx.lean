import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.U3

section Emb

variable {m : ℕ} {A B : Type} [CommRing A] [CommRing B]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem emb_def (x : GG m A) : emb x =
    if x.right = 1 then fromBlocks x.mat 0 0 ((theta x.left : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)
    else fromBlocks 0 x.mat ((theta x.left : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) 0 := rfl

/- English proof (translation)
Establish `e : ((theta (GG.map f x).left : GL (Fin m) B) : Matrix (Fin m) (Fin m) B) = ((theta x.left : GL (Fin m) A) : Matrix (Fin m) (Fin m) A).map f` using `by show ((theta (GeneralLinearGroup.map f x.left) : GL (Fin m) B) : Matrix (Fin m) (Fin m) B) = _`. Rewrite using `[← map_theta]`. Both sides reduce to the same expression. Rewrite using `[emb_def, emb_def, e, GG.map_right, GG.map_mat]`. Apply the tactic sequence `split_ifs <;> simp [Matrix.fromBlocks_map]`.
-/
private theorem emb_map (f : A →+* B) (x : GG m A) : emb (GG.map f x) = (emb x).map f := by
  have e : ((theta (GG.map f x).left : GL (Fin m) B) : Matrix (Fin m) (Fin m) B) =
      ((theta x.left : GL (Fin m) A) : Matrix (Fin m) (Fin m) A).map f := by
    show ((theta (GeneralLinearGroup.map f x.left) : GL (Fin m) B) : Matrix (Fin m) (Fin m) B) = _
    rw [← map_theta]; rfl
  rw [emb_def, emb_def, e, GG.map_right, GG.map_mat]
  split_ifs <;> simp [Matrix.fromBlocks_map]

private def col (s : ℤˣ) (b : Fin m) : Fin m ⊕ Fin m := if s = 1 then .inl b else .inr b

/- English proof (translation)
Rewrite using `[emb_def]`. Unfold `col`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
private theorem emb_col (x : GG m A) (a b : Fin m) : emb x (.inl a) (col x.right b) = x.mat a b := by
  rw [emb_def]
  unfold col
  split_ifs <;> rfl

/- English proof (translation)
Establish `hm : x.mat = y.mat`. Use extensionality with `a b`. Rewrite using `[← emb_col, ← emb_col, e, h]`. Conclude with `SemidirectProduct.ext (Units.ext hm) h`.
-/
private theorem emb_inj {x y : GG m A} (h : x.right = y.right) (e : emb x = emb y) : x = y := by
  have hm : x.mat = y.mat := by
    ext a b
    rw [← emb_col, ← emb_col, e, h]
  exact SemidirectProduct.ext (Units.ext hm) h

private def eqs (s : ℤˣ) (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A :=
  if s = 1 then fromBlocks (X.toBlocks₁₁ * (Jmat A m * X.toBlocks₂₂ᵀ * Jmat A m) - 1) X.toBlocks₁₂ X.toBlocks₂₁ 0
  else fromBlocks (X.toBlocks₁₂ * (Jmat A m * X.toBlocks₂₁ᵀ * Jmat A m) - 1) X.toBlocks₁₁ X.toBlocks₂₂ 0

/- English proof (translation)
Establish `e11 : (X.map f).toBlocks₁₁ = X.toBlocks₁₁.map f` using `rfl`. Establish `e12 : (X.map f).toBlocks₁₂ = X.toBlocks₁₂.map f` using `rfl`. Establish `e21 : (X.map f).toBlocks₂₁ = X.toBlocks₂₁.map f` using `rfl`. Establish `e22 : (X.map f).toBlocks₂₂ = X.toBlocks₂₂.map f` using `rfl`. Unfold `eqs`.

Apply the tactic sequence `split_ifs <;> simp [e11, e12, e21, e22, Matrix.fromBlocks_map, Matrix.map_mul, Matrix.transpose_map, Jmat_map, Matrix.map_sub]`.
-/
private theorem eqs_map (f : A →+* B) (s : ℤˣ) (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A) :
    eqs s (X.map f) = (eqs s X).map f := by
  have e11 : (X.map f).toBlocks₁₁ = X.toBlocks₁₁.map f := rfl
  have e12 : (X.map f).toBlocks₁₂ = X.toBlocks₁₂.map f := rfl
  have e21 : (X.map f).toBlocks₂₁ = X.toBlocks₂₁.map f := rfl
  have e22 : (X.map f).toBlocks₂₂ = X.toBlocks₂₂.map f := rfl
  unfold eqs
  split_ifs <;> simp [e11, e12, e21, e22, Matrix.fromBlocks_map, Matrix.map_mul, Matrix.transpose_map, Jmat_map,
    Matrix.map_sub]

/- English proof (translation)
Establish `hv` using `theta_inv_val (theta a)`. Rewrite `hv` using `[theta_theta]`. Rewrite using `[← hv]`. Conclude with `a.mul_inv`.
-/
private theorem mul_theta (a : GL (Fin m) A) :
    (a : Matrix (Fin m) (Fin m) A) * (Jmat A m * ((theta a : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)ᵀ * Jmat A m) = 1 := by
  have hv := theta_inv_val (theta a)
  rw [theta_theta] at hv
  rw [← hv]
  exact a.mul_inv

/- English proof (translation)
Establish `h' : Jmat A m * Qᵀ * Jmat A m * P = 1` using `mul_eq_one_comm.mp h`. Set `a : GL (Fin m) A` to `⟨P, Jmat A m * Qᵀ * Jmat A m, h, h'⟩`. Use `⟨a, rfl, ?_⟩` and prove the remaining obligations. Use `show Jmat A m * (Jmat A m * Qᵀ * Jmat A m)ᵀ * Jmat A m = Q`. Rewrite using `[Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Jmat_transpose, ← Matrix.mul_assoc (Jmat A m) (Jmat A m), Jmat_mul_Jmat, Matrix.one_mul, Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.mul_one]`.
-/
private theorem ex_theta (P Q : Matrix (Fin m) (Fin m) A) (h : P * (Jmat A m * Qᵀ * Jmat A m) = 1) :
    ∃ a : GL (Fin m) A, (a : Matrix (Fin m) (Fin m) A) = P ∧ ((theta a : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) = Q := by
  have h' : Jmat A m * Qᵀ * Jmat A m * P = 1 := mul_eq_one_comm.mp h
  let a : GL (Fin m) A := ⟨P, Jmat A m * Qᵀ * Jmat A m, h, h'⟩
  refine ⟨a, rfl, ?_⟩
  show Jmat A m * (Jmat A m * Qᵀ * Jmat A m)ᵀ * Jmat A m = Q
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Jmat_transpose,
    ← Matrix.mul_assoc (Jmat A m) (Jmat A m), Jmat_mul_Jmat, Matrix.one_mul, Matrix.mul_assoc, Jmat_mul_Jmat,
    Matrix.mul_one]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Unfold `eqs at h`. Rewrite `h` using `[← Matrix.fromBlocks_zero]`. Use `split_ifs at h with hs`.

Take `⟨h1, h2, h3, -⟩` from `Matrix.fromBlocks_inj.1 h`. Take `⟨a, ha, hb⟩` from `ex_theta _ _ (sub_eq_zero.1 h1)`. Use `⟨⟨a, s⟩, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.fromBlocks_toBlocks X, h2, h3, ← ha, ← hb]`. Conclude with `if_pos hs`.

Take `⟨h1, h2, h3, -⟩` from `Matrix.fromBlocks_inj.1 h`. Take `⟨a, ha, hb⟩` from `ex_theta _ _ (sub_eq_zero.1 h1)`. Use `⟨⟨a, s⟩, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.fromBlocks_toBlocks X, h2, h3, ← ha, ← hb]`. Conclude with `if_neg hs`.

Introduce and unpack `⟨x, rfl, rfl⟩`. Rewrite using `[emb_def]`. Unfold `eqs`. Apply the tactic sequence `split_ifs <;> simp [GG.mat, mul_theta]`.
-/
private theorem eqs_iff (s : ℤˣ) (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A) :
    eqs s X = 0 ↔ ∃ x : GG m A, x.right = s ∧ emb x = X := by
  constructor
  · intro h
    unfold eqs at h
    rw [← Matrix.fromBlocks_zero] at h
    split_ifs at h with hs
    · obtain ⟨h1, h2, h3, -⟩ := Matrix.fromBlocks_inj.1 h
      obtain ⟨a, ha, hb⟩ := ex_theta _ _ (sub_eq_zero.1 h1)
      refine ⟨⟨a, s⟩, rfl, ?_⟩
      rw [← Matrix.fromBlocks_toBlocks X, h2, h3, ← ha, ← hb]
      exact if_pos hs
    · obtain ⟨h1, h2, h3, -⟩ := Matrix.fromBlocks_inj.1 h
      obtain ⟨a, ha, hb⟩ := ex_theta _ _ (sub_eq_zero.1 h1)
      refine ⟨⟨a, s⟩, rfl, ?_⟩
      rw [← Matrix.fromBlocks_toBlocks X, h2, h3, ← ha, ← hb]
      exact if_neg hs
  · rintro ⟨x, rfl, rfl⟩
    rw [emb_def]
    unfold eqs
    split_ifs <;> simp [GG.mat, mul_theta]

/- English proof (translation)
Use `(IsLocallyConstant.iff_eventually_eq _).mpr fun g => ?_` and prove the remaining obligations. Establish `hr` using `h1.eventually_eq g`. Establish `hm : ∀ᶠ g' in nhds g, ∀ a b, (x g').mat a b = (x g).mat a b`. Simplify using `only [Filter.eventually_all]`. Conclude with `fun a b => (h2 a b).eventually_eq g`.

Use `filter_upwards [hr, hm] with g' h1' h2'`. Conclude with `SemidirectProduct.ext (Units.ext (Matrix.ext h2')) h1'`.
-/
private theorem lc_gg {Γ : Type} [TopologicalSpace Γ] (x : Γ → GG m A) (h1 : IsLocallyConstant fun g => (x g).right)
    (h2 : ∀ a b, IsLocallyConstant fun g => (x g).mat a b) : IsLocallyConstant x := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g => ?_
  have hr := h1.eventually_eq g
  have hm : ∀ᶠ g' in nhds g, ∀ a b, (x g').mat a b = (x g).mat a b := by
    simp only [Filter.eventually_all]
    exact fun a b => (h2 a b).eventually_eq g
  filter_upwards [hr, hm] with g' h1' h2'
  exact SemidirectProduct.ext (Units.ext (Matrix.ext h2')) h1'

end Emb

section Desc

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}

omit [IsTopologicalGroup Γ] in
/- English proof (translation)
Apply `lc_gg` to reduce the goal to its premises. Establish `hfun : (fun g => (GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g)).right) = fun g => η g`. Use function extensionality and compare the values at `g`. Rewrite using `[GG.map_right]`. Conclude with `s.hasMult g`.

Rewrite using `[hfun]`. Conclude with `hη`. Introduce `a b`. Establish `hfun : (fun g => (GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g)).mat a b) = fun g => Ideal.Quotient.mk (maximalIdeal R ^ n) ((s.hom g).mat a b)`. Use function extensionality and compare the values at `g`.

Rewrite using `[GG.map_mat]`. Both sides reduce to the same expression. Rewrite using `[hfun]`. Conclude with `s.cont a b n`.
-/
private theorem lc_mod (hη : IsLocallyConstant η) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (s : GLift O η Ψ R) (n : ℕ) :
    IsLocallyConstant fun g => GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g) := by
  apply lc_gg
  · have hfun : (fun g => (GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g)).right) = fun g => η g := by
      funext g
      rw [GG.map_right]
      exact s.hasMult g
    rw [hfun]
    exact hη
  · intro a b
    have hfun : (fun g => (GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g)).mat a b) =
        fun g => Ideal.Quotient.mk (maximalIdeal R ^ n) ((s.hom g).mat a b) := by
      funext g
      rw [GG.map_mat]
      rfl
    rw [hfun]
    exact s.cont a b n

omit [IsTopologicalGroup Γ] in
/- English proof (translation)
Conclude with `(IsLocallyConstant.isClopen_fiber h 1).isClosed`.
-/
private theorem ker_closed {G : Type*} [Group G] (φ : Γ →* G) (h : IsLocallyConstant φ) :
    IsClosed (φ.ker : Set Γ) := by
  exact (IsLocallyConstant.isClopen_fiber h 1).isClosed

/- English proof (translation)
Conclude with `Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.mpr (hN g hg)) (ker_closed φ h)`.
-/
private theorem le_ker {G : Type*} [Group G] (φ : Γ →* G) (h : IsLocallyConstant φ) (N : Set Γ)
    (hN : ∀ g ∈ N, φ g = 1) : (Subgroup.normalClosure N).topologicalClosure ≤ φ.ker := by
  exact Subgroup.topologicalClosure_minimal _
    (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.mpr (hN g hg)) (ker_closed φ h)

/- English proof (translation)
Use `haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)`. Introduce `g hg`. Rewrite using `[MonoidHom.mem_ker]`. Establish `hn : ∀ n : ℕ, GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g) = 1`. Introduce `n`.

Establish `hk` using `le_ker ((GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n))).comp s.hom) (lc_mod hη s n) N (fun g' hg' => by simp [hN g' hg']) hg`. Conclude with `hk`. Establish `hsep : ∀ y : R, (∀ n : ℕ, y ∈ maximalIdeal R ^ n) → y = 0`. Introduce `y hy`. Establish `hH : IsHausdorff (maximalIdeal R) R` using `inferInstance`.

Apply `hH.haus y` to reduce the goal to its premises. Introduce `n`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`. Conclude with `hy n`. Use `SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => ?_)) ?_` and prove the remaining obligations.

Use `sub_eq_zero.mp (hsep _ fun n => ?_)` and prove the remaining obligations. Establish `e` using `congrArg (fun z : GG 3 (R ⧸ maximalIdeal R ^ n) => z.mat a b) ((hn n).trans (map_one (GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)))).symm)`. Simplify using `only [GG.map_mat, Matrix.map_apply] at e`. Conclude with `Ideal.Quotient.eq.mp e`. Establish `e` using `congrArg SemidirectProduct.right (hn 0)`.

Rewrite `e` using `[GG.map_right]`. Conclude with `e`.
-/
private theorem kills_closure (hη : IsLocallyConstant η) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (s : GLift O η Ψ R) (N : Set Γ) (hN : Kills N R s) :
    (Subgroup.normalClosure N).topologicalClosure ≤ s.hom.ker := by
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  intro g hg
  rw [MonoidHom.mem_ker]
  have hn : ∀ n : ℕ, GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g) = 1 := by
    intro n
    have hk := le_ker ((GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n))).comp s.hom) (lc_mod hη s n) N
      (fun g' hg' => by simp [hN g' hg']) hg
    exact hk
  have hsep : ∀ y : R, (∀ n : ℕ, y ∈ maximalIdeal R ^ n) → y = 0 := by
    intro y hy
    have hH : IsHausdorff (maximalIdeal R) R := inferInstance
    apply hH.haus y
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hy n
  refine SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => ?_)) ?_
  · refine sub_eq_zero.mp (hsep _ fun n => ?_)
    have e := congrArg (fun z : GG 3 (R ⧸ maximalIdeal R ^ n) => z.mat a b)
      ((hn n).trans (map_one (GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)))).symm)
    simp only [GG.map_mat, Matrix.map_apply] at e
    exact Ideal.Quotient.eq.mp e
  · have e := congrArg SemidirectProduct.right (hn 0)
    rw [GG.map_right] at e
    exact e

omit [IsTopologicalGroup Γ] in
/- English proof (translation)
Introduce `s` and use `(QuotientGroup.isQuotientMap_mk M).isOpen_preimage.1 (h s)`.
-/
private theorem lc_quot {X : Type} (M : Subgroup Γ) (f : Γ ⧸ M → X)
    (h : IsLocallyConstant fun g : Γ => f (QuotientGroup.mk g)) : IsLocallyConstant f := fun s =>
  (QuotientGroup.isQuotientMap_mk M).isOpen_preimage.1 (h s)

omit [IsTopologicalGroup Γ] in
/- English proof (translation)
Establish `hid : Lift.map (AlgHom.id O R) r = r` using `Lift.ext (MonoidHom.ext fun q => Matrix.ext fun i j => rfl)`. Establish `hP : ∀ g : Γ, eqs (η g) (r.hom (QuotientGroup.mk g)) = 0`. Establish `h0` using `(hr R).1 (AlgHom.id O R)`. Rewrite `h0` using `[hid]`. Conclude with `h0`.

Use `choose x hxr hxe using fun g => (eqs_iff (η g) _).mp (hP g)`. Set `hom : Γ →* GG 3 R` to `{ toFun := x map_one' := emb_inj ((hxr 1).trans (map_one η)) (by rw [hxe, QuotientGroup.mk_one, map_one, map_one]) map_mul' := fun g h => emb_inj (by rw [hxr, SemidirectProduct.mul_right, hxr, hxr, map_mul]) (by rw [hxe, map_mul emb, hxe, hxe, QuotientGroup.mk_mul, map_mul]) }`. Establish `hcont : ∀ a b, AdicCont (maximalIdeal R) fun g => (hom g).mat a b`. Introduce `a b n`. Establish `hfun : (fun g => Ideal.Quotient.mk (maximalIdeal R ^ n) ((hom g).mat a b)) = fun g => Ideal.Quotient.mk (maximalIdeal R ^ n) (r.hom (QuotientGroup.mk g) (Sum.inl a) (col (η g) b))`.

Use function extensionality and compare the values at `g`. Use `show Ideal.Quotient.mk (maximalIdeal R ^ n) ((x g).mat a b) = _`. Rewrite using `[← emb_col, hxe, hxr]`. Rewrite using `[hfun]`. Use `(IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_` and prove the remaining obligations.

Establish `hc` using `((r.cont (Sum.inl a) (col (η g0) b) n).comp_continuous (QuotientGroup.isQuotientMap_mk M).continuous).eventually_eq g0`. Use `filter_upwards [hη.eventually_eq g0, hc] with g h1 h2`. Rewrite using `[h1]`. Conclude with `h2`. Establish `hred : ∀ g, GG.map (res O R : R →+* ResidueField O) (hom g) = rbar O η Ψ g`.

Introduce `g`. Use `emb_inj ?_ ?_` and prove the remaining obligations. Use `show (GG.map (res O R : R →+* ResidueField O) (x g)).right = _`. Rewrite using `[GG.map_right, hxr]`. Both sides reduce to the same expression.

Use `show emb (GG.map (res O R : R →+* ResidueField O) (x g)) = _`. Rewrite using `[emb_map, hxe, ← hrb]`. Conclude with `Matrix.ext fun i j => r.red _ i j`. Set `s0 : GLift O η Ψ R` to `⟨hom, hcont, hred⟩`. Establish `hkill : ∀ g ∈ N, hom g = 1`.

Introduce `g hg`. Use `emb_inj ((hxr g).trans (hηN g hg)) ?_` and prove the remaining obligations. Use `show emb (x g) = emb 1`. Rewrite using `[hxe, (QuotientGroup.eq_one_iff g).mpr (hNM hg), map_one, map_one]`. Use `⟨Univ.mk R s0 ?_⟩` and prove the remaining obligations.

Introduce `R' _ _ _`. Use `⟨fun f => ?_, fun r' hr' => ?_⟩` and prove the remaining obligations. Introduce `g hg show GG.map (f : R →+* R') (hom g) = 1`. Rewrite using `[hkill g hg, map_one]`. Establish `hker : M ≤ r'.hom.ker` using `hM R' r' hr'`.

Set `φ : Γ ⧸ M →* GG 3 R'` to `QuotientGroup.lift M r'.hom hker`. Establish `Lcont : ∀ i j, AdicCont (maximalIdeal R') fun q => (emb.comp φ) q i j`. Introduce `i j n`. Apply `lc_quot` to reduce the goal to its premises. Establish `hfun : (fun g : Γ => Ideal.Quotient.mk (maximalIdeal R' ^ n) ((emb.comp φ) (QuotientGroup.mk g) i j)) = (fun y : GG 3 (R' ⧸ maximalIdeal R' ^ n) => emb y i j) ∘ (fun g => GG.map (Ideal.Quotient.mk (maximalIdeal R' ^ n)) (r'.hom g))`.

Use function extensionality and compare the values at `g`. Use `show _ = emb (GG.map (Ideal.Quotient.mk (maximalIdeal R' ^ n)) (r'.hom g)) i j`. Rewrite using `[emb_map]`. Both sides reduce to the same expression. Rewrite using `[hfun]`.

Conclude with `(lc_mod hη r' n).comp _`. Establish `Lred : ∀ q i j, res O R' ((emb.comp φ) q i j) = rb q i j`. Introduce `q`. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H g`.

Introduce `i j`. Rewrite using `[hrb]`. Use `show (res O R') (emb (r'.hom g) i j) = _`. Rewrite using `[← r'.red g, emb_map]`. Both sides reduce to the same expression.

Set `L : Lift O rb R'` to `⟨emb.comp φ, Lcont, Lred⟩`. Establish `hL : ∀ g : Γ, eqs (η g) (L.hom (QuotientGroup.mk g)) = 0` using `fun g => (eqs_iff _ _).mpr ⟨r'.hom g, r'.hasMult g, rfl⟩`. Take `⟨f, hf, huniq⟩` from `(hr R').2 L hL`. Establish `fwd : ∀ f : R →ₐ[O] R', Lift.map f r = L → GLift.map f s0 = r'`. Introduce `f hf`.

Use `GLift.ext (MonoidHom.ext fun g => emb_inj ?_ ?_)` and prove the remaining obligations. Use `show (GG.map (f : R →+* R') (x g)).right = _`. Rewrite using `[GG.map_right, hxr, r'.hasMult g]`. Use `show emb (GG.map (f : R →+* R') (x g)) = _`. Rewrite using `[emb_map, hxe]`.

Conclude with `congrArg (fun L' : Lift O rb R' => L'.hom (QuotientGroup.mk g)) hf`. Establish `bwd : ∀ f : R →ₐ[O] R', GLift.map f s0 = r' → Lift.map f r = L`. Introduce `f hf`. Use `Lift.ext (MonoidHom.ext fun q => ?_)` and prove the remaining obligations. Proceed by induction on `q using QuotientGroup.induction_on with`.

Consider the case `H g => show (r.hom (g : Γ ⧸ M)).map (f : R →+* R') = emb (r'.hom g)`. Rewrite using `[← hxe, ← emb_map, ← hf]`. Both sides reduce to the same expression. Conclude with `⟨f, fwd f hf, fun f' hf' => huniq f' (bwd f' hf')⟩`.
-/
private theorem transfer (hη : IsLocallyConstant η) (N : Set Γ) (M : Subgroup Γ) [M.Normal] (hNM : N ⊆ M)
    (hM : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (s : GLift O η Ψ R), Kills N R s → M ≤ s.hom.ker)
    (hηN : ∀ g ∈ N, η g = 1)
    (rb : Γ ⧸ M →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ResidueField O))
    (hrb : ∀ g : Γ, rb (QuotientGroup.mk g) = emb (rbar O η Ψ g))
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rb R)
    (hr : Represents (fun _ _ _ _ r => ∀ g : Γ, eqs (η g) (r.hom (QuotientGroup.mk g)) = 0) r) :
    Nonempty (Univ (Kills (O := O) (η := η) (Ψ := Ψ) N)) := by
  have hid : Lift.map (AlgHom.id O R) r = r := Lift.ext (MonoidHom.ext fun q => Matrix.ext fun i j => rfl)
  have hP : ∀ g : Γ, eqs (η g) (r.hom (QuotientGroup.mk g)) = 0 := by
    have h0 := (hr R).1 (AlgHom.id O R)
    rw [hid] at h0
    exact h0
  choose x hxr hxe using fun g => (eqs_iff (η g) _).mp (hP g)
  let hom : Γ →* GG 3 R :=
    { toFun := x
      map_one' := emb_inj ((hxr 1).trans (map_one η)) (by rw [hxe, QuotientGroup.mk_one, map_one, map_one])
      map_mul' := fun g h => emb_inj (by rw [hxr, SemidirectProduct.mul_right, hxr, hxr, map_mul])
        (by rw [hxe, map_mul emb, hxe, hxe, QuotientGroup.mk_mul, map_mul]) }
  have hcont : ∀ a b, AdicCont (maximalIdeal R) fun g => (hom g).mat a b := by
    intro a b n
    have hfun : (fun g => Ideal.Quotient.mk (maximalIdeal R ^ n) ((hom g).mat a b)) =
        fun g => Ideal.Quotient.mk (maximalIdeal R ^ n) (r.hom (QuotientGroup.mk g) (Sum.inl a) (col (η g) b)) := by
      funext g
      show Ideal.Quotient.mk (maximalIdeal R ^ n) ((x g).mat a b) = _
      rw [← emb_col, hxe, hxr]
    rw [hfun]
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
    have hc := ((r.cont (Sum.inl a) (col (η g0) b) n).comp_continuous
      (QuotientGroup.isQuotientMap_mk M).continuous).eventually_eq g0
    filter_upwards [hη.eventually_eq g0, hc] with g h1 h2
    rw [h1]
    exact h2
  have hred : ∀ g, GG.map (res O R : R →+* ResidueField O) (hom g) = rbar O η Ψ g := by
    intro g
    refine emb_inj ?_ ?_
    · show (GG.map (res O R : R →+* ResidueField O) (x g)).right = _
      rw [GG.map_right, hxr]
      rfl
    · show emb (GG.map (res O R : R →+* ResidueField O) (x g)) = _
      rw [emb_map, hxe, ← hrb]
      exact Matrix.ext fun i j => r.red _ i j
  let s0 : GLift O η Ψ R := ⟨hom, hcont, hred⟩
  have hkill : ∀ g ∈ N, hom g = 1 := by
    intro g hg
    refine emb_inj ((hxr g).trans (hηN g hg)) ?_
    show emb (x g) = emb 1
    rw [hxe, (QuotientGroup.eq_one_iff g).mpr (hNM hg), map_one, map_one]
  refine ⟨Univ.mk R s0 ?_⟩
  intro R' _ _ _
  refine ⟨fun f => ?_, fun r' hr' => ?_⟩
  · intro g hg
    show GG.map (f : R →+* R') (hom g) = 1
    rw [hkill g hg, map_one]
  · have hker : M ≤ r'.hom.ker := hM R' r' hr'
    let φ : Γ ⧸ M →* GG 3 R' := QuotientGroup.lift M r'.hom hker
    have Lcont : ∀ i j, AdicCont (maximalIdeal R') fun q => (emb.comp φ) q i j := by
      intro i j n
      apply lc_quot
      have hfun : (fun g : Γ => Ideal.Quotient.mk (maximalIdeal R' ^ n) ((emb.comp φ) (QuotientGroup.mk g) i j)) =
          (fun y : GG 3 (R' ⧸ maximalIdeal R' ^ n) => emb y i j) ∘
            (fun g => GG.map (Ideal.Quotient.mk (maximalIdeal R' ^ n)) (r'.hom g)) := by
        funext g
        show _ = emb (GG.map (Ideal.Quotient.mk (maximalIdeal R' ^ n)) (r'.hom g)) i j
        rw [emb_map]
        rfl
      rw [hfun]
      exact (lc_mod hη r' n).comp _
    have Lred : ∀ q i j, res O R' ((emb.comp φ) q i j) = rb q i j := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        intro i j
        rw [hrb]
        show (res O R') (emb (r'.hom g) i j) = _
        rw [← r'.red g, emb_map]
        rfl
    let L : Lift O rb R' := ⟨emb.comp φ, Lcont, Lred⟩
    have hL : ∀ g : Γ, eqs (η g) (L.hom (QuotientGroup.mk g)) = 0 :=
      fun g => (eqs_iff _ _).mpr ⟨r'.hom g, r'.hasMult g, rfl⟩
    obtain ⟨f, hf, huniq⟩ := (hr R').2 L hL
    have fwd : ∀ f : R →ₐ[O] R', Lift.map f r = L → GLift.map f s0 = r' := by
      intro f hf
      refine GLift.ext (MonoidHom.ext fun g => emb_inj ?_ ?_)
      · show (GG.map (f : R →+* R') (x g)).right = _
        rw [GG.map_right, hxr, r'.hasMult g]
      · show emb (GG.map (f : R →+* R') (x g)) = _
        rw [emb_map, hxe]
        exact congrArg (fun L' : Lift O rb R' => L'.hom (QuotientGroup.mk g)) hf
    have bwd : ∀ f : R →ₐ[O] R', GLift.map f s0 = r' → Lift.map f r = L := by
      intro f hf
      refine Lift.ext (MonoidHom.ext fun q => ?_)
      induction q using QuotientGroup.induction_on with
      | H g =>
        show (r.hom (g : Γ ⧸ M)).map (f : R →+* R') = emb (r'.hom g)
        rw [← hxe, ← emb_map, ← hf]
        rfl
    exact ⟨f, fwd f hf, fun f' hf' => huniq f' (bwd f' hf')⟩

end Desc

/- English proof (translation)
Use `haveI : IsClosed (N : Set G) := hN`. Rewrite using `[totallyDisconnectedSpace_iff_connectedComponent_one]`. Use `Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun q hq => ?_⟩` and prove the remaining obligations. Proceed by induction on `q using QuotientGroup.induction_on with`. Consider the case `H g`.

Assume the negation of the conclusion as `hne`. Establish `hgN : g ∉ N` using `fun h => hne ((QuotientGroup.eq_one_iff g).mpr h)`. Establish `key` using `ProfiniteGrp.closedSubgroup_eq_sInf_open (⟨N, hN⟩ : ClosedSubgroup G)`. Establish `hmem : g ∉ (⟨N, hN⟩ : ClosedSubgroup G).toSubgroup` using `hgN`. Rewrite `hmem` using `[key, Subgroup.mem_sInf]`.

Use `push_neg at hmem`. Take `⟨K, ⟨hKo, hNK⟩, hgK⟩` from `hmem`. Set `H : Subgroup (G ⧸ N)` to `K.map (QuotientGroup.mk' N)`. Establish `hHo : IsOpen (H : Set (G ⧸ N))`. Establish `hset : (H : Set (G ⧸ N)) = (QuotientGroup.mk : G → G ⧸ N) '' K`.

Simplify using `[H]`. Rewrite using `[hset]`. Conclude with `QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ hKo`. Establish `hHc : IsClopen (H : Set (G ⧸ N))` using `⟨H.isClosed_of_isOpen hHo, hHo⟩`. Establish `hgH` using `hHc.connectedComponent_subset H.one_mem hq`.

Take `⟨k, hk, hkg⟩` from `Subgroup.mem_map.mp hgH`. Apply `hgK` to reduce the goal to its premises. Establish `hkN : k⁻¹ * g ∈ N` using `QuotientGroup.eq.mp hkg`. Establish `hmul` using `K.mul_mem hk (hNK hkN)`. Simplify using `using hmul`.
-/
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  haveI : IsClosed (N : Set G) := hN
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun q hq => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    by_contra hne
    have hgN : g ∉ N := fun h => hne ((QuotientGroup.eq_one_iff g).mpr h)
    have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (⟨N, hN⟩ : ClosedSubgroup G)
    have hmem : g ∉ (⟨N, hN⟩ : ClosedSubgroup G).toSubgroup := hgN
    rw [key, Subgroup.mem_sInf] at hmem
    push_neg at hmem
    obtain ⟨K, ⟨hKo, hNK⟩, hgK⟩ := hmem
    let H : Subgroup (G ⧸ N) := K.map (QuotientGroup.mk' N)
    have hHo : IsOpen (H : Set (G ⧸ N)) := by
      have hset : (H : Set (G ⧸ N)) = (QuotientGroup.mk : G → G ⧸ N) '' K := by
        simp [H]
      rw [hset]
      exact QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ hKo
    have hHc : IsClopen (H : Set (G ⧸ N)) := ⟨H.isClosed_of_isOpen hHo, hHo⟩
    have hgH := hHc.connectedComponent_subset H.one_mem hq
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hgH
    apply hgK
    have hkN : k⁻¹ * g ∈ N := QuotientGroup.eq.mp hkg
    have hmul := K.mul_mem hk (hNK hkN)
    simpa using hmul

section Quot

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι]
  [DecidableEq ι] {rb : Γ →* Matrix ι ι (ResidueField O)}

/- English proof (translation)
Use `haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne`. Use `haveI hco : IsCO O (R ⧸ J) := co_quot O R (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)`. Establish `hcomp : ∀ {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R ⧸ J →ₐ[O] R'), Lift.map f (Lift.map (Ideal.Quotient.mkₐ O J) r) = Lift.map (f.comp (Ideal.Quotient.mkₐ O J)) r` using `fun f => Lift.ext (MonoidHom.ext fun q => Matrix.ext fun i j => rfl)`. Use `⟨R ⧸ J, inferInstance, inferInstance, hco, Lift.map (Ideal.Quotient.mkₐ O J) r, ?_⟩` and prove the remaining obligations. Introduce `R' _ _ _`.

Use `⟨fun f => ?_, fun r' hr' => ?_⟩` and prove the remaining obligations. Rewrite using `[hcomp, hJ]`. Introduce `x hx`. Rewrite using `[RingHom.mem_ker]`. Use `show f (Ideal.Quotient.mk J x) = 0`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]`. Take `⟨f, hf, huniq⟩` from `(hr R').2 r' trivial`. Establish `hJf : J ≤ RingHom.ker f` using `(hJ R' f).mp (by rw [hf]; exact hr')`. Set `F : R ⧸ J →ₐ[O] R'` to `Ideal.Quotient.liftₐ J f (fun a ha => hJf ha)`. Establish `e : F.comp (Ideal.Quotient.mkₐ O J) = f`.

Use extensionality with `a`. Both sides reduce to the same expression. Use `⟨F, ?_, fun g hg => ?_⟩` and prove the remaining obligations. Conclude with `(hcomp F).trans (by rw [e]; exact hf)`. Establish `hg' : g.comp (Ideal.Quotient.mkₐ O J) = f` using `huniq _ ((hcomp g).symm.trans hg)`.

Conclude with `Ideal.Quotient.algHom_ext O (hg'.trans e.symm)`.
-/
private theorem rep_quot {Q : Cond O rb} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rb R)
    (hr : Represents (fun _ _ _ _ _ => True) r) (J : Ideal R)
    (hJ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'),
      Q R' (r.map f) ↔ J ≤ RingHom.ker f) (hne : J ≠ ⊤) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (_ : IsCO O S) (s : Lift O rb S), Represents Q s := by
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI hco : IsCO O (R ⧸ J) :=
    co_quot O R (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hcomp : ∀ {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R ⧸ J →ₐ[O] R'),
      Lift.map f (Lift.map (Ideal.Quotient.mkₐ O J) r) = Lift.map (f.comp (Ideal.Quotient.mkₐ O J)) r :=
    fun f => Lift.ext (MonoidHom.ext fun q => Matrix.ext fun i j => rfl)
  refine ⟨R ⧸ J, inferInstance, inferInstance, hco, Lift.map (Ideal.Quotient.mkₐ O J) r, ?_⟩
  intro R' _ _ _
  refine ⟨fun f => ?_, fun r' hr' => ?_⟩
  · rw [hcomp, hJ]
    intro x hx
    rw [RingHom.mem_ker]
    show f (Ideal.Quotient.mk J x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · obtain ⟨f, hf, huniq⟩ := (hr R').2 r' trivial
    have hJf : J ≤ RingHom.ker f := (hJ R' f).mp (by rw [hf]; exact hr')
    let F : R ⧸ J →ₐ[O] R' := Ideal.Quotient.liftₐ J f (fun a ha => hJf ha)
    have e : F.comp (Ideal.Quotient.mkₐ O J) = f := by
      ext a
      rfl
    refine ⟨F, ?_, fun g hg => ?_⟩
    · exact (hcomp F).trans (by rw [e]; exact hf)
    · have hg' : g.comp (Ideal.Quotient.mkₐ O J) = f := huniq _ ((hcomp g).symm.trans hg)
      exact Ideal.Quotient.algHom_ext O (hg'.trans e.symm)

end Quot

end UpperTheory.V.U3

/- English proof (translation)
Introduce `O _ _ _ _ _ l _ _ Γ _ _ _ _ _ _ η Ψ hη hχ N hN M _ hMeq hΦ`. Establish `hMc : IsClosed (M : Set Γ)`. Rewrite using `[hMeq]`. Conclude with `Subgroup.isClosed_topologicalClosure _`. Use `haveI : IsClosed (M : Set Γ) := hMc`.

Use `haveI : TotallyDisconnectedSpace (Γ ⧸ M) := totDisc_quot M hMc`. Establish `hNM : N ⊆ M` using `fun g hg => by`. Rewrite using `[hMeq]`. Conclude with `Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hg)`. Establish `hrbar_lc : IsLocallyConstant (rbar O η Ψ)`.

Use `(IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_` and prove the remaining obligations. Use `filter_upwards [hχ.eventually_eq g0, hη.eventually_eq g0] with g h1 h2`. Use `show (⟨tor (ResidueField O) (barChar O Ψ g), η g⟩ : GG 3 (ResidueField O)) = ⟨tor (ResidueField O) (barChar O Ψ g0), η g0⟩`. Rewrite using `[h1, h2]`. Establish `hηN : ∀ g ∈ N, η g = 1` using `fun g hg => by`.

Establish `h0` using `congrArg SemidirectProduct.right (hN g hg)`. Conclude with `h0`. Establish `hkillM : M ≤ (rbar O η Ψ).ker`. Rewrite using `[hMeq]`. Conclude with `le_ker (rbar O η Ψ) hrbar_lc N hN`.

Set `rb : Γ ⧸ M →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ResidueField O)` to `emb.comp (QuotientGroup.lift M (rbar O η Ψ) hkillM)`. Establish `hrb : ∀ g : Γ, rb (QuotientGroup.mk g) = emb (rbar O η Ψ g)` using `fun g => rfl`. Establish `hrb_lc : IsLocallyConstant rb` using `lc_quot M rb (hrbar_lc.comp emb)`. Establish `hM' : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (s : GLift O η Ψ R), Kills N R s → M ≤ s.hom.ker`. Introduce `R _ _ _ s hs`.

Rewrite using `[hMeq]`. Conclude with `kills_closure hη s N hs`. Take `⟨R, _, _, _, r, hr⟩` from `univ_lift l O (Γ ⧸ M) (Fin 3 ⊕ Fin 3) rb hΦ hrb_lc`. Set `J : Ideal R` to `Ideal.span {y | ∃ (g : Γ) (i j : Fin 3 ⊕ Fin 3), y = eqs (η g) (r.hom (QuotientGroup.mk g)) i j}`. Establish `hJ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), (∀ g : Γ, eqs (η g) ((Lift.map f r).hom (QuotientGroup.mk g)) = 0) ↔ J ≤ RingHom.ker f`.

Introduce `R' _ _ _ f`. Establish `key : ∀ g : Γ, eqs (η g) ((Lift.map f r).hom (QuotientGroup.mk g)) = (eqs (η g) (r.hom (QuotientGroup.mk g))).map (f : R →+* R')` using `fun g => eqs_map (f : R →+* R') _ _`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `y ⟨g, i, j, rfl⟩`. Establish `he` using `congrFun (congrFun ((key g).symm.trans (h g)) i) j`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Conclude with `he`. Introduce `h g`.

Rewrite using `[key]`. Use extensionality with `i j`. Establish `hy : eqs (η g) (r.hom (QuotientGroup.mk g)) i j ∈ J` using `Ideal.subset_span ⟨g, i, j, rfl⟩`. Establish `he` using `h hy`. Rewrite `he` using `[RingHom.mem_ker]`.

Conclude with `he`. Establish `hJm : J ≤ maximalIdeal R`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `y ⟨g, i, j, rfl⟩`. Rewrite using `[SetLike.mem_coe, ← res_eq_zero_iff O R]`.

Establish `e1 : (r.hom (QuotientGroup.mk g)).map (res O R : R →+* ResidueField O) = emb (rbar O η Ψ g)` using `Matrix.ext fun a b => r.red _ a b`. Establish `e2 : eqs (η g) (emb (rbar O η Ψ g)) = 0` using `(eqs_iff _ _).mpr ⟨rbar O η Ψ g, rfl, rfl⟩`. Establish `e3 : (eqs (η g) (r.hom (QuotientGroup.mk g))).map (res O R : R →+* ResidueField O) = 0` using `(eqs_map (res O R : R →+* ResidueField O) (η g) (r.hom (QuotientGroup.mk g))).symm.trans (by rw [e1]; exact e2)`. Conclude with `congrFun (congrFun e3 i) j`. Establish `hne : J ≠ ⊤` using `ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJm`.

Take `⟨S, _, _, _, s, hs⟩` from `rep_quot (Q := fun _ _ _ _ r => ∀ g : Γ, eqs (η g) (r.hom (QuotientGroup.mk g)) = 0) r hr J hJ hne`. Conclude with `transfer hη N M hNM hM' hηN rb hrb s hs`.
-/
theorem UpperTheory.V.U3.exists_univ :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (l : ℕ) [Fact l.Prime] [CharP (ResidueField O) l]
      {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ]
      (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ), IsLocallyConstant η → IsLocallyConstant (barChar O Ψ) → ∀ N : Set Γ, (∀ g ∈ N, rbar O η Ψ g = 1) →
      ∀ (M : Subgroup Γ) [M.Normal], M = (Subgroup.normalClosure N).topologicalClosure →
      PhiCond (Γ ⧸ M) l → Nonempty (Univ (Kills (O := O) (η := η) (Ψ := Ψ) N)) := by
  intro O _ _ _ _ _ l _ _ Γ _ _ _ _ _ _ η Ψ hη hχ N hN M _ hMeq hΦ
  have hMc : IsClosed (M : Set Γ) := by
    rw [hMeq]
    exact Subgroup.isClosed_topologicalClosure _
  haveI : IsClosed (M : Set Γ) := hMc
  haveI : TotallyDisconnectedSpace (Γ ⧸ M) := totDisc_quot M hMc
  have hNM : N ⊆ M := fun g hg => by
    rw [hMeq]
    exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hg)
  have hrbar_lc : IsLocallyConstant (rbar O η Ψ) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
    filter_upwards [hχ.eventually_eq g0, hη.eventually_eq g0] with g h1 h2
    show (⟨tor (ResidueField O) (barChar O Ψ g), η g⟩ : GG 3 (ResidueField O)) =
      ⟨tor (ResidueField O) (barChar O Ψ g0), η g0⟩
    rw [h1, h2]
  have hηN : ∀ g ∈ N, η g = 1 := fun g hg => by
    have h0 := congrArg SemidirectProduct.right (hN g hg)
    exact h0
  have hkillM : M ≤ (rbar O η Ψ).ker := by
    rw [hMeq]
    exact le_ker (rbar O η Ψ) hrbar_lc N hN
  let rb : Γ ⧸ M →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ResidueField O) :=
    emb.comp (QuotientGroup.lift M (rbar O η Ψ) hkillM)
  have hrb : ∀ g : Γ, rb (QuotientGroup.mk g) = emb (rbar O η Ψ g) := fun g => rfl
  have hrb_lc : IsLocallyConstant rb := lc_quot M rb (hrbar_lc.comp emb)
  have hM' : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (s : GLift O η Ψ R),
      Kills N R s → M ≤ s.hom.ker := by
    intro R _ _ _ s hs
    rw [hMeq]
    exact kills_closure hη s N hs
  obtain ⟨R, _, _, _, r, hr⟩ := univ_lift l O (Γ ⧸ M) (Fin 3 ⊕ Fin 3) rb hΦ hrb_lc
  let J : Ideal R := Ideal.span {y | ∃ (g : Γ) (i j : Fin 3 ⊕ Fin 3), y = eqs (η g) (r.hom (QuotientGroup.mk g)) i j}
  have hJ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'),
      (∀ g : Γ, eqs (η g) ((Lift.map f r).hom (QuotientGroup.mk g)) = 0) ↔ J ≤ RingHom.ker f := by
    intro R' _ _ _ f
    have key : ∀ g : Γ, eqs (η g) ((Lift.map f r).hom (QuotientGroup.mk g)) =
        (eqs (η g) (r.hom (QuotientGroup.mk g))).map (f : R →+* R') := fun g => eqs_map (f : R →+* R') _ _
    constructor
    · intro h
      rw [Ideal.span_le]
      rintro y ⟨g, i, j, rfl⟩
      have he := congrFun (congrFun ((key g).symm.trans (h g)) i) j
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact he
    · intro h g
      rw [key]
      ext i j
      have hy : eqs (η g) (r.hom (QuotientGroup.mk g)) i j ∈ J := Ideal.subset_span ⟨g, i, j, rfl⟩
      have he := h hy
      rw [RingHom.mem_ker] at he
      exact he
  have hJm : J ≤ maximalIdeal R := by
    rw [Ideal.span_le]
    rintro y ⟨g, i, j, rfl⟩
    rw [SetLike.mem_coe, ← res_eq_zero_iff O R]
    have e1 : (r.hom (QuotientGroup.mk g)).map (res O R : R →+* ResidueField O) = emb (rbar O η Ψ g) :=
      Matrix.ext fun a b => r.red _ a b
    have e2 : eqs (η g) (emb (rbar O η Ψ g)) = 0 := (eqs_iff _ _).mpr ⟨rbar O η Ψ g, rfl, rfl⟩
    have e3 : (eqs (η g) (r.hom (QuotientGroup.mk g))).map (res O R : R →+* ResidueField O) = 0 :=
      (eqs_map (res O R : R →+* ResidueField O) (η g) (r.hom (QuotientGroup.mk g))).symm.trans (by rw [e1]; exact e2)
    exact congrFun (congrFun e3 i) j
  have hne : J ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJm
  obtain ⟨S, _, _, _, s, hs⟩ :=
    rep_quot (Q := fun _ _ _ _ r => ∀ g : Γ, eqs (η g) (r.hom (QuotientGroup.mk g)) = 0) r hr J hJ hne
  exact transfer hη N M hNM hM' hηN rb hrb s hs
