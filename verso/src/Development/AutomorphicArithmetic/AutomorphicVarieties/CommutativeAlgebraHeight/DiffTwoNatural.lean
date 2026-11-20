import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.UPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

noncomputable section

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Establish `hm : MvPolynomial.aeval (fun g => (X * C (MvPolynomial.X g) : (MvPolynomial G A)[X])) (MvPolynomial.monomial m c) = C (MvPolynomial.monomial m c) * X ^ m.degree`. Rewrite using `[MvPolynomial.aeval_monomial, Finsupp.prod]`. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`.

Rewrite using `[MvPolynomial.monomial_eq, Finsupp.prod, map_mul, map_prod, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]`. Simplify using `only [map_pow]`. Use `show _ = _ * (X : (MvPolynomial G A)[X]) ^ (∑ i ∈ m.support, m i)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hm, Polynomial.coeff_C_mul_X_pow]`.

Distinguish the cases in `hmd : m = d`. Substitute `hmd` using the available equality. Distinguish the cases in `hk : k = m.degree`. Rewrite using `[if_pos hk, if_pos hk.symm]`. Rewrite using `[if_neg hk, if_neg fun h => hk h.symm, MvPolynomial.coeff_zero]`.

Establish `hz : MvPolynomial.coeff d (MvPolynomial.monomial m c) = 0`. Rewrite using `[MvPolynomial.coeff_monomial, if_neg hmd]`. Apply the tactic sequence `split_ifs <;> simp only [hz, MvPolynomial.coeff_zero]`. Consider the case `add p q hp hq`. Rewrite using `[map_add, Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem scale_coeff {A G : Type} [CommRing A] (P : MvPolynomial G A) (k : ℕ) (d : G →₀ ℕ) :
    MvPolynomial.coeff d ((MvPolynomial.aeval
      (fun g => (X * C (MvPolynomial.X g) : (MvPolynomial G A)[X])) P).coeff k) =
      if d.degree = k then MvPolynomial.coeff d P else 0 := by
  induction P using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm : MvPolynomial.aeval (fun g => (X * C (MvPolynomial.X g) : (MvPolynomial G A)[X]))
        (MvPolynomial.monomial m c) = C (MvPolynomial.monomial m c) * X ^ m.degree := by
      rw [MvPolynomial.aeval_monomial, Finsupp.prod]
      simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      rw [MvPolynomial.monomial_eq, Finsupp.prod, map_mul, map_prod, Polynomial.algebraMap_apply,
        MvPolynomial.algebraMap_eq]
      simp only [map_pow]
      show _ = _ * (X : (MvPolynomial G A)[X]) ^ (∑ i ∈ m.support, m i)
      ring
    rw [hm, Polynomial.coeff_C_mul_X_pow]
    by_cases hmd : m = d
    · subst hmd
      by_cases hk : k = m.degree
      · rw [if_pos hk, if_pos hk.symm]
      · rw [if_neg hk, if_neg fun h => hk h.symm, MvPolynomial.coeff_zero]
    · classical
      have hz : MvPolynomial.coeff d (MvPolynomial.monomial m c) = 0 := by
        rw [MvPolynomial.coeff_monomial, if_neg hmd]
      split_ifs <;> simp only [hz, MvPolynomial.coeff_zero]
  | add p q hp hq =>
    rw [map_add, Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]
    split_ifs <;> simp

/- English proof (translation)
Introduce `d hd`. Establish `key : d.degree = n`. Establish `e` using `scale_coeff P d.degree d`. Rewrite `e` using `[h, mul_comm, Polynomial.coeff_C_mul_X_pow, if_pos (rfl : d.degree = d.degree)]`. Assume the negation of the conclusion as `hne`.

Rewrite `e` using `[if_neg hne, MvPolynomial.coeff_zero]`. Conclude with `hd e.symm`. Use `show (Finsupp.weight (fun _ => 1)) d = n`. Rewrite using `[← Finsupp.degree_eq_weight_one]`. Conclude with `key`.
-/
private theorem homog_of_scale {A G : Type} [CommRing A] (P : MvPolynomial G A) (n : ℕ)
    (h : MvPolynomial.aeval (fun g => (X * C (MvPolynomial.X g) : (MvPolynomial G A)[X])) P = X ^ n * C P) :
    P.IsHomogeneous n := by
  intro d hd
  have key : d.degree = n := by
    have e := scale_coeff P d.degree d
    rw [h, mul_comm, Polynomial.coeff_C_mul_X_pow, if_pos (rfl : d.degree = d.degree)] at e
    by_contra hne
    rw [if_neg hne, MvPolynomial.coeff_zero] at e
    exact hd e.symm
  show (Finsupp.weight (fun _ => 1)) d = n
  rw [← Finsupp.degree_eq_weight_one]
  exact key

variable {n : ℕ} {A A' G : Type} [CommRing A] [CommRing A'] [Group G] [Fintype G] [DecidableEq G]

private def PRep (D : GDet n A G) (P : MvPolynomial G A) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra A S] (y : MonoidAlgebra S G),
    D.D S y = MvPolynomial.aeval (fun g => y.coeff g) P

private def el {S : Type} [CommRing S] (c : G → S) : MonoidAlgebra S G := ∑ g, MonoidAlgebra.single g (c g)

/- English proof (translation)
Simplify using `[el, Finsupp.single_apply]`.
-/
private theorem el_coeff {S : Type} [CommRing S] (c : G → S) (g : G) : (el c).coeff g = c g := by
  simp [el, Finsupp.single_apply]

/- English proof (translation)
Rewrite using `[h]`. Simplify using `only [el_coeff]`.
-/
private theorem PRep.el {D : GDet n A G} {P : MvPolynomial G A} (h : PRep D P) {S : Type} [CommRing S] [Algebra A S]
    (c : G → S) : D.D S (el c) = MvPolynomial.aeval c P := by
  rw [h]
  simp only [el_coeff]

/- English proof (translation)
Use `⟨D.D (MvPolynomial G A) (el MvPolynomial.X), ?_⟩` and prove the remaining obligations. Introduce `S _ _ y`. Set `f : MvPolynomial G A →ₐ[A] S` to `MvPolynomial.aeval fun g => y.coeff g`. Establish `hy : MonoidAlgebra.mapRingHom G (f : MvPolynomial G A →+* S) (el MvPolynomial.X) = y`. Apply `MonoidAlgebra.ext` to reduce the goal to its premises.

Use extensionality with `g`. Rewrite using `[MonoidAlgebra.mapRingHom_apply, el_coeff]`. Simplify using `[f]`. Use `D.nat (MvPolynomial G A) S f (el MvPolynomial.X)` as an intermediate fact. Rewrite `this` using `[hy]`.

Rewrite using `[this]`.
-/
private theorem ex_rep (D : GDet n A G) : ∃ P, PRep D P := by
  refine ⟨D.D (MvPolynomial G A) (el MvPolynomial.X), ?_⟩
  intro S _ _ y
  let f : MvPolynomial G A →ₐ[A] S := MvPolynomial.aeval fun g => y.coeff g
  have hy : MonoidAlgebra.mapRingHom G (f : MvPolynomial G A →+* S) (el MvPolynomial.X) = y := by
    apply MonoidAlgebra.ext
    ext g
    rw [MonoidAlgebra.mapRingHom_apply, el_coeff]
    simp [f]
  have := D.nat (MvPolynomial G A) S f (el MvPolynomial.X)
  rw [hy] at this
  rw [this]

/- English proof (translation)
Establish `e1` using `h.el (S := MvPolynomial G A) MvPolynomial.X`. Establish `e2` using `h'.el (S := MvPolynomial G A) MvPolynomial.X`. Rewrite `e1`, `e2` using `[MvPolynomial.aeval_X_left_apply]`. Rewrite using `[← e1, ← e2]`.
-/
private theorem PRep.poly_eq {D : GDet n A G} {P Q : MvPolynomial G A} (h : PRep D P) (h' : PRep D Q) : P = Q := by
  have e1 := h.el (S := MvPolynomial G A) MvPolynomial.X
  have e2 := h'.el (S := MvPolynomial G A) MvPolynomial.X
  rw [MvPolynomial.aeval_X_left_apply] at e1 e2
  rw [← e1, ← e2]

omit [Fintype G] [DecidableEq G] in
/- English proof (translation)
Apply `GDet.ext` to reduce the goal to its premises. Introduce `B _ _ x`. Rewrite using `[h B x, h' B x]`.
-/
private theorem PRep.det_eq {D D' : GDet n A G} {P : MvPolynomial G A} (h : PRep D P) (h' : PRep D' P) : D = D' := by
  apply GDet.ext
  intro B _ _ x
  rw [h B x, h' B x]

omit [Fintype G] [DecidableEq G] in
/- English proof (translation)
Introduce `S _ _ y`. Use `letI : Algebra A S := ((algebraMap A' S).comp f).toAlgebra`. Use `show D.D S y = _`. Rewrite using `[h S y, MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]`. Both sides reduce to the same expression.
-/
private theorem PRep.map {D : GDet n A G} {P : MvPolynomial G A} (h : PRep D P) (f : A →+* A') :
    PRep (D.map f) (MvPolynomial.map f P) := by
  intro S _ _ y
  letI : Algebra A S := ((algebraMap A' S).comp f).toAlgebra
  show D.D S y = _
  rw [h S y, MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
  rfl

/- English proof (translation)
Apply `homog_of_scale P n` to reduce the goal to its premises. Establish `e : _root_.el (fun g => (X * C (MvPolynomial.X g) : (MvPolynomial G A)[X])) = (X : (MvPolynomial G A)[X]) • _root_.el (fun g => (C (MvPolynomial.X g) : (MvPolynomial G A)[X]))`. Simplify using `only [_root_.el, Finset.smul_sum, MonoidAlgebra.smul_single']`. Establish `h1` using `h.el (S := (MvPolynomial G A)[X]) (fun g => (X * C (MvPolynomial.X g) : (MvPolynomial G A)[X]))`. Rewrite `h1` using `[e, D.homog, h.el]`.

Rewrite using `[← h1]`. Use `congr 1`. Use `congrArg (fun φ => φ P) (MvPolynomial.comp_aeval (R := A) (MvPolynomial.X : G → MvPolynomial G A) (Polynomial.CAlgHom (R := A) (A := MvPolynomial G A)))` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, MvPolynomial.aeval_X_left_apply] at this`. Simplify using `using this.symm`.
-/
private theorem PRep.homog {D : GDet n A G} {P : MvPolynomial G A} (h : PRep D P) : P.IsHomogeneous n := by
  apply homog_of_scale P n
  have e : _root_.el (fun g => (X * C (MvPolynomial.X g) : (MvPolynomial G A)[X])) =
      (X : (MvPolynomial G A)[X]) • _root_.el (fun g => (C (MvPolynomial.X g) : (MvPolynomial G A)[X])) := by
    simp only [_root_.el, Finset.smul_sum, MonoidAlgebra.smul_single']
  have h1 := h.el (S := (MvPolynomial G A)[X]) (fun g => (X * C (MvPolynomial.X g) : (MvPolynomial G A)[X]))
  rw [e, D.homog, h.el] at h1
  rw [← h1]
  congr 1
  have := congrArg (fun φ => φ P)
    (MvPolynomial.comp_aeval (R := A) (MvPolynomial.X : G → MvPolynomial G A)
      (Polynomial.CAlgHom (R := A) (A := MvPolynomial G A)))
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X_left_apply] at this
  simpa using this.symm

private def d1 (P : MvPolynomial G A) : A := MvPolynomial.eval (Pi.single 1 1) P - 1

private def d2 (P : MvPolynomial G A) : MvPolynomial (G ⊕ G) A :=
  MvPolynomial.aeval (fun g : G => ∑ a : G, (MvPolynomial.X (Sum.inl a) * MvPolynomial.X (Sum.inr (a⁻¹ * g)) :
    MvPolynomial (G ⊕ G) A)) P - MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr P

omit [Fintype G] in
/- English proof (translation)
Unfold `d1`. Rewrite using `[map_sub, map_one, MvPolynomial.eval_map]`. Use `congr 1`. Rewrite using `[show MvPolynomial.eval (Pi.single (1 : G) (1 : A)) P = MvPolynomial.eval₂ (RingHom.id A) (Pi.single 1 1) P from rfl, MvPolynomial.eval₂_comp_left, RingHom.comp_id]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases hi : i = 1 <;> simp [hi]`.
-/
private theorem diffOne_natural (P : MvPolynomial G A) (f : A →+* A') : d1 (MvPolynomial.map f P) = f (d1 P) := by
  unfold d1
  rw [map_sub, map_one, MvPolynomial.eval_map]
  congr 1
  rw [show MvPolynomial.eval (Pi.single (1 : G) (1 : A)) P =
    MvPolynomial.eval₂ (RingHom.id A) (Pi.single 1 1) P from rfl, MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  congr 1
  funext i
  by_cases hi : i = 1 <;> simp [hi]

omit [DecidableEq G] in
/- English proof (translation)
Unfold `d2`. Rewrite using `[map_sub, map_mul, MvPolynomial.map_rename, MvPolynomial.map_rename]`. Use `congr 1`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]`. Use `congr 1`.

Conclude with `RingHom.ext fun a => by simp`. Use function extensionality and compare the values at `g`. Simplify using `[map_sum]`.
-/
private theorem diffTwo_natural (P : MvPolynomial G A) (f : A →+* A') :
    d2 (MvPolynomial.map f P) = MvPolynomial.map f (d2 P) := by
  unfold d2
  rw [map_sub, map_mul, MvPolynomial.map_rename, MvPolynomial.map_rename]
  congr 1
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_comp_left]
  congr 1
  · exact RingHom.ext fun a => by simp
  · funext g
    simp [map_sum]

/- English proof (translation)
Establish `h1 : _root_.el (Pi.single (1 : G) (1 : A)) = 1`. Rewrite using `[MonoidAlgebra.one_def]`. Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Use extensionality with `g`. Rewrite using `[el_coeff, MonoidAlgebra.coeff_single]`.

Apply the tactic sequence `by_cases hg : g = 1 <;> simp [hg]`. Use `h.el (S := A) (Pi.single 1 1)` as an intermediate fact. Rewrite `this` using `[h1, map_one]`. Unfold `_root_.d1`. Rewrite using `[sub_eq_zero]`.

Simplify `this.symm` using `[MvPolynomial.coe_aeval_eq_eval]`.
-/
private theorem PRep.d1 {D : GDet n A G} {P : MvPolynomial G A} (h : PRep D P) : d1 P = 0 := by
  have h1 : _root_.el (Pi.single (1 : G) (1 : A)) = 1 := by
    rw [MonoidAlgebra.one_def]
    apply MonoidAlgebra.ext
    ext g
    rw [el_coeff, MonoidAlgebra.coeff_single]
    by_cases hg : g = 1 <;> simp [hg]
  have := h.el (S := A) (Pi.single 1 1)
  rw [h1, map_one] at this
  unfold _root_.d1
  rw [sub_eq_zero]
  simpa [MvPolynomial.coe_aeval_eq_eval] using this.symm

/- English proof (translation)
Establish `hx` using `h.el (S := MvPolynomial (G ⊕ G) A) (fun a => MvPolynomial.X (Sum.inl a))`. Establish `hy` using `h.el (S := MvPolynomial (G ⊕ G) A) (fun a => MvPolynomial.X (Sum.inr a))`. Establish `hxy` using `h (MvPolynomial (G ⊕ G) A) (_root_.el (fun a : G => (MvPolynomial.X (Sum.inl a) : MvPolynomial (G ⊕ G) A)) * _root_.el (fun a : G => (MvPolynomial.X (Sum.inr a) : MvPolynomial (G ⊕ G) A)))`. Rewrite `hxy` using `[map_mul, hx, hy]`. Establish `hc : (fun g => (_root_.el (fun a : G => (MvPolynomial.X (Sum.inl a) : MvPolynomial (G ⊕ G) A)) * _root_.el (fun a : G => (MvPolynomial.X (Sum.inr a) : MvPolynomial (G ⊕ G) A))).coeff g) = fun g => ∑ a : G, (MvPolynomial.X (Sum.inl a) * MvPolynomial.X (Sum.inr (a⁻¹ * g)) : MvPolyn …`.

Use function extensionality and compare the values at `g`. Simplify using `only [_root_.el, Finset.sum_mul_sum, MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a _`. Rewrite using `[Finset.sum_eq_single (a⁻¹ * g)]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `hab`. Conclude with `hb (eq_inv_mul_of_mul_eq hab)`.

Introduce `hn`. Conclude with `absurd (Finset.mem_univ _) hn`. Rewrite `hxy` using `[hc]`. Establish `e1 : MvPolynomial.rename Sum.inl P = MvPolynomial.aeval (fun a => (MvPolynomial.X (Sum.inl a) : MvPolynomial (G ⊕ G) A)) P`. Rewrite using `[← MvPolynomial.aeval_X_left_apply (MvPolynomial.rename Sum.inl P), MvPolynomial.aeval_rename]`.

Both sides reduce to the same expression. Establish `e2 : MvPolynomial.rename Sum.inr P = MvPolynomial.aeval (fun a => (MvPolynomial.X (Sum.inr a) : MvPolynomial (G ⊕ G) A)) P`. Rewrite using `[← MvPolynomial.aeval_X_left_apply (MvPolynomial.rename Sum.inr P), MvPolynomial.aeval_rename]`. Both sides reduce to the same expression. Unfold `_root_.d2`.

Rewrite using `[sub_eq_zero, ← hxy, e1, e2]`.
-/
private theorem PRep.d2 {D : GDet n A G} {P : MvPolynomial G A} (h : PRep D P) : d2 P = 0 := by
  have hx := h.el (S := MvPolynomial (G ⊕ G) A) (fun a => MvPolynomial.X (Sum.inl a))
  have hy := h.el (S := MvPolynomial (G ⊕ G) A) (fun a => MvPolynomial.X (Sum.inr a))
  have hxy := h (MvPolynomial (G ⊕ G) A)
    (_root_.el (fun a : G => (MvPolynomial.X (Sum.inl a) : MvPolynomial (G ⊕ G) A)) *
      _root_.el (fun a : G => (MvPolynomial.X (Sum.inr a) : MvPolynomial (G ⊕ G) A)))
  rw [map_mul, hx, hy] at hxy
  have hc : (fun g => (_root_.el (fun a : G => (MvPolynomial.X (Sum.inl a) : MvPolynomial (G ⊕ G) A)) *
      _root_.el (fun a : G => (MvPolynomial.X (Sum.inr a) : MvPolynomial (G ⊕ G) A))).coeff g) =
      fun g => ∑ a : G, (MvPolynomial.X (Sum.inl a) * MvPolynomial.X (Sum.inr (a⁻¹ * g)) :
        MvPolynomial (G ⊕ G) A) := by
    funext g
    simp only [_root_.el, Finset.sum_mul_sum, MonoidAlgebra.single_mul_single, MonoidAlgebra.coeff_sum,
      MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single (a⁻¹ * g)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hab
      exact hb (eq_inv_mul_of_mul_eq hab)
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  rw [hc] at hxy
  have e1 : MvPolynomial.rename Sum.inl P =
      MvPolynomial.aeval (fun a => (MvPolynomial.X (Sum.inl a) : MvPolynomial (G ⊕ G) A)) P := by
    rw [← MvPolynomial.aeval_X_left_apply (MvPolynomial.rename Sum.inl P), MvPolynomial.aeval_rename]
    rfl
  have e2 : MvPolynomial.rename Sum.inr P =
      MvPolynomial.aeval (fun a => (MvPolynomial.X (Sum.inr a) : MvPolynomial (G ⊕ G) A)) P := by
    rw [← MvPolynomial.aeval_X_left_apply (MvPolynomial.rename Sum.inr P), MvPolynomial.aeval_rename]
    rfl
  unfold _root_.d2
  rw [sub_eq_zero, ← hxy, e1, e2]

private def Mn (G : Type) (n : ℕ) : Type := {d : G →₀ ℕ // d.degree = n}

private instance (G : Type) [Finite G] (n : ℕ) : Finite (Mn G n) :=
  ((Finsupp.finite_of_degree_le (σ := G) n).subset fun _ h => le_of_eq h).to_subtype

private def pol (a : Mn G n → A) : MvPolynomial G A :=
  letI := Fintype.ofFinite (Mn G n)
  ∑ s, MvPolynomial.monomial s.1 (a s)

omit [Group G] [DecidableEq G] in
/- English proof (translation)
Simplify using `only [pol]`. Conclude with `MvPolynomial.IsHomogeneous.sum _ _ _ fun s _ => MvPolynomial.isHomogeneous_monomial _ s.2`.
-/
private theorem pol_homog (a : Mn G n → A) : (pol a).IsHomogeneous n := by
  simp only [pol]
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun s _ => MvPolynomial.isHomogeneous_monomial _ s.2

omit [Group G] [DecidableEq G] in
/- English proof (translation)
Simplify using `[pol]`.
-/
private theorem pol_map (a : Mn G n → A) (f : A →+* A') : MvPolynomial.map f (pol a) = pol fun s => f (a s) := by
  simp [pol]

omit [Group G] in
/- English proof (translation)
Simplify using `only [pol]`. Rewrite using `[MvPolynomial.coeff_sum, Finset.sum_eq_single s]`. Simplify using the standard rewrite rules. Introduce `t _ hts`. Rewrite using `[MvPolynomial.coeff_monomial, if_neg]`.

Introduce `h`. Conclude with `hts (Subtype.ext h)`. Introduce `hs`. Simplify using `at hs`.
-/
private theorem pol_coeff (a : Mn G n → A) (s : Mn G n) : MvPolynomial.coeff s.1 (pol a) = a s := by
  simp only [pol]
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single s]
  · simp
  · intro t _ hts
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro h
    exact hts (Subtype.ext h)
  · intro hs
    simp at hs

omit [Group G] in
/- English proof (translation)
Use extensionality with `d`. Distinguish the cases in `hd : d.degree = n`. Conclude with `pol_coeff (fun s : Mn G n => MvPolynomial.coeff s.1 P) ⟨d, hd⟩`. Rewrite using `[(pol_homog (n := n) _).coeff_eq_zero hd, h.coeff_eq_zero hd]`.
-/
private theorem pol_eq {P : MvPolynomial G A} (h : P.IsHomogeneous n) :
    (pol fun s : Mn G n => MvPolynomial.coeff s.1 P) = P := by
  ext d
  by_cases hd : d.degree = n
  · exact pol_coeff (fun s : Mn G n => MvPolynomial.coeff s.1 P) ⟨d, hd⟩
  · rw [(pol_homog (n := n) _).coeff_eq_zero hd, h.coeff_eq_zero hd]

private def defI (P : MvPolynomial G A) : Ideal A :=
  Ideal.span (insert (d1 P) (Set.range fun d => MvPolynomial.coeff d (d2 P)))

/- English proof (translation)
Establish `key : (∀ x ∈ defI P, f x = 0) ↔ ∀ x ∈ insert (d1 P) (Set.range fun d => MvPolynomial.coeff d (d2 P)), f x = 0`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Conclude with `h x (Ideal.subset_span hx)`. Introduce `h x hx`.

Establish `hle : defI P ≤ RingHom.ker f` using `Ideal.span_le.2 fun y hy => RingHom.mem_ker.2 (h y hy)`. Conclude with `RingHom.mem_ker.1 (hle hx)`. Rewrite using `[key, Set.forall_mem_insert, Set.forall_mem_range, diffOne_natural, diffTwo_natural]`. Apply `and_congr Iff.rfl` to reduce the goal to its premises. Rewrite using `[MvPolynomial.ext_iff]`.

Simplify using `[MvPolynomial.coeff_map]`.
-/
private theorem defI_iff (P : MvPolynomial G A) (f : A →+* A') :
    (∀ x ∈ defI P, f x = 0) ↔ d1 (MvPolynomial.map f P) = 0 ∧ d2 (MvPolynomial.map f P) = 0 := by
  have key : (∀ x ∈ defI P, f x = 0) ↔
      ∀ x ∈ insert (d1 P) (Set.range fun d => MvPolynomial.coeff d (d2 P)), f x = 0 := by
    constructor
    · intro h x hx
      exact h x (Ideal.subset_span hx)
    · intro h x hx
      have hle : defI P ≤ RingHom.ker f :=
        Ideal.span_le.2 fun y hy => RingHom.mem_ker.2 (h y hy)
      exact RingHom.mem_ker.1 (hle hx)
  rw [key, Set.forall_mem_insert, Set.forall_mem_range, diffOne_natural, diffTwo_natural]
  apply and_congr Iff.rfl
  rw [MvPolynomial.ext_iff]
  simp [MvPolynomial.coeff_map]

/- English proof (translation)
Use `choose a0 ha0 using fun s => IsLocalRing.residue_surjective (abar s)`. Use `haveI : IsCO O (MvPowerSeries (Mn G n) O) := co_mvps O O (Mn G n)`. Set `a : Mn G n → MvPowerSeries (Mn G n) O` to `fun s => MvPowerSeries.C (a0 s) + MvPowerSeries.X s`. Establish `hres : ∀ s, res O (MvPowerSeries (Mn G n) O) (a s) = abar s`. Introduce `s`.

Establish `hX : res O (MvPowerSeries (Mn G n) O) (MvPowerSeries.X s) = 0`. Rewrite using `[res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]`. Simplify using the standard rewrite rules. Establish `hC : res O (MvPowerSeries (Mn G n) O) (MvPowerSeries.C (a0 s)) = abar s`. Rewrite using `[show (MvPowerSeries.C (a0 s) : MvPowerSeries (Mn G n) O) = algebraMap O _ (a0 s) from rfl, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha0]`.

Simplify using `only [a, map_add, hX, hC, add_zero]`. Establish `hmapres : MvPolynomial.map (res O (MvPowerSeries (Mn G n) O) : MvPowerSeries (Mn G n) O →+* ResidueField O) (pol a) = pol abar`. Rewrite using `[pol_map]`. Use `congr 1`. Use function extensionality and compare the values at `s`.

Conclude with `hres s`. Establish `hJ : defI (pol a) ≤ maximalIdeal (MvPowerSeries (Mn G n) O)`. Introduce `x hx`. Use `(defI_iff (pol a) (res O (MvPowerSeries (Mn G n) O) : MvPowerSeries (Mn G n) O →+* ResidueField O)).2 (by rw [hmapres]; exact ⟨h1, h2⟩)` as an intermediate fact. Conclude with `(res_eq_zero_iff O _ x).1 (this x hx)`.

Establish `hJt : defI (pol a) ≠ ⊤` using `fun h => (IsLocalRing.maximalIdeal.isMaximal (MvPowerSeries (Mn G n) O)).ne_top (top_le_iff.1 (h ▸ hJ))`. Use `haveI : Nontrivial (MvPowerSeries (Mn G n) O ⧸ defI (pol a)) := ⟨⟨0, 1, fun h => hJt ((Ideal.eq_top_iff_one _).2 ((Ideal.Quotient.eq_zero_iff_mem (a := (1 : MvPowerSeries (Mn G n) O))).1 (by rw [map_one]; exact h.symm)))⟩⟩`. Use `haveI : IsCO O (MvPowerSeries (Mn G n) O ⧸ defI (pol a)) := co_quot O _ _ (Ideal.Quotient.mkₐ O (defI (pol a))) (Ideal.Quotient.mkₐ_surjective O _)`. Establish `hq` using `(defI_iff (pol a) (Ideal.Quotient.mkₐ O (defI (pol a)) : MvPowerSeries (Mn G n) O →+* MvPowerSeries (Mn G n) O ⧸ defI (pol a))).1 (fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 hx)`. Rewrite `hq` using `[pol_map]`.

Use `⟨MvPowerSeries (Mn G n) O ⧸ defI (pol a), inferInstance, inferInstance, inferInstance, fun s => Ideal.Quotient.mkₐ O (defI (pol a)) (a s), fun s => ?_, hq.1, hq.2, ?_⟩` and prove the remaining obligations. Rewrite using `[res_map]`. Conclude with `hres s`. Introduce `R' _ _ _ a' ha' hd1 hd2`. Establish `hm : ∀ s, a' s - algebraMap O R' (a0 s) ∈ maximalIdeal R'`.

Introduce `s`. Rewrite using `[← res_eq_zero_iff O R', map_sub, ha' s, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha0 s, sub_self]`. Take `⟨F, ⟨hFC, hFX⟩, hFu⟩` from `co_ev O O R' (Mn G n) (Algebra.ofId O R') (fun s => a' s - algebraMap O R' (a0 s)) hm`. Establish `hFa : ∀ s, F (a s) = a' s`. Introduce `s`.

Simplify using `only [a, map_add, hFC, hFX, Algebra.ofId_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hFJ : ∀ x ∈ defI (pol a), F x = 0`. Use `(defI_iff (pol a) (F : MvPowerSeries (Mn G n) O →+* R')).2 ?_` and prove the remaining obligations. Rewrite using `[pol_map, show (fun s => (F : MvPowerSeries (Mn G n) O →+* R') (a s)) = a' from funext hFa]`.

Conclude with `⟨hd1, hd2⟩`. Use `⟨Ideal.Quotient.liftₐ (defI (pol a)) F hFJ, fun s => hFa s, ?_⟩` and prove the remaining obligations. Introduce `f hf`. Establish `hC : ∀ x, (f.comp (Ideal.Quotient.mkₐ O (defI (pol a)))) (MvPowerSeries.C x) = algebraMap O R' x` using `fun x => (f.comp (Ideal.Quotient.mkₐ O (defI (pol a)))).commutes x`. Establish `hfq : f.comp (Ideal.Quotient.mkₐ O (defI (pol a))) = F`.

Use `hFu _ ⟨fun x => ?_, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[hC, Algebra.ofId_apply]`. Establish `e : (MvPowerSeries.X s : MvPowerSeries (Mn G n) O) = a s - MvPowerSeries.C (a0 s)`. Simplify using `[a]`. Rewrite using `[e, map_sub, hC, AlgHom.comp_apply, hf s]`.

Apply `Ideal.Quotient.algHom_ext O` to reduce the goal to its premises. Rewrite using `[hfq]`. Both sides reduce to the same expression.
-/
private theorem points (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] (abar : Mn G n → ResidueField O) (h1 : d1 (pol abar) = 0)
    (h2 : d2 (pol abar) = 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (a : Mn G n → R),
      (∀ s, res O R (a s) = abar s) ∧ d1 (pol a) = 0 ∧ d2 (pol a) = 0 ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (a' : Mn G n → R'),
        (∀ s, res O R' (a' s) = abar s) → d1 (pol a') = 0 → d2 (pol a') = 0 →
        ∃! f : R →ₐ[O] R', ∀ s, f (a s) = a' s := by
  classical
  choose a0 ha0 using fun s => IsLocalRing.residue_surjective (abar s)
  haveI : IsCO O (MvPowerSeries (Mn G n) O) := co_mvps O O (Mn G n)
  let a : Mn G n → MvPowerSeries (Mn G n) O := fun s => MvPowerSeries.C (a0 s) + MvPowerSeries.X s
  have hres : ∀ s, res O (MvPowerSeries (Mn G n) O) (a s) = abar s := by
    intro s
    have hX : res O (MvPowerSeries (Mn G n) O) (MvPowerSeries.X s) = 0 := by
      rw [res_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
      simp
    have hC : res O (MvPowerSeries (Mn G n) O) (MvPowerSeries.C (a0 s)) = abar s := by
      rw [show (MvPowerSeries.C (a0 s) : MvPowerSeries (Mn G n) O) = algebraMap O _ (a0 s) from rfl,
        AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha0]
    simp only [a, map_add, hX, hC, add_zero]
  have hmapres : MvPolynomial.map (res O (MvPowerSeries (Mn G n) O) : MvPowerSeries (Mn G n) O →+* ResidueField O)
      (pol a) = pol abar := by
    rw [pol_map]
    congr 1
    funext s
    exact hres s
  have hJ : defI (pol a) ≤ maximalIdeal (MvPowerSeries (Mn G n) O) := by
    intro x hx
    have := (defI_iff (pol a) (res O (MvPowerSeries (Mn G n) O) :
      MvPowerSeries (Mn G n) O →+* ResidueField O)).2 (by rw [hmapres]; exact ⟨h1, h2⟩)
    exact (res_eq_zero_iff O _ x).1 (this x hx)
  have hJt : defI (pol a) ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal (MvPowerSeries (Mn G n) O)).ne_top (top_le_iff.1 (h ▸ hJ))
  haveI : Nontrivial (MvPowerSeries (Mn G n) O ⧸ defI (pol a)) :=
    ⟨⟨0, 1, fun h => hJt ((Ideal.eq_top_iff_one _).2
      ((Ideal.Quotient.eq_zero_iff_mem (a := (1 : MvPowerSeries (Mn G n) O))).1 (by rw [map_one]; exact h.symm)))⟩⟩
  haveI : IsCO O (MvPowerSeries (Mn G n) O ⧸ defI (pol a)) :=
    co_quot O _ _ (Ideal.Quotient.mkₐ O (defI (pol a))) (Ideal.Quotient.mkₐ_surjective O _)
  have hq := (defI_iff (pol a) (Ideal.Quotient.mkₐ O (defI (pol a)) :
      MvPowerSeries (Mn G n) O →+* MvPowerSeries (Mn G n) O ⧸ defI (pol a))).1
    (fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 hx)
  rw [pol_map] at hq
  refine ⟨MvPowerSeries (Mn G n) O ⧸ defI (pol a), inferInstance, inferInstance, inferInstance,
    fun s => Ideal.Quotient.mkₐ O (defI (pol a)) (a s), fun s => ?_, hq.1, hq.2, ?_⟩
  · rw [res_map]
    exact hres s
  intro R' _ _ _ a' ha' hd1 hd2
  have hm : ∀ s, a' s - algebraMap O R' (a0 s) ∈ maximalIdeal R' := by
    intro s
    rw [← res_eq_zero_iff O R', map_sub, ha' s, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq,
      ha0 s, sub_self]
  obtain ⟨F, ⟨hFC, hFX⟩, hFu⟩ :=
    co_ev O O R' (Mn G n) (Algebra.ofId O R') (fun s => a' s - algebraMap O R' (a0 s)) hm
  have hFa : ∀ s, F (a s) = a' s := by
    intro s
    simp only [a, map_add, hFC, hFX, Algebra.ofId_apply]
    ring
  have hFJ : ∀ x ∈ defI (pol a), F x = 0 := by
    refine (defI_iff (pol a) (F : MvPowerSeries (Mn G n) O →+* R')).2 ?_
    rw [pol_map, show (fun s => (F : MvPowerSeries (Mn G n) O →+* R') (a s)) = a' from funext hFa]
    exact ⟨hd1, hd2⟩
  refine ⟨Ideal.Quotient.liftₐ (defI (pol a)) F hFJ, fun s => hFa s, ?_⟩
  intro f hf
  have hC : ∀ x, (f.comp (Ideal.Quotient.mkₐ O (defI (pol a)))) (MvPowerSeries.C x) = algebraMap O R' x :=
    fun x => (f.comp (Ideal.Quotient.mkₐ O (defI (pol a)))).commutes x
  have hfq : f.comp (Ideal.Quotient.mkₐ O (defI (pol a))) = F := by
    refine hFu _ ⟨fun x => ?_, fun s => ?_⟩
    · rw [hC, Algebra.ofId_apply]
    · have e : (MvPowerSeries.X s : MvPowerSeries (Mn G n) O) = a s - MvPowerSeries.C (a0 s) := by
        simp [a]
      rw [e, map_sub, hC, AlgHom.comp_apply, hf s]
  apply Ideal.Quotient.algHom_ext O
  rw [hfq]
  rfl

end

/- English proof (translation)
Introduce `O _ _ _ _ _ n G _ _ _ _ Dbar`. Use `letI : Fintype G := Fintype.ofFinite G`. Take `⟨Pbar, hPbar⟩` from `ex_rep Dbar`. Establish `hhom` using `hPbar.homog`. Establish `hpolbar : (pol fun s : Mn G n => MvPolynomial.coeff s.1 Pbar) = Pbar` using `pol_eq hhom`.

Take `⟨R, _, _, _, a, ha, hd1, hd2, huniv⟩` from `points O (fun s : Mn G n => MvPolynomial.coeff s.1 Pbar) (by rw [hpolbar]; exact hPbar.d1) (by rw [hpolbar]; exact hPbar.d2)`. Take `⟨D, hD⟩` from `u_poly (pol a) (pol_homog a) (sub_eq_zero.1 hd1) (sub_eq_zero.1 hd2)`. Establish `hDrep : PRep D (pol a)` using `hD`. Establish `hmapD : ∀ {R' : Type} [CommRing R'] (f : R →+* R'), PRep (D.map f) (pol fun s => f (a s))`. Introduce `R' _ f`.

Rewrite using `[← pol_map]`. Conclude with `hDrep.map f`. Use `⟨R, inferInstance, inferInstance, inferInstance, D, ⟨⟨fun i N => IsLocallyConstant.of_discrete _, ?_⟩, ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `hmapD (res O R : R →+* ResidueField O)`. Rewrite `h1` using `[show (fun s => (res O R : R →+* ResidueField O) (a s)) = (fun s : Mn G n => MvPolynomial.coeff s.1 Pbar) from funext ha, hpolbar]`.

Conclude with `h1.det_eq hPbar`. Introduce `R' _ _ _ D' hD'`. Take `⟨P', hP'⟩` from `ex_rep D'`. Establish `hpol' : (pol fun s : Mn G n => MvPolynomial.coeff s.1 P') = P'` using `pol_eq hP'.homog`. Establish `hred : MvPolynomial.map (res O R' : R' →+* ResidueField O) P' = Pbar`.

Establish `h1` using `hP'.map (res O R' : R' →+* ResidueField O)`. Rewrite `h1` using `[hD'.red]`. Conclude with `h1.poly_eq hPbar`. Establish `ha' : ∀ s : Mn G n, res O R' (MvPolynomial.coeff s.1 P') = MvPolynomial.coeff s.1 Pbar`. Introduce `s`.

Rewrite using `[← hred, MvPolynomial.coeff_map]`. Both sides reduce to the same expression. Take `⟨f, hf, hfu⟩` from `huniv R' (fun s => MvPolynomial.coeff s.1 P') ha' (by rw [hpol']; exact hP'.d1) (by rw [hpol']; exact hP'.d2)`. Establish `key : ∀ g : R →ₐ[O] R', D.map (g : R →+* R') = D' ↔ ∀ s, g (a s) = MvPolynomial.coeff s.1 P'`. Introduce `g`.

Prove the components needed by the constructor for the conclusion. Introduce `h s`. Establish `h1` using `hmapD (g : R →+* R')`. Rewrite `h1` using `[h]`. Establish `e` using `h1.poly_eq hP'`.

Rewrite `e` using `[← hpol']`. Establish `e2` using `congrArg (MvPolynomial.coeff s.1) e`. Rewrite `e2` using `[pol_coeff, pol_coeff]`. Conclude with `e2`. Introduce `h`.

Establish `h1` using `hmapD (g : R →+* R')`. Rewrite `h1` using `[show (fun s => (g : R →+* R') (a s)) = (fun s : Mn G n => MvPolynomial.coeff s.1 P') from funext h, hpol']`. Conclude with `h1.det_eq hP'`. Conclude with `⟨f, (key f).2 hf, fun g hg => hfu g ((key g).1 hg)⟩`.
-/
theorem UpperTheory.V.CA.u_fin :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {n : ℕ} {G : Type} [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] (Dbar : GDet n (ResidueField O) G), ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (D : GDet n R G), IsUnivDet O Dbar D := by
  intro O _ _ _ _ _ n G _ _ _ _ Dbar
  classical
  letI : Fintype G := Fintype.ofFinite G
  obtain ⟨Pbar, hPbar⟩ := ex_rep Dbar
  have hhom := hPbar.homog
  have hpolbar : (pol fun s : Mn G n => MvPolynomial.coeff s.1 Pbar) = Pbar := pol_eq hhom
  obtain ⟨R, _, _, _, a, ha, hd1, hd2, huniv⟩ := points O (fun s : Mn G n => MvPolynomial.coeff s.1 Pbar)
    (by rw [hpolbar]; exact hPbar.d1) (by rw [hpolbar]; exact hPbar.d2)
  obtain ⟨D, hD⟩ := u_poly (pol a) (pol_homog a) (sub_eq_zero.1 hd1) (sub_eq_zero.1 hd2)
  have hDrep : PRep D (pol a) := hD
  have hmapD : ∀ {R' : Type} [CommRing R'] (f : R →+* R'), PRep (D.map f) (pol fun s => f (a s)) := by
    intro R' _ f
    rw [← pol_map]
    exact hDrep.map f
  refine ⟨R, inferInstance, inferInstance, inferInstance, D, ⟨⟨fun i N => IsLocallyConstant.of_discrete _, ?_⟩, ?_⟩⟩
  · have h1 := hmapD (res O R : R →+* ResidueField O)
    rw [show (fun s => (res O R : R →+* ResidueField O) (a s)) =
      (fun s : Mn G n => MvPolynomial.coeff s.1 Pbar) from funext ha, hpolbar] at h1
    exact h1.det_eq hPbar
  · intro R' _ _ _ D' hD'
    obtain ⟨P', hP'⟩ := ex_rep D'
    have hpol' : (pol fun s : Mn G n => MvPolynomial.coeff s.1 P') = P' := pol_eq hP'.homog
    have hred : MvPolynomial.map (res O R' : R' →+* ResidueField O) P' = Pbar := by
      have h1 := hP'.map (res O R' : R' →+* ResidueField O)
      rw [hD'.red] at h1
      exact h1.poly_eq hPbar
    have ha' : ∀ s : Mn G n, res O R' (MvPolynomial.coeff s.1 P') = MvPolynomial.coeff s.1 Pbar := by
      intro s
      rw [← hred, MvPolynomial.coeff_map]
      rfl
    obtain ⟨f, hf, hfu⟩ := huniv R' (fun s => MvPolynomial.coeff s.1 P') ha'
      (by rw [hpol']; exact hP'.d1) (by rw [hpol']; exact hP'.d2)
    have key : ∀ g : R →ₐ[O] R', D.map (g : R →+* R') = D' ↔ ∀ s, g (a s) = MvPolynomial.coeff s.1 P' := by
      intro g
      constructor
      · intro h s
        have h1 := hmapD (g : R →+* R')
        rw [h] at h1
        have e := h1.poly_eq hP'
        rw [← hpol'] at e
        have e2 := congrArg (MvPolynomial.coeff s.1) e
        rw [pol_coeff, pol_coeff] at e2
        exact e2
      · intro h
        have h1 := hmapD (g : R →+* R')
        rw [show (fun s => (g : R →+* R') (a s)) = (fun s : Mn G n => MvPolynomial.coeff s.1 P') from funext h,
          hpol'] at h1
        exact h1.det_eq hP'
    exact ⟨f, (key f).2 hf, fun g hg => hfu g ((key g).1 hg)⟩
