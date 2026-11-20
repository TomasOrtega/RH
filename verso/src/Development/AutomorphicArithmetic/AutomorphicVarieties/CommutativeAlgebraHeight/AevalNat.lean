import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPoly

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

section

variable {n : ℕ} {A G : Type} [CommRing A] [Group G]

private noncomputable def pol (D : GDet n A G) (s : Finset G) : MvPolynomial s A :=
  D.D _ (∑ a : s, MonoidAlgebra.single (a : G) (MvPolynomial.X a))

/- English proof (translation)
Establish `h` using `(d_poly D.toDet (fun a : s => (MonoidAlgebra.single (a : G) 1 : MonoidAlgebra A G))).1`. Establish `h2 : D.toDet.poly (fun a : s => (MonoidAlgebra.single (a : G) 1 : MonoidAlgebra A G)) = pol D s`. Express the relevant statement in the definitionally equal form `D.D _ (ofT A G _ _) = D.D _ _`. Use `congr 1`. Simplify using `[Det.gen, map_sum, ofT_tmul]`.

Rewrite `h` using `[h2]`. Then use the resulting hypothesis.
-/
private theorem pol_homog (D : GDet n A G) (s : Finset G) : (pol D s).IsHomogeneous n := by
  have h := (d_poly D.toDet (fun a : s => (MonoidAlgebra.single (a : G) 1 : MonoidAlgebra A G))).1
  have h2 : D.toDet.poly (fun a : s => (MonoidAlgebra.single (a : G) 1 : MonoidAlgebra A G)) = pol D s := by
    change D.D _ (ofT A G _ _) = D.D _ _
    congr 1
    simp [Det.gen, map_sum, ofT_tmul]
  rwa [h2] at h

/- English proof (translation)
The claim follows from `letI : Algebra A S' := ((algebraMap A' S').comp f).toAlgebra D.nat S S' { φ with commutes' := h } y`.
-/
private theorem nat' (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A') {S S' : Type} [CommRing S]
    [Algebra A S] [CommRing S'] [Algebra A' S'] (φ : S →+* S')
    (h : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (f a)) (y : MonoidAlgebra S G) :
    (D.map f).D S' (MonoidAlgebra.mapRingHom G φ y) = φ (D.D S y) :=
  letI : Algebra A S' := ((algebraMap A' S').comp f).toAlgebra
  D.nat S S' { φ with commutes' := h } y

/- English proof (translation)
Rewrite using `[pol, pol, ← nat' D f (MvPolynomial.map f) (by simp)]`. Use `congr 1`. Simplify using `[map_sum]`.
-/
private theorem pol_map (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A') (s : Finset G) :
    pol (D.map f) s = MvPolynomial.map f (pol D s) := by
  rw [pol, pol, ← nat' D f (MvPolynomial.map f) (by simp)]
  congr 1
  simp [map_sum]

/- English proof (translation)
Rewrite using `[Finset.sum_coe_sort s (fun a => MonoidAlgebra.single a (y.coeff a))]`. Use extensionality with `g`. Simplify using `only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression.

Conclude with `(Finsupp.notMem_support_iff.1 fun h' => h (hy h')).symm`.
-/
private theorem sum_single {S : Type} [CommRing S] (s : Finset G) (y : MonoidAlgebra S G)
    (hy : y.coeff.support ⊆ s) : ∑ a : s, MonoidAlgebra.single (a : G) (y.coeff a) = y := by
  classical
  rw [Finset.sum_coe_sort s (fun a => MonoidAlgebra.single a (y.coeff a))]
  ext g
  simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply, Finsupp.single_apply, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 fun h' => h (hy h')).symm

/- English proof (translation)
Rewrite using `[pol, ← D.nat]`. Use `congr 1`. Use `conv_lhs => rw [← sum_single s y hy]`. Simplify using `[map_sum]`.
-/
private theorem pol_eval (D : GDet n A G) (s : Finset G) {S : Type} [CommRing S] [Algebra A S]
    (y : MonoidAlgebra S G) (hy : y.coeff.support ⊆ s) :
    D.D S y = MvPolynomial.aeval (fun a : s => y.coeff a) (pol D s) := by
  rw [pol, ← D.nat]
  congr 1
  conv_lhs => rw [← sum_single s y hy]
  simp [map_sum]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [h]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X]`.
-/
private theorem aeval_nat {σ A' : Type} [CommRing A'] (f : A →+* A') {S S' : Type} [CommRing S]
    [Algebra A S] [CommRing S'] [Algebra A' S'] (φ : S →+* S')
    (h : ∀ a, φ (algebraMap A S a) = algebraMap A' S' (f a)) (c : σ → S) (p : MvPolynomial σ A) :
    φ (MvPolynomial.aeval c p) = MvPolynomial.aeval (fun a => φ (c a)) (MvPolynomial.map f p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [h]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, MvPolynomial.map_X]

/- English proof (translation)
Introduce `g hg`. Rewrite `hg`, the goal using `[Finsupp.mem_support_iff]`. Introduce `h`. Apply `hg` to reduce the goal to its premises. Simplify using `[h]`.
-/
private theorem supp_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (y : MonoidAlgebra S G) :
    (MonoidAlgebra.mapRingHom G φ y).coeff.support ⊆ y.coeff.support := by
  intro g hg
  rw [Finsupp.mem_support_iff] at hg ⊢
  intro h
  apply hg
  simp [h]

/- English proof (translation)
Use extensionality with `m`. Use `sub_eq_zero.1 (IsHausdorff.haus (I := I) inferInstance _ fun N => ?_)` and prove the remaining obligations. Use `congrArg (MvPolynomial.coeff m) (h N)` as an intermediate fact. Rewrite `this` using `[MvPolynomial.coeff_map, MvPolynomial.coeff_map, Ideal.Quotient.eq]`. Rewrite using `[SModEq.zero, smul_eq_mul, Ideal.mul_top]`.

Conclude with `this`.
-/
private theorem sep (I : Ideal A) [IsAdicComplete I A] {σ : Type} {p q : MvPolynomial σ A}
    (h : ∀ N : ℕ, MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) p = MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) q) :
    p = q := by
  ext m
  refine sub_eq_zero.1 (IsHausdorff.haus (I := I) inferInstance _ fun N => ?_)
  have := congrArg (MvPolynomial.coeff m) (h N)
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map, Ideal.Quotient.eq] at this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact this

/- English proof (translation)
Use `choose f hf using fun N => Ideal.Quotient.mk_surjective (c N)`. Take `⟨L, hL⟩` from `IsPrecomplete.prec (I := I) inferInstance (f := f) (fun {m k} hmk => by`. Rewrite using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hf, ← h k m hmk, ← hf k, Ideal.Quotient.factor_mk])`. Use `⟨L, fun N => ?_⟩` and prove the remaining obligations. Use `hL N` as an intermediate fact.

Rewrite `this` using `[SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hf]`. Conclude with `this.symm`.
-/
private theorem lim0 (I : Ideal A) [IsAdicComplete I A] (c : ∀ N : ℕ, A ⧸ I ^ N)
    (h : ∀ (N M : ℕ) (h : M ≤ N), Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (c N) = c M) :
    ∃ a : A, ∀ N, Ideal.Quotient.mk (I ^ N) a = c N := by
  choose f hf using fun N => Ideal.Quotient.mk_surjective (c N)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) inferInstance (f := f) (fun {m k} hmk => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hf, ← h k m hmk, ← hf k,
      Ideal.Quotient.factor_mk])
  refine ⟨L, fun N => ?_⟩
  have := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Ideal.Quotient.eq, hf] at this
  exact this.symm

/- English proof (translation)
Use `choose a ha using fun m : σ →₀ ℕ => lim0 I (fun N => (c N).coeff m) fun N M hle => by`. Rewrite using `[← h N M hle, MvPolynomial.coeff_map]`. Use `⟨∑ m ∈ (Finsupp.finite_of_degree_le (σ := σ) n).toFinset, MvPolynomial.monomial m (a m), fun N => ?_⟩` and prove the remaining obligations. Use extensionality with `m`. Simplify using `only [MvPolynomial.coeff_map, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']`.

Use `split_ifs with hm`. Conclude with `ha m N`. Rewrite using `[map_zero, (hc N).coeff_eq_zero]`. Introduce `hd`. Conclude with `hm (by simp [hd])`.
-/
private theorem lim1 (I : Ideal A) [IsAdicComplete I A] {σ : Type} [Finite σ]
    (c : ∀ N : ℕ, MvPolynomial σ (A ⧸ I ^ N)) (hc : ∀ N, (c N).IsHomogeneous n)
    (h : ∀ (N M : ℕ) (h : M ≤ N),
      MvPolynomial.map (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) (c N) = c M) :
    ∃ p : MvPolynomial σ A, ∀ N, MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) p = c N := by
  classical
  choose a ha using fun m : σ →₀ ℕ => lim0 I (fun N => (c N).coeff m) fun N M hle => by
    rw [← h N M hle, MvPolynomial.coeff_map]
  refine ⟨∑ m ∈ (Finsupp.finite_of_degree_le (σ := σ) n).toFinset, MvPolynomial.monomial m (a m), fun N => ?_⟩
  ext m
  simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
  split_ifs with hm
  · exact ha m N
  · rw [map_zero, (hc N).coeff_eq_zero]
    intro hd
    exact hm (by simp [hd])

/- English proof (translation)
Use `⟨∑ a : y.coeff.support, MonoidAlgebra.single (a : G) (MvPolynomial.X (y.coeff a)), ?_, ?_⟩` and prove the remaining obligations. Introduce `g hg`. Assume the negation of the conclusion as `h`. Rewrite `hg` using `[Finsupp.mem_support_iff]`. Apply `hg` to reduce the goal to its premises.

Simplify using `only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply]`. Use `Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Conclude with `h a.2`. Use `conv_rhs => rw [← sum_single _ y le_rfl]`.

Simplify using `[map_sum]`.
-/
private theorem lift_ex {S : Type} [CommRing S] [Algebra A S] (y : MonoidAlgebra S G) :
    ∃ y' : MonoidAlgebra (MvPolynomial S A) G, y'.coeff.support ⊆ y.coeff.support ∧
      MonoidAlgebra.mapRingHom G ((MvPolynomial.aeval id : MvPolynomial S A →ₐ[A] S) : MvPolynomial S A →+* S) y' = y := by
  classical
  refine ⟨∑ a : y.coeff.support, MonoidAlgebra.single (a : G) (MvPolynomial.X (y.coeff a)), ?_, ?_⟩
  · intro g hg
    by_contra h
    rw [Finsupp.mem_support_iff] at hg
    apply hg
    simp only [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single, Finsupp.finset_sum_apply]
    refine Finset.sum_eq_zero fun a _ => Finsupp.single_eq_of_ne ?_
    rintro rfl
    exact h a.2
  · conv_rhs => rw [← sum_single _ y le_rfl]
    simp [map_sum]

end

/- English proof (translation)
Introduce `n A G _ _ I _ Ds hDs`. Use `choose P hP using fun s : Finset G => lim1 I (fun N => pol (Ds N) s) (fun N => pol_homog _ s) fun N M h => by rw [← pol_map, hDs N M h]`. Establish `red : ∀ (N : ℕ) (s : Finset G) {S S' : Type} [CommRing S] [Algebra A S] [CommRing S'] [Algebra (A ⧸ I ^ N) S'] (φ : S →+* S') (_ : ∀ a, φ (algebraMap A S a) = algebraMap _ S' (Ideal.Quotient.mk (I ^ N) a)) (y : MonoidAlgebra S G), y.coeff.support ⊆ s → φ (MvPolynomial.aeval (fun …`. Introduce `N s S S' _ _ _ _ φ h y hy`. Rewrite using `[aeval_nat _ φ h, hP, pol_eval _ s _ ((supp_map φ y).trans hy)]`.

Simplify using the standard rewrite rules. Establish `red' : ∀ (N : ℕ) (s : Finset G) {σ : Type} (y : MonoidAlgebra (MvPolynomial σ A) G), y.coeff.support ⊆ s → MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) = (Ds N).D _ (MonoidAlgebra.mapRingHom G (MvPolynomial.map (Ideal.Quotient.m …` using `fun N s σ y hy => red N s _ (by simp) y hy`. Establish `nat : ∀ (s : Finset G) {S S' : Type} [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S'] (φ : S →ₐ[A] S') (y : MonoidAlgebra S G), MvPolynomial.aeval (fun a : s => (MonoidAlgebra.mapRingHom G (φ : S →+* S') y).coeff a) (P s) = φ (MvPolynomial.aeval (fun a : s => y.coeff a) (P …`. Introduce `s S S' _ _ _ _ φ y`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`.

Simplify using the standard rewrite rules. Establish `indep : ∀ (s : Finset G) {S : Type} [CommRing S] [Algebra A S] (y : MonoidAlgebra S G), y.coeff.support ⊆ s → MvPolynomial.aeval (fun a : y.coeff.support => y.coeff a) (P _) = MvPolynomial.aeval (fun a : s => y.coeff a) (P s)`. Introduce `s S _ _ y hy`. Take `⟨y', h1, h2⟩` from `lift_ex (A := A) y`. Establish `e1` using `nat s (MvPolynomial.aeval id) y'`.

Establish `e2` using `nat y.coeff.support (MvPolynomial.aeval id) y'`. Rewrite `e1`, `e2` using `[h2]`. Rewrite using `[e1, e2]`. Use `congr 1`. Conclude with `sep I fun N => by rw [red' N _ _ h1, red' N _ _ (h1.trans hy)]`.

Set `E : ∀ (S : Type) [CommRing S] [Algebra A S], MonoidAlgebra S G → S` to `fun S _ _ y => MvPolynomial.aeval (fun a : y.coeff.support => y.coeff a) (P _)`. Establish `Enat : ∀ (S S' : Type) [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S'] (φ : S →ₐ[A] S') (y : MonoidAlgebra S G), E S' (MonoidAlgebra.mapRingHom G (φ : S →+* S') y) = φ (E S y)` using `fun S S' _ _ _ _ φ y => (indep _ _ (supp_map _ y)).trans (nat _ φ y)`. Establish `Ered : ∀ (N : ℕ) {σ : Type} (y : MonoidAlgebra (MvPolynomial σ A) G), MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) (E _ y) = (Ds N).D _ (MonoidAlgebra.mapRingHom G (MvPolynomial.map (Ideal.Quotient.mk (I ^ N))) y)` using `fun N σ y => red' N _ y le_rfl`. Establish `Eone : ∀ (S : Type) [CommRing S] [Algebra A S], E S 1 = 1`. Introduce `S _ _`.

Establish `h1 : E (MvPolynomial S A) 1 = 1` using `sep I fun N => by simp only [Ered, map_one]`. Use `Enat _ S (MvPolynomial.aeval id) 1` as an intermediate fact. Rewrite `this` using `[h1, map_one, map_one]`. Then use the resulting hypothesis. Establish `Emul : ∀ (S : Type) [CommRing S] [Algebra A S] (x y), E S (x * y) = E S x * E S y`. Introduce `S _ _ x y`.

Take `⟨x', -, rfl⟩` from `lift_ex (A := A) x`. Take `⟨y', -, rfl⟩` from `lift_ex (A := A) y`. Rewrite using `[← map_mul, Enat, Enat, Enat, ← map_mul]`. Use `congr 1`. Conclude with `sep I fun N => by simp only [Ered, map_mul]`.

Establish `Ehom : ∀ (S : Type) [CommRing S] [Algebra A S] (b : S) (x), E S (b • x) = b ^ n * E S x`. Introduce `S _ _ b x`. Take `⟨x', -, rfl⟩` from `lift_ex (A := A) x`. Establish `h1 : E _ ((MvPolynomial.X b : MvPolynomial S A) • x') = MvPolynomial.X b ^ n * E _ x'` using `sep I fun N => by`. Rewrite using `[map_mul, map_pow, Ered, Ered, ← (Ds N).homog]`.

Use `congr 1`. Use `ext1`. Use `ext1`. Simplify using the standard rewrite rules. Establish `h2` using `Enat _ S (MvPolynomial.aeval id) ((MvPolynomial.X b : MvPolynomial S A) • x')`.

Rewrite `h2` using `[h1, map_mul, map_pow, MvPolynomial.aeval_X, ← Enat]`. Use `Eq.trans ?_ h2` and prove the remaining obligations. Use `congr 1`. Use extensionality with `g`. Simplify using the standard rewrite rules.

Use `⟨⟨fun S _ _ => ⟨⟨E S, Eone S⟩, Emul S⟩, Enat, Ehom⟩, fun N => ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `B _ _ y`. Use `letI : Algebra A B := ((algebraMap (A ⧸ I ^ N) B).comp (Ideal.Quotient.mk (I ^ N))).toAlgebra`. Use `red N _ (RingHom.id B) (fun _ => rfl) y le_rfl` as an intermediate fact. Use `Eq.trans this ?_` and prove the remaining obligations.

Use `congr 1`. Use extensionality with `g`. Simplify using the standard rewrite rules. Introduce `D hD`. Use extensionality with `B _ _ y`.

Establish `: pol D y.coeff.support = P _` using `sep I fun N => by rw [hP, ← pol_map, hD]`. Rewrite using `[pol_eval D _ y le_rfl, this]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.CA.u_lim :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (I : Ideal A) [IsAdicComplete I A] (Ds : ∀ N : ℕ, GDet n (A ⧸ I ^ N) G), (∀ (N M : ℕ) (h : M ≤ N), (Ds N).map (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) = Ds M) → ∃! D : GDet n A G, ∀ N, D.map (Ideal.Quotient.mk (I ^ N)) = Ds N := by
  intro n A G _ _ I _ Ds hDs
  choose P hP using fun s : Finset G => lim1 I (fun N => pol (Ds N) s) (fun N => pol_homog _ s)
    fun N M h => by rw [← pol_map, hDs N M h]
  have red : ∀ (N : ℕ) (s : Finset G) {S S' : Type} [CommRing S] [Algebra A S] [CommRing S'] [Algebra (A ⧸ I ^ N) S']
      (φ : S →+* S') (_ : ∀ a, φ (algebraMap A S a) = algebraMap _ S' (Ideal.Quotient.mk (I ^ N) a))
      (y : MonoidAlgebra S G), y.coeff.support ⊆ s →
      φ (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) = (Ds N).D S' (MonoidAlgebra.mapRingHom G φ y) := by
    intro N s S S' _ _ _ _ φ h y hy
    rw [aeval_nat _ φ h, hP, pol_eval _ s _ ((supp_map φ y).trans hy)]
    simp
  have red' : ∀ (N : ℕ) (s : Finset G) {σ : Type} (y : MonoidAlgebra (MvPolynomial σ A) G), y.coeff.support ⊆ s →
      MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) =
        (Ds N).D _ (MonoidAlgebra.mapRingHom G (MvPolynomial.map (Ideal.Quotient.mk (I ^ N))) y) :=
    fun N s σ y hy => red N s _ (by simp) y hy
  have nat : ∀ (s : Finset G) {S S' : Type} [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S']
      (φ : S →ₐ[A] S') (y : MonoidAlgebra S G),
      MvPolynomial.aeval (fun a : s => (MonoidAlgebra.mapRingHom G (φ : S →+* S') y).coeff a) (P s) =
        φ (MvPolynomial.aeval (fun a : s => y.coeff a) (P s)) := by
    intro s S S' _ _ _ _ φ y
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    simp
  have indep : ∀ (s : Finset G) {S : Type} [CommRing S] [Algebra A S] (y : MonoidAlgebra S G),
      y.coeff.support ⊆ s → MvPolynomial.aeval (fun a : y.coeff.support => y.coeff a) (P _) =
        MvPolynomial.aeval (fun a : s => y.coeff a) (P s) := by
    intro s S _ _ y hy
    obtain ⟨y', h1, h2⟩ := lift_ex (A := A) y
    have e1 := nat s (MvPolynomial.aeval id) y'
    have e2 := nat y.coeff.support (MvPolynomial.aeval id) y'
    rw [h2] at e1 e2
    rw [e1, e2]
    congr 1
    exact sep I fun N => by rw [red' N _ _ h1, red' N _ _ (h1.trans hy)]
  let E : ∀ (S : Type) [CommRing S] [Algebra A S], MonoidAlgebra S G → S :=
    fun S _ _ y => MvPolynomial.aeval (fun a : y.coeff.support => y.coeff a) (P _)
  have Enat : ∀ (S S' : Type) [CommRing S] [Algebra A S] [CommRing S'] [Algebra A S']
      (φ : S →ₐ[A] S') (y : MonoidAlgebra S G), E S' (MonoidAlgebra.mapRingHom G (φ : S →+* S') y) = φ (E S y) :=
    fun S S' _ _ _ _ φ y => (indep _ _ (supp_map _ y)).trans (nat _ φ y)
  have Ered : ∀ (N : ℕ) {σ : Type} (y : MonoidAlgebra (MvPolynomial σ A) G),
      MvPolynomial.map (Ideal.Quotient.mk (I ^ N)) (E _ y) =
        (Ds N).D _ (MonoidAlgebra.mapRingHom G (MvPolynomial.map (Ideal.Quotient.mk (I ^ N))) y) :=
    fun N σ y => red' N _ y le_rfl
  have Eone : ∀ (S : Type) [CommRing S] [Algebra A S], E S 1 = 1 := by
    intro S _ _
    have h1 : E (MvPolynomial S A) 1 = 1 := sep I fun N => by simp only [Ered, map_one]
    have := Enat _ S (MvPolynomial.aeval id) 1
    rwa [h1, map_one, map_one] at this
  have Emul : ∀ (S : Type) [CommRing S] [Algebra A S] (x y), E S (x * y) = E S x * E S y := by
    intro S _ _ x y
    obtain ⟨x', -, rfl⟩ := lift_ex (A := A) x
    obtain ⟨y', -, rfl⟩ := lift_ex (A := A) y
    rw [← map_mul, Enat, Enat, Enat, ← map_mul]
    congr 1
    exact sep I fun N => by simp only [Ered, map_mul]
  have Ehom : ∀ (S : Type) [CommRing S] [Algebra A S] (b : S) (x), E S (b • x) = b ^ n * E S x := by
    intro S _ _ b x
    obtain ⟨x', -, rfl⟩ := lift_ex (A := A) x
    have h1 : E _ ((MvPolynomial.X b : MvPolynomial S A) • x') = MvPolynomial.X b ^ n * E _ x' :=
      sep I fun N => by
        rw [map_mul, map_pow, Ered, Ered, ← (Ds N).homog]
        congr 1
        ext1
        ext1
        simp
    have h2 := Enat _ S (MvPolynomial.aeval id) ((MvPolynomial.X b : MvPolynomial S A) • x')
    rw [h1, map_mul, map_pow, MvPolynomial.aeval_X, ← Enat] at h2
    refine Eq.trans ?_ h2
    congr 1
    ext g
    simp
  refine ⟨⟨fun S _ _ => ⟨⟨E S, Eone S⟩, Emul S⟩, Enat, Ehom⟩, fun N => ?_, ?_⟩
  · ext B _ _ y
    letI : Algebra A B := ((algebraMap (A ⧸ I ^ N) B).comp (Ideal.Quotient.mk (I ^ N))).toAlgebra
    have := red N _ (RingHom.id B) (fun _ => rfl) y le_rfl
    refine Eq.trans this ?_
    congr 1
    ext g
    simp
  · intro D hD
    ext B _ _ y
    have : pol D y.coeff.support = P _ := sep I fun N => by rw [hP, ← pol_map, hD]
    rw [pol_eval D _ y le_rfl, this]
    rfl
