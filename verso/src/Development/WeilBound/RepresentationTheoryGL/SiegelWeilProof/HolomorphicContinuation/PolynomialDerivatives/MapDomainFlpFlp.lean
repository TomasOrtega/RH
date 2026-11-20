import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.NullStableAlt

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.LC.Basic

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC

variable {m n : ℕ}

abbrev Ix (m n : ℕ) := Fin m × Fin n × Bool

def flp (k : Ix m n) : Ix m n := (k.1, k.2.1, !k.2.2)

/- English proof (translation)
Take `⟨a, i, b⟩` from `k`. Simplify using `[flp]`.
-/
theorem flp_flp (k : Ix m n) : flp (flp k) = k := by
  obtain ⟨a, i, b⟩ := k; simp [flp]

def flpEquiv : Ix m n ≃ Ix m n := ⟨flp, flp, flp_flp, flp_flp⟩

/- English proof (translation)
The claim follows from `flpEquiv.injective`.
-/
theorem flp_injective : Function.Injective (flp (m := m) (n := n)) := flpEquiv.injective

/- English proof (translation)
Take `⟨a, i, b⟩` from `k`. Apply the tactic sequence `cases b <;> (simp [cr, flp]; try abel)`.
-/
theorem cr_apply (c : ℝ) (k : Ix m n) (P : PX m n) :
    cr c k P = (2 * c : ℂ) • (X (flp k) * P) - pderiv k P := by
  obtain ⟨a, i, b⟩ := k
  cases b <;> (simp [cr, flp]; try abel)

/- English proof (translation)
Establish `h : ⁅(pderiv k : Derivation ℂ (PX m n) (PX m n)), (pderiv l : Derivation ℂ (PX m n) (PX m n))⁆ = 0`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce `i`. Rewrite using `[Derivation.commutator_apply, pderiv_X, pderiv_X]`. Simplify using `only [Pi.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h2` using `congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D P) h`. Simplify using `only [Derivation.commutator_apply] at h2`. Conclude with `sub_eq_zero.mp (by simpa using h2)`.
-/
theorem pderiv_comm' (k l : Ix m n) (P : PX m n) :
    pderiv k (pderiv l P) = pderiv l (pderiv k P) := by
  classical
  have h : ⁅(pderiv k : Derivation ℂ (PX m n) (PX m n)), (pderiv l : Derivation ℂ (PX m n) (PX m n))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation ℂ (PX m n) (PX m n) => D P) h
  simp only [Derivation.commutator_apply] at h2
  exact sub_eq_zero.mp (by simpa using h2)

/- English proof (translation)
Simplify using `only [cr_apply, map_sub, Derivation.map_smul, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul]`. Simplify using `only [MvPolynomial.smul_eq_C_mul, pderiv_C, mul_zero, zero_mul, add_zero, zero_add]`. Rewrite using `[pderiv_comm' k l P]`. Establish `e : (flp l = k) ↔ (flp k = l)` using `⟨fun h => by rw [← h, flp_flp], fun h => by rw [← h, flp_flp]⟩`. Distinguish the cases in `h : flp l = k`.

Establish `h'` using `e.mp h`. Simplify using `only [h, h', if_true]`. Expand and normalize the polynomial expressions, which then agree. Establish `h' : ¬ flp k = l` using `fun h'' => h (e.mpr h'')`. Simplify using `only [h, h', if_false]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem cr_comm (c : ℝ) (k l : Ix m n) (P : PX m n) :
    cr c k (cr c l P) = cr c l (cr c k P) := by
  classical
  simp only [cr_apply, map_sub, Derivation.map_smul, Derivation.leibniz, pderiv_X, Pi.single_apply, smul_eq_mul]
  simp only [MvPolynomial.smul_eq_C_mul, pderiv_C, mul_zero, zero_mul, add_zero, zero_add]
  rw [pderiv_comm' k l P]
  have e : (flp l = k) ↔ (flp k = l) :=
    ⟨fun h => by rw [← h, flp_flp], fun h => by rw [← h, flp_flp]⟩
  by_cases h : flp l = k
  · have h' := e.mp h
    simp only [h, h', if_true]
    ring
  · have h' : ¬ flp k = l := fun h'' => h (e.mpr h'')
    simp only [h, h', if_false]
    ring

/- English proof (translation)
Introduce and unpack `_ ⟨k, rfl⟩ _ ⟨l, rfl⟩`. Conclude with `LinearMap.ext fun P => cr_comm c k l P`.
-/
theorem crAlg_comm (c : ℝ) : ∀ a ∈ Set.range (cr (m := m) (n := n) c), ∀ b ∈ Set.range (cr (m := m) (n := n) c),
    a * b = b * a := by
  rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
  exact LinearMap.ext fun P => cr_comm c k l P

abbrev CrAlg (m n : ℕ) (c : ℝ) : Subalgebra ℂ (Module.End ℂ (PX m n)) := Algebra.adjoin ℂ (Set.range (cr c))

instance instCommRingCrAlg (c : ℝ) : CommRing (CrAlg m n c) := Algebra.adjoinCommRingOfComm ℂ (crAlg_comm c)

def gen (c : ℝ) (k : Ix m n) : CrAlg m n c := ⟨cr c k, Algebra.subset_adjoin ⟨k, rfl⟩⟩

def phi (c : ℝ) : PX m n →ₐ[ℂ] CrAlg m n c := MvPolynomial.aeval (gen c)

/- English proof (translation)
Rewrite using `[phi, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← Finset.prod_map_toList]`. Rewrite using `[SubmonoidClass.coe_list_prod, List.map_map]`. Use `congr 1`.
-/
theorem coe_phi_monomial (c : ℝ) (s : Ix m n →₀ ℕ) :
    ((phi c (monomial s 1) : CrAlg m n c) : Module.End ℂ (PX m n)) =
      ((Finset.univ : Finset (Ix m n)).toList.map fun k => (cr c k) ^ (s k)).prod := by
  rw [phi, aeval_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    ← Finset.prod_map_toList]
  rw [SubmonoidClass.coe_list_prod, List.map_map]
  congr 1

/- English proof (translation)
Rewrite using `[coe_phi_monomial]`. Both sides reduce to the same expression.
-/
theorem fockMono_eq (c : ℝ) (s : Ix m n →₀ ℕ) :
    fockMono c s = ((phi c (monomial s 1) : CrAlg m n c) : Module.End ℂ (PX m n)) 1 := by
  rw [coe_phi_monomial]; rfl

/- English proof (translation)
Use `conv_rhs => rw [p.as_sum]`. Rewrite using `[map_sum, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Establish `: monomial s (p.coeff s) = p.coeff s • (monomial s 1 : PX m n)`. Rewrite using `[smul_monomial, smul_eq_mul, mul_one]`.

Rewrite using `[this, map_smul, Subalgebra.coe_smul, LinearMap.smul_apply, fockMono_eq]`.
-/
theorem fock_eq (c : ℝ) (p : PX m n) : fock c p = ((phi c p : CrAlg m n c) : Module.End ℂ (PX m n)) 1 := by
  conv_rhs => rw [p.as_sum]
  rw [map_sum, AddSubmonoidClass.coe_finsetSum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have : monomial s (p.coeff s) = p.coeff s • (monomial s 1 : PX m n) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, Subalgebra.coe_smul, LinearMap.smul_apply, fockMono_eq]

/- English proof (translation)
Simplify using `only [fock_eq, map_add, Subalgebra.coe_add, LinearMap.add_apply]`.
-/
theorem fock_add (c : ℝ) (p q : PX m n) : fock c (p + q) = fock c p + fock c q := by
  simp only [fock_eq, map_add, Subalgebra.coe_add, LinearMap.add_apply]

/- English proof (translation)
Simplify using `only [fock_eq, map_smul, Subalgebra.coe_smul, LinearMap.smul_apply]`.
-/
theorem fock_smul (c : ℝ) (a : ℂ) (p : PX m n) : fock c (a • p) = a • fock c p := by
  simp only [fock_eq, map_smul, Subalgebra.coe_smul, LinearMap.smul_apply]

/- English proof (translation)
Simplify using `[fock]`.
-/
theorem fock_zero (c : ℝ) : fock c (0 : PX m n) = 0 := by simp [fock]

/- English proof (translation)
Use `fock_add c (p - q) q` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Rewrite using `[this, add_sub_cancel_right]`.
-/
theorem fock_sub (c : ℝ) (p q : PX m n) : fock c (p - q) = fock c p - fock c q := by
  have := fock_add c (p - q) q
  rw [sub_add_cancel] at this
  rw [this, add_sub_cancel_right]

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simp [fock_zero]`. Consider the case `insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add, ih]`.
-/
theorem fock_sum (c : ℝ) {ι : Type*} (t : Finset ι) (f : ι → PX m n) :
    fock c (∑ i ∈ t, f i) = ∑ i ∈ t, fock c (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [fock_zero]
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add, ih]

/- English proof (translation)
Rewrite using `[fock_eq, fock_eq, map_mul, Subalgebra.coe_mul, Module.End.mul_apply]`. Simplify using `[phi, gen]`.
-/
theorem fock_X_mul (c : ℝ) (k : Ix m n) (p : PX m n) : fock c (X k * p) = cr c k (fock c p) := by
  rw [fock_eq, fock_eq, map_mul, Subalgebra.coe_mul, Module.End.mul_apply]
  simp [phi, gen]

/- English proof (translation)
Rewrite using `[fockMono_eq, fock_eq]`.
-/
theorem fock_monomial (c : ℝ) (s : Ix m n →₀ ℕ) : fock c (monomial s 1) = fockMono c s := by
  rw [fockMono_eq, fock_eq]

/- English proof (translation)
Simplify using `only [Finsupp.degree_eq_sum, Finsupp.add_apply, Finset.sum_add_distrib]`.
-/
theorem degree_add' (a b : Ix m n →₀ ℕ) : (a + b).degree = a.degree + b.degree := by
  simp only [Finsupp.degree_eq_sum, Finsupp.add_apply, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [Finsupp.degree_eq_sum]`. Rewrite using `[← Equiv.sum_comp flpEquiv]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `Finsupp.mapDomain_apply flp_injective t i`.
-/
theorem degree_mapDomain (t : Ix m n →₀ ℕ) : (Finsupp.mapDomain flp t).degree = t.degree := by
  simp only [Finsupp.degree_eq_sum]
  rw [← Equiv.sum_comp flpEquiv]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finsupp.mapDomain_apply flp_injective t i

/- English proof (translation)
Rewrite using `[← Finsupp.mapDomain_comp]`. Establish `: (flp ∘ flp : Ix m n → Ix m n) = id` using `funext flp_flp`. Rewrite using `[this, Finsupp.mapDomain_id]`.
-/
theorem mapDomain_flp_flp (t : Ix m n →₀ ℕ) : Finsupp.mapDomain flp (Finsupp.mapDomain flp t) = t := by
  rw [← Finsupp.mapDomain_comp]
  have : (flp ∘ flp : Ix m n → Ix m n) = id := funext flp_flp
  rw [this, Finsupp.mapDomain_id]

def DegLT (d : ℕ) (Q : PX m n) : Prop := ∀ t ∈ Q.support, t.degree < d

/- English proof (translation)
Simplify using `[DegLT]`.
-/
theorem DegLT.zero (d : ℕ) : DegLT d (0 : PX m n) := by simp [DegLT]

/- English proof (translation)
Introduce `t ht`. Break down `Finset.mem_union.mp (MvPolynomial.support_add ht) with h | h` into its components or cases. Conclude with `hP t h`. Conclude with `hQ t h`.
-/
theorem DegLT.add {d : ℕ} {P Q : PX m n} (hP : DegLT d P) (hQ : DegLT d Q) : DegLT d (P + Q) := by
  classical
  intro t ht
  rcases Finset.mem_union.mp (MvPolynomial.support_add ht) with h | h
  · exact hP t h
  · exact hQ t h

/- English proof (translation)
Introduce `t ht`. Rewrite `ht` using `[MvPolynomial.support_neg]`. Conclude with `hP t ht`.
-/
theorem DegLT.neg {d : ℕ} {P : PX m n} (hP : DegLT d P) : DegLT d (-P) := by
  intro t ht; rw [MvPolynomial.support_neg] at ht; exact hP t ht

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `hP.add hQ.neg`.
-/
theorem DegLT.sub {d : ℕ} {P Q : PX m n} (hP : DegLT d P) (hQ : DegLT d Q) : DegLT d (P - Q) := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg

/- English proof (translation)
Introduce `t ht`. Conclude with `hP t (MvPolynomial.support_smul ht)`.
-/
theorem DegLT.smul {d : ℕ} {P : PX m n} (a : ℂ) (hP : DegLT d P) : DegLT d (a • P) := by
  intro t ht; exact hP t (MvPolynomial.support_smul ht)

/- English proof (translation)
Introduce `t ht` and use `lt_of_lt_of_le (hP t ht) h`.
-/
theorem DegLT.mono {d d' : ℕ} {P : PX m n} (hP : DegLT d P) (h : d ≤ d') : DegLT d' P :=
  fun t ht => lt_of_lt_of_le (hP t ht) h

/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using DegLT.zero d`. Consider the case `insert a t ha ih`. Rewrite using `[Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a t)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem DegLT.sum {d : ℕ} {ι : Type*} (t : Finset ι) (f : ι → PX m n) (h : ∀ i ∈ t, DegLT d (f i)) :
    DegLT d (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using DegLT.zero d
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a t)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Introduce `t ht`. Rewrite `ht` using `[MvPolynomial.support_X_mul]`. Take `⟨t', ht', rfl⟩` from `Finset.mem_map.mp ht`. Simplify using `only [addLeftEmbedding_apply, degree_add', Finsupp.degree_single]`. Use `hP t' ht'` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem DegLT.X_mul {d : ℕ} {P : PX m n} (j : Ix m n) (hP : DegLT d P) : DegLT (d + 1) (X j * P) := by
  intro t ht
  rw [MvPolynomial.support_X_mul] at ht
  obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
  simp only [addLeftEmbedding_apply, degree_add', Finsupp.degree_single]
  have := hP t' ht'
  omega

/- English proof (translation)
Introduce `t ht`. Rewrite `ht` using `[P.as_sum, map_sum]`. Take `⟨s, hs, hts⟩` from `Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)`. Rewrite `hts` using `[pderiv_monomial]`. Establish `ht'` using `MvPolynomial.support_monomial_subset hts`.

Rewrite `ht'` using `[Finset.mem_singleton]`. Substitute `ht'` using the available equality. Use `lt_of_le_of_lt ?_ (hP s hs)` and prove the remaining obligations. Simplify using `only [Finsupp.degree_eq_sum]`. Conclude with `Finset.sum_le_sum fun i _ => tsub_le_self`.
-/
theorem DegLT.pderiv {d : ℕ} {P : PX m n} (k : Ix m n) (hP : DegLT d P) : DegLT d (pderiv k P) := by
  classical
  intro t ht
  rw [P.as_sum, map_sum] at ht
  obtain ⟨s, hs, hts⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum ht)
  rw [pderiv_monomial] at hts
  have ht' := MvPolynomial.support_monomial_subset hts
  rw [Finset.mem_singleton] at ht'
  subst ht'
  refine lt_of_le_of_lt ?_ (hP s hs)
  simp only [Finsupp.degree_eq_sum]
  exact Finset.sum_le_sum fun i _ => tsub_le_self

def Sm (c : ℝ) (s : Ix m n →₀ ℕ) : PX m n := monomial (Finsupp.mapDomain flp s) ((2 * c : ℂ) ^ s.degree)

def err (c : ℝ) (s : Ix m n →₀ ℕ) : PX m n := fockMono c s - Sm c s

/- English proof (translation)
Simplify using `only [Sm, Finsupp.mapDomain_add, Finsupp.mapDomain_single, degree_add', Finsupp.degree_single, pow_succ]`. Rewrite using `[add_comm (Finsupp.mapDomain flp s), monomial_single_add, pow_one, ← mul_smul_comm, smul_monomial, smul_eq_mul, mul_comm (2 * (c : ℂ))]`.
-/
theorem Sm_succ (c : ℝ) (s : Ix m n →₀ ℕ) (k : Ix m n) :
    Sm c (s + Finsupp.single k 1) = (2 * c : ℂ) • (X (flp k) * Sm c s) := by
  simp only [Sm, Finsupp.mapDomain_add, Finsupp.mapDomain_single, degree_add', Finsupp.degree_single, pow_succ]
  rw [add_comm (Finsupp.mapDomain flp s), monomial_single_add, pow_one, ← mul_smul_comm, smul_monomial, smul_eq_mul,
    mul_comm (2 * (c : ℂ))]

/- English proof (translation)
Introduce `t ht`. Use `MvPolynomial.support_monomial_subset ht` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Substitute `this` using the available equality. Rewrite using `[degree_mapDomain]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem Sm_deg (c : ℝ) (s : Ix m n →₀ ℕ) : DegLT (s.degree + 1) (Sm c s) := by
  intro t ht
  have := MvPolynomial.support_monomial_subset ht
  rw [Finset.mem_singleton] at this
  subst this
  rw [degree_mapDomain]
  omega

/- English proof (translation)
Simplify using `[fockMono]`.
-/
theorem fockMono_zero (c : ℝ) : fockMono (m := m) (n := n) c 0 = 1 := by
  simp [fockMono]

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `s hs`. Establish `: s = 0` using `(Finsupp.degree_eq_zero_iff s).mp hs`.

Substitute `this` using the available equality. Simplify using `[err, Sm, fockMono_zero, DegLT.zero]`. Consider the case `succ d ih`. Introduce `s hs`. Establish `hs0 : s ≠ 0`.

Introduce `h`. Substitute `h` using the available equality. Simplify using `at hs`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, s k ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hs0 (Finsupp.ext h)`. Establish `hle : Finsupp.single k 1 ≤ s`. Introduce `i`. Distinguish the cases in `hi : i = k`.

Substitute `hi` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[Finsupp.single_apply, Ne.symm hi]`. Use `set s' := s - Finsupp.single k 1 with hs'`.

Establish `hsplit : s = s' + Finsupp.single k 1` using `(tsub_add_cancel_of_le hle).symm`. Establish `hd' : s'.degree = d`. Use `degree_add' s' (Finsupp.single k 1)` as an intermediate fact. Rewrite `this` using `[← hsplit, Finsupp.degree_single]`. Use linear arithmetic over natural numbers and integers.

Establish `hrec : fockMono c s = cr c k (fockMono c s')`. Rewrite using `[← fock_monomial, ← fock_monomial, hsplit, add_comm, monomial_single_add, pow_one, fock_X_mul]`. Establish `e : err c s = (2 * c : ℂ) • (X (flp k) * err c s') - pderiv k (Sm c s' + err c s')`. Rewrite using `[err, hrec, cr_apply, hsplit, Sm_succ, err]`. Simplify using `only [sub_add_cancel, mul_sub, smul_sub]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Use `DegLT.sub (DegLT.smul _ (DegLT.X_mul _ (ih s' hd'))) (DegLT.pderiv _ (DegLT.add ?_ ((ih s' hd').mono (by omega))))` and prove the remaining obligations. Use `Sm_deg c s'` as an intermediate fact. Rewrite `this` using `[hd']`. Then use the resulting hypothesis.
-/
theorem err_deg (c : ℝ) : ∀ d : ℕ, ∀ s : Ix m n →₀ ℕ, s.degree = d → DegLT d (err c s) := by
  intro d
  induction d with
  | zero =>
    intro s hs
    have : s = 0 := (Finsupp.degree_eq_zero_iff s).mp hs
    subst this
    simp [err, Sm, fockMono_zero, DegLT.zero]
  | succ d ih =>
    intro s hs
    have hs0 : s ≠ 0 := by
      intro h; subst h; simp at hs
    obtain ⟨k, hk⟩ : ∃ k, s k ≠ 0 := by
      by_contra h; push_neg at h; exact hs0 (Finsupp.ext h)
    have hle : Finsupp.single k 1 ≤ s := by
      intro i
      by_cases hi : i = k
      · subst hi; simp; omega
      · simp [Finsupp.single_apply, Ne.symm hi]
    set s' := s - Finsupp.single k 1 with hs'
    have hsplit : s = s' + Finsupp.single k 1 := (tsub_add_cancel_of_le hle).symm
    have hd' : s'.degree = d := by
      have := degree_add' s' (Finsupp.single k 1)
      rw [← hsplit, Finsupp.degree_single] at this
      omega
    have hrec : fockMono c s = cr c k (fockMono c s') := by
      rw [← fock_monomial, ← fock_monomial, hsplit, add_comm, monomial_single_add, pow_one, fock_X_mul]
    have e : err c s = (2 * c : ℂ) • (X (flp k) * err c s') - pderiv k (Sm c s' + err c s') := by
      rw [err, hrec, cr_apply, hsplit, Sm_succ, err]
      simp only [sub_add_cancel, mul_sub, smul_sub]
      abel
    rw [e]
    refine DegLT.sub (DegLT.smul _ (DegLT.X_mul _ (ih s' hd'))) (DegLT.pderiv _ (DegLT.add ?_ ((ih s' hd').mono (by omega))))
    have := Sm_deg c s'
    rwa [hd'] at this

/- English proof (translation)
Simplify using `only [fock, err, add_sub_cancel]`.
-/
theorem fock_decomp (c : ℝ) (p : PX m n) :
    fock c p = ∑ s ∈ p.support, p.coeff s • (Sm c s + err c s) := by
  simp only [fock, err, add_sub_cancel]

/- English proof (translation)
Introduce `p q hpq`. Rewrite using `[← sub_eq_zero]`. Establish `h0 : fock c (p - q) = 0` using `by rw [fock_sub, hpq, sub_self]`. Use `set r := p - q`. Assume the negation of the conclusion as `hr`.

Establish `hne : r.support.Nonempty` using `MvPolynomial.support_nonempty.mpr hr`. Take `⟨s0, hs0, hmax⟩` from `Finset.exists_max_image r.support Finsupp.degree hne`. Establish `key` using `congrArg (MvPolynomial.coeff (Finsupp.mapDomain flp s0)) h0`. Rewrite `key` using `[fock_decomp, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, Finset.sum_eq_single s0]`. Rewrite `key` using `[MvPolynomial.coeff_smul, MvPolynomial.coeff_add, Sm, MvPolynomial.coeff_monomial, if_pos rfl]`.

Establish `herr : MvPolynomial.coeff (Finsupp.mapDomain flp s0) (err c s0) = 0`. Assume the negation of the conclusion as `hne'`. Use `err_deg c _ s0 rfl _ (MvPolynomial.mem_support_iff.mpr hne')` as an intermediate fact. Rewrite `this` using `[degree_mapDomain]`. Conclude with `lt_irrefl _ this`.

Rewrite `key` using `[herr, add_zero, smul_eq_mul]`. Establish `hc' : (2 * c : ℂ) ≠ 0`. Establish `: (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`. Conclude with `mul_ne_zero two_ne_zero this`. Conclude with `(mul_ne_zero (MvPolynomial.mem_support_iff.mp hs0) (pow_ne_zero _ hc')) key`.

Introduce `s hs hne'`. Rewrite using `[MvPolynomial.coeff_smul, MvPolynomial.coeff_add, Sm, MvPolynomial.coeff_monomial]`. Establish `h1 : Finsupp.mapDomain flp s ≠ Finsupp.mapDomain flp s0` using `fun h => hne' (Finsupp.mapDomain_injective flp_injective h)`. Rewrite using `[if_neg h1]`. Establish `herr : MvPolynomial.coeff (Finsupp.mapDomain flp s0) (err c s) = 0`.

Assume the negation of the conclusion as `hne''`. Use `err_deg c _ s rfl _ (MvPolynomial.mem_support_iff.mpr hne'')` as an intermediate fact. Rewrite `this` using `[degree_mapDomain]`. Conclude with `absurd (hmax s hs) (not_le.mpr this)`. Rewrite using `[herr, add_zero, smul_zero]`.

Introduce `h`. Conclude with `absurd hs0 h`.
-/
theorem fock_injective (c : ℝ) (hc : 0 < c) : Function.Injective (fock (m := m) (n := n) c) := by
  classical
  intro p q hpq
  rw [← sub_eq_zero]
  have h0 : fock c (p - q) = 0 := by rw [fock_sub, hpq, sub_self]
  set r := p - q
  by_contra hr
  have hne : r.support.Nonempty := MvPolynomial.support_nonempty.mpr hr
  obtain ⟨s0, hs0, hmax⟩ := Finset.exists_max_image r.support Finsupp.degree hne
  have key := congrArg (MvPolynomial.coeff (Finsupp.mapDomain flp s0)) h0
  rw [fock_decomp, MvPolynomial.coeff_zero, MvPolynomial.coeff_sum, Finset.sum_eq_single s0] at key
  · rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_add, Sm, MvPolynomial.coeff_monomial, if_pos rfl] at key
    have herr : MvPolynomial.coeff (Finsupp.mapDomain flp s0) (err c s0) = 0 := by
      by_contra hne'
      have := err_deg c _ s0 rfl _ (MvPolynomial.mem_support_iff.mpr hne')
      rw [degree_mapDomain] at this
      exact lt_irrefl _ this
    rw [herr, add_zero, smul_eq_mul] at key
    have hc' : (2 * c : ℂ) ≠ 0 := by
      have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
      exact mul_ne_zero two_ne_zero this
    exact (mul_ne_zero (MvPolynomial.mem_support_iff.mp hs0) (pow_ne_zero _ hc')) key
  · intro s hs hne'
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_add, Sm, MvPolynomial.coeff_monomial]
    have h1 : Finsupp.mapDomain flp s ≠ Finsupp.mapDomain flp s0 :=
      fun h => hne' (Finsupp.mapDomain_injective flp_injective h)
    rw [if_neg h1]
    have herr : MvPolynomial.coeff (Finsupp.mapDomain flp s0) (err c s) = 0 := by
      by_contra hne''
      have := err_deg c _ s rfl _ (MvPolynomial.mem_support_iff.mpr hne'')
      rw [degree_mapDomain] at this
      exact absurd (hmax s hs) (not_le.mpr this)
    rw [herr, add_zero, smul_zero]
  · intro h; exact absurd hs0 h

/- English proof (translation)
Establish `hc' : (2 * c : ℂ) ≠ 0`. Establish `: (c : ℂ) ≠ 0` using `by exact_mod_cast hc.ne'`. Conclude with `mul_ne_zero two_ne_zero this`. Introduce `d`. Proceed by induction on `d with`.

Consider the case `zero`. Introduce `Q hQ`. Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[fock_zero]`. Use `symm`.

Assume the negation of the conclusion as `hne`. Take `⟨t, ht⟩` from `MvPolynomial.support_nonempty.mpr hne`. Conclude with `Nat.not_lt_zero _ (hQ t ht)`. Consider the case `succ d ih`. Introduce `Q hQ`.

Use `set p0 : PX m n := ∑ t ∈ Q.support, (Q.coeff t / (2 * c : ℂ) ^ t.degree) • monomial (Finsupp.mapDomain flp t) 1`. Establish `hp0 : fock c p0 = (∑ t ∈ Q.support, monomial t (Q.coeff t)) + ∑ t ∈ Q.support, (Q.coeff t / (2 * c : ℂ) ^ t.degree) • err c (Finsupp.mapDomain flp t)`. Rewrite using `[fock_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[fock_smul, fock_monomial, err, smul_sub, Sm, mapDomain_flp_flp, degree_mapDomain, smul_monomial, smul_eq_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc')]`.

Normalize the expressions using the abelian group laws. Establish `hR : DegLT d (∑ t ∈ Q.support, (Q.coeff t / (2 * c : ℂ) ^ t.degree) • err c (Finsupp.mapDomain flp t))`. Use `DegLT.sum _ _ fun t ht => DegLT.smul _ ?_` and prove the remaining obligations. Establish `h1` using `err_deg c _ (Finsupp.mapDomain flp t) rfl`. Rewrite `h1` using `[degree_mapDomain]`.

Conclude with `h1.mono (by have := hQ t ht; omega)`. Take `⟨p1, hp1⟩` from `ih _ hR`. Conclude with `⟨p0 - p1, by rw [fock_sub, hp0, hp1, add_sub_cancel_right]; exact Q.as_sum.symm⟩`.
-/
theorem fock_surj_deg (c : ℝ) (hc : 0 < c) :
    ∀ d : ℕ, ∀ Q : PX m n, DegLT d Q → ∃ p, fock c p = Q := by
  classical
  have hc' : (2 * c : ℂ) ≠ 0 := by
    have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    exact mul_ne_zero two_ne_zero this
  intro d
  induction d with
  | zero =>
    intro Q hQ
    refine ⟨0, ?_⟩
    rw [fock_zero]
    symm
    by_contra hne
    obtain ⟨t, ht⟩ := MvPolynomial.support_nonempty.mpr hne
    exact Nat.not_lt_zero _ (hQ t ht)
  | succ d ih =>
    intro Q hQ
    set p0 : PX m n := ∑ t ∈ Q.support, (Q.coeff t / (2 * c : ℂ) ^ t.degree) • monomial (Finsupp.mapDomain flp t) 1
    have hp0 : fock c p0 = (∑ t ∈ Q.support, monomial t (Q.coeff t)) + ∑ t ∈ Q.support,
        (Q.coeff t / (2 * c : ℂ) ^ t.degree) • err c (Finsupp.mapDomain flp t) := by
      rw [fock_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [fock_smul, fock_monomial, err, smul_sub, Sm, mapDomain_flp_flp, degree_mapDomain, smul_monomial,
        smul_eq_mul, div_mul_cancel₀ _ (pow_ne_zero _ hc')]
      abel
    have hR : DegLT d (∑ t ∈ Q.support,
        (Q.coeff t / (2 * c : ℂ) ^ t.degree) • err c (Finsupp.mapDomain flp t)) := by
      refine DegLT.sum _ _ fun t ht => DegLT.smul _ ?_
      have h1 := err_deg c _ (Finsupp.mapDomain flp t) rfl
      rw [degree_mapDomain] at h1
      exact h1.mono (by have := hQ t ht; omega)
    obtain ⟨p1, hp1⟩ := ih _ hR
    exact ⟨p0 - p1, by rw [fock_sub, hp0, hp1, add_sub_cancel_right]; exact Q.as_sum.symm⟩

/- English proof (translation)
Introduce `Q`. Use `fock_surj_deg c hc (Q.support.sup Finsupp.degree + 1) Q fun t ht => ?_` and prove the remaining obligations. Conclude with `Nat.lt_succ_of_le (Finset.le_sup ht)`.
-/
theorem fock_surjective (c : ℝ) (hc : 0 < c) : Function.Surjective (fock (m := m) (n := n) c) := by
  intro Q
  refine fock_surj_deg c hc (Q.support.sup Finsupp.degree + 1) Q fun t ht => ?_
  exact Nat.lt_succ_of_le (Finset.le_sup ht)

/- English proof (translation)
Introduce `m n c hc`. Conclude with `⟨⟨fock_add c, fun a p => fock_smul c a p⟩, ⟨fock_injective c hc, fock_surjective c hc⟩, fun k p => fock_X_mul c k p⟩`.
-/
theorem fockBasic : FockBasic := by
  intro m n c hc
  exact ⟨⟨fock_add c, fun a p => fock_smul c a p⟩, ⟨fock_injective c hc, fock_surjective c hc⟩, fun k p => fock_X_mul c k p⟩

end PositivityTheory.Rg.Sw.LC.Basic

namespace PositivityTheory.Rg.Sw.LC

/- English proof (translation)
The claim follows from `Basic.fockBasic`.
-/
theorem fockBasic : FockBasic := Basic.fockBasic

end PositivityTheory.Rg.Sw.LC
