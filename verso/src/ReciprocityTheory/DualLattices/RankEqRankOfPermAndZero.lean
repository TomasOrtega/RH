import ReciprocityTheory.DualLattices.EmbeddingSeparatingGroupStatement
import ReciprocityTheory.DualLattices.UnramifiedCokernelLengthOfLengthEigenLengthProduct
import ReciprocityTheory.DualLattices.IsLocalOfIntegers
import ReciprocityTheory.DualLattices.RankMapLeRank

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

section Rank

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.map_apply, Matrix.smul_apply]`.
-/
private lemma map_smul_hom {n S T : Type} [Fintype n] [CommRing S] [CommRing T] (f : S →+* T)
    (r : S) (A : Matrix n n S) : (r • A).map f = f r • A.map f := by
  ext i j
  simp [Matrix.map_apply, Matrix.smul_apply]

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

/- English proof (translation)
Use `haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hS.integers.hom_inj`. Establish `hcp : cp ≠ 0`. Introduce `h`. Establish `hv` using `hS.cp_val`. Establish `hp2` using `(Fact.out : p.Prime).two_le`.

Rewrite `hv` using `[h, map_zero, map_zero, zero_pow (by omega)]`. Conclude with `hS.p_ne hv.symm`. Establish `hE : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det`. Rewrite using `[← RingHom.mapMatrix_apply, ← RingHom.map_det]`. Conclude with `H.isUnit_det_E.map _`.

Establish `h1 : U.εT (U.cj i) = 0`. Establish `he` using `εT_E hS H U i`. Rewrite `he` using `[h0, Matrix.transpose_zero, Matrix.zero_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcc : U.cj (U.cj i) = i`.

Assume the negation of the conclusion as `hne`. Take `⟨a, ha⟩` from `U.distinct _ _ hne`. Establish `e : U.sg (U.cj (U.cj i)) a = U.sg i a` using `by rw [U.conj, U.conj, hS.invol]`. Rewrite `ha` using `[e, sub_self, map_zero, map_zero]`. Conclude with `zero_ne_one ha`.

Establish `hx : ∀ x : Fin g → R, (U.εL (U.cj (U.cj i)))ᵀ *ᵥ x = 0`. Introduce `x`. Set `y : LinearMap.range (Matrix.mulVecLin (U.εL (U.cj (U.cj i)))ᵀ)` to `⟨(U.εL (U.cj (U.cj i)))ᵀ *ᵥ x, ⟨x, rfl⟩⟩`. Establish `hk` using `up_kill hS H U (U.cj i) (Submodule.Quotient.mk y)`. Rewrite `hk` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, h1]`.

Simplify using `only [Matrix.mulVecLin_zero, LinearMap.range_zero, Submodule.map_bot, Submodule.mem_bot] at hk`. Establish `hk' : cp • ((U.εL (U.cj (U.cj i)))ᵀ *ᵥ x) = 0`. Simplify `hk` using `[y]`. Conclude with `(smul_eq_zero.mp hk').resolve_left hcp`. Rewrite `hx` using `[hcc]`.

Establish `hT : (U.εL i)ᵀ = 0`. Use extensionality with `a b`. Use `congrFun (hx (Pi.single b 1)) a` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Pi.single_apply]`. Conclude with `Matrix.transpose_eq_zero.mp hT`.
-/
private lemma εL_eq_zero (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (h0 : U.εT i = 0) : U.εL i = 0 := by
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hS.integers.hom_inj
  have hcp : cp ≠ 0 := by
    intro h
    have hv := hS.cp_val
    have hp2 := (Fact.out : p.Prime).two_le
    rw [h, map_zero, map_zero, zero_pow (by omega)] at hv
    exact hS.p_ne hv.symm
  have hE : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact H.isUnit_det_E.map _
  have h1 : U.εT (U.cj i) = 0 := by
    have he := εT_E hS H U i
    rw [h0, Matrix.transpose_zero, Matrix.zero_mul] at he
    calc U.εT (U.cj i) = ((H.E.map (algebraMap ℤ_[p] R))⁻¹ * H.E.map (algebraMap ℤ_[p] R)) *
          U.εT (U.cj i) := by rw [Matrix.nonsing_inv_mul _ hE, Matrix.one_mul]
      _ = (H.E.map (algebraMap ℤ_[p] R))⁻¹ * (H.E.map (algebraMap ℤ_[p] R) * U.εT (U.cj i)) :=
          Matrix.mul_assoc _ _ _
      _ = 0 := by rw [← he, Matrix.mul_zero]
  have hcc : U.cj (U.cj i) = i := by
    by_contra hne
    obtain ⟨a, ha⟩ := U.distinct _ _ hne
    have e : U.sg (U.cj (U.cj i)) a = U.sg i a := by rw [U.conj, U.conj, hS.invol]
    rw [e, sub_self, map_zero, map_zero] at ha
    exact zero_ne_one ha
  have hx : ∀ x : Fin g → R, (U.εL (U.cj (U.cj i)))ᵀ *ᵥ x = 0 := by
    intro x
    let y : LinearMap.range (Matrix.mulVecLin (U.εL (U.cj (U.cj i)))ᵀ) :=
      ⟨(U.εL (U.cj (U.cj i)))ᵀ *ᵥ x, ⟨x, rfl⟩⟩
    have hk := up_kill hS H U (U.cj i) (Submodule.Quotient.mk y)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, h1] at hk
    simp only [Matrix.mulVecLin_zero, LinearMap.range_zero, Submodule.map_bot,
      Submodule.mem_bot] at hk
    have hk' : cp • ((U.εL (U.cj (U.cj i)))ᵀ *ᵥ x) = 0 := by
      simpa [y] using hk
    exact (smul_eq_zero.mp hk').resolve_left hcp
  rw [hcc] at hx
  have hT : (U.εL i)ᵀ = 0 := by
    ext a b
    have := congrFun (hx (Pi.single b 1)) a
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  exact Matrix.transpose_eq_zero.mp hT

/- English proof (translation)
Establish `h` using `εL_eq_zero hS H U i h0`. Take `⟨e⟩` from `U.rank i`. Use `haveI : Nontrivial R := (Function.Injective.isDomain (algebraMap R C) hS.integers.hom_inj).toNontrivial`. Assume the negation of the conclusion as `hr`. Establish `hall : ∀ y : LinearMap.range (Matrix.mulVecLin (U.εL i)), y = 0`.

Introduce and unpack `⟨y, x, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[h]`. Establish `hne : (Pi.single ⟨0, Nat.pos_of_ne_zero hr⟩ 1 : Fin (U.r i) → R) ≠ 0`. Introduce `hz`.

Use `congrFun hz ⟨0, Nat.pos_of_ne_zero hr⟩` as an intermediate fact. Simplify using `at this`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← e.apply_symm_apply (Pi.single _ 1), hall (e.symm _), map_zero]`.
-/
private lemma r_eq_zero (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (h0 : U.εT i = 0) : U.r i = 0 := by
  have h := εL_eq_zero hS H U i h0
  obtain ⟨e⟩ := U.rank i
  haveI : Nontrivial R :=
    (Function.Injective.isDomain (algebraMap R C) hS.integers.hom_inj).toNontrivial
  by_contra hr
  have hall : ∀ y : LinearMap.range (Matrix.mulVecLin (U.εL i)), y = 0 := by
    rintro ⟨y, x, rfl⟩
    apply Subtype.ext
    simp [h]
  have hne : (Pi.single ⟨0, Nat.pos_of_ne_zero hr⟩ 1 : Fin (U.r i) → R) ≠ 0 := by
    intro hz
    have := congrFun hz ⟨0, Nat.pos_of_ne_zero hr⟩
    simp at this
  apply hne
  rw [← e.apply_symm_apply (Pi.single _ 1), hall (e.symm _), map_zero]

/- English proof (translation)
Establish `hsum : (H.ρ a).map (algebraMap ℤ_[p] R) = ∑ i, U.sg i a • U.εT i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[U.εT_sum, Matrix.mul_one]`. Use `_ = ∑ i, U.sg i a • U.εT i := by`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => U.εT_eig a i`. Rewrite using `[hsum, Finset.mul_sum, Finset.sum_eq_single j]`. Rewrite using `[Matrix.mul_smul, U.εT_orth, if_pos rfl]`. Introduce `b _ hb`. Rewrite using `[Matrix.mul_smul, U.εT_orth, if_neg (Ne.symm hb), smul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.
-/
private lemma εT_eig_left {H : HodgeTateDatum p g v R O σ cp} (U : UnramData p g v R O σ cp H) (a : O)
    (j : Fin U.m) : U.εT j * (H.ρ a).map (algebraMap ℤ_[p] R) = U.sg j a • U.εT j := by
  have hsum : (H.ρ a).map (algebraMap ℤ_[p] R) = ∑ i, U.sg i a • U.εT i := by
    calc (H.ρ a).map (algebraMap ℤ_[p] R) = (H.ρ a).map (algebraMap ℤ_[p] R) * ∑ i, U.εT i := by
          rw [U.εT_sum, Matrix.mul_one]
      _ = ∑ i, U.sg i a • U.εT i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => U.εT_eig a i
  rw [hsum, Finset.mul_sum, Finset.sum_eq_single j]
  · rw [Matrix.mul_smul, U.εT_orth, if_pos rfl]
  · intro b _ hb
    rw [Matrix.mul_smul, U.εT_orth, if_neg (Ne.symm hb), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

section Local

variable [IsLocalRing R]

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Rewrite `hu` using `[hS.integers.isUnit_iff_valuation_eq_one]`. Conclude with `absurd hu (ne_of_lt hr)`.
-/
private lemma res_zero (hS : HodgeTateSetting p v R O σ cp) {r : R} (hr : v (algebraMap R C r) < 1) :
    IsLocalRing.residue R r = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  rw [hS.integers.isUnit_iff_valuation_eq_one] at hu
  exact absurd hu (ne_of_lt hr)

/- English proof (translation)
Rewrite using `[Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, hS.integers.isUnit_iff_valuation_eq_one]`. Conclude with `hr`.
-/
private lemma res_ne (hS : HodgeTateSetting p v R O σ cp) {r : R} (hr : v (algebraMap R C r) = 1) :
    IsLocalRing.residue R r ≠ 0 := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    not_not, hS.integers.isUnit_iff_valuation_eq_one]
  exact hr

/- English proof (translation)
Establish `hp` using `(Fact.out : p.Prime)`. Rewrite using `[CharP.charP_iff_prime_eq_zero hp, ← map_natCast (IsLocalRing.residue R)]`. Conclude with `res_zero hS hS.p_lt`.
-/
private lemma charP_res (hS : HodgeTateSetting p v R O σ cp) : CharP (IsLocalRing.ResidueField R) p := by
  have hp := (Fact.out : p.Prime)
  rw [CharP.charP_iff_prime_eq_zero hp, ← map_natCast (IsLocalRing.residue R)]
  exact res_zero hS hS.p_lt

/- English proof (translation)
Take `⟨c, hc⟩` from `Ideal.mem_span_singleton'.mp (PadicInt.appr_spec 1 z)`. Establish `hz : z = ((z.appr 1 : ℕ) : ℤ_[p]) + c * (p : ℤ_[p]) ^ 1`. Rewrite using `[hc]`. Expand and normalize the polynomial expressions, which then agree. Establish `hp0 : ((p : ℕ) : IsLocalRing.ResidueField R) = 0` using `CharP.cast_eq_zero _ p`.

Establish `key : IsLocalRing.residue R (algebraMap ℤ_[p] R z) = ((z.appr 1 : ℕ) : IsLocalRing.ResidueField R)`. Establish `e` using `congrArg (fun w => IsLocalRing.residue R (algebraMap ℤ_[p] R w)) hz`. Simplify using `only [map_add, map_mul, map_pow, map_natCast, hp0, pow_one, mul_zero, add_zero] at e`. Conclude with `e`. Rewrite using `[key, map_natCast]`.
-/
private lemma frob_fix [CharP (IsLocalRing.ResidueField R) p] (z : ℤ_[p]) :
    frobenius (IsLocalRing.ResidueField R) p (IsLocalRing.residue R (algebraMap ℤ_[p] R z)) =
      IsLocalRing.residue R (algebraMap ℤ_[p] R z) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec 1 z)
  have hz : z = ((z.appr 1 : ℕ) : ℤ_[p]) + c * (p : ℤ_[p]) ^ 1 := by
    rw [hc]
    ring
  have hp0 : ((p : ℕ) : IsLocalRing.ResidueField R) = 0 := CharP.cast_eq_zero _ p
  have key : IsLocalRing.residue R (algebraMap ℤ_[p] R z) =
      ((z.appr 1 : ℕ) : IsLocalRing.ResidueField R) := by
    have e := congrArg (fun w => IsLocalRing.residue R (algebraMap ℤ_[p] R w)) hz
    simp only [map_add, map_mul, map_pow, map_natCast, hp0, pow_one, mul_zero, add_zero] at e
    exact e
  rw [key, map_natCast]

/- English proof (translation)
Establish `hA : ∀ a j, (U.εT j).map (IsLocalRing.residue R) * ((H.ρ a).map (algebraMap ℤ_[p] R)).map (IsLocalRing.residue R) = IsLocalRing.residue R (U.sg j a) • (U.εT j).map (IsLocalRing.residue R)`. Introduce `a j`. Rewrite using `[← Matrix.map_mul, εT_eig_left U a j, map_smul_hom]`. Establish `hB : ∀ a j, ((H.ρ a).map (algebraMap ℤ_[p] R)).map (IsLocalRing.residue R) * (U.εT j).map (IsLocalRing.residue R) = IsLocalRing.residue R (U.sg j a) • (U.εT j).map (IsLocalRing.residue R)`. Introduce `a j`.

Rewrite using `[← Matrix.map_mul, U.εT_eig a j, map_smul_hom]`. Establish `hC : ∀ a, (((H.ρ a).map (algebraMap ℤ_[p] R)).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) = ((H.ρ a).map (algebraMap ℤ_[p] R)).map (IsLocalRing.residue R)`. Introduce `a`. Use extensionality with `x y`. Simplify using `only [Matrix.map_apply]`.

Conclude with `frob_fix _`. Establish `hsgp : ∀ a j, frobenius (IsLocalRing.ResidueField R) p (IsLocalRing.residue R (U.sg j a)) = IsLocalRing.residue R (U.sg (U.φ j) a)`. Introduce `a j`. Rewrite using `[frobenius_def, ← map_pow]`. Establish `h` using `res_zero hS (U.frob j a)`.

Rewrite `h` using `[map_sub, sub_eq_zero]`. Conclude with `h.symm`. Establish `hD : ∀ a j, ((H.ρ a).map (algebraMap ℤ_[p] R)).map (IsLocalRing.residue R) * ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) = IsLocalRing.residue R (U.sg (U.φ j) a) • ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.Residue …`. Introduce `a j`. Rewrite using `[← hC a, ← Matrix.map_mul, hB a j, map_smul_hom, hsgp]`.

Establish `hE1 : ∑ j, ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) = 1`. Establish `e : ∑ j, ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) = (frobenius (IsLocalRing.ResidueField R) p).mapMatrix ((IsLocalRing.residue R).mapMatrix (∑ j, U.εT j))`. Simplify using `only [map_sum, RingHom.mapMatrix_apply]`. Rewrite using `[e, U.εT_sum, map_one, map_one]`. Establish `hF : ∀ j, j ≠ i → (U.εT (U.φ i)).map (IsLocalRing.residue R) * ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) = 0`.

Introduce `j hj`. Establish `hφ : U.φ i ≠ U.φ j` using `fun h => hj (U.φ.injective h).symm`. Take `⟨a, ha⟩` from `U.distinct _ _ hφ`. Establish `h1` using `res_ne hS ha`. Rewrite `h1` using `[map_sub]`.

Establish `key : (IsLocalRing.residue R (U.sg (U.φ i) a) - IsLocalRing.residue R (U.sg (U.φ j) a)) • ((U.εT (U.φ i)).map (IsLocalRing.residue R) * ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p)) = 0`. Rewrite using `[sub_smul, sub_eq_zero, ← Matrix.smul_mul, ← hA a (U.φ i), Matrix.mul_assoc, hD a j, Matrix.mul_smul]`. Conclude with `(smul_eq_zero.mp key).resolve_left h1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hE1, Matrix.mul_one]`.

Use `_ = ∑ j, (U.εT (U.φ i)).map (IsLocalRing.residue R) * ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) := Finset.mul_sum _ _ _`. Use `_ = _ := Finset.sum_eq_single i (fun j _ hj => hF j hj) (fun h => absurd (Finset.mem_univ i) h)`.
-/
private lemma frob_block (hS : HodgeTateSetting p v R O σ cp) [CharP (IsLocalRing.ResidueField R) p]
    {H : HodgeTateDatum p g v R O σ cp} (U : UnramData p g v R O σ cp H) (i : Fin U.m) :
    (U.εT (U.φ i)).map (IsLocalRing.residue R) = (U.εT (U.φ i)).map (IsLocalRing.residue R) *
      ((U.εT i).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) := by
  classical
  have hA : ∀ a j, (U.εT j).map (IsLocalRing.residue R) *
      ((H.ρ a).map (algebraMap ℤ_[p] R)).map (IsLocalRing.residue R) =
      IsLocalRing.residue R (U.sg j a) • (U.εT j).map (IsLocalRing.residue R) := by
    intro a j
    rw [← Matrix.map_mul, εT_eig_left U a j, map_smul_hom]
  have hB : ∀ a j, ((H.ρ a).map (algebraMap ℤ_[p] R)).map (IsLocalRing.residue R) *
      (U.εT j).map (IsLocalRing.residue R) =
      IsLocalRing.residue R (U.sg j a) • (U.εT j).map (IsLocalRing.residue R) := by
    intro a j
    rw [← Matrix.map_mul, U.εT_eig a j, map_smul_hom]
  have hC : ∀ a, (((H.ρ a).map (algebraMap ℤ_[p] R)).map (IsLocalRing.residue R)).map
      (frobenius (IsLocalRing.ResidueField R) p) =
      ((H.ρ a).map (algebraMap ℤ_[p] R)).map (IsLocalRing.residue R) := by
    intro a
    ext x y
    simp only [Matrix.map_apply]
    exact frob_fix _
  have hsgp : ∀ a j, frobenius (IsLocalRing.ResidueField R) p (IsLocalRing.residue R (U.sg j a)) =
      IsLocalRing.residue R (U.sg (U.φ j) a) := by
    intro a j
    rw [frobenius_def, ← map_pow]
    have h := res_zero hS (U.frob j a)
    rw [map_sub, sub_eq_zero] at h
    exact h.symm
  have hD : ∀ a j, ((H.ρ a).map (algebraMap ℤ_[p] R)).map (IsLocalRing.residue R) *
      ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) =
      IsLocalRing.residue R (U.sg (U.φ j) a) •
        ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) := by
    intro a j
    rw [← hC a, ← Matrix.map_mul, hB a j, map_smul_hom, hsgp]
  have hE1 : ∑ j, ((U.εT j).map (IsLocalRing.residue R)).map
      (frobenius (IsLocalRing.ResidueField R) p) = 1 := by
    have e : ∑ j, ((U.εT j).map (IsLocalRing.residue R)).map
        (frobenius (IsLocalRing.ResidueField R) p) =
        (frobenius (IsLocalRing.ResidueField R) p).mapMatrix
          ((IsLocalRing.residue R).mapMatrix (∑ j, U.εT j)) := by
      simp only [map_sum, RingHom.mapMatrix_apply]
    rw [e, U.εT_sum, map_one, map_one]
  have hF : ∀ j, j ≠ i → (U.εT (U.φ i)).map (IsLocalRing.residue R) *
      ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) = 0 := by
    intro j hj
    have hφ : U.φ i ≠ U.φ j := fun h => hj (U.φ.injective h).symm
    obtain ⟨a, ha⟩ := U.distinct _ _ hφ
    have h1 := res_ne hS ha
    rw [map_sub] at h1
    have key : (IsLocalRing.residue R (U.sg (U.φ i) a) - IsLocalRing.residue R (U.sg (U.φ j) a)) •
        ((U.εT (U.φ i)).map (IsLocalRing.residue R) *
          ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p)) = 0 := by
      rw [sub_smul, sub_eq_zero, ← Matrix.smul_mul, ← hA a (U.φ i), Matrix.mul_assoc, hD a j,
        Matrix.mul_smul]
    exact (smul_eq_zero.mp key).resolve_left h1
  calc (U.εT (U.φ i)).map (IsLocalRing.residue R) = (U.εT (U.φ i)).map (IsLocalRing.residue R) *
        ∑ j, ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) := by
        rw [hE1, Matrix.mul_one]
    _ = ∑ j, (U.εT (U.φ i)).map (IsLocalRing.residue R) *
        ((U.εT j).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p) :=
        Finset.mul_sum _ _ _
    _ = _ := Finset.sum_eq_single i (fun j _ hj => hF j hj) (fun h => absurd (Finset.mem_univ i) h)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← frob_block hS U i]`. Use `_ ≤ (((U.εT i).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p)).rank := Matrix.rank_mul_le_right _ _`. Use `_ ≤ Module.finrank (IsLocalRing.ResidueField R) (LinearMap.range ((U.εT i).map (IsLocalRing.residue R)).mulVecLin) := RankA.rank_map_le _ _`. Use `_ = ((U.εT i).map (IsLocalRing.residue R)).rank := rfl`.
-/
private lemma rank_phi_le (hS : HodgeTateSetting p v R O σ cp) [CharP (IsLocalRing.ResidueField R) p]
    {H : HodgeTateDatum p g v R O σ cp} (U : UnramData p g v R O σ cp H) (i : Fin U.m) :
    ((U.εT (U.φ i)).map (IsLocalRing.residue R)).rank ≤
      ((U.εT i).map (IsLocalRing.residue R)).rank := by
  calc ((U.εT (U.φ i)).map (IsLocalRing.residue R)).rank =
        ((U.εT (U.φ i)).map (IsLocalRing.residue R) *
          ((U.εT i).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p)).rank := by
        rw [← frob_block hS U i]
    _ ≤ (((U.εT i).map (IsLocalRing.residue R)).map (frobenius (IsLocalRing.ResidueField R) p)).rank :=
        Matrix.rank_mul_le_right _ _
    _ ≤ Module.finrank (IsLocalRing.ResidueField R)
          (LinearMap.range ((U.εT i).map (IsLocalRing.residue R)).mulVecLin) :=
        RankA.rank_map_le _ _
    _ = ((U.εT i).map (IsLocalRing.residue R)).rank := rfl

end Local

end Rank

/- English proof (translation)
Introduce `p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U`. Use `haveI : IsLocalRing R := isLocal_of_integers hS.integers`. Use `haveI : CharP (IsLocalRing.ResidueField R) p := charP_res hS`. Establish `hidem : ∀ i, U.εT i * U.εT i = U.εT i` using `fun i => by rw [U.εT_orth, if_pos rfl]`. Use `haveI hfree : ∀ i, Module.Free R (LinearMap.range (U.εT i).mulVecLin) := fun i => (RankA.free_range_idem _ (hidem i)).1`.

Use `haveI hfin : ∀ i, Module.Finite R (LinearMap.range (U.εT i).mulVecLin) := fun i => (RankA.free_range_idem _ (hidem i)).2`. Establish `hsn : ∀ i ∈ Finset.univ, ((U.εT i).map (IsLocalRing.residue R)).rank ≤ Module.finrank R (LinearMap.range (U.εT i).mulVecLin)` using `fun i _ => RankA.rank_map_le _ _`. Establish `hsumn : ∑ i, Module.finrank R (LinearMap.range (U.εT i).mulVecLin) = Fintype.card (Ix g)` using `RankA.sum_finrank U.εT U.εT_orth U.εT_sum`. Establish `hsums : ∑ i, ((U.εT i).map (IsLocalRing.residue R)).rank = Fintype.card (Ix g)`. Establish `horth : ∀ i j, (U.εT i).map (IsLocalRing.residue R) * (U.εT j).map (IsLocalRing.residue R) = if i = j then (U.εT i).map (IsLocalRing.residue R) else 0`.

Introduce `i j`. Rewrite using `[← Matrix.map_mul, U.εT_orth]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hs1 : ∑ i, (U.εT i).map (IsLocalRing.residue R) = 1`. Establish `e : ∑ i, (U.εT i).map (IsLocalRing.residue R) = (IsLocalRing.residue R).mapMatrix (∑ i, U.εT i)`.

Simplify using `only [map_sum, RingHom.mapMatrix_apply]`. Rewrite using `[e, U.εT_sum, map_one]`. Conclude with `RankA.sum_finrank (fun i => (U.εT i).map (IsLocalRing.residue R)) horth hs1`. Establish `hseq : ∀ i, ((U.εT i).map (IsLocalRing.residue R)).rank = Module.finrank R (LinearMap.range (U.εT i).mulVecLin)`. Establish `h` using `(Finset.sum_eq_sum_iff_of_le hsn).mp (hsums.trans hsumn.symm)`.

Conclude with `fun i => h i (Finset.mem_univ i)`. Establish `hphi : ∀ i, ((U.εT (U.φ i)).map (IsLocalRing.residue R)).rank = ((U.εT i).map (IsLocalRing.residue R)).rank`. Establish `hle : ∀ i ∈ Finset.univ, ((U.εT (U.φ i)).map (IsLocalRing.residue R)).rank ≤ ((U.εT i).map (IsLocalRing.residue R)).rank` using `fun i _ => rank_phi_le hS U i`. Establish `hs : ∑ i, ((U.εT (U.φ i)).map (IsLocalRing.residue R)).rank = ∑ i, ((U.εT i).map (IsLocalRing.residue R)).rank` using `Equiv.sum_comp U.φ (fun i => ((U.εT i).map (IsLocalRing.residue R)).rank)`. Conclude with `fun i => (Finset.sum_eq_sum_iff_of_le hle).mp hs i (Finset.mem_univ i)`.

Use `⟨fun i => ⟨Module.finrank R (LinearMap.range (U.εT i).mulVecLin), ?_, ?_⟩, fun i h0 => r_eq_zero hS H U i h0⟩` and prove the remaining obligations. Conclude with `⟨(Module.finBasisOfFinrankEq R _ rfl).equivFun⟩`. Establish `hn : Module.finrank R (LinearMap.range (U.εT (U.φ i)).mulVecLin) = Module.finrank R (LinearMap.range (U.εT i).mulVecLin)`. Rewrite using `[← hseq, ← hseq, hphi]`. Conclude with `⟨(Module.finBasisOfFinrankEq R _ hn).equivFun⟩`.
-/
theorem rank_eq_rank_of_perm_and_zero : EigenRankStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H U
  classical
  haveI : IsLocalRing R := isLocal_of_integers hS.integers
  haveI : CharP (IsLocalRing.ResidueField R) p := charP_res hS
  have hidem : ∀ i, U.εT i * U.εT i = U.εT i := fun i => by rw [U.εT_orth, if_pos rfl]
  haveI hfree : ∀ i, Module.Free R (LinearMap.range (U.εT i).mulVecLin) :=
    fun i => (RankA.free_range_idem _ (hidem i)).1
  haveI hfin : ∀ i, Module.Finite R (LinearMap.range (U.εT i).mulVecLin) :=
    fun i => (RankA.free_range_idem _ (hidem i)).2
  have hsn : ∀ i ∈ Finset.univ, ((U.εT i).map (IsLocalRing.residue R)).rank ≤
      Module.finrank R (LinearMap.range (U.εT i).mulVecLin) := fun i _ => RankA.rank_map_le _ _
  have hsumn : ∑ i, Module.finrank R (LinearMap.range (U.εT i).mulVecLin) = Fintype.card (Ix g) :=
    RankA.sum_finrank U.εT U.εT_orth U.εT_sum
  have hsums : ∑ i, ((U.εT i).map (IsLocalRing.residue R)).rank = Fintype.card (Ix g) := by
    have horth : ∀ i j, (U.εT i).map (IsLocalRing.residue R) * (U.εT j).map (IsLocalRing.residue R) =
        if i = j then (U.εT i).map (IsLocalRing.residue R) else 0 := by
      intro i j
      rw [← Matrix.map_mul, U.εT_orth]
      split_ifs <;> simp
    have hs1 : ∑ i, (U.εT i).map (IsLocalRing.residue R) = 1 := by
      have e : ∑ i, (U.εT i).map (IsLocalRing.residue R) =
          (IsLocalRing.residue R).mapMatrix (∑ i, U.εT i) := by
        simp only [map_sum, RingHom.mapMatrix_apply]
      rw [e, U.εT_sum, map_one]
    exact RankA.sum_finrank (fun i => (U.εT i).map (IsLocalRing.residue R)) horth hs1
  have hseq : ∀ i, ((U.εT i).map (IsLocalRing.residue R)).rank =
      Module.finrank R (LinearMap.range (U.εT i).mulVecLin) := by
    have h := (Finset.sum_eq_sum_iff_of_le hsn).mp (hsums.trans hsumn.symm)
    exact fun i => h i (Finset.mem_univ i)
  have hphi : ∀ i, ((U.εT (U.φ i)).map (IsLocalRing.residue R)).rank =
      ((U.εT i).map (IsLocalRing.residue R)).rank := by
    have hle : ∀ i ∈ Finset.univ, ((U.εT (U.φ i)).map (IsLocalRing.residue R)).rank ≤
        ((U.εT i).map (IsLocalRing.residue R)).rank := fun i _ => rank_phi_le hS U i
    have hs : ∑ i, ((U.εT (U.φ i)).map (IsLocalRing.residue R)).rank =
        ∑ i, ((U.εT i).map (IsLocalRing.residue R)).rank :=
      Equiv.sum_comp U.φ (fun i => ((U.εT i).map (IsLocalRing.residue R)).rank)
    exact fun i => (Finset.sum_eq_sum_iff_of_le hle).mp hs i (Finset.mem_univ i)
  refine ⟨fun i => ⟨Module.finrank R (LinearMap.range (U.εT i).mulVecLin), ?_, ?_⟩,
    fun i h0 => r_eq_zero hS H U i h0⟩
  · exact ⟨(Module.finBasisOfFinrankEq R _ rfl).equivFun⟩
  · have hn : Module.finrank R (LinearMap.range (U.εT (U.φ i)).mulVecLin) =
        Module.finrank R (LinearMap.range (U.εT i).mulVecLin) := by
      rw [← hseq, ← hseq, hphi]
    exact ⟨(Module.finBasisOfFinrankEq R _ hn).equivFun⟩

end ReciprocityTheory.PGsh.Up
