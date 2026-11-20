import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.FixBdQZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CentraliserRank
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Set `K` to `FractionRing A`. Establish `inj : Function.Injective (algebraMap A K)` using `IsFractionRing.injective A K`. Set `φ : Matrix (Fin n) (Fin n) A →ₐ[A] Matrix (Fin n) (Fin n) K` to `(Algebra.ofId A K).mapMatrix`. Establish `φinj : Function.Injective φ` using `Matrix.map_injective inj`. Take `⟨h1, h2⟩` from `UpperTheory.V.AlgebraTools.centraliser_rank (fun i => algebraMap A K (al i)) (φ P) (inj.comp hal) (by`.

Establish `: φ P = P.map (algebraMap A K)` using `rfl`. Rewrite using `[this, Matrix.charpoly_map, hP, Polynomial.map_prod]`. Use the proof step `simp)`. Use `⟨fun N _ _ f hf hc => ?_, fun E Y hE hY => φinj ?_⟩` and prove the remaining obligations. Use `set U := LinearMap.ker (LinearMap.mulLeft K (φ P) - LinearMap.mulRight K (φ P)) with hU`.

Set `ψ : N →ₗ[A] U` to `{ toFun := fun z => ⟨φ (f z), by`. Rewrite using `[hU, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, ← map_mul, hc, map_mul, sub_self]⟩`. Use the proof step `map_add' := fun y z => Subtype.ext (by simp)`. Use the proof step `map_smul' := fun c z => Subtype.ext (by simp) }`. Establish `hψ : Function.Injective ψ` using `fun y z h => hf (φinj (congrArg Subtype.val h))`.

Apply `Module.finrank_le_of_rank_le` to reduce the goal to its premises. Use `(LinearMap.rank_le_of_injective ψ hψ).trans ?_` and prove the remaining obligations. Rewrite using `[← IsLocalization.rank_eq K (nonZeroDivisors A) le_rfl, ← Module.finrank_eq_rank, h1, Fintype.card_fin]`. Take `⟨q, hq⟩` from `h2 (φ Y) (by rw [← map_mul, hY, map_mul])`. Take `⟨r, hr⟩` from `h2 (φ E) (by rw [← map_mul, hE, map_mul])`.

Rewrite using `[map_mul, map_mul, hq, hr, ← map_mul, ← map_mul, mul_comm]`.
-/
private theorem centralizer_rank_le {A : Type} [CommRing A] [IsDomain A] {n : ℕ} (al : Fin n → A) (P : Matrix (Fin n) (Fin n) A)
    (hal : Function.Injective al) (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i))) :
    (∀ (N : Type) [AddCommGroup N] [Module A N] (f : N →ₗ[A] Matrix (Fin n) (Fin n) A), Function.Injective f →
      (∀ z, P * f z = f z * P) → Module.finrank A N ≤ n) ∧
    ∀ E Y : Matrix (Fin n) (Fin n) A, P * E = E * P → P * Y = Y * P → E * Y = Y * E := by
  let K := FractionRing A
  have inj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  let φ : Matrix (Fin n) (Fin n) A →ₐ[A] Matrix (Fin n) (Fin n) K := (Algebra.ofId A K).mapMatrix
  have φinj : Function.Injective φ := Matrix.map_injective inj
  obtain ⟨h1, h2⟩ := UpperTheory.V.AlgebraTools.centraliser_rank (fun i => algebraMap A K (al i)) (φ P) (inj.comp hal) (by
    have : φ P = P.map (algebraMap A K) := rfl
    rw [this, Matrix.charpoly_map, hP, Polynomial.map_prod]
    simp)
  refine ⟨fun N _ _ f hf hc => ?_, fun E Y hE hY => φinj ?_⟩
  · set U := LinearMap.ker (LinearMap.mulLeft K (φ P) - LinearMap.mulRight K (φ P)) with hU
    let ψ : N →ₗ[A] U :=
      { toFun := fun z => ⟨φ (f z), by
          rw [hU, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
            ← map_mul, hc, map_mul, sub_self]⟩
        map_add' := fun y z => Subtype.ext (by simp)
        map_smul' := fun c z => Subtype.ext (by simp) }
    have hψ : Function.Injective ψ := fun y z h => hf (φinj (congrArg Subtype.val h))
    apply Module.finrank_le_of_rank_le
    refine (LinearMap.rank_le_of_injective ψ hψ).trans ?_
    rw [← IsLocalization.rank_eq K (nonZeroDivisors A) le_rfl, ← Module.finrank_eq_rank, h1, Fintype.card_fin]
  · obtain ⟨q, hq⟩ := h2 (φ Y) (by rw [← map_mul, hY, map_mul])
    obtain ⟨r, hr⟩ := h2 (φ E) (by rw [← map_mul, hE, map_mul])
    rw [map_mul, map_mul, hq, hr, ← map_mul, ← map_mul, mul_comm]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => simp [Finset.sum_insert hi, ih]`.
-/
private theorem dual_sum_ep_prime_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) :
    (∑ i ∈ s, f i).ep' j = ∑ i ∈ s, (f i).ep' j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => simp [Finset.sum_insert hi, ih]`.
-/
private theorem dual_sum_eta_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ i ∈ s, f i).eta = ∑ i ∈ s, (f i).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih => simp [Finset.sum_insert hi, ih]`.
-/
private theorem dual_sum_a_coord {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [Finset.sum_insert hi, ih]

/- English proof (translation)
Take `⟨c1, c2⟩` from `centralizer_rank_le al P hal hP`. Establish `ha : ∀ Z ∈ N, ∀ i j, (Z i j).a = 0 ∧ (Z i j).ep = 0` using `fun Z hZ i j => by`. Distinguish the cases in `h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)`. Use `(h1 hZ i j).1 h` as an intermediate fact. Conclude with `⟨this.1 rfl, this.2.1 rfl⟩`.

Use `(h1 hZ i j).2 h` as an intermediate fact. Conclude with `⟨this.1 rfl, this.2.1 rfl⟩`. Establish `hb : ∀ Z ∈ N, ∀ i j s, (Z i j).ep' s = 0` using `fun Z hZ i j s => by`. Distinguish the cases in `h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)`. Conclude with `congrFun (((h1 hZ i j).1 h).2.2.1 rfl) s`.

Establish `e` using `c2 (diagonal fun i => if (i : ℕ) < a then 1 else 0) (Matrix.of fun i j => (Z i j).ep' s) ?_ ?_`. Establish `e'` using `congrFun (congrFun e i) j`. Rewrite `e'` using `[diagonal_mul, mul_diagonal, of_apply]`. Apply the tactic sequence `by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp_all`. Use extensionality with `u v`.

Rewrite using `[diagonal_mul, mul_diagonal]`. Distinguish the cases in `h' : ((u : ℕ) < a) ↔ ((v : ℕ) < a)`. Simplify using `[h', mul_comm]`. Establish `: P u v = 0` using `(hev u v).2 h'`. Simplify using `[this]`.

Use extensionality with `u v`. Establish `e'` using `congrArg (fun M : Matrix (Fin n) (Fin n) (DD A g) => (M u v).ep' s) (h2 Z hZ)`. Simplify `e'` using `[Matrix.mul_apply, dual_sum_ep_prime_coord, hR, fun i j => (ha Z hZ i j).1]`. Establish `hs : ∀ (c : A) (y : DD A g), (c • y).eta = c * y.eta` using `fun c y => by`. Establish `hc : c • y = DD.C (algebraMap A A c) * y` using `rfl`.

Simplify using `[hc]`. Use `c1 N { toFun := fun Z => Matrix.of fun i j => (Z.1 i j).eta map_add' := fun y z => rfl map_smul' := fun c z => by ext i j; simp [hs] } ?_ ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `Z hZ`. Use extensionality with `i j`.

Conclude with `(ha _ Z.2 i j).1`. Conclude with `congrFun (ha _ Z.2 i j).2 _`. Conclude with `hb _ Z.2 i j _`. Conclude with `congrFun (congrFun hZ i) j`. Introduce and unpack `⟨Z, hZ⟩`.

Express the relevant statement in the definitionally equal form `P * (Matrix.of fun i j => (Z i j).eta) = (Matrix.of fun i j => (Z i j).eta) * P`. Use extensionality with `u v`. Establish `e'` using `congrArg (fun M : Matrix (Fin n) (Fin n) (DD A g) => (M u v).eta) (h2 Z hZ)`. Simplify `e'` using `[Matrix.mul_apply, dual_sum_eta_coord, hR, fun i j => (ha Z hZ i j).1, fun i j => (ha Z hZ i j).2, hb Z hZ]`.
-/
private theorem finrank_centralizer_W1_le {A : Type} [CommRing A] [IsDomain A] {n a g : ℕ} (al : Fin n → A)
    (P : Matrix (Fin n) (Fin n) A)
    (hal : Function.Injective al) (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)))
    (hev : P ∈ Ev A A n a) (R : Matrix (Fin n) (Fin n) (DD A g)) (hR : ∀ i j, (R i j).a = P i j)
    (N : Submodule A (Matrix (Fin n) (Fin n) (DD A g))) (h1 : N ≤ pairedDualFirstOrderDualMatrixSpace n A A g a) (h2 : ∀ Z ∈ N, R * Z = Z * R) :
    Module.finrank A N ≤ n := by
  obtain ⟨c1, c2⟩ := centralizer_rank_le al P hal hP
  have ha : ∀ Z ∈ N, ∀ i j, (Z i j).a = 0 ∧ (Z i j).ep = 0 := fun Z hZ i j => by
    by_cases h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · have := (h1 hZ i j).1 h
      exact ⟨this.1 rfl, this.2.1 rfl⟩
    · have := (h1 hZ i j).2 h
      exact ⟨this.1 rfl, this.2.1 rfl⟩
  have hb : ∀ Z ∈ N, ∀ i j s, (Z i j).ep' s = 0 := fun Z hZ i j s => by
    by_cases h : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · exact congrFun (((h1 hZ i j).1 h).2.2.1 rfl) s
    · have e := c2 (diagonal fun i => if (i : ℕ) < a then 1 else 0) (Matrix.of fun i j => (Z i j).ep' s) ?_ ?_
      · have e' := congrFun (congrFun e i) j
        rw [diagonal_mul, mul_diagonal, of_apply] at e'
        by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp_all
      · ext u v
        rw [diagonal_mul, mul_diagonal]
        by_cases h' : ((u : ℕ) < a) ↔ ((v : ℕ) < a)
        · simp [h', mul_comm]
        · have : P u v = 0 := (hev u v).2 h'
          simp [this]
      · ext u v
        have e' := congrArg (fun M : Matrix (Fin n) (Fin n) (DD A g) => (M u v).ep' s) (h2 Z hZ)
        simpa [Matrix.mul_apply, dual_sum_ep_prime_coord, hR, fun i j => (ha Z hZ i j).1] using e'
  have hs : ∀ (c : A) (y : DD A g), (c • y).eta = c * y.eta := fun c y => by
    have hc : c • y = DD.C (algebraMap A A c) * y := rfl
    simp [hc]
  refine c1 N
    { toFun := fun Z => Matrix.of fun i j => (Z.1 i j).eta
      map_add' := fun y z => rfl
      map_smul' := fun c z => by ext i j; simp [hs] } ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro Z hZ
    ext i j
    · exact (ha _ Z.2 i j).1
    · exact congrFun (ha _ Z.2 i j).2 _
    · exact hb _ Z.2 i j _
    · exact congrFun (congrFun hZ i) j
  · rintro ⟨Z, hZ⟩
    change P * (Matrix.of fun i j => (Z i j).eta) = (Matrix.of fun i j => (Z i j).eta) * P
    ext u v
    have e' := congrArg (fun M : Matrix (Fin n) (Fin n) (DD A g) => (M u v).eta) (h2 Z hZ)
    simpa [Matrix.mul_apply, dual_sum_eta_coord, hR, fun i j => (ha Z hZ i j).1, fun i j => (ha Z hZ i j).2, hb Z hZ] using e'

/- English proof (translation)
Introduce `l _ F n x k σ al hal hP`. Take `⟨C, hC⟩` from `fixBd l F n x k _ false false false true false false true false Unit (fun _ => 1) (fun _ => k.ρ1 x.A σ) (fun _ => k.ρ1 x.A σ⁻¹) false rfl`. Use `⟨C, fun m => ?_⟩` and prove the remaining obligations. Establish `red : ∀ g, (k.ρ1 x.A g).map (fun y => (⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j), fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩ : DD (x.Am m) k.g)) = k.ρ1 (x.Am m) g`. Introduce `g`.

Express the relevant statement in the definitionally equal form `(x.redD k.g m).mapMatrix (k.ρ1 x.A g) = _`. Rewrite using `[Kap.ρ1, Kap.ρ1, map_mul, map_add, map_one]`. Both sides reduce to the same expression. Use `le_trans (le_of_eq ?_) ((hC m).trans (Nat.pow_le_pow_right Nat.card_pos ?_))` and prove the remaining obligations. Use `congr 1`.

Use extensionality with `Y`. Simplify using `only [red, one_smul, Set.mem_setOf_eq, forall_const, Bool.false_eq_true, IsEmpty.forall_iff, true_and]`. Both sides reduce to the same expression. Use `Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _` and prove the remaining obligations. Use `finrank_centralizer_W1_le al _ hal hP (x.blk σ) (k.ρ1 x.A σ) (fun i j => ?_) _ (inf_le_left.trans inf_le_left) fun Z hZ => ?_` and prove the remaining obligations.

Establish `hc : ∀ c : x.A, algebraMap x.A (DD x.A k.g) c = DD.C c` using `fun c => rfl`. Rewrite using `[Kap.ρ1, add_mul, one_mul]`. Simplify using `[Matrix.mul_apply, dual_sum_a_coord, DD.epM, NP.ρX, hc]`. Take `⟨r1, r2, -⟩` from `rho1 l F n x k x.A`. Establish `e : (1 : x.A) • (k.ρ1 x.A σ * (Z * k.ρ1 x.A σ⁻¹)) - Z = 0` using `(Submodule.mem_iInf _).1 hZ.2 ()`.

Rewrite `e` using `[one_smul, sub_eq_zero]`. Use `conv_rhs => rw [← e]`. Rewrite using `[mul_assoc, mul_assoc, ← r2, inv_mul_cancel, r1, mul_one]`.
-/
theorem UpperTheory.V.Pa.h0q :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (k : Kap x) (σ : F.G₀) (al : Fin n → x.A), Function.Injective al → (mat x.ρ σ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)) → ∃ C : ℕ, ∀ (m : ℕ), {Y : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g) | Y ∈ k.EpsilonEtaTensorDual (x.Am m) ∧ k.ρ1 (x.Am m) σ * Y * k.ρ1 (x.Am m) σ⁻¹ = Y}.ncard ≤ Nat.card x.K ^ (m * n + C) := by
  intro l _ F n x k σ al hal hP
  obtain ⟨C, hC⟩ := fixBd l F n x k _ false false false true false false true false Unit (fun _ => 1)
    (fun _ => k.ρ1 x.A σ) (fun _ => k.ρ1 x.A σ⁻¹) false rfl
  refine ⟨C, fun m => ?_⟩
  have red : ∀ g, (k.ρ1 x.A g).map (fun y => (⟨algebraMap x.A (x.Am m) y.a, fun j => algebraMap x.A (x.Am m) (y.ep j), fun j => algebraMap x.A (x.Am m) (y.ep' j), algebraMap x.A (x.Am m) y.eta⟩ : DD (x.Am m) k.g)) = k.ρ1 (x.Am m) g := by
    intro g
    change (x.redD k.g m).mapMatrix (k.ρ1 x.A g) = _
    rw [Kap.ρ1, Kap.ρ1, map_mul, map_add, map_one]
    rfl
  refine le_trans (le_of_eq ?_) ((hC m).trans (Nat.pow_le_pow_right Nat.card_pos ?_))
  · congr 1
    ext Y
    simp only [red, one_smul, Set.mem_setOf_eq, forall_const, Bool.false_eq_true, IsEmpty.forall_iff, true_and]
    rfl
  · refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _
    refine finrank_centralizer_W1_le al _ hal hP (x.blk σ) (k.ρ1 x.A σ) (fun i j => ?_) _ (inf_le_left.trans inf_le_left) fun Z hZ => ?_
    · have hc : ∀ c : x.A, algebraMap x.A (DD x.A k.g) c = DD.C c := fun c => rfl
      rw [Kap.ρ1, add_mul, one_mul]
      simp [Matrix.mul_apply, dual_sum_a_coord, DD.epM, NP.ρX, hc]
    · obtain ⟨r1, r2, -⟩ := rho1 l F n x k x.A
      have e : (1 : x.A) • (k.ρ1 x.A σ * (Z * k.ρ1 x.A σ⁻¹)) - Z = 0 := (Submodule.mem_iInf _).1 hZ.2 ()
      rw [one_smul, sub_eq_zero] at e
      conv_rhs => rw [← e]
      rw [mul_assoc, mul_assoc, ← r2, inv_mul_cancel, r1, mul_one]
