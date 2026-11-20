import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsFiniteAdeleLikePairElementary
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Establish `hr : Module.finrank ℤ L = Fintype.card ι`. Apply `le_antisymm` to reduce the goal to its premises. Simplify using `using Submodule.finrank_le L`. Set `f : (ι → ℤ) →ₗ[ℤ] L` to `LinearMap.codRestrict L (N • LinearMap.id) hL`. Establish `hf : Function.Injective f`.

Introduce `a b hab`. Establish `: N • a = N • b` using `congrArg Subtype.val hab`. Conclude with `smul_right_injective _ hN this`. Simplify using `using LinearMap.finrank_le_finrank_of_injective hf`. Set `b : Module.Basis ι ℤ L` to `(Module.finBasisOfFinrankEq ℤ L hr).reindex (Fintype.equivFin ι).symm`.

Use `⟨Matrix.of fun i j => (b j : ι → ℤ) i, fun j => (b j).2, fun v hv => ⟨b.repr ⟨v, hv⟩, ?_⟩⟩` and prove the remaining obligations. Use `congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)` as an intermediate fact. Use function extensionality and compare the values at `i`. Establish `h2` using `congrFun this i`. Simplify using `only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at h2`.

Rewrite using `[← h2]`. Simplify using `[Matrix.mulVec, dotProduct, mul_comm]`.
-/
theorem exists_matrix_span_of_smul_mem {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℤ)) (N : ℤ)
    (hN : N ≠ 0) (hL : ∀ v : ι → ℤ, N • v ∈ L) :
    ∃ H : Matrix ι ι ℤ, (∀ j, (fun i => H i j) ∈ L) ∧ ∀ v ∈ L, ∃ c : ι → ℤ, v = H *ᵥ c := by
  have hr : Module.finrank ℤ L = Fintype.card ι := by
    apply le_antisymm
    · simpa using Submodule.finrank_le L
    · let f : (ι → ℤ) →ₗ[ℤ] L := LinearMap.codRestrict L (N • LinearMap.id) hL
      have hf : Function.Injective f := by
        intro a b hab
        have : N • a = N • b := congrArg Subtype.val hab
        exact smul_right_injective _ hN this
      simpa using LinearMap.finrank_le_finrank_of_injective hf
  let b : Module.Basis ι ℤ L := (Module.finBasisOfFinrankEq ℤ L hr).reindex (Fintype.equivFin ι).symm
  refine ⟨Matrix.of fun i j => (b j : ι → ℤ) i, fun j => (b j).2, fun v hv => ⟨b.repr ⟨v, hv⟩, ?_⟩⟩
  have := congrArg Subtype.val (b.sum_repr ⟨v, hv⟩)
  funext i
  have h2 := congrFun this i
  simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at h2
  rw [← h2]
  simp [Matrix.mulVec, dotProduct, mul_comm]

/- English proof (translation)
Establish `hM' : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Set `φ : (ι → ℤ) →ₗ[ℤ] (ι → ℚ)` to `{ toFun := fun z i => (M : ℚ)⁻¹ * z i map_add' := fun a b => by funext i; simp [mul_add] map_smul' := fun a b => by funext i; simp; ring }`. Take `⟨H, hH, hc⟩` from `exists_matrix_span_of_smul_mem (L.comap φ) ((M : ℤ) * M) (by have := hM.ne'; positivity) (fun v => by`. Establish `: φ (((M : ℤ) * M) • v) = fun i => (M : ℚ) * v i`. Use function extensionality and compare the values at `i`.

Simplify using `[φ]`. Clear the denominators using the available nonvanishing facts. Simplify using `only [Submodule.mem_comap, this]`. Conclude with `h2 v)`. Set `h : Matrix ι ι ℚ` to `Matrix.of fun i j => (M : ℚ)⁻¹ * H i j`.

Establish `key : ∀ v ∈ L, ∃ c : ι → ℤ, v = h *ᵥ fun i => (c i : ℚ)`. Introduce `v hv`. Use `choose z hz using h1 v hv`. Establish `hφ : φ z = v`. Use function extensionality and compare the values at `i`.

Simplify using `only [φ, LinearMap.coe_mk, AddHom.coe_mk, ← hz]`. Clear the denominators using the available nonvanishing facts. Take `⟨c, hc'⟩` from `hc z (by simpa [hφ] using hv)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, hc']`.

Use function extensionality and compare the values at `i`. Simplify using `[φ, h, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]`. Use `choose C hC using fun j => key _ (h2 (Pi.single j 1))`. Set `g : Matrix ι ι ℚ` to `Matrix.of fun i j => (M : ℚ)⁻¹ * C j i`. Establish `hg : h * g = 1`.

Use extensionality with `i j`. Use `congrFun (hC j) i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct] at this`. Establish `e : (h * g) i j = (M : ℚ)⁻¹ * ∑ k, h i k * (C j k : ℚ)`. Simplify using `only [Matrix.mul_apply, g, Matrix.of_apply, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Rewrite using `[e, ← this]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[hM']`.

Simplify using `[hij]`. Use `⟨h, g, hg, fun j => hH j, fun v hv i => ?_⟩` and prove the remaining obligations. Take `⟨c, rfl⟩` from `key v hv`. Use `⟨c i, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec, mul_eq_one_comm.mp hg, Matrix.one_mulVec]`.
-/
theorem exists_matrix_basis_of_lattice {ι : Type} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℚ)) (M : ℕ)
    (hM : 0 < M) (h1 : ∀ v ∈ L, ∀ i, ∃ z : ℤ, (M : ℚ) * v i = z)
    (h2 : ∀ z : ι → ℤ, (fun i => (M : ℚ) * z i) ∈ L) :
    ∃ h g : Matrix ι ι ℚ, h * g = 1 ∧ (∀ j, (fun i => h i j) ∈ L) ∧ ∀ v ∈ L, ∀ i, ∃ z : ℤ, (g *ᵥ v) i = z := by
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  let φ : (ι → ℤ) →ₗ[ℤ] (ι → ℚ) :=
    { toFun := fun z i => (M : ℚ)⁻¹ * z i
      map_add' := fun a b => by funext i; simp [mul_add]
      map_smul' := fun a b => by funext i; simp; ring }
  obtain ⟨H, hH, hc⟩ := exists_matrix_span_of_smul_mem (L.comap φ) ((M : ℤ) * M)
    (by have := hM.ne'; positivity) (fun v => by
      have : φ (((M : ℤ) * M) • v) = fun i => (M : ℚ) * v i := by
        funext i
        simp [φ]
        field_simp
      simp only [Submodule.mem_comap, this]
      exact h2 v)
  let h : Matrix ι ι ℚ := Matrix.of fun i j => (M : ℚ)⁻¹ * H i j
  have key : ∀ v ∈ L, ∃ c : ι → ℤ, v = h *ᵥ fun i => (c i : ℚ) := by
    intro v hv
    choose z hz using h1 v hv
    have hφ : φ z = v := by
      funext i
      simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, ← hz]
      field_simp
    obtain ⟨c, hc'⟩ := hc z (by simpa [hφ] using hv)
    refine ⟨c, ?_⟩
    rw [← hφ, hc']
    funext i
    simp [φ, h, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  choose C hC using fun j => key _ (h2 (Pi.single j 1))
  let g : Matrix ι ι ℚ := Matrix.of fun i j => (M : ℚ)⁻¹ * C j i
  have hg : h * g = 1 := by
    ext i j
    have := congrFun (hC j) i
    simp only [Matrix.mulVec, dotProduct] at this
    have e : (h * g) i j = (M : ℚ)⁻¹ * ∑ k, h i k * (C j k : ℚ) := by
      simp only [Matrix.mul_apply, g, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, ← this]
    by_cases hij : i = j
    · subst hij; simp [hM']
    · simp [hij]
  refine ⟨h, g, hg, fun j => hH j, fun v hv i => ?_⟩
  obtain ⟨c, rfl⟩ := key v hv
  refine ⟨c i, ?_⟩
  rw [Matrix.mulVec_mulVec, mul_eq_one_comm.mp hg, Matrix.one_mulVec]

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Conclude with `R₀.sum_mem fun σ _ => R₀.mul_mem (intCast_mem R₀ _) (R₀.prod_mem fun i _ => hk _ _)`.
-/
theorem det_mem_subring_of_entries {ι : Type} [Fintype ι] [DecidableEq ι] {R : Type} [CommRing R] (R₀ : Subring R)
    (k : Matrix ι ι R) (hk : ∀ i j, k i j ∈ R₀) : k.det ∈ R₀ := by
  rw [Matrix.det_apply']
  exact R₀.sum_mem fun σ _ => R₀.mul_mem (intCast_mem R₀ _) (R₀.prod_mem fun i _ => hk _ _)

/- English proof (translation)
Introduce `ι _ _ R _ _ R₀ hp x hx`. Take `⟨-, hden, hinj⟩` from `adelicPair_elementary R R₀ hp`. Use `set y := x.adjugate with hy`. Establish `hxy : x * y = 1` using `by rw [hy, Matrix.mul_adjugate, hx, one_smul]`. Establish `hyx : y * x = 1` using `mul_eq_one_comm.mp hxy`.

Take `⟨M, hM, hMr⟩` from `hden ((ι × ι) ⊕ (ι × ι)) (Sum.elim (fun p => x p.1 p.2) (fun p => y p.1 p.2))`. Establish `hMx : ∀ i j, (M : R) * x i j ∈ R₀` using `fun i j => hMr (Sum.inl (i, j))`. Establish `hMy : ∀ i j, (M : R) * y i j ∈ R₀` using `fun i j => hMr (Sum.inr (i, j))`. Set `L : Submodule ℤ (ι → ℚ)` to `AddSubgroup.toIntSubmodule { carrier := {v | ∀ i, ∑ k, y i k * algebraMap ℚ R (v k) ∈ R₀} add_mem' := fun {a b} ha hb i => by`. Simplify `R₀.add_mem (ha i) (hb i)` using `[mul_add, Finset.sum_add_distrib]`.

Use the proof step `zero_mem' := fun i => by simp`. Use the proof step `neg_mem' := fun {a} ha i => by simpa using R₀.neg_mem (ha i) }`. Establish `hLm : ∀ v, v ∈ L ↔ ∀ i, ∑ k, y i k * algebraMap ℚ R (v k) ∈ R₀` using `fun v => Iff.rfl`. Establish `h2 : ∀ z : ι → ℤ, (fun i => (M : ℚ) * z i) ∈ L`. Introduce `z`.

Rewrite using `[hLm]`. Introduce `i`. Use `R₀.sum_mem fun k _ => ?_` and prove the remaining obligations. Establish `: y i k * algebraMap ℚ R ((M : ℚ) * z k) = (M : R) * y i k * z k` using `by simp; ring`. Rewrite using `[this]`.

Conclude with `R₀.mul_mem (hMy _ _) (intCast_mem R₀ _)`. Establish `h1 : ∀ v ∈ L, ∀ i, ∃ z : ℤ, (M : ℚ) * v i = z`. Introduce `v hv i`. Apply `hp.int_of_mem` to reduce the goal to its premises. Establish `e : (fun k => algebraMap ℚ R (v k)) = x *ᵥ (y *ᵥ fun k => algebraMap ℚ R (v k))`.

Rewrite using `[Matrix.mulVec_mulVec, hxy, Matrix.one_mulVec]`. Establish `e'` using `congrFun e i`. Rewrite using `[map_mul, map_natCast, e']`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.mul_sum]`.

Use `R₀.sum_mem fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc]`. Conclude with `R₀.mul_mem (hMx _ _) ((hLm v).1 hv k)`. Take `⟨h, g, hg, hh, hgL⟩` from `exists_matrix_basis_of_lattice L M hM h1 h2`. Establish `hMg : ∀ i j, (M : R) * algebraMap ℚ R (g i j) ∈ R₀`.

Introduce `i j`. Take `⟨z, hz⟩` from `hgL _ (h2 (Pi.single j 1)) i`. Establish `: (M : ℚ) * g i j = z`. Rewrite using `[← hz]`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Rewrite using `[Finset.sum_eq_single j]`. Simplify using `[mul_comm]`. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules.

Establish `e : (M : R) * algebraMap ℚ R (g i j) = (z : R)`. Rewrite using `[← map_natCast (algebraMap ℚ R), ← map_mul, this, map_intCast]`. Rewrite using `[e]`. Conclude with `intCast_mem R₀ _`. Establish `hk : ∀ i j, (g.map (algebraMap ℚ R) * x) i j ∈ R₀`.

Introduce `i j`. Use `choose q a ha hqa using fun k => hp.approx M hM (x k j)`. Establish `hq : q ∈ L`. Rewrite using `[hLm]`. Introduce `l`.

Establish `e : ∑ k, y l k * algebraMap ℚ R (q k) = (y * x) l j - ∑ k, (M : R) * y l k * a k`. Rewrite using `[Matrix.mul_apply, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [hqa k]; ring`. Rewrite using `[e, hyx]`. Use `R₀.sub_mem ?_ (R₀.sum_mem fun k _ => R₀.mul_mem (hMy _ _) (ha k))` and prove the remaining obligations.

Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Use `exacts [R₀.one_mem, R₀.zero_mem]`. Take `⟨z, hz⟩` from `hgL q hq i`. Establish `e : (g.map (algebraMap ℚ R) * x) i j = algebraMap ℚ R ((g *ᵥ q) i) + ∑ k, (M : R) * algebraMap ℚ R (g i k) * a k`.

Simplify using `only [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, map_mul]`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [hqa k]; ring`. Rewrite using `[e, hz, map_intCast]`. Conclude with `R₀.add_mem (intCast_mem R₀ _) (R₀.sum_mem fun k _ => R₀.mul_mem (hMg _ _) (ha k))`.

Establish `hk' : ∀ i j, (y * h.map (algebraMap ℚ R)) i j ∈ R₀` using `fun i j => (hLm _).1 (hh j) i`. Establish `hmd : ∀ t : Matrix ι ι ℚ, (t.map (algebraMap ℚ R)).det = algebraMap ℚ R t.det` using `fun t => ((algebraMap ℚ R).map_det t).symm`. Establish `hdy : y.det = 1`. Use `congrArg Matrix.det hxy` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, hx, one_mul, Matrix.det_one]`. Then use the resulting hypothesis.

Take `⟨zg, hzg⟩` from `hp.int_of_mem g.det (by`. Use `det_mem_subring_of_entries R₀ _ hk` as an intermediate fact. Rewrite using `[Matrix.det_mul, hx, mul_one, hmd] at this)` and apply the resulting hypothesis. Take `⟨zh, hzh⟩` from `hp.int_of_mem h.det (by`. Use `det_mem_subring_of_entries R₀ _ hk'` as an intermediate fact.

Rewrite using `[Matrix.det_mul, hdy, one_mul, hmd] at this)` and apply the resulting hypothesis. Establish `hdd : h.det * g.det = 1` using `by rw [← Matrix.det_mul, hg, Matrix.det_one]`. Establish `hz : zh * zg = 1`. Rewrite `hdd` using `[hzg, hzh]`. Conclude with `hdd` after adjusting the coercions.

Establish `hxe : x = h.map (algebraMap ℚ R) * (g.map (algebraMap ℚ R) * x)`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.map_mul, hg]`. Simplify using the standard rewrite rules. Break down `Int.eq_one_or_neg_one_of_mul_eq_one' hz with ⟨e1, e2⟩ | ⟨e1, e2⟩` into its components or cases. Use `⟨h, _, by simp [hzh, e1], ?_, hk, hxe⟩` and prove the remaining obligations.

Rewrite using `[Matrix.det_mul, hx, hmd, hzg, e2]`. Simplify using the standard rewrite rules. Break down `isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩` into its components or cases. Rewrite `hzh` using `[Matrix.det_isEmpty, e1]`. Evaluate the numerical expressions using `at hzh`.

Set `d : ι → ℚ` to `fun i => if i = i₀ then -1 else 1`. Establish `hd : (Matrix.diagonal d).det = -1` using `by simp [d]`. Establish `hdd2 : Matrix.diagonal d * Matrix.diagonal d = 1`. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `by_cases hi : i = i₀ <;> simp [d, hi]`. Use `⟨h * Matrix.diagonal d, (Matrix.diagonal d).map (algebraMap ℚ R) * (g.map (algebraMap ℚ R) * x), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, hd, hzh, e1]`. Simplify using the standard rewrite rules.

Rewrite using `[Matrix.det_mul, Matrix.det_mul, hx, hmd, hmd, hd, hzg, e2]`. Simplify using the standard rewrite rules. Introduce `i j`. Rewrite using `[Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]`. Use `R₀.mul_mem ?_ (hk i j)` and prove the remaining obligations.

Distinguish the cases in `hi : i = i₀`. Simplify `R₀.neg_mem R₀.one_mem` using `[d, hi]`. Simplify `R₀.one_mem` using `[d, hi]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_assoc h, hdd2, Matrix.mul_one]`. Conclude with `hxe`.
-/
theorem sl_class_number_one : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), AdelicPair R R₀ → ∀ x : Matrix ι ι R, x.det = 1 → ∃ (h : Matrix ι ι ℚ) (k : Matrix ι ι R), h.det = 1 ∧ k.det = 1 ∧ (∀ i j, k i j ∈ R₀) ∧ x = h.map (algebraMap ℚ R) * k := by
  intro ι _ _ R _ _ R₀ hp x hx
  obtain ⟨-, hden, hinj⟩ := adelicPair_elementary R R₀ hp
  set y := x.adjugate with hy
  have hxy : x * y = 1 := by rw [hy, Matrix.mul_adjugate, hx, one_smul]
  have hyx : y * x = 1 := mul_eq_one_comm.mp hxy
  obtain ⟨M, hM, hMr⟩ := hden ((ι × ι) ⊕ (ι × ι)) (Sum.elim (fun p => x p.1 p.2) (fun p => y p.1 p.2))
  have hMx : ∀ i j, (M : R) * x i j ∈ R₀ := fun i j => hMr (Sum.inl (i, j))
  have hMy : ∀ i j, (M : R) * y i j ∈ R₀ := fun i j => hMr (Sum.inr (i, j))
  let L : Submodule ℤ (ι → ℚ) := AddSubgroup.toIntSubmodule
    { carrier := {v | ∀ i, ∑ k, y i k * algebraMap ℚ R (v k) ∈ R₀}
      add_mem' := fun {a b} ha hb i => by
        simpa [mul_add, Finset.sum_add_distrib] using R₀.add_mem (ha i) (hb i)
      zero_mem' := fun i => by simp
      neg_mem' := fun {a} ha i => by simpa using R₀.neg_mem (ha i) }
  have hLm : ∀ v, v ∈ L ↔ ∀ i, ∑ k, y i k * algebraMap ℚ R (v k) ∈ R₀ := fun v => Iff.rfl
  have h2 : ∀ z : ι → ℤ, (fun i => (M : ℚ) * z i) ∈ L := by
    intro z
    rw [hLm]
    intro i
    refine R₀.sum_mem fun k _ => ?_
    have : y i k * algebraMap ℚ R ((M : ℚ) * z k) = (M : R) * y i k * z k := by simp; ring
    rw [this]
    exact R₀.mul_mem (hMy _ _) (intCast_mem R₀ _)
  have h1 : ∀ v ∈ L, ∀ i, ∃ z : ℤ, (M : ℚ) * v i = z := by
    intro v hv i
    apply hp.int_of_mem
    have e : (fun k => algebraMap ℚ R (v k)) = x *ᵥ (y *ᵥ fun k => algebraMap ℚ R (v k)) := by
      rw [Matrix.mulVec_mulVec, hxy, Matrix.one_mulVec]
    have e' := congrFun e i
    rw [map_mul, map_natCast, e']
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    refine R₀.sum_mem fun k _ => ?_
    rw [← mul_assoc]
    exact R₀.mul_mem (hMx _ _) ((hLm v).1 hv k)
  obtain ⟨h, g, hg, hh, hgL⟩ := exists_matrix_basis_of_lattice L M hM h1 h2
  have hMg : ∀ i j, (M : R) * algebraMap ℚ R (g i j) ∈ R₀ := by
    intro i j
    obtain ⟨z, hz⟩ := hgL _ (h2 (Pi.single j 1)) i
    have : (M : ℚ) * g i j = z := by
      rw [← hz]
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single j]
      · simp [mul_comm]
      · intro b _ hb; simp [hb]
      · simp
    have e : (M : R) * algebraMap ℚ R (g i j) = (z : R) := by
      rw [← map_natCast (algebraMap ℚ R), ← map_mul, this, map_intCast]
    rw [e]
    exact intCast_mem R₀ _
  have hk : ∀ i j, (g.map (algebraMap ℚ R) * x) i j ∈ R₀ := by
    intro i j
    choose q a ha hqa using fun k => hp.approx M hM (x k j)
    have hq : q ∈ L := by
      rw [hLm]
      intro l
      have e : ∑ k, y l k * algebraMap ℚ R (q k) = (y * x) l j - ∑ k, (M : R) * y l k * a k := by
        rw [Matrix.mul_apply, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun k _ => by rw [hqa k]; ring
      rw [e, hyx]
      refine R₀.sub_mem ?_ (R₀.sum_mem fun k _ => R₀.mul_mem (hMy _ _) (ha k))
      rw [Matrix.one_apply]
      split_ifs
      exacts [R₀.one_mem, R₀.zero_mem]
    obtain ⟨z, hz⟩ := hgL q hq i
    have e : (g.map (algebraMap ℚ R) * x) i j =
        algebraMap ℚ R ((g *ᵥ q) i) + ∑ k, (M : R) * algebraMap ℚ R (g i k) * a k := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, Matrix.map_apply, map_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by rw [hqa k]; ring
    rw [e, hz, map_intCast]
    exact R₀.add_mem (intCast_mem R₀ _) (R₀.sum_mem fun k _ => R₀.mul_mem (hMg _ _) (ha k))
  have hk' : ∀ i j, (y * h.map (algebraMap ℚ R)) i j ∈ R₀ := fun i j => (hLm _).1 (hh j) i
  have hmd : ∀ t : Matrix ι ι ℚ, (t.map (algebraMap ℚ R)).det = algebraMap ℚ R t.det := fun t =>
    ((algebraMap ℚ R).map_det t).symm
  have hdy : y.det = 1 := by
    have := congrArg Matrix.det hxy
    rwa [Matrix.det_mul, hx, one_mul, Matrix.det_one] at this
  obtain ⟨zg, hzg⟩ := hp.int_of_mem g.det (by
    have := det_mem_subring_of_entries R₀ _ hk
    rwa [Matrix.det_mul, hx, mul_one, hmd] at this)
  obtain ⟨zh, hzh⟩ := hp.int_of_mem h.det (by
    have := det_mem_subring_of_entries R₀ _ hk'
    rwa [Matrix.det_mul, hdy, one_mul, hmd] at this)
  have hdd : h.det * g.det = 1 := by rw [← Matrix.det_mul, hg, Matrix.det_one]
  have hz : zh * zg = 1 := by
    rw [hzg, hzh] at hdd
    exact_mod_cast hdd
  have hxe : x = h.map (algebraMap ℚ R) * (g.map (algebraMap ℚ R) * x) := by
    rw [← Matrix.mul_assoc, ← Matrix.map_mul, hg]
    simp
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hz with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨h, _, by simp [hzh, e1], ?_, hk, hxe⟩
    rw [Matrix.det_mul, hx, hmd, hzg, e2]
    simp
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
    · rw [Matrix.det_isEmpty, e1] at hzh
      norm_num at hzh
    · let d : ι → ℚ := fun i => if i = i₀ then -1 else 1
      have hd : (Matrix.diagonal d).det = -1 := by simp [d]
      have hdd2 : Matrix.diagonal d * Matrix.diagonal d = 1 := by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        by_cases hi : i = i₀ <;> simp [d, hi]
      refine ⟨h * Matrix.diagonal d, (Matrix.diagonal d).map (algebraMap ℚ R) * (g.map (algebraMap ℚ R) * x),
        ?_, ?_, ?_, ?_⟩
      · rw [Matrix.det_mul, hd, hzh, e1]
        simp
      · rw [Matrix.det_mul, Matrix.det_mul, hx, hmd, hmd, hd, hzg, e2]
        simp
      · intro i j
        rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul]
        refine R₀.mul_mem ?_ (hk i j)
        by_cases hi : i = i₀
        · simpa [d, hi] using R₀.neg_mem R₀.one_mem
        · simpa [d, hi] using R₀.one_mem
      · rw [← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_assoc h, hdd2, Matrix.mul_one]
        exact hxe

end GlobalTheory.ClassFin
